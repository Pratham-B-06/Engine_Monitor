/*
 * Engine monitor application layer (sampling, FFT, RPM, baseline, DS18B20,
 * UART framing, PWM command RX, IR tach).
 *
 * UART frame (12 bytes, both directions):
 *   [0xA5][ID_H][ID_L][D0..D7][CRC8]      CRC8 poly 0x07 over ID_H..D7
 *   0x0100 vib   : u16 rms_mg, u16 freq_cHz, u16 rpm, u16 amp1x_mg   (LE)
 *   0x0101 temp  : i16 temp_cC, u8 valid, 5x pad
 *   0x01FF status: u8 flags, u8 base_pct, u16 tach_rpm, u16 missed, u16 i2c_err
 *        flags: b0 vib_alarm, b1 temp_alarm, b2 baseline_ready,
 *               b3 temp_valid, b4 sensor_fault
 *   0x0200 cmd   : u8 pwm_percent (0..100)   (ESP32 -> STM32)
 */
#include "app.h"
#include "main.h"
#include "i2c.h"
#include "tim.h"
#include "usart.h"
#include "arm_math.h"
#include <string.h>
#include <math.h>

/* ---------------- configuration ---------------- */
#define FS_HZ            1000u
#define N                1024u
#define ACC_LSB_PER_G    16384.0f      /* +-2 g */
#define F_MIN_HZ         5u
#define F_MAX_HZ         180u          /* MPU DLPF = 184 Hz */
#define AMP_MIN_G        0.005f        /* below this: no valid 1x peak */
#define BASE_WINDOWS     30u           /* ~30 s */
#define K_ALARM          2.0f
#define TEMP_ON_C100     7000          /* 70.0 C */
#define TEMP_OFF_C100    6500          /* 65.0 C */
#define TACH_PPR         1u
#define PWM_ARR          199u          /* TIM1 ARR */

#define MPU_ADDR         (0x68u << 1)
#define OW_PORT          GPIOA
#define OW_PIN           GPIO_PIN_1    /* DS18B20 DQ, external 4.7k pull-up to 3V3 */

/* ---------------- state ---------------- */
static int16_t  win[2][N][3];
static volatile uint16_t w_idx;
static volatile uint8_t  w_active;
static volatile uint8_t  w_ready;      /* 1 + buffer index when ready: 0 none, 1 buf0, 2 buf1 */
static uint8_t  dma_buf[6];
static volatile uint16_t missed, i2c_err, overrun;
static uint8_t  sensor_ok;

static arm_rfft_fast_instance_f32 rfft;
static float hann[N], fft_in[N], fft_out[N], mag2[N / 2], pwr[N / 2];

static volatile uint8_t  pwm_req;
static uint8_t  pwm_cmd;

static uint8_t  base_ready, base_n, vib_alarm, bad_cnt, good_cnt;
static float    base_rms_sum, base_amp_sum, base_rms, base_amp;

static int16_t  temp_c100;
static uint8_t  temp_valid, temp_alarm;
static uint8_t  t_state;               /* 0 idle, 1 converting */
static uint32_t t_tick;

static volatile uint32_t tach_ovf, tach_last, tach_tick;
static volatile uint16_t tach_rpm;
static volatile uint8_t  tach_have_last;

static uint8_t rx_buf[12], rx_idx;
static uint8_t rx_byte;

/* ---------------- helpers ---------------- */
static uint8_t crc8(const uint8_t *p, uint8_t n)
{
  uint8_t c = 0;
  while (n--) {
    c ^= *p++;
    for (uint8_t i = 0; i < 8; i++) c = (c & 0x80) ? (uint8_t)((c << 1) ^ 0x07) : (uint8_t)(c << 1);
  }
  return c;
}

static void send_frame(uint16_t id, const uint8_t d[8])
{
  uint8_t f[12];
  f[0] = 0xA5; f[1] = (uint8_t)(id >> 8); f[2] = (uint8_t)id;
  memcpy(&f[3], d, 8);
  f[11] = crc8(&f[1], 10);
  HAL_UART_Transmit(&huart1, f, sizeof f, 20);
}

static void put16(uint8_t *d, uint16_t v) { d[0] = (uint8_t)v; d[1] = (uint8_t)(v >> 8); }

/* ---------------- DS18B20 (1-Wire, bit-banged, TIM6 = 1 MHz) ---------------- */
static inline void us_delay(uint16_t us)
{
  uint16_t s = (uint16_t)TIM6->CNT;
  while ((uint16_t)((uint16_t)TIM6->CNT - s) < us) { }
}
static inline void ow_low(void)  { OW_PORT->BSRR = (uint32_t)OW_PIN << 16; }
static inline void ow_rel(void)  { OW_PORT->BSRR = OW_PIN; }
static inline uint8_t ow_rd(void){ return (OW_PORT->IDR & OW_PIN) != 0; }

static uint8_t ow_reset(void)
{
  uint8_t present;
  ow_low(); us_delay(480);
  __disable_irq();
  ow_rel(); us_delay(70);
  present = !ow_rd();
  __enable_irq();
  us_delay(410);
  return present;
}
static void ow_write_bit(uint8_t b)
{
  __disable_irq();
  ow_low(); us_delay(b ? 6 : 60);
  ow_rel(); us_delay(b ? 64 : 10);
  __enable_irq();
}
static uint8_t ow_read_bit(void)
{
  uint8_t v;
  __disable_irq();
  ow_low(); us_delay(3);
  ow_rel(); us_delay(9);
  v = ow_rd();
  us_delay(55);
  __enable_irq();
  return v;
}
static void ow_write(uint8_t v) { for (uint8_t i = 0; i < 8; i++) { ow_write_bit(v & 1); v >>= 1; } }
static uint8_t ow_read(void) { uint8_t v = 0; for (uint8_t i = 0; i < 8; i++) v |= (uint8_t)(ow_read_bit() << i); return v; }

static uint8_t ow_crc(const uint8_t *p, uint8_t n)
{
  uint8_t c = 0;
  while (n--) {
    uint8_t b = *p++;
    for (uint8_t i = 0; i < 8; i++) {
      uint8_t m = (c ^ b) & 1; c >>= 1; if (m) c ^= 0x8C; b >>= 1;
    }
  }
  return c;
}

static void temp_service(void)
{
  uint32_t now = HAL_GetTick();
  if (t_state == 0) {
    if (ow_reset()) { ow_write(0xCC); ow_write(0x44); t_state = 1; t_tick = now; }
    else { temp_valid = 0; t_tick = now; t_state = 2; }          /* no sensor: retry later */
  } else if (t_state == 1 && (now - t_tick) >= 800) {
    uint8_t sp[9];
    if (ow_reset()) {
      ow_write(0xCC); ow_write(0xBE);
      for (uint8_t i = 0; i < 9; i++) sp[i] = ow_read();
      if (ow_crc(sp, 8) == sp[8]) {
        int16_t raw = (int16_t)(sp[0] | (sp[1] << 8));
        temp_c100 = (int16_t)(((int32_t)raw * 100) / 16);
        temp_valid = 1;
        if (temp_c100 >= TEMP_ON_C100) temp_alarm = 1;
        else if (temp_c100 <= TEMP_OFF_C100) temp_alarm = 0;
      } else temp_valid = 0;
    } else temp_valid = 0;
    uint8_t d[8] = {0};
    put16(d, (uint16_t)temp_c100); d[2] = temp_valid;
    send_frame(0x0101, d);
    t_state = 0;
  } else if (t_state == 2 && (now - t_tick) >= 1000) {
    uint8_t d[8] = {0}; d[2] = 0; send_frame(0x0101, d);
    t_state = 0;
  }
}

/* ---------------- MPU6050 ---------------- */
static uint8_t mpu_init(void)
{
  uint8_t who = 0, v;
  if (HAL_I2C_Mem_Read(&hi2c1, MPU_ADDR, 0x75, I2C_MEMADD_SIZE_8BIT, &who, 1, 50) != HAL_OK) return 0;
  if (who != 0x68) return 0;
  v = 0x00; HAL_I2C_Mem_Write(&hi2c1, MPU_ADDR, 0x6B, I2C_MEMADD_SIZE_8BIT, &v, 1, 50); /* wake, internal osc */
  HAL_Delay(50);
  v = 0x01; HAL_I2C_Mem_Write(&hi2c1, MPU_ADDR, 0x1A, I2C_MEMADD_SIZE_8BIT, &v, 1, 50); /* DLPF 184 Hz -> 1 kHz base rate */
  v = 0x00; HAL_I2C_Mem_Write(&hi2c1, MPU_ADDR, 0x19, I2C_MEMADD_SIZE_8BIT, &v, 1, 50); /* SMPLRT_DIV=0 */
  v = 0x00; HAL_I2C_Mem_Write(&hi2c1, MPU_ADDR, 0x1C, I2C_MEMADD_SIZE_8BIT, &v, 1, 50); /* +-2 g */
  return 1;
}

/* ---------------- ISR-side callbacks ---------------- */
void HAL_TIM_PeriodElapsedCallback(TIM_HandleTypeDef *htim)
{
  if (htim->Instance == TIM7) {                 /* 1 kHz sample tick */
    if (hi2c1.State != HAL_I2C_STATE_READY) { missed++; return; }
    if (HAL_I2C_Mem_Read_DMA(&hi2c1, MPU_ADDR, 0x3B, I2C_MEMADD_SIZE_8BIT, dma_buf, 6) != HAL_OK) missed++;
  } else if (htim->Instance == TIM3) {          /* tach timer overflow */
    tach_ovf++;
  }
}

void HAL_I2C_MemRxCpltCallback(I2C_HandleTypeDef *hi2c)
{
  if (hi2c->Instance != I2C1) return;
  int16_t *s = win[w_active][w_idx];
  s[0] = (int16_t)((dma_buf[0] << 8) | dma_buf[1]);
  s[1] = (int16_t)((dma_buf[2] << 8) | dma_buf[3]);
  s[2] = (int16_t)((dma_buf[4] << 8) | dma_buf[5]);
  if (++w_idx >= N) {
    if (w_ready) overrun++;
    w_ready = (uint8_t)(w_active + 1);
    w_active ^= 1;
    w_idx = 0;
  }
}

void HAL_I2C_ErrorCallback(I2C_HandleTypeDef *hi2c)
{
  if (hi2c->Instance == I2C1) i2c_err++;
}

void HAL_TIM_IC_CaptureCallback(TIM_HandleTypeDef *htim)
{
  if (htim->Instance != TIM3 || htim->Channel != HAL_TIM_ACTIVE_CHANNEL_1) return;
  uint32_t now = HAL_TIM_ReadCapturedValue(htim, TIM_CHANNEL_1);
  if (tach_have_last) {
    int32_t d = (int32_t)(tach_ovf * 65536u) + (int32_t)now - (int32_t)tach_last;
    if (d > 1000) {                                      /* ignore >60k RPM glitches */
      uint32_t r = 60000000u / ((uint32_t)d * TACH_PPR);
      tach_rpm = (uint16_t)(r > 65535u ? 65535u : r);
      tach_tick = HAL_GetTick();
    }
  }
  tach_have_last = 1;
  tach_last = now;
  tach_ovf = 0;
}

void HAL_UART_RxCpltCallback(UART_HandleTypeDef *huart)
{
  if (huart->Instance != USART1) return;
  if (rx_idx == 0 && rx_byte != 0xA5) { HAL_UART_Receive_IT(&huart1, &rx_byte, 1); return; }
  rx_buf[rx_idx++] = rx_byte;
  if (rx_idx == sizeof rx_buf) {
    if (crc8(&rx_buf[1], 10) == rx_buf[11]) {
      uint16_t id = (uint16_t)((rx_buf[1] << 8) | rx_buf[2]);
      if (id == 0x0200 && rx_buf[3] <= 100) pwm_req = rx_buf[3];
      rx_idx = 0;
    } else {                                             /* resync on next 0xA5 inside buffer */
      uint8_t k = 1;
      while (k < sizeof rx_buf && rx_buf[k] != 0xA5) k++;
      rx_idx = (uint8_t)(sizeof rx_buf - k);
      memmove(rx_buf, &rx_buf[k], rx_idx);
    }
  }
  HAL_UART_Receive_IT(&huart1, &rx_byte, 1);
}

/* ---------------- window processing ---------------- */
static void process_window(const int16_t (*b)[3])
{
  float rms2 = 0.0f;
  memset(pwr, 0, sizeof pwr);
  for (uint8_t ax = 0; ax < 3; ax++) {
    float mean = 0.0f;
    for (uint16_t i = 0; i < N; i++) mean += (float)b[i][ax];
    mean /= (float)N;
    for (uint16_t i = 0; i < N; i++) {
      float v = ((float)b[i][ax] - mean) * (1.0f / ACC_LSB_PER_G);
      rms2 += v * v;
      fft_in[i] = v * hann[i];
    }
    arm_rfft_fast_f32(&rfft, fft_in, fft_out, 0);
    arm_cmplx_mag_squared_f32(fft_out, mag2, N / 2);
    for (uint16_t k = 0; k < N / 2; k++) pwr[k] += mag2[k];
  }
  float rms = sqrtf(rms2 / (float)N);

  uint16_t kmin = (uint16_t)((F_MIN_HZ * N + FS_HZ - 1) / FS_HZ);
  uint16_t kmax = (uint16_t)((F_MAX_HZ * N) / FS_HZ);
  uint16_t kp = kmin;
  for (uint16_t k = kmin; k <= kmax; k++) if (pwr[k] > pwr[kp]) kp = k;

  float a = sqrtf(pwr[kp - 1]), c0 = sqrtf(pwr[kp]), c = sqrtf(pwr[kp + 1]);
  float den = a - 2.0f * c0 + c;
  float delta = (den != 0.0f) ? 0.5f * (a - c) / den : 0.0f;
  if (delta > 0.5f) delta = 0.5f; else if (delta < -0.5f) delta = -0.5f;
  float amp_g = 4.0f * c0 / (float)N;                    /* Hann coherent gain 0.5 */
  float freq = ((float)kp + delta) * (float)FS_HZ / (float)N;
  uint16_t rpm = 0;
  if (amp_g >= AMP_MIN_G) rpm = (uint16_t)(freq * 60.0f + 0.5f); else freq = 0.0f;

  /* baseline + alarm */
  if (pwm_cmd == 0) {
    base_ready = 0; base_n = 0; base_rms_sum = base_amp_sum = 0; vib_alarm = 0; bad_cnt = good_cnt = 0;
  } else if (!base_ready) {
    base_rms_sum += rms; base_amp_sum += amp_g;
    if (++base_n >= BASE_WINDOWS) {
      base_rms = base_rms_sum / base_n; if (base_rms < 0.002f) base_rms = 0.002f;
      base_amp = base_amp_sum / base_n; if (base_amp < AMP_MIN_G) base_amp = AMP_MIN_G;
      base_ready = 1;
    }
  } else {
    uint8_t over = (rms > K_ALARM * base_rms) || (amp_g > K_ALARM * base_amp);
    if (over) { bad_cnt++; good_cnt = 0; } else { good_cnt++; bad_cnt = 0; }
    if (bad_cnt >= 2) vib_alarm = 1;
    if (good_cnt >= 3) vib_alarm = 0;
  }

  uint8_t d[8];
  put16(&d[0], (uint16_t)(rms * 1000.0f));
  put16(&d[2], (uint16_t)(freq * 100.0f));
  put16(&d[4], rpm);
  put16(&d[6], (uint16_t)(amp_g * 1000.0f));
  send_frame(0x0100, d);

  uint32_t now = HAL_GetTick();
  if ((now - tach_tick) > 1500) tach_rpm = 0;
  d[0] = (uint8_t)(vib_alarm | (temp_alarm << 1) | (base_ready << 2) | (temp_valid << 3) | ((!sensor_ok) << 4));
  d[1] = base_ready ? 100 : (uint8_t)((base_n * 100u) / BASE_WINDOWS);
  put16(&d[2], tach_rpm);
  put16(&d[4], (uint16_t)(missed));
  put16(&d[6], (uint16_t)(i2c_err));
  send_frame(0x01FF, d);
}

/* ---------------- public ---------------- */
void app_init(void)
{
  /* priorities: sample tick > tach capture > I2C/DMA > UART */
  HAL_NVIC_SetPriority(TIM7_IRQn, 0, 0);
  HAL_NVIC_SetPriority(TIM3_IRQn, 1, 0);
  HAL_NVIC_SetPriority(I2C1_EV_IRQn, 2, 0);
  HAL_NVIC_SetPriority(I2C1_ER_IRQn, 2, 0);
  HAL_NVIC_SetPriority(DMA1_Stream0_IRQn, 2, 0);
  HAL_NVIC_SetPriority(USART1_IRQn, 3, 0);
  HAL_NVIC_EnableIRQ(USART1_IRQn);

  for (uint16_t i = 0; i < N; i++) hann[i] = 0.5f - 0.5f * cosf(2.0f * 3.14159265f * (float)i / (float)(N - 1));
  arm_rfft_fast_init_f32(&rfft, N);

  /* motor: PWM off, direction forward (PB4=1, PB5=0 -> check against your L298N wiring) */
  HAL_GPIO_WritePin(GPIOB, GPIO_PIN_4, GPIO_PIN_SET);
  HAL_GPIO_WritePin(GPIOB, GPIO_PIN_5, GPIO_PIN_RESET);
  __HAL_TIM_SET_COMPARE(&htim1, TIM_CHANNEL_1, 0);
  HAL_TIM_PWM_Start(&htim1, TIM_CHANNEL_1);

  HAL_TIM_Base_Start(&htim6);                           /* 1 MHz free-run for us_delay */
  __HAL_TIM_ENABLE_IT(&htim3, TIM_IT_UPDATE);
  HAL_TIM_IC_Start_IT(&htim3, TIM_CHANNEL_1);

  HAL_UART_Receive_IT(&huart1, &rx_byte, 1);

  sensor_ok = mpu_init();
  if (sensor_ok) HAL_TIM_Base_Start_IT(&htim7);
}

void app_loop(void)
{
  if (pwm_req != pwm_cmd) {                             /* apply command, relearn baseline */
    pwm_cmd = pwm_req;
    __HAL_TIM_SET_COMPARE(&htim1, TIM_CHANNEL_1, (uint32_t)pwm_cmd * (PWM_ARR + 1u) / 100u);
    base_ready = 0; base_n = 0; base_rms_sum = base_amp_sum = 0; vib_alarm = 0; bad_cnt = good_cnt = 0;
  }
  if (w_ready) {
    uint8_t idx = (uint8_t)(w_ready - 1);
    process_window((const int16_t (*)[3])win[idx]);
    w_ready = 0;
  }
  temp_service();
}
