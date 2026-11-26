#ifndef APP_H
#define APP_H

/* Call once after MX_*_Init(), then call app_loop() from the main while(1). */
void app_init(void);
void app_loop(void);

/* Called from USART1_IRQHandler path (HAL callbacks live in app.c). */

#endif
