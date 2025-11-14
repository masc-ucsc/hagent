#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "driver/gpio.h"

#define LED_GPIO 7
#define BLNK_FREQ_MS 500 

void blink_task(void *pvParameter)
{
    // Reset the pin to a default state (good practice)
    gpio_reset_pin(LED_GPIO);
    
    // Set the GPIO as a push-pull output
    gpio_set_direction(LED_GPIO, GPIO_MODE_OUTPUT);
    
    // Count the number of times the LED has blinked
    int count = 0;

    while(1) {
        gpio_set_level(LED_GPIO, 0);
        vTaskDelay(BLNK_FREQ_MS / portTICK_PERIOD_MS);
        gpio_set_level(LED_GPIO, 1);
        vTaskDelay(BLNK_FREQ_MS / portTICK_PERIOD_MS);
        count++;
        printf("The LED has blinked %d times\n", count);
    }
}

void app_main()
{
    xTaskCreate(blink_task, "blink_task", 2048, NULL, 5, NULL);
}

