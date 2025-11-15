# Board: ESP32-C3-DevKit-RUST-1

## Model
- ESP32 Model: esp32c3

## GPIO Mapping

| Function | GPIO Pin | Notes |
|----------|----------|-------|
| LED | GPIO7 | Built-in LED |
| WS2812 | GPIO2 | Addressable RGB LED |
| Button | GPIO9 | Boot button, active low |
| I2C_SDA | GPIO10 | Shared with IMU and temp/humidity sensor |
| I2C_SCL | GPIO8 | Shared with IMU and temp/humidity sensor |
| UART_RX | GPIO21 | UART0 RX |
| UART_TX | GPIO20 | UART0 TX |
| USB_DN | GPIO18 | USB data negative |
| USB_DP | GPIO19 | USB data positive |
| ADC1_CH0 | GPIO0 | Analog input |
| ADC1_CH1 | GPIO1 | Analog input |
| ADC1_CH2 | GPIO2 | Analog input (shared with WS2812) |
| ADC1_CH3 | GPIO3 | Analog input |
| ADC2_CH0 | GPIO4 | Analog input |
| ADC2_CH1 | GPIO5 | Analog input |

## Reference
- URL: https://github.com/esp-rs/esp-rust-board
- Purchase: https://www.aliexpress.com/item/1005004418342288.html

## Example Usage

```c
// LED control example
#include "driver/gpio.h"

gpio_set_direction(GPIO_NUM_7, GPIO_MODE_OUTPUT);
gpio_set_level(GPIO_NUM_7, 1);  // Turn on LED
```

```c
// Button reading example
#include "driver/gpio.h"

gpio_set_direction(GPIO_NUM_9, GPIO_MODE_INPUT);
gpio_set_pull_mode(GPIO_NUM_9, GPIO_PULLUP_ONLY);

int button_state = gpio_get_level(GPIO_NUM_9);
if (button_state == 0) {
    // Button is pressed
}
```

```c
// I2C initialization example
#include "driver/i2c.h"

#define I2C_MASTER_SCL_IO    8
#define I2C_MASTER_SDA_IO    10
#define I2C_MASTER_FREQ_HZ   100000

i2c_config_t conf = {
    .mode = I2C_MODE_MASTER,
    .sda_io_num = I2C_MASTER_SDA_IO,
    .scl_io_num = I2C_MASTER_SCL_IO,
    .sda_pullup_en = GPIO_PULLUP_ENABLE,
    .scl_pullup_en = GPIO_PULLUP_ENABLE,
    .master.clk_speed = I2C_MASTER_FREQ_HZ,
};
i2c_param_config(I2C_NUM_0, &conf);
i2c_driver_install(I2C_NUM_0, conf.mode, 0, 0, 0);
```