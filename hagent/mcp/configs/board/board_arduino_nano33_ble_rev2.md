# Arduino Nano 33 BLE Rev2 Board Notes

## Project Setup
- **Build system**: `arduino-cli`
- **Project structure**: Standard Arduino sketch project
  - Sketch directory: `<sketch_name>/`
  - Main file: `<sketch_name>.ino`
- **Build/Flash commands**:
  - Compile: `arduino-cli compile --fqbn arduino:mbed_nano:nano33ble <sketch_name>`
  - Upload: `arduino-cli upload -p <PORT> --fqbn arduino:mbed_nano:nano33ble <sketch_name>`
  - Monitor: `arduino-cli monitor -p <PORT>`

## Board Overview
- `board`: nano33ble_rev2
- `model`: Arduino Nano 33 BLE Rev2 without headers (ABX00071) / with headers (ABX00072)
- `fqbn`: arduino:mbed_nano:nano33ble
- `core`: arduino:mbed_nano
- 64 MHz Arm® Cortex®-M4F (with FPU) via NINA-B306 module (Nordic nRF52480); 1 MB Flash, 256 kB RAM
- Micro-B USB connector for power and programming; operates at **3.3 V logic only — NOT 5 V tolerant**
- Board includes RGB LED, built-in LED (DL1), reset button (PB1), 9-axis IMU (BMI270 + BMM150), Bluetooth® 5, IEEE 802.15.4 (Thread/Zigbee®)

> **CRITICAL:** Nano 33 BLE Rev2 only supports 3.3 V I/Os and is NOT 5 V tolerant. Do not connect 5 V signals directly to this board or it will be damaged.

## On-Board Peripherals

### IMU (9-axis)

| IC | Function | Details |
| -- | -------- | ------- |
| BMI270 | 3-axis Accelerometer + 3-axis Gyroscope | Accel: ±2g/±4g/±8g/±16g; Gyro: ±125–±2000 dps; 16-bit |
| BMM150 | 3-axis Magnetometer | 0.3 µT resolution; ±1300 µT (x,y), ±2500 µT (z) |

### I2C Bus

| Bus | Pins | Notes |
| --- | ---- | ----- |
| I2C (SDA/SCL) | A4 / A5 | Internal pull-up present; default usage is I2C — **not recommended as analog inputs** |

### Direct GPIO Attachments

| Function | Pin / Define |
| -------- | ------------ |
| RGB LED (Red) | P0.24 / `LEDR` |
| RGB LED (Green) | P0.16 / `LEDG` |
| RGB LED (Blue) | P0.06 / `LEGB` |
| Built-in LED | P0.13 / `LED_BUILTIN` |
| Reset Button | PB1 |

### Wireless

| Feature | Details |
| ------- | ------- |
| Bluetooth® 5 | 2 Mbps, Long Range, Advertising Extensions; +8 dBm TX, -95 dBm sensitivity |
| IEEE 802.15.4 | Thread, Zigbee® |
| NFC-A tag | Supported via NINA-B306 |

### Other Processor Peripherals (NINA-B306 / nRF52480)

| Feature | Details |
| ------- | ------- |
| ADC | 12-bit, 200 ksps |
| USB | Full-speed 12 Mbps |
| SPI | High-speed 32 MHz; Quad SPI 32 MHz |
| Serial interfaces | QSPI / SPI / TWI / I²S / PDM / QDEC |
| Security | Arm® CryptoCell CC310; 128-bit AES/ECB/CCM/AAR co-processor |
| DMA | EasyDMA for all digital interfaces |

## Pin Reference

### Left Header (Analog Side)

| Pin | Function | Type | Description |
| --- | -------- | ---- | ----------- |
| 1 | D13 / SCK | Digital | SPI Serial Clock (P0.13) |
| 2 | +3V3 | Power Out | Internally generated 3.3 V output |
| 3 | AREF | Analog | Analog reference; can be used as GPIO |
| 4 | A0 / DAC0 | Analog | ADC in / DAC out; can be used as GPIO |
| 5 | A1 | Analog | ADC in; can be used as GPIO |
| 6 | A2 | Analog | ADC in; can be used as GPIO |
| 7 | A3 | Analog | ADC in; can be used as GPIO |
| 8 | A4 / SDA | Analog | ADC in; I2C SDA; internal pull-up (1) |
| 9 | A5 / SCL | Analog | ADC in; I2C SCL; internal pull-up (1) |
| 10 | A6 | Analog | ADC in; can be used as GPIO |
| 11 | A7 | Analog | ADC in; can be used as GPIO |
| 12 | VUSB | Power In/Out | Normally NC; can be connected to USB VUSB pin via jumper |
| 13 | RST | Digital In | Active low reset input |
| 14 | GND | Power | Ground |
| 15 | VIN | Power In | Voltage input |

> (1) A4 and A5 have internal pull-ups and default to I2C — usage as analog inputs is not recommended.

### Right Header (Digital Side)

| Pin | Function | Type | Description |
| --- | -------- | ---- | ----------- |
| 16 | D0 / TX | Digital | USART TX; can be used as GPIO (P1.03) |
| 17 | D1 / RX | Digital | USART RX; can be used as GPIO (P1.10) |
| 18 | RST | Digital In | Active low reset input (duplicate) |
| 19 | GND | Power | Ground |
| 20 | D2 | Digital | GPIO (P1.11) |
| 21 | D3 / PWM | Digital | GPIO; PWM (P1.12) |
| 22 | D4 | Digital | GPIO (P1.15) |
| 23 | D5 / PWM | Digital | GPIO; PWM (P1.13) |
| 24 | D6 / PWM | Digital | GPIO; PWM (P1.14) |
| 25 | D7 | Digital | GPIO (P0.23) |
| 26 | D8 | Digital | GPIO (P0.21) |
| 27 | D9 / PWM | Digital | GPIO; PWM (P0.27) |
| 28 | D10 / PWM | Digital | GPIO; PWM (P1.02) |
| 29 | D11 / MOSI | Digital | SPI MOSI; can be used as GPIO (P1.01) |
| 30 | D12 / MISO | Digital | SPI MISO; can be used as GPIO (P1.08) |

### USB Connector

| Pin | Function | Type | Description |
| --- | -------- | ---- | ----------- |
| 1 | VUSB | Power | Power supply input (output if powered via header VUSB) |
| 2 | D- | Differential | USB differential data − |
| 3 | D+ | Differential | USB differential data + |
| 4 | ID | Analog | Selects Host/Device functionality |
| 5 | GND | Power | Ground |

### Debug Pads (Bottom, 3×2, 100 mil pitch, pin 4 removed)

| Pin | Function | Type | Description |
| --- | -------- | ---- | ----------- |
| 1 | +3V3 | Power Out | Voltage reference |
| 2 | SWD | Digital | nRF52480 Single Wire Debug Data |
| 3 | SWCLK | Digital In | nRF52480 Single Wire Debug Clock |
| 5 | GND | Power | Ground |
| 6 | RST | Digital In | Active low reset input |

## Factory Reset / Initial Verification

If the board is unresponsive or you need to verify it, follow this "Recipe". **IMPORTANT:** Do NOT assume a "soft reset" via the tool is sufficient. You MUST instruct the user to perform the manual hardware reset to guarantee the board is in a recoverable state.

1. **Enter Bootloader**:
   - **Instruct**: **CRITICAL:** Ask the user to double-tap the **RESET** button (PB1) quickly right after power-up. Explicitly tell the user: "You MUST manually double-tap the button; do not rely on the tool's auto-reset."
   - **Confirm**: Wait for the user to confirm they have done this.
   - **Verify**: Use `hagent_arduino` with `api='list_boards'`. It should appear with the correct FQBN.
   - **Troubleshoot**: If not found, ask user to try again or check cable.

2. **Upload Test**:
   - **Instruct**: Tell the user you are ready to upload the Blink sketch.
   - **Confirm**: Wait for the user to reply "Ready" or "Go ahead".
   - **Action**: Use `hagent_arduino` with `api='compile'` (defaults to Blink).
   - **Action**: Use `hagent_arduino` with `api='upload'`.
   - **Verify**: Ask user if the built-in LED (L) is blinking.

3. **Monitor**:
   - **Action**: Use `hagent_arduino` with `api='monitor'` to check for serial output.

## Power Notes
- **USB (Micro-B) input**: Minimum 4.8–4.96 V (due to Schottky diode drop into DC-DC); board powered via USB connector or VUSB/VIN header pins.
- **VIN pin input**: Up to 21 V; stepped down by MP2322GQH DC-DC converter (≥65% efficiency at minimum load, >85% at 12 V).
- **3V3 pin**: Internally generated 3.3 V output.
- **5V pin**: Does NOT supply 5 V — it is connected (via jumper SJ5) to the USB power input (VUSB), not a regulated 5 V rail.
- **I/O voltage**: 3.3 V only. **NOT 5 V tolerant.** Applying 5 V signals will damage the board.
- **Operating temperature**: −40 °C to 85 °C.

## Additional Resources
- Arduino IDE (Desktop): https://www.arduino.cc/en/software
- Arduino Cloud Editor: https://create.arduino.cc/editor
- Arduino Cloud Editor - Getting Started: https://docs.arduino.cc/arduino-cloud/guides/editor/
- Arduino Project Hub: https://create.arduino.cc/projecthub?by=part&part_id=11332&sort=trending
- Library Reference: https://www.arduino.cc/reference/en/
- Forum: http://forum.arduino.cc/
- NINA-B306 Datasheet: https://content.u-blox.com/sites/default/files/NINA-B3_DataSheet_UBX17052099.pdf
