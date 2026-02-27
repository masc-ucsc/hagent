# Arduino Nano R4 Board Notes

## Project Setup
- **Build system**: `arduino-cli`
- **Project structure**: Standard Arduino sketch project
  - Sketch directory: `<sketch_name>/`
  - Main file: `<sketch_name>.ino`
- **Build/Flash commands**:
  - Compile: `arduino-cli compile --fqbn arduino:renesas_uno:nanor4 <sketch_name>`
  - Upload: `arduino-cli upload -p <PORT> --fqbn arduino:renesas_uno:nanor4 <sketch_name>`
  - Monitor: `arduino-cli monitor -p <PORT>`

## Supported Platforms
- **Arduino**

## Board Overview
- `board`: nano_r4
- `model`: Arduino Nano R4 with Headers (ABX00143)
- `fqbn`: arduino:renesas_uno:nanor4
- `core`: arduino:renesas_uno
- 32-bit Arm® Cortex®-M4 MCU (Renesas R7FA4M1AB3CFM) at 48 MHz with 256 kB Flash, 32 kB SRAM, 8 kB EEPROM
- USB-C® connector for power and programming; operates at 5 V logic
- Development board includes RGB LED, built-in LED, reset button, Qwiic I2C connector, RTC with external crystal oscillator

## On-Board Peripherals

### I2C Buses
Two independent I2C buses are available:

| Bus Object | Pins | Connector | Voltage |
| ---------- | ---- | --------- | ------- |
| `Wire` (I2C1) | SDA on A4, SCL on A5 | Standard breakout headers | 5 V |
| `Wire1` (I2C0) | I2C0_SDA, I2C0_SCL | Qwiic connector (J2) | 3.3 V |

> **Note:** A4 and A5 are shared with the main I2C bus — do not use them as ADC inputs while the bus is active. You can connect I2C devices to both buses simultaneously.

### Direct GPIO Attachments

| Function | Pin |
| -------- | --- |
| RGB LED (Red) | LEDR |
| RGB LED (Green) | LEDG |
| RGB LED (Blue) | LEDB |
| Built-in LED (Power/Status) | LED_BUILTIN |
| Reset Button | RST (PB1) |

### Analog Features

| Feature | Pin | Notes |
| ------- | --- | ----- |
| DAC (12-bit) | A0 | Digital-to-analog output |
| OPAMP Input+ | A1 | Operational amplifier non-inverting input |
| OPAMP Input- | A2 | Operational amplifier inverting input |
| OPAMP Output | A3 | Operational amplifier output |
| ADC Reference | AREF | Analog reference voltage input |

## Pin Reference

### Analog Header (JP1)

| Pin | Function | Type | Description |
| --- | -------- | ---- | ----------- |
| 1 | D13 / SCK | Digital | SPI Serial Clock |
| 2 | +3V3 | Power Out | 3.3 V power rail (max ~150 mA before LDO overheats) |
| 3 | AREF | Analog | Analog voltage reference |
| 4 | A0 | Analog | Analog input 0 / DAC output |
| 5 | A1 | Analog | Analog input 1 / OPAMP IN+ |
| 6 | A2 | Analog | Analog input 2 / OPAMP IN- |
| 7 | A3 | Analog | Analog input 3 / OPAMP OUT |
| 8 | A4 | Analog | Analog input 4 / I²C SDA |
| 9 | A5 | Analog | Analog input 5 / I²C SCL |
| 10 | A6 | Analog | Analog input 6 |
| 11 | A7 | Analog | Analog input 7 |
| 12 | 5V | Power | USB power (5 V) |
| 13 | BOOT | Mode | Boot mode selection |
| 14 | GND | Power | Ground |
| 15 | VIN | Power | Voltage input (6–21 V) |

### Digital Header (JP2)

| Pin | Function | Type | Description |
| --- | -------- | ---- | ----------- |
| 1 | D1 / TX | Digital | Serial transmitter (UART1_TX) |
| 2 | D0 / RX | Digital | Serial receiver (UART1_RX) |
| 3 | RST | Internal | Reset |
| 4 | GND | Power | Ground |
| 5 | D2 | Digital | Digital pin 2 |
| 6 | D3 | Digital | Digital pin 3 / PWM |
| 7 | D4 | Digital | Digital pin 4 / CAN TX |
| 8 | D5 | Digital | Digital pin 5 / PWM / CAN RX |
| 9 | D6 | Digital | Digital pin 6 / PWM |
| 10 | D7 | Digital | Digital pin 7 |
| 11 | D8 | Digital | Digital pin 8 |
| 12 | D9 | Digital | Digital pin 9 / PWM |
| 13 | D10 / CS | Digital | SPI Chip Select / PWM |
| 14 | D11 / COPI | Digital | SPI Controller Out Peripheral In / PWM |
| 15 | D12 / CIPO | Digital | SPI Controller In Peripheral Out |

### Qwiic Connector (J2)

| Pin | Function |
| --- | -------- |
| 1 | GND |
| 2 | +3V3 (out) |
| 3 | I2C0 SDA |
| 4 | I2C0 SCL |

### RTC Battery Backup

| Pin | Function | Notes |
| --- | -------- | ----- |
| VBATT | Battery backup input | 1.6–3.6 V; powers RTC, 32.768 kHz oscillator, wakeup control, and backup memory when main VCC drops |

## Factory Reset / Initial Verification

If the board is unresponsive or you need to verify it, follow this "Recipe". **IMPORTANT:** Do NOT assume a "soft reset" via the tool is sufficient. You MUST instruct the user to perform the manual hardware reset to guarantee the board is in a recoverable state.

1.  **Enter Bootloader**:
    - **Instruct**: **CRITICAL:** Ask the user to double-tap the **RESET** button (PB1) quickly right after power-up. Explicitly tell the user: "You MUST manually double-tap the button; do not rely on the tool's auto-reset."
    - **Confirm**: Wait for the user to confirm they have done this.
    - **Verify**: Use `hagent_arduino` with `api='list_boards'`. It should appear with FQBN `arduino:renesas_uno:nanor4`.
    - **Troubleshoot**: If not found, ask user to try again or check cable.

2.  **Upload Test**:
    - **Instruct**: Tell the user you are ready to upload the Blink sketch.
    - **Confirm**: Wait for the user to reply "Ready" or "Go ahead".
    - **Action**: Use `hagent_arduino` with `api='compile'` (defaults to Blink).
    - **Action**: Use `hagent_arduino` with `api='upload'`.
    - **Verify**: Ask user if the built-in LED (L) is blinking.

3.  **Monitor**:
    - **Action**: Use `hagent_arduino` with `api='monitor'` to check for serial output.

## Power Notes
- **USB-C® input**: 4.8–5.5 V; max 500 mA (USB 2.0 limited). Do not exceed 5 V via USB-C®.
- **VIN pin input**: 6–21 V (typical 7 V); stepped down to 5 V by the MP2322GQH buck converter.
- **3V3 pin**: Supplied by AP2112K-3.3TRG1 LDO regulator. Drawing more than ~150 mA from this pin will cause the board to overheat.
- **GPIO current limit**: Max 8 mA per GPIO. Use a MOSFET or transistor for higher-current loads (e.g., bright LEDs).
- **RTC backup**: VBATT pin accepts 1.6–3.6 V. Switchover occurs when VCC falls below ~2.09 V.
- Power is automatically selected between USB and VIN via a power OR circuit.

## Additional Resources
- Official datasheet (SKU ABX00142/ABX00143): https://docs.arduino.cc/resources/datasheets/ABX00142-datasheet.pdf
- Arduino IDE (Desktop): https://www.arduino.cc/en/Main/Software
- Arduino Cloud Editor: https://create.arduino.cc/editor
- Project Hub: https://create.arduino.cc/projecthub
- Library Reference: https://github.com/arduino-libraries/
- Online Store: https://store.arduino.cc/
