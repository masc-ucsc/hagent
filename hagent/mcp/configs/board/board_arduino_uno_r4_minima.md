# Arduino UNO R4 Minima Board Notes

## Project Setup
- **Build system**: `arduino-cli`
- **Project structure**: Standard Arduino sketch project
  - Sketch directory: `<sketch_name>/`
  - Main file: `<sketch_name>.ino`
- **Build/Flash commands**:
  - Compile: `arduino-cli compile --fqbn arduino:renesas_uno:minima <sketch_name>`
  - Upload: `arduino-cli upload -p <PORT> --fqbn arduino:renesas_uno:minima <sketch_name>`
  - Monitor: `arduino-cli monitor -p <PORT>`

## Supported Platforms
- **Arduino**

## Board Overview
- `board`: uno_r4_minima
- `model`: Arduino UNO R4 Minima (ABX00080)
- `fqbn`: arduino:renesas_uno:minima
- `core`: arduino:renesas_uno
- 32-bit Arm® Cortex®-M4 MCU (Renesas R7FA4M1AB3CFM#AA0) at 48 MHz with 256 kB Flash, 32 kB SRAM, 8 kB EEPROM (data flash)
- USB-C® connector for power and programming; operates at 5 V logic
- Development board includes TX/RX/Power/SCK LEDs, reset button, barrel jack (DC Jack), ICSP header, SWD/JTAG connector

## On-Board Peripherals

### I2C Bus
One I2C bus is available via two sets of pins:

| Bus | Pins | Notes |
| --- | ---- | ----- |
| I2C (Wire) | A4 (SDA), A5 (SCL) | Analog header; 5 V |
| I2C (Wire) | D18 (SDA), D19 (SCL) | Dedicated digital header pins; 5 V |

> **Note:** A4/A5 are shared with the I2C bus — do not use them as ADC inputs while the bus is active.

### Direct GPIO Attachments

| Function | Reference |
| -------- | --------- |
| Built-in LED | LED_BUILTIN (P111) |
| TX LED | DL1 (P012) |
| RX LED | DL2 (P013) |
| Power LED | DL3 |
| SCK LED | DL4 |
| Reset Button | PB1 (RST) |

### Analog Features

| Feature | Pin | Notes |
| ------- | --- | ----- |
| DAC (12-bit) | A0 | Digital-to-analog output (P014) |
| OPAMP Input+ | A1 | Operational amplifier non-inverting input (P000) |
| OPAMP Input- | A2 | Operational amplifier inverting input (P001) |
| OPAMP Output | A3 | Operational amplifier output (P002) |
| ADC | A0–A5 | Up to 14-bit resolution |
| ADC Reference | AREF | Analog reference voltage input |

### Communication Interfaces

| Interface | Pins | Notes |
| --------- | ---- | ----- |
| UART | D0 (RX), D1 (TX) | Serial0 |
| SPI | D10 (CS), D11 (COPI), D12 (CIPO), D13 (SCK) | Also available on ICSP header |
| I2C | A4 (SDA), A5 (SCL) / D18 (SDA), D19 (SCL) | |
| CAN | D4 (CANTX0), D5 (CANRX0) | External transceiver required |

## Pin Reference

### Analog Header (JANALOG)

| Pin | Function | Type | Description |
| --- | -------- | ---- | ----------- |
| 1 | BOOT | Mode | Mode selection |
| 2 | IOREF | Reference | Digital logic voltage reference — connected to 5 V |
| 3 | RESET | Reset | Reset |
| 4 | +3V3 | Power Out | 3.3 V power rail |
| 5 | +5V | Power Out | 5 V power rail |
| 6 | GND | Power | Ground |
| 7 | GND | Power | Ground |
| 8 | VIN | Power In | Voltage input (6–24 V) |
| 9 | A0 | Analog | Analog input 0 / DAC |
| 10 | A1 | Analog | Analog input 1 / OPAMP+ |
| 11 | A2 | Analog | Analog input 2 / OPAMP- |
| 12 | A3 | Analog | Analog input 3 / OPAMPOut |
| 13 | A4 | Analog | Analog input 4 / I²C SDA |
| 14 | A5 | Analog | Analog input 5 / I²C SCL |

### Digital Header (JDIGITAL)

| Pin | Function | Type | Description |
| --- | -------- | ---- | ----------- |
| 1 | SCL / D19 | Digital | I²C Serial Clock |
| 2 | SDA / D18 | Digital | I²C Serial Data |
| 3 | AREF | Analog | Analog Reference Voltage |
| 4 | GND | Power | Ground |
| 5 | D13 / SCK | Digital | GPIO 13 / SPI Clock |
| 6 | D12 / CIPO | Digital | GPIO 12 / SPI Controller In Peripheral Out |
| 7 | D11 / COPI | Digital | GPIO 11 (PWM) / SPI Controller Out Peripheral In |
| 8 | D10 / CS | Digital | GPIO 10 (PWM) / SPI Chip Select |
| 9 | D9 | Digital | GPIO 9 (PWM~) |
| 10 | D8 | Digital | GPIO 8 |
| 11 | D7 | Digital | GPIO 7 |
| 12 | D6 | Digital | GPIO 6 (PWM~) |
| 13 | D5 / CANRX0 | Digital | GPIO 5 (PWM~) / CAN Transmitter (TX) |
| 14 | D4 / CANTX0 | Digital | GPIO 4 / CAN Receiver (RX) |
| 15 | D3 | Digital | GPIO 3 (PWM~) / Interrupt Pin |
| 16 | D2 | Digital | GPIO 2 / Interrupt Pin |
| 17 | D1 / TX0 | Digital | GPIO 1 / Serial 0 Transmitter (TX) |
| 18 | D0 / RX0 | Digital | GPIO 0 / Serial 0 Receiver (RX) |

### ICSP Header (J1)

| Pin | Function | Type | Description |
| --- | -------- | ---- | ----------- |
| 1 | CIPO | Internal | Controller In Peripheral Out |
| 2 | +5V | Internal | Power Supply of 5 V |
| 3 | SCK | Internal | Serial Clock |
| 4 | COPI | Internal | Controller Out Peripheral In |
| 5 | RESET | Internal | Reset |
| 6 | GND | Internal | Ground |

### SWD/JTAG Connector (J2)

| Pin | Function | Type | Description |
| --- | -------- | ---- | ----------- |
| 1 | +5V | Internal | Power Supply of 5 V |
| 2 | SWDIO | Internal | Data I/O pin |
| 3 | GND | Internal | Ground |
| 4 | SWCLK | Internal | Clock Pin |
| 5 | GND | Internal | Ground |
| 6 | NC | Internal | Not connected |
| 7 | RX | Internal | Serial Receiver |
| 8 | TX | Internal | Serial Transmitter |
| 9 | GND | Internal | Ground |
| 10 | NC | Internal | Not connected |

## Factory Reset / Board Recovery

If the board is unresponsive or not reachable via USB, it can be recovered using the built-in bootloader:

1. Double-tap the **RESET** button (PB1) right after power-up to enter bootloader mode.
2. Once in bootloader mode, the board can be re-flashed via USB.

## Power Notes
- **USB-C® input**: 4.8–5.5 V. Do not power the board with more than 5 V via the USB-C® port.
- **VIN pin / Barrel jack (J4)**: 6–24 V (typical 7 V); stepped down to 5 V by the ISL854102FRZ buck converter. Max converter output: 48 V / 1.2 A.
- **3V3 pin**: Draws power from the VCC_USB pin on the R7FA4M1AB3CFM#AA0; not connected to the buck converter.
- **GPIO current limit**: Max 8 mA per GPIO. Use a MOSFET or transistor for higher-current loads (e.g., servo motors).
- **Rated current (USB-C, blink firmware)**: ~29.71 mA min / ~33.39 mA typical / ~36.98 mA max.
- **Schottky diodes** (D2, D3: PMEG6020AELRX) provide reverse polarity and overvoltage protection on VUSB and VIN paths. USB power to the MCU is approximately ~4.7 V due to Schottky drop.
- **ESD protection**: PRTR5V0U2X,215 (D4) on the USB data lines.
- Power is automatically selected between USB and VIN/Barrel Jack via the ISL854102FRZ and diode OR arrangement.

## Recommended Operating Conditions

| Symbol | Description | Min | Typ | Max | Unit |
| ------ | ----------- | --- | --- | --- | ---- |
| VIN | Input voltage from VIN pad / DC Jack | 6 | 7.0 | 24 | V |
| VUSB | Input voltage from USB connector | 4.8 | 5.0 | 5.5 | V |
| TOP | Operating Temperature | -40 | 25 | 85 | °C |

## Additional Resources
- Official datasheet (SKU ABX00080): https://docs.arduino.cc/resources/datasheets/ABX00080-datasheet.pdf
- Arduino IDE (Desktop): https://www.arduino.cc/en/Main/Software
- Arduino Cloud Editor: https://create.arduino.cc/editor
- Project Hub: https://create.arduino.cc/projecthub
- Library Reference: https://github.com/arduino-libraries/
- Online Store: https://store.arduino.cc/
- Renesas RA4M1 series: https://www.renesas.com/en/products/microcontrollers-microprocessors/ra-cortex-m-mcus/ra4m1-32-bit-microcontrollers-48mhz-cortex-m4-and-lcd-controller-and-cap-touch-hmi
