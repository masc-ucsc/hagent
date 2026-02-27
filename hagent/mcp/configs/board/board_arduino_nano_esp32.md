# Arduino Nano ESP32 Board Notes

## Project Setup
- **Build system**: `arduino-cli`
- **Project structure**: Standard Arduino sketch project
  - Sketch directory: `<sketch_name>/`
  - Main file: `<sketch_name>.ino`
- **Build/Flash commands**:
  - Compile: `arduino-cli compile --fqbn arduino:esp32:nano_nora <sketch_name>`
  - Upload: `arduino-cli upload -p <PORT> --fqbn arduino:esp32:nano_nora <sketch_name>`
  - Monitor: `arduino-cli monitor -p <PORT>`

## Supported Platforms
- **Arduino**

> **Note:** This board may not appear with its name and FQBN when using `arduino-cli board list` or the MCP tool that lists connected Arduino boards. It often shows up only as a Serial Port (USB). Flash directly to that port — do not rely on board listing to identify it.

## Board Overview
- `board`: nano_esp32
- `model`: Arduino Nano ESP32 (ABX00083)
- `fqbn`: arduino:esp32:nano_nora
- `core`: arduino:esp32 (Arduino Board Package for ESP32, derived from Espressif's arduino-esp32)
- Xtensa® Dual-Core 32-bit LX7 microprocessor (ESP32-S3 SoC, embedded in NORA-W106-10B from u-blox®) at up to 240 MHz
- 384 kB ROM, 512 kB SRAM, 8 kB RTC SRAM (FAST + SLOW), 8 MB embedded PSRAM (Octal SPI)
- 128 Mbit (16 MB) external QSPI flash (GD25B128EWIGR, U3) at 133 MHz, up to 664 Mbit/s transfer rate
- USB-C® connector for power and programming; operates at **3.3 V logic**
- Wi-Fi® 4 (802.11 b/g/n) and Bluetooth® LE v5.0 via built-in antenna (2402–2480 MHz)
- Development board includes RGB LED, SCK LED, Power LED, reset button, 32.768 kHz crystal oscillator (Y1)

## On-Board Peripherals

### I2C Bus

| Bus | Default Pins | Notes |
| --- | ------------ | ----- |
| I2C (Wire) | A4 (SDA), A5 (SCL) | Default assignment; can be remapped to most GPIOs due to ESP32-S3 flexibility |

> **Note:** The I2C bus defaults to A4/A5 for retro-compatibility. Many libraries assume this assignment. SDA/SCL can be remapped, but some GPIOs may conflict with other essential functions.

### Direct GPIO Attachments

| Function | Arduino Pin | GPIO |
| -------- | ----------- | ---- |
| RGB LED (Red) | D14 | GPIO46 |
| RGB LED (Green) | D15 | GPIO08 |
| RGB LED (Blue) | D16 | GPIO45 |
| Built-in LED / SCK LED | LED_BUILTIN | GPIO48 |
| Power LED | DL3 | — |
| Reset Button | RST | PB1 |

### Analog Features

| Feature | Pins | Notes |
| ------- | ---- | ----- |
| ADC1 | A0 (GPIO01), A1 (GPIO02), A2 (GPIO03), A3 (GPIO04) | ADC1_CH0–CH3; available in RTC mode |
| ADC2 | A4 (GPIO11), A5 (GPIO12), A6 (GPIO13), A7 (GPIO14) | ADC2_CH0–CH3; available in RTC mode |

> **Note:** There is no DAC on this board. All digital and analog pins are **3.3 V only** — do not connect higher voltage devices.

### Communication Interfaces

| Interface | Default Pins | Notes |
| --------- | ------------ | ----- |
| UART | D0 (RX / GPIO44), D1 (TX / GPIO43) | |
| SPI | D13/SCK (GPIO48), D12/CIPO (GPIO47), D11/COPI (GPIO38), D10/CS (GPIO21) | |
| I2C | A4 (SDA / GPIO11), A5 (SCL / GPIO12) | Reassignable to most GPIOs |
| I2S | Any free GPIO | No fixed pins; standard/TDM: MCLK, BCLK, WS, DIN/DOUT; PDM: CLK, DIN/DOUT |
| CAN / TWAI® | Any free GPIO | No fixed pins; CAN2.0B classic only — NOT compatible with CAN FD |

### Wireless

| Protocol | Standard | Max Data Rate | Max Range | Output Power (EIRP) |
| -------- | -------- | ------------- | --------- | ------------------- |
| Wi-Fi® | 802.11 b/g/n (Wi-Fi 4) | 150 Mbps (HT-40) | 500 m | 20 dBm radiated |
| Bluetooth® LE | v5.0 | 2 Mbps | — | 10 dBm radiated |

### Interrupts & Timers

All GPIOs can be configured as interrupts (LOW, HIGH, CHANGE, FALLING, RISING) via the interrupt matrix.

Timers available: 52-bit system timer (2x counters at 16 MHz, 3x comparators), 4x general-purpose 54-bit timers, 3x watchdog timers (MWDT0, MWDT1 in main system; RWDT in RTC module).

### Reset Levels (ESP32-S3)

The ESP32-S3 supports four reset levels: CPU reset, Core reset (preserves RTC peripherals), System reset (full digital system including RTC), and Chip reset. Hardware reset via onboard button PB1; software reset also supported.

## Pin Reference

### Analog Header (JP1)

| Pin | Function | Type | Description |
| --- | -------- | ---- | ----------- |
| 1 | D13 / SCK | NC | Serial Clock (also LED_BUILTIN, GPIO48) |
| 2 | +3V3 | Power Out | 3.3 V power rail |
| 3 | BOOT0 | Mode | Board Reset 0 |
| 4 | A0 | Analog | Analog input 0 (GPIO01 / ADC1_CH0) |
| 5 | A1 | Analog | Analog input 1 (GPIO02 / ADC1_CH1) |
| 6 | A2 | Analog | Analog input 2 (GPIO03 / ADC1_CH2) |
| 7 | A3 | Analog | Analog input 3 (GPIO04 / ADC1_CH3) |
| 8 | A4 | Analog | Analog input 4 / I²C SDA (GPIO11 / ADC2_CH0) |
| 9 | A5 | Analog | Analog input 5 / I²C SCL (GPIO12 / ADC2_CH1) |
| 10 | A6 | Analog | Analog input 6 (GPIO13 / ADC2_CH2) |
| 11 | A7 | Analog | Analog input 7 (GPIO14 / ADC2_CH3) |
| 12 | VBUS | Power Out | USB power (5 V, only active when powered via USB) |
| 13 | BOOT1 | Mode | Board Reset 1 |
| 14 | GND | Power | Ground |
| 15 | VIN | Power In | Voltage input (6–21 V) |

### Digital Header (JP2)

| Pin | Function | Type | Description |
| --- | -------- | ---- | ----------- |
| 1 | D12 / CIPO | Digital | SPI Controller In Peripheral Out (GPIO47) |
| 2 | D11 / COPI | Digital | SPI Controller Out Peripheral In (GPIO38) |
| 3 | D10 / CS | Digital | SPI Chip Select (GPIO21) |
| 4 | D9 | Digital | Digital pin 9 (GPIO18) |
| 5 | D8 | Digital | Digital pin 8 (GPIO17) |
| 6 | D7 | Digital | Digital pin 7 (GPIO10) |
| 7 | D6 | Digital | Digital pin 6 (GPIO09) |
| 8 | D5 | Digital | Digital pin 5 (GPIO08) |
| 9 | D4 | Digital | Digital pin 4 (GPIO07) |
| 10 | D3 | Digital | Digital pin 3 (GPIO06) |
| 11 | D2 | Digital | Digital pin 2 (GPIO05) |
| 12 | GND | Power | Ground |
| 13 | RST | Internal | Reset |
| 14 | D0 / RX | Digital | Serial Receiver (RX) (GPIO44) |
| 15 | D1 / TX | Digital | Serial Transmitter (TX) (GPIO43) |

> **Note:** CIPO/COPI/CS replaces the MISO/MOSI/SS terminology. All pins are PWM-capable (~) unless otherwise noted.

## Factory Reset / Board Recovery

If the board is unresponsive or not reachable via USB, it can be recovered using the built-in bootloader:

1. Double-tap the **RESET** button (PB1) right after power-up to enter bootloader mode.
2. Once in bootloader mode, the board can be re-flashed via USB.

## Power Notes
- **Operating voltage**: 3.3 V. All digital and analog pins are **3.3 V only** — connecting higher voltage devices will risk damaging the board.
- **USB-C® input (VBUS)**: 4.8–5.5 V. Do not power the board with more than 5 V via USB-C®.
- **VIN pin**: 6–21 V; stepped down to 3.3 V by the MP2322GQH (U2) buck converter (max 21 V / 1 A).
- **VBUS pin**: Provides 5 V only when the board is powered via USB. When powered via VIN, the VBUS pin is not activated — no 5 V available from the board in that case.
- **3V3 pin**: Connected to the output of the MP2322GQH step-down converter; primarily used to power external components.
- **GPIO current limit**: Source up to 40 mA, sink up to 28 mA per GPIO. Do not connect devices drawing higher current directly to a GPIO.
- **Buck converter efficiency (VIN input)**:
  - 4.5 V → >90%
  - 12 V → 85–90%
  - 18 V → <85%
- **Low power modes** (ESP32-S3 SoC only — other board components add to total consumption):
  - Deep sleep: ~7 μA
  - Light sleep: ~240 μA
- **Schottky diode** (D2: PMEG6020AELRX) on VBUS path for protection. ESD protection (D3: PRTR5V0U2X,215) on USB data lines.

## Recommended Operating Conditions

| Symbol | Description | Min | Typ | Max | Unit |
| ------ | ----------- | --- | --- | --- | ---- |
| VIN | Input voltage from VIN pad | 6 | 7.0 | 21 | V |
| VUSB | Input voltage from USB connector | 4.8 | 5.0 | 5.5 | V |
| Tambient | Ambient Temperature | -40 | 25 | 105 | °C |

## Additional Resources
- Official datasheet (SKU ABX00083): https://docs.arduino.cc/resources/datasheets/ABX00083-datasheet.pdf
- Arduino IDE (Desktop): https://www.arduino.cc/en/Main/Software
- Arduino Cloud Editor: https://create.arduino.cc/editor
- Project Hub: https://create.arduino.cc/projecthub
- Library Reference: https://github.com/arduino-libraries/
- Online Store: https://store.arduino.cc/
