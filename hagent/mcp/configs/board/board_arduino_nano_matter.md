# Arduino Nano Matter Board Notes

## Project Setup
- **Build system**: `arduino-cli`
- **Project structure**: Standard Arduino sketch project
  - Sketch directory: `<sketch_name>/`
  - Main file: `<sketch_name>.ino`
- **Build/Flash commands**:
  - Compile: `arduino-cli compile --fqbn SiliconLabs:silabs:nano_matter <sketch_name>`
  - Upload: `arduino-cli upload -p <PORT> --fqbn SiliconLabs:silabs:nano_matter <sketch_name>`
  - Monitor: `arduino-cli monitor -p <PORT>`

## Supported Platforms
- **Arduino**

> **Note:** This board may not appear with its name and FQBN when using `arduino-cli board list` or the MCP tool that lists connected Arduino boards. It often shows up only as a Serial Port (USB). Flash directly to that port — do not rely on board listing to identify it.

## Board Overview
- `board`: nano_matter
- `model`: Arduino Nano Matter — without headers (ABX00112) / with headers (ABX00137)
- `fqbn`: SiliconLabs:silabs:nano_matter
- `core`: SiliconLabs:silabs
- 78 MHz, 32-bit Arm® Cortex®-M33 microcontroller (MGM240SD22VNA from Silicon Labs)
- 1536 kB Flash, 256 kB RAM
- USB-C® connector (J1: CX90B-16P) for power and data; operates at **3.3 V logic**
- Connectivity: 802.15.4 Thread, Bluetooth® Low Energy 5.3, Bluetooth® Mesh — built-in antenna
- Security: Secure Vault® from Silicon Labs
- USB bridge: ATSAM-D11-D14A-MUT (U1); TVS Array PRTR5V0U2X,215 (D1) for ESD protection
- Development board includes RGB LED (DL1: UHD1110-FKA-CL1A13R3Q1BBQFMF3), Power LED (DL2), reset button (PB1), user button (BTN_BUILTIN), 32.768 kHz crystal oscillator (Y1)
- Debugging: JTAG/SWD debug port accessible through test pads; OpenOCD compatible (no J-Link)
- Dimensions: 18 mm × 45 mm; Weight: 4 g
- Four 1.65 mm drilled mounting holes for mechanical fixing
- Available as castellated/through-hole (ABX00112) for SMD mounting, or with pre-installed headers (ABX00137)

## On-Board Peripherals

### I2C Buses

| Bus | Pins | Notes |
| --- | ---- | ----- |
| I2C0 (Wire) | A4 (SDA), A5 (SCL) | Default I2C bus |
| I2C1 (Wire1) | ~D6 (SDA1), ~D5 (SCL1) | Secondary I2C bus |

### Direct GPIO Attachments

| Function | Pin / Label |
| -------- | ----------- |
| RGB LED (Red) | LEDR |
| RGB LED (Green) | LEDG |
| RGB LED (Blue) | LEDB |
| Power LED | DL2 (Power LED) |
| Reset Button | RST (PB1) |
| User Button | BTN_BUILTIN |

### Analog Features

| Feature | Pins | Notes |
| ------- | ---- | ----- |
| ADC (12-bit, ×20 channels) | A0–A7, and other GPIO | 12-bit resolution |
| DAC (up to 12-bit, ×4 channels) | A0 (DAC0), A1 (DAC2), A6 (DAC1), A7 (DAC3) | Up to 12-bit DAC output |
| ADC Reference | AREF | Analog reference voltage input |

### Communication Interfaces

| Interface | Pins | Notes |
| --------- | ---- | ----- |
| UART0 | ~D1 (PIN_SERIAL_TX1), ~D0 (PIN_SERIAL_RX1) | Primary UART |
| UART1 (additional) | Available via GPIO | Second UART port available |
| SPI0 | ~D13 (SCK), ~D12 (MISO), ~D11 (MOSI), ~D10 (SS) | Primary SPI |
| SPI1 | ~D2 (SCK1), ~D3 (SS1), ~D4 (SDA1), ~D5 (SCL1) | Secondary SPI |
| I2C0 | A4 (SDA), A5 (SCL) | Primary I2C |
| I2C1 | ~D6 (SDA1), ~D5 (SCL1) | Secondary I2C |
| PWM | All 22 exposed GPIO (~D2–~D13, A0–A7, etc.) | Up to 5 channels simultaneously operational |

### Wireless

| Protocol | Standard | Notes |
| -------- | -------- | ----- |
| Thread | IEEE 802.15.4 | IoT mesh networking |
| Bluetooth® LE | v5.3 | Short-range communication |
| Bluetooth® Mesh | — | Included |

## Pin Reference

### Analog Header (JP1)

| Pin | Function | Type | Description |
| --- | -------- | ---- | ----------- |
| 1 | ~D13 / SCK | Digital / SPI | SPI Clock / DAC (SPI0) |
| 2 | +3V3 | Power Out | 3.3 V power rail |
| 3 | AREF | Analog | Analog reference voltage |
| 4 | A0 / ~D14 | Analog | Analog input 0 / DAC0 |
| 5 | A1 / ~D15 | Analog | Analog input 1 / DAC2 |
| 6 | A2 / ~D16 | Analog | Analog input 2 |
| 7 | A3 / ~D17 | Analog | Analog input 3 / I2C0 SCL |
| 8 | A4 / ~D18 | Analog / I2C | Analog input 4 / I2C0 SDA |
| 9 | A5 / ~D19 | Analog / I2C | Analog input 5 / I2C0 SCL |
| 10 | A6 / ~D20 | Analog | Analog input 6 / DAC1 |
| 11 | A7 / ~D21 | Analog | Analog input 7 / DAC3 |
| 12 | +5V | Power | +5V (outputs 5V when USB powered) |
| 13 | NC | — | Not connected |
| 14 | GND | Power | Ground |
| 15 | VIN | Power In | Voltage input (6–21 V max) |

### Digital Header (JP2)

| Pin | Function | Type | Description |
| --- | -------- | ---- | ----------- |
| 1 | ~D12 / MISO | Digital / SPI | SPI Controller In Peripheral Out (SPI0) |
| 2 | ~D11 / MOSI | Digital / SPI | SPI Controller Out Peripheral In (SPI0) |
| 3 | ~D10 / SS | Digital / SPI | SPI Chip Select (SPI0) |
| 4 | ~D9 | Digital | Digital pin 9 |
| 5 | ~D8 | Digital | Digital pin 8 |
| 6 | ~D7 | Digital | Digital pin 7 |
| 7 | ~D6 / SDA1 | Digital / I2C | Digital pin 6 / I2C1 SDA |
| 8 | ~D5 / SCL1 | Digital / I2C | Digital pin 5 / I2C1 SCL |
| 9 | ~D4 / SDA1 | Digital / SPI | Digital pin 4 / SPI1 |
| 10 | ~D3 / SS1 | Digital / SPI | Digital pin 3 / SPI1 Chip Select |
| 11 | ~D2 / SCK1 | Digital / SPI | Digital pin 2 / SPI1 Clock |
| 12 | GND | Power | Ground |
| 13 | RST | Internal | Reset |
| 14 | ~D1 / PIN_SERIAL_RX1 | Digital / UART | Serial Receiver (UART0 RX) |
| 15 | ~D0 / PIN_SERIAL_TX1 | Digital / UART | Serial Transmitter (UART0 TX) |

> **Note:** All 22 exposed I/O pins can be used as digital GPIO and support PWM, with a maximum of 5 PWM channels simultaneously operational.

## Factory Reset / Board Recovery

If the board is unresponsive, it can be recovered using the built-in bootloader via the Arduino IDE:

1. Double-tap the **RESET** button (PB1) to enter bootloader mode.
2. Re-flash via USB using the Arduino IDE or arduino-cli.
3. The Nano Matter uses **OpenOCD** for flashing/debugging (not J-Link / Simplicity Commander).
4. For a full erase: in the Arduino IDE, set programmer to OpenOCD then select `Tools > Burn Bootloader`.

## Power Notes
- **Operating voltage**: 3.3 V logic on all pins. Do not apply higher voltages to GPIO.
- **USB-C® input (VUSB)**: 4.8–5.5 V typical.
- **VIN pin**: 6–21 V; stepped down by the MP2322GQH (U3) buck converter (max +21 V).
- **5V pin**: Outputs +5 V **only when the board is USB powered**. Not available when powered via VIN.
- **3V3 pin**: Input/output; can accept an external +3.3 VDC supply for low-power operation (bypasses USB bridge).
- **Low-power tip**: Cut the LED solder jumper (SJ4) to disable the power LED and save energy. For maximum efficiency, power via the 3V3 pin with an external 3.3 V supply — this does not power the USB bridge.
- **LDO Regulator**: AP2112K-3.3TRG1 (U2), takes +5 V input → +3.3 V output for the USB bridge rail (3V3_011).
- **Typical current consumption**: ~16 mA (powered via 5V pin, running Matter color lightbulb example).
- **Safety**: Disconnect power before board modifications. Avoid short-circuiting.

## Recommended Operating Conditions

| Parameter | Symbol | Min | Typ | Max | Unit |
| --------- | ------ | --- | --- | --- | ---- |
| Input voltage from USB connector | VUSB | 4.8 | 5.0 | 5.5 | V |
| Input voltage from VIN pad | VIN | 6 | 7.0 | 21 | V |
| Operating Temperature | TOP | -40 | — | 85 | °C |

## Additional Resources
- Official datasheet (SKU ABX00112 / ABX00137): https://docs.arduino.cc/resources/datasheets/ABX00112-ABX00137-datasheet.pdf
- Nano Matter Documentation: https://docs.arduino.cc/hardware/nano-matter
- Arduino IDE (Desktop): https://www.arduino.cc/en/Main/Software
- Arduino Cloud Editor: https://create.arduino.cc/editor
- Arduino Cloud Getting Started: https://docs.arduino.cc/arduino-cloud/getting-started/iot-cloud-getting-started
- Project Hub: https://create.arduino.cc/projecthub
- Library Reference: https://www.arduino.cc/reference/en/
- Online Store: https://store.arduino.cc/
