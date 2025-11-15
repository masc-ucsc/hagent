# ESP32-C3 DevKit-RUST-1 Notes

## Project Setup
- **Build system**: ESP-IDF (C/C++ framework)
- **Project structure**: Standard ESP-IDF CMake project
  - Source directory: `main/`
  - Build directory: `build/`
  - Configuration: `sdkconfig`
- **Build/Flash commands**:
  - Build: `idf.py build`
  - Flash: `idf.py flash`
  - Build + Flash: `idf.py build flash`
  - Monitor (note: requires TTY and ctrl+] to exit): `idf.py monitor`

## Board Overview
- `board`: esp32c3 (ESP32-C3-DevKit-RUST-1)
- RISC-V single-core MCU up to 160 MHz with 384 KB ROM, 400 KB SRAM, 8 KB RTC SRAM
- Integrated IEEE 802.11 b/g/n Wi-Fi, Bluetooth 5, Bluetooth Mesh, USB Serial/JTAG
- Development board includes sensors, LEDs, button, battery charger, USB Type-C connector

## On-Board Peripherals

### I2C Bus
- Bus pins: SDA on GPIO10, SCL on GPIO8

| Peripheral | Part | Crate | Address |
| ---------- | ---- | ----- | ------- |
| IMU | ICM-42670-P | `icm42670` | 0x68 |
| Temperature & Humidity | SHTC3 | `shtcx` | 0x70 |

### Direct GPIO Attachments

| Function | GPIO |
| -------- | ---- |
| WS2812 RGB LED | GPIO2 |
| Indicator LED | GPIO7 |
| Boot/User Button | GPIO9 |

## Pin Reference

DO NOT USE GPIO18 or GPIO19 for your code, or it will destroy the USB setup. This will require a factory reset.

### Left Edge

| Pin | Description | SoC |
| --- | ----------- | --- |
| 1 | Reset | EN/CHIP_PU |
| 2 | 3V3 | — |
| 3 | N/C | — |
| 4 | GND | — |
| 5 | IO0/ADC1-0 | GPIO0 |
| 6 | IO1/ADC1-1 | GPIO1 |
| 7 | IO2/ADC1-2 | GPIO2 |
| 8 | IO3/ADC1-3 | GPIO3 |
| 9 | IO4/ADC2-0 | GPIO4 |
| 10 | IO5/ADC2-1 | GPIO5 |
| 11 | IO6/MTCK | GPIO6 |
| 12 | IO7/MTDO/LED | GPIO7 |
| 13 | IO9/LOG | GPIO8 |
| 14 | IO21/U0RXD | GPIO21 |
| 15 | IO20/U0TXD | GPIO20 |
| 16 | IO9/BOOT | GPIO9 |

### Right Edge

| Pin | Description | SoC |
| --- | ----------- | --- |
| 1 | VBAT | — |
| 2 | EN [1] | — |
| 3 | VBUS [2] | — |
| 4 | NC | — |
| 5 | NC | — |
| 6 | NC | — |
| 7 | NC | — |
| 8 | NC | — |
| 9 | IO18/USB_D- | GPIO18 |
| 10 | IO19/USB_D+ | GPIO19 |
| 11 | IO8/SCL | GPIO8 |
| 12 | IO10/SDA | GPIO10 |

[1] Connected to LDO enable pin  
[2] Connected to USB 5V input

## Power Notes
- USB Type-C power input (no USB-PD negotiation)
- On-board MCP73831T-2ACI/OT Li-Ion charger targets 4.2 V; battery protection not included
- Battery voltage sensing is not provided on this board

## Additional Resources
- Full board README: https://github.com/esp-rs/esp-rust-board/blob/master/README.md
