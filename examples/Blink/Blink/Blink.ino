/*
  Blink
  Blinks the built-in LED once per second.
  Works on any Arduino board.
*/

#include "Arduino.h"

void setup() {
  pinMode(LED_BUILTIN, OUTPUT);
}

void loop() {
  digitalWrite(LED_BUILTIN, HIGH);
  delay(1000);
  digitalWrite(LED_BUILTIN, LOW);
  delay(1000);
}