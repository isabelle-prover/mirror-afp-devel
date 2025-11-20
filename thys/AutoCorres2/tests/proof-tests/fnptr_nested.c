/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef unsigned char uint8_t;

typedef struct {
  void (*g1)(void);
  unsigned (*g2) (void);
  unsigned content;
} obj_t;

obj_t *f3(uint8_t *x);
obj_t *f4(uint8_t *x);


unsigned fourty_two(void) {
  return 42;
}

void empty_fun(void) {
}

void h1(uint8_t *ptr) {

  [[calls(empty_fun)]] f4(ptr)->g1(); 
}

unsigned h2(uint8_t *ptr) {
  unsigned x = 0;
  [[calls(fourty_two)]]x = f4(ptr)->g2(); 
  return x;
}

void h(uint8_t *ptr) {
  [[calls(empty_fun)]] f3((uint8_t*)ptr)->g1();
}

unsigned char nested_switch(unsigned char i, unsigned char j)
{
  unsigned x = 0;
  switch (i) {
    case 0:
      switch (j) {
      case 0:
        return 1;
      default:
        return 2;
      }
    case 1:
      x = 2;
      break;
    case 2:
      x = 3; /* last case can fall through*/
    }
  return x;
}
