/*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned int inc(unsigned int *x) {
  return *x + 1;
}

unsigned int ternary1(unsigned int x, unsigned int y, unsigned int z) {
  unsigned int a = x == 42 ? y : z;
  return a;
}

unsigned int ternary2(unsigned int x) {
  return x > 10 ? 10 : (x < 5 ? 0 : 5);
}

unsigned int ternary3(unsigned int *x1, unsigned int *x2, unsigned int *y, unsigned int *z) {
  unsigned int a = ternary1(x1 != 0 ? *x1 : (x2 != 0 ? *x2 : 0), inc(y), z != 0 ? inc(z) : 12);  
  return a;
}