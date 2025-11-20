/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

void f(unsigned char *x)
{
  *x = *x + 1;
}

int h(unsigned int n) {
  int ret = 0;
  unsigned char x = 0;
  f(&x);
  ret = x + 1;
  return ret;
}

int g(unsigned int n) {
  int ret = 0;
  for (unsigned int i = 0; i < n; i++) {
    unsigned char x = 0;
    f(&x);
    if (i == 42) {
      ret = 42;
      break;
    }
  }
  return ret;
}
