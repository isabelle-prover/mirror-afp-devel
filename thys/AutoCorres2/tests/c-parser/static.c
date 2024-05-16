/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int n = 33;

int foo1(int k) {
  static int n = 1;
  return n + k;
}

int foo2(int k) {
  static int n = 2;
  n = n + k;
  return n;
}

int inc(int n) {
  return n + 1;
}

int glob(int m) {
   return n + m;
}


void f(int i) {}

int g(void) {
  static int i;
  return i;
}
