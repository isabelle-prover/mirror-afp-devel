/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int g;

int bitwise_or(int i, int j) {
  return (i | j);
};

int same(int i) {
  g = i;
  return i;
};

int call_same(void) {
  int k = 0;
  int j = 1;
  int i = 2;
  k = same(i) | same (j);
  return k;
};
