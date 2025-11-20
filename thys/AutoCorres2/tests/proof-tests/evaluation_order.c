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

int same_pure(int i) {
  return i;
};

int same_read_only(int i) {
  return g + i;
};

int call_same_pure(void) {
  int k = 0;
  int j = 1;
  int i = 2;
  k = same_pure(i) | same_pure(j);
  return k;
};

int call_same_read_only(void) {
  int k = 0;
  int j = 1;
  int i = 2;
  k = same_read_only(i) | same_read_only(j);
  return k;
};


int call_same(void) {
  int k = 0;
  int j = 1;
  int i = 2;
  int x = same(i);
  int y = same(j);
  k = x | y;
  return k;
};
