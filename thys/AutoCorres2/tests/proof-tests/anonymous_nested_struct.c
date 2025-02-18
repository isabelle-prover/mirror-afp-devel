/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef struct {
  unsigned char id;
  union {
    struct {
      int x;
      int y;
    };
    struct {
      int r;
      int phi;
    };
  };
} coord_t;

int main (coord_t x) {
  x.phi = 2;
  x.x = 1;
  return x.r;
}

typedef struct {
  int fst;
  int snd;
} pair_t;

int foo (void) {
  int o1 = __builtin_offsetof(pair_t, fst);
  int o2 = __builtin_offsetof(coord_t, x);
  return o1;
}
