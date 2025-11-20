/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef struct named_pair {
  unsigned first;
  unsigned second;
} named_pair_t;

struct nested {
  named_pair_t first_pair;
  struct {
    unsigned aaa;
    unsigned bbb;
  } second_pair;
};

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

int main1(coord_t x) {
  x.phi = 2;
  x.x = 1;
  named_pair_t y;
  struct nested n;
  return x.r;
}

typedef struct {
  int fst;
  int snd;
} pair_t;

int foo1 (void) {
  int o1 = __builtin_offsetof(pair_t, fst);
  return o1;
}

int foo2 (void) {
  int o2 = __builtin_offsetof(coord_t, x);
  return o2;
}

typedef struct {
  union {
    unsigned char x;
    unsigned char y;
    unsigned char z;
  };
} inner_t;

typedef struct {
  unsigned short p;
  inner_t inner;
} outer_t;

int bar(void) {
  int o = __builtin_offsetof(outer_t, inner.x);
  return o;
}

char * access_y (inner_t * v) {
  char * x = (char *) (&(v->x));
  char * y = (char *) (&(v->y));
  char * z = (char *) (&(v->z));
  return z;
}
