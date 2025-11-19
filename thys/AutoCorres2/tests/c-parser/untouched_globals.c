/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int x, y = 1;

struct s { char c; int array[4]; };

struct s glob1, glob2 = { '3', 1,2 };

int f(int n)
{
  y++;
  return n + 1;
}

int g(int n)
{
  return n*n;
}

#define SOME_CONSTANT 13

struct tuple {
  int a;
  int b;
};

static int counter = SOME_CONSTANT;
static struct tuple t = { 0 };

static const int array_int[] = {
  [0] = 1,
  [1] = 1
};

typedef struct {
  const int * const array;
} outer_t;

static const outer_t outer1 = {
  .array = array_int
};


/*

*/
typedef struct {
  const int const array[2];
} outer_value_t;



int touch_types (void) {
  struct tuple y;
  outer_t x;
}
/*
static const outer_value_t outer2 = {
  .array = array_int
};
*/