/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
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
  unsigned a;
  unsigned b;
};

typedef struct tuple1 {
  unsigned x;
  unsigned y;
} tuple1_t;

typedef struct tuple2 {
  unsigned x;
  unsigned y;
} tuple2_t;


tuple1_t gt1[2] = {{1,2}, {3,4}};
tuple2_t gt2[2] = {{1,2}, {3,4}};

tuple1_t _gt1m[2] = {{1,2}, {3,4}};
tuple2_t* pgt2 = gt2;


static int counter = SOME_CONSTANT;
static struct tuple t = { 0 };

static unsigned array_int[] = {
  [0] = 1,
  [1] = 1
};

typedef struct {
  const unsigned * const array;
} outer_t;

static const outer_t outer1 = {
  .array = array_int
};

/*

*/
typedef struct {
  const unsigned array[2];
} outer_value_t;

unsigned glob;


unsigned init_ptr (unsigned * p) {
  *p = 1;
  return *p;
}

unsigned inc_ptr (unsigned * p) {
  *p = *p + 1;
  return *p;
}

void inc_glob() {
  inc_ptr (&glob);
}

void init_glob() {
  glob = 1;
}

unsigned get_array(outer_value_t * p) {
  return p->array[0];
}
/*
static const outer_value_t outer2 = {
  .array = array_int
};
*/


static unsigned *arr_ptr_1;
static unsigned arr_1[120];

static unsigned **foo(void)
{
    arr_ptr_1 = arr_1;
    return &arr_ptr_1;
}


static int *arr_ptr_2;
static int arr_2[120];

static int **bar(void)
{
    arr_ptr_2 = arr_2;
    return &arr_ptr_2;
}

void touch_types (void) {
  struct tuple x;
  tuple1_t y;
  tuple2_t z;
  outer_t a;
  }
