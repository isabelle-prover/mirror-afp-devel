/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef unsigned plain_array[3];
typedef struct pair {
  unsigned first;
  unsigned snd;
} pair;

typedef struct buffer {
  unsigned buf[2];
  unsigned size;
} buffer;


void inc (unsigned* y) {
  *y = *y + 1;
}

void dec (unsigned* y) {
  *y = *y - 1;
}

void inc_untyp(unsigned *ptr) {
  inc(ptr);
  /** AUXUPD: "(True, ptr_retyp (ptr_coerce \<acute>ptr :: unit ptr))" */
}

unsigned odd(unsigned n);
unsigned even(unsigned n) {
  if (n == 0) {
     return 1;
  } else {
     dec(&n);
     return odd(n);
  }
};
unsigned odd(unsigned n) {
  if (n == 1) {
    return 1;
  } else {
    dec(&n);
    return even(n);
  }
};


unsigned g = 42;

void call_inc_global(void) {
  inc(&g);
}

unsigned call_inc_local_uninitialized(void) {
  unsigned m;
  inc(&m);
  return(42);
}

unsigned call_inc_local_initialized(void) {
  unsigned m = 42;
  inc(&m);
  return(m);
}

unsigned call_inc_parameter(unsigned n) {
  inc(&n);
  return(n);
}


unsigned call_inc_array(unsigned i) {
  plain_array arr;
  inc(&(arr[i]));
  return arr[i];
}

unsigned call_inc_buffer(unsigned i) {
  buffer b;
  inc(&(b.buf[i]));
  return b.buf[i];
}

unsigned call_inc_first(void) {
  pair tuple;
  inc(&(tuple.first));
  return tuple.first;
}


unsigned call_inc_untyp(unsigned i) {
  inc_untyp(&i);
  return i;
}

unsigned call_inc_nested(unsigned i) {
  unsigned m;
  unsigned n;
  inc(&m);
  inc(&i);
  inc(&n);
  return (m + i + n);
}


void f1(unsigned *x)
{
  *x = 0;
  exit(1);
}

void g1(void)
{
  unsigned x;
  f1(&x);
}

/*
void f2(int *x)
{
  *x = 0;
  exit(1);
}

void g2(void)
{
  int x;
  f1(&x);
}

*/