/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

void dec (unsigned* y) {
  *y = *y - 1;
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


unsigned inc_ref (unsigned y) {
  return y + 1;
}

unsigned g;


void call_inc_first(void) {
  pair tuple;
  inc(&(tuple.first));
}

unsigned garr[3];

void call_inc_global_array(unsigned i) {
  inc(&(garr[i]));
}
unsigned call_inc_array(unsigned i) {
  unsigned arr[3];
  inc(&(arr[i]));
  return arr[i];
}

unsigned call_inc_buffer(unsigned i) {
  buffer b;
  inc(&(b.buf[i]));
  return b.buf[i];
}

void call_inc_buffer_ptr(buffer* b1, unsigned i) {

  inc(&(b1->buf[i]));
}

void call_inc_buffer_size_ptr(buffer* b2, unsigned i) {

  inc(&(b2->size));
}

void call_inc_array_ptr(unsigned *arr, unsigned i) {
  inc(&(arr[i]));
}


unsigned call_inc(unsigned n) {
  n = n;
  unsigned res;
  inc(&g);
  unsigned i;
  unsigned j = 2;
  inc(&i);
  inc(&j);
  inc(&n);
  res = g + i + j + n;
  i = 2;
  return res;
}


unsigned call_inc_ref(void) {
  unsigned res;
  g = inc_ref(g);
  res = g;
  return res;
}

unsigned call_inc_ref_local(void) {
  unsigned res;
  unsigned i;
  i = 42;
  i = inc_ref(i);
  res = i;
  return i;
}


int main(int n) {
  unsigned m  = inc_ref (n) ;
  unsigned k;
  inc(&m);
  inc(&k); 


}


