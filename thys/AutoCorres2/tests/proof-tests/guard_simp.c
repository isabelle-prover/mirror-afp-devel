/*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


void inc (unsigned* y) {
  *y = *y + 1;
}

void inc2 (unsigned * y, unsigned * z) {
  inc(y);
  inc(z);
}

void heap_inc2(unsigned * y, unsigned * z) {
  inc2(y, z);
}

void call_heap_inc2(unsigned * p, unsigned * q) {
  inc2(p,q);
  heap_inc2(p, q);
  inc2(p, q);

}

void inc2_loop(unsigned * y, unsigned * z, unsigned i) {
  unsigned k = 0;
  inc2(y, z);
  for (k=0; k <= i; k++) {
    inc2(y,z);
  }
}

void inc2_while(unsigned * y, unsigned * z, unsigned i) {
  inc2(y, z);
  while (*y<i) {
    inc2(y,z);
    if (*y < *z) break;
  }
}

unsigned cond(unsigned * x, unsigned * y, unsigned i) {
  if (i > 42) {
    inc2(x, y);
    return (i > 42);
  } else {
    inc2(y, x);
    return (i > 42);
  }
}

int fac_exit(int n) {
  if (n < 0) {
    exit(1);
  } else if (n == 0) {
    return 0;
  } else { 
    return fac_exit (n - 1);
  };
}

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

unsigned shuffle(unsigned char *buf, unsigned char len){
 unsigned tmp= 0;
 if (len > 4){
  return 42;
 }
 for(int i = 0; i < len; i++){
  tmp |= (unsigned)(*(buf - i)) << (i*8);
 }
 return tmp;
}

void swap (unsigned int *p, unsigned int * q) {
  unsigned tmp;
  tmp = *p;
  *p = *q;
  *q = tmp;
}

unsigned int swap_local (unsigned int n, unsigned int m)
{
  swap(&n, &m);
  return (*(&n) + *(&m));
}

unsigned int g;

unsigned int inc_g (unsigned int n) {
 g = g + n;
 return g;
}