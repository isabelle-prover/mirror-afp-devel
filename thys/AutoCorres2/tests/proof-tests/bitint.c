/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct foo {
  _BitInt(9) n;
};

unsigned add_unsigned(unsigned n, unsigned m) {
  return n + m;
}

int add_signed(int n, int m) {
  return n + m;
}


unsigned _BitInt(9) add_unsigned_bitint(unsigned _BitInt(9) n, unsigned _BitInt(9) m) {
  return n + m;
}

unsigned _BitInt(9) call_add_unsigned_bitint (unsigned _BitInt(9) n, unsigned _BitInt(9) m) {
  unsigned _BitInt(9) res = 0;
  res = add_unsigned_bitint (n, m);
  return res;
}

int add_signed_bitint( _BitInt(9) n, _BitInt(9) m) {
  return n + m;
}


void bit_int_guard_tests(void) {
  unsigned n = 0;
  int i = 0;
  n = 2uwb + 2uwb;
  i = 2wb + 2wb;
  i = -2wb - 2wb;
  n = ((unsigned _BitInt((3) + 1))1uwb) << (3);
  i = (( _BitInt((3) + 1))1wb) << (3);

  i = i << 3;
}

void inc_bitint (unsigned _BitInt(9) * p) {
  unsigned x = 0;
  x = ((_BitInt(9)) 2uwb) + 1u;
  (*p) = (*p) + 1u;
}

void bitint_fun(unsigned n) {
  _BitInt(3) b;
   struct foo X;
   b = b + 1;
  unsigned long x = 0;
  x =  (_BitInt(2)) 2 ;
  x = (((unsigned _BitInt((3) + 1))1) << (3));
  x = __builtin_choose_expr(__builtin_constant_p(0 + 1 
    + x), 2, 3) + 1;
  unsigned long y = 0;
  y = b;
  b = b;
  y = X.n;
  X.n = b;
  unsigned long z = 0;
  
}

