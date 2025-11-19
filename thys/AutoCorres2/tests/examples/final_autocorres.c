/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned add(unsigned n, unsigned m) {
  return n + m;
}

unsigned minus(unsigned n, unsigned m) {
  return n - m;
}

unsigned mul(unsigned n, unsigned m) {
  return n * m;
}


unsigned div(unsigned n, unsigned m) {
  return n / m;
}

typedef unsigned (* binop_t) (unsigned, unsigned);

unsigned call_add_minus(binop_t f, unsigned n, unsigned m) {
  __attribute__((calls(add, minus))) return f(n,m);
}

unsigned call_mul_div(binop_t f, unsigned n, unsigned m) {
  __attribute__((calls(mul, div))) return f(n,m);
}