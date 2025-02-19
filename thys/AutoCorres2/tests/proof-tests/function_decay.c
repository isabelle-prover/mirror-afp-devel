/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef unsigned (* fun_t)(unsigned);

unsigned foo(unsigned n) {return n;}

fun_t fs  = foo;

fun_t select(void) {
  return foo;
}

fun_t select1(void) {
  return (fun_t) foo;
}

unsigned main(unsigned n) {

  unsigned result = 0;
  fun_t f = select1();
  result = f(n);
  return result;
}