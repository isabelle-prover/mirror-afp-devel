/*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
*/

typedef void ( *fnptr_t)(int *x);

void inc(int *x) {
  *x = *x + 1;
}

void dec(int *x) {
  *x = *x - 1;
}

const fnptr_t array[] =
  {
    inc, dec, inc, dec, inc, dec, inc, dec, inc, dec,
    inc, dec, inc, dec, inc, dec, inc, dec, inc, dec,
    inc, dec, inc, dec, inc, dec, inc, dec, inc, dec,
    inc, dec, inc, dec, inc, dec, inc, dec, inc, dec,
  };

void main(int *x) {
  int i = *x;
  if (i < sizeof(array))
    array[i](x);
}