/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef union element {
  unsigned all;
  struct {
     unsigned foo;
  } f;
} element;

typedef union outer {
  unsigned all[128];
  struct inner {
    element array[128];
  } inner;
} outer;

void main (void){
//  element* e;
  outer x;
  x.inner.array[0].all = 0;
}
