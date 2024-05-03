/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


typedef struct inner {
  unsigned x[4];
} inner;

typedef struct outer {

   inner inners[128];
} outer;

void main (void){
  outer v;
  v.inners[2].x[3] = 2;
}
