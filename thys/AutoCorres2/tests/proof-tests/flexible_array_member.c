/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef struct {
  char len;
  long arr[];
} arr_t;


long get (arr_t* p, unsigned n) {
  long result = 0;  
  long * q = 0;
  q =  p->arr;
  *(p->arr) = *q;
  result = p->arr[n];
  p->arr[n] = 2;
  return result;
}