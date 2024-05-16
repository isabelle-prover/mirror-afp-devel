/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef struct {
    unsigned long array_A[1];
    unsigned char x;
} A;

typedef struct {
    unsigned long array_B[1];
} B;

unsigned long elem_A(A *s) {
  return s->array_A[0];
}

unsigned long elem_B(B *s) {
  return s->array_B[0];
}
