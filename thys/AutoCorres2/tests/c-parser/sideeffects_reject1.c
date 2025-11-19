/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int inc(int * x) {
  (*x) = (*x) + 1;
}

int reject_mixed_function_and_addressed_locals(int x, int y) {
  int result = 0;
  inc(&x);
  result = inc(&x) + x;
  return result;
}