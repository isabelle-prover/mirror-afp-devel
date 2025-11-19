/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct t { void (*p)(int x[128]); };

void some_function(int x[128]) {};

void unique_test (struct t *a, int x[128])
{
  [[calls(some_function)]] a->p(x);
}
