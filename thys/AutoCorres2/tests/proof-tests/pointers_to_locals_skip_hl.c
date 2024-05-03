/*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

void f(int *x)
{
  *x = 0;
  exit(1);
}

void g(void)
{
  int x;
  f(&x);
}
