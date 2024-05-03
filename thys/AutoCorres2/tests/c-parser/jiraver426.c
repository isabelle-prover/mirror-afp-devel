/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

_Noreturn void abort(int i);

unsigned f(unsigned i)
{
  if (i < 0) abort(-1);
  return i * i;
}

_Noreturn void myexit(int i)
{
  abort(i + 1);
}
