/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


volatile int g;

int f(int x)
{
  /** GHOSTUPD:
        "(\<acute>x < 42, (%n. n + 1))" */
  return x + 3;
}
