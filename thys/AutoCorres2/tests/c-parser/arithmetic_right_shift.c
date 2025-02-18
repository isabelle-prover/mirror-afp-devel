/*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int c;
unsigned u;

int f(void)
{
  c = c >> 5;
  return c;
}

unsigned g(void)
{
  u = u >> 5;
  return u;
}
