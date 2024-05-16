/*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct x;
struct y;

struct x {
  int y[1];
  struct y *z;
};

struct y {
  int x[2];
  struct x *z;
};

int f(struct x a, struct y b)
{
  a.y[0] = b.x[0];
}
