/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

static const int b = 0;
static const int a = b + 2;


static const unsigned int c = 0;

unsigned int arr[1] = {c};

int g(void) {
  return b;
}

int f(int n)
{
    static const int z = 0;
    static const int y = z;
    static const int x = z + y + a;
    return y;
}

unsigned int h(void) {
  return arr[0];
}
