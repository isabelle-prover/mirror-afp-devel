/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned char * table[1] = { 0 };

void write_table(unsigned char * ptr1) {
  table[0] = ptr1;
}

unsigned char g(unsigned char i)
{
  unsigned char *ptr = table[i];
  return *ptr;
}

unsigned char f(unsigned char i)
{
  return *(table[i]);
}
