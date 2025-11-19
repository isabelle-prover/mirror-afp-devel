/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int x, y;
/** MODIFIES: x [*] */
int machine_proto(void);

/** MODIFIES: phantom_machine_state y */
int proto2(int);

int f(int i)
{
  int x1 = machine_proto();
  int x2 = proto2(i);
  return i + x1 + x2;
}

int g(void)
{
  y++;
  return x + y;
}

