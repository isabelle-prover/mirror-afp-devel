/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef struct {
  int r2, r3;
} seL4_UserContext;

int
useContext(seL4_UserContext *ucptr)
{
  return ucptr->r2 + ucptr->r3;
}

int
anonUseContext(void)
{
  typedef struct {int r4, r5;} foo; 
  foo *ucptr;
  struct {int r6, r7;} *vcptr;
  return ucptr->r4 + vcptr->r7;
}
