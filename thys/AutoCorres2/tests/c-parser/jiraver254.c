/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int f(int x)
{
  _Bool b = (x < 10);
  return (b == 0);
}

int g(_Bool b2)
{
  return b2 > 3;
}

_Bool h(_Bool b3)
{
  return !b3;
}

_Bool comp(_Bool b1, _Bool b2)
{
  _Bool x = b1 && h(!b2) || h(b2);
 return x; 
}

/* pointers convert to bool, being 1 if non-null, 0 otherwise */
_Bool ptrconversion(char *ptr)
{
  return ptr;
}
