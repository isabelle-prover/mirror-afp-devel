/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int deref_int(int * p) {
  return *p;
}

void inc_ptr(int * p) {
  *p = *p + 1;
}

void inc_uptr(unsigned * p) {
  *p = *p + 1;
}


int call_inc(int x) {
  inc_ptr(&x);
  return x;
}

unsigned call_uinc(unsigned x) {
  inc_uptr(&x);
  return x;
}

unsigned call_inc_uptr_assign (unsigned x) {
  unsigned res = 0;
  res = ({unsigned y = x;
    inc_uptr(&y);
    y;
  });
  return res;
}

int call_inc_ptr_assign (int x) {
  int res = 0;
  res = ({int y = x;
    inc_ptr(&y);
    y;
  });
  return res;
}


int cex(int *old, int new) {
  *old = new;
  return 0;
}

int inc_from_assign(int *ptr, int x) {
  int ok = 0;
  ok = ({
    ({
       int cx_r = 1;
       cex(&cx_r, 2);
    });
  });
  if (ok) return x; else exit(1);
}
int inc_from_init(int *ptr, int x) {
  int ok = ({
    ({
       int cx_r = 1;
       cex(&cx_r, 2);
    });
  });
  if (ok) return x; else exit(1);
}








