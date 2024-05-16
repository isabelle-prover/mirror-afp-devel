/*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


void inc (unsigned* y) {
  *y = *y + 1;
}

void inc2 (unsigned * y, unsigned * z) {
  inc(y);
  inc(z);
}

unsigned many_inc(unsigned n, unsigned m) {

  unsigned n1 = n;
  unsigned m1 = n;
  unsigned n2 = n;
  unsigned m2 = n;
  unsigned n3 = n;
  unsigned m3 = n;
  unsigned n4 = n;
  unsigned m4 = n;
  unsigned n5 = n;
  unsigned m5 = n;
  unsigned n6 = n;
  unsigned m6 = n;
  unsigned n7 = n;
  unsigned m7 = n;
  unsigned n8 = n;
  unsigned m8 = n;
  unsigned n9 = n;
  unsigned m9 = n;
  unsigned n0 = n;
  unsigned m0 = n;

  inc2(&n,  &m);
  inc2(&n1, &m1);
  inc2(&n2, &m2);
  inc2(&n3, &m3);
  inc2(&n4, &m4);
  inc2(&n5, &m5);
  inc2(&n6, &m6);
  inc2(&n7, &m7);
  inc2(&n8, &m8);
  inc2(&n9, &m9);
  inc2(&n0, &m0);

  inc2(&n,  &m);
  inc2(&n1, &m1);
  inc2(&n2, &m2);
  inc2(&n3, &m3);
  inc2(&n4, &m4);
  inc2(&n5, &m5);
  inc2(&n6, &m6);
  inc2(&n7, &m7);
  inc2(&n8, &m8);
  inc2(&n9, &m9);
  inc2(&n0, &m0);

  inc2(&n,  &m);
  inc2(&n1, &m1);
  inc2(&n2, &m2);
  inc2(&n3, &m3);
  inc2(&n4, &m4);
  inc2(&n5, &m5);
  inc2(&n6, &m6);
  inc2(&n7, &m7);
  inc2(&n8, &m8);
  inc2(&n9, &m9);
  inc2(&n0, &m0);


  inc2(&n,  &m);
  inc2(&n1, &m1);
  inc2(&n2, &m2);
  inc2(&n3, &m3);
  inc2(&n4, &m4);
  inc2(&n5, &m5);
  inc2(&n6, &m6);
  inc2(&n7, &m7);
  inc2(&n8, &m8);
  inc2(&n9, &m9);
  inc2(&n0, &m0);

  inc2(&n,  &m);
  inc2(&n1, &m1);
  inc2(&n2, &m2);
  inc2(&n3, &m3);
  inc2(&n4, &m4);
  inc2(&n5, &m5);
  inc2(&n6, &m6);
  inc2(&n7, &m7);
  inc2(&n8, &m8);
  inc2(&n9, &m9);
  inc2(&n0, &m0);

  return n + n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 + n0 +
    m + m1 + m2 + m3 + m4 + m5 + m6 + m7 + m8 + m9 + m0;
}



