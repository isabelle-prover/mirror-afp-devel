/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned main(unsigned n, unsigned *q) {
  unsigned * p = q;
  *(p++) = n;
  *p = n + 1;
  *(p--) = n + 1;
  return (*p);
}

unsigned main1(unsigned n, unsigned *q) {
  unsigned * p = q;
  *(p + 1) = n;
  *p = n + 1;
  return (*p);
}



void foo(unsigned  * p) {
  *(p++) = 0;
}

unsigned arr[120];

unsigned add (unsigned x, unsigned y) {
  return (x + y);
}

unsigned arr_upd(unsigned i, unsigned v) {
  arr[i++] = add(v, v);
  arr[v] = i++;
  while (add(v,i) ) {
    arr[i] = i;
  }
  while (add(v--,i) ) {
    arr[i] = i;
  }
  while (add(v--,i) ) {
    if (i < 2) break;
    arr[i] = i;
  }
  while (add(v--,i) ) {
    if (i < 2) continue;
    arr[i] = i;
  }
  while (add(v--,i) ) {
    if (i < 2) return 42;
    if (i < 3) goto cleanup;
    arr[i] = i;
  }
cleanup:
  return v;
}

unsigned loop1(unsigned n) {
  unsigned m = 0;
  while (n--) {
    m++;
  }
  return m;
}

unsigned loop2(unsigned n) {
  unsigned m = 0;
  while (1) {
    if (n) {n--;} else {n--; break;};
    m++;
  }
  return m;
}

unsigned main2(unsigned n) {
  unsigned m = 0;
  unsigned x = 0;
  for (unsigned i = 0; i < 120; i++) {
    arr[i] = n++ + m++;
    x = m;
  }

  while (1) {
    x--;
  }

  while (n--) {
    m++;
  }
  return m;
}

unsigned main3(unsigned n) {
  unsigned m = 0;
  unsigned x = 0;
  for (unsigned i = 0; i < 120; i++) {
    arr[i] = n++ + m++;
    x = m;
  }
  while (n--) {
    m++;
  }

  return m;
}


/* FIXME: abstract_try_catch fails here */
/*
unsigned main4(unsigned n) {
  unsigned m = 0;
  unsigned x = 0;

  while (1) {
    if (n) {n--;} else {n--; break;};
    m++;
  };

  while (1) {
    x--;
  }
  return m;
}
*/

