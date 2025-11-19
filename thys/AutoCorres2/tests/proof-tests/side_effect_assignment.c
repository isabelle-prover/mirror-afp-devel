/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


unsigned main4(unsigned n, unsigned *q) {
  unsigned * p = q;
  *(p++) = n;
  *p = n + 1;
  *(p--) = n + 1;
  *(--p) = n - 1;
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

void write (unsigned * p, unsigned v) {
  *p = v;
}

void do_write (unsigned * buf, unsigned v, unsigned n) {
  for (unsigned i = 0; i < n; i++) {
    write(buf, v);
    buf++;
  }
}

void do_write1 (unsigned * buf, unsigned v, unsigned n) {
  for (unsigned i = 0; i < n; i++) {
    write(buf++, v);
  }
}

unsigned ptr_fun(unsigned *s, unsigned *t) {
  unsigned result = 0;
  result = *(s++) + *(t++);
  result = result + (*s) + (*t);
  return result;
}

unsigned multi_assign(unsigned n, unsigned m) {
  unsigned result = 0;
  result = n = m;
  result = result + n;
  return result;
}

void zero_loop_post (unsigned * buf, unsigned size) {
  while (size--) {
    buf[size] = 0;
  }
}

void zero_loop_pre (unsigned * buf, unsigned size) {
  while (--size) {
    buf[size] = 0;
  }
}

void for_pre (unsigned * buf, unsigned size, unsigned v) {
  for (int i = 0; i <= size; ++i, --v) {
    buf[i] = v;
  }
}

void while_log_and(unsigned * buf, unsigned size, unsigned v) {
  unsigned n = size;
  while (n-- && buf[n] == 0) {
    buf[n] = v;
  }
}

int commas (int x, int y) {
  int result = (x++, y++, x + y);
  return result;
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

