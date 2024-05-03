/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


typedef struct inner {
    unsigned fld1;
    unsigned fld2;
} inner_t;


unsigned add3 (unsigned n, inner_t inner) {
  return n + inner.fld1 + inner.fld2;
}

unsigned add (unsigned n, unsigned m) {
  return n + m;
}


unsigned lookup_fld1 (inner_t inner) {
 return inner.fld1;
}

unsigned single (inner_t inner) {
 inner_t my_inner;
 my_inner.fld1 = inner.fld1;
 my_inner.fld2 = 42;
 return (add (my_inner.fld1, 1));
}

unsigned foo_selectors (inner_t inner) {
 inner_t my_inner;
 my_inner.fld1 = inner.fld1;
 my_inner.fld2 = 42;
 return (add (my_inner.fld1, my_inner.fld2));
}

unsigned foo_never (inner_t inner) {
 inner_t my_inner;
 my_inner.fld1 = inner.fld1;
 my_inner.fld2 = 42;
 return (add (my_inner.fld1, my_inner.fld2));
}

unsigned bar_selectors (inner_t inner) {
 inner_t my_inner;
 my_inner.fld1 = inner.fld1;
 my_inner.fld2 = 42;
 return (add3 (1, my_inner) + add3 (2, my_inner));
}

unsigned bar_always (inner_t inner) {
 inner_t my_inner;
 my_inner.fld1 = inner.fld1;
 my_inner.fld2 = 42;
 return (add3 (1, my_inner) + add3 (2, my_inner));
}

