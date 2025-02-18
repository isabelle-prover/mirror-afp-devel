/*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


typedef struct pair {
unsigned fst;
unsigned snd;
} pair_t;


unsigned get_fst(pair_t p, pair_t *q) {
 if (p.fst == 0) {
   exit (1);
 } else {
   q -> fst = p.snd;
   q -> snd = p.fst;
   return (q->fst);
 }
}

pair_t * g;

unsigned main(unsigned n, unsigned m) {
  unsigned n1 = n;
  unsigned m1 = n;
  pair_t local_p;
  local_p.fst = n;
  local_p.snd = m;
  m1 = get_fst(local_p, g);
  return m + n + n1 + m1;
}



