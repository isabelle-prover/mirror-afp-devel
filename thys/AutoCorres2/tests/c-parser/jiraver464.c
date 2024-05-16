/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int y;

/** DONT_TRANSLATE */
/** MODIFIES:
    FNSPEC
    f_spec: "\<Gamma> \<turnstile> \<lbrace> \<acute>x < 3 \<rbrace> Call f \<lbrace> \<acute>ret' < 3 \<rbrace>"
*/
int f(int x)
{
  // y++;
  return x;
}

int g(int x)
{
  return x + 1;
}


/** MODIFIES: */
/** DONT_TRANSLATE */
/** FNSPEC clz_spec:
  "\<forall>\<sigma>. \<Gamma> \<turnstile>
    \<lbrace>\<sigma>. \<acute>x \<noteq> 0 \<rbrace>
      \<acute>ret' :== PROC clz(\<acute>x)
    \<lbrace> \<acute>ret' = of_nat (word_clz \<^bsup>\<sigma>\<^esup>x) \<rbrace>"
*/
static inline int
clz(unsigned int x)
{
    return __builtin_clz(x);
}

/** MODIFIES:
    FNSPEC
        halt_spec: "\<Gamma> \<turnstile> {} Call halt_'proc {}"
*/
void halt(void);
