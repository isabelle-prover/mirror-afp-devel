/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include "mmio.c"

/** DONT_TRANSLATE
    FNSPEC builtin_unreachable_spec: "
      \<Gamma> \<turnstile> \<lbrace> False \<rbrace>
        Call unreachable_'proc
      \<lbrace> True \<rbrace>"
    MODIFIES:
 */
void unreachable(void);

/** DONT_TRANSLATE
    FNSPEC empty_spec: "
      \<Gamma> \<turnstile> \<lbrace> \<acute>state < 42 \<rbrace>
        Call unreachable_'proc
      \<lbrace> False \<rbrace>"
    MODIFIES:
 */
void empty(void);

void call_unreachable (unsigned i) {
 if (i < 2) {unreachable();};
}