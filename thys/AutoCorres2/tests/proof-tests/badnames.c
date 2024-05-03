/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


int bad_names(void)
{
    int globals = 3;
    int myvars = 3;
    int P = 4;
    int A = 4;
    int B = 4;
    int R = 5;
    int L1_skip = 5;
    int L2_skip = 6;
    int L1_modify = 7;
    int L2_modify = 8;
    int global_exn_var = 2;
    /* Following line used to kill local_var_extract. */
    int adglobs_addr = 4;

    return globals + global_exn_var + P + R + A + B + myvars + L1_skip + L2_skip + L1_modify + L2_modify + adglobs_addr;
}

/* Also used to kill local_var_extract. */
int bad_vars(int symbol_table)
{
    return symbol_table;
}

/* Testcase for VER-351. The C parser generates some StrictC'__assert_fail_foo param names
 * which we need to demangle carefully. */
void __assert_fail(const char *, const char *, int, const char *);

typedef struct {
  int x;
} S;

int zero(void) {
  return 0;
}

void my_exit(int line) { exit(line); }

/* Clash of return variable name, and intern return variable name */
S zero_S(int i) {
  if (!(i > 0)) my_exit(-1);
  S ret;
  ret.x = zero();
  ret.x = zero();
  return ret;
}

