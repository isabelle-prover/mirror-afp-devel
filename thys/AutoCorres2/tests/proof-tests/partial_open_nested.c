/*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct x {
    unsigned long y;
};

struct A {
    int f1;
    int f2;
    struct x f3;
};

struct B {
    struct A a;
    int f4;
    int f5;
    int f6;
    unsigned f7;
};

int process_f(int *f) {
    return (*f) + 2;
}

int process_g(unsigned *f) {
    return (int) ((*f) + 2);
}

int process_A(struct A *a) {
    return a->f1 + a->f2;
}

int process_B(struct B *b) {
    return process_A(&(b->a)) + process_f(&(b->f4)) + process_f(&(b->f6)) + process_g(&(b->f7));
}
