/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#ifdef GCC 
#include <stdio.h>
#endif
typedef struct {int elem; int next;} my_struct0;
typedef struct {int elem; int next;}  __attribute__ ((aligned (64))) my_struct1;
typedef struct {int elem; int next;}  __attribute__ ((aligned (32))) my_struct2;
typedef struct {int elem; int next __attribute__ ((aligned (32)));} my_struct3;

typedef struct {int elem; int next;}  __attribute__ ((aligned((sizeof(my_struct1))))) my_struct4;

typedef struct A { unsigned long data[4]; } A_t;

struct B {
    int field1;
    struct A_b {
        A_t field2;
        A_t field3;
    }  __attribute__((aligned(sizeof(A_t)))) b; /* structure attribute */
};

struct C {
    int field1;
    struct A_c {
        A_t field2;
        A_t field3;
    }  c __attribute__((aligned(sizeof(A_t)))); /* field attribute */
};

int foo(void) {
 my_struct0 s0;
 my_struct1 s1;
 my_struct2 s2;
 my_struct3 s3;
 my_struct4 s4;
 struct B b;
 struct C c;
 return 1;
}

#ifdef GCC
int main(void) {
  printf ("alignof int: %lu\n", __alignof__(int));
  printf ("sizeof int: %lu\n\n", sizeof(int));

  printf ("alignof my_struct0: %lu\n", __alignof__(my_struct0));
  printf ("sizeof my_struct0: %lu\n", sizeof(my_struct0));
  printf ("offsetof (my_struct0, next): %lu\n\n", __builtin_offsetof(my_struct0, next));

  printf ("alignof my_struct1: %lu\n", __alignof__(my_struct1));
  printf ("sizeof my_struct1: %lu\n", sizeof(my_struct1));
  printf ("offsetof (my_struct1, next): %lu\n\n", __builtin_offsetof(my_struct1, next));

  printf ("alignof my_struct2: %lu\n", __alignof__(my_struct2));
  printf ("sizeof my_struct2: %lu\n", sizeof(my_struct2));
  printf ("offsetof (my_struct2, next): %lu\n\n", __builtin_offsetof(my_struct2, next));

  printf ("alignof my_struct3: %lu\n", __alignof__(my_struct3));
  printf ("sizeof my_struct3: %lu\n", sizeof(my_struct3));
  printf ("offsetof (my_struct3, next): %lu\n\n", __builtin_offsetof(my_struct3, next));

  printf ("alignof my_struct4: %lu\n", __alignof__(my_struct4));
  printf ("sizeof my_struct4: %lu\n", sizeof(my_struct4));
  printf ("offsetof (my_struct4, next): %lu\n\n", __builtin_offsetof(my_struct4, next));
}
#endif

