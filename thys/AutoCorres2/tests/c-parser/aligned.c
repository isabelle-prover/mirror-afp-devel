/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#ifdef GCC 
#include <stdio.h>
#endif
struct strc0 {int elem; int next;};
typedef struct {int elem; int next;} my_struct0;
typedef struct {int elem; int next;} __attribute__((aligned (64))) my_struct1;
typedef __attribute__((aligned (64))) struct {int elem; int next;}  my_struct_before;
typedef struct __attribute__ ((aligned (32))) {int elem; int next;}  my_struct2;
typedef struct {int elem; int next __attribute__ ((aligned (32)));} my_struct3;
typedef struct {int elem; int next; int arr[14];} my_struct5 __attribute__((aligned (64)));
typedef struct __attribute__ ((aligned((sizeof(my_struct1))))) {int elem; int next;} my_struct4;

struct outer0 {my_struct0 my_struct; unsigned field_two;};

struct outer1 {my_struct1 my_struct; unsigned field_two;};
struct outer2 {my_struct_before my_struct; unsigned field_two;};
struct outer3 {my_struct0 my_struct __attribute__((aligned (64)))  ; unsigned field_two;};
struct outer_arr1 {my_struct1 arr1[42]; unsigned field_two;};
struct outer5 {unsigned field_one; my_struct5 my_struct_arr[2];};
/* struct outer_arr2 {my_struct_before arr1[42]; unsigned field_two;}; */

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
 my_struct5 s5;
 struct outer0 o0;
 struct outer1 o1;
 struct outer2 o2;
 struct outer3 o3;
 struct outer5 o5;
 struct outer_arr1 a1;
 //struct outer_arr2 a2;
 struct B b;
 struct C c;
 //my_struct_before arr1[44]; 
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

