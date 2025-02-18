/*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
*/

typedef char  (*object_f1_t)(unsigned long object);
typedef short (*object_f2_t)(unsigned long object);
typedef int   (*object_f3_t)(unsigned long object);

typedef struct {
    object_f1_t f1_ptr;
    object_f2_t f2_ptr;
    object_f3_t f3_ptr;
} obj_fnptr_t;

typedef struct {
    char  c1;
    short s1;
    int   i1;
} obj1_t;

typedef struct {
    short s2;
    int   i2;
    char  c2;
} obj2_t;

#define ptr(x) ((void *) x)

char
obj1_f1(unsigned long object) {
    obj1_t *obj = ptr(object);
    return obj->c1;
}

short
obj1_f2(unsigned long object) {
    obj1_t *obj = ptr(object);
    return obj->s1;
}

int
obj1_f3(unsigned long object) {
    obj1_t *obj = ptr(object);
    return obj->i1;
}

char
obj2_f1(unsigned long object) {
    obj2_t *obj = ptr(object);
    return obj->c2;
}

static const obj_fnptr_t array[] =
  {
    {
        .f1_ptr = obj1_f1, .f2_ptr = obj1_f2, .f3_ptr = obj1_f3
    },
    {
       .f1_ptr = obj2_f1, .f2_ptr = 0, .f3_ptr = 0
    }
  };

char
f1(unsigned short type, unsigned long x) {
    if (array[type].f1_ptr != 0) {
        return (char) array[type].f1_ptr(x);
    } else {
        return 1;
    }
}
