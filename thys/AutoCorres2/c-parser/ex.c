/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#define offsetof(type, member) __builtin_offsetof(type, member)

int g_static = 2;
int g_ordinary;
int g_addressed;

void main (int n) {
  g_ordinary = g_static + n;
  *(&g_addressed) = g_ordinary;
}
typedef struct inner {
    unsigned fld1;
    unsigned fld2;
    unsigned fld3;
} inner_t;


typedef struct outer {
   inner_t inner;
   unsigned fld;
} outer_t;



struct outer get_outer (outer_t * p) {
  return *p;
}


typedef struct unpacked {
char chr;
long lng;
} long_t;


long get_lng (long_t * p) {
  return p->lng;
};

void set_chr (long_t * p, char c) {
  p->chr = c;
};

typedef struct array {
  long_t elements[12];
} array_t;

void set_array (array_t * p, unsigned i, char c) {
  p->elements[i].chr = c;
}

typedef struct matrix {
  long_t elements[2][3];
} matrix_t;

void set_matrix (matrix_t * p, unsigned i, unsigned j, char c) {
  p->elements[i][j].chr = c;
}

struct struct_one { 
  struct struct_two *next;
};

struct struct_two { 
  struct struct_one *next;
};

struct struct_two *t;

struct a;
struct b;

struct a { 
  struct b * child;
  int x;
};
struct b {
  struct a * child;
  int x;
};

struct a a;


typedef struct {int elem; int next;}  my_struct_packed;
typedef struct {int next; my_struct_packed elem;}  my_struct_packed_nested;

typedef struct {int elem; int * next;}  __attribute__ ((aligned (64))) my_struct;

typedef unsigned long long phys_t;

phys_t f1(void)
{
   return (phys_t) 1ULL;
}

phys_t f2(void)
{
   return (typeof((phys_t) 1ULL)) 1ULL;
}

int some_decls(int n, int m) {
  typedef struct {int elem1; int * next1 __attribute__ ((aligned (16)));} my_local_struct;
  int * a[10 + sizeof(n+1)];
  int * b[sizeof(typeof(n))];
  my_struct s;
  my_local_struct t;
  my_struct_packed_nested s1;
  int k;
  typeof(s.next) p;
  k = offsetof(my_struct, next);
  k = offsetof(my_struct_packed_nested, elem.elem);
  k = offsetof(my_struct_packed_nested, elem.next);

};

int foo (int n, int m)
{
  int k;
  k = n + m + sizeof(n);
  k = (typeof(n)) k;
  return (k + 1);
}

int call_foo(void)
{
  int i, j = 0;
  int res;
  res = foo(i ,j);
  return res;
}

unsigned factorial(unsigned n) {
  if(n == 0) return 1;
  return n * factorial(n-1);
}

unsigned odd(unsigned n);
unsigned even(unsigned n) {
  if (n == 0) {
     return 1;
  } else {
     return odd(n - 1);
  }
};
unsigned odd(unsigned n) {
  if (n == 1) {
    return 1;
  } else {
    return even(n - 1);
  }
};


unsigned g;
unsigned add(unsigned n, unsigned m) {
  unsigned ret = n + m;
  g = ret;
  return ret;
}

unsigned call_add (unsigned i, unsigned k) { 
  g = add (i, k);
  return add(add(i, k), add(add(k,i), i));
}

int id(int a) {
  return *(&a);
}