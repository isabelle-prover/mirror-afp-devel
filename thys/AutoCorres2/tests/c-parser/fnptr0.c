/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


unsigned f(unsigned x) { return x + 1; }

unsigned g(unsigned);


typedef unsigned word_t;
typedef unsigned (* unop_u_ptr_t)(word_t object);

unsigned unop_u(unsigned);
typedef typeof(unop_u) unop_u_t;

unsigned odd_disp(unsigned);
unsigned even_disp(unsigned);

static const unop_u_ptr_t odd_even_dispatcher[2] = {
 odd_disp,
 even_disp
};



unsigned even_disp(word_t n) {
  if (n==0) {
    return 1;
  } else {
  return (odd_even_dispatcher[0])(n - 1);
  } 
}

unsigned odd_disp(word_t n) {
  if (n==0) {
    return 0;
  } else {
    return (odd_even_dispatcher[1])(n - 1);
  } 
}


unsigned binop_u(unsigned, unsigned);
unsigned unop_u(unsigned);


int binop(int, int);
int unop(int);

int gi = 0;
typedef typeof(binop) binop_t;
typedef typeof(unop) unop_t;

typedef typeof(binop_u) binop_u_t;

typedef struct object {
  binop_t * binop;
  unop_t * unop;
} object_t;

int add(int n, int m) {
  int k = gi;
  return n + m;
}


int minus(int n, int m) {
  return n - m;
}

int inc(int n) {
  return n + 1;
}

int dec(int n) {
  return n - 1;
}

typedef struct simple {
  int f1;
  int f2;
} simple_t;


static const simple_t s = {.f1=0, .f2=1};

static const int arr[2] = {1, 2};
static const simple_t sarr[2] = {{.f1=0, .f2=1}, {.f1=3, .f2=4}};

unsigned add_u(unsigned n, unsigned m) {
  return n + m;
}


static const object_t subtractor = {.binop = minus, .unop = dec};

static const binop_t* add_p = add;
static const binop_u_t* add_u_p = add_u;

int indirect_call_add(int n, int m) {
  return add_p(n, m);
}

int indirect_call_add_u(int i, int j) {
  return add_u_p(i, j);
}

static const object_t dispatcher[2] = {
 {.binop = add, .unop = inc},
 {.binop = minus, .unop = dec}
};

int call_binop(int i, int n, int m) {
  int r = 0;
  r = dispatcher[i].binop(n, m);
  return (r);
};

int parameter_call(binop_t *p, int n, int m) {
  return(p(n,m));
}

int parameter_call_add(int n, int m) {
  return(parameter_call(add, n, m));
}

int nested_parameter_call(binop_t *p, int n, int m) {
  return(parameter_call(p, n, m));
}

/*
int call_binop_obj(object_t * p, int n, int m) {
  return (p->binop(n, m));
}

int call_binop_global(int n, int m) {
  return (subtractor.binop(n, m));
}
*/

void callthem(void)
{
  g((int)f);
  g((int)&f);
}

unsigned global1, global2;

void callable1(void)
{
  global1++;
}

void callable2(void)
{
  global2++;
}

int voidcaller(void (*pfn)(void))
{
  pfn();
  return 2;
}

int callvoidcaller(void)
{
  return voidcaller(callable1);
}

int intcallable1(void)
{
  return 3;
}

int intcallable2(void)
{
  return 4;
}

int intcaller(int (*ipfn)(void) /** CALLS intcallable2 */)
{
  return ipfn();
}

int callintcaller(void)
{
  return intcaller(intcallable2);
}
