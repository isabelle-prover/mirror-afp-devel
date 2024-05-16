/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef unsigned word_t;
typedef unsigned (* unop_u_ptr_t)(word_t object);

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


void loop(void) {loop();}

unsigned binop_u(unsigned, unsigned);
typedef typeof(binop_u) binop_u_t;

int binop(int, int);
int unop(int);
typedef typeof(binop) binop_t;
typedef typeof(unop) unop_t;

int gi = 0;
unsigned gu = 2;

typedef struct object {
  binop_t * binop;
  unop_t * unop;
} object_t;

typedef struct object_u {
  binop_u_t * binop_u;
  unop_u_ptr_t unop_u;
} object_u_t;


int const_arg(const int c) {
  while (1) {
    if (c <= 0) { 
      return (c + 1);
    } else {
      return (c + 2);
   } 
 }
}

int fac(int n) {
 if (n <= 0) {
   return 0;
} else {
   return (fac (n - 1));
}
}

unsigned odd(unsigned);
unsigned even(unsigned n) {
  unsigned m = n;
  if (n==0) {
    return 1;
  } else {
    return odd(n - 1);
  } 
}

unsigned odd(unsigned m) {
  unsigned n = m;
  if (m==0) {
    return 0;
  } else {
    return even(m - 1);
  } 
}

int call_fac(int n) {
  return fac(n);
};

int silly(int n) {
 if (n <= 0) {
   exit(1);
 }
 return 0;
}

int call_silly(int n) {
  return (silly(n));
}


int add(int n, int m) {
  int k = gi;
  return n + m;
}

int minus(int n, int m) {
  return n - m;
}

int mul(int n, int m) {
  return n * m;
}

int inc(int n) {
  return n + 1;
}


int dec(int n) {
  return n - 1;
}


unsigned add_u(unsigned n, unsigned m) {
  return n + m;
}

unsigned add_gu(unsigned n, unsigned m) {
  return n + m + gu;
}

unsigned call_add_u(unsigned n, unsigned m) {
  return add_u(n, m);
}


void inc_gu(void) {
 gu = gu + 1;
}

unsigned inc_u(unsigned n) {
  return n + gu;
}


static const binop_t* add_p = add;
static const binop_u_t* add_u_p = add_u;

int call_add(int i, int j) {
  return add (i, j);
}

int indirect_call_add(int i, int j) {
  int k = 0;
  k = add_p(i, j);
  return k;
}

unsigned indirect_call_add_u(unsigned i, unsigned j) {
  return add_u_p(i, j);
}

enum type {ZERO, ONE, TWO, THREE, FOUR, TYPE_MAX};

static const object_t dispatcher[TYPE_MAX] = {
 [ZERO] = {.binop = add, .unop = inc},
 [ONE] = {.binop = minus, .unop = dec},
 [TWO] = {.binop = mul, .unop = dec},
 [THREE] = {.binop = minus, .unop = inc},
 [FOUR] = {.binop = 0, .unop = 0} 
};

int call_binop(unsigned char i, int n, int m) {
  int r = 0;
  if (dispatcher[i].binop != 0) {
  r = dispatcher[i].binop(n, m);
  }
  return (r);
};


static const object_u_t dispatcher_u[2] = {
 {.binop_u = add_u, .unop_u = inc_u},
 {.binop_u = add_gu, .unop_u = inc_u}
};

unsigned call_binop_u(int i, unsigned n, unsigned m) {
  unsigned r = 0;
  r = dispatcher_u[i].binop_u(n, m);
  return (r);
};


int parameter_call(binop_t *p, int n, int m) {
  return(p(n,m));
}

int parameter_call_add(int n, int m) {
  return parameter_call(add, n, m);
}

int nested_parameter_call(binop_t *q, int n, int m) {
  return(parameter_call(q, n, m));
}

unsigned f(unsigned x) { return x + 1; }
unsigned g(unsigned);

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

int intcaller(int (*ipfn)(void))
{
  return ipfn();
}

int callintcaller(void)
{
  return intcaller(intcallable2);
}


int call_object_binop_return(object_t * p, int x, int y)
{
  return p->binop(x,y);
}

int call_object_binop_assign(object_t * p, int x, int y)
{
  int t1 = p->binop(x,y);
  int t2 = p->binop(x,y);
  return (t1 + t2);
}

int call_object_binop_emb(object_t * p, int x, int y)
{
  int t = add (p->binop(x,y), p->binop(x,y));
  return (t + x + y);
}



typedef enum {
	Success,
	Error 
} Return;

typedef unsigned (*myop_t_ptr)(unsigned arg1);
typedef struct object1 object1_t;

struct object1 {
  myop_t_ptr unop;
};

unsigned call_object0(const object1_t *  p)
{
  unsigned n = 0;
  n = p->unop(0);
  return n;
}

unsigned call_object1(const object1_t *  p)
{
  Return n = 0;
  n = p->unop(0);
  return n;
}




