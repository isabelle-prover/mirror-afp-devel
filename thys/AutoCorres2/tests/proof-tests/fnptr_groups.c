/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef unsigned (* unop)(unsigned );  
typedef void (* unop_ptr)(unsigned *);  
typedef unsigned (* binop_ptr)(unsigned *, unsigned *);  
typedef unsigned (* binop)(unsigned, unsigned );

unsigned inc(unsigned n) {return (n + 1);}
unsigned dec(unsigned n) {return (n - 1);}
unsigned add(unsigned n, unsigned m) {return (n + m);}
unsigned minus(unsigned n, unsigned m) {return (n - m);}

void inc_ptr(unsigned * n) {*n = (*n + 1);}
void dec_ptr(unsigned * n) {*n = (*n - 1);}

void inc_ptr_value(unsigned * n) {*n = (*n + 1);}

void dec_ptr_value(unsigned * n) {*n = (*n - 1);}

unsigned add_ptr_value(unsigned * n, unsigned * m) {
  if (*n > 22) exit (1);
  *n = (*n + *m);
  return 0;
}

unsigned minus_ptr_value(unsigned * n, unsigned * m) {
  if (*n < *m)  exit(1);
  *n = (*n - *m); 
  return 0;
}

unsigned * glob_m;
unsigned call_binop_ptr (binop_ptr f, unsigned n, unsigned m) {
  unsigned status = 1;
  [[calls(add_ptr_value, minus_ptr_value)]]status = f(&n, glob_m);
/*  inc_ptr (&m);*/
  inc_ptr (&n);
  return status;
}

unop unop_disp[2] = {inc, dec};
binop binop_disp[2] = {add, minus};

/*
unop_ptr unop_ptr_disp[2] = {inc_ptr, dec_ptr};
*/
unop_ptr unop_ptr_value_disp[2] = {inc_ptr_value, dec_ptr_value};

unsigned call_unop(unsigned i, unsigned n) {
  return unop_disp[i](n);
}

/*
void call_unop_ptr(unsigned i, unsigned n) {
  unop_ptr_disp[i](&n);
}
*/
void call_unop_ptr_value(unsigned i, unsigned n) {
  unop_ptr_value_disp[i](&n);
}

unsigned call_unop_param(unop f, unsigned n) {
  return f(n);
}

unsigned call_binop_param(binop g, unsigned n, unsigned m) {
  return g(n, m);
}


unsigned call_binop_param1(binop g, unsigned* n, unsigned m) {
  [[calls(add, minus)]] return g(*n, m);
}
unsigned main1 (unsigned n) {
  unsigned x1 = 0;
  x1 = call_unop_param(inc, n) ;
  return x1;
}
unsigned call_binop(unsigned i, unsigned n, unsigned m) {
  return binop_disp[i](n, m);
}


typedef struct object {
  binop a_binop;
} object_t;

typedef struct object1 {
  binop b_binop;
} object1_t;

object_t * obj;

unsigned glob_binop(unsigned n, unsigned m) {
  return obj->a_binop(n,m);
}

unsigned call_obj (object_t * p, unsigned n, unsigned m) {
  return p->a_binop(n, m);
}

unsigned call_obj1 (object1_t * p, unsigned n, unsigned m) {
  [[calls()]] p->b_binop(n, m);
}

void setup_obj(void) {
  object_t obj;
  obj.a_binop = add;
  /* binop p = &(obj.a_binop); */
}

unsigned call_binop_param_from_obj (object_t * p, unsigned n, unsigned m) {
  return call_binop_param (p->a_binop, n, m);
}

binop binop_disp1[3] = {add, minus, glob_binop};

unsigned call_binop_disp1(unsigned i, unsigned n, unsigned m) {
  return binop_disp1[i](n,m);
}

unsigned odd(unsigned);
unsigned even(unsigned);

unop odd_even_disp[2] = {odd, even};

unsigned even (unsigned n) {
  if (n == 0) {
    return 0;
  } else {
    return odd_even_disp[0](n - 1);
  }
}

unsigned odd (unsigned n) {
  if (n == 0) {
    return 1;
  } else if ( n == 1) {
    return 0;
  } else {
    return odd_even_disp[1](n - 1);
} 
}

unsigned crazy(unsigned n, unsigned m) {
  int choice = 0;
  if (n <= m) {choice = 1;}
  return binop_disp[choice](n, m);
}

binop select(unsigned n, unsigned m) {
 if (n <= m) return binop_disp[0]; else return binop_disp[1];
}


unsigned call_select(unsigned n, unsigned m) {
  binop sel = select(n,m);
  __attribute__((calls(add, minus)))  return sel(n,m);
}

unsigned call_select_empty(unsigned n, unsigned m) {
  binop sel = select(n,m);
  __attribute__((calls()))  return sel(n,m);
}

object_t object_disp[2] = {{.a_binop = add}, {.a_binop = minus}};

unsigned call_object_disp_local (unsigned i, unsigned n, unsigned m) {
  object_t x = object_disp[i];
  return x.a_binop(n, m);
}
/* Combination of clique and indirect_binop did not work.
unsigned indirect_binop(binop f, unsigned n, unsigned m) {
  return f(n, m);
}

unsigned indirect_add(unsigned n, unsigned m) {
  return indirect_binop(add, n, m);
}



unsigned indirect_crazy(unsigned n, unsigned m) {
  return indirect_binop(crazy, n, m);
}
*/
/*
typedef struct { void (* op)(unsigned char *); } object_t;

void inc(unsigned char *x) { (*x)++; }

object_t objects[1] = { { .op = inc } };

unsigned char f(void) {
  unsigned char x = 0;
  objects[0].op(&x);
  return x;
}

void call_glob(unsigned char * x) {
  objects[0].op(x);
}

object_t objects2[2] = { { .op = inc }, { .op = call_glob } };


unsigned char g(unsigned n) {
  unsigned char x = 0;
  objects2[n].op(&x);
  return x;
}
*/
/*
unsigned char obj_call(object_t* p, unsigned char n) {
  (p->op(&n));
  return n;
}
*/