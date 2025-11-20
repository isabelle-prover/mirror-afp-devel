/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */






int inc_ptr(int * p) {
  *p = *p + 1;
  return *p;
}

int check (int n) {
  return (n < 42);
}

int inc_expr (int n) {
  int result =0;
  inc_ptr(&n);
  result = check(n) + n;
}

unsigned log_bool (unsigned n, unsigned m) {
  int x = 0;
  x = n++ && m;
  return x;

}

typedef struct elem  {
  int content;
  } elem_t;

#define NULL ((void*)0)

int elem_fun(elem_t * p) {
  elem_t * t = p;
  int x = 0;
  x = p != NULL || (t != NULL && !t->content);
  return x;
}

void content_assign (elem_t * p, int * n, int m) {
  p->content = inc_ptr(n) + m;
}

int commas(int x, int y) {
  int result = 0;
  result = x * 3;
  result = (x++, x * 2, x + 5);
  return result;
}


unsigned write (unsigned * p, unsigned v) {
  *p = v;
  return v;
}

unsigned do_write1 (unsigned * buf, unsigned v, unsigned n) {
  unsigned result = 0;
  result = write(buf++, v);
  return result;
}

unsigned for_loops(unsigned x, unsigned y) {
  unsigned result = 0;
  for (unsigned i = 0; i < 42; ++i) {
    x = x + y;
  }
  result = x * 3;
  result = (x++, x * 2, x + 5);
  return x;
}


int call_inc_ptr_assign (int x) {
  int res = 0;
  res = ({int y = x;
    inc_ptr(&y);
    y;
  });
}

unsigned g;

unsigned * some_ptr(unsigned * p) {
  g++;
  return p;
}

unsigned some_value(unsigned v) {
  g++;
  return v;
}



unsigned pre_post(unsigned x, unsigned y) {
  unsigned result = 0;
  /* result = x = y; */

  unsigned arr[100];

  result = x = y;
  result += ++y + x;
  while (x--/* -- */) {y = y + 1;}
/*
  ++y = x + 1;
  result = y;

  unsigned i = 99;
  while (--i && arr[i] == 0) {
   y += 2;}
  if (--i & --y) {
   y += 3;
  }
*/
/*
  result = (y--)?y:x;
*/
  if (y-- && y) {return 42;} 
/*
  if (y--) {result = y;} {result = y;}
  switch (y--) {
  case 0: return y;
  case 1: return y;
  default: return y;
  }
*/
  return result;

  
}



unsigned main1 (unsigned * p, unsigned v) {
  unsigned result = some_value(v++); /* should be rejected */
}


/*
unsigned main (unsigned * p, unsigned v) {
  *(some_ptr(p)) = some_value(v); // should be rejected 
}
*/
unsigned arr[120];

unsigned add (unsigned x, unsigned y) {
  return (x + y + arr[2]);
}

unsigned arr_upd(unsigned i, unsigned v) {
  arr[i++] = add(v, v);
}







typedef struct pair {
  unsigned fst;
  unsigned snd;
} pair_t;

unsigned pair_fun(pair_t p1, pair_t p2, unsigned i) {
  unsigned res = 0;
  unsigned arr[10];
  p1.fst = p2.fst;



}


int pure_add(int x, int y) {return x + y;}

int statement_expr_return(void) {
 int x = 0;
 int z = 0;
 return ({int y = x + 1; 
   z = y + 1;
   z;});
}

int statement_expr_return1(void) {
 int x = 0;
 int z = 0;
 return ({int y = x + 1; 
   z = y + 1;
   pure_add(z, y);});
}



int call_inc_ptr_init (int x) {

  int res = ({int y = x;
    inc_ptr(&y);
    y;
  });
}

int call_inc_ptr_assign2 (int x) {
  int res = 0;
  res = ({x = x + 1; x = x + 2;
    ({int y = x;
    inc_ptr(&y);
    y;
  });});
  res = ({int y = x;
    inc_ptr(&y);
    y;
  });
}

int call_inc_ptr_assign1 (int x) {
  int res = 0;
  res = ({x = x + 1; x = x + 2;
    ({int y = x;
    inc_ptr(&y);
    y;
  });});
}



int call_inc_ptr (int x) {
  int res = 0;
  inc_ptr (&x);
  res = x;
  return res;
}


int statement_expr_typeof(void) {
 int x = 0;
 int z = 0;
 z= ({int y = x + 1; 
   z = y + 1;
   (typeof(pure_add(x, y))) z + 1; });
  return z;
}

int proto(int x, int y);
__attribute__((__const__)) int proto_const(int x, int y);
__attribute__((__pure__)) int proto_pure(int x, int y);

int call_proto(int x, int y) {
  int res = 0;
  res = proto_const(x, y) + proto_const(x, y);
  res = proto_pure(x, y) + proto_pure(x, y);
  res = proto_pure(x, y) + proto_const(x, y);
  res = proto(x, y) + proto_const(x, y);
/*  res = proto(x, y) + proto_pure(x, y); */
  res = proto(x, y) + x + y;
  return res;
}

int statement_expr_stmt(void) {
 int x = 0;
 int z = 0;
  ({int y = x + 1; 
   z = y + 1;
   z = z + 1; });
  return z;
}

int statement_expr_stmt1(void) {
 int x = 0;
 int z = 0;
  ({int y = x + 1; 
   z = y + 1;
   pure_add(z,z); });
  return z;
}

int statement_expr_stmt2(void) {
 int x = 0;
 int z = 0;
  ({int y = x + 1; 
   z = y + 1;
   z + y; });
  return z;
}

int statement_expr_assign_ecall_nested(void) {
 int x = 0;
 int z = 0;
 x = ({int y = x + 1; 
   z = y + 1;
  z = ({int k = y +1;
        k + y;}); 
   pure_add(x, y) + z + y; });
  return z;
}


int statement_expr_assign_ecall(void) {
 int x = 0;
 int z = 0;
  x = ({int y = x + 1; 
   z = y + 1;
   pure_add(z, x) + 1; });
  return z;
}
int statement_expr_assign_call(void) {
 int x = 0;
 int z = 0;
  x = ({int y = x + 1; 
   z = y + 1;
   pure_add(z, x); });
  return z;
}

int statement_expr_assign_cond(void) {
 int x = 0;
 int z = 0;
  x = ({int y = x + 1; 
   z = y + 1;
   z == 0 ? z : z + 1; });
  return z;
}

int statement_nested_expr_assign(void) {
 int x = 0;
 int z = 0;
  x = ({int y = x + 1; 
   z = y + 1;
   ({z = z + 1; z;}); });
  return z;
}

int g1;
int g2;

int any_add(int x, int y) {g1 = x + y; return g1;}
int call_test(int x, int y) {
  int res = any_add(pure_add(x, y), any_add(x,y));
  return res;
}

int call_pure (int x, int y) {

  x = pure_add(x, y);
  return x;
}

int ro_add(int x, int y) {return x + y + g1;}
int any_add2(int x, int y) {g2 = x + y; return g2;}
int bad_fun(int x, int y) {
  int res = 0; 
  res = any_add(x, y) + g2;
}

_Bool uadd_overflow(unsigned int x, unsigned int y, unsigned int *sum)
{
    *sum = x + y;
    return *sum < x;
}

unsigned safe_add(unsigned x, unsigned y) {
  unsigned res = 0;
  if (!uadd_overflow(x, y, &res)) {exit(1);};
  return res;
}



int foo1(void) {
  int * x = 0;
  return 42 + g1 + *x;
} 

int emb_fun(int x) {
  int res = 0;
  res = x + ro_add(x, x);
  return res;
}



int statement_expr_if(void) {
 int x = 0;
 int z = 0;
  if (({int y = x + 1; 
   z = y + 1;
   z; })) 
     {z++;} 
  else {z--;};
  return z;
}

int statement_expr_assign(void) {
 int x = 0;
 int z = 0;
  x = ({int y = x + 1; 
   z = y + 1;
   z; });
  return z;
}

int statement_expr_var_initializer(void) {
 /* int x = 0;*/
 /* int y = 0;*/
  int z = 0;
  int x = ({int y = x + 1; 
   z = y + 1;
   (z + y); });
  return z;
}
int statement_expr_while(void) {
 int x = 0;
 int z = 0;
  while (({int y = x + 1; 
   z = y + 1;
   z + y; })) 
     {z++;} ;
  return z;
}

#define offsetof(type, member) __builtin_offsetof(type, member)

int g_static = 2;
int g_ordinary;
int g_addressed;

void main2(int n) {
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
unsigned add1(unsigned n, unsigned m) {
  unsigned ret = n + m;
  g = ret;
  return ret;
}

unsigned call_add1 (unsigned i, unsigned k) { 
  g = add1 (i, k);
  unsigned x1 = add(i,k);
  unsigned x2 = add(k, i);
  unsigned x3 = add(x2, i);
  return add(x1, x3);
}

int id(int a) {
  return *(&a);
}


typedef unsigned long word_t;

#define MY_MAX 2
#define N_BITS 12

#define calc_div(x, a) \
    (((x) + (((typeof((x))) (a)) - 1)) / ((typeof((x))) (a)))

#define calc(bits) calc_div((bits), N_BITS)

struct irq_bitmap {
  word_t bitmap[calc(MY_MAX)];
};

unsigned statement_with_paren (unsigned x) {
  unsigned v = 0;
  (v += x + 1);
  (v++);
  (add(v, x));
  return v;
}


typedef unsigned char uint8_t;

typedef struct {
  void (*g1)(void);
  unsigned (*g2) (void);
  unsigned content;
} obj_t;

obj_t *f3(uint8_t *x);
obj_t *f4(uint8_t *x);

unsigned fourty_two(void) {
  return 42;
}

void empty_fun(void) {
}

void h1(uint8_t *ptr) {

  [[calls(empty_fun)]] f4(ptr)->g1(); 
}

unsigned h2(uint8_t *ptr) {
  unsigned x = 0;
  [[calls(fourty_two)]]x = f4(ptr)->g2(); 
  return x;
}


/*
unsigned main1 (unsigned * p, unsigned v) {
  unsigned result = some_value(v++); 
}
*/
void touch_types (void) {
  struct struct_one x;
  struct struct_two y;
  struct b b;
}
