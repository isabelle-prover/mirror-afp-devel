/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


#include "union.h"

/*
typedef unsigned int uint32;

typedef union myunion {
  unsigned int y;
  int x;
} myunion;
*/


typedef enum color {red, green, blue} color;



typedef struct my_struct {
  int fld_i; 
  int fld_k;
  color c;
} my_struct;



typedef union reg { 
   unsigned int all; 
   struct {   
       unsigned int f1:16;    
       unsigned int f2:16;    
   }f;
} reg;


typedef union regs {
  unsigned int all[2];
  struct {
    reg reg1;
    reg reg2;
  }r;
} regs;



typedef struct nested_struct { 
   unsigned int xx;
   char ch; 
   unsigned int xy [2];
   unsigned int xz [2];
   my_struct nns [112];
   struct {   
       unsigned int n1;    
       unsigned int n2;    
       unsigned int n3;    
       unsigned int n4;    
       unsigned int n5;     
       unsigned int n6;     
   }n;
} nested_struct;

void bar (void) {

  nested_struct ns;
}



typedef struct enclosing_struct { 
   unsigned int all; 
   union nested_union {   
       unsigned int f1;
       unsigned int f2; 
   }f;
   union nested_union* p;
} nested_union;


typedef union mybitfield_union { 
   unsigned int all; 
   struct {   
       uint32 f1:8;    
       unsigned int f2:8;    
       unsigned int f3:4;    
       unsigned int f4:4;    
       unsigned int f5:4;     
       unsigned int f6:4;
   }f;
} mybitfield_union;

typedef struct mybitfield {
       unsigned int g1:8;    
       unsigned int g2:8;
       unsigned int g3:8;
       unsigned int g4:4;    
       unsigned int g5:4;    
} mybitfield;

typedef union mybitfield_union1 { 
   unsigned int all; 
   mybitfield g;
} mybitfield_union1;


typedef union mystruct_array_union { 
   unsigned int all1[2]; 
   struct {   
       unsigned int f1;    
       unsigned int f2;
   }f;
} mystruct_array_union;


int foo() {
  myunion u;
  int k;
  u.x = 42;
  //u.y = "c";
  k = u.x;
  return k;
}

void bar () {
  mybitfield_union ub;
  ub.all = 42;
  mybitfield_union1 ub1;
  ub1.all = 43;
  nested_union nu;
  nu.f.f1 = 42;
  my_struct s;
  nested_struct ns;
}


int car () {
struct local_nested_struct { 
   unsigned int xx; 
   struct {   
       unsigned int n1;    
       unsigned int n2;    
       unsigned int n3;    
       unsigned int n4;    
       unsigned int n5;     
       unsigned int n6;     
   }n;
};
 struct local_nested_struct x;
 x.n.n1 = 22;
 if (x.n.n1 == 23) {return 0;} 
 return 1;
}

mystruct_array_union g;
void access (void) {
  mystruct_array_union *p = &g;
  p->f.f1 = 2;
}


void bar1 () {
  nested_struct ns;
}


regs REGS;

void reg_fun (void) {

  unsigned int r = REGS.r.reg1.all;
};

typedef union  { 
   unsigned int all1[1]; 
   struct {   
       unsigned int f1;    
   } f;
  union {
    unsigned int x1;
    unsigned int x2;
  } g;
} my_union;

unsigned access1 (my_union u) {
  return u.all1[0];
}

my_union update1 (my_union u, unsigned n) {
  u.all1[0] = n;
  return u;
}

void heap_update1 (my_union * u, unsigned n) {
  u->all1[0] = n;
}


unsigned access2 (my_union u) {
  return u.g.x2;
}

my_union update2 (my_union u, unsigned n) {
  u.g.x2 = n;
  return u;
}

void heap_update2 (my_union * u, unsigned n) {
  u->g.x2 = n;
}

unsigned access3 (my_union u) {
  return u.g.x1;
}

unsigned access4 (my_union u) {
  return u.f.f1;
}

unsigned ptr_access3 (my_union * u) {
  return u->g.x1;
}

unsigned ptr_access_nested_struct (nested_struct * p) {
  return p->n.n1;
}

typedef struct {
  unsigned fst;
  unsigned snd;
 } unsigned_pair;

typedef struct {
  signed fst;
  signed snd;
 } signed_pair;


typedef union {
  unsigned_pair u;
  signed_pair s;
} open_union;


typedef union {
  struct {
   char b1;
   char b2;
   char b3;
   char b4;
  } all;
  unsigned f;
} fab;


unsigned access_fab1(fab * p) {
  return p->f;
}

char access_fabi2(fab * p) {
  return p->all.b1;
}

unsigned get_unsigned_first (open_union * p) {
  return (p->u.fst);
 
}

unsigned get_signed_first (open_union * p) {
  return (p->s.fst);
}

unsigned_pair * get_unsigned (open_union * p) {
  return (&(p->u));
}

typedef union {
  struct {
    char b1;
    char b2;
    unsigned short s;
  } composed1;
  struct {
    char c1;
    char c2;
    union {
      unsigned short s1;
      unsigned short s2;
    } s;
  } composed2;
  unsigned int raw;
} packed_union;

char get_b1 (packed_union x) {
  return x.composed1.b1;
}

char get_c1 (packed_union x) {
  return x.composed2.c1;
}

short get_s1 (packed_union x) {
  return x.composed2.s.s1;
}

short get_s2 (packed_union x) {
  return x.composed2.s.s2;
}

unsigned get_raw (packed_union x) {
  return x.raw;
}
