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

/*
void access1 (void) {
  mystruct_array_union *p = &g;
  p->all1[0] = 2;
}
*/




void bar1 () {
  nested_struct ns;
}



typedef union my_union { 
   unsigned char all1[sizeof(unsigned int)]; 
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

unsigned access2 (my_union u) {
  return u.g.x2;
}

unsigned access3 (my_union u) {
  return u.g.x1;
}


unsigned access4 (my_union * u) {
  unsigned x = u->g.x1 + u->g.x2 + u->all1[1] + u->f.f1;
//  my_union u1= (*u); // FIXME: initialisation of union fails 
//  unsigned y = u1.g.x1;
  return x; // + y ;
}

unsigned access3 (my_union u) {
  return u.g.x1;
}


my_union update1 (my_union u, unsigned x) {
  u.all1[1] = x;
  return u;
}

my_union update2 (my_union u, unsigned x) {
  u.g.x1 = x;
  return u;
}

void heap_update1 (my_union * u, unsigned x) {
  u->all1[0] = x;
}

void heap_update2 (my_union * u, unsigned x) {
  u->g.x1 = x;
}

my_union heap_update3 (my_union u, unsigned x) {
  u.g.x1 = x;
  return u;
}

regs REGS;

void reg_fun (void) {

  unsigned int r = REGS.r.reg1.all;
};

typedef struct {
  struct {
    struct {
      unsigned fld1;
      struct {
       unsigned fld;
      } fld2;
    } fld_inner2;
  } fld_inner1;
} nested3;

unsigned access_nested (nested3 x) {
  return x.fld_inner1.fld_inner2.fld1;
}

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
