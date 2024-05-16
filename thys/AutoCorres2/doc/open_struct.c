/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef struct closed {
  unsigned c1;
  unsigned c2;
} closed_t;

typedef struct inner {
    unsigned fld1;
    unsigned fld2;
    unsigned fld3;
    closed_t fld4;
} inner_t;


typedef struct outer {
   inner_t inner;
   unsigned fld;
} outer_t;

void upd_inner(outer_t *p, inner_t * q) {
  p -> inner = *q;
}


void set_c1(closed_t * p, unsigned c) {
  p->c1 = c;
}

typedef struct unpacked {
char chr;
unsigned lng;
} unpacked_t;


long get_lng (unpacked_t * p) {
  return p->lng;
};

void set_chr (unpacked_t * p, char c) {
  p->chr = c;
};

typedef struct array {
  unpacked_t elements[2];
  unsigned int count;
} array_t;

char get_element(array_t * p, unsigned i) {
  return p->elements[i].chr;
}

char get_element_char(array_t * p, unsigned char i) {
  return p->elements[i].chr;
}

char get_element_int(array_t * p, int i) {
  return p->elements[i].chr;
}

void set_element(array_t * p, unsigned i, unsigned c) {
  p->elements[i].chr = c;
}

void set_element_int(array_t * p, int i, unsigned c) {
  p->elements[i].chr = c;
}

typedef struct other {
  unsigned fx;
  closed_t fz;
  unpacked_t fy;
} other_t;


void set_fy (other_t *p, char c) {
  p->fy.chr = c;
}


typedef struct two_dimensional {
  unpacked_t matrix[2][3];
} two_dimensional_t;

void set_matrix_element(two_dimensional_t * p, unsigned i, unsigned j, char c) {
  p->matrix[i][j].chr = c;
}


struct outer get_outer (outer_t * p) {
  return *p;
}

unsigned get_fld (outer_t *p) {
  return p->fld;
}


typedef struct outer_array {
  inner_t inner_array[5];
  unsigned fld;
} outer_array_t;

unsigned get_first_inner (outer_array_t * p) {
 return p->inner_array[1].fld1;
}

void fld_upd(outer_t *p, unsigned v)
{
    p -> fld = v;
}

inner_t get_inner (outer_t *p) {
  return p -> inner;
}


void fld1_upd(inner_t *p, unsigned v)
{
    p -> fld1 = v;
}



void outer_fld1_upd(outer_t *p, unsigned v)
{
    p -> inner.fld1 = v;
}


void outer_inner_fld1_upd(outer_t *p, unsigned v)
{
    fld1_upd (&(p -> inner), v);
}


typedef struct data {
  int x;
  unsigned y1;
  unsigned y2;
  unsigned y3;
  unsigned y4;
} data_t;

typedef struct data_array {
  data_t array[10];
} data_array_t;

typedef struct data_struct1 {
  data_t d1;
  data_t d2;
} data_struct1_t;

typedef struct data_struct2 {
  data_struct1_t d;
} data_struct2_t;

int test_data(data_t *d)
{
  return d->x;
}

int test_data_array(data_array_t *d)
{
  return test_data(&(d->array[0]));
}

int test_data_struct2(data_struct2_t *d)
{
  return test_data(&(d->d.d1));
}

void set_NULL_void(void ** p) {
 *p = 0;
}

void set_NULL_unsigned(unsigned ** p) {
 *p = 0;
}