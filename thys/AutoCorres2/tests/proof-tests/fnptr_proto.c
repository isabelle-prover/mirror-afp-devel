/*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef struct buffer {
  unsigned char * buf;
  unsigned int len;
} buffer_t; 

struct workers_t
{
	unsigned int (*worker1) (unsigned char *, unsigned int);
	unsigned int (*worker2) (unsigned char *, unsigned int);
};

unsigned int inc_ptr(unsigned int * n, unsigned m) {
  return (*n) + m;
}
unsigned int dec_ptr(unsigned int * n, unsigned m) {
  return (*n) - m;
}

unsigned int caller(unsigned int * n, unsigned m) {
  return inc_ptr(n, m);
}
unsigned int w(unsigned char* p, unsigned int n);
unsigned int w1(unsigned char* p, unsigned int n);
__attribute__((__pure__)) unsigned int w2(unsigned char* p, unsigned int n);

unsigned int w_buf(buffer_t * p);
unsigned int v(unsigned char* p, unsigned int n);
void u(void);

unsigned assign_w(unsigned char * p, unsigned int n) {
  unsigned res = w(p,n) + n;
  inc_ptr(&res, n);
  return res;
}
unsigned embedded_prototypes(unsigned char * p, unsigned n) {
  unsigned res = 0;
  res = w2(p, n) + w2(p, n);  
  res = res + w(p,n);  
  res = res + w1(p,n);
}

unsigned int do_call (unsigned int (*f) (unsigned char *, unsigned int), unsigned char *v, unsigned int m)
{
	[[calls(w)]]return f(v, m);
}

unsigned int do_call_buff (unsigned int (*f) (buffer_t *), buffer_t * p)
{
	[[calls(w_buf)]]return f(p);
}

unsigned int do_call_exit (unsigned int (*f) (unsigned char *, unsigned int), unsigned char *v, unsigned int m)
{
	[[calls(w)]]return f(v, m);
}

void empty_fun(void) {
};
void call_empty_fun(void) {
  empty_fun();
}

void do_call_void (void (*f) (void)) {
  [[calls(u)]] f();
}

unsigned int func (struct workers_t *w, unsigned char v, unsigned int d)
{
	unsigned int ret = 0;
	if (d)
		ret = do_call(w->worker1, &v, d);
	else
		ret = do_call(w->worker2, &v, d);
	return ret;
}