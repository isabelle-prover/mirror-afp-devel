/*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned fac (unsigned n) {
  if (n == 0) { 
    return 1;
  } else {
    return n * fac (n-1);
  }
}

unsigned fac3 (unsigned n, unsigned m, unsigned k) {
  if (n + m + k == 0) { 
    return 1;
  } else {
    return (n + m + k) * fac3 (n - 1, m - 1 , k - 1);
  }
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


typedef enum {
    Good = 2,
    Bad = 4,
} return_t;


/*
typedef unsigned return_t;
*/

typedef return_t (*handler_t)(unsigned content);

typedef struct implementation {
    handler_t my_handler;
} implementation_t;


static return_t worker(unsigned arg, handler_t my_handler)
{
	return my_handler(arg);
}

return_t handler (unsigned content) {
  return Good;
}

handler_t select (void) {
  return handler;
}

return_t call_select(unsigned x) {
  handler_t p = select();
  __attribute__((calls(handler))) return p(x);
}


/* FIXME: fails in L2 */
return_t call_select_worker(unsigned x) {
  handler_t p = select();
  return worker(x, p);
}

return_t call_handler (void) {
  worker (3, handler);
}

void bar (const handler_t implementation)
{
	return_t status =  Bad ;
	status = worker(2, implementation);
}

return_t foo (const implementation_t *implementation)
{
	return_t status =  Bad ;
	[[calls(handler)]] status = implementation->my_handler(0);
/* status = worker (3, handler); */ /* FIXME: crashes L1 */
  return status;
}

return_t call_foo (const implementation_t *implementation)
{
  return foo(implementation);
}


return_t foo1 (const implementation_t *implementation)
{
	return_t status = Bad;
	status = worker(42, implementation->my_handler);
  return status;
}

return_t foo2 (const implementation_t *implementation)
{
	return_t status = Bad;
	status = worker(42, implementation->my_handler) + 2;
  return status;
}

typedef return_t (*disp_t)(const implementation_t *);


disp_t foo1_p = foo1;
disp_t foo_p = foo;


return_t call_glob_disp1(unsigned x, implementation_t * impl) {
  return_t status = foo1_p(impl);
  return status;
} 

return_t call_glob_disp(unsigned x, implementation_t * impl) {
  return_t status = foo_p(impl);
  return status;
} 

implementation_t * get_obj() {
  return 0;
}

return_t call_get_obj(void) {
  return_t status = Bad;
  implementation_t *p = get_obj();
  [[calls(handler)]] status = p->my_handler(2);
  return status;
}

implementation_t * glob_impl;
return_t glob_handler1 (unsigned x) {
  return_t status = Bad;
  implementation_t * impl = glob_impl;
  if (glob_impl == 0) {
    return Bad; 
  } else {
    [[calls(handler)]] status = impl->my_handler(x);
     return status;  
  }
  
}

return_t glob_handler2 (unsigned x) {
  return_t status = Bad;
  implementation_t * impl = glob_impl;
  if (glob_impl == 0) {
    return Bad; 
  } else {
     __attribute__ ((calls(handler))) return impl->my_handler(x);
  }
  
}
