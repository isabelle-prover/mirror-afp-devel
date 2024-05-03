/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned glob_arr[4];
unsigned glob(unsigned u) {
  glob_arr[2] = u;
}

int unsigned_to_signed (unsigned n) {
  int m;
  m = (int) n;
  return m;
}
int max (int a, int b) {
 if (a <= b) {
   return b;
 } else { 
   return a;
 }
};

unsigned g = 0;

signed add(signed n, signed m) {
  return (n + m);
}

signed call_add(signed p, signed q) {
  unsigned result = p + q;
  result = add(q, p);
  return result;
}


void void_proc(unsigned n, unsigned m) {
  g = n + m;
}

void call_void_proc(unsigned n) {
  void_proc(n,2);
}
unsigned seq_assign (unsigned n) {
  unsigned m = 0;
  unsigned k = 0;
  unsigned o = 0;
  m = n + 1;
  k = m + 1;
  n = n + 1;
  m = n + 1;
  void_proc(n, m);
  void_proc(n, k);
  n = n + 1;
  m = n + 1;
  n = n + 1;
  m = m + n;
  k = k+ 1;
  n = m + n;
  m = n + 6;
  k = m + n;
  n = n + 1;
  m = n + 6;
  o = k + n + o;
  if (m > n) {
    k = n + 2;
    
  } else {
    k = n + 3;
    k = n + 2;


  }
  return n + m + k + o;
}

unsigned call_seq_assign (unsigned x) {
  return seq_assign(x);
};


unsigned inc_g(void) {
  g = g + 1;
  return g;
}

unsigned deref (unsigned* p) {
  return *p;
}

unsigned deref_g (void) {
  return (deref (&g));
}



unsigned factorial(unsigned n) {
  if(n == 0) return 1;
  return n * factorial(n-1);
}


unsigned call_factorial(void) {
  return factorial(42);
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


unsigned dead_f(unsigned);
unsigned dead_h(unsigned);
unsigned dead_g(unsigned n) {
  if (0) { 
    return dead_f(n);
  } else {
    return n;
  }
}

unsigned dead_f(unsigned n) {
  if (0) { 
    return dead_g(n);
  } else {
    return dead_h(n);
  }
}
unsigned dead_h(unsigned n) {
  return dead_f(n);
}


