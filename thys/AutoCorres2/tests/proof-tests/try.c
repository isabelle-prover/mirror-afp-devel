/*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// forces exit monad
void assert_0(int x) {
  if (x == 0)
    exit(-1);
}

unsigned int f(unsigned int x) {
  assert_0(x);
  if (x == 1)
    exit(-1);
  return (x + 1);
}

unsigned int g(unsigned int x) {
  assert_0(x);
  if (x == 1)
    exit(-1);
  else
    return (x + 1);
}


unsigned int do_cmp(unsigned int a, unsigned int b) {
  return a == b;
}

// tuples
void h(unsigned int x) {
    
  unsigned int cmp;
  unsigned int a, b;
  assert_0(1);
  if(x == 0) {
    a = 2;
    b = 3;
  } else {
    a = 6;
    b = 7;
  }
  cmp = do_cmp(a, b);
  if(cmp != 0) {
    assert_0(2);
  }
  return;
}

// exiting conditions
unsigned int i1(unsigned int x) {
  assert_0(x);
  if (x == 0) {
    assert_0(x);
    return 1;
  }
  x = x + 1;
  return x;
}

unsigned int i2(unsigned int x) {
  assert_0(x);
  if (x == 0) {
    x = x + 1;
  } else {
    assert_0(x);
    return 1;
  }
  x = x + 1;
  return x;
}

unsigned int i3(unsigned int x) {
  assert_0(x);
  if (x > 0) {
    if (x == 1)
      assert_0(x);
    else
      return 2;
    return 1;
  }
  x = x + 1;
  return x;
}

static unsigned int a;
unsigned int i4(unsigned int x) {
  assert_0(x);
  if (x == 0) {
    assert_0(x);
    a = x;
    return x;
  }
  x = x + 1;
  return x;
}

// while loop
void w(unsigned int x) {
  while (x > 0) {
    if (42 == x)
      exit(1);
    else
      x--;
  }
}

// pointers to locals
unsigned inc_value(unsigned x) {
  return x+1;
}
void inc(unsigned *x) {
  *x=*x+1;
}
void finally_elimination2(unsigned x) {
  if (x > 2) {
     x = inc_value(x);
     return;
  };
  inc(&x);
}