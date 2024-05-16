/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef struct POINT {
    int a; 
    int b; 
} POINT;

typedef struct LINE {
   POINT from;
   POINT to;
} LINE;

int G;

int same(int n) {
  return n;
};

int glob_add(int n, int m) {
  G = G + n + m;
};


int in_loop(int n, int m, int k) {
  POINT p0;
  int i;
  for (i = 0; i <= n; i++) {
     p0.a = 0;
     p0.b = 0;
     if (i==2) {G = p0.a;} else {G = p0.b;}
  }
  return G;
}

int in_loop_nested(int n, int m, int k) {
  LINE l0;
  int i;
  for (i = 0; i <= n; i++) {
     l0.from.a = 0;
     l0.from.b = 0;
     l0.to.a = 0;
     l0.to.b = 0;
     if (i==2) {G = l0.from.a;} else {G = l0.to.b;}
  }
  return G;
}

int in_loop_partial(int n, int m, int k) {
  POINT p0;
  int i;
  for (i = 0; i <= n; i++) {
     p0.a = 0;
     if (i==2) {G = p0.a;} else {G = 23;}
  }
  return G;
}

int partial_declare_before_use(int n, int m, int k) {
  POINT p;
  int l1 = 0;
  int l2 = 0;

  p.a = same(n);
  l1 = p.a;
  p.b = same(m);
  l2 = p.b;

  glob_add(l1, l2);
  return G;
};

int nested(int n, int m, int k) {
  LINE l;

  l.from.a = same(n);
  l.from.b = 1;
  l.to.a = 1;
  l.to.b = same(n);

  glob_add(l.from.a, l.to.b);
  return G;
};

int nested_partial(int n, int m, int k) {
  LINE l;

  l.from.a = same(n);
  l.to.b = same(n);

  glob_add(l.from.a, l.to.b);
  return G;
};

int string_of_vars(int n) {
    int n1, n2, n3, n4, n5;
    n1 = n;
    n2 = n1;
    n3 = n2;
    n4 = n3;
    n5 = n4;
    return n5;
};

int string_of_vars_explode(int n, int m, int k) {
    int n1, n2, n3, n4, n5;
    n1 = n + k;
    n2 = n1 + m * n + 2;
    n3 = n2 + k + n;
    n4 = n3 + m * n + 2;
    n5 = n2 + n * k;
    return n5;
};

