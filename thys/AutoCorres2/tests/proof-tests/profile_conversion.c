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

int caller(int n, int m, int k) {
  POINT p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11  /* */;
/*
  POINT p0 = {0}; 
  POINT p1 = {0}; 
  POINT p2 = {0}; 
  POINT p3 = {0}; 
  POINT p4 = {0}; 
  POINT p5 = {0}; 
  POINT p6 = {0}; 
  POINT p7 = {0}; 
  POINT p8 = {0}; 
  POINT p9 = {0}; 
  POINT p10 = {0}; 
  POINT p11 = {0}; 
*/

  p0.a = same(n);
  p0.b = 1;

  p1.a = same(n);
  p1.b = 1;

  p2.a = same(n);
  p2.b = 1;

  p3.a = same(n);
  p3.b = 1;

  p4.a = same(n);
  p4.b = 1;

  p5.a = same(n);
  p5.b = 1;

  p6.a = same(n);
  p6.b = 1;

  p7.a = same(n);
  p7.b = 1;

  p8.a = same(n);
  p8.b = 1;

  p9.a = same(n);
  p9.b = 1;

  p10.a = same(n);
  p10.b = 1;

  p11.a = same(n);
  p11.b = 1;


  glob_add(p0.a, p0.b);

  glob_add(p1.a, p1.b);

  glob_add(p2.a, p2.b);

  glob_add(p3.a, p3.b);
  glob_add(p4.a, p4.b);

  glob_add(p5.a, p5.b);
  glob_add(p6.a, p6.b);
  glob_add(p7.a, p7.b);

  glob_add(p8.a, p8.b);
  glob_add(p9.a, p9.b);
  glob_add(p10.a, p10.b);
  glob_add(p11.a, p11.b);

  return G;
};

