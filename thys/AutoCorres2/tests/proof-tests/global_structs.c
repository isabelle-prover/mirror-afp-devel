/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef struct S1 
{
unsigned int f1; 
int  f2;
} S1;

typedef struct S2 
{
unsigned int g1; 
int  g2;
} S2;


struct S1 s1;
struct S2 * s2 = 0;



int s1_access(unsigned int n, int i) {
  s1.f1 = n;
  s1.f2 = i;
  return s1.f2;
};

int s2_access(unsigned int n, int i) {
  s2->g1 = n;
  s2->g2 = i;
  return s2->g2;
};