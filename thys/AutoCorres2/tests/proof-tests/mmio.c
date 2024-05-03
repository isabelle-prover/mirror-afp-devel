/*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned int state = 0;
unsigned int g1 = 0;
unsigned int g2 = 0;

/* We have this dummy definition to ensure that \<Gamma> is defined */
void dummy(void) {
  int i = 0;
};

/** DONT_TRANSLATE
    FNSPEC step_spec: "\<forall>st. \<Gamma> \<turnstile> \<lbrace>\<acute>state = st \<rbrace> Call step_'proc \<lbrace>abs_step st \<acute>state\<rbrace>" 
    MODIFIES: state 
*/
void step(void);
/* According to the code, local variables are not supported in L2 abstraction
for Spec command
*/

/** DONT_TRANSLATE
    FNSPEC step2_spec: "\<forall>g1 g2. \<Gamma> \<turnstile> \<lbrace>(\<acute>g1, \<acute>g2) = (g1, g2) \<rbrace> Call step2_'proc \<lbrace>abs_step2 (g1, g2) (\<acute>g1, \<acute>g2) \<rbrace>" 
    MODIFIES: g1 g2 
*/
void step2(void);
/* According to the code, local variables are not supported in L2 abstraction
for Spec command
*/

typedef struct { unsigned int x; } P_t;
P_t p1;
P_t p2;
void init_P(void) {
  p1 = p2;
  p2 = p1;
};
/** DONT_TRANSLATE
    FNSPEC step3_spec: "\<forall>p1 p2. \<Gamma> \<turnstile> \<lbrace>(\<acute>p1, \<acute>p2) = (p1, p2) \<rbrace> Call step3_'proc \<lbrace>
      (abs_step2 (x_C p1, x_C p2) (x_C \<acute>p1, x_C \<acute>p2) \<or>
       abs_step2 (x_C \<acute>p1, x_C \<acute>p2) (x_C p1, x_C p2) ) &
      x_C \<acute>p1 = x_C p1 & x_C \<acute>p1 = x_C p2
 \<rbrace>" 
    MODIFIES: g1 g2 
*/
void step3(void);
/* According to the code, local variables are not supported in L2 abstraction
for Spec command
*/