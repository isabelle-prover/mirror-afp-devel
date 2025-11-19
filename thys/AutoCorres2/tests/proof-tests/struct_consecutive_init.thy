(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory struct_consecutive_init imports
  "AutoCorres2_Main.AutoCorres_Main"
begin


install_C_file "struct_consecutive_init.c"


text \<open>Capture C-Ideom to initialize a struct value by a sequence of assignments.
Even when executed within a while loop the dependency of the the initial (unspecified)
value of \<^verbatim>\<open>p0\<close> is removed.
In the translation from Simpl to L1 subsequent assignments to the same local variable
are combined and simplified to a constructor application. 
And thus liveness analysis (in translation from L1 to L2) will remove the 
dependency of the inner while loop on \<^verbatim>\<open>p0\<close>. Additionally in the optimization phase
of L2 will remove the now superfluous assignment to a unspecified value.

Note that it also works for nested structs. But not for partial initialisation. This would 
require a liveness analysis on the level of struct components and not only on the complete struct.
 \<close>


autocorres [] "struct_consecutive_init.c"

context l1_corres_in_loop
begin
thm l1_in_loop'_def
thm l1_in_loop'_corres
thm l1_opt_in_loop'_def
end

context l1_definition_string_of_vars
begin
thm l1_opt_string_of_vars'_def
end


context struct_consecutive_init_all_impl
begin

thm nested'_def
thm in_loop_partial'_def [of n m k]
thm in_loop'_def
thm string_of_vars'_def
thm string_of_vars_explode'_def
lemma "in_loop' n m k \<equiv> 
  do { whileLoop (\<lambda>i s. i \<le> n)
      (\<lambda>i. do {modify (G_''_update (\<lambda>old. 0));
              guard (\<lambda>s. 0 \<le> 2147483649 + i);
              guard (\<lambda>s. i \<le> INT_MAX - 1);
              return (i + 1)
           })
      (sint 0);
      gets (\<lambda>s. sint (G_'' s))
  }"
  by (simp add: in_loop'_def)

lemma "in_loop_nested' n m k \<equiv> do { whileLoop (\<lambda>i s. i \<le> n)
                              (\<lambda>i. do {modify (G_''_update (\<lambda>old. 0));
                                      guard (\<lambda>s. 0 \<le> 2147483649 + i);
                                      guard (\<lambda>s. i \<le> INT_MAX - 1);
                                      return (i + 1)
                                   })
                             0;
                            gets (\<lambda>s. sint (G_'' s))
                         }"
  by (simp add: in_loop_nested'_def)


lemma "in_loop_partial' n m k \<equiv> do {p0 <- unknown;
                             whileLoop (\<lambda>(i, p0) a. i \<le> n)
                               (\<lambda>(i, p0). do {condition (\<lambda>s. i = 2)
                                               (modify (G_''_update (\<lambda>old. 0)))
                                               (modify (G_''_update (\<lambda>old. 0x17)));
                                             guard (\<lambda>s. 0 \<le> 2147483649 + i);
                                             guard (\<lambda>s. i \<le> INT_MAX - 1);
                                             return (i + 1, a_C_update (\<lambda>_. 0) p0)
                                          })
                              (0, p0);
                             gets (\<lambda>s. sint (G_'' s))
                          }
"
  by (simp add: in_loop_partial'_def return_bind cong del: whileLoop_cong)
thm partial_declare_before_use'_def
thm nested'_def
thm nested_partial'_def

end

context ts_definition_crosswise_init
begin
thm ts_def
lemma "crosswise_init' \<equiv> do {
  i \<leftarrow> owhile (\<lambda>i s. i \<le> (2::32 word)) (\<lambda>i. oreturn (i + 1)) 0;
  oreturn ()
}"
  unfolding crosswise_init'_def .

end

context ts_definition_cond_init
begin
thm ts_def [no_vars]
lemma "cond_init' i \<equiv> if i < 0x2A then POINT_C 0x21 0x2C else POINT_C 0x21 0x2A"
  unfolding ts_def .
end

context ts_definition_cond_init1
begin
thm ts_def [no_vars]
lemma "cond_init1' i \<equiv> if i < 0x2A then POINT_C 0x21 0x2C else POINT_C 0x21 0x2A"
  unfolding ts_def .
end

context ts_definition_cond_init_while
begin
thm ts_def [no_vars]
lemma "cond_init_while' i \<equiv> do {
  (i, y) \<leftarrow>
    owhile (\<lambda>(i, x) s. i < 0x64)
     (\<lambda>(i, x).
         oreturn
          (case if i < 0x2A
                then (POINT_C (UCAST(32 \<rightarrow> 32 signed) i + 3) (UCAST(32 \<rightarrow> 32 signed) i),
                      POINT_C (UCAST(32 \<rightarrow> 32 signed) i + 2) (UCAST(32 \<rightarrow> 32 signed) i))
                else (POINT_C (UCAST(32 \<rightarrow> 32 signed) x + 2) (UCAST(32 \<rightarrow> 32 signed) i),
                      POINT_C (UCAST(32 \<rightarrow> 32 signed) i + 3) (UCAST(32 \<rightarrow> 32 signed) i)) of
           (dst, src) \<Rightarrow>
             (i + 1,
              x + i + SCAST(32 signed \<rightarrow> 32) (a_C src) + SCAST(32 signed \<rightarrow> 32) (b_C dst) + SCAST(32 signed \<rightarrow> 32) (b_C src) +
              SCAST(32 signed \<rightarrow> 32) (a_C dst))))
     (i, 0);
  oreturn y
}"
  unfolding ts_def .
end

context ts_definition_cond_init_while4
begin
thm ts_def [no_vars]
lemma "cond_init_while4' i \<equiv> do {
  (i, y) \<leftarrow>
    owhile (\<lambda>(i, x) s. i < 0x64)
     (\<lambda>(i, x).
         oreturn
          (case if i < 0x2A
                then (POINT_C (UCAST(32 \<rightarrow> 32 signed) i + 6) (UCAST(32 \<rightarrow> 32 signed) i),
                      POINT_C (UCAST(32 \<rightarrow> 32 signed) i + 4) (UCAST(32 \<rightarrow> 32 signed) i),
                      POINT_C (UCAST(32 \<rightarrow> 32 signed) i + 3) (UCAST(32 \<rightarrow> 32 signed) i),
                      POINT_C (UCAST(32 \<rightarrow> 32 signed) i + 2) (UCAST(32 \<rightarrow> 32 signed) i))
                else (POINT_C (UCAST(32 \<rightarrow> 32 signed) i + 7) (UCAST(32 \<rightarrow> 32 signed) i),
                      POINT_C (UCAST(32 \<rightarrow> 32 signed) i + 5) (UCAST(32 \<rightarrow> 32 signed) i),
                      POINT_C (UCAST(32 \<rightarrow> 32 signed) x + 2) (UCAST(32 \<rightarrow> 32 signed) i),
                      POINT_C (UCAST(32 \<rightarrow> 32 signed) i + 3) (UCAST(32 \<rightarrow> 32 signed) i)) of
           (four, three, dst, src) \<Rightarrow>
             (i + 1,
              x + i + SCAST(32 signed \<rightarrow> 32) (a_C src) + SCAST(32 signed \<rightarrow> 32) (b_C dst) +
              SCAST(32 signed \<rightarrow> 32) (b_C src) +
              SCAST(32 signed \<rightarrow> 32) (a_C dst) +
              SCAST(32 signed \<rightarrow> 32) (a_C three) +
              SCAST(32 signed \<rightarrow> 32) (b_C three) +
              SCAST(32 signed \<rightarrow> 32) (a_C four) +
              SCAST(32 signed \<rightarrow> 32) (b_C four))))
     (i, 0);
  oreturn y
}"
  unfolding ts_def .
end

context ts_definition_cond_init_while_nested
begin
thm ts_def [no_vars]
lemma "cond_init_while_nested' i \<equiv> do {
  (i, y) \<leftarrow>
    owhile (\<lambda>(i, x) s. i < 0x64)
     (\<lambda>(i, x).
         oreturn
          (case if i < 0x2A
                then (i + 1,
                      x + i + SCAST(32 signed \<rightarrow> 32) (UCAST(32 \<rightarrow> 32 signed) i + 2) + SCAST(32 signed \<rightarrow> 32) (UCAST(32 \<rightarrow> 32 signed) i + 3) +
                      SCAST(32 signed \<rightarrow> 32) (UCAST(32 \<rightarrow> 32 signed) i) +
                      SCAST(32 signed \<rightarrow> 32) (UCAST(32 \<rightarrow> 32 signed) i) +
                      SCAST(32 signed \<rightarrow> 32) (UCAST(32 \<rightarrow> 32 signed) i + 4) +
                      SCAST(32 signed \<rightarrow> 32) (UCAST(32 \<rightarrow> 32 signed) i))
                else (i + 1,
                      x + i + SCAST(32 signed \<rightarrow> 32) (UCAST(32 \<rightarrow> 32 signed) i + 3) + SCAST(32 signed \<rightarrow> 32) (UCAST(32 \<rightarrow> 32 signed) i + 4) +
                      SCAST(32 signed \<rightarrow> 32) (UCAST(32 \<rightarrow> 32 signed) i) +
                      SCAST(32 signed \<rightarrow> 32) (UCAST(32 \<rightarrow> 32 signed) i) +
                      SCAST(32 signed \<rightarrow> 32) (UCAST(32 \<rightarrow> 32 signed) i + 5) +
                      SCAST(32 signed \<rightarrow> 32) (UCAST(32 \<rightarrow> 32 signed) i)) of
           (x, xa) \<Rightarrow> (x, xa)))
     (i, 0);
  oreturn y
}"
  unfolding ts_def .
end

end