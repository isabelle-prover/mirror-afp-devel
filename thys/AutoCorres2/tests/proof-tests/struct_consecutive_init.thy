(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory struct_consecutive_init imports
  "AutoCorres2_Main.AutoCorres_Main"
begin


install_C_file "struct_consecutive_init.c"

ML\<open>
val t1 = @{term "a_C ((a_C_update (\<lambda>v. 1)) (POINT_C ret__int 1))"}
val t2 = Value_Command.value @{context} t1
\<close>
term "a_C ((a_C_update (\<lambda>v. 1)) (POINT_C ret__int 1))"

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

declare [[verbose=0, ML_print_depth=1000]]

autocorres "struct_consecutive_init.c"

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
end