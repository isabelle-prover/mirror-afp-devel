(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Tests for handling "try" construct introduced by Autocorres.
 *)
theory "try"
imports "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "try.c"

autocorres []"try.c"

context ts_definition_w begin

thm w'_def
print_synthesize_rules exit
lemma "w' x \<equiv>
  do { whileLoop (\<lambda>x s. 0 < x)
               (\<lambda>x. condition (\<lambda>s. x = 0x2A)
                       (throw 1)
                       (return (x - 1)))
              x;
             skip
         }"
  \<comment> \<open>we do not want a \<^const>\<open>try\<close> to show up in the definition of \<^const>\<open>w'\<close>!\<close>
  by (rule w'_def)

end

context ts_definition_f begin

thm f'_def

lemma "f' x \<equiv>
  (do { assert_0' (sint x);
       when (x = 1) (throw ((- 1)));
       return (x + 1)
   })"
  \<comment> \<open>we do not want a \<^const>\<open>try\<close> to show up in the definition of \<^const>\<open>f'\<close>!\<close>
  by (rule f'_def)

end

context ts_definition_g begin

thm g'_def

lemma "g' x \<equiv>
  (do { assert_0' (sint x);
       condition (\<lambda>s. x = 1)
         (throw (- 1))
         (return (x + 1))
   })"
  \<comment> \<open>we do not want a \<^const>\<open>try\<close> to show up in the definition of \<^const>\<open>g'\<close>!\<close>
  by (rule g'_def)

end

context ts_definition_h begin

thm h'_def

lemma "h' x \<equiv>
  do { assert_0' 1;
    (a, b) <- return (if x = 0 then (2, 3) else (6, 7));
    ret <- return (do_cmp' a b);
    unless (ret = 0) (assert_0' 2)
  }"
  \<comment> \<open>we do not want a \<^const>\<open>try\<close> to show up in the definition of \<^const>\<open>h'\<close>!\<close>
  by (rule h'_def)

end

context wa_definition_i1 begin
thm wa_def
end
context ts_definition_i1 begin

thm i1'_def

lemma "i1' x \<equiv>
  do { assert_0' (sint x);
    condition (\<lambda>s. x = 0)
      (do { assert_0' 0;
           return 1
       })
      (return (x + 1))
  }"
  \<comment> \<open>we do not want a \<^const>\<open>try\<close> to show up in the definition of \<^const>\<open>i1'\<close>!\<close>
  by (rule i1'_def)

end

context ts_definition_i2 begin

thm i2'_def
term i2'

lemma "i2' x \<equiv> do { assert_0' (sint x);
              condition (\<lambda>s. x = 0)
                (liftE (do { x <- return 1;
                           return (x + 1)
                        }))
                (do{ assert_0' (sint x);
                     return 1
                 })
          }"
  \<comment> \<open>we do not want a \<^const>\<open>try\<close> to show up in the definition of \<^const>\<open>i2'\<close>!\<close>
  
  by (rule i2'_def)

end

context ts_definition_i3 begin

thm i3'_def [no_vars]

lemma "i3' x \<equiv> do {
  _ \<leftarrow> assert_0' (sint x);
  condition (\<lambda>s. 0 < x) 
    (condition (\<lambda>s. x = 1) 
      (do {v \<leftarrow> assert_0' 1; return 1})
      (return 2))
    (return (x + 1))
}"
  \<comment> \<open>we do not want a \<^const>\<open>try\<close> to show up in the definition of \<^const>\<open>i3'\<close>!\<close>
  by (rule i3'_def)

end

context ts_definition_i4 begin

thm i4'_def
term i4'
lemma "i4' x \<equiv>
  do { assert_0' (sint x);
        condition (\<lambda>s. x = 0)
          (do { assert_0' 0;
               modify (a_''_update (\<lambda>old. 0));
               return 0
           })
          (return (x + 1))
    }"
  \<comment> \<open>we do not want a \<^const>\<open>try\<close> to show up in the definition of \<^const>\<open>i4'\<close>!\<close>
  by (rule i4'_def)

end

context ts_definition_finally_elimination2 begin

thm finally_elimination2'_def
term finally_elimination2'
lemma "finally_elimination2' x \<equiv>
heap_w32.assume_with_fresh_stack_ptr 1 (\<lambda>a. {[x]})
 (\<lambda>x\<^sub>p. do {condition (\<lambda>s. 2 < heap_w32 s x\<^sub>p)
             (do {x <- gets (\<lambda>s. heap_w32 s x\<^sub>p);
                 ret <- return (inc_value' x);
                 modify (heap_w32_update (\<lambda>h. h(x\<^sub>p := ret)))
              })
             (inc' x\<^sub>p)
        })"
  \<comment> \<open>we do not want a \<^const>\<open>finally\<close> to show up in the definition of
    \<^const>\<open>finally_elimination2'\<close>!\<close>
  by (rule finally_elimination2'_def)

end

end
