(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Regression for VER-320 and other array-related bugs.
 * Here we prove that writing a pointer that points into an array
 * will update the array.
 *)
theory array_indirect_update imports "AutoCorres2_Main.AutoCorres_Main" begin

install_C_file "array_indirect_update.c"
autocorres [ignore_addressable_fields_error]"array_indirect_update.c"

context ts_definition_bar begin
thm foo'_def bar'_def

lemma
  "arr = PTR_COERCE(32 signed word[10] \<rightarrow> 32 signed word) array_' \<Longrightarrow>
    \<forall>a\<in>set (array_addrs arr 10). ptr_valid (heap_typing s) ((ptr_coerce a)::32 word ptr) \<Longrightarrow>
     bar' \<bullet> s
   \<lbrace> \<lambda>Res _ s. heap_w32 s (ptr_coerce (arr +\<^sub>p 4)) = 3 \<rbrace>"
  unfolding foo'_def bar'_def
  apply (simp add: array_ptr_index_field_lvalue_conv [symmetric] 
      array_ptr_index_simps del: replicate_numeral replicate_0 replicate_Suc)
  apply runs_to_vcg
   apply blast
   apply (clarsimp simp: set_array_addrs )
  apply (subgoal_tac "(4 :: nat) < 10")
   apply fastforce
  apply arith
  done

end
end
