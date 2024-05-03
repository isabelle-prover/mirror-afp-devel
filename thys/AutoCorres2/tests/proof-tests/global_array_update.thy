(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory global_array_update imports "AutoCorres2_Main.AutoCorres_Main" begin

install_C_file "global_array_update.c"
autocorres [ignore_addressable_fields_error]"global_array_update.c"

print_record lifted_globals

context global_array_update_all_impl 
begin
thm bar'_def bar2'_def
end

lemma (in ts_definition_bar) "\<forall>a\<in>set (array_addrs (PTR_COERCE(32 signed word[1024] \<rightarrow> 32 signed word) foo_') 1024).
               ptr_valid (heap_typing s) ((ptr_coerce a)::32 word ptr) \<Longrightarrow>
          bar' \<bullet> s
       \<lbrace> \<lambda>_ s. heap_w32 s (ptr_coerce ( (PTR_COERCE(32 signed word[1024] \<rightarrow> 32 signed word) foo_') +\<^sub>p 3)) = 42 \<rbrace>"
  unfolding bar'_def
  term foo_'
  apply runs_to_vcg
  apply blast
  apply (clarsimp simp: set_array_addrs fun_upd_apply
      ptr_coerce_index_array_ptr_index_numeral_conv''
      simp del: replicate_numeral replicate_0 replicate_Suc)
  by simp

end
