(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Test force/prevent heap abstraction.
 *)

theory heap_lift_force_prevent
imports "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "heap_lift_force_prevent.c"

autocorres [
    no_heap_abs = unlifted_a unlifted_b,
    ts_force nondet = unlifted_a unlifted_b lifted_a lifted_b
    ] "heap_lift_force_prevent.c"


lemma heap_w32_hrs_mem [simp]:
    "\<lbrakk> ptr_valid (heap_typing (lift_global_heap s)) p; heap_w32 (lift_global_heap s) p = a \<rbrakk>
      \<Longrightarrow> h_val (hrs_mem (t_hrs_' s)) p = a"
  by (simp add: heap_w32.read_commutes)

lemma (in ts_definition_lifted_a) lifted_a_wp [runs_to_vcg]:
    "ptr_valid (heap_typing s) p \<Longrightarrow> heap_w32 s p = a \<Longrightarrow> P (Result a) s \<Longrightarrow> lifted_a' p \<bullet> s \<lbrace> \<lambda>r s. P r s \<rbrace>"
  unfolding lifted_a'_def
  apply runs_to_vcg
  apply simp
  done

lemma (in ts_definition_unlifted_a) unlifted_a_wp [runs_to_vcg]:
    "c_guard p \<Longrightarrow> P (Result (h_val (hrs_mem (t_hrs_' s)) p)) s ==>
                  unlifted_a' p \<bullet> s \<lbrace> \<lambda>r s. P r s \<rbrace>"
  unfolding unlifted_a'_def
  by runs_to_vcg

lemma (in ts_definition_lifted_b) lifted_b_wp [runs_to_vcg]:
    "ptr_valid (heap_typing s) p \<Longrightarrow>  heap_w32 s p = a \<Longrightarrow> P (Result (a * 3)) s \<Longrightarrow> lifted_b' p \<bullet> s \<lbrace> \<lambda>r s. P r s \<rbrace>"
  unfolding lifted_b'_def
  apply runs_to_vcg
  apply (auto simp: simple_lift_c_guard lift_global_heap_def field_simps
      intro: ptr_valid_h_t_valid h_t_valid_c_guard)
  done

lemma  (in ts_definition_unlifted_b) unlifted_b_wp [runs_to_vcg]:
    "ptr_valid (hrs_htd (t_hrs_' s)) p \<Longrightarrow>
      \<forall>t. lift_global_heap t = lift_global_heap s \<longrightarrow> P (Result (h_val (hrs_mem (t_hrs_' t)) p * 3)) t \<Longrightarrow>
              unlifted_b' p \<bullet> s \<lbrace> \<lambda>r s. P r s \<rbrace>"
  unfolding unlifted_b'_def
  apply runs_to_vcg

    apply (auto simp add: ptr_valid_c_guard mult.commute)
  by (metis (no_types, lifting) dbl_inc_def dbl_inc_simps(3) distrib_right 
      heap_w32_hrs_mem lifted_globals_ext_simps(4) mult_numeral_1 numeral_One)


end

