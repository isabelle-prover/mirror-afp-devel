(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Memset
imports "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "memset.c"

autocorres [
  heap_abs_syntax,
  no_heap_abs=memset,
  no_signed_word_abs=memset,
  unsigned_word_abs=memset] "memset.c"

lemma c_guard_word8_ptr [simp]:
     "c_guard (x :: word8 ptr) = (x \<noteq> NULL)"
  apply (clarsimp simp: c_guard_def ptr_aligned_def c_null_guard_def)
  apply (metis Ptr_ptr_val first_in_intvl intvl_Suc not_less_eq ptr_val.ptr_val_def)
  done

lemma to_bytes_word8 [simp]: "to_bytes (a :: word8) x = [a]"
  by (clarsimp simp: to_bytes_def typ_info_word word_rsplit_same)

lemma heap_update_list_id [simp]:
    "heap_update_list x [] = (\<lambda>x. x)"
  apply (rule ext)
  apply simp
  done

lemma heap_update_heap_update_list:
   "\<lbrakk> ptr_val p = q + (of_nat (length l)); Suc (length l) < addr_card \<rbrakk> \<Longrightarrow>
      heap_update (p :: word8 ptr) v (heap_update_list q l s) = (heap_update_list q (l @ [v]) s)"
  supply unsigned_of_nat [simp del]
  apply (rule ext)
  apply (clarsimp simp: heap_update_def unat_of_nat
    addr_card word_bits_def fun_upd_def)
  apply (subst heap_update_list_value, clarsimp simp: addr_card)
  apply safe
   apply (subst if_P)
    apply (fastforce intro: intvlI)
   apply (clarsimp simp: unat_of_nat word_bits_def)
  apply (subst (1 2)  heap_update_list_value,
    simp add: addr_card,
    simp add: addr_card)
  apply (case_tac "x \<in> {q..+length l}")
   apply (subst if_P, simp)
   apply (subst if_P)
    apply clarsimp
    apply (metis (full_types) intvlD intvlI less_SucI)
   apply (subst nth_append, clarsimp)
   apply (metis (opaque_lifting, no_types) add_diff_cancel2 intvlD le_unat_uoi less_or_eq_imp_le not_le)
  apply clarsimp
  apply (metis intvlD intvlI less_antisym)
  done

lemmas runs_to_whileLoop2 =  runs_to_whileLoop_res' [split_tuple C and B arity: 2]

lemma (in ts_definition_memset) memset:

"n < addr_card \<Longrightarrow> 0 \<notin> {ptr_val p ..+ n} \<Longrightarrow>
                memset' p c n \<bullet> s0
          \<lbrace> \<lambda>rv s. s = t_hrs_'_update (hrs_mem_update
              (heap_update_list (ptr_val p) (replicate n (scast c)))) s0 \<rbrace>"
  unfolding memset'_def
  apply runs_to_vcg
      apply (rule runs_to_whileLoop2 [where R="measure (\<lambda>((d', n'), _). n')"
                and I="\<lambda>(d', n') s.
                   n' \<le> n \<and>
                   (n' \<le> n \<longrightarrow> d' = ptr_coerce p +\<^sub>p int (n - n')) \<and>
                   (n' \<le> n \<longrightarrow> s = t_hrs_'_update
                  (hrs_mem_update (heap_update_list (ptr_val p) (replicate (n - n') (scast c)))) s0)"])
     apply runs_to_vcg
  subgoal by simp
  subgoal by (clarsimp simp: CTypesDefs.ptr_add_def)
  subgoal by simp
  subgoal
    apply simp
    apply runs_to_vcg
    subgoal
      apply (clarsimp simp: CTypesDefs.ptr_add_def)
      by (metis diff_diff_cancel intvlI of_nat_diff zero_less_diff)
    subgoal by arith
    subgoal
      by (clarsimp simp: CTypesDefs.ptr_add_def)
    subgoal
      apply (clarsimp simp: CTypesDefs.ptr_add_def)
      apply (rule globals.fold_congs, simp, simp)
      apply (clarsimp simp: hrs_mem_update_def)
      apply (subst heap_update_heap_update_list)
        apply (clarsimp simp: CTypesDefs.ptr_add_def)
       apply (clarsimp)
       apply arith
      apply (metis diff_Suc_diff_eq2 diff_diff_left minus_nat.diff_0 replicate_Suc_append)
      done
    subgoal by simp
    done
  done

lemma word_rsplit_sword_0 [simplified, simp]:
  "word_rsplit (0 :: addr_bitsize signed word) = replicate (size_of TYPE(addr)) (0 :: word8)"
  apply (simp add: word_rsplit_def bin_rsplit_def Let_def)
  done

lemma word_rsplit_word_0 [simplified, simp]:
  "word_rsplit (0 :: addr_bitsize word) = replicate (size_of TYPE(addr)) (0 :: word8)"
  apply (simp add: word_rsplit_def bin_rsplit_def Let_def)
  done

lemma heap_update_zero_node [simplified]:
  "heap_update_list p (replicate (size_of TYPE(node_C)) 0) = heap_update (Ptr p) (node_C NULL 0)"
  apply (rule ext)
  apply (clarsimp simp: heap_update_def to_bytes_def)
  apply (subst packed_type_access_ti, simp)
  apply (clarsimp simp: access_ti\<^sub>0_def)
  apply (clarsimp simp: to_bytes_def to_bytes_p_def node_C_tag_def node_C_typ_info)
  apply (subst final_pad_def)
  apply (clarsimp simp: typ_info_word size_td_lt_ti_typ_pad_combine Let_def padup_def)
  apply (clarsimp simp: ti_typ_pad_combine_def)
  apply (clarsimp simp: ti_typ_combine_def empty_typ_info_def typ_info_ptr typ_info_word)
  done

lemma (in memset_global_addresses) is_valid_node_C_non_NULL [simplified, simp]:
  "ptr_valid (heap_typing (lift_global_heap s)) (p::node_C ptr) \<Longrightarrow> 0 \<notin> {ptr_val p ..+ size_of TYPE(node_C)}"
  by (meson c_guard_def c_null_guard_def heap_node_C.valid_implies_c_guard)

lemma (in ts_definition_zero_node) zero_node:
  "ptr_valid (heap_typing s\<^sub>0 ) p \<Longrightarrow> zero_node' p \<bullet> s\<^sub>0 \<lbrace> \<lambda>rv s. s = s\<^sub>0[p := (node_C NULL 0) ] \<rbrace> "
  thm zero_node'_def
  apply (clarsimp simp: zero_node'_def )
  supply memset [runs_to_vcg]
  apply runs_to_vcg
  subgoal by (simp add: addr_card)
  subgoal by (simp add: is_valid_node_C_non_NULL)
  subgoal by (simp add:  is_valid_node_C_non_NULL addr_card heap_update_zero_node write_commutes update_node_def)
  done

end
