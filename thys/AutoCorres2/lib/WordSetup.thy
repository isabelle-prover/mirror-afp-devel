(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)



theory WordSetup (* part of non-AFP Word_Lib *)
  imports
  Word_Lemmas_32_Internal
  Word_Lemmas_64_Internal
  Distinct_Prop
begin

(* Distinct_Prop lemmas that need word lemmas: *)

lemma distinct_prop_enum:
  "\<lbrakk> \<And>x y. \<lbrakk> x \<le> stop; y \<le> stop; x \<noteq> y \<rbrakk> \<Longrightarrow> P x y \<rbrakk>
     \<Longrightarrow> distinct_prop P [0 :: 'a :: len word .e. stop]"
  apply (simp add: upto_enum_def distinct_prop_map del: upt.simps)
  apply (rule distinct_prop_distinct)
   apply simp
  apply (simp add: less_Suc_eq_le del: upt.simps)
  apply (erule_tac x="of_nat x" in meta_allE)
  apply (erule_tac x="of_nat y" in meta_allE)
  apply (frule_tac y=x in unat_le)
  apply (frule_tac y=y in unat_le)
  apply (erule word_unat.Rep_cases)+
  apply (simp add: toEnum_of_nat[OF unat_lt2p]
                   word_le_nat_alt)
  done

lemma distinct_prop_enum_step:
  "\<lbrakk> \<And>x y. \<lbrakk> x \<le> stop div step; y \<le> stop div step; x \<noteq> y \<rbrakk> \<Longrightarrow> P (x * step) (y * step) \<rbrakk>
     \<Longrightarrow> distinct_prop P [0, step .e. stop]"
  apply (simp add: upto_enum_step_def distinct_prop_map)
  apply (rule distinct_prop_enum)
  apply simp
  done

lemmas word_bits_def = 
  Machine_Word_64_Basics.word_bits_def Machine_Word_32_Basics.word_bits_def 

lemmas word_size_def =
  Machine_Word_64_Basics.word_size_def Machine_Word_32_Basics.word_size_def

lemmas word_bits_size =
  Machine_Word_64.word_bits_size  Machine_Word_32.word_bits_size 

lemmas word_bits_len_of =
  Machine_Word_64.word_bits_len_of Machine_Word_32.word_bits_len_of

lemmas word_bits_conv = 
  Machine_Word_64_Basics.word_bits_conv Machine_Word_32_Basics.word_bits_conv


hide_const (open) Machine_Word_32_Basics.word_bits
hide_const (open) Machine_Word_64_Basics.word_bits
hide_const (open) Machine_Word_32_Basics.word_size
hide_const (open) Machine_Word_64_Basics.word_size
hide_const (open) Machine_Word_32_Basics.word_size_bits
hide_const (open) Machine_Word_64_Basics.word_size_bits

end
