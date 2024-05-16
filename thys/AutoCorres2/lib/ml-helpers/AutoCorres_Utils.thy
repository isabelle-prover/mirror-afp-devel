(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory AutoCorres_Utils
  imports 
    Print_Annotated 
    ML_Fun_Cache 
  keywords "lazy_named_theorems"::thy_decl

begin

definition CONV_ID:: "'a::{} \<Rightarrow> 'a" where
 "CONV_ID x \<equiv> x"

lemma CONV_ID_intro: "(x::'a::{}) \<equiv> CONV_ID x"
  by (simp add: CONV_ID_def)

ML_file "utils.ML"

definition "FALSE \<equiv> (\<And>P. PROP P)"
lemma ex_falso_quodlibet: "PROP FALSE \<Longrightarrow> PROP P"
  by (simp add: FALSE_def)

ML_file \<open>context_tactical.ML\<close>
ML_file "lazy_named_theorems.ML"
ML_file "interpretation_data.ML"

definition sim_set :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "sim_set R A B \<longleftrightarrow> (\<forall>a\<in>A. \<exists>b\<in>B. R a b)"

lemma sim_set_empty: "sim_set R {} B"
  by (auto simp: sim_set_def)

lemma sim_set_insert: "R a b \<Longrightarrow> sim_set R A B \<Longrightarrow> sim_set R (insert a A) (insert b B)"
  by (auto simp: sim_set_def)

lemma sim_set_Collect_Ex:
  "(\<And>a. sim_set R {x. P a x} {x. Q a x}) \<Longrightarrow> sim_set R {x. \<exists>a. P a x} {x. \<exists>a. Q a x}"
  by (fastforce simp: sim_set_def)

lemma sim_set_Collect_conj:
  "(A \<Longrightarrow> sim_set R {x. P x} {x. Q x}) \<Longrightarrow> sim_set R {x. A \<and> P x} {x. A \<and> Q x}"
  by (fastforce simp: sim_set_def)

lemma sim_set_Collect_eq:
  "R a b \<Longrightarrow> sim_set R {x. x = a} {x. x = b}"
  by (fastforce simp: sim_set_def)

lemma sim_set_eq_rel_set: "sim_set R = rel_set R OO (\<subseteq>)"
  apply (auto simp: sim_set_def rel_set_def relcomp.simps fun_eq_iff OO_def)[1]
  subgoal for A B
    by (intro exI[of _ "{b\<in>B. \<exists>a\<in>A. R a b}"]) blast
  apply blast
  done

end
