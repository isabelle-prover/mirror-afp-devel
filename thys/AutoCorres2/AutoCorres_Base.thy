(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

chapter "Basic Stuff" 
theory AutoCorres_Base
  imports
  "TypHeapLib"
  "LemmaBucket_C"
  "CTranslation"
  "Synthesize"
  "Cong_Tactic"

  "Reaches"
  "Mutual_CCPO_Recursion"
  "Simp_Trace"
begin

definition THIN :: "prop \<Rightarrow> prop" where "PROP THIN (PROP P) \<equiv> PROP P"

lemma THIN_I: "PROP P \<Longrightarrow> PROP THIN (PROP P)"
  by (simp add: THIN_def)

ML_file \<open>utils.ML\<close>

named_theorems corres_admissible and corres_top
named_theorems funp_intros and fun_of_rel_intros


definition fun_of_rel:: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "fun_of_rel r f = (\<forall>x y. r x y \<longrightarrow> y = f x)"

definition funp:: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
 "funp r = (\<exists>f. fun_of_rel r f)" 

lemma funp_witness: "fun_of_rel r f \<Longrightarrow> funp r"
  by (auto simp add: funp_def)

lemma funp_to_single_valuedp: "funp r \<Longrightarrow> single_valuedp r"
  by (auto simp add: single_valuedp_def funp_def fun_of_rel_def)

lemma fun_of_rel_xval[fun_of_rel_intros]:
  "fun_of_rel L f_l \<Longrightarrow> fun_of_rel R f_r \<Longrightarrow> fun_of_rel (rel_xval L R) (map_xval f_l f_r)"
  by (auto simp add: fun_of_rel_def rel_xval.simps)

lemma funp_rel_xval[funp_intros, corres_admissible]:
  assumes L: "funp L" 
  assumes R: "funp R" 
  shows "funp (rel_xval L R)"
proof -
  from L obtain f_l where f_l: "\<And>x y. L x y \<longrightarrow> y = f_l x" by (auto simp add: funp_def fun_of_rel_def)
  from R obtain f_r where f_r: "\<And>x y. R x y \<longrightarrow> y = f_r x" by (auto simp add: funp_def fun_of_rel_def)
  define f where "f = map_xval f_l f_r"
  {
    fix x y
    have "rel_xval L R x y \<longrightarrow> y = f x"
      using f_l f_r
      by (auto simp add: rel_xval.simps f_def)
  }
  then show ?thesis
    by (auto simp add: funp_def fun_of_rel_def)
qed

lemma fun_of_rel_eq[fun_of_rel_intros]: "fun_of_rel (=) (\<lambda>x. x)"
  by (auto simp add: fun_of_rel_def)

lemma fun_of_rel_bot[fun_of_rel_intros]: "fun_of_rel (\<lambda>_ _. False) f"
  by (auto simp add: fun_of_rel_def)

lemma funp_eq[funp_intros, corres_admissible]: "funp (=)"
  by (auto simp add: funp_def fun_of_rel_def)

lemma admissible_mem: "ccpo.admissible Inf (\<ge>) (\<lambda>A. x \<in> A)"
  by (auto simp: ccpo.admissible_def)

lemma funp_rel_prod[funp_intros, corres_admissible]: 
  assumes L: "funp L" 
  assumes R: "funp R" 
  shows "funp (rel_prod L R)"
proof -
  from L obtain f_l where f_l: "\<And>x y. L x y \<longrightarrow> y = f_l x" by (auto simp add: funp_def fun_of_rel_def)
  from R obtain f_r where f_r: "\<And>x y. R x y \<longrightarrow> y = f_r x" by (auto simp add: funp_def fun_of_rel_def)
  define f where "f = map_prod f_l f_r"
  {
    fix x y
    have "rel_prod L R x y \<longrightarrow> y = f x"
      using f_l f_r
      by (auto simp add: rel_prod.simps f_def map_prod_def split: prod.splits)
  }
  then show ?thesis
    by (auto simp add: funp_def fun_of_rel_def)
qed

lemma funp_rel_sum[funp_intros, corres_admissible]:
  assumes L: "funp L" 
  assumes R: "funp R" 
  shows "funp (rel_sum L R)"
proof -
  from L obtain f_l where f_l: "\<And>x y. L x y \<longrightarrow> y = f_l x" by (auto simp add: funp_def fun_of_rel_def)
  from R obtain f_r where f_r: "\<And>x y. R x y \<longrightarrow> y = f_r x" by (auto simp add: funp_def fun_of_rel_def)
  define f where "f = sum_map f_l f_r"
  {
    fix x y
    have "rel_sum L R x y \<longrightarrow> y = f x"
      using f_l f_r
      by (auto simp add: rel_sum.simps f_def)
  }
  then show ?thesis
    by (auto simp add: funp_def fun_of_rel_def)
qed

lemma fun_of_rel_bottom: "fun_of_rel ((\<lambda>_ _. False)) f"
  by (auto simp add: fun_of_rel_def)

lemma funp_bottom [funp_intros, corres_admissible]: "funp (\<lambda>_ _. False)"
  using fun_of_rel_bottom
  by (metis funp_def)

lemma fun_of_rel_prod[fun_of_rel_intros]:
  "fun_of_rel L f_l \<Longrightarrow> fun_of_rel R f_r \<Longrightarrow> fun_of_rel (rel_prod L R) (map_prod f_l f_r)"
  by (auto simp add: fun_of_rel_def)

lemma fun_of_rel_sum[fun_of_rel_intros]:
  "fun_of_rel L f_l \<Longrightarrow> fun_of_rel R f_r \<Longrightarrow> fun_of_rel (rel_sum L R) (sum_map f_l f_r)"
  by (auto simp add: fun_of_rel_def rel_sum.simps)

lemma fun_of_relcompp[fun_of_rel_intros]: "fun_of_rel F f \<Longrightarrow> fun_of_rel G g \<Longrightarrow> fun_of_rel (F OO G) (g o f)"
  by (auto simp add: fun_of_rel_def)

lemma funp_relcompp[funp_intros, corres_admissible]: "funp F \<Longrightarrow> funp G \<Longrightarrow> funp (F OO G)"
  using fun_of_relcompp
  by (force simp add: funp_def)


lemma fun_of_rel_rel_map[fun_of_rel_intros]: "fun_of_rel (rel_map f) f"
  by (auto simp add: fun_of_rel_def rel_map_def)

lemma funp_rel_map[funp_intros, corres_admissible]: "funp (rel_map f)"
  using fun_of_rel_rel_map
  by (auto simp add:funp_def)

lemma ccpo_prod_gfp_gfp:
  "class.ccpo
    (prod_lub Inf Inf :: (('a::complete_lattice * 'b :: complete_lattice) set \<Rightarrow> _))
    (rel_prod (\<ge>) (\<ge>)) (mk_less (rel_prod (\<ge>) (\<ge>)))"
  by (rule ccpo_rel_prodI ccpo_Inf)+

lemma runs_to_partial_top[corres_top]: "\<top> \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (simp add: runs_to_partial_def_old)

lemma refines_top[corres_top]: "refines C \<top> s t R"
  by (auto simp add: refines_def_old)

lemma pred_andE[elim!]: "\<lbrakk> (A and B) x; \<lbrakk> A x; B x \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by(simp add:pred_conj_def)

lemma pred_andI[intro!]: "\<lbrakk> A x; B x \<rbrakk> \<Longrightarrow> (A and B) x"
  by(simp add:pred_conj_def)

(* A version of "measure" that takes any wellorder, instead of
 * being fixed to "nat". *)
definition measure' :: "('a \<Rightarrow> 'b::wellorder) => ('a \<times> 'a) set"
where "measure' = (\<lambda>f. {(a, b). f a < f b})"

lemma in_measure'[simp, code_unfold]:
    "((x,y) : measure' f) = (f x < f y)"
  by (simp add:measure'_def)

lemma wf_measure' [iff]: "wf (measure' f)"
  apply (clarsimp simp: measure'_def)
  apply (insert wf_inv_image [OF wellorder_class.wf, where f=f])
  apply (clarsimp simp: inv_image_def)
  done

lemma wf_wellorder_measure: "wf {(a, b). (M a :: 'a :: wellorder) < M b}"
  apply (subgoal_tac "wf (inv_image ({(a, b). a < b}) M)")
   apply (clarsimp simp: inv_image_def)
  apply (rule wf_inv_image)
  apply (rule wellorder_class.wf)
  done

lemma wf_custom_measure:
  "\<lbrakk> \<And>a b. (a, b) \<in> R \<Longrightarrow> f a < (f :: 'a \<Rightarrow> nat) b \<rbrakk> \<Longrightarrow>  wf R"
  by (metis in_measure wf_def wf_measure)

lemma rel_fun_conversep': "rel_fun R Q f g \<longleftrightarrow> rel_fun R\<inverse>\<inverse> Q\<inverse>\<inverse> g f"
  unfolding rel_fun_def by auto

end
