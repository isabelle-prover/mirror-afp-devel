(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

chapter \<open>Mutual CCPO Recursion \<open>fixed_point\<close>\<close>

theory Mutual_CCPO_Recursion
  imports
    "HOL-Library.Complete_Partial_Order2"
    "AutoCorres_Utils"
  keywords "fixed_point" :: thy_goal_stmt
begin

section \<open>Relate orders between locale and type classes\<close>

lemma gfp_lub_fun: "gfp.lub_fun = Inf"
  unfolding fun_lub_def fun_eq_iff Inf_apply image_def by simp

lemma gfp_le_fun: "gfp.le_fun = (\<ge>)"
  unfolding fun_ord_def le_fun_def fun_eq_iff Inf_apply image_def by simp

lemma
  shows fst_prod_lub: "fst (prod_lub luba lubb S) = luba (fst ` S)"
    and snd_prod_lub: "snd (prod_lub luba lubb S) = lubb (snd ` S)"
  by (auto simp: prod_lub_def)

lemma fun_lub_app: "fun_lub lub S x = lub ((\<lambda>f. f x) ` S)"
  by (auto simp: fun_lub_def image_def)

lemma ccpo_Inf: "class.ccpo (Inf :: 'a::complete_lattice set \<Rightarrow> _) (\<ge>) (mk_less (\<ge>))"
  by (rule cont_intro)

lemma ccpo_Sup: "class.ccpo (Sup :: 'a::complete_lattice set \<Rightarrow> _) (\<le>) (mk_less (\<le>))"
  by (rule cont_intro)

lemma ccpo_flat: "class.ccpo (flat_lub b) (flat_ord b) (mk_less (flat_ord b))"
  using Partial_Function.ccpo[OF flat_interpretation] .

lemma monotone_pair[partial_function_mono]:
  "monotone R orda f \<Longrightarrow> monotone R ordb g \<Longrightarrow> monotone R (rel_prod orda ordb) (\<lambda>x. (f x, g x))"
  by (simp add: monotone_def)

lemma monotone_fst'[partial_function_mono]:
  "monotone orda (rel_prod ordb ordc) f \<Longrightarrow> monotone orda ordb (\<lambda>x. fst (f x))"
  by (auto simp add: monotone_def rel_prod_sel)

lemma monotone_snd'[partial_function_mono]:
  "monotone orda (rel_prod ordb ordc) f \<Longrightarrow> monotone orda ordc (\<lambda>x. snd (f x))"
  by (auto simp add: monotone_def rel_prod_sel)

lemma monotone_id_fun_elim[partial_function_mono]:
  "monotone (\<ge>) ord (\<lambda>x. x) \<Longrightarrow> monotone (\<ge>) (fun_ord ord) (\<lambda>x. x)"
  by (auto simp add: monotone_def le_fun_def fun_ord_def)

lemma monotone_id[partial_function_mono]: "monotone ord ord (\<lambda>x. x)"
  by (auto simp add: monotone_def)

lemma monotone_abs:
  "(\<And>x. monotone R Q (\<lambda>f. F f x)) \<Longrightarrow> monotone R (fun_ord Q) (\<lambda>f x. F f x)"
  by (simp add: monotone_def fun_ord_def)

lemma monotone_fun_ord_applyD:
  "monotone orda (fun_ord ordb) f \<Longrightarrow> monotone orda ordb (\<lambda>y. f y x)"
  by(auto simp add: monotone_def fun_ord_def)

lemma admissible_snd:
  "cont luba orda (prod_lub lubb Inf) (rel_prod ordb (\<ge>)) F \<Longrightarrow>
    ccpo.admissible luba orda (\<lambda>x. snd (F x))"
  unfolding ccpo.admissible_def cont_def prod_eq_iff
  by (auto simp: prod_lub_def)

lemma cont_apply_gfp: "cont gfp.lub_fun gfp.le_fun Inf (\<le>) (\<lambda>x. x c)"
  by (rule cont_applyI) (simp add: cont_def)

lemma mcont_mem_gfp:
  "mcont gfp.lub_fun gfp.le_fun (Inf) (\<ge>) F \<Longrightarrow> gfp.admissible (\<lambda>A. x \<in> F A)"
  by (auto simp: mcont_def cont_def ccpo.admissible_def)

lemma mcont2mcont_call:
  "mcont luba orda (fun_lub lubb) (fun_ord ordb) F \<Longrightarrow> mcont luba orda lubb ordb (\<lambda>x. F x c)"
  by (auto simp: mcont_def monotone_def cont_def fun_lub_def fun_ord_def le_fun_def fun_eq_iff)
     (simp add: image_def)

lemma preorder_fun_ord [partial_function_mono]: "class.preorder R (mk_less R) \<Longrightarrow> class.preorder (fun_ord R) (mk_less (fun_ord R))"
  by (force simp: class.preorder_def fun_ord_def mk_less_def)

lemma preorder_monotone_const'[partial_function_mono]: 
 "class.preorder leq (mk_less leq) \<Longrightarrow> monotone ord leq (\<lambda>_. c)"
  by (rule preorder.monotone_const)

declare preorder_rel_prodI [partial_function_mono]
declare gfp.preorder [partial_function_mono]
declare lfp.preorder [partial_function_mono]

lemma option_ord_preorder [partial_function_mono]: "class.preorder option_ord (mk_less option_ord)" 
  by simp

section \<open>Prove admissibility of \<open>corresXF\<close>\<close>

lemma not_imp_not_iff: "(\<not>A \<longrightarrow> \<not>B) \<longleftrightarrow> (B \<longrightarrow> A)"
  by auto

lemma mcont_fun_lub_call:
  "mcont luba orda (fun_lub lubb) (fun_ord ordb) f \<Longrightarrow>
     mcont luba orda lubb ordb (\<lambda>y. f y x)"
  by (simp add: mcont_fun_lub_apply)

lemma chain_disj_of_subsingleton:
  "Complete_Partial_Order.chain ord {r. P r} \<Longrightarrow>
    Complete_Partial_Order.chain ord {r. Q r} \<Longrightarrow>
    (\<And>r q. P r \<Longrightarrow> Q q \<Longrightarrow> r = q) \<Longrightarrow>
    Complete_Partial_Order.chain ord {r. P r \<or> Q r}"
  by (auto simp: chain_def)

definition subsingleton_set :: "'a set \<Rightarrow> bool" where
  "subsingleton_set P \<longleftrightarrow> (\<forall>a\<in>P. \<forall>b\<in>P. a = b)"

lemma subsingleton_set_empty[iff]: "subsingleton_set {}"
  by (simp add: subsingleton_set_def)

lemma subsingleton_set_singleton[iff]: "subsingleton_set {x}"
  by (simp add: subsingleton_set_def)

context ccpo
begin

lemma subsingleton_sets_imp_chain:
  "subsingleton_set (\<Union> Ps) \<Longrightarrow> Complete_Partial_Order.chain (\<le>) (\<Union> Ps)"
  by (auto simp: subsingleton_set_def Complete_Partial_Order.chain_def Ball_def)

lemma Sup_of_subsingleton_sets_eq:
  assumes Ps: "subsingleton_set (\<Union> Ps)" and P: "P \<in> Ps" and a: "a \<in> P"
  shows "Sup (\<Union> Ps) = a" 
proof (intro order.antisym ccpo_Sup_least ccpo_Sup_upper subsingleton_sets_imp_chain[OF Ps])
  fix x :: 'a assume "x \<in> \<Union> Ps"
  then obtain Q where "Q \<in> Ps" "x \<in> Q" by auto
  with Ps P a show "x \<le> a"
    by (auto simp add: subsingleton_set_def Ball_def)
qed (use P a in blast)

lemma monotone_Sup_of_subsingleton_sets:
  assumes Ps: "\<And>F. subsingleton_set (\<Union> (Ps F))"
    and *: "\<And>F G. ord F G \<Longrightarrow> sim_set (sim_set (\<le>)) (Ps F) (Ps G)"
  shows "monotone ord (\<le>) (\<lambda>F. Sup (\<Union> (Ps F)))"
proof (intro monotoneI ccpo_Sup_least subsingleton_sets_imp_chain[OF Ps])
  fix F G x assume "ord F G" "x \<in> \<Union> (Ps F)"
  with *[of F G] obtain y where "x \<le> y" "y \<in> \<Union> (Ps G)"
    by (fastforce simp: sim_set_def)
  then show "x \<le> Sup (\<Union> (Ps G))"
    apply (intro order_trans[OF \<open>x \<le> y\<close>])
    apply (intro ccpo_Sup_upper subsingleton_sets_imp_chain[OF Ps])
    apply auto
    done
qed

lemma ccpo_refl: "x \<le> x" ..

lemma fixp_unfold_def:
  fixes f :: "'a \<Rightarrow> 'a"
  assumes def: "F \<equiv> ccpo.fixp Sup (\<le>) f"
  assumes f: "monotone (\<le>) (\<le>) f"
  shows "F = f F"
  by (unfold def) (rule fixp_unfold[OF f])

lemma fixp_induct_def:
  fixes f :: "'a \<Rightarrow> 'a"
  assumes def: "F \<equiv> ccpo.fixp Sup (\<le>) f"
  assumes mono: "monotone (\<le>) (\<le>) f"
  assumes adm: "ccpo.admissible Sup (\<le>) P"
  assumes bot: "P (Sup {})"
  assumes step: "\<And>x. P x \<Longrightarrow> P (f x)"
  shows "P F"
  by (unfold def) (rule fixp_induct[OF adm mono bot step])

lemma induct_Sup_of_subsingleton_sets:
  assumes Ps: "subsingleton_set (\<Union> Ps)"
    and adm: "ccpo.admissible Sup (\<le>) P"
    and bot: "P (Sup {})"
    and step: "\<And>p x. p \<in> Ps \<Longrightarrow> x \<in> p \<Longrightarrow> P x"
  shows "P (Sup (\<Union> Ps))"
proof cases
  assume *: "(\<Union> Ps) = {}" from bot show ?thesis unfolding * .
next
  assume *: "(\<Union> Ps) \<noteq> {}"
  show ?thesis
    by (intro ccpo.admissibleD[OF adm subsingleton_sets_imp_chain[OF Ps] *])
       (blast intro: step)
qed

lemma induct_Sup_of_subsingleton_sets_def:
  assumes F: "F \<equiv> Sup (\<Union> Ps)"
  assumes Ps: "subsingleton_set (\<Union> Ps)"
    and adm: "ccpo.admissible Sup (\<le>) P"
    and bot: "P (Sup {})"
    and step: "\<And>p x. p \<in> Ps \<Longrightarrow> x \<in> p \<Longrightarrow> P x"
  shows "P F"
  unfolding F by (rule induct_Sup_of_subsingleton_sets; fact)

end

lemma flat_lub_empty: "flat_lub x {} = x"
  by (simp add: flat_lub_def)

lemma monotone_bind_option[partial_function_mono]:
  "monotone ord option_ord f \<Longrightarrow> (\<And>a. monotone ord option_ord (\<lambda>x. g x a)) \<Longrightarrow>
    monotone ord option_ord (\<lambda>x. Option.bind (f x) (g x))"
  by (fastforce simp: monotone_def flat_ord_def bind_eq_None_conv)

lemma (in ccpo) admissible_ord: "ccpo.admissible Sup (\<le>) (\<lambda>x. x \<le> b)"
  by (clarsimp simp add: ccpo.admissible_def intro!: ccpo_Sup_least)

ML_file \<open>mutual_ccpo_recursion.ML\<close>

setup \<open>
  (Mutual_CCPO_Rec.add_ccpo "option" Mutual_CCPO_Rec.synth_option
    #> Mutual_CCPO_Rec.add_ccpo "lfp" Mutual_CCPO_Rec.synth_lfp
    #> Mutual_CCPO_Rec.add_ccpo "gfp" Mutual_CCPO_Rec.synth_gfp)
  |> Context.theory_map \<close>

no_notation top ("\<top>")
no_notation bot ("\<bottom>")
no_notation sup (infixl "\<squnion>" 65)
no_notation inf (infixl "\<sqinter>" 70)

hide_const (open) cont

end
