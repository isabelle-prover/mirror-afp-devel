(*  Title:       Hereditar(il)y (Finite) Multisets
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Hereditar(il)y (Finite) Multisets\<close>

theory Hereditary_Multiset
imports Multiset_More Nested_Multiset
begin


subsection \<open>Type Definition\<close>

datatype hmultiset =
  HMSet (hmsetmset: "hmultiset multiset")

lemma hmsetmset_inject[simp]: "hmsetmset A = hmsetmset B \<longleftrightarrow> A = B"
  by (blast intro: hmultiset.expand)

primrec Rep_hmultiset :: "hmultiset \<Rightarrow> unit nmultiset" where
  "Rep_hmultiset (HMSet M) = MSet (image_mset Rep_hmultiset M)"

primrec (nonexhaustive) Abs_hmultiset :: "unit nmultiset \<Rightarrow> hmultiset" where
  "Abs_hmultiset (MSet M) = HMSet (image_mset Abs_hmultiset M)"

lemma type_definition_hmultiset:
  "type_definition Rep_hmultiset Abs_hmultiset {X. no_elem X}"
proof (unfold_locales, unfold mem_Collect_eq)
  fix X
  show "no_elem (Rep_hmultiset X)"
    by (induct X) (auto intro!: no_elem.intros)
  show "Abs_hmultiset (Rep_hmultiset X) = X"
    by (induct X) auto
next
  fix Y :: "unit nmultiset"
  assume "no_elem Y"
  thus "Rep_hmultiset (Abs_hmultiset Y) = Y"
    by (induct Y rule: no_elem.induct) auto
qed

setup_lifting type_definition_hmultiset

lemma HMSet_alt: "HMSet = Abs_hmultiset o MSet o image_mset Rep_hmultiset"
  by (auto simp: type_definition.Rep_inverse[OF type_definition_hmultiset])

lemma HMSet_transfer[transfer_rule]: "rel_fun (rel_mset pcr_hmultiset) pcr_hmultiset MSet HMSet"
  unfolding HMSet_alt by (force simp: rel_fun_def multiset.in_rel nmultiset.rel_eq
    pcr_hmultiset_def cr_hmultiset_def
    type_definition.Rep_inverse[OF type_definition_hmultiset] intro!: multiset.map_cong)


subsection \<open>Restriction of Dershowitz and Manna's Nested Multiset Order\<close>

instantiation hmultiset :: linorder
begin

lift_definition less_hmultiset :: "hmultiset \<Rightarrow> hmultiset \<Rightarrow> bool" is "op <" .
lift_definition less_eq_hmultiset :: "hmultiset \<Rightarrow> hmultiset \<Rightarrow> bool" is "op \<le>" .

instance
  by (intro_classes; transfer) auto

end

lemma less_HMSet_iff_less_multiset_ext\<^sub>D\<^sub>M: "HMSet M < HMSet N \<longleftrightarrow> less_multiset_ext\<^sub>D\<^sub>M (op <) M N"
  unfolding less_multiset_ext\<^sub>D\<^sub>M_def
proof (transfer, unfold less_nmultiset.simps less_multiset_ext\<^sub>D\<^sub>M_def, safe)
  fix M N :: "unit nmultiset multiset" and X Y
  assume *: "pred_mset no_elem (N - X + Y)" "pred_mset no_elem N" "X \<noteq> {#}"
    "X \<subseteq># N" "\<forall>k. k \<in># Y \<longrightarrow> (\<exists>a. a \<in># X \<and> k < a)"
  then have "X \<in> Collect (pred_mset no_elem)"
    unfolding multiset.pred_set mem_Collect_eq by (metis rev_subsetD set_mset_mono)
  from *(1) have "Y \<in> Collect (pred_mset no_elem)"
    unfolding multiset.pred_set mem_Collect_eq by (metis add_diff_cancel_left' in_diffD)
  show
    "\<exists>X'\<in>Collect (pred_mset no_elem). \<exists>Y'\<in>Collect (pred_mset no_elem).
      X' \<noteq> {#} \<and> filter_mset no_elem X' \<subseteq># filter_mset no_elem N \<and> N - X + Y = N - X' + Y' \<and>
      (\<forall>k\<in>Collect no_elem.  k \<in># Y' \<longrightarrow> (\<exists>a\<in>Collect no_elem. a \<in># X' \<and> k < a))"
    by (rule bexI[OF _ \<open>X \<in> Collect (pred_mset no_elem)\<close>],
        rule bexI[OF _ \<open>Y \<in> Collect (pred_mset no_elem)\<close>])
      (insert *; force simp: set_mset_diff multiset.pred_set multiset_filter_mono)
next
  fix M N :: "unit nmultiset multiset" and X Y
  assume *:
    "pred_mset no_elem (N - X + Y)" "pred_mset no_elem N" "pred_mset no_elem X" "pred_mset no_elem Y"
    "X \<noteq> {#}" "filter_mset no_elem X \<subseteq># filter_mset no_elem N"
    "\<forall>k\<in>Collect no_elem.  k \<in># Y \<longrightarrow> (\<exists>a\<in>Collect no_elem. a \<in># X \<and> k < a)"
  then have [simp]: "filter_mset no_elem X = X" "filter_mset no_elem N = N"
    unfolding filter_mset_eq_conv by (auto simp: multiset.pred_set)
  show
    "\<exists>X' Y'. X' \<noteq> {#} \<and> X' \<subseteq># N \<and>  N - X + Y = N - X' + Y' \<and>
     (\<forall>k. k \<in># Y' \<longrightarrow> (\<exists>a. a \<in># X' \<and> k < a))"
    by (rule exI[of _ X], rule exI[of _ Y]) (insert *; auto simp: multiset.pred_set)
qed

lemma hmsetmset_less[simp]: "hmsetmset M < hmsetmset N \<longleftrightarrow> M < N"
  by (cases M, cases N, simp add: less_multiset_ext\<^sub>D\<^sub>M_less less_HMSet_iff_less_multiset_ext\<^sub>D\<^sub>M)

lemma hmsetmset_le[simp]: "hmsetmset M \<le> hmsetmset N \<longleftrightarrow> M \<le> N"
  unfolding le_less hmsetmset_less by (metis hmultiset.collapse)

lemma wf_less_hmultiset: "wf {(X :: hmultiset, Y :: hmultiset). X < Y}"
  unfolding wf_eq_minimal by transfer (insert wf_less_nmultiset[unfolded wf_eq_minimal], fast)

instance hmultiset :: wellorder
  using wf_less_hmultiset unfolding wf_def mem_Collect_eq prod.case by intro_classes metis

lemma HMSet_less[simp]: "HMSet M < HMSet N \<longleftrightarrow> M < N"
  by (simp add: less_HMSet_iff_less_multiset_ext\<^sub>D\<^sub>M less_multiset_ext\<^sub>D\<^sub>M_less)

lemma HMSet_le[simp]: "HMSet M \<le> HMSet N \<longleftrightarrow> M \<le> N"
  by (simp add: hmsetmset_le[symmetric])

inductive_set hmultiset_sub where
  "X \<in># M \<Longrightarrow> (X, HMSet M) \<in> hmultiset_sub"

lemma wf_hmultiset_sub[simp]: "wf hmultiset_sub"
proof (rule wfUNIVI)
  fix P and M :: hmultiset
  assume ih: "\<forall>M. (\<forall>N. (N, M) \<in> hmultiset_sub \<longrightarrow> P N) \<longrightarrow> P M"
  show "P M"
    by (induct M; rule ih[rule_format]) (auto simp: hmultiset_sub.simps)
qed

end
