(*  Title:       Countable Ordinals

    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Continuity\<close>

theory OrdinalCont
  imports OrdinalInduct
begin

subsection \<open>Continuous functions\<close>

locale continuous =
  fixes F :: "ordinal \<Rightarrow> ordinal"
  assumes cont: "F (oLimit f) = oLimit (\<lambda>n. F (f n))"

lemmas continuousD = continuous.cont

lemma (in continuous) monoD: assumes "x \<le> y" shows "F x \<le> F y"
proof -
  have "oLimit (case_nat u (\<lambda>n. v)) = max u v" for u v
    apply (simp add: max_def)
    by (metis (no_types, lifting) le_oLimit less_oLimitE linorder_not_le oLimit_Suc nat.case order_le_less)
  then show "F x \<le> F y"
    by (metis \<open>x \<le> y\<close> cont le_oLimit max.absorb2 nat.case(1))
qed

lemma (in continuous) mono: "mono F"
  by (simp add: local.monoD monoI)

lemma continuousI:
  assumes lim: "\<And>f. strict_mono f \<Longrightarrow> F (oLimit f) = oLimit (\<lambda>n. F (f n))"
  assumes suc: "\<And>x. F x \<le> F (oSuc x)"
  shows "continuous F"
proof -
  have mono: "x \<le> y \<Longrightarrow> F x \<le> F y" for x y
  proof (induction y arbitrary: x rule: oLimit_induct)
    case zero
    then show ?case by auto
  next
    case (suc x)
    with assms show ?case
      by (metis antisym_conv1 le_oSucE nless_le order.trans)
  next
    case (lim f)
    with assms show ?case thm assms(1)
      by (metis le_oLimitI nle_le oLimit_leI)
  qed
  have "F (oLimit f) = oLimit (\<lambda>n. F (f n))" for f
  proof (cases "\<forall>n. f n < oLimit f")
    case True
    then have \<section>: "oLimit (\<lambda>n. f (make_mono f n)) = oLimit f"
      by (simp add: oLimit_make_mono_eq)
    have "\<And>n. \<exists>m. F (f n) \<le> F (f (make_mono f m))"
      by (metis True mono less_oLimitD linorder_not_less oLimit_make_mono_eq ordinal_linear)
    then show ?thesis
      by (metis True \<section> oLimit_eqI lim strict_mono_f_make_mono)
  next
    case False
    then show ?thesis
      by (metis le_oLimit less_oLimitE linorder_not_le mono nle_le)
  qed
  with mono show ?thesis
    by (simp add: continuous.intro)
qed


subsection \<open>Normal functions\<close>

locale normal = continuous +
  assumes strict: "strict_mono F"

lemma (in normal) mono: "mono F"
  by (rule mono)

lemma (in normal) continuous: "continuous F"
  by (rule continuous.intro, rule cont)

lemma (in normal) monoD: "x \<le> y \<Longrightarrow> F x \<le> F y"
  by (rule monoD)

lemma (in normal) strict_monoD: "x < y \<Longrightarrow> F x < F y"
  by (erule strict_monoD[OF strict])

lemma (in normal) cancel_eq: "(F x = F y) = (x = y)"
  by (rule strict_mono_cancel_eq[OF strict])

lemma (in normal) cancel_less: "(F x < F y) = (x < y)"
  by (rule strict_mono_cancel_less[OF strict])

lemma (in normal) cancel_le: "(F x \<le> F y) = (x \<le> y)"
  by (rule strict_mono_cancel_le[OF strict])

lemma (in normal) oLimit: "F (oLimit f) = oLimit (\<lambda>n. F (f n))"
  by (rule cont)

lemma (in normal) increasing: "x \<le> F x"
proof (induction x rule: oLimit_induct)
  case zero
  then show ?case
    by simp
next
  case (suc x)
  then show ?case
    by (simp add: normal.strict_monoD normal_axioms oSuc_leI order.strict_trans1)
next
  case (lim f)
  then show ?case
    by (metis cont le_oLimitI oLimit_leI)
qed

lemma normalI:
  assumes lim: "\<And>f. strict_mono f \<Longrightarrow> F (oLimit f) = oLimit (\<lambda>n. F (f n))"
  assumes suc: "\<And>x. F x < F (oSuc x)"
  shows "normal F"
proof -
  have mono: "x \<le> y \<Longrightarrow> F x \<le> F y" for x y
    using continuousI assms
    by (metis continuous.monoD linorder_not_less ordinal_linear)
  then have "OrdinalInduct.strict_mono F"
    by (metis OrdinalInduct.strict_monoI leD oSuc_leI order_less_le suc)
  then show ?thesis
    by (meson continuousI leD lim nle_le normal.intro normal_axioms.intro suc)
qed

lemma normal_range_le:
  assumes nml: "normal F" "normal G" and "range G \<subseteq> range F"
  shows "F x \<le> G x"
proof (induction x rule: oLimit_induct)
  case zero
  with assms show ?case
    by (metis image_iff normal.monoD ordinal_0_le range_subsetD)
next
  case (suc x)
  then have "G (oSuc x) \<in> range F"
    using assms(3) by blast
  then show ?case
    by (smt (verit, ccfv_SIG) nml dual_order.trans leD le_oSucE less_oSuc normal.cancel_le ordinal_linear rangeE suc)
next
  case (lim f)
  then show ?case
    by (metis nml le_oLimitI normal.oLimit oLimit_leI)
qed

lemma normal_range_eq:
  "\<lbrakk>normal F; normal G; range F = range G\<rbrakk> \<Longrightarrow> F = G"
  by (force simp add: normal_range_le intro: order_antisym)

end
