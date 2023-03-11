(*  Title:       Countable Ordinals

    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Fixed-points\<close>

theory OrdinalFix
  imports OrdinalInverse
begin

primrec iter :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)"
  where
    "iter 0       F x = x"
  | "iter (Suc n) F x = F (iter n F x)"

definition
  oFix :: "(ordinal \<Rightarrow> ordinal) \<Rightarrow> ordinal \<Rightarrow> ordinal" where
  "oFix F a = oLimit (\<lambda>n. iter n F a)"

lemma oFix_fixed:
  assumes "continuous F" "a \<le> F a"
  shows "F (oFix F a) = oFix F a"
proof -
  have "a \<le> oLimit (\<lambda>n. F (iter n F a))"
    by (metis OrdinalFix.iter.simps(1) \<open>a \<le> F a\<close> le_oLimitI)
  then have "iter k F a \<le> oLimit (\<lambda>n. F (iter n F a))" for k
    by (induction k) auto
  then have "oLimit (\<lambda>n. F (iter n F a)) = oLimit (\<lambda>n. iter n F a)"
    by (metis (no_types, lifting) OrdinalFix.iter.simps(2) le_oLimit nle_le oLimit_leI)
  then show ?thesis
    by (simp add: assms(1) continuousD oFix_def)
qed

lemma oFix_least:
  assumes "mono F" "F x = x" "a \<le> x" shows "oFix F a \<le> x"
proof -
  have "iter n F a \<le> x" for n
  proof (induction n)
    case (Suc n)
    with assms monotoneD show ?case by fastforce 
  qed (use assms in auto)
  then show ?thesis
    by (simp add: oFix_def oLimit_leI)
qed

lemma mono_oFix: 
  assumes "mono F"  shows "mono (oFix F)"
proof -
  have "iter n F x \<le> iter n F y" if "x \<le> y" for n x y
    using that assms
    by (induction n) (auto simp: monoD)
  then show ?thesis
    by (metis le_oLimitI monoI oFix_def oLimit_leI)
qed

lemma less_oFixD: "\<lbrakk>x < oFix F a; mono F; F x = x\<rbrakk> \<Longrightarrow> x < a"
  by (meson linorder_not_le oFix_least)

lemma less_oFixI: "a < F a \<Longrightarrow> a < oFix F a"
  by (metis OrdinalFix.iter.simps leD le_oLimit oFix_def order_neq_le_trans)

lemma le_oFix: "a \<le> oFix F a"
  by (metis OrdinalFix.iter.simps(1) le_oLimit oFix_def)

lemma le_oFix1: "F a \<le> oFix F a"
  by (metis OrdinalFix.iter.simps le_oLimit oFix_def)

lemma less_oFix_0D:
  assumes "x < oFix F 0" "mono F" shows "x < F x"
proof -
  have "x < iter n F 0 \<Longrightarrow> x < F x" for n
  proof (induction n)
    case 0 then show ?case by auto
  next
    case (Suc n)
    with \<open>mono F\<close> show ?case
      using monotoneD order.strict_trans2 by fastforce
  qed
  then show ?thesis
    using assms(1) less_oLimitD oFix_def by fastforce
qed

lemma zero_less_oFix_eq: "(0 < oFix F 0) = (0 < F 0)"
proof -
  have "F 0 \<le> 0 \<Longrightarrow> iter n F 0 \<le> 0" for n
    by (induction n) auto
  then show ?thesis
    using less_oFixI oFix_def by fastforce
qed

lemma oFix_eq_self: 
  assumes "F a = a" shows "oFix F a = a"
proof -
  have "iter n F a = a" for n
    by (induction n) (auto simp: assms)
  then show ?thesis
    by (simp add: oFix_def)
qed


subsection \<open>Derivatives of ordinal functions\<close>

text "The derivative of F enumerates all the fixed-points of F"

definition
  oDeriv :: "(ordinal \<Rightarrow> ordinal) \<Rightarrow> ordinal \<Rightarrow> ordinal" where
  "oDeriv F = ordinal_rec (oFix F 0) (\<lambda>p x. oFix F (oSuc x))"

lemma oDeriv_0 [simp]:
  "oDeriv F 0 = oFix F 0"
  by (simp add: oDeriv_def)

lemma oDeriv_oSuc [simp]:
  "oDeriv F (oSuc x) = oFix F (oSuc (oDeriv F x))"
  by (simp add: oDeriv_def)

lemma oDeriv_oLimit [simp]:
  "oDeriv F (oLimit f) = oLimit (\<lambda>n. oDeriv F (f n))"
  by (metis dual_order.trans le_oFix less_oSuc oDeriv_def order_le_less ordinal_rec_oLimit)

lemma oDeriv_fixed:
  assumes "normal F" shows "F (oDeriv F n) = oDeriv F n"
proof (induction n rule: oLimit_induct)
  case zero
  then show ?case
    by (simp add: assms normal.continuous oFix_fixed)
next
  case (suc x)
  then show ?case
    by (simp add: assms normal.continuous normal.increasing oFix_fixed)
next
  case (lim f)
  then show ?case
    by (simp add: assms continuousD normal.continuous)
qed

lemma oDeriv_fixedD: "\<lbrakk>oDeriv F x = x; normal F\<rbrakk> \<Longrightarrow> F x = x"
  by (metis oDeriv_fixed)

lemma normal_oDeriv: "normal (oDeriv F)"
  by (metis le_oFix normal_ordinal_rec oDeriv_def oSuc_le_eq_less)

lemma oDeriv_increasing:
  assumes "continuous F" shows "F n \<le> oDeriv F n"
proof (induction n rule: oLimit_induct)
  case zero
  then show ?case
    by (simp add: le_oFix1)
next
  case (suc x)
  with continuous.monoD [OF assms] show ?case
    by (metis dual_order.trans le_oFix1 normal.increasing normal_oDeriv oDeriv_oSuc oSuc_le_oSuc)
next
  case (lim f)
  then show ?case
    by (metis assms continuousD le_oLimitI oDeriv_oLimit oLimit_leI)
qed

lemma oDeriv_total:
  assumes "normal F" "F x = x" shows "\<exists>n. x = oDeriv F n"
proof -
  have "\<exists>n. oDeriv F n \<le> x \<and> x < oDeriv F (oSuc n)"
    by (metis assms normal.mono normal.oInv_ex normal_oDeriv oDeriv_0 oFix_least ordinal_0_le)
  then show ?thesis
    by (metis assms leD normal.mono oDeriv_oSuc oFix_least oSuc_leI order_neq_le_trans)
qed

lemma range_oDeriv: "normal F \<Longrightarrow> range (oDeriv F) = {x. F x = x}"
  by (auto intro: oDeriv_fixed dest: oDeriv_total)

end

