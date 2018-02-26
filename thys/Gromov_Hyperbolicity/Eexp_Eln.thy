(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)


theory Eexp_Eln
  imports Library_Complements
begin

section \<open>The exponential on extended real numbers.\<close>

text \<open>To define the distance on the Gromov completion of hyperbolic spaces, we need to use
the exponential on extended real numbers. We can not use the symbol \verb+exp+, as this symbol
is already used in Banach algebras, so we use \verb+eexp+ instead. We prove its basic
properties (together with properties of the logarithm) here. We also use it to define the square
root on ennreal.\<close>

function eexp::"ereal \<Rightarrow> ennreal" where
"eexp (ereal r) = ennreal (exp r)"
| "eexp (\<infinity>) = \<infinity>"
| "eexp (-\<infinity>) = 0"
by (auto intro: ereal_cases)
termination by standard (rule wf_empty)

lemma eexp_0 [simp]:
  "eexp 0 = 1"
by (auto simp add: zero_ereal_def one_ennreal_def)

function eln::"ennreal \<Rightarrow> ereal" where
"eln (ennreal r) = (if r \<le> 0 then -\<infinity> else ereal (ln r))"
| "eln (\<infinity>) = \<infinity>"
by (auto intro: ennreal_cases, metis ennreal_eq_0_iff, simp add: ennreal_neg)
termination by standard (rule wf_empty)

lemma eln_simps [simp]:
  "eln 0 = -\<infinity>"
  "eln 1 = 0"
  "eln top = \<infinity>"
apply (simp only: eln.simps ennreal_0[symmetric], simp)
apply (simp only: eln.simps ennreal_1[symmetric], simp)
using eln.simps(2) by auto

lemma eln_real_pos:
  assumes "r > 0"
  shows "eln (ennreal r) = ereal (ln r)"
using eln.simps assms by auto

lemma eln_eexp [simp]:
  "eln (eexp x) = x"
apply (cases x) using eln.simps by auto

lemma eexp_eln [simp]:
  "eexp (eln x) = x"
apply (cases x) using eln.simps by auto

lemma eexp_strict_mono:
  "strict_mono eexp"
proof -
  have "eexp x < eexp y" if "x < y" for x y
    apply (cases x, cases y)
    using that apply (auto simp add: ennreal_less_iff)
    by (cases y, auto)
  then show ?thesis unfolding strict_mono_def by auto
qed

lemma eexp_mono:
  "mono eexp"
using eexp_strict_mono by (simp add: strict_mono_mono)

lemma eexp_strict_mono2 [mono_intros]:
  assumes "x < y"
  shows "eexp x < eexp y"
using eexp_strict_mono assms unfolding strict_mono_def by auto

lemma eexp_mono2 [mono_intros]:
  assumes "x \<le> y"
  shows "eexp x \<le> eexp y"
using eexp_mono assms unfolding mono_def by auto

lemma eexp_le1 [simp]:
  "eexp x \<le> 1 \<longleftrightarrow> x \<le> 0"
by (metis eexp_0 eexp_mono2 eexp_strict_mono eq_iff le_cases strict_mono_eq)

lemma eexp_ge1 [simp]:
  "eexp x \<ge> 1 \<longleftrightarrow> x \<ge> 0"
by (metis eexp_0 eexp_mono2 eexp_strict_mono eq_iff le_cases strict_mono_eq)

lemma eln_strict_mono:
  "strict_mono eln"
by (metis eexp_eln strict_monoI eexp_strict_mono strict_mono_less)

lemma eln_mono:
  "mono eln"
using eln_strict_mono by (simp add: strict_mono_mono)

lemma eln_strict_mono2 [mono_intros]:
  assumes "x < y"
  shows "eln x < eln y"
using eln_strict_mono assms unfolding strict_mono_def by auto

lemma eln_mono2 [mono_intros]:
  assumes "x \<le> y"
  shows "eln x \<le> eln y"
using eln_mono assms unfolding mono_def by auto

lemma eln_le0 [simp]:
  "eln x \<le> 0 \<longleftrightarrow> x \<le> 1"
by (metis eexp_eln eexp_le1)

lemma eln_ge0 [simp]:
  "eln x \<ge> 0 \<longleftrightarrow> x \<ge> 1"
by (metis eexp_eln eexp_ge1)

lemma bij_eexp:
  "bij eexp"
by (auto intro!: bij_betw_byWitness[of _ eln])

lemma bij_eln:
  "bij eln"
by (auto intro!: bij_betw_byWitness[of _ eexp])

lemma eexp_continuous:
  "continuous_on UNIV eexp"
apply (rule continuous_onI_mono)
using eexp_mono unfolding mono_def by (auto simp add: bij_eexp bij_is_surj)

lemma eexp_tendsto [tendsto_intros]:
  assumes "((\<lambda>n. u n) \<longlongrightarrow> l) F"
  shows "((\<lambda>n. eexp(u n)) \<longlongrightarrow> eexp l) F"
using eexp_continuous assms by (metis UNIV_I continuous_on tendsto_compose)

lemma eln_continuous:
  "continuous_on UNIV eln"
apply (rule continuous_onI_mono)
using eln_mono unfolding mono_def by (auto simp add: bij_eln bij_is_surj)

lemma eln_tendsto [tendsto_intros]:
  assumes "((\<lambda>n. u n) \<longlongrightarrow> l) F"
  shows "((\<lambda>n. eln(u n)) \<longlongrightarrow> eln l) F"
using eln_continuous assms by (metis UNIV_I continuous_on tendsto_compose)

lemma eexp_special_values [simp]:
  "eexp x = 0 \<longleftrightarrow> x = -\<infinity>"
  "eexp x = 1 \<longleftrightarrow> x = 0"
  "eexp x = \<infinity> \<longleftrightarrow> x = \<infinity>"
  "eexp x = top \<longleftrightarrow> x = \<infinity>"
by auto (metis eln_eexp eln_simps)+

lemma eln_special_values [simp]:
  "eln x = -\<infinity> \<longleftrightarrow> x = 0"
  "eln x = 0 \<longleftrightarrow> x = 1"
  "eln x = \<infinity> \<longleftrightarrow> x = \<infinity>"
apply auto
apply (metis eexp.simps eexp_eln eexp_0)+
by (metis eexp.simps(2) eexp_eln infinity_ennreal_def)

lemma eexp_add_mult:
  assumes "\<not>((a = \<infinity> \<and> b = -\<infinity>) \<or> (a = -\<infinity> \<and> b = \<infinity>))"
  shows "eexp(a+b) = eexp a * eexp b"
apply (cases a, cases b)
using assms by (auto simp add: ennreal_mult'' exp_add ennreal_top_eq_mult_iff)

lemma eln_mult_add:
  assumes "\<not>((a = \<infinity> \<and> b = 0) \<or> (a = 0 \<and> b = \<infinity>))"
  shows "eln(a * b) = eln a + eln b"
by (smt assms eexp.simps(2) eexp.simps(3) eexp_add_mult eexp_eln eln_eexp)

text \<open>We can also define the square root on ennreal using the above exponential.\<close>

definition esqrt::"ennreal \<Rightarrow> ennreal"
  where "esqrt x = eexp(eln x/2)"

lemma esqrt_square [simp]:
  "(esqrt x) * (esqrt x) = x"
proof -
  have "y/2 + y/2 = y" for y::ereal
    by (cases y, auto)
  then show ?thesis
    unfolding esqrt_def by (subst eexp_add_mult[symmetric], auto)
qed

lemma esqrt_simps [simp]:
  "esqrt 0 = 0"
  "esqrt 1 = 1"
  "esqrt \<infinity> = \<infinity>"
  "esqrt top = top"
unfolding esqrt_def by auto

lemma esqrt_mult:
  "esqrt(a * b) = esqrt a * esqrt b"
proof -
  have [simp]: "z/ereal 2 = -\<infinity> \<longleftrightarrow> z = -\<infinity>" for z
    by (auto simp add: ereal_divide_eq)

  consider "a = 0" | "b = 0" | "a>0 \<and> b > 0"
    using zero_less_iff_neq_zero by auto
  then show ?thesis
    apply (cases, auto)
    apply (cases a, cases b, auto simp add: ennreal_mult_top ennreal_top_mult)
    unfolding esqrt_def apply (subst eexp_add_mult[symmetric], auto)
    apply (subst eln_mult_add, auto)
    done
qed

lemma esqrt_square2 [simp]:
  "esqrt(x * x) = x"
  unfolding esqrt_mult by auto

lemma esqrt_bij:
  "bij esqrt"
by (rule bij_betw_byWitness[of _ "\<lambda>x. x * x"], auto)

lemma esqrt_strict_mono:
  "strict_mono esqrt"
  unfolding esqrt_def
  apply (rule strict_mono_compose[OF eexp_strict_mono])
  apply (rule strict_mono_compose[OF _ eln_strict_mono])
  by (auto simp add: ereal_less_divide_pos ereal_mult_divide strict_mono_def)

lemma esqrt_mono:
  "mono esqrt"
using esqrt_strict_mono by (simp add: strict_mono_mono)

lemma esqrt_mono2 [mono_intros]:
  assumes "x \<le> y"
  shows "esqrt x \<le> esqrt y"
using esqrt_mono assms unfolding mono_def by auto

lemma esqrt_continuous:
  "continuous_on UNIV esqrt"
apply (rule continuous_onI_mono)
using esqrt_mono unfolding mono_def by (auto simp add: esqrt_bij bij_is_surj)

lemma esqrt_tendsto [tendsto_intros]:
  assumes "((\<lambda>n. u n) \<longlongrightarrow> l) F"
  shows "((\<lambda>n. esqrt(u n)) \<longlongrightarrow> esqrt l) F"
using esqrt_continuous assms by (metis UNIV_I continuous_on tendsto_compose)

lemma esqrt_ennreal_ennreal_sqrt [simp]:
  assumes "t \<ge> (0::real)"
  shows "esqrt (ennreal t) = ennreal (sqrt t)"
proof -
  have "ennreal t = ennreal (sqrt t) * ennreal(sqrt t)"
    apply (subst ennreal_mult[symmetric]) using assms by auto
  then show ?thesis
    by auto
qed

lemma ennreal_sqrt2:
  "ennreal (sqrt 2) = esqrt 2"
using esqrt_ennreal_ennreal_sqrt[of 2] by auto

lemma esqrt_4 [simp]:
  "esqrt 4 = 2"
by (metis ennreal_numeral esqrt_ennreal_ennreal_sqrt real_sqrt_four zero_le_numeral)

lemma esqrt_le [simp]:
  "esqrt x \<le> esqrt y \<longleftrightarrow> x \<le> y"
proof
  assume "esqrt x \<le> esqrt y"
  then have "esqrt x * esqrt x \<le> esqrt y * esqrt y"
    by (intro mult_mono, auto)
  then show "x \<le> y" by auto
qed (auto intro: mono_intros)

end (*of theory Eexp_Eln*)
