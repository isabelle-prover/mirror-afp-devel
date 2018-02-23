(* License: LGPL *)
(*
Author: Julian Parsert <julian.parsert@gmail.com>
Author: Cezary Kaliszyk
*)


section \<open> Utility Functions \<close>

text \<open> Utility functions and results involving them. \<close>

theory Utility_Functions
  imports
    Preferences
    "HOL-Analysis.Analysis"
    Syntax
begin


subsection "Ordinal utility functions"

text \<open> Ordinal utility function locale \<close>

locale ordinal_utility =
  fixes carrier :: "'a set"
  fixes relation :: "'a relation"
  fixes u :: "'a \<Rightarrow> real"
  assumes util_def[iff]: "x \<in> carrier \<Longrightarrow> y \<in> carrier \<Longrightarrow> x \<succeq>[relation] y \<longleftrightarrow> u x \<ge> u y"
  assumes not_outside: "x \<succeq>[relation] y \<Longrightarrow> x \<in> carrier"
    and "x \<succeq>[relation] y \<Longrightarrow> y \<in> carrier"
begin

lemma util_def_conf: "x \<in> carrier \<Longrightarrow> y \<in> carrier \<Longrightarrow> u x \<ge> u y \<longleftrightarrow> x \<succeq>[relation] y"
  using util_def by blast


text \<open> Utility function implies totality of relation \<close>
lemma util_imp_total: "total_on carrier relation"
proof
  fix x and y
  assume x_inc: "x \<in> carrier" and y_inc : "y \<in> carrier"
  have fst : "u x \<ge> u y \<or> u y \<ge> u x"
    using util_def by auto
  then show  "x \<succeq>[relation] y \<or> y \<succeq>[relation] x"
    by (simp add: x_inc y_inc)
qed

lemma x_y_in_carrier: "x \<succeq>[relation] y \<Longrightarrow> x \<in> carrier \<and> y \<in> carrier"
  by (meson ordinal_utility_axioms ordinal_utility_def)

text \<open> Utility function implies transitivity of relation. \<close>

lemma util_imp_trans: "trans relation"
proof (rule transI)
  fix x and y and z
  assume x_y: "x \<succeq>[relation] y"
  assume y_z: "y \<succeq>[relation] z"
  have x_ge_y: "x \<succeq>[relation] y"
    using x_y by auto
  then have x_y: "u x \<ge> u y"
    by (meson x_y_in_carrier ordinal_utility_axioms util_def x_y)
  have "u y \<ge> u z"
    by (meson y_z ordinal_utility_axioms ordinal_utility_def)
  have "x \<in> carrier"
    using x_y_in_carrier[of x y] x_ge_y  by simp
  then have "u x \<ge> u z"
    using \<open>u z \<le> u y\<close> order_trans x_y by blast
  hence "x \<succeq>[relation] z"
    by (meson \<open>x \<in> carrier\<close> ordinal_utility_axioms ordinal_utility_def y_z)
  then show "x \<succeq>[relation] z" .
qed

lemma util_imp_refl: "refl_on carrier relation"
  by (smt mem_Sigma_iff ordinal_utility_axioms ordinal_utility_def refl_on_def subrelI)

text \<open> This utility function definition is ordinal.
        Hence they are only unique up to a monotone transformation. \<close>

lemma ordinality_of_utility_function :
  fixes f :: "real \<Rightarrow> real"
  assumes monot: "monotone ((>)) ((>)) f"
  shows "(f \<circ> u) x > (f \<circ> u) y \<longleftrightarrow> u x > u y"
proof -
  let ?func = "(\<lambda>x. f(u x))"
  have "\<forall>m n . u m \<ge> u n \<longleftrightarrow> ?func m \<ge> ?func n"
    by (metis le_less monot monotone_def not_less)
  hence "u x > u y \<longleftrightarrow> ?func x > ?func y"
    using not_le by blast
  thus ?thesis  by auto
qed


corollary utility_prefs_corresp :
  fixes f :: "real \<Rightarrow> real"
  assumes monotonicity : "monotone ((>)) ((>)) f"
  shows "\<forall>x\<in>carrier. \<forall>y\<in>carrier. (x,y) \<in> relation \<longleftrightarrow> (f \<circ> u) x \<ge> (f \<circ> u) y"
  by (meson monotonicity not_less ordinality_of_utility_function util_def_conf)

end

text \<open> A utility function implies a rational preference relation.
      Hence a utility function contains exactly the same amount of information as a RPR \<close>

sublocale ordinal_utility \<subseteq> rational_preference carrier relation
proof
  fix x and y
  assume xy: "x \<succeq>[relation] y"
  then show "x \<in> carrier"
    and "y \<in> carrier"
    using not_outside by (simp)
      (meson xy refl_onD2 util_imp_refl)
next
  show "preorder_on carrier relation"
  proof-
    have "trans relation" using util_imp_trans by auto
    then have "preorder_on carrier relation"
      by (simp add: preorder_on_def util_imp_refl)
    then show ?thesis .
  qed
next
  show "total_on carrier relation"
    by (simp add: util_imp_total)
qed


text \<open> Given a finite carrier set. We can guarantee that given a rational preference
       relation, there must also exist a utility function representing this relation.
       Construction of witness roughly follows from@{cite "tadelis2013game"}\<close>

theorem fnt_carrier_exists_util_fun:
  assumes "finite carrier"
  assumes "rational_preference carrier relation"
  shows "\<exists>u. ordinal_utility carrier relation u"
proof-
  define f where
    f: "f = (\<lambda>x. card (no_better_than x carrier relation))"
  have "ordinal_utility carrier relation f"
  proof
    fix x y
    assume x_c: "x \<in> carrier"
    assume y_c: "y \<in> carrier"
    show "x \<succeq>[relation] y \<longleftrightarrow> (real (f y) \<le> real (f x))"
    proof
      assume asm: "x \<succeq>[relation] y"
      define yn where
        yn: "yn = no_better_than y carrier relation"
      define xn where
        xn: "xn = no_better_than x carrier relation"
      then have "yn \<subseteq> xn"
        by (simp add: asm yn assms(2) rational_preference.no_better_subset_pref)
      then have "card yn \<le> card xn"
        by (simp add: x_c y_c asm assms rational_preference.card_leq_pref xn yn)
      then show "(real (f y) \<le> real (f x))"
        using  f xn yn of_nat_le_iff by blast
    next
      assume "real (f y) \<le> real (f x)"
      then show "x \<succeq>[relation] y"
        using assms f rational_preference.card_leq_pref x_c y_c by fastforce
    qed
  next
    fix x y
    assume asm: "x \<succeq>[relation] y"
    show "x \<in> carrier"
      by (meson asm assms(2) preference.not_outside rational_preference.axioms(1))
    show "y \<in> carrier"
      by (meson asm assms(2) preference_def rational_preference_def)
  qed
  then show ?thesis
    by blast
qed


subsection \<open> Utility function on  Euclidean Space \<close>

locale eucl_ordinal_utility = ordinal_utility carrier relation u
  for carrier :: "('a::euclidean_space) set"
  and relation :: "'a relation"
  and u :: "'a \<Rightarrow> real"

sublocale eucl_ordinal_utility \<subseteq> rational_preference carrier relation
  using rational_preference_axioms by blast

lemma ord_eucl_utility_imp_rpr: "eucl_ordinal_utility s rel u \<longrightarrow> real_vector_rpr s rel"
  by (metis eucl_ordinal_utility_def ordinal_utility.util_imp_refl
      ordinal_utility.util_imp_total ordinal_utility.util_imp_trans preference_def
      preorder_on_def rational_preference.intro rational_preference_axioms.intro
      real_vector_rpr_def refl_on_domain)

context eucl_ordinal_utility
begin

text \<open> Local non-satiation on utility functions \<close>

lemma lns_pref_lns_util [iff]:
  "local_nonsatiation carrier relation \<longleftrightarrow>
  (\<forall>x\<in>carrier. \<forall>e > 0. \<exists>y\<in>carrier.
  norm (y - x) \<le> e \<and> u y > u x)" (is "_ \<longleftrightarrow> ?alt")
proof
  assume lns: "local_nonsatiation carrier relation"
  have "\<forall>a b. a \<succ> b \<longrightarrow> u a > u b"
    by (metis less_eq_real_def util_def x_y_in_carrier)
  then show "?alt"
    by (meson lns local_nonsatiation_def)
next
  assume lns: "?alt"
  show "local_nonsatiation carrier relation"
  proof(rule lns_normI)
    fix x and e::real
    assume x_in: "x \<in> carrier"
    assume e: "e > 0"
    have "\<forall>x \<in> carrier. \<forall>e>0. \<exists>y\<in>carrier. norm (y - x) \<le> e \<and> y \<succ> x"
      by (meson less_eq_real_def linorder_not_less lns util_def)
    have "\<exists>y\<in>carrier. norm (y - x) \<le> e \<and> u y > u x"
      using e x_in lns by blast
    then show "\<exists>y\<in>carrier. norm (y - x) \<le> e \<and> y \<succ> x"
      by (meson compl not_less util_def x_in)
  qed
qed

end

end
