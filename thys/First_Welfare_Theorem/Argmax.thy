
section \<open>Arg Min and Arg Max\<close>

text \<open>
Taken from Lattices-Big.thy from the Isabelle-devel.
Once the new Isabelle release comes most contents of this file (except the last defs/proofs)
can be deleted and replaced by the library.

Title:      HOL/Lattices-Big.thy
    Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel
                with contributions by Jeremy Avigad \<close>


theory Argmax
  imports
    "HOL-Analysis.Analysis"
begin


subsection \<open>Arg Min\<close>

definition is_arg_min :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
"is_arg_min f P x = (P x \<and> \<not>(\<exists>y. P y \<and> f y < f x))"

definition arg_min :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a" where
"arg_min f P = (SOME x. is_arg_min f P x)"

abbreviation arg_min_on :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> 'a set \<Rightarrow> 'a" where
"arg_min_on f S \<equiv> arg_min f (\<lambda>x. x \<in> S)"

syntax
  "_arg_min" :: "('a \<Rightarrow> 'b) \<Rightarrow> pttrn \<Rightarrow> bool \<Rightarrow> 'a"
    ("(3ARG'_MIN _ _./ _)" [0, 0, 10] 10)
translations
  "ARG_MIN f x. P" \<rightleftharpoons> "CONST arg_min f (\<lambda>x. P)"

lemma is_arg_min_linorder: fixes f :: "'a \<Rightarrow> 'b :: linorder"
shows "is_arg_min f P x = (P x \<and> (\<forall>y. P y \<longrightarrow> f x \<le> f y))"
by(auto simp add: is_arg_min_def)

lemma arg_minI:
  "\<lbrakk> P x;
    \<And>y. P y \<Longrightarrow> \<not> f y < f x;
    \<And>x. \<lbrakk> P x; \<forall>y. P y \<longrightarrow> \<not> f y < f x \<rbrakk> \<Longrightarrow> Q x \<rbrakk>
  \<Longrightarrow> Q (arg_min f P)"
apply (simp add: arg_min_def is_arg_min_def)
apply (rule someI2_ex)
 apply blast
apply blast
done

lemma arg_min_equality:
  "\<lbrakk> P k; \<And>x. P x \<Longrightarrow> f k \<le> f x \<rbrakk> \<Longrightarrow> f (arg_min f P) = f k"
  for f :: "_ \<Rightarrow> 'a::order"
apply (rule arg_minI)
  apply assumption
 apply (simp add: less_le_not_le)
by (metis le_less)

lemma wf_linord_ex_has_least:
  "\<lbrakk> wf r; \<forall>x y. (x, y) \<in> r\<^sup>+ \<longleftrightarrow> (y, x) \<notin> r\<^sup>*; P k \<rbrakk>
   \<Longrightarrow> \<exists>x. P x \<and> (\<forall>y. P y \<longrightarrow> (m x, m y) \<in> r\<^sup>*)"
apply (drule wf_trancl [THEN wf_eq_minimal [THEN iffD1]])
apply (drule_tac x = "m ` Collect P" in spec)
by force

lemma ex_has_least_nat: "P k \<Longrightarrow> \<exists>x. P x \<and> (\<forall>y. P y \<longrightarrow> m x \<le> m y)"
  for m :: "'a \<Rightarrow> nat"
apply (simp only: pred_nat_trancl_eq_le [symmetric])
apply (rule wf_pred_nat [THEN wf_linord_ex_has_least])
 apply (simp add: less_eq linorder_not_le pred_nat_trancl_eq_le)
by assumption

lemma arg_min_nat_lemma:
  "P k \<Longrightarrow> P(arg_min m P) \<and> (\<forall>y. P y \<longrightarrow> m (arg_min m P) \<le> m y)"
  for m :: "'a \<Rightarrow> nat"
apply (simp add: arg_min_def is_arg_min_linorder)
apply (rule someI_ex)
apply (erule ex_has_least_nat)
done

lemmas arg_min_natI = arg_min_nat_lemma [THEN conjunct1]

lemma is_arg_min_arg_min_nat: fixes m :: "'a \<Rightarrow> nat"
shows "P x \<Longrightarrow> is_arg_min m P (arg_min m P)"
by (metis arg_min_nat_lemma is_arg_min_linorder)

lemma arg_min_nat_le: "P x \<Longrightarrow> m (arg_min m P) \<le> m x"
  for m :: "'a \<Rightarrow> nat"
by (rule arg_min_nat_lemma [THEN conjunct2, THEN spec, THEN mp])

lemma ex_min_if_finite:
  "\<lbrakk> finite S; S \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>m\<in>S. \<not>(\<exists>x\<in>S. x < (m::'a::order))"
by(induction rule: finite.induct) (auto intro: order.strict_trans)

lemma ex_is_arg_min_if_finite: fixes f :: "'a \<Rightarrow> 'b :: order"
shows "\<lbrakk> finite S; S \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>x. is_arg_min f (\<lambda>x. x : S) x"
unfolding is_arg_min_def
using ex_min_if_finite[of "f ` S"]
by auto

lemma arg_min_SOME_Min:
  "finite S \<Longrightarrow> arg_min_on f S = (SOME y. y \<in> S \<and> f y = Min(f ` S))"
unfolding arg_min_def is_arg_min_linorder
apply(rule arg_cong[where f = Eps])
apply (auto simp: fun_eq_iff intro: Min_eqI[symmetric])
done

lemma arg_min_if_finite: fixes f :: "'a \<Rightarrow> 'b :: order"
assumes "finite S" "S \<noteq> {}"
shows  "arg_min_on f S \<in> S" and "\<not>(\<exists>x\<in>S. f x < f (arg_min_on f S))"
using ex_is_arg_min_if_finite[OF assms, of f]
unfolding arg_min_def is_arg_min_def
by(auto dest!: someI_ex)

lemma arg_min_inj_eq: fixes f :: "'a \<Rightarrow> 'b :: order"
shows "\<lbrakk> inj_on f {x. P x}; P a; \<forall>y. P y \<longrightarrow> f a \<le> f y \<rbrakk> \<Longrightarrow> arg_min f P = a"
apply(simp add: arg_min_def is_arg_min_def)
apply(rule someI2[of _ a])
 apply (simp add: less_le_not_le)
by (metis inj_on_eq_iff less_le mem_Collect_eq)


subsection \<open>Arg Max\<close>

definition is_arg_max :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
"is_arg_max f P x = (P x \<and> \<not>(\<exists>y. P y \<and> f y > f x))"

definition arg_max :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a" where
"arg_max f P = (SOME x. is_arg_max f P x)"

abbreviation arg_max_on :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> 'a set \<Rightarrow> 'a" where
"arg_max_on f S \<equiv> arg_max f (\<lambda>x. x \<in> S)"

syntax
  "_arg_max" :: "('a \<Rightarrow> 'b) \<Rightarrow> pttrn \<Rightarrow> bool \<Rightarrow> 'a"
    ("(3ARG'_MAX _ _./ _)" [0, 0, 10] 10)
translations
  "ARG_MAX f x. P" \<rightleftharpoons> "CONST arg_max f (\<lambda>x. P)"

lemma is_arg_max_linorder: fixes f :: "'a \<Rightarrow> 'b :: linorder"
shows "is_arg_max f P x = (P x \<and> (\<forall>y. P y \<longrightarrow> f x \<ge> f y))"
by(auto simp add: is_arg_max_def)

lemma arg_maxI:
  "P x \<Longrightarrow>
    (\<And>y. P y \<Longrightarrow> \<not> f y > f x) \<Longrightarrow>
    (\<And>x. P x \<Longrightarrow> \<forall>y. P y \<longrightarrow> \<not> f y > f x \<Longrightarrow> Q x) \<Longrightarrow>
    Q (arg_max f P)"
apply (simp add: arg_max_def is_arg_max_def)
apply (rule someI2_ex)
 apply blast
apply blast
done

lemma arg_max_equality:
  "\<lbrakk> P k; \<And>x. P x \<Longrightarrow> f x \<le> f k \<rbrakk> \<Longrightarrow> f (arg_max f P) = f k"
  for f :: "_ \<Rightarrow> 'a::order"
apply (rule arg_maxI [where f = f])
  apply assumption
 apply (simp add: less_le_not_le)
by (metis le_less)

lemma ex_has_greatest_nat_lemma:
  "P k \<Longrightarrow> \<forall>x. P x \<longrightarrow> (\<exists>y. P y \<and> \<not> f y \<le> f x) \<Longrightarrow> \<exists>y. P y \<and> \<not> f y < f k + n"
  for f :: "'a \<Rightarrow> nat"
by (induct n) (force simp: le_Suc_eq)+

lemma ex_has_greatest_nat:
  "P k \<Longrightarrow> \<forall>y. P y \<longrightarrow> f y < b \<Longrightarrow> \<exists>x. P x \<and> (\<forall>y. P y \<longrightarrow> f y \<le> f x)"
  for f :: "'a \<Rightarrow> nat"
apply (rule ccontr)
apply (cut_tac P = P and n = "b - f k" in ex_has_greatest_nat_lemma)
  apply (subgoal_tac [3] "f k \<le> b")
   apply auto
done

lemma arg_max_nat_lemma:
  "\<lbrakk> P k;  \<forall>y. P y \<longrightarrow> f y < b \<rbrakk>
  \<Longrightarrow> P (arg_max f P) \<and> (\<forall>y. P y \<longrightarrow> f y \<le> f (arg_max f P))"
  for f :: "'a \<Rightarrow> nat"
apply (simp add: arg_max_def is_arg_max_linorder)
apply (rule someI_ex)
apply (erule (1) ex_has_greatest_nat)
done

lemmas arg_max_natI = arg_max_nat_lemma [THEN conjunct1]

lemma arg_max_nat_le: "P x \<Longrightarrow> \<forall>y. P y \<longrightarrow> f y < b \<Longrightarrow> f x \<le> f (arg_max f P)"
  for f :: "'a \<Rightarrow> nat"
  by (blast dest: arg_max_nat_lemma [THEN conjunct2, THEN spec, of P])


(* License: LGPL *)
subsection \<open> Definitions and Lemmas by Julian Parsert \<close>


text \<open> definition of argmax and argmin returing a set. \<close>

definition arg_min_set :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where
    "arg_min_set f S = {x. is_arg_min f (\<lambda>x. x\<in>S) x}"

definition arg_max_set :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where
    "arg_max_set f S = {x. is_arg_max f (\<lambda>x. x\<in>S) x}"


text \<open> Useful lemmas for @{term "arg_max_set"} and @{term "arg_min_set"}. \<close>

lemma no_better_in_s:
  assumes "x \<in> arg_max_set f S"
  shows "\<nexists>y. y \<in> S \<and> (f y) > (f x)"
  by (metis arg_max_set_def assms is_arg_max_def mem_Collect_eq)

lemma argmax_sol_in_s:
  assumes "x \<in> arg_max_set f S"
  shows "x \<in> S"
  by (metis CollectD arg_max_set_def assms is_arg_max_def)

lemma leq_all_in_sol:
  fixes f :: "'a \<Rightarrow> ('b :: preorder)"
  assumes "x \<in> arg_max_set f S"
  shows "\<forall>y \<in> S. f y \<ge> f x \<longrightarrow> y \<in> arg_max_set f S"
  using assms le_less_trans by (auto simp: arg_max_set_def is_arg_max_def)

lemma all_leq:
  fixes f :: "'a \<Rightarrow> ('b :: linorder)"
  assumes "x \<in> arg_max_set f S"
  shows "\<forall>y \<in> S. f x \<ge> f y"
  by (meson assms leI no_better_in_s)

lemma all_in_argmax_equal:
  fixes f :: "'a \<Rightarrow> ('b :: linorder)"
  assumes "x \<in> arg_max_set f S"
  shows "\<forall>y \<in> arg_max_set f S. f x = f y"
    by (meson all_leq argmax_sol_in_s assms le_less no_better_in_s)

end
