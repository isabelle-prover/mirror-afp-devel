\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>E-Unification Examples\<close>
theory E_Unification_Examples
  imports
    Main
    ML_Unification_HOL_Setup
    Unify_Assumption_Tactic
    Unify_Fact_Tactic
    Unify_Resolve_Tactics
begin

paragraph \<open>Summary\<close>
text \<open>Sample applications of e-unifiers, methods, etc. introduced in this session.\<close>

experiment
begin

subsection \<open>Using The Simplifier For Unification.\<close>

inductive_set even :: "nat set" where
zero: "0 \<in> even" |
step: "n \<in> even \<Longrightarrow> Suc (Suc n) \<in> even"

text \<open>Premises of the form @{term "SIMPS_TO_UNIF lhs rhs"} are solved by
@{ML_structure Simplifier_Unification}. It first normalises @{term lhs} and then unifies the
normalisation with @{term rhs}. See also @{theory ML_Unification.ML_Unification_HOL_Setup}.\<close>

lemma [uhint prio = Prio.LOW]: "n \<noteq> 0 \<Longrightarrow> PROP SIMPS_TO_UNIF (n - 1) m \<Longrightarrow> n \<equiv> Suc m"
  unfolding SIMPS_TO_UNIF_eq by linarith

text \<open>By default, below unification methods use
@{ML Standard_Mixed_Unification.first_higherp_decomp_comb_higher_unify}, which is a combination of
various practical unification algorithms.\<close>

schematic_goal "(\<And>x. x + 4 = n) \<Longrightarrow> Suc ?x = n"
  by uassm

lemma "6 \<in> even"
  apply (urule step)
  apply (urule step)
  apply (urule step)
  apply (urule zero)
  done

lemma "(220 + (80 - 2 * 2)) \<in> even"
  apply (urule step)
  apply (urule (rr) step)
  apply (urule zero)
  done

lemma
  assumes "[a,b,c] = [c,b,a]"
  shows "[a] @ [b,c] = [c,b,a]"
  using assms by uassm

lemma "x \<in> ({z, y, x} \<union> S) \<inter> {x}"
  by (ufact TrueI)

schematic_goal "(x + (y :: nat))^2 \<le> x^2 + 2*x*y + y^2 + 4 * y + x - y"
  supply power2_sum[simp]
  by (ufact TrueI)

lemma
  assumes "\<And>s. P (Suc (Suc 0)) (s(x := (1 :: nat), x := 1 + 1 * 4 - 3))"
  shows "P 2 (s(x := 2))"
  by (ufact assms)

subsection \<open>Providing Canonical Solutions With Unification Hints\<close>

lemma sub_self_eq_zero [uhint]: "(n :: nat) - n \<equiv> 0" by simp

schematic_goal "n - ?m = (0 :: nat)"
  by (ufact refl)

text \<open>The following example shows a non-trivial interplay of the simplifier and unification hints:
Using just unification, the hint @{thm sub_self_eq_zero} is not applicable in the following example
since @{term 0} cannot be unified with @{term "length []"}.
However, the simplifier can rewrite @{term "length []"} to @{term 0} and the hint can then be applied.\<close>

(*uncomment to see the trace*)
(* declare [[ML_map_context \<open>Logger.set_log_levels Logger.root Logger.TRACE\<close>]] *)

schematic_goal "n - ?m = length []"
  by (ufact refl)

text \<open>There are also two ways to solve this using only unification hints:
\<^enum> We allow the recursive use of unification hints when unifying @{thm sub_self_eq_zero} and our goal
and register @{term "length [] = 0"} as an additional hint.
\<^enum> We use an alternative for @{thm sub_self_eq_zero} that makes the recursive use of unification
hints explicit and register @{term "length [] = 0"} as an additional hint.\<close>

lemma length_nil_eq [uhint]: "length [] = 0" by simp

text \<open>Solution 1: we can use @{attribute rec_uhint} for recursive usages of hints.
Warning: recursive hint applications easily loop.\<close>

schematic_goal "n - ?m = length []"
  supply [[ucombine del: \<open>(Standard_Unification_Combine.default_metadata \<^binding>\<open>simp_unif\<close>)\<close>]]
  (*doesn't work*)
  \<comment> \<open>by (ufact refl)\<close>
  supply sub_self_eq_zero[uhint del, rec_uhint]
  by (ufact refl)

text \<open>Solution 2: make the recursion explicit in the hint.\<close>

lemma [uhint]: "k \<equiv> 0 \<Longrightarrow> (n :: nat) \<equiv> m \<Longrightarrow> n - m \<equiv> k" by simp

schematic_goal "n - ?m = length []"
  supply [[ucombine del: \<open>(Standard_Unification_Combine.default_metadata \<^binding>\<open>simp_unif\<close>)\<close>]]
  by (ufact refl)

subsection \<open>Strenghten Unification With Unification Hints\<close>

lemma
  assumes [uhint]: "n = m"
  shows "n - m = (0 :: nat)"
  by (ufact refl)

lemma
  assumes "x = y"
  shows "y = x"
  supply eq_commute[uhint]
  by (ufact assms)


paragraph \<open>Unfolding definitions.\<close>

definition "mysuc n = Suc n"

lemma
  assumes "\<And>m. Suc n > mysuc m"
  shows "mysuc n > Suc 3"
  supply mysuc_def[uhint]
  by (ufact assms)


paragraph \<open>Discharging meta impliciations with object-level implications\<close>

lemma [uhint]:
  "Trueprop A \<equiv> A' \<Longrightarrow> Trueprop B \<equiv> B' \<Longrightarrow> Trueprop (A \<longrightarrow> B) \<equiv> (PROP A' \<Longrightarrow> PROP B')"
  using atomize_imp[symmetric] by simp

lemma
  assumes "A \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> D"
  shows "A \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> D"
  using assms by ufact

lemma
  assumes "A \<longrightarrow> ((B \<longrightarrow> C) \<longrightarrow> D) \<longrightarrow> E"
  shows "A \<Longrightarrow> ((B \<Longrightarrow> C) \<Longrightarrow> D) \<Longrightarrow> E"
  using assms by ufact

subsection \<open>Better Control Over Meta Variable Instantiations\<close>

text \<open>Consider the following type-inference problem.\<close>
schematic_goal
  assumes app_typeI: "\<And>f x.  (\<And>x. ArgT x \<Longrightarrow> DomT x (f x)) \<Longrightarrow> ArgT x \<Longrightarrow> DomT x (f x)"
  and f_type: "\<And>x. ArgT x \<Longrightarrow> DomT x (f x)"
  and x_type: "ArgT x"
  shows "?T (f x)"
  apply (urule app_typeI) \<comment>\<open>compare with the following application, creating an (unintuitive) higher-order instantiation\<close>
  (* apply (rule app_typeI) *)
  oops

end

end
