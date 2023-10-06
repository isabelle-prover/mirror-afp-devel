\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>E-Unification Examples\<close>
theory E_Unification_Examples
  imports
    Main
    ML_Unification_HOL_Setup
    Unify_Fact_Tactic
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

lemma [uhint where prio = Prio.LOW]: "n \<noteq> 0 \<Longrightarrow> PROP SIMPS_TO_UNIF (n - 1) m \<Longrightarrow> n \<equiv> Suc m"
  unfolding SIMPS_TO_UNIF_eq by linarith

text \<open>By default, below unification methods use
@{ML Standard_Mixed_Unification.first_higherp_first_comb_higher_unify}, which is a combination of
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
  apply (urule step)+
  apply (urule zero)
  done

lemma
  assumes "[a,b,c] = [c,b,a]"
  shows "[a] @ [b,c] = [c,b,a]"
  using assms by uassm

lemma "x \<in> ({z, y, x} \<union> S) \<inter> {x}"
  by (ufact TrueI)

lemma "(x + (y :: nat))^2 \<le> x^2 + 2*x*y + y^2 + 4 * y + x - y"
  supply power2_sum[simp]
  by (ufact TrueI)

lemma
  assumes "\<And>s. P (Suc (Suc 0)) (s(x := (1 :: nat), x := 1 + 1 * 4 - 3))"
  shows "P 2 (s(x := 2))"
  by (ufact assms[of s])

subsection \<open>Providing Canonical Solutions With Unification Hints\<close>

lemma [uhint]: "xs \<equiv> [] \<Longrightarrow> length xs \<equiv> 0" by simp

schematic_goal "length ?xs = 0"
  by (ufact refl)

lemma [uhint]: "(n :: nat) \<equiv> m \<Longrightarrow> n - m \<equiv> 0" by simp

schematic_goal "n - ?m = (0 :: nat)"
  by (ufact refl)

text \<open>The following fails because, by default, @{ML Standard_Unification_Hints.try_hints}
uses the higher-order pattern unifier to unify hints against a given disagreement pair, and
@{term 0} cannot be higher-order pattern unified with @{term "length []"}. The unification of the
hint requires the use of yet another hint, namely @{term "length xs = 0"} (cf. above).\<close>
schematic_goal "n - ?m = length []"
  \<comment> \<open>by (ufact refl)\<close>
  oops

text \<open>There are two ways to fix this:
\<^enum> We allow the recursive uses of unification hints when searching for suitable unification hints.
\<^enum> We use a different unification hint that the recursive use of hints explicit.\<close>

text \<open>Solution 1: recursive usages of hints. Warning: such recursive applications easily loop.\<close>
schematic_goal "n - ?m = length []"
  using [[uhint where concl_unifier = Standard_Mixed_Unification.first_higherp_first_comb_higher_unify]]
  by (ufact refl)

text \<open>Solution 2: make the recursion explicit in the hint.\<close>

lemma [uhint]: "k \<equiv> 0 \<Longrightarrow> (n :: nat) \<equiv> m \<Longrightarrow> n - m \<equiv> k" by simp

schematic_goal "n - ?m = length []"
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
