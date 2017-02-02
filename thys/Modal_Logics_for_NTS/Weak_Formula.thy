theory Weak_Formula
imports
  Weak_Transition_System
  Formula
begin

section \<open>Weak Formulas\<close>

subsection \<open>Weak formulas and weak preformulas\<close>

context weak_nominal_ts  -- \<open>We use~@{term \<tau>} in our definition of weak formulas.\<close>
begin

inductive weak_formula :: "('idx,'pred::fs,'act::bn) formula \<Rightarrow> bool"
where
  wf_Conj: "finite (supp xset) \<Longrightarrow> (\<And>x. x \<in> set_bset xset \<Longrightarrow> weak_formula x) \<Longrightarrow> weak_formula (Conj xset)"
| wf_Not: "weak_formula x \<Longrightarrow> weak_formula (Not x)"
| wf_Act: "weak_formula x \<Longrightarrow> weak_formula (Act \<alpha> x)"
| wf_Pred: "weak_formula x \<Longrightarrow> weak_formula (Act \<tau> (Conj (binsert (Pred \<phi>) (bsingleton x))))"

lemma finite_supp_wf_Pred [simp]: "finite (supp (binsert (Pred \<phi>) (bsingleton x)))"
proof -
  have "supp (bsingleton x) \<subseteq> supp x"
    by (simp add: eqvtI supp_fun_app_eqvt)
  moreover have "eqvt binsert"
    by (simp add: eqvtI)
  ultimately have "supp (binsert (Pred \<phi>) (bsingleton x)) \<subseteq> supp \<phi> \<union> supp x"
    using supp_fun_app supp_fun_app_eqvt by fastforce
  then show ?thesis
    by (metis finite_UnI finite_supp rev_finite_subset)
qed

text \<open>@{const weak_formula} is equivariant.\<close>

lemma weak_formula_eqvt: "weak_formula x \<Longrightarrow> weak_formula (p \<bullet> x)"
proof (induct rule: weak_formula.induct)
  case (wf_Conj xset) then show ?case
    by simp (metis (no_types, lifting) imageE permute_finite permute_set_eq_image set_bset_eqvt supp_eqvt weak_formula.wf_Conj)
qed (auto simp add: wf_Not wf_Act wf_Pred tau_eqvt)

end

end
