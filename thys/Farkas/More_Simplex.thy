(* Authors: R. Bottesch, M. W. Haslbeck, R. Thiemann *)

section \<open>Preliminaries\<close>

text \<open>We derive some basic properties of constraints and linear polynomials
  that are needed later on, but were not present in the simplex formalization.\<close>

theory More_Simplex
  imports Simplex.Simplex
begin

lemma poly_eq_iff: "p = q \<longleftrightarrow> (\<forall> v. coeff p v = coeff q v)"
  by transfer auto

lemma poly_eqI:
  assumes "\<And>v. coeff p v = coeff q v"
  shows "p = q"
  using assms poly_eq_iff by simp

lemma coeff_lp_monom [simp]:
  shows "coeff (lp_monom c v) v' = (if v = v' then c else 0)"
  using coeff.rep_eq lp_monom.rep_eq by auto

lemma coeff_zero_simp [simp]:
  "coeff 0 v = 0"
  using zero_coeff_zero by blast

lemma coeff_sum_list:
  assumes "distinct xs"
  shows "coeff (\<Sum>x\<leftarrow>xs. f x *R lp_monom 1 x) v = (if v \<in> set xs then f v else 0)"
  using assms by (induction xs) auto

lemma linear_poly_sum:
  "p \<lbrace> v \<rbrace> = (\<Sum>x\<in>vars p. coeff p x *R v x)"
  by transfer simp

lemma ALP_vars_list_distinct: 
  "distinct (Abstract_Linear_Poly.vars_list p)"
  by transfer (use distinct_sorted_list_of_set in auto)

lemma valuate_lp_monom_1[simp]: "((lp_monom 1 x) \<lbrace>v\<rbrace>) = v x" 
  by transfer simp 

lemma all_valuate_zero: assumes "\<And>(v::'a::lrv valuation). p \<lbrace>v\<rbrace> = 0"
  shows "p = 0"
  using all_val assms by blast

lemma valuate_sum: "((\<Sum>x\<in>A. f x) \<lbrace> v \<rbrace>) = (\<Sum>x\<in>A. ((f x) \<lbrace> v \<rbrace>))" 
  by (induct A rule: infinite_finite_induct, auto simp: valuate_zero valuate_add)

lemma linear_poly_eqI: assumes "\<And>(v::'a::lrv valuation). (p \<lbrace>v\<rbrace>) = (q \<lbrace>v\<rbrace>)"
  shows "p = q"
  using assms 
proof -
  have "(p - q) \<lbrace> v \<rbrace> = 0" for v::"'a::lrv valuation"
    using assms by (subst valuate_minus) auto
  then have "p - q = 0"
    by (intro all_valuate_zero) auto
  then show ?thesis
    by simp
qed

lemma QDelta_0_0: "QDelta 0 0 = 0" by code_simp
lemma qdsnd_0: "qdsnd 0 = 0" by code_simp
lemma qdfst_0: "qdfst 0 = 0" by code_simp

lemma vars_lp_monom: "vars (lp_monom r x) = (if r = 0 then {} else {x})" 
  by (transfer, auto)

lemma monom_poly_assemble:
  assumes "is_monom p"
  shows "monom_coeff p *R lp_monom 1 (monom_var p) = p"
  by (simp add: assms linear_poly_eqI monom_valuate valuate_scaleRat)

lemma uminus_less_lrv[simp]: fixes a b :: "'a :: lrv"
  shows "- a < - b \<longleftrightarrow> b < a" 
proof -
  have "(- a < - b) = (-1 *R a < -1 *R b)" by simp
  also have "\<dots> \<longleftrightarrow> (b < a)" 
    using scaleRat_less2[of _ _ "-1"] scaleRat_less2[of "-1 *R a" "-1 *R b" "-1"] by auto 
  finally show ?thesis .
qed


lemma normalized_tableau_preprocess': "\<triangle> (Tableau (preprocess' cs (start_fresh_variable cs)))"
proof -
  let ?s = "start_fresh_variable cs"
  show ?thesis
    using lvars_distinct[of cs ?s]
    using lvars_tableau_ge_start[of cs ?s]
    using vars_tableau_vars_constraints[of cs ?s]
    using start_fresh_variable_fresh[of cs] 
    unfolding normalized_tableau_def Let_def
    by (smt disjoint_iff_not_equal inf.absorb_iff2 inf.strict_order_iff rhs_no_zero_tableau_start set_mp)
qed

end