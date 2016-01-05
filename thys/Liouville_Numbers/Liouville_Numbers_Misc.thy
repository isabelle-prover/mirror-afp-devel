(* 
  File:    Liouville_Numbers_Misc.thy
  Author:  Manuel Eberl <eberlm@in.tum.de>

*)

section \<open>Liouville Numbers\<close>
subsection \<open>Preliminary lemmas\<close>
theory Liouville_Numbers_Misc
imports
  Complex_Main
  "$AFP/Algebraic_Numbers/Algebraic_Numbers"
  "~~/src/HOL/Library/Poly_Deriv"
begin

lemma of_int_pos: "x > 0 \<Longrightarrow> of_int x > (0::'a::{linordered_idom})"
  by simp

lemma of_int_nonneg: "x \<ge> 0 \<Longrightarrow> of_int x \<ge> (0::'a::{linordered_idom})"
  by simp

text \<open>
  We will require these inequalities on factorials to show properties of the standard 
  construction later.
\<close>
lemma fact_ge_self: "fact n \<ge> n"
  by (cases "n = 0") (simp_all add: dvd_imp_le dvd_fact)

lemma fact_ineq: "n \<ge> 1 \<Longrightarrow> fact n + k \<le> fact (n + k)"
proof (induction k)
  case (Suc k)
  from Suc have "fact n + Suc k \<le> fact (n + k) + 1" by simp
  also from Suc have "\<dots> \<le> fact (n + Suc k)" by simp
  finally show ?case .
qed simp_all

lemma Ints_setsum:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> \<int>"
  shows   "setsum f A \<in> \<int>"
  by (cases "finite A", insert assms, induction A rule: finite_induct)
     (auto intro!: Ints_add)

lemma suminf_split_initial_segment':
  "summable (f :: nat \<Rightarrow> 'a::real_normed_vector) \<Longrightarrow> 
       suminf f = (\<Sum>n. f (n + k + 1)) + setsum f {..k}"
  by (subst suminf_split_initial_segment[of _ "Suc k"], assumption, subst lessThan_Suc_atMost) 
     simp_all

lemma Rats_eq_int_div_int': "(\<rat> :: real set) = {of_int p / of_int q |p q. q > 0}"
proof safe
  fix x :: real assume "x \<in> \<rat>"
  then obtain p q where pq: "x = of_int p / of_int q" "q \<noteq> 0" 
    by (subst (asm) Rats_eq_int_div_int) (auto simp: real_of_int_def)
  show "\<exists>p q. x = real_of_int p / real_of_int q \<and> 0 < q"
  proof (cases "q > 0")
    case False
    show ?thesis by (rule exI[of _ "-p"], rule exI[of _ "-q"]) (insert False pq, auto)
  qed (insert pq, force)
qed auto

lemma Rats_cases':
  assumes "(x :: real) \<in> \<rat>"
  obtains p q where "q > 0" "x = of_int p / of_int q"
  using assms by (subst (asm) Rats_eq_int_div_int') auto

lemma rpoly_smult: "rpoly (Polynomial.smult s p) x = s * rpoly p x"
  unfolding eval_poly_def by auto

lemma continuous_on_poly [continuous_intros]: 
  fixes p :: "'a :: {real_normed_field} poly"
  assumes "continuous_on A f"
  shows   "continuous_on A (\<lambda>x. poly p (f x))"
proof -
  have "continuous_on A (\<lambda>x. (\<Sum>i\<le>degree p. (f x) ^ i * coeff p i))" 
    by (intro continuous_intros assms)
  also have "\<dots> = (\<lambda>x. poly p (f x))" by (intro ext) (simp add: poly_as_setsum)
  finally show ?thesis .
qed

text \<open>
  The following variant of the Mean Value Theorem for polynomials does not require us
  to know which of the two boundaries is lower.
\<close>
lemma poly_MVT':
  assumes "{min a b..max a b} \<subseteq> A"
  shows   "\<exists>x\<in>A. poly p b - poly p a = (b - a) * poly (pderiv p) (x::real)"
proof (cases a b rule: linorder_cases)
  case less
  from poly_MVT[OF less, of p] guess x by (elim exE conjE)
  thus ?thesis by (intro bexI[of _ x]) (auto intro!: subsetD[OF assms])

next
  case greater
  from poly_MVT[OF greater, of p] guess x by (elim exE conjE)
  thus ?thesis by (intro bexI[of _ x]) (auto simp: algebra_simps intro!: subsetD[OF assms])
qed (insert assms, auto)


text \<open>
  Algebraic numbers can be defined in two equivalent ways: all real numbers that are 
  roots of rational polynomials or of integer polynomials. The Algebraic-Numbers AFP entry 
  uses the rational definition, but we need the integer definition.

  The equivalence is obvious since any rational polynomial can be multiplied with the 
  LCM of its coefficients, yielding an integer polynomial with the same roots.
\<close>
lemma algebraicE:
  assumes "algebraic (x :: real)"
  obtains p where "\<And>n. coeff p n \<in> \<int>" "p \<noteq> 0" "poly p x = 0"
proof -
  from assms obtain p where p: "p \<noteq> 0" "rpoly p x = 0"
    unfolding algebraic_def by auto
  def cs \<equiv> "map quotient_of (coeffs p)"
  def d \<equiv> "Lcm (set (map snd cs))"
  def p' \<equiv> "real_of_rat_poly (smult (of_int d) p)"

  have "\<forall>n. coeff p' n \<in> \<int>"
  proof
    fix n :: nat
    show "coeff p' n \<in> \<int>"
    proof (cases "n \<le> degree p")
      case True
      def c \<equiv> "coeff p n"
      def a \<equiv> "fst (quotient_of c)" and b \<equiv> "snd (quotient_of c)"
      have b_pos: "b > 0" unfolding b_def using quotient_of_nonzero by simp
      have "coeff p' n = of_rat (of_int d * c)" by (simp add: p'_def c_def)
      also have "c = of_int a / of_int b" unfolding a_def b_def by (simp add: quotient_of_div)
      also have "of_int d * \<dots> = of_int a * (of_int d / of_int b)" by simp
      also from True p have "b dvd d" unfolding b_def d_def c_def cs_def
        by (intro dvd_Lcm_int) (auto simp: o_def coeffs_def simp del: upt_Suc)
      with b_pos have "rat_of_int d / of_int b \<in> \<int>" 
        by (auto elim!: dvdE simp: algebra_simps)
      from Ints_mult[OF _ this] have "of_int a * (rat_of_int d / of_int b) \<in> \<int>" by simp
      hence "real_of_rat (of_int a * (rat_of_int d / of_int b)) \<in> \<int>"
        by (elim Ints_cases) simp
      finally show "coeff p' n \<in> \<int>" .
    qed (auto simp: p'_def not_le coeff_eq_0)
  qed
  moreover have "set (map snd cs) \<subseteq> {0<..}"
    unfolding cs_def using quotient_of_nonzero by (auto simp: coeffs_def simp del: upt_Suc) 
  hence "d \<noteq> 0" unfolding d_def by (induction cs) simp_all
  with p have "p' \<noteq> 0" by (simp add: p'_def)
  moreover from p have "poly p' x = 0" by (simp add: p'_def poly_real_of_rat_poly)
  ultimately show ?thesis using that[of p'] by blast
qed

text \<open>
  The following inequality gives a lower bound for the absolute value of an 
  integer polynomial at a rational point that is not a root.
\<close>
lemma int_poly_rat_no_root_ge: 
  fixes p :: "real poly" and a b :: int
  assumes "\<And>n. coeff p n \<in> \<int>"
  assumes "b > 0" "poly p (a / b) \<noteq> 0"
  defines "n \<equiv> degree p"
  shows   "abs (poly p (a / b)) \<ge> 1 / real b ^ n"
proof -
  let ?S = "(\<Sum>i\<le>n. coeff p i * real a ^ i * (real b ^ (n - i)))"
  from \<open>b > 0\<close> have eq: "?S = real b ^ n * poly p (a / b)"
    by (simp add: poly_as_setsum power_divide mult_ac n_def setsum_right_distrib power_diff)
  have "?S \<in> \<int>" by (intro Ints_setsum Ints_mult assms Ints_power) simp_all
  moreover from assms have "?S \<noteq> 0" by (subst eq) auto
  ultimately have "abs ?S \<ge> 1" by (elim Ints_cases) simp
  with eq \<open>b > 0\<close> show ?thesis by (simp add: field_simps abs_mult)
qed

end
