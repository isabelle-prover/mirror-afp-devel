(* 
  File:    Liouville_Numbers_Misc.thy
  Author:  Manuel Eberl <eberlm@in.tum.de>

*)

section \<open>Liouville Numbers\<close>
subsection \<open>Preliminary lemmas\<close>
theory Liouville_Numbers_Misc
imports
  Complex_Main
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
    by (subst (asm) Rats_eq_int_div_int) auto
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


text \<open>
  Algebraic numbers can be defined in two equivalent ways: all real numbers that are 
  roots of rational polynomials or of integer polynomials. The Algebraic-Numbers AFP entry 
  uses the rational definition, but we need the integer definition.

  The equivalence is obvious since any rational polynomial can be multiplied with the 
  LCM of its coefficients, yielding an integer polynomial with the same roots.
\<close>
subsection \<open>Algebraic numbers\<close>

definition algebraic :: "'a :: field_char_0 \<Rightarrow> bool" where
  "algebraic x \<longleftrightarrow> (\<exists>p. (\<forall>i. coeff p i \<in> \<int>) \<and> p \<noteq> 0 \<and> poly p x = 0)"

lemma algebraicI:
  assumes "\<And>i. coeff p i \<in> \<int>" "p \<noteq> 0" "poly p x = 0"
  shows   "algebraic x"
  using assms unfolding algebraic_def by blast
  
lemma algebraicE:
  assumes "algebraic x"
  obtains p where "\<And>i. coeff p i \<in> \<int>" "p \<noteq> 0" "poly p x = 0"
  using assms unfolding algebraic_def by blast

lemma quotient_of_denom_pos': "snd (quotient_of x) > 0"
  using quotient_of_denom_pos[OF surjective_pairing] .
  
lemma of_int_div_in_Ints: 
  "b dvd a \<Longrightarrow> of_int a div of_int b \<in> (\<int> :: 'a :: ring_div set)"
proof (cases "of_int b = (0 :: 'a)")
  assume "b dvd a" "of_int b \<noteq> (0::'a)"
  then obtain c where "a = b * c" by (elim dvdE)
  with \<open>of_int b \<noteq> (0::'a)\<close> show ?thesis by simp
qed auto

lemma of_int_divide_in_Ints: 
  "b dvd a \<Longrightarrow> of_int a / of_int b \<in> (\<int> :: 'a :: field set)"
proof (cases "of_int b = (0 :: 'a)")
  assume "b dvd a" "of_int b \<noteq> (0::'a)"
  then obtain c where "a = b * c" by (elim dvdE)
  with \<open>of_int b \<noteq> (0::'a)\<close> show ?thesis by simp
qed auto

lemma algebraic_altdef:
  fixes p :: "'a :: field_char_0 poly"
  shows "algebraic x \<longleftrightarrow> (\<exists>p. (\<forall>i. coeff p i \<in> \<rat>) \<and> p \<noteq> 0 \<and> poly p x = 0)"
proof safe
  fix p assume rat: "\<forall>i. coeff p i \<in> \<rat>" and root: "poly p x = 0" and nz: "p \<noteq> 0"
  def cs \<equiv> "coeffs p"
  from rat have "\<forall>c\<in>range (coeff p). \<exists>c'. c = of_rat c'" unfolding Rats_def by blast
  then obtain f where f: "\<And>i. coeff p i = of_rat (f (coeff p i))" 
    by (subst (asm) bchoice_iff) blast
  def cs' \<equiv> "map (quotient_of \<circ> f) (coeffs p)"
  def d \<equiv> "Lcm (set (map snd cs'))"
  def p' \<equiv> "smult (of_int d) p"
  
  have "\<forall>n. coeff p' n \<in> \<int>"
  proof
    fix n :: nat
    show "coeff p' n \<in> \<int>"
    proof (cases "n \<le> degree p")
      case True
      def c \<equiv> "coeff p n"
      def a \<equiv> "fst (quotient_of (f (coeff p n)))" and b \<equiv> "snd (quotient_of (f (coeff p n)))"
      have b_pos: "b > 0" unfolding b_def using quotient_of_denom_pos' by simp
      have "coeff p' n = of_int d * coeff p n" by (simp add: p'_def)
      also have "coeff p n = of_rat (of_int a / of_int b)" unfolding a_def b_def
        by (subst quotient_of_div [of "f (coeff p n)", symmetric])
           (simp_all add: f [symmetric])
      also have "of_int d * \<dots> = of_rat (of_int (a*d) / of_int b)"
        by (simp add: of_rat_mult of_rat_divide)
      also from nz True have "b \<in> snd ` set cs'" unfolding cs'_def
        by (force simp: o_def b_def coeffs_def simp del: upt_Suc)
      hence "b dvd (a * d)" unfolding d_def by simp
      hence "of_int (a * d) / of_int b \<in> (\<int> :: rat set)"
        by (rule of_int_divide_in_Ints)
      hence "of_rat (of_int (a * d) / of_int b) \<in> \<int>" by (elim Ints_cases) auto
      finally show ?thesis .
    qed (auto simp: p'_def not_le coeff_eq_0)
  qed
  
  moreover have "set (map snd cs') \<subseteq> {0<..}"
    unfolding cs'_def using quotient_of_denom_pos' by (auto simp: coeffs_def simp del: upt_Suc) 
  hence "d \<noteq> 0" unfolding d_def by (induction cs') simp_all
  with nz have "p' \<noteq> 0" by (simp add: p'_def)
  moreover from root have "poly p' x = 0" by (simp add: p'_def)
  ultimately show "algebraic x" unfolding algebraic_def by blast
next

  assume "algebraic x"
  then obtain p where p: "\<And>i. coeff p i \<in> \<int>" "poly p x = 0" "p \<noteq> 0" 
    by (force simp: algebraic_def)
  moreover have "coeff p i \<in> \<int> \<Longrightarrow> coeff p i \<in> \<rat>" for i by (elim Ints_cases) simp
  ultimately show  "(\<exists>p. (\<forall>i. coeff p i \<in> \<rat>) \<and> p \<noteq> 0 \<and> poly p x = 0)" by auto
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
  shows   "abs (poly p (a / b)) \<ge> 1 / of_int b ^ n"
proof -
  let ?S = "(\<Sum>i\<le>n. coeff p i * of_int a ^ i * (of_int b ^ (n - i)))"
  from \<open>b > 0\<close> have eq: "?S = of_int b ^ n * poly p (a / b)"
    by (simp add: poly_altdef power_divide mult_ac n_def setsum_right_distrib power_diff)
  have "?S \<in> \<int>" by (intro Ints_setsum Ints_mult assms Ints_power) simp_all
  moreover from assms have "?S \<noteq> 0" by (subst eq) auto
  ultimately have "abs ?S \<ge> 1" by (elim Ints_cases) simp
  with eq \<open>b > 0\<close> show ?thesis by (simp add: field_simps abs_mult)
qed

end
