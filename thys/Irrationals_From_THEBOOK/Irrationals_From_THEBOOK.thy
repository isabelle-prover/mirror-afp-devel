section \<open>Some irrational numbers\<close>
text \<open>From Aigner and Ziegler, \emph{Proofs from THE BOOK} (Springer, 2018), Chapter 8, pp. 50--51.\<close>

theory Irrationals_From_THEBOOK imports "Stirling_Formula.Stirling_Formula"
   
begin

subsection \<open>Basic definitions and their consequences\<close>

definition hf where "hf \<equiv> \<lambda>n. \<lambda>x::real. (x^n * (1-x)^n) / fact n"

definition cf where "cf \<equiv> \<lambda>n i. if i < n then 0 else (n choose (i-n)) * (-1)^(i-n)"

text \<open>Mere knowledge that the coefficients are integers is not enough later on.\<close>
lemma hf_int_poly:
  fixes x::real
  shows "hf n = (\<lambda>x. (1 / fact n) * (\<Sum>i=0..2*n. real_of_int (cf n i) * x^i))"
proof 
  fix x
  have inj: "inj_on ((+)n) {..n}" 
    by (auto simp: inj_on_def)
  have [simp]: "((+)n) ` {..n} = {n..2*n}"
    using nat_le_iff_add by fastforce
  have "(x^n * (-x + 1)^n) = x ^ n * (\<Sum>k\<le>n. real (n choose k) * (- x) ^ k)"
    unfolding binomial_ring by simp
  also have "\<dots> = x ^ n * (\<Sum>k\<le>n. real_of_int ((n choose k) * (-1)^k) * x ^ k)"
    by (simp add: mult.assoc flip: power_minus)
  also have "\<dots> = (\<Sum>k\<le>n. real_of_int ((n choose k) * (-1)^k) * x ^ (n+k))"
    by (simp add: sum_distrib_left mult_ac power_add)
  also have "\<dots> = (\<Sum>i=n..2*n. real_of_int (cf n i) * x^i)"
    by (simp add: sum.reindex [OF inj, simplified] cf_def)
  finally have "hf n x = (1 / fact n) * (\<Sum>i = n..2 * n. real_of_int (cf n i) * x^i)"
    by (simp add: hf_def)
  moreover have "(\<Sum>i = 0..<n. real_of_int (cf n i) * x^i) = 0"
    by (simp add: cf_def)
  ultimately show "hf n x = (1 / fact n) * (\<Sum>i = 0..2 * n. real_of_int (cf n i) * x^i)"
    using sum.union_disjoint [of "{0..<n}" "{n..2*n}" "\<lambda>i. real_of_int (cf n i) * x^i"]
    by (simp add: ivl_disj_int_two(7) ivl_disj_un_two(7) mult_2)
qed

text \<open>Lemma (ii) in the text has strict inequalities, but that's more work and is less useful.\<close>
lemma 
  assumes "0 \<le> x" "x \<le> 1" 
  shows hf_nonneg: "0 \<le> hf n x" and hf_le_inverse_fact: "hf n x \<le> 1/fact n"
  using assms by (auto simp: hf_def divide_simps mult_le_one power_le_one)

lemma hf_differt [iff]: "hf n differentiable at x"
  unfolding hf_int_poly differentiable_def
  by (intro derivative_eq_intros exI | simp)+

lemma deriv_sum_int:
  "deriv (\<lambda>x. \<Sum>i=0..n. real_of_int (c i) * x^i) x 
       = (if n=0 then 0 else (\<Sum>i=0..n-1. of_int((i+1) * c(Suc i)) * x^i))"
  (is "deriv ?f x = (if n=0 then 0 else ?g)")
proof -
  have "(?f has_real_derivative ?g) (at x)" if "n > 0"
  proof -
    have "(\<Sum>i = 0..n. i * x ^ (i - Suc 0) * (c i))
        = (\<Sum>i = 1..n. (real (i-1) + 1) * of_int (c i) * x ^ (i-1))"
      using that by (auto simp: sum.atLeast_Suc_atMost intro!: sum.cong)
    also have "\<dots> = sum ((\<lambda>i. (real i + 1) * c (Suc i) * x^i) \<circ> (\<lambda>n. n-1)) 
                     {1..Suc (n-1)}"
      using that by simp
    also have "\<dots> = ?g"
      by (simp flip: sum.atLeast_atMost_pred_shift [where m=0])
    finally have \<section>: "(\<Sum>a = 0..n. a * x ^ (a - Suc 0) * (c a)) = ?g" .
    show ?thesis
      by (rule derivative_eq_intros \<section> | simp)+
  qed
  then show ?thesis
    by (force intro: DERIV_imp_deriv)
qed

text \<open>We calculate the coefficients of the $k$th derivative precisely.\<close>
lemma hf_deriv_int_poly:
  "(deriv^^k) (hf n) = (\<lambda>x. (1/fact n) * (\<Sum>i=0..2*n-k. of_int (int(\<Prod>{i<..i+k}) * cf n (i+k)) * x^i))"
proof (induction k)
  case 0
  show ?case 
    by (simp add: hf_int_poly)
next
  case (Suc k)
  define F where "F \<equiv> \<lambda>x. (\<Sum>i = 0..2*n - k. real_of_int (int(\<Prod>{i<..i+k}) * cf n (i+k)) * x^i)"
  have Fd: "F field_differentiable at x" for x
    unfolding field_differentiable_def F_def
    by (rule derivative_eq_intros exI | force)+
  have [simp]: "prod int {i<..Suc (i + k)} = (1 + int i) * prod int {Suc i<..Suc (i + k)}" for i
    by (metis Suc_le_mono atLeastSucAtMost_greaterThanAtMost le_add1 of_nat_Suc prod.head) 
  have "deriv (\<lambda>x. F x / fact n) x 
      = (\<Sum>i = 0..2 * n - Suc k. of_int (int(\<Prod>{i<..i+ Suc k}) * cf n (Suc (i+k))) * x^i) / fact n" for x
    unfolding deriv_cdivide_right [OF Fd]
    by (fastforce simp add: F_def deriv_sum_int cf_def simp flip: of_int_mult intro: sum.cong)
  then show ?case
    by (simp add: Suc F_def)
qed

lemma hf_deriv_0: "(deriv^^k) (hf n) 0 \<in> \<int>"
proof (cases "n \<le> k")
  case True
  then obtain j where "(fact k::real) = real_of_int j * fact n"
    by (metis fact_dvd dvd_def mult.commute of_int_fact of_int_mult) 
  moreover have "prod real {0<..k} = fact k"
    by (simp add: fact_prod atLeastSucAtMost_greaterThanAtMost)
  ultimately show ?thesis
    by (simp add: hf_deriv_int_poly dvd_def)
next
  case False
  then show ?thesis
    by (simp add: hf_deriv_int_poly cf_def)
qed

lemma deriv_hf_minus: "deriv (hf n) = (\<lambda>x. - deriv (hf n) (1-x))"
proof 
  fix x
  have "hf n = hf n \<circ> (\<lambda>x. (1-x))"
    by (simp add: fun_eq_iff hf_def mult.commute)
  then have "deriv (hf n) x = deriv (hf n \<circ> (\<lambda>x. (1-x))) x"
    by fastforce
  also have "\<dots> = deriv (hf n) (1-x) * deriv ((-) 1) x"
    by (intro real_derivative_chain) auto
  finally show "deriv (hf n) x = - deriv (hf n) (1-x)"
    by simp
qed

lemma deriv_n_hf_diffr [iff]: "(deriv^^k) (hf n) field_differentiable at x"
  unfolding field_differentiable_def hf_deriv_int_poly
  by (rule derivative_eq_intros exI | force)+

lemma deriv_n_hf_minus: "(deriv^^k) (hf n) = (\<lambda>x. (-1)^k * (deriv^^k) (hf n) (1-x))"
proof (induction k)
  case 0
  then show ?case
    by (simp add: fun_eq_iff hf_def)
next
  case (Suc k)
  have o: "(\<lambda>x. (deriv ^^ k) (hf n) (1-x)) = (deriv ^^ k) (hf n) \<circ> (-) 1"
    by auto
  show ?case
  proof
    fix x
    have [simp]: "((deriv^^k) (hf n) \<circ> (-) 1) field_differentiable at x"
      by (force intro: field_differentiable_compose)
    have "(deriv ^^ Suc k) (hf n) x = deriv (\<lambda>x. (-1) ^ k * (deriv ^^ k) (hf n) (1-x)) x"
      by simp (metis Suc)
    also have "\<dots> = (-1) ^ k * deriv (\<lambda>x. (deriv ^^ k) (hf n) (1-x)) x"
      using o by fastforce
    also have "\<dots> = (-1) ^ Suc k * (deriv ^^ Suc k) (hf n) (1-x)"
      by (subst o, subst deriv_chain, auto)
    finally show "(deriv ^^ Suc k) (hf n) x = (-1) ^ Suc k * (deriv ^^ Suc k) (hf n) (1-x)" .
  qed
qed

subsection \<open>Towards the main result\<close>

lemma hf_deriv_1: "(deriv^^k) (hf n) 1 \<in> \<int>"
  by (smt (verit, best) Ints_1 Ints_minus Ints_mult Ints_power deriv_n_hf_minus hf_deriv_0)

lemma hf_deriv_eq_0: "k > 2*n \<Longrightarrow> (deriv^^k) (hf n) = (\<lambda>x. 0)"
  by (force simp add: cf_def hf_deriv_int_poly)

text \<open>The case for positive integers\<close>
lemma exp_nat_irrational:
  assumes "s > 0" shows "exp (real_of_int s) \<notin> \<rat>"
proof
  assume "exp (real_of_int s) \<in> \<rat>"
  then obtain a b where ab: "a > 0" "b > 0" "coprime a b" and exp_s: "exp s = of_int a / of_int b"
    by (smt (verit) Rats_cases' divide_nonpos_pos exp_gt_zero of_int_0_less_iff)
  define n where "n \<equiv> nat (max (a^2) (3 * s^3))"
  then have ns3: "s^3 \<le> real n / 3"
    by linarith
  have "n > 0"
    using \<open>a > 0\<close> by (simp add: n_def max.strict_coboundedI1)
  then have "s ^ (2*n+1) \<le> s ^ (3*n)"
    using \<open>a > 0\<close> assms by (intro power_increasing) auto
  also have "\<dots> = real_of_int(s^3) ^ n"
    by (simp add: power_mult)
  also have "\<dots> \<le> (n / 3) ^ n"
    using assms ns3 by (simp add: power_mono)
  also have "\<dots> \<le> (n / exp 1) ^ n"
    using exp_le \<open>n > 0\<close> by (auto simp: divide_simps)
  finally have s_le: "s ^ (2*n+1) \<le> (n / exp 1) ^ n"
    by presburger 
  have a_less: "a < sqrt (2*pi*n)"
  proof -
    have "2*pi > 1"
      using pi_ge_two by linarith
    have "a \<le> sqrt n"
      using \<open>0 < n\<close> n_def of_nat_nat real_le_rsqrt by fastforce
    also have "\<dots> < sqrt (2*pi*n)"
      by (simp add: \<open>0 < n\<close> \<open>1 < 2 * pi\<close>)
    finally show ?thesis .
  qed
  have "sqrt (2*pi*n) * (n / exp 1) ^ n > a * s ^ (2*n+1)"
    using mult_strict_right_mono [OF a_less] mult_left_mono [OF s_le]
    by (smt (verit, best) s_le ab(1) assms of_int_1 of_int_le_iff of_int_mult zero_less_power)
  then have n: "fact n > a * s ^ (2*n+1)"
    using fact_bounds(1) by (smt (verit, best) \<open>0 < n\<close> of_int_fact of_int_less_iff)
  define F where "F \<equiv> \<lambda>x. \<Sum>i\<le>2*n. (-1)^i * s^(2*n-i) * (deriv^^i) (hf n) x"
  have Fder: "(F has_real_derivative -s * F x + s^(2*n+1) * hf n x) (at x)" for x
  proof -
    have *: "sum f {..n+n} = sum f {..<n+n}" if "f (n+n) = 0" for f::"nat \<Rightarrow> real"
      by (smt (verit, best) lessThan_Suc_atMost sum.lessThan_Suc that)
    have [simp]: "(deriv ((deriv ^^ (n+n)) (hf n)) x) = 0"
      using hf_deriv_eq_0 [where k= "Suc(n+n)"] by simp
    have \<section>: "(\<Sum>k\<le>n+n. (-1) ^ k * ((deriv ^^ Suc k) (hf n) x * of_int s ^ (n+n - k))) 
           + s * (\<Sum>j=0..n+n. (-1) ^ j * ((deriv ^^ j) (hf n) x * of_int s ^ (n+n - j))) 
           = s * (hf n x * of_int s ^ (n+n))" 
      using \<open>n>0\<close>
      apply (subst sum_Suc_reindex)
      apply (simp add: algebra_simps atLeast0AtMost)
      apply (force simp add: * mult.left_commute [of "of_int s"] minus_nat.diff_Suc sum_distrib_left 
              simp flip: sum.distrib intro: comm_monoid_add_class.sum.neutral split: nat.split_asm)
      done
    show ?thesis
      unfolding F_def 
      apply (rule derivative_eq_intros field_differentiable_derivI | simp)+
      using \<section> by (simp add: algebra_simps atLeast0AtMost eval_nat_numeral)
  qed
  have F01_Ints: "F 0 \<in> \<int>" "F 1 \<in> \<int>"
    by (simp_all add: F_def hf_deriv_0 hf_deriv_1 Ints_sum)
  define sF where "sF \<equiv> \<lambda>x. exp (of_int s * x) * F x"
  define sF' where "sF' \<equiv> \<lambda>x. of_int s ^ Suc(2*n) * (exp (of_int s * x) * hf n x)"
  have sF_der: "(sF has_real_derivative sF' x) (at x)" for x
    unfolding sF_def sF'_def
    by (rule refl Fder derivative_eq_intros | force simp: algebra_simps)+
  let ?N = "b * integral {0..1} sF'"
  have sF'_integral: "(sF' has_integral sF 1 - sF 0) {0..1}"
    by (smt (verit) fundamental_theorem_of_calculus has_real_derivative_iff_has_vector_derivative 
                    has_vector_derivative_at_within sF_der)
  then have "?N = a * F 1 - b * F 0"
    using \<open>b > 0\<close> by (simp add: integral_unique exp_s sF_def algebra_simps)
  also have "\<dots> \<in> \<int>"
    using hf_deriv_1 by (simp add: F01_Ints)
  finally have N_Ints: "?N \<in> \<int>" .
  have "sF' (1/2) > 0" and ge0: "\<And>x. x \<in> {0..1} \<Longrightarrow> 0 \<le> sF' x"
    using assms by (auto simp: sF'_def hf_def)
  moreover have "continuous_on {0..1} sF'"
    unfolding sF'_def hf_def by (intro continuous_intros) auto
  ultimately have False if "(sF' has_integral 0) {0..1}"
    using has_integral_0_cbox_imp_0 [of 0 1 sF' "1/2"] that by auto
  then have "integral {0..1} sF' > 0"
    by (metis ge0 has_integral_nonneg integral_unique order_le_less sF'_integral) 
  then have "0 < ?N"
    by (simp add: \<open>b > 0\<close>)
  have "integral {0..1} sF' = of_int s ^ Suc(2*n) * integral {0..1} (\<lambda>x. exp (s*x) * hf n x)"
    unfolding sF'_def by force 
  also have "\<dots> \<le> of_int s ^ Suc(2*n) * (exp s * (1 / fact n))"
  proof (rule mult_left_mono)
    have "integral {0..1} (\<lambda>x. exp (s*x) * hf n x) \<le> integral {0..1} (\<lambda>x::real. exp s * (1/fact n))"
    proof (intro mult_mono integral_le)
      show "(\<lambda>x. exp (s*x) * hf n x) integrable_on {0..1}"
        using \<open>0 < ?N\<close> not_integrable_integral sF'_def by fastforce
    qed (use assms hf_nonneg hf_le_inverse_fact in auto)
    also have "\<dots> = exp s * (1 / fact n)"
      by simp
    finally show "integral {0..1} (\<lambda>x. exp (s*x) * hf n x) \<le> exp s * (1 / fact n)" .
  qed (use assms in auto)
  finally have "?N \<le> b * of_int s ^ Suc(2*n) * exp s * (1 / fact n)"
    using \<open>b > 0\<close> by (simp add: sF'_def mult_ac divide_simps)
  also have "\<dots> < 1"
    using n apply (simp add: field_simps exp_s)
    by (metis of_int_fact of_int_less_iff of_int_mult of_int_power)
  finally show False
    using \<open>0 < ?N\<close> Ints_cases N_Ints by force
qed

theorem exp_irrational:
  fixes q::real assumes "q \<in> \<rat>" "q \<noteq> 0" shows "exp q \<notin> \<rat>"
proof 
  assume q: "exp q \<in> \<rat>"
  obtain s t where "s \<noteq> 0" "t > 0" "q = of_int s / of_int t"
    by (metis Rats_cases' assms div_0 of_int_0)
  then have "(exp q) ^ (nat t) = exp s"
    by (smt (verit, best) exp_divide_power_eq of_nat_nat zero_less_nat_eq)
  moreover have "exp q ^ (nat t) \<in> \<rat>"
    by (simp add: q)
  ultimately show False
    by (smt (verit, del_insts) Rats_inverse \<open>s \<noteq> 0\<close> exp_minus exp_nat_irrational of_int_of_nat)
qed

corollary ln_irrational: 
  fixes q::real assumes "q \<in> \<rat>" "q > 0"  "q \<noteq> 1" shows "ln q \<notin> \<rat>"
  using assms exp_irrational [of "ln q"] exp_ln_iff [of q] by force

end
