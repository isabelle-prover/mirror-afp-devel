subsection \<open>The Pentagonal Number Theorem\<close>
theory Pentagonal_Number_Theorem
imports
  Partition_Function
  Theta_Functions.Jacobi_Triple_Product
begin

subsubsection \<open>The analytic version\<close>

text \<open>
  The analytic version of the pentagonal number theorem states that:
  \[\phi(q) = (q; q)_\infty = f(-q, -q^2) = \theta(-\sqrt{q}, q\sqrt{q})\]
  where $f(a,b)$ denotes the Ramanujan theta function and $\theta(w,q)$ denotes the
  Jacobi theta function (both in terms of the nome).

  This is an easily corollary from the Jacobi triple product, which is already
  in the AFP.  
\<close>
theorem pentagonal_number_theorem_complex:
  fixes q :: complex
  assumes q: "norm q < 1"
  shows   "euler_phi q = ramanujan_theta (-q) (-(q\<^sup>2))"
proof -
  include qpochhammer_inf_notation
  have "ramanujan_theta (-q) (-(q\<^sup>2)) = (\<Prod>i<3. (q * q ^ i; q^3)\<^sub>\<infinity>)"
    by (subst ramanujan_theta_triple_product_complex)
       (use q in \<open>simp_all flip: power_Suc add: norm_power power_less_one_iff eval_nat_numeral\<close>)
  also have "\<dots> = (q ; q)\<^sub>\<infinity>"
    by (rule prod_qpochhammer_inf_group) (use q in auto)
  finally show ?thesis by (simp add: euler_phi_def)
qed

lemma pentagonal_number_theorem_real:
  fixes q :: real
  assumes q: "\<bar>q\<bar> < 1"
  shows   "euler_phi q = ramanujan_theta (-q) (-(q\<^sup>2))"
proof -
  include qpochhammer_inf_notation
  have "complex_of_real ((q; q)\<^sub>\<infinity>) = (of_real q; of_real q)\<^sub>\<infinity>"
    by (subst qpochhammer_inf_of_real) (use q in auto)
  also have "\<dots> = euler_phi (of_real q)"
    by (simp add: euler_phi_def)
  also have "\<dots> = complex_of_real (ramanujan_theta (-q) (-(q^2)))"
    by (subst pentagonal_number_theorem_complex)
       (use q in \<open>auto simp flip: ramanujan_theta_of_real\<close>)
  finally show ?thesis
    by (simp only: of_real_eq_iff euler_phi_def)
qed

text \<open>
  As a corollary, we get the following power series representation for $\phi(q)$.
\<close>
lemma has_sum_euler_phi_complex:
  fixes q :: complex
  assumes q: "norm q < 1"
  shows "((\<lambda>k. (-1) powi k * q ^ pent_num k) has_sum euler_phi q) UNIV"
proof -
  have *: "q ^ pent_num n = q powi (n * (3 * n - 1) div 2)" for n
  proof -
    have "n * (3 * n - 1) \<ge> 0"
      by (cases "n > 0") (auto intro: mult_nonpos_nonpos)
    hence "q powi (n * (3 * n - 1) div 2) = q ^ nat (n * (3 * n - 1) div 2)"
      unfolding power_int_def by auto
    thus ?thesis
      unfolding pent_num_def by simp
  qed

  show ?thesis
  proof (cases "q = 0")
    case [simp]: True
    have "((\<lambda>n. (-1) powi n * q powi (n*(3*n-1) div 2)) 
            has_sum ramanujan_theta (-q) (-q\<^sup>2)) {0}"
      by (intro has_sum_finiteI) auto
    also have "?this \<longleftrightarrow> ((\<lambda>n. (-1) powi n * q ^ pent_num n) 
                         has_sum ramanujan_theta (-q) (-q\<^sup>2)) UNIV"
      unfolding * by (intro has_sum_cong_neutral) (auto simp: dvd_div_eq_0_iff)
    finally show ?thesis
      by (auto simp: has_sum_iff summable_on_iff_abs_summable_on_complex)
  next
    include qpochhammer_inf_notation
    case [simp]: False
    have "(\<lambda>n. 1 + norm q ^ Suc n) has_prod (-norm q; norm q)\<^sub>\<infinity>"
      using has_prod_qpochhammer_inf[of "norm q" "-norm q"] q by simp
    hence th1: "abs_convergent_prod (\<lambda>n. 1 - q ^ (n+1))"
      by (simp add: abs_convergent_prod_def norm_mult norm_power has_prod_iff)
  
    have prod: "(\<lambda>n. 1 - q ^ Suc n) has_prod (q; q)\<^sub>\<infinity>"
      using has_prod_qpochhammer_inf[of q q] q by simp
    have "((\<lambda>n. (-q) powi (n*(n+1) div 2) * (-(q^2)) powi (n*(n-1) div 2))
             has_sum ramanujan_theta (-q) (-(q^2))) UNIV"
      by (rule has_sum_ramanujan_theta)
         (auto simp: norm_power power_less_one_iff q simp flip: power_Suc)
    also have "(\<lambda>n. (-q) powi (n*(n+1) div 2) * (-(q^2)) powi (n*(n-1) div 2)) = 
               (\<lambda>n. (- 1) powi n * q powi (n*(3*n-1) div 2))"
      (is "?lhs = ?rhs")
    proof
      fix n :: int
      have "(-q) powi (n*(n+1) div 2) * (-(q^2)) powi (n*(n-1) div 2) =
              (-1) powi (n*(n+1) div 2 + n*(n-1) div 2) * 
              (q powi (n*(n+1) div 2) * (q^2) powi (n*(n-1) div 2))"
        by (auto simp: power_int_minus_left)
      also have "n*(n+1) div 2 + n*(n-1) div 2 = (n*(n+1) + n*(n-1)) div 2"
        by (rule div_plus_div_distrib_dvd_left [symmetric]) auto
      also have "(n*(n+1) + n*(n-1)) div 2 = n ^ 2"
        by (simp add: algebra_simps power2_eq_square)
      also have "(-1) powi (n ^ 2) = (-1::complex) powi n"
        by (auto simp: power_int_minus_left)
      also have "(q^2) powi (n*(n-1) div 2) = q powi (n*(n-1))"
        by (simp add: power_int_power)
      also have "q powi (n * (n + 1) div 2) * q powi (n * (n - 1)) =
                 q powi (n * (n + 1) div 2 + (2 * n * (n - 1)) div 2)"
        by (simp add: power_int_add)
      also have "n * (n + 1) div 2 + (2 * n * (n - 1)) div 2 = (n*(n+1) + 2*n*(n-1)) div 2"
        by (rule div_plus_div_distrib_dvd_left [symmetric]) auto
      also have "n*(n+1) + 2*n*(n-1) = n * (3 * n - 1)"
        by (simp add: algebra_simps)
      finally show "?lhs n = ?rhs n" .
    qed
    finally have sum: "((\<lambda>n. (-1) powi n * q powi (n*(3*n-1) div 2)) 
                         has_sum ramanujan_theta (-q) (-q\<^sup>2)) UNIV" .
    also have "ramanujan_theta (-q) (-q\<^sup>2) = euler_phi q"
      using pentagonal_number_theorem_complex[of q] assms by (simp add: euler_phi_def)
    finally show ?thesis unfolding * .
  qed
qed

text \<open>
  The following is the more explicit form of the Pentagonal Number Theorem usually found
  in textbooks:
  \[\prod_{n=1}^\infty \big(1 - q^n\big) = \sum_{k=-\infty}^\infty (-1)^k q^{k(3k-1)/2}\]
  The exponents $g_k$ are the generalised pentagonal numbers we defined earlier.
\<close>
lemma pentagonal_number_theorem_complex':
  fixes q :: complex
  assumes q: "norm q < 1"
  shows "abs_convergent_prod (\<lambda>n. 1 - q^(n+1))" (is ?th1)
    and "(\<lambda>k. (-1) powi k * q ^ pent_num k) abs_summable_on UNIV" (is ?th2)
    and "(\<Prod>n::nat. 1 - q^(n+1)) = (\<Sum>\<^sub>\<infinity>(k::int). (-1) powi k * q ^ pent_num k)" (is ?th3)
proof -
  include qpochhammer_inf_notation
  have *: "q ^ pent_num n = q powi (n * (3 * n - 1) div 2)" for n
  proof -
    have "n * (3 * n - 1) \<ge> 0"
      by (cases "n > 0") (auto intro: mult_nonpos_nonpos)
    hence "q powi (n * (3 * n - 1) div 2) = q ^ nat (n * (3 * n - 1) div 2)"
      unfolding power_int_def by auto
    thus ?thesis
      unfolding pent_num_def by simp
  qed

  have "?th1 \<and> ?th2 \<and> ?th3"
  proof (cases "q = 0")
    case [simp]: True
    have "((\<lambda>n. (-1) powi n * q powi (n*(3*n-1) div 2)) 
            has_sum ramanujan_theta (-q) (-q\<^sup>2)) {0}"
      by (intro has_sum_finiteI) auto
    also have "?this \<longleftrightarrow> ((\<lambda>n. (-1) powi n * q ^ pent_num n)
                         has_sum ramanujan_theta (-q) (-q\<^sup>2)) UNIV"
      unfolding * by (intro has_sum_cong_neutral) (auto simp: dvd_div_eq_0_iff)
    finally show ?thesis
      by (auto simp: abs_convergent_prod_def has_sum_iff summable_on_iff_abs_summable_on_complex)
  next
    case [simp]: False
    have "(\<lambda>n. 1 + norm q ^ Suc n) has_prod (-norm q; norm q)\<^sub>\<infinity>"
      using has_prod_qpochhammer_inf[of "norm q" "-norm q"] q by simp
    hence th1: "abs_convergent_prod (\<lambda>n. 1 - q ^ (n+1))"
      by (simp add: abs_convergent_prod_def norm_mult norm_power has_prod_iff)
  
    have prod: "(\<lambda>n. 1 - q ^ Suc n) has_prod (q; q)\<^sub>\<infinity>"
      using has_prod_qpochhammer_inf[of q q] q by simp
    have sum: "((\<lambda>n. (-1) powi n * q ^ pent_num n) has_sum euler_phi q) UNIV"
      using has_sum_euler_phi_complex[of q] assms by simp
  
    have "(\<lambda>n. (-1) powi n * q ^ pent_num n) summable_on UNIV"
      using sum  by (rule has_sum_imp_summable)
    hence th2: "(\<lambda>n. (-1) powi n * q ^ pent_num n) abs_summable_on UNIV"
      by (simp add: summable_on_iff_abs_summable_on_complex)

    have th3: "(\<Prod>n. 1 - q ^ (n+1)) = (\<Sum>\<^sub>\<infinity>(k::int). (-1) powi k * q ^ pent_num k)"
      using sum prod by (simp add: has_prod_iff has_sum_iff euler_phi_def)

    show ?thesis
      using th1 th2 th3 by blast
  qed
  thus ?th1 ?th2 ?th3
    by blast+
qed


subsubsection \<open>The formal power series version\<close>

text \<open>
  We now rephrase the above analytic result in terms of formal power series.

  First, we give the generating function of $\phi(q)$ in terms of the generalised
  pentagonal numbers.
\<close>
definition fps_euler_phi :: "'a :: ring_1 fps" where
  "fps_euler_phi = 
     Abs_fps (\<lambda>n. if n \<in> pent_nums then if even (inv_pent_num n) then 1 else -1 else 0)"

lemma sums_euler_phi_complex:
  fixes q :: complex and f :: "nat \<Rightarrow> complex"
  assumes q: "norm q < 1"
  defines "f \<equiv> (\<lambda>n. if n \<in> pent_nums then if even (inv_pent_num n) then 1 else -1 else 0)"
  shows   "(\<lambda>k. f k * q ^ k) sums euler_phi q"
proof -
  have "((\<lambda>k. (-1) powi k * q ^ pent_num k) has_sum euler_phi q) UNIV"
    using q by (rule has_sum_euler_phi_complex)

  also have "?this \<longleftrightarrow> ((\<lambda>k. f k * q ^ k) has_sum euler_phi q) pent_nums"
    by (rule has_sum_reindex_bij_witness[of _ inv_pent_num pent_num])
       (auto simp: pent_num_inv_pent_num f_def)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>k. f k * q ^ k) has_sum euler_phi q) UNIV"
    by (rule has_sum_cong_neutral) (auto simp: f_def)
  finally show "(\<lambda>k. f k * q ^ k) sums euler_phi q"
    by (simp add: has_sum_imp_sums)
qed

theorem has_fps_expansion_euler_phi_complex [fps_expansion_intros]:
  "euler_phi has_fps_expansion (fps_euler_phi :: complex fps)"
proof (rule has_fps_expansionI)
  have "eventually (\<lambda>q. q \<in> ball 0 1) (nhds (0::complex))"
    by (rule eventually_nhds_in_open) auto
  thus "eventually (\<lambda>q. (\<lambda>n. fps_nth fps_euler_phi n * q ^ n) sums euler_phi q) (nhds (0::complex))"
  proof eventually_elim
    case (elim q)
    thus ?case
      using sums_euler_phi_complex[of q] by (simp add: fps_euler_phi_def)
  qed
qed


text \<open>
  The formal power series version of the pentagonal number theorem states that the power series
  $\sum_{n\geq 0} p(n) X^n$ and  $\sum_{k\in\mathbb{Z}} (-1)^k X^{k(3k-1)/2}$ are multiplicative
  inverses of one another.

  We just determined that $\sum_{n\geq 0} p(n) q^n = \prod_{k\geq 1} \frac{1}{1-a^k}$ holds 
  analytically, so all we have to do is to lift this to the level of formal power series.
\<close>
theorem fps_Partition'_eq:
  "Abs_fps (\<lambda>n. of_nat (Partition' n) :: complex) = inverse fps_euler_phi"
proof -
  define f :: "nat \<Rightarrow> complex fps" where "f = (\<lambda>n. (\<Prod>i<n. (1 - fps_X ^ Suc i)))"
  define h :: "complex fps" where "h = inverse (Abs_fps (\<lambda>n. of_nat (Partition' n)))"
  define f' :: "nat \<Rightarrow> complex \<Rightarrow> complex" where "f' = (\<lambda>n z. (\<Prod>i<n. (1 - z ^ Suc i)))"

  have "fps_euler_phi = h"
  proof (rule uniform_limit_imp_fps_expansion_eq)
    have "(\<lambda>k. \<Prod>i<k. 1 / (1 - fps_X ^ Suc i)) \<longlonglongrightarrow> Abs_fps (\<lambda>n. complex_of_nat (Partition' n))"
      using has_prod_Partition'_aux[where ?'a = complex] LIMSEQ_lessThan_iff_atMost by blast
    hence "(\<lambda>k. inverse (\<Prod>i<k. 1 / (1 - fps_X ^ Suc i))) \<longlonglongrightarrow> h"
      unfolding h_def by (intro tendsto_intros) auto
    also have "(\<lambda>k. inverse (\<Prod>i<k. 1 / (1 - fps_X ^ Suc i))) = f"
      by (simp add: f_def inverse_prod_fps fps_divide_unit)
    finally show "(f \<longlongrightarrow> h) sequentially" .
  next
    show "open (ball 0 (1/2) :: complex set)" "0 \<in> (ball 0 (1/2) :: complex set)"
      by auto
  next
    show "\<forall>\<^sub>F x in sequentially. f' x has_fps_expansion f x"
      unfolding f'_def f_def by (intro always_eventually allI fps_expansion_intros)
  next
    show "euler_phi has_fps_expansion (fps_euler_phi :: complex fps)"
      by (rule has_fps_expansion_euler_phi_complex)
  next
    define r where "r = (\<lambda>n (a,q). \<Prod>k<n. 1 - a * q ^ k :: complex)"
    define s where "s = (\<lambda>(a,q). qpochhammer_inf a q :: complex)"
    have "uniform_limit (cball 0 (1/2) \<times> cball 0 (1/2)) r s sequentially"
      unfolding r_def s_def by (rule uniform_limit_qpochhammer_inf) (auto simp: compact_Times)
    hence 1: "uniform_limit (ball 0 (1/2)) (\<lambda>n q. r n (q, q)) (\<lambda>q. s (q, q)) sequentially"
      by (rule uniform_limit_compose) auto
    thus "uniform_limit (ball 0 (1 / 2)) f' euler_phi sequentially"
      by (simp add: f'_def r_def s_def euler_phi_def [abs_def])
  next
    show "\<forall>\<^sub>F x in sequentially. f' x holomorphic_on ball 0 (1 / 2)"
      unfolding f'_def by (intro always_eventually allI holomorphic_intros)
  qed auto

  hence "inverse fps_euler_phi =
           inverse (inverse (Abs_fps (\<lambda>n. of_nat (Partition' n) :: complex)))"
    unfolding h_def by simp
  also have "\<dots> = Abs_fps (\<lambda>n. of_nat (Partition' n))"
    by (rule fps_inverse_idempotent) auto
  finally show ?thesis ..
qed

lemma fps_nth_euler_phi_0 [simp]: "fps_nth fps_euler_phi 0 = 1"
proof -
  have "pent_num 0 \<in> pent_nums"
    by blast
  moreover have "inv_pent_num 0 = 0"
    by (intro inv_pent_num_eqI) auto
  ultimately show ?thesis
    unfolding fps_euler_phi_def by simp
qed

lemma has_fps_expansion_inverse_euler_phi_complex:
  "(\<lambda>q. 1 / euler_phi q :: complex) 
     has_fps_expansion Abs_fps (\<lambda>n. of_nat (Partition' n))"
proof -
  have "(\<lambda>q. inverse (euler_phi q :: complex)) has_fps_expansion (inverse fps_euler_phi)"
    by (intro fps_expansion_intros has_fps_expansion_euler_phi_complex) auto
  also have "\<dots> = Abs_fps (\<lambda>n. of_nat (Partition' n))"
    unfolding fps_Partition'_eq ..
  finally show ?thesis
    by (simp add: field_simps)
qed

lemma conv_radius_Partition':
  "conv_radius (\<lambda>n. of_nat (Partition' n) :: 'a :: {banach,real_normed_algebra_1}) \<ge> 1"
proof -
  have "fps_conv_radius (Abs_fps (\<lambda>n. of_nat (Partition' n) :: complex)) \<ge> 1"
    using has_fps_expansion_inverse_euler_phi_complex
    by (rule holomorphic_on_imp_fps_conv_radius_ge) (auto intro!: holomorphic_intros)
  thus ?thesis
    by (simp add: fps_conv_radius_def conv_radius_def)
qed

lemma sums_inverse_euler_phi_complex:
  assumes "norm z < 1"
  shows   "(\<lambda>k. of_nat (Partition' k) * z ^ k :: complex) sums (1 / euler_phi z)"
proof -
  define F where "F = Abs_fps (\<lambda>k. of_nat (Partition' k) :: complex)"
  have "(\<lambda>n. fps_nth F n * z ^ n) sums (1 / euler_phi z)"
  proof (rule has_fps_expansion_imp_sums_complex)
    show "(\<lambda>z. 1 / euler_phi z) has_fps_expansion F"
      unfolding F_def using has_fps_expansion_inverse_euler_phi_complex by simp
  next
    show "(\<lambda>z. 1 / euler_phi z) holomorphic_on eball 0 1"
      by (auto intro!: holomorphic_intros)
  qed (use assms in auto) 
  thus ?thesis
    by (simp add: F_def)
qed

lemma sums_inverse_euler_phi_real:
  assumes "\<bar>x\<bar> < (1::real)"
  shows   "(\<lambda>k. of_nat (Partition' k) * x ^ k) sums (1 / euler_phi x)"
proof -
  have "(\<lambda>k. of_nat (Partition' k) * (of_real x) ^ k :: complex) sums (1 / euler_phi (of_real x))"
    by (rule sums_inverse_euler_phi_complex) (use assms in auto)
  also have "(\<lambda>k. of_nat (Partition' k) * (of_real x) ^ k :: complex) =
             (\<lambda>k. of_real (of_nat (Partition' k) * x ^ k) :: complex)"
    by simp
  also have "1 / euler_phi (of_real x :: complex) = of_real (1 / euler_phi x)"
    using assms by (simp add: euler_phi_of_real)
  finally show ?thesis
    unfolding sums_of_real_iff .
qed


subsection \<open>A recurrence for the partition function\<close>

text \<open>
  A direct consequence of this is the following recurrence for the partition numbers:
  \[p(n) = \sum_{\substack{k\in\mathbb{Z}\\g_k \in [1,n]}} p(n - g_k)\]
  where $n > 0$ and $g_k = k(3k-1)/2$ are the generalised pentagonal numbers. Note that the
  sum on the right-hand side has $O(\sqrt{n})$ terms.
\<close>
theorem Partition'_recurrence:
  assumes n: "n > 0"
  shows   "int (Partition' n) =
             (\<Sum>i | i \<in> {1..n} \<and> i \<in> pent_nums. 
               (if even (inv_pent_num i) then -1 else 1) * int (Partition' (n - i)))"
proof -
  define F where "F = Abs_fps (\<lambda>n. of_nat (Partition' n) :: complex)"
  define G where "G = (fps_euler_phi :: complex fps)"

  have "complex_of_int 0 = fps_nth (1 :: complex fps) n"
    using n by simp
  also have "1 = G * F"
    unfolding F_def G_def fps_Partition'_eq by (simp add: inverse_mult_eq_1')
  also have "fps_nth (G * F) n = (\<Sum>i=0..n. fps_nth G i * fps_nth F (n - i))"
    by (subst fps_mult_nth) auto
  also have "\<dots> = (\<Sum>i=0..n. of_int (fps_nth fps_euler_phi i * int (Partition' (n - i))))"
    by (intro sum.cong) (auto simp: G_def F_def fps_euler_phi_def)
  also have "\<dots> = of_int (\<Sum>i=0..n. fps_nth fps_euler_phi i * int (Partition' (n - i)))"
    by simp
  finally have "0 = (\<Sum>i = 0..n. fps_nth fps_euler_phi i * int (Partition' (n - i)))"
    by (simp only: of_int_eq_iff)
  also have "\<dots> = (\<Sum>i\<in>{0..n}-{0}. fps_nth fps_euler_phi i * int (Partition' (n - i))) + Partition' n"
    by (subst sum.remove[of _ 0]) auto
  also have "(\<Sum>i\<in>{0..n}-{0}. fps_nth fps_euler_phi i * int (Partition' (n - i))) =
             (\<Sum>i | i \<in> {1..n} \<and> i \<in> pent_nums. fps_nth fps_euler_phi i * int (Partition' (n - i)))"
    by (intro sum.mono_neutral_right) (auto simp: fps_euler_phi_def)
  finally have "int (Partition' n) = 
                  (\<Sum>i | i \<in> {1..n} \<and> i \<in> pent_nums. -fps_nth fps_euler_phi i * int (Partition' (n - i)))"
    by (auto simp: add_eq_0_iff2 sum_negf)
  also have "\<dots> = (\<Sum>i | i \<in> {1..n} \<and> i \<in> pent_nums. 
                     (if even (inv_pent_num i) then -1 else 1) * int (Partition' (n - i)))"
    by (intro sum.cong) (auto simp: fps_euler_phi_def)
  finally show ?thesis .
qed


subsection \<open>Upper bound\<close>

(* Theorem 14.5 in Apostol *)
text \<open>
  Lastly, we prove an upper bound for the partition function based on a lower bound
  for $\phi(x)$.

  We follow Apostol's presentation of the proof by van Lint~\cite[Theorem~14.5]{apostol}.
  The basic idea is to recall that
  \[\sum_{k\geq 0} p(k) x^k = \frac{1}{\phi(x)}\]
  and note that due to the monotonicity of $\phi$ we have:
  \[\sum_{k\geq 0} p(k) x^k \geq \sum_{k\geq n} p(n) x^n = p(n) \frac{x^n}{1-x}\]
  After combining the two, we take logarithms and rearrange to get get:
  \[\log p(n) \leq -\log \phi(x) - n \log x + \log (1 - x)\]
  We then use the bound $\phi(x) \geq -\frac{\pi^2}{6} \frac{x}{1-x}$ and make the change
  of variables $t = \frac{1-x}{x}$ and some other small estimates to get:
  \[\log p(n) \leq \frac{\pi^2}{6t} + (n-1) t + \log t\]
  We then plug in the optimal value for $t$ and make some more final estimates to get
  the final result:
  \[p(n) \leq \frac{\pi\exp(K \sqrt{n})}{\sqrt{6(n-1)}}
      \hspace*{2em}\text{where}\ K = \sqrt{\tfrac{2}{3}}\pi\]

  Note that asymptotically, $p(n) \sim \exp(K\sqrt{n}) / (4\sqrt{3}n)$,
  so the inequality is off by roughly a factor of $3\sqrt{n}$, which is relatively small
  considering that $p(n)$ grows superpolynomially.
\<close>
theorem Partition'_le:
  assumes n: "n > 1"
  shows "real (Partition' n) \<le> pi * exp (pi * sqrt (2 / 3 * real n)) / sqrt (6 * (real n - 1))"
proof -
  define c where "c = real n - 1"
  have c: "c > 0"
    using n by (simp add: c_def)
  define u where "u = sqrt (1 + 2/3 * c * pi ^ 2)"
  have u: "u > 1"
    using c by (simp add: u_def)

  define t :: real where "t = (u - 1) / (2 * c)"
  have t: "t > 0"
    using c unfolding t_def by (intro divide_pos_pos) (auto simp: u_def)

  define x where "x = 1 / (1 + t)"
  have x: "x \<in> {0<..<1}"
    using t by (auto simp: x_def)
  have t_conv_x: "t = (1 - x) / x"
    using t by (simp add: x_def field_simps)

  define g where "g = (\<lambda>x. pi ^ 2 / (6 * x) + c * x + ln x)"
  define f where "f = (\<lambda>x::real. 1 / euler_phi x)"
  define p where "p = (\<lambda>n. real (Partition' n))"
  have p_pos: "p n > 0" for n
    by (simp add: p_def Partition'_pos)

  have "p n * x ^ n / (1 - x) \<le> f x"
  proof (rule sums_le)
    show "(\<lambda>k. p k * x ^ k) sums f x"
      unfolding p_def f_def by (rule sums_inverse_euler_phi_real) (use x in auto)
  next
    have "(\<lambda>k. p n * x ^ n * x ^ k) sums (p n * x ^ n * (1 / (1 - x)))"
      by (intro sums_mult geometric_sums) (use x in auto)
    also have "(\<lambda>k. p n * x ^ n * x ^ k) = (\<lambda>k. p n * x ^ (k + n))"
      by (simp add: power_add mult_ac)
    also have "p n * x ^ n * (1 / (1 - x)) = p n * x ^ n / (1 - x)"
      by simp
    finally have "(\<lambda>k. if k + n \<ge> n then p n * x ^ (k + n) else 0) sums (p n * x ^ n / (1 - x))"
      by simp
    thus "(\<lambda>k. if k \<ge> n then p n * x ^ k else 0) sums (p n * x ^ n / (1 - x))"
      by (subst (asm) sums_zero_iff_shift) auto
  next
    fix k :: nat
    show "(if n \<le> k then p n * x ^ k else 0) \<le> p k * x ^ k"
      unfolding p_def using x by (auto intro!: Partition'_mono)
  qed
  hence "ln (p n * x ^ n / (1 - x)) \<le> ln (f x)"
    unfolding f_def using x 
    by (subst ln_le_cancel_iff)
       (auto intro!: euler_phi_pos_real divide_pos_pos mult_pos_pos p_pos)
  also have "ln (p n * x ^ n / (1 - x)) = ln (p n) + real n * ln x - ln (1 - x)"
    using x p_pos[of n] by (simp add: ln_mult ln_div ln_realpow)
  finally have "ln (p n) \<le> ln (f x) + real n * (-ln x) + ln (1 - x)"
    by simp

  also have "ln (f x) \<le> pi ^ 2 / (6 * t)"
    using ln_euler_phi_ge[of x] x by (simp add: f_def ln_div t_conv_x)
  also have "1 - x = t * x"
    using x by (simp add: t_conv_x)
  also have "ln (t * x) = ln t + ln x"
    using t x by (simp add: ln_mult)
  also have "pi\<^sup>2 / (6 * t) + real n * - ln x + (ln t + ln x) =
             pi\<^sup>2 / (6 * t) + c * (-ln x) + ln t"
    by (simp add: algebra_simps c_def)
  also have "-ln x \<le> t"
  proof -
    have "-ln x = ln (1 / x)"
      by (subst ln_div) (use x in auto)
    also have "1 / x = 1 + t"
      using x by (simp add: t_conv_x field_simps)
    also have "ln (1 + t) \<le> t"
      by (rule ln_add_one_self_le_self) (use x in \<open>auto simp: t_conv_x\<close>)
    finally show ?thesis .
  qed
  hence "c * (-ln x) \<le> c * t"
    using c by (intro mult_left_mono) auto
  finally have "ln (p n) \<le> g t"
    unfolding g_def c_def by linarith
  hence "exp (ln (p n)) \<le> exp (g t)"
    by (subst exp_le_cancel_iff)
  hence "p n \<le> exp (g t)"
    by (simp add: p_pos)

  also have "\<dots> = exp (pi\<^sup>2 / (6 * t) + c * t) * t"
    using t by (simp add: g_def exp_add)
  also have "c * t = (u - 1) / 2"
    using c by (simp add: t_def)
  also have "pi ^ 2 / (6 * t) = pi\<^sup>2 / 3 * c / (u - 1)"
    unfolding t_def by (simp add: divide_simps)
  also have "pi\<^sup>2 / 3 * c / (u - 1) + (u - 1) / 2 = sqrt (1 + 2 * c * pi ^ 2 / 3)"
    using c by (simp add: u_def field_simps)
  also have "\<dots> \<le> sqrt (2 / 3 * pi ^ 2 * real n)"
  proof -
    have "1 + 2 * c * pi ^ 2 / 3 = 2 / 3 * pi ^ 2 * real n + (1 - 2 / 3 * pi ^ 2)"
      by (simp add: c_def field_simps)
    also have "1 - 2 / 3 * pi ^ 2 \<le> 1 - 2 / 3 * 3 ^ 2"
      by (intro diff_left_mono mult_left_mono power_mono less_imp_le[OF pi_gt3]) auto
    also have "\<dots> \<le> 0"
      by simp
    finally have "1 + 2 * c * pi ^ 2 / 3 \<le> 2 / 3 * pi ^ 2 * real n"
      by simp
    thus ?thesis
      by (rule real_sqrt_le_mono)
  qed
  also have "\<dots> = pi * sqrt (2 / 3 * real n)"
    by (simp add: real_sqrt_mult real_sqrt_divide)
  also have "t = (sqrt (1 + 2 * c * pi\<^sup>2 / 3) - 1) / (2 * c)"
    by (simp add: t_def u_def)
  also have "\<dots> \<le> (sqrt (2 * c * pi\<^sup>2 / 3)) / (2 * c)"
    using c sqrt_add_le_add_sqrt[of 1 "2 * c * pi ^ 2 / 3"]
    by (intro divide_right_mono) simp_all
  also have "\<dots> = pi / (sqrt 2 * sqrt 3 * sqrt c)"
    using c by (simp add: real_sqrt_mult real_sqrt_divide field_simps power2_eq_square)
  also have "\<dots> = pi / sqrt (6 * c)"
    using c by (simp flip: real_sqrt_mult)

  finally show ?thesis
    using t by (simp add: mult_ac c_def p_def)
qed

end