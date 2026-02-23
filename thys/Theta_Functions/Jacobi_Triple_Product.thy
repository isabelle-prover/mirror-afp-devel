section \<open>The Jacobi Triple Product\<close>
theory Jacobi_Triple_Product
imports
  Theta_Functions
  "Lambert_Series.Lambert_Series_Library"
  "Combinatorial_Q_Analogues.Euler_Function"
begin

(*<*)
(* TODO: notation for the "old" deprecated infinite sums; why is this even still active *)
no_notation Infinite_Set_Sum.abs_summable_on (infix "abs'_summable'_on" 50)
(*>*)

subsection \<open>Versions for Jacobi's theta function\<close>

unbundle qpochhammer_inf_notation

text \<open>
  The following follows the short proof given by Andrews~\cite{andrews},
  which makes use of two series expansions for $(a; b)_\infty$ and $1/(a; b)\infty$ 
  due to Euler.

  We prove it for Jacobi's theta function and derive a version for Ramanujan's later on.
  One could possibly also adapt the prove to work for Ramanujan's version directly, which
  makes the transfer to Jacobi's function a bit easier. However, I chose to do it for
  Jacobi's version first in order to stay closer to the text by Andrews.

  The proof is fairly straightforward; the only messy part is proving the absolute convergence
  of the double sum (which Andrews does not bother doing). This is necessary in order to
  allow the exchange of the order of summation.
\<close>
theorem jacobi_theta_nome_triple_product_complex:
  fixes w q :: complex
  assumes "w \<noteq> 0" "norm q < 1"
  shows   "jacobi_theta_nome w q = (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> * (-q*w ; q\<^sup>2)\<^sub>\<infinity> * (-q/w ; q\<^sup>2)\<^sub>\<infinity>"
proof -
  text \<open>
    We first establish the identity for real $w$ and $q$ with the somewhat arbitrarily
    chosen bounds $q\in (0,\frac{1}{4})$ and $w\in (\frac{1}{2}, 1)$. This is considerably
    more restrictive than Andrews's version, but I was not able to prove absolute convergence
    of the sum for his bounds.

    It does not matter anyway, since we will extend it to the full domain of \<open>\<theta>\<close> by
    analytic continuation later anyway.
  \<close>
  have eq_real: "jacobi_theta_nome w q = (q\<^sup>2; q\<^sup>2)\<^sub>\<infinity> * (-q*w; q\<^sup>2)\<^sub>\<infinity> * (-q/w; q\<^sup>2)\<^sub>\<infinity>"
    if wq: "0 < q" "q < 1/4" "1/2 < w" "w < 1" for q w :: real
  proof -
    have q2: "q^2 < 1"
      using wq by (simp add:  power_less_one_iff)
    define tri where "tri = (\<lambda>n::nat. n*(n+1) div 2)"
    have [simp]: "2 * (n * (n - Suc 0) div 2) = n * (n - Suc 0)" for n
      by (subst dvd_mult_div_cancel) auto
    from wq have [simp]: "w \<noteq> 0" "q \<noteq> 0"
      by auto
    have [simp]: "(q\<^sup>2; q\<^sup>2)\<^sub>\<infinity> \<noteq> 0"
    proof
      assume "(q\<^sup>2; q\<^sup>2)\<^sub>\<infinity> = 0"
      then obtain n where "q^2 * q ^ (2*n) = 1"
        using q2 wq by (auto simp: qpochhammer_inf_zero_iff power_mult)
      hence "q ^ (2*n + 2) = 1"
        by (simp add: eval_nat_numeral)
      moreover have "q ^ (2*n + 2) < 1"
        by (subst power_less_one_iff) (use wq in auto)
      ultimately show False
        by linarith
    qed

    have "((\<lambda>n. (q\<^sup>2)^(n*(n-1) div 2) * (-w*q)^n / (\<Prod>k=1..n. (q\<^sup>2)^k - 1)) has_sum (-w*q;q\<^sup>2)\<^sub>\<infinity>) UNIV"
      by (intro norm_summable_imp_has_sum sums_qpochhammer_inf_real norm_summable_qpochhammer_inf)
         (use wq q2 mult_strict_mono[of w 1 q 1] in auto)
    hence "((\<lambda>n. q ^ (n*(n-1)) * (q^n * (-w)^n) / (\<Prod>k=1..n. q^(2*k) - 1)) has_sum (-w*q; q\<^sup>2)\<^sub>\<infinity>) UNIV"
      by (simp add: norm_power power_less_one_iff power_minus' power_mult_distrib mult_ac
               flip: power_mult)
    also have "(\<lambda>n. q ^ (n*(n-1)) * (q^n * (-w)^n) / (\<Prod>k=1..n. q^(2*k) - 1)) = 
               (\<lambda>n. q ^ (n^2) * w^n * (q^(2*n+2); q^2)\<^sub>\<infinity> / (q^2;q^2)\<^sub>\<infinity>)" (is "?lhs = ?rhs")
    proof
      fix n :: nat
      have "(q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> = (\<Prod>k<n. 1 - q^(2*k+2)) * (q^(2*n+2) ; q\<^sup>2)\<^sub>\<infinity>"
        using qpochhammer_inf_mult_power_q[of "q^2" "q^2" n] q2
        by (simp add: power_add power2_eq_square power_mult_distrib mult_ac mult_2_right
                      qpochhammer_nonneg_def)
      also have "(\<Prod>k<n. 1 - q^(2*k+2)) = (\<Prod>k=1..n. 1 - q^(2*k))"
        by (rule prod.reindex_bij_witness[of _ "\<lambda>k. k-1" Suc]) auto
      also have "(\<Prod>k=1..n. 1 - q^(2*k)) = (-1)^n * (\<Prod>k=1..n. q^(2*k)-1)"
        by (subst prod_diff_swap) auto
      finally have "?lhs n = q ^ (n*(n-1)) * q^n * w^n * (q^(2*n+2); q^2)\<^sub>\<infinity> / (q^2;q^2)\<^sub>\<infinity>"
        by (auto simp: divide_simps power_minus')
      also have "q^(n*(n-1)) * q^n = q^(n*(n-1) + n)"
        by (simp add: power_add)
      also have "n*(n-1) + n = n^2"
        by (simp add: power2_eq_square algebra_simps)
      finally show "?lhs n = ?rhs n" .
    qed
    finally have "((\<lambda>n. (q\<^sup>2; q\<^sup>2)\<^sub>\<infinity> * (q^(n^2) * w^n * (q^(2*n+2); q\<^sup>2)\<^sub>\<infinity> / (q\<^sup>2;q\<^sup>2)\<^sub>\<infinity>))
                     has_sum (q\<^sup>2; q\<^sup>2)\<^sub>\<infinity> * (-w*q;q\<^sup>2)\<^sub>\<infinity>) UNIV"
      by (rule has_sum_cmult_right)
    hence "((\<lambda>n. q^(n^2) * w^n * (q^(2*n+2); q\<^sup>2)\<^sub>\<infinity>) has_sum (q\<^sup>2;q\<^sup>2)\<^sub>\<infinity> * (-w*q;q\<^sup>2)\<^sub>\<infinity>) UNIV"
      by simp
    also have "?this \<longleftrightarrow> ((\<lambda>n. q powi (n^2) * w powi n * (q powi (2*n+2); q\<^sup>2)\<^sub>\<infinity>) has_sum 
                           (q\<^sup>2;q\<^sup>2)\<^sub>\<infinity> * (-w*q;q\<^sup>2)\<^sub>\<infinity>) {0..}"
      by (intro has_sum_reindex_bij_witness[of _ nat int])
         (auto simp: power_int_def nat_add_distrib nat_mult_distrib nat_power_eq)
    also have "\<dots> \<longleftrightarrow> ((\<lambda>n. q powi (n^2) * w powi n * (q powi (2*n+2); q\<^sup>2)\<^sub>\<infinity>) has_sum 
                           (q\<^sup>2;q\<^sup>2)\<^sub>\<infinity> * (-w*q;q\<^sup>2)\<^sub>\<infinity>) UNIV"
    proof (rule has_sum_cong_neutral)
      fix n :: int
      assume "n \<in> UNIV - {0..}"
      hence n: "n < 0"
        by simp
      define k where "k = nat (-n-1)"
      have "q powi (2 * int k) = (q ^ 2) ^ k"
        by (auto simp: power_int_def power_mult nat_mult_distrib)
      hence "q powi (2 * n + 2) * q\<^sup>2 ^ k = q powi (2*(n + 1 + int k))"
        by (simp add: power_int_add flip: power_mult power_int_mult)
      also have "n + 1 + int k = 0"
        using n by (auto simp: k_def)
      finally have "\<exists>k. q powi (2 * n + 2) * q\<^sup>2 ^ k = 1"
        by (intro exI[of _ k]) auto
      thus "q powi (n^2) * w powi n * (q powi (2 * n + 2) ; q\<^sup>2)\<^sub>\<infinity> = 0"
        using q2 by (auto simp: qpochhammer_inf_zero_iff intro!: exI[of _ "-1"])
    qed auto
    finally have "((\<lambda>n. q powi (n^2) * w powi n * (q powi (2*n+2); q\<^sup>2)\<^sub>\<infinity>) has_sum 
                    (q\<^sup>2;q\<^sup>2)\<^sub>\<infinity> * (-w*q;q\<^sup>2)\<^sub>\<infinity>) UNIV" .

    text \<open>
      Brace yourselves: now we have to prove absolute convergence of the double sum.
      We use a crude bound for the inner sum, at which point the outer sum is just
      a geometric one that obviously converges.
    \<close>
    have "((\<lambda>(n,m). q powi n\<^sup>2 * w powi n * ((-1)^m * q powi (m^2+m+2*n*m) / (\<Prod>i=1..m. 1 - q^(2*i)))) has_sum
            (q\<^sup>2; q\<^sup>2)\<^sub>\<infinity> * (-w*q ; q\<^sup>2)\<^sub>\<infinity>) (UNIV \<times> UNIV)"
    proof (rule has_sum_SigmaI; (unfold prod.case)?)
      show "((\<lambda>n. q powi (n^2) * w powi n * (q powi (2*n+2); q\<^sup>2)\<^sub>\<infinity>) 
              has_sum (q\<^sup>2;q\<^sup>2)\<^sub>\<infinity> * (-w*q;q\<^sup>2)\<^sub>\<infinity>) UNIV"
        by fact
    next
      fix n :: int
      have "((\<lambda>m. q\<^sup>2 ^ (m*(m-1) div 2) * (q powi (2*n+2))^m / (\<Prod>k=1..m. q\<^sup>2^k-1)) has_sum
                      (q powi (2*n+2);q\<^sup>2)\<^sub>\<infinity>) UNIV"
        by (intro norm_summable_imp_has_sum sums_qpochhammer_inf_real
                  norm_summable_qpochhammer_inf) (use q2 in auto)
      also have "(\<lambda>m. (q\<^sup>2) ^ (m*(m-1) div 2) * (q powi (2*n+2))^m / (\<Prod>k=1..m. q\<^sup>2^k-1)) =
                 (\<lambda>m. (-1)^m * q powi (m^2+m+2*n*m) / (\<Prod>k=1..m. 1-q^(2*k)))" (is "?lhs = ?rhs")
      proof
        fix m :: nat
        have "(q\<^sup>2) ^ (m*(m-1) div 2) * (q powi (2*n+2))^m = 
              q powi (int m * int (m-1) + int m * (2*n+2))" 
          by (simp add: power_int_add power_int_nonneg_exp nat_mult_distrib power_int_power' 
                        power_mult_distrib ring_distribs mult_ac
                   del: power_Suc flip: power_mult)
        also have "int m * int (m-1) + int m * (2*n+2) = int m ^ 2 + int m + 2 * n * int m"
          by (cases m) (simp_all add: algebra_simps power2_eq_square)
        finally have "q\<^sup>2 ^ (m * (m - 1) div 2) * (q powi (2 * n + 2)) ^ m =
                      q powi (int m ^ 2 + int m + 2 * n * int m)" .
        moreover have "(\<Prod>k=1..m. q\<^sup>2^k-1) = (-1)^m * (\<Prod>k=1..m. 1 - q^(2*k))"
        proof -
          have "(\<Prod>k=1..m. q\<^sup>2^k-1) = (\<Prod>k=1..m. q^(2*k)-1)"
            by (simp add: power_mult)
          also have "\<dots> = (-1)^m * (\<Prod>k=1..m. 1 - q^(2*k))"
            by (subst prod_diff_swap) auto
          finally show ?thesis .
        qed
        ultimately show "?lhs m = ?rhs m"
          by (simp add: divide_simps)
      qed
      finally show "((\<lambda>m. q powi (n^2) * w powi n * ((-1)^m * q powi (m^2+m+2*n*m) / (\<Prod>k=1..m. 1 - q^(2*k)))) has_sum
                       (q powi (n^2) * w powi n * (q powi (2*n+2);q\<^sup>2)\<^sub>\<infinity>)) UNIV"
        by (rule has_sum_cmult_right)
    next
      have "(\<lambda>(n, m). q powi n\<^sup>2 * w powi n * (q powi ((int m)\<^sup>2 + int m + 2 * n * int m) /
              (\<Prod>i = 1..m. 1 - q ^ (2 * i)))) summable_on UNIV \<times> UNIV"
      proof (rule summable_on_comparison_test; (safe)?)
        fix n :: int and m :: nat
        have "q powi (n\<^sup>2) * w powi n * (q powi (m\<^sup>2 + m + 2*n*m) / (\<Prod>i=1..m. 1-q^(2*i))) \<le>
              q powi (n\<^sup>2) * w powi n * (q powi (m\<^sup>2 + m + 2*n*m) / (\<Prod>i=1..m. 1-q^1))"
          by (intro mult_left_mono divide_left_mono prod_mono zero_le_power_int conjI
                       diff_left_mono power_decreasing mult_nonneg_nonneg prod_pos mult_pos_pos)
             (use wq in \<open>auto simp: power_less_one_iff power_le_one_iff\<close>)
        also have "\<dots> = q powi (n\<^sup>2) * w powi n * (q powi (m\<^sup>2 + m + 2*n*m) / (1-q)^m)"
          by simp
        also have "\<dots> = q powi (n+m)^2 * w powi n * (q / (1-q))^m"
          by (simp add: power2_eq_square algebra_simps power_int_add power_divide)
        also have "\<dots> = q powi (n+m)^2 * w powi (n+m) * (q / (w * (1 - q)))^m"
          using wq by (simp add: power_int_add divide_simps mult_ac)
        also have "\<dots> \<le> w powi (n+m)^2 * w powi (n+m) * (q / (w * (1 - q)))^m"
          by (rule mult_right_mono power_int_mono)+ (use wq in auto)
        also have "\<dots> = w powi ((n+m)^2+(n+m)) * (q/(w*(1-q)))^m"
          by (simp add: power2_eq_square power_int_add)             
        finally show "q powi n\<^sup>2 * w powi n * (q powi (int m ^ 2 + int m + 2*n * int m) / 
                         (\<Prod>i=1..m. 1-q^(2*i)))
                      \<le> (case (n, m) of (n, m) \<Rightarrow> w powi ((n+m)^2+(n+m)) * (q/(w*(1-q)))^m)"
          by simp
      next
        have "(\<lambda>(n,m). w powi (n^2+n) * (q/(w*(1-q)))^m) summable_on UNIV \<times> UNIV"
        proof (rule summable_on_SigmaI; (unfold prod.case)?)
          fix n :: int
          have "q < (1 / 2) * (3 / 4)"
            using wq by simp
          also have "\<dots> \<le> w * (1 - q)"
            by (intro mult_mono) (use wq in auto)
          finally have "(\<lambda>m. (q/(w*(1-q)))^m) sums (1 / (1 - q/(w*(1-q))))"
            by (intro geometric_sums) (use wq in \<open>auto simp: power_le_one_iff power_less_one_iff\<close>)
          hence "((\<lambda>m. (q/(w*(1-q)))^m) has_sum (1 / (1 - q/(w*(1-q))))) UNIV"
            by (intro sums_nonneg_imp_has_sum) (use wq in auto)
          thus "((\<lambda>m. w powi (n\<^sup>2 + n) * (q / (w * (1 - q))) ^ m) 
                  has_sum (w powi (n\<^sup>2 + n)) * (1/(1-q/(w*(1-q))))) UNIV"
            by (intro has_sum_cmult_right)
        next
          have "summable (\<lambda>n. w ^ n)"
            by (intro summable_mult2 summable_geometric) (use wq in auto)
          hence "(\<lambda>n. w ^ n) summable_on UNIV"
            by (rule summable_nonneg_imp_summable_on) (use wq in auto)
          hence "(\<lambda>n. w ^ n * (1 / (1 - q / (w * (1 - q))))) summable_on UNIV"
            by (intro summable_on_cmult_left)
          hence "(\<lambda>n. w ^ n * (1 / (1 - q / (w * (1 - q))))) summable_on range (\<lambda>n. n*(n+1))"
            by (rule summable_on_subset) auto
          also have "?this \<longleftrightarrow> (\<lambda>n. w ^ (n*(n+1)) * (1 / (1 - q/(w*(1-q))))) summable_on UNIV"
          proof (subst summable_on_reindex)
            have "strict_mono (\<lambda>n::nat. n * (n + 1))"
              by (intro strict_monoI_Suc) auto
            thus "inj (\<lambda>n::nat. n * (n + 1))"
              by (rule strict_mono_imp_inj_on)
          qed (simp_all only: o_def)
          also have "\<dots> \<longleftrightarrow> (\<lambda>n. w powi (n*(n+1)) * (1 / (1 - q/(w*(1-q))))) summable_on {0..}"
            by (rule summable_on_reindex_bij_witness[of _ nat int])
               (auto simp: power_int_def nat_mult_distrib nat_add_distrib)
          finally have summable1: "(\<lambda>n. w powi (n*(n+1)) * (1/(1-q/(w*(1-q))))) summable_on {0..}" .
          also have "?this \<longleftrightarrow> (\<lambda>n. w powi (n*(n+1)) * (1/(1-q/(w*(1-q))))) summable_on {..-1}"
            by (rule summable_on_reindex_bij_witness[of _ "\<lambda>n. -n-1" "\<lambda>n. -n-1"]) 
               (auto simp: algebra_simps)
          finally have summable2: "(\<lambda>n. w powi (n*(n+1)) * (1/(1-q/(w*(1-q))))) summable_on {..-1}" .
          have "(\<lambda>n. w powi (n*(n+1)) * (1/(1-q/(w*(1-q))))) summable_on ({..-1} \<union> {0..})"
            by (intro summable_on_union summable1 summable2)
          also have "{..-1} \<union> {0::int..} = UNIV"
            by auto
          finally show "(\<lambda>n. w powi (n^2+n) * (1/(1-q/(w*(1-q))))) summable_on UNIV"
            by (simp add: power2_eq_square algebra_simps)
        qed (use wq in auto)
        also have "?this \<longleftrightarrow> ((\<lambda>(n,m). w powi ((n + int m)\<^sup>2 + (n + int m)) * (q/(w*(1-q))) ^ m)
                                summable_on UNIV \<times> UNIV)"
          by (rule summable_on_reindex_bij_witness
                [of _ "\<lambda>(n,m). (n + int m, m)" "\<lambda>(n,m). (n - int m, m)"]) auto
        finally show "(\<lambda>(n,m). w powi ((n+m)\<^sup>2 + (n+m)) * (q/(w*(1-q)))^m) summable_on UNIV \<times> UNIV" .
      qed (use wq in \<open>auto intro!: mult_nonneg_nonneg divide_nonneg_pos prod_pos
                           simp: power_less_one_iff\<close>)
      hence "(\<lambda>(n, m). q powi n\<^sup>2 * w powi n * ((-1) ^ m * q powi ((int m)\<^sup>2 + int m + 2 * n * int m) /
              (\<Prod>i=1..m. 1 - q ^ (2 * i)))) abs_summable_on UNIV \<times> UNIV"
        using wq by (simp add: case_prod_unfold abs_mult power_abs
                               power_int_abs abs_prod power_le_one_iff)
      thus "(\<lambda>(n, m). q powi n\<^sup>2 * w powi n * ((- 1) ^ m * q powi ((int m)\<^sup>2 + int m + 2 * n * int m) /
              (\<Prod>i = 1..m. 1 - q ^ (2 * i)))) summable_on UNIV \<times> UNIV"
        by (rule abs_summable_summable)
    qed

    also have "(\<lambda>(n,m). q powi n\<^sup>2 * w powi n * ((-1)^m * q powi (int m ^ 2 + int m + 2 * n * int m) /
                   (\<Prod>i=1..m. 1 - q^(2*i)))) =
               (\<lambda>(n,m). ((-1)^m * (q/w)^m / (\<Prod>i=1..m. 1 - q^(2*i))) *
                        (q powi ((n+m)^2) * w powi (n+m)))"
      by (simp add: power2_eq_square field_simps power_int_add)
    also have "(\<dots> has_sum ((q\<^sup>2; q\<^sup>2)\<^sub>\<infinity> * (-w*q; q\<^sup>2)\<^sub>\<infinity>)) (UNIV \<times> UNIV) \<longleftrightarrow>
                 ((\<lambda>(n,m). ((-1)^m * (q/w)^m / (\<Prod>i=1..m. 1 - q^(2*i))) * (q powi (n^2) * w powi n))
                    has_sum ((q\<^sup>2; q\<^sup>2)\<^sub>\<infinity> * (-w*q; q\<^sup>2)\<^sub>\<infinity>)) (UNIV \<times> UNIV)"
      by (rule has_sum_reindex_bij_witness[of _ "\<lambda>(n, m). (n - int m, m)" "\<lambda>(n, m). (n + int m, m)"])
         auto
    finally have sum:
      "((\<lambda>(n,m). ((-q/w)^m / (\<Prod>i=1..m. 1 - q^(2*i))) * (q powi (n^2) * w powi n))
         has_sum ((q\<^sup>2; q\<^sup>2)\<^sub>\<infinity> * (-w*q; q\<^sup>2)\<^sub>\<infinity>)) (UNIV \<times> UNIV)" 
      by (simp add: power_minus')

    have "((\<lambda>n. inverse (-q/w; q\<^sup>2)\<^sub>\<infinity> * (q powi (n^2) * w powi n)) 
            has_sum (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> * (- w * q ; q\<^sup>2)\<^sub>\<infinity>) UNIV"
    proof (rule has_sum_SigmaD[OF sum]; unfold prod.case)
      fix n :: int
      have "((\<lambda>m. (-q/w)^m / (\<Prod>i=1..m. 1 - (q\<^sup>2)^i)) has_sum (inverse (-q/w; q\<^sup>2)\<^sub>\<infinity>)) UNIV"
        by (intro norm_summable_imp_has_sum sums_inverse_qpochhammer_inf_real
                  norm_summable_inverse_qpochhammer_inf)
           (use q2 wq in \<open>auto simp: norm_divide\<close>)
      also have "(\<lambda>i. (q^2)^i) = (\<lambda>i. q^(2*i))"
        by (simp add: power_mult)
      finally show "((\<lambda>m. ((-q/w)^m / (\<Prod>i=1..m. 1 - q^(2*i))) * (q powi (n^2) * w powi n)) 
                       has_sum (inverse (-q/w; q\<^sup>2)\<^sub>\<infinity> * (q powi (n^2) * w powi n))) UNIV"
        by (rule has_sum_cmult_left)
    qed
    hence "((\<lambda>n. (-q/w; q\<^sup>2)\<^sub>\<infinity> * (inverse (-q/w; q\<^sup>2)\<^sub>\<infinity> * (q powi (n^2) * w powi n)))
              has_sum (-q/w;q\<^sup>2)\<^sub>\<infinity> * ((q\<^sup>2;q\<^sup>2)\<^sub>\<infinity> * (-w*q;q\<^sup>2)\<^sub>\<infinity>)) UNIV"
      by (rule has_sum_cmult_right)
    moreover have "(-q/w; q\<^sup>2)\<^sub>\<infinity> \<noteq> 0"
    proof
      assume "(-q/w; q\<^sup>2)\<^sub>\<infinity> = 0"
      then obtain n where "q ^ (2*n+1) / w = -1"
        using q2 by (auto simp: qpochhammer_inf_zero_iff power_mult)
      have "norm (q ^ (2 * n + 1) / w) = q ^ (2*n+1) / w"
        using wq by (simp add: norm_divide norm_power)
      also have "\<dots> \<le> q ^ 1 / w"
        by (intro divide_right_mono power_decreasing) (use wq in auto)
      also have "\<dots> < 1"
        using wq by simp
      also note \<open>q ^ (2*n+1) / w = -1\<close>
      finally show False
        by simp
    qed
    ultimately have "((\<lambda>n. w powi n * q powi (n^2)) has_sum 
                       (q\<^sup>2; q\<^sup>2)\<^sub>\<infinity> * (-q*w; q\<^sup>2)\<^sub>\<infinity> * (-q/w; q\<^sup>2)\<^sub>\<infinity>) UNIV"
      by (simp add: divide_simps mult_ac)
    moreover have "((\<lambda>n. w powi n * q powi (n^2)) has_sum jacobi_theta_nome w q) UNIV"
      by (rule has_sum_jacobi_theta_nome) (use wq in auto)
    ultimately show "jacobi_theta_nome w q = (q\<^sup>2; q\<^sup>2)\<^sub>\<infinity> * (-q*w; q\<^sup>2)\<^sub>\<infinity> * (-q/w; q\<^sup>2)\<^sub>\<infinity>"
      using has_sum_unique by blast
  qed

  text \<open>
    We perform analytic continuation to extend the identity to all $w$:
  \<close>
  have eq_real2:
     "jacobi_theta_nome w (complex_of_real q) = 
        (of_real q ^ 2; of_real q ^ 2)\<^sub>\<infinity> * (-of_real q * w; of_real q ^ 2)\<^sub>\<infinity> * 
        (-of_real q / w; of_real q ^ 2)\<^sub>\<infinity>" 
    if wq: "w \<noteq> 0" "q \<in> {0<..<1/4}" for w :: complex and q :: real
  proof -
    define r where "r = (2/3 :: real)"
    have r: "q < r" "1/2 < r" "r < 1"
      using wq by (simp_all add: r_def)
    define f where
      "f = (\<lambda>w. jacobi_theta_nome w (complex_of_real q) - 
                (of_real q ^ 2; of_real q ^ 2)\<^sub>\<infinity> * (-of_real q * w; of_real q ^ 2)\<^sub>\<infinity> * 
                (-of_real q / w; of_real q ^ 2)\<^sub>\<infinity>)"
    have "f w = 0"
    proof (rule analytic_continuation[of f])
      show "f holomorphic_on (-{0})"
        unfolding f_def using wq
        by (auto intro!: holomorphic_intros simp: norm_power power_less_one_iff)
    next
      show "of_real ` {1/2<..<1} \<subseteq> -{0}"
        using wq by auto
    next
      show "of_real r islimpt complex_of_real ` {1/2<..<1}" using r
        by (intro islimpt_isCont_image continuous_intros)
           (auto simp: eventually_at_filter open_imp_islimpt simp del: of_real_add)
    next
      show "f w = 0" if "w \<in> complex_of_real ` {1/2<..<1}" for w :: complex
      proof -
        from that obtain x where x: "w = complex_of_real x" "x \<in> {1/2<..<1}"
          by auto
        have "0 = complex_of_real (jacobi_theta_nome x q - (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> * (-q*x; q\<^sup>2)\<^sub>\<infinity> * (-q/x ; q\<^sup>2)\<^sub>\<infinity>)"
          by (subst eq_real) (use wq x in auto)
        also have "\<dots> = f w" using x wq
          by (simp add: f_def power_less_one_iff 
                   flip: jacobi_theta_nome_of_real qpochhammer_inf_of_real)
        finally show ?thesis ..
      qed
    qed (use wq r in \<open>auto simp: connected_punctured_universe\<close>)
    thus ?thesis
      by (simp add: f_def)
  qed

  text \<open>
    And another analytic continuation to extend it to all $q$:
  \<close>
  show "jacobi_theta_nome w q = (q ^ 2; q ^ 2)\<^sub>\<infinity> * (-q * w; q ^ 2)\<^sub>\<infinity> * (-q / w; q ^ 2)\<^sub>\<infinity>" 
  proof -
    note wq = assms
    define f where
      "f = (\<lambda>q. jacobi_theta_nome w q - 
                (q ^ 2; q ^ 2)\<^sub>\<infinity> * (-q * w; q ^ 2)\<^sub>\<infinity> * (-q / w; q ^ 2)\<^sub>\<infinity>)"
    have "f q = 0"
    proof (rule analytic_continuation[of f])
      show "f holomorphic_on (ball 0 1)"
        unfolding f_def using wq
        by (auto intro!: holomorphic_intros simp: norm_power power_less_one_iff)
    next
      show "of_real ` {0<..<1/4} \<subseteq> ball (0::complex) 1"
        using wq by auto
    next
      show "of_real (1/8) islimpt complex_of_real ` {0<..<1/4}"
        by (intro islimpt_isCont_image continuous_intros)
           (auto simp: eventually_at_filter open_imp_islimpt complex_eq_iff)
    next
      show "f q = 0" if "q \<in> complex_of_real ` {0<..<1/4}" for q :: complex
      proof -
        from that obtain x where x: "q = complex_of_real x" "x \<in> {0<..<1/4}"
          by auto
        have "0 = jacobi_theta_nome w x - (of_real x ^ 2 ; of_real x ^ 2)\<^sub>\<infinity> *
                  (-of_real x * w; of_real x ^ 2)\<^sub>\<infinity> * (-of_real x / w ; of_real x ^ 2)\<^sub>\<infinity>"
          by (subst eq_real2) (use wq x in auto)
        also have "\<dots> = f q" using x wq
          by (simp add: f_def power_less_one_iff 
                   flip: jacobi_theta_nome_of_real qpochhammer_inf_of_real)
        finally show ?thesis ..
      qed
    qed (use wq in auto)
    thus ?thesis
      by (simp add: f_def)
  qed
qed

lemma jacobi_theta_nome_triple_product_real:
  fixes w q :: real
  assumes "w \<noteq> 0" "\<bar>q\<bar> < 1"
  shows   "jacobi_theta_nome w q = (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> * (-q*w ; q\<^sup>2)\<^sub>\<infinity> * (-q/w ; q\<^sup>2)\<^sub>\<infinity>"
proof -
  define q' w' where "q' = complex_of_real q" and "w' = complex_of_real w"
  have "complex_of_real (jacobi_theta_nome w q) = jacobi_theta_nome w' q'"
    by (simp add: jacobi_theta_nome_of_real w'_def q'_def)
  also have "\<dots> = (q'\<^sup>2 ; q'\<^sup>2)\<^sub>\<infinity> * (-q'*w' ; q'\<^sup>2)\<^sub>\<infinity> * (-q'/w' ; q'\<^sup>2)\<^sub>\<infinity>"
    by (rule jacobi_theta_nome_triple_product_complex)
       (use assms in \<open>simp_all add: q'_def w'_def\<close>)
  also have "\<dots> = of_real ((q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> * (-q*w ; q\<^sup>2)\<^sub>\<infinity> * (-q/w ; q\<^sup>2)\<^sub>\<infinity>)" using assms 
    by (simp add: q'_def w'_def power_less_one_iff abs_square_less_1 flip: qpochhammer_inf_of_real)
  finally show ?thesis
    by (simp only: of_real_eq_iff)
qed


subsection \<open>Version of Ramanujan's theta function\<close>

text \<open>
  The triple product for Ramanujan's theta function, which follows easily from the above one,
  has a particularly elegant form:
  \[f(a,b) = (-a; ab)_\infty\,(-b; ab)_\infty\, (ab; ab)_\infty\]
  It follows directly from the version for Jacobi's theta function, although I again have to
  employ analytic continuation to avoid dealing with the branch cuts when converting 
  Ramanujan's theta function to Jacobi's.
\<close>
theorem ramanujan_theta_triple_product_complex:
  fixes a b :: complex
  assumes "norm (a * b) < 1"
  shows   "ramanujan_theta a b = (-a ; a*b)\<^sub>\<infinity> * (-b ; a*b)\<^sub>\<infinity> * (a*b ; a*b)\<^sub>\<infinity>"
proof -
  have real_eq1: "ramanujan_theta a b = (-a ; a * b)\<^sub>\<infinity> * (-b ; a * b)\<^sub>\<infinity> * (a * b ; a * b)\<^sub>\<infinity>"
    if ab: "a > 0" "b > 0" "a * b < 1" for a b :: real
  proof -
    define w q where "w = sqrt (a/b)" and "q = sqrt (a*b)"
    have [simp]: "w \<noteq> 0"
      using ab by (auto simp: w_def sgn_if)
    have q: "\<bar>q\<bar> < 1"
      using ab by (simp_all add: q_def abs_mult flip: real_sqrt_abs')
  
    have "ramanujan_theta a b = jacobi_theta_nome w q"
      using ab by (auto simp: sgn_if jacobi_theta_nome_def w_def q_def real_sqrt_mult real_sqrt_divide)
    also have "\<dots> = (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> * (- q * w ; q\<^sup>2)\<^sub>\<infinity> * (- q / w ; q\<^sup>2)\<^sub>\<infinity>"
      by (rule jacobi_theta_nome_triple_product_real) (use q in auto)
    also have "\<dots> = (-a ; a * b)\<^sub>\<infinity> * (-b ; a * b)\<^sub>\<infinity> * (a * b ; a * b)\<^sub>\<infinity>"
      using ab by (simp add: mult_ac q_def w_def real_sqrt_mult real_sqrt_divide power_mult_distrib)
    finally show ?thesis .
  qed

  have real_eq2: "ramanujan_theta a b = (-a ; a * b)\<^sub>\<infinity> * (-b ; a * b)\<^sub>\<infinity> * (a * b ; a * b)\<^sub>\<infinity>"
    if ab: "a > 0" "norm (a * b) < 1" for a :: real and b :: complex
  proof -
    define f :: "complex \<Rightarrow> complex"
      where "f = (\<lambda>b. ramanujan_theta (of_real a) b - (-of_real a ; of_real a * b)\<^sub>\<infinity> * 
                      (-b ; of_real a * b)\<^sub>\<infinity> * (of_real a * b ; of_real a * b)\<^sub>\<infinity>)"

    have "f b = 0"
    proof (rule analytic_continuation[where f = f])
      show "f holomorphic_on (ball 0 (1 / a))"
        unfolding f_def using ab by (intro holomorphic_intros) (auto simp: norm_mult field_simps)
    next
      show "complex_of_real ` {0<..<1/a} \<subseteq> ball 0 (1/a)"
       and "complex_of_real (1/(2*a)) \<in> ball 0 (1/a)"
        using ab by (auto simp: norm_mult norm_divide field_simps)
    next
      show "complex_of_real (1 / (2 * a)) islimpt
            complex_of_real ` {0<..<1 / a}"
        by (intro islimpt_isCont_image continuous_intros open_imp_islimpt)
           (use ab in \<open>auto simp: complex_eq_iff eventually_at_filter field_simps\<close>)
    next
      fix b assume "b \<in> complex_of_real ` {0<..<1/a}"
      then obtain x where x: "b = complex_of_real x" "x \<in> {0<..<1/a}"
        by auto
      show "f b = 0"
        unfolding f_def using real_eq1[of a x] x ab
        by (simp add: field_simps ramanujan_theta_of_real flip: qpochhammer_inf_of_real)
    qed (use ab in \<open>auto simp: norm_mult field_simps\<close>)
    thus ?thesis
      by (simp add: f_def)
  qed

  show "ramanujan_theta a b = (-a ; a * b)\<^sub>\<infinity> * (-b ; a * b)\<^sub>\<infinity> * (a * b ; a * b)\<^sub>\<infinity>"
  proof (cases "b = 0")
    case True
    thus ?thesis by auto
  next
    case False
    note ab = assms
    define f :: "complex \<Rightarrow> complex"
      where "f = (\<lambda>a. ramanujan_theta a b - (-a ; a * b)\<^sub>\<infinity> * (-b ; a * b)\<^sub>\<infinity> * (a * b ; a * b)\<^sub>\<infinity>)"

    have "f a = 0"
    proof (rule analytic_continuation[where f = f])
      show "f holomorphic_on (ball 0 (1 / norm b))"
        unfolding f_def using ab \<open>b \<noteq> 0\<close>
        by (intro holomorphic_intros) (auto simp: field_simps norm_mult)
    next
      show "complex_of_real ` {0<..<1/norm b} \<subseteq> ball 0 (1 / norm b)"
       and "complex_of_real (1/(2*norm b)) \<in> ball 0 (1 / norm b)"
        using ab \<open>b \<noteq> 0\<close> by (auto simp: norm_mult norm_divide field_simps)
    next
      show "complex_of_real (1 / (2 * norm b)) islimpt
            complex_of_real ` {0<..<1 / norm b}"
        by (intro islimpt_isCont_image continuous_intros open_imp_islimpt)
           (use ab \<open>b \<noteq> 0\<close> in \<open>auto simp: complex_eq_iff eventually_at_filter field_simps\<close>)
    next
      fix a assume "a \<in> complex_of_real ` {0<..<1/norm b}"
      then obtain x where x: "a = complex_of_real x" "x \<in> {0<..<1/norm b}"
        by auto
      show "f a = 0"
        unfolding f_def using real_eq2[of x b] x ab \<open>b \<noteq> 0\<close>
        by (simp add: norm_mult field_simps ramanujan_theta_of_real flip: qpochhammer_inf_of_real)
    qed (use ab \<open>b \<noteq> 0\<close> in \<open>auto simp: norm_mult field_simps\<close>)
    thus ?thesis
      by (simp add: f_def)
  qed
qed

lemma ramanujan_theta_triple_product_real:
  fixes a b :: real
  assumes ab: "\<bar>a * b\<bar> < 1"
  shows   "ramanujan_theta a b = (-a ; a * b)\<^sub>\<infinity> * (-b ; a * b)\<^sub>\<infinity> * (a * b ; a * b)\<^sub>\<infinity>"
proof -
  define a' b' where "a' = complex_of_real a" and "b' = complex_of_real b"
  have "complex_of_real (ramanujan_theta a b) = ramanujan_theta a' b'"
    by (simp add: a'_def b'_def ramanujan_theta_of_real)
  also have "\<dots> = (-a' ; a' * b')\<^sub>\<infinity> * (-b' ; a' * b')\<^sub>\<infinity> * (a' * b' ; a' * b')\<^sub>\<infinity>"
    by (rule ramanujan_theta_triple_product_complex)
       (use assms in \<open>auto simp: a'_def b'_def abs_mult norm_mult\<close>)
  also have "\<dots> = complex_of_real ((-a ; a * b)\<^sub>\<infinity> * (-b ; a * b)\<^sub>\<infinity> * (a * b ; a * b)\<^sub>\<infinity>)"
    using assms by (simp flip: qpochhammer_inf_of_real add: a'_def b'_def)
  finally show ?thesis
    by (simp only: of_real_eq_iff)
qed


subsection \<open>A related identity for $\varphi(q)^3$\<close>

text \<open>
  By instantiating the Jacobi triple product for $f(qz, 1/z)$ and differentiating,
  we obtain the following identity:
  \[\varphi(q)^3 = \sum_{n=-\infty}^\infty (-1)^n n q^{n(n+1)/2} = 
      \sum_{n=0}^\infty (-1)^n (2n+1) q^{n(n+1)/2} \]
\<close>
lemma has_sum_euler_phi_cube_complex:
  fixes q :: complex
  assumes q: "norm q < 1"
  shows "((\<lambda>n. (-1) powi n * of_int n * q powi (n * (n + 1) div 2)) has_sum euler_phi q ^ 3) UNIV"
proof -
  include qpochhammer_inf_notation
  define \<phi> where "\<phi> = euler_phi q"
  define g where "g = (\<lambda>z. ramanujan_theta (q * z) (1 / z))"

  have lim: "uniform_limit (cball (-1) (1/2)) (\<lambda>X z. \<Sum>n\<in>X. q powi (n * (n + 1) div 2) * z powi n)
                 g finite_sets_at_top"
  proof -
    define B where "B = (\<lambda>z. (q * z, 1 / z)) ` cball (-1) (1/2)"
    have "uniform_limit (cball (-1) (1/2)) (\<lambda>X z. case (q*z, 1/z) of (a, b) \<Rightarrow>
             \<Sum>n\<in>X. a powi (n * (n + 1) div 2) * b powi (n * (n - 1) div 2))
             (\<lambda>z. case (q*z, 1/z) of (a, b) \<Rightarrow> ramanujan_theta a b) finite_sets_at_top"
    proof (rule uniform_limit_compose[OF uniform_limit_ramanujan_theta[of B]])
      show "compact B" unfolding B_def
        by (intro compact_continuous_image continuous_intros) auto
    qed (use q in \<open>auto simp: B_def\<close>)
    also have "?this \<longleftrightarrow> uniform_limit (cball (-1) (1/2)) 
                 (\<lambda>X z. \<Sum>n\<in>X. q powi (n * (n + 1) div 2) * z powi n) g finite_sets_at_top"
    proof (intro uniform_limit_cong eventually_finite_subsets_at_top_weakI allI ballI, goal_cases)
      case (1 X z)
      from 1 have [simp]: "z \<noteq> 0"
        by auto
      have "(q*z) powi (n * (n + 1) div 2) * (1/z) powi (n * (n - 1) div 2) =
              q powi (n*(n+1) div 2) * z powi n" for n
      proof -
        have "(q*z) powi (n * (n + 1) div 2) * (1/z) powi (n * (n - 1) div 2) =
              q powi (n * (n + 1) div 2) * z powi (n * (n + 1) div 2 - n * (n - 1) div 2)"
          by (simp add: power_int_diff power_int_divide_distrib power_int_mult_distrib)
        also have "n * (n + 1) div 2 - n * (n - 1) div 2 = n"
          by (cases "even n") (auto elim!: evenE oddE simp: algebra_simps)
        finally show ?thesis .
      qed
      thus ?case by simp
    qed (simp_all add: g_def)
    finally show ?thesis .
  qed

  have ev: "\<forall>\<^sub>F X in finite_sets_at_top.
              continuous_on (cball (-1) (1/2)) (\<lambda>z. \<Sum>n\<in>X. q powi (n * (n + 1) div 2) * z powi n) \<and>
              (\<forall>z\<in>ball (-1) (1/2). ((\<lambda>z. \<Sum>n\<in>X. q powi (n * (n + 1) div 2) * z powi n)
                  has_field_derivative (\<Sum>n\<in>X. q powi (n * (n + 1) div 2) * n * z powi (n - 1))) (at z))"
  proof (intro eventually_finite_subsets_at_top_weakI conjI ballI, goal_cases)
    case 1
    thus ?case by (auto intro!: continuous_intros)
  next
    case 2
    thus ?case
      by (auto intro!: derivative_eq_intros simp: field_simps)
  qed

  obtain g' where g':
    "\<And>z. z \<in> ball (-1) (1/2) \<Longrightarrow> (g has_field_derivative g' z) (at z)"
    "\<And>z. z \<in> ball (-1) (1/2) \<Longrightarrow> 
       ((\<lambda>n. q powi (n * (n + 1) div 2) * of_int n * z powi (n - 1)) has_sum g' z) UNIV"
    unfolding has_sum_def  by (rule has_complex_derivative_uniform_limit[OF ev lim]) auto
  note [derivative_intros] = g'(1)

  define f where
    "f = (\<lambda>z. g z - \<phi> * (1 + 1 / z) * (-q*z ; q)\<^sub>\<infinity> * (-q/z ; q)\<^sub>\<infinity>)"

  have f_eq_0: "f z = 0" if z: "z \<noteq> 0" for z
  proof -
    have "f z = ramanujan_theta (q * z) (1 / z) - \<phi> * (1 + 1 / z) * (-q*z ; q)\<^sub>\<infinity> * (-q/z ; q)\<^sub>\<infinity>"
      by (simp add: g_def f_def)
    also have "ramanujan_theta (q * z) (1 / z) = \<phi> * (-q*z ; q)\<^sub>\<infinity> * (-1/z ; q)\<^sub>\<infinity>"
      using q z by (subst ramanujan_theta_triple_product_complex)
                   (auto simp: abs_mult field_simps euler_phi_def \<phi>_def)
    also have "(-1/z ; q)\<^sub>\<infinity> = (1 + 1 / z) * (-q/z ; q)\<^sub>\<infinity>"
      using q z by (subst qpochhammer_inf_mult_q) (auto)
    also have "\<phi> * (-q*z ; q)\<^sub>\<infinity> * \<dots> = \<phi> * (1 + 1 / z) * (-q*z ; q)\<^sub>\<infinity> * (-q/z ; q)\<^sub>\<infinity>"
      using z by (simp add: field_simps)
    finally show "f z = 0"
      by simp
  qed

  have [derivative_intros]:
      "((\<lambda>x. (-q*x ; q)\<^sub>\<infinity>) has_field_derivative deriv (\<lambda>x. (-q*x ; q)\<^sub>\<infinity>) (-1)) (at (-1))"
    by (intro analytic_derivI analytic_intros) (use q in auto)
  have [derivative_intros]:
      "((\<lambda>x. (-q/x ; q)\<^sub>\<infinity>) has_field_derivative deriv (\<lambda>x. (-q/x ; q)\<^sub>\<infinity>) (-1)) (at (-1))"
    by (intro analytic_derivI analytic_intros) (use q in auto)

  have "(f has_field_derivative (g' (-1) + \<phi> * (q ; q)\<^sub>\<infinity> * (q ; q)\<^sub>\<infinity>)) (at (-1))"
    unfolding f_def by (rule derivative_eq_intros refl | (simp; fail))+
  hence "(f has_field_derivative (g' (-1) + \<phi> ^ 3)) (at (-1))"
    by (simp add: power3_eq_cube \<phi>_def euler_phi_def)
  also have "?this \<longleftrightarrow> ((\<lambda>_. 0) has_field_derivative (g' (-1) + \<phi> ^ 3)) (at (-1))"
  proof (rule DERIV_cong_ev)
    have "eventually (\<lambda>z. z \<in> -{0}) (nhds (-1 :: complex))"
      by (rule eventually_nhds_in_open) auto
    thus "eventually (\<lambda>z. f z = 0) (nhds (-1))"
      by eventually_elim (use f_eq_0 in auto)
  qed auto
  finally have "((\<lambda>_. 0) has_field_derivative g' (-1) + \<phi> ^ 3) (at (-1))" .
  moreover have "((\<lambda>_. 0) has_field_derivative 0) (at (-1 :: complex))"
    by simp
  ultimately have "g' (-1) + \<phi> ^ 3 = 0"
    by (rule DERIV_unique)
  hence "\<phi> ^ 3 = -g' (-1)"
    by (simp add: add_eq_0_iff)

  have "((\<lambda>n. -(q powi (n * (n + 1) div 2) * of_int n * (-1) powi (n - 1))) has_sum -g' (-1)) UNIV"
    unfolding has_sum_uminus using g'(2)[of "-1"] by simp
  also have "(\<lambda>n. -(q powi (n * (n + 1) div 2) * of_int n * (-1) powi (n - 1))) =
             (\<lambda>n. q powi (n * (n + 1) div 2) * of_int n * (-1) powi n)"
    by (simp add: power_int_diff)
  finally show "((\<lambda>n. (-1) powi n * of_int n * q powi (n * (n + 1) div 2))
                  has_sum euler_phi q ^ 3) UNIV"
    using \<open>\<phi> ^ 3 = -g' (-1)\<close> by (simp add: mult_ac \<phi>_def)
qed

lemma has_sum_euler_phi_cube_real:
  fixes q :: real
  assumes q: "\<bar>q\<bar> < 1"
  shows "((\<lambda>n. (-1) powi n * of_int n * q powi (n * (n + 1) div 2)) has_sum euler_phi q ^ 3) UNIV"
proof -
  have "((\<lambda>n. (-1) powi n * of_int n * (complex_of_real q) powi (n * (n + 1) div 2)) 
           has_sum euler_phi (complex_of_real q) ^ 3) UNIV"
    by (rule has_sum_euler_phi_cube_complex) (use q in auto)
  also have "(\<lambda>n. (-1) powi n * of_int n * (complex_of_real q) powi (n * (n + 1) div 2)) =
             (\<lambda>n. of_real ((-1) powi n * of_int n * q powi (n * (n + 1) div 2)))"
    by simp
  also have "euler_phi (complex_of_real q) ^ 3  = of_real (euler_phi q ^ 3)"
    using q by (simp add: euler_phi_of_real)
  finally show ?thesis
    by (subst (asm) has_sum_of_real_iff)
qed

lemma powser_euler_phi_cube_complex:
  fixes q :: complex
  assumes q: "norm q < 1"
  shows "(\<lambda>n. (-1) ^ n * of_nat (2 * n + 1) * q ^ (n * (n + 1) div 2)) sums euler_phi q ^ 3"
proof -
  have sum: "((\<lambda>n. (-1) powi n * of_int n * q powi (n * (n + 1) div 2)) has_sum euler_phi q ^ 3) UNIV"
    by (rule has_sum_euler_phi_cube_complex) fact

  define S1 where "S1 = (\<Sum>\<^sub>\<infinity> n\<in>{0..}. (-1) powi n * of_int n * q powi (n * (n + 1) div 2))"
  have "(\<lambda>n. (-1) powi n * of_int n * q powi (n * (n + 1) div 2)) summable_on {0..}"
    by (rule summable_on_subset, rule has_sum_imp_summable[OF sum]) auto
  hence sum1: "((\<lambda>n. (-1) powi n * of_int n * q powi (n * (n + 1) div 2)) has_sum S1) {0..}"
    using sum unfolding S1_def by simp
  also have "?this \<longleftrightarrow> ((\<lambda>n. (-1)^n * of_nat n * q ^ (n * (n + 1) div 2)) has_sum S1) UNIV"
    by (rule has_sum_reindex_bij_witness[of _ int nat]) 
       (auto simp: add_ac power_int_def nat_add_distrib nat_mult_distrib nat_div_distrib)
  finally have "((\<lambda>n. (-1)^n * of_nat n * q ^ (n * (n + 1) div 2)) has_sum S1) UNIV" .
  hence sums1: "(\<lambda>n. (-1)^n * of_nat n * q ^ (n * (n + 1) div 2)) sums S1"
    by (rule has_sum_imp_sums)

  define S2 where "S2 = (\<Sum>\<^sub>\<infinity> n\<in>{..-1}. (-1) powi n * of_int n * q powi (n * (n + 1) div 2))"
  have "(\<lambda>n. (-1) powi n * of_int n * q powi (n * (n + 1) div 2)) summable_on {..-1}"
    by (rule summable_on_subset, rule has_sum_imp_summable[OF sum]) auto
  hence sum2: "((\<lambda>n. (-1) powi n * of_int n * q powi (n * (n + 1) div 2)) has_sum S2) {..-1}"
    using sum unfolding S2_def by simp
  also have "?this \<longleftrightarrow> ((\<lambda>n. (-1) powi n * of_int (n+1) * q powi (n * (n + 1) div 2)) has_sum S2) {0..}"
    by (rule has_sum_reindex_bij_witness[of _ "\<lambda>n. -n-1" "\<lambda>n. -n-1"])
       (auto simp: algebra_simps power_int_diff power_int_minus simp flip: power_int_inverse)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>n. (-1)^n * of_nat (n+1) * q ^ (n * (n + 1) div 2)) has_sum S2) UNIV"
    by (rule has_sum_reindex_bij_witness[of _ int nat]) 
       (auto simp: add_ac power_int_def nat_add_distrib nat_mult_distrib nat_div_distrib)
  finally have "((\<lambda>n. (-1)^n * of_nat (n+1) * q ^ (n * (n + 1) div 2)) has_sum S2) UNIV" .
  hence sums2: "(\<lambda>n. (-1)^n * of_nat (n+1) * q ^ (n * (n + 1) div 2)) sums S2"
    by (rule has_sum_imp_sums)

  have "(\<lambda>n. (-1)^n * of_nat (2*n+1) * q ^ (n * (n + 1) div 2)) sums (S1 + S2)"
    using sums_add[OF sums1 sums2] by (simp add: algebra_simps)
  also have "S1 + S2 = euler_phi q ^ 3"
  proof -
    have "((\<lambda>n. (-1) powi n * of_int n * q powi (n * (n + 1) div 2)) has_sum (S1 + S2)) ({0..} \<union> {..-1})"
      by (intro has_sum_Un_disjoint sum1 sum2) auto
    also have "{0..} \<union> {..-1} = (UNIV :: int set)"
      by auto
    finally have "((\<lambda>n. (-1) powi n * of_int n * q powi (n * (n + 1) div 2)) has_sum (S1 + S2)) UNIV" .
    from this and sum show "S1 + S2 = euler_phi q ^ 3"
      by (rule has_sum_unique)
  qed
  finally show ?thesis .
qed

lemma powser_euler_phi_cube_real:
  fixes q :: real
  assumes q: "\<bar>q\<bar> < 1"
  shows "(\<lambda>n. (-1) ^ n * real (2 * n + 1) * q ^ (n * (n + 1) div 2)) sums euler_phi q ^ 3"
proof -
  have "(\<lambda>n. (-1) ^ n * of_nat (2 * n + 1) * complex_of_real q ^ (n * (n + 1) div 2)) sums 
          euler_phi (of_real q) ^ 3"
    by (rule powser_euler_phi_cube_complex) (use q in auto)
  also have "(\<lambda>n. (-1) ^ n * of_nat (2 * n + 1) * complex_of_real q ^ (n * (n + 1) div 2)) =
             (\<lambda>n. of_real ((-1) ^ n * real (2 * n + 1) * q ^ (n * (n + 1) div 2)))"
    by simp
  also have "euler_phi (complex_of_real q) ^ 3 = of_real (euler_phi q ^ 3)"
    by (subst euler_phi_of_real) (use q in auto)
  finally show ?thesis
    by (subst (asm) sums_of_real_iff)
qed


subsection \<open>(Non-)vanishing of theta functinos\<close>

text \<open>
  A corollary of the Jacobi triple product: the Jacobi theta function has no zeros apart from
  the ``obvious'' ones, i.e.\ the ones at the center of the cells of the lattice generated
  by the period $1$ and the quasiperiod $t$.
\<close>
corollary jacobi_theta_00_eq_0_iff_complex:
  fixes z t :: complex
  assumes "Im t > 0"
  shows   "jacobi_theta_00 z t = 0 \<longleftrightarrow> (\<exists>m n. z = (of_int m + 1/2) + (of_int n + 1/2) * t)"
proof
  assume "\<exists>m n. z = (of_int m + 1/2) + (of_int n + 1/2) * t"
  then obtain m n where mn: "z = (of_int m + 1/2) + (of_int n + 1/2) * t"
    by blast
  show "jacobi_theta_00 z t = 0"
    unfolding mn by (rule jacobi_theta_00_eq_0')
next
  assume "jacobi_theta_00 z t = 0"
  define w q where "w = to_nome (2*z)" and "q = to_nome t"
  have [simp]: "w \<noteq> 0" "q \<noteq> 0"
    by (auto simp: w_def q_def)
  have q: "norm q < 1"
    using assms by (auto simp: q_def norm_to_nome)
  have q2: "norm (q ^ 2) < 1"
    by (simp add: norm_power power_less_one_iff q)

  note \<open>jacobi_theta_00 z t = 0\<close>
  also have "jacobi_theta_00 z t = jacobi_theta_nome w q"
    by (simp add: jacobi_theta_00_def w_def q_def to_nome_power)
  also have "\<dots> = (q\<^sup>2 ; q\<^sup>2)\<^sub>\<infinity> * (- q * w ; q\<^sup>2)\<^sub>\<infinity> * (- q / w ; q\<^sup>2)\<^sub>\<infinity>"
    by (rule jacobi_theta_nome_triple_product_complex) (use q in auto)
  also have "\<dots> = 0 \<longleftrightarrow> ((\<exists>n. q^(2*n+2) = 1) \<or> (\<exists>n. (w*q^(2*n+1)) = -1) \<or> (\<exists>n. (q^(2*n+1)/w) = -1))"
    using q q2 by (simp add: qpochhammer_inf_zero_iff power_add power_mult mult.assoc
                             power2_eq_square power_mult_distrib mult.commute[of w]
                             minus_equation_iff[of _ 1] eq_commute[of "-1"])
  also have "(\<lambda>n. q^(2*n+2) = 1) = (\<lambda>_. False)"
  proof
    fix n :: nat
    have "norm (q ^ (2*n+2)) < 1"
      unfolding norm_power by (subst power_less_one_iff) (use q in auto)
    thus "q^(2*n+2) = 1 \<longleftrightarrow> False"
      by auto
  qed
  finally show "\<exists>m n. z = (of_int m + 1/2) + (of_int n + 1/2) * t"
  proof (elim disjE exE FalseE)
    fix n :: nat
    assume "w * q ^ (2*n+1) = -1"
    also have "w * q ^ (2*n+1) = to_nome (2 * z + (2 * of_nat n + 1) * t)"
      by (simp add: w_def q_def to_nome_power algebra_simps flip: to_nome_add)
    finally have "(2 * z + (2 * of_nat n + 1) * t - 1) / 2 \<in> \<int>"
      unfolding to_nome_eq_neg1_iff' .
    then obtain m where m: "(2 * z + (2 * of_nat n + 1) * t - 1) / 2 = of_int m"
      by (elim Ints_cases)
    have "z = (of_int m + 1/2) + (of_int (-int (n+1)) + 1/2) * t"
      by (subst m [symmetric]) (auto simp: field_simps)
    thus ?thesis
      by blast
  next
    fix n :: nat
    assume "q ^ (2*n+1) / w = -1"
    also have "q ^ (2*n+1) / w = to_nome (-2 * z + (2 * of_nat n + 1) * t)"
      by (simp add: w_def q_def to_nome_power algebra_simps flip: to_nome_add to_nome_diff)
    finally have "(-2 * z + (2 * of_nat n + 1) * t - 1) / 2 \<in> \<int>"
      unfolding to_nome_eq_neg1_iff' .
    then obtain m where m: "(-2 * z + (2 * of_nat n + 1) * t - 1) / 2 = of_int m"
      by (elim Ints_cases)
    have "z = (of_int (-m-1) + 1/2) + (of_int (int n) + 1/2) * t"
      unfolding of_int_diff of_int_minus by (subst m [symmetric]) (auto simp: field_simps)
    thus ?thesis
      by blast
  qed
qed

lemma jacobi_theta_00_nonzero:
  assumes z: "Im t > 0" and "Im z / Im t - 1 / 2 \<notin> \<int>"
  shows   "jacobi_theta_00 z t \<noteq> 0"
proof
  assume "jacobi_theta_00 z t = 0"
  then obtain m n where *: "z = (of_int m + 1/2) + (of_int n + 1/2) * t"
    by (subst (asm) jacobi_theta_00_eq_0_iff_complex) (use \<open>Im t > 0\<close> in auto)
  hence "Im z = (of_int n + 1/2) * Im t"
    by simp
  hence "Im z / Im t - 1 / 2 = of_int n"
    using z by (auto simp: field_simps)
  also have "\<dots> \<in> \<int>"
    by auto
  finally show False
    using assms by simp
qed

lemma jacobi_theta_00_0_left_nonzero:
  assumes "Im t > 0"
  shows   "jacobi_theta_00 0 t \<noteq> 0"
  by (simp add: assms minus_in_Ints_iff jacobi_theta_00_nonzero)

lemma jacobi_theta_nome_nonzero_complex:
  fixes q w :: complex
  assumes [simp]: "w \<noteq> 0" "norm q < 1"
  assumes "q = 0 \<or> (ln (norm w) / ln (norm q) - 1) / 2 \<notin> \<int>"
  shows   "jacobi_theta_nome w q \<noteq> 0"
proof (cases "q = 0")
  case [simp]: False
  define z where "z = -\<i> * ln w / pi" 
  define t where "t = -\<i> * ln q / pi" 
  have [simp]: "to_nome z = w" "to_nome t = q"
    using assms by (simp_all add: z_def t_def to_nome_def)
  have "Im t > 0"
    by (auto simp: t_def field_simps)

  have *: "Im z / (2 * Im t) - 1 / 2 = (ln (norm w) / ln (norm q) - 1) / 2"
    by (auto simp: z_def t_def)
  have "jacobi_theta_nome w q = jacobi_theta_00 (z/2) t"
    by (simp add: jacobi_theta_00_def to_nome_power)
  also have "\<dots> \<noteq> 0"
  proof (rule jacobi_theta_00_nonzero)
    have "Im (z / 2) / Im t - 1/2 = ln (norm w) / (2 * ln (norm q)) - 1 / 2"
      by (simp add: z_def t_def)
    also have "\<dots> = (ln (norm w) / ln (norm q) - 1) / 2"
      by (simp add: field_simps)
    also have "\<dots> \<notin> \<int>"
      using assms by auto
    finally show "Im (z / 2) / Im t - 1/2 \<notin> \<int>" .
  qed (use * \<open>Im t > 0\<close> in auto)
  finally show ?thesis .
qed auto

lemma jacobi_theta_nome_q_q_nonzero_complex:
  assumes "norm (q::complex) < 1" "q \<noteq> 0"
  shows   "jacobi_theta_nome q q \<noteq> 0"
proof
  assume "jacobi_theta_nome q q = 0"
  define t where "t = -\<i> * ln q / pi" 
  have [simp]: "to_nome t = q"
    using assms by (simp_all add: t_def to_nome_def)
  have "Im t > 0"
    using assms by (auto simp: t_def field_simps)

  note \<open>jacobi_theta_nome q q = 0\<close>
  also have "jacobi_theta_nome q q = jacobi_theta_00 (t/2) t"
    by (simp add: jacobi_theta_00_def to_nome_power)
  finally obtain m n where *: "t / 2 = (of_int m + 1/2) + (of_int n + 1/2) * t"
    by (subst (asm) jacobi_theta_00_eq_0_iff_complex) (use \<open>Im t > 0\<close> in auto)
  have "t = (2 * of_int m + 1) + (2 * of_int n + 1) * t"
    using arg_cong[OF *, of "\<lambda>x. x * 2"] by (simp add: ring_distribs mult_ac)
  hence **: "2 * of_int n * t = -(2 * of_int m + 1)"
    by (Groebner_Basis.algebra)
  have "n = 0"
    using \<open>Im t > 0\<close> arg_cong[OF **, of Im] by simp
  with ** have "-2 * complex_of_int m = of_int 1"
    by simp
  also have "-2 * complex_of_int m = of_int (-2 * m)"
    by simp
  finally have "-2 * m = 1"
    by (simp only: of_int_eq_iff)
  thus False
    by presburger
qed

lemma jacobi_theta_nome_nonzero_real:
  fixes q w :: real
  assumes [simp]: "w \<noteq> 0" "norm q < 1" and "(ln \<bar>w\<bar> / ln \<bar>q\<bar> - 1) / 2 \<notin> \<int>"
  shows   "jacobi_theta_nome w q \<noteq> 0"
proof -
  have "jacobi_theta_nome (complex_of_real w) (complex_of_real q) \<noteq> 0"
    by (rule jacobi_theta_nome_nonzero_complex) (use assms in auto)
  thus ?thesis
    by (simp add: jacobi_theta_nome_of_real)
qed

lemma jacobi_theta_nome_1_left_nonzero_complex:
  assumes "norm (q :: complex) < 1"
  shows   "jacobi_theta_nome 1 q \<noteq> 0"
  by (simp add: assms minus_in_Ints_iff jacobi_theta_nome_nonzero_complex)

lemma jacobi_theta_nome_1_left_nonzero_real:
  assumes "\<bar>q::real\<bar> < 1"
  shows   "jacobi_theta_nome 1 q \<noteq> 0"
  by (metis assms jacobi_theta_nome_1_left_nonzero_complex jacobi_theta_nome_of_real 
            norm_of_real of_real_0 of_real_1)

unbundle no_qpochhammer_inf_notation

end