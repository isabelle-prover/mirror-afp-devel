
(* Author: Benoît Ballenghien, Université Paris-Saclay, CNRS, ENS Paris-Saclay, LMF *)

(*<*)
theory SG_Theorem
  imports FLT_Sufficient_Conditions
begin
  (*>*)


section \<open>Sophie Germain's Theorem: classical Version\<close>

text \<open>The proof we give here is from \<^cite>\<open>Francinou_Gianella_Nicolas_2014\<close>.\<close>

subsection \<open>A Crucial Lemma\<close>

lemma Sophie_Germain_lemma_computation : 
  fixes x y :: int assumes \<open>odd p\<close>
  defines \<open>S \<equiv> \<Sum>k = 0..p - 1. (- y) ^ (p - 1 - k) * x ^ k\<close>
  shows \<open>(x + y) * S = x ^ p + y ^ p\<close>
proof -
  from \<open>odd p\<close> have \<open>0 < p\<close> by (simp add: odd_pos)

  from int_distrib(1) have \<open>(x + y) * S = x * S - (- y) * S\<close> by auto
  have \<open>x * S = (\<Sum>k = 0..p - 1. (- y) ^ (p - 1 - k) * x ^ (k + 1))\<close>
    by (unfold S_def, subst sum_distrib_left) (rule sum.cong[OF refl], simp)
  also have \<open>\<dots> = (\<Sum>k = 0..p - 1. (- y) ^ (p - (k + 1)) * x ^ (k + 1))\<close> by simp
  also have \<open>\<dots> = x ^ p + (\<Sum>k = 1..p - 1. (- y) ^ (p - k) * x ^ k)\<close>
    by (subst sum.shift_bounds_cl_nat_ivl[symmetric])
      (simp, metis One_nat_def \<open>0 < p\<close> not_gr0 power_eq_if)
  finally have S1 : \<open>x * S = x ^ p + (\<Sum>k = 1..p - 1. (- y) ^ (p - k) * x ^ k)\<close> .

  have \<open>k \<in> {0..p - 1} \<Longrightarrow> (- y) ^ Suc (p - 1 - k) * x ^ k = (- y) ^ (p - k) * x ^ k\<close> for k
    by (rule arg_cong[where f = \<open>\<lambda>n. (- y) ^ n * x ^ _\<close>])
      (metis Suc_diff_le Suc_pred' \<open>0 < p\<close> atLeastAtMost_iff)
  hence \<open>(- y) * S = (\<Sum>k = 0..p - 1. (- y) ^ (p - k) * x ^ k)\<close>
    by (unfold S_def, subst sum_distrib_left, intro sum.cong[OF refl])
      (subst mult.assoc[symmetric], subst power_Suc[symmetric], simp)
  also have \<open>\<dots> = (- y) ^ (p - 0) * x ^ 0 + (\<Sum>k = 1..p - 1. (- y) ^ (p - k) * x ^ k)\<close>
    by (unfold One_nat_def, subst sum.atLeast_Suc_atMost[symmetric]) simp_all
  also have \<open>(- y) ^ (p - 0) * x ^ 0 = - (y ^ p)\<close>
    by (simp add: \<open>odd p\<close>)
  finally have S2 : \<open>- y * S = - (y ^ p) + (\<Sum>k = 1..p - 1. (- y) ^ (p - k) * x ^ k)\<close> .

  show \<open>(x + y) * S = x ^ p + y ^ p\<close>
    unfolding \<open>(x + y) * S = x * S - (- y) * S\<close> S1 S2 by simp
qed

lemma Sophie_Germain_lemma_computation_cong_simp :
  fixes p :: nat and n x y :: int assumes \<open>p \<noteq> 0\<close> \<open>[y = - x] (mod n)\<close>
  defines \<open>S \<equiv> \<lambda>x y. \<Sum>k = 0..p - 1. (- y) ^ (p - 1 - k) * x ^ k\<close>
  shows \<open>[S x y = p * x ^ (p - 1)] (mod n)\<close>
proof -
  from \<open>[y = - x] (mod n)\<close> have \<open>[S x y = S x (- x)] (mod n)\<close>
    unfolding S_def
    by (meson cong_minus_minus_iff cong_pow cong_scalar_right cong_sum)
  also have \<open>S x (- x) = (\<Sum>k = 0..p - 1. x ^ (p - 1))\<close>
    unfolding S_def
    by (rule sum.cong[OF refl], simp)
      (metis One_nat_def diff_Suc_eq_diff_pred le_add_diff_inverse2 power_add)
  also from \<open>p \<noteq> 0\<close> have \<open>\<dots> = p * x ^ (p - 1)\<close> by simp
  finally show \<open>[S x y = p * x ^ (p - 1)] (mod n)\<close> .
qed

lemma Sophie_Germain_lemma_only_possible_prime_common_divisor :
  fixes x y z :: int and p :: nat
  defines S_def: \<open>S \<equiv> \<lambda>x y. \<Sum>k = 0..p - 1. (- y) ^ (p - 1 - k) * x ^ k\<close>
  assumes \<open>prime p\<close> \<open>prime q\<close> \<open>coprime x y\<close> \<open>q dvd x + y\<close> \<open>q dvd S x y\<close>
  shows \<open>q = p\<close>
proof (rule ccontr)
  from \<open>prime p\<close> have \<open>p \<noteq> 0\<close> by auto
  assume \<open>q \<noteq> p\<close>
  from \<open>q dvd x + y\<close> have \<open>[y = - x] (mod q)\<close>
    by (metis add_minus_cancel cong_iff_dvd_diff uminus_add_conv_diff)
  from Sophie_Germain_lemma_computation_cong_simp[OF \<open>p \<noteq> 0\<close> this]
  have \<open>[S x y = p * x ^ (p - 1)] (mod q)\<close> unfolding S_def .
  with \<open>q dvd S x y\<close> \<open>q \<noteq> p\<close> \<open>prime q\<close> \<open>prime p\<close> have \<open>q dvd x ^ (p - 1)\<close>
    by (metis cong_dvd_iff prime_dvd_mult_iff prime_nat_int_transfer primes_dvd_imp_eq)
  with \<open>prime q\<close> prime_dvd_power_int prime_nat_int_transfer have \<open>q dvd x\<close> by blast
  with \<open>q dvd x + y\<close> \<open>[y = - x] (mod q)\<close> have \<open>q dvd y\<close> by (simp add: cong_dvd_iff)
  with \<open>coprime x y\<close> \<open>q dvd x\<close> \<open>prime q\<close> show False
    by (metis coprime_def not_prime_unit)
qed

lemma Sophie_Germain_lemma :
  fixes x y z :: int
  assumes \<open>odd p\<close> and \<open>prime p\<close> and fermat : \<open>x ^ p + y ^ p + z ^ p = 0\<close>
    and \<open>[x \<noteq> 0] (mod p)\<close> and \<open>coprime y z\<close>
  defines \<open>S \<equiv> \<Sum>k = 0..p - 1. (- z) ^ (p - 1 - k) * y ^ k\<close>
  shows \<open>\<exists>a \<alpha>. y + z = a ^ p \<and> S = \<alpha> ^ p\<close>
proof -
  from Sophie_Germain_lemma_computation[OF \<open>odd p\<close>]
  have \<open>(y + z) * S = y ^ p + z ^ p\<close> unfolding S_def .
  also from fermat have \<open>\<dots> = (- x) ^ p\<close> by (simp add: \<open>odd p\<close>)
  finally have \<open>(y + z) * S = \<dots>\<close> .
  
  have \<open>coprime (y + z) S\<close>
  proof (rule ccontr)
    assume \<open>\<not> coprime (y + z) S\<close>
    then consider \<open>y + z = 0\<close> | \<open>S = 0\<close> | q :: nat where \<open>prime q\<close> \<open>q dvd y + z\<close> \<open>q dvd S\<close>
      by (elim not_coprime_nonzeroE)
        (use \<open>(y + z) * S = (- x) ^ p\<close> \<open>[x \<noteq> 0] (mod p)\<close> in force,
          metis nat_0_le prime_int_nat_transfer)
    hence \<open>p dvd (y + z) * S\<close>
    proof cases
      fix q :: nat assume \<open>prime q\<close> \<open>q dvd y + z\<close> \<open>q dvd S\<close>
      from Sophie_Germain_lemma_only_possible_prime_common_divisor
        [OF \<open>prime p\<close> _ \<open>coprime y z\<close> \<open>q dvd y + z\<close> \<open>q dvd S\<close>[unfolded S_def]]
      show \<open>p dvd (y + z) * S\<close> using \<open>int q dvd S\<close> \<open>prime q\<close> by auto
    qed simp_all
    with \<open>(y + z) * S = (- x) ^ p\<close> \<open>[x \<noteq> 0] (mod p)\<close> show False
      by (metis \<open>prime p\<close> cong_0_iff dvd_minus_iff prime_dvd_power_int prime_nat_int_transfer)
  qed

  from prod_is_some_powerE[OF coprime_commute[THEN iffD1, OF \<open>coprime (y + z) S\<close>]]
  obtain \<alpha> where \<open>normalize S = \<alpha> ^ p\<close>
    by (metis (no_types, lifting) \<open>(y + z) * S = (- x) ^ p\<close> mult.commute)
  moreover from prod_is_some_powerE[OF \<open>coprime (y + z) S\<close> \<open>(y + z) * S = (- x) ^ p\<close>]
  obtain a where \<open>normalize (y + z) = a ^ p\<close> by blast
  ultimately have \<open>S = (if 0 \<le> S then \<alpha> ^ p else (- \<alpha>) ^ p)\<close>
    \<open>y + z = (if 0 \<le> y + z then a ^ p else (- a) ^ p)\<close>
    by (metis \<open>odd p\<close> abs_of_nonneg abs_of_nonpos
        add.inverse_inverse linorder_linear normalize_int_def power_minus_odd)+
  thus \<open>\<exists>a \<alpha>. y + z = a ^ p \<and> S = \<alpha> ^ p\<close> by meson
qed



subsection \<open>The Theorem\<close>

theorem Sophie_Germain_theorem :
  \<open>\<nexists>x y z :: int. x ^ p + y ^ p = z ^ p \<and> [x \<noteq> 0] (mod p) \<and>
                  [y \<noteq> 0] (mod p) \<and> [z \<noteq> 0] (mod p)\<close> if SG : \<open>SG p\<close>
proof (rule ccontr) \<comment> \<open>The proof is done by contradiction.\<close>
  from SophGer_primeD(1)[OF \<open>SG p\<close>] have odd_p : \<open>odd p\<close> .
  from SG_simps.pos[OF \<open>SG p\<close>] have pos_p : \<open>0 < p\<close> .

  assume \<open>\<not> (\<nexists>x y z. x ^ p + y ^ p = z ^ p \<and> [x \<noteq> 0] (mod int p) \<and>
                     [y \<noteq> 0] (mod int p) \<and> [z \<noteq> 0] (mod int p))\<close>
  then obtain x y z :: int
    where fermat : \<open>x ^ p + y ^ p = z ^ p\<close>
      and not_cong_0 : \<open>[x \<noteq> 0] (mod p)\<close> \<open>[y \<noteq> 0] (mod p)\<close> \<open>[z \<noteq> 0] (mod p)\<close> by blast

\<comment> \<open>We first assume w.l.o.g. that \<^term>\<open>x\<close>, \<^term>\<open>y\<close> and \<^term>\<open>z\<close> are setwise \<^const>\<open>coprime\<close>.\<close>
  let ?gcd = \<open>Gcd {x, y, z}\<close>
  wlog coprime : \<open>?gcd = 1\<close> goal False generalizing x y z keeping fermat not_cong_0
    using FLT_setwise_coprime_reduction_mod_version[OF fermat not_cong_0]
      hypothesis by blast

\<comment> \<open>Then we can deduce that \<^term>\<open>x\<close>, \<^term>\<open>y\<close> and \<^term>\<open>z\<close> are pairwise \<^const>\<open>coprime\<close>.\<close>
  have coprime_x_y : \<open>coprime x y\<close>
    by (fact FLT_setwise_coprime_imp_pairwise_coprime
        [OF SG_simps.nonzero[OF \<open>SG p\<close>] fermat coprime])
  have coprime_y_z : \<open>coprime y z\<close>
  proof (subst coprime_minus_right_iff[symmetric],
      rule FLT_setwise_coprime_imp_pairwise_coprime[OF SG_simps.nonzero[OF \<open>SG p\<close>]])
    from fermat \<open>odd p\<close> show \<open>y ^ p + (- z) ^ p = (- x) ^ p\<close> by simp
  next
    show \<open>Gcd {y, - z, - x} = 1\<close>
      by (metis Gcd_insert coprime gcd_neg1_int insert_commute)
  qed
  have coprime_x_z : \<open>coprime x z\<close>
  proof (subst coprime_minus_right_iff[symmetric],
      rule FLT_setwise_coprime_imp_pairwise_coprime[OF SG_simps.nonzero[OF \<open>SG p\<close>]])
    from fermat \<open>odd p\<close> show \<open>x ^ p + (- z) ^ p = (- y) ^ p\<close> by simp
  next
    show \<open>Gcd {x, - z, - y} = 1\<close> 
      by (metis Gcd_insert coprime gcd_neg1_int insert_commute)
  qed

  let ?q = \<open>2 * p + 1\<close>
    \<comment> \<open>From @{thm [show_question_marks = false] SG_simps.p_th_power_mod_q} we have that among \<^term>\<open>x\<close>, \<^term>\<open>y\<close>
      and \<^term>\<open>z\<close>, one (and only one, see below) is a multiple of \<^term>\<open>?q\<close>.\<close>
  have q_dvd_xyz : \<open>?q dvd x \<or> ?q dvd y \<or> ?q dvd z\<close>
  proof (rule ccontr)
    have cong_add_here : \<open>[x ^ p = n1] (mod ?q) \<Longrightarrow> [y ^ p = n2] (mod ?q) \<Longrightarrow> [z ^ p = n3] (mod ?q) \<Longrightarrow>
                          [x ^ p + y ^ p + (- z) ^ p = n1 + n2 - n3] (mod ?q)\<close> for n1 n2 n3
      by (simp add: cong_add cong_diff \<open>odd p\<close>)
    assume \<open>\<not> (?q dvd x \<or> ?q dvd y \<or> ?q dvd z)\<close>
    hence \<open>\<not> ?q dvd x\<close> \<open>\<not> ?q dvd y\<close> \<open>\<not> ?q dvd z\<close> by simp_all
    from this[THEN SG_simps.p_th_power_mod_q[OF \<open>SG p\<close>]] cong_add_here \<open>odd p\<close>
    have \<open>  [x ^ p + y ^ p + (- z) ^ p = - 3] (mod ?q) \<or> [x ^ p + y ^ p + (- z) ^ p = - 1] (mod ?q)
          \<or> [x ^ p + y ^ p + (- z) ^ p = 1] (mod ?q) \<or> [x ^ p + y ^ p + (- z) ^ p = 3] (mod ?q)\<close> (is ?disj_congs)
      by (elim disjE) fastforce+ (* eight cases *)
    moreover from fermat \<open>odd p\<close> have \<open>[x ^ p + y ^ p + (- z) ^ p = 0] (mod ?q)\<close> by simp
    ultimately show False by (metis cong_def SG_simps.notcong_zero[OF \<open>SG p\<close>])
  qed

\<comment> \<open>Without loss of generality, we can assume that \<^term>\<open>x\<close> is a multiple of \<^term>\<open>?q\<close>.\<close>
  wlog \<open>?q dvd x\<close> goal False generalizing x y z
    keeping fermat not_cong_0 coprime_x_y coprime_y_z coprime_x_z q_dvd_xyz
  proof -
    from negation q_dvd_xyz have \<open>?q dvd y \<or> ?q dvd z\<close> by simp
    thus False
    proof (elim disjE)
      assume \<open>?q dvd y\<close>
      thus False
      proof (rule hypothesis[OF _ _ not_cong_0(2, 1, 3)])
        from fermat show \<open>y ^ p + x ^ p = z ^ p\<close> by linarith
      next
        show \<open>coprime y x\<close> \<open>coprime x z\<close> \<open>coprime y z\<close>
          by (simp_all add: coprime_commute coprime_x_y coprime_x_z coprime_y_z)
      next
        from q_dvd_xyz show \<open>?q dvd y \<or> ?q dvd x \<or> ?q dvd z\<close> by linarith
      qed
    next
      assume \<open>?q dvd z\<close>
      hence \<open>?q dvd - z\<close> by simp
      thus False
      proof (rule hypothesis)
        from fermat \<open>odd p\<close> show \<open>(- z) ^ p + x ^ p = (- y) ^ p\<close> by simp
      next
        from \<open>[x \<noteq> 0] (mod p)\<close> \<open>[y \<noteq> 0] (mod p)\<close> \<open>[z \<noteq> 0] (mod p)\<close>
        show \<open>[x \<noteq> 0] (mod p)\<close> \<open>[- y \<noteq> 0] (mod p)\<close> \<open>[- z \<noteq> 0] (mod p)\<close>
          by (simp_all add: cong_0_iff)
      next
        show \<open>coprime (- z) x\<close> \<open>coprime x (- y)\<close> \<open>coprime (- z) (- y)\<close>
          by (simp_all add: coprime_commute coprime_x_y coprime_x_z coprime_y_z)
      next
        from q_dvd_xyz show \<open>?q dvd - z \<or> ?q dvd x \<or> ?q dvd - y\<close> by auto
      qed
    qed
  qed

\<comment> \<open>Now we can use the lemma above.\<close>
  let ?S = \<open>\<lambda>y z. \<Sum>k = 0..p - 1. (- z) ^ (p - 1 - k) * y ^ k\<close>
  from fermat \<open>odd p\<close> have \<open>y ^ p + x ^ p + (- z) ^ p = 0\<close>
    \<open>x ^ p + y ^ p + (- z) ^ p = 0\<close> \<open>(-z ) ^ p + x ^ p + y ^ p = 0\<close> by simp_all
  from Sophie_Germain_lemma[OF SophGer_primeD(1-2)[OF \<open>SG p\<close>]
      \<open>x ^ p + y ^ p + (- z) ^ p = 0\<close> \<open>[x \<noteq> 0] (mod p)\<close>]
  obtain a \<alpha> where a_prop : \<open>y + (- z) = a ^ p\<close>
    and \<alpha>_prop : \<open>?S y (-z) = \<alpha> ^ p\<close>
    using coprime_minus_right_iff coprime_y_z by blast

  from Sophie_Germain_lemma[OF SophGer_primeD(1-2)[OF \<open>SG p\<close>]
      \<open>y ^ p + x ^ p + (- z) ^ p = 0\<close> \<open>[y \<noteq> 0] (mod p)\<close>]
  obtain b where b_prop : \<open>x + - z = b ^ p\<close>
    by (metis coprime_minus_right_iff coprime_x_z)
  
  from Sophie_Germain_lemma[OF SophGer_primeD(1-2)[OF \<open>SG p\<close>]
      \<open>(-z ) ^ p + x ^ p + y ^ p = 0\<close>] coprime_x_z \<open>[z \<noteq> 0] (mod p)\<close> 
  obtain c where c_prop : \<open>x + y = c ^ p\<close>
    by (meson cong_0_iff coprime_x_y dvd_minus_iff)


  from \<open>?q dvd x\<close> have \<open>\<not> ?q dvd y\<close> and \<open>\<not> ?q dvd z\<close>
    using coprime_x_y coprime_x_z not_coprimeI not_prime_unit prime_nat_int_transfer
    by (metis SophGer_primeD(3)[OF \<open>SG p\<close>] prime_nat_int_transfer)+

  from b_prop \<open>?q dvd x\<close> have \<open>[b ^ p = - z] (mod ?q)\<close>
    by (metis add_diff_cancel_right' cong_iff_dvd_diff)
  with \<open>\<not> ?q dvd z\<close> cong_dvd_iff dvd_minus_iff have \<open>\<not> ?q dvd b ^ p\<close> by blast
  with \<open>0 < p\<close> have \<open>\<not> ?q dvd b\<close> by (meson dvd_power dvd_trans)
  with SG_simps.p_th_power_mod_q[OF \<open>SG p\<close>]
  have cong1 : \<open>[b ^ p = 1] (mod ?q) \<or> [b ^ p = - 1] (mod ?q)\<close> by blast

  from c_prop \<open>?q dvd x\<close> have \<open>[c ^ p = y] (mod ?q)\<close>
    by (metis add_diff_cancel_right' cong_iff_dvd_diff)
  with \<open>\<not> ?q dvd y\<close> cong_dvd_iff have \<open>\<not> ?q dvd c ^ p\<close> by blast
  with \<open>0 < p\<close> have \<open>\<not> ?q dvd c\<close> by (meson dvd_power dvd_trans)
  with SG_simps.p_th_power_mod_q[OF \<open>SG p\<close>]
  have cong2 : \<open>[c ^ p = 1] (mod ?q) \<or> [c ^ p = - 1] (mod ?q)\<close> by blast


  have \<open>?q dvd a\<close>
  proof (rule ccontr)
    have cong_add_here : \<open>[b ^ p = n1] (mod ?q) \<Longrightarrow> [c ^ p = n2] (mod ?q) \<Longrightarrow> [a ^ p = n3] (mod ?q) \<Longrightarrow>
                          [b ^ p + c ^ p - a ^ p = n1 + n2 - n3] (mod ?q)\<close> for n1 n2 n3
      by (intro cong_add cong_diff)
    assume \<open>\<not> ?q dvd a\<close>
    with SG_simps.p_th_power_mod_q[OF \<open>SG p\<close>]
    have cong3 : \<open>[a ^ p = 1] (mod ?q) \<or> [a ^ p = - 1] (mod ?q)\<close> by blast
    from cong1 cong2 cong3 cong_add_here
    have \<open>  [b ^ p + c ^ p - a ^ p = - 3] (mod ?q) \<or> [b ^ p + c ^ p - a ^ p = - 1] (mod ?q)
          \<or> [b ^ p + c ^ p - a ^ p = 1] (mod ?q) \<or> [b ^ p + c ^ p - a ^ p = 3] (mod ?q)\<close> (is ?disj_congs)
      by (elim disjE) fastforce+ (* eight cases *)
    have \<open>b ^ p + c ^ p - a ^ p = 2 * x\<close> by (fold a_prop b_prop c_prop) simp
    also from \<open>?q dvd x\<close> cong_0_iff have \<open>[2 * x = 0] (mod ?q)\<close>
      by (metis dvd_add_right_iff mult_2)
    finally have \<open>[b ^ p + c ^ p - a ^ p = 0] (mod ?q)\<close> .
    with \<open>?disj_congs\<close> show False by (metis cong_def SG_simps.notcong_zero[OF \<open>SG p\<close>])
  qed
  with oddE \<open>odd p\<close> have \<open>?q dvd a ^ p\<close> by fastforce
  with a_prop have \<open>[y = z] (mod ?q)\<close> by (simp add: cong_iff_dvd_diff)
  with cong_sym have \<open>[z = y] (mod ?q)\<close> by blast


\<comment> \<open>It is now time to conclude the proof!\<close>
  have \<open>\<alpha> ^ p = ?S y (-z)\<close> by (fact \<alpha>_prop[symmetric])
  also from SG_simps.nonzero[OF \<open>SG p\<close>] \<open>[z = y] (mod ?q)\<close> cong_minus_minus_iff
  have \<open>[?S y (-z) = p * y ^ (p - 1)] (mod ?q)\<close>
    by (blast intro: Sophie_Germain_lemma_computation_cong_simp)
  finally have \<open>[\<alpha> ^ p = p * y ^ (p - 1)] (mod ?q)\<close> .

  from SG_simps.p_th_power_mod_q[OF \<open>SG p\<close> \<open>\<not> ?q dvd c ^ p\<close>] \<open>[c ^ p = y] (mod ?q)\<close>
  have \<open>[y = 1] (mod ?q) \<or> [y = - 1] (mod ?q)\<close> by (metis cong2 cong_def)
  hence \<open>[y ^ (p - 1) = 1] (mod ?q)\<close>
    by (elim disjE) (drule cong_pow[where n = \<open>p - 1\<close>], simp add: \<open>odd p\<close>)+
  from cong_trans[OF \<open>[\<alpha> ^ p = p * y ^ (p - 1)] (mod ?q)\<close> cong_mult[OF cong_refl this]]
  have \<open>[\<alpha> ^ p = p] (mod ?q)\<close> by simp

\<comment> \<open>But \<^term>\<open>\<alpha> ^ p\<close> is congruent to \<^term>\<open>- 1 :: int\<close>, \<^term>\<open>0 :: int\<close> or \<^term>\<open>1 :: int\<close>
      modulo \<^term>\<open>?q\<close>, whereas \<^term>\<open>p\<close> can not be; hence the final contradiction.\<close>
  moreover from SG_simps.p_th_power_mod_q[OF \<open>SG p\<close>]
  have \<open>[\<alpha> ^ p = - 1] (mod ?q) \<or> [\<alpha> ^ p = 0] (mod ?q) \<or> [\<alpha> ^ p = 1] (mod ?q)\<close>
    by (metis cong_0_iff cong_pow power_0_left)
  ultimately show False by (metis SG_simps.notcong_p[OF \<open>SG p\<close>] cong_def)
qed




(*<*)
end
  (*>*)