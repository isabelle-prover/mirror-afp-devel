subsection \<open> Legendre's Polygonal Number Theorem \<close>
text\<open>We will use the definition of the polygonal numbers from the Gauss Theorem theory file
which also imports the Three Squares Theorem AFP entry \cite{Three_Squares-AFP}.\<close>

theory Polygonal_Number_Theorem_Legendre
  imports Polygonal_Number_Theorem_Gauss
begin

text \<open>This lemma shows that under certain conditions, an integer $N$ can be written as the sum of four polygonal numbers.\<close>

lemma sum_of_four_polygonal_numbers:
  fixes N m :: nat
  fixes b :: int
  assumes "m \<ge> 3"
  assumes "N \<ge> 2*m"
  assumes "[N = b] (mod m)"
  assumes odd_b: "odd b"
  assumes "b \<in> {1/2 + sqrt (6*N/m - 3) .. 2/3 + sqrt (8*N/m - 8)}"
  assumes "N \<ge> 9"
  shows "\<exists>k1 k2 k3 k4. N = polygonal_number m k1 + polygonal_number m k2 + polygonal_number m k3 + polygonal_number m k4"

proof -
  define I where "I = {1/2 + sqrt (6*N/m - 3) .. 2/3 + sqrt (8*N/m - 8)}"
  from assms(5) I_def have "b \<in> I" by auto
  define a::int where a_def: "a = 2*(N-b) div m + b"
  have "m dvd (N-b)" using assms(3)
    by (smt (verit, ccfv_threshold) cong_iff_dvd_diff zdvd_zdiffD)
  hence "even (2*(N-b) div m)"
    by (metis div_mult_swap dvd_triv_left)
  hence "odd a" using a_def assms(3) odd_b by auto
  from assms(1) have "m^3 \<ge> m"
    by (simp add: power3_eq_cube)
  hence "N \<ge> 2 * m" using assms(1,2) by simp
  from assms(1) have m_pos: "m > 0" by auto
  have "N \<ge> b"
  proof -
    from assms(1) have "m \<ge> 1" by auto
    hence "1/m \<le> 1" using m_pos by auto
    moreover have "N > 0" using \<open>N \<ge> 2 * m\<close> m_pos by auto
    ultimately have "N/m \<le> N"
      using divide_less_eq_1 less_eq_real_def by fastforce
    hence "sqrt(8*N/m - 8) \<le> sqrt(8*(N-1))" by auto
    from assms(1) have "m^3 \<ge> 3*3*(3::real)"
      by (metis numeral_le_real_of_nat_iff numeral_times_numeral power3_eq_cube power_mono zero_le_numeral)
    from \<open>N \<ge> 9\<close> have "N-1 \<ge> 8" by auto
    hence "(N-1)^2 \<ge> 8*(N-1)" using \<open>N > 0\<close> by (simp add: power2_eq_square)
    hence "(N-1) \<ge> sqrt (8*(N-1))" using \<open>N > 0\<close>
      by (metis of_nat_0_le_iff of_nat_mono of_nat_power real_sqrt_le_mono real_sqrt_pow2 real_sqrt_power)
    hence "N - (1::real) - sqrt(8*N/m - 8) \<ge> 0"
      using \<open>sqrt (real (8 * N) / real m - 8) \<le> sqrt (real (8 * (N - 1)))\<close> \<open>9 \<le> N\<close> by linarith
    hence expr_pos: "N - (2/3::real) - sqrt(8*N/m - 8) \<ge> 0" by auto
    have "b \<le> 2/3 + sqrt(8*N/m - 8)" using \<open>b \<in> I\<close> I_def by auto
    hence "N - b \<ge> N - (2/3 + sqrt(8*N/m-8))" by auto
    hence "N - b \<ge> 0"
      using expr_pos of_int_0_le_iff by auto
    thus ?thesis by auto
  qed
  from \<open>N \<ge> 2 * m\<close> m_pos have "6*N/m - 3 \<ge> 0" by (simp add: mult_imp_le_div_pos)
  hence "1/2 + sqrt (6*N/m - 3) > 0"
    by (smt (verit, del_insts) divide_le_0_1_iff real_sqrt_ge_zero)
  with \<open>b \<in> I\<close> assms(3) I_def have "b \<ge> 1" by auto
  hence b_pos: "b \<ge> 0" by auto
  from \<open>b \<in> I\<close> have b_in_I: "(1/2::real) + sqrt (6* real N / real m - 3) \<le> b \<and> b \<le> (2/3::real) + sqrt (8 * real N/real m - 8)" unfolding I_def by auto
  from b_pos \<open>N \<ge> b\<close> a_def have a_pos: "a \<ge> 0"
    by (smt (verit) m_pos of_nat_0_less_iff pos_imp_zdiv_neg_iff)
  hence "a \<ge> 1"
    by (smt (verit) \<open>odd a\<close> dvd_0_right)
  have "a - b = 2*(N-b) div m" using a_def by auto
  from \<open>int m dvd (int N - b)\<close> have "m dvd 2*(N-b)" by fastforce
  have "a = 2*(N-b)/m + b" using a_def m_pos
    using \<open>int m dvd 2 * (int N - b)\<close> by fastforce
  hence "a = 2*N/m - 2*b/m + b"
    by (simp add: assms diff_divide_distrib of_nat_diff)
  hence "(2::real)*N/m = a + 2*b/m - b" by auto
  hence "(2::real)*N = (a + 2*b/m - b)*m"
    using m_pos by (simp add: divide_eq_eq)
  hence "(2::real)*N = m*(a-b) + 2*b"
    using \<open>int m dvd 2 * (int N - b)\<close> a_def by auto
  hence "N = m*(a-b)/2 + b" by auto
  hence N_expr: "real N = real m * (of_int a - of_int b) / 2 + of_int b" by auto
  have "even (a-b)" using \<open>odd a\<close> \<open>odd b\<close> by auto
  hence "2 dvd m*(a-b)" by auto
  hence N_expr2: "N = m*(a-b) div 2 + b" using \<open>N = m*(a-b)/2 + b\<close> by linarith
  define Nr where "Nr = real_of_nat N"
  define mr where "mr = real m"
  define ar where "ar = real_of_int a"
  define br where "br = real_of_int b"
  from assms(1) have "mr \<ge> 3" using mr_def by auto
  moreover have "Nr \<ge> 2*mr" using Nr_def mr_def \<open>N \<ge> 2 * m\<close> by auto
  moreover have "br \<ge> 0" using br_def b_pos by auto
  moreover have "mr > 0" using mr_def m_pos by auto
  moreover have "ar \<ge> 0" using ar_def \<open>a \<ge> 0\<close> by auto
  moreover have "Nr = mr*(ar-br)/2 + br" using Nr_def mr_def ar_def br_def N_expr by auto
  moreover have "1/2 + sqrt (6*Nr/mr-3) \<le> br \<and> br \<le> 2/3 + sqrt (8*Nr/mr-8)" using Nr_def mr_def br_def b_in_I by auto
  ultimately have "br^2 < 4*ar \<and> 3*ar < br^2+2*br+4" using Cauchy_lemma_r_eq_zero
    by auto
  hence real_ineq:"(real_of_int b)^2 < 4*(real_of_int a) \<and> 3*(real_of_int a) < (real_of_int b)^2 + 2*(real_of_int b) + 4"
    using br_def ar_def by auto
  hence int_ineq1: "b^2<4*a" using of_int_less_iff by fastforce
  from real_ineq have int_ineq2: "3*a < b^2+2*b+4" using of_int_less_iff by fastforce

  define an:: nat where "an = nat a"
  from a_pos have "an = a" unfolding an_def by auto
  define bn:: nat where "bn = nat b"
  from b_pos have "bn = b" unfolding bn_def by auto
  have "an \<ge> 1" using \<open>int an = a\<close> \<open>a \<ge> 1\<close> by auto
  moreover have "bn \<ge> 1" using \<open>int bn = b\<close> \<open>b \<ge> 1\<close> by auto
  moreover have "odd an" using \<open>odd a\<close> \<open>int an = a\<close> by auto
  moreover have "odd bn" using \<open>odd b\<close> \<open>int bn = b\<close> by auto
  moreover have "bn ^ 2 < 4 * an" using int_ineq1 \<open>int an = a\<close> \<open>int bn = b\<close>
    using of_nat_less_iff by fastforce
  moreover have "3 * an < bn ^ 2 + 2 * bn + 4" using int_ineq2 \<open>int an = a\<close> \<open>int bn = b\<close>
    using of_nat_less_iff by fastforce
  ultimately have "\<exists>s t u v :: int. s \<ge> 0 \<and> t \<ge> 0 \<and> u \<ge> 0 \<and> v \<ge> 0 \<and> an = s^2 + t^2 + u^2 + v^2 \<and>
bn = s+t+u+v" using four_nonneg_int_sum by auto
  hence "\<exists>s t u v :: int. s \<ge> 0 \<and> t \<ge> 0 \<and> u \<ge> 0 \<and> v \<ge> 0 \<and> a = s^2 + t^2 + u^2 + v^2 \<and>
b = s+t+u+v" using \<open>int an = a\<close> \<open>int bn = b\<close> by auto
  then obtain s t u v :: int where stuv: "s \<ge> 0 \<and> t \<ge> 0 \<and> u \<ge> 0 \<and> v \<ge> 0 \<and> a = s^2 + t^2 + u^2 + v^2 \<and>
b = s+t+u+v" by auto
  hence "N = (m*(s^2+t^2+u^2+v^2-s-t-u-v) div 2) + s+t+u+v" using N_expr2 by (smt (verit, ccfv_threshold))
  hence "N = (m*(s^2-s+t^2-t+u^2-u+v^2-v) div 2) + s+t+u+v" by (smt (verit, ccfv_SIG))
  hence "N = (m * (s * (s-1) + t * (t-1) + u * (u-1) + v * (v-1)) div 2) +s+t+u+v" by (simp add: power2_eq_square algebra_simps)
  hence previous_step: "N = (m * s * (s-1) + m * t * (t-1) + m * u * (u-1) + m * v * (v-1)) div 2 + s+t+u+v" by (simp add: algebra_simps)
  moreover have "2 dvd m * s * (s-1)" by simp
  moreover have "2 dvd m * t * (t-1)" by simp
  moreover have "2 dvd m * u * (u-1)" by simp
  moreover have "2 dvd m * v * (v-1)" by simp
  ultimately have "N = m * s * (s-1) div 2 + m * t * (t-1) div 2 + m * u * (u-1) div 2 + m * v *(v-1) div 2 + s+t+u+v" by fastforce
  hence N_expr3: "N = m * s * (s-1) div 2 + s + m * t * (t-1) div 2 + t + m * u * (u-1) div 2 + u + m * v * (v-1) div 2 + v" by auto
  define sn::nat where "sn = nat s"
  define tn::nat where "tn = nat t"
  define un::nat where "un = nat u"
  define vn::nat where "vn = nat v"
  have "sn = s" using stuv sn_def by auto
  hence "m * sn * (sn-1) = m * s * (s-1)" by fastforce
  hence "m * sn * (sn-1) div 2 = m * s * (s-1) div 2" by linarith
  have "tn = t" using stuv tn_def by auto
  hence "m * tn * (tn-1) = m * t * (t-1)" by fastforce
  hence "m * tn * (tn-1) div 2 = m * t * (t-1) div 2" by linarith
  have "un = u" using stuv un_def by auto
  hence "m * un * (un-1) = m * u * (u-1)" by fastforce
  hence "m * un * (un-1) div 2 = m * u * (u-1) div 2" by linarith
  have "vn = v" using stuv vn_def by auto
  hence "m * vn * (vn-1) = m * v * (v-1)" by fastforce
  hence "m * vn * (vn-1) div 2 = m * v * (v-1) div 2" by linarith
  have "N = m * sn * (sn-1) div 2 + sn + m * tn * (tn-1) div 2 + tn + m * un * (un-1) div 2 + un + m * vn * (vn-1) div 2 + vn"
    using N_expr3 \<open>sn = s\<close> \<open>tn = t\<close> \<open>un = u\<close> \<open>vn = v\<close> \<open>m * sn * (sn-1) div 2 = m * s * (s-1) div 2\<close> \<open>m * tn * (tn-1) div 2 = m * t * (t-1) div 2\<close> \<open>m * un * (un-1) div 2 = m * u * (u-1) div 2\<close> \<open>m * vn * (vn-1) div 2 = m * v * (v-1) div 2\<close> by linarith
  hence "N = polygonal_number m sn + polygonal_number m tn + polygonal_number m un + polygonal_number m vn"
    using Polygonal_Number_Theorem_Gauss.polygonal_number_def by presburger
  thus ?thesis by blast
qed

text \<open>We show Legendre's polygonal number theorem which corresponds to Theorem 1.10 in \cite{nathanson1996}.\<close>

theorem Legendre_Polygonal_Number_Theorem:
  fixes m N :: nat
  assumes "m \<ge> 3"
  assumes "N \<ge> 28*m^3"
  shows "odd m \<Longrightarrow> \<exists>k1 k2 k3 k4::nat. N = polygonal_number m k1 + polygonal_number m k2 + polygonal_number m k3 + polygonal_number m k4"
and "even m \<Longrightarrow> \<exists>k1 k2 k3 k4 k5::nat. N = polygonal_number m k1 + polygonal_number m k2 + polygonal_number m k3 + polygonal_number m k4 + polygonal_number m k5 \<and> (k1 = 0 \<or> k1 = 1 \<or> k2 = 0 \<or> k2 = 1 \<or> k3 = 0 \<or> k3 = 1 \<or> k4 = 0 \<or> k4 = 1 \<or> k5 = 0 \<or> k5 = 1)"

proof -
  define L :: real where "L = (2/3 + sqrt (8*N/m - 8)) - (1/2 + sqrt (6*N/m - 3))"
  define I where "I = {1/2 + sqrt (6*N/m - 3) .. 2/3 + sqrt (8*N/m - 8)}"
  from assms(1) have "m^3 \<ge> m"
    by (simp add: power3_eq_cube)
  hence "N \<ge> 2 * m" using assms by simp
  have m_pos: "m > 0" using assms(1) by simp
  have "L > 2 * of_nat m" using assms \<open>N \<ge> 2 * m\<close> m_pos L_def
    apply -
    apply (rule interval_length_greater_than_2m[where N="of_nat N" and m="of_nat m"])
       apply (simp_all)
    by (metis (no_types, opaque_lifting) of_nat_le_iff of_nat_mult of_nat_numeral power3_eq_cube)
  hence 2: "L > 2 * m" by simp
  show thm_odd_m: "odd m \<Longrightarrow> \<exists>k1 k2 k3 k4. N = polygonal_number m k1 + polygonal_number m k2 + polygonal_number m k3 + polygonal_number m k4"
  proof -
    assume odd_m: "odd m"
    from assms(1) have "m > 0" by auto
    define ce where "ce = \<lceil>1/2 + sqrt (6*N/m - 3)\<rceil>"
    have "\<forall> i\<in>{0..2*m-1}. ce + i \<ge> ce" by auto
    hence lower_bound: "\<forall> i\<in>{0..2*m-1}. ce + i \<ge> 1/2 + sqrt (6*N/m - 3)" using ceiling_le_iff ce_def by blast
    have "2*m-1 + ce \<le> 2/3 + sqrt (8*N/m - 8)" using 2 L_def assms(1) ce_def by linarith
    hence upper_bound: "\<forall> i\<in>{0..2*m-1}. ce + i \<le>  2/3 + sqrt (8*N/m - 8)" by auto
    from lower_bound upper_bound have in_interval: "\<forall> i\<in>{0..2*m-1}. ce + i \<in> I" unfolding ce_def I_def by auto
    have "\<exists> f::nat \<Rightarrow> int. (\<forall> i\<in>{0..m-1}. odd (f i)) \<and> (\<forall> i\<in>{1..m-1}. f i = f 0 + 2*i) \<and> (\<forall> i\<in>{0..m-1}. f i \<in> I)"
    proof -
      have ?thesis if odd_f0: "odd ce"
      proof -
        define g::"nat \<Rightarrow> int" where "g i = ce + 2*i"
        have "odd (g 0)" using odd_f0 \<open>g \<equiv> \<lambda>i. ce + int (2 * i)\<close> by auto
        hence "\<forall> i\<in>{0..m-1}. odd (g i)" using \<open>g \<equiv> \<lambda>i. ce + int (2 * i)\<close> by auto
        have "\<forall> i\<in>{1..m-1}. g i = g 0 + 2*i" using \<open>g \<equiv> \<lambda>i. ce + int (2 * i)\<close> by auto
        have "\<forall> i\<in>{0..m-1}. 2*i < 2*m-1" using m_pos by auto
        hence "\<forall> i\<in>{0..m-1}. g i \<in> I" using \<open>g \<equiv> \<lambda>i. ce + int (2 * i)\<close> in_interval by fastforce
        show ?thesis using \<open>\<forall>i\<in>{0..m - 1}. odd (g i)\<close> \<open>\<forall>i\<in>{0..m - 1}. real_of_int (g i) \<in> I\<close> \<open>\<forall>i\<in>{1..m - 1}. g i = g 0 + int(2 * i)\<close> by blast
      qed
      moreover have ?thesis if "even ce"
      proof -
        from \<open>even ce\<close> have odd_f1: "odd (ce + 1)" by auto
        define g::"nat \<Rightarrow> int" where "g i = ce + (2*i + 1)"
        have "odd (g 0)" using odd_f1 \<open>g \<equiv> \<lambda>i. ce + int (2 * i + 1)\<close> by auto
        hence "\<forall> i\<in>{0..m-1}. odd (g i)" using \<open>g \<equiv> \<lambda>i. ce + int (2 * i + 1)\<close> by auto
        have "\<forall> i\<in>{1..m-1}. g i = g 0 + 2*i" using \<open>g \<equiv> \<lambda>i. ce + int (2 * i + 1)\<close> by auto
        have "\<forall> i\<in>{0..m-1}. 2*i + 1 \<le> 2*m-1" using m_pos by auto
        hence "\<forall> i\<in>{0..m-1}. g i \<in> I" using \<open>g \<equiv> \<lambda>i. ce + int (2 * i + 1)\<close> in_interval by fastforce
        show ?thesis using \<open>\<forall>i\<in>{0..m - 1}. odd (g i)\<close> \<open>\<forall>i\<in>{0..m - 1}. real_of_int (g i) \<in> I\<close> \<open>\<forall>i\<in>{1..m - 1}. g i = g 0 + int(2 *i)\<close> by blast
      qed
      ultimately show ?thesis by blast
    qed
    then obtain f::"nat \<Rightarrow> int" where f_def: "(\<forall> i\<in>{0..m-1}. odd (f i)) \<and> (\<forall> i\<in>{1..m-1}. f i = f 0 + 2*i) \<and> (\<forall> i\<in>{0..m-1}. f i \<in> I)" by auto

    have inj_lemma: "\<lbrakk>i \<in> {0..m-1}; j \<in> {0..m-1}; [f i = f j] (mod m)\<rbrakk> \<Longrightarrow> i = j" for i j
    proof -
      assume asm1: "i \<in> {0..m-1}"
      assume asm2: "j \<in> {0..m-1}"
      assume asm3: "[f i = f j] (mod m)"
      from f_def have "odd (f 0)" by auto
      hence "\<exists> k::int. f 0 = 2*k + 1" by (metis oddE)
      then obtain k::int where k_def: "f 0 = 2*k + 1" by auto
      have False if case2: "i = 0 \<and> j > 0"
      proof -
        have "f j = f 0 + 2*j" using f_def case2 asm2 by auto
        hence "[2*k + 1 = 2*k + 1 + 2*j] (mod m)" using asm3 case2 k_def by auto
        hence "[2*j = 0] (mod m)"
          by (metis cong_add_lcancel_0 cong_int_iff cong_sym_eq int_ops(1))
        have "coprime 2 m" using odd_m by simp
        hence "[j = 0] (mod m)" using \<open>[2*j = 0] (mod m)\<close> by (simp add: cong_0_iff coprime_dvd_mult_right_iff)
        thus False using asm2 case2 cong_less_modulus_unique_nat by fastforce
      qed
      moreover have False if case3: "i > 0 \<and> j = 0"
      proof -
        have "f i = f 0 + 2*i" using f_def case3 asm1 by auto
        hence "[2*k + 1 + 2*i = 2*k + 1] (mod m)" using asm3 case3 k_def by auto
        hence "[2*i = 0] (mod m)"
          by (metis cong_add_lcancel_0 cong_int_iff cong_sym_eq int_ops(1))
        have "coprime 2 m" using odd_m by simp
        hence "[i = 0] (mod m)" using \<open>[2*i = 0] (mod m)\<close> by (simp add: cong_0_iff coprime_dvd_mult_right_iff)
        thus False using asm1 case3 cong_less_modulus_unique_nat by fastforce
      qed
      moreover have ?thesis if case4: "i > 0 \<and> j > 0"
      proof -
        have "i > 0" and "j > 0" using case4 by auto
        have "f i = f 0 + 2*i" using f_def case4 asm1 by auto
        moreover have "f j = f 0 + 2*j" using f_def case4 asm2 by auto
        ultimately have "[2*k + 1 + 2*i = 2*k + 1 + 2*j] (mod m)" using case4 k_def asm3 by fastforce
        hence "[2*i = 2*j] (mod m)"
          using cong_add_lcancel cong_int_iff by blast
        have "coprime 2 m" using odd_m by simp
        hence "[i = j] (mod m)"
          using \<open>[2 * i = 2 * j] (mod m)\<close> cong_mult_lcancel_nat by auto
        thus ?thesis using asm1 asm2 case4 cong_less_modulus_unique_nat by auto
      qed
      ultimately show ?thesis by fastforce
    qed
    have complete_cong_class: "\<exists>i \<in> {0..m-1}. [f i = S] (mod m)" for S
    proof -
      have "(f i) mod m = (f j) mod m \<Longrightarrow> [f i = f j] (mod m)" for i j
        by (simp add: unique_euclidean_semiring_class.cong_def)
      hence inj2: "\<lbrakk>i \<in> {0..m-1}; j \<in> {0..m-1}; (f i) mod m = (f j) mod m\<rbrakk> \<Longrightarrow> i = j" for i j
        using inj_lemma by auto
      hence injective: "\<forall>i \<in> {0..m-1}. \<forall>j \<in> {0..m-1}. (f i) mod m = (f j) mod m \<longrightarrow> i = j"
        by auto
      define g :: "nat \<Rightarrow> int" where "g i = (f i) mod m"
      then have g_inj2: "\<forall>i \<in> {0..m-1}. \<forall> j \<in> {0..m-1}. g i = g j \<longrightarrow> i = j"
        using \<open>g \<equiv> \<lambda>i. f i mod int m\<close> injective  by fastforce
      then have g_inj: "inj_on g {0..m-1}"
        by (meson inj_onI)
      have g_range2: "\<forall> i \<in> {0..m-1}. g i \<in> {0..m-1}" using \<open>g \<equiv> \<lambda>i. f i mod int m\<close>
        by (metis m_pos Euclidean_Rings.pos_mod_bound Euclidean_Rings.pos_mod_sign atLeastAtMost_iff mod_by_1 mod_if not_gr0 of_nat_0_less_iff of_nat_1 of_nat_diff verit_comp_simplify1(3) zle_diff1_eq)
      hence image_subset: "g ` {0..m-1} \<subseteq> {0..m-1}" by blast
      have g_range: "i \<in> {0..m-1} \<Longrightarrow> g i \<in> {0..m-1}" using \<open>g \<equiv> \<lambda>i. f i mod int m\<close>
        by (metis m_pos Euclidean_Rings.pos_mod_bound Euclidean_Rings.pos_mod_sign atLeastAtMost_iff mod_by_1 mod_if not_gr0 of_nat_0_less_iff of_nat_1 of_nat_diff verit_comp_simplify1(3) zle_diff1_eq)
      have card_ge_m: "card (g ` {0..m-1}) \<ge> m" using g_inj
        by (metis m_pos Suc_diff_1 card_atLeastAtMost card_image minus_nat.diff_0 verit_comp_simplify1(2))
      have "card {0..m-1} = m" using m_pos by force
      hence card_le_m: "card (g ` {0..m-1}) \<le> m" using m_pos
        by (metis card_image g_inj le_refl)
      from card_ge_m card_le_m have image_size: "card (g ` {0..m-1}) = m" by auto
      with \<open>card {0..m-1} = m\<close> have equal_card: "card (g ` {0..m-1}) = card {0..m-1}" by auto
      have "finite (g ` {0..m-1})" using image_size by auto
      with equal_card image_subset have "g ` {0..m-1} = {0..m-1}"
        by (metis card_image card_subset_eq finite_atLeastAtMost_int image_int_atLeastAtMost inj_on_of_nat of_nat_0)
      hence "i \<in> {0..m-1} \<Longrightarrow> \<exists> j \<in> {0..m-1}. i = g j" for i by auto
      hence "i \<in> {0..m-1} \<Longrightarrow> \<exists> j \<in> {0..m-1}. i = (f j) mod m" for i
        using \<open>g \<equiv> \<lambda>i. f i mod int m\<close> by auto
      hence surj: "i \<in> {0..m-1} \<Longrightarrow> \<exists> j \<in> {0..m-1}. [i = f j] (mod m)" for i
        by (metis mod_mod_trivial unique_euclidean_semiring_class.cong_def)
      have "S mod m \<ge> 0" using m_pos by simp
      moreover have "S mod m \<le> m-1"
        using m_pos by (simp add: of_nat_diff)
      ultimately have "S mod m \<in> {0..m-1}" by auto
      with surj m_pos have "\<exists> j \<in> {0..m-1}. [S mod m = f j] (mod m)"
        by (metis atLeastAtMost_iff less_eq_nat.simps(1) nonneg_int_cases of_nat_less_iff verit_comp_simplify(3))
      thus ?thesis using cong_mod_right cong_sym by blast
    qed
    have "\<exists> b::int. [N = b] (mod m) \<and> odd b \<and> b \<in> I"
    proof -
      have "N mod m \<ge> 0" by auto
      moreover have "N mod m \<le> m-1"
        using m_pos less_Suc_eq_le by fastforce
      ultimately have "N mod m \<in> {0..m-1}" by auto
      with complete_cong_class have "\<exists> i. i \<in> {0..m-1} \<and> [f i = N] (mod m)" by blast
      then obtain c::nat where c_def: "c \<in> {0..m-1} \<and> [f c = N] (mod m)" by auto
      define b::int where "b = f c"
      have "[N = b] (mod m)" using b_def c_def by (metis cong_sym)
      moreover have "odd b" using b_def f_def c_def by auto
      moreover have "b \<in> I" using b_def f_def c_def by auto
      ultimately show ?thesis by auto
    qed
    then obtain b::int where b_def: "[N = b] (mod m) \<and> odd b \<and> b \<in> I" by auto
    have "m^3 \<ge> m" using m_pos by (auto simp add: power3_eq_cube)
    hence "N \<ge> 28*m" using assms(1,2) by linarith
    hence "N \<ge> 2*m" by simp
    have "m^3 \<ge> 3*3*(3::nat)" using assms(1)
      by (metis power3_eq_cube power_mono zero_le_numeral)
    hence "N \<ge> 28*3*3*(3::nat)" using assms(2) by auto
    hence "N \<ge> 9" by simp
    show ?thesis using sum_of_four_polygonal_numbers assms(1) b_def I_def \<open>N \<ge> 2 * m\<close> \<open>N \<ge> 9\<close> by blast
  qed
  show thm_even_m: "even m \<Longrightarrow> \<exists>k1 k2 k3 k4 k5. N = polygonal_number m k1 + polygonal_number m k2 + polygonal_number m k3 + polygonal_number m k4 + polygonal_number m k5 \<and> (k1 = 0 \<or> k1 = 1 \<or> k2 = 0 \<or> k2 = 1 \<or> k3 = 0 \<or> k3 = 1 \<or> k4 = 0 \<or> k4 = 1 \<or> k5 = 0 \<or> k5 = 1)"
  proof -
    assume even_m: "even m"
    from assms(1) have "m > 0" by auto
    define ce where "ce = \<lceil>1/2 + sqrt (6*N/m - 3)\<rceil>"
    have "\<forall> i\<in>{0..m-1}. ce + i \<ge> ce" by auto
    hence lower_bound: "\<forall> i\<in>{0..m-1}. ce + i \<ge> 1/2 + sqrt (6*N/m - 3)" using ceiling_le_iff ce_def by blast
    have "m-1 + ce \<le> 2/3 + sqrt (8*N/m - 8)" using 2 L_def assms(1) ce_def by linarith
    hence upper_bound: "\<forall> i\<in>{0..m-1}. ce + i \<le>  2/3 + sqrt (8*N/m - 8)" by auto
    from lower_bound upper_bound have in_interval: "\<forall> i\<in>{0..m-1}. ce + i \<in> I" unfolding ce_def I_def by auto
    have "\<exists> f::nat \<Rightarrow> int. (\<forall> i\<in>{1..m-1}. f i = f 0 + i) \<and> (\<forall> i\<in>{0..m-1}. f i \<in> I)"
    proof -
      define g::"nat \<Rightarrow> int" where "g i = ce + i"
      have "\<forall> i\<in>{1..m-1}. g i = g 0 + i" using \<open>g \<equiv> \<lambda>i. ce + int i\<close> by auto
      have "\<forall> i\<in>{0..m-1}. i < m" using m_pos by auto
      hence "\<forall> i\<in>{0..m-1}. g i \<in> I" using \<open>g \<equiv> \<lambda>i. ce + int i\<close> in_interval by fastforce
      show ?thesis by (metis Num.of_nat_simps(1) \<open>\<forall>i\<in>{0..m - 1}. real_of_int (g i) \<in> I\<close> \<open>g \<equiv> \<lambda>i. ce + int i\<close> arith_extra_simps(6))
    qed
    then obtain f::"nat \<Rightarrow> int" where f_def: "(\<forall> i\<in>{1..m-1}. f i = f 0 + i) \<and> (\<forall> i\<in>{0..m-1}. f i \<in> I)" by auto
    have inj_lemma: "\<lbrakk>i \<in> {0..m-1}; j \<in> {0..m-1}; [f i = f j] (mod m)\<rbrakk> \<Longrightarrow> i = j" for i j
    proof -
      assume asm1: "i \<in> {0..m-1}"
      assume asm2: "j \<in> {0..m-1}"
      assume asm3: "[f i = f j] (mod m)"
      have False if case2: "i = 0 \<and> j > 0"
      proof -
        have "f j = f 0 + j" using f_def case2 asm2 by auto
        hence "[f 0  = f 0 + j] (mod m)" using asm3 case2 by auto
        hence "[j = 0] (mod m)"
          by (metis cong_add_lcancel_0 cong_int_iff cong_sym_eq int_ops(1))
        thus False using asm2 case2 cong_less_modulus_unique_nat by fastforce
      qed
      moreover have False if case3: "i > 0 \<and> j = 0"
      proof -
        have "f i = f 0 + i" using f_def case3 asm1 by auto
        hence "[f 0 + i = f 0] (mod m)" using asm3 case3 by auto
        hence "[i = 0] (mod m)"
          by (metis cong_add_lcancel_0 cong_int_iff cong_sym_eq int_ops(1))
        thus False using asm1 case3 cong_less_modulus_unique_nat by fastforce
      qed
      moreover have ?thesis if case4: "i > 0 \<and> j > 0"
      proof -
        have "i > 0" and "j > 0" using case4 by auto
        have "f i = f 0 + i" using f_def case4 asm1 by auto
        moreover have "f j = f 0 + j" using f_def case4 asm2 by auto
        ultimately have "[f 0 + i = f 0 + j] (mod m)" using case4 asm3 by fastforce
        hence "[i = j] (mod m)"
          using cong_add_lcancel cong_int_iff by blast
        thus ?thesis using asm1 asm2 case4 cong_less_modulus_unique_nat by auto
      qed
      ultimately show ?thesis by fastforce
    qed
    have complete_cong_class: "\<exists>i \<in> {0..m-1}. [f i = S] (mod m)" for S
    proof -
      have "(f i) mod m = (f j) mod m \<Longrightarrow> [f i = f j] (mod m)" for i j
        by (simp add: unique_euclidean_semiring_class.cong_def)
      hence inj2: "\<lbrakk>i \<in> {0..m-1}; j \<in> {0..m-1}; (f i) mod m = (f j) mod m\<rbrakk> \<Longrightarrow> i = j" for i j
        using inj_lemma by auto
      hence injective: "\<forall>i \<in> {0..m-1}. \<forall>j \<in> {0..m-1}. (f i) mod m = (f j) mod m \<longrightarrow> i = j"
        by auto
      define g :: "nat \<Rightarrow> int" where "g i = (f i) mod m"
      then have g_inj2: "\<forall>i \<in> {0..m-1}. \<forall> j \<in> {0..m-1}. g i = g j \<longrightarrow> i = j"
        using \<open>g \<equiv> \<lambda>i. f i mod int m\<close> injective  by fastforce
      then have g_inj: "inj_on g {0..m-1}"
        by (meson inj_onI)
      have g_range2: "\<forall> i \<in> {0..m-1}. g i \<in> {0..m-1}" using \<open>g \<equiv> \<lambda>i. f i mod int m\<close>
        by (metis m_pos Euclidean_Rings.pos_mod_bound Euclidean_Rings.pos_mod_sign atLeastAtMost_iff mod_by_1 mod_if not_gr0 of_nat_0_less_iff of_nat_1 of_nat_diff verit_comp_simplify1(3) zle_diff1_eq)
      hence image_subset: "g ` {0..m-1} \<subseteq> {0..m-1}" by blast
      have g_range: "i \<in> {0..m-1} \<Longrightarrow> g i \<in> {0..m-1}" using \<open>g \<equiv> \<lambda>i. f i mod int m\<close>
        by (metis m_pos Euclidean_Rings.pos_mod_bound Euclidean_Rings.pos_mod_sign atLeastAtMost_iff mod_by_1 mod_if not_gr0 of_nat_0_less_iff of_nat_1 of_nat_diff verit_comp_simplify1(3) zle_diff1_eq)
      have card_ge_m: "card (g ` {0..m-1}) \<ge> m" using g_inj
        by (metis m_pos Suc_diff_1 card_atLeastAtMost card_image minus_nat.diff_0 verit_comp_simplify1(2))
      have "card {0..m-1} = m" using m_pos by force
      hence card_le_m: "card (g ` {0..m-1}) \<le> m" using m_pos
        by (metis card_image g_inj le_refl)
      from card_ge_m card_le_m have image_size: "card (g ` {0..m-1}) = m" by auto
      with \<open>card {0..m-1} = m\<close> have equal_card: "card (g ` {0..m-1}) = card {0..m-1}" by auto
      have "finite (g ` {0..m-1})" using image_size by auto
      with equal_card image_subset have "g ` {0..m-1} = {0..m-1}"
        by (metis card_image card_subset_eq finite_atLeastAtMost_int image_int_atLeastAtMost inj_on_of_nat of_nat_0)
      hence "i \<in> {0..m-1} \<Longrightarrow> \<exists> j \<in> {0..m-1}. i = g j" for i by auto
      hence "i \<in> {0..m-1} \<Longrightarrow> \<exists> j \<in> {0..m-1}. i = (f j) mod m" for i
        using \<open>g \<equiv> \<lambda>i. f i mod int m\<close> by auto
      hence surj: "i \<in> {0..m-1} \<Longrightarrow> \<exists> j \<in> {0..m-1}. [i = f j] (mod m)" for i
        by (metis mod_mod_trivial unique_euclidean_semiring_class.cong_def)
      have "S mod m \<ge> 0" using m_pos by simp
      moreover have "S mod m \<le> m-1"
        using m_pos by (simp add: of_nat_diff)
      ultimately have "S mod m \<in> {0..m-1}" by auto
      with surj m_pos have "\<exists> j \<in> {0..m-1}. [S mod m = f j] (mod m)"
        by (metis atLeastAtMost_iff less_eq_nat.simps(1) nonneg_int_cases of_nat_less_iff verit_comp_simplify(3))
      thus ?thesis using cong_mod_right cong_sym by blast
    qed
    have thm_odd_n: ?thesis if "odd N"
    proof -
      have "\<exists> b::int. [N = b] (mod m) \<and> odd b \<and> b \<in> I"
      proof -
        from complete_cong_class have "\<exists> i. i \<in> {0..m-1} \<and> [f i = N] (mod m)" by blast
        then obtain c::nat where c_def: "c \<in> {0..m-1} \<and> [f c = N] (mod m)" by auto
        define b::int where "b = f c"
        have "[N = b] (mod m)" using b_def c_def by (metis cong_sym)
        moreover have "odd b"
        proof
          assume "even b"
          have "\<exists>k::int. N = b + k*m" using \<open>[N = b] (mod m)\<close>
          by (metis cong_iff_lin cong_sym_eq mult.commute)
          then obtain k::int where k_def: "N = b + k*m" by auto
          have "even (k*m)" using even_m by auto
          hence "even N" using k_def \<open>even b\<close> by presburger
          thus False using \<open>odd N\<close> by blast
        qed
        moreover have "b \<in> I" using b_def f_def c_def by auto
        ultimately show ?thesis by auto
      qed
      then obtain b::int where b_def: "[N = b] (mod m) \<and> odd b \<and> b \<in> I" by auto
      have "m^3 \<ge> m" using m_pos by (auto simp add: power3_eq_cube)
      hence "N \<ge> 28*m" using assms(1,2) by linarith
      hence "N \<ge> 2*m" by simp
      have "m^3 \<ge> 3*3*(3::nat)" using assms(1)
        by (metis power3_eq_cube power_mono zero_le_numeral)
      hence "N \<ge> 28*3*3*(3::nat)" using assms(2) by auto
      hence "N \<ge> 9" by simp
      hence "\<exists>k1 k2 k3 k4. N = polygonal_number m k1 + polygonal_number m k2 + polygonal_number m k3 + polygonal_number m k4"
        using sum_of_four_polygonal_numbers assms(1) b_def I_def \<open>N \<ge> 2 * m\<close> \<open>N \<ge> 9\<close> by blast
      then obtain k1 k2 k3 k4 where "N = polygonal_number m k1 + polygonal_number m k2 + polygonal_number m k3 + polygonal_number m k4" by blast
      moreover have "polygonal_number m 0 = 0" using Polygonal_Number_Theorem_Gauss.polygonal_number_def by auto
      ultimately have "N = polygonal_number m k1 + polygonal_number m k2 + polygonal_number m k3 + polygonal_number m k4 + polygonal_number m 0" by linarith
      thus ?thesis by blast
    qed
    have thm_even_n: ?thesis if "even N"
    proof -
      have "\<exists> b::int. [N-1 = b] (mod m) \<and> odd b \<and> b \<in> I"
      proof -
        from complete_cong_class have "\<exists> i. i \<in> {0..m-1} \<and> [f i = N-1] (mod m)" by blast
        then obtain c::nat where c_def: "c \<in> {0..m-1} \<and> [f c = N-1] (mod m)" by auto
        define b::int where "b = f c"
        have "[N-1 = b] (mod m)" using b_def c_def by (metis cong_sym)
        moreover have "odd b"
        proof
          assume "even b"
          have "\<exists>k::int. N-1 = b + k*m" using \<open>[N-1 = b] (mod m)\<close>
          by (metis (full_types) cong_iff_lin cong_sym_eq mult.commute)
          then obtain k::int where k_def: "N-1 = b + k*m" by auto
          have "even (k*m)" using even_m by auto
          hence "even (N-1)" using k_def \<open>even b\<close> by presburger
          hence "odd N"
            by (metis Groups.mult_ac(2) \<open>2 * m \<le> N\<close> add_eq_self_zero add_leD1 assms(1) dvd_diffD1 le_trans mult_2_right nat_1_add_1 nat_dvd_1_iff_1 rel_simps(25) zero_neq_numeral)
          thus False using \<open>even N\<close> by blast
        qed
        moreover have "b \<in> I" using b_def f_def c_def by auto
        ultimately show ?thesis by auto
      qed
      then obtain b::int where b_def: "[N-1 = b] (mod m) \<and> odd b \<and> b \<in> I" by auto
      from b_def have "b \<in> I" by auto
      define a::int where a_def: "a = 2*(N-1-b) div m + b"
      have "m dvd (N-1-b)" using b_def
        by (smt (verit, ccfv_threshold) cong_iff_dvd_diff zdvd_zdiffD)
      hence "even (2*(N-1-b) div m)"
        by (metis div_mult_swap dvd_triv_left)
      hence "odd a" using a_def b_def by auto
      from assms(1) have "m^3 \<ge> m"
        by (simp add: power3_eq_cube)
      hence "N \<ge> 2 * m" using assms(1,2) by simp
      from assms(1) have m_pos: "m > 0" by auto
      have "N-1 \<ge> b"
      proof -
        from assms(1) have "m \<ge> 1" by auto
        hence "1/m \<le> 1" using m_pos by auto
        moreover have "N > 0" using \<open>N \<ge> 2 * m\<close> m_pos by auto
        ultimately have "N/m \<le> N"
          using divide_less_eq_1 less_eq_real_def by fastforce
        hence "sqrt(8*N/m - 8) \<le> sqrt(8*(N-1))" by auto
        from assms(1) have "m^3 \<ge> 3*3*(3::real)"
          by (metis numeral_le_real_of_nat_iff numeral_times_numeral power3_eq_cube power_mono zero_le_numeral)
        hence "N \<ge> 28*3*3*(3::real)" using assms(2) by linarith
        hence "N-6 \<ge> 6" by simp
        hence "N-6 \<ge> 0" by simp
        with \<open>N-6 \<ge> 6\<close> have "(N-6)^2 \<ge> 6^2"
          using power2_nat_le_eq_le by blast
        hence "(N-6)^2 \<ge> 24" by simp
        hence "(N-2)^2 \<ge> 8*(N-1)" by (simp add: power2_eq_square algebra_simps)
        hence "(N-2) \<ge> sqrt (8*(N-1))" using \<open>N > 0\<close>
          by (metis of_nat_0_le_iff of_nat_mono of_nat_power real_sqrt_le_mono real_sqrt_pow2 real_sqrt_power)
        hence "N - (2::real) - sqrt(8*N/m - 8) \<ge> 0"
          using \<open>sqrt (real (8 * N) / real m - 8) \<le> sqrt (real (8 * (N - 1)))\<close> \<open>N-6 \<ge> 6\<close> by linarith
        hence expr_pos: "N - 1 - (2/3::real) - sqrt(8*N/m - 8) \<ge> 0" by auto
        have "b \<le> 2/3 + sqrt(8*N/m - 8)" using \<open>b \<in> I\<close> I_def by auto
        hence "N - 1 - b \<ge> N - 1 - (2/3 + sqrt(8*N/m-8))" by auto
        hence "N - 1 - b \<ge> 0"
          using expr_pos of_int_0_le_iff by auto
        thus ?thesis by auto
      qed
      from \<open>N \<ge> 2 * m\<close> m_pos have "6*N/m - 3 \<ge> 0" by (simp add: mult_imp_le_div_pos)
      hence "1/2 + sqrt (6*N/m - 3) > 0"
        by (smt (verit, del_insts) divide_le_0_1_iff real_sqrt_ge_zero)
      with \<open>b \<in> I\<close> b_def I_def have "b \<ge> 1" by auto
      hence b_pos: "b \<ge> 0" by auto
      from \<open>b \<in> I\<close> have b_in_I: "(1/2::real) + sqrt (6* real N / real m - 3) \<le> b \<and> b \<le> (2/3::real) + sqrt (8 * real N/real m - 8)" unfolding I_def by auto
      from b_pos \<open>N-1 \<ge> b\<close> a_def have a_pos: "a \<ge> 0"
        by (smt (verit) m_pos of_nat_0_less_iff pos_imp_zdiv_neg_iff)
      hence "a \<ge> 1"
        by (smt (verit) \<open>odd a\<close> dvd_0_right)
      have "a - b = 2*(N-1-b) div m" using a_def by auto
      from \<open>int m dvd (N - 1 - b)\<close> have "m dvd 2*(N-1-b)" by fastforce
      have "a = 2*(N-1-b)/m + b" using a_def m_pos
        using \<open>int m dvd 2 * (N - 1 - b)\<close> by fastforce
      hence "a = 2*(N-1)/m - 2*b/m + b"
        by (simp add: assms diff_divide_distrib of_nat_diff)
      hence "(2::real)*(N-1)/m = a + 2*b/m - b" by auto
      hence "(2::real)*(N-1) = (a + 2*b/m - b)*m"
        using m_pos by (simp add: divide_eq_eq)
      hence "(2::real)*(N-1) = m*(a-b) + 2*b"
        using \<open>int m dvd 2 * (N - 1 - b)\<close> a_def by auto
      hence "N-1 = m*(a-b)/2 + b" by auto
      hence "N = m*(a-b)/2 + b + 1"
        using \<open>2 * m \<le> N\<close> assms(1) by linarith
      hence N_expr: "N = real m * (of_int a - of_int b) / 2 + of_int b + 1" by auto
      have "even (a-b)" using \<open>odd a\<close> b_def by auto
      hence "2 dvd m*(a-b)" by auto
      hence N_expr2: "N = m*(a-b) div 2 + b + 1" using \<open>N = m*(a-b)/2 + b + 1\<close> by linarith
      define Nr where "Nr = real_of_nat N"
      define mr where "mr = real m"
      define ar where "ar = real_of_int a"
      define br where "br = real_of_int b"
      from assms(1) have "mr \<ge> 3" using mr_def by auto
      moreover have "Nr \<ge> 2*mr" using Nr_def mr_def \<open>N \<ge> 2 * m\<close> by auto
      moreover have "br \<ge> 0" using br_def b_pos by auto
      moreover have "mr > 0" using mr_def m_pos by auto
      moreover have "ar \<ge> 0" using ar_def \<open>a \<ge> 0\<close> by auto
      moreover have "Nr = mr*(ar-br)/2 + br + 1" using Nr_def mr_def ar_def br_def N_expr by auto
      moreover have "1/2 + sqrt (6*Nr/mr-3) \<le> br \<and> br \<le> 2/3 + sqrt (8*Nr/mr-8)" using Nr_def mr_def br_def b_in_I by auto
      ultimately have "br^2 < 4*ar \<and> 3*ar < br^2+2*br+4" using Cauchy_lemma
        by auto
      hence real_ineq:"(real_of_int b)^2 < 4*(real_of_int a) \<and> 3*(real_of_int a) < (real_of_int b)^2 + 2*(real_of_int b) + 4"
        using br_def ar_def by auto
      hence int_ineq1: "b^2<4*a" using of_int_less_iff by fastforce
      from real_ineq have int_ineq2: "3*a < b^2+2*b+4" using of_int_less_iff by fastforce

      define an:: nat where "an = nat a"
      from a_pos have "an = a" unfolding an_def by auto
      define bn:: nat where "bn = nat b"
      from b_pos have "bn = b" unfolding bn_def by auto
      have "an \<ge> 1" using \<open>int an = a\<close> \<open>a \<ge> 1\<close> by auto
      moreover have "bn \<ge> 1" using \<open>int bn = b\<close> \<open>b \<ge> 1\<close> by auto
      moreover have "odd an" using \<open>odd a\<close> \<open>int an = a\<close> by auto
      moreover have "odd bn" using b_def \<open>int bn = b\<close> by auto
      moreover have "bn ^ 2 < 4 * an" using int_ineq1 \<open>int an = a\<close> \<open>int bn = b\<close>
        using of_nat_less_iff by fastforce
      moreover have "3 * an < bn ^ 2 + 2 * bn + 4" using int_ineq2 \<open>int an = a\<close> \<open>int bn = b\<close>
        using of_nat_less_iff by fastforce
      ultimately have "\<exists>s t u v :: int. s \<ge> 0 \<and> t \<ge> 0 \<and> u \<ge> 0 \<and> v \<ge> 0 \<and> an = s^2 + t^2 + u^2 + v^2 \<and>
    bn = s+t+u+v" using four_nonneg_int_sum by auto
      hence "\<exists>s t u v :: int. s \<ge> 0 \<and> t \<ge> 0 \<and> u \<ge> 0 \<and> v \<ge> 0 \<and> a = s^2 + t^2 + u^2 + v^2 \<and>
    b = s+t+u+v" using \<open>int an = a\<close> \<open>int bn = b\<close> by auto
      then obtain s t u v :: int where stuv: "s \<ge> 0 \<and> t \<ge> 0 \<and> u \<ge> 0 \<and> v \<ge> 0 \<and> a = s^2 + t^2 + u^2 + v^2 \<and>
    b = s+t+u+v" by auto
      hence "N = (m*(s^2+t^2+u^2+v^2-s-t-u-v) div 2) + s+t+u+v + 1" using N_expr2 by (smt (verit, ccfv_threshold))
      hence "N = (m*(s^2-s+t^2-t+u^2-u+v^2-v) div 2) + s+t+u+v + 1" by (smt (verit, ccfv_SIG))
      hence "N = (m * (s * (s-1) + t * (t-1) + u * (u-1) + v * (v-1)) div 2) +s+t+u+v + 1" by (simp add: power2_eq_square algebra_simps)
      hence previous_step: "N = (m * s * (s-1) + m * t * (t-1) + m * u * (u-1) + m * v * (v-1)) div 2 + s+t+u+v + 1" by (simp add: algebra_simps)
      moreover have "2 dvd m * s * (s-1)" by simp
      moreover have "2 dvd m * t * (t-1)" by simp
      moreover have "2 dvd m * u * (u-1)" by simp
      moreover have "2 dvd m * v * (v-1)" by simp
      ultimately have "N = m * s * (s-1) div 2 + m * t * (t-1) div 2 + m * u * (u-1) div 2 + m * v *(v-1) div 2 + s+t+u+v + 1" by fastforce
      hence N_expr3: "N = m * s * (s-1) div 2 + s + m * t * (t-1) div 2 + t + m * u * (u-1) div 2 + u + m * v * (v-1) div 2 + v + 1" by auto
      define sn::nat where "sn = nat s"
      define tn::nat where "tn = nat t"
      define un::nat where "un = nat u"
      define vn::nat where "vn = nat v"
      have "sn = s" using stuv sn_def by auto
      hence "m * sn * (sn-1) = m * s * (s-1)" by fastforce
      hence "m * sn * (sn-1) div 2 = m * s * (s-1) div 2" by linarith
      have "tn = t" using stuv tn_def by auto
      hence "m * tn * (tn-1) = m * t * (t-1)" by fastforce
      hence "m * tn * (tn-1) div 2 = m * t * (t-1) div 2" by linarith
      have "un = u" using stuv un_def by auto
      hence "m * un * (un-1) = m * u * (u-1)" by fastforce
      hence "m * un * (un-1) div 2 = m * u * (u-1) div 2" by linarith
      have "vn = v" using stuv vn_def by auto
      hence "m * vn * (vn-1) = m * v * (v-1)" by fastforce
      hence "m * vn * (vn-1) div 2 = m * v * (v-1) div 2" by linarith
      have "N = m * sn * (sn-1) div 2 + sn + m * tn * (tn-1) div 2 + tn + m * un * (un-1) div 2 + un + m * vn * (vn-1) div 2 + vn + 1"
        using N_expr3 \<open>sn = s\<close> \<open>tn = t\<close> \<open>un = u\<close> \<open>vn = v\<close> \<open>m * sn * (sn-1) div 2 = m * s * (s-1) div 2\<close> \<open>m * tn * (tn-1) div 2 = m * t * (t-1) div 2\<close> \<open>m * un * (un-1) div 2 = m * u * (u-1) div 2\<close> \<open>m * vn * (vn-1) div 2 = m * v * (v-1) div 2\<close> by linarith
      hence "N = polygonal_number m sn + polygonal_number m tn + polygonal_number m un + polygonal_number m vn + 1"
        using Polygonal_Number_Theorem_Gauss.polygonal_number_def by presburger
      also have "polygonal_number m 1 = 1" using Polygonal_Number_Theorem_Gauss.polygonal_number_def by auto
      ultimately have "N = polygonal_number m sn + polygonal_number m tn + polygonal_number m un + polygonal_number m vn + polygonal_number m 1" by auto
      thus ?thesis by blast
    qed
    show ?thesis using thm_odd_n thm_even_n by blast
  qed
qed
end