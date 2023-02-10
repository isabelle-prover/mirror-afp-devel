theory Compress

imports Kyber_spec
        Mod_Plus_Minus
        Abs_Qr
        "HOL-Analysis.Finite_Cartesian_Product"

begin

lemma prime_half:
  assumes "prime (p::int)"
          "p > 2"
  shows "\<lceil>p / 2\<rceil> > \<lfloor>p / 2\<rfloor>"
proof -
  have "odd p" using prime_odd_int[OF assms] .
  then have "\<lceil>p / 2\<rceil> > p/2" 
  by (smt (verit, best) cos_npi_int cos_zero_iff_int 
    le_of_int_ceiling mult.commute times_divide_eq_right)
  then have "\<lfloor>p / 2\<rfloor> < p/2" 
  by (meson floor_less_iff less_ceiling_iff)
  then show ?thesis using \<open>\<lceil>p / 2\<rceil> > p/2\<close> by auto
qed

lemma ceiling_int: 
  "\<lceil>of_int a + b\<rceil> = a + \<lceil>b\<rceil>"
unfolding ceiling_def by (simp add: add.commute)

lemma deg_Poly':
  assumes "Poly xs \<noteq> 0" 
  shows "degree (Poly xs) \<le> length xs - 1"
proof (induct xs)
  case (Cons a xs)
  then show ?case
    by simp (metis Poly.simps(1) Suc_le_eq Suc_pred 
    le_imp_less_Suc length_greater_0_conv)
qed simp


context kyber_spec begin

section \<open>Compress and Decompress Functions\<close>


text \<open>Properties of the \<open>mod+-\<close> function.\<close>

lemma two_mid_lt_q:
  "2 * \<lfloor>real_of_int q/2\<rfloor> < q" 
using oddE[OF prime_odd_int[OF q_prime q_gt_two]] by fastforce

lemma mod_plus_minus_range_q: 
  assumes "y \<in> {-\<lfloor>q/2\<rfloor>..\<lfloor>q/2\<rfloor>}"
  shows "y mod+- q = y"
using assms mod_plus_minus_rangeE q_gt_zero q_odd by presburger

 

text \<open>Compression only works for $x \in \mathbb{Z}_q$ and outputs an integer 
  in $\{0,\dots, 2^d-1\}$ , where $d$ is a positive integer with 
  $d < \rceil\log_2 (q)\lceil$. 
  For compression we omit the least important bits. 
  Decompression rescales to the modulus q.\<close>


definition compress :: "nat \<Rightarrow> int \<Rightarrow> int" where 
  "compress d x = 
  round (real_of_int (2^d * x) / real_of_int q) mod (2^d)"

definition decompress :: "nat \<Rightarrow> int \<Rightarrow> int" where 
  "decompress d x = 
  round (real_of_int q * real_of_int x / real_of_int 2^d)"

  

lemma compress_zero: "compress d 0 = 0"
unfolding compress_def by auto

lemma compress_less:
  \<open>compress d x < 2 ^ d\<close>
  by (simp add: compress_def)

lemma decompress_zero: "decompress d 0 = 0" 
unfolding decompress_def by auto


text \<open>Properties of the exponent $d$.\<close>

lemma d_lt_logq: 
  assumes "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
  shows "d< log 2 q"
using assms by linarith

lemma twod_lt_q: 
  assumes "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
  shows "2 powr (real d) < of_int q"
using assms less_log_iff[of 2 q d] d_lt_logq q_gt_zero 
by auto




lemma break_point_gt_q_div_two:
  assumes "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
  shows "\<lceil>q-(q/(2*2^d))\<rceil> > \<lfloor>q/2\<rfloor>"
proof -
  have "1/((2::real)^d) \<le> (1::real)" 
    using one_le_power[of 2 d] by simp
  have "\<lceil>q-(q/(2*2^d))\<rceil> \<ge> q-(q/2)* (1/(2^d))" by simp
  moreover have "q-(q/2)* (1/(2^d)) \<ge> q - q/2" 
    using \<open>1/((2::real)^d) \<le> (1::real)\<close>  
    by (smt (z3) calculation divide_le_eq divide_nonneg_nonneg 
      divide_self_if mult_left_mono of_int_nonneg 
      times_divide_eq_right q_gt_zero)
  ultimately have "\<lceil>q-(q/(2*2^d))\<rceil> \<ge> \<lceil>q/2\<rceil> " by linarith
  moreover have "\<lceil>q/2\<rceil> > \<lfloor>q/2\<rfloor>" 
    using prime_half[OF q_prime q_gt_two] .
  ultimately show ?thesis by auto
qed

lemma decompress_zero_unique: 
  assumes "decompress d s = 0"
          "s \<in> {0..2^d - 1}"
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
  shows "s = 0"
proof -
  let ?x = "real_of_int q * real_of_int s / 
    real_of_int 2^d + 1/2"
  have "0 \<le> ?x \<and> ?x < 1" using assms(1)
     unfolding decompress_def round_def 
    using floor_correct[of ?x] by auto
  then have "real_of_int q * real_of_int s / 
    real_of_int 2^d < 1/2" by linarith
  moreover have "real_of_int q / real_of_int 2^d > 1" 
    using twod_lt_q[OF assms(3)] 
    by (simp add: powr_realpow)
  ultimately have "real_of_int s < 1/2" 
  by (smt (verit, best) divide_less_eq_1_pos field_sum_of_halves 
    pos_divide_less_eq times_divide_eq_left)
  then show ?thesis using assms(2) by auto 
qed

text \<open>Range of compress and decompress functions\<close>


lemma range_compress: 
  assumes "x\<in>{0..q-1}" "of_nat d < \<lceil>(log 2 q)::real\<rceil>" 
  shows "compress d x \<in> {0..2^d - 1}" 
using compress_def by auto

lemma range_decompress:
  assumes "x\<in>{0..2^d - 1}" "of_nat d < \<lceil>(log 2 q)::real\<rceil>" 
  shows "decompress d x \<in> {0..q-1}" 
using decompress_def assms
proof (auto, goal_cases)
case 1
  then show ?case 
  by (smt (verit, best) divide_eq_0_iff divide_numeral_1 
    less_divide_eq_1_pos mult_of_int_commute 
    nonzero_mult_div_cancel_right of_int_eq_0_iff 
    of_int_less_1_iff powr_realpow q_gt_zero q_nonzero 
    round_0 round_mono twod_lt_q zero_less_power)
next
case 2
  have "real_of_int q/2^d > 1" using twod_lt_q[OF assms(2)]
    by (simp add: powr_realpow)
  then have log: "real_of_int q - real_of_int q/2^d \<le> q-1" by simp
  have "x \<le> 2^d-1" using assms(1) by simp
  then have "real_of_int x \<le> 2^d - 1" by (simp add: int_less_real_le)
  then have "real_of_int q * real_of_int x / 2^d \<le> 
    real_of_int q * (2^d-1) / 2^d" 
    by (smt (verit, best) divide_strict_right_mono 
      mult_less_cancel_left_pos of_int_pos q_gt_zero 
      zero_less_power)
  also have "\<dots> = real_of_int q * 2^d /2^d - real_of_int q/2^d"
    by (simp add: diff_divide_distrib right_diff_distrib)
  finally have "real_of_int q * real_of_int x / 2^d \<le> 
    real_of_int q - real_of_int q/2^d" by simp
  then have "round (real_of_int q * real_of_int x / 2^d) \<le> 
    round (real_of_int q - real_of_int q/2^d)" 
    using round_mono by blast
  also have "\<dots> \<le> q - 1" 
    using log by (metis round_mono round_of_int)
  finally show ?case by auto
qed

text \<open>Compression is a function qrom $\mathbb{Z} / q\mathbb{Z}$ to 
  $\mathbb{Z} / (2^d)\mathbb{Z}$.\<close>

lemma compress_in_range: 
  assumes "x\<in>{0..\<lceil>q-(q/(2*2^d))\<rceil>-1}" 
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>" 
  shows "round (real_of_int (2^d * x) / real_of_int q) < 2^d " 
proof - 
  have "(2::int)^d \<noteq> 0" by simp  
  have "real_of_int x < real_of_int q - real_of_int q / (2 * 2^d)" 
    using assms(1) less_ceiling_iff by auto 
  then have "2^d * real_of_int x / real_of_int q < 
    2^d * (real_of_int q - real_of_int q / (2 * 2^d)) / 
    real_of_int q" 
    by (simp add: divide_strict_right_mono q_gt_zero) 
  also have "\<dots> = 2^d * ((real_of_int q / real_of_int q) -
    (real_of_int q / real_of_int q) / (2 * 2^d))" 
  by (simp add:algebra_simps diff_divide_distrib) 
  also have "\<dots> = 2^d * (1 - 1/(2*2^d))" 
    using q_nonzero by simp 
  also have "\<dots> = 2^d - 1/2" 
    using \<open>2^d \<noteq> 0\<close> by (simp add: right_diff_distrib') 
  finally have "2^d * real_of_int x / real_of_int q < 
    2^d - (1::real)/(2::real)" 
    by auto 
  then show ?thesis unfolding round_def 
    using floor_less_iff by fastforce 
qed

text \<open>When does the modulo operation in the compression function change the output? 
  Only when  \<open>x \<ge> \<lceil>q-(q / (2*2^d))\<rceil>\<close>. Then we can determine that the compress function 
  maps to zero. This is why we need the \<open>mod+-\<close> in the definition of Compression.
  Otherwise the error bound would not hold.\<close>

lemma compress_no_mod: 
  assumes "x\<in>{0..\<lceil>q-(q / (2*2^d))\<rceil>-1}" 
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>" 
  shows "compress d x = 
    round (real_of_int (2^d * x) / real_of_int q)" 
unfolding compress_def 
using compress_in_range[OF assms] assms(1) q_gt_zero 
by (smt (z3) atLeastAtMost_iff divide_nonneg_nonneg 
  mod_pos_pos_trivial mult_less_cancel_left_pos 
  of_int_nonneg of_nat_0_less_iff right_diff_distrib'
  round_0 round_mono zero_less_power)

lemma compress_2d: 
  assumes "x\<in>{\<lceil>q-(q/(2*2^d))\<rceil>..q-1}" 
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>" 
  shows "round (real_of_int (2^d * x) / real_of_int q) = 2^d " 
using assms proof - 
  have "(2::int)^d \<noteq> 0" by simp
  have "round (real_of_int (2^d * x) / real_of_int q) \<ge> 2^d"
  proof -
    have "real_of_int x \<ge> real_of_int q - real_of_int q / (2 * 2^d)"
      using assms(1) ceiling_le_iff by auto 
    then have "2^d * real_of_int x / real_of_int q \<ge> 
      2^d * (real_of_int q - real_of_int q / (2 * 2^d)) / 
      real_of_int q" 
      using q_gt_zero by (simp add: divide_right_mono) 
    also have "2^d * (real_of_int q - real_of_int q / 
      (2 * 2^d)) / real_of_int q
      = 2^d * ((real_of_int q / real_of_int q) -
      (real_of_int q / real_of_int q) / (2 * 2^d))" 
      by (simp add:algebra_simps diff_divide_distrib) 
    also have "\<dots> = 2^d * (1 - 1/(2*2^d))" 
      using q_nonzero by simp 
    also have "\<dots> = 2^d - 1/2" 
      using \<open>2^d \<noteq> 0\<close> by (simp add: right_diff_distrib') 
    finally have "2^d * real_of_int x / real_of_int q \<ge> 
      2^d - (1::real)/(2::real)" 
      by auto 
    then show ?thesis unfolding round_def using le_floor_iff by force
  qed
  moreover have "round (real_of_int (2^d * x) / real_of_int q) \<le> 2^d"
  proof -
    have "d < log 2 q" using assms(2) by linarith
    then have "2 powr (real d) < of_int q" 
      using less_log_iff[of 2 q d] q_gt_zero by auto
    have "x < q" using assms(1) by auto
    then have "real_of_int x/ real_of_int q < 1"
      by (simp add: q_gt_zero)
    then have "real_of_int (2^d * x) / real_of_int q < 
      real_of_int (2^d)" 
      by (auto) (smt (verit, best) divide_less_eq_1_pos 
        nonzero_mult_div_cancel_left times_divide_eq_right 
        zero_less_power)
    then show ?thesis unfolding round_def by linarith
  qed 
  ultimately show ?thesis by auto
qed

lemma compress_mod: 
  assumes "x\<in>{\<lceil>q-(q/(2*2^d))\<rceil>..q-1}" 
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>" 
  shows "compress d x = 0" 
unfolding compress_def using compress_2d[OF assms] by simp


text \<open>Error after compression and decompression of data.
  To prove the error bound, we distinguish the cases where the \<open>mod+-\<close> is relevant or not.\<close>

text \<open>First let us look at the error bound for no \<open>mod+-\<close> reduction.\<close>

lemma decompress_compress_no_mod: 
  assumes "x\<in>{0..\<lceil>q-(q/(2*2^d))\<rceil>-1}" 
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
  shows "abs (decompress d (compress d x) - x) \<le> 
    round ( real_of_int q / real_of_int (2^(d+1)))" 
proof - 
  have "abs (decompress d (compress d x) - x) = 
    abs (real_of_int (decompress d (compress d x)) - 
    real_of_int q / real_of_int (2^d) * 
    (real_of_int (2^d * x) / real_of_int q))"
    using q_gt_zero by force
  also have "\<dots> \<le> abs (real_of_int (decompress d (compress d x)) -
    real_of_int q / real_of_int (2^d) * real_of_int (compress d x)) +
    abs (real_of_int q / real_of_int (2^d) * 
    real_of_int (compress d x) - real_of_int q / real_of_int (2^d) *
    real_of_int (2^d) / real_of_int q * x)"
    using abs_triangle_ineq[of 
      "real_of_int (decompress d (compress d x)) -
       real_of_int q / real_of_int (2^d) * real_of_int (compress d x)"
      "real_of_int q / real_of_int (2^d) * real_of_int (compress d x)
       - real_of_int q / real_of_int (2^d) * real_of_int (2^d) / 
       real_of_int q * real_of_int x"] by auto
  also have "\<dots> \<le> 1/2 + abs (real_of_int q / real_of_int (2^d) *
    (real_of_int (compress d x) - 
     real_of_int (2^d) / real_of_int q * real_of_int x))"
    proof -
      have part_one: 
        "abs (real_of_int (decompress d (compress d x)) -
        real_of_int q / real_of_int (2^d) * real_of_int (compress d x))
        \<le> 1/2"
        unfolding decompress_def 
        using of_int_round_abs_le[of "real_of_int q * 
          real_of_int (compress d x) / real_of_int 2^d"] by simp
      have "real_of_int q * real_of_int (compress d x) / 2^d -
        real_of_int x =
        real_of_int q * (real_of_int (compress d x) - 
        2^d * real_of_int x / real_of_int q) / 2^d" 
        by (smt (verit, best) divide_cancel_right 
        nonzero_mult_div_cancel_left of_int_eq_0_iff 
        q_nonzero right_diff_distrib times_divide_eq_left 
        zero_less_power)
      then have part_two: 
        "abs (real_of_int q / real_of_int (2^d) * 
        real_of_int (compress d x) -
        real_of_int q / real_of_int (2^d) * real_of_int (2^d) /
        real_of_int q * x) =
        abs (real_of_int q / real_of_int (2^d) * 
        (real_of_int (compress d x) - real_of_int (2^d) /
        real_of_int q * x)) " by auto
      show ?thesis using part_one part_two by auto
   qed
  also have "\<dots> = 1/2 + (real_of_int q / real_of_int (2^d)) *
      abs (real_of_int (compress d x) - real_of_int (2^d) /
      real_of_int q * real_of_int x)"
    by (subst abs_mult) (smt (verit, best) assms(2) 
      less_divide_eq_1_pos of_int_add of_int_hom.hom_one 
      of_int_power powr_realpow twod_lt_q zero_less_power)
  also have "\<dots> \<le> 1/2 + (real_of_int q / real_of_int (2^d)) * (1/2) "
    using compress_no_mod[OF assms] 
    using of_int_round_abs_le[of "real_of_int (2^d) *
      real_of_int x / real_of_int q"]
    by (smt (verit, ccfv_SIG) divide_nonneg_nonneg left_diff_distrib 
      mult_less_cancel_left_pos of_int_mult of_int_nonneg q_gt_zero 
      times_divide_eq_left zero_le_power)
  finally have "real_of_int (abs (decompress d (compress d x) - x)) \<le>
                real_of_int q / real_of_int (2*2^d) + 1/2" 
    by simp
  then show ?thesis unfolding round_def using le_floor_iff 
    by fastforce
qed


lemma no_mod_plus_minus: 
  assumes "abs y \<le> round ( real_of_int q / real_of_int (2^(d+1)))"
          "d>0"
  shows "abs y = abs (y mod+- q)"
proof -
  have "round (real_of_int q / real_of_int (2^(d+1))) \<le> \<lfloor>q/2\<rfloor>" 
  unfolding round_def 
  proof -
    have "real_of_int q/real_of_int (2^d) \<le> real_of_int q/2" 
    using \<open>d>0\<close> 
    proof -
      have "1 / real_of_int (2^d) \<le> 1/2" 
        using \<open>d>0\<close> inverse_of_nat_le[of 2 "2^d"]
        by (simp add: self_le_power)
      then show ?thesis using q_gt_zero 
        by (smt (verit, best) frac_less2 of_int_le_0_iff zero_less_power)
    qed
    moreover have "real_of_int q/2 + 1 \<le> real_of_int q" 
      using q_gt_two by auto
    ultimately have "real_of_int q / real_of_int (2^d) + 1 \<le> 
      real_of_int q" by linarith
    then have fact: "real_of_int q / real_of_int (2 ^ (d + 1)) + 
      1/2 \<le> real_of_int q/2" 
      by auto
    then show "\<lfloor>real_of_int q / real_of_int (2 ^ (d + 1)) + 1/2\<rfloor> \<le>
      \<lfloor>real_of_int q/2\<rfloor>" 
      using floor_mono[OF fact] by auto
  qed
  then have "abs y \<le> \<lfloor>q/2\<rfloor>" using assms by auto
  then show ?thesis using mod_plus_minus_range_odd[OF q_gt_zero q_odd] 
  by (smt (verit, del_insts) mod_plus_minus_def mod_pos_pos_trivial neg_mod_plus_minus 
    q_odd two_mid_lt_q)
qed


lemma decompress_compress_no_mod_plus_minus: 
  assumes "x\<in>{0..\<lceil>q-(q/(2*2^d))\<rceil>-1}" 
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
          "d>0"
  shows "abs ((decompress d (compress d x) - x) mod+- q) \<le> 
          round ( real_of_int q / real_of_int (2^(d+1)))"
proof -
  have "abs ((decompress d (compress d x) - x) mod+- q) =
        abs ((decompress d (compress d x) - x)) " 
    using no_mod_plus_minus[OF decompress_compress_no_mod
      [OF assms(1) assms(2)] assms(3)] by auto
  then show ?thesis using decompress_compress_no_mod
    [OF assms(1) assms(2)] by auto
qed

text \<open>Now lets look at what happens when the \<open>mod+-\<close> reduction comes into action.\<close>


lemma decompress_compress_mod: 
  assumes "x\<in>{\<lceil>q-(q/(2*2^d))\<rceil>..q-1}" 
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
  shows "abs ((decompress d (compress d x) - x) mod+- q) \<le> 
         round ( real_of_int q / real_of_int (2^(d+1)))"
proof -
  have "(decompress d (compress d x) - x) = - x" 
    using compress_mod[OF assms] unfolding decompress_def 
    by auto
  moreover have "-x mod+- q = -x+q"
  proof -
    have range_x: "x \<in> {\<lfloor>real_of_int q / 2\<rfloor><..q - 1}" using assms(1) 
      break_point_gt_q_div_two[OF assms(2)] by auto
    then have *: "- x \<in> {-q + 1..< -\<lfloor>real_of_int q / 2\<rfloor>}" by auto
    have **: "-x + q \<in>{0..<q-\<lfloor>real_of_int q / 2\<rfloor>}" using * by auto 
    have "-x + q \<in>{0..<q}" 
    proof (subst atLeastLessThan_iff)
      have "q-\<lfloor>real_of_int q / 2\<rfloor> \<le> q" using q_gt_zero by auto
      moreover have "0 \<le> - x + q \<and> - x + q < q-\<lfloor>real_of_int q / 2\<rfloor>" using ** by auto
      ultimately show "0 \<le> - x + q \<and> - x + q < q" by linarith
    qed
    then have rew: "-x mod q = -x + q" using mod_rangeE by fastforce
    have "-x mod q < q - \<lfloor>real_of_int q / 2\<rfloor>" using ** by (subst rew)(auto simp add: * range_x)
    then have "\<lfloor>real_of_int q / 2\<rfloor> \<ge> - x mod q" by linarith
    then show ?thesis unfolding mod_plus_minus_def using rew by auto
  qed
  moreover have "abs (q - x) \<le> round ( real_of_int q / 
    real_of_int (2^(d+1)))" 
  proof -
    have "abs (q-x) = q-x" 
      using assms(1) by auto
    also have "\<dots> \<le> q - \<lceil>q - q/(2*2^d)\<rceil>" 
      using assms(1) by simp
    also have "\<dots> = - \<lceil>- q/(2*2^d)\<rceil>" 
      using ceiling_int[of q "- q/(2*2^d)"] by auto
    also have "\<dots> = \<lfloor>q/(2*2^d)\<rfloor>" 
      by (simp add: ceiling_def)
    also have "\<dots> \<le> round (q/(2*2^d))" 
      using floor_le_round by blast
    finally have "abs (q-x) \<le> round (q/(2^(d+1)))" by auto
    then show ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed

text \<open>Together, we can determine the general error bound on 
  decompression of compression of the data.
  This error needs to be small enough not to disturb the encryption and decryption process.\<close>

lemma decompress_compress: 
  assumes "x\<in>{0..<q}"
          "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
          "d>0"
  shows "let x' = decompress d (compress d x) in 
         abs ((x' - x) mod+- q) \<le> 
          round ( real_of_int q / real_of_int (2^(d+1)) )" 
proof (cases "x<\<lceil>q-(q/(2*2^d))\<rceil>")
case True
  then have range_x: "x\<in>{0..\<lceil>q-(q/(2*2^d))\<rceil>-1}" 
    using assms(1) by auto
  show ?thesis unfolding Let_def 
    using decompress_compress_no_mod_plus_minus[OF 
    range_x assms(2) assms(3)] by auto
next
case False
  then have range_x: "x\<in>{\<lceil>q-(q/(2*2^d))\<rceil>..q-1}" 
    using assms(1) by auto
  show ?thesis unfolding Let_def 
    using decompress_compress_mod[OF range_x assms(2)] 
    by auto
qed

text \<open>We have now defined compression only on integers (ie \<open>{0..<q}\<close>, corresponding to \<open>\<int>_q\<close>). 
  We need to extend this notion to the ring \<open>\<int>_q[X]/(X^n+1)\<close>. Here, a compressed polynomial 
  is the compression on every coefficient.\<close>

text \<open>
How to channel through the types
\begin{itemize}
\item \<open>to_qr :: 'a mod_ring poly \<Rightarrow> 'a qr\<close>
\item \<open>Poly ::  'a mod_ring list \<Rightarrow> 'a mod_ring poly\<close>
\item \<open>map of_int_mod_ring :: int list \<Rightarrow> 'a mod_ring list\<close>
\item \<open>map compress :: int list \<Rightarrow> int list\<close>
\item \<open>map to_int_mod_ring :: 'a mod_ring list \<Rightarrow> int list\<close>
\item \<open>coeffs :: 'a mod_ring poly \<Rightarrow> 'a mod_ring list\<close>
\item \<open>of_qr :: 'a qr \<Rightarrow> 'a mod_ring poly\<close>
\end{itemize}
\<close>
definition compress_poly :: "nat \<Rightarrow> 'a qr \<Rightarrow> 'a qr" where
  "compress_poly d = 
        to_qr \<circ>
        Poly \<circ>
        (map of_int_mod_ring) \<circ>
        (map (compress d)) \<circ>
        (map to_int_mod_ring) \<circ>
        coeffs \<circ>
        of_qr"

definition decompress_poly :: "nat \<Rightarrow> 'a qr \<Rightarrow> 'a qr" where
  "decompress_poly d = 
        to_qr \<circ>
        Poly \<circ>
        (map of_int_mod_ring) \<circ>
        (map (decompress d)) \<circ>
        (map to_int_mod_ring) \<circ>
        coeffs \<circ>
        of_qr"


text \<open>Lemmas for compression error for polynomials. Lemma telescope to go qrom module level 
    down to integer coefficients and back up again.\<close>



lemma of_int_mod_ring_eq_0:
  "((of_int_mod_ring x :: 'a mod_ring) = 0) \<longleftrightarrow> 
    (x mod q = 0)"
by (metis CARD_a mod_0 of_int_code(2) 
  of_int_mod_ring.abs_eq of_int_mod_ring.rep_eq 
  of_int_of_int_mod_ring)

lemma dropWhile_mod_ring:
  "dropWhile ((=)0) (map of_int_mod_ring xs :: 'a mod_ring list) = 
   map of_int_mod_ring (dropWhile (\<lambda>x. x mod q = 0) xs)"
proof (induct xs)
  case (Cons x xs)
  have "dropWhile ((=) 0) (map of_int_mod_ring (x # xs)) = 
        dropWhile ((=) 0) ((of_int_mod_ring x :: 'a mod_ring) # 
        (map of_int_mod_ring xs))"
    by auto
  also have "\<dots> = (if 0 = (of_int_mod_ring x :: 'a mod_ring) 
    then dropWhile ((=) 0) (map of_int_mod_ring xs) 
    else map of_int_mod_ring (x # xs))" 
    unfolding dropWhile.simps(2)[of "((=) 0)" 
      "of_int_mod_ring x :: 'a mod_ring" "map of_int_mod_ring xs"]
    by auto
  also have "\<dots> = (if x mod q = 0 
    then map of_int_mod_ring (dropWhile (\<lambda>x. x mod q = 0) xs)
    else map of_int_mod_ring (x # xs))" 
    using of_int_mod_ring_eq_0 unfolding Cons.hyps by auto
  also have "\<dots> = map of_int_mod_ring (dropWhile (\<lambda>x. x mod q = 0) 
    (x # xs))"
    unfolding dropWhile.simps(2) by auto
  finally show ?case by blast
qed simp

lemma strip_while_mod_ring:
"(strip_while ((=) 0) (map of_int_mod_ring xs :: 'a mod_ring list)) =
  map of_int_mod_ring (strip_while (\<lambda>x. x mod q = 0)  xs)"
unfolding strip_while_def comp_def rev_map dropWhile_mod_ring by auto


lemma of_qr_to_qr_Poly: 
  assumes "length (xs :: int list) < Suc (nat n)"
          "xs \<noteq> []"
  shows "of_qr (to_qr 
    (Poly (map (of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) xs))) =
     Poly (map (of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) xs)"
    (is "_ = ?Poly")
proof -
  have deg: "degree (?Poly) < n"
    using deg_Poly'[of "map of_int_mod_ring xs"] assms 
    by (smt (verit, del_insts) One_nat_def Suc_pred degree_0 
      length_greater_0_conv length_map less_Suc_eq_le 
      order_less_le_trans zless_nat_eq_int_zless)
  then show ?thesis
    using of_qr_to_qr[of "?Poly"] deg_mod_qr_poly[of "?Poly"] 
      deg_qr_n by (smt (verit, best) of_nat_less_imp_less)
qed

lemma telescope_stripped:
  assumes "length (xs :: int list) < Suc (nat n)"
    "strip_while (\<lambda>x. x mod q = 0) xs = xs"
    "set xs \<subseteq> {0..<q}"
  shows "(map to_int_mod_ring) 
    (coeffs (of_qr (to_qr (Poly 
    (map (of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) xs))))) = xs"
proof (cases "xs = []")
case False
  have ge_zero: "0\<le>x" and lt_q:"x < int CARD ('a)" 
    if "x\<in>set xs" for x 
    using assms(3) CARD_a atLeastLessThan_iff that by auto
  have to_int_of_int: "map (to_int_mod_ring \<circ> 
    (of_int_mod_ring :: int \<Rightarrow> 'a mod_ring)) xs = xs"
    using to_int_mod_ring_of_int_mod_ring[OF ge_zero lt_q] 
    by (simp add: map_idI)
  show ?thesis using assms(2) 
    of_qr_to_qr_Poly[OF assms(1) False] 
    by (auto simp add: to_int_of_int strip_while_mod_ring) 
qed (simp)

lemma map_to_of_mod_ring:
  assumes "set xs \<subseteq> {0..<q}"
  shows "map (to_int_mod_ring \<circ> 
    (of_int_mod_ring :: int \<Rightarrow> 'a mod_ring)) xs = xs"
using assms by (induct xs) (simp_all add: CARD_a)

lemma telescope:
  assumes "length (xs :: int list) < Suc (nat n)"
    "set xs \<subseteq> {0..<q}"
  shows "(map to_int_mod_ring) 
    (coeffs (of_qr (to_qr (Poly 
    (map (of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) xs))))) =
    strip_while (\<lambda>x. x mod q = 0) xs"
proof (cases "xs = strip_while (\<lambda>x. x mod q = 0) xs")
case True
  then show ?thesis using telescope_stripped assms 
    by auto
next
case False
  let ?of_int = "(map (of_int_mod_ring :: 
    int \<Rightarrow> 'a mod_ring) xs)"
  have "xs \<noteq> []" using False by auto
  then have "(map to_int_mod_ring) 
    (coeffs (of_qr (to_qr (Poly ?of_int)))) = 
    (map to_int_mod_ring) (coeffs (Poly ?of_int))"
    using of_qr_to_qr_Poly[OF assms(1)] by auto
  also have "\<dots> = (map to_int_mod_ring) 
    (strip_while ((=) 0) ?of_int)" 
    by auto
  also have "\<dots> = map (to_int_mod_ring \<circ> 
    (of_int_mod_ring :: int \<Rightarrow> 'a mod_ring))
    (strip_while (\<lambda>x. x mod q = 0) xs)" 
    using strip_while_mod_ring by auto
  also have "\<dots> = strip_while (\<lambda>x. x mod q = 0) xs"
  using assms(2) proof (induct xs rule: rev_induct)
  case (snoc y ys)
    let ?to_of_mod_ring = "to_int_mod_ring \<circ> 
      (of_int_mod_ring :: int \<Rightarrow> 'a mod_ring)"
    have "map ?to_of_mod_ring 
      (strip_while (\<lambda>x. x mod q = 0) (ys @ [y])) =
      (if y mod q = 0 
       then map ?to_of_mod_ring (strip_while (\<lambda>x. x mod q = 0) ys)
       else map ?to_of_mod_ring ys @ [?to_of_mod_ring y])"
      by (subst strip_while_snoc) auto
    also have "\<dots> = (if y mod q = 0 
        then strip_while (\<lambda>x. x mod q = 0) ys
        else map ?to_of_mod_ring ys @ [?to_of_mod_ring y])"
    using snoc by fastforce
    also have "\<dots> = (if y mod q = 0 
        then strip_while (\<lambda>x. x mod q = 0) ys
        else ys @ [y])"
      using map_to_of_mod_ring[OF snoc(2)] by auto
    also have "\<dots> = strip_while (\<lambda>x. x mod q = 0) (ys @ [y])" 
      by auto
    finally show ?case .
  qed simp
  finally show ?thesis by auto
qed

lemma length_coeffs_of_qr: 
  "length (coeffs (of_qr (x ::'a qr))) < Suc (nat n)"
proof (cases "x=0")
case False
  then have "of_qr x \<noteq> 0" by simp
  then show ?thesis 
    using length_coeffs_degree[of "of_qr x"] deg_of_qr[of x]
    using deg_qr_n by fastforce
qed  (auto simp add: n_gt_zero) 
end

lemma strip_while_change: 
  assumes "\<And>x. P x \<longrightarrow> S x" "\<And>x. (\<not> P x) \<longrightarrow> (\<not> S x)"
  shows "strip_while P xs = strip_while S xs"
proof (induct xs rule: rev_induct)
case (snoc x xs)
  have "P x = S x" using assms[of x] by blast
  then show ?case by (simp add: snoc.hyps)
qed simp

lemma strip_while_change_subset: 
  assumes "set xs \<subseteq> s" 
    "\<forall>x\<in>s. P x \<longrightarrow> S x" 
    "\<forall>x\<in>s. (\<not> P x) \<longrightarrow> (\<not> S x)"
  shows "strip_while P xs = strip_while S xs"
using assms(1) proof (induct xs rule: rev_induct)
case (snoc x xs)
  have "x\<in>s" using snoc(2) by simp
  then have "P x \<longrightarrow> S x" and "(\<not> P x) \<longrightarrow> (\<not> S x)" 
    using assms(2) assms(3) by auto
  then have "P x = S x" by blast
  then show ?case
  using snoc.hyps snoc.prems by auto
qed simp

text \<open>Estimate for decompress compress for polynomials. Using the inequality for integers,
  chain it up to the level of polynomials.\<close>
context kyber_spec
begin
lemma decompress_compress_poly:
  assumes "of_nat d < \<lceil>(log 2 q)::real\<rceil>"
          "d>0"
  shows "let x' = decompress_poly d (compress_poly d x) in 
    abs_infty_poly (x - x') \<le> 
    round ( real_of_int q / real_of_int (2^(d+1)) )" 
proof -
  let ?x' = "decompress_poly d (compress_poly d x)"
  have "abs_infty_q (poly.coeff (of_qr (x - ?x')) xa)
       \<le> round (real_of_int q / real_of_int (2 ^ (d + 1)))" 
  for xa
  proof -
    let ?telescope = "(\<lambda>xs. (map to_int_mod_ring) 
      (coeffs (of_qr (to_qr (Poly 
      (map (of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) xs))))))"
    define compress_x where 
      "compress_x =  map (compress d \<circ> to_int_mod_ring) 
      (coeffs (of_qr x))"
    let ?to_Poly = "(\<lambda>a. Poly (map ((of_int_mod_ring :: 
      int \<Rightarrow> 'a mod_ring) \<circ> decompress d) a))"
    have "abs_infty_q (poly.coeff (of_qr x) xa -
      poly.coeff (of_qr (to_qr (?to_Poly 
      (?telescope compress_x)))) xa ) = 
      abs_infty_q (poly.coeff (of_qr x) xa - 
      poly.coeff (of_qr (to_qr (?to_Poly 
      (strip_while (\<lambda>x. x = 0) compress_x)))) xa )" 
    proof (cases "x = 0")
    case True
      then have "compress_x = []" 
        unfolding compress_x_def by auto
      then show ?thesis by simp
    next
    case False
      then have nonempty:"compress_x \<noteq> []" 
        unfolding compress_x_def by simp
      have "length compress_x < Suc (nat n)" 
         by (auto simp add: compress_x_def length_coeffs_of_qr)
      moreover have "set compress_x \<subseteq> {0..<q}" 
      proof -
        have to: "to_int_mod_ring (s::'a mod_ring) \<in> 
            {0..q - 1}" for s
          using to_int_mod_ring_range by auto
        have "compress d (to_int_mod_ring (s::'a mod_ring)) \<in> 
          {0..<q}" for s
          using range_compress[OF to assms(1), of s] 
          twod_lt_q[OF assms(1)]
          by (simp add: powr_realpow)
        then show ?thesis unfolding compress_x_def by auto
      qed
      ultimately have "?telescope compress_x = 
        strip_while (\<lambda>x. x mod q = 0) compress_x"
        by (intro telescope[of "compress_x"]) simp
      moreover have "strip_while (\<lambda>x. x mod q = 0) compress_x = 
        strip_while (\<lambda>x. x = 0) compress_x"
      proof -
        have \<open>compress d s = 0\<close> if \<open>compress d s mod q = 0\<close> for s
        proof -
          from \<open>int d < \<lceil>log 2 (real_of_int q)\<rceil>\<close> twod_lt_q [of d]
          have \<open>2 ^ d < q\<close>
            by (simp add: powr_realpow)
          with compress_less [of d s] have \<open>compress d s < q\<close>
            by simp
          then have \<open>compress d s = compress d s mod q\<close>
            by (simp add: compress_def)
          with that show ?thesis
            by simp
        qed
        then have right: "\<And>s. compress d s mod q = 0 \<longrightarrow> 
          compress d s = 0" by simp
        have  "\<not> (compress d s = 0)" 
          if "\<not> (compress d s mod q = 0)" for s
          using twod_lt_q compress_def that by force
        then have left: "\<And>s. \<not> (compress d s mod q = 0) \<longrightarrow> 
          \<not> (compress d s = 0)" by simp
        have "strip_while (\<lambda>x. x mod q = 0) compress_x = 
          strip_while (\<lambda>x. x mod q = 0) (map (compress d) 
          (map to_int_mod_ring (coeffs (of_qr x))))"
          (is "_ = strip_while (\<lambda>x. x mod q = 0) 
            (map (compress d) ?rest)")
          unfolding compress_x_def by simp
        also have "\<dots> = map (compress d) 
          (strip_while ((\<lambda>y. y mod q = 0) \<circ> compress d)
          (map to_int_mod_ring (coeffs (of_qr x))))"
          using strip_while_map[of "\<lambda>y. y mod q = 0" "compress d"] 
          by blast
        also have "\<dots> = map (compress d) 
          (strip_while ((\<lambda>y. y = 0) \<circ> compress d)
          (map to_int_mod_ring (coeffs (of_qr x))))"
          by (smt (verit, best) comp_eq_dest_lhs left right 
            strip_while_change)
        also have "\<dots> = strip_while (\<lambda>x. x = 0) 
          (map (compress d) ?rest)"
          using strip_while_map[of "\<lambda>y. y = 0" 
            "compress d", symmetric] by blast
        finally show ?thesis 
          unfolding compress_x_def by auto 
      qed
      ultimately show ?thesis by auto
    qed
    also have "\<dots> = abs_infty_q (poly.coeff (of_qr x) xa -
      poly.coeff (?to_Poly (strip_while (\<lambda>x. x = 0) compress_x)) xa)" 
    proof (cases "?to_Poly (strip_while (\<lambda>x. x = 0) compress_x) = 0")
    case False
      have "degree (?to_Poly (strip_while (\<lambda>x. x = 0) compress_x)) \<le>
        length (map ((of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) \<circ> 
        decompress d) (strip_while (\<lambda>x. x = 0) compress_x)) - 1" 
        using deg_Poly'[OF False] .
      moreover have "length (map (of_int_mod_ring \<circ> decompress d) 
          (strip_while (\<lambda>x. x = 0) compress_x)) \<le> 
          length (coeffs (of_qr x))"
        unfolding compress_x_def 
        by (metis length_map length_strip_while_le)
      moreover have "length (coeffs (of_qr x)) - 1 < deg_qr TYPE('a)"
        using deg_of_qr degree_eq_length_coeffs by metis
      ultimately have deg: 
        "degree (?to_Poly (strip_while (\<lambda>x. x = 0) compress_x)) < 
        deg_qr TYPE('a)" by auto
      show ?thesis using of_qr_to_qr'
        by (simp add: of_qr_to_qr'[OF deg])
    qed simp
    also have "\<dots> = abs_infty_q (poly.coeff (of_qr x) xa -
      poly.coeff (Poly (map of_int_mod_ring (strip_while (\<lambda>x. x = 0) 
        (map (decompress d) compress_x)))) xa )" 
    proof -
      have  "s = 0" if "decompress d s = 0" "s \<in> {0..2^d - 1}" for s 
        using decompress_zero_unique[OF that assms(1)] .
      then have right: "\<forall>s \<in> {0..2^d-1}. decompress d s = 0 \<longrightarrow> 
        s = 0" by simp
      have left: "\<forall> s \<in> {0..2^d-1}. decompress d s \<noteq> 0 \<longrightarrow> s \<noteq> 0" 
        using decompress_zero[of d] by auto
      have compress_x_range: "set compress_x \<subseteq> {0..2^d - 1}" 
        unfolding compress_x_def compress_def by auto
      have "map (decompress d) (strip_while (\<lambda>x. x = 0) compress_x) =
        map (decompress d) (strip_while (\<lambda>x. decompress d x = 0) 
          compress_x)"
      using strip_while_change_subset[OF compress_x_range right left] 
        by auto
      also have "\<dots> = strip_while (\<lambda>x. x = 0) 
        (map (decompress d) compress_x)"
      proof -
        have "(\<lambda>x. x = 0) \<circ> decompress d = (\<lambda>x. decompress d x = 0)" 
          using comp_def by blast
        then show ?thesis 
          using strip_while_map[symmetric, of "decompress d" 
            "\<lambda>x. x=0" compress_x] by auto
      qed
      finally have "map (decompress d) (strip_while (\<lambda>x. x = 0) 
        compress_x) =  strip_while (\<lambda>x. x = 0) (map (decompress d)
        compress_x)" by auto
      then show ?thesis by (metis map_map)
    qed
    also have "\<dots> = abs_infty_q (poly.coeff (of_qr x) xa -
      poly.coeff (Poly (map of_int_mod_ring (strip_while 
      (\<lambda>x. x mod q = 0) (map (decompress d) compress_x)))) xa )" 
    proof -
      have range: "set (map (decompress d) compress_x) \<subseteq> {0..<q}" 
        unfolding compress_x_def compress_def
        using range_decompress[OF _ assms(1)] by auto
      have right: " \<forall>x\<in>{0..<q}. x = 0 \<longrightarrow> x mod q = 0" by auto
      have left: "\<forall>x\<in>{0..<q}. \<not> x = 0 \<longrightarrow> \<not> x mod q = 0" by auto
      have "strip_while (\<lambda>x. x = 0) (map (decompress d) compress_x) =
        strip_while (\<lambda>x. x mod q = 0) (map (decompress d) compress_x)"
      using strip_while_change_subset[OF range right left] by auto
      then show ?thesis by auto
    qed
    also have "\<dots> = abs_infty_q (poly.coeff (of_qr x) xa -
      poly.coeff (Poly (map of_int_mod_ring 
      (map (decompress d) compress_x))) xa )" 
      by (metis Poly_coeffs coeffs_Poly strip_while_mod_ring)
    also have "\<dots> = abs_infty_q (poly.coeff (of_qr x) xa -
      ((of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) \<circ> decompress d \<circ> 
        compress d \<circ> to_int_mod_ring) (poly.coeff (of_qr x) xa))" 
    using coeffs_Poly 
    proof (cases "xa < length (coeffs (?to_Poly  compress_x))")
    case True
      have "poly.coeff (?to_Poly compress_x) xa =
            coeffs (?to_Poly compress_x) ! xa"
      using nth_coeffs_coeff[OF True] by simp
      also have "\<dots> = strip_while ((=) 0) (map (
        (of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) \<circ> decompress d) 
        compress_x) ! xa"
        using coeffs_Poly by auto
      also have "\<dots> = (map ((of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) \<circ> 
        decompress d) compress_x) ! xa" 
        using True by (metis coeffs_Poly nth_strip_while)
      also have "\<dots> = ((of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) \<circ> 
        decompress d \<circ> compress d \<circ> to_int_mod_ring) 
        (coeffs (of_qr x) ! xa)" 
        unfolding compress_x_def 
        by (smt (z3) True coeffs_Poly compress_x_def length_map 
          length_strip_while_le map_map not_less nth_map order_trans)
      also have "\<dots> = ((of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) \<circ> 
        decompress d \<circ> compress d \<circ> to_int_mod_ring) 
        (poly.coeff (of_qr x) xa)" 
        by (metis (no_types, lifting) True coeffs_Poly compress_x_def 
          length_map length_strip_while_le not_less nth_coeffs_coeff 
          order.trans)
      finally have no_coeff: "poly.coeff (?to_Poly compress_x) xa = 
          ((of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) \<circ> decompress d \<circ> 
          compress d \<circ> to_int_mod_ring) (poly.coeff (of_qr x) xa)" 
        by auto
      show ?thesis unfolding compress_x_def 
      by (metis compress_x_def map_map no_coeff)
    next
    case False
      then have "poly.coeff (?to_Poly compress_x) xa = 0"
        by (metis Poly_coeffs coeff_Poly_eq nth_default_def)
      moreover have "((of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) \<circ> 
        decompress d \<circ> compress d \<circ> to_int_mod_ring) 
        (poly.coeff (of_qr x) xa) = 0" 
      proof (cases "poly.coeff (of_qr x) xa = 0")
      case True
        then show ?thesis using compress_zero decompress_zero 
          by auto
      next
      case False
        then show ?thesis 
        proof (subst ccontr, goal_cases)
        case 1
          then have "poly.coeff (?to_Poly compress_x) xa \<noteq> 0" 
            by (subst coeff_Poly) (metis (no_types, lifting) comp_apply 
              compress_x_def compress_zero decompress_zero map_map 
              nth_default_coeffs_eq nth_default_map_eq 
              of_int_mod_ring_hom.hom_zero to_int_mod_ring_hom.hom_zero)
          then show ?case using \<open>poly.coeff (?to_Poly compress_x) xa = 0\<close> 
            by auto
        qed auto
      qed
      ultimately show ?thesis by auto
    qed
    also have "\<dots> = abs_infty_q (
      ((of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) \<circ> decompress d \<circ> 
        compress d \<circ> to_int_mod_ring) (poly.coeff (of_qr x) xa) -
        poly.coeff (of_qr x) xa)" 
      using abs_infty_q_minus by (metis minus_diff_eq)
    also have "\<dots> = \<bar>((decompress d \<circ> compress d \<circ> to_int_mod_ring) 
      (poly.coeff (of_qr x) xa) -
       to_int_mod_ring (poly.coeff (of_qr x) xa)) mod+- q\<bar>"
      unfolding abs_infty_q_def 
      using to_int_mod_ring_of_int_mod_ring 
      by (smt (verit, best) CARD_a comp_apply mod_plus_minus_def 
        of_int_diff of_int_mod_ring.rep_eq 
        of_int_mod_ring_to_int_mod_ring of_int_of_int_mod_ring)
    also have "\<dots> \<le> round (real_of_int q / real_of_int (2 ^ (d + 1)))" 
    proof -
      have range_to_int_mod_ring: 
        "to_int_mod_ring (poly.coeff (of_qr x) xa) \<in> {0..<q}"
        using to_int_mod_ring_range by auto
      then show ?thesis 
        unfolding abs_infty_q_def Let_def
        using decompress_compress[OF range_to_int_mod_ring assms] 
        by simp
    qed
    finally have "abs_infty_q (poly.coeff (of_qr x) xa - poly.coeff 
      (of_qr (to_qr (?to_Poly (?telescope compress_x)))) xa ) 
      \<le> round (real_of_int q / real_of_int (2 ^ (d + 1)))" by auto
    then show ?thesis unfolding compress_x_def decompress_poly_def 
      compress_poly_def by (auto simp add: o_assoc)
  qed
  moreover have finite: 
    "finite (range (abs_infty_q \<circ> poly.coeff (of_qr (x - ?x'))))" 
    by (metis finite_Max image_comp image_image)
  ultimately show ?thesis unfolding abs_infty_poly_def 
    using Max_le_iff[OF finite] by auto
qed



text \<open>More properties of compress and decompress, used for returning message at the end.\<close>

lemma compress_1:
  shows "compress 1 x \<in> {0,1}"
unfolding compress_def by auto

lemma compress_poly_1:
  shows "\<forall>i. poly.coeff (of_qr (compress_poly 1 x)) i \<in> {0,1}"
proof -
  have "poly.coeff (of_qr (compress_poly 1 x)) i \<in> {0,1}" 
    for i
  proof -
    have "set (map (compress 1) 
      ((map to_int_mod_ring \<circ> coeffs \<circ> of_qr) x)) \<subseteq> {0,1}"
      using compress_1 by auto
    then have "set ((map (compress 1) \<circ> map to_int_mod_ring \<circ> 
      coeffs \<circ> of_qr) x) \<subseteq> {0,1}"
      (is "set (?compressed_1) \<subseteq> _")
      by auto
    then have "set (map (of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) 
      ?compressed_1) \<subseteq> {0,1}"
      (is "set (?of_int_compressed_1)\<subseteq>_")
      by (smt (verit, best) imageE insert_iff of_int_mod_ring_hom.hom_zero 
        of_int_mod_ring_to_int_mod_ring set_map singletonD subsetD subsetI 
        to_int_mod_ring_hom.hom_one)
    then have "nth_default 0 (?of_int_compressed_1) i
       \<in> {0,1}"
       by (smt (verit, best) comp_apply compress_1 compress_zero  
        insert_iff nth_default_map_eq of_int_mod_ring_hom.hom_zero 
        of_int_mod_ring_to_int_mod_ring singleton_iff 
        to_int_mod_ring_hom.hom_one)
    moreover have "Poly (?of_int_compressed_1)
      = Poly (?of_int_compressed_1) mod qr_poly" 
    proof -
      have "degree (Poly (?of_int_compressed_1)) < deg_qr TYPE('a)"
      proof (cases "Poly ?of_int_compressed_1 \<noteq> 0")
      case True
        have "degree (Poly ?of_int_compressed_1) \<le> 
          length (map (of_int_mod_ring :: int \<Rightarrow> 'a mod_ring) 
          ?compressed_1) - 1"
          using deg_Poly'[OF True] by simp
        also have "\<dots> = length ((coeffs \<circ> of_qr) x) - 1" 
          by simp 
        also have "\<dots> < n" unfolding comp_def 
          using length_coeffs_of_qr
          by (metis deg_qr_n deg_of_qr degree_eq_length_coeffs 
          nat_int zless_nat_conj)
        finally have "degree (Poly ?of_int_compressed_1) < n"
        using True \<open>int (length ((coeffs \<circ> of_qr) x) - 1) < n\<close> 
          deg_Poly' by fastforce
        then show ?thesis using deg_qr_n by simp
      next
      case False
        then show ?thesis 
        using deg_qr_pos by auto
      qed
      then show ?thesis
        using deg_mod_qr_poly[of "Poly (?of_int_compressed_1)", 
          symmetric] by auto
    qed
    ultimately show ?thesis unfolding compress_poly_def comp_def
      using of_qr_to_qr[of "Poly (?of_int_compressed_1)"]  
      by auto
  qed
  then show ?thesis by auto
qed
end

lemma of_int_mod_ring_mult:
  "of_int_mod_ring (a*b) = of_int_mod_ring a * of_int_mod_ring b"
unfolding of_int_mod_ring_def
by (metis (mono_tags, lifting) Rep_mod_ring_inverse mod_mult_eq 
  of_int_mod_ring.rep_eq of_int_mod_ring_def times_mod_ring.rep_eq)
  
context kyber_spec
begin
lemma decompress_1: 
  assumes "a\<in>{0,1}"
  shows "decompress 1 a = round(real_of_int q/2) * a" 
unfolding decompress_def using assms by auto 

lemma decompress_poly_1: 
  assumes "\<forall>i. poly.coeff (of_qr x) i \<in> {0,1}"
  shows "decompress_poly 1 x = 
    to_module (round((real_of_int q)/2)) * x"
proof -
  have "poly.coeff (of_qr (decompress_poly 1 x)) i = 
   poly.coeff (of_qr (to_module (round((real_of_int q)/2)) * x)) i"
  for i 
  proof -
    have "set (map to_int_mod_ring (coeffs (of_qr x))) \<subseteq> {0,1}" 
    (is "set (?int_coeffs) \<subseteq> _")
    proof -
      have "set (coeffs (of_qr x)) \<subseteq> {0,1}" using assms 
      by (meson forall_coeffs_conv insert_iff subset_code(1))
      then show ?thesis by auto
    qed
    then have "map (decompress 1) (?int_coeffs) = 
      map ((*) (round (real_of_int q/2))) (?int_coeffs)"
    proof (induct "?int_coeffs")
    case (Cons a xa)
      then show ?case using decompress_1
      by (meson map_eq_conv subsetD)
    qed simp
    then have "poly.coeff (of_qr (decompress_poly 1 x)) i = 
      poly.coeff (of_qr (to_qr (Poly (map of_int_mod_ring
        (map (\<lambda>a. round(real_of_int q/2) * a) 
        (?int_coeffs)))))) i"
      unfolding decompress_poly_def comp_def by presburger
    also have "\<dots> = poly.coeff (of_qr (to_qr (Poly 
        (map (\<lambda>a. of_int_mod_ring ((round(real_of_int q/2)) * a)) 
        (?int_coeffs))))) i"
      using map_map[of of_int_mod_ring "((*) (round (real_of_int q/2)))"]
      by (smt (z3) map_eq_conv o_apply)
    also have "\<dots> = poly.coeff (of_qr (to_qr (Poly 
        (map (\<lambda>a. of_int_mod_ring (round(real_of_int q/2)) * 
        of_int_mod_ring a) (?int_coeffs))))) i"
      by (simp add: of_int_mod_ring_mult[of "(round(real_of_int q/2))"])
    also have "\<dots> = poly.coeff (of_qr (to_qr (Poly 
        (map (\<lambda>a. of_int_mod_ring (round(real_of_int q/2)) * a) 
        (map of_int_mod_ring (?int_coeffs)))))) i"
      using map_map[symmetric, of 
        "(\<lambda>a. of_int_mod_ring (round (real_of_int q/2)) * a ::'a mod_ring)"
        "of_int_mod_ring"] unfolding comp_def by presburger
    also have "\<dots> = poly.coeff (of_qr (to_qr 
        (Polynomial.smult (of_int_mod_ring (round(real_of_int q/2))) 
        (Poly (map of_int_mod_ring (?int_coeffs)))))) i"
      using smult_Poly[symmetric, of 
        "(of_int_mod_ring (round (real_of_int q/2)))"] 
      by metis
    also have "\<dots> = poly.coeff (of_qr ((to_module 
      (round (real_of_int q/2)) * 
      to_qr (Poly (map of_int_mod_ring (?int_coeffs)))))) i"
      unfolding to_module_def 
      using to_qr_smult_to_module
        [of "of_int_mod_ring (round (real_of_int q/2))"]
      by metis
    also have "\<dots> = poly.coeff (of_qr
       (to_module (round (real_of_int q/2)) *
        to_qr (Poly (coeffs (of_qr x)))))i"
      by (subst map_map[of of_int_mod_ring to_int_mod_ring], 
        unfold comp_def)(subst of_int_mod_ring_to_int_mod_ring, auto)
    also have "\<dots> = poly.coeff (of_qr
       (to_module (round (real_of_int q/2)) * x))i"
      by (subst Poly_coeffs) (subst to_qr_of_qr, simp)
    finally show ?thesis by auto
  qed
  then have eq: "of_qr (decompress_poly 1 x) = 
    of_qr (to_module (round((real_of_int q)/2)) * x)"
    by (simp add: poly_eq_iff)
  show ?thesis using arg_cong[OF eq, of "to_qr"] 
    to_qr_of_qr[of "decompress_poly 1 x"] 
    to_qr_of_qr[of "to_module (round (real_of_int q/2)) * x"] 
    by auto
qed
end
text \<open>Compression and decompression for vectors.\<close>

definition map_vector :: 
  "('b \<Rightarrow> 'c) \<Rightarrow> ('b, 'n) vec \<Rightarrow> ('c, 'n::finite) vec" where
  "map_vector f v = (\<chi> i. f (vec_nth v i))"

context kyber_spec 
begin
text \<open>Compression and decompression of vectors in \<open>\<int>_q[X]/(X^n+1)\<close>.\<close>

definition compress_vec :: 
  "nat \<Rightarrow> ('a qr, 'k) vec \<Rightarrow> ('a qr, 'k) vec" where
  "compress_vec d = map_vector (compress_poly d)"

definition decompress_vec :: 
  "nat \<Rightarrow> ('a qr, 'k) vec \<Rightarrow> ('a qr, 'k) vec" where
  "decompress_vec d = map_vector (decompress_poly d)"

end

end
