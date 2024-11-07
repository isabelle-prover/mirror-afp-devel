section \<open>From diagonal to off-diagonal\<close>

theory From_Diagonal
  imports Closer_To_Diagonal

begin

subsection \<open>Lemma 11.2\<close>

definition "ok_fun_11_2a \<equiv> \<lambda>k. \<lceil>real k powr (3/4)\<rceil> * log 2 k"

definition "ok_fun_11_2b \<equiv> \<lambda>\<mu> k. k powr (39/40) * (log 2 \<mu> + 3 * log 2 k)"

definition "ok_fun_11_2c \<equiv> \<lambda>\<mu> k. - k * log 2 (1 - (2 / (1-\<mu>)) * k powr (-1/40))"

definition "ok_fun_11_2 \<equiv> \<lambda>\<mu> k. 2 - ok_fun_71 \<mu> k + ok_fun_11_2a k
      + max (ok_fun_11_2b \<mu> k) (ok_fun_11_2c \<mu> k)"

lemma ok_fun_11_2a: "ok_fun_11_2a \<in> o(real)"
  unfolding ok_fun_11_2a_def
  by real_asymp

text \<open>possibly, the functions that depend upon @{term \<mu>} need a more refined analysis to cover 
a closed interval of possible values. But possibly not, as the text implies @{term "\<mu>=2/5"}.\<close>

lemma ok_fun_11_2b: "ok_fun_11_2b \<mu> \<in> o(real)"
  unfolding ok_fun_11_2b_def by real_asymp

lemma ok_fun_11_2c: "ok_fun_11_2c \<mu> \<in> o(real)"
unfolding ok_fun_11_2c_def
  by real_asymp

lemma ok_fun_11_2:
  assumes "0<\<mu>" "\<mu><1" 
  shows "ok_fun_11_2 \<mu> \<in> o(real)"
  unfolding ok_fun_11_2_def
  by (simp add: assms const_smallo_real maxmin_in_smallo ok_fun_11_2a ok_fun_11_2b ok_fun_11_2c ok_fun_71 sum_in_smallo)


definition "Big_From_11_2 \<equiv>     
   \<lambda>\<mu> k. Big_ZZ_8_6 \<mu> k \<and> Big_X_7_1 \<mu> k \<and> Big_Y_6_2 \<mu> k \<and> Big_Red_5_3 \<mu> k \<and> Big_Blue_4_1 \<mu> k 
       \<and> 1 \<le> \<mu>^2 * real k \<and> 2 / (1-\<mu>) * real k powr (-1/40) < 1 \<and> 1/k < 1/2 - 3 * eps k"

lemma Big_From_11_2:
  assumes "0<\<mu>0" "\<mu>0 \<le> \<mu>1" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>k. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_From_11_2 \<mu> k"
proof -
  have A: "\<forall>\<^sup>\<infinity>k. \<forall>\<mu>. \<mu>0 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> 1 \<le> \<mu>\<^sup>2 * k"
  proof (intro eventually_all_geI0)
    show *: "\<forall>\<^sup>\<infinity>x. 1 \<le> \<mu>0\<^sup>2 * real x"
      using \<open>0<\<mu>0\<close> by real_asymp
  next
    fix k \<mu>
    assume "1 \<le> \<mu>0\<^sup>2 * real k" and "\<mu>0 \<le> \<mu>" "\<mu> \<le> \<mu>1"
    with \<open>0<\<mu>0\<close> show "1 \<le> \<mu>\<^sup>2 * k"
      by (smt (verit, ccfv_SIG) mult_le_cancel_right of_nat_less_0_iff power_mono)
  qed
  have B: "\<forall>\<^sup>\<infinity>k. \<forall>\<mu>. \<mu>0 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> 2 / (1-\<mu>) * k powr (-1/40) < 1"
  proof (intro eventually_all_geI1)
    show "\<forall>\<^sup>\<infinity>k. 2 / (1-\<mu>1) * k powr (-1/40) < 1"
      by real_asymp
  qed (use assms in auto)
  have C: "\<forall>\<^sup>\<infinity>k. 1/k < 1/2 - 3 * eps k"
    unfolding eps_def by real_asymp
  show ?thesis
    unfolding Big_From_11_2_def
    using assms Big_ZZ_8_6 Big_X_7_1 Big_Y_6_2 Big_Red_5_3 Big_Blue_4_1 A B C
    by (simp add: eventually_conj_iff all_imp_conj_distrib)  
qed

text \<open>Simply to prevent issues about the positioning of the function @{term real}\<close>
abbreviation "ratio \<equiv> \<lambda>\<mu> s t. \<mu> * (real s + real t) / real s"

text \<open>the text refers to the actual Ramsey number but I don't see how that could work.
Theorem 11.1 will define @{term n} to be one less than the Ramsey number, hence we add that one back here.\<close>
lemma (in Book) From_11_2:
  assumes "l=k"  
  assumes big: "Big_From_11_2 \<mu> k"
  defines "\<R> \<equiv> Step_class {red_step}" and "\<S> \<equiv> Step_class {dboost_step}"
  defines "t \<equiv> card \<R>" and "s \<equiv> card \<S>"
  defines "nV' \<equiv> Suc nV"
  assumes 0: "card X0 \<ge> nV div 2" and "p0 \<ge> 1/2"
  shows "log 2 nV' \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (ratio \<mu> s t) + ok_fun_11_2 \<mu> k"
proof -
  have big71: "Big_X_7_1 \<mu> k" and big62: "Big_Y_6_2 \<mu> k" and big86: "Big_ZZ_8_6 \<mu> k" and big53: "Big_Red_5_3 \<mu> k"
    and big41: "Big_Blue_4_1 \<mu> k" and big\<mu>: "1 \<le> \<mu>^2 * real k"
    and big_le1: "2 / (1-\<mu>) * real k powr (-1/40) < 1"
    using big by (auto simp: Big_From_11_2_def)
  have big\<mu>1: "1 \<le> \<mu> * real k"
    using big\<mu> \<mu>01
    by (smt (verit, best) mult_less_cancel_right2 mult_right_mono of_nat_less_0_iff power2_eq_square)
  then have log2\<mu>k: "log 2 \<mu> + log 2 k \<ge> 0"
    using kn0 \<mu>01 add_log_eq_powr by auto
  have big\<mu>2: "1 \<le> \<mu> * (real k)\<^sup>2"
    unfolding power2_eq_square by (smt (verit, ccfv_SIG) big\<mu>1 \<mu>01 mult_less_cancel_left1 mult_mono')
  define g where "g \<equiv> \<lambda>k. \<lceil>real k powr (3/4)\<rceil> * log 2 k"
  have g: "g \<in> o(real)"
    unfolding g_def by real_asymp
  have bb_gt0: "bigbeta > 0"
    using big53 bigbeta_gt0 \<open>l=k\<close> by blast
  have "t < k"
    by (simp add: \<R>_def t_def red_step_limit)
  have "s < k"
    unfolding \<S>_def s_def
    using bblue_dboost_step_limit big41 \<open>l=k\<close> by fastforce  

  have k34: "k powr (3/4) \<le> k powr 1"
    using kn0 by (intro powr_mono) auto

  define g712 where "g712 \<equiv> \<lambda>k. 2 - ok_fun_71 \<mu> k + g k"
  have "nV' \<ge> 2"
    using gorder_ge2 nV'_def by linarith
  have "nV' \<le> 4 * card X0"
    using 0 card_XY0 by (auto simp: nV'_def odd_iff_mod_2_eq_one)
  with \<mu>01 have "2 powr (ok_fun_71 \<mu> k - 2) * \<mu>^k * (1-\<mu>) ^ t * (bigbeta / \<mu>) ^ s * nV'
      \<le> 2 powr ok_fun_71 \<mu> k * \<mu>^k * (1-\<mu>) ^ t * (bigbeta / \<mu>) ^ s * card X0"
    using \<mu>01 by (simp add: powr_diff mult.assoc bigbeta_ge0 mult_left_mono)
  also have "\<dots> \<le> card (Xseq halted_point)"
    using X_7_1 assms big71 by blast
  also have "\<dots> \<le> 2 powr (g k)"
  proof -
    have "1/k < p0 - 3 * \<epsilon>"
    using big \<open>p0 \<ge> 1/2\<close> by (auto simp: Big_From_11_2_def)
    also have "\<dots> \<le> pee halted_point"
      using Y_6_2_halted big62 assms by blast
    finally have "pee halted_point > 1/k" .
    moreover have "termination_condition (Xseq halted_point) (Yseq halted_point)"
      using halted_point_halted step_terminating_iff by blast
    ultimately have "card (Xseq halted_point) \<le> RN k (nat \<lceil>real k powr (3/4)\<rceil>)"
      using \<open>l=k\<close> pee_def termination_condition_def by auto
    then show ?thesis
      unfolding g_def by (smt (verit) RN34_le_2powr_ok kn0 of_nat_le_iff)
  qed
  finally have 58: "2 powr (g k) \<ge> 2 powr (ok_fun_71 \<mu> k - 2) * \<mu>^k * (1-\<mu>) ^ t * (bigbeta / \<mu>) ^ s * nV'" .
  then have 59: "nV' \<le> 2 powr (g712 k) * (1/\<mu>) ^ k * (1 / (1-\<mu>)) ^ t * (\<mu> / bigbeta) ^ s"
    using \<mu>01 bb_gt0 by (simp add: g712_def powr_diff powr_add mult.commute divide_simps) argo

  define a where "a \<equiv> 2 / (1-\<mu>)"
  have ok_less1: "a * real k powr (-1/40) < 1"
    unfolding a_def using big_le1 by blast
  consider "s < k powr (39/40)" | "s \<ge> k powr (39/40)" "bigbeta \<ge> (1 - a * k powr (-1/40)) * (s / (s + t))"
    using ZZ_8_6 big86 a_def \<open>l=k\<close> by (force simp: s_def t_def \<S>_def \<R>_def)
  then show ?thesis
  proof cases
    case 1
    define h where "h \<equiv> \<lambda>c k. real k powr (39/40) * (log 2 \<mu> + real c * log 2 (real k))"
    have h: "h c \<in> o(real)" for c
      unfolding h_def by real_asymp

    have le_h: "\<bar>s * log 2 (ratio \<mu> s t)\<bar> \<le> h 1 k"
    proof (cases "s>0")
      case True
      with \<open>s>0\<close> have \<mu>eq: "ratio \<mu> s t = \<mu> * (1 + t/s)"
        by (auto simp: distrib_left add_divide_distrib)
      show ?thesis 
      proof (cases "log 2 (ratio \<mu> s t) \<le> 0")
        case True
        have "s * (- log 2 (\<mu> * (1 + t/s))) \<le> real k powr (39/40) * (log 2 \<mu> + log 2 (real k))"
        proof (intro mult_mono)
          show "s \<le> k powr (39 / 40)"
            using "1" by linarith
        next
          have "inverse (\<mu> * (1 + t/s)) \<le> inverse \<mu>"
            using \<mu>01 inverse_le_1_iff by fastforce
          also have "\<dots> \<le> \<mu> * k"
            using big\<mu> \<mu>01 by (metis neq_iff mult.assoc mult_le_cancel_left_pos power2_eq_square right_inverse)
          finally have "inverse (\<mu> * (1 + t/s)) \<le> \<mu> * k" .
          moreover have "0 < \<mu> * (1 + real t / real s)"
            using \<mu>01 \<open>0 < s\<close> by (simp add: zero_less_mult_iff add_num_frac)
          ultimately have "- log 2 (\<mu> * (1 + real t / real s)) \<le> log 2 (\<mu> * k)"
            using \<mu>01 kn0 by (simp add: zero_less_mult_iff flip: log_inverse log_mult)
          then show "- log 2 (\<mu> * (1 + real t / real s)) \<le> log 2 \<mu> + log 2 (real k)"
            using \<open>\<mu>>0\<close> kn0 log_mult by fastforce
        qed (use True \<mu>eq in auto)
        with \<open>s>0\<close> big\<mu>1 True show ?thesis
          by (simp add: \<mu>eq h_def mult_le_0_iff)
      next
        case False
        have lek: "1 + t/s \<le> k"
        proof -
          have "real t \<le> real t * real s"
            using True mult_le_cancel_left1 by fastforce
          then have "1 + t/s \<le> 1 + t"
            by (simp add: True pos_divide_le_eq)
          also have "\<dots> \<le> k"
            using \<open>t < k\<close> by linarith
          finally show ?thesis .
        qed
        have "\<bar>s * log 2 (ratio \<mu> s t)\<bar> \<le> k powr (39/40) * log 2 (ratio \<mu> s t)"
          using False "1" by auto
        also have "\<dots> = k powr (39/40) * (log 2 (\<mu> * (1 + t/s)))"
          by (simp add: \<mu>eq)
        also have "\<dots> = k powr (39/40) * (log 2 \<mu> + log 2 (1 + t/s))"
          using \<mu>01 by (smt (verit, best) divide_nonneg_nonneg log_mult of_nat_0_le_iff) 
        also have "\<dots> \<le> k powr (39/40) * (log 2 \<mu> + log 2 k)"
          by (smt (verit, best) "1" Transcendental.log_mono divide_nonneg_nonneg lek 
              mult_le_cancel_left_pos of_nat_0_le_iff)
        also have "\<dots> \<le> h 1 k"
          unfolding h_def using kn0 by force
        finally show ?thesis .
      qed 
    qed (use log2\<mu>k h_def in auto)

    have \<beta>: "bigbeta \<ge> 1 / (real k)\<^sup>2"
      using big53 bigbeta_ge_square \<open>l=k\<close> by blast
    then have "(\<mu> / bigbeta) ^ s \<le> (\<mu> * (real k)\<^sup>2) ^ s"
      using bb_gt0 kn0 \<mu>01 by (intro power_mono) (auto simp: divide_simps mult.commute)
    also have "\<dots> \<le> (\<mu> * (real k)\<^sup>2) powr (k powr (39/40))"
      using \<mu>01 big\<mu>2 1 by (smt (verit) powr_less_mono powr_one_eq_one powr_realpow)
    also have "\<dots> = 2 powr (log 2 ((\<mu> * (real k)\<^sup>2) powr (k powr (39/40))))"
      by (smt (verit, best) big\<mu>2 powr_gt_zero powr_log_cancel)
    also have "\<dots> = 2 powr h 2 k"
      using \<mu>01 big\<mu>2 kn0 by (simp add: log_powr log_nat_power log_mult h_def)
    finally have \<dagger>: "(\<mu> / bigbeta) ^ s \<le> 2 powr h 2 k" .
    have \<ddagger>: "nV' \<le> 2 powr (g712 k) * (1/\<mu>) ^ k * (1 / (1-\<mu>)) ^ t * 2 powr h 2 k"
      using 59 mult_left_mono [OF \<dagger>, of "2 powr (g712 k) * (1/\<mu>) ^ k * (1 / (1-\<mu>)) ^ t"]
      by (smt (verit) \<mu>01 pos_prod_le powr_nonneg_iff zero_less_divide_iff zero_less_power)
    have *: "log 2 nV' \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + (g712 k + h 2 k)"
      using \<mu>01 \<open>nV' \<ge> 2\<close> by (simp add: log_mult log_nat_power order.trans [OF Transcendental.log_mono [OF _ _ \<ddagger>]])

    show ?thesis
    proof -
      have le_ok_fun: "g712 k + h 3 k \<le> ok_fun_11_2 \<mu> k"
        by (simp add: g712_def h_def ok_fun_11_2_def g_def ok_fun_11_2a_def ok_fun_11_2b_def)
      have h3: "h 3 k = h 1 k + h 2 k - real k powr (39/40) * log 2 \<mu>"
        by (simp add: h_def algebra_simps)
      have "0 \<le> h 1 k + s * log 2 ((\<mu> * real s + \<mu> * real t) / s)"
        by (smt (verit, del_insts) of_nat_add distrib_left le_h)
      moreover have "log 2 \<mu> < 0"
        using \<mu>01 by simp
      ultimately have "g712 k + h 2 k \<le> s * log 2 (ratio \<mu> s t) + ok_fun_11_2 \<mu> k"
        by (smt (verit, best) kn0 distrib_left h3 le_ok_fun nat_neq_iff of_nat_eq_0_iff pos_prod_lt powr_gt_zero)
      then show "log 2 nV' \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (ratio \<mu> s t) + ok_fun_11_2 \<mu> k"
        using "*" by linarith
    qed
  next
    case 2
    then have "s > 0"
      using kn0 powr_gt_zero by fastforce
    define h where "h \<equiv> \<lambda>k. real k * log 2 (1 - a * k powr (-1/40))"
    have "s * log 2 (\<mu> / bigbeta) = s * log 2 \<mu> - s * log 2 (bigbeta)"
      using \<mu>01 bb_gt0 2 by (simp add: log_divide algebra_simps)
    also have "\<dots> \<le> s * log 2 \<mu> - s * log 2 ((1 - a * k powr (-1/40)) * (s / (s + t)))"
      using 2 \<open>s>0\<close> ok_less1 by (intro diff_mono order_refl mult_left_mono Transcendental.log_mono) auto
    also have "\<dots> = s * log 2 \<mu> - s * (log 2 (1 - a * k powr (-1/40)) + log 2 (s / (s + t)))"
      using \<open>0 < s\<close> a_def add_log_eq_powr big_le1 by auto
    also have "\<dots> = s * log 2 (ratio \<mu> s t) - s * log 2 (1 - a * k powr (-1/40))"
      using \<open>0 < \<mu>\<close> \<open>0 < s\<close> minus_log_eq_powr by (auto simp flip: right_diff_distrib')
    also have "\<dots> < s * log 2 (ratio \<mu> s t) - h k"
    proof -
      have "log 2 (1 - a * real k powr (-1/40)) < 0"
        using \<mu>01 kn0 a_def ok_less1 by auto
      with \<open>s<k\<close> show ?thesis
        by (simp add: h_def)
    qed
    finally have \<dagger>: "s * log 2 (\<mu> / bigbeta) < s * log 2 (ratio \<mu> s t) - h k" .
    show ?thesis
    proof -
      have le_ok_fun: "g712 k - h k \<le> ok_fun_11_2 \<mu> k"
        by (simp add: g712_def h_def ok_fun_11_2_def g_def ok_fun_11_2a_def a_def ok_fun_11_2c_def)
      have "log 2 nV' \<le> s * log 2 (\<mu> / bigbeta) + k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + (g712 k)"
      proof (intro order.trans [OF Transcendental.log_mono [OF _ _ 59]])
        show "log 2 (2 powr g712 k * (1/\<mu>) ^ k * (1 / (1-\<mu>)) ^ t * (\<mu> / bigbeta) ^ s)
            \<le> s * log 2 (\<mu> / bigbeta) + k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + g712 k"
          using bb_gt0 \<mu>01 by (simp add: log_mult log_nat_power)
      qed (use \<open>nV' \<ge> 2\<close> in auto)
      with \<dagger> le_ok_fun show "log 2 nV' \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (ratio \<mu> s t) + ok_fun_11_2 \<mu> k"
        by simp
    qed
  qed
qed

subsection \<open>Lemma 11.3\<close>

text \<open>same remark as in Lemma 11.2 about the use of the Ramsey number in the conclusion\<close>
lemma (in Book) From_11_3:
  assumes "l=k"  
  assumes big: "Big_Y_6_1 \<mu> k"
  defines "\<R> \<equiv> Step_class {red_step}" and "\<S> \<equiv> Step_class {dboost_step}"
  defines "t \<equiv> card \<R>" and "s \<equiv> card \<S>"
  defines "nV' \<equiv> Suc nV"
  assumes 0: "card Y0 \<ge> nV div 2" and "p0 \<ge> 1/2"
  shows "log 2 nV' \<le> log 2 (RN k (k-t)) + s + t + 2 - ok_fun_61 k"
proof -
  define RS where "RS \<equiv> Step_class {red_step,dboost_step}"
  have "RS = \<R> \<union> \<S>"
    using Step_class_insert \<R>_def \<S>_def RS_def by blast
  moreover obtain "finite \<R>" "finite \<S>"
    by (simp add: \<R>_def \<S>_def)
  moreover have "disjnt \<R> \<S>"
    using \<R>_def \<S>_def disjnt_Step_class by auto
  ultimately have card_RS: "card RS = t+s"
    by (simp add: t_def s_def card_Un_disjnt)
  have 4: "nV'/4 \<le> card Y0"
    using 0 card_XY0 by (auto simp: nV'_def odd_iff_mod_2_eq_one)
  have ge0: "0 \<le> 2 powr ok_fun_61 k * p0 ^ card RS"
    using p0_01 by fastforce
  have "nV' \<ge> 2"
    using gorder_ge2 nV'_def by linarith
  have "2 powr (- real s - real t + ok_fun_61 k - 2) * nV' = 2 powr (ok_fun_61 k - 2) * (1/2) ^ card RS * nV'"
    by (simp add: powr_add powr_diff powr_minus power_add powr_realpow divide_simps card_RS)
  also have "\<dots> \<le> 2 powr (ok_fun_61 k - 2) * p0 ^ card RS * nV'"
    using power_mono [OF \<open>p0 \<ge> 1/2\<close>] \<open>nV' \<ge> 2\<close> by auto
  also have "\<dots> \<le> 2 powr (ok_fun_61 k) * p0 ^ card RS * (nV'/4)"
    by (simp add: divide_simps powr_diff split: if_split_asm)
  also have "\<dots> \<le> 2 powr (ok_fun_61 k) * p0 ^ card RS * card Y0"
    using   mult_left_mono [OF 4 ge0 ] by simp
  also have "\<dots> \<le> card (Yseq halted_point)"
    using Y_6_1 big \<open>l=k\<close> by (auto simp: RS_def divide_simps split: if_split_asm)
  finally have "2 powr (- real s - real t + ok_fun_61 k - 2) * nV' \<le> card (Yseq halted_point)" .
  moreover
  { assume "card (Yseq halted_point) \<ge> RN k (k-t)"
    then obtain K where K: "K \<subseteq> Yseq halted_point" and "size_clique (k-t) K Red \<or> size_clique k K Blue"
      by (metis RN_commute Red_Blue_RN Yseq_subset_V)
    then have KRed: "size_clique (k-t) K Red"
      using \<open>l=k\<close> no_Blue_clique by blast
    have "card (K \<union> Aseq halted_point) = k"
    proof (subst card_Un_disjnt)
      show "finite K" "finite (Aseq halted_point)"
        using K finite_Aseq finite_Yseq infinite_super by blast+
      show "disjnt K (Aseq halted_point)"
        using valid_state_seq[of halted_point] K disjnt_subset1
        by (auto simp: valid_state_def disjoint_state_def)
      have "card (Aseq halted_point) = t"
        using red_step_eq_Aseq \<R>_def t_def by presburger
      then show "card K + card (Aseq halted_point) = k"
        using Aseq_less_k[OF] nat_less_le KRed size_clique_def by force
    qed
    moreover have "clique (K \<union> Aseq halted_point) Red"
    proof -
      obtain "K \<subseteq> V" "Aseq halted_point \<subseteq> V"
        by (meson Aseq_subset_V KRed size_clique_def)
      moreover have "clique K Red"
        using KRed size_clique_def by blast
      moreover have "clique (Aseq halted_point) Red"
        by (meson A_Red_clique valid_state_seq)
      moreover have "all_edges_betw_un (Aseq halted_point) (Yseq halted_point) \<subseteq> Red"
        using valid_state_seq[of halted_point] K
        by (auto simp: valid_state_def RB_state_def all_edges_betw_un_Un2)
      then have "all_edges_betw_un K (Aseq halted_point) \<subseteq> Red"
        using K all_edges_betw_un_mono2 all_edges_betw_un_commute by blast
      ultimately show ?thesis
        by (simp add: local.clique_Un)
    qed
    ultimately have "size_clique k (K \<union> Aseq halted_point) Red"
      using KRed Aseq_subset_V by (auto simp: size_clique_def)
    then have False
      using no_Red_clique by blast
  } 
  ultimately have *: "2 powr (- real s - real t + ok_fun_61 k - 2) * nV' < RN k (k-t)"
    by fastforce
  have "- real s - real t + ok_fun_61 k - 2 + log 2 nV' = log 2 (2 powr (- real s - real t + ok_fun_61 k - 2) * nV')"
    using add_log_eq_powr \<open>nV' \<ge> 2\<close> by auto
  also have "\<dots> \<le> log 2 (RN k (k-t))"
    using "*" Transcendental.log_mono \<open>nV' \<ge> 2\<close> less_eq_real_def by auto
  finally show "log 2 nV' \<le> log 2 (RN k (k - t)) + real s + real t + 2 - ok_fun_61 k"
    by linarith
qed

subsection \<open>Theorem 11.1\<close>

(* actually it is undefined when k=0 or x=1; Lean puts ln(0) = 0.
   AND IT DEPENDS UPON k!!*)
definition FF :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "FF \<equiv> \<lambda>k x y. log 2 (RN k (nat\<lfloor>real k - x * real k\<rfloor>)) / real k + x + y"

definition GG :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "GG \<equiv> \<lambda>\<mu> x y. log 2 (1/\<mu>) + x * log 2 (1/(1-\<mu>)) + y * log 2 (\<mu> * (x+y) / y)"

definition FF_bound :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "FF_bound \<equiv> \<lambda>k u. FF k 0 u + 1"

lemma log2_RN_ge0: "0 \<le> log 2 (RN k k) / k"
proof (cases "k=0")
  case False
  then have "RN k k \<ge> 1"
    by (simp add: RN_eq_0_iff leI)
  then show ?thesis
    by simp
qed auto

(* even with ln(0) = 0, the singularity requires its own case*)
lemma le_FF_bound:
  assumes x: "x \<in> {0..1}" and "y \<in> {0..u}" 
  shows "FF k x y \<le> FF_bound k u"
proof (cases "\<lfloor>k - x*k\<rfloor> = 0")
  case True  \<comment>\<open>to handle the singularity\<close>
  with assms log2_RN_ge0[of k] show ?thesis
    by (simp add: True FF_def FF_bound_def log_def)
next
  case False
  with gr0I have "k>0" by fastforce
  with False assms have *: "0 < \<lfloor>k - x*k\<rfloor>"
    using linorder_neqE_linordered_idom by fastforce
  have le_k: "k - x*k \<le> k"
    using x by auto
  then have le_k: "nat \<lfloor>k - x*k\<rfloor> \<le> k"
    by linarith
  have "log 2 (RN k (nat \<lfloor>k - x*k\<rfloor>)) / k \<le> log 2 (RN k k) / k"
  proof (intro divide_right_mono Transcendental.log_mono)
    show "0 < real (RN k (nat \<lfloor>k - x*k\<rfloor>))"
      by (metis RN_eq_0_iff \<open>k>0\<close> gr_zeroI * of_nat_0_less_iff zero_less_nat_eq) 
  qed (auto simp: RN_mono le_k)
  then show ?thesis
    using assms False le_SucE by (fastforce simp: FF_def FF_bound_def)
qed

lemma FF2: "y' \<le> y \<Longrightarrow> FF k x y' \<le> FF k x y"
  by (simp add: FF_def)

lemma FF_GG_bound:
  assumes \<mu>: "0 < \<mu>" "\<mu> < 1" and x: "x \<in> {0..1}" and y: "y \<in> {0..\<mu> * x / (1-\<mu>) + \<eta>}" 
  shows "min (FF k x y) (GG \<mu> x y) + \<eta> \<le> FF_bound k (\<mu> / (1-\<mu>) + \<eta>) + \<eta>"
proof -
  have FF_ub: "FF k x y \<le> FF_bound k (\<mu> / (1-\<mu>) + \<eta>)"
  proof (rule order.trans)
    show "FF k x y \<le> FF_bound k y"
      using x y by (simp add: le_FF_bound)
  next
    have "y \<le> \<mu> / (1-\<mu>) + \<eta>"
      using x y \<mu> by simp (smt (verit, best) frac_le mult_left_le)
    then show "FF_bound k y \<le> FF_bound k (\<mu> / (1-\<mu>) + \<eta>)"
      by (simp add: FF_bound_def FF_def)
  qed
  show ?thesis
    using FF_ub by auto
qed

context P0_min
begin 

definition "ok_fun_11_1 \<equiv> \<lambda>\<mu> k. max (ok_fun_11_2 \<mu> k) (2 - ok_fun_61 k)"

lemma ok_fun_11_1:
  assumes "0<\<mu>" "\<mu><1" 
  shows "ok_fun_11_1 \<mu> \<in> o(real)"
  unfolding ok_fun_11_1_def
  by (simp add: assms const_smallo_real maxmin_in_smallo ok_fun_11_2 ok_fun_61 sum_in_smallo)

lemma eventually_ok111_le_\<eta>:
  assumes "\<eta> > 0" and \<mu>: "0<\<mu>" "\<mu><1" 
  shows "\<forall>\<^sup>\<infinity>k. ok_fun_11_1 \<mu> k / k \<le> \<eta>"
proof -
  have "(\<lambda>k. ok_fun_11_1 \<mu> k / k) \<in> o(\<lambda>k. 1)"
    using eventually_mono ok_fun_11_1 [OF \<mu>] by (fastforce simp: smallo_def divide_simps)
  with assms have "\<forall>\<^sup>\<infinity>k. \<bar>ok_fun_11_1 \<mu> k\<bar> / k \<le> \<eta>"
    by (auto simp: smallo_def)
  then show ?thesis
    by (metis (mono_tags, lifting) eventually_mono abs_divide abs_le_D1 abs_of_nat)
qed

lemma eventually_powr_le_\<eta>:
  assumes "\<eta> > 0" 
  shows "\<forall>\<^sup>\<infinity>k. (2 / (1-\<mu>)) * k powr (-1/20) \<le> \<eta>"
  using assms by real_asymp

definition "Big_From_11_1 \<equiv> 
   \<lambda>\<eta> \<mu> k. Big_From_11_2 \<mu> k \<and> Big_ZZ_8_5 \<mu> k \<and> Big_Y_6_1 \<mu> k \<and> ok_fun_11_1 \<mu> k / k \<le> \<eta>/2
         \<and> (2 / (1-\<mu>)) * k powr (-1/20) \<le> \<eta>/2 
         \<and> Big_Closer_10_1 (1/101) (nat\<lceil>k/100\<rceil>) \<and> 3 / (k * ln 2) \<le> \<eta>/2 \<and> k\<ge>3"

text \<open>In sections 9 and 10 (and by implication all proceeding sections), we needed to consider 
  a closed interval of possible values of @{term \<mu>}. Let's hope, maybe not here. 
The fact below can only be proved with the strict inequality @{term "\<eta> > 0"}, 
which is why it is also strict in the theorems depending on this property.\<close>
lemma Big_From_11_1:
  assumes "\<eta> > 0" "0<\<mu>" "\<mu><1" 
  shows "\<forall>\<^sup>\<infinity>k. Big_From_11_1 \<eta> \<mu> k"
proof -
  have "\<forall>\<^sup>\<infinity>l. Big_Closer_10_1 (1/101) l"
    by (rule Big_Closer_10_1) auto
  then have a: "\<forall>\<^sup>\<infinity>k. Big_Closer_10_1 (1/101) (nat\<lceil>k/100\<rceil>)"
    unfolding eventually_sequentially
    by (meson le_divide_eq_numeral1(1) le_natceiling_iff nat_ceiling_le_eq)
  have b: "\<forall>\<^sup>\<infinity>k. 3 / (k * ln 2) \<le> \<eta>/2"
    using \<open>\<eta>>0\<close> by real_asymp
  show ?thesis
  unfolding Big_From_11_1_def
  using assms a b Big_From_11_2[of \<mu> \<mu>] Big_ZZ_8_5[of \<mu> \<mu>] Big_Y_6_1[of \<mu> \<mu>]
  using eventually_ok111_le_\<eta>[of "\<eta>/2"] eventually_powr_le_\<eta> [of "\<eta>/2"]
  by (auto simp: eventually_conj_iff all_imp_conj_distrib eventually_sequentially)
qed

text \<open>The actual proof of theorem 11.1 is now combined with the development of section 12,
since the concepts seem to be inescapably mixed up.\<close>

end (*P0_min*)

end
