section \<open>The function $\lceil\log_2 n\rceil$\<close>
theory Ceil_Log2
  imports Complex_Main
begin

definition ceillog2 :: "nat \<Rightarrow> nat" where
  "ceillog2 n = (if n = 0 then 0 else nat \<lceil>log 2 (real n)\<rceil>)"

lemma ceillog2_0 [simp]: "ceillog2 0 = 0"
  and ceillog2_Suc_0 [simp]: "ceillog2 (Suc 0) = 0"
  and ceillog2_2 [simp]: "ceillog2 2 = 1"
  by (auto simp: ceillog2_def)

lemma ceillog2_2_power [simp]: "ceillog2 (2 ^ n) = n"
  by (auto simp: ceillog2_def)

lemma ceillog2_ge_log:
  assumes "n > 0"
  shows   "real (ceillog2 n) \<ge> log 2 (real n)"
proof -
  have "real_of_int \<lceil>log 2 (real n)\<rceil> \<ge> log 2 (real n)"
    by linarith
  thus ?thesis
    using assms unfolding ceillog2_def by auto
qed

lemma ceillog2_less_log:
  assumes "n > 0"
  shows   "real (ceillog2 n) < log 2 (real n) + 1"
proof -
  have "real_of_int \<lceil>log 2 (real n)\<rceil> < log 2 (real n) + 1"
    by linarith
  thus ?thesis
    using assms unfolding ceillog2_def by auto
qed

lemma ceillog2_le_iff:
  assumes "n > 0"
  shows   "ceillog2 n \<le> l \<longleftrightarrow> n \<le> 2 ^ l"
proof -
  have "ceillog2 n \<le> l \<longleftrightarrow> real n \<le> 2 ^ l"
    unfolding ceillog2_def using assms by (auto simp: log_le_iff powr_realpow)
  also have "2 ^ l = real (2 ^ l)"
    by simp
  also have "real n \<le> real (2 ^ l) \<longleftrightarrow> n \<le> 2 ^ l"
    by linarith
  finally show ?thesis .
qed

lemma ceillog2_ge_iff:
  assumes "n > 0"
  shows   "ceillog2 n \<ge> l \<longleftrightarrow> 2 ^ l < 2 * n"
proof -
  have "-1 < (0 :: real)"
    by auto
  also have "\<dots> \<le> log 2 (real n)"
    using assms by auto
  finally have "ceillog2 n \<ge> l \<longleftrightarrow> real l - 1 < log 2 (real n)"
    unfolding ceillog2_def using assms by (auto simp: le_nat_iff le_ceiling_iff)
  also have "\<dots> \<longleftrightarrow> real l < log 2 (real (2 * n))"
    using assms by (auto simp: log_mult)
  also have "\<dots> \<longleftrightarrow> 2 ^ l < real (2 * n)"
    using assms by (subst less_log_iff) (auto simp: powr_realpow)
  also have "2 ^ l = real (2 ^ l)"
    by simp
  also have "real (2 ^ l) < real (2 * n) \<longleftrightarrow> 2 ^ l < 2 * n"
    by linarith
  finally show ?thesis .
qed

lemma le_two_power_ceillog2: "n \<le> 2 ^ ceillog2 n"
proof (cases "n = 0")
  case False
  thus ?thesis
    using ceillog2_le_iff[of n "ceillog2 n"] by simp
qed auto

lemma two_power_ceillog2_gt:
  assumes "n > 0"
  shows   "2 * n > 2 ^ ceillog2 n"
  using ceillog2_ge_iff[of n "ceillog2 n"] assms by simp

lemma ceillog2_eqI:
  assumes "n \<le> 2 ^ l" "2 ^ l < 2 * n"
  shows   "ceillog2 n = l"
proof -
  from assms have "n > 0"
    by (intro Nat.gr0I) auto
  thus ?thesis using assms
    by (intro antisym[of _ l])
       (auto simp: ceillog2_le_iff ceillog2_ge_iff)
qed

lemma ceillog2_rec_even:
  assumes "k > 0"
  shows   "ceillog2 (2 * k) = Suc (ceillog2 k)"
  by (rule ceillog2_eqI) (auto simp: le_two_power_ceillog2 two_power_ceillog2_gt assms)

lemma ceillog2_mono:
  assumes "m \<le> n"
  shows   "ceillog2 m \<le> ceillog2 n"
proof (cases "m = 0")
  case False
  have "\<lceil>log 2 (real m)\<rceil> \<le> \<lceil>log 2 (real n)\<rceil>"
    by (intro ceiling_mono) (use False assms in auto)
  hence "nat \<lceil>log 2 (real m)\<rceil> \<le> nat \<lceil>log 2 (real n)\<rceil>"
    by linarith
  thus ?thesis using False assms
    unfolding ceillog2_def by simp
qed auto
  
lemma ceillog2_rec_odd:
  assumes "k > 0"
  shows   "ceillog2 (Suc (2 * k)) = Suc (ceillog2 (Suc k))"
proof -
  have "ceillog2 (2 * k + 2) \<le> ceillog2 (2 * k + 1)"
    using assms
    by (smt (verit, ccfv_threshold) One_nat_def add_diff_cancel_right' add_gr_0 ceillog2_0 
             ceillog2_le_iff dvd_triv_left le_less_Suc_eq le_two_power_ceillog2 linorder_not_less  
             mult_pos_pos nat_arith.suc1 nat_power_eq_Suc_0_iff not_less_eq_eq numeral_2_eq_2 
             semiring_parity_class.even_mask_iff)
  moreover have "ceillog2 (2 * k + 2) \<ge> ceillog2 (2 * k + 1)"
    by (rule ceillog2_mono) auto
  ultimately have "ceillog2 (2 * k + 2) = ceillog2 (2 * k + 1)"
    by (rule antisym)
  also have "2 * k + 2 = 2 * Suc k"
    by simp
  also have "ceillog2 (2 * Suc k) = Suc (ceillog2 (Suc k))"
    by (rule ceillog2_rec_even) auto
  finally show ?thesis 
    by simp
qed  

(* TODO: better code is possible using bitlen and "count trailing 0 bits" *)
lemma ceillog2_rec:
  "ceillog2 n = (if n \<le> 1 then 0 else 1 + ceillog2 ((n + 1) div 2))"
proof (cases "n \<le> 1")
  case True
  thus ?thesis
    by (cases n) auto
next
  case False
  thus ?thesis
    by (cases "even n") (auto elim!: evenE oddE simp: ceillog2_rec_even ceillog2_rec_odd)
qed

lemmas [code] = ceillog2_rec

end