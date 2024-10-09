(*
  Author: Manuel Eberl, University of Innsbruck

  log2(n) rounded up, for a natural number n
  Compare Discrete.log, floorlog, and many others from the library.
*)
section \<open>Parallel shear sort\<close>
subsection \<open>Auxiliary material\<close>
subsubsection \<open>The $\lceil\log_2 n\rceil$ function\<close>
theory Ceil_Log2
  imports Complex_Main
begin

definition ceillog2 :: "nat \<Rightarrow> nat" where
  "ceillog2 n = (if n = 0 then 0 else nat \<lceil>log 2 (real n)\<rceil>)"

lemma ceillog2_le_1 [simp]: "n \<le> 1 \<Longrightarrow> ceillog2 n = 0"
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
  assumes "n \<le> 2 ^ l" and "2 ^ l < 2 * n"
  shows   "ceillog2 n = l"
proof -
  from assms have "n > 0"
    by (intro Nat.gr0I) auto
  thus ?thesis using assms
    by (intro antisym[of _ l])
       (auto simp: ceillog2_le_iff ceillog2_ge_iff)
qed

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


lemma ceillog2_rec:
  assumes "n > 1"
  shows   "ceillog2 n = Suc (ceillog2 ((n + 1) div 2))"
proof -
  from assms have "log 2 n > 0"
    by force
  have "Suc (ceillog2 ((n + 1) div 2)) = nat (\<lceil>log 2 (real ((n - 1) div 2 + 1))\<rceil>) + 1"
    unfolding ceillog2_def using assms by (cases n) auto
  also have "\<dots> = nat (\<lceil>log 2 (real ((n - 1) div 2 + 1))\<rceil> + 1)"
  proof (subst nat_add_distrib)
    have "log 2 (real ((n - 1) div 2 + 1)) \<ge> 0"
      by force
    thus "\<lceil>log 2 (real ((n - 1) div 2 + 1))\<rceil> \<ge> 0"
      by linarith
  qed auto
  also have "\<dots> = ceillog2 n"
    unfolding ceillog2_def using assms by (subst (2) ceiling_log2_div2) auto
  finally show ?thesis ..
qed

lemma ceillog2_rec_even:
  assumes "k > 0"
  shows   "ceillog2 (2 * k) = Suc (ceillog2 k)"
  by (rule ceillog2_eqI) (auto simp: le_two_power_ceillog2 two_power_ceillog2_gt assms)

lemma ceillog2_rec_odd:
  assumes "k > 0"
  shows   "ceillog2 (Suc (2 * k)) = Suc (ceillog2 (Suc k))"
  using assms by (subst ceillog2_rec) auto

lemma funpow_div2_ceillog2_le_1:
  "((\<lambda>n. (n + 1) div 2) ^^ ceillog2 n) n \<le> 1"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n \<le> 1")
    case True
    thus ?thesis by auto
  next
    case False
    have "((\<lambda>n. (n + 1) div 2) ^^ Suc (ceillog2 ((n + 1) div 2))) n \<le> 1"
      using less.IH[of "(n+1) div 2"] False by (subst funpow_Suc_right) auto
    also have "Suc (ceillog2 ((n + 1) div 2)) = ceillog2 n"
      using False by (subst ceillog2_rec[of n]) auto
    finally show ?thesis .
  qed
qed


fun ceillog2_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "ceillog2_aux acc n = (if n \<le> 1 then acc else ceillog2_aux (acc + 1) ((n + 1) div 2))"

lemmas [simp del] = ceillog2_aux.simps

lemma ceillog2_aux_correct: "ceillog2_aux acc n = ceillog2 n + acc"
proof (induction acc n rule: ceillog2_aux.induct)
  case (1 acc n)
  show ?case
  proof (cases "n \<le> 1")
    case False
    thus ?thesis using ceillog2_rec[of n] "1.IH"
      by (auto simp: ceillog2_aux.simps[of acc n])
  qed (auto simp: ceillog2_aux.simps[of acc n])
qed

lemma ceillog2_code [code]: "ceillog2 n = ceillog2_aux 0 n"
  by (simp add: ceillog2_aux_correct)
(* TODO: better code equation using bit operations *)

end