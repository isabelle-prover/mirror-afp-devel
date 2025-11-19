section \<open>Generalised pentagonal numbers\<close>
theory Pentagonal_Numbers
  imports Main "HOL-Library.FuncSet"
begin

text \<open>
  The pentagonal numbers are defined as a sequence of natural numbers $(g_k)_{n\in\mathbb{N}}$ 
  with $g_k = \frac{1}{2} k(3k-1)$. Visually, they count the number of spheres needed to 
  fill a pentagon where each side consists of $k$ spheres -- similarly to how $k^2$ is the number
  of spheres needed to fill up a square with $k$ spheres on each side.

  We define the \<^emph>\<open>generalised\<close> pentagonal numbers, where the only difference is that $k$ may also
  be negative~\oeiscite{A001318}.

  The function $g_k$ (with $k\in\mathbb{Z}$) is injective, since we have:
  \[g_0 < g_1 < g_{-1} < g_2 < g_{-2} < g_3 < g_{-3} < \ldots\]
\<close>
definition pent_num :: "int \<Rightarrow> nat" where
  "pent_num k = nat (k * (3 * k - 1) div 2)"

definition pent_nums :: "nat set" where
  "pent_nums = range pent_num"

lemma pent_num_0 [simp]: "pent_num 0 = 0"
  by (simp add: pent_num_def)

lemma pent_num_in_pent_nums [intro]: "pent_num k \<in> pent_nums"
  unfolding pent_nums_def by blast

lemma twice_pent_num_eq: "2 * int (pent_num k) = k * (3 * k - 1)"
proof -
  have "k * (3 * k - 1) \<ge> 0"
  proof (cases "k > 0")
    case True
    thus ?thesis
      by (intro mult_nonneg_nonneg) auto
  next
    case False
    thus ?thesis
      by (intro mult_nonpos_nonpos) auto
  qed
  thus ?thesis
    unfolding pent_num_def by simp
qed

lemma strict_mono_pent_num:
  assumes "0 \<le> m" "m < n"
  shows   "pent_num m < pent_num n"
proof -
  have "2 * int (pent_num m) < 2 * int (pent_num n)"
  proof -
    have "m * (3 * m - 1) \<le> m * (3 * n - 1)"
      by (intro mult_left_mono) (use assms in auto)
    also have "\<dots> < n * (3 * n - 1)"
      by (intro mult_strict_right_mono) (use assms in auto)
    finally show ?thesis
      unfolding twice_pent_num_eq by simp
  qed
  thus ?thesis
    by simp
qed

lemma pent_num_less_iff_nonneg:
  assumes "i \<ge> 0" "j \<ge> 0"
  shows   "pent_num i < pent_num j \<longleftrightarrow> i < j"
  by (cases i j rule: linorder_cases)
     (use assms strict_mono_pent_num[of i j] strict_mono_pent_num[of j i] in auto)

lemma pent_num_le_iff_nonneg:
  assumes "i \<ge> 0" "j \<ge> 0"
  shows   "pent_num i \<le> pent_num j \<longleftrightarrow> i \<le> j"
  by (cases i j rule: linorder_cases)
     (use assms strict_mono_pent_num[of i j] strict_mono_pent_num[of j i] in auto)

lemma mono_pent_num:
  assumes "0 \<le> m" "m \<le> n"
  shows   "pent_num m \<le> pent_num n"
  using strict_mono_pent_num[of m n] assms by (cases "m = n") auto

lemma strict_antimono_pent_num:
  assumes "m < n" "n \<le> 0"
  shows   "pent_num m > pent_num n"
proof -
  have "2 * int (pent_num m) > 2 * int (pent_num n)"
  proof -
    have "n * (3 * n - 1) \<le> n * (3 * m - 1)"
      by (intro mult_left_mono_neg) (use assms in auto)
    also have "\<dots> < m * (3 * m - 1)"
      by (intro mult_strict_right_mono_neg) (use assms in auto)
    finally show ?thesis
      unfolding twice_pent_num_eq by simp
  qed
  thus ?thesis
    by simp
qed


lemma pent_num_less_iff_nonpos:
  assumes "i \<le> 0" "j \<le> 0"
  shows   "pent_num i < pent_num j \<longleftrightarrow> i > j"
  by (cases i j rule: linorder_cases)
     (use assms strict_antimono_pent_num[of i j] strict_antimono_pent_num[of j i] in auto)

lemma pent_num_le_iff_nonpos:
  assumes "i \<le> 0" "j \<le> 0"
  shows   "pent_num i \<le> pent_num j \<longleftrightarrow> i \<ge> j"
  by (cases i j rule: linorder_cases)
     (use assms strict_antimono_pent_num[of i j] strict_antimono_pent_num[of j i] in auto)

lemma antimono_pent_num:
  assumes "m \<le> n" "n \<le> 0"
  shows   "pent_num m \<ge> pent_num n"
  using strict_antimono_pent_num[of m n] assms by (cases "m = n") auto

lemma pent_num_uminus: "int (pent_num (-n)) = int (pent_num n) + n"
proof -
  have "2 * (int (pent_num (-n)) - int (pent_num n)) = 2 * n"
    unfolding twice_pent_num_eq ring_distribs by (simp add: algebra_simps)
  thus ?thesis
    by simp
qed

lemma pent_num_uminus': "pent_num (-int n) = pent_num (int n) + n"
  using pent_num_uminus[of "int n"] by simp

lemma pent_num_neg_increment: "int (pent_num (n + 1)) = int (pent_num (-n)) + 2 * n + 1"
proof -
  have "2 * (int (pent_num (n+1)) - int (pent_num (-n))) = 2 * (2 * n + 1)"
    unfolding twice_pent_num_eq ring_distribs by (simp add: algebra_simps)
  thus ?thesis
    by simp
qed

lemma pent_num_increment: "int (pent_num (n + 1)) = int (pent_num n) + 3 * n + 1"
proof -
  have "2 * (int (pent_num (n+1)) - int (pent_num n)) = 2 * (3 * n + 1)"
    unfolding twice_pent_num_eq ring_distribs by (simp add: algebra_simps)
  thus ?thesis
    by simp
qed

lemma pent_num_increment': "pent_num (int n + 1) = pent_num (int n) + 3 * n + 1"
  using pent_num_increment[of "int n"] by simp

lemma pent_num_decrement: "int (pent_num (n - 1)) = int (pent_num n) - 3 * n + 2"
  using pent_num_increment[of "n-1"] by simp

lemma pent_num_decrement': "pent_num (int n - 1) = pent_num (int n) + 2 - 3 * n"
  using pent_num_decrement[of "int n"] by simp

lemma pent_num_less_pent_num_neg:
  assumes "n > 0"
  shows   "pent_num n < pent_num (-n)"
proof -
  have "0 < n"
    using assms by simp
  also have "\<dots> = int (pent_num (-n)) - int (pent_num n)"
    by (simp add: pent_num_uminus)
  finally show ?thesis by simp
qed

lemma pent_num_neg_less_pent_num_increment:
  assumes "n \<ge> 0"
  shows   "pent_num (-n) < pent_num (n+1)"
proof -
  have "0 < 2 * n + 1"
    using assms by simp
  also have "\<dots> = int (pent_num (n + 1)) - int (pent_num (-n))"
    by (simp add: pent_num_uminus pent_num_increment)
  finally show ?thesis by simp
qed

lemma inj_pent_num_aux:
  assumes "m < 0" "n > 0" "pent_num m = pent_num n"
  shows   False
proof (cases "-m \<ge> n")
  case False
  have "pent_num m < pent_num (-m+1)"
    using pent_num_neg_less_pent_num_increment[of "-m"] assms by simp
  also have "pent_num (-m+1) \<le> pent_num n"
    by (rule mono_pent_num) (use assms False in auto)
  finally show False
    using assms by auto
next
  case True
  have "pent_num n < pent_num (-n)"
    by (rule pent_num_less_pent_num_neg) (use assms in auto)
  also have "\<dots> \<le> pent_num m"
    by (rule antimono_pent_num) (use assms True in auto)
  finally show False
    using assms by auto
qed
  
lemma inj_pent_num: "inj pent_num"
proof
  fix m n :: int
  assume "pent_num m = pent_num n"
  hence False if "m \<noteq> n"
    using that
  proof (induction m n rule: linorder_wlog)
    case (le m n)
    hence "m < n"
      by auto
    have "m < 0" "n > 0"
      using strict_antimono_pent_num[of m n] strict_mono_pent_num[of m n] \<open>m < n\<close> le.prems
      by linarith+
    thus False
      using inj_pent_num_aux[of m n] le.prems by simp
  qed (simp add: eq_commute)
  thus "m = n"
    by blast
qed

lemma pent_num_eq_iff: "pent_num m = pent_num n \<longleftrightarrow> m = n"
  using inj_pent_num unfolding inj_on_def by blast


definition inv_pent_num :: "nat \<Rightarrow> int" where
  "inv_pent_num n = (if n \<in> pent_nums then THE k. pent_num k = n else 0)"

lemma pent_num_inv_pent_num:
  assumes "n \<in> pent_nums"
  shows   "pent_num (inv_pent_num n) = n"
proof -
  have "\<exists>k. pent_num k = n"
    using assms by (auto simp: pent_nums_def)
  moreover have "k = k'" if "pent_num k = n" "pent_num k' = n" for k k'
    using inj_onD[OF inj_pent_num, of k k'] that by auto
  ultimately have "\<exists>!k. pent_num k = n"
    by blast
  from theI'[OF this] and assms show ?thesis
    by (simp add: inv_pent_num_def)
qed

lemma inv_pent_num_pent_num [simp]: "inv_pent_num (pent_num k) = k"
  by (metis pent_num_eq_iff pent_num_inv_pent_num pent_num_in_pent_nums)

lemma inv_pent_num_eqI: "pent_num k = n \<Longrightarrow> inv_pent_num n = k"
  using inv_pent_num_pent_num by metis

lemma pent_num_eq_0_iff: "pent_num k = 0 \<longleftrightarrow> k = 0"
  by (metis inv_pent_num_pent_num pent_num_0)

lemma pent_num_pos_iff: "pent_num k > 0 \<longleftrightarrow> k \<noteq> 0"
  using pent_num_eq_0_iff[of k] by linarith


text \<open>
  An obvious but useful fact: only a finite number of pentagonal numbers are $\leq\,k$ for any
  given $k$. In fact the number of pentagonal numbers $\leq\,k$ is $O(\sqrt{k})$, but we will
  not show this here.
\<close>
lemma finite_pent_num_le: "finite {i. pent_num i \<le> k}"
proof (rule finite_subset)
  show "{i. pent_num i \<le> k} \<subseteq> {-int k..int k}"
  proof
    fix i assume i: "i \<in> {i. pent_num i \<le> k}"

    have *: "k \<le> pent_num (int k)"
    proof -
      have "2 * int k \<le> int k * (3 * int k - 1)"
        by (cases "k = 0") auto
      also have "\<dots> = 2 * int (pent_num (int k))"
        by (simp add: twice_pent_num_eq)
      finally show "k \<le> pent_num (int k)"
        by linarith
    qed

    have "i \<le> int k"
    proof (cases "i \<ge> 0")
      case True
      have "pent_num i \<le> k"
        using i by simp
      also have "k \<le> pent_num (int k)"
        by (fact *)
      finally show "i \<le> int k"
        using True by (simp add: pent_num_le_iff_nonneg)
    qed auto

    moreover have "-int k \<le> i"
    proof (cases "i \<ge> 0")
      case False
      have "pent_num i \<le> k"
        using i by simp
      also have "k \<le> pent_num (int k)"
        by fact
      also have "\<dots> \<le> pent_num (-int k)"
        by (subst pent_num_uminus') auto
      finally show "i \<ge> -int k"
        using False by (simp add: pent_num_le_iff_nonpos)
    qed auto

    ultimately show "i \<in> {-int k..int k}"
      by auto
  qed
qed auto

lemma finite_pent_num_minus_le: "finite {i. pent_num (-i) \<le> k}"
proof -
  have "bij_betw uminus {i. pent_num i \<le> k} {i. pent_num (-i) \<le> k}"
    by (rule bij_betwI[of _ _ _ uminus]) auto
  from bij_betw_finite[OF this] and finite_pent_num_le[of k] show ?thesis
    by simp
qed

end