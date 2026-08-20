section \<open>Dedekind sums\<close>
theory Dedekind_Sums
imports 
  Complex_Main 
  "HOL-Library.Periodic_Fun"
  "HOL-Library.Real_Mod"
  "HOL-Number_Theory.Number_Theory" 
  "Bernoulli.Bernoulli_FPS"
begin

subsection \<open>Preliminaries\<close>

lemma rcong_of_intI: "[a = b] (mod m) \<Longrightarrow> [of_int a = of_int b] (rmod (of_int m))"
  by (metis cong_iff_lin mult.commute of_int_add of_int_mult rcong_altdef)

lemma rcong_of_int_iff: "[of_int a = of_int b] (rmod (of_int m)) \<longleftrightarrow> [a = b] (mod m)"
proof
  assume "[of_int a = of_int b] (rmod (of_int m))"
  then obtain k where "real_of_int b = of_int a + of_int k * of_int m"
    unfolding rcong_altdef by blast
  also have "\<dots> = of_int (a + k * m)"
    by simp
  finally have "b = a + k * m"
    by linarith
  thus "[a = b] (mod m)"
    by (simp add: cong_iff_lin)
qed (intro rcong_of_intI)


subsection \<open>Definition and basic properties\<close>

(* 
  TODO: Perhaps a more standard definition that also aligns with dedekind_sum_code 
  would be better. There is also a generalisation with three parameters instead of two
  (see Wikipedia) that one could look into.
*)
text \<open>
  Our definition of Dedekind sums follows Apostol~\<^cite>\<open>apostol\<close>. 
\<close>
definition dedekind_sum :: "int \<Rightarrow> int \<Rightarrow> real" where
  "dedekind_sum h k \<equiv> \<Sum>r\<in>{1..<k}. (of_int r / of_int k * (frac (of_int (h*r) / of_int k) - 1/2))"

definition dedekind_frac :: "real \<Rightarrow> real" where
  "dedekind_frac x = (if x \<in> \<int> then 0 else frac x - 1 / 2)"

lemma dedekind_frac_int [simp]: "x \<in> \<int> \<Longrightarrow> dedekind_frac x = 0"
  by (auto simp: dedekind_frac_def)

notation dedekind_frac ("\<langle>_\<rangle>")

lemma dedekind_sum_le1_right [simp]: "k \<le> 1 \<Longrightarrow> dedekind_sum h k = 0"
  by (simp add: dedekind_sum_def)

lemma dedekind_sum_2_right: "dedekind_sum h 2 = (if even h then -1/4 else 0)"
proof -
  have *: "{1..<2} = {1::int}"
    by auto
  have "dedekind_sum h 2 = (frac (real_of_int h / 2) - 1/2) / 2"
    by (simp add: dedekind_sum_def * field_simps)
  also have "\<dots> = (if even h then -1/4 else 0)"
    by (cases "even h") (auto elim!: evenE oddE simp: add_divide_distrib)
  finally show ?thesis .
qed

interpretation dedekind_frac: periodic_fun_simple' dedekind_frac
proof
  show "\<langle>x + 1\<rangle> = \<langle>x\<rangle>" for x
    by (auto simp: dedekind_frac_def frac_1_eq)
qed

lemma dedekind_frac_uminus [simp]: "\<langle>-x\<rangle> = -\<langle>x\<rangle>"
  by (auto simp add: dedekind_frac_def frac_neg)

lemma dedekind_frac_one_minus [simp]: "\<langle>1 - x\<rangle> = -\<langle>x\<rangle>"
  by (metis dedekind_frac.minus_1 dedekind_frac_uminus minus_diff_eq)

lemma dedekind_frac_rcong:
  assumes "[x = x'] (rmod 1)"
  shows   "\<langle>x\<rangle> = \<langle>x'\<rangle>"
proof -
  from assms obtain k where k: "x' = x + of_int k"
    by (auto simp: rcong_altdef)
  thus ?thesis
    by (auto simp: dedekind_frac.plus_of_int)
qed

lemma dedekind_frac_mod:
  "\<langle>of_int (a mod k) / of_int k\<rangle> = \<langle>of_int a / of_int k\<rangle>"
proof (cases "k = 0")
  case False
  have "[real_of_int (a mod k) = real_of_int a] (rmod real_of_int k)"
    by (intro rcong_of_intI cong_mod_leftI cong_refl)
  thus ?thesis using False
    by (intro dedekind_frac_rcong rcong_divide_modulus) auto
qed auto

lemma sum_dedekind_frac_eq_0:
  "(\<Sum>r\<in>{1..<k}. \<langle>of_int r / of_int k\<rangle>) = 0"
proof -
  have "(\<Sum>r\<in>{1..<k}. \<langle>of_int (r) / of_int k\<rangle>) =
        (\<Sum>r\<in>{1..<k}. \<langle>of_int (k - r) / of_int k\<rangle>)"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>r. k - r" "\<lambda>r. k - r"]) auto
  also have "(\<Sum>r\<in>{1..<k}. \<langle>of_int (k - r) / of_int k\<rangle>) =
             (\<Sum>r\<in>{1..<k}. \<langle>1 + -of_int r / of_int k\<rangle>)"
    by (intro sum.cong refl arg_cong[of _ _ dedekind_frac]) (auto simp: field_simps)
  also have "\<dots> = -(\<Sum>r\<in>{1..<k}. \<langle>of_int r / of_int k\<rangle>)"
    by (simp add: sum_negf)
  finally show ?thesis
    by simp
qed

lemma sum_dedekind_aux: 
  assumes "f (0::int) = 0"
  shows   "(\<Sum>r\<in>{0..<k}. f r) = (\<Sum>r\<in>{1..<k}. f r)"
proof (rule sum.mono_neutral_right)
  have "{0..<k} - {1..<k} \<subseteq> {0}"
    by auto
  thus "\<forall>i\<in>{0..<k}-{1..<k}. f i = 0"
    using assms by blast
qed auto

lemma sum_dedekind_frac_eq_0':
  "(\<Sum>r\<in>{0..<k}. \<langle>of_int r / of_int k\<rangle>) = 0"
proof -
  have "(\<Sum>r\<in>{0..<k}. \<langle>of_int r / of_int k\<rangle>) = (\<Sum>r\<in>{1..<k}. \<langle>of_int r / of_int k\<rangle>)"
    by (rule sum_dedekind_aux) auto
  with sum_dedekind_frac_eq_0[of k] show ?thesis
    by simp
qed

lemma sum_dedekind_frac_mult_eq_0:
  assumes "coprime h k"
  shows   "(\<Sum>r\<in>{1..<k}. \<langle>of_int (h * r) / of_int k\<rangle>) = 0"
proof -
  have "(\<Sum>r\<in>{1..<k}. \<langle>of_int (h * r) / of_int k\<rangle>) =
        (\<Sum>r\<in>{1..<k}. \<langle>of_int ((h * r) mod k) / of_int k\<rangle>)"
  proof (intro sum.cong)
    fix r assume r: "r \<in> {1..<k}"
    have k: "k > 0"
      using r by auto
    have "(h * r) mod k = h * r - k * ((h * r) div k)"
      by (metis minus_mult_div_eq_mod)
    also have "real_of_int \<dots> / of_int k = of_int (h * r) / of_int k - of_int ((h * r) div k)"
      using k by (auto simp: field_simps)
    also have "\<langle>\<dots>\<rangle> = \<langle>of_int (h * r) / of_int k\<rangle>"
      by (rule dedekind_frac.minus_of_int)
    finally show "\<langle>of_int (h * r) / of_int k\<rangle> = \<langle>of_int ((h * r) mod k) / of_int k\<rangle>" ..
  qed auto
  also have "\<dots> = (\<Sum>r\<in>{1..<k}. \<langle>of_int r / of_int k\<rangle>)"
    by (rule sum.reindex_bij_betw[OF bij_betw_int_remainders_mult[OF assms]])
  also have "\<dots> = 0"
    by (rule sum_dedekind_frac_eq_0)
  finally show ?thesis .
qed

lemma sum_dedekind_frac_mult_eq_0':
  assumes "coprime h k"
  shows   "(\<Sum>r\<in>{0..<k}. \<langle>of_int (h * r) / of_int k\<rangle>) = 0"
proof -
  have "(\<Sum>r\<in>{0..<k}. \<langle>of_int (h * r) / of_int k\<rangle>) = (\<Sum>r\<in>{1..<k}. \<langle>of_int (h * r) / of_int k\<rangle>)"
    by (intro sum_dedekind_aux) auto
  also have "\<dots> = 0"
    by (intro sum_dedekind_frac_mult_eq_0 assms)
  finally show ?thesis .
qed

lemma dedekind_sum_altdef:
  assumes "coprime h k"
  shows   "dedekind_sum h k = (\<Sum>r\<in>{1..<k}. \<langle>of_int r / of_int k\<rangle> * \<langle>of_int (h*r) / of_int k\<rangle>)"
proof -
  have "(\<Sum>r\<in>{1..<k}. \<langle>of_int r / of_int k\<rangle> * \<langle>of_int (h*r) / of_int k\<rangle>) =
        (\<Sum>r\<in>{1..<k}. (of_int r / of_int k - 1 / 2) * \<langle>of_int (h*r) / of_int k\<rangle>)"
  proof (intro sum.cong ballI)
    fix r assume r: "r \<in> {1..<k}"
    hence "1 \<le> r" "r < k"
      by auto
    hence "\<not>k dvd r"
      using zdvd_not_zless by auto
    hence "real_of_int r / real_of_int k \<notin> \<int>"
      using r by (subst of_int_div_of_int_in_Ints_iff) auto
    moreover have "frac (real_of_int r / real_of_int k) = real_of_int r / real_of_int k"
      using r by (subst frac_eq) auto
    ultimately show "\<langle>real_of_int r / real_of_int k\<rangle> * \<langle>real_of_int (h * r) / real_of_int k\<rangle> = 
                     (real_of_int r / real_of_int k - 1 / 2) * \<langle>real_of_int (h * r) / real_of_int k\<rangle>"
      by (subst dedekind_frac_def) auto
  qed auto
  also have "\<dots> = (\<Sum>r\<in>{1..<k}. of_int r / of_int k * \<langle>of_int (h*r) / of_int k\<rangle>) -
                  1 / 2 * (\<Sum>r\<in>{1..<k}. \<langle>of_int (h*r) / of_int k\<rangle>)"
    unfolding sum_distrib_left sum_subtractf [symmetric] by (simp add: ring_distribs)
  also have "(\<Sum>r\<in>{1..<k}. \<langle>of_int (h*r) / of_int k\<rangle>) = 0"
    by (intro sum_dedekind_frac_mult_eq_0 assms)
  also have "(\<Sum>r\<in>{1..<k}. of_int r / of_int k * \<langle>of_int (h*r) / of_int k\<rangle>) = dedekind_sum h k"
    unfolding dedekind_sum_def
  proof (intro sum.cong)
    fix r assume r: "r \<in> {1..<k}"
    have "\<not>k dvd h * r"
    proof
      assume "k dvd h * r"
      with assms have "k dvd r"
        using coprime_commute coprime_dvd_mult_right_iff by blast
      hence "k \<le> r"
        using r by (intro zdvd_imp_le) auto
      thus False
        using r by simp
    qed
    hence "real_of_int (h * r) / real_of_int k \<notin> \<int>"
      using r by (subst of_int_div_of_int_in_Ints_iff) auto
    thus "real_of_int r / real_of_int k * \<langle>real_of_int (h * r) / real_of_int k\<rangle> =
          real_of_int r / real_of_int k * (frac (real_of_int (h * r) / real_of_int k) - 1 / 2)"
      by (auto simp: dedekind_frac_def)
  qed auto
  finally show ?thesis
    by simp
qed

(* Apostol's Theorem 3.6 *)
theorem dedekind_sum_cong:
  assumes "[h' = h] (mod k)"
  assumes "coprime h' k \<or> coprime h k"
  shows "dedekind_sum h' k = dedekind_sum h k"
proof -
  have coprime: "coprime h' k" "coprime h k"
    using coprime_cong_cong_left[OF assms(1)] assms(2) by auto
  show ?thesis
    unfolding coprime[THEN dedekind_sum_altdef]
  proof (intro sum.cong)
    fix r assume r: "r \<in> {1..<k}"
    have "[real_of_int (h' * r) = real_of_int (h * r)] (rmod real_of_int k)"
      by (intro rcong_of_intI cong_mult cong_refl assms)
    hence "\<langle>real_of_int (h' * r) / real_of_int k\<rangle> = \<langle>real_of_int (h * r) / real_of_int k\<rangle>"
      using r by (intro dedekind_frac_rcong rcong_divide_modulus) auto
    thus "\<langle>real_of_int r / real_of_int k\<rangle> * \<langle>real_of_int (h' * r) / real_of_int k\<rangle> =
          \<langle>real_of_int r / real_of_int k\<rangle> * \<langle>real_of_int (h * r) / real_of_int k\<rangle>"
      by simp
  qed auto
qed

theorem dedekind_sum_negate:
  assumes "coprime h k"
  shows   "dedekind_sum (-h) k = -dedekind_sum h k"
proof -
  have *: "coprime (-h) k"
    using assms by auto
  show ?thesis
    unfolding dedekind_sum_altdef[OF assms] dedekind_sum_altdef[OF *]
    by (simp_all add: sum_negf)
qed

theorem dedekind_sum_negate_cong:
  assumes "[h' = -h] (mod k)" "coprime h' k \<or> coprime h k"
  shows "dedekind_sum h' k = -dedekind_sum h k"
proof -
  have coprime: "coprime h' k" "coprime h k"
    using coprime_cong_cong_left[OF assms(1)] assms(2) by auto
  from coprime show ?thesis
    using assms(1) dedekind_sum_cong dedekind_sum_negate by metis
qed

theorem dedekind_sum_inverse:
  assumes "[h * h' = 1] (mod k)"
  shows   "dedekind_sum h k = dedekind_sum h' k"
proof -
  have 1: "coprime h k"
    using assms coprime_iff_invertible_int by blast
  have 2: "coprime h' k"
    using assms coprime_iff_invertible_int by (subst (asm) mult.commute) auto
  have "dedekind_sum h' k =
          (\<Sum>r = 1..<k. \<langle>real_of_int (1 * r) / real_of_int k\<rangle> * \<langle>real_of_int (h' * r) / real_of_int k\<rangle>)"
    unfolding dedekind_sum_altdef[OF 2] by simp
  also have "\<dots> = (\<Sum>r = 1..<k. \<langle>real_of_int (h * ((h' * r) mod k)) / real_of_int k\<rangle> *
                                \<langle>real_of_int ((h' * r) mod k) / real_of_int k\<rangle>)"
  proof (rule sum.cong, goal_cases)
    case (2 r)
    have "[real_of_int (1 * r) = real_of_int (h * h' * r)] (rmod real_of_int k)"
      using assms by (intro rcong_of_intI cong_mult cong_refl assms) (auto simp: cong_sym)
    also have "[real_of_int (h * h' * r) = real_of_int (h * ((h' * r) mod k))] (rmod of_int k)"
      by (subst mult.assoc, intro rcong_of_intI cong_mult cong_refl cong_mod_rightI)
    finally have *: "\<langle>real_of_int (1 * r) / real_of_int k\<rangle> =
                     \<langle>real_of_int (h * ((h' * r) mod k)) / real_of_int k\<rangle>"
      using 2 by (intro ext dedekind_frac_rcong rcong_divide_modulus) auto
    have "[real_of_int (h' * r) = real_of_int (h' * r mod k)] (rmod real_of_int k)"
      by (intro rcong_of_intI cong_refl cong_mod_rightI)
    hence "\<langle>real_of_int (h' * r) / real_of_int k\<rangle> = \<langle>real_of_int ((h' * r) mod k) / real_of_int k\<rangle>"
      using 2 by (intro dedekind_frac_rcong rcong_divide_modulus) auto
    thus ?case using *
      by (simp add: mult_ac)
  qed auto
  also have "\<dots> = (\<Sum>r = 1..<k. \<langle>real_of_int (h * r) / real_of_int k\<rangle> * \<langle>real_of_int r / real_of_int k\<rangle>)"
    by (rule sum.reindex_bij_betw [OF bij_betw_int_remainders_mult]) fact
  also have "\<dots> = dedekind_sum h k"
    using 1 by (simp add: dedekind_sum_altdef mult_ac)
  finally show ?thesis ..
qed

theorem dedekind_sum_inverse':
  assumes "[h * h' = -1] (mod k)"
  shows   "dedekind_sum h k = -dedekind_sum h' k"
proof -
  have "[-(h * h') = - (-1)] (mod k)"
    using assms unfolding cong_minus_minus_iff .
  hence 1: "[h * -h' = 1] (mod k)"
    by simp
  hence "[h' * (-h) = 1] (mod k)"
    by (simp add: mult_ac)
  hence 2: "coprime h' k"
    using assms coprime_iff_invertible_int by blast
  from 1 have "dedekind_sum h k = dedekind_sum (-h') k"
    by (intro dedekind_sum_inverse)
  thus ?thesis
    using 2 by (simp add: dedekind_sum_negate)
qed

theorem dedekind_sum_eq_zero:
  assumes "[h\<^sup>2 + 1 = 0] (mod k)"
  shows   "dedekind_sum h k = 0"
proof -
  have "[h * h = h ^ 2 + 1 - 1] (mod k)"
    by (simp add: algebra_simps power2_eq_square)
  also have "[h ^ 2 + 1 - 1 = 0 - 1] (mod k)"
    by (intro cong_diff assms cong_refl)
  finally have "[h * h = -1] (mod k)"
    by simp
  hence "dedekind_sum h k = -dedekind_sum h k"
    by (rule dedekind_sum_inverse')
  thus ?thesis
    by simp
qed


subsection \<open>The Reciprocity Law\<close>

theorem sum_of_powers': 
  "(\<Sum>k<n::nat. (real k) ^ m) = (bernpoly (Suc m) n - bernpoly (Suc m) 0) / (m + 1)"
proof (cases "n = 0")
  case True
  thus ?thesis
    by auto
next
  case False
  hence "{..<n} = {..n-1}"
    by auto
  thus ?thesis
    using sum_of_powers[of m "n - 1"] False by (simp add: of_nat_diff)
qed

theorem sum_of_powers'_int: 
  assumes "n \<ge> 0"
  shows   "(\<Sum>k=0..<n::int. real_of_int k ^ m) = (bernpoly (Suc m) n - bernpoly (Suc m) 0) / (m + 1)"
proof -
  have "(\<Sum>k=0..<n::int. real_of_int k ^ m) = (\<Sum>k<nat n::nat. real k ^ m)"
    by (intro sum.reindex_bij_witness[of _ int nat]) auto
  also have "(\<Sum>k<nat n::nat. real k ^ m) = (bernpoly (Suc m) n - bernpoly (Suc m) 0) / (m + 1)"
    using assms by (subst sum_of_powers') (auto)
  finally show ?thesis by simp
qed

theorem sum_of_powers'_int_from_1:
  assumes "n \<ge> 0" "m > 0"
  shows   "(\<Sum>k=1..<n::int. real_of_int k ^ m) = (bernpoly (Suc m) n - bernpoly (Suc m) 0) / (m + 1)"
proof -
  have "(\<Sum>k=1..<n::int. real_of_int k ^ m) = (\<Sum>k=0..<n::int. real_of_int k ^ m)"
    using assms by (intro sum.mono_neutral_left) auto
  also have "\<dots> = (bernpoly (Suc m) n - bernpoly (Suc m) 0) / (m + 1)"
    using assms by (subst sum_of_powers'_int) auto
  finally show ?thesis by simp
qed

(* Apostol's Theorem 3.7 *)
theorem dedekind_sum_reciprocity:
  assumes "h > 0" and "k > 0" and "coprime h k"
  shows "12 * h * k * dedekind_sum h k + 12 * k * h * dedekind_sum k h =
         h\<^sup>2 + k\<^sup>2 - 3 * h * k + 1"
proof -
  have upto_3_eq [simp]: "{..(3::nat)} = {0, 1, 2, 3}"
    by auto
  have [simp]: "(3 choose 2) = 3"
    by (simp add: eval_nat_numeral)

  define S where "S = (\<Sum>r\<in>{1..<k}. \<langle>of_int (h*r) / of_int k\<rangle> ^ 2)"
  define T where "T = (\<Sum>r = 1..<k. \<lfloor>real_of_int (h * r) / k\<rfloor> * (\<lfloor>real_of_int (h * r) / k\<rfloor> + 1))"

  have "S = (\<Sum>r\<in>{1..<k}. \<langle>of_int ((h * r) mod k) / of_int k\<rangle> ^ 2)"
    unfolding S_def
    by (intro sum.cong arg_cong[of _ _ "\<lambda>x. x ^ 2"] dedekind_frac_mod [symmetric] refl)
  also have "\<dots> = (\<Sum>r\<in>{1..<k}. \<langle>of_int r / of_int k\<rangle> ^ 2)"
    by (rule sum.reindex_bij_betw[OF bij_betw_int_remainders_mult]) fact
  also have "\<dots> = (\<Sum>r\<in>{1..<k}. (of_int r / of_int k - 1 / 2) ^ 2)"
  proof (rule sum.cong, goal_cases)
    case (2 r)
    have "\<not>k dvd r"
      using 2 by (auto dest!: zdvd_imp_le)
    hence "of_int r / real_of_int k \<notin> \<int>"
      using 2 by (subst of_int_div_of_int_in_Ints_iff) auto
    moreover have "frac (of_int r / real_of_int k) = of_int r / of_int k"
      using 2 by (subst frac_eq) auto
    ultimately show ?case
      by (simp add: dedekind_frac_def)
  qed auto
  also have "\<dots> = 1 / k\<^sup>2 * (\<Sum>r=1..<k. of_int r ^ 2) -
                  1 / k * (\<Sum>r=1..<k. of_int r) +
                  (\<Sum>r=1..<k. 1 / 4)"
    unfolding sum_distrib_left sum_subtractf [symmetric] sum.distrib [symmetric] dedekind_sum_def
    by (intro sum.cong) (auto simp: field_simps power2_eq_square)
  finally have "S = \<dots>" .

  note this [symmetric]
  also have "S = (\<Sum>r = 1..<k. (frac (real_of_int (h * r) / real_of_int k) - 1 / 2)\<^sup>2)"
    unfolding S_def
  proof (rule sum.cong, goal_cases)
    case (2 r)
    have "\<not>k dvd r"
      using 2 by (auto dest!: zdvd_imp_le)
    hence "\<not>k dvd h * r"
      using assms(3) coprime_commute coprime_dvd_mult_right_iff by blast
    hence "of_int (h * r) / real_of_int k \<notin> \<int>"
      using 2 by (subst of_int_div_of_int_in_Ints_iff) auto
    thus ?case
      by (simp add: dedekind_frac_def)
  qed auto
  also have "\<dots> =
    2 * h * dedekind_sum h k +
    (\<Sum>r=1..<k. real_of_int (\<lfloor>of_int(h*r)/k\<rfloor> * (\<lfloor>h*r/k\<rfloor> + 1))) -
    h\<^sup>2/k\<^sup>2 * (\<Sum>r=1..<k. real_of_int r ^ 2) +
    (\<Sum>r=1..<k. 1/4)"
    unfolding sum_distrib_left sum_subtractf [symmetric] sum.distrib [symmetric] dedekind_sum_def
    by (intro sum.cong) (auto simp: field_simps power2_eq_square frac_def)
  finally have "2 * h * dedekind_sum h k =
                 -(\<Sum>r=1..<k. real_of_int (\<lfloor>of_int(h*r)/k\<rfloor> * (\<lfloor>h*r/k\<rfloor> + 1))) +
                 (h\<^sup>2 + 1)/k\<^sup>2 * (\<Sum>r=1..<k. real_of_int r ^ 2) - 1/k * (\<Sum>r=1..<k. of_int r)"
    by (simp add: add_divide_distrib ring_distribs)
  hence "6 * k * (2 * h * dedekind_sum h k) = 6 * k * (
          -(\<Sum>r=1..<k. real_of_int (\<lfloor>of_int(h*r)/k\<rfloor> * (\<lfloor>h*r/k\<rfloor> + 1))) +
           (h\<^sup>2 + 1)/k\<^sup>2 * (\<Sum>r=1..<k. real_of_int r ^ 2) - 1/k * (\<Sum>r=1..<k. of_int r))"
    by (simp only: )
  also have "\<dots> = -6 * k * (\<Sum>r=1..<k. real_of_int (\<lfloor>of_int(h*r)/k\<rfloor> * (\<lfloor>h*r/k\<rfloor> + 1))) +
                  6 * (h\<^sup>2 + 1)/k * (\<Sum>r=1..<k. real_of_int r ^ 2) -
                  6 * (\<Sum>r=1..<k. real_of_int r)"
    using \<open>k > 0\<close> by (simp add: field_simps power2_eq_square)
  also have "(\<Sum>v=1..<k. real_of_int v) = k ^ 2 / 2 - k / 2"
    using sum_of_powers'_int_from_1[of k 1] assms
    by (simp add: bernpoly_def algebra_simps power2_eq_square)
  also have "6 * \<dots> = 3 * k\<^sup>2 - 3 *k"
    using assms by (simp add: field_simps)
  also have "(\<Sum>v=1..<k. real_of_int v ^ 2) = k ^ 3 / 3 - k ^ 2 / 2 + k / 6"
    using assms by (subst sum_of_powers'_int_from_1) (auto simp: bernpoly_def)
  also have "real_of_int (6 * (h\<^sup>2 + 1)) / real_of_int k * \<dots> =
             2 * h\<^sup>2 * k\<^sup>2 + 2 * k\<^sup>2 - 3 * h\<^sup>2 * k - 3 * k + h\<^sup>2 + 1" 
    using assms by (simp add: field_simps power3_eq_cube power2_eq_square)
  finally have sum_eq1: "12 * h * k * dedekind_sum h k = 
    -6 * k * T + 2 * h\<^sup>2 * k\<^sup>2 + 2 * k\<^sup>2 - 3 * h\<^sup>2 * k - 3 * k + h\<^sup>2 + 1 - 3 * k\<^sup>2 + 3 * k"
    by (simp add: mult_ac T_def)

  define N where "N = (\<lambda>v. card {r\<in>{1..<k}. \<lfloor>real_of_int (h*r)/k\<rfloor> = v - 1})"
  have N_eq_aux: "{r\<in>{1..<k}. \<lfloor>real_of_int (h*r)/k\<rfloor> = v - 1} =
                  {1..<k} \<inter> {\<lfloor>k * (v - 1) / h\<rfloor><..\<lfloor>k * v / h\<rfloor>}" for v
  proof -
    have "\<lfloor>real_of_int (h*r)/k\<rfloor> = v - 1 \<longleftrightarrow> r \<in> {\<lfloor>k * (v - 1) / h\<rfloor><..\<lfloor>k * v / h\<rfloor>}"
      if r: "r \<in> {1..<k}" for r
    proof -
      have neq: "real_of_int r \<noteq> k * v / h" for v
      proof
        assume "real_of_int r = k * v / h"
        hence "real_of_int (r * h) = real_of_int (k * v)"
          using assms unfolding of_int_mult by (simp add: field_simps)
        hence *: "r * h = k * v"
          by linarith
        have "k dvd r * h"
          by (subst *) auto
        with \<open>coprime h k\<close> have "k dvd r"
          by (simp add: coprime_commute coprime_dvd_mult_left_iff)
        with r show False
          by (auto dest!: zdvd_imp_le)
      qed
  
      have "\<lfloor>real_of_int (h*r)/k\<rfloor> = v - 1 \<longleftrightarrow> h * r / k \<in> {v-1..<v}"
        unfolding atLeastLessThan_iff by linarith
      also have "\<dots> \<longleftrightarrow> r \<in> {k * (v - 1) / h..<k * v / h}"
        using assms by (auto simp: field_simps)
      also have "\<dots> \<longleftrightarrow> r \<in> {k * (v - 1) / h<..k * v / h}"
        using neq[of "v - 1"] neq[of v] by auto
      also have "\<dots> \<longleftrightarrow> r \<in> {\<lfloor>k * (v - 1) / h\<rfloor><..\<lfloor>k * v / h\<rfloor>}"
        unfolding greaterThanAtMost_iff by safe linarith+
      finally show "\<lfloor>real_of_int (h*r)/k\<rfloor> = v - 1 \<longleftrightarrow> r \<in> {\<lfloor>k * (v - 1) / h\<rfloor><..\<lfloor>k * v / h\<rfloor>}" .
    qed
    thus "{r\<in>{1..<k}. \<lfloor>real_of_int (h*r)/k\<rfloor> = v - 1} =
           {1..<k} \<inter> {\<lfloor>k * (v - 1) / h\<rfloor><..\<lfloor>k * v / h\<rfloor>}"
      by blast
  qed

  define N' where "N' = (\<lambda>v. if v = h then k - 1 else \<lfloor>k * v / h\<rfloor>)"

  have N_eq: "int (N v) = N' v - N' (v - 1)" if v: "v \<in> {1..h}" for v
  proof (cases "v = h")
    case False
    have le: "\<lfloor>real_of_int k * (real_of_int v - 1) / real_of_int h\<rfloor>
              \<le> \<lfloor>real_of_int k * real_of_int v / real_of_int h\<rfloor>"
      using assms by (intro floor_mono divide_right_mono mult_left_mono) auto
    have "N v = card ({1..<k} \<inter> {\<lfloor>k * (v - 1) / h\<rfloor><..\<lfloor>k * v / h\<rfloor>})"
      unfolding N_def N_eq_aux ..
    also have "{\<lfloor>k * (v - 1) / h\<rfloor><..\<lfloor>k * v / h\<rfloor>} \<subseteq> {1..<k}"
    proof -
      have "\<lfloor>k * (v - 1) / h\<rfloor> \<ge> 0"
        using v \<open>k > 0\<close> \<open>h > 0\<close> by auto
      moreover have "\<lfloor>k * v / h\<rfloor> < k"
        using v False \<open>k > 0\<close> \<open>h > 0\<close> by (subst floor_less_iff) (auto simp: field_simps)
      ultimately have "{\<lfloor>k * (v - 1) / h\<rfloor><..\<lfloor>k * v / h\<rfloor>} \<subseteq> {0<..k-1}"
        unfolding Ioc_subset_iff by auto
      also have "{0<..k-1} = {1..<k}"
        by force
      finally show ?thesis .
    qed
    hence "{1..<k} \<inter> {\<lfloor>k * (v - 1) / h\<rfloor><..\<lfloor>k * v / h\<rfloor>} = {\<lfloor>k * (v - 1) / h\<rfloor><..\<lfloor>k * v / h\<rfloor>}"
      by blast
    finally show ?thesis
      using le v False by (simp add: N'_def)
  next
    case [simp]: True
    have le: "\<lfloor>real_of_int k * (real_of_int h - 1) / real_of_int h\<rfloor> \<le> k - 1"
      using assms by (subst floor_le_iff) (auto simp: field_simps)
    have "N h = card ({1..<k} \<inter> {\<lfloor>k * (h - 1) / h\<rfloor><..\<lfloor>k * h / h\<rfloor>})"
      unfolding N_def N_eq_aux ..
    also have "\<lfloor>k * h / h\<rfloor> = k"
      using assms by simp
    also have "{1..<k} \<inter> {\<lfloor>real_of_int (k * (h - 1)) / real_of_int h\<rfloor><..k} = 
               {\<lfloor>real_of_int (k * (h - 1)) / real_of_int h\<rfloor>+1..<k}"
    proof -
      have nonneg: "\<lfloor>real_of_int k * (real_of_int h - 1) / real_of_int h\<rfloor> \<ge> 0"
        unfolding of_int_mult using assms by auto
      have "{1..<k} \<inter> {\<lfloor>real_of_int (k * (h - 1)) / real_of_int h\<rfloor>+1..<k+1} =
            {max 1 (\<lfloor>real_of_int k * (real_of_int h - 1) / real_of_int h\<rfloor>+1)..<k}"
        by simp
      also have "max 1 (\<lfloor>real_of_int k * (real_of_int h - 1) / real_of_int h\<rfloor>+1) =
                 \<lfloor>real_of_int k * (real_of_int h - 1) / real_of_int h\<rfloor> + 1"
        using nonneg by auto
      also have "{\<lfloor>real_of_int (k * (h - 1)) / real_of_int h\<rfloor>+1..<k+1} =
                 {\<lfloor>real_of_int (k * (h - 1)) / real_of_int h\<rfloor><..k}"
        by force
      finally show ?thesis by simp
    qed
    finally show ?thesis
      using le by (simp add: N'_def)
  qed

  have "T = (\<Sum>(v,r) \<in> (SIGMA v:{1..h}. {r\<in>{1..<k}. \<lfloor>of_int (h*r)/k\<rfloor> = v - 1}). (v - 1) * v)"
    unfolding T_def
  proof (intro sum.reindex_bij_witness[of _ snd "\<lambda>r. (\<lfloor>of_int (h*r)/k\<rfloor> + 1, r)"], goal_cases)
    case (2 r)
    have "\<lfloor>real_of_int h * real_of_int r / real_of_int k\<rfloor> < h"
      using 2 assms by (subst floor_less_iff) (auto simp: field_simps)
    thus ?case using 2 assms by auto
  qed (use assms in auto)
  also have "\<dots> = (\<Sum>v=1..h. \<Sum>r|r\<in>{1..<k} \<and> \<lfloor>real_of_int(h*r)/k\<rfloor> = v - 1. (v - 1) * v)"
  proof (intro sum.Sigma [symmetric] ballI)
    show "finite {r \<in> {1..<k}. \<lfloor>real_of_int (h * r) / real_of_int k\<rfloor> = v - 1}" for v
      by (rule finite_subset[of _ "{1..<k}"]) auto
  qed auto
  also have "\<dots> = (\<Sum>v=1..h. (v - 1) * v * int (N v))"
    by (simp add: N_def mult_ac)
  also have "\<dots> = (\<Sum>v=1..h. (v - 1) * v * (N' v - N' (v - 1)))"
    by (intro sum.cong) (auto simp: N_eq)
  also have "\<dots> = (\<Sum>v=1..h. (v - 1) * v * N' v) - (\<Sum>v=1..h. (v - 1) * v * N' (v - 1))"
    by (simp add: ring_distribs sum_subtractf)
  also have "(\<Sum>v=1..h. (v - 1) * v * N' (v - 1)) = (\<Sum>v=0..<h. (v + 1) * v * N' v)"
    by (rule sum.reindex_bij_witness[of _ "\<lambda>v. v+1" "\<lambda>v. v-1"]) auto
  also have "\<dots> = (\<Sum>v=1..<h. (v + 1) * v * N' v)"
    by (intro sum.mono_neutral_right) auto
  also have "{1..h} = insert h {1..<h}"
    using assms by auto
  also have "(\<Sum>v\<in>\<dots>. (v - 1) * v * N' v) =
               (\<Sum>v = 1..<h. (v - 1) * v * N' v) + (h - 1) * h * N' h"
    by (subst sum.insert) auto
  also have "(\<Sum>v=1..<h. (v-1) * v * N' v) + (h-1) * h * N' h - (\<Sum>v=1..<h. (v+1) * v * N' v) =
             (h-1) * h * N' h - 2 * (\<Sum>v=1..<h. v * N' v)"
    by (simp add: ring_distribs sum_subtractf sum.distrib sum_distrib_left sum_negf mult_ac)
  also have "(\<Sum>v = 1..<h. v * N' v) = (\<Sum>v = 1..<h. v * \<lfloor>of_int (k * v)/h\<rfloor>)"
    by (intro sum.cong) (auto simp: N'_def)
  also have "N' h = k - 1"
    by (simp add: N'_def)
  finally have *: "- 2 * (\<Sum>v = 1..<h. v * \<lfloor>of_int (k * v)/h\<rfloor>) =
                   -(h - 1) * h * (k - 1) + T"
    by linarith

  have "12 * k * h * dedekind_sum k h =
           6 * k * (-2 * (\<Sum>v=1..<h. v * \<lfloor>real_of_int (k * v)/h\<rfloor>)) +
            12*k^2/h * (\<Sum>v=1..<h. real_of_int v ^ 2) -
            6 * k * (\<Sum>v=1..<h. real_of_int v)"
    by (simp add: dedekind_sum_def algebra_simps power2_eq_square sum.distrib sum_subtractf
                  sum_distrib_left sum_distrib_right sum_negf frac_def sum_divide_distrib)
  also note *
  also have "real_of_int (6 * k * (- (h - 1) * h * (k - 1) + T)) =
             6 * k * T - 6 * h\<^sup>2 * k\<^sup>2 + 6 * h * k\<^sup>2 + 6 * h\<^sup>2 * k - 6 * h * k"
    by (simp add: algebra_simps power2_eq_square)
  also have "(\<Sum>v=1..<h. real_of_int v) = h ^ 2 / 2 - h / 2"
    using sum_of_powers'_int_from_1[of h 1] assms
    by (simp add: bernpoly_def algebra_simps power2_eq_square)
  also have "real_of_int (6 * k) * \<dots> = 3 * h\<^sup>2 * k - 3 * h * k"
    using assms by (simp add: field_simps)
  also have "(\<Sum>v=1..<h. real_of_int v ^ 2) = h ^ 3 / 3 - h ^ 2 / 2 + h / 6"
    using assms by (subst sum_of_powers'_int_from_1) (auto simp: bernpoly_def)
  also have "real_of_int (12 * k\<^sup>2) / real_of_int h * \<dots> =
             4 * h\<^sup>2 * k\<^sup>2 - 6 * h * k\<^sup>2 + 2 * k\<^sup>2" 
    using assms by (simp add: field_simps power3_eq_cube power2_eq_square)
  finally have sum_eq2: "12 * k * h * dedekind_sum k h =
                          6 * k * T - 2 * h\<^sup>2 * k\<^sup>2 + 3 * h\<^sup>2 * k - 3 * h * k + 2 * k\<^sup>2"
    by simp
  

  have "real_of_int (12 * h * k) * dedekind_sum h k + real_of_int (12 * k * h) * dedekind_sum k h =
        real_of_int (h\<^sup>2 - 3 * h * k + k\<^sup>2 + 1)"
    unfolding sum_eq1 sum_eq2 by simp
  thus ?thesis
    by simp
qed

theorem dedekind_sum_reciprocity':
  assumes "h > 0" and "k > 0" and "coprime h k"
  shows "dedekind_sum h k = -dedekind_sum k h + h / k / 12 + k / h / 12 - 1 / 4 + 1 / (12 * h * k)"
  using dedekind_sum_reciprocity[OF assms] assms
  by (auto simp: field_simps power2_eq_square)


subsection \<open>Congruence Properties\<close>

definition dedekind_sum' :: "int \<Rightarrow> int \<Rightarrow> int" where
  "dedekind_sum' h k = \<lfloor>6 * real_of_int k * dedekind_sum h k\<rfloor>"

lemma dedekind_sum'_le1_right [simp]: "k \<le> 1 \<Longrightarrow> dedekind_sum' h k = 0"
  by (simp add: dedekind_sum'_def)

lemma dedekind_sum'_2_right: "dedekind_sum' h 2 = (if even h then -3 else 0)"
  by (simp add: dedekind_sum'_def dedekind_sum_2_right)

lemma dedekind_sum'_cong: 
  "[h = h'] (mod k) \<Longrightarrow> coprime h k \<or> coprime h' k \<Longrightarrow> dedekind_sum' h k = dedekind_sum' h' k"
  unfolding dedekind_sum'_def by (subst dedekind_sum_cong[of h h' k]) auto

(* Apostol's Theorem 3.8 *)
lemma
  assumes "k > 0"
  shows   of_int_dedekind_sum':
            "real_of_int (dedekind_sum' h k) = 6 * real_of_int k * dedekind_sum h k"
    and   dedekind_sum'_altdef:
            "dedekind_sum' h k = h * (k - 1) * (2 * k - 1) - 
               6 * (\<Sum>r = 1..<k. r * \<lfloor>of_int (h * r) / k\<rfloor>) - 3 * (k * (k - 1) div 2)"
    and   dedekind_sum'_cong_3: "[dedekind_sum' h k = h * (k - 1) * (2 * k - 1)] (mod 3)"
proof -
  have [simp]: "{..3} = {0,1,2,3::nat}"
    by auto
  have [simp]: "(3 choose 2) = 3"
    by (auto simp: eval_nat_numeral)
  have "6 * k * dedekind_sum h k = 6 * h / k * (\<Sum>r=1..<k. of_int r ^ 2) -
          6 * (\<Sum>r=1..<k. of_int r * \<lfloor>h*r/k\<rfloor>) - 3 * (\<Sum>r=1..<k. of_int r ^ 1)"
    by (simp add: dedekind_sum_def frac_def algebra_simps sum_distrib_left sum_distrib_right
                  sum_subtractf sum.distrib sum_divide_distrib power2_eq_square)
  also have "6 * h / k * (\<Sum>r=1..<k. real_of_int r ^ 2) = 2 * h * k\<^sup>2 + h - 3 * h * k"
    using assms by (subst sum_of_powers'_int_from_1)
                   (auto simp: bernpoly_def field_simps power2_eq_square power3_eq_cube)
  also have "3 * (\<Sum>r=1..<k. real_of_int r ^ 1) = 3 * (k * (k - 1) / 2)"
    using assms by (subst sum_of_powers'_int_from_1)
                   (auto simp: bernpoly_def field_simps power2_eq_square)
  also have "even (k * (k - 1))"
    by auto
  hence "(k * (k - 1) / 2) = real_of_int ((k * (k - 1)) div 2)"
    by fastforce
  also have "2 * h * k\<^sup>2 + h - 3 * h * k = h * (k - 1) * (2 * k - 1)"
    by (simp add: algebra_simps power2_eq_square)
  finally have eq: "6 * real_of_int k * dedekind_sum h k =
                    real_of_int (h * (k - 1) * (2 * k - 1) - 
                       6 * (\<Sum>r = 1..<k. r * \<lfloor>of_int (h * r) / k\<rfloor>) - 3 * (k * (k - 1) div 2))"
    unfolding of_int_diff of_int_add by simp

  have "6 * real_of_int k * dedekind_sum h k \<in> \<int>"
    unfolding eq by (rule Ints_of_int)
  thus "real_of_int (dedekind_sum' h k) = 6 * of_int k * dedekind_sum h k"
    unfolding dedekind_sum'_def by (auto elim!: Ints_cases)
  show eq': "dedekind_sum' h k = h * (k - 1) * (2 * k - 1) - 
               6 * (\<Sum>r = 1..<k. r * \<lfloor>of_int (h * r) / k\<rfloor>) - 3 * (k * (k - 1) div 2)"
    unfolding dedekind_sum'_def eq by (simp only: floor_of_int)
  have "[dedekind_sum' h k = h * (k - 1) * (2 * k - 1) - 0 - 0] (mod 3)"
    unfolding eq' by (intro cong_diff cong_refl) (auto simp: Cong.cong_def)
  thus"[dedekind_sum' h k = h * (k - 1) * (2 * k - 1)] (mod 3)"
    by simp
qed

lemma three_dvd_dedekind_sum'_iff_aux:
  fixes h k :: int
  defines "\<theta> \<equiv> gcd 3 k"
  assumes "k > 0" "coprime h k"
  shows   "3 dvd (2 * dedekind_sum' h k) \<longleftrightarrow> \<not>3 dvd k"
proof -
  have "[2 * dedekind_sum' h k = 2 * (h * (k - 1) * (2 * k - 1))] (mod 3)"
    by (intro cong_mult dedekind_sum'_cong_3 cong_refl assms)
  also have "2 * (h * (k - 1) * (2 * k - 1)) = h * (k - 1) * (4 * k + (-2))"
    by (simp add: algebra_simps)
  also have "[\<dots> = h * (k - 1) * (1 * k + 1)] (mod 3)"
    by (intro cong_mult cong_refl cong_add cong_diff) (auto simp: Cong.cong_def)
  finally have cong: "[2 * dedekind_sum' h k = h * (k - 1) * (k + 1)] (mod 3)"
    by simp

  show "3 dvd (2 * dedekind_sum' h k) \<longleftrightarrow> \<not>3 dvd k"
  proof (cases "3 dvd k")
    case True
    have "\<not>3 dvd h"
      using \<open>coprime h k\<close> True by fastforce
    have "[2 * dedekind_sum' h k = h * (k - 1) * (k + 1)] (mod 3)"
      by (fact cong)
    also have "[h * (k - 1) * (k + 1) = h * (0 - 1) * (0 + 1)] (mod 3)"
      using True by (intro cong_mult cong_diff cong_add cong_refl) (auto simp: cong_0_iff)
    also have "h * (0 - 1) * (0 + 1) = -h"
      by simp
    finally have "3 dvd (2 * dedekind_sum' h k) \<longleftrightarrow> 3 dvd (-h)"
      using cong_dvd_iff by blast
    with \<open>\<not>3 dvd h\<close> True show ?thesis by auto
  next
    case False
    hence "3 dvd (k + 1) \<or> 3 dvd (k - 1)"
      by presburger
    hence "3 dvd (h * (k - 1) * (k + 1))"
      by force
    also have "?this \<longleftrightarrow> 3 dvd (2 * dedekind_sum' h k)"
      using cong cong_dvd_iff by blast
    finally show ?thesis
      using False by auto
  qed
qed

   
lemma dedekind_sum'_reciprocity:
  fixes h k :: int
  assumes "h > 0" "k > 0" "coprime h k"
  shows "2 * h * dedekind_sum' h k = -2 * k * dedekind_sum' k h + h\<^sup>2 + k\<^sup>2 - 3 * h * k + 1"
proof -
  have "real_of_int (2 * h * dedekind_sum' h k) = 12 * h * k * dedekind_sum h k"
    unfolding of_int_mult of_int_dedekind_sum'[OF assms(2)] by simp
  also have "\<dots> = real_of_int (-12 * k * h) * dedekind_sum k h + real_of_int (h\<^sup>2 + k\<^sup>2 - 3 * h * k + 1)"
    using dedekind_sum_reciprocity[OF assms] by simp
  also have "\<dots> = real_of_int (-2 * k * dedekind_sum' k h + h\<^sup>2 + k\<^sup>2 - 3 * h * k + 1)"
    using of_int_dedekind_sum'[OF assms(1)] by simp
  finally show ?thesis by linarith
qed

lemma cong_dedekind_sum'_1:
  fixes h k :: int
  defines "\<theta> \<equiv> gcd 3 k"
  assumes "h > 0" "coprime h k"
  shows "[2 * k * dedekind_sum' k h = 0] (mod \<theta> * k)"
proof -
  have "\<theta> = 1 \<or> \<theta> = 3"
    using gcd_prime_int[of 3 k] unfolding \<theta>_def by auto
  thus ?thesis
  proof
    assume "\<theta> = 3"
    hence "3 dvd k"
      unfolding \<theta>_def by (metis gcd_dvd2)
    with \<open>coprime h k\<close> have "\<not>3 dvd h"
      by force
    have "3 dvd 2 * dedekind_sum' k h"
      using assms \<open>\<not>3 dvd h\<close>
      by (subst three_dvd_dedekind_sum'_iff_aux) (auto simp: coprime_commute)
    hence "3 * k dvd 2 * dedekind_sum' k h * k"
      by auto
    thus ?thesis
      using \<open>\<theta> = 3\<close> by (simp add: cong_0_iff)
  qed (auto simp: cong_0_iff)
qed

lemma cong_dedekind_sum'_2_aux:
  fixes h k :: int
  defines "\<theta> \<equiv> gcd 3 k"
  assumes "h > 0" "k > 0" "coprime h k"
  shows "[2 * h * dedekind_sum' h k = h\<^sup>2 + 1] (mod \<theta> * k)"
proof -
  have "[-(2 * k * dedekind_sum' k h) + h\<^sup>2 + k\<^sup>2 - 3 * h * k + 1 = -0 + h\<^sup>2 + 0 - 0 + 1] (mod \<theta> * k)"
    unfolding \<theta>_def
    by (intro cong_diff cong_add cong_mult cong_refl cong_uminus cong_dedekind_sum'_1 assms)
       (simp_all add: cong_0_iff power2_eq_square)
  also have "-(2 * k * dedekind_sum' k h) + h\<^sup>2 + k\<^sup>2 - 3 * h * k + 1 = 2 * h * dedekind_sum' h k"
    using dedekind_sum'_reciprocity[of k h] assms by (auto simp: coprime_commute)
  finally show ?thesis by simp
qed

lemma dedekind_sum'_negate:
  assumes "k > 0" "coprime h k"
  shows   "dedekind_sum' (-h) k = -dedekind_sum' h k"
proof -
  have "real_of_int (dedekind_sum' (-h) k) = real_of_int (-dedekind_sum' h k)"
    using assms unfolding of_int_minus
    by (subst (1 2) of_int_dedekind_sum') (auto simp: dedekind_sum_negate)
  thus ?thesis
    by linarith
qed

lemma cong_dedekind_sum'_2:
  fixes h k :: int
  defines "\<theta> \<equiv> gcd 3 k"
  assumes "k > 0" "coprime h k"
  shows "[2 * h * dedekind_sum' h k = h\<^sup>2 + 1] (mod \<theta> * k)"
proof (cases h "0 :: int" rule: linorder_cases)
  case greater
  thus ?thesis
    using cong_dedekind_sum'_2_aux[of h k] assms by auto
next
  case less
  thus ?thesis
    using cong_dedekind_sum'_2_aux[of "-h" k] assms by (auto simp: dedekind_sum'_negate)
next
  case equal
  thus ?thesis using assms by (auto simp: Cong.cong_def)
qed


(* Apostol's Theorem 3.9 *)
theorem dedekind_sum'_cong_8:
  assumes "k > 0" "coprime h k"
  shows "[2 * dedekind_sum' h k = 
          (k-1)*(k+2) - 4*h*(k-1) + 4*(\<Sum>r\<in>{1..<(k+1) div 2}. \<lfloor>2*h*r/k\<rfloor>)] (mod 8)"
proof -
  define S1 where "S1 = (\<Sum>r=1..<k. r * \<lfloor>of_int (h * r) / k\<rfloor>)"
  define S2 where "S2 = (\<Sum>r | r \<in> {1..<k} \<and> odd r. \<lfloor>of_int (h * r) / k\<rfloor>)"
  define S3 where "S3 = (\<Sum>r=1..<k. \<lfloor>of_int (h * r) / k\<rfloor>)"
  define S4 where "S4 = (\<Sum>r=1..<(k+1) div 2. \<lfloor>of_int (2 * h * r) / k\<rfloor>)"
  have "4 * 2 dvd 4 * (k * (k - 1))"
    by (intro mult_dvd_mono) auto
  hence dvd: "8 dvd 4 * k * (k - 1)"
    by (simp add: mult_ac)
  
  have "[4 * S1 = 4 * (\<Sum>r=1..<k. if even r then 0 else \<lfloor>of_int (h * r) / k\<rfloor>)] (mod 8)"
    unfolding S1_def sum_distrib_left
  proof (intro cong_sum, goal_cases)
    case (1 r)
    show ?case
    proof (cases "odd r")
      case True
      have *: "4 * r mod 8 = 4"
        using \<open>odd r\<close> by presburger
      have "[4 * r * \<lfloor>real_of_int (h * r) / k\<rfloor> = 4 * \<lfloor>real_of_int (h * r) / k\<rfloor>] (mod 8)"
        by (rule cong_mult[OF _ cong_refl]) (use * in \<open>auto simp: Cong.cong_def\<close>)
      thus ?thesis
        using True by (simp add: mult_ac)
    qed (auto simp: cong_0_iff)
  qed
  also have "(\<Sum>r=1..<k. if even r then 0 else \<lfloor>of_int (h * r) / k\<rfloor>) = S2"
    unfolding S2_def by (intro sum.mono_neutral_cong_right) auto
  finally have S12: "[4 * S1 = 4 * S2] (mod 8)" .

  have "2 * dedekind_sum' h k =
          2 * (h * (k - 1) * (2 * k - 1)) - 12 * S1 - 6 * (k * (k - 1) div 2)"
    using assms by (subst dedekind_sum'_altdef) (auto simp: S1_def)
  also have "6 * (k * (k - 1) div 2) = 3 * k * (k - 1)"
    by (subst div_mult_swap) auto
  also have "2 * (h * (k - 1) * (2 * k - 1)) - 12 * S1 - 3 * k * (k - 1) =
             -2 * h * (k - 1) + h * (4 * k * (k - 1)) - 12 * S1 + k * (k - 1) - 4 * k * (k - 1)"
    by (simp add: algebra_simps)
  also have "[\<dots> = -2 * h * (k - 1) + h * 0 - 4 * S1 + k * (k - 1) - 0] (mod 8)"
    using dvd by (intro cong_diff cong_add S12 cong_mult cong_refl)
                 (auto simp: Cong.cong_def mod_eq_0_iff_dvd)
  also have "-2 * h * (k - 1) + h * 0 - 4 * S1 + k * (k - 1) - 0 = (k - 1) * (k - 2 * h) - 4 * S1"
    by (simp add: algebra_simps)
  also have "[\<dots> = (k - 1) * (k - 2 * h) - 4 * S2] (mod 8)"
    by (intro cong_diff cong_refl S12)
  also have "S2 = S3 - S4"
  proof -
    have *: "{r. r \<in> {1..<k} \<and> odd r} = {1..<k} - {r. r \<in> {1..<k} \<and> even r}"
      by auto
    have "S2 = S3 - (\<Sum>r | r \<in> {1..<k} \<and> even r. \<lfloor>of_int (h * r) / k\<rfloor>)"
      unfolding S2_def S3_def * by (subst Groups_Big.sum_diff) auto
    also have "(\<Sum>r | r \<in> {1..<k} \<and> even r. \<lfloor>of_int (h * r) / k\<rfloor>) = S4"
      unfolding S4_def using \<open>k > 0\<close>
      by (intro sum.reindex_bij_witness[of _ "\<lambda>r. 2 * r" "\<lambda>r. r div 2"])
         (auto simp: real_of_int_div)
    finally show ?thesis .
  qed
  also have "4 * (S3 - S4) = 4 * S3 - 4 * S4"
    by (simp add: algebra_simps)
  also have "4 * S3 = 2 * (h - 1) * (k - 1)"
  proof -
    have "real_of_int S3 = (\<Sum>r=1..<k. -\<langle>of_int (h * r) / k\<rangle> + of_int (h * r) / k - 1 / 2)"
      unfolding S3_def of_int_sum
    proof (intro sum.cong)
      fix r assume r: "r \<in> {1..<k}"
      hence "\<not>k dvd r"
        by (auto dest!: zdvd_imp_le)
      hence "\<not>k dvd (h * r)"
        using assms coprime_commute coprime_dvd_mult_right_iff by blast
      hence "real_of_int (h * r) / real_of_int k \<notin> \<int>"
        using assms by (subst of_int_div_of_int_in_Ints_iff) auto
      thus "real_of_int \<lfloor>real_of_int (h * r) / real_of_int k\<rfloor> =
               -\<langle>real_of_int (h * r) / real_of_int k\<rangle> + real_of_int (h * r) / real_of_int k - 1 / 2"
        by (simp add: dedekind_frac_def frac_def)
    qed auto
    also have "4 * \<dots> = -4 * (\<Sum>r=1..<k. \<langle>of_int (h * r) / k\<rangle>) +
                          4 * h / k * (\<Sum>r=1..<k. of_int r ^ 1) - ((real_of_int k * 4 - 4) / 2)"
      using assms
      by (simp add: sum.distrib sum_subtractf sum_negf of_nat_diff mult_ac 
                    sum_distrib_left sum_distrib_right sum_divide_distrib)
    also have "(\<Sum>r=1..<k. \<langle>of_int (h * r) / k\<rangle>) = 0"
      using assms by (intro sum_dedekind_frac_mult_eq_0)
    also have "4 * h / k * (\<Sum>r=1..<k. real_of_int r ^ 1) = 2 * h * (k - 1)"
      using assms by (subst sum_of_powers'_int_from_1) (auto simp: field_simps bernpoly_def)
    also have "-4 * 0 + real_of_int (2 * h * (k - 1)) - (real_of_int k * 4 - 4) / 2 =
               real_of_int (2 * (h - 1) * (k - 1))"
      by (simp add: field_simps)
    also have "4 * real_of_int S3 = real_of_int (4 * S3)"
      by simp
    finally show ?thesis by linarith
  qed
  also have "(k - 1) * (k - 2 * h) - (2 * (h - 1) * (k - 1) - 4 * S4) =
             (k - 1) * (k + 2) - 4 * h * (k - 1) + 4 * S4"
    by (simp add: algebra_simps)
  finally show "[2 * dedekind_sum' h k = (k-1)*(k+2) - 4*h*(k-1) + 4*S4] (mod 8)"
    unfolding S4_def .
qed

theorem dedekind_sum'_cong_8_odd:
  assumes "k > 0" "coprime h k" "odd k"
  shows "[2 * dedekind_sum' h k = 
          k - 1 + 4*(\<Sum>r\<in>{1..<(k+1) div 2}. \<lfloor>2*h*r/k\<rfloor>)] (mod 8)"
proof -
  define S where "S = (\<Sum>r=1..<(k+1) div 2. \<lfloor>of_int (2 * h * r) / k\<rfloor>)"

  have 1: "[(k-1)*(k+2) = k - 1] (mod 8)"
  proof -
    from assms obtain k' where k': "k = 2 * k' + 1"
      by (elim oddE)
    define k'' where "k'' = k' mod 4"
    have "k'' \<in> {0..<4}"
      unfolding k''_def by simp
    also have "{0..<4} = {0, 1, 2, 3::int}"
      by auto
    finally have "(2 * k'' + 1) ^ 2 mod 8 = 1"
      by auto

    have "[k ^ 2 = ((2 * k') mod (2 * 4) + 1) ^ 2 mod 8] (mod 8)"
      unfolding k' by (intro cong_add cong_refl cong_pow cong_mod_rightI) (auto simp: Cong.cong_def)
    also have "(2 * k') mod (2 * 4) = 2 * k''"
      by (subst mod_mult_mult1) (auto simp: k''_def)
    also have "(2 * k'' + 1) ^ 2 mod 8 = 1"
      by fact
    finally have *: "[k ^ 2 = 1] (mod 8)" .

    have "(k-1)*(k+2) = k^2 + k - 2"
      by (simp add: algebra_simps power2_eq_square)
    also have "[\<dots> = 1 + k - 2] (mod 8)"
      by (intro cong_add cong_refl cong_diff *)
    finally show ?thesis
      by simp
  qed

  have 2: "[4 * h * (k - 1) = 0] (mod 8)"
  proof -
    have "4 * 1 * 2 dvd 4 * h * (k - 1)"
      using assms by (intro mult_dvd_mono) auto
    thus ?thesis by (simp add: cong_0_iff)
  qed

  have "[2 * dedekind_sum' h k = (k-1)*(k+2) - 4*h*(k-1) + 4*S] (mod 8)"
    unfolding S_def using assms by (intro dedekind_sum'_cong_8)
  also have "[(k-1)*(k+2) - 4*h*(k-1) + 4*S = (k - 1) - 0 + 4 * S] (mod 8)"
    by (intro cong_add cong_diff cong_refl 1 2)
  finally show ?thesis
    by (simp add: S_def)
qed


(* Apostol's Theorem 3.10 *)
lemma dedekind_sum'_cong_power_of_two:
  fixes h k k1 :: int and n :: nat
  assumes "h > 0" "k1 > 0" "odd k1" "n > 0" "k = 2 ^ n * k1" "coprime h k"
  shows   "[2 * h * dedekind_sum' h k =
              h\<^sup>2 + k\<^sup>2 + 1 + 5 * k - 4 * k * (\<Sum>v=1..<(h+1) div 2. \<lfloor>of_int (2 * k * v) / h\<rfloor>)]
           (mod 2 ^ (n + 3))"
proof -
  from assms have "even k"
    by auto
  with \<open>coprime h k\<close> have "odd h"
    using coprime_common_divisor odd_one by blast
  from assms have "k > 0"
    by auto
  define S where "S = (\<Sum>v=1..<(h+1) div 2. \<lfloor>of_int (2 * k * v) / h\<rfloor>)"
  have "[2 * dedekind_sum' k h * k = (h - 1 + 4 * S) * k] (mod (8 * k))"
    unfolding S_def using \<open>h > 0\<close> \<open>k > 0\<close> \<open>coprime h k\<close> \<open>odd h\<close>
    by (intro dedekind_sum'_cong_8_odd cong_cmult_rightI) (auto simp: coprime_commute)
  also have "8 * k = 2 ^ (n + 3) * k1"
    using assms by (simp add: power_add)
  finally have *: "[2 * dedekind_sum' k h * k = (h - 1 + 4 * S) * k] (mod 2 ^ (n + 3))"
    using cong_modulus_mult by blast

  have **: "[k - 4 * h * k = 5 * k] (mod 2 ^ (n + 3))"
  proof -
    have "2 ^ 2 * 2 ^ n * 2 dvd 4 * k * (h + 1)"
      using assms by (intro mult_dvd_mono) auto
    hence "2 ^ (n + 3) dvd (5 * k - (k - 4 * h * k))"
      by (simp add: algebra_simps power_add)
    thus ?thesis
      by (subst cong_sym) (auto simp: cong_iff_dvd_diff)
  qed

  have "2 * h * dedekind_sum' h k = h\<^sup>2 + k\<^sup>2 - 3 * h * k + 1 - 2 * dedekind_sum' k h * k"
    using dedekind_sum'_reciprocity[of h k] \<open>h > 0\<close> \<open>k > 0\<close> \<open>coprime h k\<close> by simp
  also have "[\<dots> = h\<^sup>2 + k\<^sup>2 - 3 * h * k + 1 - (h - 1 + 4 * S) * k] (mod 2 ^ (n + 3))"
    using * by (intro cong_add cong_diff cong_refl)
  also have "h\<^sup>2 + k\<^sup>2 - 3*h*k + 1 - (h - 1 + 4*S) * k = h\<^sup>2 + k\<^sup>2 + 1 + (k - 4*h*k) - 4*k*S"
    by (simp add: algebra_simps)
  also have "[\<dots> = h\<^sup>2 + k\<^sup>2 + 1 + 5 * k - 4*k*S] (mod 2 ^ (n + 3))"
    by (intro cong_add cong_diff cong_refl **)
  finally show ?thesis
    by (simp add: S_def)
qed

lemma dedekind_sum'_cong_power_of_two':
  fixes h k k1 :: int
  assumes "h > 0" "k > 0" "even k" "coprime h k"
  shows   "[2 * h * dedekind_sum' h k =
              h\<^sup>2 + k\<^sup>2 + 1 + 5 * k - 4 * k * (\<Sum>v=1..<(h+1) div 2. \<lfloor>of_int (2 * k * v) / h\<rfloor>)]
           (mod 2 ^ (multiplicity 2 k + 3))"
proof (rule dedekind_sum'_cong_power_of_two)
  define k1 where "k1 = k div 2 ^ multiplicity 2 k"
  have "2 ^ multiplicity 2 k dvd k"
    using multiplicity_dvd by blast
  thus k_eq: "k = 2 ^ multiplicity 2 k * k1"
    by (auto simp: k1_def)
  show "odd k1"
    using \<open>k > 0\<close> multiplicity_decompose[of k 2] by (auto simp: k1_def)
  show "multiplicity 2 k > 0"
    using \<open>even k\<close> \<open>k > 0\<close> by (simp add: multiplicity_gt_zero_iff)
  show "k1 > 0"
    using \<open>k > 0\<close> by (subst (asm) k_eq) (auto simp: zero_less_mult_iff)
qed (use assms in auto)


(* Apostol's Theorem 3.11 *)
lemma dedekind_sum_diff_even_int_aux:
  fixes a b c d :: int assumes det: "a * d - b * c = 1"
  fixes q c1 r \<delta>' :: int and \<delta> :: real
  assumes a: "a > 0"
  assumes q: "q \<in> {3, 5, 7, 13}" and "c1 > 0" 
  assumes c: "c = q * c1"
  defines "r \<equiv> 24 div (q - 1)"
  defines "\<delta>' \<equiv> (2 * dedekind_sum' a c - (a + d)) - (2 * q * dedekind_sum' a c1 - (a + d) * q)"
  defines "\<delta> \<equiv> (dedekind_sum a c - (a+d)/(12*c)) - (dedekind_sum a c1 - (a+d)/(12*c1))"
  shows   "of_int \<delta>' = 12 * c * \<delta>" and "24 * c dvd r * \<delta>'"
proof -
  define \<theta> where "\<theta> = gcd 3 c"
  define \<theta>1 where "\<theta>1 = gcd 3 c1"
  have "even r" "odd q"
    using q by (auto simp: r_def)

  have "q > 0"
    using q by auto
  have "c > 0"
    using q and \<open>c1 > 0\<close> and c by auto
  have "[a * d - b * 0 = a * d - b * c] (mod c)"
    by (intro cong_diff cong_mult cong_refl) (auto simp: Cong.cong_def)
  also have "a * d - b * c = 1"
    by fact
  finally have "[a * d = 1] (mod c)"
    by simp
  hence "coprime a c"
    using coprime_iff_invertible_int by blast
  have "coprime a c1"
    using \<open>coprime a c\<close> c by auto

  show of_int_\<delta>': "of_int \<delta>' = 12 * c * \<delta>"
    using \<open>c > 0\<close> \<open>c1 > 0\<close> \<open>q > 0\<close> unfolding \<delta>'_def \<delta>_def of_int_mult of_int_diff
    by (subst (1 2) of_int_dedekind_sum') (auto simp: field_simps c)

  have "[2 * a * dedekind_sum' a c = a\<^sup>2 + 1] (mod \<theta> * c)"
    using \<open>coprime a c\<close> \<open>c > 0\<close> unfolding \<theta>_def by (intro cong_dedekind_sum'_2) auto
  hence "[2 * a * dedekind_sum' a c - a * (a + d) = (a\<^sup>2 + 1) - a * (a + d)] (mod \<theta> * c)"
    by (intro cong_diff cong_refl)
  also have "(a\<^sup>2 + 1) - a * (a + d) = -b * c"
    using det unfolding power2_eq_square by (simp add: algebra_simps)
  finally have "[2 * a * dedekind_sum' a c - a * (a + d) = -b * c] (mod \<theta> * c)" .
  hence 1: "[2 * a * dedekind_sum' a c - a * (a + d) = -b * c] (mod \<theta>1 * c)"
    by (rule cong_dvd_mono_modulus) (auto simp: \<theta>_def \<theta>1_def c)

  have "[2 * a * dedekind_sum' a c1 * q = (a\<^sup>2 + 1) * q] (mod \<theta>1 * c1 * q)"
    using \<open>coprime a c1\<close> \<open>c1 > 0\<close> unfolding \<theta>1_def
    by (intro cong_cmult_rightI cong_dedekind_sum'_2) auto
  hence "[2 * a * dedekind_sum' a c1 * q - a * (a + d) * q =
          (a\<^sup>2 + 1) * q - a * (a + d) * q] (mod \<theta>1 * c)"
    by (intro cong_diff cong_refl) (auto simp: c mult_ac)
  also have "(a\<^sup>2 + 1) * q - a * (a + d) * q = -q * b * c"
    using det unfolding power2_eq_square by (simp add: algebra_simps)
  finally have 2: "[2 * a * q * dedekind_sum' a c1 - a * (a + d) * q = -q * b * c] (mod \<theta>1 * c)"
    by (simp add: mult_ac)

  have r_\<delta>': "r * \<delta>' = r * (2 * dedekind_sum' a c - (a + d) - 
                     (2 * q * dedekind_sum' a c1 - (a + d) * q))"
    by (simp add: \<delta>'_def algebra_simps)

  have r_a_\<delta>': "r * a * \<delta>' = r * (2 * a * dedekind_sum' a c - a * (a + d) - 
                     (2 * a * q * dedekind_sum' a c1 - a * (a + d) * q))"
    by (simp add: \<delta>'_def algebra_simps)
  also have "[\<dots> = r * (-b * c - (-q * b * c))] (mod \<theta>1 * c)"
    by (intro cong_mult cong_diff 1 2 cong_refl)
  also have "r * (-b * c - (-q * b * c)) = r * (q - 1) * b * c"
    by (simp add: algebra_simps)
  also have "r * (q - 1) = 24"
    using q by (auto simp: r_def)
  also have "\<theta>1 * 1 * c dvd 24 * b * c"
    by (intro mult_dvd_mono) (auto simp: \<theta>1_def gcd_dvdI1)
  hence "[24 * b * c = 0] (mod \<theta>1 * c)"
    by (simp add: cong_0_iff)
  finally have "\<theta>1 * c dvd r * \<delta>' * a"
    by (simp add: cong_0_iff mult_ac)
  moreover have "coprime a (gcd 3 c1)"
    using \<open>coprime a c1\<close> coprime_imp_coprime dvd_trans by blast
  ultimately have "\<theta>1 * c dvd r * \<delta>'"
    using \<open>coprime a c\<close>
    by (subst (asm) coprime_dvd_mult_left_iff) (auto simp: \<theta>1_def coprime_commute)

  have "3 * c dvd r * \<delta>'"
  proof (cases "q = 3")
    case False
    hence "\<not>3 dvd q"
      using q by auto
    hence "coprime 3 q"
      by (intro prime_imp_coprime) auto
    hence [simp]: "\<theta>1 = \<theta>"
      by (auto simp: \<theta>_def \<theta>1_def c gcd_mult_right_left_cancel)
    show ?thesis
    proof (cases "\<theta> = 3")
      case True
      with \<open>\<theta>1 * c dvd r * \<delta>'\<close> show ?thesis by auto
    next
      case False
      hence [simp]: "\<theta> = 1"
        unfolding \<theta>_def by (subst gcd_prime_int) auto
      hence "\<not>3 dvd c"
        unfolding \<theta>_def by (subst (asm) gcd_prime_int) auto
      hence "\<not>3 dvd c1"
        unfolding c using \<open>coprime 3 q\<close> coprime_dvd_mult_right_iff by blast
      have "[2 * dedekind_sum' a c = 0] (mod 3)"
        using three_dvd_dedekind_sum'_iff_aux[of c a] \<open>c > 0\<close> \<open>coprime a c\<close> \<open>\<not>3 dvd c\<close>
        by (auto simp: cong_0_iff)
      moreover have "[2 * dedekind_sum' a c1 * q = 0] (mod 3)"
        using three_dvd_dedekind_sum'_iff_aux[of c1 a] \<open>c1 > 0\<close> \<open>coprime a c1\<close> \<open>\<not>3 dvd c1\<close>
        by (auto simp: cong_0_iff)
      ultimately have "[r * \<delta>' = 
                        r * ((0 - (a + d)) - (0 - (a + d) * q))] (mod 3)"
        unfolding r_\<delta>' by (intro cong_mult cong_diff cong_refl) (simp_all add: mult_ac)
      also have "r * ((0 - (a + d)) - (0 - (a + d) * q)) = r * (q - 1) * (a + d)"
        by (simp add: algebra_simps)
      also have "r * (q - 1) = 24"
        using q by (auto simp: r_def)
      also have "[24 * (a + d) = 0] (mod 3)"
        by (simp add: cong_0_iff)
      finally have "3 dvd r * \<delta>'"
        by (simp add: cong_0_iff)
      moreover from \<open>\<theta>1 * c dvd r * \<delta>'\<close> have "c dvd r * \<delta>'"
        by (simp add: mult_ac)
      moreover have "coprime 3 c"
        using \<open>\<not>3 dvd c\<close> by (intro prime_imp_coprime) auto
      ultimately show "3 * c dvd r * \<delta>'"
        using divides_mult by blast
    qed
  next
    case [simp]: True
    have [simp]: "r = 12"
      by (simp add: r_def)
    have [simp]: "\<theta> = 3"
      by (auto simp: \<theta>_def c)
    show ?thesis
    proof (cases "\<theta>1 = 3")
      case True
      with \<open>\<theta>1 * c dvd r * \<delta>'\<close> show ?thesis by simp
    next
      case False
      hence [simp]: "\<theta>1 = 1"
        unfolding \<theta>1_def by (subst gcd_prime_int) auto
      hence "\<not>3 dvd c1"
        unfolding \<theta>1_def by (subst (asm) gcd_prime_int) auto
      have "[2 * dedekind_sum' a c1 * a * q = 0 * q] (mod 3 * q)"
        using three_dvd_dedekind_sum'_iff_aux[of c1 a] \<open>c1 > 0\<close> \<open>coprime a c1\<close> \<open>\<not>3 dvd c1\<close>
        by (intro cong_cmult_rightI) (auto simp: cong_0_iff)
      hence "[r * a * \<delta>' = r * (2 * a * dedekind_sum' a c - a * (a + d) - (0 - a * (a + d) * q))] (mod 9)"
        unfolding r_a_\<delta>' by (intro cong_mult cong_diff cong_refl) (auto simp: mult_ac)
      also have "r * (2 * a * dedekind_sum' a c - a * (a + d) - (0 - a * (a + d) * q)) =
                 r * (2 * a * dedekind_sum' a c) + 2 * r * (a\<^sup>2 + a * d)"
        by (simp add: algebra_simps power2_eq_square)
      also have "[2 * a * dedekind_sum' a c = a^2 + 1] (mod \<theta> * c)"
        using cong_dedekind_sum'_2[of c a] \<open>c > 0\<close> \<open>coprime a c\<close> unfolding \<theta>_def by auto
      hence "[2 * a * dedekind_sum' a c = a\<^sup>2 + 1] (mod 9)"
        by (rule cong_dvd_mono_modulus) (auto simp: c)
      hence "[r * (2 * a * dedekind_sum' a c) + 2 * r * (a\<^sup>2 + a * d) =
              r * (a\<^sup>2 + 1) + 2 * r * (a\<^sup>2 + a * d)] (mod 9)"
        by (intro cong_add cong_mult cong_refl)
      also have "r * (a\<^sup>2 + 1) + 2 * r * (a\<^sup>2 + a * d) = 3 * r * a\<^sup>2 + r + 2 * r * (a * d)"
        by (simp add: algebra_simps)
      also have "a * d = b * c + 1"
        using det by (simp add: algebra_simps)
      also have "3 * r * a\<^sup>2 + r + 2 * r * (b * c + 1) = 9 * (4 + 8 * b * c1 + a\<^sup>2 * 4)"
        by (simp add: algebra_simps c)
      also have "[\<dots> = 0] (mod 9)"
        by (simp add: cong_0_iff)
      finally have "9 dvd r * a * \<delta>'"
        by (simp add: cong_0_iff)
      moreover have "coprime a (3 ^ 2)"
        using \<open>coprime a c\<close> c by (subst coprime_power_right_iff) auto
      hence "coprime a 9"
        by (simp del: coprime_power_right_iff)
      ultimately have "9 dvd r * \<delta>'"
        by (metis coprime_commute coprime_dvd_mult_right_iff mult.assoc mult.commute)

      have "3 * c1 dvd 4 * \<delta>'"
      proof (rule divides_mult)
        show "coprime 3 c1"
          using \<open>\<theta>1 = 1\<close> unfolding \<theta>1_def by auto
      next
        have "3 * c1 dvd 3 * (4 * \<delta>')"
          using \<open>\<theta>1 * c dvd r * \<delta>'\<close> by (simp add: c mult_ac)
        thus "c1 dvd 4 * \<delta>'"
          by (subst (asm) dvd_mult_cancel_left) auto
      next
        have "3 * 3 dvd 3 * (4 * \<delta>')"
          using \<open>9 dvd r * \<delta>'\<close> by simp
        thus "3 dvd 4 * \<delta>'"
          by (subst (asm) dvd_mult_cancel_left) auto
      qed
      hence "3 * c dvd 3 * (4 * \<delta>')"
        by (intro mult_dvd_mono dvd_refl) (auto simp: c)
      thus ?thesis
        by (simp add: c mult_ac)
    qed
  qed

  show "24 * c dvd r * \<delta>'"
  proof (cases "even c")
    assume "odd c"
    hence "odd c1"
      by (auto simp: c)

    define T :: "int \<Rightarrow> int" where
      "T = (\<lambda>c. (\<Sum>r = 1..<(c + 1) div 2. \<lfloor>real_of_int (2 * a * r) / real_of_int c\<rfloor>))"

    have "[2 * dedekind_sum' a c = c - 1 + 4 * T c] (mod 8)"
      unfolding T_def by (rule dedekind_sum'_cong_8_odd)
                         (use \<open>coprime a c\<close> \<open>odd c\<close> \<open>c > 0\<close> in auto)
    moreover have "[2 * dedekind_sum' a c1 * q = (c1 - 1 + 4 * T c1) * q] (mod 8)"
      unfolding T_def by (intro cong_mult cong_refl dedekind_sum'_cong_8_odd) 
                         (use \<open>coprime a c1\<close> \<open>odd c1\<close> \<open>c1 > 0\<close> in auto)
    ultimately have "[r * \<delta>' = r * ((c - 1 + 4 * T c - (a + d)) - 
                                   ((c1 - 1 + 4 * T c1) * q - (a + d) * q))] (mod 8)"
      unfolding \<delta>'_def by (intro cong_diff cong_mult[of r] cong_refl) (auto simp: mult_ac)
    also have "r * ((c - 1 + 4*T c - (a+d)) - ((c1 - 1 + 4*T c1)*q - (a+d)*q)) =
                 r * (q - 1) * (a + d + 1) + (r * 4) * (T c - q * T c1)"
      by (simp add: c algebra_simps)
    also have "r * (q - 1) = 24"
      using q by (auto simp: r_def)
    also have "[24 * (a + d + 1) + r * 4 * (T c - q * T c1) =
                0 * (a + d + 1) + 0 * (T c - q * T c1)] (mod 8)"
      using \<open>even r\<close> by (intro cong_add cong_mult cong_refl) (auto simp: cong_0_iff)
    finally have "8 dvd r * \<delta>'"
      by (simp add: cong_0_iff)

    have "8 * (3 * c) dvd r * \<delta>'"
    proof (rule divides_mult)
      have "coprime (2 ^ 3) (3 * c)"
        using \<open>odd c\<close> unfolding coprime_power_left_iff by auto
      thus "coprime 8 (3 * c)"
        by (simp del: coprime_power_left_iff)
    qed fact+
    thus ?thesis
      by simp
  next
    assume "even c"
    with \<open>coprime a c\<close> have "odd a"
      using coprime_common_divisor odd_one by blast
    from \<open>even c\<close> and \<open>odd q\<close> have "even c1"
      by (auto simp: c)

    define n where "n = multiplicity 2 c"
    define c' where "c' = c div 2 ^ n"
    have "c = 2 ^ n * c'"
      unfolding c'_def n_def by (simp add: multiplicity_dvd)
    have n_altdef: "n = multiplicity 2 c1"
      using \<open>odd q\<close> by (auto simp: n_def c multiplicity_prime_elem_times_other)
    have "odd c'"
      unfolding c'_def n_def using \<open>c > 0\<close> multiplicity_decompose[of c 2] by auto

    define T where "T = (\<lambda>c. (\<Sum>v = 1..<(a + 1) div 2. \<lfloor>real_of_int (2 * c * v) / real_of_int a\<rfloor>))"

    have "[2 * a * dedekind_sum' a c = a\<^sup>2 + c\<^sup>2 + 1 + 5 * c - 4 * c * T c] (mod 2 ^ (n + 3))"
      unfolding n_def T_def using \<open>a > 0\<close> \<open>c > 0\<close> \<open>coprime a c\<close> \<open>even c\<close> \<open>odd a\<close>
      by (intro dedekind_sum'_cong_power_of_two') auto
    moreover have "[2 * a * dedekind_sum' a c1 * q = (a\<^sup>2 + c1\<^sup>2 + 1 + 5 * c1 - 4 * c1 * T c1) * q]
                     (mod 2 ^ (n + 3))"
      unfolding n_altdef T_def using \<open>a > 0\<close> \<open>c1 > 0\<close> \<open>coprime a c1\<close> \<open>even c1\<close> \<open>odd a\<close>
      by (intro cong_mult[of _ _ _ q] dedekind_sum'_cong_power_of_two') auto
    ultimately have "[r * a * \<delta>' =
                        r * ((a\<^sup>2 + c\<^sup>2 + 1 + 5 * c - 4 * c * T c) - a * (a + d) - 
                        ((a\<^sup>2 + c1\<^sup>2 + 1 + 5 * c1 - 4 * c1 * T c1) * q - a * (a + d) * q))]
                      (mod 2 ^ (n + 3))"
      unfolding r_a_\<delta>' by (intro cong_mult[of r] cong_diff cong_refl) (auto simp: mult_ac)
    also have "r * ((a\<^sup>2 + c\<^sup>2 + 1 + 5 * c - 4 * c * T c) - a * (a + d) - 
                        ((a\<^sup>2 + c1\<^sup>2 + 1 + 5 * c1 - 4 * c1 * T c1) * q - a * (a + d) * q)) =
               r*(q-1) * (a * d - 1 + c * c1) - 4*c*r * (T c - T c1)"
      by (simp add: algebra_simps c power2_eq_square)
    also have "r * (q - 1) = 24"
      using q by (auto simp: r_def)
    also have "a * d - 1 = b * c"
      using det by (simp add: algebra_simps)
    also have "24 * (b * c + c * c1) = 24 * c * (b + c1)"
      by (simp add: algebra_simps)
    also have "[24 * c * (b + c1) - 4 * c * r * (T c - T c1) = 0 - 0] (mod 2 ^ (n + 3))"
    proof (intro cong_diff)
      have "2 ^ (n + 3) dvd 2 ^ (n + 3) * (3 * c' * (b + c1))"
        using dvd_triv_left by blast
      also have "\<dots> = 24 * c * (b + c1)"
        by (simp add: \<open>c = 2 ^ n * c'\<close> mult_ac power_add)
      finally show "[24 * c * (b + c1) = 0] (mod 2 ^ (n + 3))"
        by (simp add: cong_0_iff)
    next
      have "4 * 2 ^ n * 2 * 1 dvd 4 * c * r * (T c - T c1)"
        using \<open>even r\<close> by (intro mult_dvd_mono) (auto simp: \<open>c = 2 ^ n * c'\<close>)
      thus "[4 * c * r * (T c - T c1) = 0] (mod 2 ^ (n + 3))"
        by (simp add: power_add cong_0_iff mult_ac)
    qed
    finally have "2 ^ (n + 3) dvd r * \<delta>' * a"
      by (simp add: cong_0_iff mult_ac)
    hence "2 ^ (n + 3) dvd r * \<delta>'"
      using \<open>odd a\<close> by (subst (asm) coprime_dvd_mult_left_iff) auto

    have "2 ^ (n + 3) * (3 * c') dvd r * \<delta>'"
    proof (rule divides_mult)
      show "coprime (2 ^ (n + 3)) (3 * c')"
        using \<open>odd c'\<close> by simp
      show "2 ^ (n + 3) dvd r * \<delta>'"
        by fact
      have "3 * c' dvd 3 * c"
        by (auto simp: \<open>c = 2 ^ n * c'\<close>)
      also have "3 * c dvd r * \<delta>'"
        by fact
      finally show "3 * c' dvd r * \<delta>'" .
    qed
    thus ?thesis
      by (simp add: \<open>c = 2 ^ n * c'\<close> power_add mult_ac)
  qed
qed

(* Apostol's Theorem 3.11 *)
theorem dedekind_sum_diff_even_int:
  fixes a b c d :: int assumes det: "a * d - b * c = 1"
  fixes q c1 r :: int and \<delta>' :: "int \<Rightarrow> int" and \<delta> :: "int \<Rightarrow> real"
  assumes q: "q \<in> {3, 5, 7, 13}" and "c1 > 0" 
  assumes c: "c = q * c1"
  defines "r \<equiv> 24 div (q - 1)"
  defines "\<delta>' \<equiv> (\<lambda>a. 2 * dedekind_sum' a c - (a + d) - (2 * q * dedekind_sum' a c1 - (a + d) * q))"
  defines "\<delta> \<equiv> (\<lambda>a. dedekind_sum a c - (a+d)/(12*c) - (dedekind_sum a c1 - (a+d)/(12*c1)))"
  shows   "of_int (\<delta>' a) = 12 * c * \<delta> a" 
    and   "24 * c dvd r * \<delta>' a"
    and   "real_of_int r * \<delta> a / 2 \<in> \<int>"
proof -
  define a' t where "a' = a mod c" and "t = a div c"
  have a'_eq: "a' = a - t * c"
    by (simp add: a'_def t_def algebra_simps)
  have cong1: "[a' = a] (mod c)"
    by (simp add: a'_def)
  hence cong2: "[a' = a] (mod c1)"
    using c by (metis cong_modulus_mult mult.commute)

  have "q > 0"
    using q by auto
  have "c > 0"
    using q and \<open>c1 > 0\<close> and c by auto
  have "[a * d - b * 0 = a * d - b * c] (mod c)"
    by (intro cong_diff cong_mult cong_refl) (auto simp: Cong.cong_def)
  also have "a * d - b * c = 1"
    by fact
  finally have "[a * d = 1] (mod c)"
    by simp
  hence "coprime a c"
    using coprime_iff_invertible_int by blast
  have "coprime a c1"
    using \<open>coprime a c\<close> c by auto

  have "a' \<ge> 0"
    using \<open>c > 0\<close> by (auto simp: a'_def)
  moreover have "a' \<noteq> 0"
    using \<open>coprime a c\<close> q by (auto simp: a'_def c)
  ultimately have "a' > 0"
    by linarith

  have 1: "dedekind_sum a' c = dedekind_sum a c" using cong1
    by (rule dedekind_sum_cong) (use \<open>coprime a c\<close> in \<open>auto simp: a'_def coprime_commute\<close>)
  have 2: "dedekind_sum' a' c = dedekind_sum' a c" using cong1
    by (rule dedekind_sum'_cong) (use \<open>coprime a c\<close> in \<open>auto simp: a'_def coprime_commute\<close>)
  have 3: "dedekind_sum a' c1 = dedekind_sum a c1" using cong2
    by (rule dedekind_sum_cong) (use \<open>coprime a c1\<close> in \<open>auto simp: a'_def coprime_commute\<close>)
  have 4: "dedekind_sum' a' c1 = dedekind_sum' a c1" using cong2
    by (rule dedekind_sum'_cong) (use \<open>coprime a c1\<close> in \<open>auto simp: a'_def coprime_commute\<close>)

  have \<delta>_eq: "\<delta> a' = \<delta> a - t * (q - 1) / 12"
    unfolding \<delta>_def 1 3 using \<open>c > 0\<close> \<open>c1 > 0\<close> \<open>q > 0\<close>
    by (simp add: field_simps c a'_eq)
  have \<delta>'_eq: "\<delta>' a' = \<delta>' a - c * t * (q - 1)"
    unfolding \<delta>'_def 2 4 using \<open>c > 0\<close> \<open>c1 > 0\<close> \<open>q > 0\<close>
    by (simp add: field_simps c a'_eq)

  have det': "a' * d - (b - t * d) * c = 1"
    using det by (simp add: a'_eq algebra_simps)

  have "of_int (\<delta>' a') = 12 * c * \<delta> a'"
    unfolding \<delta>'_def \<delta>_def using det' \<open>c1 > 0\<close> q c \<open>a' > 0\<close> 
    by (intro dedekind_sum_diff_even_int_aux[of a' d "b - t * d" c]) auto
  thus of_int_\<delta>': "of_int (\<delta>' a) = 12 * c * \<delta> a"
    by (simp add: \<delta>_eq \<delta>'_eq field_simps)

  have "24 * c dvd r * \<delta>' a'"
    unfolding r_def \<delta>'_def using det' \<open>c1 > 0\<close> q c \<open>a' > 0\<close>
    by (intro dedekind_sum_diff_even_int_aux[of a' d "b - t * d" c]) auto
  also have "r * \<delta>' a' = r * \<delta>' a - (q - 1) * r * c * t"
    by (simp add: \<delta>'_eq algebra_simps)
  also have "(q - 1) * r = 24"
    unfolding r_def using q by auto
  also have "24 * c dvd r * \<delta>' a - 24 * c * t \<longleftrightarrow> 24 * c dvd r * \<delta>' a"
    by (rule dvd_diff_left_iff) auto
  finally show "24 * c dvd r * \<delta>' a" .

  then obtain m where m: "r * \<delta>' a = 24 * c * m"
    by auto
  hence "real_of_int (r * \<delta>' a) = real_of_int (24 * c * m)"
    by (simp only: )
  hence "real_of_int r * \<delta> a / 2 = of_int m"
    using \<open>c > 0\<close> by (simp add: of_int_\<delta>' field_simps)
  also have "\<dots> \<in> \<int>"
    by simp
  finally show "real_of_int r * \<delta> a / 2 \<in> \<int>" .
qed

no_notation dedekind_frac ("\<langle>_\<rangle>")

(* TODO: formulation in terms of sums over roots of unity or the cotangent *)


subsection \<open>Fast evaluation of Dedekind sums\<close>

text \<open>
  For coprime $h$, $k$ (which is the most important case), the reciprocity identity allows us
  to express $s(h,k)$ in terms of $s(k,h)$ (modulo some simple rational expressions involving
  $h$ and $k$). Moreover, it is clear that $s(h, k) = s(h', k)$ whenever 
  $h = h'\ (\text{mod}\ k)$. Thus we can compute $s(h,k)$ with a straightforward algorithm akin
  to Euclid's GCD algorithm. The running time ought to be the same as the Euclid's algorithm,
  i.e.\ $O(\log (\text{max}(h,k))^2)$ bit operations (but the precise analysis takes some work,
  which we don't do here).
\<close>

fun dedekind_sum'_code :: "int \<Rightarrow> int \<Rightarrow> int" where
  "dedekind_sum'_code h k =
    (if k \<le> 2 then 0
     else let h = h mod k 
          in  (k * (k - 3 * h - 2 * dedekind_sum'_code k h) + h\<^sup>2 + 1) div (2*h))"

lemmas [simp del] = dedekind_sum'_code.simps

definition dedekind_sum_code :: "int \<Rightarrow> int \<Rightarrow> rat" where
  "dedekind_sum_code h k = of_int (dedekind_sum'_code h k) / of_int (6 * k)"

lemma dedekind_sum'_code_correct:
  assumes "coprime h k"
  shows   "dedekind_sum' h k = dedekind_sum'_code h k"
  using assms
proof (induction h k rule: dedekind_sum'_code.induct)
  case (1 h k)
  define h' where "h' = h mod k"
  show ?case
  proof (cases "k \<le> 2")
    case True
    show ?thesis
    proof (cases "k \<le> 1")
      case True
      thus ?thesis
        by (simp add: dedekind_sum'_code.simps)
    next
      case False
      with True have "k = 2"
        by simp
      thus ?thesis
        using "1.prems" True by (simp add: dedekind_sum'_2_right dedekind_sum'_code.simps)
    qed
  next
    case False
    have "\<not>k dvd h"
      using "1.prems" False by auto
    hence "h mod k \<noteq> 0"
      by auto
    moreover have "h mod k \<ge> 0"
      by (rule pos_mod_sign) (use False in auto)
    ultimately have "h' > 0" by (simp add: h'_def)
      
    have "dedekind_sum' h k = dedekind_sum' h' k"
      by (rule dedekind_sum'_cong) (use "1.prems" in \<open>auto simp: h'_def\<close>)
    also have "2 * h' * \<dots> = (h'\<^sup>2 - 2 * k * dedekind_sum' k h' + k\<^sup>2 - 3 * h' * k + 1)"
      by (subst dedekind_sum'_reciprocity)
         (use False "1.prems" \<open>h' > 0\<close> in \<open>auto simp: h'_def\<close>)
    also have "dedekind_sum' k h' = dedekind_sum'_code k h'"
      by (rule "1.IH") (use False "1.prems" in \<open>auto simp: h'_def coprime_commute\<close>)
    also have "(h'\<^sup>2 - 2 * k * \<dots> + k\<^sup>2 - 3 * h' * k + 1) div (2*h') = dedekind_sum'_code h k"
      using False by (subst (2) dedekind_sum'_code.simps) 
                     (auto simp: h'_def Let_def algebra_simps power2_eq_square)
    also have "(2 * h' * dedekind_sum' h k) div (2*h') = dedekind_sum' h k"
      using \<open>h' > 0\<close> by simp
    finally show ?thesis .
  qed
qed

lemma dedekind_sum_code_correct:
  assumes "coprime h k"
  shows   "dedekind_sum h k = of_rat (dedekind_sum_code h k)"
proof (cases "k > 0")
  case False
  thus ?thesis
    by (auto simp: dedekind_sum_code_def dedekind_sum'_code.simps)
next
  case True
  hence "dedekind_sum h k = of_rat (of_int (dedekind_sum' h k) / of_int (6 * k))"
    using of_int_dedekind_sum'[of k h] assms by (simp add: field_simps of_rat_divide of_rat_mult)
  also have "dedekind_sum' h k = dedekind_sum'_code h k"
    by (rule dedekind_sum'_code_correct) fact
  also have "of_int \<dots> / of_int (6*k) = dedekind_sum_code h k"
    by (simp add: dedekind_sum_code_def)
  finally show ?thesis .
qed

value "[dedekind_sum_code h 29. h \<leftarrow> [0..<29], coprime h 29]"

end