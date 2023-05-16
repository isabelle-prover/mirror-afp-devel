(*  Title:      Three_Squares/Quadratic_Forms.thy
    Author:     Anton Danilkin
*)

section \<open>Properties of quadratic forms and their equivalences\<close>

theory Quadratic_Forms
  imports Complex_Main Low_Dimensional_Linear_Algebra
begin

consts qf_app :: "'a \<Rightarrow> 'b \<Rightarrow> int" (infixl "$$" 65)

definition qf2_app :: "mat2 \<Rightarrow> vec2 \<Rightarrow> int" where
"qf2_app m v = <v | m $ v>"

adhoc_overloading qf_app qf2_app

definition qf3_app :: "mat3 \<Rightarrow> vec3 \<Rightarrow> int" where
"qf3_app m v = <v | m $ v>"

adhoc_overloading qf_app qf3_app

lemma qf2_app_zero [simp]:
  fixes m :: mat2
  shows "m $$ 0 = 0"
  unfolding qf2_app_def by auto

lemma qf3_app_zero [simp]:
  fixes m :: mat3
  shows "m $$ 0 = 0"
  unfolding qf3_app_def by auto

consts qf_positive_definite :: "'a \<Rightarrow> bool"

definition qf2_positive_definite :: "mat2 \<Rightarrow> bool" where
"qf2_positive_definite m = (\<forall>v. v \<noteq> 0 \<longrightarrow> m $$ v > 0)"

adhoc_overloading qf_positive_definite qf2_positive_definite

definition qf3_positive_definite :: "mat3 \<Rightarrow> bool" where
"qf3_positive_definite m = (\<forall>v. v \<noteq> 0 \<longrightarrow> m $$ v > 0)"

adhoc_overloading qf_positive_definite qf3_positive_definite

lemma qf2_positive_definite_positive:
  fixes m :: mat2
  assumes "qf_positive_definite m"
  shows "\<forall>v. m $$ v \<ge> 0"
  using assms unfolding qf2_positive_definite_def
  by (metis order_less_le order_refl qf2_app_zero)

lemma qf3_positive_definite_positive:
  fixes m :: mat3
  assumes "qf_positive_definite m"
  shows "\<forall>v. m $$ v \<ge> 0"
  using assms unfolding qf3_positive_definite_def
  by (metis order_less_le order_refl qf3_app_zero)

consts qf_action :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 55)

definition qf2_action :: "mat2 \<Rightarrow> mat2 \<Rightarrow> mat2" where
"qf2_action a u = u\<^sup>T * a * u"

adhoc_overloading qf_action qf2_action

definition qf3_action :: "mat3 \<Rightarrow> mat3 \<Rightarrow> mat3" where
"qf3_action a u = u\<^sup>T * a * u"

adhoc_overloading qf_action qf3_action

lemma qf2_action_id:
  fixes a :: mat2
  shows "a \<cdot> 1 = a"
  unfolding qf2_action_def
  by simp

lemma qf3_action_id:
  fixes a :: mat3
  shows "a \<cdot> 1 = a"
  unfolding qf3_action_def
  by simp

lemma qf2_action_mul [simp]:
  fixes a u v :: mat2
  shows "a \<cdot> (u * v) = (a \<cdot> u) \<cdot> v"
  unfolding qf2_action_def
  by (simp add: algebra_simps)

lemma qf3_action_mul [simp]:
  fixes a u v :: mat3
  shows "a \<cdot> (u * v) = (a \<cdot> u) \<cdot> v"
  unfolding qf3_action_def
  by (simp add: algebra_simps)

consts qf_equiv :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "~" 65)

definition qf2_equiv :: "mat2 \<Rightarrow> mat2 \<Rightarrow> bool" where
"qf2_equiv a b = (\<exists>u. mat_det u = 1 \<and> a \<cdot> u = b)"

adhoc_overloading qf_equiv qf2_equiv

definition qf3_equiv :: "mat3 \<Rightarrow> mat3 \<Rightarrow> bool" where
"qf3_equiv a b = (\<exists>u. mat_det u = 1 \<and> a \<cdot> u = b)"

adhoc_overloading qf_equiv qf3_equiv

lemma qf2_equiv_sym_impl:
  fixes a b :: mat2
  shows "a ~ b \<Longrightarrow> b ~ a"
unfolding qf2_equiv_def qf2_action_def
proof -
  assume "\<exists>u. mat_det u = 1 \<and> u\<^sup>T * a * u = b"
  then obtain u where "mat_det u = 1 \<and> u\<^sup>T * a * u = b" by blast
  hence "mat_det (u\<^sup>-\<^sup>1) = 1 \<and> ((u\<^sup>-\<^sup>1)\<^sup>T) * b * (u\<^sup>-\<^sup>1) = a"
    unfolding mat2_inverse_transpose[symmetric]
    using mat2_inverse_cancel_left[of "u\<^sup>T"] mat2_inverse_cancel_right
    by (auto simp add: algebra_simps)
  thus "\<exists>u. mat_det u = 1 \<and> u\<^sup>T * b * u = a" by blast
qed

lemma qf3_equiv_sym_impl:
  fixes a b :: mat3
  shows "a ~ b \<Longrightarrow> b ~ a"
unfolding qf3_equiv_def qf3_action_def
proof -
  assume "\<exists>u. mat_det u = 1 \<and> u\<^sup>T * a * u = b"
  then obtain u where "mat_det u = 1 \<and> u\<^sup>T * a * u = b" by blast
  hence "mat_det (u\<^sup>-\<^sup>1) = 1 \<and> ((u\<^sup>-\<^sup>1)\<^sup>T) * b * (u\<^sup>-\<^sup>1) = a"
    unfolding mat3_inverse_transpose[symmetric]
    using mat3_inverse_cancel_left[of "u\<^sup>T"] mat3_inverse_cancel_right
    by (auto simp add: algebra_simps)
  thus "\<exists>u. mat_det u = 1 \<and> u\<^sup>T * b * u = a" by blast
qed

lemma qf2_equiv_sym:
  fixes a b :: mat2
  shows "a ~ b \<longleftrightarrow> b ~ a"
  using qf2_equiv_sym_impl by blast

lemma qf3_equiv_sym:
  fixes a b :: mat3
  shows "a ~ b \<longleftrightarrow> b ~ a"
  using qf3_equiv_sym_impl by blast

lemma qf2_equiv_trans:
  fixes a b c :: mat2
  assumes "a ~ b"
  assumes "b ~ c"
  shows "a ~ c"
  using assms by (metis mult_1 mat2_mul_det qf2_action_mul qf2_equiv_def)

lemma qf3_equiv_trans:
  fixes a b c :: mat3
  assumes "a ~ b"
  assumes "b ~ c"
  shows "a ~ c"
  using assms by (metis mult_1 mat3_mul_det qf3_action_mul qf3_equiv_def)

lemma qf2_action_app [simp]:
  fixes a u :: mat2
  fixes v :: vec2
  shows "(a \<cdot> u) $$ v = a $$ (u $ v)"
  unfolding qf2_action_def qf2_app_def
  using vec2_dot_transpose_right by auto

lemma qf3_action_app [simp]:
  fixes a u :: mat3
  fixes v :: vec3
  shows "(a \<cdot> u) $$ v = a $$ (u $ v)"
  unfolding qf3_action_def qf3_app_def
  using vec3_dot_transpose_right by auto

lemma qf2_equiv_preserves_positive_definite:
  fixes a b :: mat2
  assumes "a ~ b"
  shows "qf_positive_definite a \<longleftrightarrow> qf_positive_definite b"
  unfolding qf2_positive_definite_def
  by (metis assms mat2_special_preserves_zero qf2_action_app
            qf2_equiv_def qf2_equiv_sym)

lemma qf3_equiv_preserves_positive_definite:
  fixes a b :: mat3
  assumes "a ~ b"
  shows "qf_positive_definite a \<longleftrightarrow> qf_positive_definite b"
  unfolding qf3_positive_definite_def
  by (metis assms mat3_special_preserves_zero qf3_action_app
            qf3_equiv_def qf3_equiv_sym)

lemma qf2_equiv_preserves_sym:
  fixes a b :: mat2
  assumes "a ~ b"
  shows "mat2_sym a \<longleftrightarrow> mat2_sym b"
proof -
  obtain u where "mat_det u = 1" "u\<^sup>T * a * u = b"
    using assms unfolding qf2_action_def qf2_equiv_def by auto
  thus ?thesis
    unfolding mat2_sym_criterion
    using mat2_inversable_cancel_left[of "u\<^sup>T" "a\<^sup>T * u" "a * u"]
          mat2_inversable_cancel_right[of u "a\<^sup>T" a]
    by (auto simp add: algebra_simps)
qed

lemma qf3_equiv_preserves_sym:
  fixes a b :: mat3
  assumes "a ~ b"
  shows "mat3_sym a \<longleftrightarrow> mat3_sym b"
proof -
  obtain u where "mat_det u = 1" "u\<^sup>T * a * u = b"
    using assms unfolding qf3_action_def qf3_equiv_def by auto
  thus ?thesis
    unfolding mat3_sym_criterion
    using mat3_inversable_cancel_left[of "u\<^sup>T" "a\<^sup>T * u" "a * u"]
          mat3_inversable_cancel_right[of u "a\<^sup>T" a]
    by (auto simp add: algebra_simps)
qed

lemma qf2_equiv_preserves_det:
  fixes a b :: mat2
  assumes "a ~ b"
  shows "mat_det a = mat_det b"
  using assms unfolding qf2_action_def qf2_equiv_def by auto

lemma qf3_equiv_preserves_det:
  fixes a b :: mat3
  assumes "a ~ b"
  shows "mat_det a = mat_det b"
  using assms unfolding qf3_action_def qf3_equiv_def by auto

lemma qf2_equiv_preserves_range_subset:
  fixes a b :: mat2
  assumes "a ~ b"
  shows "range (($$) b) \<subseteq> range (($$) a)"
proof -
  obtain u where 0: "mat_det u = 1" "a \<cdot> u = b"
    using assms unfolding qf2_equiv_def by auto
  show ?thesis unfolding 0[symmetric] image_def by auto
qed

lemma qf3_equiv_preserves_range_subset:
  fixes a b :: mat3
  assumes "a ~ b"
  shows "range (($$) b) \<subseteq> range (($$) a)"
proof -
  obtain u where 0: "mat_det u = 1" "a \<cdot> u = b"
    using assms unfolding qf3_equiv_def by auto
  show ?thesis unfolding 0[symmetric] image_def by auto
qed

lemma qf2_equiv_preserves_range:
  fixes a b :: mat2
  assumes "a ~ b"
  shows "range (($$) a) = range (($$) b)"
  using assms qf2_equiv_sym qf2_equiv_preserves_range_subset by blast

lemma qf3_equiv_preserves_range:
  fixes a b :: mat3
  assumes "a ~ b"
  shows "range (($$) a) = range (($$) b)"
  using assms qf3_equiv_sym qf3_equiv_preserves_range_subset by blast

text \<open>Lemma 1.1 from @{cite nathanson1996}.\<close>

lemma qf2_positive_definite_criterion:
  fixes a
  assumes "mat_sym a"
  shows "qf_positive_definite a \<longleftrightarrow> mat2\<^sub>1\<^sub>1 a > 0 \<and> mat_det a > 0"
proof
  assume 0: "qf_positive_definite a"
  have "vec2 1 0 \<noteq> 0 \<longrightarrow> a $$ vec2 1 0 > 0" using 0
    unfolding qf2_positive_definite_def by blast
  hence 1: "mat2\<^sub>1\<^sub>1 a > 0"
    unfolding zero_vec2_def vec2_dot_def times_mat2_def mat2_app_def qf2_app_def
    by auto
  let ?v = "vec2 (- mat2\<^sub>1\<^sub>2 a) (mat2\<^sub>1\<^sub>1 a)"
  have "?v \<noteq> 0 \<longrightarrow> a $$ ?v > 0" using 0
    unfolding qf2_positive_definite_def by blast
  hence "mat2\<^sub>1\<^sub>1 a * mat_det a > 0" using assms 1
    unfolding zero_vec2_def vec2_dot_def times_mat2_def mat2_app_def
              mat2_det_def mat2_sym_def qf2_app_def
    by (simp add: mult.commute)
  hence 2: "mat_det a > 0" using 1 zero_less_mult_pos by blast
  show "mat2\<^sub>1\<^sub>1 a > 0 \<and> mat_det a > 0" using 1 2 by blast
next
  assume 3: "mat2\<^sub>1\<^sub>1 a > 0 \<and> mat_det a > 0"
  show "qf_positive_definite a" unfolding qf2_positive_definite_def
  proof (rule allI; rule impI)
    fix v :: vec2
    assume "v \<noteq> 0"
    hence 4: "vec2\<^sub>1 v \<noteq> 0 \<or> vec2\<^sub>2 v \<noteq> 0" unfolding zero_vec2_def
      by (metis vec2.collapse)
    let ?n = "(mat2\<^sub>1\<^sub>1 a * vec2\<^sub>1 v + mat2\<^sub>1\<^sub>2 a * vec2\<^sub>2 v)\<^sup>2 + (mat_det a) * (vec2\<^sub>2 v)\<^sup>2"
    have 5: "mat2\<^sub>1\<^sub>1 a * (a $$ v) = ?n"
      using assms
      unfolding vec2_dot_def times_mat2_def mat2_app_def mat2_det_def
                mat2_sym_def qf2_app_def power2_eq_square
      by (simp add: algebra_simps)
    have "?n > 0" using 3 4
      by (metis add.commute add_0 add_pos_nonneg mult_eq_0_iff
          mult_pos_pos power_zero_numeral zero_le_power2 zero_less_power2)
    thus "a $$ v > 0" using 3 5 zero_less_mult_pos by metis
  qed
qed

lemma congruence_class_close:
  fixes k m :: int
  assumes "m > 0"
  shows "\<exists>t. 2 * \<bar>k + m * t\<bar> \<le> m" (is "\<exists> t. ?P t")
proof -
  let ?s = "k div m"
  have 0: "k - m * ?s \<ge> 0 \<and> k - m * ?s < m" using assms
    by (metis pos_mod_sign pos_mod_bound add.commute add_diff_cancel_right'
              div_mod_decomp_int mult.commute)
  show ?thesis proof cases
    assume "2 * (k - m * ?s) \<le> m"
    hence "?P (- ?s)" using 0 by auto
    thus ?thesis by blast
  next
    assume "\<not> (2 * (k - m * ?s) \<le> m)"
    hence "2 * (k - m * ?s) > m" by auto
    hence "?P (- (?s + 1))" using 0 by (simp add: algebra_simps)
    thus ?thesis by blast
  qed
qed

text \<open>Lemma 1.2 from @{cite nathanson1996}.\<close>

lemma lemma_1_2:
  fixes b :: mat2
  assumes "mat_sym b"
  assumes "qf_positive_definite b"
  shows "\<exists>a. a ~ b \<and>
             2 * \<bar>mat2\<^sub>1\<^sub>2 a\<bar> \<le> mat2\<^sub>1\<^sub>1 a \<and>
             mat2\<^sub>1\<^sub>1 a \<le> (2 / sqrt 3) * sqrt (mat_det a)" (is "\<exists>a. ?P a")
proof -
  define a\<^sub>1\<^sub>1 where "a\<^sub>1\<^sub>1 \<equiv> LEAST y. y > 0 \<and> (\<exists>x. int y = b $$ x)"
  have 0: "\<exists>y. y > 0 \<and> (\<exists>x. int y = b $$ x)"
    apply (rule exI[of _ "nat (b $$ (vec2 1 1))"])
    using assms(2) unfolding qf2_positive_definite_def zero_vec2_def
    apply (metis nat_0_le order_less_le vec2.inject zero_less_nat_eq zero_neq_one)
    done
  obtain r where 1: "a\<^sub>1\<^sub>1 > 0" "int a\<^sub>1\<^sub>1 = b $$ r"
    using a\<^sub>1\<^sub>1_def LeastI_ex[OF 0] by auto
  let ?h = "gcd (vec2\<^sub>1 r) (vec2\<^sub>2 r)"
  have "r \<noteq> 0" using assms(2) 1 by fastforce
  hence 2: "?h > 0" by (simp; metis vec2.collapse zero_vec2_def)
  let ?r' = "vec2 (vec2\<^sub>1 r div ?h) (vec2\<^sub>2 r div ?h)"
  have "?r' \<noteq> 0" using 2 unfolding zero_vec2_def
    by (simp add: algebra_simps dvd_div_eq_0_iff)
  hence "nat (b $$ ?r') > 0 \<and> (\<exists>x. int (nat (b $$ ?r')) = b $$ x)"
    using assms(2) unfolding qf2_positive_definite_def by auto
  hence "a\<^sub>1\<^sub>1 \<le> nat (b $$ ?r')" unfolding a\<^sub>1\<^sub>1_def by (rule Least_le)
  hence "a\<^sub>1\<^sub>1 \<le> b $$ ?r'" using 1 by auto
  also have "... = (b $$ r) div ?h\<^sup>2" proof -
    have "(b $$ ?r') * ?h\<^sup>2 = b $$ r" "?h\<^sup>2 dvd b $$ r"
      unfolding qf2_app_def vec2_dot_def mat2_app_def power2_eq_square
      using 1
      by (auto simp add: algebra_simps mult_dvd_mono)
    thus "b $$ ?r' = (b $$ r) div ?h\<^sup>2" using 2 by auto
  qed
  also have "... = a\<^sub>1\<^sub>1 div ?h\<^sup>2" using 1 by auto
  finally have "a\<^sub>1\<^sub>1 \<le> a\<^sub>1\<^sub>1 div ?h\<^sup>2" .
  also have "... \<le> a\<^sub>1\<^sub>1" using 1 2
    by (smt (z3) div_by_1 int_div_less_self of_nat_0_less_iff zero_less_power)
  finally have "?h = 1" using 1 2
    by (smt (verit) int_div_less_self of_nat_0_less_iff power2_eq_square
                    zero_less_power zmult_eq_1_iff)
  then obtain s\<^sub>1 s\<^sub>2 where 3: "1 = (vec2\<^sub>1 r) * s\<^sub>2 - (vec2\<^sub>2 r) * s\<^sub>1"
    by (metis bezout_int diff_minus_eq_add mult.commute mult_minus_right)
  define a'\<^sub>1\<^sub>2 where "
    a'\<^sub>1\<^sub>2 \<equiv>
      (mat2\<^sub>1\<^sub>1 b) * (vec2\<^sub>1 r) * s\<^sub>1
    + (mat2\<^sub>1\<^sub>2 b) * ((vec2\<^sub>1 r) * s\<^sub>2 + (vec2\<^sub>2 r) * s\<^sub>1)
    + (mat2\<^sub>2\<^sub>2 b) * (vec2\<^sub>2 r) * s\<^sub>2
  "
  obtain t where 4: "2 * \<bar>a'\<^sub>1\<^sub>2 + a\<^sub>1\<^sub>1 * (t :: int)\<bar> \<le> a\<^sub>1\<^sub>1"
    using 1 congruence_class_close by fastforce
  define a\<^sub>1\<^sub>2 where "a\<^sub>1\<^sub>2 \<equiv> a'\<^sub>1\<^sub>2 + a\<^sub>1\<^sub>1 * t"
  define a\<^sub>2\<^sub>2 where "a\<^sub>2\<^sub>2 \<equiv> b $$ (vec2 (s\<^sub>1 + (vec2\<^sub>1 r) * t) (s\<^sub>2 + (vec2\<^sub>2 r) * t))"
  let ?u = "
    mat2
      (vec2\<^sub>1 r) (s\<^sub>1 + (vec2\<^sub>1 r) * t)
      (vec2\<^sub>2 r) (s\<^sub>2 + (vec2\<^sub>2 r) * t)
  "
  let ?a = "
    mat2
      a\<^sub>1\<^sub>1 a\<^sub>1\<^sub>2
      a\<^sub>1\<^sub>2 a\<^sub>2\<^sub>2
  "
  have 5: "mat_det ?u = 1" unfolding mat2_det_def
    using 3 by (simp add: algebra_simps)
  have 6: "?a = b \<cdot> ?u" using assms(1) 1
    unfolding qf2_action_def mat2_transpose_def qf2_app_def vec2_dot_def
              mat2_app_def times_mat2_def mat2_sym_def
              a\<^sub>1\<^sub>2_def a\<^sub>1\<^sub>2_def a\<^sub>2\<^sub>2_def a'\<^sub>1\<^sub>2_def
    by (simp add: algebra_simps)
  have "b ~ ?a" unfolding qf2_equiv_def using 5 6 by auto
  hence 7: "?a ~ b" using qf2_equiv_sym by blast
  have 8: "2 * \<bar>mat2\<^sub>1\<^sub>2 ?a\<bar> \<le> mat2\<^sub>1\<^sub>1 ?a" using 4 unfolding a\<^sub>1\<^sub>2_def by auto
  have "a\<^sub>1\<^sub>1 \<le> int (nat a\<^sub>2\<^sub>2)"
    unfolding a\<^sub>1\<^sub>1_def a\<^sub>2\<^sub>2_def
    apply (rule rev_iffD1[OF _ nat_int_comparison(3)])
    apply (rule wellorder_Least_lemma(2))
    using assms(2) 5 unfolding qf2_positive_definite_def zero_vec2_def mat2_det_def
    apply (metis add.right_neutral diff_add_cancel mat2.sel
                 mult_zero_left mult_zero_right nat_0_le order_less_le vec2.inject
                 zero_less_nat_eq zero_neq_one)
    done
  hence "a\<^sub>1\<^sub>1 \<le> a\<^sub>2\<^sub>2" using 1 by linarith
  hence "4 * a\<^sub>1\<^sub>1\<^sup>2 \<le> 4 * a\<^sub>1\<^sub>1 * a\<^sub>2\<^sub>2" unfolding power2_eq_square using 1 by auto
  also have "... = 4 * (mat_det ?a + a\<^sub>1\<^sub>2\<^sup>2)"
    unfolding mat2_det_def power2_eq_square by auto
  also have "... = 4 * mat_det ?a + (2 * \<bar>a\<^sub>1\<^sub>2\<bar>)\<^sup>2"
    unfolding power2_eq_square by auto
  also have "... \<le> 4 * mat_det ?a + (int a\<^sub>1\<^sub>1)\<^sup>2"
    using 4 power2_le_iff_abs_le unfolding a\<^sub>1\<^sub>2_def by (smt (verit))
  finally have "3 * a\<^sub>1\<^sub>1\<^sup>2 \<le> 4 * (mat_det ?a)" by auto
  hence "a\<^sub>1\<^sub>1\<^sup>2 \<le> (4 / 3) * mat_det ?a" by linarith
  hence "sqrt (a\<^sub>1\<^sub>1\<^sup>2) \<le> sqrt ((4 / 3) * mat_det ?a)"
    using real_sqrt_le_mono by blast
  hence "a\<^sub>1\<^sub>1 \<le> sqrt ((4 / 3) * mat_det ?a)" by auto
  hence "a\<^sub>1\<^sub>1 \<le> (sqrt 4) / (sqrt 3) * sqrt (mat_det ?a)"
    unfolding real_sqrt_mult real_sqrt_divide by blast
  hence 9: "mat2\<^sub>1\<^sub>1 ?a \<le> (2 / sqrt 3) * sqrt (mat_det ?a)" by auto
  have "?P ?a" using 7 8 9 by blast
  thus ?thesis by blast
qed

text \<open>Theorem 1.2 from @{cite nathanson1996}.\<close>

theorem qf2_det_one_equiv_canonical:
  fixes f :: mat2
  assumes "mat_sym f"
  assumes "qf_positive_definite f"
  assumes "mat_det f = 1"
  shows "f ~ 1"
proof -
  obtain a where
    0: "f ~ a"
       "2 * \<bar>mat2\<^sub>1\<^sub>2 a\<bar> \<le> mat2\<^sub>1\<^sub>1 a"
       "mat2\<^sub>1\<^sub>1 a \<le> (2 / sqrt 3) * sqrt (mat_det a)"
    using assms lemma_1_2[of f] qf2_equiv_sym by auto
  have 1: "mat_sym a"
    using assms 0 qf2_equiv_preserves_sym by auto
  have 2: "qf_positive_definite a"
    using assms 0 qf2_equiv_preserves_positive_definite by auto
  have 3: "mat_det a = 1" using assms 0 qf2_equiv_preserves_det by auto
  have 4: "mat2\<^sub>1\<^sub>1 a \<ge> 1"
    apply (rule allE[OF 2[unfolded qf2_positive_definite_def], of "vec2 1 0"])
    unfolding zero_vec2_def vec2_dot_def mat2_app_def qf2_app_def
              qf2_positive_definite_def
    apply auto
    done
  have 5: "mat2\<^sub>1\<^sub>1 a < 2" using 0 unfolding 3
    by (smt (verit, best) divide_le_eq int_less_real_le mult_cancel_left1
                          of_int_1 real_sqrt_four real_sqrt_le_iff
                          real_sqrt_mult_self real_sqrt_one)
  have 6: "mat2\<^sub>1\<^sub>1 a = 1" using 4 5 by auto
  have 7: "mat2\<^sub>1\<^sub>2 a = 0" "mat2\<^sub>2\<^sub>1 a = 0" using 0 1 6 unfolding mat2_sym_def by auto
  have 8: "mat2\<^sub>2\<^sub>2 a = 1" using 3 6 7 unfolding mat2_det_def by auto
  have "a = 1" using 6 7 8 unfolding one_mat2_def using mat2.collapse by metis
  thus ?thesis using 0 by metis
qed

text \<open>Lemma 1.3 from @{cite nathanson1996}.\<close>

lemma lemma_1_3:
  fixes a :: mat3
  assumes "mat_sym a"
  defines "a' \<equiv>
    mat2
      (mat3\<^sub>1\<^sub>1 a * mat3\<^sub>2\<^sub>2 a - (mat3\<^sub>1\<^sub>2 a)\<^sup>2) (mat3\<^sub>1\<^sub>1 a * mat3\<^sub>2\<^sub>3 a - mat3\<^sub>1\<^sub>2 a * mat3\<^sub>1\<^sub>3 a)
      (mat3\<^sub>1\<^sub>1 a * mat3\<^sub>2\<^sub>3 a - mat3\<^sub>1\<^sub>2 a * mat3\<^sub>1\<^sub>3 a) (mat3\<^sub>1\<^sub>1 a * mat3\<^sub>3\<^sub>3 a - (mat3\<^sub>1\<^sub>3 a)\<^sup>2)
  "
  defines "d' \<equiv>
    mat_det (
      mat2
        (mat3\<^sub>1\<^sub>1 a) (mat3\<^sub>1\<^sub>2 a)
        (mat3\<^sub>1\<^sub>2 a) (mat3\<^sub>2\<^sub>2 a)
    )
  "
  shows
    "mat_det a' = mat3\<^sub>1\<^sub>1 a * mat_det a" (is "?P")
    "\<And>x. mat3\<^sub>1\<^sub>1 a * (a $$ x) =
      (mat3\<^sub>1\<^sub>1 a * vec3\<^sub>1 x + mat3\<^sub>1\<^sub>2 a * vec3\<^sub>2 x + mat3\<^sub>1\<^sub>3 a * vec3\<^sub>3 x)\<^sup>2 +
      (a' $$ (vec2 (vec3\<^sub>2 x) (vec3\<^sub>3 x)))" (is "\<And>x. ?Q x")
    "qf_positive_definite a \<Longrightarrow> qf_positive_definite a'"
    "qf_positive_definite a \<longleftrightarrow> mat3\<^sub>1\<^sub>1 a > 0 \<and> d' > 0 \<and> mat_det a > 0"
proof -
  show 0: ?P using assms
    unfolding a'_def mat2_det_def mat3_det_def mat3_sym_def power2_eq_square
    by (simp add: algebra_simps)
  show 1: "\<And>x. ?Q x" using assms
    unfolding a'_def vec2_dot_def vec3_dot_def mat2_app_def mat3_app_def
              mat3_sym_def qf2_app_def qf3_app_def power2_eq_square
    by (simp add: algebra_simps)
  have 2: "qf_positive_definite a \<Longrightarrow> mat3\<^sub>1\<^sub>1 a > 0"
  proof -
    assume 3: "qf_positive_definite a"
    show "mat3\<^sub>1\<^sub>1 a > 0"
      using allE[OF iffD1[OF qf3_positive_definite_def 3], of "vec3 1 0 0"]
      unfolding zero_vec3_def vec3_dot_def mat3_app_def qf3_app_def
      by auto
  qed
  show 4: "qf_positive_definite a \<Longrightarrow> qf_positive_definite a'"
  unfolding qf2_positive_definite_def
  proof
    fix v :: vec2
    assume 5: "qf_positive_definite a"
    hence 6: "mat3\<^sub>1\<^sub>1 a > 0" using 2 by blast
    have "a' $$ v \<le> 0 \<Longrightarrow> v = 0" proof -
      assume 7: "a' $$ v \<le> 0"
      obtain x\<^sub>2 x\<^sub>3 where 8: "v = vec2 x\<^sub>2 x\<^sub>3" by (rule vec2.exhaust)
      define x\<^sub>1 where "x\<^sub>1 \<equiv> - (mat3\<^sub>1\<^sub>2 a * x\<^sub>2 + mat3\<^sub>1\<^sub>3 a * x\<^sub>3)"
      have "mat3\<^sub>1\<^sub>1 a * (a $$ (vec3 x\<^sub>1 (mat3\<^sub>1\<^sub>1 a * x\<^sub>2) (mat3\<^sub>1\<^sub>1 a * x\<^sub>3))) =
        (mat3\<^sub>1\<^sub>1 a * x\<^sub>1 + mat3\<^sub>1\<^sub>2 a * mat3\<^sub>1\<^sub>1 a * x\<^sub>2 + mat3\<^sub>1\<^sub>3 a * mat3\<^sub>1\<^sub>1 a * x\<^sub>3)\<^sup>2 +
        (a' $$ (vec2 (mat3\<^sub>1\<^sub>1 a * x\<^sub>2) (mat3\<^sub>1\<^sub>1 a * x\<^sub>3)))"
        unfolding 1 by (simp add: algebra_simps)
      also have "... = a' $$ (vec2 (mat3\<^sub>1\<^sub>1 a * x\<^sub>2) (mat3\<^sub>1\<^sub>1 a * x\<^sub>3))"
        unfolding x\<^sub>1_def by (simp add: algebra_simps)
      also have "... = (mat3\<^sub>1\<^sub>1 a)\<^sup>2 * (a' $$ v)"
        unfolding 8 vec2_dot_def mat2_app_def qf2_app_def power2_eq_square
        by (simp add: algebra_simps)
      also have "... \<le> 0"
        using 7 unfolding power2_eq_square by (simp add: mult_nonneg_nonpos)
      finally have "mat3\<^sub>1\<^sub>1 a * (a $$ (vec3 x\<^sub>1 (mat3\<^sub>1\<^sub>1 a * x\<^sub>2) (mat3\<^sub>1\<^sub>1 a * x\<^sub>3))) \<le> 0"
        .
      hence "a $$ (vec3 x\<^sub>1 (mat3\<^sub>1\<^sub>1 a * x\<^sub>2) (mat3\<^sub>1\<^sub>1 a * x\<^sub>3)) \<le> 0"
        using 6 by (simp add: mult_le_0_iff)
      hence "vec3 x\<^sub>1 (mat3\<^sub>1\<^sub>1 a * x\<^sub>2) (mat3\<^sub>1\<^sub>1 a * x\<^sub>3) = 0"
        using 5 unfolding qf3_positive_definite_def by fastforce
      hence "x\<^sub>2 = 0" "x\<^sub>3 = 0" using 6 unfolding zero_vec3_def by fastforce+
      thus "v = 0" unfolding 8 zero_vec2_def by blast
    qed
    thus "v \<noteq> 0 \<longrightarrow> 0 < a' $$ v" by fastforce
  qed
  have 9: "qf_positive_definite a \<Longrightarrow> d' > 0 \<and> mat_det a > 0"
  proof -
    assume 10: "qf_positive_definite a"
    have 11: "mat3\<^sub>1\<^sub>1 a > 0" using 2 10 by blast
    have "qf_positive_definite a'" using 4 10 by blast
    hence 12: "mat2\<^sub>1\<^sub>1 a' > 0 \<and> mat_det a' > 0"
      using qf2_positive_definite_criterion
      unfolding a'_def mat2_sym_def by fastforce
    have 13: "d' > 0"
      using 12 unfolding a'_def d'_def mat2_det_def power2_eq_square by fastforce
    have 14: "mat_det a > 0"
      using 11 12 unfolding 0 by (simp add: zero_less_mult_iff)
    show "d' > 0 \<and> (mat_det a) > 0" using 13 14 by blast
  qed
  have 15: "mat3\<^sub>1\<^sub>1 a > 0 \<and> d' > 0 \<and> mat_det a > 0 \<Longrightarrow> qf_positive_definite a"
  proof -
    assume 16: "mat3\<^sub>1\<^sub>1 a > 0 \<and> d' > 0 \<and> mat_det a > 0"
    have 17: "mat2\<^sub>1\<^sub>1 a' > 0"
      using 16 unfolding a'_def d'_def mat2_det_def power2_eq_square
      by (simp add: algebra_simps)
    have 18: "mat_det a' > 0" using 16 unfolding 0 by fastforce
    have 19: "qf_positive_definite a'"
      using qf2_positive_definite_criterion 17 18
      unfolding a'_def mat2_sym_def by fastforce
    show "qf_positive_definite a"
    unfolding qf3_positive_definite_def
    proof
      fix x :: vec3
      have "a $$ x \<le> 0 \<Longrightarrow> x = 0" proof -
        assume "a $$ x \<le> 0"
        hence 20: "mat3\<^sub>1\<^sub>1 a * (a $$ x) \<le> 0"
          using 16 mult_le_0_iff order_less_le by auto
        have "a' $$ (vec2 (vec3\<^sub>2 x) (vec3\<^sub>3 x)) \<le> 0"
          using 20 unfolding 1 power2_eq_square by (smt (verit) zero_le_square)
        hence 21: "a' $$ (vec2 (vec3\<^sub>2 x) (vec3\<^sub>3 x)) = 0"
          using 19 qf2_positive_definite_positive
          using nle_le by blast
        have 22: "vec3\<^sub>2 x = 0" "vec3\<^sub>3 x = 0"
          using 19 21 unfolding zero_vec2_def qf2_positive_definite_def
          by (smt (verit) vec2.inject)+
        have "mat3\<^sub>1\<^sub>1 a * vec3\<^sub>1 x + mat3\<^sub>1\<^sub>2 a * vec3\<^sub>2 x + mat3\<^sub>1\<^sub>3 a * vec3\<^sub>3 x = 0"
          using 20 21 unfolding 1 by fastforce
        hence "vec3\<^sub>1 x = 0" using 16 22 by fastforce
        thus "x = 0" using 22 unfolding zero_vec3_def by (metis vec3.collapse)
      qed
      thus "x \<noteq> 0 \<longrightarrow> 0 < a $$ x" by fastforce
    qed
  qed
  show "qf_positive_definite a \<longleftrightarrow> mat3\<^sub>1\<^sub>1 a > 0 \<and> d' > 0 \<and> mat_det a > 0"
    using 2 9 15 by blast
qed

text \<open>Lemma 1.4 from @{cite nathanson1996}.\<close>

lemma lemma_1_4:
  fixes b :: mat3
  fixes v' :: mat2
  fixes r s :: int
  assumes "mat_sym b"
  assumes "qf_positive_definite b"
  assumes "mat_det v' = 1"
  defines "b' \<equiv>
    mat2
      (mat3\<^sub>1\<^sub>1 b * mat3\<^sub>2\<^sub>2 b - (mat3\<^sub>1\<^sub>2 b)\<^sup>2) (mat3\<^sub>1\<^sub>1 b * mat3\<^sub>2\<^sub>3 b - mat3\<^sub>1\<^sub>2 b * mat3\<^sub>1\<^sub>3 b)
      (mat3\<^sub>1\<^sub>1 b * mat3\<^sub>2\<^sub>3 b - mat3\<^sub>1\<^sub>2 b * mat3\<^sub>1\<^sub>3 b) (mat3\<^sub>1\<^sub>1 b * mat3\<^sub>3\<^sub>3 b - (mat3\<^sub>1\<^sub>3 b)\<^sup>2)
  "
  defines "a' \<equiv> b' \<cdot> v'"
  defines "v \<equiv>
    mat3
      1 r s
      0 (mat2\<^sub>1\<^sub>1 v') (mat2\<^sub>1\<^sub>2 v')
      0 (mat2\<^sub>2\<^sub>1 v') (mat2\<^sub>2\<^sub>2 v')
  "
  defines "a \<equiv> b \<cdot> v"
  shows
    "\<And>y. mat3\<^sub>1\<^sub>1 b * (b $$ y) =
      (mat3\<^sub>1\<^sub>1 b * vec3\<^sub>1 y + mat3\<^sub>1\<^sub>2 b * vec3\<^sub>2 y + mat3\<^sub>1\<^sub>3 b * vec3\<^sub>3 y)\<^sup>2 +
      (b' $$ (vec2 (vec3\<^sub>2 y) (vec3\<^sub>3 y)))" (is "\<And>y. ?P y")
    "mat3\<^sub>1\<^sub>1 a = mat3\<^sub>1\<^sub>1 b"
    "\<And>x. mat3\<^sub>1\<^sub>1 a * (a $$ x) =
      (mat3\<^sub>1\<^sub>1 a * vec3\<^sub>1 x + mat3\<^sub>1\<^sub>2 a * vec3\<^sub>2 x + mat3\<^sub>1\<^sub>3 a * vec3\<^sub>3 x)\<^sup>2 +
      (a' $$ (vec2 (vec3\<^sub>2 x) (vec3\<^sub>3 x)))" (is "\<And>x. ?Q x")
proof -
  show "\<And>y. ?P y" using assms
    unfolding b'_def vec2_dot_def vec3_dot_def mat2_app_def mat3_app_def
              mat3_sym_def qf2_app_def qf3_app_def power2_eq_square
    by (simp add: algebra_simps)
  show "mat3\<^sub>1\<^sub>1 a = mat3\<^sub>1\<^sub>1 b"
    unfolding a_def v_def times_mat3_def mat3_transpose_def qf3_action_def
    by force
  show "\<And>y. ?Q y" using assms
    by (simp add: algebra_simps power2_eq_square
                  a_def v_def a'_def b'_def vec2_dot_def vec3_dot_def
                  times_mat2_def times_mat3_def mat2_app_def mat3_app_def
                  mat2_transpose_def mat3_transpose_def mat3_sym_def
                  qf2_app_def qf3_app_def qf2_action_def qf3_action_def)
qed

text \<open>Lemma 1.5 from @{cite nathanson1996}.\<close>

lemma lemma_1_5:
  fixes u\<^sub>1\<^sub>1 u\<^sub>2\<^sub>1 u\<^sub>3\<^sub>1
  assumes "Gcd {u\<^sub>1\<^sub>1, u\<^sub>2\<^sub>1, u\<^sub>3\<^sub>1} = 1"
  shows "\<exists>u. mat3\<^sub>1\<^sub>1 u = u\<^sub>1\<^sub>1 \<and> mat3\<^sub>2\<^sub>1 u = u\<^sub>2\<^sub>1 \<and> mat3\<^sub>3\<^sub>1 u = u\<^sub>3\<^sub>1 \<and> mat_det u = 1"
proof -
  let ?a = "gcd u\<^sub>1\<^sub>1 u\<^sub>2\<^sub>1"
  show ?thesis proof cases
    assume "?a = 0"
    hence 0: "u\<^sub>1\<^sub>1 = 0" "u\<^sub>2\<^sub>1 = 0" "u\<^sub>3\<^sub>1 = 1 \<or> u\<^sub>3\<^sub>1 = -1" using assms by auto
    let ?u = "
      mat3
      0 0 (- 1)
      0 u\<^sub>3\<^sub>1 0
      u\<^sub>3\<^sub>1 0 0"
    show ?thesis
      apply (rule exI[of _ ?u])
      unfolding mat3_det_def using 0 apply auto
      done
  next
    assume 1: "?a \<noteq> 0"
    obtain u\<^sub>1\<^sub>2 u\<^sub>2\<^sub>2 where 2: "u\<^sub>1\<^sub>1 * u\<^sub>2\<^sub>2 - u\<^sub>2\<^sub>1 * u\<^sub>1\<^sub>2 = ?a" using bezout_int
      by (metis diff_minus_eq_add mult.commute mult_minus_right)
    have "gcd ?a u\<^sub>3\<^sub>1 = 1" using assms by (simp add: gcd.assoc)
    then obtain u\<^sub>3\<^sub>3 b where 3: "?a * u\<^sub>3\<^sub>3 - b * u\<^sub>3\<^sub>1 = 1" using bezout_int
      by (metis diff_minus_eq_add mult.commute mult_minus_right)
    let ?u = "
      mat3
      u\<^sub>1\<^sub>1 u\<^sub>1\<^sub>2 ((u\<^sub>1\<^sub>1 div ?a) * b)
      u\<^sub>2\<^sub>1 u\<^sub>2\<^sub>2 ((u\<^sub>2\<^sub>1 div ?a) * b)
      u\<^sub>3\<^sub>1 0 u\<^sub>3\<^sub>3"
    have "mat_det ?u =
          u\<^sub>1\<^sub>1 * u\<^sub>2\<^sub>2 * u\<^sub>3\<^sub>3
        + u\<^sub>1\<^sub>2 * ((u\<^sub>2\<^sub>1 div ?a) * b) * u\<^sub>3\<^sub>1
        - ((u\<^sub>1\<^sub>1 div ?a) * b) * u\<^sub>2\<^sub>2 * u\<^sub>3\<^sub>1
        - u\<^sub>1\<^sub>2 * u\<^sub>2\<^sub>1 * u\<^sub>3\<^sub>3"
      unfolding mat3_det_def by auto
    also have "... =
          u\<^sub>1\<^sub>1 * u\<^sub>2\<^sub>2 * u\<^sub>3\<^sub>3
        + u\<^sub>1\<^sub>2 * (u\<^sub>2\<^sub>1 div ?a) * (b * u\<^sub>3\<^sub>1)
        - u\<^sub>2\<^sub>2 * (u\<^sub>1\<^sub>1 div ?a) * (b * u\<^sub>3\<^sub>1)
        - u\<^sub>1\<^sub>2 * u\<^sub>2\<^sub>1 * u\<^sub>3\<^sub>3"
      by auto
    also have "... =
          u\<^sub>1\<^sub>1 * u\<^sub>2\<^sub>2 * u\<^sub>3\<^sub>3
        + u\<^sub>1\<^sub>2 * (u\<^sub>2\<^sub>1 div ?a) * (?a * u\<^sub>3\<^sub>3 - 1)
        - u\<^sub>2\<^sub>2 * (u\<^sub>1\<^sub>1 div ?a) * (?a * u\<^sub>3\<^sub>3 - 1)
        - u\<^sub>1\<^sub>2 * u\<^sub>2\<^sub>1 * u\<^sub>3\<^sub>3"
      using 3 by (simp add: algebra_simps)
    also have "... =
          u\<^sub>1\<^sub>1 * u\<^sub>2\<^sub>2 * u\<^sub>3\<^sub>3
        + u\<^sub>1\<^sub>2 * ((u\<^sub>2\<^sub>1 div ?a) * ?a) * u\<^sub>3\<^sub>3
        - u\<^sub>1\<^sub>2 * (u\<^sub>2\<^sub>1 div ?a)
        - u\<^sub>2\<^sub>2 * ((u\<^sub>1\<^sub>1 div ?a) * ?a) * u\<^sub>3\<^sub>3
        + u\<^sub>2\<^sub>2 * (u\<^sub>1\<^sub>1 div ?a)
        - u\<^sub>1\<^sub>2 * u\<^sub>2\<^sub>1 * u\<^sub>3\<^sub>3"
      by (simp add: algebra_simps)
    also have "... =
        - u\<^sub>1\<^sub>2 * (u\<^sub>2\<^sub>1 div ?a)
        + u\<^sub>2\<^sub>2 * (u\<^sub>1\<^sub>1 div ?a)"
      by (simp add: algebra_simps)
    also have "... =
        - u\<^sub>1\<^sub>2 * (u\<^sub>2\<^sub>1 div ?a)
        + u\<^sub>2\<^sub>2 * u\<^sub>1\<^sub>1 div ?a"
      by (metis dvd_div_mult gcd_dvd1 mult.commute)
    also have "... =
        - u\<^sub>1\<^sub>2 * (u\<^sub>2\<^sub>1 div ?a)
        + (?a + u\<^sub>2\<^sub>1 * u\<^sub>1\<^sub>2) div ?a"
      using 2 by (simp add: algebra_simps)
    also have "... =
        - u\<^sub>1\<^sub>2 * (u\<^sub>2\<^sub>1 div ?a)
        + 1 + (u\<^sub>2\<^sub>1 * u\<^sub>1\<^sub>2) div ?a"
      using 1 by auto
    also have "... = 1" by (simp add: algebra_simps div_mult1_eq)
    finally have 4: "mat_det ?u = 1" .
    show ?thesis
      apply (rule exI[of _ ?u])
      using 4 apply auto
      done
  qed
qed

text \<open>Lemma 1.6 from @{cite nathanson1996}.\<close>

lemma lemma_1_6:
  fixes c :: mat3
  assumes "mat_sym c"
  assumes "qf_positive_definite c"
  shows "\<exists>a. a ~ c \<and>
             2 * (max \<bar>mat3\<^sub>1\<^sub>2 a\<bar> \<bar>mat3\<^sub>1\<^sub>3 a\<bar>) \<le> mat3\<^sub>1\<^sub>1 a \<and>
             mat3\<^sub>1\<^sub>1 a \<le> (4 / 3) * root 3 (mat_det a)"
proof -
  define a\<^sub>1\<^sub>1 where "a\<^sub>1\<^sub>1 \<equiv> LEAST y. y > 0 \<and> (\<exists>x. int y = c $$ x)"
  have 0: "\<exists>y. y > 0 \<and> (\<exists>x. int y = c $$ x)"
    apply (rule exI[of _ "nat (c $$ (vec3 1 1 1))"])
    using assms(2) unfolding qf3_positive_definite_def zero_vec3_def
    apply (metis nat_0_le order_less_le vec3.inject zero_less_nat_eq zero_neq_one)
    done
  obtain t where 1: "a\<^sub>1\<^sub>1 > 0" "int a\<^sub>1\<^sub>1 = c $$ t"
    using a\<^sub>1\<^sub>1_def LeastI_ex[OF 0] by auto
  let ?h = "Gcd {vec3\<^sub>1 t, vec3\<^sub>2 t, vec3\<^sub>3 t}"
  have "t \<noteq> 0" using assms(2) 1 by fastforce
  hence 2: "?h > 0" by (simp; metis vec3.collapse zero_vec3_def)
  let ?t' = "vec3 (vec3\<^sub>1 t div ?h) (vec3\<^sub>2 t div ?h) (vec3\<^sub>3 t div ?h)"
  have "?t' \<noteq> 0" using 2 unfolding zero_vec3_def
    by (auto simp add: algebra_simps dvd_div_eq_0_iff)
  hence "nat (c $$ ?t') > 0 \<and> (\<exists>x. int (nat (c $$ ?t')) = c $$ x)"
    using assms(2) unfolding qf3_positive_definite_def by auto
  hence "a\<^sub>1\<^sub>1 \<le> nat (c $$ ?t')" unfolding a\<^sub>1\<^sub>1_def by (rule Least_le)
  hence "a\<^sub>1\<^sub>1 \<le> c $$ ?t'" using 1 by auto
  also have "... = (c $$ t) div ?h\<^sup>2" proof -
    have "?h dvd vec3\<^sub>1 t" "?h dvd vec3\<^sub>2 t" "?h dvd vec3\<^sub>3 t"
      by (meson Gcd_dvd insertCI)+
    then have "(c $$ ?t') * ?h\<^sup>2 = c $$ t" "?h\<^sup>2 dvd c $$ t"
      unfolding qf3_app_def vec3_dot_def mat3_app_def power2_eq_square
      using 1
      by (auto simp add: algebra_simps mult_dvd_mono)
    thus "c $$ ?t' = (c $$ t) div ?h\<^sup>2" using 2 by auto
  qed
  also have "... = a\<^sub>1\<^sub>1 div ?h\<^sup>2" using 1 by auto
  finally have "a\<^sub>1\<^sub>1 \<le> a\<^sub>1\<^sub>1 div ?h\<^sup>2" .
  also have "... \<le> a\<^sub>1\<^sub>1" using 1 2
    by (smt (z3) div_by_1 int_div_less_self of_nat_0_less_iff zero_less_power)
  finally have "?h = 1" using 1 2
    by (smt (verit) int_div_less_self of_nat_0_less_iff power2_eq_square
                    zero_less_power zmult_eq_1_iff)
  then obtain u where 3: "mat3\<^sub>1\<^sub>1 u = vec3\<^sub>1 t" "mat3\<^sub>2\<^sub>1 u = vec3\<^sub>2 t"
                         "mat3\<^sub>3\<^sub>1 u = vec3\<^sub>3 t" "mat_det u = 1"
    using lemma_1_5 by blast
  define b where "b \<equiv> c \<cdot> u"
  have 4: "mat_sym b"
    using 3 assms(1) qf3_equiv_preserves_sym
    unfolding b_def qf3_equiv_def
    by auto
  have 5: "qf_positive_definite b"
    using 3 assms(2) qf3_equiv_preserves_positive_definite
    unfolding b_def qf3_equiv_def
    by auto
  have 6: "a\<^sub>1\<^sub>1 = (LEAST y. y > 0 \<and> (\<exists>x. int y = b $$ x))"
    unfolding a\<^sub>1\<^sub>1_def apply (rule arg_cong[of _ _ Least])
    using 3 qf3_equiv_preserves_range[of c b]
    unfolding b_def image_def qf3_equiv_def
    apply fast
    done
  have 7: "a\<^sub>1\<^sub>1 = mat3\<^sub>1\<^sub>1 b"
    using 1 3
    by (simp add: algebra_simps
                  b_def times_mat3_def vec3_dot_def mat3_app_def
                  mat3_transpose_def qf3_app_def qf3_action_def)
  define b' where "b' \<equiv>
    mat2
      (mat3\<^sub>1\<^sub>1 b * mat3\<^sub>2\<^sub>2 b - (mat3\<^sub>1\<^sub>2 b)\<^sup>2) (mat3\<^sub>1\<^sub>1 b * mat3\<^sub>2\<^sub>3 b - mat3\<^sub>1\<^sub>2 b * mat3\<^sub>1\<^sub>3 b)
      (mat3\<^sub>1\<^sub>1 b * mat3\<^sub>2\<^sub>3 b - mat3\<^sub>1\<^sub>2 b * mat3\<^sub>1\<^sub>3 b) (mat3\<^sub>1\<^sub>1 b * mat3\<^sub>3\<^sub>3 b - (mat3\<^sub>1\<^sub>3 b)\<^sup>2)
  "
  have 8: "mat_sym b'" unfolding b'_def mat2_sym_def by auto
  have 9: "mat_det b' = mat3\<^sub>1\<^sub>1 b * mat_det b"
          "\<And>x. mat3\<^sub>1\<^sub>1 b * (b $$ x) =
            (mat3\<^sub>1\<^sub>1 b * vec3\<^sub>1 x + mat3\<^sub>1\<^sub>2 b * vec3\<^sub>2 x + mat3\<^sub>1\<^sub>3 b * vec3\<^sub>3 x)\<^sup>2 +
            (b' $$ (vec2 (vec3\<^sub>2 x) (vec3\<^sub>3 x)))"
          "qf_positive_definite b'"
    using 4 5 b'_def lemma_1_3 by blast+
  obtain a' v' where 10: "a' = b' \<cdot> v'"
                         "mat_det v' = 1"
                         "mat2\<^sub>1\<^sub>1 a' \<le> (2 / sqrt 3) * sqrt (mat3\<^sub>1\<^sub>1 b * mat_det b)"
    using 8 9 qf2_equiv_sym qf2_equiv_preserves_det lemma_1_2[of b']
    unfolding qf2_equiv_def by metis
  obtain r s where 11: "2 * \<bar>(mat3\<^sub>1\<^sub>2 b) * (mat2\<^sub>1\<^sub>1 v') +
                            (mat3\<^sub>1\<^sub>3 b) * (mat2\<^sub>2\<^sub>1 v') + a\<^sub>1\<^sub>1 * (r :: int)\<bar> \<le> a\<^sub>1\<^sub>1"
                       "2 * \<bar>(mat3\<^sub>1\<^sub>2 b) * (mat2\<^sub>1\<^sub>2 v') +
                            (mat3\<^sub>1\<^sub>3 b) * (mat2\<^sub>2\<^sub>2 v') + a\<^sub>1\<^sub>1 * (s :: int)\<bar> \<le> a\<^sub>1\<^sub>1"
    using 1 congruence_class_close by fastforce
  define a\<^sub>1\<^sub>2 where "a\<^sub>1\<^sub>2 \<equiv> (mat3\<^sub>1\<^sub>2 b) * (mat2\<^sub>1\<^sub>1 v') +
                          (mat3\<^sub>1\<^sub>3 b) * (mat2\<^sub>2\<^sub>1 v') + a\<^sub>1\<^sub>1 * r"
  define a\<^sub>1\<^sub>3 where "a\<^sub>1\<^sub>3 \<equiv> (mat3\<^sub>1\<^sub>2 b) * (mat2\<^sub>1\<^sub>2 v') +
                          (mat3\<^sub>1\<^sub>3 b) * (mat2\<^sub>2\<^sub>2 v') + a\<^sub>1\<^sub>1 * s"
  define v where "v \<equiv>
    mat3
      1 r s
      0 (mat2\<^sub>1\<^sub>1 v') (mat2\<^sub>1\<^sub>2 v')
      0 (mat2\<^sub>2\<^sub>1 v') (mat2\<^sub>2\<^sub>2 v')
  "
  have 12: "mat_det v = 1"
    using 10 unfolding v_def mat2_det_def mat3_det_def by (simp add: algebra_simps)
  define a where "a \<equiv> b \<cdot> v"
  have 13: "mat_det a = mat_det b"
    using 12 qf3_equiv_preserves_det
    unfolding a_def qf3_equiv_def
    by metis
  have 14: "a\<^sub>1\<^sub>1 = (LEAST y. y > 0 \<and> (\<exists>x. int y = a $$ x))"
    unfolding 6 apply (rule arg_cong[of _ _ Least])
    using 12 qf3_equiv_preserves_range[of b a]
    unfolding a_def image_def qf3_equiv_def
    apply fast
    done
  have 15: "mat3\<^sub>1\<^sub>1 a = mat3\<^sub>1\<^sub>1 b"
           "\<And>x. mat3\<^sub>1\<^sub>1 a * (a $$ x) =
              (mat3\<^sub>1\<^sub>1 a * vec3\<^sub>1 x + mat3\<^sub>1\<^sub>2 a * vec3\<^sub>2 x + mat3\<^sub>1\<^sub>3 a * vec3\<^sub>3 x)\<^sup>2 +
              (a' $$ (vec2 (vec3\<^sub>2 x) (vec3\<^sub>3 x)))"
    using 4 5 10 lemma_1_4 unfolding b'_def v_def a_def by blast+
  have 16: "mat2\<^sub>1\<^sub>1 a' = mat3\<^sub>1\<^sub>1 a * mat3\<^sub>2\<^sub>2 a - (mat3\<^sub>1\<^sub>2 a)\<^sup>2"
    using 15(2)[of "vec3 0 1 0"]
    unfolding vec3_dot_def vec2_dot_def mat3_app_def mat2_app_def
              qf3_app_def qf2_app_def
    by simp
  define a\<^sub>2\<^sub>2 where "a\<^sub>2\<^sub>2 \<equiv> a $$ (vec3 0 1 0)"
  have 17: "a\<^sub>1\<^sub>1 = mat3\<^sub>1\<^sub>1 a" unfolding 7 15 by auto
  have 18: "a\<^sub>1\<^sub>2 = mat3\<^sub>1\<^sub>2 a" "a\<^sub>1\<^sub>3 = mat3\<^sub>1\<^sub>3 a" "a\<^sub>2\<^sub>2 = mat3\<^sub>2\<^sub>2 a" "a\<^sub>2\<^sub>2 = mat3\<^sub>2\<^sub>2 a"
    using 13(1) 17
    unfolding a_def v_def a\<^sub>1\<^sub>2_def a\<^sub>1\<^sub>3_def a\<^sub>2\<^sub>2_def
    by (auto simp add: algebra_simps
                       times_mat3_def vec3_dot_def mat3_app_def
                       mat3_transpose_def qf3_app_def qf3_action_def)
  have 19: "a ~ c"
    unfolding qf3_equiv_sym[of a c]
    unfolding a_def b_def qf3_equiv_def qf3_action_mul[symmetric]
    using 3 12 by (metis mat3_mul_det mult_1)
  have 20: "2 * (max \<bar>mat3\<^sub>1\<^sub>2 a\<bar> \<bar>mat3\<^sub>1\<^sub>3 a\<bar>) \<le> mat3\<^sub>1\<^sub>1 a"
    using 11 unfolding 17[symmetric] 18 a\<^sub>1\<^sub>2_def[symmetric] a\<^sub>1\<^sub>3_def[symmetric]
    by auto
  have 21: "(2 / sqrt 3) ^ 6 = 64 / 27" unfolding power_def by auto
  have "a\<^sub>1\<^sub>1 \<le> int (nat a\<^sub>2\<^sub>2)"
    unfolding a\<^sub>1\<^sub>1_def a\<^sub>2\<^sub>2_def
    apply (rule rev_iffD1[OF _ nat_int_comparison(3)])
    apply (rule wellorder_Least_lemma(2))
    using assms(2) 5 12
    apply (metis a_def b_def nat_0_le nat_int of_nat_0 qf3_action_app
                 qf3_equiv_def qf3_equiv_preserves_positive_definite
                 qf3_positive_definite_def qf3_positive_definite_positive
                 vec3.sel(2) zero_neq_one zero_vec3_def zless_nat_conj)
    done
  hence "a\<^sub>1\<^sub>1 \<le> a\<^sub>2\<^sub>2" using 1 by linarith
  hence "(mat3\<^sub>1\<^sub>1 a)\<^sup>2 \<le> a\<^sub>1\<^sub>1 * a\<^sub>2\<^sub>2" unfolding power2_eq_square using 1 17 by auto
  also have "... = mat2\<^sub>1\<^sub>1 a' + a\<^sub>1\<^sub>2\<^sup>2" using 16 17 18 by auto
  also have "... \<le> (2 / sqrt 3) * sqrt (mat3\<^sub>1\<^sub>1 b * mat_det b) + a\<^sub>1\<^sub>2\<^sup>2"
    using 10 by auto
  also have "... \<le> (2 / sqrt 3) * sqrt (mat3\<^sub>1\<^sub>1 a * mat_det a) + (mat3\<^sub>1\<^sub>1 a)\<^sup>2 / 4"
    using 11 13 15 17 18 a\<^sub>1\<^sub>2_def
          power2_le_iff_abs_le[of "real_of_int (mat3\<^sub>1\<^sub>1 a)" "(mat3\<^sub>1\<^sub>2 a) * 2"]
    by auto
  finally have "(3 / 4) * (mat3\<^sub>1\<^sub>1 a)\<^sup>2 \<le> (2 / sqrt 3) * sqrt (mat3\<^sub>1\<^sub>1 a * mat_det a)"
    by (simp add: algebra_simps)
  hence "(mat3\<^sub>1\<^sub>1 a)\<^sup>2 \<le> (2 / sqrt 3) ^ 3 * sqrt (mat3\<^sub>1\<^sub>1 a * mat_det a)"
    unfolding power2_eq_square power3_eq_cube by (simp add: algebra_simps)
  hence "((mat3\<^sub>1\<^sub>1 a)\<^sup>2)\<^sup>2 \<le> ((2 / sqrt 3) ^ 3 * sqrt (mat3\<^sub>1\<^sub>1 a * mat_det a))\<^sup>2"
    using 1(1) unfolding 17[symmetric] power2_eq_square
    by (metis of_int_power power2_eq_square power_mono zero_le_square)
  hence "(mat3\<^sub>1\<^sub>1 a) ^ 4 \<le> (2 / sqrt 3) ^ 6 * (sqrt (mat3\<^sub>1\<^sub>1 a * mat_det a))\<^sup>2"
    by (simp add: power_mult_distrib)
  hence "(mat3\<^sub>1\<^sub>1 a) ^ 4 \<le> (2 / sqrt 3) ^ 6 * mat3\<^sub>1\<^sub>1 a * mat_det a"
    using 4 5 13 17 lemma_1_3 by auto
  hence "(mat3\<^sub>1\<^sub>1 a) ^ 3 \<le> (2 / sqrt 3) ^ 6 * mat_det a"
    using 1(1) unfolding 17[symmetric]
    unfolding power_def apply (simp add: algebra_simps)
    apply (metis mult_left_le_imp_le of_nat_0_less_iff times_divide_eq_right)
    done
  hence "(mat3\<^sub>1\<^sub>1 a) ^ 3 \<le> (64 / 27) * mat_det a" using 21 by auto
  hence "root 3 ((mat3\<^sub>1\<^sub>1 a) ^ 3) \<le> root 3 ((64 / 27) * mat_det a)" by auto
  hence "root 3 ((mat3\<^sub>1\<^sub>1 a) ^ 3) \<le> root 3 (64 / 27) * root 3 (mat_det a)"
    unfolding real_root_mult by auto
  hence "mat3\<^sub>1\<^sub>1 a \<le> root 3 (64 / 27) * root 3 (mat_det a)"
    using odd_real_root_power_cancel by auto
  hence 22: "mat3\<^sub>1\<^sub>1 a \<le> (4 / 3) * root 3 (mat_det a)"
    using real_root_divide by force
  show ?thesis using 19 20 22 by blast
qed

text \<open>Theorem 1.3 from @{cite nathanson1996}.\<close>

theorem qf3_det_one_equiv_canonical:
  fixes f :: mat3
  assumes "mat_sym f"
  assumes "qf_positive_definite f"
  assumes "mat_det f = 1"
  shows "f ~ 1"
proof -
  obtain a where
    0: "f ~ a \<and>
        2 * (max \<bar>mat3\<^sub>1\<^sub>2 a\<bar> \<bar>mat3\<^sub>1\<^sub>3 a\<bar>) \<le> mat3\<^sub>1\<^sub>1 a \<and>
        mat3\<^sub>1\<^sub>1 a \<le> (4 / 3) * root 3 (mat_det a)"
    using assms lemma_1_6[of f] qf3_equiv_sym by auto
  have 1: "mat_sym a"
    using assms 0 qf3_equiv_preserves_sym by auto
  have 2: "qf_positive_definite a"
    using assms 0 qf3_equiv_preserves_positive_definite by auto
  have 3: "mat_det a = 1" using assms 0 qf3_equiv_preserves_det by auto
  have 4: "mat3\<^sub>1\<^sub>2 a = 0" "mat3\<^sub>1\<^sub>3 a = 0" using 0 3 by auto
  have "mat3\<^sub>1\<^sub>1 a \<ge> 1"
    apply (rule allE[OF 2[unfolded qf3_positive_definite_def], of "vec3 1 0 0"])
    unfolding zero_vec3_def vec3_dot_def mat3_app_def qf3_app_def
              qf3_positive_definite_def
    apply auto
    done
  hence 6: "mat3\<^sub>1\<^sub>1 a = 1" using 0 3 by auto
  define a' where "a' \<equiv>
    mat2
      (mat3\<^sub>2\<^sub>2 a) (mat3\<^sub>2\<^sub>3 a)
      (mat3\<^sub>3\<^sub>2 a) (mat3\<^sub>3\<^sub>3 a)
  "
  have 7: "mat_det a' = 1"
    using 3 4 6 unfolding a'_def mat2_det_def mat3_det_def by auto
  have 8: "mat_sym a'" using 1 unfolding a'_def mat2_sym_def mat3_sym_def by auto
  have 9: "qf_positive_definite a'"
  using 2 unfolding qf2_positive_definite_def qf3_positive_definite_def
  proof -
    assume 10: "\<forall>v. v \<noteq> 0 \<longrightarrow> a $$ v > 0"
    show "\<forall>v. v \<noteq> 0 \<longrightarrow> a' $$ v > 0"
    proof (rule; rule)
      fix v :: vec2
      assume "v \<noteq> 0"
      hence "vec3 0 (vec2\<^sub>1 v) (vec2\<^sub>2 v) \<noteq> 0"
        unfolding zero_vec2_def zero_vec3_def by (metis vec2.collapse vec3.inject)
      hence "a $$ (vec3 0 (vec2\<^sub>1 v) (vec2\<^sub>2 v)) > 0" using 10 by auto
      thus "a' $$ v > 0"
        unfolding a'_def vec2_dot_def vec3_dot_def
                  mat2_app_def mat3_app_def qf2_app_def qf3_app_def
                  qf2_positive_definite_def qf3_positive_definite_def
        by auto
    qed
  qed
  obtain u' where 11: "mat_det u' = 1" "a' \<cdot> u' = 1"
    using 7 8 9 qf2_det_one_equiv_canonical[of a']
    unfolding qf2_equiv_def
    by auto
  define u where "u \<equiv>
    mat3
      1 0 0
      0 (mat2\<^sub>1\<^sub>1 u') (mat2\<^sub>1\<^sub>2 u')
      0 (mat2\<^sub>2\<^sub>1 u') (mat2\<^sub>2\<^sub>2 u')
  "
  have 12: "mat_det u = 1"
    using 11 unfolding u_def mat2_det_def mat3_det_def by auto
  have 13: "a \<cdot> u = 1"
    using 1 4 6 11
    by (simp add: algebra_simps
                  a'_def u_def one_mat2_def one_mat3_def
                  times_mat2_def times_mat3_def
                  mat2_transpose_def mat3_transpose_def
                  qf2_action_def qf3_action_def mat3_sym_def)
  have "a ~ 1" using 12 13 unfolding qf3_equiv_def by blast
  thus ?thesis using 0 qf3_equiv_trans by blast
qed

end
