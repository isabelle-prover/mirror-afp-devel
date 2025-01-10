theory Cauchy_Eigenvalue_Interlacing
  imports Misc_Matrix_Results

begin

section "Rayleigh Quotient Lemmas"

definition rayleigh_quotient_complex ("\<rho>\<^sub>c") where
  "\<rho>\<^sub>c M x = (QF M x) / (x \<bullet>c x)"

definition rayleigh_quotient ("\<rho>") where
  "\<rho> M x = Re (\<rho>\<^sub>c M x)"

declare
  rayleigh_quotient_complex_def[simp]
  rayleigh_quotient_def[simp]

lemma rayleigh_quotient_negative: "A \<in> carrier_mat n n \<Longrightarrow> x \<in> carrier_vec n \<Longrightarrow> \<rho> A x = - \<rho> (- A) x"
  by auto

lemma rayleigh_quotient_complex_scale:
  fixes k :: real
  assumes "A \<in> carrier_mat n n"
  assumes "v \<in> carrier_vec n"
  assumes "k \<noteq> 0"
  shows "\<rho>\<^sub>c A v = \<rho>\<^sub>c A (k \<cdot>\<^sub>v v)"
proof-
  have "\<rho>\<^sub>c A v = (k^2 * ((A *\<^sub>v v) \<bullet>c v)) / (k^2 * (v \<bullet>c v))" using assms(3) by simp
  also have "... = (((k \<cdot>\<^sub>v (A *\<^sub>v v)) \<bullet>c (k \<cdot>\<^sub>v v))) / (k^2 * (v \<bullet>c v))"
    by (smt (verit, ccfv_SIG) assms(1) assms(2) more_arith_simps(11) mult_mat_vec_carrier power2_eq_square scalar_prod_smult_distrib smult_carrier_vec smult_scalar_prod_distrib vec_conjugate_real)
  also have "... = (((k \<cdot>\<^sub>v (A *\<^sub>v v)) \<bullet>c (k \<cdot>\<^sub>v v))) / (((k \<cdot>\<^sub>v v) \<bullet>c (k \<cdot>\<^sub>v v)))"
    by (simp add: power2_eq_square)
  also have "... = ((((A *\<^sub>v (k \<cdot>\<^sub>v v))) \<bullet>c (k \<cdot>\<^sub>v v))) / (((k \<cdot>\<^sub>v v) \<bullet>c (k \<cdot>\<^sub>v v)))"
    by (metis assms(1) assms(2) mult_mat_vec)
  also have "... = \<rho>\<^sub>c A (k \<cdot>\<^sub>v v)" by auto
  finally show ?thesis .
qed

lemma rayleigh_quotient_scale:
  fixes k :: real
  assumes "A \<in> carrier_mat n n"
  assumes "v \<in> carrier_vec n"
  assumes "k \<noteq> 0"
  shows "\<rho> A v = \<rho> A (k \<cdot>\<^sub>v v)"
  by (smt (verit, ccfv_SIG) rayleigh_quotient_complex_scale assms Groups.mult_ac(2) complex_norm_square conjugate_complex_def inner_prod_smult_left_right mult_divide_mult_cancel_left_if mult_mat_vec mult_mat_vec_carrier norm_of_real of_real_eq_0_iff power_eq_0_iff quadratic_form_def rayleigh_quotient_complex_def rayleigh_quotient_def)

lemma hermitian_rayleigh_quotient_real:
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat n n"
  assumes "v \<in> carrier_vec n"
  assumes "hermitian A"
  assumes "v \<noteq> 0\<^sub>v n"
  shows "\<rho>\<^sub>c A v \<in> Reals"
proof-
  have "QF A v \<in> Reals"
    using hermitian_quadratic_form_real assms by blast
  moreover have "inner_prod v v \<in> Reals" by (simp add: self_inner_prod_real)
  moreover have "inner_prod v v \<noteq> 0" using assms(2,4) by fastforce
  ultimately show ?thesis unfolding rayleigh_quotient_complex_def using Reals_divide by blast
qed

section "Vector Summation Lemmas"

lemma complex_vec_norm_sum:
  fixes x :: "complex vec"
  assumes "x \<in> carrier_vec n"
  shows "vec_norm x = csqrt ((\<Sum>i \<in> {..<n}. (cmod (x$i))^2))"
proof-
  have *: "\<And>i. i \<in> {..<n} \<Longrightarrow> (conjugate x)$i = conjugate (x$i)"
    using assms by auto
  have **: "\<And>i. i \<in> {..<n} \<Longrightarrow> (x$i) * conjugate (x$i) = (cmod (x$i))^2"
    using mult_conj_cmod_square by blast
  have "vec_norm x = csqrt (x \<bullet>c x)"
    by (simp add: vec_norm_def)
  also have "... = csqrt (\<Sum>i \<in> {..<n}. (x$i) * (conjugate x)$i)"
    by (metis assms atLeast0LessThan carrier_vecD dim_vec_conjugate scalar_prod_def)
  also have "... = csqrt (\<Sum>i \<in> {..<n}. (x$i) * conjugate (x$i))"
    by (simp add: *)
  also have "... = csqrt ((\<Sum>i \<in> {..<n}. (cmod (x$i))^2))" using ** by fastforce
  finally show ?thesis .
qed

lemma inner_prod_vec_sum:
  assumes "v \<in> carrier_vec n"
  assumes "w \<in> carrier_vec n"
  assumes "B \<subseteq> carrier_vec n"
  assumes "finite B"
  assumes "v = finsum_vec TYPE('a::conjugatable_ring) n (\<lambda>b. cs b \<cdot>\<^sub>v b) B"
  shows "inner_prod w v = (\<Sum>b \<in> B. cs b * inner_prod w b)"
proof-
  let ?vs = "\<lambda>b. cs b \<cdot>\<^sub>v b"
  let ?f = "\<lambda>i b. if i \<in> {..<n} then (?vs b)$i * (conjugate w)$i else 0"
  have f: "\<And>y. finite {x. ?f x y \<noteq> 0}"
  proof-
    fix y
    have "{x. ?f x y \<noteq> 0} \<subseteq> {..<n}" by (simp add: subset_eq)
    thus "finite {x. ?f x y \<noteq> 0}" using finite_nat_iff_bounded by blast
  qed
  have vs: "?vs \<in> B \<rightarrow> carrier_vec n" using assms(3) by force
  have b_scale: "\<And>i b. i \<in> {..<n} \<Longrightarrow> b \<in> B \<Longrightarrow> (?vs b)$i = cs b * b$i"
    using assms(3) by auto
  have assoc: "\<And>i b. (cs b * b$i) * (conjugate w)$i = cs b * (b$i * (conjugate w)$i)"
    using Groups.mult_ac(1) by blast

  have "inner_prod w v = (\<Sum>i \<in> {..<n}. v$i * (conjugate w)$i)"
    unfolding scalar_prod_def using atLeast0LessThan assms(2) by force
  moreover have "\<And>i. i \<in> {..<n} \<Longrightarrow> v$i = (\<Sum>b \<in> B. (?vs b)$i)"
    using index_finsum_vec[OF assms(4) _ vs] unfolding assms(5) by blast
  ultimately have "inner_prod w v = (\<Sum>i \<in> {..<n}. (\<Sum>b \<in> B. (?vs b)$i) * (conjugate w)$i)"
    by force
  also have "... = (\<Sum>i \<in> {..<n}. \<Sum>b \<in> B. (?vs b)$i * (conjugate w)$i)"
    by (simp add: sum_distrib_right)
  also have "... = (\<Sum>i \<in> {..<n}. \<Sum>b \<in> B. ?f i b)"
    by fastforce
  also have "... = Sum_any (\<lambda>i. \<Sum>b \<in> B. ?f i b)"
    using Sum_any.conditionalize[of "{..<n}" "\<lambda>i. (\<Sum>b \<in> B. ?f i b)"]
    by (smt (verit, ccfv_SIG) Sum_any.cong finite_nat_iff_bounded subset_eq sum.neutral)
  also have "... = (\<Sum>b \<in> B. (Sum_any (\<lambda>i. ?f i b)))"
    using Sum_any_sum_swap[OF assms(4) f, of "\<lambda>x. x"] .
  also have "... = (\<Sum>b \<in> B. (\<Sum>i \<in> {..<n}. (?vs b)$i * (conjugate w)$i))"
  proof-
    have "\<And>b. b \<in> B \<Longrightarrow> (\<Sum>i \<in> {..<n}. (?vs b)$i * (conjugate w)$i) = Sum_any (\<lambda>i. ?f i b)"
      using Sum_any.conditionalize[of "{..<n}"] by blast
    thus ?thesis by fastforce
  qed
  also have "... = (\<Sum>b \<in> B. (\<Sum>i \<in> {..<n}. (cs b * b$i) * (conjugate w)$i))"
    using b_scale by simp
  also have "... = (\<Sum>b \<in> B. (\<Sum>i \<in> {..<n}. cs b * (b$i * (conjugate w)$i)))"
    using assoc by force
  also have "... = (\<Sum>b \<in> B. cs b * (\<Sum>i \<in> {..<n}. b$i * (conjugate w)$i))"
    by (simp add: sum_distrib_left)
  also have "... = (\<Sum>b \<in> B. cs b * inner_prod w b)"
    unfolding scalar_prod_def using atLeast0LessThan assms(2) by force
  finally show ?thesis  .
qed

lemma sprod_vec_sum:
  assumes "v \<in> carrier_vec n"
  assumes "w \<in> carrier_vec n"
  assumes "B \<subseteq> carrier_vec n"
  assumes "finite B"
  assumes "v = finsum_vec TYPE('a::{comm_ring}) n (\<lambda>b. cs b \<cdot>\<^sub>v b) B"
  shows "w \<bullet> v = (\<Sum>b \<in> B. cs b * (w \<bullet> b))"
proof-
  let ?vs = "\<lambda>b. cs b \<cdot>\<^sub>v b"
  let ?f = "\<lambda>i b. if i \<in> {..<n} then (?vs b)$i * w$i else 0"
  have f: "\<And>y. finite {x. ?f x y \<noteq> 0}"
  proof-
    fix y
    have "{x. ?f x y \<noteq> 0} \<subseteq> {..<n}" by (simp add: subset_eq)
    thus "finite {x. ?f x y \<noteq> 0}" using finite_nat_iff_bounded by blast
  qed

  have vs: "?vs \<in> B \<rightarrow> carrier_vec n" using assms(3) by force
  have b_scale: "\<And>i b. i \<in> {..<n} \<Longrightarrow> b \<in> B \<Longrightarrow> (?vs b)$i = cs b * b$i"
    using assms(3) by auto
  have assoc: "\<And>i b. (cs b * b$i) * w$i = cs b * (b$i * w$i)"
    using Groups.mult_ac(1) by blast
  have B_dim: "\<And>b. b \<in> B \<Longrightarrow> dim_vec b = n"
    using assms(3) by fastforce

  have "w \<bullet> v = (\<Sum>i \<in> {..<n}. v$i * w$i)"
    unfolding scalar_prod_def using atLeast0LessThan[of n] assms(1)
    by (metis (no_types, lifting) Groups.mult_ac(2) carrier_vecD sum.cong)
  moreover have "\<And>i. i \<in> {..<n} \<Longrightarrow> v$i = (\<Sum>b \<in> B. (?vs b)$i)"
    using index_finsum_vec[OF assms(4) _ vs] unfolding assms(5) by blast
  ultimately have "w \<bullet> v = (\<Sum>i \<in> {..<n}. (\<Sum>b \<in> B. (?vs b)$i) * w$i)"
    by force
  also have "... = (\<Sum>i \<in> {..<n}. \<Sum>b \<in> B. (?vs b)$i * w$i)"
    by (simp add: sum_distrib_right)
  also have "... = (\<Sum>i \<in> {..<n}. \<Sum>b \<in> B. ?f i b)"
    by fastforce
  also have "... = Sum_any (\<lambda>i. \<Sum>b \<in> B. ?f i b)"
    using Sum_any.conditionalize[of "{..<n}" "\<lambda>i. (\<Sum>b \<in> B. ?f i b)"]
    by (smt (verit, ccfv_SIG) Sum_any.cong finite_nat_iff_bounded subset_eq sum.neutral)
  also have "... = (\<Sum>b \<in> B. (Sum_any (\<lambda>i. ?f i b)))"
    using Sum_any_sum_swap[OF assms(4) f, of "\<lambda>x. x"] .
  also have "... = (\<Sum>b \<in> B. (\<Sum>i \<in> {..<n}. (?vs b)$i * w$i))"
  proof-
    have "\<And>b. b \<in> B \<Longrightarrow> (\<Sum>i \<in> {..<n}. (?vs b)$i * w$i) = Sum_any (\<lambda>i. ?f i b)"
      using Sum_any.conditionalize[of "{..<n}"] by blast
    thus ?thesis by fastforce
  qed
  also have "... = (\<Sum>b \<in> B. (\<Sum>i \<in> {..<n}. (cs b * b$i) * w$i))"
    using b_scale by simp
  also have "... = (\<Sum>b \<in> B. (\<Sum>i \<in> {..<n}. cs b * (b$i * w$i)))"
    using assoc by force
  also have "... = (\<Sum>b \<in> B. cs b * (\<Sum>i \<in> {..<n}. b$i * w$i))"
    by (simp add: sum_distrib_left)
  also have "... = (\<Sum>b \<in> B. cs b * (\<Sum>i \<in> {..<n}. w$i * b$i))"
    by (metis (no_types, lifting) Groups.mult_ac(2) sum.cong)
  also have "... = (\<Sum>b \<in> B. cs b * (w \<bullet> b))"
    unfolding scalar_prod_def using atLeast0LessThan assms(3) B_dim by fastforce
  finally show ?thesis  .
qed

lemma mat_vec_mult_sum:
  assumes "v \<in> carrier_vec n"
  assumes "A \<in> carrier_mat n n"
  assumes "B \<subseteq> carrier_vec n"
  assumes "finite B"
  assumes "v = finsum_vec TYPE('a::comm_ring) n (\<lambda>b. cs b \<cdot>\<^sub>v b) B"
  shows "A *\<^sub>v v = finsum_vec TYPE('a::comm_ring) n (\<lambda>b. cs b \<cdot>\<^sub>v (A *\<^sub>v b)) B"
    (is "?lhs = ?rhs")
proof-
  have "\<And>i. i < n \<Longrightarrow> ?lhs$i = ?rhs$i"
  proof-
    fix i assume *: "i < n"
    let ?r = "row A i"
    have "?lhs$i = ?r \<bullet> v" using * assms(2) unfolding mult_mat_vec_def by simp
    also have "... = (\<Sum>b \<in> B. (cs b * (?r \<bullet> b)))"
      using sprod_vec_sum[OF assms(1) _ assms(3) assms(4) assms(5)] assms(2) by fastforce
    also have "... = (\<Sum>b \<in> B. (cs b * ((A *\<^sub>v b)$i)))"
      using * assms(2) unfolding mult_mat_vec_def by simp
    also have "... = (\<Sum>b \<in> B. ((cs b \<cdot>\<^sub>v (A *\<^sub>v b))$i))"
      using assms(2) * by force
    also have "... = (finsum_vec TYPE('a::comm_ring) n (\<lambda>b. cs b \<cdot>\<^sub>v (A *\<^sub>v b)) B)$i"
      using index_finsum_vec[OF assms(4) *]
      by (smt (verit, best) Pi_I assms(2) carrier_matD(1) carrier_vec_dim_vec dim_mult_mat_vec index_smult_vec(2) sum.cong)
    finally show "?lhs$i = ?rhs$i" by blast
  qed
  moreover have "?lhs \<in> carrier_vec n" using assms(1) assms(2) by force
  moreover have "?rhs \<in> carrier_vec n"
    by (smt (verit, ccfv_SIG) Pi_iff assms(2) assms(3) finsum_vec_closed mult_mat_vec_carrier smult_carrier_vec subsetD)
  ultimately show ?thesis by (metis (no_types, lifting) carrier_vecD eq_vecI)
qed

section "Module Span Lemmas"

context module
begin

lemma mk_coeffs_of_list:
  assumes "\<alpha> \<in> (set A \<rightarrow> carrier R)"
  shows "\<exists>c \<in> {0..<length A} \<rightarrow> carrier R. \<forall>v \<in> set A. mk_coeff A c v = \<alpha> v"
  using assms
proof(induct "length A" arbitrary: A)
  case 0
  thus ?case by fastforce
next
  case (Suc n)
  then obtain a A' where a: "A = A' @ [a]" by (metis length_Suc_conv_rev)
  hence "\<alpha> \<in> (set A' \<rightarrow> carrier R)" using Suc.prems by simp
  moreover from a have len_A': "n = length A'" using Suc(2) by auto
  ultimately obtain c' where c':
      "c' \<in> {0..<length A'} \<rightarrow> carrier R \<and> (\<forall>v \<in> set A'. mk_coeff A' c' v = \<alpha> v)"
    using Suc.hyps by blast

  have len_A'_A: "length A' = length A - 1" using Suc(2) len_A' by presburger
  moreover have "[0..<length A] = [0..<length A - 1] @ [length A - 1]"
    by (metis Suc(2) calculation len_A' upt_Suc_append zero_order(1))
  ultimately have A_A'_int: "[0..<length A] = [0..<length A'] @ [length A']" by presburger
  show ?case
  proof(cases "a \<in> set A'")
    case True
    hence A_A': "set A = set A'" using a by auto
    define c where "c \<equiv> (\<lambda>i. if i \<in> {0..<length A'} then c' i else \<zero>)"
    hence c_carrier: "c \<in> {0..<length A} \<rightarrow> carrier R" using c' by force
    moreover have "\<forall>v \<in> set A. mk_coeff A c v = \<alpha> v"
    proof
      fix v assume *: "v \<in> set A"
      show "mk_coeff A c v = \<alpha> v"
      proof(cases "v = a")
        case True
        hence "find_indices v A = (find_indices v A') @ [length A - 1]" 
        proof-
          from A_A'_int have "find_indices v A
              = (filter (\<lambda>i. A ! i = v) [0..<length A']) @ (filter (\<lambda>i. A ! i = v) [length A'])"
            unfolding find_indices_def by (metis Suc.hyps(2) filter_append len_A')
          moreover then have "(filter (\<lambda>i. A ! i = v) [0..<length A']) = (find_indices v A')"
            using a by auto
          moreover have "filter (\<lambda>i. A ! i = v) [length A'] = [length A']" by (simp add: True a)
          ultimately show ?thesis using len_A'_A by argo
        qed
        hence "map c (find_indices v A) = (map c (find_indices v A')) @ [c (length A - 1)]"
          by auto
        hence "foldr (\<oplus>) (map c (find_indices v A)) \<zero>
            = foldr (\<oplus>) (map c (find_indices v A')) (\<zero> \<oplus> c (length A - 1))"
          by (simp add: c_def len_A'_A)
        also have "... = (foldr (\<oplus>) (map c (find_indices v A')) \<zero>) \<oplus> c (length A - 1)"
          by (metis R.sumlist_def R.zero_closed c_carrier atLeastLessThan_iff c_def calculation cring_simprules(16) len_A'_A less_irrefl_nat mk_coeff_carrier mk_coeff_def)
        finally have "mk_coeff A c v = mk_coeff A' c v \<oplus> c (length A - 1)"
          unfolding mk_coeff_def R.sumlist_def .
        moreover have "c (length A - 1) = \<zero>" unfolding c_def using len_A' a by force
        moreover have "mk_coeff A' c v \<in> carrier R"
          by (smt (verit) Pi_iff c' c_def mk_coeff_carrier)
        ultimately have "mk_coeff A c v = mk_coeff A' c v" by algebra
        moreover have "mk_coeff A' c v = mk_coeff A' c' v"
          unfolding mk_coeff_def find_indices_def
          by (metis (mono_tags, lifting) c_def list.map_cong mem_Collect_eq set_filter set_upt)
        ultimately show ?thesis by (metis "*" A_A' c')
      next
        case v_neq_a: False
        hence "find_indices v A = find_indices v A'"
        proof-
          from A_A'_int have "find_indices v A
              = (filter (\<lambda>i. A ! i = v) [0..<length A']) @ (filter (\<lambda>i. A ! i = v) [length A'])"
            unfolding find_indices_def by (metis Suc.hyps(2) filter_append len_A')
          moreover have "(filter (\<lambda>i. A ! i = v) [0..<length A']) = find_indices v A'"
            unfolding find_indices_def
            by (smt (verit, ccfv_SIG) a append.right_neutral calculation filter.simps(1) filter.simps(2) filter_cong find_indices_def find_indices_snoc nth_append_length v_neq_a)
          moreover have "(filter (\<lambda>i. A ! i = v) [length A']) = []" using a v_neq_a by auto
          ultimately show ?thesis by force
        qed
        hence "mk_coeff A c v = mk_coeff A' c v" unfolding mk_coeff_def by fastforce
        also have "... = mk_coeff A' c' v"
          unfolding mk_coeff_def find_indices_def c_def
          by (smt (verit, best) atLeastLessThan_upt list.map_cong mem_Collect_eq set_filter)
        also have "... = \<alpha> v" using c' * A_A' by blast
        finally show ?thesis .
      qed
    qed
    ultimately show ?thesis by blast
  next
    case False
    hence A_A': "set A' = set A - {a}" by (simp add: a)
    define c where "c \<equiv> (\<lambda>i. if i \<in> {0..<length A'} then c' i else \<alpha> a)"
    hence "c \<in> {0..<length A} \<rightarrow> carrier R" using Suc.prems a c' by fastforce
    moreover have "\<forall>v \<in> set A. mk_coeff A c v = \<alpha> v"
    proof
      fix v assume *: "v \<in> set A"
      show "mk_coeff A c v = \<alpha> v"
      proof(cases "v = a")
        case v_eq_a: True
        hence "filter (\<lambda>i. A ! i = v) [0..<length A] = [length A - 1]"
        proof-
          from A_A'_int have "filter (\<lambda>i. A ! i = v) [0..<length A]
              = (filter (\<lambda>i. A ! i = v) [0..<length A']) @ (filter (\<lambda>i. A ! i = v) [length A'])"
            by (metis Suc.hyps(2) filter_append len_A')
          moreover have "(filter (\<lambda>i. A ! i = v) [0..<length A']) = []"
          proof-
            have "\<And>i. i < length A' \<Longrightarrow> A!i \<noteq> v" by (metis False a nth_append nth_mem v_eq_a)
            thus ?thesis by fastforce
          qed
          moreover have "(filter (\<lambda>i. A ! i = v) [length A']) = [length A']" by (simp add: a v_eq_a)
          ultimately show ?thesis by (metis Suc.hyps(2) diff_Suc_1 len_A' self_append_conv2)
        qed
        hence "map c (filter (\<lambda>i. A ! i = v) [0..<length A]) = [c (length A')]"
          by (metis len_A' Suc.hyps(2) diff_Suc_1 list.map(1) list.map(2))
        moreover have "c (length A') = \<alpha> v" by (simp add: v_eq_a c_def)
        ultimately have "mk_coeff A c v = \<alpha> v \<oplus> \<zero>" unfolding mk_coeff_def find_indices_def by force
        moreover have "\<alpha> v \<in> carrier R" using "*" Suc(3) by blast
        ultimately show ?thesis by auto
      next (* copied exactly from the other v_neq_a case *)
        case v_neq_a: False
        hence "find_indices v A = find_indices v A'"
        proof-
          from A_A'_int have "find_indices v A
              = (filter (\<lambda>i. A ! i = v) [0..<length A']) @ (filter (\<lambda>i. A ! i = v) [length A'])"
            unfolding find_indices_def by (metis Suc.hyps(2) filter_append len_A')
          moreover have "(filter (\<lambda>i. A ! i = v) [0..<length A']) = find_indices v A'"
            unfolding find_indices_def
            by (smt (verit, ccfv_SIG) a append.right_neutral calculation filter.simps(1) filter.simps(2) filter_cong find_indices_def find_indices_snoc nth_append_length v_neq_a)
          moreover have "(filter (\<lambda>i. A ! i = v) [length A']) = []" using a v_neq_a by auto
          ultimately show ?thesis by force
        qed
        hence "mk_coeff A c v = mk_coeff A' c v" unfolding mk_coeff_def by fastforce
        also have "... = mk_coeff A' c' v"
          unfolding mk_coeff_def find_indices_def c_def
          by (smt (verit, best) atLeastLessThan_upt list.map_cong mem_Collect_eq set_filter)
        also have "... = \<alpha> v" by (metis c' * a insert_iff v_neq_a vec_space.append_insert)
        finally show ?thesis .
      qed
    qed
    ultimately show ?thesis by blast
  qed
qed

lemma span_list_span:
  assumes "set A \<subseteq> carrier M"
  shows "span_list A = span (set A)"
proof-
  have "span_list A \<subseteq> span (set A)"
  proof(rule subsetI)
    fix x assume "x \<in> span_list A"
    then obtain c where c: "x = lincomb_list c A \<and> c \<in> {0..<length A} \<rightarrow> carrier R"
      unfolding span_list_def by blast
    hence 1: "lincomb_list c A = lincomb (mk_coeff A c) (set A)"
      using lincomb_list_as_lincomb[OF assms(1)] by presburger
    have "mk_coeff A c \<in> (set A) \<rightarrow> carrier R" by (simp add: c mk_coeff_carrier)
    hence 2: "lincomb (mk_coeff A c) (set A) \<in> span (set A)" unfolding span_def by blast
    show "x \<in> span (set A)" using 1 2 c by argo
  qed
  moreover have "span (set A) \<subseteq> span_list A"
  proof(rule subsetI)
    fix x assume *: "x \<in> span (set A)"
    then obtain \<alpha> where \<alpha>: "x = lincomb \<alpha> (set A) \<and> \<alpha> \<in> (set A \<rightarrow> carrier R)"
      using * finite_span assms by auto
    define \<alpha>' where "\<alpha>' = (\<lambda>v. if v \<in> set A then \<alpha> v else \<zero>)"
    hence \<alpha>_\<alpha>': "\<And>v. v \<in> set A \<Longrightarrow> \<alpha> v = \<alpha>' v" by presburger
    hence x_\<alpha>': "x = lincomb \<alpha>' (set A)"
      using \<alpha>
      unfolding lincomb_def
      by (smt (verit) M.add.finprod_cong' Pi_iff assms basic_trans_rules(31) carrier_is_submodule submoduleE(4))
    have 1: "\<alpha>' \<in> (set A \<rightarrow> carrier R)" by (simp add: Pi_cong \<alpha> \<alpha>'_def)
    then obtain c where c: "c \<in> {0..<length A} \<rightarrow> carrier R \<and> (\<forall>v \<in> set A. mk_coeff A c v = \<alpha>' v)"
      using mk_coeffs_of_list by blast
    have "mk_coeff A c = \<alpha>'" unfolding \<alpha>'_def by (metis mk_coeff_0 c \<alpha>_\<alpha>')
    hence "lincomb \<alpha>' (set A) = lincomb_list c A"
        using lincomb_list_as_lincomb[OF assms(1), of c] c by argo
    also have "... \<in> span_list A" using c in_span_listI by blast
    finally show "x \<in> span_list A" using x_\<alpha>' by blast
  qed
  ultimately show ?thesis by blast
qed

end

section "Module Homomorphism Linear Combination and Span Lemmas"

context mod_hom
begin

lemma lincomb_list_distrib:
  assumes "set S \<subseteq> carrier M"
  assumes "\<alpha> \<in> {..<length S} \<rightarrow> carrier R"
  shows "f (M.lincomb_list \<alpha> S) = N.lincomb_list \<alpha> (map f S)"
  using assms
proof(induct "length S" arbitrary: S \<alpha>)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then obtain v S' where v: "S = v # S'" by (metis length_Suc_conv)
  have 1: "n = length S'" using Suc(2) v by auto
  have 2: "set S' \<subseteq> carrier M" using Suc(3) v by auto
  have 3: "(\<alpha> \<circ> Suc) \<in> {..<length S'} \<rightarrow> carrier R" using "1" Suc(4) Suc.hyps(2) by fastforce
  
  have ih: "f (M.lincomb_list (\<alpha> \<circ> Suc) S') = N.lincomb_list (\<alpha> \<circ> Suc) (map f S')"
    using Suc.hyps(1)[OF 1 2 3] .
  
  have *: "M.lincomb_list \<alpha> (v # S') = (\<alpha> 0 \<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (M.lincomb_list (\<alpha> \<circ> Suc) S')"
    using M.lincomb_list_Cons .
  have "v \<in> carrier M" using Suc.prems(1) v by force
  moreover have "\<alpha> 0 \<in> carrier R" using Suc(4) Suc.hyps(2) by auto
  ultimately have "\<alpha> 0 \<odot>\<^bsub>M\<^esub> v \<in> carrier M" by blast
  moreover have "M.lincomb_list (\<alpha> \<circ> Suc) S' \<in> carrier M"
    by (metis (no_types, lifting) "1" "2" M.lincomb_list_carrier Pi_iff Suc(4) Suc.hyps(2) Suc_less_eq atLeastLessThan_iff lessThan_iff o_apply)
  ultimately have "f (M.lincomb_list \<alpha> S) = (f (\<alpha> 0 \<odot>\<^bsub>M\<^esub> v)) \<oplus>\<^bsub>N\<^esub> (f (M.lincomb_list (\<alpha> \<circ> Suc) S'))"
    using f_hom * v unfolding module_hom_def by force
  also have "... = (\<alpha> 0 \<odot>\<^bsub>N\<^esub> f v) \<oplus>\<^bsub>N\<^esub> (f (M.lincomb_list (\<alpha> \<circ> Suc) S'))"
    by (simp add: \<open>\<alpha> 0 \<in> carrier R\<close> \<open>v \<in> carrier M\<close>)
  also have "... = (\<alpha> 0 \<odot>\<^bsub>N\<^esub> f v) \<oplus>\<^bsub>N\<^esub> (N.lincomb_list (\<alpha> \<circ> Suc) (map f S'))" using ih by argo
  also have "... = N.lincomb_list \<alpha> (map f S)"
    using N.lincomb_list_Cons by (simp add: v)
  finally show ?case .
qed

lemma lincomb_distrib:
  assumes "inj_on f S"
  assumes "S \<subseteq> carrier M"
  assumes "\<alpha> \<in> S \<rightarrow> carrier R"
  assumes "\<forall>v \<in> S. \<alpha> v = \<beta> (f v)"
  assumes "finite S"
  shows "f (M.lincomb \<alpha> S) = N.lincomb \<beta> (f`S)"
proof-
  let ?\<alpha>' = "(\<lambda>v. (\<alpha> v) \<odot>\<^bsub>M\<^esub> v)"
  let ?\<beta>' = "(\<lambda>v. (\<beta> v) \<odot>\<^bsub>N\<^esub> v)"
  have *: "?\<alpha>' \<in> S \<rightarrow> carrier M" using assms(2,3) by auto
  have "f (M.lincomb \<alpha> S) = f (finsum M ?\<alpha>' S)" using M.lincomb_def by presburger
  also have "... = (\<Oplus>\<^bsub>N\<^esub>a\<in>S. f ((\<alpha> a) \<odot>\<^bsub>M\<^esub> a))" using hom_sum[OF assms(2) *] .
  also have "... = (\<Oplus>\<^bsub>N\<^esub>a\<in>S. (\<alpha> a) \<odot>\<^bsub>N\<^esub> (f a))"
  proof-
    have "\<forall>a \<in> S. a \<in> carrier M" using assms(2) by fastforce
    moreover have "\<forall>a \<in> S. \<alpha> a \<in> carrier R" using assms(3) by blast
    ultimately show ?thesis
      using f_hom unfolding module_hom_def by (simp add: N.M.add.finprod_cong')
  qed
  also have "... = (\<Oplus>\<^bsub>N\<^esub>a\<in>S. (\<beta> (f a)) \<odot>\<^bsub>N\<^esub> (f a))"
    by (smt (verit, del_insts) N.M.add.finprod_cong' M.summands_valid PiE Pi_I assms(2-4) basic_trans_rules(31) f_im f_smult)
  also have "... = (\<Oplus>\<^bsub>N\<^esub>a\<in>(f`S). (?\<beta>' a))"
    by (smt (verit, best) assms(1,4) M.summands_valid N.M.add.finprod_cong' N.M.add.finprod_reindex PiE Pi_I assms(2) assms(3) assms(4) basic_trans_rules(31) f_im f_smult imageE)
  also have "... = N.lincomb \<beta> (f`S)" using N.lincomb_def by presburger
  finally show ?thesis .
qed

lemma lincomb_distrib_obtain:
  assumes "inj_on f S"
  assumes "S \<subseteq> carrier M"
  assumes "\<alpha> \<in> S \<rightarrow> carrier R"
  assumes "\<forall>v \<in> S. \<alpha> v = \<beta> (f v)"
  assumes "finite S"
  obtains \<beta> where "(\<forall>v \<in> S. \<alpha> v = \<beta> (f v)) \<and> f (M.lincomb \<alpha> S) = N.lincomb \<beta> (f`S)"
proof-
  obtain \<beta> where \<beta>: "\<forall>v \<in> S. \<alpha> v = \<beta> (f v)"
  proof-
    let ?\<beta> = "\<lambda>y. \<alpha> (THE x. x \<in> S \<and> f x = y)"
    have "\<forall>v \<in> S. \<alpha> v = ?\<beta> (f v)"
    proof
      fix v assume "v \<in> S"
      then have "v = (THE x. x \<in> S \<and> f x = f v)"
        using assms(1) by (simp add: inj_on_def the_equality)
      thus "\<alpha> v = ?\<beta> (f v)" by argo
    qed
    thus ?thesis using that by fast
  qed
  thus ?thesis using lincomb_distrib that assms by blast
qed

lemma image_span_list:
  assumes "set vs \<subseteq> carrier M"
  shows "f`(M.span_list vs) = N.span_list (map f vs)" (is "?lhs = ?rhs")
proof-
  have "?lhs \<subseteq> ?rhs"
  proof(rule subsetI)
    fix w assume "w \<in> ?lhs"
    then obtain v where v: "v \<in> M.span_list vs \<and> f v = w" by blast
    then obtain \<alpha> where \<alpha>: "v = M.lincomb_list \<alpha> vs \<and> \<alpha> \<in> {..<length vs} \<rightarrow> carrier R"
      unfolding M.span_list_def by fastforce
    hence "f v = N.lincomb_list \<alpha> (map f vs)" using lincomb_list_distrib[OF assms(1)] v by blast
    thus "w \<in> ?rhs" using v \<alpha> unfolding N.span_list_def by force
  qed
  moreover have "?rhs \<subseteq> ?lhs"
  proof(rule subsetI)
    fix w assume "w \<in> ?rhs"
    then obtain \<alpha> where \<alpha>: "w = N.lincomb_list \<alpha> (map f vs) \<and> \<alpha> \<in> {..<length vs} \<rightarrow> carrier R"
      unfolding N.span_list_def by fastforce
    hence "w = f (M.lincomb_list \<alpha> vs)"
      using lincomb_list_distrib[OF assms] by presburger
    thus "w \<in> ?lhs" using \<alpha> unfolding M.span_list_def by fastforce
  qed
  ultimately show ?thesis by blast
qed

lemma image_span:
  assumes "finite vs"
  assumes "vs \<subseteq> carrier M"
  shows "f`(M.span vs) = N.span (f`vs)"
proof-
  obtain vs_list where vs_list: "set vs_list = vs" using assms(1) finite_list by blast
  have "f`vs = set (map f vs_list)" using vs_list by simp
  hence "N.span (f`vs) = N.span_list (map f vs_list)"
    by (metis N.span_list_span M.sum_simp assms(2) f_im image_subset_iff)
  moreover have "M.span vs = M.span_list vs_list"
    using M.span_list_span vs_list assms(2) by presburger
  ultimately show ?thesis using image_span_list assms vs_list by presburger
qed

end

section "Linear Map Lemmas"

lemma (in linear_map) inj_image_lin_indpt:
  assumes "inj_on T (carrier V)"
  assumes "S \<subseteq> carrier V"
  assumes "V.module.lin_indpt S"
  assumes "finite S"
  shows "W.module.lin_indpt (T`S)"
proof(rule ccontr)
  assume "\<not> W.module.lin_indpt (T`S)"
  then obtain B \<beta> b where B: "finite B
      \<and> B \<subseteq> T`S
      \<and> (\<beta> \<in> (B \<rightarrow> carrier K))
      \<and> (lincomb \<beta> B = \<zero>\<^bsub>W\<^esub>)
      \<and> (b\<in>B)
      \<and> (\<beta> b \<noteq> \<zero>\<^bsub>K\<^esub>)"
    using W.module.lin_dep_def by auto
  define A where "A \<equiv> {a \<in> S. T a \<in> B}"
  define \<alpha> where "\<alpha> \<equiv> (\<lambda>v. \<beta> (T v))"
  have 1: "inj_on T A"
    by (metis (no_types, lifting) assms(1,2) inj_on_subset A_def mem_Collect_eq subsetI)
  have 2: "A \<subseteq> carrier V" using A_def assms(2) by blast
  have 3: "\<alpha> \<in> A \<rightarrow> carrier K"
  proof
    fix x assume "x \<in> A"
    moreover then have "T x \<in> carrier W" using 2 by blast
    ultimately show "\<alpha> x \<in> carrier K" unfolding \<alpha>_def using B  A_def by blast
  qed
  have 4: "\<forall>v\<in>A. \<alpha> v = \<beta> (T v)" using \<alpha>_def by blast
  have 5: "finite A" using A_def assms(4) by force
  have "B = T`A" unfolding A_def using B by blast
  hence "lincomb \<beta> B = T (V.module.lincomb \<alpha> A)" using lincomb_distrib[OF 1 2 3 4 5] by argo
  hence "T (V.module.lincomb \<alpha> A) = \<zero>\<^bsub>W\<^esub>" using B by argo
  moreover have "T (\<zero>\<^bsub>V\<^esub>) = \<zero>\<^bsub>W\<^esub>" by auto
  ultimately have *: "(V.module.lincomb \<alpha> A) = \<zero>\<^bsub>V\<^esub>" using assms(1) by (simp add: 2 3 inj_onD)
  moreover obtain a where "T a = b \<and> a \<in> A" using B \<open>B = T ` A\<close> by blast
  moreover then have "\<alpha> a \<noteq> \<zero>\<^bsub>K\<^esub>" by (simp add: B \<alpha>_def)
  moreover have "A \<subseteq> S" using A_def by blast
  ultimately show False using assms(3) 5 3 V.module.lin_dep_def by blast
qed

lemma linear_map_mat:
  assumes "A \<in> carrier_mat n m"
  shows "linear_map class_ring (module_vec TYPE('a::{field,ring_1}) m) (module_vec TYPE('a) n) ((*\<^sub>v) A)"
    (is "linear_map ?K ?V ?W ?T") 
proof-
  have "vectorspace ?K ?V" using VS_Connect.vec_vs[of "m"] by blast
  moreover have "vectorspace ?K ?W" using VS_Connect.vec_vs[of "n"] by blast
  moreover have "mod_hom ?K ?V ?W ?T"
  proof-
    have V: "module ?K ?V" by (simp add: vec_module)
    moreover have W: "module ?K ?W" by (simp add: vec_module)
    moreover have "?T \<in> LinearCombinations.module_hom ?K ?V ?W"
    proof-
      have "?T \<in> carrier ?V \<rightarrow> carrier ?W" by (metis Pi_I assms mult_mat_vec_carrier vec_space.cV)
      moreover have "\<forall>v\<^sub>1 \<in> carrier ?V. \<forall>v\<^sub>2 \<in> carrier ?V. ?T (v\<^sub>1 + v\<^sub>2) = ?T v\<^sub>1 + ?T v\<^sub>2"
        by (metis module_vec_def assms monoid_record_simps(1) mult_add_distrib_mat_vec)
      moreover have "\<forall>\<alpha> \<in> carrier ?K. \<forall>v \<in> carrier ?V. ?T (\<alpha> \<cdot>\<^sub>v v) = \<alpha> \<cdot>\<^sub>v (?T v)"
        by (metis assms mult_mat_vec vec_space.cV)
      ultimately show ?thesis unfolding module_vec_def module_hom_def by force
    qed
    ultimately show ?thesis
      unfolding mod_hom_def mod_hom_axioms_def by blast
  qed
  ultimately show ?thesis unfolding linear_map_def by blast
qed

section "Courant-Fischer Minimax Theorem"

text
  "We follow the proof given in this set of lecture notes by Dr. David Bindel:
  https://www.cs.cornell.edu/courses/cs6210/2019fa/lec/2019-11-04.pdf."

definition sup_defined :: "'a::preorder set \<Rightarrow> bool" where
  "sup_defined S \<longleftrightarrow> S \<noteq> {} \<and> bdd_above S"

definition inf_defined :: "'a::preorder set \<Rightarrow> bool" where
  "inf_defined S \<longleftrightarrow> S \<noteq> {} \<and> bdd_below S"

locale hermitian_mat = complex_vec_space n for n +
  fixes A :: "complex mat"
  assumes dim_is: "A \<in> carrier_mat n n"
  assumes is_herm: "hermitian A"
begin

definition dimensional :: "complex vec set \<Rightarrow> nat \<Rightarrow> bool" where
  "dimensional \<V> k \<longleftrightarrow> (\<exists>vs. \<V> = span vs \<and> card vs = k \<and> vs \<subseteq> carrier_vec n \<and> lin_indpt vs)"

lemma dimensional_n: "dimensional \<V> k \<Longrightarrow> \<V> \<subseteq> carrier_vec n"
  using hermitian_mat.dimensional_def hermitian_mat_axioms by auto

lemma dimensional_n_vec: "\<And>v. v \<in> \<V> \<Longrightarrow> dimensional \<V> k \<Longrightarrow> v \<in> carrier_vec n"
  using dimensional_n by fast

text "Note here that we refer to the Inf and Sup rather than the Min and Max."

definition rayleigh_min:
  "rayleigh_min \<V> = Inf {\<rho> A v | v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V> \<and> vec_norm v = 1}"

definition rayleigh_max:
  "rayleigh_max \<V> = Sup {\<rho> A v | v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V> \<and> vec_norm v = 1}"

definition maximin :: "nat \<Rightarrow> real" where
  "maximin k = Sup {rayleigh_min \<V> | \<V>. dimensional \<V> k}"

definition minimax :: "nat \<Rightarrow> real" where
  "minimax k = Inf {rayleigh_max \<V> | \<V>. dimensional \<V> (n - k + 1)}"

definition maximin_defined where
  "maximin_defined k \<longleftrightarrow> sup_defined {rayleigh_min \<V> | \<V>. dimensional \<V> k}"
                               
definition minimax_defined where
  "minimax_defined k \<longleftrightarrow> inf_defined {rayleigh_max \<V> | \<V>. dimensional \<V> (n - k + 1)}"

end

locale courant_fischer = hermitian_mat n for n +
  fixes \<Lambda> U :: "complex mat"
  fixes es :: "complex list"
  assumes eigvals: "eigvals_of A es"
  assumes eigvals_sorted: "sorted_wrt (\<ge>) es"
  assumes A_decomp: "real_diag_decomp A \<Lambda> U
      \<and> diag_mat \<Lambda> = es
      \<and> set es \<subseteq> Reals
      \<and> U \<in> carrier_mat n n
      \<and> \<Lambda> \<in> carrier_mat n n"
begin

sublocale conjugatable_vec_space "TYPE(complex)" n .

lemma dim: "local.dim = n"
  by (simp add: dim_is_n)

lemma fin_dim: "fin_dim" by simp

lemma gr_n_lin_dpt:
  assumes "B \<subseteq> carrier_vec n"
  assumes "card B > local.dim"
  shows "lin_dep B"
  using li_le_dim(2)[of B] dim fin_dim assms by linarith

lemma rayleigh_kx:
  assumes "v \<in> carrier_vec n"
  assumes "k \<noteq> 0"
  assumes "v \<noteq> 0\<^sub>v n"
  shows "\<rho> A (k \<cdot>\<^sub>v v) = \<rho> A v"
proof-
  let ?v' = "(k \<cdot>\<^sub>v v)"
  have "(A *\<^sub>v ?v') \<bullet>c ?v' = (cmod k)^2 * (QF A v)"
    by (smt (verit, ccfv_SIG) dim_is assms(1) carrier_vecD cring_simprules(11) dim_vec_conjugate index_smult_vec(2) inner_prod_smult_right mult_conj_cmod_square mult_mat_vec mult_mat_vec_carrier quadratic_form_def scalar_prod_smult_left)
  moreover have "?v' \<bullet>c ?v' = (cmod k)^2 * (v \<bullet>c v)"
    by (metis assms(1) cring_simprules(11) dim_vec_conjugate index_smult_vec(2) inner_prod_smult_right mult_conj_cmod_square scalar_prod_smult_left)
  ultimately show "\<rho> A ?v' = \<rho> A v" by (simp add: assms(2))
qed

lemma unit_vec_rayleigh_formula:
  assumes unit_v: "vec_norm v = 1"
  assumes v_dim: "v \<in> carrier_vec n"
  shows "\<rho> A v = (\<Sum>j \<in> {..<n}. es!j * (cmod ((U\<^sup>H *\<^sub>v v)$j))^2)"
proof-
  have U_\<Lambda>: "unitary U \<and> unitary U\<^sup>H" "A = U * \<Lambda> * U\<^sup>H" "U\<^sup>H \<in> carrier_mat n n"
      apply (metis A_decomp adjoint_is_conjugate_transpose real_diag_decomp_def unitarily_equiv_def unitary_adjoint unitary_diag_def)
     apply (metis A_decomp adjoint_is_conjugate_transpose real_diag_decomp_def similar_mat_wit_def unitarily_equiv_def unitary_diag_def)
    by (simp add: A_decomp)
  have"diagonal_mat \<Lambda>" using A_decomp unfolding real_diag_decomp_def by fastforce
  hence \<Lambda>_diag_mult: "\<And>x i. x \<in> carrier_vec n \<Longrightarrow> i \<in> {..<n} \<Longrightarrow> (\<Lambda> *\<^sub>v x)$i = (\<Lambda>$$(i,i) * x$i)"
    using A_decomp diagonal_mat_mult_vec by blast
  have \<Lambda>_diag_eigenvals: "\<And>i. i \<in> {..<n} \<Longrightarrow> \<Lambda>$$(i,i) = es!i"
    using A_decomp
    unfolding diag_mat_def
    by (smt (verit, del_insts) carrier_matD(1) diff_zero length_map length_upt lessThan_iff nth_map nth_upt semiring_norm(50))

  define x where "x \<equiv> U\<^sup>H *\<^sub>v v"
  hence x_dim: "x \<in> carrier_vec n"
    using U_\<Lambda>(3) mult_mat_vec_carrier v_dim by blast
  hence x_conj_dim: "conjugate x \<in> carrier_vec n" by simp
  have x_norm: "vec_norm x = 1" using U_\<Lambda> unit_v unitary_vec_norm v_dim x_def by presburger

  have *: "\<And>i. i \<in> {..<n} \<Longrightarrow> (conjugate x)$i = conjugate (x$i)"
    unfolding conjugate_vec_def using x_dim by auto

  have "v \<bullet>c v = 1" using unit_v csqrt_eq_1 unfolding vec_norm_def by blast
  hence "QF A v / Complex_Matrix.inner_prod v v = QF A v" by simp
  hence "\<rho> A v = complex_of_real (Re (QF A v))"
    unfolding rayleigh_quotient_def by simp
  also have "... = QF A v"
    using hermitian_quadratic_form_real[OF dim_is v_dim is_herm] by simp
  also have "... = inner_prod v ((U * \<Lambda> * U\<^sup>H) *\<^sub>v v)"
    unfolding quadratic_form_def using U_\<Lambda> by blast
  also have "... = inner_prod v (U *\<^sub>v ((\<Lambda> * U\<^sup>H) *\<^sub>v v))"
    by (smt (verit, best) A_decomp More_Matrix.carrier_vec_conjugate assoc_mat_mult_vec' carrier_dim_vec mat_vec_mult_assoc transpose_carrier_mat v_dim)
  also have "... = inner_prod (U\<^sup>H *\<^sub>v v) ((\<Lambda> * U\<^sup>H) *\<^sub>v v)"
    by (metis A_decomp More_Matrix.carrier_vec_conjugate adjoint_def_alter adjoint_is_conjugate_transpose mult_carrier_mat mult_mat_vec_carrier transpose_carrier_mat v_dim)
  also have "... = (\<Lambda> *\<^sub>v x) \<bullet>c x"
    by (metis A_decomp More_Matrix.carrier_vec_conjugate carrier_vecD mat_vec_mult_assoc transpose_carrier_mat v_dim x_def)
  also have "... = (\<Sum>j \<in> {..<n}. (\<Lambda> *\<^sub>v x)$j * (conjugate x)$j)"
    unfolding inner_prod_def scalar_prod_def using atLeast0LessThan x_dim by auto
  also have "... = (\<Sum>j \<in> {..<n}. (\<Lambda>$$(j,j) * x$j) * (conjugate x)$j)" 
    using \<Lambda>_diag_mult x_dim by auto
  also have "... = (\<Sum>j \<in> {..<n}. (es!j * x$j) * (conjugate x)$j)"
    using \<Lambda>_diag_eigenvals by simp
  also have "... = (\<Sum>j \<in> {..<n}. (es!j * x$j) * conjugate (x$j))"
    using * by simp
  also have "... = (\<Sum>j \<in> {..<n}. es!j * (cmod (x$j))^2)"
    by (smt (verit) cring_simprules(11) mult_conj_cmod_square of_real_mult of_real_sum sum.cong)
  finally show "\<rho> A v = (\<Sum>j \<in> {..<n}. es!j * (cmod (x$j))^2)" 
    using of_real_eq_iff by blast
qed

lemma rayleigh_bdd_below':
  assumes "k \<le> n"
  shows "\<exists>m. \<forall>v \<in> carrier_vec n. v \<noteq> 0\<^sub>v n \<longrightarrow> \<rho> A v \<ge> m"
proof-
  define m where "m \<equiv> Min (Re ` set es)"
  have "\<And>v. v \<in> carrier_vec n \<Longrightarrow> v \<noteq> 0\<^sub>v n \<Longrightarrow> \<rho> A v \<ge> m"
  proof-
    fix v :: "complex vec"
    assume *: "v \<in> carrier_vec n" "v \<noteq> 0\<^sub>v n"
    define v' where "v' \<equiv> vec_normalize v"
    have v': "vec_norm v' = 1 \<and> v' \<in> carrier_vec n"
      using normalized_vec_norm[of v n] unfolding vec_norm_def v'_def
      using * csqrt_1 normalized_vec_dim by presburger
    have "\<rho> A v = \<rho> A v'"
      by (metis "*"(1) normalize_zero rayleigh_kx v' v'_def vec_eq_norm_smult_normalized vec_norm_zero)
    also have "... = (\<Sum>i \<in> {..<n}. es!i * (cmod ((U\<^sup>H *\<^sub>v v')$i))^2)"
      using unit_vec_rayleigh_formula * v' by blast
    also have "... \<ge> m"
    proof-
      have "vec_norm (U\<^sup>H *\<^sub>v v') = 1"
        by (metis v' A_decomp Complex_Matrix.unitary_def adjoint_dim_row adjoint_is_conjugate_transpose carrier_matD(2) real_diag_decomp_def unitary_adjoint unitary_diagD(3) unitary_vec_norm)
      moreover have "vec_norm (U\<^sup>H *\<^sub>v v') = csqrt (\<Sum>i \<in> {..<n}. (cmod ((U\<^sup>H *\<^sub>v v')$i))^2)"
        by (metis complex_vec_norm_sum A_decomp carrier_dim_vec carrier_matD(2) dim_mult_mat_vec dim_row_conjugate index_transpose_mat(2))
      ultimately have norm: "(\<Sum>i \<in> {..<n}. (cmod ((U\<^sup>H *\<^sub>v v')$i))^2) = 1"
        by (metis Re_complex_of_real one_complex.sel(1) one_power2 power2_csqrt)

      have "finite (Re ` set es)" by simp
      hence "\<forall>x \<in> Re ` set es. m \<le> x" using Min_le m_def by blast
      moreover have "\<forall>i \<in> {..<n}. \<exists>x \<in> Re ` set es. x = es!i"
        by (metis A_decomp carrier_matD(1) diag_mat_length image_eqI lessThan_iff nth_mem of_real_Re subsetD)
      ultimately have "\<And>i. i \<in> {..<n} \<Longrightarrow> m \<le> es!i"
        by (metis Im_complex_of_real Re_complex_of_real less_eq_complex_def)
      hence ineq:
          "\<And>i. i \<in> {..<n} \<Longrightarrow>  m * (cmod ((U\<^sup>H *\<^sub>v v')$i))^2 \<le> es!i * (cmod ((U\<^sup>H *\<^sub>v v')$i))^2"
        by (metis conjugate_square_positive mult_conj_cmod_square mult_right_mono of_real_hom.hom_mult)
        
      have "m \<le> m * (\<Sum>i \<in> {..<n}. (cmod ((U\<^sup>H *\<^sub>v v')$i))^2)" using norm by auto
      also have "... = (\<Sum>i \<in> {..<n}. m * (cmod ((U\<^sup>H *\<^sub>v v')$i))^2)"
        by (simp add: mult_hom.hom_sum)
      also have "... \<le> (\<Sum>i \<in> {..<n}. es!i * (cmod ((U\<^sup>H *\<^sub>v v')$i))^2)"
        by (smt (verit, best) of_real_sum sum_mono ineq)
      finally show ?thesis
        by (metis Im_complex_of_real Re_complex_of_real less_eq_complex_def)
    qed
    finally show "\<rho> A v \<ge> m" by (simp add: less_eq_complex_def)
  qed
  thus ?thesis by blast
qed

lemma rayleigh_bdd_below:
  assumes "dimensional \<V> k"
  assumes "k \<le> n"
  shows "\<exists>m. \<forall>v \<in> \<V>. v \<noteq> 0\<^sub>v n \<longrightarrow> \<rho> A v \<ge> m"
  using assms
  unfolding dimensional_def
  by (meson span_is_subset2 subsetI rayleigh_bdd_below' span_closed span_mem)

lemma rayleigh_min_exists:
  assumes "dimensional \<V> k"
  assumes "k \<le> n"
  shows "\<forall>x \<in> {\<rho> A v | v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V> \<and> vec_norm v = 1}. rayleigh_min \<V> \<le> x"
  using rayleigh_bdd_below[OF assms(1) assms(2)]
  unfolding rayleigh_min
  by (smt (verit) bdd_below.I cInf_lower mem_Collect_eq)

lemma courant_fischer_unit_rayleigh_helper2:
  assumes "dimensional \<V> (k + 1)"
  shows "\<exists>v. vec_norm v = 1 \<and> v \<in> \<V> \<and> v \<noteq> 0\<^sub>v n \<and> \<rho> A v \<le> es!k"
proof-
  have suc_k_leq_n: "k + 1 \<le> n"
    using assms(1) unfolding dimensional_def using gr_n_lin_dpt
    by (metis dim fin_dim li_le_dim(2))
  obtain v where v:
      "v \<in> carrier_vec n" "vec_norm v = 1" "(\<forall>j < k. (U\<^sup>H *\<^sub>v v)$j = 0) \<and> v \<noteq> 0\<^sub>v n \<and> v \<in> \<V>"
  proof-
    let ?k_kernel = "{v \<in> carrier_vec n. (\<forall>j < k. (U\<^sup>H *\<^sub>v v)$j = 0)}"
    obtain v where v: "v \<in> ?k_kernel \<inter> \<V> \<and> v \<noteq> 0\<^sub>v n"
    proof-
      obtain B\<^sub>\<V> where B\<^sub>\<V>: "\<V> = span B\<^sub>\<V> \<and> card B\<^sub>\<V> = k + 1 \<and> B\<^sub>\<V> \<subseteq> carrier_vec n \<and> lin_indpt B\<^sub>\<V>"
        using assms unfolding dimensional_def by blast
      obtain B\<^sub>k where B\<^sub>k: "span B\<^sub>k \<subseteq> ?k_kernel \<and> card B\<^sub>k = n - k \<and> B\<^sub>k \<subseteq> carrier_vec n \<and> lin_indpt B\<^sub>k"
      proof-
        obtain M where M: "M * U\<^sup>H = 1\<^sub>m n \<and> U\<^sup>H * M = 1\<^sub>m n \<and> M \<in> carrier_mat n n"
          by (metis A_decomp Complex_Matrix.unitary_def adjoint_dim_row adjoint_is_conjugate_transpose carrier_matD(2) mat_mult_left_right_inverse real_diag_decomp_def unitary_adjoint unitary_diagD(3) unitary_simps(1))
        define B\<^sub>k where "B\<^sub>k = set (drop k (cols M))"
        hence "B\<^sub>k \<subseteq> set (cols M)" by (meson set_drop_subset)
        hence lin_indpt:  "lin_indpt B\<^sub>k"
          by (metis M A_decomp More_Matrix.carrier_vec_conjugate det_zero_low_rank distinct_cols_id idom_vec.lin_dep_cols_imp_det_0 lin_indpt_id linorder_not_le one_carrier_mat rank_mat_mul_right supset_ld_is_ld transpose_carrier_mat vec_space.lin_indpt_full_rank)

        have 1: "span B\<^sub>k \<subseteq> ?k_kernel"
        proof
          fix v assume *: "v \<in> span B\<^sub>k"
          then obtain cs where "v = lincomb cs B\<^sub>k"
            by (metis (no_types, lifting) M \<open>B\<^sub>k \<subseteq> set (cols M)\<close> carrier_matD(1) cols_dim fin_dim finite_in_span li_le_dim(1) lin_indpt order_trans)
          hence sum: "U\<^sup>H *\<^sub>v v = finsum_vec TYPE(complex) n (\<lambda>b. (cs b) \<cdot>\<^sub>v (U\<^sup>H *\<^sub>v b)) B\<^sub>k"
            using mat_vec_mult_sum[of v n "U\<^sup>H" B\<^sub>k cs] unfolding lincomb_def
            by (metis A_decomp B\<^sub>k_def List.finite_set M More_Matrix.carrier_vec_conjugate \<open>B\<^sub>k \<subseteq> set (cols M)\<close> \<open>v = lincomb cs B\<^sub>k\<close> basic_trans_rules(23) carrier_matD(1) cols_dim finsum_vec lincomb_closed transpose_carrier_mat)

          have "\<And>i. i < k \<Longrightarrow> (U\<^sup>H *\<^sub>v v)$i = 0"
          proof-
            fix i assume *: "i < k"
            have cs: "(\<lambda>b. cs b \<cdot>\<^sub>v (U\<^sup>H *\<^sub>v b)) \<in> B\<^sub>k \<rightarrow> carrier_vec n"
            proof
              fix x assume "x \<in> B\<^sub>k"
              thus "cs x \<cdot>\<^sub>v (U\<^sup>H *\<^sub>v x) \<in> carrier_vec n"
                by (metis A_decomp carrier_dim_vec carrier_matD(2) dim_mult_mat_vec dim_row_conjugate index_smult_vec(2) index_transpose_mat(2))
            qed
            have B\<^sub>k: "\<And>b. b \<in> B\<^sub>k \<Longrightarrow> (U\<^sup>H *\<^sub>v b)$i = 0"
            proof-
              fix b assume **: "b \<in> B\<^sub>k"
              then obtain j' where "b = drop k (cols M)!j' \<and> j' < n - k"
                by (metis B\<^sub>k_def M carrier_matD(2) cols_length in_set_conv_nth length_drop)
              then obtain j where j: "b = (cols M)!j \<and> j \<ge> k \<and> j < n"
                by (metis Groups.add_ac(2) M add_leD1 carrier_matD(2) cols_length le_add2 less_diff_conv nth_drop suc_k_leq_n)

              have "i < n \<and> j < n \<and> i \<noteq> j" using * j by simp
              hence "0 = (1\<^sub>m n)$$(i,j)" by simp
              also have "... = (U\<^sup>H * M)$$(i,j)"
                using M by argo
              also have "... = row U\<^sup>H i \<bullet> col M j"
                by (metis "*" M add_leD1 carrier_matD(1) carrier_matD(2) dual_order.strict_trans1 index_mult_mat(1) index_mult_mat(2) j suc_k_leq_n)
              also have "... = row U\<^sup>H i \<bullet> b"
                using j M by auto
              also have "... = (U\<^sup>H *\<^sub>v b)$i"
                by (metis "*" A_decomp carrier_matD(2) dim_row_conjugate dual_order.strict_trans dual_order.strict_trans1 index_mult_mat_vec index_transpose_mat(2) j)
              finally show "(U\<^sup>H *\<^sub>v b)$i = 0" by presburger 
            qed

            have "(U\<^sup>H *\<^sub>v v)$i = (finsum_vec TYPE(complex) n (\<lambda>b. (cs b) \<cdot>\<^sub>v (U\<^sup>H *\<^sub>v b)) B\<^sub>k)$i"
              using sum by simp
            also have "... = (\<Sum>b \<in> B\<^sub>k. ((cs b) \<cdot>\<^sub>v (U\<^sup>H *\<^sub>v b))$i)"
              using index_finsum_vec[of B\<^sub>k i n "(\<lambda>b. (cs b) \<cdot>\<^sub>v (U\<^sup>H *\<^sub>v b))"] cs "*" B\<^sub>k_def suc_k_leq_n
              by fastforce
            also have "... = (\<Sum>b \<in> B\<^sub>k. (cs b) * ((U\<^sup>H *\<^sub>v b))$i)"
              using "*" A_decomp suc_k_leq_n by force
            also have "... = (\<Sum>b \<in> B\<^sub>k. (cs b) * 0)"
              using B\<^sub>k by fastforce
            also have "... = 0"
              by simp
            finally show "(U\<^sup>H *\<^sub>v v)$i = 0" .
          qed
          thus "v \<in> ?k_kernel"
            by (smt (verit) "*" M \<open>B\<^sub>k \<subseteq> set (cols M)\<close> basic_trans_rules(23) carrier_matD(1) cols_dim mem_Collect_eq span_closed)
        qed
        have 2: "card B\<^sub>k = n - k"
        proof-
          have "distinct (cols M)"
            by (metis A_decomp M More_Matrix.carrier_vec_conjugate conjugatable_vec_space.distinct_cols_id lin_indpt_full_rank lin_indpt_id linorder_not_le non_distinct_low_rank one_carrier_mat rank_mat_mul_right transpose_carrier_mat)
          hence "card B\<^sub>k = length (drop k (cols M))"
            using B\<^sub>k_def distinct_card distinct_drop by blast
          moreover have "length (cols M) = n" using M by force
          ultimately show ?thesis by force
        qed
        have 3: "B\<^sub>k \<subseteq> carrier_vec n"
          by (metis M \<open>B\<^sub>k \<subseteq> set (cols M)\<close> basic_trans_rules(23) carrier_matD(1) cols_dim)

        from 1 2 3 lin_indpt that show ?thesis by blast
      qed
      define B where "B = B\<^sub>\<V> \<union> B\<^sub>k"
      have "B\<^sub>\<V> \<inter> B\<^sub>k \<noteq> {} \<Longrightarrow> ?thesis"
      proof-
        assume *: "B\<^sub>\<V> \<inter> B\<^sub>k \<noteq> {}"
        have "0\<^sub>v n \<notin> B\<^sub>\<V>" by (simp add: B\<^sub>\<V> vs_zero_lin_dep)
        moreover have "0\<^sub>v n \<notin> B\<^sub>k" by (simp add: B\<^sub>k vs_zero_lin_dep)
        ultimately obtain b where b: "b \<in> B\<^sub>\<V> \<inter> B\<^sub>k \<and> b \<noteq> 0\<^sub>v n" using * by blast
        moreover then have "b \<in> \<V>" by (simp add: B\<^sub>\<V> span_mem)
        moreover have "b \<in> ?k_kernel"
          by (metis (no_types, lifting) B\<^sub>k IntE Set.basic_monos(7) b in_own_span)
        ultimately show ?thesis using that by fast
      qed
      moreover have "B\<^sub>\<V> \<inter> B\<^sub>k = {} \<Longrightarrow> ?thesis"
      proof-
        assume *: "B\<^sub>\<V> \<inter> B\<^sub>k = {}"
        hence "card (B\<^sub>\<V> \<union> B\<^sub>k) = card B\<^sub>\<V> + card B\<^sub>k"
          by (simp add: B\<^sub>\<V> B\<^sub>k card_Un_disjnt disjnt_def li_le_dim(1))
        hence "card B > n" using B_def B\<^sub>\<V> B\<^sub>k suc_k_leq_n by presburger
        moreover have "B \<subseteq> carrier_vec n" unfolding B_def using B\<^sub>\<V> B\<^sub>k by blast
        ultimately have lin_dep: "lin_dep B" using gr_n_lin_dpt dim by presburger
        obtain cs cs' where
            eq: "lincomb cs B\<^sub>\<V> = lincomb cs' B\<^sub>k \<and> (\<exists>b \<in> B\<^sub>\<V>. cs b \<noteq> 0) \<and> (\<exists>b \<in> B\<^sub>k. cs' b \<noteq> 0)"
        proof-
          obtain cs where cs: "lincomb cs B = 0\<^sub>v n \<and> (\<exists>b \<in> B. cs b \<noteq> 0)"
            by (metis lin_dep \<open>B \<subseteq> carrier_vec n\<close> \<open>n < card B\<close> bot_nat_0.extremum_strict card.infinite finite_lin_indpt2)
          define cs' where "cs' = (\<lambda>v. - cs v)"
          have "\<And>i. i < n \<Longrightarrow> (lincomb cs B\<^sub>\<V>)$i = (lincomb cs' B\<^sub>k)$i"
          proof-
            fix i
            assume **: "i < n"
            have "0 = (lincomb cs B)$i"
              by (simp add: "**" cs)
            also have "... = (\<Sum>b \<in> B. (cs b \<cdot>\<^sub>v b)$i)"
              by (smt (verit, ccfv_SIG) ** R.add.finprod_cong' \<open>B \<subseteq> carrier_vec n\<close> carrier_vecD index_smult_vec(1) lincomb_index smult_carrier_vec summands_valid)
            also have "... = (\<Sum>b \<in> B\<^sub>\<V>. (cs b \<cdot>\<^sub>v b)$i) + (\<Sum>b \<in> B\<^sub>k. (cs b \<cdot>\<^sub>v b)$i)"
              by (simp add: B\<^sub>\<V> B\<^sub>k B_def fin_dim_li_fin sum.union_disjoint *)
            finally have "(\<Sum>b \<in> B\<^sub>\<V>. (cs b \<cdot>\<^sub>v b)$i) = - (\<Sum>b \<in> B\<^sub>k. (cs b \<cdot>\<^sub>v b)$i)"
              by (simp add: eq_neg_iff_add_eq_0)
            hence "(lincomb cs B\<^sub>\<V>)$i = (\<Sum>b \<in> B\<^sub>k. - ((cs b) \<cdot>\<^sub>v b)$i)"
              by (smt (verit, best) "**" B\<^sub>\<V> R.add.finprod_cong' carrier_vecD index_smult_vec(1) lincomb_index smult_carrier_vec sum_negf summands_valid)
            moreover have "\<And>v. v \<in> carrier_vec n \<Longrightarrow> - (v$i) = (-v)$i"
              by (simp add: "**") 
            moreover have "\<And>b. (- (cs b) \<cdot>\<^sub>v b)$i = (( - cs b) \<cdot>\<^sub>v b)$i"
              by blast
            ultimately have "(lincomb cs B\<^sub>\<V>)$i = (\<Sum>b \<in> B\<^sub>k. ((- cs b) \<cdot>\<^sub>v b)$i)"
              by (smt (verit, del_insts) B\<^sub>k R.add.finprod_cong' local.vec_neg smult_carrier_vec smult_l_minus summands_valid)
            also have "... = (lincomb cs' B\<^sub>k)$i"
              by (smt (verit, best) "**" B\<^sub>k R.add.finprod_cong' carrier_vecD cs'_def index_smult_vec(1) lincomb_index smult_carrier_vec summands_valid)
            finally show "(lincomb cs B\<^sub>\<V>)$i = (lincomb cs' B\<^sub>k)$i" by blast
          qed
          hence 1: "(lincomb cs B\<^sub>\<V>) = (lincomb cs' B\<^sub>k)"  
            by (metis (no_types, lifting) B\<^sub>\<V> B\<^sub>k carrier_vecD eq_vecI lincomb_closed)
          have 2: "\<exists>b \<in> B\<^sub>\<V>. cs b \<noteq> 0"
          proof(rule ccontr)
            assume "\<not> (\<exists>b\<in>B\<^sub>\<V>. cs b \<noteq> 0)"
            hence *: "\<forall>b \<in> B\<^sub>\<V>. cs b = 0" by blast
            hence "\<forall>i < n. (lincomb cs B\<^sub>\<V>)$i = 0" by (simp add: B\<^sub>\<V> vec_space.lincomb_index)
            hence "lincomb cs B\<^sub>\<V> = 0\<^sub>v n" using B\<^sub>\<V> by auto
            moreover have "lin_indpt B\<^sub>k" using B\<^sub>k by blast
            ultimately have "\<forall>b \<in> B\<^sub>k. cs' b = 0"
              by (metis (no_types, lifting) "1" B\<^sub>k fin fin_dim lin_dep_def order.refl)
            hence "\<forall>b \<in> B\<^sub>k. cs b = 0" unfolding cs'_def by fastforce
            hence "\<forall>b \<in> B. cs b = 0" using * unfolding B_def by blast
            thus False using cs by blast
          qed
          have 3: "\<exists>b \<in> B\<^sub>k. cs' b \<noteq> 0"
          proof(rule ccontr)
            assume "\<not> (\<exists>b \<in> B\<^sub>k. cs' b \<noteq> 0)"
            hence *: "\<forall>b \<in> B\<^sub>k. cs' b = 0" by blast
            hence "\<forall>i < n. (lincomb cs' B\<^sub>k)$i = 0" by (simp add: B\<^sub>k vec_space.lincomb_index)
            hence "lincomb cs' B\<^sub>k = 0\<^sub>v n" using B\<^sub>k by auto
            moreover have "lin_indpt B\<^sub>\<V>" using B\<^sub>\<V> by blast
            ultimately have "\<forall>b \<in> B\<^sub>\<V>. cs b = 0"
              by (metis "1" B\<^sub>\<V> fin_dim li_le_dim(1) lin_dep_def subsetI)
            hence "\<forall>b \<in> B. cs b = 0" using * unfolding B_def cs'_def by fastforce
            thus False using cs by blast
          qed
          from 1 2 3 that show ?thesis by algebra
        qed
        define v where "v \<equiv> lincomb cs B\<^sub>\<V>"
        define w where "w \<equiv> lincomb cs' B\<^sub>k"
        have "\<And>i. i < n \<Longrightarrow> v$i = w$i" using eq v_def w_def by argo
        moreover have "\<And>i. i < n \<Longrightarrow> w$i = (\<Sum>b \<in> B\<^sub>k. (cs' b \<cdot>\<^sub>v b)$i)"
          by (smt (verit, best) B\<^sub>k carrier_vecD index_smult_vec(1) lincomb_index smult_carrier_vec sum.cong summands_valid w_def)
        moreover have "v \<in> \<V>" by (simp add: B\<^sub>\<V> in_spanI li_le_dim(1) v_def)
        moreover have "w \<in> ?k_kernel"
        proof-
          have "w \<in> carrier_vec n" by (metis B\<^sub>\<V> eq lincomb_closed w_def)
          moreover have "U\<^sup>H \<in> carrier_mat n n" by (simp add: A_decomp)
          moreover have "B\<^sub>k \<subseteq> carrier_vec n" by (simp add: B\<^sub>k)
          moreover have "finite B\<^sub>k" by (simp add: B\<^sub>k fin)
          ultimately have "U\<^sup>H *\<^sub>v w = finsum_vec TYPE(complex) n (\<lambda>b. cs' b \<cdot>\<^sub>v (U\<^sup>H *\<^sub>v b)) B\<^sub>k"
            using mat_vec_mult_sum[of w n "U\<^sup>H" B\<^sub>k] lincomb_def w_def by fastforce
          thus ?thesis using B\<^sub>k \<open>finite B\<^sub>k\<close> w_def by blast
        qed
        moreover have "v \<noteq> 0\<^sub>v n" by (metis B\<^sub>\<V> eq fin fin_dim lin_dep_crit order.refl v_def)
        ultimately show ?thesis using eq that v_def w_def by auto
      qed
      ultimately show ?thesis by blast
    qed
    moreover define v' where "v' \<equiv> vec_normalize v"
    ultimately have "v' \<in> carrier_vec n \<and> vec_norm v' = 1"
      using normalized_vec_norm vec_norm_def by force
    moreover then have v': "v' = (1 / vec_norm v) \<cdot>\<^sub>v v"
        by (metis div_by_1 one_smult_vec v'_def vec_normalize_def)
    moreover have "v' \<noteq> 0\<^sub>v n" by (metis calculation(1) field.one_not_zero vec_norm_zero)
    moreover have "v' \<in> \<V>"
    proof-
      have "v \<in> \<V>" using v by blast
      thus ?thesis using v' assms unfolding dimensional_def by auto
    qed
    moreover have "\<forall>j < k. (U\<^sup>H *\<^sub>v v')$j = 0"
    proof clarify
      fix j assume *: "j < k"
      have "(U\<^sup>H *\<^sub>v v')$j =  (U\<^sup>H *\<^sub>v ((1 / vec_norm v) \<cdot>\<^sub>v v))$j"
        using v' by blast
      also have "... = ((1 / vec_norm v) \<cdot>\<^sub>v (U\<^sup>H *\<^sub>v v))$j"
        by (metis A_decomp More_Matrix.carrier_vec_conjugate \<open>v' \<in> carrier_vec n \<and> vec_norm v' = 1\<close> mult_mat_vec smult_carrier_vec transpose_carrier_mat v')
      also have "... = (1 / vec_norm v) * ((U\<^sup>H *\<^sub>v v)$j)"
        using "*" A_decomp suc_k_leq_n by auto
      also have "... = (1 / vec_norm v) * 0" using "*" v by auto
      finally show "(U\<^sup>H *\<^sub>v v')$j = 0" by algebra
    qed
    ultimately show ?thesis using that by blast
  qed
  then obtain weights where weights: "(\<forall>i \<in> {k..<n}. weights i \<ge> 0)
      \<and> (\<Sum>i \<in> {k..<n}. weights i) = 1 \<and> \<rho> A v = (\<Sum>i \<in> {k..<n}. weights i * es!i)"
  proof-
    define weights where "weights \<equiv> \<lambda>i. (cmod ((U\<^sup>H *\<^sub>v v)$i))^2"
    hence 1: "(\<forall>i \<in> {k..<n}. weights i \<ge> 0)" by auto

    have "\<And>i. i \<in> {..<k} \<Longrightarrow> (U\<^sup>H *\<^sub>v v)$i = 0" using v by blast
    hence *: "\<And>i. i \<in> {..<k} \<Longrightarrow> weights i = 0" using weights_def by auto
    hence **: "\<And>i. i \<in> {..<k} \<Longrightarrow> weights i * es!i = 0" by (simp add: weights_def)

    have "(\<Sum>i \<in> {..<n}. weights i) = (\<Sum>i \<in> {..<k}. weights i) + (\<Sum>i \<in> {k..<n}. weights i)"
      by (smt (verit, ccfv_threshold) "*" atLeast0LessThan atLeastLessThan_iff le_eq_less_or_eq linorder_not_le sum.atLeastLessThan_concat sum.not_neutral_contains_not_neutral zero_order(1))
    also have "... = (\<Sum>i \<in> {k..<n}. weights i)"
      by (simp add: "*")
    finally have weights: "(\<Sum>i \<in> {..<n}. weights i) = (\<Sum>i \<in> {k..<n}. weights i)" .

    have "(\<Sum>i \<in> {..<n}. weights i * es!i) = (\<Sum>i \<in> {..<k}. weights i * es!i)
        + (\<Sum>i \<in> {k..<n}. weights i * es!i)"
      by (smt (verit, ccfv_threshold) "**" atLeast0LessThan atLeastLessThan_iff le_eq_less_or_eq linorder_not_le sum.atLeastLessThan_concat sum.not_neutral_contains_not_neutral zero_order(1))
    also have "... = (\<Sum>i \<in> {k..<n}. weights i * es!i)"
      by (simp add: **)
    finally have weights_es: "(\<Sum>i \<in> {..<n}. weights i * es!i) = (\<Sum>i \<in> {k..<n}. weights i * es!i)" .

    have "\<rho> A v = (\<Sum>i \<in> {..<n}. weights i * es!i)"
      using unit_vec_rayleigh_formula v weights_def by algebra
    hence 2: "\<rho> A v = (\<Sum>i \<in> {k..<n}. weights i * es!i)" using weights_es by argo

    have norm: "vec_norm (U\<^sup>H *\<^sub>v v) = vec_norm v"
      by (metis A_decomp More_Matrix.carrier_vec_conjugate adjoint_is_conjugate_transpose real_diag_decompD(1) transpose_carrier_mat unitary_adjoint unitary_diagD(3) unitary_vec_norm v(1))
    hence "vec_norm (U\<^sup>H *\<^sub>v v) = 1" using v(2) by argo
    moreover have "U\<^sup>H *\<^sub>v v \<in> carrier_vec n"
      by (metis A_decomp adjoint_dim_row adjoint_is_conjugate_transpose carrier_matD(2) carrier_vec_dim_vec dim_mult_mat_vec)
    ultimately have "(\<Sum>i \<in> {..<n}. weights i) = 1"
      unfolding weights_def by (metis complex_vec_norm_sum norm Re_complex_of_real csqrt_eq_1 one_complex.sel(1) v(2))
    hence 3: "(\<Sum>i \<in> {k..<n}. weights i) = 1" using weights by presburger

    show ?thesis
      by (metis 1 2 3 that[of weights] Im_complex_of_real Re_complex_of_real less_eq_complex_def of_real_hom.hom_one of_real_hom.hom_zero of_real_sum)
  qed
  have "length es = n"
    using A_decomp
    unfolding diag_mat_def
    by (metis A_decomp carrier_matD(1) diag_mat_length)
  hence "\<And>i. i \<in> {k..<n} \<Longrightarrow> es!i \<le> es!k"
    using eigvals_sorted
    by (metis atLeastLessThan_iff le_eq_less_or_eq sorted_wrt_iff_nth_less verit_eq_simplify(6))
  then have "\<And>i. i \<in> {k..<n} \<Longrightarrow> weights i * es!i \<le> weights i * es!k"
    by (meson weights atLeastLessThan_iff mult_left_mono)
  then have "(\<Sum>i \<in> {k..<n}. weights i * es!i) \<le> (\<Sum>i \<in> {k..<n}. weights i * es!k)"
    by (meson sum_mono)
  also have "... = (\<Sum>i \<in> {k..<n}. weights i) * es!k"
    by (metis ideal.scale_sum_left)
  also have "... = es!k" using weights by auto
  finally have "\<rho> A v \<le> es!k"
    using weights by presburger
  thus "\<exists>v. vec_norm v = 1 \<and> v \<in> \<V> \<and> v \<noteq> 0\<^sub>v n \<and> \<rho> A v \<le> es!k" using v by blast
qed

lemma courant_fischer_unit_rayleigh_helper3:
  assumes "n > 0"
  assumes "k < n"
  assumes "eigvals_of A es"
  defines "es_R \<equiv> map Re es"
  shows "\<exists>\<V>. dimensional \<V> (k + 1) \<and> (\<forall>v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V> \<and> vec_norm v = 1 \<longrightarrow> es_R ! k \<le> \<rho> A v)"
proof-
  let ?geq = "\<lambda>v. \<rho> A v \<ge> es_R!k"
  let ?P = "\<lambda>\<V> v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V> \<and> vec_norm v = 1"
  let ?Q = "\<lambda>\<V>. dimensional \<V> (k + 1)"

  have "inverts_mat U (adjoint U)"
    using A_decomp
    unfolding real_diag_decomp_def unitary_diag_def unitarily_equiv_def similar_mat_wit_def
    by (metis Complex_Matrix.unitary_def)
  hence U_invertible: "invertible_mat U" 
    by (metis A_decomp Complex_Matrix.unitary_def carrier_matD(1) carrier_matD(2) invertible_mat_def square_mat.simps unitaryD2)

  have "unitary U"
    using A_decomp
    unfolding real_diag_decomp_def unitary_diag_def unitarily_equiv_def
    by blast
  hence U_ortho: "corthogonal_mat U" using unitary_is_corthogonal A_decomp by auto

  have "set es \<subseteq> Reals" by (simp add: A_decomp)
  hence es_R: "map complex_of_real es_R = es"
  proof-
    { fix i assume *: "i < length es"
      hence "es!i \<in> Reals" using A_decomp by auto
      hence "complex_of_real (es_R!i) = es!i" by (simp add: * es_R_def)
    }
    thus ?thesis by (simp add: es_R_def map_nth_eq_conv)
  qed

  let ?\<V>_basis = "set (take (k + 1) (cols U))"
  define \<V> where "\<V> \<equiv> span ?\<V>_basis"
  have "lin_indpt ?\<V>_basis"
    using lin_indpt_subset_cols[of U "?\<V>_basis"] A_decomp U_invertible
    by (meson in_set_takeD subset_code(1))
  moreover have \<V>_basis_card: "card ?\<V>_basis = k + 1"
  proof-
    have "distinct (cols U)"
      by (metis A_decomp U_invertible invertible_det nat_less_le non_distinct_low_rank vec_space.det_rank_iff)
    hence "distinct (take (k + 1) (cols U))"
      using distinct_take by blast
    thus ?thesis
      by (metis A_decomp Suc_leI add.commute add_diff_cancel_right' append_take_drop_id assms(2) carrier_matD(2) cols_length diff_diff_cancel distinct_card length_append length_drop plus_1_eq_Suc)
  qed
  ultimately have 1: "?Q \<V>"
    unfolding dimensional_def
    by (metis A_decomp \<V>_def carrier_matD(1) cols_dim in_set_takeD subset_code(1))
  moreover have 2: "\<forall>v. ?P \<V> v \<longrightarrow> ?geq v"
  proof clarify
    fix v :: "complex vec"
    assume *: "v \<noteq> 0\<^sub>v n"
    assume **: "v \<in> \<V>"
    assume ***: "vec_norm v = 1"

    have "set (cols U) \<subseteq> carrier_vec n" using A_decomp cols_dim by blast
    hence \<V>_basis_dim: "?\<V>_basis \<subseteq> carrier_vec n" by (meson in_set_takeD subset_code(1))
    hence v_dim: "v \<in> carrier_vec n" using "**" \<V>_def span_closed by blast

    (* cols k+1 to n of U are orthogonal to v *)
    define x where "x \<equiv> U\<^sup>H *\<^sub>v v"
    have x_dim: "x \<in> carrier_vec n"
      by (metis A_decomp More_Matrix.carrier_vec_conjugate mult_mat_vec_carrier transpose_carrier_mat v_dim x_def)
    have x_norm: "vec_norm x = 1"
      by (metis "***" A_decomp More_Matrix.carrier_vec_conjugate adjoint_is_conjugate_transpose real_diag_decomp_def transpose_carrier_mat unitarily_equiv_def unitary_adjoint unitary_diag_def unitary_vec_norm v_dim x_def)
    have weights: "(\<Sum>j \<in> {..<n}. (cmod (x$j))^2) = 1"
      by (metis atLeast0LessThan carrier_vecD cpx_vec_length_square of_real_eq_1_iff power_one vec_norm_sq_cpx_vec_length_sq x_dim x_norm)

    have ineq: "\<And>j. j \<in> {..<n} \<Longrightarrow> es!k * (cmod (x$j))^2 \<le> es!j * (cmod (x$j))^2"
    proof- (* case on j \<le> k *)
      fix j
      assume *: "j \<in> {..<n}"
      show "es!k * (cmod (x$j))^2 \<le> es!j * (cmod (x$j))^2"
      proof(cases "j \<le> k")
        case True
        hence "es!k \<le> es!j"
          by (metis A_decomp antisym_conv1 assms(2) carrier_matD(1) diag_mat_length eigvals_sorted nless_le sorted_wrt_nth_less)
        thus ?thesis by (simp add: less_eq_complex_def mult_right_mono)
      next
        case False
        hence j_gr_k: "j > k" by simp
        have "inner_prod (col U j) v = 0"
        proof-
          have j: "j < dim_col U" using * A_decomp by blast
          have "\<forall>b \<in> ?\<V>_basis. \<exists>i. i < dim_col U \<and> b = col U i \<and> i \<noteq> j"
          proof
            fix b assume *: "b \<in> ?\<V>_basis"
            then obtain i where "b = (cols U)!i \<and> i \<le> k"
              by (metis A_decomp U_invertible \<V>_basis_card add.commute distinct_card distinct_take in_set_conv_nth invertible_det less_Suc_eq_le nat_less_le nth_take plus_1_eq_Suc vec_space.det_rank_iff vec_space.non_distinct_low_rank)
            moreover then have "i \<noteq> j" using j_gr_k by force
            ultimately show "\<exists>i<dim_col U. b = col U i \<and> i \<noteq> j"
              by (meson cols_nth j j_gr_k le_simps(1) order_le_less_trans)
          qed
          hence basis_ortho: "\<forall>b \<in> ?\<V>_basis. inner_prod (col U j) b = 0"
            using j_gr_k corthogonal_matD[OF U_ortho _ j] by fast

          obtain cs where "lincomb cs ?\<V>_basis = v"
            using "**" \<V>_def \<V>_basis_dim finite_in_span by blast
          hence "inner_prod (col U j) v = (\<Sum>b\<in>?\<V>_basis. cs b * inner_prod (col U j) b)"
            by (smt (verit, best) A_decomp List.finite_set R.add.finprod_cong' \<V>_basis_dim carrier_matD(1) col_dim finsum_vec inner_prod_vec_sum lincomb_def v_dim)
          thus ?thesis using basis_ortho by fastforce
        qed
        hence "conjugate (col U j) \<bullet> v = 0"
          by (metis A_decomp carrier_matD(1) col_dim conjugate_vec_sprod_comm v_dim)
        hence "row U\<^sup>H j \<bullet> v = 0"
          by (metis "*" adjoint_dim_row adjoint_is_conjugate_transpose adjoint_row carrier_vecD dim_mult_mat_vec lessThan_iff x_def x_dim)
        hence "x$j = 0"
          unfolding x_def
          by (metis "*" carrier_vecD dim_mult_mat_vec index_mult_mat_vec lessThan_iff x_def x_dim)
        thus ?thesis by fastforce
      qed
    qed

    have "es_R!k = es!k"
      by (metis A_decomp assms(2) carrier_matD(1) diag_mat_length es_R length_map nth_map)
    also have "... = es!k * (\<Sum>j \<in> {..<n}. (cmod (x$j))^2)"
      by (simp add: weights)
    also have "... = (\<Sum>j \<in> {..<n}. es!k * (cmod (x$j))^2)"
      by (simp add: mult_hom.hom_sum)
    also have "... \<le> (\<Sum>j \<in> {..<n}. es!j * (cmod (x$j))^2)"
      by (meson ineq sum_mono)
    also have "... = \<rho> A v"
      using unit_vec_rayleigh_formula A_decomp *** v_dim x_def by fastforce
    finally show "?geq v" by (simp add: less_eq_complex_def)
  qed
  ultimately show ?thesis by blast
qed

theorem courant_fischer_maximin:
  assumes "n > 0"
  assumes "k < n"
  shows "es!k = maximin (k + 1)"
        "maximin_defined (k + 1)"
proof-
  have "inverts_mat U (adjoint U)"
    using A_decomp
    unfolding real_diag_decomp_def unitary_diag_def unitarily_equiv_def similar_mat_wit_def
    by (metis Complex_Matrix.unitary_def)
  hence U_invertible: "invertible_mat U" 
    by (metis A_decomp Complex_Matrix.unitary_def carrier_matD(1) carrier_matD(2) invertible_mat_def square_mat.simps unitaryD2)

  have "unitary U"
    using A_decomp
    unfolding real_diag_decomp_def unitary_diag_def unitarily_equiv_def
    by blast
  hence U_ortho: "corthogonal_mat U" using unitary_is_corthogonal A_decomp by auto

  define es_R where "es_R \<equiv> map Re es"
  have "set es \<subseteq> Reals" by (simp add: A_decomp)
  hence es_R: "map complex_of_real es_R = es"
  proof-
    { fix i assume *: "i < length es"
      hence "es!i \<in> Reals" using A_decomp by auto
      hence "complex_of_real (es_R!i) = es!i" by (simp add: * es_R_def)
    }
    thus ?thesis by (simp add: es_R_def map_nth_eq_conv)
  qed
  hence es_R_i: "\<And>i. i \<in> {..<n} \<Longrightarrow> es_R!i = Re (es!i)"
    using dim_is eigvals eigvals_poly_length es_R_def by simp
  hence es_R_k: "es_R!k = Re (es!k)" by (simp add: assms(2))

  let ?leq = "\<lambda>v. \<rho> A v \<le> es_R!k"
  let ?geq = "\<lambda>v. \<rho> A v \<ge> es_R!k"
  let ?P = "\<lambda>\<V> v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V> \<and> vec_norm v = 1"
  let ?Q = "\<lambda>\<V>. dimensional \<V> (k + 1)"
  let ?S\<^sub>\<rho> = "\<lambda>\<V>. {\<rho> A v |v. ?P \<V> v}"

  have 1: "\<And>\<V>. ?Q \<V> \<Longrightarrow> (\<exists>v. ?P \<V> v \<and> ?leq v)"
    by (metis Re_complex_of_real courant_fischer.courant_fischer_unit_rayleigh_helper2 courant_fischer_axioms es_R_k less_eq_complex_def)

  have 2: "\<exists>\<V>. ?Q \<V> \<and> (\<forall>v. ?P \<V> v \<longrightarrow> ?geq v)"
    using courant_fischer_unit_rayleigh_helper3[OF assms(1) assms(2) eigvals]
    unfolding es_R_def
    by blast

  from 2 obtain \<V>' where \<V>': "?Q \<V>' \<and> (\<forall>v. ?P \<V>' v \<longrightarrow> ?geq v)" by blast
  from this 1 obtain v' where v': "?P \<V>' v' \<and> ?leq v'" by presburger
  moreover have all_v_geq: "\<forall>v. ?P \<V>' v \<longrightarrow> ?geq v" using \<V>' by blast
  ultimately have "\<rho> A v' = es_R!k" by fastforce
  hence "es_R!k \<in> ?S\<^sub>\<rho> \<V>'" using v' by fastforce
  moreover have "\<forall>x \<in> ?S\<^sub>\<rho> \<V>'. x \<ge> es_R!k" using all_v_geq by blast
  ultimately have "es_R!k = Inf (?S\<^sub>\<rho> \<V>')" by (smt (verit) rayleigh_bdd_below cInf_eq_minimum)
  moreover have "\<And>\<V>. ?Q \<V> \<Longrightarrow> Inf (?S\<^sub>\<rho> \<V>) \<le> es_R!k"
  proof-
    fix \<V>
    assume *: "?Q \<V>"
    then obtain v where v: "?P \<V> v \<and> ?leq v" using 1 by presburger
    then have "\<rho> A v \<in> ?S\<^sub>\<rho> \<V>" by blast
    then have "Inf (?S\<^sub>\<rho> \<V>) \<le> \<rho> A v"
      using rayleigh_min_exists[OF *] assms(2) rayleigh_min courant_fischer_axioms by auto
    thus "Inf (?S\<^sub>\<rho> \<V>) \<le> es_R!k" using v by linarith
  qed
  ultimately have *: "es_R!k \<in> {Inf (?S\<^sub>\<rho> \<V>) | \<V>. ?Q \<V>} \<and> (\<forall>x \<in> {Inf (?S\<^sub>\<rho> \<V>) | \<V>. ?Q \<V>}. x \<le> es_R!k)"
    using \<V>' by blast
  hence "Sup {Inf (?S\<^sub>\<rho> \<V>) | \<V>. ?Q \<V>} = es_R!k" by (meson cSup_eq_maximum)
  moreover have "Sup {Inf (?S\<^sub>\<rho> \<V>) | \<V>. ?Q \<V>} = maximin (k + 1)"
    unfolding maximin_def rayleigh_min dimensional_def by blast
  ultimately show "es!k = maximin (k + 1)"
    by (metis A_decomp assms(2) carrier_matD(1) diag_mat_length es_R length_map nth_map)
  show "maximin_defined (k + 1)"
    using * unfolding maximin_defined_def sup_defined_def rayleigh_min bdd_above_def by blast
qed

end

lemma courant_fischer_maximin:
  fixes A :: "complex mat"
  assumes "n > 0"
  assumes "k < n"
  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "eigvals_of A es"
  assumes "sorted_wrt (\<ge>) es"
  shows "es!k = hermitian_mat.maximin n A (k + 1)" "hermitian_mat.maximin_defined n A (k + 1)"
proof-
  obtain \<Lambda> U where "real_diag_decomp A \<Lambda> U
      \<and> diag_mat \<Lambda> = es
      \<and> set es \<subseteq> Reals
      \<and> U \<in> carrier_mat n n
      \<and> \<Lambda> \<in> carrier_mat n n"
    by (metis hermitian_real_diag_decomp_eigvals assms(3-5))
  then interpret cf: courant_fischer A n \<Lambda> U es
    using assms by unfold_locales
  show "es!k = hermitian_mat.maximin n A (k + 1)"
    using cf.courant_fischer_maximin(1)[OF assms(1) assms(2)] .
  show "hermitian_mat.maximin_defined n A (k + 1)"
    using cf.courant_fischer_maximin(2)[OF assms(1) assms(2)] .
qed

lemma maximin_minimax:
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "k < n"
  shows "hermitian_mat.maximin n (-A) (n - k) = - hermitian_mat.minimax n A (k + 1)"
        "hermitian_mat.maximin_defined n (-A) (n - k) \<Longrightarrow> hermitian_mat.minimax_defined n A (k + 1)"
proof-
  interpret hm: hermitian_mat n A using assms by unfold_locales
  interpret hm': hermitian_mat n "-A"
    using assms by (simp add: hermitian_mat.intro negative_hermitian)

  define P where "P \<equiv> \<lambda>v \<V>. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V> \<and> vec_norm v = 1"
  define Q where "Q \<equiv> \<lambda>\<V>. hm'.dimensional \<V> (n - k)"

  have "Inf {Sup {\<rho> A v |v. P v \<V>} |\<V>. Q \<V>} = - Sup (uminus`{Sup {\<rho> A v |v. P v \<V>} |\<V>. Q \<V>})"
    using Inf_real_def .
  moreover have *: "uminus`{Sup {\<rho> A v |v. P v \<V>} |\<V>. Q \<V>} = {- Sup {\<rho> A v |v. P v \<V>} |\<V>. Q \<V>}"
    by blast
  moreover have **: "{- Sup {\<rho> A v |v. P v \<V>} |\<V>. Q \<V>} = {Inf {\<rho> (-A) v |v. P v \<V>} |\<V>. Q \<V>}"
  proof-
    have "\<And>\<V>. Q \<V> \<Longrightarrow> - Sup {\<rho> A v |v. P v \<V>} = Inf {\<rho> (-A) v |v. P v \<V>}"
    proof-
      fix \<V> assume *: "Q \<V>"
      have "Inf {\<rho> (-A) v |v. P v \<V>} = - Sup (uminus`{\<rho> (-A) v |v. P v \<V>})"
        using Inf_real_def by fast
      moreover have "uminus`{\<rho> (-A) v |v. P v \<V>} = {- \<rho> (-A) v |v. P v \<V>}" by blast
      moreover have "{- \<rho> (-A) v |v. P v \<V>} = {\<rho> A v |v. P v \<V>}"
      proof-
        have "\<And>v. P v \<V> \<Longrightarrow> - \<rho> (- A) v = \<rho> A v"
          by (metis * P_def Q_def assms(1) hm.dimensional_n_vec rayleigh_quotient_negative)
        thus ?thesis by metis
      qed
      ultimately show "- Sup {\<rho> A v |v. P v \<V>} = Inf {\<rho> (-A) v |v. P v \<V>}" by presburger
    qed
    thus ?thesis by force
  qed
  ultimately have "- Inf {Sup {\<rho> A v |v. P v \<V>} |\<V>. Q \<V>} = Sup {Inf {\<rho> (-A) v |v. P v \<V>} |\<V>. Q \<V>}"
    by auto
  moreover have "n - (k + 1) + 1 = n - k" using assms(3) by fastforce
  ultimately show "hermitian_mat.maximin n (-A) (n - k) = - hermitian_mat.minimax n A (k + 1)"
    by (simp add: hm.minimax_def hm'.maximin_def hm'.rayleigh_min hm.rayleigh_max P_def Q_def)

  show "hermitian_mat.minimax_defined n A (k + 1)" if "hermitian_mat.maximin_defined n (-A) (n - k)"
  proof-
    have "{Sup {\<rho> A v |v. P v \<V>} |\<V>. Q \<V>} \<noteq> {}"
      using that
      unfolding hm'.maximin_defined_def sup_defined_def hm'.rayleigh_min P_def Q_def
      by fast
    moreover have "bdd_below {Sup {\<rho> A v |v. P v \<V>} |\<V>. Q \<V>}"
    proof-
      have "bdd_above {Inf {\<rho> (-A) v |v. P v \<V>} |\<V>. Q \<V>}"
        using that
        unfolding hm'.maximin_defined_def sup_defined_def hm'.rayleigh_min P_def Q_def
        by argo
      hence "bdd_above {- Sup {\<rho> A v |v. P v \<V>} |\<V>. Q \<V>}" using ** by argo
      hence "bdd_below {Sup {\<rho> A v |v. P v \<V>} |\<V>. Q \<V>}" by (smt (verit, best) * bdd_above_uminus)
      thus ?thesis by blast
    qed
    moreover have "n - k = n - (k + 1) + 1" using assms(3) by simp
    ultimately show ?thesis
      unfolding hm.minimax_defined_def inf_defined_def hm.rayleigh_max P_def Q_def by algebra
  qed
qed

lemma courant_fischer_minimax:
  fixes A :: "complex mat"
  assumes "n > 0"
  assumes "k < n"
  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "eigvals_of A es"
  assumes "sorted_wrt (\<ge>) es"
  shows "es!k = hermitian_mat.minimax n A (k + 1)"
        "hermitian_mat.minimax_defined n A (k + 1)"
proof-
  define A' where "A' \<equiv> - A"
  define es' where "es' = rev (map (\<lambda>x. -x) es)"
  have A'_hermitian: "hermitian A'" using negative_hermitian A'_def assms by blast
  moreover have "eigvals_of A' es'"
    using neg_mat_eigvals A'_def assms(3) assms(5) es'_def by blast
  moreover have A'_dim: "A' \<in> carrier_mat n n" by (simp add: A'_def assms(3))
  moreover have "sorted_wrt (\<ge>) es'"
  proof-
    let ?l = "(map (\<lambda>x. -x) es)"
    { fix i j assume "i < j" "j < length ?l"
      moreover then have "es!i \<ge> es!j" using assms(6) sorted_wrt_iff_nth_less[of "(\<ge>)" es] by force
      ultimately have "?l!i \<le> ?l!j" by simp
    }
    hence "sorted_wrt (\<le>) ?l" by (metis sorted_wrt_iff_nth_less)
    thus ?thesis by (simp add: sorted_wrt_rev es'_def)
  qed
  ultimately have *: "es'!(n - k - 1) = hermitian_mat.maximin n A' (n - k)
      \<and> hermitian_mat.maximin_defined n A' (n - k)"
    using courant_fischer_maximin[of n "n - k - 1" A' es'] assms by (simp add: Suc_diff_Suc)
  moreover have "es!k = - es'!(n - k - 1)"
  proof-
    have "n - k - 1 < length es" using assms(2) assms(3) assms(5) eigvals_poly_length by force
    moreover have "length es = n"
      using assms(3) assms(5) by auto
    ultimately have "es!k = (rev es)!(n - k - 1)"
      using rev_nth[of "n - k - 1" es] by (simp add: Suc_diff_Suc assms(2) le_simps(1))
    also have "... = rev (map (\<lambda>x. -x) (map (\<lambda>x. -x) es))!(n - k - 1)"
      by simp
    also have "... = - es'!(n - k - 1)"
      by (metis \<open>n - k - 1 < length es\<close> es'_def length_map length_rev nth_map rev_map)
    finally show ?thesis .
  qed
  ultimately show "es!k = hermitian_mat.minimax n A (k + 1)"
      "hermitian_mat.minimax_defined n A (k + 1)"
     apply (simp add: A'_def assms(2) assms(3) assms(4) maximin_minimax(1))
    using A'_def * assms(2) assms(3) assms(4) maximin_minimax(2) by blast
qed

subsection "Theorem Statement"

theorem courant_fischer:
  fixes A :: "complex mat"
  assumes "n > 0"
  assumes "k < n"
  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "eigvals_of A es"
  assumes "sorted_wrt (\<ge>) es"
  shows "es!k = hermitian_mat.minimax n A (k + 1)"
        "es!k = hermitian_mat.maximin n A (k + 1)"
        "hermitian_mat.minimax_defined n A (k + 1)"
        "hermitian_mat.maximin_defined n A (k + 1)"
     using assms courant_fischer_minimax apply algebra
    using assms courant_fischer_maximin apply algebra
   using assms courant_fischer_minimax apply algebra
  using assms courant_fischer_maximin by algebra

section "Cauchy Eigenvalue Interlacing Theorem"

text
  "We follow the proof given in this set of lecture notes by Dr. David Bindel:
  https://www.cs.cornell.edu/courses/cs6210/2019fa/lec/2019-11-04.pdf"

subsection "Theorem Statement and Proof"

theorem cauchy_eigval_interlacing:
  fixes A W :: "complex mat"
  assumes "n > 0"
  assumes "j < n"
  assumes "m \<le> n"
  assumes "m > 0"
  assumes "j < m"

  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "eigvals_of A \<alpha>"
  assumes "sorted_wrt (\<ge>) \<alpha>"

  assumes "W \<in> carrier_mat n m"
  assumes "W\<^sup>H * W = 1\<^sub>m m"
  assumes "inj_on (\<lambda>v. W *\<^sub>v v) (carrier_vec m)"

  defines "B \<equiv> W\<^sup>H * A * W"
  assumes "eigvals_of B \<beta>"
  assumes "sorted_wrt (\<ge>) \<beta>"
  shows "\<alpha>!(n-m+j) \<le> \<beta>!j" "\<beta>!j \<le> \<alpha>!j"
proof-
  interpret A: hermitian_mat n A using assms hermitian_mat_def by presburger
  interpret B: hermitian_mat m B
  proof unfold_locales
    show "B \<in> carrier_mat m m" unfolding B_def using assms by fastforce
    show "hermitian B"
    proof-
      have "B\<^sup>H = (W\<^sup>H * A * W)\<^sup>H" unfolding B_def by blast
      also have "... =  W\<^sup>H * A * (W\<^sup>H)\<^sup>H"
        by (smt (verit, ccfv_threshold) assms adjoint_dim' adjoint_is_conjugate_transpose adjoint_mult assoc_mult_mat hermitian_def mult_carrier_mat)
      also have "... = W\<^sup>H * A * W" by (simp add: transpose_conjugate)
      also have "... = B" unfolding B_def by blast
      finally show ?thesis by (simp add: adjoint_is_conjugate_transpose hermitian_def)
    qed
  qed

  have \<alpha>: "\<forall>k < n. \<alpha>!k = hermitian_mat.minimax n A (k + 1)
      \<and> \<alpha>!k = hermitian_mat.maximin n A (k + 1)
      \<and> hermitian_mat.minimax_defined n A (k + 1)
      \<and> hermitian_mat.maximin_defined n A (k + 1)"
    using courant_fischer assms by presburger

  let ?lhs = "\<lambda>\<V>. {\<rho> B v |v. v \<noteq> 0\<^sub>v m \<and> v \<in> \<V> \<and> vec_norm v = 1}"
  let ?rhs = "\<lambda>\<V>. {\<rho> A v |v. v \<noteq> 0\<^sub>v n \<and> v \<in> (*\<^sub>v) W ` \<V> \<and> vec_norm v = 1}"
  have rayleigh_sets_eq: "\<And>\<V> k. B.dimensional \<V> k \<Longrightarrow> ?lhs \<V> = ?rhs \<V>"
  proof-
    fix \<V> k assume *: "B.dimensional \<V> k"
    have "?lhs \<V> \<subseteq> ?rhs \<V>"
    proof
      let ?lhs = "?lhs \<V>"
      let ?rhs = "?rhs \<V>"
      fix x assume **: "x \<in> ?lhs"
      then obtain v where v: "v \<noteq> 0\<^sub>v m \<and> v \<in> \<V> \<and> vec_norm v = 1 \<and> x = \<rho> B v" by blast
      let ?c = "1 / (vec_norm (W *\<^sub>v v))"
      define v' where "v' \<equiv> ?c \<cdot>\<^sub>v (W *\<^sub>v v)"
      have "\<rho>\<^sub>c B v = ((B *\<^sub>v v) \<bullet>c v) / (v \<bullet>c v)" by simp
      also have "... = ((W\<^sup>H *\<^sub>v (A * W *\<^sub>v v)) \<bullet>c v) / (v \<bullet>c v)"
        unfolding assms(9)
        by (smt (verit, best) assms "*" A.dim_is B.dimensional_n_vec More_Matrix.carrier_vec_conjugate assoc_mult_mat assoc_mult_mat_vec carrier_vecD dim_mult_mat_vec hermitian_def index_mult_mat(2) mult_carrier_mat transpose_carrier_mat v)
      also have "... = ((A * W *\<^sub>v v) \<bullet>c (W *\<^sub>v v)) / (v \<bullet>c v)"
        by (metis (no_types, lifting) assms(6,10) "*" A.dim_is B.hermitian_mat_axioms cscalar_prod_conjugate_transpose hermitian_mat.dimensional_n_vec mult_carrier_mat mult_mat_vec_carrier v)
      also have "... = ((A * W *\<^sub>v v) \<bullet>c (W *\<^sub>v v)) / (v \<bullet>c ((1\<^sub>m m) *\<^sub>v v))"
        using "*" v B.dimensional_n_vec by force
      also have "... = ((A *\<^sub>v (W *\<^sub>v v)) \<bullet>c (W *\<^sub>v v)) / (v \<bullet>c (W\<^sup>H *\<^sub>v (W *\<^sub>v v)))"
        by (metis "*" assms(6,10,11) B.dimensional_n_vec adjoint_dim' adjoint_is_conjugate_transpose assoc_mult_mat_vec v)
      also have "... = ((A *\<^sub>v (W *\<^sub>v v)) \<bullet>c (W *\<^sub>v v)) / ((W *\<^sub>v v) \<bullet>c ((W *\<^sub>v v)))"
        by (metis "*" assms(10) B.dimensional_n_vec adjoint_def_alter adjoint_is_conjugate_transpose mult_mat_vec_carrier v)
      also have "... = \<rho>\<^sub>c A (W *\<^sub>v v)" by simp
      finally have "\<rho> B v = \<rho> A (W *\<^sub>v v)" by fastforce
      also have "... = \<rho> A v'"
        unfolding v'_def
        by (smt (verit, best) assms(6,10,11) "*" rayleigh_quotient_scale B.hermitian_mat_axioms adjoint_is_conjugate_transpose div_by_1 hermitian_mat.dimensional_n_vec inner_prod_mult_mat_vec_right mult_mat_vec_carrier of_real_hom.hom_one one_mult_mat_vec v vec_norm_def)
      finally have "x = \<rho> A v'" using v by fast
      moreover have "vec_norm v' = 1"
        by (smt (verit, ccfv_threshold) assms(10,11) "*" B.dimensional_n_vec adjoint_dim' adjoint_is_conjugate_transpose assoc_mult_mat_vec carrier_matD(1) cscalar_prod_adjoint dim_mult_mat_vec div_by_1 one_mult_mat_vec scalar_vec_one v v'_def vec_norm_def)
      moreover have "v' \<in> (*\<^sub>v) W ` \<V>"
        by (smt (z3) assms(10,11) "*" B.dimensional_n_vec Setcompr_eq_image adjoint_is_conjugate_transpose div_by_1 inner_prod_mult_mat_vec_left mem_Collect_eq one_mult_mat_vec one_smult_vec v v'_def vec_norm_def)
      moreover have "v' \<noteq> 0\<^sub>v n"
        by (metis A.add.one_closed calculation(2) one_neq_zero vec_norm_zero)
      ultimately show "x \<in> ?rhs" by blast
    qed
    moreover have "?rhs \<V> \<subseteq> ?lhs \<V>"
    proof
      let ?lhs = "?lhs \<V>"
      let ?rhs = "?rhs \<V>"
      fix x assume **: "x \<in> ?rhs"
      then obtain v' where v': "v' \<noteq> 0\<^sub>v n \<and> v' \<in> (*\<^sub>v) W ` \<V> \<and> vec_norm v' = 1 \<and> x = \<rho> A v'" by blast
      then obtain u where u: "W *\<^sub>v u = v' \<and> u \<noteq> 0\<^sub>v m \<and> u \<in> \<V>"
        by (smt (verit, ccfv_threshold) assms(6,10,11) B.dimensional_n B.smult_l_null Setcompr_eq_image * adjoint_is_conjugate_transpose assms(15) assms(7) csqrt_1 inner_prod_mult_mat_vec_left inner_prod_smult_left_right mem_Collect_eq mult_eq_0_iff one_mult_mat_vec one_neq_zero power2_csqrt subset_eq vec_norm_def)
      hence u_m: "u \<in> carrier_vec m" using "*" B.dimensional_n_vec by blast
      let ?c = "1 / vec_norm u"
      define v where "v \<equiv> ?c \<cdot>\<^sub>v u"
      have "\<rho>\<^sub>c B v = ((B *\<^sub>v v) \<bullet>c v) / (v \<bullet>c v)" by simp
      also have "... = ((W\<^sup>H *\<^sub>v (A * W *\<^sub>v v)) \<bullet>c v) / (v \<bullet>c v)"
        unfolding assms(9)
        by (smt (verit, ccfv_threshold) assms(6,10,11,13) u_m A.dim_is B.smult_one adjoint_is_conjugate_transpose adjoint_mult assms(15) assms(4) assms(7) cscalar_prod_conjugate_transpose divide_self_if hermitian_def inner_prod_mult_mat_vec_right mult_carrier_mat mult_mat_vec_carrier one_mult_mat_vec u v' v_def vec_norm_def)
      also have "... = ((A * W *\<^sub>v v) \<bullet>c (W *\<^sub>v v)) / (v \<bullet>c v)"
        by (smt (verit, ccfv_threshold) assms(6,10,11) "*" A.dim_is B.dimensional_n_vec Complex_Matrix.adjoint_adjoint adjoint_dim' adjoint_is_conjugate_transpose assms(7) carrier_matD(1) carrier_vecD cscalar_prod_adjoint dim_mult_mat_vec index_mult_mat(2) index_smult_vec(2) u v_def)
      also have "... = ((A * W *\<^sub>v v) \<bullet>c (W *\<^sub>v v)) / (v \<bullet>c ((1\<^sub>m m) *\<^sub>v v))"
        by (simp add: u_m v_def)
      also have "... = ((A *\<^sub>v (W *\<^sub>v v)) \<bullet>c (W *\<^sub>v v)) / (v \<bullet>c (W\<^sup>H *\<^sub>v (W *\<^sub>v v)))"
        by (metis assms(6,10,11) B.smult_one adjoint_dim' adjoint_is_conjugate_transpose assoc_mult_mat_vec div_by_1 inner_prod_mult_mat_vec_left one_mult_mat_vec u u_m v' v_def vec_norm_def)
      also have "... = ((A *\<^sub>v (W *\<^sub>v v)) \<bullet>c (W *\<^sub>v v)) / ((W *\<^sub>v v) \<bullet>c ((W *\<^sub>v v)))" 
        by (metis assms(10) B.smult_closed u_m v_def adjoint_def_alter adjoint_is_conjugate_transpose mult_mat_vec_carrier)
      also have "... = \<rho>\<^sub>c A (W *\<^sub>v v)" by simp
      finally have "\<rho> B v = \<rho> A (W *\<^sub>v v)" by fastforce
      also have "... = \<rho> A (W *\<^sub>v (?c \<cdot>\<^sub>v u))" using v_def by blast
      also have "... = \<rho> A (?c \<cdot>\<^sub>v (W *\<^sub>v u))" by (metis assms(10) mult_mat_vec u u_m)
      also have "... = \<rho> A v'"
        by (metis assms(10,11) u_m adjoint_is_conjugate_transpose div_by_1 inner_prod_mult_mat_vec_left one_mult_mat_vec one_smult_vec u v' vec_norm_def)
      finally have "x = \<rho> B v" using v' by presburger
      moreover have "vec_norm v = 1"
        by (metis carrier_dim_vec csqrt_1 normalized_vec_norm u u_m v_def vec_norm_def vec_normalize_def)
      moreover then have "v \<noteq> 0\<^sub>v m" using vec_norm_zero by force
      moreover have "v \<in> \<V>"
        by (metis assms(10,11) B.smult_one adjoint_is_conjugate_transpose div_by_1 inner_prod_mult_mat_vec_right one_mult_mat_vec u u_m v' v_def vec_norm_def)
      ultimately show "x \<in> ?lhs" by blast
    qed
    ultimately show "?lhs \<V> = ?rhs \<V>" by blast
  qed

  let ?lhs_min = "\<lambda>k. {A.rayleigh_min ((\<lambda>v. W *\<^sub>v v)`\<V>) | \<V>. B.dimensional \<V> k}"
  let ?rhs_min = "\<lambda>k. {A.rayleigh_min \<V> | \<V>. A.dimensional \<V> k}"
  let ?lhs_max = "\<lambda>k. {A.rayleigh_max ((\<lambda>v. W *\<^sub>v v)`\<V>) | \<V>. B.dimensional \<V> k}"
  let ?rhs_max = "\<lambda>k. {A.rayleigh_max \<V> | \<V>. A.dimensional \<V> k}"
  have rayleigh_sets_eq': "\<And>k. ?lhs_min k \<subseteq> ?rhs_min k" "\<And>k. ?lhs_max k \<subseteq> ?rhs_max k"
  proof-
    fix k
    have *: "{(\<lambda>v. W *\<^sub>v v)`\<V> | \<V>. B.dimensional \<V> k} \<subseteq> {\<V> | \<V>. A.dimensional \<V> k}"
    proof(rule subsetI)
      fix \<V> assume *: "\<V> \<in> {(\<lambda>v. W *\<^sub>v v)`\<V> | \<V>. B.dimensional \<V> k}"
      have "A.dimensional \<V> k"
      proof-
        let ?f = "\<lambda>v. W *\<^sub>v v"
        obtain \<V>' where \<V>': "\<V> = ?f`\<V>' \<and> B.dimensional \<V>' k" using * by blast
        then obtain vs' where vs': "\<V>' = B.span vs'
            \<and> card vs' = k
            \<and> vs' \<subseteq> carrier_vec m
            \<and> B.lin_indpt vs'"
          unfolding B.dimensional_def by presburger
        define vs where "vs = ?f`vs'"

        interpret W: linear_map
            class_ring
            "(module_vec TYPE(complex) m)"
            "(module_vec TYPE(complex) n)"
            "(\<lambda>v. W *\<^sub>v v)"
          using linear_map_mat[OF assms(10)] .    
        
        have inj: "inj_on ?f (carrier B.V)" using assms(12) by fastforce
        have 1: "vs' \<subseteq> carrier B.V" using B.cV vs' by argo
        have "\<V> = A.span vs" using W.image_span by (simp add: B.li_le_dim(1) \<V>' vs' vs_def)
        moreover have "card vs = k"
        proof-
          have "card vs' = k" using vs' by blast
          moreover have "vs' \<subseteq> carrier B.V" by (simp add: vs')
          ultimately show ?thesis by (metis inj card_image subset_inj_on vs_def)
        qed
        moreover have "vs \<subseteq> carrier_vec n"
        proof(rule subsetI)
          fix v assume "v \<in> vs"
          then obtain v' where "v' \<in> vs' \<and> ?f v' = v" using vs_def by blast
          thus "v \<in> carrier_vec n" using assms(10) mult_mat_vec_carrier vs' by blast
        qed
        moreover have "A.lin_indpt vs"
          using W.inj_image_lin_indpt[OF inj] vs' vs_def B.fin_dim_li_fin by auto
        ultimately show ?thesis unfolding A.dimensional_def by blast
      qed
      thus "\<V> \<in> {\<V> | \<V>. A.dimensional \<V> k}" by blast
    qed
    
    from * show "?lhs_min k \<subseteq> ?rhs_min k" by blast
    from * show "?lhs_max k \<subseteq> ?rhs_max k" by blast
  qed

  have "\<beta>!j = B.maximin (j + 1)"
    using courant_fischer(2)[OF assms(4,5) B.dim_is B.is_herm assms(14,15)] .
  also have "... = Sup {A.rayleigh_min ((\<lambda>v. W *\<^sub>v v)`\<V>) | \<V>. B.dimensional \<V> (j + 1)}"
    unfolding B.maximin_def B.rayleigh_min A.rayleigh_min
    by (metis (no_types, lifting) rayleigh_sets_eq)
  also have "... \<le> \<alpha>!j"
  proof-
    let ?lhs = "{A.rayleigh_min ((\<lambda>v. W *\<^sub>v v)`\<V>) | \<V>. B.dimensional \<V> (j + 1)}"
    let ?rhs = "{A.rayleigh_min \<V> | \<V>. A.dimensional \<V> (j + 1)}"
    have \<alpha>\<^sub>j: "\<alpha>!j = A.maximin (j + 1)"
      using courant_fischer(2)[OF assms(1,2,6,7,8,9)] by argo
    hence Re_\<alpha>\<^sub>j: "Re (\<alpha>!j) = Sup ?rhs"
      by (simp add: A.maximin_def image_Collect)

    hence "?lhs \<subseteq> ?rhs" using rayleigh_sets_eq'(1) by presburger
    moreover have "?lhs \<noteq> {}"
    proof-
      let ?vs = "set (take (j + 1) (unit_vecs m))"
      have "B.dimensional (B.span ?vs) (j + 1)"
      proof-
        have "card ?vs = j + 1"
          by (metis B.unit_vecs_distinct distinct_take B.unit_vecs_length Groups.add_ac(2) One_nat_def Suc_leI add_0_right add_Suc_right assms(5) diff_zero distinct_card length_take length_upt take_upt)
        moreover have "B.lin_indpt ?vs"
          by (meson B.basis_def B.supset_ld_is_ld B.unit_vecs_basis set_take_subset)
        moreover have "?vs \<subseteq> carrier_vec m"
          by (meson in_set_takeD subset_code(1) unit_vecs_carrier)
        ultimately show ?thesis unfolding B.dimensional_def by blast
      qed
      thus ?thesis by blast
    qed
    moreover have "bdd_above ?rhs"
      using \<alpha>
      by (simp add: A.maximin_defined_def assms(2) sup_defined_def)
    ultimately have "Sup ?lhs \<le> Sup ?rhs" by (meson cSup_subset_mono)
    thus ?thesis using Re_\<alpha>\<^sub>j \<alpha>\<^sub>j less_eq_complex_def by force
  qed
  finally show "\<beta>!j \<le> \<alpha>!j" .

  let ?j' = "n - m + j"
  have j'_le: "?j' < n" using assms by linarith
  hence j'_eq: "n - ?j' + 1 = m - j + 1" using assms(3) by force

  have "\<alpha>!?j' = A.minimax (?j' + 1)" using courant_fischer(1)[OF assms(1) j'_le assms(6,7,8,9)] .
  also have "... \<le> Inf {A.rayleigh_max ((\<lambda>v. W *\<^sub>v v)`\<V>) | \<V>. B.dimensional \<V> (n - ?j')}"
  proof-
    let ?rhs = "{A.rayleigh_max ((\<lambda>v. W *\<^sub>v v)`\<V>) | \<V>. B.dimensional \<V> (n - ?j')}"
    let ?lhs = "{A.rayleigh_max \<V> | \<V>. A.dimensional \<V> (n - ?j')}"

    have "?rhs \<subseteq> ?lhs" using rayleigh_sets_eq'(2) by presburger
    moreover have "?rhs \<noteq> {}"
    proof-
      let ?vs = "set (take (n - ?j') (unit_vecs m))"
      have "B.dimensional (B.span ?vs) (n - ?j')"
      proof-
        have "card ?vs = n - ?j'"
          by (metis B.unit_vecs_distinct distinct_take B.unit_vecs_length Groups.add_ac(2) One_nat_def add_Suc_right diff_zero distinct_card length_take length_upt take_upt diff_add_inverse2 diff_le_self j'_eq)
        moreover have "B.lin_indpt ?vs"
          by (meson B.basis_def B.supset_ld_is_ld B.unit_vecs_basis set_take_subset)
        moreover have "?vs \<subseteq> carrier_vec m"
          by (meson in_set_takeD subset_code(1) unit_vecs_carrier)
        ultimately show ?thesis unfolding B.dimensional_def by blast
      qed
      thus ?thesis by blast
    qed
    moreover have "bdd_below ?lhs"
    proof-
      have "n - m + j < n" using j'_le by blast
      moreover then have "n - ((n - m + j) + 1) + 1 = n - (n - m + j)" by linarith
      ultimately show ?thesis
        using \<alpha>
        unfolding A.minimax_defined_def inf_defined_def
        by (smt (verit, del_insts) Collect_cong)
    qed
    ultimately have "Inf ?lhs \<le> Inf ?rhs"
      using cInf_superset_mono[of ?rhs ?lhs] by fast
    moreover have "n - (n - m + j) = n - (n - m + j + 1) + 1" using assms by linarith
    ultimately show ?thesis by (simp add: less_eq_complex_def A.minimax_def)
  qed
  also have "... = Inf {A.rayleigh_max ((\<lambda>v. W *\<^sub>v v)`\<V>) | \<V>. B.dimensional \<V> (m - j)}"
    using assms(3) by force
  also have "... = B.minimax (j + 1)"
  proof-
    have "m - j = m - (j + 1) + 1" by (simp add: Suc_diff_Suc assms(5))
    thus ?thesis
      unfolding B.minimax_def B.rayleigh_max A.rayleigh_max
      by (metis (mono_tags, lifting) rayleigh_sets_eq)
  qed
  also have "... = \<beta>!j"
    using courant_fischer(1)[OF assms(4,5) B.dim_is B.is_herm assms(14,15)] by argo
  finally show "\<alpha>!(n - m + j) \<le> \<beta>!j" .
qed

corollary cauchy_eigval_interlacing_alt:
  fixes A W :: "complex mat"
  assumes "n > 0"
  assumes "j < n"
  assumes "m \<le> n"
  assumes "m > 0"
  assumes "j < m"

  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "eigvals_of A \<alpha>"
  assumes "sorted_wrt (\<ge>) \<alpha>"

  assumes "W \<in> carrier_mat n m"
  assumes "W\<^sup>H * W = 1\<^sub>m m"
  assumes "inj_on (\<lambda>v. W *\<^sub>v v) (carrier_vec m)"

  defines "B \<equiv> W\<^sup>H * A * W"
  assumes "eigvals_of B \<beta>"
  assumes "sorted_wrt (\<ge>) \<beta>"

  shows "\<beta>!j \<in> {\<alpha>!(n-m+j)..\<alpha>!j}"
  using cauchy_eigval_interlacing assms by presburger

subsection "Principal Submatrix Corollaries"

corollary ps_eigval_interlacing:
  fixes A :: "complex mat"
  fixes k
  assumes "n > 0"
  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "eigvals_of A \<alpha>"
  assumes "sorted_wrt (\<ge>) \<alpha>"

  assumes "I \<subseteq> {..<n}"
  assumes "I \<noteq> {}"
  defines "B \<equiv> submatrix A I I"
  defines "m \<equiv> card I"
  assumes "eigvals_of B \<beta>"
  assumes "sorted_wrt (\<ge>) \<beta>"

  assumes "j < m"
  shows "\<alpha>!(n-m+j) \<le> \<beta>!j" "\<beta>!j \<le> \<alpha>!j"
proof-
  have 0: "n > 0" using assms(1) .
  have 1: "j < n"
    by (metis assms(6,12) card_lessThan card_mono finite_lessThan m_def not_le not_less_iff_gr_or_eq order.strict_trans)
  have 2: "m \<le> n"
    using assms(6,9) atLeast0LessThan subset_eq_atLeast0_lessThan_card by presburger
  have 3: "m > 0" using assms(12) by linarith
  have 4: "j < m" using assms(12) .
  have 5: "A \<in> carrier_mat n n" using assms(2) .
  have 6: "hermitian A" using assms(3) .
  have 7: "eigvals_of A \<alpha>" using assms(4) .
  have 8: "sorted_wrt (\<ge>) \<alpha>" using assms(5) .

  obtain Inm where Inm:
      "B = Inm\<^sup>H * A * Inm"
      "Inm\<^sup>H * Inm = 1\<^sub>m m"
      "Inm \<in> carrier_mat n m"
      "inj_on ((*\<^sub>v) Inm) (carrier_vec m)"
    using submatrix_as_matrix_prod_obt assms by blast
  hence 9: "eigvals_of (Inm\<^sup>H * A * Inm) \<beta>" using assms(10) by blast
  have 10: "sorted_wrt (\<lambda>x y. y \<le> x) \<beta>" by (simp add: assms(11))

  have *: "\<beta>!j \<in> {\<alpha>!(n-m+j)..\<alpha>!j}"
    using cauchy_eigval_interlacing_alt[OF 0 1 2 3 4 5 6 7 8 Inm(3,2,4) 9 10] .

  from * show "\<alpha>!(n-m+j) \<le> \<beta>!j" by presburger
  from * show"\<beta>!j \<le> \<alpha>!j" by presburger
qed

corollary ps_eigval_interlacing_alt:
  fixes A :: "complex mat"
  fixes k
  assumes "n > 0"
  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "eigvals_of A \<alpha>"
  assumes "sorted_wrt (\<ge>) \<alpha>"

  assumes "I \<subseteq> {..<n}"
  assumes "I \<noteq> {}"
  defines "B \<equiv> submatrix A I I"
  defines "m \<equiv> card I"
  assumes "eigvals_of B \<beta>"
  assumes "sorted_wrt (\<ge>) \<beta>"

  assumes "j < m"
  shows "\<beta>!j \<in> {\<alpha>!(n-m+j)..\<alpha>!j}"
  using ps_eigval_interlacing assms by presburger

subsection "Leading Principal Submatrix Corollaries"

corollary lps_eigval_interlacing:
  fixes A :: "complex mat"
  fixes k
  assumes "n > 0"
  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "eigvals_of A \<alpha>"
  assumes "sorted_wrt (\<ge>) \<alpha>"

  assumes "0 < m"
  assumes "m \<le> n"
  defines "B \<equiv> lps A m"
  assumes "eigvals_of B \<beta>"
  assumes "sorted_wrt (\<ge>) \<beta>"

  assumes "j < m"
  shows "\<alpha>!(n-m+j) \<le> \<beta>!j" "\<beta>!j \<le> \<alpha>!j"
   using ps_eigval_interlacing(1)[OF assms(1,2,3,4,5), of "{..<m}"] assms apply auto[1]
  using ps_eigval_interlacing(2)[OF assms(1,2,3,4,5), of "{..<m}"] assms by auto

corollary lps_eigval_interlacing_alt:
  fixes A :: "complex mat"
  fixes k
  assumes "n > 0"
  assumes "A \<in> carrier_mat n n"
  assumes "hermitian A"
  assumes "eigvals_of A \<alpha>"
  assumes "sorted_wrt (\<ge>) \<alpha>"

  assumes "0 < m"
  assumes "m \<le> n"
  defines "B \<equiv> lps A m"
  assumes "eigvals_of B \<beta>"
  assumes "sorted_wrt (\<ge>) \<beta>"

  assumes "j < m"
  shows "\<beta>!j \<in> {\<alpha>!(n-m+j)..\<alpha>!j}"
  using lps_eigval_interlacing assms by presburger

end