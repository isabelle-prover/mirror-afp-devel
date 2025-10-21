theory Lemma_1_8_Coding                                 
  imports Lemma_1_8_Defs
begin

subsubsection \<open>Bounds on the defined variables\<close>

locale K_Nonnegative = Lemma_1_8_Defs +
  assumes \<delta>_pos: "\<delta> > 0"
      and L_pos: "L > 0"
      and L_lower_bound: "L \<ge> max_coeff P"
      and len_z: "length z = \<nu>+1"
      and \<B>_even: "2 dvd \<B>"
      and \<B>_lower_bound: "\<B> > 2 * fact \<delta> * (nat L) * (1 + sum_list z)^\<delta>"   
begin

text \<open>This is for convenience in proofs, but the following lemma is strictly stronger.\<close>
lemma \<B>_ge_1[simp]: "\<B> \<ge> 1" 
  using \<B>_lower_bound \<delta>_pos L_pos by auto

lemma \<B>_gt_2[simp]: "\<B> > 2" 
  using \<B>_lower_bound
  by (smt (verit, ccfv_threshold) L_pos \<B>_ge_1 fact_gt_zero less_2_cases less_numeral_extra(3)
      less_one linorder_neqE_nat mult_eq_0_iff nat_1_eq_mult_iff nat_le_iff_add not_one_le_zero 
      power_not_zero zero_less_nat_eq)

text \<open>Also for convenience.\<close>
lemma \<B>_ge_2[simp]: "\<B> \<ge> 2" 
  using \<B>_gt_2 by linarith

lemma b_def_reverse: "2 * b = \<B>" using \<B>_even b_def by simp

lemma b_ge_1[simp]: "b \<ge> 1" 
  using b_def_reverse \<B>_ge_1 by fastforce

lemma n_ge_1[simp]: "n j \<ge> 1" 
  unfolding n_def by auto

lemma L_lower_bound_specialize: "L \<ge> abs (P_coeff i)" 
proof cases
  assume assm: "P_coeff i \<noteq> 0"
  hence "P_coeff i \<in> coeffs P"
    unfolding P_coeff_def coeffs_def by (simp add: coeff_def coeff_keys)
  hence 0: "abs (P_coeff i) \<in> abs ` coeffs P"
    by auto

  have "L \<ge> Max (abs ` coeffs P)"
    using L_lower_bound max_coeff_def by metis
  thus ?thesis
    using 0 by (meson Max_ge finite_coeffs finite_imageI order_trans)
next 
  assume "\<not> P_coeff i \<noteq> 0"
  hence "P_coeff i = 0" by auto
  thus ?thesis using L_pos by auto
qed

lemma \<delta>_tuples_finite[simp]: "finite \<delta>_tuples"
proof -
  have stronger: "finite {i::nat list. length i = n \<and> sum_list i \<le> K }" 
    (is "finite (?S n)") for n K
  proof (induction n)
    case 0 thus ?case by auto
  next
    case (Suc n)
    { fix i assume assm_i: "i \<in> ?S (Suc n)"
      then obtain j0 j where i_def: "i = j0#j"
        by (smt (verit, best) Suc_length_conv mem_Collect_eq)
      hence "(j0, j) \<in> ({..K} \<times> ?S n)" using assm_i by auto
      hence "i \<in> (\<lambda>(j0, j). j0#j) ` ({..K} \<times> ?S n)" using i_def by auto }
    hence "?S (Suc n) \<subseteq> (\<lambda>(j0, j). j0#j) ` ({..K} \<times> ?S n)" 
     by blast
    moreover have "finite ((\<lambda>(j0, j). j0#j) ` ({..K} \<times> ?S n))" 
      using Suc.IH by blast
    ultimately have "finite (?S (Suc n))" 
      by (meson finite_subset)
    thus ?case .
  qed
  thus ?thesis unfolding \<delta>_tuples_def .
qed

lemma P_z_insertion: "insertion z_assign P = (\<Sum>i\<in>\<delta>_tuples. P_coeff i * mpow z i)"
proof -
  have mpow_eq: "i\<in>\<delta>_tuples \<Longrightarrow> (\<Prod>s\<le>\<nu>. (z_assign s)^(i!s)) = mpow z i" for i
  proof -
    assume i_def: "i\<in>\<delta>_tuples" 
    have 0: "s < length z \<Longrightarrow> z_assign s = int (z!s)" for s
    proof -
      assume "s < length z"
      hence "s < length (map int z)" 
        using length_map by simp
      hence "z_assign s = (map int z) ! s"
        unfolding z_assign_def using nth0_nth by blast
      also have "... = int (z ! s)"
        using `s < length z` nth_map by blast
      finally show ?thesis .
    qed

    have z_i_length: "min (length z) (length i) = length z"
      using \<delta>_tuples_def len_z i_def by auto
    
    have "(\<Prod>s\<le>\<nu>. (z_assign s)^(i!s)) = (\<Prod>s<length z. (z_assign s)^(i!s))"
      using Suc_eq_plus1 len_z lessThan_Suc_atMost by presburger  
    also have "... = (\<Prod>s<length z. (int (z!s))^(i!s))"
      using 0 by simp
    finally show "(\<Prod>s\<le>\<nu>. (z_assign s)^(i!s)) = int (mpow z i)"
      unfolding mpow_def using z_i_length by auto
  qed
 
  have "P = (\<Sum>i\<in>\<delta>_tuples. of_int (P_coeff i) * (\<Prod>s=0..\<nu>. (Var s)^(i!s)))"
    unfolding \<delta>_tuples_def \<nu>_def \<delta>_def of_int_Const P_coeff_def 
    using mpoly_multivariate_expansion by auto
  hence "insertion z_assign P = (\<Sum>i\<in>\<delta>_tuples. insertion z_assign (of_int (P_coeff i)) * 
    insertion z_assign (\<Prod>s\<le>\<nu>. (Var s)^(i!s)))"
    using insertion_sum insertion_mult \<delta>_tuples_finite
    by (smt (verit, del_insts) sum.cong atLeast0AtMost)
  also have "... = (\<Sum>i\<in>\<delta>_tuples. P_coeff i * insertion z_assign (\<Prod>s\<le>\<nu>. (Var s)^(i!s)))"
    using of_int_Const by simp
  also have "... = (\<Sum>i\<in>\<delta>_tuples. P_coeff i * mpow z i)" 
    by (simp add: mpow_eq)
  finally show ?thesis .
qed


text \<open>This is essentially an instance of the multinomial theorem.\<close>
lemma c_delta_expansion:
  "(1+c)^\<delta> = (\<Sum>i\<in>\<delta>_tuples. of_nat ((\<delta> mchoose i) * mpow z i) * X^(\<Sum>s\<le>\<nu>. i!s * n s))"
proof -
  define F::"(int mpoly) list" where 
    "F = map (\<lambda>s. of_nat (z!(nat s)) * X^(n (nat s))) [0..\<nu>]"   
  
  have F_length: "length F = \<nu>+1" 
    unfolding F_def by simp

  have F_get: "s < length F \<Longrightarrow> F!s = of_nat (z!s) * X^(n s)" for s 
    unfolding F_def using F_length by simp

  have F_mpow: "length i = \<nu> + 1 \<Longrightarrow>
    mpow F i = of_nat (mpow z i) * X ^ (\<Sum>s<\<nu> + 1. i ! s * n s)" for i
  proof -
    assume "length i = \<nu> + 1"
    hence F_i_length: "min (length F) (length i) = \<nu> + 1" using F_length by auto
    have "mpow F i = (\<Prod>s<\<nu>+1. (of_nat (z!s) * X^(n s)) ^ i!s)" 
      using F_i_length by (simp add: mpow_def F_get)
    also have "... = (\<Prod>s<\<nu>+1. (of_nat (z!s))^ i!s) * (\<Prod>s<\<nu>+1. (X^(n s)) ^ i!s)"
     by (simp add: power_mult_distrib prod.distrib)   
    also have "... = of_nat (mpow z i) * (\<Prod>s<\<nu>+1. (X^(n s)) ^ i!s)" 
      unfolding mpow_def using len_z F_i_length by auto
    also have "... = of_nat (mpow z i) * (\<Prod>s<\<nu>+1. X^(i!s * n s))"
      by (metis mult.commute power_mult)
    also have "... = of_nat (mpow z i) * X^(\<Sum>s<\<nu>+1. i!s * n s)" 
      by (smt (verit, ccfv_SIG) power_sum prod.cong)
    finally show ?thesis .
  qed

  have "(1 + c)^\<delta> = (1 + (\<Sum>s\<le>\<nu>. F!s))^\<delta>" 
    by (simp add : c_def F_get F_length)
  also have "... = (1 + sum_list F)^\<delta>" 
    using F_length by (metis Suc_eq_plus1 atLeastLessThanSuc_atLeastAtMost sum_list_sum_nth 
                       atLeast0AtMost)
  also have "... = (\<Sum>i | length i = length F \<and> sum_list i \<le> \<delta>. of_nat (\<delta> mchoose i) * mpow F i)" 
    by (simp only: multinomial_ring_alt)
  also have "... = (\<Sum>i\<in>\<delta>_tuples. of_nat (\<delta> mchoose i) * mpow F i)" 
    unfolding \<delta>_tuples_def by (simp add: F_length)
  also have "... = (\<Sum>i\<in>\<delta>_tuples. of_nat (\<delta> mchoose i) * 
    of_nat (mpow z i) * X^(\<Sum>s\<le>\<nu>. i!s * n s))"
    by (auto simp add: algebra_simps F_mpow \<delta>_tuples_def lessThan_Suc_atMost)
  finally show ?thesis by auto
qed

lemma n_\<nu>p1_ge_sum: "i\<in>\<delta>_tuples \<Longrightarrow> n (\<nu>+1) \<ge> (\<Sum>s\<le>\<nu>. i!s * n s)"
proof - 
  assume i_def: "i\<in>\<delta>_tuples"

  { fix s assume "s \<in> {..\<nu>}" 
    hence "i!s * n s \<le> i!s * n \<nu>" 
      unfolding n_def by (simp add: power_increasing) }
  note 0 = this

  have "(\<Sum>s\<le>\<nu>. i!s * n s) \<le> (\<Sum>s\<le>\<nu>. i!s * n \<nu>)"
    using 0 by (meson atLeastAtMost_iff atMost_iff sum_mono zero_le)
  also have "... = n \<nu> * (\<Sum>s\<le>\<nu>. i!s)"
    using sum_distrib_right by (metis mult.commute)
  also have "... = n \<nu> * (\<Sum>s<length i. i!s)"
    using i_def unfolding \<delta>_tuples_def using lessThan_Suc_atMost by force
  also have "... = n \<nu> * sum_list i"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  also have "... \<le> n \<nu> * \<delta>"
    using i_def unfolding \<delta>_tuples_def by simp
  also have "... \<le> n (\<nu>+1)"
    unfolding n_def by auto
  finally show ?thesis .
qed

lemma D_exponent_inj: "inj_on D_exponent \<delta>_tuples"
proof
  have digit: "i \<in> \<delta>_tuples \<Longrightarrow> 
    nth_digit (\<Sum>s\<le>\<nu>. i!s * (\<delta>+1)^s) s (\<delta>+1) = (if s \<le> \<nu> then i!s else 0)" for i s
  proof -
    assume i_def: "i \<in> \<delta>_tuples"
    have "s \<le> \<nu> \<Longrightarrow> i!s < \<delta>+1" for s
    proof -
      assume "s \<le> \<nu>" 
      hence "s < length i" using i_def \<delta>_tuples_def by auto
      hence "i!s \<le> sum_list i" using elem_le_sum_list by auto
      thus ?thesis using i_def \<delta>_tuples_def by auto
    qed 
    hence "nth_digit (\<Sum>s=0..\<nu>. i!s * (\<delta>+1)^s) s (\<delta>+1) = (if s \<le> \<nu> then i!s else 0)"
      using nth_digit_gen_power_series_general[of "\<delta>+1" \<nu>] \<delta>_pos by simp
    thus ?thesis
      using atMost_atLeast0 by presburger
  qed

  fix i j assume i_def: "i\<in>\<delta>_tuples" and j_def: "j\<in>\<delta>_tuples" 
    and "D_exponent i = D_exponent j"
  hence "(\<Sum>s\<le>\<nu>. i!s * (\<delta>+1)^s) = (\<Sum>s\<le>\<nu>. j!s * (\<delta>+1)^s)"
    unfolding D_exponent_def using n_\<nu>p1_ge_sum n_def
    by (metis (no_types, lifting) diff_diff_cancel sum.cong)
  hence "s \<le> \<nu> \<Longrightarrow> i!s = j!s" for s
    using digit i_def j_def by (metis (full_types))
  hence "s < length i \<Longrightarrow> i!s = j!s" for s  
    using i_def unfolding \<delta>_tuples_def by auto
  thus "i = j" 
    apply (simp add: List.list_eq_iff_nth_eq)
    using \<delta>_tuples_def i_def j_def by force
qed

definition R_exponent :: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where 
  "R_exponent i j = D_exponent j + (\<Sum>s\<le>\<nu>. i!s * n s)"

lemma R_expansion:
  "R = (\<Sum>i\<in>\<delta>_tuples. (\<Sum>j\<in>\<delta>_tuples. 
    of_int ((\<delta> mchoose i) * mfact j * fact (\<delta> - sum_list j) * mpow z i * P_coeff j) *
    X^(R_exponent i j)))"
proof -
  define A::"nat list \<Rightarrow> int mpoly" where "A = (\<lambda>i. of_nat ((\<delta> mchoose i) * mpow z i))" 
  define B::"nat list \<Rightarrow> int mpoly" where "B = (\<lambda>i. of_int (D_precoeff i * P_coeff i))" 
  
  have AB_rewrite: "A i * B j = of_int ((\<delta> mchoose i) * mfact j * 
    fact (\<delta> - sum_list j) * mpow z i * P_coeff j)" for i j
  using A_def B_def D_precoeff_def by simp

  have "R = (1+c)^\<delta> * D" by (simp add: R_def)
  also have "... = (\<Sum>i\<in>\<delta>_tuples. A i * X^(\<Sum>s\<le>\<nu>. i!s * n s)) *
    (\<Sum>j\<in>\<delta>_tuples. B j * X^(D_exponent j))"
    by (simp add: D_def c_delta_expansion A_def B_def)
  also have "... = (\<Sum>i\<in>\<delta>_tuples. (\<Sum>j\<in>\<delta>_tuples. 
    A i * X^(\<Sum>s\<le>\<nu>. i!s * n s) * (B j * X^(D_exponent j))))"
    using sum_product by simp
  also have "... = (\<Sum>i\<in>\<delta>_tuples. (\<Sum>j\<in>\<delta>_tuples. 
    (A i * B j) * (X^(\<Sum>s\<le>\<nu>. i!s * n s) * X^(D_exponent j))))"
    by (simp add: algebra_simps)
  also have "... = (\<Sum>i\<in>\<delta>_tuples. (\<Sum>j\<in>\<delta>_tuples. 
    A i * B j * X^(R_exponent i j)))"
    unfolding R_exponent_def by (simp add: mult.commute power_add)
  finally show ?thesis by (simp add: AB_rewrite)
qed

lemma c_degree_bound: "degree c 0 \<le> n \<nu>"
proof -
  have 0: "s\<in>{..\<nu>} \<Longrightarrow> degree (of_nat (z!s) * X^(n s)) 0 \<le> n \<nu>" for s
  proof -
    assume Hs: "s \<in> {..\<nu>}"
    have "degree (of_nat (z!s) * X^(n s)) 0 \<le> degree (X^(n s)) 0"
      using degree_mult degree_Const of_nat_Const by (metis add_0)
    also have "... \<le> n s * degree X 0"
      using degree_pow by auto
    also have "... = n s" 
      unfolding X_def using degree_Var by (metis nat_mult_1_right) 
    also have "... \<le> n \<nu>"
      unfolding n_def using Hs
      by (simp add: power_increasing)
    finally show ?thesis .
  qed

  have "degree c 0 \<le> Max (insert 0 ((\<lambda>s. degree (of_nat (z!s) * X^(n s)) 0) ` {..\<nu>}))"
    unfolding c_def using degree_sum by blast
  also have "... \<le> n \<nu>" 
    by (simp add: 0)
  finally show ?thesis .
qed

lemma D_degree_bound: "degree D 0 \<le> n (\<nu>+1)"
proof -
  have 0: "i\<in>\<delta>_tuples \<Longrightarrow>  
    degree (of_int (D_precoeff i * P_coeff i) * X^(D_exponent i)) 0 \<le> n (\<nu>+1)" for i
  proof -
    assume "i\<in>\<delta>_tuples"
    have "degree (of_int (D_precoeff i * P_coeff i) * X^(D_exponent i)) 0 \<le> 
      degree (X^(D_exponent i)) 0" 
      using degree_mult degree_Const of_int_Const by (metis add_0)
    also have "... \<le> D_exponent i"
      unfolding X_def using degree_pow degree_Var by (metis mult.right_neutral)
    also have "... \<le> n (\<nu>+1)"
      unfolding D_exponent_def by auto
    finally show ?thesis .
  qed

  have "degree D 0 \<le> Max (insert 0 (
    (\<lambda>i. degree (of_int (D_precoeff i * P_coeff i) * X^(D_exponent i)) 0) ` \<delta>_tuples))"
    unfolding D_def using degree_sum \<delta>_tuples_finite by blast
  also have "... \<le> n (\<nu>+1)"
    using 0 by auto
  finally show ?thesis .
qed

lemma R_degree_bound: "degree R 0 \<le> (2*\<delta>+1) * n \<nu>"
proof - 
  have c_1_deg: "degree (1 + c) 0 \<le> degree c 0"
  proof cases
    assume "degree c 0 \<ge> 1"
    thus ?thesis using degree_add degree_one by (metis max_def zero_le)
  next
    assume "\<not> 1 \<le> degree c 0"
    hence "degree c 0 = 0" by auto
    moreover have "degree (1 + c) 0 \<le> 0"
      by (metis degree_add MPoly_Type.degree_one calculation max_0L) 
    ultimately show ?thesis by auto
  qed

  have "degree R 0 \<le> degree ((1+c)^\<delta>) 0 + degree D 0"
    unfolding R_def by (simp add: degree_mult)
  also have "... \<le> \<delta> * degree (1+c) 0 + degree D 0"
    by (simp add: degree_pow)
  also have "... \<le> \<delta> * degree c 0 + degree D 0" 
    by (simp add: c_1_deg)
  also have "... \<le> \<delta> * n \<nu> + n (\<nu>+1)"
    using c_degree_bound D_degree_bound by (simp add: add_le_mono)
  finally show ?thesis unfolding n_def by auto
qed  


lemma R_univariate: "vars R \<subseteq> {0}"
proof -
  define x where "x = (\<lambda>i j. of_int 
    (int ((\<delta> mchoose i) * mfact j * fact (\<delta> - sum_list j) * mpow z i) * P_coeff j) 
    * X ^ R_exponent i j)"
  have vars_0: "vars (x i j) \<subseteq> {0}" for i j 
  proof -
    have "vars (x i j) \<subseteq> vars (X^R_exponent i j)"
      using vars_Const vars_mult of_int_Const x_def by fastforce
    also have "... \<subseteq> vars X"
      using vars_pow by auto
    also have "... = {0}"
      using vars_Var X_def by metis
    finally show ?thesis .
  qed

  have "vars R \<subseteq> (\<Union>i\<in>\<delta>_tuples. vars (\<Sum>j\<in>\<delta>_tuples. x i j))" 
    unfolding R_expansion x_def using vars_setsum \<delta>_tuples_finite by blast
  also have "... \<subseteq> (\<Union>i\<in>\<delta>_tuples. (\<Union>j\<in>\<delta>_tuples. vars (x i j)))"
    using vars_setsum \<delta>_tuples_finite by fast
  also have "... \<subseteq> (\<Union>i\<in>\<delta>_tuples. (\<Union>j\<in>\<delta>_tuples. {0}))"
    using vars_0 by auto
  also have "... \<subseteq> {0}"
    by auto
  finally show ?thesis .
qed

lemma R_sum_e: "R = (\<Sum>i\<le>(2*\<delta>+1) * n \<nu>. (of_int (e i)) * X^i)"
proof -
  have 0: "i \<notin> {..(2*\<delta>+1) * n \<nu>} \<Longrightarrow> of_int (e i) * X^i = 0" for i
  proof -
    assume "i\<notin>{..(2*\<delta>+1) * n \<nu>}"
    hence "i > (2*\<delta>+1) * n \<nu>" 
      by auto
    hence "i > degree R 0" 
      using R_degree_bound by auto
    hence "i \<notin> ((\<lambda>m. lookup m 0) ` keys (mapping_of R))"
      unfolding degree_def by auto
    hence "Poly_Mapping.single 0 i \<notin> keys (mapping_of R)"
      by (metis lookup_single_eq rev_image_eqI)
    hence "e i = 0" 
      unfolding e_def coeff_def by (simp add: in_keys_iff)
    thus ?thesis by auto
  qed

  have "R = Sum_any (\<lambda>i. monom (Poly_Mapping.single 0 i) (e i))"
    using mpoly_univariate_expansion R_univariate e_def by auto
  also have "... = Sum_any (\<lambda>i. Const (e i) * monom (Poly_Mapping.single 0 i) 1)"
    using cst_poly_times_monom_one by (metis (mono_tags, lifting) Const.abs_eq)
  also have "... = Sum_any (\<lambda>i. of_int (e i) * X^i)"
    unfolding of_int_Const e_def X_def
    by (metis (no_types, lifting) Var.abs_eq Var\<^sub>0_def monom.abs_eq monom_pow mult_1 power_one)
  also have "... = Sum_any (\<lambda>i. if i\<in>{..(2*\<delta>+1) * n \<nu>} then of_int (e i) * X^i else 0)"
    using 0 by meson
  also have "... = (\<Sum>i\<in>{..(2*\<delta>+1) * n \<nu>}. of_int (e i) * X^i)"
    by (simp add: Sum_any.conditionalize)
  finally show ?thesis .
qed


lemma e_expression:
  "e p = (\<Sum>i\<in>\<delta>_tuples. (\<Sum>j\<in>\<delta>_tuples \<inter> {j. R_exponent i j = p}.
    (\<delta> mchoose i) * mfact j * fact (\<delta> - sum_list j) * P_coeff j * mpow z i))"
proof -
  define m where "m = Poly_Mapping.single (0::nat) p"
  define c where "c = (\<lambda>i j. 
    (\<delta> mchoose i) * mfact j * fact (\<delta> - sum_list j) * mpow z i * P_coeff j)"

  { fix i j
    have "X^(R_exponent i j) = monom (Poly_Mapping.single 0 (R_exponent i j)) 1"
      unfolding X_def
      by (metis Var.abs_eq Var\<^sub>0_def monom.abs_eq monom_pow nat_mult_1 power_one)
    hence "of_int (c i j) * X^(R_exponent i j) = monom (Poly_Mapping.single 0 (R_exponent i j)) (c i j)"
      unfolding of_int_Const using cst_poly_times_monom_one by (metis Const.abs_eq)
    hence "coeff (of_int (c i j) * X^(R_exponent i j)) m =
      coeff (monom (Poly_Mapping.single 0 (R_exponent i j)) (c i j)) m"
      by simp
    also have "... = (c i j when m = Poly_Mapping.single 0 (R_exponent i j))"
      using More_MPoly_Type.coeff_monom by blast
    also have "... = (c i j when R_exponent i j = p)"
      unfolding m_def by (smt (verit, best) lookup_single_eq)
    finally have "coeff (of_int (c i j) * X^(R_exponent i j)) m = 
      (c i j when R_exponent i j = p)" . }
  note coeff_interior = this

  have 0: "(\<Sum>j\<in>\<delta>_tuples. (c i j when R_exponent i j = p)) =
     (\<Sum>j\<in>\<delta>_tuples \<inter> {j. R_exponent i j = p}. c i j)" for i
     using \<delta>_tuples_finite
     by (smt (verit, ccfv_SIG) mem_Collect_eq sum.cong sum.inter_restrict when_def)

   have "e p = coeff (\<Sum>i\<in>\<delta>_tuples. (\<Sum>j\<in>\<delta>_tuples. of_int (c i j) * X^(R_exponent i j))) m"
    unfolding e_def m_def c_def using R_expansion by simp
  also have "... = (\<Sum>i\<in>\<delta>_tuples. (\<Sum>j\<in>\<delta>_tuples. coeff (of_int (c i j) * X^(R_exponent i j)) m))"
    using coeff_sum \<delta>_tuples_finite by (smt (verit, best) sum.cong)
  also have "... = (\<Sum>i\<in>\<delta>_tuples. (\<Sum>j\<in>\<delta>_tuples. (c i j when R_exponent i j = p)))"
    using coeff_interior by simp
  also have "... = (\<Sum>i\<in>\<delta>_tuples. (\<Sum>j\<in>\<delta>_tuples \<inter> {j. R_exponent i j = p}. c i j))"
    using 0 by simp
  finally show ?thesis unfolding c_def
    by (smt (verit, ccfv_SIG) ab_semigroup_mult_class.mult_ac(1) 
        mult.commute of_nat_mult sum.cong)  
qed

text \<open>This is a key step of the proof.\<close>
lemma e_n_\<nu>1_expression: "e (n (\<nu>+1)) = fact \<delta> * insertion z_assign P"
proof -
  have simp_indices: "i\<in>\<delta>_tuples \<Longrightarrow> \<delta>_tuples \<inter> {j. R_exponent i j = n (\<nu>+1)} = {i}" 
    (is "_ \<Longrightarrow> ?S i = {i}") for i
  proof -
    assume i_def: "i\<in>\<delta>_tuples"
    have 0: "i \<in> ?S i"
      unfolding R_exponent_def D_exponent_def using n_\<nu>p1_ge_sum i_def by simp
    have 1: "j1 \<in> ?S i \<Longrightarrow> j2 \<in> ?S i \<Longrightarrow> j1 = j2" for j1 j2
      unfolding R_exponent_def using D_exponent_inj
      by (simp add: inj_on_def)   
    
    have "{i} \<subseteq> ?S i" using 0 by auto
    moreover have "card (?S i) \<le> 1" using 1 by (simp add: card_le_Suc0_iff_eq)
    ultimately show ?thesis
      by (metis One_nat_def \<delta>_tuples_finite card.empty card.insert
          card_seteq empty_iff finite.emptyI finite_Int)
  qed

  have simp_coeff: "i\<in>\<delta>_tuples \<Longrightarrow> (\<delta> mchoose i) * mfact i * fact (\<delta> - sum_list i) = fact \<delta>" for i
    unfolding \<delta>_tuples_def multinomial_def multinomial'_def using mchoose_dvd by fastforce
   
  have "e (n (\<nu>+1)) = (\<Sum>i\<in>\<delta>_tuples. (\<Sum>j\<in>\<delta>_tuples \<inter> {j. R_exponent i j = n (\<nu>+1)}.
    (\<delta> mchoose i) * mfact j * fact (\<delta> - sum_list j) * P_coeff j * mpow z i))"
    by (simp add: e_expression)
  also have "... = (\<Sum>i\<in>\<delta>_tuples.
    (\<delta> mchoose i) * mfact i * fact (\<delta> - sum_list i) * P_coeff i * mpow z i)"
    using simp_indices by auto
  also have "... = (\<Sum>i\<in>\<delta>_tuples. fact \<delta> * P_coeff i * mpow z i)"
    using simp_coeff by auto
  also have "... = fact \<delta> * (\<Sum>i\<in>\<delta>_tuples. P_coeff i * mpow z i)"
    using sum_distrib_left
    by (smt (verit) ab_semigroup_mult_class.mult_ac(1) sum.cong)
  also have "... = fact \<delta> * insertion z_assign P"
    using P_z_insertion by simp
  finally show ?thesis .
qed

lemma abs_int[simp]: "abs (int x) = int x" 
  using abs_of_nat by auto

text \<open>This is a key step of the proof.\<close>
lemma e_upper_bound:
  "abs (e p) \<le> fact \<delta> * L * (1 + sum_list z)^\<delta>"
proof -
  { 
    fix i assume "i\<in>\<delta>_tuples"
    define S_i where "S_i = \<delta>_tuples \<inter> {j. R_exponent i j = p}"

    have "finite S_i" unfolding S_i_def using \<delta>_tuples_finite by simp
    
    { fix j1 j2 assume "j1 \<in> S_i" and "j2 \<in> S_i" 
      hence "D_exponent j1 = D_exponent j2" 
        unfolding S_i_def R_exponent_def by auto
      hence "j1 = j2" 
        using `j1 \<in> S_i` `j2 \<in> S_i` D_exponent_inj unfolding S_i_def
        by (meson IntD1 inj_on_contraD) }
    hence "card S_i \<le> 1" by (simp add: `finite S_i` card_le_Suc0_iff_eq)
 
    have 0: "(\<Sum>j\<in>S_i. mfact j * fact (\<delta> - sum_list j) * abs (P_coeff j)) \<le> 
      fact \<delta> * L * card S_i"
    proof -
      have "j\<in>S_i \<Longrightarrow> mfact j * fact (\<delta> - sum_list j) \<le> fact \<delta>" for j
        unfolding S_i_def \<delta>_tuples_def using mchoose_le by blast
      hence "j\<in>S_i \<Longrightarrow> mfact j * fact (\<delta> - sum_list j) * abs (P_coeff j) \<le> fact \<delta> * L" for j
        using L_lower_bound_specialize
        by (metis abs_ge_zero mult_mono' of_nat_0_le_iff of_nat_fact zle_int)
      thus ?thesis by (simp add: mult.commute sum_bounded_above)
    qed

    have "abs (\<Sum>j\<in>S_i. (\<delta> mchoose i) * mfact j * fact (\<delta> - sum_list j) * P_coeff j * mpow z i)
      \<le> (\<Sum>j\<in>S_i. abs ((\<delta> mchoose i) * mfact j * fact (\<delta> - sum_list j) * P_coeff j * mpow z i))"
      using sum_abs by simp
    also have "... = (\<Sum>j\<in>S_i. (\<delta> mchoose i) * 
      mfact j * fact (\<delta> - sum_list j) * abs (P_coeff j) * mpow z i)"
      using abs_mult abs_int by (metis (no_types, opaque_lifting))
    also have "... = (\<Sum>j\<in>S_i. int (\<delta> mchoose i) * mpow z i * 
      (mfact j * fact (\<delta> - sum_list j) * abs (P_coeff j)))"
      by (simp add: algebra_simps)
    also have "... = int (\<delta> mchoose i) * mpow z i *
      (\<Sum>j\<in>S_i. mfact j * fact (\<delta> - sum_list j) * abs (P_coeff j))"
      by (simp only: sum_distrib_left) 
    also have "... \<le> int (\<delta> mchoose i) * mpow z i * (fact \<delta> * L * card S_i)"
      using 0 by (simp add: mult_left_mono)
    also have "... \<le> fact \<delta> * L * int (\<delta> mchoose i) * mpow z i"
      using `card S_i \<le> 1` L_pos order_le_less by fastforce
    finally have "abs (\<Sum>j\<in>S_i. (\<delta> mchoose i) * mfact j * fact (\<delta> - sum_list j) *
      P_coeff j * mpow z i) \<le> fact \<delta> * L * int (\<delta> mchoose i) * mpow z i" .
  } note bound_coeff = this
    
  have "abs (e p) \<le> (\<Sum>i\<in>\<delta>_tuples. abs (\<Sum>j\<in>\<delta>_tuples \<inter> {j. R_exponent i j = p}. 
    (\<delta> mchoose i) * mfact j * fact (\<delta> - sum_list j) * P_coeff j * mpow z i))"
    using sum_abs e_expression by simp
  also have "... \<le> (\<Sum>i\<in>\<delta>_tuples. fact \<delta> * L * (int (\<delta> mchoose i) * mpow z i))"
    using bound_coeff
    by (simp add: ab_semigroup_mult_class.mult_ac(1) sum_mono)
  also have "... = fact \<delta> * L * (\<Sum>i\<in>\<delta>_tuples. int (\<delta> mchoose i) * mpow z i)" 
    by (simp only: sum_distrib_left)
  also have "... = fact \<delta> * L * int (\<Sum>i\<in>\<delta>_tuples. (\<delta> mchoose i) * mpow z i)"
    using int_sum by simp
  also have "... = fact \<delta> * L * int ((1 + sum_list z)^\<delta>)"
    unfolding \<delta>_tuples_def
    by (simp only: multinomial_ring_alt len_z of_nat_id)
   finally show ?thesis by simp
qed

lemma e_b_bound: shows "0 < e j + b" and "e j + b < \<B>"
proof -
  have 0: "abs (e j) < b"
  proof -
    have "2 * abs (e j) \<le> 2 * fact \<delta> * L * (1 + sum_list z)^\<delta>"
      using e_upper_bound by (simp add: algebra_simps)
    also have "... = int ( 2 * fact \<delta> * (nat L) * (1 + sum_list z)^\<delta>)" 
      using int_ops L_pos by auto
    also have "... < int \<B>" using \<B>_lower_bound
      by presburger
    finally show ?thesis using b_def_reverse by auto
  qed

  have "e j < b" using 0 by linarith
  thus "e j + b < \<B>" using b_def_reverse by linarith
  
  have "- e j < b" using 0 by linarith
  thus "0 < e j + b" by linarith
qed 

text \<open>This is a key step of the proof.\<close>
lemma K_expression: "K = (\<Sum>i\<le>(2*\<delta>+1) * n \<nu>. (e i + int b) * \<B>^i)"
proof -
  have 0: "insertion \<B>_assign R = (\<Sum>i\<le>(2*\<delta>+1) * n \<nu>. (e i) * \<B>^i)"
  proof -
    have "insertion \<B>_assign R = (\<Sum>i\<le>(2*\<delta>+1) * n \<nu>. (e i) * (insertion \<B>_assign X)^i)"
      by (simp add: R_sum_e)
    also have "... = (\<Sum>i\<le>(2*\<delta>+1) * n \<nu>. (e i) * \<B>^i)"
      unfolding X_def \<B>_assign_def by simp
    finally show ?thesis .  
  qed

  have "K = insertion \<B>_assign R + S" 
    by (simp add: K_def)
  also have "... = (\<Sum>i\<le>(2*\<delta>+1) * n \<nu>. e i * \<B>^i) + (\<Sum>i\<le>(2*\<delta>+1) * n \<nu>. b * \<B>^i)"
    by (simp add: S_def 0)
  also have "... = (\<Sum>i\<le>(2*\<delta>+1) * n \<nu>. (e i + int b) * \<B>^i)"
    by (simp add: sum.distrib algebra_simps)
  finally show ?thesis .
qed

lemma \<delta>_n_positive: "0 < (2*\<delta>+1) * n \<nu>"
  using n_ge_1
  by (metis add_gr_0 mult_pos_pos not_gr0 not_one_le_zero zero_less_one)

lemma K_lower_bound: "K > int \<B>^((2*\<delta>+1) * n \<nu>)"
proof -
  from \<delta>_n_positive have "(\<Sum>i=0..<(2*\<delta>+1) * n \<nu>. \<B>^i) = 1 + (\<Sum>i=1..<(2*\<delta>+1) * n \<nu>. \<B>^i)" 
    using sum.atLeast_Suc_lessThan power_0 by (metis One_nat_def)
  hence 0: "(\<Sum>i<(2*\<delta>+1) * n \<nu>. \<B>^i) > 0"
    by (metis Suc_eq_plus1 add.commute atLeast0LessThan zero_less_Suc)
   
  have "j \<in> {..(2*\<delta>+1) * n \<nu>} \<Longrightarrow> 1 \<le> e j + b" for j
    using int_one_le_iff_zero_less e_b_bound by blast  
  hence 1: "j \<in> {..(2*\<delta>+1) * n \<nu>} \<Longrightarrow> \<B>^j \<le> (e j + b) * \<B>^j" for j
    using \<B>_ge_1 by simp

  have "int \<B>^((2*\<delta>+1) * n \<nu>) < int (\<Sum>i<(2*\<delta>+1) * n \<nu>. \<B>^i) + \<B>^((2*\<delta>+1) * n \<nu>)" 
    using 0 by (simp add: nat_int_comparison(2))
  also have "... = (\<Sum>i<(2*\<delta>+1) * n \<nu>. int \<B>^i) + \<B>^((2*\<delta>+1) * n \<nu>)"
    using Int.int_sum by simp
  also have "... = (\<Sum>i\<le>(2*\<delta>+1) * n \<nu>. int \<B>^i)"
    by (metis lessThan_Suc_atMost of_nat_eq_of_nat_power_cancel_iff sum.lessThan_Suc)
  also have "... \<le> K" unfolding K_expression
    using sum_mono 1 by (metis (no_types, lifting) of_nat_power)
  finally show ?thesis .
qed

corollary K_gt_0: "K > 0"
  using \<B>_gt_2 \<delta>_n_positive K_lower_bound
  by (smt (verit) of_nat_zero_less_power_iff power_eq_0_iff zero_less_power2)

end

end
