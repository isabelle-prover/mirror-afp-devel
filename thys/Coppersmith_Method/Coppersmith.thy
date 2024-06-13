section \<open> Proof of Coppersmith's Method \<close>

text \<open> In this file, we prove the full version of Coppersmith's method. \<close>

theory Coppersmith
imports Coppersmith_Generic
begin

subsection \<open> Preliminaries and setup \<close>

lemma calculate_h_coppersmith_aux_gteq1: 
  fixes e::"real"
  assumes "degree p > 1"
  assumes "e > 0"
  shows "calculate_h_coppersmith_aux p e \<ge> 1"
proof - 
  let ?x = "degree p"
  have h1: "real ?x - 1 > 0"
    using assms by simp
  have h2: "(real ?x * e) > 0"
    using assms by simp
  have "(real ?x - 1)/(real ?x*e) > 0"
    using h1 h2 by simp
  then have "((real ?x - 1) / (real ?x * e) + 1) / real ?x > 0"
    using assms 
    by (smt (verit) h1 zero_less_divide_iff)
  then show ?thesis   unfolding calculate_h_coppersmith_aux_def 
    by (smt (verit) zero_less_ceiling)
qed

lemma calculate_h_coppersmith_aux_gt1: 
  assumes deg_gt: "degree p > 1"
  assumes "e > 0"
  assumes e_lt2: "e < 1/(real (degree p))"
  shows "calculate_h_coppersmith_aux p e > 1"
proof - 
  let ?x = "degree p"
  have xe: "real ?x * e < 1"
    using e_lt2 deg_gt 
    by (simp add: less_divide_eq mult_of_nat_commute)
  then have div_gt: "(real ?x - 1) / (real ?x * e) > real ?x - 1" 
    by (smt (verit) assms(1) assms(2) div_by_1 divide_strict_left_mono less_imp_of_nat_less linordered_semiring_strict_class.mult_pos_pos of_nat_1)
  have "((real ?x - 1) / (real ?x * e) + 1) > real ?x"
    using div_gt  
    by linarith
  then show ?thesis
  unfolding calculate_h_coppersmith_aux_def 
  by (smt (verit, ccfv_SIG) assms(2) e_lt2 less_divide_eq_1_pos one_less_ceiling zero_less_divide_iff)
qed

subsubsection \<open> Dimension properties of matrix \<close>

lemma dim_vector_vec_associated_to_int_poly_padded:
  shows "dim_vec (vec_associated_to_int_poly_padded n p X)  = n"
  unfolding vec_associated_to_int_poly_padded_def by simp

lemma dim_vector_row_of_coppersmith_matrix:
  shows "dim_vec (row_of_coppersmith_matrix p M X h i j) = (degree p)*h"
  unfolding row_of_coppersmith_matrix_def using dim_vector_vec_associated_to_int_poly_padded
  by blast

lemma dim_vector_form_basis_coppersmith_aux:
  fixes i:: "nat"
  assumes "i < (degree p)"
  shows "dim_vec ((form_basis_coppersmith_aux p M X h j) ! i) = (degree p)*h"
proof - 
  have " (map (\<lambda>i. row_of_coppersmith_matrix p M X h i j) [0..<degree p]) ! i
        = row_of_coppersmith_matrix p M X h i j"
    using assms by simp
  then show ?thesis
  unfolding form_basis_coppersmith_aux_def
  using dim_vector_row_of_coppersmith_matrix[of p M X h _ j] by presburger
qed

lemma length_form_basis_coppersmith_aux:
  shows "length (form_basis_coppersmith_aux p M X h j) = degree p"
  unfolding form_basis_coppersmith_aux_def by simp

lemma length_form_basis_coppersmith:
  fixes h:: "nat"
  assumes h_gt: "h > 0"
  shows "length (form_basis_coppersmith p M X h) = (degree p)*h"
proof - 
  let ?form_basis = "form_basis_coppersmith p M X h"
  have "length (concat (map (form_basis_coppersmith_aux p M X h) [0..<h])) =
  sum_list (map length (map (form_basis_coppersmith_aux p M X h) [0..<h]))"
    using length_concat[of "map (form_basis_coppersmith_aux p M X h) [0..<h]"]
    by blast
  then have "length (concat (map (form_basis_coppersmith_aux p M X h) [0..<h])) =
    sum_list (map (\<lambda>j. length (form_basis_coppersmith_aux p M X h j)) [0..<h])"
    by (smt (verit, ccfv_SIG) length_map nth_equalityI nth_map)
  then have "length (concat (map (form_basis_coppersmith_aux p M X h) [0..<h])) =
    sum_list (map (\<lambda>j. degree p) [0..<h])"
    using length_form_basis_coppersmith_aux by presburger
  then have len_is: "length (concat (map (form_basis_coppersmith_aux p M X h) [0..<h])) =
    (\<Sum>j\<leftarrow>[0..<h]. degree p)" by blast
  have "(\<Sum>j\<leftarrow>[0..<h]. degree p) = h*(degree p)"
    using h_gt proof (induct h)
    case 0
    then show ?case by blast
  next
    case (Suc h)
    {assume *: "h = 0"
      then have "(\<Sum>j\<leftarrow>[0..<Suc h]. degree p) = Suc h * degree p"
        by simp
    } moreover {assume *: "h > 0"
      then have "(\<Sum>j\<leftarrow>[0..< h]. degree p) = h * degree p"
        using Suc by blast
      then have "(\<Sum>j\<leftarrow>[0..<Suc h]. degree p) = Suc h * degree p"
        by simp
    }
    ultimately show ?case by fast
  qed
  then show ?thesis  using len_is 
    by (simp add: form_basis_coppersmith_def)
qed

lemma concat_property_helper:
  assumes "j < h"
  shows "concat (map (\<lambda>i. f i) [0..<h]) = concat (map (\<lambda>i. f i) [0..<j]) @ concat (map (\<lambda>i. f i) [j..<h])"
  using assms
  proof (induct j)
    case 0
    then show ?case by simp
  next
    case (Suc j)
    then show ?case 
      by (metis concat_append less_nat_zero_code map_append not_less_eq upt_append)
  qed

lemma concat_equal_lists_length:
  fixes f:: "nat \<Rightarrow> int vec list"
  fixes i j d:: "nat"
  assumes len_is: "\<And>i. i < h \<Longrightarrow> length (f i) = d"
  shows "length (concat (map (\<lambda>i. f i) [0..<h])) = d*h"
  using assms
proof (induct h)
  case 0
  then show ?case by auto
next
  case (Suc h)
  then have ind_h: "length (concat (map f [0..<h])) = d * h"
    by simp
  have concat_is: "concat (map f [0..<Suc h]) = concat (map f [0..<h]) @ concat (map f [h..<Suc h])"
    using concat_property_helper by blast
  have "concat (map f [h..<Suc h]) = f h"
    by auto
  then have "length (concat (map f [h..<Suc h])) = d"
    using Suc.prems by force
  then show ?case using ind_h concat_is 
    by simp
qed

lemma concat_property:
  fixes f:: "nat \<Rightarrow> int vec list"
  fixes i j d:: "nat"
  assumes "h > 0"
  assumes d_gt: "d > 0"
  assumes r_lt: "r < d*h"
  assumes len_is: "\<And>i. i < h \<Longrightarrow> length (f i) = d"
  assumes j_eq: "j = nat \<lfloor>real r / real d\<rfloor>"
  assumes i_eq: "i = r - d * j"
  shows "(concat (map (\<lambda>i. f i) [0..<h])) ! r = (f j) ! i"
  using assms nth_append 
proof - 
  have j_lt_h: "j < h"
    using r_lt j_eq 
    by (simp add: floor_divide_of_nat_eq less_mult_imp_div_less mult.commute)
  then have concat_is: "concat (map (\<lambda>i. f i) [0..<h]) = concat (map (\<lambda>i. f i) [0..<j]) @ concat (map (\<lambda>i. f i) [j..<h])"
    using concat_property_helper assms 
    by blast
  have len_is: "length (concat (map (\<lambda>i. f i) [0..<j])) = d*j"
    using len_is 
    by (meson \<open>j < h\<close> concat_equal_lists_length nat_SN.gt_trans)
  have "r \<ge> d*j"
    using i_eq 
    by (simp add: assms(5) floor_divide_of_nat_eq)
  then have "(concat (map (\<lambda>i. f i) [0..<j]) @ concat (map (\<lambda>i. f i) [j..<h])) ! r =
    concat (map (\<lambda>i. f i) [j..<h]) ! (r - d*j)"
    using nth_append len_is 
    by (metis leD)
  then have concat_r_1: "(concat (map (\<lambda>i. f i) [0..<h])) ! r  = concat (map (\<lambda>i. f i) [j..<h]) ! i"
    using concat_is assms(6) by presburger
  have concat_is_2: "concat (map (\<lambda>i. f i) [j..<h]) = (f j) @ concat (map (\<lambda>i. f i) [(j+1)..<h])"  
    by (metis Suc_eq_plus1 \<open>j < h\<close> concat.simps(2) list.map(2) upt_conv_Cons)
  have "r < d*(nat \<lfloor>real r / real d\<rfloor>) +  d"
    using d_gt 
    by (simp add: add.commute dividend_less_times_div floor_divide_of_nat_eq)
  then have "i < d"
    using i_eq j_eq 
    using \<open>d * j \<le> r\<close> by presburger
  then have "concat (map (\<lambda>i. f i) [j..<h]) ! i = (f j) ! i"
    using concat_is_2 len_is j_lt_h nth_append 
    by (metis assms(4))
  then show ?thesis 
    using concat_r_1 by metis
qed

lemma row_of: 
  assumes r_lt: "r < (degree p)*h"
  defines "d \<equiv> degree p"
  defines "j \<equiv> nat \<lfloor>real r / real d\<rfloor>"
  defines "i \<equiv> r - d * j"
  shows "(form_basis_coppersmith p M X h) ! r = 
    ((form_basis_coppersmith_aux p M X h j) ! i)"
  using r_lt j_def i_def concat_property length_form_basis_coppersmith_aux
  using assms(2) form_basis_coppersmith_def 
  by (smt (verit, best) less_imp_of_nat_less mult_0_right mult_cancel1 neq0_conv)

lemma dim_vector_form_basis_coppersmith:
  fixes i:: "nat"
  assumes "i < (degree p)*h"
  shows "dim_vec ((form_basis_coppersmith p M X h) ! i) = (degree p)*h" 
proof - 
  let ?j = "(nat \<lfloor>real i / real (degree p)\<rfloor>)"
  have "(form_basis_coppersmith p M X h) ! i = (form_basis_coppersmith_aux p M X h ?j) ! (i - (degree p) *?j)"
    using dim_vector_form_basis_coppersmith_aux
    using assms row_of by presburger
  then show ?thesis
    using dim_vector_form_basis_coppersmith_aux 
    by (metis assms bot_nat_0.not_eq_extremum floor_divide_of_nat_eq less_nat_zero_code mod_less_divisor modulo_nat_def mult.commute mult_0_right nat_int)
qed

subsubsection \<open> Equivalent Coppersmith matrix \<close>

definition form_coppersmith_matrix:: "int poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int mat"
  where "form_coppersmith_matrix p M X h  = mat ((degree p)*h) ((degree p)*h) 
      (\<lambda>(r, c). (let d = degree p; j = nat (floor (r/d)); i = (r - d*j) in (M^(h-1-j))*(coeff (p^j* (monom 1 i)) c)*X^c))"

lemma matrix_match: 
  assumes r_lt: "r < (degree p)*h"
  assumes c_lt: "c < (degree p)*h"
  assumes "h > 0"
  shows "(vec_list_to_square_mat (form_basis_coppersmith p M X h))$$(r, c) =  (form_coppersmith_matrix p M X h)$$(r, c)"
proof - 
  let ?d = "degree p"
  let ?j = "nat \<lfloor>real r / real ?d\<rfloor>"
  let ?i = "r - ?d * ?j"

  have i_lt: "?i < ?d"
    by (metis (no_types) Groups.mult_ac(2) assms(2) bot_nat_0.not_eq_extremum floor_divide_of_nat_eq less_nat_zero_code mod_less_divisor modulo_nat_def mult_0_right nat_int)
  have i_gt: "?i \<ge> 0"
    by blast
  have "?j \<ge> 0"
    by auto
  have "(form_basis_coppersmith p M X h) ! r = 
    ((form_basis_coppersmith_aux p M X h ?j) ! ?i)"
   using length_form_basis_coppersmith_aux length_form_basis_coppersmith r_lt
   row_of 
   by presburger
  then have eq: "vec_list_to_square_mat (form_basis_coppersmith p M X h) $$ (r, c) = 
  ((form_basis_coppersmith_aux p M X h ?j) ! ?i) $ c"
    using c_lt r_lt unfolding vec_list_to_square_mat_def 
    by (metis assms(3) length_form_basis_coppersmith mat_of_rows_index)
  have form_basis_elt: "((form_basis_coppersmith_aux p M X h ?j) ! ?i) $ c = (row_of_coppersmith_matrix p M X h ?i ?j) $ c"
    unfolding form_basis_coppersmith_aux_def 
    using i_lt i_gt 
    by simp
   have "(row_of_coppersmith_matrix p M X h ?i ?j) $ c = int M ^ (h - 1 - ?j) * poly.coeff (p ^ ?j * monom 1 ?i) c * int X ^ c"
     unfolding row_of_coppersmith_matrix_def vec_associated_to_int_poly_padded_def 
     using coeff_smult assms(2) index_vec semiring_1_class.of_nat_power by auto
  then have eq1: "((form_basis_coppersmith_aux p M X h ?j) ! ?i) $ c = int M ^ (h - 1 - ?j) * poly.coeff (p ^ ?j * monom 1 ?i) c * int X ^ c"
    using form_basis_elt by argo
  have eq2: "(form_coppersmith_matrix p M X h)$$(r, c) = int M ^ (h - 1 - ?j) * poly.coeff (p ^ ?j * monom 1 ?i) c * int X ^ c"
    by (metis (mono_tags, lifting) assms(1) assms(2) form_coppersmith_matrix_def index_mat(1) prod.simps(2))
  then show ?thesis using eq1 eq2 eq by auto
qed

subsubsection \<open> Lower triangular \<close>

lemma form_coppersmith_matrix_is_lower_triangular:
  fixes r c::"nat"
  assumes "h > 0"
  assumes r_lt: "r < c"
  assumes c_lt: "c < (degree p)*h"
  shows "(form_coppersmith_matrix p M X h)$$(r, c) = 0"
proof - 
  let ?d = "degree p"
  let ?j = "nat \<lfloor>real r / real ?d\<rfloor>"
  let ?i = "r - ?d * ?j"
  have i_lt: "?i < ?d"
    using Groups.mult_ac(2) assms(2) bot_nat_0.not_eq_extremum floor_divide_of_nat_eq less_nat_zero_code mod_less_divisor modulo_nat_def mult_0_right nat_int
    by (metis assms(3))
  have i_gt: "?i \<ge> 0"
    by blast
  have "?j \<ge> 0"
    by auto
  have entry_prop: "(form_coppersmith_matrix p M X h)$$(r, c) = (M^(h-1-?j))*(coeff (p^?j* (monom 1 ?i)) c)*X^c"
    unfolding form_coppersmith_matrix_def 
    by (metis (no_types, lifting) assms(2) assms(3) index_mat(1) less_imp_le_nat nat_SN.compat2 prod.simps(2) semiring_1_class.of_nat_power)
  have "degree (p^?j* (monom 1 ?i)) = ?d*?j + ?i"
    by (smt (z3) degree_power_eq degree_0 degree_monom_eq degree_mult_eq i_gt i_lt monom_hom.hom_0_iff nat_SN.compat2 rel_simps(70) semiring_1_no_zero_divisors_class.power_not_zero)
  then have "coeff (p^?j* (monom 1 ?i)) c = 0"
    using r_lt 
    by (metis (no_types, lifting) floor_divide_of_nat_eq leD le_add_diff_inverse le_degree nat_int thd)
  then show ?thesis using entry_prop by simp
qed

lemma form_coppersmith_basis_is_lower_triangular:
  fixes i j::"nat"
  assumes "h > 0"
  assumes i_lt: "i < j"
  assumes j_lt: "j < (degree p)*h"
  shows "(vec_list_to_square_mat (form_basis_coppersmith p M X h)) $$ (i,j) = 0"
  using matrix_match assms 
  by (metis (no_types, lifting) form_coppersmith_matrix_is_lower_triangular nat_SN.gt_trans)

subsubsection \<open> Distinct elements \<close>
lemma coppersmith_matrix_carrier_mat:
  assumes "h > 0"
  shows "vec_list_to_square_mat (form_basis_coppersmith p M X h) \<in> carrier_mat ((degree p)*h) ((degree p)*h)"
  using length_form_basis_coppersmith dim_vector_form_basis_coppersmith
  by (simp add: assms mat_of_rows_def vec_list_to_square_mat_def)

lemma no_zeros_on_diagonal_coppersmith:
  assumes "degree p \<ge> 1"
  assumes M_gt: "M > 0"
  assumes X_gt: "X > 0"
  assumes h_gt: "h > 0"
  shows "0 \<notin> set (diag_mat (vec_list_to_square_mat (form_basis_coppersmith p M X h)))"
proof - 
  let ?d = "degree p"
  have row_dim: "dim_row (vec_list_to_square_mat (form_basis_coppersmith p M X h)) = ?d*h"
    using coppersmith_matrix_carrier_mat assms by blast
  have "\<And> i::nat. i < ?d*h \<Longrightarrow> (vec_list_to_square_mat (form_basis_coppersmith p M X h))$$(i, i) \<noteq> 0"
  proof -
    fix i::"nat"
    assume *: "i < ?d*h"

    let ?d = "degree p"
    let ?j = "nat \<lfloor>real i / real ?d\<rfloor>"
    let ?i = "i - ?d * ?j"
    have coeff_is: "(form_coppersmith_matrix p M X h)$$(i, i) = (M^(h-1-?j))*(coeff (p^?j* (monom 1 ?i)) i)*X^i"
      unfolding form_coppersmith_matrix_def 
      by (metis (mono_tags, lifting) "*" index_mat(1) prod.simps(2) semiring_1_class.of_nat_power)
    have "degree (p^?j* (monom 1 ?i)) = ?i + ?j*?d"
      by (smt (verit, best) degree_power_eq assms(1) degree_0 degree_monom_eq degree_mult_eq less_numeral_extra(3) monom_hom.hom_0_iff mult.commute of_nat_0_less_iff of_nat_1 of_nat_le_iff semiring_1_no_zero_divisors_class.power_not_zero)
    also have "... = i"
      by (metis add.commute floor_divide_of_nat_eq le_add_diff_inverse mult.commute nat_int times_div_less_eq_dividend)
    finally have "coeff (p^?j* (monom 1 ?i)) i \<noteq> 0"
      by (smt (verit, del_insts) assms(1) degree_0 leading_coeff_neq_0 monom_hom.hom_0_iff mult_eq_0_iff not_one_le_zero semiring_1_no_zero_divisors_class.power_not_zero)
    then have "(form_coppersmith_matrix p M X h)$$(i, i) \<noteq> 0"
      using coeff_is M_gt X_gt 
      by (metis mult_eq_0_iff nat_0 nat_int semiring_norm(137) zero_less_power)
    then show "(vec_list_to_square_mat (form_basis_coppersmith p M X h))$$(i, i) \<noteq> 0"
      using matrix_match * h_gt by fastforce
  qed
  then show ?thesis
    unfolding diag_mat_def using row_dim
    by auto
qed                                                                        

lemma form_basis_coppersmith_distinct:
  fixes M X::"nat"
  assumes "1 \<le> degree p"
  assumes p_neq: "p \<noteq> 0"
  assumes M_gt: "M > 0"
  assumes X_gt: "X > 0"
  assumes h_gt: "h > 0"
  shows "distinct (form_basis_coppersmith p M X h)"
proof - 
  let ?M = "vec_list_to_square_mat (form_basis_coppersmith p M X h)"
  let ?dim = "degree p * h"
  have carrier_mat: "?M \<in> carrier_mat ?dim ?dim"
    using coppersmith_matrix_carrier_mat[OF h_gt] by auto
  have lower_triangular: "(\<And>i j. i < j \<Longrightarrow>
            j < degree p * h \<Longrightarrow>
            vec_list_to_square_mat (form_basis_coppersmith p M X h) $$ (i, j) =
            0)"
    using form_coppersmith_basis_is_lower_triangular[OF h_gt]
    by blast
  have zero_not_in: "0 \<notin> set (diag_mat
               (vec_list_to_square_mat
                 (form_basis_coppersmith p M X
                   h)))"
    using no_zeros_on_diagonal_coppersmith[OF assms(1) M_gt X_gt h_gt]  
    by blast
  have "rows (vec_list_to_square_mat (form_basis_coppersmith p M X h)) = form_basis_coppersmith p M X h"
    unfolding vec_list_to_square_mat_def using carrier_mat 
    by (metis carrier_vec_dim_vec dim_vector_form_basis_coppersmith h_gt in_set_conv_nth length_form_basis_coppersmith rows_mat_of_rows subset_code(1))
  then show ?thesis
  using lower_triangular_imp_distinct[OF carrier_mat lower_triangular zero_not_in] 
  by simp
qed

lemma matrix_row_form_basis_coppersmith:
  assumes "degree p \<ge> 1"
  assumes i_lt: "i < (degree p)*h"
  assumes "h > 0"
  shows "row (vec_list_to_square_mat (form_basis_coppersmith p M X h)) i = (form_basis_coppersmith p M X h) ! i"
  using length_form_basis_coppersmith[of h p M X]
  by (metis assms(2) assms(3) carrier_vec_dim_vec dim_vector_form_basis_coppersmith mat_of_rows_row vec_list_to_square_mat_def)

subsubsection \<open> Linear independence properties \<close>
lemma form_basis_coppersmith_lin_ind:
  assumes "M > 0"
  assumes "X > 0"
  assumes "degree p \<ge> 1"
  assumes "h > 0"
  shows "\<not> module.lin_dep class_ring (module_vec TYPE(int) ((degree p)*h))
        (set (form_basis_coppersmith p M X h))"
proof - 
  let ?M = "vec_list_to_square_mat (form_basis_coppersmith p M X h)"
  have no_zeros_on_diagonal: " 0 \<notin> set (diag_mat ?M)"
    using no_zeros_on_diagonal_coppersmith assms 
    by presburger
  have form_basis_distinct: "distinct (form_basis_coppersmith p M X ((degree p)*h))"
    using form_basis_coppersmith_distinct assms by fastforce
  have matrix_carrier: "?M \<in> carrier_mat ((degree p)*h) ((degree p)*h)"
    using assms(4) coppersmith_matrix_carrier_mat by blast
  have lower_triangular: "(\<And>i j. i < j \<Longrightarrow> j < ((degree p)*h) \<Longrightarrow> ?M $$ (i, j) = 0) "
    using form_coppersmith_basis_is_lower_triangular assms 
    by blast
  have "\<not> module.lin_dep class_ring (module_vec TYPE(int) ((degree p)*h)) (set (rows ?M))"
    using idom_vec.lower_triangular_imp_lin_indpt_rows[OF matrix_carrier lower_triangular]
      no_zeros_on_diagonal form_basis_distinct
    by blast
  then show ?thesis 
    using Suc_eq_plus1 assms(3)  length_rows matrix_row_form_basis_coppersmith nth_equalityI nth_rows plus_1_eq_Suc
    by (metis assms(4) carrier_matD(1) length_form_basis_coppersmith local.matrix_carrier)
qed

subsubsection \<open> Divisible by X property \<close>

lemma row_of_cs_matrix_div_by_Xpow:
  fixes M X i j h::"nat"
  assumes i_lt: "i < degree p"
  assumes j_lt: "j < h"
  assumes j_lt: "ja < h*(degree p)"
  shows "(row_of_coppersmith_matrix p M X h i j) $ ja mod (X ^ ja) = 0"
proof -
  let ?v = "row_of_coppersmith_matrix p M X h i j"
  have "ja < dim_vec ?v"
    unfolding row_of_coppersmith_matrix_def vec_associated_to_int_poly_padded_def
    using j_lt 
    by (simp add: mult.commute)
  then show ?thesis 
    unfolding row_of_coppersmith_matrix_def vec_associated_to_int_poly_padded_def
    by simp
qed

lemma form_basis_coppersmith_div_by_Xpow:
  fixes M X::"nat" 
  fixes a:: "int vec"
  assumes j_lt: "ja < h*(degree p)"
  assumes a_inset: "a \<in> set (form_basis_coppersmith p M X h)"
  shows " (a $ ja) mod (X ^ ja) = 0" 
proof - 
  have "\<exists>i j. i < degree p \<and> j < h \<and> a = row_of_coppersmith_matrix p M X h i j"
    using a_inset unfolding form_basis_coppersmith_def form_basis_coppersmith_aux_def
    by fastforce
  then show ?thesis
    using assms row_of_cs_matrix_div_by_Xpow 
    by blast
qed

subsubsection \<open> Zero mod M property \<close>

lemma row_of_cs_matrix_zero_mod_M:
  fixes M X i j h::"nat"
  assumes p_neq: "p \<noteq> 0"
  assumes M_gt: "M > 0"
  assumes X_gt: "X > 0"
  assumes h_gt1: "h > 1"
  assumes p_zero_mod_M: "poly p x0 mod M = 0"
  assumes deg_gt: "degree p > 1"
  assumes i_lt: "i < degree p"
  assumes j_lt: "j < h"
  shows "poly (int_poly_associated_to_vec (row_of_coppersmith_matrix p M X h i j) X) x0 mod M ^(h-1) = 0"
proof - 
  have ipos: "0 < 1/(real (degree p))"
    using deg_gt by auto

  have hj: "h - 1 = ((h - 1) - j) + j"
    using h_gt1 j_lt
    by auto
  let ?dim_vec = "(degree p * h)"
  let ?og_vec = "vec ?dim_vec (\<lambda>ja. poly.coeff (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i)) ja * int (X ^ ja))::int vec"
  let ?new_vec = "vec ?dim_vec (\<lambda>ja. poly.coeff (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i)) ja)"

  have lhs_eq: "\<lfloor>real_of_int (?og_vec $ ja) / real (X ^ ja)\<rfloor> = floor (((?og_vec $ ja)::real)/(X^ja))" if "ja < ?dim_vec" for ja::"nat"
    by simp
  have rhs_eq: "poly.coeff (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i)) ja = ?new_vec $ ja"
    if *: "ja < ?dim_vec" for ja::"nat"
    using * by auto
    have floor_div: "floor (((?og_vec $ ja)::real)/(X^ja)) = poly.coeff (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i)) ja"
    if "ja < ?dim_vec" for ja::"nat"
    by (metis (no_types, lifting) X_gt floor_divide_of_int_eq index_vec nat_neq_iff nonzero_mult_div_cancel_right of_int_of_nat_eq of_nat_eq_0_iff semiring_1_no_zero_divisors_class.power_not_zero that)
  then have floor_div_match: "\<lfloor>real_of_int (?og_vec $ ja) / real (X ^ ja)\<rfloor> = ?new_vec $ ja" if *: "ja < ?dim_vec" for ja::"nat"
    using lhs_eq rhs_eq * by presburger
  let ?og_vec_div = "vec (degree p * h)
            (\<lambda>ja. \<lfloor>real_of_int (?og_vec $ ja) / real (X ^ ja)\<rfloor>)"
  have same_vec: "?og_vec_div = ?new_vec" using floor_div_match by force

  have "int_poly_associated_to_vec ?og_vec X = (\<Sum>i<degree p * h.
           monom (?og_vec_div $ i) i)"
    unfolding int_poly_associated_to_vec_def by auto
  then have "int_poly_associated_to_vec ?og_vec X = (\<Sum>i<?dim_vec. monom (?new_vec $ i) i)"
    using same_vec by presburger

  then have poly_of_interest_is: "int_poly_associated_to_vec (row_of_coppersmith_matrix p M X h i j) X = 
    (\<Sum>i<?dim_vec. monom (?new_vec $ i) i)" 
    unfolding row_of_coppersmith_matrix_def vec_associated_to_int_poly_padded_def
    by auto

  have same_coeffs_lhs: "poly.coeff (\<Sum>i<?dim_vec. monom (?new_vec $ i) i) ia = ?new_vec $ ia"
    if *:"ia < ?dim_vec" for ia
    by (metis (no_types, lifting) "*" \<open>int_poly_associated_to_vec (vec (degree p * h) (\<lambda>ja. poly.coeff (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i)) ja * int (X ^ ja))) X = (\<Sum>ia<degree p * h. monom (vec (degree p * h) (poly.coeff (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i))) $ ia) ia)\<close> access_entry_in_int_poly_associated_to_vec dim_vec floor_div_match)
  have "?new_vec $ ia = poly.coeff (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i)) ia"
    if *:"ia < ?dim_vec" for ia
    using * by auto
  then have same_coeffs: "poly.coeff (\<Sum>i<?dim_vec. monom (?new_vec $ i) i) ia = 
    poly.coeff (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i)) ia"
    if *:"ia < ?dim_vec" for ia
    using same_coeffs_lhs "*" 
    by presburger
  have all_poly_eq: "\<And>p1 p2::int poly. \<And>d. degree p1 < d \<Longrightarrow> degree p2 < d \<Longrightarrow>
(\<And>i. i < d \<Longrightarrow> coeff p1 i = coeff p2 i) \<Longrightarrow> p1 = p2"
    by (metis coeff_eq_0 linorder_neqE_nat nat_SN.gt_trans poly_eqI)
  have deg_lt_1: "degree (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i)) < ?dim_vec"
    using i_lt ipos
    by (smt (verit, ccfv_threshold) Euclidean_Rings.div_eq_0_iff M_gt Nat.diff_cancel Polynomial.degree_power_eq add.right_neutral add_diff_cancel_left' add_diff_inverse_nat degree_monom_eq degree_mult_eq degree_smult_eq diff_add_inverse div_mult2_eq gr_implies_not0 j_lt j_lt less_nat_zero_code monom_eq_0_iff monom_hom.hom_0_iff msrevs(1) mult_eq_0_iff mult_is_0 of_int_of_nat_eq of_nat_0_less_iff of_nat_0_less_iff p_neq semiring_1_no_zero_divisors_class.power_not_zero zero_less_divide_1_iff zero_less_power)
  have poly_coeff_lt: "degree (monom (?new_vec $ i) i) < ?dim_vec"
    if *: "i < ?dim_vec" for i
    using * 
    by (metis bot_nat_0.not_eq_extremum degree_0 degree_monom_eq less_nat_zero_code monom_hom.hom_0_iff)
  have poly_degree_helper:"\<And> n. \<And>f::nat \<Rightarrow> int poly. (\<And>i. i < d \<Longrightarrow> degree (f i) < n) \<Longrightarrow> degree (\<Sum>i < d. (f i)) < n" if *: "d > 0" for d
    using *
  proof (induct d)
    case 0
    then show ?case by blast
  next
    case (Suc d)
    {assume *: "d = 0"
      then have "degree (sum f {..<Suc d}) < n"
        using Suc.prems by auto
    } moreover {assume *: "d > 0"
      then have "degree (sum f {..<d}) < n"
        using Suc by simp
      then have "degree (sum f {..<Suc d}) < n"
        using Suc 
        by (simp add: degree_add_less)
    }
    ultimately show ?case by blast
  qed
  have deg_lt_2: "degree (\<Sum>i<?dim_vec. monom (?new_vec $ i) i) < ?dim_vec"
    using deg_gt h_gt1 poly_degree_helper poly_coeff_lt 
    by force
  then have poly_of_interest_is2: "(\<Sum>i<?dim_vec. monom (?new_vec $ i) i) = (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i))"
    using all_poly_eq[OF deg_lt_1 deg_lt_2] same_coeffs 
    by (metis (no_types, lifting))
  have "poly.coeff (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i)) ja = 
    int (M ^ (h - 1 - j))*(poly.coeff (p ^ j * monom 1 i)) ja" if *: "ja < ?dim_vec" for ja::"nat"
    by auto
  have poly_is: "poly (p ^ j * monom 1 i) x0 = (poly p x0)^j*(poly (monom 1 i) x0)"
    by auto
  then have poly_is_2: "poly (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i)) x0
    = int (M ^ (h - 1 - j))*poly (p ^ j * monom 1 i) x0"
    by simp
  obtain k::"int" where "poly p x0 = k * M"
    using p_zero_mod_M
    by (metis mult.commute Divides.zmod_eq_0D)
  then have "poly (p ^ j * monom 1 i) x0 = M^j*(k)^j*(poly (monom 1 i) x0)"
    using poly_is
    by (simp add: power_mult_distrib) 
  then have j_gt_0_exk: "\<exists>k::int. poly (p ^ j * monom 1 i) x0 = M^j*k" if "j > 0"
    using that by auto
  {assume *: " j > 0"
    then have "\<exists>k::int. poly (p ^ j * monom 1 i) x0 = M^j*k"
      using j_gt_0_exk[OF *] by auto
    then obtain k::"int" where k_prop: "poly (p ^ j * monom 1 i) x0 = M^j*k"
      by blast
    have  "poly (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i)) x0 = 
    (int (M ^ (h - 1 - j))) *  M^j*k"
      using k_prop by auto
    also have  "... = (int (M^(h-1)))*k"
      using hj
      by (simp add: power_add)
    finally have "\<exists>k::int. poly (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i)) x0 = (M^(h-1))*k"
    by auto
  } moreover {assume *: "j = 0"
  then have "int (M ^ (h - 1 - j)) = int (M ^ (h -1))"
    by auto
  then have "\<exists>k::int. poly (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i)) x0 = (M^(h-1))*k"
    using poly_is_2 by auto
  }
  ultimately have "\<exists>k::int. poly (smult (int (M ^ (h - 1 - j))) (p ^ j * monom 1 i)) x0 = (M^(h-1))*k"
    by fast
 then show ?thesis 
   using poly_of_interest_is poly_of_interest_is2 by auto
qed

lemma form_basis_coppersmith_zero_mod_M:
  fixes M X::"nat"
  assumes p_neq: "p \<noteq> 0"
  assumes M_gt: "M > 0"
  assumes X_gt: "X > 0"
  assumes h_gt: "h > 1"
  assumes p_zero_mod_M: "poly p x0 mod M = 0"
  assumes a_inset: "a \<in> set (form_basis_coppersmith p M X h)"
  assumes deg_gt: "degree p > 1"
  shows "poly (int_poly_associated_to_vec a X) x0 mod M ^ (h - 1) = 0" 
proof - 
  have "\<exists>i j. i < degree p \<and> j < h \<and> a = row_of_coppersmith_matrix p M X h i j"
    using a_inset unfolding form_basis_coppersmith_def form_basis_coppersmith_aux_def
    by fastforce
  then show ?thesis
    using assms row_of_cs_matrix_zero_mod_M[OF p_neq M_gt X_gt h_gt p_zero_mod_M deg_gt] 
    by auto
qed

subsubsection \<open> Determinant of matrix \<close>

lemma determinant_bound_arithmetic_helper:
  fixes k:: "nat"
  shows "(\<Prod> j<(w+1). k^j) = sqrt (k^(w*(w+1)))"
proof (induct w)
  case 0
  then show ?case
    by simp
next
  case (Suc w)
  have "prod ((^) k) {..<Suc w + 1} = k^(w+1)*(prod ((^) k) {..< w + 1})"
    using Groups.mult_ac(2) by auto
  also have "... = k^(w+1)*sqrt (k ^ (w * (w + 1)))"
    by (metis Suc of_nat_mult)
  also have "... = sqrt ((k^(w+1))^2)*sqrt (k ^ (w * (w + 1)))"
    by (metis of_nat_0_le_iff pos2 real_root_pos2 semiring_1_class.of_nat_power sqrt_def)
  also have "... = sqrt ((k^(2*w+2)))*sqrt (k ^ (w * (w + 1)))"
    by (metis (no_types, opaque_lifting) Suc_eq_plus1 add.commute mult_Suc_right power_even_eq)
  also have "... = sqrt (k^((2*w+2)+(w * (w + 1))))"
    by (metis Num.of_nat_simps(5) power_add real_sqrt_mult)
  also have "... = sqrt (k^((2*w+2+w^2 + w)))"
    by (simp add: power2_eq_square)
  also have "... = sqrt (k^((w^2 + 3*w+2)))"
    by (smt (z3) eval_nat_numeral(3) more_arith_simps(11) mult_Suc power_add power_commuting_commutes)
  finally have "prod ((^) k) {..<Suc w + 1} = sqrt (k^((w+1)*(w+2)))"
    by (smt (verit, del_insts) Groups.mult_ac(2) Num.of_nat_simps(5) Rings.ring_distribs(2) \<open>prod ((^) k) {..<Suc w + 1} = k ^ (w + 1) * prod ((^) k) {..<w + 1}\<close> \<open>real (k ^ (w + 1) * prod ((^) k) {..<w + 1}) = real (k ^ (w + 1)) * sqrt (real (k ^ (w * (w + 1))))\<close> \<open>real (k ^ (w + 1)) * sqrt (real (k ^ (w * (w + 1)))) = sqrt (real ((k ^ (w + 1))\<^sup>2)) * sqrt (real (k ^ (w * (w + 1))))\<close> power_add power_even_eq real_sqrt_mult)
  then show ?case by auto
qed

lemma det_of_form_coppersmith_matrix:
  fixes M X:: "nat"
  assumes "M > 0"
  assumes "X > 0"
  assumes d_is: "d = degree p"
  assumes monic_poly: "coeff p d = 1"
  assumes h_gt: "h > 1"
  assumes deg_gt: "degree p > 1"
  shows "det (form_coppersmith_matrix p M X h) = 
    (root 2 (M^((h-1)*d*h))) *  (root 2 (X^((d*h-1)*d*h)))"
proof -
  let ?A = "form_coppersmith_matrix p M X h"
  have matrix_dims:"?A \<in> carrier_mat (d*h) (d*h)"
    unfolding form_coppersmith_matrix_def using d_is by auto
  then have det_eq: "det ?A = prod_list (diag_mat ?A)"
    using assms det_lower_triangular no_zeros_on_diagonal_helper form_coppersmith_matrix_is_lower_triangular
    by (smt (verit, del_insts) nat_SN.default_gt_zero nat_SN.gt_trans)
  have "j = nat (floor (k/d)) \<Longrightarrow> degree (p^j* (monom (1::int) (k - d*j))) = k" if k_lt: "k < d*h" for k j
  proof - 
    assume j_eq: "j = nat (floor (k/d))"
    have deg_lhs: "degree (p^j) = d*j"
      using d_is
      by (metis Missing_Polynomial.degree_power_eq deg_gt degree_0 not_one_less_zero) 
    have "k - d*j \<ge> 0"
      using j_eq by blast
    then have deg_rhs: "degree (monom (1::int) (k - d*j)) = k - d*j"
      by (simp add: degree_monom_eq)
    show "degree (p^j* (monom (1::int) (k - d*j))) = k"
      using deg_lhs deg_rhs 
      by (simp add: assms(3) degree_mult_eq floor_divide_of_nat_eq j_eq)
  qed
  then have leading_coeff_1: "j = nat (floor (k/d)) \<Longrightarrow> coeff (p^j* (monom (1::int) (k - d*j))) k = 1" if k_lt: "k < d*h" for k j
    using monic_poly 
    by (metis lead_coeff_monom assms(3) k_lt monic_mult monic_power)
  have all_elems_diag: "\<And>k. k < d*h \<Longrightarrow> (?A $$ (k, k)) = 
(let j = nat (floor (k/d)); i = (k - d*j) in (M^(h-1-j))*(coeff (p^j* (monom (1::int) i)) k)*X^k)"
    unfolding form_coppersmith_matrix_def using matrix_dims d_is 
    by (metis (no_types, lifting) index_mat(1) old.prod.case semiring_1_class.of_nat_power)
  then have diag_rewrite: "\<And>k. k < d*h \<Longrightarrow> (?A $$ (k, k)) = (M^(h-1-nat (floor (k/d))))*X^k"
    using leading_coeff_1 
    by simp
  have "prod_list (diag_mat ?A) = (\<Prod>k<d*h. ?A$$(k, k))"
    by (metis atLeast0LessThan carrier_matD(1) matrix_dims prod_list_diag_prod)
  then have prod_list_is: "prod_list (diag_mat ?A) = (\<Prod>k<d*h. (M^(h-1-nat (floor (k/d))))*X^k)"
    using diag_rewrite matrix_dims by simp
  have prod_split: "(\<Prod>k<d*h. (M^(h-1-nat (floor (k/d))))*X^k) = (\<Prod>k<d*h. (M^(h-1-nat (floor (k/d)))))* (\<Prod>k<d*h. X^k)"
    by (metis (no_types) prod.distrib)

  have lhs_prod: "(\<Prod>k<d*h. (M^(h-1-nat (floor (k/d))))) = (root 2 (M^((h-1)*d*h)))"
    using deg_gt d_is  h_gt
  proof (induct "d*h" arbitrary: h rule: less_induct)
    case less
    have prod_split1: "\<And>f. real (\<Prod>k<d * 2. f d) =
          real (\<Prod>k<d. f d) * real (\<Prod>k\<in>{d..<2*d}. f d)"
     using deg_gt 
     by (smt (verit, ccfv_SIG) atLeast0LessThan le_add_same_cancel1 mult_2 mult_2_right of_nat_mult prod.atLeastLessThan_concat zero_order(1))
      {assume *: "h = 2"
      have prod_is: "real (\<Prod>k<d * 2. M ^ (2 - 1 - nat \<lfloor>real k / real d\<rfloor>)) =
        real (\<Prod>k<d. M ^ (2 - 1 - nat \<lfloor>real k / real d\<rfloor>)) * real (\<Prod>k\<in>{d..<2*d}. M ^ (2 - 1 - nat \<lfloor>real k / real d\<rfloor>))"
        using prod_split1 
        by (smt (verit) le_add2 lessThan_atLeast0 mult.commute mult_2_right of_nat_mult prod.atLeastLessThan_concat zero_order(1))
      have "\<And>k. k<d \<Longrightarrow> nat \<lfloor>real k / real d\<rfloor> = 0"
        by auto
      then have h1: "real (\<Prod>k<d. M ^ (2 - 1 - nat \<lfloor>real k / real d\<rfloor>)) = (M ^ (d*(2 - 1)))"
        by simp

      have "\<And>k. k\<in>{d..<2*d} \<Longrightarrow> nat \<lfloor>real k / real d\<rfloor> = 1"
        by (simp add: floor_divide_of_nat_eq nat_div_eq_Suc_0_iff)
      then have h2: "real (\<Prod>k\<in>{d..<2*d}. M ^ (2 - 1 - nat \<lfloor>real k / real d\<rfloor>)) = real  M ^ (d*(2 - 1 - 1))"
        by auto
      have "real (\<Prod>k<d * 2. M ^ (2 - 1 - nat \<lfloor>real k / real d\<rfloor>)) = real  M ^ (d*(2 - 1 - 1)) * real (M ^ (d*(2 - 1)))"
        using h1 h2 prod_is by simp
      also have "... =
        root 2 (real (M ^ ((2 - 1) * d * 2)))"
        using Groups.mult_ac(3) Suc_1 Suc_eq_plus1 add_diff_cancel_left' of_nat_0_le_iff pos2 power_0 power_mult real_root_pos2 semiring_1_class.of_nat_power verit_minus_simplify(1) verit_prod_simplify(2)
        by (smt (verit, ccfv_threshold) h1 h2 of_nat_mult prod_is)
      finally have "real (\<Prod>k<d * h. M ^ (h - 1 - nat \<lfloor>real k / real d\<rfloor>)) =
    root 2 (real (M ^ ((h - 1) * d * h)))"
        using * by auto
    } moreover {assume *: "h > 2"
      have prod_split: "real (\<Prod>k<d * h. M ^ (h - 1 - nat \<lfloor>real k / real d\<rfloor>)) =
        real (\<Prod>k<d*(h-1). M ^ (h - 1 - nat \<lfloor>real k / real d\<rfloor>)) * real (\<Prod>k\<in>{d*(h-1)..<d * h}. M ^ (h - 1 - nat \<lfloor>real k / real d\<rfloor>))"
        by (smt (verit) Num.of_nat_simps(5) atLeast0LessThan diff_le_self mult.commute mult_less_cancel1 prod.atLeastLessThan_concat verit_comp_simplify1(3) zero_order(1))
      have ind_dec: "(d * (h - 1)) < d * h"
        using less.prems by simp
      have ind_still: "1 < h - 1" using * by auto
      have h1_aux: "real (\<Prod>k<d * (h-1). M ^ ((h-1) - 1 - nat \<lfloor>real k / real d\<rfloor>)) =
               root 2 (real (M ^ (((h-1) - 1) * d * (h-1))))"
        using less.hyps[OF ind_dec less.prems(1) less.prems(2) ind_still] 
        by blast
      have "2*d*(h-1)+((h-1) - 1) * d * (h-1) = d * (h-1)*((h-1)-1+2)"
        by simp
      then have arith_helper: "2*d*(h-1)+((h-1) - 1) * d * (h-1) = d * (h-1)*(h)"
        by (metis Suc_1 Suc_diff_Suc Suc_eq_plus1 add_Suc_right diff_diff_left le_add_diff_inverse less_imp_le_nat local.less(4) plus_1_eq_Suc)
      have gteq: "(h-1) - 1 - nat \<lfloor>real k / real d\<rfloor> \<ge> 0" if k_is: "k<d * (h-1)" for k
      proof - 
        have "k/d <d * (h-1)/d"
          using k_is less.prems(1-2) 
          by (metis divide_strict_right_mono ind_dec less_imp_of_nat_less nat_mult_less_cancel_disj of_nat_0_less_iff)
        then show ?thesis by blast
      qed
      have sum_pow: "b \<ge> 0 \<Longrightarrow> c \<ge> 0 \<Longrightarrow> M ^ (b + c) = M^b * M^c" for b c
        using power_add by blast
      then have "M ^ ((h-1)- nat \<lfloor>real k / real d\<rfloor>) = M* M ^ ((h-1) - 1 - nat \<lfloor>real k / real d\<rfloor>)" if k_is: "k<d * (h-1)" for k
      proof - 
        have "(h-1)- nat \<lfloor>real k / real d\<rfloor> = 1 + (h-1)- 1 -nat \<lfloor>real k / real d\<rfloor>"
          using gteq by auto
        then have "M ^ ((h-1)- nat \<lfloor>real k / real d\<rfloor>)  = M^(1 + (h-1)- 1 -nat \<lfloor>real k / real d\<rfloor>)"
          by argo
        then show ?thesis using gteq sum_pow[of "1" "(h - 1) - 1 - nat \<lfloor>real k / real d\<rfloor>"]
          by (metis (no_types, opaque_lifting) Groups.mult_ac(2) diff_commute div_le_dividend floor_divide_of_nat_eq k_is le_add_diff_inverse less_irrefl_nat less_mult_imp_div_less nat_int nonzero_mult_div_cancel_right power_one_right verit_prod_simplify(1) zero_less_diff zero_order(1))
      qed
      then have "real (\<Prod>k<d * (h-1). M ^ ((h-1)- nat \<lfloor>real k / real d\<rfloor>)) = 
      real (\<Prod>k<d * (h-1). M* M ^ ((h-1) - 1 - nat \<lfloor>real k / real d\<rfloor>))"
        by simp
      moreover have "... = real (\<Prod>k<d * (h-1). M)*real (\<Prod>k<d * (h-1). M ^ ((h-1) - 1 - nat \<lfloor>real k / real d\<rfloor>))"
        by auto
      moreover have "... =
               M^(d*(h-1))*root 2 (real (M ^ (((h-1) - 1) * d * (h-1))))"
        by (metis card_lessThan h1_aux prod_constant)
      moreover have "... =
        root 2 M^(2*d*(h-1))*root 2 (real (M ^ (((h-1) - 1) * d * (h-1))))"
        by (simp add:  power_mult)
      moreover have "... = root 2 (real M^(2*d*(h-1))*(M ^ (((h-1) - 1) * d * (h-1))))"
        using pos2 real_root_mult real_root_power by presburger
      moreover have "... = root 2 (real (M ^ ( 2*d*(h-1)+((h-1) - 1) * d * (h-1))))"
        by (simp add: power_add)
      moreover have "... = root 2 (real (M ^ ((h - 1) * d * h)))"
        using arith_helper 
        by (metis Groups.mult_ac(2))
      ultimately have h1: "real (\<Prod>k<d * (h-1). M ^ ((h-1)- nat \<lfloor>real k / real d\<rfloor>))  = root 2 (real (M ^ ((h - 1) * d * h)))"
        by argo
      have "nat \<lfloor>real k / real d\<rfloor> = h-1" if k_in: "k\<in>{d*(h-1)..<d * h}" for k
      proof -
        have "k \<ge> d*(h-1)"
          using k_in by auto
        then have "real k / d \<ge> real (d*(h-1))/d"
          using less.prems(1-2) 
          by (smt (verit, del_insts) frac_le ind_dec linordered_nonzero_semiring_class.of_nat_mono mult_less_cancel1 of_nat_0_le_iff of_nat_0_less_iff)
        then have b1: "real k / real d \<ge> h -1"
          using ind_dec by auto
        have "k < d*h"
          using k_in by auto
        then have "real k / d < real (d*h)/d"
          using less.prems(1-2) 
          by (metis divide_strict_right_mono ind_dec less_imp_of_nat_less mult_less_cancel1 of_nat_0_less_iff)
        then have b2: "real k / real d < h"
          using less.prems 
          by simp
        show ?thesis using b1 b2 
          by (simp add: floor_eq4)
      qed
      then have h2: "real (\<Prod>k\<in>{d*(h-1)..<d * h}. M ^ (h - 1 - nat \<lfloor>real k / real d\<rfloor>)) = 1"
        by simp
      then have "real (\<Prod>k<d * h. M ^ (h - 1 - nat \<lfloor>real k / real d\<rfloor>)) =
        real (\<Prod>k<d * (h - 1). M ^ (h - 1 - nat \<lfloor>real k / real d\<rfloor>))"
        using prod_split 
        by (smt (verit, del_insts) div_by_1 nonzero_mult_div_cancel_right)
      then have "real (\<Prod>k<d * h. M ^ (h - 1 - nat \<lfloor>real k / real d\<rfloor>)) =
         root 2 (real (M ^ ((h - 1) * d * h)))"
        using h1 
        by presburger
    }
    ultimately show ?case using less.prems(3) 
      by linarith
  qed

  have dh_gt_1: "d * h > 1"
    using deg_gt h_gt 
    by (metis One_nat_def assms(3) less_1_mult)
  let ?k = "d*h - 1"
  have rhs_prod: "(\<Prod>k<d*h. X^k) = root 2 (X^((d*h-1)*d*h))"
    using dh_gt_1 determinant_bound_arithmetic_helper[of X ?k] 
    by (metis (no_types, lifting) Groups.add_ac(2) le_add_diff_inverse less_imp_le_nat more_arith_simps(11) sqrt_def)
  have "(\<Prod>k<d*h. (M^(h-1-nat (floor (k/d))))*X^k) = (root 2 (M^((h-1)*d*h))) *  (root 2 (X^((d*h-1)*d*h)))"
    using prod_split lhs_prod rhs_prod 
    by simp
  then show ?thesis 
    using prod_list_is det_eq
    by linarith
qed

lemma det_of_matrix:
  fixes M X:: "nat"
  assumes "M > 0"
  assumes "X > 0"
  assumes "d > 1"
  assumes d_is: "d = degree p"
  assumes monic_poly: "coeff p d = 1"
  assumes h_gt: "h > 1"
  shows "det (vec_list_to_square_mat (form_basis_coppersmith p M X h)) = 
    (root 2 (M^((h-1)*d*h))) *  (root 2 (X^((d*h-1)*d*h)))"
proof - 
 have dims_1: "vec_list_to_square_mat (form_basis_coppersmith p M X h) \<in> carrier_mat (d*h) (d*h)"
    using h_gt dim_vector_form_basis_coppersmith length_form_basis_coppersmith 
    using assms(4) coppersmith_matrix_carrier_mat by simp
  have dims_2: "form_coppersmith_matrix p M X h \<in> carrier_mat (d*h) (d*h)" 
    unfolding form_coppersmith_matrix_def using d_is by auto
  have "\<And>r c. r < degree p * h \<Longrightarrow>
    c < degree p * h \<Longrightarrow>
    vec_list_to_square_mat (form_basis_coppersmith p M X h) $$ (r, c) =
    form_coppersmith_matrix p M X h $$ (r, c)"
    using h_gt matrix_match[of _ p h _ M X] by blast
  then have "vec_list_to_square_mat (form_basis_coppersmith p M X h) = form_coppersmith_matrix p M X h"
     using dims_1 dims_2 d_is by auto
  then show ?thesis
    using det_of_form_coppersmith_matrix assms
    by metis
qed

subsection \<open> Top-level proof \<close>

definition root_bound:: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real"
  where "root_bound M d eps = 1/2*(M powr (1/d - eps))"

subsubsection \<open> Arithmetic \<close>

lemma epsilon_bounded_below:
  assumes "d > 0"
  assumes "eps > 0"
  assumes "d*h-1 > 0"
  assumes "d = degree p"
  assumes "h = calculate_h_coppersmith p eps"
  shows "eps \<ge> (d-1)/(d*(d*h-1))"
proof - 
  have "h \<ge> ((d-1)/(d*(eps)) + 1)/d"
    using assms unfolding calculate_h_coppersmith_def calculate_h_coppersmith_aux_def
    by (smt (verit, ccfv_SIG) Num.of_nat_simps(2) One_nat_def divide_less_cancel nat_less_real_le of_nat_0_less_iff of_nat_add of_nat_ceiling of_nat_diff of_nat_le_iff of_nat_less_0_iff plus_1_eq_Suc)
  then have "d*h \<ge> ((d-1)/(d*(eps)) + 1)"
    using assms 
    by (metis Groups.mult_ac(2) Num.of_nat_simps(5) less_divide_eq of_nat_0_less_iff verit_comp_simplify1(3))
  then have "d*h - 1\<ge> (d-1)/(d*(eps))"
    using assms 
    by linarith
  then have "(d*h-1)*d*(eps) \<ge> d-1"
    using assms(1-2)
    by (simp add: divide_le_eq)
  then show ?thesis
    using assms 
    by (metis Groups.mult_ac(2) divide_le_eq mult_sign_intros(5) of_nat_0_less_iff)
qed

lemma z_arith:
  assumes x: "(x::real) \<ge> 0"
  shows "x / (1 + x) \<le> ln (1 + x)"
proof -
  define g where "g = (\<lambda>z::real.  ln (1 + z) - z / 1 + z)"
  define g' where "g' = (\<lambda>z::real. 1 / (1 + z))"
  have gz: "g 0 \<ge> 0"
    unfolding g_def by auto
  have 1: "z \<in> {0..x} \<Longrightarrow> (g has_real_derivative (g' z)) (at z)" for z
    unfolding g_def g'_def
    by (auto intro!: derivative_eq_intros DERIV_powr)
  have 2: "g' z \<ge> 0" if z:"z \<in> {0..x}" for z
    unfolding g'_def
    using z by auto
  have "g 0 \<le> g x"
    by (intro deriv_nonneg_imp_mono[OF 1 2 x]) 
  thus ?thesis using gz unfolding g_def
    by (smt (verit, ccfv_SIG) assms divide_minus_left ln_diff_le)
qed

lemma powr_divide_both:
  assumes "(a::real) \<ge> 0" "x > 0" "b powr y \<ge> 1"
  assumes le: "a powr x \<ge> b powr y"
  shows "a \<ge> b powr (y / x)"
proof -
  have "0 \<le> 1/x" using assms by auto
  from powr_mono_both[OF this _ assms(3) le, of "1 / x"]
  show ?thesis
    using assms by (auto simp add:powr_powr)
qed
  
lemma coppersmith_arithmetic_convergence_1:
  fixes y:: "real"
  assumes y: "y \<ge> 1 / 0.18"
  shows "0 \<le> 1.414 - (1 + y) powr (1 / y) "
proof -
  define g where "g = (\<lambda>z::real.  1.414 - (1 + z) powr (1 / z))"

  define g' where "g' = (\<lambda>z::real. -((1 + z) powr (1 / z) *
       (1 / (z * (1 + z)) - ln (1 + z) / (z * z))))"

  have a:"(1414 / 10 ^ 3) powr 50 \<ge>  ((1 + 1 / (18 / 10\<^sup>2))::real) powr 9"
    by (auto simp add: field_simps)
  have "(1414 / 10 ^ 3) \<ge>  ((1 + 1 / (18 / 10\<^sup>2))::real) powr (9 / 50)"
    apply(intro powr_divide_both[OF _ _ _ a])
    by auto
  then have gz: "g (1 / 0.18) \<ge> 0"
    unfolding g_def by auto

  have 1: "z \<in> {1 / (18 / 10\<^sup>2)..y} \<Longrightarrow> (g has_real_derivative (g' z)) (at z)" for z
    unfolding g_def g'_def
    by (auto intro!: derivative_eq_intros DERIV_powr)
  have 2: "g' z \<ge> 0" if z:"z \<in> {1 / (18 / 10\<^sup>2)..y}" for z
  proof -
    have zpos: "z > 0" using z by auto
    have 1: "(1 + z) powr (1 / z) \<ge> 0"
      by simp
    have "z / (1 + z) \<le> ln (1 + z)" using z_arith zpos by auto
    then have 2: "(1 / (z * (1 + z)) - ln (1 + z) / (z * z)) \<le> 0"
      apply (simp add: field_simps zpos)
      by (metis (no_types, opaque_lifting) distrib_left ge_refl more_arith_simps(6) nonzero_divide_mult_cancel_left not_less times_divide_eq_right zpos)
    have "(1 + z) powr (1 / z) * (1 / (z * (1 + z)) - ln (1 + z) / (z * z)) \<le> 0"
      using 1 2 mult_nonneg_nonpos 
      by blast 
    then show ?thesis
      unfolding g'_def
      by auto
  qed
  have "g (1 / 0.18) \<le> g y"
    by (intro deriv_nonneg_imp_mono[OF 1 2 y])
  thus ?thesis using gz unfolding g_def by auto
qed

lemma coppersmith_arithmetic_convergence:
  fixes x:: "real"
  assumes x: "0 < x" "x \<le> 0.18"
  shows "(1 + (1/x)) powr (x) \<le> sqrt 2"
proof -
  have "1 / x \<ge> 1 / 0.18"
    using x by (auto simp add: le_divide_eq_numeral(1))
  from coppersmith_arithmetic_convergence_1[OF this]
  have 1: " (1 + 1 / x) powr (1 / (1 / x)) \<le> 1.414"
    using x by auto

  have "707 powr 2 \<le> (sqrt 2 * 500) powr 2"
    by (auto simp add: field_simps)
  from powr_divide_both[OF _ _ _ this]
  have "707 \<le> sqrt 2 * 500"
    by auto

  thus ?thesis
    using assms 1 by auto
qed

subsubsection \<open> Main results \<close>

lemma coppersmith_finds_small_roots:
  fixes p f:: "int poly"
  fixes M X:: "nat"
  fixes x0:: "int"
  fixes eps::"real"
  assumes zero_mod_M: "poly p x0 mod M = 0"
  assumes d_is: "d = degree p"
  assumes d_gt: "d > 1"
  assumes monic_poly: "coeff p d = 1"
  assumes X_lt: "X < root_bound M d eps"
  assumes M_gt: "M > 0"
  assumes X_gt_zero: "X > 0"
  assumes x0_le: "abs x0 \<le> X"
  assumes eps_le: "eps \<le> 0.18*(d-1)/d"
  assumes eps_lt: "eps < 1/(real (degree p))"
  assumes eps_gt: "eps > 0"
  assumes f_is: "f = coppersmith p M X eps"
  shows "poly f x0 = 0"
proof -
  define h where "h = calculate_h_coppersmith p eps"
  let ?cs_basis = "form_basis_coppersmith p M X h"

  have h_gt_0: "h > 0"
    unfolding h_def
    using calculate_h_coppersmith_aux_gteq1 assms unfolding calculate_h_coppersmith_def 
    by fastforce

  then have dh_gt_0: "d*h > 0"
    unfolding h_def
    using d_gt by auto

  have h_gt: "h > 1"
    unfolding h_def
    using One_nat_def eps_gt d_is d_gt calculate_h_coppersmith_aux_gt1 calculate_h_coppersmith_def eps_lt one_less_nat_eq
    by presburger

  have dim_form_basis: "length ?cs_basis = d*h"
    using length_form_basis_coppersmith[of h p M X] d_is d_gt h_gt
    using h_def by blast

  have li1: "set (map of_int_vec ?cs_basis) \<subseteq> carrier_vec (d  * h)"
    apply clarsimp
    by (metis assms(2) carrier_vec_dim_vec dim_vector_form_basis_coppersmith in_set_conv_nth local.dim_form_basis)

  have dist: "distinct ?cs_basis"
    using h_def
    by (smt (verit, ccfv_SIG) X_gt_zero assms(2) assms(3) assms(4) assms(6) form_basis_coppersmith_distinct h_gt leading_coeff_0_iff less_imp_le_nat nat_SN.gt_trans zero_less_one_class.zero_less_one)
  then have li2: "distinct ((map of_int_vec ?cs_basis)::rat vec list)"
    using casted_distinct_is_distinct by blast

  have form_basis_lin_ind: "\<not> module.lin_dep class_ring (module_vec TYPE(int) (d*h))
        (set (form_basis_coppersmith p M X h))"
    using assms form_basis_coppersmith_lin_ind h_gt_0
    by simp

  then have li3:"module.lin_indpt class_ring
        (module_vec TYPE(rat) (d * h))
        (set (map of_int_vec (?cs_basis)))"
    using h_def
    by (metis dist assms(2) casting_lin_comb_helper dim_vector_form_basis_coppersmith distinct_Ex1 local.dim_form_basis)

  from form_basis_coppersmith_zero_mod_M[OF _ M_gt X_gt_zero h_gt zero_mod_M]
  have 2: "\<And>a. a \<in> set ?cs_basis \<Longrightarrow> poly (int_poly_associated_to_vec a X) x0 mod M ^ (h - 1) = 0"
    using h_def
    by (metis d_is d_gt degree_0 semiring_norm(136))

  have pmod: "poly (p ^ (h - 1)) x0 mod (M ^ (h - 1)) = 0"
  proof -
    from zero_mod_M
    obtain k where "poly p x0 = k *int  M"
      by fastforce
    then have "(poly p x0) ^ (h - 1) = (k *int  M)^(h-1)" by auto
    moreover have "... = (k^(h-1) *  (M^(h-1)))"
      by (simp add: power_mult_distrib)
    ultimately show ?thesis
      by auto
  qed

  have 1: "(\<And>v j. v \<in> set ?cs_basis \<Longrightarrow>
            j < d * h \<Longrightarrow> v $ j mod X ^ j = 0)"
    using form_basis_coppersmith_div_by_Xpow h_def
    by (metis Groups.mult_ac(2) assms(2))

  have "real_of_int
   (det (vec_list_to_square_mat ?cs_basis)) =
    root 2 ((M ^ ((h - 1) * d * h))) *
    root 2 (real (X ^ ((d * h - 1) * d * h)))" (is "?lhs = ?rhs")
    apply (subst det_of_matrix[OF M_gt X_gt_zero d_gt d_is monic_poly h_gt])
    by auto
  then have "(?lhs)^2 = (?rhs)^2"
    by auto
  then have drw: "(det (mat_of_rows (d * h) ?cs_basis))\<^sup>2 =
    M ^ ((h - 1) * d * h) * X ^ ((d * h - 1) * d * h)"
    apply (clarsimp simp add: field_simps)
    by (smt (verit, del_insts) local.dim_form_basis of_int_eq_iff of_int_mult of_int_of_nat_eq of_int_power vec_list_to_square_mat_def)

  let ?cdh = "root (d*h - 1) (d*h)*(root 2 2)"

  let ?x = "1/real(d*h-1)"
  have x_inv: "1/?x = d*h -1"
    by simp
  have "eps*d \<le> (0.18*(d-1)/d)*d"
    using d_gt eps_le
    by (metis le_simps(1) of_nat_0_le_iff of_nat_1 of_nat_diff times_left_mono) 
  then have "1/((d-1)/(d*eps) - 1 + 1) \<le> 0.18"
    using d_gt by (auto simp add: field_simps)
  then have helper_ineq:"1/(d*((d-1)/(d*eps) + 1)/d - 1) \<le> 0.18"
    using d_gt by auto
  have "h = \<lceil>((real d - 1) / (real d * eps) + 1) / real d\<rceil>"
    unfolding h_def calculate_h_coppersmith_def calculate_h_coppersmith_aux_def 
    using d_is
    by (metis calculate_h_coppersmith_aux_def calculate_h_coppersmith_def h_def h_gt_0 nat_eq_iff nat_neq_iff) 
  then have h_gteq_helper: "h \<ge> ((d-1)/(d*eps) + 1)/d"
    by (metis (no_types, opaque_lifting) Num.of_nat_simps(2) d_gt le_simps(1) nat_eq_iff2 of_nat_0_le_iff of_nat_diff real_nat_ceiling_ge)
  then have "d*h \<ge> d*((d-1)/(d*eps) + 1)/d"
    using d_gt h_gt 
    by (simp add: Groups.mult_ac(2) divide_le_eq)
  then have h_gteq_helper2: "d*h - 1 \<ge> d*((d-1)/(d*eps) + 1)/d -1"
    by linarith

  have inequality_helper:"a / b > a" if *: "a > 0 \<and> b > 0 \<and> b < 1" for a b :: "real"
    using * 
    using frac_less2 by fastforce
  have "d*eps < 1"
    using eps_lt d_is d_gt
    by (auto simp add: field_simps)
  then have "(d-1)/(d*eps) > d-1"
    using d_gt eps_gt inequality_helper[of "d-1" "d*eps"] by auto
  then have gteq: "d*((d-1)/(d*eps) + 1)/d - 1 > 0"
    using d_gt 
    by (auto simp add: field_simps)
  have "1/(d*h - 1) \<le> 0.18"
    using h_gteq_helper2 gteq helper_ineq 
    by (smt (verit, ccfv_SIG) frac_le)
  then have "?x \<le> 0.18" by blast
  then have "(1 + (1/?x)) powr (?x) \<le> sqrt 2"
    using coppersmith_arithmetic_convergence
    by (smt (verit, best) gteq h_gteq_helper2 zero_compare_simps(7))
  then have "(d*h) powr (1/(d*h - 1)::real) \<le> sqrt 2"
    using x_inv 
    apply (clarsimp simp add: field_simps)
    by (metis Num.of_nat_simps(3) Num.of_nat_simps(5) Suc_pred' dh_gt_0 numeral_nat(7))
  then have "root (d*h - 1) (d*h) \<le> sqrt 2"
    using root_powr_inverse
    using pos2 real_root_gt_0_iff  zero_less_diff
    by (metis d_gt dh_gt_0 h_gt less_1_mult of_nat_0_less_iff)

  then have "root (d*h - 1) (d*h)*(root 2 2) \<le> sqrt 2 *(root 2 2)"
    by simp
  then have "?cdh \<le> 2"
    using sqrt_def by auto
  then have "root (d*h - 1) (d*h)*(root 2 2)* X \<le> 2*X"
    using X_gt_zero by simp
  then have "
    root (d*h - 1) (d*h)*(root 2 2)* X < M powr (1/d - eps)"
    using X_lt unfolding root_bound_def by simp
  then have arith: "
    (root (d*h - 1) (d*h)*(root 2 2)* X) ^ (d * h * (d*h - 1)) <
    (M powr (1/d - eps))  ^ (d * h * (d*h - 1)) "
    by (smt (verit, del_insts) d_gt dh_gt_0 h_gt less_1_mult linordered_semidom_class.power_strict_mono mult_nonneg_nonneg nat_0_less_mult_iff of_nat_0_le_iff real_root_ge_zero zero_less_diff)
  have "2 ^ (d * h *  (d * h - 1) div 2) *
    X ^ ((d * h - 1) * d * h)  * (d * h) ^ (d * h)
    <  (M ^ ((h - 1)  *  (d * h)))"
  proof -
    have "root (d*h - 1) (d*h) ^ (d * h * (d*h - 1))
      = (root (d*h - 1) (d*h) ^ (d*h - 1)) ^ (d * h)"
      using power_mult
      by (metis Groups.mult_ac(2))
    also have "... = (d * h) ^ (d * h)"
      apply (subst real_root_pow_pos2)
      using gteq h_gteq_helper2 apply linarith
      by auto
    finally have *: "root (d*h - 1) (d*h) ^ (d * h * (d*h - 1)) = (d * h) ^ (d * h)" .

    have **: "root 2 2 ^ (d * h * (d*h - 1))
      =  2 ^ (d * h * (d*h - 1) div 2)"
      by (smt (verit, del_insts) Suc_pred' dh_gt_0 even_Suc even_mult_iff real_sqrt_power_even sqrt_def)

    have eps_bounded_below:"eps \<ge> (d-1)/(d*(d*h-1))"
      using epsilon_bounded_below h_gt d_gt d_is
      by (metis eps_gt bot_nat_0.not_eq_extremum div_by_0 h_def less_eq_real_def nat_0_less_mult_iff semiring_1_class.of_nat_0) 

    then have "(1/d - eps) * (d*h - 1)\<le> h - 1"
      using d_gt apply (clarsimp simp add: field_simps)
      by (smt (verit) One_nat_def diff_mult_distrib2 divide_le_eq h_gt less_or_eq_imp_le mult_le_mono2 mult_sign_intros(5) nat_mult_1_right of_nat_diff of_nat_less_iff of_nat_mult semiring_1_class.of_nat_0 zero_less_one_class.zero_less_one)
    then have "(d * h) * ((1/d - eps) * (d*h - 1)) \<le> (d * h) * (h - 1)"
      by (simp add: mult_left_mono)
    then have "(1/d - eps) * (d * h * (d*h - 1)) \<le> ((h - 1)  *  (d * h))"
      by (auto simp add: field_simps)
    then have "M powr ((1/d - eps) * (d * h * (d*h - 1))) \<le> M powr ((h - 1)  *  (d * h))"
      using M_gt powr_mono by auto
    then have ***: "(M powr (1/d - eps)) ^ (d * h * (d*h - 1)) \<le> (M ^ ((h - 1)  *  (d * h)))"
      by (metis M_gt of_nat_0_less_iff of_nat_power_eq_of_nat_cancel_iff powr_gt_zero powr_powr powr_realpow)
    show ?thesis
      using arith * ** ***
      apply (simp add: power_mult_distrib)
      by (smt (verit) Groups.mult_ac(2) Num.of_nat_simps(2) Num.of_nat_simps(4) Num.of_nat_simps(5) more_arith_simps(11) of_nat_power_less_of_nat_cancel_iff one_add_one semiring_1_class.of_nat_power)
  qed
  then have "(2 ^ (d * h *  (d * h - 1) div 2) *
    X ^ ((d * h - 1) * d * h)  *
    (d * h) ^ (d * h)) *
    M ^ ((h - 1) * d * h)
    <  (M ^ ((h - 1) * (d * h))) *
    M ^ ((h - 1) * d * h)"
    using M_gt
    by (clarsimp simp add: field_simps)
  then have "2 ^ (d * h *  (d * h - 1) div 2) *
    M ^ ((h - 1) * d * h) *
    X ^ ((d * h - 1) * d * h)  *
    (d * h) ^ (d * h)
    <  (M ^ (h - 1)) ^ (2 * (d * h))"
    by (smt (verit, del_insts) Groups.mult_ac(2) Groups.mult_ac(3) numeral_nat(7) power2_eq_square power_mult power_mult_distrib)
  then have 3: "real_of_rat 2 ^ (d * h * (d * h - 1) div  2) *
    real_of_int ((det (mat_of_rows (d * h) ?cs_basis))\<^sup>2) *
    real (d * h) ^ (d * h)
    < ((M ^ (h - 1)) ^ (2 * (d * h)))"
    unfolding drw
    by (smt (verit, del_insts) Groups.mult_ac(2) Groups.mult_ac(3) Num.of_nat_simps(5) more_arith_simps(11) of_int_of_nat_eq of_nat_numeral of_nat_power_less_of_nat_cancel_iff of_rat_of_int_eq power_mult semiring_1_class.of_nat_power)

  interpret lll: LLL_with_assms
    "d * h" "d * h" "?cs_basis" "2"
    apply unfold_locales
    subgoal by auto
    subgoal
      unfolding cof_vec_space.lin_indpt_list_def
      using li1 li2 li3 by auto
    using dim_form_basis by auto

  interpret lll: coppersmith_assms
    "d * h" "d * h" "?cs_basis"
    "2" x0 "M^(h - 1)" X "p ^ (h - 1)"
    apply unfold_locales
    subgoal using M_gt by auto
    subgoal using X_gt_zero  by auto
    subgoal using dh_gt_0 by auto
    subgoal using pmod by auto
    subgoal using x0_le by auto
    subgoal
      by (metis d_gt bot_nat_0.extremum_strict h_gt local.dim_form_basis mult_eq_0_iff)
    subgoal using 1 by auto
    using 2 by auto

  
  have *: "lll.short_vector = short_vector 2 ?cs_basis"
    using lll.short_vector_impl by presburger

  from lll.root_poly_short_vector
  show ?thesis
    using lll.bnd_raw_imp_short_vec_bound 3 lll.square_Gramian_determinant_eq_det_square
    unfolding f_is coppersmith_def first_vector_coppersmith_def Let_def *
    using h_def by fastforce
qed

theorem coppersmith_finds_small_roots_pretty:
  fixes p f:: "int poly"
  fixes M X:: "nat"
  fixes x0:: "int"
  fixes eps:: "real"
  defines "d \<equiv> degree p"
  defines "f \<equiv> coppersmith p M X eps"
  assumes monic_poly: "monic p"
  assumes "d > 1" and "M > 0" and "X > 0"
  assumes zero_mod_M: "poly p x0 mod M = 0"
  assumes X_lt: "X < root_bound M d eps"
  assumes x0_le: "abs x0 \<le> X"
  assumes eps_le: "eps \<le> 0.18 * (d-1)/d"
  assumes eps_lt: "eps < 1 / d"
  assumes eps_gt0: "eps > 0"
  shows "poly f x0 = 0"
  using assms coppersmith_finds_small_roots 
  by presburger

end