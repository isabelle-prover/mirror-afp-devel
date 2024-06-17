section \<open> Proof of Lightweight Algorithm \<close>

text \<open> We start by proving the "lightweight algorithm" as a
  stepping stone to the full algorithm (proved in Coppersmith.thy). \<close>

theory Towards_Coppersmith

imports Coppersmith_Generic
begin

subsection \<open> Basic properties \<close>

lemma dim_form_basis_helper:
  shows "length (form_basis_helper p M X d) = d + 1"
  unfolding form_basis_helper_def 
  by auto

lemma dim_form_basis:
  shows "length (form_basis p M X d) = d + 2"
  using dim_form_basis_helper form_basis_def by simp

subsection \<open> Matrix properties \<close>

subsubsection \<open> Basic properties and preliminaries \<close>

lemma dim_row_basis_mat:
  assumes "degree p \<ge> 1"
  shows "dim_row (vec_list_to_square_mat (form_basis p M X (degree p - 1))) = degree p + 1"
proof - 
  have "length (form_basis p M X (degree p - 1)) = degree p + 1"
    using assms dim_form_basis[of p M X "degree p - 1"] 
    by auto 
  then show ?thesis
    unfolding vec_list_to_square_mat_def mat_of_rows_list_def by auto
qed

lemma dim_col_basis_mat:
  assumes "degree p \<ge> 1"
  shows"dim_col (vec_list_to_square_mat (form_basis p M X (degree p - 1))) = (degree p + 1)"
proof - 
  have "length (form_basis p M X (degree p - 1)) = degree p + 1"
    using assms dim_form_basis[of p M X "degree p - 1"] 
    by auto 
  then show ?thesis unfolding vec_list_to_square_mat_def
    by auto
qed

lemma matrix_carrier:
  assumes "degree p \<ge> 1"
  assumes "i < degree p + 1"
  shows "vec_list_to_square_mat (form_basis p M X (degree p - 1)) \<in> carrier_mat (degree p + 1) (degree p + 1)"
  using dim_row_basis_mat[of p M X] dim_col_basis_mat[of p M X] assms 
  by auto

lemma vector_sum_monom:
  fixes v:: "int vec"
  fixes d i:: "nat"
  assumes "d = dim_vec v"
  assumes "d > 0"
  assumes i_lt: "i < d"
  assumes zero_monom: "\<And>j::nat. j < d \<Longrightarrow> j \<noteq> i \<Longrightarrow> monom (v $ j) j = 0"
  shows "(\<Sum>i< d. monom (v $ i) i) = monom (v $ i) i"
proof - 
  have "(\<Sum>i< d.  monom (v $ i) i) = (\<Sum>i\<in>{0..<d}.  monom (v $ i) i)"
    using atLeast_upt set_upt by presburger
  then have sum_split: "(\<Sum>i< d.  monom (v $ i) i) = (\<Sum>i\<in>{0..<d}-{i}.  monom (v $ i) i) +  monom (v $ i) i"
    using i_lt 
    by (metis (no_types, lifting) Groups.add_ac(2) atLeast0LessThan finite_lessThan lessThan_iff sum.remove)
  have "\<And>j::nat. j \<in> {0..<d}-{i} \<Longrightarrow> monom (v $ j) j = 0"
    using zero_monom i_lt by simp
  then have "(\<Sum>i\<in>{0..<d}-{i}.  monom (v $ i) i) = (\<Sum>i\<in>{0..<d}-{i}. 0)"
    by (simp add: sum.neutral)
  then show ?thesis using sum_split by simp
qed

lemma int_poly_associated_to_g_i_vec:
  assumes X_gt: "X > 0"
  assumes M_gt: "M > 0"
  assumes i_lt: "i \<le> (degree p)"
  shows "int_poly_associated_to_vec (g_i_vec M X i (degree p + 1)) X = monom M i"
proof - 
  let ?gi = "g_i_vec M X i (degree p + 1)"
  let ?d = "degree p"
  let ?newvec = "vec (dim_vec (g_i_vec M X i (degree p + 1)))
            (\<lambda>j. \<lfloor>real_of_int (g_i_vec M X i (degree p + 1) $ j) / real (X ^ j)\<rfloor>)"
  have dim_vec_gi: "dim_vec ?gi = degree p + 1"
    unfolding g_i_vec_def by simp
  then have dim_vec_newvec: "dim_vec ?newvec = ?d + 1"
    by simp
  then have newvec_j: "\<And>j. j < ?d+1 \<Longrightarrow> j \<noteq> i \<Longrightarrow> ?newvec $ j = 0"
    unfolding g_i_vec_def by simp
  then have monom_zero: "\<And>j. j < ?d+1 \<Longrightarrow> j \<noteq> i \<Longrightarrow> monom (?newvec $ j) j = 0"
    by blast
  have poly_monom_sum: "(\<Sum>i< ?d+1.
           monom (?newvec $ i) i) = monom (?newvec $ i) i"
    using vector_sum_monom[of "?d+1" ?newvec i] dim_vec_newvec monom_zero assms(3)
    by simp
  have newvec_i: "?newvec $ i = M"
    using X_gt M_gt i_lt dim_vec_newvec unfolding g_i_vec_def by simp
  then have monom_i: "monom M i = monom (?newvec $ i) i"
    by auto
  show ?thesis
    using monom_i poly_monom_sum dim_vec_newvec
    unfolding int_poly_associated_to_vec_def by auto
qed

lemma ith_row_form_basis:
  shows "i \<le> d \<Longrightarrow> ((form_basis p M X d)!i) = (form_basis_helper p M X d)!i"
        "((form_basis p M X d)!(d+1)) = vec_associated_to_int_poly p X"
  using dim_form_basis_helper[of p M X d] form_basis_def
   apply (simp add: append_Cons_nth_left)
  using dim_form_basis_helper[of p M X d] form_basis_def
  by (simp add: append_Cons_nth(1) append_Cons_nth_left)

lemma set_form_basis:
  shows "x\<in> set (form_basis p M X (degree p - 1)) \<Longrightarrow> x = vec_associated_to_int_poly p X \<or>
  x \<in> set (form_basis_helper p M X (degree p - 1))"
  using ith_row_form_basis ith_row_form_basis_helper dim_form_basis
    form_basis_def
  by simp 

lemma dim_vector_in_basis:
  fixes i:: "nat"
  assumes "i < d + 2"
  shows "dim_vec ((form_basis p M X d) ! i) = (degree p+1)"
proof -
  let ?vec = "(form_basis p M X d) ! i"
  have eo: "List.member (form_basis_helper p M X d) ?vec \<or> ?vec = vec_associated_to_int_poly p X"
    using assms  
    by (metis List.member_def add_Suc_right dim_form_basis_helper form_basis_def less_Suc_eq nat_1_add_1 nth_append nth_append_length nth_mem plus_1_eq_Suc) 
  have len_helper: "length (form_basis_helper p M X d) = d + 1"
    using dim_form_basis form_basis_def by simp
  have h1: "\<And>x. List.member (form_basis_helper p M X d) x \<Longrightarrow> dim_vec x = degree p + 1"
  proof - 
    fix x 
    assume "List.member (form_basis_helper p M X d) x"
    then have "\<exists>k. x = g_i_vec M X k (degree p + 1)"
      using ith_row_form_basis_helper
      by (metis List.member_def dim_form_basis_helper in_set_conv_nth le_simps(2) semiring_norm(174)) 
    then show "dim_vec x = degree p + 1"
      using assms unfolding g_i_vec_def by auto
  qed 
  have h2: "dim_vec (vec_associated_to_int_poly p X) = degree p + 1"
    using assms dim_vec_vec_associated_to_poly
    by auto
  show ?thesis
    using h1 h2 eo by auto 
qed


subsubsection \<open> Properties of matrix associated to input \<close>

lemma matrix_row_form_basis_carrier:
  assumes "degree p \<ge> 1"
  assumes "i < degree p + 1"
  shows "form_basis p M X (degree p - 1) ! i \<in> carrier_vec (degree p + 1)"
proof - 
  show ?thesis
    using assms  dim_vector_in_basis[of i " degree p - 1" p M X]
    unfolding carrier_vec_def by auto 
qed

lemma matrix_row_form_basis:
  assumes "degree p \<ge> 1"
  assumes i_lt: "i < degree p + 1"
  shows "row (vec_list_to_square_mat (form_basis p M X (degree p - 1))) i = (form_basis p M X (degree p - 1)) ! i"
  using dim_form_basis[of p M X "degree p - 1"]
  by (metis add_Suc_right arith_special(3) assms(1) assms(2) le_add_diff_inverse mat_of_rows_row matrix_row_form_basis_carrier plus_1_eq_Suc semiring_norm(174) vec_list_to_square_mat_def)

lemma matrix_diagonal_element:
  assumes "degree p \<ge> 1"
  assumes "i < degree p"
  shows "vec_list_to_square_mat
                             (form_basis p M X (degree p - 1)) $$
                            (i, i) = ((form_basis p M X (degree p - 1)) ! i)$i"
  using assms 
  by (metis dim_col_basis_mat dim_row_basis_mat index_row(1) less_Suc_eq matrix_row_form_basis semiring_norm(174))

lemma no_zeros_on_diagonal:
  assumes "degree p \<ge> 1"
  assumes "M > 0"
  assumes "X > 0"
  shows "0 \<notin> set (diag_mat (vec_list_to_square_mat (form_basis p M X (degree p - 1))))"
proof - 
  have eval_elt: "\<And>i. i < degree p + 1 \<Longrightarrow> vec_list_to_square_mat (form_basis p M X (degree p - 1)) $$ (i, i) 
  = ((form_basis p M X (degree p - 1))!i)$i"
  proof - 
    fix i
    assume "i < degree p + 1"
    then show "vec_list_to_square_mat (form_basis p M X (degree p - 1)) $$ (i, i) 
  = ((form_basis p M X (degree p - 1))!i)$i"
      using assms dim_form_basis dim_row_basis_mat dim_vector_in_basis index_row(1)
      by (metis dim_col_basis_mat matrix_row_form_basis)
  qed
  have "\<And>i. i < degree p + 1 \<Longrightarrow> 
    ((form_basis p M X (degree p - 1))!i)$i \<noteq> 0"
  proof - 
    fix i
    assume i_lt: "i < degree p + 1"
    {assume *: "i < degree p"
      then have "((form_basis p M X (degree p - 1))!i) = (form_basis_helper p M X (degree p - 1))!i"
        by (metis add_2_eq_Suc' add_diff_cancel_left' assms(1) dim_form_basis form_basis_def length_append_singleton nth_append ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
      then have "((form_basis p M X (degree p - 1))!i)$i \<noteq> 0"
        using no_zeros_on_diagonal_helper assms "*" 
        by (metis bot_nat_0.not_eq_extremum mult_eq_0_iff of_nat_eq_0_iff power_eq_0_iff)
    }
    moreover {assume *: "i = degree p"
      then have eq: "((form_basis p M X (degree p - 1))!i) = vec_associated_to_int_poly p X"
        by (metis assms(1) dim_form_basis_helper form_basis_def nth_append_length ordered_cancel_comm_monoid_diff_class.diff_add)
      have "coeff p (degree p) \<noteq> 0"
        using assms(1) by force
      then have "((form_basis p M X (degree p - 1))!i)$i \<noteq> 0"
        using * eq assms unfolding vec_associated_to_poly_def
        by auto
    }
    ultimately show "((form_basis p M X (degree p - 1))!i)$i \<noteq> 0"
      using i_lt  
      by linarith
  qed
  then have imp_false: "(\<exists>i < degree p + 1. 
    (vec_list_to_square_mat (form_basis p M X (degree p - 1)) $$ (i, i))
     = 0) \<Longrightarrow> False"
    by (metis eval_elt)
  then have "0 \<in> set (map (\<lambda>i. vec_list_to_square_mat
                        (form_basis p M X (degree p - 1)) $$
                       (i, i)) [0..< degree p + 1]) \<Longrightarrow> False"
  proof - 
    assume "0 \<in> set (map (\<lambda>i. vec_list_to_square_mat
                        (form_basis p M X (degree p - 1)) $$
                       (i, i)) [0..< degree p + 1])"
    then have "\<exists>(i::nat) <  degree p + 1. vec_list_to_square_mat
                        (form_basis p M X (degree p - 1)) $$
                       (i, i) = 0"
      using less_SucI less_Suc_eq 
      by auto
    then show "False" using imp_false 
      by auto
  qed
  then show ?thesis
    unfolding diag_mat_def
    using dim_row_basis_mat assms
    by auto 
qed

lemma form_basis_helper_is_lower_triangular:
  fixes i j:: "nat"
  assumes "i < j"
  assumes "j < (degree p + 1)"
  shows "((form_basis_helper p M X (degree p - 1))!i)$j = 0"
proof - 
  have "(form_basis_helper p M X (degree p - 1))!i = g_i_vec M X i (degree p + 1)"
    using ith_row_form_basis_helper assms 
    by (smt (verit, best) Suc_diff_Suc diff_is_0_eq le_add_diff_inverse nat_SN.gt_trans nat_le_linear nat_less_le plus_1_eq_Suc semiring_norm(174))
  then show ?thesis unfolding g_i_vec_def using assms
    by force
qed

lemma form_basis_is_lower_triangular:
  fixes i j::"nat"
  assumes i_lt: "i < j"
  assumes j_lt: "j < (degree p + 1)"
  shows "(vec_list_to_square_mat (form_basis p M X (degree p - 1))) $$ (i,j) = 0"
proof - 
  let ?M = "vec_list_to_square_mat (form_basis p M X (degree p - 1))"
  have M_elt: "?M $$ (i, j) = ((form_basis p M X (degree p - 1))!i)$j"
    by (smt (verit) Suc_eq_plus1 Suc_pred assms(1) assms(2) dim_col_basis_mat dim_row_basis_mat index_row(1) le_add1 less_Suc0 matrix_row_form_basis nat_SN.gt_trans nat_neq_iff plus_1_eq_Suc)
  {assume *: "i < degree p"
    then have "(form_basis p M X (degree p - 1))!i = (form_basis_helper p M X (degree p - 1))!i"
      by (simp add: form_basis_def dim_form_basis_helper nth_append)
    then have "((form_basis p M X (degree p - 1))!i)$j = ((form_basis_helper p M X (degree p - 1))!i)$j"
      by auto
    then have "((form_basis p M X (degree p - 1))!i)$j = 0"
      using form_basis_helper_is_lower_triangular[OF i_lt j_lt] assms * 
      by auto
  } moreover {
    assume *: "i = degree p"
    have " (form_basis p M X (degree p - 1))!i = vec_associated_to_int_poly p X"
      using "*" assms(1) assms(2) by linarith
    then have "((form_basis p M X (degree p - 1))!i)$j = 0"
      using assms 
      by (metis "*" Suc_eq_plus1 not_less_eq)
  }
  ultimately have "((form_basis p M X (degree p - 1))!i)$j = 0"
    using assms(1) assms(2) by linarith
  then show ?thesis using M_elt 
    by auto 
qed





lemma form_basis_distinct:
  assumes "degree p \<ge> 1"
  assumes "M > 0"
  assumes "X > 0"
  shows "distinct (form_basis p M X (degree p - 1))"
proof - 
  let ?M = "vec_list_to_square_mat (form_basis p M X (degree p - 1))"
  let ?dim = "degree p + 1"
  have rows_eq: "rows ?M = form_basis p M X (degree p - 1)"
    by (smt (verit, best) assms(1) dim_row_basis_mat in_set_conv_nth mat_of_rows_carrier(2) matrix_row_form_basis_carrier rows_mat_of_rows subset_code(1) vec_list_to_square_mat_def)
  have in_set:"?M \<in> carrier_mat ?dim ?dim"
    using dim_row_basis_mat[of p M X] dim_col_basis_mat[of p M X] assms  
    unfolding carrier_mat_def by auto
  show ?thesis
    using lower_triangular_imp_distinct[OF in_set] form_basis_is_lower_triangular no_zeros_on_diagonal assms rows_eq 
    by auto
qed

lemma det_of_matrix:
  fixes M X:: "nat"
  assumes "M > 0"
  assumes "X > 0"
  assumes "degree p \<ge> 1"
  assumes d_is: "d = degree p"
  assumes n_is: "n = (\<Sum>i\<le>d. i)"
  assumes monic_poly: "coeff p d = 1"
  shows "det (vec_list_to_square_mat (form_basis p M X (degree p - 1))) =
    M^(degree p)*X^n"
proof - 
  let ?A = "vec_list_to_square_mat (form_basis p M X (degree p - 1))"
  have in_set:"?A \<in> carrier_mat (d+1) (d+1)"
    using d_is dim_row_basis_mat[of p M X] dim_col_basis_mat[of p M X] assms  
    unfolding carrier_mat_def 
    by auto
  then have "det ?A = prod_list (diag_mat ?A)"
    using det_lower_triangular no_zeros_on_diagonal_helper form_basis_is_lower_triangular
      assms 
    by metis
  have all_elems_diag: "\<And>i. i < d + 1 \<Longrightarrow> (?A $$ (i, i)) = ((form_basis p M X (degree p - 1)) ! i)$i"
    by (metis assms(3) assms(4) carrier_matD(2) in_set list_of_vec_index list_of_vec_row_nth matrix_row_form_basis)
  have last_elem: "((form_basis p M X (d - 1)) ! (d))$(d) = ((vec_associated_to_int_poly p X) $ (d))"
    using dim_form_basis_helper[of p M X "d-1"]  ith_row_form_basis(2)[of p M X "d-1"]  d_is
    by (metis Nat.le_imp_diff_is_add assms(3)) 
  have "(\<Prod>i<d+1. (((form_basis p M X (d - 1)) ! i)$i)) = (\<Prod>i<d. (((form_basis p M X (d - 1)) ! i)$i))*(((form_basis p M X (d - 1)) ! d)$d)"
    by auto
  then have prod_is: "(\<Prod>i<d+1. (((form_basis p M X (d - 1)) ! i)$i)) = (\<Prod>i<d. (((form_basis p M X (d - 1)) ! i)$i))*((vec_associated_to_int_poly p X) $ (d))"
    using last_elem by auto
  have "prod_list (diag_mat ?A) = (\<Prod>i<d+1. (?A $$ (i, i)))"
    unfolding diag_mat_def using dim_row_basis_mat[of p M X] assms(3) d_is
    by (metis (no_types, lifting) atLeast_upt distinct_upt prod.distinct_set_conv_list) 
  then have eq1: "prod_list (diag_mat ?A) = (\<Prod>i<d+1. (((form_basis p M X (d - 1)) ! i)$i))"
    using all_elems_diag d_is by auto
  have sub_prod_is: "(\<Prod>i<d. ((((form_basis p M X (d-1)))! i)$i)) = (\<Prod>i<d. ((((form_basis_helper p M X (d-1)))! i)$i))"
    using ith_row_form_basis(1) by auto
  have "prod_list (diag_mat ?A) = (\<Prod>i<d. ((((form_basis p M X (d-1)))! i)$i)) * ((vec_associated_to_int_poly p X) $ (d))"
    using  HOL.trans[OF eq1 prod_is] by auto
  then have prod_list_is: "prod_list (diag_mat ?A) = (\<Prod>i<d. ((((form_basis_helper p M X (d-1)))! i)$i)) * ((vec_associated_to_int_poly p X) $ (d))"
    using sub_prod_is by auto
  have prod_two: "(vec_associated_to_int_poly p X) $ (d) = X^d"
    unfolding vec_associated_to_poly_def 
    using d_is monic_poly by auto
  have same_prod: "(\<Prod>i<d. ((form_basis_helper p M X (d-1))! i)$i) =  (\<Prod>i<d. (g_i_vec M X i (degree p + 1))$i)"
    using ith_row_form_basis_helper by auto 
  have "\<And>k. k \<le> degree p \<Longrightarrow> (\<Prod>i<k. (g_i_vec M X i (degree p + 1))$i) = M^k*X^(\<Sum>i<k. i)"
  proof -
    fix k 
    assume "k \<le> degree p"
    then show "(\<Prod>i<k. (g_i_vec M X i (degree p + 1))$i) = M^k*X^(\<Sum>i<k. i)"
    proof (induct k)
      case 0
      then show ?case unfolding g_i_vec_def by auto 
    next
      case (Suc d)
      have "(\<Prod>i<Suc d. g_i_vec M X i (degree p + 1) $ i) = (\<Prod>i<d. g_i_vec M X i (degree p + 1) $ i)*g_i_vec M X (d) (degree p + 1) $ (d)"
        by auto 
      then have h1: "(\<Prod>i<Suc d. g_i_vec M X i (degree p + 1) $ i) = (M ^ d * X ^ \<Sum> {..<d})*g_i_vec M X (d) (degree p + 1) $ (d)"
        using Suc by auto
      have h2: "g_i_vec M X (d) (degree p + 1) $ (d) = M*X^d "
        using Suc(2) unfolding g_i_vec_def by auto 
      show ?case
        using h1 h2 
        by (simp add: mult.left_commute power_add)
    qed
  qed
  then have "(\<Prod>i<d. (g_i_vec M X i (degree p + 1))$i) = M^d*X^(\<Sum>i<d. i)"
    using d_is by auto
  then have prod_one: "(\<Prod>i<d. ((form_basis_helper p M X (d-1))! i)$i) = M^d*X^(\<Sum>i<d. i)"
    using same_prod 
    by auto 
  have n_is_alt: "n = (\<Sum>i<d. i) + d"
    using n_is 
    by (metis lessThan_Suc_atMost sum.lessThan_Suc)
  have "prod_list (diag_mat ?A) = M^d*X^(\<Sum>i<d. i)*X^d"
    using prod_one prod_two prod_list_is by auto
  then have "prod_list (diag_mat ?A) = M^d*X^((\<Sum>i<d. i) + d)"
    by (simp add: power_add)
  then have det_prod: "prod_list (diag_mat ?A) = M^(degree p)*X^n"
    using n_is d_is n_is_alt by auto
  have "det ?A = prod_list (diag_mat ?A)"
    using prod_list_is form_basis_is_lower_triangular det_lower_triangular
    using \<open>det (vec_list_to_square_mat (form_basis p M X (degree p - 1))) = prod_list (diag_mat (vec_list_to_square_mat (form_basis p M X (degree p - 1))))\<close> by force 
  then show ?thesis
    using det_prod by auto
qed

subsubsection \<open> Properties of casted matrix \<close>

lemma dim_row_basis_of_int_mat:
  assumes "degree p \<ge> 1"
  shows "dim_row (vec_list_to_square_mat (map of_int_vec (form_basis p M X (degree p - 1)))) = degree p + 1"
proof -
  have "length (form_basis p M X (degree p - 1)) = degree p + 1"
    using assms dim_form_basis[of p M X "degree p - 1"] 
    by auto 
  then show ?thesis 
    by (simp add: vec_list_to_square_mat_def)
qed

lemma dim_col_basis_of_int_mat:
  assumes "degree p \<ge> 1"
  shows"dim_col (vec_list_to_square_mat (map of_int_vec (form_basis p M X (degree p - 1)))) = (degree p + 1)"
proof - 
  have "length (form_basis p M X (degree p - 1)) = degree p + 1"
    using assms dim_form_basis[of p M X "degree p - 1"] 
    by auto 
  then show ?thesis unfolding vec_list_to_square_mat_def
    by auto
qed

lemma of_int_matrix_row_form_basis_carrier:
  assumes "degree p \<ge> 1"
  assumes "i < degree p + 1"
  shows "(map of_int_vec (form_basis p M X (degree p - 1))) ! i \<in> carrier_vec (degree p + 1)"
  using matrix_row_form_basis_carrier assms 
  by (metis (no_types, lifting) Suc_eq_plus1 add_Suc_right arith_special(3) dim_form_basis map_carrier_vec nth_map ordered_cancel_comm_monoid_diff_class.diff_add)

lemma of_int_matrix_carrier:
  assumes "degree p \<ge> 1"
  assumes "i < degree p + 1"
  shows "vec_list_to_square_mat (map of_int_vec (form_basis p M X (degree p - 1))) \<in> carrier_mat (degree p + 1) (degree p + 1)"
  using dim_row_basis_of_int_mat[of p M X] dim_col_basis_of_int_mat[of p M X] assms 
  by auto

lemma of_int_matrix_row_form_basis:
  assumes "degree p \<ge> 1"
  assumes i_lt: "i < degree p + 1"
  shows "row (vec_list_to_square_mat (map of_int_vec (form_basis p M X (degree p - 1)))) i = (map of_int_vec (form_basis p M X (degree p - 1))) ! i"
proof - 
  let ?vs = "form_basis p M X (degree p - 1)"
  have cv: "map of_int_vec (form_basis p M X (degree p - 1)) ! i
    \<in> carrier_vec (degree p + 1)" using matrix_row_form_basis_carrier[of p i M X]
    using of_int_matrix_row_form_basis_carrier[of p i M X] assms  by auto
  have i_lt_len: "i < length (map of_int_vec (form_basis p M X (degree p - 1)))"
    using i_lt dim_form_basis[of p M X "degree p - 1"]
    by auto 
  show ?thesis
    unfolding vec_list_to_square_mat_def using mat_of_rows_row[OF i_lt_len cv]
      dim_form_basis[of p M X "degree p - 1"]
    using assms(1) by auto
qed

lemma of_int_matrix_row_form_basis_var:
  assumes "degree p \<ge> 1"
  assumes i_lt: "i < degree p + 1"
  shows "row (vec_list_to_square_mat (map of_int_vec (form_basis p M X (degree p - 1)))) i = of_int_vec ((form_basis p M X (degree p - 1)) ! i)"
  using of_int_matrix_row_form_basis assms
  by (metis add_2_eq_Suc' dim_form_basis le_add_diff_inverse nth_map plus_1_eq_Suc semiring_norm(174)) 

lemma of_int_mat_element:
  fixes i j::"nat"
  assumes "degree p \<ge> 1"
  assumes "i < (degree p + 1)"
  assumes "j < (degree p + 1)"
  shows "(vec_list_to_square_mat (map of_int_vec (form_basis p M X (degree p - 1)))) $$ (i,j) = 
    of_int ((vec_list_to_square_mat (form_basis p M X (degree p - 1))) $$ (i,j))"
proof -
  let ?M1 = "vec_list_to_square_mat (form_basis p M X (degree p - 1))"
  let ?M2 = "vec_list_to_square_mat (map of_int_vec (form_basis p M X (degree p - 1)))"
  have "?M1 $$ (i, j) = (row ?M1 i) $ j"
    using assms 
    by (metis dim_col_basis_mat dim_row_basis_mat index_row(1))
  then have row1: "?M1 $$ (i, j) = ((form_basis p M X (degree p - 1)) ! i)$j"
    using assms(1) assms(2) matrix_row_form_basis by presburger
  have  "?M2 $$ (i, j) = (row ?M2 i) $ j"
    using assms dim_col_basis_of_int_mat dim_row_basis_of_int_mat
    by (metis index_row(1))
  then have row2: "?M2 $$ (i, j) = (of_int_vec ((form_basis p M X (degree p - 1)) ! i)) $j"
    using assms of_int_matrix_row_form_basis_var 
    by metis
  show ?thesis
    using row1 row2
    by (metis assms(1) assms(2) assms(3) dim_col_basis_mat index_map_vec(1) index_row(2) matrix_row_form_basis) 
qed

lemma of_int_mat_is_lower_triangular:
  fixes i j::"nat"
  assumes "degree p \<ge> 1"
  assumes "i < j"
  assumes "j < (degree p + 1)"
  shows "(vec_list_to_square_mat (map of_int_vec (form_basis p M X (degree p - 1)))) $$ (i,j) = 0"
  using assms of_int_mat_element form_basis_is_lower_triangular
  by (smt (verit, best) less_imp_le_nat nat_SN.compat of_int_code(2))

lemma of_int_mat_no_zeros_on_diagonal:
  assumes p_gt: "degree p \<ge> 1"
  assumes "M > 0"
  assumes "X > 0"
  shows "0 \<notin> set (diag_mat (vec_list_to_square_mat ((map of_int_vec (form_basis p M X (degree p - 1)))::rat vec list)))"
proof - 
  let ?M1 = "vec_list_to_square_mat (form_basis p M X (degree p - 1))"
  let ?M2 = "vec_list_to_square_mat ((map of_int_vec (form_basis p M X (degree p - 1)))::rat vec list)"
  let ?dim = "degree p + 1"
  have all: "\<And>i. i < ?dim \<Longrightarrow> ?M2 $$ (i, i) = 0 \<Longrightarrow> False"
  proof - 
    fix i
    assume i_lt: "i < degree p + 1"
    assume M2_elt: "vec_list_to_square_mat
          ((map of_int_vec (form_basis p M X (degree p - 1)))::rat vec list) $$
         (i, i) = 0"
    obtain k::"int" where k_prop: "?M1 $$ (i, i) = k"
      using i_lt matrix_carrier[of p i]
      by auto
    then have k_inset: "k \<in> set (map (\<lambda>i. ?M1 $$ (i, i)) [0..<?dim])"
      using i_lt nth_map_upt[of i ?dim 0 "\<lambda>i. ?M1 $$ (i, i)"] dim_row_basis_mat[of p M X] 
      by (metis (no_types, lifting) add.left_neutral diff_zero in_set_conv_nth length_map length_upt)
    have same_elt: "?M2 $$ (i, i) = rat_of_int (?M1 $$ (i, i))"
      using of_int_mat_element[OF p_gt i_lt i_lt] i_lt 
      by auto
    then have "(0::rat) = rat_of_int k"
      using M2_elt k_prop 
      by auto
    then have "k = 0"
      by auto
    then have "0 \<in> set (diag_mat ?M1)"
      using k_inset unfolding diag_mat_def
      using dim_row_basis_mat[of p M X] assms 
      by auto
    then show "False"
      using no_zeros_on_diagonal assms 
      by blast
  qed
  then have "0 \<in> set (map (\<lambda>i. ?M2 $$(i, i)) [0..< ?dim]) \<Longrightarrow> False" 
  proof - 
    assume "0 \<in> set (map (\<lambda>i. ?M2 $$(i, i)) [0..< ?dim])"
    then have "\<exists>i \<in> set [0..<degree p + 1]. 0 = ?M2$$(i, i)"
      using all atLeastLessThan_iff imageE list.set_map set_upt by force
    then have "\<exists>i < degree p + 1. 0 = ?M2$$(i, i)"
      using atLeast_upt by blast
    then show "False" using all 
      by fastforce
  qed
  then have "0 \<in> set (diag_mat (vec_list_to_square_mat ((map of_int_vec (form_basis p M X (degree p - 1)))::rat vec list))) \<Longrightarrow> False"
    using dim_row_basis_of_int_mat assms
    unfolding diag_mat_def 
    by (smt (verit, best))
  then show ?thesis by auto
qed

lemma of_int_mat_form_basis_distinct:
  assumes "degree p \<ge> 1"
  assumes "M > 0"
  assumes "X > 0"
  shows "distinct ((map of_int_vec (form_basis p M X (degree p - 1)))::rat vec list) "
proof - 
  let ?M = "vec_list_to_square_mat ((map of_int_vec (form_basis p M X (degree p - 1)))::rat vec list)"
  let ?dim = "degree p + 1"
  have rows_eq: "rows ?M = ((map of_int_vec (form_basis p M X (degree p - 1)))::rat vec list)"
    unfolding vec_list_to_square_mat_def
    apply (intro rows_mat_of_rows)
    apply clarsimp
    by (smt (verit, ccfv_SIG) One_nat_def add.commute add_Suc_right assms(1) dim_form_basis in_set_conv_nth matrix_row_form_basis_carrier one_add_one ordered_cancel_comm_monoid_diff_class.diff_add plus_1_eq_Suc)
  have in_set:"?M \<in> carrier_mat ?dim ?dim"                
    using dim_row_basis_of_int_mat[of p M X] dim_col_basis_of_int_mat[of p M X] assms  
    unfolding carrier_mat_def by auto
  show ?thesis
    using lower_triangular_imp_distinct[OF in_set] of_int_mat_is_lower_triangular of_int_mat_no_zeros_on_diagonal assms rows_eq 
    by metis
qed

lemma of_int_form_basis_lin_ind:
  assumes "M > 0"
  assumes "X > 0"
  assumes "degree p \<ge> 1"
  shows "\<not> module.lin_dep class_ring (module_vec TYPE(rat) (degree p + 1))
        (set ((map of_int_vec (form_basis p M X (degree p - 1)))::rat vec list))"
proof - 
  let ?M = "vec_list_to_square_mat ((map of_int_vec (form_basis p M X (degree p - 1)))::rat vec list)"
  have rows_M: "(rows
             (vec_list_to_square_mat
               (map of_int_vec (form_basis p M X (degree p - 1))))::rat vec list)
    = (map of_int_vec (form_basis p M X (degree p - 1))::rat vec list)"
    unfolding vec_list_to_square_mat_def 
    apply (intro rows_mat_of_rows)
    apply clarsimp
    apply (subst dim_form_basis)
    by (smt (verit) One_nat_def add.commute add_Suc_right assms(3) dim_form_basis in_set_conv_nth matrix_row_form_basis_carrier nat_1_add_1 ordered_cancel_comm_monoid_diff_class.diff_add plus_1_eq_Suc)
  have no_zeros_on_diagonal: " 0 \<notin> set (diag_mat ?M)"
    using of_int_mat_no_zeros_on_diagonal assms 
    by auto
  have lower_triangular: "(\<And>i j. i < j \<Longrightarrow> j < (degree p + 1) \<Longrightarrow> ?M $$ (i, j) = 0) "
    using of_int_mat_is_lower_triangular assms by auto
  have form_basis_distinct: "distinct ((map of_int_vec (form_basis p M X (degree p - 1))::rat vec list))"
    using of_int_mat_form_basis_distinct assms by auto
  have matrix_carrier: "?M \<in> carrier_mat (degree p + 1) (degree p + 1)"
    using of_int_matrix_carrier assms by auto 
  have "\<not> module.lin_dep class_ring (module_vec TYPE(rat) (degree p + 1)) (set (rows ?M))"
    using idom_vec.lower_triangular_imp_lin_indpt_rows[OF matrix_carrier lower_triangular]
      form_basis_distinct no_zeros_on_diagonal
    by blast
  then show ?thesis using rows_M 
    by auto
qed 

subsection \<open> Top-level proof \<close>

lemma towards_coppersmith:
  fixes p f:: "int poly"
  fixes M X:: "nat"
  fixes x0:: "int"
  assumes zero_mod_M: "poly p x0 mod M = 0"
  assumes d_is: "d = degree p" 
  assumes d_gt: "d > 0"
  assumes monic_poly: "coeff p d = 1"
  assumes X_gt: "X > 0"  
  assumes X_lt: "X < 1/(sqrt 2)*1/(root d (d+1))*(root (d*(d+1)) M)^2"
  assumes M_gt: "M > 0"
  assumes x0_le: "abs x0 \<le> X"
  assumes f_is: "f = towards_coppersmith p M X"
  shows "poly f x0 = 0"
proof -
  let ?cs_basis = "form_basis p M X (degree p - 1)"

  have li1_1: " vec_associated_to_int_poly p (int X) \<in> carrier_vec (Suc d)"
    by (metis assms(2) carrier_vec_dim_vec dim_vec_vec_associated_to_poly semiring_norm(174))
  have li1_2: "\<And>xa. xa \<in> set (form_basis_helper p M X (degree p - Suc 0)) \<Longrightarrow> xa \<in> carrier_vec (Suc d)"
    by (metis (no_types, lifting) assms(2) carrier_vec_dim_vec dim_form_basis_helper dim_vec g_i_vec_def in_set_conv_nth ith_row_form_basis_helper le_simps(2) semiring_norm(174))
  have li1: "set (map of_int_vec ?cs_basis) \<subseteq> carrier_vec (d + 1)"
    unfolding form_basis_def using li1_1 li1_2
    by auto

  have "distinct ?cs_basis"
    using d_is d_gt X_gt M_gt form_basis_distinct by force
  then have li2: "distinct ((map of_int_vec ?cs_basis)::rat vec list)"
    using casted_distinct_is_distinct by blast

  have li3:" module.lin_indpt class_ring
        (module_vec TYPE(rat) (d + 1))
        (set (map of_int_vec
               (form_basis p M X
                 (degree p - 1))))"
    unfolding form_basis_def
    using M_gt d_is X_gt d_gt form_basis_def of_int_form_basis_lin_ind by auto

  have 2: "\<And>a. a \<in> set ?cs_basis \<Longrightarrow> poly (int_poly_associated_to_vec a X) x0 mod M = 0" 
  proof - 
    fix a
    assume "a \<in> set ?cs_basis"
    then obtain i where a_prop: "i < d + 1 \<and> a = ?cs_basis ! i"
      by (metis (no_types, lifting) Suc_leI add_Suc_right arith_special(3) d_is d_gt dim_form_basis in_set_conv_nth numeral_nat(7) ordered_cancel_comm_monoid_diff_class.diff_add semiring_norm(174))
    {assume *: "i = d"
      then have " poly (int_poly_associated_to_vec a X) x0 mod M = 0"
        using  zero_mod_M
        using ith_row_form_basis a_prop *
        by (metis One_nat_def Suc_leI vec_associated_to_int_poly_inverse X_gt d_is d_gt ordered_cancel_comm_monoid_diff_class.diff_add)
    } moreover {assume *: "i < d"
      then have a_is:"a = g_i_vec M X i (d + 1)"
        using ith_row_form_basis d_is a_prop ith_row_form_basis_helper 
        by simp
      have i_lteq: "i \<le> degree p"
        using d_is * by auto
      have "int_poly_associated_to_vec a X = monom (int M) i"
        using d_is a_is int_poly_associated_to_g_i_vec[OF X_gt M_gt i_lteq] 
        by blast
      then have "poly (int_poly_associated_to_vec a X) x0 = x0^i * (int M)"
        by (simp add: poly_monom)
      then have "poly (int_poly_associated_to_vec a X) x0 mod M = 0"
        by auto
    }
    ultimately show "poly (int_poly_associated_to_vec a X) x0 mod M = 0" 
      using a_prop 
      by (metis Suc_eq_plus1 Suc_leI linorder_neqE_nat not_less)
  qed
  let ?vec = "vec_associated_to_int_poly p X"
  have vaip_div:"\<And>j. j < dim_vec ?vec \<Longrightarrow> ?vec $ j mod X ^ j = 0"
    by (simp add: vec_associated_to_poly_def)
  have form_basis_helper_div:"(\<And>v j. v \<in> set (form_basis_helper p M X (degree p - 1)) \<Longrightarrow>
            j < dim_vec v \<Longrightarrow> v $ j mod X ^ j = 0)" 
  proof - 
    fix v j
    assume v_inset: "v \<in> set (form_basis_helper p M X (degree p - 1))"
    assume j_lt: "j < dim_vec v"
    obtain i where "i < degree p \<and> v = (form_basis_helper p M X (degree p - 1)) ! i"
      using v_inset dim_form_basis_helper 
      by (metis (no_types, lifting) add.right_neutral add_Suc_right add_diff_inverse_nat assms(2) d_gt in_set_conv_nth less_Suc_eq not_less_zero plus_1_eq_Suc)
    then have v_is: "v = g_i_vec M X i (degree p + 1)"
      using ith_row_form_basis_helper[of i "degree p - 1" p M X]  
      by (metis Suc_pred' assms(2) d_gt le_simps(2))
    {assume *: "j = i"
      then have "v$j = int M * int X ^ i"
        using v_is j_lt unfolding g_i_vec_def 
        by fastforce
      then have "v $ j mod X ^ j = 0"
        using * by auto 
    } moreover {assume *: "j \<noteq> i"
      then have "v$j = 0"
        using v_is j_lt unfolding g_i_vec_def 
        by auto
      then have "v $ j mod X ^ j = 0" 
        by auto
    }
    ultimately show "v $ j mod X ^ j = 0"
      by blast
  qed

  then have 1: "(\<And>v j. v \<in> set ?cs_basis \<Longrightarrow>
            j < d + 1 \<Longrightarrow> v $ j mod X ^ j = 0)"
    using vaip_div form_basis_helper_div ith_row_form_basis set_form_basis
    by (metis assms(2) dim_form_basis dim_vector_in_basis in_set_conv_nth) 

  have " det (vec_list_to_square_mat (?cs_basis)) =
    int (M ^ degree p * X ^ \<Sum> {..d})"
    apply (intro det_of_matrix[OF M_gt X_gt _ d_is _ monic_poly])
    using d_is d_gt by auto
  
  then have d: "det (mat_of_rows (d + 1) ?cs_basis) =  M^d * X^(d * (d+1) div 2)"
    unfolding vec_list_to_square_mat_def
      dim_form_basis
    by (metis Suc_pred' add_2_eq_Suc' d_is d_gt atLeast0AtMost gauss_sum_nat semiring_norm(174))

  have d1: "(sqrt 2)^(d* (d+1)) = 2 ^ (d * (d + 1) div 2)"
    apply (subst sqrt_even_pow2[symmetric])
    using real_sqrt_power by auto

  have d2:"root d (real (d + 1)) ^ (d * (d + 1)) = (d + 1) ^ (d + 1)"
    by (metis d_gt of_nat_0_le_iff power_mult real_root_pow_pos2 semiring_1_class.of_nat_power)
    
  have "sqrt 2 * root d (d+1) * X < (root (d*(d+1)) M)^2"
    using X_lt d_gt
    by (auto simp add: field_simps)

  then have "(sqrt 2 * root d (d+1) * X) ^ (d * (d+1)) < M ^ 2"
    by (smt (verit, ccfv_SIG) Num.of_nat_simps(4) d_gt linordered_semiring_strict_class.mult_pos_pos mult_sign_intros(1) nat_less_real_le of_nat_0_le_iff real_root_ge_0_iff real_root_less_iff real_root_pos_unique real_root_power real_sqrt_ge_0_iff semiring_1_class.of_nat_power)

  moreover have "(sqrt 2 * root d (d+1) * X) ^ (d * (d+1)) =
    (sqrt 2)^(d* (d+1))  * X ^ (d * (d+1)) * 
    (root d (d+1))^(d * (d+1))"
    by (auto simp add: field_simps)

  ultimately have "(2 ^ (d * (d + 1) div 2) *
     real (X ^ (d * (d + 1) div 2))^2 *
    real ((d + 1) ^ (d + 1)))
    < M ^ 2 "
    unfolding d1 d2
    by (smt (verit) Num.of_nat_simps(2) Num.of_nat_simps(4) Num.of_nat_simps(5) d1 d2 dvd_div_mult_self even_add even_mult_iff more_arith_simps(6) of_nat_le_iff one_add_one power_mult semiring_1_class.of_nat_power)
  then have "
     (2 ^ (d * (d + 1) div 2) *
     (X ^ (d * (d + 1) div 2))^2 *
    ((d + 1) ^ (d + 1)))
    < M ^ 2 "
    by (smt (verit) Num.of_nat_simps(2) Num.of_nat_simps(4) Num.of_nat_simps(5) nat_1_add_1 of_nat_power_less_of_nat_cancel_iff semiring_1_class.of_nat_power)
  
  then have "
     (2 ^ (d * (d + 1) div 2) *
     (X ^ (d * (d + 1) div 2))^2 *
    ((d + 1) ^ (d + 1)))  * M ^ (2 * d)
    < M ^ 2  * M ^ (2 * d)"
    by (simp add: M_gt)
 
  then have h3: "2 ^ (d * (d + 1) div 2) *
    (M ^ d *  X ^ (d * (d + 1) div 2))\<^sup>2 *
    (d + 1) ^ (d + 1)
    < (M ^ (2 * (d + 1)))"
    by (auto simp add: algebra_simps monoid_mult_class.power_mult power2_eq_square)
  then have "Suc d ^ d * ((M ^ d)\<^sup>2 * (2 ^ ((d + d * d) div 2) * (X ^ ((d + d * d) div 2))\<^sup>2)) +
    d * (Suc d ^ d * ((M ^ d)\<^sup>2 * (2 ^ ((d + d * d) div 2) * (X ^ ((d + d * d) div 2))\<^sup>2)))
    < M * (M * M ^ (d * 2)) \<Longrightarrow>
    (1 + real d) ^ d *
    ((real M ^ d)\<^sup>2 * (2 ^ ((d + d * d) div 2) * (real X ^ ((d + d * d) div 2))\<^sup>2)) +
    real d *
    ((1 + real d) ^ d *
     ((real M ^ d)\<^sup>2 * (2 ^ ((d + d * d) div 2) * (real X ^ ((d + d * d) div 2))\<^sup>2)))
    < real M * (real M * real M ^ (d * 2))"
    proof -
    assume a1: "Suc d ^ d * ((M ^ d)\<^sup>2 * (2 ^ ((d + d * d) div 2) * (X ^ ((d + d * d) div 2))\<^sup>2)) + d * (Suc d ^ d * ((M ^ d)\<^sup>2 * (2 ^ ((d + d * d) div 2) * (X ^ ((d + d * d) div 2))\<^sup>2))) < M * (M * M ^ (d * 2))"
    have "\<forall>n na. real n < real na \<or> \<not> n < na"
      by simp
    then have "(1 + real d) ^ d * real ((M ^ d)\<^sup>2 * (2 ^ ((d + d * d) div 2) * (X ^ ((d + d * d) div 2))\<^sup>2)) + real d * ((1 + real d) ^ d * real ((M ^ d)\<^sup>2 * (2 ^ ((d + d * d) div 2) * (X ^ ((d + d * d) div 2))\<^sup>2))) < real (M * (M * M ^ (d * 2)))"
      using a1 by (smt (z3) Num.of_nat_simps(2) Num.of_nat_simps(4) Num.of_nat_simps(5) plus_1_eq_Suc semiring_1_class.of_nat_power)
    then show "(1 + real d) ^ d * ((real M ^ d)\<^sup>2 * (2 ^ ((d + d * d) div 2) * (real X ^ ((d + d * d) div 2))\<^sup>2)) + real d * ((1 + real d) ^ d * ((real M ^ d)\<^sup>2 * (2 ^ ((d + d * d) div 2) * (real X ^ ((d + d * d) div 2))\<^sup>2))) < real M * (real M * real M ^ (d * 2))"
      by simp
  qed
  then have 3: "real_of_rat 2 ^
    ((d + 1) * (d + 1 - 1) div 2) *
    real_of_int
     ((det (mat_of_rows (d + 1)
             (form_basis p M X
               (degree p -
                1))))\<^sup>2) *
    (real (d + 1)) ^ (d + 1)
    < real (M ^ (2 * (d + 1)))"
    using h3
    unfolding d
    by (auto simp add: field_simps)
    
  interpret lll: LLL_with_assms
    "d+1" "d+1" "?cs_basis" "2"
    apply unfold_locales
    subgoal by auto
    subgoal
      unfolding cof_vec_space.lin_indpt_list_def
      using li1 li2 li3 by auto
    using assms(2) d_gt dim_form_basis by auto
  
  interpret cs: coppersmith_assms
    "d+1" "d+1" "?cs_basis"
    "2" x0 M X p
    apply unfold_locales
    subgoal using M_gt by auto
    subgoal using X_gt by auto
    subgoal by auto
    subgoal using zero_mod_M by auto
    subgoal using x0_le by auto
    subgoal
      using assms(2) d_gt dim_form_basis by auto
    subgoal using 1 by auto
    using 2 by auto

  have *: "lll.short_vector = short_vector 2 ?cs_basis"
    using lll.short_vector_impl by presburger

  from cs.root_poly_short_vector
  show ?thesis
    using cs.bnd_raw_imp_short_vec_bound 3 lll.square_Gramian_determinant_eq_det_square
    unfolding f_is towards_coppersmith_def first_vector_def Let_def *
    by auto
qed

lemma towards_coppersmith_pretty:
  fixes p f:: "int poly"
  fixes M X:: "nat"
  fixes x0:: "int"
  defines "d \<equiv> degree p"
  defines "f \<equiv> towards_coppersmith p M X"
  assumes monic_poly: "monic p"
  assumes "d > 0" and "M > 0" and "X > 0"
  assumes zero_mod_M: "poly p x0 mod M = 0"
  assumes X_lt: "X < 1/(sqrt 2)*1/(root d (d+1))*(root (d*(d+1)) M)^2"
  assumes x0_le: "abs x0 \<le> X"
  shows "poly f x0 = 0"
  using assms towards_coppersmith
  by presburger

end