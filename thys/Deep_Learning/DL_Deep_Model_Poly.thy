(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Polynomials representing the Deep Network Model\<close>

theory DL_Deep_Model_Poly
imports DL_Deep_Model PP_More_MPoly "../Jordan_Normal_Form/Determinant"
begin

definition "polyfun N f = (\<exists>p. vars p \<subseteq> N \<and> (\<forall>x. insertion x p = f x))"

lemma polyfunI: "(\<And>P. (\<And>p. vars p \<subseteq> N \<Longrightarrow> (\<And>x. insertion x p = f x) \<Longrightarrow> P) \<Longrightarrow> P) \<Longrightarrow> polyfun N f"
  unfolding polyfun_def by metis

lemma polyfun_subset: "N\<subseteq>N' \<Longrightarrow> polyfun N f \<Longrightarrow> polyfun N' f" 
  unfolding polyfun_def by blast

lemma polyfun_const: "polyfun N (\<lambda>_. c)"
proof -
  have "\<And>x. insertion x (monom 0 c) = c" using insertion_single by (metis insertion_one monom_one mult.commute mult.right_neutral single_zero)
  then show ?thesis unfolding polyfun_def by (metis (full_types) empty_iff keys_single single_zero subsetI subset_antisym vars_monom_subset)
qed

lemma polyfun_add:
assumes "polyfun N f" "polyfun N g"
shows "polyfun N (\<lambda>x. f x + g x)"
proof -
  obtain p1 p2 where "vars p1 \<subseteq> N" "\<forall>x. insertion x p1 = f x" 
                     "vars p2 \<subseteq> N" "\<forall>x. insertion x p2 = g x"
    using polyfun_def assms by metis
  then have "vars (p1 + p2) \<subseteq> N" "\<forall>x. insertion x (p1 + p2) = f x + g x" 
    using vars_add using Un_iff subsetCE subsetI apply blast 
    by (simp add: \<open>\<forall>x. insertion x p1 = f x\<close> \<open>\<forall>x. insertion x p2 = g x\<close> insertion_add)
  then show ?thesis using polyfun_def by blast
qed

lemma polyfun_mult:
assumes "polyfun N f" "polyfun N g"
shows "polyfun N (\<lambda>x. f x * g x)"
proof -
  obtain p1 p2 where "vars p1 \<subseteq> N" "\<forall>x. insertion x p1 = f x" 
                     "vars p2 \<subseteq> N" "\<forall>x. insertion x p2 = g x"
    using polyfun_def assms by metis
  then have "vars (p1 * p2) \<subseteq> N" "\<forall>x. insertion x (p1 * p2) = f x * g x" 
    using vars_mult using Un_iff subsetCE subsetI apply blast 
    by (simp add: \<open>\<forall>x. insertion x p1 = f x\<close> \<open>\<forall>x. insertion x p2 = g x\<close> insertion_mult)
  then show ?thesis using polyfun_def by blast
qed

lemma polyfun_Sum:
assumes "finite I"
assumes "\<And>i. i\<in>I \<Longrightarrow> polyfun N (f i)"
shows "polyfun N (\<lambda>x. \<Sum>i\<in>I. f i x)"
  using assms 
  apply (induction I rule:finite_induct) 
  apply (simp add: polyfun_const)
  using comm_monoid_add_class.setsum.insert polyfun_add by fastforce

lemma polyfun_Prod:
assumes "finite I"
assumes "\<And>i. i\<in>I \<Longrightarrow> polyfun N (f i)"
shows "polyfun N (\<lambda>x. \<Prod>i\<in>I. f i x)"
  using assms 
  apply (induction I rule:finite_induct) 
  apply (simp add: polyfun_const)
  using comm_monoid_add_class.setsum.insert polyfun_mult by fastforce

lemma polyfun_single:
assumes "i\<in>N"
shows "polyfun N (\<lambda>x. x i)"
proof -
  have "\<forall>f. insertion f (monom (PP_Poly_Mapping.single i 1) 1) = f i" using insertion_single by simp
  then show ?thesis unfolding polyfun_def 
    using vars_monom_single[of i 1 1] One_nat_def assms singletonD subset_eq
    by blast
qed

lemma polyfun_det:
assumes "\<And>x. (A x) \<in> carrier\<^sub>m n n"
assumes "\<And>x i j. i<n \<Longrightarrow> j<n \<Longrightarrow> polyfun N (\<lambda>x. (A x) $$ (i,j))"
shows "polyfun N (\<lambda>x. det (A x))"
proof -
  {
    fix p assume "p\<in> {p. p permutes {0..<n}}"
    then have "p permutes {0..<n}" by auto
    then have "\<And>x. x < n \<Longrightarrow> p x < n" using permutes_in_image by auto
    then have "polyfun N (\<lambda>x. \<Prod>i = 0..<n. A x $$ (i, p i))" 
      using polyfun_Prod[of "{0..<n}" N "\<lambda>i x. A x $$ (i, p i)"] assms by simp
    then have "polyfun N (\<lambda>x. signof p * (\<Prod>i = 0..<n. A x $$ (i, p i)))" using polyfun_const polyfun_mult by blast
  }
  moreover have "finite {i. i permutes {0..<n}}" by (simp add: finite_permutations)
  ultimately show ?thesis  unfolding det_def'[OF assms(1)] 
    using polyfun_Sum[OF `finite {i. i permutes {0..<n}}`, of N "\<lambda>p x. signof p * (\<Prod>i = 0..<n. A x $$ (i, p i))"] 
    by blast
qed

lemma polyfun_extract_matrix:
assumes "i<m" "j<n" 
shows "polyfun {..<a + (m * n + c)} (\<lambda>f. extract_matrix (\<lambda>i. f (i + a)) m n $$ (i,j))"
unfolding index_extract_matrix[OF assms] apply (rule polyfun_single) using two_digit_le[OF assms] by simp

lemma polyfun_mat_mult_vec:
assumes "\<And>x. v x \<in> carrier\<^sub>v n"
assumes "\<And>j. j<n \<Longrightarrow> polyfun N (\<lambda>x. v x $ j)"
assumes "\<And>x. A x \<in> carrier\<^sub>m m n"
assumes "\<And>i j. i<m \<Longrightarrow> j<n \<Longrightarrow> polyfun N (\<lambda>x. A x $$ (i,j))"
assumes "j < m"
shows "polyfun N (\<lambda>x. ((A x) \<otimes>\<^sub>m\<^sub>v (v x)) $ j)"
proof -
  have "\<And>x. j < dim\<^sub>r (A x)" using `j < m` assms(3) mat_carrierD(1) by force
  have "\<And>x. n = dim\<^sub>v (v x)" using assms(1) vec_elemsD by fastforce
  {
    fix i assume "i \<in> {0..<n}"
    then have "i < n" by auto
    { 
      fix x 
      have "i < dim\<^sub>v (v x)" using assms(1) vec_elemsD `i<n` by fastforce
      have "j < dim\<^sub>r (A x)" using `j < m` assms(3) mat_carrierD(1) by force
      have "dim\<^sub>c (A x) = dim\<^sub>v (v x)" by (metis assms(1) assms(3) mat_carrierD(2) vec_elemsD)
      then have "row (A x) j $ i = A x $$ (j,i)" "i<n" using `j < dim\<^sub>r (A x)` `i<n` by (simp_all add: \<open>i < dim\<^sub>v (v x)\<close>)
    }
    then have "polyfun N (\<lambda>x. row (A x) j $ i * v x $ i)"  
      using polyfun_mult assms(4)[OF `j < m`] assms(2) by fastforce
  }
  then show ?thesis unfolding index_mat_mult_vec[OF `\<And>x. j < dim\<^sub>r (A x)`] scalar_prod_def 
    using polyfun_Sum[of "{0..<n}" N "\<lambda>i x. row (A x) j $ i * v x $ i"] finite_atLeastLessThan[of 0 n] `\<And>x. n = dim\<^sub>v (v x)`
    by simp
qed

(* The variable a has been inserted here to make the induction work:*)
lemma polyfun_evaluate_net_plus_a:
assumes "map dim\<^sub>v inputs = input_sizes m"
assumes "valid_net m"
assumes "j < output_size m"
shows "polyfun {..<a + count_weights m} (\<lambda>f. evaluate_net (insert_weights m (\<lambda>i. f (i + a))) inputs $ j)" 
using assms proof (induction m arbitrary:inputs j a)
  case (Input)
  then show ?case unfolding insert_weights.simps evaluate_net.simps using polyfun_const by metis
next
  case (Conv x m)
  then obtain x1 x2 where "x=(x1,x2)" by fastforce
  show ?case unfolding `x=(x1,x2)` insert_weights.simps evaluate_net.simps drop_map unfolding list_of_vec_index 
  proof (rule polyfun_mat_mult_vec)
    {
      fix f
      have 1:"valid_net' (insert_weights m (\<lambda>i. f (i + x1 * x2)))" 
        using `valid_net (Conv x m)` valid_net.simps by (metis 
        convnet.distinct(1) convnet.distinct(5) convnet.inject(2) remove_insert_weights)
      have 2:"map dim\<^sub>v inputs = input_sizes (insert_weights m (\<lambda>i. f (i + x1 * x2)))" 
        using input_sizes_remove_weights remove_insert_weights 
        by (simp add: Conv.prems(1))
      have "dim\<^sub>v (evaluate_net (insert_weights m (\<lambda>i. f (i + x1 * x2))) inputs) = output_size m"
       using output_size_correct[OF 1 2] using remove_insert_weights by auto
      then show "evaluate_net (insert_weights m (\<lambda>i. f (i + x1 * x2))) inputs \<in> carrier\<^sub>v (output_size m)"
        using vec_carrier_def by (metis (full_types) mem_Collect_eq)
    }

    have "map dim\<^sub>v inputs = input_sizes m" by (simp add: Conv.prems(1))
    have "valid_net m" using Conv.prems(2) valid_net.cases by fastforce
    show "\<And>j. j < output_size m \<Longrightarrow>  polyfun {..<a + count_weights (Conv (x1, x2) m)}
          (\<lambda>f. evaluate_net (insert_weights m (\<lambda>i. f (i + x1 * x2 + a))) inputs $ j)"
      unfolding vec_of_list_index count_weights.simps 
      using Conv(1)[OF `map dim\<^sub>v inputs = input_sizes m` `valid_net m`, of _ "x1 * x2 + a"] 
      unfolding semigroup_add_class.add.assoc ab_semigroup_add_class.add.commute[of "x1 * x2" a]
      by blast


    have "output_size m = x2" using Conv.prems(2) \<open>x = (x1, x2)\<close> valid_net.cases by fastforce
    show "\<And>f. extract_matrix (\<lambda>i. f (i + a)) x1 x2 \<in> carrier\<^sub>m x1 (output_size m)" unfolding `output_size m = x2` using dim_extract_matrix
      using mat_carrierI by (metis (no_types, lifting))
    
    show "\<And>i j. i < x1 \<Longrightarrow> j < output_size m \<Longrightarrow> polyfun {..<a + count_weights (Conv (x1, x2) m)} (\<lambda>f. extract_matrix (\<lambda>i. f (i + a)) x1 x2 $$ (i, j))"
      unfolding `output_size m = x2` count_weights.simps using polyfun_extract_matrix[of _ x1 _ x2 a "count_weights m"] by blast

    show "j < x1" using Conv.prems(3) \<open>x = (x1, x2)\<close> by auto
  qed
next
  case (Pool m1 m2 inputs j a)
  have A2:"\<And>f. map dim\<^sub>v (take (length (input_sizes (insert_weights m1 (\<lambda>i. f (i + a))))) inputs) = input_sizes m1"
    by (metis Pool.prems(1)  append_eq_conv_conj input_sizes.simps(3) input_sizes_remove_weights remove_insert_weights take_map)
  have B2:"\<And>f. map dim\<^sub>v (drop (length (input_sizes (insert_weights m1 (\<lambda>i. f (i + a))))) inputs) = input_sizes m2"
    using Pool.prems(1) append_eq_conv_conj input_sizes.simps(3) input_sizes_remove_weights remove_insert_weights by (metis drop_map)
  have A3:"valid_net m1" and B3:"valid_net m2" using `valid_net (Pool m1 m2)` valid_net.simps by blast+
  have "output_size (Pool m1 m2) = output_size m2" unfolding output_size.simps 
    using `valid_net (Pool m1 m2)` "valid_net.cases" by fastforce
  then have A4:"j < output_size m1" and B4:"j < output_size m2" using `j < output_size (Pool m1 m2)` by simp_all
 
  let ?net1 = "\<lambda>f. evaluate_net (insert_weights m1 (\<lambda>i. f (i + a)))
    (take (length (input_sizes (insert_weights m1 (\<lambda>i. f (i + a))))) inputs)"
  let ?net2 = "\<lambda>f. evaluate_net (insert_weights m2 (\<lambda>i. f (i + count_weights m1 + a)))
    (drop (length (input_sizes (insert_weights m1 (\<lambda>i. f (i + a))))) inputs)"
  have length1: "\<And>f. output_size m1 = dim\<^sub>v (?net1 f)"
    by (metis A2 A3 input_sizes_remove_weights output_size_correct remove_insert_weights)
  then have jlength1:"\<And>f. j < dim\<^sub>v (?net1 f)" using A4 by metis
  have length2: "\<And>f. output_size m2 = dim\<^sub>v (?net2 f)" 
    by (metis B2 B3 input_sizes_remove_weights output_size_correct remove_insert_weights)
  then have jlength2:"\<And>f. j < dim\<^sub>v (?net2 f)" using B4 by metis
  have cong1:"\<And>xf. (\<lambda>f. evaluate_net (insert_weights m1 (\<lambda>i. f (i + a)))
        (take (length (input_sizes (insert_weights m1 (\<lambda>i. xf (i + a))))) inputs) $ j)
         = (\<lambda>f. ?net1 f $ j)" 
    using input_sizes_remove_weights remove_insert_weights by auto
  have cong2:"\<And>xf. (\<lambda>f. evaluate_net (insert_weights m2 (\<lambda>i. f (i + (a + count_weights m1))))
        (drop (length (input_sizes (insert_weights m1 (\<lambda>i. xf (i + a))))) inputs) $ j)
         = (\<lambda>f. ?net2 f $ j)" 
    unfolding semigroup_add_class.add.assoc[symmetric] ab_semigroup_add_class.add.commute[of a "count_weights m1"] 
    using input_sizes_remove_weights remove_insert_weights by auto

  show ?case unfolding insert_weights.simps evaluate_net.simps index_component_mult[OF jlength1 jlength2] count_weights.simps
    apply (rule polyfun_mult)
    using Pool.IH(1)[OF A2 A3 A4, of a, unfolded cong1] 
    using Pool.IH(2)[OF B2 B3 B4, of "a + count_weights m1", unfolded cong2 semigroup_add_class.add.assoc[of a]]  
    using polyfun_subset[of "{..<a + count_weights m1}" "{..<a + (count_weights m1 + count_weights m2)}"] 
    by auto
qed

lemma polyfun_evaluate_net:
assumes "map dim\<^sub>v inputs = input_sizes m"
assumes "valid_net m"
assumes "j < output_size m"
shows "polyfun {..<count_weights m} (\<lambda>f. evaluate_net (insert_weights m f) inputs $ j)" 
using polyfun_evaluate_net_plus_a[where a=0, OF assms] by simp

lemma polyfun_tensors_from_net:
assumes "valid_net m"
assumes "is \<lhd> input_sizes m"
assumes "j < output_size m"
shows "polyfun {..<count_weights m} (\<lambda>f. Tensor.lookup (tensors_from_net (insert_weights m f) $ j) is)"
proof -
  have 1:"\<And>f. valid_net' (insert_weights m f)" by (simp add: assms(1) remove_insert_weights)
  have input_sizes:"\<And>f. input_sizes (insert_weights m f) = input_sizes m"
    unfolding input_sizes_remove_weights by (simp add: remove_insert_weights)
  have 2:"\<And>f. is \<lhd> input_sizes (insert_weights m f)" 
    unfolding input_sizes using assms(2) by blast
  have 3:"\<And>f. j < output_size' (insert_weights m f)" 
    by (simp add: assms(3) remove_insert_weights)
  have "\<And>f1 f2. base_input (insert_weights m f1) is = base_input (insert_weights m f2) is"
    unfolding base_input_def by (simp add: input_sizes)
  then have "\<And>xf. (\<lambda>f. evaluate_net (insert_weights m f) (base_input (insert_weights m xf) is) $ j)
    = (\<lambda>f. evaluate_net (insert_weights m f) (base_input (insert_weights m f) is) $ j)"
    by metis 
  then show ?thesis unfolding lookup_tensors_from_net[OF 1 2 3] 
    using polyfun_evaluate_net[OF base_input_length[OF 2, unfolded input_sizes, symmetric] assms(1) assms(3)] 
    by fastforce
qed

lemma polyfun_matricize:
assumes "\<And>x. dims (T x) = ds"
assumes "\<And>is. is \<lhd> ds \<Longrightarrow> polyfun N (\<lambda>x. Tensor.lookup (T x) is)"
assumes "\<And>x. dim\<^sub>r (matricize I (T x)) = nr"
assumes "\<And>x. dim\<^sub>c (matricize I (T x)) = nc"
assumes "i < nr"
assumes "j < nc"
shows "polyfun N (\<lambda>x. matricize I (T x) $$ (i,j))"
proof -
  let ?weave = "\<lambda> x. (weave I 
    (digit_encode (sublist ds I ) i) 
    (digit_encode (sublist ds (-I )) j))"
  have 1:"\<And>x. matricize I (T x) $$ (i,j) = Tensor.lookup (T x) (?weave x)" unfolding matricize_def
    by (metis (no_types, lifting) assms(1) assms(3) assms(4) assms(5) assms(6) case_prod_conv 
    mat_dim_col_mat(1) mat_dim_row_mat(1) mat_index_mat(1) matricize_def)
  have "\<And>x. ?weave x \<lhd> ds"
    using valid_index_weave(1) assms(2) digit_encode_valid_index mat_dim_row_mat(1) matricize_def
    using assms digit_encode_valid_index matricize_def by (metis mat_dim_col_mat(1))
  then have "polyfun N (\<lambda>x. Tensor.lookup (T x) (?weave x))" using assms(2) by simp
  then show ?thesis unfolding 1 using assms(1) by blast
qed

lemma "(\<not> (a::nat) < b) = (a \<ge> b)"
by (metis not_le)

lemma polyfun_submatrix:
assumes "\<And>x. (A x) \<in> carrier\<^sub>m m n"
assumes "\<And>x i j. i<m \<Longrightarrow> j<n \<Longrightarrow> polyfun N (\<lambda>x. (A x) $$ (i,j))"
assumes "i < card {i. i < m \<and> i \<in> I}"
assumes "j < card {j. j < n \<and> j \<in> J}"
assumes "infinite I" "infinite J"
shows "polyfun N (\<lambda>x. (submatrix (A x) I J) $$ (i,j))"
proof -
  have 1:"\<And>x. (submatrix (A x) I J) $$ (i,j) = (A x) $$ (pick I i, pick J j)"
    using submatrix_index by (metis (no_types, lifting) Collect_cong assms(1) assms(3) assms(4) mat_carrierD(1) mat_carrierD(2))
  have "pick I i < m"  "pick J j < n" using card_le_pick_inf[OF `infinite I`] card_le_pick_inf[OF `infinite J`]
    `i < card {i. i < m \<and> i \<in> I}`[unfolded set_le_in] `j < card {j. j < n \<and> j \<in> J}`[unfolded set_le_in] not_less by metis+
  then show ?thesis unfolding 1 by (simp add: assms(2))
qed

context deep_model_correct_params_y
begin

definition witness_submatrix where
"witness_submatrix j f = submatrix (A' f) rows_with_1 rows_with_1"


lemma polyfun_tensor_deep_model:
assumes "is \<lhd> input_sizes (deep_model_l rs)" 
shows "polyfun {..<weight_space_dim}
  (\<lambda>f. Tensor.lookup (tensors_from_net (insert_weights (deep_model_l rs) f) $ y) is)"
proof -
  have 1:"\<And>f. remove_weights (insert_weights (deep_model_l rs) f) = deep_model_l rs"
    using remove_insert_weights by metis
  then have "y < output_size ( deep_model_l rs)" using valid_deep_model y_valid length_output_deep_model by force
  have 0:"{..<weight_space_dim} = set [0..<weight_space_dim]" by auto
  then show ?thesis unfolding weight_space_dim_def using polyfun_tensors_from_net assms(1) valid_deep_model 
    `y < output_size ( deep_model_l rs )` by metis
qed

lemma input_sizes_deep_model: "input_sizes (deep_model_l rs) = replicate (2 * N_half) (last rs)" 
  unfolding N_half_def using input_sizes_deep_model deep 
  by (metis (no_types, lifting) Nitpick.size_list_simp(2) One_nat_def Suc_1 Suc_le_lessD diff_Suc_Suc length_tl less_imp_le_nat list.size(3) not_less_eq numeral_3_eq_3 realpow_num_eq_if)

lemma polyfun_matrix_deep_model:
assumes "i<(last rs) ^ N_half"
assumes "j<(last rs) ^ N_half"
shows "polyfun {..<weight_space_dim} (\<lambda>f. A' f $$ (i,j))"
proof -
  have 0:"y < output_size ( deep_model_l rs )" using valid_deep_model y_valid length_output_deep_model by force
  have 1:"\<And>f. remove_weights (insert_weights (deep_model_l rs) f) = deep_model_l rs"
    using remove_insert_weights by metis
  have 2:"(\<And>f is. is \<lhd> replicate (2 * N_half) (last rs) \<Longrightarrow>
         polyfun {..<weight_space_dim} (\<lambda>x. Tensor.lookup (A x) is))" 
    unfolding A_def using polyfun_tensor_deep_model[unfolded input_sizes_deep_model] 0 by blast
  show ?thesis 
    unfolding A'_def A_def apply (rule polyfun_matricize) 
    using dims_tensor_deep_model[OF 1] 2[unfolded A_def] 
    using dims_A'_pow[unfolded A'_def A_def] `i<(last rs) ^ N_half` `j<(last rs) ^ N_half` 
    by auto
qed

lemma polyfun_submatrix_deep_model:
assumes "i < r ^ N_half"
assumes "j < r ^ N_half"
shows "polyfun {..<weight_space_dim} (\<lambda>f. witness_submatrix y f $$ (i,j))"
unfolding witness_submatrix_def 
proof (rule polyfun_submatrix)
  have 1:"\<And>f. remove_weights (insert_weights (deep_model_l rs) f) = deep_model_l rs"
    using remove_insert_weights by metis
  show "\<And>f. A' f \<in> carrier\<^sub>m ((last rs) ^ N_half) ((last rs) ^ N_half)"
    using "1" dims_A'_pow using weight_space_dim_def by auto
  show "\<And>f i j. i < last rs ^ N_half \<Longrightarrow> j < last rs ^ N_half \<Longrightarrow>
        polyfun {..<weight_space_dim} (\<lambda>f. A' f $$ (i, j))"
    using polyfun_matrix_deep_model weight_space_dim_def by force
  show "i < card {i. i < last rs ^ N_half \<and> i \<in> rows_with_1}" 
    using assms(1) card_rows_with_1 dims_Aw'_pow set_le_in by metis
  show "j < card {i. i < last rs ^ N_half \<and> i \<in> rows_with_1}" 
    using assms(2) card_rows_with_1 dims_Aw'_pow set_le_in by metis
  show "infinite rows_with_1" "infinite rows_with_1" by (simp_all add: infinite_rows_with_1)
qed

lemma polyfun_det_deep_model:
shows "polyfun {..<weight_space_dim} (\<lambda>f. det (witness_submatrix y f))"
proof (rule polyfun_det)
  fix f
  have "remove_weights (insert_weights (deep_model_l rs) f) = deep_model_l rs"
    using remove_insert_weights by metis

  show "witness_submatrix y f \<in> carrier\<^sub>m (r ^ N_half) (r ^ N_half)" 
    unfolding witness_submatrix_def apply (rule mat_carrierI) unfolding dim_submatrix[unfolded set_le_in] 
    unfolding dims_A'_pow[unfolded weight_space_dim_def] using card_rows_with_1 dims_Aw'_pow by simp_all
  show "\<And>i j. i < r ^ N_half \<Longrightarrow> j < r ^ N_half \<Longrightarrow> polyfun {..<weight_space_dim} (\<lambda>f. witness_submatrix y f $$ (i, j))"
    using polyfun_submatrix_deep_model by blast
qed

end

end
