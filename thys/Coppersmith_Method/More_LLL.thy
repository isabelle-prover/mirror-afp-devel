section \<open> Preliminary results for LLL \<close>

text \<open> In this file, we prove some additional results involving
  lattices and a bound for LLL. \<close>

theory More_LLL
imports
  "LLL_Basis_Reduction.LLL"
begin 

context vec_module begin

lemma in_lattice_ofD:
  assumes x: "x \<in> lattice_of a"
  assumes a: "set a \<subseteq> carrier_vec n"
  obtains v where
    "v \<in> carrier_vec (length a)"
    "mat_of_cols n a *\<^sub>v map_vec of_int (v::int vec) = x"
proof -
  from in_latticeE[OF x]
  obtain c where
    c: "x = sumlist (map (\<lambda> i. of_int (c i) \<cdot>\<^sub>v a ! i) [0 ..< length a])" .

  have "x = lincomb_list (of_int \<circ> c) a "
    unfolding lincomb_list_def c by auto
  also have "... = 
    mat_of_cols n a *\<^sub>v vec (length a) (of_int \<circ> c)"
    apply (subst lincomb_list_as_mat_mult)
    using a by auto
  also have "... = 
    mat_of_cols n a *\<^sub>v map_vec of_int (vec (length a) c)"
    by (auto simp add: map_vec)
  finally have "x = mat_of_cols n a *\<^sub>v map_vec of_int (vec (length a) c)" .
  thus ?thesis
    by (auto intro!: that)
qed

lemma exists_list_all2:
  assumes "\<forall>x. (x \<in> set xs \<longrightarrow> (\<exists>y. P x y))"
  obtains ys where "list_all2 P xs ys"
  using assms
proof (induction xs arbitrary: thesis)
  case Nil
  then show ?case
    by auto
next
  case c: (Cons x xs)
  obtain y where y: "P x y"
    using c(3) by auto
  obtain ys where ys: "list_all2 P xs ys"
    using c
    by auto 
  show ?case using c y ys by auto
qed
  
lemma subset_lattice_ofD:
  assumes xs: "set xs \<subseteq> lattice_of a" "set xs \<subseteq> carrier_vec n"
  assumes a: "set a \<subseteq> carrier_vec n"
  obtains vs where
    "vs \<in> carrier_mat (length a) (length xs)"
    "mat_of_cols n a * map_mat of_int vs = mat_of_cols n xs"
proof -
  define P where "P = 
    (\<lambda>x v. v \<in> carrier_vec (length a) \<and>
    mat_of_cols n a *\<^sub>v map_vec of_int (v::int vec) = x)"
  obtain ys where ys: "list_all2 P xs ys"
    apply (subst exists_list_all2[where P = "P", where xs = "xs"])
    unfolding P_def
    apply (meson a in_lattice_ofD subsetD xs)
    by auto

  then have len: "length xs = length ys"
    using list_all2_lengthD by blast

  define vs where "vs = mat_of_cols (length a) ys"
  have 1: "vs \<in> carrier_mat (length a) (length xs)"
    unfolding vs_def
    by (metis len mat_of_cols_carrier(1))

  have "i < length ys \<Longrightarrow>
    mat_of_cols n a *\<^sub>v
    of_int_hom.vec_hom (col (mat_of_cols (length a) ys) i) = xs ! i" for i
    by (metis P_def col_mat_of_cols list_all2_conv_all_nth ys)
  then have "i < length ys \<Longrightarrow>
   col (mat_of_cols n a * of_int_hom.mat_hom (mat_of_cols (length a) ys)) i =
   col (mat_of_cols n xs) i" for i
    apply (subst col_mat_of_cols)
    subgoal using len by auto
    subgoal using len xs(2) by fastforce
    apply (subst col_mult2)
    by auto
  then have 2: "mat_of_cols n a * map_mat of_int vs = mat_of_cols n xs"
    unfolding vs_def
    apply (intro mat_col_eqI)
    using len by auto

  show ?thesis
    apply (intro that)
    using 1 2 by auto
qed

lemma mk_coeff_list_nth:
  assumes "i < length ls" "distinct ls"
  shows "mk_coeff ls f (ls ! i) = f i"
  using assms
proof (induction ls arbitrary: f i)
  case Nil
  then show ?case
    by auto
next
  case (Cons l ls)
  then show ?case
    by (auto simp add: mk_coeff_Cons nth_equal_first_eq)
qed

text \<open> This next lemma is trivial when the cols are not distinct. \<close>
lemma mat_mul_non_zero_col_lin_dep:
  assumes A: "A \<in> carrier_mat n y" "distinct (cols A)"
  assumes U: "U \<in> carrier_mat y z"
  assumes i: "i < z" "col U i \<noteq> 0\<^sub>v y"
  assumes eqz: "A * U = 0\<^sub>m n z"
  shows "lin_dep (set (cols A))"
proof -
  obtain j where j: "j < y" "U $$ (j,i) \<noteq> 0"
    using U i
    unfolding vec_eq_iff
    by auto

  have Aeq: "A = mat_of_cols n (cols A)"
    using A by auto
  have "0\<^sub>v n = A *\<^sub>v (col U i)"  
    using eqz
    unfolding mat_eq_iff vec_eq_iff
    using A U i by auto
  also have "... = mat_of_cols n (cols A) *\<^sub>v vec (length (cols A)) (\<lambda>ia. U $$ (ia, i))"
    unfolding col_def Aeq[symmetric] using A U by auto
  also have "... =
    lincomb_list (\<lambda>ia. U $$ (ia, i)) (cols A)"
    apply (subst lincomb_list_as_mat_mult[symmetric])
     apply (metis assms(1) carrier_matD(1) carrier_vecD cols_dim subsetD)
    by auto
  also have "... =
    lincomb (mk_coeff (cols A) (\<lambda>ia. U $$ (ia, i))) (set (cols A))"
    apply (subst lincomb_list_as_lincomb)
    using assms(1) cols_dim apply blast
    by auto
  finally have
    lc:"lincomb (mk_coeff (cols A) (\<lambda>ia. U $$ (ia, i))) (set (cols A)) = 0\<^sub>v n" by auto

  have mc: "mk_coeff (cols A) (\<lambda>ia. U $$ (ia, i)) (col A j) \<noteq> 0"
    using mk_coeff_list_nth
    by (metis assms(1) assms(2) carrier_matD(2) cols_length cols_nth j)

  have "col A j \<in> set (cols A)"
    by (metis assms(1) carrier_matD(2) cols_length cols_nth j(1) nth_mem)
  thus ?thesis
    apply (intro lin_dep_crit [OF _ _ _ _ mc lc])
    using A j by auto
qed

lemma lin_indpt_mul_eq_ident:
  assumes a: "distinct a" "lin_indpt (set a)"
    "set a \<subseteq> carrier_vec n" "length a = m"
  assumes u: "u \<in> carrier_mat m m"
  assumes e: "mat_of_cols n a = mat_of_cols n a * u"
  shows "u = 1\<^sub>m m"
proof (rule ccontr)
  assume "u \<noteq> 1\<^sub>m m"
  then obtain i where i: "i < m"
    "col (u - 1\<^sub>m m) i \<noteq> 0\<^sub>v m"
    unfolding vec_eq_iff mat_eq_iff
    using u by auto
  have 1:"mat_of_cols n a \<in> carrier_mat n m"
    using assms(4) mat_of_cols_carrier(1) by blast
  have 2:"distinct (cols (mat_of_cols n a))"
    by (simp add: assms(1) assms(3))

  have "mat_of_cols n a * (u - 1\<^sub>m m) = 0\<^sub>m n m"
    by (smt (verit, ccfv_SIG) assms(4) e mat_of_cols_carrier(1) minus_r_inv_mat mult_minus_distrib_mat one_carrier_mat right_mult_one_mat u)
  from mat_mul_non_zero_col_lin_dep[OF 1 2 _ i this]
  show False
    using a by (simp add: assms(3) minus_carrier_mat)
qed

end

text \<open> Set up a locale: vec\_module where the ring has characteristic zero \<close>
locale ring_char_0_vec_module = vec_module f_ty n for
  f_ty::"'a:: {comm_ring_1, ring_char_0} itself"
  and n
begin                                                           

text \<open> This next lemma shows that different basis a, b of the same lattice 
  have the same Gram determinant. \<close>
lemma lattice_of_eq_gram_det_eq:
  fixes a b::"'a vec list"
  assumes a: "distinct a" "lin_indpt (set a)" "set a \<subseteq> carrier_vec n"
  assumes b: "set b \<subseteq> carrier_vec n" "length a = length b"
  assumes lat_eq: "lattice_of a = lattice_of b"
  defines A: "A \<equiv> mat_of_cols n a"
  defines B: "B \<equiv> mat_of_cols n b"
  shows "det (A\<^sup>T * A) = det (B\<^sup>T * B)"
proof -
  let ?m = "length a"
  have "set b \<subseteq> lattice_of a"
    by (simp add: lat_eq b basis_in_latticeI subsetI)    
  from subset_lattice_ofD[OF this]
  obtain vs where
    vs: "vs \<in> carrier_mat (length a) (length b)"
    "mat_of_cols n a * map_mat of_int vs = mat_of_cols n b"
    using a b by blast
  then have vsn: "vs \<in> carrier_mat ?m ?m" using b(2) by auto
  have "set a \<subseteq> lattice_of b"
    using a(3) lat_eq basis_in_latticeI by auto
  from subset_lattice_ofD[OF this]
  obtain us where
    us: "us \<in> carrier_mat (length b) (length a)"
    "mat_of_cols n b * map_mat of_int us = mat_of_cols n a"
    using a b by blast
  then have usn: "us \<in> carrier_mat ?m ?m" using b(2) by auto
  have "mat_of_cols n a =
    (mat_of_cols n a * map_mat of_int vs) * map_mat of_int us"
    using us vs by simp
  also have "... = mat_of_cols n a * (map_mat of_int vs * map_mat of_int us)"
    by (auto intro!: assoc_mult_mat us vs)
  also have "... = mat_of_cols n a * (map_mat of_int (vs * us))"
    by (metis of_int_hom.mat_hom_mult us(1) vs(1))
  finally have "mat_of_cols n a = mat_of_cols n a * (map_mat of_int (vs * us))" .

  from lin_indpt_mul_eq_ident[OF a(1-3) _ _ this]
  have "((map_mat of_int (vs * us))::'a mat) = (1\<^sub>m ?m::'a mat)"
    using vsn usn by auto
  then have "vs * us = 1\<^sub>m ?m"
    by (simp add: of_int_hom.mat_hom_inj of_int_hom.mat_hom_one)

  then have "det vs * det us = 1"
    using det_mult[OF vsn usn] by simp
  then have "(det us)^2 = 1"
    using power2_eq_1_iff zmult_eq_1_iff by blast
  then have us1: "(det (map_mat of_int us))^2 = 1"
    by (metis of_int_hom.hom_det of_int_hom.hom_one of_int_power)

  have Bcarr:"B \<in> carrier_mat n ?m"
    unfolding B using b by auto
  then have BtBcarr:"B\<^sup>T * B \<in> carrier_mat ?m ?m" by auto
  then have uBtBcarr: " (of_int_hom.mat_hom us)\<^sup>T * (B\<^sup>T * B) \<in> carrier_mat ?m ?m"
    using usn
    by simp

  have d: "of_int_hom.mat_hom us \<in> carrier_mat (length a) (length a)"
    using b(2) us(1) by auto
  have "det (A\<^sup>T * A) =
    det ((B * map_mat of_int us)\<^sup>T * (B * map_mat of_int us))"
      using us A B by auto
  also have "... = det ( (map_mat of_int us)\<^sup>T * (B\<^sup>T * B)  * map_mat of_int us)"
      apply (subst transpose_mult[OF Bcarr d])
    using us b
    by (smt (verit, ccfv_threshold) Bcarr assoc_mult_mat map_carrier_mat mult_carrier_mat transpose_carrier_mat)
  also have "... = det (map_mat of_int us)^2 * det (B\<^sup>T * B)"
    apply (subst det_mult[OF uBtBcarr d])
    apply (subst det_mult[OF _ BtBcarr])
    using usn by (auto simp add: det_transpose power2_eq_square)
  finally show ?thesis
    using us1
    by (metis l_one)
qed

lemma lattice_of_eq_gram_det_rows_eq:
  fixes a b::"'a vec list"
  assumes a: "distinct a" "lin_indpt (set a)" "set a \<subseteq> carrier_vec n"
  assumes b: "set b \<subseteq> carrier_vec n"  "length a = length b"
  assumes lat_eq: "lattice_of a = lattice_of b"
  defines A: "A \<equiv> mat_of_rows n a"
  defines B: "B \<equiv> mat_of_rows n b"
  shows "det (A * A\<^sup>T) = det (B * B\<^sup>T)"
proof -
  have transpose_mat_a: "A = transpose_mat (mat_of_cols n a)"
    by (simp add: transpose_mat_of_cols A)
  have transpose_mat_b: "B = transpose_mat (mat_of_cols n b)"
    by (simp add: transpose_mat_of_cols B)
  from lattice_of_eq_gram_det_eq[OF assms(1-6)]
  have "det ((mat_of_cols n a)\<^sup>T * mat_of_cols n a) =
    det ((mat_of_cols n b)\<^sup>T * mat_of_cols n b)" by blast
  then show ?thesis
  using transpose_mat_a transpose_mat_b
  by auto
qed

lemma lattice_of_eq_sq_det_eq:
  fixes a b::"'a vec list"
  assumes a: "distinct a" "lin_indpt (set a)" "set a \<subseteq> carrier_vec n" "length a = n"
  assumes b: "set b \<subseteq> carrier_vec n" "length b = n"
  assumes lat_eq: "lattice_of a = lattice_of b"
  shows "(det (mat_of_cols n a))^2 = (det (mat_of_cols n b))^2"
proof -
  from lattice_of_eq_gram_det_eq[OF a(1-3) b(1) _ lat_eq]
  have "det ((mat_of_cols n a)\<^sup>T * (mat_of_cols n a)) =
    det ((mat_of_cols n b)\<^sup>T * (mat_of_cols n b))"
    using a b by auto

  thus ?thesis
    by (metis assms(4) b(2) carrier_matI det_mult det_transpose index_transpose_mat(2) index_transpose_mat(3) mat_of_cols_carrier(2) mat_of_cols_carrier(3) power2_eq_square)
qed

lemma lattice_of_eq_sq_det_rows_eq:
  fixes a b::"'a vec list"
  assumes a: "distinct a" "lin_indpt (set a)" "set a \<subseteq> carrier_vec n" "length a = n"
  assumes b: "set b \<subseteq> carrier_vec n" "length b = n"
  assumes lat_eq: "lattice_of a = lattice_of b"
  shows "(det (mat_of_rows n a))^2 = (det (mat_of_rows n b))^2"
proof - 
  have transpose_mat_a: "mat_of_rows n a = transpose_mat (mat_of_cols n a)"
    by (simp add: transpose_mat_of_cols)
  have transpose_mat_b: "mat_of_rows n b = transpose_mat (mat_of_cols n b)"
    by (simp add: transpose_mat_of_cols)
  have "(det (mat_of_cols n a))\<^sup>2 = (det (mat_of_cols n b))\<^sup>2"
    using lattice_of_eq_sq_det_eq assms by blast
  then show ?thesis
  using transpose_mat_a transpose_mat_b det_transpose 
  by (metis assms(4) b(2) mat_of_rows_carrier(1) transpose_mat_of_rows)
qed

end

context LLL_with_assms
begin

text \<open> This next lemma bounds the size of the shortest vector 
  by the determinant. \<close>
lemma short_vector_det_bound:
  assumes m: "m \<noteq> 0"
  assumes k: "k \<le> m"
  shows "
    (rat_of_int \<parallel>short_vector\<parallel>\<^sup>2) ^ k \<le> 
    \<alpha> ^ (k * (k-1) div 2) * rat_of_int (gs.Gramian_determinant reduce_basis k)"
proof -

  from reduce_basis
  have rb: "lattice_of reduce_basis = L" 
    "reduced reduce_basis m" 
    "lin_indep reduce_basis" 
    "length reduce_basis = m" by auto

  have sv0: "short_vector = reduce_basis ! 0"
    using rb m unfolding short_vector_def
    by (metis hd_conv_nth list.size(3))

  have "map of_int_hom.vec_hom reduce_basis ! 0 = of_int_hom.vec_hom short_vector"
    apply (subst nth_map)
    using m by (auto simp add: sv0 rb)

  then have sve: "rat_of_int \<parallel> short_vector \<parallel>\<^sup>2 =
    \<parallel>gram_schmidt_fs.gso n (map of_int_hom.vec_hom reduce_basis) 0\<parallel>\<^sup>2"
    by (smt (verit, del_insts) LLL_invD(2) assms(1) cof_vec_space.lin_indpt_list_def gram_schmidt_fs_Rn.fs0_gso0 gram_schmidt_fs_Rn.intro not_gr0 rb(3) reduce_basis_inv sq_norm_of_int)

  from reduce_basis_inv
  have LLLi: "LLL_invariant True m reduce_basis" by auto

  then have "LLL_invariant_weak reduce_basis"
    using LLL_inv_imp_w by auto

  from Gramian_determinant[OF this k]
  have gd: "rat_of_int (gs.Gramian_determinant reduce_basis k) =
    (\<Prod>i<k.
        \<parallel>gram_schmidt_fs.gso n (map of_int_hom.vec_hom reduce_basis) i\<parallel>\<^sup>2) "
    "0 < gs.Gramian_determinant reduce_basis k" by auto
                
  have "weakly_reduced reduce_basis m"
    using LLL.LLL_invD(8) LLLi by blast

  then have *: "(\<forall> i. Suc i < m \<longrightarrow> 
   \<parallel>gram_schmidt_fs.gso n (map of_int_hom.vec_hom reduce_basis) i\<parallel>\<^sup>2 \<le>
    \<alpha> * \<parallel>gram_schmidt_fs.gso n (map of_int_hom.vec_hom reduce_basis) (Suc i)\<parallel>\<^sup>2)"
    using gram_schmidt_fs.weakly_reduced_def by blast

  have **: "i < k \<Longrightarrow>
    \<parallel>gram_schmidt_fs.gso n (map of_int_hom.vec_hom reduce_basis) 0\<parallel>\<^sup>2 \<le>
    \<alpha>^i * \<parallel>gram_schmidt_fs.gso n (map of_int_hom.vec_hom reduce_basis) i\<parallel>\<^sup>2" for i
  proof (induction i)
    case 0
    then show ?case
      by auto
  next
    case (Suc i)
    from Suc
    have 1: "\<parallel>gram_schmidt_fs.gso n (map of_int_hom.vec_hom reduce_basis) 0\<parallel>\<^sup>2
      \<le> \<alpha> ^ i * \<parallel>gram_schmidt_fs.gso n (map of_int_hom.vec_hom reduce_basis) i\<parallel>\<^sup>2"
      by auto

    have "Suc i < m"
      using Suc(2) k order_less_le_trans by blast
    then
    have "\<parallel>gram_schmidt_fs.gso n (map of_int_hom.vec_hom reduce_basis) i\<parallel>\<^sup>2
      \<le> \<alpha> * \<parallel>gram_schmidt_fs.gso n (map of_int_hom.vec_hom reduce_basis) (Suc i)\<parallel>\<^sup>2"
      by (meson "*" Suc(2) less_Suc_eq not_less_eq)

    then have 2: "\<alpha> ^ i *\<parallel>gram_schmidt_fs.gso n (map of_int_hom.vec_hom reduce_basis) i\<parallel>\<^sup>2
      \<le> \<alpha> ^ (i+1) * \<parallel>gram_schmidt_fs.gso n (map of_int_hom.vec_hom reduce_basis) (Suc i)\<parallel>\<^sup>2"
      by (simp add: \<alpha>0(1))

    show ?case using 1 2 by auto
  qed

  have "(rat_of_int \<parallel> short_vector \<parallel>\<^sup>2) ^ k =
   (\<Prod>i<k. \<parallel>gram_schmidt_fs.gso n (map of_int_hom.vec_hom reduce_basis) 0\<parallel>\<^sup>2)"
    using prod_pow sve
    by simp

  also have "... \<le> (\<Prod>i<k. \<alpha>^i * \<parallel>gram_schmidt_fs.gso n (map of_int_hom.vec_hom reduce_basis) i\<parallel>\<^sup>2)"
    apply (intro prod_mono)
    using ** by auto

  also have "... = (\<Prod>i<k. \<alpha>^i) * rat_of_int (gs.Gramian_determinant reduce_basis k)"
    unfolding gd
    by simp

  also have "... =  \<alpha>^(k * (k-1) div 2) * rat_of_int (gs.Gramian_determinant reduce_basis k)"
    unfolding power_sum[symmetric]
    by (metis Sum_Ico_nat atLeast0LessThan mult_eq_0_iff verit_minus_simplify(2))

  finally show ?thesis .
qed

lemma square_Gramian_determinant_eq_det_square:
  assumes sq:"n = m"
  shows "gs.Gramian_determinant fs_init m =
    (det (mat_of_rows m fs_init))^2"
  unfolding gs.Gramian_determinant_def
  apply (subst gs.Gramian_matrix_alt_def)
  apply (simp add: len)
  by (metis LLL_invD(9) assms det_mult det_transpose len mat_of_cols_carrier(1) mat_of_rows_carrier(1) power2_eq_square reduce_basis_inv take_all transpose_mat_of_rows)

end

end