theory Cauchy_Eigenvalue_Interlacing
  imports Misc_Matrix_Results

begin

section "Courant-Fischer Minimax Theorem"

text
  "We took inspiration from the proof given in this set of lecture notes by Dr. David Bindel:
  https://www.cs.cornell.edu/courses/cs6210/2019fa/lec/2019-11-04.pdf. In particular, the approach
  presented there explicitly obtains the eigenvector basis via diagonal decomposition, which is
  conducive to the theorems we have available."

definition sup_defined :: "'a::preorder set \<Rightarrow> bool" where
  "sup_defined S \<longleftrightarrow> S \<noteq> {} \<and> bdd_above S"

definition inf_defined :: "'a::preorder set \<Rightarrow> bool" where
  "inf_defined S \<longleftrightarrow> S \<noteq> {} \<and> bdd_below S"

locale cf_setup = cmplx_herm_mat n for n
begin

text
  "Although the @{term cf_setup} locale adds no more assumptions beyond those from the
  @{term cmplx_herm_mat} locale, we separate the Courant Fischer proof into a separate locale so that
  the terms involved in the proof (such as @{term \<Lambda>} and @{term U}) don't pollute the namespace."

definition dimensional :: "complex vec set \<Rightarrow> nat \<Rightarrow> bool" where
  "dimensional \<V> k \<longleftrightarrow> subspace class_ring \<V> V \<and> vectorspace.dim class_ring (vs \<V>) = k"

lemma dimensional_n: "dimensional \<V> k \<Longrightarrow> \<V> \<subseteq> carrier_vec n"
  unfolding dimensional_def subspace_def submodule_def by auto

lemma dimensional_n_vec: "\<And>v. v \<in> \<V> \<Longrightarrow> dimensional \<V> k \<Longrightarrow> v \<in> carrier_vec n"
  using dimensional_n by fast

text "Note here that we refer to the Inf and Sup rather than the Min and Max."

definition rayleigh_min where
  "rayleigh_min \<V> = Inf {\<rho> A v | v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V>}"

definition rayleigh_max where
  "rayleigh_max \<V> = Sup {\<rho> A v | v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V>}"

definition maximin :: "nat \<Rightarrow> real" where
  "maximin k = Sup {rayleigh_min \<V> | \<V>. dimensional \<V> k}"

definition minimax :: "nat \<Rightarrow> real" where
  "minimax k = Inf {rayleigh_max \<V> | \<V>. dimensional \<V> (n - k + 1)}"

definition maximin_defined where
  "maximin_defined k \<longleftrightarrow> sup_defined {rayleigh_min \<V> | \<V>. dimensional \<V> k}"
                               
definition minimax_defined where
  "minimax_defined k \<longleftrightarrow> inf_defined {rayleigh_max \<V> | \<V>. dimensional \<V> (n - k + 1)}"

abbreviation es :: "complex list" where "es \<equiv> eigenvalues"

definition \<Lambda>_U :: "complex mat \<times> complex mat" where
  "\<Lambda>_U \<equiv> SOME (\<Lambda>, U). real_diag_decomp A \<Lambda> U \<and> es = diag_mat \<Lambda>"

definition \<Lambda> :: "complex mat" where
  "\<Lambda> \<equiv> fst \<Lambda>_U"

definition U :: "complex mat" where
  "U \<equiv> snd \<Lambda>_U"

lemma A_decomp: "real_diag_decomp A \<Lambda> U" and es: "es = diag_mat \<Lambda>"
proof-
  obtain \<Lambda>' U' where decomp: "real_diag_decomp A \<Lambda>' U'" "diag_mat \<Lambda>' = es"
    by (meson A_dim A_herm eigenvalues hermitian_real_diag_decomp_eigvals)
  thus "real_diag_decomp A \<Lambda> U" "es = diag_mat \<Lambda>"
    unfolding \<Lambda>_def U_def \<Lambda>_U_def
    by (metis (mono_tags, lifting) someI_ex case_prod_unfold old.prod.case)+
qed

lemma U_carrier: "U \<in> carrier_mat n n" and \<Lambda>_carrier: "\<Lambda> \<in> carrier_mat n n"
  using A_decomp A_dim
  unfolding real_diag_decomp_def unitary_diag_def unitarily_equiv_def similar_mat_wit_def
  by auto+

lemma UH_carrier: "U\<^sup>H \<in> carrier_mat n n" by (simp add: U_carrier)

lemma UH_unitary: "unitary U\<^sup>H"
  by (metis A_decomp U_carrier adjoint_is_conjugate_transpose real_diag_decompD(1) unitary_adjoint unitary_diagD(3))

lemma len_U_cols: "length (cols U) = n" using U_carrier by simp

lemma dim: "local.dim = n"
  by (simp add: dim_is_n)

lemma fin_dim: "fin_dim" by simp

lemma U_cols_orthogonal_span:
  assumes I: "I \<subseteq> {0..<n}"
  assumes v: "v \<in> span {col U i | i. i \<in> I}"
  assumes j: "j \<in> {0..<n} - I"
  shows "(U\<^sup>H *\<^sub>v v)$j = 0"
proof-
  let ?\<B> = "{col U i | i. i \<in> I}"
  have v_carrier: "v \<in> carrier_vec n"
  proof-
    have "col U i \<in> carrier_vec n" if "i < n" for i
      using U_carrier col_carrier_vec that by blast
    thus ?thesis
      using v I by (smt (verit, best) atLeastLessThan_iff mem_Collect_eq span_closed subset_iff)
  qed
  have \<B>_carrier: "?\<B> \<subseteq> carrier_vec n" using U_carrier col_dim by blast
  obtain cs B where cs: "finite B" "B \<subseteq> ?\<B>" "v = lincomb cs B"
    using v[unfolded span_def] by blast

  have "(U\<^sup>H *\<^sub>v v)$j = (conjugate (col U j)) \<bullet> v" using j len_U_cols by auto
  also have "\<dots> = (\<Sum>b \<in> B. cs b * ((conjugate (col U j)) \<bullet> b))"
    apply (rule sprod_vec_sum[of v n "conjugate (col U j)" B cs])
        apply (rule v_carrier) 
    using UH_carrier
       apply fastforce   
    using \<B>_carrier cs(2)
      apply order
     apply (simp add: cs(1))
    by (simp add: cs(3) lincomb_def)
  also have "\<dots> = 0"
  proof-
    have "b \<in> B \<Longrightarrow> b \<bullet>c ((col U j)) = 0" for b
      using I j cs(2) len_U_cols A_decomp diag_decomp_ortho
      using corthogonal_matD[OF diag_decomp_ortho[OF A_decomp]]
      by (smt (verit, best) Diff_iff atLeastLessThan_iff cols_length mem_Collect_eq subsetD)
    hence "b \<in> B \<Longrightarrow> (conjugate (col U j)) \<bullet> b = 0" for b
      using U_carrier \<B>_carrier cs(2)
      by (metis (lifting) carrier_matD(1) col_dim conjugate_vec_sprod_comm subsetD)
    thus ?thesis by force
  qed
  finally show "((U\<^sup>H *\<^sub>v v)$j) = 0" by force
qed

lemma U_cols_basis:
  assumes I: "I \<subseteq> {0..<n}"
  defines [simp]: "\<B> \<equiv> {col U i | i. i \<in> I}"
  shows "\<B> \<subseteq> carrier_vec n"
        "lin_indpt \<B>"
        "card \<B> = card I"
        "vectorspace.dim class_ring (vs (span \<B>)) = card I"
proof-
  show carrier: "\<B> \<subseteq> carrier_vec n" using U_carrier \<B>_def col_dim by blast

  have "lin_indpt (set (cols U))" using A_dim diag_decomp_cols_lin_indpt[OF A_decomp] by blast
  moreover have "\<B> \<subseteq> set (cols U)"
    unfolding \<B>_def
    using I U_carrier len_U_cols
    by (smt (verit, best) cols_def cols_length image_iff list.set_map mem_Collect_eq set_upt subset_iff)
  ultimately show li: "lin_indpt \<B>" using supset_ld_is_ld by blast

  have "i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> col U i \<noteq> col U j" for i j
    using I A_decomp U_carrier
    by (metis det_identical_cols diag_decomp_invertible invertible_det lessThan_atLeast0 lessThan_iff subset_eq)
  hence "inj_on (col U) I" using I inj_on_subset unfolding inj_on_def by blast
  moreover have "\<B> = (col U)`I" unfolding \<B>_def by blast
  ultimately show "card \<B> = card I" using card_image[of "col U" I] by argo
  thus "vectorspace.dim class_ring (vs (span \<B>)) = card I"
    apply (subst dim_of_lin_indpt_span[OF li carrier])
    using I by (simp add: finite_subset)
qed

end

context cmplx_herm_mat
begin

interpretation A?: cf_setup A n by unfold_locales

text "In the local context, we interpret the @{const cf_setup} locale, giving us access to the
abbreviation @{const es} as well as other constants like @{const U} and @{const \<Lambda>} which form
the decomposition of @{term A}. Once the local context is closed, this interpretation is no
longer accessible, so these names do not pollute the @{const cmplx_herm_mat} namespace."

lemma len_eigenvalues: "length es = n"
  by (metis \<Lambda>_carrier es carrier_matD(1) diag_mat_def length_map length_upt verit_minus_simplify(2))

lemma unit_vec_rayleigh_formula:
  assumes unit_v: "vec_norm v = 1"
  assumes v_dim: "v \<in> carrier_vec n"
  shows "\<rho> A v = (\<Sum>j \<in> {..<n}. es!j * (cmod ((U\<^sup>H *\<^sub>v v)$j))^2)"
proof-
  have U_\<Lambda>: "unitary U \<and> unitary U\<^sup>H" "A = U * \<Lambda> * U\<^sup>H" "U\<^sup>H \<in> carrier_mat n n"
      apply (metis U_carrier A_decomp adjoint_is_conjugate_transpose real_diag_decomp_def unitarily_equiv_def unitary_adjoint unitary_diag_def)
     apply (metis A_decomp adjoint_is_conjugate_transpose real_diag_decomp_def similar_mat_wit_def unitarily_equiv_def unitary_diag_def)
    by (simp add: U_carrier)
  have "diagonal_mat \<Lambda>" using A_decomp unfolding real_diag_decomp_def by fastforce
  hence \<Lambda>_diag_mult: "\<And>x i. x \<in> carrier_vec n \<Longrightarrow> i \<in> {..<n} \<Longrightarrow> (\<Lambda> *\<^sub>v x)$i = (\<Lambda>$$(i,i) * x$i)"
    using \<Lambda>_carrier diagonal_mat_mult_vec by blast
  have \<Lambda>_diag_eigenvals: "\<And>i. i \<in> {..<n} \<Longrightarrow> \<Lambda>$$(i,i) = es!i"
    using A_decomp \<Lambda>_carrier by (simp add: diag_mat_def es)

  define x where "x \<equiv> U\<^sup>H *\<^sub>v v"
  hence x_dim: "x \<in> carrier_vec n" using U_\<Lambda>(3) mult_mat_vec_carrier v_dim by blast
  hence x_conj_dim: "conjugate x \<in> carrier_vec n" by simp
  have x_norm: "vec_norm x = 1" using U_\<Lambda> unit_v unitary_vec_norm v_dim x_def by presburger

  have *: "\<And>i. i \<in> {..<n} \<Longrightarrow> (conjugate x)$i = conjugate (x$i)"
    unfolding conjugate_vec_def using x_dim by auto

  have "v \<bullet>c v = 1" using unit_v csqrt_eq_1 unfolding vec_norm_def by blast
  hence "QF A v / Complex_Matrix.inner_prod v v = QF A v" by simp
  hence "\<rho> A v = complex_of_real (Re (QF A v))"
    unfolding rayleigh_quotient_def rayleigh_quotient_complex_def by simp
  also have "\<dots> = QF A v"
    using hermitian_quadratic_form_real[OF v_dim] by simp
  also have "\<dots> = inner_prod v ((U * \<Lambda> * U\<^sup>H) *\<^sub>v v)"
    unfolding quadratic_form_def using U_\<Lambda> by argo
  also have "\<dots> = inner_prod v (U *\<^sub>v ((\<Lambda> * U\<^sup>H) *\<^sub>v v))"
    by (smt (verit, best) \<Lambda>_carrier U_carrier More_Matrix.carrier_vec_conjugate assoc_mat_mult_vec' carrier_dim_vec mat_vec_mult_assoc transpose_carrier_mat v_dim)
  also have "\<dots> = inner_prod (U\<^sup>H *\<^sub>v v) ((\<Lambda> * U\<^sup>H) *\<^sub>v v)"
    by (metis \<Lambda>_carrier U_carrier More_Matrix.carrier_vec_conjugate adjoint_def_alter adjoint_is_conjugate_transpose mult_carrier_mat mult_mat_vec_carrier transpose_carrier_mat v_dim)
  also have "\<dots> = (\<Lambda> *\<^sub>v x) \<bullet>c x"
    by (metis \<Lambda>_carrier U_carrier More_Matrix.carrier_vec_conjugate carrier_vecD mat_vec_mult_assoc transpose_carrier_mat v_dim x_def)
  also have "\<dots> = (\<Sum>j \<in> {..<n}. (es!j * x$j) * conjugate (x$j))"
    using \<Lambda>_diag_mult x_dim \<Lambda>_diag_eigenvals atLeast0LessThan x_dim by (simp add: inner_prod_def scalar_prod_def)
  also have "\<dots> = (\<Sum>j \<in> {..<n}. es!j * (cmod (x$j))^2)"
    by (smt (verit) cring_simprules(11) mult_conj_cmod_square of_real_mult of_real_sum sum.cong)
  finally show "\<rho> A v = (\<Sum>j \<in> {..<n}. es!j * (cmod (x$j))^2)" 
    using of_real_eq_iff by blast
qed

lemma rayleigh_bdd_below': "\<forall>v \<in> carrier_vec n. v \<noteq> 0\<^sub>v n \<longrightarrow> \<rho> A v \<ge> Min (Re ` set es)"
proof-
  define m where "m \<equiv> Min (Re ` set es)"
  have "\<rho> A v \<ge> m" if *: "v \<in> carrier_vec n" "v \<noteq> 0\<^sub>v n" for v
  proof-
    define v' where "v' \<equiv> vec_normalize v"
    have v': "vec_norm v' = 1 \<and> v' \<in> carrier_vec n"
      using normalized_vec_norm[of v n] unfolding vec_norm_def v'_def
      using * csqrt_1 normalized_vec_dim by presburger
    have "\<rho> A v = \<rho> A v'"
      using A_dim *(1) v' v'_def
      by (metis normalize_zero rayleigh_quotient_scale_complex vec_eq_norm_smult_normalized vec_norm_zero)
    also have "\<dots> = (\<Sum>i \<in> {..<n}. es!i * (cmod ((U\<^sup>H *\<^sub>v v')$i))^2)"
      using unit_vec_rayleigh_formula * v' by blast
    also have "\<dots> \<ge> m"
    proof-
      have "vec_norm (U\<^sup>H *\<^sub>v v') = 1"
        by (metis v' U_carrier A_decomp Complex_Matrix.unitary_def adjoint_dim_row adjoint_is_conjugate_transpose carrier_matD(2) real_diag_decomp_def unitary_adjoint unitary_diagD(3) unitary_vec_norm)
      moreover have "vec_norm (U\<^sup>H *\<^sub>v v') = csqrt (\<Sum>i \<in> {..<n}. (cmod ((U\<^sup>H *\<^sub>v v')$i))^2)"
        by (metis complex_vec_norm_sum U_carrier carrier_dim_vec carrier_matD(2) dim_mult_mat_vec dim_row_conjugate index_transpose_mat(2))
      ultimately have norm: "(\<Sum>i \<in> {..<n}. (cmod ((U\<^sup>H *\<^sub>v v')$i))^2) = 1"
        by (metis Re_complex_of_real one_complex.sel(1) one_power2 power2_csqrt)

      have "finite (Re ` set es)" by simp
      hence "\<forall>x \<in> Re ` set es. m \<le> x" using Min_le m_def by blast
      moreover have "\<forall>i \<in> {..<n}. \<exists>x \<in> Re ` set es. x = es!i"
        using es eigenvalues_real len_eigenvalues by (simp add: subsetD)
      ultimately have "\<And>i. i \<in> {..<n} \<Longrightarrow> m \<le> es!i"
        by (metis Im_complex_of_real Re_complex_of_real less_eq_complex_def)
      hence ineq: "\<And>i. i \<in> {..<n} \<Longrightarrow>  m * (cmod ((U\<^sup>H *\<^sub>v v')$i))^2 \<le> es!i * (cmod ((U\<^sup>H *\<^sub>v v')$i))^2"
        by (metis conjugate_square_positive mult_conj_cmod_square mult_right_mono of_real_hom.hom_mult)
        
      have "m \<le> m * (\<Sum>i \<in> {..<n}. (cmod ((U\<^sup>H *\<^sub>v v')$i))^2)" using norm by auto
      also have "\<dots> = (\<Sum>i \<in> {..<n}. m * (cmod ((U\<^sup>H *\<^sub>v v')$i))^2)"
        by (simp add: mult_hom.hom_sum)
      also have "\<dots> \<le> (\<Sum>i \<in> {..<n}. es!i * (cmod ((U\<^sup>H *\<^sub>v v')$i))^2)"
        by (smt (verit, best) of_real_sum sum_mono ineq)
      finally show ?thesis
        by (metis Im_complex_of_real Re_complex_of_real less_eq_complex_def)
    qed
    finally show "\<rho> A v \<ge> m" by (simp add: less_eq_complex_def)
  qed
  thus ?thesis unfolding m_def by blast
qed

lemma rayleigh_bdd_below:
  assumes "dimensional \<V> k"
  shows "\<exists>m. \<forall>v \<in> \<V>. v \<noteq> 0\<^sub>v n \<longrightarrow> \<rho> A v \<ge> m"
  by (meson assms dimensional_n rayleigh_bdd_below' subsetD)

lemma rayleigh_min_exists:
  assumes "dimensional \<V> k"
  shows "\<forall>x \<in> {\<rho> A v | v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V>}. rayleigh_min \<V> \<le> x"
  using rayleigh_bdd_below[OF assms]
  unfolding rayleigh_min_def
  by (smt (verit) bdd_below.I cInf_lower mem_Collect_eq)

lemma courant_fischer_unit_rayleigh_helper1:
  assumes "dimensional \<V> (k + 1)"
  shows "\<exists>v. vec_norm v = 1 \<and> v \<in> \<V> \<and> v \<noteq> 0\<^sub>v n \<and> \<rho> A v \<le> es!k"
proof-
  define \<B>' where "\<B>' = {col U i | i. i \<in> {k..<n}}"
  have \<V>: "subspace class_ring \<V> V"
    using assms dimensional_def by blast
  have k: "k < n"
    using assms unfolding dimensional_def
    using subspace_dim[of \<V>] subspace_fin_dim[of \<V>] fin_dim dim
    by linarith
  have \<B>'_dim: "vectorspace.dim class_ring (vs (span \<B>')) = n - k" and carrier_\<B>': "\<B>' \<subseteq> carrier_vec n"
    using U_cols_basis[of "{k..<n}", folded \<B>'_def] by auto

  obtain v where v: "v \<in> \<V> \<inter> span \<B>'" and nz: "v \<noteq> 0\<^sub>v n"
    using dim_sum_nontriv_int[OF \<V> span_is_subspace[OF carrier_\<B>'] _ fin_dim, unfolded \<B>'_dim]
    using assms[unfolded dimensional_def] dim k
    by auto
  define v' where "v' \<equiv> vec_normalize v"
  have v': "vec_norm v' = 1" "v' \<in> \<V> \<inter> span \<B>'" "v' \<in> carrier_vec n"
  proof-
    have "subspace class_ring (span \<B>') V" using carrier_\<B>' span_is_subspace by presburger
    thus "v' \<in> \<V> \<inter> span \<B>'"
      using v carrier_\<B>' assms \<V>
      unfolding v'_def vec_normalize_def dimensional_def
      using assms dimensional_n module_incl_imp_submodule submoduleE(4) submodule_is_module
      by auto
    show "vec_norm v' = 1" "v' \<in> carrier_vec n"
      using v nz assms unfolding v'_def
       apply (metis IntE basic_trans_rules(31) csqrt_1 dimensional_n normalized_vec_norm vec_norm_def)
      using v nz assms unfolding v'_def
      by (meson IntE basic_trans_rules(31) dimensional_n normalized_vec_dim)
  qed

  have *: "i < k \<Longrightarrow> cmod ((U\<^sup>H *\<^sub>v v')$i) = 0" for i
    using U_cols_orthogonal_span[of "{k..<n}" v' i] k v'(2)[unfolded \<B>'_def] by force
  have "\<rho> A v' = (\<Sum>i=0..<n. es!i * complex_of_real ((cmod ((U\<^sup>H *\<^sub>v v')$i))\<^sup>2))"
    by (rule unit_vec_rayleigh_formula[OF v'(1,3), folded atLeast0LessThan])
  also have "\<dots> = (\<Sum>i=0..<k. es!i * complex_of_real ((cmod ((U\<^sup>H *\<^sub>v v')$i))\<^sup>2))
      + (\<Sum>i=k..<n. es!i * complex_of_real ((cmod ((U\<^sup>H *\<^sub>v v')$i))\<^sup>2))"
    using k by (metis (lifting) le_eq_less_or_eq sum.atLeastLessThan_concat zero_le)
  also have "\<dots> = (\<Sum>i=k..<n. es!i * complex_of_real ((cmod ((U\<^sup>H *\<^sub>v v')$i))\<^sup>2))"
    using * by fastforce
  also have "\<dots> \<le> (\<Sum>i=k..<n. es!k * complex_of_real ((cmod ((U\<^sup>H *\<^sub>v v')$i))\<^sup>2))"
  proof-
    have "\<forall>i < n. k \<le> i \<longrightarrow> es!i \<le> es!k"
      using eigenvalues_sorted by (simp add: le_eq_less_or_eq len_eigenvalues sorted_wrt_iff_nth_less)
    hence "\<forall>i \<in> {k..<n}. es!i * complex_of_real ((cmod ((U\<^sup>H *\<^sub>v v')$i))\<^sup>2)
        \<le> es ! k * complex_of_real ((cmod ((U\<^sup>H *\<^sub>v v')$i))\<^sup>2)"
      apply (clarify, simp add: atLeastLessThan_def lessThan_def atLeast_def)
      by (metis conjugate_square_positive mult_conj_cmod_square mult_right_mono of_real_power)
    thus ?thesis by (meson sum_mono)
  qed
  also have "\<dots> = es!k * (\<Sum>i=k..<n. ((cmod ((U\<^sup>H *\<^sub>v v')$i))\<^sup>2))"
    by (simp add: mult_hom.hom_sum)
  also have "\<dots> = es!k * (vec_norm (U\<^sup>H *\<^sub>v v'))\<^sup>2"
  proof-
    have 1: "U\<^sup>H *\<^sub>v v' \<in> carrier_vec n" using UH_carrier v'(3) by force
    have "(vec_norm (U\<^sup>H *\<^sub>v v'))\<^sup>2 = (\<Sum>i<n. ((cmod ((U\<^sup>H *\<^sub>v v')$i))\<^sup>2))"
      unfolding complex_vec_norm_sum[OF 1] by force
    also have "\<dots> = (\<Sum>i=0..<k. ((cmod ((U\<^sup>H *\<^sub>v v')$i))\<^sup>2)) + (\<Sum>i=k..<n. ((cmod ((U\<^sup>H *\<^sub>v v')$i))\<^sup>2))"
      using k by (metis k atLeast0LessThan le_eq_less_or_eq sum.atLeastLessThan_concat zero_order(1))
    also have "\<dots> = (\<Sum>i=k..<n. ((cmod ((U\<^sup>H *\<^sub>v v')$i))\<^sup>2))" using * by simp
    finally show ?thesis by simp
  qed
  also have "\<dots> = es!k"
    using unitary_vec_norm[OF v'(3) UH_carrier UH_unitary, unfolded v'(1)] by simp
  finally show ?thesis using v' by (metis IntE field.one_not_zero vec_norm_zero)
qed

lemma courant_fischer_unit_rayleigh_helper2:
  assumes k: "k < n"
  defines "es_R \<equiv> map Re es"
  shows "\<exists>\<V>. dimensional \<V> (k + 1) \<and> (\<forall>v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V> \<longrightarrow> es_R ! k \<le> \<rho> A v)"
proof-
  let ?geq = "\<lambda>v. \<rho> A v \<ge> es_R!k"
  let ?P = "\<lambda>\<V> v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V> \<and> vec_norm v = 1"
  let ?Q = "\<lambda>\<V>. dimensional \<V> (k + 1)"

  have es_R: "map complex_of_real es_R = es"
  proof-
    { fix i assume *: "i < length es"
      hence "es!i \<in> Reals" using eigenvalues_real by auto
      hence "complex_of_real (es_R!i) = es!i" by (simp add: * es_R_def)
    }
    thus ?thesis by (simp add: es_R_def map_nth_eq_conv)
  qed

  let ?\<B> = "{col U i | i. i \<in> {..<k + 1}}"
  define \<V> where "\<V> \<equiv> span ?\<B>"
  have \<B>_card: "card ?\<B> = k + 1" and \<B>_dim: "?\<B> \<subseteq> carrier_vec n" and 1: "?Q \<V>"
    unfolding dimensional_def \<V>_def
    using assms U_carrier U_cols_basis[of "{..<k + 1}"] 
    by (simp_all add: span_is_subspace lessThan_atLeast0)
  moreover have 2: "\<forall>v. ?P \<V> v \<longrightarrow> ?geq v"
  proof clarify
    fix v :: "complex vec"
    assume *: "v \<noteq> 0\<^sub>v n" and **: "v \<in> \<V>" and ***: "vec_norm v = 1"

    have v_dim: "v \<in> carrier_vec n" using ** \<B>_dim \<V>_def span_closed by blast

    (* cols k+1 to n of U are orthogonal to v *)
    define x where "x \<equiv> U\<^sup>H *\<^sub>v v"
    have x_dim: "x \<in> carrier_vec n"
      by (metis U_carrier More_Matrix.carrier_vec_conjugate mult_mat_vec_carrier transpose_carrier_mat v_dim x_def)
    have x_norm: "vec_norm x = 1"
      using ***
      using A_decomp[unfolded real_diag_decomp_def unitary_diag_def unitarily_equiv_def]
      using x_def x_dim v_dim
      by (metis Complex_Matrix.unitary_def adjoint_is_conjugate_transpose carrier_vecD dim_mult_mat_vec unitary_adjoint unitary_vec_norm)

    have ineq: "\<And>j. j \<in> {..<n} \<Longrightarrow> es!k * (cmod (x$j))^2 \<le> es!j * (cmod (x$j))^2"
    proof- (* case on j \<le> k *)
      fix j
      assume *: "j \<in> {..<n}"
      show "es!k * (cmod (x$j))^2 \<le> es!j * (cmod (x$j))^2"
      proof(cases "j \<le> k")
        case True
        hence "es!k \<le> es!j"
          using k by (metis len_eigenvalues antisym_conv1 eigenvalues_sorted nless_le sorted_wrt_nth_less)
        thus ?thesis by (simp add: less_eq_complex_def mult_right_mono)
      next
        case False
        hence "j > k" by simp
        hence "cmod (x$j) = 0"
          using * **[unfolded \<V>_def] assms U_cols_orthogonal_span[of "{..<k + 1}" v j, folded x_def]
          by (metis Diff_iff Suc_eq_plus1 atLeastLessThan_iff lessThan_atLeast0 lessThan_subset_iff
              less_iff_succ_less_eq norm_zero not_less_eq)
        thus ?thesis by fastforce
      qed
    qed

    have unit: "(\<Sum>j \<in> {..<n}. (cmod (x$j))^2) = 1"
      by (metis atLeast0LessThan carrier_vecD cpx_vec_length_square of_real_eq_1_iff power_one vec_norm_sq_cpx_vec_length_sq x_dim x_norm)
    have "es_R!k = es!k" using k eigenvalues_real es_R len_eigenvalues by (metis length_map nth_map)
    also have "\<dots> = es!k * (\<Sum>j \<in> {..<n}. (cmod (x$j))^2)" by (simp add: unit)
    also have "\<dots> = (\<Sum>j \<in> {..<n}. es!k * (cmod (x$j))^2)" by (simp add: mult_hom.hom_sum)
    also have "\<dots> \<le> (\<Sum>j \<in> {..<n}. es!j * (cmod (x$j))^2)" by (meson ineq sum_mono)
    also have "\<dots> = \<rho> A v" using unit_vec_rayleigh_formula A_decomp *** v_dim x_def by fastforce
    finally show "?geq v" by (simp add: less_eq_complex_def)
  qed
  ultimately have *: "dimensional \<V> (k + 1) \<and> (\<forall>v. ?P \<V> v \<longrightarrow> es_R ! k \<le> \<rho> A v)" by blast
  moreover have "\<forall>v. v \<noteq> 0\<^sub>v n \<longrightarrow> v \<in> \<V> \<longrightarrow> \<rho> A v = \<rho> A (vec_normalize v) \<and> ?P \<V> (vec_normalize v)"
  proof (clarify, rule conjI)
    fix v assume v: "v \<noteq> 0\<^sub>v n" "v \<in> \<V>"
    show "?P \<V> (vec_normalize v)"
      using 1 * v vec_normalize_norm[of v n] submodule_is_module[of \<V>]
      using vec_normalize_def[of v] dimensional_def[of \<V> "k + 1"] subspace_def[of class_ring \<V> V]
      by (metis dimensional_n dimensional_n_vec module_incl_imp_submodule rmult_0 submoduleE(4)
          vec_eq_norm_smult_normalized)
    show "\<rho> A v = \<rho> A (vec_normalize v)"
      unfolding vec_normalize_def 
      using rayleigh_quotient_scale_complex[OF A_dim, of v "1 / vec_norm v"] v * dimensional_n_vec vec_norm_zero
      by auto
  qed
  ultimately show ?thesis by metis
qed

subsection "Max-Min Statement"

proposition courant_fischer_maximin:
  assumes k: "k < n"
  shows "es!k = maximin (k + 1)"
        "maximin_defined (k + 1)"
proof-
  define es_R where "es_R \<equiv> map Re es"
  have es_R: "map complex_of_real es_R = es"
  proof-
    { fix i assume *: "i < length es"
      hence "es!i \<in> Reals" using eigenvalues_real by auto
      hence "complex_of_real (es_R!i) = es!i" by (simp add: * es_R_def)
    }
    thus ?thesis by (simp add: es_R_def map_nth_eq_conv)
  qed
  hence es_R_i: "\<And>i. i \<in> {..<n} \<Longrightarrow> es_R!i = Re (es!i)"
    using A_dim eigenvalues eigvals_poly_length es_R_def by simp
  hence es_R_k: "es_R!k = Re (es!k)" by (simp add: k)

  let ?leq = "\<lambda>v. \<rho> A v \<le> es_R!k"
  let ?geq = "\<lambda>v. \<rho> A v \<ge> es_R!k"
  let ?P = "\<lambda>\<V> v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V>"
  let ?Q = "\<lambda>\<V>. dimensional \<V> (k + 1)"
  let ?S\<^sub>\<rho> = "\<lambda>\<V>. {\<rho> A v |v. ?P \<V> v}"

  have 1: "\<And>\<V>. ?Q \<V> \<Longrightarrow> (\<exists>v. ?P \<V> v \<and> ?leq v)"
    using es_R_k by (metis Re_complex_of_real courant_fischer_unit_rayleigh_helper1 less_eq_complex_def)

  have 2: "\<exists>\<V>. ?Q \<V> \<and> (\<forall>v. ?P \<V> v \<longrightarrow> ?geq v)"
    using courant_fischer_unit_rayleigh_helper2[OF k] unfolding es_R_def by blast

  from 2 obtain \<V>' where \<V>': "?Q \<V>' \<and> (\<forall>v. ?P \<V>' v \<longrightarrow> ?geq v)" by blast
  from this 1 obtain v' where v': "?P \<V>' v' \<and> ?leq v'" by presburger
  moreover have all_v_geq: "\<forall>v. ?P \<V>' v \<longrightarrow> ?geq v" using \<V>' by blast
  ultimately have "\<rho> A v' = es_R!k" by fastforce
  hence "es_R!k \<in> ?S\<^sub>\<rho> \<V>'" using v' by force
  moreover have "\<forall>x \<in> ?S\<^sub>\<rho> \<V>'. x \<ge> es_R!k" using all_v_geq by blast
  ultimately have "es_R!k = Inf (?S\<^sub>\<rho> \<V>')" by (smt (verit) rayleigh_bdd_below cInf_eq_minimum)
  moreover have "\<And>\<V>. ?Q \<V> \<Longrightarrow> Inf (?S\<^sub>\<rho> \<V>) \<le> es_R!k"
  proof-
    fix \<V>
    assume *: "?Q \<V>"
    then obtain v where v: "?P \<V> v \<and> ?leq v" using 1 by presburger
    then have "\<rho> A v \<in> ?S\<^sub>\<rho> \<V>" by blast
    then have "Inf (?S\<^sub>\<rho> \<V>) \<le> \<rho> A v"
      using rayleigh_min_exists[OF *] k rayleigh_min_def cf_setup_axioms by auto
    thus "Inf (?S\<^sub>\<rho> \<V>) \<le> es_R!k" using v by linarith
  qed
  ultimately have *: "es_R!k \<in> {Inf (?S\<^sub>\<rho> \<V>) | \<V>. ?Q \<V>} \<and> (\<forall>x \<in> {Inf (?S\<^sub>\<rho> \<V>) | \<V>. ?Q \<V>}. x \<le> es_R!k)"
    using \<V>' by blast
  hence "Sup {Inf (?S\<^sub>\<rho> \<V>) | \<V>. ?Q \<V>} = es_R!k" by (meson cSup_eq_maximum)
  moreover have "Sup {Inf (?S\<^sub>\<rho> \<V>) | \<V>. ?Q \<V>} = maximin (k + 1)"
    unfolding maximin_def rayleigh_min_def dimensional_def by blast
  ultimately show "es!k = maximin (k + 1)"
    using k es_R by (metis len_eigenvalues length_map nth_map)
  show "maximin_defined (k + 1)"
    using * unfolding maximin_defined_def sup_defined_def rayleigh_min_def bdd_above_def by blast
qed

subsection "Min-Max Statement"

interpretation neg: cf_setup "-A" n
  by (unfold_locales, simp add: A_dim, simp add: negative_hermitian)

lemma neg_es: "neg.es = rev (map (\<lambda>x. -x) es)"
proof-
  let ?l = "(map (\<lambda>x. -x) es)"
  { fix i j assume "i < j" "j < length ?l"
    moreover then have "es!i \<ge> es!j"
      using eigenvalues_sorted sorted_wrt_iff_nth_less[of "(\<ge>)" es] by force
    ultimately have "?l!i \<le> ?l!j" by simp
  }
  hence "sorted_wrt (\<le>) ?l" by (metis sorted_wrt_iff_nth_less)
  thus ?thesis
    using sorted_wrt_rev
    by (metis A_herm hermitian_is_square neg.eigenvalues_unique neg_mat_eigvals rev_rev_ident
        eigenvalues(1))
qed

lemma maximin_minimax:
  assumes k: "k < n"
  shows "neg.maximin (n - k) = - minimax (k + 1)"
        "neg.maximin_defined (n - k) \<Longrightarrow> minimax_defined (k + 1)"
proof-
  define P where "P \<equiv> \<lambda>(v::complex vec) \<V>. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V>"
  define Q where "Q \<equiv> \<lambda>\<V>. neg.dimensional \<V> (n - k)"

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
          using * A_dim
          unfolding P_def Q_def
          by (metis dimensional_n_vec rayleigh_quotient_negative)
        thus ?thesis by metis
      qed
      ultimately show "- Sup {\<rho> A v |v. P v \<V>} = Inf {\<rho> (-A) v |v. P v \<V>}" by presburger
    qed
    thus ?thesis by force
  qed
  ultimately have "- Inf {Sup {\<rho> A v |v. P v \<V>} |\<V>. Q \<V>} = Sup {Inf {\<rho> (-A) v |v. P v \<V>} |\<V>. Q \<V>}"
    by auto
  moreover have "n - (k + 1) + 1 = n - k" using k by fastforce
  ultimately show "cf_setup.maximin (-A) n (n - k) = - cf_setup.minimax A n (k + 1)"
    by (simp add: minimax_def neg.maximin_def neg.rayleigh_min_def rayleigh_max_def P_def Q_def)

  show "cf_setup.minimax_defined A n (k + 1)" if "cf_setup.maximin_defined (-A) n (n - k)"
  proof-
    have "{Sup {\<rho> A v |v. P v \<V>} |\<V>. Q \<V>} \<noteq> {}"
      using that
      unfolding neg.maximin_defined_def sup_defined_def neg.rayleigh_min_def P_def Q_def
      by fast
    moreover have "bdd_below {Sup {\<rho> A v |v. P v \<V>} |\<V>. Q \<V>}"
    proof-
      have "bdd_above {Inf {\<rho> (-A) v |v. P v \<V>} |\<V>. Q \<V>}"
        using that
        unfolding neg.maximin_defined_def sup_defined_def neg.rayleigh_min_def P_def Q_def
        by argo
      hence "bdd_above {- Sup {\<rho> A v |v. P v \<V>} |\<V>. Q \<V>}" using ** by argo
      hence "bdd_below {Sup {\<rho> A v |v. P v \<V>} |\<V>. Q \<V>}" by (smt (verit, best) * bdd_above_uminus)
      thus ?thesis by blast
    qed
    moreover have "n - k = n - (k + 1) + 1" using k by simp
    ultimately show ?thesis
      unfolding minimax_defined_def inf_defined_def rayleigh_max_def P_def Q_def by algebra
  qed
qed

lemma courant_fischer_minimax:
  assumes k: "k < n"
  shows "es!k = minimax (k + 1)" "minimax_defined (k + 1)"
proof-
  define es' where "es' = rev (map (\<lambda>x. -x) es)"
  have *: "es'!(n - k - 1) = neg.maximin (n - k)
      \<and> neg.maximin_defined (n - k)"
    using k neg.courant_fischer_maximin[of "n - k - 1"]
    using neg.eigenvalues_unique neg_es es'_def
    by (metis One_nat_def Suc_diff_Suc Suc_less_eq diff_less_Suc minus_nat.simps(1) semiring_norm(174)
        zero_less_diff)
  moreover have "es!k = - es'!(n - k - 1)"
  proof-
    have "n - k - 1 < length es" using k A_dim eigenvalues eigvals_poly_length by force
    moreover have "length es = n" using A_dim eigenvalues by auto
    ultimately have "es!k = (rev es)!(n - k - 1)"
      using rev_nth[of "n - k - 1" es] by (simp add: Suc_diff_Suc k le_simps(1))
    also have "\<dots> = rev (map (\<lambda>x. -x) (map (\<lambda>x. -x) es))!(n - k - 1)"
      by simp
    also have "\<dots> = - es'!(n - k - 1)"
      by (metis \<open>n - k - 1 < length es\<close> es'_def length_map length_rev nth_map rev_map)
    finally show ?thesis .
  qed
  ultimately show "es!k = cf_setup.minimax A n (k + 1)" "cf_setup.minimax_defined A n (k + 1)"
    using assms maximin_minimax by force+
qed

subsection "Theorem Statement"

theorem courant_fischer:
  assumes "k < n"
  shows "es!k = minimax (k + 1)"
        "es!k = maximin (k + 1)"
        "minimax_defined (k + 1)"
        "maximin_defined (k + 1)"
  using courant_fischer_minimax courant_fischer_maximin maximin_minimax assms by algebra+

section "Cauchy Eigenvalue Interlacing Theorem"

text
  "We follow the proof given in this set of lecture notes by Dr. David Bindel:
  https://www.cs.cornell.edu/courses/cs6210/2019fa/lec/2019-11-04.pdf"

subsection "Theorem Statement and Proof"

lemma cauchy_eigval_interlacing_aux:
  fixes W B :: "complex mat"
  fixes \<alpha> \<beta> :: "complex list"
  fixes j m :: nat

  defines "B \<equiv> W\<^sup>H * A * W"
  defines "\<alpha> \<equiv> eigenvalues"
  defines "\<beta> \<equiv> cmplx_herm_mat.eigenvalues B"

  assumes j: "j < n" "j < m"
  assumes m: "0 < m" "m \<le> n"

  assumes W_dim: "W \<in> carrier_mat n m"
  assumes W_isom: "isometry_mat W n m"

  shows "\<beta>!j \<le> \<alpha>!j" "set \<alpha> \<subseteq> \<real>" "set \<beta> \<subseteq> \<real>" "length \<alpha> = n" "length \<beta> = m"
proof-
  interpret B: cf_setup B m
    using A_dim A_herm W_dim B_def compression_is_hermitian(1)
    by (metis carrier_matD(2) carrier_mat_triv cmplx_herm_mat.intro
         cf_setup.intro dim_row_conjugate index_mult_mat(2,3) index_transpose_mat(2))

  show \<alpha>_real: "set \<alpha> \<subseteq> \<real>"
    using hermitian_real_diag_decomp_eigvals[OF A_dim A_herm] \<alpha>_def eigenvalues(1) by metis
  show \<beta>_real: "set \<beta> \<subseteq> \<real>"
    using hermitian_real_diag_decomp_eigvals[of B n \<beta>] B.eigenvalues(1) \<beta>_def
    by (metis B.A_dim B.A_herm hermitian_real_diag_decomp_eigvals)
  show \<alpha>_length: "length \<alpha> = n" using \<alpha>_def eigenvalues(1) A_dim \<alpha>_def by auto
  have "B \<in> carrier_mat m m" by (simp add: B.A_dim)
  show \<beta>_length: "length \<beta> = m" using B.A_dim B.eigenvalues(1) \<beta>_def by fastforce

  let ?S\<^sub>1 = "{B.rayleigh_min \<V> | \<V>. B.dimensional \<V> (j + 1)}"
  let ?S\<^sub>2 = "{A.rayleigh_min ((*\<^sub>v) W ` \<V>) |\<V>. B.dimensional \<V> (j + 1)}"
  let ?S\<^sub>3 = "{A.rayleigh_min \<V> | \<V>. A.dimensional \<V> (Suc j)}"

  interpret isom: isometry_mat W n m by (rule W_isom)
  have *: "\<And>\<V>. B.dimensional \<V> (Suc j) \<Longrightarrow> A.dimensional ((*\<^sub>v) W ` \<V>) (Suc j)"
  proof-
    fix \<V> assume *: "B.dimensional \<V> (Suc j)"
    note Bdim =
      conjunct1[OF *[unfolded B.dimensional_def]]
      conjunct2[OF *[unfolded B.dimensional_def]]
    show "A.dimensional ((*\<^sub>v) W ` \<V>) (Suc j)"
      unfolding A.dimensional_def isom.inj_subspace_image[OF isom.is_inj Bdim(1) B.fin_dim] Bdim(2)
      using isom.subspace_image[OF Bdim(1)]
      by blast
  qed
  hence S\<^sub>2_sub_S\<^sub>3: "?S\<^sub>2 \<subseteq> ?S\<^sub>3" by auto
  have bdd_above_S\<^sub>3: "bdd_above ?S\<^sub>3"
    using j(1) courant_fischer \<alpha>_def
    by (metis (lifting) ext A.maximin_defined_def Suc_eq_plus1 sup_defined_def)
  hence bdd_above_S\<^sub>2: "bdd_above ?S\<^sub>2"
    using S\<^sub>2_sub_S\<^sub>3 by (meson basic_trans_rules(31) bdd_above_def)
  have S\<^sub>2_ne: "?S\<^sub>2 \<noteq> {}"
    using j(2)
    by (metis (mono_tags, lifting) B.courant_fischer_unit_rayleigh_helper2 empty_Collect_eq)

  have "Re (\<beta>!j) = B.maximin (j + 1)"
    using B.courant_fischer(2)[OF j(2)] \<beta>_def by simp
  also have "\<dots> \<le> Sup {A.rayleigh_min ((\<lambda>v. W *\<^sub>v v)`\<V>) | \<V>. B.dimensional \<V> (j + 1)}"
  proof-
    note 1 = bdd_above_S\<^sub>2
    have 2: "\<forall>y \<in> ?S\<^sub>1. \<exists>x \<in> ?S\<^sub>2. y \<le> x"
    proof clarify
      fix \<V> assume dim: "B.dimensional \<V> (j + 1)"
      define \<V>' where "\<V>' \<equiv> (*\<^sub>v) W ` \<V>"
      have dim_\<V>': "A.dimensional \<V>' (j + 1)" using *[OF dim[simplified], folded \<V>'_def] by fastforce

      define x :: real where "x \<equiv> A.rayleigh_min \<V>'"
      have "x \<in> ?S\<^sub>2" unfolding x_def \<V>'_def using dim by blast
      moreover have "B.rayleigh_min \<V> \<le> x"
      proof-
        have le: "\<And>x. x \<in> {v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V>'} \<Longrightarrow> B.rayleigh_min \<V> \<le> \<rho> A x"
        proof-
          fix x assume x: "x \<in> {v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V>'}"
          then obtain v where xv: "x = W *\<^sub>v v" and v: "v \<in> \<V>" and v_nz: "v \<noteq> 0\<^sub>v m"
            unfolding \<V>'_def using that isom.T0_is_0 by fastforce

          have 1: "inner_prod (W *\<^sub>v v) (A *\<^sub>v (W *\<^sub>v v)) = inner_prod v ((W\<^sup>H * A * W *\<^sub>v v))"
          proof-
            have "inner_prod (W *\<^sub>v v) (A *\<^sub>v (W *\<^sub>v v)) = inner_prod v (W\<^sup>H *\<^sub>v (A *\<^sub>v (W *\<^sub>v v)))"
              using W_dim v dim
              by (meson A_dim B.cmplx_herm_mat_axioms cscalar_prod_conjugate_transpose
                  B.dimensional_n_vec mult_mat_vec_carrier)
            also have "\<dots> = inner_prod v ((W\<^sup>H * A * W) *\<^sub>v v)"
              using W_dim A_dim v dim
              by (smt (verit, ccfv_SIG) B.dimensional_n_vec More_Matrix.carrier_vec_conjugate assoc_mult_mat_vec mult_carrier_mat
                  mult_mat_vec_carrier transpose_carrier_mat)
            finally show ?thesis .
          qed
          have 2: "inner_prod (W *\<^sub>v v) (W *\<^sub>v v) = inner_prod v v"
            using isom.preserves_norm v dim by (metis B.dimensional_n_vec inner_prod_vec_norm_pow2)
          have bdd: "bdd_below {\<rho> B v |v. v \<noteq> 0\<^sub>v m \<and> v \<in> \<V>}"
            using B.rayleigh_bdd_below' dim[unfolded B.dimensional_def subspace_def submodule_def]
            unfolding bdd_below_def
            by auto
          have "\<rho> A x = \<rho> A (W *\<^sub>v v)" unfolding xv ..
          also have "\<dots> = \<rho> B v"
            unfolding rayleigh_quotient_def rayleigh_quotient_complex_def B_def quadratic_form_def 1 2 ..
          finally show "B.rayleigh_min \<V> \<le> \<rho> A x"
            unfolding B.rayleigh_min_def
            using v v_nz bdd
            by (metis (mono_tags, lifting) cInf_lower mem_Collect_eq)
        qed
        have ne: "{v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V>'} \<noteq> {}"
          using dim_\<V>'[unfolded A.dimensional_def] nontriv_subspace_exists by fastforce
        have set_rw: "{\<rho> A v |v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V>'} = \<rho> A ` {v. v \<noteq> 0\<^sub>v n \<and> v \<in> \<V>'}" by blast
        show ?thesis
          unfolding x_def A.rayleigh_min_def set_rw
          by (rule cINF_greatest[OF ne, of "B.rayleigh_min \<V>" "\<lambda>v. \<rho> A v"], rule le)
      qed
      ultimately show "\<exists>x \<in> ?S\<^sub>2. B.rayleigh_min \<V> \<le> x" by blast
    qed
    have 3: "?S\<^sub>1 \<noteq> {}" using S\<^sub>2_ne by blast
    show ?thesis
      apply (simp add: B.maximin_def)
      using 1 2 3 by (metis (lifting) ext Suc_eq_plus1 cSup_mono) 
  qed
  also have "\<dots> \<le> Sup {A.rayleigh_min \<V> | \<V>. A.dimensional \<V> (j + 1)}"
    by (metis (no_types, lifting) ext S\<^sub>2_ne S\<^sub>2_sub_S\<^sub>3 Suc_eq_plus1 bdd_above_S\<^sub>3 cSup_subset_mono)
  also have "\<dots> = Re (\<alpha>!j)"
    using bdd_above_S\<^sub>3 \<alpha>_def courant_fischer(2)[OF j(1), unfolded A.maximin_def] by force
  finally have "Re (\<beta>!j) \<le> Re (\<alpha>!j)" .
  moreover have "\<alpha>!j \<in> \<real>" using \<alpha>_real \<alpha>_length j(1) by fastforce
  moreover have "\<beta>!j \<in> \<real>" using \<beta>_real \<beta>_length j(2) by fastforce
  ultimately show "\<beta>!j \<le> \<alpha>!j" by (simp add: complex_is_Real_iff less_eq_complex_def)
qed

theorem cauchy_eigval_interlacing:
  fixes W B :: "complex mat"
  fixes \<alpha> \<beta> :: "complex list"
  fixes j m :: nat

  defines "B \<equiv> W\<^sup>H * A * W"
  defines "\<alpha> \<equiv> eigenvalues"
  defines "\<beta> \<equiv> cmplx_herm_mat.eigenvalues B"

  assumes j: "j < n" "j < m"
  assumes m: "0 < m" "m \<le> n"
  assumes W_dim: "W \<in> carrier_mat n m"
  assumes W_isom: "isometry_mat W n m"

  shows "\<alpha>!(n - m + j) \<le> \<beta>!j" "\<beta>!j \<le> \<alpha>!j" "set \<alpha> \<subseteq> \<real>" "set \<beta> \<subseteq> \<real>" "length \<alpha> = n" "length \<beta> = m"
proof-
  interpret B: cf_setup B m
    apply unfold_locales
    using A_dim A_herm W_dim B_def compression_is_hermitian
    by auto
  show "\<beta>!j \<le> \<alpha>!j" "set \<alpha> \<subseteq> \<real>" "set \<beta> \<subseteq> \<real>" and lengths: "length \<alpha> = n" "length \<beta> = m"
    by (rule cauchy_eigval_interlacing_aux[OF j m W_dim W_isom, folded B_def \<alpha>_def \<beta>_def])+

  define A' where "A' \<equiv> - A"
  interpret A': cf_setup A' n
    using A_dim A_herm negative_hermitian by (unfold_locales, auto simp add: A'_def)
  define B' where "B' \<equiv> W\<^sup>H * A' * W"
  have neg_B: "B' = - B" unfolding B'_def A'_def B_def using W_dim A_dim by force
  then interpret B': cf_setup B' m
    by (simp add: B.A_dim B.negative_hermitian cmplx_herm_mat.intro cf_setup.intro)
  define \<alpha>' where "\<alpha>' = A'.es"
  define \<beta>' where "\<beta>' \<equiv> B'.es"

  let ?j' = "m - j - 1"
  have j': "?j' < n" "?j' < m" using m by simp_all
  have "\<alpha>!(n - m + j) = - \<alpha>' ! (m - j - 1)"
    using lengths(1) m j j' neg_es[folded A'_def] by (simp add: \<alpha>'_def \<alpha>_def rev_nth)
  moreover have "\<beta>!j = - \<beta>' ! (m - j - 1)"
    using lengths(2) m j j' neg_es
    by (simp add: \<beta>'_def \<beta>_def B.neg_es Suc_diff_Suc neg_B rev_nth)
  ultimately show "\<alpha>!(n - m + j) \<le> \<beta>!j"
    using cmplx_herm_mat.cauchy_eigval_interlacing_aux(1)
      [ OF A'.cmplx_herm_mat_axioms j' m W_dim W_isom, folded B'_def]
    unfolding \<beta>'_def \<alpha>'_def A'_def B'_def
    by force
qed

subsection "Principal Submatrix Corollaries (Using @{const pick} Function)"

corollary submatrix_eigval_interlacing:
  fixes I :: "nat set"

  defines "B \<equiv> submatrix A I I"
  defines "m \<equiv> card I"
  defines "\<alpha> \<equiv> eigenvalues"
  defines "\<beta> \<equiv> cmplx_herm_mat.eigenvalues B"

  assumes j: "j < m"
  assumes I: "I \<subseteq> {..<n}" "I \<noteq> {}" 

  shows "\<alpha>!(n - m + j) \<le> \<beta>!j" "\<beta>!j \<le> \<alpha>!j" "set \<alpha> \<subseteq> \<real>" "set \<beta> \<subseteq> \<real>" "length \<alpha> = n" "length \<beta> = m"
proof-
  obtain Q where Q: "B = Q\<^sup>H * A * Q" "isometry_mat Q n m"
    using A_dim I B_def m_def submatrix_as_compression_obt by blast
  have Q_carrier: "Q \<in> carrier_mat n m"
    using Q(2)[unfolded isometry_mat_def mat_as_linear_map_def] ..

  interpret B: cf_setup B m
    apply unfold_locales
    using A_dim A_herm B_def Q compression_is_hermitian(2)
     apply (metis Q_carrier)
    by (simp add: I(1) B_def principal_submatrix_hermitian)

  have 1: "j < n"
    using j m_def I(1)
    by (metis atLeast0LessThan dual_order.strict_trans le_eq_less_or_eq subset_eq_atLeast0_lessThan_card)
  have 2: "0 < m" using j by linarith
  have 3: "m \<le> n"
    using I(1) m_def atLeast0LessThan subset_eq_atLeast0_lessThan_card by presburger

  show "\<alpha>!(n - m + j) \<le> \<beta>!j" "\<beta>!j \<le> \<alpha>!j" "set \<alpha> \<subseteq> \<real>" "set \<beta> \<subseteq> \<real>" "length \<alpha> = n" "length \<beta> = m"
    using cauchy_eigval_interlacing[OF 1 j 2 3 Q_carrier Q(2)]
    unfolding Q(1)[symmetric]
    by (simp_all add: \<alpha>_def \<beta>_def)
qed

subsection "Principal Submatrix Corollary (as Injective Function on Indices)"

corollary submatrix_eigval_interlacing':
  fixes B :: "complex mat"
  fixes m :: "nat"
  fixes f :: "nat \<Rightarrow> nat"

  defines "B \<equiv> submatrix_of_inj A f f m m"
  defines "\<alpha> \<equiv> eigenvalues"
  defines "\<beta> \<equiv> cmplx_herm_mat.eigenvalues B"

  assumes f: "f : {..<m} \<rightarrow> {..<n}"
  assumes inj: "inj_on f {..<m}"
  assumes j: "j < m"

  shows "\<alpha>!(n - m + j) \<le> \<beta>!j" "\<beta>!j \<le> \<alpha>!j" "set \<alpha> \<subseteq> \<real>" "set \<beta> \<subseteq> \<real>" "length \<alpha> = n" "length \<beta> = m"
proof-
  obtain Q where Q: "B = Q\<^sup>H * A * Q" "isometry_mat Q n m"
    using f inj \<alpha>_def B_def submatrix_of_inj_as_compression_obt by (metis A_dim)
  have Q_carrier: "Q \<in> carrier_mat n m"
    using Q(2)[unfolded isometry_mat_def mat_as_linear_map_def] ..

  interpret B: cf_setup B m
    apply unfold_locales
    using A_dim A_herm B_def Q compression_is_hermitian Q_carrier
    by meson+

  note 3 = card_inj[OF f inj, simplified]
  hence 1: "j < n" using j by auto
  have 2: "0 < m" using j by linarith
  show "\<alpha>!(n - m + j) \<le> \<beta>!j" "\<beta>!j \<le> \<alpha>!j" "set \<alpha> \<subseteq> \<real>" "set \<beta> \<subseteq> \<real>" "length \<alpha> = n" "length \<beta> = m"
    using \<alpha>_def \<beta>_def Q(1) cauchy_eigval_interlacing[OF 1 j 2 3 Q_carrier Q(2)] by fastforce+
qed

end

section "Theorem Statements (Outside Locale)"

theorem courant_fischer:
  fixes A :: "complex mat"

  defines "es \<equiv> cmplx_herm_mat.eigenvalues A"

  assumes carrier: "A \<in> carrier_mat n n"
  assumes herm: "hermitian A"
  assumes k: "k < n"

  shows "es!k = cf_setup.minimax A n (k + 1)"
        "es!k = cf_setup.maximin A n (k + 1)"
        "cf_setup.minimax_defined A n (k + 1)"
        "cf_setup.maximin_defined A n (k + 1)"
  by (rule cmplx_herm_mat.courant_fischer
      [OF cmplx_herm_mat.intro, OF carrier herm k, folded es_def])+

theorem cauchy_eigval_interlacing:
  fixes A W B :: "complex mat"
  fixes \<alpha> \<beta> :: "complex list"
  fixes j m n :: nat

  defines "B \<equiv> W\<^sup>H * A * W"
  defines "\<alpha> \<equiv> cmplx_herm_mat.eigenvalues A"
  defines "\<beta> \<equiv> cmplx_herm_mat.eigenvalues B"

  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  assumes j: "j < n" "j < m"
  assumes m: "0 < m" "m \<le> n"
  assumes W_dim: "W \<in> carrier_mat n m"
  assumes W_isom: "isometry_mat W n m"

  shows "\<alpha>!(n - m + j) \<le> \<beta>!j" "\<beta>!j \<le> \<alpha>!j" "set \<alpha> \<subseteq> \<real>" "set \<beta> \<subseteq> \<real>" "length \<alpha> = n" "length \<beta> = m"
  by (rule cmplx_herm_mat.cauchy_eigval_interlacing
      [OF cmplx_herm_mat.intro, OF A j m W_dim W_isom, folded B_def \<alpha>_def \<beta>_def])+

corollary submatrix_eigval_interlacing:
  fixes A :: "complex mat"
  fixes I :: "nat set"

  defines "B \<equiv> submatrix A I I"
  defines "m \<equiv> card I"
  defines "\<alpha> \<equiv> cmplx_herm_mat.eigenvalues A"
  defines "\<beta> \<equiv> cmplx_herm_mat.eigenvalues B"

  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  assumes j: "j < m"
  assumes I: "I \<subseteq> {..<n}" "I \<noteq> {}" 

  shows "\<alpha>!(n - m + j) \<le> \<beta>!j" "\<beta>!j \<le> \<alpha>!j" "set \<alpha> \<subseteq> \<real>" "set \<beta> \<subseteq> \<real>" "length \<alpha> = n" "length \<beta> = m"
  by (rule cmplx_herm_mat.submatrix_eigval_interlacing
      [OF cmplx_herm_mat.intro, of A n j I, folded B_def m_def \<alpha>_def \<beta>_def, OF A j I])+

corollary submatrix_eigval_interlacing':
  fixes A B :: "complex mat"
  fixes m :: "nat"
  fixes f :: "nat \<Rightarrow> nat"

  defines "B \<equiv> submatrix_of_inj A f f m m"
  defines "\<alpha> \<equiv> cmplx_herm_mat.eigenvalues A"
  defines "\<beta> \<equiv> cmplx_herm_mat.eigenvalues B"

  assumes A: "A \<in> carrier_mat n n" "hermitian A"
  assumes f: "f : {..<m} \<rightarrow> {..<n}"
  assumes inj: "inj_on f {..<m}"
  assumes j: "j < m"

  shows "\<alpha>!(n - m + j) \<le> \<beta>!j" "\<beta>!j \<le> \<alpha>!j" "set \<alpha> \<subseteq> \<real>" "set \<beta> \<subseteq> \<real>" "length \<alpha> = n" "length \<beta> = m"
  by (rule cmplx_herm_mat.submatrix_eigval_interlacing'
      [OF cmplx_herm_mat.intro, of A n f m, folded B_def \<alpha>_def \<beta>_def, OF A f inj j])+

end