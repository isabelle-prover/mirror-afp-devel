section \<open>Spectral Theory\label{sec:expander_eigenvalues}\<close>

text \<open>This section establishes the correspondence of the variationally defined expansion paramters 
with the definitions using the spectrum of the stochastic matrix. Additionally stronger 
results for the expansion parameters are derived.\<close>

theory Expander_Graphs_Eigenvalues
  imports 
    Expander_Graphs_Algebra
    Expander_Graphs_TTS 
    Perron_Frobenius.HMA_Connect
    Commuting_Hermitian.Commuting_Hermitian
begin

unbundle intro_cong_syntax

hide_const Matrix_Legacy.transpose
hide_const Matrix_Legacy.row
hide_const Matrix_Legacy.mat
hide_const Matrix.mat
hide_const Matrix.row
hide_fact Matrix_Legacy.row_def
hide_fact Matrix_Legacy.mat_def
hide_fact Matrix.vec_eq_iff
hide_fact Matrix.mat_def
hide_fact Matrix.row_def
no_notation Matrix.scalar_prod  (infix "\<bullet>" 70)
no_notation Ordered_Semiring.max ("Max\<index>")

lemma mult_right_mono': "y \<ge> (0::real) \<Longrightarrow> x \<le> z \<or> y = 0 \<Longrightarrow> x * y \<le> z * y"  
  by (metis mult_cancel_right mult_right_mono)

lemma poly_prod_zero:
  fixes x :: "'a :: idom"
  assumes "poly (\<Prod>a\<in>#xs. [:- a, 1:]) x = 0"
  shows "x \<in># xs"
  using assms by (induction xs, auto)

lemma poly_prod_inj_aux_1:
  fixes xs ys :: "('a :: idom) multiset"
  assumes "x \<in># xs"
  assumes "(\<Prod>a\<in>#xs. [:- a, 1:]) = (\<Prod>a\<in>#ys. [:- a, 1:])"
  shows "x \<in># ys"
proof -
  have "poly (\<Prod>a\<in>#ys. [:- a, 1:]) x = poly (\<Prod>a\<in>#xs. [:- a, 1:]) x" using assms(2) by simp
  also have "... = poly (\<Prod>a\<in>#xs - {#x#} + {#x#}. [:- a, 1:]) x"
    using assms(1) by simp
  also have "... = 0"
    by simp
  finally have "poly (\<Prod>a\<in>#ys. [:- a, 1:]) x = 0" by simp
  thus "x \<in># ys" using poly_prod_zero by blast
qed

lemma poly_prod_inj_aux_2:
  fixes xs ys :: "('a :: idom) multiset"
  assumes "x \<in># xs \<union># ys"
  assumes "(\<Prod>a\<in>#xs. [:- a, 1:]) = (\<Prod>a\<in>#ys. [:- a, 1:])"
  shows "x \<in># xs \<inter># ys"
proof (cases "x \<in># xs")
  case True
  then show ?thesis using poly_prod_inj_aux_1[OF True assms(2)] by simp
next
  case False
  hence a:"x \<in># ys"
    using assms(1) by simp
  then show ?thesis 
    using poly_prod_inj_aux_1[OF a assms(2)[symmetric]] by simp
qed

lemma poly_prod_inj:
  fixes xs ys :: "('a :: idom) multiset"
  assumes "(\<Prod>a\<in>#xs. [:- a, 1:]) = (\<Prod>a\<in>#ys. [:- a, 1:])"
  shows "xs = ys"
  using assms
proof (induction "size xs + size ys" arbitrary: xs ys rule:nat_less_induct)
  case 1
  show ?case
  proof (cases "xs \<union># ys = {#}")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain x where "x \<in># xs \<union># ys" by auto
    hence a:"x \<in># xs \<inter># ys"
      by (intro poly_prod_inj_aux_2[OF _ 1(2)])
    have b: "[:- x, 1:] \<noteq> 0" 
      by simp
    have c: "size (xs-{#x#}) + size (ys-{#x#}) < size xs + size ys" 
      using a by (simp add: add_less_le_mono size_Diff1_le size_Diff1_less)

    have "[:- x, 1:] * (\<Prod>a\<in>#xs - {#x#}. [:- a, 1:]) = (\<Prod>a\<in>#xs. [:- a, 1:])"
      using a by (subst prod_mset.insert[symmetric]) simp
    also have "... = (\<Prod>a\<in>#ys. [:- a, 1:])" using 1 by simp
    also have "... = [:- x, 1:] * (\<Prod>a\<in>#ys - {#x#}. [:- a, 1:])"
      using a by (subst prod_mset.insert[symmetric]) simp
    finally have "[:- x, 1:]*(\<Prod>a\<in>#xs-{#x#}. [:- a, 1:])=[:-x, 1:]*(\<Prod>a\<in>#ys-{#x#}. [:- a, 1:])"
      by simp
    hence "(\<Prod>a\<in>#xs-{#x#}. [:- a, 1:]) = (\<Prod>a\<in>#ys-{#x#}. [:- a, 1:])" 
      using mult_left_cancel[OF b] by simp
    hence d:"xs - {#x#} = ys - {#x#}"
      using 1 c by simp
    have "xs = xs - {#x#} + {#x#}"
      using a by simp
    also have "... = ys - {#x#} + {#x#}"
      unfolding d by simp
    also have "... = ys"
      using a by simp
    finally show ?thesis by simp
  qed
qed

definition eigenvalues :: "('a::comm_ring_1)^'n^'n \<Rightarrow> 'a multiset" 
  where 
    "eigenvalues A = (SOME as. charpoly A = (\<Prod>a\<in>#as. [:- a, 1:]) \<and> size as = CARD ('n))"

lemma char_poly_factorized_hma: 
  fixes A :: "complex^'n^'n"
  shows "\<exists>as. charpoly A = (\<Prod>a\<leftarrow>as. [:- a, 1:]) \<and> length as = CARD ('n)"
  by (transfer_hma rule:char_poly_factorized)

lemma eigvals_poly_length:
  fixes A :: "complex^'n^'n"
  shows 
    "charpoly A = (\<Prod>a\<in>#eigenvalues A. [:- a, 1:])" (is "?A") 
    "size (eigenvalues A) = CARD ('n)" (is "?B")
proof -
  define f where "f as = (charpoly A = (\<Prod>a\<in>#as. [:- a, 1:]) \<and> size as = CARD('n))" for as
  obtain as where as_def: "charpoly A = (\<Prod>a\<leftarrow>as. [:- a, 1:])" "length as = CARD('n)"
    using char_poly_factorized_hma by auto

  have "charpoly A = (\<Prod>a\<leftarrow>as. [:- a, 1:])"
    unfolding as_def by simp
  also have "... = (\<Prod>a\<in>#mset as. [:- a, 1:])" 
    unfolding prod_mset_prod_list[symmetric] mset_map by simp
  finally have "charpoly A = (\<Prod>a\<in>#mset as. [:- a, 1:])" by simp
  moreover have "size (mset as)  = CARD('n)"
    using as_def by simp
  ultimately have "f (mset as)" 
    unfolding f_def by auto
  hence "f (eigenvalues A)" 
    unfolding eigenvalues_def f_def[symmetric] using someI[where x = "mset as" and P="f"] by auto
  thus ?A ?B
    unfolding f_def by auto
qed

lemma similar_matrix_eigvals:
  fixes A B :: "complex^'n^'n"
  assumes "similar_matrix A B"
  shows "eigenvalues A = eigenvalues B"
proof -
  have "(\<Prod>a\<in>#eigenvalues A. [:- a, 1:]) = (\<Prod>a\<in>#eigenvalues B. [:- a, 1:])"
    using similar_matrix_charpoly[OF assms] unfolding eigvals_poly_length(1) by simp
  thus ?thesis
    by (intro poly_prod_inj) simp
qed

definition upper_triangular_hma :: "'a::zero^'n^'n \<Rightarrow> bool"
  where "upper_triangular_hma A \<equiv>
    \<forall>i. \<forall> j. (to_nat j < Bij_Nat.to_nat i \<longrightarrow> A $h i $h j = 0)"

lemma for_all_reindex2:
  assumes "range f = A"
  shows "(\<forall>x \<in> A. \<forall>y \<in> A. P x y) \<longleftrightarrow> (\<forall>x y. P (f x) (f y))"
  using assms by auto

lemma upper_triangular_hma: 
  fixes A :: "('a::zero)^'n^'n"
  shows "upper_triangular (from_hma\<^sub>m A) = upper_triangular_hma A" (is "?L = ?R")
proof -
  have "?L \<longleftrightarrow> (\<forall>i\<in>{0..<CARD('n)}. \<forall>j\<in>{0..<CARD('n)}. j < i \<longrightarrow> A $h from_nat i $h from_nat j = 0)"
    unfolding upper_triangular_def from_hma\<^sub>m_def by auto
  also have "... \<longleftrightarrow>  (\<forall>(i::'n) (j::'n). to_nat j < to_nat i \<longrightarrow> A $h from_nat (to_nat i) $h from_nat (to_nat j) = 0)"
    by (intro for_all_reindex2 range_to_nat[where 'a="'n"])
  also have "... \<longleftrightarrow>  ?R"
    unfolding upper_triangular_hma_def by auto
  finally show ?thesis by simp
qed

lemma from_hma_carrier: 
  fixes A :: "'a^('n::finite)^('m::finite)"
  shows "from_hma\<^sub>m A \<in> carrier_mat (CARD ('m)) (CARD ('n))"
  unfolding from_hma\<^sub>m_def by simp

definition diag_mat_hma :: "'a^'n^'n \<Rightarrow> 'a multiset"
  where "diag_mat_hma A = image_mset (\<lambda>i. A $h i $h i)  (mset_set UNIV)"

lemma diag_mat_hma: 
  fixes A :: "'a^'n^'n"
  shows  "mset (diag_mat (from_hma\<^sub>m A)) = diag_mat_hma A" (is "?L = ?R")
proof - 
  have "?L = {#from_hma\<^sub>m A $$ (i, i). i \<in># mset [0..<CARD('n)]#}" 
    using from_hma_carrier[where A="A"] unfolding diag_mat_def mset_map by simp
  also have "... = {#from_hma\<^sub>m A $$ (i, i). i \<in># image_mset to_nat (mset_set (UNIV :: 'n set))#}"
    using range_to_nat[where 'a="'n"]
    by (intro arg_cong2[where f="image_mset"] refl) (simp add:image_mset_mset_set[OF inj_to_nat])
  also have "... = {#from_hma\<^sub>m A $$ (to_nat i, to_nat i). i \<in># (mset_set (UNIV :: 'n set))#}"
    by (simp add:image_mset.compositionality comp_def)
  also have "... = ?R"
    unfolding diag_mat_hma_def from_hma\<^sub>m_def using to_nat_less_card[where 'a="'n"]
    by (intro image_mset_cong) auto
  finally show ?thesis by simp
qed

definition adjoint_hma :: "complex^'m^'n \<Rightarrow> complex^'n^'m" where
  "adjoint_hma A = map_matrix cnj (transpose A)"

lemma adjoint_hma_eq: "adjoint_hma A $h i $h j = cnj (A $h j $h i)"
  unfolding adjoint_hma_def map_matrix_def map_vector_def transpose_def by auto

lemma adjoint_hma:
  fixes A :: "complex^('n::finite)^('m::finite)"
  shows "mat_adjoint (from_hma\<^sub>m A) = from_hma\<^sub>m (adjoint_hma A)"
proof -
  have "mat_adjoint (from_hma\<^sub>m A) $$ (i,j) = from_hma\<^sub>m (adjoint_hma A) $$ (i,j)"
    if "i < CARD('n)" "j < CARD('m)"  for i j
    using from_hma_carrier that unfolding mat_adjoint_def from_hma\<^sub>m_def adjoint_hma_def 
      Matrix.mat_of_rows_def map_matrix_def map_vector_def transpose_def by auto
  thus ?thesis
    using from_hma_carrier
    by (intro eq_matI) auto
qed

definition cinner where "cinner v w = scalar_product v (map_vector cnj w)"

context 
  includes lifting_syntax 
begin

lemma cinner_hma: 
  fixes x y :: "complex^'n"
  shows "cinner x y = (from_hma\<^sub>v x) \<bullet>c (from_hma\<^sub>v y)" (is "?L = ?R")
proof -
  have "?L = (\<Sum>i\<in>UNIV. x $h i * cnj (y $h i))" 
    unfolding cinner_def map_vector_def  scalar_product_def by simp
  also have "... = (\<Sum>i = 0..<CARD('n). x $h from_nat i * cnj (y $h from_nat i))"
    using to_nat_less_card to_nat_from_nat_id
    by (intro sum.reindex_bij_betw[symmetric] bij_betwI[where g="to_nat"]) auto
  also have "... = ?R" 
    unfolding Matrix.scalar_prod_def from_hma\<^sub>v_def
    by simp
  finally show ?thesis by simp
qed

lemma cinner_hma_transfer[transfer_rule]: 
  "(HMA_V ===> HMA_V ===> (=)) (\<bullet>c) cinner"
  unfolding  HMA_V_def  cinner_hma
  by (auto simp:rel_fun_def)

lemma adjoint_hma_transfer[transfer_rule]: 
  "(HMA_M ===> HMA_M) (mat_adjoint) adjoint_hma"
  unfolding HMA_M_def rel_fun_def by (auto simp add:adjoint_hma)

end

lemma adjoint_adjoint_id[simp]: "adjoint_hma (adjoint_hma A ) = A"
  by (transfer) (simp add:adjoint_adjoint)

lemma adjoint_def_alter_hma: 
  "cinner (A *v v) w = cinner v (adjoint_hma A *v w)" 
  by (transfer_hma rule:adjoint_def_alter)

lemma cinner_0: "cinner 0 0 = 0"
  by (transfer_hma)

lemma cinner_scale_left: "cinner (a *s v) w = a * cinner v w"
  by transfer_hma

lemma cinner_scale_right: "cinner v (a *s w) = cnj a * cinner v w"
  by transfer (simp add: inner_prod_smult_right)

lemma norm_of_real: 
  shows "norm (map_vector complex_of_real v) = norm v"
  unfolding norm_vec_def map_vector_def
  by (intro L2_set_cong) auto

definition unitary_hma :: "complex^'n^'n \<Rightarrow> bool"
  where "unitary_hma A \<longleftrightarrow> A ** adjoint_hma A = Finite_Cartesian_Product.mat 1"

definition unitarily_equiv_hma where
  "unitarily_equiv_hma A B U \<equiv> (unitary_hma U \<and> similar_matrix_wit A B U (adjoint_hma U))"

definition diagonal_mat :: "('a::zero)^('n::finite)^'n \<Rightarrow> bool" where
  "diagonal_mat A \<equiv> (\<forall>i. \<forall>j. i \<noteq> j \<longrightarrow> A $h i $h j = 0)"

lemma diagonal_mat_ex: 
  assumes "diagonal_mat A"
  shows "A = diag (\<chi> i. A $h i $h i)"
  using assms unfolding diagonal_mat_def diag_def 
  by (intro iffD2[OF vec_eq_iff] allI) auto

lemma diag_diagonal_mat[simp]: "diagonal_mat (diag x)"
  unfolding diag_def diagonal_mat_def by auto

lemma diag_imp_upper_tri: "diagonal_mat A \<Longrightarrow> upper_triangular_hma A"
  unfolding diagonal_mat_def upper_triangular_hma_def  
  by (metis nat_neq_iff)

definition unitary_diag where
    "unitary_diag A b U \<equiv> unitarily_equiv_hma A (diag b) U"

definition real_diag_decomp_hma where
  "real_diag_decomp_hma A d U \<equiv> unitary_diag A d U  \<and> 
  (\<forall>i. d $h i \<in> Reals)"

definition hermitian_hma :: "complex^'n^'n \<Rightarrow> bool" where 
  "hermitian_hma A = (adjoint_hma A = A)"

lemma from_hma_one:
  "from_hma\<^sub>m (mat 1 :: (('a::{one,zero})^'n^'n)) = 1\<^sub>m CARD('n)"
  unfolding Finite_Cartesian_Product.mat_def from_hma\<^sub>m_def using from_nat_inj
  by (intro eq_matI) auto

lemma from_hma_mult: 
  fixes A :: "('a :: semiring_1)^'m^'n"
  fixes B :: "'a^'k^'m::finite"
  shows "from_hma\<^sub>m A * from_hma\<^sub>m B = from_hma\<^sub>m (A ** B)"
  using HMA_M_mult unfolding rel_fun_def HMA_M_def by auto

lemma hermitian_hma:
  "hermitian_hma A = hermitian (from_hma\<^sub>m A)"
   unfolding hermitian_def adjoint_hma hermitian_hma_def by auto

lemma unitary_hma:
  fixes A :: "complex^'n^'n"
  shows  "unitary_hma A = unitary (from_hma\<^sub>m A)" (is "?L = ?R")
proof -
  have "?R \<longleftrightarrow> from_hma\<^sub>m A * mat_adjoint (from_hma\<^sub>m A) = 1\<^sub>m (CARD('n))"
    using from_hma_carrier
    unfolding unitary_def inverts_mat_def by simp
  also have "... \<longleftrightarrow> from_hma\<^sub>m (A ** adjoint_hma A) = from_hma\<^sub>m (mat 1::complex^'n^'n)"
    unfolding adjoint_hma from_hma_mult from_hma_one by simp
  also have "... \<longleftrightarrow> A ** adjoint_hma A = Finite_Cartesian_Product.mat 1"
    unfolding from_hma\<^sub>m_inj  by simp
  also have "... \<longleftrightarrow> ?L" unfolding unitary_hma_def by simp
  finally show ?thesis by simp
qed

lemma unitary_hmaD:
  fixes A :: "complex^'n^'n"
  assumes "unitary_hma A"
  shows "adjoint_hma A ** A = mat 1" (is "?A") "A ** adjoint_hma A = mat 1" (is "?B")
proof -
  have "mat_adjoint (from_hma\<^sub>m A) * from_hma\<^sub>m A = 1\<^sub>m CARD('n)"
    using assms unitary_hma by (intro unitary_simps from_hma_carrier ) auto
  thus ?A
    unfolding adjoint_hma from_hma_mult from_hma_one[symmetric] from_hma\<^sub>m_inj
    by simp
  show ?B
    using assms unfolding unitary_hma_def by simp
qed

lemma unitary_hma_adjoint:
  assumes "unitary_hma A"
  shows "unitary_hma (adjoint_hma A)"
  unfolding unitary_hma_def adjoint_adjoint_id unitary_hmaD[OF assms] by simp

lemma unitarily_equiv_hma:
  fixes A :: "complex^'n^'n"
  shows  "unitarily_equiv_hma A B U = 
    unitarily_equiv (from_hma\<^sub>m A) (from_hma\<^sub>m B) (from_hma\<^sub>m U)"
    (is "?L = ?R")
proof -
  have "?R \<longleftrightarrow> (unitary_hma U \<and> similar_mat_wit (from_hma\<^sub>m A) (from_hma\<^sub>m B) (from_hma\<^sub>m U) (from_hma\<^sub>m (adjoint_hma U)))"
    unfolding Spectral_Theory_Complements.unitarily_equiv_def unitary_hma[symmetric] adjoint_hma
    by simp
  also have "... \<longleftrightarrow> unitary_hma U \<and> similar_matrix_wit A B U (adjoint_hma U)"
    using HMA_similar_mat_wit unfolding rel_fun_def HMA_M_def
    by (intro arg_cong2[where f="(\<and>)"] refl) force 
  also have "... \<longleftrightarrow> ?L"
    unfolding unitarily_equiv_hma_def by auto
  finally show ?thesis by simp
qed

lemma Matrix_diagonal_matD: 
  assumes "Matrix.diagonal_mat A"
  assumes "i<dim_row A" "j<dim_col A"
  assumes "i \<noteq> j"
  shows "A $$ (i,j) = 0"
  using assms unfolding Matrix.diagonal_mat_def by auto

lemma diagonal_mat_hma:
  fixes A :: "('a :: zero)^('n :: finite)^'n"
  shows  "diagonal_mat A = Matrix.diagonal_mat (from_hma\<^sub>m A)" (is "?L = ?R")
proof 
  show "?L \<Longrightarrow> ?R"
    unfolding diagonal_mat_def Matrix.diagonal_mat_def from_hma\<^sub>m_def 
    using from_nat_inj  by auto
next
  assume a:"?R"

  have "A $h i $h j = 0" if "i \<noteq> j" for i j
  proof -
    have "A $h i $h j = (from_hma\<^sub>m A) $$ (to_nat i,to_nat j)"
      unfolding from_hma\<^sub>m_def using to_nat_less_card[where 'a="'n"] by simp 
    also have "... = 0"
      using to_nat_less_card[where 'a="'n"] to_nat_inj that 
      by (intro Matrix_diagonal_matD[OF a]) auto
    finally show ?thesis by simp
  qed
  thus "?L"
    unfolding diagonal_mat_def by auto
qed

lemma unitary_diag_hma:
  fixes A :: "complex^'n^'n"
  shows "unitary_diag A d U = 
    Spectral_Theory_Complements.unitary_diag (from_hma\<^sub>m A) (from_hma\<^sub>m (diag d)) (from_hma\<^sub>m U)"
proof -
  have "Matrix.diagonal_mat (from_hma\<^sub>m (diag d))"
    unfolding diagonal_mat_hma[symmetric] by simp
  thus ?thesis
    unfolding unitary_diag_def Spectral_Theory_Complements.unitary_diag_def unitarily_equiv_hma
    by auto
qed

lemma real_diag_decomp_hma:
  fixes A :: "complex^'n^'n"
  shows "real_diag_decomp_hma A d U = 
    real_diag_decomp (from_hma\<^sub>m A) (from_hma\<^sub>m (diag d)) (from_hma\<^sub>m U)"
proof -
  have 0:"(\<forall>i. d $h i \<in> \<real>) \<longleftrightarrow> (\<forall>i < CARD('n). from_hma\<^sub>m (diag d) $$ (i,i) \<in> \<real>)"
    unfolding from_hma\<^sub>m_def diag_def using to_nat_less_card by fastforce
  show ?thesis
    unfolding real_diag_decomp_hma_def real_diag_decomp_def unitary_diag_hma 0
    by auto
qed

lemma diagonal_mat_diag_ex_hma:
  assumes "Matrix.diagonal_mat A" "A \<in> carrier_mat CARD('n) CARD ('n :: finite)"
  shows "from_hma\<^sub>m (diag (\<chi> (i::'n). A $$ (to_nat i,to_nat i))) = A"
  using assms from_nat_inj unfolding from_hma\<^sub>m_def diag_def Matrix.diagonal_mat_def
  by (intro eq_matI) (auto simp add:to_nat_from_nat_id)

theorem commuting_hermitian_family_diag_hma:
  fixes Af :: "(complex^'n^'n) set"
  assumes "finite Af"
    and "Af \<noteq> {}"
    and "\<And>A. A \<in> Af \<Longrightarrow> hermitian_hma A"
    and "\<And>A B. A \<in> Af \<Longrightarrow> B\<in> Af \<Longrightarrow> A ** B = B ** A"
  shows "\<exists> U. \<forall> A\<in> Af. \<exists>B. real_diag_decomp_hma A B U"  
proof -
  have 0:"finite (from_hma\<^sub>m ` Af)"
    using assms(1)by (intro finite_imageI) 
  have 1: "from_hma\<^sub>m ` Af \<noteq> {}"
    using assms(2) by simp
  have 2: "A \<in> carrier_mat (CARD ('n)) (CARD ('n))" if "A \<in> from_hma\<^sub>m ` Af" for A
    using that unfolding from_hma\<^sub>m_def by (auto simp add:image_iff)
  have 3: "0 < CARD('n)"
    by simp
  have 4: "hermitian A" if "A \<in> from_hma\<^sub>m ` Af" for A
    using hermitian_hma assms(3) that by auto
  have 5: "A * B = B * A" if "A \<in> from_hma\<^sub>m ` Af" "B \<in> from_hma\<^sub>m ` Af" for A B
    using that assms(4) by (auto simp add:image_iff from_hma_mult)
  have "\<exists>U. \<forall>A\<in> from_hma\<^sub>m ` Af. \<exists>B. real_diag_decomp A B U"
    using commuting_hermitian_family_diag[OF 0 1 2 3 4 5] by auto
  then obtain U Bmap where U_def: "\<And>A. A \<in> from_hma\<^sub>m ` Af \<Longrightarrow> real_diag_decomp A (Bmap A) U"
    by metis
  define U' :: "complex^'n^'n" where "U' = to_hma\<^sub>m U"
  define Bmap' :: "complex^'n^'n \<Rightarrow> complex^'n" 
    where "Bmap' = (\<lambda>M. (\<chi> i. (Bmap (from_hma\<^sub>m M)) $$ (to_nat i,to_nat i)))"

  have "real_diag_decomp_hma A (Bmap' A) U'" if "A \<in> Af" for A 
  proof -
    have rdd: "real_diag_decomp (from_hma\<^sub>m A) (Bmap (from_hma\<^sub>m A)) U"
      using U_def that by simp

    have "U \<in> carrier_mat CARD('n) CARD('n)" "Bmap (from_hma\<^sub>m A) \<in> carrier_mat CARD('n) CARD('n)" 
      "Matrix.diagonal_mat (Bmap (from_hma\<^sub>m A))"
      using rdd unfolding real_diag_decomp_def Spectral_Theory_Complements.unitary_diag_def
        Spectral_Theory_Complements.unitarily_equiv_def similar_mat_wit_def
      by (auto simp add:Let_def)

    hence "(from_hma\<^sub>m (diag (Bmap' A))) = Bmap (from_hma\<^sub>m A)" "(from_hma\<^sub>m U') = U"
      unfolding Bmap'_def U'_def by (auto simp add:diagonal_mat_diag_ex_hma)
    hence "real_diag_decomp (from_hma\<^sub>m A) (from_hma\<^sub>m (diag (Bmap' A))) (from_hma\<^sub>m U')"
      using rdd by auto
    thus "?thesis"
      unfolding real_diag_decomp_hma by simp
  qed
  thus ?thesis
    by (intro exI[where x="U'"]) auto
qed

lemma char_poly_upper_triangular: 
  fixes A :: "complex^'n^'n"
  assumes "upper_triangular_hma A"
  shows "charpoly A = (\<Prod>a \<in># diag_mat_hma A. [:- a, 1:])"
proof -
  have "charpoly A = char_poly (from_hma\<^sub>m A)"
    using HMA_char_poly unfolding rel_fun_def HMA_M_def
    by (auto simp add:eq_commute)
  also have "... = (\<Prod>a\<leftarrow>diag_mat (from_hma\<^sub>m A). [:- a, 1:])"
    using assms unfolding upper_triangular_hma[symmetric]
    by (intro char_poly_upper_triangular[where n="CARD('n)"] from_hma_carrier) auto
  also have "... = (\<Prod>a\<in># mset (diag_mat (from_hma\<^sub>m A)). [:- a, 1:])"
    unfolding prod_mset_prod_list[symmetric] mset_map by simp
  also have "... = (\<Prod>a\<in># diag_mat_hma A. [:- a, 1:])"
    unfolding diag_mat_hma by simp
  finally show "charpoly A = (\<Prod>a\<in># diag_mat_hma A. [:- a, 1:])" by simp
qed

lemma upper_tri_eigvals:
  fixes A :: "complex^'n^'n"
  assumes "upper_triangular_hma A"
  shows "eigenvalues A = diag_mat_hma A"
proof -
  have "(\<Prod>a\<in>#eigenvalues A. [:- a, 1:]) = charpoly A"
    unfolding  eigvals_poly_length[symmetric] by simp
  also have "... = (\<Prod>a\<in>#diag_mat_hma A. [:- a, 1:])"
    by (intro char_poly_upper_triangular assms)
  finally have "(\<Prod>a\<in>#eigenvalues A. [:- a, 1:]) = (\<Prod>a\<in>#diag_mat_hma A. [:- a, 1:])"
    by simp
  thus ?thesis
    by (intro poly_prod_inj) simp
qed

lemma cinner_self:
  fixes v :: "complex^'n"
  shows "cinner v v = norm v^2"
proof -
  have 0: "x * cnj x = complex_of_real (x \<bullet> x)" for x :: complex 
    unfolding inner_complex_def complex_mult_cnj by (simp add:power2_eq_square)
  thus ?thesis
    unfolding cinner_def power2_norm_eq_inner scalar_product_def inner_vec_def 
      map_vector_def by simp 
qed

lemma unitary_iso:
  assumes "unitary_hma U" 
  shows "norm (U *v v) = norm v"
proof -
  have "norm (U *v v)^2 = cinner (U *v v) (U *v v)"
    unfolding cinner_self by simp
  also have "... = cinner v v"
    unfolding adjoint_def_alter_hma matrix_vector_mul_assoc unitary_hmaD[OF assms] by simp
  also have "... = norm v^2"
    unfolding cinner_self by simp
  finally have "complex_of_real (norm (U *v v)^2) = norm v^2" by simp
  thus ?thesis
    by (meson norm_ge_zero of_real_hom.injectivity power2_eq_iff_nonneg)
qed

lemma (in semiring_hom) mult_mat_vec_hma:
  "map_vector hom (A *v v) = map_matrix hom A *v map_vector hom v"
  using mult_mat_vec_hom by transfer auto

lemma (in semiring_hom) mat_hom_mult_hma:
  "map_matrix hom (A ** B) = map_matrix hom A ** map_matrix hom B"
  using mat_hom_mult by transfer auto

context regular_graph_tts 
begin

lemma to_nat_less_n: "to_nat (x::'n) < n"
  using to_nat_less_card card_n by metis 

lemma to_nat_from_nat: "x < n \<Longrightarrow> to_nat (from_nat x :: 'n) = x"
  using to_nat_from_nat_id card_n by metis

lemma hermitian_A: "hermitian_hma A"
  using count_sym unfolding hermitian_hma_def adjoint_hma_def A_def map_matrix_def 
    map_vector_def transpose_def by simp

lemma nonneg_A: "nonneg_mat A"
  unfolding nonneg_mat_def A_def by auto

lemma g_step_1:
  assumes "v \<in> verts G"
  shows "g_step (\<lambda>_. 1) v = 1" (is "?L = ?R")
proof -
  have "?L = in_degree G v / d"
    unfolding g_step_def in_degree_def by simp
  also have "... = 1"
    unfolding reg(2)[OF assms] using d_gt_0 by simp
  finally show ?thesis by simp
qed

lemma markov: "markov (A :: real^'n^'n)"
proof -
  have "A *v 1 = (1::real ^'n)" (is "?L = ?R")
  proof -
    have "A *v 1 = (\<chi> i. g_step (\<lambda>_. 1) (enum_verts i))"
      unfolding g_step_conv one_vec_def by simp
    also have "... = (\<chi> i. 1)"
      using bij_betw_apply[OF enum_verts] by (subst g_step_1) auto
    also have "... = 1" unfolding one_vec_def by simp
    finally show ?thesis by simp
  qed
  thus ?thesis
    by (intro markov_symI nonneg_A symmetric_A)
qed

lemma nonneg_J: "nonneg_mat J"
  unfolding nonneg_mat_def J_def by auto

lemma J_eigvals: "eigenvalues J = {#1::complex#} + replicate_mset (n - 1) 0"
proof -
  define \<alpha> :: "nat \<Rightarrow> real" where "\<alpha> i = sqrt (i^2+i)" for i :: nat

  define q :: "nat \<Rightarrow> nat \<Rightarrow> real"
    where "q i j = (
        if i = 0 then (1/sqrt n) else (
        if j < i then ((-1) / \<alpha> i) else (
        if j = i then (i / \<alpha> i) else 0)))" for i j

  define Q :: "complex^'n^'n" where "Q = (\<chi> i j. complex_of_real (q (to_nat i) (to_nat j)))"

  define D :: "complex^'n^'n" where 
    "D = (\<chi> i j. if to_nat i = 0 \<and> to_nat j = 0 then 1 else 0)"

  have 2: "[0..<n] = 0#[1..<n]"
    using n_gt_0 upt_conv_Cons by auto

  have aux0: "(\<Sum>k = 0..<n. q j k * q i k) = of_bool (i = j)" if 1:"i \<le> j" "j < n"  for i j
  proof -
    consider (a) "i = j \<and> j = 0" | (b) "i = 0 \<and> i < j" | (c) " 0 < i \<and> i < j" | (d) "0 < i \<and> i = j"
      using 1 by linarith
    thus ?thesis
    proof (cases)
      case a
      then show ?thesis using n_gt_0 by (simp add:q_def)
    next
      case b
      have "(\<Sum>k = 0..<n. q j k*q i k)=(\<Sum>k\<in>insert j ({0..<j} \<union> {j+1..<n}). q j k*q i k)"
        using that(2) by (intro sum.cong) auto
      also have "...=q j j*q i j+(\<Sum>k=0..<j. q j k * q i k)+(\<Sum>k=j+1..<n. q j k * q i k)"
        by (subst sum.insert) (auto simp add: sum.union_disjoint)
      also have "... = 0" using b unfolding q_def by simp
      finally show ?thesis using b by simp
    next
      case c
      have "(\<Sum>k = 0..<n. q j k*q i k)=(\<Sum>k\<in>insert i ({0..<i} \<union> {i+1..<n}). q j k*q i k)"
        using that(2) c by (intro sum.cong) auto
      also have "...=q j i*q i i+(\<Sum>k=0..<i. q j k * q i k)+(\<Sum>k=i+1..<n. q j k * q i k)"
        by (subst sum.insert) (auto simp add: sum.union_disjoint)
      also have "... =(-1) / \<alpha> j * i / \<alpha> i+ i * ((-1) / \<alpha> j *  (-1) / \<alpha> i)"
        using c unfolding q_def by simp
      also have "... = 0"
        by (simp add:algebra_simps)
      finally show ?thesis using c by simp
    next
      case d
      have "real i + real i^2 = real (i + i^2)" by simp
      also have "... \<noteq> real 0" 
        unfolding of_nat_eq_iff using d by simp
      finally have d_1: "real i  + real i^2 \<noteq> 0" by simp
      have "(\<Sum>k = 0..<n. q j k*q i k)=(\<Sum>k\<in>insert i ({0..<i} \<union> {i+1..<n}). q j k*q i k)"
        using that(2) d by (intro sum.cong) auto
      also have "...=q j i*q i i+(\<Sum>k=0..<i. q j k * q i k)+(\<Sum>k=i+1..<n. q j k * q i k)"
        by (subst sum.insert) (auto simp add: sum.union_disjoint)
      also have "... = i/ \<alpha> i * i / \<alpha> i+ i * ((-1) / \<alpha> i *  (-1) / \<alpha> i)"
        using d that unfolding q_def by simp
      also have "... = (i^2 + i) / (\<alpha> i)^2"
        by (simp add: power2_eq_square divide_simps)
      also have "... = 1"
        using d_1 unfolding \<alpha>_def by (simp add:algebra_simps) 
      finally show ?thesis using d by simp
    qed
  qed

  have 0:"(\<Sum>k = 0..<n. q j k * q i k) = of_bool (i = j)" (is "?L = ?R")  if "i < n" "j < n"  for i j
  proof -
    have "?L = (\<Sum>k = 0..<n. q (max i j) k * q (min i j) k)"
      by (cases "i \<le> j") ( simp_all add:ac_simps cong:sum.cong)
    also have "... = of_bool (min i j = max i j)"
      using that by (intro aux0) auto
    also have "... = ?R" 
      by (cases "i \<le> j") auto
    finally show ?thesis by simp
  qed
  
  have "(\<Sum>k\<in>UNIV. Q $h j $h k * cnj (Q $h i $h k)) = of_bool (i=j)" (is "?L = ?R") for i j
  proof -
    have "?L = complex_of_real (\<Sum>k \<in> (UNIV::'n set). q (to_nat j) (to_nat k) * q (to_nat i) (to_nat k))" 
      unfolding Q_def 
      by (simp add:case_prod_beta scalar_prod_def map_vector_def inner_vec_def row_def inner_complex_def)
    also have "... = complex_of_real (\<Sum>k=0..<n. q (to_nat j) k * q (to_nat i) k)"
      using to_nat_less_n to_nat_from_nat
      by (intro arg_cong[where f="of_real"] sum.reindex_bij_betw bij_betwI[where g="from_nat"]) (auto)
    also have "... = complex_of_real (of_bool(to_nat i = to_nat j))"
      using to_nat_less_n by (intro arg_cong[where f="of_real"] 0) auto
    also have "... = ?R"
      using to_nat_inj by auto
    finally show ?thesis by simp
  qed
  hence "Q ** adjoint_hma Q = mat 1"
    by (intro iffD2[OF vec_eq_iff]) (auto simp add:matrix_matrix_mult_def mat_def adjoint_hma_eq)
  hence unit_Q: "unitary_hma Q"
    unfolding unitary_hma_def by simp

  have "card {(k::'n). to_nat k = 0} = card {from_nat 0 :: 'n}" 
    using to_nat_from_nat[where x="0"] n_gt_0
    by (intro arg_cong[where f="card"] iffD2[OF set_eq_iff]) auto
  hence 5:"card {(k::'n). to_nat k = 0} = 1" by simp
  hence 1:"adjoint_hma Q ** D = (\<chi> i j. (if to_nat j = 0 then complex_of_real (1/sqrt n) else 0))"
    unfolding Q_def D_def by (intro iffD2[OF vec_eq_iff] allI)
     (auto simp add:adjoint_hma_eq matrix_matrix_mult_def q_def if_distrib if_distribR sum.If_cases)

  have "(adjoint_hma Q ** D ** Q) $h i $h j = J $h i $h j" (is "?L1 = ?R1") for i j 
  proof - 
    have "?L1 =1/((sqrt (real n)) * complex_of_real (sqrt (real n)))"
      unfolding 1 unfolding Q_def using n_gt_0 5
      by (auto simp add:matrix_matrix_mult_def q_def if_distrib if_distribR sum.If_cases) 
    also have "... = 1/sqrt (real n)^2"
      unfolding of_real_divide of_real_mult power2_eq_square
      by simp
    also have "... = J $h i $h j"
      unfolding J_def card_n using n_gt_0 by simp
    finally show ?thesis by simp
  qed

  hence "adjoint_hma Q ** D ** Q = J"
    by (intro iffD2[OF vec_eq_iff] allI) auto 

  hence "similar_matrix_wit J D (adjoint_hma Q) Q" 
    unfolding similar_matrix_wit_def unitary_hmaD[OF unit_Q] by auto
  hence "similar_matrix J D"
    unfolding similar_matrix_def by auto
  hence "eigenvalues J = eigenvalues D"
    by (intro similar_matrix_eigvals)
  also have "... = diag_mat_hma D"
    by (intro upper_tri_eigvals diag_imp_upper_tri) (simp add:D_def diagonal_mat_def)
  also have "... = {# of_bool (to_nat i = 0). i \<in># mset_set (UNIV :: 'n set)#}"
    unfolding diag_mat_hma_def D_def of_bool_def by simp 
  also have "... = {# of_bool (i = 0). i \<in># mset_set (to_nat ` (UNIV :: 'n set))#}"
    unfolding image_mset_mset_set[OF inj_to_nat, symmetric] 
    by (simp add:image_mset.compositionality comp_def)
  also have "... = mset (map (\<lambda>i. of_bool(i=0)) [0..<n])"
    unfolding range_to_nat card_n mset_map by simp
  also have "... = mset (1 # map (\<lambda>i. 0) [1..<n])"
    unfolding 2 by (intro arg_cong[where f="mset"]) simp
  also have "... = {#1#} + replicate_mset (n-1) 0"
    using n_gt_0 by (simp add:map_replicate_const mset_repl)
  finally show ?thesis by simp
qed

lemma J_markov: "markov J"
proof -
  have "nonneg_mat J"
    unfolding J_def nonneg_mat_def by auto
  moreover have "transpose J = J" 
    unfolding J_def transpose_def by auto
  moreover have "J *v 1 = (1 :: real^'n)"
    unfolding J_def by (simp add:matrix_vector_mult_def one_vec_def) 
  ultimately show ?thesis
    by (intro markov_symI) auto
qed

lemma markov_complex_apply: 
  assumes "markov M"
  shows "(map_matrix complex_of_real M) *v (1 :: complex^'n) = 1" (is "?L = ?R")
proof -
  have "?L = (map_matrix complex_of_real M) *v (map_vector complex_of_real 1)"
    by (intro arg_cong2[where f="(*v)"] refl) (simp add: map_vector_def one_vec_def)
  also have "... = map_vector (complex_of_real) 1"
    unfolding of_real_hom.mult_mat_vec_hma[symmetric] markov_apply[OF assms] by simp
  also have "... = ?R"
    by (simp add: map_vector_def one_vec_def)
  finally show ?thesis by simp
qed

lemma J_A_comm_real: "J ** A = A ** (J :: real^'n^'n)" 
proof -
  have 0: "(\<Sum>k\<in>UNIV. A $h k $h i / real CARD('n)) = 1 / real CARD('n)" (is "?L = ?R") for i 
  proof -
    have "?L = (1 v* A) $h i / real CARD('n)"
      unfolding vector_matrix_mult_def by (simp add:sum_divide_distrib) 
    also have "... = ?R"
      unfolding markov_apply[OF markov] by simp
    finally show ?thesis by simp
  qed
  have 1: "(\<Sum>k\<in>UNIV. A $h i $h k / real CARD('n)) = 1 / real CARD('n)" (is "?L = ?R") for i 
  proof -
    have "?L = (A *v 1) $h i / real CARD('n)"
      unfolding matrix_vector_mult_def by (simp add:sum_divide_distrib) 
    also have "... = ?R"
      unfolding markov_apply[OF markov] by simp
    finally show ?thesis by simp
  qed

  show ?thesis
    unfolding J_def using 0 1
    by (intro iffD2[OF vec_eq_iff] allI) (simp add:matrix_matrix_mult_def)
qed

lemma J_A_comm: "J ** A = A ** (J :: complex^'n^'n)" (is "?L = ?R")
proof -
  have "J ** A = map_matrix complex_of_real (J ** A)"
    unfolding of_real_hom.mat_hom_mult_hma J_def A_def
    by (auto simp add:map_matrix_def map_vector_def)
  also have "... = map_matrix complex_of_real (A ** J)"
    unfolding J_A_comm_real by simp
  also have "... = map_matrix complex_of_real A ** map_matrix complex_of_real J"
    unfolding of_real_hom.mat_hom_mult_hma by simp
  also have "... = ?R"
    unfolding A_def J_def
    by (auto simp add:map_matrix_def map_vector_def)
  finally show ?thesis by simp
qed

definition \<gamma>\<^sub>a :: "'n itself \<Rightarrow> real" where
  "\<gamma>\<^sub>a _ = (if n > 1 then Max_mset (image_mset cmod (eigenvalues A - {#1#})) else 0)"

definition \<gamma>\<^sub>2 :: "'n itself \<Rightarrow> real" where
  "\<gamma>\<^sub>2 _ = (if n > 1 then Max_mset {# Re x. x \<in># (eigenvalues A - {#1#})#} else 0)"

lemma J_sym: "hermitian_hma J"
  unfolding J_def hermitian_hma_def
  by (intro  iffD2[OF vec_eq_iff] allI) (simp add: adjoint_hma_eq)

lemma
  shows evs_real: "set_mset (eigenvalues A::complex multiset) \<subseteq> \<real>" (is "?R1")
    and ev_1: "(1::complex) \<in># eigenvalues A"
    and \<gamma>\<^sub>a_ge_0: "\<gamma>\<^sub>a TYPE ('n) \<ge> 0"
    and find_any_ev: 
      "\<forall>\<alpha> \<in># eigenvalues A - {#1#}. \<exists>v. cinner v 1 = 0 \<and> v \<noteq> 0 \<and> A *v v = \<alpha> *s v" 
    and \<gamma>\<^sub>a_bound: "\<forall>v. cinner v 1 = 0 \<longrightarrow> norm (A *v v) \<le> \<gamma>\<^sub>a TYPE('n) * norm v"
    and \<gamma>\<^sub>2_bound: "\<forall>(v::real^'n). v \<bullet> 1 = 0 \<longrightarrow> v \<bullet> (A *v v) \<le> \<gamma>\<^sub>2 TYPE ('n) * norm v^2"
proof -
  have "\<exists> U. \<forall> A\<in> {J,A}. \<exists>B. real_diag_decomp_hma A B U"  
    using J_sym hermitian_A J_A_comm
    by (intro commuting_hermitian_family_diag_hma) auto
  then obtain U Ad Jd 
    where A_decomp: "real_diag_decomp_hma A Ad U" and K_decomp: "real_diag_decomp_hma J Jd U"
    by auto
  have J_sim: "similar_matrix_wit J (diag Jd) U (adjoint_hma U)" and 
    unit_U: "unitary_hma U"
    using K_decomp unfolding real_diag_decomp_hma_def unitary_diag_def unitarily_equiv_hma_def
    by auto

  have "diag_mat_hma (diag Jd) = eigenvalues (diag Jd)"
    by (intro upper_tri_eigvals[symmetric] diag_imp_upper_tri J_sim) auto
  also have "... = eigenvalues J"
    using J_sim by (intro similar_matrix_eigvals[symmetric]) (auto simp add:similar_matrix_def)
  also have "... ={#1::complex#} + replicate_mset (n - 1) 0"
    unfolding J_eigvals by simp
  finally have 0:"diag_mat_hma (diag Jd) = {#1::complex#} + replicate_mset (n - 1) 0" by simp
  hence "1 \<in># diag_mat_hma (diag Jd)" by simp
  then obtain i where i_def:"Jd $h i = 1" 
    unfolding diag_mat_hma_def diag_def by auto
  have "{# Jd $h j. j \<in># mset_set (UNIV - {i}) #} = {#Jd $h j. j \<in># mset_set UNIV - mset_set {i}#}"
    unfolding diag_mat_hma_def by (intro arg_cong2[where f="image_mset"] mset_set_Diff) auto
  also have "... = diag_mat_hma (diag Jd)  - {#1#}"
    unfolding diag_mat_hma_def diag_def by (subst image_mset_Diff) (auto simp add:i_def)
  also have "... =  replicate_mset (n - 1) 0"
    unfolding 0 by simp
  finally have "{# Jd $h j. j \<in># mset_set (UNIV - {i}) #} = replicate_mset (n - 1) 0"
    by simp
  hence "set_mset {# Jd $h j. j \<in># mset_set (UNIV - {i}) #} \<subseteq> {0}" 
    by simp
  hence 1:"Jd $h j = 0" if "j \<noteq> i" for j
    using that by auto

  define u where "u = adjoint_hma U *v 1"
  define \<alpha> where "\<alpha> = u $h i"

  have "U *v u = (U ** adjoint_hma U) *v 1"
    unfolding u_def by (simp add:matrix_vector_mul_assoc)
  also have "... = 1"
    unfolding unitary_hmaD[OF unit_U] by simp
  also have "... \<noteq>  0"
    by simp
  finally have "U *v u \<noteq> 0" by simp 
  hence u_nz: "u \<noteq> 0"
    by (cases "u = 0") auto

  have "diag Jd *v u = adjoint_hma U ** U ** diag Jd ** adjoint_hma U *v 1"
    unfolding unitary_hmaD[OF unit_U] u_def by (auto simp add:matrix_vector_mul_assoc)
  also have "... = adjoint_hma U ** (U ** diag Jd ** adjoint_hma U) *v 1"
    by (simp add:matrix_mul_assoc)
  also have "... = adjoint_hma U ** J *v 1"
    using J_sim unfolding similar_matrix_wit_def by simp
  also have "... = adjoint_hma U *v (map_matrix complex_of_real J *v 1)"
    by (simp add:map_matrix_def map_vector_def J_def matrix_vector_mul_assoc)
  also have "... = u"
    unfolding u_def markov_complex_apply[OF J_markov] by simp
  finally have u_ev: "diag Jd *v u = u" by simp
  hence "Jd * u = u"
    unfolding diag_vec_mult_eq by simp
  hence "u $h j = 0" if "j \<noteq> i" for j
    using 1 that unfolding times_vec_def vec_eq_iff by auto
  hence u_alt: "u = axis i \<alpha>"
    unfolding \<alpha>_def axis_def vec_eq_iff by auto
  hence \<alpha>_nz: "\<alpha> \<noteq> 0"
    using u_nz by (cases "\<alpha>=0") auto

  have A_sim: "similar_matrix_wit A (diag Ad) U (adjoint_hma U)" and Ad_real: "\<forall>i. Ad $h i \<in> \<real>"
    using A_decomp unfolding real_diag_decomp_hma_def unitary_diag_def unitarily_equiv_hma_def
    by auto

  have "diag_mat_hma (diag Ad) = eigenvalues (diag Ad)"
    by (intro upper_tri_eigvals[symmetric] diag_imp_upper_tri A_sim) auto
  also have "... = eigenvalues A"
    using A_sim by (intro similar_matrix_eigvals[symmetric]) (auto simp add:similar_matrix_def)
  finally have 3:"diag_mat_hma (diag Ad) = eigenvalues A" 
    by simp

  show ?R1
    unfolding 3[symmetric] diag_mat_hma_def diag_def using Ad_real by auto

  have "diag Ad *v u = adjoint_hma U ** U ** diag Ad ** adjoint_hma U *v 1"
    unfolding unitary_hmaD[OF unit_U] u_def by (auto simp add:matrix_vector_mul_assoc)
  also have "... = adjoint_hma U ** (U ** diag Ad ** adjoint_hma U) *v 1"
    by (simp add:matrix_mul_assoc)
  also have "... = adjoint_hma U ** A *v 1"
    using A_sim unfolding similar_matrix_wit_def by simp
  also have "... = adjoint_hma U *v (map_matrix complex_of_real A *v 1)"
    by (simp add:map_matrix_def map_vector_def A_def matrix_vector_mul_assoc)
  also have "... = u"
    unfolding u_def markov_complex_apply[OF markov] by simp
  finally have u_ev_A: "diag Ad *v u = u" by simp
  hence "Ad * u = u"
    unfolding diag_vec_mult_eq by simp
  hence 5:"Ad $h i = 1"
    using \<alpha>_nz unfolding u_alt times_vec_def vec_eq_iff axis_def by force 

  thus ev_1: "(1::complex) \<in># eigenvalues A"
    unfolding 3[symmetric] diag_mat_hma_def diag_def by auto

  have "eigenvalues A - {#1#} = diag_mat_hma (diag Ad) - {#1#}"
    unfolding 3 by simp
  also have "... = {#Ad $h j. j \<in># mset_set UNIV#} - {# Ad $h i #}"
    unfolding 5 diag_mat_hma_def diag_def by simp
  also have "... = {#Ad $h j. j \<in># mset_set UNIV - mset_set {i}#}"
    by (subst image_mset_Diff) auto
  also have "... = {#Ad $h j. j \<in># mset_set (UNIV - {i})#}"
    by (intro arg_cong2[where f="image_mset"] mset_set_Diff[symmetric]) auto 
  finally have 4:"eigenvalues A - {#1#} = {#Ad $h j. j \<in># mset_set (UNIV - {i})#}" by simp

  have "cmod (Ad $h k) \<le> \<gamma>\<^sub>a TYPE ('n)" if "n > 1" "k \<noteq> i" for k
    unfolding \<gamma>\<^sub>a_def 4 using that Max_ge by auto
  moreover have "k = i" if "n = 1" for k
    using that to_nat_less_n by simp 
  ultimately have norm_Ad: "norm (Ad $h k) \<le> \<gamma>\<^sub>a TYPE ('n) \<or> k = i" for k
    using n_gt_0 by (cases "n = 1", auto) 

  have "Re (Ad $h k) \<le> \<gamma>\<^sub>2 TYPE ('n)" if "n > 1" "k \<noteq> i" for k
    unfolding \<gamma>\<^sub>2_def 4 using that Max_ge by auto
  moreover have "k = i" if "n = 1" for k
    using that to_nat_less_n by simp 
  ultimately have Re_Ad: "Re (Ad $h k) \<le> \<gamma>\<^sub>2 TYPE ('n) \<or> k = i" for k
    using n_gt_0 by (cases "n = 1", auto) 

  show \<Lambda>\<^sub>e_ge_0: "\<gamma>\<^sub>a TYPE ('n) \<ge> 0"
  proof (cases "n > 1")
    case True
    then obtain k where k_def: "k \<noteq> i"
      by (metis (full_types) card_n from_nat_inj n_gt_0 one_neq_zero)
    have "0 \<le> cmod (Ad $h k)" 
      by simp
    also have "... \<le> \<gamma>\<^sub>a TYPE ('n)" 
      using norm_Ad k_def by auto
    finally show ?thesis by auto
  next
    case False
    thus ?thesis unfolding \<gamma>\<^sub>a_def by simp
  qed

  have "\<exists>v. cinner v 1 = 0 \<and> v \<noteq> 0 \<and> A *v v = \<beta> *s v" if \<beta>_ran: "\<beta> \<in># eigenvalues A - {#1#}" for \<beta>
  proof -
    obtain j where j_def: "\<beta> = Ad $h j" "j \<noteq> i"
      using \<beta>_ran unfolding 4 by auto
    define v where "v = U *v axis j 1" 

    have "A *v v = A ** U *v axis j 1" 
      unfolding v_def by (simp add:matrix_vector_mul_assoc)
    also have "... = ((U ** diag Ad ** adjoint_hma U) ** U) *v axis j 1"
      using A_sim unfolding similar_matrix_wit_def by simp
    also have "... = U ** diag Ad ** (adjoint_hma U ** U) *v axis j 1"
      by (simp add:matrix_mul_assoc)
    also have "... = U ** diag Ad *v axis j 1"
      using unitary_hmaD[OF unit_U] by simp
    also have "... = U *v (Ad * axis j 1)"
      by (simp add:matrix_vector_mul_assoc[symmetric] diag_vec_mult_eq)
    also have "... = U *v (\<beta> *s axis j 1)"
      by (intro arg_cong2[where f="(*v)"] iffD2[OF vec_eq_iff]) (auto simp:j_def axis_def) 
    also have "... = \<beta> *s v"
      unfolding v_def by (simp add:vector_scalar_commute) 
    finally have 5:"A *v v = \<beta> *s v" by simp

    have "cinner v 1 = cinner (axis j 1) (adjoint_hma U *v 1)"
      unfolding v_def adjoint_def_alter_hma by simp
    also have "... = cinner (axis j 1) (axis i \<alpha>)"
      unfolding u_def[symmetric] u_alt by simp
    also have " ... = 0" 
      using j_def(2) unfolding cinner_def axis_def scalar_product_def  map_vector_def 
      by (auto simp:if_distrib if_distribR sum.If_cases)
    finally have 6:"cinner v 1  = 0 "
      by simp

    have "cinner v v = cinner (axis j 1) (adjoint_hma U *v (U *v (axis j 1)))"
      unfolding v_def adjoint_def_alter_hma by simp
    also have "... = cinner (axis j 1) (axis j 1)"
      unfolding matrix_vector_mul_assoc unitary_hmaD[OF unit_U] by simp
    also have "... = 1"
      unfolding cinner_def axis_def scalar_product_def  map_vector_def 
      by (auto simp:if_distrib if_distribR sum.If_cases)
    finally have "cinner v v = 1"
      by simp
    hence 7:"v \<noteq> 0"
      by (cases "v=0") (auto simp add:cinner_0)

    show ?thesis
      by (intro exI[where x="v"] conjI 6 7 5)
  qed

  thus "\<forall>\<alpha> \<in># eigenvalues A - {#1#}. \<exists>v. cinner v 1 = 0 \<and> v \<noteq> 0 \<and> A *v v = \<alpha> *s v"
    by simp

  have "norm (A *v v) \<le> \<gamma>\<^sub>a TYPE('n) * norm v" if "cinner v 1 = 0" for v 
  proof -
    define w where "w= adjoint_hma U *v v"

    have "w $h i = cinner w (axis i 1)"
      unfolding cinner_def axis_def scalar_product_def map_vector_def 
      by (auto simp:if_distrib if_distribR sum.If_cases)
    also have "... = cinner v (U *v axis i 1)"
      unfolding w_def adjoint_def_alter_hma by simp
    also have "... = cinner v ((1 / \<alpha>) *s (U *v u))"
      unfolding vector_scalar_commute[symmetric] u_alt using \<alpha>_nz
      by (intro_cong "[\<sigma>\<^sub>2 cinner, \<sigma>\<^sub>2 (*v)]") (auto simp add:axis_def vec_eq_iff)
    also have "... = cinner v ((1 / \<alpha>) *s 1)"
      unfolding u_def matrix_vector_mul_assoc unitary_hmaD[OF unit_U] by simp
    also have "... = 0"
      unfolding cinner_scale_right that by simp
    finally have w_orth: "w $h i = 0" by simp

    have "norm (A *v v) = norm (U *v (diag Ad *v w))"
      using A_sim  unfolding matrix_vector_mul_assoc similar_matrix_wit_def w_def
      by (simp add:matrix_mul_assoc)
    also have "... = norm (diag Ad *v w)"
      unfolding unitary_iso[OF unit_U] by simp
    also have "... = norm (Ad * w)"
      unfolding diag_vec_mult_eq by simp
    also have "... = sqrt (\<Sum>i\<in>UNIV. (cmod (Ad $h i) * cmod (w $h i))\<^sup>2)"
      unfolding norm_vec_def L2_set_def times_vec_def by (simp add:norm_mult)
    also have "... \<le> sqrt (\<Sum>i\<in>UNIV. ((\<gamma>\<^sub>a TYPE('n)) * cmod (w $h i))^2)"
      using w_orth norm_Ad
      by (intro iffD2[OF real_sqrt_le_iff] sum_mono power_mono mult_right_mono') auto
    also have "... = \<bar>\<gamma>\<^sub>a TYPE('n)\<bar> * sqrt (\<Sum>i\<in>UNIV. (cmod (w $h i))\<^sup>2)"
      by (simp add:power_mult_distrib sum_distrib_left[symmetric] real_sqrt_mult)
    also have "... = \<bar>\<gamma>\<^sub>a TYPE('n)\<bar> * norm w"
      unfolding norm_vec_def L2_set_def by simp
    also have "... = \<gamma>\<^sub>a TYPE('n) * norm w"
      using \<Lambda>\<^sub>e_ge_0 by simp
    also have "... = \<gamma>\<^sub>a TYPE('n) * norm v"
      unfolding w_def unitary_iso[OF unitary_hma_adjoint[OF unit_U]] by simp
    finally show "norm (A *v v) \<le> \<gamma>\<^sub>a TYPE('n) * norm v"
      by simp
  qed

  thus "\<forall>v. cinner v 1 = 0 \<longrightarrow> norm (A *v v) \<le> \<gamma>\<^sub>a TYPE('n) * norm v" by auto

  have "v \<bullet> (A *v v) \<le> \<gamma>\<^sub>2 TYPE ('n) * norm v^2" if "v \<bullet> 1 = 0" for v :: "real^'n"
  proof -
    define v' where "v' = map_vector complex_of_real v"
    define w where "w= adjoint_hma U *v v'"

    have "w $h i = cinner w (axis i 1)"
      unfolding cinner_def axis_def scalar_product_def map_vector_def 
      by (auto simp:if_distrib if_distribR sum.If_cases)
    also have "... = cinner v' (U *v axis i 1)"
      unfolding w_def adjoint_def_alter_hma by simp
    also have "... = cinner v' ((1 / \<alpha>) *s (U *v u))"
      unfolding vector_scalar_commute[symmetric] u_alt using \<alpha>_nz
      by (intro_cong "[\<sigma>\<^sub>2 cinner, \<sigma>\<^sub>2 (*v)]") (auto simp add:axis_def vec_eq_iff)
    also have "... = cinner v' ((1 / \<alpha>) *s 1)"
      unfolding u_def matrix_vector_mul_assoc unitary_hmaD[OF unit_U] by simp
    also have "... = cnj (1 / \<alpha>) * cinner v' 1"
      unfolding cinner_scale_right by simp
    also have "... = cnj (1 / \<alpha>) * complex_of_real (v \<bullet> 1)"
      unfolding cinner_def scalar_product_def map_vector_def inner_vec_def v'_def
      by (intro arg_cong2[where f="(*)"] refl) (simp)
    also have "... = 0"
      unfolding that by simp
    finally have w_orth: "w $h i = 0" by simp

    have "complex_of_real (norm v^2) = complex_of_real (v \<bullet> v)" 
      by (simp add: power2_norm_eq_inner)
    also have "... = cinner v' v'"
      unfolding v'_def cinner_def scalar_product_def inner_vec_def map_vector_def by simp
    also have "... = norm v'^2"
      unfolding cinner_self by simp
    also have "... = norm w^2"
      unfolding w_def unitary_iso[OF unitary_hma_adjoint[OF unit_U]] by simp
    also have "... = cinner w w"
      unfolding cinner_self by simp
    also have "... = (\<Sum>j\<in>UNIV. complex_of_real (cmod (w $h j)^2))"
      unfolding cinner_def scalar_product_def map_vector_def 
      cmod_power2 complex_mult_cnj[symmetric] by simp
    also have "... = complex_of_real (\<Sum>j\<in>UNIV.  (cmod (w $h j)^2))"
      by simp
    finally have "complex_of_real (norm v^2) = complex_of_real (\<Sum>j\<in>UNIV.  (cmod (w $h j)^2))"
      by simp
    hence norm_v: "norm v^2 = (\<Sum>j\<in>UNIV.  (cmod (w $h j)^2))"
      using of_real_hom.injectivity by blast

    have "complex_of_real (v \<bullet> (A *v v)) = cinner v' (map_vector of_real (A *v v))"
      unfolding v'_def cinner_def scalar_product_def inner_vec_def map_vector_def
      by simp
    also have "... = cinner v' (map_matrix of_real A *v v')" 
      unfolding v'_def of_real_hom.mult_mat_vec_hma by simp
    also have "... = cinner v' (A *v v')"
      unfolding map_matrix_def map_vector_def A_def by auto
    also have "... = cinner v' (U ** diag Ad ** adjoint_hma U *v v')"
      using A_sim unfolding similar_matrix_wit_def by simp
    also have "... = cinner (adjoint_hma U *v v') (diag Ad ** adjoint_hma U *v v')"
      unfolding adjoint_def_alter_hma adjoint_adjoint adjoint_adjoint_id
      by (simp add:matrix_vector_mul_assoc matrix_mul_assoc)
    also have "... = cinner w (diag Ad *v w)"
      unfolding w_def by (simp add:matrix_vector_mul_assoc)
    also have "... = cinner w (Ad * w)"
      unfolding diag_vec_mult_eq by simp
    also have "... = (\<Sum>j\<in>UNIV. cnj (Ad $h j) * cmod (w $h j)^2)"
      unfolding cinner_def map_vector_def scalar_product_def cmod_power2 complex_mult_cnj[symmetric]
      by (simp add:algebra_simps)
    also have "... = (\<Sum>j\<in>UNIV. Ad $h j * cmod (w $h j)^2)"
      using Ad_real by (intro sum.cong refl arg_cong2[where f="(*)"] iffD1[OF Reals_cnj_iff]) auto
    also have "... = (\<Sum>j\<in>UNIV. complex_of_real (Re (Ad $h j) * cmod (w $h j)^2))"
      using Ad_real by (intro sum.cong refl) simp
    also have "... = complex_of_real (\<Sum>j\<in> UNIV. Re (Ad $h j) * cmod (w $h j)^2)"
      by simp
    finally have "complex_of_real (v\<bullet>(A *v v)) = of_real(\<Sum>j\<in>UNIV. Re (Ad $h j) * cmod (w $h j)^2)"
      by simp
    hence "v\<bullet>(A *v v) = (\<Sum>j\<in>UNIV. Re (Ad $h j) * cmod (w $h j)^2)" 
      using of_real_hom.injectivity by blast
    also have "... \<le> (\<Sum>j\<in>UNIV. \<gamma>\<^sub>2 TYPE ('n) * cmod (w $h j)^2)"
      using w_orth Re_Ad by (intro sum_mono mult_right_mono') auto
    also have "... = \<gamma>\<^sub>2 TYPE ('n) * (\<Sum>j\<in>UNIV. cmod (w $h j)^2)"
      by (simp add:sum_distrib_left)
    also have "... = \<gamma>\<^sub>2 TYPE ('n) * norm v^2"
      unfolding norm_v by simp
    finally show ?thesis by simp
  qed

  thus "\<forall>(v::real^'n). v \<bullet> 1 = 0 \<longrightarrow> v \<bullet> (A *v v) \<le> \<gamma>\<^sub>2 TYPE ('n) * norm v^2"
    by auto
qed

lemma find_any_real_ev:
  assumes "complex_of_real \<alpha> \<in># eigenvalues A - {#1#}"
  shows "\<exists>v. v \<bullet> 1 = 0 \<and> v \<noteq> 0 \<and> A *v v = \<alpha> *s v"
proof -
  obtain w where w_def: "cinner w 1 = 0" "w \<noteq> 0" "A *v w = \<alpha> *s w"
    using find_any_ev assms by auto

  have "w = 0" if "map_vector Re (1 *s w) = 0" "map_vector Re (\<i> *s w) = 0"
    using that by (simp add:vec_eq_iff map_vector_def complex_eq_iff) 
  then obtain c where c_def: "map_vector Re (c *s w) \<noteq> 0"
    using w_def(2) by blast

  define u where "u = c *s w"

  define v where "v = map_vector Re u" 

  hence "v \<bullet> 1 = Re (cinner u 1)"
    unfolding cinner_def inner_vec_def scalar_product_def map_vector_def by simp
  also have "... = 0"
    unfolding u_def cinner_scale_left w_def(1) by simp
  finally have 1:"v \<bullet> 1 = 0" by simp

  have "A *v v = (\<chi> i. \<Sum>j\<in>UNIV. A $h i $h j * Re (u $h j))"
    unfolding matrix_vector_mult_def v_def map_vector_def by simp
  also have "... = (\<chi> i. \<Sum>j\<in>UNIV. Re ( of_real (A $h i $h j) * u $h j))"
    by simp
  also have "... = (\<chi> i. Re (\<Sum>j\<in>UNIV. A $h i $h j * u $h j))"
    unfolding A_def by simp
  also have "... = map_vector Re (A *v u)"
    unfolding map_vector_def matrix_vector_mult_def by simp
  also have "... = map_vector Re (of_real \<alpha> *s u)"
    unfolding u_def vector_scalar_commute w_def(3)  
    by (simp add:ac_simps)
  also have "... = \<alpha> *s v"
    unfolding v_def by (simp add:vec_eq_iff map_vector_def)
  finally have 2: "A *v v = \<alpha> *s v" by simp

  have 3:"v \<noteq> 0" 
    unfolding v_def u_def using c_def by simp

  show ?thesis
    by (intro exI[where x="v"] conjI 1 2 3)
qed

lemma size_evs:
  "size (eigenvalues A - {#1::complex#}) = n-1"
proof -
  have "size (eigenvalues A :: complex multiset) = n"
    using eigvals_poly_length card_n[symmetric] by auto
  thus "size (eigenvalues A - {#(1::complex)#}) = n -1"
    using ev_1 by (simp add: size_Diff_singleton)
qed

lemma find_\<gamma>\<^sub>2:
  assumes "n > 1"
  shows "\<gamma>\<^sub>a TYPE('n) \<in># image_mset cmod (eigenvalues A - {#1::complex#})"
proof -
  have "set_mset (eigenvalues A - {#(1::complex)#}) \<noteq> {}"
    using assms size_evs by auto
  hence 2: "cmod ` set_mset (eigenvalues A - {#1#}) \<noteq> {}"
    by simp
  have "\<gamma>\<^sub>a TYPE('n) \<in> set_mset (image_mset cmod (eigenvalues A - {#1#}))"
    unfolding \<gamma>\<^sub>a_def using assms 2 Max_in by auto
  thus "\<gamma>\<^sub>a TYPE('n) \<in># image_mset cmod (eigenvalues A - {#1#})"
    by simp
qed

lemma \<gamma>\<^sub>2_real_ev:
  assumes "n > 1"
  shows "\<exists>v. (\<exists>\<alpha>. abs \<alpha>=\<gamma>\<^sub>a TYPE('n) \<and> v \<bullet> 1=0 \<and> v \<noteq> 0 \<and> A *v v = \<alpha> *s v)"  
proof -
  obtain \<alpha> where \<alpha>_def: "cmod \<alpha> = \<gamma>\<^sub>a TYPE('n)" "\<alpha> \<in># eigenvalues A - {#1#}"
    using find_\<gamma>\<^sub>2[OF assms] by auto
  have "\<alpha> \<in> \<real>"
    using in_diffD[OF \<alpha>_def(2)] evs_real by auto
  then obtain \<beta> where \<beta>_def: "\<alpha> = of_real \<beta>" 
    using Reals_cases by auto

  have 0:"complex_of_real \<beta> \<in># eigenvalues A-{#1#}"
    using \<alpha>_def unfolding \<beta>_def by auto

  have 1: "\<bar>\<beta>\<bar> = \<gamma>\<^sub>a TYPE('n)"
    using \<alpha>_def unfolding \<beta>_def by simp
  show ?thesis
    using find_any_real_ev[OF 0] 1 by auto
qed

lemma \<gamma>\<^sub>a_real_bound: 
  fixes v :: "real^'n"
  assumes "v \<bullet> 1 = 0"
  shows "norm (A *v v) \<le> \<gamma>\<^sub>a TYPE('n) * norm v"
proof -
  define w where "w = map_vector complex_of_real v"

  have "cinner w 1 = v \<bullet> 1"
    unfolding w_def cinner_def map_vector_def scalar_product_def inner_vec_def 
    by simp
  also have "... = 0" using assms by simp
  finally have 0: "cinner w 1 = 0" by simp
  have "norm (A *v v) = norm (map_matrix complex_of_real A *v (map_vector complex_of_real v))"
    unfolding norm_of_real of_real_hom.mult_mat_vec_hma[symmetric] by simp
  also have "... = norm (A *v w)"
    unfolding w_def A_def map_matrix_def map_vector_def by simp
  also have "... \<le> \<gamma>\<^sub>a TYPE('n) * norm w"
    using \<gamma>\<^sub>a_bound 0 by auto
  also have "... = \<gamma>\<^sub>a TYPE('n) * norm v"
    unfolding w_def norm_of_real by simp
  finally show ?thesis by simp
qed

lemma \<Lambda>\<^sub>e_eq_\<Lambda>: "\<Lambda>\<^sub>a = \<gamma>\<^sub>a TYPE('n)"
proof -
  have "\<bar>g_inner f (g_step f)\<bar> \<le> \<gamma>\<^sub>a TYPE('n) * (g_norm f)\<^sup>2" 
    (is "?L \<le> ?R") if "g_inner f (\<lambda>_. 1) = 0" for f
  proof -
    define v where "v = (\<chi> i. f (enum_verts i))"
    have 0: " v \<bullet> 1 = 0" 
      using that unfolding g_inner_conv one_vec_def v_def by auto
    have "?L = \<bar>v \<bullet> (A *v v)\<bar>"
      unfolding g_inner_conv g_step_conv v_def by simp
    also have "... \<le> (norm v * norm (A *v v))"
      by (intro Cauchy_Schwarz_ineq2) 
    also have "... \<le> (norm v * (\<gamma>\<^sub>a TYPE('n) * norm v))"
      by (intro mult_left_mono \<gamma>\<^sub>a_real_bound 0) auto
    also have "... = ?R"
      unfolding g_norm_conv v_def by (simp add:algebra_simps power2_eq_square)
    finally show ?thesis by simp
  qed
  hence "\<Lambda>\<^sub>a \<le> \<gamma>\<^sub>a TYPE('n)"
    using \<gamma>\<^sub>a_ge_0 by (intro expander_intro_1) auto

  moreover have "\<Lambda>\<^sub>a \<ge> \<gamma>\<^sub>a TYPE('n)" 
  proof (cases "n > 1")
    case True
    then obtain v \<alpha> where v_def: "abs \<alpha> = \<gamma>\<^sub>a TYPE('n)" "A *v v =\<alpha> *s v" "v \<noteq> 0" "v \<bullet> 1 = 0"
      using \<gamma>\<^sub>2_real_ev by auto
    define f where "f x = v $h enum_verts_inv x" for x
    have v_alt: "v = (\<chi> i. f (enum_verts i))"
      unfolding f_def Rep_inverse by simp

    have "g_inner f (\<lambda>_. 1) = v \<bullet> 1"
      unfolding g_inner_conv v_alt one_vec_def by simp
    also have "... = 0" using v_def by simp
    finally have 2:"g_inner f (\<lambda>_. 1) = 0" by simp

    have "\<gamma>\<^sub>a TYPE('n) * g_norm f^2 = \<gamma>\<^sub>a TYPE('n) * norm v^2" 
      unfolding g_norm_conv v_alt by simp
    also have "... = \<gamma>\<^sub>a TYPE('n) * \<bar>v \<bullet> v\<bar>" 
      by (simp add: power2_norm_eq_inner)
    also have "... = \<bar>v \<bullet> (\<alpha> *s v)\<bar>" 
      unfolding v_def(1)[symmetric] scalar_mult_eq_scaleR 
      by (simp add:abs_mult)
    also have "... = \<bar>v \<bullet> (A *v v)\<bar>" 
      unfolding v_def by simp
    also have "... = \<bar>g_inner f (g_step f)\<bar>" 
      unfolding g_inner_conv g_step_conv v_alt by simp
    also have "... \<le> \<Lambda>\<^sub>a * g_norm f^2" 
      by (intro expansionD1 2) 
    finally have "\<gamma>\<^sub>a TYPE('n) * g_norm f^2 \<le>  \<Lambda>\<^sub>a * g_norm f^2" by simp
    moreover have "norm v^2 > 0" 
      using v_def(3) by simp
    hence "g_norm f^2 > 0" 
      unfolding g_norm_conv v_alt by simp
    ultimately show ?thesis by simp 
  next
    case False
    hence "n = 1" using n_gt_0 by simp
    hence "\<gamma>\<^sub>a TYPE('n) = 0"
      unfolding \<gamma>\<^sub>a_def by simp

    then show ?thesis using \<Lambda>_ge_0 by simp
  qed
  ultimately show ?thesis by simp
qed

lemma \<gamma>\<^sub>2_ev: 
  assumes "n > 1"
  shows "\<exists>v. v \<bullet> 1 = 0 \<and> v \<noteq> 0 \<and> A *v v = \<gamma>\<^sub>2 TYPE('n) *s v"
proof -
  have "set_mset (eigenvalues A - {#1::complex#}) \<noteq> {}"
    using size_evs assms by auto
  hence "Max (Re ` set_mset (eigenvalues A - {#1#})) \<in> Re ` set_mset (eigenvalues A - {#1#})"
    by (intro Max_in) auto
  hence "\<gamma>\<^sub>2 TYPE ('n) \<in> Re ` set_mset (eigenvalues A - {#1#})" 
    unfolding \<gamma>\<^sub>2_def using assms by simp
  then obtain \<alpha> where \<alpha>_def: "\<alpha> \<in> set_mset (eigenvalues A - {#1#})" "\<gamma>\<^sub>2 TYPE ('n) = Re \<alpha>"
    by auto
  have \<alpha>_real: "\<alpha> \<in> \<real>"
    using evs_real in_diffD[OF \<alpha>_def(1)] by auto
  have "complex_of_real (\<gamma>\<^sub>2 TYPE ('n)) = of_real (Re \<alpha>)"
    unfolding \<alpha>_def by simp
  also have "... = \<alpha>"
    using \<alpha>_real by simp
  also have "... \<in># eigenvalues A - {#1#}"
    using \<alpha>_def(1) by simp
  finally have 0:"complex_of_real (\<gamma>\<^sub>2 TYPE ('n)) \<in># eigenvalues A - {#1#}" by simp
  thus ?thesis
    using find_any_real_ev[OF 0] by auto
qed

lemma \<Lambda>\<^sub>2_eq_\<gamma>\<^sub>2: "\<Lambda>\<^sub>2 = \<gamma>\<^sub>2 TYPE ('n)"
proof (cases "n > 1")
  case True

  obtain v where v_def: "v \<bullet> 1 = 0" "v \<noteq> 0" "A *v v = \<gamma>\<^sub>2 TYPE('n) *s v" 
    using \<gamma>\<^sub>2_ev[OF True] by auto

  define f where "f x = v $h enum_verts_inv x" for x
  have v_alt: "v = (\<chi> i. f (enum_verts i))"
    unfolding f_def Rep_inverse by simp

  have "g_inner f (\<lambda>_. 1) = v \<bullet> 1"
    unfolding g_inner_conv v_alt one_vec_def by simp
  also have "... = 0" unfolding v_def(1) by simp
  finally have f_orth: "g_inner f (\<lambda>_. 1) = 0" by simp

  have "\<gamma>\<^sub>2 TYPE('n) * norm v^2= v \<bullet> (\<gamma>\<^sub>2 TYPE('n) *s v)"
    unfolding power2_norm_eq_inner by (simp add:algebra_simps scalar_mult_eq_scaleR)
  also have "... = v \<bullet> (A *v v)"
    unfolding v_def by simp
  also have "... = g_inner f (g_step f)"
    unfolding v_alt g_inner_conv g_step_conv by simp
  also have "... \<le> \<Lambda>\<^sub>2 * g_norm f^2"
    by (intro os_expanderD f_orth) 
  also have "... = \<Lambda>\<^sub>2 * norm v^2"
    unfolding v_alt g_norm_conv by simp
  finally have "\<gamma>\<^sub>2 TYPE('n) * norm v^2 \<le> \<Lambda>\<^sub>2 * norm v^2" by simp
  hence "\<gamma>\<^sub>2 TYPE('n) \<le> \<Lambda>\<^sub>2"
    using v_def(2) by simp
  moreover have "\<Lambda>\<^sub>2 \<le> \<gamma>\<^sub>2 TYPE ('n)"
    using \<gamma>\<^sub>2_bound  
    by (intro os_expanderI[OF True]) 
      (simp add: g_inner_conv g_step_conv g_norm_conv one_vec_def)
  ultimately show ?thesis by simp
next
  case False
  then show ?thesis 
    unfolding \<Lambda>\<^sub>2_def \<gamma>\<^sub>2_def by simp
qed

lemma expansionD2:
  assumes "g_inner f (\<lambda>_. 1) = 0"
  shows "g_norm (g_step f) \<le> \<Lambda>\<^sub>a * g_norm f" (is "?L \<le> ?R")
proof -
  define v where "v = (\<chi> i. f (enum_verts i))"
  have "v \<bullet> 1 = g_inner f (\<lambda>_. 1)"
    unfolding g_inner_conv v_def one_vec_def by simp
  also have "... = 0" using assms by simp
  finally have 0:"v \<bullet> 1 = 0" by simp
  have "g_norm (g_step f) = norm (A *v v)"
    unfolding g_norm_conv g_step_conv v_def by auto
  also have "... \<le> \<Lambda>\<^sub>a * norm v"
    unfolding \<Lambda>\<^sub>e_eq_\<Lambda> by (intro \<gamma>\<^sub>a_real_bound 0)
  also have "... = \<Lambda>\<^sub>a * g_norm f"
    unfolding g_norm_conv v_def by simp
  finally show ?thesis by simp
qed

lemma rayleigh_bound: 
  fixes v :: "real^'n"
  shows "\<bar>v \<bullet> (A *v v)\<bar> \<le> norm v^2"
proof -
  define f where "f x = v $h enum_verts_inv x" for x
  have v_alt: "v = (\<chi> i. f (enum_verts i))"
    unfolding f_def Rep_inverse by simp

  have "\<bar>v \<bullet> (A *v v)\<bar> = \<bar>g_inner f (g_step f)\<bar>"
    unfolding v_alt g_inner_conv g_step_conv by simp
  also have "... = \<bar>(\<Sum>a\<in>arcs G. f (head G a) * f (tail G a))\<bar>/d"
    unfolding g_inner_step_eq by simp
  also have "... \<le> (d * (g_norm f)\<^sup>2) / d"
    by (intro divide_right_mono bdd_above_aux) auto
  also have "... = g_norm f^2" 
    using d_gt_0 by simp
  also have "... = norm v^2"
    unfolding g_norm_conv v_alt by simp
  finally show ?thesis by simp
qed

text \<open>The following implies that two-sided expanders are also one-sided expanders.\<close>

lemma \<Lambda>\<^sub>2_range: "\<bar>\<Lambda>\<^sub>2\<bar> \<le> \<Lambda>\<^sub>a"
proof (cases "n > 1")
  case True
  hence 0:"set_mset (eigenvalues A - {#1::complex#}) \<noteq> {}"
    using size_evs by auto

  have "\<gamma>\<^sub>2 TYPE ('n) = Max (Re ` set_mset (eigenvalues A - {#1::complex#}))"
    unfolding \<gamma>\<^sub>2_def using True by simp
  also have "... \<in> Re ` set_mset (eigenvalues A - {#1::complex#})"
    using Max_in 0 by simp
  finally have "\<gamma>\<^sub>2 TYPE ('n) \<in> Re ` set_mset (eigenvalues A - {#1::complex#})"
    by simp
  then obtain \<alpha> where \<alpha>_def: "\<alpha> \<in> set_mset (eigenvalues A - {#1::complex#})" "\<gamma>\<^sub>2 TYPE ('n) = Re \<alpha>"
    by auto

  have "\<bar>\<Lambda>\<^sub>2\<bar> = \<bar>\<gamma>\<^sub>2 TYPE ('n) \<bar>"
    using \<Lambda>\<^sub>2_eq_\<gamma>\<^sub>2 by simp
  also have "... = \<bar>Re \<alpha>\<bar>" 
    using \<alpha>_def by simp
  also have "... \<le> cmod \<alpha>"
    using abs_Re_le_cmod by simp
  also have "... \<le> Max (cmod ` set_mset (eigenvalues A - {#1#}))"
    using \<alpha>_def(1) by (intro Max_ge) auto
  also have "... \<le> \<gamma>\<^sub>a TYPE('n)" 
    unfolding \<gamma>\<^sub>a_def using True by simp
  also have "... = \<Lambda>\<^sub>a"
    using \<Lambda>\<^sub>e_eq_\<Lambda> by simp
  finally show ?thesis by simp
next 
  case False
  thus ?thesis 
    unfolding \<Lambda>\<^sub>2_def \<Lambda>\<^sub>a_def by simp
qed

end

lemmas (in regular_graph) expansionD2 =  
  regular_graph_tts.expansionD2[OF eg_tts_1,
    internalize_sort "'n :: finite", OF _ regular_graph_axioms, 
    unfolded remove_finite_premise, cancel_type_definition, OF verts_non_empty]

lemmas (in regular_graph) \<Lambda>\<^sub>2_range =  
  regular_graph_tts.\<Lambda>\<^sub>2_range[OF eg_tts_1,
    internalize_sort "'n :: finite", OF _ regular_graph_axioms, 
    unfolded remove_finite_premise, cancel_type_definition, OF verts_non_empty]

unbundle no_intro_cong_syntax

end