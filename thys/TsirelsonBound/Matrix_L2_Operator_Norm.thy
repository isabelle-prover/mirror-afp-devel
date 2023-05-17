(*
Author: 
  Mnacho Echenim, Université Grenoble Alpes
*)

theory Matrix_L2_Operator_Norm 
  imports 
    Tensor_Mat_Compl_Properties
begin
text \<open>We formalize the $\mathcal{L}_2$ operator norm on matrices on nonempty vector spaces. This norm can 
be defined on a matrix $A$ by $\|A\|_2 = \sup \{\|A\cdot v\|_2\,\mid\, \|v\|_2 = 1\}$, and it 
is equal to the maximum singular value of $A$.\<close>

section \<open>Preliminary results\<close>


subsection \<open>Commutator and anticommutator\<close>
text \<open>We define the notions of commutator and anticommutator of two matrices. When these matrices
commute, their commutator is the zero matrix.\<close>

definition commutator :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> 
  complex Matrix.mat" where
"commutator A B = A * B - B * A"

definition anticommutator where
"anticommutator A B = A * B + B * A"

lemma commutator_dim:
  assumes "A \<in> carrier_mat n n"
  and "B \<in> carrier_mat n n"
shows "commutator A B \<in> carrier_mat n n" using assms unfolding commutator_def
  by (metis minus_carrier_mat mult_carrier_mat) 

lemma anticommutator_dim:
  assumes "A \<in> carrier_mat n n"
  and "B \<in> carrier_mat n n"
shows "anticommutator A B \<in> carrier_mat n n" using assms 
  unfolding anticommutator_def
  by (metis add_carrier_mat mult_carrier_mat)

lemma commutator_zero_iff:
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
shows "commutator A B = 0\<^sub>m n n \<longleftrightarrow> A*B = B * A"
proof -
  have "A*B \<in> carrier_mat n n" using assms by simp
  moreover have "B*A\<in> carrier_mat n n" using assms by simp
  ultimately show ?thesis unfolding commutator_def
    by (metis left_add_zero_mat mat_minus_minus minus_r_inv_mat)
qed

lemma anticommutator_zero_iff:
  fixes A::"'a ::ring Matrix.mat"
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
shows "anticommutator A B = 0\<^sub>m n n \<longleftrightarrow> B*A = -(A*B)"
proof -
  have ab: "A*B \<in> carrier_mat n n" using assms by simp
  have ba: "B*A\<in> carrier_mat n n" using assms by simp
  show ?thesis unfolding anticommutator_def
  proof
    assume "A * B + B * A = 0\<^sub>m n n"
    thus "B*A = - (A*B)" using ab ba mat_add_eq_0_if by auto
  next
    show "B * A = - (A * B) \<Longrightarrow> A * B + B * A = 0\<^sub>m n n" using ab ba
      by (metis uminus_l_inv_mat uminus_uminus_mat) 
  qed
qed

lemma commutator_mult_expand:
  assumes "A \<in> carrier_mat n n"
  and "B \<in> carrier_mat n n"
  and "C \<in> carrier_mat n n"
  and "D \<in> carrier_mat n n"
shows "commutator A B * commutator C D = 
  A * B * (C * D) - A * B * (D * C) - B * A * (C * D) + B * A * (D * C)" 
proof -
  have "commutator A B * commutator C D = A * B * commutator C D - 
    B * A * commutator C D"
    using assms commutator_def 
      minus_mult_distrib_mat[of "A * B" n n "B * A" "commutator C D"]
      commutator_dim[of C n D] by simp
  also have "... = A * B * (C * D) - A * B * (D * C) - B * A * commutator C D"
    using assms commutator_def 
      mult_minus_distrib_mat[of "A * B" n n "C * D" n "D * C"]
    by simp
  also have "... = A * B * (C * D) - A * B * (D * C) - B * A * (C * D) +
     B * A * (D * C)" 
    using assms commutator_def 
      mult_minus_distrib_mat[of "B * A" n n "C * D" n "D * C"]
    by (auto simp add:  algebra_simps)
  finally show ?thesis .
qed


section \<open>Maximum modulus in a spectrum\<close>
text \<open>We prove some basic results on the maximum modulus of elements in a matrix $A$,
and focus on the case where $A$ is a Hermitian matrix.\<close>

subsection \<open>Definition and basic properties for Hermitian matrices\<close>
definition spmax:: "complex Matrix.mat \<Rightarrow> real" where
"spmax A = Max.F {cmod a|a. a\<in> spectrum A}"

lemma spmax_mem:
  assumes "A \<in> carrier_mat n n"
  and "0 < n"
shows "spmax A \<in> {cmod a|a. a \<in> spectrum A}"
proof -
  define del where "del = {cmod a|a. a \<in> spectrum A}"
  define M where "M = Max.F del"
  have "del \<noteq> {}" using spectrum_ne assms unfolding del_def by auto
  moreover have "\<And>x. x \<in> del \<Longrightarrow> 0 \<le> x" unfolding del_def by force
  have "finite del" using del_def by (simp add: spectrum_finite) 
  hence "M \<in> {cmod a|a. a \<in> spectrum A}" 
    using  Max_in[of del] \<open>del \<noteq> {}\<close> M_def del_def by simp
  thus ?thesis unfolding spmax_def M_def del_def .
qed

lemma spmax_geq_0:
  assumes "A \<in> carrier_mat n n" 
  and "0 < n"
  shows "0 \<le> spmax A" 
proof -
  define del where "del = {cmod a|a. a \<in> spectrum A}"
  define M where "M = Max.F del"
  have "del \<noteq> {}" using spectrum_ne assms unfolding del_def by auto
  moreover have "\<And>x. x \<in> del \<Longrightarrow> 0 \<le> x" unfolding del_def by force
  have "finite del" using del_def by (simp add: spectrum_finite) 
  hence "M \<in> del" using  Max_in[of del] \<open>del \<noteq> {}\<close> M_def by simp
  hence "0 \<le> M" using \<open>\<And>x. x \<in> del \<Longrightarrow> 0 \<le> x\<close> by simp
  thus ?thesis unfolding spmax_def del_def M_def .
qed

lemma Re_inner_mult_diag_le:
  fixes B::"complex Matrix.mat"
  assumes "diagonal_mat B"
  and "B \<in> carrier_mat n n"
  and "0 < n"
  and "M = Max.F {Re (conjugate a)|a. a\<in> diag_elems B}"
shows "\<forall> v \<in> carrier_vec n. Re (inner_prod (B *\<^sub>v v) v) \<le> 
  M * Re ((inner_prod v v))" 
proof -
  define del where "del = {Re (conjugate a)|a. a\<in> diag_elems B}"
  have "finite del" using del_def by simp
  moreover have "del \<noteq> {}" using diag_elems_ne[of B] assms del_def by simp
  ultimately have "M \<in> del" using  Max_in[of del] del_def assms 
    unfolding spmax_def by simp
  have "\<forall> v \<in> carrier_vec n. Re (inner_prod (B *\<^sub>v v) v) \<le> 
    M * Re ((inner_prod v v))" 
  proof
    fix v::"complex Matrix.vec"
    assume "v \<in> carrier_vec n"
    hence " Re (inner_prod (B *\<^sub>v v) v) = 
      Re (\<Sum> i \<in> {0 ..< n}. (conjugate (B $$ (i,i))) * 
      (vec_index v i *  (conjugate (vec_index v i))))" 
      using assms inner_mult_diag_expand by simp
    also have "... = (\<Sum> i \<in> {0 ..< n}. Re ((conjugate (B $$ (i,i))) * 
      (vec_index v i *  (conjugate (vec_index v i)))))" by simp
    also have "... \<le> (\<Sum> i \<in> {0 ..< n}. M * 
      Re (vec_index v i *  (conjugate (vec_index v i))))"
    proof (rule sum_mono)
      show "\<And>i. i \<in> {0..<n} \<Longrightarrow>  Re ((conjugate (B $$ (i,i))) * 
      (vec_index v i *  (conjugate (vec_index v i)))) \<le> 
      M * Re  (vec_index v i *  (conjugate (vec_index v i)))"
      proof -
        fix i
        assume "i \<in> {0 ..< n}"
        hence "Re ((conjugate (B $$ (i,i))) * 
          (vec_index v i *  (conjugate (vec_index v i)))) = 
          Re (conjugate (B $$ (i,i))) * Re (vec_index v i *  
          (conjugate (vec_index v i)))"
          using real_mult_re mult_conj_real assms by auto
        also have "... \<le> M *  Re (vec_index v i * (conjugate (vec_index v i)))"
        proof -
          have "Re (conjugate (B $$ (i, i))) \<in> del" using assms \<open>i \<in> {0 ..< n}\<close> 
            unfolding del_def diag_elems_def by auto
          hence rel: "Re (conjugate (B $$ (i, i))) \<le> M" 
            using assms \<open>finite del\<close> del_def by auto
          have "0 \<le> vec_index v i * conjugate (vec_index v i)" 
            using less_eq_complex_def by simp
          moreover have "vec_index v i * conjugate (vec_index v i) = 
            Re (vec_index v i * conjugate (vec_index v i))" 
            using mult_conj_real complex_is_Real_iff
            by (metis of_real_Re)  
          ultimately have "0 \<le> Re (vec_index v i * conjugate (vec_index v i))" 
            by simp
          thus "Re (conjugate (B $$ (i, i))) * Re (vec_index v i * 
            conjugate (vec_index v i)) \<le> 
            M * Re (vec_index v i * conjugate (vec_index v i))" 
            using rel mult_right_mono by blast
        qed
        finally show 
          "Re ((conjugate (B $$ (i,i))) * (vec_index v i *  
          (conjugate (vec_index v i)))) \<le> 
          M * Re (vec_index v i * conjugate (vec_index v i))" .
      qed
    qed 
    also have "... = Re (\<Sum> i \<in> {0 ..< n}. M * 
      (vec_index v i *  (conjugate (vec_index v i))))" 
      by simp
    also have "... = Re (M * (inner_prod v v))"
    proof -
      have "(\<Sum> i \<in> {0 ..< n}. M*(vec_index v i * (conjugate (vec_index v i))))=
        M * (\<Sum> i \<in> {0 ..< n}. (vec_index v i *  (conjugate (vec_index v i))))" 
        by (simp add: sum_distrib_left)
      also have "... = M * (inner_prod v v)" unfolding Matrix.scalar_prod_def 
        using assms \<open>v \<in> carrier_vec n\<close> by force
      finally show ?thesis by simp
    qed
    also have "... = M * Re (inner_prod v v)" using assms by simp
    finally show "Re (Complex_Matrix.inner_prod (B *\<^sub>v v) v) \<le> 
      M * Re (Complex_Matrix.inner_prod v v)" .
  qed
  thus ?thesis using assms by auto
qed

lemma Re_inner_mult_diag_le':
  fixes B::"complex Matrix.mat"
  assumes "diagonal_mat B"
  and "B \<in> carrier_mat n n"
  and "0 < n"
  and "(M::real) = Max.F {cmod a|a. a\<in> diag_elems B}"
  and "v\<in> carrier_vec n"
shows "cmod (inner_prod v (B *\<^sub>v v)) \<le> M * inner_prod v v" 
proof -
  define del where "del = {cmod a|a. a\<in> diag_elems B}"
  have "finite del" using del_def by simp
  moreover have "del \<noteq> {}" using diag_elems_ne[of B] assms del_def by simp
  ultimately have "M \<in> del" using  Max_in[of del] del_def assms 
    unfolding  spmax_def by simp
  have "cmod (inner_prod v (B *\<^sub>v v)) = cmod (\<Sum> i \<in> {0 ..< n}. B $$ (i,i) * 
      (vec_index v i *  (conjugate (vec_index v i))))" 
    using assms inner_mult_diag_expand' by simp
  also have "... \<le> (\<Sum> i \<in> {0 ..< n}. cmod (B $$ (i,i) * 
    (vec_index v i *  (conjugate (vec_index v i)))))" 
    by (simp add: sum_norm_le) 
  also have "... \<le> (\<Sum> i \<in> {0 ..< n}. M * 
    cmod (vec_index v i *  (conjugate (vec_index v i))))"
  proof (rule sum_mono)
    show "\<And>i. i \<in> {0..<n} \<Longrightarrow>  cmod (B $$ (i,i) * 
    (vec_index v i *  (conjugate (vec_index v i)))) \<le> 
    M * cmod  (vec_index v i *  (conjugate (vec_index v i)))"
    proof -
      fix i
      assume "i \<in> {0 ..< n}"
      hence "cmod (B $$ (i,i) * (vec_index v i *(conjugate (vec_index v i)))) = 
        cmod (B $$ (i,i)) * cmod (vec_index v i *  (conjugate (vec_index v i)))"
        by (simp add: norm_mult)
      also have "... \<le> M *  cmod (vec_index v i *  (conjugate (vec_index v i)))"
      proof -
        have "cmod (B $$ (i, i)) \<in> del" using assms \<open>i \<in> {0 ..< n}\<close> 
          unfolding del_def diag_elems_def by auto
        hence  "cmod (B $$ (i, i)) \<le> M" using assms \<open>finite del\<close> del_def 
          by auto
        thus ?thesis using mult_right_mono norm_ge_zero by blast
      qed
      finally show 
        "cmod (B $$ (i,i) * (vec_index v i *  (conjugate (vec_index v i)))) \<le> 
        M * cmod (vec_index v i * conjugate (vec_index v i))" .
    qed
  qed 
  also have "... = (\<Sum> i \<in> {0 ..< n}. M * 
    (vec_index v i *  (conjugate (vec_index v i))))"
    using cmod_conjugate_square_eq by auto
  also have "... = M * (\<Sum> i \<in> {0 ..< n}. 
    (vec_index v i *  (conjugate (vec_index v i))))" 
    by (simp add: sum_distrib_left) 
  also have "... = M * (inner_prod v v)" unfolding Matrix.scalar_prod_def 
    using assms \<open>v \<in> carrier_vec n\<close> by force
  finally show ?thesis using less_eq_complex_def by simp
qed

lemma hermitian_mult_inner_prod_le:
  fixes A::"complex Matrix.mat"
  assumes "A \<in> carrier_mat n n"
  and "0 < n"
  and "hermitian A"
  and "v \<in> carrier_vec n"
  shows "cmod (inner_prod v (A *\<^sub>v v)) \<le> (spmax A) * (inner_prod v v)"
proof - 
  obtain B U where bu: "real_diag_decomp A B U"  
    using assms hermitian_real_diag_decomp[of A] by auto
  define M where "M = Max.F {cmod a|a. a\<in> diag_elems B}"
  have meq: "M = spmax A" unfolding spmax_def M_def 
    using unitary_diag_spectrum_eq'[of A] bu 
    by (metis assms(1) real_diag_decompD(1))
  have uc: "Complex_Matrix.adjoint U \<in> carrier_mat n n" using bu
    by (meson adjoint_dim' assms(1) real_diag_decompD(1) 
        unitary_diag_carrier(2))
  hence mv: "U * B * (Complex_Matrix.adjoint U) *\<^sub>v v = 
    U  *\<^sub>v (B  *\<^sub>v ((Complex_Matrix.adjoint U) *\<^sub>v v))" 
    using assoc_mat_mult_vec'[of U] assms bu real_diag_decompD(1) 
      unitary_diag_carrier(1) 
    by (metis Complex_Matrix.adjoint_adjoint adjoint_dim)
  have "inner_prod v (A *\<^sub>v v) = inner_prod v (U  *\<^sub>v (B  *\<^sub>v 
    ((Complex_Matrix.adjoint U) *\<^sub>v v)))"
    using unitarily_equiv_eq bu mv real_diag_decompD(1)
    by (metis unitary_diag_imp_unitarily_equiv)
  also have "... = inner_prod ((Complex_Matrix.adjoint U) *\<^sub>v v) 
    (B *\<^sub>v  ((Complex_Matrix.adjoint U) *\<^sub>v v))"      
  proof (rule adjoint_def_alter)
    show "v\<in> carrier_vec n" using \<open>v\<in> carrier_vec n\<close> .
    show "U \<in> carrier_mat n n" using uc
      by (metis Complex_Matrix.adjoint_adjoint adjoint_dim') 
    have "(Complex_Matrix.adjoint U *\<^sub>v v) \<in> carrier_vec n" 
      using \<open>Complex_Matrix.adjoint U \<in> carrier_mat n n\<close> \<open>v\<in> carrier_vec n\<close> 
      by simp
    thus "B *\<^sub>v (Complex_Matrix.adjoint U *\<^sub>v v) \<in> carrier_vec n" 
      using assms bu real_diag_decompD(1) unitary_diag_carrier(1)
      by (metis mult_mat_vec_carrier)
  qed
  finally have "inner_prod v (A *\<^sub>v v) = 
    inner_prod ((Complex_Matrix.adjoint U) *\<^sub>v v) 
    (B *\<^sub>v  ((Complex_Matrix.adjoint U) *\<^sub>v v))" .
  hence "cmod (inner_prod v (A *\<^sub>v v)) = 
    cmod (inner_prod ((Complex_Matrix.adjoint U) *\<^sub>v v)
    (B *\<^sub>v  ((Complex_Matrix.adjoint U) *\<^sub>v v)))" by simp
  also have "... \<le> M * inner_prod (Complex_Matrix.adjoint U *\<^sub>v v) 
    (Complex_Matrix.adjoint U *\<^sub>v v)"
  proof (rule Re_inner_mult_diag_le')
    show bc: "B\<in> carrier_mat n n" 
      using assms bu real_diag_decompD(1) unitary_diag_carrier(1) by metis
    show "M = Max.F {cmod a |a. a \<in> diag_elems B}"
      using M_def by simp
    show "(Complex_Matrix.adjoint U *\<^sub>v v) \<in> carrier_vec n" 
      using \<open>Complex_Matrix.adjoint U \<in> carrier_mat n n\<close> \<open>v\<in> carrier_vec n\<close>
      by simp
    show "diagonal_mat B" using assms bu real_diag_decompD(1) unitary_diagD(2) 
      by metis
    show "0 < n" using assms by simp
  qed 
  also have "... = M * inner_prod v v" 
  proof -
    have "unitary U" using bu unitarily_equivD(1)
      using real_diag_decompD(1) unitary_diagD(3) by blast 
    thus ?thesis using  assms bu uc unitary_inner_prod
      by (metis Complex_Matrix.adjoint_adjoint adjoint_dim' unitary_adjoint 
          unitary_inner_prod) 
  qed
  finally show ?thesis using meq by simp
qed

lemma  hermitian_trace_rank_le:
assumes "A \<in> carrier_mat n n"
  and "hermitian A"
  and "v \<in> carrier_vec n"
  and "0 < n"
shows "cmod (Complex_Matrix.trace (A * (rank_1_proj v))) \<le> 
  (spmax A) * (inner_prod v v)"
  using assms  hermitian_mult_inner_prod_le
  by (metis rank_1_proj_trace_inner) 

lemma hermitian_pos_decomp_cmod_le:
  assumes "A\<in> carrier_mat n n"
  and "C\<in> carrier_mat n n"
  and "0 < n"
and "hermitian C"
and "Complex_Matrix.positive A"
shows "cmod (Complex_Matrix.trace (C * A)) \<le> 
  Re (Complex_Matrix.trace A) * (spmax C)"
proof -
  have a: "A\<in> carrier_mat n n" using assms by simp
  have b: "C\<in> carrier_mat n n" using assms by simp
  have "0 < n" using assms by simp
  obtain B U where bu: "real_diag_decomp A B U"
    using hermitian_real_diag_decomp[of A] positive_is_hermitian assms by auto
  have ud: "unitary_diag A B U" using bu by simp
  have "Complex_Matrix.positive A" using assms by simp
  {
    fix i
    assume "i <n"
    have "cmod (Complex_Matrix.trace (C * rank_1_proj (Matrix.col U i))) \<le> 
      spmax C * inner_prod (Matrix.col U i) (Matrix.col U i)"
    proof (rule hermitian_trace_rank_le)
      show "C\<in> carrier_mat n n" "hermitian C" using assms by simp+
      show "Matrix.col U i \<in> carrier_vec n" using 
          unitary_diag_carrier(2) assms ud 
        by (metis carrier_dim_vec carrier_matD(1) dim_col)
    qed (simp add: assms)
    also have "... = spmax C"
    proof -
      have "inner_prod (Matrix.col U i) (Matrix.col U i) = \<parallel>Matrix.col U i\<parallel>\<^sup>2"
        using vec_norm_sq_cpx_vec_length_sq inner_prod_vec_norm_pow2 by auto
      also have "... = 1" using unitary_col_norm_square assms unitary_diagD(3) 
        unitary_diag_carrier(2) ud
        by (metis \<open>i < n\<close> of_real_eq_1_iff)
      finally show ?thesis by simp
    qed
    finally have 
      "cmod (Complex_Matrix.trace (C * rank_1_proj (Matrix.col U i))) \<le> spmax C" 
      using less_eq_complex_def by simp
  } note mprop = this
  thus "cmod (Complex_Matrix.trace (C * A)) \<le> 
    Re (Complex_Matrix.trace A) * spmax C" 
    using a b ud positive_decomp_cmod_le  assms by simp 
qed

lemma hermitian_density_cmod_le:
  fixes R::"complex Matrix.mat"
  assumes "R\<in> carrier_mat n n"
  and "A\<in> carrier_mat n n"
  and "0 < n"
and "hermitian A"
and "density_operator R"
shows "cmod (Complex_Matrix.trace (A * R)) \<le> (spmax A)"
proof -
  have "cmod (Complex_Matrix.trace (A * R)) \<le> 
    Re (Complex_Matrix.trace R) * (spmax A)"
    using hermitian_pos_decomp_cmod_le assms unfolding density_operator_def 
    by blast
  also have "... = spmax A" using assms unfolding density_operator_def by simp
  finally show ?thesis .
qed

lemma tensor_mat_hermitian_positive_le:
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat m m"
  and "C\<in> carrier_mat n n"
  and "D\<in> carrier_mat m m"
  and "0 < n"
  and "0 < m"
  and "hermitian A"
  and "hermitian B"
  and "Complex_Matrix.positive C"
  and "Complex_Matrix.positive D"
shows "cmod (Complex_Matrix.trace ((A\<Otimes>B)*(C\<Otimes>D))) \<le> 
  Re (Complex_Matrix.trace C) * Re (Complex_Matrix.trace D) *
  spmax A * spmax B"
proof -
  have "Complex_Matrix.trace ((A\<Otimes>B)*(C\<Otimes>D)) = 
    Complex_Matrix.trace ((A*C) \<Otimes> (B*D))"
    using mult_distr_tensor assms
    by (metis carrier_matD(2) positive_dim_eq)
  also have "... = 
    Complex_Matrix.trace (A * C) * (Complex_Matrix.trace (B * D))"
    using assms tensor_mat_trace by (meson mult_carrier_mat)
  finally have "Complex_Matrix.trace ((A\<Otimes>B)*(C\<Otimes>D)) = 
    Complex_Matrix.trace (A * C) * (Complex_Matrix.trace (B * D))" .
  hence "cmod (Complex_Matrix.trace ((A\<Otimes>B)*(C\<Otimes>D))) = 
    cmod (Complex_Matrix.trace (A * C)) *
    cmod (Complex_Matrix.trace (B * D))"
    by (simp add: norm_mult) 
  also have "... \<le> Re (Complex_Matrix.trace C) * spmax A *
    cmod (Complex_Matrix.trace (B * D))"
    by (meson assms(1) assms(3) assms(5) assms(7) assms(9) 
        hermitian_pos_decomp_cmod_le mult_right_mono norm_ge_zero) 
  also have "... \<le> Re (Complex_Matrix.trace C) * spmax A *
    Re (Complex_Matrix.trace D) * spmax B"
  proof -
    have "0 \<le> Re (Complex_Matrix.trace C) * spmax A" 
      using assms positive_trace spmax_geq_0
      by (simp add: cpx_ge_0_real nonnegative_complex_is_real)
    moreover have "cmod (Complex_Matrix.trace (B * D)) \<le> 
      Re (Complex_Matrix.trace D) * spmax B"
      using assms hermitian_pos_decomp_cmod_le by auto 
    ultimately show ?thesis
      by (metis Groups.mult_ac(2) Groups.mult_ac(3) mult_left_mono)
  qed
  also have "... = Re (Complex_Matrix.trace C) * 
    Re (Complex_Matrix.trace D) * spmax A * spmax B" by simp
  finally show ?thesis .
qed

lemma tensor_mat_hermitian_density_le:
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat m m"
  and "C\<in> carrier_mat n n"
  and "D\<in> carrier_mat m m"
  and "0 < n"
  and "0 < m"
  and "hermitian A"
  and "hermitian B"
  and "density_operator C"
  and "density_operator D"
shows "cmod (Complex_Matrix.trace ((A\<Otimes>B)*(C\<Otimes>D))) \<le> 
  spmax A * spmax B"
proof -
  have "cmod (Complex_Matrix.trace ((A\<Otimes>B)*(C\<Otimes>D))) \<le> 
  Re (Complex_Matrix.trace C) * Re (Complex_Matrix.trace D) *
  spmax A * spmax B" 
    by (meson assms density_operator_def tensor_mat_hermitian_positive_le)
  moreover have "Complex_Matrix.trace C = 1" 
    using assms unfolding density_operator_def by simp
  moreover have "Complex_Matrix.trace D = 1" 
    using assms unfolding density_operator_def by simp
  ultimately show ?thesis by simp
qed




lemma idty_spmax:
  assumes "0 < n"
  shows "spmax (1\<^sub>m n) = 1" using idty_spectrum assms unfolding spmax_def by simp

lemma spmax_uminus:
  fixes A::"complex Matrix.mat"
  assumes "hermitian A"
  and "A\<in> carrier_mat n n"
  and "0 < n"
  shows "spmax (-A) = spmax A" 
proof -
  have "{cmod a |a. a \<in> spectrum (- A)} = {cmod (-a) |a. a \<in> spectrum A}"
    using assms spectrum_uminus[of A n]
    by (smt (verit) Collect_cong mem_Collect_eq)
  also have "... = {cmod a |a. a \<in> spectrum A}" by simp
  finally have "{cmod a |a. a \<in> spectrum (- A)} = 
    {cmod a |a. a \<in> spectrum A}" .
  thus ?thesis unfolding spmax_def by simp
qed

lemma spmax_smult:
fixes A::"complex Matrix.mat"
  assumes "hermitian A"
  and "A\<in> carrier_mat n n"
  and "0 < n"
  shows "spmax (x \<cdot>\<^sub>m A) = cmod x * spmax A" 
proof -
  have "{cmod a |a. a \<in> spectrum (x \<cdot>\<^sub>m A)} = {cmod (x*a) |a. a \<in> spectrum A}"
    using assms spectrum_smult[of A n] by auto
  also have "... = {cmod x * cmod a |a. a \<in> spectrum A}" 
    by (simp add: norm_mult)  
  finally have eq: "{cmod a |a. a \<in> spectrum (x \<cdot>\<^sub>m A)} = 
    {cmod x * cmod a |a. a \<in> spectrum A}" .
  have "\<forall>b \<in> {cmod a |a. a \<in> spectrum A}. 0 \<le> b" by auto
  moreover have "finite {cmod a |a. a \<in> spectrum A}" 
    by (simp add: spectrum_finite) 
  moreover have "{cmod a |a. a \<in> spectrum A} \<noteq> {}" 
    using assms spectrum_ne by fastforce
  moreover have "{cmod x * a |a. a \<in> {cmod a |a. a \<in> spectrum A}} = 
    {cmod x * cmod a |a. a \<in> spectrum A}" by auto
  ultimately have "Max.F {cmod x * cmod a |a. a \<in> spectrum A} = 
    cmod x * Max.F {cmod a |a. a \<in> spectrum A}"
    using pos_mult_Max[of "{cmod a |a. a \<in> spectrum A}"]
    by (smt (verit) Collect_cong norm_ge_zero)
  thus ?thesis using eq unfolding spmax_def by auto
qed

lemma spmax_smult_pos:
fixes A::"complex Matrix.mat"
  assumes "hermitian A"
  and "A\<in> carrier_mat n n"
  and "0 < n"
  and "0 \<le> x"
  shows "spmax (x \<cdot>\<^sub>m A) = x * spmax A" 
proof -
  have "spmax (x \<cdot>\<^sub>m A) = cmod x * spmax A" 
    using assms spmax_smult by simp
  also have "... = x * spmax A" using assms by simp
  finally show ?thesis .
qed

lemma hermitian_square_spmax:
fixes A::"complex Matrix.mat"
  assumes "hermitian A"
and "A\<in> carrier_mat n n"
and "0 < n"
shows "spmax (A*A) = spmax A * spmax A"
proof -
  have "spmax (A * A) = Max.F {cmod (a*a) |a. a \<in> spectrum A}" 
  proof -
    have "{cmod a|a. a \<in> spectrum (A*A)} = {cmod (a*a) |a. a \<in> spectrum A}"
      using assms hermitian_square_spectrum_eq[of A n]  by auto
    thus ?thesis unfolding spmax_def by simp
  qed
  also have "... = Max.F {cmod a * cmod a|a. a\<in> spectrum A}" 
    by (simp add: norm_mult)
  also have "... = spmax A * spmax A" unfolding spmax_def
  proof (rule square_Max)
    show "finite (spectrum A)" using spectrum_finite[of A] by simp
    show "spectrum A \<noteq> {}" using spectrum_ne[of A] assms by simp
  qed auto
  finally show ?thesis .
qed

lemma hermitian_square_idty_spmax:
  assumes "0 < n"
  and "A\<in> carrier_mat n n"
  and "hermitian A"
  and "A*A = 1\<^sub>m n"
shows "spmax A = 1" 
proof -
  have "spmax A * spmax A = 1" 
    using hermitian_square_spmax[of A] assms idty_spmax by simp
  thus "spmax A = 1" 
    using spmax_geq_0 assms
    by (metis abs_of_nonneg le_numeral_extra(1) more_arith_simps(6) 
        real_sqrt_abs2)
qed

lemma hermitian_mult_density_trace:
  assumes "A\<in> carrier_mat n n"
  and "R\<in> carrier_mat n n"
  and "0 < n"
  and "hermitian A"
  and "A * A = 1\<^sub>m n"
  and "density_operator R"
shows "\<bar>Complex_Matrix.trace (A*R)\<bar> \<le> 1"
proof -
  have "spmax A = 1" using assms hermitian_square_idty_spmax by simp
  hence "cmod (Complex_Matrix.trace (A*R)) \<le> 1" 
    using hermitian_density_cmod_le assms by metis
  thus ?thesis using abs_cmod_eq
    by (metis Reals_of_real abs_norm_cancel cpx_real_abs_eq 
        cpx_real_abs_leq of_real_1) 
qed

lemma tensor_mat_hermitian_density_spmax_le:
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat m m"
  and "C\<in> carrier_mat n n"
  and "D\<in> carrier_mat m m"
  and "0 < n"
  and "0 < m"
  and "hermitian A"
  and "hermitian B"
  and "A * A = 1\<^sub>m n"
  and "B * B = 1\<^sub>m m"
  and "density_operator C"
  and "density_operator D"
shows "cmod (Complex_Matrix.trace ((A\<Otimes>B)*(C\<Otimes>D))) \<le> 1"
proof -
  have "cmod (Complex_Matrix.trace ((A\<Otimes>B)*(C\<Otimes>D))) \<le> 
  spmax A * spmax B"
    using tensor_mat_hermitian_density_le assms by simp
  moreover have "spmax A = 1"
    by (metis assms(1) assms(5) assms(7) assms(9) 
        hermitian_square_spmax idty_spmax less_1_mult 
        linorder_le_less_linear mult_eq_1 semiring_norm(138) 
        spmax_geq_0)
  moreover have "spmax B = 1"
    by (metis assms(10) assms(2) assms(6) assms(8) 
        hermitian_square_spmax idty_spmax less_1_mult 
        linorder_le_less_linear mult_eq_1 semiring_norm(138) 
        spmax_geq_0)
  ultimately show ?thesis by simp
qed


subsection \<open>Eigenvector for the element with maximum modulus\<close>

definition spmax_wit where
"spmax_wit A = (SOME k. eigenvalue A k \<and> spmax A = cmod k)"

lemma spmax_wit_eigenvalue:
  assumes "A\<in> carrier_mat n n"
  and "0 < n"
  shows "eigenvalue A (spmax_wit A) \<and> spmax A = cmod (spmax_wit A)"
proof -
  let ?V = "SOME k. eigenvalue A k \<and> spmax A = cmod k"
  have vprop: "eigenvalue A ?V \<and> spmax A = cmod ?V" using 
      someI_ex[of "\<lambda>h. eigenvalue A h \<and> spmax A = cmod h"]
       spmax_def spmax_mem assms spectrum_eigenvalues
    by (metis (mono_tags, lifting) mem_Collect_eq)
  thus ?thesis using spmax_wit_def by simp 
qed

lemma find_eigen_spmax_neq_0:
  assumes "A\<in> carrier_mat n n"
  and "0 < n"
shows "find_eigenvector A (spmax_wit A) \<noteq> 0\<^sub>v n" using 
    find_eigenvector assms spmax_wit_eigenvalue unfolding eigenvector_def
  by blast

lemma find_eigen_spmax_dim:
  assumes "A\<in> carrier_mat n n"
  and "0 < n"
shows "dim_vec (vec_normalize (find_eigenvector A (spmax_wit A))) = n" 
  using find_eigenvector assms spmax_wit_eigenvalue  
  unfolding  eigenvector_def
  by (metis carrier_dim_vec carrier_matD(1) carrier_vec_dim_vec 
      normalized_vec_dim)

lemma nrm_spmax_eigenvector_eq:
  assumes "v = vec_normalize (find_eigenvector A (spmax_wit A))"
  and "A\<in> carrier_mat n n"
  and "0 < n"
  shows "cmod (inner_prod v (A *\<^sub>v v)) = spmax A" 
proof -
  define ve where "ve = find_eigenvector A (spmax_wit A)"
  have "ve \<noteq> 0\<^sub>v n" using assms find_eigen_spmax_neq_0 unfolding ve_def by simp
  have "dim_vec ve = n" using assms(2) assms(3) spmax_wit_eigenvalue  
    unfolding ve_def eigenvector_def
    by (metis find_eigen_spmax_dim index_smult_vec(2) 
        vec_eq_norm_smult_normalized) 
  have "eigenvector A 
    (vec_normalize (find_eigenvector A (spmax_wit A))) (spmax_wit A)"
  proof (rule normalize_keep_eigenvector)
    show "eigenvector A (find_eigenvector A (spmax_wit A)) (spmax_wit A)" 
      using assms
      find_eigenvector spmax_wit_eigenvalue 
      unfolding  eigenvector_def by blast
    show "A \<in> carrier_mat n n" using assms by simp
    show "find_eigenvector A (spmax_wit A) \<in> carrier_vec n" using assms
      find_eigenvector spmax_wit_eigenvalue 
      unfolding  eigenvector_def by blast
  qed
  hence "inner_prod v (A *\<^sub>v v) = inner_prod v ((spmax_wit A)\<cdot>\<^sub>v v)" 
    using assms 
    unfolding  eigenvector_def by force
  also have "... = spmax_wit A * inner_prod v v" by simp
  also have "... = spmax_wit A" using normalized_vec_norm[of ve] assms 
    \<open>dim_vec ve = n\<close> \<open>ve \<noteq> 0\<^sub>v n\<close> carrier_vec_dim_vec mult_cancel_left2 ve_def 
    by blast
  finally have "inner_prod v (A *\<^sub>v v) = spmax_wit A" .
  thus "cmod (inner_prod v (A *\<^sub>v v)) = spmax A"
    using assms(2) assms(3) spmax_wit_eigenvalue by presburger
qed


section \<open>The $\mathcal{L}_2$ operator norm\<close>

subsection \<open>Definition and preliminary results\<close>
definition rvec_norm where
"rvec_norm v = Re (vec_norm v)"

definition L2_op_nrm where
"L2_op_nrm A = 
  Sup {rvec_norm (A *\<^sub>v v) |v. dim_vec v = dim_col A \<and> rvec_norm v = 1}"


lemma  mat_mult_inner_prod_le:
  fixes A::"complex Matrix.mat"
  assumes "0 < dim_col A"
  and "v \<in> carrier_vec (dim_col A)"
shows "cmod (inner_prod (A *\<^sub>v v) (A *\<^sub>v v)) \<le> 
  spmax ((Complex_Matrix.adjoint A) * A) * (inner_prod v v)"
proof -
  define dimr where "dimr = dim_col A"
  define fc::"complex Matrix.mat set" 
    where "fc = carrier_mat (dim_col A) (dim_col A)"
  interpret cpx_sq_mat "dim_col A" "dim_col A" fc 
  proof 
    show "0 < dim_col A" using assms by simp
  qed (auto simp add: fc_def)
  define C where "C = (Complex_Matrix.adjoint A) * A"  
  have "hermitian C" 
    using mult_adjoint_hermitian[of A "dim_row A" "dim_col A"] C_def by simp  
  have "C \<in> fc" using assms adjoint_dim' fc_def C_def 
    by (metis carrier_mat_triv mult_carrier_mat)
  have "cmod (inner_prod (A *\<^sub>v v) (A *\<^sub>v v)) = cmod (inner_prod v (C *\<^sub>v v))" 
    unfolding C_def
    using inner_prod_mult_mat_vec_right \<open>v\<in> carrier_vec (dim_col A)\<close> 
    by (metis carrier_mat_triv) 
  also have "... \<le>  (spmax C) * inner_prod v v" 
    using hermitian_mult_inner_prod_le \<open>C\<in> fc\<close> \<open>hermitian C\<close> 
    \<open>v\<in> carrier_vec (dim_col A)\<close>
    by (metis assms(1) fc_mats_carrier)
  finally show "cmod (inner_prod (A *\<^sub>v v) (A *\<^sub>v v)) \<le> 
    spmax ((Complex_Matrix.adjoint A) * A) * (inner_prod v v)" 
    unfolding C_def by simp
qed

lemma normalized_rvec_norm:
  assumes "v \<noteq> 0\<^sub>v (dim_vec v)"
  shows "rvec_norm (vec_normalize v) = 1" 
  using normalized_vec_norm assms carrier_vec_dim_vec csqrt_eq_1 
  unfolding vec_norm_def rvec_norm_def
  by (metis one_complex.sel(1))

lemma vec_norm_smult:
  shows "vec_norm (c  \<cdot>\<^sub>v v) = (cmod c) * (vec_norm v)"
proof -
  have "Complex_Matrix.inner_prod (c \<cdot>\<^sub>v v) (c \<cdot>\<^sub>v v) = 
    conjugate c * c * Complex_Matrix.inner_prod v v" 
    unfolding vec_norm_def using inner_prod_smult_right 
    by (simp add: conjugate_smult_vec) 
  also have "... = (cmod c)^2 * Complex_Matrix.inner_prod v v" 
    by (metis cross3_simps(11) mult_conj_cmod_square)
  finally have eq: "Complex_Matrix.inner_prod (c \<cdot>\<^sub>v v) (c \<cdot>\<^sub>v v) = 
    (cmod c)^2 * Complex_Matrix.inner_prod v v" .
  have "(cmod c)^2 * Complex_Matrix.inner_prod v v \<in> Reals" 
    using self_inner_prod_real by simp
  hence "csqrt ((cmod c)^2 * Complex_Matrix.inner_prod v v) = 
    sqrt (Re ((cmod c)^2 * Complex_Matrix.inner_prod v v))" 
    using self_cscalar_prod_geq_0 by auto
  also have "... = (sqrt (Re (cmod c)^2) * 
    sqrt (Re (Complex_Matrix.inner_prod v v)))"
    by (simp add: real_sqrt_mult)
  also have "... = cmod c * sqrt (Re (Complex_Matrix.inner_prod v v))" 
    by fastforce
  also have "... = cmod c * csqrt (Complex_Matrix.inner_prod v v)" by auto
  finally have "csqrt ((cmod c)^2 * Complex_Matrix.inner_prod v v) = 
    cmod c * csqrt (Complex_Matrix.inner_prod v v)" .
  hence "csqrt (Complex_Matrix.inner_prod (c \<cdot>\<^sub>v v) (c \<cdot>\<^sub>v v)) = 
    cmod c * csqrt (Complex_Matrix.inner_prod v v)" using eq by simp
  thus ?thesis unfolding vec_norm_def by simp
qed

lemma rvec_norm_smult:
  shows "rvec_norm (c  \<cdot>\<^sub>v v) = (cmod c) * (rvec_norm v)" 
  using vec_norm_smult unfolding rvec_norm_def by simp

lemma mult_mat_zero_vec:
  assumes "A \<in> carrier_mat n m"
and "v = 0\<^sub>v m"
shows "A *\<^sub>v v = 0\<^sub>v n" 
proof (intro eq_vecI)
  show "dim_vec (A *\<^sub>v v) = dim_vec (0\<^sub>v n)" using assms by simp
next
  fix i
  assume "i < dim_vec (0\<^sub>v n)"
  hence "Matrix.vec_index (A *\<^sub>v v) i = Matrix.scalar_prod (Matrix.row A i) v" 
    using assms by simp
  also have "... = 0" using assms by auto
  also have "... = Matrix.vec_index (0\<^sub>v n) i" using \<open>i < dim_vec (0\<^sub>v n)\<close> 
    by auto 
  finally show "Matrix.vec_index (A *\<^sub>v v) i = Matrix.vec_index (0\<^sub>v n) i" .
qed

lemma mat_mult_vec_normalize:
  assumes "dim_col A = dim_vec v"
  shows "A *\<^sub>v v = vec_norm v \<cdot>\<^sub>v (A *\<^sub>v (vec_normalize v))"
proof-
  have "A *\<^sub>v v = A *\<^sub>v (vec_norm v \<cdot>\<^sub>v vec_normalize v)" 
    using vec_eq_norm_smult_normalized by simp
  also have "... = vec_norm v \<cdot>\<^sub>v (A *\<^sub>v (vec_normalize v))" 
    using mult_mat_vec[of A _ _ "vec_normalize v" "vec_norm v"] assms
    by (metis carrier_mat_triv carrier_vec_dim_vec normalized_vec_dim)
  finally show ?thesis .
qed

lemma vec_norm_real:
  shows "vec_norm v \<in> Reals"
proof -
  have "Im (vec_norm v) = 0" using vec_norm_geq_0 less_eq_complex_def by force
  thus ?thesis using complex_is_Real_iff by auto
qed

lemma rvec_norm_geq_0:
  shows "0 \<le> rvec_norm v" unfolding rvec_norm_def
  using vec_norm_geq_0 less_eq_complex_def by auto

lemma rvec_norm_triangle:
  assumes "dim_vec u = dim_vec v"
  shows "rvec_norm (u + v) \<le> rvec_norm u + rvec_norm v"
  using vec_norm_triangle[OF assms] less_eq_complex_def 
  unfolding rvec_norm_def by simp

lemma cmod_vec_norm:
  shows "cmod (vec_norm v) = vec_norm v"
proof -
  have "cmod (vec_norm v) = sqrt ((Re (vec_norm v))^2)" using vec_norm_real
    by (simp add: in_Reals_norm)
  also have "... = Re (vec_norm v)" 
    using vec_norm_real vec_norm_geq_0 cpx_ge_0_real by simp
  also have "... = vec_norm v" using vec_norm_real by simp
  finally show ?thesis .
qed

lemma cmod_rvec_norm:
  shows "cmod (rvec_norm v) = rvec_norm v"
  unfolding rvec_norm_def using cmod_vec_norm
  by (metis Re_complex_of_real) 

lemma inner_prod_rvec_norm_pow2:
  shows "(rvec_norm v)\<^sup>2 = v \<bullet>c v" 
  using rvec_norm_def inner_prod_vec_norm_pow2 vec_norm_eq_cpx_vec_length 
  by auto  

lemma rvec_norm_mat_mult_le:
  assumes "v \<in>carrier_vec (dim_col A)"
  and "0 < dim_col A"
  shows "cmod (inner_prod (A *\<^sub>v v) (A *\<^sub>v v))
       \<le> spmax (Complex_Matrix.adjoint A * A) * (rvec_norm v)\<^sup>2"
proof -
  have "cmod (inner_prod (A *\<^sub>v v) (A *\<^sub>v v)) \<le> 
    spmax (Complex_Matrix.adjoint A * A) * inner_prod v v" 
    using assms mat_mult_inner_prod_le[of A v] by simp
  also have "... = spmax (Complex_Matrix.adjoint A * A) * (rvec_norm v)\<^sup>2" 
    using cmod_rvec_norm inner_prod_rvec_norm_pow2 norm_power by simp
  finally show ?thesis using less_eq_complex_def by simp
qed

lemma square_leq:
  assumes "a\<^sup>2 \<le> b * c\<^sup>2"
  and "0 \<le> c"
shows "a \<le> (sqrt b) * c" 
  by (metis assms real_le_rsqrt real_sqrt_mult real_sqrt_unique)

lemma rvec_set_ne:
  assumes "0 < dim_col A"
  shows "{rvec_norm (A *\<^sub>v v)|v. dim_vec v = dim_col A \<and> rvec_norm v = 1} \<noteq> {}"
proof -
  define vn::"complex Matrix.vec" where "vn = unit_vec (dim_col A) 0"
  have "vn \<noteq> 0\<^sub>v (dim_vec vn)" unfolding vn_def using assms by simp
  hence "rvec_norm (vec_normalize vn) = 1" using normalized_rvec_norm by simp
  moreover have "dim_vec (vec_normalize vn) = dim_col A" unfolding vn_def 
    by simp
  ultimately show ?thesis by auto
qed

lemma unitary_col_vec_norm:
  assumes "U \<in> carrier_mat n n"
  and "unitary U"
  and "i < n"
  shows "vec_norm (Matrix.col U i) = 1" using unitary_col_norm assms
  by (simp add: vec_norm_eq_cpx_vec_length)

lemma unitary_col_rvec_norm:
  assumes "U \<in> carrier_mat n n"
  and "unitary U"
  and "i < n"
  shows "rvec_norm (Matrix.col U i) = 1" using unitary_col_vec_norm[OF assms]
  by (simp add: rvec_norm_def)

lemma Cauchy_Schwarz_complex_rvec_norm:
assumes "dim_vec x = dim_vec y"
shows "cmod (inner_prod x y) \<le> rvec_norm x * rvec_norm y"
proof -
  have x: "x \<in> carrier_vec (dim_vec x)" by simp
  moreover have y: "y \<in> carrier_vec (dim_vec x)" using assms by simp
  ultimately have "(cmod (inner_prod x y))\<^sup>2 = inner_prod x y * inner_prod y x" 
    using complex_norm_square by (metis inner_prod_swap mult_conj_cmod_square)
  also have "... \<le> inner_prod x x * inner_prod y y" 
    using Cauchy_Schwarz_complex_vec x y by blast
  finally have "(cmod (inner_prod x y))\<^sup>2 \<le> inner_prod x x * inner_prod y y" .
  hence "(cmod (inner_prod x y))\<^sup>2 \<le> Re (inner_prod x x) * Re (inner_prod y y)"
    using less_eq_complex_def by simp
  hence "sqrt ((cmod (inner_prod x y))\<^sup>2) \<le> 
    sqrt (Re (inner_prod x x) * Re (inner_prod y y))"
    using real_sqrt_le_iff by blast
  also have "... =  sqrt (Re (inner_prod x x)) * sqrt (Re (inner_prod y y))"
    by (simp add: real_sqrt_mult)
  finally have "sqrt ((cmod (inner_prod x y))\<^sup>2) \<le> 
    sqrt (Re (inner_prod x x)) * sqrt (Re (inner_prod y y))" .
  thus ?thesis using less_eq_complex_def
    by (metis Re_complex_of_real cmod_power2 cmod_rvec_norm 
        inner_prod_rvec_norm_pow2 norm_complex_def)
qed

subsection \<open>The $\mathcal{L}_2$ operator norm is equal to the maximum singular value\<close>

definition max_sgval where
"max_sgval A = sqrt (spmax (Complex_Matrix.adjoint A * A))"

lemma max_sgval_geq_0:
  assumes "A\<in> carrier_mat n n" 
  and "0 < n"
shows "0 \<le> max_sgval A" 
  using spmax_geq_0[of "Complex_Matrix.adjoint A * A" n] 
  unfolding max_sgval_def
  by (meson adjoint_dim' assms(1) assms(2) mult_carrier_mat real_sqrt_ge_zero) 


lemma max_sgval_uminus:
  shows "max_sgval (-A) = max_sgval A" 
proof -
  have "Complex_Matrix.adjoint (-A) = - (Complex_Matrix.adjoint A)" 
    using adjoint_uminus[of A] 
    by simp
  hence "Complex_Matrix.adjoint (-A)*(-A) = -(Complex_Matrix.adjoint A) * (-A)" 
    by simp
  also have "... = - (Complex_Matrix.adjoint A * (-A))" by simp
  also have "... = Complex_Matrix.adjoint A * A" by simp
  finally have "Complex_Matrix.adjoint (-A) * (-A) = 
    Complex_Matrix.adjoint A * A" .
  thus ?thesis unfolding max_sgval_def by simp
qed


lemma rvec_leq_sg_spmax:
  assumes "0 < dim_col A"
  and "v\<in> carrier_vec (dim_col A)"
shows "rvec_norm (A *\<^sub>v v) \<le> (max_sgval A) * rvec_norm v"
proof -
  define M where "M = spmax (Complex_Matrix.adjoint A * A)"
  have "cmod (inner_prod (A *\<^sub>v v) (A *\<^sub>v v))
     \<le>  M * (rvec_norm v)\<^sup>2" using rvec_norm_mat_mult_le assms 
    unfolding M_def  by simp
  hence "(rvec_norm (A *\<^sub>v v))\<^sup>2 \<le>  M * (rvec_norm v)\<^sup>2" 
    using inner_prod_rvec_norm_pow2[of "A *\<^sub>v v"] assms cmod_rvec_norm
    by (metis inner_prod_rvec_norm_pow2 norm_power of_real_hom.hom_power)
  hence "rvec_norm (A *\<^sub>v v) \<le> (sqrt M) * rvec_norm v"
    by (rule square_leq, (auto simp add: rvec_norm_geq_0))
  thus ?thesis unfolding max_sgval_def M_def by simp
qed

lemma max_sgval_smult:
  assumes "A\<in> carrier_mat n n"
  and "0 < n"
  shows "max_sgval (a\<cdot>\<^sub>mA) = cmod a * max_sgval A" 
proof -
  have "Complex_Matrix.adjoint (a\<cdot>\<^sub>mA) * (a\<cdot>\<^sub>mA) = 
    conjugate a\<cdot>\<^sub>m (Complex_Matrix.adjoint A) * (a\<cdot>\<^sub>mA)"
    using adjoint_scale[of a] by simp
  also have "... = conjugate a\<cdot>\<^sub>m (Complex_Matrix.adjoint A * (a\<cdot>\<^sub>mA))" 
    using mult_smult_assoc_mat[of "Complex_Matrix.adjoint A"] adjoint_dim[of A] 
      smult_carrier_mat[of A] assms by (meson mult_smult_assoc_mat)
  also have "... = (conjugate a) \<cdot>\<^sub>m (a \<cdot>\<^sub>m (Complex_Matrix.adjoint A) * A)" 
    using mult_smult_distrib[of "Complex_Matrix.adjoint A"] adjoint_dim[of A] 
      smult_carrier_mat[of A] assms by (metis mult_smult_assoc_mat) 
  also have "... = (conjugate a * a) \<cdot>\<^sub>m (Complex_Matrix.adjoint A) * A"
    by (metis adjoint_dim_col  carrier_mat_triv index_smult_mat(3) 
        mult_smult_assoc_mat smult_smult_times)
  also have "... = (cmod a)\<^sup>2 \<cdot>\<^sub>m(Complex_Matrix.adjoint A * A)"
    by (metis adjoint_dim' assms(1) cross3_simps(11) mult_conj_cmod_square 
        mult_smult_assoc_mat)
  finally have "Complex_Matrix.adjoint (a\<cdot>\<^sub>mA) * (a\<cdot>\<^sub>mA) = 
    (cmod a)\<^sup>2 \<cdot>\<^sub>m(Complex_Matrix.adjoint A * A)" .
  moreover have "spmax ((cmod a)\<^sup>2 \<cdot>\<^sub>m(Complex_Matrix.adjoint A * A)) = 
    (cmod a)\<^sup>2 * spmax ((Complex_Matrix.adjoint A * A))" 
  proof (rule spmax_smult_pos)
    show "hermitian (Complex_Matrix.adjoint A * A)" 
      using assms mult_adjoint_hermitian by auto
    show "0 < dim_col A" using assms by simp
  qed (auto simp add: assms)
  ultimately have "spmax (Complex_Matrix.adjoint (a\<cdot>\<^sub>mA) * (a\<cdot>\<^sub>mA)) = 
    (cmod a)\<^sup>2 * spmax (Complex_Matrix.adjoint A * A)" by simp
  thus ?thesis unfolding max_sgval_def 
    by (metis abs_norm_cancel real_sqrt_abs real_sqrt_mult)
qed

lemma L2_op_nrm_le_max_sgval:
  assumes "0 < dim_col A"
  shows "L2_op_nrm A \<le> max_sgval A" unfolding L2_op_nrm_def
proof (rule Sup_real_le)
  have vg: "\<forall>v\<in>carrier_vec (dim_col A). rvec_norm (A *\<^sub>v v) \<le> 
    (max_sgval A) * rvec_norm v"
    using assms rvec_leq_sg_spmax by simp
  show "\<forall>a\<in>{rvec_norm (A *\<^sub>v v) |v. dim_vec v = dim_col A \<and> rvec_norm v = 1}. 
    0 \<le> a" 
    using rvec_norm_geq_0 by auto
  show "\<forall>a\<in>{rvec_norm (A *\<^sub>v v) |v. dim_vec v = dim_col A \<and> rvec_norm v = 1}. 
    a \<le>max_sgval A" 
    using vg carrier_vec_def by force
  show "{rvec_norm (A *\<^sub>v v) |v. dim_vec v = dim_col A \<and> rvec_norm v = 1} \<noteq> {}"
    using assms rvec_set_ne by simp
qed

lemma max_sgval_eigen:
  assumes "A\<in> carrier_mat n n"
  and "0 < n"
  and "C = Complex_Matrix.adjoint A * A"
  and "v = vec_normalize (find_eigenvector C (spmax_wit C))"
shows "rvec_norm (A *\<^sub>v v) = max_sgval A"
proof -
  have "cmod (inner_prod (A *\<^sub>v v) (A *\<^sub>v v)) = cmod (inner_prod v (C *\<^sub>v v))" 
    using inner_prod_mult_mat_vec_right nrm_spmax_eigenvector_eq
    by (metis adjoint_dim' assms(1) assms(2) assms(3) assms(4) 
        carrier_vecI find_eigen_spmax_dim mult_carrier_mat)
  also have "... = spmax C" using assms nrm_spmax_eigenvector_eq[of C]
    by (metis assms(3) adjoint_dim' mult_carrier_mat 
        nrm_spmax_eigenvector_eq assms(4))
  finally have "cmod (inner_prod (A *\<^sub>v v) (A *\<^sub>v v)) = spmax C" .
  hence "(rvec_norm (A *\<^sub>v v))\<^sup>2 = spmax C" 
    using inner_prod_rvec_norm_pow2[of "A *\<^sub>v v"] assms cmod_rvec_norm
    by (metis inner_prod_rvec_norm_pow2 norm_power of_real_hom.hom_power)
  thus "rvec_norm (A *\<^sub>v v) = max_sgval A" using assms unfolding max_sgval_def
    by (simp add: real_sqrt_unique rvec_norm_geq_0)
qed

lemma rvec_normalize_leq_L2_op_nrm:
  assumes "rvec_norm v = 1"
  and "dim_col A = dim_vec v"
  and "0 < dim_col A"
shows "rvec_norm (A *\<^sub>v v) \<le> L2_op_nrm A" 
proof -
  have vg: "\<forall>v\<in>carrier_vec (dim_col A). rvec_norm (A *\<^sub>v v) \<le> 
    (max_sgval A) * rvec_norm v"
    using assms rvec_leq_sg_spmax by simp
  show ?thesis unfolding L2_op_nrm_def
  proof (rule Sup_ge_real)
    show "rvec_norm (A *\<^sub>v v) \<in> 
      {rvec_norm (A *\<^sub>v v) |v. dim_vec v = dim_col A \<and> rvec_norm v = 1}"
      using assms by auto
    show "\<forall>a\<in>{rvec_norm (A *\<^sub>v v) |v. dim_vec v = dim_col A \<and> rvec_norm v = 1}. 
      a \<le>max_sgval A" 
      using vg carrier_vec_def by force 
    show "\<forall>a\<in>{rvec_norm (A *\<^sub>v v) |v. dim_vec v = dim_col A \<and> rvec_norm v = 1}. 
      0 \<le> a" 
      using rvec_norm_geq_0 by auto
  qed
qed

lemma max_sgval_le_L2_op_nrm:
  assumes "A \<in> carrier_mat n n"
  and "0 < n"
  shows "max_sgval A \<le> L2_op_nrm A" 
proof -
  define C where "C = Complex_Matrix.adjoint A * A"
  define v where "v = vec_normalize (find_eigenvector C (spmax_wit C))"
  have "max_sgval A = rvec_norm (A *\<^sub>v v)" 
    using assms max_sgval_eigen v_def C_def 
    by simp
  also have "... \<in> {rvec_norm (A *\<^sub>v v) |v. dim_vec v = dim_col A \<and> 
    rvec_norm v = 1}"
  proof -
    have "dim_vec v = dim_col A" using assms find_eigen_spmax_dim 
      unfolding v_def
      by (metis C_def adjoint_dim' carrier_matD(2) mult_carrier_mat)
    moreover have "rvec_norm v = 1" 
      using normalized_vec_norm find_eigen_spmax_neq_0 assms
      by (metis C_def adjoint_dim' calculation carrier_matD(2) 
          carrier_vec_dim_vec mult_carrier_mat normalize_zero 
          normalized_rvec_norm v_def)
    ultimately show ?thesis by auto
  qed
  finally have "max_sgval A \<in> 
    {rvec_norm (A *\<^sub>v v) |v. dim_vec v = dim_col A \<and> rvec_norm v = 1}" .
  thus "max_sgval A \<le> L2_op_nrm A" unfolding L2_op_nrm_def
    using assms L2_op_nrm_def rvec_normalize_leq_L2_op_nrm by auto
qed


lemma vec_norm_leq_L2_op_nrm:
  assumes "A\<in> carrier_mat n n"
  and "v\<in> carrier_vec n"
  and "0 < n"
  and "vec_norm v = 1"
shows "vec_norm (A *\<^sub>v v) \<le> L2_op_nrm A" 
proof -
  have "rvec_norm v = 1" using assms
    by (simp add: rvec_norm_def)
  hence "rvec_norm (A *\<^sub>v v) \<le> L2_op_nrm A" unfolding L2_op_nrm_def
    by (metis assms(1) assms(2) assms(3) carrier_dim_vec carrier_matD(2) 
        L2_op_nrm_def rvec_normalize_leq_L2_op_nrm)
  have "vec_norm (A *\<^sub>v v) = rvec_norm (A *\<^sub>v v)"
    by (metis Re_complex_of_real cmod_vec_norm rvec_norm_def)
  also have "... \<le> L2_op_nrm A" using \<open>rvec_norm (A *\<^sub>v v) \<le> L2_op_nrm A\<close> 
    by (simp add: less_eq_complex_def)
  finally show ?thesis .
qed

lemma rvec_norm_leq_L2_op_nrm:
  assumes "A\<in> carrier_mat n n"
  and "v\<in> carrier_vec n"
  and "0 < n"
  and "rvec_norm v = 1"
shows "rvec_norm (A *\<^sub>v v) \<le> L2_op_nrm A" unfolding L2_op_nrm_def
    by (metis assms carrier_dim_vec carrier_matD(2) 
        L2_op_nrm_def rvec_normalize_leq_L2_op_nrm)


lemma cmod_trace_rank_le_L2_op_nrm:
  assumes "A\<in> carrier_mat n n"
  and "v\<in> carrier_vec n"
  and "0 < n"
  and "rvec_norm v = 1"
  shows "cmod (Complex_Matrix.trace (A * rank_1_proj v)) \<le> L2_op_nrm A"
proof -
  have "cmod (Complex_Matrix.trace (A * rank_1_proj v)) = 
    cmod (Complex_Matrix.inner_prod v (A *\<^sub>v v))" 
    using rank_1_proj_trace_inner[of A] assms by simp
  also have "... \<le> rvec_norm v * rvec_norm (A *\<^sub>v v)" 
    using Cauchy_Schwarz_complex_rvec_norm assms(1) assms(2) by auto
  also have "... = rvec_norm (A *\<^sub>v v)" using assms by simp
  also have "... \<le> L2_op_nrm A" using rvec_norm_leq_L2_op_nrm assms by simp
  finally show ?thesis .
qed



lemma expect_val_L2_op_nrm:
  fixes A::"complex Matrix.mat"
  assumes "A\<in> carrier_mat n n"
  and "R\<in> carrier_mat n n"
  and "0 < n"
  and "density_operator R"
  shows "cmod (Complex_Matrix.trace (A * R)) \<le> L2_op_nrm A"
proof -
  have "hermitian R" using assms unfolding density_operator_def
    by (simp add: positive_is_hermitian) 
  from this obtain B U where rd: "real_diag_decomp R B U" 
    using hermitian_real_diag_decomp[of R] assms by auto
  hence "unitary U"
    using real_diag_decompD(1) unitary_diagD(3) by blast 
  have "U\<in> carrier_mat n n" using rd unitary_diag_carrier(2) assms
    by (metis real_diag_decompD(1))
  have "cmod (Complex_Matrix.trace (A * R)) \<le> 
    Re (Complex_Matrix.trace R) * L2_op_nrm A"
  proof (rule positive_decomp_cmod_le[of R n])
    show "Complex_Matrix.positive R" using assms 
      unfolding density_operator_def by simp
    show "unitary_diag R B U" using rd by simp
    show "\<And>i. i < n \<Longrightarrow> 
      cmod (Complex_Matrix.trace (A * rank_1_proj (Matrix.col U i))) \<le> 
      L2_op_nrm A"
    proof-
      fix i
      assume "i < n"
      show "cmod (Complex_Matrix.trace (A * rank_1_proj (Matrix.col U i))) \<le> 
        L2_op_nrm A"
      proof (rule cmod_trace_rank_le_L2_op_nrm[of A n])
        show "Matrix.col U i \<in> carrier_vec n"
          by (metis \<open>unitary_diag R B U\<close> assms(2) carrier_matD(1) 
              col_dim unitary_diag_carrier(2))
        show "rvec_norm (Matrix.col U i) = 1" 
          using unitary_col_rvec_norm \<open>unitary U\<close> \<open>i < n\<close> \<open>U\<in> carrier_mat n n\<close> 
          by simp
      qed (auto simp add: assms)
    qed
  qed (auto simp add: assms)
  also have "... = L2_op_nrm A" using assms 
    unfolding density_operator_def by simp
  finally show ?thesis .
qed

subsection \<open>Consequences for the $\mathcal{L}_2$ operator norm\<close>

lemma L2_op_nrm_geq_0:
assumes "A \<in> carrier_mat n n"
  and "0 < n"
shows "0 \<le> L2_op_nrm A" 
  using assms max_sgval_le_L2_op_nrm[of A n] max_sgval_geq_0[of A n] 
  by simp

lemma L2_op_nrm_max_sgval_eq:
  assumes "A \<in> carrier_mat n n"
  and "0 < n"
  shows "L2_op_nrm A = max_sgval A"
proof -
  have "L2_op_nrm A \<le> max_sgval A" using assms L2_op_nrm_le_max_sgval by simp
  moreover have "max_sgval A \<le> L2_op_nrm A" 
    using assms max_sgval_le_L2_op_nrm by simp
  ultimately show ?thesis by simp
qed

lemma rvec_leq_L2_op_nrm:
  assumes "A \<in> carrier_mat n n"
  and "0 < n"
  and "v\<in> carrier_vec n"
shows "rvec_norm (A *\<^sub>v v) \<le> (L2_op_nrm A) * rvec_norm v"
  using assms L2_op_nrm_max_sgval_eq rvec_leq_sg_spmax by simp

lemma L2_op_nrm_mult_le:
  assumes "A \<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "0 < n"
shows "L2_op_nrm (A*B) \<le> L2_op_nrm A * L2_op_nrm B" 
proof -
  have "Sup {rvec_norm (A * B *\<^sub>v v) |v. dim_vec v = n \<and> rvec_norm v = 1} \<le> 
    L2_op_nrm A * L2_op_nrm B" 
  proof (rule Sup_real_le)
    show "{rvec_norm (A * B *\<^sub>v v) |v. dim_vec v = n \<and> rvec_norm v = 1} \<noteq> {}" 
      using rvec_set_ne assms by auto
    show "\<forall>a\<in>{rvec_norm (A * B *\<^sub>v v) |v. dim_vec v = n \<and> rvec_norm v = 1}. 
      0  \<le> a" 
      using rvec_norm_geq_0 by auto
    show "\<forall>a\<in>{rvec_norm (A * B *\<^sub>v v) |v. dim_vec v = n \<and> rvec_norm v = 1}. 
      a \<le> L2_op_nrm A * L2_op_nrm B" 
    proof
      fix x
      assume "x \<in> {rvec_norm (A * B *\<^sub>v v)|v. dim_vec v = n \<and> rvec_norm v = 1}"
      hence "\<exists>v.(dim_vec v = n \<and>rvec_norm v = 1 \<and> x = rvec_norm (A * B *\<^sub>v v))" 
        by auto
      from this obtain v where "dim_vec v = n" and "rvec_norm v = 1" 
        and "x = rvec_norm (A * B *\<^sub>v v)" by auto note vprop = this
      have "A * B *\<^sub>v v = A *\<^sub>v (B *\<^sub>v v)" using assms vprop by auto
      hence "x = rvec_norm (A *\<^sub>v (B *\<^sub>v v))" using vprop by simp
      also have "... \<le> L2_op_nrm A * rvec_norm (B *\<^sub>v v)" 
        using assms rvec_leq_L2_op_nrm[of A n "B *\<^sub>v v"] carrier_vecI 
          mult_mat_vec_carrier vprop(1) 
        by blast
      also have "... \<le> L2_op_nrm A * (L2_op_nrm B)" 
        using vprop rvec_normalize_leq_L2_op_nrm[of v] assms
        by (metis carrier_matD(2) more_arith_simps(6) mult_mono' mult_zero_right 
            rvec_norm_geq_0 verit_comp_simplify1(2))
      finally show "x \<le> L2_op_nrm A * L2_op_nrm B" .
    qed
  qed
  thus ?thesis using assms L2_op_nrm_def by simp
qed

lemma L2_op_nrm_smult:
  assumes "A\<in> carrier_mat n n"
  and "0 < n"
shows "L2_op_nrm (c \<cdot>\<^sub>m A) = cmod c * L2_op_nrm A"
  by (metis L2_op_nrm_max_sgval_eq assms(1) assms(2) max_sgval_smult 
      smult_carrier_mat)

lemma L2_op_nrm_uminus:
  assumes "A\<in> carrier_mat n n"
  and "0 < n"
shows "L2_op_nrm (-A) = L2_op_nrm A" 
  using L2_op_nrm_max_sgval_eq max_sgval_uminus[of A] assms by simp

lemma L2_op_nrm_triangle:
  assumes "A \<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "0 < n"
shows "L2_op_nrm (A+B) \<le> L2_op_nrm A + L2_op_nrm B"
proof -
  define C where "C = Complex_Matrix.adjoint (A+B) * (A+B)"
  have "C \<in> carrier_mat n n" using C_def 
    by (metis add_carrier_mat adjoint_dim' assms(2) mult_carrier_mat) 
  define v where "v = vec_normalize (find_eigenvector C (spmax_wit C))"
  have "v\<in> carrier_vec n" using v_def
    by (metis \<open>C \<in> carrier_mat n n\<close> assms(3) carrier_dim_vec 
        find_eigen_spmax_dim) 
  have "rvec_norm (A *\<^sub>v v) \<le> L2_op_nrm A"
  proof (rule rvec_normalize_leq_L2_op_nrm)
    show "0 < dim_col A" using assms by simp
    show "dim_col A = dim_vec v" using \<open>v\<in> carrier_vec n\<close> assms by simp
    show "rvec_norm v = 1" using v_def
      by (metis \<open>C \<in> carrier_mat n n\<close> \<open>v \<in> carrier_vec n\<close> assms(3) carrier_vecD 
          find_eigen_spmax_neq_0 normalize_zero normalized_rvec_norm 
          zero_carrier_vec)
  qed
   have "rvec_norm (B *\<^sub>v v) \<le> L2_op_nrm B"
  proof (rule rvec_normalize_leq_L2_op_nrm)
    show "0 < dim_col B" using assms by simp
    show "dim_col B = dim_vec v" using \<open>v\<in> carrier_vec n\<close> assms by simp
    show "rvec_norm v = 1" using v_def
      by (metis \<open>C \<in> carrier_mat n n\<close> \<open>v \<in> carrier_vec n\<close> assms(3) carrier_vecD 
          find_eigen_spmax_neq_0 normalize_zero normalized_rvec_norm 
          zero_carrier_vec)
  qed
  have "(A+B)*\<^sub>v v = A *\<^sub>v v + B *\<^sub>v v" 
  proof (rule add_mult_distrib_mat_vec)
    show "A \<in> carrier_mat n n" "B\<in> carrier_mat n n" using assms by auto
    show "v\<in> carrier_vec n" using \<open>v\<in> carrier_vec n\<close> .
  qed
  hence "L2_op_nrm (A+B) = rvec_norm (A *\<^sub>v v + B *\<^sub>v v)" 
    using L2_op_nrm_max_sgval_eq[of "A+B" n] max_sgval_eigen[of "A+B" n] 
      C_def v_def by (simp add: assms(2) assms(3))
  also have "... \<le> rvec_norm (A *\<^sub>v v) + rvec_norm (B *\<^sub>v v)" 
    using rvec_norm_triangle assms \<open>v\<in> carrier_vec n\<close> by simp
  also have "... \<le> L2_op_nrm A + L2_op_nrm B" 
    using \<open>rvec_norm (B *\<^sub>v v) \<le> L2_op_nrm B\<close> \<open>rvec_norm (A *\<^sub>v v) \<le> L2_op_nrm A\<close> 
    by simp
  finally show ?thesis .
qed

lemma L2_op_nrm_triangle':
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "0 < n"
shows "L2_op_nrm (A-B) \<le> L2_op_nrm A + L2_op_nrm B"
proof -
  have "L2_op_nrm (A-B) = L2_op_nrm (A + (-B))" 
    using assms add_uminus_minus_mat[of A] by simp
  also have "... \<le> L2_op_nrm A + L2_op_nrm (-B)" 
    using L2_op_nrm_triangle assms by simp
  also have "... = L2_op_nrm A + L2_op_nrm B" 
    using L2_op_nrm_uminus assms by simp
  finally show ?thesis .
qed

lemma hermitian_max_sgval_eq:
fixes A::"complex Matrix.mat"
assumes "hermitian A"
and "0 < dim_row A"
shows "max_sgval A = spmax A"
proof -
  define n where "n = dim_row A"
  have "A \<in> carrier_mat n n" 
    using assms n_def hermitian_square by (simp add: hermitian_square)
  have "max_sgval A = sqrt (spmax (A * A))" 
    using assms unfolding max_sgval_def hermitian_def by simp
  also have "... = spmax A" 
    using assms hermitian_square_spmax spmax_geq_0 \<open>A \<in> carrier_mat n n\<close> 
    by simp
  finally show ?thesis .
qed

lemma hermitian_L2_op_nrm_spmax_eq:
fixes A::"complex Matrix.mat"
assumes "hermitian A"
and "0 < dim_row A"
shows "L2_op_nrm A = spmax A" 
proof -
  define n where "n = dim_row A"
  have "A \<in> carrier_mat n n" 
    using n_def by (metis assms(1) hermitian_square) 
  thus ?thesis 
    using assms hermitian_max_sgval_eq[of A] L2_op_nrm_max_sgval_eq[of A n] n_def
    by metis
qed

lemma hermitian_L2_op_nrm_sqrt:
fixes A::"complex Matrix.mat"
assumes "hermitian A"
and "0 < dim_row A"
shows "L2_op_nrm A = sqrt (L2_op_nrm (A*A))"
  by (metis assms hermitian_L2_op_nrm_spmax_eq hermitian_commute hermitian_def 
      hermitian_max_sgval_eq index_mult_mat(2) max_sgval_def) 

lemma idty_L2_op_nrm:
  assumes "0 < n"
  shows "L2_op_nrm (1\<^sub>m n) = 1" 
  using assms idty_spmax[of n] hermitian_L2_op_nrm_spmax_eq
  by (simp add: hermitian_one)

lemma commutator_L2_op_nrm_le:
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "0 < n"
  shows "L2_op_nrm (commutator A B) \<le> 2 * L2_op_nrm A * L2_op_nrm B"
proof -
  have "L2_op_nrm (commutator A B) \<le> L2_op_nrm (A*B) + L2_op_nrm (B * A)" 
    unfolding commutator_def 
    using L2_op_nrm_triangle'[of "A*B" n] assms by simp
  also have "... \<le> L2_op_nrm A * L2_op_nrm B + L2_op_nrm (B*A)" 
    using L2_op_nrm_mult_le assms by simp
  also have "... \<le> L2_op_nrm A * L2_op_nrm B + L2_op_nrm B * L2_op_nrm A" 
    using L2_op_nrm_mult_le[of B n A] assms 
    by linarith
  also have "... = L2_op_nrm A * L2_op_nrm B + L2_op_nrm A * L2_op_nrm B" by simp
  also have "... = 2 * L2_op_nrm A * L2_op_nrm B" by simp
  finally show ?thesis .
qed

lemma herm_sq_id_L2_op_nrm:
  assumes "0 < n"
  and "A\<in> carrier_mat n n"
  and "hermitian A"
  and "A*A = 1\<^sub>m n"
shows "L2_op_nrm A = 1"
proof -
  have "spmax A = 1" using assms hermitian_square_idty_spmax by simp
  thus ?thesis using hermitian_L2_op_nrm_spmax_eq assms by simp
qed

lemma comm_L2_op_nrm_le:
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "0 < n"
  and "A*A = 1\<^sub>m n"
  and "B*B = 1\<^sub>m n"
  and "hermitian A"
  and "hermitian B"
shows "L2_op_nrm (commutator A B) \<le> 2"
proof -
  have "L2_op_nrm (commutator A B) \<le> 2 * L2_op_nrm A * L2_op_nrm B" 
    using assms commutator_L2_op_nrm_le by simp
  also have "... = 2 * L2_op_nrm A" 
    using herm_sq_id_L2_op_nrm assms by simp
  also have "... = 2" 
    using herm_sq_id_L2_op_nrm assms by simp
  finally show ?thesis .
qed

lemma idty_smult_nat_L2_op_nrm:
  assumes "0 < n"
  shows "L2_op_nrm ((m::nat) \<cdot>\<^sub>m (1\<^sub>m n)) = m"
proof -
  have "L2_op_nrm ((m::nat) \<cdot>\<^sub>m (1\<^sub>m n)) = spmax ((m::nat) \<cdot>\<^sub>m (1\<^sub>m n))"
    using hermitian_L2_op_nrm_spmax_eq[of "m \<cdot>\<^sub>m 1\<^sub>m n"] hermitian_one 
      assms hermitian_smult
    by (metis index_one_mat(2) index_smult_mat(2) of_real_of_nat_eq 
        one_carrier_mat)
  also have "... = m * L2_op_nrm (1\<^sub>m n)" 
    using spmax_smult_pos [of "1\<^sub>m n" n "m"] assms hermitian_one  
    hermitian_L2_op_nrm_spmax_eq[of "1\<^sub>m n"] 
    by (simp add: \<open>\<And>n. hermitian (1\<^sub>m n)\<close>)
  also have "... = m" using idty_L2_op_nrm[of n] assms by simp
  finally show ?thesis .
qed
end