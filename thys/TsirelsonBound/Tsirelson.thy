(*
Author: 
  Mnacho Echenim, Université Grenoble Alpes
*)

theory Tsirelson 
  imports  
    Projective_Measurements.CHSH_Inequality
    Matrix_L2_Operator_Norm Density_Matrix_Basics

begin
text \<open>This part contains a formalization of the CHSH operator and the CHSH quantum
expectation, along with Tsirelson's proof that this quantum expectation cannot be greater
than $2\cdot \sqrt{2}$. The development of this proof permits to extract the additional
result that when one of the parties involved in the CHSH experiment makes measurements on 
commuting observables, the quantum expectation cannot be greater than 2. This is the same
upper-bound as in the case where a local hidden variable hypothesis is made.\<close>

section \<open>CHSH inequalities\<close>
text \<open>The CHSH operator is used to represent the experiment in which two parties each perform
measurements using two observables, respectively $A_1,A_2$ and $B_1,B_2$. Given the resource $R$,
in general a density matrix representing an entangled state, the CHSH expectation represents
the quantum expectation of performing simultaneous measurements on $R$. The CHSH setting
also assumes that along with being Hermitian matrics, all the squared observables are equal
to the identity and commute with the observables of the other party.\<close>

subsection \<open>Some intermediate results for particular observables\<close>

lemma chsh_complex:
  fixes A0::complex
  assumes "A0 \<in> Reals"
  and "B0 \<in> Reals"
  and "A1 \<in> Reals"
  and "B1 \<in> Reals"
  and "\<bar>A0 * B1\<bar> \<le> 1"
  and "\<bar>A0 * B0\<bar> \<le> 1"
  and "\<bar>A1 * B0\<bar> \<le> 1"
  and "\<bar>A1 * B1\<bar> \<le> 1"
shows "\<bar>A0 * B1 - A0 * B0 + A1 * B0 + A1*B1\<bar> \<le> 2"
proof - 
  have "\<bar>A0 * B1 - A0 * B0 + A1 * B0 + A1*B1\<bar> = 
    \<bar>Re A0 * (Re B1) - Re A0 * (Re B0) + Re A1 * (Re B0) + Re A1 * (Re B1)\<bar>"
    using assms by (simp add: cpx_real_abs_eq)
  moreover have "\<bar>Re A0 * (Re B1) - Re A0 * (Re B0) + 
    Re A1 * (Re B0) + Re A1 * (Re B1)\<bar> \<le> 2"
  proof (rule chsh_real)
    show "\<bar>Re A0 * Re B1\<bar> \<le> 1" using assms real_cpx_abs_leq by simp
    show "\<bar>Re A1 * Re B1\<bar> \<le> 1" using assms real_cpx_abs_leq by simp
    show "\<bar>Re A0 * Re B0\<bar> \<le> 1" using assms real_cpx_abs_leq by simp
    show "\<bar>Re A1 * Re B0\<bar> \<le> 1" using assms real_cpx_abs_leq by simp
  qed
  ultimately show ?thesis
    by (simp add: less_eq_complex_def)
qed


lemma (in bin_cpx) Z_XpZ_rho_trace:
  shows "Complex_Matrix.trace (Z_I * I_XpZ * rho_psim) = 1/sqrt 2"
proof -
  have "Complex_Matrix.trace (Z_I * I_XpZ * rho_psim) = 
    Complex_Matrix.trace (Z_XpZ * rho_psim)" 
    by (simp add: Z_I_XpZ_eq)
  also have "... = Complex_Matrix.trace (rho_psim * Z_XpZ)"
  proof (rule trace_comm)
    show "Z_XpZ \<in> carrier_mat 4 4" using Z_XpZ_carrier .
    show "rho_psim \<in> carrier_mat 4 4" using rho_psim_carrier .
  qed
  also have "... = 1/sqrt 2" by simp
  finally show ?thesis .
qed

lemma (in bin_cpx) X_XpZ_rho_trace:
  shows "Complex_Matrix.trace (X_I * I_XpZ * rho_psim) = 1/sqrt 2"
proof -
  have "Complex_Matrix.trace (X_I * I_XpZ * rho_psim) = 
    Complex_Matrix.trace (X_XpZ * rho_psim)" 
    by (simp add: X_I_XpZ_eq)
  also have "... = Complex_Matrix.trace (rho_psim * X_XpZ)"
  proof (rule trace_comm)
    show "X_XpZ \<in> carrier_mat 4 4" using X_XpZ_carrier .
    show "rho_psim \<in> carrier_mat 4 4" using rho_psim_carrier .
  qed
  also have "... = 1/sqrt 2" by simp
  finally show ?thesis .
qed

lemma (in bin_cpx) X_ZmX_rho_trace:
  shows "Complex_Matrix.trace (X_I * I_ZmX * rho_psim) = 1/sqrt 2"
proof -
  have "Complex_Matrix.trace (X_I * I_ZmX * rho_psim) = 
    Complex_Matrix.trace (X_ZmX * rho_psim)" 
    by (simp add: X_I_ZmX_eq)
  also have "... = Complex_Matrix.trace (rho_psim * X_ZmX)"
  proof (rule trace_comm)
    show "X_ZmX \<in> carrier_mat 4 4" using X_ZmX_carrier .
    show "rho_psim \<in> carrier_mat 4 4" using rho_psim_carrier .
  qed
  also have "... = 1/sqrt 2" by simp
  finally show ?thesis .
qed

lemma (in bin_cpx) Z_ZmX_rho_trace:
  shows "Complex_Matrix.trace (Z_I * I_ZmX * rho_psim) = -1/sqrt 2"
proof -
  have "Complex_Matrix.trace (Z_I * I_ZmX * rho_psim) = 
    Complex_Matrix.trace (Z_ZmX * rho_psim)" 
    by (simp add: Z_I_ZmX_eq)
  also have "... = Complex_Matrix.trace (rho_psim * Z_ZmX)"
  proof (rule trace_comm)
    show "Z_ZmX \<in> carrier_mat 4 4" using Z_ZmX_carrier .
    show "rho_psim \<in> carrier_mat 4 4" using rho_psim_carrier .
  qed
  also have "... = -1/sqrt 2" by simp
  finally show ?thesis .
qed

subsection \<open>The CHSH operator and expectation\<close>

definition CHSH_op :: "'a::conjugatable_field Matrix.mat \<Rightarrow> 'a Matrix.mat \<Rightarrow> 
  'a Matrix.mat \<Rightarrow> 'a Matrix.mat \<Rightarrow> 'a Matrix.mat" 
  where
"CHSH_op A0 A1 B0 B1 = A0 * B1 - A0 * B0 + A1 * B0 + A1 * B1"

definition CHSH_expect :: "'a::conjugatable_field Matrix.mat \<Rightarrow> 'a Matrix.mat \<Rightarrow> 
  'a Matrix.mat \<Rightarrow> 'a Matrix.mat \<Rightarrow> 'a Matrix.mat \<Rightarrow> 'a"
  where
"CHSH_expect A0 A1 B0 B1 R = Complex_Matrix.trace ((CHSH_op A0 A1 B0 B1) * R)"

definition CHSH_cond :: "nat \<Rightarrow> 'a::conjugatable_field Matrix.mat \<Rightarrow> 
  'a::conjugatable_field Matrix.mat \<Rightarrow> 
  'a::conjugatable_field Matrix.mat \<Rightarrow> 'a::conjugatable_field Matrix.mat \<Rightarrow> bool"
  where
"CHSH_cond n A0 A1 B0 B1 =
  (A0 \<in> carrier_mat n n \<and> 
  A0 * A0 = 1\<^sub>m n \<and> 
  A1 \<in> carrier_mat n n \<and>
  A1 * A1 = 1\<^sub>m n \<and>
  B0 \<in> carrier_mat n n \<and>
  B0 * B0 = 1\<^sub>m n \<and>
  B1 \<in> carrier_mat n n \<and>
  B1 * B1 = 1\<^sub>m n \<and>
  A0 * B1 = B1 * A0 \<and>
  A0 * B0 = B0 * A0 \<and>
  A1 * B0 = B0 * A1 \<and>
  A1 * B1 = B1 * A1)"

definition CHSH_cond_hermit where
"CHSH_cond_hermit n A0 A1 B0 B1 \<longleftrightarrow> CHSH_cond n A0 A1 B0 B1 \<and> hermitian A0 \<and> 
  hermitian A1 \<and> hermitian B0 \<and> hermitian B1"

lemma CHSH_op_dim:
  assumes "A0 \<in> carrier_mat n m"
  and "A1 \<in> carrier_mat n m"
  and "B0 \<in> carrier_mat m p"
  and "B1 \<in> carrier_mat m p"
shows "CHSH_op A0 A1 B0 B1 \<in> carrier_mat n p" unfolding CHSH_op_def 
  using assms by simp

lemma CHSH_op_hermitian:
  assumes "hermitian A0"
  and "hermitian B0"
  and "hermitian A1"
  and "hermitian B1"
  and "A0 * B0 = B0 * A0"
  and "A1 * B0 = B0 * A1"
  and "A0 * B1 = B1 * A0"
  and "A1 * B1 = B1 * A1"
shows "hermitian (CHSH_op A0 A1 B0 B1)" 
  using assms hermitian_add hermitian_def hermitian_minus hermitian_square 
    index_add_mat(2) index_minus_mat(2) index_mult_mat(2) 
  unfolding CHSH_op_def
  by (smt (z3) Linear_Algebra_Complements.hermitian_square adjoint_mult)

lemma CHSH_cond_hermit_expect_eq:
  assumes "CHSH_cond_hermit n A0 A1 B0 B1"
  and "R\<in> carrier_mat n n"
  and "0 < n"
  shows "CHSH_expect A0 A1 B0 B1 R = 
    cpx_sq_mat.obs_expect_value n n  R (CHSH_op A0 A1 B0 B1)"
  unfolding CHSH_expect_def 
proof (rule obs_expect_value[symmetric])
  show "hermitian (CHSH_op A0 A1 B0 B1)" using CHSH_op_hermitian assms 
    unfolding CHSH_cond_hermit_def CHSH_cond_def by metis
  show "CHSH_op A0 A1 B0 B1 \<in> carrier_mat n n" 
    using assms unfolding CHSH_cond_hermit_def CHSH_cond_def
    by (meson CHSH_op_dim) 
qed (auto simp add: assms)

lemma CHSH_op_expand_right:
  fixes A0::"'a::conjugatable_field Matrix.mat"
  assumes "A0 \<in> carrier_mat n m"
  and "A1 \<in> carrier_mat n m"
  and "B0 \<in> carrier_mat m p"
  and "B1 \<in> carrier_mat m p"
  and "R \<in> carrier_mat p p'"
shows "(CHSH_op A0 A1 B0 B1) * R = 
  A0 * B1 * R - A0 * B0 * R + A1 * B0 * R + A1 * B1 * R"  
proof -
  have "(CHSH_op A0 A1 B0 B1) * R = 
    (A0 * B1  - A0 * B0 + A1 * B0) * R + A1 * B1 * R" unfolding CHSH_op_def
    by (meson add_carrier_mat add_mult_distrib_mat assms(2) assms(3) 
        assms(4) assms(5) mult_carrier_mat)
  also have "... = (A0 * B1  - A0 * B0) * R + A1 * B0 * R + A1 * B1 * R"
    by (metis add_mult_distrib_mat assms(1) assms(2) assms(3) assms(5) 
        minus_carrier_mat mult_carrier_mat)
  also have "... = A0 * B1 * R - A0 * B0 * R + A1 * B0 * R + A1 * B1 * R"
    by (metis assms(1) assms(3) assms(4) assms(5) minus_mult_distrib_mat 
        mult_carrier_mat)
  finally show ?thesis .
qed

lemma CHSH_op_expand_left:
  fixes A0::"'a::conjugatable_field Matrix.mat"
  assumes "A0 \<in> carrier_mat n m"
  and "A1 \<in> carrier_mat n m"
  and "B0 \<in> carrier_mat m p"
  and "B1 \<in> carrier_mat m p"
  and "R \<in> carrier_mat p n"
shows "R * (CHSH_op A0 A1 B0 B1) = 
  R * (A0 * B1) - R * (A0 * B0) + R * (A1 * B0) + R * (A1 * B1)"  
proof -
  have "R * (CHSH_op A0 A1 B0 B1) = 
    R * (A0 * B1  - A0 * B0 + A1 * B0) + R * (A1 * B1)" unfolding CHSH_op_def
    using mult_add_distrib_mat[of R p n _ p "A1 * B1"] assms by simp
  also have "... = R * (A0 * B1  - A0 * B0) + R * (A1 * B0) + R * (A1 * B1)"
    using mult_add_distrib_mat assms 
    by (metis minus_carrier_mat mult_carrier_mat)
  also have "... = R * (A0 * B1) - R * (A0 * B0) + R * (A1 * B0) + 
    R * (A1 * B1)"
    using mult_minus_distrib_mat[of R p n "A0 * B1" p] assms by simp
  finally show ?thesis .
qed

lemma CHSH_expect_expand:
  assumes "A0 \<in> carrier_mat n m"
  and "A1 \<in> carrier_mat n m"
  and "B0 \<in> carrier_mat m p"
  and "B1 \<in> carrier_mat m p"
  and "R \<in> carrier_mat p n"
  shows "CHSH_expect A0 A1 B0 B1 R = 
    Complex_Matrix.trace (A0 * B1 * R) -
    Complex_Matrix.trace (A0 * B0 * R) +
    Complex_Matrix.trace (A1 * B0 * R) +
    Complex_Matrix.trace (A1 * B1 * R)" 
proof -
  have "CHSH_expect A0 A1 B0 B1 R = 
    Complex_Matrix.trace (A0 * B1 * R - A0 * B0 * R + A1 * B0 * R + 
      A1 * B1 * R)" 
    unfolding CHSH_expect_def using CHSH_op_expand_right[of A0] assms by simp
  also have "... = Complex_Matrix.trace (A0 * B1 * R) -
    Complex_Matrix.trace (A0 * B0 * R) +
    Complex_Matrix.trace (A1 * B0 * R) +
    Complex_Matrix.trace (A1 * B1 * R)"
    by (meson assms mult_carrier_mat trace_ch_expand) 
  finally show ?thesis .
qed

lemma CHSH_condD:
  assumes "CHSH_cond n A0 A1 B0 B1"
  shows "A0 \<in> carrier_mat n n" 
  "A0 * A0 = 1\<^sub>m n" 
  "A1 \<in> carrier_mat n n"
  "A1 * A1 = 1\<^sub>m n"
  "B0 \<in> carrier_mat n n"
  "B0 * B0 = 1\<^sub>m n"
  "B1 \<in> carrier_mat n n"
  "B1 * B1 = 1\<^sub>m n"
  "A0 * B1 = B1 * A0"
  "A0 * B0 = B0 * A0"
  "A1 * B0 = B0 * A1"
  "A1 * B1 = B1 * A1" using assms unfolding CHSH_cond_def by auto

lemma CHSH_cond_simps[simp]:
  assumes "CHSH_cond n A0 A1 B0 B1"
  shows "A1 * B1 * (A0 * B1) = A1*A0"
    "A1 * B1 * (A1 * B0) = B1 * B0"  
    "A1 * B1 * (A1 * B1) = 1\<^sub>m n"
    "A1 * B1 * (A0 * B0) = A1 * A0 * (B1 * B0)"
    "A1 * B0 * (A0 * B1) = A1 * A0 * (B0 * B1)"
    "A1 * B0 * (A0 * B0) = A1 * A0"
    "A1 * B0 * (A1 * B0) = 1\<^sub>m n"
    "A1 * B0 * (A1 * B1) = B0 * B1"
    "A0 * B0 * (A0 * B1) = B0 * B1"
    "A0 * B0 * (A0 * B0) = 1\<^sub>m n"
    "A0 * B0 * (A1 * B0) = A0 * A1"
    "A0 * B0 * (A1 * B1) = A0 * A1 * (B0 * B1)"
    "A0 * B1 * (A0 * B1) = 1\<^sub>m n"
    "A0 * B1 * (A0 * B0) = B1 * B0"
    "A0 * B1 * (A1 * B0) = A0 * A1 * (B1 * B0)"
    "A0 * B1 * (A1 * B1) = A0 * A1"
proof -
  show "A1 * B1 * (A0 * B1) = A1*A0" using assms unfolding CHSH_cond_def
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
  show  "A1 * B1 * (A1 * B0) = B1 * B0" using assms unfolding CHSH_cond_def 
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
  show  "A1 * B1 * (A1 * B1) = 1\<^sub>m n"  using assms unfolding CHSH_cond_def 
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
  show  "A1 * B1 * (A0 * B0) = A1 * A0 * (B1 * B0)"  
    using assms unfolding CHSH_cond_def 
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
  show  "A1 * B0 * (A0 * B1) = A1 * A0 * (B0 * B1)"  
    using assms unfolding CHSH_cond_def 
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
  show  "A1 * B0 * (A0 * B0) = A1 * A0"  using assms unfolding CHSH_cond_def 
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
  show  "A1 * B0 * (A1 * B0) = 1\<^sub>m n"  using assms unfolding CHSH_cond_def 
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
  show  "A1 * B0 * (A1 * B1) = B0 * B1"  using assms unfolding CHSH_cond_def 
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
  show  "A0 * B0 * (A0 * B1) = B0 * B1"  using assms unfolding CHSH_cond_def 
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
  show  "A0 * B0 * (A0 * B0) = 1\<^sub>m n"  using assms unfolding CHSH_cond_def 
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
  show  "A0 * B0 * (A1 * B0) = A0 * A1"  using assms unfolding CHSH_cond_def  
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
  show  "A0 * B0 * (A1 * B1) = A0 * A1 * (B0 * B1)" 
    using assms unfolding CHSH_cond_def  
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
  show  "A0 * B1 * (A0 * B1) = 1\<^sub>m n" using assms unfolding CHSH_cond_def  
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
  show  "A0 * B1 * (A0 * B0) = B1 * B0" using assms unfolding CHSH_cond_def  
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
  show  "A0 * B1 * (A1 * B0) = A0 * A1 * (B1 * B0)" 
    using assms unfolding CHSH_cond_def  
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
  show  "A0 * B1 * (A1 * B1) = A0 * A1" using assms unfolding CHSH_cond_def
    by (smt (verit) assoc_mult_mat mult_carrier_mat right_mult_one_mat)
qed

lemma CHSH_op_square:
  assumes "CHSH_cond n A0 A1 B0 B1"
shows "(CHSH_op A0 A1 B0 B1) * (CHSH_op A0 A1 B0 B1) = 
  (4::nat) \<cdot>\<^sub>m (1\<^sub>m n) - (commutator A0 A1) * (commutator B0 B1)"
proof -
  have "(CHSH_op A0 A1 B0 B1) * (CHSH_op A0 A1 B0 B1) = 
    A0 * B1 * (CHSH_op A0 A1 B0 B1) - A0 * B0 * (CHSH_op A0 A1 B0 B1) + 
    A1 * B0 * (CHSH_op A0 A1 B0 B1) + A1 * B1 * (CHSH_op A0 A1 B0 B1)"   
  proof (rule CHSH_op_expand_right)
    show "A0 \<in> carrier_mat n n" using assms unfolding CHSH_cond_def by simp
    show "A1 \<in> carrier_mat n n" using assms unfolding CHSH_cond_def by simp
    show "B0 \<in> carrier_mat n n" using assms unfolding CHSH_cond_def by simp
    show "B1 \<in> carrier_mat n n" using assms unfolding CHSH_cond_def by simp
    show "CHSH_op A0 A1 B0 B1 \<in> carrier_mat n n" 
      using assms CHSH_op_dim[of A0] 
      unfolding CHSH_cond_def by force
  qed
  also have "... = A0 * B1 * (CHSH_op A0 A1 B0 B1) - 
    A0 * B0 * (CHSH_op A0 A1 B0 B1) + 
    A1 * B0 * (CHSH_op A0 A1 B0 B1) +
    (A1 * B1 * (A0 * B1) - A1 * B1 * (A0 * B0) + A1 * B1 * (A1 * B0) + 
    A1 * B1 * (A1 * B1))"
    using assms CHSH_op_expand_left[of A0  n n A1 B0 n B1 "A1*B1"]  
      unfolding CHSH_cond_def by auto
  also have "... = A0 * B1 * (CHSH_op A0 A1 B0 B1) - 
    A0 * B0 * (CHSH_op A0 A1 B0 B1) + 
    A1 * B0 * (CHSH_op A0 A1 B0 B1) +
    (A1*A0 - A1 * A0 * (B1 * B0) + B1 * B0 + 1\<^sub>m n)" using assms by simp
  also have "... = A0 * B1 * (CHSH_op A0 A1 B0 B1) - 
    A0 * B0 * (CHSH_op A0 A1 B0 B1) + 
    (A1 * B0 * (A0 * B1) - A1 * B0 * (A0 * B0) + A1 * B0 * (A1 * B0) + 
    A1 * B0 * (A1 * B1)) + 
    (A1*A0 - A1 * A0 * (B1 * B0) + B1 * B0 + 1\<^sub>m n)"
    using assms CHSH_op_expand_left[of A0  n n A1 B0 n B1 "A1*B0"] 
    unfolding CHSH_cond_def by auto
  also have "... = A0 * B1 * (CHSH_op A0 A1 B0 B1) - 
    A0 * B0 * (CHSH_op A0 A1 B0 B1) + 
    (A1 * A0 * (B0 * B1) - A1 * A0  + 1\<^sub>m n + B0 * B1) + 
    (A1 * A0 - A1 * A0 * (B1 * B0) + B1 * B0 + 1\<^sub>m n)" using assms by simp
  also have "... = A0 * B1 * (CHSH_op A0 A1 B0 B1) - 
    (A0 * B0 * (A0 * B1) - A0 * B0 * (A0 * B0) + A0 * B0 * (A1 * B0) + 
    A0 * B0 * (A1 * B1)) + 
    (A1 * A0 * (B0 * B1) - A1 * A0  + 1\<^sub>m n + B0 * B1) + 
    (A1 * A0 - A1 * A0 * (B1 * B0) + B1 * B0 + 1\<^sub>m n)"
    using assms CHSH_op_expand_left[of A0  n n A1 B0 n B1 "A0*B0"] 
    unfolding CHSH_cond_def by auto
  also have "... = A0 * B1 * (CHSH_op A0 A1 B0 B1) - 
    (B0* B1 - 1\<^sub>m n + A0 * A1 + A0 * A1 * (B0 * B1)) + 
    (A1 * A0 * (B0 * B1) - A1 * A0  + 1\<^sub>m n + B0 * B1) + 
    (A1 * A0 - A1 * A0 * (B1 * B0) + B1 * B0 + 1\<^sub>m n)" 
    using assms by simp
  also have "... = 
    (A0 * B1 * (A0 * B1) - A0 * B1 * (A0 * B0) + A0 * B1 * (A1 * B0) + 
    A0 * B1 * (A1 * B1)) - 
    (B0* B1 - 1\<^sub>m n + A0 * A1 + A0 * A1 * (B0 * B1)) + 
    (A1 * A0 * (B0 * B1) - A1 * A0  + 1\<^sub>m n + B0 * B1) + 
    (A1 * A0 - A1 * A0 * (B1 * B0) + B1 * B0 + 1\<^sub>m n)"
    using assms CHSH_op_expand_left[of A0  n n A1 B0 n B1 "A0*B1"] 
    unfolding CHSH_cond_def by auto
  also have "... = (1\<^sub>m n - B1 *  B0 + A0 * A1 * (B1 * B0) + A0 * A1) - 
    (B0 * B1 - 1\<^sub>m n + A0 * A1 + A0 * A1 * (B0 * B1)) + 
    (A1 * A0 * (B0 * B1) - A1 * A0  + 1\<^sub>m n + B0 * B1) + 
    (A1 * A0 - A1 * A0 * (B1 * B0) + B1 * B0 + 1\<^sub>m n)" 
    using assms by simp  
  also have "... = (1\<^sub>m n  + A0 * A1 * (B1 * B0)  + 1\<^sub>m n  - 
    A0 * A1 * (B0 * B1)) + 
    (A1 * A0 * (B0 * B1)  + 1\<^sub>m n) - A1 * A0 * (B1 * B0)  + 1\<^sub>m n" 
    using assms unfolding CHSH_cond_def 
    by (auto simp add:  algebra_simps)
  also have "... = (4::nat)\<cdot>\<^sub>m 1\<^sub>m n - 
    (A0 * A1 * (B0 * B1) - A0 * A1 * (B1 * B0) - A1 * A0 *(B0 * B1) + 
    A1 * A0 * (B1 * B0))"
    using assms unfolding CHSH_cond_def 
    by (auto simp add: algebra_simps)
  also have "... = (4::nat)\<cdot>\<^sub>m 1\<^sub>m n - (commutator A0 A1) * (commutator B0 B1)"
    using assms commutator_mult_expand[of A0 n A1] 
    unfolding CHSH_cond_def by simp
  finally show ?thesis .
qed

lemma CHSH_cond_hermitD:
  assumes "CHSH_cond_hermit n A0 A1 B0 B1"
  shows "CHSH_cond n A0 A1 B0 B1"
  "hermitian A0"
  "hermitian A1"
  "hermitian B0"
  "hermitian B1"
  using assms unfolding CHSH_cond_hermit_def by auto

lemma CHSH_cond_hermit_unitary: 
  assumes "CHSH_cond_hermit n A0 A1 B0 B1"
  shows "unitary A0" "unitary A1" "unitary B0" "unitary B1" 
  using assms unfolding CHSH_cond_hermit_def CHSH_cond_def
  by (metis Complex_Matrix.unitary_def carrier_matD(1) 
      hermitian_def inverts_mat_def)+


lemma CHSH_expect_add:
  assumes "A0 \<in> carrier_mat n n"
  and "A1 \<in> carrier_mat n n"
  and "B0 \<in> carrier_mat n n"
  and "B1 \<in> carrier_mat n n"
  and "R0 \<in> carrier_mat n n"
  and "R1 \<in> carrier_mat n n"
shows "CHSH_expect A0 A1 B0 B1 (R0 + R1) = 
  CHSH_expect A0 A1 B0 B1 R0 +
  CHSH_expect A0 A1 B0 B1 R1" 
proof -
  note chsh = CHSH_op_dim[OF assms(1) assms(2) assms(3) assms(4)]
  have "CHSH_op A0 A1 B0 B1 * (R0 + R1) = 
    CHSH_op A0 A1 B0 B1 * R0 + CHSH_op A0 A1 B0 B1 * R1" 
    using  mult_add_distrib_mat[OF chsh] assms by auto 
  thus ?thesis 
  using assms trace_add_linear unfolding CHSH_expect_def
  by (metis chsh mult_carrier_mat)
qed

lemma CHSH_expect_zero:
assumes "A0 \<in> carrier_mat n n"
  and "A1 \<in> carrier_mat n n"
  and "B0 \<in> carrier_mat n n"
  and "B1 \<in> carrier_mat n n"
shows "CHSH_expect A0 A1 B0 B1 (0\<^sub>m n n) = 0" 
  using CHSH_expect_expand assms
proof -
  have "CHSH_expect A0 A1 B0 B1 (0\<^sub>m n n) = 
    Complex_Matrix.trace (A0 * B1 * 0\<^sub>m n n) -
    Complex_Matrix.trace (A0 * B0 * 0\<^sub>m n n) + 
    Complex_Matrix.trace (A1 * B0 * 0\<^sub>m n n) + 
    Complex_Matrix.trace (A1 * B1 * 0\<^sub>m n n)"
    by (meson CHSH_expect_expand assms zero_carrier_mat)
  then show ?thesis
    using assms(2) assms(3) assms(4) by force
qed

lemma (in cpx_sq_mat) CHSH_expect_sum:
  assumes "finite S" 
  and "A0 \<in> fc_mats"
  and "A1 \<in> fc_mats"
  and "B0 \<in> fc_mats"
  and "B1 \<in> fc_mats"
  and "\<And>i. i \<in> S \<Longrightarrow> R i \<in> fc_mats"  
shows "CHSH_expect A0 A1 B0 B1 (sum_mat R S) = 
  sum (\<lambda>i. CHSH_expect A0 A1 B0 B1 (R i)) S" using assms
proof (induct rule: finite_induct)
  case empty
  then show ?case using CHSH_expect_zero
    by (metis dim_eq fc_mats_carrier sum.empty sum_mat_empty)
next
  case (insert x F)
  have "CHSH_expect A0 A1 B0 B1 (sum_mat R (insert x F)) = 
    CHSH_expect A0 A1 B0 B1 (R x + (sum_mat R F))" 
    using insert sum_mat_insert[of R]
    by (simp add: image_subsetI)
  also have "... = CHSH_expect A0 A1 B0 B1 (R x) +
    CHSH_expect A0 A1 B0 B1 (sum_mat R F)" 
  proof (rule CHSH_expect_add) 
    have fc: "fc_mats = carrier_mat dimR dimR" 
      using fc_mats_carrier dim_eq by simp
    show "A0 \<in> carrier_mat dimR dimR" "A1 \<in> carrier_mat dimR dimR"
      "B0 \<in> carrier_mat dimR dimR" "B1 \<in> carrier_mat dimR dimR"
      "R x \<in> carrier_mat dimR dimR" 
      using insert fc by auto
    show "sum_mat R F \<in> carrier_mat dimR dimR" 
      using insert fc sum_mat_carrier dim_eq by blast
  qed
  also have "... = sum (\<lambda>i. CHSH_expect A0 A1 B0 B1 (R i)) (insert x F)"
    by (simp add: assms insert(1) insert(2) insert(3) insert(8))
  finally show ?case .
qed

lemma CHSH_expect_smult:
 assumes "A0 \<in> carrier_mat n n"
  and "A1 \<in> carrier_mat n n"
  and "B0 \<in> carrier_mat n n"
  and "B1 \<in> carrier_mat n n"
  and "R0 \<in> carrier_mat n n"
shows "CHSH_expect A0 A1 B0 B1 (a  \<cdot>\<^sub>m R0) = 
  a * CHSH_expect A0 A1 B0 B1 R0"
proof -
  note chsh = CHSH_op_dim[OF assms(1) assms(2) assms(3) assms(4)]
  show ?thesis using chsh
    by (metis (no_types, lifting) CHSH_expect_def assms(5) mult_carrier_mat 
        mult_smult_distrib trace_smult) 
qed

lemma CHSH_expect_real:
  assumes "0 < n"
  and "CHSH_cond_hermit n A0 A1 B0 B1"
  and "R\<in> carrier_mat n n"
  and "Complex_Matrix.positive R"
  shows "CHSH_expect A0 A1 B0 B1 R \<in> Reals"
proof -
  define fc::"complex Matrix.mat set" where "fc = carrier_mat n n"
  interpret cpx_sq_mat n n fc  
  proof 
    show "0 < n" using assms by simp
  qed (auto simp add: fc_def)
  have "Complex_Matrix.trace (A0 * B1 * R) \<in> Reals" 
  proof (rule pos_hermitian_trace_reals)
    show "A0 * B1 \<in> carrier_mat n n" using assms 
      unfolding CHSH_cond_hermit_def CHSH_cond_def
      by (metis mult_carrier_mat)
    show "hermitian (A0*B1)" using hermitian_commute assms 
      unfolding CHSH_cond_hermit_def CHSH_cond_def 
      by blast
  qed (auto simp add: assms)
  moreover have "Complex_Matrix.trace (A0 * B0 * R) \<in> Reals" 
  proof (rule pos_hermitian_trace_reals)
    show "A0 * B0 \<in> carrier_mat n n" using assms 
      unfolding CHSH_cond_hermit_def CHSH_cond_def
      by (metis mult_carrier_mat)
    show "hermitian (A0*B0)" using hermitian_commute assms 
      unfolding CHSH_cond_hermit_def CHSH_cond_def 
      by blast
  qed (auto simp add: assms)
  moreover have "Complex_Matrix.trace (A1 * B0 * R) \<in> Reals" 
  proof (rule pos_hermitian_trace_reals)
    show "A1 * B0 \<in> carrier_mat n n" using assms 
      unfolding CHSH_cond_hermit_def CHSH_cond_def
      by (metis mult_carrier_mat)
    show "hermitian (A1*B0)" using hermitian_commute assms 
      unfolding CHSH_cond_hermit_def CHSH_cond_def 
      by blast
  qed (auto simp add: assms)
  moreover have "Complex_Matrix.trace (A1 * B1 * R) \<in> Reals" 
  proof (rule pos_hermitian_trace_reals)
    show "A1 * B1 \<in> carrier_mat n n" using assms 
      unfolding CHSH_cond_hermit_def CHSH_cond_def
      by (metis mult_carrier_mat)
    show "hermitian (A1*B1)" using hermitian_commute assms 
      unfolding CHSH_cond_hermit_def CHSH_cond_def 
      by blast
  qed (auto simp add: assms)
  moreover have "CHSH_expect A0 A1 B0 B1 R = 
    Complex_Matrix.trace (A0 * B1 * R) -
    Complex_Matrix.trace (A0 * B0 * R) +
    Complex_Matrix.trace (A1 * B0 * R) +
    Complex_Matrix.trace (A1 * B1 * R)" 
    using CHSH_expect_expand assms 
    unfolding CHSH_cond_hermit_def CHSH_cond_def by meson
  ultimately show ?thesis by simp
qed

lemma CHSH_op_square_L2_op_nrm_le:
  assumes "CHSH_cond_hermit n A0 A1 B0 B1"
  and "0 < n"
  shows "L2_op_nrm ((CHSH_op A0 A1 B0 B1) * (CHSH_op A0 A1 B0 B1)) \<le> 8"
proof -
  have dima: "commutator A0 A1 \<in> carrier_mat n n" 
    using  assms commutator_dim unfolding CHSH_cond_hermit_def CHSH_cond_def 
    by metis 
  moreover have dimb: "commutator B0 B1 \<in> carrier_mat n n" 
    using  assms commutator_dim unfolding CHSH_cond_hermit_def CHSH_cond_def 
    by metis 
  ultimately have 
    dim: "(commutator A0 A1) * (commutator B0 B1) \<in> carrier_mat n n" by simp
  have "L2_op_nrm ((CHSH_op A0 A1 B0 B1) * (CHSH_op A0 A1 B0 B1)) = 
    L2_op_nrm ((4::nat) \<cdot>\<^sub>m (1\<^sub>m n) - (commutator A0 A1) * (commutator B0 B1))" 
    using CHSH_op_square[of n] assms unfolding CHSH_cond_hermit_def by simp
  also have "... \<le> L2_op_nrm ((4::nat) \<cdot>\<^sub>m (1\<^sub>m n)) + 
    L2_op_nrm ((commutator A0 A1) * (commutator B0 B1))"
    by (rule L2_op_nrm_triangle', (auto simp add: assms dim))
  also have "... = 4 + L2_op_nrm ((commutator A0 A1) * (commutator B0 B1))" 
    using idty_smult_nat_L2_op_nrm[of n 4] assms by simp
  also have "... \<le> 4 + L2_op_nrm (commutator A0 A1) * L2_op_nrm (commutator B0 B1)"
  proof -
    have "L2_op_nrm ((commutator A0 A1) * (commutator B0 B1)) \<le> 
      L2_op_nrm (commutator A0 A1) * L2_op_nrm (commutator B0 B1)"
    proof (rule L2_op_nrm_mult_le)
      show "commutator A0 A1 \<in> carrier_mat n n" using assms commutator_dim 
        unfolding CHSH_cond_hermit_def CHSH_cond_def by simp
      show "commutator B0 B1 \<in> carrier_mat n n" using assms commutator_dim 
        unfolding CHSH_cond_hermit_def CHSH_cond_def by simp
    qed (simp add: assms)
    thus ?thesis by simp
  qed
  also have "... \<le> 4 + L2_op_nrm (commutator A0 A1) * 2" 
  proof -
    have "L2_op_nrm (commutator B0 B1) \<le> 2" 
      using comm_L2_op_nrm_le[of B0 n] assms commutator_dim 
      unfolding CHSH_cond_hermit_def CHSH_cond_def by simp
    hence "L2_op_nrm (commutator A0 A1) * L2_op_nrm (commutator B0 B1) \<le> 
      L2_op_nrm (commutator A0 A1) * 2"
      using L2_op_nrm_geq_0 dima
      by (metis Groups.mult_ac(2) assms(2) linorder_not_less 
          mult_le_cancel_right)
    thus ?thesis by simp
  qed
  also have "... \<le> 4 + 4"
  proof -
    have "L2_op_nrm (commutator A0 A1) \<le> 2" 
      using comm_L2_op_nrm_le[of A0 n] assms commutator_dim 
      unfolding CHSH_cond_hermit_def CHSH_cond_def by simp
    hence "L2_op_nrm (commutator A0 A1) * 2 \<le> 2 * 2" by linarith      
    thus ?thesis by simp
  qed
  finally show "L2_op_nrm ((CHSH_op A0 A1 B0 B1) * (CHSH_op A0 A1 B0 B1)) \<le> 8" 
    by simp
qed

lemma CHSH_op_square_spmax_le:
  assumes "CHSH_cond_hermit n A0 A1 B0 B1"
  and "0 < n"
shows "spmax ((CHSH_op A0 A1 B0 B1) * (CHSH_op A0 A1 B0 B1)) \<le> 8"
proof -
  define Op where "Op = CHSH_op A0 A1 B0 B1"
  have "spmax (Op * Op) =  L2_op_nrm (Op * Op)" 
  proof (rule hermitian_L2_op_nrm_spmax_eq[symmetric])
    show "0 < dim_row (Op * Op)" 
      using assms CHSH_op_dim[of A0 n n A1 B0 n B1] 
      unfolding Op_def CHSH_cond_hermit_def CHSH_cond_def by simp
    show "hermitian (Op * Op)" 
      using hermitian_square_hermitian[of Op] CHSH_op_hermitian[of A0] assms 
      unfolding Op_def CHSH_cond_hermit_def CHSH_cond_def by simp
  qed
  also have "... \<le> 8" using CHSH_op_square_L2_op_nrm_le assms 
    unfolding Op_def by simp
  finally show ?thesis unfolding Op_def .
qed

lemma CHSH_op_L2_op_nrm_le:
assumes "CHSH_cond_hermit n A0 A1 B0 B1"
  and "0 < n"
shows "L2_op_nrm (CHSH_op A0 A1 B0 B1) \<le> 2 * sqrt 2"
proof -
  define Op where "Op = CHSH_op A0 A1 B0 B1"
  have "L2_op_nrm Op = max_sgval Op" 
    using L2_op_nrm_max_sgval_eq[of Op n] CHSH_op_dim[of A0 n n] assms
    unfolding CHSH_cond_hermit_def CHSH_cond_def Op_def by simp
  also have "... = sqrt (spmax (Op * Op))" 
    using CHSH_op_hermitian[of A0] assms 
    unfolding max_sgval_def hermitian_def CHSH_cond_hermit_def 
      CHSH_cond_def Op_def 
    by simp
  also have "... \<le> sqrt 8" 
    using assms CHSH_op_square_spmax_le[of n A0 A1 B0 B1] 
    unfolding Op_def 
    by simp
  also have "... = 2 * sqrt 2" 
    by (metis mult_2_right numeral.simps(2) real_sqrt_four real_sqrt_mult) 
  finally show ?thesis unfolding Op_def .
qed

lemma (in cpx_sq_mat) CHSH_cond_hermit_lhv_upper:
  assumes "CHSH_cond_hermit dimR A0 A1 B0 B1"
  and "lhv M A0 B1 R U0 V1"
  and "lhv M A0 B0 R U0 V0"
  and "lhv M A1 B0 R U1 V0"
  and "lhv M A1 B1 R U1 V1"
  and "0 < n"
shows "\<bar>(LINT w|M. qt_expect A0 U0 w * qt_expect B1 V1 w) -
        (LINT w|M. qt_expect A0 U0 w * qt_expect B0 V0 w) + 
        (LINT w|M. qt_expect A1 U1 w * qt_expect B0 V0 w) + 
        (LINT w|M. qt_expect A1 U1 w * qt_expect B1 V1 w)\<bar>
        \<le> 2" 
proof - 
  have "\<bar>(LINT w|M. qt_expect A0 U0 w * qt_expect B1 V1 w) -
        (LINT w|M. qt_expect A0 U0 w * qt_expect B0 V0 w) + 
        (LINT w|M. qt_expect A1 U1 w * qt_expect B0 V0 w) + 
        (LINT w|M. qt_expect A1 U1 w * qt_expect B1 V1 w)\<bar> = 
        \<bar>(LINT w|M. qt_expect A1 U1 w * qt_expect B0 V0 w) + 
        (LINT w|M. qt_expect A0 U0 w * qt_expect B1 V1 w)  + 
        (LINT w|M. qt_expect A1 U1 w * qt_expect B1 V1 w)-
        (LINT w|M. qt_expect A0 U0 w * qt_expect B0 V0 w)\<bar>" by simp
  also have "... \<le> 2"
  proof (rule prob_space.chsh_expect)
    show "prob_space M" using assms unfolding lhv_def by simp
    show "AE w in M. \<bar>qt_expect A0 U0 w\<bar> \<le> 1" unfolding qt_expect_def
    proof (rule spectrum_abs_1_weighted_suml)
      show "lhv M A0 B1 R U0 V1" using assms by simp
      show "hermitian A0" using assms unfolding CHSH_cond_hermit_def by simp
      show "A0 \<in> fc_mats" using fc_mats_carrier dim_eq assms 
        unfolding CHSH_cond_hermit_def CHSH_cond_def by simp
      thus "{Re x |x. x \<in> spectrum A0} \<subseteq> {- 1, 1}" 
        using assms CHSH_cond_hermit_unitary(1) unitary_hermitian_Re_spectrum
          \<open>hermitian A0\<close> fc_mats_carrier npos dim_eq
        by (metis (no_types, lifting))
      show "{Re x |x. x \<in> spectrum A0} \<noteq> {}" 
        using \<open>A0\<in> fc_mats\<close> fc_mats_carrier npos dim_eq 
          \<open>hermitian A0\<close> spectrum_ne by fastforce 
    qed
    show "AE w in M. \<bar>qt_expect A1 U1 w\<bar> \<le> 1" unfolding qt_expect_def
    proof (rule spectrum_abs_1_weighted_suml)
      show "lhv M A1 B1 R U1 V1" using assms by simp
      show "hermitian A1" using assms unfolding CHSH_cond_hermit_def by simp
      show "A1 \<in> fc_mats" using fc_mats_carrier dim_eq assms 
        unfolding CHSH_cond_hermit_def CHSH_cond_def by simp
      thus "{Re x |x. x \<in> spectrum A1} \<subseteq> {- 1, 1}" 
        using assms CHSH_cond_hermit_unitary(2) unitary_hermitian_Re_spectrum
          \<open>hermitian A1\<close> fc_mats_carrier npos dim_eq 
        by (metis (no_types, lifting))
      show "{Re x |x. x \<in> spectrum A1} \<noteq> {}" 
        using \<open>A1\<in> fc_mats\<close> fc_mats_carrier npos dim_eq 
          \<open>hermitian A1\<close> spectrum_ne by fastforce 
    qed
    show "AE w in M. \<bar>qt_expect B0 V0 w\<bar> \<le> 1" unfolding qt_expect_def
    proof (rule spectrum_abs_1_weighted_sumr)
      show "lhv M A1 B0 R U1 V0" using assms by simp
      show "hermitian B0" using assms unfolding CHSH_cond_hermit_def by simp
      show "B0 \<in> fc_mats" using fc_mats_carrier dim_eq assms 
        unfolding CHSH_cond_hermit_def CHSH_cond_def by simp
      thus "{Re x |x. x \<in> spectrum B0} \<subseteq> {- 1, 1}" 
        using assms CHSH_cond_hermit_unitary(3) unitary_hermitian_Re_spectrum
          \<open>hermitian B0\<close> fc_mats_carrier npos dim_eq 
        by (metis (no_types, lifting))
      show "{Re x |x. x \<in> spectrum B0} \<noteq> {}" 
        using \<open>B0\<in> fc_mats\<close> fc_mats_carrier npos dim_eq 
          \<open>hermitian B0\<close> spectrum_ne by fastforce 
    qed
    show "AE w in M. \<bar>qt_expect B1 V1 w\<bar> \<le> 1" unfolding qt_expect_def
    proof (rule spectrum_abs_1_weighted_sumr)
      show "lhv M A1 B1 R U1 V1" using assms by simp
      show "hermitian B1" using assms unfolding CHSH_cond_hermit_def by simp
      show "B1 \<in> fc_mats" using fc_mats_carrier dim_eq assms 
        unfolding CHSH_cond_hermit_def CHSH_cond_def by simp
      thus "{Re x |x. x \<in> spectrum B1} \<subseteq> {- 1, 1}" 
        using assms CHSH_cond_hermit_unitary(4) unitary_hermitian_Re_spectrum
          \<open>hermitian B1\<close> fc_mats_carrier npos dim_eq 
        by (metis (no_types, lifting))
      show "{Re x |x. x \<in> spectrum B1} \<noteq> {}" 
        using \<open>B1\<in> fc_mats\<close> fc_mats_carrier npos dim_eq 
          \<open>hermitian B1\<close> spectrum_ne by fastforce 
    qed
    show "integrable M (\<lambda>w. qt_expect A0 U0 w * qt_expect B1 V1 w)"
      using spectr_sum_integrable[of M] assms by simp
    show "integrable M (\<lambda>w. qt_expect A1 U1 w * qt_expect B1 V1 w)"
      using spectr_sum_integrable[of M] assms by simp
    show "integrable M (\<lambda>w. qt_expect A1 U1 w * qt_expect B0 V0 w)"
      using spectr_sum_integrable[of M] assms by simp
    show "integrable M (\<lambda>w. qt_expect A0 U0 w * qt_expect B0 V0 w)"
      using spectr_sum_integrable[of M] assms by simp
  qed
  finally show ?thesis .
qed

lemma (in cpx_sq_mat) CHSH_expect_lhv_lint_eq:
  assumes "R \<in> fc_mats"
  and "Complex_Matrix.positive R"
  and "CHSH_cond_hermit dimR A0 A1 B0 B1"
  and "lhv M A0 B1 R U0 V1"
  and "lhv M A0 B0 R U0 V0"
  and "lhv M A1 B0 R U1 V0"
  and "lhv M A1 B1 R U1 V1"
shows "(LINT w|M. qt_expect A0 U0 w * qt_expect B1 V1 w) -
        (LINT w|M. qt_expect A0 U0 w * qt_expect B0 V0 w) + 
        (LINT w|M. qt_expect A1 U1 w * qt_expect B0 V0 w) + 
        (LINT w|M. qt_expect A1 U1 w * qt_expect B1 V1 w) = 
        CHSH_expect A0 A1 B0 B1 R" (is "?L = ?R")
proof -
  have "A0 \<in> fc_mats" using assms fc_mats_carrier dim_eq 
    unfolding CHSH_cond_hermit_def CHSH_cond_def by simp
  have "B0 \<in> fc_mats" using assms fc_mats_carrier dim_eq 
    unfolding CHSH_cond_hermit_def CHSH_cond_def by simp
  have "A1 \<in> fc_mats" using assms fc_mats_carrier dim_eq 
    unfolding CHSH_cond_hermit_def CHSH_cond_def by simp
  have "B1 \<in> fc_mats" using assms fc_mats_carrier dim_eq 
    unfolding CHSH_cond_hermit_def CHSH_cond_def by simp
  have "LINT w|M. qt_expect A0 U0 w * qt_expect B1 V1 w = 
    Re (Complex_Matrix.trace (A0 * B1 * R))" 
  proof (rule sum_qt_expect)
    show "hermitian A0" "hermitian B1" 
      using assms unfolding CHSH_cond_hermit_def by auto
  qed (auto simp add: \<open>A0 \<in> fc_mats\<close> \<open>B1 \<in> fc_mats\<close> assms)
  moreover have "LINT w|M. qt_expect A0 U0 w * qt_expect B0 V0 w = 
    Re (Complex_Matrix.trace (A0 * B0 * R))" 
  proof (rule sum_qt_expect)
    show "hermitian A0" "hermitian B0" 
      using assms unfolding CHSH_cond_hermit_def by auto
  qed (auto simp add: \<open>A0 \<in> fc_mats\<close> \<open>B0 \<in> fc_mats\<close> assms)
  moreover have "LINT w|M. qt_expect A1 U1 w * qt_expect B0 V0 w = 
    Re (Complex_Matrix.trace (A1 * B0 * R))" 
  proof (rule sum_qt_expect)
    show "hermitian A1" "hermitian B0" 
      using assms unfolding CHSH_cond_hermit_def by auto
  qed (auto simp add: \<open>A1 \<in> fc_mats\<close> \<open>B0 \<in> fc_mats\<close> assms)
  moreover have "LINT w|M. qt_expect A1 U1 w * qt_expect B1 V1 w = 
    Re (Complex_Matrix.trace (A1 * B1 * R))" 
  proof (rule sum_qt_expect)
    show "hermitian A1" "hermitian B1" 
      using assms unfolding CHSH_cond_hermit_def by auto
  qed (auto simp add: \<open>A1 \<in> fc_mats\<close> \<open>B1 \<in> fc_mats\<close> assms)
  ultimately have "?L = 
    Re (Complex_Matrix.trace (A0 * B1 * R)) -
    Re (Complex_Matrix.trace (A0 * B0 * R)) +
    Re (Complex_Matrix.trace (A1 * B0 * R)) +
    Re (Complex_Matrix.trace (A1 * B1 * R))" by simp
  also have "... = Re (Complex_Matrix.trace (A0 * B1 * R) -
    Complex_Matrix.trace (A0 * B0 * R) +
    Complex_Matrix.trace (A1 * B0 * R) +
    Complex_Matrix.trace (A1 * B1 * R))" by simp
  also have "... = Re (CHSH_expect A0 A1 B0 B1 R)" 
    using CHSH_expect_expand assms fc_mats_carrier dim_eq 
      \<open>A0 \<in> fc_mats\<close> \<open>B0 \<in> fc_mats\<close> \<open>A1 \<in> fc_mats\<close> \<open>B1 \<in> fc_mats\<close>
    by metis
  also have "... = CHSH_expect A0 A1 B0 B1 R" 
    using CHSH_expect_real assms fc_mats_carrier dim_eq npos 
    by simp
  finally show ?thesis .
qed

subsection \<open>CHSH inequality for separable density matrices\<close>

definition CHSH_cond_local where
"CHSH_cond_local n m A0 A1 B0 B1 \<equiv>
  A0 \<in> carrier_mat n n \<and> A1 \<in> carrier_mat n n \<and>
  B0 \<in> carrier_mat m m \<and> B1 \<in> carrier_mat m m \<and>
  hermitian A0 \<and> hermitian A1 \<and> hermitian B0 \<and> hermitian B1 \<and>
  A0 * A0 = 1\<^sub>m n \<and> A1 * A1 = 1\<^sub>m n \<and> B0 * B0 = 1\<^sub>m m \<and> B1 * B1 = 1\<^sub>m m"

lemma CHSH_cond_local_imp_cond_hermit:
  assumes "CHSH_cond_local n m A0 A1 B0 B1"
  and "0 < n"
  and "0 < m"
  shows "CHSH_cond_hermit (n*m) (A0 \<Otimes> 1\<^sub>m m) (A1 \<Otimes> 1\<^sub>m m) 
    (1\<^sub>m n \<Otimes> B0) (1\<^sub>m n \<Otimes> B1)"
  unfolding CHSH_cond_hermit_def CHSH_cond_def
proof (intro conjI)
  show "A0 \<Otimes> 1\<^sub>m m \<in> carrier_mat (n * m) (n * m)" 
    "A1 \<Otimes> 1\<^sub>m m \<in> carrier_mat (n * m) (n * m)" 
    "1\<^sub>m n \<Otimes> B0 \<in> carrier_mat (n * m) (n * m)"
    "1\<^sub>m n \<Otimes> B1 \<in> carrier_mat (n * m) (n * m)"
    using assms unfolding CHSH_cond_local_def by auto
  show "hermitian (A0 \<Otimes> 1\<^sub>m m)" "hermitian (A1 \<Otimes> 1\<^sub>m m)" 
    "hermitian (1\<^sub>m n \<Otimes> B0)" "hermitian (1\<^sub>m n \<Otimes> B1)"
    using assms tensor_mat_hermitian unfolding CHSH_cond_local_def
    by (metis hermitian_one one_carrier_mat)+
  show "(A0 \<Otimes> 1\<^sub>m m) * (A0 \<Otimes> 1\<^sub>m m) = 1\<^sub>m (n * m)" 
    using assms tensor_mat_square_idty idty_square 
    unfolding CHSH_cond_local_def by auto
  show "(A1 \<Otimes> 1\<^sub>m m) * (A1 \<Otimes> 1\<^sub>m m) = 1\<^sub>m (n * m)"
    using assms tensor_mat_square_idty idty_square 
    unfolding CHSH_cond_local_def by auto
  show "(1\<^sub>m n \<Otimes> B0) * (1\<^sub>m n \<Otimes> B0) = 1\<^sub>m (n * m)"
    using assms tensor_mat_square_idty idty_square 
    unfolding CHSH_cond_local_def by auto
  show "(1\<^sub>m n \<Otimes> B1) * (1\<^sub>m n \<Otimes> B1) = 1\<^sub>m (n * m)"
    using assms tensor_mat_square_idty idty_square 
    unfolding CHSH_cond_local_def by auto
  show "(A0 \<Otimes> 1\<^sub>m m) * (1\<^sub>m n \<Otimes> B1) = (1\<^sub>m n \<Otimes> B1) * (A0 \<Otimes> 1\<^sub>m m)"
    using tensor_mat_commute assms unfolding CHSH_cond_local_def
    by (smt (verit) assoc_mult_mat mult_carrier_mat)
  show "(A0 \<Otimes> 1\<^sub>m m) * (1\<^sub>m n \<Otimes> B0) = (1\<^sub>m n \<Otimes> B0) * (A0 \<Otimes> 1\<^sub>m m)"
    using tensor_mat_commute assms unfolding CHSH_cond_local_def
    by (smt (verit) assoc_mult_mat mult_carrier_mat)
  show "(A1 \<Otimes> 1\<^sub>m m) * (1\<^sub>m n \<Otimes> B0) = (1\<^sub>m n \<Otimes> B0) * (A1 \<Otimes> 1\<^sub>m m)"
    using tensor_mat_commute assms unfolding CHSH_cond_local_def
    by (smt (verit) assoc_mult_mat mult_carrier_mat)
  show "(A1 \<Otimes> 1\<^sub>m m) * (1\<^sub>m n \<Otimes> B1) = (1\<^sub>m n \<Otimes> B1) * (A1 \<Otimes> 1\<^sub>m m)"
    using tensor_mat_commute assms unfolding CHSH_cond_local_def
    by (smt (verit) assoc_mult_mat mult_carrier_mat)
qed

lemma limit_CHSH_cond:
  shows "CHSH_cond_hermit 4 Z_I X_I I_ZmX I_XpZ"
proof -
  have "CHSH_cond_hermit (2 * 2) Z_I X_I I_ZmX I_XpZ" 
    unfolding Z_I_def X_I_def I_ZmX_def I_XpZ_def 
  proof (rule CHSH_cond_local_imp_cond_hermit)
    show "CHSH_cond_local 2 2 Z X ZmX XpZ" unfolding CHSH_cond_local_def
      by (simp add: X_carrier X_hermitian XpZ_carrier XpZ_hermitian XpZ_inv 
          Z_carrier Z_hermitian ZmX_carrier ZmX_hermitian ZmX_inv)
  qed auto
  thus ?thesis by simp
qed

lemma CHSH_expect_separable_expand:
  assumes "separately_decomposes R n nA nB K F S"
  and "A0 \<in> carrier_mat nA nA"
  and "A1 \<in> carrier_mat nA nA"
  and "B0 \<in> carrier_mat nB nB"
  and "B1 \<in> carrier_mat nB nB"
shows "CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1) R =
  sum (\<lambda>a. K a * CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1)
      ((F a) \<Otimes> (S a))) {..< n}"  
proof -
  define fc::"complex Matrix.mat set" 
    where "fc = carrier_mat (nA * nB) (nA * nB)"
  interpret cpx_sq_mat "nA * nB" "nA * nB" fc
  proof
    show "fc = carrier_mat (nA * nB) (nA * nB)" using fc_def by simp
    show "0 < nA * nB" using assms  separately_decomposes_carrier_pos 
      by simp
  qed simp   
  have dec: "\<And>a. a \<in> {..<n} \<Longrightarrow> (F a \<Otimes> S a) \<in> fc"
  proof -
    fix a
    assume "a\<in> {..< n}"
    hence "F a \<in> carrier_mat nA nA" "S a\<in> carrier_mat nB nB" 
      using assms unfolding separately_decomposes_def by auto
    thus "(F a \<Otimes> S a) \<in> fc" 
      using tensor_mat_carrier assms unfolding fc_def by auto
  qed
  hence dec': "\<And>a. a \<in> {..<n} \<Longrightarrow> K a \<cdot>\<^sub>m (F a \<Otimes> S a) \<in> fc"
    by (simp add: smult_mem)
  have car: "A0 \<Otimes> 1\<^sub>m nB \<in> fc" "A1 \<Otimes> 1\<^sub>m nB \<in> fc" 
    "1\<^sub>m nA \<Otimes> B0 \<in> fc" "1\<^sub>m nA \<Otimes> B1 \<in> fc" 
    using assms tensor_mat_carrier unfolding fc_def by auto
  have "CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1) R =
    CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1)
    (sum_mat (\<lambda>a. K a \<cdot>\<^sub>m ((F a) \<Otimes> (S a))) {..< n})" 
    using assms unfolding separately_decomposes_def by simp
  also have "... =
    sum (\<lambda>a. CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1)
      (K a \<cdot>\<^sub>m ((F a) \<Otimes> (S a)))) {..< n}" 
    by (rule CHSH_expect_sum, (auto simp add: dec' car))
  also have "... = 
    sum (\<lambda>a. K a * CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1)
      ((F a) \<Otimes> (S a))) {..< n}" 
  proof (rule sum.cong)
    fix x
    assume "x\<in> {..< n}"
    thus "CHSH_expect (A0 \<Otimes> 1\<^sub>m nB) (A1 \<Otimes> 1\<^sub>m nB) (1\<^sub>m nA \<Otimes> B0) (1\<^sub>m nA \<Otimes> B1)
      (K x \<cdot>\<^sub>m (F x \<Otimes> S x)) =
      K x * CHSH_expect (A0 \<Otimes> 1\<^sub>m nB) (A1 \<Otimes> 1\<^sub>m nB) (1\<^sub>m nA \<Otimes> B0) 
      (1\<^sub>m nA \<Otimes> B1) (F x \<Otimes> S x)" 
      using car dec CHSH_expect_smult fc_mats_carrier by blast
  qed simp
  finally show ?thesis .
qed

lemma CHSH_expect_tensor_leq:
  assumes "CHSH_cond_local nA nB A0 A1 B0 B1"
  and "RA \<in> carrier_mat nA nA"
  and "density_operator RA"
  and "RB \<in> carrier_mat nB nB"
  and "density_operator RB"
  and "0 < nA"
  and "0 < nB"
shows "\<bar>CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1) (RA\<Otimes>RB)\<bar> \<le>2"
proof -
  have "CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1) (RA\<Otimes>RB) = 
    Complex_Matrix.trace ((A0 \<Otimes> 1\<^sub>m nB) * (1\<^sub>m nA \<Otimes> B1) * (RA\<Otimes>RB)) -
    Complex_Matrix.trace ((A0 \<Otimes> 1\<^sub>m nB) * (1\<^sub>m nA \<Otimes> B0) * (RA\<Otimes>RB)) +
    Complex_Matrix.trace ((A1 \<Otimes> 1\<^sub>m nB) * (1\<^sub>m nA \<Otimes> B0) * (RA\<Otimes>RB)) +
    Complex_Matrix.trace ((A1 \<Otimes> 1\<^sub>m nB) * (1\<^sub>m nA \<Otimes> B1) * (RA\<Otimes>RB))"
  proof (rule CHSH_expect_expand)
    show "A0 \<Otimes> 1\<^sub>m nB \<in> carrier_mat (nA*nB) (nA*nB)"
      using assms unfolding CHSH_cond_local_def
      by (metis carrier_matD(1) carrier_matD(2) index_mult_mat(2) 
          index_mult_mat(3) tensor_mat_carrier)
    show "A1 \<Otimes> 1\<^sub>m nB \<in> carrier_mat (nA*nB) (nA*nB)"
      using assms unfolding CHSH_cond_local_def
      by (metis carrier_matD(1) carrier_matD(2) index_mult_mat(2) 
          index_mult_mat(3) tensor_mat_carrier)
    show "1\<^sub>m nA \<Otimes> B0 \<in> carrier_mat (nA * nB) (nA*nB)"
      using assms unfolding CHSH_cond_local_def
      by (metis carrier_matD(1) carrier_matD(2) index_mult_mat(2) 
          index_mult_mat(3) tensor_mat_carrier)
    show "1\<^sub>m nA \<Otimes> B1 \<in> carrier_mat (nA * nB) (nA * nB)"
      using assms unfolding CHSH_cond_local_def
      by (metis carrier_matD(1) carrier_matD(2) index_mult_mat(2) 
          index_mult_mat(3) tensor_mat_carrier)
    show "(RA\<Otimes>RB) \<in> carrier_mat (nA * nB) (nA * nB)"
      using tensor_mat_carrier assms by blast
  qed
  also have "... = 
    Complex_Matrix.trace ((A0 \<Otimes>  B1) * (RA\<Otimes>RB)) -
    Complex_Matrix.trace ((A0 \<Otimes>  B0) * (RA\<Otimes>RB)) +
    Complex_Matrix.trace ((A1 \<Otimes>  B0) * (RA\<Otimes>RB)) +
    Complex_Matrix.trace ((A1 \<Otimes>  B1) * (RA\<Otimes>RB))" 
    using assms tensor_mat_mult_id  unfolding CHSH_cond_local_def by presburger
  also have "... =  
    Complex_Matrix.trace (A0 * RA) * Complex_Matrix.trace (B1 * RB) -
    Complex_Matrix.trace (A0 * RA) * Complex_Matrix.trace (B0 * RB) +
    Complex_Matrix.trace (A1 * RA) * Complex_Matrix.trace (B0 * RB) +
    Complex_Matrix.trace (A1 * RA) * Complex_Matrix.trace (B1 * RB)" 
  proof -
    have "Complex_Matrix.trace ((A0 \<Otimes>  B1) * (RA\<Otimes>RB)) = 
      Complex_Matrix.trace (A0 * RA) * Complex_Matrix.trace (B1 * RB)"    
      using tensor_mat_trace_mult_distr assms unfolding CHSH_cond_local_def by auto
    moreover have "Complex_Matrix.trace ((A0 \<Otimes>  B0) * (RA\<Otimes>RB)) = 
      Complex_Matrix.trace (A0 * RA) * Complex_Matrix.trace (B0 * RB)"
      using tensor_mat_trace_mult_distr assms unfolding CHSH_cond_local_def by auto
    moreover have "Complex_Matrix.trace ((A1 \<Otimes>  B0) * (RA\<Otimes>RB)) = 
      Complex_Matrix.trace (A1 * RA) * Complex_Matrix.trace (B0 * RB)"
      using tensor_mat_trace_mult_distr assms unfolding CHSH_cond_local_def by auto
    moreover have "Complex_Matrix.trace ((A1 \<Otimes>  B1) * (RA\<Otimes>RB)) = 
      Complex_Matrix.trace (A1 * RA) * Complex_Matrix.trace (B1 * RB)" 
      using tensor_mat_trace_mult_distr assms unfolding CHSH_cond_local_def by auto
    ultimately show ?thesis by simp
  qed
  finally have exp: "CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) 
    (1\<^sub>m nA\<Otimes>B1) (RA\<Otimes>RB) = 
    Complex_Matrix.trace (A0 * RA) * Complex_Matrix.trace (B1 * RB) -
    Complex_Matrix.trace (A0 * RA) * Complex_Matrix.trace (B0 * RB) +
    Complex_Matrix.trace (A1 * RA) * Complex_Matrix.trace (B0 * RB) +
    Complex_Matrix.trace (A1 * RA) * Complex_Matrix.trace (B1 * RB)" .
  have "\<bar>Complex_Matrix.trace (A0 * RA) * Complex_Matrix.trace (B1 * RB) -
    Complex_Matrix.trace (A0 * RA) * Complex_Matrix.trace (B0 * RB) +
    Complex_Matrix.trace (A1 * RA) * Complex_Matrix.trace (B0 * RB) +
    Complex_Matrix.trace (A1 * RA) * Complex_Matrix.trace (B1 * RB)\<bar> \<le> 2"    
  proof (rule chsh_complex)
    show "Complex_Matrix.trace (A0 * RA) \<in> \<real>" 
      using assms unfolding CHSH_cond_local_def
      by (simp add: density_operator_def pos_hermitian_trace_reals)
    show "\<bar>Complex_Matrix.trace (A0*RA) * Complex_Matrix.trace (B1*RB)\<bar> \<le> 1"
    proof (rule cpx_abs_mult_le_1)
      show "\<bar>Complex_Matrix.trace (A0 * RA)\<bar> \<le> 1" 
        using assms hermitian_mult_density_trace unfolding CHSH_cond_local_def by auto
      show "\<bar>Complex_Matrix.trace (B1 * RB)\<bar> \<le> 1" 
        using assms hermitian_mult_density_trace unfolding CHSH_cond_local_def by auto
    qed
    show "Complex_Matrix.trace (A1 * RA) \<in> \<real>" 
      using assms unfolding CHSH_cond_local_def
      by (simp add: density_operator_def pos_hermitian_trace_reals)
    show "\<bar>Complex_Matrix.trace (A1*RA) * Complex_Matrix.trace (B1*RB)\<bar> \<le> 1"
    proof (rule cpx_abs_mult_le_1)
      show "\<bar>Complex_Matrix.trace (A1 * RA)\<bar> \<le> 1" 
        using assms hermitian_mult_density_trace unfolding CHSH_cond_local_def by auto
      show "\<bar>Complex_Matrix.trace (B1 * RB)\<bar> \<le> 1" 
        using assms hermitian_mult_density_trace unfolding CHSH_cond_local_def by auto
    qed
    show "Complex_Matrix.trace (B0 * RB) \<in> \<real>" 
      using assms unfolding CHSH_cond_local_def
      by (simp add: density_operator_def pos_hermitian_trace_reals)
    show "\<bar>Complex_Matrix.trace (A0*RA) * Complex_Matrix.trace (B0*RB)\<bar> \<le> 1"
    proof (rule cpx_abs_mult_le_1)
      show "\<bar>Complex_Matrix.trace (A0 * RA)\<bar> \<le> 1" 
        using assms hermitian_mult_density_trace unfolding CHSH_cond_local_def by auto
      show "\<bar>Complex_Matrix.trace (B0 * RB)\<bar> \<le> 1" 
        using assms hermitian_mult_density_trace unfolding CHSH_cond_local_def by auto
    qed
    show "Complex_Matrix.trace (B1 * RB) \<in> \<real>" 
      using assms unfolding CHSH_cond_local_def
      by (simp add: density_operator_def pos_hermitian_trace_reals)
    show "\<bar>Complex_Matrix.trace (A1*RA) * Complex_Matrix.trace (B0*RB)\<bar> \<le> 1"
    proof (rule cpx_abs_mult_le_1)
      show "\<bar>Complex_Matrix.trace (A1 * RA)\<bar> \<le> 1" 
        using assms hermitian_mult_density_trace unfolding CHSH_cond_local_def by auto
      show "\<bar>Complex_Matrix.trace (B0 * RB)\<bar> \<le> 1" 
        using assms hermitian_mult_density_trace unfolding CHSH_cond_local_def by auto
    qed
  qed
  thus ?thesis using exp by simp
qed

subsection \<open>CHSH inequality for commuting observables\<close>

lemma CHSH_op_square_commute_L2_op_nrm_eq:
  assumes "CHSH_cond_hermit n A0 A1 B0 B1"
  and "0 < n"
  and "commutator A0 A1 = 0\<^sub>m n n \<or> commutator B0 B1 = 0\<^sub>m n n"
  shows "L2_op_nrm ((CHSH_op A0 A1 B0 B1) * (CHSH_op A0 A1 B0 B1)) = 4"
proof -
  have dima: "commutator A0 A1 \<in> carrier_mat n n" 
    using  assms commutator_dim 
    unfolding CHSH_cond_hermit_def CHSH_cond_def by metis 
  moreover have dimb: "commutator B0 B1 \<in> carrier_mat n n" 
    using  assms commutator_dim 
    unfolding CHSH_cond_hermit_def CHSH_cond_def by metis 
  ultimately have 
    dim: "(commutator A0 A1) * (commutator B0 B1) \<in> carrier_mat n n" by simp
  have "L2_op_nrm ((CHSH_op A0 A1 B0 B1) * (CHSH_op A0 A1 B0 B1)) = 
    L2_op_nrm ((4::nat) \<cdot>\<^sub>m (1\<^sub>m n) - (commutator A0 A1) * (commutator B0 B1))" 
    using CHSH_op_square[of n] assms unfolding CHSH_cond_hermit_def by simp
  also have "... = L2_op_nrm ((4::nat) \<cdot>\<^sub>m (1\<^sub>m n))"
  proof (cases "commutator A0 A1 = 0\<^sub>m n n")
    case True
    hence "(commutator A0 A1) * (commutator B0 B1) = 0\<^sub>m n n" 
      using dima dimb by simp
    hence "(4::nat) \<cdot>\<^sub>m (1\<^sub>m n) - (commutator A0 A1) * (commutator B0 B1) = 
      (4::nat) \<cdot>\<^sub>m (1\<^sub>m n)" 
      using right_minus_zero_mat
      by (metis index_one_mat(2) index_one_mat(3) index_smult_mat(2) 
          index_smult_mat(3))
    then show ?thesis by simp
  next
    case False
    hence "commutator B0 B1 = 0\<^sub>m n n" using assms by simp
     hence "(commutator A0 A1) * (commutator B0 B1) = 0\<^sub>m n n" 
      using dima dimb by simp
    hence "(4::nat) \<cdot>\<^sub>m (1\<^sub>m n) - (commutator A0 A1) * (commutator B0 B1) = 
      (4::nat) \<cdot>\<^sub>m (1\<^sub>m n)" 
      using right_minus_zero_mat
      by (metis index_one_mat(2) index_one_mat(3) index_smult_mat(2) 
          index_smult_mat(3))
    then show ?thesis by simp
  qed
  also have "... = 4" using idty_smult_nat_L2_op_nrm[of n 4] assms by simp
  finally show ?thesis .
qed

lemma CHSH_op_square_commute_spmax_eq:
  assumes "CHSH_cond_hermit n A0 A1 B0 B1"
  and "0 < n"
  and "commutator A0 A1 = 0\<^sub>m n n \<or> commutator B0 B1 = 0\<^sub>m n n"
shows "spmax ((CHSH_op A0 A1 B0 B1) * (CHSH_op A0 A1 B0 B1)) =4"
proof -
  define Op where "Op = CHSH_op A0 A1 B0 B1"
  have "spmax (Op * Op) =  L2_op_nrm (Op * Op)" 
  proof (rule hermitian_L2_op_nrm_spmax_eq[symmetric])
    show "0 < dim_row (Op * Op)" 
      using assms CHSH_op_dim[of A0 n n A1 B0 n B1] 
      unfolding Op_def CHSH_cond_hermit_def CHSH_cond_def by simp
    show "hermitian (Op * Op)" 
      using hermitian_square_hermitian[of Op] CHSH_op_hermitian[of A0] assms 
      unfolding Op_def CHSH_cond_hermit_def CHSH_cond_def by simp
  qed
  also have "... =4" using CHSH_op_square_commute_L2_op_nrm_eq assms 
    unfolding Op_def by simp
  finally show ?thesis unfolding Op_def .
qed

lemma CHSH_op_commute_L2_op_nrm_eq:
assumes "CHSH_cond_hermit n A0 A1 B0 B1"
  and "0 < n"
  and "commutator A0 A1 = 0\<^sub>m n n \<or> commutator B0 B1 = 0\<^sub>m n n"
shows "L2_op_nrm (CHSH_op A0 A1 B0 B1) = 2"
proof -
  define Op where "Op = CHSH_op A0 A1 B0 B1"
  have "L2_op_nrm Op = max_sgval Op" 
    using L2_op_nrm_max_sgval_eq[of Op n] CHSH_op_dim[of A0 n n] assms
    unfolding CHSH_cond_hermit_def CHSH_cond_def Op_def by simp
  also have "... = sqrt (spmax (Op * Op))" 
    using CHSH_op_hermitian[of A0] assms 
    unfolding max_sgval_def hermitian_def CHSH_cond_hermit_def 
      CHSH_cond_def Op_def 
    by simp
  also have "... = 2" 
    using assms CHSH_op_square_commute_spmax_eq[of n A0 A1 B0 B1] 
    unfolding Op_def 
    by simp
  finally show ?thesis unfolding Op_def .
qed

subsection \<open>Result summary on the CHSH inequalities\<close>

text \<open>Under the local hidden variable hypothesis, this value is bounded by 2.\<close>
lemma CHSH_expect_lhv_leq:
  assumes "R \<in> carrier_mat n n"
  and "0 < n"
  and "Complex_Matrix.positive R"
  and "CHSH_cond_hermit n A0 A1 B0 B1"
  and "cpx_sq_mat.lhv n n M A0 B1 R U0 V1"
  and "cpx_sq_mat.lhv n n M A0 B0 R U0 V0"
  and "cpx_sq_mat.lhv n n M A1 B0 R U1 V0"
  and "cpx_sq_mat.lhv n n M A1 B1 R U1 V1"
shows "\<bar>CHSH_expect A0 A1 B0 B1 R\<bar> \<le>  2" 
proof -
  define fc::"complex Matrix.mat set" 
    where "fc = carrier_mat n n"
  interpret cpx_sq_mat n n fc
  proof
    show "fc = carrier_mat n n" using fc_def by simp
    show "0 < n" using assms 
      by simp
  qed simp
  have "R\<in> fc" using assms fc_def by simp
  have "\<bar>CHSH_expect A0 A1 B0 B1 R\<bar> \<le> complex_of_real 2" 
  proof (rule cpx_real_abs_leq)
    have "R\<in> carrier_mat n n" using assms by simp
    show "\<bar>(LINT w|M. qt_expect A0 U0 w * qt_expect B1 V1 w) -
          (LINT w|M. qt_expect A0 U0 w * qt_expect B0 V0 w) + 
          (LINT w|M. qt_expect A1 U1 w * qt_expect B0 V0 w) + 
          (LINT w|M. qt_expect A1 U1 w * qt_expect B1 V1 w)\<bar> \<le> 2"
      using CHSH_cond_hermit_lhv_upper assms by blast
    show "CHSH_expect A0 A1 B0 B1 R =
      (LINT w|M. qt_expect A0 U0 w * qt_expect B1 V1 w) -
          (LINT w|M. qt_expect A0 U0 w * qt_expect B0 V0 w) + 
          (LINT w|M. qt_expect A1 U1 w * qt_expect B0 V0 w) + 
          (LINT w|M. qt_expect A1 U1 w * qt_expect B1 V1 w)"
      using CHSH_expect_lhv_lint_eq[OF \<open>R\<in> fc\<close> assms(3) assms(4)] assms
      by fastforce
    show "CHSH_expect A0 A1 B0 B1 R \<in> \<real>" 
      using CHSH_expect_real[OF assms(2) assms(4) assms(1) assms(3)]
      by simp
  qed
  thus ?thesis by simp
qed

text \<open>When the considered density operator is separable, this value is still bounded by 2.\<close>
lemma CHSH_expect_separable_leq:
  assumes "CHSH_cond_local nA nB A0 A1 B0 B1"
  and "separable_density nA nB R"
  and "A0 \<in> carrier_mat nA nA"
  and "A1 \<in> carrier_mat nA nA"
  and "B0 \<in> carrier_mat nB nB"
  and "B1 \<in> carrier_mat nB nB"
shows "\<bar>CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1) R\<bar> 
  \<le> 2" 
proof -
  have "\<exists>n K F S. separately_decomposes R n nA nB K F S"
    using assms unfolding separable_density_def by simp
  from this obtain n K F S where 
    "separately_decomposes R n nA nB K F S" by auto 
  note props = this
  define fc::"complex Matrix.mat set" 
    where "fc = carrier_mat (nA * nB) (nA * nB)"
  interpret cpx_sq_mat "nA * nB" "nA * nB" fc
  proof
    show "fc = carrier_mat (nA * nB) (nA * nB)" using fc_def by simp
    show "0 < nA * nB" using assms props separately_decomposes_carrier_pos 
      by simp
  qed simp   
  have dec: "\<And>a. a \<in> {..<n} \<Longrightarrow> (F a \<Otimes> S a) \<in> fc"
  proof -
    fix a
    assume "a\<in> {..< n}"
    hence "F a \<in> carrier_mat nA nA" "S a\<in> carrier_mat nB nB" 
      using props unfolding separately_decomposes_def by auto
    thus "(F a \<Otimes> S a) \<in> fc" 
      using tensor_mat_carrier assms unfolding fc_def by auto
  qed
  hence dec': "\<And>a. a \<in> {..<n} \<Longrightarrow> K a \<cdot>\<^sub>m (F a \<Otimes> S a) \<in> fc"
    by (simp add: smult_mem)
  have car: "A0 \<Otimes> 1\<^sub>m nB \<in> fc" "A1 \<Otimes> 1\<^sub>m nB \<in> fc" 
    "1\<^sub>m nA \<Otimes> B0 \<in> fc" "1\<^sub>m nA \<Otimes> B1 \<in> fc" 
    using assms tensor_mat_carrier unfolding fc_def by auto
  have "CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1) R =
    CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1)
    (sum_mat (\<lambda>a. K a \<cdot>\<^sub>m ((F a) \<Otimes> (S a))) {..< n})" 
    using props unfolding separately_decomposes_def by simp
  also have "... =
    sum (\<lambda>a. CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1)
      (K a \<cdot>\<^sub>m ((F a) \<Otimes> (S a)))) {..< n}" 
    by (rule CHSH_expect_sum, (auto simp add: dec' car))
  also have "... = 
    sum (\<lambda>a. K a * CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1)
      ((F a) \<Otimes> (S a))) {..< n}" 
  proof (rule sum.cong)
    fix x
    assume "x\<in> {..< n}"
    thus "CHSH_expect (A0 \<Otimes> 1\<^sub>m nB) (A1 \<Otimes> 1\<^sub>m nB) (1\<^sub>m nA \<Otimes> B0) (1\<^sub>m nA \<Otimes> B1)
      (K x \<cdot>\<^sub>m (F x \<Otimes> S x)) =
      K x * CHSH_expect (A0 \<Otimes> 1\<^sub>m nB) (A1 \<Otimes> 1\<^sub>m nB) (1\<^sub>m nA \<Otimes> B0) 
      (1\<^sub>m nA \<Otimes> B1) (F x \<Otimes> S x)" 
      using car dec CHSH_expect_smult fc_mats_carrier by blast
  qed simp
  finally have "CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1) R =
    sum (\<lambda>a. K a * CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1)
      ((F a) \<Otimes> (S a))) {..< n}" .
  hence "\<bar>CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1) R\<bar> \<le>
    sum (\<lambda>a. \<bar>K a * CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1)
      ((F a) \<Otimes> (S a))\<bar>) {..< n}" using sum_abs_cpx by simp
  also have "... = sum (\<lambda>a. K a * \<bar>CHSH_expect (A0\<Otimes>1\<^sub>m nB) (A1\<Otimes>1\<^sub>m nB) 
    (1\<^sub>m nA\<Otimes>B0) (1\<^sub>m nA\<Otimes>B1) ((F a) \<Otimes> (S a))\<bar>) {..< n}"
  proof (rule sum.cong)
    fix x
    assume "x\<in> {..< n}"
    show "\<bar>complex_of_real (K x) *
      CHSH_expect (A0 \<Otimes> 1\<^sub>m nB) (A1 \<Otimes> 1\<^sub>m nB) (1\<^sub>m nA \<Otimes> B0) (1\<^sub>m nA \<Otimes> B1) 
      (F x \<Otimes> S x)\<bar> =
      complex_of_real (K x) * \<bar>CHSH_expect (A0 \<Otimes> 1\<^sub>m nB) (A1 \<Otimes> 1\<^sub>m nB) 
      (1\<^sub>m nA \<Otimes> B0) (1\<^sub>m nA \<Otimes> B1) (F x \<Otimes> S x)\<bar>" 
    proof (rule abs_mult_cpx)
      show "0 \<le> K x" 
        using \<open>x\<in> {..< n}\<close> props cpx_of_real_ge_0 
        unfolding separately_decomposes_def by simp 
    qed
  qed simp
  also have "... \<le> sum (\<lambda>a. complex_of_real (K a)* 2) {..< n}"
  proof (rule sum_mono)
    fix a
    assume "a\<in>{..< n}"
    have "\<bar>CHSH_expect (A0 \<Otimes> 1\<^sub>m nB) (A1 \<Otimes> 1\<^sub>m nB) (1\<^sub>m nA \<Otimes> B0) 
      (1\<^sub>m nA \<Otimes> B1) (F a \<Otimes> S a)\<bar> \<le> 2" 
    proof (rule CHSH_expect_tensor_leq)
      show "CHSH_cond_local nA nB A0 A1 B0 B1" using assms by simp
      show "F a \<in> carrier_mat nA nA" using props \<open>a\<in> {..< n}\<close>
        unfolding separately_decomposes_def by simp
      show "density_operator (F a)" using props \<open>a\<in> {..< n}\<close>
        unfolding separately_decomposes_def by simp
      show  "S a \<in> carrier_mat nB nB" using props \<open>a\<in> {..< n}\<close>
        unfolding separately_decomposes_def by simp
      show "density_operator (S a)" using props \<open>a\<in> {..< n}\<close>
        unfolding separately_decomposes_def by simp
    qed (auto simp add: separately_decomposes_carrier_pos[OF props])
    moreover have "0 \<le> complex_of_real (K a)" 
      using props \<open>a\<in> {..< n}\<close> unfolding separately_decomposes_def by simp
    ultimately show "complex_of_real (K a) *
         \<bar>CHSH_expect (A0 \<Otimes> 1\<^sub>m nB) (A1 \<Otimes> 1\<^sub>m nB) (1\<^sub>m nA \<Otimes> B0) 
        (1\<^sub>m nA \<Otimes> B1) (F a \<Otimes> S a)\<bar>
         \<le> complex_of_real (K a) * 2"
      using mult_left_mono by blast 
  qed
  also have "... = (sum (\<lambda>a. complex_of_real (K a)) {..< n}) * 2"
    by (metis sum_distrib_right)
  also have "... = 2" 
  proof -
    have "sum (\<lambda>a. complex_of_real (K a)) {..< n} = 1"  
      using props unfolding separately_decomposes_def
      by (metis  of_real_hom.hom_one of_real_hom.hom_sum)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

text \<open>When any of the pairs of observables used in the measurements commutes,
this value remains bounded by 2.\<close>
lemma CHSH_expect_commute_leq:
  assumes "CHSH_cond_hermit n A0 A1 B0 B1"
  and "R\<in> carrier_mat n n"
  and "density_operator R"
  and "0 < n"
  and "commutator A0 A1 = 0\<^sub>m n n \<or> commutator B0 B1 = 0\<^sub>m n n"
shows "\<bar>CHSH_expect A0 A1 B0 B1 R\<bar> \<le>  2"
proof -  
  have "cmod (CHSH_expect A0 A1 B0 B1 R) \<le> L2_op_nrm (CHSH_op A0 A1 B0 B1)"
    unfolding CHSH_expect_def
  proof (rule expect_val_L2_op_nrm[of _ n])
    show "CHSH_op A0 A1 B0 B1 \<in> carrier_mat n n" using assms CHSH_op_dim
      unfolding CHSH_cond_hermit_def CHSH_cond_def by auto
  qed (auto simp add: assms)
  also have "... = 2" using assms CHSH_op_commute_L2_op_nrm_eq by simp
  finally have "cmod (CHSH_expect A0 A1 B0 B1 R) \<le> 2" .
  moreover have "\<bar>CHSH_expect A0 A1 B0 B1 R\<bar> = 
    cmod (CHSH_expect A0 A1 B0 B1 R)"
    by (simp add: abs_complex_def)
  ultimately show ?thesis
    by (metis Reals_of_real abs_norm_cancel cpx_real_abs_eq 
        cpx_real_abs_leq of_real_numeral)
qed

text \<open>In the general case, this value is bounded by $2\cdot\sqrt{2}$.\<close>
lemma CHSH_expect_gen_leq:
  assumes "CHSH_cond_hermit n A0 A1 B0 B1"
  and "R\<in> carrier_mat n n"
  and "density_operator R"
  and "0 < n"
shows "\<bar>CHSH_expect A0 A1 B0 B1 R\<bar> \<le>  (2 * sqrt 2)"
proof -  
  have "cmod (CHSH_expect A0 A1 B0 B1 R) \<le> L2_op_nrm (CHSH_op A0 A1 B0 B1)"
    unfolding CHSH_expect_def
  proof (rule expect_val_L2_op_nrm[of _ n])
    show "CHSH_op A0 A1 B0 B1 \<in> carrier_mat n n" using assms CHSH_op_dim
      unfolding CHSH_cond_hermit_def CHSH_cond_def by auto
  qed (auto simp add: assms)
  also have "... \<le> 2 * sqrt 2" using assms CHSH_op_L2_op_nrm_le by simp
  finally have "cmod (CHSH_expect A0 A1 B0 B1 R) \<le> 2 * sqrt 2" .
  moreover have "\<bar>CHSH_expect A0 A1 B0 B1 R\<bar> = 
    cmod (CHSH_expect A0 A1 B0 B1 R)"
    by (simp add: abs_complex_def)
  ultimately show ?thesis
    by (metis Reals_of_real abs_norm_cancel cpx_real_abs_eq cpx_real_abs_leq)
qed

text \<open>The bound $2\cdot\sqrt{2}$ can be reached by a suitable choice of observables, when the
Bell state is measured.\<close>
lemma CHSH_expect_limit:
shows "\<bar>CHSH_expect Z_I X_I I_ZmX I_XpZ  rho_psim\<bar> = 2 * sqrt 2"
proof -
  define fc::"complex Matrix.mat set" where "fc = carrier_mat 4 4"
  interpret bin_cpx 4 4 fc 
  proof 
    show "0 < (4::nat)"  by simp
  qed (auto simp add: fc_def)
  have "CHSH_expect Z_I X_I I_ZmX I_XpZ rho_psim =
    Complex_Matrix.trace (Z_I * I_XpZ * rho_psim) - 
    Complex_Matrix.trace (Z_I * I_ZmX * rho_psim) +
    Complex_Matrix.trace (X_I * I_ZmX * rho_psim) +
    Complex_Matrix.trace (X_I * I_XpZ * rho_psim)" 
    using CHSH_expect_expand I_XpZ_carrier I_ZmX_carrier X_I_carrier 
      Z_I_carrier rho_psim_carrier by blast
  also have "... = complex_of_real (1 / sqrt 2) -
    complex_of_real (- 1 / sqrt 2) +
    complex_of_real (1 / sqrt 2) +
    complex_of_real (1 / sqrt 2)"
    using X_XpZ_rho_trace X_ZmX_rho_trace Z_XpZ_rho_trace Z_ZmX_rho_trace 
    by presburger 
  also have "... = 2 * sqrt 2"
    using real_sqrt_divide two_div_sqrt_two by force
  finally have c: "CHSH_expect Z_I X_I I_ZmX I_XpZ rho_psim = 2 * sqrt 2" . 
  have "\<bar>CHSH_expect Z_I X_I I_ZmX I_XpZ rho_psim\<bar> =
    \<bar>Re (CHSH_expect Z_I X_I I_ZmX I_XpZ rho_psim)\<bar>"
    by (metis Re_complex_of_real Reals_of_real c cpx_real_abs_eq)
  thus ?thesis using c by simp
qed

end