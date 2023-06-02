(*
Author: 
  Mnacho Echenim, Université Grenoble Alpes
  Mehdi Mhalla, Université Grenoble Alpes
  Coraline Mori, Grenoble INP-Ensimag, UGA
*)

theory Density_Matrix_Basics 
  imports 
    Matrix_L2_Operator_Norm
begin

section \<open>On density matrices\<close>

subsection \<open>Density matrix characterization\<close>
text \<open>Density matrices are defined as positive operators with trace 1, we prove in this
section that they are exactly the convex combinations of pure states.\<close>

lemma (in cpx_sq_mat) mixed_state_density_operator:
  assumes "\<And>i. i \<in> {..< (n::nat)} \<Longrightarrow> 0 \<le> p i"
  and "sum p {..< n} = 1"
  and "\<And>i. i  \<in> {..< n} \<Longrightarrow> dim_vec (v i) = dimR"
  and "\<And>i. i  \<in> {..< n} \<Longrightarrow> \<parallel>v i\<parallel> = 1"
shows "density_operator (sum_mat (\<lambda> i. (p i)  \<cdot>\<^sub>m (rank_1_proj (v i))) {..< n})"
  unfolding density_operator_def
proof
  have car: "\<And>i. i \<in> {..< n} \<Longrightarrow> rank_1_proj (v i) \<in> fc_mats" 
    using assms rank_1_proj_carrier fc_mats_carrier dim_eq
    by metis
  show "Complex_Matrix.positive (sum_mat (\<lambda>i. p i \<cdot>\<^sub>m rank_1_proj (v i)) 
    {..< n})"
  proof (rule sum_mat_positive)
    show "finite {..< n}" by simp
    show "\<And>i. i \<in> {..< n} \<Longrightarrow> p i \<cdot>\<^sub>m rank_1_proj (v i) \<in> fc_mats" using car
      by (simp add: cpx_sq_mat_smult) 
    show "\<And>i. i \<in> {..< n} \<Longrightarrow> Complex_Matrix.positive (p i \<cdot>\<^sub>m rank_1_proj (v i))"
    proof -
      fix i
      assume "i\<in> {..< n}"
      show "Complex_Matrix.positive (p i \<cdot>\<^sub>m rank_1_proj (v i))"
      proof (rule positive_smult)
        show  "Complex_Matrix.positive (rank_1_proj (v i))" using \<open>i\<in> {..< n}\<close>
          by (simp add: assms rank_1_proj_positive)
        show "0 \<le> p i" using assms \<open>i\<in> {..< n}\<close> by simp
        show "rank_1_proj (v i) \<in> carrier_mat dimR dimR" 
          using \<open>i\<in> {..< n}\<close> car fc_mats_carrier dim_eq by simp
      qed
    qed
  qed
  have "Complex_Matrix.trace (sum_mat (\<lambda>i. p i \<cdot>\<^sub>m rank_1_proj (v i)) {..< n})= 
    sum (\<lambda>i. Complex_Matrix.trace (p i \<cdot>\<^sub>m rank_1_proj (v i))) {..< n}"
  proof (rule trace_sum_mat)
    show "finite {..< n}" by simp 
    show "\<And>i. i \<in> {..< n} \<Longrightarrow> p i \<cdot>\<^sub>m rank_1_proj (v i) \<in> fc_mats" using car
      by (simp add: cpx_sq_mat_smult) 
  qed
  also have "... = sum (\<lambda>i. p i * Complex_Matrix.trace (rank_1_proj (v i))) 
    {..< n}"
  proof (rule sum.cong)
    fix i
    assume "i\<in>{..< n}" 
    show "Complex_Matrix.trace (p i \<cdot>\<^sub>m rank_1_proj (v i)) = 
      p i * Complex_Matrix.trace (rank_1_proj (v i))"
    proof (rule trace_smult)
      show "rank_1_proj (v i) \<in> carrier_mat dimR dimR" 
        using \<open>i\<in> {..< n}\<close> car fc_mats_carrier dim_eq by simp
    qed
  qed simp
  also have "... = sum (\<lambda>i. p i) {..< n}"
  proof (rule sum.cong)
    fix i
    assume "i\<in>{..< n}"
    thus "p i * Complex_Matrix.trace (rank_1_proj (v i)) = p i" 
      using assms rank_1_proj_trace by simp
  qed simp
  also have "... = 1" using assms by simp
  finally show "Complex_Matrix.trace 
    (sum_mat (\<lambda>i. p i \<cdot>\<^sub>m rank_1_proj (v i)) {..< n}) = 1" .
qed

lemma (in cpx_sq_mat) density_operator_mixed_state:
  assumes "R\<in> fc_mats"
  and "density_operator R"
shows "\<exists> p v (n::nat). (\<forall>i\<in>{..< n}. 0 \<le> p i) \<and> 
  (\<forall>i \<in> {..< n}. dim_vec (v i) = dimR) \<and>
  (\<forall>i \<in> {..< n}. \<parallel>v i\<parallel> = 1) \<and> (sum p {..< n} = 1) \<and> 
  (R = sum_mat (\<lambda> i. (p i)  \<cdot>\<^sub>m (rank_1_proj (v i))) {..< n})"
proof -
  have "R\<in> carrier_mat dimR dimR" using assms fc_mats_carrier dim_eq by simp
  have "0 < dimR" using npos .
  moreover have "hermitian R" using assms positive_is_hermitian 
    unfolding density_operator_def by simp
  moreover have "R\<in> carrier_mat dimR dimR" using assms fc_mats_carrier dim_eq 
    by simp
  ultimately obtain B U where rdd: "real_diag_decomp R B U" 
    using hermitian_real_diag_decomp by blast
  hence "unitary_diag R B U" by simp
  hence "dim_row B = dimR"
    using assms dim_eq fc_mats_carrier unitary_diag_carrier(1) by blast 
  define p where "p = (\<lambda>i. diag_mat B!i)"
  define v where "v = (\<lambda>i. Matrix.col U i)"
  have "\<forall>i\<in>{..< dimR}. 0 \<le> p i" 
  proof
    fix i
    assume "i \<in> {..< dimR}"
    have "0 \<le> B$$(i,i)" 
    proof (rule positive_unitary_diag_pos)
      show "R\<in> carrier_mat dimR dimR" using \<open>R \<in> carrier_mat dimR dimR\<close> .
      show "Complex_Matrix.positive R" 
        using  assms unfolding density_operator_def by simp
      show "unitary_diag R B U" using rdd by simp
      show "i < dimR" using \<open>i\<in> {..< dimR}\<close> by simp
    qed
    also have "... = p i" 
      using \<open>dim_row B = dimR\<close> \<open>i\<in> {..< dimR}\<close> 
      unfolding p_def diag_mat_def by simp
    finally show "0 \<le> p i" .
  qed
  moreover have "\<forall>i \<in> {..< dimR}. dim_vec (v i) = dimR"
    using \<open>unitary_diag R B U\<close> assms(1) dim_col dim_eq fc_mats_carrier 
      unitary_diag_carrier(2) v_def by blast
  moreover have "\<forall>i \<in> {..< dimR}. \<parallel>v i\<parallel> = 1" 
  proof
    fix i
    assume "i \<in> {..< dimR}"
    show "\<parallel>v i\<parallel> = 1" unfolding v_def
    proof (rule unitary_col_norm)
      show "i < dimR" using \<open>i\<in> {..< dimR}\<close> by simp
      show "Complex_Matrix.unitary U" 
        using rdd \<open>unitary_diag R B U\<close> unitary_diagD(3) by blast
      show "U \<in> carrier_mat dimR dimR"
        using \<open>R \<in> carrier_mat dimR dimR\<close> \<open>unitary_diag R B U\<close> 
          unitary_diag_carrier(2) by auto
    qed
  qed
  moreover have "sum p {..< dimR} = 1" using unitarily_equiv_trace'
  proof-
    have "sum p {..< dimR} = (\<Sum>i = 0..<dim_row R. B $$ (i, i))"
    proof (rule sum.cong)
      show "{..<dimR} = {0..<dim_row R}"
        using \<open>R \<in> carrier_mat dimR dimR\<close> by auto 
      show "\<And>x. x \<in> {0..<dim_row R} \<Longrightarrow> p x = B $$ (x, x)"
        using \<open>dim_row B = dimR\<close> \<open>R \<in> carrier_mat dimR dimR\<close> 
        unfolding p_def diag_mat_def by auto
    qed
    also have "... = Complex_Matrix.trace R" 
      using unitarily_equiv_trace' \<open>R \<in> carrier_mat dimR dimR\<close>
      by (metis \<open>unitary_diag R B U\<close> unitary_diag_imp_unitarily_equiv) 
    also have "... = 1" using assms unfolding density_operator_def by simp
    finally show ?thesis .
  qed
  moreover have "R = sum_mat (\<lambda> i. (p i)  \<cdot>\<^sub>m (rank_1_proj (v i))) {..< dimR}" 
    unfolding p_def v_def 
  proof  (rule sum_decomp_cols[symmetric])
    show "R\<in> fc_mats" using assms by simp
    show "unitary_diag R B U" using \<open>unitary_diag R B U\<close> .
    show "hermitian R" using assms positive_is_hermitian 
      unfolding density_operator_def by simp
  qed
  ultimately show ?thesis by auto
qed

lemma (in cpx_sq_mat) density_operator_iff_mixed_state:
  assumes "R\<in> fc_mats"
  shows "density_operator R \<longleftrightarrow> 
    (\<exists> p v (n::nat). (\<forall>i\<in>{..< n}. 0 \<le> p i) \<and> 
      (\<forall>i \<in> {..< n}. dim_vec (v i) = dimR) \<and>
      (\<forall>i \<in> {..< n}. \<parallel>v i\<parallel> = 1) \<and> (sum p {..< n} = 1) \<and> 
      (R = sum_mat (\<lambda> i. (p i)  \<cdot>\<^sub>m (rank_1_proj (v i))) {..< n}))" (is "?L \<longleftrightarrow> ?R")
proof
  show "?L \<Longrightarrow> ?R" using density_operator_mixed_state[OF  assms] by simp
next
  show "?R \<Longrightarrow> ?L" 
  proof -
    assume "\<exists>p v (n::nat). (\<forall>i\<in>{..<n}. 0 \<le> p i) \<and>
       (\<forall>i\<in>{..<n}. dim_vec (v i) = dimR) \<and> (\<forall>i\<in>{..<n}. \<parallel>v i\<parallel> = 1) \<and> 
      sum p {..<n} = 1 \<and> R = sum_mat (\<lambda>i. p i \<cdot>\<^sub>m rank_1_proj (v i)) {..<n}"
    from this obtain n p v where "\<And>i. i\<in>{..<(n::nat)} \<Longrightarrow> 0 \<le> p i" and 
      "\<forall>i\<in>{..<n}. dim_vec (v i) = dimR" and "\<forall>i\<in>{..<n}. \<parallel>v i\<parallel> = 1" and 
      "sum p {..<n} = 1" and 
      "R = sum_mat (\<lambda>i. p i \<cdot>\<^sub>m rank_1_proj (v i)) {..<n}" by auto note npv = this
    thus "density_operator R" using npv mixed_state_density_operator by auto 
  qed
qed
  

subsection \<open>Separable density matrices\<close>

text \<open>We define the notion of a separable density matrix: this is a matrix of the form
$\sum_{i = 1}^n p_i \rho^i_A\otimes \rho^i_B$, where the $p_i$s are positive and sum
up to 1. \<close>

definition separately_decomposes where
"separately_decomposes R (n::nat) nA nB K F S \<equiv> 
   (\<forall>a< n. (0::complex) \<le> (complex_of_real (K a)) \<and> 
     F a\<in> carrier_mat nA nA \<and> S a \<in> carrier_mat nB nB \<and>
    density_operator (F a) \<and> density_operator (S a)) \<and> 0 < nA * nB \<and>
    sum K {..< n} = 1 \<and> R = fixed_carrier_mat.sum_mat (nA * nB) (nA * nB) 
      (\<lambda>a. K a \<cdot>\<^sub>m ((F a) \<Otimes> (S a))) {..< n}"

definition separable_density where
"separable_density nA nB R \<equiv> 
  \<exists> (n::nat) K F S. separately_decomposes R n nA nB K F S"

lemma separately_decomposes_carrier:
  assumes "separately_decomposes R (n::nat) nA nB K F S"
  and "0 < nA"
  and "0 < nB"
shows "R \<in> carrier_mat (nA*nB) (nA*nB)"
proof -
  define fc::"complex Matrix.mat set" 
  where "fc = carrier_mat (nA * nB) (nA * nB)"
  interpret cpx_sq_mat "nA * nB" "nA * nB" fc
  proof
    show "fc = carrier_mat (nA * nB) (nA * nB)" using fc_def by simp
    show "0 < nA * nB" using assms unfolding separately_decomposes_def 
      by simp
  qed simp
  have  car: "\<And>a. a \<in> {..<n} \<Longrightarrow> F a \<Otimes> S a \<in> fc"
  proof -
    fix a
    assume "a\<in> {..< n}"
    hence "F a \<in> carrier_mat nA nA" "S a\<in> carrier_mat nB nB" 
      using assms unfolding separately_decomposes_def by auto
    thus "F a \<Otimes> S a \<in> fc" using tensor_mat_carrier unfolding fc_def
      by (metis carrier_matD(1) carrier_matD(2)) 
  qed 
  have "R = sum_mat (\<lambda>a. K a \<cdot>\<^sub>m ((F a) \<Otimes> (S a))) {..< n}"
    using assms unfolding separately_decomposes_def by simp
  also have "...\<in> carrier_mat (nA*nB) (nA*nB)"
  proof (rule sum_mat_carrier)
    show "\<And>i. i \<in> {..<n} \<Longrightarrow> K i \<cdot>\<^sub>m (F i \<Otimes> S i) \<in> fc" using car
      by (simp add: smult_mem)
  qed
  finally show ?thesis .
qed

lemma separately_decomposes_carrier_pos:
  assumes "separately_decomposes R n nA nB K F S"
  shows "0 < nA" "0 < nB" 
  using assms unfolding separately_decomposes_def by auto

lemma separable_density_carrier:
  assumes "separable_density nA nB R"
  and "0 < nA"
  and "0 < nB"
shows "R \<in> carrier_mat (nA*nB) (nA*nB)"
proof -
  have "\<exists>n K F S. separately_decomposes R n nA nB K F S"
    using assms unfolding separable_density_def by simp
  from this obtain n K F S where 
    "separately_decomposes R n nA nB K F S" by auto 
  note props = this  
  thus ?thesis using separately_decomposes_carrier assms by simp
qed
 
lemma separately_decomposes_trace:
  assumes "separately_decomposes R n nA nB K F S"
  shows "Complex_Matrix.trace R = 1"
proof -
  define fc::"complex Matrix.mat set" 
    where "fc = carrier_mat (nA * nB) (nA * nB)"
  interpret cpx_sq_mat "nA * nB" "nA * nB" fc
  proof
    show "fc = carrier_mat (nA * nB) (nA * nB)" using fc_def by simp
    show "0 < nA * nB" using assms unfolding separately_decomposes_def 
      by simp
  qed simp
  have  car: "\<And>a. a \<in> {..<n} \<Longrightarrow> F a \<Otimes> S a \<in> fc"
  proof -
    fix a
    assume "a\<in> {..< n}"
    hence "F a \<in> carrier_mat nA nA" "S a\<in> carrier_mat nB nB" 
      using assms unfolding separately_decomposes_def by auto
    thus "F a \<Otimes> S a \<in> fc" using tensor_mat_carrier unfolding fc_def
      by (metis carrier_matD(1) carrier_matD(2)) 
  qed 
  have adev: "\<forall>a < n. Complex_Matrix.trace (K a \<cdot>\<^sub>m ((F a) \<Otimes> (S a))) =
    K a * (Complex_Matrix.trace (F a) * Complex_Matrix.trace (S a))" 
  proof (intro allI impI)
    fix a
    assume "a < n"
    have "Complex_Matrix.trace (K a \<cdot>\<^sub>m ((F a) \<Otimes> (S a))) =
      K a * Complex_Matrix.trace ((F a) \<Otimes> (S a))" 
    proof (rule trace_smult) 
      show "F a \<Otimes> S a \<in> carrier_mat (nA * nB) (nA * nB)" using car \<open>a < n\<close>
        by (simp add: fc_def)
    qed
    also have "... = K a * (Complex_Matrix.trace (F a) * 
      Complex_Matrix.trace (S a))"
    proof -
      have "Complex_Matrix.trace ((F a) \<Otimes> (S a)) = 
        Complex_Matrix.trace (F a) * Complex_Matrix.trace (S a)"
        using tensor_mat_trace assms unfolding separately_decomposes_def
        by (meson \<open>a < n\<close> nat_0_less_mult_iff)
      thus ?thesis by simp
    qed
    finally show "Complex_Matrix.trace (K a \<cdot>\<^sub>m ((F a) \<Otimes> (S a))) =
      K a * (Complex_Matrix.trace (F a) * Complex_Matrix.trace (S a))" .
  qed
  have "Complex_Matrix.trace R = 
    Complex_Matrix.trace (sum_mat (\<lambda>a. K a \<cdot>\<^sub>m ((F a) \<Otimes> (S a))) {..< n})"
    using assms unfolding separately_decomposes_def by simp
  also have "... = 
    sum (\<lambda>a. Complex_Matrix.trace (K a \<cdot>\<^sub>m ((F a) \<Otimes> (S a)))) {..< n}"    
  proof (rule trace_sum_mat)
    show "\<And>a. a \<in> {..<n} \<Longrightarrow> K a \<cdot>\<^sub>m (F a \<Otimes> S a) \<in> fc" 
      using car cpx_sq_mat_smult by auto 
  qed simp
  also have "... = 
    sum (\<lambda>a. K a * (Complex_Matrix.trace (F a)* Complex_Matrix.trace (S a))) 
      {..< n}" using adev by simp
  also have "... = sum (\<lambda>a. K a) {..< n}" 
  proof -
    have "\<forall>a < n. Complex_Matrix.trace (F a)* Complex_Matrix.trace (S a) = 1"
    proof (intro allI impI)
      fix a
      assume "a < n"
      thus "Complex_Matrix.trace (F a) * Complex_Matrix.trace (S a) = 1"
        using assms unfolding separately_decomposes_def  
        by (metis density_operator_def lambda_one) 
    qed
    thus ?thesis by simp
  qed
  also have "... = 1" using assms unfolding separately_decomposes_def  
    by simp
  finally show ?thesis .
qed

lemma separately_decomposes_positive:
  assumes "separately_decomposes R  n nA nB K F S"
  and "0 < nA"
  and "0 < nB"
  shows "Complex_Matrix.positive R"
proof -
  define fc::"complex Matrix.mat set" 
    where "fc = carrier_mat (nA * nB) (nA * nB)"
  interpret cpx_sq_mat "nA * nB" "nA * nB" fc
  proof
    show "fc = carrier_mat (nA * nB) (nA * nB)" using fc_def by simp
    show "0 < nA * nB" using assms unfolding separately_decomposes_def 
      by simp
  qed simp
  have ac: "\<forall>a\<in>{..<n}.(F a \<Otimes> S a) \<in> fc"
  proof
    fix a
    assume "a\<in> {..< n}"
    hence "F a \<in> carrier_mat nA nA" "S a\<in> carrier_mat nB nB" 
      using assms unfolding separately_decomposes_def by auto
    thus "F a \<Otimes> S a \<in> fc" using tensor_mat_carrier unfolding fc_def
      by (metis carrier_matD(1) carrier_matD(2))
  qed
  have "Complex_Matrix.positive (sum_mat (\<lambda>a. K a\<cdot>\<^sub>m(F a \<Otimes> (S a))) {..< n})"
  proof (rule sum_mat_positive)
    show "\<And>a. a\<in>{..<n} \<Longrightarrow> K a \<cdot>\<^sub>m (F a \<Otimes> S a) \<in> fc" 
      using ac by (simp add: cpx_sq_mat_smult)
    show "\<And>i. i\<in>{..<n} \<Longrightarrow> Complex_Matrix.positive (K i \<cdot>\<^sub>m (F i \<Otimes> S i))"
    proof -
      fix i
      assume "i \<in> {..< n}"
      show "Complex_Matrix.positive (K i \<cdot>\<^sub>m (F i \<Otimes> S i))"
      proof (rule positive_smult)
        show "F i \<Otimes> S i \<in> carrier_mat (nA*nB) (nA*nB)" 
          using \<open>i \<in> {..< n}\<close> ac fc_def by simp
        show "0 \<le> complex_of_real (K i)" using \<open>i \<in> {..< n}\<close> assms 
          unfolding separately_decomposes_def by simp
        show "Complex_Matrix.positive (F i \<Otimes> S i)"
        proof (rule tensor_mat_positive)
          show "0 < nA" using assms by simp
          show "0 < nB" using assms by simp
          show "F i \<in> carrier_mat nA nA" using \<open>i \<in> {..< n}\<close> assms
            unfolding separately_decomposes_def by simp
          show "S i \<in> carrier_mat nB nB" using \<open>i \<in> {..< n}\<close> assms
            unfolding separately_decomposes_def by simp
          show "Complex_Matrix.positive (F i)" using \<open>i \<in> {..< n}\<close> assms
            unfolding separately_decomposes_def density_operator_def by simp
          show "Complex_Matrix.positive (S i)" using \<open>i \<in> {..< n}\<close> assms
            unfolding separately_decomposes_def density_operator_def by simp
        qed
      qed
    qed
  qed simp
  thus ?thesis using assms unfolding separately_decomposes_def by simp
qed

text \<open>A separable density matrix is indeed a density matrix:\<close>

lemma separable_density_operator:
  assumes "separable_density nA nB R"
  and "0 < nA"
  and "0 < nB"
  shows "density_operator R" unfolding density_operator_def
proof 
  have "\<exists>n K F S. separately_decomposes R n nA nB K F S"
    using assms unfolding separable_density_def by simp
  from this obtain n K F S where 
    "separately_decomposes R n nA nB K F S" by auto 
  note props = this
  show "Complex_Matrix.positive R" 
    using assms props separately_decomposes_positive
    by metis
  show "Complex_Matrix.trace R = 1" using props separately_decomposes_trace
    by metis
qed


subsection \<open>Characterization of pure states\<close>

text \<open>A density matrix represents a pure state if it is the rank 1 projection of a single 
vector. These can be characterized either as the density matrices with a square of trace 1,
or as the density matrices that are projectors.\<close>

definition pure_density_operator where
"pure_density_operator R \<equiv> (\<exists> v. R = rank_1_proj v)"

lemma density_pure_single_diag:
  assumes "A \<in> carrier_mat n n"
  and "Complex_Matrix.trace A = (1::real)"
  and "Complex_Matrix.trace (A*A) = (1::real)"
  and "unitary_diag A B U"
  and "I = {0 ..< n}"
  and "\<forall>i\<in>I. A $$ (i,i) \<ge> 0" 
  and "\<forall>i\<in>I. B $$ (i,i) \<ge> 0"
shows "\<exists>j\<in>I. B $$ (j,j) = 1 \<and> (\<forall>i \<in> I-{j}. B $$ (i,i) = 0)"
proof -
  have "(\<Sum> i\<in>I. B $$ (i,i)) = 1" 
    using assms by (smt (verit, best) carrier_matD(1) 
        sum.cong unitarily_equiv_trace' unitary_diag_imp_unitarily_equiv)
  also have "(\<Sum> i\<in>I. (B $$ (i,i) * B $$ (i,i))) = 1" 
    using assms squared_A_trace'[of A] by simp
  hence "\<exists>j\<in>I. B $$ (j,j) = 1" using assms pos_square_1_elem[of I "\<lambda>x.(B $$ (x, x))"]
    using calculation by blast
  from this obtain j where "j\<in>I" and "B $$ (j,j) = 1" by auto
  hence "\<forall>i \<in> (I-{j}). B $$ (i,i) = 0" 
    using assms sum_eq_elmt[of I "\<lambda>x.(B $$ (x, x))" 1 j]
    using calculation by blast
  thus "\<exists>j\<in>I. B $$ (j,j) = 1 \<and> (\<forall>i \<in> I-{j}. B $$ (i,i) = 0)"
    using \<open>B $$ (j, j) = 1\<close> \<open>j \<in> I\<close> by blast
qed

lemma rank_1_proj_square_trace:
  fixes v::"complex Matrix.vec"
  assumes "A = rank_1_proj v"
  shows "Complex_Matrix.trace (A*A) = \<parallel>v\<parallel>\<^sup>2 * Complex_Matrix.trace A"
proof -
  have "Complex_Matrix.trace (A*A) =
    Complex_Matrix.trace ((rank_1_proj v) * rank_1_proj v)"
    using assms by simp
  also have "... = Complex_Matrix.trace ((inner_prod v v) \<cdot>\<^sub>m (outer_prod v v))"
    using outer_prod_mult_outer_prod
    unfolding rank_1_proj_def
    by (metis carrier_vec_dim_vec)
  also have "... = (inner_prod v v) * Complex_Matrix.trace (outer_prod v v)"
    by (metis rank_1_proj_carrier rank_1_proj_def trace_smult)
  also have "... = \<parallel>v\<parallel>\<^sup>2 * Complex_Matrix.trace (outer_prod v v)"
    using cmod_rvec_norm inner_prod_rvec_norm_pow2
      inner_prod_vec_norm_pow2 vec_norm_sq_cpx_vec_length_sq by presburger
  also have "... = \<parallel>v\<parallel>\<^sup>2 * Complex_Matrix.trace A"
    using assms unfolding rank_1_proj_def by simp
  finally show ?thesis .
qed

lemma rank_1_proj_trace':
  assumes "Complex_Matrix.trace (rank_1_proj v) = 1"
  shows "\<parallel>v\<parallel> = 1"
proof -
  have "Complex_Matrix.trace (rank_1_proj v) = inner_prod v v" using trace_outer_prod 
    unfolding rank_1_proj_def using carrier_vecI by blast
  also have "... = (vec_norm v)\<^sup>2" unfolding vec_norm_def using power2_csqrt by presburger
  also have "... = \<parallel>v\<parallel>\<^sup>2" using vec_norm_sq_cpx_vec_length_sq by simp
  finally have "... = 1" using assms by simp
  thus "\<parallel>v\<parallel> = 1"
    by (metis cmod_vec_norm norm_neg_numeral numeral_One of_real_hom.hom_1_iff 
        of_real_hom.hom_uminus one_neq_neg_one power2_eq_1_iff 
        vec_norm_eq_cpx_vec_length) 
qed

lemma density_square_pure:
  assumes "A \<in> carrier_mat n n"
  and "0 < n"
  and "density_operator A"
  and "Complex_Matrix.trace (A*A) = 1"
shows "pure_density_operator A"
proof -
  define fc::"complex Matrix.mat set" where "fc = carrier_mat n n"
  interpret cpx_sq_mat n n fc
  proof 
    show "fc = carrier_mat n n" unfolding fc_def by simp
    show "0 < n" using assms by simp
  qed simp
  have her:"hermitian A" using assms hermitian_def positive_is_hermitian
    by (simp add: density_operator_def)
  from this obtain B U where uni:"real_diag_decomp A B U"
    using assms hermitian_real_diag_decomp[of A]
    by (smt (verit, best) hermitian_decomp_decomp' hermitian_schur_decomp)
  have exj:"\<exists>j<dim_row A. B $$ (j,j) = 1 \<and> (\<forall>i<dim_row A. i\<noteq>j \<longrightarrow> B $$ (i,i) = 0)"
  proof (rule positive_square_trace)
    show "A \<in> carrier_mat (dim_row A) (dim_row A)"
      by (simp add: \<open>hermitian A\<close> hermitian_square)
    show "Complex_Matrix.trace A = complex_of_real 1"
      using assms density_operator_def by simp
    show "Complex_Matrix.trace (A * A) = 1"
      using assms by simp
    show "real_diag_decomp A B U"
      by (simp add: \<open>real_diag_decomp A B U\<close>)
    show "Complex_Matrix.positive A"
      using assms density_operator_def by simp
    show "0 < dim_row A" using assms npos
      by (metis carrier_matD(1))
  qed
  from this obtain j where jdim:"j<dim_row A" and j1:"B $$ (j,j) = 1"
    and ji0:"(\<forall>i<dim_row A. i\<noteq>j \<longrightarrow> B $$ (i,i) = 0)" by auto
  have "dim_row B = dim_row A" using \<open>real_diag_decomp A B U\<close>
        unitarily_equivD real_diag_decomp_def similar_mat_wit_dim_row 
           unitary_diag_imp_unitarily_equiv by blast
  hence "diag_mat B ! j = 1" using j1 jdim
    unfolding diag_mat_def
    by simp
  have insj:"{..< dim_row A} = insert j ({..< dim_row A}-{j})"
    using jdim by blast
  have "A = sum_mat (\<lambda>i. (diag_mat B ! i) \<cdot>\<^sub>m rank_1_proj (Matrix.col U i))
      {..< dim_row A}"
    using assms sum_decomp_cols \<open>hermitian A\<close> real_diag_decompD(1)
    by (simp add: \<open>real_diag_decomp A B U\<close> fc_mats_carrier)
  also have "... = (diag_mat B ! j) \<cdot>\<^sub>m rank_1_proj (Matrix.col U j)"
  proof (rule sum_mat_singleton)
    have "\<And>i. i < dim_row A \<Longrightarrow> rank_1_proj (Matrix.col U i) \<in> fc"
    proof -
      fix i
      assume "i<dim_row A"
      have "dim_vec (Matrix.col U i) = n" using \<open>real_diag_decomp A B U\<close> assms
        by (metis carrier_matD(1) dim_col fc_mats_carrier 
            real_diag_decompD(1) unitary_diag_carrier(2))
      thus "rank_1_proj (Matrix.col U i) \<in> fc" using rank_1_proj_carrier
          fc_mats_carrier dim_eq
        by blast
    qed
    thus "(\<lambda>i. rank_1_proj (Matrix.col U i)) ` {..<dim_row A} \<subseteq> fc" by auto
    show "\<forall>i\<in>{..<dim_row A}. i \<noteq> j \<longrightarrow> diag_mat B ! i = 0"
    proof (intro ballI impI) 
      fix i
      assume"i\<in> {..<dim_row A}"
      and "i \<noteq> j"
      have "diag_mat B ! i = B $$ (i,i)" using \<open>i\<in> {..<dim_row A}\<close> 
          \<open>dim_row B = dim_row A\<close>
        unfolding diag_mat_def by simp
      thus "diag_mat B ! i = 0" using \<open>i\<noteq>j\<close> ji0
        using \<open>i \<in> {..<dim_row A}\<close> by simp
    qed
  qed (auto simp add: jdim)
  also have "... = rank_1_proj (Matrix.col U j)"
    using \<open>diag_mat B ! j = 1\<close> by auto
  finally have "A = rank_1_proj (Matrix.col U j)" .
  thus "pure_density_operator A" 
    unfolding pure_density_operator_def by auto
qed

lemma density_square_pure':
  assumes "density_operator A"
  and "A = rank_1_proj v"
shows "Complex_Matrix.trace (A*A) = 1"
proof -
  have "Complex_Matrix.trace (A*A) = \<parallel>v\<parallel>\<^sup>2 * Complex_Matrix.trace A"
    using assms by (simp add: rank_1_proj_square_trace)
  also have "... = Complex_Matrix.trace A"
    using rank_1_proj_trace' assms unfolding density_operator_def
    by simp
  also have "... = 1" using assms unfolding density_operator_def
    by simp
  finally show ?thesis by auto
qed 

lemma 
  assumes "A\<in> carrier_mat n n"
  and "0 < n"
  and "density_operator A"
shows pure_density_charact: 
  "(pure_density_operator A) \<longleftrightarrow> (Complex_Matrix.trace (A*A) = 1)"
and pure_density_charact': 
  "(pure_density_operator A) \<longleftrightarrow> (A*A = A)"
proof -
  show "(pure_density_operator A) \<longleftrightarrow> (Complex_Matrix.trace (A*A) = 1)"
  using assms density_square_pure density_square_pure' 
    pure_density_operator_def[of A] by auto
next
  show "(pure_density_operator A) \<longleftrightarrow> (A*A = A)"
  proof
    assume "pure_density_operator A"
    hence "\<exists>v. A = rank_1_proj v" unfolding pure_density_operator_def by simp
    from this obtain v where "A = rank_1_proj v" by auto
    have "1 = Complex_Matrix.trace A" 
      using assms unfolding density_operator_def by simp
    also have "... = \<parallel>v\<parallel>\<^sup>2" using trace_rank_1_proj \<open>A = rank_1_proj v\<close> by simp
    finally have "\<parallel>v\<parallel> = 1"
      by (simp add: \<open>1 = Complex_Matrix.trace A\<close> \<open>A = rank_1_proj v\<close> 
          rank_1_proj_trace') 
    thus "A*A = A" using rank_1_proj_projector \<open>A = rank_1_proj v\<close> 
      unfolding projector_def by simp
  next
    assume "A*A = A"
    hence "Complex_Matrix.trace (A*A) = Complex_Matrix.trace A" by simp
    also have "... = 1" using assms unfolding density_operator_def by simp
    finally have "Complex_Matrix.trace (A*A) = 1" .
    thus "pure_density_operator A" using assms density_square_pure by simp
  qed
qed

section \<open>Quantum expectation values and traces\<close>

text \<open>The expectation value of a projective measurement is the average outcome value of
the measurement, where each outcome value is weighted by the probability that it occurs.
We show that the expectation value of a density matrix $\rho$ for an observable represented
by the Hermitian matrix $A$ is $\mathrm{Tr}(A\cdot\rho)$.\<close>

definition (in cpx_sq_mat) expect_value where
"expect_value R p M = 
  sum (\<lambda>i. meas_outcome_prob R M i * (meas_outcome_val (M i))) {..< p}"

definition (in cpx_sq_mat) obs_expect_value where
"obs_expect_value R A = 
  expect_value R (proj_meas_size (make_pm A)) (proj_meas_outcomes (make_pm A))"

lemma (in cpx_sq_mat) expect_value_trace:
  assumes "proj_measurement p M"
  and "R\<in> fc_mats"
shows "expect_value R p M = 
  Complex_Matrix.trace (sum_mat 
    (\<lambda>i. meas_outcome_val (M i)\<cdot>\<^sub>m (meas_outcome_prj (M i))) {..< p} * R)"
proof -
  have car: "\<And>i. i < p \<Longrightarrow> meas_outcome_prj (M i) * R \<in> fc_mats" 
    using assms unfolding proj_measurement_def
    using cpx_sq_mat_mult by auto
  have "expect_value R p M = sum (\<lambda>i. meas_outcome_val (M i) * 
    (Complex_Matrix.trace( R* meas_outcome_prj (M i)))) {..< p}" 
    unfolding expect_value_def meas_outcome_prob_def
    by (simp add: mult.commute)
  also have "... = sum (\<lambda>i. meas_outcome_val (M i) * 
    (Complex_Matrix.trace(meas_outcome_prj (M i) * R))) {..< p}"
  proof -
    have "\<And>i. i < p \<Longrightarrow>  Complex_Matrix.trace (R * meas_outcome_prj (M i)) = 
      Complex_Matrix.trace (meas_outcome_prj (M i) * R)"       
      using assms dim_eq fc_mats_carrier trace_comm 
      unfolding proj_measurement_def by auto 
    thus ?thesis by simp
  qed
  also have "... = sum (\<lambda>i. (Complex_Matrix.trace 
    (meas_outcome_val (M i)\<cdot>\<^sub>m meas_outcome_prj (M i) * R))) {..< p}"
  proof -
    have "\<And>i. i < p \<Longrightarrow> meas_outcome_val (M i) * 
    (Complex_Matrix.trace(meas_outcome_prj (M i) * R)) = 
    Complex_Matrix.trace (meas_outcome_val (M i)\<cdot>\<^sub>m meas_outcome_prj (M i)* R)"
    proof -
      fix i
      assume "i < p"
      hence "meas_outcome_val (M i) * 
        (Complex_Matrix.trace(meas_outcome_prj (M i) * R)) = 
        Complex_Matrix.trace (meas_outcome_val (M i)\<cdot>\<^sub>m (meas_outcome_prj (M i)* R))"
        using assms car
        by (metis dim_eq fc_mats_carrier trace_smult)
      also have "... =  Complex_Matrix.trace 
        (meas_outcome_val (M i)\<cdot>\<^sub>m meas_outcome_prj (M i)* R)"
      proof -
        have "meas_outcome_val (M i)\<cdot>\<^sub>m (meas_outcome_prj (M i)* R) = 
          meas_outcome_val (M i)\<cdot>\<^sub>m meas_outcome_prj (M i)* R" 
          using car assms unfolding proj_measurement_def
          by (metis \<open>i < p\<close> dim_eq fc_mats_carrier mult_smult_assoc_mat)
        thus ?thesis by simp
      qed
      finally show "meas_outcome_val (M i) * 
        (Complex_Matrix.trace(meas_outcome_prj (M i) * R)) =
        Complex_Matrix.trace 
        (meas_outcome_val (M i)\<cdot>\<^sub>m meas_outcome_prj (M i)* R)" .    
    qed
    thus ?thesis by simp
  qed
  also have "... = Complex_Matrix.trace (sum_mat 
    (\<lambda>i. meas_outcome_val (M i)\<cdot>\<^sub>m (meas_outcome_prj (M i)) * R) {..< p})" 
  proof (rule trace_sum_mat[symmetric])
    fix i
    assume "i \<in> {..< p}"
    hence "meas_outcome_val (M i) \<cdot>\<^sub>m meas_outcome_prj (M i) \<in> fc_mats" 
      using assms cpx_sq_mat_smult[of " meas_outcome_prj (M i)"]  
      unfolding proj_measurement_def by simp
    thus "meas_outcome_val (M i) \<cdot>\<^sub>m meas_outcome_prj (M i) * R \<in> fc_mats"
      by (simp add: assms(2) cpx_sq_mat_mult) 
  qed simp
  also have "... = Complex_Matrix.trace (sum_mat 
    (\<lambda>i. meas_outcome_val (M i)\<cdot>\<^sub>m (meas_outcome_prj (M i))) {..< p} * R)"
  proof -
    have "sum_mat (\<lambda>i. meas_outcome_val (M i)\<cdot>\<^sub>m (meas_outcome_prj (M i)) * R)
      {..< p} = sum_mat 
      (\<lambda>i. meas_outcome_val (M i)\<cdot>\<^sub>m (meas_outcome_prj (M i))) {..< p} * R"
    proof (rule sum_mat_distrib_right)
      show "\<And>i. i \<in> {..<p} \<Longrightarrow> meas_outcome_val (M i) \<cdot>\<^sub>m meas_outcome_prj (M i) \<in> 
        fc_mats"  
      proof -
        fix i
        assume "i \<in> {..<p}"
        thus "meas_outcome_val (M i) \<cdot>\<^sub>m meas_outcome_prj (M i) \<in> fc_mats" 
          using assms cpx_sq_mat_smult[of " meas_outcome_prj (M i)"]  
          unfolding proj_measurement_def by simp
      qed
    qed (auto simp add: assms)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma (in cpx_sq_mat) expect_value_hermitian:
  assumes "A\<in> fc_mats"
  and "hermitian A"
  and "make_pm A = (p, M)"
  and "R\<in> fc_mats"
shows "expect_value R p M = Complex_Matrix.trace (A * R)"
proof -
  have "expect_value R p M = Complex_Matrix.trace (sum_mat 
    (\<lambda>i. meas_outcome_val (M i)\<cdot>\<^sub>m (meas_outcome_prj (M i))) {..< p} * R)" 
    using assms make_pm_proj_measurement expect_value_trace by simp
  also have "... = Complex_Matrix.trace (A * R)"
  proof -
    have "sum_mat (\<lambda>i. meas_outcome_val (M i)\<cdot>\<^sub>m (meas_outcome_prj (M i))) 
      {..< p} = A" 
      using make_pm_sum assms by simp
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma obs_expect_value:
  assumes "A\<in> carrier_mat n n"
  and "hermitian A"
  and "R\<in> carrier_mat n n"
  and "0 < n"
shows "cpx_sq_mat.obs_expect_value n n R A = Complex_Matrix.trace (A * R)" 
proof -
  define fc::"complex Matrix.mat set" 
  where "fc = carrier_mat n n"
  interpret cpx_sq_mat n n fc
  proof
    show "fc = carrier_mat n n" using fc_def by simp
    show "0 < n" using assms by simp
  qed simp
  show ?thesis unfolding obs_expect_value_def
  proof (rule expect_value_hermitian)
    show "make_pm A=(proj_meas_size (make_pm A), proj_meas_outcomes (make_pm A))"
      using make_pm_decomp by simp
  qed (auto simp add: assms fc_def)
qed

end