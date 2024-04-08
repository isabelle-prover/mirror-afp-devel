theory Uncertainty_Principle
  imports "QHLProver.Complex_Matrix"
begin

section\<open>Setup\<close>

abbreviation bra_ket ("\<langle>_|_\<rangle>")
  where "\<langle>u|v\<rangle> \<equiv> inner_prod u v"

text\<open>Fix an n-dimensional normalized quantum state $\psi$.\<close>
locale quantum_state =
  fixes n:: nat
    and \<psi>:: "complex Matrix.vec"
  assumes dim[simp]: "\<psi> \<in> carrier_vec n"
      and normalized[simp]: "\<langle>\<psi>|\<psi>\<rangle> = 1"

begin 

text\<open>Observables on $\psi$ are hermitian matrices of appropriate dimensions.\<close>
abbreviation observable:: "complex Matrix.mat \<Rightarrow> bool" where
  "observable A \<equiv> A \<in> carrier_mat n n \<and> hermitian A"

text\<open>
  The mean value of an observable A is defined as $\langle \psi | A | \psi \rangle$. It is useful to
  have a scalar matrix of appropriate dimension containing this value. On paper, this is usually implicit.
\<close>
abbreviation mean_mat :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" ("\<llangle>_\<rrangle>")
  where "\<llangle>A\<rrangle> \<equiv> \<langle>\<psi>| A *\<^sub>v \<psi>\<rangle> \<cdot>\<^sub>m 1\<^sub>m n"

text\<open>
  The standard deviation of an observable A = $\sqrt {\langle \psi | A^2 | \psi \rangle - \langle \psi | A | \psi \rangle^2}$.
  Since the standard deviation is real (see lemma std-dev-real), we can define it as being of type real using norm.
  This simultaneously restricts it to positive values. (powers of two are expanded for simplicity)
\<close>
abbreviation std_dev :: "complex Matrix.mat \<Rightarrow> real" ("\<Delta>")
  where "\<Delta> A \<equiv> norm (csqrt (\<langle>\<psi>| (A * A *\<^sub>v \<psi>)\<rangle> - \<langle>\<psi>| A *\<^sub>v \<psi>\<rangle> * \<langle>\<psi>| A *\<^sub>v \<psi>\<rangle>))"   

end 

abbreviation commutator :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" ("\<lbrakk>_,_\<rbrakk>")
  where "commutator A B \<equiv> (A * B - B * A)"

abbreviation anticommutator :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" ("\<lbrace>_,_\<rbrace>")
  where "anticommutator A B \<equiv> (A * B + B * A)"

section\<open>Auxiliary Lemmas\<close>

lemma inner_prod_distrib_add_mat: 
  fixes u v :: "complex vec"
  assumes 
    "u \<in> carrier_vec n"
    "v \<in> carrier_vec m"
    "A \<in> carrier_mat n m"
    "B \<in> carrier_mat n m"
  shows "\<langle>u| (A + B) *\<^sub>v v\<rangle> = \<langle>u| A *\<^sub>v v\<rangle> + \<langle>u| B *\<^sub>v v\<rangle>"
  apply (subst add_mult_distrib_mat_vec)
  using assms by (auto intro: inner_prod_distrib_right)

lemma inner_prod_distrib_minus_mat: 
  fixes u v :: "complex vec"
  assumes 
    "u \<in> carrier_vec n"
    "v \<in> carrier_vec m"
    "A \<in> carrier_mat n m"
    "B \<in> carrier_mat n m"
  shows "\<langle>u| (A - B) *\<^sub>v v\<rangle> = \<langle>u| A *\<^sub>v v\<rangle> - \<langle>u| B *\<^sub>v v\<rangle>"
  apply (subst minus_mult_distrib_mat_vec)
  using assms by (auto intro: inner_prod_minus_distrib_right)

text\<open>Proving the usual Cauchy-Schwarz inequality using its formulation for complex vector spaces.\<close>
lemma Cauchy_Schwarz:
  assumes "v \<in> carrier_vec n" "u \<in> carrier_vec n"
  shows "norm (\<langle>u|v\<rangle>)^2 \<le> Re (\<langle>u|u\<rangle> * \<langle>v|v\<rangle>)"
proof-
  have "norm (\<langle>u|v\<rangle>)^2 \<le> (\<langle>u|u\<rangle> * \<langle>v|v\<rangle>)"
    using assms
    by (metis Cauchy_Schwarz_complex_vec complex_norm_square conjugate_complex_def inner_prod_swap)
  moreover have "(\<langle>u|u\<rangle> * \<langle>v|v\<rangle>) \<in> \<real>"
    by (simp add: complex_is_Real_iff)
  ultimately show ?thesis by (simp add: less_eq_complex_def)
qed

context quantum_state
begin

text\<open>Show that the the standard deviation yields a real value. This justifies our definition in terms of the norm.\<close>
lemma std_dev_real: 
  assumes "observable A"
  shows "csqrt (\<langle>\<psi>| (A * A *\<^sub>v \<psi>)\<rangle> - \<langle>\<psi>| A *\<^sub>v \<psi>\<rangle> * \<langle>\<psi>| A *\<^sub>v \<psi>\<rangle>) \<in> \<real>"
proof (subst csqrt_of_real_nonneg)
  \<comment>\<open>The term under the square root is real ...\<close>
  have "(\<langle>\<psi>|A * A *\<^sub>v \<psi>\<rangle> - \<langle>\<psi>|A *\<^sub>v \<psi>\<rangle> * \<langle>\<psi>|A *\<^sub>v \<psi>\<rangle>) \<in> \<real>" 
    apply (intro Reals_diff Reals_mult hermitian_inner_prod_real)
    using assms by (auto simp: hermitian_def adjoint_mult)
  then show "Im (\<langle>\<psi>|A * A *\<^sub>v \<psi>\<rangle> - \<langle>\<psi>|A *\<^sub>v \<psi>\<rangle> * \<langle>\<psi>|A *\<^sub>v \<psi>\<rangle>) = 0" 
    using complex_is_Real_iff by simp
next
  have *:"adjoint A = A" using assms hermitian_def by blast
  \<comment>\<open>... and positive (Cauchy-Schwarz)\<close>
  have "\<langle>\<psi>|A *\<^sub>v \<psi>\<rangle> * \<langle>\<psi>|A *\<^sub>v \<psi>\<rangle> \<le> \<langle>\<psi>|\<psi>\<rangle> * \<langle>\<psi>|A * A *\<^sub>v \<psi>\<rangle>"
    apply (subst assoc_mult_mat_vec) prefer 4
       apply (subst (2) adjoint_def_alter) prefer 4
          apply (subst (2) adjoint_def_alter) prefer 4
             apply (subst (1 2) *)
             apply (rule Cauchy_Schwarz_complex_vec[OF dim])
    using assms by auto
  then show "0 \<le> Re (\<langle>\<psi>|A * A *\<^sub>v \<psi>\<rangle> - \<langle>\<psi>|A *\<^sub>v \<psi>\<rangle> * \<langle>\<psi>|A *\<^sub>v \<psi>\<rangle>)"
    by (simp add: less_eq_complex_def)
  \<comment>\<open>Thus the result of the complex square root is real\<close>
qed simp

text\<open>This is an alternative way of formulating the standard deviation.\<close>
lemma std_dev_alt: 
  assumes "observable A"
  shows "\<Delta> A = norm (csqrt (\<langle>\<psi>| (A - \<llangle>A\<rrangle>) * (A - \<llangle>A\<rrangle>) *\<^sub>v \<psi>\<rangle>))"
proof-
  \<comment>\<open>Expand the matrix term\<close>
  have "(A - \<llangle>A\<rrangle>) * (A - \<llangle>A\<rrangle>) = (A + - \<llangle>A\<rrangle>) * (A + - \<llangle>A\<rrangle>)"
    using assms minus_add_uminus_mat by force
  also have *: "... = A * A + A * - \<llangle>A\<rrangle> + - \<llangle>A\<rrangle> * A + - \<llangle>A\<rrangle> * - \<llangle>A\<rrangle>" 
    apply (mat_assoc n)
    using assms by auto
  also have "... = A * A - \<llangle>A\<rrangle> * A - \<llangle>A\<rrangle> * A + \<llangle>A\<rrangle> * \<llangle>A\<rrangle>"
    using uminus_mult_right_mat assms by auto
  also have "... = A * A - \<langle>\<psi>| A *\<^sub>v \<psi>\<rangle> \<cdot>\<^sub>m A - \<langle>\<psi>| A *\<^sub>v \<psi>\<rangle> \<cdot>\<^sub>m A + \<llangle>A\<rrangle> * \<llangle>A\<rrangle>"
    using assms by auto
  finally have 1:
     "\<langle>\<psi>| (A - \<llangle>A\<rrangle>) * (A - \<llangle>A\<rrangle>) *\<^sub>v \<psi>\<rangle> = 
      \<langle>\<psi>| (A * A - \<langle>\<psi>| A *\<^sub>v \<psi>\<rangle> \<cdot>\<^sub>m A - \<langle>\<psi>| A *\<^sub>v \<psi>\<rangle> \<cdot>\<^sub>m A + \<llangle>A\<rrangle> * \<llangle>A\<rrangle>) *\<^sub>v \<psi>\<rangle>"
    by simp

  \<comment>\<open>The mean is linear, so it distributes over the matrix term ...\<close>
  have 2:
    "\<langle>\<psi>| (A * A - \<langle>\<psi>| A *\<^sub>v \<psi>\<rangle> \<cdot>\<^sub>m A - \<langle>\<psi>| A *\<^sub>v \<psi>\<rangle> \<cdot>\<^sub>m A + \<llangle>A\<rrangle> * \<llangle>A\<rrangle>) *\<^sub>v \<psi>\<rangle> =
     \<langle>\<psi>|A * A *\<^sub>v \<psi>\<rangle> - \<langle>\<psi>|\<langle>\<psi>|A *\<^sub>v \<psi>\<rangle> \<cdot>\<^sub>m A *\<^sub>v \<psi>\<rangle> - \<langle>\<psi>|\<langle>\<psi>|A *\<^sub>v \<psi>\<rangle> \<cdot>\<^sub>m A *\<^sub>v \<psi>\<rangle> + \<langle>\<psi>|\<llangle>A\<rrangle> * \<llangle>A\<rrangle> *\<^sub>v \<psi>\<rangle>"
    apply (subst inner_prod_distrib_add_mat) prefer 5
        apply (subst inner_prod_distrib_minus_mat) prefer 5
            apply (subst inner_prod_distrib_minus_mat)
    using assms by auto

  \<comment>\<open>... and a scaling factor can be pulled outside\<close>
  have 3: "\<langle>\<psi>|\<langle>\<psi>|A *\<^sub>v \<psi>\<rangle> \<cdot>\<^sub>m A *\<^sub>v \<psi>\<rangle> = \<langle>\<psi>|A *\<^sub>v \<psi>\<rangle> * \<langle>\<psi>|A *\<^sub>v \<psi>\<rangle>"
    by (metis assms dim inner_prod_smult_left mult_mat_vec_carrier smult_mat_mult_mat_vec_assoc)

  \<comment>\<open>This also means that this is just the mean squared\<close>
  have "\<langle>\<psi>|\<llangle>A\<rrangle> * \<llangle>A\<rrangle> *\<^sub>v \<psi>\<rangle> = \<langle>\<psi>|A *\<^sub>v \<psi>\<rangle> * \<langle>\<psi>|\<llangle>A\<rrangle> *\<^sub>v \<psi>\<rangle>"
    apply (subst mult_smult_assoc_mat) prefer 3
      apply (subst smult_mat_mult_mat_vec_assoc) prefer 3
        apply (subst inner_prod_smult_left)
    using assms by (auto intro!: mult_mat_vec_carrier)
  also have "... = \<langle>\<psi>|A *\<^sub>v \<psi>\<rangle> * \<langle>\<psi>|A *\<^sub>v \<psi>\<rangle>"
      apply (subst smult_mat_mult_mat_vec_assoc) prefer 3
        apply (subst inner_prod_smult_left[where n = n])
    using assms by auto
  finally have 4: "\<langle>\<psi>|\<llangle>A\<rrangle> * \<llangle>A\<rrangle> *\<^sub>v \<psi>\<rangle> = \<langle>\<psi>|A *\<^sub>v \<psi>\<rangle> * \<langle>\<psi>|A *\<^sub>v \<psi>\<rangle>" by simp

  \<comment>\<open>With these four equivalences we can rewrite the standard deviation as specified\<close>
  show ?thesis
    by (simp add: 1 2 3 4)
qed

section\<open>Main Proof\<close>

text\<open>Note that when swapping two observables inside an inner product, it is the same as conjugating the result.\<close>
lemma cnj_observables:
  assumes "observable A" "observable B" 
  shows "cnj \<langle>\<psi>| (A * B) *\<^sub>v \<psi>\<rangle> = \<langle>\<psi>| (B * A) *\<^sub>v \<psi>\<rangle>"
proof -
  have "cnj (conjugate \<langle>A * B *\<^sub>v \<psi>|\<psi>\<rangle>) = \<langle>adjoint (B * A) *\<^sub>v \<psi>|\<psi>\<rangle>"
    using assms by (metis (full_types) adjoint_mult complex_cnj_cnj conjugate_complex_def hermitian_def)
  then show ?thesis
    using assms by (metis adjoint_def_alter dim inner_prod_swap mult_carrier_mat mult_mat_vec_carrier)
qed

text\<open>
  With the above lemma we can make two observations about the behaviour of the commutator/
  anticommutator inside an inner product.
\<close>
lemma commutator_im: 
  assumes "observable A" "observable B" 
  shows "\<langle>\<psi>| \<lbrakk>A, B\<rbrakk> *\<^sub>v \<psi>\<rangle> = 2 * \<i> * Im(\<langle>\<psi>| A * B *\<^sub>v \<psi>\<rangle>)"
proof -
  have "\<langle>\<psi>| \<lbrakk>A, B\<rbrakk> *\<^sub>v \<psi>\<rangle> = \<langle>\<psi>| A * B *\<^sub>v \<psi>\<rangle> - \<langle>\<psi>| B * A *\<^sub>v \<psi>\<rangle>" 
    using assms by (auto intro!: inner_prod_distrib_minus_mat)
  also have "... = \<langle>\<psi>| A * B *\<^sub>v \<psi>\<rangle> - cnj \<langle>\<psi>| A * B *\<^sub>v \<psi>\<rangle>" 
    by (subst cnj_observables[OF assms], simp)
  finally show ?thesis
    using complex_diff_cnj by simp
qed

lemma anticommutator_re: 
  assumes "observable A" "observable B" 
  shows "\<langle>\<psi>| \<lbrace>A, B\<rbrace> *\<^sub>v \<psi>\<rangle> = 2 * Re(\<langle>\<psi>| A * B *\<^sub>v \<psi>\<rangle>)"
proof -
  have "\<langle>\<psi>| \<lbrace>A, B\<rbrace> *\<^sub>v \<psi>\<rangle> = \<langle>\<psi>| A * B *\<^sub>v \<psi>\<rangle> + \<langle>\<psi>| B * A *\<^sub>v \<psi>\<rangle>" 
    using assms by (auto intro!: inner_prod_distrib_add_mat)
  also have "... = \<langle>\<psi>| A * B *\<^sub>v \<psi>\<rangle> + cnj \<langle>\<psi>| A * B *\<^sub>v \<psi>\<rangle>" 
    by (subst cnj_observables[OF assms], simp)
  finally show ?thesis
    using complex_add_cnj by simp
qed

text\<open>
  This intermediate step already looks similar to the uncertainty principle. The LHS will play the
  role of the lower bound in the uncertainty principle. The RHS will turn into the standard 
  deviation of our observables under a certain substitution.
\<close>
lemma commutator_ineq:
  assumes "observable A" "observable B" 
  shows "(norm \<langle>\<psi>| \<lbrakk>A, B\<rbrakk> *\<^sub>v \<psi>\<rangle>)^2 \<le>  4 * Re (\<langle>\<psi>| A * A *\<^sub>v \<psi>\<rangle> * \<langle>\<psi>| B * B *\<^sub>v \<psi>\<rangle>)"
proof -
  \<comment>\<open> 
    The inner product of our quantum state under A and B can be expressed in terms of its real and 
    imaginary part 
  \<close>
  let ?x = "Re(\<langle>\<psi>| A * B *\<^sub>v \<psi>\<rangle>)"
  let ?y = "Im(\<langle>\<psi>| A * B *\<^sub>v \<psi>\<rangle>)"

  \<comment>\<open>These parts can be expressed using the commutator/anticommutator as shown above\<close>
  have im: "(norm \<langle>\<psi>| \<lbrakk>A, B\<rbrakk> *\<^sub>v \<psi>\<rangle>)^2 = 4 * ?y^2"
    apply (subst commutator_im[OF assms])
    using cmod_power2 by simp

  have re: "(norm \<langle>\<psi>| \<lbrace>A, B\<rbrace> *\<^sub>v \<psi>\<rangle>)^2 = 4 * ?x^2"
    apply (subst anticommutator_re[OF assms])
    using cmod_power2 by simp

  \<comment>\<open>Meaning, the sum of the commutator terms gives us $2 \langle \psi | A B | \psi \rangle$. Squared we get ...\<close>
  from im re have "(norm \<langle>\<psi>| \<lbrakk>A, B\<rbrakk> *\<^sub>v \<psi>\<rangle>)^2 + (norm \<langle>\<psi>| \<lbrace>A, B\<rbrace> *\<^sub>v \<psi>\<rangle>)^2 = 4 * (?x^2 + ?y^2)" 
    by simp
  also have "... = 4 * norm(\<langle>\<psi>| A * B *\<^sub>v \<psi>\<rangle>)^2" 
    using cmod_power2 by simp
  also have "... = 4 * norm(\<langle>A *\<^sub>v \<psi>| B *\<^sub>v \<psi>\<rangle>)^2" 
    apply (subst assoc_mult_mat_vec) prefer 4
       apply (subst adjoint_def_alter)
    using assms hermitian_def by (auto, force)
  \<comment>\<open>Now we use the Cauchy-Schwarz inequality\<close>
  also have "... \<le> 4 * Re (\<langle>A *\<^sub>v \<psi>| A *\<^sub>v \<psi>\<rangle> * \<langle>B *\<^sub>v \<psi>| B *\<^sub>v \<psi>\<rangle>)" 
    by (smt (verit) assms Cauchy_Schwarz dim mult_mat_vec_carrier)
  \<comment>\<open>Rewrite this term\<close>
  also have "... = 4 * Re (\<langle>\<psi>| A * A *\<^sub>v \<psi>\<rangle> * \<langle>\<psi>| B * B *\<^sub>v \<psi>\<rangle>)" 
    apply (subst (1 2) assoc_mult_mat_vec) prefer 7
          apply (subst (3 4) adjoint_def_alter)
    using assms by (auto simp: hermitian_def)
  \<comment>\<open>Dropping a positive term on the LHS does not affect the inequality\<close>
  finally show ?thesis 
    using norm_ge_zero by (smt (verit, ccfv_threshold) zero_le_power2)
qed

text\<open>
  This is part of the substitution we need in the final proof. This lemma
  shows that the commutator simplifies nicely under that substitution.
\<close>
lemma commutator_sub_mean[simp]: 
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"   
  shows "\<lbrakk>A - \<llangle>A\<rrangle>, B - \<llangle>B\<rrangle>\<rbrakk> = \<lbrakk>A,B\<rbrakk>"
proof -
  \<comment>\<open>
    Simply expand everything.
    The unary minus signs are deliberate, because we want to have addition in the parentheses. 
    Otherwise mat-assoc cannot remove the parentheses.
  \<close>
  have "\<lbrakk>A - \<llangle>A\<rrangle>, B - \<llangle>B\<rrangle>\<rbrakk> = A * B - \<llangle>A\<rrangle> * B - A * \<llangle>B\<rrangle> - \<llangle>A\<rrangle> * (- \<llangle>B\<rrangle>) - (B * A + (- (\<llangle>B\<rrangle> * A)) + (- (B * \<llangle>A\<rrangle>)) - \<llangle>B\<rrangle> * (- \<llangle>A\<rrangle>))" 
    apply (mat_assoc n)
    using assms by auto
  \<comment>\<open>Remove the last subtraction in the parentheses and unnecessary minus signs\<close>
  also have "... = A * B - \<llangle>A\<rrangle> * B - A * \<llangle>B\<rrangle> - (- (\<llangle>A\<rrangle> * \<llangle>B\<rrangle>)) - (B * A + (- (\<llangle>B\<rrangle> * A)) + (- (B * \<llangle>A\<rrangle>)) - (- (\<llangle>B\<rrangle> * \<llangle>A\<rrangle>)))"
    using assms by auto
  also have "... = A * B - \<llangle>A\<rrangle> * B - A * \<llangle>B\<rrangle> + - (- (\<llangle>A\<rrangle> * \<llangle>B\<rrangle>)) - (B * A + (- (\<llangle>B\<rrangle> * A)) + (- (B * \<llangle>A\<rrangle>)) + (- (- (\<llangle>B\<rrangle> * \<llangle>A\<rrangle>))))"
    apply (mat_assoc n)
    using assms by auto
  also have "... = A * B - \<llangle>A\<rrangle> * B - A * \<llangle>B\<rrangle> + \<llangle>A\<rrangle> * \<llangle>B\<rrangle> - (B * A + (- (\<llangle>B\<rrangle> * A)) + (- (B * \<llangle>A\<rrangle>)) + \<llangle>B\<rrangle> * \<llangle>A\<rrangle>)"
   by simp
  \<comment>\<open>Remove parentheses\<close>
  also have "... = A * B - \<llangle>A\<rrangle> * B - A * \<llangle>B\<rrangle> + \<llangle>A\<rrangle> * \<llangle>B\<rrangle> - B * A + (- (- (\<llangle>B\<rrangle> * A))) + (- (- (B * \<llangle>A\<rrangle>))) - \<llangle>B\<rrangle> * \<llangle>A\<rrangle>"
    apply (mat_assoc n)
    using assms by auto
  also have "... =A * B - \<llangle>A\<rrangle> * B - A * \<llangle>B\<rrangle> + \<llangle>A\<rrangle> * \<llangle>B\<rrangle> - B * A + \<llangle>B\<rrangle> * A + B * \<llangle>A\<rrangle> - \<llangle>B\<rrangle> * \<llangle>A\<rrangle>"
    using uminus_uminus_mat by simp 
  \<comment>\<open>Commutative mean\<close>
  also have "...= A * B - \<llangle>A\<rrangle> * B - A * \<llangle>B\<rrangle> + \<llangle>A\<rrangle> * \<llangle>B\<rrangle> - B * A + A * \<llangle>B\<rrangle> + \<llangle>A\<rrangle> * B - \<llangle>A\<rrangle> * \<llangle>B\<rrangle>"
    using assms by auto
  \<comment>\<open>Reorder terms\<close>
  also have "...= A * B - B * A + \<llangle>A\<rrangle> * B - \<llangle>A\<rrangle> * B + A * \<llangle>B\<rrangle> - A * \<llangle>B\<rrangle> + \<llangle>A\<rrangle> * \<llangle>B\<rrangle> - \<llangle>A\<rrangle> * \<llangle>B\<rrangle>"
    apply (mat_assoc n)
    using assms by auto
  \<comment>\<open>Everything but the first two terms are eliminated, resulting in the commutator\<close>
  finally show ?thesis using assms minus_r_inv_mat by auto
qed


theorem uncertainty_principle: 
  assumes "observable C" "observable D"
  shows "\<Delta> C * \<Delta> D \<ge>  norm \<langle>\<psi>|\<lbrakk>C,D\<rbrakk> *\<^sub>v \<psi>\<rangle> / 2"
proof -
  \<comment>\<open>Perform the substitution\<close>
  let ?A = "C - \<llangle>C\<rrangle>"
  let ?B = "D - \<llangle>D\<rrangle>"

  \<comment>\<open>These matrices are valid observables\<close>
  from assms have observables_A_B: "observable ?A" "observable ?B"
    using hermitian_inner_prod_real assms Reals_cnj_iff 
    by (auto simp: hermitian_def adjoint_minus adjoint_one adjoint_scale)

  \<comment>\<open>Start with commutator-ineq\<close>
  have "(norm \<langle>\<psi>| \<lbrakk>?A, ?B\<rbrakk> *\<^sub>v \<psi>\<rangle>)^2 \<le> 4 * Re ((\<langle>\<psi>| ?A * ?A *\<^sub>v \<psi>\<rangle>) * (\<langle>\<psi>| ?B * ?B *\<^sub>v \<psi>\<rangle>))"
    using commutator_ineq[OF observables_A_B] by auto
  \<comment>\<open>Simplify the commutator\<close>
  then have "(norm \<langle>\<psi>| \<lbrakk>C, D\<rbrakk> *\<^sub>v \<psi>\<rangle>)^2 \<le> 4 * Re ((\<langle>\<psi>| ?A * ?A *\<^sub>v \<psi>\<rangle>) * (\<langle>\<psi>| ?B * ?B *\<^sub>v \<psi>\<rangle>))"
    using assms by simp
  \<comment>\<open>Apply sqrt to both sides\<close>
  then have "sqrt ((norm (\<langle>\<psi>| \<lbrakk>C, D\<rbrakk> *\<^sub>v \<psi>\<rangle>))^2) \<le> sqrt (4 * Re ((\<langle>\<psi>| ?A * ?A *\<^sub>v \<psi>\<rangle>) * (\<langle>\<psi>| ?B * ?B *\<^sub>v \<psi>\<rangle>)))"
    using real_sqrt_le_mono by blast
  \<comment>\<open>Simplify\<close>
  then have "norm (\<langle>\<psi>| \<lbrakk>C, D\<rbrakk> *\<^sub>v \<psi>\<rangle>) \<le> 2 * sqrt (Re ((\<langle>\<psi>| ?A * ?A *\<^sub>v \<psi>\<rangle>) * (\<langle>\<psi>| ?B * ?B *\<^sub>v \<psi>\<rangle>)))"
    by (auto cong: real_sqrt_mult)
  \<comment>\<open>Because these inner products are positive and real, norm = Re\<close>
  then have "norm (\<langle>\<psi>| \<lbrakk>C, D\<rbrakk> *\<^sub>v \<psi>\<rangle>) \<le> 2 * sqrt ( \<bar>Re ((\<langle>\<psi>| ?A * ?A *\<^sub>v \<psi>\<rangle>) * (\<langle>\<psi>| ?B * ?B *\<^sub>v \<psi>\<rangle>))\<bar>)"
    by (smt (verit, ccfv_SIG) real_sqrt_le_iff)
  then have "norm (\<langle>\<psi>| \<lbrakk>C, D\<rbrakk> *\<^sub>v \<psi>\<rangle>) \<le> 2 * sqrt (norm ((\<langle>\<psi>| ?A * ?A *\<^sub>v \<psi>\<rangle>) * (\<langle>\<psi>| ?B * ?B *\<^sub>v \<psi>\<rangle>)))"
    by (auto simp: in_Reals_norm Reals_cnj_iff cnj_observables observables_A_B)
  \<comment>\<open>Rewrite term to recover the standard deviation (As formulated in std-dev-alt)\<close>
  then have "norm (\<langle>\<psi>| \<lbrakk>C, D\<rbrakk> *\<^sub>v \<psi>\<rangle>) \<le> 2 * norm (csqrt (\<langle>\<psi>| ?A * ?A *\<^sub>v \<psi>\<rangle>)) * norm (csqrt (\<langle>\<psi>| ?B * ?B *\<^sub>v \<psi>\<rangle>))"
    by (simp add: norm_mult real_sqrt_mult)
  then show "\<Delta> C * \<Delta> D \<ge> norm \<langle>\<psi>|\<lbrakk>C, D\<rbrakk> *\<^sub>v \<psi>\<rangle> / 2" 
    using assms by (auto cong: std_dev_alt)
qed

end

end