section \<open>\<open>Trace_Class\<close> -- Trace-class operators\<close>

theory Trace_Class
  imports Complex_Bounded_Operators.Complex_L2 HS2Ell2
    Weak_Operator_Topology Positive_Operators Compact_Operators
    Spectral_Theorem
begin

hide_fact (open) Infinite_Set_Sum.abs_summable_on_Sigma_iff
hide_fact (open) Infinite_Set_Sum.abs_summable_on_comparison_test
hide_const (open) Determinants.trace
hide_fact (open) Determinants.trace_def

unbundle cblinfun_notation

subsection \<open>Auxiliary lemmas\<close>

lemma 
  fixes h :: \<open>'a::{chilbert_space}\<close>
  assumes \<open>is_onb E\<close>
  shows parseval_abs_summable: \<open>(\<lambda>e. (cmod (e \<bullet>\<^sub>C h))\<^sup>2) abs_summable_on E\<close>
proof (cases \<open>h = 0\<close>)
  case True
  then show ?thesis by simp
next
  case False
  then have \<open>(\<Sum>\<^sub>\<infinity>e\<in>E. (cmod (e \<bullet>\<^sub>C h))\<^sup>2) \<noteq> 0\<close>
    using assms by (simp add: parseval_identity is_onb_def)
  then show ?thesis
    using infsum_not_exists by auto
qed

lemma basis_image_square_has_sum1:
  \<comment> \<open>Half of \<^cite>\<open>\<open>Proposition 18.1\<close> in conway00operator\<close>, other half in \<open>basis_image_square_has_sum1\<close>.\<close>
  fixes E :: \<open>'a::complex_inner set\<close> and F :: \<open>'b::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> and \<open>is_onb F\<close>
  shows \<open>((\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) has_sum t) E \<longleftrightarrow> ((\<lambda>(e,f). (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2) has_sum t) (E\<times>F)\<close>
proof (rule iffI)
  assume asm: \<open>((\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) has_sum t) E\<close>
  have sum1: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. (norm (A *\<^sub>V e))\<^sup>2)\<close>
    using asm infsumI by blast
  have abs1: \<open>(\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) abs_summable_on E\<close>
    using asm summable_on_def by auto
  have sum2: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2)\<close>
    apply (subst sum1)
    apply (rule infsum_cong)
    using assms(2)
    by (simp add: is_onb_def flip: parseval_identity)
  have abs2: \<open>(\<lambda>e. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2) abs_summable_on E\<close>
    using _ abs1 apply (rule summable_on_cong[THEN iffD2])
    apply (subst parseval_identity)
    using assms(2) by (auto simp: is_onb_def)
  have abs3: \<open>(\<lambda>(x, y). (cmod (y \<bullet>\<^sub>C (A *\<^sub>V x)))\<^sup>2) abs_summable_on E \<times> F\<close>
    thm abs_summable_on_Sigma_iff
    apply (rule abs_summable_on_Sigma_iff[THEN iffD2], rule conjI)
    using abs2 apply (auto simp del: real_norm_def)
    using assms(2) parseval_abs_summable apply blast
    by auto
  have sum3: \<open>t = (\<Sum>\<^sub>\<infinity>(e,f)\<in>E\<times>F. (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2)\<close>
    apply (subst sum2)
    apply (subst infsum_Sigma'_banach[symmetric])
    using abs3 abs_summable_summable apply blast
    by auto
  then show \<open>((\<lambda>(e,f). (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2) has_sum t) (E\<times>F)\<close>
    using abs3 abs_summable_summable has_sum_infsum by blast
next
  assume asm: \<open>((\<lambda>(e,f). (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2) has_sum t) (E\<times>F)\<close>
  have abs3: \<open>(\<lambda>(x, y). (cmod (y \<bullet>\<^sub>C (A *\<^sub>V x)))\<^sup>2) abs_summable_on E \<times> F\<close>
    using asm summable_on_def summable_on_iff_abs_summable_on_real
    by blast
  have sum3: \<open>t = (\<Sum>\<^sub>\<infinity>(e,f)\<in>E\<times>F. (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2)\<close>
    using asm infsumI by blast
  have sum2: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2)\<close>
    by (metis (mono_tags, lifting) asm infsum_Sigma'_banach infsum_cong sum3 summable_iff_has_sum_infsum)
  have abs2: \<open>(\<lambda>e. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2) abs_summable_on E\<close>
    by (smt (verit, del_insts) abs3 summable_on_Sigma_banach summable_on_cong summable_on_iff_abs_summable_on_real)
  have sum1: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. (norm (A *\<^sub>V e))\<^sup>2)\<close>
    apply (subst sum2)
    apply (rule infsum_cong)
    using assms
    by (auto intro!: simp: parseval_identity is_onb_def)
  have abs1: \<open>(\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) abs_summable_on E\<close>
    using assms abs2
    by (auto intro!: simp: parseval_identity is_onb_def)
  show \<open>((\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) has_sum t) E\<close>
    using abs1 sum1 by auto
qed

lemma basis_image_square_has_sum2:
  \<comment> \<open>Half of \<^cite>\<open>\<open>Proposition 18.1\<close> in conway00operator\<close>, other half in @{thm [source] basis_image_square_has_sum1}.\<close>
  fixes E :: \<open>'a::chilbert_space set\<close> and F :: \<open>'b::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> and \<open>is_onb F\<close>
  shows \<open>((\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) has_sum t) E \<longleftrightarrow> ((\<lambda>f. (norm (A* *\<^sub>V f))\<^sup>2) has_sum t) F\<close>
proof -
  have \<open>((\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) has_sum t) E \<longleftrightarrow> ((\<lambda>(e,f). (cmod (f \<bullet>\<^sub>C (A *\<^sub>V e)))\<^sup>2) has_sum t) (E\<times>F)\<close>
    using basis_image_square_has_sum1 assms by blast
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>(e,f). (cmod ((A* *\<^sub>V f) \<bullet>\<^sub>C e))\<^sup>2) has_sum t) (E\<times>F)\<close>
    apply (subst cinner_adj_left)
    by (rule refl)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>(f,e). (cmod ((A* *\<^sub>V f) \<bullet>\<^sub>C e))\<^sup>2) has_sum t) (F\<times>E)\<close>
    apply (subst asm_rl[of \<open>F\<times>E = prod.swap ` (E\<times>F)\<close>])
     apply force
    apply (subst has_sum_reindex)
    by (auto simp: o_def)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>f. (norm (A* *\<^sub>V f))\<^sup>2) has_sum t) F\<close>
    apply (subst cinner_commute, subst complex_mod_cnj)
    using basis_image_square_has_sum1 assms
    by blast
  finally show ?thesis
    by -
qed

subsection \<open>Trace-norm and trace-class\<close>

lemma trace_norm_basis_invariance:
  assumes \<open>is_onb E\<close> and \<open>is_onb F\<close>
  shows \<open>((\<lambda>e. cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))) has_sum t) E \<longleftrightarrow> ((\<lambda>f. cmod (f \<bullet>\<^sub>C (abs_op A *\<^sub>V f))) has_sum t) F\<close>
    \<comment> \<open>@{cite "conway00operator"}, Corollary 18.2\<close>
proof -
  define B where \<open>B = sqrt_op (abs_op A)\<close>
  have \<open>complex_of_real (cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))) = (B* *\<^sub>V B*\<^sub>V e) \<bullet>\<^sub>C e\<close> for e
    apply (simp add: B_def positive_hermitianI flip: cblinfun_apply_cblinfun_compose)
    by (metis abs_op_pos abs_pos cinner_commute cinner_pos_if_pos complex_cnj_complex_of_real complex_of_real_cmod)
  also have \<open>\<dots> e = complex_of_real ((norm (B *\<^sub>V e))\<^sup>2)\<close> for e
    apply (subst cdot_square_norm[symmetric])
    apply (subst cinner_adj_left[symmetric])
    by (simp add: B_def)
  finally have *: \<open>cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) = (norm (B *\<^sub>V e))\<^sup>2\<close> for e
    by (metis Re_complex_of_real)

  have \<open>((\<lambda>e. cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))) has_sum t) E \<longleftrightarrow> ((\<lambda>e. (norm (B *\<^sub>V e))\<^sup>2) has_sum t) E\<close>
    by (simp add: *)
  also have \<open>\<dots> = ((\<lambda>f. (norm (B* *\<^sub>V f))\<^sup>2) has_sum t) F\<close>
    apply (subst basis_image_square_has_sum2[where F=F])
    by (simp_all add: assms)
  also have \<open>\<dots> = ((\<lambda>f. (norm (B *\<^sub>V f))\<^sup>2) has_sum t) F\<close>
    using basis_image_square_has_sum2 assms(2) by blast
  also have \<open>\<dots> = ((\<lambda>e. cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))) has_sum t) F\<close>
    by (simp add: *)
  finally show ?thesis
    by simp
qed

definition trace_class :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner) \<Rightarrow> bool\<close> 
  where \<open>trace_class A \<longleftrightarrow> (\<exists>E. is_onb E \<and> (\<lambda>e. e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) abs_summable_on E)\<close>

lemma trace_classI:
  assumes \<open>is_onb E\<close> and \<open>(\<lambda>e. e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) abs_summable_on E\<close>
  shows \<open>trace_class A\<close>
  using assms(1) assms(2) trace_class_def by blast

lemma trace_class_iff_summable:
  assumes \<open>is_onb E\<close>
  shows \<open>trace_class A \<longleftrightarrow> (\<lambda>e. e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) abs_summable_on E\<close>
  apply (auto intro!: trace_classI assms simp: trace_class_def)
  using assms summable_on_def trace_norm_basis_invariance by blast

lemma trace_class_0[simp]: \<open>trace_class 0\<close>
  unfolding trace_class_def
  by (auto intro!: exI[of _ some_chilbert_basis] simp: is_onb_def is_normal_some_chilbert_basis)

(* lemma polar_polar_abs_op: \<open>(polar_decomposition a)* o\<^sub>C\<^sub>L polar_decomposition a o\<^sub>C\<^sub>L abs_op a = abs_op a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  using polar_decomposition_correct[of a] polar_decomposition_correct'[of a]
  by (simp add: cblinfun_compose_assoc) *)

lemma trace_class_uminus: \<open>trace_class t \<Longrightarrow> trace_class (-t)\<close>
  by (auto simp add: trace_class_def)

lemma trace_class_uminus_iff[simp]: \<open>trace_class (-a) = trace_class a\<close>
  by (auto simp add: trace_class_def)

definition trace_norm where \<open>trace_norm A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))) else 0)\<close>

definition trace where \<open>trace A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C (A *\<^sub>V e)) else 0)\<close>

lemma trace_0[simp]: \<open>trace 0 = 0\<close>
  unfolding trace_def by simp

lemma trace_class_abs_op[simp]: \<open>trace_class (abs_op A) = trace_class A\<close>
  unfolding trace_class_def
  by simp

lemma trace_abs_op[simp]: \<open>trace (abs_op A) = trace_norm A\<close>
proof (cases \<open>trace_class A\<close>)
  case True
  have pos: \<open>e \<bullet>\<^sub>C (abs_op A *\<^sub>V e) \<ge> 0\<close> for e
    by (simp add: cinner_pos_if_pos)
  then have abs: \<open>e \<bullet>\<^sub>C (abs_op A *\<^sub>V e) = abs (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))\<close> for e
    by (simp add: abs_pos)
  
  have \<open>trace (abs_op A) = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))\<close>
    by (simp add: trace_def True)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. complex_of_real (cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e))))\<close>
    using pos abs complex_of_real_cmod by presburger
  also have \<open>\<dots> = complex_of_real (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)))\<close>
    by (simp add: infsum_of_real)
  also have \<open>\<dots> = trace_norm A\<close>
    by (simp add: trace_norm_def True)
  finally show ?thesis
    by -
next
  case False
  then show ?thesis 
    by (simp add: trace_def trace_norm_def)
qed

lemma trace_norm_pos: \<open>trace_norm A = trace A\<close> if \<open>A \<ge> 0\<close>
  by (metis abs_op_id_on_pos that trace_abs_op)


lemma trace_norm_alt_def:
  assumes \<open>is_onb B\<close>
  shows \<open>trace_norm A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>B. cmod (e  \<bullet>\<^sub>C (abs_op A *\<^sub>V e))) else 0)\<close>
  by (metis (mono_tags, lifting) assms infsum_eqI' is_onb_some_chilbert_basis trace_norm_basis_invariance trace_norm_def)

lemma trace_class_finite_dim[simp]: \<open>trace_class A\<close> for A :: \<open>'a::{cfinite_dim,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner\<close>
  apply (subst trace_class_iff_summable[of some_chilbert_basis])
  by (auto intro!: summable_on_finite)

lemma trace_class_scaleC: \<open>trace_class (c *\<^sub>C a)\<close> if \<open>trace_class a\<close>
proof -
  from that obtain B where \<open>is_onb B\<close> and \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op a *\<^sub>V x)) abs_summable_on B\<close>
    by (auto simp: trace_class_def)
  then show ?thesis
    by (auto intro!: exI[of _ B] summable_on_cmult_right simp: trace_class_def \<open>is_onb B\<close> abs_op_scaleC norm_mult)
qed

lemma trace_scaleC: \<open>trace (c *\<^sub>C a) = c * trace a\<close>
proof -
  consider (trace_class) \<open>trace_class a\<close> | (c0) \<open>c = 0\<close> | (non_trace_class) \<open>\<not> trace_class a\<close> \<open>c \<noteq> 0\<close>
    by auto
  then show ?thesis
  proof cases
    case trace_class
    then have \<open>trace_class (c *\<^sub>C a)\<close>
      by (rule trace_class_scaleC)
    then have \<open>trace (c *\<^sub>C a) = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C (c *\<^sub>C a *\<^sub>V e))\<close>
      unfolding trace_def by simp
    also have \<open>\<dots> = c * (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C (a *\<^sub>V e))\<close>
      by (auto simp: infsum_cmult_right')
    also from trace_class have \<open>\<dots> = c * trace a\<close>
      by (simp add: Trace_Class.trace_def)
    finally show ?thesis
      by -
  next
    case c0
    then show ?thesis 
      by simp
  next
    case non_trace_class
    then have \<open>\<not> trace_class (c *\<^sub>C a)\<close>
      by (metis divideC_field_simps(2) trace_class_scaleC)
    with non_trace_class show ?thesis
      by (simp add: trace_def)
  qed
qed

lemma trace_uminus: \<open>trace (- a) = - trace a\<close>
  by (metis mult_minus1 scaleC_minus1_left trace_scaleC)

lemma trace_norm_0[simp]: \<open>trace_norm 0 = 0\<close>
  by (auto simp: trace_norm_def)

lemma trace_norm_nneg[simp]: \<open>trace_norm a \<ge> 0\<close>
  apply (cases \<open>trace_class a\<close>)
  by (auto simp: trace_norm_def infsum_nonneg)

lemma trace_norm_scaleC: \<open>trace_norm (c *\<^sub>C a) = norm c * trace_norm a\<close>
proof -
  consider (trace_class) \<open>trace_class a\<close> | (c0) \<open>c = 0\<close> | (non_trace_class) \<open>\<not> trace_class a\<close> \<open>c \<noteq> 0\<close>
    by auto
  then show ?thesis
  proof cases
    case trace_class
    then have \<open>trace_class (c *\<^sub>C a)\<close>
      by (rule trace_class_scaleC)
    then have \<open>trace_norm (c *\<^sub>C a) = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. norm (e \<bullet>\<^sub>C (abs_op (c *\<^sub>C a) *\<^sub>V e)))\<close>
      unfolding trace_norm_def by simp
    also have \<open>\<dots> = norm c * (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. norm (e \<bullet>\<^sub>C (abs_op a *\<^sub>V e)))\<close>
      by (auto simp: infsum_cmult_right' abs_op_scaleC norm_mult)
    also from trace_class have \<open>\<dots> = norm c * trace_norm a\<close>
      by (simp add: trace_norm_def)
    finally show ?thesis
      by -
  next
    case c0
    then show ?thesis
      by simp
  next
    case non_trace_class
    then have \<open>\<not> trace_class (c *\<^sub>C a)\<close>
      by (metis divideC_field_simps(2) trace_class_scaleC)
    with non_trace_class show ?thesis
      by (simp add: trace_norm_def)
  qed
qed


lemma trace_norm_nondegenerate: \<open>a = 0\<close> if \<open>trace_class a\<close> and \<open>trace_norm a = 0\<close>
proof (rule ccontr)
  assume \<open>a \<noteq> 0\<close>
  then have \<open>abs_op a \<noteq> 0\<close>
    using abs_op_nondegenerate by blast
  then obtain x where xax: \<open>x \<bullet>\<^sub>C (abs_op a *\<^sub>V x) \<noteq> 0\<close>
    by (metis cblinfun.zero_left cblinfun_cinner_eqI cinner_zero_right)
  then have \<open>norm x \<noteq> 0\<close>
    by auto
  then have xax': \<open>sgn x \<bullet>\<^sub>C (abs_op a *\<^sub>V sgn x) \<noteq> 0\<close> and [simp]: \<open>norm (sgn x) = 1\<close>
    unfolding sgn_div_norm using xax by (auto simp: cblinfun.scaleR_right)
  obtain B where sgnx_B: \<open>{sgn x} \<subseteq> B\<close> and \<open>is_onb B\<close>
    apply atomize_elim apply (rule orthonormal_basis_exists)
    using \<open>norm x \<noteq> 0\<close> by (auto simp: is_ortho_set_def sgn_div_norm)

  from \<open>is_onb B\<close> that
  have summable: \<open>(\<lambda>e. e \<bullet>\<^sub>C (abs_op a *\<^sub>V e)) abs_summable_on B\<close>
    using trace_class_iff_summable by fastforce

  from that have \<open>0 = trace_norm a\<close>
    by simp
  also from \<open>is_onb B\<close> have \<open>trace_norm a = (\<Sum>\<^sub>\<infinity>e\<in>B. cmod (e \<bullet>\<^sub>C (abs_op a *\<^sub>V e)))\<close>
    by (smt (verit, ccfv_SIG) abs_norm_cancel infsum_cong infsum_not_exists real_norm_def trace_class_def trace_norm_alt_def)
  also have \<open>\<dots> \<ge> (\<Sum>\<^sub>\<infinity>e\<in>{sgn x}. cmod (e \<bullet>\<^sub>C (abs_op a *\<^sub>V e)))\<close> (is \<open>_ \<ge> \<dots>\<close>)
    apply (rule infsum_mono2)
    using summable sgnx_B by auto
  also from xax' have \<open>\<dots> > 0\<close>
    by (simp add: is_orthogonal_sym xax')
  finally show False
    by simp
qed

typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space) trace_class = \<open>Collect trace_class :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
  morphisms from_trace_class Abs_trace_class
  by (auto intro!: exI[of _ 0])
setup_lifting type_definition_trace_class

lemma trace_class_from_trace_class[simp]: \<open>trace_class (from_trace_class t)\<close>
  using from_trace_class by blast

lemma trace_pos: \<open>trace a \<ge> 0\<close> if \<open>a \<ge> 0\<close>
  by (metis abs_op_def complex_of_real_nn_iff sqrt_op_unique that trace_abs_op trace_norm_nneg)

lemma trace_adj_prelim: \<open>trace (a*) = cnj (trace a)\<close> if \<open>trace_class a\<close> and \<open>trace_class (a*)\<close>
  \<comment> \<open>We will later strengthen this as \<open>trace_adj\<close> and then hide this fact.\<close>
  by (simp add: trace_def that flip: cinner_adj_right infsum_cnj)

subsection \<open>Hilbert-Schmidt operators\<close>

definition hilbert_schmidt where \<open>hilbert_schmidt a \<longleftrightarrow> trace_class (a* o\<^sub>C\<^sub>L a)\<close>

definition hilbert_schmidt_norm where \<open>hilbert_schmidt_norm a = sqrt (trace_norm (a* o\<^sub>C\<^sub>L a))\<close>

lemma hilbert_schmidtI: \<open>hilbert_schmidt a\<close> if \<open>trace_class (a* o\<^sub>C\<^sub>L a)\<close>
  using that unfolding hilbert_schmidt_def by simp

lemma hilbert_schmidt_0[simp]: \<open>hilbert_schmidt 0\<close>
  unfolding hilbert_schmidt_def by simp

lemma hilbert_schmidt_norm_pos[simp]: \<open>hilbert_schmidt_norm a \<ge> 0\<close>
  by (auto simp: hilbert_schmidt_norm_def)

lemma has_sum_hilbert_schmidt_norm_square:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (a)\<close>
  assumes \<open>is_onb B\<close> and \<open>hilbert_schmidt a\<close>
  shows \<open>((\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) has_sum (hilbert_schmidt_norm a)\<^sup>2) B\<close>
proof -
  from \<open>hilbert_schmidt a\<close>
  have \<open>trace_class (a* o\<^sub>C\<^sub>L a)\<close>
  using hilbert_schmidt_def by blast
  with \<open>is_onb B\<close> have \<open>((\<lambda>x. cmod (x \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) *\<^sub>V x))) has_sum trace_norm (a* o\<^sub>C\<^sub>L a)) B\<close>
    by (metis (no_types, lifting) abs_op_def has_sum_cong has_sum_infsum positive_cblinfun_squareI sqrt_op_unique trace_class_def trace_norm_alt_def trace_norm_basis_invariance)
  then show ?thesis
    by (auto simp: cinner_adj_right cdot_square_norm of_real_power norm_power hilbert_schmidt_norm_def)
qed

lemma summable_hilbert_schmidt_norm_square:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (a)\<close>
  assumes \<open>is_onb B\<close> and \<open>hilbert_schmidt a\<close>
  shows \<open>(\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) summable_on B\<close>
  using assms(1) assms(2) has_sum_hilbert_schmidt_norm_square summable_on_def by blast

lemma summable_hilbert_schmidt_norm_square_converse:
  assumes \<open>is_onb B\<close>
  assumes \<open>(\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) summable_on B\<close>
  shows \<open>hilbert_schmidt a\<close>
proof -
  from assms(2)
  have \<open>(\<lambda>x. cmod (x \<bullet>\<^sub>C ((a* o\<^sub>C\<^sub>L a) *\<^sub>V x))) summable_on B\<close>
    by (metis (no_types, lifting) cblinfun_apply_cblinfun_compose cinner_adj_right cinner_pos_if_pos cmod_Re positive_cblinfun_squareI power2_norm_eq_cinner' summable_on_cong)
  then have \<open>trace_class (a* o\<^sub>C\<^sub>L a)\<close>
    by (metis (no_types, lifting) abs_op_def assms(1) positive_cblinfun_squareI sqrt_op_unique summable_on_cong trace_class_def)
  then show ?thesis
    using hilbert_schmidtI by blast
qed

lemma infsum_hilbert_schmidt_norm_square:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (a)\<close>
  assumes \<open>is_onb B\<close> and \<open>hilbert_schmidt a\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a *\<^sub>V x))\<^sup>2) = ((hilbert_schmidt_norm a)\<^sup>2)\<close>
    using assms has_sum_hilbert_schmidt_norm_square infsumI by blast


lemma 
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (d)\<close>
  assumes  \<open>hilbert_schmidt b\<close>
  shows hilbert_schmidt_comp_right: \<open>hilbert_schmidt (a o\<^sub>C\<^sub>L b)\<close>
    and hilbert_schmidt_norm_comp_right: \<open>hilbert_schmidt_norm (a o\<^sub>C\<^sub>L b) \<le> norm a * hilbert_schmidt_norm b\<close>
proof -
  define B :: \<open>'a set\<close> where \<open>B = some_chilbert_basis\<close>
  have [simp]: \<open>is_onb B\<close>
    by (simp add: B_def)

  have leq: \<open>(norm ((a o\<^sub>C\<^sub>L b) *\<^sub>V x))\<^sup>2 \<le> (norm a)\<^sup>2 * (norm (b *\<^sub>V x))\<^sup>2\<close> for x
    by (metis cblinfun_apply_cblinfun_compose norm_cblinfun norm_ge_zero power_mono power_mult_distrib)

  have \<open>(\<lambda>x. (norm (b *\<^sub>V x))\<^sup>2) summable_on B\<close>
    using \<open>is_onb B\<close> summable_hilbert_schmidt_norm_square assms by blast
  then have sum2: \<open>(\<lambda>x. (norm a)\<^sup>2 * (norm (b *\<^sub>V x))\<^sup>2) summable_on B\<close>
    using summable_on_cmult_right by blast
  then have \<open>(\<lambda>x. ((norm a)\<^sup>2 * (norm (b *\<^sub>V x))\<^sup>2)) abs_summable_on B\<close>
    by auto
  then have \<open>(\<lambda>x. (norm ((a o\<^sub>C\<^sub>L b) *\<^sub>V x))\<^sup>2) abs_summable_on B\<close>
    apply (rule abs_summable_on_comparison_test)
    using leq by force
  then have sum5: \<open>(\<lambda>x. (norm ((a o\<^sub>C\<^sub>L b) *\<^sub>V x))\<^sup>2) summable_on B\<close>
    by auto
  then show [simp]: \<open>hilbert_schmidt (a o\<^sub>C\<^sub>L b)\<close>
    using \<open>is_onb B\<close>
    by (rule summable_hilbert_schmidt_norm_square_converse[rotated])

  have \<open>(hilbert_schmidt_norm (a o\<^sub>C\<^sub>L b))\<^sup>2 = (\<Sum>\<^sub>\<infinity>x\<in>B. (norm ((a o\<^sub>C\<^sub>L b) *\<^sub>V x))\<^sup>2)\<close>
    apply (rule infsum_hilbert_schmidt_norm_square[symmetric])
    by simp_all
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>B. (norm a)\<^sup>2 * (norm (b *\<^sub>V x))\<^sup>2)\<close>
    using sum5 sum2 leq by (rule infsum_mono)
  also have \<open>\<dots> = (norm a)\<^sup>2 * (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (b *\<^sub>V x))\<^sup>2)\<close>
    by (simp add: infsum_cmult_right')
  also have \<open>\<dots> = (norm a)\<^sup>2 * (hilbert_schmidt_norm b)\<^sup>2\<close>
    by (simp add: assms infsum_hilbert_schmidt_norm_square)
  finally show \<open>hilbert_schmidt_norm (a o\<^sub>C\<^sub>L b) \<le> norm a * hilbert_schmidt_norm b\<close>
    apply (rule_tac power2_le_imp_le)
    by (auto intro!: mult_nonneg_nonneg simp: power_mult_distrib)
qed


lemma hilbert_schmidt_adj[simp]:
  \<comment> \<open>Implicit in \<^cite>\<open>conway00operator\<close>, Proposition 18.6 (b)\<close>
  assumes \<open>hilbert_schmidt a\<close>
  shows \<open>hilbert_schmidt (a*)\<close>
proof -
  from assms
  have \<open>(\<lambda>e. (norm (a *\<^sub>V e))\<^sup>2) summable_on some_chilbert_basis\<close>
    using is_onb_some_chilbert_basis summable_hilbert_schmidt_norm_square by blast
  then have \<open>(\<lambda>e. (norm (a* *\<^sub>V e))\<^sup>2) summable_on some_chilbert_basis\<close>
    by (metis basis_image_square_has_sum2 is_onb_some_chilbert_basis summable_on_def)
  then show ?thesis
    using is_onb_some_chilbert_basis summable_hilbert_schmidt_norm_square_converse by blast
qed

lemma hilbert_schmidt_norm_adj[simp]:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (b)\<close>
  shows \<open>hilbert_schmidt_norm (a*) = hilbert_schmidt_norm a\<close>
proof (cases \<open>hilbert_schmidt a\<close>)
  case True
  then have \<open>((\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) has_sum (hilbert_schmidt_norm a)\<^sup>2) some_chilbert_basis\<close>
    by (simp add: has_sum_hilbert_schmidt_norm_square)
  then have 1: \<open>((\<lambda>x. (norm (a* *\<^sub>V x))\<^sup>2) has_sum (hilbert_schmidt_norm a)\<^sup>2) some_chilbert_basis\<close>
    by (metis basis_image_square_has_sum2 is_onb_some_chilbert_basis)

  from True
  have \<open>hilbert_schmidt (a*)\<close>
    by simp
  then have 2: \<open>((\<lambda>x. (norm (a* *\<^sub>V x))\<^sup>2) has_sum (hilbert_schmidt_norm (a*))\<^sup>2) some_chilbert_basis\<close>
    by (simp add: has_sum_hilbert_schmidt_norm_square)

  from 1 2 show ?thesis
  by (metis abs_of_nonneg hilbert_schmidt_norm_pos infsumI real_sqrt_abs)
next
  case False
  then have \<open>\<not> hilbert_schmidt (a*)\<close>
    using hilbert_schmidt_adj by fastforce

  then show ?thesis
    by (metis False hilbert_schmidt_def hilbert_schmidt_norm_def trace_norm_def)
qed

lemma 
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (d)\<close>
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close> and b
  assumes  \<open>hilbert_schmidt a\<close>
  shows hilbert_schmidt_comp_left: \<open>hilbert_schmidt (a o\<^sub>C\<^sub>L b)\<close>
  apply (subst asm_rl[of \<open>a o\<^sub>C\<^sub>L b = (b* o\<^sub>C\<^sub>L a*)*\<close>], simp)
  by (auto intro!: assms hilbert_schmidt_comp_right hilbert_schmidt_adj simp del: adj_cblinfun_compose)

lemma 
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (d)\<close>
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close> and b
  assumes  \<open>hilbert_schmidt a\<close>
  shows hilbert_schmidt_norm_comp_left: \<open>hilbert_schmidt_norm (a o\<^sub>C\<^sub>L b) \<le> norm b * hilbert_schmidt_norm a\<close>
  apply (subst asm_rl[of \<open>a o\<^sub>C\<^sub>L b = (b* o\<^sub>C\<^sub>L a*)*\<close>], simp)
  using hilbert_schmidt_norm_comp_right[of \<open>a*\<close> \<open>b*\<close>]
  by (auto intro!: assms hilbert_schmidt_adj simp del: adj_cblinfun_compose)

lemma hilbert_schmidt_scaleC: \<open>hilbert_schmidt (c *\<^sub>C a)\<close> if \<open>hilbert_schmidt a\<close>
  using hilbert_schmidt_def that trace_class_scaleC by fastforce 

lemma hilbert_schmidt_scaleR: \<open>hilbert_schmidt (r *\<^sub>R a)\<close> if \<open>hilbert_schmidt a\<close>
  by (simp add: hilbert_schmidt_scaleC scaleR_scaleC that) 

lemma hilbert_schmidt_uminus: \<open>hilbert_schmidt (- a)\<close> if \<open>hilbert_schmidt a\<close>
  by (metis hilbert_schmidt_scaleC scaleC_minus1_left that) 

lemma hilbert_schmidt_plus: \<open>hilbert_schmidt (t + u)\<close> if \<open>hilbert_schmidt t\<close> and \<open>hilbert_schmidt u\<close>
  for t u :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (e).
     We use a different proof than Conway: Our proof of \<open>trace_class_plus\<close> below was easy to adapt to Hilbert-Schmidt operators,
     so we adapted that one. However, Conway's proof would most likely work as well, and possible additionally
     allow us to weaken the sort of \<^typ>\<open>'b\<close> to \<^class>\<open>complex_inner\<close>.\<close>
proof -
  define II :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'a)\<close> where \<open>II = cblinfun_left + cblinfun_right\<close>
  define JJ :: \<open>('b\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> where \<open>JJ = cblinfun_left* + cblinfun_right*\<close>
  define t2 u2 where \<open>t2 = t* o\<^sub>C\<^sub>L t\<close> and \<open>u2 = u* o\<^sub>C\<^sub>L u\<close>
  define tu :: \<open>('a\<times>'a) \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>'b)\<close> where \<open>tu = (cblinfun_left o\<^sub>C\<^sub>L t o\<^sub>C\<^sub>L cblinfun_left*) + (cblinfun_right o\<^sub>C\<^sub>L u o\<^sub>C\<^sub>L cblinfun_right*)\<close>
  define tu2 :: \<open>('a\<times>'a) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'a)\<close> where \<open>tu2 = (cblinfun_left o\<^sub>C\<^sub>L t2 o\<^sub>C\<^sub>L cblinfun_left*) + (cblinfun_right o\<^sub>C\<^sub>L u2 o\<^sub>C\<^sub>L cblinfun_right*)\<close>
  have t_plus_u: \<open>t + u = JJ o\<^sub>C\<^sub>L tu o\<^sub>C\<^sub>L II\<close>
    apply (simp add: II_def JJ_def tu_def cblinfun_compose_add_left cblinfun_compose_add_right cblinfun_compose_assoc)
    by (simp flip: cblinfun_compose_assoc)
  have tu_tu2: \<open>tu* o\<^sub>C\<^sub>L tu = tu2\<close>
    by (simp add: tu_def tu2_def t2_def u2_def cblinfun_compose_add_left 
        cblinfun_compose_add_right cblinfun_compose_assoc adj_plus
        isometryD[THEN simp_a_oCL_b] cblinfun_right_left_ortho[THEN simp_a_oCL_b]
        cblinfun_left_right_ortho[THEN simp_a_oCL_b])
  have \<open>trace_class tu2\<close>
  proof (rule trace_classI)
    define BL BR B :: \<open>('a\<times>'a) set\<close> where \<open>BL = some_chilbert_basis \<times> {0}\<close>
      and \<open>BR = {0} \<times> some_chilbert_basis\<close>
      and \<open>B = BL \<union> BR\<close>
    have \<open>BL \<inter> BR = {}\<close>
      using is_ortho_set_some_chilbert_basis
      by (auto simp: BL_def BR_def is_ortho_set_def)
    show \<open>is_onb B\<close>
      by (simp add: BL_def BR_def B_def is_onb_prod)
    have \<open>tu2 \<ge> 0\<close>
      by (auto intro!: positive_cblinfunI simp: t2_def u2_def cinner_adj_right tu2_def cblinfun.add_left cinner_pos_if_pos)
    then have abs_tu2: \<open>abs_op tu2 = tu2\<close>
      by (metis abs_opI)
    have abs_t2: \<open>abs_op t2 = t2\<close>
      by (metis abs_opI positive_cblinfun_squareI t2_def)
    have abs_u2: \<open>abs_op u2 = u2\<close>
      by (metis abs_opI positive_cblinfun_squareI u2_def)

    from that(1)
    have \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op t2 *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
      by (simp add: hilbert_schmidt_def t2_def trace_class_iff_summable[OF is_onb_some_chilbert_basis])
    then have \<open>(\<lambda>x. x \<bullet>\<^sub>C (t2 *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
      by (simp add: abs_t2)
    then have sum_BL: \<open>(\<lambda>x. x \<bullet>\<^sub>C (tu2 *\<^sub>V x)) abs_summable_on BL\<close>
      apply (subst asm_rl[of \<open>BL = (\<lambda>x. (x,0)) ` some_chilbert_basis\<close>])
      by (auto simp: BL_def summable_on_reindex inj_on_def o_def tu2_def cblinfun.add_left)
    from that(2)
    have \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op u2 *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
      by (simp add: hilbert_schmidt_def u2_def trace_class_iff_summable[OF is_onb_some_chilbert_basis])
    then have \<open>(\<lambda>x. x \<bullet>\<^sub>C (u2 *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
      by (simp add: abs_u2)
    then have sum_BR: \<open>(\<lambda>x. x \<bullet>\<^sub>C (tu2 *\<^sub>V x)) abs_summable_on BR\<close>
      apply (subst asm_rl[of \<open>BR = (\<lambda>x. (0,x)) ` some_chilbert_basis\<close>])
      by (auto simp: BR_def summable_on_reindex inj_on_def o_def tu2_def cblinfun.add_left)
    from sum_BL sum_BR
    show \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op tu2 *\<^sub>V x)) abs_summable_on B\<close>
      using \<open>BL \<inter> BR = {}\<close>
      by (auto intro!: summable_on_Un_disjoint simp: B_def abs_tu2)
  qed
  then have \<open>hilbert_schmidt tu\<close>
    by (auto simp flip: tu_tu2 intro!: hilbert_schmidtI)
  with t_plus_u
  show \<open>hilbert_schmidt (t + u)\<close>
    by (auto intro: hilbert_schmidt_comp_left hilbert_schmidt_comp_right)
qed

lemma hilbert_schmidt_minus: \<open>hilbert_schmidt (a - b)\<close> if \<open>hilbert_schmidt a\<close> and \<open>hilbert_schmidt b\<close>
  for a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  using hilbert_schmidt_plus hilbert_schmidt_uminus that(1) that(2) by fastforce

typedef (overloaded) ('a::chilbert_space,'b::complex_inner) hilbert_schmidt = \<open>Collect hilbert_schmidt :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
  by (auto intro!: exI[of _ 0])
setup_lifting type_definition_hilbert_schmidt

instantiation hilbert_schmidt :: (chilbert_space, chilbert_space) 
  "{zero,scaleC,uminus,plus,minus,dist_norm,sgn_div_norm,uniformity_dist,open_uniformity}" begin
lift_definition zero_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt\<close> is 0 by auto
lift_definition norm_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt \<Rightarrow> real\<close> is hilbert_schmidt_norm .
lift_definition scaleC_hilbert_schmidt :: \<open>complex \<Rightarrow> ('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt\<close> is scaleC
  by (simp add: hilbert_schmidt_scaleC)
lift_definition scaleR_hilbert_schmidt :: \<open>real \<Rightarrow> ('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt\<close> is scaleR
  by (simp add: hilbert_schmidt_scaleR)
lift_definition uminus_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt\<close> is uminus
  by (simp add: hilbert_schmidt_uminus)
lift_definition minus_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt\<close> is minus
  by (simp add: hilbert_schmidt_minus)
lift_definition plus_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt\<close> is plus
  by (simp add: hilbert_schmidt_plus)
definition \<open>dist a b = norm (a - b)\<close> for a b :: \<open>('a,'b) hilbert_schmidt\<close>
definition \<open>sgn x = inverse (norm x) *\<^sub>R x\<close> for x :: \<open>('a,'b) hilbert_schmidt\<close>
definition \<open>uniformity = (INF e\<in>{0<..}. principal {(x::('a,'b) hilbert_schmidt, y). dist x y < e})\<close>
definition \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e\<in>{0<..}. principal {(x, y). norm (x - y) < e}. x' = x \<longrightarrow> y \<in> U)\<close> for U :: \<open>('a,'b) hilbert_schmidt set\<close>
instance
proof intro_classes
  show \<open>(*\<^sub>R) r = ((*\<^sub>C) (complex_of_real r) :: ('a,'b) hilbert_schmidt \<Rightarrow> _)\<close> for r :: real
    apply (rule ext)
    apply transfer
    by (auto simp: scaleR_scaleC)
  show \<open>dist x y = norm (x - y)\<close> for x y :: \<open>('a,'b) hilbert_schmidt\<close>
    by (simp add: dist_hilbert_schmidt_def)
  show \<open>sgn x = inverse (norm x) *\<^sub>R x\<close> for x :: \<open>('a,'b) hilbert_schmidt\<close>
    by (simp add: Trace_Class.sgn_hilbert_schmidt_def)
  show \<open>uniformity = (INF e\<in>{0<..}. principal {(x::('a,'b) hilbert_schmidt, y). dist x y < e})\<close>
    using Trace_Class.uniformity_hilbert_schmidt_def by blast
  show \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)\<close> for U :: \<open>('a,'b) hilbert_schmidt set\<close>
    by (simp add: uniformity_hilbert_schmidt_def open_hilbert_schmidt_def dist_hilbert_schmidt_def)
qed
end

lift_definition hs_compose :: \<open>('b::chilbert_space,'c::complex_inner) hilbert_schmidt 
                               \<Rightarrow> ('a::chilbert_space,'b) hilbert_schmidt \<Rightarrow> ('a,'c) hilbert_schmidt\<close> is
    cblinfun_compose
  by (simp add: hilbert_schmidt_comp_right)

lemma
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, 18.8 Proposition\<close>
  fixes A :: \<open>'a :: chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b :: chilbert_space\<close>
  shows trace_class_iff_sqrt_hs: \<open>trace_class A \<longleftrightarrow> hilbert_schmidt (sqrt_op (abs_op A))\<close> (is ?thesis1)
    and trace_class_iff_hs_times_hs: \<open>trace_class A \<longleftrightarrow> (\<exists>B (C::'a\<Rightarrow>\<^sub>C\<^sub>L'a). hilbert_schmidt B \<and> hilbert_schmidt C \<and> A = B o\<^sub>C\<^sub>L C)\<close> (is ?thesis2)
    and trace_class_iff_abs_hs_times_hs: \<open>trace_class A \<longleftrightarrow> (\<exists>B (C::'a\<Rightarrow>\<^sub>C\<^sub>L'a). hilbert_schmidt B \<and> hilbert_schmidt C \<and> abs_op A = B o\<^sub>C\<^sub>L C)\<close> (is ?thesis3)
proof -
  define Sq W where \<open>Sq = sqrt_op (abs_op A)\<close> and \<open>W = polar_decomposition A\<close>
  have trace_class_sqrt_hs: \<open>hilbert_schmidt Sq\<close> if \<open>trace_class A\<close>
  proof (rule hilbert_schmidtI)
    from that
    have \<open>trace_class (abs_op A)\<close>
      by simp
    then show \<open>trace_class (Sq* o\<^sub>C\<^sub>L Sq)\<close>
      by (auto simp: Sq_def positive_hermitianI)
  qed
  have sqrt_hs_hs_times_hs: \<open>\<exists>B (C :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a). hilbert_schmidt B \<and> hilbert_schmidt C \<and> A = B o\<^sub>C\<^sub>L C\<close>
    if \<open>hilbert_schmidt Sq\<close>
  proof -
    have \<open>A = W o\<^sub>C\<^sub>L abs_op A\<close>
      by (simp add: polar_decomposition_correct W_def)
    also have \<open>\<dots> = (W o\<^sub>C\<^sub>L Sq) o\<^sub>C\<^sub>L Sq\<close>
      by (metis Sq_def abs_op_pos cblinfun_compose_assoc positive_hermitianI sqrt_op_pos sqrt_op_square)
    finally have \<open>A = (W o\<^sub>C\<^sub>L Sq) o\<^sub>C\<^sub>L Sq\<close>
      by -
    then show ?thesis
      apply (rule_tac exI[of _ \<open>W o\<^sub>C\<^sub>L Sq\<close>], rule_tac exI[of _ Sq])
      using that by (auto simp add: hilbert_schmidt_comp_right)
  qed
  have hs_times_hs_abs_hs_times_hs: \<open>\<exists>B (C :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a). hilbert_schmidt B \<and> hilbert_schmidt C \<and> abs_op A = B o\<^sub>C\<^sub>L C\<close>
    if \<open>\<exists>B (C :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a). hilbert_schmidt B \<and> hilbert_schmidt C \<and> A = B o\<^sub>C\<^sub>L C\<close>
  proof -
    from that obtain B and C :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where \<open>hilbert_schmidt B\<close> and \<open>hilbert_schmidt C\<close> and ABC: \<open>A = B o\<^sub>C\<^sub>L C\<close>
      by auto
    from \<open>hilbert_schmidt B\<close>
    have hs_WB: \<open>hilbert_schmidt (W* o\<^sub>C\<^sub>L B)\<close>
      by (simp add: hilbert_schmidt_comp_right)
    have \<open>abs_op A = W* o\<^sub>C\<^sub>L A\<close>
      by (simp add: W_def polar_decomposition_correct')
    also have \<open>\<dots> = (W* o\<^sub>C\<^sub>L B) o\<^sub>C\<^sub>L C\<close>
      by (metis ABC cblinfun_compose_assoc)
    finally have \<open>abs_op A = (W* o\<^sub>C\<^sub>L B) o\<^sub>C\<^sub>L C\<close>
      by -
    with hs_WB \<open>hilbert_schmidt C\<close>
    show ?thesis
      by auto
  qed
  have abs_hs_times_hs_trace_class: \<open>trace_class A\<close>
    if \<open>\<exists>B (C :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a). hilbert_schmidt B \<and> hilbert_schmidt C \<and> abs_op A = B o\<^sub>C\<^sub>L C\<close>
  proof -
    from that obtain B and C :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where \<open>hilbert_schmidt B\<close> and \<open>hilbert_schmidt C\<close> and ABC: \<open>abs_op A = B o\<^sub>C\<^sub>L C\<close>
      by auto
    from \<open>hilbert_schmidt B\<close>
    have \<open>hilbert_schmidt (B*)\<close>
      by simp
    then have \<open>(\<lambda>e. (norm (B* *\<^sub>V e))\<^sup>2) abs_summable_on some_chilbert_basis\<close>
      by (metis is_onb_some_chilbert_basis summable_hilbert_schmidt_norm_square summable_on_iff_abs_summable_on_real)
    moreover 
    from \<open>hilbert_schmidt C\<close>
    have \<open>(\<lambda>e. (norm (C *\<^sub>V e))\<^sup>2) abs_summable_on some_chilbert_basis\<close>
      by (metis is_onb_some_chilbert_basis summable_hilbert_schmidt_norm_square summable_on_iff_abs_summable_on_real)
    ultimately have \<open>(\<lambda>e. norm (B* *\<^sub>V e) * norm (C *\<^sub>V e)) abs_summable_on some_chilbert_basis\<close>
      apply (rule_tac abs_summable_product)
      by (metis (no_types, lifting) power2_eq_square summable_on_cong)+
    then have \<open>(\<lambda>e. cinner e (abs_op A *\<^sub>V e)) abs_summable_on some_chilbert_basis\<close>
    proof (rule Infinite_Sum.abs_summable_on_comparison_test)
      fix e :: 'a assume \<open>e \<in> some_chilbert_basis\<close>
      have \<open>norm (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) = norm ((B* *\<^sub>V e) \<bullet>\<^sub>C (C *\<^sub>V e))\<close>
        by (simp add: ABC cinner_adj_left)
      also have \<open>\<dots> \<le> norm (B* *\<^sub>V e) * norm (C *\<^sub>V e)\<close>
        by (rule Cauchy_Schwarz_ineq2)
      also have \<open>\<dots> = norm (norm (B* *\<^sub>V e) * norm (C *\<^sub>V e))\<close>
        by simp
      finally show \<open>cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) \<le> norm (norm (B* *\<^sub>V e) * norm (C *\<^sub>V e))\<close>
        by -
    qed
    then show \<open>trace_class A\<close>
      apply (rule trace_classI[rotated]) by simp
  qed
  from trace_class_sqrt_hs sqrt_hs_hs_times_hs hs_times_hs_abs_hs_times_hs abs_hs_times_hs_trace_class
  show ?thesis1 and ?thesis2 and ?thesis3
    unfolding Sq_def by metis+
qed


lemma trace_exists:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.9\<close>
  assumes \<open>is_onb B\<close> and \<open>trace_class A\<close>
  shows \<open>(\<lambda>e. e \<bullet>\<^sub>C (A *\<^sub>V e)) summable_on B\<close>
proof -
  obtain b c :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where \<open>hilbert_schmidt b\<close> \<open>hilbert_schmidt c\<close> and Abc: \<open>A = c* o\<^sub>C\<^sub>L b\<close>
    by (metis abs_op_pos adj_cblinfun_compose assms(2) double_adj hilbert_schmidt_comp_left hilbert_schmidt_comp_right polar_decomposition_correct polar_decomposition_correct' positive_hermitianI trace_class_iff_hs_times_hs)


  have \<open>(\<lambda>e. (norm (b *\<^sub>V e))\<^sup>2) summable_on B\<close>
    using \<open>hilbert_schmidt b\<close> assms(1) summable_hilbert_schmidt_norm_square by auto
  moreover have \<open>(\<lambda>e. (norm (c *\<^sub>V e))\<^sup>2) summable_on B\<close>
    using \<open>hilbert_schmidt c\<close> assms(1) summable_hilbert_schmidt_norm_square by auto
  ultimately have \<open>(\<lambda>e. (((norm (b *\<^sub>V e))\<^sup>2 + (norm (c *\<^sub>V e))\<^sup>2)) / 2) summable_on B\<close>
    by (auto intro!: summable_on_cdivide summable_on_add)

  then have \<open>(\<lambda>e. (((norm (b *\<^sub>V e))\<^sup>2 + (norm (c *\<^sub>V e))\<^sup>2)) / 2) abs_summable_on B\<close>
    by simp

  then have \<open>(\<lambda>e. e \<bullet>\<^sub>C (A *\<^sub>V e)) abs_summable_on B\<close>
  proof (rule abs_summable_on_comparison_test)
    fix e assume \<open>e \<in> B\<close>
    obtain \<gamma> where \<open>cmod \<gamma> = 1\<close> and \<gamma>: \<open>\<gamma> * ((b *\<^sub>V e) \<bullet>\<^sub>C (c *\<^sub>V e)) = abs ((b *\<^sub>V e) \<bullet>\<^sub>C (c *\<^sub>V e))\<close>
      apply atomize_elim
      apply (cases \<open>(b *\<^sub>V e) \<bullet>\<^sub>C (c *\<^sub>V e) \<noteq> 0\<close>)
       apply (rule exI[of _ \<open>cnj (sgn ((b *\<^sub>V e) \<bullet>\<^sub>C (c *\<^sub>V e)))\<close>])
       apply (auto simp add: norm_sgn intro!: norm_one)
      by (metis (no_types, lifting) abs_mult_sgn cblinfun.scaleC_right cblinfun_mult_right.rep_eq cdot_square_norm complex_norm_square complex_scaleC_def mult.comm_neutral norm_one norm_sgn one_cinner_one)

    have \<open>cmod (e \<bullet>\<^sub>C (A *\<^sub>V e)) = Re (abs (e \<bullet>\<^sub>C (A *\<^sub>V e)))\<close>
      by (metis abs_nn cmod_Re norm_abs)
    also have \<open>\<dots> = Re (abs ((b *\<^sub>V e) \<bullet>\<^sub>C (c *\<^sub>V e)))\<close>
      by (metis (mono_tags, lifting) Abc abs_nn cblinfun_apply_cblinfun_compose cinner_adj_left cinner_commute' complex_mod_cnj complex_of_real_cmod norm_abs)
    also have \<open>\<dots> = Re (((b *\<^sub>V e) \<bullet>\<^sub>C (\<gamma> *\<^sub>C (c *\<^sub>V e))))\<close>
      by (simp add: \<gamma>)
    also have \<open>\<dots> \<le> ((norm (b *\<^sub>V e))\<^sup>2 + (norm (\<gamma> *\<^sub>C (c *\<^sub>V e)))\<^sup>2) / 2\<close>
      by (smt (z3) field_sum_of_halves norm_ge_zero polar_identity_minus zero_le_power_eq_numeral)
    also have \<open>\<dots> = ((norm (b *\<^sub>V e))\<^sup>2 + (norm (c *\<^sub>V e))\<^sup>2) / 2\<close>
      by (simp add: \<open>cmod \<gamma> = 1\<close>)
    also have \<open>\<dots> \<le> norm (((norm (b *\<^sub>V e))\<^sup>2 + (norm (c *\<^sub>V e))\<^sup>2) / 2)\<close>
      by simp
    finally show \<open>cmod (e \<bullet>\<^sub>C (A *\<^sub>V e)) \<le> norm (((norm (b *\<^sub>V e))\<^sup>2 + (norm (c *\<^sub>V e))\<^sup>2) / 2)\<close>
      by -
  qed

  then show ?thesis
    by (metis abs_summable_summable)
    
qed


lemma trace_plus_prelim: 
  assumes \<open>trace_class a\<close> \<open>trace_class b\<close> \<open>trace_class (a+b)\<close>
    \<comment> \<open>We will later strengthen this as \<open>trace_plus\<close> and then hide this fact.\<close>
  shows \<open>trace (a + b) = trace a + trace b\<close>
  by (auto simp add: assms infsum_add trace_def cblinfun.add_left cinner_add_right
      intro!: infsum_add trace_exists)

lemma hs_times_hs_trace_class: 
  fixes B :: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close> and C :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>hilbert_schmidt B\<close> and \<open>hilbert_schmidt C\<close>
  shows \<open>trace_class (B o\<^sub>C\<^sub>L C)\<close>
  \<comment> \<open>Not an immediate consequence of @{thm [source] trace_class_iff_hs_times_hs} because here the types of \<^term>\<open>B\<close>, \<^term>\<open>C\<close> are more general.\<close>
proof -
  define A Sq W where \<open>A = B o\<^sub>C\<^sub>L C\<close> and \<open>Sq = sqrt_op (abs_op A)\<close> and \<open>W = polar_decomposition A\<close>

  from \<open>hilbert_schmidt B\<close>
  have hs_WB: \<open>hilbert_schmidt (W* o\<^sub>C\<^sub>L B)\<close>
    by (simp add: hilbert_schmidt_comp_right)
  have \<open>abs_op A = W* o\<^sub>C\<^sub>L A\<close>
    by (simp add: W_def polar_decomposition_correct')
  also have \<open>\<dots> = (W* o\<^sub>C\<^sub>L B) o\<^sub>C\<^sub>L C\<close>
    by (metis A_def cblinfun_compose_assoc)
  finally have abs_op_A: \<open>abs_op A = (W* o\<^sub>C\<^sub>L B) o\<^sub>C\<^sub>L C\<close>
    by -
  from \<open>hilbert_schmidt (W* o\<^sub>C\<^sub>L B)\<close>
  have \<open>hilbert_schmidt (B* o\<^sub>C\<^sub>L W)\<close>
    by (simp add: assms(1) hilbert_schmidt_comp_left)
  then have \<open>(\<lambda>e. (norm ((B* o\<^sub>C\<^sub>L W) *\<^sub>V e))\<^sup>2) abs_summable_on some_chilbert_basis\<close>
    by (metis is_onb_some_chilbert_basis summable_hilbert_schmidt_norm_square summable_on_iff_abs_summable_on_real)
  moreover from \<open>hilbert_schmidt C\<close>
  have \<open>(\<lambda>e. (norm (C *\<^sub>V e))\<^sup>2) abs_summable_on some_chilbert_basis\<close>
    by (metis is_onb_some_chilbert_basis summable_hilbert_schmidt_norm_square summable_on_iff_abs_summable_on_real)
  ultimately have \<open>(\<lambda>e. norm ((B* o\<^sub>C\<^sub>L W) *\<^sub>V e) * norm (C *\<^sub>V e)) abs_summable_on some_chilbert_basis\<close>
    apply (rule_tac abs_summable_product)
    by (metis (no_types, lifting) power2_eq_square summable_on_cong)+
  then have \<open>(\<lambda>e. cinner e (abs_op A *\<^sub>V e)) abs_summable_on some_chilbert_basis\<close>
  proof (rule Infinite_Sum.abs_summable_on_comparison_test)
    fix e :: 'a assume \<open>e \<in> some_chilbert_basis\<close>
    have \<open>norm (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) = norm (((B* o\<^sub>C\<^sub>L W) *\<^sub>V e) \<bullet>\<^sub>C (C *\<^sub>V e))\<close>
      by (simp add: abs_op_A cinner_adj_left cinner_adj_right)
    also have \<open>\<dots> \<le> norm ((B* o\<^sub>C\<^sub>L W) *\<^sub>V e) * norm (C *\<^sub>V e)\<close>
      by (rule Cauchy_Schwarz_ineq2)
    also have \<open>\<dots> = norm (norm ((B* o\<^sub>C\<^sub>L W) *\<^sub>V e) * norm (C *\<^sub>V e))\<close>
      by simp
    finally show \<open>cmod (e \<bullet>\<^sub>C (abs_op A *\<^sub>V e)) \<le> norm (norm ((B* o\<^sub>C\<^sub>L W) *\<^sub>V e) * norm (C *\<^sub>V e))\<close>
      by -
  qed
  then show \<open>trace_class A\<close>
    apply (rule trace_classI[rotated]) by simp
qed

instantiation hilbert_schmidt :: (chilbert_space, chilbert_space) complex_vector begin
instance
proof intro_classes
  fix a b c :: \<open>('a,'b) hilbert_schmidt\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer by auto
  show \<open>a + b = b + a\<close>
    apply transfer by auto
  show \<open>0 + a = a\<close>
    apply transfer by auto
  show \<open>- a + a = 0\<close>
    apply transfer by auto
  show \<open>a - b = a + - b\<close>
    apply transfer by auto
  show \<open>r *\<^sub>C (a + b) = r *\<^sub>C a + r *\<^sub>C b\<close> for r :: complex
    apply transfer
    using scaleC_add_right 
    by auto
  show \<open>(r + r') *\<^sub>C a = r *\<^sub>C a + r' *\<^sub>C a\<close> for r r' :: complex
    apply transfer
    by (simp add: scaleC_add_left)
  show \<open>r *\<^sub>C r' *\<^sub>C a = (r * r') *\<^sub>C a\<close> for r r'
    apply transfer by auto
  show \<open>1 *\<^sub>C a = a\<close>
    apply transfer by auto
qed
end (* instantiation hilbert_schmidt :: complex_vector *)


instantiation hilbert_schmidt :: (chilbert_space, chilbert_space) "complex_inner" begin
lift_definition cinner_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt \<Rightarrow> ('a,'b) hilbert_schmidt \<Rightarrow> complex\<close> is
  \<open>\<lambda>b c. trace (b* o\<^sub>C\<^sub>L c)\<close> .
instance
proof intro_classes
  fix x y z :: \<open>('a,'b) hilbert_schmidt\<close>
  show \<open>x \<bullet>\<^sub>C y = cnj (y \<bullet>\<^sub>C x)\<close>
  proof (transfer; unfold mem_Collect_eq)
    fix x y :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    assume hs_xy: \<open>hilbert_schmidt x\<close> \<open>hilbert_schmidt y\<close>
    then have tc: \<open>trace_class ((y* o\<^sub>C\<^sub>L x)*)\<close> \<open>trace_class (y* o\<^sub>C\<^sub>L x)\<close>
      by (auto intro!: hs_times_hs_trace_class)
    have \<open>trace (x* o\<^sub>C\<^sub>L y) = trace ((y* o\<^sub>C\<^sub>L x)*)\<close>
      by simp
    also have \<open>\<dots> = cnj (trace (y* o\<^sub>C\<^sub>L x))\<close>
      using tc trace_adj_prelim by blast
    finally show \<open>trace (x* o\<^sub>C\<^sub>L y) = cnj (trace (y* o\<^sub>C\<^sub>L x))\<close>
      by -
  qed
  show \<open>(x + y) \<bullet>\<^sub>C z = x \<bullet>\<^sub>C z + y \<bullet>\<^sub>C z\<close>
  proof (transfer; unfold mem_Collect_eq) 
    fix x y z :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    assume [simp]: \<open>hilbert_schmidt x\<close> \<open>hilbert_schmidt y\<close> \<open>hilbert_schmidt z\<close>
    have [simp]: \<open>trace_class ((x + y)* o\<^sub>C\<^sub>L z)\<close> \<open>trace_class (x* o\<^sub>C\<^sub>L z)\<close> \<open>trace_class (y* o\<^sub>C\<^sub>L z)\<close>
      by (auto intro!: hs_times_hs_trace_class hilbert_schmidt_adj hilbert_schmidt_plus)
    then have [simp]: \<open>trace_class ((x* o\<^sub>C\<^sub>L z) + (y* o\<^sub>C\<^sub>L z))\<close>
      by (simp add: adj_plus cblinfun_compose_add_left)
    show \<open>trace ((x + y)* o\<^sub>C\<^sub>L z) = trace (x* o\<^sub>C\<^sub>L z) + trace (y* o\<^sub>C\<^sub>L z)\<close>
      by (simp add: trace_plus_prelim adj_plus cblinfun_compose_add_left hs_times_hs_trace_class)
  qed
  show \<open>r *\<^sub>C x \<bullet>\<^sub>C y = cnj r * (x \<bullet>\<^sub>C y)\<close> for r
    apply transfer 
    by (simp add: trace_scaleC)
  show \<open>0 \<le> x \<bullet>\<^sub>C x\<close>
    apply transfer
    by (simp add: positive_cblinfun_squareI trace_pos)
  show \<open>(x \<bullet>\<^sub>C x = 0) = (x = 0)\<close>
  proof (transfer; unfold mem_Collect_eq)
    fix x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    assume [simp]: \<open>hilbert_schmidt x\<close>
    have \<open>trace (x* o\<^sub>C\<^sub>L x) = 0 \<longleftrightarrow> trace (abs_op (x* o\<^sub>C\<^sub>L x)) = 0\<close>
      by (metis abs_op_def positive_cblinfun_squareI sqrt_op_unique)
    also have \<open>\<dots> \<longleftrightarrow> trace_norm (x* o\<^sub>C\<^sub>L x) = 0\<close>
      by simp
    also have \<open>\<dots> \<longleftrightarrow> x* o\<^sub>C\<^sub>L x = 0\<close>
      by (metis \<open>hilbert_schmidt x\<close> hilbert_schmidt_def trace_norm_0 trace_norm_nondegenerate)
    also have \<open>\<dots> \<longleftrightarrow> x = 0\<close>
      using cblinfun_compose_zero_right op_square_nondegenerate by blast
    finally show \<open>trace (x* o\<^sub>C\<^sub>L x) = 0 \<longleftrightarrow> x = 0\<close>
      by -
  qed
  show \<open>norm x = sqrt (cmod (x \<bullet>\<^sub>C x))\<close>
    apply transfer
    apply (auto simp: hilbert_schmidt_norm_def)
    by (metis Re_complex_of_real cmod_Re positive_cblinfun_squareI trace_norm_pos trace_pos)
qed
end

lemma hilbert_schmidt_norm_triangle_ineq:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (e). We do not use their proof but get it as a
  simple corollary of the instantiation of \<open>hilbert_schmidt\<close> as a inner product space.
  The proof by Conway would probably allow us to weaken the sort of \<^typ>\<open>'b\<close> to \<^class>\<open>complex_inner\<close>.\<close>
  fixes a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>hilbert_schmidt a\<close> \<open>hilbert_schmidt b\<close>
  shows \<open>hilbert_schmidt_norm (a + b) \<le> hilbert_schmidt_norm a + hilbert_schmidt_norm b\<close>
proof -
  define a' b' where \<open>a' = Abs_hilbert_schmidt a\<close> and \<open>b' = Abs_hilbert_schmidt b\<close>
  have [transfer_rule]: \<open>cr_hilbert_schmidt a a'\<close>
    by (simp add: Abs_hilbert_schmidt_inverse a'_def assms(1) cr_hilbert_schmidt_def)
  have [transfer_rule]: \<open>cr_hilbert_schmidt b b'\<close>
    by (simp add: Abs_hilbert_schmidt_inverse assms(2) b'_def cr_hilbert_schmidt_def)
  have \<open>norm (a' + b') \<le> norm a' + norm b'\<close>
    by (rule norm_triangle_ineq)
  then show ?thesis
    apply transfer
    by -
qed

lift_definition adj_hs :: \<open>('a::chilbert_space,'b::chilbert_space) hilbert_schmidt \<Rightarrow> ('b,'a) hilbert_schmidt\<close> is adj
  by auto

lemma adj_hs_plus: \<open>adj_hs (x + y) = adj_hs x + adj_hs y\<close>
  apply transfer 
  by (simp add: adj_plus)

lemma adj_hs_minus: \<open>adj_hs (x - y) = adj_hs x - adj_hs y\<close>
  apply transfer 
  by (simp add: adj_minus)

lemma norm_adj_hs[simp]: \<open>norm (adj_hs x) = norm x\<close>
  apply transfer
  by simp

lemma hilbert_schmidt_norm_geq_norm:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.6 (c)\<close>
  assumes \<open>hilbert_schmidt a\<close>
  shows \<open>norm a \<le> hilbert_schmidt_norm a\<close>
proof -
  have \<open>norm (a x) \<le> hilbert_schmidt_norm a\<close> if \<open>norm x = 1\<close> for x
  proof -
    obtain B where \<open>x \<in> B\<close> and \<open>is_onb B\<close>
      using orthonormal_basis_exists[of \<open>{x}\<close>] \<open>norm x = 1\<close>
      by force
    have \<open>(norm (a x))\<^sup>2 = (\<Sum>\<^sub>\<infinity>x\<in>{x}. (norm (a x))\<^sup>2)\<close>
      by simp
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a x))\<^sup>2)\<close>
      apply (rule infsum_mono_neutral)
      by (auto intro!: summable_hilbert_schmidt_norm_square \<open>is_onb B\<close> assms \<open>x \<in> B\<close>)
    also have \<open>\<dots> = (hilbert_schmidt_norm a)\<^sup>2\<close>
      using infsum_hilbert_schmidt_norm_square[OF \<open>is_onb B\<close> assms]
      by -
    finally show ?thesis
      by force
  qed
  then show ?thesis
    by (auto intro!: norm_cblinfun_bound_unit)
qed


subsection \<open>Trace-norm and trace-class, continued\<close>

lemma trace_class_comp_left: \<open>trace_class (a o\<^sub>C\<^sub>L b)\<close> if \<open>trace_class a\<close> for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (a)\<close>
proof -
  from \<open>trace_class a\<close>
  obtain C :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and B where \<open>hilbert_schmidt C\<close> and \<open>hilbert_schmidt B\<close> and aCB: \<open>a = C o\<^sub>C\<^sub>L B\<close>
    by (auto simp: trace_class_iff_hs_times_hs)
  from \<open>hilbert_schmidt B\<close> have \<open>hilbert_schmidt (B o\<^sub>C\<^sub>L b)\<close>
    by (simp add: hilbert_schmidt_comp_left)
  with \<open>hilbert_schmidt C\<close> have \<open>trace_class (C o\<^sub>C\<^sub>L (B o\<^sub>C\<^sub>L b))\<close>
    using hs_times_hs_trace_class by blast
  then show ?thesis
    by (simp flip: aCB cblinfun_compose_assoc) 
qed

lemma trace_class_comp_right: \<open>trace_class (a o\<^sub>C\<^sub>L b)\<close> if \<open>trace_class b\<close> for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (a)\<close>
proof -
  from \<open>trace_class b\<close>
  obtain C :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and B where \<open>hilbert_schmidt C\<close> and \<open>hilbert_schmidt B\<close> and aCB: \<open>b = C o\<^sub>C\<^sub>L B\<close>
    by (auto simp: trace_class_iff_hs_times_hs)
  from \<open>hilbert_schmidt C\<close> have \<open>hilbert_schmidt (a o\<^sub>C\<^sub>L C)\<close>
    by (simp add: hilbert_schmidt_comp_right)
  with \<open>hilbert_schmidt B\<close> have \<open>trace_class ((a o\<^sub>C\<^sub>L C) o\<^sub>C\<^sub>L B)\<close>
    using hs_times_hs_trace_class by blast
  then show ?thesis
    by (simp flip: aCB add: cblinfun_compose_assoc) 
qed

lemma 
  fixes B :: \<open>'a::chilbert_space set\<close> and A :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and b :: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close> and c :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> 
  shows trace_alt_def:
    \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Proposition 18.9\<close>
    \<open>is_onb B \<Longrightarrow> trace A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>B. e \<bullet>\<^sub>C (A *\<^sub>V e)) else 0)\<close>
    and trace_hs_times_hs: \<open>hilbert_schmidt c \<Longrightarrow> hilbert_schmidt b \<Longrightarrow> trace (c o\<^sub>C\<^sub>L b) = 
          ((of_real (hilbert_schmidt_norm ((c*) + b)))\<^sup>2 - (of_real (hilbert_schmidt_norm ((c*) - b)))\<^sup>2 -
                      \<i> * (of_real (hilbert_schmidt_norm (((c*) + \<i> *\<^sub>C b))))\<^sup>2 +
                      \<i> * (of_real (hilbert_schmidt_norm (((c*) - \<i> *\<^sub>C b))))\<^sup>2) / 4\<close>
proof -
  have ecbe_has_sum: \<open>((\<lambda>e. e \<bullet>\<^sub>C ((c o\<^sub>C\<^sub>L b) *\<^sub>V e)) has_sum
          ((of_real (hilbert_schmidt_norm ((c*) + b)))\<^sup>2 - (of_real (hilbert_schmidt_norm ((c*) - b)))\<^sup>2 -
            \<i> * (of_real (hilbert_schmidt_norm ((c*) + \<i> *\<^sub>C b)))\<^sup>2 +
            \<i> * (of_real (hilbert_schmidt_norm ((c*) - \<i> *\<^sub>C b)))\<^sup>2) / 4) B\<close>
    if \<open>is_onb B\<close> and \<open>hilbert_schmidt c\<close> and \<open>hilbert_schmidt b\<close> for B :: \<open>'y::chilbert_space set\<close> and c :: \<open>'x::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'y\<close> and b
    apply (simp flip: cinner_adj_left[of c])
    apply (subst cdot_norm)
    using that by (auto simp add: field_class.field_divide_inverse infsum_cmult_left'
        simp del: Num.inverse_eq_divide_numeral
        simp flip: cblinfun.add_left cblinfun.diff_left cblinfun.scaleC_left of_real_power
        intro!: has_sum_cmult_left has_sum_cmult_right has_sum_add has_sum_diff has_sum_of_real
        has_sum_hilbert_schmidt_norm_square hilbert_schmidt_plus hilbert_schmidt_minus hilbert_schmidt_scaleC)

  then have ecbe_infsum: \<open>(\<Sum>\<^sub>\<infinity>e\<in>B. e \<bullet>\<^sub>C ((c o\<^sub>C\<^sub>L b) *\<^sub>V e)) =
          (((of_real (hilbert_schmidt_norm ((c*) + b)))\<^sup>2 - (of_real (hilbert_schmidt_norm ((c*) - b)))\<^sup>2 -
            \<i> * (of_real (hilbert_schmidt_norm ((c*) + \<i> *\<^sub>C b)))\<^sup>2 +
            \<i> * (of_real (hilbert_schmidt_norm ((c*) - \<i> *\<^sub>C b)))\<^sup>2) / 4)\<close>
    if \<open>is_onb B\<close> and \<open>hilbert_schmidt c\<close> and \<open>hilbert_schmidt b\<close> for B :: \<open>'y::chilbert_space set\<close> and c :: \<open>'x::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'y\<close> and b
    using infsumI that(1) that(2) that(3) by blast

  show \<open>trace (c o\<^sub>C\<^sub>L b) = 
        ((of_real (hilbert_schmidt_norm ((c*) + b)))\<^sup>2 - (of_real (hilbert_schmidt_norm ((c*) - b)))\<^sup>2 -
            \<i> * (of_real (hilbert_schmidt_norm ((c*) + \<i> *\<^sub>C b)))\<^sup>2 +
            \<i> * (of_real (hilbert_schmidt_norm ((c*) - \<i> *\<^sub>C b)))\<^sup>2) / 4\<close>
    if \<open>hilbert_schmidt c\<close> and \<open>hilbert_schmidt b\<close>
  proof -
    from that have tc_cb[simp]: \<open>trace_class (c o\<^sub>C\<^sub>L b)\<close>
      by (rule hs_times_hs_trace_class)
    show ?thesis
      using ecbe_infsum[OF is_onb_some_chilbert_basis \<open>hilbert_schmidt c\<close> \<open>hilbert_schmidt b\<close>]
      apply (simp only: trace_def)
      by simp
  qed

  show \<open>trace A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>B. e \<bullet>\<^sub>C (A *\<^sub>V e)) else 0)\<close> if \<open>is_onb B\<close>
  proof (cases \<open>trace_class A\<close>)
    case True
    with that
    obtain b c :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where hs_b: \<open>hilbert_schmidt b\<close> and hs_c: \<open>hilbert_schmidt c\<close> and Acb: \<open>A = c o\<^sub>C\<^sub>L b\<close>
      by (metis trace_class_iff_hs_times_hs)
    have [simp]: \<open>trace_class  (c o\<^sub>C\<^sub>L b)\<close>
      using Acb True by auto

    show \<open>trace A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>B. e \<bullet>\<^sub>C (A *\<^sub>V e)) else 0)\<close>
      using ecbe_infsum[OF is_onb_some_chilbert_basis hs_c hs_b]
      using ecbe_infsum[OF \<open>is_onb B\<close> hs_c hs_b]
      by (simp only: Acb trace_def)
  next
    case False
    then show ?thesis
      by (simp add: trace_def)
  qed
qed

lemma trace_ket_sum:
  fixes A :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  assumes \<open>trace_class A\<close>
  shows \<open>trace A = (\<Sum>\<^sub>\<infinity>e. ket e \<bullet>\<^sub>C (A *\<^sub>V ket e))\<close>
  apply (subst infsum_reindex[where h=ket, unfolded o_def, symmetric])
  by (auto simp: \<open>trace_class A\<close>  trace_alt_def[OF is_onb_ket] is_onb_ket)

lemma trace_one_dim[simp]: \<open>trace A = one_dim_iso A\<close> for A :: \<open>'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
proof -
  have onb: \<open>is_onb {1 :: 'a}\<close>
    by auto
  have \<open>trace A = 1 \<bullet>\<^sub>C (A *\<^sub>V 1)\<close>
    apply (subst trace_alt_def)
     apply (fact onb)
    by simp
  also have \<open>\<dots> = one_dim_iso A\<close>
    by (simp add: cinner_cblinfun_def one_dim_iso_def)
  finally show ?thesis
    by -
qed


lemma trace_has_sum:
  assumes \<open>is_onb E\<close>
  assumes \<open>trace_class t\<close>
  shows \<open>((\<lambda>e. e \<bullet>\<^sub>C (t *\<^sub>V e)) has_sum trace t) E\<close>
  using assms(1) assms(2) trace_alt_def trace_exists by fastforce


lemma trace_sandwich_isometry[simp]: \<open>trace (sandwich U A) = trace A\<close> if \<open>isometry U\<close>
proof (cases \<open>trace_class A\<close>)
  case True
  note True[simp]
  have \<open>is_ortho_set ((*\<^sub>V) U ` some_chilbert_basis)\<close>
    unfolding is_ortho_set_def
    apply auto
    apply (metis (no_types, opaque_lifting) cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply cinner_adj_right is_ortho_set_def is_ortho_set_some_chilbert_basis isometry_def that)
    by (metis is_normal_some_chilbert_basis isometry_preserves_norm norm_zero that zero_neq_one)
  moreover have \<open>x \<in> (*\<^sub>V) U ` some_chilbert_basis \<Longrightarrow> norm x = 1\<close> for x
    using is_normal_some_chilbert_basis isometry_preserves_norm that by fastforce
  ultimately obtain B where BU: \<open>B \<supseteq> U ` some_chilbert_basis\<close> and \<open>is_onb B\<close>
    apply atomize_elim
    by (rule orthonormal_basis_exists)

  have xUy: \<open>x \<bullet>\<^sub>C U y = 0\<close> if xBU: \<open>x \<in> B - U ` some_chilbert_basis\<close> for x y
  proof -
    from that \<open>is_onb B\<close> \<open>isometry U\<close>
    have \<open>x \<bullet>\<^sub>C z = 0\<close> if \<open>z \<in> U ` some_chilbert_basis\<close> for z
      using that by (metis BU Diff_iff in_mono is_onb_def is_ortho_set_def)
    then have \<open>x \<in> orthogonal_complement (closure (cspan (U ` some_chilbert_basis)))\<close>
      by (metis orthogonal_complementI orthogonal_complement_of_closure orthogonal_complement_of_cspan)
    then have \<open>x \<in> space_as_set (- ccspan (U ` some_chilbert_basis))\<close>
      by (simp add: ccspan.rep_eq uminus_ccsubspace.rep_eq)
    then have \<open>x \<in> space_as_set (- (U *\<^sub>S top))\<close>
      by (metis cblinfun_image_ccspan ccspan_some_chilbert_basis)
    moreover have \<open>U y \<in> space_as_set (U *\<^sub>S top)\<close>
      by simp
    ultimately show ?thesis
      apply (transfer fixing: x y)
      using orthogonal_complement_orthoI by blast
  qed

  have [simp]: \<open>trace_class (sandwich U A)\<close>
    by (simp add: sandwich.rep_eq trace_class_comp_left trace_class_comp_right)
  have \<open>trace (sandwich U A) = (\<Sum>\<^sub>\<infinity>e\<in>B. e \<bullet>\<^sub>C ((sandwich U *\<^sub>V A) *\<^sub>V e))\<close>
    using \<open>is_onb B\<close> trace_alt_def by fastforce
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>e\<in>U ` some_chilbert_basis. e \<bullet>\<^sub>C ((sandwich U *\<^sub>V A) *\<^sub>V e))\<close>
    apply (rule infsum_cong_neutral)
    using BU xUy by (auto simp: sandwich_apply)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. U e \<bullet>\<^sub>C ((sandwich U *\<^sub>V A) *\<^sub>V U e))\<close>
    apply (subst infsum_reindex)
    apply (metis cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply inj_on_inverseI isometry_def that)
    by (auto simp: o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C A e)\<close>
    apply (rule infsum_cong)
    apply (simp add: sandwich_apply flip: cinner_adj_right)
    by (metis cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply isometry_def that)
  also have \<open>\<dots> = trace A\<close>
    by (simp add: trace_def)
  finally show ?thesis
    by -
next
  case False
  note False[simp]
  then have [simp]: \<open>\<not> trace_class (sandwich U A)\<close>
    by (smt (verit, ccfv_SIG) cblinfun_assoc_left(1) cblinfun_compose_id_left cblinfun_compose_id_right isometryD sandwich.rep_eq that trace_class_comp_left trace_class_comp_right)
  show ?thesis
    by (simp add: trace_def)
qed

lemma circularity_of_trace:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (e)\<close>
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close> and b :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    \<comment> \<open>The proof from \<^cite>\<open>conway00operator\<close> only work for square operators, we generalize it\<close>
  assumes \<open>trace_class a\<close>
    \<comment> \<open>Actually, \<^term>\<open>trace_class (a o\<^sub>C\<^sub>L b) \<and> trace_class (b o\<^sub>C\<^sub>L a)\<close> is sufficient here,
        see @{cite "mathoverflow-circ-trace2"} but the proof is more involved.
        Only \<^term>\<open>trace_class (a o\<^sub>C\<^sub>L b)\<close> is not sufficient, 
        see @{cite "mathoverflow-circ-trace1"}.\<close>
  shows \<open>trace (a o\<^sub>C\<^sub>L b) = trace (b o\<^sub>C\<^sub>L a)\<close>
proof -
  (* We first make a and b into square operators by padding them because for those the circularity of the trace is easier. *)
  define a' b' :: \<open>('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b)\<close> 
    where \<open>a' = cblinfun_right o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L cblinfun_left*\<close>
      and \<open>b' = cblinfun_left o\<^sub>C\<^sub>L b o\<^sub>C\<^sub>L cblinfun_right*\<close>

  have \<open>trace_class a'\<close>
    by (simp add: a'_def assms trace_class_comp_left trace_class_comp_right)

  (* Circularity of the trace for square operators *)
  have circ': \<open>trace (a' o\<^sub>C\<^sub>L b') = trace (b' o\<^sub>C\<^sub>L a')\<close>
  proof -
    from \<open>trace_class a'\<close>
    obtain B C :: \<open>('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b)\<close> where \<open>hilbert_schmidt B\<close> and \<open>hilbert_schmidt C\<close> and aCB: \<open>a' = C* o\<^sub>C\<^sub>L B\<close>
      by (metis abs_op_pos adj_cblinfun_compose double_adj hilbert_schmidt_comp_left hilbert_schmidt_comp_right polar_decomposition_correct polar_decomposition_correct' positive_hermitianI trace_class_iff_hs_times_hs)
    have hs_iB: \<open>hilbert_schmidt (\<i> *\<^sub>C B)\<close>
      by (metis Abs_hilbert_schmidt_inverse Rep_hilbert_schmidt \<open>hilbert_schmidt B\<close> mem_Collect_eq scaleC_hilbert_schmidt.rep_eq)
    have *: \<open>Re (trace (C* o\<^sub>C\<^sub>L B)) = Re (trace (C o\<^sub>C\<^sub>L B*))\<close> if \<open>hilbert_schmidt B\<close> \<open>hilbert_schmidt C\<close> for B C :: \<open>('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b)\<close>
    proof -
      from that
      obtain B' C' where \<open>B = Rep_hilbert_schmidt B'\<close> and \<open>C = Rep_hilbert_schmidt C'\<close>
        by (meson Rep_hilbert_schmidt_cases mem_Collect_eq)
      then have [transfer_rule]: \<open>cr_hilbert_schmidt B B'\<close> \<open>cr_hilbert_schmidt C C'\<close>
        by (simp_all add: cr_hilbert_schmidt_def)
  
      have \<open>Re (trace (C* o\<^sub>C\<^sub>L B)) = Re (C' \<bullet>\<^sub>C B')\<close>
        apply transfer by simp
      also have \<open>\<dots> = (1/4) * ((norm (C' + B'))\<^sup>2 - (norm (C' - B'))\<^sup>2)\<close>
        by (simp add: cdot_norm)
      also have \<open>\<dots> = (1/4) * ((norm (adj_hs C' + adj_hs B'))\<^sup>2 - (norm (adj_hs C' - adj_hs B'))\<^sup>2)\<close>
        by (simp add: flip: adj_hs_plus adj_hs_minus)
      also have \<open>\<dots> = Re (adj_hs C' \<bullet>\<^sub>C adj_hs B')\<close>
        by (simp add: cdot_norm)
      also have \<open>\<dots> = Re (trace (C o\<^sub>C\<^sub>L B*))\<close>
        apply transfer by simp
      finally show ?thesis
        by -
    qed
    have **: \<open>trace (C* o\<^sub>C\<^sub>L B) = cnj (trace (C o\<^sub>C\<^sub>L B*))\<close> if \<open>hilbert_schmidt B\<close> \<open>hilbert_schmidt C\<close> for B C :: \<open>('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b)\<close>
      using *[OF \<open>hilbert_schmidt B\<close> \<open>hilbert_schmidt C\<close>]
      using *[OF hilbert_schmidt_scaleC[of _ \<i>, OF \<open>hilbert_schmidt B\<close>] \<open>hilbert_schmidt C\<close>]
      apply (auto simp: trace_scaleC cblinfun_compose_uminus_right trace_uminus)
      by (smt (verit, best) cnj.code complex.collapse)
  
    have \<open>trace (b' o\<^sub>C\<^sub>L a') = trace ((b' o\<^sub>C\<^sub>L C*) o\<^sub>C\<^sub>L B)\<close>
      by (simp add: aCB cblinfun_assoc_left(1))
    also from ** \<open>hilbert_schmidt B\<close> \<open>hilbert_schmidt C\<close> have \<open>\<dots> = cnj (trace ((C o\<^sub>C\<^sub>L b'*) o\<^sub>C\<^sub>L B*))\<close>
      by (metis adj_cblinfun_compose double_adj hilbert_schmidt_comp_left)
    also have \<open>\<dots> = cnj (trace (C o\<^sub>C\<^sub>L (B o\<^sub>C\<^sub>L b')*))\<close>
      by (simp add: cblinfun_assoc_left(1))
    also  from ** \<open>hilbert_schmidt B\<close> \<open>hilbert_schmidt C\<close> have \<open>\<dots> = trace (C* o\<^sub>C\<^sub>L (B o\<^sub>C\<^sub>L b'))\<close>
      by (simp add: hilbert_schmidt_comp_left)
    also have \<open>\<dots> = trace (a' o\<^sub>C\<^sub>L b')\<close>
      by (simp add: aCB cblinfun_compose_assoc)
    finally show ?thesis
      by simp
  qed

  have \<open>trace (a o\<^sub>C\<^sub>L b) = trace (sandwich cblinfun_right (a o\<^sub>C\<^sub>L b) :: ('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b))\<close>
    by simp
  also have \<open>\<dots> = trace (sandwich cblinfun_right (a o\<^sub>C\<^sub>L (cblinfun_left* o\<^sub>C\<^sub>L (cblinfun_left :: _\<Rightarrow>\<^sub>C\<^sub>L('a\<times>'b))) o\<^sub>C\<^sub>L b) :: ('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b))\<close>
    by simp
  also have \<open>\<dots> = trace (a' o\<^sub>C\<^sub>L b')\<close>
    by (simp only: a'_def b'_def sandwich_apply cblinfun_compose_assoc)
  also have \<open>\<dots> = trace (b' o\<^sub>C\<^sub>L a')\<close>
    by (rule circ')
  also have \<open>\<dots> = trace (sandwich cblinfun_left (b o\<^sub>C\<^sub>L (cblinfun_right* o\<^sub>C\<^sub>L (cblinfun_right :: _\<Rightarrow>\<^sub>C\<^sub>L('a\<times>'b))) o\<^sub>C\<^sub>L a) :: ('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b))\<close>
    by (simp only: a'_def b'_def sandwich_apply cblinfun_compose_assoc)
  also have \<open>\<dots> = trace (sandwich cblinfun_left (b o\<^sub>C\<^sub>L a) :: ('a\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b))\<close>
    by simp
  also have \<open>\<dots> = trace (b o\<^sub>C\<^sub>L a)\<close>
    by simp
  finally show \<open>trace (a o\<^sub>C\<^sub>L b) = trace (b o\<^sub>C\<^sub>L a)\<close>
    by -
qed

lemma trace_butterfly_comp: \<open>trace (butterfly x y o\<^sub>C\<^sub>L a) = y \<bullet>\<^sub>C (a *\<^sub>V x)\<close>
proof -
  have \<open>trace (butterfly x y o\<^sub>C\<^sub>L a) = trace (vector_to_cblinfun y* o\<^sub>C\<^sub>L (a o\<^sub>C\<^sub>L (vector_to_cblinfun x :: complex \<Rightarrow>\<^sub>C\<^sub>L _)))\<close>
    unfolding butterfly_def
    by (metis cblinfun_compose_assoc circularity_of_trace trace_class_finite_dim)
  also have \<open>\<dots> = y \<bullet>\<^sub>C (a *\<^sub>V x)\<close>
    by (simp add: one_dim_iso_cblinfun_comp)
  finally show ?thesis
    by -
qed

lemma trace_butterfly: \<open>trace (butterfly x y) = y \<bullet>\<^sub>C x\<close>
  using trace_butterfly_comp[where a=id_cblinfun] by auto

lemma trace_butterfly_comp': \<open>trace (a o\<^sub>C\<^sub>L butterfly x y) = y \<bullet>\<^sub>C (a *\<^sub>V x)\<close>
  by (simp add: cblinfun_comp_butterfly trace_butterfly)


lemma trace_norm_adj[simp]: \<open>trace_norm (a*) = trace_norm a\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (f)\<close>
proof -
  have \<open>of_real (trace_norm (a*)) = trace (sandwich (polar_decomposition a) *\<^sub>V abs_op a)\<close>
    by (metis abs_op_adj trace_abs_op)
  also have \<open>\<dots> = trace ((polar_decomposition a)* o\<^sub>C\<^sub>L (polar_decomposition a) o\<^sub>C\<^sub>L abs_op a)\<close>
    by (metis (no_types, lifting) abs_op_adj cblinfun_compose_assoc circularity_of_trace double_adj
        polar_decomposition_correct polar_decomposition_correct' sandwich.rep_eq trace_class_abs_op trace_def)
  also have \<open>\<dots> = trace (abs_op a)\<close>
    by (simp add: cblinfun_compose_assoc polar_decomposition_correct polar_decomposition_correct')
  also have \<open>\<dots> = of_real (trace_norm a)\<close>
    by simp
  finally show ?thesis
    by simp
qed

lemma trace_class_adj[simp]: \<open>trace_class (a*)\<close> if \<open>trace_class a\<close>
proof (rule ccontr)
  assume asm: \<open>\<not> trace_class (a*)\<close>
  then have \<open>trace_norm (a*) = 0\<close>
    by (simp add: trace_norm_def)
  then have \<open>trace_norm a = 0\<close>
    by (metis trace_norm_adj)
  then have \<open>a = 0\<close>
    using that trace_norm_nondegenerate by blast
  then have \<open>trace_class (a*)\<close>
    by simp
  with asm show False
    by simp
qed

lift_definition adj_tc :: \<open>('a::chilbert_space, 'b::chilbert_space) trace_class \<Rightarrow> ('b,'a) trace_class\<close> is adj
  by simp

lift_definition selfadjoint_tc :: \<open>('a::chilbert_space, 'a) trace_class \<Rightarrow> bool\<close> is selfadjoint.

lemma selfadjoint_tc_def': \<open>selfadjoint_tc a \<longleftrightarrow> adj_tc a = a\<close>
  apply transfer
  using selfadjoint_def by blast 

lemma trace_class_finite_dim'[simp]: \<open>trace_class A\<close> for A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::{cfinite_dim,chilbert_space}\<close>
  by (metis double_adj trace_class_adj trace_class_finite_dim)

lemma trace_class_plus[simp]:
  fixes t u :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>trace_class t\<close> and \<open>trace_class u\<close>
  shows \<open>trace_class (t + u)\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (a).
      However, we use a completely different proof that does not need the fact that trace class operators can be diagonalized with countably many diagonal elements.\<close>
proof -
  define II :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'a)\<close> where \<open>II = cblinfun_left + cblinfun_right\<close>
  define JJ :: \<open>('b\<times>'b) \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> where \<open>JJ = cblinfun_left* + cblinfun_right*\<close>
  define tu :: \<open>('a\<times>'a) \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>'b)\<close> where \<open>tu = (cblinfun_left o\<^sub>C\<^sub>L t o\<^sub>C\<^sub>L cblinfun_left*) + (cblinfun_right o\<^sub>C\<^sub>L u o\<^sub>C\<^sub>L cblinfun_right*)\<close>
  have t_plus_u: \<open>t + u = JJ o\<^sub>C\<^sub>L tu o\<^sub>C\<^sub>L II\<close>
    apply (simp add: II_def JJ_def tu_def cblinfun_compose_add_left cblinfun_compose_add_right cblinfun_compose_assoc)
    by (simp flip: cblinfun_compose_assoc)
  have \<open>trace_class tu\<close>
  proof (rule trace_classI)
    define BL BR B :: \<open>('a\<times>'a) set\<close> where \<open>BL = some_chilbert_basis \<times> {0}\<close>
      and \<open>BR = {0} \<times> some_chilbert_basis\<close>
      and \<open>B = BL \<union> BR\<close>
    have \<open>BL \<inter> BR = {}\<close>
      using is_ortho_set_some_chilbert_basis
      by (auto simp: BL_def BR_def is_ortho_set_def)
    show \<open>is_onb B\<close>
      by (simp add: BL_def BR_def B_def is_onb_prod)
    have abs_tu: \<open>abs_op tu = (cblinfun_left o\<^sub>C\<^sub>L abs_op t o\<^sub>C\<^sub>L cblinfun_left*) + (cblinfun_right o\<^sub>C\<^sub>L abs_op u o\<^sub>C\<^sub>L cblinfun_right*)\<close>
      using [[show_consts]]
    proof -
      have \<open>((cblinfun_left o\<^sub>C\<^sub>L abs_op t o\<^sub>C\<^sub>L cblinfun_left*) + (cblinfun_right o\<^sub>C\<^sub>L abs_op u o\<^sub>C\<^sub>L cblinfun_right*))*
        o\<^sub>C\<^sub>L ((cblinfun_left o\<^sub>C\<^sub>L abs_op t o\<^sub>C\<^sub>L cblinfun_left*) + (cblinfun_right o\<^sub>C\<^sub>L abs_op u o\<^sub>C\<^sub>L cblinfun_right*))
        = tu* o\<^sub>C\<^sub>L tu\<close>
      proof -
        have tt[THEN simp_a_oCL_b, simp]: \<open>(abs_op t)* o\<^sub>C\<^sub>L abs_op t = t* o\<^sub>C\<^sub>L t\<close>
          by (simp add: abs_op_def positive_cblinfun_squareI positive_hermitianI)
        have uu[THEN simp_a_oCL_b, simp]: \<open>(abs_op u)* o\<^sub>C\<^sub>L abs_op u = u* o\<^sub>C\<^sub>L u\<close>
          by (simp add: abs_op_def positive_cblinfun_squareI positive_hermitianI)
        note isometryD[THEN simp_a_oCL_b, simp]
        note cblinfun_right_left_ortho[THEN simp_a_oCL_b, simp]
        note cblinfun_left_right_ortho[THEN simp_a_oCL_b, simp]
        show ?thesis
          using tt[of \<open>cblinfun_left* :: ('a\<times>'a) \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>] uu[of \<open>cblinfun_right* :: ('a\<times>'a) \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>]
          by (simp add: tu_def cblinfun_compose_add_right cblinfun_compose_add_left adj_plus
              cblinfun_compose_assoc)
      qed
      moreover have \<open>(cblinfun_left o\<^sub>C\<^sub>L abs_op t o\<^sub>C\<^sub>L cblinfun_left*) + (cblinfun_right o\<^sub>C\<^sub>L abs_op u o\<^sub>C\<^sub>L cblinfun_right*) \<ge> 0\<close>
        apply (rule positive_cblinfunI)
        by (auto simp: cblinfun.add_left cinner_pos_if_pos)
      ultimately show ?thesis
        by (rule abs_opI[symmetric])
    qed
    from assms(1)
    have \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op t *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
      by (metis is_onb_some_chilbert_basis summable_on_iff_abs_summable_on_complex trace_class_abs_op trace_exists)
    then have sum_BL: \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op tu *\<^sub>V x)) abs_summable_on BL\<close>
      apply (subst asm_rl[of \<open>BL = (\<lambda>x. (x,0)) ` some_chilbert_basis\<close>])
      by (auto simp: BL_def summable_on_reindex inj_on_def o_def abs_tu cblinfun.add_left)
    from assms(2)
    have \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op u *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
      by (metis is_onb_some_chilbert_basis summable_on_iff_abs_summable_on_complex trace_class_abs_op trace_exists)
    then have sum_BR: \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op tu *\<^sub>V x)) abs_summable_on BR\<close>
      apply (subst asm_rl[of \<open>BR = (\<lambda>x. (0,x)) ` some_chilbert_basis\<close>])
      by (auto simp: BR_def summable_on_reindex inj_on_def o_def abs_tu cblinfun.add_left)
    from sum_BL sum_BR
    show \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op tu *\<^sub>V x)) abs_summable_on B\<close>
      using \<open>BL \<inter> BR = {}\<close>
      by (auto intro!: summable_on_Un_disjoint simp: B_def)
  qed
  with t_plus_u
  show \<open>trace_class (t + u)\<close>
    by (simp add: trace_class_comp_left trace_class_comp_right)
qed

lemma trace_class_minus[simp]: \<open>trace_class t \<Longrightarrow> trace_class u \<Longrightarrow> trace_class (t - u)\<close>
  for t u :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  by (metis trace_class_plus trace_class_uminus uminus_add_conv_diff)

lemma trace_plus: 
  assumes \<open>trace_class a\<close> \<open>trace_class b\<close>
  shows \<open>trace (a + b) = trace a + trace b\<close>
  by (simp add: assms(1) assms(2) trace_plus_prelim)
hide_fact trace_plus_prelim

lemma trace_class_sum:
  fixes a :: \<open>'a \<Rightarrow> 'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close>
  assumes \<open>\<And>i. i\<in>I \<Longrightarrow> trace_class (a i)\<close>
  shows \<open>trace_class (\<Sum>i\<in>I. a i)\<close>
  using assms apply (induction I rule:infinite_finite_induct)
  by auto

lemma
  assumes \<open>\<And>i. i\<in>I \<Longrightarrow> trace_class (a i)\<close>
  shows trace_sum: \<open>trace (\<Sum>i\<in>I. a i) = (\<Sum>i\<in>I. trace (a i))\<close>
  using assms apply (induction I rule:infinite_finite_induct)
  by (auto simp: trace_plus trace_class_sum)

lemma cmod_trace_times: \<open>cmod (trace (a o\<^sub>C\<^sub>L b)) \<le> norm a * trace_norm b\<close> if \<open>trace_class b\<close> 
  for b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (e)\<close>
proof -
  define W where \<open>W = polar_decomposition b\<close>

  have \<open>norm W \<le> 1\<close>
    by (metis W_def norm_partial_isometry norm_zero order_refl polar_decomposition_partial_isometry zero_less_one_class.zero_le_one)
  have hs1: \<open>hilbert_schmidt (sqrt_op (abs_op b))\<close>
    using that trace_class_iff_sqrt_hs by blast
  then have hs2: \<open>hilbert_schmidt (sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*)\<close>
    by (simp add: hilbert_schmidt_comp_left)

  from \<open>trace_class b\<close>
  have \<open>trace_class (a o\<^sub>C\<^sub>L b)\<close>
    using trace_class_comp_right by blast
  then have sum1: \<open>(\<lambda>e. e \<bullet>\<^sub>C ((a o\<^sub>C\<^sub>L b) *\<^sub>V e)) abs_summable_on some_chilbert_basis\<close>
    by (metis is_onb_some_chilbert_basis summable_on_iff_abs_summable_on_complex trace_exists)

  have sum5: \<open>(\<lambda>x. (norm (sqrt_op (abs_op b) *\<^sub>V x))\<^sup>2) summable_on some_chilbert_basis\<close>
    using summable_hilbert_schmidt_norm_square[OF is_onb_some_chilbert_basis hs1]
    by (simp add: power2_eq_square)

  have sum4: \<open>(\<lambda>x. (norm ((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V x))\<^sup>2) summable_on some_chilbert_basis\<close>
    using summable_hilbert_schmidt_norm_square[OF is_onb_some_chilbert_basis hs2]
    by (simp add: power2_eq_square)

  have sum3: \<open>(\<lambda>e. norm ((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V e) * norm (sqrt_op (abs_op b) *\<^sub>V e)) summable_on some_chilbert_basis\<close>
    apply (rule abs_summable_summable)
    apply (rule abs_summable_product)
    by (intro sum4 sum5 summable_on_iff_abs_summable_on_real[THEN iffD1])+

  have sum2: \<open>(\<lambda>e. ((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V e) \<bullet>\<^sub>C (sqrt_op (abs_op b) *\<^sub>V e)) abs_summable_on some_chilbert_basis\<close>
    using sum3[THEN summable_on_iff_abs_summable_on_real[THEN iffD1]]
    apply (rule abs_summable_on_comparison_test)
    by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2)

  from \<open>trace_class b\<close>
  have \<open>cmod (trace (a o\<^sub>C\<^sub>L b)) = cmod (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C ((a o\<^sub>C\<^sub>L b) *\<^sub>V e))\<close>
    by (simp add: trace_class_comp_right trace_def)
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. cmod (e \<bullet>\<^sub>C ((a o\<^sub>C\<^sub>L b) *\<^sub>V e)))\<close>
    using sum1 by (rule norm_infsum_bound)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. cmod (((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V e) \<bullet>\<^sub>C (sqrt_op (abs_op b) *\<^sub>V e)))\<close>
    apply (simp add: positive_hermitianI flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
    by (metis (full_types) W_def abs_op_def cblinfun_compose_assoc polar_decomposition_correct sqrt_op_pos sqrt_op_square)
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. norm ((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V e) * norm (sqrt_op (abs_op b) *\<^sub>V e))\<close>
    using sum2 sum3 apply (rule infsum_mono)
    using complex_inner_class.Cauchy_Schwarz_ineq2 by blast
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. norm (norm ((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V e) * norm (sqrt_op (abs_op b) *\<^sub>V e)))\<close>
    by simp
  also have \<open>\<dots> \<le> sqrt (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. (norm (norm ((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V e)))\<^sup>2) 
                * sqrt (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. (norm (norm (sqrt_op (abs_op b) *\<^sub>V e)))\<^sup>2)\<close>
    apply (rule Cauchy_Schwarz_ineq_infsum)
    using sum4 sum5 by auto
  also have \<open>\<dots> = sqrt (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. (norm ((sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) *\<^sub>V e))\<^sup>2)
                * sqrt (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. (norm (sqrt_op (abs_op b) *\<^sub>V e))\<^sup>2)\<close>
    by simp
  also have \<open>\<dots> = hilbert_schmidt_norm (sqrt_op (abs_op b) o\<^sub>C\<^sub>L W* o\<^sub>C\<^sub>L a*) * hilbert_schmidt_norm (sqrt_op (abs_op b))\<close>
    apply (subst infsum_hilbert_schmidt_norm_square, simp, fact hs2)
    apply (subst infsum_hilbert_schmidt_norm_square, simp, fact hs1)
    by simp
  also have \<open>\<dots> \<le> hilbert_schmidt_norm (sqrt_op (abs_op b)) * norm (W* o\<^sub>C\<^sub>L a*) * hilbert_schmidt_norm (sqrt_op (abs_op b))\<close>
    by (metis cblinfun_assoc_left(1) hilbert_schmidt_norm_comp_left hilbert_schmidt_norm_pos mult.commute mult_right_mono that trace_class_iff_sqrt_hs)
  also have \<open>\<dots> \<le> hilbert_schmidt_norm (sqrt_op (abs_op b)) * norm (W*) * norm (a*) * hilbert_schmidt_norm (sqrt_op (abs_op b))\<close>
    by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) hilbert_schmidt_norm_pos mult_right_mono norm_cblinfun_compose ordered_comm_semiring_class.comm_mult_left_mono)
  also have \<open>\<dots> \<le> hilbert_schmidt_norm (sqrt_op (abs_op b)) * norm (a*) * hilbert_schmidt_norm (sqrt_op (abs_op b))\<close>
    by (metis \<open>norm W \<le> 1\<close> hilbert_schmidt_norm_pos mult.right_neutral mult_left_mono mult_right_mono norm_adj norm_ge_zero)
  also have \<open>\<dots> = norm a * (hilbert_schmidt_norm (sqrt_op (abs_op b)))\<^sup>2\<close>
    by (simp add: power2_eq_square)
  also have \<open>\<dots> = norm a * trace_norm b\<close>
    apply (simp add: hilbert_schmidt_norm_def positive_hermitianI)
    by (metis abs_op_idem of_real_eq_iff trace_abs_op)
  finally show ?thesis
    by -
qed

lemma trace_leq_trace_norm[simp]: \<open>cmod (trace a) \<le> trace_norm a\<close>
proof (cases \<open>trace_class a\<close>)
  case True
  then have \<open>cmod (trace a) \<le> norm (id_cblinfun :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a) * trace_norm a\<close>
    using cmod_trace_times[where a=\<open>id_cblinfun :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and b=a]
    by simp
  also have \<open>\<dots> \<le> trace_norm a\<close>
    apply (rule mult_left_le_one_le)
    by (auto intro!: mult_left_le_one_le simp: norm_cblinfun_id_le)
  finally show ?thesis
    by -
next
  case False
  then show ?thesis
    by (simp add: trace_def)
qed

lemma trace_norm_triangle: 
  fixes a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes [simp]: \<open>trace_class a\<close> \<open>trace_class b\<close>
  shows \<open>trace_norm (a + b) \<le> trace_norm a + trace_norm b\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (a)\<close>
proof -
  define w where \<open>w = polar_decomposition (a+b)\<close>
  have \<open>norm (w*) \<le> 1\<close>
    by (metis dual_order.refl norm_adj norm_partial_isometry norm_zero polar_decomposition_partial_isometry w_def zero_less_one_class.zero_le_one)
  have \<open>trace_norm (a + b) = cmod (trace (abs_op (a+b)))\<close>
    by simp
  also have \<open>\<dots> = cmod (trace (w* o\<^sub>C\<^sub>L (a+b)))\<close>
    by (simp add: polar_decomposition_correct' w_def)
  also have \<open>\<dots> \<le> cmod (trace (w* o\<^sub>C\<^sub>L a)) + cmod (trace (w* o\<^sub>C\<^sub>L b))\<close>
    by (simp add: cblinfun_compose_add_right norm_triangle_ineq trace_class_comp_right trace_plus)
  also have \<open>\<dots> \<le> (norm (w*) * trace_norm a) + (norm (w*) * trace_norm b)\<close>
    by (smt (verit, best) assms(1) assms(2) cmod_trace_times)
  also have \<open>\<dots> \<le> trace_norm a + trace_norm b\<close>
    using \<open>norm (w*) \<le> 1\<close>
    by (smt (verit, ccfv_SIG) mult_le_cancel_right2 trace_norm_nneg)
  finally show ?thesis
    by -
qed

instantiation trace_class :: (chilbert_space, chilbert_space) "{complex_vector}" begin
(* Lifted definitions *)
lift_definition zero_trace_class :: \<open>('a,'b) trace_class\<close> is 0 by auto
lift_definition minus_trace_class :: \<open>('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class\<close> is minus by auto
lift_definition uminus_trace_class :: \<open>('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class\<close> is uminus by simp
lift_definition plus_trace_class :: \<open>('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class\<close> is plus by auto
lift_definition scaleC_trace_class :: \<open>complex \<Rightarrow> ('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class\<close> is scaleC
  by (metis (no_types, opaque_lifting) cblinfun_compose_id_right cblinfun_compose_scaleC_right mem_Collect_eq trace_class_comp_left)
lift_definition scaleR_trace_class :: \<open>real \<Rightarrow> ('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class\<close> is scaleR
  by (metis (no_types, opaque_lifting) cblinfun_compose_id_right cblinfun_compose_scaleC_right mem_Collect_eq scaleR_scaleC trace_class_comp_left)
instance
proof standard
  fix a b c :: \<open>('a,'b) trace_class\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer by auto
  show \<open>a + b = b + a\<close>
    apply transfer by auto
  show \<open>0 + a = a\<close>
    apply transfer by auto
  show \<open>- a + a = 0\<close>
    apply transfer by auto
  show \<open>a - b = a + - b\<close>
    apply transfer by auto
  show \<open>(*\<^sub>R) r = ((*\<^sub>C) (complex_of_real r) :: _ \<Rightarrow> ('a,'b) trace_class)\<close> for r :: real
    by (metis (mono_tags, opaque_lifting) Trace_Class.scaleC_trace_class_def Trace_Class.scaleR_trace_class_def id_apply map_fun_def o_def scaleR_scaleC)
  show \<open>r *\<^sub>C (a + b) = r *\<^sub>C a + r *\<^sub>C b\<close> for r :: complex
    apply transfer
    by (metis (no_types, lifting) scaleC_add_right)
  show \<open>(r + r') *\<^sub>C a = r *\<^sub>C a + r' *\<^sub>C a\<close> for r r' :: complex
    apply transfer
    by (metis (no_types, lifting) scaleC_add_left)
  show \<open>r *\<^sub>C r' *\<^sub>C a = (r * r') *\<^sub>C a\<close> for r r' :: complex
    apply transfer by auto
  show \<open>1 *\<^sub>C a = a\<close>
    apply transfer by auto
qed
end

lemma from_trace_class_0[simp]: \<open>from_trace_class 0 = 0\<close>
  by (simp add: zero_trace_class.rep_eq)

instantiation trace_class :: (chilbert_space, chilbert_space) "{complex_normed_vector}" begin
(* Definitions related to the trace norm *)
lift_definition norm_trace_class :: \<open>('a,'b) trace_class \<Rightarrow> real\<close> is trace_norm .
definition sgn_trace_class :: \<open>('a,'b) trace_class \<Rightarrow> ('a,'b) trace_class\<close> where \<open>sgn_trace_class a = a /\<^sub>R norm a\<close>
definition dist_trace_class :: \<open>('a,'b) trace_class \<Rightarrow> _ \<Rightarrow> _\<close> where \<open>dist_trace_class a b = norm (a - b)\<close>
definition [code del]: "uniformity_trace_class = (INF e\<in>{0<..}. principal {(x::('a,'b) trace_class, y). dist x y < e})"
definition [code del]: "open_trace_class U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e\<in>{0<..}. principal {(x, y). dist x y < e}. x' = x \<longrightarrow> y \<in> U)" for U :: "('a,'b) trace_class set"
instance
proof standard
  fix a b :: \<open>('a,'b) trace_class\<close>
  show \<open>dist a b = norm (a - b)\<close>
    by (metis (no_types, lifting) Trace_Class.dist_trace_class_def)
  show \<open>uniformity = (INF e\<in>{0<..}. principal {(x :: ('a,'b) trace_class, y). dist x y < e})\<close>
    by (simp add: uniformity_trace_class_def)
  show \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)\<close> for U :: \<open>('a,'b) trace_class set\<close>
    by (smt (verit, del_insts) case_prod_beta' eventually_mono open_trace_class_def uniformity_trace_class_def)
  show \<open>(norm a = 0) = (a = 0)\<close>
    apply transfer
    by (auto simp add: trace_norm_nondegenerate)
  show \<open>norm (a + b) \<le> norm a + norm b\<close>
    apply transfer
    by (auto simp: trace_norm_triangle)
  show \<open>norm (r *\<^sub>C a) = cmod r * norm a\<close> for r
    apply transfer
    by (auto simp: trace_norm_scaleC)
  then show \<open>norm (r *\<^sub>R a) = \<bar>r\<bar> * norm a\<close> for r
    by (metis norm_of_real scaleR_scaleC)
  show \<open>sgn a = a /\<^sub>R norm a\<close>
    by (simp add: sgn_trace_class_def)
qed
end






lemma trace_norm_comp_right:
  fixes a :: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close> and b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assumes \<open>trace_class b\<close>
  shows \<open>trace_norm (a o\<^sub>C\<^sub>L b) \<le> norm a * trace_norm b\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (g)\<close>
proof -
  define w w1 s where \<open>w = polar_decomposition b\<close> and \<open>w1 = polar_decomposition (a o\<^sub>C\<^sub>L b)\<close>
    and \<open>s = w1* o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L w\<close>
  have abs_ab: \<open>abs_op (a o\<^sub>C\<^sub>L b) = s o\<^sub>C\<^sub>L abs_op b\<close>
    by (auto simp: w1_def w_def s_def cblinfun_compose_assoc polar_decomposition_correct polar_decomposition_correct')
  have norm_s_t: \<open>norm s \<le> norm a\<close>
  proof -
    have \<open>norm s \<le> norm (w1* o\<^sub>C\<^sub>L a) * norm w\<close>
      by (simp add: norm_cblinfun_compose s_def)
    also have \<open>\<dots> \<le> norm (w1*) * norm a * norm w\<close>
      by (metis mult.commute mult_left_mono norm_cblinfun_compose norm_ge_zero)
    also have \<open>\<dots> \<le> norm a\<close>
      by (metis (no_types, opaque_lifting) dual_order.refl mult.commute mult.right_neutral mult_zero_left norm_adj norm_ge_zero norm_partial_isometry norm_zero polar_decomposition_partial_isometry w1_def w_def)
    finally show ?thesis
      by -
  qed
  have \<open>trace_norm (a o\<^sub>C\<^sub>L b) = cmod (trace (abs_op (a o\<^sub>C\<^sub>L b)))\<close>
    by simp
  also have \<open>\<dots> = cmod (trace (s o\<^sub>C\<^sub>L abs_op b))\<close>
    using abs_ab by presburger
  also have \<open>\<dots> \<le> norm s * trace_norm (abs_op b)\<close>
    using assms by (simp add: cmod_trace_times)
  also from norm_s_t have \<open>\<dots> \<le> norm a * trace_norm b\<close>
    by (metis abs_op_idem mult_right_mono of_real_eq_iff trace_abs_op trace_norm_nneg)
  finally show ?thesis
    by -
qed

lemma trace_norm_comp_left:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (g)\<close>
  fixes a :: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close> and b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assumes [simp]: \<open>trace_class a\<close>
  shows \<open>trace_norm (a o\<^sub>C\<^sub>L b) \<le> trace_norm a * norm b\<close>
proof -
  have \<open>trace_norm (b* o\<^sub>C\<^sub>L a*) \<le> norm (b*) * trace_norm (a*)\<close>
    apply (rule trace_norm_comp_right)
    by simp
  then have \<open>trace_norm ((b* o\<^sub>C\<^sub>L a*)*) \<le> norm b * trace_norm a\<close>
    by (simp del: adj_cblinfun_compose)
  then show ?thesis
    by (simp add: mult.commute)
qed

lemma bounded_clinear_trace_duality: \<open>trace_class t \<Longrightarrow> bounded_clinear (\<lambda>a. trace (t o\<^sub>C\<^sub>L a))\<close>
  apply (rule bounded_clinearI[where K=\<open>trace_norm t\<close>])
  apply (auto simp add: cblinfun_compose_add_right trace_class_comp_left trace_plus trace_scaleC)[2]
  by (metis circularity_of_trace order_trans trace_leq_trace_norm trace_norm_comp_right)

lemma trace_class_butterfly[simp]: \<open>trace_class (butterfly x y)\<close> for x :: \<open>'a::chilbert_space\<close> and y :: \<open>'b::chilbert_space\<close>
  unfolding butterfly_def
  apply (rule trace_class_comp_left)
  by simp

lemma trace_adj: \<open>trace (a*) = cnj (trace a)\<close>
  by (metis Complex_Inner_Product0.complex_inner_1_right cinner_zero_right double_adj is_onb_some_chilbert_basis is_orthogonal_sym trace_adj_prelim trace_alt_def trace_class_adj)
hide_fact trace_adj_prelim

lemma cmod_trace_times': \<open>cmod (trace (a o\<^sub>C\<^sub>L b)) \<le> norm b * trace_norm a\<close> if \<open>trace_class a\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 18.11 (e)\<close>
  apply (subst asm_rl[of \<open>a o\<^sub>C\<^sub>L b = (b* o\<^sub>C\<^sub>L a*)*\<close>], simp)
  apply (subst trace_adj)
  using cmod_trace_times[of \<open>a*\<close> \<open>b*\<close>]
  by (auto intro!: that trace_class_adj hilbert_schmidt_comp_right hilbert_schmidt_adj simp del: adj_cblinfun_compose)


lift_definition iso_trace_class_compact_op_dual' :: \<open>('a::chilbert_space,'b::chilbert_space) trace_class \<Rightarrow> ('b,'a) compact_op \<Rightarrow>\<^sub>C\<^sub>L complex\<close> is
  \<open>\<lambda>t c. trace (from_compact_op c o\<^sub>C\<^sub>L t)\<close>
proof (rename_tac t)
  include lifting_syntax
  fix t :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assume \<open>t \<in> Collect trace_class\<close>
  then have [simp]: \<open>trace_class t\<close>
    by simp
  have \<open>cmod (trace (from_compact_op x o\<^sub>C\<^sub>L t)) \<le> norm x * trace_norm t\<close> for x
    by (metis \<open>trace_class t\<close> cmod_trace_times from_compact_op_norm)
  then show \<open>bounded_clinear (\<lambda>c. trace (from_compact_op c o\<^sub>C\<^sub>L t))\<close>
    apply (rule_tac bounded_clinearI[where K=\<open>trace_norm t\<close>])
    by (auto simp: from_compact_op_plus from_compact_op_scaleC cblinfun_compose_add_right
        cblinfun_compose_add_left trace_plus trace_class_comp_right trace_scaleC)
qed

lemma iso_trace_class_compact_op_dual'_apply: \<open>iso_trace_class_compact_op_dual' t c = trace (from_compact_op c o\<^sub>C\<^sub>L from_trace_class t)\<close>
  by (simp add: iso_trace_class_compact_op_dual'.rep_eq)

lemma iso_trace_class_compact_op_dual'_plus: \<open>iso_trace_class_compact_op_dual' (a + b) = iso_trace_class_compact_op_dual' a + iso_trace_class_compact_op_dual' b\<close>
  apply transfer
  by (simp add: cblinfun_compose_add_right trace_class_comp_right trace_plus)

lemma iso_trace_class_compact_op_dual'_scaleC: \<open>iso_trace_class_compact_op_dual' (c *\<^sub>C a) = c *\<^sub>C iso_trace_class_compact_op_dual' a\<close>
  apply transfer
  by (simp add: trace_scaleC)

lemma iso_trace_class_compact_op_dual'_bounded_clinear[bounded_clinear, simp]:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 19.1\<close>
    \<open>bounded_clinear (iso_trace_class_compact_op_dual' :: ('a::chilbert_space,'b::chilbert_space) trace_class \<Rightarrow> _)\<close>
proof -
  let ?iso = \<open>iso_trace_class_compact_op_dual' :: ('a,'b) trace_class \<Rightarrow> _\<close>
  have \<open>norm (?iso t) \<le> norm t\<close> for t
  proof (rule norm_cblinfun_bound)
    show \<open>norm t \<ge> 0\<close> by simp
    fix c
    show \<open>cmod (iso_trace_class_compact_op_dual' t *\<^sub>V c) \<le> norm t * norm c\<close>
      apply (transfer fixing: c)
      apply simp
      by (metis cmod_trace_times from_compact_op_norm ordered_field_class.sign_simps(5))
  qed
  then show \<open>bounded_clinear ?iso\<close>
    apply (rule_tac bounded_clinearI[where K=1])
    by (auto simp: iso_trace_class_compact_op_dual'_plus iso_trace_class_compact_op_dual'_scaleC)
qed


lemma iso_trace_class_compact_op_dual'_surjective[simp]: 
  \<open>surj (iso_trace_class_compact_op_dual' :: ('a::chilbert_space,'b::chilbert_space) trace_class \<Rightarrow> _)\<close>
proof -
  let ?iso = \<open>iso_trace_class_compact_op_dual' :: ('a,'b) trace_class \<Rightarrow> _\<close>
  have \<open>\<exists>A. \<Phi> = ?iso A\<close> for \<Phi> :: \<open>('b, 'a) compact_op \<Rightarrow>\<^sub>C\<^sub>L complex\<close>
  proof -
    define p where \<open>p x y = \<Phi> (butterfly_co y x)\<close> for x y
    have norm_p: \<open>norm (p x y) \<le> norm \<Phi> * norm x * norm y\<close> for x y
    proof -
      have \<open>norm (p x y) \<le> norm \<Phi> * norm (butterfly_co y x)\<close>
        by (auto simp: p_def norm_cblinfun)
      also have \<open>\<dots> = norm \<Phi> * norm (butterfly y x)\<close>
        apply transfer by simp
      also have \<open>\<dots> = norm \<Phi> * norm x * norm y\<close>
        by (simp add: norm_butterfly)
      finally show ?thesis
        by -
    qed
    have [simp]: \<open>bounded_sesquilinear p\<close>
      apply (rule bounded_sesquilinear.intro)
      using norm_p
      by (auto
          intro!: exI[of _ \<open>norm \<Phi>\<close>]
          simp add: p_def butterfly_co_add_left butterfly_co_add_right  complex_vector.linear_add 
          cblinfun.scaleC_right cblinfun.scaleC_left ab_semigroup_mult_class.mult_ac)
    define A where \<open>A = (the_riesz_rep_sesqui p)*\<close>
    then have xAy: \<open>x \<bullet>\<^sub>C (A y) = p x y\<close> for x y
      by (simp add: cinner_adj_right the_riesz_rep_sesqui_apply)
    have \<Phi>C: \<open>\<Phi> C = trace (from_compact_op C o\<^sub>C\<^sub>L A)\<close> if \<open>finite_rank (from_compact_op C)\<close> for C
    proof -
      from that
      obtain x y and n :: nat where C_sum: \<open>from_compact_op C = (\<Sum>i<n. butterfly (y i) (x i))\<close>
        apply atomize_elim by (rule finite_rank_sum_butterfly)
      then have \<open>C = (\<Sum>i<n. butterfly_co (y i) (x i))\<close>
        apply transfer by simp
      then have \<open>\<Phi> C = (\<Sum>i<n. \<Phi> *\<^sub>V butterfly_co (y i) (x i))\<close>
        using cblinfun.sum_right by blast
      also have \<open>\<dots> = (\<Sum>i<n. p (x i) (y i))\<close>
        using p_def by presburger
      also have \<open>\<dots> = (\<Sum>i<n. (x i) \<bullet>\<^sub>C (A (y i)))\<close>
        using xAy by presburger
      also have \<open>\<dots> = (\<Sum>i<n. trace (butterfly (y i) (x i) o\<^sub>C\<^sub>L A))\<close>
        by (simp add: trace_butterfly_comp)
      also have \<open>\<dots> = trace ((\<Sum>i<n. butterfly (y i) (x i)) o\<^sub>C\<^sub>L A)\<close>
        by (metis (mono_tags, lifting) cblinfun_compose_sum_left sum.cong trace_class_butterfly trace_class_comp_left trace_sum)
      also have \<open>\<dots> = trace (from_compact_op C o\<^sub>C\<^sub>L A)\<close>
        using C_sum by presburger
      finally show ?thesis
        by -
    qed
    have \<open>trace_class A\<close>
    proof (rule trace_classI)
      show \<open>is_onb some_chilbert_basis\<close>
        by simp
      define W where \<open>W = polar_decomposition A\<close>
      have \<open>norm (W*) \<le> 1\<close>
        by (metis W_def nle_le norm_adj norm_partial_isometry norm_zero not_one_le_zero polar_decomposition_partial_isometry)
      have \<open>(\<Sum>x\<in>E. cmod (x \<bullet>\<^sub>C (abs_op A *\<^sub>V x))) \<le> norm \<Phi>\<close> if \<open>finite E\<close> and \<open>E \<subseteq> some_chilbert_basis\<close> for E
      proof -
        define CE where \<open>CE = (\<Sum>x\<in>E. (butterfly x x))\<close>
        from \<open>E \<subseteq> some_chilbert_basis\<close>
        have \<open>norm CE \<le> 1\<close>
          by (auto intro!: sum_butterfly_is_Proj norm_is_Proj is_normal_some_chilbert_basis simp: CE_def is_ortho_set_antimono)
        have \<open>(\<Sum>x\<in>E. cmod (x \<bullet>\<^sub>C (abs_op A *\<^sub>V x))) = cmod (\<Sum>x\<in>E. x \<bullet>\<^sub>C (abs_op A *\<^sub>V x))\<close>
          apply (rule sum_cmod_pos)
          by (simp add: cinner_pos_if_pos)
        also have \<open>\<dots> = cmod (\<Sum>x\<in>E. (W *\<^sub>V x) \<bullet>\<^sub>C (A *\<^sub>V x))\<close>
          apply (rule arg_cong, rule sum.cong, simp)
          by (metis W_def cblinfun_apply_cblinfun_compose cinner_adj_right polar_decomposition_correct')
        also have \<open>\<dots> = cmod (\<Sum>x\<in>E. \<Phi> (butterfly_co x (W x)))\<close>
          apply (rule arg_cong, rule sum.cong, simp)
          by (simp flip: p_def xAy)
        also have \<open>\<dots> = cmod (\<Phi> (\<Sum>x\<in>E. butterfly_co x (W x)))\<close>
          by (simp add: cblinfun.sum_right)
        also have \<open>\<dots> \<le> norm \<Phi> * norm (\<Sum>x\<in>E. butterfly_co x (W x))\<close>
          using norm_cblinfun by blast
        also have \<open>\<dots> = norm \<Phi> * norm (\<Sum>x\<in>E. butterfly x (W x))\<close>
          apply transfer by simp
        also have \<open>\<dots> = norm \<Phi> * norm (\<Sum>x\<in>E. (butterfly x x o\<^sub>C\<^sub>L W*))\<close>
          apply (rule arg_cong, rule sum.cong, simp)
          by (simp add: butterfly_comp_cblinfun)
        also have \<open>\<dots> = norm \<Phi> * norm (CE o\<^sub>C\<^sub>L W*)\<close>
          by (simp add: CE_def cblinfun_compose_sum_left)
        also have \<open>\<dots> \<le> norm \<Phi>\<close>
          apply (rule mult_left_le, simp_all)
          using \<open>norm CE \<le> 1\<close> \<open>norm (W*) \<le> 1\<close>
          by (metis mult_le_one norm_cblinfun_compose norm_ge_zero order_trans)
        finally show ?thesis
          by -
      qed
      then show \<open>(\<lambda>x. x \<bullet>\<^sub>C (abs_op A *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
        apply (rule_tac nonneg_bdd_above_summable_on)
        by (auto intro!: bdd_aboveI2)
    qed
    then obtain A' where A': \<open>A = from_trace_class A'\<close>
      using from_trace_class_cases by blast
    from \<Phi>C have \<Phi>C': \<open>\<Phi> C = ?iso A' C\<close> if \<open>finite_rank (from_compact_op C)\<close> for C
      by (simp add: that iso_trace_class_compact_op_dual'_apply A')
    have \<open>\<Phi> = ?iso A'\<close>
      apply (unfold cblinfun_apply_inject[symmetric])
      apply (rule finite_rank_separating_on_compact_op)
      using \<Phi>C' by (auto intro!: cblinfun.bounded_clinear_right)
    then show ?thesis
      by auto
  qed
  then show ?thesis
    by auto
qed

lemma iso_trace_class_compact_op_dual'_isometric[simp]:
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Theorem 19.1\<close>
  \<open>norm (iso_trace_class_compact_op_dual' t) = norm t\<close> for t :: \<open>('a::chilbert_space, 'b::chilbert_space) trace_class\<close>
proof -
  let ?iso = \<open>iso_trace_class_compact_op_dual' :: ('a,'b) trace_class \<Rightarrow> _\<close>
  have \<open>norm (?iso t) \<le> norm t\<close> for t
  proof (rule norm_cblinfun_bound)
    show \<open>norm t \<ge> 0\<close> by simp
    fix c
    show \<open>cmod (iso_trace_class_compact_op_dual' t *\<^sub>V c) \<le> norm t * norm c\<close>
      apply (transfer fixing: c)
      apply simp
      by (metis cmod_trace_times from_compact_op_norm ordered_field_class.sign_simps(5))
  qed
  moreover have \<open>norm (?iso t) \<ge> norm t\<close> for t
  proof -
    define s where \<open>s E = (\<Sum>e\<in>E. cmod (e \<bullet>\<^sub>C (abs_op (from_trace_class t) *\<^sub>V e)))\<close> for E
    have bound: \<open>norm (?iso t) \<ge> s E\<close> if \<open>finite E\<close> and \<open>E \<subseteq> some_chilbert_basis\<close> for E
    proof - 
      text \<open>Partial duplication from the proof of @{thm [source] iso_trace_class_compact_op_dual'_surjective}.
In Conway's text, this subproof occurs only once. However, it did not become clear to use how this works:
It seems that Conway's proof only implies that \<^const>\<open>iso_trace_class_compact_op_dual'\<close> is isometric on
the subset of trace-class operators \<^term>\<open>A\<close> constructed in that proof, but not necessarily on others (if \<^const>\<open>iso_trace_class_compact_op_dual'\<close> were non-injective, there might be others)\<close>
      define A \<Phi> where \<open>A = from_trace_class t\<close> and \<open>\<Phi> = ?iso t\<close>
      define W where \<open>W = polar_decomposition A\<close>
      have \<open>norm (W*) \<le> 1\<close>
        by (metis W_def nle_le norm_adj norm_partial_isometry norm_zero not_one_le_zero polar_decomposition_partial_isometry)
      define CE where \<open>CE = (\<Sum>x\<in>E. (butterfly x x))\<close>
      from \<open>E \<subseteq> some_chilbert_basis\<close>
      have \<open>norm CE \<le> 1\<close>
        by (auto intro!: sum_butterfly_is_Proj norm_is_Proj is_normal_some_chilbert_basis simp: CE_def is_ortho_set_antimono)
      have \<open>s E = (\<Sum>x\<in>E. cmod (x \<bullet>\<^sub>C (abs_op A *\<^sub>V x)))\<close>
        using A_def s_def by blast
      also have \<open>\<dots> = cmod (\<Sum>x\<in>E. x \<bullet>\<^sub>C (abs_op A *\<^sub>V x))\<close>
        apply (rule sum_cmod_pos)
        by (simp add: cinner_pos_if_pos)
      also have \<open>\<dots> = cmod (\<Sum>x\<in>E. (W *\<^sub>V x) \<bullet>\<^sub>C (A *\<^sub>V x))\<close>
        apply (rule arg_cong, rule sum.cong, simp)
        by (metis W_def cblinfun_apply_cblinfun_compose cinner_adj_right polar_decomposition_correct')
      also have \<open>\<dots> = cmod (\<Sum>x\<in>E. \<Phi> (butterfly_co x (W x)))\<close>
        apply (rule arg_cong, rule sum.cong, simp)
        by (auto simp: \<Phi>_def iso_trace_class_compact_op_dual'_apply butterfly_co.rep_eq trace_butterfly_comp
            simp flip: A_def)
      also have \<open>\<dots> = cmod (\<Phi> (\<Sum>x\<in>E. butterfly_co x (W x)))\<close>
        by (simp add: cblinfun.sum_right)
      also have \<open>\<dots> \<le> norm \<Phi> * norm (\<Sum>x\<in>E. butterfly_co x (W x))\<close>
        using norm_cblinfun by blast
      also have \<open>\<dots> = norm \<Phi> * norm (\<Sum>x\<in>E. butterfly x (W x))\<close>
        apply transfer by simp
      also have \<open>\<dots> = norm \<Phi> * norm (\<Sum>x\<in>E. (butterfly x x o\<^sub>C\<^sub>L W*))\<close>
        apply (rule arg_cong, rule sum.cong, simp)
        by (simp add: butterfly_comp_cblinfun)
      also have \<open>\<dots> = norm \<Phi> * norm (CE o\<^sub>C\<^sub>L W*)\<close>
        by (simp add: CE_def cblinfun_compose_sum_left)
      also have \<open>\<dots> \<le> norm \<Phi>\<close>
        apply (rule mult_left_le, simp_all)
        using \<open>norm CE \<le> 1\<close> \<open>norm (W*) \<le> 1\<close>
        by (metis mult_le_one norm_cblinfun_compose norm_ge_zero order_trans)
      finally show ?thesis
        by (simp add: \<Phi>_def)
    qed
    have \<open>trace_class (from_trace_class t)\<close> and \<open>norm t = trace_norm (from_trace_class t)\<close>
      using from_trace_class
      by (auto simp add: norm_trace_class.rep_eq)
    then have \<open>((\<lambda>e. cmod (e \<bullet>\<^sub>C (abs_op (from_trace_class t) *\<^sub>V e))) has_sum norm t) some_chilbert_basis\<close>      
      by (metis (no_types, lifting) has_sum_cong has_sum_infsum is_onb_some_chilbert_basis trace_class_def trace_norm_alt_def trace_norm_basis_invariance)
    then have lim: \<open>(s \<longlongrightarrow> norm t) (finite_subsets_at_top some_chilbert_basis)\<close>
      by (simp add: filterlim_iff has_sum_def s_def)
    show ?thesis
      using _ _ lim apply (rule tendsto_le)
      by (auto intro!: tendsto_const eventually_finite_subsets_at_top_weakI bound)
  qed
  ultimately show ?thesis
    using nle_le by blast
qed


instance trace_class :: (chilbert_space, chilbert_space) cbanach
proof
  let ?UNIVc = \<open>UNIV :: (('b,'a) compact_op \<Rightarrow>\<^sub>C\<^sub>L complex) set\<close>
  let ?UNIVt = \<open>UNIV :: ('a,'b) trace_class set\<close>
  let ?iso = \<open>iso_trace_class_compact_op_dual' :: ('a,'b) trace_class \<Rightarrow> _\<close>
  have lin_inv[simp]: \<open>bounded_clinear (inv ?iso)\<close>
    apply (rule bounded_clinear_inv[where b=1])
    by auto
  have [simp]: \<open>inj ?iso\<close>
  proof (rule injI)
    fix x y assume \<open>?iso x = ?iso y\<close>
    then have \<open>norm (?iso (x - y)) = 0\<close>
      by (metis (no_types, opaque_lifting) add_diff_cancel_left diff_self iso_trace_class_compact_op_dual'_isometric iso_trace_class_compact_op_dual'_plus norm_eq_zero ordered_field_class.sign_simps(12))
    then have \<open>norm (x - y) = 0\<close>
      by simp
    then show \<open>x = y\<close>
      by simp
  qed
  have norm_inv[simp]: \<open>norm (inv ?iso x) = norm x\<close> for x
    by (metis iso_trace_class_compact_op_dual'_isometric iso_trace_class_compact_op_dual'_surjective surj_f_inv_f)
  have \<open>complete ?UNIVc\<close>
    by (simp add: complete_UNIV)
  then have \<open>complete (inv ?iso ` ?UNIVc)\<close>
    apply (rule complete_isometric_image[rotated 4, where e=1])
    by (auto simp: bounded_clinear.bounded_linear)
  then have \<open>complete ?UNIVt\<close>
    by (simp add: inj_imp_surj_inv)
  then show \<open>Cauchy X \<Longrightarrow> convergent X\<close> for X :: \<open>nat \<Rightarrow> ('a, 'b) trace_class\<close>
    by (simp add: complete_def convergent_def)
qed



lemma trace_norm_geq_cinner_abs_op: \<open>\<psi> \<bullet>\<^sub>C (abs_op t *\<^sub>V \<psi>) \<le> trace_norm t\<close> if \<open>trace_class t\<close> and \<open>norm \<psi> = 1\<close>
proof -
  have \<open>\<exists>B. {\<psi>} \<subseteq> B \<and> is_onb B\<close>
    apply (rule orthonormal_basis_exists)
    using \<open>norm \<psi> = 1\<close>
    by auto
  then obtain B where \<open>is_onb B\<close> and \<open>\<psi> \<in> B\<close>
    by auto

  have \<open>\<psi> \<bullet>\<^sub>C (abs_op t *\<^sub>V \<psi>) = (\<Sum>\<^sub>\<infinity>\<psi>\<in>{\<psi>}. \<psi> \<bullet>\<^sub>C (abs_op t *\<^sub>V \<psi>))\<close>
    by simp
  also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>\<psi>\<in>B. \<psi> \<bullet>\<^sub>C (abs_op t *\<^sub>V \<psi>))\<close>
    apply (rule infsum_mono_neutral_complex)
    using \<open>\<psi> \<in> B\<close> \<open>is_onb B\<close> that
    by (auto simp add: trace_exists cinner_pos_if_pos)
  also have \<open>\<dots> = trace_norm t\<close>
    using \<open>is_onb B\<close> that
    by (metis trace_abs_op trace_alt_def trace_class_abs_op)
  finally show ?thesis
    by -
qed

lemma norm_leq_trace_norm: \<open>norm t \<le> trace_norm t\<close> if \<open>trace_class t\<close> 
  for t :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close> 
proof -
  wlog not_singleton: \<open>class.not_singleton TYPE('a)\<close>
    using not_not_singleton_cblinfun_zero[of t] negation by simp
  note cblinfun_norm_approx_witness' = cblinfun_norm_approx_witness[internalize_sort' 'a, OF complex_normed_vector_axioms not_singleton]

  show ?thesis
  proof (rule field_le_epsilon)
    fix \<epsilon> :: real assume \<open>\<epsilon> > 0\<close>

    define \<delta> :: real where 
      \<open>\<delta> = min (sqrt (\<epsilon> / 2)) (\<epsilon> / (4 * (norm (sqrt_op (abs_op t)) + 1)))\<close>
    have \<open>\<delta> > 0\<close>
      using \<open>\<epsilon> > 0\<close> apply (auto simp add: \<delta>_def)
      by (smt (verit) norm_not_less_zero zero_less_divide_iff)
    have \<delta>_small: \<open>\<delta>\<^sup>2 + 2 * norm (sqrt_op (abs_op t)) * \<delta> \<le> \<epsilon>\<close>
    proof -
      define n where \<open>n = norm (sqrt_op (abs_op t))\<close>
      then have \<open>n \<ge> 0\<close>
        by simp
      have \<delta>: \<open>\<delta> = min (sqrt (\<epsilon> / 2)) (\<epsilon> / (4 * (n + 1)))\<close>
        by (simp add: \<delta>_def n_def)

      have \<open>\<delta>\<^sup>2 + 2 * n * \<delta> \<le> \<epsilon> / 2 + 2 * n * \<delta>\<close>
        apply (rule add_right_mono)
        apply (subst \<delta>) apply (subst min_power_distrib_left)
        using \<open>\<epsilon> > 0\<close> \<open>n \<ge> 0\<close> by auto
      also have \<open>\<dots> \<le> \<epsilon> / 2 + 2 * n * (\<epsilon> / (4 * (n + 1)))\<close>
        apply (intro add_left_mono mult_left_mono)
        by (simp_all add: \<delta> \<open>n \<ge> 0\<close>)
      also have \<open>\<dots> = \<epsilon> / 2 + 2 * (n / (n+1)) * (\<epsilon> / 4)\<close>
        by simp
      also have \<open>\<dots> \<le> \<epsilon> / 2 + 2 * 1 * (\<epsilon> / 4)\<close>
        apply (intro add_left_mono mult_left_mono mult_right_mono)
        using \<open>n \<ge> 0\<close> \<open>\<epsilon> > 0\<close> by auto
      also have \<open>\<dots> = \<epsilon>\<close>
        by simp
      finally show \<open>\<delta>\<^sup>2 + 2 * n * \<delta> \<le> \<epsilon>\<close>
        by -
    qed

    from \<open>\<delta> > 0\<close> obtain \<psi> where \<psi>\<epsilon>: \<open>norm (sqrt_op (abs_op t)) - \<delta> \<le> norm (sqrt_op (abs_op t) *\<^sub>V \<psi>)\<close> and \<open>norm \<psi> = 1\<close>
      apply atomize_elim by (rule cblinfun_norm_approx_witness')

    have aux1: \<open>2 * complex_of_real x = complex_of_real (2 * x)\<close> for x
      by simp

    have \<open>complex_of_real (norm t) = norm (abs_op t)\<close>
      by simp
    also have \<open>\<dots> = (norm (sqrt_op (abs_op t)))\<^sup>2\<close>
      by (simp add: positive_hermitianI flip: norm_AadjA)
    also have \<open>\<dots> \<le> (norm (sqrt_op (abs_op t) *\<^sub>V \<psi>) + \<delta>)\<^sup>2\<close>
      by (smt (verit) \<psi>\<epsilon> complex_of_real_mono norm_triangle_ineq4 norm_triangle_sub pos2 power_strict_mono)
    also have \<open>\<dots> = (norm (sqrt_op (abs_op t) *\<^sub>V \<psi>))\<^sup>2 + \<delta>\<^sup>2 + 2 * norm (sqrt_op (abs_op t) *\<^sub>V \<psi>) * \<delta>\<close>
      by (simp add: power2_sum)
    also have \<open>\<dots> \<le> (norm (sqrt_op (abs_op t) *\<^sub>V \<psi>))\<^sup>2 + \<delta>\<^sup>2 + 2 * norm (sqrt_op (abs_op t)) * \<delta>\<close>
      apply (rule complex_of_real_mono_iff[THEN iffD2])
      by (smt (z3) \<open>0 < \<delta>\<close> \<open>norm \<psi> = 1\<close> more_arith_simps(11) mult_less_cancel_right_disj norm_cblinfun one_power2 power2_eq_square)
    also have \<open>\<dots> \<le> (norm (sqrt_op (abs_op t) *\<^sub>V \<psi>))\<^sup>2 + \<epsilon>\<close>
      apply (rule complex_of_real_mono_iff[THEN iffD2])
      using \<delta>_small by auto
    also have \<open>\<dots> = ((sqrt_op (abs_op t) *\<^sub>V \<psi>) \<bullet>\<^sub>C (sqrt_op (abs_op t) *\<^sub>V \<psi>)) + \<epsilon>\<close>
      by (simp add: cdot_square_norm)
    also have \<open>\<dots> = (\<psi> \<bullet>\<^sub>C (abs_op t *\<^sub>V \<psi>)) + \<epsilon>\<close>
      by (simp add: positive_hermitianI flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
    also have \<open>\<dots> \<le> trace_norm t + \<epsilon>\<close>
      using \<open>norm \<psi> = 1\<close> \<open>trace_class t\<close> by (auto simp add: trace_norm_geq_cinner_abs_op)
    finally show \<open>norm t \<le> trace_norm t + \<epsilon>\<close>
      using complex_of_real_mono_iff by blast
  qed
qed

lemma clinear_from_trace_class[iff]: \<open>clinear from_trace_class\<close>
  apply (rule clinearI; transfer)
  by auto

lemma bounded_clinear_from_trace_class[bounded_clinear]:
  \<open>bounded_clinear (from_trace_class :: ('a::chilbert_space,'b::chilbert_space) trace_class \<Rightarrow> _)\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  show ?thesis
    apply (rule bounded_clinearI[where K=1]; transfer)
    by (auto intro!: norm_leq_trace_norm[internalize_sort' 'a] chilbert_space_axioms True)
next
  case False
  then have zero: \<open>A = 0\<close> for A :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    by (rule not_not_singleton_cblinfun_zero)
  show ?thesis
    apply (rule bounded_clinearI[where K=1])
    by (subst zero, simp)+
qed


instantiation trace_class :: (chilbert_space, chilbert_space) order begin
lift_definition less_eq_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class \<Rightarrow> bool\<close> is
  less_eq.
lift_definition less_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class \<Rightarrow> bool\<close> is
  less.
instance
  apply intro_classes
     apply (auto simp add: less_eq_trace_class.rep_eq less_trace_class.rep_eq)
  by (simp add: from_trace_class_inject)
end


lift_definition compose_tcl :: \<open>('a::chilbert_space, 'b::chilbert_space) trace_class \<Rightarrow> ('c::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> ('c,'b) trace_class\<close> is
  \<open>cblinfun_compose :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'c \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> 'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  by (simp add: trace_class_comp_left)

lift_definition compose_tcr :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) \<Rightarrow> ('c::chilbert_space, 'a) trace_class \<Rightarrow> ('c,'b) trace_class\<close> is
  \<open>cblinfun_compose :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'c \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> 'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  by (simp add: trace_class_comp_right)

lemma norm_compose_tcl: \<open>norm (compose_tcl a b) \<le> norm a * norm b\<close>
  by (auto intro!: trace_norm_comp_left simp: norm_trace_class.rep_eq compose_tcl.rep_eq)

lemma norm_compose_tcr: \<open>norm (compose_tcr a b) \<le> norm a * norm b\<close>
  by (auto intro!: trace_norm_comp_right simp: norm_trace_class.rep_eq compose_tcr.rep_eq)

interpretation compose_tcl: bounded_cbilinear compose_tcl
proof (intro bounded_cbilinear.intro exI[of _ 1] allI)
  fix a a' :: \<open>('a,'b) trace_class\<close> and b b' :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and r :: complex
  show \<open>compose_tcl (a + a') b = compose_tcl a b + compose_tcl a' b\<close>
    apply transfer
    by (simp add: cblinfun_compose_add_left)
  show \<open>compose_tcl a (b + b') = compose_tcl a b + compose_tcl a b'\<close>
    apply transfer
    by (simp add: cblinfun_compose_add_right)
  show \<open>compose_tcl (r *\<^sub>C a) b = r *\<^sub>C compose_tcl a b\<close>
    apply transfer
    by simp
  show \<open>compose_tcl a (r *\<^sub>C b) = r *\<^sub>C compose_tcl a b\<close>
    apply transfer
    by simp
  show \<open>norm (compose_tcl a b) \<le> norm a * norm b * 1\<close>
    by (simp add: norm_compose_tcl)
qed

interpretation compose_tcr: bounded_cbilinear compose_tcr
proof (intro bounded_cbilinear.intro exI[of _ 1] allI)
  fix a a' :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and b b' :: \<open>('c,'a) trace_class\<close> and r :: complex
  show \<open>compose_tcr (a + a') b = compose_tcr a b + compose_tcr a' b\<close>
    apply transfer
    by (simp add: cblinfun_compose_add_left)
  show \<open>compose_tcr a (b + b') = compose_tcr a b + compose_tcr a b'\<close>
    apply transfer
    by (simp add: cblinfun_compose_add_right)
  show \<open>compose_tcr (r *\<^sub>C a) b = r *\<^sub>C compose_tcr a b\<close>
    apply transfer
    by simp
  show \<open>compose_tcr a (r *\<^sub>C b) = r *\<^sub>C compose_tcr a b\<close>
    apply transfer
    by simp
  show \<open>norm (compose_tcr a b) \<le> norm a * norm b * 1\<close>
    by (simp add: norm_compose_tcr)
qed

lemma trace_norm_sandwich: \<open>trace_norm (sandwich e t) \<le> (norm e)^2 * trace_norm t\<close> if \<open>trace_class t\<close>
  apply (simp add: sandwich_apply)
  by (smt (z3) Groups.mult_ac(2) more_arith_simps(11) mult_left_mono norm_adj norm_ge_zero power2_eq_square that trace_class_comp_right trace_norm_comp_left trace_norm_comp_right)

lemma trace_class_sandwich: \<open>trace_class b \<Longrightarrow> trace_class (sandwich a b)\<close>
  by (simp add: sandwich_apply trace_class_comp_right trace_class_comp_left)

definition \<open>sandwich_tc e t = compose_tcl (compose_tcr e t) (e*)\<close>

lemma sandwich_tc_transfer[transfer_rule]:
  includes lifting_syntax
  shows \<open>((=) ===> cr_trace_class ===> cr_trace_class) (\<lambda>e. (*\<^sub>V) (sandwich e)) sandwich_tc\<close>
  by (auto intro!: rel_funI simp: sandwich_tc_def cr_trace_class_def compose_tcl.rep_eq compose_tcr.rep_eq sandwich_apply)

lemma from_trace_class_sandwich_tc:
  \<open>from_trace_class (sandwich_tc e t) = sandwich e (from_trace_class t)\<close>
  apply transfer
  by (rule sandwich_apply)

lemma norm_sandwich_tc: \<open>norm (sandwich_tc e t) \<le> (norm e)^2 * norm t\<close>
  by (simp add: norm_trace_class.rep_eq from_trace_class_sandwich_tc trace_norm_sandwich)

lemma sandwich_tc_pos: \<open>sandwich_tc e t \<ge> 0\<close> if \<open>t \<ge> 0\<close>
  using that apply (transfer fixing: e)
  by (simp add: sandwich_pos)

lemma sandwich_tc_scaleC_right: \<open>sandwich_tc e (c *\<^sub>C t) = c *\<^sub>C sandwich_tc e t\<close>
  apply (transfer fixing: e c)
  by (simp add: cblinfun.scaleC_right)



lemma sandwich_tc_plus: \<open>sandwich_tc e (t + u) = sandwich_tc e t + sandwich_tc e u\<close>
  by (simp add: sandwich_tc_def compose_tcr.add_right compose_tcl.add_left)

lemma sandwich_tc_minus: \<open>sandwich_tc e (t - u) = sandwich_tc e t - sandwich_tc e u\<close>
  by (simp add: sandwich_tc_def compose_tcr.diff_right compose_tcl.diff_left)

lemma sandwich_tc_uminus_right: \<open>sandwich_tc e (- t) = - sandwich_tc e t\<close>
  by (metis (no_types, lifting) add.right_inverse arith_simps(50) diff_0 group_cancel.sub1 sandwich_tc_minus)

lemma trace_comp_pos:
  fixes a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>trace_class b\<close>
  assumes \<open>a \<ge> 0\<close> and \<open>b \<ge> 0\<close>
  shows \<open>trace (a o\<^sub>C\<^sub>L b) \<ge> 0\<close>
proof -
  obtain c :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where \<open>a = c* o\<^sub>C\<^sub>L c\<close>
  by (metis assms(2) positive_hermitianI sqrt_op_pos sqrt_op_square)
  then have \<open>trace (a o\<^sub>C\<^sub>L b) = trace (sandwich c b)\<close>
    by (simp add: sandwich_apply assms(1) cblinfun_assoc_left(1) circularity_of_trace trace_class_comp_right)
  also have \<open>\<dots> \<ge> 0\<close>
    by (auto intro!: trace_pos sandwich_pos assms)
  finally show ?thesis
    by -
qed


lemma trace_norm_one_dim: \<open>trace_norm x = cmod (one_dim_iso x)\<close>
  apply (rule of_real_eq_iff[where 'a=complex, THEN iffD1])
  apply (simp add: abs_op_one_dim flip: trace_abs_op)
  by (simp add: abs_complex_def)

lemma trace_norm_bounded:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>A \<ge> 0\<close> and \<open>trace_class B\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>trace_class A\<close>
proof -
  have \<open>(\<lambda>x. x \<bullet>\<^sub>C (B *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
    by (metis assms(2) is_onb_some_chilbert_basis summable_on_iff_abs_summable_on_complex trace_exists)
  then have \<open>(\<lambda>x. x \<bullet>\<^sub>C (A *\<^sub>V x)) abs_summable_on some_chilbert_basis\<close>
    apply (rule abs_summable_on_comparison_test)
    using \<open>A \<ge> 0\<close> \<open>A \<le> B\<close>
    by (auto intro!: cmod_mono cinner_pos_if_pos simp: abs_op_id_on_pos less_eq_cblinfun_def)
  then show ?thesis
    by (auto intro!: trace_classI[OF is_onb_some_chilbert_basis] simp: abs_op_id_on_pos \<open>A \<ge> 0\<close>)
qed

lemma trace_norm_cblinfun_mono:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>A \<ge> 0\<close> and \<open>trace_class B\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>trace_norm A \<le> trace_norm B\<close>
proof -
  from assms have \<open>trace_class A\<close>
    by (rule trace_norm_bounded)
  from \<open>A \<le> B\<close> and \<open>A \<ge> 0\<close>
  have \<open>B \<ge> 0\<close>
    by simp
  have \<open>cmod (x \<bullet>\<^sub>C (abs_op A *\<^sub>V x)) \<le> cmod (x \<bullet>\<^sub>C (abs_op B *\<^sub>V x))\<close> for x
    using \<open>A \<le> B\<close>
    unfolding less_eq_cblinfun_def
    using \<open>A \<ge> 0\<close> \<open>B \<ge> 0\<close> 
    by (auto intro!: cmod_mono cinner_pos_if_pos simp: abs_op_id_on_pos)
  then show \<open>trace_norm A \<le> trace_norm B\<close>
    using \<open>trace_class A\<close> \<open>trace_class B\<close>
    by (auto intro!: infsum_mono 
        simp add: trace_norm_def trace_class_iff_summable[OF is_onb_some_chilbert_basis])
qed



lemma norm_cblinfun_mono_trace_class:
  fixes A B :: \<open>('a::chilbert_space, 'a) trace_class\<close>
  assumes \<open>A \<ge> 0\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>norm A \<le> norm B\<close>
  using assms
  apply transfer
  apply (rule trace_norm_cblinfun_mono)
  by auto

lemma trace_norm_butterfly: \<open>trace_norm (butterfly a b) = (norm a) * (norm b)\<close>
  for a b :: \<open>_ :: chilbert_space\<close>
proof -
  have \<open>trace_norm (butterfly a b) = trace (abs_op (butterfly a b))\<close>
    by (simp flip: trace_abs_op)
  also have \<open>\<dots> = (norm a / norm b) * trace (selfbutter b)\<close>
    by (simp add: abs_op_butterfly scaleR_scaleC trace_scaleC del: trace_abs_op)
  also have \<open>\<dots> = (norm a / norm b) * trace ((vector_to_cblinfun b :: complex \<Rightarrow>\<^sub>C\<^sub>L _)* o\<^sub>C\<^sub>L vector_to_cblinfun b)\<close>
    apply (subst butterfly_def)
    apply (subst circularity_of_trace)
    by simp_all
  also have \<open>\<dots> = (norm a / norm b) * (b \<bullet>\<^sub>C b)\<close>
    by simp
  also have \<open>\<dots> = (norm a) * (norm b)\<close>
    by (simp add: cdot_square_norm power2_eq_square)
  finally show ?thesis
    using of_real_eq_iff by blast
qed


lemma from_trace_class_sum:
  shows \<open>from_trace_class (\<Sum>x\<in>M. f x) = (\<Sum>x\<in>M. from_trace_class (f x))\<close>
  apply (induction M rule:infinite_finite_induct)
  by (simp_all add: plus_trace_class.rep_eq)


lemma has_sum_mono_neutral_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  from assms(1)
  have \<open>((\<lambda>x. from_trace_class (f x)) has_sum from_trace_class a) A\<close>
    apply (rule Infinite_Sum.has_sum_bounded_linear[rotated])
    by (intro bounded_clinear_from_trace_class bounded_clinear.bounded_linear)
  moreover
  from assms(2)
  have \<open>((\<lambda>x. from_trace_class (g x)) has_sum from_trace_class b) B\<close>
    apply (rule Infinite_Sum.has_sum_bounded_linear[rotated])
    by (intro bounded_clinear_from_trace_class bounded_clinear.bounded_linear)
  ultimately have \<open>from_trace_class a \<le> from_trace_class b\<close>
    apply (rule has_sum_mono_neutral_cblinfun)
    using assms by (auto simp: less_eq_trace_class.rep_eq)
  then show ?thesis
    by (auto simp: less_eq_trace_class.rep_eq)
qed

lemma has_sum_mono_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "(f has_sum x) A" and "(g has_sum y) A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "x \<le> y"
  using assms has_sum_mono_neutral_traceclass by force

lemma infsum_mono_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "f summable_on A" and "g summable_on A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "infsum f A \<le> infsum g A"
  by (meson assms has_sum_infsum has_sum_mono_traceclass)

lemma infsum_mono_neutral_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "f summable_on A" and "g summable_on B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "infsum f A \<le> infsum g B"
  using assms(1) assms(2) assms(3) assms(4) assms(5) has_sum_mono_neutral_traceclass summable_iff_has_sum_infsum by blast

instance trace_class :: (chilbert_space, chilbert_space) ordered_complex_vector
  apply (intro_classes; transfer)
  by (auto intro!: scaleC_left_mono scaleC_right_mono)

lemma Abs_trace_class_geq0I: \<open>0 \<le> Abs_trace_class t\<close> if \<open>trace_class t\<close> and \<open>t \<ge> 0\<close>
  using that by (simp add: zero_trace_class.abs_eq less_eq_trace_class.abs_eq eq_onp_def)

lift_definition tc_compose :: \<open>('b::chilbert_space, 'c::chilbert_space) trace_class 
                               \<Rightarrow> ('a::chilbert_space, 'b) trace_class \<Rightarrow> ('a,'c) trace_class\<close> is
    cblinfun_compose
  by (simp add: trace_class_comp_left)

lemma norm_tc_compose:
  \<open>norm (tc_compose a b) \<le> norm a * norm b\<close>
proof transfer
  fix a :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and b :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'c\<close>
  assume \<open>a \<in> Collect trace_class\<close> and tc_b: \<open>b \<in> Collect trace_class\<close>
  then have \<open>trace_norm (a o\<^sub>C\<^sub>L b) \<le> trace_norm a * norm b\<close>
    by (simp add: trace_norm_comp_left)
  also have \<open>\<dots> \<le> trace_norm a * trace_norm b\<close>
    using tc_b by (auto intro!: mult_left_mono norm_leq_trace_norm)
  finally show \<open>trace_norm (a o\<^sub>C\<^sub>L b) \<le> trace_norm a * trace_norm b\<close>
    by -
qed


lift_definition trace_tc :: \<open>('a::chilbert_space, 'a) trace_class \<Rightarrow> complex\<close> is trace.

lemma trace_tc_plus: \<open>trace_tc (a + b) = trace_tc a + trace_tc b\<close>
  apply transfer by (simp add: trace_plus)

lemma trace_tc_scaleC: \<open>trace_tc (c *\<^sub>C a) = c *\<^sub>C trace_tc a\<close>
  apply transfer by (simp add: trace_scaleC)

lemma trace_tc_norm: \<open>norm (trace_tc a) \<le> norm a\<close>
  apply transfer by auto

lemma bounded_clinear_trace_tc[bounded_clinear, simp]: \<open>bounded_clinear trace_tc\<close>
  apply (rule bounded_clinearI[where K=1])
  by (auto simp: trace_tc_scaleC trace_tc_plus intro!: trace_tc_norm)


lemma norm_tc_pos: \<open>norm A = trace_tc A\<close> if \<open>A \<ge> 0\<close>
   using that apply transfer by (simp add: trace_norm_pos)

lemma norm_tc_pos_Re: \<open>norm A = Re (trace_tc A)\<close> if \<open>A \<ge> 0\<close>
  using norm_tc_pos[OF that]
  by (metis Re_complex_of_real)

lemma from_trace_class_pos: \<open>from_trace_class A \<ge> 0 \<longleftrightarrow> A \<ge> 0\<close>
  by (simp add: less_eq_trace_class.rep_eq)

lemma infsum_tc_norm_bounded_abs_summable:
  fixes A :: \<open>'a \<Rightarrow> ('b::chilbert_space, 'b::chilbert_space) trace_class\<close>
  assumes pos: \<open>\<And>x. x \<in> M \<Longrightarrow> A x \<ge> 0\<close>
  assumes bound_B: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> M \<Longrightarrow> norm (\<Sum>x\<in>F. A x) \<le> B\<close>
  shows \<open>A abs_summable_on M\<close>
proof -
  have \<open>(\<Sum>x\<in>F. norm (A x)) = norm (\<Sum>x\<in>F. A x)\<close> if \<open>F \<subseteq> M\<close> for F
  proof -
    have \<open>complex_of_real (\<Sum>x\<in>F. norm (A x)) = (\<Sum>x\<in>F. complex_of_real (trace_norm (from_trace_class (A x))))\<close>
      by (simp add: norm_trace_class.rep_eq trace_norm_pos)
    also have \<open>\<dots> = (\<Sum>x\<in>F. trace (from_trace_class (A x)))\<close>
      using that pos by (auto intro!: sum.cong simp add: trace_norm_pos less_eq_trace_class.rep_eq)
    also have \<open>\<dots> = trace (from_trace_class (\<Sum>x\<in>F. A x))\<close>
      by (simp add: from_trace_class_sum trace_sum)
    also have \<open>\<dots> = norm (\<Sum>x\<in>F. A x)\<close>
      by (smt (verit, ccfv_threshold) calculation norm_of_real norm_trace_class.rep_eq sum_norm_le trace_leq_trace_norm)
    finally show ?thesis
      using of_real_eq_iff by blast
  qed
  with bound_B have bound_B': \<open>(\<Sum>x\<in>F. norm (A x)) \<le> B\<close> if \<open>finite F\<close> and \<open>F \<subseteq> M\<close> for F
    by (metis that(1) that(2))
  then show \<open>A abs_summable_on M\<close>
    apply (rule_tac nonneg_bdd_above_summable_on)
    by (auto intro!: bdd_aboveI)
qed

lemma trace_norm_uminus[simp]: \<open>trace_norm (-a) = trace_norm a\<close>
  by (metis abs_op_uminus of_real_eq_iff trace_abs_op)

lemma trace_norm_triangle_minus: 
  fixes a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes [simp]: \<open>trace_class a\<close> \<open>trace_class b\<close>
  shows \<open>trace_norm (a - b) \<le> trace_norm a + trace_norm b\<close>
  using trace_norm_triangle[of a \<open>-b\<close>]
  by auto

lemma trace_norm_abs_op[simp]: \<open>trace_norm (abs_op t) = trace_norm t\<close>
  by (simp add: trace_norm_def)

lemma
  fixes t :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space\<close>
  shows cblinfun_decomp_4pos: \<open>
             \<exists>t1 t2 t3 t4.
              t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4
               \<and> t1 \<ge> 0 \<and> t2 \<ge> 0 \<and> t3 \<ge> 0 \<and> t4 \<ge> 0\<close>  (is ?thesis1)
  and trace_class_decomp_4pos: \<open>trace_class t \<Longrightarrow>
             \<exists>t1 t2 t3 t4.
              t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4
               \<and> trace_class t1 \<and> trace_class t2 \<and> trace_class t3 \<and> trace_class t4
               \<and> trace_norm t1 \<le> trace_norm t \<and> trace_norm t2 \<le> trace_norm t \<and> trace_norm t3 \<le> trace_norm t \<and> trace_norm t4 \<le> trace_norm t 
               \<and> t1 \<ge> 0 \<and> t2 \<ge> 0 \<and> t3 \<ge> 0 \<and> t4 \<ge> 0\<close> (is \<open>_ \<Longrightarrow> ?thesis2\<close>)
proof -
  define th ta where \<open>th = (1/2) *\<^sub>C (t + t*)\<close> and \<open>ta = (-\<i>/2) *\<^sub>C (t - t*)\<close>
  have th_herm: \<open>th* = th\<close>
    by (simp add: adj_plus th_def)
  have \<open>ta* = ta\<close>
    by (simp add: adj_minus ta_def scaleC_diff_right adj_uminus)
  have \<open>t = th + \<i> *\<^sub>C ta\<close>
    by (smt (verit, ccfv_SIG) add.commute add.inverse_inverse complex_i_mult_minus complex_vector.vector_space_assms(1) complex_vector.vector_space_assms(3) diff_add_cancel group_cancel.add2 i_squared scaleC_half_double ta_def th_def times_divide_eq_right)
  define t1 t2 where \<open>t1 = (abs_op th + th) /\<^sub>R 2\<close> and \<open>t2 = (abs_op th - th) /\<^sub>R 2\<close>
  have \<open>t1 \<ge> 0\<close>
    using abs_op_geq_neq[unfolded selfadjoint_def, OF \<open>th* = th\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t1_def intro!: scaleR_nonneg_nonneg)
  have \<open>t2 \<ge> 0\<close>
    using abs_op_geq[unfolded selfadjoint_def, OF \<open>th* = th\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t2_def intro!: scaleR_nonneg_nonneg)
  have \<open>th = t1 - t2\<close>
    apply (simp add: t1_def t2_def)
    by (metis (no_types, opaque_lifting) Extra_Ordered_Fields.sign_simps(8) diff_add_cancel ordered_field_class.sign_simps(2) ordered_field_class.sign_simps(27) scaleR_half_double)
  define t3 t4 where \<open>t3 = (abs_op ta + ta) /\<^sub>R 2\<close> and \<open>t4 = (abs_op ta - ta) /\<^sub>R 2\<close>
  have \<open>t3 \<ge> 0\<close>
    using abs_op_geq_neq[unfolded selfadjoint_def, OF \<open>ta* = ta\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t3_def intro!: scaleR_nonneg_nonneg)
  have \<open>t4 \<ge> 0\<close>
    using abs_op_geq[unfolded selfadjoint_def, OF \<open>ta* = ta\<close>] ordered_field_class.sign_simps(15)
    by (fastforce simp add: t4_def intro!: scaleR_nonneg_nonneg)
  have \<open>ta = t3 - t4\<close>
    apply (simp add: t3_def t4_def)
    by (metis (no_types, opaque_lifting) Extra_Ordered_Fields.sign_simps(8) diff_add_cancel ordered_field_class.sign_simps(2) ordered_field_class.sign_simps(27) scaleR_half_double)
  have decomp: \<open>t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4\<close>
    by (simp add: \<open>t = th + \<i> *\<^sub>C ta\<close> \<open>th = t1 - t2\<close> \<open>ta = t3 - t4\<close> scaleC_diff_right)
  from decomp \<open>t1 \<ge> 0\<close> \<open>t2 \<ge> 0\<close> \<open>t3 \<ge> 0\<close> \<open>t4 \<ge> 0\<close>
  show ?thesis1
    by auto
  show ?thesis2 if \<open>trace_class t\<close>
  proof -
    have \<open>trace_class th\<close> \<open>trace_class ta\<close>
      by (auto simp add: th_def ta_def
          intro!: \<open>trace_class t\<close> trace_class_scaleC trace_class_plus trace_class_minus trace_class_uminus trace_class_adj)
    then have tc: \<open>trace_class t1\<close> \<open>trace_class t2\<close> \<open>trace_class t3\<close> \<open>trace_class t4\<close>
      by (auto simp add: t1_def t2_def t3_def t4_def scaleR_scaleC intro!: trace_class_scaleC)
    have tn_th: \<open>trace_norm th \<le> trace_norm t\<close>
      using trace_norm_triangle[of t \<open>t*\<close>] 
      by (auto simp add: that th_def trace_norm_scaleC)
    have tn_ta: \<open>trace_norm ta \<le> trace_norm t\<close>
      using trace_norm_triangle_minus[of t \<open>t*\<close>] 
      by (auto simp add: that ta_def trace_norm_scaleC)
    have tn1: \<open>trace_norm t1 \<le> trace_norm t\<close>
      using trace_norm_triangle[of \<open>abs_op th\<close> th] tn_th
      by (auto simp add: \<open>trace_class th\<close> t1_def trace_norm_scaleC scaleR_scaleC)
    have tn2: \<open>trace_norm t2 \<le> trace_norm t\<close>
      using trace_norm_triangle_minus[of \<open>abs_op th\<close> th] tn_th
      by (auto simp add: \<open>trace_class th\<close> t2_def trace_norm_scaleC scaleR_scaleC)
    have tn3: \<open>trace_norm t3 \<le> trace_norm t\<close>
      using trace_norm_triangle[of \<open>abs_op ta\<close> ta] tn_ta
      by (auto simp add: \<open>trace_class ta\<close> t3_def trace_norm_scaleC scaleR_scaleC)
    have tn4: \<open>trace_norm t4 \<le> trace_norm t\<close>
      using trace_norm_triangle_minus[of \<open>abs_op ta\<close> ta] tn_ta
      by (auto simp add: \<open>trace_class ta\<close> t4_def trace_norm_scaleC scaleR_scaleC)
    from decomp tc \<open>t1 \<ge> 0\<close> \<open>t2 \<ge> 0\<close> \<open>t3 \<ge> 0\<close> \<open>t4 \<ge> 0\<close> tn1 tn2 tn3 tn4
    show ?thesis2
      by auto
  qed
qed

lemma trace_class_decomp_4pos':
  fixes t :: \<open>('a::chilbert_space,'a) trace_class\<close>
  shows \<open>\<exists>t1 t2 t3 t4.
              t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4
               \<and> norm t1 \<le> norm t \<and> norm t2 \<le> norm t \<and> norm t3 \<le> norm t \<and> norm t4 \<le> norm t 
               \<and> t1 \<ge> 0 \<and> t2 \<ge> 0 \<and> t3 \<ge> 0 \<and> t4 \<ge> 0\<close>
proof -
  from trace_class_decomp_4pos[of \<open>from_trace_class t\<close>, OF trace_class_from_trace_class]
  obtain t1' t2' t3' t4'
    where *: \<open>from_trace_class t = t1' - t2' + \<i> *\<^sub>C t3' - \<i> *\<^sub>C t4'
               \<and> trace_class t1' \<and> trace_class t2' \<and> trace_class t3' \<and> trace_class t4'
               \<and> trace_norm t1' \<le> trace_norm (from_trace_class t) \<and> trace_norm t2' \<le> trace_norm (from_trace_class t) \<and> trace_norm t3' \<le> trace_norm (from_trace_class t) \<and> trace_norm t4' \<le> trace_norm (from_trace_class t) 
               \<and> t1' \<ge> 0 \<and> t2' \<ge> 0 \<and> t3' \<ge> 0 \<and> t4' \<ge> 0\<close>
    by auto
  then obtain t1 t2 t3 t4 where
    t1234: \<open>t1' = from_trace_class t1\<close> \<open>t2' = from_trace_class t2\<close> \<open>t3' = from_trace_class t3\<close> \<open>t4' = from_trace_class t4\<close>
    by (metis from_trace_class_cases mem_Collect_eq)
  with * have n1234: \<open>norm t1 \<le> norm t\<close> \<open>norm t2 \<le> norm t\<close> \<open>norm t3 \<le> norm t\<close> \<open>norm t4 \<le> norm t\<close>
    by (metis norm_trace_class.rep_eq)+
  have t_decomp: \<open>t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4\<close>
    using * unfolding t1234 
    by (auto simp: from_trace_class_inject
        simp flip: scaleC_trace_class.rep_eq plus_trace_class.rep_eq minus_trace_class.rep_eq)
  have pos1234: \<open>t1 \<ge> 0\<close> \<open>t2 \<ge> 0\<close> \<open>t3 \<ge> 0\<close> \<open>t4 \<ge> 0\<close>
    using * unfolding t1234 
    by (auto simp: less_eq_trace_class_def)
  from t_decomp pos1234 n1234
  show ?thesis
    by blast
qed

thm bounded_clinear_trace_duality
lemma bounded_clinear_trace_duality': \<open>trace_class t \<Longrightarrow> bounded_clinear (\<lambda>a. trace (a o\<^sub>C\<^sub>L t))\<close> for t :: \<open>_::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space\<close>
  apply (rule bounded_clinearI[where K=\<open>trace_norm t\<close>])
    apply (auto simp add: cblinfun_compose_add_left trace_class_comp_right trace_plus trace_scaleC)[2]
  by (metis circularity_of_trace order_trans trace_leq_trace_norm trace_norm_comp_right)

lemma infsum_nonneg_traceclass:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space, 'b) trace_class"
  assumes "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsum f M \<ge> 0"
  apply (cases \<open>f summable_on M\<close>)
   apply (subst infsum_0_simp[symmetric])
   apply (rule infsum_mono_neutral_traceclass)
  using assms by (auto simp: infsum_not_exists)

lemma sandwich_tc_compose: \<open>sandwich_tc (A o\<^sub>C\<^sub>L B) = sandwich_tc A o sandwich_tc B\<close>
  apply (rule ext)
  apply (rule from_trace_class_inject[THEN iffD1])
  apply (transfer fixing: A B)
  by (simp add: sandwich_compose)

lemma sandwich_tc_0_left[simp]: \<open>sandwich_tc 0 = 0\<close>
  by (auto intro!: ext simp add: sandwich_tc_def compose_tcl.zero_left compose_tcr.zero_left)

lemma sandwich_tc_0_right[simp]: \<open>sandwich_tc e 0 = 0\<close>
  by (auto intro!: ext simp add: sandwich_tc_def compose_tcl.zero_left compose_tcr.zero_right)

lemma sandwich_tc_scaleC_left: \<open>sandwich_tc (c *\<^sub>C e) t = (cmod c)^2 *\<^sub>C sandwich_tc e t\<close>
  apply (rule from_trace_class_inject[THEN iffD1])
  by (simp add: from_trace_class_sandwich_tc scaleC_trace_class.rep_eq
      sandwich_scaleC_left)

lemma sandwich_tc_scaleR_left: \<open>sandwich_tc (r *\<^sub>R e) t = r^2 *\<^sub>R sandwich_tc e t\<close>
  by (simp add: scaleR_scaleC sandwich_tc_scaleC_left flip: of_real_power)

lemma bounded_cbilinear_tc_compose: \<open>bounded_cbilinear tc_compose\<close>
  unfolding bounded_cbilinear_def
  apply transfer
  apply (auto intro!: exI[of _ 1] simp: cblinfun_compose_add_left cblinfun_compose_add_right)
  by (meson norm_leq_trace_norm dual_order.trans mult_right_mono trace_norm_comp_right trace_norm_nneg)
lemmas bounded_clinear_tc_compose_left[bounded_clinear] = bounded_cbilinear.bounded_clinear_left[OF bounded_cbilinear_tc_compose]
lemmas bounded_clinear_tc_compose_right[bounded_clinear] = bounded_cbilinear.bounded_clinear_right[OF bounded_cbilinear_tc_compose]

lift_definition tc_butterfly :: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space \<Rightarrow> ('b,'a) trace_class\<close>
  is butterfly
  by simp

lemma norm_tc_butterfly: \<open>norm (tc_butterfly \<psi> \<phi>) = norm \<psi> * norm \<phi>\<close>
  apply (transfer fixing: \<psi> \<phi>)
  by (simp add: trace_norm_butterfly)

lemma comp_tc_butterfly[simp]: \<open>tc_compose (tc_butterfly a b) (tc_butterfly c d) = (b \<bullet>\<^sub>C c) *\<^sub>C tc_butterfly a d\<close>
  apply transfer'
  by simp

lemma tc_butterfly_pos[simp]: \<open>0 \<le> tc_butterfly \<psi> \<psi>\<close>
  apply transfer
  by simp

lift_definition rank1_tc :: \<open>('a::chilbert_space, 'b::chilbert_space) trace_class \<Rightarrow> bool\<close> is rank1.
lift_definition finite_rank_tc :: \<open>('a::chilbert_space, 'b::chilbert_space) trace_class \<Rightarrow> bool\<close> is finite_rank.

lemma finite_rank_tc_0[iff]: \<open>finite_rank_tc 0\<close>
  apply transfer by simp

lemma finite_rank_tc_plus: \<open>finite_rank_tc (a + b)\<close>
  if \<open>finite_rank_tc a\<close> and \<open>finite_rank_tc b\<close>
  using that apply transfer
  by simp

lemma finite_rank_tc_scale: \<open>finite_rank_tc (c *\<^sub>C a)\<close> if \<open>finite_rank_tc a\<close>
  using that apply transfer by simp

lemma csubspace_finite_rank_tc: \<open>csubspace (Collect finite_rank_tc)\<close>
  apply (rule complex_vector.subspaceI)
  by (auto intro!: finite_rank_tc_plus finite_rank_tc_scale)

lemma rank1_trace_class: \<open>trace_class a\<close> if \<open>rank1 a\<close>
  for a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  using that by (auto intro!: simp: rank1_iff_butterfly)

lemma finite_rank_trace_class: \<open>trace_class a\<close> if \<open>finite_rank a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
proof -
  from \<open>finite_rank a\<close> obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> Collect rank1\<close>
    and a_def: \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
    by (smt (verit, ccfv_threshold) complex_vector.span_explicit finite_rank_def mem_Collect_eq)
  then show \<open>trace_class a\<close>
    unfolding a_def
    apply induction
    by (auto intro!: trace_class_plus trace_class_scaleC intro: rank1_trace_class)
qed

lemma trace_minus: 
  assumes \<open>trace_class a\<close> \<open>trace_class b\<close>
  shows \<open>trace (a - b) = trace a - trace b\<close>
  by (metis (no_types, lifting) add_uminus_conv_diff assms(1) assms(2) trace_class_uminus trace_plus trace_uminus)

lemma trace_cblinfun_mono:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>trace_class A\<close> and \<open>trace_class B\<close>
  assumes \<open>A \<le> B\<close>
  shows \<open>trace A \<le> trace B\<close>
proof -
  have sumA: \<open>(\<lambda>e. e \<bullet>\<^sub>C (A *\<^sub>V e)) summable_on some_chilbert_basis\<close>
    by (auto intro!: trace_exists assms)
  moreover have sumB: \<open>(\<lambda>e. e \<bullet>\<^sub>C (B *\<^sub>V e)) summable_on some_chilbert_basis\<close>
    by (auto intro!: trace_exists assms)
  moreover have \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<le> x \<bullet>\<^sub>C (B *\<^sub>V x)\<close> for x
    using assms(3) less_eq_cblinfun_def by blast
  ultimately have \<open>(\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C (A *\<^sub>V e)) \<le> (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C (B *\<^sub>V e))\<close>
    by (rule infsum_mono_complex)
  then show ?thesis
    by (metis assms(1) assms(2) assms(3) diff_ge_0_iff_ge trace_minus trace_pos)
qed

lemma trace_tc_mono:
  assumes \<open>A \<le> B\<close>
  shows \<open>trace_tc A \<le> trace_tc B\<close>
  using assms
  apply transfer
  by (simp add: trace_cblinfun_mono)

lemma trace_tc_0[simp]: \<open>trace_tc 0 = 0\<close>
  apply transfer' by simp

lemma cspan_tc_transfer[transfer_rule]: 
  includes lifting_syntax
  shows \<open>(rel_set cr_trace_class ===> rel_set cr_trace_class) cspan cspan\<close>
proof (intro rel_funI rel_setI)
  fix B :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close> and C
  assume \<open>rel_set cr_trace_class B C\<close>
  then have BC: \<open>B = from_trace_class ` C\<close>
    by (auto intro!: simp: cr_trace_class_def image_iff rel_set_def)

  show \<open>\<exists>t\<in>cspan C. cr_trace_class a t\<close> if \<open>a \<in> cspan B\<close> for a
  proof -
    from that obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> B\<close> and a_sum: \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
      by (auto simp: complex_vector.span_explicit)
    from \<open>F \<subseteq> B\<close>
    obtain F' where \<open>F' \<subseteq> C\<close> and FF': \<open>F = from_trace_class ` F'\<close>
      by (auto elim!: subset_imageE simp: BC)
    define t where \<open>t = (\<Sum>x\<in>F'. f (from_trace_class x) *\<^sub>C x)\<close>
    have \<open>a = from_trace_class t\<close>
      by (simp add: a_sum t_def from_trace_class_sum scaleC_trace_class.rep_eq FF'
          sum.reindex o_def from_trace_class_inject inj_on_def)
    moreover have \<open>t \<in> cspan C\<close>
      by (metis (no_types, lifting) \<open>F' \<subseteq> C\<close> complex_vector.span_clauses(4) complex_vector.span_sum complex_vector.span_superset subsetD t_def)
    ultimately show \<open>\<exists>t\<in>cspan C. cr_trace_class a t\<close>
      by (auto simp: cr_trace_class_def)
  qed

  show \<open>\<exists>a\<in>cspan B. cr_trace_class a t\<close> if \<open>t \<in> cspan C\<close> for t
  proof -
    from that obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> C\<close> and t_sum: \<open>t = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
      by (auto simp: complex_vector.span_explicit)
    define a where \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C from_trace_class x)\<close>
    then have \<open>a = from_trace_class t\<close>
      by (simp add: t_sum a_def from_trace_class_sum scaleC_trace_class.rep_eq)
    moreover have \<open>a \<in> cspan B\<close>
      using BC \<open>F \<subseteq> C\<close> 
      by (auto intro!: complex_vector.span_base complex_vector.span_sum complex_vector.span_scale simp: a_def)
    ultimately show ?thesis
      by (auto simp: cr_trace_class_def)
  qed
qed

lemma finite_rank_tc_def': \<open>finite_rank_tc A \<longleftrightarrow> A \<in> cspan (Collect rank1_tc)\<close>
  apply transfer'
  apply (auto simp: finite_rank_def)
  apply (metis (no_types, lifting) Collect_cong rank1_trace_class)
  by (metis (no_types, lifting) Collect_cong rank1_trace_class)


lemma tc_butterfly_add_left: \<open>tc_butterfly (a + a') b = tc_butterfly a b + tc_butterfly a' b\<close>
  apply transfer
  by (rule butterfly_add_left)

lemma tc_butterfly_add_right: \<open>tc_butterfly a (b + b') = tc_butterfly a b + tc_butterfly a b'\<close>
  apply transfer
  by (rule butterfly_add_right)

lemma tc_butterfly_sum_left: \<open>tc_butterfly (\<Sum>i\<in>M. \<psi> i) \<phi> = (\<Sum>i\<in>M. tc_butterfly (\<psi> i) \<phi>)\<close>
  apply transfer
  by (rule butterfly_sum_left)

lemma tc_butterfly_sum_right: \<open>tc_butterfly \<psi> (\<Sum>i\<in>M. \<phi> i) = (\<Sum>i\<in>M. tc_butterfly \<psi> (\<phi> i))\<close>
  apply transfer
  by (rule butterfly_sum_right)

lemma tc_butterfly_scaleC_left[simp]: "tc_butterfly (c *\<^sub>C \<psi>) \<phi> = c *\<^sub>C tc_butterfly \<psi> \<phi>"
  apply transfer by simp

lemma tc_butterfly_scaleC_right[simp]: "tc_butterfly \<psi> (c *\<^sub>C \<phi>) = cnj c *\<^sub>C tc_butterfly \<psi> \<phi>"
  apply transfer by simp

lemma bounded_sesquilinear_tc_butterfly[iff]: \<open>bounded_sesquilinear (\<lambda>a b. tc_butterfly b a)\<close>
  by (auto intro!: bounded_sesquilinear.intro exI[of _ 1]
      simp: tc_butterfly_add_left tc_butterfly_add_right norm_tc_butterfly)


lemma trace_norm_plus_orthogonal:
  assumes \<open>trace_class a\<close> and \<open>trace_class b\<close>
  assumes \<open>a* o\<^sub>C\<^sub>L b = 0\<close> and \<open>a o\<^sub>C\<^sub>L b* = 0\<close>
  shows \<open>trace_norm (a + b) = trace_norm a + trace_norm b\<close>
proof -
  have \<open>trace_norm (a + b) = trace (abs_op (a + b))\<close>
    by simp
  also have \<open>\<dots> = trace (abs_op a + abs_op b)\<close>
   by (simp add: abs_op_plus_orthogonal assms)
  also have \<open>\<dots> = trace (abs_op a) + trace (abs_op b)\<close>
    by (simp add: assms trace_plus)
  also have \<open>\<dots> = trace_norm a + trace_norm b\<close>
    by simp
  finally show ?thesis
    using of_real_eq_iff by blast
qed

lemma norm_tc_plus_orthogonal:
  assumes \<open>tc_compose (adj_tc a) b = 0\<close> and \<open>tc_compose a (adj_tc b) = 0\<close>
  shows \<open>norm (a + b) = norm a + norm b\<close>
  using assms apply transfer
  by (auto intro!: trace_norm_plus_orthogonal)


lemma trace_norm_sum_exchange:
  fixes t :: \<open>_ \<Rightarrow> (_::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space)\<close>
  assumes \<open>\<And>i. i \<in> F \<Longrightarrow> trace_class (t i)\<close>
  assumes \<open>\<And>i j. i \<in> F \<Longrightarrow> j \<in> F \<Longrightarrow> i \<noteq> j \<Longrightarrow> (t i)* o\<^sub>C\<^sub>L t j = 0\<close>
  assumes \<open>\<And>i j. i \<in> F \<Longrightarrow> j \<in> F \<Longrightarrow> i \<noteq> j \<Longrightarrow> t i o\<^sub>C\<^sub>L (t j)* = 0\<close>
  shows \<open>trace_norm (\<Sum>i\<in>F. t i) = (\<Sum>i\<in>F. trace_norm (t i))\<close>
proof (insert assms, induction F rule:infinite_finite_induct)
  case (infinite A)
  then show ?case
    by simp
next
  case empty
  show ?case
    by simp
next
  case (insert x F)
  have \<open>trace_norm (\<Sum>i\<in>insert x F. t i) = trace_norm (t x + (\<Sum>x\<in>F. t x))\<close>
    by (simp add: insert)
  also have \<open>\<dots> = trace_norm (t x) + trace_norm (\<Sum>x\<in>F. t x)\<close>
  proof (rule trace_norm_plus_orthogonal)
    show \<open>trace_class (t x)\<close>
      by (simp add: insert.prems)
    show \<open>trace_class (\<Sum>x\<in>F. t x)\<close>
      by (simp add: trace_class_sum insert.prems)
    show \<open>t x* o\<^sub>C\<^sub>L (\<Sum>x\<in>F. t x) = 0\<close>
      by (auto intro!: sum.neutral insert.prems simp: cblinfun_compose_sum_right sum_adj insert.hyps)
    show \<open>t x o\<^sub>C\<^sub>L (\<Sum>x\<in>F. t x)* = 0\<close>
      by (auto intro!: sum.neutral insert.prems simp: cblinfun_compose_sum_right sum_adj insert.hyps)
  qed
  also have \<open>\<dots> = trace_norm (t x) + (\<Sum>x\<in>F. trace_norm (t x))\<close>
    apply (subst insert.IH)
    by (simp_all add: insert.prems)
  also have \<open>\<dots> = (\<Sum>i\<in>insert x F. trace_norm (t i))\<close>
    by (simp add: insert)
  finally show ?case
    by -
qed

lemma norm_tc_sum_exchange:
  assumes \<open>\<And>i j. i \<in> F \<Longrightarrow> j \<in> F \<Longrightarrow> i \<noteq> j \<Longrightarrow> tc_compose (adj_tc (t i)) (t j) = 0\<close>
  assumes \<open>\<And>i j. i \<in> F \<Longrightarrow> j \<in> F \<Longrightarrow> i \<noteq> j \<Longrightarrow> tc_compose (t i) (adj_tc (t j)) = 0\<close>
  shows \<open>norm (\<Sum>i\<in>F. t i) = (\<Sum>i\<in>F. norm (t i))\<close>
  using assms apply transfer
  by (auto intro!: trace_norm_sum_exchange)


instantiation trace_class :: (one_dim, one_dim) complex_inner begin
lift_definition cinner_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class \<Rightarrow> complex\<close> is \<open>(\<bullet>\<^sub>C)\<close>.
instance
proof intro_classes
  fix x y z :: \<open>('a, 'b) trace_class\<close>
  show \<open>x \<bullet>\<^sub>C y = cnj (y \<bullet>\<^sub>C x)\<close>
    apply transfer'
    by simp
  show \<open>(x + y) \<bullet>\<^sub>C z = x \<bullet>\<^sub>C z + y \<bullet>\<^sub>C z\<close>
    apply transfer'
    by (simp add: cinner_simps)
  show \<open>r *\<^sub>C x \<bullet>\<^sub>C y = cnj r * (x \<bullet>\<^sub>C y)\<close> for r
    apply (transfer' fixing: r)
    using cinner_simps by blast
  show \<open>0 \<le> x \<bullet>\<^sub>C x\<close>
    apply transfer'
    by simp
  show \<open>(x \<bullet>\<^sub>C x = 0) = (x = 0)\<close>
    apply transfer'
    by auto
  show \<open>norm x = sqrt (cmod (x \<bullet>\<^sub>C x))\<close>
  proof transfer'
    fix x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    define c :: complex where \<open>c = one_dim_iso x\<close>
    then have xc: \<open>x = c *\<^sub>C 1\<close>
      by simp
    have \<open>trace_norm x = norm c\<close>
      by (simp add: trace_norm_one_dim xc)
    also have \<open>norm c = sqrt (cmod (x \<bullet>\<^sub>C x))\<close>
      by (metis inner_real_def norm_eq_sqrt_cinner norm_one norm_scaleC real_inner_1_right xc)
    finally show \<open>trace_norm x = sqrt (cmod (x \<bullet>\<^sub>C x)) \<close>
      by (simp add: cinner_cblinfun_def)
  qed
qed
end


instantiation trace_class :: (one_dim, one_dim) one_dim begin
lift_definition one_trace_class :: \<open>('a, 'b) trace_class\<close> is 1
  by auto
lift_definition times_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class\<close> is \<open>(*)\<close>
  by auto
lift_definition divide_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class\<close> is \<open>(/)\<close>
  by auto
lift_definition inverse_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class\<close> is \<open>Fields.inverse\<close>
  by auto
definition canonical_basis_trace_class :: \<open>('a, 'b) trace_class list\<close> where \<open>canonical_basis_trace_class = [1]\<close>
definition canonical_basis_length_trace_class :: \<open>('a, 'b) trace_class itself \<Rightarrow> nat\<close> where \<open>canonical_basis_length_trace_class = 1\<close>
instance
proof intro_classes
  fix x y z :: \<open>('a, 'b) trace_class\<close>
  have [simp]: \<open>1 \<noteq> (0 :: ('a, 'b) trace_class)\<close>
    using one_trace_class.rep_eq by force
  then have [simp]: \<open>0 \<noteq> (1 :: ('a, 'b) trace_class)\<close>
    by force
  show \<open>distinct (canonical_basis :: (_,_) trace_class list)\<close>
    by (simp add: canonical_basis_trace_class_def)
  show \<open>cindependent (set canonical_basis :: (_,_) trace_class set)\<close>
    by (simp add: canonical_basis_trace_class_def)
  show \<open>canonical_basis_length TYPE(('a, 'b) trace_class) = length (canonical_basis :: (_,_) trace_class list)\<close>
    by (simp add: canonical_basis_length_trace_class_def canonical_basis_trace_class_def)
  show \<open>x \<in> set canonical_basis \<Longrightarrow> norm x = 1\<close>
    apply (simp add: canonical_basis_trace_class_def)
    by (smt (verit, ccfv_threshold) one_trace_class_def cinner_trace_class.abs_eq cnorm_eq_1 one_cinner_one one_trace_class.rsp)
  show \<open>canonical_basis = [1 :: ('a,'b) trace_class]\<close>
    by (simp add: canonical_basis_trace_class_def)
  show \<open>a *\<^sub>C 1 * b *\<^sub>C 1 = (a * b) *\<^sub>C (1 :: ('a,'b) trace_class)\<close> for a b :: complex
    apply (transfer' fixing: a b)
    by simp
  show \<open>x div y = x * inverse y\<close>
    apply transfer'
    by (simp add: divide_cblinfun_def)
  show \<open>inverse (a *\<^sub>C 1 :: ('a,'b) trace_class) = 1 /\<^sub>C a\<close> for a :: complex
    apply transfer'
    by simp
  show \<open>is_ortho_set (set canonical_basis :: ('a,'b) trace_class set)\<close>
    by (simp add: is_ortho_set_def canonical_basis_trace_class_def)
  show \<open>cspan (set canonical_basis :: ('a,'b) trace_class set) = UNIV\<close>
  proof (intro Set.set_eqI iffI UNIV_I)
    fix x :: \<open>('a,'b) trace_class\<close>
    have \<open>\<exists>c. y = c *\<^sub>C 1\<close> for y :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      apply (rule exI[where x=\<open>one_dim_iso y\<close>])
      by simp
    then obtain c where \<open>x = c *\<^sub>C 1\<close>
      apply transfer'
      by auto
    then show \<open>x \<in> cspan (set canonical_basis)\<close>
      by (auto intro!: complex_vector.span_base complex_vector.span_clauses
          simp: canonical_basis_trace_class_def)
  qed
qed
end

lemma from_trace_class_one_dim_iso[simp]: \<open>from_trace_class = one_dim_iso\<close>
proof (rule ext)
  fix x:: \<open>('a, 'b) trace_class\<close>
  have \<open>from_trace_class x = from_trace_class (one_dim_iso x *\<^sub>C 1)\<close>
    by simp
  also have \<open>\<dots> = one_dim_iso x *\<^sub>C from_trace_class 1\<close>
    using scaleC_trace_class.rep_eq by blast
  also have \<open>\<dots> = one_dim_iso x *\<^sub>C 1\<close>
    by (simp add: one_trace_class.rep_eq)
  also have \<open>\<dots> = one_dim_iso x\<close>
    by simp
  finally show \<open>from_trace_class x = one_dim_iso x\<close>
    by -
qed

lemma trace_tc_one_dim_iso[simp]: \<open>trace_tc = one_dim_iso\<close>
  by (simp add: trace_tc.rep_eq[abs_def])

lemma compose_tcr_id_left[simp]: \<open>compose_tcr id_cblinfun t = t\<close>
  by (auto intro!: from_trace_class_inject[THEN iffD1] simp: compose_tcr.rep_eq)

lemma compose_tcl_id_right[simp]: \<open>compose_tcl t id_cblinfun = t\<close>
  by (auto intro!: from_trace_class_inject[THEN iffD1] simp: compose_tcl.rep_eq)


lemma sandwich_tc_id_cblinfun[simp]: \<open>sandwich_tc id_cblinfun t = t\<close>
  by (simp add: from_trace_class_inverse sandwich_tc_def)

lemma bounded_clinear_sandwich_tc[bounded_clinear]: \<open>bounded_clinear (sandwich_tc e)\<close>
  using norm_sandwich_tc[of e]
  by (auto intro!: bounded_clinearI[where K=\<open>(norm e)\<^sup>2\<close>]
      simp: sandwich_tc_plus sandwich_tc_scaleC_right cross3_simps)

lemma trace_class_Proj: \<open>trace_class (Proj S) \<longleftrightarrow> finite_dim_ccsubspace S\<close>
proof -
  define C where \<open>C = some_onb_of S\<close>
  then obtain B where \<open>is_onb B\<close> and \<open>C \<subseteq> B\<close>
    using orthonormal_basis_exists some_onb_of_norm1 by blast
  have card_C: \<open>card C = cdim (space_as_set S)\<close>
    by (simp add: C_def some_onb_of_card)
  have S_C: \<open>S = ccspan C\<close>
    by (simp add: C_def)

  from \<open>is_onb B\<close>
  have \<open>trace_class (Proj S) \<longleftrightarrow> ((\<lambda>x. x \<bullet>\<^sub>C (abs_op (Proj S) *\<^sub>V x)) abs_summable_on B)\<close>
    by (rule trace_class_iff_summable)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>x. cmod (x \<bullet>\<^sub>C (Proj S *\<^sub>V x))) abs_summable_on B)\<close>
    by simp
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>x. 1::real) abs_summable_on C)\<close>
  proof (rule summable_on_cong_neutral)
    fix x :: 'a
    show \<open>norm 1 = 0\<close> if \<open>x \<in> C - B\<close>
      using that \<open>C \<subseteq> B\<close> by auto
    show \<open>norm (cmod (x \<bullet>\<^sub>C (Proj S *\<^sub>V x))) = norm (1::real)\<close> if \<open>x \<in> B \<inter> C\<close>
      apply (subst Proj_fixes_image)
      using C_def Int_absorb1 that \<open>is_onb B\<close>
      by (auto simp: is_onb_def cnorm_eq_1)
    show \<open>norm (cmod (x \<bullet>\<^sub>C (Proj S *\<^sub>V x))) = 0\<close> if \<open>x \<in> B - C\<close>
      apply (subst Proj_0_compl)
       apply (subst S_C)
       apply (rule mem_ortho_ccspanI)
      using that \<open>is_onb B\<close> \<open>C \<subseteq> B\<close>
      by (force simp: is_onb_def is_ortho_set_def)+
  qed
  also have \<open>\<dots> \<longleftrightarrow> finite C\<close>
    using infsum_diverge_constant[where A=C and c=\<open>1::real\<close>]
    by auto
  also have \<open>\<dots> \<longleftrightarrow> finite_dim_ccsubspace S\<close>
    by (metis C_def S_C ccspan_finite_dim some_onb_of_finite_dim)
  finally show ?thesis
    by -
qed

lemma not_trace_class_trace0: \<open>trace a = 0\<close> if \<open>\<not> trace_class a\<close>
  using that by (simp add: trace_def)


lemma trace_Proj: \<open>trace (Proj S) = cdim (space_as_set S)\<close>
proof (cases \<open>finite_dim_ccsubspace S\<close>)
  case True
  define C where \<open>C = some_onb_of S\<close>
  then obtain B where \<open>is_onb B\<close> and \<open>C \<subseteq> B\<close>
    using orthonormal_basis_exists some_onb_of_norm1 by blast
  have [simp]: \<open>finite C\<close>
    using C_def True some_onb_of_finite_dim by blast
  have card_C: \<open>card C = cdim (space_as_set S)\<close>
    by (simp add: C_def some_onb_of_card)
  have S_C: \<open>S = ccspan C\<close>
    by (simp add: C_def)

  from True have \<open>trace_class (Proj S)\<close>
    by (simp add: trace_class_Proj)
  with \<open>is_onb B\<close> have \<open>((\<lambda>e. e \<bullet>\<^sub>C (Proj S *\<^sub>V e)) has_sum trace (Proj S)) B\<close>
    by (rule trace_has_sum)
  then have \<open>((\<lambda>e. 1) has_sum trace (Proj S)) C\<close>
  proof (rule has_sum_cong_neutral[THEN iffD1, rotated -1])
    fix x :: 'a
    show \<open>1 = 0\<close> if \<open>x \<in> C - B\<close>
      using that \<open>C \<subseteq> B\<close> by auto
    show \<open>x \<bullet>\<^sub>C (Proj S *\<^sub>V x) = 1\<close> if \<open>x \<in> B \<inter> C\<close>
      apply (subst Proj_fixes_image)
      using C_def Int_absorb1 that \<open>is_onb B\<close>
      by (auto simp: is_onb_def cnorm_eq_1)
    show \<open>is_orthogonal x (Proj S *\<^sub>V x)\<close> if \<open>x \<in> B - C\<close>
      apply (subst Proj_0_compl)
       apply (subst S_C)
       apply (rule mem_ortho_ccspanI)
      using that \<open>is_onb B\<close> \<open>C \<subseteq> B\<close>
      by (force simp: is_onb_def is_ortho_set_def)+
  qed
  then have \<open>trace (Proj S) = card C\<close>
    using has_sum_constant[OF \<open>finite C\<close>, of 1]
    apply simp
    using has_sum_unique by blast
  also have \<open>\<dots> = cdim (space_as_set S)\<close>
    using card_C by presburger
  finally show ?thesis
    by -
next
  case False
  then have \<open>\<not> trace_class (Proj S)\<close>
    using trace_class_Proj by blast
  then have \<open>trace (Proj S) = 0\<close>
    by (rule not_trace_class_trace0)
  moreover from False have \<open>cdim (space_as_set S) = 0\<close>
    apply transfer
    by (simp add: cdim_infinite_0)
  ultimately show ?thesis
    by simp
qed

lemma trace_tc_pos: \<open>t \<ge> 0 \<Longrightarrow> trace_tc t \<ge> 0\<close>
  using trace_tc_mono by fastforce

lift_definition tc_apply :: \<open>('a::chilbert_space,'b::chilbert_space) trace_class \<Rightarrow> 'a \<Rightarrow> 'b\<close> is cblinfun_apply.

lemma bounded_cbilinear_tc_apply: \<open>bounded_cbilinear tc_apply\<close>
  apply (rule bounded_cbilinear.intro; transfer)
      apply (auto intro!: exI[of _ 1] cblinfun.add_left cblinfun.add_right cblinfun.scaleC_right)
  by (smt (verit, del_insts) mult_right_mono norm_cblinfun norm_ge_zero norm_leq_trace_norm)

lift_definition diagonal_operator_tc :: \<open>('a \<Rightarrow> complex) \<Rightarrow> ('a ell2, 'a ell2) trace_class\<close> is
  \<open>\<lambda>f. if f abs_summable_on UNIV then diagonal_operator f else 0\<close>
proof (rule CollectI)
  fix f :: \<open>'a \<Rightarrow> complex\<close>
  show \<open>trace_class (if f abs_summable_on UNIV then diagonal_operator f else 0)\<close>
  proof (cases \<open>f abs_summable_on UNIV\<close>)
    case True
    have bdd: \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
    proof (rule bdd_aboveI2)
      fix x
      have \<open>cmod (f x) = (\<Sum>\<^sub>\<infinity>x\<in>{x}. cmod (f x))\<close>
        by simp
      also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x. cmod (f x))\<close>
        apply (rule infsum_mono_neutral)
        by (auto intro!: True)
      finally show \<open>cmod (f x) \<le> (\<Sum>\<^sub>\<infinity>x. cmod (f x))\<close>
        by -
    qed
    have \<open>trace_class (diagonal_operator f)\<close>
      by (auto intro!: trace_classI[OF is_onb_ket] summable_on_reindex[THEN iffD2] True
          simp: abs_op_diagonal_operator o_def diagonal_operator_ket bdd)
    with True show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by simp
  qed
qed

lemma from_trace_class_diagonal_operator_tc:
  assumes \<open>f abs_summable_on UNIV\<close>
  shows \<open>from_trace_class (diagonal_operator_tc f) = diagonal_operator f\<close>
  apply (transfer fixing: f)
  using assms by simp

lemma tc_butterfly_scaleC_summable:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>f abs_summable_on A\<close>
  shows \<open>(\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) summable_on A\<close>
proof -
  define M where \<open>M = (\<Sum>\<^sub>\<infinity>x\<in>A. norm (f x))\<close>
  have \<open>(\<Sum>x\<in>F. cmod (f x) * norm (tc_butterfly (ket x) (ket x))) \<le> M\<close> if \<open>finite F\<close> and \<open>F \<subseteq> A\<close> for F
  proof -
    have \<open>(\<Sum>x\<in>F. norm (f x) * norm (tc_butterfly (ket x) (ket x))) = (\<Sum>x\<in>F. norm (f x))\<close>
      by (simp add: norm_tc_butterfly)
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>A. norm (f x))\<close>
      using assms finite_sum_le_infsum norm_ge_zero that(1) that(2) by blast
    also have \<open>\<dots> = M\<close>
      by (simp add: M_def)
    finally show ?thesis
      by -
  qed
  then have \<open>(\<lambda>x. norm (f x *\<^sub>C tc_butterfly (ket x) (ket x))) abs_summable_on A\<close>
    apply (intro nonneg_bdd_above_summable_on bdd_aboveI)
    by auto
  then show ?thesis
    by (auto intro: abs_summable_summable)
qed



lemma tc_butterfly_scaleC_has_sum:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>f abs_summable_on UNIV\<close>
  shows \<open>((\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) has_sum diagonal_operator_tc f) UNIV\<close>
proof -
  define D where \<open>D = (\<Sum>\<^sub>\<infinity>x. f x *\<^sub>C tc_butterfly (ket x) (ket x))\<close>
  have bdd_f: \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
    by (metis assms summable_on_bdd_above_real)

  have \<open>ket y \<bullet>\<^sub>C from_trace_class D (ket z) = ket y \<bullet>\<^sub>C from_trace_class (diagonal_operator_tc f) (ket z)\<close> for y z
  proof -
    have blin_tc_apply: \<open>bounded_linear (\<lambda>a. tc_apply a (ket z))\<close>
      by (intro bounded_clinear.bounded_linear bounded_cbilinear.bounded_clinear_left bounded_cbilinear_tc_apply)
    have summ: \<open>(\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) summable_on UNIV\<close>
      by (intro tc_butterfly_scaleC_summable assms)

    have \<open>((\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) has_sum D) UNIV\<close>
      by (simp add: D_def summ)
    with blin_tc_apply have \<open>((\<lambda>x. tc_apply (f x *\<^sub>C tc_butterfly (ket x) (ket x)) (ket z)) has_sum tc_apply D (ket z)) UNIV\<close>
      by (rule Infinite_Sum.has_sum_bounded_linear)
    then have \<open>((\<lambda>x. ket y \<bullet>\<^sub>C tc_apply (f x *\<^sub>C tc_butterfly (ket x) (ket x)) (ket z)) has_sum ket y \<bullet>\<^sub>C tc_apply D (ket z)) UNIV\<close>
      by (smt (verit, best) has_sum_cong has_sum_imp_summable has_sum_infsum infsumI infsum_cinner_left summable_on_cinner_left)
    then have \<open>((\<lambda>x. of_bool (x=y) * of_bool (y=z) * f y) has_sum ket y \<bullet>\<^sub>C tc_apply D (ket z)) UNIV\<close>
      apply (rule has_sum_cong[THEN iffD2, rotated])
      by (auto intro!: simp: tc_apply.rep_eq scaleC_trace_class.rep_eq tc_butterfly.rep_eq)
    then have \<open>((\<lambda>x. of_bool (y=z) * f y) has_sum ket y \<bullet>\<^sub>C tc_apply D (ket z)) {y}\<close>
      apply (rule has_sum_cong_neutral[THEN iffD2, rotated -1])
      by auto
    then have \<open>ket y \<bullet>\<^sub>C tc_apply D (ket z) = of_bool (y=z) * f y\<close>
      by simp
    also have \<open>\<dots> = ket y \<bullet>\<^sub>C from_trace_class (diagonal_operator_tc f) (ket z)\<close>
      by (simp add: diagonal_operator_tc.rep_eq assms diagonal_operator_ket bdd_f)
    finally show ?thesis
      by (simp add: tc_apply.rep_eq)
  qed
  then have \<open>from_trace_class D = from_trace_class (diagonal_operator_tc f)\<close>
    by (auto intro!: equal_ket cinner_ket_eqI)
  then have \<open>D = diagonal_operator_tc f\<close>
    by (simp add: from_trace_class_inject)
  with tc_butterfly_scaleC_summable[OF assms]
  show ?thesis
    using D_def by force
qed

lemma diagonal_operator_tc_invalid: \<open>\<not> f abs_summable_on UNIV \<Longrightarrow> diagonal_operator_tc f = 0\<close>
  apply (transfer fixing: f) by simp



lemma tc_butterfly_scaleC_infsum:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) = diagonal_operator_tc f\<close>
proof (cases \<open>f abs_summable_on UNIV\<close>)
  case True
  then show ?thesis
    using infsumI tc_butterfly_scaleC_has_sum by fastforce
next
  case False
  then have [simp]: \<open>diagonal_operator_tc f = 0\<close>
    apply (transfer fixing: f) by simp
  have \<open>\<not> (\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) summable_on UNIV\<close>
  proof (rule notI)
    assume \<open>(\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) summable_on UNIV\<close>
    then have \<open>(\<lambda>x. trace_tc (f x *\<^sub>C tc_butterfly (ket x) (ket x))) summable_on UNIV\<close>
      apply (rule summable_on_bounded_linear[rotated])
      by (simp add: bounded_clinear.bounded_linear)
    then have \<open>f summable_on UNIV\<close>
      apply (rule summable_on_cong[THEN iffD1, rotated])
      apply (transfer' fixing: f)
      by (simp add: trace_scaleC trace_butterfly)
    with False
    show False
      by (metis summable_on_iff_abs_summable_on_complex)
  qed
  then have [simp]: \<open>(\<Sum>\<^sub>\<infinity>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) = 0\<close>
    using infsum_not_exists by blast
  show ?thesis 
    by simp
qed

lemma from_trace_class_abs_summable: \<open>f abs_summable_on X \<Longrightarrow> (\<lambda>x. from_trace_class (f x)) abs_summable_on X\<close>
    apply (rule abs_summable_on_comparison_test[where g=\<open>f\<close>])
    by (simp_all add: norm_leq_trace_norm norm_trace_class.rep_eq)

lemma from_trace_class_summable: \<open>f summable_on X \<Longrightarrow> (\<lambda>x. from_trace_class (f x)) summable_on X\<close>
  apply (rule Infinite_Sum.summable_on_bounded_linear[where h=from_trace_class])
  by (simp_all add: bounded_clinear.bounded_linear bounded_clinear_from_trace_class)

lemma from_trace_class_infsum: 
  assumes \<open>f summable_on UNIV\<close>
  shows \<open>from_trace_class (\<Sum>\<^sub>\<infinity>x. f x) = (\<Sum>\<^sub>\<infinity>x. from_trace_class (f x))\<close>
  apply (rule infsum_bounded_linear_strong[symmetric])
  using assms
  by (auto intro!: bounded_clinear.bounded_linear bounded_clinear_from_trace_class from_trace_class_summable)

lemma cspan_trace_class:
  \<open>cspan (Collect trace_class :: ('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) set) = Collect trace_class\<close>
proof (intro Set.set_eqI iffI)
  fix x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  show \<open>x \<in> Collect trace_class \<Longrightarrow> x \<in> cspan (Collect trace_class)\<close>
    by (simp add: complex_vector.span_clauses)
  assume \<open>x \<in> cspan (Collect trace_class)\<close>
  then obtain F f where x_def: \<open>x = (\<Sum>a\<in>F. f a *\<^sub>C a)\<close> and \<open>F \<subseteq> Collect trace_class\<close>
    by (auto intro!: simp: complex_vector.span_explicit)
  then have \<open>trace_class x\<close>
    by (auto intro!: trace_class_sum trace_class_scaleC simp: x_def)
  then show \<open>x \<in> Collect trace_class \<close>
    by simp
qed

lemma monotone_convergence_tc:
  fixes f :: \<open>'b \<Rightarrow> ('a, 'a::chilbert_space) trace_class\<close>
  assumes bounded: \<open>\<forall>\<^sub>F x in F. trace_tc (f x) \<le> B\<close>
  assumes pos: \<open>\<forall>\<^sub>F x in F. f x \<ge> 0\<close>
  assumes increasing: \<open>increasing_filter (filtermap f F)\<close>
  shows \<open>\<exists>L. (f \<longlongrightarrow> L) F\<close>
proof -
  wlog \<open>F \<noteq> \<bottom>\<close>
    using negation by simp
  then have \<open>filtermap f F \<noteq> \<bottom>\<close>
    by (simp add: filtermap_bot_iff)
  have \<open>mono_on {t::('a,'a) trace_class. t \<ge> 0} trace_tc\<close>
    by (simp add: ord.mono_onI trace_tc_mono)
  with increasing
  have \<open>increasing_filter (filtermap (trace_tc o f) F)\<close>
    unfolding filtermap_compose
    apply (rule increasing_filtermap)
    by (auto intro!: pos simp: eventually_filtermap)
  then obtain l where l: \<open>((\<lambda>x. trace_tc (f x)) \<longlongrightarrow> l) F\<close>
    apply atomize_elim
    apply (rule monotone_convergence_complex)
    using bounded by (simp_all add: o_def)
  have \<open>cauchy_filter (filtermap f F)\<close>
  proof (rule cauchy_filter_metricI)
    fix e :: real assume \<open>e > 0\<close>
    define d where \<open>d = e/4\<close>
    have \<open>\<forall>\<^sub>F x in filtermap f F. dist (trace_tc x) l < d\<close>
      unfolding eventually_filtermap
      using l apply (rule tendstoD)
      using \<open>e > 0\<close> by (simp add: d_def)
    then obtain P1 where ev_P1: \<open>eventually P1 (filtermap f F)\<close> and P1: \<open>P1 x \<Longrightarrow> dist (trace_tc x) l < d\<close> for x
      by blast
    from increasing obtain P2 where ev_P2: \<open>eventually P2 (filtermap f F)\<close> and
      P2: \<open>P2 x \<Longrightarrow> (\<forall>\<^sub>F z in filtermap f F. z \<ge> x)\<close> for x
      using increasing_filter_def by blast
    define P where \<open>P x \<longleftrightarrow> P1 x \<and> P2 x\<close> for x
    with ev_P1 ev_P2 have ev_P: \<open>eventually P (filtermap f F)\<close>
      by (auto intro!: eventually_conj simp: P_def[abs_def])
    have \<open>dist x y < e\<close> if \<open>P x\<close> and \<open>P y\<close> for x y
    proof -
      from \<open>P x\<close> have \<open>\<forall>\<^sub>F z in filtermap f F. z \<ge> x\<close>
        by (simp add: P_def P2)
      moreover from \<open>P y\<close> have \<open>\<forall>\<^sub>F z in filtermap f F. z \<ge> y\<close>
        by (simp add: P_def P2)
      ultimately have \<open>\<forall>\<^sub>F z in filtermap f F. z \<ge> x \<and> z \<ge> y \<and> P1 z\<close>
        using ev_P1 by (auto intro!: eventually_conj)
      from eventually_happens'[OF \<open>filtermap f F \<noteq> \<bottom>\<close> this]
      obtain z where \<open>z \<ge> x\<close> and \<open>z \<ge> y\<close> and \<open>P1 z\<close>
        by auto
      have \<open>dist x y \<le> norm (z - x) + norm (z - y)\<close>
        by (metis (no_types, lifting) diff_add_cancel diff_add_eq_diff_diff_swap dist_trace_class_def norm_minus_commute norm_triangle_sub)
      also from \<open>x \<le> z\<close> \<open>y \<le> z\<close> have \<open>\<dots> = (trace_tc z - trace_tc x) + (trace_tc z - trace_tc y)\<close>
        by (metis (no_types, lifting) cross3_simps(16) diff_left_mono diff_self norm_tc_pos of_real_add trace_tc_plus)
      also from \<open>x \<le> z\<close> \<open>y \<le> z\<close> have \<open>\<dots> = norm (trace_tc z - trace_tc x) + norm (trace_tc z - trace_tc y)\<close>                  
        by (simp add: Extra_Ordered_Fields.complex_of_real_cmod trace_tc_mono abs_pos)
      also have \<open>\<dots> = dist (trace_tc z) (trace_tc x) + dist (trace_tc z) (trace_tc y)\<close>
        using dist_complex_def by presburger
      also have \<open>\<dots> \<le> (dist (trace_tc z) l + dist (trace_tc x) l) + (dist (trace_tc z) l + dist (trace_tc y) l)\<close> 
        apply (intro complex_of_real_mono add_mono)
        by (simp_all add: dist_triangle2)
      also from P1 \<open>P1 z\<close> that have \<open>\<dots> < 4 * d\<close>
        by (smt (verit, best) P_def complex_of_real_strict_mono_iff)
      also have \<open>\<dots> = e\<close>
        by (simp add: d_def)
      finally show ?thesis
        by simp
    qed
    with ev_P show \<open>\<exists>P. eventually P (filtermap f F) \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)\<close>
      by blast
  qed
  then have \<open>convergent_filter (filtermap f F)\<close>
  using cauchy_filter_convergent by fastforce
  then show \<open>\<exists>L. (f \<longlongrightarrow> L) F\<close>
    by (simp add: convergent_filter_iff filterlim_def)
qed

lemma nonneg_bdd_above_summable_on_tc:
  fixes f :: \<open>'a \<Rightarrow> ('c::chilbert_space, 'c) trace_class\<close>
  assumes pos: \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  assumes bdd: \<open>bdd_above (trace_tc ` sum f ` {F. F\<subseteq>A \<and> finite F})\<close>
  shows \<open>f summable_on A\<close>
proof -
  have pos': \<open>(\<Sum>x\<in>F. f x) \<ge> 0\<close> if \<open>finite F\<close> and \<open>F \<subseteq> A\<close> for F
    using that pos
    by (simp add: basic_trans_rules(31) sum_nonneg)
  from pos have incr: \<open>increasing_filter (filtermap (sum f) (finite_subsets_at_top A))\<close>
    by (auto intro!: increasing_filtermap[where X=\<open>{F. finite F \<and> F \<subseteq> A}\<close>] mono_onI sum_mono2)
  from bdd obtain B where B: \<open>trace_tc (sum f X) \<le> B\<close> if \<open>finite X\<close> and \<open>X \<subseteq> A\<close> for X
    apply atomize_elim
    by (auto simp: bdd_above_def)
  show ?thesis
    apply (simp add: summable_on_def has_sum_def)
    by (safe intro!: pos' incr monotone_convergence_tc[where B=B] B
        eventually_finite_subsets_at_top_weakI)
qed


lemma summable_Sigma_positive_tc:
  fixes f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('c, 'c::chilbert_space) trace_class\<close>
  assumes \<open>\<And>x. x\<in>X \<Longrightarrow> f x summable_on Y x\<close>
  assumes \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y) summable_on X\<close>
  assumes \<open>\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y x \<Longrightarrow> f x y \<ge> 0\<close>
  shows \<open>(\<lambda>(x, y). f x y) summable_on (SIGMA x:X. Y x)\<close>
proof -
  have \<open>trace_tc (\<Sum>(x,y)\<in>F. f x y) \<le> trace_tc (\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y)\<close> if \<open>F \<subseteq> Sigma X Y\<close> and \<open>finite F\<close> for F
  proof -
    define g where \<open>g x y = (if (x,y) \<in> Sigma X Y then f x y else 0)\<close> for x y
    have g_pos[iff]: \<open>g x y \<ge> 0\<close> for x y
      using assms by (auto intro!: simp: g_def)
    have g_summable: \<open>g x summable_on Y x\<close> for x
      by (metis assms(1) g_def mem_Sigma_iff summable_on_0 summable_on_cong)
    have sum_g_summable: \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>Y x. g x y) summable_on X\<close>
      by (metis (mono_tags, lifting) SigmaI g_def assms(2) infsum_cong summable_on_cong)
    have \<open>(\<Sum>(x,y)\<in>F. f x y) = (\<Sum>(x,y)\<in>F. g x y)\<close>
      by (smt (verit, ccfv_SIG) g_def split_cong subsetD sum.cong that(1))
    also have \<open>(\<Sum>(x,y)\<in>F. g x y) \<le> (\<Sum>(x,y)\<in>fst ` F \<times> snd ` F. g x y)\<close>
      using that assms apply (auto intro!: sum_mono2 assms simp: image_iff)
      by force+
    also have \<open>\<dots> = (\<Sum>x\<in>fst ` F. \<Sum>y\<in>snd ` F. g x y)\<close>
      by (metis (no_types, lifting) finite_imageI sum.Sigma sum.cong that(2))
    also have \<open>\<dots> = (\<Sum>x\<in>fst ` F. \<Sum>\<^sub>\<infinity>y\<in>snd ` F. g x y)\<close>
      by (metis finite_imageI infsum_finite that(2))
    also have \<open>\<dots> \<le> (\<Sum>x\<in>fst ` F. \<Sum>\<^sub>\<infinity>y\<in>Y x. g x y)\<close>
      apply (intro sum_mono infsum_mono_neutral_traceclass)
      using assms that
          apply (auto intro!: g_summable)
      by (simp add: g_def)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>fst ` F. \<Sum>\<^sub>\<infinity>y\<in>Y x. g x y)\<close>
      using that by (auto intro!: infsum_finite[symmetric] simp: )
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y x. g x y)\<close>
      apply (rule infsum_mono_neutral_traceclass)
      using that assms by (auto intro!: infsum_nonneg_traceclass sum_g_summable)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y)\<close>
      by (smt (verit, ccfv_threshold) g_def infsum_cong mem_Sigma_iff)
    finally show ?thesis
      using trace_tc_mono by blast
  qed
  then show ?thesis
    apply (rule_tac nonneg_bdd_above_summable_on_tc)
    by (auto intro!: assms bdd_aboveI2)
qed


lemma infsum_Sigma_positive_tc:
  fixes f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('c::chilbert_space, 'c) trace_class\<close>
  assumes \<open>\<And>x. x\<in>X \<Longrightarrow> f x summable_on Y x\<close>
  assumes \<open>\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y x \<Longrightarrow> f x y \<ge> 0\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y) = (\<Sum>\<^sub>\<infinity>(x,y)\<in>Sigma X Y. f x y)\<close>
proof (cases \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y) summable_on X\<close>)
  case True
  show ?thesis
    apply (rule infsum_Sigma'_banach)
    apply (rule summable_Sigma_positive_tc)
    using assms True by auto
next
  case False
  then have 1: \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y) = 0\<close>
    using infsum_not_exists by blast
  from False have \<open>\<not> (\<lambda>(x,y). f x y) summable_on Sigma X Y\<close>
    using summable_on_Sigma_banach by blast
  then have 2: \<open>(\<Sum>\<^sub>\<infinity>(x, y)\<in>Sigma X Y. f x y) = 0\<close>
    using infsum_not_exists by blast
  from 1 2 show ?thesis
    by simp
qed

lemma infsum_swap_positive_tc:
  fixes f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('c::chilbert_space, 'c) trace_class\<close>
  assumes \<open>\<And>x. x\<in>X \<Longrightarrow> f x summable_on Y\<close>
  assumes \<open>\<And>y. y\<in>Y \<Longrightarrow> (\<lambda>x. f x y) summable_on X\<close>
  assumes \<open>\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> f x y \<ge> 0\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y. f x y) = (\<Sum>\<^sub>\<infinity>y\<in>Y. \<Sum>\<^sub>\<infinity>x\<in>X. f x y)\<close>
proof -
  have \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y. f x y) = (\<Sum>\<^sub>\<infinity>(x,y)\<in>X\<times>Y. f x y)\<close>
    apply (rule infsum_Sigma_positive_tc)
    using assms by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(y,x)\<in>Y\<times>X. f x y)\<close>
    apply (subst product_swap[symmetric])
    by (simp add: infsum_reindex o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>y\<in>Y. \<Sum>\<^sub>\<infinity>x\<in>X. f x y)\<close>
    apply (rule infsum_Sigma_positive_tc[symmetric])
    using assms by auto
  finally show ?thesis
    by -
qed



lemma separating_density_ops:
  assumes \<open>B > 0\<close>
  shows \<open>separating_set clinear {t :: ('a::chilbert_space, 'a) trace_class. 0 \<le> t \<and> norm t \<le> B}\<close>
proof -
  define S where \<open>S = {t :: ('a, 'a) trace_class. 0 \<le> t \<and> norm t \<le> B}\<close>
  have \<open>cspan S = UNIV\<close>
  proof (intro Set.set_eqI iffI UNIV_I)
    fix t :: \<open>('a, 'a) trace_class\<close>
    from trace_class_decomp_4pos'
    obtain t1 t2 t3 t4 where t_decomp: \<open>t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4\<close>
      and pos: \<open>t1 \<ge> 0\<close> \<open>t2 \<ge> 0\<close> \<open>t3 \<ge> 0\<close> \<open>t4 \<ge> 0\<close>
      by fast
    have \<open>t' \<in> cspan S\<close> if \<open>t' \<ge> 0\<close> for t'
    proof -
      define t'' where \<open>t'' = (B / norm t') *\<^sub>R t'\<close>
      have \<open>t'' \<in> S\<close>
        using \<open>B > 0\<close>
        by (simp add: S_def that zero_le_scaleR_iff t''_def)
      have t'_t'': \<open>t' = (norm t' / B) *\<^sub>R t''\<close>
        using \<open>B > 0\<close> t''_def by auto
      show \<open>t' \<in> cspan S\<close>
        apply (subst t'_t'')
        using \<open>t'' \<in> S\<close>
        by (simp add: scaleR_scaleC complex_vector.span_clauses)
    qed
    with pos have \<open>t1 \<in> cspan S\<close> and \<open>t2 \<in> cspan S\<close> and \<open>t3 \<in> cspan S\<close> and \<open>t4 \<in> cspan S\<close>
      by auto
    then show \<open>t \<in> cspan S\<close>
      by (auto intro!: complex_vector.span_diff complex_vector.span_add complex_vector.span_scale
          intro: complex_vector.span_base simp: t_decomp)
  qed
  then show \<open>separating_set clinear S\<close>
    by (rule separating_set_clinear_cspan)
qed

lemma summable_abs_summable_tc:
  fixes f :: \<open>'a \<Rightarrow> ('b::chilbert_space,'b) trace_class\<close>
  assumes \<open>f summable_on X\<close>
  assumes \<open>\<And>x. x\<in>X \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>f abs_summable_on X\<close>
proof -
  from assms(1) have \<open>(\<lambda>x. trace_tc (f x)) summable_on X\<close>
    apply (rule summable_on_bounded_linear[rotated])
    by (simp add: bounded_clinear.bounded_linear)
  then have \<open>(\<lambda>x. Re (trace_tc (f x))) summable_on X\<close>
    using summable_on_Re by blast
  then show \<open>(\<lambda>x. norm (f x)) summable_on X\<close>
    by (metis (mono_tags, lifting) assms(2) norm_tc_pos_Re summable_on_cong)
qed




subsection \<open>More Hilbert-Schmidt\<close>

lemma trace_class_hilbert_schmidt: \<open>hilbert_schmidt a\<close> if \<open>trace_class a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  by (auto intro!: trace_class_comp_right that simp: hilbert_schmidt_def)

lemma finite_rank_hilbert_schmidt: \<open>hilbert_schmidt a\<close> if \<open>finite_rank a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  using finite_rank_comp_right finite_rank_trace_class hilbert_schmidtI that by blast

lemma hilbert_schmidt_compact: \<open>compact_op a\<close> if \<open>hilbert_schmidt a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  \<comment> \<open>\<^cite>\<open>conway00operator\<close>, Corollary 18.7.
      (Only the second part. The first part is stated inside this proof though.)\<close>
proof -
  have \<open>\<exists>b. finite_rank b \<and> hilbert_schmidt_norm (b - a) < \<epsilon>\<close> if \<open>\<epsilon> > 0\<close> for \<epsilon>
  proof -
    have \<open>\<epsilon>\<^sup>2 > 0\<close>
      using that by force
    obtain B :: \<open>'a set\<close> where \<open>is_onb B\<close>
      using is_onb_some_chilbert_basis by blast
    with \<open>hilbert_schmidt a\<close> have a_sum_B: \<open>(\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) summable_on B\<close>
      by (auto intro!: summable_hilbert_schmidt_norm_square)
    then have \<open>((\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) has_sum (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a *\<^sub>V x))\<^sup>2)) B\<close>
      using has_sum_infsum by blast
    from tendsto_iff[THEN iffD1, rule_format, OF this[unfolded has_sum_def] \<open>\<epsilon>\<^sup>2 > 0\<close>]
    obtain F where [simp]: \<open>finite F\<close> and \<open>F \<subseteq> B\<close>
      and Fbound: \<open>dist (\<Sum>x\<in>F. (norm (a *\<^sub>V x))\<^sup>2) (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a *\<^sub>V x))\<^sup>2) < \<epsilon>\<^sup>2\<close>
      apply atomize_elim
      by (auto intro!: simp: eventually_finite_subsets_at_top)
    define p b where \<open>p = (\<Sum>x\<in>F. selfbutter x)\<close> and \<open>b = a o\<^sub>C\<^sub>L p\<close>
    have [simp]: \<open>p x = x\<close> if \<open>x \<in> F\<close> for x
      apply (simp add: p_def cblinfun.sum_left)
      apply (subst sum_single[where i=x])
      using \<open>F \<subseteq> B\<close> that \<open>is_onb B\<close>
      by (auto intro!: simp:  cnorm_eq_1 is_onb_def is_ortho_set_def)
    have [simp]: \<open>p x = 0\<close> if \<open>x \<in> B - F\<close> for x
      using \<open>F \<subseteq> B\<close> that \<open>is_onb B\<close>
      apply (auto intro!: sum.neutral simp add: p_def cblinfun.sum_left is_onb_def is_ortho_set_def)
      by auto
    have \<open>finite_rank p\<close>
      by (simp add: finite_rank_sum p_def)
    then have \<open>finite_rank b\<close>
      by (simp add: b_def finite_rank_comp_right)
    with \<open>hilbert_schmidt a\<close> have \<open>hilbert_schmidt (b - a)\<close>
      by (auto intro!: hilbert_schmidt_minus intro: finite_rank_hilbert_schmidt)
    then have \<open>(hilbert_schmidt_norm (b - a))\<^sup>2 = (\<Sum>\<^sub>\<infinity>x\<in>B. (norm ((b - a) *\<^sub>V x))\<^sup>2)\<close>
      by (simp add: infsum_hilbert_schmidt_norm_square \<open>is_onb B\<close>)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>B-F. (norm (a *\<^sub>V x))\<^sup>2)\<close>
      by (auto intro!: infsum_cong_neutral
          simp: b_def cblinfun.diff_left)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a *\<^sub>V x))\<^sup>2) - (\<Sum>x\<in>F. (norm (a *\<^sub>V x))\<^sup>2)\<close>
      apply (subst infsum_Diff)
      using \<open>F \<subseteq> B\<close> a_sum_B by auto
    also have \<open>\<dots> < \<epsilon>\<^sup>2\<close>
      using Fbound
      by (simp add: dist_norm)
    finally show ?thesis
      using \<open>finite_rank b\<close>
      using power_less_imp_less_base that by fastforce
  qed
  then have \<open>\<exists>b. finite_rank b \<and> dist b a < \<epsilon>\<close> if \<open>\<epsilon> > 0\<close> for \<epsilon>
    apply (rule ex_mono[rule_format, rotated])
     apply (auto intro!: that simp: dist_norm)
    using hilbert_schmidt_minus \<open>hilbert_schmidt a\<close> finite_rank_hilbert_schmidt hilbert_schmidt_norm_geq_norm
    by fastforce
  then show ?thesis
    by (simp add: compact_op_finite_rank closure_approachable)
qed

lemma trace_class_compact: \<open>compact_op a\<close> if \<open>trace_class a\<close> 
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  by (simp add: hilbert_schmidt_compact that trace_class_hilbert_schmidt)



subsection \<open>Spectral Theorem\<close>

text \<open>The spectral theorem for trace class operators.
A corollary of the one for compact operators (\<^theory>\<open>Hilbert_Space_Tensor_Product.Spectral_Theorem\<close>) but not an immediate one.\<close>

lift_definition spectral_dec_proj_tc :: \<open>('a::chilbert_space, 'a) trace_class \<Rightarrow> nat \<Rightarrow> ('a, 'a) trace_class\<close> is
  spectral_dec_proj
  using finite_rank_trace_class spectral_dec_proj_finite_rank trace_class_compact by blast

lift_definition spectral_dec_val_tc :: \<open>('a::chilbert_space, 'a) trace_class \<Rightarrow> nat \<Rightarrow> complex\<close> is
  spectral_dec_val.

lemma spectral_dec_proj_tc_finite_rank: 
  assumes \<open>adj_tc a = a\<close>
  shows \<open>finite_rank_tc (spectral_dec_proj_tc a n)\<close>
  using assms apply transfer
  by (simp add: spectral_dec_proj_finite_rank trace_class_compact)

lemma spectral_dec_summable_tc:
  assumes \<open>selfadjoint_tc a\<close>
  shows \<open>(\<lambda>n. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n)  abs_summable_on  UNIV\<close>
proof (intro nonneg_bounded_partial_sums_imp_summable_on norm_ge_zero eventually_finite_subsets_at_top_weakI)
  define a' where \<open>a' = from_trace_class a\<close>
  then have [transfer_rule]: \<open>cr_trace_class a' a\<close>
    by (simp add: cr_trace_class_def)

  have \<open>compact_op a'\<close>
    by (auto intro!: trace_class_compact simp: a'_def)
  have \<open>selfadjoint a'\<close>
    using a'_def assms selfadjoint_tc.rep_eq by blast 
  fix F :: \<open>nat set\<close> assume \<open>finite F\<close>
  define R where \<open>R = (\<Squnion>n\<in>F. spectral_dec_space a' n)\<close>
  have \<open>(\<Sum>x\<in>F. norm (spectral_dec_val_tc a x *\<^sub>C spectral_dec_proj_tc a x))
        = norm (\<Sum>x\<in>F. spectral_dec_val_tc a x *\<^sub>C spectral_dec_proj_tc a x)\<close>
  proof (rule norm_tc_sum_exchange[symmetric]; transfer; rename_tac n m F)
    fix n m :: nat assume (* \<open>n \<in> F\<close> and \<open>m \<in> F\<close> and *) \<open>n \<noteq> m\<close>
    then have *: \<open>Proj (spectral_dec_space a' n) o\<^sub>C\<^sub>L Proj (spectral_dec_space a' m) = 0\<close> if \<open>spectral_dec_val a' n \<noteq> 0\<close> and \<open>spectral_dec_val a' m \<noteq> 0\<close>
      by (auto intro!: orthogonal_projectors_orthogonal_spaces[THEN iffD1] spectral_dec_space_orthogonal \<open>compact_op a'\<close> \<open>selfadjoint a'\<close>simp: )
    show \<open>(spectral_dec_val a' n *\<^sub>C spectral_dec_proj a' n)* o\<^sub>C\<^sub>L spectral_dec_val a' m *\<^sub>C spectral_dec_proj a' m = 0\<close>
      by (auto intro!: * simp: spectral_dec_proj_def adj_Proj)
    show \<open>spectral_dec_val a' n *\<^sub>C spectral_dec_proj a' n o\<^sub>C\<^sub>L (spectral_dec_val a' m *\<^sub>C spectral_dec_proj a' m)* = 0\<close>
      by (auto intro!: * simp: spectral_dec_proj_def adj_Proj)
  qed
  also have \<open>\<dots> = trace_norm (\<Sum>x\<in>F. spectral_dec_val a' x *\<^sub>C spectral_dec_proj a' x)\<close>
    by (metis (no_types, lifting) a'_def spectral_dec_proj_tc.rep_eq spectral_dec_val_tc.rep_eq from_trace_class_sum norm_trace_class.rep_eq scaleC_trace_class.rep_eq sum.cong) 
  also have \<open>\<dots> = trace_norm (\<Sum>x. if x\<in>F then spectral_dec_val a' x *\<^sub>C spectral_dec_proj a' x else 0)\<close>
    by (simp add: \<open>finite F\<close> suminf_If_finite_set) 
  also have \<open>\<dots> = trace_norm (\<Sum>x. (spectral_dec_val a' x *\<^sub>C spectral_dec_proj a' x) o\<^sub>C\<^sub>L Proj R)\<close>
  proof -
    have \<open>spectral_dec_proj a' n = spectral_dec_proj a' n o\<^sub>C\<^sub>L Proj R\<close> if \<open>n \<in> F\<close> for n
      by (auto intro!: Proj_o_Proj_subspace_left[symmetric] SUP_upper that simp: spectral_dec_proj_def R_def)
    moreover have \<open>spectral_dec_proj a' n o\<^sub>C\<^sub>L Proj R = 0\<close> if \<open>n \<notin> F\<close> for n
      using that
      by (auto intro!: orthogonal_spaces_SUP_right spectral_dec_space_orthogonal \<open>compact_op a'\<close> \<open>selfadjoint a'\<close>
          simp: spectral_dec_proj_def R_def
          simp flip: orthogonal_projectors_orthogonal_spaces)
    ultimately show ?thesis
      by (auto intro!: arg_cong[where f=trace_norm] suminf_cong)
  qed
  also have \<open>\<dots> = trace_norm ((\<Sum>x. spectral_dec_val a' x *\<^sub>C spectral_dec_proj a' x) o\<^sub>C\<^sub>L Proj R)\<close>
    apply (intro arg_cong[where f=trace_norm] bounded_linear.suminf[symmetric] 
        bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_left sums_summable)
    using \<open>compact_op a'\<close> \<open>selfadjoint a'\<close> spectral_dec_sums by blast
  also have \<open>\<dots> = trace_norm (a' o\<^sub>C\<^sub>L Proj R)\<close>
    using spectral_dec_sums[OF \<open>compact_op a'\<close> \<open>selfadjoint a'\<close>] sums_unique by fastforce 
  also have \<open>\<dots> \<le> trace_norm a' * norm (Proj R)\<close>
    by (auto intro!: trace_norm_comp_left simp: a'_def)
  also have \<open>\<dots> \<le> trace_norm a'\<close>
    by (simp add: mult_left_le norm_Proj_leq1) 
  finally show \<open>(\<Sum>x\<in>F. norm (spectral_dec_val_tc a x *\<^sub>C spectral_dec_proj_tc a x)) \<le> trace_norm a'\<close>
    by -
qed


lemma spectral_dec_has_sum_tc:
  assumes \<open>selfadjoint_tc a\<close>
  shows \<open>((\<lambda>n. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n)  has_sum  a) UNIV\<close>
proof -
  define a' b b' where \<open>a' = from_trace_class a\<close>
    and \<open>b = (\<Sum>\<^sub>\<infinity>n. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n)\<close> and \<open>b' = from_trace_class b\<close>
  have [simp]: \<open>compact_op a'\<close>
    by (auto intro!: trace_class_compact simp: a'_def)
  have [simp]: \<open>selfadjoint a'\<close>
    using a'_def assms selfadjoint_tc.rep_eq by blast 
  have [simp]: \<open>trace_class b'\<close>
    by (simp add: b'_def) 
  from spectral_dec_summable_tc[OF assms]
  have has_sum_b: \<open>((\<lambda>n. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n)  has_sum  b) UNIV\<close>
    by (metis abs_summable_summable b_def summable_iff_has_sum_infsum) 
  then have \<open>((\<lambda>F. \<Sum>n\<in>F. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n) \<longlongrightarrow> b) (finite_subsets_at_top UNIV)\<close>
    by (simp add: has_sum_def)
  then have \<open>((\<lambda>F. norm ((\<Sum>n\<in>F. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n) - b)) \<longlongrightarrow> 0) (finite_subsets_at_top UNIV)\<close>
    using LIM_zero tendsto_norm_zero by blast 
  then have \<open>((\<lambda>F. norm ((\<Sum>n\<in>F. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n) - b)) \<longlongrightarrow> 0) (filtermap (\<lambda>n. {..<n}) sequentially)\<close>
    by (meson filterlim_compose filterlim_filtermap filterlim_lessThan_at_top) 
  then have \<open>((\<lambda>m. norm ((\<Sum>n\<in>{..<m}. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n) - b)) \<longlongrightarrow> 0) sequentially\<close>
    by (simp add: filterlim_filtermap) 
  then have \<open>((\<lambda>m. trace_norm ((\<Sum>n\<in>{..<m}. spectral_dec_val a' n *\<^sub>C spectral_dec_proj a' n) - b')) \<longlongrightarrow> 0) sequentially\<close>
    unfolding a'_def b'_def
    by transfer
  then have \<open>((\<lambda>m. norm ((\<Sum>n\<in>{..<m}. spectral_dec_val a' n *\<^sub>C spectral_dec_proj a' n) - b')) \<longlongrightarrow> 0) sequentially\<close>
    apply (rule tendsto_0_le[where K=1])
    by (auto intro!: eventually_sequentiallyI norm_leq_trace_norm trace_class_minus
        trace_class_sum trace_class_scaleC spectral_dec_proj_finite_rank
        intro: finite_rank_trace_class)
  then have \<open>(\<lambda>n. spectral_dec_val a' n *\<^sub>C spectral_dec_proj a' n) sums b'\<close>
    using LIM_zero_cancel sums_def tendsto_norm_zero_iff by blast 
  moreover have \<open>(\<lambda>n. spectral_dec_val a' n *\<^sub>C spectral_dec_proj a' n) sums a'\<close>
    using \<open>compact_op a'\<close> \<open>selfadjoint a'\<close> by (rule spectral_dec_sums)
  ultimately have \<open>a = b\<close>
    using a'_def b'_def from_trace_class_inject sums_unique2 by blast
  with has_sum_b show ?thesis
    by simp
qed


lemma spectral_dec_sums_tc:
  assumes \<open>selfadjoint_tc a\<close>
  shows \<open>(\<lambda>n. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n)  sums  a\<close>
  using assms has_sum_imp_sums spectral_dec_has_sum_tc by blast 

lift_definition spectral_dec_vecs_tc :: \<open>('a,'a) trace_class \<Rightarrow> 'a::chilbert_space set\<close> is
  spectral_dec_vecs.

lemma compact_from_trace_class[iff]: \<open>compact_op (from_trace_class t)\<close>
  by (auto intro!: simp: trace_class_compact)

lemma sum_some_onb_of_tc_butterfly:
  assumes \<open>finite_dim_ccsubspace S\<close>
  shows \<open>(\<Sum>x\<in>some_onb_of S. tc_butterfly x x) = Abs_trace_class (Proj S)\<close>
  by (metis (mono_tags, lifting) assms from_trace_class_inverse from_trace_class_sum sum.cong sum_some_onb_of_butterfly tc_butterfly.rep_eq)

lemma butterfly_spectral_dec_vec_tc_has_sum:
  assumes \<open>t \<ge> 0\<close>
  shows \<open>((\<lambda>v. tc_butterfly v v) has_sum t) (spectral_dec_vecs_tc t)\<close>
proof -
  define t' where \<open>t' = from_trace_class t\<close>
  note power2_csqrt[unfolded power2_eq_square, simp]
  note Reals_cnj_iff[simp]
  have [simp]: \<open>compact_op t'\<close>
    by (simp add: t'_def)
  from assms have \<open>selfadjoint_tc t\<close>
    apply transfer
    apply (rule comparable_hermitean[of 0])
    by simp_all
  have spectral_real[simp]: \<open>spectral_dec_val t' n \<in> \<real>\<close> for n
    apply (rule spectral_dec_val_real)
    using \<open>selfadjoint_tc t\<close> by (auto intro!: trace_class_compact simp: selfadjoint_tc.rep_eq t'_def)

  have *: \<open>((\<lambda>(n,v). tc_butterfly v v) has_sum t) (SIGMA n:UNIV. (*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n))\<close>
  proof (rule has_sum_SigmaI[where g=\<open>\<lambda>n. spectral_dec_val t' n *\<^sub>C spectral_dec_proj_tc t n\<close>])
    have \<open>spectral_dec_val t' n \<ge> 0\<close> for n
      by (simp add: assms from_trace_class_pos spectral_dec_val_nonneg t'_def)
    then have [simp]: \<open>cnj (csqrt (spectral_dec_val t' n)) * csqrt (spectral_dec_val t' n) = spectral_dec_val t' n\<close> for n
      apply (auto simp add: csqrt_of_real_nonneg less_eq_complex_def)
      by (metis of_real_Re of_real_mult spectral_real sqrt_sqrt)
    have sum: \<open>(\<Sum>y\<in>(\<lambda>x. csqrt (spectral_dec_val t' n) *\<^sub>C x) ` some_onb_of (spectral_dec_space t' n). tc_butterfly y y) = spectral_dec_val t' n *\<^sub>C spectral_dec_proj_tc t n\<close> for n
    proof (cases \<open>spectral_dec_val t' n = 0\<close>)
      case True
      then show ?thesis
        by (metis (mono_tags, lifting) csqrt_0 imageE scaleC_eq_0_iff sum.neutral tc_butterfly_scaleC_left)
    next
      case False
      then have \<open>inj_on (\<lambda>x. csqrt (spectral_dec_val t' n) *\<^sub>C x) X\<close> for X :: \<open>'a set\<close>
        by (meson csqrt_eq_0 inj_scaleC)
      then show ?thesis 
        by (simp add: sum.reindex False spectral_dec_space_finite_dim sum_some_onb_of_tc_butterfly
            spectral_dec_proj_def spectral_dec_proj_tc_def flip: scaleC_sum_right t'_def)
    qed
    then show \<open>((\<lambda>y. case (n, y) of (n, v) \<Rightarrow> tc_butterfly v v) has_sum spectral_dec_val t' n *\<^sub>C spectral_dec_proj_tc t n)
          ((*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n))\<close> for n
      by (auto intro!: has_sum_finiteI finite_imageI some_onb_of_finite_dim spectral_dec_space_finite_dim simp: t'_def)
    show \<open>((\<lambda>n. spectral_dec_val t' n *\<^sub>C spectral_dec_proj_tc t n) has_sum t) UNIV\<close>
      by (auto intro!: spectral_dec_has_sum_tc \<open>selfadjoint_tc t\<close> simp: t'_def simp flip: spectral_dec_val_tc.rep_eq)
    show \<open>(\<lambda>(n, v). tc_butterfly v v) summable_on (SIGMA n:UNIV. (*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n))\<close>
    proof -
      have inj: \<open>inj_on ((*\<^sub>C) (csqrt (spectral_dec_val t' n))) (some_onb_of (spectral_dec_space t' n))\<close> for n
      proof (cases \<open>spectral_dec_val t' n = 0\<close>)
        case True
        then have \<open>spectral_dec_space t' n = 0\<close>
          using spectral_dec_space_0 by blast
        then have \<open>some_onb_of (spectral_dec_space t' n) = {}\<close>
          using some_onb_of_0 by auto
        then show ?thesis
          by simp
      next
        case False
        then show ?thesis
          by (auto intro!: inj_scaleC)
      qed
      have 1: \<open>(\<lambda>x. tc_butterfly x x) abs_summable_on (\<lambda>xa. csqrt (spectral_dec_val t' n) *\<^sub>C xa) ` some_onb_of (spectral_dec_space t' n)\<close> for n
        by (auto intro!: summable_on_finite some_onb_of_finite_dim spectral_dec_space_finite_dim simp: t'_def)
      (* have \<open>(\<Sum>\<^sub>\<infinity>x\<in>some_onb_of (spectral_dec_space t' h). norm (tc_butterfly x x)) = spectral_dec_proj t' h\<close> for h *)
      have \<open>(\<lambda>n. cmod (spectral_dec_val t' n) * (\<Sum>\<^sub>\<infinity>h\<in>some_onb_of (spectral_dec_space t' n). norm (tc_butterfly h h))) abs_summable_on UNIV\<close>
      proof -
        have *: \<open>(\<Sum>\<^sub>\<infinity>h\<in>some_onb_of (spectral_dec_space t' n). norm (tc_butterfly h h)) = norm (spectral_dec_proj_tc t n)\<close> for n
        proof -
          have \<open>(\<Sum>\<^sub>\<infinity>h\<in>some_onb_of (spectral_dec_space t' n). norm (tc_butterfly h h))
              = (\<Sum>\<^sub>\<infinity>h\<in>some_onb_of (spectral_dec_space t' n). 1)\<close>
            by (simp add: infsum_cong norm_tc_butterfly some_onb_of_norm1)
          also have \<open>\<dots> = card (some_onb_of (spectral_dec_space t' n))\<close>
            by simp
          also have \<open>\<dots> = cdim (space_as_set (spectral_dec_space t' n))\<close>
            by (simp add: some_onb_of_card)
          also have \<open>\<dots> = norm (spectral_dec_proj_tc t n)\<close>
            unfolding t'_def 
            apply transfer
            by (metis of_real_eq_iff of_real_of_nat_eq spectral_dec_proj_def spectral_dec_proj_pos
                trace_Proj trace_norm_pos)
          finally show ?thesis
            by -
        qed
        show ?thesis
          apply (simp add: * )
          by (metis (no_types, lifting) \<open>selfadjoint_tc t\<close> norm_scaleC spectral_dec_summable_tc
              spectral_dec_val_tc.rep_eq summable_on_cong t'_def)
      qed
      then have 2: \<open>(\<lambda>n. \<Sum>\<^sub>\<infinity>v\<in>(*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n).
            norm (tc_butterfly v v)) abs_summable_on UNIV\<close>
        apply (subst infsum_reindex)
        by (auto intro!: inj simp: o_def infsum_cmult_right' norm_mult (* inj_on_def *) simp del: real_norm_def)
      show ?thesis
        apply (rule abs_summable_summable)
        apply (rule abs_summable_on_Sigma_iff[THEN iffD2])
        using 1 2 by auto
    qed
  qed
  have \<open>((\<lambda>v. tc_butterfly v v) has_sum t) (\<Union>n. (*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n))\<close>
  proof -
    have **: \<open>(\<Union>n. (*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n)) =
              snd ` (SIGMA n:UNIV. (*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n))\<close>
      by force
    have inj: \<open>inj_on snd (SIGMA n:UNIV. (\<lambda>x. csqrt (spectral_dec_val t' n) *\<^sub>C x) ` some_onb_of (spectral_dec_space t' n))\<close>
    proof (rule inj_onI)
      fix nh assume nh: \<open>nh \<in> (SIGMA n:UNIV. (\<lambda>x. csqrt (spectral_dec_val t' n) *\<^sub>C x) ` some_onb_of (spectral_dec_space t' n))\<close>
      fix mg assume mg: \<open>mg \<in> (SIGMA m:UNIV. (\<lambda>x. csqrt (spectral_dec_val t' m) *\<^sub>C x) ` some_onb_of (spectral_dec_space t' m))\<close>
      assume \<open>snd nh = snd mg\<close>
      from nh obtain n h where nh': \<open>nh = (n, csqrt (spectral_dec_val t' n) *\<^sub>C h)\<close> and h: \<open>h \<in> some_onb_of (spectral_dec_space t' n)\<close>
        by blast
      from mg obtain m g where mg': \<open>mg = (m, csqrt (spectral_dec_val t' m) *\<^sub>C g)\<close> and g: \<open>g \<in> some_onb_of (spectral_dec_space t' m)\<close>
        by blast
      have \<open>n = m\<close>
      proof (rule ccontr)
        assume [simp]: \<open>n \<noteq> m\<close>
        from h have val_not_0: \<open>spectral_dec_val t' n \<noteq> 0\<close>
          using some_onb_of_0 spectral_dec_space_0 by fastforce
        from \<open>snd nh = snd mg\<close> nh' mg' have eq: \<open>csqrt (spectral_dec_val t' n) *\<^sub>C h = csqrt (spectral_dec_val t' m) *\<^sub>C g\<close>
          by simp
        from \<open>n \<noteq> m\<close> have \<open>orthogonal_spaces (spectral_dec_space t' n) (spectral_dec_space t' m)\<close>
          apply (rule spectral_dec_space_orthogonal[rotated -1])
          using \<open>selfadjoint_tc t\<close> by (auto intro!: trace_class_compact simp: t'_def selfadjoint_tc.rep_eq)
        with h g have \<open>is_orthogonal h g\<close>
          using orthogonal_spaces_ccspan by fastforce
        then have \<open>is_orthogonal (csqrt (spectral_dec_val t' n) *\<^sub>C h) (csqrt (spectral_dec_val t' m) *\<^sub>C g)\<close>
          by force
        with eq have val_h_0: \<open>csqrt (spectral_dec_val t' n) *\<^sub>C h = 0\<close>
          by simp
        with val_not_0 have \<open>h = 0\<close>
          by fastforce
        with h show False
          using some_onb_of_is_ortho_set
          by (auto simp: is_ortho_set_def)
      qed
      with \<open>snd nh = snd mg\<close> nh' mg' show \<open>nh = mg\<close>
        by simp
    qed
    from * show ?thesis
      apply (subst ** )
      apply (rule has_sum_reindex[THEN iffD2, rotated])
      by (auto intro!: inj simp: o_def case_prod_unfold)
  qed
  then show ?thesis
    by (simp add: spectral_dec_vecs_tc.rep_eq spectral_dec_vecs_def flip: t'_def)
qed


lemma spectral_dec_vec_tc_norm_summable:
  assumes \<open>t \<ge> 0\<close>
  shows \<open>(\<lambda>v. (norm v)\<^sup>2) summable_on (spectral_dec_vecs_tc t)\<close>
proof -
  from butterfly_spectral_dec_vec_tc_has_sum[OF assms]
  have \<open>(\<lambda>v. tc_butterfly v v) summable_on (spectral_dec_vecs_tc t)\<close>
    using has_sum_imp_summable by blast
  then have \<open>(\<lambda>v. trace_tc (tc_butterfly v v)) summable_on (spectral_dec_vecs_tc t)\<close>
    apply (rule summable_on_bounded_linear[rotated])
    by (simp add: bounded_clinear.bounded_linear)
  moreover have *: \<open>trace_tc (tc_butterfly v v) = of_real ((norm v)\<^sup>2)\<close> for v :: 'a
    by (metis norm_tc_butterfly norm_tc_pos power2_eq_square tc_butterfly_pos)
  ultimately have \<open>(\<lambda>v. complex_of_real ((norm v)\<^sup>2)) summable_on (spectral_dec_vecs_tc t)\<close>
    by simp
  then show ?thesis
    by (smt (verit, ccfv_SIG) norm_of_real summable_on_cong summable_on_iff_abs_summable_on_complex zero_le_power2)
qed



subsection \<open>More Trace-Class\<close>




lemma finite_rank_tc_dense_aux: \<open>closure (Collect finite_rank_tc :: ('a::chilbert_space, 'a) trace_class set) = UNIV\<close>
proof (intro order_top_class.top_le subsetI)
  fix a :: \<open>('a,'a) trace_class\<close>
  wlog selfadj: \<open>selfadjoint_tc a\<close> goal \<open>a \<in> closure (Collect finite_rank_tc)\<close> generalizing a
  proof -
    define b c where \<open>b = a + adj_tc a\<close> and \<open>c = \<i> *\<^sub>C (a - adj_tc a)\<close>
    have \<open>adj_tc b = b\<close>
      unfolding b_def
      apply transfer
      by (simp add: adj_plus)
    have \<open>adj_tc c = c\<close>
      unfolding c_def
      apply transfer
      apply (simp add: adj_minus)
      by (metis minus_diff_eq scaleC_right.minus)
    have abc: \<open>a = (1/2) *\<^sub>C b + (-\<i>/2) *\<^sub>C c\<close>
      apply (simp add: b_def c_def)
      by (metis (no_types, lifting) cross3_simps(8) diff_add_cancel group_cancel.add2 scaleC_add_right scaleC_half_double)
    have \<open>b \<in> closure (Collect finite_rank_tc)\<close> and \<open>c \<in> closure (Collect finite_rank_tc)\<close>
      using \<open>adj_tc b = b\<close> \<open>adj_tc c = c\<close> hypothesis selfadjoint_tc_def' by auto
    with abc have \<open>a \<in> cspan (closure (Collect finite_rank_tc))\<close>
      by (metis complex_vector.span_add complex_vector.span_clauses(1) complex_vector.span_clauses(4))
    also have \<open>\<dots> \<subseteq> closure (cspan (Collect finite_rank_tc))\<close>
      by (simp add: closure_mono complex_vector.span_minimal complex_vector.span_superset)
    also have \<open>\<dots> = closure (Collect finite_rank_tc)\<close>
      by (metis Set.basic_monos(1) complex_vector.span_minimal complex_vector.span_superset csubspace_finite_rank_tc subset_antisym)
    finally show ?thesis
      by -
  qed
  then have \<open>(\<lambda>n. spectral_dec_val_tc a n *\<^sub>C spectral_dec_proj_tc a n)  sums  a\<close>
    by (simp add: spectral_dec_sums_tc)
  moreover from selfadj 
  have \<open>finite_rank_tc (\<Sum>i<n. spectral_dec_val_tc a i *\<^sub>C spectral_dec_proj_tc a i)\<close> for n
    apply (induction n)
     by (auto intro!: finite_rank_tc_plus spectral_dec_proj_tc_finite_rank finite_rank_tc_scale
        simp: selfadjoint_tc_def')
  ultimately show \<open>a \<in> closure (Collect finite_rank_tc)\<close>
    unfolding sums_def closure_sequential
    apply (auto intro!: simp: sums_def closure_sequential)
    by meson
qed


lemma finite_rank_tc_dense: \<open>closure (Collect finite_rank_tc :: ('a::chilbert_space, 'b::chilbert_space) trace_class set) = UNIV\<close>
proof -
  have \<open>UNIV = closure (Collect finite_rank_tc :: ('a\<times>'b, 'a\<times>'b) trace_class set)\<close>
    by (rule finite_rank_tc_dense_aux[symmetric])
  define l r and corner :: \<open>('a\<times>'b, 'a\<times>'b) trace_class \<Rightarrow> _\<close> where
    \<open>l = cblinfun_left\<close> and \<open>r = cblinfun_right\<close> and
    \<open>corner t = compose_tcl (compose_tcr (r*) t) l\<close> for t
  have [iff]: \<open>bounded_clinear corner\<close>
    by (auto intro: bounded_clinear_compose compose_tcl.bounded_clinear_left compose_tcr.bounded_clinear_right 
        simp: corner_def[abs_def])
  have \<open>UNIV = corner ` UNIV\<close>
  proof (intro UNIV_eq_I range_eqI)
    fix t
    have \<open>from_trace_class (corner (compose_tcl (compose_tcr r t) (l*)))
         = (r* o\<^sub>C\<^sub>L r) o\<^sub>C\<^sub>L from_trace_class t o\<^sub>C\<^sub>L (l* o\<^sub>C\<^sub>L l)\<close>
      by (simp add: corner_def compose_tcl.rep_eq compose_tcr.rep_eq cblinfun_compose_assoc)
    also have \<open>\<dots> = from_trace_class t\<close>
      by (simp add: l_def r_def)
    finally show \<open>t = corner (compose_tcl (compose_tcr r t) (l*))\<close>
      by (metis from_trace_class_inject)
  qed
  also have \<open>\<dots> = corner ` closure (Collect finite_rank_tc)\<close>
    by (simp add: finite_rank_tc_dense_aux)
  also have \<open>\<dots> \<subseteq> closure (corner ` Collect finite_rank_tc)\<close>
    by (auto intro!: bounded_clinear.bounded_linear closure_bounded_linear_image_subset)
  also have \<open>\<dots> \<subseteq> closure (Collect finite_rank_tc)\<close>
  proof (intro closure_mono subsetI CollectI)
    fix t assume \<open>t \<in> corner ` Collect finite_rank_tc\<close>
    then obtain u where \<open>finite_rank_tc u\<close> and tu: \<open>t = corner u\<close>
      by blast
    show \<open>finite_rank_tc t\<close>
      using \<open>finite_rank_tc u\<close>
      by (auto intro!: finite_rank_compose_right[of _ l] finite_rank_compose_left[of _ \<open>r*\<close>]
          simp add: corner_def tu finite_rank_tc.rep_eq compose_tcl.rep_eq compose_tcr.rep_eq)
  qed
  finally show ?thesis
    by blast
qed


hide_fact finite_rank_tc_dense_aux


lemma onb_butterflies_span_trace_class:
  fixes A :: \<open>'a::chilbert_space set\<close> and B :: \<open>'b::chilbert_space set\<close>
  assumes \<open>is_onb A\<close> and \<open>is_onb B\<close>
  shows \<open>ccspan ((\<lambda>(x, y). tc_butterfly x y) ` (A\<times>B)) = \<top>\<close>
proof -
  have \<open>closure (cspan ((\<lambda>(x, y). tc_butterfly x y) ` (A\<times>B))) \<supseteq> Collect rank1_tc\<close>
  proof (rule subsetI)
    \<comment> \<open>This subproof is almost identical to the corresponding one in
        @{thm [source] finite_rank_dense_compact}, and lengthy. Can they be merged into one subproof?\<close>
    fix x :: \<open>('b, 'a) trace_class\<close> assume \<open>x \<in> Collect rank1_tc\<close>
    then obtain a b where xab: \<open>x = tc_butterfly a b\<close>
      apply transfer using rank1_iff_butterfly by fastforce
    define f where \<open>f F G = tc_butterfly (Proj (ccspan F) a) (Proj (ccspan G) b)\<close> for F G
    have lim: \<open>(case_prod f \<longlongrightarrow> x) (finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B)\<close>
    proof (rule tendstoI, subst dist_norm)
      fix e :: real assume \<open>e > 0\<close>
      define d where \<open>d = (if norm a = 0 \<and> norm b = 0 then 1 
                                  else e / (max (norm a) (norm b)) / 4)\<close>
      have d: \<open>norm a * d + norm a * d + norm b * d < e\<close>
      proof -
        have \<open>norm a * d \<le> e/4\<close>
          using \<open>e > 0\<close> apply (auto simp: d_def)
           apply (simp add: divide_le_eq)
          by (smt (z3) Extra_Ordered_Fields.mult_sign_intros(3) \<open>0 < e\<close> antisym_conv divide_le_eq less_imp_le linordered_field_class.mult_imp_div_pos_le mult_left_mono nice_ordered_field_class.dense_le nice_ordered_field_class.divide_nonneg_neg nice_ordered_field_class.divide_nonpos_pos nle_le nonzero_mult_div_cancel_left norm_imp_pos_and_ge ordered_field_class.sign_simps(5) split_mult_pos_le)
        moreover have \<open>norm b * d \<le> e/4\<close>
          using \<open>e > 0\<close> apply (auto simp: d_def)
           apply (simp add: divide_le_eq)
          by (smt (verit) linordered_field_class.mult_imp_div_pos_le mult_left_mono norm_le_zero_iff ordered_field_class.sign_simps(5))
        ultimately have \<open>norm a * d + norm a * d + norm b * d \<le> 3 * e / 4\<close>
          by linarith
        also have \<open>\<dots> < e\<close>
          by (simp add: \<open>0 < e\<close>)
        finally show ?thesis
          by -
      qed
      have [simp]: \<open>d > 0\<close>
        using \<open>e > 0\<close> apply (auto simp: d_def)
         apply (smt (verit, best) nice_ordered_field_class.divide_pos_pos norm_eq_zero norm_not_less_zero)
        by (smt (verit) linordered_field_class.divide_pos_pos zero_less_norm_iff)
      from Proj_onb_limit[where \<psi>=a, OF assms(1)]
      have \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. norm (Proj (ccspan F) a - a) < d\<close>
        by (metis Lim_null \<open>0 < d\<close> order_tendstoD(2) tendsto_norm_zero_iff)
      moreover from Proj_onb_limit[where \<psi>=b, OF assms(2)]
      have \<open>\<forall>\<^sub>F G in finite_subsets_at_top B. norm (Proj (ccspan G) b - b) < d\<close>
        by (metis Lim_null \<open>0 < d\<close> order_tendstoD(2) tendsto_norm_zero_iff)
      ultimately have FG_close: \<open>\<forall>\<^sub>F (F,G) in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B. 
              norm (Proj (ccspan F) a - a) < d \<and> norm (Proj (ccspan G) b - b) < d\<close>
        unfolding case_prod_beta
        by (rule eventually_prodI)
      have fFG_dist: \<open>norm (f F G - x) < e\<close> 
        if \<open>norm (Proj (ccspan F) a - a) < d\<close> and \<open>norm (Proj (ccspan G) b - b) < d\<close>
          and \<open>F \<subseteq> A\<close> and \<open>G \<subseteq> B\<close> for F G
      proof -
        have a_split: \<open>a = Proj (ccspan F) a + Proj (ccspan (A-F)) a\<close>
          using assms apply (simp add: is_onb_def is_ortho_set_def that Proj_orthog_ccspan_union flip: cblinfun.add_left)
          apply (subst Proj_orthog_ccspan_union[symmetric])
           apply (metis DiffD1 DiffD2 in_mono that(3))
          using \<open>F \<subseteq> A\<close> by (auto intro!: simp: Un_absorb1)
        have b_split: \<open>b = Proj (ccspan G) b + Proj (ccspan (B-G)) b\<close>
          using assms apply (simp add: is_onb_def is_ortho_set_def that Proj_orthog_ccspan_union flip: cblinfun.add_left)
          apply (subst Proj_orthog_ccspan_union[symmetric])
           apply (metis DiffD1 DiffD2 in_mono that(4))
          using \<open>G \<subseteq> B\<close> by (auto intro!: simp: Un_absorb1)
        have n1: \<open>norm (f F (B-G)) \<le> norm a * d\<close> for F
        proof -
          have \<open>norm (f F (B-G)) \<le> norm a * norm (Proj (ccspan (B-G)) b)\<close>
            by (auto intro!: mult_right_mono is_Proj_reduces_norm simp add: f_def norm_tc_butterfly)
          also have \<open>\<dots> \<le> norm a * norm (Proj (ccspan G) b - b)\<close>
            by (metis add_diff_cancel_left' b_split less_eq_real_def norm_minus_commute)
          also have \<open>\<dots> \<le> norm a * d\<close>
            by (meson less_eq_real_def mult_left_mono norm_ge_zero that(2))
          finally show ?thesis
            by -
        qed
        have n2: \<open>norm (f (A-F) G) \<le> norm b * d\<close> for G
        proof -
          have \<open>norm (f (A-F) G) \<le> norm b * norm (Proj (ccspan (A-F)) a)\<close>
            by (auto intro!: mult_right_mono is_Proj_reduces_norm simp add: f_def norm_tc_butterfly mult.commute)
          also have \<open>\<dots> \<le> norm b * norm (Proj (ccspan F) a - a)\<close>
            by (smt (verit, best) a_split add_diff_cancel_left' minus_diff_eq norm_minus_cancel)
          also have \<open>\<dots> \<le> norm b * d\<close>
            by (meson less_eq_real_def mult_left_mono norm_ge_zero that(1))
          finally show ?thesis
            by -
        qed
        have \<open>norm (f F G - x) = norm (- f F (B-G) - f (A-F) (B-G) - f (A-F) G)\<close>
          unfolding xab
          apply (subst a_split, subst b_split)
          by (simp add: f_def tc_butterfly_add_right tc_butterfly_add_left)
        also have \<open>\<dots> \<le> norm (f F (B-G)) + norm (f (A-F) (B-G)) + norm (f (A-F) G)\<close>
          by (smt (verit, best) norm_minus_cancel norm_triangle_ineq4)
        also have \<open>\<dots> \<le> norm a * d + norm a * d + norm b * d\<close>
          using n1 n2
          by (meson add_mono_thms_linordered_semiring(1))
        also have \<open>\<dots> < e\<close>
          by (fact d)
        finally show ?thesis
          by -
      qed
      show \<open>\<forall>\<^sub>F FG in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B. norm (case_prod f FG - x) < e\<close>
        apply (rule eventually_elim2)
          apply (rule eventually_prodI[where P=\<open>\<lambda>F. finite F \<and> F \<subseteq> A\<close> and Q=\<open>\<lambda>G. finite G \<and> G \<subseteq> B\<close>])
           apply auto[2]
         apply (rule FG_close)
        using fFG_dist by fastforce
    qed
    have nontriv: \<open>finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B \<noteq> \<bottom>\<close>
      by (simp add: prod_filter_eq_bot)
    have inside: \<open>\<forall>\<^sub>F x in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B. 
              case_prod f x \<in> cspan ((\<lambda>(\<xi>,\<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B))\<close>
    proof (rule eventually_mp[where P=\<open>\<lambda>(F,G). finite F \<and> finite G\<close>])
      show \<open>\<forall>\<^sub>F (F,G) in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B. finite F \<and> finite G\<close>
        by (smt (verit) case_prod_conv eventually_finite_subsets_at_top_weakI eventually_prod_filter)
      have f_in_span: \<open>f F G \<in> cspan ((\<lambda>(\<xi>,\<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B))\<close> if [simp]: \<open>finite F\<close> \<open>finite G\<close> and \<open>F \<subseteq> A\<close> \<open>G \<subseteq> B\<close> for F G
      proof -
        have \<open>Proj (ccspan F) a \<in> cspan F\<close>
          by (metis Proj_range cblinfun_apply_in_image ccspan_finite that(1))
        then obtain r where ProjFsum: \<open>Proj (ccspan F) a = (\<Sum>x\<in>F. r x *\<^sub>C x)\<close>
          apply atomize_elim
          using complex_vector.span_finite[OF \<open>finite F\<close>]
          by auto
        have \<open>Proj (ccspan G) b \<in> cspan G\<close>
          by (metis Proj_range cblinfun_apply_in_image ccspan_finite that(2))
        then obtain s where ProjGsum: \<open>Proj (ccspan G) b = (\<Sum>x\<in>G. s x *\<^sub>C x)\<close>
          apply atomize_elim
          using complex_vector.span_finite[OF \<open>finite G\<close>]
          by auto
        have \<open>tc_butterfly \<xi> \<eta> \<in> (\<lambda>(\<xi>, \<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B)\<close>
          if \<open>\<eta> \<in> G\<close> and \<open>\<xi> \<in> F\<close> for \<eta> \<xi>
          using \<open>F \<subseteq> A\<close> \<open>G \<subseteq> B\<close> that by (auto intro!: pair_imageI)
        then show ?thesis
          by (auto intro!: complex_vector.span_sum complex_vector.span_scale
              intro: complex_vector.span_base[where a=\<open>tc_butterfly _ _\<close>]
              simp add: f_def ProjFsum ProjGsum tc_butterfly_sum_left tc_butterfly_sum_right)
      qed
      show \<open>\<forall>\<^sub>F x in finite_subsets_at_top A \<times>\<^sub>F finite_subsets_at_top B.
                      (case x of (F, G) \<Rightarrow> finite F \<and> finite G) \<longrightarrow> (case x of (F, G) \<Rightarrow> f F G) \<in> cspan ((\<lambda>(\<xi>, \<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B))\<close>
        apply (rule eventually_mono)
        apply (rule eventually_prodI[where P=\<open>\<lambda>F. finite F \<and> F \<subseteq> A\<close> and Q=\<open>\<lambda>G. finite G \<and> G \<subseteq> B\<close>])
        by (auto intro!: f_in_span)
    qed
    show \<open>x \<in> closure (cspan ((\<lambda>(\<xi>, \<eta>). tc_butterfly \<xi> \<eta>) ` (A \<times> B)))\<close>
      using lim nontriv inside by (rule limit_in_closure)
  qed
  moreover have \<open>cspan (Collect rank1_tc :: ('b,'a) trace_class set) = Collect finite_rank_tc\<close>
    using finite_rank_tc_def' by fastforce
  moreover have \<open>closure (Collect finite_rank_tc :: ('b,'a) trace_class set) = UNIV\<close>
    by (rule finite_rank_tc_dense)
  ultimately have \<open>closure (cspan ((\<lambda>(x, y). tc_butterfly x y) ` (A\<times>B))) \<supseteq> UNIV\<close>
    by (smt (verit, del_insts) Un_UNIV_left closed_sum_closure_left closed_sum_cspan closure_closure closure_is_csubspace complex_vector.span_eq_iff complex_vector.subspace_span subset_Un_eq)
  then show ?thesis
    by (metis ccspan.abs_eq ccspan_UNIV closure_UNIV complex_vector.span_UNIV top.extremum_uniqueI)
qed

lemma separating_set_tc_butterfly: \<open>separating_set bounded_clinear ((\<lambda>(g,h). tc_butterfly g h) ` (UNIV \<times> UNIV))\<close>
  apply (rule separating_set_mono[where S=\<open>(\<lambda>(g, h). tc_butterfly g h) ` (some_chilbert_basis \<times> some_chilbert_basis)\<close>])
  by (auto intro!: separating_set_bounded_clinear_dense onb_butterflies_span_trace_class) 

lemma separating_set_tc_butterfly_nested:
  assumes \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c::complex_normed_vector) \<Rightarrow> _) A\<close>
  assumes \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c conjugate_space) \<Rightarrow> _) B\<close>
  shows \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c) \<Rightarrow> _) ((\<lambda>(g,h). tc_butterfly g h) ` (A \<times> B))\<close>
proof -
  from separating_set_tc_butterfly
  have \<open>separating_set bounded_clinear ((\<lambda>(g,h). tc_butterfly g h) ` prod.swap ` (UNIV \<times> UNIV))\<close>
    by simp
  then have \<open>separating_set bounded_clinear ((\<lambda>(g,h). tc_butterfly h g) ` (UNIV \<times> UNIV))\<close>
    unfolding image_image by simp
  then have \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c) \<Rightarrow> _) ((\<lambda>(g,h). tc_butterfly h g) ` (B \<times> A))\<close>
    apply (rule separating_set_bounded_sesquilinear_nested)
    apply (rule bounded_sesquilinear_tc_butterfly)
    using assms by auto
  then have \<open>separating_set (bounded_clinear :: (_ \<Rightarrow> 'c) \<Rightarrow> _) ((\<lambda>(g,h). tc_butterfly h g) ` prod.swap ` (A \<times> B))\<close>
    by (smt (verit, del_insts) SigmaE SigmaI eq_from_separatingI image_iff pair_in_swap_image separating_setI)
  then show ?thesis
    unfolding image_image by simp
qed




end
