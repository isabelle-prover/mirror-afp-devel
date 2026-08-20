section \<open>\<open>Oracle_Programs\<close> -- Oracle programs and their execution\<close>

theory Oracle_Programs imports
  CO_Operations
  Invariant_Preservation
  Compressed_Oracle_Is_RO
begin

subsection \<open>Oracle programs\<close>

datatype ('mem, 'x, 'y) program_step = ProgramStep \<open>'mem update\<close> | QueryStep \<open>'x update \<Rightarrow> 'mem update\<close> \<open>'y update \<Rightarrow> 'mem update\<close>
type_synonym ('mem, 'x, 'y) program = \<open>('mem, 'x, 'y) program_step list\<close>


inductive is_QueryStep :: \<open>('mem,'x,'y::ab_group_add) program_step \<Rightarrow> bool\<close> where is_QueryStep_QueryStep[iff]: \<open>is_QueryStep (QueryStep X Y)\<close>
inductive is_ProgramStep :: \<open>('mem,'x,'y::ab_group_add) program_step \<Rightarrow> bool\<close> where is_ProgramStep_ProgramStep[iff]: \<open>is_ProgramStep (ProgramStep U)\<close>

lemma is_QueryStep_ProgramStep[iff]: \<open>\<not> is_QueryStep (ProgramStep U)\<close>
  using is_QueryStep.cases by blast

lemma is_ProgramStep_QueryStep[iff]: \<open>\<not> is_ProgramStep (QueryStep X Y)\<close>
  by (simp add: is_ProgramStep.simps)

fun valid_program_step where \<open>valid_program_step (QueryStep X Y) = compatible X Y\<close> | \<open>valid_program_step (ProgramStep U) = isometry U\<close>
definition valid_program where \<open>valid_program prog = list_all valid_program_step prog\<close>

lemma valid_program_cons[simp]: \<open>valid_program (p # ps) \<longleftrightarrow> valid_program_step p \<and> valid_program ps\<close>
  by (simp add: valid_program_def)

lemma valid_program_append: \<open>valid_program (p @ q) \<longleftrightarrow> valid_program p \<and> valid_program q\<close>
  by (simp add: valid_program_def)

lemma valid_program_empty[iff]: \<open>valid_program []\<close>
  by (simp add: valid_program_def)

fun exec_program_step :: \<open>('x \<Rightarrow> 'y) \<Rightarrow> ('mem,'x,'y::ab_group_add) program_step \<Rightarrow> 'mem ell2 \<Rightarrow> 'mem ell2\<close> where
  \<open>exec_program_step h (ProgramStep U) \<psi> = U *\<^sub>V \<psi>\<close>
| \<open>exec_program_step h (QueryStep X Y) \<psi> = (X;Y) (function_oracle h) *\<^sub>V \<psi>\<close>

fun exec_program_step_with :: \<open>('x \<times> 'y \<times> 'o) update \<Rightarrow> ('mem,'x,'y) program_step \<Rightarrow> ('mem \<times> 'o) ell2 \<Rightarrow> ('mem \<times> 'o) ell2\<close> where
  \<open>exec_program_step_with Q (ProgramStep U) \<psi> = Fst U *\<^sub>V \<psi>\<close>
| \<open>exec_program_step_with Q (QueryStep X Y) \<psi> = (Fst o X; (Fst o Y; Snd)) Q \<psi>\<close>

definition exec_program :: \<open>('x \<Rightarrow> 'y::ab_group_add) \<Rightarrow> ('mem,'x,'y) program \<Rightarrow> 'mem ell2 \<Rightarrow> 'mem ell2\<close> where
  \<open>exec_program h program \<psi> = fold (exec_program_step h) program \<psi>\<close>
definition exec_program_with :: \<open>('x \<times> 'y \<times> 'o) update \<Rightarrow> ('mem,'x,'y) program \<Rightarrow> ('mem\<times>'o) ell2 \<Rightarrow> ('mem\<times>'o) ell2\<close> where
  \<open>exec_program_with Q program \<psi> = fold (exec_program_step_with Q) program \<psi>\<close>

lemma bounded_clinear_exec_program_step_with[bounded_clinear]: \<open>bounded_clinear (exec_program_step_with Q step)\<close>
  apply (cases step)
  by (auto intro!: cblinfun.bounded_clinear_right simp add: exec_program_step_with.simps[abs_def])

lemma exec_program_empty[simp]: \<open>exec_program h [] \<psi> = \<psi>\<close>
  by (simp add: exec_program_def)
lemma exec_program_with_empty[simp]: \<open>exec_program_with Q [] \<psi> = \<psi>\<close>
  by (simp add: exec_program_with_def)
lemma exec_program_append: \<open>exec_program h (p @ q) \<psi> = exec_program h q (exec_program h p \<psi>)\<close>
  by (simp add: exec_program_def)
lemma exec_program_with_append: \<open>exec_program_with Q (p @ q) \<psi> = exec_program_with Q q (exec_program_with Q p \<psi>)\<close>
  by (simp add: exec_program_with_def)
lemma exec_program_cons[simp]: \<open>exec_program h (step#prog) \<psi> = exec_program h prog (exec_program_step h step \<psi>)\<close>
  by (simp add: exec_program_def)
lemma exec_program_with_cons[simp]: \<open>exec_program_with Q (step#prog) \<psi> = exec_program_with Q prog (exec_program_step_with Q step \<psi>)\<close>
  by (simp add: exec_program_with_def)


lemma norm_exec_program_step_with: \<open>norm (exec_program_step_with oracle program_step \<psi>) \<le> norm \<psi>\<close> if \<open>valid_program_step program_step\<close> and \<open>norm oracle \<le> 1\<close>
proof (cases program_step)
  case (ProgramStep U)
  with that have \<open>isometry U\<close>
    by simp
  then have \<open>norm (Fst U) = 1\<close>
    by (simp add: register_norm norm_isometry)
  then show ?thesis
    apply (simp add: ProgramStep)
    by (smt (verit, del_insts) \<open>norm (Fst U) = 1\<close> mult_cancel_right1 norm_cblinfun)
next
  case (QueryStep X Y)
  with that
  have [register]: \<open>compatible X Y\<close>
    using valid_program_step.simps by blast
  have [register]: \<open>register (Fst \<circ> X;(Fst \<circ> Y;Snd))\<close>
    by simp
  have \<open>norm ((Fst \<circ> X;(Fst \<circ> Y;Snd)) oracle *\<^sub>V \<psi>) \<le> norm ((Fst \<circ> X;(Fst \<circ> Y;Snd)) oracle) * norm \<psi>\<close>
    using norm_cblinfun by blast
  also have \<open>\<dots> = norm oracle * norm \<psi>\<close>
    by (simp add: register_norm)
  also have \<open>\<dots> \<le> norm \<psi>\<close>
  by (simp add: mult_left_le_one_le that(2))
  finally show ?thesis
    by (simp add: QueryStep)
qed

lemma norm_exec_program_with: 
  \<open>norm (exec_program_with oracle program \<psi>) \<le> norm \<psi>\<close> if \<open>norm oracle \<le> 1\<close> and \<open>valid_program program\<close> for program
proof (insert that(2), induction program rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc program_step program)
  then have \<open>valid_program_step program_step\<close> and \<open>valid_program program\<close>
    by (auto simp: valid_program_append)
  have \<open>norm (exec_program_step_with oracle program_step (exec_program_with oracle program \<psi>)) \<le> norm (exec_program_with oracle program \<psi>)\<close>
    by (smt (verit, del_insts) \<open>valid_program_step program_step\<close> mult_left_le_one_le norm_exec_program_step_with norm_ge_zero that(1))
  also have \<open>\<dots> \<le> norm \<psi>\<close>
    using \<open>valid_program program\<close> snoc.IH by force
  finally show ?case
    by (simp add: exec_program_with_append)
qed

lemma norm_exec_program_step_with_isometry:
  assumes \<open>valid_program_step program_step\<close>
  assumes \<open>isometry query\<close>
  shows \<open>norm (exec_program_step_with query program_step \<psi>) = norm \<psi>\<close>
proof (cases program_step)
  case (ProgramStep U)
  with assms have \<open>isometry U\<close>
    by simp
  with ProgramStep show ?thesis
    by (simp add: isometry_preserves_norm register_isometry)
next
  case (QueryStep X Y)
  with assms have [register]: \<open>compatible X Y\<close>
    by simp
  have \<open>register (Fst \<circ> X;(Fst \<circ> Y;Snd))\<close>
    by simp
  with assms have \<open>isometry ((Fst \<circ> X;(Fst \<circ> Y;Snd)) query)\<close>
    using register_isometry by blast
  then show ?thesis
    by (simp add: QueryStep isometry_preserves_norm)
qed

(* (* TODO move *)
lemma norm_exec_program_step_with:
  assumes \<open>norm Q \<le> 1\<close>
  assumes \<open>valid_program_step step\<close>
  assumes \<open>norm \<psi> \<le> 1\<close>
  shows \<open>norm (exec_program_step_with Q step \<psi>) \<le> 1\<close>
proof -
  have aux: \<open>norm (X *\<^sub>V \<psi>) \<le> 1\<close> if \<open>norm X \<le> 1\<close> and \<open>norm \<psi> \<le> 1\<close> for X \<psi>
    by (smt (verit) mult_le_one norm_cblinfun norm_ge_zero that(1,2))
  show ?thesis
  proof (cases step)
    case (ProgramStep U)
    then show ?thesis
    using assms
    by (auto intro!: aux simp: register_norm norm_isometry)
  next
    case (QueryStep X Y)
    with assms have [register]: \<open>compatible X Y\<close>
      by simp
    then have reg: \<open>register (Fst \<circ> X;(Fst \<circ> Y;Snd))\<close>
      by simp
    then show ?thesis
      by (auto intro!: aux assms simp: register_norm[OF ] norm_isometry QueryStep)
  qed
qed

(* TODO move *)
lemma norm_exec_program_with:
  assumes \<open>norm U \<le> 1\<close>
  assumes \<open>valid_program program\<close>
  assumes \<open>norm \<psi> \<le> 1\<close>
  shows \<open>norm (exec_program_with U program \<psi>) \<le> 1\<close>
  using \<open>valid_program program\<close>
  apply (induction program rule:rev_induct)
   apply (simp add: assms)
  by (simp add: assms exec_program_with_append valid_program_append norm_exec_program_step_with) *)


subsection \<open>Lifting\<close>

fun lift_program_step :: \<open>('a update \<Rightarrow> 'mem update) \<Rightarrow> ('a,'x,'y::ab_group_add) program_step \<Rightarrow> ('mem,'x,'y) program_step\<close> where
  \<open>lift_program_step Q (ProgramStep U) = ProgramStep (Q U)\<close>
| \<open>lift_program_step Q (QueryStep X Y) = QueryStep (Q o X) (Q o Y)\<close>

definition lift_program :: \<open>('a update \<Rightarrow> 'mem update) \<Rightarrow> ('a,'x,'y::ab_group_add) program_step list \<Rightarrow> ('mem,'x,'y) program\<close> where
  \<open>lift_program Q p = map (lift_program_step Q) p\<close>

lemma valid_program_step_lift:
  assumes \<open>register Q\<close> and \<open>valid_program_step p\<close>
  shows \<open>valid_program_step (lift_program_step Q p)\<close>
proof (cases p)
  case (ProgramStep U)
  then have \<open>isometry (Q U)\<close>
    using assms register_isometry valid_program_step.simps(2) by blast
  then show ?thesis
    using ProgramStep by auto
next
  case (QueryStep X Y)
  with assms show ?thesis
    by simp
qed

lemma valid_program_lift:
  assumes \<open>register Q\<close> and \<open>valid_program p\<close>
  shows \<open>valid_program (lift_program Q p)\<close>
  using assms(2)
  by (auto simp add: valid_program_def lift_program_def list.pred_map list_all_length valid_program_step_lift assms(1))

lemma lift_program_empty[simp]: \<open>lift_program Q [] = []\<close>
  by (simp add: lift_program_def)

lemma lift_program_cons: \<open>lift_program Q (program_step # program) = lift_program_step Q program_step # lift_program Q program\<close>
  by (simp add: lift_program_def)

lemma lift_program_append: \<open>lift_program Q (program1 @ program2) = lift_program Q program1 @ lift_program Q program2\<close>
  by (simp add: lift_program_def)

lemma is_QueryStep_lift_program_step[simp]: \<open>is_QueryStep (lift_program_step Q program_step) \<longleftrightarrow> is_QueryStep program_step\<close>
  apply (cases program_step)
  by simp_all

lemma filter_is_QueryStep_lift_program: \<open>filter is_QueryStep (lift_program Q program) = lift_program Q (filter is_QueryStep program)\<close>
  apply (induction program)
  by (auto simp: lift_program_def)

lemma length_lift_program[simp]: \<open>length (lift_program Q program) = length program\<close>
  apply (induction program)
  by (auto simp: lift_program_def)

definition \<open>query_count program = length (filter is_QueryStep program)\<close>

lemma query_count_append[simp]: \<open>query_count (p @ q) = query_count p + query_count q\<close>
  by (simp add: query_count_def)
lemma query_count_nil[simp]: \<open>query_count [] = 0\<close>
  by (simp add: query_count_def)
lemma query_count_cons_QueryStep[simp]: \<open>query_count (QueryStep X Y # p) = query_count p + 1\<close>
  by (simp add: query_count_def)
lemma query_count_cons_ProgramStep[simp]: \<open>query_count (ProgramStep U # p) = query_count p\<close>
  by (simp add: query_count_def)
lemma query_count_lift_program[simp]: \<open>query_count (lift_program Q p) = query_count p\<close>
  by (simp add: query_count_def filter_is_QueryStep_lift_program)

lemma exec_lift_program_step_Fst:
  assumes \<open>valid_program_step program_step\<close>
  shows \<open>exec_program_step h (lift_program_step Fst program_step) (\<psi> \<otimes>\<^sub>s \<phi>) = exec_program_step h program_step \<psi> \<otimes>\<^sub>s \<phi>\<close>
proof (cases program_step)
  case (ProgramStep U)
  then show ?thesis
    by (simp add: Fst_def tensor_op_ell2)
next
  case (QueryStep X Y)
  with assms have [register]: \<open>compatible X Y\<close>
    using valid_program_step.simps(1) by blast
  have \<open>(Fst \<circ> (X;Y)) (function_oracle h) *\<^sub>V \<psi> \<otimes>\<^sub>s \<phi> = ((X;Y) (function_oracle h) *\<^sub>V \<psi>) \<otimes>\<^sub>s \<phi>\<close>
    by (simp add: Fst_def tensor_op_ell2)
  then show ?thesis
    by (simp add: QueryStep register_comp_pair)
qed

lemma exec_lift_program_Fst:
  assumes \<open>valid_program program\<close>
  shows \<open>exec_program h (lift_program Fst program) (\<psi> \<otimes>\<^sub>s \<phi>) = exec_program h program \<psi> \<otimes>\<^sub>s \<phi>\<close>
  apply (insert assms, induction program rule:rev_induct)
  by (simp_all add: lift_program_append exec_program_append lift_program_cons valid_program_append exec_lift_program_step_Fst)

subsection \<open>Final measurement\<close>

definition measurement_probability :: \<open>('a update \<Rightarrow> 'mem update) \<Rightarrow> 'mem ell2 \<Rightarrow> 'a \<Rightarrow> real\<close> where 
  \<open>measurement_probability Q \<psi> x = (norm (Q (proj (ket x)) \<psi>))\<^sup>2\<close>

lemma measurement_probability_nonneg: \<open>measurement_probability Q \<psi> x \<ge> 0\<close>
  by (simp add: measurement_probability_def)

lemma norm_register_Proj_ket_invariant_union:
  \<comment> \<open>Helper lemma\<close>
  assumes \<open>register Q\<close> and \<open>A \<inter> B = {}\<close>
  shows \<open>(norm (Q (Proj (ket_invariant (A \<union> B))) \<psi>))\<^sup>2 = (norm (Q (Proj (ket_invariant A)) \<psi>))\<^sup>2 + (norm (Q (Proj (ket_invariant B)) \<psi>))\<^sup>2\<close>
proof -
  have ortho1: \<open>orthogonal_spaces (ket_invariant A) (ket_invariant B)\<close>
    using assms(2) by force
  have ortho2: \<open>is_orthogonal (Q (Proj (ket_invariant A)) *\<^sub>V \<psi>) (Q (Proj (ket_invariant B)) *\<^sub>V \<psi>)\<close>
  proof -
    from ortho1 have \<open>orthogonal_spaces (lift_invariant Q (ket_invariant A)) (lift_invariant Q (ket_invariant B))\<close>
      by (simp add: orthogonal_spaces_lift_invariant assms)
    then have \<open>is_orthogonal (Proj (lift_invariant Q (ket_invariant A)) \<psi>) (Proj (lift_invariant Q (ket_invariant B)) \<psi>)\<close>
      by (metis Proj_lift_invariant assms(1) cblinfun_apply_in_image lift_invariant_def orthogonal_spaces_def)
    moreover have \<open>Proj (lift_invariant Q (ket_invariant A)) = Q (Proj (ket_invariant A))\<close>
      by (simp add: Proj_ket_invariant_butterfly Proj_lift_invariant assms(1) butterfly_eq_proj)
    moreover have \<open>Proj (lift_invariant Q (ket_invariant B)) = Q (Proj (ket_invariant B))\<close>
      by (simp add: Proj_lift_invariant assms(1) ket_invariant_def)
    ultimately show ?thesis
      by simp
  qed    
  have \<open>(norm (Q (Proj (ket_invariant (A \<union> B))) \<psi>))\<^sup>2 = (norm (Q (Proj (ket_invariant A \<squnion> ket_invariant B)) \<psi>))\<^sup>2\<close>
    by (simp add: ket_invariant_union)
  also have \<open>\<dots> = (norm (Q (Proj (ket_invariant A) + (Proj (ket_invariant B))) \<psi>))\<^sup>2\<close>
    by (metis Proj_sup ortho1) 
  also have \<open>\<dots> = (norm (Q (Proj (ket_invariant A)) \<psi> + Q (Proj (ket_invariant B)) \<psi>))\<^sup>2\<close>
    by (simp add: complex_vector.linear_add clinear_register \<open>register Q\<close> cblinfun.add_left)
  also have \<open>\<dots> = (norm (Q (Proj (ket_invariant A)) \<psi>))\<^sup>2 + (norm (Q (Proj (ket_invariant B)) \<psi>))\<^sup>2\<close>
    by (simp add: pythagorean_theorem ortho2)
  finally show ?thesis
    by -
qed



lemma measurement_probability_sum:
  assumes \<open>register Q\<close> and \<open>finite F\<close>
  shows \<open>(\<Sum>x\<in>F. measurement_probability Q \<psi> x) = (norm (Q (Proj (ket_invariant F)) \<psi>))\<^sup>2\<close>
proof (use \<open>finite F\<close> in induction)
  case empty
  show ?case
    apply simp
    by (metis (no_types, lifting) assms(1) cancel_comm_monoid_add_class.diff_cancel cblinfun.zero_left register_minus)
next
  case (insert x F)
  have \<open>(norm (Q (Proj (ket_invariant (insert x F))) *\<^sub>V \<psi>))\<^sup>2 = (norm (Q (Proj (ket_invariant F)) *\<^sub>V \<psi>))\<^sup>2 + (norm (Q (Proj (ket_invariant {x})) *\<^sub>V \<psi>))\<^sup>2\<close>
    apply (rewrite at \<open>insert x F\<close> to \<open>F \<union> {x}\<close> DEADID.rel_mono_strong)
     apply simp
    apply (subst norm_register_Proj_ket_invariant_union)
    by (simp_all add: assms insert.hyps)
  also have \<open>\<dots> = (norm (Q (proj (ket x)) \<psi>))\<^sup>2 + (norm (Q (Proj (ccspan (ket ` F))) \<psi>))\<^sup>2\<close>
    by (simp add: ket_invariant_def)
  also have \<open>\<dots> = (norm (Q (proj (ket x)) \<psi>))\<^sup>2 + sum (measurement_probability Q \<psi>) F\<close>
    by (simp add: insert.IH ket_invariant_def)
  also have \<open>\<dots> = sum (measurement_probability Q \<psi>) (insert x F)\<close>
    by (simp add: insert.hyps measurement_probability_def)
  finally show ?case
    by simp
qed

lemma
  assumes \<open>register Q\<close>
  shows measurement_probability_summable: \<open>measurement_probability Q \<psi> summable_on A\<close>
    and measurement_probability_infsum_leq: \<open>(\<Sum>\<^sub>\<infinity>x\<in>A. measurement_probability Q \<psi> x) \<le> (norm (Q (Proj (ket_invariant A)) \<psi>))\<^sup>2\<close>
proof -
  define m s where \<open>m x = measurement_probability Q \<psi> x\<close> and \<open>s A = (norm (Q (Proj (ket_invariant A)) \<psi>))\<^sup>2\<close> for A x
  have sum_m_fin: \<open>sum m F = s F\<close> if \<open>finite F\<close> for F
    by (simp add: measurement_probability_sum m_def s_def that assms)
  have s_mono: \<open>s A \<le> s B\<close> if \<open>A \<subseteq> B\<close> for A B
  proof -
    have [simp]: \<open>A \<union> B = B\<close>
      using that by blast
    have \<open>s A \<le> s A + s (B-A)\<close>
      by (simp add: s_def)
    also have \<open>\<dots> = s B\<close>
      apply (simp add: s_def)
      apply (subst norm_register_Proj_ket_invariant_union[symmetric])
      using that
      by (auto simp: assms)
    finally show ?thesis
      by -
  qed
  have m_pos: \<open>m x \<ge> 0\<close> for x
    by (simp add: m_def measurement_probability_nonneg)
  show summable: \<open>m summable_on A\<close> for A
    apply (rule nonneg_bounded_partial_sums_imp_summable_on[where C=\<open>s UNIV\<close>])
    using s_mono[of _ UNIV] sum_m_fin
    by (auto intro!: eventually_finite_subsets_at_top_weakI simp: m_pos)
  then show \<open>infsum m A \<le> s A\<close>
    apply (rule infsum_le_finite_sums)
    using s_mono[of _ A] sum_m_fin
    by auto
qed

lemma dist_inv_measurement_probability:
  fixes I :: \<open>'i::finite set\<close>
  assumes [register]: \<open>register Q\<close>
  shows \<open>(\<Sum>x\<in>I. measurement_probability Q \<psi> x) = (dist_inv Q (ket_invariant (-I)) \<psi>)\<^sup>2\<close>
proof -
  have \<open>(\<Sum>x\<in>I. measurement_probability Q \<psi> x) = (norm (Q (Proj (ket_invariant I)) *\<^sub>V \<psi>))\<^sup>2\<close>
    by (simp add: measurement_probability_sum)
  then show ?thesis
    by (simp add: dist_inv_def ket_invariant_compl)
qed

lemma dist_inv_avg_measurement_probability:
  fixes I :: \<open>'h::finite \<Rightarrow> 'i::finite set\<close>
  assumes [register]: \<open>register Q\<close>
  shows \<open>(\<Sum>h\<in>UNIV. \<Sum>x\<in>I h. measurement_probability Q (\<psi> h) x) / CARD('h)
             = (dist_inv_avg Q (\<lambda>h. ket_invariant (- I h)) \<psi>)\<^sup>2\<close>
  by (simp add: dist_inv_avg_def real_sqrt_pow2 divide_nonneg_pos
      sum_nonneg dist_inv_measurement_probability)



subsection \<open>Preservation\<close>



lemma dist_inv_avg_exec_compatible:
  fixes prog
  assumes \<open>valid_program prog\<close>
  assumes [register]: \<open>compatible Q R\<close>
  shows \<open>dist_inv_avg Q I (\<lambda>h::'x::finite\<Rightarrow>'y::{finite,ab_group_add}. exec_program h (lift_program R prog) (\<psi> h))
       \<le> dist_inv_avg Q I \<psi>\<close>
proof (insert \<open>valid_program prog\<close>, induction prog rule:rev_induct)
  case Nil
  with assms show ?case
    by simp
next
  case (snoc program_step prog)
  show ?case
  proof (cases program_step)
    case (ProgramStep U)
    have \<open>dist_inv_avg Q I (\<lambda>h. exec_program h (lift_program R (prog @ [program_step])) (\<psi> h))
         \<le> (MAX h::'x\<Rightarrow>'y. norm U) * dist_inv_avg Q I (\<lambda>h. exec_program h (lift_program R prog) (\<psi> h))\<close>
      apply (simp add: lift_program_append lift_program_cons exec_program_append ProgramStep del: range_constant Max_const)
      apply (rule dist_inv_avg_apply_compatible[where R=\<open>\<lambda>_. R\<close>])
      by simp
    also have \<open>\<dots> \<le> dist_inv_avg Q I \<psi>\<close>
      using snoc
      by (simp_all add: ProgramStep norm_isometry valid_program_append)
    finally show ?thesis
      by -
  next
    case (QueryStep X Y)
    with snoc have [register]: \<open>compatible X Y\<close> by (simp add: valid_program_append)
    have \<open>dist_inv_avg Q I (\<lambda>h. exec_program h (lift_program R (prog @ [program_step])) (\<psi> h)) 
      \<le> (MAX h::'x\<Rightarrow>'y. norm (function_oracle h)) * dist_inv_avg Q I (\<lambda>h. exec_program h (lift_program R prog) (\<psi> h))\<close>
      apply (simp add: lift_program_append lift_program_cons exec_program_append QueryStep 
          del: range_constant Max_const norm_function_oracle)
       apply (rule dist_inv_avg_apply_compatible[where R=\<open>\<lambda>_. (R \<circ> X;R \<circ> Y)\<close>])
      by simp
    also have \<open>\<dots> \<le> dist_inv_avg Q I \<psi>\<close>
      using snoc
      by (simp_all add: QueryStep valid_program_append)
    finally show ?thesis
      by -
  qed
qed

lemma dist_inv_exec'_compatible:
  fixes prog
  assumes \<open>valid_program prog\<close>
  assumes normU: \<open>norm U \<le> 1\<close>
  assumes [register]: \<open>register R\<close>
  assumes compatQ1[register]: \<open>compatible Q (Fst o R)\<close>
  assumes compatQ2[register]: \<open>compatible Q Snd\<close>
  shows \<open>dist_inv Q I (exec_program_with U (lift_program R prog) \<psi>) \<le> dist_inv Q I \<psi>\<close>
proof (insert \<open>valid_program prog\<close>, induction prog rule:rev_induct)
  case Nil
  with assms show ?case
    by simp
next
  case (snoc program_step prog)
  show ?case
  proof (cases program_step)
    case (ProgramStep V)
    have \<open>dist_inv Q I (exec_program_with U (lift_program R (prog @ [program_step])) \<psi>)
      \<le> norm V * dist_inv Q I (exec_program_with U (lift_program R prog) \<psi>)\<close>
      apply (simp add: lift_program_append exec_program_with_append lift_program_cons ProgramStep)
      using dist_inv_apply_compatible[OF compatQ1]
      by simp
    also have \<open>\<dots> \<le> dist_inv Q I \<psi>\<close>
      using ProgramStep norm_isometry snoc(1) snoc.prems valid_program_append exec_program_with_append by fastforce
    finally show ?thesis
      by -
  next
    case (QueryStep X Y)
    with snoc have [register]: \<open>compatible X Y\<close> by (simp add: valid_program_append)
    then have compat[register]: \<open>compatible Q (Fst \<circ> (R \<circ> X);(Fst \<circ> (R \<circ> Y);Snd))\<close>
      by (auto intro!: compatible3' compatible_comp_inner simp flip: comp_assoc)
    have \<open>dist_inv Q I (exec_program_with U (lift_program R (prog @ [program_step])) \<psi>)
      \<le> norm U * dist_inv Q I (exec_program_with U (lift_program R prog) \<psi>)\<close>
      apply (simp add: lift_program_append lift_program_cons QueryStep exec_program_with_append)
      by (rule dist_inv_apply_compatible[OF compat])
    also have \<open>\<dots> \<le> dist_inv Q I \<psi>\<close>
      by (smt (verit, ccfv_SIG) assms(2) dist_inv_pos mult_cancel_right1
          mult_left_le_one_le snoc(1) snoc.prems valid_program_append zero_le_mult_iff)
    finally show ?thesis
      by -
  qed
qed




subsection \<open>Misc\<close>

(* TODO sort me *)

lemma dist_inv_induct:
  fixes "oracle" :: \<open>('x \<times> 'y::ab_group_add \<times> ('x \<Rightarrow> 'y option)) update\<close>
  assumes \<open>compatible R Fst\<close>
  assumes \<open>(\<Sum>i<query_count program. g i) \<le> \<epsilon>\<close>
  assumes init: \<open>\<psi>0 \<in> space_as_set (lift_invariant R (J 0))\<close>
  assumes \<open>J (query_count program) \<le> I\<close>
  assumes \<open>valid_program program\<close>
  assumes \<open>\<And>X Y i. compatible X Y \<Longrightarrow> preserves ((Fst \<circ> X;(Fst \<circ> Y;Snd)) oracle :: ('m \<times> _) update) (lift_invariant R (J i))
           (lift_invariant R (J (Suc i))) (g i)\<close>
  assumes \<open>norm oracle \<le> 1\<close>
  assumes \<open>norm \<psi>0 \<le> 1\<close>
  shows \<open>dist_inv R I (exec_program_with oracle program \<psi>0) \<le> \<epsilon>\<close>
proof -
  note [[simproc del: Laws_Quantum.compatibility_warn]]
  define f where \<open>f n = (\<Sum>i<n. g i)\<close> for n
  from \<open>compatible R Fst\<close> have [register]: \<open>register R\<close>
    using compatible_register1 by blast
  have \<open>dist_inv R (J (query_count program)) (exec_program_with oracle program \<psi>0) \<le> f (query_count program)\<close>
  proof (insert \<open>valid_program program\<close>, induction program rule:rev_induct)
    case Nil
    from init
    have \<open>dist_inv R (J 0) \<psi>0 = 0\<close>
      by (simp add: dist_inv_0_iff)
    then show ?case
      by (simp add: assms(2) query_count_def f_def)
  next
    case (snoc program_step program)
    from snoc.prems have \<open>valid_program program\<close>
      using valid_program_append by blast
    from snoc.prems have \<open>valid_program_step program_step\<close>
      by (simp add: valid_program_append)
    define i where \<open>i = query_count program\<close>
    show ?case
    proof (cases program_step)
      case (ProgramStep U)
      with \<open>valid_program_step program_step\<close>
      have [iff]: \<open>isometry U\<close>
        by simp
      have \<open>preserves (Fst U) (lift_invariant R (J i)) (lift_invariant R (J i)) 0\<close>
        apply (rule_tac preserves_compatible[where F=Fst])
        using \<open>compatible R Fst\<close> compatible_register_invariant_compatible_register compatible_sym apply blast
        by simp
      then have \<open>dist_inv R (J i) (Fst U *\<^sub>V exec_program_with oracle program \<psi>0) \<le> f i\<close>
        apply (rule dist_inv_leq_if_preserves[THEN order_trans])
        using snoc.IH[OF \<open>valid_program program\<close>]
        by (simp_all add: norm_isometry register_isometry query_count_def i_def)
      then show ?thesis
        by (simp add: ProgramStep exec_program_with_append i_def query_count_def)
    next
      case (QueryStep X Y)
      with \<open>valid_program_step program_step\<close>
      have [register]: \<open>compatible X Y\<close>
        by simp
      with assms have pres: \<open>preserves ((Fst \<circ> X;(Fst \<circ> Y;Snd)) oracle) (lift_invariant R (J i))
           (lift_invariant R (J (Suc i))) (g i)\<close>
        by fast
      have fg': \<open>norm ((Fst \<circ> X;(Fst \<circ> Y;Snd)) oracle) * f i + g i * norm (exec_program_with oracle program \<psi>0) \<le> f (Suc i)\<close>
      proof -
        have \<open>norm ((Fst \<circ> X;(Fst \<circ> Y;Snd)) oracle) \<le> 1\<close>
          apply (subst register_norm[where a="oracle"])
          by (simp_all add: assms)
        moreover have \<open>norm (exec_program_with oracle program \<psi>0) \<le> 1\<close>
          apply (rule norm_exec_program_with[THEN order_trans])
          using \<open>valid_program program\<close> assms by simp_all
        moreover have \<open>f i + g i \<le> f (Suc i)\<close>
          by (simp add: f_def)
        moreover have gpos: \<open>g i \<ge> 0\<close> for i
          using \<open>compatible X Y\<close> assms(6) preserves_def by blast
        moreover have \<open>f i \<ge> 0\<close>
          by (auto intro!: sum_nonneg gpos simp: f_def)
        ultimately  
        show ?thesis
          by (smt (verit) mult_left_le mult_left_le_one_le norm_ge_zero)
      qed
      show ?thesis
        apply (simp add: QueryStep exec_program_with_append flip: i_def)
        using pres apply (rule dist_inv_leq_if_preserves[THEN order_trans])
          apply (simp, simp)
        using snoc.IH[OF \<open>valid_program program\<close>, folded i_def]
        by (smt (verit, ccfv_SIG) fg' mult_left_mono norm_ge_zero)
    qed
  qed
  with assms show ?thesis
    using \<open>register R\<close>
    by (smt (verit, best) dist_inv_mono f_def)
qed

subsection \<open>Random Oracles\<close>

lemma standard_query_for_fixed_function_generic:
  fixes standard_query
  assumes \<open>\<And>H x y z. H x = Some z \<Longrightarrow> standard_query *\<^sub>V (ket (x,y,H)) = ket (x, y + z, H)\<close> (* e.g. standard_query_ket_full_Some *)
  assumes \<open>valid_program program\<close>
  shows \<open>exec_program h program initial_state \<otimes>\<^sub>s ket (Some o h) 
       = exec_program_with standard_query program (initial_state \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
proof (insert \<open>valid_program program\<close>, induction program rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc program_step prog)
  then have [simp]: \<open>valid_program prog\<close>
    using list_all_append valid_program_def by blast
  show ?case
  proof (cases program_step)
    case (ProgramStep U)
    have \<open>exec_program h (prog @ [program_step]) initial_state \<otimes>\<^sub>s ket (Some \<circ> h) = (U *\<^sub>V exec_program h prog initial_state) \<otimes>\<^sub>s ket (Some \<circ> h)\<close>
      by (simp add: ProgramStep exec_program_append)
    also have \<open>\<dots> = Fst U *\<^sub>V exec_program h prog initial_state \<otimes>\<^sub>s ket (Some \<circ> h)\<close>
      by (simp add: Fst_def tensor_op_ell2)
    also have \<open>\<dots> = Fst U *\<^sub>V exec_program_with standard_query prog (initial_state \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
      by (subst snoc.IH, simp_all)
    also have \<open>\<dots> = exec_program_with standard_query (prog @ [program_step]) (initial_state \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
      by (simp add: ProgramStep exec_program_with_append)
    finally show ?thesis
      by -
  next
    case (QueryStep X Y)
    then have [register]: \<open>compatible X Y\<close>
      using snoc.prems valid_program_def by force
    have \<open>exec_program h (prog @ [program_step]) initial_state \<otimes>\<^sub>s ket (Some \<circ> h) = ((X;Y) (function_oracle h) *\<^sub>V exec_program h prog initial_state) \<otimes>\<^sub>s ket (Some \<circ> h)\<close>
      by (simp add: QueryStep exec_program_append)
    also have \<open>\<dots> = Fst ((X;Y) (function_oracle h)) *\<^sub>V (exec_program h prog initial_state \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
      by (simp add: Fst_def tensor_op_ell2)
    also have \<open>\<dots> = (Fst o X; (Fst o Y; Snd)) standard_query *\<^sub>V (exec_program h prog initial_state \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
      by (simp add: standard_query_for_fixed_func_generic assms)
    also have \<open>\<dots> = (Fst o X; (Fst o Y; Snd)) standard_query *\<^sub>V exec_program_with standard_query prog (initial_state \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
      by (subst snoc.IH, simp_all)
    also have \<open>\<dots> = exec_program_with standard_query (prog @ [program_step]) (initial_state \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
      by (simp add: QueryStep exec_program_with_append)
    finally show ?thesis
      by -
  qed
qed

lemma standard_query_for_fixed_function_dist_inv_generic:
  assumes \<open>\<And>H x y z. H x = Some z \<Longrightarrow> standard_query *\<^sub>V (ket (x,y,H)) = ket (x, y + z, H)\<close> (* e.g. standard_query_ket_full_Some *)
  assumes \<open>valid_program program\<close>
  assumes compat: \<open>compatible_invariants (\<top> \<otimes>\<^sub>S ccspan {ket (Some \<circ> h)}) J\<close>
  assumes IJ: \<open>J \<sqinter> (\<top> \<otimes>\<^sub>S ccspan{ket (Some o h)}) = I \<otimes>\<^sub>S ccspan{ket (Some o h)}\<close>
  assumes [register]: \<open>register Q\<close>
  shows \<open>dist_inv Q I (exec_program h program initial_state) =
    dist_inv (Fst o Q; Snd) J (exec_program_with standard_query program (initial_state \<otimes>\<^sub>s ket (Some \<circ> h)))\<close>
proof -
  define e1 e2 where \<open>e1 = exec_program h program initial_state\<close> and \<open>e2 = exec_program_with standard_query program (initial_state \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
  define keth where \<open>keth = ket (Some o h)\<close>
  have e2e1: \<open>e2 = e1 \<otimes>\<^sub>s keth\<close>
    unfolding e1_def e2_def keth_def
    using standard_query_for_fixed_function_generic assms
    by fastforce
  have \<open>dist_inv Q I e1 = norm ((id_cblinfun - Q (Proj I)) *\<^sub>V e1)\<close>
    by (simp add: dist_inv_def Proj_ortho_compl register_minus)
  also have \<open>\<dots> = norm (e1 \<otimes>\<^sub>s keth - (Q (Proj I) *\<^sub>V e1) \<otimes>\<^sub>s keth)\<close>
    by (simp add: norm_tensor_ell2 keth_def cblinfun.diff_left flip: tensor_ell2_diff1)
  also have \<open>\<dots> = norm ((id_cblinfun - Fst (Q (Proj I)) o\<^sub>C\<^sub>L Snd (proj keth)) *\<^sub>V e1 \<otimes>\<^sub>s keth)\<close>
    by (simp add: Fst_def Snd_def comp_tensor_op tensor_op_ell2 cblinfun.diff_left)
  also have \<open>\<dots> = dist_inv (Fst o Q; Snd) (I \<otimes>\<^sub>S ccspan{keth}) (e1 \<otimes>\<^sub>s keth)\<close>
    by (simp add: dist_inv_def Proj_ortho_compl register_minus tensor_ccsubspace_via_Proj
        Proj_on_own_range is_Proj_tensor_op register_pair_apply)
  also have \<open>\<dots> = dist_inv (Fst o Q; Snd) (J \<sqinter> (\<top> \<otimes>\<^sub>S ccspan{ket (Some o h)})) (e1 \<otimes>\<^sub>s keth)\<close>
    by (simp add: IJ keth_def)
  also have \<open>\<dots> = dist_inv (Fst o Q; Snd) J (e1 \<otimes>\<^sub>s keth)\<close>
    using compat apply (rule dist_inv_intersect_onesided)
     apply simp
    by (simp add: dist_inv_def Proj_ortho_compl register_minus tensor_ccsubspace_via_Proj
        Proj_on_own_range is_Proj_tensor_op register_pair_apply cblinfun.diff_left keth_def)
  also have \<open>\<dots> = dist_inv (Fst o Q; Snd) J e2\<close>
    by (simp add: e2e1)
  finally show \<open>dist_inv Q I e1 = \<dots>\<close>
    by -
qed



lemma standard_query_is_ro_generic:
  fixes standard_query
  assumes \<open>\<And>H x y z. H x = Some z \<Longrightarrow> standard_query *\<^sub>V (ket (x,y,H)) = ket (x, y + z, H)\<close> (* e.g. standard_query_ket_full_Some *)
  assumes \<open>valid_program program\<close>
  shows \<open>exec_program_with standard_query program (initial_state \<otimes>\<^sub>s (superpos_total :: ('x::finite \<Rightarrow> 'y::{finite,ab_group_add} option) ell2))
      = (\<Sum>h\<in>UNIV. (exec_program h program initial_state \<otimes>\<^sub>s ket (Some o h)) /\<^sub>R sqrt CARD('x \<Rightarrow> 'y))\<close>
proof (insert assms(2), induction program rule: rev_induct)
  case Nil
  have \<open>sum ket (total_functions :: ('x \<Rightarrow> 'y option) set) = (\<Sum>h\<in>UNIV. ket (\<lambda>a. Some (h a)))\<close>
    apply (simp add: total_functions_def2 sum.reindex fun.inj_map)
    by (simp add: o_def)
  then show ?case
    by (simp add: uniform_superpos_def2 scaleR_scaleC card_fun card_total_functions tensor_ell2_scaleC2
        flip: scaleC_sum_right tensor_ell2_sum_right)
next
  case (snoc step prog)
  then have \<open>valid_program_step step\<close> and [iff]: \<open>valid_program prog\<close>
    by (simp_all add: valid_program_append)
  have \<open>exec_program_step_with standard_query step (\<psi> \<otimes>\<^sub>s ket (Some o h)) =
        exec_program_step h step \<psi> \<otimes>\<^sub>s ket (Some o h)\<close> for h \<psi>
  proof (cases step)
    case (ProgramStep U)
    then show ?thesis
      by (simp add: Fst_def tensor_op_ell2)
  next
    case (QueryStep X Y)
    with \<open>valid_program_step step\<close> have [register]: \<open>compatible X Y\<close>
      by simp
    have \<open>exec_program_step_with standard_query step (\<psi> \<otimes>\<^sub>s ket (Some \<circ> h))
        = (Fst \<circ> X;(Fst \<circ> Y;Snd)) standard_query *\<^sub>V (\<psi> \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
      by (simp add: QueryStep)
    also have \<open>\<dots> = ((Fst \<circ> X;(Fst \<circ> Y;Snd)) standard_query o\<^sub>C\<^sub>L Snd (selfbutter (ket (Some o h)))) *\<^sub>V (\<psi> \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
      by simp
    also have \<open>\<dots> = (Fst \<circ> X;(Fst \<circ> Y;Snd)) (standard_query o\<^sub>C\<^sub>L (Snd o Snd) (selfbutter (ket (Some o h)))) *\<^sub>V (\<psi> \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
      by (simp add: register_mult[symmetric, where F=\<open>(_;_)\<close>] register_pair_Snd[unfolded o_def, THEN fun_cong])
    also have \<open>\<dots> = (Fst \<circ> X;(Fst \<circ> Y;Snd)) ((Fst; Snd o Fst) (function_oracle h) o\<^sub>C\<^sub>L (Snd o Snd) (selfbutter (ket (Some o h)))) *\<^sub>V (\<psi> \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
      apply (rewrite at \<open>(Fst;Snd \<circ> Fst) (function_oracle h)\<close> to \<open>assoc (function_oracle h \<otimes>\<^sub>o id_cblinfun)\<close> DEADID.rel_mono_strong)
       apply (simp add: assoc_def register_pair_Fst[unfolded o_def, THEN fun_cong] flip: Fst_def)
      apply (rule arg_cong[where f=\<open>\<lambda>x. (_;_) x *\<^sub>V _\<close>])
      by (auto intro!: equal_ket simp: Snd_def tensor_op_ket cinner_ket tensor_ell2_ket assms
          assoc_ell2_sandwich sandwich_apply function_oracle_apply)
    also have \<open>\<dots> = ((Fst \<circ> X;(Fst \<circ> Y;Snd)) ((Fst; Snd o Fst) (function_oracle h)) o\<^sub>C\<^sub>L Snd (selfbutter (ket (Some o h)))) *\<^sub>V (\<psi> \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
      by (simp add: register_mult[symmetric, where F=\<open>(_;_)\<close>] register_pair_Snd[unfolded o_def, THEN fun_cong])
    also have \<open>\<dots> = (Fst \<circ> X;(Fst \<circ> Y;Snd)) ((Fst; Snd o Fst) (function_oracle h)) *\<^sub>V (\<psi> \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
      by simp
    also have \<open>\<dots> = Fst ((X;Y) (function_oracle h)) *\<^sub>V (\<psi> \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
      apply (rewrite at \<open>(Fst \<circ> X;(Fst \<circ> Y;Snd)) ((Fst;Snd \<circ> Fst) _)\<close> to \<open>((Fst \<circ> X;(Fst \<circ> Y;Snd)) o (Fst;Snd \<circ> Fst)) _\<close> DEADID.rel_mono_strong)
       apply simp
      apply (subst register_comp_pair[symmetric])
        apply (simp, simp)
      by (simp add: register_pair_Snd register_pair_Fst register_comp_pair flip: comp_assoc)
    also have \<open>\<dots> = ((X;Y) (function_oracle h) *\<^sub>V \<psi>) \<otimes>\<^sub>s ket (Some \<circ> h)\<close>
      by (simp add: Fst_def tensor_op_ell2)
    also have \<open>\<dots> = exec_program_step h step \<psi> \<otimes>\<^sub>s ket (Some \<circ> h)\<close>
      by (simp add: QueryStep)
    finally show ?thesis
      by -
  qed
  then show ?case
    by (simp add: exec_program_with_append exec_program_append snoc.IH o_def
        complex_vector.linear_sum[where f=\<open>exec_program_step_with standard_query step\<close>]
        bounded_clinear.clinear bounded_clinear_exec_program_step_with scaleR_scaleC
        clinear.scaleC)
qed



lemma standard_query_is_ro_dist_inv_generic:
  fixes standard_query :: \<open>('x::finite \<times> 'y::{finite,ab_group_add} \<times> ('x \<rightharpoonup> 'y)) ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>
  assumes \<open>\<And>H x y z. H x = Some z \<Longrightarrow> standard_query *\<^sub>V (ket (x,y,H)) = ket (x, y + z, H)\<close> (* e.g. standard_query_ket_full_Some *)
  assumes \<open>valid_program program\<close>
  assumes [register]: \<open>register Q\<close>
  shows \<open>dist_inv_avg Q (\<lambda>_. I) (\<lambda>h. exec_program h program initial_state) =
    dist_inv (Fst o Q) I (exec_program_with standard_query program (initial_state \<otimes>\<^sub>s superpos_total))\<close> (is \<open>?lhs = ?rhs\<close>)
proof -
  have \<open>?rhs\<^sup>2 = (dist_inv (Fst \<circ> Q) I (\<Sum>h\<in>UNIV. (exec_program h program initial_state \<otimes>\<^sub>s ket (Some \<circ> h)) /\<^sub>R sqrt (real CARD('x \<Rightarrow> 'y))))\<^sup>2\<close>
    apply (subst standard_query_is_ro_generic)
    using assms by simp_all
  also have \<open>\<dots> = (norm (\<Sum>i\<in>UNIV. ((Q (Proj (- I)) *\<^sub>V exec_program i program initial_state) \<otimes>\<^sub>s ket (Some \<circ> i)) /\<^sub>R sqrt (real CARD('x \<Rightarrow> 'y))))\<^sup>2\<close>
    by (simp add: dist_inv_def cblinfun.sum_right Fst_def tensor_op_ell2 cblinfun.scaleR_right)
  also have \<open>\<dots> = (\<Sum>a\<in>UNIV. (norm (((Q (Proj (- I)) *\<^sub>V exec_program a program initial_state) \<otimes>\<^sub>s ket (Some \<circ> a)) /\<^sub>R sqrt (real CARD('x \<Rightarrow> 'y))))\<^sup>2)\<close>
    apply (subst pythagorean_theorem_sum)
      apply (simp, metis fun.inj_map_strong option.inject)
     apply simp
    by simp
  also have \<open>\<dots> = (\<Sum>a\<in>UNIV. (dist_inv (Fst o Q) I (exec_program a program initial_state \<otimes>\<^sub>s ket (Some \<circ> a)))\<^sup>2 /\<^sub>R real CARD('x \<Rightarrow> 'y))\<close>
    by (auto intro!: sum.cong simp: dist_inv_def Fst_def tensor_op_ell2 power_mult_distrib real_inv_sqrt_pow2)
  also have \<open>\<dots> = (\<Sum>x\<in>UNIV. (dist_inv Q I (exec_program x program initial_state))\<^sup>2) /\<^sub>R real CARD('x \<Rightarrow> 'y)\<close>
    by (metis (no_types, lifting) dist_inv_Fst_tensor norm_ket scaleR_right.sum sum.cong)
  also have \<open>\<dots> = ?lhs\<^sup>2\<close>
    by (simp add: dist_inv_avg_def real_sqrt_pow2 sum_nonneg divide_inverse flip: sum_distrib_left)
  finally show ?thesis
    by simp
qed

lemma (in compressed_oracle) standard_query_is_ro_dist_inv:
  assumes \<open>valid_program program\<close>
  assumes [register]: \<open>register Q\<close>
  shows \<open>dist_inv_avg Q (\<lambda>_. I) (\<lambda>h. exec_program h program initial_state) =
    dist_inv (Fst o Q) I (exec_program_with standard_query program (initial_state \<otimes>\<^sub>s superpos_total))\<close> (is \<open>?lhs = ?rhs\<close>)
  using standard_query_ket_full_Some assms by (rule standard_query_is_ro_dist_inv_generic)

lemma (in compressed_oracle) standard_query'_is_ro_dist_inv:
  assumes \<open>valid_program program\<close>
  assumes [register]: \<open>register Q\<close>
  shows \<open>dist_inv_avg Q (\<lambda>_. I) (\<lambda>h. exec_program h program initial_state) =
    dist_inv (Fst o Q) I (exec_program_with standard_query' program (initial_state \<otimes>\<^sub>s superpos_total))\<close> (is \<open>?lhs = ?rhs\<close>)
  using standard_query'_ket_full_Some assms by (rule standard_query_is_ro_dist_inv_generic)



lemma (in compressed_oracle) compress_query_is_standard_query_generic:
  fixes query standard_query
  assumes \<open>valid_program program\<close>
  assumes \<open>standard_query o\<^sub>C\<^sub>L reg_3_3 compress = reg_3_3 compress o\<^sub>C\<^sub>L query\<close>
  shows \<open>exec_program_with standard_query program (initial_state \<otimes>\<^sub>s superpos_total)
      =  Snd compress *\<^sub>V exec_program_with query program (initial_state \<otimes>\<^sub>s ket (\<lambda>x. None))\<close>
proof (insert \<open>valid_program program\<close>, induction program rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: compress_empty)
next
  case (snoc program_step prog)
  then have [simp]: \<open>valid_program prog\<close>
    by (simp add: valid_program_def)
  show ?case
  proof (cases program_step)
    case (ProgramStep U)
    have \<open>exec_program_with standard_query (prog @ [program_step]) (initial_state \<otimes>\<^sub>s superpos_total)
         = Fst U *\<^sub>V Snd compress *\<^sub>V exec_program_with query prog (initial_state \<otimes>\<^sub>s ket Map.empty)\<close>
      by (simp add: ProgramStep snoc.IH exec_program_with_append)
    also have \<open>\<dots> = Snd compress *\<^sub>V Fst U *\<^sub>V exec_program_with query prog (initial_state \<otimes>\<^sub>s ket Map.empty)\<close>
      by (simp flip: cblinfun_apply_cblinfun_compose swap_registers)
    also have \<open>\<dots> = Snd compress *\<^sub>V exec_program_with query (prog @ [program_step]) (initial_state \<otimes>\<^sub>s ket Map.empty)\<close>
      by (simp add: ProgramStep exec_program_with_append)
    finally show ?thesis
      by -
  next
    case (QueryStep X Y)
    with snoc.prems have [register]: \<open>compatible X Y\<close>
      by (simp add: valid_program_def)
    have aux: \<open>(Fst \<circ> X;(Fst \<circ> Y;Snd)) (reg_3_3 compress) = Snd compress\<close>
      by (simp add: reg_3_3_def register_pair_Snd[unfolded o_def, THEN fun_cong])
    have \<open>exec_program_with standard_query (prog @ [program_step]) (initial_state \<otimes>\<^sub>s superpos_total)
          = (Fst \<circ> X;(Fst \<circ> Y;Snd)) standard_query *\<^sub>V Snd compress *\<^sub>V exec_program_with query prog (initial_state \<otimes>\<^sub>s ket Map.empty)\<close>
      by (simp add: QueryStep snoc.IH exec_program_with_append)
    also have \<open>\<dots> = (Fst \<circ> X;(Fst \<circ> Y;Snd)) (standard_query o\<^sub>C\<^sub>L reg_3_3 compress) *\<^sub>V exec_program_with query prog (initial_state \<otimes>\<^sub>s ket Map.empty)\<close>
      by (simp_all add: aux flip: register_mult)
    also have \<open>\<dots> = (Fst \<circ> X;(Fst \<circ> Y;Snd)) (reg_3_3 compress o\<^sub>C\<^sub>L query) *\<^sub>V exec_program_with query prog (initial_state \<otimes>\<^sub>s ket Map.empty)\<close>
      by (simp add: assms)
    also have \<open>\<dots> = Snd compress *\<^sub>V (Fst \<circ> X;(Fst \<circ> Y;Snd)) query *\<^sub>V (exec_program_with query) prog (initial_state \<otimes>\<^sub>s ket Map.empty)\<close>
      by (simp_all add: aux flip: register_mult)
    also have \<open>\<dots> = Snd compress *\<^sub>V (exec_program_with query) (prog @ [program_step]) (initial_state \<otimes>\<^sub>s ket (\<lambda>x. None))\<close>
      by (simp add: QueryStep Cons exec_program_with_append)
    finally show ?thesis
      by -
  qed
qed



lemma (in compressed_oracle) query_is_standard_query_generic:
  fixes query standard_query
  assumes \<open>valid_program program\<close>
  assumes \<open>standard_query o\<^sub>C\<^sub>L reg_3_3 compress = reg_3_3 compress o\<^sub>C\<^sub>L query\<close>
  shows \<open>dist_inv Fst I (exec_program_with standard_query program (initial_state \<otimes>\<^sub>s superpos_total))
       = dist_inv Fst I (exec_program_with query program (initial_state \<otimes>\<^sub>s ket (\<lambda>x. None)))\<close>
proof -
  have \<open>dist_inv Fst I (exec_program_with standard_query program (initial_state \<otimes>\<^sub>s superpos_total))
       = norm (Fst (Proj (- I)) *\<^sub>V Snd compress *\<^sub>V exec_program_with query program (initial_state \<otimes>\<^sub>s ket (\<lambda>x. None)))\<close>
    by (simp add: compress_query_is_standard_query_generic assms dist_inv_def Proj_on_own_range register_projector)
  also have \<open>\<dots> = norm (Snd compress *\<^sub>V Fst (Proj (- I)) *\<^sub>V exec_program_with query program (initial_state \<otimes>\<^sub>s ket (\<lambda>x. None)))\<close>
    by (simp flip: cblinfun_apply_cblinfun_compose swap_registers)
  also have \<open>\<dots> = norm (Fst (Proj (- I)) *\<^sub>V exec_program_with query program (initial_state \<otimes>\<^sub>s ket (\<lambda>x. None)))\<close>
    by (simp add: isometry_preserves_norm register_isometry[where F=Snd])
  also have \<open>\<dots> = dist_inv Fst I (exec_program_with query program (initial_state \<otimes>\<^sub>s ket (\<lambda>x. None)))\<close>
    by (simp add: dist_inv_def Proj_on_own_range register_projector)
  finally show ?thesis
    by -
qed



lemma (in compressed_oracle) query_is_standard_query:
  assumes \<open>valid_program program\<close>
  shows
  \<open>dist_inv Fst I (exec_program_with standard_query program (initial_state \<otimes>\<^sub>s superpos_total)) =
   dist_inv Fst I (exec_program_with query program (initial_state \<otimes>\<^sub>s ket (\<lambda>x. None)))\<close>
  using query_is_standard_query_generic standard_query_compress assms by blast

lemma (in compressed_oracle) query'_is_standard_query:
  assumes \<open>valid_program program\<close>
  shows
  \<open>dist_inv Fst I (exec_program_with standard_query' program (initial_state \<otimes>\<^sub>s superpos_total)) =
   dist_inv Fst I (exec_program_with query' program (initial_state \<otimes>\<^sub>s ket (\<lambda>x. None)))\<close>
  using query_is_standard_query_generic standard_query'_compress assms by blast

lemma (in compressed_oracle) query_is_random_oracle:
  assumes \<open>valid_program program\<close>
  shows \<open>dist_inv_avg id (\<lambda>_. I) (\<lambda>h. exec_program h program initial_state) =
         dist_inv Fst I (exec_program_with query program (initial_state \<otimes>\<^sub>s ket (\<lambda>_. None)))\<close>
  by (simp add: standard_query_is_ro_dist_inv assms query_is_standard_query)


lemma (in compressed_oracle) query'_is_random_oracle:
  assumes \<open>valid_program program\<close>
  shows \<open>dist_inv_avg id (\<lambda>_. I) (\<lambda>h. exec_program h program initial_state) =
         dist_inv Fst I (exec_program_with query' program (initial_state \<otimes>\<^sub>s ket (\<lambda>_. None)))\<close>
  by (simp add: standard_query'_is_ro_dist_inv assms query'_is_standard_query)


lemma (in compressed_oracle) dist_inv_exec_query_exec_fixed:
  fixes program :: \<open>('mem, 'x::finite, 'y::{finite,ab_group_add}) program_step list\<close>
  fixes Q :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2 \<Rightarrow> 'mem ell2 \<Rightarrow>\<^sub>C\<^sub>L 'mem ell2\<close>
  assumes \<open>valid_program program\<close>
  assumes [register]: \<open>register Q\<close>
  shows \<open>dist_inv (Fst \<circ> Q) I (exec_program_with query program (\<psi> \<otimes>\<^sub>s ket (\<lambda>_. None)))
       = dist_inv_avg Q (\<lambda>_. I) (\<lambda>h. exec_program h program \<psi>)\<close>
proof -
  have \<open>dist_inv (Fst \<circ> Q) I (exec_program_with query program (\<psi> \<otimes>\<^sub>s ket (\<lambda>_. None)))
      = dist_inv Fst (lift_invariant Q I) (exec_program_with query program (\<psi> \<otimes>\<^sub>s ket (\<lambda>_. None)))\<close>
    by (metis (no_types, lifting) Proj_lift_invariant assms(2) dist_inv_def lift_invariant_compl o_apply)
  also have \<open>\<dots> = dist_inv_avg id (\<lambda>h. lift_invariant Q I) (\<lambda>h. exec_program h program \<psi>)\<close>
    by (simp add: query_is_random_oracle assms)
  also have \<open>\<dots> = dist_inv_avg Q (\<lambda>_. I) (\<lambda>h. exec_program h program \<psi>)\<close>
    by (simp add: dist_inv_avg_register_rewrite)
  finally show ?thesis
    by -
qed

lemma (in compressed_oracle) dist_inv_exec_query'_exec_fixed:
  fixes program :: \<open>('mem, 'x::finite, 'y::{finite,ab_group_add}) program_step list\<close>
  fixes Q :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2 \<Rightarrow> 'mem ell2 \<Rightarrow>\<^sub>C\<^sub>L 'mem ell2\<close>
  assumes \<open>valid_program program\<close>
  assumes [register]: \<open>register Q\<close>
  shows \<open>dist_inv (Fst \<circ> Q) I (exec_program_with query' program (\<psi> \<otimes>\<^sub>s ket (\<lambda>_. None)))
       = dist_inv_avg Q (\<lambda>_. I) (\<lambda>h. exec_program h program \<psi>)\<close>
proof -
  have \<open>dist_inv (Fst \<circ> Q) I (exec_program_with query' program (\<psi> \<otimes>\<^sub>s ket (\<lambda>_. None)))
      = dist_inv Fst (lift_invariant Q I) (exec_program_with query' program (\<psi> \<otimes>\<^sub>s ket (\<lambda>_. None)))\<close>
    by (metis (no_types, lifting) Proj_lift_invariant assms(2) dist_inv_def lift_invariant_compl o_apply)
  also have \<open>\<dots> = dist_inv_avg id (\<lambda>h. lift_invariant Q I) (\<lambda>h. exec_program h program \<psi>)\<close>
    by (simp add: query'_is_random_oracle assms)
  also have \<open>\<dots> = dist_inv_avg Q (\<lambda>_. I) (\<lambda>h. exec_program h program \<psi>)\<close>
    by (simp add: dist_inv_avg_register_rewrite)
  finally show ?thesis
    by -
qed


end
