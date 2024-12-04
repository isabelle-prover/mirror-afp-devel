section \<open>\<open>Spectral_Theorem\<close> -- The spectral theorem for compact operators\<close>

theory Spectral_Theorem
  imports Compact_Operators Positive_Operators Eigenvalues
begin

subsection \<open>Spectral decomp, compact op\<close>

fun spectral_dec_val :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> nat \<Rightarrow> complex\<close>
  \<comment> \<open>The eigenvalues in the spectral decomposition\<close>
  and spectral_dec_space :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> nat \<Rightarrow> 'a ccsubspace\<close>
  \<comment> \<open>The eigenspaces in the spectral decomposition\<close>
  and spectral_dec_op :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close>
  \<comment> \<open>A sequence of operators mostly for the proof of spectral composition. But see also \<open>spectral_dec_op_spectral_dec_proj\<close> below.\<close>
  where \<open>spectral_dec_val a n = largest_eigenvalue (spectral_dec_op a n)\<close>
  | \<open>spectral_dec_space a n = (if spectral_dec_val a n = 0 then 0 else eigenspace (spectral_dec_val a n) (spectral_dec_op a n))\<close>
  | \<open>spectral_dec_op a (Suc n) = spectral_dec_op a n o\<^sub>C\<^sub>L Proj (- spectral_dec_space a n)\<close>
  | \<open>spectral_dec_op a 0 = a\<close>

definition spectral_dec_proj :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close> where
  \<comment> \<open>Projectors in the spectral decomposition\<close>
  \<open>spectral_dec_proj a n = Proj (spectral_dec_space a n)\<close>

declare spectral_dec_val.simps[simp del]
declare spectral_dec_space.simps[simp del]

lemmas spectral_dec_def = spectral_dec_val.simps
lemmas spectral_dec_space_def = spectral_dec_space.simps

lemma spectral_dec_op_selfadj:
  assumes \<open>selfadjoint a\<close>
  shows \<open>selfadjoint (spectral_dec_op a n)\<close>
proof (induction n)
  case 0
  with assms show ?case
    by simp
next
  case (Suc n)
  define E T where \<open>E = spectral_dec_space a n\<close> and \<open>T = spectral_dec_op a n\<close>
  from Suc have \<open>normal_op T\<close>
    by (auto intro!: selfadjoint_imp_normal simp: T_def)
  then have \<open>reducing_subspace E T\<close>
    by (auto intro!: eigenspace_is_reducing simp: spectral_dec_space_def E_def T_def)
  then have \<open>reducing_subspace (- E) T\<close>
    by simp
  then have *: \<open>Proj (- E) o\<^sub>C\<^sub>L T o\<^sub>C\<^sub>L Proj (- E) = T o\<^sub>C\<^sub>L Proj (- E)\<close>
    by (simp add: invariant_subspace_iff_PAP reducing_subspace_def)
  show ?case
    using Suc
    apply (simp add: flip: T_def E_def * )
    by (simp add: selfadjoint_def adj_Proj cblinfun_compose_assoc)
qed


lemma spectral_dec_op_compact:
  assumes \<open>compact_op a\<close>
  shows \<open>compact_op (spectral_dec_op a n)\<close>
  apply (induction n)
  by (auto intro!: compact_op_comp_left assms)

lemma spectral_dec_val_eigenvalue_of_spectral_dec_op:
  fixes a :: \<open>'a::{chilbert_space, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>spectral_dec_val a n \<in> eigenvalues (spectral_dec_op a n)\<close>
  by (auto intro!: largest_eigenvalue_ex spectral_dec_op_compact spectral_dec_op_selfadj assms
      simp: spectral_dec_def)

lemma spectral_dec_proj_finite_rank: 
  assumes \<open>compact_op a\<close>
  shows \<open>finite_rank (spectral_dec_proj a n)\<close>
  apply (cases \<open>spectral_dec_val a n = 0\<close>)
  by (auto intro!: finite_rank_Proj_finite_dim compact_op_eigenspace_finite_dim spectral_dec_op_compact assms
      simp: spectral_dec_proj_def spectral_dec_space_def)

lemma norm_spectral_dec_op:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>norm (spectral_dec_op a n) = cmod (spectral_dec_val a n)\<close>
  by (simp add: spectral_dec_def cmod_largest_eigenvalue spectral_dec_op_compact spectral_dec_op_selfadj assms)

lemma spectral_dec_op_decreasing_eigenspaces:
  assumes \<open>n \<ge> m\<close> and \<open>e \<noteq> 0\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>eigenspace e (spectral_dec_op a n) \<le> eigenspace e (spectral_dec_op a m)\<close>
proof -
  have *: \<open>eigenspace e (spectral_dec_op a (Suc n)) \<le> eigenspace e (spectral_dec_op a n)\<close> for n
  proof (intro ccsubspace_leI subsetI)
    fix h
    assume asm: \<open>h \<in> space_as_set (eigenspace e (spectral_dec_op a (Suc n)))\<close>
    have \<open>orthogonal_spaces (eigenspace e (spectral_dec_op a (Suc n))) (kernel (spectral_dec_op a (Suc n)))\<close>
      using spectral_dec_op_selfadj[of a \<open>Suc n\<close>] \<open>e \<noteq> 0\<close> \<open>selfadjoint a\<close>
      by (auto intro!: eigenspaces_orthogonal selfadjoint_imp_normal spectral_dec_op_selfadj
          simp: spectral_dec_space_def simp flip: eigenspace_0)
    then have \<open>eigenspace e (spectral_dec_op a (Suc n)) \<le> - kernel (spectral_dec_op a (Suc n))\<close>
      using orthogonal_spaces_leq_compl by blast 
    also have \<open>\<dots> \<le> - spectral_dec_space a n\<close>
      by (auto intro!: ccsubspace_leI kernel_memberI simp: Proj_0_compl)
    finally have \<open>h \<in> space_as_set (- spectral_dec_space a n)\<close>
      using asm by (simp add: Set.basic_monos(7) less_eq_ccsubspace.rep_eq)
    then have \<open>spectral_dec_op a n h = spectral_dec_op a (Suc n) h\<close>
      by (simp add: Proj_fixes_image) 
    also have \<open>\<dots> = e *\<^sub>C h\<close>
      using asm eigenspace_memberD by blast 
    finally show \<open>h \<in> space_as_set (eigenspace e (spectral_dec_op a n))\<close>
      by (simp add: eigenspace_memberI) 
  qed
  define k where \<open>k = n - m\<close>
  from * have \<open>eigenspace e (spectral_dec_op a (m + k)) \<le> eigenspace e (spectral_dec_op a m)\<close>
    by (induction k) (auto simp del: spectral_dec_op.simps intro: order.trans)
  then show ?thesis
    using \<open>n \<ge> m\<close> by (simp add: k_def)
qed

lemma spectral_dec_val_not_not_singleton:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<not> class.not_singleton TYPE('a)\<close>
  shows \<open>spectral_dec_val a n = 0\<close>
proof -
  from assms have \<open>spectral_dec_op a n = 0\<close>
    by (rule not_not_singleton_cblinfun_zero)
  then have \<open>largest_eigenvalue (spectral_dec_op a n) = 0\<close>
    by simp
  then show ?thesis
    by (simp add: spectral_dec_def)
qed

lemma spectral_dec_val_eigenvalue_aux:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Theorem II.5.1\<close>
  fixes a :: \<open>'a::{chilbert_space, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes eigen_neq0: \<open>spectral_dec_val a n \<noteq> 0\<close>
  shows \<open>spectral_dec_val a n \<in> eigenvalues a\<close>
proof -
  define e where \<open>e = spectral_dec_val a n\<close>
  with assms have \<open>e \<noteq> 0\<close>
    by fastforce

  from spectral_dec_op_decreasing_eigenspaces[where m=0 and a=a and n=n, OF _ \<open>e \<noteq> 0\<close> \<open>selfadjoint a\<close>]
  have 1: \<open>eigenspace e (spectral_dec_op a n) \<le> eigenspace e a\<close>
    by simp
  have 2: \<open>spectral_dec_space a n \<noteq> \<bottom>\<close>
  proof -
    have \<open>spectral_dec_val a n \<in> eigenvalues (spectral_dec_op a n)\<close>
      by (simp add: assms(1) assms(2) spectral_dec_val.simps spectral_dec_op_compact spectral_dec_op_selfadj largest_eigenvalue_ex) 
    then show ?thesis
      using \<open>e \<noteq> 0\<close> by (simp add: eigenvalues_def spectral_dec_space.simps e_def)
  qed
  from 1 2 have \<open>eigenspace e a \<noteq> \<bottom>\<close>
    by (auto simp: spectral_dec_space_def bot_unique simp flip: e_def simp: \<open>e \<noteq> 0\<close>)
  then show \<open>e \<in> eigenvalues a\<close>
    by (simp add: eigenvalues_def)
qed

lemma spectral_dec_val_eigenvalue:
  \<comment> \<open>\<^cite>\<open>conway2013course\<close>, Theorem II.5.1\<close>
  fixes a :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes eigen_neq0: \<open>spectral_dec_val a n \<noteq> 0\<close>
  shows \<open>spectral_dec_val a n \<in> eigenvalues a\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  show ?thesis
    using chilbert_space_axioms True assms
    by (rule spectral_dec_val_eigenvalue_aux[internalize_sort' 'a])
next
  case False
  then have \<open>spectral_dec_val a n = 0\<close>
    by (rule spectral_dec_val_not_not_singleton)
  with assms show ?thesis
    by simp
qed

hide_fact spectral_dec_val_eigenvalue_aux

lemma spectral_dec_val_decreasing:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes \<open>n \<ge> m\<close>
  shows \<open>cmod (spectral_dec_val a n) \<le> cmod (spectral_dec_val a m)\<close>
proof -
  have \<open>norm (spectral_dec_op a (Suc n)) \<le> norm (spectral_dec_op a n)\<close> for n
    apply simp
    by (smt (verit) Proj_partial_isometry cblinfun_compose_zero_right mult_cancel_left2 norm_cblinfun_compose norm_le_zero_iff norm_partial_isometry) 
  then have *: \<open>cmod (spectral_dec_val a (Suc n)) \<le> cmod (spectral_dec_val a n)\<close> for n
    by (simp add: cmod_largest_eigenvalue spectral_dec_op_compact assms spectral_dec_op_selfadj spectral_dec_def
        del: spectral_dec_op.simps)
  define k where \<open>k = n - m\<close>
  have \<open>cmod (spectral_dec_val a (m + k)) \<le> cmod (spectral_dec_val a m)\<close>
    apply (induction k arbitrary: m)
     apply simp
    by (metis "*" add_Suc_right order_trans_rules(23)) 
  with \<open>n \<ge> m\<close> show ?thesis
    by (simp add: k_def)
qed


lemma spectral_dec_val_distinct_aux:
  fixes a :: \<open>('a::{chilbert_space, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close>
  assumes \<open>n \<noteq> m\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes neq0: \<open>spectral_dec_val a n \<noteq> 0\<close>
  shows \<open>spectral_dec_val a n \<noteq> spectral_dec_val a m\<close>
proof (rule ccontr)
  assume \<open>\<not> spectral_dec_val a n \<noteq> spectral_dec_val a m\<close>
  then have eq: \<open>spectral_dec_val a n = spectral_dec_val a m\<close>
    by blast
  wlog nm: \<open>n > m\<close> goal False generalizing n m keeping eq neq0
    using hypothesis[of n m] negation assms eq neq0
    by auto
  define e where \<open>e = spectral_dec_val a n\<close>
  with neq0 have \<open>e \<noteq> 0\<close>
    by simp

  have \<open>spectral_dec_space a n \<noteq> \<bottom>\<close>
  proof -
    have \<open>e \<in> eigenvalues (spectral_dec_op a n)\<close>
      by (auto intro!: spectral_dec_val_eigenvalue_of_spectral_dec_op assms simp: e_def)
    then show ?thesis
      by (simp add: spectral_dec_space_def eigenvalues_def e_def neq0)
  qed
  then obtain h where \<open>norm h = 1\<close> and h_En: \<open>h \<in> space_as_set (spectral_dec_space a n)\<close>
    using ccsubspace_contains_unit by blast 
  have T_Sucm_h: \<open>spectral_dec_op a (Suc m) h = 0\<close>
  proof -
    have \<open>spectral_dec_space a n = eigenspace e (spectral_dec_op a n)\<close>
      by (simp add: spectral_dec_space_def e_def neq0)
    also have \<open>\<dots> \<le> eigenspace e (spectral_dec_op a m)\<close>
      using \<open>n > m\<close> \<open>e \<noteq> 0\<close> assms
      by (auto intro!: spectral_dec_op_decreasing_eigenspaces simp: )
    also have \<open>\<dots> = spectral_dec_space a m\<close>
      using neq0 by (simp add: spectral_dec_space_def e_def eq)
    finally have \<open>h \<in> space_as_set (spectral_dec_space a m)\<close>
      using h_En
      by (simp add: basic_trans_rules(31) less_eq_ccsubspace.rep_eq) 
    then show \<open>spectral_dec_op a (Suc m) h = 0\<close>
      by (simp add: Proj_0_compl)
  qed
  have \<open>spectral_dec_op a (Suc m + k) h = 0\<close> if \<open>k \<le> n - m - 1\<close> for k
  proof (insert that, induction k)
    case 0
    from T_Sucm_h show ?case
      by simp
  next
    case (Suc k)
    define mk1 where \<open>mk1 = Suc (m + k)\<close>
    from Suc.prems have \<open>mk1 \<le> n\<close>
      using mk1_def by linarith 
    have \<open>eigenspace e (spectral_dec_op a n) \<le> eigenspace e (spectral_dec_op a mk1)\<close>
      using \<open>mk1 \<le> n\<close> \<open>e \<noteq> 0\<close> \<open>selfadjoint a\<close>
      by (rule spectral_dec_op_decreasing_eigenspaces)
    with h_En have h_mk1: \<open>h \<in> space_as_set (eigenspace e (spectral_dec_op a mk1))\<close>
      by (auto simp: e_def spectral_dec_space_def less_eq_ccsubspace.rep_eq neq0)
    have \<open>Proj (- spectral_dec_space a mk1) *\<^sub>V h = 0 \<or> Proj (- spectral_dec_space a mk1) *\<^sub>V h = h\<close>
    proof (cases \<open>e = spectral_dec_val a mk1\<close>)
      case True
      from h_mk1 have \<open>Proj (- spectral_dec_space a mk1) h = 0\<close>
        using \<open>e \<noteq> 0\<close> by (simp add: Proj_0_compl True spectral_dec_space_def)
      then show ?thesis 
        by simp
    next
      case False
      have \<open>orthogonal_spaces (eigenspace e (spectral_dec_op a mk1)) (spectral_dec_space a mk1)\<close>
        by (simp add: False assms eigenspaces_orthogonal spectral_dec_space.simps spectral_dec_op_selfadj selfadjoint_imp_normal) 
      with h_mk1 have \<open>h \<in> space_as_set (- spectral_dec_space a mk1)\<close>
        using less_eq_ccsubspace.rep_eq orthogonal_spaces_leq_compl by blast 
      then have \<open>Proj (- spectral_dec_space a mk1) h = h\<close>
        by (rule Proj_fixes_image)
      then show ?thesis 
        by simp
    qed
    with Suc show ?case
      by (auto simp: mk1_def)
  qed
  from this[where k=\<open>n - m - 1\<close>]
  have \<open>spectral_dec_op a n h = 0\<close>
    using \<open>n > m\<close>
    by (simp del: spectral_dec_op.simps)
  moreover from h_En have \<open>spectral_dec_op a n h = e *\<^sub>C h\<close>
    by (simp add: neq0 e_def eigenspace_memberD spectral_dec_space_def)
  ultimately show False
    using \<open>norm h = 1\<close> \<open>e \<noteq> 0\<close>
    by force
qed

lemma spectral_dec_val_distinct:
  fixes a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>n \<noteq> m\<close>
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes neq0: \<open>spectral_dec_val a n \<noteq> 0\<close>
  shows \<open>spectral_dec_val a n \<noteq> spectral_dec_val a m\<close>
proof (cases \<open>class.not_singleton TYPE('a)\<close>)
  case True
  show ?thesis
    using chilbert_space_axioms True assms
    by (rule spectral_dec_val_distinct_aux[internalize_sort' 'a])
next
  case False
  then have \<open>spectral_dec_val a n = 0\<close>
    by (rule spectral_dec_val_not_not_singleton)
  with assms show ?thesis
    by simp
qed

hide_fact spectral_dec_val_distinct_aux

lemma spectral_dec_val_tendsto_0:
  (* In the proof of Conway, Functional, Theorem II.5.1 *)
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>spectral_dec_val a \<longlonglongrightarrow> 0\<close>
proof (cases \<open>\<exists>n. spectral_dec_val a n = 0\<close>)
  case True
  then obtain n where \<open>spectral_dec_val a n = 0\<close>
    by auto
  then have \<open>spectral_dec_val a m = 0\<close> if \<open>m \<ge> n\<close> for m
    using spectral_dec_val_decreasing[OF assms that]
    by simp
  then show \<open>spectral_dec_val a \<longlonglongrightarrow> 0\<close>
    by (auto intro!: tendsto_eventually eventually_sequentiallyI)
next
  case False
  define E where \<open>E = spectral_dec_val a\<close>
  from False have \<open>E n \<in> eigenvalues a\<close> for n
    by (simp add: spectral_dec_val_eigenvalue assms E_def)
  then have \<open>eigenspace (E n) a \<noteq> 0\<close> for n
    by (simp add: eigenvalues_def)
  then obtain e where e_E: \<open>e n \<in> space_as_set (eigenspace (E n) a)\<close>
    and norm_e: \<open>norm (e n) = 1\<close> for n
    apply atomize_elim
    using ccsubspace_contains_unit 
    by (auto intro!: choice2)
  then obtain h n where \<open>strict_mono n\<close> and aen_lim: \<open>(\<lambda>j. a (e (n j))) \<longlonglongrightarrow> h\<close>
  proof atomize_elim
    from \<open>compact_op a\<close>
    have compact:\<open>compact (closure (a ` cball 0 1))\<close>
      by (simp add: compact_op_def2)
    from norm_e have \<open>a (e n) \<in> closure (a ` cball 0 1)\<close> for n
      using closure_subset[of \<open>a ` cball 0 1\<close>] by auto
    with compact[unfolded compact_def, rule_format, of \<open>\<lambda>n. a (e n)\<close>]
    show \<open>\<exists>n h. strict_mono n \<and> (\<lambda>j. a (e (n j))) \<longlonglongrightarrow> h\<close>
      by (auto simp: o_def)
  qed
  have ortho_en: \<open>is_orthogonal (e (n j)) (e (n k))\<close> if \<open>j \<noteq> k\<close> for j k
  proof -
    have \<open>n j \<noteq> n k\<close>
      by (simp add: \<open>strict_mono n\<close> strict_mono_eq that)
    then have \<open>E (n j) \<noteq> E (n k)\<close>
      unfolding E_def
      apply (rule spectral_dec_val_distinct)
      using False assms by auto
    then have \<open>orthogonal_spaces (eigenspace (E (n j)) a) (eigenspace (E (n k)) a)\<close>
      apply (rule eigenspaces_orthogonal)
      by (simp add: assms(2) selfadjoint_imp_normal) 
    with e_E show ?thesis
      using orthogonal_spaces_def by blast
  qed
  have aEe: \<open>a (e n) = E n *\<^sub>C e n\<close> for n
    by (simp add: e_E eigenspace_memberD)
  obtain \<alpha> where E_lim: \<open>(\<lambda>n. norm (E n)) \<longlonglongrightarrow> \<alpha>\<close>
    by (rule decseq_convergent[where X=\<open>\<lambda>n. cmod (E n)\<close> and B=0])
       (use spectral_dec_val_decreasing[OF assms] in \<open>auto intro!: simp: decseq_def E_def\<close>)
  then have \<open>\<alpha> \<ge> 0\<close>
    apply (rule LIMSEQ_le_const)
    by simp
  have aen_diff: \<open>norm (a (e (n j)) - a (e (n k))) \<ge> \<alpha> * sqrt 2\<close> if \<open>j \<noteq> k\<close> for j k
  proof -
    from E_lim and spectral_dec_val_decreasing[OF assms, folded E_def]
    have E_geq_\<alpha>: \<open>cmod (E n) \<ge> \<alpha>\<close> for n
      apply (rule_tac decseq_ge[unfolded decseq_def, rotated])
      by auto
    have \<open>(norm (a (e (n j)) - a (e (n k))))\<^sup>2 = (cmod (E (n j)))\<^sup>2 + (cmod (E (n k)))\<^sup>2\<close>
      by (simp add: polar_identity_minus aEe that ortho_en norm_e)
    also have \<open>\<dots> \<ge> \<alpha>\<^sup>2 + \<alpha>\<^sup>2\<close> (is \<open>_ \<ge> \<dots>\<close>)
      apply (rule add_mono)
      using E_geq_\<alpha> \<open>\<alpha> \<ge> 0\<close> by auto
    also have \<open>\<dots> = (\<alpha> * sqrt 2)\<^sup>2\<close>
      by (simp add: algebra_simps)
    finally show ?thesis
      apply (rule power2_le_imp_le)
      by simp
  qed
  have \<open>\<alpha> = 0\<close>
  proof -
    have \<open>\<alpha> * sqrt 2 < \<epsilon>\<close> if \<open>\<epsilon> > 0\<close> for \<epsilon>
    proof -
      from \<open>strict_mono n\<close> have cauchy: \<open>Cauchy (\<lambda>k. a (e (n k)))\<close>
        using LIMSEQ_imp_Cauchy aen_lim by blast
      obtain k where k: \<open>\<forall>m\<ge>k. \<forall>na\<ge>k. dist (a *\<^sub>V e (n m)) (a *\<^sub>V e (n na)) < \<epsilon>\<close>
        apply atomize_elim
        using cauchy[unfolded Cauchy_def, rule_format, OF \<open>\<epsilon> > 0\<close>]
        by simp
      define j where \<open>j = Suc k\<close>
      then have \<open>j \<noteq> k\<close>
        by simp
      from k have \<open>dist (a (e (n j))) (a (e (n k))) < \<epsilon>\<close>
        by (simp add: j_def)
      with aen_diff[OF \<open>j \<noteq> k\<close>] show \<open>\<alpha> * sqrt 2 < \<epsilon>\<close>
        by (simp add: Cauchy_def dist_norm)
    qed
    with \<open>\<alpha> \<ge> 0\<close> show \<open>\<alpha> = 0\<close>
      by (smt (verit) linordered_semiring_strict_class.mult_pos_pos real_sqrt_le_0_iff)
  qed
  with E_lim show ?thesis
    by (auto intro!: tendsto_norm_zero_cancel simp: E_def)
qed

lemma spectral_dec_op_tendsto:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>spectral_dec_op a \<longlonglongrightarrow> 0\<close>
  apply (rule tendsto_norm_zero_cancel)
  using spectral_dec_val_tendsto_0[OF assms]
  apply (simp add: norm_spectral_dec_op assms)
  using tendsto_norm_zero by blast 

lemma spectral_dec_op_spectral_dec_proj:
  \<open>spectral_dec_op a n = a - (\<Sum>i<n. spectral_dec_val a i *\<^sub>C spectral_dec_proj a i)\<close>
proof (induction n)
  case 0
  show ?case
    by simp
next
  case (Suc n)
  have \<open>spectral_dec_op a (Suc n) = spectral_dec_op a n o\<^sub>C\<^sub>L Proj (- spectral_dec_space a n)\<close>
    by simp
  also have \<open>\<dots> = spectral_dec_op a n - spectral_dec_val a n *\<^sub>C spectral_dec_proj a n\<close> (is \<open>?lhs = ?rhs\<close>)
  proof -
    have \<open>?lhs h = ?rhs h\<close> if \<open>h \<in> space_as_set (spectral_dec_space a n)\<close> for h
    proof -
      have \<open>?lhs h = 0\<close>
        by (simp add: Proj_0_compl that) 
      have \<open>spectral_dec_op a n *\<^sub>V h = spectral_dec_val a n *\<^sub>C h\<close>
        by (smt (verit, best) Proj_fixes_image \<open>(spectral_dec_op a n o\<^sub>C\<^sub>L Proj (- spectral_dec_space a n)) *\<^sub>V h = 0\<close> cblinfun_apply_cblinfun_compose complex_vector.scale_eq_0_iff eigenspace_memberD spectral_dec_space.elims kernel_Proj kernel_cblinfun_compose kernel_memberD kernel_memberI ortho_involution that) 
      also have \<open>\<dots> = spectral_dec_val a n *\<^sub>C (spectral_dec_proj a n *\<^sub>V h)\<close>
        by (simp add: Proj_fixes_image spectral_dec_proj_def that) 
      finally
      have \<open>?rhs h = 0\<close>
        by (simp add: cblinfun.diff_left)
      with \<open>?lhs h = 0\<close> show ?thesis
        by simp
    qed
    moreover have \<open>?lhs h = ?rhs h\<close> if \<open>h \<in> space_as_set (- spectral_dec_space a n)\<close> for h
      by (simp add: Proj_0_compl Proj_fixes_image cblinfun.diff_left spectral_dec_proj_def that) 
    ultimately have \<open>?lhs h = ?rhs h\<close> 
      if \<open>h \<in> space_as_set (spectral_dec_space a n \<squnion> - spectral_dec_space a n) \<close> for h
      using that by (rule eq_on_ccsubspaces_sup)
    then show \<open>?lhs = ?rhs\<close>
      by (auto intro!: cblinfun_eqI simp add: )
  qed
  also have \<open>\<dots> = a - (\<Sum>i<Suc n. spectral_dec_val a i *\<^sub>C spectral_dec_proj a i)\<close>
    by (simp add: Suc.IH) 
  finally show ?case
    by -
qed


lemma sequential_tendsto_reorder:
  assumes \<open>inj g\<close>
  assumes \<open>f \<longlonglongrightarrow> l\<close>
  shows \<open>(f o g) \<longlonglongrightarrow> l\<close>
proof (intro lim_explicit[THEN iffD2] impI allI)
  fix S assume \<open>open S\<close> and \<open>l \<in> S\<close>
  with \<open>f \<longlonglongrightarrow> l\<close>
  obtain M where M: \<open>f m \<in> S\<close> if \<open>m \<ge> M\<close> for m
    using tendsto_obtains_N by blast 
  define N where \<open>N = Max (g -` {..<M}) + 1\<close>
  have N: \<open>g n \<ge> M\<close> if \<open>n \<ge> N\<close> for n
  proof -
    from \<open>inj g\<close> have \<open>finite (g -` {..<M})\<close>
      using finite_vimageI by blast 
    then have \<open>N > n\<close> if \<open>n \<in> g -` {..<M}\<close> for n
      using N_def that
      by (simp add: less_Suc_eq_le) 
    then have \<open>N > n\<close> if \<open>g n < M\<close> for n
      by (simp add: that) 
    with that show \<open>g n \<ge> M\<close>
      using linorder_not_less by blast 
  qed
  from N M show \<open>\<exists>N. \<forall>n\<ge>N. (f \<circ> g) n \<in> S\<close>
    by auto
qed





lemma spectral_dec_sums:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>(\<lambda>n. spectral_dec_val a n *\<^sub>C spectral_dec_proj a n)  sums  a\<close>
proof -
  from spectral_dec_op_tendsto[OF assms]
  have \<open>(\<lambda>n. a - spectral_dec_op a n) \<longlonglongrightarrow> a\<close>
    by (simp add: tendsto_diff_const_left_rewrite)
  moreover from spectral_dec_op_spectral_dec_proj[of a]
  have \<open>a - spectral_dec_op a n = (\<Sum>i<n. spectral_dec_val a i *\<^sub>C spectral_dec_proj a i)\<close> for n
    by simp
  ultimately show ?thesis
    by (simp add: sums_def)
qed

lemma spectral_dec_val_real:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>spectral_dec_val a n \<in> \<real>\<close>
  by (metis Reals_0 assms(1) assms(2) eigenvalue_selfadj_real spectral_dec_val_eigenvalue) 


lemma spectral_dec_space_orthogonal:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  assumes \<open>n \<noteq> m\<close>
  shows \<open>orthogonal_spaces (spectral_dec_space a n) (spectral_dec_space a m)\<close>
proof (cases \<open>spectral_dec_val a n = 0 \<or> spectral_dec_val a m = 0\<close>)
  case True
  then show ?thesis
    by (auto intro!: simp: spectral_dec_space_def)
next
  case False
  have \<open>spectral_dec_space a n \<le> eigenspace (spectral_dec_val a n) a\<close>
    using \<open>selfadjoint a\<close>
    by (metis False spectral_dec_space.elims spectral_dec_op.simps(2) spectral_dec_op_decreasing_eigenspaces zero_le) 
  moreover have \<open>spectral_dec_space a m \<le> eigenspace (spectral_dec_val a m) a\<close>
    using \<open>selfadjoint a\<close>
    by (metis False spectral_dec_space.elims spectral_dec_op.simps(2) spectral_dec_op_decreasing_eigenspaces zero_le) 
  moreover have \<open>orthogonal_spaces (eigenspace (spectral_dec_val a n) a) (eigenspace (spectral_dec_val a m) a)\<close>
    apply (intro eigenspaces_orthogonal selfadjoint_imp_normal assms
        spectral_dec_val_distinct)
    using False by simp
  ultimately show ?thesis
    by (meson order.trans orthocomplemented_lattice_class.compl_mono orthogonal_spaces_leq_compl) 
qed

lemma spectral_dec_proj_pos: \<open>spectral_dec_proj a n \<ge> 0\<close>
  by (auto intro!: simp: spectral_dec_proj_def)

lemma
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows spectral_dec_tendsto_pos_op: \<open>(\<lambda>n. max 0 (spectral_dec_val a n) *\<^sub>C spectral_dec_proj a n)  sums  pos_op a\<close>  (is ?thesis1)
    and spectral_dec_tendsto_neg_op: \<open>(\<lambda>n. - min (spectral_dec_val a n) 0 *\<^sub>C spectral_dec_proj a n)  sums  neg_op a\<close>  (is ?thesis2)
proof -
  define I J where \<open>I = {n. spectral_dec_val a n \<ge> 0}\<close>
    and \<open>J = {n. spectral_dec_val a n \<le> 0}\<close>
  define R S where \<open>R = (\<Squnion>n\<in>I. spectral_dec_space a n)\<close>
    and \<open>S = (\<Squnion>n\<in>J. spectral_dec_space a n)\<close>
  define aR aS where \<open>aR = a o\<^sub>C\<^sub>L Proj R\<close> and \<open>aS = - a o\<^sub>C\<^sub>L Proj S\<close>
  have spectral_dec_cases: \<open>(0 < spectral_dec_val a n \<Longrightarrow> P) \<Longrightarrow>
    (spectral_dec_val a n < 0 \<Longrightarrow> P) \<Longrightarrow>
    (spectral_dec_val a n = 0 \<Longrightarrow> P) \<Longrightarrow> P\<close> for n P
    apply atomize_elim
    using reals_zero_comparable[OF spectral_dec_val_real[OF assms, of n]]
    by auto
  have PRP: \<open>spectral_dec_proj a n o\<^sub>C\<^sub>L Proj R = spectral_dec_proj a n\<close> if \<open>n \<in> I\<close> for n
    by (auto intro!: Proj_o_Proj_subspace_left
        simp add: R_def SUP_upper that spectral_dec_proj_def)
  have PR0: \<open>spectral_dec_proj a n o\<^sub>C\<^sub>L Proj R = 0\<close> if \<open>n \<notin> I\<close> for n
    apply (cases rule: spectral_dec_cases[of n])
    using that
    by (auto intro!: orthogonal_spaces_SUP_right spectral_dec_space_orthogonal assms
        simp: spectral_dec_proj_def R_def I_def
        simp flip: orthogonal_projectors_orthogonal_spaces)
  have PSP: \<open>spectral_dec_proj a n o\<^sub>C\<^sub>L Proj S = spectral_dec_proj a n\<close> if \<open>n \<in> J\<close> for n
    by (auto intro!: Proj_o_Proj_subspace_left
        simp add: S_def SUP_upper that spectral_dec_proj_def)
  have PS0: \<open>spectral_dec_proj a n o\<^sub>C\<^sub>L Proj S = 0\<close> if \<open>n \<notin> J\<close> for n
    apply (cases rule: spectral_dec_cases[of n])
    using that
    by (auto intro!: orthogonal_spaces_SUP_right spectral_dec_space_orthogonal assms
        simp: spectral_dec_proj_def S_def J_def
        simp flip: orthogonal_projectors_orthogonal_spaces)
  from spectral_dec_sums[OF assms]
  have \<open>(\<lambda>n. (spectral_dec_val a n *\<^sub>C spectral_dec_proj a n) o\<^sub>C\<^sub>L Proj R) sums aR\<close>
    unfolding aR_def
    apply (rule bounded_linear.sums[rotated])
    by (intro bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_left)
  then have sum_aR: \<open>(\<lambda>n. max 0 (spectral_dec_val a n) *\<^sub>C spectral_dec_proj a n)  sums  aR\<close>
    apply (rule sums_cong[THEN iffD1, rotated])
    by (simp add: I_def PR0 PRP max_def)
  from sum_aR have \<open>aR \<ge> 0\<close>
    apply (rule sums_pos_cblinfun)
    by (auto intro!: spectral_dec_proj_pos scaleC_nonneg_nonneg simp: max_def)
  from spectral_dec_sums[OF assms]
  have \<open>(\<lambda>n. spectral_dec_val a n *\<^sub>C spectral_dec_proj a n o\<^sub>C\<^sub>L Proj S) sums - aS\<close>
    unfolding aS_def minus_minus cblinfun_compose_uminus_left
    apply (rule bounded_linear.sums[rotated])
    by (intro bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_left)
  then have sum_aS': \<open>(\<lambda>n. min (spectral_dec_val a n) 0 *\<^sub>C spectral_dec_proj a n)  sums  - aS\<close>
    apply (rule sums_cong[THEN iffD1, rotated])
    by (simp add: J_def PS0 PSP min_def)
  then have sum_aS: \<open>(\<lambda>n. - min (spectral_dec_val a n) 0 *\<^sub>C spectral_dec_proj a n)  sums  aS\<close>
    using sums_minus by fastforce 
  from sum_aS have \<open>aS \<ge> 0\<close>
    by (rule sums_pos_cblinfun)
       (auto intro!: spectral_dec_proj_pos scaleC_nonpos_nonneg simp: max_def min_def)
  from sum_aR sum_aS'
  have \<open>(\<lambda>n. max 0 (spectral_dec_val a n) *\<^sub>C spectral_dec_proj a n
           + min (spectral_dec_val a n) 0 *\<^sub>C spectral_dec_proj a n) sums (aR - aS)\<close>
    using sums_add by fastforce
  then have \<open>(\<lambda>n. spectral_dec_val a n *\<^sub>C spectral_dec_proj a n) sums (aR - aS)\<close>
  proof (rule sums_cong[THEN iffD1, rotated])
    fix n
    have \<open>max 0 (spectral_dec_val a n) + min (spectral_dec_val a n) 0
          = spectral_dec_val a n\<close>
      apply (cases rule: spectral_dec_cases[of n])
      by (auto intro!: simp: max_def min_def)
    then
    show \<open>max 0 (spectral_dec_val a n) *\<^sub>C spectral_dec_proj a n +
          min (spectral_dec_val a n) 0 *\<^sub>C spectral_dec_proj a n =
          spectral_dec_val a n *\<^sub>C spectral_dec_proj a n\<close>
      by (metis scaleC_left.add) 
  qed
  with spectral_dec_sums[OF assms]
  have \<open>aR - aS = a\<close>
    using sums_unique2 by blast 
  have \<open>aR o\<^sub>C\<^sub>L aS = 0\<close>
    by (metis (no_types, opaque_lifting) Proj_idempotent \<open>0 \<le> aR\<close> \<open>aR - aS = a\<close> aR_def add_cancel_left_left add_minus_cancel adj_0 adj_Proj adj_cblinfun_compose assms(2) cblinfun_compose_minus_right comparable_hermitean lift_cblinfun_comp(2) selfadjoint_def uminus_add_conv_diff) 
  have \<open>aR = pos_op a\<close> and \<open>aS = neg_op a\<close>
    by (intro pos_op_neg_op_unique[where b=aR and c=aS]
        \<open>aR - aS = a\<close> \<open>0 \<le> aR\<close> \<open>0 \<le> aS\<close> \<open>aR o\<^sub>C\<^sub>L aS = 0\<close>)+
  with sum_aR and sum_aS
  show ?thesis1 and ?thesis2
    by auto
qed

lemma  spectral_dec_tendsto_abs_op:
  assumes \<open>compact_op a\<close>
  assumes \<open>selfadjoint a\<close>
  shows \<open>(\<lambda>n. cmod (spectral_dec_val a n) *\<^sub>R spectral_dec_proj a n)  sums  abs_op a\<close>
proof -
  from spectral_dec_tendsto_pos_op[OF assms] spectral_dec_tendsto_neg_op[OF assms]
  have \<open>(\<lambda>n. max 0 (spectral_dec_val a n) *\<^sub>C spectral_dec_proj a n
           + - min (spectral_dec_val a n) 0 *\<^sub>C spectral_dec_proj a n) sums (pos_op a + neg_op a)\<close>
    using sums_add by blast
  then have \<open>(\<lambda>n. cmod (spectral_dec_val a n) *\<^sub>R spectral_dec_proj a n)  sums  (pos_op a + neg_op a)\<close>
    apply (rule sums_cong[THEN iffD1, rotated])
    using spectral_dec_val_real[OF assms]
    apply (simp add: complex_is_Real_iff cmod_def max_def min_def less_eq_complex_def scaleR_scaleC
        flip: scaleC_add_right)
    by (metis complex_surj zero_complex.code) 
  then show ?thesis
    by (simp add: pos_op_plus_neg_op) 
qed

definition spectral_dec_vecs :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> 'a::chilbert_space set\<close> where
  \<open>spectral_dec_vecs a = (\<Union>n. scaleC (csqrt (spectral_dec_val a n)) ` some_onb_of (spectral_dec_space a n))\<close>

lemma spectral_dec_vecs_ortho:
  assumes \<open>selfadjoint a\<close> and \<open>compact_op a\<close>
  shows \<open>is_ortho_set (spectral_dec_vecs a)\<close>
proof (unfold is_ortho_set_def, intro conjI ballI impI)
  show \<open>0 \<notin> spectral_dec_vecs a\<close>
  proof (rule notI)
    assume \<open>0 \<in> spectral_dec_vecs a\<close>
    then obtain n v where v0: \<open>0 = csqrt (spectral_dec_val a n) *\<^sub>C v\<close> and v_in: \<open>v \<in> some_onb_of (spectral_dec_space a n)\<close>
      by (auto simp: spectral_dec_vecs_def)
    from v_in have \<open>v \<noteq> 0\<close>
      using some_onb_of_norm1 by fastforce
    from v_in have \<open>spectral_dec_space a n \<noteq> 0\<close>
      using some_onb_of_0 by force
    then have \<open>spectral_dec_val a n \<noteq> 0\<close>
      by (meson spectral_dec_space.elims)
    with v0 \<open>v \<noteq> 0\<close> show False
      by force
  qed
  fix g h assume g: \<open>g \<in> spectral_dec_vecs a\<close> and h: \<open>h \<in> spectral_dec_vecs a\<close> and \<open>g \<noteq> h\<close>
  from g obtain ng g' where gg': \<open>g = csqrt (spectral_dec_val a ng) *\<^sub>C g'\<close> and g'_in: \<open>g' \<in> some_onb_of (spectral_dec_space a ng)\<close>
    by (auto simp: spectral_dec_vecs_def)
  from h obtain nh h' where hh': \<open>h = csqrt (spectral_dec_val a nh) *\<^sub>C h'\<close> and h'_in: \<open>h' \<in> some_onb_of (spectral_dec_space a nh)\<close>
    by (auto simp: spectral_dec_vecs_def)
  have \<open>is_orthogonal g' h'\<close>
  proof (cases \<open>ng = nh\<close>)
    case True
    with h'_in have \<open>h' \<in> some_onb_of (spectral_dec_space a nh)\<close>
      by simp
    with g'_in True \<open>g \<noteq> h\<close> gg' hh'
    show ?thesis
      using  is_ortho_set_def by fastforce
  next
    case False
    then have \<open>orthogonal_spaces (spectral_dec_space a ng) (spectral_dec_space a nh)\<close>
      by (auto intro!: spectral_dec_space_orthogonal assms simp: )
    with h'_in g'_in show \<open>is_orthogonal g' h'\<close>
      using orthogonal_spaces_ccspan by force
  qed
  then show \<open>is_orthogonal g h\<close>
    by (simp add: gg' hh')
qed

lemma spectral_dec_val_nonneg:
  assumes \<open>a \<ge> 0\<close>
  assumes \<open>compact_op a\<close>
  shows \<open>spectral_dec_val a n \<ge> 0\<close>
proof -
  define v where \<open>v = spectral_dec_val a n\<close>
  wlog non0: \<open>spectral_dec_val a n \<noteq> 0\<close> generalizing v keeping v_def
    using negation by force
  have [simp]: \<open>selfadjoint a\<close>
    using adj_0 assms(1) comparable_hermitean selfadjoint_def by blast
  have \<open>v \<in> eigenvalues a\<close>
    by (auto intro!: non0 spectral_dec_val_eigenvalue assms simp: v_def)
  then show \<open>spectral_dec_val a n \<ge> 0\<close>
    using assms(1) eigenvalues_nonneg v_def by blast
qed

lemma spectral_dec_space_finite_dim[intro]:
  assumes \<open>compact_op a\<close>
  shows \<open>finite_dim_ccsubspace (spectral_dec_space a n)\<close>
  by (auto intro!: compact_op_eigenspace_finite_dim spectral_dec_op_compact assms simp: spectral_dec_space_def)


lemma spectral_dec_space_0:
  assumes \<open>spectral_dec_val a n = 0\<close>
  shows \<open>spectral_dec_space a n = 0\<close>
  by (simp add: assms spectral_dec_space_def)


end