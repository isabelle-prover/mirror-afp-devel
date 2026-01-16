section \<open>\<open>Invariant_Preservation\<close> – Preservation of invariants under queries\<close>

theory Invariant_Preservation
  imports Function_At Misc_Compressed_Oracle
begin

hide_const (open) Order.top
no_notation Order.bottom ("\<bottom>\<index>")
unbundle no m_inv_syntax
unbundle lattice_syntax

subsection \<open>Invariants\<close>


definition \<open>preserves U I J \<epsilon> \<longleftrightarrow> \<epsilon> \<ge> 0 \<and> (\<forall>\<psi>\<in>space_as_set I. norm (U *\<^sub>V \<psi> - Proj J *\<^sub>V U *\<^sub>V \<psi>) \<le> \<epsilon> * norm \<psi>)\<close>
  for U :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>

lemma preserves_def_closure:
  assumes \<open>space_as_set I = closure I'\<close>
  shows \<open>preserves U I J \<epsilon> \<longleftrightarrow> \<epsilon> \<ge> 0 \<and> (\<forall>\<psi>\<in>I'. norm (U *\<^sub>V \<psi> - Proj J *\<^sub>V U *\<^sub>V \<psi>) \<le> \<epsilon> * norm \<psi>)\<close>
proof (rule iffI; (elim conjE)?)
  show \<open>preserves U I J \<epsilon> \<Longrightarrow> 0 \<le> \<epsilon> \<and> (\<forall>\<psi>\<in>I'. norm (U *\<^sub>V \<psi> - Proj J *\<^sub>V U *\<^sub>V \<psi>) \<le> \<epsilon> * norm \<psi>)\<close>
    by (metis assms closure_subset in_mono preserves_def)
  show \<open>preserves U I J \<epsilon>\<close>
    if \<open>0 \<le> \<epsilon>\<close> and bound: \<open>(\<forall>\<psi>\<in>I'. norm (U *\<^sub>V \<psi> - Proj J *\<^sub>V U *\<^sub>V \<psi>) \<le> \<epsilon> * norm \<psi>)\<close>
  proof (unfold preserves_def, intro conjI ballI)
    from that show \<open>\<epsilon> \<ge> 0\<close> by simp
    fix \<psi> assume \<open>\<psi> \<in> space_as_set I\<close>
    with assms have \<open>\<psi> \<in> closure I'\<close>
      by simp
    then obtain \<phi> where \<open>\<phi> \<longlonglongrightarrow> \<psi>\<close> and \<open>\<phi> n \<in> I'\<close> for n
      using closure_sequential by blast
    define f where \<open>f \<xi> = \<epsilon> * norm \<xi> - norm (U *\<^sub>V \<xi> - Proj J *\<^sub>V U *\<^sub>V \<xi>)\<close> for \<xi>
    with \<open>\<phi> _ \<in> I'\<close> bound have bound': \<open>f (\<phi> n) \<ge> 0\<close> for n
      by simp
    have \<open>continuous_on UNIV f\<close>
      unfolding f_def
      by (intro continuous_intros)
    then have \<open>(\<lambda>n. f (\<phi> n)) \<longlonglongrightarrow> f \<psi>\<close>
      using \<open>\<phi> \<longlonglongrightarrow> \<psi>\<close>  apply (rule continuous_on_tendsto_compose[where s=UNIV and f=f])
      by auto
    with bound' have \<open>f \<psi> \<ge> 0\<close>
      by (simp add: Lim_bounded2)
    then show \<open>norm (U *\<^sub>V \<psi> - Proj J *\<^sub>V U *\<^sub>V \<psi>) \<le> \<epsilon> * norm \<psi>\<close>
      by (simp add: f_def)
  qed
qed

lemma preservesI_closure:
  assumes \<open>\<epsilon> \<ge> 0\<close>
  assumes closure: \<open>space_as_set I \<subseteq> closure I'\<close>
  assumes \<open>csubspace I'\<close>
  assumes bound: \<open>\<And>\<psi>. \<psi> \<in> I' \<Longrightarrow> norm \<psi> = 1 \<Longrightarrow> norm (U *\<^sub>V \<psi> - Proj J *\<^sub>V U *\<^sub>V \<psi>) \<le> \<epsilon>\<close>
  shows \<open>preserves U I J \<epsilon>\<close>
proof -
  have *: \<open>space_as_set (ccspan I') = closure I'\<close>
    by (metis assms(3) ccspan.rep_eq complex_vector.span_eq_iff)
  have \<open>preserves U (ccspan I') J \<epsilon>\<close>
  proof (unfold preserves_def_closure[OF *], intro conjI ballI)
    from assms show \<open>\<epsilon> \<ge> 0\<close> by simp

    fix \<psi> assume \<psi>I: \<open>\<psi> \<in> I'\<close>
    show \<open>norm (U *\<^sub>V \<psi> - Proj J *\<^sub>V U *\<^sub>V \<psi>) \<le> \<epsilon> * norm \<psi>\<close>
    proof (cases \<open>\<psi> = 0\<close>)
      case True
      then show ?thesis by auto
    next
      case False
      then have \<open>norm \<psi> > 0\<close>
        by simp
      define \<phi> where \<open>\<phi> = \<psi> /\<^sub>C norm \<psi>\<close>
      from \<psi>I have \<open>\<phi> \<in> I'\<close>
        by (simp add: \<phi>_def \<open>csubspace I'\<close> complex_vector.subspace_scale)
      moreover from False have \<open>norm \<phi> = 1\<close>
        by (simp add: \<phi>_def norm_inverse)
      ultimately have \<open>norm (U *\<^sub>V \<phi> - Proj J *\<^sub>V U *\<^sub>V \<phi>) \<le> \<epsilon>\<close>
        by (rule bound)
      then have \<open>norm (U *\<^sub>V \<psi> - Proj J *\<^sub>V U *\<^sub>V \<psi>) / norm \<psi> \<le> \<epsilon>\<close>
        unfolding \<phi>_def
        by (auto simp flip: scaleC_diff_right
            simp add: norm_inverse divide_inverse_commute cblinfun.scaleC_right)
      with \<open>norm \<psi> > 0\<close> show ?thesis
        by (simp add: divide_le_eq)
    qed
  qed
  then show \<open>preserves U I J \<epsilon>\<close>
    by (smt (verit) "*" closure in_mono preserves_def)
qed


lemma preservesI:
  assumes \<open>\<epsilon> \<ge> 0\<close>
  assumes \<open>\<And>\<psi>. \<psi> \<in> space_as_set I \<Longrightarrow> norm \<psi> = 1 \<Longrightarrow> norm (U *\<^sub>V \<psi> - Proj J *\<^sub>V U *\<^sub>V \<psi>) \<le> \<epsilon>\<close>
  shows \<open>preserves U I J \<epsilon>\<close>
  apply (rule preservesI_closure[where I'=\<open>space_as_set I\<close>])
  using assms by auto

lemma preservesI':
  assumes \<open>\<epsilon> \<ge> 0\<close>
  assumes \<open>\<And>\<psi>. \<psi> \<in> space_as_set I \<Longrightarrow> norm \<psi> = 1 \<Longrightarrow> norm (Proj (-J) *\<^sub>V U *\<^sub>V \<psi>) \<le> \<epsilon>\<close>
  shows \<open>preserves U I J \<epsilon>\<close>
  using \<open>\<epsilon>\<ge>0\<close> apply (rule preservesI)
  apply (frule assms(2))
  by (simp_all add: Proj_ortho_compl cblinfun.diff_left)

lemma preserves_onorm: \<open>preserves U I J \<epsilon> \<longleftrightarrow> norm ((id_cblinfun - Proj J) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I) \<le> \<epsilon>\<close>
proof (rule iffI) 
  assume pres: \<open>preserves U I J \<epsilon>\<close>
  show \<open>norm ((id_cblinfun - Proj J) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I) \<le> \<epsilon>\<close>
  proof (rule norm_cblinfun_bound)
    from pres show \<open>\<epsilon> \<ge> 0\<close>
      by (simp add: preserves_def)
    fix \<psi>
    define \<phi> where \<open>\<phi> = Proj I *\<^sub>V \<psi>\<close>
    have norm\<phi>: \<open>norm \<phi> \<le> norm \<psi>\<close>
      unfolding \<phi>_def apply (rule is_Proj_reduces_norm) by simp

    have \<open>norm (((id_cblinfun - Proj J) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I) *\<^sub>V \<psi>) = norm (U *\<^sub>V \<phi> - Proj J *\<^sub>V U *\<^sub>V \<phi>)\<close>
      unfolding \<phi>_def by (simp add: cblinfun.diff_left)
    also from pres have \<open>\<dots> \<le> \<epsilon> * norm \<phi>\<close>
      by (metis Proj_range \<phi>_def cblinfun_apply_in_image preserves_def)
    also have \<open>\<dots> \<le> \<epsilon> * norm \<psi>\<close>
      by (simp add: \<open>0 \<le> \<epsilon>\<close> mult_left_mono norm\<phi>)
    finally show \<open>norm (((id_cblinfun - Proj J) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I) *\<^sub>V \<psi>) \<le> \<epsilon> * norm \<psi>\<close>
      by -
  qed
next
  assume norm: \<open>norm ((id_cblinfun - Proj J) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I) \<le> \<epsilon>\<close>
  show \<open>preserves U I J \<epsilon>\<close>
  proof (rule preservesI)
    show \<open>\<epsilon> \<ge> 0\<close>
      using norm norm_ge_zero order_trans by blast
    fix \<psi> assume [simp]: \<open>\<psi> \<in> space_as_set I\<close> and [simp]: \<open>norm \<psi> = 1\<close>
    have \<open>norm (U *\<^sub>V \<psi> - Proj J *\<^sub>V U *\<^sub>V \<psi>) = norm ((id_cblinfun - Proj J) *\<^sub>V U *\<^sub>V \<psi>)\<close>
      by (simp add: cblinfun.diff_left)
    also have \<open>\<dots> = norm ((id_cblinfun - Proj J) *\<^sub>V U *\<^sub>V Proj I *\<^sub>V \<psi>)\<close>
      by (simp add: Proj_fixes_image)
    also have \<open>\<dots> = norm (((id_cblinfun - Proj J) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I) *\<^sub>V \<psi>)\<close>
      by simp
    also have \<open>\<dots> \<le> norm ((id_cblinfun - Proj J) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I) * norm \<psi>\<close>
      using norm_cblinfun by blast
    also have \<open>\<dots> \<le> \<epsilon>\<close>
      by (simp add: norm)
    finally show \<open>norm (U *\<^sub>V \<psi> - Proj J *\<^sub>V U *\<^sub>V \<psi>) \<le> \<epsilon>\<close>
      by -
  qed
qed

lemma preserves_cong: 
  assumes \<open>\<And>\<psi>. \<psi> \<in> space_as_set I \<Longrightarrow> U *\<^sub>V \<psi> = U' *\<^sub>V \<psi>\<close>
  shows \<open>preserves U I J \<epsilon> \<longleftrightarrow> preserves U' I J \<epsilon>\<close>
  by (simp add: assms preserves_def)

lemma preserves_mono:
  assumes \<open>preserves U I J \<epsilon>\<close>
  assumes \<open>I \<ge> I'\<close>
  assumes \<open>J \<le> J'\<close>
  assumes \<open>\<epsilon> \<le> \<epsilon>'\<close>
  shows \<open>preserves U I' J' \<epsilon>'\<close>
proof (rule preservesI)
  show \<open>\<epsilon>' \<ge> 0\<close>
    by (smt (verit) assms(1) assms(4) preserves_def)
  fix \<psi> assume \<open>\<psi> \<in> space_as_set I'\<close>
  then have \<open>\<psi> \<in> space_as_set I\<close>
    using \<open>I \<ge> I'\<close> less_eq_ccsubspace.rep_eq by blast
  assume [simp]: \<open>norm \<psi> = 1\<close>

  have \<open>norm (U *\<^sub>V \<psi> - Proj J' *\<^sub>V U *\<^sub>V \<psi>) = norm ((id_cblinfun - Proj J') *\<^sub>V U *\<^sub>V \<psi>)\<close>
    by (simp add: cblinfun.diff_left)
  also have \<open>\<dots> \<le> norm ((id_cblinfun - Proj J) *\<^sub>V U *\<^sub>V \<psi>)\<close>
  proof -
    from \<open>J \<le> J'\<close>
    have \<open>id_cblinfun - Proj J \<ge> id_cblinfun - Proj J'\<close>
      by (simp add: Proj_mono)
    then show ?thesis
      by (metis (no_types, lifting) Proj_fixes_image Proj_ortho_compl Proj_range adj_Proj cblinfun_apply_in_image cdot_square_norm cinner_adj_right cnorm_ge_square less_eq_cblinfun_def)
  qed
  also have \<open>\<dots> = norm (U *\<^sub>V \<psi> - Proj J *\<^sub>V U *\<^sub>V \<psi>)\<close>
    by (simp add: cblinfun.diff_left)
  also from \<open>\<psi> \<in> space_as_set I\<close> \<open>preserves U I J \<epsilon>\<close>
  have \<open>\<dots> \<le> \<epsilon>\<close>
    by (auto simp: preserves_def)
  also have \<open>\<dots> \<le> \<epsilon>'\<close>
    using \<open>\<epsilon> \<le> \<epsilon>'\<close>
    by (simp add: mult_right_mono)
  finally show \<open>norm (U *\<^sub>V \<psi> - Proj J' *\<^sub>V U *\<^sub>V \<psi>) \<le> \<epsilon>'\<close>
    by simp
qed

text \<open>The next lemma allows us to decompose the preservation of an invariant into the preservation
  of simpler invariants. The main requirement is that the simpler invariants are all orthogonal.

  This is in particular useful when one wants to show the preservation of an invariant that
  refers to the oracle input register and other unrelated registers.
  One can then decompose the invariant into many invariants that fix the input and unrelated registers
  to specific computational basis states. (I.e., wlog the input register is in a state of the form \<^term>\<open>ket x\<close>.

  Unfortunately, we have a proof only in the case of finitely many simpler invariants.
  This excludes, e.g., infinite oracle input registers etc. (e.g., quantum ints, quantum lists).\<close>

lemma invariant_splitting:
  fixes X :: \<open>'i set\<close>
  fixes I S :: \<open>'i \<Rightarrow> 'a::chilbert_space ccsubspace\<close>
  fixes J :: \<open>'i \<Rightarrow> 'b::chilbert_space ccsubspace\<close>
  assumes ortho_S: \<open>\<And>x y. x\<in>X \<Longrightarrow> y\<in>X \<Longrightarrow> x \<noteq> y \<Longrightarrow> orthogonal_spaces (S x) (S y)\<close>
  assumes ortho_S': \<open>\<And>x y. x\<in>X \<Longrightarrow> y\<in>X \<Longrightarrow> x \<noteq> y \<Longrightarrow> orthogonal_spaces (S' x) (S' y)\<close>
  assumes IS: \<open>\<And>x. x\<in>X \<Longrightarrow> I x \<le> S x\<close>
  assumes JS': \<open>\<And>x. x\<in>X \<Longrightarrow> J x \<le> S' x\<close>
  assumes USS': \<open>\<And>x. x\<in>X \<Longrightarrow> U *\<^sub>S S x \<le> S' x\<close>
  assumes II: \<open>II \<le> (\<Sum>x\<in>X. I x)\<close>
  assumes JJ: \<open>JJ \<ge> (\<Sum>x\<in>X. J x)\<close>
  assumes \<epsilon>0: \<open>\<epsilon> \<ge> 0\<close>
  assumes [iff]: \<open>finite X\<close>
  assumes pres: \<open>\<And>x. x\<in>X \<Longrightarrow> preserves U (I x) (J x) \<epsilon>\<close>
  shows \<open>preserves U II JJ \<epsilon>\<close>
proof -
  have \<open>preserves U (\<Sum>x\<in>X. I x) (\<Sum>x\<in>X. J x) \<epsilon>\<close>
  proof (rule preservesI_closure[where I'=\<open>(\<Sum>x\<in>X. space_as_set (I x))\<close>])
    from \<epsilon>0 show \<open>\<epsilon> \<ge> 0\<close> by -

    show \<open>csubspace (\<Sum>x\<in>X. space_as_set (I x))\<close>
      by (simp add: csubspace_set_sum)
    show \<open>space_as_set (sum I X) \<subseteq> closure (\<Sum>x\<in>X. space_as_set (I x))\<close>
      apply (rule eq_refl)
      apply (use \<open>finite X\<close> in induction)
      by (auto simp: sup_ccsubspace.rep_eq simp flip: closed_sum_def)

    fix \<psi> assume \<open>\<psi> \<in> (\<Sum>x\<in>X. space_as_set (I x))\<close>
    then obtain \<psi>' where \<psi>'I: \<open>\<psi>' x \<in> space_as_set (I x)\<close> and \<psi>'sum: \<open>\<psi> = (\<Sum>x\<in>X. \<psi>' x)\<close> for x
    proof (atomize_elim, use \<open>finite X\<close> in \<open>induction arbitrary: \<psi>\<close>)
      case empty
      then show ?case 
        by (auto intro!: exI[where x=\<open>\<lambda>_. 0\<close>])
    next
      case (insert x X)
      have aux: \<open>\<psi> \<in> space_as_set (I x) + (\<Sum>x\<in>X. space_as_set (I x)) \<Longrightarrow>
        \<exists>\<psi>0 \<psi>1. \<psi> = \<psi>0 + \<psi>1 \<and> \<psi>0 \<in> (\<Sum>x\<in>X. space_as_set (I x)) \<and> \<psi>1 \<in> space_as_set (I x)\<close>
        by (metis add.commute set_plus_elim)
      from insert.prems
      obtain \<psi>0 \<psi>1 where \<psi>_decomp: \<open>\<psi> = \<psi>0 + \<psi>1\<close> and \<psi>0: \<open>\<psi>0 \<in> (\<Sum>x\<in>X. space_as_set (I x))\<close> and \<psi>1: \<open>\<psi>1 \<in> space_as_set (I x)\<close>
        apply atomize_elim by (auto intro!: aux simp: insert.hyps)
      from insert.IH[OF \<psi>0]
      obtain \<psi>0' where \<psi>0'I: \<open>\<psi>0' x \<in> space_as_set (I x)\<close> and \<psi>0'sum: \<open>\<psi>0 = sum \<psi>0' X\<close> for x
        by auto
      define \<psi>' where \<open>\<psi>' = \<psi>0'(x := \<psi>1)\<close>
      have \<open>\<psi>' x \<in> space_as_set (I x)\<close> for x
        by (simp add: \<psi>'_def \<psi>0'I \<psi>1)
      moreover have \<open>\<psi> = sum \<psi>' (insert x X)\<close>
        by (metis \<psi>'_def \<psi>0'sum \<psi>_decomp add.commute fun_upd_apply insert.hyps(1) insert.hyps(2) sum.cong sum.insert)
      ultimately show ?case
        by auto
    qed

    assume [simp]: \<open>norm \<psi> = 1\<close>

    define \<eta>' \<eta> where \<open>\<eta>' x = U *\<^sub>V (\<psi>' x) - Proj (J x) *\<^sub>V U *\<^sub>V (\<psi>' x)\<close> and \<open>\<eta> = (\<Sum>x\<in>X. \<eta>' x)\<close> for x
    with pres have \<eta>'bound: \<open>norm (\<eta>' x) \<le> \<epsilon> * norm (\<psi>' x)\<close> if \<open>x\<in>X\<close> for x
      using that by (simp add: \<psi>'I preserves_def)
    define US where \<open>US x = U *\<^sub>S S x\<close> for x
 
    have \<open>\<psi>' x \<in> space_as_set (S x)\<close> if \<open>x\<in>X\<close> for x
      using that \<psi>'I IS less_eq_ccsubspace.rep_eq by blast
    then have U\<psi>'S': \<open>U *\<^sub>V \<psi>' x \<in> space_as_set (S' x)\<close> if \<open>x\<in>X\<close> for x
      using USS'[OF that] that
      by (metis cblinfun_image.rep_eq closure_subset imageI in_mono less_eq_ccsubspace.rep_eq)

    have \<eta>'S': \<open>\<eta>' x \<in> space_as_set (S' x)\<close> if \<open>x\<in>X\<close> for x
    proof -
      have \<open>Proj (J x) *\<^sub>V U *\<^sub>V (\<psi>' x) \<in> space_as_set (J x)\<close>
        by (metis Proj_range cblinfun_apply_in_image)
      also have \<open>\<dots> \<subseteq> space_as_set (S' x)\<close>
        unfolding US_def less_eq_ccsubspace.rep_eq[symmetric] using JS' that by auto
      finally have *: \<open>Proj (J x) *\<^sub>V U *\<^sub>V (\<psi>' x) \<in> space_as_set (S' x)\<close>
        by -
      with U\<psi>'S'[OF that]
      show \<open>\<eta>' x \<in> space_as_set (S' x)\<close>
        unfolding \<eta>'_def
        by (metis Proj_fixes_image Proj_range cblinfun.diff_right cblinfun_apply_in_image)
    qed
    from ortho_S' USS'
    have ortho_US: \<open>orthogonal_spaces (US x) (US y)\<close> if \<open>x \<noteq> y\<close> and \<open>x\<in>X\<close> and \<open>y\<in>X\<close> for x y
      by (metis US_def in_mono less_eq_ccsubspace.rep_eq orthogonal_spaces_def
          that(1,2,3))
    have ortho_I: \<open>orthogonal_spaces (I x) (I y)\<close> if \<open>x \<noteq> y\<close> and \<open>x\<in>X\<close> and \<open>y\<in>X\<close> for x y
      by (meson IS less_eq_ccsubspace.rep_eq ortho_S orthogonal_spaces_def subsetD that)
    have ortho_J: \<open>orthogonal_spaces (J x) (J y)\<close> if \<open>x \<noteq> y\<close> and \<open>x\<in>X\<close> and \<open>y\<in>X\<close> for x y
      using JS' ortho_S' that
      by (meson less_eq_ccsubspace.rep_eq orthogonal_spaces_def subsetD)

    from ortho_S' \<eta>'S'
    have \<eta>'ortho: \<open>is_orthogonal (\<eta>' x) (\<eta>' y)\<close> if \<open>x \<noteq> y\<close> and \<open>x\<in>X\<close> and \<open>y\<in>X\<close> for x y
      by (meson orthogonal_spaces_def that)
    have \<psi>'ortho: \<open>is_orthogonal (\<psi>' x) (\<psi>' y)\<close> if \<open>x \<noteq> y\<close> and \<open>x\<in>X\<close> and \<open>y\<in>X\<close> for x y
      using \<psi>'I ortho_I orthogonal_spaces_def that by blast

    have \<eta>'2: \<open>\<eta>' x = U *\<^sub>V \<psi>' x - Proj (\<Sum>x\<in>X. (J x)) *\<^sub>V U *\<^sub>V \<psi>' x\<close> if \<open>x \<in> X\<close> for x
    proof -
      have \<open>Proj (J y) *\<^sub>V U *\<^sub>V \<psi>' x = 0\<close> if \<open>x \<noteq> y\<close> and \<open>y \<in> X\<close> for y
      proof -
        have \<open>U *\<^sub>V \<psi>' x \<in> space_as_set (S' x)\<close>
          using \<open>x \<in> X\<close> by (rule U\<psi>'S')
        moreover have \<open>orthogonal_spaces (S' x) (J y)\<close>
          using JS'[OF \<open>y\<in>X\<close>] ortho_S'[OF \<open>x\<in>X\<close> \<open>y\<in>X\<close> \<open>x\<noteq>y\<close>]
          by (meson less_eq_ccsubspace.rep_eq orthogonal_spaces_def subset_eq)
        ultimately show ?thesis
          by (metis (no_types, opaque_lifting) Proj_fixes_image Proj_ortho_compl Proj_range Set.basic_monos(7) cancel_comm_monoid_add_class.diff_cancel cblinfun.diff_left cblinfun.diff_right cblinfun_apply_in_image id_cblinfun.rep_eq less_eq_ccsubspace.rep_eq orthogonal_spaces_leq_compl)
      qed
      then have \<open>\<eta>' x = U *\<^sub>V \<psi>' x - Proj (J x) *\<^sub>V U *\<^sub>V \<psi>' x - (\<Sum>y\<in>X-{x}. Proj (J y) *\<^sub>V U *\<^sub>V \<psi>' x)\<close>
        unfolding \<eta>'_def
        by (metis (no_types, lifting) DiffE Diff_insert_absorb diff_0_right mk_disjoint_insert sum.not_neutral_contains_not_neutral)
      also have \<open>\<dots> = U *\<^sub>V \<psi>' x - (\<Sum>y\<in>X. Proj (J y) *\<^sub>V U *\<^sub>V \<psi>' x)\<close>
        apply (subst (2) asm_rl[of \<open>X = {x} \<union> (X-{x})\<close>])
         apply (simp add: insert_absorb \<open>x \<in> X\<close>)
        apply (subst sum.union_disjoint)
        by auto
      also have \<open>\<dots> = U *\<^sub>V \<psi>' x - (\<Sum>y\<in>X. Proj (J y)) *\<^sub>V U *\<^sub>V \<psi>' x\<close>
        by (simp add: cblinfun.sum_left)
      also have \<open>\<dots> = U *\<^sub>V \<psi>' x - Proj (\<Sum>y\<in>X. J y) *\<^sub>V U *\<^sub>V \<psi>' x\<close>
        apply (subst Proj_sum_spaces)
        using ortho_J by auto
      finally show ?thesis
        by -
    qed

    have \<open>norm (U *\<^sub>V \<psi> - Proj (sum J X) *\<^sub>V U *\<^sub>V \<psi>) = norm (\<Sum>x\<in>X. U *\<^sub>V \<psi>' x - Proj (sum J X) *\<^sub>V U *\<^sub>V \<psi>' x)\<close>
      by (simp add: \<psi>'sum sum_subtractf cblinfun.sum_right)
    also from \<eta>'2 have \<open>\<dots> = norm (\<Sum>x\<in>X. \<eta>' x)\<close>
      by simp
    also have \<open>\<dots> = norm \<eta>\<close>
      using \<eta>_def by blast
    also have \<open>(norm \<eta>)\<^sup>2 = (\<Sum>x\<in>X. (norm (\<eta>' x))\<^sup>2)\<close>
      unfolding \<eta>_def
      apply (rule pythagorean_theorem_sum)
      using \<eta>'ortho by auto
    also have \<open>\<dots> \<le> (\<Sum>x\<in>X. (\<epsilon> * norm (\<psi>' x))\<^sup>2)\<close>
      apply (rule sum_mono)
      by (simp add: \<eta>'bound power_mono)
    also have \<open>\<dots> \<le> \<epsilon>\<^sup>2 * (\<Sum>x\<in>X. (norm (\<psi>' x))\<^sup>2)\<close>
      by (simp add: sum_distrib_left power_mult_distrib)
    also have \<open>\<dots> = \<epsilon>\<^sup>2 * (norm \<psi>)\<^sup>2\<close>
    proof -
      have aux: \<open>a \<in> X \<Longrightarrow> a' \<in> X \<Longrightarrow> a \<noteq> a' \<Longrightarrow> \<psi> = sum \<psi>' X \<Longrightarrow> is_orthogonal (\<psi>' a) (\<psi>' a')\<close> for a a'
        by (meson \<psi>'I IS less_eq_ccsubspace.rep_eq ortho_S orthogonal_spaces_def subset_iff)
      show ?thesis
      apply (subst pythagorean_theorem_sum[symmetric])
        using \<psi>'sum aux by auto
    qed
    finally show \<open>norm (U *\<^sub>V \<psi> - Proj (sum J X) *\<^sub>V U *\<^sub>V \<psi>) \<le> \<epsilon>\<close>
      using \<open>\<epsilon>\<ge>0\<close> \<open>norm \<psi> = 1\<close> by (auto simp flip: power_mult_distrib)
  qed
  then show ?thesis
    apply (rule preserves_mono)
    using assms by auto
qed

text \<open>An invariant that is consists of all states that are the superposition of computational basis states.

Useful for representing a classically formulated condition (e.g., \<^term>\<open>x \<noteq> 0\<close>) as an invariant (\<^term>\<open>ket_invariant {x. x\<noteq>0}\<close>).\<close>

definition \<open>ket_invariant M = ccspan (ket ` M)\<close>

lemma ket_invariant_UNIV[simp]: \<open>ket_invariant UNIV = \<top>\<close>
  unfolding ket_invariant_def by simp

lemma ket_invariant_empty[simp]: \<open>ket_invariant {} = \<bottom>\<close>
  unfolding ket_invariant_def by simp

lemma ket_invariant_Rep_ell2: \<open>\<psi> \<in> space_as_set (ket_invariant I) \<longleftrightarrow> (\<forall>i\<in>-I. Rep_ell2 \<psi> i = 0)\<close>
  by (simp add: ket_invariant_def space_ccspan_ket) 

lemma ket_invariant_compl: \<open>ket_invariant (-M) = - ket_invariant M\<close>
proof -
  have \<open>ket_invariant (-M) \<le> - ket_invariant M\<close> for M :: \<open>'a set\<close>
    unfolding ket_invariant_def
    apply (rule ccspan_leq_ortho_ccspan) 
    by auto
  moreover have \<open>- ket_invariant M \<le> ket_invariant (-M)\<close>
  proof (rule ccsubspace_leI_unit)
    fix \<psi>
    assume \<open>\<psi> \<in> space_as_set (- ket_invariant M)\<close>
    then have \<open>is_orthogonal \<psi> \<phi>\<close> if \<open>\<phi> \<in> space_as_set (ket_invariant M)\<close> for \<phi>
      using that
      by (auto simp: uminus_ccsubspace.rep_eq orthogonal_complement_def)
    then have \<open>is_orthogonal (ket m) \<psi>\<close> if \<open>m \<in> M\<close> for m
      by (simp add: ccspan_superset' is_orthogonal_sym ket_invariant_def that)
    then have \<open>Rep_ell2 \<psi> m = 0\<close> if \<open>m \<in> M\<close> for m
      by (simp add: cinner_ket_left that)
    then show \<open>\<psi> \<in> space_as_set (ket_invariant (- M))\<close>
      unfolding ket_invariant_Rep_ell2
      by simp
  qed
  ultimately show ?thesis
    by (rule order.antisym)
qed

lemma ket_invariant_tensor: \<open>ket_invariant I \<otimes>\<^sub>S ket_invariant J = ket_invariant (I \<times> J)\<close>
proof -
  have \<open>ket_invariant I \<otimes>\<^sub>S ket_invariant J = ccspan {x \<otimes>\<^sub>s y |x y. x \<in> ket ` I \<and> y \<in> ket ` J}\<close>
    by (simp add: tensor_ccsubspace_ccspan ket_invariant_def)
  also have \<open>\<dots> = ccspan {ket (x, y)| x y. x \<in> I \<and> y \<in> J}\<close>
    by (auto intro!: arg_cong[where f=ccspan] simp flip: tensor_ell2_ket)
  also have \<open>\<dots> = ccspan (ket ` (I \<times> J))\<close>
    by (auto intro!: arg_cong[where f=ccspan])
  also have \<open>\<dots> = ket_invariant (I \<times> J)\<close>
    by (simp add: ket_invariant_def)
  finally show ?thesis
    by -
qed


abbreviation \<open>preserves_ket U I J \<epsilon> \<equiv> preserves U (ket_invariant I) (ket_invariant J) \<epsilon>\<close>

lemma orthogonal_spaces_ket[simp]: \<open>orthogonal_spaces (ket_invariant M) (ket_invariant N) \<longleftrightarrow> M \<inter> N = {}\<close> for M N
  apply rule
  apply (simp add: ket_invariant_def orthogonal_spaces_def)
  apply (metis Int_emptyI ccspan_superset imageI inf_commute ket_invariant_def orthogonal_ket subset_iff)
  apply (simp add: orthogonal_spaces_leq_compl ket_invariant_def)
  by (smt (verit, best) ccspan_leq_ortho_ccspan disjoint_iff_not_equal imageE orthogonal_ket)

lemma ket_invariant_le[simp]: \<open>ket_invariant M \<le> ket_invariant N \<longleftrightarrow> M \<subseteq> N\<close> for M N
proof -
  have \<open>x \<in> N\<close> 
    if \<open>x \<in> M\<close> and *: \<open>\<And>\<psi>. (\<forall>y. y \<notin> M \<longrightarrow> Rep_ell2 \<psi> y = 0) \<longrightarrow> (\<forall>y. y \<notin> N \<longrightarrow> Rep_ell2 \<psi> y = 0)\<close> for x
    using *[of \<open>ket x\<close>]
    using \<open>x \<in> M \<close> by (auto simp: ket.rep_eq)
  then show ?thesis
    by (auto simp add: less_eq_ccsubspace.rep_eq subset_eq Ball_def ket_invariant_Rep_ell2) 
qed

lemma ket_invariant_mono:
  assumes \<open>I \<subseteq> J\<close>
  shows \<open>ket_invariant I \<le> ket_invariant J\<close>
  using [[simp_trace]]
  by (simp add: assms)

lemma ket_invariant_Inf: \<open>ket_invariant (Inf M) = Inf (ket_invariant ` M)\<close>
proof (rule order.antisym)
  show \<open>ket_invariant (\<Inter> M) \<le> Inf (ket_invariant ` M)\<close>
    by (simp add: Inf_lower le_Inf_iff)
  show \<open>Inf (ket_invariant ` M) \<le> ket_invariant (\<Inter> M)\<close>
  proof (rule ccsubspace_leI_unit)
    fix \<psi>
    assume \<open>\<psi> \<in> space_as_set (Inf (ket_invariant ` M))\<close>
    then have \<open>\<psi> \<in> space_as_set (ket_invariant N)\<close> if \<open>N \<in> M\<close> for N
      by (metis Inf_lower imageI in_mono less_eq_ccsubspace.rep_eq that)
    then have \<open>Rep_ell2 \<psi> n = 0\<close> if \<open>n \<notin> N\<close> and \<open>N \<in> M\<close> for n N
      using that by (auto simp: ket_invariant_Rep_ell2)
    then have \<open>Rep_ell2 \<psi> n = 0\<close> if \<open>n \<notin> Inf M\<close> for n
      using that by blast
    then show \<open>\<psi> \<in> space_as_set (ket_invariant (\<Inter> M))\<close>
      by (meson ComplD ket_invariant_Rep_ell2)
  qed
qed
    

lemma ket_invariant_INF: \<open>ket_invariant (INF x\<in>M. f x) = (INF x\<in>M. ket_invariant (f x))\<close>
  by (simp add: image_image ket_invariant_Inf)


lemma ket_invariant_Sup: \<open>ket_invariant (Sup M) = Sup (ket_invariant ` M)\<close>
proof -
  have \<open>ket_invariant (Sup M) = ket_invariant (- (Inf (uminus ` M)))\<close>
    by (subst uminus_Inf, simp)
  also have \<open>\<dots> = - ket_invariant (Inf (uminus ` M))\<close>
    using ket_invariant_compl by blast
  also have \<open>\<dots> = - Inf (ket_invariant ` uminus ` M)\<close>
    using ket_invariant_Inf by auto
  also have \<open>\<dots> = - Inf (uminus ` ket_invariant ` M)\<close>
    by (metis (no_types, lifting) INF_cong image_image ket_invariant_compl)
  also have \<open>\<dots> = Sup (ket_invariant ` M)\<close>
    apply (subst uminus_Inf)
    by (metis (no_types, lifting) SUP_cong image_comp image_image o_apply ortho_involution)
  finally show ?thesis
    by -
qed

lemma ket_invariant_SUP: \<open>ket_invariant (SUP x\<in>M. f x) = (SUP x\<in>M. ket_invariant (f x))\<close>
  by (simp add: image_image ket_invariant_Sup)

lemma ket_invariant_inter: \<open>ket_invariant M \<sqinter> ket_invariant N = ket_invariant (M \<inter> N)\<close> for M N
  using ket_invariant_INF[where M=UNIV and f=\<open>\<lambda>x. if x then M else N\<close>]
  by (smt (verit) INF_UNIV_bool_expand)

lemma ket_invariant_union: \<open>ket_invariant M \<squnion> ket_invariant N = ket_invariant (M \<union> N)\<close> for M N
  using ket_invariant_SUP[where M=UNIV and f=\<open>\<lambda>x. if x then M else N\<close>]
  by (smt (verit) SUP_UNIV_bool_expand)

lemma sum_ket_invariant[simp]:
  assumes \<open>finite X\<close>
  shows \<open>(\<Sum>x\<in>X. ket_invariant (M x)) = ket_invariant (\<Union>x\<in>X. M x)\<close>
  using assms apply induction
  apply auto using ket_invariant_union by blast

lemma ket_invariant_inj[simp]:
  \<open>ket_invariant M = ket_invariant N \<longleftrightarrow> M = N\<close> for M N
  by (metis dual_order.eq_iff ket_invariant_le)

text \<open>Given an invariant on the content of a register, this gives the corresponding invariant 
  on the whole state. Useful for plugging together several invariants on different subsystems.\<close>

definition \<open>lift_invariant F I = F (Proj I) *\<^sub>S \<top>\<close>

lemma lift_invariant_comp: 
  assumes [simp]:  \<open>register G\<close>
  shows \<open>lift_invariant (F o G) = lift_invariant F o lift_invariant G\<close>
  by (auto intro!: ext simp: lift_invariant_def Proj_on_own_range register_projector)

lemma lift_invariant_top[simp]: \<open>register F \<Longrightarrow> lift_invariant F \<top> = \<top>\<close>
  by (metis Proj_on_own_range' cblinfun_compose_id_right id_cblinfun_adjoint lift_invariant_def register_unitary unitary_id unitary_range)

lemma Proj_lift_invariant: \<open>register F \<Longrightarrow> Proj (lift_invariant F I) = F (Proj I)\<close>
  using [[simproc del: Laws_Quantum.compatibility_warn]]
  unfolding lift_invariant_def
  by (simp add: Proj_on_own_range register_projector) 

lemma ket_invariant_image_assoc: 
  \<open>ket_invariant ((\<lambda>((a, b), c). (a, b, c)) ` X) = lift_invariant assoc (ket_invariant X)\<close>
proof -
  have \<open>ket_invariant ((\<lambda>((a, b), c). (a, b, c)) ` X) = assoc_ell2 *\<^sub>S ket_invariant X\<close>
    by (auto intro!: arg_cong[where f=ccspan] image_eqI simp add: ket_invariant_def image_image cblinfun_image_ccspan)
  also have \<open>\<dots> = lift_invariant assoc (ket_invariant X)\<close>
    by (simp add: lift_invariant_def assoc_ell2_sandwich Proj_sandwich)
  finally show ?thesis
    by -
qed

lemma lift_invariant_inj[simp]: \<open>lift_invariant F I = lift_invariant F J \<longleftrightarrow> I = J\<close> if [register]: \<open>register F\<close>
proof (rule iffI[rotated], simp)
  assume asm: \<open>lift_invariant F I = lift_invariant F J\<close>
  then have \<open>F (Proj I) *\<^sub>S \<top> = F (Proj J) *\<^sub>S \<top>\<close>
    by (simp add: lift_invariant_def)
  then have \<open>F (Proj I) = F (Proj J)\<close>
    by (metis Proj_lift_invariant asm that)
  then have \<open>Proj I = Proj J\<close>
    by (simp add: register_inj')
  then show \<open>I = J\<close>
    using Proj_inj by blast
qed

lemma lift_invariant_decomp:
  fixes U :: \<open>_ \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space\<close>
  assumes \<open>\<And>\<theta>. F \<theta> = sandwich U *\<^sub>V (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
  assumes \<open>unitary U\<close>
  shows \<open>lift_invariant F I = U *\<^sub>S (I \<otimes>\<^sub>S \<top>)\<close>
  by (simp add: lift_invariant_def assms Proj_tensor_Proj Proj_sandwich flip: Proj_top)

text \<open>Invariants are compatible if their projectors commute, i.e., if you can simultaneously measure them.
  This can happen if they refer to different parts of the system. (E.g., one talks about register X,
  the other about register Y.) But also for example for any ket-invariants.

  See lemma \<open>preserves_intersect\<close> below for a useful consequence.\<close>

definition \<open>compatible_invariants A B \<longleftrightarrow> Proj A o\<^sub>C\<^sub>L Proj B = Proj B o\<^sub>C\<^sub>L Proj A\<close>

lemma compatible_invariants_inter: \<open>Proj A o\<^sub>C\<^sub>L Proj B = Proj (A \<sqinter> B)\<close> if \<open>compatible_invariants A B\<close>
proof -
  have \<open>is_Proj (Proj A o\<^sub>C\<^sub>L Proj B)\<close>
    apply (rule is_Proj_I)
    apply (metis Proj_idempotent cblinfun_assoc_left(1) compatible_invariants_def that)
    by (metis adj_Proj adj_cblinfun_compose compatible_invariants_def that)

  have \<open>(Proj A o\<^sub>C\<^sub>L Proj B) *\<^sub>S \<top> \<le> A\<close>
    by (simp add: Proj_image_leq cblinfun_compose_image)
  moreover have \<open>(Proj A o\<^sub>C\<^sub>L Proj B) *\<^sub>S \<top> \<le> B\<close>
    using that by (simp add: Proj_image_leq cblinfun_compose_image compatible_invariants_def)
  ultimately have leq1: \<open>(Proj A o\<^sub>C\<^sub>L Proj B) *\<^sub>S \<top> \<le> A \<sqinter> B\<close>
    by auto

  have leq2: \<open>A \<sqinter> B \<le> (Proj A o\<^sub>C\<^sub>L Proj B) *\<^sub>S \<top>\<close>
  proof (rule ccsubspace_leI, rule subsetI)
    fix \<psi> assume \<open>\<psi> \<in> space_as_set (A \<sqinter> B)\<close>
    then have \<open>Proj A *\<^sub>V \<psi> = \<psi>\<close> \<open>Proj B *\<^sub>V \<psi> = \<psi>\<close>
      by (simp_all add: Proj_fixes_image)
    then have \<open>\<psi> = (Proj A o\<^sub>C\<^sub>L Proj B) *\<^sub>V \<psi>\<close>
      by simp
    also have \<open>(Proj A o\<^sub>C\<^sub>L Proj B) *\<^sub>V \<psi> \<in> space_as_set ((Proj A o\<^sub>C\<^sub>L Proj B) *\<^sub>S \<top>)\<close>
      using cblinfun_apply_in_image by blast
    finally show \<open>\<psi> \<in> space_as_set ((Proj A o\<^sub>C\<^sub>L Proj B) *\<^sub>S \<top>)\<close>
      by -
  qed

  from leq1 leq2 have \<open>(Proj A o\<^sub>C\<^sub>L Proj B) *\<^sub>S \<top> = A \<sqinter> B\<close>
    using order_class.order_eq_iff by blast

  with \<open>is_Proj (Proj A o\<^sub>C\<^sub>L Proj B)\<close> show \<open>Proj A o\<^sub>C\<^sub>L Proj B = Proj (A \<sqinter> B)\<close>
    using Proj_on_own_range by force
qed

lemma compatible_invariants_ket[iff]: \<open>compatible_invariants (ket_invariant I) (ket_invariant J)\<close>
proof -
  have I: \<open>Proj (ket_invariant I) = Proj (ket_invariant (I-J)) + Proj (ket_invariant (I\<inter>J))\<close>
    apply (subst Proj_sup[symmetric])
    by (auto simp add: Un_Diff_Int ket_invariant_union)
  have J: \<open>Proj (ket_invariant J) = Proj (ket_invariant (J-I)) + Proj (ket_invariant (I\<inter>J))\<close>
    apply (subst Proj_sup[symmetric])
    by (auto intro!: arg_cong[where f=Proj] simp add: Un_Diff_Int ket_invariant_union)
  have \<open>Proj (ket_invariant I) o\<^sub>C\<^sub>L Proj (ket_invariant J) = Proj (ket_invariant J) o\<^sub>C\<^sub>L Proj (ket_invariant I)\<close>
    apply (simp add: I J)
    by (smt (verit) Diff_disjoint I Int_Diff_disjoint Proj_bot adj_Proj adj_cblinfun_compose cblinfun_compose_add_left cblinfun_compose_add_right orthogonal_projectors_orthogonal_spaces orthogonal_spaces_ket)
  then show ?thesis
    by (simp add: compatible_invariants_def)
qed

lemma preserves_intersect:
  assumes \<open>compatible_invariants J1 J2\<close>
  assumes pres1: \<open>preserves U I J1 \<epsilon>1\<close>
  assumes pres2: \<open>preserves U I J2 \<epsilon>2\<close>
  shows \<open>preserves U I (J1 \<sqinter> J2) (\<epsilon>1 + \<epsilon>2)\<close>
(* TODO: can be improved to "sqrt (e1^2 + e2^2)" *)
proof (rule preservesI)
  show \<open>0 \<le> \<epsilon>1 + \<epsilon>2\<close>
    by (meson add_nonneg_nonneg pres1 pres2 preserves_def)

  fix \<psi> assume \<open>\<psi> \<in> space_as_set I\<close> and \<open>norm \<psi> = 1\<close>
  define \<phi> J where \<open>\<phi> = U *\<^sub>V \<psi>\<close> and \<open>J = J1 \<sqinter> J2\<close>

  note norm_diff_triangle_le[trans]

  from pres1
  have \<open>norm (\<phi> - Proj J1 *\<^sub>V \<phi>) \<le> \<epsilon>1\<close>
    by (metis \<open>\<psi> \<in> space_as_set I\<close> \<open>norm \<psi> = 1\<close> \<phi>_def mult_cancel_left1 preserves_def)
  also 
  have \<open>norm (\<phi> - Proj J2 *\<^sub>V \<phi>) \<le> \<epsilon>2\<close>
    using \<open>\<psi> \<in> space_as_set I\<close> \<open>norm \<psi> = 1\<close> \<phi>_def pres2 preserves_def by force
  then have \<open>norm (Proj J1 *\<^sub>V (\<phi> - Proj J2 *\<^sub>V \<phi>)) \<le> \<epsilon>2\<close>
    using Proj_is_Proj is_Proj_reduces_norm order_trans by blast
  then have \<open>norm (Proj J1 *\<^sub>V \<phi> - Proj J1 *\<^sub>V Proj J2 *\<^sub>V \<phi>) \<le> \<epsilon>2\<close>
    by (simp add: cblinfun.diff_right)
  also have \<open>Proj J1 *\<^sub>V Proj J2 *\<^sub>V \<phi> = Proj J *\<^sub>V \<phi>\<close>
    by (metis J_def assms(1) cblinfun_apply_cblinfun_compose compatible_invariants_inter)
  finally show \<open>norm (\<phi> - Proj J *\<^sub>V \<phi>) \<le> \<epsilon>1 + \<epsilon>2\<close>
    by -
qed

lemma preserves_intersect_ket:
  assumes \<open>preserves_ket U I J1 \<epsilon>1\<close>
  assumes \<open>preserves_ket U I J2 \<epsilon>2\<close>
  shows \<open>preserves_ket U I (J1 \<sqinter> J2) (\<epsilon>1 + \<epsilon>2)\<close>
  apply (simp flip: ket_invariant_inter)
  using _ assms apply (rule preserves_intersect)
  by (rule compatible_invariants_ket)

text \<open>An invariant is compatible with a register intuitively if the invariant only talks about
  parts of the quantum state outside the register.\<close>

definition \<open>compatible_register_invariant F I \<longleftrightarrow> (\<forall>A. Proj I o\<^sub>C\<^sub>L F A = F A o\<^sub>C\<^sub>L Proj I)\<close>
  for F :: \<open>'a update \<Rightarrow> 'b update\<close>

lemma compatible_register_invariant_top[simp]:
  \<open>compatible_register_invariant F \<top>\<close>
  by (simp add: compatible_register_invariant_def)

lemma compatible_register_invariant_bot[simp]:
  \<open>compatible_register_invariant F \<bottom>\<close>
  by (simp add: compatible_register_invariant_def)


lemma compatible_register_invariant_id:
  assumes \<open>\<And>y. I = UNIV \<or> I = {}\<close>
  shows \<open>compatible_register_invariant id (ket_invariant I)\<close>
  using assms
  by (metis compatible_register_invariant_bot compatible_register_invariant_top ket_invariant_UNIV ket_invariant_empty)

lemma compatible_register_invariant_compatible_register:
  assumes \<open>compatible F G\<close>
  shows \<open>compatible_register_invariant F (lift_invariant G I)\<close>
  unfolding compatible_register_invariant_def lift_invariant_def
  by (metis Proj_is_Proj Proj_on_own_range assms compatible_def register_projector)

lemma compatible_register_invariant_chain[simp]: 
  \<open>compatible_register_invariant (F o G) (lift_invariant F I)  \<longleftrightarrow> compatible_register_invariant G I\<close> if [simp]: \<open>register F\<close>
  by (simp add: compatible_register_invariant_def Proj_lift_invariant register_mult register_inj[THEN inj_eq])

text \<open>Allows to decompose the preservation of an invariant into a part that is preserved
  inside a register, and a part outside of it.\<close>

lemma preserves_register:
  fixes F :: \<open>'a update \<Rightarrow> 'b update\<close>
  assumes pres: \<open>preserves U' I' J' \<epsilon>\<close>
  assumes reg[register]: \<open>register F\<close>
  assumes compat: \<open>compatible_register_invariant F K\<close>
  assumes FU': \<open>\<forall>\<psi>\<in>space_as_set I. F U' *\<^sub>V \<psi> = U *\<^sub>V \<psi>\<close>
  assumes FI'_I: \<open>lift_invariant F I' \<ge> I\<close>
  assumes KI: \<open>K \<ge> I\<close>
  assumes FJ'K_I: \<open>lift_invariant F J' \<sqinter> K \<le> J\<close>
  shows \<open>preserves U I J \<epsilon>\<close>
proof -
  define PI' PJ' where \<open>PI' = Proj I'\<close> and \<open>PJ' = Proj J'\<close>
  have 1: \<open>preserves (F U') (lift_invariant F I') (lift_invariant F J') \<epsilon>\<close>
  proof (unfold preserves_onorm)
    have \<open>norm ((id_cblinfun - Proj (lift_invariant F J')) o\<^sub>C\<^sub>L F U' o\<^sub>C\<^sub>L Proj (lift_invariant F I'))
        = norm ((id_cblinfun - PJ') o\<^sub>C\<^sub>L U' o\<^sub>C\<^sub>L PI')\<close> (is \<open>?lhs = _\<close>)
      by (smt (verit, best) PI'_def PJ'_def Proj_lift_invariant reg register_minus register_mult register_norm register_of_id)
    also from pres have \<open>\<dots> \<le> \<epsilon>\<close>
      by (simp add: preserves_onorm PJ'_def PI'_def)
    finally show \<open>?lhs \<le> \<epsilon>\<close>
      by -
  qed

  from compat
  have 2: \<open>preserves (F U') K K 0\<close>
    by (simp add: preserves_onorm cblinfun_compose_assoc cblinfun_compose_minus_left compatible_register_invariant_def)

  with 1 compat 
  have \<open>preserves (F U') (lift_invariant F I' \<sqinter> K) (lift_invariant F J' \<sqinter> K) \<epsilon>\<close>
    apply (subst asm_rl[of \<open>\<epsilon> = \<epsilon> + 0\<close>], simp)
    apply (rule preserves_intersect)
    by (auto simp add: compatible_invariants_def compatible_register_invariant_def preserves_mono Proj_lift_invariant)

  then have \<open>preserves (F U') I J \<epsilon>\<close>
    apply (rule preserves_mono)
    using FI'_I FJ'K_I KI by auto
  then show ?thesis
    apply (rule preserves_cong[THEN iffD1, rotated])
    using FU' by auto
qed

lemma preserves_top[simp]: \<open>\<epsilon> \<ge> 0 \<Longrightarrow> preserves U I \<top> \<epsilon>\<close>
  unfolding preserves_onorm by simp

lemma preserves_bot[simp]: \<open>\<epsilon> \<ge> 0 \<Longrightarrow> preserves U \<bottom> J \<epsilon>\<close>
  unfolding preserves_onorm by simp

lemma preserves_0[simp]: \<open>\<epsilon> \<ge> 0 \<Longrightarrow> preserves 0 I J \<epsilon>\<close>
  unfolding preserves_onorm by simp


text \<open>Tensor product of two invariants: The invariant that requires the first part of the system
to satisfy invariant \<^term>\<open>I\<close> and the second to satisfy \<^term>\<open>J\<close>.\<close>

definition \<open>tensor_invariant I J = ccspan {x \<otimes>\<^sub>s y | x y. x \<in> space_as_set I \<and> y \<in> space_as_set J}\<close>

lemma tensor_invariant_via_Proj: \<open>tensor_invariant I J = (Proj I \<otimes>\<^sub>o Proj J) *\<^sub>S \<top>\<close>
proof (rule Proj_inj, rule tensor_ell2_extensionality, rename_tac \<psi> \<phi>)
  fix \<psi> \<phi>
  define \<psi>1 \<psi>2 where \<open>\<psi>1 = Proj I \<psi>\<close> and \<open>\<psi>2 = Proj (-I) \<psi>\<close>
  have \<open>\<psi> = \<psi>1 + \<psi>2\<close>
    by (simp add: \<psi>1_def \<psi>2_def Proj_ortho_compl minus_cblinfun.rep_eq)
  have \<psi>1I: \<open>\<psi>1 \<in> space_as_set I\<close>
    by (metis Proj_idempotent \<psi>1_def cblinfun_apply_cblinfun_compose norm_Proj_apply) 

  define \<phi>1 \<phi>2 where \<open>\<phi>1 = Proj J \<phi>\<close> and \<open>\<phi>2 = Proj (-J) \<phi>\<close>
  have \<open>\<phi> = \<phi>1 + \<phi>2\<close>
    by (simp add: \<phi>1_def \<phi>2_def Proj_ortho_compl minus_cblinfun.rep_eq)
  have \<phi>1J: \<open>\<phi>1 \<in> space_as_set J\<close>
    by (metis Proj_idempotent \<phi>1_def cblinfun_apply_cblinfun_compose norm_Proj_apply) 

  have aux: \<open>xa \<in> space_as_set I \<Longrightarrow> y \<in> space_as_set J \<Longrightarrow> \<phi> \<bullet>\<^sub>C y \<noteq> 0 \<Longrightarrow> is_orthogonal \<psi>2 xa\<close> for xa y
    by (metis Proj_fixes_image \<open>\<psi> = \<psi>1 + \<psi>2\<close> \<psi>1I \<psi>1_def add_left_imp_eq cblinfun.real.add_right kernel_Proj kernel_memberI orthogonal_complement_orthoI pth_d uminus_ccsubspace.rep_eq)
  have \<open>\<psi>2 \<otimes>\<^sub>s \<phi> \<in> space_as_set (- tensor_invariant I J)\<close>
    by (auto intro!: aux orthogonal_complementI simp add: uminus_ccsubspace.rep_eq tensor_invariant_def ccspan.rep_eq
        simp flip: orthogonal_complement_of_closure orthogonal_complement_of_cspan)
  then have \<psi>2\<phi>: \<open>Proj (tensor_invariant I J) *\<^sub>V (\<psi>2 \<otimes>\<^sub>s \<phi>) = 0\<close>
    by (simp add: kernel_memberD)

  have aux: \<open>xa \<in> space_as_set I \<Longrightarrow> y \<in> space_as_set J \<Longrightarrow> \<phi>2 \<bullet>\<^sub>C y \<noteq> 0 \<Longrightarrow> is_orthogonal \<psi>1 xa\<close> for xa y
    by (metis Proj_fixes_image \<open>\<phi> = \<phi>1 + \<phi>2\<close> \<phi>1J \<phi>1_def add_left_imp_eq cblinfun.real.add_right kernel_Proj kernel_memberI orthogonal_complement_orthoI pth_d uminus_ccsubspace.rep_eq)
  have \<open>\<psi>1 \<otimes>\<^sub>s \<phi>2 \<in> space_as_set (- tensor_invariant I J)\<close>
    by (auto intro!: aux orthogonal_complementI simp add: uminus_ccsubspace.rep_eq tensor_invariant_def ccspan.rep_eq
        simp flip: orthogonal_complement_of_closure orthogonal_complement_of_cspan)
  then have \<psi>1\<phi>2: \<open>Proj (tensor_invariant I J) *\<^sub>V (\<psi>1 \<otimes>\<^sub>s \<phi>2) = 0\<close>
    by (simp add: kernel_memberD)

  have \<psi>1\<phi>1: \<open>Proj (tensor_invariant I J) *\<^sub>V (\<psi>1 \<otimes>\<^sub>s \<phi>1) = \<psi>1 \<otimes>\<^sub>s \<phi>1\<close>
    by (auto intro!: Proj_fixes_image space_as_set_ccspan_memberI exI[of _ \<psi>1] exI[of _ \<phi>1]
        simp: tensor_invariant_def \<psi>1I \<phi>1J)

  have ProjProj: \<open>Proj ((Proj I \<otimes>\<^sub>o Proj J) *\<^sub>S \<top>) = Proj I \<otimes>\<^sub>o Proj J\<close>
    by (simp add: Proj_on_own_range' adj_Proj comp_tensor_op tensor_op_adjoint)

  show \<open>Proj (tensor_invariant I J) *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>) = Proj ((Proj I \<otimes>\<^sub>o Proj J) *\<^sub>S \<top>) *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>)\<close>
    apply (simp add: ProjProj tensor_op_ell2 flip: \<psi>1_def \<phi>1_def)
    apply (simp add: \<open>\<psi> = \<psi>1 + \<psi>2\<close> tensor_ell2_add1 cblinfun.add_right \<psi>2\<phi>)
    by (simp add: \<psi>1\<phi>1 \<psi>1\<phi>2 \<open>\<phi> = \<phi>1 + \<phi>2\<close> tensor_ell2_add2 cblinfun.add_right)
qed

lemma tensor_invariant_mono_left: \<open>I \<le> I' \<Longrightarrow> tensor_invariant I J \<le> tensor_invariant I' J\<close>
  by (auto intro!: space_as_set_mono ccspan_mono simp add: tensor_invariant_def less_eq_ccsubspace.rep_eq)

lemma swap_tensor_invariant[simp]: \<open>swap_ell2 *\<^sub>S tensor_invariant I J = tensor_invariant J I\<close>
  by (force intro!: arg_cong[where f=ccspan] simp: cblinfun_image_ccspan tensor_invariant_def)

lemma tensor_invariant_SUP_left: \<open>tensor_invariant (SUP x\<in>X. I x) J = (SUP x\<in>X. tensor_invariant (I x) J)\<close>
proof (rule order.antisym)
  show \<open>(SUP x\<in>X. tensor_invariant (I x) J) \<le> tensor_invariant (SUP x\<in>X. I x) J\<close>
    by (auto intro!: SUP_least tensor_invariant_mono_left SUP_upper)

  have tensor_left_apply: \<open>CBlinfun (\<lambda>x. x \<otimes>\<^sub>s y) *\<^sub>V x = x \<otimes>\<^sub>s y\<close> for x :: \<open>'a ell2\<close> and y :: \<open>'b ell2\<close>
    by (simp add: bounded_clinear_tensor_ell22 bounded_clinear_CBlinfun_apply clinear_tensor_ell22)

  show \<open>tensor_invariant (SUP x\<in>X. I x) J \<le> (SUP x\<in>X. tensor_invariant (I x) J)\<close>
  proof -
    have \<open>tensor_invariant (SUP x\<in>X. I x) J = ccspan {x \<otimes>\<^sub>s y |x y. x \<in> space_as_set (SUP x\<in>X. I x) \<and> y \<in> space_as_set J}\<close>
      by (auto simp: tensor_invariant_def)
    also have \<open>\<dots> = ccspan (\<Squnion>y\<in>space_as_set J. {x \<otimes>\<^sub>s y |x. x \<in> space_as_set (SUP x\<in>X. I x)})\<close>
      by (auto intro!: arg_cong[where f=ccspan])
    also have \<open>\<dots> = (\<Squnion>y\<in>space_as_set J. ccspan {x \<otimes>\<^sub>s y |x. x \<in> space_as_set (SUP x\<in>X. I x)})\<close>
      by (smt (verit) Sup.SUP_cong ccspan_Sup image_image)
    also have \<open>\<dots> = (\<Squnion>y\<in>space_as_set J. ccspan (cblinfun_apply (CBlinfun (\<lambda>x. x \<otimes>\<^sub>s y)) ` {x. x \<in> space_as_set (SUP x\<in>X. I x)}))\<close>
      apply (rule SUP_cong, simp)
      apply (rule arg_cong[where f=ccspan])
      by (auto simp add: image_def tensor_left_apply)
    also have \<open>\<dots> = (\<Squnion>y\<in>space_as_set J. CBlinfun (\<lambda>x. x \<otimes>\<^sub>s y) *\<^sub>S (SUP x\<in>X. I x))\<close>
      apply (subst cblinfun_image_ccspan[symmetric])
      by auto
    also have \<open>\<dots> = (\<Squnion>y\<in>space_as_set J. (SUP x\<in>X. CBlinfun (\<lambda>x. x \<otimes>\<^sub>s y) *\<^sub>S I x))\<close>
      apply (subst cblinfun_image_SUP)
      by simp
    also have \<open>\<dots> \<le> (\<Squnion>x\<in>X. tensor_invariant (I x) J)\<close>
    proof (rule SUP_least)
      fix y 
      assume \<open>y \<in> space_as_set J\<close>
      have \<open>(CBlinfun (\<lambda>x. x \<otimes>\<^sub>s y) *\<^sub>S I x) \<le> (tensor_invariant (I x) J)\<close> for x
        apply (rule ccsubspace_leI)
        apply (simp add: tensor_invariant_def cblinfun_image.rep_eq ccspan.rep_eq image_def
            tensor_left_apply)
        apply (rule closure_mono)
        by (auto intro!: complex_vector.span_base \<open>y \<in> space_as_set J\<close>)
      then show \<open>(SUP x\<in>X. CBlinfun (\<lambda>x. x \<otimes>\<^sub>s y) *\<^sub>S I x) \<le> (SUP x\<in>X. tensor_invariant (I x) J)\<close>
        by (auto intro!: SUP_mono)
    qed
    finally show \<open>tensor_invariant (\<Squnion> (I ` X)) J \<le> (\<Squnion>x\<in>X. tensor_invariant (I x) J)\<close>
      by -
  qed
qed

lemma tensor_invariant_SUP_right: \<open>tensor_invariant I (SUP x\<in>X. J x) = (SUP x\<in>X. tensor_invariant I (J x))\<close>
proof -
  have \<open>tensor_invariant I (SUP x\<in>X. J x) = swap_ell2 *\<^sub>S tensor_invariant (SUP x\<in>X. J x) I\<close>
    by simp
  also have \<open>\<dots> = swap_ell2 *\<^sub>S (SUP x\<in>X. tensor_invariant (J x) I)\<close>
    by (simp add: tensor_invariant_SUP_left)
  also have \<open>\<dots> = (SUP x\<in>X. swap_ell2 *\<^sub>S tensor_invariant (J x) I)\<close>
    using cblinfun_image_SUP by blast
  also have \<open>\<dots> = (SUP x\<in>X. tensor_invariant I (J x))\<close>
    by simp
  finally show ?thesis
    by -
qed

lemma tensor_invariant_bot_left[simp]: \<open>tensor_invariant \<bottom> J = \<bottom>\<close>
  using tensor_invariant_SUP_left[where I=id and X=\<open>{}\<close> and J=J]
  by simp

lemma tensor_invariant_bot_right[simp]: \<open>tensor_invariant I \<bottom> = \<bottom>\<close>
  using tensor_invariant_SUP_right[where J=id and X=\<open>{}\<close> and I=I]
  by simp

lemma tensor_invariant_Sup_left: \<open>tensor_invariant (Sup II) J = (SUP I\<in>II. tensor_invariant I J)\<close>
  using tensor_invariant_SUP_left[where X=II and I=id and J=J]
  by simp

lemma tensor_invariant_Sup_right: \<open>tensor_invariant I (Sup JJ) = (SUP J\<in>JJ. tensor_invariant I J)\<close>
  using tensor_invariant_SUP_right[where X=JJ and I=I and J=id]
  by simp

lemma tensor_invariant_sup_left: \<open>tensor_invariant (I1 \<squnion> I2) J = tensor_invariant I1 J \<squnion> tensor_invariant I2 J\<close>
  using tensor_invariant_Sup_left[where II=\<open>{I1,I2}\<close>]
  by auto

lemma tensor_invariant_sup_right: \<open>tensor_invariant I (J1 \<squnion> J2) = tensor_invariant I J1 \<squnion> tensor_invariant I J2\<close>
  using tensor_invariant_Sup_right[where JJ=\<open>{J1,J2}\<close>]
  by auto

lemma compatible_register_invariant_compl: \<open>compatible_register_invariant F I \<Longrightarrow> compatible_register_invariant F (-I)\<close>
  by (simp add: compatible_register_invariant_def Proj_ortho_compl cblinfun_compose_minus_left cblinfun_compose_minus_right)

lemma compatible_register_invariant_SUP:
  assumes [simp]: \<open>register F\<close>
  assumes compat: \<open>\<And>x. x \<in> X \<Longrightarrow> compatible_register_invariant F (I x)\<close>
  shows \<open>compatible_register_invariant F (SUP x\<in>X. I x)\<close>
proof -
  from register_decomposition[OF \<open>register F\<close>]
  have \<open>let 'd::type = register_decomposition_basis F in ?thesis\<close>
  proof with_type_mp
    case with_type_mp
    then obtain U :: \<open>('a \<times> 'd) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> 
      where [iff]: \<open>unitary U\<close> and FU: \<open>F \<theta> = sandwich U *\<^sub>V (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
      by auto
    have *: \<open>Proj (I x) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L (A \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L U* = U o\<^sub>C\<^sub>L (A \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L U* o\<^sub>C\<^sub>L Proj (I x)\<close> if \<open>x \<in> X\<close> for x A
      using compat[OF that]
      by (simp add: compatible_register_invariant_def FU sandwich_apply cblinfun_compose_assoc)
    have \<open>(U* o\<^sub>C\<^sub>L Proj (I x) o\<^sub>C\<^sub>L U) o\<^sub>C\<^sub>L (A \<otimes>\<^sub>o id_cblinfun) = (A \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (U* o\<^sub>C\<^sub>L Proj (I x) o\<^sub>C\<^sub>L U)\<close> if \<open>x \<in> X\<close> for x A
      using *[where A=A, OF that, THEN arg_cong, where f=\<open>\<lambda>x. U* o\<^sub>C\<^sub>L x\<close>, THEN arg_cong, where f=\<open>\<lambda>x. x o\<^sub>C\<^sub>L U\<close>]
      apply (simp add: cblinfun_compose_assoc)
      by (simp flip: cblinfun_compose_assoc)
    then have \<open>Proj (U* *\<^sub>S I x) o\<^sub>C\<^sub>L (A \<otimes>\<^sub>o id_cblinfun) = (A \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L Proj (U* *\<^sub>S I x)\<close> if \<open>x \<in> X\<close> for x A
      using that
      by (simp flip: Proj_sandwich add: sandwich_apply)
    then have \<open>Proj (U* *\<^sub>S I x) \<in> commutant (range (\<lambda>A. A \<otimes>\<^sub>o id_cblinfun))\<close> if \<open>x \<in> X\<close> for x
      unfolding commutant_def using that by auto
    then have \<open>Proj (U* *\<^sub>S I x) \<in> range (\<lambda>B. id_cblinfun \<otimes>\<^sub>o B)\<close> if \<open>x \<in> X\<close> for x
      by (simp add: commutant_tensor1 that)
    then obtain \<pi> where *: \<open>Proj (U* *\<^sub>S I x) = id_cblinfun \<otimes>\<^sub>o \<pi> x\<close> if \<open>x \<in> X\<close> for x
      apply atomize_elim
      apply (rule choice)
      by (simp add: image_iff)
    have \<pi>_proj: \<open>is_Proj (\<pi> x)\<close> if \<open>x \<in> X\<close> for x
    proof -
      have \<open>Proj (U* *\<^sub>S I x)* = Proj (U* *\<^sub>S I x)\<close>
        by (simp add: adj_Proj)
      then have \<open>(id_cblinfun :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _) \<otimes>\<^sub>o \<pi> x = id_cblinfun \<otimes>\<^sub>o \<pi> x*\<close>
        by (simp add: *[OF that] tensor_op_adjoint)
      then have 1: \<open>\<pi> x = \<pi> x*\<close>
        using inj_tensor_right[OF id_cblinfun_not_0] injD by fastforce
      have \<open>Proj (U* *\<^sub>S I x) o\<^sub>C\<^sub>L Proj (U* *\<^sub>S I x) = Proj (U* *\<^sub>S I x)\<close>
        by simp
      then have \<open>(id_cblinfun :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _) \<otimes>\<^sub>o (\<pi> x o\<^sub>C\<^sub>L \<pi> x) = id_cblinfun \<otimes>\<^sub>o \<pi> x\<close>
        by (simp add: *[OF that] comp_tensor_op)
      then have 2: \<open>\<pi> x o\<^sub>C\<^sub>L \<pi> x = \<pi> x\<close>
        using inj_tensor_right[OF id_cblinfun_not_0] injD by fastforce
      from 1 2 show \<open>is_Proj (\<pi> x)\<close>
        by (simp add: is_Proj_I)
    qed
    define \<sigma> where \<open>\<sigma> x = \<pi> x *\<^sub>S \<top>\<close> for x
    have **: \<open>U* *\<^sub>S I x = tensor_invariant \<top> (\<sigma> x)\<close> if \<open>x \<in> X\<close> for x
      using *[OF that, THEN arg_cong, where f=\<open>\<lambda>t. t *\<^sub>S \<top>\<close>]
      by (simp add: tensor_invariant_via_Proj \<sigma>_def Proj_on_own_range \<pi>_proj that)
    have \<open>sandwich (U*) (Proj (SUP x\<in>X. I x)) = Proj (U* *\<^sub>S (SUP x\<in>X. I x))\<close>
      by (smt (verit) sandwich_apply Proj_lift_invariant Proj_range \<open>unitary U\<close> cblinfun_compose_image unitary_adj unitary_range unitary_sandwich_register)
    also have \<open>\<dots> = Proj (SUP x\<in>X. U* *\<^sub>S I x)\<close>
      by (simp add: cblinfun_image_SUP)
    also have \<open>\<dots> = Proj (SUP x\<in>X. tensor_invariant \<top> (\<sigma> x))\<close>
      using "**" by auto
    also have \<open>\<dots> = Proj (tensor_invariant \<top> (SUP x\<in>X. \<sigma> x))\<close>
      by (simp add: tensor_invariant_SUP_right)
    also have \<open>\<dots> = id_cblinfun \<otimes>\<^sub>o Proj (SUP x\<in>X. \<sigma> x)\<close>
      by (simp add: Proj_on_own_range' adj_Proj comp_tensor_op tensor_invariant_via_Proj tensor_op_adjoint)
    also have \<open>\<dots> \<in> commutant (range (\<lambda>A. A \<otimes>\<^sub>o id_cblinfun))\<close>
      by (simp add: commutant_tensor1)
    finally have \<open>(U* o\<^sub>C\<^sub>L Proj (SUP x\<in>X. I x) o\<^sub>C\<^sub>L U) o\<^sub>C\<^sub>L (A \<otimes>\<^sub>o id_cblinfun) = (A \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (U* o\<^sub>C\<^sub>L Proj (SUP x\<in>X. I x) o\<^sub>C\<^sub>L U)\<close> for A
      by (simp add: sandwich_apply commutant_def)
    from this[THEN arg_cong, where f=\<open>\<lambda>x. U o\<^sub>C\<^sub>L x\<close>, THEN arg_cong, where f=\<open>\<lambda>x. x o\<^sub>C\<^sub>L U*\<close>]
    have \<open>Proj (SUP x\<in>X. I x) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L (A \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L U* = U o\<^sub>C\<^sub>L (A \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L U* o\<^sub>C\<^sub>L Proj (SUP x\<in>X. I x)\<close> for A
      apply (simp add: cblinfun_compose_assoc)
      by (simp flip: cblinfun_compose_assoc)
    then have \<open>Proj (SUP x\<in>X. I x) o\<^sub>C\<^sub>L F A = F A o\<^sub>C\<^sub>L Proj (SUP x\<in>X. I x)\<close> for A
      by (simp add: FU sandwich_apply cblinfun_compose_assoc)
    then show \<open>compatible_register_invariant F (SUP x\<in>X. I x)\<close>
      by (simp add: compatible_register_invariant_def)
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed

lemma compatible_register_invariant_INF:
  assumes [simp]: \<open>register F\<close>
  assumes compat: \<open>\<And>x. x \<in> X \<Longrightarrow> compatible_register_invariant F (I x)\<close>
  shows \<open>compatible_register_invariant F (INF x\<in>X. I x)\<close>
proof -
  from compat have \<open>compatible_register_invariant F (- I x)\<close> if \<open>x \<in> X\<close> for x
    by (simp add: compatible_register_invariant_compl that)
  then have \<open>compatible_register_invariant F (SUP x\<in>X. - I x)\<close>
    by (simp add: compatible_register_invariant_SUP)
  then have \<open>compatible_register_invariant F (- (SUP x\<in>X. - I x))\<close>
    by (simp add: compatible_register_invariant_compl)
  then show \<open>compatible_register_invariant F (INF x\<in>X. I x)\<close>
    by (metis Extra_General.uminus_INF ortho_involution)
qed

lemma compatible_register_invariant_Sup:
  assumes \<open>register F\<close>
  assumes \<open>\<And>I. I\<in>II \<Longrightarrow> compatible_register_invariant F I\<close>
  shows \<open>compatible_register_invariant F (Sup II)\<close>
  using compatible_register_invariant_SUP[where X=II and I=id and F=F] assms by simp

lemma compatible_register_invariant_Inf:
  assumes \<open>register F\<close>
  assumes \<open>\<And>I. I\<in>II \<Longrightarrow> compatible_register_invariant F I\<close>
  shows \<open>compatible_register_invariant F (Inf II)\<close>
  using compatible_register_invariant_INF[where X=II and I=id and F=F] assms by simp

lemma compatible_register_invariant_inter:
  assumes \<open>register F\<close>
  assumes \<open>compatible_register_invariant F I\<close>
  assumes \<open>compatible_register_invariant F J\<close>
  shows \<open>compatible_register_invariant F (I \<sqinter> J)\<close>
  using compatible_register_invariant_Inf[where II=\<open>{I,J}\<close>]
  using assms by auto

lemma compatible_register_invariant_pair:
  assumes \<open>compatible_register_invariant F I\<close>
  assumes \<open>compatible_register_invariant G I\<close>
  shows \<open>compatible_register_invariant (F;G) I\<close>
proof (cases \<open>compatible F G\<close>)
  case True
  note this[simp]

  have *: \<open>Proj I o\<^sub>C\<^sub>L (F;G) (a \<otimes>\<^sub>o b) = (F;G) (a \<otimes>\<^sub>o b) o\<^sub>C\<^sub>L Proj I\<close> for a b
    using assms    
    apply (simp add: register_pair_apply compatible_register_invariant_def)
    by (metis cblinfun_compose_assoc)
  have \<open>Proj I o\<^sub>C\<^sub>L (F;G) A = (F;G) A o\<^sub>C\<^sub>L Proj I\<close> for A
    apply (rule tensor_extensionality[THEN fun_cong[where x=A]])
    by (auto intro!: comp_preregister[unfolded comp_def, OF _ preregister_mult_left]
        comp_preregister[unfolded comp_def, OF _ preregister_mult_right] * )
  then show ?thesis
    using assms by (auto simp: compatible_register_invariant_def)
next
  case False
  then show ?thesis 
    using [[simproc del: Laws_Quantum.compatibility_warn]]
    by (auto simp: compatible_register_invariant_def register_pair_def compatible_def)
qed

lemma compatible_register_invariant_tensor: 
  assumes [register]: \<open>register F\<close> \<open>register G\<close>
  assumes \<open>compatible_register_invariant F I\<close>
  assumes \<open>compatible_register_invariant G J\<close>
  shows \<open>compatible_register_invariant (F \<otimes>\<^sub>r G) (I \<otimes>\<^sub>S J)\<close>
proof -
  have [iff]: \<open>preregister (\<lambda>ab. Proj (I \<otimes>\<^sub>S J) o\<^sub>C\<^sub>L (F \<otimes>\<^sub>r G) ab)\<close>
    by (auto intro!: comp_preregister[unfolded comp_def, OF _ preregister_mult_left])
  have [iff]: \<open>preregister (\<lambda>ab. (F \<otimes>\<^sub>r G) ab o\<^sub>C\<^sub>L Proj (I \<otimes>\<^sub>S J))\<close>
    by (auto intro!: comp_preregister[unfolded comp_def, OF _ preregister_mult_right])
  have IF: \<open>Proj I o\<^sub>C\<^sub>L F a = F a o\<^sub>C\<^sub>L Proj I\<close> for a
    using assms(3) compatible_register_invariant_def by blast
  have JG: \<open>Proj J o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L Proj J\<close> for b
    using assms(4) compatible_register_invariant_def by blast
  have \<open>Proj (I \<otimes>\<^sub>S J) o\<^sub>C\<^sub>L (F \<otimes>\<^sub>r G) (a \<otimes>\<^sub>o b) = (F \<otimes>\<^sub>r G) (a \<otimes>\<^sub>o b) o\<^sub>C\<^sub>L Proj (I \<otimes>\<^sub>S J)\<close> for a b
    by (simp add: tensor_ccsubspace_via_Proj Proj_on_own_range is_Proj_tensor_op comp_tensor_op IF JG)
  then have \<open>(\<lambda>ab. Proj (I \<otimes>\<^sub>S J) o\<^sub>C\<^sub>L (F \<otimes>\<^sub>r G) ab) = (\<lambda>ab. (F \<otimes>\<^sub>r G) ab o\<^sub>C\<^sub>L Proj (I \<otimes>\<^sub>S J))\<close>
    apply (rule_tac tensor_extensionality)
    by auto
  then show ?thesis
    unfolding compatible_register_invariant_def
    by meson
qed


lemma compatible_register_invariant_image_shrinks:
  assumes \<open>compatible_register_invariant F I\<close>
  shows \<open>F U *\<^sub>S I \<le> I\<close>
proof -
  have \<open>F U *\<^sub>S I = (F U o\<^sub>C\<^sub>L Proj I) *\<^sub>S \<top>\<close>
    by (simp add: cblinfun_compose_image)
  also have \<open>\<dots> = (Proj I o\<^sub>C\<^sub>L F U) *\<^sub>S \<top>\<close>
    by (metis assms compatible_register_invariant_def)
  also have \<open>\<dots> \<le> Proj I *\<^sub>S \<top>\<close>
    by (simp add: Proj_image_leq cblinfun_compose_image)
  also have \<open>\<dots> = I\<close>
    by simp
  finally show ?thesis
    by -
qed

lemma sum_eq_SUP_ccsubspace:
  fixes I :: \<open>'a \<Rightarrow> 'b::complex_normed_vector ccsubspace\<close>
  assumes \<open>finite X\<close>
  shows \<open>(\<Sum>x\<in>X. I x) = (SUP x\<in>X. I x)\<close>
  using assms apply induction
  by simp_all

text \<open>Variant of @{thm [source] invariant_splitting} (see there) that allows the 
  operation that is applied to depend on the state of some other register.\<close>

lemma inv_split_reg:
  fixes X :: \<open>'x update \<Rightarrow> 'm update\<close> \<comment> \<open>register containing the index for the unitary\<close>
    and Y :: \<open>'z \<Rightarrow> 'y update \<Rightarrow> 'm update\<close> \<comment> \<open>register on which the unitary operates\<close>
    and K :: \<open>'z \<Rightarrow> 'm ell2 ccsubspace\<close> \<comment> \<open>additional invariants\<close>
    and M :: \<open>'z set\<close>
(* TODO rename U1 I1 J1 etc to U' etc. for easier instantiation *)
  assumes U1_U: \<open>\<And>z \<psi>. z\<in>M \<Longrightarrow> \<psi> \<in> space_as_set (K z) \<Longrightarrow> (Y z (U1 z)) *\<^sub>V \<psi> = U *\<^sub>V \<psi>\<close>
  assumes pres_I1: \<open>\<And>z. z\<in>M \<Longrightarrow> preserves (U1 z) (I1 z) (J1 z) \<epsilon>\<close>
  assumes I_leq: \<open>I \<le> (SUP z\<in>M. K z \<sqinter> lift_invariant (Y z) (I1 z))\<close>
  assumes J_geq: \<open>\<And>z. z\<in>M \<Longrightarrow> J \<ge> K z \<sqinter> lift_invariant (Y z) (J1 z)\<close>
  assumes YK: \<open>\<And>z. z\<in>M \<Longrightarrow> compatible_register_invariant (Y z) (K z)\<close>
  assumes regY: \<open>\<And>z. z\<in>M \<Longrightarrow> register (Y z)\<close>
  assumes orthoK: \<open>\<And>z z'. z\<in>M \<Longrightarrow> z'\<in>M \<Longrightarrow> z \<noteq> z' \<Longrightarrow> orthogonal_spaces (K z) (K z')\<close>
  assumes \<open>\<epsilon> \<ge> 0\<close>
  assumes [iff]: \<open>finite M\<close>
  shows \<open>preserves U I J \<epsilon>\<close>
proof -
  show ?thesis
  proof (rule invariant_splitting[where S=\<open>K\<close> and S'=\<open>K\<close> and I=\<open>\<lambda>z. K z \<sqinter> lift_invariant (Y z) (I1 z)\<close>
          and J=\<open>\<lambda>z. K z \<sqinter> lift_invariant (Y z) (J1 z)\<close> and X=M])
    from orthoK
    show \<open>orthogonal_spaces (K z) (K z')\<close> if \<open>z\<in>M\<close> \<open>z'\<in>M\<close> \<open>z \<noteq> z'\<close> for z z'
      using that by simp
    then show \<open>orthogonal_spaces (K z) (K z')\<close> if \<open>z\<in>M\<close> \<open>z'\<in>M\<close> \<open>z \<noteq> z'\<close> for z z'
      using that by -
    show \<open>K z \<sqinter> lift_invariant (Y z) (I1 z) \<le> K z\<close> for z
      by auto
    show \<open>K z \<sqinter> lift_invariant (Y z) (J1 z) \<le> K z\<close> for z
      by auto
    show \<open>U *\<^sub>S K z \<le> K z\<close> if \<open>z\<in>M\<close> for z
    proof -
      from U1_U[OF that]
      have \<open>U *\<^sub>S K z = (Y z) (U1 z) *\<^sub>S K z\<close>
        apply (rule_tac space_as_set_inject[THEN iffD1])
        by (simp add: cblinfun_image.rep_eq)
      also from YK[OF that] have \<open>\<dots> \<le> K z\<close>
        by (simp add: compatible_register_invariant_image_shrinks)
      finally show ?thesis
        by -
    qed
    from I_leq
    show \<open>I \<le> (\<Sum>z\<in>M. K z \<sqinter> lift_invariant (Y z) (I1 z))\<close>
      apply (subst sum_eq_SUP_ccsubspace)
      by auto
    from J_geq
    show \<open>(\<Sum>z\<in>M. K z \<sqinter> lift_invariant (Y z) (J1 z)) \<le> J\<close>
      apply (subst sum_eq_SUP_ccsubspace)
      by (auto simp: SUP_le_iff)
    from assms show \<open>0 \<le> \<epsilon>\<close>
      by -
    show \<open>preserves U (K z \<sqinter> lift_invariant (Y z) (I1 z))
          (K z \<sqinter> lift_invariant (Y z) (J1 z)) \<epsilon>\<close> if \<open>z\<in>M\<close> for z
    proof -
      show ?thesis
      proof (rule preserves_register[where U'=\<open>U1 z\<close> and I'=\<open>I1 z\<close> and J'=\<open>J1 z\<close> and F=\<open>Y z\<close> and K=\<open>K z\<close>])
        show \<open>preserves (U1 z) (I1 z) (J1 z) \<epsilon>\<close>
          by (simp add: pres_I1[OF that])
        show \<open>register (Y z)\<close>
          using regY[OF that] by -
        from YK[OF that] show \<open>compatible_register_invariant (Y z) (K z)\<close>
          by -
        from U1_U[OF that]
        show \<open>\<forall>\<psi>\<in>space_as_set (K z \<sqinter> lift_invariant (Y z) (I1 z)). (Y z) (U1 z) *\<^sub>V \<psi> = U *\<^sub>V \<psi>\<close>
          by auto
        show \<open>K z \<sqinter> lift_invariant (Y z) (I1 z) \<le> lift_invariant (Y z) (I1 z)\<close>
          by auto
        show \<open>K z \<sqinter> lift_invariant (Y z) (I1 z) \<le> K z\<close>
          by simp
        show \<open>lift_invariant (Y z) (J1 z) \<sqinter> K z \<le> K z \<sqinter> lift_invariant (Y z) (J1 z)\<close>
          using [[simp_trace]]
          by simp
      qed
    qed
    show \<open>finite M\<close>
      by simp
  qed
qed


lemma Proj_ket_invariant_ket: \<open>Proj (ket_invariant X) *\<^sub>V ket i = (if i\<in>X then ket i else 0)\<close>
proof (cases \<open>i\<in>X\<close>)
  case True
  then have \<open>ket i \<in> space_as_set (ket_invariant X)\<close>
    by (simp add: ccspan_superset' ket_invariant_def)
  then have \<open>Proj (ket_invariant X) *\<^sub>V ket i = ket i\<close>
    by (rule Proj_fixes_image)
  also have \<open>ket i = (if i\<in>X then ket i else 0)\<close>
    using True by simp
  finally show ?thesis
    by -
next
  case False
  then have *: \<open>ket i \<in> space_as_set (ket_invariant (-X))\<close>
    by (simp add: ccspan_superset' ket_invariant_def)
  have \<open>Proj (ket_invariant X) *\<^sub>V ket i = (id_cblinfun - Proj (ket_invariant (-X))) *\<^sub>V ket i\<close>
    by (simp add: Proj_ortho_compl ket_invariant_compl)
  also have \<open>\<dots> = ket i - Proj (ket_invariant (-X)) *\<^sub>V ket i\<close>
    by (simp add: minus_cblinfun.rep_eq)
  also from * have \<open>\<dots> = ket i - ket i\<close>
    by (simp add: Proj_fixes_image)
  also have \<open>\<dots> = (if i\<in>X then ket i else 0)\<close>
    using False by simp
  finally show ?thesis 
    by -
qed

lemma lift_invariant_function_at_ket_inv: \<open>lift_invariant (function_at x) (ket_invariant I) = ket_invariant {f. f x \<in> I}\<close>
proof -
  have \<open>Proj (lift_invariant (function_at x) (ket_invariant I)) = Proj (ket_invariant {f. f x \<in> I})\<close>
  proof (rule equal_ket)
    fix f :: \<open>'a \<Rightarrow> 'b\<close>
    have \<open>Proj (lift_invariant (function_at x) (ket_invariant I)) (ket f) = function_at x (Proj (ket_invariant I)) (ket f)\<close>
      by (simp add: Proj_on_own_range lift_invariant_def register_projector)
    also have \<open>\<dots> = function_at_U x *\<^sub>V Fst (Proj (ket_invariant I)) *\<^sub>V (function_at_U x)* *\<^sub>V ket f\<close>
      by (simp add: function_at_def sandwich_apply comp_def)
    also have \<open>\<dots> = function_at_U x *\<^sub>V Fst (Proj (ket_invariant I)) *\<^sub>V ket (f x, snd (puncture_function x f))\<close>
      by (simp flip: puncture_function_split)
    also have \<open>\<dots> = (if f x \<in> I then function_at_U x *\<^sub>V (ket (f x) \<otimes>\<^sub>s ket (snd (puncture_function x f))) else 0)\<close>
      by (auto simp: Fst_def tensor_op_ell2 Proj_ket_invariant_ket simp flip: tensor_ell2_ket)
    also have \<open>\<dots> = (if f x \<in> I then ket (fix_punctured_function x (f x, snd (puncture_function x f))) else 0)\<close>
      by (simp add: tensor_ell2_ket)
    also have \<open>\<dots> = (if f x \<in> I then ket f else 0)\<close>
      by (simp flip: puncture_function_split)
    also have \<open>\<dots> = Proj (ket_invariant {f. f x \<in> I}) *\<^sub>V ket f\<close>
      by (simp add: Proj_ket_invariant_ket)
    finally show \<open>Proj (lift_invariant (function_at x) (ket_invariant I)) *\<^sub>V ket f = Proj (ket_invariant {f. f x \<in> I}) *\<^sub>V ket f\<close>
      by -
  qed
  then show ?thesis
    by (rule Proj_inj)
qed

lemma ket_invariant_prod: \<open>Proj (ket_invariant (A \<times> B)) = Proj (ket_invariant A) \<otimes>\<^sub>o Proj (ket_invariant B)\<close>
  apply (rule equal_ket)
  by (auto simp: Proj_ket_invariant_ket tensor_op_ell2 simp flip: tensor_ell2_ket
      split: if_split_asm)

lemma lift_Fst_inv: \<open>lift_invariant Fst I = I \<otimes>\<^sub>S \<top>\<close>
  apply (rule Proj_inj)
  by (simp add: lift_invariant_def Proj_on_own_range register_projector Fst_def tensor_ccsubspace_via_Proj)
lemma lift_Snd_inv: \<open>lift_invariant Snd I = \<top> \<otimes>\<^sub>S I\<close>
  apply (rule Proj_inj)
  by (simp add: lift_invariant_def Proj_on_own_range register_projector Snd_def tensor_ccsubspace_via_Proj)

lemma lift_Snd_ket_inv: \<open>lift_invariant Snd (ket_invariant I) = ket_invariant (UNIV \<times> I)\<close>
  apply (rule Proj_inj)
  apply (simp add: lift_invariant_def Proj_on_own_range register_projector ket_invariant_prod)
  by (simp add: Snd_def)
lemma lift_Fst_ket_inv: \<open>lift_invariant Fst (ket_invariant I) = ket_invariant (I \<times> UNIV)\<close>
  apply (rule Proj_inj)
  apply (simp add: lift_invariant_def Proj_on_own_range register_projector ket_invariant_prod)
  by (simp add: Fst_def)

lemma lift_inv_prod: 
  assumes [simp]: \<open>compatible F G\<close>
  shows \<open>lift_invariant (F;G) (ket_invariant (I \<times> J)) = 
      lift_invariant F (ket_invariant I) \<sqinter> lift_invariant G (ket_invariant J)\<close>
  by (simp add: compatible_proj_intersect lift_invariant_def register_pair_apply ket_invariant_prod)

lemma lift_inv_tensor: 
  assumes [register]: \<open>register F\<close> \<open>register G\<close>
  shows \<open>lift_invariant (F \<otimes>\<^sub>r G) (ket_invariant (I \<times> J)) = 
      lift_invariant F (ket_invariant I) \<otimes>\<^sub>S lift_invariant G (ket_invariant J)\<close>
  by (simp add: lift_invariant_def ket_invariant_prod tensor_ccsubspace_image)


lemma lift_invariant_sup:
  fixes F :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) \<Rightarrow> ('b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2)\<close>
  assumes [simp]: \<open>register F\<close>
  shows \<open>lift_invariant F (I \<squnion> J) = lift_invariant F I \<squnion> lift_invariant F J\<close>
proof -
  from register_decomposition[OF \<open>register F\<close>]
  have \<open>let 'c::type = register_decomposition_basis F in ?thesis\<close>
  proof with_type_mp
    case with_type_mp
    then obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> 
    where \<open>unitary U\<close> and FU: \<open>F \<theta> = sandwich U *\<^sub>V (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
      by auto
    have lift_F: \<open>lift_invariant F K = U *\<^sub>S (Proj (tensor_invariant K \<top>)) *\<^sub>S \<top>\<close> for K
      using \<open>unitary U\<close>
      by (simp add: lift_invariant_def FU sandwich_apply cblinfun_compose_image tensor_invariant_via_Proj)
    show \<open>lift_invariant F (I \<squnion> J) = lift_invariant F I \<squnion> lift_invariant F J\<close>
      by (auto simp: lift_F tensor_invariant_sup_left)
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed

lemma lift_invariant_SUP:
  fixes F :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) \<Rightarrow> ('b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2)\<close>
  assumes \<open>register F\<close>
  shows \<open>lift_invariant F (SUP x\<in>X. I x) = (SUP x\<in>X. lift_invariant F (I x))\<close>
proof -
  from register_decomposition[OF \<open>register F\<close>]
  have \<open>let 'd::type = register_decomposition_basis F in ?thesis\<close>
  proof with_type_mp
    case with_type_mp
    then obtain U :: \<open>('a \<times> 'd) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> 
      where \<open>unitary U\<close> and FU: \<open>F \<theta> = sandwich U *\<^sub>V (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
      by auto
    have lift_F: \<open>lift_invariant F K = U *\<^sub>S (Proj (tensor_invariant K \<top>)) *\<^sub>S \<top>\<close> for K
      using \<open>unitary U\<close>
      by (simp add: lift_invariant_def FU sandwich_apply cblinfun_compose_image tensor_invariant_via_Proj)
    show \<open>lift_invariant F (SUP x\<in>X. I x) = (SUP x\<in>X. lift_invariant F (I x))\<close>
      by (auto simp: lift_F tensor_invariant_SUP_left cblinfun_image_SUP)
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed

lemma lift_invariant_compl: \<open>lift_invariant R (- U) = - lift_invariant R U\<close> if \<open>register R\<close>
  apply (simp add: lift_invariant_def Proj_ortho_compl)
  by (metis (no_types, lifting) Proj_is_Proj Proj_on_own_range Proj_ortho_compl Proj_range register_minus register_of_id
      register_projector that)

lemma lift_invariant_INF:
  assumes \<open>register F\<close>
  shows \<open>lift_invariant F (\<Sqinter>x\<in>A. I x) = (\<Sqinter>x\<in>A. lift_invariant F (I x))\<close>
  using lift_invariant_SUP[OF assms, where I=\<open>\<lambda>x. - I x\<close> and X=A]
  by (simp add: lift_invariant_compl assms flip: uminus_INF)

(* TODO move *)
lemma lift_invariant_inf: 
  assumes \<open>register F\<close>
  shows \<open>lift_invariant F (I \<sqinter> J) = lift_invariant F I \<sqinter> lift_invariant F J\<close>
  using lift_invariant_INF[where A=\<open>{False,True}\<close> and I=\<open>\<lambda>b. if b then J else I\<close>] assms
  by simp


(* TODO move *)
lemma lift_invariant_mono:
  assumes \<open>register F\<close>
  assumes \<open>I \<le> J\<close>
  shows \<open>lift_invariant F I \<le> lift_invariant F J\<close>
  by (metis assms(1,2) inf.absorb_iff2 lift_invariant_inf)


lemma lift_inv_prod':
  fixes F :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) \<Rightarrow> ('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2)\<close>
  fixes G :: \<open>('b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow> ('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2)\<close>
  assumes [simp]: \<open>compatible F G\<close>
  shows \<open>lift_invariant (F;G) (ket_invariant I) = 
      (SUP (x,y)\<in>I. lift_invariant F (ket_invariant {x}) \<sqinter> lift_invariant G (ket_invariant {y}))\<close>
  by (simp flip: lift_inv_prod lift_invariant_SUP ket_invariant_SUP)

lemma lift_inv_tensor':
  assumes [register]: \<open>register F\<close> \<open>register G\<close>
  shows \<open>lift_invariant (F \<otimes>\<^sub>r G) (ket_invariant I) = 
      (SUP (x,y)\<in>I. lift_invariant F (ket_invariant {x}) \<otimes>\<^sub>S lift_invariant G (ket_invariant {y}))\<close>
  by (simp add: register_tensor_is_register flip: lift_inv_tensor lift_invariant_SUP ket_invariant_SUP)

lemma classical_operator_ket_invariant:
  assumes \<open>inj_map f\<close>
  shows \<open>classical_operator f *\<^sub>S ket_invariant I = ket_invariant (Some -` f ` I)\<close>
proof -
  have \<open>ccspan ((\<lambda>x. case f x of None \<Rightarrow> 0 | Some x \<Rightarrow> ket x) ` I) = (\<Squnion>x\<in>I. ccspan ((\<lambda>x. case f x of None \<Rightarrow> 0 | Some x \<Rightarrow> ket x) ` {x}))\<close>
    by (auto intro: arg_cong[where f=ccspan] simp add: SUP_ccspan)
  also have \<open>\<dots> = (\<Squnion>x\<in>I. ccspan (ket ` Some -` f ` {x}))\<close>
  proof (rule SUP_cong[OF refl])
    fix x
    have [simp]: \<open>Some -` {None} = {}\<close>
      by fastforce
    have [simp]: \<open>Some -` {Some a} = {a}\<close> for a
      by fastforce
    show \<open>ccspan ((\<lambda>x. case f x of None \<Rightarrow> 0 | Some x \<Rightarrow> ket x) ` {x}) = ccspan (ket ` Some -` f ` {x})\<close>
      apply (cases \<open>f x\<close>)
      by auto
  qed
  also have \<open>\<dots> = ccspan (ket ` Some -` f ` I)\<close>
    by (auto intro: arg_cong[where f=ccspan] simp add: SUP_ccspan)
  finally show ?thesis
    by (simp add: ket_invariant_def cblinfun_image_ccspan image_image classical_operator_ket assms
        classical_operator_exists_inj)
qed


lemma Proj_ket_invariant_singleton: \<open>Proj (ket_invariant {x}) = selfbutter (ket x)\<close>
  by (simp add: ket_invariant_def butterfly_eq_proj)


lemma lift_inv_classical:
  fixes F :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2 \<Rightarrow> 'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> and f :: \<open>'a \<times> 'c \<Rightarrow> 'b\<close>
  assumes [register]: \<open>register F\<close>
  assumes \<open>inj f\<close>
  assumes \<open>\<And>x::'a. x \<in> I \<Longrightarrow> F (selfbutter (ket x)) = sandwich (classical_operator (Some o f)) (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun)\<close>
  shows \<open>lift_invariant F (ket_invariant I) = ket_invariant (f ` (I \<times> UNIV))\<close>
proof -
  have [iff]: \<open>isometry (classical_operator (Some \<circ> f))\<close>
    by (auto intro!: isometry_classical_operator assms)
  have \<open>lift_invariant F (ket_invariant I) = (SUP x\<in>I. lift_invariant F (ket_invariant {x}))\<close>
    by (simp add: flip: lift_invariant_SUP ket_invariant_SUP)
  also have \<open>\<dots> = (SUP x\<in>I. F (selfbutter (ket x)) *\<^sub>S \<top>)\<close>
    by (simp add: lift_invariant_def Proj_ket_invariant_singleton)
  also have \<open>\<dots> = (SUP x\<in>I. sandwich (classical_operator (Some o f)) (selfbutter (ket x) \<otimes>\<^sub>o id_cblinfun) *\<^sub>S \<top>)\<close>
    using assms by force
  also have \<open>\<dots> = (SUP x\<in>I. sandwich (classical_operator (Some o f)) (Proj (ket_invariant ({x} \<times> UNIV))) *\<^sub>S \<top>)\<close>
    apply (simp add: flip: ket_invariant_tensor)
    by (metis (no_types, lifting) Proj_ket_invariant_singleton Proj_top ket_invariant_UNIV ket_invariant_prod ket_invariant_tensor)
  also have \<open>\<dots> = (SUP x\<in>I. Proj (classical_operator (Some o f) *\<^sub>S ket_invariant ({x} \<times> UNIV)) *\<^sub>S \<top>)\<close>
    using Proj_sandwich by fastforce
  also have \<open>\<dots> = (SUP x\<in>I. classical_operator (Some o f) *\<^sub>S ket_invariant ({x} \<times> UNIV))\<close>
    by auto
  also have \<open>\<dots> = (SUP x\<in>I. ket_invariant (f ` ({x} \<times> UNIV)))\<close>
    apply (subst classical_operator_ket_invariant)
     apply (simp add: assms(2)) 
    by (simp add: inj_vimage_image_eq flip: image_image)
  also have \<open>\<dots> = ket_invariant (\<Union>x\<in>I. f ` ({x} \<times> UNIV))\<close>
    by (simp add: ket_invariant_SUP)
  also have \<open>\<dots> = ket_invariant (f ` (I \<times> UNIV))\<close>
    by auto
  finally show ?thesis
    by -
qed

lemma register_image_lift_invariant: 
  assumes \<open>register F\<close>
  assumes \<open>isometry U\<close>
  shows \<open>F U *\<^sub>S lift_invariant F I = lift_invariant F (U *\<^sub>S I)\<close>
proof -
  have \<open>F U *\<^sub>S lift_invariant F I = F U *\<^sub>S F (Proj I) *\<^sub>S \<top>\<close>
    by (simp add: lift_invariant_def)
  also have \<open>\<dots> = F U *\<^sub>S F (Proj I) *\<^sub>S (F U)* *\<^sub>S \<top>\<close>
    by (simp add: assms(1,2) range_adjoint_isometry register_isometry)
  also have \<open>\<dots> = F (sandwich U (Proj I)) *\<^sub>S \<top>\<close>
    by (smt (verit, best) Proj_lift_invariant Proj_range Proj_sandwich assms(1,2) range_adjoint_isometry
        register_isometry register_sandwich)
  also have \<open>\<dots> = F (Proj (U *\<^sub>S I)) *\<^sub>S \<top>\<close>
    by (simp add: Proj_sandwich assms(2))
  also have \<open>\<dots> = lift_invariant F (U *\<^sub>S I)\<close>
    by (simp add: lift_invariant_def)
  finally show ?thesis
    by -
qed



lemma ell2_sum_ket_ket_invariant:
  fixes \<psi> :: \<open>'a ell2\<close>
  assumes \<open>\<psi> \<in> space_as_set (ket_invariant X)\<close>
  shows \<open>\<psi> = (\<Sum>\<^sub>\<infinity>i\<in>X. Rep_ell2 \<psi> i *\<^sub>C ket i)\<close>
proof -
  from assms have \<open>\<psi> = Proj (ket_invariant X) *\<^sub>V \<psi>\<close>
    by (simp add: Proj_fixes_image)
  also have \<open>\<dots> = Proj (ket_invariant X) *\<^sub>V (\<Sum>\<^sub>\<infinity>i. Rep_ell2 \<psi> i *\<^sub>C ket i)\<close>
    by (simp flip: ell2_decompose_infsum)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. Rep_ell2 \<psi> i *\<^sub>C Proj (ket_invariant X) *\<^sub>V ket i)\<close>
    by (simp flip: infsum_cblinfun_apply add: ell2_decompose_summable cblinfun.scaleC_right)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. Rep_ell2 \<psi> i *\<^sub>C (if i\<in>X then ket i else 0))\<close>
    by (simp add: Proj_ket_invariant_ket)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i\<in>X. Rep_ell2 \<psi> i *\<^sub>C ket i)\<close>
    apply (rule infsum_cong_neutral)
    by auto
  finally show ?thesis
    by simp
qed

lemma compatible_register_invariant_Fst_comp:
  fixes I :: \<open>('a \<times> 'b) set\<close>
  assumes [simp]: \<open>register F\<close>
  assumes \<open>\<And>y. compatible_register_invariant F (ket_invariant ((\<lambda>x. (x,y)) -` I))\<close>
  shows \<open>compatible_register_invariant (Fst o F) (ket_invariant I)\<close>
  apply (subst asm_rl[of \<open>I = (\<Union>y. ((\<lambda>x. (x,y)) -` I) \<times> {y})\<close>])
   apply fastforce
  apply (simp add: ket_invariant_SUP)
  apply (rule compatible_register_invariant_SUP, simp)
  apply (simp add: compatible_register_invariant_def ket_invariant_prod Fst_def comp_tensor_op)
  by (metis assms compatible_register_invariant_def)

lemma compatible_register_invariant_Fst:
  assumes \<open>\<And>y. ((\<lambda>x. (x,y)) -` I) = UNIV \<or> ((\<lambda>x. (x,y)) -` I) = {}\<close>
  shows \<open>compatible_register_invariant Fst (ket_invariant I)\<close>
  apply (subst asm_rl[of \<open>Fst = Fst o id\<close>], simp)
  apply (rule compatible_register_invariant_Fst_comp, simp)
  using assms by (rule compatible_register_invariant_id)

lemma compatible_register_invariant_Snd_comp:
  fixes I :: \<open>('a \<times> 'b) set\<close>
  assumes [simp]: \<open>register F\<close>
  assumes \<open>\<And>x. compatible_register_invariant F (ket_invariant ((\<lambda>y. (x,y)) -` I))\<close>
  shows \<open>compatible_register_invariant (Snd o F) (ket_invariant I)\<close>
  apply (subst asm_rl[of \<open>I = (\<Union>x. {x} \<times> ((\<lambda>y. (x,y)) -` I))\<close>])
   apply fastforce
  apply (simp add: ket_invariant_SUP)
  apply (rule compatible_register_invariant_SUP, simp)
  apply (simp add: compatible_register_invariant_def ket_invariant_prod Snd_def comp_tensor_op)
  by (metis assms compatible_register_invariant_def)

lemma compatible_register_invariant_Snd:
  assumes \<open>\<And>x. ((\<lambda>y. (x,y)) -` I) = UNIV \<or> ((\<lambda>y. (x,y)) -` I) = {}\<close>
  shows \<open>compatible_register_invariant Snd (ket_invariant I)\<close>
  apply (subst asm_rl[of \<open>Snd = Snd o id\<close>], simp)
  apply (rule compatible_register_invariant_Snd_comp, simp)
  using assms by (rule compatible_register_invariant_id)

lemma compatible_register_invariant_Fst_tensor[simp]:
  shows \<open>compatible_register_invariant Fst (\<top> \<otimes>\<^sub>S I)\<close>
  by (simp add: compatible_register_invariant_def Fst_def Proj_on_own_range comp_tensor_op is_Proj_tensor_op tensor_ccsubspace_via_Proj)

lemma compatible_register_invariant_Snd_tensor[simp]:
  shows \<open>compatible_register_invariant Snd (I \<otimes>\<^sub>S \<top>)\<close>
  by (simp add: compatible_register_invariant_def Snd_def Proj_on_own_range comp_tensor_op is_Proj_tensor_op tensor_ccsubspace_via_Proj)

lemma compatible_register_invariant_sandwich_comp:
  fixes U :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  assumes [simp]: \<open>unitary U\<close>
  assumes \<open>compatible_register_invariant F (U* *\<^sub>S I)\<close>
  shows \<open>compatible_register_invariant (sandwich U o F) I\<close>
  apply (subst asm_rl[of \<open>I = U *\<^sub>S U* *\<^sub>S I\<close>])
   apply (simp add: cblinfun_assoc_left(2))
  using assms 
  by (simp add: compatible_register_invariant_def unitary_sandwich_register register_mult
      flip: Proj_sandwich[of U])

lemma compatible_register_invariant_function_at_comp:
  assumes [simp]: \<open>register F\<close>
  assumes \<open>\<And>z. compatible_register_invariant F (ket_invariant {f x |f. f \<in> I \<and> z(x := undefined) = f(x := undefined)})\<close>
  shows \<open>compatible_register_invariant (function_at x o F) (ket_invariant I)\<close>
proof -
  have \<open>(\<lambda>a. (a, snd (puncture_function x z))) -` Some -` inv_map (Some \<circ> fix_punctured_function x) ` I 
        = (\<lambda>a. (a, snd (puncture_function x z))) -` puncture_function x ` I\<close> (is \<open>?lhs = _\<close>) for z
    by (simp add: inv_map_total bij_fix_punctured_function bij_is_surj inj_vimage_image_eq
        flip: image_image)
  also have \<open>\<dots> z = {f x | f. f\<in>I \<and> snd (puncture_function x z) = snd (puncture_function x f)}\<close> for z
    apply (transfer fixing: I x)
    by auto
  also have \<open>\<dots> z = {f x | f. f\<in>I \<and> z(x:=undefined) = f(x:=undefined)}\<close> for z
  proof -
    have aux: \<open>f \<in> I \<Longrightarrow>
         z(x := undefined) \<circ> Transposition.transpose x undefined =
         f(x := undefined) \<circ> Transposition.transpose x undefined \<Longrightarrow>
         \<exists>fa. f x = fa x \<and> fa \<in> I \<and> z(x := undefined) = fa(x := undefined)\<close> for f
      by (metis swap_nilpotent)
    show ?thesis
      apply (transfer fixing: z x I)
      using aux by (auto simp: fun_upd_comp_left)
  qed
  finally have \<open>compatible_register_invariant F (ket_invariant ((\<lambda>a. (a, snd (puncture_function x z))) -` Some -` inv_map (Some \<circ> fix_punctured_function x) ` I))\<close> for z
    by (simp add: assms)
  then have *: \<open>compatible_register_invariant F (ket_invariant ((\<lambda>a. (a, y)) -` Some -` inv_map (Some \<circ> fix_punctured_function x) ` I))\<close> for y
    by (metis fix_punctured_function_inverse snd_conv)
  show ?thesis
    unfolding function_at_def function_at_U_def Let_def comp_assoc
    apply (rule compatible_register_invariant_sandwich_comp)
     apply (simp add: bij_fix_punctured_function)
    apply (subst classical_operator_adjoint)
     apply (simp add: bij_fix_punctured_function bij_is_inj)
    apply (subst classical_operator_ket_invariant)
     apply (simp add: bij_fix_punctured_function bij_is_inj)
    apply (rule compatible_register_invariant_Fst_comp, simp)
    using * by simp
qed

lemma compatible_register_invariant_function_at:
  assumes \<open>\<And>f y. f\<in>I \<Longrightarrow> f(x:=y) \<in> I\<close>
  shows \<open>compatible_register_invariant (function_at x) (ket_invariant I)\<close>
  apply (subst asm_rl[of \<open>function_at x = function_at x o id\<close>], simp)
  apply (rule compatible_register_invariant_function_at_comp, simp)
  apply (rule compatible_register_invariant_id)
  using assms fun_upd_idem_iff by fastforce

text \<open>The following lemma allows show that an invariant is preserved across several consecutive
  operations. Usually, \<^term>\<open>norm V\<close> and \<^term>\<open>norm U \<le> 1\<close>, so the lemma essentially says that
  the errors are additive.\<close>

lemma preserves_trans[trans]:
  assumes presU: \<open>preserves U I J \<epsilon>\<close>
  assumes presV: \<open>preserves V J K \<delta>\<close>
  shows \<open>preserves (V o\<^sub>C\<^sub>L U) I K (norm V * \<epsilon> + norm U * \<delta>)\<close>
proof -
  have \<open>norm ((id_cblinfun - Proj K) o\<^sub>C\<^sub>L (V o\<^sub>C\<^sub>L U) o\<^sub>C\<^sub>L Proj I)
    = norm ((id_cblinfun - Proj K) o\<^sub>C\<^sub>L V o\<^sub>C\<^sub>L (Proj J + (id_cblinfun - Proj J)) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I)\<close>
    by (auto simp add: cblinfun_assoc_left(1))
  also have \<open>\<dots> \<le> norm ((id_cblinfun - Proj K) o\<^sub>C\<^sub>L V o\<^sub>C\<^sub>L Proj J o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I)
                + norm ((id_cblinfun - Proj K) o\<^sub>C\<^sub>L V o\<^sub>C\<^sub>L (id_cblinfun - Proj J) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I)\<close>
    by (smt (verit) cblinfun_compose_add_left cblinfun_compose_add_right norm_triangle_ineq)
  also have \<open>\<dots> \<le> norm ((id_cblinfun - Proj K) o\<^sub>C\<^sub>L V o\<^sub>C\<^sub>L Proj J o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I) + norm V * \<epsilon>\<close>
  proof -
    have \<open>norm ((id_cblinfun - Proj K) o\<^sub>C\<^sub>L V o\<^sub>C\<^sub>L (id_cblinfun - Proj J) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I)
       \<le> norm (id_cblinfun - Proj K) * norm (V o\<^sub>C\<^sub>L (id_cblinfun - Proj J) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I)\<close>
      by (metis cblinfun_assoc_left(1) norm_cblinfun_compose)
    also have \<open>\<dots> \<le> norm (V o\<^sub>C\<^sub>L (id_cblinfun - Proj J) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I)\<close>
      by (metis Groups.mult_ac(2) Proj_ortho_compl mult.right_neutral mult_left_mono norm_Proj_leq1 norm_ge_zero)
    also have \<open>\<dots> \<le> norm V * norm ((id_cblinfun - Proj J) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I)\<close>
      by (metis cblinfun_assoc_left(1) norm_cblinfun_compose)
    also have \<open>\<dots> \<le> norm V * \<epsilon>\<close>
      by (meson norm_ge_zero ordered_comm_semiring_class.comm_mult_left_mono presU preserves_onorm)
    finally show ?thesis
      by (rule add_left_mono)
  qed
  also have \<open>\<dots> \<le> norm ((id_cblinfun - Proj K) o\<^sub>C\<^sub>L V o\<^sub>C\<^sub>L Proj J o\<^sub>C\<^sub>L U) * norm (Proj I) + norm V * \<epsilon>\<close>
    by (simp add: norm_cblinfun_compose)
  also have \<open>\<dots> \<le> norm ((id_cblinfun - Proj K) o\<^sub>C\<^sub>L V o\<^sub>C\<^sub>L Proj J o\<^sub>C\<^sub>L U) + norm V * \<epsilon>\<close>
    by (simp add: norm_is_Proj mult.commute mult_left_le_one_le)
  also have \<open>\<dots> \<le> norm ((id_cblinfun - Proj K) o\<^sub>C\<^sub>L V o\<^sub>C\<^sub>L Proj J) * norm U + norm V * \<epsilon>\<close>
    by (simp add: norm_cblinfun_compose)
  also have \<open>\<dots> \<le> norm U * \<delta> + norm V * \<epsilon>\<close>
    by (metis add.commute add_le_cancel_left mult.commute mult_left_mono norm_ge_zero presV preserves_onorm)
  finally show ?thesis
    by (simp add: preserves_onorm)
qed

text \<open>An operation that operates on a register that is outside the invariant preserves the invariant perfectly.\<close>

lemma preserves_compatible: 
  assumes compat: \<open>compatible_register_invariant F I\<close>
  assumes \<open>\<epsilon> \<ge> 0\<close>
  shows \<open>preserves (F U) I I \<epsilon>\<close>
proof (rule preservesI')
  from assms show \<open>\<epsilon> \<ge> 0\<close> by -
  fix \<psi> assume \<open>\<psi> \<in> space_as_set I\<close>
  then have \<psi>I: \<open>\<psi> = Proj I *\<^sub>V \<psi>\<close>
    using Proj_fixes_image by force
  from compat have FI: \<open>F U *\<^sub>V Proj I *\<^sub>V \<psi> = Proj I *\<^sub>V F U *\<^sub>V \<psi>\<close>
    by (metis cblinfun_apply_cblinfun_compose compatible_register_invariant_def)
  have \<open>Proj (- I) *\<^sub>V F U *\<^sub>V \<psi> = 0\<close>
    apply (subst \<psi>I) apply (subst FI)
    by (metis FI Proj_ortho_compl \<psi>I cancel_comm_monoid_add_class.diff_cancel cblinfun.diff_left id_cblinfun_apply)
  with \<open>\<epsilon> \<ge> 0\<close> show \<open>norm (Proj (- I) *\<^sub>V F U *\<^sub>V \<psi>) \<le> \<epsilon>\<close>
    by simp
qed

lemma Proj_ket_invariant_butterfly: \<open>Proj (ket_invariant {x}) = selfbutter (ket x)\<close>
  by (simp add: butterfly_eq_proj ket_invariant_def)

lemma ket_in_ket_invariantI: \<open>ket x \<in> space_as_set (ket_invariant I)\<close> if \<open>x \<in> I\<close>
  by (metis Proj_ket_invariant_ket Proj_range cblinfun_apply_in_image that)

lemma cblinfun_image_ket_invariant_leqI:
  assumes \<open>\<And>x. x \<in> I \<Longrightarrow> U *\<^sub>V ket x \<in> space_as_set J\<close>
  shows \<open>U *\<^sub>S ket_invariant I \<le> J\<close>
  by (simp add: assms cblinfun_image_ccspan ccspan_leqI image_subset_iff ket_invariant_def)

lemma preserves0I: \<open>preserves U I J 0 \<longleftrightarrow> U *\<^sub>S I \<le> J\<close>
proof
  have \<open>(id_cblinfun - Proj J) o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Proj I = 0 \<Longrightarrow> U *\<^sub>S I \<le> J\<close>
    by (metis (no_types, lifting) Proj_range add_diff_cancel_left' cblinfun_assoc_left(2) cblinfun_compose_minus_left cblinfun_compose_id_left cblinfun_image_mono diff_add_cancel diff_zero top_greatest)
  then show \<open>preserves U I J 0 \<Longrightarrow> U *\<^sub>S I \<le> J\<close>
    by (auto simp: preserves_onorm)
next
  assume leq: \<open>U *\<^sub>S I \<le> J\<close>
  show \<open>preserves U I J 0\<close>
  proof (rule preservesI)
    show \<open>0 \<le> (0::real)\<close> by simp
    fix \<psi>
    assume \<open>\<psi> \<in> space_as_set I\<close>
    with leq have \<open>U *\<^sub>V \<psi> \<in> space_as_set J\<close>
      by (metis (no_types, lifting) Proj_fixes_image Proj_range cblinfun_apply_cblinfun_compose cblinfun_apply_in_image cblinfun_compose_image less_eq_ccsubspace.rep_eq subset_iff)
    then have \<open>Proj J *\<^sub>V U *\<^sub>V \<psi> = U *\<^sub>V \<psi>\<close>
      by (simp add: Proj_fixes_image)
    then show \<open>norm (U *\<^sub>V \<psi> - Proj J *\<^sub>V U *\<^sub>V \<psi>) \<le> 0\<close>
      by simp
  qed
qed

lemma lift_invariant_id[simp]: \<open>lift_invariant id I = I\<close>
  by (simp add: lift_invariant_def)

lemma lift_invariant_pair_tensor:
  assumes \<open>compatible X Y\<close>
  shows \<open>lift_invariant (X;Y) (I \<otimes>\<^sub>S J) = lift_invariant X I \<sqinter> lift_invariant Y J\<close>
proof -
  have \<open>lift_invariant (X;Y) (I \<otimes>\<^sub>S J) = (X;Y) (Proj (I \<otimes>\<^sub>S J)) *\<^sub>S \<top>\<close>
    by (simp add: lift_invariant_def)
  also have \<open>\<dots> = (X;Y) (Proj I \<otimes>\<^sub>o Proj J) *\<^sub>S \<top>\<close>
    by (simp add: Proj_on_own_range is_Proj_tensor_op tensor_ccsubspace_via_Proj)
  also have \<open>\<dots> = (X (Proj I) o\<^sub>C\<^sub>L Y (Proj J)) *\<^sub>S \<top>\<close>
    by (simp add: Laws_Quantum.register_pair_apply assms)
  also have \<open>\<dots> = lift_invariant X I \<sqinter> lift_invariant Y J\<close>
    by (simp add: assms compatible_proj_intersect lift_invariant_def)
  finally show ?thesis
    by -
qed

lemma lift_invariant_tensor_tensor:
  assumes [register]: \<open>register X\<close> \<open>register Y\<close>
  shows \<open>lift_invariant (X \<otimes>\<^sub>r Y) (I \<otimes>\<^sub>S J) = lift_invariant X I \<otimes>\<^sub>S lift_invariant Y J\<close>
proof -
  have \<open>lift_invariant (X \<otimes>\<^sub>r Y) (I \<otimes>\<^sub>S J) = (X \<otimes>\<^sub>r Y) (Proj (I \<otimes>\<^sub>S J)) *\<^sub>S \<top>\<close>
    by (simp add: lift_invariant_def)
  also have \<open>\<dots> = (X \<otimes>\<^sub>r Y) (Proj I \<otimes>\<^sub>o Proj J) *\<^sub>S \<top>\<close>
    by (simp add: Proj_on_own_range is_Proj_tensor_op tensor_ccsubspace_via_Proj)
  also have \<open>\<dots> = (X (Proj I) \<otimes>\<^sub>o Y (Proj J)) *\<^sub>S \<top>\<close>
    by (simp add: Laws_Quantum.register_pair_apply assms register_tensor_apply)
  also have \<open>\<dots> = lift_invariant X I \<otimes>\<^sub>S lift_invariant Y J\<close>
    by (simp add: lift_invariant_def tensor_ccsubspace_image)
  finally show ?thesis
    by -
qed

lemma orthogonal_spaces_lift_invariant[simp]: 
  assumes \<open>register Q\<close>
  shows \<open>orthogonal_spaces (lift_invariant Q S) (lift_invariant Q T) \<longleftrightarrow> orthogonal_spaces S T\<close>
proof -
  have \<open>orthogonal_spaces (lift_invariant Q S) (lift_invariant Q T) \<longleftrightarrow> Q (Proj S) o\<^sub>C\<^sub>L Q (Proj T) = 0\<close>
    by (simp add: orthogonal_projectors_orthogonal_spaces lift_invariant_def Proj_on_own_range assms register_projector)
  also have \<open>\<dots> \<longleftrightarrow> Proj S o\<^sub>C\<^sub>L Proj T = 0\<close>
    by (metis (no_types, lifting) assms norm_eq_zero register_mult register_norm)
  also have \<open>\<dots> \<longleftrightarrow> orthogonal_spaces S T\<close>
    by (simp add: orthogonal_projectors_orthogonal_spaces)
  finally show ?thesis
    by -
qed



subsection \<open>Distance from invariants\<close>

definition dist_inv where \<open>dist_inv R I \<psi> = norm (R (Proj (-I)) *\<^sub>V \<psi>)\<close>
  for R :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) \<Rightarrow> ('b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2)\<close>
definition dist_inv_avg where \<open>dist_inv_avg R I \<psi> = sqrt ((\<Sum>x\<in>UNIV. (dist_inv R (I x) (\<psi> x))\<^sup>2) / CARD('x))\<close> for \<psi> :: \<open>'x::finite \<Rightarrow> _\<close>

lemma dist_inv_pos[iff]: \<open>dist_inv R I \<psi> \<ge> 0\<close>
  by (simp add: dist_inv_def)
lemma dist_inv_avg_pos[iff]: \<open>dist_inv_avg R I \<psi> \<ge> 0\<close>
  by (simp add: dist_inv_avg_def sum_nonneg)

lemma dist_inv_0_iff:
  assumes \<open>register R\<close>
  shows \<open>dist_inv R I \<psi> = 0 \<longleftrightarrow> \<psi> \<in> space_as_set (lift_invariant R I)\<close>
proof -
  have \<open>dist_inv R I \<psi> = 0 \<longleftrightarrow> R (Proj (- I)) *\<^sub>V \<psi> = 0\<close>
    by (simp add: dist_inv_def)
  also have \<open>\<dots> \<longleftrightarrow> Proj (R (Proj (- I)) *\<^sub>S \<top>) \<psi> = 0\<close>
  by (simp add: Proj_on_own_range assms register_projector)
  also have \<open>\<dots> \<longleftrightarrow> \<psi> \<in> space_as_set (- (R (Proj (- I)) *\<^sub>S \<top>))\<close>
    using Proj_0_compl kernel_memberI by fastforce
  also have \<open>\<dots> \<longleftrightarrow> \<psi> \<in> space_as_set (- lift_invariant R (-I))\<close>
  by (simp add: lift_invariant_def)
  also have \<open>\<dots> \<longleftrightarrow> \<psi> \<in> space_as_set (lift_invariant R I)\<close>
    by (metis (no_types, lifting) Proj_lift_invariant Proj_ortho_compl Proj_range assms
        ortho_involution register_minus register_of_id)
  finally show ?thesis
    by -
qed

lemma dist_inv_avg_0_iff:
  assumes \<open>register R\<close>
  shows \<open>dist_inv_avg R I \<psi> = 0 \<longleftrightarrow> (\<forall>h. \<psi> h \<in> space_as_set (lift_invariant R (I h)))\<close>
proof -
  have \<open>dist_inv_avg R I \<psi> = 0 \<longleftrightarrow> (\<forall>h. (dist_inv R (I h) (\<psi> h))\<^sup>2 = 0)\<close>
    by (simp add: dist_inv_avg_def sum_nonneg_eq_0_iff)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>h. \<psi> h \<in> space_as_set (lift_invariant R (I h)))\<close>
    by (simp add: assms dist_inv_0_iff)
  finally show ?thesis
    by -
qed

lemma dist_inv_mono:
  assumes \<open>I \<le> J\<close>
  assumes [register]: \<open>register Q\<close>
  shows \<open>dist_inv Q J \<psi> \<le> dist_inv Q I \<psi>\<close>
proof -
  from assms
  have ProjJI: \<open>Proj (-J) = Proj (-J) o\<^sub>C\<^sub>L Proj (-I)\<close>
    by (simp add: Proj_o_Proj_subspace_left)
  have \<open>norm (Q (Proj (- J) o\<^sub>C\<^sub>L Proj (- I)) *\<^sub>V \<psi>) \<le> norm (Q (Proj (- I)) *\<^sub>V \<psi>)\<close>
  by (metis Proj_is_Proj assms(2) is_Proj_reduces_norm register_mult'
      register_projector)
  then show ?thesis
    by (simp add: dist_inv_def flip: ProjJI)
qed


lemma dist_inv_avg_mono:
  assumes \<open>\<And>h. I h \<le> J h\<close>
  assumes [register]: \<open>register Q\<close>
  shows \<open>dist_inv_avg Q J \<psi> \<le> dist_inv_avg Q I \<psi>\<close>
  by (auto intro!: sum_mono divide_right_mono dist_inv_mono assms
      simp: dist_inv_avg_def)

lemma dist_inv_Fst_tensor:
  assumes \<open>norm \<phi> = 1\<close>
  shows \<open>dist_inv (Fst o R) I (\<psi> \<otimes>\<^sub>s \<phi>) = dist_inv R I \<psi>\<close>
proof -
  have \<open>(norm (Fst (R (Proj (- I))) *\<^sub>V \<psi> \<otimes>\<^sub>s \<phi>))\<^sup>2 = (norm (R (Proj (- I)) *\<^sub>V \<psi>))\<^sup>2\<close>
    by (simp add: Fst_def tensor_op_ell2 norm_tensor_ell2 assms)
  then show ?thesis
    by (simp add: dist_inv_def)
qed

lemma dist_inv_avg_Fst_tensor:
  assumes \<open>\<And>h. norm (\<phi> h) = 1\<close>
  shows \<open>dist_inv_avg (Fst o R) I (\<lambda>h. \<psi> h \<otimes>\<^sub>s \<phi> h) = dist_inv_avg R I \<psi>\<close>
  by (simp add: assms dist_inv_avg_def dist_inv_Fst_tensor)

lemma dist_inv_register_rewrite:
  assumes \<open>register Q\<close> and \<open>register R\<close>
  assumes \<open>lift_invariant Q I = lift_invariant R J\<close>
  shows \<open>dist_inv Q I \<psi> = dist_inv R J \<psi>\<close>
proof -
  from assms
  have  \<open>lift_invariant Q (-I) = lift_invariant R (-J)\<close>
    by (simp add: lift_invariant_compl)
  then have \<open>Proj (Q (Proj (-I)) *\<^sub>S \<top>) = Proj (R (Proj (-J)) *\<^sub>S \<top>)\<close>
    by (simp add: lift_invariant_def)
  then have \<open>R (Proj (- J)) = Q (Proj (- I))\<close>
    by (metis Proj_lift_invariant assms lift_invariant_def)
  with assms
  show ?thesis
    by (simp add: dist_inv_def)
qed



lemma dist_inv_avg_register_rewrite:
  assumes \<open>register Q\<close> and \<open>register R\<close>
  assumes \<open>\<And>h. lift_invariant Q (I h) = lift_invariant R (J h)\<close>
  shows \<open>dist_inv_avg Q I \<psi> = dist_inv_avg R J \<psi>\<close>
  using assms by (auto intro!: dist_inv_register_rewrite sum.cong simp add: dist_inv_avg_def)

lemma distance_from_inv_avg0I: 
  \<open>dist_inv_avg Q I \<psi> = 0 \<longleftrightarrow> (\<forall>h. dist_inv Q (I h) (\<psi> h) = 0)\<close> for h :: \<open>'h::finite\<close> and \<psi> :: \<open>'h \<Rightarrow> _\<close>
  by (simp add: dist_inv_avg_def sum_nonneg_eq_0_iff)

lemma dist_inv_apply:
  assumes [register]: \<open>register Q\<close> \<open>register S\<close>
  assumes [iff]: \<open>unitary U\<close>
  assumes QSR: \<open>Q o S = R\<close>
  shows \<open>dist_inv Q I (R U *\<^sub>V \<psi>) = dist_inv Q (S U* *\<^sub>S I) \<psi>\<close>
proof -
  have \<open>norm (Q (Proj (- I)) *\<^sub>V R U *\<^sub>V \<psi>) = norm (Q (Proj (- (S U* *\<^sub>S I))) *\<^sub>V \<psi>)\<close>
  proof -
    have \<open>norm (Q (Proj (- I)) *\<^sub>V R U *\<^sub>V \<psi>) = norm (Q (S U)* *\<^sub>V Q (Proj (- I)) *\<^sub>V Q (S U) *\<^sub>V \<psi>)\<close>
      by (metis assms(1,2,3,4) isometry_preserves_norm o_def register_unitary unitary_twosided_isometry)
    also have \<open>\<dots> = norm (sandwich (Q (S U)*) (Q (Proj (-I))) *\<^sub>V \<psi>)\<close>
      by (simp add: sandwich_apply)
    also have \<open>\<dots> = norm (Q (sandwich (S U*) *\<^sub>V Proj (- I)) *\<^sub>V \<psi>)\<close>
      by (simp add: flip: register_sandwich register_adj)
    also have \<open>\<dots> = norm (Q (Proj (S U* *\<^sub>S - I)) *\<^sub>V \<psi>)\<close>
      by (simp add: Proj_sandwich register_coisometry)
    also have \<open>\<dots> = norm (Q (Proj (- (S U* *\<^sub>S I))) *\<^sub>V \<psi>)\<close>
      by (simp add: unitary_image_ortho_compl register_unitary)
    finally show ?thesis
      by -
  qed
  then show ?thesis
    by (simp add: dist_inv_def)
qed



(* TODO remove \<rightarrow> dist_inv_apply *)
lemma dist_inv_apply_iff:
  assumes [register]: \<open>register Q\<close>
  assumes [iff]: \<open>unitary U\<close>
  shows \<open>dist_inv Q I (Q U *\<^sub>V \<psi>) = dist_inv Q (U* *\<^sub>S I) \<psi>\<close>
  apply (subst dist_inv_apply[where S=id])
  by auto


lemma dist_inv_avg_apply:
  assumes [register]: \<open>register Q\<close> \<open>register S\<close>
  assumes [iff]: \<open>\<And>h. unitary (U h)\<close>
  assumes \<open>Q o S = R\<close>
  shows \<open>dist_inv_avg Q I (\<lambda>h. R (U h) *\<^sub>V \<psi> h) = dist_inv_avg Q (\<lambda>h. S (U h)* *\<^sub>S I h) \<psi>\<close>
  using assms by (auto intro!: sum.cong simp: dist_inv_avg_def dist_inv_apply[where S=S])

(* TODO remove \<rightarrow> dist_inv_avg_apply *)
lemma dist_inv_avg_apply_iff:
  assumes [register]: \<open>register Q\<close>
  assumes [iff]: \<open>\<And>h. unitary (U h)\<close>
  shows \<open>dist_inv_avg Q I (\<lambda>h. Q (U h) *\<^sub>V \<psi> h) = dist_inv_avg Q (\<lambda>h. U h* *\<^sub>S I h) \<psi>\<close>
  by (auto intro!: sum.cong dist_inv_apply_iff simp: dist_inv_avg_def)


lemma dist_inv_intersect_onesided:
  assumes \<open>compatible_invariants I J\<close>
  assumes \<open>register Q\<close>
  assumes \<open>dist_inv Q I \<psi> = 0\<close>
  shows \<open>dist_inv Q (J \<sqinter> I) \<psi> = dist_inv Q J \<psi>\<close>
proof -
  have inside: \<open>\<psi> \<in> space_as_set (lift_invariant Q I)\<close>
    using assms(2,3) dist_inv_0_iff by blast
  have \<open>norm (Q (Proj (- (J \<sqinter> I))) *\<^sub>V \<psi>) = norm (\<psi> - Q (Proj (J \<sqinter> I)) *\<^sub>V \<psi>)\<close>
    by (metis (no_types, lifting) Proj_ortho_compl assms(2) cblinfun.diff_left id_cblinfun.rep_eq register_minus
        register_of_id)
  also have \<open>\<dots> = norm (\<psi> - Q (Proj (J) o\<^sub>C\<^sub>L Proj (I)) *\<^sub>V \<psi>)\<close>
    by (metis assms compatible_invariants_def compatible_invariants_inter)
  also have \<open>\<dots> = norm (\<psi> - Q (Proj (J)) *\<^sub>V Q (Proj (I)) *\<^sub>V \<psi>)\<close>
    by (simp add: assms register_mult')
  also have \<open>\<dots> = norm (\<psi> - Q (Proj (J)) *\<^sub>V \<psi>)\<close>
    by (metis Proj_fixes_image Proj_lift_invariant assms inside)
  also have \<open>\<dots> = norm (Q (Proj (- J)) *\<^sub>V \<psi>)\<close>
    by (simp add: Proj_ortho_compl assms cblinfun.diff_left register_minus)
  finally have \<open>norm (Q (Proj (- (J \<sqinter> I))) *\<^sub>V \<psi>) = norm (Q (Proj (- J)) *\<^sub>V \<psi>)\<close>
    by -
  then show ?thesis
    by (simp add: dist_inv_def)
qed



lemma dist_inv_avg_intersect:
  assumes \<open>\<And>h. compatible_invariants (I h) (J h)\<close>
  assumes \<open>register Q\<close>
  assumes \<open>dist_inv_avg Q I \<psi> = 0\<close>
  shows \<open>dist_inv_avg Q (\<lambda>h. J h \<sqinter> I h) \<psi> = dist_inv_avg Q J \<psi>\<close>
proof -
  have \<open>dist_inv Q (I h) (\<psi> h) = 0 \<close> for h
    using assms(3) distance_from_inv_avg0I by blast
  then show ?thesis
    by (auto intro!: sum.cong dist_inv_intersect_onesided assms simp: dist_inv_avg_def)
qed

lemma dist_inv_avg_const: \<open>dist_inv_avg Q (\<lambda>_. I) (\<lambda>_. \<psi>) = dist_inv Q I \<psi>\<close>
  by (simp add: dist_inv_avg_def dist_inv_def)

(* TODO move *)
lemma register_plus:
  assumes \<open>register Q\<close>
  shows \<open>Q (a + b) = Q a + Q b\<close>
  by (simp add: assms clinear_register complex_vector.linear_add)

(* TODO move *)
lemma compatible_invariants_uminus_left[simp]: \<open>compatible_invariants (-I) J \<longleftrightarrow> compatible_invariants I J\<close>
  by (simp add: Proj_ortho_compl cblinfun_compose_minus_left cblinfun_compose_minus_right compatible_invariants_def)

(* TODO move *)
lemma compatible_invariants_uminus_right[simp]: \<open>compatible_invariants I (-J) \<longleftrightarrow> compatible_invariants I J\<close>
  by (simp add: Proj_ortho_compl cblinfun_compose_minus_left cblinfun_compose_minus_right compatible_invariants_def)

lemma compatible_invariants_sup: \<open>Proj (A \<squnion> B) = Proj A + Proj B - Proj A o\<^sub>C\<^sub>L Proj B\<close> if \<open>compatible_invariants A B\<close>
  apply (rewrite at \<open>A \<squnion> B\<close> to \<open>- (-A \<sqinter> -B)\<close> DEADID.rel_mono_strong)
   apply simp
  apply (subst Proj_ortho_compl)
  by (simp add: that Proj_ortho_compl cblinfun_compose_minus_left cblinfun_compose_minus_right flip: compatible_invariants_inter )

lemma compatible_invariants_sym: \<open>compatible_invariants S T \<longleftrightarrow> compatible_invariants T S\<close>
  by (metis compatible_invariants_def)

lemma compatible_invariants_refl[iff]: \<open>compatible_invariants S S\<close>
  by (metis compatible_invariants_def)

lemma compatible_invariants_infI:
  assumes [iff]: \<open>compatible_invariants S U\<close>
  assumes [iff]: \<open>compatible_invariants S T\<close>
  assumes [iff]: \<open>compatible_invariants T U\<close>
  shows \<open>compatible_invariants S (T \<sqinter> U)\<close>
  by (smt (verit, del_insts) assms(1,2,3) cblinfun_compose_assoc compatible_invariants_def compatible_invariants_inter)


lemma compatible_invariants_supI:
  assumes [iff]: \<open>compatible_invariants S U\<close>
  assumes [iff]: \<open>compatible_invariants S T\<close>
  assumes [iff]: \<open>compatible_invariants T U\<close>
  shows \<open>compatible_invariants S (T \<squnion> U)\<close>
  apply (rewrite at \<open>T \<squnion> U\<close> to \<open>- (-T \<sqinter> -U)\<close> DEADID.rel_mono_strong)
   apply simp
  by (auto intro!: compatible_invariants_infI simp del: compl_inf)

lemma compatible_invariants_inf_sup_distrib1:
  fixes S T U :: \<open>'a::chilbert_space ccsubspace\<close>
  assumes \<open>compatible_invariants S U\<close>
  assumes \<open>compatible_invariants S T\<close>
  assumes \<open>compatible_invariants T U\<close>
  shows \<open>S \<sqinter> (T \<squnion> U) = (S \<sqinter> T) \<squnion> (S \<sqinter> U)\<close>
proof -
  have [iff]: \<open>compatible_invariants (S \<sqinter> T) (S \<sqinter> U)\<close>
    using assms by (auto intro!: compatible_invariants_infI simp: compatible_invariants_sym)
  have \<open>Proj (S \<sqinter> (T \<squnion> U)) = Proj ((S \<sqinter> T) \<squnion> (S \<sqinter> U))\<close>
    apply (simp add: assms compatible_invariants_sup compatible_invariants_supI flip: compatible_invariants_inter)
    by (metis (no_types, lifting) Proj_idempotent assms(2) cblinfun_compose_add_right cblinfun_compose_assoc cblinfun_compose_minus_right
        compatible_invariants_def)
  then show ?thesis
    using Proj_inj by blast
qed

lemma compatible_invariants_inf_sup_distrib2:
  fixes S T U :: \<open>'a::chilbert_space ccsubspace\<close>
  assumes [iff]: \<open>compatible_invariants S U\<close>
  assumes [iff]: \<open>compatible_invariants S T\<close>
  assumes [iff]: \<open>compatible_invariants T U\<close>
  shows \<open>(T \<squnion> U) \<sqinter> S = (T \<sqinter> S) \<squnion> (U \<sqinter> S)\<close>
  by (simp add: compatible_invariants_inf_sup_distrib1 inf_commute)

lemma compatible_invariants_sup_inf_distrib1:
  fixes S T U :: \<open>'a::chilbert_space ccsubspace\<close>
  assumes \<open>compatible_invariants S U\<close>
  assumes \<open>compatible_invariants S T\<close>
  assumes \<open>compatible_invariants T U\<close>
  shows \<open>S \<squnion> (T \<sqinter> U) = (S \<squnion> T) \<sqinter> (S \<squnion> U)\<close>
  by (smt (verit, ccfv_SIG) Groups.add_ac(1) assms(1,2,3) compatible_invariants_def compatible_invariants_inf_sup_distrib1
      compatible_invariants_supI inf_commute inf_sup_absorb plus_ccsubspace_def)

lemma compatible_invariants_sup_inf_distrib2:
  fixes S T U :: \<open>'a::chilbert_space ccsubspace\<close>
  assumes \<open>compatible_invariants S U\<close>
  assumes \<open>compatible_invariants S T\<close>
  assumes \<open>compatible_invariants T U\<close>
  shows \<open>(T \<sqinter> U) \<squnion> S = (T \<squnion> S) \<sqinter> (U \<squnion> S)\<close>
  by (metis Groups.add_ac(2) assms(1,2,3) compatible_invariants_sup_inf_distrib1 plus_ccsubspace_def)

(* TODO move *)
lemma is_orthogonal_Proj_orthogonal_spaces:
  assumes \<open>orthogonal_spaces S T\<close>
  shows \<open>is_orthogonal (Proj S *\<^sub>V \<psi>) (Proj T *\<^sub>V \<psi>)\<close>
  by (metis Proj_range assms cblinfun_apply_in_image orthogonal_spaces_def)

lemma dist_inv_intersect:
  assumes [register]: \<open>register Q\<close>
  assumes [iff]: \<open>compatible_invariants I J\<close>
  shows \<open>dist_inv Q (I \<sqinter> J) \<psi> \<le> sqrt ((dist_inv Q I \<psi>)\<^sup>2 + (dist_inv Q J \<psi>)\<^sup>2)\<close>
proof -
  define PInJ PJnI PnInJ PnI PnJ PnIJ where \<open>PInJ = Q (Proj (I \<sqinter> - J))\<close>
    and \<open>PJnI = Q (Proj (-I \<sqinter> J))\<close> and \<open>PnInJ = Q (Proj (-I \<sqinter> -J))\<close>
    and \<open>PnI = Q (Proj (-I))\<close> and \<open>PnJ = Q (Proj (-J))\<close>
    and \<open>PnIJ = Q (Proj (- (I \<sqinter> J)))\<close>

  have compat1: \<open>compatible_invariants (I \<sqinter> - J) J\<close>
    by (metis Proj_o_Proj_subspace_left Proj_o_Proj_subspace_right compatible_invariants_def compatible_invariants_uminus_right inf_le2)
  have compat2: \<open>compatible_invariants (I \<sqinter> - J) I\<close>
    by (simp add: Proj_o_Proj_subspace_left Proj_o_Proj_subspace_right compatible_invariants_def)

  have ortho1: \<open>orthogonal_spaces (I \<sqinter> - J) (- I \<sqinter> J)\<close>
    by (simp add: le_infI2 orthogonal_spaces_leq_compl)
  have ortho2: \<open>orthogonal_spaces (I \<sqinter> - J \<squnion> - I \<sqinter> J) (- I \<sqinter> - J)\<close>
    by (metis inf_le1 inf_le2 ortho_involution orthocomplemented_lattice_class.compl_sup orthogonal_spaces_leq_compl sup.mono)
  have ortho3: \<open>orthogonal_spaces (- I \<sqinter> J) (- I \<sqinter> - J)\<close>
    by (simp add: le_infI2 orthogonal_spaces_leq_compl) 
  have ortho4: \<open>orthogonal_spaces (I \<sqinter> - J) (- I \<sqinter> - J)\<close>
    by (metis inf_sup_absorb le_infI2 ortho2 orthogonal_spaces_leq_compl)
  have ortho5: \<open>is_orthogonal (PInJ \<psi>) (PnInJ \<psi>)\<close>
    using ortho4 by (auto intro!: is_orthogonal_Proj_orthogonal_spaces simp: PInJ_def PnInJ_def simp flip: Proj_lift_invariant)
  have ortho6: \<open>is_orthogonal (PJnI \<psi>) (PnInJ \<psi>)\<close>
    using ortho3 by (auto intro!: is_orthogonal_Proj_orthogonal_spaces simp: PJnI_def PnInJ_def simp flip: Proj_lift_invariant)
  have ortho7: \<open>is_orthogonal (PInJ \<psi>) (PJnI \<psi>)\<close>
    using ortho1 by (auto intro!: is_orthogonal_Proj_orthogonal_spaces simp: PJnI_def PInJ_def simp flip: Proj_lift_invariant)

  have nI: \<open>-I \<sqinter> J \<squnion> -I \<sqinter> -J = -I\<close>
    by (simp flip: compatible_invariants_inf_sup_distrib1)
  then have PnI_decomp: \<open>PnI = PJnI + PnInJ\<close>
    by (simp add: PnI_def PJnI_def PnInJ_def register_inj' ortho3
        flip: register_plus Proj_sup)

  have nJ: \<open>I \<sqinter> -J \<squnion> -I \<sqinter> -J = -J\<close>
    by (metis (no_types, lifting) assms(2) compatible_invariants_inf_sup_distrib1 compatible_invariants_refl compatible_invariants_sym
        compatible_invariants_uminus_left complemented_lattice_class.sup_compl_top inf_aci(1) inf_top.comm_neutral)
  then have PnJ_decomp: \<open>PnJ = PInJ + PnInJ\<close>
    by (simp add: PnJ_def PInJ_def PnInJ_def register_inj' ortho4
        flip: register_plus Proj_sup)

  have \<open>I \<sqinter> - J \<squnion> - I \<sqinter> J \<squnion> - I \<sqinter> - J = - I \<squnion> - J\<close>
    by (metis (no_types, lifting) Groups.add_ac(1) boolean_algebra_cancel.sup2 nI nJ plus_ccsubspace_def sup_inf_absorb)
  then have PnIJ_decomp: \<open>PnIJ = PInJ + PJnI + PnInJ\<close>
    by (simp add: PnIJ_def PInJ_def PJnI_def PnInJ_def register_inj' ortho1 ortho2
        flip: register_plus Proj_sup)

  have \<open>(dist_inv Q (I \<sqinter> J) \<psi>)\<^sup>2 = (norm (PnIJ \<psi>))\<^sup>2\<close>
    by (simp add: PnIJ_def dist_inv_def)
  also have \<open>\<dots> = (norm (PInJ *\<^sub>V \<psi>))\<^sup>2 + (norm (PJnI *\<^sub>V \<psi>))\<^sup>2 + (norm (PnInJ *\<^sub>V \<psi>))\<^sup>2\<close>
    by (simp add: PnIJ_decomp cblinfun.add_left pythagorean_theorem cinner_add_left ortho5 ortho6 ortho7)
  also have \<open>\<dots> \<le> ((norm (PJnI *\<^sub>V \<psi>))\<^sup>2 + (norm (PnInJ *\<^sub>V \<psi>))\<^sup>2) + ((norm (PInJ *\<^sub>V \<psi>))\<^sup>2 + (norm (PnInJ *\<^sub>V \<psi>))\<^sup>2)\<close>
    by simp
  also have \<open>\<dots> = (norm (PnI \<psi>))\<^sup>2 + (norm (PnJ \<psi>))\<^sup>2\<close>
    by (simp add: ortho5 ortho6 PnI_decomp PnJ_decomp cblinfun.add_left pythagorean_theorem)
  also have \<open>\<dots> \<le> (dist_inv Q I \<psi>)\<^sup>2 + (dist_inv Q J \<psi>)\<^sup>2\<close>
    apply (rule add_mono)
    using assms
    by (simp_all add: PnI_def PnJ_def dist_inv_def)

  finally show ?thesis
    using real_le_rsqrt by presburger
qed


subsection \<open>Preservation of invariants\<close>


(* TODO move stuff from above *)

lemma preserves_lift_invariant:
  assumes [register]: \<open>register Q\<close>
  shows \<open>preserves (Q U) (lift_invariant Q I) (lift_invariant Q J) \<epsilon> \<longleftrightarrow> preserves U I J \<epsilon>\<close>
  using register_minus[OF assms, of id_cblinfun, symmetric]
  by (simp add: preserves_onorm Proj_lift_invariant register_mult register_norm)


lemma dist_inv_leq_if_preserves:
  assumes pres: \<open>preserves U (lift_invariant S J) (lift_invariant R I) \<gamma>\<close>
  assumes [register]: \<open>register S\<close> \<open>register R\<close>
  shows \<open>dist_inv R I (U *\<^sub>V \<psi>) \<le> norm U * dist_inv S J \<psi> + \<gamma> * norm \<psi>\<close>
proof -
  note [[simproc del: Laws_Quantum.compatibility_warn]]
  define \<psi>good \<psi>bad where \<open>\<psi>good = S (Proj J) *\<^sub>V \<psi>\<close> and \<open>\<psi>bad = S (Proj (- J)) *\<^sub>V \<psi>\<close>
  define \<psi>' \<psi>'good \<psi>'bad where \<open>\<psi>' = U \<psi>good\<close> and \<open>\<psi>'good = R (Proj I) \<psi>'\<close> and \<open>\<psi>'bad = R (Proj (-I)) \<psi>'\<close>
  from pres have \<open>\<gamma> \<ge> 0\<close>
    using preserves_def by blast
  have \<psi>_decomp: \<open>\<psi> = \<psi>good + \<psi>bad\<close>
    by (simp add: \<psi>good_def \<psi>bad_def Proj_ortho_compl register_minus flip: cblinfun.add_left)
  have \<psi>'_decomp: \<open>\<psi>' = \<psi>'good + \<psi>'bad\<close>
    by (simp add: \<psi>'good_def \<psi>'bad_def Proj_ortho_compl register_minus flip: cblinfun.add_left)
  define \<delta> where \<open>\<delta> = dist_inv S J \<psi>\<close>
  then have \<psi>bad_bound: \<open>norm \<psi>bad \<le> \<delta>\<close>
    unfolding dist_inv_def \<psi>bad_def by blast
  have \<open>\<psi>good \<in> space_as_set (lift_invariant S J)\<close>
    by (simp add: \<psi>good_def lift_invariant_def)
  with pres have \<open>norm (\<psi>' - Proj (lift_invariant R I) *\<^sub>V \<psi>') \<le> \<gamma> * norm \<psi>good\<close>
    by (simp add: preserves_def \<psi>'_def)
  then have \<open>norm \<psi>'bad \<le> \<gamma> * norm \<psi>good\<close>
    by (simp add: \<psi>'bad_def Proj_ortho_compl register_minus cblinfun.diff_left Proj_lift_invariant)
  also have \<open>\<gamma> * norm \<psi>good \<le> \<gamma> * norm \<psi>\<close>
    by (auto intro!: mult_left_mono is_Proj_reduces_norm \<open>\<gamma> \<ge> 0\<close> intro: register_projector
        simp add: \<psi>good_def)
  finally have \<psi>'bad_bound: \<open>norm \<psi>'bad \<le> \<gamma> * norm \<psi>\<close>
    by meson
  have U\<psi>_decomp: \<open>U \<psi> = \<psi>'good + \<psi>'bad + U \<psi>bad\<close>
    by (simp add: \<psi>_decomp \<psi>'_decomp cblinfun.add_right flip: \<psi>'_def)
  have mI\<psi>'good0: \<open>R (Proj (- I)) \<psi>'good = 0\<close>
    by (metis Proj_fixes_image Proj_lift_invariant \<psi>'_decomp \<psi>'_def \<psi>'bad_def add_diff_cancel_right' assms
        cancel_comm_monoid_add_class.diff_cancel cblinfun.diff_right cblinfun_apply_in_image lift_invariant_def)
  have mI\<psi>'bad: \<open>norm (R (Proj (- I)) \<psi>'bad) \<le> \<gamma> * norm \<psi>\<close>
    by (metis \<psi>'bad_bound \<psi>'_decomp \<psi>'bad_def add_diff_cancel_left' cblinfun.diff_right diff_zero
        mI\<psi>'good0)
  from \<psi>bad_bound 
  have \<open>norm (U \<psi>bad) \<le> norm U * \<delta>\<close>
    apply (rule_tac order_trans[OF norm_cblinfun[of U \<psi>bad]])
    by (simp add: mult_left_mono)
  then have \<open>norm (R (Proj (- I)) *\<^sub>V U \<psi>bad) \<le> norm U * \<delta>\<close>
    apply (rule_tac order_trans[OF norm_cblinfun])
    apply (subgoal_tac \<open>norm (R (Proj (- I))) \<le> 1\<close>)
     apply (smt (verit, best) mult_left_le_one_le norm_ge_zero) 
    by (simp add: norm_Proj_leq1 register_norm)
  with mI\<psi>'bad have \<open>dist_inv R I (U *\<^sub>V \<psi>) \<le> norm U * \<delta> + \<gamma> * norm \<psi>\<close>
    apply (simp add: dist_inv_def U\<psi>_decomp cblinfun.add_right mI\<psi>'good0)
    by (smt (verit, del_insts) norm_triangle_ineq)
  then show ?thesis
    by (simp add: \<delta>_def)
qed

lemma dist_inv_preservesI:
  assumes \<open>dist_inv S J \<psi> \<le> \<epsilon>\<close>
  assumes pres: \<open>preserves U (lift_invariant S J) (lift_invariant R I) \<gamma>\<close>
  assumes \<open>norm U \<le> 1\<close>
  assumes \<open>norm \<psi> \<le> 1\<close>
  assumes \<open>\<gamma> + \<epsilon> \<le> \<delta>\<close>
  assumes [register]: \<open>register S\<close> \<open>register R\<close>
  shows \<open>dist_inv R I (U *\<^sub>V \<psi>) \<le> \<delta>\<close>
proof -
  have \<open>\<gamma> \<ge> 0\<close>
    using pres preserves_def by blast
  with assms have \<open>norm U * dist_inv S J \<psi> + \<gamma> * norm \<psi> \<le> \<delta>\<close>
    by (smt (verit, ccfv_SIG) dist_inv_def mult_left_le mult_left_le_one_le norm_ge_zero)
  then show ?thesis
    apply (rule order_trans[rotated])
    by (rule dist_inv_leq_if_preserves[OF pres \<open>register S\<close> \<open>register R\<close>])
qed


lemma dist_inv_apply_compatible:
  assumes \<open>compatible Q R\<close>
  shows \<open>dist_inv Q I (R U *\<^sub>V \<psi>) \<le> norm U * dist_inv Q I \<psi>\<close>
proof -
  have [register]: \<open>register Q\<close>
    using assms compatible_register1 by blast
  have [register]: \<open>register R\<close>
    using assms compatible_register2 by blast
  have \<open>preserves (R U) (lift_invariant Q I) (lift_invariant Q I) 0\<close>
    apply (rule preserves_compatible[of R])
    by (simp_all add: assms compatible_register_invariant_compatible_register compatible_sym)
  then have \<open>dist_inv Q I (R U *\<^sub>V \<psi>) \<le> norm (R U) * dist_inv Q I \<psi> + 0 * norm \<psi>\<close>
    apply (rule dist_inv_leq_if_preserves)
    by simp_all
  also have \<open>\<dots> \<le> norm U * dist_inv Q I \<psi>\<close>
    by (simp add: register_norm)
  finally show ?thesis
    by -
qed



lemma dist_inv_avg_apply_compatible:
  assumes \<open>\<And>h. compatible Q (R h)\<close>
  shows \<open>dist_inv_avg Q I (\<lambda>h. R h (U h) *\<^sub>V \<psi> h) \<le> (MAX h. norm (U h)) * dist_inv_avg Q I \<psi>\<close>
proof -
  have [iff]: \<open>(MAX h\<in>UNIV. norm (U h)) \<ge> 0\<close>
    by (simp add: Max_ge_iff)
  have \<open>dist_inv_avg Q I (\<lambda>h. R h (U h) *\<^sub>V \<psi> h)
   = sqrt ((\<Sum>h\<in>UNIV. (dist_inv Q (I h) (R h (U h) *\<^sub>V \<psi> h))\<^sup>2) / real CARD('a))\<close>
    by (simp add: dist_inv_avg_def)
  also have \<open>\<dots> \<le> sqrt ((\<Sum>h\<in>UNIV. (norm (U h) * dist_inv Q (I h) (\<psi> h))\<^sup>2) / real CARD('a))\<close>
    by (auto intro!: divide_right_mono sum_mono dist_inv_apply_compatible assms)
  also have \<open>\<dots> \<le> sqrt ((\<Sum>h\<in>UNIV. ((MAX h. norm (U h)) * dist_inv Q (I h) (\<psi> h))\<^sup>2) / real CARD('a))\<close>
    by (auto intro!: divide_right_mono power_mono sum_mono mult_right_mono)
  also have \<open>\<dots> = (MAX h. norm (U h)) * sqrt ((\<Sum>h\<in>UNIV. (dist_inv Q (I h) (\<psi> h))\<^sup>2) / real CARD('a))\<close>
    by (simp add: power_mult_distrib real_sqrt_mult real_sqrt_abs abs_of_nonneg flip: sum_distrib_left times_divide_eq_right)
  also have \<open>\<dots> = (MAX h. norm (U h)) * dist_inv_avg Q I \<psi>\<close>
    by (simp add: dist_inv_avg_def)
  finally show ?thesis
    by -
qed



end
