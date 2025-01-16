section \<open>Quantum instantiation of complements\<close>

theory Axioms_Complement_Quantum
  imports
    Laws_Quantum
    Quantum_Extra
    Hilbert_Space_Tensor_Product.Weak_Star_Topology
    Hilbert_Space_Tensor_Product.Partial_Trace
    With_Type.With_Type
    Hilbert_Space_Tensor_Product.Misc_Tensor_Product_TTS
begin

unbundle no m_inv_syntax
unbundle cblinfun_syntax
unbundle lattice_syntax
unbundle register_syntax
no_notation Lattice.join (infixl "\<squnion>\<index>" 65)
no_notation elt_set_eq (infix "=o" 50)
no_notation eq_closure_of ("closure'_of\<index>")
hide_const (open) Order.top
declare [[eta_contract]]












(* (* TODO: can we use a generic rule similar to sum_parametric' instead? *)
lemma has_sum_weak_star_transfer[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_weak_star) ===> (rel_set R) ===> cr_cblinfun_weak_star ===> (\<longleftrightarrow>)) (has_sum_in weak_star_topology) has_sum\<close>
  unfolding has_sum_euclidean_iff[symmetric]
  by transfer_prover
 *)

(* lemma summable_on_weak_star_transfer[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_weak_star) ===> (rel_set R) ===> (\<longleftrightarrow>)) (summable_on_in weak_star_topology) Infinite_Sum.summable_on\<close>
(* TODO: can we use a generic rule similar to sum_parametric' instead? *)
  unfolding summable_on_def summable_on_in_def
  by transfer_prover
 *)

(* lemma infsum_weak_star_transfer[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> cr_cblinfun_weak_star) ===> (rel_set R) ===> cr_cblinfun_weak_star) (infsum_in weak_star_topology) infsum\<close>
(* TODO: can we use a generic rule similar to sum_parametric' instead? *)
proof (intro rel_funI, rename_tac f g A B)
  fix f :: \<open>'a \<Rightarrow> 'c \<Rightarrow>\<^sub>C\<^sub>L 'd\<close> and g A B
  assume [transfer_rule]: \<open>(R ===> cr_cblinfun_weak_star) f g\<close>
  assume [transfer_rule]: \<open>rel_set R A B\<close>
  show \<open>cr_cblinfun_weak_star (infsum_in Weak_Star_Topology.weak_star_topology f A) (infsum g B)\<close>
  proof (cases \<open>g summable_on B\<close>)
    case True
    then have True': \<open>summable_on_in weak_star_topology f A\<close>
      apply transfer by simp
    define a b where \<open>a = infsum_in weak_star_topology f A\<close> and \<open>b = infsum g B\<close>
    from True' have 1: \<open>has_sum_in weak_star_topology f A a\<close>
      by (simp add: a_def has_sum_in_infsum_in)
    from True have \<open>has_sum g B b\<close>
      using b_def summable_iff_has_sum_infsum by blast
    then have 2: \<open>b' = b\<close> if \<open>has_sum g B b'\<close> for b'
      using infsumI that by blast
    from 1 2 show \<open>cr_cblinfun_weak_star a b\<close>
      unfolding cr_cblinfun_weak_star_def
      apply transfer
      by simp
  next
    case False
    then have False': \<open>\<not> summable_on_in weak_star_topology f A\<close>
      apply transfer by simp
    then show ?thesis
      by (simp add: False infsum_not_exists not_summable_infsum_in_0 zero_cblinfun_weak_star.transfer)
  qed
qed
 *)

(* lemma map_filter_on_id: \<open>map_filter_on S (\<lambda>x. x) F = F\<close> if \<open>\<forall>\<^sub>F x in F. x \<in> S\<close>
  using that
  by (auto intro!: filter_eq_iff[THEN iffD2] simp: eventually_map_filter_on eventually_frequently_simps)
 *)

(* lemma inverse_real_inverse: \<open>inverse_real_inst.inverse_real = inverse\<close>
  by (simp add: HOL.nitpick_unfold)
 *)

(* lemma top_filter_parametric':
  assumes \<open>Domainp r = S\<close>
  assumes \<open>right_total r\<close>
  shows \<open>rel_filter r (principal (Collect S)) \<top>\<close>
proof (rule rel_filter.intros)
  define Z where \<open>Z = principal {(x,y). r x y}\<close>
  show \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    by (simp add: eventually_principal Z_def)
  show \<open>map_filter_on {(x, y). r x y} fst Z = principal (Collect S)\<close>
    using \<open>Domainp r = S\<close> by (auto simp add: filter_eq_iff eventually_principal Z_def eventually_map_filter_on)
  show \<open>map_filter_on {(x, y). r x y} snd Z = \<top>\<close>
    apply (auto simp add: filter_eq_iff eventually_principal Z_def eventually_map_filter_on)
    by (metis assms(2) right_totalE)
qed
 *)

(* 
lemma Inf_filter_parametric'[transfer_rule]:
  includes lifting_syntax
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes \<open>Domainp r = S\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(rel_set (rel_filter r) ===> rel_filter r)
     (\<lambda>M. inf (Inf M) (principal (Collect S)))
     Inf\<close>
proof (rule rel_funI)
  fix Fs Gs
  assume asm[transfer_rule]: \<open>rel_set (rel_filter r) Fs Gs\<close>
  show \<open>rel_filter r (inf (Inf Fs) (principal (Collect S))) (Inf Gs)\<close>
  proof (cases \<open>Fs = {}\<close>)
    case True
    then have \<open>Gs = {}\<close>
      by (metis asm empty_iff equals0I rel_setD2)
    show ?thesis
      using assms by (simp add: True \<open>Gs = {}\<close> top_filter_parametric')
  next
    case False
    then have \<open>Gs \<noteq> {}\<close>
      by (metis asm ex_in_conv rel_setD1)
    have dom: \<open>Domainp (rel_filter r) F = (F \<le> principal (Collect S))\<close> for F
      by (simp add: Domainp_rel_filter assms(1))
    have 1: \<open>(rel_filter r)
       (Sup {F. Ball Fs ((\<le>) F) \<and> Domainp (rel_filter r) F})
       (Inf Gs)\<close> (is \<open>(rel_filter r) ?I _\<close>)
      unfolding Inf_filter_def[abs_def]
      by transfer_prover
    have \<open>F \<le> principal (Collect S)\<close> if \<open>F \<in> Fs\<close> for F
      by (meson DomainPI asm dom rel_setD1 that)
    have \<open>?I = (inf (Inf Fs) (principal (Collect S)))\<close>
      unfolding dom Inf_filter_def
      apply auto
      apply (rule antisym)
      apply auto
        apply (simp add: Collect_mono_iff Sup_subset_mono)
      apply (metis (no_types, lifting) Sup_least mem_Collect_eq)
      by (smt (verit, del_insts) Collect_mono False Sup_subset_mono \<open>\<And>Fa. Fa \<in> Fs \<Longrightarrow> Fa \<le> principal (Collect S)\<close> bot.extremum_unique dual_order.refl inf.bounded_iff order_trans subsetI)
    show ?thesis
      using "1" \<open>Sup {F. Ball Fs ((\<le>) F) \<and> Domainp (rel_filter r) F} = inf (Inf Fs) (principal (Collect S))\<close> by fastforce
  qed
qed
 *)


(* 
lemma inf_filter_parametric'[transfer_rule]:
  includes lifting_syntax
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(rel_filter r ===> rel_filter r ===> rel_filter r)
     inf inf\<close>
proof (rule rel_funI, rule rel_funI, rename_tac F1 F2 G1 G2)
  fix F1 F2 G1 G2
  assume asmF[transfer_rule]: \<open>rel_filter r F1 F2\<close>
  assume asmG[transfer_rule]: \<open>rel_filter r G1 G2\<close>
  then have *: \<open>G1 \<le> principal (Collect (Domainp r))\<close>
    by (meson Domainp.intros Domainp_rel_filter)
  have \<open>rel_filter r (Inf {F1,G1} \<sqinter> principal (Collect (Domainp r))) (Inf {F2,G2})\<close>
    by transfer_prover
  with * show \<open>rel_filter r (inf F1 G1) (inf F2 G2)\<close>
    by (auto simp: inf_assoc inf.absorb_iff1)
qed
 *)


(* lemma convergent_ow_typeclass2[simp]:
  assumes \<open>open V\<close>
  shows \<open>convergent_ow V (openin (top_of_set V)) f \<longleftrightarrow> (\<exists>l. f \<longlonglongrightarrow> l \<and> l \<in> V)\<close>
  by (simp add: limitin_canonical_iff_gen assms)
 *)

(* lemma convergent_on_typeclass3[simp]:
  assumes \<open>open V\<close> \<open>closed V\<close> \<open>range f \<subseteq> V\<close>
  shows \<open>convergent_ow V (openin (top_of_set V)) f \<longleftrightarrow> convergent f\<close>
  apply (simp add: assms)
  by (meson assms(2) assms(3) closed_sequentially convergent_def range_subsetD)
 *)

(* lemma cmod_distrib_plus: \<open>a \<ge> 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> cmod (a + b) = cmod a + cmod b\<close>
  by (simp add: cmod_Re) *)

lemma register_decomposition_converse:
  assumes \<open>unitary U\<close>
  shows \<open>register (\<lambda>x. sandwich U (id_cblinfun \<otimes>\<^sub>o x))\<close>
  using _ unitary_sandwich_register apply (rule register_comp[unfolded o_def])
  using assms by auto

lemma iso_register_decomposition:
  assumes [simp]: \<open>iso_register F\<close>
  shows \<open>\<exists>U. unitary U \<and> F = sandwich U\<close>
proof -
  from register_decomposition
  have \<open>let 'c::type = register_decomposition_basis F in
        \<exists>U. unitary U \<and> F = sandwich U\<close>
  proof with_type_mp
    show [simp]: \<open>register F\<close>
      using assms iso_register_is_register by blast 
    with_type_case

(*     assume register_decomposition:
      \<open>\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. F \<theta> = Complex_Bounded_Linear_Function.sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>
 *)
    let ?ida = \<open>id_cblinfun :: 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>

    from with_type_mp.premise
    obtain V :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where \<open>unitary V\<close>
      and FV: \<open>F \<theta> = sandwich V (\<theta> \<otimes>\<^sub>o ?ida)\<close> for \<theta>
      by auto

    have inj_V: \<open>inj ((*\<^sub>V) (sandwich V))\<close>
      by (meson \<open>unitary V\<close> register_inj unitary_sandwich_register)
    have \<open>surj F\<close>
      by (meson assms iso_register_inv_comp2 surj_iff)
    have surj_tensor: \<open>surj (\<lambda>a::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2. a \<otimes>\<^sub>o ?ida)\<close>
      apply (rule surj_from_comp[where g=\<open>sandwich V\<close>])
      using \<open>surj F\<close> inj_V by (auto simp: FV)
    then obtain a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> 
      where a: \<open>a \<otimes>\<^sub>o ?ida = butterfly (ket undefined) (ket undefined) \<otimes>\<^sub>o butterfly (ket undefined) (ket undefined)\<close>
      by (smt (verit, best) surjD)

    have \<open>selfbutter (ket (undefined, undefined)) \<noteq> 0\<close>
      by (metis butterfly_apply cblinfun.zero_left complex_vector.scale_eq_0_iff ket_nonzero orthogonal_ket)
    with a have \<open>a \<noteq> 0\<close>
      by (auto simp: tensor_ell2_ket tensor_butterfly)


    obtain \<gamma> where \<gamma>: \<open>?ida = \<gamma> *\<^sub>C butterfly (ket undefined) (ket undefined)\<close>
      apply atomize_elim
      using a \<open>a \<noteq> 0\<close> by (rule tensor_op_almost_injective)
    then have \<open>?ida (ket undefined) = \<gamma> *\<^sub>C (butterfly (ket undefined) (ket undefined) *\<^sub>V ket undefined)\<close>
      by (simp add: \<open>id_cblinfun = \<gamma> *\<^sub>C butterfly (ket undefined) (ket undefined)\<close> scaleC_cblinfun.rep_eq)
    then have \<open>ket undefined = \<gamma> *\<^sub>C ket undefined\<close>
      by (metis butterfly_apply cinner_ket_same id_cblinfun_apply ket_nonzero scaleC_cancel_right scaleC_one)
    then have \<open>\<gamma> = 1\<close>
      by (smt (z3) \<gamma> butterfly_apply butterfly_scaleC_left cblinfun_id_cblinfun_apply complex_vector.scale_cancel_right cinner_ket_same ket_nonzero)

    define T U where \<open>T = CBlinfun (\<lambda>\<psi>. \<psi> \<otimes>\<^sub>s ket undefined)\<close> and \<open>U = V o\<^sub>C\<^sub>L T\<close>
    have T: \<open>T \<psi> = \<psi> \<otimes>\<^sub>s ket undefined\<close> for \<psi>
      unfolding T_def
      apply (subst bounded_clinear_CBlinfun_apply)
      by (auto intro!: bounded_clinear_tensor_ell22)
    have \<open>sandwich T (butterfly (ket i) (ket j)) = butterfly (ket i) (ket j) \<otimes>\<^sub>o id_cblinfun\<close> for i j
      by (simp add: T sandwich_apply cblinfun_comp_butterfly butterfly_comp_cblinfun \<gamma> \<open>\<gamma> = 1\<close> tensor_butterfly)
    then have sandwich_T: \<open>sandwich T a = a \<otimes>\<^sub>o ?ida\<close> for a
      apply (rule_tac fun_cong[where x=a])
      apply (rule weak_star_clinear_eq_butterfly_ketI[where T=weak_star_topology])
      by auto

    have \<open>F (butterfly x y) = V o\<^sub>C\<^sub>L (butterfly x y \<otimes>\<^sub>o ?ida) o\<^sub>C\<^sub>L V*\<close> for x y
      by (simp add: sandwich_apply FV)
    also have \<open>\<dots> x y = V o\<^sub>C\<^sub>L (butterfly (T x) (T y)) o\<^sub>C\<^sub>L V*\<close> for x y
      by (simp add: T \<gamma> \<open>\<gamma> = 1\<close> tensor_butterfly)
    also have \<open>\<dots> x y = U o\<^sub>C\<^sub>L (butterfly x y) o\<^sub>C\<^sub>L U*\<close> for x y
      by (simp add: U_def butterfly_comp_cblinfun cblinfun_comp_butterfly)
    finally have F_rep:  \<open>F a = U o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L U*\<close> for a
      apply (rule_tac fun_cong[where x=a])
      apply (rule weak_star_clinear_eq_butterfly_ketI[where T=weak_star_topology])
      by (auto simp: clinear_register weak_star_cont_register simp flip: sandwich_apply)

    have \<open>isometry T\<close>
      apply (rule orthogonal_on_basis_is_isometry[where B=\<open>range ket\<close>])
      by (auto simp: T)
    moreover have \<open>T *\<^sub>S \<top> = \<top>\<close>
    proof -
      have 1: \<open>\<phi> \<otimes>\<^sub>s \<xi> \<in> range ((*\<^sub>V) T)\<close> for \<phi> \<xi>
      proof -
        have \<open>T *\<^sub>V (cinner (ket undefined) \<xi> *\<^sub>C \<phi>) = \<phi> \<otimes>\<^sub>s (cinner (ket undefined) \<xi> *\<^sub>C ket undefined)\<close>
          by (simp add: T tensor_ell2_scaleC1 tensor_ell2_scaleC2)
        also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s (butterfly (ket undefined) (ket undefined) *\<^sub>V \<xi>)\<close>
          by simp
        also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s (?ida *\<^sub>V \<xi>)\<close>
          by (simp add: \<gamma> \<open>\<gamma> = 1\<close>)
        also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s \<xi>\<close>
          by simp
        finally show ?thesis
          by (metis range_eqI)
      qed

      have \<open>\<top> \<le> ccspan {ket x | x. True}\<close>
        by (simp add: full_SetCompr_eq)
      also have \<open>\<dots> \<le> ccspan {\<phi> \<otimes>\<^sub>s \<xi> | \<phi> \<xi>. True}\<close>
        apply (rule ccspan_mono)
        by (auto simp flip: tensor_ell2_ket)
      also from 1 have \<open>\<dots> \<le> ccspan (range ((*\<^sub>V) T))\<close>
        by (auto intro!: ccspan_mono)
      also have \<open>\<dots> = T *\<^sub>S \<top>\<close>
        by (metis (mono_tags, opaque_lifting) calculation cblinfun_image_ccspan cblinfun_image_mono eq_iff top_greatest)
      finally show \<open>T *\<^sub>S \<top> = \<top>\<close>
        using top.extremum_uniqueI by blast
    qed

    ultimately have \<open>unitary T\<close>
      by (rule surj_isometry_is_unitary)
    then have \<open>unitary U\<close>
      by (simp add: U_def \<open>unitary V\<close>)

    from F_rep \<open>unitary U\<close> show \<open>\<exists>U. unitary U \<and> F = sandwich U\<close>
      by (auto simp: sandwich_apply[abs_def])
  qed
  from this[THEN with_type_prepare_cancel, cancel_type_definition, OF with_type_nonempty, OF this]
  show ?thesis
    by -
qed

lemma complement_exists:
  fixes F :: \<open>'a update \<Rightarrow> 'b update\<close>
  assumes \<open>register F\<close>
  shows \<open>let 'c::type = register_decomposition_basis F in
         \<exists>G :: 'c update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G)\<close>
proof (use register_decomposition[OF \<open>register F\<close>] in \<open>rule with_type_mp\<close>)
  note [[simproc del: Laws_Quantum.compatibility_warn]]
  assume register_decomposition: \<open>\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. F \<theta> = Complex_Bounded_Linear_Function.sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>
  then obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    where [simp]: "unitary U" and F: \<open>F a = sandwich U (a \<otimes>\<^sub>o id_cblinfun)\<close> for a
    by auto
  define G :: \<open>'c update \<Rightarrow> 'b update\<close> where \<open>G b = sandwich U (id_cblinfun \<otimes>\<^sub>o b)\<close> for b
  have [simp]: \<open>register G\<close>
    unfolding G_def apply (rule register_decomposition_converse) by simp
  have \<open>F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a\<close> for a b
  proof -
    have \<open>F a o\<^sub>C\<^sub>L G b = sandwich U (a \<otimes>\<^sub>o b)\<close>
      by (auto simp: F G_def sandwich_apply cblinfun_assoc_right
          \<open>unitary U\<close> lift_cblinfun_comp[OF unitaryD1]
          lift_cblinfun_comp[OF comp_tensor_op])
    moreover have \<open>G b o\<^sub>C\<^sub>L F a = sandwich U (a \<otimes>\<^sub>o b)\<close>
      by (auto simp: F G_def sandwich_apply cblinfun_assoc_right
          \<open>unitary U\<close> lift_cblinfun_comp[OF unitaryD1]
          lift_cblinfun_comp[OF comp_tensor_op])
    ultimately show ?thesis by simp
  qed
  then have [simp]: \<open>compatible F G\<close>
    by (auto simp: compatible_def \<open>register F\<close>)
  moreover have \<open>iso_register (F;G)\<close>
  proof -
    have \<open>(F;G) (a \<otimes>\<^sub>o b) = sandwich U (a \<otimes>\<^sub>o b)\<close> for a b
      by (auto simp: register_pair_apply F G_def sandwich_apply cblinfun_assoc_right
          \<open>unitary U\<close> lift_cblinfun_comp[OF unitaryD1]
          lift_cblinfun_comp[OF comp_tensor_op])
    then have FG: \<open>(F;G) = sandwich U\<close>
      apply (rule tensor_extensionality[rotated -1])
      by (simp_all add: unitary_sandwich_register)
    define I where \<open>I = sandwich (U*)\<close> for x
    have [simp]: \<open>register I\<close>
      by (simp add: I_def unitary_sandwich_register)
    have \<open>I o (F;G) = id\<close> and FGI: \<open>(F;G) o I = id\<close>
      by (auto intro!:ext simp: I_def[abs_def] FG sandwich_apply cblinfun_assoc_right
          \<open>unitary U\<close> lift_cblinfun_comp[OF unitaryD1] lift_cblinfun_comp[OF unitaryD2]
          lift_cblinfun_comp[OF comp_tensor_op])
    then show \<open>iso_register (F;G)\<close>
      by (auto intro!: iso_registerI)
  qed
  ultimately show \<open>\<exists>G :: 'c update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G)\<close>
    apply (rule_tac exI[of _ G]) by auto
qed

lemma commutant_exchange:
  fixes F :: \<open>'a update \<Rightarrow> 'b update\<close>
  assumes \<open>iso_register F\<close>
  shows \<open>commutant (F ` X) = F ` commutant X\<close>
proof (rule Set.set_eqI)
  fix x :: \<open>'b update\<close>
  from assms
  obtain G where \<open>F o G = id\<close> and \<open>G o F = id\<close> and [simp]: \<open>register G\<close>
    using iso_register_def by blast
  from assms have [simp]: \<open>register F\<close>
    using iso_register_def by blast
  have \<open>x \<in> commutant (F ` X) \<longleftrightarrow> (\<forall>y \<in> F ` X. x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x)\<close>
    by (simp add: commutant_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y \<in> F ` X. G x o\<^sub>C\<^sub>L G y = G y o\<^sub>C\<^sub>L G x)\<close>
    by (metis (no_types, opaque_lifting) \<open>F \<circ> G = id\<close> \<open>G o F = id\<close> \<open>register G\<close> comp_def eq_id_iff register_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>y \<in> X. G x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L G x)\<close>
    by (simp add: \<open>G \<circ> F = id\<close> pointfree_idE)
  also have \<open>\<dots> \<longleftrightarrow> G x \<in> commutant X\<close>
    by (simp add: commutant_def)
  also have \<open>\<dots> \<longleftrightarrow> x \<in> F ` commutant X\<close>
    by (metis (no_types, opaque_lifting) \<open>G \<circ> F = id\<close> \<open>F \<circ> G = id\<close> image_iff pointfree_idE)
  finally show \<open>x \<in> commutant (F ` X) \<longleftrightarrow> x \<in> F ` commutant X\<close>
    by -
qed

lemma complement_range:
  assumes [simp]: \<open>compatible F G\<close> and [simp]: \<open>iso_register (F;G)\<close>
  shows \<open>range G = commutant (range F)\<close>
proof -
  have [simp]: \<open>register F\<close> \<open>register G\<close>
    using assms compatible_def by metis+
  have [simp]: \<open>(F;G) (a \<otimes>\<^sub>o b) = F a o\<^sub>C\<^sub>L G b\<close> for a b
    using Laws_Quantum.register_pair_apply assms by blast
  have [simp]: \<open>range F = (F;G) ` range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)\<close>
    by force
  have [simp]: \<open>range G = (F;G) ` range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
    by force
  show \<open>range G = commutant (range F)\<close>
    by (simp add: commutant_exchange commutant_tensor1)
qed

(* lemma isCont_iff_preserves_convergence:
  assumes \<open>\<And>F. (id \<longlongrightarrow> a) F \<Longrightarrow> (f \<longlongrightarrow> f a) F\<close>
  shows \<open>isCont f a\<close>
  using assms
  by (simp add: isCont_def Lim_at_id) *)


lemma register_inv_G_o_F: 
  assumes [simp]: \<open>register F\<close> and [simp]: \<open>register G\<close> and range_FG: \<open>range F \<subseteq> range G\<close>
  shows \<open>register (inv G \<circ> F)\<close>
proof -
  note [[simproc del: Laws_Quantum.compatibility_warn]]
  define GF where \<open>GF = inv G o F\<close>
  have F_rangeG[simp]: \<open>F x \<in> range G\<close> for x
   using range_FG by auto
  have [simp]: \<open>inj F\<close> and [simp]: \<open>inj G\<close>
    by (simp_all add: register_inj)
  have [simp]: \<open>bounded_clinear F\<close> \<open>bounded_clinear G\<close>
    by (simp_all add: register_bounded_clinear)
  have [simp]: \<open>clinear F\<close> \<open>clinear G\<close>
    by (simp_all add: bounded_clinear.clinear)
  have addJ: \<open>GF (x + y) = GF x + GF y\<close> for x y
    unfolding GF_def o_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst complex_vector.linear_add[OF \<open>clinear G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    by (simp add: complex_vector.linear_add)
  have scaleJ: \<open>GF (r *\<^sub>C x) = r *\<^sub>C GF x\<close> for r x
    unfolding GF_def o_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst complex_vector.linear_scale[OF \<open>clinear G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    by (simp add: complex_vector.linear_scale)
  have unitalJ: \<open>GF id_cblinfun = id_cblinfun\<close>
    unfolding GF_def o_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G])
    by (auto intro!: range_eqI[of _ _ id_cblinfun]) 
  have multJ: \<open>GF (a o\<^sub>C\<^sub>L b) = GF a o\<^sub>C\<^sub>L GF b\<close> for a b
    unfolding GF_def o_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst register_mult[symmetric, OF \<open>register G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    by (simp add: register_mult)
  have adjJ: \<open>GF (a*) = (GF a)*\<close> for a
    unfolding GF_def o_def
    apply (rule injD[OF \<open>inj G\<close>])
    apply (subst register_adjoint[OF \<open>register G\<close>])
    apply (subst Hilbert_Choice.f_inv_into_f[where f=G], simp)+
    using \<open>register F\<close> register_adjoint by blast
  have normJ: \<open>norm (GF a) = norm a\<close> for a
    unfolding GF_def
    by (metis F_rangeG \<open>register F\<close> \<open>register G\<close> f_inv_into_f o_def register_norm)
  have weak_star_J: \<open>continuous_map weak_star_topology weak_star_topology GF\<close>
  proof -
    have \<open>continuous_map weak_star_topology weak_star_topology F\<close>
      by (simp add: weak_star_cont_register)
    then have \<open>continuous_map weak_star_topology (subtopology weak_star_topology (range F)) F\<close>
      by (simp add: continuous_map_into_subtopology)
    moreover have \<open>continuous_map (subtopology weak_star_topology (range G)) weak_star_topology (inv G)\<close>
      using \<open>register G\<close> register_inv_weak_star_continuous by blast
    ultimately show \<open>continuous_map weak_star_topology weak_star_topology GF\<close>
      by (simp add: GF_def range_FG continuous_map_compose continuous_map_from_subtopology_mono)
  qed

  from addJ scaleJ unitalJ multJ adjJ normJ weak_star_J
  show \<open>register GF\<close>
    unfolding register_def by (auto intro!: bounded_clinearI[where K=1])
qed


lemma same_range_equivalent:
  fixes F :: \<open>'a update \<Rightarrow> 'c update\<close> and G :: \<open>'b update \<Rightarrow> 'c update\<close>
  assumes [simp]: \<open>register F\<close> and [simp]: \<open>register G\<close>
  assumes range_FG: \<open>range F = range G\<close>
  shows \<open>equivalent_registers F G\<close>
proof -
  note [[simproc del: Laws_Quantum.compatibility_warn]]
  have regGF: \<open>register (inv G o F)\<close>
    using assms by (auto intro!: register_inv_G_o_F)
  have regFG: \<open>register (inv F o G)\<close>
    using assms by (auto intro!: register_inv_G_o_F)
  have \<open>inj G\<close>
    by (simp add: register_inj)
  with range_FG have GFFG: \<open>(inv G o F) o (inv F o G) = id\<close>
    by (smt (verit) assms(1) f_inv_into_f invI isomorphism_expand o_def rangeI register_inj)
  have \<open>inj F\<close>
    by (simp add: register_inj)
  with range_FG have FGGF: \<open>(inv F o G) o (inv G o F) = id\<close>
    by (metis GFFG fun.set_map image_inv_f_f left_right_inverse_eq surj_iff)
  from regGF regFG GFFG FGGF have iso_FG: \<open>iso_register (inv F o G)\<close>
    using iso_registerI by auto
  have FFG: \<open>F o (inv F o G) = G\<close>
    by (smt (verit) FGGF GFFG fun.inj_map_strong fun.map_comp fun.set_map image_inv_f_f inj_on_imageI2 inv_id inv_into_injective inv_o_cancel o_inv_o_cancel range_FG surj_id surj_imp_inj_inv)
  from FFG iso_FG show \<open>equivalent_registers F G\<close>
    by (simp add: equivalent_registersI)
qed

lemma complement_unique:
  assumes "compatible F G" and \<open>iso_register (F;G)\<close>
  assumes "compatible F H" and \<open>iso_register (F;H)\<close>
  shows \<open>equivalent_registers G H\<close>
  by (metis assms compatible_def complement_range same_range_equivalent)

















subsection \<open>Finite dimensional complement\<close>

typedef ('a, 'b::finite) complement_domain_simple = \<open>{..< if CARD('b) div CARD('a) \<noteq> 0 then CARD('b) div CARD('a) else 1}\<close>
  by auto

instance complement_domain_simple :: (type, finite) finite
proof intro_classes
  have \<open>inj Rep_complement_domain_simple\<close>
    by (simp add: Rep_complement_domain_simple_inject inj_on_def)
  moreover have \<open>finite (range Rep_complement_domain_simple)\<close>
    by (metis finite_lessThan type_definition.Rep_range type_definition_complement_domain_simple)
  ultimately show \<open>finite (UNIV :: ('a,'b) complement_domain_simple set)\<close>
    using finite_image_iff by blast
qed

lemma CARD_complement_domain: 
  assumes \<open>CARD('b::finite) = n * CARD('a)\<close>
  shows \<open>CARD(('a,'b) complement_domain_simple) = n\<close>
proof -
  from assms have \<open>n > 0\<close>
    by (metis nat_0_less_mult_iff zero_less_card_finite)
  have *: \<open>inj Rep_complement_domain_simple\<close>
    by (simp add: Rep_complement_domain_simple_inject inj_on_def)
  moreover have \<open>card (range (Rep_complement_domain_simple :: ('a,'b) complement_domain_simple \<Rightarrow> _)) = n\<close>
    apply (subst type_definition.Rep_range[OF type_definition_complement_domain_simple])
    using assms \<open>n > 0\<close> apply simp
    by force
  ultimately show ?thesis
    by (metis card_image)
qed



lemma register_decomposition_finite_aux:
  fixes \<Phi> :: \<open>'a::finite update \<Rightarrow> 'b::finite update\<close>
  assumes [simp]: \<open>register \<Phi>\<close>
  shows \<open>\<exists>U :: ('a \<times> ('a, 'b) complement_domain_simple) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> 
              (\<forall>\<theta>. \<Phi> \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>
  \<comment> \<open>Proof based on \<^cite>\<open>daws21unitalanswer\<close>\<close>
proof -
  note [[simproc del: compatibility_warn]]
  fix \<xi>0 :: 'a

  have [simp]: \<open>clinear \<Phi>\<close>
    by (simp add: clinear_register)

  define P where \<open>P i = Proj (ccspan {ket i})\<close> for i :: 'a
  have P_butter: \<open>P i = butterfly (ket i) (ket i)\<close> for i
    by (simp add: P_def butterfly_eq_proj)

  define P' where \<open>P' i = \<Phi> (P i)\<close> for i :: 'a
  have proj_P': \<open>is_Proj (P' i)\<close> for i
    by (simp add: P_def P'_def register_projector)
  have \<open>(\<Sum>i\<in>UNIV. P i) = id_cblinfun\<close>
    using sum_butterfly_ket P_butter by simp
  then have sumP'id: \<open>(\<Sum>i\<in>UNIV. P' i) = id_cblinfun\<close>
    unfolding P'_def 
    apply (subst complex_vector.linear_sum[OF \<open>clinear \<Phi>\<close>, symmetric])
    by auto

  define S where \<open>S i = P' i *\<^sub>S \<top>\<close> for i :: 'a
  have P'id: \<open>P' i *\<^sub>V \<psi> = \<psi>\<close> if \<open>\<psi> \<in> space_as_set (S i)\<close> for i \<psi>
    using S_def that proj_P'
    by (metis cblinfun_fixes_range is_Proj_algebraic)

  obtain B0 where finiteB0: \<open>finite (B0 i)\<close> and cspanB0: \<open>cspan (B0 i) = space_as_set (S i)\<close> for i
    apply atomize_elim apply (simp flip: all_conj_distrib) apply (rule choice)
    by (meson cfinite_dim_finite_subspace_basis csubspace_space_as_set)

  obtain B where orthoB: \<open>is_ortho_set (B i)\<close>
    and normalB: \<open>\<And>b. b \<in> B i \<Longrightarrow> norm b = 1\<close>
    and cspanB: \<open>cspan (B i) = cspan (B0 i)\<close>
    and finiteB: \<open>finite (B i)\<close> for i
    apply atomize_elim apply (simp flip: all_conj_distrib) apply (rule choice)
    using orthonormal_basis_of_cspan[OF finiteB0] by blast

  from cspanB cspanB0 have cspanB: \<open>cspan (B i) = space_as_set (S i)\<close> for i
    by simp
  then have ccspanB: \<open>ccspan (B i) = S i\<close> for i
    by (metis ccspan.rep_eq closure_finite_cspan finiteB space_as_set_inject)
  from orthoB have indepB: \<open>cindependent (B i)\<close> for i
    by (simp add: Complex_Inner_Product.is_ortho_set_cindependent)

  have orthoBiBj: \<open>is_orthogonal x y\<close> if \<open>x \<in> B i\<close> and \<open>y \<in> B j\<close> and \<open>i \<noteq> j\<close> for x y i j
  proof -
    from \<open>x \<in> B i\<close> obtain x' where x: \<open>x = P' i *\<^sub>V x'\<close>
      by (metis S_def cblinfun_fixes_range complex_vector.span_base cspanB is_Proj_idempotent proj_P')
    from \<open>y \<in> B j\<close> obtain y' where y: \<open>y = P' j *\<^sub>V y'\<close>
      by (metis S_def cblinfun_fixes_range complex_vector.span_base cspanB is_Proj_idempotent proj_P')
    have \<open>cinner x y = cinner (P' i *\<^sub>V x') (P' j *\<^sub>V  y')\<close>
      using x y by simp
    also have \<open>\<dots> = cinner (P' j *\<^sub>V P' i *\<^sub>V x') y'\<close>
      by (metis cinner_adj_left is_Proj_algebraic proj_P')
    also have \<open>\<dots> = cinner (\<Phi> (P j o\<^sub>C\<^sub>L P i) *\<^sub>V x') y'\<close>
      unfolding P'_def register_mult[OF \<open>register \<Phi>\<close>, symmetric] by simp
    also have \<open>\<dots> = cinner (\<Phi> (butterfly (ket j) (ket j) o\<^sub>C\<^sub>L butterfly (ket i) (ket i)) *\<^sub>V x') y'\<close>
      unfolding P_butter by simp
    also have \<open>\<dots> = cinner (\<Phi> 0 *\<^sub>V x') y'\<close>
      by (metis butterfly_comp_butterfly complex_vector.scale_eq_0_iff orthogonal_ket that(3))
    also have \<open>\<dots> = 0\<close>
      by (simp add: complex_vector.linear_0)
    finally show ?thesis
      by -
  qed


  define B' where \<open>B' = (\<Union>i\<in>UNIV. B i)\<close>

  have P'B: \<open>P' i = Proj (ccspan (B i))\<close> for i
    unfolding ccspanB S_def
    using proj_P' Proj_on_own_range'[symmetric] is_Proj_algebraic by blast

  have \<open>(\<Sum>i\<in>UNIV. P' i) = Proj (ccspan B')\<close>
  proof (unfold B'_def, use finite[of UNIV] in induction)
    case empty
    show ?case by auto
  next
    case (insert j M)
    have \<open>(\<Sum>i\<in>insert j M. P' i) = P' j + (\<Sum>i\<in>M. P' i)\<close>
      by (meson insert.hyps(1) insert.hyps(2) sum.insert)
    also have \<open>\<dots> = Proj (ccspan (B j)) + Proj (ccspan (\<Union>i\<in>M. B i))\<close>
      unfolding P'B insert.IH[symmetric] by simp
    also have \<open>\<dots> = Proj (ccspan (B j \<union> (\<Union>i\<in>M. B i)))\<close>
      apply (rule Proj_orthog_ccspan_union[symmetric])
      using orthoBiBj insert.hyps(2) by auto
    also have \<open>\<dots> = Proj (ccspan (\<Union>i\<in>insert j M. B i))\<close>
      by auto
    finally show ?case
      by simp
  qed

  with sumP'id 
  have ccspanB': \<open>ccspan B' = \<top>\<close>
    by (metis Proj_range cblinfun_image_id)
  hence cspanB': \<open>cspan B' = UNIV\<close>
    by (metis B'_def finiteB ccspan.rep_eq finite_UN_I finite_class.finite_UNIV closure_finite_cspan top_ccsubspace.rep_eq)

  from orthoBiBj orthoB have orthoB': \<open>is_ortho_set B'\<close>
    unfolding B'_def is_ortho_set_def by blast
  then have indepB': \<open>cindependent B'\<close>
    using is_ortho_set_cindependent by blast
  have cardB': \<open>card B' = CARD('b)\<close>
    apply (subst complex_vector.dim_span_eq_card_independent[symmetric])
     apply (rule indepB')
    apply (subst cspanB')
    using cdim_UNIV_ell2 by auto

  from orthoBiBj orthoB
  have Bdisj: \<open>B i \<inter> B j = {}\<close> if \<open>i \<noteq> j\<close> for i j
    unfolding is_ortho_set_def
    using that by fastforce

  have cardBsame: \<open>card (B i) = card (B j)\<close> for i j
  proof -
    define Si_to_Sj where \<open>Si_to_Sj i j \<psi> = \<Phi> (butterfly (ket j) (ket i)) *\<^sub>V \<psi>\<close> for i j \<psi>
    have S2S2S: \<open>Si_to_Sj j i (Si_to_Sj i j \<psi>) = \<psi>\<close> if \<open>\<psi> \<in> space_as_set (S i)\<close> for i j \<psi>
      using that P'id
      by (simp add: Si_to_Sj_def cblinfun_apply_cblinfun_compose[symmetric] register_mult P_butter P'_def)
    also have lin[simp]: \<open>clinear (Si_to_Sj i j)\<close> for i j
      unfolding Si_to_Sj_def by simp
    have S2S: \<open>Si_to_Sj i j x \<in> space_as_set (S j)\<close> for i j x
    proof -
      have \<open>Si_to_Sj i j x = P' j *\<^sub>V Si_to_Sj i j x\<close>
        by (simp add: Si_to_Sj_def cblinfun_apply_cblinfun_compose[symmetric] register_mult P_butter P'_def)
      also have \<open>P' j *\<^sub>V Si_to_Sj i j x \<in> space_as_set (S j)\<close>
        by (simp add: S_def)
      finally show ?thesis by -
    qed
    have bij: \<open>bij_betw (Si_to_Sj i j) (space_as_set (S i)) (space_as_set (S j))\<close>
      apply (rule bij_betwI[where g=\<open>Si_to_Sj j i\<close>])
      using S2S S2S2S by (auto intro!: funcsetI)
    have \<open>cdim (space_as_set (S i)) = cdim (space_as_set (S j))\<close>
      using lin apply (rule isomorphic_equal_cdim[where f=\<open>Si_to_Sj i j\<close>])
      using bij by (auto simp: bij_betw_def)
    then show ?thesis
      by (metis complex_vector.dim_span_eq_card_independent cspanB indepB)
  qed

  have CARD'b: \<open>CARD('b) = card (B \<xi>0) * CARD('a)\<close>
  proof -
    have \<open>CARD('b) = card B'\<close>
      using cardB' by simp
    also have \<open>\<dots> = (\<Sum>i\<in>UNIV. card (B i))\<close>
      unfolding B'_def apply (rule card_UN_disjoint)
      using finiteB Bdisj by auto
    also have \<open>\<dots> = (\<Sum>(i::'a)\<in>UNIV. card (B \<xi>0))\<close>
      using cardBsame by metis
    also have \<open>\<dots> = card (B \<xi>0) * CARD('a)\<close>
      by auto
    finally show ?thesis by -
  qed

  obtain f where bij_f: \<open>bij_betw f (UNIV::('a,'b) complement_domain_simple set) (B \<xi>0)\<close>
    apply atomize_elim apply (rule finite_same_card_bij)
    using finiteB CARD_complement_domain[OF CARD'b] by auto

  define u where \<open>u = (\<lambda>(\<xi>,\<alpha>). \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V f \<alpha>)\<close> for \<xi> :: 'a and \<alpha> :: \<open>('a,'b) complement_domain_simple\<close>
  obtain U where Uapply: \<open>U *\<^sub>V ket \<xi>\<alpha> = u \<xi>\<alpha>\<close> for \<xi>\<alpha>
    apply atomize_elim
    apply (rule exI[of _ \<open>cblinfun_extension (range ket) (\<lambda>k. u (inv ket k))\<close>])
    apply (subst cblinfun_extension_apply)
      apply (rule cblinfun_extension_exists_finite_dim)
    by (auto simp add: inj_ket cindependent_ket)

  define eqa where \<open>eqa a b = (if a = b then 1 else 0 :: complex)\<close> for a b :: 'a
  define eqc where \<open>eqc a b = (if a = b then 1 else 0 :: complex)\<close> for a b :: \<open>('a,'b) complement_domain_simple\<close>
  define eqac where \<open>eqac a b = (if a = b then 1 else 0 :: complex)\<close> for a b :: \<open>'a * ('a,'b) complement_domain_simple\<close>

  have \<open>cinner (U *\<^sub>V ket \<xi>\<alpha>) (U *\<^sub>V ket \<xi>'\<alpha>') = eqac \<xi>\<alpha> \<xi>'\<alpha>'\<close> for \<xi>\<alpha> \<xi>'\<alpha>'
  proof -
    obtain \<xi> \<alpha> \<xi>' \<alpha>' where \<xi>\<alpha>: \<open>\<xi>\<alpha> = (\<xi>,\<alpha>)\<close> and \<xi>'\<alpha>': \<open>\<xi>'\<alpha>' = (\<xi>',\<alpha>')\<close>
      apply atomize_elim by auto
    have \<open>cinner (U *\<^sub>V ket (\<xi>,\<alpha>)) (U *\<^sub>V ket (\<xi>', \<alpha>')) = cinner (\<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V f \<alpha>) (\<Phi> (butterfly (ket \<xi>') (ket \<xi>0)) *\<^sub>V f \<alpha>')\<close>
      unfolding Uapply u_def by simp
    also have \<open>\<dots> = cinner ((\<Phi> (butterfly (ket \<xi>') (ket \<xi>0)))* *\<^sub>V \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (simp add: cinner_adj_left)
    also have \<open>\<dots> = cinner (\<Phi> (butterfly (ket \<xi>') (ket \<xi>0) *) *\<^sub>V \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (metis (no_types, lifting) assms register_def)
    also have \<open>\<dots> = cinner (\<Phi> (butterfly (ket \<xi>0) (ket \<xi>') o\<^sub>C\<^sub>L butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (simp add: register_mult cblinfun_apply_cblinfun_compose[symmetric])
    also have \<open>\<dots> = cinner (\<Phi> (eqa \<xi>' \<xi> *\<^sub>C butterfly (ket \<xi>0) (ket \<xi>0)) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (simp add: eqa_def cinner_ket) 
    also have \<open>\<dots> = eqa \<xi>' \<xi> * cinner (\<Phi> (butterfly (ket \<xi>0) (ket \<xi>0)) *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      by (smt (verit, ccfv_threshold) \<open>clinear \<Phi>\<close> eqa_def cblinfun.scaleC_left cinner_commute 
              cinner_scaleC_left cinner_zero_right complex_cnj_one complex_vector.linear_scale)
    also have \<open>\<dots> = eqa \<xi>' \<xi> * cinner (P' \<xi>0 *\<^sub>V f \<alpha>) (f \<alpha>')\<close>
      using P_butter P'_def by simp
    also have \<open>\<dots> = eqa \<xi>' \<xi> * cinner (f \<alpha>) (f \<alpha>')\<close>
      apply (subst P'id)
       apply (metis bij_betw_imp_surj_on bij_f complex_vector.span_base cspanB rangeI)
      by simp
    also have \<open>\<dots> = eqa \<xi>' \<xi> * eqc \<alpha> \<alpha>'\<close>
    proof -
      from normalB bij_f
      have aux1: \<open>f \<alpha>' \<bullet>\<^sub>C f \<alpha>' \<noteq> 1 \<Longrightarrow> eqa \<xi>' \<xi> = 0\<close>
        by (metis bij_betw_imp_surj_on cnorm_eq_1 rangeI)
      from orthoB bij_f have aux2: \<open>\<alpha> \<noteq> \<alpha>' \<Longrightarrow> f \<alpha> \<bullet>\<^sub>C f \<alpha>' \<noteq> 0 \<Longrightarrow> eqa \<xi>' \<xi> = 0\<close>
        by (smt (z3) bij_betw_iff_bijections iso_tuple_UNIV_I is_ortho_set_def)
      from aux1 aux2 show ?thesis
        unfolding  eqc_def by auto
    qed
    finally show ?thesis
      by (simp add: eqa_def eqac_def eqc_def \<xi>'\<alpha>' \<xi>\<alpha>)
  qed
  then have [simp]: \<open>isometry U\<close>
    apply (rule_tac orthogonal_on_basis_is_isometry[where B=\<open>range ket\<close>])
    using eqac_def by auto

  have \<open>sandwich (U*) (\<Phi> (butterfly (ket \<xi>) (ket \<eta>))) = butterfly (ket \<xi>) (ket \<eta>) \<otimes>\<^sub>o id_cblinfun\<close> for \<xi> \<eta>
  proof (rule equal_ket, rename_tac \<xi>1\<alpha>)
    fix \<xi>1\<alpha> obtain \<xi>1 :: 'a and \<alpha> :: \<open>('a,'b) complement_domain_simple\<close> where \<xi>1\<alpha>: \<open>\<xi>1\<alpha> = (\<xi>1,\<alpha>)\<close> 
      apply atomize_elim by auto
    have \<open>sandwich (U*) (\<Phi> (butterfly (ket \<xi>) (ket \<eta>))) *\<^sub>V ket \<xi>1\<alpha> = U* *\<^sub>V \<Phi> (butterfly (ket \<xi>) (ket \<eta>)) *\<^sub>V \<Phi> (butterfly (ket \<xi>1) (ket \<xi>0)) *\<^sub>V f \<alpha>\<close>
      by (simp add: sandwich_apply[abs_def] cblinfun_apply_cblinfun_compose \<xi>1\<alpha> Uapply u_def)
    also have \<open>\<dots> = U* *\<^sub>V \<Phi> (butterfly (ket \<xi>) (ket \<eta>) o\<^sub>C\<^sub>L butterfly (ket \<xi>1) (ket \<xi>0)) *\<^sub>V f \<alpha>\<close>
      by (metis (no_types, lifting) assms butterfly_comp_butterfly lift_cblinfun_comp(4) register_mult)
    also have \<open>\<dots> = U* *\<^sub>V \<Phi> (eqa \<eta> \<xi>1 *\<^sub>C butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V f \<alpha>\<close>
      by (simp add: eqa_def cinner_ket)
    also have \<open>\<dots> = eqa \<eta> \<xi>1 *\<^sub>C U* *\<^sub>V \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V f \<alpha>\<close>
      by (simp add: complex_vector.linear_scale)
    also have \<open>\<dots> = eqa \<eta> \<xi>1 *\<^sub>C U* *\<^sub>V U *\<^sub>V ket (\<xi>, \<alpha>)\<close>
      unfolding Uapply u_def by simp
    also from \<open>isometry U\<close> have \<open>\<dots> = eqa \<eta> \<xi>1 *\<^sub>C ket (\<xi>, \<alpha>)\<close>
      unfolding cblinfun_apply_cblinfun_compose[symmetric] by simp
    also have \<open>\<dots> = (butterfly (ket \<xi>) (ket \<eta>) *\<^sub>V ket \<xi>1) \<otimes>\<^sub>s ket \<alpha>\<close>
      by (simp add: eqa_def tensor_ell2_scaleC1 tensor_ell2_ket)
    also have \<open>\<dots> = (butterfly (ket \<xi>) (ket \<eta>) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket \<xi>1\<alpha>\<close>
      by (simp add: \<xi>1\<alpha> tensor_op_ket)
    finally show \<open>sandwich (U*) (\<Phi> (butterfly (ket \<xi>) (ket \<eta>))) *\<^sub>V ket \<xi>1\<alpha> = (butterfly (ket \<xi>) (ket \<eta>) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket \<xi>1\<alpha>\<close>
      by -
  qed
  then have 1: \<open>sandwich (U*) (\<Phi> \<theta>) = \<theta> \<otimes>\<^sub>o id_cblinfun\<close> for \<theta>
    apply (rule clinear_eq_butterfly_ketI[THEN fun_cong, where x=\<theta>, rotated -1])
    by (auto intro: bounded_clinear.clinear bounded_linear_intros register_bounded_clinear \<open>register \<Phi>\<close>)

  have [simp]: \<open>unitary U\<close>
  proof -
    have \<open>\<Phi> (butterfly (ket \<xi>) (ket \<xi>1)) *\<^sub>S \<top> \<le> U *\<^sub>S \<top>\<close> for \<xi> \<xi>1
    proof -
      have *: \<open>\<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V b \<in> space_as_set (U *\<^sub>S \<top>)\<close> if \<open>b \<in> B \<xi>0\<close> for b
        apply (subst asm_rl[of \<open>\<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>V b = u (\<xi>, inv f b)\<close>])
         apply (simp add: u_def, metis bij_betw_inv_into_right bij_f that)
        by (metis Uapply cblinfun_apply_in_image)

      have \<open>\<Phi> (butterfly (ket \<xi>) (ket \<xi>1)) *\<^sub>S \<top> = \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>S \<Phi> (butterfly (ket \<xi>0) (ket \<xi>0)) *\<^sub>S \<Phi> (butterfly (ket \<xi>0) (ket \<xi>1)) *\<^sub>S \<top>\<close>
        unfolding cblinfun_compose_image[symmetric] register_mult[OF assms]
        by simp
      also have \<open>\<dots> \<le> \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>S \<Phi> (butterfly (ket \<xi>0) (ket \<xi>0)) *\<^sub>S \<top>\<close>
        by (meson cblinfun_image_mono top_greatest)
      also have \<open>\<dots> = \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>S S \<xi>0\<close>
        by (simp add: S_def P'_def P_butter)
      also have \<open>\<dots> = \<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) *\<^sub>S ccspan (B \<xi>0)\<close>
        by (simp add: ccspanB)
      also have \<open>\<dots> = ccspan (\<Phi> (butterfly (ket \<xi>) (ket \<xi>0)) ` B \<xi>0)\<close>
        by (meson cblinfun_image_ccspan)
      also have \<open>\<dots> \<le> U *\<^sub>S \<top>\<close>
        by (rule ccspan_leqI, use * in auto)
      finally show ?thesis by -
    qed
    moreover have \<open>\<Phi> id_cblinfun *\<^sub>S \<top> \<le> (SUP \<xi>\<in>UNIV. \<Phi> (butterfly (ket \<xi>) (ket \<xi>)) *\<^sub>S \<top>)\<close>
      unfolding sum_butterfly_ket[symmetric]
      apply (subst complex_vector.linear_sum, simp)
      by (rule cblinfun_sum_image_distr)
    ultimately have \<open>\<Phi> id_cblinfun *\<^sub>S \<top> \<le> U *\<^sub>S \<top>\<close>
      by (metis (no_types, lifting) Proj_range Proj_top SUP_le_iff assms register_of_id top_le)
    then have \<open>U *\<^sub>S \<top> = \<top>\<close>
      using top.extremum_unique by auto
    with \<open>isometry U\<close> show \<open>unitary U\<close>
      by (rule surj_isometry_is_unitary)
  qed

  have \<open>\<Phi> \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
  proof -
    from 1 have \<open>sandwich U (sandwich (U*) *\<^sub>V \<Phi> \<theta>) = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
      by simp
    then show ?thesis
      by (simp flip: sandwich_compose cblinfun_apply_cblinfun_compose)
  qed

  then show ?thesis
    apply (rule_tac exI[of _ U])
    by simp
qed

lemma register_decomposition_finite:
  fixes \<Phi> :: \<open>'a update \<Rightarrow> 'b::finite update\<close>
  assumes [simp]: \<open>register \<Phi>\<close>
  shows \<open>\<exists>U :: ('a \<times> ('a, 'b) complement_domain_simple) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> 
              (\<forall>\<theta>. \<Phi> \<theta> = sandwich U (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>
proof -
  have inj_butterket: \<open>inj (\<lambda>a. butterfly (ket a) (ket a) :: 'a update)\<close>
  proof (rule injI)
    fix x y :: 'a
    assume \<open>butterfly (ket x) (ket x) = butterfly (ket y) (ket y)\<close>
    then have \<open>butterfly (ket x) (ket x) *\<^sub>V ket x = butterfly (ket y) (ket y)  *\<^sub>V ket x\<close>
      by simp
    then show \<open>x = y\<close>
      apply (cases \<open>x = y\<close>)
      by (auto simp: cinner_ket)
  qed

  from cindependent_butterfly_ket
  have \<open>cindependent (range (\<lambda>a. butterfly (ket a) (ket a)) :: 'a update set)\<close>
    apply (subgoal_tac \<open>(range (\<lambda>a. butterfly (ket a) (ket a)) :: 'a update set) \<subseteq> {butterfly (ket i) (ket j) |i j. True}\<close>)
    by (auto intro: complex_vector.dependent_mono)
  then have \<open>cindependent (\<Phi> ` range (\<lambda>a. butterfly (ket a) (ket a)))\<close>
    apply (rule complex_vector.linear_independent_injective_image[rotated])
    by (simp_all add: register_inj clinear_register)
  then have \<open>finite (\<Phi> ` range (\<lambda>a. butterfly (ket a) (ket a)))\<close>
    using cindependent_cfinite_dim_finite by blast
  then have \<open>finite (range (\<lambda>a. butterfly (ket a) (ket a)) :: 'a update set)\<close>
    apply (rule Finite_Set.inj_on_finite[rotated -1, where f=\<Phi>])
    by (simp_all add: register_inj)
  then have \<open>finite (UNIV :: 'a set)\<close>
    apply (rule Finite_Set.inj_on_finite[rotated -1, where f=\<open>\<lambda>a. butterfly (ket a) (ket a)\<close>])
     apply (rule inj_butterket)
    by simp
  then have \<open>class.finite TYPE('a)\<close>
    by intro_classes
  from register_decomposition_finite_aux[unoverload_type 'a, OF this]
  show ?thesis
    using assms by metis
qed

hide_fact register_decomposition_finite_aux

lemma complement_exists_simple:
  fixes F :: \<open>'a update \<Rightarrow> 'b::finite update\<close>
  assumes \<open>register F\<close>
  shows \<open>\<exists>G :: ('a, 'b) complement_domain_simple update \<Rightarrow> 'b update. compatible F G \<and> iso_register (F;G)\<close>
proof -
  note [[simproc del: Laws_Quantum.compatibility_warn]]
  obtain U :: \<open>('a \<times> ('a, 'b) complement_domain_simple) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    where [simp]: "unitary U" and F: \<open>F a = sandwich U (a \<otimes>\<^sub>o id_cblinfun)\<close> for a
    apply atomize_elim using assms by (rule register_decomposition_finite)
  define G :: \<open>(('a, 'b) complement_domain_simple) update \<Rightarrow> 'b update\<close> where \<open>G b = sandwich U (id_cblinfun \<otimes>\<^sub>o b)\<close> for b
  have [simp]: \<open>register G\<close>
    unfolding G_def apply (rule register_decomposition_converse) by simp
  have \<open>F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a\<close> for a b
  proof -
    have \<open>F a o\<^sub>C\<^sub>L G b = sandwich U (a \<otimes>\<^sub>o b)\<close>
      by (auto simp: F G_def sandwich_apply cblinfun_assoc_left lift_cblinfun_comp[OF unitaryD1] 
          lift_cblinfun_comp[OF comp_tensor_op] \<open>unitary U\<close>)
    moreover have \<open>G b o\<^sub>C\<^sub>L F a = sandwich U (a \<otimes>\<^sub>o b)\<close>
      by (auto simp: F G_def sandwich_apply cblinfun_assoc_left lift_cblinfun_comp[OF unitaryD1] 
          lift_cblinfun_comp[OF comp_tensor_op] \<open>unitary U\<close>)
    ultimately show ?thesis by simp
  qed
  then have [simp]: \<open>compatible F G\<close>
    by (auto simp: compatible_def \<open>register F\<close> \<open>register G\<close>)
  moreover have \<open>iso_register (F;G)\<close>
  proof -
    have \<open>(F;G) (a \<otimes>\<^sub>o b) = sandwich U (a \<otimes>\<^sub>o b)\<close> for a b
      by (auto simp: register_pair_apply F G_def sandwich_apply cblinfun_assoc_left lift_cblinfun_comp[OF unitaryD1] 
          lift_cblinfun_comp[OF comp_tensor_op] \<open>unitary U\<close>)
    then have FG: \<open>(F;G) = sandwich U\<close>
      apply (rule tensor_extensionality[rotated -1])
      by (simp_all add: bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose bounded_cbilinear.add_right clinearI unitary_sandwich_register)

    define I where \<open>I = sandwich (U*)\<close> for x
    have [simp]: \<open>register I\<close>
      by (simp add: I_def unitary_sandwich_register)
    have IFG: \<open>I o (F;G) = id\<close>
      by (auto intro!:ext simp: I_def[abs_def] FG sandwich_apply lift_cblinfun_comp[OF unitaryD1]
          \<open>unitary U\<close> cblinfun_assoc_left)
    have FGI: \<open>(F;G) o I = id\<close>
      by (auto intro!:ext simp: I_def[abs_def] FG sandwich_apply cblinfun_assoc_left
          lift_cblinfun_comp[OF unitaryD1] lift_cblinfun_comp[OF unitaryD2] \<open>unitary U\<close>)
    from IFG FGI show \<open>iso_register (F;G)\<close>
      by (auto intro!: iso_registerI)
  qed
  ultimately show ?thesis
    apply (rule_tac exI[of _ G]) by (auto)
qed

unbundle no cblinfun_syntax
unbundle no lattice_syntax
unbundle no register_syntax

end
