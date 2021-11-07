theory Pure_States
  imports Quantum_Extra2 "HOL-Eisbach.Eisbach"
begin

definition \<open>pure_state_target_vector F \<eta>\<^sub>F = (if ket default \<in> range (cblinfun_apply (F (butterfly \<eta>\<^sub>F \<eta>\<^sub>F)))
   then ket default
   else (SOME \<eta>'. norm \<eta>' = 1 \<and> \<eta>' \<in> range (cblinfun_apply (F (butterfly \<eta>\<^sub>F \<eta>\<^sub>F)))))\<close>

lemma pure_state_target_vector_eqI:
  assumes \<open>F (butterfly \<eta>\<^sub>F \<eta>\<^sub>F) = G (butterfly \<eta>\<^sub>G \<eta>\<^sub>G)\<close>
  shows \<open>pure_state_target_vector F \<eta>\<^sub>F = pure_state_target_vector G \<eta>\<^sub>G\<close>
  by (simp add: assms pure_state_target_vector_def)

lemma pure_state_target_vector_ket_default: \<open>pure_state_target_vector F \<eta>\<^sub>F = ket default\<close> if \<open>ket default \<in> range (cblinfun_apply (F (butterfly \<eta>\<^sub>F \<eta>\<^sub>F)))\<close>
  by (simp add: pure_state_target_vector_def that)

lemma
  assumes [simp]: \<open>\<eta>\<^sub>F \<noteq> 0\<close> \<open>register F\<close>
  shows pure_state_target_vector_in_range: \<open>pure_state_target_vector F \<eta>\<^sub>F \<in> range ((*\<^sub>V) (F (selfbutter \<eta>\<^sub>F)))\<close> (is ?range)
    and pure_state_target_vector_norm: \<open>norm (pure_state_target_vector F \<eta>\<^sub>F) = 1\<close> (is ?norm)
proof -
  from assms have \<open>selfbutter \<eta>\<^sub>F \<noteq> 0\<close>
    by (metis butterfly_0_right complex_vector.scale_zero_right inj_selfbutter_upto_phase)
  then have \<open>F (selfbutter \<eta>\<^sub>F) \<noteq> 0\<close>
    using register_inj[OF \<open>register F\<close>, THEN injD, where y=0]
    by (auto simp: complex_vector.linear_0)
  then obtain \<psi>' where \<psi>': \<open>F (selfbutter \<eta>\<^sub>F) *\<^sub>V \<psi>' \<noteq> 0\<close>
    by (meson cblinfun_eq_0_on_UNIV_span complex_vector.span_UNIV)
  have ex: \<open>\<exists>\<psi>. norm \<psi> = 1 \<and> \<psi> \<in> range ((*\<^sub>V) (F (selfbutter \<eta>\<^sub>F)))\<close>
    apply (rule exI[of _ \<open>(F (selfbutter \<eta>\<^sub>F) *\<^sub>V \<psi>') /\<^sub>C norm (F (selfbutter \<eta>\<^sub>F) *\<^sub>V \<psi>')\<close>])
    using \<psi>' apply (auto simp add: norm_inverse)
    by (metis cblinfun.scaleC_right rangeI)
  then show ?range
    by (metis (mono_tags, lifting) pure_state_target_vector_def verit_sko_ex')
  show ?norm
    apply (simp add: pure_state_target_vector_def)
    using ex by (metis (mono_tags, lifting) verit_sko_ex')
qed


lemma pure_state_target_vector_correct: 
  assumes [simp]: \<open>\<eta> \<noteq> 0\<close> \<open>register F\<close>
  shows \<open>F (selfbutter \<eta>) *\<^sub>V pure_state_target_vector F \<eta> \<noteq> 0\<close>
proof -
  obtain \<psi> where \<psi>: \<open>F (selfbutter \<eta>) \<psi> = pure_state_target_vector F \<eta>\<close>
    apply atomize_elim
    using pure_state_target_vector_in_range[OF assms]
    by (smt (verit, best) image_iff top_ccsubspace.rep_eq top_set_def)

  define n where \<open>n = cinner \<eta> \<eta>\<close>
  then have \<open>n \<noteq> 0\<close>
    by auto

  have pure_state_target_vector_neq0: \<open>pure_state_target_vector F \<eta> \<noteq> 0\<close>
    using pure_state_target_vector_norm[OF assms]
    by auto

  have \<open>F (selfbutter \<eta>) *\<^sub>V pure_state_target_vector F \<eta> = F (selfbutter \<eta>) *\<^sub>V F (selfbutter \<eta>) *\<^sub>V \<psi>\<close>
    by (simp add: \<psi>)
  also have \<open>\<dots> = n *\<^sub>C F (selfbutter \<eta>) *\<^sub>V \<psi>\<close>
    by (simp flip: cblinfun_apply_cblinfun_compose add: register_mult register_scaleC n_def)
  also have \<open>\<dots> = n *\<^sub>C pure_state_target_vector F \<eta>\<close>
    by (simp add: \<psi>)
  also have \<open>\<dots> \<noteq> 0\<close>
    using pure_state_target_vector_neq0 \<open>n \<noteq> 0\<close>
    by auto
  finally show ?thesis
    by -
qed

definition \<open>pure_state' F \<psi> \<eta>\<^sub>F = F (butterfly \<psi> \<eta>\<^sub>F) *\<^sub>V pure_state_target_vector F \<eta>\<^sub>F\<close>

abbreviation \<open>pure_state F \<psi> \<equiv> pure_state' F \<psi> (ket default)\<close>

nonterminal pure_tensor
syntax "_pure_tensor" :: \<open>'a \<Rightarrow> 'b \<Rightarrow> pure_tensor \<Rightarrow> pure_tensor\<close> ("_ _ \<otimes>\<^sub>p _" [1000, 0, 0] 1000)
syntax "_pure_tensor2" :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> pure_tensor\<close> ("_ _ \<otimes>\<^sub>p _ _" [1000, 0, 1000, 0] 1000)
syntax "_pure_tensor1" :: \<open>'a \<Rightarrow> 'b \<Rightarrow> pure_tensor\<close>
syntax "_pure_tensor_start" :: \<open>pure_tensor \<Rightarrow> 'a\<close> ("'(_')")

translations
  "_pure_tensor2 F \<psi> G \<phi>" \<rightharpoonup> "CONST pure_state (F; G) (\<psi> \<otimes>\<^sub>s \<phi>)"
  "_pure_tensor F \<psi> (CONST pure_state G \<phi>)" \<rightharpoonup> "CONST pure_state (F; G) (\<psi> \<otimes>\<^sub>s \<phi>)"
  "_pure_tensor_start x" \<rightharpoonup> "x"

  "_pure_tensor_start (_pure_tensor2 F \<psi> G \<phi>)" \<leftharpoondown> "CONST pure_state (F; G) (\<psi> \<otimes>\<^sub>s \<phi>)"
  "_pure_tensor F \<psi> (_pure_tensor2 G \<phi> H \<eta>)" \<leftharpoondown> "_pure_tensor2 F \<psi> (G;H) (\<phi> \<otimes>\<^sub>s \<eta>)"

term \<open>(F \<psi> \<otimes>\<^sub>p G \<phi> \<otimes>\<^sub>p H z)\<close>
term \<open>pure_state (F; G) (a \<otimes>\<^sub>s b)\<close>

lemma register_pair_butterfly_tensor: \<open>(F; G) (butterfly (a \<otimes>\<^sub>s b) (c \<otimes>\<^sub>s d)) = F (butterfly a c) o\<^sub>C\<^sub>L G (butterfly b d)\<close>
  if [simp]: \<open>compatible F G\<close>
  by (auto simp: default_prod_def simp flip: tensor_ell2_ket tensor_butterfly register_pair_apply)

lemma pure_state_eqI:
  assumes \<open>F (selfbutter \<eta>\<^sub>F) = G (selfbutter \<eta>\<^sub>G)\<close>
  assumes \<open>F (butterfly \<psi> \<eta>\<^sub>F) = G (butterfly \<phi> \<eta>\<^sub>G)\<close>
  shows \<open>pure_state' F \<psi> \<eta>\<^sub>F = pure_state' G \<phi> \<eta>\<^sub>G\<close>
proof -
  from assms(1) have \<open>pure_state_target_vector F \<eta>\<^sub>F = pure_state_target_vector G \<eta>\<^sub>G\<close>
    by (rule pure_state_target_vector_eqI)
  with assms(2)
  show ?thesis
    unfolding pure_state'_def
    by simp
qed


definition \<open>regular_register F \<longleftrightarrow> register F \<and> (\<exists>a. (F; complement F) (selfbutterket default \<otimes>\<^sub>o a) = selfbutterket default)\<close>

lemma regular_registerI:
  assumes [simp]: \<open>register F\<close>
  assumes [simp]: \<open>complements F G\<close>
  assumes eq: \<open>(F; G) (selfbutterket default \<otimes>\<^sub>o a) = selfbutterket default\<close>
  shows \<open>regular_register F\<close>
proof -
  have [simp]: \<open>compatible F G\<close>
    using assms by (simp add: complements_def)
  from \<open>complements F G\<close>
  obtain I where cFI: \<open>complement F o I = G\<close> and \<open>iso_register I\<close>
    apply atomize_elim
    by (meson Laws_Complement_Quantum.complement_unique equivalent_registers_def equivalent_registers_sym)
  have \<open>(F; complement F) (selfbutterket default \<otimes>\<^sub>o I a) = (F; G) (selfbutterket default \<otimes>\<^sub>o a)\<close>
    using cFI by (auto simp: register_pair_apply)
  also have \<open>\<dots> = selfbutterket default\<close>
    by (rule eq)
  finally show ?thesis
    unfolding regular_register_def by auto
qed

lemma regular_register_pair:
  assumes [simp]: \<open>compatible F G\<close>
  assumes \<open>regular_register F\<close> and \<open>regular_register G\<close>
  shows \<open>regular_register (F;G)\<close>
proof -
  have [simp]: \<open>bij (F;complement F)\<close> \<open>bij (G;complement G)\<close>
    using assms(1) compatible_def complement_is_complement complements_def iso_register_bij by blast+
  have [simp]: \<open>bij ((F;G);complement (F;G))\<close>
    using assms(1) complement_is_complement complements_def iso_register_bij pair_is_register by blast
  have [simp]: \<open>register F\<close> \<open>register G\<close>
    using assms(1) unfolding compatible_def by auto

  obtain aF where [simp]: \<open>inv (F;complement F) (selfbutterket default) = selfbutterket default \<otimes>\<^sub>o aF\<close>
    by (metis assms(2) compatible_complement_right invI pair_is_register register_inj regular_register_def)
  obtain aG where [simp]: \<open>inv (G;complement G) (selfbutterket default) = selfbutterket default \<otimes>\<^sub>o aG\<close>
    by (metis assms(3) complement_is_complement complements_def inj_iff inv_f_f iso_register_inv_comp1 regular_register_def)
  define t1 where \<open>t1 = inv ((F;G); complement (F;G)) (selfbutterket default)\<close>
  define t2 where \<open>t2 = inv (F; (G; complement (F;G))) (selfbutterket default)\<close>
  define t3 where \<open>t3 = inv (G; (F; complement (F;G))) (selfbutterket default)\<close>


  have \<open>complements F (G; complement (F;G))\<close>
    apply (rule complements_complement_pair)
    by simp
  then have \<open>equivalent_registers (complement F) (G; complement (F;G))\<close>
    using Laws_Complement_Quantum.complement_unique equivalent_registers_sym by blast
  then obtain I where [simp]: \<open>iso_register I\<close> and I: \<open>(G; complement (F;G)) = complement F o I\<close>
    by (metis equivalent_registers_def)
  then have [simp]: \<open>register I\<close>
    by (meson iso_register_is_register)
  have [simp]: \<open>bij (id \<otimes>\<^sub>r I)\<close>
    by (rule iso_register_bij, simp)
  have [simp]: \<open>inv (id \<otimes>\<^sub>r I) = id \<otimes>\<^sub>r inv I\<close>
    by auto

  have \<open>t2 = (inv (id \<otimes>\<^sub>r I) o inv (F;complement F)) (selfbutterket default)\<close>
    unfolding t2_def I
    apply (subst o_inv_distrib[symmetric]) 
    by (auto simp: pair_o_tensor)
  also have \<open>\<dots> = (selfbutterket default \<otimes>\<^sub>o inv I aF)\<close>
    apply auto
    by (metis \<open>iso_register I\<close> id_def iso_register_def iso_register_inv register_id register_tensor_apply)
  finally have t2': \<open>t2 = selfbutterket default \<otimes>\<^sub>o inv I aF\<close>
    by simp

  have *: \<open>complements G (F; complement (F;G))\<close>
    apply (rule complements_complement_pair')
    by simp
  then have [simp]: \<open>compatible G (F; complement (F;G))\<close>
    using complements_def by blast
  from * have \<open>equivalent_registers (complement G) (F; complement (F;G))\<close>
    using complement_unique equivalent_registers_sym by blast
  then obtain J where [simp]: \<open>iso_register J\<close> and I: \<open>(F; complement (F;G)) = complement G o J\<close>
    by (metis equivalent_registers_def)
  then have [simp]: \<open>register J\<close>
    by (meson iso_register_is_register)
  have [simp]: \<open>bij (id \<otimes>\<^sub>r J)\<close>
    by (rule iso_register_bij, simp)
  have [simp]: \<open>inv (id \<otimes>\<^sub>r J) = id \<otimes>\<^sub>r inv J\<close>
    by auto

  have \<open>t3 = (inv (id \<otimes>\<^sub>r J) o inv (G;complement G)) (selfbutterket default)\<close>
    unfolding t3_def I
    apply (subst o_inv_distrib[symmetric]) 
    by (auto simp: pair_o_tensor)
  also have \<open>\<dots> = (selfbutterket default \<otimes>\<^sub>o inv J aG)\<close>
    apply auto
    by (metis \<open>iso_register J\<close> id_def iso_register_def iso_register_inv register_id register_tensor_apply)
  finally have t3': \<open>t3 = selfbutterket default \<otimes>\<^sub>o inv J aG\<close>
    by simp

  have *: \<open>((F;G); complement (F;G)) o assoc' = (F; (G; complement (F;G)))\<close>
    apply (rule tensor_extensionality3)
    by (auto simp: register_pair_apply  compatible_complement_pair1 compatible_complement_pair2)
  have t2_t1: \<open>t2 = assoc t1\<close>
    unfolding t1_def t2_def *[symmetric] apply (subst o_inv_distrib)
    by auto

  have *: \<open>((F;G); complement (F;G)) o (swap \<otimes>\<^sub>r id) o assoc' = (G; (F; complement (F;G)))\<close>
    apply (rule tensor_extensionality3)
      apply (auto intro!: register_comp register_tensor_is_register pair_is_register complements_complement_pair
        simp: register_pair_apply compatible_complement_pair1)
    by (metis assms(1) cblinfun_assoc_left(1) swap_registers_left)
  have t3_t1: \<open>t3 = assoc ((swap \<otimes>\<^sub>r id) t1)\<close>
    unfolding t1_def t3_def *[symmetric] apply (subst o_inv_distrib)
    by (auto intro!: bij_comp simp: iso_register_bij o_inv_distrib)

  from \<open>t2 = assoc t1\<close> \<open>t3 = assoc ((swap \<otimes>\<^sub>r id) t1)\<close>
  have *: \<open>selfbutterket default \<otimes>\<^sub>o inv J aG =  assoc ((swap \<otimes>\<^sub>r id) (assoc' (selfbutterket default \<otimes>\<^sub>o inv I aF)))\<close>
    by (simp add: t2' t3')

  have \<open>selfbutterket default \<otimes>\<^sub>o swap (inv J aG) = (id \<otimes>\<^sub>r swap) (selfbutterket default \<otimes>\<^sub>o inv J aG)\<close>
    by auto
  also have \<open>\<dots> = ((id \<otimes>\<^sub>r swap) o assoc o (swap \<otimes>\<^sub>r id) o assoc') (selfbutterket default \<otimes>\<^sub>o inv I aF)\<close>
    by (simp add: *)
  also have \<open>\<dots> = (assoc o swap) (selfbutterket default \<otimes>\<^sub>o inv I aF)\<close>
    apply (rule fun_cong[where g=\<open>assoc o swap\<close>])
    apply (intro tensor_extensionality3 register_comp register_tensor_is_register)
    by auto
  also have \<open>\<dots> = assoc (inv I aF \<otimes>\<^sub>o selfbutterket default)\<close>
    by auto
  finally have *: \<open>selfbutterket default \<otimes>\<^sub>o swap (inv J aG) = assoc (inv I aF \<otimes>\<^sub>o selfbutterket default)\<close>
    by -

  obtain c where *: \<open>selfbutterket (default::'c) \<otimes>\<^sub>o swap (inv J aG) = selfbutterket default \<otimes>\<^sub>o c \<otimes>\<^sub>o selfbutterket default\<close>
    apply atomize_elim
    apply (rule overlapping_tensor)
    using * unfolding assoc_ell2_sandwich sandwich_def
    by auto

  have \<open>t1 = ((swap \<otimes>\<^sub>r id) o assoc') t3\<close>
    by (simp add: t3_t1 register_tensor_distrib[unfolded o_def, THEN fun_cong] flip: id_def)
  also have \<open>\<dots> = ((swap \<otimes>\<^sub>r id) o assoc' o (id \<otimes>\<^sub>r swap)) (selfbutterket (default::'c) \<otimes>\<^sub>o swap (inv J aG))\<close>
    unfolding t3' by auto
  also have \<open>\<dots> = ((swap \<otimes>\<^sub>r id) o assoc' o (id \<otimes>\<^sub>r swap)) (selfbutterket default \<otimes>\<^sub>o c \<otimes>\<^sub>o selfbutterket default)\<close>
    unfolding * by simp
  also have \<open>\<dots> = selfbutterket default \<otimes>\<^sub>o c\<close>
    apply (simp del: tensor_butterfly)
    by (simp add: default_prod_def)
  finally have \<open>t1 = selfbutterket default \<otimes>\<^sub>o c\<close>
    by -

  then show ?thesis
    apply (auto intro!: exI[of _ c] simp: regular_register_def t1_def)
    by (metis \<open>bij ((F;G);complement (F;G))\<close> bij_inv_eq_iff)
qed

lemma regular_register_comp: \<open>regular_register (F o G)\<close> if \<open>regular_register F\<close> \<open>regular_register G\<close>
proof -
  have [simp]: \<open>register F\<close> \<open>register G\<close>
    using regular_register_def that by blast+
  from that obtain a where a: \<open>(F; complement F) (selfbutterket default \<otimes>\<^sub>o a) = selfbutterket default\<close>
    unfolding regular_register_def by metis
  from that obtain b where b: \<open>(G; complement G) (selfbutterket default \<otimes>\<^sub>o b) = selfbutterket default\<close>
    unfolding regular_register_def by metis
  have \<open>complements (F o G) (complement F; F o complement G)\<close>
    by (simp add: complements_chain)
  then have \<open>equivalent_registers (complement F; F o complement G) (complement (F o G))\<close>
    using complement_unique by blast
  then obtain J where [simp]: \<open>iso_register J\<close> and 1: \<open>(complement F; F o complement G) o J = (complement (F o G))\<close>
    using equivalent_registers_def by blast
  have [simp]: \<open>register J\<close>
    by (simp add: iso_register_is_register)

  define c where \<open>c = inv J (a \<otimes>\<^sub>o b)\<close>

  have \<open>((F o G); complement (F o G)) (selfbutterket default \<otimes>\<^sub>o c) = ((F o G); (complement F; F o complement G)) (selfbutterket default \<otimes>\<^sub>o J c)\<close>
    by (auto simp flip: 1 simp: register_pair_apply)
  also have \<open>\<dots> = ((F o (G; complement G); complement F) o assoc' o (id \<otimes>\<^sub>r swap)) (selfbutterket default \<otimes>\<^sub>o J c)\<close>
    apply (subst register_comp_pair[symmetric])
      apply auto[2]
    apply (subst pair_o_assoc')
       apply auto[3]
    apply (subst pair_o_tensor)
    by auto
  also have \<open>\<dots> = ((F o (G; complement G); complement F) o assoc') (selfbutterket default \<otimes>\<^sub>o swap (J c))\<close>
    by auto
  also have \<open>\<dots> = ((F o (G; complement G); complement F) o assoc') (selfbutterket default \<otimes>\<^sub>o (b \<otimes>\<^sub>o a))\<close>
    unfolding c_def apply (subst surj_f_inv_f[where f=J])
     apply (meson \<open>iso_register J\<close> bij_betw_inv_into_right iso_register_inv_comp1 iso_register_inv_comp2 iso_tuple_UNIV_I o_bij surj_iff_all)
    by auto
  also have \<open>\<dots> = (F \<circ> (G;complement G);complement F) ((selfbutterket default \<otimes>\<^sub>o b) \<otimes>\<^sub>o a)\<close>
    by (simp add: assoc'_apply)
  also have \<open>\<dots> = (F; complement F) ((G;complement G) (selfbutterket default \<otimes>\<^sub>o b) \<otimes>\<^sub>o a)\<close>
    by (simp add: register_pair_apply')
  also have \<open>\<dots> = selfbutterket default\<close>
    by (auto simp: a b) 
  finally have \<open>(F \<circ> G;complement (F \<circ> G)) (selfbutterket default \<otimes>\<^sub>o c) = selfbutterket default\<close>
    by -
  then show ?thesis
    using \<open>register F\<close> \<open>register G\<close> register_comp regular_register_def by blast
qed

lemma regular_iso_register:
  assumes \<open>regular_register F\<close>
  assumes [register]: \<open>iso_register F\<close>
  shows \<open>F (selfbutterket default) = selfbutterket default\<close>
proof -
  from assms(1) obtain a where a: \<open>(F;complement F) (selfbutterket default \<otimes>\<^sub>o a) = selfbutterket default\<close>
    using regular_register_def by blast

  let ?u = \<open>empty_var :: (unit ell2 \<Rightarrow>\<^sub>C\<^sub>L unit ell2) \<Rightarrow> _\<close>
  have \<open>is_unit_register ?u\<close> and \<open>is_unit_register (complement F)\<close>
    by auto
  then have \<open>equivalent_registers (complement F) ?u\<close>
    using unit_register_unique by blast
  then obtain I where \<open>iso_register I\<close> and \<open>complement F = ?u o I\<close>
    by (metis \<open>is_unit_register (complement F)\<close> equivalent_registers_def is_unit_register_empty_var unit_register_unique)
  have \<open>selfbutterket default = (F; ?u o I) (selfbutterket default \<otimes>\<^sub>o a)\<close>
    using \<open>complement F = empty_var \<circ> I\<close> a by presburger
  also have \<open>\<dots> = (F; ?u) (selfbutterket default \<otimes>\<^sub>o I a)\<close>
    by (metis Laws_Quantum.register_pair_apply \<open>complement F = empty_var \<circ> I\<close> \<open>equivalent_registers (complement F) empty_var\<close> assms(2) comp_apply complement_is_complement complements_def equivalent_complements iso_register_is_register)
  also have \<open>\<dots> = (F; ?u) (selfbutterket default \<otimes>\<^sub>o (one_dim_iso (I a) *\<^sub>C id_cblinfun))\<close>
    by simp
  also have \<open>\<dots> = one_dim_iso (I a) *\<^sub>C (F; ?u) (selfbutterket default \<otimes>\<^sub>o id_cblinfun)\<close>
    by (simp add: Axioms_Quantum.register_pair_apply empty_var_def iso_register_is_register)
  also have \<open>\<dots> = one_dim_iso (I a) *\<^sub>C F (selfbutterket default)\<close>
    by (auto simp: register_pair_apply iso_register_is_register simp del: id_cblinfun_eq_1)
  finally have F: \<open>one_dim_iso (I a) *\<^sub>C F (selfbutterket default) = selfbutterket default\<close>
    by simp

  from F have \<open>one_dim_iso (I a) \<noteq> (0::complex)\<close>
    by (metis butterfly_apply butterfly_scaleC_left complex_vector.scale_eq_0_iff id_cblinfun_eq_1 id_cblinfun_not_0 cinner_ket_same ket_nonzero one_dim_iso_of_one one_dim_iso_of_zero')

  have \<open>selfbutterket default = one_dim_iso (I a) *\<^sub>C F (selfbutterket default)\<close>
    using F by simp
  also have \<open>\<dots> = one_dim_iso (I a) *\<^sub>C F (selfbutterket default o\<^sub>C\<^sub>L selfbutterket default)\<close>
    by auto
  also have \<open>\<dots> = one_dim_iso (I a) *\<^sub>C (F (selfbutterket default) o\<^sub>C\<^sub>L F (selfbutterket default))\<close>
    by (simp add: assms(2) iso_register_is_register register_mult)
  also have \<open>\<dots> = one_dim_iso (I a) *\<^sub>C ((selfbutterket default /\<^sub>C one_dim_iso (I a)) o\<^sub>C\<^sub>L (selfbutterket default /\<^sub>C one_dim_iso (I a)))\<close>
    by (metis (no_types, lifting) F \<open>one_dim_iso (I a) \<noteq> 0\<close> complex_vector.scale_left_imp_eq inverse_1 left_inverse scaleC_scaleC zero_neq_one)
  also have \<open>\<dots> = one_dim_iso (I a) *\<^sub>C selfbutterket default\<close>
    by (smt (verit, best) butterfly_comp_butterfly calculation cblinfun_compose_scaleC_left cblinfun_compose_scaleC_right complex_vector.scale_cancel_left cinner_ket_same left_inverse scaleC_one scaleC_scaleC)
  finally have \<open>one_dim_iso (I a) = (1::complex)\<close>
    by (metis butterfly_0_left butterfly_apply complex_vector.scale_cancel_right cinner_ket_same ket_nonzero scaleC_one)
  with F show \<open>F (selfbutterket default) = selfbutterket default\<close>
    by simp
qed

lemma pure_state_nested:
  assumes [simp]: \<open>compatible F G\<close>
  assumes \<open>regular_register H\<close>
  assumes \<open>iso_register H\<close>
  shows \<open>pure_state (F;G) (pure_state H h \<otimes>\<^sub>s g) = pure_state ((F o H);G) (h \<otimes>\<^sub>s g)\<close>
proof -
  note [[simproc del: Laws_Quantum.compatibility_warn]]
  have [simp]: \<open>register H\<close>
    by (meson assms(3) iso_register_is_register)
  have [simp]: \<open>H (selfbutterket default) = selfbutterket default\<close>
    apply (rule regular_iso_register)
    using assms by auto
  have 1: \<open>pure_state_target_vector H (ket default) = ket default\<close>
    apply (rule pure_state_target_vector_ket_default)
    apply auto
    by (metis (no_types, lifting) cinner_ket_same rangeI scaleC_one)

  have \<open>butterfly (pure_state H h) (ket default) = butterfly (H (butterfly h (ket default)) *\<^sub>V ket default) (ket default)\<close>
    by (simp add: pure_state'_def 1)
  also have \<open>\<dots> = H (butterfly h (ket default)) o\<^sub>C\<^sub>L selfbutterket default\<close>
    by (metis (no_types, hide_lams) adj_cblinfun_compose butterfly_adjoint butterfly_comp_cblinfun double_adj)
  also have \<open>\<dots> = H (butterfly h (ket default)) o\<^sub>C\<^sub>L H (selfbutterket default)\<close>
    by simp
  also have \<open>\<dots> = H (butterfly h (ket default) o\<^sub>C\<^sub>L selfbutterket default)\<close>
    by (meson \<open>register H\<close> register_mult)
  also have \<open>\<dots> = H (butterfly h (ket default))\<close>
    by auto
  finally have 2: \<open>butterfly (pure_state H h) (ket default) = H (butterfly h (ket default))\<close>
    by simp

  show ?thesis
    apply (rule pure_state_eqI)
    using 1 2
    by (auto simp: register_pair_butterfly_tensor compatible_ac_rules default_prod_def simp flip: tensor_ell2_ket)
qed

lemma state_apply1: 
  assumes [register]: \<open>compatible F G\<close>
  shows \<open>F U *\<^sub>V (F \<psi> \<otimes>\<^sub>p G \<phi>) = (F (U \<psi>) \<otimes>\<^sub>p G \<phi>)\<close>
proof -
  have [register]: \<open>compatible F G\<close>
    using assms(1) complements_def by blast
  have \<open>F U *\<^sub>V (F \<psi> \<otimes>\<^sub>p G \<phi>) = (F;G) (U \<otimes>\<^sub>o id_cblinfun) *\<^sub>V (F \<psi> \<otimes>\<^sub>p G \<phi>)\<close>
    apply (subst register_pair_apply)
    by auto
  also have \<open>\<dots> = (F (U \<psi>) \<otimes>\<^sub>p G \<phi>)\<close>
    unfolding pure_state'_def 
    by (auto simp: register_mult' cblinfun_comp_butterfly tensor_op_ell2)
  finally show ?thesis
    by -
qed

lemma Fst_regular[simp]: \<open>regular_register Fst\<close>
  apply (rule regular_registerI[where a=\<open>selfbutterket default\<close> and G=Snd])
  by (auto simp: pair_Fst_Snd default_prod_def)

lemma Snd_regular[simp]: \<open>regular_register Snd\<close>
  apply (rule regular_registerI[where a=\<open>selfbutterket default\<close> and G=Fst])
    apply auto[2]
  apply (auto simp only: default_prod_def swap_apply simp flip: swap_def)
  by auto

lemma id_regular[simp]: \<open>regular_register id\<close>
  apply (rule regular_registerI[where G=unit_register and a=id_cblinfun])
  by (auto simp: register_pair_apply)

lemma swap_regular[simp]: \<open>regular_register swap\<close>
  by (auto intro!: regular_register_pair simp: swap_def)

lemma assoc_regular[simp]: \<open>regular_register assoc\<close>
  by (auto intro!: regular_register_pair regular_register_comp simp: assoc_def)

lemma assoc'_regular[simp]: \<open>regular_register assoc'\<close>
  by (auto intro!: regular_register_pair regular_register_comp simp: assoc'_def)

lemma cspan_pure_state': 
  assumes \<open>iso_register F\<close>
  assumes \<open>cspan (g ` X) = UNIV\<close>
  assumes \<eta>_cond: \<open>F (selfbutter \<eta>) *\<^sub>V pure_state_target_vector F \<eta> \<noteq> 0\<close>
  shows \<open>cspan ((\<lambda>z. pure_state' F (g z) \<eta>) ` X) = UNIV\<close>
proof -
  from iso_register_decomposition[of F]
  obtain U where [simp]: \<open>unitary U\<close> and F: \<open>F = sandwich U\<close>
    using assms(1) by blast

  define \<eta>' c where \<open>\<eta>' = pure_state_target_vector F \<eta>\<close> and \<open>c = cinner (U *\<^sub>V \<eta>) \<eta>'\<close>

  from \<eta>_cond
  have \<open>c \<noteq> 0\<close>
    by (simp add: \<eta>'_def F sandwich_def c_def cinner_adj_right)

  have \<open>cspan ((\<lambda>z. pure_state' F (g z) \<eta>) ` X) = cspan ((\<lambda>z. F (butterfly (g z) \<eta>) *\<^sub>V \<eta>') ` X)\<close>
    by (simp add: \<eta>'_def pure_state'_def)
  also have \<open>\<dots> = cspan ((\<lambda>z. (butterfly (U *\<^sub>V g z) (U *\<^sub>V \<eta>)) *\<^sub>V \<eta>') ` X)\<close>
    by (simp add: F sandwich_def cinner_adj_right)
  also have \<open>\<dots> = cspan ((\<lambda>z. c *\<^sub>C U *\<^sub>V g z) ` X)\<close>
    by (simp add: c_def)
  also have \<open>\<dots> = (\<lambda>z. c *\<^sub>C U *\<^sub>V z) ` cspan (g ` X)\<close>
    apply (subst complex_vector.linear_span_image[symmetric])
    by (auto simp: image_image)
  also have \<open>\<dots> = (\<lambda>z. c *\<^sub>C U *\<^sub>V z) ` UNIV\<close>
    using assms(2) by presburger
  also have \<open>\<dots> = UNIV\<close>
    apply (rule surjI[where f=\<open>\<lambda>z. (U* *\<^sub>V z) /\<^sub>C c\<close>])
    using \<open>c \<noteq> 0\<close> by (auto simp flip: cblinfun_apply_cblinfun_compose)
  finally show ?thesis
    by -
qed

lemma cspan_pure_state: 
  assumes [simp]: \<open>iso_register F\<close>
  assumes \<open>cspan (g ` X) = UNIV\<close>
  shows \<open>cspan ((\<lambda>z. pure_state F (g z)) ` X) = UNIV\<close>
  apply (rule cspan_pure_state')
  using assms apply auto[2]
  apply (rule pure_state_target_vector_correct)
  by (auto simp: iso_register_is_register)

lemma pure_state_bounded_clinear:
  assumes [register]: \<open>compatible F G\<close>
  shows \<open>bounded_clinear (\<lambda>\<psi>. (F \<psi> \<otimes>\<^sub>p G \<phi>))\<close>
proof -
  have [bounded_clinear]: \<open>bounded_clinear (F;G)\<close>
    using assms pair_is_register register_bounded_clinear by blast
  show ?thesis
    unfolding pure_state'_def
    by (auto intro!: bounded_linear_intros)
qed

lemma pure_state_bounded_clinear_right:
  assumes [register]: \<open>compatible F G\<close>
  shows \<open>bounded_clinear (\<lambda>\<phi>. (F \<psi> \<otimes>\<^sub>p G \<phi>))\<close>
proof -
  have [bounded_clinear]: \<open>bounded_clinear (F;G)\<close>
    using assms pair_is_register register_bounded_clinear by blast
  show ?thesis
    unfolding pure_state'_def
    by (auto intro!: bounded_linear_intros)
qed

lemma pure_state_clinear:
  assumes [register]: \<open>compatible F G\<close>
  shows \<open>clinear (\<lambda>\<psi>. (F \<psi> \<otimes>\<^sub>p G \<phi>))\<close>
  using assms bounded_clinear.clinear pure_state_bounded_clinear by blast

method pure_state_flatten_nested =
  (subst pure_state_nested, (auto; fail)[3])+

text \<open>The following method \<open>pure_state_eq\<close> tries to solve a equality where both sides are of the form
  \<open>F\<^sub>1(\<psi>\<^sub>1) \<otimes>\<^sub>p F\<^sub>2(\<psi>\<^sub>2) \<otimes>\<^sub>p \<dots> \<otimes>\<^sub>p F\<^sub>n(\<psi>\<^sub>n)\<close> by reordering the registers and unfolding nested register pairs.
  (For the unfolding of nested pairs, it is necessary that the corresponding \<^term>\<open>compatible F G\<close> facts are provable by the simplifier.)

  If the some of the pure states \<^term>\<open>\<psi>\<^sub>i\<close> themselves are \<open>\<otimes>\<^sub>p\<close>-tensors, they will be flattened if possible. 
  (If all necessary conditions can be proven, such as \<open>regular_register\<close> etc.)

  The method may either succeed, fail, or reduce the equality to a hopefully simpler one.\<close>

method pure_state_eq =
  (pure_state_flatten_nested?,
    rule pure_state_eqI;
    auto simp: register_pair_butterfly_tensor compatible_ac_rules default_prod_def
    simp flip: tensor_ell2_ket)

lemma example:
  fixes F :: \<open>bit update \<Rightarrow> 'c::{finite,default} update\<close>
    and G :: \<open>bit update \<Rightarrow> 'c update\<close>
  assumes [register]: \<open>compatible F G\<close>
  shows  \<open>(F;G) CNOT o\<^sub>C\<^sub>L (G;F) CNOT o\<^sub>C\<^sub>L (F;G) CNOT = (F;G) swap_ell2\<close>
proof -
  define Z where \<open>Z = complement (F;G)\<close>
  then have [register]: \<open>compatible Z F\<close> \<open>compatible Z G\<close>
    using assms compatible_complement_pair1 compatible_complement_pair2 compatible_sym by blast+

  have [simp]: \<open>iso_register (F;(G;Z))\<close>
    using Z_def assms complements_complement_pair complements_def by blast

  have eq1: \<open>((F;G) CNOT o\<^sub>C\<^sub>L (G;F) CNOT o\<^sub>C\<^sub>L (F;G) CNOT) *\<^sub>V (F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z))
           = (F;G) swap_ell2 *\<^sub>V (F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z))\<close> for f g z
  proof -
    have \<open>(F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z)) = ((F;G) (ket f \<otimes>\<^sub>s ket g) \<otimes>\<^sub>p Z(ket z))\<close>
      by pure_state_eq
    also have \<open>(F;G) CNOT *\<^sub>V \<dots> = ((F;G) (ket f \<otimes>\<^sub>s ket (g+f)) \<otimes>\<^sub>p Z(ket z))\<close>
      apply (subst state_apply1) by auto
    also have \<open>\<dots> = ((G;F) (ket (g+f) \<otimes>\<^sub>s ket f) \<otimes>\<^sub>p Z(ket z))\<close>
      by pure_state_eq
    also have \<open>(G;F) CNOT *\<^sub>V \<dots> = ((G;F) (ket (g+f) \<otimes>\<^sub>s ket g) \<otimes>\<^sub>p Z ket z)\<close>
      apply (subst state_apply1) by auto
    also have \<open>\<dots> = ((F;G) (ket g \<otimes>\<^sub>s ket (g+f)) \<otimes>\<^sub>p Z ket z)\<close>
      by pure_state_eq
    also have \<open>(F;G) CNOT *\<^sub>V \<dots> = ((F;G) ket g \<otimes>\<^sub>s ket f \<otimes>\<^sub>p Z ket z)\<close>
      apply (subst state_apply1) by auto
    also have \<open>\<dots> = (F(ket g) \<otimes>\<^sub>p G(ket f) \<otimes>\<^sub>p Z(ket z))\<close>
      by pure_state_eq
    finally have 1: \<open>((F;G) CNOT o\<^sub>C\<^sub>L (G;F) CNOT o\<^sub>C\<^sub>L (F;G) CNOT) *\<^sub>V (F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z)) = (F(ket g) \<otimes>\<^sub>p G(ket f) \<otimes>\<^sub>p Z(ket z))\<close>
      by auto

    have \<open>(F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z)) = ((F;G) (ket f \<otimes>\<^sub>s ket g) \<otimes>\<^sub>p Z(ket z))\<close>
      by pure_state_eq
    also have \<open>(F;G) swap_ell2 *\<^sub>V \<dots> = ((F;G) (ket g \<otimes>\<^sub>s ket f) \<otimes>\<^sub>p Z(ket z))\<close>
      by (auto simp: state_apply1 swap_ell2_tensor simp del: tensor_ell2_ket)
    also have \<open>\<dots> = (F(ket g) \<otimes>\<^sub>p G(ket f) \<otimes>\<^sub>p Z(ket z))\<close>
      by pure_state_eq
    finally have 2: \<open>(F;G) swap_ell2 *\<^sub>V (F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z)) = (F(ket g) \<otimes>\<^sub>p G(ket f) \<otimes>\<^sub>p Z(ket z))\<close>
      by -

    from 1 2 show ?thesis
      by simp
  qed

  then have eq1: \<open>((F;G) CNOT o\<^sub>C\<^sub>L (G;F) CNOT o\<^sub>C\<^sub>L (F;G) CNOT) *\<^sub>V \<psi>
           = (F;G) swap_ell2 *\<^sub>V \<psi>\<close> if \<open>\<psi> \<in> {(F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z))| f g z. True}\<close> for \<psi>
    using that by auto

  moreover have \<open>cspan {(F(ket f) \<otimes>\<^sub>p G(ket g) \<otimes>\<^sub>p Z(ket z))| f g z. True} = UNIV\<close>
    apply (simp only: double_exists setcompr_eq_image full_SetCompr_eq)
    apply simp
    apply (rule cspan_pure_state)
    by auto

  ultimately show ?thesis
    using cblinfun_eq_on_UNIV_span by blast
qed

end
