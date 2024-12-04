section \<open>\<open>Weak_Star_Topology\<close> -- Weak* topology on complex bounded operators\<close>

theory Weak_Star_Topology
  imports Trace_Class Weak_Operator_Topology Misc_Tensor_Product_TTS
begin

definition weak_star_topology :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L'b::chilbert_space) topology\<close>
  where \<open>weak_star_topology = pullback_topology UNIV (\<lambda>x. \<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x))
                              (product_topology (\<lambda>_. euclidean)  (Collect trace_class))\<close>

lemma open_map_product_topology_reindex:
  fixes \<pi> :: \<open>'b \<Rightarrow> 'a\<close>
  assumes bij_\<pi>: \<open>bij_betw \<pi> B A\<close> and ST: \<open>\<And>x. x\<in>B \<Longrightarrow> S x = T (\<pi> x)\<close>
  assumes g_def: \<open>\<And>f. g f = restrict (f o \<pi>) B\<close>
  shows \<open>open_map (product_topology T A) (product_topology S B) g\<close>
proof -
  define \<pi>' g' where \<open>\<pi>' = inv_into B \<pi>\<close> and \<open>g' f = restrict (f \<circ> \<pi>') A\<close> for f :: \<open>'b \<Rightarrow> 'c\<close>
  have bij_g: \<open>bij_betw g (Pi\<^sub>E A V) (Pi\<^sub>E B (V \<circ> \<pi>))\<close> for V
    apply (rule bij_betw_byWitness[where f'=g'])
    subgoal
      unfolding g'_def g_def \<pi>'_def
      by (smt (verit, best) PiE_restrict bij_\<pi> bij_betw_imp_surj_on bij_betw_inv_into_right comp_eq_dest_lhs inv_into_into restrict_def restrict_ext)
    subgoal
      unfolding g'_def g_def \<pi>'_def
      by (smt (verit, ccfv_SIG) PiE_restrict bij_\<pi> bij_betwE bij_betw_inv_into_left comp_apply restrict_apply restrict_ext)
    subgoal
      unfolding g'_def g_def \<pi>'_def
      using PiE_mem bij_\<pi> bij_betw_imp_surj_on by fastforce
    subgoal
      unfolding g'_def g_def \<pi>'_def
      by (smt (verit, best) PiE_mem bij_\<pi> bij_betw_iff_bijections bij_betw_inv_into_left comp_def image_subset_iff restrict_PiE_iff)
    done
  have open_gU: \<open>openin (product_topology S B) (g ` U)\<close> if \<open>openin (product_topology T A) U\<close> for U
  proof -
    from product_topology_open_contains_basis[OF that]
    obtain V where xAV: \<open>x \<in> PiE A (V x)\<close> and openV: \<open>openin (T a) (V x a)\<close> and finiteV: \<open>finite {a. V x a \<noteq> topspace (T a)}\<close>
      and AVU: \<open>Pi\<^sub>E A (V x) \<subseteq> U\<close> if \<open>x \<in> U\<close> for x a
      apply atomize_elim
      apply (rule choice4)
      by meson
    define V' where \<open>V' x b = (if b \<in> B then V x (\<pi> b) else topspace (S b))\<close> for b x
    have PiEV': \<open>Pi\<^sub>E B (V x \<circ> \<pi>) = Pi\<^sub>E B (V' x)\<close> for x
      by (metis (mono_tags, opaque_lifting) PiE_cong V'_def comp_def)
    from xAV AVU have AVU': \<open>(\<Union>x\<in>U. Pi\<^sub>E A (V x)) = U\<close>
      by blast
    have openVb: \<open>openin (S b) (V' x b)\<close> if [simp]: \<open>x \<in> U\<close> for x b
      by (auto simp: ST V'_def intro!: openV)
    have \<open>bij_betw \<pi>' {a\<in>A. V x a \<noteq> topspace (T a)} {b\<in>B. (V x \<circ> \<pi>) b \<noteq> topspace (S b)}\<close> for x
      apply (rule bij_betw_byWitness[where f'=\<pi>])
         apply simp
         apply (metis \<pi>'_def bij_\<pi> bij_betw_inv_into_right)
      using \<pi>'_def bij_\<pi> bij_betw_imp_inj_on apply fastforce
       apply (smt (verit, best) ST \<pi>'_def bij_\<pi> bij_betw_imp_surj_on comp_apply f_inv_into_f image_Collect_subsetI inv_into_into mem_Collect_eq)
      using ST bij_\<pi> bij_betwE by fastforce

    then have \<open>finite {b\<in>B. (V x \<circ> \<pi>) b \<noteq> topspace (S b)}\<close> if \<open>x \<in> U\<close> for x
      apply (rule bij_betw_finite[THEN iffD1])
      using that finiteV
      by simp
    also have \<open>{b\<in>B. (V x \<circ> \<pi>) b \<noteq> topspace (S b)} = {b. V' x b \<noteq> topspace (S b)}\<close> if \<open>x \<in> U\<close> for x
      by (auto simp: V'_def)
    finally have finiteV\<pi>: \<open>finite {b. V' x b \<noteq> topspace (S b)}\<close> if \<open>x \<in> U\<close> for x
      using that by -
    from openVb finiteV\<pi>
    have \<open>openin (product_topology S B) (Pi\<^sub>E B (V' x))\<close> if [simp]: \<open>x \<in> U\<close> for x
      by (auto intro!: product_topology_basis)
    with bij_g PiEV' have \<open>openin (product_topology S B) (g ` (Pi\<^sub>E A (V x)))\<close> if \<open>x \<in> U\<close> for x
      by (metis bij_betw_imp_surj_on that)
    then have \<open>openin (product_topology S B) (\<Union>x\<in>U. (g ` (Pi\<^sub>E A (V x))))\<close>
      by blast
    with AVU' show \<open>openin (product_topology S B) (g ` U)\<close>
      by (metis image_UN)
  qed
  show \<open>open_map (product_topology T A) (product_topology S B) g\<close>
    by (simp add: open_gU open_map_def)
qed

lemma homeomorphic_map_product_topology_reindex:
  fixes \<pi> :: \<open>'b \<Rightarrow> 'a\<close>
  assumes big_\<pi>: \<open>bij_betw \<pi> B A\<close> and ST: \<open>\<And>x. x\<in>B \<Longrightarrow> S x = T (\<pi> x)\<close>
  assumes g_def: \<open>\<And>f. g f = restrict (f o \<pi>) B\<close>
  shows \<open>homeomorphic_map (product_topology T A) (product_topology S B) g\<close>
proof (rule bijective_open_imp_homeomorphic_map)
  show open_map: \<open>open_map (product_topology T A) (product_topology S B) g\<close>
    using assms by (rule open_map_product_topology_reindex)
  define \<pi>' g' where \<open>\<pi>' = inv_into B \<pi>\<close> and \<open>g' f = restrict (f \<circ> \<pi>') A\<close> for f :: \<open>'b \<Rightarrow> 'c\<close>
  have \<open>bij_betw \<pi>' A B\<close>
    by (simp add: \<pi>'_def big_\<pi> bij_betw_inv_into)

  have l1: \<open>x \<in> (\<lambda>x. restrict (x \<circ> \<pi>) B) ` (\<Pi>\<^sub>E i\<in>A. topspace (T i))\<close> if \<open>x \<in> (\<Pi>\<^sub>E i\<in>B. topspace (S i))\<close> for x
  proof -
    have \<open>g' x \<in> (\<Pi>\<^sub>E i\<in>A. topspace (T i))\<close>
      by (smt (z3) g'_def PiE_mem \<pi>'_def assms(1) assms(2) bij_betw_imp_surj_on bij_betw_inv_into_right comp_apply inv_into_into restrict_PiE_iff that)
    moreover have \<open>x = restrict (g' x \<circ> \<pi>) B\<close>
      by (smt (verit) PiE_restrict \<pi>'_def assms(1) bij_betwE bij_betw_inv_into_left comp_apply restrict_apply restrict_ext that g'_def)
    ultimately show ?thesis
      by (intro rev_image_eqI)
  qed
  show topspace: \<open>g ` topspace (product_topology T A) = topspace (product_topology S B)\<close>
    using l1 assms unfolding g_def [abs_def] topspace_product_topology
    by (auto simp: bij_betw_def)

  show \<open>inj_on g (topspace (product_topology T A))\<close>
    apply (simp add: g_def[abs_def])
    by (smt (verit) PiE_ext assms(1) bij_betw_iff_bijections comp_apply inj_on_def restrict_apply') 
  
  have open_map_g': \<open>open_map (product_topology S B) (product_topology T A) g'\<close>
    using \<open>bij_betw \<pi>' A B\<close> apply (rule open_map_product_topology_reindex)
     apply (metis ST \<pi>'_def big_\<pi> bij_betw_imp_surj_on bij_betw_inv_into_right inv_into_into)
    using g'_def by blast
  have g'g: \<open>g' (g x) = x\<close> if \<open>x \<in> topspace (product_topology T A)\<close> for x
    using that unfolding g'_def g_def topspace_product_topology
    by (smt (verit) PiE_restrict \<open>bij_betw \<pi>' A B\<close> \<pi>'_def big_\<pi> bij_betwE
          bij_betw_inv_into_right comp_def restrict_apply' restrict_ext)
  have gg': \<open>g (g' x) = x\<close> if \<open>x \<in> topspace (product_topology S B)\<close> for x
    unfolding g'_def g_def
    by (metis (no_types, lifting) g'_def f_inv_into_f g'g g_def inv_into_into that topspace)

  from open_map_g'
  have \<open>openin (product_topology T A) (g' ` U)\<close> if \<open>openin (product_topology S B) U\<close> for U
    using open_map_def that by blast
  also have \<open>g' ` U = (g -` U) \<inter> (topspace (product_topology T A))\<close> if \<open>openin (product_topology S B) U\<close> for U
  proof -
    from that
    have U_top: \<open>U \<subseteq> topspace (product_topology S B)\<close>
      using openin_subset by blast
    from topspace
    have topspace': \<open>topspace (product_topology T A) = g' ` topspace (product_topology S B)\<close>
      by (metis bij_betw_byWitness bij_betw_def calculation g'g gg' openin_subset openin_topspace)
    show ?thesis
      unfolding topspace'
      using U_top gg' 
      by auto
  qed
  finally have open_gU2: \<open>openin (product_topology T A) ((g -` U) \<inter> (topspace (product_topology T A)))\<close>
    if \<open>openin (product_topology S B) U\<close> for U
  using that by blast

  then show \<open>continuous_map (product_topology T A) (product_topology S B) g\<close>
    by (smt (verit, best) g'g image_iff open_eq_continuous_inverse_map open_map_g' topspace)
qed

lemma weak_star_topology_def':
  \<open>weak_star_topology = pullback_topology UNIV (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) euclidean\<close>
proof -
  define f g where \<open>f x = (\<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x))\<close> and \<open>g f' = f' o from_trace_class\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and f' :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> complex\<close>
  have \<open>homeomorphic_map (product_topology (\<lambda>_. euclidean) (Collect trace_class)) (product_topology (\<lambda>_. euclidean) UNIV) g\<close>
    unfolding g_def[abs_def]
    apply (rule homeomorphic_map_product_topology_reindex[where \<pi>=from_trace_class])
    subgoal
      by (smt (verit, best) UNIV_I bij_betwI' from_trace_class from_trace_class_cases from_trace_class_inject)
    by auto
  then have homeo_g: \<open>homeomorphic_map (product_topology (\<lambda>_. euclidean) (Collect trace_class)) euclidean g\<close>
    by (simp add: euclidean_product_topology)
  have \<open>weak_star_topology = pullback_topology UNIV f (product_topology (\<lambda>_. euclidean) (Collect trace_class))\<close>
    by (simp add: weak_star_topology_def pullback_topology_homeo_cong homeo_g f_def[abs_def])
  also have \<open>\<dots> = pullback_topology UNIV (g o f) euclidean\<close>
    by (subst pullback_topology_homeo_cong)
       (auto simp add: homeo_g f_def[abs_def] split: if_splits)
  also have \<open>\<dots> = pullback_topology UNIV (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) euclidean\<close>
    by (auto simp: f_def[abs_def] g_def[abs_def] o_def)
  finally show ?thesis
    by -
qed

lemma weak_star_topology_topspace[simp]:
  "topspace weak_star_topology = UNIV"
  unfolding weak_star_topology_def topspace_pullback_topology topspace_euclidean by auto

lemma weak_star_topology_basis':
  fixes f::"('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space)" and U::"'i \<Rightarrow> complex set" and t::"'i \<Rightarrow> ('b,'a) trace_class"
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> open (U i)" 
  shows "openin weak_star_topology {f. \<forall>i\<in>I. trace (from_trace_class (t i) o\<^sub>C\<^sub>L f) \<in> U i}"
proof -
  have 1: "open {g. \<forall>i\<in>I. g (t i) \<in> U i}"
    using assms by (rule product_topology_basis')
  show ?thesis
    unfolding weak_star_topology_def'
    apply (subst openin_pullback_topology)
    apply (intro exI conjI)
    using 1 by auto
qed

lemma weak_star_topology_basis:
  fixes f::"('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space)" and U::"'i \<Rightarrow> complex set" and t::"'i \<Rightarrow> ('b \<Rightarrow>\<^sub>C\<^sub>L 'a)"
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> open (U i)" 
  assumes tc: \<open>\<And>i. i \<in> I \<Longrightarrow> trace_class (t i)\<close>
  shows "openin weak_star_topology {f. \<forall>i\<in>I. trace (t i o\<^sub>C\<^sub>L f) \<in> U i}"
proof -
  obtain t' where tt': \<open>t i = from_trace_class (t' i)\<close> if \<open>i \<in> I\<close> for i
    by (atomize_elim, rule choice) (use tc from_trace_class_cases in blast)
  show ?thesis
    using assms by (auto simp: tt' o_def intro!: weak_star_topology_basis')
qed

lemma wot_weaker_than_weak_star:
  "continuous_map weak_star_topology cweak_operator_topology (\<lambda>f. f)"
  unfolding weak_star_topology_def cweak_operator_topology_def
proof (rule continuous_map_pullback_both)
  define g' :: \<open>('b \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> complex) \<Rightarrow> 'b \<times> 'a \<Rightarrow> complex\<close> where 
    \<open>g' f = (\<lambda>(x,y). f (butterfly y x))\<close> for f
  show \<open>(\<lambda>x. \<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x)) -` topspace (product_topology (\<lambda>_. euclidean) (Collect trace_class)) \<inter> UNIV
    \<subseteq> (\<lambda>f. f) -` UNIV\<close>
    by simp
  show \<open>g' (\<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x)) = (\<lambda>(xa, y). xa \<bullet>\<^sub>C (x *\<^sub>V y))\<close>
    if \<open>(\<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x)) \<in> topspace (product_topology (\<lambda>_. euclidean) (Collect trace_class))\<close>
    for x
    by (auto intro!: ext simp: g'_def trace_butterfly_comp)
  show \<open>continuous_map (product_topology (\<lambda>_. euclidean) (Collect trace_class)) euclidean g'\<close>
    apply (subst euclidean_product_topology[symmetric])
    apply (rule continuous_map_coordinatewise_then_product)
    subgoal for i
      unfolding g'_def case_prod_unfold
      by (metis continuous_map_product_projection mem_Collect_eq trace_class_butterfly)
    subgoal
      by (auto simp: g'_def[abs_def])
    done
qed

lemma wot_weaker_than_weak_star':
  \<open>openin cweak_operator_topology U \<Longrightarrow> openin weak_star_topology U\<close>
  using wot_weaker_than_weak_star[where 'a='a and 'b='b]
  by (auto simp: continuous_map_def weak_star_topology_topspace)

lemma weak_star_topology_continuous_duality':
  shows "continuous_map weak_star_topology euclidean (\<lambda>x. trace (from_trace_class t o\<^sub>C\<^sub>L x))"
proof -
  have "continuous_map weak_star_topology euclidean ((\<lambda>f. f t) o (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)))"
    unfolding weak_star_topology_def' apply (rule continuous_map_pullback)
    using continuous_on_product_coordinates by fastforce
  then show ?thesis unfolding comp_def by simp
qed

lemma weak_star_topology_continuous_duality:
  assumes \<open>trace_class t\<close>
  shows "continuous_map weak_star_topology euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L x))"
  by (metis assms from_trace_class_cases mem_Collect_eq weak_star_topology_continuous_duality')

lemma continuous_on_weak_star_topo_iff_coordinatewise:
  fixes f :: \<open>'a \<Rightarrow> 'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close>
  shows "continuous_map T weak_star_topology f
    \<longleftrightarrow> (\<forall>t. trace_class t \<longrightarrow> continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L f x)))"
proof (intro iffI allI impI)
  fix t :: \<open>'c \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assume \<open>trace_class t\<close>
  assume "continuous_map T weak_star_topology f"
  with continuous_map_compose[OF this weak_star_topology_continuous_duality, OF \<open>trace_class t\<close>]
  have "continuous_map T euclidean ((\<lambda>x. trace (t o\<^sub>C\<^sub>L x)) o f)"
    by simp
  then show "continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L f x))"
    unfolding comp_def by auto
next
  assume \<open>\<forall>t. trace_class t \<longrightarrow> continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L f x))\<close>
  then have \<open>continuous_map T euclidean (\<lambda>x. trace (from_trace_class t o\<^sub>C\<^sub>L f x))\<close> for t
    by auto
  then have *: "continuous_map T euclidean ((\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) o f)"
    by (auto simp flip: euclidean_product_topology simp: o_def)
  show "continuous_map T weak_star_topology f"
    unfolding weak_star_topology_def'
    apply (rule continuous_map_pullback')
    by (auto simp add: *)
qed

lemma weak_star_topology_weaker_than_euclidean:
  "continuous_map euclidean weak_star_topology (\<lambda>f. f)"
  apply (subst continuous_on_weak_star_topo_iff_coordinatewise)
  by (auto intro!: linear_continuous_on bounded_clinear.bounded_linear bounded_clinear_trace_duality)


typedef (overloaded) ('a,'b) cblinfun_weak_star = \<open>UNIV :: ('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector) set\<close> 
  morphisms from_weak_star to_weak_star ..
setup_lifting type_definition_cblinfun_weak_star

lift_definition id_weak_star :: \<open>('a::complex_normed_vector, 'a) cblinfun_weak_star\<close> is id_cblinfun .

instantiation cblinfun_weak_star :: (complex_normed_vector, complex_normed_vector) complex_vector begin
lift_definition scaleC_cblinfun_weak_star :: \<open>complex \<Rightarrow> ('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star\<close> 
  is \<open>scaleC\<close> .
lift_definition uminus_cblinfun_weak_star :: \<open>('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star\<close> is uminus .
lift_definition zero_cblinfun_weak_star :: \<open>('a, 'b) cblinfun_weak_star\<close> is 0 .
lift_definition minus_cblinfun_weak_star :: \<open>('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star\<close> is minus .
lift_definition plus_cblinfun_weak_star :: \<open>('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star\<close> is plus .
lift_definition scaleR_cblinfun_weak_star :: \<open>real \<Rightarrow> ('a, 'b) cblinfun_weak_star \<Rightarrow> ('a, 'b) cblinfun_weak_star\<close> is scaleR .
instance
  by (intro_classes; transfer) (auto simp add: scaleR_scaleC scaleC_add_right scaleC_add_left)
end

instantiation cblinfun_weak_star :: (chilbert_space, chilbert_space) topological_space begin
lift_definition open_cblinfun_weak_star :: \<open>('a, 'b) cblinfun_weak_star set \<Rightarrow> bool\<close> is \<open>openin weak_star_topology\<close> .
instance
proof intro_classes
  show \<open>open (UNIV :: ('a,'b) cblinfun_weak_star set)\<close>
    by transfer (metis weak_star_topology_topspace openin_topspace)
  show \<open>open S \<Longrightarrow> open T \<Longrightarrow> open (S \<inter> T)\<close> for S T :: \<open>('a,'b) cblinfun_weak_star set\<close>
    by transfer auto
  show \<open>\<forall>S\<in>K. open S \<Longrightarrow> open (\<Union> K)\<close> for K :: \<open>('a,'b) cblinfun_weak_star set set\<close>
    by transfer auto
qed
end

lemma transfer_nhds_weak_star_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(cr_cblinfun_weak_star ===> rel_filter cr_cblinfun_weak_star) (nhdsin weak_star_topology) nhds\<close>
proof -
  have "(cr_cblinfun_weak_star ===> rel_filter cr_cblinfun_weak_star)
          (\<lambda>a. \<Sqinter> (principal ` {S. openin weak_star_topology S \<and> a \<in> S}))
          (\<lambda>a. \<Sqinter> (principal ` {S. open S \<and> a \<in> S}))"
    by transfer_prover
  thus ?thesis
    unfolding nhds_def nhdsin_def weak_star_topology_topspace by simp
qed

lemma limitin_weak_star_topology':
  \<open>limitin weak_star_topology f l F \<longleftrightarrow> (\<forall>t. ((\<lambda>j. trace (from_trace_class t o\<^sub>C\<^sub>L f j)) \<longlongrightarrow> trace (from_trace_class t o\<^sub>C\<^sub>L l)) F)\<close>
  by (simp add: weak_star_topology_def' limitin_pullback_topology tendsto_coordinatewise)

lemma limitin_weak_star_topology:
  \<open>limitin weak_star_topology f l F \<longleftrightarrow> (\<forall>t. trace_class t \<longrightarrow> ((\<lambda>j. trace (t o\<^sub>C\<^sub>L f j)) \<longlongrightarrow> trace (t o\<^sub>C\<^sub>L l)) F)\<close>
  by (smt (z3) eventually_mono from_trace_class from_trace_class_cases limitin_weak_star_topology' mem_Collect_eq tendsto_def)

lemma filterlim_weak_star_topology:
  \<open>filterlim f (nhdsin weak_star_topology l) = limitin weak_star_topology f l\<close>
  by (auto simp: weak_star_topology_topspace simp flip: filterlim_nhdsin_iff_limitin)

lemma openin_weak_star_topology': \<open>openin weak_star_topology U \<longleftrightarrow> (\<exists>V. open V \<and> U = (\<lambda>x t. trace (from_trace_class t o\<^sub>C\<^sub>L x)) -` V)\<close>
  by (simp add: weak_star_topology_def' openin_pullback_topology)

(* lemma openin_weak_star_topology: \<open>openin weak_star_topology U \<longleftrightarrow> (\<exists>V. open V \<and> U = (\<lambda>x t. trace (t o\<^sub>C\<^sub>L x)) -` V)\<close> *)

lemma hausdorff_weak_star[simp]: \<open>Hausdorff_space weak_star_topology\<close>
  by (metis cweak_operator_topology_topspace hausdorff_cweak_operator_topology 
            Hausdorff_space_def weak_star_topology_topspace wot_weaker_than_weak_star')
(* proof (unfold Hausdorff_space_def, intro ballI impI)
  fix x y :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> assume \<open>x \<noteq> y\<close>
  then obtain a b where \<open>a \<bullet>\<^sub>C (x *\<^sub>V b) \<noteq> a \<bullet>\<^sub>C (y *\<^sub>V b)\<close>
    by (meson cblinfun_eqI cinner_extensionality)
  then have \<open>trace (butterfly b a o\<^sub>C\<^sub>L x) \<noteq> trace (butterfly b a o\<^sub>C\<^sub>L y)\<close>
    by (simp add: trace_butterfly_comp)
  then obtain U' V' where U': \<open>trace (butterfly b a o\<^sub>C\<^sub>L x) \<in> U'\<close> and V': \<open>trace (butterfly b a o\<^sub>C\<^sub>L y) \<in> V'\<close> 
    and \<open>open U'\<close> and \<open>open V'\<close> and \<open>U' \<inter> V' = {}\<close>
    by (meson separation_t2)
  define U'' V'' where \<open>U'' = {f. \<forall>i\<in>{butterfly b a}. f i \<in> U'}\<close> and \<open>V'' = {f. \<forall>i\<in>{butterfly b a}. f i \<in> V'}\<close>
  have \<open>open U''\<close>
    unfolding U''_def apply (rule product_topology_basis')
    using \<open>open U'\<close> by auto
  have \<open>open V''\<close>
    unfolding V''_def apply (rule product_topology_basis')
    using \<open>open V'\<close> by auto
  define U V where \<open>U = (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) -` U''\<close> and
    \<open>V = (\<lambda>x t. if trace_class t then trace (t o\<^sub>C\<^sub>L x) else 0) -` V''\<close>
  have openU: \<open>openin weak_star_topology U\<close>
    using U_def \<open>open U''\<close> openin_weak_star_topology by blast
  have openV: \<open>openin weak_star_topology V\<close>
    using V_def \<open>open V''\<close> openin_weak_star_topology by blast
  have \<open>x \<in> U\<close>
    by (auto simp: U_def U''_def U')
  have \<open>y \<in> V\<close>
    by (auto simp: V_def V''_def V')
  have \<open>U \<inter> V = {}\<close>
    using \<open>U' \<inter> V' = {}\<close> by (auto simp: U_def V_def U''_def V''_def)
  show \<open>\<exists>U V. openin weak_star_topology U \<and> openin weak_star_topology V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}\<close>
    apply (rule exI[of _ U], rule exI[of _ V])
    using \<open>x \<in> U\<close> \<open>y \<in> V\<close> openU openV \<open>U \<inter> V = {}\<close> by auto
qed *)


lemma Domainp_cr_cblinfun_weak_star[simp]: \<open>Domainp cr_cblinfun_weak_star = (\<lambda>_. True)\<close>
  by (metis (no_types, opaque_lifting) DomainPI cblinfun_weak_star.left_total left_totalE)

lemma Rangep_cr_cblinfun_weak_star[simp]: \<open>Rangep cr_cblinfun_weak_star = (\<lambda>_. True)\<close>
  by (meson RangePI cr_cblinfun_weak_star_def)


lemma transfer_euclidean_weak_star_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_topology cr_cblinfun_weak_star) weak_star_topology euclidean\<close>
proof (unfold rel_topology_def, intro conjI allI impI)
  show \<open>(rel_set cr_cblinfun_weak_star ===> (=)) (openin weak_star_topology) (openin euclidean)\<close>
    unfolding rel_fun_def rel_set_def open_openin [symmetric] cr_cblinfun_weak_star_def
    by (transfer, intro allI impI arg_cong[of _ _ "openin x" for x]) blast
next
  fix U :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
  assume \<open>openin weak_star_topology U\<close>
  show \<open>Domainp (rel_set cr_cblinfun_weak_star) U\<close>
    by (simp add: Domainp_set)
next
  fix U :: \<open>('a, 'b) cblinfun_weak_star set\<close>
  assume \<open>openin euclidean U\<close>
  show \<open>Rangep (rel_set cr_cblinfun_weak_star) U\<close>
    by (simp add: Rangep_set)
qed



instance cblinfun_weak_star :: (chilbert_space, chilbert_space) t2_space
  apply (rule hausdorff_OFCLASS_t2_space)
  apply transfer
  by (rule hausdorff_weak_star)
(* proof intro_classes
  fix a b :: \<open>('a,'b) cblinfun_weak_star\<close>
  assume \<open>a \<noteq> b\<close>
  then have \<open>Abs_cblinfun_wot (from_weak_star a) \<noteq> Abs_cblinfun_wot (from_weak_star b)\<close>
    by (simp add: Abs_cblinfun_wot_inject from_weak_star_inject)
  from hausdorff[OF this]

  show \<open>a \<noteq> b \<Longrightarrow> \<exists>U V. open U \<and> open V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}\<close>
    apply transfer using wot_weaker_than_weak_star' by auto
qed *)

lemma weak_star_topology_plus_cont: \<open>LIM (x,y) nhdsin weak_star_topology a \<times>\<^sub>F nhdsin weak_star_topology b.
            x + y :> nhdsin weak_star_topology (a + b)\<close>
proof -
  have trace_plus: \<open>trace (t o\<^sub>C\<^sub>L (a + b)) = trace (t o\<^sub>C\<^sub>L a) + trace (t o\<^sub>C\<^sub>L b)\<close> if \<open>trace_class t\<close> for t :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and a b
    by (auto simp: cblinfun_compose_add_right trace_plus that trace_class_comp_left)
  show ?thesis
    unfolding weak_star_topology_def'
    by (rule pullback_topology_bi_cont[where f'=plus])
       (auto simp: trace_plus case_prod_unfold tendsto_add_Pair)
qed

instance cblinfun_weak_star :: (chilbert_space, chilbert_space) topological_group_add
proof intro_classes
  show \<open>((\<lambda>x. fst x + snd x) \<longlongrightarrow> a + b) (nhds a \<times>\<^sub>F nhds b)\<close> for a b :: \<open>('a,'b) cblinfun_weak_star\<close>
    apply transfer
    using weak_star_topology_plus_cont
    by (auto simp: case_prod_unfold)

  have \<open>continuous_map weak_star_topology euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L - x))\<close> if \<open>trace_class t\<close> for t :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    using weak_star_topology_continuous_duality[of \<open>-t\<close>]
    by (auto simp: cblinfun_compose_uminus_left cblinfun_compose_uminus_right intro!: that trace_class_uminus)
  then have *: \<open>continuous_map weak_star_topology weak_star_topology (uminus :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Rightarrow> _)\<close>
    by (auto simp: continuous_on_weak_star_topo_iff_coordinatewise)
  show \<open>(uminus \<longlongrightarrow> - a) (nhds a)\<close> for a :: \<open>('a,'b) cblinfun_weak_star\<close>
    apply (subst tendsto_at_iff_tendsto_nhds[symmetric])
    apply (subst isCont_def[symmetric])
    apply (rule continuous_on_interior[where S=UNIV])
     apply (subst continuous_map_iff_continuous2[symmetric])
     apply transfer
    using * by auto
qed

lemma continuous_map_left_comp_weak_star: 
  \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>a::'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _. b o\<^sub>C\<^sub>L a)\<close> 
  for b :: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close>
proof (unfold weak_star_topology_def, rule continuous_map_pullback_both)
  define g' :: \<open>('b \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> complex) \<Rightarrow> ('c \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> complex)\<close> where
    \<open>g' f = (\<lambda>t\<in>Collect trace_class. f (t o\<^sub>C\<^sub>L b))\<close> for f
  show \<open>(\<lambda>x. \<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x)) -` topspace (product_topology (\<lambda>_. euclidean) (Collect trace_class)) \<inter> UNIV
    \<subseteq> (o\<^sub>C\<^sub>L) b -` UNIV\<close>
    by simp
  show \<open>g' (\<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x)) = (\<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L (b o\<^sub>C\<^sub>L x)))\<close> for x
    by (auto intro!: ext simp: g'_def[abs_def] cblinfun_compose_assoc trace_class_comp_left)
  show \<open>continuous_map (product_topology (\<lambda>_. euclidean) (Collect trace_class))
     (product_topology (\<lambda>_. euclidean) (Collect trace_class)) g'\<close>
    apply (rule continuous_map_coordinatewise_then_product)
    subgoal for i
      unfolding g'_def
      apply (subst restrict_apply')
      subgoal by simp     
      subgoal by (metis continuous_map_product_projection mem_Collect_eq trace_class_comp_left)
      done
    subgoal by (auto simp: g'_def[abs_def])
    done
qed

lemma continuous_map_right_comp_weak_star: 
  \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>b::'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _. b o\<^sub>C\<^sub>L a)\<close> 
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
proof (subst weak_star_topology_def, subst weak_star_topology_def, rule continuous_map_pullback_both)
  define g' :: \<open>('c \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> complex) \<Rightarrow> ('c \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> complex)\<close> where
    \<open>g' f = (\<lambda>t\<in>Collect trace_class. f (a o\<^sub>C\<^sub>L t))\<close> for f
  show \<open>(\<lambda>x. \<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x)) -` topspace (product_topology (\<lambda>_. euclidean) (Collect trace_class)) \<inter> UNIV
    \<subseteq> (\<lambda>b. b o\<^sub>C\<^sub>L a) -` UNIV\<close>
    by simp
  have *: "trace (a o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L x) = trace (y o\<^sub>C\<^sub>L (x o\<^sub>C\<^sub>L a))" if "trace_class y" for x :: "'b \<Rightarrow>\<^sub>C\<^sub>L 'c" and y :: "'c \<Rightarrow>\<^sub>C\<^sub>L 'a"
    by (simp add: circularity_of_trace simp_a_oCL_b that trace_class_comp_left)
  show \<open>g' (\<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L x)) = (\<lambda>t\<in>Collect trace_class. trace (t o\<^sub>C\<^sub>L (x o\<^sub>C\<^sub>L a)))\<close> for x
    by (auto intro!: ext simp: g'_def[abs_def] trace_class_comp_right *)
  show \<open>continuous_map (product_topology (\<lambda>_. euclidean) (Collect trace_class))
     (product_topology (\<lambda>_. euclidean) (Collect trace_class)) g'\<close>
    apply (rule continuous_map_coordinatewise_then_product)
    subgoal for i
      unfolding g'_def mem_Collect_eq
      apply (subst restrict_apply')
      subgoal by simp
      subgoal
        by (metis continuous_map_product_projection mem_Collect_eq trace_class_comp_right)
      done
    subgoal by (auto simp: g'_def[abs_def])
    done
qed

lemma continuous_map_scaleC_weak_star: \<open>continuous_map weak_star_topology weak_star_topology (scaleC c)\<close>
  apply (subst asm_rl[of \<open>scaleC c = (o\<^sub>C\<^sub>L) (c *\<^sub>C id_cblinfun)\<close>])
  subgoal by auto
  subgoal by (rule continuous_map_left_comp_weak_star)
  done

lemma continuous_scaleC_weak_star: \<open>continuous_on X (scaleC c :: (_,_) cblinfun_weak_star \<Rightarrow> _)\<close>
  apply (rule continuous_on_subset[rotated, where s=UNIV])
  subgoal by simp
  subgoal
    apply (subst continuous_map_iff_continuous2[symmetric])
    apply transfer
    by (rule continuous_map_scaleC_weak_star)
  done

lemma weak_star_closure_is_csubspace[simp]:
  fixes A::"('a::chilbert_space, 'b::chilbert_space) cblinfun_weak_star set"
  assumes \<open>csubspace A\<close>
  shows \<open>csubspace (closure A)\<close>
proof (rule complex_vector.subspaceI)
  include lattice_syntax
  show 0: \<open>0 \<in> closure A\<close>
    by (simp add: assms closure_def complex_vector.subspace_0)
  show \<open>x + y \<in> closure A\<close> if \<open>x \<in> closure A\<close> \<open>y \<in> closure A\<close> for x y
  proof -
    define FF where \<open>FF = ((nhds x \<sqinter> principal A) \<times>\<^sub>F (nhds y \<sqinter> principal A))\<close>
    have nt: \<open>FF \<noteq> bot\<close>
      by (simp add: prod_filter_eq_bot that(1) that(2) FF_def flip: closure_nhds_principal)
    have \<open>\<forall>\<^sub>F x in FF. fst x \<in> A\<close>
      unfolding FF_def
      by (smt (verit, ccfv_SIG) eventually_prod_filter fst_conv inf_sup_ord(2) le_principal)
    moreover have \<open>\<forall>\<^sub>F x in FF. snd x \<in> A\<close>
      unfolding FF_def
      by (smt (verit, ccfv_SIG) eventually_prod_filter snd_conv inf_sup_ord(2) le_principal)
    ultimately have FF_plus: \<open>\<forall>\<^sub>F x in FF. fst x + snd x \<in> A\<close>
      by (smt (verit, best) assms complex_vector.subspace_add eventually_elim2)

    have \<open>(fst \<longlongrightarrow> x) ((nhds x \<sqinter> principal A) \<times>\<^sub>F (nhds y \<sqinter> principal A))\<close>
      apply (simp add: filterlim_def)
      using filtermap_fst_prod_filter
      using le_inf_iff by blast
    moreover have \<open>(snd \<longlongrightarrow> y) ((nhds x \<sqinter> principal A) \<times>\<^sub>F (nhds y \<sqinter> principal A))\<close>
      apply (simp add: filterlim_def)
      using filtermap_snd_prod_filter
      using le_inf_iff by blast
    ultimately have \<open>(id \<longlongrightarrow> (x,y)) FF\<close>
      by (simp add: filterlim_def nhds_prod prod_filter_mono FF_def)

    moreover note tendsto_add_Pair[of x y]
    ultimately have \<open>(((\<lambda>x. fst x + snd x) o id) \<longlongrightarrow> (\<lambda>x. fst x + snd x) (x,y)) FF\<close>
      unfolding filterlim_def nhds_prod
      by (smt (verit, best) filterlim_compose filterlim_def filterlim_filtermap fst_conv snd_conv tendsto_compose_filtermap)

    then have \<open>((\<lambda>x. fst x + snd x) \<longlongrightarrow> (x+y)) FF\<close>
      by simp
    then show \<open>x + y \<in> closure A\<close>
      using nt FF_plus by (rule limit_in_closure)
  qed
  show \<open>c *\<^sub>C x \<in> closure A\<close> if \<open>x \<in> closure A\<close> for x c
  proof (cases "c = 0")
    case False
    have "(*\<^sub>C) c ` closure A \<subseteq> closure A"
      using csubspace_scaleC_invariant[of c A] \<open>csubspace A\<close> False closure_subset[of A] 
      by (intro image_closure_subset continuous_scaleC_weak_star closed_closure) auto
    thus ?thesis
      using that by blast
  qed (use 0 in auto)
qed


lemma transfer_csubspace_cblinfun_weak_star[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_weak_star ===> (=)) csubspace csubspace\<close>
  unfolding complex_vector.subspace_def
  by transfer_prover

lemma transfer_closed_cblinfun_weak_star[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_weak_star ===> (=)) (closedin weak_star_topology) closed\<close>
proof -
  have "(rel_set cr_cblinfun_weak_star ===> (=))
          (\<lambda>S. openin weak_star_topology (UNIV - S))
          (\<lambda>S. open (UNIV - S)) "
    by transfer_prover
  thus ?thesis
    by (simp add: closed_def[abs_def] closedin_def[abs_def] Compl_eq_Diff_UNIV)
qed

lemma transfer_closure_cblinfun_weak_star[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_weak_star ===> rel_set cr_cblinfun_weak_star) (Abstract_Topology.closure_of weak_star_topology) closure\<close>
  apply (subst closure_of_hull[where X=weak_star_topology, unfolded weak_star_topology_topspace, simplified, abs_def])
  apply (subst closure_hull[abs_def])
  unfolding hull_def
  by transfer_prover

lemma weak_star_closure_is_csubspace'[simp]:
  fixes A::"('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) set"
  assumes \<open>csubspace A\<close>
  shows \<open>csubspace (weak_star_topology closure_of A)\<close>
  using weak_star_closure_is_csubspace[of \<open>to_weak_star ` A\<close>] assms
  apply (transfer fixing: A)
  by simp

lemma has_sum_closed_weak_star_topology:
  assumes aA: \<open>\<And>i. a i \<in> A\<close>
  assumes closed: \<open>closedin weak_star_topology A\<close>
  assumes subspace: \<open>csubspace A\<close>
  assumes has_sum: \<open>\<And>t. trace_class t \<Longrightarrow> ((\<lambda>i. trace (t o\<^sub>C\<^sub>L a i)) has_sum trace (t o\<^sub>C\<^sub>L b)) I\<close>
  shows \<open>b \<in> A\<close>
proof -
  have 1: \<open>range (sum a) \<subseteq> A\<close>
  proof -
    have \<open>sum a X \<in> A\<close> for X
      apply (induction X rule:infinite_finite_induct)
      by (auto simp add: subspace complex_vector.subspace_0 aA complex_vector.subspace_add)
    then show ?thesis
      by auto
  qed

  from has_sum
  have \<open>((\<lambda>F. \<Sum>i\<in>F. trace (t o\<^sub>C\<^sub>L a i)) \<longlongrightarrow> trace (t o\<^sub>C\<^sub>L b)) (finite_subsets_at_top I)\<close> if \<open>trace_class t\<close> for t
    by (auto intro: that simp: has_sum_def)
  then have \<open>limitin weak_star_topology (\<lambda>F. \<Sum>i\<in>F. a i) b (finite_subsets_at_top I)\<close>
    by (auto simp add: limitin_weak_star_topology cblinfun_compose_sum_right trace_sum trace_class_comp_left)
  then show \<open>b \<in> A\<close>
    using 1 closed apply (rule limitin_closedin)
    by simp
qed

lemma has_sum_in_weak_star:
  \<open>has_sum_in weak_star_topology f A l \<longleftrightarrow> 
     (\<forall>t. trace_class t \<longrightarrow> ((\<lambda>i. trace (t o\<^sub>C\<^sub>L f i)) has_sum trace (t o\<^sub>C\<^sub>L l)) A)\<close>
proof -
  have *: \<open>trace (t o\<^sub>C\<^sub>L sum f F) = sum (\<lambda>i. trace (t o\<^sub>C\<^sub>L f i)) F\<close> if \<open>trace_class t\<close> 
    for t F
    by (simp_all add: cblinfun_compose_sum_right that trace_class_comp_left trace_sum)
  show ?thesis
    by (simp add: * has_sum_def has_sum_in_def limitin_weak_star_topology)
qed

lemma has_sum_butterfly_ket: \<open>has_sum_in weak_star_topology (\<lambda>i. butterfly (ket i) (ket i)) UNIV id_cblinfun\<close>
proof (rule has_sum_in_weak_star[THEN iffD2, rule_format])
  fix t :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  assume [simp]: \<open>trace_class t\<close>
  from trace_has_sum[OF is_onb_ket \<open>trace_class t\<close>]
  have \<open>((\<lambda>i. ket i \<bullet>\<^sub>C (t *\<^sub>V ket i)) has_sum trace t) UNIV\<close>
    apply (subst (asm) has_sum_reindex)
    by (auto simp: o_def)
  then show \<open>((\<lambda>i. trace (t o\<^sub>C\<^sub>L butterfly (ket i) (ket i))) has_sum trace (t o\<^sub>C\<^sub>L id_cblinfun)) UNIV\<close>
    by (simp add: trace_butterfly_comp')
qed

lemma sandwich_weak_star_cont[simp]:
  \<open>continuous_map weak_star_topology weak_star_topology (sandwich A)\<close>
  using continuous_map_compose[OF continuous_map_left_comp_weak_star continuous_map_right_comp_weak_star]
  by (auto simp: o_def sandwich_apply[abs_def])

lemma has_sum_butterfly_ket_a: \<open>has_sum_in weak_star_topology (\<lambda>i. butterfly (a *\<^sub>V ket i) (ket i)) UNIV a\<close>
proof -
  have \<open>has_sum_in weak_star_topology ((\<lambda>b. a o\<^sub>C\<^sub>L b) \<circ> (\<lambda>i. butterfly (ket i) (ket i))) UNIV (a o\<^sub>C\<^sub>L id_cblinfun)\<close>
    apply (rule has_sum_in_comm_additive)
    by (auto intro!: has_sum_butterfly_ket continuous_map_is_continuous_at_point limitin_continuous_map
        continuous_map_left_comp_weak_star  cblinfun_compose_add_right
        simp: Modules.additive_def)
  then show ?thesis
    by (auto simp: o_def cblinfun_comp_butterfly)
qed


lemma finite_rank_weak_star_dense[simp]: \<open>weak_star_topology closure_of (Collect finite_rank) = (UNIV :: ('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) set)\<close>
proof -
  have \<open>x \<in> weak_star_topology closure_of (Collect finite_rank)\<close> for x :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  proof (rule limitin_closure_of)
    define f :: \<open>'a \<Rightarrow> 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> where \<open>f = (\<lambda>i. butterfly (x *\<^sub>V ket i) (ket i))\<close>
    have \<open>has_sum_in weak_star_topology f UNIV x\<close>
      using f_def has_sum_butterfly_ket_a by blast
    then show \<open>limitin weak_star_topology (sum f) x (finite_subsets_at_top UNIV)\<close>
      using has_sum_in_def by blast
    show \<open>\<forall>\<^sub>F F in finite_subsets_at_top UNIV.
       (\<Sum>i\<in>F. butterfly (x *\<^sub>V ket i) (ket i)) \<in> Collect finite_rank\<close>
      by (auto intro!: finite_rank_sum simp: f_def)
    show \<open>finite_subsets_at_top UNIV \<noteq> \<bottom>\<close>
      by simp
  qed
  then show ?thesis
    by auto
qed


lemma butterkets_weak_star_dense[simp]:
  \<open>weak_star_topology closure_of cspan ((\<lambda>(\<xi>,\<eta>). butterfly (ket \<xi>) (ket \<eta>)) ` UNIV) = UNIV\<close>
  (* Stronger form proven in comment below, but would need strengthening of finite_rank_weak_star_dense first *)
proof -
  from continuous_map_image_closure_subset[OF weak_star_topology_weaker_than_euclidean]
  have \<open>weak_star_topology closure_of (cspan ((\<lambda>(\<xi>,\<eta>). butterfly (ket \<xi>) (ket \<eta>)) ` UNIV))
          \<supseteq> closure (cspan ((\<lambda>(\<xi>,\<eta>). butterfly (ket \<xi>) (ket \<eta>)) ` UNIV))\<close> (is \<open>_ \<supseteq> \<dots>\<close>)
    by auto
  moreover 
  have \<open>\<dots> = Collect compact_op\<close>
    unfolding finite_rank_dense_compact[OF is_onb_ket is_onb_ket, symmetric]
    by (simp add: image_image case_prod_beta flip: map_prod_image)
  moreover have \<open>\<dots> \<supseteq> Collect finite_rank\<close>
    by (metis closure_subset compact_op_finite_rank mem_Collect_eq subsetI subset_antisym)
  ultimately have *: \<open>weak_star_topology closure_of (cspan ((\<lambda>(\<xi>,\<eta>). butterfly (ket \<xi>) (ket \<eta>)) ` UNIV)) \<supseteq> Collect finite_rank\<close>
    by blast
  have \<open>weak_star_topology closure_of cspan ((\<lambda>(\<xi>,\<eta>). butterfly (ket \<xi>) (ket \<eta>)) ` UNIV)
        = weak_star_topology closure_of (weak_star_topology closure_of cspan ((\<lambda>(\<xi>,\<eta>). butterfly (ket \<xi>) (ket \<eta>)) ` UNIV))\<close>
    by simp
  also have \<open>\<dots> \<supseteq> weak_star_topology closure_of Collect finite_rank\<close> (is \<open>_ \<supseteq> \<dots>\<close>)
    using * closure_of_mono by blast
  also have \<open>\<dots> = UNIV\<close>
    by simp
  finally show ?thesis
    by auto
qed
(* 
lemma butterkets_weak_star_dense[simp]:
  assumes \<open>is_onb A\<close> and \<open>is_onb B\<close>
  shows \<open>weak_star_topology closure_of cspan (cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B))) = UNIV\<close>
proof -
  from continuous_map_image_closure_subset[OF weak_star_topology_weaker_than_euclidean]
  have \<open>weak_star_topology closure_of (cspan (cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B)))) 
            \<supseteq> closure (cspan (cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B))))\<close> (is \<open>_ \<supseteq> \<dots>\<close>)
    by auto
  moreover from finite_rank_dense_compact[OF assms]
  have \<open>\<dots> \<supseteq> Collect finite_rank\<close>
    by (metis closure_subset compact_op_def complex_vector.span_span mem_Collect_eq subsetD subsetI)
  ultimately have *: \<open>weak_star_topology closure_of (cspan (cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B)))) \<supseteq> Collect finite_rank\<close>
    by simp
  have \<open>weak_star_topology closure_of cspan (cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B)))
        = weak_star_topology closure_of (weak_star_topology closure_of cspan (cspan ((\<lambda>(\<xi>,\<eta>). butterfly \<xi> \<eta>) ` (A \<times> B))))\<close>
    by simp
  also have \<open>\<dots> \<supseteq> weak_star_topology closure_of Collect finite_rank\<close> (is \<open>_ \<supseteq> \<dots>\<close>)
    using * closure_of_mono by blast
  also have \<open>\<dots> = UNIV\<close>
    thm finite_rank_weak_star_dense
    by simp
  finally show ?thesis
    by auto
qed
 *)


lemma weak_star_clinear_eq_butterfly_ketI:
  fixes F G :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow> 'c::complex_vector\<close>
  assumes "clinear F" and "clinear G"
    and \<open>continuous_map weak_star_topology T F\<close> and \<open>continuous_map weak_star_topology T G\<close>
    and \<open>Hausdorff_space T\<close>
  assumes "\<And>i j. F (butterfly (ket i) (ket j)) = G (butterfly (ket i) (ket j))"
  shows "F = G"
proof -
  have FG: \<open>F x = G x\<close> if \<open>x \<in> cspan ((\<lambda>(\<xi>,\<eta>). butterfly (ket \<xi>) (ket \<eta>)) ` UNIV)\<close> for x
    by (smt (verit) assms(1) assms(2) assms(6) complex_vector.linear_eq_on imageE split_def that)
  show ?thesis
    apply (rule ext)
    using \<open>Hausdorff_space T\<close> FG
    apply (rule closure_of_eqI[where f=F and g=G and S=\<open>cspan ((\<lambda>(\<xi>,\<eta>). butterfly (ket \<xi>) (ket \<eta>)) ` UNIV)\<close>])
    using assms butterkets_weak_star_dense by auto
qed

lemma continuous_map_scaleC_weak_star'[continuous_intros]:
  assumes \<open>continuous_map T weak_star_topology f\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. scaleC c (f x))\<close>
  using continuous_map_compose[OF assms continuous_map_scaleC_weak_star]
  by (simp add: o_def)

lemma continuous_map_uminus_weak_star[continuous_intros]:
  assumes \<open>continuous_map T weak_star_topology f\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. - f x)\<close>
  apply (subst scaleC_minus1_left[abs_def,symmetric])
  by (intro continuous_map_scaleC_weak_star' assms)

lemma continuous_map_add_weak_star[continuous_intros]: 
  assumes \<open>continuous_map T weak_star_topology f\<close>
  assumes \<open>continuous_map T weak_star_topology g\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. f x + g x)\<close>
proof -
  have \<open>continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L f x))\<close> if \<open>trace_class t\<close> for t
    using assms(1) continuous_on_weak_star_topo_iff_coordinatewise that by auto
  moreover have \<open>continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L g x))\<close> if \<open>trace_class t\<close> for t
    using assms(2) continuous_on_weak_star_topo_iff_coordinatewise that by auto
  ultimately show ?thesis
    by (auto intro!: continuous_map_add simp add: continuous_on_weak_star_topo_iff_coordinatewise
        cblinfun_compose_add_right trace_class_comp_left trace_plus)
qed

lemma continuous_map_minus_weak_star[continuous_intros]: 
  assumes \<open>continuous_map T weak_star_topology f\<close>
  assumes \<open>continuous_map T weak_star_topology g\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. f x - g x)\<close>
  by (subst diff_conv_add_uminus) (intro assms continuous_intros)

lemma weak_star_topology_is_norm_topology_fin_dim[simp]: 
  \<open>(weak_star_topology :: ('a::{cfinite_dim,chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'b::{cfinite_dim,chilbert_space}) topology) = euclidean\<close>
proof -
  have 1: \<open>continuous_map euclidean weak_star_topology (id :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> _)\<close>
    by (simp add: id_def weak_star_topology_weaker_than_euclidean)
  have \<open>continuous_map weak_star_topology cweak_operator_topology (id :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> _)\<close>
    by (simp only: id_def wot_weaker_than_weak_star)
  then have 2: \<open>continuous_map weak_star_topology euclidean (id :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> _)\<close>
    by (simp only: wot_is_norm_topology_findim)
  from 1 2
  show ?thesis
    by (auto simp: topology_finer_continuous_id[symmetric] simp flip: openin_inject)
qed



lemma infsum_mono_wot:
  fixes f :: "'a \<Rightarrow> ('b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  assumes "summable_on_in cweak_operator_topology f A" and "summable_on_in cweak_operator_topology g A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "infsum_in cweak_operator_topology f A \<le> infsum_in cweak_operator_topology g A"
  by (meson assms has_sum_in_infsum_in has_sum_mono_wot hausdorff_cweak_operator_topology)



unbundle no_cblinfun_notation

end
