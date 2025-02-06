(*  Title:   Lemmas_Coproduct_Measure.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section \<open> Preliminaries \<close>
theory Lemmas_Coproduct_Measure
  imports "HOL-Probability.Probability"
          "Standard_Borel_Spaces.Abstract_Metrizable_Topology"
begin

subsection \<open>Metrics and Metrizability\<close>
(* TODO: Move the following to Standard_Borel_Spaces.Abstract_Metrizable_Topology *)
lemma metrizable_space_metric_space:
  assumes d:"Metric_space UNIV d" "Metric_space.mtopology UNIV d = euclidean"
  shows "class.metric_space d (\<Sqinter>e\<in>{0<..}. principal {(x,y). d x y < e}) open"
proof -
  interpret Metric_space UNIV d by fact
  show ?thesis
  proof
    show "open U \<longleftrightarrow> (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in \<Sqinter>e\<in>{0<..}. principal {(F, y). d F y < e}.  x' = x \<longrightarrow> y \<in> U)" for U
    proof(subst eventually_INF_base)
      show "a \<in> {0<..} \<Longrightarrow> b \<in> {0<..} \<Longrightarrow> \<exists>x\<in>{0<..}. principal {(F, y). d F y < x} \<le> principal {(F, y). d F y < a} \<sqinter> principal {(F, y). d F y < b}" for a b
        by(auto intro!: bexI[where x="min a b"])
    next
      show "open U \<longleftrightarrow> (\<forall>x\<in>U. \<exists>b\<in>{0<..}. \<forall>\<^sub>F (x', y) in principal {(F, y). d F y < b}. x' = x \<longrightarrow> y \<in> U)"
        by(fastforce simp: openin_mtopology[simplified d(2),simplified] eventually_principal)
    qed simp
  qed(auto simp: triangle')
qed

corollary metrizable_space_metric_space_ex:
  assumes "metrizable_space (euclidean :: 'a :: topological_space topology)"
  shows "\<exists>(d :: 'a \<Rightarrow> 'a \<Rightarrow> real) F. class.metric_space d F open"
proof -
  from assms obtain d :: "'a \<Rightarrow> 'a \<Rightarrow> real" where "Metric_space UNIV d" "Metric_space.mtopology UNIV d = euclidean"
    by (metis Metric_space.topspace_mtopology metrizable_space_def topspace_euclidean)
  from metrizable_space_metric_space[OF this] show ?thesis
    by blast
qed

lemma completely_metrizable_space_metric_space:
  assumes "Metric_space (UNIV :: 'a ::topological_space set) d" "Metric_space.mtopology UNIV d = euclidean" "Metric_space.mcomplete UNIV d"
  shows "class.complete_space d (\<Sqinter>e\<in>{0<..}. principal {(x,y). d x y < e}) open"
proof -
  interpret Metric_space UNIV d by fact
  interpret m:metric_space d "\<Sqinter>e\<in>{0<..}. principal {(x,y). d x y < e}" "open"
    by(auto intro!: metrizable_space_metric_space assms)
  (* Why do we need the following? *)
  have [simp]:"topological_space.convergent (open :: 'a set \<Rightarrow> bool) = convergent"
  proof
    fix x :: "nat \<Rightarrow> 'a"
    have *:"class.topological_space (open :: 'a set \<Rightarrow> bool)"
      by standard auto
    show "topological_space.convergent open x = convergent x"
      by(simp add: topological_space.convergent_def[OF *] topological_space.nhds_def[OF *] convergent_def nhds_def)
  qed
  show ?thesis
    apply unfold_locales
    using assms(3) by(auto simp: mcomplete_def assms(2) MCauchy_def m.Cauchy_def convergent_def)
qed

lemma completely_metrizable_space_metric_space_ex:
  assumes "completely_metrizable_space (euclidean :: 'a :: topological_space topology)"
  shows "\<exists>(d :: 'a \<Rightarrow> 'a \<Rightarrow> real) F. class.complete_space d F open"
proof -
  from assms obtain d :: "'a \<Rightarrow> 'a \<Rightarrow> real" where "Metric_space UNIV d" "Metric_space.mtopology UNIV d = euclidean" "Metric_space.mcomplete UNIV d"
    by (metis Metric_space.topspace_mtopology completely_metrizable_space_def topspace_euclidean)
  from completely_metrizable_space_metric_space[OF this] show ?thesis
    by blast
qed

subsection \<open> Copy of Extended non-negative reals\<close>
text \<open> In the proof of the change of ordering of the infinite sum (@{term infsum}) for @{typ ennreal},
we use \texttt{infsum\_Sigma} and \texttt{compact\_uniformly\_continuous}. Thus, we need to interpret
@{typ ennreal} as a metric space. However, there is no standard metric on @{typ ennreal} even though
it is a Polish space (thus, a metrizable space). Hence, we do not want to give a metric on @{typ ennreal}
globally. Instead of defining a metric on @{typ ennreal}, we define a type copy of @{typ ennreal},
then define a metric on the copy and prove the change of ordering of the infinite sum.
Finally, we transfer the theorems to the ones for @{typ ennreal}.\<close>
typedef ennreal' = "UNIV :: ennreal set"
  by simp

lemma bij_Abs_ennreal': "bij Abs_ennreal'"
  by (metis Abs_ennreal'_cases Abs_ennreal'_inject UNIV_I bij_iff)

lemma inj_Abs_ennreal': "inj Abs_ennreal'"
  by (simp add: Abs_ennreal'_inject inj_on_def)

setup_lifting type_definition_ennreal'

instantiation ennreal' :: complete_linorder
begin

lift_definition top_ennreal' :: ennreal' is top .
lift_definition bot_ennreal' :: ennreal' is 0 .
lift_definition sup_ennreal' :: "ennreal' \<Rightarrow> ennreal' \<Rightarrow> ennreal'" is sup .
lift_definition inf_ennreal' :: "ennreal' \<Rightarrow> ennreal' \<Rightarrow> ennreal'" is inf .
lift_definition Inf_ennreal' :: "ennreal' set \<Rightarrow> ennreal'" is "Inf" .
lift_definition Sup_ennreal' :: "ennreal' set \<Rightarrow> ennreal'" is "sup 0 \<circ> Sup" .

lift_definition less_eq_ennreal' :: "ennreal' \<Rightarrow> ennreal' \<Rightarrow> bool" is "(\<le>)" .
lift_definition less_ennreal' :: "ennreal' \<Rightarrow> ennreal' \<Rightarrow> bool" is "(<)" .

instance
  by standard
     (transfer, auto simp: Inf_lower Inf_greatest Sup_upper sup.coboundedI2 Sup_least)+

end

instantiation ennreal' :: infinity
begin

definition infinity_ennreal' :: ennreal'
where
  [simp]: "\<infinity> = (top::ennreal')"

instance ..

end

instantiation ennreal' :: "{semiring_1_no_zero_divisors, comm_semiring_1}"
begin

lift_definition one_ennreal' :: ennreal' is 1 .
lift_definition zero_ennreal' :: ennreal' is 0 .
lift_definition plus_ennreal' :: "ennreal' \<Rightarrow> ennreal' \<Rightarrow> ennreal'" is "(+)" .
lift_definition times_ennreal' :: "ennreal' \<Rightarrow> ennreal' \<Rightarrow> ennreal'" is "(*)" .

instance
  by standard (transfer; auto simp: field_simps)+

end

instantiation ennreal' :: minus
begin

lift_definition minus_ennreal' :: "ennreal' \<Rightarrow> ennreal' \<Rightarrow> ennreal'" is minus .

instance ..

end

instance ennreal' :: numeral ..

instance ennreal' :: ordered_comm_monoid_add
  by (standard, transfer) (use ennreal_add_left_cancel_le in auto)

lemma ennreal'_nonneg[simp]: "\<And>r :: ennreal'. 0 \<le> r"
  by transfer simp

lemma sum_Rep_ennreal'[simp]: "(\<Sum>i\<in>I. Rep_ennreal' (f i)) = Rep_ennreal' (sum f I)"
  by (induction I rule: infinite_finite_induct) (auto simp: sum_nonneg zero_ennreal'.rep_eq plus_ennreal'.rep_eq)

lemma transfer_sum_ennreal' [transfer_rule]:
  "rel_fun (rel_fun (=) pcr_ennreal') (rel_fun (=) pcr_ennreal') sum sum"
  using rel_funD by(fastforce simp:  comp_def ennreal'.pcr_cr_eq cr_ennreal'_def)

lemma pcr_ennreal'_eq:"pcr_ennreal' a b \<longleftrightarrow> b = Abs_ennreal' a"
  by (metis Abs_ennreal'_inverse Rep_ennreal'_inverse UNIV_I cr_ennreal'_def ennreal'.pcr_cr_eq)

lemma rel_set_pcr_ennreal'_eq:"rel_set pcr_ennreal' A B \<longleftrightarrow> B = Abs_ennreal' ` A"
  by(auto simp: rel_set_def pcr_ennreal'_eq)

lemma transfer_lessThan_ennreal'[transfer_rule]:
 "rel_fun pcr_ennreal' (rel_set pcr_ennreal') lessThan lessThan"
proof -
  have [simp]: "\<And>x xa. xa < Abs_ennreal' x \<Longrightarrow> xa \<in> Abs_ennreal' ` {..<x} "
    by (metis Abs_ennreal'_cases imageI lessThan_iff less_ennreal'.abs_eq)
  show ?thesis
    by(fastforce simp: rel_set_pcr_ennreal'_eq pcr_ennreal'_eq  less_ennreal'.abs_eq)
qed

lemma transfer_greaterThan_ennreal'[transfer_rule]:
 "rel_fun pcr_ennreal' (rel_set pcr_ennreal') greaterThan greaterThan"
proof -
  have [simp]: "\<And>x xa. Abs_ennreal' x < xa \<Longrightarrow> xa \<in> Abs_ennreal' ` {x<..}"
    by (metis Abs_ennreal'_cases greaterThan_iff image_eqI less_ennreal'.abs_eq)
  show ?thesis
    by(fastforce simp: rel_set_pcr_ennreal'_eq pcr_ennreal'_eq  less_ennreal'.abs_eq)
qed

text \<open> The transfer rule for @{term generate_topology}. \<close>
lemma homeomorphism_generating_topology_imp:
  assumes bj:"bij f"
    and "generate_topology S a"
  shows "generate_topology ((`) f ` S) (f ` a)"
proof -
  have [simp]:"f ` UNIV = UNIV"
    by (simp add: assms(1) bij_betw_imp_surj_on)
  have [simp]:"f ` (a \<inter> b) = f ` a \<inter> f ` b" for a b
    by(intro image_Int bij_betw_imp_inj_on[OF bj])
  have [simp]: "(f ` \<Union> K) = (\<Union> ((`) f ` K))" for K
    by blast 
  show ?thesis
    using assms(2)
  proof(induct rule: generate_topology.induct)
    case (Basis s)
    then show ?case
      by(auto intro!: generate_topology.Basis)
  qed (auto intro!: generate_topology.Int generate_topology.UNIV generate_topology.UN)
qed  

corollary homeomorphism_generating_topology_eq:
  assumes bjf: "bij f"
  shows "generate_topology S a = generate_topology ((`) f ` S) (f ` a)"
proof -
  define g where "g \<equiv> the_inv f"
  have bjg: "bij g"
    using assms bij_betw_the_inv_into g_def by blast
  have gf: "g (f x) = x" for x
    by (metis assms bij_betw_imp_inj_on g_def the_inv_f_f)
  show ?thesis
  proof
    assume "generate_topology ((`) f ` S) (f ` a) "
    then have "generate_topology ((`) g ` ((`) f ` S)) (g ` f ` a)"
      by(auto intro!: homeomorphism_generating_topology_imp[OF bjg])
    moreover have "((`) g ` ((`) f ` S)) = S" "g ` f ` a = a"
      using gf by(auto simp: image_comp)
    ultimately show "generate_topology S a"
      by argo
  qed(auto intro!: bjf homeomorphism_generating_topology_imp)
qed

lemma transfer_generate_topology_ennreal'[transfer_rule]:
 "rel_fun (rel_set (rel_set pcr_ennreal')) (rel_fun (rel_set pcr_ennreal') (=)) generate_topology generate_topology"
proof(intro rel_funI)
  fix S S' a b
  assume h:"rel_set (rel_set pcr_ennreal') S S'" "rel_set pcr_ennreal' a b"
  then have [simp]:"S' = (`) Abs_ennreal' ` S"
    by(auto simp: rel_set_def[of "rel_set pcr_ennreal'"] rel_set_pcr_ennreal'_eq)
  show "generate_topology S a =  generate_topology S' b"
    using h(2) by(auto simp: rel_set_pcr_ennreal'_eq homeomorphism_generating_topology_eq[OF bij_Abs_ennreal'])
qed

instantiation ennreal' :: topological_space
begin

lift_definition open_ennreal' :: "ennreal' set \<Rightarrow> bool" is "open" .

instance
  by standard (transfer, auto)+

end

instance ennreal' :: second_countable_topology
proof
  obtain B :: "ennreal set set" where B:
    "countable B" "open = generate_topology B"
    using ex_countable_subbasis by blast
  have "open = generate_topology ((`) Abs_ennreal' ` B)"
    using B(2) by transfer auto
  with B(1) show "\<exists>B':: ennreal' set set. countable B' \<and> open = generate_topology B'"
    by(auto intro!: exI[where x="(\<lambda>b. Abs_ennreal' ` b) ` B"])
qed

instance ennreal' :: linorder_topology
  by (standard, transfer) (use open_ennreal_def in auto)

lemma continuous_map_Abs_ennreal':"continuous_on UNIV Abs_ennreal'"
  by (metis continuous_on_open_vimage image_vimage_eq open_Int open_UNIV open_ennreal'.abs_eq)

lemma continuous_map_Rep_ennreal':"continuous_on UNIV Rep_ennreal'"
  by (metis continuous_on_open_vimage image_vimage_eq open_Int open_UNIV open_ennreal'.rep_eq)

corollary continuous_map_ennreal'_eq: "continuous_on A f \<longleftrightarrow> continuous_on A (\<lambda>x. Rep_ennreal' (f x))"
proof
  have "(\<lambda>x. Abs_ennreal' (Rep_ennreal' (f x))) = f"
    by (simp add: Rep_ennreal'_inverse)
  thus "continuous_on A f" if h:"continuous_on A (\<lambda>x. Rep_ennreal' (f x))"
    using continuous_on_compose[OF h continuous_on_subset[OF continuous_map_Abs_ennreal']]
    by(simp add: comp_def)
qed(simp add: continuous_on_compose[OF _ continuous_on_subset[OF continuous_map_Rep_ennreal'],simplified comp_def])

lemma ennreal_ennreal'_homeomorphic:
  "(euclidean :: ennreal topology) homeomorphic_space (euclidean :: ennreal' topology)"
  by(auto simp: homeomorphic_space_def homeomorphic_maps_def continuous_map_Abs_ennreal'
                continuous_map_Rep_ennreal' Abs_ennreal'_inverse Rep_ennreal'_inverse
        intro!: exI[where x=Rep_ennreal'] exI[where x=Abs_ennreal'])

corollary Polish_space_ennreal': "Polish_space (euclidean :: ennreal' topology)"
  using Polish_space_ennreal ennreal_ennreal'_homeomorphic homeomorphic_Polish_space_aux by blast

instantiation ennreal' :: metric_space
begin

definition dist_ennreal' :: "ennreal' \<Rightarrow> ennreal' \<Rightarrow> real"
  where "dist_ennreal' \<equiv> SOME d. Metric_space UNIV d \<and>
                                 Metric_space.mtopology UNIV d = euclidean \<and>
                                 Metric_space.mcomplete UNIV d"

definition uniformity_ennreal' :: "(ennreal' \<times> ennreal') filter"
  where "uniformity_ennreal' \<equiv> \<Sqinter>e\<in>{0<..}. principal {(x,y). dist x y < e}"

instance
proof -
  let ?open = "open :: ennreal' set \<Rightarrow> bool"
  interpret c:complete_space dist uniformity ?open
  proof -
    have "\<exists>d. Metric_space (UNIV :: ennreal' set) d \<and>
              Metric_space.mtopology UNIV d = euclidean \<and>
              Metric_space.mcomplete UNIV d"
      by (metis Polish_space_ennreal' Metric_space.topspace_mtopology Polish_space_def completely_metrizable_space_def topspace_euclidean)
    hence "Metric_space (UNIV :: ennreal' set) dist \<and>
           Metric_space.mtopology (UNIV :: ennreal' set) dist = euclidean \<and>
           Metric_space.mcomplete (UNIV :: ennreal' set) dist"
      unfolding dist_ennreal'_def by(rule someI_ex)
    with completely_metrizable_space_metric_space show "class.complete_space dist uniformity ?open"
      by(fastforce simp: uniformity_ennreal'_def)
  qed
  have [simp]:"topological_space.convergent ?open = convergent"
  proof
    fix x :: "nat \<Rightarrow> ennreal'"
    have *:"class.topological_space ?open"
      by standard auto
    show "topological_space.convergent open x = convergent x"
      by(simp add: topological_space.convergent_def[OF *] topological_space.nhds_def[OF *] convergent_def nhds_def)
  qed
  show "OFCLASS(ennreal', metric_space_class)"
    by standard (use uniformity_ennreal'_def c.open_uniformity c.dist_triangle2 c.Cauchy_convergent in auto)
qed

end

subsection \<open> Lemmas for Infinite Sum \<close>
lemma transfer_nhds_ennreal'[transfer_rule]: "rel_fun pcr_ennreal' (rel_filter pcr_ennreal') nhds nhds"
proof(rule rel_funI)
  fix x x'
  assume h:"pcr_ennreal' x x'"
  then have b:"nhds (x, x') \<sqinter> principal {(y, y'). pcr_ennreal' y y'} \<noteq> \<bottom>" (is "?F \<noteq> _")
    by(auto simp: eventually_False[symmetric] eventually_inf_principal dest: eventually_nhds_x_imp_x)
  have ev_eq1:"(\<forall>\<^sub>F xx' in nhds (x, x'). pcr_ennreal' (fst xx') (snd xx') \<longrightarrow> P (fst xx'))
                \<longleftrightarrow> eventually P (nhds x)" for P
  proof
    assume "\<forall>\<^sub>F xx' in nhds (x, x'). pcr_ennreal' (fst xx') (snd xx') \<longrightarrow> P (fst xx')"
    then obtain S where
      S:"open S" "(x, x') \<in> S" "\<And>xx'. xx' \<in> S \<Longrightarrow> pcr_ennreal' (fst xx') (snd xx') \<Longrightarrow> P (fst xx')"
      unfolding eventually_nhds by blast
    then obtain A B where AB: "open A" "open (Abs_ennreal' ` B)" "(x,x') \<in> A \<times> Abs_ennreal' ` B" "A \<times> Abs_ennreal' ` B \<subseteq> S"
      by (metis ennreal'.type_definition_ennreal' open_prod_elim surj_image_vimage_eq type_definition.univ)
    have AB1:"open (A \<inter> B)" "x \<in> A \<inter> B"
      using AB h by(auto simp: open_ennreal'.abs_eq pcr_ennreal'_eq dest: injD[OF inj_Abs_ennreal'])
    have AB2: "(y, Abs_ennreal' y) \<in> S" "pcr_ennreal' (fst (y, Abs_ennreal' y)) (snd (y, Abs_ennreal' y))"
      if y:"y \<in> A" "y \<in> B" for y
      using AB y by(auto simp: pcr_ennreal'_eq)
    show "eventually P (nhds x)"
      using S(3)[OF AB2] AB1 by(auto intro!: exI[where x="A \<inter> B"] simp: eventually_nhds)
  next
    assume "eventually P (nhds x)"
    then obtain S where "open S" "x \<in> S" "\<And>y. y \<in> S \<Longrightarrow> P y"
      by(auto simp: eventually_nhds)
    thus "\<forall>\<^sub>F xx' in nhds (x, x'). pcr_ennreal' (fst xx') (snd xx') \<longrightarrow> P (fst xx')"
      unfolding eventually_nhds by(auto intro!: exI[where x="S \<times> UNIV"] simp: open_Times)
  qed
  have ev_eq2:"(\<forall>\<^sub>F xx' in nhds (x, x'). pcr_ennreal' (fst xx') (snd xx') \<longrightarrow> P (snd xx'))
                \<longleftrightarrow> eventually P (nhds x')" for P
  proof
    assume "\<forall>\<^sub>F xx' in nhds (x, x'). pcr_ennreal' (fst xx') (snd xx') \<longrightarrow> P (snd xx')"
    then obtain S where
      S:"open S" "(x, x') \<in> S" "\<And>xx'. xx' \<in> S \<Longrightarrow> pcr_ennreal' (fst xx') (snd xx') \<Longrightarrow> P (snd xx')"
      unfolding eventually_nhds by blast
    then obtain A B where AB: "open A" "open (Abs_ennreal' ` B)" "(x,x') \<in> A \<times> Abs_ennreal' ` B" "A \<times> Abs_ennreal' ` B \<subseteq> S"
      by (metis ennreal'.type_definition_ennreal' open_prod_elim surj_image_vimage_eq type_definition.univ)
    have AB1:"open (A \<inter> B)" "x \<in> A \<inter> B"
      using AB h by(auto simp: open_ennreal'.abs_eq pcr_ennreal'_eq dest: injD[OF inj_Abs_ennreal'])
    have AB2: "(y, Abs_ennreal' y) \<in> S" "pcr_ennreal' (fst (y, Abs_ennreal' y)) (snd (y, Abs_ennreal' y))"
      if y:"y \<in> A" "y \<in> B" for y
      using AB y by(auto simp: pcr_ennreal'_eq)
    show "eventually P (nhds x')"
      using S(3)[OF AB2] AB1 h
      by(auto intro!: exI[where x="Abs_ennreal' ` (A \<inter> B)"] simp: eventually_nhds pcr_ennreal'_eq open_ennreal'.abs_eq)
  next
    assume "eventually P (nhds x')"
    then obtain S where "open S" "x' \<in> S" "\<And>y. y \<in> S \<Longrightarrow> P y"
      by(auto simp: eventually_nhds)
    thus "\<forall>\<^sub>F xx' in nhds (x, x'). pcr_ennreal' (fst xx') (snd xx') \<longrightarrow> P (snd xx')"
      unfolding eventually_nhds by(auto intro!: exI[where x="UNIV \<times> S"] simp: open_Times)
  qed
  show "rel_filter pcr_ennreal' (nhds x) (nhds x')"
  proof(rule rel_filter.intros)
    show "\<forall>\<^sub>F (x, y) in nhds (x, x') \<sqinter> principal {(y, y'). pcr_ennreal' y y'}. pcr_ennreal' x y"
      unfolding eventually_inf_principal using h by(auto intro!: eventuallyI simp: pcr_ennreal'_eq)
  qed (auto intro!: filter_eqI simp: eventually_inf_principal eventually_map_filter_on  split_beta' ev_eq1 ev_eq2)
qed

lemmas transfer_filtermap_ennreal'[transfer_rule] = filtermap_parametric[where A=HOL.eq and B=pcr_ennreal']

lemma transfer_filterlim_ennreal'[transfer_rule]:
 "rel_fun (rel_fun (=) pcr_ennreal') (rel_fun (rel_filter pcr_ennreal') (rel_fun (rel_filter (=)) (=))) filterlim filterlim"
  unfolding filterlim_def by transfer_prover

lemma transfer_The_ennreal:
  assumes P:"\<exists>!x. P x"
    and "rel_fun pcr_ennreal' (=) P P'"
  shows "The P' = Abs_ennreal' (The P)" 
proof -
  have P':"\<exists>!x'. P' x'"
    by (metis Rep_ennreal'_inverse pcr_ennreal'_eq rel_funD[OF assms(2)] P)
  show ?thesis
  proof(rule the1I2)
    fix x
    assume h:"P x"
    show "(THE a. P' a) = Abs_ennreal' x"
      by(rule the1I2[OF P']) (metis (full_types) h P' assms(2) ennreal'.id_abs_transfer rel_funD)
  qed fact
qed

lemma transfer_infsum_ennreal'[transfer_rule]:
 "rel_fun (rel_fun (=) pcr_ennreal') (rel_fun (=) pcr_ennreal') infsum (infsum :: ('a \<Rightarrow> _) \<Rightarrow> _ \<Rightarrow> _)"
proof -
  have *:"rel_fun pcr_ennreal' (=) (\<lambda>l. (sum x \<longlongrightarrow> l) (finite_subsets_at_top A))
                                   (\<lambda>l. (sum y \<longlongrightarrow> l) (finite_subsets_at_top A))"
    if [transfer_rule]: "rel_fun (=) pcr_ennreal' x y" for x :: "'a \<Rightarrow> ennreal" and y and A
    by transfer_prover
  show ?thesis
    apply(simp add: nonneg_summable_on_complete infsum_def[abs_def])
    apply(intro rel_funI)
    apply(simp add: pcr_ennreal'_eq Topological_Spaces.Lim_def)
    apply(intro transfer_The_ennreal)
     apply (meson has_sum_def has_sum_unique nonneg_has_sum_complete zero_le)
    using * by auto
qed

lemma inf_sum_Rep_Abs_ennreal':"infsum f A = Rep_ennreal' (infsum ((\<lambda>x. Abs_ennreal' (f x))) A)"
  by transfer (simp add: comp_def)

lemma continuous_on_add_ennreal':
  fixes f g :: "'a::topological_space \<Rightarrow> ennreal'"
  shows "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> continuous_on A (\<lambda>x. f x + g x)"
  unfolding continuous_map_ennreal'_eq plus_ennreal'.rep_eq
  by(rule continuous_on_add_ennreal)

lemma uniformly_continuous_add_ennreal': "isUCont (\<lambda>(x::ennreal', y). x + y)"
proof(safe intro!: compact_uniformly_continuous)
  have "compact (UNIV \<times> UNIV :: (ennreal' \<times> ennreal') set)"
    by(intro compact_Times compact_UNIV)
  thus "compact (UNIV :: (ennreal' \<times> ennreal') set)"
    by simp
qed(auto intro!: continuous_on_add_ennreal' continuous_on_fst continuous_on_snd simp: split_beta')

lemma infsum_eq_suminf:
  assumes "f summable_on UNIV"
  shows "(\<Sum>\<^sub>\<infinity> n\<in>UNIV. f n) = suminf f"
  using has_sum_imp_sums[OF has_sum_infsum[OF assms]]
  by (simp add: sums_iff)

lemma infsum_Sigma_ennreal':
  fixes f :: "_ \<Rightarrow> ennreal'"
  shows "infsum f (Sigma A B) = infsum (\<lambda>x. infsum (\<lambda>y. f (x, y)) (B x)) A"
  by(auto intro!: uniformly_continuous_add_ennreal' infsum_Sigma nonneg_summable_on_complete)

lemma infsum_swap_ennreal':
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> ennreal'"
  shows "infsum (\<lambda>x. infsum (\<lambda>y. f x y) B) A = infsum (\<lambda>y. infsum (\<lambda>x. f x y) A) B"
  by(auto intro!: infsum_swap uniformly_continuous_add_ennreal' nonneg_summable_on_complete)

lemma infsum_Sigma_ennreal:
  fixes f :: "_ \<Rightarrow> ennreal"
  shows "infsum f (Sigma A B) = infsum (\<lambda>x. infsum (\<lambda>y. f (x, y)) (B x)) A"
  by (simp add: inf_sum_Rep_Abs_ennreal' infsum_Sigma_ennreal' Rep_ennreal'_inverse)

lemma infsum_swap_ennreal:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> ennreal"
  shows "infsum (\<lambda>x. infsum (\<lambda>y. f x y) B) A = infsum (\<lambda>y. infsum (\<lambda>x. f x y) A) B"
  by (simp add: inf_sum_Rep_Abs_ennreal' Rep_ennreal'_inverse infsum_swap_ennreal'[where A=A])

lemma has_sum_cmult_right_ennreal:
  fixes f :: "_ \<Rightarrow> ennreal"
  assumes "c < \<top>"  "(f has_sum a) A"
  shows "((\<lambda>x. c * f x) has_sum c * a) A"
  using ennreal_tendsto_cmult[OF assms(1)] assms(2)
  by (force simp add: has_sum_def sum_distrib_left)

lemma infsum_cmult_right_ennreal:
  fixes f :: "_ \<Rightarrow> ennreal"
  assumes "c < \<top>"
  shows "(\<Sum>\<^sub>\<infinity>x\<in>A. c * f x) = c * infsum f A"
  by (simp add: assms has_sum_cmult_right_ennreal infsumI nonneg_summable_on_complete)

lemma ennreal_sum_SUP_eq:
  fixes f :: "nat \<Rightarrow> _ \<Rightarrow> ennreal"
  assumes "finite A" "\<And>x. x \<in> A \<Longrightarrow> incseq (\<lambda>j. f j x)"
  shows "(\<Sum>i\<in>A. \<Squnion>n. f n i) = (\<Squnion>n. \<Sum>i\<in>A. f n i)"
  using assms
proof induction
  case empty
  then show ?case
    by simp
next
  case ih:(insert x F)
  show ?case (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<Squnion>n. f n x) + (\<Squnion>n. sum (f n) F)"
      using ih by simp
    also have "... = (\<Squnion>n. f n x + sum (f n) F)"
      using ih by(auto intro!: incseq_sumI2 ennreal_SUP_add[symmetric])
    also have "... = ?rhs"
      using ih by simp
    finally show ?thesis .
  qed
qed 

lemma ennreal_infsum_Sup_eq:
  fixes f :: "nat \<Rightarrow> _ \<Rightarrow> ennreal"
  assumes "\<And>x. x \<in> A \<Longrightarrow> incseq (\<lambda>j. f j x)"
  shows "(\<Sum>\<^sub>\<infinity>x\<in>A. (SUP j. f j x)) = (SUP j. (\<Sum>\<^sub>\<infinity>x\<in>A. f j x))" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Squnion> (sum (\<lambda>x. \<Squnion>j. f j x) ` {F. finite F \<and> F \<subseteq> A}))"
    by(auto intro!: nonneg_infsum_complete simp: SUP_upper2 assms)
  also have "... = (\<Squnion>A\<in>{F. finite F \<and> F \<subseteq> A}. \<Squnion>j. sum (f j) A)"
    using assms by(auto intro!: SUP_cong ennreal_sum_SUP_eq)
  also have "... = (\<Squnion>j. \<Squnion>A\<in>{F. finite F \<and> F \<subseteq> A}. sum (f j) A)"
    using SUP_commute by fast
  also have "... = ?rhs"
    by(subst nonneg_infsum_complete) (use assms in auto)
  finally show ?thesis .
qed

lemma bounded_infsum_summable:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0" "(\<Sum>\<^sub>\<infinity>x\<in>A. ennreal (f x)) < top"
  shows "f summable_on A"
proof(rule nonneg_bdd_above_summable_on)
  from assms(2) obtain K where K:"(\<Sum>\<^sub>\<infinity>x\<in>A. ennreal (f x)) \<le> ennreal K" "K \<ge> 0"
    using less_top_ennreal by force
  show "bdd_above (sum f ` {F. F \<subseteq> A \<and> finite F})"
  proof(safe intro!: bdd_aboveI[where M=K])
    fix A'
    assume A':"A' \<subseteq> A" "finite A'"
    have "(\<Sum>\<^sub>\<infinity>x\<in>A. ennreal (f x)) = (\<Squnion> (sum (\<lambda>x. ennreal (f x)) ` {F. finite F \<and> F \<subseteq> A}))"
      by (simp add: nonneg_infsum_complete)
    also have "... = (\<Squnion> ((\<lambda>F. ennreal (sum f F)) ` {F. finite F \<and> F \<subseteq> A}))"
      by(auto intro!: SUP_cong sum_ennreal assms)
    finally have "(\<Squnion> ((\<lambda>F. ennreal (sum f F)) ` {F. finite F \<and> F \<subseteq> A})) \<le> ennreal K"
      using K by order
    hence "ennreal (sum f A') \<le> ennreal K"
      by (simp add: A' SUP_le_iff)
    thus "sum f A' \<le> K"
      by (simp add: K(2))
  qed
qed fact

lemma infsum_less_top_dest:
  fixes f :: "_ \<Rightarrow> _::{ordered_comm_monoid_add, topological_comm_monoid_add, t2_space, complete_linorder, linorder_topology}"
  assumes "(\<Sum>\<^sub>\<infinity>x\<in>A. f x) < top" "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0" "x \<in> A"
  shows "f x < top"
proof(rule ccontr)
  assume f:"\<not> f x < top"
  have "(\<Sum>\<^sub>\<infinity>x\<in>A. f x) = (\<Sum>\<^sub>\<infinity>y\<in>A - {x} \<union> {x}. f y)"
    by(rule arg_cong[where f="infsum _"]) (use assms in auto)
  also have "... = (\<Sum>\<^sub>\<infinity>y\<in>A- {x}. f y) + (\<Sum>\<^sub>\<infinity>y\<in>{x}. f y)"
    using assms(2) by(intro infsum_Un_disjoint) (auto intro!: nonneg_summable_on_complete)
  also have "... =  (\<Sum>\<^sub>\<infinity>y\<in>A- {x}. f y) + top"
    using f top.not_eq_extremum by fastforce
  also have "... = top"
    by(auto intro!: add_top infsum_nonneg assms)
  finally show False
    using assms(1) by simp
qed

lemma infsum_ennreal_eq:
  assumes "f summable_on A" "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
  shows "(\<Sum>\<^sub>\<infinity>x\<in>A. ennreal (f x)) = ennreal (\<Sum>\<^sub>\<infinity>x\<in>A. f x)"
proof -
  have "(\<Sum>\<^sub>\<infinity>x\<in>A. ennreal (f x)) = (\<Squnion> (sum (\<lambda>x. ennreal (f x)) ` {F. finite F \<and> F \<subseteq> A}))"
    by (simp add: nonneg_infsum_complete)
  also have "... = (\<Squnion> ((\<lambda>F. ennreal (sum f F)) ` {F. finite F \<and> F \<subseteq> A}))"
    by(auto intro!: SUP_cong sum_ennreal assms)
  also have "... = ennreal (\<Sum>\<^sub>\<infinity>x\<in>A. f x)"
    using infsum_nonneg_is_SUPREMUM_ennreal[OF assms] by simp
  finally show ?thesis .
qed

lemma abs_summable_on_integrable_iff:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  shows "Infinite_Sum.abs_summable_on f A \<longleftrightarrow> integrable (count_space A) f"
  by (simp add: abs_summable_equivalent abs_summable_on_def)

lemma infsum_eq_integral:
  fixes f :: "_ \<Rightarrow> _ :: {banach, second_countable_topology}"
  assumes "Infinite_Sum.abs_summable_on f A"
  shows "infsum f A = integral\<^sup>L (count_space A) f"
  using assms infsetsum_infsum[of f A,symmetric]
  by(auto simp: abs_summable_on_integrable_iff abs_summable_on_def infsetsum_def)

end