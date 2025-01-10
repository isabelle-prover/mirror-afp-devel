section \<open>\<open>Misc_Tensor_Product\<close> -- Miscelleanous results missing from other theories\<close>

theory Misc_Tensor_Product
  imports "HOL-Analysis.Elementary_Topology" "HOL-Analysis.Abstract_Topology"
    "HOL-Analysis.Abstract_Limits" "HOL-Analysis.Function_Topology" "HOL-Cardinals.Cardinals"
    "HOL-Analysis.Infinite_Sum" "HOL-Analysis.Harmonic_Numbers" Containers.Containers_Auxiliary
    Complex_Bounded_Operators.Extra_General
    Complex_Bounded_Operators.Extra_Vector_Spaces
    Complex_Bounded_Operators.Extra_Ordered_Fields
begin

unbundle lattice_syntax

lemma local_defE: "(\<And>x. x=y \<Longrightarrow> P) \<Longrightarrow> P" by metis
    \<comment> \<open>A helper lemma to introduce a local ``definition`` in the current goal when backwards reasoning.
        \<open>apply (rule local_defE[where x=\<open>stuff\<close>])\<close> will insert \<^term>\<open>x=stuff\<close> as a premise.
        This can be useful before using \<open>apply transfer\<close> because it will introduce some 
        additional knowledge about the properties of \<^term>\<open>x\<close> into the transferred goal.\<close>

lemma inv_prod_swap[simp]: \<open>inv prod.swap = prod.swap\<close>
  by (simp add: inv_unique_comp)

lemma filterlim_parametric[transfer_rule]: 
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  shows \<open>((R ===> S) ===> rel_filter S ===> rel_filter R ===> (=)) filterlim filterlim\<close>
  using filtermap_parametric[transfer_rule] le_filter_parametric[transfer_rule] apply fail?
  unfolding filterlim_def
  by transfer_prover


definition rel_topology :: \<open>('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a topology \<Rightarrow> 'b topology \<Rightarrow> bool)\<close> where
  \<open>rel_topology R S T \<longleftrightarrow> (rel_fun (rel_set R) (=)) (openin S) (openin T)
 \<and> (\<forall>U. openin S U \<longrightarrow> Domainp (rel_set R) U) \<and> (\<forall>U. openin T U \<longrightarrow> Rangep (rel_set R) U)\<close>

lemma rel_topology_eq[relator_eq]: \<open>rel_topology (=) = (=)\<close>
  unfolding rel_topology_def using openin_inject
  by (auto simp: rel_fun_eq rel_set_eq fun_eq_iff)

lemma Rangep_conversep[simp]: \<open>Rangep (R\<inverse>\<inverse>) = Domainp R\<close>
  by blast

lemma Domainp_conversep[simp]: \<open>Domainp (R\<inverse>\<inverse>) = Rangep R\<close>
  by blast

lemma conversep_rel_fun:
  includes lifting_syntax
  shows \<open>(T ===> U)\<inverse>\<inverse> = (T\<inverse>\<inverse>) ===> (U\<inverse>\<inverse>)\<close>
  by (auto simp: rel_fun_def)

lemma rel_topology_conversep[simp]: \<open>rel_topology (R\<inverse>\<inverse>) = ((rel_topology R)\<inverse>\<inverse>)\<close>
  by (auto simp add: rel_topology_def[abs_def] simp flip: conversep_rel_fun[where U=\<open>(=)\<close>, simplified])

lemma openin_parametric[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_topology R ===> rel_set R ===> (=)) openin openin\<close>
  by (auto simp add: rel_fun_def rel_topology_def)

lemma topspace_parametric [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_topology R ===> rel_set R) topspace topspace\<close>
proof -
  have *: \<open>\<exists>y\<in>topspace T'. R x y\<close> if \<open>rel_topology R T T'\<close> \<open>x \<in> topspace T\<close> for x T T' and R :: \<open>'q \<Rightarrow> 'r \<Rightarrow> bool\<close>
  proof -
    from that obtain U where \<open>openin T U\<close> and \<open>x \<in> U\<close>
      unfolding topspace_def
      by auto
    from \<open>openin T U\<close>
    have \<open>Domainp (rel_set R) U\<close>
      using \<open>rel_topology R T T'\<close> rel_topology_def by blast
    then obtain V where [transfer_rule]: \<open>rel_set R U V\<close>
      by blast
    with \<open>x \<in> U\<close> obtain y where \<open>R x y\<close> and \<open>y \<in> V\<close>
      by (meson rel_set_def)
    from \<open>rel_set R U V\<close> \<open>rel_topology R T T'\<close> \<open>openin T U\<close>
    have \<open>openin T' V\<close>
      by (simp add: rel_topology_def rel_fun_def)
    with \<open>y \<in> V\<close> have \<open>y \<in> topspace T'\<close>
      using openin_subset by auto
    with \<open>R x y\<close> show \<open>\<exists>y\<in>topspace T'. R x y\<close>
      by auto
  qed

  show ?thesis
    using *[where ?R.1=R]
    using *[where ?R.1=\<open>R\<inverse>\<inverse>\<close>]
    by (auto intro!: rel_setI)
qed

lemma [transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_total S\<close>
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  assumes [transfer_rule]: \<open>bi_total R\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>(rel_topology R ===> rel_topology S ===> (R ===> S) ===> (=)) continuous_map continuous_map\<close>
  unfolding continuous_map_def Pi_def
  by transfer_prover


lemma limitin_closedin:
  assumes \<open>limitin T f c F\<close>
  assumes \<open>range f \<subseteq> S\<close>
  assumes \<open>closedin T S\<close>
  assumes \<open>\<not> trivial_limit F\<close>
  shows \<open>c \<in> S\<close>
proof -
  from assms have \<open>T closure_of S = S\<close>
    by (simp add: closure_of_eq)
  moreover have \<open>c \<in> T closure_of S\<close>
    using assms(1) _ assms(4) apply (rule limitin_closure_of)
    using range_subsetD[OF assms(2)] by auto
  ultimately show ?thesis
    by simp
qed


lemma closure_nhds_principal: \<open>a \<in> closure A \<longleftrightarrow> inf (nhds a) (principal A) \<noteq> bot\<close>
proof (rule iffI)
  show \<open>inf (nhds a) (principal A) \<noteq> bot\<close> if \<open>a \<in> closure A\<close>
  proof (cases \<open>a \<in> A\<close>)
    case True
    thus ?thesis
      unfolding filter_eq_iff eventually_inf eventually_principal eventually_nhds by force
  next
    case False
    have "at a within A \<noteq> bot"
      using False that by (subst at_within_eq_bot_iff) auto
    also have "at a within A = inf (nhds a) (principal A)"
      using False by (simp add: at_within_def)
    finally show ?thesis .
  qed
  show \<open>a \<in> closure A\<close> if \<open>inf (nhds a) (principal A) \<noteq> bot\<close>
    by (metis Diff_empty Diff_insert0 at_within_def closure_subset not_in_closure_trivial_limitI subsetD that)
qed


lemma limit_in_closure:
  assumes lim: \<open>(f \<longlongrightarrow> x) F\<close>
  assumes nt: \<open>F \<noteq> bot\<close>
  assumes inA: \<open>\<forall>\<^sub>F x in F. f x \<in> A\<close>
  shows \<open>x \<in> closure A\<close>
proof (rule Lim_in_closed_set[of _ _ F])
  show "\<forall>\<^sub>F x in F. f x \<in> closure A"
    using inA by eventually_elim (use closure_subset in blast)
qed (use assms in auto)

(* TODO Move *)
lemma filterlim_nhdsin_iff_limitin:
  \<open>l \<in> topspace T \<and> filterlim f (nhdsin T l) F \<longleftrightarrow> limitin T f l F\<close>
  unfolding limitin_def
proof safe
  fix U assume *: "l \<in> topspace T" "filterlim f (nhdsin T l) F" "openin T U" "l \<in> U"
  hence "eventually (\<lambda>y. y \<in> U) (nhdsin T l)"
    unfolding eventually_nhdsin by blast
  thus "eventually (\<lambda>x. f x \<in> U) F"
    using *(2) eventually_compose_filterlim by blast
next
  assume *: "l \<in> topspace T" "\<forall>U. openin T U \<and> l \<in> U \<longrightarrow> (\<forall>\<^sub>F x in F. f x \<in> U)"
  show "filterlim f (nhdsin T l) F"
    unfolding filterlim_def le_filter_def eventually_filtermap
  proof safe
    fix P :: "'a \<Rightarrow> bool"
    assume "eventually P (nhdsin T l)"
    then obtain U where U: "openin T U" "l \<in> U" "\<forall>x\<in>U. P x"
      using *(1) unfolding eventually_nhdsin by blast
    with * have "eventually (\<lambda>x. f x \<in> U) F"
      by blast
    thus "eventually (\<lambda>x. P (f x)) F"
      by eventually_elim (use U in blast)
  qed
qed

lemma pullback_topology_bi_cont: 
  fixes g :: \<open>'a \<Rightarrow> ('b \<Rightarrow> 'c::topological_space)\<close>
    and f :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> and f' :: \<open>'c \<Rightarrow> 'c \<Rightarrow> 'c\<close>
  assumes gf_f'g: \<open>\<And>a b i. g (f a b) i = f' (g a i) (g b i)\<close>
  assumes f'_cont: \<open>\<And>a' b'. (case_prod f' \<longlongrightarrow> f' a' b') (nhds a' \<times>\<^sub>F nhds b')\<close>
  defines \<open>T \<equiv> pullback_topology UNIV g euclidean\<close>
  shows \<open>LIM (x,y) nhdsin T a \<times>\<^sub>F nhdsin T b. f x y :> nhdsin T (f a b)\<close>
proof -
  have topspace[simp]: \<open>topspace T = UNIV\<close>
    unfolding T_def topspace_pullback_topology by simp
  have openin: \<open>openin T U \<longleftrightarrow> (\<exists>V. open V \<and> U = g -` V)\<close> for U
    by (simp add: assms openin_pullback_topology)

  have 1: \<open>nhdsin T a = filtercomap g (nhds (g a))\<close>
    for a :: 'a
    by (auto simp add: filter_eq_iff eventually_filtercomap eventually_nhds eventually_nhdsin openin)

  have \<open>((g \<circ> case_prod f) \<longlongrightarrow> g (f a b)) (nhdsin T a \<times>\<^sub>F nhdsin T b)\<close>
  proof (unfold tendsto_def, intro allI impI)
    fix S assume \<open>open S\<close> and gfS: \<open>g (f a b) \<in> S\<close>
    obtain U where gf_PiE: \<open>g (f a b) \<in> Pi\<^sub>E UNIV U\<close> and openU: \<open>\<forall>i. openin euclidean (U i)\<close>
      and finiteD: \<open>finite {i. U i \<noteq> topspace euclidean}\<close> and US: \<open>Pi\<^sub>E UNIV U \<subseteq> S\<close>
      using product_topology_open_contains_basis[OF \<open>open S\<close>[unfolded open_fun_def] gfS]
      by auto

    define D where \<open>D = {i. U i \<noteq> UNIV}\<close>
    with finiteD have \<open>finite D\<close>
      by auto

    from openU have openU: \<open>open (U i)\<close> for i
      by auto

    have *: \<open>f' (g a i) (g b i) \<in> U i\<close> for i
      by (metis PiE_mem gf_PiE iso_tuple_UNIV_I gf_f'g)

    have \<open>\<forall>\<^sub>F x in nhds (g a i) \<times>\<^sub>F nhds (g b i). case_prod f' x \<in> U i\<close> for i
      using tendsto_def[THEN iffD1, rule_format, OF f'_cont openU *, of i] by -

    then obtain Pa Pb where \<open>eventually (Pa i) (nhds (g a i))\<close> and \<open>eventually (Pb i) (nhds (g b i))\<close>
      and PaPb_plus: \<open>(\<forall>x y. Pa i x \<longrightarrow> Pb i y \<longrightarrow> f' x y \<in> U i)\<close> for i
      unfolding eventually_prod_filter by (metis prod.simps(2))

    from \<open>\<And>i. eventually (Pa i) (nhds (g a i))\<close>
    obtain Ua where \<open>open (Ua i)\<close> and a_Ua: \<open>g a i \<in> Ua i\<close> and Ua_Pa: \<open>Ua i \<subseteq> Collect (Pa i)\<close> for i
      unfolding eventually_nhds
      apply atomize_elim
      by (metis mem_Collect_eq subsetI)
    from \<open>\<And>i. eventually (Pb i) (nhds (g b i))\<close>
    obtain Ub where \<open>open (Ub i)\<close> and b_Ub: \<open>g b i \<in> Ub i\<close> and Ub_Pb: \<open>Ub i \<subseteq> Collect (Pb i)\<close> for i
      unfolding eventually_nhds
      apply atomize_elim
      by (metis mem_Collect_eq subsetI)
    have UaUb_plus: \<open>x \<in> Ua i \<Longrightarrow> y \<in> Ub i \<Longrightarrow> f' x y \<in> U i\<close> for i x y
      by (metis PaPb_plus Ua_Pa Ub_Pb mem_Collect_eq subsetD)

    define Ua' where \<open>Ua' i = (if i\<in>D then Ua i else UNIV)\<close> for i
    define Ub' where \<open>Ub' i = (if i\<in>D then Ub i else UNIV)\<close> for i

    have Ua'_UNIV: \<open>U i = UNIV \<Longrightarrow> Ua' i = UNIV\<close> for i
      by (simp add: D_def Ua'_def)
    have Ub'_UNIV: \<open>U i = UNIV \<Longrightarrow> Ub' i = UNIV\<close> for i
      by (simp add: D_def Ub'_def)
    have [simp]: \<open>open (Ua' i)\<close> for i
      by (simp add: Ua'_def \<open>open (Ua _)\<close>)
    have [simp]: \<open>open (Ub' i)\<close> for i
      by (simp add: Ub'_def \<open>open (Ub _)\<close>)
    have a_Ua': \<open>g a i \<in> Ua' i\<close> for i
      by (simp add: Ua'_def a_Ua)
    have b_Ub': \<open>g b i \<in> Ub' i\<close> for i
      by (simp add: Ub'_def b_Ub)
    have UaUb'_plus: \<open>a' \<in> Ua' i \<Longrightarrow> b' \<in> Ub' i \<Longrightarrow> f' a' b' \<in> U i\<close> for i a' b'
      apply (cases \<open>i \<in> D\<close>)
      using UaUb_plus by (auto simp add: Ua'_def  Ub'_def D_def)

    define Ua'' where \<open>Ua'' = Pi UNIV Ua'\<close>
    define Ub'' where \<open>Ub'' = Pi UNIV Ub'\<close>

    have \<open>open Ua''\<close>
      using finiteD Ua'_UNIV
      by (auto simp add: open_fun_def Ua''_def PiE_UNIV_domain
            openin_product_topology_alt D_def intro!: exI[where x=\<open>Ua'\<close>] intro: rev_finite_subset)
    have \<open>open Ub''\<close>
      using finiteD Ub'_UNIV
      by (auto simp add: open_fun_def Ub''_def PiE_UNIV_domain
            openin_product_topology_alt D_def intro!: exI[where x=\<open>Ub'\<close>] intro: rev_finite_subset)
    have a_Ua'': \<open>g a \<in> Ua''\<close>
      by (simp add: Ua''_def a_Ua')
    have b_Ub'': \<open>g b \<in> Ub''\<close>
      by (simp add: Ub''_def b_Ub')
    have UaUb''_plus: \<open>a' \<in> Ua'' \<Longrightarrow> b' \<in> Ub'' \<Longrightarrow> f' (a' i) (b' i) \<in> U i\<close> for i a' b'
      using UaUb'_plus by (force simp add: Ua''_def  Ub''_def)

    define Ua''' where \<open>Ua''' = g -` Ua''\<close>
    define Ub''' where \<open>Ub''' = g -` Ub''\<close>
    have \<open>openin T Ua'''\<close>
      using \<open>open Ua''\<close> by (auto simp: openin Ua'''_def)
    have \<open>openin T Ub'''\<close>
      using \<open>open Ub''\<close> by (auto simp: openin Ub'''_def)
    have a_Ua'': \<open>a \<in> Ua'''\<close>
      by (simp add: Ua'''_def a_Ua'')
    have b_Ub'': \<open>b \<in> Ub'''\<close>
      by (simp add: Ub'''_def b_Ub'')
    have UaUb'''_plus: \<open>a \<in> Ua''' \<Longrightarrow> b \<in> Ub''' \<Longrightarrow> f' (g a i) (g b i) \<in> U i\<close> for i a b
      by (simp add: Ua'''_def UaUb''_plus Ub'''_def)

    define Pa' where \<open>Pa' a \<longleftrightarrow> a \<in> Ua'''\<close> for a
    define Pb' where \<open>Pb' b \<longleftrightarrow> b \<in> Ub'''\<close> for b

    have Pa'_nhd: \<open>eventually Pa' (nhdsin T a)\<close>
      using \<open>openin T Ua'''\<close>
      by (auto simp add: Pa'_def eventually_nhdsin intro!: exI[of _ \<open>Ua'''\<close>] a_Ua'')
    have Pb'_nhd: \<open>eventually Pb' (nhdsin T b)\<close>
      using \<open>openin T Ub'''\<close>
      by (auto simp add: Pb'_def eventually_nhdsin intro!: exI[of _ \<open>Ub'''\<close>] b_Ub'')
    have Pa'Pb'_plus: \<open>(g \<circ> case_prod f) (a, b) \<in> S\<close> if \<open>Pa' a\<close> \<open>Pb' b\<close> for a b
      using that UaUb'''_plus US
      by (auto simp add: Pa'_def Pb'_def PiE_UNIV_domain Pi_iff gf_f'g)

    show \<open>\<forall>\<^sub>F x in nhdsin T a \<times>\<^sub>F nhdsin T b. (g \<circ> case_prod f) x \<in> S\<close>
      using Pa'_nhd Pb'_nhd Pa'Pb'_plus
      unfolding eventually_prod_filter
      apply -
      apply (rule exI[of _ Pa'])
      apply (rule exI[of _ Pb'])
      by simp
  qed
  then show ?thesis
    unfolding 1 filterlim_filtercomap_iff by -
qed

definition \<open>has_sum_in T f A x \<longleftrightarrow> limitin T (sum f) x (finite_subsets_at_top A)\<close>


lemma has_sum_in_finite:
  assumes "finite F"
  assumes \<open>sum f F \<in> topspace T\<close>
  shows "has_sum_in T f F (sum f F)"
  using assms
  by (simp add: finite_subsets_at_top_finite has_sum_in_def limitin_def eventually_principal)


definition \<open>summable_on_in T f A \<longleftrightarrow> (\<exists>x. has_sum_in T f A x)\<close>

definition \<open>infsum_in T f A = (let L = Collect (has_sum_in T f A) in if card L = 1 then the_elem L else 0)\<close>
(* The reason why we return 0 also in the case that there are several solutions is to make sure infsum_in is parametric.
(See lemma 'infsum_in_parametric' below. *)

lemma hausdorff_OFCLASS_t2_space: \<open>OFCLASS('a::topological_space, t2_space_class)\<close> if \<open>Hausdorff_space (euclidean :: 'a topology)\<close>
proof intro_classes
  fix a b :: 'a
  assume \<open>a \<noteq> b\<close>
  from that
  show \<open>\<exists>U V. open U \<and> open V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}\<close>
    unfolding Hausdorff_space_def disjnt_def
    using \<open>a \<noteq> b\<close> by auto
qed

lemma hausdorffI: 
  assumes \<open>\<And>x y. x \<in> topspace T \<Longrightarrow> y \<in> topspace T \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>U V. openin T U \<and> openin T V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}\<close>
  shows \<open>Hausdorff_space T\<close>
  using assms by (auto simp: Hausdorff_space_def disjnt_def)

lemma hausdorff_euclidean[simp]: \<open>Hausdorff_space (euclidean :: _::t2_space topology)\<close>
  apply (rule hausdorffI)
  by (metis (mono_tags, lifting) hausdorff open_openin)

lemma has_sum_in_unique:
  assumes \<open>Hausdorff_space T\<close>
  assumes \<open>has_sum_in T f A l\<close>
  assumes \<open>has_sum_in T f A l'\<close>
  shows \<open>l = l'\<close>
  using assms(2,3)[unfolded has_sum_in_def] _ assms(1)
  apply (rule limitin_Hausdorff_unique)
  by simp

lemma infsum_in_def':
  assumes \<open>Hausdorff_space T\<close>
  shows \<open>infsum_in T f A = (if summable_on_in T f A then (THE s. has_sum_in T f A s) else 0)\<close>
proof (cases \<open>Collect (has_sum_in T f A) = {}\<close>)
  case True
  then show ?thesis using True
    by (auto simp: infsum_in_def summable_on_in_def Let_def card_1_singleton_iff)
next
  case False
  then have \<open>summable_on_in T f A\<close>
    by (metis (no_types, lifting) empty_Collect_eq summable_on_in_def)
  from False \<open>Hausdorff_space T\<close>
  have \<open>card (Collect (has_sum_in T f A)) = 1\<close>
    by (metis (mono_tags, opaque_lifting) has_sum_in_unique is_singletonI' is_singleton_altdef mem_Collect_eq)
  then show ?thesis
    using \<open>summable_on_in T f A\<close>
    by (smt (verit, best) assms card_1_singletonE has_sum_in_unique infsum_in_def mem_Collect_eq singletonI the_elem_eq the_equality)
qed

lemma has_sum_in_infsum_in: 
  assumes \<open>Hausdorff_space T\<close> and summable: \<open>summable_on_in T f A\<close>
  shows \<open>has_sum_in T f A (infsum_in T f A)\<close>
  apply (simp add: infsum_in_def'[OF \<open>Hausdorff_space T\<close>] summable)
  apply (rule theI'[of \<open>has_sum_in T f A\<close>])
  using has_sum_in_unique[OF \<open>Hausdorff_space T\<close>, of f A] summable
  by (meson summable_on_in_def)


lemma nhdsin_mono:
  assumes [simp]: \<open>\<And>x. openin T' x \<Longrightarrow> openin T x\<close>
  assumes [simp]: \<open>topspace T = topspace T'\<close>
  shows \<open>nhdsin T a \<le> nhdsin T' a\<close>
  unfolding nhdsin_def 
  by (auto intro!: INF_superset_mono)


lemma has_sum_in_cong: 
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "has_sum_in T f A x \<longleftrightarrow> has_sum_in T g A x"
proof -
  have \<open>(\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x \<in> U) \<longleftrightarrow> (\<forall>\<^sub>F x in finite_subsets_at_top A. sum g x \<in> U)\<close> for U
    apply (rule eventually_subst)
    apply (subst eventually_finite_subsets_at_top)
    by (metis (mono_tags, lifting) assms empty_subsetI finite.emptyI subset_eq sum.cong)
  then show ?thesis
    by (simp add: has_sum_in_def limitin_def)
qed

lemma infsum_in_eqI':
  fixes f g :: \<open>'a \<Rightarrow> 'b::comm_monoid_add\<close>
  assumes \<open>\<And>x. has_sum_in T f A x \<longleftrightarrow> has_sum_in T g B x\<close>
  shows \<open>infsum_in T f A = infsum_in T g B\<close>
  by (simp add: infsum_in_def assms[abs_def] summable_on_in_def)

lemma infsum_in_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "infsum_in T f A = infsum_in T g A"
  using assms infsum_in_eqI' has_sum_in_cong by blast

lemma limitin_cong: "limitin T f c F \<longleftrightarrow> limitin T g c F" if "eventually (\<lambda>x. f x = g x) F"
  by (smt (verit, best) eventually_elim2 limitin_transform_eventually that)

lemma has_sum_in_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>has_sum_in T g (h ` A) x \<longleftrightarrow> has_sum_in T (g \<circ> h) A x\<close>
proof -
  have \<open>has_sum_in T g (h ` A) x \<longleftrightarrow> limitin T (sum g) x (finite_subsets_at_top (h ` A))\<close>
    by (simp add: has_sum_in_def)
  also have \<open>\<dots> \<longleftrightarrow> limitin T (\<lambda>F. sum g (h ` F)) x (finite_subsets_at_top A)\<close>
    apply (subst filtermap_image_finite_subsets_at_top[symmetric])
    by (simp_all add: assms eventually_filtermap limitin_def)
  also have \<open>\<dots> \<longleftrightarrow> limitin T (sum (g \<circ> h)) x (finite_subsets_at_top A)\<close>
    apply (rule limitin_cong)
    apply (rule eventually_finite_subsets_at_top_weakI)
    apply (rule sum.reindex)
    using assms subset_inj_on by blast
  also have \<open>\<dots> \<longleftrightarrow> has_sum_in T (g \<circ> h) A x\<close>
    by (simp add: has_sum_in_def)
  finally show ?thesis .
qed

lemma summable_on_in_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>summable_on_in T g (h ` A) \<longleftrightarrow> summable_on_in T (g \<circ> h) A\<close>
  by (simp add: assms summable_on_in_def has_sum_in_reindex)

lemma infsum_in_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>infsum_in T g (h ` A) = infsum_in T (g \<circ> h) A\<close>
  by (metis Collect_cong assms has_sum_in_reindex infsum_in_def)

lemma has_sum_in_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "has_sum_in T (\<lambda>x. f (g x)) A s \<longleftrightarrow> has_sum_in T f B s"
proof -
  have \<open>has_sum_in T (\<lambda>x. f (g x)) A s \<longleftrightarrow> has_sum_in T f (g ` A) s\<close>
    by (metis (mono_tags, lifting) assms bij_betw_imp_inj_on has_sum_in_cong has_sum_in_reindex o_def)
  also have \<open>\<dots> = has_sum_in T f B s\<close>
    using assms bij_betw_imp_surj_on by blast
  finally show ?thesis .
qed


lemma has_sum_euclidean_iff: \<open>has_sum_in euclidean f A s \<longleftrightarrow> (f has_sum s) A\<close>
  by (simp add: has_sum_def has_sum_in_def)

lemma summable_on_euclidean_eq: \<open>summable_on_in euclidean f A \<longleftrightarrow> f summable_on A\<close>
  by (auto simp add: infsum_def infsum_in_def has_sum_euclidean_iff[abs_def] has_sum_def
      t2_space_class.Lim_def summable_on_def summable_on_in_def)

lemma infsum_euclidean_eq: \<open>infsum_in euclidean f A = infsum f A\<close>
  by (auto simp add: infsum_def infsum_in_def' summable_on_euclidean_eq
      has_sum_euclidean_iff[abs_def] has_sum_def t2_space_class.Lim_def)

lemma infsum_in_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "infsum_in T (\<lambda>x. f (g x)) A = infsum_in T f B"
proof -
  have \<open>infsum_in T (\<lambda>x. f (g x)) A = infsum_in T f (g ` A)\<close>
    by (metis (mono_tags, lifting) assms bij_betw_imp_inj_on infsum_in_cong infsum_in_reindex o_def)
  also have \<open>\<dots> = infsum_in T f B\<close>
    using assms bij_betw_imp_surj_on by blast
  finally show ?thesis .
qed

lemma limitin_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  shows \<open>(rel_topology S ===> (R ===> S) ===> S ===> rel_filter R ===> (\<longleftrightarrow>)) limitin limitin\<close>
proof (intro rel_funI, rename_tac T T' f f' l l' F F')
  fix T T' f f' l l' F F'
  assume [transfer_rule]: \<open>rel_topology S T T'\<close>
  assume [transfer_rule]: \<open>(R ===> S) f f'\<close>
  assume [transfer_rule]: \<open>S l l'\<close>
  assume [transfer_rule]: \<open>rel_filter R F F'\<close>

  have topspace: \<open>l \<in> topspace T \<longleftrightarrow> l' \<in> topspace T'\<close>
    by transfer_prover

  have open1: \<open>\<forall>\<^sub>F x in F. f x \<in> U\<close>
    if \<open>openin T U\<close> and \<open>l \<in> U\<close> and lhs: \<open>(\<forall>V. openin T' V \<and> l' \<in> V \<longrightarrow> (\<forall>\<^sub>F x in F'. f' x \<in> V))\<close>
    for U
  proof -
    from \<open>rel_topology S T T'\<close> \<open>openin T U\<close>
    obtain V where \<open>openin T' V\<close> and [transfer_rule]: \<open>rel_set S U V\<close>
      by (smt (verit, best) Domainp.cases rel_fun_def rel_topology_def)
    with \<open>S l l'\<close> have \<open>l' \<in> V\<close>
      by (metis (no_types, lifting) assms bi_uniqueDr rel_setD1 that(2))
    with lhs \<open>openin T' V\<close>
    have \<open>\<forall>\<^sub>F x in F'. f' x \<in> V\<close>
      by auto
    then show \<open>\<forall>\<^sub>F x in F. f x \<in> U\<close>
      by transfer simp
  qed

  have open2: \<open>\<forall>\<^sub>F x in F'. f' x \<in> V\<close>
    if \<open>openin T' V\<close> and \<open>l' \<in> V\<close> and lhs: \<open>(\<forall>U. openin T U \<and> l \<in> U \<longrightarrow> (\<forall>\<^sub>F x in F. f x \<in> U))\<close>
    for V
  proof -
    from \<open>rel_topology S T T'\<close> \<open>openin T' V\<close>
    obtain U where \<open>openin T U\<close> and [transfer_rule]: \<open>rel_set S U V\<close>
      by (auto simp: rel_topology_def rel_fun_def)
    with \<open>S l l'\<close> have \<open>l \<in> U\<close>
      by (metis (full_types) assms bi_unique_def rel_setD2 that(2))
    with lhs \<open>openin T U\<close>
    have \<open>\<forall>\<^sub>F x in F. f x \<in> U\<close>
      by auto
    then show \<open>\<forall>\<^sub>F x in F'. f' x \<in> V\<close>
      by transfer simp
  qed

  from topspace open1 open2
  show \<open>limitin T f l F = limitin T' f' l' F'\<close>
    unfolding limitin_def by auto
qed

lemma finite_subsets_at_top_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>(rel_set R ===> rel_filter (rel_set R)) finite_subsets_at_top finite_subsets_at_top\<close>
proof (intro rel_funI)
  fix A B assume \<open>rel_set R A B\<close>
  from \<open>bi_unique R\<close> obtain f where Rf: \<open>R x (f x)\<close> if \<open>x \<in> A\<close> for x
    by (metis (no_types, opaque_lifting) \<open>rel_set R A B\<close> rel_setD1)
  have \<open>inj_on f A\<close>
    by (metis (no_types, lifting) Rf assms bi_unique_def inj_onI)
  have \<open>B = f ` A\<close>
    by (metis (mono_tags, lifting) Rf \<open>rel_set R A B\<close> assms bi_uniqueDr bi_unique_rel_set_lemma image_cong)

  have RfX: \<open>rel_set R X (f ` X)\<close> if \<open>X \<subseteq> A\<close> for X
    apply (rule rel_setI)
    subgoal
      by (metis (no_types, lifting) Rf \<open>inj_on f A\<close> in_mono inj_on_image_mem_iff that)
    subgoal
      by (metis (no_types, lifting) Rf imageE subsetD that)
    done

  have Piff: \<open>(\<exists>X. finite X \<and> X \<subseteq> A \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> P (f ` Y))) \<longleftrightarrow>
              (\<exists>X. finite X \<and> X \<subseteq> B \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> B \<longrightarrow> P Y))\<close> for P
  proof (rule iffI)
    assume \<open>\<exists>X. finite X \<and> X \<subseteq> A \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> P (f ` Y))\<close>
    then obtain X where \<open>finite X\<close> and \<open>X \<subseteq> A\<close> and XP: \<open>finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> P (f ` Y)\<close> for Y
      by auto
    define X' where \<open>X' = f ` X\<close>
    have \<open>finite X'\<close>
      by (metis X'_def \<open>finite X\<close> finite_imageI)
    have \<open>X' \<subseteq> B\<close>
      by (smt (verit, best) Rf X'_def \<open>X \<subseteq> A\<close> \<open>rel_set R A B\<close> assms bi_uniqueDr image_subset_iff rel_setD1 subsetD)
    have \<open>P Y'\<close> if \<open>finite Y'\<close> and \<open>X' \<subseteq> Y'\<close> and \<open>Y' \<subseteq> B\<close> for Y'
    proof -
      define Y where \<open>Y = (f -` Y') \<inter> A\<close>
      have \<open>finite Y\<close>
        by (metis Y_def \<open>inj_on f A\<close> finite_vimage_IntI that(1))
      moreover have \<open>X \<subseteq> Y\<close>
        by (metis (no_types, lifting) X'_def Y_def \<open>X \<subseteq> A\<close> image_subset_iff_subset_vimage le_inf_iff that(2))
      moreover have \<open>Y \<subseteq> A\<close>
        by (metis (no_types, lifting) Y_def inf_le2)
      ultimately have \<open>P (f ` Y)\<close>
        by (rule XP)
      then show \<open>P Y'\<close>
        by (metis (no_types, lifting) Int_greatest Y_def \<open>B = f ` A\<close> dual_order.refl image_subset_iff_subset_vimage inf_le1 subset_antisym subset_image_iff that(3))
    qed
    then show \<open>\<exists>X. finite X \<and> X \<subseteq> B \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> B \<longrightarrow> P Y)\<close>
      by (metis (no_types, opaque_lifting) \<open>X' \<subseteq> B\<close> \<open>finite X'\<close>)
  next
    assume \<open>\<exists>X. finite X \<and> X \<subseteq> B \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> B \<longrightarrow> P Y)\<close>
    then obtain X where \<open>finite X\<close> and \<open>X \<subseteq> B\<close> and XP: \<open>finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> B \<Longrightarrow> P Y\<close> for Y
      by auto
    define X' where \<open>X' = (f -` X) \<inter> A\<close>
    have \<open>finite X'\<close>
      by (simp add: X'_def \<open>finite X\<close> \<open>inj_on f A\<close> finite_vimage_IntI)
    have \<open>X' \<subseteq> A\<close>
      by (simp add: X'_def)
    have \<open>P (f ` Y')\<close> if \<open>finite Y'\<close> and \<open>X' \<subseteq> Y'\<close> and \<open>Y' \<subseteq> A\<close> for Y'
    proof -
      define Y where \<open>Y = f ` Y'\<close>
      have \<open>finite Y\<close>
        by (metis Y_def finite_imageI that(1))
      moreover have \<open>X \<subseteq> Y\<close>
        using X'_def Y_def \<open>B = f ` A\<close> \<open>X \<subseteq> B\<close> that(2) by blast
      moreover have \<open>Y \<subseteq> B\<close>
        by (metis Y_def \<open>B = f ` A\<close> image_mono that(3))
      ultimately have \<open>P Y\<close>
        by (rule XP)
      then show \<open>P (f ` Y')\<close>
        by (smt (z3) Y_def \<open>B = f ` A\<close> imageE imageI subset_antisym subset_iff that(3) vimage_eq)
    qed
    then show \<open>\<exists>X. finite X \<and> X \<subseteq> A \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> P (f ` Y))\<close>
      by (metis \<open>X' \<subseteq> A\<close> \<open>finite X'\<close>)
  qed

  define Z where \<open>Z = filtermap (\<lambda>M. (M, f`M)) (finite_subsets_at_top A)\<close>
  have \<open>\<forall>\<^sub>F (x, y) in Z. rel_set R x y\<close>
    by (auto intro!: eventually_finite_subsets_at_top_weakI simp add: Z_def eventually_filtermap RfX)
  moreover have \<open>map_filter_on {(x, y). rel_set R x y} fst Z = finite_subsets_at_top A\<close>
    apply (rule filter_eq_iff[THEN iffD2])
    apply (subst eventually_map_filter_on)
    subgoal
      by (auto intro!: eventually_finite_subsets_at_top_weakI simp add: Z_def eventually_filtermap RfX)[1]
    subgoal
      by (auto simp add: Z_def eventually_filtermap eventually_finite_subsets_at_top RfX)
    done
  moreover have \<open>map_filter_on {(x, y). rel_set R x y} snd Z = finite_subsets_at_top B\<close>
    apply (rule filter_eq_iff[THEN iffD2])
    apply (subst eventually_map_filter_on)
    subgoal
      by (auto intro!: eventually_finite_subsets_at_top_weakI simp add: Z_def eventually_filtermap RfX)[1]
    subgoal
      by (simp add: Z_def eventually_filtermap eventually_finite_subsets_at_top RfX Piff)
    done
  ultimately show \<open>rel_filter (rel_set R) (finite_subsets_at_top A) (finite_subsets_at_top B)\<close>
    by (rule rel_filter.intros[where Z=Z])
qed

lemma sum_parametric'[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close> and S :: \<open>'c::comm_monoid_add \<Rightarrow> 'd::comm_monoid_add \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  assumes [transfer_rule]: \<open>(S ===> S ===> S) (+) (+)\<close>
  assumes [transfer_rule]: \<open>S 0 0\<close>
  shows \<open>((R ===> S) ===> rel_set R ===> S) sum sum\<close>
proof (intro rel_funI)
  fix A B f g assume \<open>rel_set R A B\<close> and \<open>(R ===> S) f g\<close>
  from \<open>bi_unique R\<close> obtain p where Rf: \<open>R x (p x)\<close> if \<open>x \<in> A\<close> for x
    by (metis (no_types, opaque_lifting) \<open>rel_set R A B\<close> rel_setD1)
  have \<open>inj_on p A\<close>
    by (metis (no_types, lifting) Rf \<open>bi_unique R\<close> bi_unique_def inj_onI)
  have \<open>B = p ` A\<close>
    by (metis (mono_tags, lifting) Rf \<open>rel_set R A B\<close> \<open>bi_unique R\<close> bi_uniqueDr bi_unique_rel_set_lemma image_cong)

  define A_copy where \<open>A_copy = A\<close>

  have *: \<open>S (f x + sum f F) (g (p x) + sum g (p ` F))\<close>
    if [transfer_rule]: \<open>S (sum f F) (sum g (p ` F))\<close> and [simp]: \<open>x \<in> A\<close> for x F
    by (metis (no_types, opaque_lifting) Rf \<open>(R ===> S) f g\<close> assms(2) rel_fun_def that(1) that(2))
  have ind_step: \<open>S (sum f (insert x F)) (sum g (p ` insert x F))\<close> 
    if \<open>S (sum f F) (sum g (p ` F))\<close> \<open>x \<in> A\<close> \<open>x \<notin> F\<close> \<open>finite F\<close> \<open>F \<subseteq> A\<close> for x F
  proof -
    have "sum g (p ` insert x F) = g (p x) + sum g (p ` F)"
      unfolding image_insert using that
      by (subst sum.insert) (use inj_onD[OF \<open>inj_on p A\<close>, of x] in \<open>auto\<close>)
    thus ?thesis
      using that * by simp
  qed

  have \<open>S (\<Sum>x\<in>A. f x) (\<Sum>x\<in>p ` A. g x)\<close> if \<open>A \<subseteq> A_copy\<close>
    using that
   apply (induction A rule:infinite_finite_induct)
    unfolding A_copy_def
    subgoal
      by (metis (no_types, lifting) \<open>inj_on p A\<close> assms(3) finite_image_iff subset_inj_on sum.infinite)
    using \<open>S 0 0\<close> ind_step by auto
  hence \<open>S (\<Sum>x\<in>A. f x) (\<Sum>x\<in>p ` A. g x)\<close>
    by (simp add: A_copy_def)
  also have \<open>\<dots> = (\<Sum>x\<in>B. g x)\<close>
    by (metis (full_types) \<open>B = p ` A\<close>)
  finally show \<open>S (\<Sum>x\<in>A. f x) (\<Sum>x\<in>B. g x)\<close>
    by -
qed


lemma has_sum_in_parametric[transfer_rule]:
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close> and S :: \<open>'c::comm_monoid_add \<Rightarrow> 'd::comm_monoid_add \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  assumes [transfer_rule]: \<open>(S ===> S ===> S) (+) (+)\<close>
  assumes [transfer_rule]: \<open>S 0 0\<close>
  shows \<open>(rel_topology S ===> (R ===> S) ===> (rel_set R) ===> S ===> (=)) has_sum_in has_sum_in\<close>
proof -
  note sum_parametric'[transfer_rule]
  show ?thesis
    unfolding has_sum_in_def
    by transfer_prover
qed

lemma has_sum_in_topspace: \<open>has_sum_in T f A s \<Longrightarrow> s \<in> topspace T\<close>
  by (metis has_sum_in_def limitin_def)

lemma summable_on_in_parametric[transfer_rule]: 
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  assumes [transfer_rule]: \<open>(S ===> S ===> S) (+) (+)\<close>
  assumes [transfer_rule]: \<open>S 0 0\<close>
  shows \<open>(rel_topology S ===> (R ===> S) ===> (rel_set R) ===> (=)) summable_on_in summable_on_in\<close>
proof (intro rel_funI)
  fix T T' assume [transfer_rule]: \<open>rel_topology S T T'\<close>
  fix f f' assume [transfer_rule]: \<open>(R ===> S) f f'\<close>
  fix A A' assume [transfer_rule]: \<open>rel_set R A A'\<close>

  define ExT ExT' where \<open>ExT P \<longleftrightarrow> (\<exists>x\<in>Collect (Domainp S). P x)\<close> and \<open>ExT' P' \<longleftrightarrow> (\<exists>x\<in>Collect (Rangep S). P' x)\<close> for P P'
  have [transfer_rule]: \<open>((S ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) ExT ExT'\<close>
    by (smt (z3) Domainp_iff ExT'_def ExT_def RangePI Rangep.cases mem_Collect_eq rel_fun_def)
  from \<open>rel_topology S T T'\<close> have top1: \<open>topspace T \<subseteq> Collect (Domainp S)\<close>
    unfolding rel_topology_def
    by (metis (no_types, lifting) Domainp_set mem_Collect_eq openin_topspace subsetI)
  from \<open>rel_topology S T T'\<close> have top2: \<open>topspace T' \<subseteq> Collect (Rangep S)\<close>
    unfolding rel_topology_def
    by (metis (no_types, lifting) RangePI Rangep.cases mem_Collect_eq openin_topspace rel_setD2 subsetI)

  have \<open>ExT (has_sum_in T f A) = ExT' (has_sum_in T' f' A')\<close>
    by transfer_prover
  with top1 top2 show \<open>summable_on_in T f A \<longleftrightarrow> summable_on_in T' f' A'\<close>
    by (metis ExT'_def ExT_def has_sum_in_topspace in_mono summable_on_in_def)
qed

lemma not_summable_infsum_in_0: \<open>\<not> summable_on_in T f A \<Longrightarrow> infsum_in T f A = 0\<close>
  by (smt (verit, del_insts) Collect_empty_eq card_eq_0_iff infsum_in_def summable_on_in_def zero_neq_one)

lemma infsum_in_parametric[transfer_rule]: 
  includes lifting_syntax
  fixes R :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  assumes [transfer_rule]: \<open>(S ===> S ===> S) (+) (+)\<close>
  assumes [transfer_rule]: \<open>S 0 0\<close>
  shows \<open>(rel_topology S ===> (R ===> S) ===> (rel_set R) ===> S) infsum_in infsum_in\<close>
proof (intro rel_funI)
  fix T T' assume [transfer_rule]: \<open>rel_topology S T T'\<close>
  fix f f' assume [transfer_rule]: \<open>(R ===> S) f f'\<close>
  fix A A' assume [transfer_rule]: \<open>rel_set R A A'\<close>
  have S_has_sum: \<open>(S ===> (=)) (has_sum_in T f A) (has_sum_in T' f' A')\<close>
    by transfer_prover

  have sum_iff: \<open>summable_on_in T f A \<longleftrightarrow> summable_on_in T' f' A'\<close>
    by transfer_prover

  define L L' where \<open>L = Collect (has_sum_in T f A)\<close> and \<open>L' = Collect (has_sum_in T' f' A')\<close>

  have LT: \<open>L \<subseteq> topspace T\<close>
    by (metis (mono_tags, lifting) Ball_Collect L_def has_sum_in_topspace subset_iff)
  have TS: \<open>topspace T \<subseteq> Collect (Domainp S)\<close>
    by (metis (no_types, lifting) Ball_Collect Domainp_set \<open>rel_topology S T T'\<close> openin_topspace rel_topology_def)
  have LT': \<open>L' \<subseteq> topspace T'\<close>
    by (metis Ball_Collect L'_def has_sum_in_topspace subset_eq)
  have T'S: \<open>topspace T' \<subseteq> Collect (Rangep S)\<close>
    by (metis (mono_tags, opaque_lifting) Ball_Collect RangePI \<open>rel_topology S T T'\<close> rel_fun_def rel_setD2 topspace_parametric)
  have Sss': \<open>S s s' \<Longrightarrow> has_sum_in T f A s \<longleftrightarrow> has_sum_in T' f' A' s'\<close> for s s'
    using S_has_sum
    by (metis (mono_tags, lifting) rel_funE)

  have \<open>rel_set S L L'\<close>
    by (smt (verit) Domainp.cases L'_def L_def Rangep.cases \<open>L \<subseteq> topspace T\<close> \<open>L' \<subseteq> topspace T'\<close> \<open>\<And>s' s. S s s' \<Longrightarrow> has_sum_in T f A s = has_sum_in T' f' A' s'\<close> \<open>topspace T \<subseteq> Collect (Domainp S)\<close> \<open>topspace T' \<subseteq> Collect (Rangep S)\<close> in_mono mem_Collect_eq rel_setI)

  have cardLL': \<open>card L = 1 \<longleftrightarrow> card L' = 1\<close>
    by (metis (no_types, lifting) \<open>rel_set S L L'\<close> assms(2) bi_unique_rel_set_lemma card_image)

  have \<open>S (infsum_in T f A) (infsum_in T' f' A')\<close> if \<open>card L \<noteq> 1\<close>
    using that cardLL' by (simp add: infsum_in_def L'_def L_def Let_def that \<open>S 0 0\<close> flip: sum_iff)

  moreover have \<open>S (infsum_in T f A) (infsum_in T' f' A')\<close> if [simp]: \<open>card L = 1\<close>
  proof -
    have [simp]: \<open>card L' = 1\<close>
      using that cardLL' by simp
    have \<open>S (the_elem L) (the_elem L')\<close>
      using \<open>rel_set S L L'\<close>
      by (metis (no_types, opaque_lifting) \<open>card L' = 1\<close> is_singleton_altdef is_singleton_the_elem rel_setD1 singleton_iff that)
    then show ?thesis
      by (simp add: infsum_in_def flip: L'_def L_def)
  qed

  ultimately show \<open>S (infsum_in T f A) (infsum_in T' f' A')\<close>
    by auto
qed

lemma infsum_parametric[transfer_rule]: 
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> (=)) ===> (rel_set R) ===> (=)) infsum infsum\<close>
  unfolding infsum_euclidean_eq[symmetric]
  by transfer_prover

lemma summable_on_transfer[transfer_rule]: 
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>((R ===> (=)) ===> (rel_set R) ===> (=)) Infinite_Sum.summable_on Infinite_Sum.summable_on\<close>
  unfolding summable_on_euclidean_eq[symmetric]
  by transfer_prover

lemma abs_gbinomial: \<open>abs (a gchoose n) = (-1)^(n - nat (ceiling a)) * (a gchoose n)\<close>
proof -
  have \<open>(\<Prod>i=0..<n. abs (a - of_nat i)) = (- 1) ^ (n - nat (ceiling a)) * (\<Prod>i=0..<n. a - of_nat i)\<close>
  proof (induction n)
    case 0
    then show ?case
      by simp
  next
    case (Suc n)
    consider (geq) \<open>of_int n \<ge> a\<close> | (lt) \<open>of_int n < a\<close>
      by fastforce
    then show ?case
    proof cases
      case geq
      from geq have \<open>abs (a - of_int n) = - (a - of_int n)\<close>
        by simp
      moreover from geq have \<open>(Suc n - nat (ceiling a)) = (n - nat (ceiling a)) + 1\<close>
        by (metis Suc_diff_le Suc_eq_plus1 ceiling_le nat_le_iff)
      ultimately show ?thesis
        apply (simp add: Suc)
        by (metis (no_types, lifting) \<open>\<bar>a - of_int (int n)\<bar> = - (a - of_int (int n))\<close> mult.assoc mult_minus_right of_int_of_nat_eq)
    next
      case lt
      from lt have \<open>abs (a - of_int n) = (a - of_int n)\<close>
        by simp
      moreover from lt have \<open>(Suc n - nat (ceiling a)) = (n - nat (ceiling a))\<close>
        by (smt (verit, ccfv_threshold) Suc_leI cancel_comm_monoid_add_class.diff_cancel diff_commute diff_diff_cancel diff_le_self less_ceiling_iff linorder_not_le order_less_le zless_nat_eq_int_zless)
      ultimately show ?thesis
        by (simp add: Suc)
    qed
  qed
  then show ?thesis
    by (simp add: gbinomial_prod_rev abs_prod)
qed

lemma gbinomial_sum_lower_abs: 
  fixes a :: \<open>'a::{floor_ceiling}\<close>
  defines \<open>a' \<equiv> nat (ceiling a)\<close>
  assumes \<open>of_nat m \<ge> a-1\<close>
  shows "(\<Sum>k\<le>m. abs (a gchoose k)) = 
                 (-1)^a' * ((-1) ^ m * (a - 1 gchoose m)) 
               - (-1)^a' * of_bool (a'>0) * ((-1) ^ (a'-1) * (a-1 gchoose (a'-1)))
               + (\<Sum>k<a'. abs (a gchoose k))"
proof -
  from assms
  have \<open>a' \<le> Suc m\<close>
    using ceiling_mono by force

  have \<open>(\<Sum>k\<le>m. abs (a gchoose k)) = (\<Sum>k=a'..m. abs (a gchoose k)) + (\<Sum>k<a'. abs (a gchoose k))\<close>
    apply (subst asm_rl[of \<open>{..m} = {a'..m} \<union> {..<a'}\<close>])
    using \<open>a' \<le> Suc m\<close> apply auto[1]
    apply (subst sum.union_disjoint)
    by auto
  also have \<open>\<dots> = (\<Sum>k=a'..m. (-1)^(k-a') * (a gchoose k)) + (\<Sum>k<a'. abs (a gchoose k))\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>x. x + _\<close>])
    apply (rule sum.cong[OF refl])
    apply (subst abs_gbinomial)
    using a'_def by blast
  also have \<open>\<dots> = (\<Sum>k=a'..m. (-1)^k * (-1)^a' * (a gchoose k)) + (\<Sum>k<a'. abs (a gchoose k))\<close>
    apply (rule arg_cong[where f=\<open>\<lambda>x. x + _\<close>])
    apply (rule sum.cong[OF refl])
    by (simp add: power_diff_conv_inverse)
  also have \<open>\<dots> = (-1)^a' * (\<Sum>k=a'..m. (a gchoose k) * (-1)^k) + (\<Sum>k<a'. abs (a gchoose k))\<close>
    by (auto intro: sum.cong simp: sum_distrib_left)
  also have \<open>\<dots> = (-1)^a' * (\<Sum>k\<le>m. (a gchoose k) * (-1)^k) - (-1)^a' * (\<Sum>k<a'. (a gchoose k) * (-1)^k) + (\<Sum>k<a'. abs (a gchoose k))\<close>
    apply (subst asm_rl[of \<open>{..m} = {..<a'} \<union> {a'..m}\<close>])
    using \<open>a' \<le> Suc m\<close> apply auto[1]
    apply (subst sum.union_disjoint)
    by (auto simp: distrib_left)
  also have \<open>\<dots> = (-1)^a' * ((- 1) ^ m * (a - 1 gchoose m)) - (-1)^a' * (\<Sum>k<a'. (a gchoose k) * (-1)^k) + (\<Sum>k<a'. abs (a gchoose k))\<close>
    apply (subst gbinomial_sum_lower_neg)
    by simp
  also have \<open>\<dots> = (-1)^a' * ((-1) ^ m * (a - 1 gchoose m)) - (-1)^a' 
               * of_bool (a'>0) * ((-1) ^ (a'-1) * (a-1 gchoose (a'-1)))
               + (\<Sum>k<a'. abs (a gchoose k))\<close>
    apply (cases \<open>a' = 0\<close>)
    subgoal
      by simp
    subgoal
      by (subst asm_rl[of \<open>{..<a'} = {..a'-1}\<close>]) (auto simp: gbinomial_sum_lower_neg)
    done
  finally show ?thesis
    by -
qed

lemma abs_gbinomial_leq1:
  fixes a :: \<open>'a :: {linordered_field}\<close>
  assumes \<open>abs a \<le> 1\<close>
  shows \<open>abs (a gchoose b) \<le> 1\<close>
proof -
  have *: \<open>-1 \<le> a\<close> \<open>a \<le> 1\<close>
    using abs_le_D2 assms minus_le_iff abs_le_iff assms by auto
  have \<open>abs (a gchoose b) = abs ((\<Prod>i = 0..<b. a - of_nat i) / fact b)\<close>
    by (simp add: gbinomial_prod_rev)
  also have \<open>\<dots> = abs ((\<Prod>i=0..<b. a - of_nat i)) / fact b\<close>
    apply (subst abs_divide)
    by simp
  also have \<open>\<dots> = (\<Prod>i=0..<b. abs (a - of_nat i)) / fact b\<close>
    apply (subst abs_prod) by simp
  also have \<open>\<dots> \<le> (\<Prod>i=0..<b. of_nat (Suc i)) / fact b\<close>
  proof (intro divide_right_mono prod_mono conjI)
    fix i assume "i \<in> {0..<b}"
    have "\<bar>a - of_nat i\<bar> \<le> \<bar>a\<bar> + \<bar>of_nat i\<bar>"
      by linarith
    also have "\<bar>a\<bar> \<le> 1"
      by fact
    finally show "\<bar>a - of_nat i\<bar> \<le> of_nat (Suc i)"
      by simp
  qed auto
  also have \<open>\<dots> = fact b / fact b\<close>
    by (subst (2) fact_prod_Suc) auto
  also have \<open>\<dots> = 1\<close>
    by simp
  finally show ?thesis
    by -
qed

lemma gbinomial_summable_abs:
  fixes a :: real
  assumes \<open>a \<ge> 0\<close> and \<open>a \<le> 1\<close>
  shows \<open>summable (\<lambda>n. abs (a gchoose n))\<close>
proof -
  define a' where \<open>a' = nat (ceiling a)\<close>
  have a': \<open>a' = 0 \<or> a' = 1\<close>
    by (metis One_nat_def a'_def assms(2) ceiling_le_one less_one nat_1 nat_mono order_le_less)
  have aux1: \<open>abs x \<le> x' \<Longrightarrow> abs y \<le> y' \<Longrightarrow> abs z \<le> z' \<Longrightarrow> x - y + z \<le> x' + y' + z'\<close> for x y z x' y' z' :: real
    by auto
  have \<open>(\<Sum>i\<le>n. \<bar>a gchoose i\<bar>) = (- 1) ^ a' * ((- 1) ^ n * (a - 1 gchoose n)) -
    (- 1) ^ a' * of_bool (0 < a') * ((- 1) ^ (a' - 1) * (a - 1 gchoose (a' - 1))) +
    (\<Sum>k<a'. \<bar>a gchoose k\<bar>)\<close> for n
    unfolding a'_def  by (rule gbinomial_sum_lower_abs) (use assms in auto)
  also have \<open>\<dots>n \<le> 1 + 1 + 1\<close> for n
    by (rule aux1) (use a' in \<open>auto simp add: abs_mult abs_gbinomial_leq1 assms\<close>)
  also have \<open>\<dots> = 3\<close>
    by simp
  finally show ?thesis
    by (meson abs_ge_zero bounded_imp_summable)
qed

lemma summable_tendsto_times_n:
  fixes f :: \<open>nat \<Rightarrow> real\<close>
  assumes pos: \<open>\<And>n. f n \<ge> 0\<close>
  assumes dec: \<open>decseq (\<lambda>n. (n+M) * f (n + M))\<close>
  assumes sum: \<open>summable f\<close>
  shows \<open>(\<lambda>n. n * f n) \<longlonglongrightarrow> 0\<close>
proof (rule ccontr)
  assume lim_not_0: \<open>\<not> (\<lambda>n. n * f n) \<longlonglongrightarrow> 0\<close>
  obtain B where \<open>(\<lambda>n. (n+M) * f (n+M)) \<longlonglongrightarrow> B\<close> and nfB': \<open>(n+M) * f (n+M) \<ge> B\<close> for n
    apply (rule decseq_convergent[where B=0, OF dec])
    using pos that by auto
  then have lim_B: \<open>(\<lambda>n. n * f n) \<longlonglongrightarrow> B\<close>
    by - (rule LIMSEQ_offset)
  have \<open>B \<ge> 0\<close>
    apply (subgoal_tac \<open>\<And>n. n * f n \<ge> 0\<close>)
    using Lim_bounded2 lim_B apply blast
    by (simp add: pos)
  moreover have \<open>B \<noteq> 0\<close>
    using lim_B lim_not_0 by blast
  ultimately have \<open>B > 0\<close>
    by linarith

  have ge: \<open>f n \<ge> B / n\<close> if \<open>n \<ge> M\<close> for n
    using nfB'[of \<open>n-M\<close>] that \<open>B > 0\<close>  by (auto simp: divide_simps mult_ac)

  have \<open>summable (\<lambda>n. B / n)\<close>
    by (rule summable_comparison_test'[where N=M]) (use sum \<open>B > 0\<close> ge in auto)

  moreover have \<open>\<not> summable (\<lambda>n. B / n)\<close>
  proof (rule ccontr)
    define C where \<open>C = (\<Sum>n. 1 / real n)\<close>
    assume \<open>\<not> \<not> summable (\<lambda>n. B / real n)\<close>
    then have \<open>summable (\<lambda>n. inverse B * (B / real n))\<close>
      using summable_mult by blast
    then have \<open>summable (\<lambda>n. 1 / real n)\<close>
      using \<open>B \<noteq> 0\<close> by auto
    then have \<open>(\<Sum>n=1..m. 1 / real n) \<le> C\<close> for m
      unfolding C_def by (rule sum_le_suminf) auto
    then have \<open>harm m \<le> C\<close> for m
      by (simp add: harm_def inverse_eq_divide)
    then have \<open>harm (nat (ceiling (exp C))) \<le> C\<close>
      by -
    then have \<open>ln (real (nat (ceiling (exp C))) + 1) \<le> C\<close>
      by (smt (verit, best) ln_le_harm)
    then show False
      by (smt (z3) exp_ln ln_ge_iff of_nat_0_le_iff real_nat_ceiling_ge)
  qed

  ultimately show False
    by simp
qed
  


lemma gbinomial_tendsto_0:
  fixes a :: real
  assumes \<open>a > -1\<close>
  shows \<open>(\<lambda>n. (a gchoose n)) \<longlonglongrightarrow> 0\<close>
proof -
  have thesis1: \<open>(\<lambda>n. (a gchoose n)) \<longlonglongrightarrow> 0\<close> if \<open>a \<ge> 0\<close> for a :: real
  proof -
    define m where \<open>m = nat (floor a)\<close>
    have m: \<open>a \<ge> real m\<close> \<open>a \<le> real m + 1\<close>
      by (simp_all add: m_def that)
    show ?thesis
    proof (insert m, induction m arbitrary: a)
      case 0
      then have *: \<open>a \<ge> 0\<close> \<open>a \<le> 1\<close>
        using assms by auto
      show ?case
        using gbinomial_summable_abs[OF *]
        using summable_LIMSEQ_zero tendsto_rabs_zero_iff by blast
    next
      case (Suc m)
      have 1: \<open>(\<lambda>n. (a-1 gchoose n)) \<longlonglongrightarrow> 0\<close>
        by (rule Suc.IH) (use Suc.prems in auto)
      then have \<open>(\<lambda>n. (a-1 gchoose Suc n)) \<longlonglongrightarrow> 0\<close>
        using filterlim_sequentially_Suc by blast
      with 1 have \<open>(\<lambda>n. (a-1 gchoose n) + (a-1 gchoose Suc n)) \<longlonglongrightarrow> 0\<close>
        by (simp add: tendsto_add_zero)
      then have \<open>(\<lambda>n. (a gchoose Suc n)) \<longlonglongrightarrow> 0\<close>
        using gbinomial_Suc_Suc[of \<open>a-1\<close>] by simp
      then show ?case
        using filterlim_sequentially_Suc by blast
    qed
  qed

  have thesis2: \<open>(\<lambda>n. (a gchoose n)) \<longlonglongrightarrow> 0\<close> if \<open>a > -1\<close> \<open>a \<le> 0\<close>
  proof -
    have decseq: \<open>decseq (\<lambda>n. abs (a gchoose n))\<close>
    proof (rule decseq_SucI)
      fix n
      have \<open>\<bar>a gchoose Suc n\<bar> = \<bar>a gchoose n\<bar> * (\<bar>a - real n\<bar> / (1 + n))\<close>
        unfolding gbinomial_prod_rev by (simp add: abs_mult) 
      also have \<open>\<dots> \<le> \<bar>a gchoose n\<bar>\<close>
        apply (rule mult_left_le)
        using assms that(2) by auto
      finally show \<open>\<bar>a gchoose Suc n\<bar> \<le> \<bar>a gchoose n\<bar>\<close>
        by -
    qed
    have abs_a1: \<open>abs (a+1) = a+1\<close>
      using assms by auto

    have \<open>0 \<le> \<bar>a + 1 gchoose n\<bar>\<close> for n
      by simp
    moreover have \<open>decseq (\<lambda>n. (n+1) * abs (a+1 gchoose (n+1)))\<close>
      using decseq apply (simp add: gbinomial_rec abs_mult)
      by (smt (verit, best) decseq_def mult.commute mult_left_mono)
    moreover have \<open>summable (\<lambda>n. abs (a+1 gchoose n))\<close>
      apply (rule gbinomial_summable_abs)
      using that by auto
    ultimately have \<open>(\<lambda>n. n * abs (a+1 gchoose n)) \<longlonglongrightarrow> 0\<close>
      by (rule summable_tendsto_times_n)
    then have \<open>(\<lambda>n. Suc n * abs (a+1 gchoose Suc n)) \<longlonglongrightarrow> 0\<close>
      by (rule_tac LIMSEQ_ignore_initial_segment[where k=1 and a=0, simplified])
    then have \<open>(\<lambda>n. abs (Suc n * (a+1 gchoose Suc n))) \<longlonglongrightarrow> 0\<close>
      by (simp add: abs_mult)
    then have \<open>(\<lambda>n. (a+1) * abs (a gchoose n)) \<longlonglongrightarrow> 0\<close>
      apply (subst (asm) gbinomial_absorption)
      by (simp add: abs_mult abs_a1)
    then have \<open>(\<lambda>n. abs (a gchoose n)) \<longlonglongrightarrow> 0\<close>
      using that(1) by force
    then show \<open>(\<lambda>n. (a gchoose n)) \<longlonglongrightarrow> 0\<close>
      by (rule tendsto_rabs_zero_cancel)
  qed

  from thesis1 thesis2 assms show ?thesis
    using linorder_linear by blast
qed


(* lemma gbinomial_minus1[simp]: \<open>(-1 gchoose n) = (case n of 0 \<Rightarrow> 1 | _ \<Rightarrow> -1)\<close>
  apply (cases n)
   apply auto
  unfolding gbinomial_prod_rev
  apply auto
  by auto *)

lemma gbinomial_abs_sum:
  fixes a :: real
  assumes \<open>a > 0\<close> and \<open>a \<le> 1\<close>
  shows \<open>(\<lambda>n. abs (a gchoose n)) sums 2\<close>
proof -
  define a' where \<open>a' = nat (ceiling a)\<close>
  have \<open>a' = 1\<close>
    using a'_def assms(1) assms(2) by linarith
  have lim: \<open>(\<lambda>n. (a - 1 gchoose n)) \<longlonglongrightarrow> 0\<close>
    by (simp add: assms(1) gbinomial_tendsto_0)
  have \<open>(\<Sum>k\<le>n. abs (a gchoose k)) = (- 1) ^ a' * ((- 1) ^ n * (a - 1 gchoose n)) -
    (- 1) ^ a' * of_bool (0 < a') * ((- 1) ^ (a'-1) * (a - 1 gchoose (a' - 1))) +
    (\<Sum>k<a'. \<bar>a gchoose k\<bar>)\<close> for n
    unfolding a'_def
    apply (rule gbinomial_sum_lower_abs)
    using assms(2) by linarith
  also have \<open>\<dots>n = 2 - (- 1) ^ n * (a - 1 gchoose n)\<close> for n
    using assms
    by (auto simp add: \<open>a' = 1\<close>)
  finally have \<open>(\<Sum>k\<le>n. abs (a gchoose k)) = 2 - (- 1) ^ n * (a - 1 gchoose n)\<close> for n
    by -
  moreover have \<open>(\<lambda>n. 2 - (- 1) ^ n * (a - 1 gchoose n)) \<longlonglongrightarrow> 2\<close>
  proof -
    have \<open>(\<lambda>n. ((-1) ^ n * (a-1 gchoose n))) \<longlonglongrightarrow> 0\<close>
      by (rule tendsto_rabs_zero_cancel) (use lim in \<open>simp add: abs_mult tendsto_rabs_zero_iff\<close>)
    then have \<open>(\<lambda>n. 2 - (- 1) ^ n * (a - 1 gchoose n)) \<longlonglongrightarrow> 2 - 0\<close>
      by (rule tendsto_diff[rotated]) simp
    then show ?thesis
      by simp
  qed
  ultimately have \<open>(\<lambda>n. \<Sum>k\<le>n. abs (a gchoose k)) \<longlonglongrightarrow> 2\<close>
    by auto
  then show ?thesis
    using sums_def_le by blast
qed

lemma sums_has_sum:
  fixes s :: \<open>'a :: banach\<close>
  assumes sums: \<open>f sums s\<close>
  assumes abs_sum: \<open>summable (\<lambda>n. norm (f n))\<close>
  shows \<open>(f has_sum s) UNIV\<close>
proof (rule has_sumI_metric)
  fix e :: real assume \<open>0 < e\<close>
  define e' where \<open>e' = e/2\<close>
  then have \<open>e' > 0\<close>
    using \<open>0 < e\<close> half_gt_zero by blast
  from suminf_exist_split[where r=e', OF \<open>0<e'\<close> abs_sum]
  obtain N where \<open>norm (\<Sum>i. norm (f (i + N))) < e'\<close>
    by auto
  then have N: \<open>(\<Sum>i. norm (f (i + N))) < e'\<close>
    by auto
  then have N': \<open>norm (\<Sum>i. f (i + N)) < e'\<close>
    apply (rule dual_order.strict_trans2)
    by (auto intro!: summable_norm summable_iff_shift[THEN iffD2] abs_sum)

  define X where \<open>X = {..<N}\<close>
  then have \<open>finite X\<close>
    by auto
  moreover have \<open>dist (sum f Y) s < e\<close> if \<open>finite Y\<close> and \<open>X \<subseteq> Y\<close> for Y
  proof -
    have \<open>dist (sum f Y) s = norm (s - sum f {..<N} - sum f (Y-{..<N}))\<close>
      by (metis X_def diff_diff_eq2 dist_norm norm_minus_commute sum.subset_diff that(1) that(2))
    also have \<open>\<dots> \<le> norm (s - sum f {..<N}) + norm (sum f (Y-{..<N}))\<close>
      using norm_triangle_ineq4 by blast
    also have \<open>\<dots> = norm (\<Sum>i. f (i + N)) + norm (sum f (Y-{..<N}))\<close>
      apply (subst suminf_minus_initial_segment)
      using sums sums_summable apply blast
      using sums sums_unique by blast
    also have \<open>\<dots> < e' + norm (sum f (Y-{..<N}))\<close>
      using N' by simp
    also have \<open>\<dots> \<le> e' + norm (\<Sum>i\<in>Y-{..<N}. norm (f i))\<close>
      apply (rule add_left_mono)
      by (smt (verit, best) real_norm_def sum_norm_le)
    also have \<open>\<dots> \<le> e' + (\<Sum>i\<in>Y-{..<N}. norm (f i))\<close>
      apply (rule add_left_mono)
      by (simp add: sum_nonneg)
    also have "(\<Sum>i\<in>Y-{..<N}. norm (f i)) = (\<Sum>i|i+N\<in>Y. norm (f (i + N)))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>i. i + N" "\<lambda>i. i - N"]) auto
    also have \<open>e' + \<dots> \<le> e' + (\<Sum>i. norm (f (i + N)))\<close>
      by (auto intro!: add_left_mono sum_le_suminf summable_iff_shift[THEN iffD2] abs_sum finite_inverse_image \<open>finite Y\<close>)
    also have \<open>\<dots> \<le> e' + e'\<close>
      using N by simp
    also have \<open>\<dots> = e\<close>
      by (simp add: e'_def)
    finally show ?thesis
      by -
  qed
  ultimately show \<open>\<exists>X. finite X \<and> X \<subseteq> UNIV \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> UNIV \<longrightarrow> dist (sum f Y) s < e)\<close>
    by auto
qed

lemma sums_has_sum_pos:
  fixes s :: real
  assumes \<open>f sums s\<close>
  assumes \<open>\<And>n. f n \<ge> 0\<close>
  shows \<open>(f has_sum s) UNIV\<close>
  apply (rule sums_has_sum)
  apply (simp add: assms(1))
  using assms(1) assms(2) summable_def by auto

lemma gbinomial_abs_has_sum:
  fixes a :: real
  assumes \<open>a > 0\<close> and \<open>a \<le> 1\<close>
  shows \<open>((\<lambda>n. abs (a gchoose n)) has_sum 2) UNIV\<close>
  apply (rule sums_has_sum_pos)
   apply (rule gbinomial_abs_sum)
  using assms by auto

lemma gbinomial_abs_has_sum_1:
  fixes a :: real
  assumes \<open>a > 0\<close> and \<open>a \<le> 1\<close>
  shows \<open>((\<lambda>n. abs (a gchoose n)) has_sum 1) (UNIV-{0})\<close>
proof -
  have \<open>((\<lambda>n. abs (a gchoose n)) has_sum 2-(\<Sum>n\<in>{0}. abs (a gchoose n))) (UNIV-{0})\<close>
    apply (rule has_sum_Diff)
      apply (rule gbinomial_abs_has_sum)
    using assms apply auto[2]
     apply (rule has_sum_finite)
    by auto
  then show ?thesis
    by simp
qed

lemma gbinomial_abs_summable:
  fixes a :: real
  assumes \<open>a > 0\<close> and \<open>a \<le> 1\<close>
  shows \<open>(\<lambda>n. (a gchoose n)) abs_summable_on UNIV\<close>
  using assms by (auto intro!: has_sum_imp_summable gbinomial_abs_has_sum)

lemma gbinomial_abs_summable_1:
  fixes a :: real
  assumes \<open>a > 0\<close> and \<open>a \<le> 1\<close>
  shows \<open>(\<lambda>n. (a gchoose n)) abs_summable_on UNIV-{0}\<close>
  using assms by (auto intro!: has_sum_imp_summable gbinomial_abs_has_sum_1)

lemma has_sum_singleton[simp]: \<open>(f has_sum y) {x} \<longleftrightarrow> f x = y\<close> for y :: \<open>'a :: {comm_monoid_add, t2_space}\<close>
  using has_sum_finite[of \<open>{x}\<close>] infsumI[of f "{x}" y] by auto


lemma has_sum_sums: \<open>f sums s\<close> if \<open>(f has_sum s) UNIV\<close>
proof -
  have \<open>(\<lambda>n. sum f {..<n}) \<longlonglongrightarrow> s\<close>
  proof (unfold tendsto_def, intro allI impI)
    fix S assume \<open>open S\<close> and \<open>s \<in> S\<close>
    with \<open>(f has_sum s) UNIV\<close>
    have \<open>\<forall>\<^sub>F F in finite_subsets_at_top UNIV. sum f F \<in> S\<close>
      using has_sum_def tendsto_def by blast
    then
    show \<open>\<forall>\<^sub>F x in sequentially. sum f {..<x} \<in> S\<close>
      using eventually_compose_filterlim filterlim_lessThan_at_top by blast
  qed
  then show ?thesis
    by (simp add: sums_def)
qed

lemma The_eqI1:
  assumes \<open>\<And>x y. F x \<Longrightarrow> F y \<Longrightarrow> x = y\<close>
  assumes \<open>\<exists>z. F z\<close>
  assumes \<open>\<And>x. F x \<Longrightarrow> P x = Q x\<close>
  shows \<open>P (The F) = Q (The F)\<close>
  by (metis assms(1) assms(2) assms(3) theI)

lemma summable_on_uminus[intro!]: 
  fixes f :: \<open>'a \<Rightarrow> 'b :: real_normed_vector\<close> (* Can probably be shown for a much wider type class. *)
  assumes \<open>f summable_on A\<close>
  shows \<open>(\<lambda>i. - f i) summable_on A\<close>
  apply (subst asm_rl[of \<open>(\<lambda>i. - f i) = (\<lambda>i. (-1) *\<^sub>R f i)\<close>])
   apply simp
  using assms by (rule summable_on_scaleR_right)

lemma summable_on_diff:
  fixes f g :: "'a \<Rightarrow> 'b::real_normed_vector"  (* Can probably be shown for a much wider type class. *)
  assumes \<open>f summable_on A\<close>
  assumes \<open>g summable_on A\<close>
  shows \<open>(\<lambda>x. f x - g x) summable_on A\<close>
  using summable_on_add[where f=f and g=\<open>\<lambda>x. - g x\<close>] summable_on_uminus[where f=g]
  using assms by auto


lemma gbinomial_1: \<open>(1 gchoose n) = of_bool (n\<le>1)\<close>
proof -
  consider (0) \<open>n=0\<close> | (1) \<open>n=1\<close> | (bigger) m where \<open>n=Suc (Suc m)\<close>
    by (metis One_nat_def not0_implies_Suc)
  then show ?thesis
  proof cases
    case 0
    then show ?thesis
      by simp
  next
    case 1
    then show ?thesis
      by simp
  next
    case bigger
    then show ?thesis
      using gbinomial_rec[where a=0 and k=\<open>Suc m\<close>]
      by simp
  qed
qed



lemma gbinomial_a_Suc_n:
  \<open>(a gchoose Suc n) = (a gchoose n) * (a-n) / Suc n\<close>
  by (simp add: gbinomial_prod_rev)

lemma has_sum_in_0[simp]:
  assumes \<open>0 \<in> topspace T\<close>
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x = 0\<close>
  shows \<open>has_sum_in T f A 0\<close>
proof -
  have \<open>has_sum_in T (\<lambda>_. 0) A 0\<close>
    using assms
    by (simp add: has_sum_in_def sum.neutral_const[abs_def])
  then show ?thesis
    apply (rule has_sum_in_cong[THEN iffD2, rotated])
    using assms by simp
qed

lemma has_sum_diff:
  fixes f g :: "'a \<Rightarrow> 'b::{topological_ab_group_add}"
  assumes \<open>(f has_sum a) A\<close>
  assumes \<open>(g has_sum b) A\<close>
  shows \<open>((\<lambda>x. f x - g x) has_sum (a - b)) A\<close>
  by (auto intro!: has_sum_add has_sum_uminus[THEN iffD2] assms simp add: simp flip: add_uminus_conv_diff)

lemma has_sum_of_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes \<open>(f has_sum a) A\<close>
  shows \<open>((\<lambda>x. of_real (f x)) has_sum (of_real a :: 'b::{real_algebra_1,real_normed_vector})) A\<close>
  apply (rule has_sum_comm_additive[unfolded o_def, where f=of_real])
  by (auto intro!: additive.intro assms tendsto_of_real)

lemma summable_on_cdivide:
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space, topological_semigroup_mult, division_ring}"
  assumes \<open>f summable_on A\<close>
  shows "(\<lambda>x. f x / c) summable_on A"
  apply (subst division_ring_class.divide_inverse)
  using assms summable_on_cmult_left by blast

lemma norm_abs[simp]: \<open>norm (abs x) = norm x\<close> for x :: \<open>'a :: {idom_abs_sgn, real_normed_div_algebra}\<close>
proof -
  have \<open>norm x = norm (sgn x * abs x)\<close>
    by (simp add: sgn_mult_abs)
  also have \<open>\<dots> = norm \<bar>x\<bar>\<close>
    by (simp add: norm_mult norm_sgn)
  finally show ?thesis
    by simp
qed

(* Strengthening of  *) thm abs_summable_product (* with narrower typeclass *)
lemma abs_summable_product:
  fixes x :: "'a \<Rightarrow> 'b::real_normed_div_algebra"
  assumes x2_sum: "(\<lambda>i. (x i)\<^sup>2) abs_summable_on A"
    and y2_sum: "(\<lambda>i. (y i)\<^sup>2) abs_summable_on A"
  shows "(\<lambda>i. x i * y i) abs_summable_on A"
proof (rule nonneg_bdd_above_summable_on)
  show \<open>0 \<le> norm (x i * y i)\<close> for i
    by simp
  show \<open>bdd_above (sum (\<lambda>i. norm (x i * y i)) ` {F. F \<subseteq> A \<and> finite F})\<close>
  proof (rule bdd_aboveI2, rename_tac F)
    fix F assume \<open>F \<in> {F. F \<subseteq> A \<and> finite F}\<close>
    then have "finite F" and "F \<subseteq> A"
      by auto

    have "norm (x i * y i) \<le> norm (x i * x i) + norm (y i * y i)" for i
      unfolding norm_mult
      by (smt mult_left_mono mult_nonneg_nonneg mult_right_mono norm_ge_zero)
    hence "(\<Sum>i\<in>F. norm (x i * y i)) \<le> (\<Sum>i\<in>F. norm ((x i)\<^sup>2) + norm ((y i)\<^sup>2))"
      using [[simp_trace]]
      by (simp add: power2_eq_square sum_mono)
    also have "\<dots> = (\<Sum>i\<in>F. norm ((x i)\<^sup>2)) + (\<Sum>i\<in>F. norm ((y i)\<^sup>2))"
      by (simp add: sum.distrib)
    also have "\<dots> \<le> (\<Sum>\<^sub>\<infinity>i\<in>A. norm ((x i)\<^sup>2)) + (\<Sum>\<^sub>\<infinity>i\<in>A. norm ((y i)\<^sup>2))"
      using x2_sum y2_sum \<open>finite F\<close> \<open>F \<subseteq> A\<close> by (auto intro!: finite_sum_le_infsum add_mono)
    finally show \<open>(\<Sum>xa\<in>F. norm (x xa * y xa)) \<le> (\<Sum>\<^sub>\<infinity>i\<in>A. norm ((x i)\<^sup>2)) + (\<Sum>\<^sub>\<infinity>i\<in>A. norm ((y i)\<^sup>2))\<close>
      by simp
  qed
qed

lemma Cauchy_Schwarz_ineq_infsum:
  fixes x :: "'a \<Rightarrow> 'b::{real_normed_div_algebra}"
  assumes x2_sum: "(\<lambda>i. (x i)\<^sup>2) abs_summable_on A"
    and y2_sum: "(\<lambda>i. (y i)\<^sup>2) abs_summable_on A"
  shows \<open>(\<Sum>\<^sub>\<infinity>i\<in>A. norm (x i * y i)) \<le> sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (x i))\<^sup>2) * sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (y i))\<^sup>2)\<close>
proof -
  (* have \<open>(norm (\<Sum>\<^sub>\<infinity>i\<in>A. x i * y i)) \<le> (\<Sum>\<^sub>\<infinity>i\<in>A. norm (x i * y i))\<close>
    by (simp add: Misc_Tensor_Product.abs_summable_product assms(2) norm_infsum_bound x2_sum)
  also *) have \<open>(\<Sum>\<^sub>\<infinity>i\<in>A. norm (x i * y i)) \<le> sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (x i))\<^sup>2) * sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (y i))\<^sup>2)\<close>
  proof (rule infsum_le_finite_sums)
    show \<open>(\<lambda>i. x i * y i) abs_summable_on A\<close>
      using Misc_Tensor_Product.abs_summable_product x2_sum y2_sum by blast
    fix F assume \<open>finite F\<close> and \<open>F \<subseteq> A\<close>


    have sum1: \<open>(\<lambda>i. (norm (x i))\<^sup>2) summable_on A\<close>
      by (metis (mono_tags, lifting) norm_power summable_on_cong x2_sum)
    have sum2: \<open>(\<lambda>i. (norm (y i))\<^sup>2) summable_on A\<close>
      by (metis (no_types, lifting) norm_power summable_on_cong y2_sum)

    have \<open>(\<Sum>i\<in>F. norm (x i * y i))\<^sup>2 = (\<Sum>i\<in>F. norm (x i) * norm (y i))\<^sup>2\<close>
      by (simp add: norm_mult)
    also have \<open>\<dots> \<le> (\<Sum>i\<in>F. (norm (x i))\<^sup>2) * (\<Sum>i\<in>F. (norm (y i))\<^sup>2)\<close>
      using Cauchy_Schwarz_ineq_sum by fastforce
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (x i))\<^sup>2) * (\<Sum>i\<in>F. (norm (y i))\<^sup>2)\<close>
      using sum1 \<open>finite F\<close> \<open>F \<subseteq> A\<close> 
      by (auto intro!: mult_right_mono finite_sum_le_infsum sum_nonneg)
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (x i))\<^sup>2) * (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (y i))\<^sup>2)\<close>
      using sum2 \<open>finite F\<close> \<open>F \<subseteq> A\<close> 
      by (auto intro!: mult_left_mono finite_sum_le_infsum infsum_nonneg)
    also have \<open>\<dots> = (sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (x i))\<^sup>2) * sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (y i))\<^sup>2))\<^sup>2\<close>
      by (smt (verit, best) calculation real_sqrt_mult real_sqrt_pow2 zero_le_power2)
  finally show \<open>(\<Sum>i\<in>F. norm (x i * y i)) \<le> sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (x i))\<^sup>2) * sqrt (\<Sum>\<^sub>\<infinity>i\<in>A. (norm (y i))\<^sup>2)\<close>
    apply (rule power2_le_imp_le)
    by (auto intro!: mult_nonneg_nonneg infsum_nonneg)
  qed
  then show ?thesis
    by -
qed

lemma continuous_map_pullback_both:
  assumes cont: \<open>continuous_map T1 T2 g'\<close>
  assumes g'g: \<open>\<And>x. f1 x \<in> topspace T1 \<Longrightarrow> x \<in> A1 \<Longrightarrow> g' (f1 x) = f2 (g x)\<close>
  assumes top1: \<open>f1 -` topspace T1 \<inter> A1 \<subseteq> g -` A2\<close>
  shows \<open>continuous_map (pullback_topology A1 f1 T1) (pullback_topology A2 f2 T2) g\<close>
proof -
  from cont
  have \<open>continuous_map (pullback_topology A1 f1 T1) T2 (g' \<circ> f1)\<close>
    by (rule continuous_map_pullback)
  then have \<open>continuous_map (pullback_topology A1 f1 T1) T2 (f2 \<circ> g)\<close>
    apply (rule continuous_map_eq)
    by (simp add: g'g topspace_pullback_topology)
  then show ?thesis
    apply (rule continuous_map_pullback')
    by (simp add: top1 topspace_pullback_topology)
qed

lemma onorm_case_prod_plus_leq: \<open>onorm (case_prod plus :: _ \<Rightarrow> 'a::real_normed_vector) \<le> sqrt 2\<close>
  apply (rule onorm_bound)
  using norm_plus_leq_norm_prod by auto

lemma bounded_linear_case_prod_plus[simp]: \<open>bounded_linear (case_prod plus)\<close>
  apply (rule bounded_linear_intro[where K=\<open>sqrt 2\<close>])
  by (auto simp add: scaleR_right_distrib norm_plus_leq_norm_prod mult.commute)

lemma pullback_topology_twice:
  assumes \<open>(f -` B) \<inter> A = C\<close>
  shows \<open>pullback_topology A f (pullback_topology B g T) = pullback_topology C (g o f) T\<close>
proof -
  have aux: \<open>S = A \<longleftrightarrow> S = B\<close> if \<open>A = B\<close> for A B S :: 'z
    using that by simp
  have *: \<open>(\<exists>V. (openin T U \<and> V = g -` U \<inter> B) \<and> S = f -` V \<inter> A) = (openin T U \<and> S = (g \<circ> f) -` U \<inter> C)\<close> for S U
    apply (cases \<open>openin T U\<close>)
    using assms
    by (auto intro!: aux simp: vimage_comp)
  then have *: \<open>(\<exists>V. (\<exists>U. openin T U \<and> V = g -` U \<inter> B) \<and> S = f -` V \<inter> A) = (\<exists>U. openin T U \<and> S = (g \<circ> f) -` U \<inter> C)\<close> for S
    by metis
  show ?thesis
    by (auto intro!: * simp: topology_eq openin_pullback_topology)
qed

lemma pullback_topology_homeo_cong:
  assumes \<open>homeomorphic_map T S g\<close>
  assumes \<open>range f \<subseteq> topspace T\<close>
  shows \<open>pullback_topology A f T = pullback_topology A (g o f) S\<close>
proof -
  have \<open>\<exists>Us. openin S Us \<and> f -` Ut \<inter> A = (g \<circ> f) -` Us \<inter> A\<close> if \<open>openin T Ut\<close> for Ut
    apply (rule exI[of _ \<open>g ` Ut\<close>])
    using assms that apply auto
    using homeomorphic_map_openness_eq apply blast
    by (smt (verit, best) homeomorphic_map_maps homeomorphic_maps_map openin_subset rangeI subsetD)
  moreover have \<open>\<exists>Ut. openin T Ut \<and> (g \<circ> f) -` Us \<inter> A = f -` Ut \<inter> A\<close> if \<open>openin S Us\<close> for Us
    apply (rule exI[of _ \<open>(g -` Us) \<inter> topspace T\<close>])
    using assms that apply auto
    by (meson continuous_map_open homeomorphic_imp_continuous_map)
  ultimately show ?thesis
    by (auto simp: topology_eq openin_pullback_topology)
qed

definition \<open>opensets_in T = Collect (openin T)\<close>
  \<comment> \<open>This behaves more nicely with the @{method transfer}-method (and friends) than \<^const>\<open>openin\<close>.
      So when rewriting a subgoal, using, e.g., \<^term>\<open>\<exists>U\<in>opensets T. xxx\<close> instead of \<^term>\<open>\<exists>U. openin T U \<longrightarrow> xxx\<close> can make @{method transfer} work better. \<close>

lemma opensets_in_parametric[transfer_rule]:
  includes lifting_syntax
  assumes \<open>bi_unique R\<close>
  shows \<open>(rel_topology R ===> rel_set (rel_set R)) opensets_in opensets_in\<close>
proof (intro rel_funI rel_setI)
  fix S T
  assume rel_topo: \<open>rel_topology R S T\<close>
  fix U
  assume \<open>U \<in> opensets_in S\<close>
  then show \<open>\<exists>V \<in> opensets_in T. rel_set R U V\<close>
    by (smt (verit, del_insts) Domainp.cases mem_Collect_eq opensets_in_def rel_fun_def rel_topo rel_topology_def)
next
  fix S T assume rel_topo: \<open>rel_topology R S T\<close>
  fix U assume \<open>U \<in> opensets_in T\<close>
  then show \<open>\<exists>V \<in> opensets_in S. rel_set R V U\<close>
    by (smt (verit) RangepE mem_Collect_eq opensets_in_def rel_fun_def rel_topo rel_topology_def)
qed

lemma hausdorff_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>(rel_topology R ===> (\<longleftrightarrow>)) Hausdorff_space Hausdorff_space\<close>
proof -
  have Hausdorff_space_def': \<open>Hausdorff_space T \<longleftrightarrow> (\<forall>x\<in>topspace T. \<forall>y\<in>topspace T. x \<noteq> y \<longrightarrow> (\<exists>U \<in> opensets_in T. \<exists>V \<in> opensets_in T. x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}))\<close>
    for T :: \<open>'z topology\<close>
    unfolding opensets_in_def Hausdorff_space_def disjnt_def Bex_def by auto
  show ?thesis
    unfolding Hausdorff_space_def'
    by transfer_prover
qed

lemma sum_cmod_pos: 
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>(\<Sum>x\<in>A. cmod (f x)) = cmod (\<Sum>x\<in>A. f x)\<close>
  by (metis (mono_tags, lifting) Re_sum assms cmod_Re sum.cong sum_nonneg)

lemma min_power_distrib_left: \<open>(min x y) ^ n = min (x ^ n) (y ^ n)\<close> if \<open>x \<ge> 0\<close> and \<open>y \<ge> 0\<close> for x y :: \<open>_ :: linordered_semidom\<close>
  by (metis linorder_le_cases min.absorb_iff2 min.order_iff power_mono that(1) that(2))

lemma abs_summable_times: 
  fixes f :: \<open>'a \<Rightarrow> 'c::{real_normed_algebra}\<close> and g :: \<open>'b \<Rightarrow> 'c\<close>
  assumes sum_f: \<open>f abs_summable_on A\<close>
  assumes sum_g: \<open>g abs_summable_on B\<close>
  shows \<open>(\<lambda>(i,j). f i * g j) abs_summable_on A \<times> B\<close>
proof -
  have a1: \<open>(\<lambda>j. norm (f i) * norm (g j)) abs_summable_on B\<close> if \<open>i \<in> A\<close> for i
    using sum_g by (simp add: summable_on_cmult_right)
  then have a2: \<open>(\<lambda>j. f i * g j) abs_summable_on B\<close> if \<open>i \<in> A\<close> for i
    apply (rule abs_summable_on_comparison_test)
     apply (fact that)
    by (simp add: norm_mult_ineq)
  from sum_f
  have \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B. norm (f x) * norm (g y)) abs_summable_on A\<close>
    by (auto simp add: infsum_cmult_right' infsum_nonneg intro!: summable_on_cmult_left)
  then have b1: \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B. norm (f x * g y)) abs_summable_on A\<close>
    apply (rule abs_summable_on_comparison_test)
    using a1 a2 by (simp_all add: norm_mult_ineq infsum_mono infsum_nonneg)
  from a2 b1 show ?thesis
    by (intro abs_summable_on_Sigma_iff[THEN iffD2]) auto
qed


definition \<open>the_default def S = (if card S = 1 then (THE x. x \<in> S) else def)\<close>

lemma card1I:
  assumes "a \<in> A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> x = a"
  shows \<open>card A = 1\<close>
  by (metis One_nat_def assms(1) assms(2) card_eq_Suc_0_ex1)

lemma the_default_CollectI:
  assumes "P a"
    and "\<And>x. P x \<Longrightarrow> x = a"
  shows "P (the_default d (Collect P))"
proof -
  have card: \<open>card (Collect P) = 1\<close>
    apply (rule card1I)
    using assms by auto
  from assms have \<open>P (THE x. P x)\<close>
    by (rule theI)
  then show ?thesis
    by (simp add: the_default_def card)
qed


lemma the_default_singleton[simp]: \<open>the_default def {x} = x\<close>
  unfolding the_default_def by auto

lemma the_default_empty[simp]: \<open>the_default def {} = def\<close>
  unfolding the_default_def by auto

lemma the_default_The: \<open>the_default z S = (THE x. x \<in> S)\<close> if \<open>card S = 1\<close>
  by (simp add: that the_default_def)

lemma the_default_parametricity[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>(T ===> rel_set T ===> T) the_default the_default\<close>
proof (intro rel_funI, rename_tac def def' S S')
  fix def def' assume [transfer_rule]: \<open>T def def'\<close>
  fix S S' assume [transfer_rule]: \<open>rel_set T S S'\<close>
  have card_eq: \<open>card S = card S'\<close>
    by transfer_prover
  show \<open>T (the_default def S) (the_default def' S')\<close>
  proof (cases \<open>card S = 1\<close>)
    case True
    define theS theS' where [no_atp]: \<open>theS = (THE x. x \<in> S)\<close> and [no_atp]: \<open>theS' = (THE x. x \<in> S')\<close>
    from True have cardS': \<open>card S' = 1\<close>
      by (simp add: card_eq)
    have \<open>theS \<in> S\<close>
      unfolding theS_def
      by (rule theI') (use True in \<open>simp add: card_eq_Suc_0_ex1\<close>)
    moreover have \<open>theS' \<in> S'\<close>
      unfolding theS'_def
      by (rule theI') (use cardS' in \<open>simp add: card_eq_Suc_0_ex1\<close>)
    ultimately have \<open>T theS theS'\<close>
      using \<open>rel_set T S S'\<close> True cardS'
      by (auto simp: rel_set_def card_1_singleton_iff)
    then show ?thesis
      by (simp add: True cardS' the_default_def theS_def theS'_def)
  next
    case False
    then have cardS': \<open>card S' \<noteq> 1\<close>
      by (simp add: card_eq)
    show ?thesis
      using False cardS' \<open>T def def'\<close>
      by (auto simp add: the_default_def)
  qed
qed

definition \<open>rel_pred T P Q = rel_set T (Collect P) (Collect Q)\<close>

lemma Collect_parametric[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_pred T ===> rel_set T) Collect Collect\<close>
  by (auto simp: rel_pred_def)

lemma fold_graph_finite:
\<comment> \<open>Exists as @{thm [source] comp_fun_commute_on.fold_graph_finite}, but the
    \<^locale>\<open>comp_fun_commute_on\<close>-assumption is not needed.\<close>
  assumes "fold_graph f z A y"
  shows "finite A"
  using assms by induct simp_all

lemma fold_graph_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule, simp]: \<open>bi_unique T\<close>
  shows \<open>((T ===> U ===> U) ===> U ===> rel_set T ===> rel_pred U)
          fold_graph fold_graph\<close>
proof (intro rel_funI, rename_tac f f' z z' A A')
  fix f f' assume [transfer_rule, simp]: \<open>(T ===> U ===> U) f f'\<close>
  fix z z' assume [transfer_rule, simp]: \<open>U z z'\<close>
  fix A A' assume [transfer_rule, simp]: \<open>rel_set T A A'\<close>
  have one_direction: \<open>\<exists>y'. fold_graph f' z' A' y' \<and> U y y'\<close> if \<open>fold_graph f z A y\<close> 
    and [transfer_rule]: \<open>U z z'\<close> \<open>(T ===> U ===> U) f f'\<close> \<open>rel_set T A A'\<close> \<open>bi_unique T\<close>
    for f f' z z' A A' y and U :: \<open>'c1 \<Rightarrow> 'd1 \<Rightarrow> bool\<close> and T :: \<open>'a1 \<Rightarrow> 'b1 \<Rightarrow> bool\<close>
    using \<open>fold_graph f z A y\<close>  \<open>rel_set T A A'\<close>
  proof (induction arbitrary: A')
    case emptyI
    then show ?case
      by (metis \<open>U z z'\<close> empty_iff equals0I fold_graph.intros(1) rel_setD2)
  next
    case (insertI x A y)
    from insertI have foldA: \<open>fold_graph f z A y\<close> and T_xA[transfer_rule]: \<open>rel_set T (insert x A) A'\<close> and xA: \<open>x \<notin> A\<close>
      by simp_all
    define DT RT where \<open>DT = Collect (Domainp T)\<close> and \<open>RT = Collect (Rangep T)\<close>
    from T_xA have \<open>x \<in> DT\<close>
      by (metis DT_def DomainPI insertCI mem_Collect_eq rel_set_def)
    then obtain x' where [transfer_rule]: \<open>T x x'\<close>
      unfolding DT_def by blast
    have \<open>x' \<in> A'\<close>
      apply transfer by simp
    define A'' where \<open>A'' = A' - {x'}\<close>
    then have A'_def: \<open>A' = insert x' A''\<close>
      using \<open>x' \<in> A'\<close> by fastforce
    have \<open>x' \<notin> A''\<close>
      unfolding A''_def by simp
    have [transfer_rule]: \<open>rel_set T A A''\<close>
      apply (subst asm_rl[of \<open>A = (insert x A) - {x}\<close>])
      using insertI.hyps apply blast
      unfolding A''_def
      by transfer_prover
    from insertI.IH[OF this]
    obtain y'' where foldA'': \<open>fold_graph f' z' A'' y''\<close> and [transfer_rule]: \<open>U y y''\<close>
      by auto
    define y' where \<open>y' = f' x' y''\<close>
    have \<open>fold_graph f' z' A' y'\<close>
      unfolding A'_def y'_def
      using \<open>x' \<notin> A''\<close> foldA''
      by (rule fold_graph.intros)
    moreover have \<open>U (f x y) y'\<close>
      unfolding y'_def by transfer_prover
    ultimately show ?case
      by auto
  qed

  show \<open>rel_pred U (fold_graph f z A) (fold_graph f' z' A')\<close>
    unfolding rel_pred_def rel_set_def bex_simps
    apply safe
    subgoal
      by (rule one_direction[of f z A _ U z' T f']) auto
    subgoal
      by (rule one_direction[of f' z' A' _ \<open>U\<inverse>\<inverse>\<close> z \<open>T\<inverse>\<inverse>\<close> f, simplified])
         (auto simp flip: conversep_rel_fun)
    done
qed

lemma Domainp_rel_filter:
  assumes \<open>Domainp r = S\<close>
  shows \<open>Domainp (rel_filter r) F \<longleftrightarrow> (F \<le> principal (Collect S))\<close>
proof (intro iffI, elim Domainp.cases, hypsubst)
  fix G 
  assume \<open>rel_filter r F G\<close>
  then obtain Z where rZ: \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    and ZF: "map_filter_on {(x, y). r x y} fst Z = F" 
    and "map_filter_on {(x, y). r x y} snd Z = G"
    using rel_filter.simps by blast
  show \<open>F \<le> principal (Collect S)\<close>
    using rZ 
    by (auto simp flip: ZF assms intro!: filter_leI  elim!: eventually_mono
             simp: eventually_principal eventually_map_filter_on case_prod_unfold DomainPI)
next
  assume asm: \<open>F \<le> principal (Collect S)\<close>
  define Z where \<open>Z = inf (filtercomap fst F) (principal {(x, y). r x y})\<close>
  have rZ: \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
    by (simp add: Z_def eventually_inf_principal)
  moreover 
  have \<open>(\<forall>\<^sub>F x in Z. P (fst x) \<and> (case x of (x, xa) \<Rightarrow> r x xa)) = eventually P F\<close> for P
    using asm apply (auto simp add: le_principal Z_def eventually_inf_principal eventually_filtercomap)
    by (smt (verit, del_insts) DomainpE assms eventually_elim2)
  then have \<open>map_filter_on {(x, y). r x y} fst Z = F\<close>
    by (simp add: filter_eq_iff eventually_map_filter_on rZ)
  ultimately show \<open>Domainp (rel_filter r) F\<close>
    by (auto simp: Domainp_iff intro!: exI rel_filter.intros)
qed


lemma map_filter_on_cong:
  assumes [simp]: \<open>\<forall>\<^sub>F x in F. x \<in> D\<close>
  assumes \<open>\<And>x. x \<in> D \<Longrightarrow> f x = g x\<close>
  shows \<open>map_filter_on D f F = map_filter_on D g F\<close>
  apply (rule filter_eq_iff[THEN iffD2, rule_format])
  apply (simp add: eventually_map_filter_on)
  apply (rule eventually_subst)
  apply (rule always_eventually)
  using assms(2) by auto 


lemma filtermap_cong: 
  assumes \<open>\<forall>\<^sub>F x in F. f x = g x\<close>
  shows \<open>filtermap f F = filtermap g F\<close>
  apply (rule filter_eq_iff[THEN iffD2, rule_format])
  apply (simp add: eventually_filtermap)
  by (smt (verit, del_insts) assms eventually_elim2)

lemma filtermap_INF_eq: 
  assumes inj_f: \<open>inj_on f X\<close>
  assumes B_nonempty: \<open>B \<noteq> {}\<close>
  assumes F_bounded: \<open>\<And>b. b\<in>B \<Longrightarrow> F b \<le> principal X\<close>
  shows \<open>filtermap f (\<Sqinter> (F ` B)) = (\<Sqinter>b\<in>B. filtermap f (F b))\<close>
proof (rule antisym)
  show \<open>filtermap f (\<Sqinter> (F ` B)) \<le> (\<Sqinter>b\<in>B. filtermap f (F b))\<close>
    by (rule filtermap_INF)
  define f1 where \<open>f1 = inv_into X f\<close>
  have f1f: \<open>x \<in> X \<Longrightarrow> f1 (f x) = x\<close> for x
    by (simp add: inj_f f1_def)
  have ff1: \<open>x \<in> f ` X \<Longrightarrow> x = f (f1 x)\<close> for x
    by (simp add: f1_def f_inv_into_f)

  have \<open>filtermap f (F b) \<le> principal (f ` X)\<close> if \<open>b \<in> B\<close> for b
    by (metis F_bounded filtermap_mono filtermap_principal that)
  then have \<open>(\<Sqinter>b\<in>B. filtermap f (F b)) \<le> (\<Sqinter>b\<in>B. principal (f ` X))\<close>
    by (simp add: INF_greatest INF_lower2) 
  also have \<open>\<dots> = principal (f ` X)\<close>
    by (simp add: B_nonempty)
  finally have \<open>\<forall>\<^sub>F x in \<Sqinter>b\<in>B. filtermap f (F b). x \<in> f ` X\<close>
    using B_nonempty le_principal by auto
  then have *: \<open>\<forall>\<^sub>F x in \<Sqinter>b\<in>B. filtermap f (F b). x = f (f1 x)\<close>
    apply (rule eventually_mono)
    by (simp add: ff1)

  have \<open>\<forall>\<^sub>F x in F b. x \<in> X\<close> if \<open>b \<in> B\<close> for b
    using F_bounded le_principal that by blast
  then have **: \<open>\<forall>\<^sub>F x in F b. f1 (f x) = x\<close> if \<open>b \<in> B\<close> for b
    apply (rule eventually_mono)
    using that by (simp_all add: f1f)

  have \<open>(\<Sqinter>b\<in>B. filtermap f (F b)) = filtermap f (filtermap f1 (\<Sqinter>b\<in>B. filtermap f (F b)))\<close>
    apply (simp add: filtermap_filtermap)
    using * by (rule filtermap_cong[where f=id, simplified])
  also have \<open>\<dots> \<le> filtermap f (\<Sqinter>b\<in>B. filtermap f1 (filtermap f (F b)))\<close>
    apply (rule filtermap_mono)
    by (rule filtermap_INF)
  also have \<open>\<dots> = filtermap f (\<Sqinter>b\<in>B. F b)\<close>
    apply (rule arg_cong[where f=\<open>filtermap _\<close>])
    apply (rule INF_cong, rule refl)
    unfolding filtermap_filtermap
    using ** by (rule filtermap_cong[where g=id, simplified])
  finally show \<open>(\<Sqinter>b\<in>B. filtermap f (F b)) \<le> filtermap f (\<Sqinter> (F ` B))\<close>
    by -
qed

lemma filtermap_inf_eq:
  assumes \<open>inj_on f X\<close>
  assumes \<open>F1 \<le> principal X\<close>
  assumes \<open>F2 \<le> principal X\<close>
  shows \<open>filtermap f (F1 \<sqinter> F2) = filtermap f F1 \<sqinter> filtermap f F2\<close>
proof -
  have \<open>filtermap f (F1 \<sqinter> F2) = filtermap f (INF F\<in>{F1,F2}. F)\<close>
    by simp
  also have \<open>\<dots> = (INF F\<in>{F1,F2}. filtermap f F)\<close>
    apply (rule filtermap_INF_eq[where X=X])
    using assms by auto
  also have \<open>\<dots> = filtermap f F1 \<sqinter> filtermap f F2\<close>
    by simp
  finally show ?thesis
    by -
qed


definition \<open>transfer_bounded_filter_Inf B M = Inf M \<sqinter> principal B\<close>

lemma Inf_transfer_bounded_filter_Inf: \<open>Inf M = transfer_bounded_filter_Inf UNIV M\<close>
  by (metis inf_top.right_neutral top_eq_principal_UNIV transfer_bounded_filter_Inf_def)

lemma Inf_bounded_transfer_bounded_filter_Inf:
  assumes \<open>\<And>F. F \<in> M \<Longrightarrow> F \<le> principal B\<close>
  assumes \<open>M \<noteq> {}\<close>
  shows \<open>Inf M = transfer_bounded_filter_Inf B M\<close>
  by (simp add: Inf_less_eq assms(1) assms(2) inf_absorb1 transfer_bounded_filter_Inf_def)


lemma transfer_bounded_filter_Inf_parametric[transfer_rule]:
  includes lifting_syntax
  fixes r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close>
  shows \<open>(rel_set r ===> rel_set (rel_filter r) ===> rel_filter r)
     transfer_bounded_filter_Inf transfer_bounded_filter_Inf\<close>
proof (intro rel_funI, unfold transfer_bounded_filter_Inf_def)
  fix BF BG assume BFBG[transfer_rule]: \<open>rel_set r BF BG\<close>
  fix Fs Gs assume FsGs[transfer_rule]: \<open>rel_set (rel_filter r) Fs Gs\<close>
  define D R where \<open>D = Collect (Domainp r)\<close> and \<open>R = Collect (Rangep r)\<close>
  
  have \<open>rel_set r D R\<close>
     by (smt (verit) D_def Domainp_iff R_def RangePI Rangep.cases mem_Collect_eq rel_setI)
  with \<open>bi_unique r\<close>
  obtain f where \<open>R = f ` D\<close> and [simp]: \<open>inj_on f D\<close> and rf0: \<open>x\<in>D \<Longrightarrow> r x (f x)\<close> for x
    using bi_unique_rel_set_lemma
    by metis
  have rf: \<open>r x y \<longleftrightarrow> x \<in> D \<and> f x = y\<close> for x y
    apply (auto simp: rf0)
    using D_def apply auto[1]
    using D_def assms bi_uniqueDr rf0 by fastforce

  from BFBG
  have \<open>BF \<subseteq> D\<close>
     by (metis rel_setD1 rf subsetI)

  have G: \<open>G = filtermap f F\<close> if \<open>rel_filter r F G\<close> for F G
    using that proof cases
    case (1 Z)
    then have Z[simp]: \<open>\<forall>\<^sub>F (x, y) in Z. r x y\<close>
      by -
    then have \<open>filtermap f F = filtermap f (map_filter_on {(x, y). r x y} fst Z)\<close>
      using 1 by simp
    also have \<open>\<dots> = map_filter_on {(x, y). r x y} (f \<circ> fst) Z\<close>
      unfolding map_filter_on_UNIV[symmetric]
      apply (subst map_filter_on_comp)
      using Z by simp_all
    also have \<open>\<dots> = G\<close>
      apply (simp add: o_def rf)
      apply (subst map_filter_on_cong[where g=snd])
      using Z apply (rule eventually_mono)
      using 1 by (auto simp: rf)
    finally show ?thesis
      by simp
  qed

  have rf_filter: \<open>rel_filter r F G \<longleftrightarrow> F \<le> principal D \<and> filtermap f F = G\<close> for F G
    apply (intro iffI conjI)
      apply (metis D_def DomainPI Domainp_rel_filter)
    using G apply simp
    by (metis D_def Domainp_iff Domainp_rel_filter G)

  have FD: \<open>F \<le> principal D\<close> if \<open>F \<in> Fs\<close> for F
    by (meson FsGs rel_setD1 rf_filter that)

  from BFBG
  have [simp]: \<open>BG = f ` BF\<close>
    by (auto simp: rel_set_def rf)

  from FsGs
  have [simp]: \<open>Gs = filtermap f ` Fs\<close>
    using G apply (auto simp: rel_set_def rf)
    by fastforce

  show \<open>rel_filter r (\<Sqinter> Fs \<sqinter> principal BF) (\<Sqinter> Gs \<sqinter> principal BG)\<close>
  proof (cases \<open>Fs = {}\<close>)
    case True
    then have \<open>Gs = {}\<close>
      by transfer
    have \<open>rel_filter r (principal BF) (principal BG)\<close>
      by transfer_prover
    with True \<open>Gs = {}\<close> show ?thesis
      by simp
  next
    case False
    note False[simp]
    then have [simp]: \<open>Gs \<noteq> {}\<close>
      by transfer
    have \<open>rel_filter r (\<Sqinter> Fs \<sqinter> principal BF) (filtermap f (\<Sqinter> Fs \<sqinter> principal BF))\<close>
      apply (rule rf_filter[THEN iffD2])
      by (simp add: \<open>BF \<subseteq> D\<close> le_infI2)
    then show ?thesis
      using FD \<open>BF \<subseteq> D\<close>
      by (simp add: Inf_less_eq 
          flip: filtermap_inf_eq[where X=D] filtermap_INF_eq[where X=D] flip: filtermap_principal)
  qed
qed


definition \<open>transfer_inf_principal F M = F \<sqinter> principal M\<close>

lemma transfer_inf_principal_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>(rel_filter T ===> rel_set T ===> rel_filter T) transfer_inf_principal transfer_inf_principal\<close>
proof -
  have *: \<open>transfer_inf_principal F M = transfer_bounded_filter_Inf M {F}\<close> for F :: \<open>'z filter\<close> and M
    by (simp add: transfer_inf_principal_def[abs_def] transfer_bounded_filter_Inf_def)
  show ?thesis
    unfolding * 
    apply transfer_prover_start
    apply transfer_step+
    by transfer_prover
qed


lemma continuous_map_is_continuous_at_point:
  assumes \<open>continuous_map T U f\<close>
  shows \<open>filterlim f (nhdsin U (f l)) (atin T l)\<close>
  by (metis assms atin_degenerate bot.extremum continuous_map_atin filterlim_iff_le_filtercomap filterlim_nhdsin_iff_limitin)

lemma set_compr_2_image_collect: \<open>{f x y |x y. P x y} = case_prod f ` Collect (case_prod P)\<close>
  by fast

lemma closure_image_closure: \<open>continuous_on (closure S) f \<Longrightarrow> closure (f ` closure S) = closure (f ` S)\<close>
  by (smt (verit) closed_closure closure_closure closure_mono closure_subset image_closure_subset image_mono set_eq_subset)


lemma has_sum_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "((\<lambda>x. f (g x)) has_sum l) A \<longleftrightarrow> (f has_sum l) B"
proof -
  have \<open>((\<lambda>x. f (g x)) has_sum l) A \<longleftrightarrow> (f has_sum l) (g ` A)\<close>
    apply (rule has_sum_reindex[symmetric, unfolded o_def])
    using assms bij_betw_imp_inj_on by blast
  also have \<open>\<dots> \<longleftrightarrow> (f has_sum l) B\<close>
    using assms bij_betw_imp_surj_on by blast
  finally show ?thesis .
qed

lemma enum_inj:
  assumes "i < CARD('a)" and "j < CARD('a)"
  shows "(Enum.enum ! i :: 'a::enum) = Enum.enum ! j \<longleftrightarrow> i = j"
  using inj_on_nth[OF enum_distinct, where I=\<open>{..<CARD('a)}\<close>]
  using assms by (auto dest: inj_onD simp flip: card_UNIV_length_enum)

lemma closedin_vimage:
  assumes \<open>closedin U S\<close>
  assumes \<open>continuous_map T U f\<close>
  shows \<open>closedin T (topspace T \<inter> (f -` S))\<close>
  by (meson assms(1) assms(2) continuous_map_closedin_preimage_eq)

lemma join_forall: \<open>(\<forall>x. P x) \<and> (\<forall>x. Q x) \<longleftrightarrow> (\<forall>x. P x \<and> Q x)\<close>
  by auto

lemma closedin_if_converge_inside:
  fixes A :: \<open>'a set\<close>
  assumes AT: \<open>A \<subseteq> topspace T\<close>
  assumes xA: \<open>\<And>(F::'a filter) f x. F \<noteq> \<bottom> \<Longrightarrow> limitin T f x F \<Longrightarrow> range f \<subseteq> A \<Longrightarrow> x \<in> A\<close>
  shows \<open>closedin T A\<close>
proof (cases \<open>A = {}\<close>)
  case True
  then show ?thesis by simp
next
  case False
  then obtain a where \<open>a \<in> A\<close>
    by auto
  define Ac where \<open>Ac = topspace T - A\<close>
  have \<open>\<exists>U. openin T U \<and> x \<in> U \<and> U \<subseteq> Ac\<close> if \<open>x \<in> Ac\<close> for x
  proof (rule ccontr)
    assume \<open>\<nexists>U. openin T U \<and> x \<in> U \<and> U \<subseteq> Ac\<close>
    then have UA: \<open>U \<inter> A \<noteq> {}\<close> if \<open>openin T U\<close>and \<open>x \<in> U\<close> for U
      by (metis Ac_def Diff_mono Diff_triv openin_subset subset_refl that)
    have [simp]: \<open>x \<in> topspace T\<close>
      using that by (simp add: Ac_def)

    define F where \<open>F = nhdsin T x \<sqinter> principal A\<close>
    have \<open>F \<noteq> \<bottom>\<close>
      apply (subst filter_eq_iff)
      apply (auto intro!: exI[of _ \<open>\<lambda>_. False\<close>] simp: F_def eventually_inf eventually_principal
          eventually_nhdsin)
      by (meson UA disjoint_iff)

    define f where \<open>f y = (if y\<in>A then y else a)\<close> for y
    with \<open>a \<in> A\<close> have \<open>range f \<subseteq> A\<close>
      by force

    have \<open>\<forall>\<^sub>F y in F. f y \<in> U\<close> if \<open>openin T U\<close> and \<open>x \<in> U\<close> for U
    proof -
      have \<open>eventually (\<lambda>x. x \<in> U) (nhdsin T x)\<close>
        using eventually_nhdsin that by fastforce
      moreover have \<open>\<exists>R. (\<forall>x\<in>A. R x) \<and> (\<forall>x. x \<in> U \<longrightarrow> R x \<longrightarrow> f x \<in> U)\<close>
        apply (rule exI[of _ \<open>\<lambda>x. x \<in> A\<close>])
        by (simp add: f_def)
      ultimately show ?thesis
        by (auto simp add: F_def eventually_inf eventually_principal)
    qed
    then have \<open>limitin T f x F\<close>
      unfolding limitin_def by simp
    with \<open>F \<noteq> \<bottom>\<close> \<open>range f \<subseteq> A\<close> xA
    have \<open>x \<in> A\<close>
      by simp
    with that show False
      by (simp add: Ac_def)
  qed
  then have \<open>openin T Ac\<close>
    apply (rule_tac openin_subopen[THEN iffD2])
    by simp
  then show ?thesis
    by (simp add: Ac_def AT closedin_def)
qed

lemma cmod_mono: \<open>0 \<le> a \<Longrightarrow> a \<le> b \<Longrightarrow> cmod a \<le> cmod b\<close>
  by (simp add: cmod_Re less_eq_complex_def)

lemma has_sum_mono_neutral_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  have \<open>((\<lambda>x. Re (f x)) has_sum Re a) A\<close>
    using assms(1) has_sum_Re has_sum_cong by blast
  moreover have \<open>((\<lambda>x. Re (g x)) has_sum Re b) B\<close>
    using assms(2) has_sum_Re has_sum_cong by blast
  ultimately have Re: \<open>Re a \<le> Re b\<close>
    apply (rule has_sum_mono_neutral)
    using assms(3-5) by (simp_all add: less_eq_complex_def)
  have \<open>((\<lambda>x. Im (f x)) has_sum Im a) A\<close>
    using assms(1) has_sum_Im has_sum_cong by blast
  then have \<open>((\<lambda>x. Im (f x)) has_sum Im a) (A \<inter> B)\<close>
    apply (rule has_sum_cong_neutral[THEN iffD1, rotated -1])
    using assms(3-5) by (auto simp add: less_eq_complex_def)
  moreover have \<open>((\<lambda>x. Im (g x)) has_sum Im b) B\<close>
    using assms(2) has_sum_Im has_sum_cong by blast
  then have \<open>((\<lambda>x. Im (f x)) has_sum Im b) (A \<inter> B)\<close>
    apply (rule has_sum_cong_neutral[THEN iffD1, rotated -1])
    using assms(3-5) by (auto simp add: less_eq_complex_def)
  ultimately have Im: \<open>Im a = Im b\<close>
    by (rule has_sum_unique)
  from Re Im show ?thesis
    using less_eq_complexI by blast
qed

lemma choice2: \<open>\<exists>f. (\<forall>x. Q1 x (f x)) \<and> (\<forall>x. Q2 x (f x))\<close>
  if \<open>\<forall>x. \<exists>y. Q1 x y \<and> Q2 x y\<close>
  by (meson that)

lemma choice3: \<open>\<exists>f. (\<forall>x. Q1 x (f x)) \<and> (\<forall>x. Q2 x (f x)) \<and> (\<forall>x. Q3 x (f x))\<close>
  if \<open>\<forall>x. \<exists>y. Q1 x y \<and> Q2 x y \<and> Q3 x y\<close>
  by (meson that)

lemma choice4: \<open>\<exists>f. (\<forall>x. Q1 x (f x)) \<and> (\<forall>x. Q2 x (f x)) \<and> (\<forall>x. Q3 x (f x)) \<and> (\<forall>x. Q4 x (f x))\<close>
  if \<open>\<forall>x. \<exists>y. Q1 x y \<and> Q2 x y \<and> Q3 x y \<and> Q4 x y\<close>
  by (meson that)

lemma choice5: \<open>\<exists>f. (\<forall>x. Q1 x (f x)) \<and> (\<forall>x. Q2 x (f x)) \<and> (\<forall>x. Q3 x (f x)) \<and> (\<forall>x. Q4 x (f x)) \<and> (\<forall>x. Q5 x (f x))\<close>
  if \<open>\<forall>x. \<exists>y. Q1 x y \<and> Q2 x y \<and> Q3 x y \<and> Q4 x y \<and> Q5 x y\<close>
  apply (simp only: flip: all_conj_distrib)
  using that by (rule choice)

definition (in order) \<open>is_Sup X s \<longleftrightarrow> (\<forall>x\<in>X. x \<le> s) \<and> (\<forall>y. (\<forall>x\<in>X. x \<le> y) \<longrightarrow> s \<le> y)\<close>
definition (in order) \<open>has_Sup X \<longleftrightarrow> (\<exists>s. is_Sup X s)\<close>

lemma (in order) is_SupI:
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> x \<le> s\<close>
  assumes \<open>\<And>y. (\<And>x. x \<in> X \<Longrightarrow> x \<le> y) \<Longrightarrow> s \<le> y\<close>
  shows \<open>is_Sup X s\<close>
  using assms by (auto simp add: is_Sup_def)

lemma is_Sup_unique: \<open>is_Sup X a \<Longrightarrow> is_Sup X b \<Longrightarrow> a=b\<close>
  by (simp add: Orderings.order_eq_iff is_Sup_def)

lemma has_Sup_bdd_above: \<open>has_Sup X \<Longrightarrow> bdd_above X\<close>
  by (metis bdd_above.unfold has_Sup_def is_Sup_def)

lemma is_Sup_has_Sup: \<open>is_Sup X s \<Longrightarrow> has_Sup X\<close>
  using has_Sup_def by blast

class Sup_order = order + Sup + sup +
  assumes is_Sup_Sup: \<open>has_Sup X \<Longrightarrow> is_Sup X (Sup X)\<close>
  assumes is_Sup_sup: \<open>has_Sup {x,y} \<Longrightarrow> is_Sup {x,y} (sup x y)\<close>

lemma (in Sup_order) is_Sup_eq_Sup:
  assumes \<open>is_Sup X s\<close>
  shows \<open>s = Sup X\<close>
  by (meson assms local.dual_order.antisym local.has_Sup_def local.is_Sup_Sup local.is_Sup_def)

lemma is_Sup_cSup:
  fixes X :: \<open>'a::conditionally_complete_lattice set\<close>
  assumes \<open>bdd_above X\<close> and \<open>X \<noteq> {}\<close>
  shows \<open>is_Sup X (Sup X)\<close>
  using assms by (auto intro!: cSup_upper cSup_least simp: is_Sup_def)

lemma continuous_map_iff_preserves_convergence:
  assumes \<open>\<And>F a. a \<in> topspace T \<Longrightarrow> limitin T id a F \<Longrightarrow> limitin U f (f a) F\<close>
  shows \<open>continuous_map T U f\<close>
  apply (rule continuous_map_atin[THEN iffD2], intro ballI)
  using assms
  by (simp add: limitin_continuous_map)


lemma SMT_choices:
  \<comment> \<open>Was included as SMT.choices in Isabelle and disappeared\<close>
  "\<And>Q. \<forall>x. \<exists>y ya. Q x y ya \<Longrightarrow> \<exists>f fa. \<forall>x. Q x (f x) (fa x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb. Q x y ya yb \<Longrightarrow> \<exists>f fa fb. \<forall>x. Q x (f x) (fa x) (fb x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb yc. Q x y ya yb yc \<Longrightarrow> \<exists>f fa fb fc. \<forall>x. Q x (f x) (fa x) (fb x) (fc x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb yc yd. Q x y ya yb yc yd \<Longrightarrow>
     \<exists>f fa fb fc fd. \<forall>x. Q x (f x) (fa x) (fb x) (fc x) (fd x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb yc yd ye. Q x y ya yb yc yd ye \<Longrightarrow>
     \<exists>f fa fb fc fd fe. \<forall>x. Q x (f x) (fa x) (fb x) (fc x) (fd x) (fe x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb yc yd ye yf. Q x y ya yb yc yd ye yf \<Longrightarrow>
     \<exists>f fa fb fc fd fe ff. \<forall>x. Q x (f x) (fa x) (fb x) (fc x) (fd x) (fe x) (ff x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb yc yd ye yf yg. Q x y ya yb yc yd ye yf yg \<Longrightarrow>
     \<exists>f fa fb fc fd fe ff fg. \<forall>x. Q x (f x) (fa x) (fb x) (fc x) (fd x) (fe x) (ff x) (fg x)"
  by metis+


lemma closedin_pullback_topology:
  "closedin (pullback_topology A f T) S \<longleftrightarrow> (\<exists>C. closedin T C \<and> S = f-`C \<inter> A)"
proof (rule iffI)
  define TT PT where \<open>TT = topspace T\<close> and \<open>PT = topspace (pullback_topology A f T)\<close>
  assume closed: \<open>closedin (pullback_topology A f T) S\<close>
  then have \<open>S \<subseteq> PT\<close>
    using PT_def closedin_subset by blast
  from closed have \<open>openin (pullback_topology A f T) (PT - S)\<close>
    by (auto intro!: simp: closedin_def PT_def)
  then obtain U where \<open>openin T U\<close> and S_fUA: \<open>PT - S = f -` U \<inter> A\<close>
    by (auto simp: openin_pullback_topology)
  define C where \<open>C = TT - U\<close>
  have \<open>closedin T C\<close>
    using C_def TT_def \<open>openin T U\<close> by blast
  moreover have \<open>S = f -` C \<inter> A\<close>
    using S_fUA \<open>S \<subseteq> PT\<close>
    apply (simp only: C_def PT_def TT_def)
    by (metis Diff_Diff_Int Diff_Int_distrib2  inf.absorb_iff2 topspace_pullback_topology vimage_Diff)
  ultimately show \<open>\<exists>C. closedin T C \<and> S = f -` C \<inter> A\<close>
    by auto
next
  assume \<open>\<exists>U. closedin T U \<and> S = f -` U \<inter> A\<close>
  then show \<open>closedin (pullback_topology A f T) S\<close>
    apply (simp add: openin_pullback_topology closedin_def topspace_pullback_topology)
    by blast
qed


lemma regular_space_pullback[intro]:
  assumes \<open>regular_space T\<close>
  shows \<open>regular_space (pullback_topology A f T)\<close>
proof (unfold regular_space_def, intro allI impI)
  define TT PT where \<open>TT = topspace T\<close> and \<open>PT = topspace (pullback_topology A f T)\<close>
  fix S y
  assume asm: \<open>closedin (pullback_topology A f T) S \<and> y \<in> PT - S\<close>
  from asm obtain C where \<open>closedin T C\<close> and S_fCA: \<open>S = f -` C \<inter> A\<close>
    by (auto simp: closedin_pullback_topology)
  from asm S_fCA
  have \<open>f y \<in> TT - C\<close>
    by (auto simp: PT_def TT_def topspace_pullback_topology)
  then obtain U' V' where \<open>openin T U'\<close> and \<open>openin T V'\<close> and \<open>f y \<in> U'\<close> and \<open>C \<subseteq> V'\<close> and \<open>U' \<inter> V' = {}\<close>
    by (metis TT_def \<open>closedin T C\<close> assms regular_space_def disjnt_def)
  define U V where \<open>U = f -` U' \<inter> A\<close> and \<open>V = f -` V' \<inter> A\<close>
  have \<open>openin (pullback_topology A f T) U\<close>
    using U_def \<open>openin T U'\<close> openin_pullback_topology by blast
  moreover have \<open>openin (pullback_topology A f T) V\<close>
    using V_def \<open>openin T V'\<close> openin_pullback_topology by blast
  moreover have \<open>y \<in> U\<close>
    by (metis DiffD1 Int_iff PT_def U_def \<open>f y \<in> U'\<close> asm topspace_pullback_topology vimageI)
  moreover have \<open>S \<subseteq> V\<close>
    using S_fCA V_def \<open>C \<subseteq> V'\<close> by blast
  moreover have \<open>disjnt U V\<close>
    using U_def V_def \<open>U' \<inter> V' = {}\<close> disjnt_def by blast

  ultimately show \<open>\<exists>U V. openin (pullback_topology A f T) U \<and> openin (pullback_topology A f T) V \<and> y \<in> U \<and> S \<subseteq> V \<and> disjnt U V\<close>
    apply (rule_tac exI[of _ U], rule_tac exI[of _ V])
    by auto
qed

lemma t3_space_euclidean_regular[iff]: \<open>regular_space (euclidean :: 'a::t3_space topology)\<close>
  using t3_space
  apply (simp add: regular_space_def disjnt_def)
  by fast

definition increasing_filter :: \<open>'a::order filter \<Rightarrow> bool\<close> where
  \<comment> \<open>Definition suggested by \<^cite>\<open>"increasing-filters"\<close>\<close>
  \<open>increasing_filter F \<longleftrightarrow> (\<forall>\<^sub>F x in F. \<forall>\<^sub>F y in F. y \<ge> x)\<close>

lemma increasing_filtermap:
  fixes F :: \<open>'a::order filter\<close> and f :: \<open>'a \<Rightarrow> 'b::order\<close> and X :: \<open>'a set\<close>
  assumes increasing: \<open>increasing_filter F\<close>
  assumes mono: \<open>mono_on X f\<close>
  assumes ev_X: \<open>eventually (\<lambda>x. x \<in> X) F\<close>
  shows \<open>increasing_filter (filtermap f F)\<close>
proof -
  from increasing
  have incr: \<open>\<forall>\<^sub>F x in F. \<forall>\<^sub>F y in F. x \<le> y\<close>
    apply (simp add: increasing_filter_def)
    by -
  have \<open>\<forall>\<^sub>F x in F. \<forall>\<^sub>F y in F. f x \<le> f y\<close>
  proof (rule eventually_elim2[OF ev_X incr])
    fix x
    assume \<open>x \<in> X\<close>
    assume \<open>\<forall>\<^sub>F y in F. x \<le> y\<close>
    then show \<open>\<forall>\<^sub>F y in F. f x \<le> f y\<close>
    proof (rule eventually_elim2[OF ev_X])
      fix y assume \<open>y \<in> X\<close> and \<open>x \<le> y\<close>
      with \<open>x \<in> X\<close> show \<open>f x \<le> f y\<close>
        using mono by (simp add: mono_on_def)
    qed
  qed
  then show \<open>increasing_filter (filtermap f F)\<close>
    by (simp add: increasing_filter_def eventually_filtermap)
qed

lemma increasing_finite_subsets_at_top[simp]: \<open>increasing_filter (finite_subsets_at_top X)\<close>
  apply (simp add: increasing_filter_def eventually_finite_subsets_at_top)
  by force

lemma monotone_convergence:
  \<comment> \<open>Following \<^cite>\<open>"increasing-filters"\<close>\<close>
  fixes f :: \<open>'b \<Rightarrow> 'a::{order_topology, conditionally_complete_linorder}\<close>
  assumes bounded: \<open>\<forall>\<^sub>F x in F. f x \<le> B\<close>
  assumes increasing: \<open>increasing_filter (filtermap f F)\<close>
  shows \<open>\<exists>l. (f \<longlongrightarrow> l) F\<close>
proof (cases \<open>F \<noteq> \<bottom>\<close>)
  case True
  note [simp] = True
  define S l where \<open>S x \<longleftrightarrow> (\<forall>\<^sub>F y in F. f y \<ge> x) \<and> x \<le> B\<close> 
    and \<open>l = Sup (Collect S)\<close> for x
  from bounded increasing
  have ev_S: \<open>eventually S (filtermap f F)\<close>
    by (auto intro!: eventually_conj simp: S_def[abs_def] increasing_filter_def eventually_filtermap)
  have bdd_S: \<open>bdd_above (Collect S)\<close>
    by (auto simp: S_def)
  have S_nonempty: \<open>Collect S \<noteq> {}\<close>
    using ev_S
    by (metis Collect_empty_eq_bot Set.empty_def True eventually_False filtermap_bot_iff)
  have \<open>(f \<longlongrightarrow> l) F\<close>
  proof (rule order_tendstoI; rename_tac x)
    fix x
    assume \<open>x < l\<close>
    then obtain s where \<open>S s\<close> and \<open>x < s\<close>
      using less_cSupD[OF S_nonempty] l_def
      by blast
    then 
    show \<open>\<forall>\<^sub>F y in F. x < f y\<close>
      using S_def basic_trans_rules(22) eventually_mono by force
  next
    fix x
    assume asm: \<open>l < x\<close>
    from ev_S
    show \<open>\<forall>\<^sub>F y in F. f y < x\<close>
      unfolding eventually_filtermap
      apply (rule eventually_mono)
      using asm
      by (metis bdd_S cSup_upper dual_order.strict_trans2 l_def mem_Collect_eq)
  qed
  then show \<open>\<exists>l. (f \<longlongrightarrow> l) F\<close>
    by (auto intro!: exI[of _ l] simp: filterlim_def)
next
  case False
  then show \<open>\<exists>l. (f \<longlongrightarrow> l) F\<close>
    by (auto intro!: exI)
qed


lemma monotone_convergence_complex:
  fixes f :: \<open>'b \<Rightarrow> complex\<close>
  assumes bounded: \<open>\<forall>\<^sub>F x in F. f x \<le> B\<close>
  assumes increasing: \<open>increasing_filter (filtermap f F)\<close>
  shows \<open>\<exists>l. (f \<longlongrightarrow> l) F\<close>
proof -
  have inc_re: \<open>increasing_filter (filtermap (\<lambda>x. Re (f x)) F)\<close>
    using increasing_filtermap[OF increasing, where f=Re and X=UNIV]
    by (simp add: less_eq_complex_def[abs_def] mono_def monotone_def filtermap_filtermap)
  from bounded have \<open>\<forall>\<^sub>F x in F. Re (f x) \<le> Re B\<close>
    using eventually_mono less_eq_complex_def by fastforce
  from monotone_convergence[OF this inc_re]
  obtain re where lim_re: \<open>((\<lambda>x. Re (f x)) \<longlongrightarrow> re) F\<close>
    by auto
  from bounded have \<open>\<forall>\<^sub>F x in F. Im (f x) = Im B\<close>
    by (simp add: less_eq_complex_def[abs_def] eventually_mono)
  then have lim_im: \<open>((\<lambda>x. Im (f x)) \<longlongrightarrow> Im B) F\<close>
    by (simp add: tendsto_eventually)
  from lim_re lim_im have \<open>(f \<longlongrightarrow> Complex re (Im B)) F\<close>
    by (simp add: tendsto_complex_iff)
  then show ?thesis
    by auto
qed

lemma compact_closed_subset:
  assumes \<open>compact s\<close>
  assumes \<open>closed t\<close>
  assumes \<open>t \<subseteq> s\<close>
  shows \<open>compact t\<close>
  by (metis assms(1) assms(2) assms(3) compact_Int_closed inf.absorb_iff2)

definition separable where \<open>separable S \<longleftrightarrow> (\<exists>B. countable B \<and> S \<subseteq> closure B)\<close>

lemma compact_imp_separable: \<open>separable S\<close> if \<open>compact S\<close> for S :: \<open>'a::metric_space set\<close>
proof -
  from that
  obtain K where \<open>finite (K n)\<close> and K_cover_S: \<open>S \<subseteq> (\<Union>k\<in>K n. ball k (1 / of_nat (n+1)))\<close> for n :: nat
  proof (atomize_elim, intro choice2 allI)
    fix n
    have \<open>S \<subseteq> (\<Union>k\<in>UNIV. ball k (1 / of_nat (n+1)))\<close>
      apply (auto intro!: simp: )
      by (smt (verit, del_insts) dist_eq_0_iff linordered_field_class.divide_pos_pos of_nat_less_0_iff)
    then show \<open>\<exists>K. finite K \<and> S \<subseteq> (\<Union>k\<in>K. ball k (1 / real (n + 1)))\<close>
      apply (simp add: compact_eq_Heine_Borel)
      by (meson Elementary_Metric_Spaces.open_ball compactE_image \<open>compact S\<close>)
  qed
  define B where \<open>B = (\<Union>n. K n)\<close>
  have \<open>countable B\<close>
    using B_def \<open>finite (K _)\<close> uncountable_infinite by blast
  have \<open>S \<subseteq> closure B\<close>
  proof (intro subsetI closure_approachable[THEN iffD2, rule_format])
    fix x assume \<open>x \<in> S\<close>
    fix e :: real assume \<open>e > 0\<close>
    define n :: nat where \<open>n = nat (ceiling (1/e))\<close>
    with \<open>e > 0\<close> have ne: \<open>1 / real (n+1) \<le> e\<close>
    proof -
      have \<open>1 / real (n+1) \<le> 1 / ceiling (1/e)\<close>
        by (simp add: \<open>0 < e\<close> linordered_field_class.frac_le n_def)
      also have \<open>\<dots> \<le> 1 / (1/e)\<close>
        by (smt (verit, del_insts) \<open>0 < e\<close> le_of_int_ceiling linordered_field_class.divide_pos_pos linordered_field_class.frac_le)
      also have \<open>\<dots> = e\<close>
        by simp
      finally show ?thesis
        by -
    qed
    have \<open>S \<subseteq> (\<Union>k\<in>K n. ball k (1 / of_nat (n+1)))\<close>
      using K_cover_S by presburger
    then obtain k where \<open>k \<in> K n\<close> and x_ball: \<open>x \<in> ball k (1 / of_nat (n+1))\<close>
      using \<open>x \<in> S\<close> by auto
    from \<open>k \<in> K n\<close> have \<open>k \<in> B\<close>
      using B_def by blast
    moreover from x_ball have \<open>dist k x < e\<close>
      by (smt (verit) ne mem_ball)
    ultimately show \<open>\<exists>k\<in>B. dist k x < e\<close>
      by fast
  qed
  show \<open>separable S\<close>
    using \<open>S \<subseteq> closure B\<close> \<open>countable B\<close> separable_def by blast
qed

lemma ex_norm1_not_singleton:
  shows \<open>\<exists>x::'a::{real_normed_vector, not_singleton}. norm x = 1\<close>
  apply (rule ex_norm1)
  by simp

lemma is_Sup_approx_below:
  fixes b :: \<open>'a::linordered_ab_group_add\<close>
  assumes \<open>is_Sup A b\<close>
  assumes \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>x\<in>A. b - \<epsilon> \<le> x\<close>
proof (rule ccontr)
  assume \<open>\<not> (\<exists>x\<in>A. b - \<epsilon> \<le> x)\<close>
  then have \<open>b - \<epsilon> \<ge> x\<close> if \<open>x \<in> A\<close> for x
    using that by auto
  with assms
  have \<open>b \<le> b - \<epsilon>\<close>
    by (simp add: is_Sup_def)
  with \<open>\<epsilon> > 0\<close>
  show False
    by simp
qed

lemma sums_le_complex: 
  fixes f g :: "nat \<Rightarrow> complex"
  assumes \<open>\<And>n. f n \<le> g n\<close>
  assumes \<open>f sums s\<close>
  assumes \<open>g sums t\<close>
  shows \<open>s \<le> t\<close>
proof -
  have \<open>Re (f n) \<le> Re (g n)\<close> for n
    by (simp add: Re_mono assms(1)) 
  moreover have \<open>(\<lambda>n. Re (f n)) sums Re s\<close>
    using assms(2) sums_Re by auto 
  moreover have \<open>(\<lambda>n. Re (g n)) sums Re t\<close>
    using assms(3) sums_Re by auto 
  ultimately have re: \<open>Re s \<le> Re t\<close>
    by (rule sums_le)
  have \<open>Im (f n) = Im (g n)\<close> for n
    by (simp add: assms(1) comp_Im_same) 
  moreover have \<open>(\<lambda>n. Im (f n)) sums Im s\<close>
    using assms(2) sums_Im by auto 
  moreover have \<open>(\<lambda>n. Im (g n)) sums Im t\<close>
    using assms(3) sums_Im by auto 
  ultimately have im: \<open>Im s = Im t\<close>
    using sums_unique2 by auto 
  from re im show \<open>s \<le> t\<close>
    using less_eq_complexI by auto 
qed

lemma infsum_single: 
  assumes "\<And>j. j \<noteq> i \<Longrightarrow> j\<in>A \<Longrightarrow> f j = 0"
  shows "infsum f A = (if i\<in>A then f i else 0)"
  apply (subst infsum_cong_neutral[where T=\<open>A \<inter> {i}\<close> and g=f])
  using assms by auto

lemma suminf_eqI:
  fixes x :: \<open>_::{comm_monoid_add,t2_space}\<close>
  assumes \<open>f sums x\<close>
  shows \<open>suminf f = x\<close>
  using assms
  by (auto intro!: simp: sums_iff)

lemma suminf_If_finite_set:
  fixes f :: \<open>_ \<Rightarrow> _::{comm_monoid_add,t2_space}\<close>
  assumes \<open>finite F\<close>
  shows \<open>(\<Sum>x\<in>F. f x) = (\<Sum>x. if x\<in>F then f x else 0)\<close>
  by (auto intro!: suminf_eqI[symmetric] sums_If_finite_set simp: assms)

definition separating_set :: \<open>(('a \<Rightarrow> 'b) \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool\<close> where
  \<open>separating_set P S \<longleftrightarrow> (\<forall>f g. P f \<longrightarrow> P g \<longrightarrow> (\<forall>x\<in>S. f x = g x) \<longrightarrow> f = g)\<close>

lemma separating_set_mono: \<open>S \<subseteq> T \<Longrightarrow> separating_set P S \<Longrightarrow> separating_set P T\<close>
  unfolding separating_set_def by fast

lemma separating_set_UNIV[simp]: \<open>separating_set P UNIV\<close>
  by (auto intro!: ext simp: separating_set_def)

lemma eq_from_separatingI:
  assumes \<open>separating_set P S\<close>
  assumes \<open>P f\<close> and \<open>P g\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> f x = g x\<close>
  shows \<open>f = g\<close>
  using assms by (simp add: separating_set_def)

lemma eq_from_separatingI2:
  assumes \<open>separating_set P ((\<lambda>(x,y). h x y) ` (S\<times>T))\<close>
  assumes \<open>P f\<close> and \<open>P g\<close>
  assumes \<open>\<And>x y. x \<in> S \<Longrightarrow> y \<in> T \<Longrightarrow> f (h x y) = g (h x y)\<close>
  shows \<open>f = g\<close>
  apply (rule eq_from_separatingI[OF assms(1)])
  using assms(2-4) by auto

lemma separating_setI:
  assumes \<open>\<And>f g. P f \<Longrightarrow> P g \<Longrightarrow> (\<And>x. x\<in>S \<Longrightarrow> f x = g x) \<Longrightarrow> f = g\<close>
  shows \<open>separating_set P S\<close>
  by (simp add: assms separating_set_def)


lemma tendsto_le_complex:
  fixes x y :: complex
  assumes F: "\<not> trivial_limit F"
    and x: "(f \<longlongrightarrow> x) F"
    and y: "(g \<longlongrightarrow> y) F"
    and ev: "eventually (\<lambda>x. g x \<le> f x) F"
  shows "y \<le> x"
proof (rule less_eq_complexI)
  note F
  moreover have \<open>((\<lambda>x. Re (f x)) \<longlongrightarrow> Re x) F\<close>
    by (simp add: assms tendsto_Re)
  moreover have \<open>((\<lambda>x. Re (g x)) \<longlongrightarrow> Re y) F\<close>
    by (simp add: assms tendsto_Re)
  moreover from ev have "eventually (\<lambda>x. Re (g x) \<le> Re (f x)) F"
    apply (rule eventually_mono)
    by (simp add: less_eq_complex_def)
  ultimately show \<open>Re y \<le> Re x\<close>
    by (rule tendsto_le)
next
  note F
  moreover have \<open>((\<lambda>x. Im (g x)) \<longlongrightarrow> Im y) F\<close>
    by (simp add: assms tendsto_Im)
  moreover 
  have \<open>((\<lambda>x. Im (g x)) \<longlongrightarrow> Im x) F\<close>
  proof -
    have \<open>((\<lambda>x. Im (f x)) \<longlongrightarrow> Im x) F\<close>
      by (simp add: assms tendsto_Im)
    moreover from ev have \<open>\<forall>\<^sub>F x in F. Im (f x) = Im (g x)\<close>
      apply (rule eventually_mono)
      by (simp add: less_eq_complex_def)
    ultimately show ?thesis
      by (rule Lim_transform_eventually)
  qed
  ultimately show \<open>Im y = Im x\<close>
    by (rule tendsto_unique)
qed

lemma bdd_above_mono2:
  assumes \<open>bdd_above (g ` B)\<close>
  assumes \<open>A \<subseteq> B\<close>
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows \<open>bdd_above (f ` A)\<close>
  by (smt (verit, del_insts) Set.basic_monos(7) assms(1) assms(2) assms(3) basic_trans_rules(23) bdd_above.I2 bdd_above.unfold imageI)


end
