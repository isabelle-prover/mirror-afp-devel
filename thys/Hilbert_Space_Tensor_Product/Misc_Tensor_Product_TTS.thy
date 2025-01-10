section \<open>\<open>Misc_Tensor_Product_TTS\<close> -- Miscelleanous results missing from \<^session>\<open>Complex_Bounded_Operators\<close>\<close>

text \<open>Here specifically results obtained from lifting existing results using the types to sets mechanism (\<^cite>\<open>"types-to-sets"\<close>).\<close>

theory Misc_Tensor_Product_TTS
  imports
    Complex_Bounded_Operators.Complex_Bounded_Linear_Function
    Misc_Tensor_Product
    Misc_Tensor_Product_BO
    With_Type.With_Type
begin

unbundle lattice_syntax
unbundle cblinfun_notation

subsection \<open>Retrieving axioms\<close>

attribute_setup axiom = \<open>Scan.lift Parse.name_position >> (fn name_pos => Thm.rule_attribute [] 
    (fn context => fn _ =>
       let val thy = Context.theory_of context
           val (full_name, _) = Name_Space.check context (Theory.axiom_table thy) name_pos
       in Thm.axiom thy full_name end))\<close> 
  \<open>Retrieve an axiom by name. E.g., write @{thm [source] [[axiom HOL.refl]]}.\<close>

subsection \<open>Auxiliary lemmas\<close>

named_theorems unoverload_def

locale local_typedef = fixes S ::"'b set" and s::"'s itself"
  assumes Ex_type_definition_S: "\<exists>(Rep::'s \<Rightarrow> 'b) (Abs::'b \<Rightarrow> 's). type_definition Rep Abs S"
begin
definition "Rep = fst (SOME (Rep::'s \<Rightarrow> 'b, Abs). type_definition Rep Abs S)"
definition "Abs = snd (SOME (Rep::'s \<Rightarrow> 'b, Abs). type_definition Rep Abs S)"
lemma type_definition_S: "type_definition Rep Abs S"
  unfolding Abs_def Rep_def split_beta'
  by (rule someI_ex) (use Ex_type_definition_S in auto)
lemma rep_in_S[simp]: "Rep x \<in> S"
  and rep_inverse[simp]: "Abs (Rep x) = x"
  and Abs_inverse[simp]: "y \<in> S \<Longrightarrow> Rep (Abs y) = y"
  using type_definition_S
  unfolding type_definition_def by auto
definition cr_S where "cr_S \<equiv> \<lambda>s b. s = Rep b"
lemma Domainp_cr_S[transfer_domain_rule]: "Domainp cr_S = (\<lambda>x. x \<in> S)"
  by (metis Abs_inverse Domainp.simps cr_S_def rep_in_S)
lemma right_total_cr_S[transfer_rule]: "right_total cr_S"
  by (rule typedef_right_total[OF type_definition_S cr_S_def])
lemma bi_unique_cr_S[transfer_rule]: "bi_unique cr_S"
  by (rule typedef_bi_unique[OF type_definition_S cr_S_def])
lemma left_unique_cr_S[transfer_rule]: "left_unique cr_S"
  by (rule typedef_left_unique[OF type_definition_S cr_S_def])
lemma right_unique_cr_S[transfer_rule]: "right_unique cr_S"
  by (rule typedef_right_unique[OF type_definition_S cr_S_def])
lemma cr_S_Rep[intro, simp]: "cr_S (Rep a) a" by (simp add: cr_S_def)
lemma cr_S_Abs[intro, simp]: "a\<in>S \<Longrightarrow> cr_S a (Abs a)" by (simp add: cr_S_def)
lemma UNIV_transfer[transfer_rule]: \<open>rel_set cr_S S UNIV\<close>
  using Domainp_cr_S right_total_cr_S right_total_UNIV_transfer by fastforce
end

lemma complete_space_as_set[simp]: \<open>complete (space_as_set V)\<close> for V :: \<open>_::cbanach ccsubspace\<close>
  by (simp add: complete_eq_closed)

definition \<open>transfer_ball_range A P \<longleftrightarrow> (\<forall>f. range f \<subseteq> A \<longrightarrow> P f)\<close>

lemma transfer_ball_range_parametric'[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule, simp]: \<open>right_unique T\<close> \<open>bi_total T\<close> \<open>bi_unique U\<close>
  shows \<open>(rel_set U ===> ((T ===> U) ===> (\<longrightarrow>)) ===> (\<longrightarrow>)) transfer_ball_range transfer_ball_range\<close>
proof (intro rel_funI impI, rename_tac A B P Q)
  fix A B P Q
  assume [transfer_rule]: \<open>rel_set U A B\<close>
  assume TUPQ[transfer_rule]: \<open>((T ===> U) ===> (\<longrightarrow>)) P Q\<close>
  assume \<open>transfer_ball_range A P\<close>
  then have Pf: \<open>P f\<close> if \<open>range f \<subseteq> A\<close> for f
    unfolding transfer_ball_range_def using that by auto
  have \<open>Q g\<close> if \<open>range g \<subseteq> B\<close> for g
  proof -
    from that \<open>rel_set U A B\<close>
    have \<open>Rangep (T ===> U) g\<close>
      apply (auto simp add: conversep_rel_fun Domainp_pred_fun_eq simp flip: Domainp_conversep)
      apply (simp add: Domainp_conversep)
      by (metis Rangep.simps range_subsetD rel_setD2)
    then obtain f where TUfg[transfer_rule]: \<open>(T ===> U) f g\<close>
      by blast
    from that have \<open>range f \<subseteq> A\<close>
      by transfer
    then have \<open>P f\<close>
      by (simp add: Pf)
    then show \<open>Q g\<close>
      by (metis TUfg TUPQ rel_funD)
  qed
  then show \<open>transfer_ball_range B Q\<close>
  by (simp add: transfer_ball_range_def)
qed

lemma transfer_ball_range_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule, simp]: \<open>bi_unique T\<close> \<open>bi_total T\<close> \<open>bi_unique U\<close>
  shows \<open>(rel_set U ===> ((T ===> U) ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) transfer_ball_range transfer_ball_range\<close>
proof -
  have \<open>(rel_set U ===> ((T ===> U) ===> (\<longrightarrow>)) ===> (\<longrightarrow>)) transfer_ball_range transfer_ball_range\<close>
    using assms(1) assms(2) assms(3) bi_unique_alt_def transfer_ball_range_parametric' by blast
  then have 1: \<open>(rel_set U ===> ((T ===> U) ===> (\<longleftrightarrow>)) ===> (\<longrightarrow>)) transfer_ball_range transfer_ball_range\<close>
    apply (rule rev_mp)
    apply (intro rel_fun_mono')
    by auto

  have \<open>(rel_set (U\<inverse>\<inverse>) ===> ((T\<inverse>\<inverse> ===> U\<inverse>\<inverse>) ===> (\<longrightarrow>)) ===> (\<longrightarrow>)) transfer_ball_range transfer_ball_range\<close>
    apply (rule transfer_ball_range_parametric')
    using assms(1) bi_unique_alt_def bi_unique_conversep apply blast
    by auto
  then have \<open>(rel_set U ===> ((T ===> U) ===> (\<longrightarrow>)\<inverse>\<inverse>) ===> (\<longrightarrow>)\<inverse>\<inverse>) transfer_ball_range transfer_ball_range\<close>
    apply (rule_tac conversepD[where r=\<open>(rel_set U ===> ((T ===> U) ===> (\<longrightarrow>)\<inverse>\<inverse>) ===> (\<longrightarrow>)\<inverse>\<inverse>)\<close>])
    by (simp add: conversep_rel_fun del: conversep_iff)
  then have 2: \<open>(rel_set U ===> ((T ===> U) ===> (\<longleftrightarrow>)) ===> (\<longrightarrow>)\<inverse>\<inverse>) transfer_ball_range transfer_ball_range\<close>
    apply (rule rev_mp)
    apply (intro rel_fun_mono')
    by (auto simp: rev_implies_def)

  from 1 2 show ?thesis
    apply (auto intro!: rel_funI simp: conversep_iff[abs_def])
     apply (smt (z3) rel_funE)
    by (smt (verit) rel_funE rev_implies_def)
qed

definition \<open>transfer_Times A B = A \<times> B\<close>

lemma transfer_Times_parametricity[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set T ===> rel_set U ===> rel_set (rel_prod T U)) transfer_Times transfer_Times\<close>
  by (auto intro!: rel_funI simp add: transfer_Times_def rel_set_def)


lemma csubspace_nonempty: \<open>csubspace X \<Longrightarrow> X \<noteq> {}\<close>
  using complex_vector.subspace_0 by auto


definition \<open>transfer_vimage_into f U s = (f -` U) \<inter> s\<close>

lemma transfer_vimage_into_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close> \<open>bi_unique B\<close>
  shows \<open>((A ===> B) ===> rel_set B ===> rel_set A ===> rel_set A) transfer_vimage_into transfer_vimage_into\<close>
  unfolding transfer_vimage_into_def
  apply (auto intro!: rel_funI simp: rel_set_def)
  by (metis Int_iff apply_rsp' assms bi_unique_def vimage_eq)+

(* Simplify with these theorems to (try to) change all \<open>\<forall>x. ...\<close> into \<open>\<forall>x\<in>S. ...\<close> (and similar)
  to enable automated creation of parametricity rules without `bi_total` assumptions. *)
lemma make_parametricity_proof_friendly:
  shows \<open>(\<forall>x. P \<longrightarrow> Q x) \<longleftrightarrow> (P \<longrightarrow> (\<forall>x. Q x))\<close>
    and \<open>(\<forall>x. x \<in> S \<longrightarrow> Q x) \<longleftrightarrow> (\<forall>x\<in>S. Q x)\<close>
    and \<open>(\<forall>x\<subseteq>S. R x) \<longleftrightarrow> (\<forall>x\<in>Pow S. R x)\<close>
    and \<open>{x\<in>S. Q x} = Set.filter Q S\<close>
    and \<open>{x. x \<subseteq> S \<and> R x} = Set.filter R (Pow S)\<close>
    and \<open>\<And>P. (\<forall>f. range f \<subseteq> A \<longrightarrow> P f) = transfer_ball_range A P\<close>
    and \<open>\<And>A B. A \<times> B = transfer_Times A B\<close>
    and \<open>\<And>B P. (\<exists>A\<subseteq>B. P A) \<longleftrightarrow> (\<exists>A\<in>Pow B. P A)\<close>
    and \<open>\<And>f U s. (f -` U) \<inter> s = transfer_vimage_into f U s\<close>
    and \<open>\<And>M B. \<Sqinter>M \<sqinter> principal B = transfer_bounded_filter_Inf B M\<close>
    and \<open>\<And>F M. F \<sqinter> principal M = transfer_inf_principal F M\<close>
  by (auto simp: transfer_ball_range_def transfer_Times_def transfer_vimage_into_def
      transfer_bounded_filter_Inf_def transfer_inf_principal_def)

subsection \<open>\<^class>\<open>plus\<close>\<close>

locale plus_ow =
  fixes U plus
  assumes \<open>\<forall>x\<in>U. \<forall>y\<in>U. plus x y \<in> U\<close>
lemma plus_ow_parametricity[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (A ===> A ===> A) ===> (=)) 
     plus_ow plus_ow\<close>
  unfolding plus_ow_def
  by transfer_prover

subsubsection \<open>\<^class>\<open>minus\<close>\<close>

locale minus_ow = fixes U minus assumes \<open>\<forall>x\<in>U. \<forall>y\<in>U. minus x y \<in> U\<close>

lemma minus_ow_parametricity[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (A ===> A ===> A) ===> (=)) 
     minus_ow minus_ow\<close>
  unfolding minus_ow_def
  by transfer_prover

subsubsection \<open>\<^class>\<open>uminus\<close>\<close>

locale uminus_ow = fixes U uminus assumes \<open>\<forall>x\<in>U. uminus x \<in> U\<close>

lemma uminus_ow_parametricity[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (A ===> A) ===> (=)) 
     uminus_ow uminus_ow\<close>
  unfolding uminus_ow_def
  by transfer_prover

subsection \<open>\<^locale>\<open>semigroup\<close>\<close>

locale semigroup_ow = plus_ow U plus for U plus +
  assumes \<open>\<forall>x\<in>U. \<forall>y\<in>U. \<forall>z\<in>U. plus x (plus y z) = plus (plus x y) z\<close>

lemma semigroup_ow_parametricity[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (A ===> A ===> A) ===> (=)) 
     semigroup_ow semigroup_ow\<close>
  unfolding semigroup_ow_def semigroup_ow_axioms_def
  by transfer_prover

lemma semigroup_ow_typeclass[simp, iff]: \<open>semigroup_ow V (+)\<close>
  if \<open>\<And>x y. x\<in>V \<Longrightarrow> y\<in>V \<Longrightarrow> x + y \<in> V\<close> for V :: \<open>'a :: semigroup_add set\<close>
  by (auto intro!: plus_ow.intro semigroup_ow.intro semigroup_ow_axioms.intro simp: Groups.add_ac that)

lemma class_semigroup_add_ud[unoverload_def]: \<open>class.semigroup_add = semigroup_ow UNIV\<close>
  by (auto intro!: ext plus_ow.intro simp: class.semigroup_add_def semigroup_ow_def semigroup_ow_axioms_def)

subsection \<open>\<^locale>\<open>abel_semigroup\<close>\<close>

locale abel_semigroup_ow = semigroup_ow U plus for U plus +
  assumes \<open>\<forall>x\<in>U. \<forall>y\<in>U. plus x y = plus y x\<close>

lemma abel_semigroup_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (A ===> A ===> A) ===> (=))
     abel_semigroup_ow abel_semigroup_ow\<close>
  unfolding abel_semigroup_ow_def abel_semigroup_ow_axioms_def make_parametricity_proof_friendly
  by transfer_prover

lemma abel_semigroup_ow_typeclass[simp, iff]: \<open>abel_semigroup_ow V (+)\<close>
  if \<open>\<And>x y. x\<in>V \<Longrightarrow> y\<in>V \<Longrightarrow> x + y \<in> V\<close> for V :: \<open>'a :: ab_semigroup_add set\<close>
  by (auto simp: abel_semigroup_ow_def abel_semigroup_ow_axioms_def Groups.add_ac that)

lemma class_ab_semigroup_add_ud[unoverload_def]: \<open>class.ab_semigroup_add = abel_semigroup_ow UNIV\<close>
  by (auto intro!: ext simp: class.ab_semigroup_add_def abel_semigroup_ow_def 
      class_semigroup_add_ud abel_semigroup_ow_axioms_def class.ab_semigroup_add_axioms_def)

subsection \<open>\<^locale>\<open>comm_monoid\<close>\<close>

locale comm_monoid_ow = abel_semigroup_ow U plus for U plus +
  fixes zero
  assumes \<open>zero \<in> U\<close>
  assumes \<open>\<forall>x\<in>U. plus x zero = x\<close>

lemma comm_monoid_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (A ===> A ===> A) ===> A ===> (=))
     comm_monoid_ow comm_monoid_ow\<close>
  unfolding comm_monoid_ow_def comm_monoid_ow_axioms_def make_parametricity_proof_friendly
  by transfer_prover

lemma comm_monoid_ow_typeclass[simp, iff]: \<open>comm_monoid_ow V (+) 0\<close>
  if \<open>0 \<in> V\<close> and \<open>\<And>x y. x\<in>V \<Longrightarrow> y\<in>V \<Longrightarrow> x + y \<in> V\<close> for V :: \<open>'a :: comm_monoid_add set\<close>
  by (auto simp: comm_monoid_ow_def comm_monoid_ow_axioms_def that)

lemma class_comm_monoid_add_ud[unoverload_def]: \<open>class.comm_monoid_add = comm_monoid_ow UNIV\<close>
  apply (auto intro!: ext simp: class.comm_monoid_add_def comm_monoid_ow_def
      class_ab_semigroup_add_ud class.comm_monoid_add_axioms_def comm_monoid_ow_axioms_def)
  by (simp_all add: abel_semigroup_ow_def abel_semigroup_ow_axioms_def)

subsection \<open>\<^class>\<open>topological_space\<close>\<close>

locale topological_space_ow = 
  fixes U "open"
  assumes \<open>open U\<close>
  assumes \<open>\<forall>S\<subseteq>U. \<forall>T\<subseteq>U. open S \<longrightarrow> open T \<longrightarrow> open (S \<inter> T)\<close>
  assumes "\<forall>K\<subseteq>Pow U. (\<forall>S\<in>K. open S) \<longrightarrow> open (\<Union>K)"

lemma topological_space_ow_parametricity[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (rel_set A ===> (=)) ===> (=)) 
     topological_space_ow topological_space_ow\<close>
  unfolding topological_space_ow_def make_parametricity_proof_friendly
  by transfer_prover

lemma class_topological_space_ud[unoverload_def]: \<open>class.topological_space = topological_space_ow UNIV\<close>
  by (auto intro!: ext simp: class.topological_space_def topological_space_ow_def)

lemma topological_space_ow_from_topology[simp]: \<open>topological_space_ow (topspace T) (openin T)\<close>
  by (auto intro!: topological_space_ow.intro)

subsection \<open>\<^const>\<open>sum\<close>\<close>

definition \<open>sum_ow z plus f S = 
  (if finite S then the_default z (Collect (fold_graph (plus o f) z S)) else z)\<close>
  for U z plus S

lemma sum_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close> \<open>bi_unique U\<close>
  shows \<open>(T ===> (V ===> T ===> T) ===> (U ===> V) ===> rel_set U ===> T)
            sum_ow sum_ow\<close>
  unfolding sum_ow_def
  by transfer_prover

lemma (in comm_monoid_set) comp_fun_commute_onI: \<open>Finite_Set.comp_fun_commute_on UNIV ((\<^bold>*) \<circ> g)\<close>
  apply (rule Finite_Set.comp_fun_commute_on.intro)
  by (simp add: o_def left_commute)

lemma (in comm_monoid_set) F_via_the_default: \<open>F g A = the_default def (Collect (fold_graph ((\<^bold>*) \<circ> g) \<^bold>1 A))\<close>
  if \<open>finite A\<close>
proof -
  have \<open>y = x\<close> if \<open>fold_graph ((\<^bold>*) \<circ> g) \<^bold>1 A x\<close> and \<open>fold_graph ((\<^bold>*) \<circ> g) \<^bold>1 A y\<close> for x y
    using that apply (rule Finite_Set.comp_fun_commute_on.fold_graph_determ[rotated 2, where S=UNIV])
    by (simp_all add: comp_fun_commute_onI)
  then have \<open>Ex1 (fold_graph ((\<^bold>*) \<circ> g) \<^bold>1 A)\<close>
    by (meson finite_imp_fold_graph that)
  then have \<open>card (Collect (fold_graph ((\<^bold>*) \<circ> g) \<^bold>1 A)) = 1\<close>
    using card_eq_Suc_0_ex1 by fastforce
  then show ?thesis
    using that by (auto simp add: the_default_The eq_fold Finite_Set.fold_def)
qed

lemma sum_ud[unoverload_def]: \<open>sum = sum_ow 0 plus\<close>
  apply (auto intro!: ext simp: sum_def sum_ow_def comm_monoid_set.F_via_the_default)
   apply (subst comm_monoid_set.F_via_the_default)
    apply (auto simp add: sum.comm_monoid_set_axioms)
  by (metis comm_monoid_add_class.sum_def sum.infinite)

(* declare sum_with[unoverload_def del] *)

subsection \<open>\<^class>\<open>t2_space\<close>\<close>

locale t2_space_ow = topological_space_ow +
  assumes \<open>\<forall>x\<in>U. \<forall>y\<in>U. x \<noteq> y \<longrightarrow> (\<exists>S\<subseteq>U. \<exists>T\<subseteq>U. open S \<and> open T \<and> x \<in> S \<and> y \<in> T \<and> S \<inter> T = {})\<close>

lemma t2_space_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (rel_set A ===> (=)) ===> (=)) 
     t2_space_ow t2_space_ow\<close>
  unfolding t2_space_ow_def t2_space_ow_axioms_def make_parametricity_proof_friendly
  by transfer_prover

lemma class_t2_space_ud[unoverload_def]: \<open>class.t2_space = t2_space_ow UNIV\<close>
  by (auto intro!: ext simp: class.t2_space_def class.t2_space_axioms_def t2_space_ow_def
      t2_space_ow_axioms_def class_topological_space_ud)

lemma t2_space_ow_from_topology[simp, iff]: \<open>t2_space_ow (topspace T) (openin T)\<close> if \<open>Hausdorff_space T\<close>
  using that
  apply (auto intro!: t2_space_ow.intro simp: t2_space_ow_axioms_def Hausdorff_space_def disjnt_def)
  by (metis openin_subset)

subsubsection \<open>\<^const>\<open>continuous_on\<close>\<close>

definition continuous_on_ow where \<open>continuous_on_ow A B opnA opnB s f 
  \<longleftrightarrow> (\<forall>U\<subseteq>B. opnB U \<longrightarrow> (\<exists>V\<subseteq>A. opnA V \<and> (V \<inter> s) = (f -` U) \<inter> s))\<close>
  for f :: \<open>'a \<Rightarrow> 'b\<close>

lemma continuous_on_ud[unoverload_def]: \<open>continuous_on s f \<longleftrightarrow> continuous_on_ow UNIV UNIV open open s f\<close>
  for f :: \<open>'a::topological_space \<Rightarrow> 'b::topological_space\<close>
  unfolding continuous_on_ow_def continuous_on_open_invariant by auto

lemma continuous_on_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close> \<open>bi_unique B\<close>
  shows \<open>(rel_set A ===> rel_set B ===> (rel_set A ===> (\<longleftrightarrow>)) ===> (rel_set B ===> (\<longleftrightarrow>)) ===> rel_set A ===> (A ===> B) ===> (\<longleftrightarrow>)) continuous_on_ow continuous_on_ow\<close>
  unfolding continuous_on_ow_def make_parametricity_proof_friendly
  by transfer_prover


subsection \<open>\<^class>\<open>scaleR\<close>\<close>

locale scaleR_ow = 
  fixes U and scaleR :: \<open>real \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  assumes scaleR_closed: \<open>\<forall>a \<in> U. scaleR r a \<in> U\<close>

lemma scaleR_ow_typeclass[simp]: \<open>scaleR_ow UNIV scaleR\<close> for scaleR
  by (simp add: scaleR_ow_def)

lemma scaleR_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> ((=) ===> A ===> A) ===> (=))
     scaleR_ow scaleR_ow\<close>
  unfolding scaleR_ow_def make_parametricity_proof_friendly
  by transfer_prover

subsection \<open>\<^class>\<open>scaleC\<close>\<close>

locale scaleC_ow = scaleR_ow +
  fixes scaleC
  assumes scaleC_closed: \<open>\<forall>a\<in>U. scaleC c a \<in> U\<close>
  assumes \<open>\<forall>a\<in>U. scaleR r a = scaleC (complex_of_real r) a\<close>

lemma scaleC_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> ((=) ===> A ===> A) ===> ((=) ===> A ===> A) ===> (=))
     scaleC_ow scaleC_ow\<close>
  unfolding scaleC_ow_def scaleC_ow_axioms_def make_parametricity_proof_friendly
  by transfer_prover

lemma class_scaleC_ud[unoverload_def]: \<open>class.scaleC = scaleC_ow UNIV\<close>
  by (auto intro!: ext simp: class.scaleC_def scaleC_ow_def scaleR_ow_def scaleC_ow_axioms_def)

subsection \<open>\<^class>\<open>ab_group_add\<close>\<close>

locale ab_group_add_ow = comm_monoid_ow U plus zero + minus_ow U minus + uminus_ow U uminus
  for U plus zero minus uminus +
  assumes \<open>\<forall>a\<in>U. uminus a \<in> U\<close>
  assumes "\<forall>a\<in>U. plus (uminus a) a = zero"
  assumes "\<forall>a\<in>U. \<forall>b\<in>U. minus a b = plus a (uminus b)"

lemma ab_group_add_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (A ===> A ===> A) ===> A ===> (A ===> A ===> A) ===> (A ===> A) ===> (=)) 
     ab_group_add_ow ab_group_add_ow\<close>
  unfolding ab_group_add_ow_def ab_group_add_ow_axioms_def
  apply transfer_prover_start
  apply transfer_step+
  by transfer_prover

lemma ab_group_add_ow_typeclass[simp]: 
  \<open>ab_group_add_ow V (+) 0 (-) uminus\<close> 
  if \<open>0 \<in> V\<close> \<open>\<forall>x\<in>V. -x \<in> V\<close> \<open>\<forall>x\<in>V. \<forall>y\<in>V. x + y \<in> V\<close>
  for V :: \<open>_ :: ab_group_add set\<close>
  using that
  apply (auto intro!: ab_group_add_ow.intro ab_group_add_ow_axioms.intro comm_monoid_ow_typeclass
      minus_ow.intro uminus_ow.intro)
  by force

lemma class_ab_group_add_ud[unoverload_def]: \<open>class.ab_group_add = ab_group_add_ow UNIV\<close>
  by (auto intro!: ext simp: class.ab_group_add_def ab_group_add_ow_def class_comm_monoid_add_ud
      minus_ow_def uminus_ow_def ab_group_add_ow_axioms_def class.ab_group_add_axioms_def)

subsection \<open>\<^locale>\<open>vector_space\<close>\<close>

locale vector_space_ow = ab_group_add_ow U plus zero minus uminus
  for U plus zero minus uminus +
  fixes scale :: "'f::field \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes
    \<open>\<forall>x\<in>U. scale a x \<in> U\<close>
    "\<forall>x\<in>U. \<forall>y\<in>U. scale a (plus x y) = plus (scale a x) (scale a y)"
    "\<forall>x\<in>U. scale (a + b) x = plus (scale a x) (scale b x)"
    "\<forall>x\<in>U. scale a (scale b x) = scale (a * b) x"
    "\<forall>x\<in>U. scale 1 x = x"

lemma vector_space_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (A ===> A ===> A) ===> A ===> (A ===> A ===> A) ===> (A ===> A) ===> ((=) ===> A ===> A) ===> (=)) 
     vector_space_ow vector_space_ow\<close>
  unfolding vector_space_ow_def vector_space_ow_axioms_def
  apply transfer_prover_start
                      apply transfer_step+
  by simp

subsection \<open>\<^class>\<open>complex_vector\<close>\<close>

locale complex_vector_ow = vector_space_ow U plus zero minus uminus scaleC + scaleC_ow U scaleR scaleC
  for U scaleR scaleC plus zero minus uminus

lemma complex_vector_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> ((=) ===> A ===> A) ===> ((=) ===> A ===> A) ===> (A ===> A ===> A) ===>
     A ===> (A ===> A ===> A) ===> (A ===> A) ===> (=))
     complex_vector_ow complex_vector_ow\<close>
  unfolding complex_vector_ow_def make_parametricity_proof_friendly
  by transfer_prover

lemma class_complex_vector_ud[unoverload_def]: \<open>class.complex_vector = complex_vector_ow UNIV\<close>
  by (auto intro!: ext simp: class.complex_vector_def vector_space_ow_def vector_space_ow_axioms_def
      class.complex_vector_axioms_def class.scaleC_def complex_vector_ow_def
      class_scaleC_ud class_ab_group_add_ud)

lemma vector_space_ow_typeclass[simp]: 
  \<open>vector_space_ow V (+) 0 (-) uminus (*\<^sub>C)\<close> 
  if [simp]: \<open>csubspace V\<close>
  for V :: \<open>_::complex_vector set\<close>
  by (auto intro!: vector_space_ow.intro ab_group_add_ow_typeclass scaleC_left.add
      vector_space_ow_axioms.intro complex_vector.subspace_neg scaleC_add_right
      complex_vector.subspace_add complex_vector.subspace_scale complex_vector.subspace_0)

lemma complex_vector_ow_typeclass[simp]:
  \<open>complex_vector_ow V (*\<^sub>R) (*\<^sub>C) (+) 0 (-) uminus\<close> if [simp]: \<open>csubspace V\<close>
  by (auto intro!: scaleC_ow_def simp add: complex_vector_ow_def scaleC_ow_def 
      scaleC_ow_axioms_def scaleR_ow_def scaleR_scaleC complex_vector.subspace_scale)


subsection \<open>\<^class>\<open>open_uniformity\<close>\<close>

locale open_uniformity_ow = "open" "open" + uniformity uniformity
  for A "open" uniformity +
  assumes open_uniformity:
    "\<And>U. U \<subseteq> A \<Longrightarrow> open U \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

lemma open_uniformity_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (rel_set A ===> (=)) ===> rel_filter (rel_prod A A) ===> (=)) 
     open_uniformity_ow open_uniformity_ow\<close>
  unfolding open_uniformity_ow_def make_parametricity_proof_friendly
  by transfer_prover

lemma class_open_uniformity_ud[unoverload_def]: \<open>class.open_uniformity = open_uniformity_ow UNIV\<close>
  by (auto intro!: ext simp: class.open_uniformity_def open_uniformity_ow_def)

lemma open_uniformity_on_typeclass[simp]: 
  fixes V :: \<open>_::open_uniformity set\<close>
  assumes \<open>closed V\<close>
  shows \<open>open_uniformity_ow V (openin (top_of_set V)) (uniformity_on V)\<close>
proof (rule open_uniformity_ow.intro, intro allI impI iffI ballI)
  fix U assume \<open>U \<subseteq> V\<close>
  assume \<open>openin (top_of_set V) U\<close>
  then obtain T where \<open>U = T \<inter> V\<close> and \<open>open T\<close>
    by (metis Int_ac(3) openin_open)
  with open_uniformity 
  have *: \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> T\<close> if \<open>x \<in> T\<close> for x
    using that by blast
  have \<open>\<forall>\<^sub>F (x', y) in uniformity_on V. x' = x \<longrightarrow> y \<in> U\<close> if \<open>x \<in> U\<close> for x
    apply (rule eventually_inf_principal[THEN iffD2])
    using *[of x] apply (rule eventually_rev_mp)
    using \<open>U = T \<inter> V\<close> that by (auto intro!: always_eventually)
  then show \<open>\<forall>\<^sub>F (x', y) in uniformity_on V. x' = x \<longrightarrow> y \<in> U\<close> if \<open>x \<in> U\<close> for x
    using that by blast
next
  fix U assume \<open>U \<subseteq> V\<close>
  assume asm: \<open>\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity_on V. x' = x \<longrightarrow> y \<in> U\<close>
  from asm[rule_format]
  have \<open>\<forall>\<^sub>F (x', y) in uniformity. x' \<in> V \<and> y \<in> V \<and> x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> U\<close> for x
    unfolding eventually_inf_principal
    apply (rule eventually_rev_mp)
    using that by (auto intro!: always_eventually)
  then have xU: \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> U\<close> for x
    apply (rule eventually_rev_mp)
    using that \<open>U \<subseteq> V\<close> by (auto intro!: always_eventually)
  have \<open>open (-V)\<close>
    using assms by auto
  with open_uniformity
  have \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> -V\<close> if \<open>x \<in> -V\<close> for x
    using that by blast
  then have xV: \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> -V\<close> for x
    apply (rule eventually_rev_mp)
     apply (rule that)
    apply (rule always_eventually)
    by auto
  have \<open>\<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U \<union> -V\<close> if \<open>x \<in> U \<union> -V\<close> for x
    using xV[of x] xU[of x] that
    by auto
  then have \<open>open (U \<union> -V)\<close>
    using open_uniformity by blast
  then show \<open>openin (top_of_set V) U\<close>
    using \<open>U \<subseteq> V\<close>
    by (auto intro!: exI simp: openin_open)
qed

subsection \<open>\<^class>\<open>uniformity_dist\<close>\<close>

locale uniformity_dist_ow = dist dist + uniformity uniformity for U dist uniformity +
  assumes uniformity_dist: "uniformity = (\<Sqinter>e\<in>{0<..}. principal {(x, y)\<in>U\<times>U. dist x y < e})"

lemma class_uniformity_dist_ud[unoverload_def]: \<open>class.uniformity_dist = uniformity_dist_ow UNIV\<close>
  by (auto intro!: ext simp: class.uniformity_dist_def uniformity_dist_ow_def)

lemma uniformity_dist_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (A ===> A ===> (=)) ===> rel_filter (rel_prod A A) ===> (=))
     uniformity_dist_ow uniformity_dist_ow\<close>
proof -
  have *: "uniformity_dist_ow U dist uniformity \<longleftrightarrow> 
          uniformity = transfer_bounded_filter_Inf (transfer_Times U U)
              ((\<lambda>e. principal (Set.filter (\<lambda>(x,y). dist x y < e) (transfer_Times U U))) ` {0<..})"
  for  U dist uniformity
    unfolding uniformity_dist_ow_def make_parametricity_proof_friendly case_prod_unfold
      prod.collapse
    apply (subst Inf_bounded_transfer_bounded_filter_Inf[where B=\<open>U\<times>U\<close>])
    by (auto simp: transfer_Times_def)
  show ?thesis
    unfolding *[abs_def]
    by transfer_prover
qed

lemma uniformity_dist_on_typeclass[simp]: \<open>uniformity_dist_ow V dist (uniformity_on V)\<close> for V :: \<open>_::uniformity_dist set\<close>
  apply (auto simp add: uniformity_dist_ow_def uniformity_dist simp flip: INF_inf_const2)
  apply (subst asm_rl[of \<open>\<And>x. Restr {(xa, y). dist xa y < x} V = {(xa, y). xa \<in> V \<and> y \<in> V \<and> dist xa y < x}\<close>, rule_format])
  by auto

subsection \<open>\<^class>\<open>sgn\<close>\<close>

locale sgn_ow =
  fixes U and sgn :: \<open>'a \<Rightarrow> 'a\<close>
  assumes sgn_closed: \<open>\<forall>a\<in>U. sgn a \<in> U\<close>

lemma sgn_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (A ===> A) ===> (=)) 
     sgn_ow sgn_ow\<close>
  unfolding sgn_ow_def
  by transfer_prover

subsection \<open>\<^class>\<open>sgn_div_norm\<close>\<close>

locale sgn_div_norm_ow = scaleR_ow U scaleR + norm norm + sgn_ow U sgn for U sgn norm scaleR +
  assumes "\<forall>x\<in>U. sgn x = scaleR (inverse (norm x)) x"

lemma class_sgn_div_norm_ud[unoverload_def]: \<open>class.sgn_div_norm = sgn_div_norm_ow UNIV\<close>
  by (auto intro!: ext simp: class.sgn_div_norm_def sgn_div_norm_ow_def sgn_div_norm_ow_axioms_def unoverload_def sgn_ow_def)

lemma sgn_div_norm_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (A ===> A) ===> (A ===> (=)) ===> ((=) ===> A ===> A) ===> (=)) 
     sgn_div_norm_ow sgn_div_norm_ow\<close>
  unfolding sgn_div_norm_ow_def sgn_div_norm_ow_axioms_def make_parametricity_proof_friendly
  by transfer_prover

lemma sgn_div_norm_on_typeclass[simp]: 
  fixes V :: \<open>_::sgn_div_norm set\<close>
  assumes \<open>\<And>v r. v\<in>V \<Longrightarrow> scaleR r v \<in> V\<close>
  shows \<open>sgn_div_norm_ow V sgn norm (*\<^sub>R)\<close> 
  using assms 
  by (auto simp add: sgn_ow_def sgn_div_norm_ow_axioms_def scaleR_ow_def sgn_div_norm_ow_def sgn_div_norm)

subsection \<open>\<^class>\<open>dist_norm\<close>\<close>

locale dist_norm_ow = dist dist + norm norm + minus_ow U minus for U minus dist norm +
  assumes dist_norm: "\<forall>x\<in>U. \<forall>y\<in>U. dist x y = norm (minus x y)"

lemma dist_norm_ud[unoverload_def]: \<open>class.dist_norm = dist_norm_ow UNIV\<close>
  by (auto intro!: ext simp: class.dist_norm_def dist_norm_ow_def dist_norm_ow_axioms_def
      minus_ow_def unoverload_def)

lemma dist_norm_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (A ===> A ===> A) ===> (A ===> A ===> (=)) ===> (A ===> (=)) ===> (=))
     dist_norm_ow dist_norm_ow\<close>
  unfolding dist_norm_ow_def dist_norm_ow_axioms_def make_parametricity_proof_friendly
  by transfer_prover

lemma dist_norm_ow_typeclass[simp]: 
  fixes A :: \<open>_::dist_norm set\<close>
  assumes \<open>\<And>a b. \<lbrakk> a \<in> A; b \<in> A \<rbrakk> \<Longrightarrow> a - b \<in> A\<close>
  shows \<open>dist_norm_ow A (-) dist norm\<close> 
  by (auto simp add: assms dist_norm_ow_def minus_ow_def dist_norm_ow_axioms_def dist_norm)

subsection \<open>\<^class>\<open>complex_inner\<close>\<close>

locale complex_inner_ow = complex_vector_ow U scaleR scaleC plus zero minus uminus
  + dist_norm_ow U minus dist norm + sgn_div_norm_ow U sgn norm scaleR
  + uniformity_dist_ow U dist uniformity
  + open_uniformity_ow U "open" uniformity
  for U scaleR scaleC plus zero minus uminus dist norm sgn uniformity "open" +
  fixes cinner :: "'a \<Rightarrow> 'a \<Rightarrow> complex"
  assumes "\<forall>x\<in>U. \<forall>y\<in>U. cinner x y = cnj (cinner y x)"
    and "\<forall>x\<in>U. \<forall>y\<in>U. \<forall>z\<in>U. cinner (plus x y) z = cinner x z + cinner y z"
    and "\<forall>x\<in>U. \<forall>y\<in>U. cinner (scaleC r x) y = cnj r * cinner x y"
    and "\<forall>x\<in>U. 0 \<le> cinner x x"
    and "\<forall>x\<in>U. cinner x x = 0 \<longleftrightarrow> x = zero"
    and "\<forall>x\<in>U. norm x = sqrt (cmod (cinner x x))"

lemma class_complex_inner_ud[unoverload_def]: \<open>class.complex_inner = complex_inner_ow UNIV\<close>
  apply (intro ext)
  by (simp add: class.complex_inner_def class.complex_inner_axioms_def complex_inner_ow_def complex_inner_ow_axioms_def unoverload_def)

lemma complex_inner_ow_parametricity[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>(rel_set T ===> ((=) ===> T ===> T) ===> ((=) ===> T ===> T) ===> (T ===> T ===> T) ===> T 
          ===> (T ===> T ===> T) ===> (T ===> T) ===> (T ===> T ===> (=)) ===> (T ===> (=))
          ===> (T ===> T) ===> rel_filter (rel_prod T T) ===> (rel_set T ===> (=))
          ===> (T ===> T ===> (=)) ===> (=)) complex_inner_ow complex_inner_ow\<close>
  unfolding complex_inner_ow_def complex_inner_ow_axioms_def
  by transfer_prover

lemma complex_inner_ow_typeclass[simp]:
  fixes V :: \<open>_::complex_inner set\<close>
  assumes [simp]: \<open>closed V\<close> \<open>csubspace V\<close>
  shows \<open>complex_inner_ow V (*\<^sub>R) (*\<^sub>C) (+) 0 (-) uminus dist norm sgn (uniformity_on V) (openin (top_of_set V)) (\<bullet>\<^sub>C)\<close>
  apply (auto intro!: complex_vector_ow_typeclass dist_norm_ow_typeclass sgn_div_norm_on_typeclass
      simp: complex_inner_ow_def cinner_simps complex_vector.subspace_diff complex_inner_ow_axioms_def
      scaleR_scaleC complex_vector.subspace_scale 
      simp flip: norm_eq_sqrt_cinner)
  by -

subsection \<open>\<^const>\<open>is_ortho_set\<close>\<close>

definition is_ortho_set_ow where \<open>is_ortho_set_ow zero cinner S \<longleftrightarrow> 
  ((\<forall>x\<in>S. \<forall>y\<in>S. x \<noteq> y \<longrightarrow> cinner x y = 0) \<and> zero \<notin> S)\<close>
  for zero cinner

lemma is_ortho_set_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(A ===> (A ===> A ===> (=)) ===> rel_set A ===> (=))
     is_ortho_set_ow is_ortho_set_ow\<close>
  unfolding is_ortho_set_ow_def make_parametricity_proof_friendly
  by transfer_prover

lemma is_ortho_set_ud[unoverload_def]: \<open>is_ortho_set = is_ortho_set_ow 0 cinner\<close>
  by (auto simp: is_ortho_set_ow_def is_ortho_set_def)

subsection \<open>\<^class>\<open>metric_space\<close>\<close>

locale metric_space_ow = uniformity_dist_ow U dist uniformity + open_uniformity_ow U "open" uniformity
  for U dist uniformity "open" +
  assumes "\<forall>x \<in> U. \<forall>y \<in> U. dist x y = 0 \<longleftrightarrow> x = y"
    and "\<forall>x\<in>U. \<forall>y\<in>U. \<forall>z\<in>U. dist x y \<le> dist x z + dist y z"

lemma metric_space_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (A ===> A ===> (=)) ===> rel_filter (rel_prod A A) ===>
            (rel_set A ===> (=)) ===> (=))
     metric_space_ow metric_space_ow\<close>
  unfolding metric_space_ow_def metric_space_ow_axioms_def make_parametricity_proof_friendly
  by transfer_prover

lemma class_metric_space_ud[unoverload_def]: \<open>class.metric_space = metric_space_ow UNIV\<close>
  by (auto intro!: ext simp: class.metric_space_def class.metric_space_axioms_def metric_space_ow_def metric_space_ow_axioms_def unoverload_def)

lemma metric_space_ow_typeclass[simp]:
  fixes V :: \<open>_::metric_space set\<close>
  assumes \<open>closed V\<close>
  shows \<open>metric_space_ow V dist (uniformity_on V) (openin (top_of_set V))\<close>
  by (auto simp: assms metric_space_ow_def metric_space_ow_axioms_def class.metric_space_axioms_def dist_triangle2)

subsection \<open>\<^const>\<open>nhds\<close>\<close>

definition nhds_ow where \<open>nhds_ow U open a = (INF S\<in>{S. S \<subseteq> U \<and> open S \<and> a \<in> S}. principal S) \<sqinter> principal U\<close>
  for U "open"

lemma nhds_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> (rel_set A ===> (=)) ===> A ===> rel_filter A) 
     nhds_ow nhds_ow\<close>
  unfolding nhds_ow_def[folded transfer_bounded_filter_Inf_def] make_parametricity_proof_friendly
  by transfer_prover

lemma topological_space_nhds_ud[unoverload_def]: \<open>topological_space.nhds = nhds_ow UNIV\<close>
  by (auto intro!: ext simp add: nhds_ow_def [[axiom topological_space.nhds_def_raw]])

lemma nhds_ud[unoverload_def]: \<open>nhds = nhds_ow UNIV open\<close>
  by (auto intro!: ext simp add: nhds_ow_def nhds_def)

lemma nhds_ow_topology[simp]: \<open>nhds_ow (topspace T) (openin T) x = nhdsin T x\<close> if \<open>x \<in> topspace T\<close>
  using that apply (auto intro!: ext simp add: nhds_ow_def nhdsin_def[abs_def])
   apply (subst INF_inf_const2[symmetric])
  using openin_subset by (auto intro!: INF_cong)

subsection \<open>\<^const>\<open>at_within\<close>\<close>

definition \<open>at_within_ow U open a s = nhds_ow U open a \<sqinter> principal (s - {a})\<close>
  for U "open" a s

lemma at_within_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>((rel_set T) ===> (rel_set T ===> (=)) ===> T ===> rel_set T ===> rel_filter T)
            at_within_ow at_within_ow\<close>
  unfolding at_within_ow_def make_parametricity_proof_friendly transfer_inf_principal_def[symmetric]
  by transfer_prover

lemma at_within_ud[unoverload_def]: \<open>at_within = at_within_ow UNIV open\<close>
  by (auto intro!: ext simp: at_within_def at_within_ow_def unoverload_def)

lemma at_within_ow_topology:
  \<open>at_within_ow (topspace T) (openin T) a S = nhdsin T a \<sqinter> principal (S - {a})\<close> 
  if \<open>a \<in> topspace T\<close>
  using that unfolding at_within_ow_def by (simp add: nhds_ow_topology)


subsection \<open>\<^const>\<open>has_sum\<close>\<close>

definition \<open>has_sum_ow U plus zero open f A x =
        filterlim (sum_ow zero plus f) (nhds_ow U (\<lambda>S. open S) x)
         (finite_subsets_at_top A)\<close>
  for U plus zero "open" f A x

lemma has_sum_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close> \<open>bi_unique U\<close>
  shows \<open>(rel_set T ===> (V ===> T ===> T) ===> T ===> (rel_set T ===> (=)) ===> (U ===> V) ===> rel_set U ===> T ===> (=))
            has_sum_ow has_sum_ow\<close>
  unfolding has_sum_ow_def
  by transfer_prover

lemma has_sum_ud[unoverload_def]: \<open>HAS_SUM = has_sum_ow UNIV plus (0::'a::{comm_monoid_add,topological_space}) open\<close>
  by (auto intro!: ext simp: has_sum_def has_sum_ow_def unoverload_def)

lemma has_sum_ow_topology:
  assumes \<open>l \<in> topspace T\<close>
  assumes \<open>0 \<in> topspace T\<close>
  assumes \<open>\<And>x y. x \<in> topspace T \<Longrightarrow> y \<in> topspace T \<Longrightarrow> x + y \<in> topspace T\<close>
  shows \<open>has_sum_ow (topspace T) (+) 0 (openin T) f S l \<longleftrightarrow> has_sum_in T f S l\<close>
  using assms apply (simp add: has_sum_ow_def has_sum_in_def nhds_ow_topology sum_ud[symmetric])
  by (metis filterlim_nhdsin_iff_limitin)

subsection \<open>\<^const>\<open>filterlim\<close>\<close>

subsection \<open>\<^const>\<open>convergent\<close>\<close>

definition convergent_ow where
  \<open>convergent_ow U open X \<longleftrightarrow> (\<exists>L\<in>U. filterlim X (nhds_ow U open L) sequentially)\<close>
for U "open"

lemma convergent_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>(rel_set T ===> (rel_set T ===> (=)) ===> ((=) ===> T) ===> (\<longleftrightarrow>))
           convergent_ow convergent_ow\<close>
  unfolding convergent_ow_def
  by transfer_prover

lemma convergent_ud[unoverload_def]: \<open>convergent = convergent_ow UNIV open\<close>
  by (auto simp: convergent_ow_def[abs_def] convergent_def[abs_def] unoverload_def)

lemma topological_space_convergent_ud[unoverload_def]: \<open>topological_space.convergent = convergent_ow UNIV\<close>
  by (auto intro!: ext simp: [[axiom topological_space.convergent_def_raw]]
      convergent_ow_def unoverload_def)

lemma convergent_ow_topology[simp]:
  \<open>convergent_ow (topspace T) (openin T) f \<longleftrightarrow> (\<exists>l. limitin T f l sequentially)\<close>
  by (auto simp: convergent_ow_def simp flip: filterlim_nhdsin_iff_limitin)

lemma convergent_ow_typeclass[simp]:
  \<open>convergent_ow V (openin (top_of_set V)) f \<longleftrightarrow> (\<exists>l. limitin (top_of_set V) f l sequentially)\<close>
  by (simp flip: convergent_ow_topology)

subsection \<open>\<^const>\<open>uniform_space.cauchy_filter\<close>\<close>

lemma cauchy_filter_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique T"
  shows "(rel_filter (rel_prod T T) ===> rel_filter T ===> (=)) 
    uniform_space.cauchy_filter
    uniform_space.cauchy_filter"
  unfolding [[axiom uniform_space.cauchy_filter_def_raw]]
  by transfer_prover

subsection \<open>\<^const>\<open>uniform_space.Cauchy\<close>\<close>

lemma uniform_space_Cauchy_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique T"
  shows "(rel_filter (rel_prod T T) ===> ((=) ===> T) ===> (=)) 
    uniform_space.Cauchy
    uniform_space.Cauchy"
  unfolding [[axiom uniform_space.Cauchy_uniform_raw]]
  using filtermap_parametric[transfer_rule] apply fail?
  by transfer_prover

subsection \<open>\<^class>\<open>complete_space\<close>\<close>

locale complete_space_ow = metric_space_ow U dist uniformity "open"
  for U dist uniformity "open" +
  assumes \<open>range X \<subseteq> U \<longrightarrow> uniform_space.Cauchy uniformity X \<longrightarrow> convergent_ow U open X\<close>

lemma class_complete_space_ud[unoverload_def]: \<open>class.complete_space = complete_space_ow UNIV\<close>
  by (auto intro!: ext simp: class.complete_space_def class.complete_space_axioms_def complete_space_ow_def complete_space_ow_axioms_def unoverload_def)

lemma complete_space_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique T"
  shows "(rel_set T ===> (T ===> T ===> (=)) ===> rel_filter (rel_prod T T) ===> (rel_set T ===> (=)) ===> (=)) 
    complete_space_ow complete_space_ow"
  unfolding complete_space_ow_def complete_space_ow_axioms_def make_parametricity_proof_friendly
  by transfer_prover

lemma complete_space_ow_typeclass[simp]:
  fixes V :: \<open>_::uniform_space set\<close>
  assumes \<open>complete V\<close>
  shows \<open>complete_space_ow V dist (uniformity_on V) (openin (top_of_set V))\<close>
proof (rule complete_space_ow.intro)
  show \<open>metric_space_ow V dist (uniformity_on V) (openin (top_of_set V))\<close>
    apply (rule metric_space_ow_typeclass)
    by (simp add: assms complete_imp_closed)
  have \<open>\<exists>l. limitin (top_of_set V) X l sequentially\<close>
    if XV: \<open>\<And>n. X n \<in> V\<close> and cauchy: \<open>uniform_space.Cauchy (uniformity_on V) X\<close> for X
  proof -
    from cauchy
    have \<open>uniform_space.cauchy_filter (uniformity_on V) (filtermap X sequentially)\<close>
      by (simp add: [[axiom uniform_space.Cauchy_uniform_raw]])
    then have \<open>cauchy_filter (filtermap X sequentially)\<close>
      by (auto simp: cauchy_filter_def [[axiom uniform_space.cauchy_filter_def_raw]])
    then have \<open>Cauchy X\<close>
      by (simp add: Cauchy_uniform)
    with \<open>complete V\<close> XV obtain l where l: \<open>X \<longlonglongrightarrow> l\<close> \<open>l \<in> V\<close>
      apply atomize_elim
      by (meson completeE)
    with XV l show ?thesis
      by (auto intro!: exI[of _ l] simp: convergent_def limitin_subtopology)
  qed
  then show \<open>complete_space_ow_axioms V (uniformity_on V) (openin (top_of_set V))\<close>
    apply (auto simp: complete_space_ow_axioms_def complete_imp_closed assms)
    by blast
qed

subsection \<open>\<^class>\<open>chilbert_space\<close>\<close>

locale chilbert_space_ow = complex_inner_ow + complete_space_ow

lemma chilbert_space_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===> ((=) ===> A ===> A) ===> ((=) ===> A ===> A) ===> (A ===> A ===> A) ===>
     A ===> (A ===> A ===> A) ===> (A ===> A) ===> (A ===> A ===> (=)) ===> (A ===> (=)) ===>
     (A ===> A) ===> rel_filter (rel_prod A A) ===> (rel_set A ===> (=)) ===> (A ===> A ===> (=)) ===> (=))
     chilbert_space_ow chilbert_space_ow\<close>
  unfolding chilbert_space_ow_def make_parametricity_proof_friendly
  by transfer_prover

lemma chilbert_space_on_typeclass[simp]:
  fixes V :: \<open>_::complex_inner set\<close>
  assumes \<open>complete V\<close> \<open>csubspace V\<close>
  shows \<open>chilbert_space_ow V (*\<^sub>R) (*\<^sub>C) (+) 0 (-) uminus dist norm sgn
     (uniformity_on V) (openin (top_of_set V)) (\<bullet>\<^sub>C)\<close>
  by (auto intro!: chilbert_space_ow.intro complex_inner_ow_typeclass
      simp: assms complete_imp_closed)

lemma class_chilbert_space_ud[unoverload_def]:
  \<open>class.chilbert_space = chilbert_space_ow UNIV\<close>
  by (auto intro!: ext simp add: class.chilbert_space_def chilbert_space_ow_def unoverload_def)

subsection \<open>\<^const>\<open>hull\<close>\<close>

definition \<open>hull_ow A S s = ((\<lambda>x. S x \<and> x \<subseteq> A) hull s) \<inter> A\<close>

lemma hull_ow_nondegenerate: \<open>hull_ow A S s = ((\<lambda>x. S x \<and> x \<subseteq> A) hull s)\<close> if \<open>x \<subseteq> A\<close> and \<open>s \<subseteq> x\<close> and \<open>S x\<close>
proof -
  have \<open>((\<lambda>x. S x \<and> x \<subseteq> A) hull s) \<subseteq> x\<close>
    apply (rule hull_minimal)
    using that by auto
  also note \<open>x \<subseteq> A\<close>
  finally show ?thesis
    unfolding hull_ow_def by auto
qed

definition \<open>transfer_bounded_Inf B M = Inf M \<sqinter> B\<close>

lemma transfer_bounded_Inf_parametric[transfer_rule]:
  includes lifting_syntax
  assumes \<open>bi_unique T\<close>
  shows \<open>(rel_set T ===> rel_set (rel_set T) ===> rel_set T) transfer_bounded_Inf transfer_bounded_Inf\<close>
  apply (auto intro!: rel_funI simp: transfer_bounded_Inf_def rel_set_def Bex_def)
  apply (metis (full_types) assms bi_uniqueDr)
  by (metis (full_types) assms bi_uniqueDl)

lemma hull_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique T"
  shows "(rel_set T ===> (rel_set T ===> (=)) ===> rel_set T ===> rel_set T) 
    hull_ow hull_ow"
proof -
  have *: \<open>hull_ow A S s = transfer_bounded_Inf A (Set.filter (\<lambda>x. S x \<and> s \<subseteq> x) (Pow A))\<close> for A S s
    by (auto simp add: hull_ow_def hull_def transfer_bounded_Inf_def)
  show ?thesis
    unfolding *
    by transfer_prover      
qed

lemma hull_ow_ud[unoverload_def]: \<open>(hull) = hull_ow UNIV\<close>
  unfolding hull_def hull_ow_def by auto

subsection \<open>\<^const>\<open>csubspace\<close>\<close>

definition
  \<open>subspace_ow plus zero scale S = (zero \<in> S \<and> (\<forall>x\<in>S. \<forall>y\<in>S. plus x y \<in> S) \<and> (\<forall>c. \<forall>x\<in>S. scale c x \<in> S))\<close>
  for plus zero scale S

lemma subspace_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>((T ===> T ===> T) ===> T ===> ((=) ===> T ===> T) ===> rel_set T ===> (=))
           subspace_ow subspace_ow\<close>
  unfolding subspace_ow_def
  by transfer_prover

lemma module_subspace_ud[unoverload_def]: \<open>module.subspace = subspace_ow plus 0\<close>
  by (auto intro!: ext simp: [[axiom module.subspace_def_raw]] subspace_ow_def)

lemma csubspace_ud[unoverload_def]: \<open>csubspace = subspace_ow (+) 0 (*\<^sub>C)\<close>
  by (simp add: csubspace_raw_def module_subspace_ud)

subsection \<open>\<^const>\<open>cspan\<close>\<close>

definition 
  \<open>span_ow U plus zero scale b = hull_ow U (subspace_ow plus zero scale) b\<close>
  for U plus zero scale b

lemma span_ow_on_typeclass: 
  assumes \<open>csubspace U\<close>
  assumes \<open>B \<subseteq> U\<close>
  shows \<open>span_ow U plus 0 scaleC B = cspan B\<close>
proof -
  have \<open>span_ow U plus 0 scaleC B = (\<lambda>x. csubspace x \<and> x \<subseteq> U) hull B\<close>
    using assms 
    by (auto simp add: span_ow_def hull_ow_nondegenerate[where x=U] csubspace_raw_def 
        simp flip: csubspace_ud)
  also have \<open>(\<lambda>x. csubspace x \<and> x \<subseteq> U) hull B = cspan B\<close>
    apply (rule hull_unique)
    using assms(2) complex_vector.span_superset apply force
    by (simp_all add: assms complex_vector.span_minimal)
  finally show ?thesis
    by -
qed

lemma (in Modules.module) span_ud[unoverload_def]: \<open>span = span_ow UNIV plus 0 scale\<close>
  by (auto intro!: ext simp: span_def span_ow_def
      module_subspace_ud hull_ow_ud)

lemmas cspan_ud[unoverload_def] = complex_vector.span_ud

lemma span_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>(rel_set T ===> (T ===> T ===> T) ===> T ===> ((=) ===> T ===> T) ===> rel_set T ===> rel_set T)
           span_ow span_ow\<close>
  unfolding span_ow_def
  by transfer_prover

subsubsection \<open>\<^const>\<open>islimpt\<close>\<close>

definition \<open>islimpt_ow U open x S \<longleftrightarrow> (\<forall>T\<subseteq>U. x\<in>T \<longrightarrow> open T \<longrightarrow> (\<exists>y\<in>S. y\<in>T \<and> y\<noteq>x))\<close> for "open"

lemma islimpt_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>(rel_set T ===> (rel_set T ===> (=)) ===> T ===> rel_set T ===> (\<longleftrightarrow>)) islimpt_ow islimpt_ow\<close>
  unfolding islimpt_ow_def make_parametricity_proof_friendly
  by transfer_prover

definition \<open>islimptin T x S \<longleftrightarrow> x \<in> topspace T \<and> (\<forall>V. x \<in> V \<longrightarrow> openin T V \<longrightarrow> (\<exists>y\<in>S. y \<in> V \<and> y \<noteq> x))\<close>

lemma islimpt_ow_from_topology: \<open>islimpt_ow (topspace T) (openin T) x S \<longleftrightarrow> islimptin T x S \<or> x \<notin> topspace T\<close>
  apply (cases \<open>x \<in> topspace T\<close>)
   apply (simp_all add: islimpt_ow_def islimptin_def Pow_def)
  by blast+

subsubsection \<open>\<^const>\<open>closure\<close>\<close>

definition \<open>closure_ow U open S = S \<union> {x\<in>U. islimpt_ow U open x S}\<close> for "open"

lemma closure_ow_with_typeclass[simp]: 
  \<open>closure_ow X (openin (top_of_set X)) S = (X \<inter> closure (X \<inter> S)) \<union> S\<close>
proof -
  have \<open>closure_ow X (openin (top_of_set X)) S = (top_of_set X) closure_of S \<union> S\<close>
    apply (simp add: closure_ow_def islimpt_ow_def closure_of_def)
    apply safe
     apply (meson PowI openin_imp_subset)
    by auto
  also have \<open>\<dots> = (X \<inter> closure (X \<inter> S)) \<union> S\<close>
    by (simp add: closure_of_subtopology)
  finally show ?thesis
    by -
qed

lemma closure_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique T\<close>
  shows \<open>(rel_set T ===> (rel_set T ===> (=)) ===> rel_set T ===> rel_set T) closure_ow closure_ow\<close>
  unfolding closure_ow_def make_parametricity_proof_friendly
  by transfer_prover

lemma closure_ow_from_topology: \<open>closure_ow (topspace T) (openin T) S = T closure_of S\<close> if \<open>S \<subseteq> topspace T\<close>
  using that apply (auto simp: closure_ow_def islimpt_ow_from_topology in_closure_of)
  apply (meson in_closure_of islimptin_def)
  by (metis islimptin_def)

lemma closure_ud[unoverload_def]: \<open>closure = closure_ow UNIV open\<close>
  unfolding closure_def closure_ow_def islimpt_def islimpt_ow_def by auto

subsection \<open>\<^const>\<open>continuous\<close>\<close>

lemma continuous_on_ow_from_topology: \<open>continuous_on_ow (topspace T) (topspace U) (openin T) (openin U) (topspace T) f \<longleftrightarrow> continuous_map T U f\<close>
  if \<open>f ` topspace T \<subseteq> topspace U\<close>
  apply (simp add: continuous_on_ow_def continuous_map_def)
  apply safe
    apply (meson image_subset_iff that)
   apply (smt (verit) Collect_mono_iff Int_def inf_absorb1 mem_Collect_eq openin_subopen openin_subset vimage_eq)
  by blast

subsection \<open>\<^const>\<open>is_onb\<close>\<close>

definition
  \<open>is_onb_ow U scaleC plus zero norm open cinner E \<longleftrightarrow> is_ortho_set_ow zero cinner E \<and> (\<forall>b\<in>E. norm b = 1) \<and> 
    closure_ow U open (span_ow U plus zero scaleC E) = U\<close>
  for U scaleC plus zero norm "open" cinner

lemma is_onb_ow_parametric[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique A\<close>
  shows \<open>(rel_set A ===>
     ((=) ===> A ===> A) ===>
     (A ===> A ===> A) ===>
     A ===>
     (A ===> (=)) ===> (rel_set A ===> (=)) ===> (A ===> A ===> (=)) ===> rel_set A ===> (=))
     is_onb_ow is_onb_ow\<close>
  unfolding is_onb_ow_def
  by transfer_prover

lemma is_onb_ud[unoverload_def]:
  \<open>is_onb = is_onb_ow UNIV scaleC plus 0 norm open cinner\<close>
  unfolding is_onb_def is_onb_ow_def
  apply (subst asm_rl[of \<open>\<And>E. ccspan E = \<top> \<longleftrightarrow> closure (cspan E) = UNIV\<close>, rule_format])
   apply (transfer, rule)
  unfolding unoverload_def
  apply transfer by auto


subsection \<open>Transferring theorems\<close>

lemma closure_of_eqI:
  fixes f g :: \<open>'a \<Rightarrow> 'b\<close> and T :: \<open>'a topology\<close> and U :: \<open>'b topology\<close>
  assumes hausdorff: \<open>Hausdorff_space U\<close>
  assumes f_eq_g: \<open>\<And>x. x \<in> S \<Longrightarrow> f x = g x\<close>
  assumes x: \<open>x \<in> T closure_of S\<close>
  assumes f: \<open>continuous_map T U f\<close> and g: \<open>continuous_map T U g\<close>
  shows \<open>f x = g x\<close>
proof -
  have \<open>topspace T \<noteq> {}\<close>
    by (metis assms(3) equals0D in_closure_of)
  have \<open>topspace U \<noteq> {}\<close>
    using \<open>topspace T \<noteq> {}\<close> assms(5) continuous_map_image_subset_topspace by blast

  {
    assume "\<exists>(Rep :: 't \<Rightarrow> 'a) Abs. type_definition Rep Abs (topspace T)"
    then interpret T: local_typedef \<open>topspace T\<close> \<open>TYPE('t)\<close>
      by unfold_locales
    assume "\<exists>(Rep :: 'u \<Rightarrow> 'b) Abs. type_definition Rep Abs (topspace U)"
    then interpret U: local_typedef \<open>topspace U\<close> \<open>TYPE('u)\<close>
      by unfold_locales

    note on_closure_eqI
    note this[unfolded unoverload_def]
    note this[unoverload_type 'b, unoverload_type 'a]
    note this[unfolded unoverload_def]
    note this[where 'a='t and 'b='u]
    note this[untransferred]
    note this[where f=f and g=g and S=\<open>S \<inter> topspace T\<close> and x=x and ?open="openin T" and opena=\<open>openin U\<close>]
    note this[simplified]
  }
  note * = this[cancel_type_definition, OF \<open>topspace T \<noteq> {}\<close>, cancel_type_definition, OF \<open>topspace U \<noteq> {}\<close>]

  have 2: \<open>f ` topspace T \<subseteq> topspace U\<close>
  by (meson assms(4) continuous_map_image_subset_topspace)
  have 3: \<open>g ` topspace T \<subseteq> topspace U\<close>
    by (simp add: continuous_map_image_subset_topspace g)
  have 4: \<open>x \<in> topspace T\<close>
    by (meson assms(3) in_closure_of)
  have 5: \<open>topological_space_ow (topspace T) (openin T)\<close>
    by simp
  have 6: \<open>t2_space_ow (topspace U) (openin U)\<close>
    by (simp add: hausdorff)
  from x have \<open>x \<in> T closure_of (S \<inter> topspace T)\<close>
    by (metis closure_of_restrict inf_commute)
  then have 7: \<open>x \<in> closure_ow (topspace T) (openin T) (S \<inter> topspace T)\<close>
    by (simp add: closure_ow_from_topology)
  have 8: \<open>continuous_on_ow (topspace T) (topspace U) (openin T) (openin U) (topspace T) f\<close>
     by (meson "2" continuous_on_ow_from_topology f)
  have 9: \<open>continuous_on_ow (topspace T) (topspace U) (openin T) (openin U) (topspace T) g\<close>
    by (simp add: "3" continuous_on_ow_from_topology g)

  show ?thesis
    apply (rule * )
    using 2 3 4 5 6 f_eq_g 7 8 9 by auto
qed


lemma orthonormal_subspace_basis_exists:
  fixes S :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_ortho_set S\<close> and norm: \<open>\<And>x. x\<in>S \<Longrightarrow> norm x = 1\<close> and \<open>S \<subseteq> space_as_set V\<close>
  shows \<open>\<exists>B. B \<supseteq> S \<and> is_ortho_set B \<and> (\<forall>x\<in>B. norm x = 1) \<and> ccspan B = V\<close>
proof -
  {
    assume "\<exists>(Rep :: 't \<Rightarrow> 'a) Abs. type_definition Rep Abs (space_as_set V)"
    then interpret T: local_typedef \<open>space_as_set V\<close> \<open>TYPE('t)\<close>
      by unfold_locales

    note orthonormal_basis_exists
    note this[unfolded unoverload_def]
    note this[unoverload_type 'a]
    note this[unfolded unoverload_def]
    note this[where 'a='t]
    note this[untransferred]
    note this[where plus=plus and scaleC=scaleC and scaleR=scaleR and zero=0 and minus=minus
        and uminus=uminus and sgn=sgn and S=S and norm=norm and cinner=cinner and dist=dist
        and ?open=\<open>openin (top_of_set (space_as_set V))\<close>
        and uniformity=\<open>uniformity_on (space_as_set V)\<close>]
    note this[simplified Domainp_rel_filter prod.Domainp_rel T.Domainp_cr_S]
  }    
  note * = this[cancel_type_definition]
  have 1: \<open>uniformity_on (space_as_set V)
    \<le> principal (Collect (pred_prod (\<lambda>x. x \<in> space_as_set V) (\<lambda>x. x \<in> space_as_set V)))\<close>
    by (auto simp: uniformity_dist intro!: le_infI2)
  have \<open>\<exists>B\<in>{A. \<forall>x\<in>A. x \<in> space_as_set V}.
     S \<subseteq> B \<and> is_onb_ow (space_as_set V) (*\<^sub>C) (+) 0 norm (openin (top_of_set (space_as_set V))) (\<bullet>\<^sub>C) B\<close>
    apply (rule * )
    using \<open>S \<subseteq> space_as_set V\<close> \<open>is_ortho_set S\<close>
    by (auto simp flip: unoverload_def
        intro!: complex_vector.subspace_scale real_vector.subspace_scale csubspace_is_subspace
        csubspace_nonempty complex_vector.subspace_add complex_vector.subspace_diff
        complex_vector.subspace_neg sgn_in_spaceI 1 norm)

  then obtain B where \<open>B \<subseteq> space_as_set V\<close> and \<open>S \<subseteq> B\<close>
    and is_onb: \<open>is_onb_ow (space_as_set V) (*\<^sub>C) (+) 0 norm (openin (top_of_set (space_as_set V))) (\<bullet>\<^sub>C) B\<close>
    by auto

  from \<open>B \<subseteq> space_as_set V\<close>
  have [simp]: \<open>cspan B \<inter> space_as_set V = cspan B\<close>
    by (smt (verit) basic_trans_rules(8) ccspan.rep_eq ccspan_leqI ccspan_superset complex_vector.span_span inf_absorb1 less_eq_ccsubspace.rep_eq)
  then have [simp]: \<open>space_as_set V \<inter> cspan B = cspan B\<close>
    by blast
  from \<open>B \<subseteq> space_as_set V\<close>
  have [simp]: \<open>space_as_set V \<inter> closure (cspan B) = closure (cspan B)\<close>
    by (metis Int_absorb1 ccspan.rep_eq ccspan_leqI less_eq_ccsubspace.rep_eq)
  have [simp]: \<open>closure X \<union> X = closure X\<close> for X :: \<open>'z::topological_space set\<close>
    using closure_subset by blast

  from is_onb have \<open>is_ortho_set B\<close>
    by (auto simp: is_onb_ow_def unoverload_def)

  moreover from is_onb have \<open>norm x = 1\<close> if \<open>x \<in> B\<close> for x
    by (auto simp: is_onb_ow_def that)

  moreover from is_onb have \<open>closure (cspan B) = space_as_set V\<close>
    by (simp add: is_onb_ow_def \<open>B \<subseteq> space_as_set V\<close>
        closure_ow_with_typeclass span_ow_on_typeclass flip: unoverload_def)
  then have \<open>ccspan B = V\<close>
    by (simp add: ccspan.abs_eq space_as_set_inverse)

  ultimately show ?thesis
    using \<open>S \<subseteq> B\<close> by auto
qed

lemma has_sum_in_comm_additive_general:
  fixes f :: \<open>'a \<Rightarrow> 'b :: comm_monoid_add\<close>
    and g :: \<open>'b \<Rightarrow> 'c :: comm_monoid_add\<close>
  assumes T0[simp]: \<open>0 \<in> topspace T\<close> and Tplus[simp]: \<open>\<And>x y. x \<in> topspace T \<Longrightarrow> y \<in> topspace T \<Longrightarrow> x+y \<in> topspace T\<close>
  assumes Uplus[simp]: \<open>\<And>x y. x \<in> topspace U \<Longrightarrow> y \<in> topspace U \<Longrightarrow> x+y \<in> topspace U\<close>
  assumes grange: \<open>g ` topspace T \<subseteq> topspace U\<close>
  assumes g0: \<open>g 0 = 0\<close>
  assumes frange: \<open>f ` S \<subseteq> topspace T\<close>
  assumes gcont: \<open>filterlim g (nhdsin U (g l)) (atin T l)\<close>
  assumes gadd: \<open>\<And>x y. x \<in> topspace T \<Longrightarrow> y \<in> topspace T \<Longrightarrow> g (x+y) = g x + g y\<close>
  assumes sumf: \<open>has_sum_in T f S l\<close>
  shows \<open>has_sum_in U (g o f) S (g l)\<close>
proof -
  define f' where \<open>f' x = (if x \<in> S then f x else 0)\<close> for x
  have \<open>topspace T \<noteq> {}\<close>
    using T0 by blast
  then have \<open>topspace U \<noteq> {}\<close>
    using grange by blast
  {
    assume "\<exists>(Rep :: 't \<Rightarrow> 'b) Abs. type_definition Rep Abs (topspace T)"
    then interpret T: local_typedef \<open>topspace T\<close> \<open>TYPE('t)\<close>
      by unfold_locales
    assume "\<exists>(Rep :: 'u \<Rightarrow> 'c) Abs. type_definition Rep Abs (topspace U)"
    then interpret U: local_typedef \<open>topspace U\<close> \<open>TYPE('u)\<close>
      by unfold_locales

    note [[show_types]]
    note has_sum_comm_additive_general
    note this[unfolded unoverload_def]
    note this[unoverload_type 'b, unoverload_type 'c]
    note this[where 'b='t and 'c='u and 'a='a]
    note this[unfolded unoverload_def]
    thm this[no_vars]
    note this[untransferred]
    note this[where f=g and g=f' and zero=0 and zeroa=0 and plus=plus and plusa=plus
        and ?open=\<open>openin U\<close> and opena=\<open>openin T\<close> and x=l and S=S and T=\<open>topspace T\<close>]
    note this[simplified]
  }
  note * = this[cancel_type_definition, OF \<open>topspace T \<noteq> {}\<close>, cancel_type_definition, OF \<open>topspace U \<noteq> {}\<close>]

  have f'T[simp]: \<open>f' x \<in> topspace T\<close> for x
    using frange f'_def by force
  have [simp]: \<open>l \<in> topspace T\<close>
    using sumf has_sum_in_topspace by blast
  have [simp]: \<open>x \<in> topspace T \<Longrightarrow> g x \<in> topspace U\<close> for x
    using grange by auto
  have sumf'T: \<open>(\<Sum>x\<in>F. f' x) \<in> topspace T\<close> if \<open>finite F\<close> for F
    using that apply induction
    by auto
  have [simp]: \<open>(\<Sum>x\<in>F. f x) \<in> topspace T\<close> if \<open>F \<subseteq> S\<close> for F
    using that apply (induction F rule:infinite_finite_induct)
      apply auto
    by (metis Tplus f'T f'_def)
  have sum_gf: \<open>(\<Sum>x\<in>F. g (f' x)) = g (\<Sum>x\<in>F. f' x)\<close> 
    if \<open>finite F\<close> and \<open>F \<subseteq> S\<close> for F
  proof -
    have \<open>(\<Sum>x\<in>F. g (f' x)) = (\<Sum>x\<in>F. g (f x))\<close>
      apply (rule sum.cong)
      using frange that by (auto simp: f'_def)
    also have \<open>\<dots> = g (\<Sum>x\<in>F. f x)\<close>
      using \<open>finite F\<close> \<open>F \<subseteq> S\<close> apply induction
      using g0 frange apply auto
      apply (subst gadd)
      by (auto simp: f'_def)
    also have \<open>\<dots> = g (\<Sum>x\<in>F. f' x)\<close>
      apply (rule arg_cong[where f=g])
      apply (rule sum.cong)
      using that by (auto simp: f'_def)
    finally show ?thesis
      by -
  qed
  from sumf have sumf': \<open>has_sum_in T f' S l\<close>
    apply (rule has_sum_in_cong[THEN iffD2, rotated])
    unfolding f'_def by auto
  have [simp]: \<open>g l \<in> topspace U\<close>
    using grange by auto
  from gcont have contg': \<open>filterlim g (nhdsin U (g l)) (nhdsin T l \<sqinter> principal (topspace T - {l}))\<close>
    apply (rule filterlim_cong[THEN iffD1, rotated -1])
      apply (rule refl)
     apply (simp add: atin_def)
    by (auto intro!: exI simp add: eventually_atin)
  from T0 grange g0 have [simp]: \<open>0 \<in> topspace U\<close>
    by auto

  have [simp]: 
    \<open>comm_monoid_ow (topspace T) (+) 0\<close>
    \<open>comm_monoid_ow (topspace U) (+) 0\<close>
    by (simp_all add: comm_monoid_ow_def abel_semigroup_ow_def
        semigroup_ow_def plus_ow_def semigroup_ow_axioms_def
        comm_monoid_ow_axioms_def Groups.add_ac abel_semigroup_ow_axioms_def)

  have \<open>has_sum_ow (topspace U) (+) 0 (openin U) (g \<circ> f') S (g l)\<close>
    apply (rule *)
    by (auto simp: topological_space_ow_from_topology sum_gf sumf'
        sum_ud[symmetric] at_within_ow_topology has_sum_ow_topology
        contg' sumf'T)

  then have \<open>has_sum_in U (g \<circ> f') S (g l)\<close>
    apply (rule has_sum_ow_topology[THEN iffD1, rotated -1])
    by simp_all
  then have \<open>has_sum_in U (g \<circ> f') S (g l)\<close>
    by simp
  then show ?thesis
    apply (rule has_sum_in_cong[THEN iffD1, rotated])
    unfolding f'_def using frange grange by auto
qed

lemma has_sum_in_comm_additive:
  fixes f :: \<open>'a \<Rightarrow> 'b :: ab_group_add\<close>
    and g :: \<open>'b \<Rightarrow> 'c :: ab_group_add\<close>
  assumes \<open>topspace T = UNIV\<close> and \<open>topspace U = UNIV\<close>
  assumes \<open>Modules.additive g\<close>
  assumes gcont: \<open>continuous_map T U g\<close>
  assumes sumf: \<open>has_sum_in T f S l\<close>
  shows \<open>has_sum_in U (g o f) S (g l)\<close>
  apply (rule has_sum_in_comm_additive_general[where T=T and U=U])
  using assms
  by (auto simp: additive.zero Modules.additive_def intro!: continuous_map_is_continuous_at_point)


section \<open>Stuff relying on the above lifting\<close>

(* TODO: Migrate this into Bounded_Operators session,
   and change "some_chilbert_basis" there to to abbreviate "some_onb_of UNIV" *)
definition \<open>some_onb_of X = (SOME B. is_ortho_set B \<and> (\<forall>b\<in>B. norm b = 1) \<and> ccspan B = X)\<close>

lemma
  fixes X :: \<open>'a::chilbert_space ccsubspace\<close>
  shows some_onb_of_is_ortho_set[iff]: \<open>is_ortho_set (some_onb_of X)\<close>
    and some_onb_of_norm1: \<open>b \<in> some_onb_of X \<Longrightarrow> norm b = 1\<close>
    and some_onb_of_ccspan[simp]: \<open>ccspan (some_onb_of X) = X\<close>
proof -
  let ?P = \<open>\<lambda>B. is_ortho_set B \<and> (\<forall>b\<in>B. norm b = 1) \<and> ccspan B = X\<close>
  have \<open>Ex ?P\<close>
    using orthonormal_subspace_basis_exists[where S=\<open>{}\<close> and V=X]
    by auto
  then have \<open>?P (some_onb_of X)\<close>
    by (simp add: some_onb_of_def verit_sko_ex)
  then show is_ortho_set_some_onb_of: \<open>is_ortho_set (some_onb_of X)\<close>
    and \<open>b \<in> some_onb_of X \<Longrightarrow> norm b = 1\<close>
    and \<open>ccspan (some_onb_of X) = X\<close>
    by auto
qed

lemma ccsubspace_as_whole_type:
  fixes X :: \<open>'a::chilbert_space ccsubspace\<close>
  assumes \<open>X \<noteq> 0\<close>
  shows \<open>let 'b::type = some_onb_of X in
         \<exists>U::'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a. isometry U \<and> U *\<^sub>S \<top> = X\<close>
proof with_type_intro
  show \<open>some_onb_of X \<noteq> {}\<close>
    using some_onb_of_ccspan[of X] assms
    by (auto simp del: some_onb_of_ccspan)
  fix Rep :: \<open>'b \<Rightarrow> 'a\<close> and Abs
  assume \<open>bij_betw Rep UNIV (some_onb_of X)\<close>
  then interpret type_definition Rep \<open>inv Rep\<close> \<open>some_onb_of X\<close>
    by (simp add: type_definition_bij_betw_iff)
  define U where \<open>U = cblinfun_extension (range ket) (Rep o inv ket)\<close>
  have [simp]: \<open>Rep i \<bullet>\<^sub>C Rep j = 0\<close> if \<open>i \<noteq> j\<close> for i j
    using Rep some_onb_of_is_ortho_set[unfolded is_ortho_set_def] that
    by (smt (verit) Rep_inverse)
  moreover have [simp]: \<open>norm (Rep i) = 1\<close> for i
    using Rep[of i] some_onb_of_norm1
    by auto
  ultimately have \<open>cblinfun_extension_exists (range ket) (Rep o inv ket)\<close>
    apply (rule_tac cblinfun_extension_exists_ortho)
    by auto
  then have U_ket[simp]: \<open>U (ket i) = Rep i\<close> for i
    by (auto simp: cblinfun_extension_apply U_def)
  have \<open>isometry U\<close>
    apply (rule orthogonal_on_basis_is_isometry[where B=\<open>range ket\<close>])
    by (auto simp: cinner_ket simp flip: cnorm_eq_1)
  moreover have \<open>U *\<^sub>S ccspan (range ket) = X\<close>
    apply (subst cblinfun_image_ccspan)
    by (simp add: Rep_range image_image)
  ultimately show \<open>\<exists>U :: 'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a. isometry U \<and> U *\<^sub>S \<top> = X\<close>
    by auto
qed

lemma some_onb_of_0[simp]: \<open>some_onb_of (0 :: 'a::chilbert_space ccsubspace) = {}\<close>
proof -
  have no0: \<open>0 \<notin> some_onb_of (0 :: 'a ccsubspace)\<close>
    using some_onb_of_norm1
    by fastforce
  have \<open>ccspan (some_onb_of 0) = (0 :: 'a ccsubspace)\<close>
    by simp
  then have \<open>some_onb_of 0 \<subseteq> space_as_set (0 :: 'a ccsubspace)\<close>
    by (metis ccspan_superset)
  also have \<open>\<dots> = {0}\<close>
    by simp
  finally show ?thesis
    using no0
    by blast
qed

lemma some_onb_of_finite_dim:
  fixes S :: \<open>'a::chilbert_space ccsubspace\<close>
  assumes \<open>finite_dim_ccsubspace S\<close>
  shows \<open>finite (some_onb_of S)\<close>
proof -
  from assms obtain C where CS: \<open>cspan C = space_as_set S\<close> and \<open>finite C\<close>
    by (meson cfinite_dim_subspace_has_basis csubspace_space_as_set finite_dim_ccsubspace.rep_eq)
  then show \<open>finite (some_onb_of S)\<close>
    using ccspan_superset complex_vector.independent_span_bound is_ortho_set_cindependent by fastforce
qed

lemma some_onb_of_in_space[iff]:
  fixes S :: \<open>'a::chilbert_space ccsubspace\<close>
  shows \<open>some_onb_of S \<subseteq> space_as_set S\<close>
  using ccspan_superset by fastforce



lemma sum_some_onb_of_butterfly:
  fixes S :: \<open>'a::chilbert_space ccsubspace\<close>
  assumes \<open>finite_dim_ccsubspace S\<close>
  shows \<open>(\<Sum>x\<in>some_onb_of S. butterfly x x) = Proj S\<close>
proof -
  obtain B where onb_S_in_B: \<open>some_onb_of S \<subseteq> B\<close> and \<open>is_onb B\<close>
    apply atomize_elim
    apply (rule orthonormal_basis_exists)
    by (simp_all add: some_onb_of_norm1)
  have S_ccspan: \<open>S = ccspan (some_onb_of S)\<close>
    by simp

  show ?thesis
  proof (rule cblinfun_eq_gen_eqI[where G=B])
    show \<open>ccspan B = \<top>\<close>
      using \<open>is_onb B\<close> is_onb_def by blast
    fix b assume \<open>b \<in> B\<close>
    show \<open>(\<Sum>x\<in>some_onb_of S. selfbutter x) *\<^sub>V b = Proj S *\<^sub>V b\<close>
    proof (cases \<open>b \<in> some_onb_of S\<close>)
      case True
      have \<open>(\<Sum>x\<in>some_onb_of S. selfbutter x) *\<^sub>V b = (\<Sum>x\<in>some_onb_of S. selfbutter x *\<^sub>V b)\<close>
        using cblinfun.sum_left by blast
      also have \<open>\<dots> = b\<close>
        apply (subst sum_single[where i=b])
        using True apply (auto intro!: simp add: assms some_onb_of_finite_dim) 
        using is_ortho_set_def apply fastforce
        using cnorm_eq_1 some_onb_of_norm1 by force
      also have \<open>\<dots> = Proj S *\<^sub>V b\<close>
        apply (rule Proj_fixes_image[symmetric])
        using True some_onb_of_in_space by blast
      finally show ?thesis
        by -
    next
      case False
      have *: \<open>is_orthogonal x b\<close> if \<open>x \<in> some_onb_of S\<close> and \<open>x \<noteq> 0\<close> for x
      proof -
        have \<open>x \<in> B\<close>
          using onb_S_in_B that(1) by fastforce
        moreover note \<open>b \<in> B\<close>
        moreover have \<open>x \<noteq> b\<close>
          using False that(1) by blast
        moreover note \<open>is_onb B\<close>
        ultimately show \<open>is_orthogonal x b\<close>
          by (simp add: is_onb_def is_ortho_set_def)
      qed
      have \<open>(\<Sum>x\<in>some_onb_of S. selfbutter x) *\<^sub>V b = (\<Sum>x\<in>some_onb_of S. selfbutter x *\<^sub>V b)\<close>
        using cblinfun.sum_left by blast
      also have \<open>\<dots> = 0\<close>
        by (auto intro!: sum.neutral simp: * )
      also have \<open>\<dots> = Proj S *\<^sub>V b\<close>
        apply (rule Proj_0_compl[symmetric])
        apply (subst S_ccspan)
        apply (rule mem_ortho_ccspanI)
        using "*" cinner_zero_right is_orthogonal_sym by blast
      finally show ?thesis 
        by -
    qed
  qed
qed


lemma cdim_infinite_0:
  assumes \<open>\<not> cfinite_dim S\<close>
  shows \<open>cdim S = 0\<close>
proof -
  from assms have not_fin_cspan: \<open>\<not> cfinite_dim (cspan S)\<close>
    using cfinite_dim_def cfinite_dim_subspace_has_basis complex_vector.span_superset by fastforce
  obtain B where \<open>cindependent B\<close> and \<open>cspan S = cspan B\<close>
    using csubspace_has_basis by blast
  with not_fin_cspan have \<open>infinite B\<close>
    by auto
  then have \<open>card B = 0\<close>
    by force
  have \<open>cdim (cspan S) = 0\<close> 
    apply (rule complex_vector.dim_unique[of B])
       apply (auto intro!: simp add: \<open>cspan S = cspan B\<close> complex_vector.span_superset)
    using \<open>cindependent B\<close> \<open>card B = 0\<close> by auto
  then show ?thesis
    by simp
qed


lemma some_onb_of_card:
  fixes S :: \<open>'a::chilbert_space ccsubspace\<close>
  shows \<open>card (some_onb_of S) = cdim (space_as_set S)\<close>
proof (cases \<open>finite_dim_ccsubspace S\<close>)
  case True
  show ?thesis
    apply (rule complex_vector.dim_eq_card[symmetric])
     apply (auto simp: is_ortho_set_cindependent)
     apply (metis True ccspan_finite some_onb_of_ccspan complex_vector.span_clauses(1) some_onb_of_finite_dim)
    by (metis True ccspan_finite some_onb_of_ccspan complex_vector.span_eq_iff csubspace_space_as_set some_onb_of_finite_dim)
next
  case False
  then have \<open>cdim (space_as_set S) = 0\<close>
    by (simp add: cdim_infinite_0 finite_dim_ccsubspace.rep_eq)
  moreover from False have \<open>infinite (some_onb_of S)\<close>
    using ccspan_finite_dim by fastforce
  ultimately show ?thesis 
    by simp
qed

end
