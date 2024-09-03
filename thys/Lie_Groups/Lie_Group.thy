(*  Title:       Lie_Group
    Author:      Richard Schmoetten <richard.schmoetten@ed.ac.uk>, 2024
    Maintainer:  Richard Schmoetten <richard.schmoetten@ed.ac.uk>
*)

theory Lie_Group

imports
  "HOL-Analysis.Analysis"
  "HOL-Eisbach.Eisbach"
  More_Manifolds
begin


section \<open>Definition of Lie Groups (as Locales)\<close>

text \<open>Some abbreviations for easier reading first. A binary operation is colloquially said
  continuous/smooth/differentiable on a manifold $M$ if it is so on the product manifold $M^2$.
  We fix the types of the binary operations in two of the definitions below, as the target space
  is made explicit only in the third (the one using \<^term>\<open>diff \<infinity>\<close>).\<close>

abbreviation (input) "continuous_on_product_manifold charts (binop::'a\<Rightarrow>'a\<Rightarrow>'a::{second_countable_topology,t2_space}) \<equiv>
  continuous_on (c_manifold_prod.carrier charts charts) (\<lambda>(a,b). binop a b)"
abbreviation (input) "smooth_on_product_manifold charts (binop::'a\<Rightarrow>'a\<Rightarrow>'a::{second_countable_topology,real_normed_vector}) \<equiv>
  smooth_on (c_manifold_prod.carrier charts charts) (\<lambda>(a,b). binop a b)"
abbreviation (input) "diff_on_product_manifold charts binop \<equiv>
  diff \<infinity> (c_manifold_prod.prod_charts charts charts) charts (\<lambda>(a,b). binop a b)"


subsection \<open>Topological groups\<close>

text \<open>A group with a topology, such that the group operations are continuous.\<close>

locale topological_group =
  manifold charts + group_on_with carrier tms tms_one dvsn invs
  for charts::"('a::{t2_space,second_countable_topology}, 'e::euclidean_space) chart set"
    and tms tms_one dvsn invs +
  assumes cts_mult: "continuous_on_product_manifold charts tms"
    and cts_inv: "continuous_on carrier invs"


subsection \<open>Lie groups\<close>

text \<open>
  A Lie group is a group on a set, but instead of a carrier set, we specify
  a set of charts, which imply the carrier set as a (smooth) manifold $M$.
  Internally, we consider the product manifold, to define smoothness of multiplication $M \times M \to M$.
  It may be overkill to keep inverse and division separate, considering \<^locale>\<open>group_on_with\<close> includes an axiom
  to relate the two, but this is how it's done in other Isabelle theories, so I'll keep it.
  It gives some extra flexibility, and an intro lemma using the more traditional group parameters
  (an operation, and an identity) and axioms is already provided in @{thm group_on_with_alt_intro}.
\<close>
locale lie_group =
  c_manifold charts \<infinity> + group_on_with carrier tms tms_one dvsn invs
  for charts::"('a::{t2_space,second_countable_topology}, 'e::euclidean_space) chart set"
    and tms tms_one dvsn invs +
  assumes smooth_mult: "diff_on_product_manifold charts tms"
    and smooth_inv: "diff \<infinity> charts charts invs"

text \<open>
  We can make a shortened locale for Lie groups where the inversion and division are implied.
  This does \emph{not} say anything about the implementation of inversion or division outside
  the carrier set. See also \<^locale>\<open>Groups_On_With.grp_on\<close>.
\<close>
locale lie_grp =
  c_manifold charts \<infinity> + grp_on carrier tms one
  for charts::"('a::{t2_space,second_countable_topology}, 'e::euclidean_space) chart set"
    and tms one +
  \<comment> \<open>multiplication and inversion are smooth\<close>
  assumes smooth_mult: "diff_on_product_manifold charts tms"
    and smooth_inv: "diff \<infinity> charts charts invs"
begin

lemma is_lie_group: "lie_group charts tms one mns invs"
  unfolding lie_group_def lie_group_axioms_def
  by (auto simp: c_manifold_axioms smooth_mult is_group_on_with smooth_inv)

sublocale lie_group charts tms one mns invs
  using is_lie_group .

end

lemma lie_group_imp_lie_grp:
  assumes "lie_group charts pls one any_mns any_invs"
  shows "lie_grp charts pls one"
  unfolding lie_grp_def lie_grp_axioms_def apply (intro conjI)
  subgoal using assms lie_group_def by blast
  subgoal
    using assms unfolding grp_on_def grp_on_axioms_def lie_group_def group_on_with_def group_on_with_axioms_def
    by (meson assms group_on_with.right_minus lie_group.axioms(2))
  subgoal using assms unfolding lie_group_def lie_group_axioms_def by simp
  subgoal using assms unfolding lie_group_def lie_group_axioms_def
    by (smt (verit, ccfv_threshold) \<open>grp_on (manifold.carrier charts) pls one\<close> diff.diff_cong
      group_on_with.inv_is_unique group_on_with.right_minus group_on_with.uminus_mem grp_on.is_group_on_with)
  done

text \<open>
  We give a few intro rules for the \<open>lie_group\<close> predicate, as well as an Eisbach method for further
  breaking down the proof of smoothness of the multiplication and inversion maps. This should
  lead to fairly organised proofs that some structure is a \<^locale>\<open>lie_group\<close>.
  In general, I would prefer \<open>group_manifold_imp_lie_group2\<close> to \<open>group_manifold_imp_lie_group\<close>.
\<close>

\<comment> \<open>This lemma is mostly here to be reproved with restrictions to the allowed manifold,
  which would simplify the applicable definition of smoothness.
  E.g. if the manifold is a Euclidean space,
  \<open>diff \<infinity>\<close> is just the standard analysis notion of "infinitely differentiable", i.e. \<open>smooth_on\<close>.\<close>
lemma group_manifold_imp_lie_group [intro]:
  assumes is_manifold: "c_manifold c \<infinity>"
    and is_group: "group_on_with (\<Union>(domain ` c)) tms tms_1 dvsn invs"
    and smooth_mult: "diff \<infinity> (c_manifold_prod.prod_charts c c) c (\<lambda>(a,b). tms a b)"
    and smooth_inv: "diff \<infinity> c c invs"
  shows "lie_group c tms tms_1 dvsn invs"
  unfolding lie_group_def manifold.carrier_def lie_group_axioms_def
  by (simp_all add: c_manifold_prod_def is_manifold is_group smooth_inv smooth_mult)

lemma group_manifold_imp_lie_group2 [intro]:
  assumes is_manifold: "c_manifold c \<infinity>"
    and is_group: "group_on_with (\<Union>(domain ` c)) tms tms_1 dvsn invs"
    and smooth_mult: "diff_axioms \<infinity> (c_manifold_prod.prod_charts c c) c (\<lambda>(a,b). tms a b)"
    and smooth_inv: "diff_axioms \<infinity> c c invs"
  shows "lie_group c tms tms_1 dvsn invs"
  by (auto intro!: c_manifolds.intro diff.intro simp: assms c_manifold_prod.c_manifold_atlas_product c_manifold_prod_def)

lemma lie_grpI [intro]:
  fixes tms tms_1 c
  defines "invs \<equiv> grp_on.invs (\<Union>(domain ` c)) tms tms_1"
  assumes is_manifold: "c_manifold c \<infinity>"
    and is_group: "grp_on (\<Union>(domain ` c)) tms tms_1"
    and smooth_mult: "diff_axioms \<infinity> (c_manifold_prod.prod_charts c c) c (\<lambda>(a,b). tms a b)"
    and smooth_inv: "diff_axioms \<infinity> c c invs"
  shows "lie_grp c tms tms_1"
  by (metis group_manifold_imp_lie_group2 grp_on.is_group_on_with invs_def is_group is_manifold
    lie_group_imp_lie_grp smooth_inv smooth_mult)

text \<open>A small method to unfold the axioms of differentiability of group operations.
  Allows for succinct goals to be stated while quickly unfolding to a useful level of technicality.\<close>
method unfold_diff_axioms = (
  unfold diff_axioms_def,
  rule allI,
  rule impI,
  (rule bexI)+,
  (rule conjI),
  rule_tac[2] conjI
)


subsection \<open>Some lemmas about Lie groups (and other needed results).\<close>
context lie_group begin

lemma obtain_chart_cover:
  assumes "S \<subseteq> carrier"
  obtains C where "\<forall>c\<in>C. c\<in>atlas" "\<forall>s\<in>S. \<exists>c\<in>C. s \<in> domain c"
  by (metis assms carrierE in_charts_in_atlas subset_iff)

lemma open_covered_by_charts:
  assumes "S \<subseteq> carrier" "open S"
  obtains C where "\<forall>c\<in>C. c\<in>atlas" "S = \<Union>{domain c | c. c\<in>C}"
proof -
  obtain C where C: "\<forall>c\<in>C. c\<in>atlas" "\<forall>s\<in>S. \<exists>c\<in>C. s \<in> domain c"
    using obtain_chart_cover assms by blast
  let ?restr_chart = "\<lambda>c. if domain c \<subseteq> S then c else restrict_chart S c"
  let ?C = "{?restr_chart c | c. c\<in>C}"
  have "\<forall>c\<in>?C. c\<in>atlas"
    using C(1) restrict_chart_in_atlas by auto
  moreover have "S = \<Union>{domain c | c. c\<in>?C}"
    using assms(2) domain_restrict_chart by (auto, metis C(2) Int_iff, fastforce)
  ultimately show ?thesis using that by presburger
qed

lemma lie_prod: "c_manifold_prod \<infinity> charts charts"
  by unfold_locales

interpretation lie_prod: c_manifold_prod \<infinity> charts charts
  by unfold_locales

lemma continuous_on_tms: 
  assumes "x \<in> carrier"
  shows "continuous_on carrier (\<lambda>y. tms x y)"
    and "continuous_on carrier (\<lambda>y. tms y x)"
proof -
  have cts_tms: "continuous_on lie_prod.carrier (\<lambda>(a, b). tms a b)"
    using lie_group_axioms diff.continuous_on unfolding lie_group_def lie_group_axioms_def by blast
  have tms_is_comp: "(tms x) = (\<lambda>(a, b). tms a b) \<circ> (\<lambda>y. (x,y))"
    by (simp add: comp_def)
  show "continuous_on carrier (\<lambda>y. tms x y)"
  proof -
    have cts_R: "continuous_on carrier (\<lambda>y. (x,y))"
      using continuous_on_Pair[OF continuous_on_const[of carrier x] continuous_on_id] .
    have pair_carrier: "Pair x ` carrier \<subseteq> lie_prod.carrier"
      unfolding image_def using lie_prod.prod_carrier assms by blast
    thus ?thesis
      using continuous_on_compose[OF cts_R] cts_tms tms_is_comp continuous_on_subset[OF _ pair_carrier]
      by metis
  qed
  show "continuous_on carrier (\<lambda>y. tms y x)"
  proof -
    have cts_L: "continuous_on carrier (\<lambda>y. (y,x))"
      using continuous_on_Pair[OF continuous_on_id continuous_on_const[of carrier x]] .
    have pair_carrier': "(\<lambda>y. (y,x)) ` carrier \<subseteq> lie_prod.carrier"
      unfolding image_def using lie_prod.prod_carrier assms by blast
    thus ?thesis
      using continuous_on_compose[OF cts_L] cts_tms tms_is_comp continuous_on_subset[OF _ pair_carrier']
      by force
  qed
qed

lemma diff_tms:
  assumes "x \<in> carrier"
  shows "diff \<infinity> charts charts (\<lambda>y. tms x y)"
    and "diff \<infinity> charts charts (\<lambda>y. tms y x)"
  subgoal
    using diff_compose[OF lie_prod.diff_left_Pair[OF assms] smooth_mult] diff.diff_cong by fastforce
  subgoal
    using diff_compose[OF lie_prod.diff_right_Pair[OF assms] smooth_mult] diff.diff_cong by fastforce
  done

lemma diff_tms_invs:
  assumes "x \<in> carrier"
  shows "diff \<infinity> charts charts (\<lambda>y. tms (invs x) y)"
    and "diff \<infinity> charts charts (\<lambda>y. tms y (invs x))"
  using diff_tms[of "invs x"] assms uminus_mem by blast+

lemma diff_tms_invs':
  assumes "x \<in> carrier"
  shows "diff \<infinity> charts charts (\<lambda>y. tms x (invs y))"
    and "diff \<infinity> charts charts (\<lambda>y. tms (invs y) x)"
  using diff_compose[OF smooth_inv diff_tms(1)[OF assms]] apply (simp add: diff.diff_cong)
  using diff_compose[OF smooth_inv diff_tms(2)[OF assms]] by (simp add: diff.diff_cong)

end


section \<open>Morphisms of Lie groups, actions and representations\<close>

subsection \<open>Morphism of Lie groups.\<close>
locale lie_group_pair =
  L1: lie_group c1 t1 i1 d1 m1 +
  L2: lie_group c2 t2 i2 d2 m2
  for c1 :: "('a::{second_countable_topology,t2_space}, 'b::euclidean_space) chart set"
    and c2 :: "('c::{second_countable_topology,t2_space}, 'd::euclidean_space) chart set"
    and t1 t2 and i1 i2 and d1 d2 and m1 m2


locale lie_group_morphism_with =
  lie_group_pair c1 c2 t1 t2 i1 i2 d1 d2 m1 m2 +
  diff \<infinity> c1 c2 f +
  group_hom_betw L1.carrier L2.carrier t1 t2 i1 i2 d1 d2 m1 m2 f
  for c1 :: "('a::{second_countable_topology,t2_space}, 'b::euclidean_space) chart set"
    and c2 :: "('c::{second_countable_topology,t2_space}, 'd::euclidean_space) chart set"
    and t1 t2 and i1 i2 and d1 d2 and m1 m2 and f

lemma (in lie_group_pair) lie_group_morphismI:
  assumes "diff \<infinity> c1 c2 f"
    and group_hom: "\<forall>x\<in>L1.carrier. \<forall>y\<in>L1.carrier. f (t1 x y) =  t2 (f x) (f y)"
    and closure: "\<forall>x\<in>L1.carrier. f x \<in> L2.carrier"
  shows "lie_group_morphism_with c1 c2 t1 t2 i1 i2 d1 d2 m1 m2 f"
proof -
  have 1: "group_on_with_pair L1.carrier L2.carrier t1 t2 i1 i2 d1 d2 m1 m2"
    using lie_group_pair_axioms unfolding lie_group_pair_def lie_group_def group_on_with_pair_def by presburger
  show ?thesis
    unfolding lie_group_morphism_with_def group_hom_betw_def group_hom_betw_axioms_def
    by (simp add: assms lie_group_pair_axioms 1)
qed

lemma (in lie_group) lie_group_morphismI:
  assumes "lie_group c2 t2 i2 d2 m2"
    and "diff \<infinity> charts c2 f"
    and group_hom: "\<forall>x\<in>carrier. \<forall>y\<in>carrier. f (tms x y) =  t2 (f x) (f y)"
    and closure: "\<forall>x\<in>carrier. f x \<in> (manifold.carrier c2)"
  shows "lie_group_morphism_with charts c2 tms t2 tms_one i2 dvsn d2 invs m2 f"
  by (auto intro: lie_group_pair.lie_group_morphismI simp: lie_group_pair_def lie_group_axioms assms)

locale lie_group_isomorphism =
  lie_group_pair c1 c2 t1 t2 i1 i2 d1 d2 m1 m2 +
  diffeomorphism \<infinity> c1 c2 f f' +
  group_hom_betw L1.carrier L2.carrier t1 t2 i1 i2 d1 d2 m1 m2 f
  for c1 :: "('a::{second_countable_topology,t2_space}, 'b::euclidean_space) chart set"
    and c2 :: "('c::{second_countable_topology,t2_space}, 'd::euclidean_space) chart set"
    and t1 t2 and i1 i2 and d1 d2 and m1 m2 and f f'



subsection \<open>Action of a Lie group on a manifold.\<close>

abbreviation (input) "diff_action_map g_charts m_charts action \<equiv>
  diff \<infinity> (c_manifold_prod.prod_charts g_charts m_charts) m_charts action"

text \<open>A Lie group action is a homomorphism from the Lie group to the automorphism group of a space,
  here a manifold, which is differentiable (smooth). I take here the more explicit definition given
  in Kirillov's lecture notes (2008; page 12), and derive the more abstract version later (after showing
  \<^term>\<open>c_manifold.Diff\<close> is not just a group, but a Lie group).\<close>
text \<open>Take care: there are now two manifolds, of which the Lie group is the primary one as far
  as namespace is concerned. Everything pertaining to the manifold acted upon is accessed with
  qualified syntax. This disappears for Lie groups acting on themselves.\<close>
locale lie_group_action =
  lie_group charts tms tms_one dvsn invs + M: c_manifold m_charts k
  for charts::"('a::{t2_space,second_countable_topology}, 'e::euclidean_space) chart set"
    and tms tms_one dvsn invs
    and m_charts::"('b::{t2_space,second_countable_topology}, 'f::euclidean_space) chart set" and k +
  fixes action (\<open>\<rho>\<close>)
  assumes act_diff: "g \<in> carrier \<Longrightarrow> (\<rho> g) \<in> M.Diff"
    and act_one: "\<rho> tms_one = M.Diff_id"
    and act_hom: "f\<in>G \<Longrightarrow> g\<in>G \<Longrightarrow> \<rho> (tms f g) = M.Diff_comp (\<rho> f) (\<rho> g)"
    and act_diff_prod: "diff_action_map charts m_charts (\<lambda>(g,m). the ((\<rho> g) m))"


text \<open>After proving Diff is a group, some of these axioms can be replaced.\<close>
locale lie_group_action' =
  lie_group charts tms tms_one dvsn invs +
  M: c_manifold m_charts k +
  A: group_hom_betw carrier M.Diff tms M.Diff_comp tms_one M.Diff_id dvsn M.Diff_comp_inv invs M.Diff_inv \<rho>
  for charts::"('a::{t2_space,second_countable_topology}, 'e::euclidean_space) chart set"
    and tms tms_one dvsn invs
    and m_charts::"('b::{t2_space,second_countable_topology}, 'f::euclidean_space) chart set" and k
    and \<rho> :: "'a \<Rightarrow> ('b\<rightharpoonup>'b)" +
  assumes diff_action_map: "diff_action_map charts m_charts (\<lambda>(g,m). the ((\<rho> g) m))"


subsection \<open>Action of a Lie Group on itself.\<close>
context lie_group begin

abbreviation (input) left_self_action :: "'a\<Rightarrow>'a\<Rightarrow>'a" (\<open>\<L> _\<close> [91])
  where "left_self_action g g' \<equiv> tms g g'"

abbreviation left_action :: "'a\<Rightarrow>('a\<rightharpoonup>'a)"
  where "left_action g \<equiv> (\<lambda>x. if x\<in>carrier then Some (left_self_action g x) else None)"

abbreviation (input) right_self_action :: "'a\<Rightarrow>'a\<Rightarrow>'a" (\<open>\<R> _\<close> [91])
  where "right_self_action g g' \<equiv> tms g' (invs g)"

abbreviation right_action :: "'a\<Rightarrow>('a\<rightharpoonup>'a)"
  where "right_action g \<equiv> (\<lambda>x. if x\<in>carrier then Some (right_self_action g x) else None)"

abbreviation (input) adjoint_self_action :: "'a\<Rightarrow>'a\<Rightarrow>'a" (*(\<open>Ad _ _\<close> [53,53])*)
  where "adjoint_self_action g g' \<equiv> tms g (tms g' (invs g))"



subsubsection \<open>The left action.\<close>

lemma L_action_in: "(left_self_action g g') \<in> carrier" if "g \<in> carrier" "g' \<in> carrier"
  by (simp add: add_mem that)

lemma the_left_action: "left_self_action x y = the (left_action x y)" if "y \<in> carrier"
  by (simp add: that)

lemma L_action_invs: "(left_self_action (invs x) \<circ> left_self_action x) y = y"
    "(left_self_action x \<circ> left_self_action (invs x)) y = y"
  if "x \<in> carrier" "y \<in> carrier"
  apply (metis (no_types, lifting) add_assoc add_zeroL comp_apply left_minus that uminus_mem)
  by (metis (no_types, lifting) add_assoc add_zeroL comp_apply right_minus that uminus_mem)

lemma L_homeomorphism: "homeomorphism carrier carrier (\<L> x) (\<L> (invs x))" if "x \<in> carrier"
proof -
  {
    fix x y assume xy_in_carrier: "x \<in> carrier" "y \<in> carrier"
    then have "tms (invs x) (tms x y) = y" and "tms x (tms (invs x) y) = y"
      using add_assoc add_zeroL uminus_mem by (metis left_minus, metis right_minus)
  }
  thus "homeomorphism carrier carrier (tms x) (tms (invs x))"
    using that continuous_on_tms(1) by (auto intro: homeomorphismI simp: L_action_in image_subset_iff uminus_mem)
qed

lemma L_homeomorphism': "homeomorphism carrier carrier (\<L> (invs x)) (\<L> x)"
  if "x \<in> carrier"
  using L_homeomorphism homeomorphism_sym that by blast

lemma L_homeomorphism_chart: "homeomorphism (domain c) (\<L> x ` domain c) (\<L> x) (\<L> (invs x))"
  if "x \<in> carrier" "c \<in> atlas" 
  using L_homeomorphism homeomorphism_of_subsets that by blast

lemma L_homeomorphism_chart': "homeomorphism (\<L> x ` domain c) (domain c) (\<L> (invs x)) (\<L> x)"
  if "x \<in> carrier" "c \<in> atlas"
  using L_homeomorphism_chart that homeomorphism_sym by blast

lemma L_open_map:
  assumes "x \<in> carrier" "open S" "S \<subseteq> carrier"
  shows "open (\<L> x ` S)"
proof -
  obtain C where C: "\<forall>c\<in>C. c\<in>atlas" "S = \<Union>{domain c | c. c\<in>C}"
    using open_covered_by_charts assms by blast
  have "\<L> x ` S = \<Union>{\<L> x ` domain c | c. c\<in>C}"
    using C(2) by auto
  thus "open (\<L> x ` S)"
    using homeomorphism_imp_open_map' L_homeomorphism by (metis assms open_carrier)
qed

lift_definition L_chart :: "'a \<Rightarrow> ('a,'e) chart \<Rightarrow> ('a,'e) chart"
  is "\<lambda>x. \<lambda>(d,d',f,f'). if x\<in>carrier \<and> d\<subseteq>carrier then (\<L> x ` d, d', f \<circ> \<L> (invs x), \<L> x \<circ> f') else ({}, {}, f, f')"
  using L_homeomorphism by (auto split: if_splits intro!: L_open_map)
    (meson homeomorphism_compose homeomorphism_of_subsets homeomorphism_symD)

lemma L_chart_apply_chart[simp]: "apply_chart (L_chart x c) = apply_chart c \<circ> \<L> (invs x)"
  and L_chart_inv_chart[simp]: "inv_chart (L_chart x c) = \<L> x \<circ> inv_chart c"
  and domain_L_chart[simp]: "domain (L_chart x c) = \<L> x ` domain c"
  and codomain_L_chart[simp]: "codomain (L_chart x c) = codomain c"
  if "x\<in>carrier" "c\<in>atlas"
  using that(1) domain_atlas_subset_carrier[OF that(2)] by (transfer, auto)+

lemma L_chart_apply_chart'[simp]: "apply_chart (L_chart x c) = apply_chart c \<circ> \<L> (invs x)"
  and L_chart_inv_chart'[simp]: "inv_chart (L_chart x c) = \<L> x \<circ> inv_chart c"
  and domain_L_chart'[simp]: "domain (L_chart x c) = \<L> x ` domain c"
  and codomain_L_chart'[simp]: "codomain (L_chart x c) = codomain c"
  if "x\<in>carrier" "domain c \<subseteq> carrier"
  using that by (transfer, auto)+

lemma smooth_compat_L_chart:
  assumes "x \<in> carrier" "c \<in> atlas" "c' \<in> atlas"
  shows "\<infinity>-smooth_compat (L_chart x c) c'"
proof -
  let ?dom1 = "(\<lambda>y. c (tms (invs x) y)) ` (tms x ` domain c \<inter> domain c')"
  let ?dom2 = "codomain c \<inter> inv_chart c -` (carrier \<inter> tms x -` domain c')"
  let ?dom3 = "c' ` (tms x ` domain c \<inter> domain c')"
  let ?dom4 = "codomain c' \<inter> inv_chart c' -` (carrier \<inter> tms (invs x) -` domain c)"

  have invs_tms_defined: "c (tms (invs x) (tms x y)) \<in> codomain c" if "y \<in> domain c" for y
    by (metis add_assoc add_uminus add_zeroL assms(1,2) chart_in_codomain in_carrier_atlasI uminus_mem that)
  have domain_simp_1: "?dom1 = ?dom2"
  proof -
    {
      fix y assume y: "tms x y \<in> domain c'" "y \<in> domain c"
      have "inv_chart c (c (tms (invs x) (tms x y))) \<in> carrier"
        and "tms x (inv_chart c (c (tms (invs x) (tms x y)))) \<in> domain c'"
        subgoal using y assms(2) invs_tms_defined by blast
        subgoal using y by (metis add_assoc add_zeroL assms(1,2) in_carrier_atlasI inv_chart_inverse left_minus uminus_mem)
        done
    } moreover {
      fix y assume y: "y \<in> codomain c" "inv_chart c y \<in> carrier" "tms x (inv_chart c y) \<in> domain c'"
      have "y = c (tms (invs x) (tms x (inv_chart c y)))"
        by (metis (full_types) assms(1) chart_inverse_inv_chart homeomorphism_apply1 L_homeomorphism y(1,2))
      then have "y \<in> (\<lambda>y. c (tms (invs x) y)) ` (tms x ` domain c \<inter> domain c')"
        using y(1,3) by blast
    }
    ultimately show "?dom1 = ?dom2" using invs_tms_defined by auto
  qed
  have domain_simp_2: "?dom3 = ?dom4"
  proof -
    {
      fix y assume y: "tms x y \<in> domain c'" "y \<in> domain c"
      have "tms x y \<in> carrier" and "tms (invs x) (tms x y) \<in> domain c"
        subgoal using y assms(3) by simp
        subgoal using y by (metis add_assoc add_zeroL assms(1,2) in_carrier_atlasI local.left_minus uminus_mem)
        done
    } moreover {
      fix y assume "y \<in> codomain c'" "inv_chart c' y \<in> carrier" "tms (invs x) (inv_chart c' y) \<in> domain c"
      then have "y \<in> c' ` (tms x ` domain c \<inter> domain c')"
        by (smt (verit, ccfv_threshold) Int_iff add_assoc add_uminus add_zeroL assms(1)
            chart_inverse_inv_chart inv_chart_in_domain rev_image_eqI uminus_mem)
    }
    ultimately show "?dom3 = ?dom4" by auto
  qed

  have "smooth_on ?dom1 (c' \<circ> (tms x \<circ> inv_chart c))"
    using diff.diff_chartsD[OF diff_tms(1)[OF assms(1)] assms(2,3)]
    by (simp add: comp_assoc domain_simp_1)
  moreover have "smooth_on ?dom3 (c \<circ> tms (invs x) \<circ> inv_chart c')"
    using diff.diff_chartsD[OF diff_tms_invs(1)[OF assms(1)] assms(3,2)] by (simp add: domain_simp_2)
  ultimately show ?thesis
    by (unfold smooth_compat_def, auto simp: assms)
qed

lemma L_chart_compat:
  assumes "x \<in> carrier" "c \<in> atlas"
  shows "\<infinity>-smooth_compat c (L_chart x c)"
  using smooth_compat_L_chart[OF assms(1,2,2)] by (simp add: smooth_compat_commute)

lemma L_chart_in_atlas: "L_chart x c \<in> atlas" if "x \<in> carrier" "c \<in> atlas"
proof (rule maximal_atlas)
  show "domain (L_chart x c) \<subseteq> carrier" using L_action_in that by auto
  fix c' assume "c' \<in> atlas"
  with that(2) have "\<infinity>-smooth_compat c c'" by (simp add: atlas_is_atlas)
  thus "\<infinity>-smooth_compat (L_chart x c) c'"
    using smooth_compat_L_chart[OF that] by (simp add: \<open>c' \<in> atlas\<close>)
qed

lemma left_action_automorphic: "c_automorphism \<infinity> charts (\<L> x) (\<L> (invs x))"
  if "x \<in> carrier"
proof (unfold_locales)
  fix y assume "y \<in> carrier"
  then obtain c1 where c1: "c1 \<in> atlas" "y \<in> domain c1" using atlasE by blast
  let ?L = "left_self_action x"
  let ?L\<^sub>i = "left_self_action (invs x)"

  text \<open>To find the second chart, for the codomain of \<^term>\<open>\<L> x\<close>, just shift the first chart across.\<close>
  show "\<exists>c1\<in>atlas. \<exists>c2\<in>atlas.
    y \<in> domain c1 \<and>
    ?L ` domain c1 \<subseteq> domain c2 \<and>
    smooth_on (codomain c1) (c2 \<circ> ?L \<circ> inv_chart c1)"
  proof (intro bexI conjI)
    let ?c2 = "L_chart x c1"

    show "y \<in> domain c1" by (simp add: c1(2))
    show "c1 \<in> atlas" "?c2 \<in> atlas" by (simp add: L_chart_in_atlas c1(1) that)+
    show "tms x ` domain c1 \<subseteq> domain ?c2" by (simp add: c1(1) that)
    
    have "(c1 \<circ> ?L\<^sub>i \<circ> ?L \<circ> inv_chart c1) a = a" if "a \<in> codomain c1" for a
      using L_action_invs(1) \<open>x \<in> carrier\<close> c1(1) that by force
    thus "smooth_on (codomain c1) (?c2 \<circ> ?L \<circ> inv_chart c1)"
      using smooth_on_id smooth_on_cong
      by (smt (verit, del_insts) L_chart_apply_chart c1(1) open_codomain that)
  qed

  show "\<exists>c1\<in>atlas. \<exists>c2\<in>atlas.
    y \<in> domain c1 \<and>
    ?L\<^sub>i ` domain c1 \<subseteq> domain c2 \<and>
    smooth_on (codomain c1) (c2 \<circ> ?L\<^sub>i \<circ> inv_chart c1)"
  proof (intro bexI conjI)
    let ?c2 = "L_chart (invs x) c1"

    have [simp]: "invs x \<in> carrier" by (simp add: that uminus_mem)

    show "y \<in> domain c1" by (simp add: c1(2))
    show "c1 \<in> atlas" "?c2 \<in> atlas" by (simp add: L_chart_in_atlas c1(1) that)+
    show "tms (invs x) ` domain c1 \<subseteq> domain ?c2" by (simp add: c1(1) that)

    have 1: "(c1 \<circ> ?L \<circ> ?L\<^sub>i \<circ> inv_chart c1) a = a"
      if "a \<in> codomain c1" for a
      using L_action_invs(2) \<open>x \<in> carrier\<close> c1 that by force
    show "smooth_on (codomain c1) (?c2 \<circ> ?L\<^sub>i \<circ> inv_chart c1)"
      apply (simp add: c1 uminus_uminus[OF that])
      using smooth_on_id 1 by (smt (verit, del_insts) open_codomain smooth_on_cong)
  qed

  { fix y assume "y \<in> carrier"
    show "tms (invs x) (tms x y) = y"
      by (metis \<open>y \<in> carrier\<close> add_assoc add_zeroL left_minus that uminus_mem)
    show "tms x (tms (invs x) y) = y"
      by (metis \<open>y \<in> carrier\<close> add_assoc add_zeroL right_minus that uminus_mem) }
qed

lemma left_action_in_Diff: "left_action x \<in> Diff" if "x \<in> carrier"
  apply (intro DiffI automorphismI exI[where x="left_self_action (invs x)"])
    subgoal using c_automorphism.c_automorphism_cong left_action_automorphic that by fastforce
    subgoal by (simp add: domIff order_class.order_eq_iff subset_iff)
  done

lemma diff_the_L: "diff \<infinity> (c_manifold_prod.prod_charts charts charts) charts (\<lambda>(g, m). the (left_action g m))"
  (is "diff \<infinity> ?prod_charts charts ?L")
proof -
  let ?prod_carrier = "manifold.carrier ?prod_charts"
  have L_eq: "?L (g,m) = (\<L> g) m" if "(g,m) \<in> ?prod_carrier" for g m
    using c_manifold_prod.prod_carrier[OF lie_prod] that by fastforce
  show ?thesis
    apply (rule diff.diff_cong[OF smooth_mult])
    using L_eq by fastforce
qed

lemma left_action: "lie_group_action' charts tms tms_one dvsn invs charts \<infinity> left_action"
  unfolding lie_group_action'_def lie_group_action'_axioms_def
  apply (simp add: lie_group_axioms c_manifold_axioms, intro conjI)
    subgoal using add_assoc add_mem left_action_in_Diff by (unfold_locales, auto)
    subgoal by (rule diff_the_L)
  done

sublocale left_action: lie_group_action' charts tms tms_one dvsn invs charts \<infinity> left_action
  by (rule left_action)



subsubsection \<open>The right action.\<close>

lemma R_action_in: "(right_self_action g g') \<in> carrier" if "g \<in> carrier" "g' \<in> carrier"
  by (simp add: add_mem that uminus_mem)

lemma the_right_action: "right_self_action x y = the (right_action x y)" if "y \<in> carrier"
  by (simp add: that)

lemma R_action_invs: "(right_self_action (invs x) \<circ> right_self_action x) y = y"
    "(right_self_action x \<circ> right_self_action (invs x)) y = y"
  if "x \<in> carrier" "y \<in> carrier"
  using add_assoc add_zeroR comp_apply right_minus left_minus that uminus_mem by simp_all

lemma R_homeomorphism: "homeomorphism carrier carrier (\<R> x) (\<R> (invs x))"
  if "x \<in> carrier"
proof -
  {
    fix x y assume xy_in_carrier: "x \<in> carrier" "y \<in> carrier"
    then have "tms (tms y (invs x)) (invs (invs x)) = y" and "tms (tms y (invs (invs x))) (invs x) = y"
      using add_assoc add_zeroR uminus_mem by (metis right_minus, metis left_minus)
  }
  thus "homeomorphism carrier carrier (\<R> x) (\<R> (invs x))"
    using that continuous_on_tms(2) by (auto intro!: homeomorphismI simp: R_action_in image_subset_iff uminus_mem)
qed

lemma R_homeomorphism': "homeomorphism carrier carrier (\<R> (invs x)) (\<R> x)"
  if "x \<in> carrier"
  using R_homeomorphism homeomorphism_sym that by blast

lemma R_homeomorphism_chart: "homeomorphism (domain c) (\<R> x ` domain c) (\<R> x) (\<R> (invs x))"
  if "x \<in> carrier" "c \<in> atlas"
  using R_homeomorphism homeomorphism_of_subsets that by blast

lemma R_homeomorphism_chart': "homeomorphism (\<R> x ` domain c) (domain c) (\<R> (invs x)) (\<R> x)"
  if "x \<in> carrier" "c \<in> atlas"
  using R_homeomorphism_chart that homeomorphism_sym by blast

lemma R_open_map:
  assumes "x \<in> carrier" "open S" "S \<subseteq> carrier"
  shows "open (\<R> x ` S)"
proof -
  obtain C where C: "\<forall>c\<in>C. c\<in>atlas" "S = \<Union>{domain c | c. c\<in>C}"
    using open_covered_by_charts assms by blast
  have "\<R> x ` S = \<Union>{\<R> x ` domain c | c. c\<in>C}"
    using C(2) by auto
  thus "open (\<R> x ` S)"
    using homeomorphism_imp_open_map' R_homeomorphism assms open_carrier by fast
qed

lift_definition R_chart :: "'a \<Rightarrow> ('a,'e) chart \<Rightarrow> ('a,'e) chart"
  is "\<lambda>x. \<lambda>(d,d',f,f'). if x\<in>carrier \<and> d\<subseteq>carrier then (\<R> x ` d, d', f \<circ> \<R> (invs x), \<R> x \<circ> f') else ({}, {}, f, f')"
  using R_homeomorphism by (auto split: if_splits intro!: R_open_map)
    (meson homeomorphism_compose homeomorphism_of_subsets homeomorphism_symD)

lemma R_chart_apply_chart[simp]: "apply_chart (R_chart x c) = apply_chart c \<circ> \<R> (invs x)"
  and R_chart_inv_chart[simp]: "inv_chart (R_chart x c) = \<R> x \<circ> inv_chart c"
  and domain_R_chart[simp]: "domain (R_chart x c) = \<R> x ` domain c"
  and codomain_R_chart[simp]: "codomain (R_chart x c) = codomain c"
  if "x\<in>carrier" "c\<in>atlas"
  using that(1) domain_atlas_subset_carrier[OF that(2)] by (transfer, auto)+

lemma R_chart_apply_chart'[simp]: "apply_chart (R_chart x c) = apply_chart c \<circ> \<R> (invs x)"
  and R_chart_inv_chart'[simp]: "inv_chart (R_chart x c) = \<R> x \<circ> inv_chart c"
  and domain_R_chart'[simp]: "domain (R_chart x c) = \<R> x ` domain c"
  and codomain_R_chart'[simp]: "codomain (R_chart x c) = codomain c"
  if "x\<in>carrier" "domain c \<subseteq> carrier"
  using that by (transfer, auto)+

lemma smooth_compat_R_chart:
  assumes "x \<in> carrier" "c \<in> atlas" "c' \<in> atlas"
  shows "\<infinity>-smooth_compat (R_chart x c) c'"
proof -
  let ?dom1 = "(\<lambda>y. c (tms y (invs (invs x)))) ` ((\<lambda>g'. tms g' (invs x)) ` domain c \<inter> domain c')"
  let ?dom2 = "codomain c \<inter> inv_chart c -` (carrier \<inter> (\<lambda>y. tms y (invs x)) -` domain c')"
  let ?dom3 = "c' ` ((\<lambda>y. tms y (invs x)) ` domain c \<inter> domain c')"
  let ?dom4 = "codomain c' \<inter> inv_chart c' -` (carrier \<inter> (\<lambda>y. tms y x) -` domain c)"

  have invs_tms_defined: "c (tms (tms y (invs x)) (invs (invs x))) \<in> codomain c" if "y \<in> domain c" for y
    using add_assoc add_zeroR assms(1,2) local.right_minus that uminus_mem by auto
  then have domain_simp_1: "?dom1 = ?dom2"
  proof -
    {
      fix y assume y: "tms y (invs x) \<in> domain c'" "y \<in> domain c"
      have "inv_chart c (c (tms (tms y (invs x)) (invs (invs x)))) \<in> carrier"
        and "tms (inv_chart c (c (tms (tms y (invs x)) (invs (invs x))))) (invs x) \<in> domain c'"
        subgoal using y invs_tms_defined assms(2) by blast
        subgoal using y add_assoc add_zeroR assms(1,2) in_carrier_atlasI inv_chart_inverse right_minus uminus_mem by metis
        done
    } moreover {
      fix y assume "y \<in> codomain c" "inv_chart c y \<in> carrier" "tms (inv_chart c y) (invs x) \<in> domain c'"
      then have "y \<in> (\<lambda>y. apply_chart c (tms y (invs (invs x)))) ` ((\<lambda>g'. tms g' (invs x)) ` domain c \<inter> domain c')"
        by (smt (verit, ccfv_threshold) IntI R_action_invs(1) assms(1) chart_inverse_inv_chart
          comp_apply imageI inv_chart_in_domain)
    }
    ultimately show "?dom1 = ?dom2" using invs_tms_defined by auto
  qed
  have domain_simp_2: "?dom3 = ?dom4"
  proof -
    {
      fix y assume y: "tms y (invs x) \<in> domain c'" "y \<in> domain c"
      have "tms y (invs x) \<in> carrier" and "tms (tms y (invs x)) x \<in> domain c"
        subgoal using y assms(3) by simp
        subgoal using y by (metis add_assoc add_zeroR assms(1,2) in_carrier_atlasI left_minus uminus_mem)
        done
    } moreover {
      fix xa assume xa: "xa \<in> codomain c'" "inv_chart c' xa \<in> carrier" "tms (inv_chart c' xa) x \<in> domain c"
      then have "xa \<in> apply_chart c' ` ((\<lambda>y. tms y (invs x)) ` domain c \<inter> domain c')"
        by (smt (verit, ccfv_threshold) Int_iff add_assoc add_zero assms(1) chart_inverse_inv_chart
          inv_chart_in_domain right_minus rev_image_eqI uminus_mem)
    }
    ultimately show "?dom3 = ?dom4" by auto
  qed

  have "smooth_on ?dom1 (c' \<circ> ((\<lambda>g'. tms g' (invs x)) \<circ> inv_chart c))"
    using diff.diff_chartsD[OF diff_tms_invs(2)[OF assms(1)] assms(2,3)]
    by (simp add: comp_assoc domain_simp_1)
  moreover have "smooth_on ?dom3 ( c \<circ> (\<lambda>g'. tms g' (invs (invs x))) \<circ> inv_chart c')"
    using diff.diff_chartsD[OF diff_tms(2)] uminus_uminus assms by (simp add: domain_simp_2)
  ultimately show ?thesis
    by (unfold smooth_compat_def, auto simp: assms)
qed

lemma R_chart_compat:
  assumes "x \<in> carrier" "c \<in> atlas"
  shows "\<infinity>-smooth_compat c (R_chart x c)"
  using smooth_compat_R_chart[OF assms(1,2,2)] by (simp add: smooth_compat_commute)

lemma R_chart_in_atlas: "R_chart x c \<in> atlas" if "x \<in> carrier" "c \<in> atlas"
proof (rule maximal_atlas)
  show "domain (R_chart x c) \<subseteq> carrier" using R_action_in that by auto
  fix c' assume "c' \<in> atlas"
  with that(2) have "\<infinity>-smooth_compat c c'" by (simp add: atlas_is_atlas)
  thus "\<infinity>-smooth_compat (R_chart x c) c'"
    using smooth_compat_R_chart[OF that] by (simp add: \<open>c' \<in> atlas\<close>)
qed

lemma right_action_automorphic: "c_automorphism \<infinity> charts (\<R> x) (\<R> (invs x))"
  if "x \<in> carrier"
proof (unfold_locales)
  fix y assume "y \<in> carrier"
  then obtain c1 where c1: "c1 \<in> atlas" "y \<in> domain c1" using atlasE by blast
  let ?R = "right_self_action x"
  let ?R\<^sub>i = "right_self_action (invs x)"

  text \<open>To find the second chart, for the codomain of \<^term>\<open>\<R> x\<close>, just shift the first chart across.\<close>
  show "\<exists>c1\<in>atlas. \<exists>c2\<in>atlas.
    y \<in> domain c1 \<and>
    ?R ` domain c1 \<subseteq> domain c2 \<and>
    smooth_on (codomain c1) (c2 \<circ> ?R \<circ> inv_chart c1)"
  proof (intro bexI conjI)
    let ?c2 = "R_chart x c1"

    show "y \<in> domain c1" by (simp add: c1(2))
    show "c1 \<in> atlas" "?c2 \<in> atlas" by (simp add: R_chart_in_atlas c1(1) that)+
    show "(\<lambda>y. tms y (invs x)) ` domain c1 \<subseteq> domain ?c2" by (simp add: c1(1) that)
    
    have cong_to_id: "(c1 \<circ> ?R\<^sub>i \<circ> ?R \<circ> inv_chart c1) a = a" if "a \<in> codomain c1" for a
      using R_action_invs(1) \<open>x \<in> carrier\<close> c1(1) that by force
    show "smooth_on (codomain c1) (?c2 \<circ> ?R \<circ> inv_chart c1)"
      using smooth_on_id smooth_on_cong cong_to_id
      by (smt (verit, ccfv_threshold) R_chart_apply_chart c1(1) comp_apply open_codomain that uminus_uminus)
  qed

  show "\<exists>c1\<in>atlas. \<exists>c2\<in>atlas.
    y \<in> domain c1 \<and>
    ?R\<^sub>i ` domain c1 \<subseteq> domain c2 \<and>
    smooth_on (codomain c1) (c2 \<circ> ?R\<^sub>i \<circ> inv_chart c1)"
  proof (intro bexI conjI)
    let ?c2 = "R_chart (invs x) c1"

    have [simp]: "invs x \<in> carrier" by (simp add: that uminus_mem)

    show "y \<in> domain c1" by (simp add: c1(2))
    show "c1 \<in> atlas" "?c2 \<in> atlas" by (simp add: R_chart_in_atlas c1(1) that)+
    show "(\<lambda>g'. tms g' (invs (invs x))) ` domain c1 \<subseteq> domain ?c2" by (simp add: c1(1) that)

    have 1: "(c1 \<circ> ?R \<circ> ?R\<^sub>i \<circ> inv_chart c1) a = a"
      if "a \<in> codomain c1" for a
      using R_action_invs(2) \<open>x \<in> carrier\<close> c1 that by force
    show "smooth_on (codomain c1) (?c2 \<circ> ?R\<^sub>i \<circ> inv_chart c1)"
      apply (rule smooth_on_cong)
      using 1 by (auto simp add: c1 uminus_uminus[OF that])
  qed

  { fix y assume "y \<in> carrier"
    show "tms (tms y (invs x)) (invs (invs x)) = y"
      by (metis \<open>y \<in> carrier\<close> add_assoc add_zeroR right_minus that uminus_mem)
    show "tms (tms y (invs (invs x))) (invs x) = y"
      by (metis \<open>y \<in> carrier\<close> add_assoc add_zeroR left_minus that uminus_mem) }
qed

lemma right_action_in_Diff: "right_action x \<in> Diff" if "x \<in> carrier"
  apply (intro DiffI automorphismI exI[where x="right_self_action (invs x)"])
    subgoal using c_automorphism.c_automorphism_cong right_action_automorphic that by fastforce
    subgoal by (simp add: domIff order_class.order_eq_iff subset_iff)
  done

end


section \<open>Models/Instances\<close>

subsection \<open>Euclidean Space\<close>
text \<open>Euclidean spaces are dealt with at the start of the section ``Differentiable Functions'' in
  \<^theory>\<open>Smooth_Manifolds.Differentiable_Manifold\<close>.
  Therefore, this section is really just a ``trivial'' exercise to get used to things.\<close>

subsubsection \<open>Euclidean Spaces are Lie groups under \<^term>\<open>(+)\<close>.\<close>
locale euclidean_lie_group_add
begin

abbreviation C
  where "C \<equiv> manifold_eucl.carrier"

abbreviation C_prod
  where "C_prod \<equiv> manifold.carrier prod_charts_eucl"

lemma eucl_is_group: "group_on_with C (+) 0 (-) uminus"
proof (unfold group_on_with_def, intro conjI)
  show "monoid_on_with C (+) 0"
    unfolding monoid_on_with_def semigroup_add_on_with_def
    using manifold_eucl_carrier
    by (simp add: monoid_on_with_axioms.intro)
  show "group_on_with_axioms C (+) 0 (-) uminus"
    unfolding group_on_with_axioms_def
    using manifold_eucl_carrier UNIV_I ab_group_add_class.ab_diff_conv_add_uminus add.left_inverse
    by auto
qed

lemma prod_domain_codomain: "domain prod_chart_eucl = C\<times>C" "C\<times>C = C_prod" "codomain prod_chart_eucl = C\<times>C"
  using c_manifold_prod.domain_prod_chart [OF eucl_makes_product_manifold]
  apply fastforce
  using c_manifold_prod.prod_carrier eucl_makes_product_manifold
  apply metis
  using c_manifold_prod.codomain_prod_chart [OF eucl_makes_product_manifold]
  by fastforce

lemma smooth_on_add_const: "smooth_on C (\<lambda>a. a+b)"
proof -
  have sm_id: "smooth_on C (\<lambda>a. a)"
    by (simp add: smooth_on_id)
  have sm_add: "smooth_on C (\<lambda>a. b)"
    by (simp add: smooth_on_const)
  show "smooth_on C (\<lambda>a. a+b)"
    using smooth_on_add [OF sm_id sm_add manifold.open_carrier]
    by simp
qed
                    
lemma smooth_binop_diff:
  fixes tms::"'a\<Rightarrow>'a\<Rightarrow>'a::euclidean_space"
  assumes "smooth_on C_prod (\<lambda>(a,b). tms a b)"
  shows "diff \<infinity> prod_charts_eucl charts_eucl (\<lambda>(x, y). tms x y)"
proof (unfold diff_def diff_axioms_def, intro conjI allI impI)
  let ?prod = "prod_charts_eucl"
  let ?mult = "\<lambda>(x, y). tms x y"
  let ?c1 = "prod_chart_eucl"
  let ?c2 = "chart_eucl"
  let ?atl = "manifold_eucl.atlas \<infinity>"
  let ?prod_atl = "c_manifold.atlas prod_charts_eucl \<infinity>"
  fix p::"'a\<times>'a"
  assume "p\<in>manifold.carrier ?prod"
  show "\<exists>c1\<in>c_manifold.atlas prod_charts_eucl \<infinity>. \<exists>c2\<in>manifold_eucl.atlas \<infinity>.
    p \<in> domain c1 \<and>
    (\<lambda>(x, y). tms x y) ` domain c1 \<subseteq> domain c2 \<and>
    smooth_on (codomain c1) (apply_chart c2 \<circ> (\<lambda>(x, y). tms x y) \<circ> inv_chart c1)"
  proof (intro bexI, intro conjI)
    show "?c1 \<in> ?prod_atl"
      by (rule c_manifold.in_charts_in_atlas [
        OF c_manifold_prod.c_manifold_atlas_product [
          OF eucl_makes_product_manifold
        ] prod_chart_in_prod_charts
      ])
    show "?c2 \<in> ?atl"
      using c_manifold.in_charts_in_atlas by simp
    show "p \<in> domain ?c1"
      by (simp add: prod_domain_codomain)
    show "(\<lambda>(x, y). tms x y) ` domain ?c1 \<subseteq> domain ?c2"
      by simp
    show "smooth_on (codomain ?c1) (apply_chart ?c2 \<circ> (\<lambda>(x, y). tms x y) \<circ> inv_chart ?c1)"
      using map_fun_eucl_prod_id_f prod_domain_codomain assms
      by metis
  qed
qed (simp add: c_manifold_prod.c_manifold_atlas_product c_manifolds.intro
      eucl_makes_product_manifold manifold_eucl.c_manifold_axioms)

lemma smooth_unop_diff:
  fixes invs::"'a\<Rightarrow>'a::euclidean_space"
  assumes "smooth_on C invs"
  shows "diff \<infinity> charts_eucl charts_eucl invs"
proof (unfold diff_def diff_axioms_def, intro conjI allI impI)
  let ?c1 = "prod_chart_eucl"
  let ?c2 = "chart_eucl"
  let ?atl = "manifold_eucl.atlas \<infinity>"
  fix x::'a
  assume "x \<in> manifold_eucl.carrier"
  show "\<exists>c1\<in>manifold_eucl.atlas \<infinity>. \<exists>c2\<in>manifold_eucl.atlas \<infinity>.
    x \<in> domain c1 \<and>
    invs ` domain c1 \<subseteq> domain c2 \<and>
    smooth_on (codomain c1) (apply_chart c2 \<circ> invs \<circ> inv_chart c1)"
  proof (intro bexI conjI)
    show "invs ` domain chart_eucl \<subseteq> domain ?c2"
      by (simp add: image_subsetI)
    have "manifold_eucl.carrier = codomain chart_eucl"
      by simp
    thus "smooth_on (codomain chart_eucl) (apply_chart chart_eucl \<circ> invs \<circ> inv_chart chart_eucl)"
      using assms map_fun_eucl_id_f
      by metis
  qed (simp+)
qed (simp add: manifold_eucl.self.c_manifolds_axioms)

lemma eucl_smooth_group_imp_lie_group:
  assumes is_group: "group_on_with C tms tms_1 dvsn invs"
    and smooth_mult: "smooth_on C_prod (\<lambda>(a,b). tms a b)"
    and smooth_inv: "smooth_on C invs"
  shows "lie_group charts_eucl tms tms_1 dvsn invs"
proof (unfold lie_group_def lie_group_axioms_def, (intro conjI))
  show "c_manifold charts_eucl \<infinity>"
    using c_manifold_def by (simp add: c1_manifold_atlas_eucl)
  show "group_on_with manifold_eucl.carrier tms tms_1 dvsn invs"
    using is_group by simp
  show "diff \<infinity> prod_charts_eucl charts_eucl (\<lambda>(a, b). tms a b)"
    using smooth_binop_diff smooth_mult by auto
  show "diff \<infinity> charts_eucl charts_eucl invs"
    using smooth_unop_diff smooth_inv by simp
qed


text \<open>Any Euclidean space is a Lie group under addition.\<close>
theorem lie_group_eucl: "lie_group charts_eucl (+) 0 (-) uminus"
  by (rule eucl_smooth_group_imp_lie_group [OF eucl_is_group eucl_add_smooth eucl_um_smooth])

interpretation lie_group_eucl: lie_group charts_eucl "(+)" 0 "(-)" uminus
  using lie_group_eucl .

end



subsection \<open>The real numbers as a Lie group\<close>

lift_definition chart_real::"(real, real) chart" is
  "(UNIV, UNIV, \<lambda>x. x, \<lambda>x. x)"
  by (auto simp: homeomorphism_def)

abbreviation "charts_real \<equiv> {chart_real}"

lemma chart_real_is_eucl: "charts_eucl = charts_real" "chart_eucl = chart_real"
  by (transfer, simp)+

theorem lie_group_real: "lie_group charts_real (+) 0 (-) uminus"
  using euclidean_lie_group_add.lie_group_eucl chart_real_is_eucl by metis


end
