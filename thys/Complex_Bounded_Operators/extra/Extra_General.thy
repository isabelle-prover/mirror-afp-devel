section \<open>\<open>Extra_General\<close> -- General missing things\<close>

theory Extra_General
  imports
    "HOL-Library.Cardinality"
    "HOL-Analysis.Elementary_Topology"
    "HOL-Analysis.Uniform_Limit"
    "HOL-Library.Set_Algebras"
    "HOL-Types_To_Sets.Types_To_Sets"
    "HOL-Library.Complex_Order"
    "HOL-Analysis.Infinite_Sum"
    "HOL-Cardinals.Cardinals"
    "HOL-Library.Complemented_Lattices"
    "HOL-Analysis.Abstract_Topological_Spaces"
begin

subsection \<open>Misc\<close>

lemma reals_zero_comparable:
  fixes x::complex
  assumes "x\<in>\<real>"
  shows "x \<le> 0 \<or> x \<ge> 0"
  using assms unfolding complex_is_real_iff_compare0 by assumption

lemma unique_choice: "\<forall>x. \<exists>!y. Q x y \<Longrightarrow> \<exists>!f. \<forall>x. Q x (f x)"
  apply (auto intro!: choice ext) by metis

lemma image_set_plus: 
  assumes \<open>linear U\<close>
  shows \<open>U ` (A + B) = U ` A + U ` B\<close>
  unfolding image_def set_plus_def
  using assms by (force simp: linear_add)

consts heterogenous_identity :: \<open>'a \<Rightarrow> 'b\<close>
overloading heterogenous_identity_id \<equiv> "heterogenous_identity :: 'a \<Rightarrow> 'a" begin
definition heterogenous_identity_def[simp]: \<open>heterogenous_identity_id = id\<close>
end

lemma L2_set_mono2:
  assumes a1: "finite L" and a2: "K \<le> L"
  shows "L2_set f K \<le> L2_set f L"
proof-
  have "(\<Sum>i\<in>K. (f i)\<^sup>2) \<le> (\<Sum>i\<in>L. (f i)\<^sup>2)"
    apply (rule sum_mono2) 
    using assms by auto
  hence "sqrt (\<Sum>i\<in>K. (f i)\<^sup>2) \<le> sqrt (\<Sum>i\<in>L. (f i)\<^sup>2)"
    by (rule real_sqrt_le_mono)
  thus ?thesis
    unfolding L2_set_def.
qed

lemma Sup_real_close:
  fixes e :: real
  assumes "0 < e"
    and S: "bdd_above S" "S \<noteq> {}"
  shows "\<exists>x\<in>S. Sup S - e < x"
proof -
  have \<open>Sup (ereal ` S) \<noteq> \<infinity>\<close>
    by (metis assms(2) bdd_above_def ereal_less_eq(3) less_SUP_iff less_ereal.simps(4) not_le)
  moreover have \<open>Sup (ereal ` S) \<noteq> -\<infinity>\<close>
    by (simp add: SUP_eq_iff assms(3))
  ultimately have Sup_bdd: \<open>\<bar>Sup (ereal ` S)\<bar> \<noteq> \<infinity>\<close>
    by auto
  then have \<open>\<exists>x'\<in>ereal ` S. Sup (ereal ` S) - ereal e < x'\<close>
    apply (rule_tac Sup_ereal_close)
    using assms by auto
  then obtain x where \<open>x \<in> S\<close> and Sup_x: \<open>Sup (ereal ` S) - ereal e < ereal x\<close>
    by auto
  have \<open>Sup (ereal ` S) = ereal (Sup S)\<close>
    using Sup_bdd by (rule ereal_Sup[symmetric])
  with Sup_x have \<open>ereal (Sup S - e) < ereal x\<close>
    by auto
  then have \<open>Sup S - e < x\<close>
    by auto
  with \<open>x \<in> S\<close> show ?thesis
    by auto
qed

text \<open>Improved version of @{attribute internalize_sort}: It is not necessary to specify the sort of the type variable.\<close>
attribute_setup internalize_sort' = \<open>let
fun find_tvar thm v = let
  val tvars = Term.add_tvars (Thm.prop_of thm) []
  val tv = case find_first (fn (n,sort) => n=v) tvars of
              SOME tv => tv | NONE => raise THM ("Type variable " ^ string_of_indexname v ^ " not found", 0, [thm])
in 
TVar tv
end

fun internalize_sort_attr (tvar:indexname) =
  Thm.rule_attribute [] (fn context => fn thm =>
    (snd (Internalize_Sort.internalize_sort (Thm.ctyp_of (Context.proof_of context) (find_tvar thm tvar)) thm)));
in
  Scan.lift Args.var >> internalize_sort_attr
end\<close>
  "internalize a sort"

lemma card_prod_omega: \<open>X *c natLeq =o X\<close> if \<open>Cinfinite X\<close>
  by (simp add: Cinfinite_Cnotzero cprod_infinite1' natLeq_Card_order natLeq_cinfinite natLeq_ordLeq_cinfinite that)

lemma countable_leq_natLeq: \<open>|X| \<le>o natLeq\<close> if \<open>countable X\<close>
  using subset_range_from_nat_into[OF that]
  by (meson card_of_nat ordIso_iff_ordLeq ordLeq_transitive surj_imp_ordLeq)

lemma set_Times_plus_distrib: \<open>(A \<times> B) + (C \<times> D) = (A + C) \<times> (B + D)\<close>
  by (auto simp: Sigma_def set_plus_def)

subsection \<open>Not singleton\<close>

class not_singleton =
  assumes not_singleton_card: "\<exists>x y. x \<noteq> y"

lemma not_singleton_existence[simp]:
  \<open>\<exists> x::('a::not_singleton). x \<noteq> t\<close>
  using not_singleton_card[where ?'a = 'a] by (metis (full_types))

lemma not_not_singleton_zero: 
  \<open>x = 0\<close> if \<open>\<not> class.not_singleton TYPE('a)\<close> for x :: \<open>'a::zero\<close>
  using that unfolding class.not_singleton_def by auto

lemma UNIV_not_singleton[simp]: "(UNIV::_::not_singleton set) \<noteq> {x}"
  using not_singleton_existence[of x] by blast

lemma UNIV_not_singleton_converse: 
  assumes"\<And>x::'a. UNIV \<noteq> {x}"
  shows "\<exists>x::'a. \<exists>y. x \<noteq> y"
  using assms
  by fastforce 

subclass (in card2) not_singleton
  apply standard using two_le_card
  by (meson card_2_iff' obtain_subset_with_card_n)

subclass (in perfect_space) not_singleton
  apply intro_classes
  by (metis (mono_tags) Collect_cong Collect_mem_eq UNIV_I local.UNIV_not_singleton local.not_open_singleton local.open_subopen)

lemma class_not_singletonI_monoid_add:
  assumes "(UNIV::'a set) \<noteq> {0}"
  shows "class.not_singleton TYPE('a::monoid_add)"
proof intro_classes
  let ?univ = "UNIV :: 'a set"
  from assms obtain x::'a where "x \<noteq> 0"
    by auto
  thus "\<exists>x y :: 'a. x \<noteq> y"
    by auto
qed

lemma not_singleton_vs_CARD_1:
  assumes \<open>\<not> class.not_singleton TYPE('a)\<close>
  shows \<open>class.CARD_1 TYPE('a)\<close>
  using assms unfolding class.not_singleton_def class.CARD_1_def
  by (metis (full_types) One_nat_def UNIV_I card.empty card.insert empty_iff equalityI finite.intros(1) insert_iff subsetI)

subsection \<open>\<^class>\<open>CARD_1\<close>\<close>

context CARD_1 begin

lemma everything_the_same[simp]: "(x::'a)=y"
  by (metis (full_types) UNIV_I card_1_singletonE empty_iff insert_iff local.CARD_1)

lemma CARD_1_UNIV: "UNIV = {x::'a}"
  by (metis (full_types) UNIV_I card_1_singletonE local.CARD_1 singletonD)

lemma CARD_1_ext: "x (a::'a) = y b \<Longrightarrow> x = y"
proof (rule ext)
  show "x t = y t"
    if "x a = y b"
    for t :: 'a
    using that  apply (subst (asm) everything_the_same[where x=a])
    apply (subst (asm) everything_the_same[where x=b])
    by simp
qed 

end

instance unit :: CARD_1
  apply standard by auto

instance prod :: (CARD_1, CARD_1) CARD_1
  apply intro_classes
  by (simp add: CARD_1)

instance "fun" :: (CARD_1, CARD_1) CARD_1
  apply intro_classes
  by (auto simp add: card_fun CARD_1)


lemma enum_CARD_1: "(Enum.enum :: 'a::{CARD_1,enum} list) = [a]"
proof -
  let ?enum = "Enum.enum :: 'a::{CARD_1,enum} list"
  have "length ?enum = 1"
    apply (subst card_UNIV_length_enum[symmetric])
    by (rule CARD_1)
  then obtain b where "?enum = [b]"
    apply atomize_elim
    apply (cases ?enum, auto)
    by (metis length_0_conv length_Cons nat.inject)
  thus "?enum = [a]"
    by (subst everything_the_same[of _ b], simp)
qed

lemma card_not_singleton: \<open>CARD('a::not_singleton) \<noteq> 1\<close>
  by (simp add: card_1_singleton_iff)


subsection \<open>Topology\<close>

lemma cauchy_filter_metricI:
  fixes F :: "'a::metric_space filter"
  assumes "\<And>e. e>0 \<Longrightarrow> \<exists>P. eventually P F \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)"
  shows "cauchy_filter F"
proof (unfold cauchy_filter_def le_filter_def, auto)
  fix P :: "'a \<times> 'a \<Rightarrow> bool"
  assume "eventually P uniformity"
  then obtain e where e: "e > 0" and P: "dist x y < e \<Longrightarrow> P (x, y)" for x y
    unfolding eventually_uniformity_metric by auto

  obtain P' where evP': "eventually P' F" and P'_dist: "P' x \<and> P' y \<Longrightarrow> dist x y < e" for x y
    apply atomize_elim using assms e by auto

  from evP' P'_dist P
  show "eventually P (F \<times>\<^sub>F F)"
    unfolding eventually_uniformity_metric eventually_prod_filter eventually_filtermap by metis
qed

lemma cauchy_filter_metric_filtermapI:
  fixes F :: "'a filter" and f :: "'a\<Rightarrow>'b::metric_space"
  assumes "\<And>e. e>0 \<Longrightarrow> \<exists>P. eventually P F \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist (f x) (f y) < e)"
  shows "cauchy_filter (filtermap f F)"
proof (rule cauchy_filter_metricI)
  fix e :: real assume e: "e > 0"
  with assms obtain P where evP: "eventually P F" and dist: "P x \<and> P y \<Longrightarrow> dist (f x) (f y) < e" for x y
    by atomize_elim auto
  define P' where "P' y = (\<exists>x. P x \<and> y = f x)" for y
  have "eventually P' (filtermap f F)"
    unfolding eventually_filtermap P'_def 
    using evP
    by (smt eventually_mono) 
  moreover have "P' x \<and> P' y \<longrightarrow> dist x y < e" for x y
    unfolding P'_def using dist by metis
  ultimately show "\<exists>P. eventually P (filtermap f F) \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)"
    by auto
qed


lemma tendsto_add_const_iff:
  \<comment> \<open>This is a generalization of \<open>Limits.tendsto_add_const_iff\<close>, 
      the only difference is that the sort here is more general.\<close>
  "((\<lambda>x. c + f x :: 'a::topological_group_add) \<longlongrightarrow> c + d) F \<longleftrightarrow> (f \<longlongrightarrow> d) F"
  using tendsto_add[OF tendsto_const[of c], of f d]
    and tendsto_add[OF tendsto_const[of "-c"], of "\<lambda>x. c + f x" "c + d"] by auto

lemma finite_subsets_at_top_minus: 
  assumes "A\<subseteq>B"
  shows "finite_subsets_at_top (B - A) \<le> filtermap (\<lambda>F. F - A) (finite_subsets_at_top B)"
proof (rule filter_leI)
  fix P assume "eventually P (filtermap (\<lambda>F. F - A) (finite_subsets_at_top B))"
  then obtain X where "finite X" and "X \<subseteq> B" 
    and P: "finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> B \<longrightarrow> P (Y - A)" for Y
    unfolding eventually_filtermap eventually_finite_subsets_at_top by auto

  hence "finite (X-A)" and "X-A \<subseteq> B - A"
    by auto
  moreover have "finite Y \<and> X-A \<subseteq> Y \<and> Y \<subseteq> B - A \<longrightarrow> P Y" for Y
    using P[where Y="Y\<union>X"] \<open>finite X\<close> \<open>X \<subseteq> B\<close>
    by (metis Diff_subset Int_Diff Un_Diff finite_Un inf.orderE le_sup_iff sup.orderE sup_ge2)
  ultimately show "eventually P (finite_subsets_at_top (B - A))"
    unfolding eventually_finite_subsets_at_top by meson
qed

lemma finite_subsets_at_top_inter: 
  assumes "A\<subseteq>B"
  shows "filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B) = finite_subsets_at_top A"
proof (subst filter_eq_iff, intro allI iffI)
  fix P :: "'a set \<Rightarrow> bool"
  assume "eventually P (finite_subsets_at_top A)"
  then show "eventually P (filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B))"
    unfolding eventually_filtermap
    unfolding eventually_finite_subsets_at_top
    by (metis Int_subset_iff assms finite_Int inf_le2 subset_trans)
next
  fix P :: "'a set \<Rightarrow> bool"
  assume "eventually P (filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B))"
  then obtain X where \<open>finite X\<close> \<open>X \<subseteq> B\<close> and P: \<open>finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> B \<Longrightarrow> P (Y \<inter> A)\<close> for Y
    unfolding eventually_filtermap eventually_finite_subsets_at_top by metis
  have *: \<open>finite Y \<Longrightarrow> X \<inter> A \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> P Y\<close> for Y
    using P[where Y=\<open>Y \<union> (B-A)\<close>]
    apply (subgoal_tac \<open>(Y \<union> (B - A)) \<inter> A = Y\<close>)
    apply (smt (verit, best) Int_Un_distrib2 Int_Un_eq(4) P Un_subset_iff \<open>X \<subseteq> B\<close> \<open>finite X\<close> assms finite_UnI inf.orderE sup_ge2)
    by auto
  show "eventually P (finite_subsets_at_top A)"
    unfolding eventually_finite_subsets_at_top
    apply (rule exI[of _ \<open>X\<inter>A\<close>])
    by (auto simp: \<open>finite X\<close> intro!: *)
qed

lemma tendsto_principal_singleton:
  shows "(f \<longlongrightarrow> f x) (principal {x})"
  unfolding tendsto_def eventually_principal by simp

lemma complete_singleton: 
  "complete {s::'a::uniform_space}"
proof-
  have "F \<le> principal {s} \<Longrightarrow>
         F \<noteq> bot \<Longrightarrow> cauchy_filter F \<Longrightarrow> F \<le> nhds s" for F
    by (metis eventually_nhds eventually_principal le_filter_def singletonD)
  thus ?thesis
    unfolding complete_uniform
    by simp
qed

lemma on_closure_eqI:
  fixes f g :: \<open>'a::topological_space \<Rightarrow> 'b::t2_space\<close>
  assumes eq: \<open>\<And>x. x \<in> S \<Longrightarrow> f x = g x\<close>
  assumes xS: \<open>x \<in> closure S\<close>
  assumes cont: \<open>continuous_on UNIV f\<close> \<open>continuous_on UNIV g\<close>
  shows \<open>f x = g x\<close>
proof -
  define X where \<open>X = {x. f x = g x}\<close>
  have \<open>closed X\<close>
    using cont by (simp add: X_def closed_Collect_eq)
  moreover have \<open>S \<subseteq> X\<close>
    by (simp add: X_def eq subsetI)
  ultimately have \<open>closure S \<subseteq> X\<close>
    using closure_minimal by blast
  with xS have \<open>x \<in> X\<close>
    by auto
  then show ?thesis
    using X_def by blast
qed

lemma on_closure_leI:
  fixes f g :: \<open>'a::topological_space \<Rightarrow> 'b::linorder_topology\<close>
  assumes eq: \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<le> g x\<close>
  assumes xS: \<open>x \<in> closure S\<close>
  assumes cont: \<open>continuous_on UNIV f\<close> \<open>continuous_on UNIV g\<close> (* Is "isCont f x" "isCont g x" sufficient? *)
  shows \<open>f x \<le> g x\<close>
proof -
  define X where \<open>X = {x. f x \<le> g x}\<close>
  have \<open>closed X\<close>
    using cont by (simp add: X_def closed_Collect_le)
  moreover have \<open>S \<subseteq> X\<close>
    by (simp add: X_def eq subsetI)
  ultimately have \<open>closure S \<subseteq> X\<close>
    using closure_minimal by blast
  with xS have \<open>x \<in> X\<close>
    by auto
  then show ?thesis
    using X_def by blast
qed


lemma tendsto_compose_at_within:
  assumes f: "(f \<longlongrightarrow> y) F" and g: "(g \<longlongrightarrow> z) (at y within S)" 
    and fg: "eventually (\<lambda>w. f w = y \<longrightarrow> g y = z) F"
    and fS: \<open>\<forall>\<^sub>F w in F. f w \<in> S\<close>
  shows "((g \<circ> f) \<longlongrightarrow> z) F"
proof (cases \<open>g y = z\<close>)
  case False
  then have 1: "(\<forall>\<^sub>F a in F. f a \<noteq> y)"
    using fg by force
  have 2: "(g \<longlongrightarrow> z) (filtermap f F) \<or> \<not> (\<forall>\<^sub>F a in F. f a \<noteq> y)"
    by (smt (verit, best) eventually_elim2 f fS filterlim_at filterlim_def g tendsto_mono)
  show ?thesis
    using "1" "2" tendsto_compose_filtermap by blast
next
  case True
  have *: ?thesis if \<open>(g \<longlongrightarrow> z) (filtermap f F)\<close>
    using that by (simp add: tendsto_compose_filtermap)
  from g
  have \<open>(g \<longlongrightarrow> g y) (inf (nhds y) (principal (S-{y})))\<close>
    by (simp add: True at_within_def)
  then have g': \<open>(g \<longlongrightarrow> g y) (inf (nhds y) (principal S))\<close>
    using True g tendsto_at_iff_tendsto_nhds_within by blast
  from f have \<open>filterlim f (nhds y) F\<close>
    by -
  then have f': \<open>filterlim f (inf (nhds y) (principal S)) F\<close>
    using fS
    by (simp add: filterlim_inf filterlim_principal)
  from f' g' show ?thesis
    by (simp add: * True filterlim_compose filterlim_filtermap)
qed

subsection \<open>Sums\<close>

lemma sum_single: 
  assumes "finite A"
  assumes "\<And>j. j \<noteq> i \<Longrightarrow> j\<in>A \<Longrightarrow> f j = 0"
  shows "sum f A = (if i\<in>A then f i else 0)"
  apply (subst sum.mono_neutral_cong_right[where S=\<open>A \<inter> {i}\<close> and h=f])
  using assms by auto

lemma has_sum_comm_additive_general: 
  \<comment> \<open>This is a strengthening of @{thm [source] has_sum_comm_additive_general}.\<close>
  fixes f :: \<open>'b :: {comm_monoid_add,topological_space} \<Rightarrow> 'c :: {comm_monoid_add,topological_space}\<close>
  assumes f_sum: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> sum (f o g) F = f (sum g F)\<close>
      \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes inS: \<open>\<And>F. finite F \<Longrightarrow> sum g F \<in> T\<close>
  assumes cont: \<open>(f \<longlongrightarrow> f x) (at x within T)\<close>
    \<comment> \<open>For \<^class>\<open>t2_space\<close> and \<^term>\<open>T=UNIV\<close>, this is equivalent to \<open>isCont f x\<close> by @{thm [source] isCont_def}.\<close>
  assumes infsum: \<open>(g has_sum x) S\<close>
  shows \<open>((f o g) has_sum (f x)) S\<close> 
proof -
  have \<open>(sum g \<longlongrightarrow> x) (finite_subsets_at_top S)\<close>
    using infsum has_sum_def by blast
  then have \<open>((f o sum g) \<longlongrightarrow> f x) (finite_subsets_at_top S)\<close>
    apply (rule tendsto_compose_at_within[where S=T])
    using assms by auto
  then have \<open>(sum (f o g) \<longlongrightarrow> f x) (finite_subsets_at_top S)\<close>
    apply (rule tendsto_cong[THEN iffD1, rotated])
    using f_sum by fastforce
  then show \<open>((f o g) has_sum (f x)) S\<close>
    using has_sum_def by blast 
qed

lemma summable_on_comm_additive_general:
  \<comment> \<open>This is a strengthening of @{thm [source] summable_on_comm_additive_general}.\<close>
  fixes g :: \<open>'a \<Rightarrow> 'b :: {comm_monoid_add,topological_space}\<close> and f :: \<open>'b \<Rightarrow> 'c :: {comm_monoid_add,topological_space}\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> sum (f o g) F = f (sum g F)\<close>
    \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes inS: \<open>\<And>F. finite F \<Longrightarrow> sum g F \<in> T\<close>
  assumes cont: \<open>\<And>x. (g has_sum x) S \<Longrightarrow> (f \<longlongrightarrow> f x) (at x within T)\<close>
    \<comment> \<open>For \<^class>\<open>t2_space\<close> and \<^term>\<open>T=UNIV\<close>, this is equivalent to \<open>isCont f x\<close> by @{thm [source] isCont_def}.\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>(f o g) summable_on S\<close>
  by (meson assms summable_on_def has_sum_comm_additive_general has_sum_def infsum_tendsto)

lemma has_sum_metric:
  fixes l :: \<open>'a :: {metric_space, comm_monoid_add}\<close>
  shows \<open>(f has_sum l) A \<longleftrightarrow> (\<forall>e. e > 0 \<longrightarrow> (\<exists>X. finite X \<and> X \<subseteq> A \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> dist (sum f Y) l < e)))\<close>
  unfolding has_sum_def
  apply (subst tendsto_iff)
  unfolding eventually_finite_subsets_at_top
  by simp

lemma summable_on_product_finite_left:
  fixes f :: \<open>'a\<times>'b \<Rightarrow> 'c::{topological_comm_monoid_add}\<close>
  assumes sum: \<open>\<And>x. x\<in>X \<Longrightarrow> (\<lambda>y. f(x,y)) summable_on Y\<close>
  assumes \<open>finite X\<close>
  shows \<open>f summable_on (X\<times>Y)\<close>
  using \<open>finite X\<close> subset_refl[of X]
proof (induction rule: finite_subset_induct')
  case empty
  then show ?case
    by simp
next
  case (insert x F)
  have *: \<open>bij_betw (Pair x) Y ({x} \<times> Y)\<close>
    apply (rule bij_betwI')
    by auto
  from sum[of x]
  have \<open>f summable_on {x} \<times> Y\<close>
    apply (rule summable_on_reindex_bij_betw[THEN iffD1, rotated])
    by (simp_all add: * insert.hyps(2))
  then have \<open>f summable_on {x} \<times> Y \<union> F \<times> Y\<close>
    apply (rule summable_on_Un_disjoint)
    using insert by auto
  then show ?case
    by (metis Sigma_Un_distrib1 insert_is_Un)
qed

lemma summable_on_product_finite_right:
  fixes f :: \<open>'a\<times>'b \<Rightarrow> 'c::{topological_comm_monoid_add}\<close>
  assumes sum: \<open>\<And>y. y\<in>Y \<Longrightarrow> (\<lambda>x. f(x,y)) summable_on X\<close>
  assumes \<open>finite Y\<close>
  shows \<open>f summable_on (X\<times>Y)\<close>
proof -
  have \<open>(\<lambda>(y,x). f(x,y)) summable_on (Y\<times>X)\<close>
    apply (rule summable_on_product_finite_left)
    using assms by auto
  then show ?thesis
    apply (subst summable_on_reindex_bij_betw[where g=prod.swap and A=\<open>Y\<times>X\<close>, symmetric])
    apply (simp add: bij_betw_def product_swap)
    by (metis (mono_tags, lifting) case_prod_unfold prod.swap_def summable_on_cong)
qed

subsection \<open>Complex numbers\<close>

lemma cmod_Re:
  assumes "x \<ge> 0"
  shows "cmod x = Re x"
  using assms unfolding less_eq_complex_def cmod_def
  by auto

lemma abs_complex_real[simp]: "abs x \<in> \<real>" for x :: complex
  by (simp add: abs_complex_def)

lemma Im_abs[simp]: "Im (abs x) = 0"
  using abs_complex_real complex_is_Real_iff by blast


lemma cnj_x_x: "cnj x * x = (abs x)\<^sup>2"
proof (cases x)
  show "cnj x * x = \<bar>x\<bar>\<^sup>2"
    if "x = Complex x1 x2"
    for x1 :: real
      and x2 :: real
    using that
    by (auto simp: complex_cnj complex_mult abs_complex_def
        complex_norm power2_eq_square complex_of_real_def)
qed

lemma cnj_x_x_geq0[simp]: \<open>cnj x * x \<ge> 0\<close>
  by (simp add: less_eq_complex_def)

lemma complex_of_real_leq_1_iff[iff]: \<open>complex_of_real x \<le> 1 \<longleftrightarrow> x \<le> 1\<close>
  by (simp add: less_eq_complex_def)

lemma x_cnj_x: \<open>x * cnj x = (abs x)\<^sup>2\<close>
  by (metis cnj_x_x mult.commute)

subsection \<open>List indices and enum\<close>

fun index_of where
  "index_of x [] = (0::nat)"
| "index_of x (y#ys) = (if x=y then 0 else (index_of x ys + 1))"

definition "enum_idx (x::'a::enum) = index_of x (enum_class.enum :: 'a list)"

lemma index_of_length: "index_of x y \<le> length y"
  apply (induction y) by auto

lemma index_of_correct:
  assumes "x \<in> set y"
  shows "y ! index_of x y = x"
  using assms apply (induction y arbitrary: x)
  by auto

lemma enum_idx_correct: 
  "Enum.enum ! enum_idx i = i"
proof-
  have "i \<in> set enum_class.enum"
    using UNIV_enum by blast 
  thus ?thesis
    unfolding enum_idx_def
    using index_of_correct by metis
qed

lemma index_of_bound: 
  assumes "y \<noteq> []" and "x \<in> set y"
  shows "index_of x y < length y"
  using assms proof(induction y arbitrary: x)
  case Nil
  thus ?case by auto
next
  case (Cons a y)
  show ?case 
  proof(cases "a = x")
    case True
    thus ?thesis by auto
  next
    case False
    moreover have "a \<noteq> x \<Longrightarrow> index_of x y < length y"
      using Cons.IH Cons.prems(2) by fastforce      
    ultimately show ?thesis by auto
  qed
qed

lemma enum_idx_bound[simp]: "enum_idx x < CARD('a)" for x :: "'a::enum"
proof-
  have p1: "False"
    if "(Enum.enum :: 'a list) = []"
  proof-
    have "(UNIV::'a set) = set ([]::'a list)"
      using that UNIV_enum by metis
    also have "\<dots> = {}"
      by blast
    finally have "(UNIV::'a set) = {}".
    thus ?thesis by simp
  qed    
  have p2: "x \<in> set (Enum.enum :: 'a list)"
    using UNIV_enum by auto
  moreover have "(enum_class.enum::'a list) \<noteq> []"
    using p2 by auto
  ultimately show ?thesis
    unfolding enum_idx_def card_UNIV_length_enum
    using index_of_bound [where x = x and y = "(Enum.enum :: 'a list)"]
    by auto   
qed

lemma index_of_nth:
  assumes "distinct xs"
  assumes "i < length xs"
  shows "index_of (xs ! i) xs = i"
  using assms
  by (metis gr_implies_not_zero index_of_bound index_of_correct length_0_conv nth_eq_iff_index_eq nth_mem)

lemma enum_idx_enum: 
  assumes \<open>i < CARD('a::enum)\<close>
  shows \<open>enum_idx (enum_class.enum ! i :: 'a) = i\<close>
  unfolding enum_idx_def apply (rule index_of_nth)
  using assms by (simp_all add: card_UNIV_length_enum enum_distinct)

subsection \<open>Filtering lists/sets\<close>

lemma map_filter_map: "List.map_filter f (map g l) = List.map_filter (f o g) l"
proof (induction l)
  show "List.map_filter f (map g []) = List.map_filter (f \<circ> g) []"
    by (simp add: map_filter_simps)
  show "List.map_filter f (map g (a # l)) = List.map_filter (f \<circ> g) (a # l)"
    if "List.map_filter f (map g l) = List.map_filter (f \<circ> g) l"
    for a :: 'c
      and l :: "'c list"
    using that  map_filter_simps(1)
    by (metis comp_eq_dest_lhs list.simps(9))
qed

lemma map_filter_Some[simp]: "List.map_filter (\<lambda>x. Some (f x)) l = map f l"
proof (induction l)
  show "List.map_filter (\<lambda>x. Some (f x)) [] = map f []"
    by (simp add: map_filter_simps)
  show "List.map_filter (\<lambda>x. Some (f x)) (a # l) = map f (a # l)"
    if "List.map_filter (\<lambda>x. Some (f x)) l = map f l"
    for a :: 'b
      and l :: "'b list"
    using that by (simp add: map_filter_simps(1))
qed

lemma filter_Un: "Set.filter f (x \<union> y) = Set.filter f x \<union> Set.filter f y"
  unfolding Set.filter_def by auto  

lemma Set_filter_unchanged: "Set.filter P X = X" if "\<And>x. x\<in>X \<Longrightarrow> P x" for P and X :: "'z set"
  using that unfolding Set.filter_def by auto

subsection \<open>Maps\<close>

definition "inj_map \<pi> = (\<forall>x y. \<pi> x = \<pi> y \<and> \<pi> x \<noteq> None \<longrightarrow> x = y)"

definition "inv_map \<pi> = (\<lambda>y. if Some y \<in> range \<pi> then Some (inv \<pi> (Some y)) else None)"

lemma inj_map_total[simp]: "inj_map (Some o \<pi>) = inj \<pi>"
  unfolding inj_map_def inj_def by simp

lemma inj_map_Some[simp]: "inj_map Some"
  by (simp add: inj_map_def)

lemma inv_map_total: 
  assumes "surj \<pi>"
  shows "inv_map (Some o \<pi>) = Some o inv \<pi>"
proof-
  have "(if Some y \<in> range (\<lambda>x. Some (\<pi> x))
          then Some (SOME x. Some (\<pi> x) = Some y)
          else None) =
         Some (SOME b. \<pi> b = y)"
    if "surj \<pi>"
    for y
    using that by auto
  hence  "surj \<pi> \<Longrightarrow>
    (\<lambda>y. if Some y \<in> range (\<lambda>x. Some (\<pi> x))
         then Some (SOME x. Some (\<pi> x) = Some y) else None) =
    (\<lambda>x. Some (SOME xa. \<pi> xa = x))"
    by (rule ext) 
  thus ?thesis 
    unfolding inv_map_def o_def inv_def
    using assms by linarith
qed

lemma inj_map_map_comp[simp]: 
  assumes a1: "inj_map f" and a2: "inj_map g" 
  shows "inj_map (f \<circ>\<^sub>m g)"
  using a1 a2
  unfolding inj_map_def
  by (metis (mono_tags, lifting) map_comp_def option.case_eq_if option.expand)

lemma inj_map_inv_map[simp]: "inj_map (inv_map \<pi>)"
proof (unfold inj_map_def, rule allI, rule allI, rule impI, erule conjE)
  fix x y
  assume same: "inv_map \<pi> x = inv_map \<pi> y"
    and pix_not_None: "inv_map \<pi> x \<noteq> None"
  have x_pi: "Some x \<in> range \<pi>" 
    using pix_not_None unfolding inv_map_def apply auto
    by (meson option.distinct(1))
  have y_pi: "Some y \<in> range \<pi>" 
    using pix_not_None unfolding same unfolding inv_map_def apply auto
    by (meson option.distinct(1))
  have "inv_map \<pi> x = Some (Hilbert_Choice.inv \<pi> (Some x))"
    unfolding inv_map_def using x_pi by simp
  moreover have "inv_map \<pi> y = Some (Hilbert_Choice.inv \<pi> (Some y))"
    unfolding inv_map_def using y_pi by simp
  ultimately have "Hilbert_Choice.inv \<pi> (Some x) = Hilbert_Choice.inv \<pi> (Some y)"
    using same by simp
  thus "x = y"
    by (meson inv_into_injective option.inject x_pi y_pi)
qed

subsection \<open>Lattices\<close>

unbundle lattice_syntax

text \<open>The following lemma is identical to @{thm [source] Complete_Lattices.uminus_Inf} 
  except for the more general sort.\<close>
lemma uminus_Inf: "- (\<Sqinter>A) = \<Squnion>(uminus ` A)" for A :: \<open>'a::complete_orthocomplemented_lattice set\<close>
proof (rule order.antisym)
  show "- \<Sqinter>A \<le> \<Squnion>(uminus ` A)"
    by (rule compl_le_swap2, rule Inf_greatest, rule compl_le_swap2, rule Sup_upper) simp
  show "\<Squnion>(uminus ` A) \<le> - \<Sqinter>A"
    by (rule Sup_least, rule compl_le_swap1, rule Inf_lower) auto
qed

text \<open>The following lemma is identical to @{thm [source] Complete_Lattices.uminus_INF}
  except for the more general sort.\<close>
lemma uminus_INF: "- (INF x\<in>A. B x) = (SUP x\<in>A. - B x)" for B :: \<open>'a \<Rightarrow> 'b::complete_orthocomplemented_lattice\<close>
  by (simp add: uminus_Inf image_image)

text \<open>The following lemma is identical to @{thm [source] Complete_Lattices.uminus_Sup}
  except for the more general sort.\<close>
lemma uminus_Sup: "- (\<Squnion>A) = \<Sqinter>(uminus ` A)" for A :: \<open>'a::complete_orthocomplemented_lattice set\<close>
  by (metis (no_types, lifting) uminus_INF image_cong image_ident ortho_involution)

text \<open>The following lemma is identical to @{thm [source] Complete_Lattices.uminus_SUP}
  except for the more general sort.\<close>
lemma uminus_SUP: "- (SUP x\<in>A. B x) = (INF x\<in>A. - B x)" for B :: \<open>'a \<Rightarrow> 'b::complete_orthocomplemented_lattice\<close>
  by (simp add: uminus_Sup image_image)

lemma has_sumI_metric:
  fixes l :: \<open>'a :: {metric_space, comm_monoid_add}\<close>
  assumes \<open>\<And>e. e > 0 \<Longrightarrow> \<exists>X. finite X \<and> X \<subseteq> A \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> dist (sum f Y) l < e)\<close>
  shows \<open>(f has_sum l) A\<close>
  unfolding has_sum_metric using assms by simp

lemma limitin_pullback_topology: 
  \<open>limitin (pullback_topology A g T) f l F \<longleftrightarrow> l\<in>A \<and> (\<forall>\<^sub>F x in F. f x \<in> A) \<and> limitin T (g o f) (g l) F\<close>
  apply (simp add: topspace_pullback_topology limitin_def openin_pullback_topology imp_ex flip: ex_simps(1))
  apply rule
   apply simp
   apply safe
  using eventually_mono apply fastforce
   apply (simp add: eventually_conj_iff)
  by (simp add: eventually_conj_iff)

lemma tendsto_coordinatewise: \<open>(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>x. ((\<lambda>i. f i x) \<longlongrightarrow> l x) F)\<close>
proof (intro iffI allI)
  assume asm: \<open>(f \<longlongrightarrow> l) F\<close>
  then show \<open>((\<lambda>i. f i x) \<longlongrightarrow> l x) F\<close> for x
    apply (rule continuous_on_tendsto_compose[where s=UNIV, rotated])
    by auto
next
  assume asm: \<open>(\<forall>x. ((\<lambda>i. f i x) \<longlongrightarrow> l x) F)\<close>
  show \<open>(f \<longlongrightarrow> l) F\<close>
  proof (unfold tendsto_def, intro allI impI)
    fix S assume \<open>open S\<close> and \<open>l \<in> S\<close>
    from product_topology_open_contains_basis[OF \<open>open S\<close>[unfolded open_fun_def] \<open>l \<in> S\<close>]
    obtain U where lU: \<open>l \<in> Pi UNIV U\<close> and openU: \<open>\<And>x. open (U x)\<close> and finiteD: \<open>finite {x. U x \<noteq> UNIV}\<close> and US: \<open>Pi UNIV U \<subseteq> S\<close>
      by (auto simp add: PiE_UNIV_domain)

    define D where \<open>D = {x. U x \<noteq> UNIV}\<close>
    with finiteD have finiteD: \<open>finite D\<close>
      by simp
    have PiUNIV: \<open>t \<in> Pi UNIV U \<longleftrightarrow> (\<forall>x\<in>D. t x \<in> U x)\<close> for t
      using D_def by blast

    have f_Ui: \<open>\<forall>\<^sub>F i in F. f i x \<in> U x\<close> for x
      using asm[rule_format, of x] openU[of x]
      using lU topological_tendstoD by fastforce

    have \<open>\<forall>\<^sub>F x in F. \<forall>i\<in>D. f x i \<in> U i\<close>
      using finiteD
    proof induction
      case empty
      then show ?case
        by simp
    next
      case (insert x F)
      with f_Ui show ?case
        by (simp add: eventually_conj_iff)
    qed

    then show \<open>\<forall>\<^sub>F x in F. f x \<in> S\<close>
      using US by (simp add: PiUNIV eventually_mono in_mono)
  qed
qed

lemma limitin_closure_of:
  assumes limit: \<open>limitin T f c F\<close>
  assumes in_S: \<open>\<forall>\<^sub>F x in F. f x \<in> S\<close>
  assumes nontrivial: \<open>\<not> trivial_limit F\<close>
  shows \<open>c \<in> T closure_of S\<close>
proof (intro in_closure_of[THEN iffD2] conjI impI allI)
  from limit show \<open>c \<in> topspace T\<close>
    by (simp add: limitin_topspace)
  fix U
  assume \<open>c \<in> U \<and> openin T U\<close>
  with limit have \<open>\<forall>\<^sub>F x in F. f x \<in> U\<close>
    by (simp add: limitin_def)
  with in_S have \<open>\<forall>\<^sub>F x in F. f x \<in> U \<and> f x \<in> S\<close>
    by (simp add: eventually_frequently_simps)
  with nontrivial
  show \<open>\<exists>y. y \<in> S \<and> y \<in> U\<close>
    using eventually_happens' by blast
qed


end
