(* Theory: Lovasz_Local_Lemma
   Author: Chelsea Edmonds *)

section \<open>Lovasz Local Lemma \<close>

theory Lovasz_Local_Lemma 
  imports 
    Basic_Method 
    "HOL-Real_Asymp.Real_Asymp" 
    Indep_Events
    Digraph_Extensions
begin

(* The following two lemmas were taken from Gauss_Sums.Polya_Vinogradov AFP entry. 
  Adding in entire dependency caused a significant slow down, could these be moved to the Analysis 
  library at some point? *)
lemma ln_add_one_self_less_self:
  fixes x :: real
  assumes "x > 0" 
  shows "ln (1 + x) < x"
proof -
  have "0 \<le> x" "0 < x" "exp x > 0" "1+x > 0" using assms by simp+
  have "1 + x < 1 + x + x\<^sup>2 / 2"
    using \<open>0 < x\<close> by auto
  also have "\<dots> \<le> exp x"
    using exp_lower_Taylor_quadratic[OF \<open>0 \<le> x\<close>] by blast
  finally have "1 + x < exp (x)" by blast
  then have "ln (1 + x) < ln (exp (x))" 
    using ln_less_cancel_iff[OF \<open>1+x > 0\<close> \<open>exp(x) > 0\<close>] by auto
  also have "\<dots> = x" using ln_exp by blast
  finally show ?thesis by auto
qed

lemma exp_1_bounds:
  assumes "x > (0::real)"
  shows   "exp 1 > (1 + 1 / x) powr x" and "exp 1 < (1 + 1 / x) powr (x+1)"
proof -
  have "ln (1 + 1 / x) < 1 / x"
    using ln_add_one_self_less_self assms by simp
  thus "exp 1 > (1 + 1 / x) powr x" using assms
    by (simp add: field_simps powr_def)
next
  have "1 < (x + 1) * ln ((x + 1) / x)" (is "_ < ?f x")
  proof (rule DERIV_neg_imp_decreasing_at_top[where ?f = ?f])
    fix t assume t: "x \<le> t"
    have "(?f has_field_derivative (ln (1 + 1 / t) - 1 / t)) (at t)"
      using t assms by (auto intro!: derivative_eq_intros simp:divide_simps)
    moreover have "ln (1 + 1 / t) - 1 / t < 0"
      using ln_add_one_self_less_self[of "1 / t"] t assms by auto
    ultimately show "\<exists>y. ((\<lambda>t. (t + 1) * ln ((t + 1) / t)) has_real_derivative y) (at t) \<and> y < 0"
      by blast
  qed real_asymp
  thus "exp 1 < (1 + 1 / x) powr (x + 1)"
    using assms by (simp add: powr_def field_simps)
qed


subsection \<open>Random Lemmas on Product Operator \<close>

lemma prod_constant_ge: 
  fixes y :: "'b :: {comm_monoid_mult, linordered_semidom}"
  assumes "card A \<le> k"
  assumes "y \<ge> 0" and "y < 1"
  shows "(\<Prod>x\<in> A. y) \<ge> y ^ k"
using assms(1) proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  then show ?case using assms(2) assms(3) by (simp add: power_le_one) 
next
  case empty
  then show ?case using assms(2) assms(3) by (simp add: power_le_one) 
next
  case (insert x F)
  then show ?case using assms(2) assms(3)
    by (metis nless_le power_decreasing prod_constant) 
qed

lemma (in linordered_idom) prod_mono3:
  assumes "finite J" "I \<subseteq> J" "\<And>i. i \<in> J \<Longrightarrow> 0 \<le> f i"  "(\<And>i. i \<in> J \<Longrightarrow> f i \<le> 1)"
  shows "prod f J \<le> prod f I"
proof -
  have "prod f J \<le> (\<Prod>i\<in>J. if i \<in> I then f i else 1)"
    using assms by (intro prod_mono) auto
  also have "\<dots> = prod f I"
    using \<open>finite J\<close> \<open>I \<subseteq> J\<close> by (simp add: prod.If_cases Int_absorb1)
  finally show ?thesis .
qed

lemma bij_on_ss_image: 
  assumes "A \<subseteq> B"
  assumes "bij_betw g B B'"
  shows "g ` A \<subseteq> B'"
  using assms by (auto simp add: bij_betw_apply subsetD)

lemma bij_on_ss_proper_image: 
  assumes "A \<subset> B"
  assumes "bij_betw g B B'"
  shows "g ` A \<subset> B'"
proof (intro psubsetI subsetI)
  fix x assume "x \<in> g ` A"
  then show "x \<in> B'" using assms bij_betw_apply subsetD by fastforce 
next
  show "g ` A \<noteq> B'" using assms by (auto) (smt (verit, best) bij_betw_iff_bijections imageE subset_eq) 
qed


subsection \<open>Dependency Graph Concept \<close>

text \<open>Uses directed graphs. The pair\_digraph locale was sufficient as multi-edges are irrelevant \<close>

locale dependency_digraph = pair_digraph "G :: nat pair_pre_digraph" + prob_space "M :: 'a measure" 
  for G M + fixes F :: "nat \<Rightarrow> 'a set"
  assumes vss: "F ` (pverts G) \<subseteq> events"
  assumes mis: "\<And> i. i \<in> (pverts G) \<Longrightarrow> mutual_indep_events (F i) F ((pverts G) - ({i} \<union> neighborhood i))" 
begin

lemma dep_graph_indiv_nh_indep: 
  assumes "A \<in> pverts G" "B \<in> pverts G"
  assumes "B \<notin> neighborhood A"
  assumes "A \<noteq> B"
  assumes "prob (F B) \<noteq> 0"
  shows "\<P>((F A) | (F B)) = prob (F A)"
proof-
  have "B \<notin> {A} \<union> neighborhood A" using assms(3) assms(4) by auto
  then have "B \<in> (pverts G - ({A} \<union> neighborhood A))" using assms(2) by auto
  moreover have "mutual_indep_events (F A) F (pverts G - ({A} \<union> neighborhood A))" using mis assms by auto
  ultimately show ?thesis using 
      assms(5) assms(1) assms(2) vss mutual_indep_ev_cond_single by auto
qed

lemma mis_subset: 
  assumes "i \<in> pverts G"
  assumes "A \<subseteq> pverts G"
  shows "mutual_indep_events (F i) F (A - ({i} \<union> neighborhood i))"
proof (cases "A \<subseteq> ({i} \<union> neighborhood i)")
  case True
  then have "A - ({i} \<union> neighborhood i) = {}" by auto
  then show ?thesis using mutual_indep_ev_empty vss assms(1) by blast
next
  case False
  then have "A - ({i} \<union> neighborhood i) \<subseteq> pverts G - ({i} \<union> neighborhood i)" using assms(2) by auto
  then show ?thesis using mutual_indep_ev_subset mis assms(1) by blast
qed

lemma dep_graph_indep_events:
  assumes "A \<subseteq> pverts G"
  assumes "\<And> Ai. Ai \<in> A \<Longrightarrow> out_degree G Ai = 0"
  shows "indep_events F A"
proof -
  have "\<And> Ai. Ai \<in> A \<Longrightarrow> (mutual_indep_events (F Ai) F (A - {Ai}))"
  proof -
    fix Ai assume ain: "Ai \<in> A"
    then have "(neighborhood Ai) = {}" using assms(2) neighborhood_empty_iff by simp
    moreover have "mutual_indep_events (F Ai) F (A - ({Ai} \<union> neighborhood Ai))" 
      using mis_subset[of Ai A] ain assms(1) by auto
    ultimately show "mutual_indep_events (F Ai) F (A - {Ai})" by simp
  qed
  then show ?thesis using mutual_indep_ev_set_all[of F A] vss by auto 
qed

end

subsection \<open>Lovasz Local General Lemma \<close>
context prob_space
begin

lemma compl_sets_index: 
  assumes "F ` A \<subseteq> events"
  shows "(\<lambda> i. space M - F i) ` A \<subseteq> events"
proof (intro subsetI)
  fix x assume "x \<in> (\<lambda>i. space M - F i) ` A"
  then obtain i where xeq: "x = space M - F i" and "i \<in> A" by blast
  then have "F i \<in> events" using assms by auto
  thus "x \<in> events" using sets.compl_sets xeq by simp
qed

lemma lovasz_inductive_base: 
  assumes "dependency_digraph G M F"
  assumes "\<And> Ai . Ai \<in> A \<Longrightarrow> g Ai \<ge> 0 \<and> g Ai < 1"
  assumes "\<And> Ai.  Ai \<in> A \<Longrightarrow> (prob (F Ai) \<le> (g Ai) * (\<Prod> Aj \<in> pre_digraph.neighborhood G Ai. (1 - (g Aj))))"
  assumes "Ai \<in> A"
  assumes "pverts G = A"
  shows "prob (F Ai) \<le> g Ai"
proof -
  have genprod: "\<And> S. S \<subseteq> A \<Longrightarrow> (\<Prod>Aj \<in> S . (1 - (g Aj))) \<le> 1" using assms(2)
    by (smt (verit) prod_le_1 subsetD) 
  interpret dg: dependency_digraph G M F using assms(1) by simp
  have "dg.neighborhood Ai \<subseteq> A" using assms(3) dg.neighborhood_wf assms(5) by simp
  then  show ?thesis 
    using genprod assms mult_left_le by (smt (verit)) 
qed

lemma lovasz_inductive_base_set: 
  assumes "N \<subseteq> A"
  assumes "\<And> Ai . Ai \<in> A \<Longrightarrow> g Ai \<ge> 0 \<and> g Ai < 1"
  assumes "\<And> Ai.  Ai \<in> A \<Longrightarrow> (prob (F Ai) \<le> (g Ai) * (\<Prod> Aj \<in> N. (1 - (g Aj))))"
  assumes "Ai \<in> A"
  shows "prob (F Ai) \<le> g Ai"
proof -
  have genprod: "\<And> S. S \<subseteq> A \<Longrightarrow> (\<Prod>Aj \<in> S . (1 - (g Aj))) \<le> 1" using assms(2)
    by (smt (verit) prod_le_1 subsetD) 
  then  show ?thesis 
    using genprod assms mult_left_le by (smt (verit)) 
qed

lemma split_prob_lt_helper:
  assumes dep_graph: "dependency_digraph G M F"
  assumes dep_graph_verts: "pverts G = A"
  assumes fbounds: "\<And> i . i \<in> A \<Longrightarrow> f i \<ge> 0 \<and> f i < 1"
  assumes prob_Ai: "\<And> Ai.  Ai \<in> A \<Longrightarrow> prob (F Ai) \<le> 
    (f Ai) * (\<Prod> Aj \<in> pre_digraph.neighborhood G Ai . (1 - (f Aj)))"
  assumes aiin: "Ai \<in> A"
  assumes "N \<subseteq> pre_digraph.neighborhood G Ai"
  assumes "\<exists> P1 P2. \<P>(F Ai | \<Inter>Aj\<in>S. space M - F Aj) = P1/P2 \<and> 
    P1 \<le> prob (F Ai)\<and> P2 \<ge> (\<Prod> Aj \<in> N . (1 - (f Aj)))"
  shows "\<P>(F Ai | \<Inter>Aj\<in>S. space M - F Aj) \<le> f Ai"
proof -
  interpret dg: dependency_digraph G M F using assms(1) by simp
  have lt1: "\<And> Aj. Aj \<in> A \<Longrightarrow>  (1 - (f Aj)) \<le> 1"
    using assms(3) by auto
  have gt0: "\<And> Aj. Aj \<in> A \<Longrightarrow> (1 - (f Aj)) > 0" using assms(3) by auto
  then have prodgt0: "\<And> S'. S' \<subseteq> A \<Longrightarrow>  (\<Prod> Aj \<in> S' . (1 - f Aj)) > 0"
    using prod_pos by (metis subsetD) 
  obtain P1 P2 where peq: "\<P>(F Ai | \<Inter>Aj\<in>S. space M - F Aj) = P1/P2" and  
   "P1 \<le> prob (F Ai)"
    and p2gt: "P2 \<ge> (\<Prod> Aj \<in> N . (1 - (f Aj)))" using assms(7) by auto
  then have "P1 \<le> (f Ai) * (\<Prod> Aj \<in> pre_digraph.neighborhood G Ai . (1 - (f Aj)))" 
    using prob_Ai aiin by fastforce
  moreover have "P2 \<ge> (\<Prod> Aj \<in> dg.neighborhood Ai . (1 - (f Aj)))" using assms(6) 
      gt0 dg.neighborhood_wf dep_graph_verts subset_iff lt1 dg.neighborhood_finite p2gt
    by (smt (verit, ccfv_threshold) prod_mono3) 
  ultimately have "P1/P2 \<le> ((f Ai) * (\<Prod> Aj \<in> dg.neighborhood Ai . (1 - (f Aj)))/(\<Prod> Aj \<in> dg.neighborhood Ai . (1 - (f Aj))))"
    using frac_le[of "(f Ai) * (\<Prod> Aj \<in> dg.neighborhood Ai . (1 - (f Aj)))" "P1" "(\<Prod> Aj \<in> dg.neighborhood Ai . (1 - (f Aj)))"] 
      prodgt0[of "dg.neighborhood Ai"] assms(3) dg.neighborhood_wf[of Ai]
    by (simp add: assms(2) bounded_measure finite_measure_compl assms(5))
  then show ?thesis using prodgt0[of "dg.neighborhood Ai"] dg.neighborhood_wf[of Ai] assms(2) peq
    by (metis divide_eq_imp rel_simps(70)) 
qed

lemma lovasz_inequality: 
  assumes finS: "finite S"
  assumes sevents: "F ` S \<subseteq> events"
  assumes S_subset: "S \<subseteq> A - {Ai}"
  assumes prob2: "prob (\<Inter> Aj \<in> S . (space M - (F Aj))) > 0"
  assumes irange: "i \<in> {0..<card S1}"
  assumes bb: "bij_betw g {0..<card S1} S1"
  assumes s1_def: "S1 = (S \<inter> N)"
  assumes s2_def: "S2 = S - S1"
  assumes ne_cond: "i > 0 \<or> S2 \<noteq> {}"
  assumes hyps: "\<And> B. B \<subset> S \<Longrightarrow> g i \<in> A \<Longrightarrow> B \<subseteq> A - {g i} \<Longrightarrow> B \<noteq> {} \<Longrightarrow> 
    0 < prob (\<Inter>Aj\<in>B. space M - F Aj) \<Longrightarrow> \<P>(F (g i) | \<Inter>Aj\<in>B. space M - F Aj) \<le> f (g i)"
  shows "\<P>((space M - F (g i)) | (\<Inter> ((\<lambda> i. space M - F i) ` g ` {0..<i} \<union> ((\<lambda> i. space M - F i) ` S2)))) 
    \<ge> (1 - f (g i))"
proof -
  let ?c = "(\<lambda> i. space M - F i)"
  define S1ss where "S1ss = g ` {0..<i}" 
  have "i \<notin> {0..<i}" by simp
  moreover have "{0..<i} \<subseteq> {0..<card S1}" using irange by simp
  ultimately have ginotin1: "g i \<notin> S1ss" using bb S1ss_def irange
    by (smt (verit, best) bij_betw_iff_bijections image_iff subset_eq) 
  have ginotin2: "g i \<notin> S2" unfolding s2_def using irange bb by (simp add: bij_betwE) 
  have giS: "g i \<in> S" using irange bij_betw_imp_surj_on imageI Int_iff s1_def bb 
    by blast
  have "{0..<i} \<subset> {0..<card S1}" using irange by auto
  then have "S1ss \<subset> S1" unfolding S1ss_def using irange bb bij_on_ss_proper_image by meson
  then have sss: "S1ss \<union> S2 \<subset> S" using s1_def s2_def by blast 
  moreover have xsiin: "g i \<in> A"using irange  
    using giS S_subset by (metis DiffE in_mono)
  moreover have ne: "S1ss \<union> S2 \<noteq> {}" using ne_cond S1ss_def by auto
  moreover have "S1ss \<union> S2 \<subseteq> A - {g i}"  using S_subset sss ginotin1 ginotin2 by auto
  moreover have gt02: "0 < prob (\<Inter> (?c ` (S1ss \<union> S2)))" using finS prob2 sevents
    prob_inter_ss_lt_index[of S ?c "S1ss \<union> S2"] ne sss compl_sets_index[of F S]  by fastforce
  ultimately have ltfAi: "\<P>(F (g i) | \<Inter> (?c ` (S1ss \<union> S2))) \<le> f (g i)"
    using hyps[of "S1ss \<union> S2"] by blast 
  have "?c ` (S1ss \<union> S2) \<subseteq> events" using sss \<open>S1ss \<subset> S1\<close> compl_subset_in_events sevents s1_def s2_def
    by fastforce
  then have "\<Inter> (?c ` (S1ss \<union> S2)) \<in> events" using Inter_event_ss sss
    by (meson \<open>S1ss \<union> S2 \<noteq> {}\<close> finite_imageI finite_subset image_is_empty finS subset_iff_psubset_eq)
  moreover have "F (g i) \<in> events" using xsiin giS sevents by auto
  ultimately have "\<P>(?c (g i) | \<Inter> (?c ` (S1ss \<union> S2))) \<ge> 1 - f (g i)" 
    using cond_prob_neg[of "\<Inter> (?c ` (S1ss \<union> S2))" "F (g i)"] gt02 xsiin ltfAi by simp
  then show "\<P>(?c (g i) | (\<Inter> (?c ` g ` {0..<i} \<union> (?c ` S2)))) \<ge> (1 - f (g i))"
    by (simp add: S1ss_def image_Un)
qed

text \<open>The main helper lemma \<close>
lemma lovasz_inductive: 
  assumes finA: "finite A"
  assumes Aevents: "F ` A \<subseteq> events"
  assumes fbounds: "\<And> i . i \<in> A \<Longrightarrow> f i \<ge> 0 \<and> f i < 1"
  assumes dep_graph: "dependency_digraph G M F"
  assumes dep_graph_verts: "pverts G = A"
  assumes prob_Ai: "\<And> Ai.  Ai \<in> A \<Longrightarrow> prob (F Ai) \<le> 
    (f Ai) * (\<Prod> Aj \<in> pre_digraph.neighborhood G Ai . (1 - (f Aj)))"
  assumes Ai_in: "Ai \<in> A"
  assumes S_subset: "S \<subseteq> A - {Ai}"
  assumes S_nempty: "S \<noteq> {}"
  assumes prob2: "prob (\<Inter> Aj \<in> S . (space M - (F Aj))) > 0"
  shows "\<P>((F Ai) | (\<Inter> Aj \<in> S . (space M - (F Aj)))) \<le> f Ai"
proof -
  let ?c = "\<lambda> i. space M - F i"
  have ceq: "\<And> A. ?c ` A = ((-) (space M)) ` (F ` A)"  by auto
  interpret dg: dependency_digraph G M F using assms(4) by simp
  have finS: "finite S" using assms finite_subset by (metis finite_Diff) 
  show "\<P>(( F Ai) | (\<Inter> Aj \<in> S . (space M - (F Aj)))) \<le> f Ai" 
    using finS Ai_in S_subset S_nempty prob2
  proof (induct S arbitrary: Ai rule: finite_psubset_induct )
    case (psubset S)
    define S1 where "S1 = (S \<inter> dg.neighborhood Ai)"
    define S2 where "S2 = S - S1"
    have "\<And> s . s \<in> S2 \<Longrightarrow> s \<in> A - ({Ai} \<union> dg.neighborhood Ai)" 
      using S1_def S2_def psubset.prems(2) by blast 
    then have s2ssmis: "S2 \<subseteq> A - ({Ai} \<union> dg.neighborhood Ai)" by auto
    have sevents: "F ` S \<subseteq> events" using assms(2) psubset.prems(2) by auto
    then have s1events: "F ` S1 \<subseteq> events" using S1_def by auto
    have finS2: "finite S2" and finS1: "finite S1" using S2_def S1_def by (simp_all add: psubset(1))
    have "mutual_indep_set (F Ai) (F ` S2)" using dg.mis[of Ai] mutual_indep_ev_subset s2ssmis 
      psubset.prems(1) dep_graph_verts mutual_indep_iff by auto
    then have mis2: "mutual_indep_set (F Ai) (?c ` S2)" 
      using mutual_indep_events_compl[of "F ` S2" "F Ai"] finS2 ceq[of S2] by simp
    have scompl_ev: "?c ` S \<subseteq> events"
      using compl_sets_index sevents by simp
    then have s2cev: "?c ` S2 \<subseteq> events" using S2_def scompl_ev by blast
    have "(\<Inter> Aj \<in> S . space M - (F Aj)) \<subseteq> (\<Inter> Aj \<in> S2 . space M - (F Aj))"
      unfolding S2_def using Diff_subset image_mono Inter_anti_mono by blast
    then have "S2 \<noteq> {} \<Longrightarrow> prob (\<Inter> Aj \<in> S2 . space M - (F Aj)) \<noteq> 0" using psubset.prems(4) s2cev 
      finS2 Inter_event_ss[of "?c ` S2"] finite_measure_mono[of "\<Inter> (?c ` S)" "\<Inter>(?c ` S2)"] by simp
    then have s2prob_eq: "S2 \<noteq> {} \<Longrightarrow> \<P>((F Ai) | (\<Inter> (?c ` S2))) = prob (F Ai)" using assms(2)
      mutual_indep_cond_full[of " F Ai" "?c ` S2"]  psubset.prems(1) s2cev finS2 mis2 by simp
    show ?case 
    proof (cases "S1 = {}")
      case True
      then show ?thesis using lovasz_inductive_base[of G F A f Ai]  psubset.prems(3) S2_def
          assms(3) assms(4) psubset.prems(1) prob_Ai s2prob_eq dep_graph_verts by (simp) 
    next
      case s1F: False
      then have csgt0: "card S1 > 0" using s1F finS1 card_gt_0_iff by blast
      obtain g where bb: "bij_betw g {0..<card S1} S1" using finS1 ex_bij_betw_nat_finite by auto
      have igt0: "\<And>i. i \<in> {0..<card S1} \<Longrightarrow> 1 - f (g i) \<ge> 0"
        using S1_def psubset.prems(2) bb bij_betw_apply assms(3) by fastforce
      have s1ss: "S1 \<subseteq> dg.neighborhood Ai" using S1_def by auto
      moreover have "\<exists> P1 P2. \<P>(F Ai | \<Inter>Aj\<in>S. space M - F Aj) = P1/P2 \<and>  P1 \<le> prob (F Ai) 
        \<and> P2 \<ge> (\<Prod> Aj \<in> S1 . (1 - (f Aj)))"
      proof (cases "S2 = {}")
        case True
        then have Seq: "S1 = S" using S1_def S2_def by auto
        have inter_eventsS: "(\<Inter> Aj \<in> S . (space M - (F Aj))) \<in> events" using  psubset.prems assms
          by (meson measure_notin_sets zero_less_measure_iff)
        then have peq: "\<P>((F Ai) | (\<Inter> Aj \<in> S1 . ?c Aj)) = 
            prob ((\<Inter> Aj \<in> S1 . ?c Aj) \<inter> (F Ai))/prob ((\<Inter> (?c ` S1)))" 
            (is "\<P>((F Ai) | (\<Inter> Aj \<in> S1 . ?c Aj)) = ?Num/?Den")
          using cond_prob_ev_def[of "(\<Inter> Aj \<in> S1 . (space M - (F Aj)))" "F Ai"] 
          using Seq psubset.prems(1) assms(2) by blast
        have "?Num \<le> prob (F Ai)" using finite_measure_mono assms(2) psubset.prems(1) by simp
        moreover have "?Den \<ge> (\<Prod> Aj \<in> S1 . (1 - (f Aj)))"
        proof -
          have pcond: "prob (\<Inter>(?c ` S1)) = 
              prob (?c (g 0)) * (\<Prod>i \<in> {1..<card S1} . \<P>(?c (g i) | (\<Inter>(?c ` g ` {0..<i}))))"
            using prob_cond_inter_index_fn_compl[of "S1" F] Seq s1events psubset(1) s1F bb by auto
          have ineq: "\<And> i. i \<in> {1..<card S1} \<Longrightarrow> \<P>(?c (g i) | (\<Inter>(?c ` g ` {0..<i}))) \<ge> (1 - (f (g i)))" 
            using lovasz_inequality[of S1 F A Ai _ S1 g S1 "{}" f] sevents finS psubset.prems(2) 
              psubset.prems(4)  bb psubset.hyps(2)[of _ "g _"] Seq by fastforce
          have "(\<And>i. i \<in> {1..<card S1} \<Longrightarrow> 1 - f (g i) \<ge> 0)" using igt0 by simp
          then have "(\<Prod>i \<in> {1..<(card S1)} . \<P>(?c (g i) | (\<Inter>(?c ` g ` {0..<i})))) 
            \<ge> (\<Prod>i \<in> {1..<(card S1)} . (1 - (f (g i))))" 
            using ineq prod_mono by (smt(verit, ccfv_threshold))
          moreover have "prob (?c (g 0)) \<ge> (1 - f (g 0))" 
          proof -
            have g0in: "g 0 \<in> A" using bb csgt0 using psubset.prems(2) bij_betwE Seq by fastforce
            then have "prob (?c (g 0)) = 1 - prob (F (g 0))" using Aevents by (simp add: prob_compl) 
            then show ?thesis using lovasz_inductive_base[of G F A f "g 0"] 
                prob_Ai assms(4) dep_graph_verts fbounds g0in by auto
          qed
          moreover have "0 \<le> (\<Prod>i = 1..<card S1. 1 - f (g i))" using igt0 by (simp add: prod_nonneg) 
          ultimately have  "prob (\<Inter>(?c ` S1)) \<ge> (1 - (f (g 0))) * (\<Prod>i \<in> {1..<(card S1)} . (1 - (f (g i))))" 
            using pcond igt0 mult_mono'[of "(1 - (f (g 0)))" ] by fastforce
          moreover have "{0..<card S1} = {0} \<union> {1..<card S1}" using csgt0 by auto
          ultimately have "prob (\<Inter>(?c ` S1)) \<ge> (\<Prod>i \<in> {0..<(card S1)} . (1 - (f (g i))))" by auto     
          moreover have "(\<Prod>i \<in> {0..<(card S1)} . (1 - (f (g i)))) = (\<Prod>i \<in> S1 . (1 - (f (i))))" 
            using prod.reindex_bij_betw bb by simp
          ultimately show ?thesis by simp
        qed
        ultimately show ?thesis using peq Seq by blast 
      next
        case s2F: False
        have s2inter: "\<Inter> (?c ` S2) \<in> events" 
          using s2F finS2 s2cev Inter_event_ss[of "?c ` S2"]  by auto
        have split: "(\<Inter> Aj \<in> S . (?c Aj)) = (\<Inter> (?c `S1)) \<inter> (\<Inter> (?c ` S2))" 
          using S1_def S2_def by auto
        then have "\<P>(F Ai | (\<Inter> Aj \<in> S . (?c Aj))) = \<P>(F Ai | (\<Inter> (?c `S1)) \<inter> (\<Inter> (?c ` S2)))" by simp
        moreover have s2n0: "prob (\<Inter> (?c ` S2)) \<noteq> 0" using psubset.prems(4) S2_def
          by (metis Int_lower2 split finite_measure_mono measure_le_0_iff s2inter semiring_norm(137)) 
        moreover have "\<Inter> (?c ` S1) \<in> events" 
          using finS1 S1_def scompl_ev s1F Inter_event_ss[of "(?c ` S1)"] by auto
        ultimately have peq: "\<P>(F Ai | (\<Inter> Aj \<in> S . (?c Aj))) = \<P>(F Ai \<inter> (\<Inter> (?c `S1)) | \<Inter> (?c ` S2))/ 
          \<P>(\<Inter> (?c `S1) | \<Inter> (?c `S2))" (is "\<P>(F Ai | (\<Inter> Aj \<in> S . (?c Aj))) = ?Num/?Den")
          using cond_prob_dual_intersect[of "F Ai" "\<Inter> (?c `S1)" "\<Inter> (?c `S2)"]  assms(2) 
            psubset.prems(1) s2inter by fastforce
        have "?Num \<le> \<P>(F Ai | \<Inter> (?c `S2))" using cond_prob_inter_set_lt[of "F Ai" "\<Inter> (?c `S2)" "?c ` S1"]
          using s1events finS1 psubset.prems(1) assms(2) s2inter finite_imageI[of S1 F] by blast
        then have "?Num \<le> prob (F Ai)" using s2F s2prob_eq by auto
        moreover have "?Den \<ge> (\<Prod> Aj \<in> S1 . (1 - (f Aj)))"  using psubset.hyps
        proof -
          have "prob (\<Inter>(?c ` S2)) > 0" using s2n0 by (meson zero_less_measure_iff) 
          then have pcond: "\<P>(\<Inter> (?c `S1) | \<Inter> (?c `S2)) = 
              (\<Prod>i = 0..<card S1 . \<P>(?c (g i) | (\<Inter> (?c ` g ` {0..<i} \<union> (?c ` S2)))))"
            using prob_cond_Inter_index_cond_compl_fn[of S1 "?c ` S2" F] s1F finS1 s2cev finS2 s2F 
              s1events bb by auto  
          have  "\<And> i. i \<in> {0..<card S1} \<Longrightarrow> \<P>(?c (g i) | (\<Inter> (?c ` g ` {0..<i} \<union> (?c ` S2)))) \<ge> (1 - f (g i))"
            using lovasz_inequality[of S F A Ai _ S1 g "dg.neighborhood Ai" S2 f] S1_def S2_def sevents 
              finS psubset.prems(2) psubset.prems(4)  bb psubset.hyps(2)[of _ "g _"] psubset(1) s2F by meson
          then have c1: "\<P>(\<Inter> (?c `S1) | \<Inter> (?c `S2)) \<ge> (\<Prod>i = 0..<card S1 . (1 - f (g i)))" 
            using prod_mono igt0 pcond bb  by (smt(verit, ccfv_threshold))
          then have "\<P>(\<Inter> (?c `S1) | \<Inter> (?c `S2)) \<ge> (\<Prod>i \<in> {0..<card S1} . (1 - f (g i)))" by blast
          moreover have "(\<Prod>i \<in> {0..<card S1} . (1 - f (g i))) = (\<Prod>x \<in> S1 . (1 - f x))" using bb
            using prod.reindex_bij_betw by fastforce 
          ultimately show ?thesis by simp
        qed 
        ultimately show ?thesis using peq by blast
      qed
      ultimately show ?thesis  by (intro split_prob_lt_helper[of G F A])
        (simp_all add: dep_graph dep_graph_verts fbounds psubset.prems(1) prob_Ai)
    qed
  qed
qed

text \<open>The main lemma \<close>
theorem lovasz_local_general: 
  assumes "A \<noteq> {}"
  assumes "F ` A \<subseteq> events"
  assumes "finite A"
  assumes "\<And> Ai . Ai \<in> A \<Longrightarrow>  f Ai \<ge> 0 \<and> f Ai < 1"
  assumes "dependency_digraph G M F"
  assumes "\<And> Ai.  Ai \<in> A \<Longrightarrow> (prob (F Ai) \<le> (f Ai) * (\<Prod> Aj \<in> pre_digraph.neighborhood G Ai. (1 - (f Aj))))"
  assumes "pverts G = A"
  shows "prob (\<Inter> Ai \<in> A . (space M - (F Ai))) \<ge> (\<Prod> Ai \<in> A . (1 - f Ai))" "(\<Prod> Ai \<in> A . (1 - f Ai)) > 0"
proof -
  show gt0: "(\<Prod> Ai \<in> A . (1 - f Ai)) > 0" using assms(4) by (simp add: prod_pos)
  let ?c = "\<lambda> i. space M - F i"
  interpret dg: dependency_digraph G M F using assms(5) by simp
  have general: "\<And>Ai S. Ai \<in> A \<Longrightarrow> S \<subseteq> A - {Ai} \<Longrightarrow> S \<noteq> {} \<Longrightarrow>  prob (\<Inter> Aj \<in> S . (?c Aj)) > 0 
    \<Longrightarrow>  \<P>(F Ai | (\<Inter> Aj \<in> S . (?c Aj))) \<le> f Ai" 
    using assms lovasz_inductive[of A F f G] by simp
  have base: "\<And> Ai. Ai \<in> A \<Longrightarrow> prob (F Ai) \<le> f Ai"
    using lovasz_inductive_base assms(4) assms(6) assms(5) assms(7) by blast
  show "prob (\<Inter> Ai \<in> A . (?c Ai)) \<ge> (\<Prod> Ai \<in> A . (1 - f Ai))"
    using assms(3) assms(1) assms(2) assms(4) general base
  proof (induct A rule: finite_ne_induct)
    case (singleton x)
    then show ?case using singleton.prems singleton prob_compl by auto
  next
    case (insert x X)
    define Ax where "Ax = ?c ` (insert x X)"
    have xie: "F x \<in> events" using insert.prems by simp
    have A'ie: "\<Inter>(?c ` X) \<in> events" using insert.prems insert.hyps by auto
    have "(\<And>Ai S. Ai \<in> insert x X \<Longrightarrow> S \<subseteq> insert x X - {Ai} \<Longrightarrow> S \<noteq> {} \<Longrightarrow> prob (\<Inter> Aj \<in> S . (?c Aj)) > 0 
      \<Longrightarrow> \<P>(F Ai | \<Inter> (?c ` S)) \<le> f Ai)" using insert.prems by simp
    then have  "(\<And>Ai S. Ai \<in> X \<Longrightarrow> S \<subseteq> X - {Ai} \<Longrightarrow> S \<noteq> {} \<Longrightarrow>  prob (\<Inter> Aj \<in> S . (?c Aj)) > 0 
      \<Longrightarrow> \<P>(F Ai | \<Inter> (?c ` S)) \<le> f Ai)" by auto
    then have A'gt: "(\<Prod>Ai\<in>X. 1 - f Ai) \<le> prob (\<Inter> (?c ` X))"
      using insert.hyps(4) insert.prems(2) insert.prems(1) insert.prems(4) by auto
    then have "prob (\<Inter>(?c ` X)) > 0" using insert.hyps insert.prems prod_pos basic_trans_rules(22) 
      diff_gt_0_iff_gt by (metis (no_types, lifting) insert_Diff insert_subset subset_insertI) 
    then have "\<P>((?c x) | (\<Inter>(?c ` X))) = 1 - \<P>(F x | (\<Inter>(?c ` X)))" 
      using cond_prob_neg[of "\<Inter>(?c ` X)" "F x"] xie A'ie by simp
    moreover have "\<P>(F x | (\<Inter>(?c ` X))) \<le> f x" using insert.prems(3)[of x X]  insert.hyps(2) insert(3) 
        A'gt \<open>0 < prob (\<Inter> (?c ` X))\<close> by fastforce
    ultimately have pnxgt: "\<P>((?c x) | (\<Inter>(?c ` X))) \<ge> 1 - f x" by simp
    have xgt0: "1 - f x \<ge> 0" using insert.prems(2)[of x] by auto
    have "prob (\<Inter> Ax) = prob ((?c x) \<inter> \<Inter>(?c ` X))" using Ax_def by simp
    also have "... = prob (\<Inter>(?c ` X)) * \<P>((?c x) | (\<Inter>(?c ` X)))" 
      using prob_intersect_B xie A'ie by simp
    also have "... \<ge> (\<Prod>Ai\<in>X. 1 - f Ai) * (1 - f x)" using A'gt pnxgt mult_left_le 
        \<open>0 < prob (\<Inter>(?c ` X))\<close> xgt0 mult_mono by (smt(verit))
    finally have "prob (\<Inter> Ax) \<ge> (\<Prod>Ai\<in>insert x X. 1 - f Ai)"
      by (simp add: local.insert(1) local.insert(3) mult.commute) 
    then show ?case using Ax_def by auto
  qed
qed

subsection \<open>Lovasz Corollaries and Variations \<close>

corollary lovasz_local_general_positive: 
  assumes "A \<noteq> {}"
  assumes "F ` A \<subseteq> events"
  assumes "finite A"
  assumes "\<And> Ai . Ai \<in> A \<Longrightarrow>  f Ai \<ge> 0 \<and> f Ai < 1"
  assumes "dependency_digraph G M F"
  assumes "\<And> Ai.  Ai \<in> A \<Longrightarrow> (prob (F Ai) \<le> 
    (f Ai) * (\<Prod> Aj \<in> pre_digraph.neighborhood G Ai. (1 - (f Aj))))"
  assumes "pverts G = A"
  shows "prob (\<Inter> Ai \<in> A . (space M - (F Ai))) > 0"
  using assms lovasz_local_general(1)[of A F f G] lovasz_local_general(2)[of A F f G] by simp

theorem lovasz_local_symmetric_dep_graph: 
  fixes e :: real
  fixes d :: nat
  assumes "A \<noteq> {}"
  assumes "F ` A \<subseteq> events"
  assumes "finite A"
  assumes "dependency_digraph G M F"
  assumes "\<And> Ai.  Ai \<in> A \<Longrightarrow> out_degree G Ai \<le> d" 
  assumes "\<And> Ai. Ai \<in> A \<Longrightarrow> prob (F Ai) \<le> p"
  assumes "exp(1)* p * (d + 1) \<le> 1" (* e should be euler's number \<Rightarrow> using exponential function? *)
  assumes "pverts G = A"
  shows "prob (\<Inter> Ai \<in> A . (space M - (F Ai))) > 0"
proof (cases "d = 0")
  case True
  interpret g: dependency_digraph G M F using assms(4) by simp
  (* Because all have mutual independence \<Longrightarrow> complete independence *)
  have "indep_events F A" using g.dep_graph_indep_events[of A] assms(8) assms(5) True by simp
  moreover have "p < 1" 
  proof -
    have "exp (1) * p \<le> 1" using assms(7) True by simp
    then show ?thesis using exp_gt_one  less_1_mult linorder_neqE_linordered_idom rel_simps(68) 
      verit_prod_simplify(2) by (smt (verit) mult_le_cancel_left1)
  qed
  ultimately show ?thesis 
    using complete_indep_bound3[of A F] assms(2) assms(1) assms(3) assms(6) by force
next
  case False
  define f :: "nat \<Rightarrow> real" where "f \<equiv> (\<lambda> Ai . 1 /(d + 1))"
  then have fbounds: "\<And> Ai. f Ai \<ge> 0 \<and> f Ai < 1" using f_def False by simp
  interpret dg: dependency_digraph G M F using assms(4) by auto
(* Showing bound is the most work *)
  have "\<And> Ai. Ai \<in> A \<Longrightarrow> prob (F Ai) \<le> (f Ai) * (\<Prod> Aj \<in> dg.neighborhood Ai . (1 - (f Aj)))"
  proof -
    fix Ai assume ain: "Ai \<in> A"
    have d_boundslt1: "(1/(d + 1)) < 1" and d_boundsgt0: "(1/(d + 1))> 0" using False by fastforce+ 
    have d_bounds2: "(1 - (1 /(d + 1)))^d < 1" using False 
      by(simp add: field_simps) (smt (verit) of_nat_0_le_iff power_mono_iff)
    have d_bounds0: "(1 - (1 /(d + 1)))^d > 0" using False by (simp)
    have "exp(1) > (1 + 1/d) powr d" using exp_1_bounds(1) False by simp
    then have "exp(1) > (1 + 1/d)^d" using False by (simp add: powr_realpow zero_compare_simps(2))
    moreover have "1/(1+ 1/d)^d = (1 - (1/(d+1)))^d"
    proof -
      have "1/(1+ 1/d)^d = 1/((d/d) + 1/d)^d" by (simp add: field_simps)
      then show ?thesis by (simp add: field_simps)
    qed
    ultimately have exp_lt: "1/exp(1) < (1 - (1 /(d + 1)))^d"
      by (metis d_bounds0 frac_less2 less_eq_real_def of_nat_zero_less_power_iff power_eq_if zero_less_divide_1_iff) 
    then have "(1 /(d + 1))* (1 - (1 /(d + 1)))^d > (1 /(d + 1))*(1/exp(1))"
      using exp_lt mult_strict_left_mono[of "1/exp(1)" "(1 - (1 /(d + 1)))^d" "(1/(d+1))"] d_boundslt1 
      by simp
    then have "(1 /(d + 1))* (1 - (1 /(d + 1)))^d > (1/((d+1)*exp(1)))" by auto 
    then have gtp: "(1 /(d + 1))* (1 - (1 /(d + 1)))^d > p"
      by (smt (verit, ccfv_SIG) d_boundslt1 d_boundsgt0 assms(7) divide_divide_eq_left divide_less_cancel 
          divide_less_eq divide_nonneg_nonpos nonzero_mult_div_cancel_left not_exp_le_zero) 
    have "card (dg.neighborhood Ai) \<le> d" using assms(5) dg.out_degree_neighborhood ain by auto
    then have "(\<Prod> Aj \<in> dg.neighborhood Ai . (1 - (1 /(d + 1)))) \<ge> (1 - (1 /(d + 1)))^d"
      using prod_constant_ge[of  "dg.neighborhood Ai" "d" "1 - (1/d+1)"] using d_boundslt1 by auto
    then have "(1 /(d + 1)) * (\<Prod> Aj \<in> dg.neighborhood Ai . (1 - (1 /(d + 1)))) \<ge> (1 /(d + 1))* (1 - (1 /(d + 1)))^d"
      by (simp add: divide_right_mono) 
    then have "(1 /(d + 1)) * (\<Prod> Aj \<in> dg.neighborhood Ai . (1 - (1 /(d + 1)))) > p" 
      using gtp by simp
    then show "prob (F Ai) \<le> f Ai * (\<Prod> Aj \<in> dg.neighborhood Ai . (1 - f Aj))"
      using assms(6) \<open>Ai \<in> A\<close> f_def by force 
  qed
  then show ?thesis using lovasz_local_general_positive[of A F f G] 
      assms(4) assms(1) assms(2) assms(3) assms(8) fbounds by auto
qed

corollary lovasz_local_symmetric4gt: 
  fixes e :: real
  fixes d :: nat
  assumes "A \<noteq> {}"
  assumes "F ` A \<subseteq> events"
  assumes "finite A"
  assumes "dependency_digraph G M F"
  assumes "\<And> Ai.  Ai \<in> A \<Longrightarrow> out_degree G Ai \<le> d" 
  assumes "\<And> Ai. Ai \<in> A \<Longrightarrow> prob (F Ai) \<le> p"
  assumes "4 * p * d \<le> 1" (* only works if d \ge 3 *)
  assumes "d \<ge> 3"
  assumes "pverts G = A"
  shows "prob (\<Inter> Ai \<in> A . (space M - F Ai)) > 0"
proof -
  have "exp(1)* p * (d + 1) \<le> 1"
  proof (cases "p = 0")
    case True
    then show ?thesis by simp
  next
    case False
    then have pgt: "p > 0" using assms(1) assms(6) assms(3) ex_min_if_finite less_eq_real_def
      by (meson basic_trans_rules(23) basic_trans_rules(24) linorder_neqE_linordered_idom measure_nonneg)
    have "3 * (d + 1) \<le> 4 * d" by (simp add: field_simps assms(8))
    then have "exp(1) * (d + 1) \<le> 4 *d"
      using exp_le exp_gt_one[of 1] assms(8)
      by (smt (verit, del_insts) Num.of_nat_simps(2) Num.of_nat_simps(5) le_add2 le_eq_less_or_eq 
          mult_right_mono nat_less_real_le numeral.simps(3) numerals(1) of_nat_numeral) 
    then have "exp(1) * (d + 1) * p \<le> 4 *d *p" using pgt by simp 
    then show ?thesis using assms(7) by (simp add: field_simps) 
  qed
  then show ?thesis using assms lovasz_local_symmetric_dep_graph[of A F G d p] by auto
qed


lemma lovasz_local_symmetric4: 
  fixes e :: real
  fixes d :: nat
  assumes "A \<noteq> {}"
  assumes "F ` A \<subseteq> events"
  assumes "finite A"
  assumes "dependency_digraph G M F"
  assumes "\<And> Ai.  Ai \<in> A \<Longrightarrow> out_degree G Ai \<le> d" 
  assumes "\<And> Ai. Ai \<in> A \<Longrightarrow> prob (F Ai) \<le> p"
  assumes "4 * p * d \<le> 1"
  assumes "d \<ge> 1"
  assumes "pverts G = A"
  shows "prob (\<Inter> Ai \<in> A . (space M - F Ai)) > 0"
proof (cases "d \<ge> 3")
  case True
  then show ?thesis using lovasz_local_symmetric4gt assms
    by presburger
next
  case d3: False
  define f :: "nat \<Rightarrow> real" where "f \<equiv> (\<lambda> Ai . 1 /(d + 1))"
  then have fbounds: "\<And> Ai. f Ai \<ge> 0 \<and> f Ai < 1" using f_def assms(8) by simp
  interpret dg: dependency_digraph G M F using assms(4) by auto
  have "\<And> Ai. Ai \<in> A \<Longrightarrow> prob (F Ai) \<le> (f Ai) * (\<Prod> Aj \<in> dg.neighborhood Ai . (1 - (f Aj)))"
  proof -
    fix Ai assume ain: "Ai \<in> A"
    have d_boundslt1: "(1/(d + 1)) < 1" and d_boundsgt0: "(1/(d + 1))> 0" using assms by fastforce+ 
    have plt: "1/(4*d) \<ge> p" using assms(7) assms(8)
      by (metis (mono_tags, opaque_lifting) Num.of_nat_simps(5) bot_nat_0.not_eq_extremum le_numeral_extra(2) 
          more_arith_simps(11) mult_of_nat_commute nat_0_less_mult_iff of_nat_0_less_iff of_nat_numeral 
          pos_divide_less_eq rel_simps(51) verit_comp_simplify(3)) 
    then have gtp: "(1 /(d + 1))* (1 - (1 /(d + 1)))^d \<ge> p"
    proof (cases "d = 1")
      case False
      then have "d = 2" using d3 assms(8) by auto 
      then show ?thesis using plt by (simp add: field_simps)
    qed (simp)
    have "card (dg.neighborhood Ai) \<le> d" using assms(5) dg.out_degree_neighborhood ain by auto
    then have "(\<Prod> Aj \<in> dg.neighborhood Ai . (1 - (1 /(d + 1)))) \<ge> (1 - (1 /(d + 1)))^d"
      using prod_constant_ge[of  "dg.neighborhood Ai" "d" "1 - (1/d+1)"] using d_boundslt1 by auto
    then have "(1 /(d + 1)) * (\<Prod> Aj \<in> dg.neighborhood Ai . (1 - (1 /(d + 1)))) \<ge> (1 /(d + 1))* (1 - (1 /(d + 1)))^d"
      by (simp add: divide_right_mono) 
    then have "(1 /(d + 1)) * (\<Prod> Aj \<in> dg.neighborhood Ai . (1 - (1 /(d + 1)))) \<ge> p" 
      using gtp by simp
    then show "prob (F Ai) \<le> f Ai * (\<Prod> Aj \<in> dg.neighborhood Ai . (1 - f Aj))"
      using assms(6) \<open>Ai \<in> A\<close> f_def by force 
  qed
  then show ?thesis 
    using lovasz_local_general_positive[of A F f G] assms(4) assms(1) assms(2) assms(3) assms(9) fbounds by auto
qed

text \<open>Converting between dependency graph and indexed set representation of mutual independence \<close>

lemma (in pair_digraph) g_Ai_simplification:
  assumes "Ai \<in> A"
  assumes "g Ai \<subseteq> A - {Ai}"
  assumes "pverts G = A"
  assumes "parcs G = {e \<in> A \<times> A . snd e \<in> (A - ({fst e} \<union> (g (fst e))))}"
  shows "g Ai = A - ({Ai} \<union> neighborhood Ai)"
proof -
  have "g Ai = A - ({Ai} \<union> {v \<in> A . v \<in> (A - ({Ai} \<union> (g (Ai))))})"  using assms(2) by auto
  then have "g Ai = A - ({Ai} \<union> {v \<in> A . (Ai, v) \<in> parcs G})"
    using Collect_cong assms(1) mem_Collect_eq assms(3) assms(4) by auto
  then show "g Ai = A - ({Ai} \<union> neighborhood Ai)" unfolding neighborhood_def using assms(3) by simp
qed

lemma define_dep_graph_set:
  assumes "A \<noteq> {}"
  assumes "F ` A \<subseteq> events"
  assumes "finite A"
  assumes "\<And> Ai. Ai \<in> A \<Longrightarrow> g Ai \<subseteq> A - {Ai} \<and> mutual_indep_events (F Ai) F (g Ai)"
  shows "dependency_digraph \<lparr> pverts = A, parcs = {e \<in> A \<times> A . snd e \<in> (A - ({fst e} \<union> (g (fst e))))} \<rparr> M F"
    (is "dependency_digraph ?G M F")
proof -
  interpret pd: pair_digraph ?G 
    using assms(3)by (unfold_locales) auto 
  have "\<And> Ai. Ai \<in> A \<Longrightarrow> g Ai \<subseteq> A - {Ai}" using assms(4) by simp
  then have "\<And> i. i \<in> A \<Longrightarrow> g i = A - ({i} \<union> pd.neighborhood i)"
    using pd.g_Ai_simplification[of _ A g] pd.pair_digraph by auto
  then have "dependency_digraph ?G M F" using assms(2) assms(4) by (unfold_locales) auto
  then show ?thesis by simp
qed

lemma define_dep_graph_deg_bound:
  assumes "A \<noteq> {}"
  assumes "F ` A \<subseteq> events"
  assumes "finite A"
  assumes "\<And> Ai. Ai \<in> A \<Longrightarrow> g Ai \<subseteq> A - {Ai} \<and> card (g Ai) \<ge> card A - d - 1 \<and> 
    mutual_indep_events (F Ai) F (g Ai)"
  shows "\<And> Ai.  Ai \<in> A \<Longrightarrow> 
    out_degree \<lparr> pverts = A, parcs = {e \<in> A \<times> A . snd e \<in> (A - ({fst e} \<union> (g (fst e))))} \<rparr> Ai \<le> d"
    (is "\<And> Ai.  Ai \<in> A \<Longrightarrow> out_degree (with_proj ?G) Ai \<le> d")
proof -
  interpret pd: dependency_digraph ?G M F using assms define_dep_graph_set by simp
  show "\<And> Ai.  Ai \<in> A \<Longrightarrow> out_degree ?G Ai \<le> d"
  proof -
    fix Ai assume a: "Ai \<in> A"
    then have geq: "g Ai = A - ({Ai} \<union> pd.neighborhood Ai)" 
      using assms(4)[of Ai] pd.pair_digraph pd.g_Ai_simplification[of Ai A g ]  by simp
    then have pss: "g Ai \<subset> A" using a by auto
    then have "card (g Ai) = card (A - ({Ai} \<union> pd.neighborhood Ai))" using assms(4) geq by argo
    moreover have ss: "({Ai} \<union> pd.neighborhood Ai) \<subseteq> A" using pd.neighborhood_wf a  by simp
    moreover have "finite ({Ai} \<union> pd.neighborhood Ai)" 
      using calculation(2) assms(3) finite_subset by auto
    moreover have "Ai \<notin> pd.neighborhood Ai" using pd.neighborhood_self_not by simp
    moreover have "card {Ai} = 1" using is_singleton_altdef by auto
    moreover have cardss: "card ({Ai} \<union> pd.neighborhood Ai) = 1 + card (pd.neighborhood Ai)" 
      using calculation(5) calculation(4) card_Un_disjoint pd.neighborhood_finite by auto
    ultimately have eq: "card (g Ai) = card A - 1 - card (pd.neighborhood Ai)" 
      using card_Diff_subset[of "({Ai} \<union> pd.neighborhood Ai)" A] assms(3) by presburger
    have ggt: "\<And> Ai. Ai \<in> A \<Longrightarrow> card (g Ai) \<ge> int (card A) - int d - 1"
      using assms(4) by fastforce 
    have "card (pd.neighborhood Ai) = card A - 1 - card (g Ai)" 
      using cardss assms(3) card_mono diff_add_inverse diff_diff_cancel diff_le_mono ss eq
      by (metis (no_types, lifting)) 
    moreover have "card A \<ge> (1 + card (g Ai))" using pss assms(3) card_seteq not_less_eq_eq by auto 
    ultimately have "card (pd.neighborhood Ai) = int (card A) - 1 - int (card (g Ai))"  by auto
    moreover have "int (card (g Ai)) \<ge> (card A) - (int d) - 1" using ggt a by simp
    ultimately show "out_degree ?G Ai \<le> d" using pd.out_degree_neighborhood by simp
  qed
qed

lemma obtain_dependency_graph:
  assumes "A \<noteq> {}"
  assumes "F ` A \<subseteq> events"
  assumes "finite A"
  assumes "\<And> Ai. Ai \<in> A \<Longrightarrow> 
    (\<exists> S . S \<subseteq> A - {Ai} \<and> card S \<ge> card A - d - 1 \<and> mutual_indep_events (F Ai) F S)"
  obtains G where "dependency_digraph G M F" "pverts G = A" "\<And> Ai.  Ai \<in> A \<Longrightarrow> out_degree G Ai \<le> d"
proof -
  obtain g where gdef: "\<And> Ai. Ai \<in> A \<Longrightarrow> g Ai \<subseteq> A - {Ai} \<and> card (g Ai) \<ge> card A - d - 1 \<and> 
    mutual_indep_events (F Ai) F (g Ai)" using assms(4) by metis
  then show ?thesis 
    using define_dep_graph_set[of A F g] define_dep_graph_deg_bound[of A F g d]that assms by auto 
qed

text \<open>This is the variation of the symmetric version most commonly in use \<close>

theorem lovasz_local_symmetric: 
  fixes d :: nat
  assumes "A \<noteq> {}"
  assumes "F ` A \<subseteq> events"
  assumes "finite A"
  assumes "\<And> Ai. Ai \<in> A \<Longrightarrow> (\<exists> S . S \<subseteq> A - {Ai} \<and> card S \<ge> card A - d - 1 \<and> mutual_indep_events (F Ai) F S)" 
  assumes "\<And> Ai. Ai \<in> A \<Longrightarrow> prob (F Ai) \<le> p"
  assumes "exp(1)* p * (d + 1) \<le> 1"
  shows "prob (\<Inter> Ai \<in> A . (space M - (F Ai))) > 0"
proof -
  obtain G where odg: "dependency_digraph G M F" "pverts G = A" "\<And> Ai.  Ai \<in> A \<Longrightarrow> out_degree G Ai \<le> d"
    using assms obtain_dependency_graph by metis
  then show ?thesis using odg assms lovasz_local_symmetric_dep_graph[of A F G d p] by auto
qed

lemma lovasz_local_symmetric4_set: 
  fixes d :: nat
  assumes "A \<noteq> {}"
  assumes "F ` A \<subseteq> events"
  assumes "finite A"
  assumes "\<And> Ai. Ai \<in> A \<Longrightarrow> (\<exists> S . S \<subseteq> A - {Ai} \<and> card S \<ge> card A - d - 1 \<and> mutual_indep_events (F Ai) F S)" 
  assumes "\<And> Ai. Ai \<in> A \<Longrightarrow> prob (F Ai) \<le> p"
  assumes "4 * p * d \<le> 1"
  assumes "d \<ge> 1"
  shows "prob (\<Inter> Ai \<in> A . (space M - F Ai)) > 0"
proof -
  obtain G where odg: "dependency_digraph G M F" "pverts G = A" "\<And> Ai.  Ai \<in> A \<Longrightarrow> out_degree G Ai \<le> d"
    using assms obtain_dependency_graph by metis
  then show ?thesis using odg assms lovasz_local_symmetric4[of A F G d p] by auto
qed
end

end