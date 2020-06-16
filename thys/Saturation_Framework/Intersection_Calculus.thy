(*  Title:       Calculi Based on the Intersection of Redundancy Criteria
 *   Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018-2020 *)

section \<open>Calculi Based on the Intersection of Redundancy Criteria\<close>

text \<open>In this section, section 2.3 of the report is covered, on calculi
  equipped with a family of redundancy criteria.\<close>

theory Intersection_Calculus
  imports
    Calculus
    Ordered_Resolution_Prover.Lazy_List_Liminf
    Ordered_Resolution_Prover.Lazy_List_Chain
begin


subsection \<open>Calculi with a Family of Redundancy Criteria\<close>

locale intersection_calculus =
  inference_system Inf + consequence_relation_family Bot Q entails_q
  for
    Bot :: "'f set" and
    Inf :: \<open>'f inference set\<close> and
    Q :: "'q set" and
    entails_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> bool"
  + fixes
    Red_Inf_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f inference set" and
    Red_F_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set"
  assumes
    Q_nonempty: "Q \<noteq> {}" and
    all_red_crit: "\<forall>q \<in> Q. calculus Bot Inf (entails_q q) (Red_Inf_q q) (Red_F_q q)"
begin

definition Red_Inf_Q :: "'f set \<Rightarrow> 'f inference set" where
  "Red_Inf_Q N = (\<Inter>q \<in> Q. Red_Inf_q q N)"

definition Red_F_Q :: "'f set \<Rightarrow> 'f set" where
  "Red_F_Q N = (\<Inter>q \<in> Q. Red_F_q q N)"

(* lem:intersection-of-red-crit *)
sublocale calculus Bot Inf entails_Q Red_Inf_Q Red_F_Q
  unfolding calculus_def calculus_axioms_def
proof (intro conjI)
  show "consequence_relation Bot entails_Q"
  using intersect_cons_rel_family .
next
  show "\<forall>N. Red_Inf_Q N \<subseteq> Inf"
    unfolding Red_Inf_Q_def
  proof
    fix N
    show "(\<Inter>q \<in> Q. Red_Inf_q q N) \<subseteq> Inf"
    proof (intro Inter_subset)
      fix Red_Infs
      assume one_red_inf: "Red_Infs \<in> (\<lambda>q. Red_Inf_q q N) ` Q"
      show "Red_Infs \<subseteq> Inf"
        using one_red_inf all_red_crit calculus.Red_Inf_to_Inf by blast
    next
      show "(\<lambda>q. Red_Inf_q q N) ` Q \<noteq> {}"
        using Q_nonempty by blast
    qed
  qed
next
  show "\<forall>B N. B \<in> Bot \<longrightarrow> N \<Turnstile>Q {B} \<longrightarrow> N - Red_F_Q N \<Turnstile>Q {B}"
  proof (intro allI impI)
    fix B N
    assume
      B_in: "B \<in> Bot" and
      N_unsat: "N \<Turnstile>Q {B}"
    show "N - Red_F_Q N \<Turnstile>Q {B}" unfolding entails_Q_def Red_F_Q_def
    proof
      fix qi
      assume qi_in: "qi \<in> Q"
      define entails_qi (infix "\<Turnstile>qi" 50) where "entails_qi = entails_q qi"
      have cons_rel_qi: "consequence_relation Bot entails_qi"
        unfolding entails_qi_def using qi_in all_red_crit calculus.axioms(1) by blast
      define Red_F_qi where "Red_F_qi = Red_F_q qi"
      have red_qi_in_Q: "Red_F_Q N \<subseteq> Red_F_qi N"
        unfolding Red_F_Q_def Red_F_qi_def using qi_in image_iff by blast
      then have "N - Red_F_qi N \<subseteq> N - Red_F_Q N" by blast
      then have entails_1: "N - Red_F_Q N \<Turnstile>qi N - Red_F_qi N"
        using qi_in all_red_crit
        unfolding calculus_def consequence_relation_def entails_qi_def by metis
      have N_unsat_qi: "N \<Turnstile>qi {B}" using qi_in N_unsat unfolding entails_qi_def entails_Q_def
        by simp
      then have N_unsat_qi: "N - Red_F_qi N \<Turnstile>qi {B}"
        using qi_in all_red_crit Red_F_qi_def calculus.Red_F_Bot[OF _ B_in] entails_qi_def
        by fastforce
      show "N - (\<Inter>q \<in> Q. Red_F_q q N) \<Turnstile>qi {B}"
        using consequence_relation.entails_trans[OF cons_rel_qi entails_1 N_unsat_qi]
        unfolding Red_F_Q_def .
    qed
  qed
next
  show "\<forall>N1 N2. N1 \<subseteq> N2 \<longrightarrow> Red_F_Q N1 \<subseteq> Red_F_Q N2"
  proof (intro allI impI)
    fix N1 :: "'f set"
    and N2 :: "'f set"
    assume
      N1_in_N2: "N1 \<subseteq> N2"
    show "Red_F_Q N1 \<subseteq> Red_F_Q N2"
    proof
      fix C
      assume "C \<in> Red_F_Q N1"
      then have "\<forall>qi \<in> Q. C \<in> Red_F_q qi N1" unfolding Red_F_Q_def by blast
      then have "\<forall>qi \<in> Q. C \<in> Red_F_q qi N2"
        using N1_in_N2 all_red_crit calculus.axioms(2) calculus.Red_F_of_subset by blast
      then show "C \<in> Red_F_Q N2" unfolding Red_F_Q_def by blast
    qed
  qed
next
  show "\<forall>N1 N2. N1 \<subseteq> N2 \<longrightarrow> Red_Inf_Q N1 \<subseteq> Red_Inf_Q N2"
  proof (intro allI impI)
    fix N1 :: "'f set"
    and N2 :: "'f set"
    assume
      N1_in_N2: "N1 \<subseteq> N2"
    show "Red_Inf_Q N1 \<subseteq> Red_Inf_Q N2"
    proof
      fix \<iota>
      assume "\<iota> \<in> Red_Inf_Q N1"
      then have "\<forall>qi \<in> Q. \<iota> \<in> Red_Inf_q qi N1" unfolding Red_Inf_Q_def by blast
      then have "\<forall>qi \<in> Q. \<iota> \<in> Red_Inf_q qi N2"
        using N1_in_N2 all_red_crit calculus.axioms(2) calculus.Red_Inf_of_subset by blast
      then show "\<iota> \<in> Red_Inf_Q N2" unfolding Red_Inf_Q_def by blast
    qed
  qed
next
  show "\<forall>N2 N1. N2 \<subseteq> Red_F_Q N1 \<longrightarrow> Red_F_Q N1 \<subseteq> Red_F_Q (N1 - N2)"
  proof (intro allI impI)
    fix N2 N1
    assume N2_in_Red_N1: "N2 \<subseteq> Red_F_Q N1"
    show "Red_F_Q N1 \<subseteq> Red_F_Q (N1 - N2)"
    proof
      fix C
      assume "C \<in> Red_F_Q N1"
      then have "\<forall>qi \<in> Q. C \<in> Red_F_q qi N1" unfolding Red_F_Q_def by blast
      moreover have "\<forall>qi \<in> Q. N2 \<subseteq> Red_F_q qi N1" using N2_in_Red_N1 unfolding Red_F_Q_def by blast
      ultimately have "\<forall>qi \<in> Q. C \<in> Red_F_q qi (N1 - N2)"
        using all_red_crit calculus.axioms(2) calculus.Red_F_of_Red_F_subset
        by blast
      then show "C \<in> Red_F_Q (N1 - N2)" unfolding Red_F_Q_def by blast
    qed
  qed
next
  show "\<forall>N2 N1. N2 \<subseteq> Red_F_Q N1 \<longrightarrow> Red_Inf_Q N1 \<subseteq> Red_Inf_Q (N1 - N2)"
  proof (intro allI impI)
    fix N2 N1
    assume N2_in_Red_N1: "N2 \<subseteq> Red_F_Q N1"
    show "Red_Inf_Q N1 \<subseteq> Red_Inf_Q (N1 - N2)"
    proof
      fix \<iota>
      assume "\<iota> \<in> Red_Inf_Q N1"
      then have "\<forall>qi \<in> Q. \<iota> \<in> Red_Inf_q qi N1" unfolding Red_Inf_Q_def by blast
      moreover have "\<forall>qi \<in> Q. N2 \<subseteq> Red_F_q qi N1" using N2_in_Red_N1 unfolding Red_F_Q_def by blast
      ultimately have "\<forall>qi \<in> Q. \<iota> \<in> Red_Inf_q qi (N1 - N2)"
        using all_red_crit calculus.axioms(2) calculus.Red_Inf_of_Red_F_subset by blast
      then show "\<iota> \<in> Red_Inf_Q (N1 - N2)" unfolding Red_Inf_Q_def by blast
    qed
  qed
next
  show "\<forall>\<iota> N. \<iota> \<in> Inf \<longrightarrow> concl_of \<iota> \<in> N \<longrightarrow> \<iota> \<in> Red_Inf_Q N"
  proof (intro allI impI)
    fix \<iota> N
    assume
      i_in: "\<iota> \<in> Inf" and
      concl_in: "concl_of \<iota> \<in> N"
    then have "\<forall>qi \<in> Q. \<iota> \<in> Red_Inf_q qi N"
      using all_red_crit calculus.axioms(2) calculus.Red_Inf_of_Inf_to_N by blast
    then show "\<iota> \<in> Red_Inf_Q N" unfolding Red_Inf_Q_def by blast
  qed
qed

(* lem:satur-wrt-intersection-of-red *)
lemma sat_int_to_sat_q: "calculus.saturated Inf Red_Inf_Q N \<longleftrightarrow>
  (\<forall>qi \<in> Q. calculus.saturated Inf (Red_Inf_q qi) N)" for N
proof
  fix N
  assume inter_sat: "calculus.saturated Inf Red_Inf_Q N"
  show "\<forall>qi \<in> Q. calculus.saturated Inf (Red_Inf_q qi) N"
  proof
    fix qi
    assume qi_in: "qi \<in> Q"
    then interpret one: calculus Bot Inf "entails_q qi" "Red_Inf_q qi" "Red_F_q qi"
      by (metis all_red_crit)
    show "one.saturated N"
      using qi_in inter_sat
      unfolding one.saturated_def saturated_def Red_Inf_Q_def by blast
  qed
next
  fix N
  assume all_sat: "\<forall>qi \<in> Q. calculus.saturated Inf (Red_Inf_q qi) N"
  show "saturated N"
    unfolding saturated_def Red_Inf_Q_def
  proof
    fix \<iota>
    assume \<iota>_in: "\<iota> \<in> Inf_from N"
    have "\<forall>Red_Inf_qi \<in> Red_Inf_q ` Q. \<iota> \<in> Red_Inf_qi N"
    proof
      fix Red_Inf_qi
      assume red_inf_in: "Red_Inf_qi \<in> Red_Inf_q ` Q"
      then obtain qi where
        qi_in: "qi \<in> Q" and
        red_inf_qi_def: "Red_Inf_qi = Red_Inf_q qi" by blast
      then interpret one: calculus Bot Inf "entails_q qi" "Red_Inf_q qi" "Red_F_q qi"
        by (metis all_red_crit)
      have "one.saturated N" using qi_in all_sat red_inf_qi_def by blast
      then show "\<iota> \<in> Red_Inf_qi N" unfolding one.saturated_def using \<iota>_in red_inf_qi_def by blast
    qed
    then show "\<iota> \<in> (\<Inter>q \<in> Q. Red_Inf_q q N)" by blast
  qed
qed

(* lem:checking-static-ref-compl-for-intersections *)
lemma stat_ref_comp_from_bot_in_sat:
  "(\<forall>N. calculus.saturated Inf Red_Inf_Q N \<and> (\<forall>B \<in> Bot. B \<notin> N) \<longrightarrow>
      (\<exists>B \<in> Bot. \<exists>qi \<in> Q. \<not> entails_q qi N {B})) \<Longrightarrow>
   statically_complete_calculus Bot Inf entails_Q Red_Inf_Q Red_F_Q"
proof (rule ccontr)
  assume
    N_saturated: "\<forall>N. (calculus.saturated Inf Red_Inf_Q N \<and> (\<forall>B \<in> Bot. B \<notin> N)) \<longrightarrow>
      (\<exists>B \<in> Bot. \<exists>qi \<in> Q. \<not> entails_q qi N {B})" and
    no_stat_ref_comp: "\<not> statically_complete_calculus Bot Inf (\<Turnstile>Q) Red_Inf_Q Red_F_Q"
  obtain N1 B1 where B1_in:
    "B1 \<in> Bot" and N1_saturated: "calculus.saturated Inf Red_Inf_Q N1" and
    N1_unsat: "N1 \<Turnstile>Q {B1}" and no_B_in_N1: "\<forall>B \<in> Bot. B \<notin> N1"
    using no_stat_ref_comp by (metis calculus_axioms statically_complete_calculus.intro
        statically_complete_calculus_axioms.intro)
  obtain B2 qi where
    qi_in: "qi \<in> Q" and
    no_qi: "\<not> entails_q qi N1 {B2}"
    using N_saturated N1_saturated no_B_in_N1 by auto
  have "N1 \<Turnstile>Q {B2}" using N1_unsat B1_in intersect_cons_rel_family
    unfolding consequence_relation_def by metis
  then have "entails_q qi N1 {B2}" unfolding entails_Q_def using qi_in by blast
  then show False using no_qi by simp
qed

end


subsection \<open>Families of Calculi\<close>

locale calculus_family =
  inference_system_family Q Inf_q + consequence_relation_family Bot Q entails_q
  for
    Bot :: "'f set" and
    Q :: "'q set" and
    Inf_q :: \<open>'q \<Rightarrow> 'f inference set\<close> and
    entails_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> bool"
  + fixes
    Red_Inf_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f inference set" and
    Red_F_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set"
  assumes
    Q_nonempty: "Q \<noteq> {}" and
    all_red_crit:
      "\<forall>q \<in> Q. calculus Bot (Inf_q q) (entails_q q) (Red_Inf_q q) (Red_F_q q)"

end
