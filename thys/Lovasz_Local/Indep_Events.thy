(* Theory: Indep_Events.thy
   Author: Chelsea Edmonds *)

section \<open> Independent Events \<close>
theory Indep_Events imports Cond_Prob_Extensions
begin

subsection \<open>More bijection helpers\<close>

lemma bij_betw_obtain_subsetr:
  assumes "bij_betw f A B"
  assumes "A' \<subseteq> A"
  obtains B' where "B' \<subseteq> B" and "B' = f ` A'"
  using assms by (metis bij_betw_def image_mono) 

lemma bij_betw_obtain_subsetl:
  assumes "bij_betw f A B"
  assumes "B' \<subseteq> B"
  obtains A' where "A' \<subseteq> A" and "B' = f ` A'"
  using assms
  by (metis bij_betw_imp_surj_on subset_imageE) 

lemma bij_betw_remove:  "bij_betw f A B \<Longrightarrow> a \<in> A \<Longrightarrow> bij_betw f (A - {a}) (B - {f a})"
  using  bij_betwE notIn_Un_bij_betw3
  by (metis Un_insert_right insert_Diff member_remove  remove_def sup_bot.right_neutral)
(* Slow *)

subsection \<open>Independent Event Extensions \<close>
text \<open> Extensions on both the indep\_event definition and the indep\_events definition \<close>
context prob_space
begin

lemma indep_eventsD: "indep_events A I \<Longrightarrow> (A`I \<subseteq> events) \<Longrightarrow> J \<subseteq> I \<Longrightarrow> J \<noteq> {} \<Longrightarrow> finite J \<Longrightarrow> 
    prob (\<Inter>j\<in>J. A j) = (\<Prod>j\<in>J. prob (A j))"
  using indep_events_def[of A I] by auto 

lemma
  assumes indep: "indep_event A B"
  shows indep_eventD_ev1: "A \<in> events"
    and indep_eventD_ev2: "B \<in> events"
  using indep unfolding indep_event_def indep_events_def UNIV_bool by auto

lemma indep_eventD: 
  assumes ie: "indep_event A B"
  shows "prob (A \<inter> B) = prob (A) * prob (B)"
  using assms indep_eventD_ev1 indep_eventD_ev2 ie[unfolded indep_event_def, THEN indep_eventsD,of UNIV] 
  by (simp add: ac_simps UNIV_bool)

lemma  indep_eventI[intro]:
  assumes ev: "A \<in> events" "B \<in> events"
    and indep: "prob (A \<inter> B) = prob A * prob B"
  shows "indep_event A B"
  unfolding indep_event_def
proof (intro indep_eventsI)
  show "\<And>i. i \<in> UNIV \<Longrightarrow> (case i of True \<Rightarrow> A | False \<Rightarrow> B) \<in> events" 
    using assms by (auto split: bool.split)
next
  fix J :: "bool set" assume jss: "J \<subseteq> UNIV" and jne: "J \<noteq> {}"  and finJ: "finite J"
  have "J \<in> Pow UNIV" by auto
  then have c: "J = UNIV \<or> J = {True} \<or> J = {False}" using jne jss UNIV_bool
    by (metis (full_types) UNIV_eq_I insert_commute subset_insert subset_singletonD) 
  then show "prob (\<Inter>i\<in>J. case i of True \<Rightarrow> A | False \<Rightarrow> B) = 
      (\<Prod>i\<in>J. prob (case i of True \<Rightarrow> A | False \<Rightarrow> B)) "
    unfolding UNIV_bool using indep by (auto simp: ac_simps)
qed

text \<open>Alternate set definition - when no possibility of duplicate objects \<close>

definition indep_events_set :: "'a set set \<Rightarrow> bool" where
"indep_events_set E \<equiv> (E \<subseteq> events \<and> (\<forall>J. J \<subseteq> E \<longrightarrow> finite J \<longrightarrow> J \<noteq> {} \<longrightarrow> prob (\<Inter>J) = (\<Prod>i\<in>J. prob i)))"

lemma indep_events_setI[intro]: "E \<subseteq> events \<Longrightarrow> (\<And>J. J \<subseteq> E \<Longrightarrow> finite J \<Longrightarrow> J \<noteq> {} \<Longrightarrow> 
    prob (\<Inter>J) = (\<Prod>i\<in>J. prob i)) \<Longrightarrow> indep_events_set E"
  using indep_events_set_def by simp

lemma indep_events_subset:
  "indep_events_set E \<longleftrightarrow> (\<forall>J\<subseteq>E. indep_events_set J)"
  by (auto simp: indep_events_set_def)

lemma indep_events_subset2:
  "indep_events_set E \<Longrightarrow> J \<subseteq> E \<Longrightarrow> indep_events_set J"
  by (auto simp: indep_events_set_def)

lemma indep_events_set_events: "indep_events_set E \<Longrightarrow> (\<And>e. e \<in> E \<Longrightarrow> e \<in> events)" 
  using indep_events_set_def by auto

lemma indep_events_set_events_ss: "indep_events_set E \<Longrightarrow>  E \<subseteq> events" 
  using indep_events_set_events by auto

lemma indep_events_set_probs: "indep_events_set E \<Longrightarrow> J \<subseteq> E \<Longrightarrow> finite J \<Longrightarrow> J \<noteq> {} \<Longrightarrow> 
    prob (\<Inter>J) = (\<Prod>i\<in>J. prob i)"
  by (simp add: indep_events_set_def)

lemma indep_events_set_prod_all: "indep_events_set E \<Longrightarrow> finite E \<Longrightarrow> E \<noteq> {} \<Longrightarrow>
     prob (\<Inter>E) = prod prob E" 
  using indep_events_set_probs by simp

lemma indep_events_not_contain_compl: 
  assumes "indep_events_set E"
  assumes "A \<in> E"
  assumes "prob A > 0" "prob A < 1"
  shows "(space M - A) \<notin> E" (is "?A' \<notin> E")
proof (rule ccontr)
  assume "\<not> (?A') \<notin> E" 
  then have "?A' \<in> E" by auto
  then have "{A, ?A'} \<subseteq> E" using assms(2) by auto
  moreover have "finite {A, ?A'}" by simp
  moreover have "{A, ?A'} \<noteq> {}"
    by simp
  ultimately have "prob (\<Inter>i\<in>{A, ?A'}. i) = (\<Prod>i\<in>{A, ?A'}. prob i)" 
    using indep_events_set_probs[of E "{A, ?A'}"] assms(1) by auto
  then have "prob (A \<inter> ?A') = prob A * prob ?A'" by simp
  moreover have "prob (A \<inter> ?A') = 0" by simp
  moreover have "prob A * prob ?A' = prob A * (1 - prob A)"
    using assms(1) assms(2) indep_events_set_events prob_compl by auto 
  moreover have "prob A * (1 - prob A) > 0" using assms(3) assms(4) by (simp add: algebra_simps)
  ultimately show False by auto
qed

lemma indep_events_contain_compl_prob01: 
  assumes "indep_events_set E"
  assumes "A \<in> E"
  assumes "space M - A \<in> E"
  shows "prob A = 0 \<or> prob A = 1"
proof (rule ccontr)
  let ?A' = "space M - A"
  assume a: "\<not> (prob A = 0 \<or> prob A = 1)"
  then have "prob A > 0"
    by (simp add: zero_less_measure_iff)
  moreover have "prob A < 1"
    using a measure_ge_1_iff by fastforce
  ultimately have "?A' \<notin> E" using assms(1) assms(2) indep_events_not_contain_compl by auto
  then show False using assms(3) by auto
qed

lemma indep_events_set_singleton: 
  assumes "A \<in> events"
  shows "indep_events_set {A}"
proof (intro indep_events_setI)
  show "{A} \<subseteq> events" using assms by simp
next
  fix J assume "J \<subseteq> {A}" "finite J" "J \<noteq> {}"
  then have "J = {A}" by auto
  then show "prob (\<Inter>J) = prod prob J" by simp
qed
 

lemma indep_events_pairs: 
  assumes "indep_events_set S"
  assumes "A \<in> S" "B \<in> S" "A \<noteq> B"
  shows "indep_event A B"
  using assms indep_events_set_probs[of "S" "{A, B}"] 
  by (intro indep_eventI) (simp_all add: indep_events_set_events)

lemma indep_events_inter_pairs: 
  assumes "indep_events_set S"
  assumes "finite A" "finite B"
  assumes "A \<noteq> {}" "B \<noteq> {}"
  assumes "A \<subseteq> S" "B \<subseteq> S" "A \<inter> B = {}"
  shows "indep_event (\<Inter>A) (\<Inter>B)"
proof (intro indep_eventI)
  have "A \<subseteq> events" "B \<subseteq> events" using indep_events_set_events assms by auto
  then show "\<Inter> A \<in> events" "\<Inter> B \<in> events" using Inter_event_ss assms by auto
next
  have "A \<union> B \<subseteq> S" using assms by auto
  then have "prob (\<Inter>(A \<union> B)) = prod prob (A \<union> B)" using assms
    by (metis Un_empty indep_events_subset infinite_Un prob_space.indep_events_set_prod_all prob_space_axioms) 
  also have "... = prod prob A * prod prob B" using assms(8)
    by (simp add: assms(2) assms(3) prod.union_disjoint) 
  finally have "prob (\<Inter>(A \<union> B)) = prob (\<Inter> A) * prob (\<Inter> B)" 
    using assms indep_events_subset indep_events_set_prod_all by metis 
  moreover have "\<Inter> (A \<union> B) = (\<Inter> A \<inter> \<Inter> B)" by auto
  ultimately show "prob (\<Inter> A \<inter> \<Inter> B) = prob (\<Inter> A) * prob (\<Inter> B)"
    by simp
qed

lemma indep_events_inter_single: 
  assumes "indep_events_set S"
  assumes "finite B"
  assumes "B \<noteq> {}"
  assumes "A \<in> S" "B \<subseteq> S" "A \<notin> B"
  shows "indep_event A (\<Inter>B)"
proof -
  have "{A} \<noteq> {}" "finite {A}" "{A} \<subseteq> S" using assms by simp_all
  moreover have "{A} \<inter> B = {}" using assms(6) by auto
  ultimately show ?thesis using indep_events_inter_pairs[of S "{A}" B] assms by auto
qed

lemma indep_events_set_prob1: 
  assumes "A \<in> events"
  assumes "prob A = 1"
  assumes "A \<notin> S"
  assumes "indep_events_set S"
  shows "indep_events_set (S \<union> {A})"
proof (intro indep_events_setI)
  show " S \<union> {A} \<subseteq> events" using assms(1) assms(4) indep_events_set_events by auto
next
  fix J assume jss: "J \<subseteq> S \<union> {A}" and finJ: "finite J" and jne: "J \<noteq> {}"
  show "prob (\<Inter>J) = prod prob J"
  proof (cases "A \<in> J")
    case t1: True
    then show ?thesis 
    proof (cases "J = {A}")
      case True
      then show ?thesis using indep_events_set_singleton assms(1) by auto
    next
      case False
      then have jun: "(J - {A}) \<union> {A} = J" using t1 by auto
      have "J - {A} \<subseteq> S" using jss by auto
      then have iej: "indep_events_set (J - {A})" using indep_events_subset2[of S "J - {A}"] assms(4) 
        by auto
      have jsse: "J - {A} \<subseteq> events" using indep_events_set_events jss
        using assms(4) by blast 
      have jne2: "J - {A} \<noteq> {}" using False jss jne by auto
      have split: "(J - {A}) \<inter> {A} = {}" by auto
      then have "prob (\<Inter>i\<in>J. i) = prob ((\<Inter>i\<in>(J - {A}). i) \<inter> A)" using jun
        by (metis Int_commute Inter_insert Un_ac(3) image_ident insert_is_Un) 
      also have "... = prob ((\<Inter>i\<in>(J - {A}). i))" 
        using prob1_basic_Inter[of A "J - {A}"] jsse assms(2) jne2 assms(1) finJ 
        by (simp add: Int_commute)
      also have "... = prob (\<Inter>(J - {A})) * prob A" using assms(2) by simp
      also have "... = (prod prob (J - {A})) * prob A"
        using iej indep_events_set_prod_all[of "J - {A}"] jne2 finJ finite_subset by auto
      also have "... = prod prob ((J - {A}) \<union> {A})" using split
        by (metis finJ jun mult.commute prod.remove t1) 
      finally show ?thesis using jun by auto 
    qed 
  next
    case False
    then have jss2: "J \<subseteq> S" using jss by auto
    then have "indep_events_set J" using assms(4) indep_events_subset2[of S J] by auto
    then show ?thesis using indep_events_set_probs finJ jne jss2 by auto
  qed
qed

lemma indep_events_set_prob0: 
  assumes "A \<in> events"
  assumes "prob A = 0"
  assumes "A \<notin> S"
  assumes "indep_events_set S"
  shows "indep_events_set (S \<union> {A})"
proof (intro indep_events_setI)
  show "S \<union> {A}\<subseteq> events" using assms(1) assms(4) indep_events_set_events by auto
next
  fix J assume jss: "J \<subseteq> S \<union> {A}" and finJ: "finite J" and jne: "J \<noteq> {}"
  show "prob (\<Inter>J) = prod prob J"
  proof (cases "A \<in> J")
    case t1: True
    then show ?thesis 
    proof (cases "J = {A}")
      case True
      then show ?thesis using indep_events_set_singleton assms(1) by auto
    next
      case False
      then have jun: "(J - {A}) \<union> {A} = J" using t1 by auto
      have "J - {A} \<subseteq> S" using jss by auto
      then have iej: "indep_events_set (J - {A})" using indep_events_subset2[of S "J - {A}"] assms(4) by auto
      have jsse: "J - {A} \<subseteq> events" using indep_events_set_events jss
        using assms(4) by blast 
      have jne2: "J - {A} \<noteq> {}" using False jss jne by auto
      have split: "(J - {A}) \<inter> {A} = {}" by auto
      then have "prob (\<Inter>i\<in>J. i) = prob ((\<Inter>i\<in>(J - {A}). i) \<inter> A)" using jun
        by (metis Int_commute Inter_insert Un_ac(3) image_ident insert_is_Un) 
      also have "... = 0" 
        using prob0_basic_Inter[of A "J - {A}"] jsse assms(2) jne2 assms(1) finJ 
        by (simp add: Int_commute)
      also have "... = prob (\<Inter>(J - {A})) * prob A" using assms(2) by simp
      also have "... = (prod prob (J - {A})) * prob A" using iej indep_events_set_prod_all[of "J - {A}"] jne2 finJ finite_subset by auto
      also have "... = prod prob ((J - {A}) \<union> {A})" using split
        by (metis finJ jun mult.commute prod.remove t1) 
      finally show ?thesis using jun by auto 
    qed 
  next
    case False
    then have jss2: "J \<subseteq> S" using jss by auto
    then have "indep_events_set J" using assms(4) indep_events_subset2[of S J] by auto
    then show ?thesis using indep_events_set_probs finJ jne jss2 by auto
  qed
qed


lemma indep_event_commute: 
  assumes "indep_event A B"
  shows "indep_event B A"
  using indep_eventI[of "B" "A"] indep_eventD[unfolded assms(1), of "A" "B"]
  by (metis Groups.mult_ac(2) Int_commute assms indep_eventD_ev1 indep_eventD_ev2)

text\<open>Showing complement operation maintains independence \<close>

lemma indep_event_one_compl:
  assumes "indep_event A B"
  shows "indep_event A (space M - B)"
proof -
  let ?B' = "space M - B"
  have "A = (A \<inter> B) \<union> (A \<inter> ?B')"
    by (metis Int_Diff Int_Diff_Un assms prob_space.indep_eventD_ev1 prob_space_axioms sets.Int_space_eq2)
  then have "prob A = prob (A \<inter> B) + prob (A \<inter> ?B')"
    by (metis Diff_Int_distrib Diff_disjoint assms finite_measure_Union indep_eventD_ev1 
        indep_eventD_ev2 sets.Int sets.compl_sets)
  then have "prob (A \<inter> ?B') = prob A - prob (A \<inter> B)" by simp   
  also have "... = prob A - prob A * prob B" using indep_eventD assms(1) by auto
  also have "... = prob A * (1 - prob B)"
    by (simp add: vector_space_over_itself.scale_right_diff_distrib)
  finally have "prob (A \<inter> ?B') = prob A * prob ?B'"
    using prob_compl indep_eventD_ev1 assms(1) indep_eventD_ev2 by presburger 
  then show "indep_event A ?B'" using indep_eventI indep_eventD_ev2 indep_eventD_ev1 assms(1)
    by (meson sets.compl_sets) 
qed

lemma indep_event_one_compl_rev:
  assumes "B \<in> events"
  assumes "indep_event A (space M - B)"
  shows "indep_event A B"
proof -
  have "space M - B \<in> events" using indep_eventD_ev2 assms by auto
  have "space M - (space M - B) = B" using compl_identity assms by simp
  then show ?thesis using indep_event_one_compl[of "A" "space M - B"] assms(2) by auto
qed

lemma indep_event_double_compl: "indep_event A B \<Longrightarrow> indep_event (space M - A) (space M - B)"
  using indep_event_one_compl indep_event_commute by auto

lemma indep_event_double_compl_rev: "A \<in> events \<Longrightarrow> B \<in> events \<Longrightarrow> 
    indep_event (space M - A) (space M - B) \<Longrightarrow> indep_event A B"
  using indep_event_double_compl[of "space M - A" "space M - B"] compl_identity by auto

lemma indep_events_set_one_compl: 
  assumes "indep_events_set S"
  assumes "A \<in> S"
  shows "indep_events_set ({space M - A} \<union> (S - {A}))"
proof (intro indep_events_setI)
  show "{space M - A} \<union> (S - {A}) \<subseteq> events"
    using indep_events_set_events assms(1) assms(2) by auto
next
  fix J assume jss: "J \<subseteq> {space M - A} \<union> (S - {A})"
  assume finJ: "finite J"
  assume jne: "J \<noteq> {}" 
  show "prob (\<Inter>J) = prod prob J"
  proof (cases "J - {space M - A} = {}")
    case True
    then have "J = {space M - A}" using jne by blast
    then show ?thesis by simp
  next
    case jne2: False
    have jss2: "J - {space M - A} \<subseteq> S" using jss assms(2) by auto
    moreover have "A \<notin> (J - {space M - A})" using jss by auto
    moreover have "finite (J - {space M - A})" using finJ by simp
    ultimately have "indep_event A (\<Inter> (J - {space M - A}))" 
      using indep_events_inter_single[of S "(J - {space M - A})" A] assms jne2 by auto
    then have ie: "indep_event (space M - A) (\<Inter> (J - {space M - A}))" 
      using indep_event_one_compl indep_event_commute by auto
    have iess: "indep_events_set (J - {space M - A})" 
      using jss2 indep_events_subset2[of S "J - {space M - A}"] assms(1) by auto
    show ?thesis 
    proof (cases "space M - A \<in> J")
      case True
      then have split: "J = (J - {space M - A}) \<union> {space M - A}" by auto
      then have "prob (\<Inter> J) = prob (\<Inter> ((J - {space M - A}) \<union> {space M - A}))" by simp
      also have "... = prob ((\<Inter> (J - {space M - A})) \<inter> (space M - A))"
        by (metis Inter_insert True \<open>J = J - {space M - A} \<union> {space M - A}\<close> inf.commute insert_Diff) 
      also have "... = prob (\<Inter> (J - {space M - A})) * prob (space M - A)" 
        using ie indep_eventD[of "\<Inter> (J - {space M - A})" "space M - A"] indep_event_commute by auto
      also have "... = (prod prob ((J - {space M - A}))) * prob (space M - A)"
        using indep_events_set_prod_all[of "J - {space M - A}"] iess jne2 finJ by auto
      finally have "prob (\<Inter> J) = prod prob J" using split
        by (metis Groups.mult_ac(2) True finJ prod.remove) 
      then show ?thesis by simp
    next
      case False
      then show ?thesis using iess
        by (simp add: assms(1) finJ indep_events_set_prod_all jne) 
    qed
  qed
qed

lemma indep_events_set_update_compl: 
  assumes "indep_events_set E"
  assumes "E = A \<union> B"
  assumes "A \<inter> B = {}"
  assumes "finite E"
  shows "indep_events_set (((-) (space M) ` A) \<union> B)"
using assms(2) assms(3)  proof (induct "card A" arbitrary: A B)
  case 0
  then show ?case using assms(1)
    using assms(4) by auto 
next
  case (Suc x)
  then obtain a A' where aeq: "A = insert a A'" and anotin: "a \<notin> A'"
    by (metis card_Suc_eq_finite)
  then have xcard: "card A' = x"
    using Suc(2) Suc(3) assms(4) by auto
  let ?B' = "B \<union> {a}" 
  have "E = A' \<union> ?B'" using aeq Suc.prems by auto
  moreover have "A' \<inter> ?B' = {}" using anotin Suc.prems(2) aeq by auto
  moreover have "?B' \<noteq> {}" by simp
  ultimately have ies: "indep_events_set ((-) (space M) ` A' \<union> ?B')" 
    using Suc.hyps(1)[of "A'" ?B'] xcard by auto
  then have "a \<in> A \<union> B" using aeq by auto
  then show ?case 
  proof (cases "(A \<union> B) - {a} = {}")
    case True
    then have "A = {a}" "B = {}" using Suc.prems aeq by auto
    then have "((-) (space M) ` A \<union> B) = {space M - a}" by auto
    moreover have "space M - a \<in> events" using aeq assms(1) Suc.prems indep_events_set_events by auto
    ultimately show ?thesis using indep_events_set_singleton by simp
  next
    case False
    have "a \<in> (-) (space M) ` A' \<union> ?B'" using aeq by auto
    then have ie: "indep_events_set ({space M - a} \<union> ((-) (space M) ` A' \<union> ?B' - {a}))" 
      using indep_events_set_one_compl[of "(-) (space M) ` A' \<union> ?B'" a] ies by auto
    show ?thesis 
    proof (cases "a \<in> (-) (space M) ` A'")
      case True
      then have "space M - a \<in> A'"
        by (smt (verit) \<open>E = A' \<union> (B \<union> {a})\<close> assms(1) compl_identity image_iff indep_events_set_events 
            indep_events_subset2 inf_sup_ord(3))
      then have "space M - a \<in> A" using aeq by auto
      moreover have "indep_events_set A" using Suc.prems(1) indep_events_subset2 assms(1)
        using aeq by blast 
      moreover have "a \<in> A" using aeq by auto
      ultimately have probs: "prob a = 0 \<or> prob a = 1" using indep_events_contain_compl_prob01[of A a] by auto
      have "((-) (space M) ` A \<union> B) = (-) (space M) ` A' \<union> {space M - a} \<union> B" using aeq by auto
      moreover have "((-) (space M) ` A' \<union> ?B' - {a}) = ((-) (space M) ` A' - {a}) \<union> B"
        using Suc.prems(2) aeq by auto
      moreover have "(-) (space M) ` A' = ((-) (space M) ` A' - {a}) \<union> {a}" using True by auto
      ultimately have "((-) (space M) ` A \<union> B) = {space M - a} \<union> ((-) (space M) ` A' \<union> ?B' - {a}) \<union> {a}"
        by (smt (verit) Un_empty_right Un_insert_right Un_left_commute) (* Longish*)
      moreover have "a \<notin> {space M - a} \<union> ((-) (space M) ` A' \<union> ?B' - {a})"
        using Diff_disjoint \<open>space M - a \<in> A'\<close> anotin empty_iff insert_iff by fastforce 
      moreover have "a \<in> events" using Suc.prems(1) assms(1) indep_events_set_events aeq by auto
      ultimately show ?thesis
        using ie indep_events_set_prob0 indep_events_set_prob1 probs by presburger
    next
      case False
      then have "(((-) (space M) `A' \<union> ?B') - {a}) = (-) (space M) `A' \<union> B" 
        using Suc.prems(2) aeq by auto
      moreover have "(-) (space M) ` A = (-) (space M) ` A' \<union> {space M - a}" using aeq
        by simp
      ultimately have "((-) (space M) ` A \<union> B) = {space M - a} \<union> ((-) (space M) ` A' \<union> ?B' - {a})"
        by auto
      then show ?thesis using ie by simp
    qed
  qed
qed

lemma indep_events_set_compl: 
  assumes "indep_events_set E"
  assumes "finite E"
  shows "indep_events_set ((\<lambda> e. space M - e) ` E)"
  using indep_events_set_update_compl[of E E "{}"] assms by auto

lemma indep_event_empty:
  assumes "A \<in> events"
  shows "indep_event A {}"
  using assms indep_eventI by auto


lemma indep_event_compl_inter:
  assumes "indep_event A C"
  assumes "B \<in> events"
  assumes "indep_event A (B \<inter> C)"
  shows "indep_event A ((space M - B) \<inter> C)"
proof (intro indep_eventI)
  show "A \<in> events" using assms(1) indep_eventD_ev1 by auto
  show "(space M - B) \<inter> C \<in> events" using assms(3) indep_eventD_ev2
    by (metis Diff_Int_distrib2 assms(1) sets.Diff sets.Int_space_eq1)
next
  have ac: "A \<inter> C \<in> events" using assms(1) indep_eventD_ev1 indep_eventD_ev2 sets.Int_space_eq1 
    by auto
  have "prob (A \<inter> ((space M - B) \<inter> C)) = prob (A \<inter> (space M - B) \<inter> C)"
    by (simp add: inf_sup_aci(2))
  also have "... = prob (A \<inter> C \<inter> (space M - B))"
    by (simp add: ac_simps)
  also have "... = prob (A \<inter> C) - prob (A \<inter> C \<inter> B)"
    using prob_compl_diff_inter[of "A \<inter> C" "B"] ac assms(2) by auto
  also have "... = prob (A) * prob C - (prob A * prob (C \<inter> B))"
    using assms(1) assms(3) indep_eventD
    by (simp add: inf_commute inf_left_commute) 
  also have "... = prob A * (prob C - prob (C \<inter> B))" by (simp add: algebra_simps)
  finally have "prob (A \<inter> ((space M - B) \<inter> C)) = prob A * (prob (C \<inter> (space M - B)))" 
    using prob_compl_diff_inter[of "C" "B"] using assms(1) assms(2)
    by (simp add: indep_eventD_ev2) 
  then show "prob (A \<inter> ((space M - B) \<inter> C)) = prob A * prob ((space M - B) \<inter> C)" by (simp add: ac_simps)
qed

(* Indep events indexed lemmas *)

lemma indep_events_index_subset:
  "indep_events F E \<longleftrightarrow> (\<forall>J\<subseteq>E. indep_events F J)"
  unfolding indep_events_def
  by (meson image_mono set_eq_subset subset_trans) 

lemma indep_events_index_subset2:
  "indep_events F E \<Longrightarrow> J \<subseteq> E \<Longrightarrow> indep_events F J"
  using indep_events_index_subset by auto

lemma indep_events_events_ss: "indep_events F E \<Longrightarrow>  F ` E \<subseteq> events" 
  unfolding indep_events_def by (auto) 

lemma indep_events_events: "indep_events F E \<Longrightarrow> (\<And>e. e \<in> E \<Longrightarrow> F e \<in> events)" 
  using indep_events_events_ss by auto

lemma indep_events_probs: "indep_events F E \<Longrightarrow> J \<subseteq> E \<Longrightarrow> finite J \<Longrightarrow> J \<noteq> {} \<Longrightarrow> prob (\<Inter>(F ` J)) = (\<Prod>i\<in>J. prob (F i))" 
  unfolding indep_events_def by auto

lemma indep_events_prod_all: "indep_events F E \<Longrightarrow> finite E \<Longrightarrow> E \<noteq> {} \<Longrightarrow> prob (\<Inter>(F ` E)) = (\<Prod>i\<in>E. prob (F i))" 
  using indep_events_probs by auto

lemma indep_events_ev_not_contain_compl: 
  assumes "indep_events F E"
  assumes "A \<in> E"
  assumes "prob (F A) > 0" "prob (F A) < 1"
  shows "(space M - F A) \<notin> F ` E" (is "?A' \<notin> F ` E")
proof (rule ccontr)
  assume "\<not> ?A' \<notin> F ` E" 
  then have "?A' \<in> F ` E" by auto
  then obtain Ae where aeq: "?A' = F Ae" and "Ae \<in> E" by blast
  then have "{A, Ae} \<subseteq> E" using assms(2) by auto
  moreover have "finite {A, Ae}" by simp
  moreover have "{A, Ae} \<noteq> {}"
    by simp
  ultimately have "prob (\<Inter>i\<in>{A, Ae}. F i) = (\<Prod>i\<in>{A, Ae}. prob (F i))" using indep_events_probs[of F E "{A, Ae}"] assms(1) by auto
  moreover have "A \<noteq> Ae"
    using subprob_not_empty using aeq by auto
  ultimately have "prob (F A \<inter> ?A') = prob (F A) * prob (?A')" using aeq by simp
  moreover have "prob (F A \<inter> ?A') = 0" by simp 
  moreover have "prob (F A) * prob ?A' = prob (F A) * (1 - prob (F A))"
    using assms(1) assms(2) indep_events_events prob_compl by metis 
  moreover have "prob (F A) * (1 - prob (F A)) > 0" using assms(3) assms(4) by (simp add: algebra_simps)
  ultimately show False by auto
qed

lemma indep_events_singleton: 
  assumes "F A \<in> events"
  shows "indep_events F {A}"
proof (intro indep_eventsI)
  show "\<And>i. i \<in> {A} \<Longrightarrow> F i \<in> events" using assms by simp
next
  fix J assume "J \<subseteq> {A}" "finite J" "J \<noteq> {}"
  then have "J = {A}" by auto
  then show "prob (\<Inter> (F ` J)) = (\<Prod>i\<in>J. prob (F i))" by simp
qed
 

lemma indep_events_ev_pairs: 
  assumes "indep_events F S"
  assumes "A \<in> S" "B \<in> S" "A \<noteq> B"
  shows "indep_event (F A) (F B)"
  using assms indep_events_probs[of F "S" "{A, B}"] 
  by (intro indep_eventI) (simp_all add: indep_events_events)

lemma indep_events_ev_inter_pairs: 
  assumes "indep_events F S"
  assumes "finite A" "finite B"
  assumes "A \<noteq> {}" "B \<noteq> {}"
  assumes "A \<subseteq> S" "B \<subseteq> S" "A \<inter> B = {}"
  shows "indep_event (\<Inter>(F ` A)) (\<Inter>(F ` B))"
proof (intro indep_eventI)
  have "(F ` A) \<subseteq> events" "(F `  B) \<subseteq> events" using indep_events_events assms(1) assms(6) assms(7) by fast+
  then show "\<Inter> (F ` A) \<in> events" "\<Inter> (F `B) \<in> events" using Inter_event_ss assms by auto
next
  have "A \<union> B \<subseteq> S" using assms by auto
  moreover have "finite (A \<union> B)" using assms(2) assms(3) by simp
  moreover have "A \<union> B \<noteq> {}" using assms by simp
  ultimately have "prob (\<Inter>(F `(A \<union> B))) = (\<Prod>i\<in>A \<union> B. prob (F i))" using assms
    using  indep_events_probs[of F S "A \<union> B"] by simp
  also have "... = (\<Prod>i\<in>A. prob (F i)) * (\<Prod>i\<in>B. prob (F i))" 
    using assms(8) prod.union_disjoint[of A B "\<lambda> i. prob (F i)"] assms(2) assms(3) by simp
  finally have "prob (\<Inter>(F `(A \<union> B))) = prob (\<Inter> (F ` A)) * prob (\<Inter> (F ` B))" 
    using assms indep_events_index_subset indep_events_prod_all by metis 
  moreover have "\<Inter> (F ` (A \<union> B)) = (\<Inter> (F ` A)) \<inter> \<Inter> (F ` B)" by auto
  ultimately show "prob (\<Inter> (F ` A) \<inter> \<Inter> (F ` B)) = prob (\<Inter> (F ` A)) * prob (\<Inter> (F ` B))"
    by simp
qed


lemma indep_events_ev_inter_single: 
  assumes "indep_events F S"
  assumes "finite B"
  assumes "B \<noteq> {}"
  assumes "A \<in> S" "B \<subseteq> S" "A \<notin> B"
  shows "indep_event (F A) (\<Inter>(F ` B))"
proof -
  have "{A} \<noteq> {}" "finite {A}" "{A} \<subseteq> S" using assms by simp_all
  moreover have "{A} \<inter> B = {}" using assms(6) by auto
  ultimately show ?thesis using indep_events_ev_inter_pairs[of F S "{A}" B] assms by auto
qed

lemma indep_events_fn_eq: 
  assumes "\<And> Ai. Ai \<in> E \<Longrightarrow> F Ai = G Ai"
  assumes "indep_events F E"
  shows "indep_events G E"
proof (intro indep_eventsI)
  show "\<And>i. i \<in> E \<Longrightarrow> G i \<in> events" using assms(2) indep_events_events assms(1)
    by metis 
next
  fix J assume jss: "J \<subseteq> E" "finite J" "J \<noteq> {}"
  moreover have "G ` J = F ` J" using assms(1) calculation(1) by auto
  moreover have "\<And> i . i \<in> J \<Longrightarrow> prob (G i) = prob (F i)"  using jss assms(1) by auto
  moreover have "(\<Prod>i\<in>J. prob (F i)) = (\<Prod>i\<in>J. prob (G i))" using calculation(5) by auto
  ultimately show "prob (\<Inter> (G ` J)) = (\<Prod>i\<in>J. prob (G i))"
    using assms(2) indep_events_probs[of F E J] by simp
qed

lemma indep_events_fn_eq_iff: 
  assumes "\<And> Ai. Ai \<in> E \<Longrightarrow> F Ai = G Ai"
  shows "indep_events F E \<longleftrightarrow> indep_events G E"
  using indep_events_fn_eq assms by auto

lemma indep_events_one_compl: 
  assumes "indep_events F S"
  assumes "A \<in> S"
  shows "indep_events (\<lambda> i. if (i = A) then (space M - F i) else F i) S" (is "indep_events ?G S")
proof (intro indep_eventsI)
  show "\<And>i. i \<in> S \<Longrightarrow> (if i = A then space M - F i else F i) \<in> events"
    using indep_events_events assms(1) assms(2)
    by (metis sets.compl_sets) 
next
  define G where "G \<equiv>?G"
  fix J assume jss: "J \<subseteq> S"
  assume finJ: "finite J"
  assume jne: "J \<noteq> {}" 
  show "prob (\<Inter>i\<in>J. ?G i) = (\<Prod>i\<in>J. prob (?G i))"
  proof (cases "J = {A}")
    case True
    then show ?thesis by simp
  next
    case jne2: False
    have jss2: "J - {A} \<subseteq> S" using jss assms(2) by auto
    moreover have "A \<notin> (J - {A})" using jss by auto
    moreover have "finite (J - {A})" using finJ by simp
    moreover have "J - {A} \<noteq> {}" using jne2 jne by auto
    ultimately have "indep_event (F A) (\<Inter> (F ` (J -  {A})))" 
      using indep_events_ev_inter_single[of F S "(J - {A})" A] assms by auto
    then have ie: "indep_event (G A) (\<Inter> (G ` (J -  {A})))" 
      using indep_event_one_compl indep_event_commute G_def by auto
    have iess: "indep_events G (J - {A})" 
      using jss2 G_def indep_events_index_subset2[of F S "J - {A}"] assms(1) 
        indep_events_fn_eq[of "J - {A}"] by auto
    show ?thesis 
    proof (cases "A \<in> J")
      case True
      then have split: "G ` J = insert (G A) (G ` (J - {A}))" by auto
      then have "prob (\<Inter> (G ` J)) = prob (\<Inter> (insert (G A) (G ` (J - {A}))))" by auto
      also have "... = prob ((G A)\<inter> \<Inter> (G ` (J - {A})) )"
        using Inter_insert by simp
      also have "... =  prob (G A) * prob (\<Inter> (G ` (J - {A})))" 
        using ie indep_eventD[of "G A" "\<Inter> (G ` (J - {A}))" ] by auto
      also have "... = prob (G A) * (\<Prod>i \<in> (J - {A}). prob (G i)) "
        using indep_events_prod_all[of G "J - {A}"] iess jne2 jne finJ by auto
      finally have "prob (\<Inter> (G ` J)) = (\<Prod>i \<in> J. prob (G i))" using split
        by (metis True finJ prod.remove) 
      then show ?thesis using G_def by simp
    next
      case False
      then have "prob (\<Inter>i\<in>J. G i) = (\<Prod>i\<in>J. prob (G i))" using iess
        by (simp add: assms(1) finJ indep_events_prod_all jne) 
      then show ?thesis using G_def by simp
    qed
  qed
qed

lemma indep_events_update_compl: 
  assumes "indep_events F E"
  assumes "E = A \<union> B"
  assumes "A \<inter> B = {}"
  assumes "finite E"
  shows "indep_events (\<lambda> Ai. if (Ai \<in> A) then (space M - (F Ai)) else (F Ai)) E" 
using assms(2) assms(3)  proof (induct "card A" arbitrary: A B)
  case 0
  let ?G = "(\<lambda>Ai. if Ai \<in> A then space M - F Ai else F Ai)"
  have "E = B" using  assms(4) \<open>E = A \<union> B\<close> \<open>0 = card A\<close>
    by simp 
  then have "\<And> i. i \<in> E \<Longrightarrow> F i = ?G i" using \<open>A \<inter> B = {}\<close> by auto
  then show ?case using assms(1) indep_events_fn_eq[of E F ?G] by simp
next
  case (Suc x)
  define G where  "G \<equiv> (\<lambda>Ai. if Ai \<in> A then space M - F Ai else F Ai)"
  obtain a A' where aeq: "A = insert a A'" and anotin: "a \<notin> A'"
    using Suc.hyps by (metis card_Suc_eq_finite)
  then have xcard: "card A' = x"
    using Suc(2) Suc(3) assms(4) by auto
  define G1 where "G1 \<equiv> (\<lambda>Ai. if Ai \<in> A' then space M - F Ai else F Ai)"
  let ?B' = "B \<union> {a}" 
  have eeq: "E = A' \<union> ?B'" using aeq Suc.prems by auto
  moreover have "A' \<inter> ?B' = {}" using anotin Suc.prems(2) aeq by auto
  moreover have "?B' \<noteq> {}" by simp
  ultimately have ies: "indep_events G1 (A' \<union> ?B')" 
    using Suc.hyps(1)[of "A'" ?B'] xcard G1_def by auto
  then have "a \<in> A \<union> B" using aeq by auto
  define G2  where "G2 \<equiv> \<lambda> Ai. if Ai = a then (space M - (G1 Ai)) else (G1 Ai)" 
  have "a \<in> A' \<union> ?B'" by auto
  then have ie: "indep_events G2 E" 
    using indep_events_one_compl[of G1 "(A' \<union> ?B')" a] ies G2_def eeq by auto
  moreover have "\<And> i. i \<in> E \<Longrightarrow> G2 i = G i"
    unfolding G2_def G1_def G_def
    by (simp add: aeq anotin) 
  ultimately have "indep_events G E" using indep_events_fn_eq[of E G2 G] by auto
  then show ?case  using G_def by simp
qed

lemma indep_events_compl: 
  assumes "indep_events F E"
  assumes "finite E"
  shows "indep_events (\<lambda> Ai. space M - F Ai) E"
proof -
  have "indep_events (\<lambda>Ai. if Ai \<in> E then space M - F Ai else F Ai) E"
    using indep_events_update_compl[of F E E "{}"] assms by auto
  moreover have "\<And> i. i \<in> E \<Longrightarrow> (\<lambda>Ai. if Ai \<in> E then space M - F Ai else F Ai) i = (\<lambda> Ai. space M - F Ai) i"
    by simp
  ultimately show ?thesis 
    using indep_events_fn_eq[of E "(\<lambda>Ai. if Ai \<in> E then space M - F Ai else F Ai)"] by auto
qed

lemma indep_events_impl_inj_on: 
  assumes "finite A"
  assumes "indep_events F A"
  assumes "\<And> A' . A' \<in> A \<Longrightarrow> prob (F A') > 0 \<and> prob (F A') < 1"
  shows "inj_on F A"
proof (intro inj_onI, rule ccontr)
  fix x y assume xin: "x \<in> A" and yin: "y \<in> A" and feq: "F x = F y"
  assume contr: "x \<noteq> y"
  then have "{x, y} \<subseteq> A" "{x, y} \<noteq> {}" "finite {x, y}" using xin yin by auto
  then have "prob (\<Inter>j\<in>{x, y}. F j) = (\<Prod>j\<in>{x, y}. prob (F j))" 
    using assms(2) indep_events_probs[of F A "{x, y}"] by auto
  moreover have "(\<Prod>j\<in>{x, y}. prob (F j)) = prob (F x) * prob (F y)" using contr by auto
  moreover have "prob (\<Inter>j\<in>{x, y}. F j) = prob (F x)" using feq by simp
  ultimately have "prob (F x) = prob (F x) * prob (F x)" using feq by simp
  then show False using assms(3) using xin by fastforce 
qed

lemma indep_events_imp_set:
  assumes "finite A"
  assumes "indep_events F A"
  assumes "\<And> A' . A' \<in> A \<Longrightarrow> prob (F A') > 0 \<and> prob (F A') < 1"
  shows "indep_events_set (F ` A)"
proof (intro indep_events_setI)
  show "F ` A \<subseteq> events" using assms(2) indep_events_events by auto
next 
  fix J assume jss: "J \<subseteq> F ` A" and finj: "finite J" and jne:"J \<noteq> {}"
  have bb: "bij_betw F A (F `A)" using bij_betw_imageI indep_events_impl_inj_on assms by meson
  then obtain I where iss: "I \<subseteq> A" and jeq: "J = F ` I" 
    using bij_betw_obtain_subsetl[OF bb] jss by metis
  moreover have "I \<noteq> {}" "finite I" using finj jeq jne assms(1) finite_subset iss by blast+
  ultimately have "prob (\<Inter> (F ` I)) = (\<Prod>i\<in>I. prob (F i))" 
    using jne finj jss indep_events_probs[of F A I] assms(2) by (simp)
  moreover have "bij_betw F I J" using jeq iss jss bb by (meson bij_betw_subset)
  ultimately show "prob (\<Inter> J) = prod prob J" using bij_betw_prod_prob jeq by (metis) 
qed

lemma indep_event_set_equiv_bij:
  assumes "bij_betw F A E"
  assumes "finite E"
  shows "indep_events_set E \<longleftrightarrow> indep_events F A"
proof -
  have im: "F ` A = E"
    using assms(1) by (simp add:  bij_betw_def) 
  then have ss: "(\<forall>e. e \<in> E \<longrightarrow> e \<in> events) \<longleftrightarrow> (F ` A \<subseteq> events)"
    using image_iff by (simp add: subset_iff) 
  have prob: "(\<forall> J. J \<subseteq> E \<longrightarrow> finite J \<longrightarrow> J \<noteq> {} \<longrightarrow> prob (\<Inter>i\<in>J. i) = (\<Prod>i\<in>J. prob i)) \<longleftrightarrow>
        (\<forall> I. I \<subseteq> A \<longrightarrow> finite I \<longrightarrow> I \<noteq> {} \<longrightarrow> prob (\<Inter>i\<in>I. F i) = (\<Prod>i\<in>I. prob (F i)))"
  proof (intro allI impI iffI)
    fix I assume p1: " \<forall>J\<subseteq>E. finite J \<longrightarrow> J \<noteq> {} \<longrightarrow> prob (\<Inter>i\<in>J. i) = prod prob J"
      and iss: "I \<subseteq> A" and f1: "finite I" and i1: "I \<noteq> {}" 
    then obtain J where jeq: "J = F ` I" and jss: "J \<subseteq> E"
      using bij_betw_obtain_subsetr[OF assms(1) iss]by metis 
    then have "prob (\<Inter>J) = prod prob J" using i1 f1 p1 jss by auto
    moreover have "bij_betw F I J" using jeq jss assms(1) iss
      by (meson bij_betw_subset) 
    ultimately show "prob (\<Inter> (F ` I)) = (\<Prod>i\<in>I. prob (F i))" using bij_betw_prod_prob
      by (metis jeq)  
  next
    fix J assume p2: "\<forall>I\<subseteq>A. finite I \<longrightarrow> I \<noteq> {} \<longrightarrow> prob (\<Inter> (F ` I)) = (\<Prod>i\<in>I. prob (F i))"
      and jss:  "J \<subseteq> E" and f2: "finite J" and j1: "J \<noteq> {}"
    then obtain I where iss: "I \<subseteq> A" and jeq: "J = F ` I" 
      using bij_betw_obtain_subsetl[OF assms(1)] by metis
    moreover have "finite A" using assms(1) assms(2)
      by (simp add: bij_betw_finite) 
    ultimately have "prob (\<Inter> (F ` I)) = (\<Prod>i\<in>I. prob (F i))" using j1 f2 p2 jss
      by (simp add: finite_subset)
    moreover have "bij_betw F I J" using jeq iss assms(1) jss by (meson bij_betw_subset)
    ultimately show "prob (\<Inter>i\<in>J. i) = prod prob J" using bij_betw_prod_prob jeq
      by (metis image_ident) 
  qed
  have "indep_events_set E \<Longrightarrow> indep_events F A"
  proof (intro indep_eventsI)
    show "\<And>i. indep_events_set E \<Longrightarrow> i \<in> A \<Longrightarrow> F i \<in> events" 
      using indep_events_set_events ss by auto
    show "\<And>J. indep_events_set E \<Longrightarrow> J \<subseteq> A \<Longrightarrow> finite J \<Longrightarrow> J \<noteq> {} \<Longrightarrow> prob (\<Inter> (F ` J)) = (\<Prod>i\<in>J. prob (F i))"
      using indep_events_set_probs prob by auto
  qed
  moreover have "indep_events F A \<Longrightarrow> indep_events_set E"
  proof (intro indep_events_setI) 
    have "\<And>e. indep_events F A \<Longrightarrow> e \<in> E \<Longrightarrow> e \<in> events" using ss indep_events_def by metis
    then show "indep_events F A \<Longrightarrow> E \<subseteq> events" by auto
    show "\<And>J. indep_events F A \<Longrightarrow> J \<subseteq> E \<Longrightarrow> finite J \<Longrightarrow> J \<noteq> {} \<Longrightarrow> prob (\<Inter>J) = prod prob J"
      using prob indep_events_def by (metis image_ident) 
  qed
  ultimately show ?thesis by auto
qed

subsection \<open> Mutual Independent Events \<close>

text \<open>Note, set based version only if no duplicates in usage case. The mutual\_indep\_events definition 
is more general and recommended \<close>
definition mutual_indep_set:: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool"
  where "mutual_indep_set A S \<longleftrightarrow> A \<in> events \<and> S \<subseteq> events \<and> (\<forall> T \<subseteq> S . T \<noteq> {} \<longrightarrow> prob (A \<inter> (\<Inter>T)) = prob A * prob (\<Inter>T))"  
(* Note condition about T not empty, only necessary due to Univ issue*)
(* Use every subset, rather than the not version given by Zhao *)

lemma mutual_indep_setI[intro]: "A \<in> events \<Longrightarrow> S \<subseteq> events \<Longrightarrow> (\<And> T. T \<subseteq> S \<Longrightarrow> T \<noteq> {} \<Longrightarrow> 
    prob (A \<inter> (\<Inter>T)) = prob A * prob (\<Inter>T)) \<Longrightarrow> mutual_indep_set A S" 
  using mutual_indep_set_def by simp

lemma mutual_indep_setD[dest]: "mutual_indep_set A S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> T \<noteq> {} \<Longrightarrow> prob (A \<inter> (\<Inter>T)) = prob A * prob (\<Inter>T)"
  using mutual_indep_set_def by simp

lemma mutual_indep_setD2[dest]: "mutual_indep_set A S \<Longrightarrow> A \<in> events"
  using mutual_indep_set_def by simp

lemma mutual_indep_setD3[dest]: "mutual_indep_set A S \<Longrightarrow> S \<subseteq> events"
  using mutual_indep_set_def by simp

lemma mutual_indep_subset: "mutual_indep_set A S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> mutual_indep_set A T"
  using mutual_indep_set_def by auto

lemma mutual_indep_event_set_defD: 
  assumes "mutual_indep_set A S"
  assumes "finite T"
  assumes "T \<subseteq> S"
  assumes "T \<noteq> {}"
  shows "indep_event A (\<Inter>T)"
proof (intro indep_eventI)
  show "A \<in> events" using mutual_indep_setD2 assms(1) by auto
  show "\<Inter> T \<in> events" using Inter_event_ss assms mutual_indep_setD3 finite_subset by blast
  show "prob (A \<inter> \<Inter> T) = prob A * prob (\<Inter> T) " 
    using assms(1) mutual_indep_setD assms(3) assms(4) by simp
qed

lemma mutual_indep_event_defI: "A \<in> events \<Longrightarrow> S \<subseteq> events \<Longrightarrow> (\<And> T. T \<subseteq> S \<Longrightarrow> T \<noteq> {} \<Longrightarrow> 
    indep_event A (\<Inter>T)) \<Longrightarrow> mutual_indep_set A S"
  using indep_eventD mutual_indep_set_def by simp

lemma mutual_indep_singleton_event: "mutual_indep_set A S \<Longrightarrow> B \<in> S \<Longrightarrow> indep_event A B" 
  using mutual_indep_event_set_defD empty_subsetI
  by (metis Set.insert_mono cInf_singleton finite.emptyI finite_insert insert_absorb insert_not_empty) 

lemma mutual_indep_cond: 
  assumes "A \<in> events" and "T \<subseteq> events" and "finite T"
  and "mutual_indep_set A S" and "T \<subseteq> S" and "T \<noteq> {}" and "prob (\<Inter>T) \<noteq> 0"
shows "\<P>(A |(\<Inter>T)) = prob A"
proof -
  have "\<Inter>T \<in> events" using assms
    by (simp add: Inter_event_ss) 
  then have "\<P>(A | (\<Inter>T)) = prob ((\<Inter>T) \<inter> A)/prob(\<Inter>T)"  using cond_prob_ev_def assms(1)
    by blast
  also have "... = prob (A \<inter> (\<Inter>T))/prob(\<Inter>T)"
    by (simp add: inf_commute) 
  also have "... = prob A * prob (\<Inter>T)/prob(\<Inter>T)" using assms mutual_indep_setD by auto
  finally show ?thesis using assms(7) by simp
qed

lemma mutual_indep_cond_full: 
  assumes "A \<in> events" and "S \<subseteq> events" and "finite S"
  and "mutual_indep_set A S" and  "S \<noteq> {}" and "prob (\<Inter>S) \<noteq> 0"
shows "\<P>(A |(\<Inter>S)) = prob A"
  using mutual_indep_cond[of A S S] assms by auto

lemma mutual_indep_cond_single: 
  assumes "A \<in> events" and "B \<in> events"
  and "mutual_indep_set A S" and "B \<in> S" and "prob B \<noteq> 0"
  shows "\<P>(A |B) = prob A"
  using mutual_indep_cond[of "A" "{B}" S] assms by auto

lemma mutual_indep_set_empty: "A \<in> events \<Longrightarrow> mutual_indep_set A {}"
  using mutual_indep_setI by auto

lemma not_mutual_indep_set_itself: 
  assumes "prob A > 0" and "prob A < 1"
  shows "\<not> mutual_indep_set A {A}"
proof (rule ccontr)
  assume "\<not> \<not> mutual_indep_set A {A}"
  then have "mutual_indep_set A {A}"
    by simp
  then have "\<And> T . T \<subseteq> {A} \<Longrightarrow> T \<noteq> {} \<Longrightarrow> prob (A \<inter> (\<Inter> T)) = prob A * prob (\<Inter>T)"
    using mutual_indep_setD by simp
  then have eq: "prob (A \<inter> (\<Inter> {A})) = prob A * prob (\<Inter>{A})"
    by blast 
  have "prob (A \<inter> (\<Inter>{A})) = prob A" by simp
  moreover have "prob A * (prob (\<Inter> {A})) = (prob A)^2"
    by (simp add: power2_eq_square) 
  ultimately show False using eq assms by auto
qed

lemma is_mutual_indep_set_itself:
  assumes "A \<in> events"
  assumes "prob A = 0 \<or> prob A = 1"
  shows "mutual_indep_set A {A}"
proof (intro mutual_indep_setI)
  show "A \<in> events" "{A} \<subseteq> events" using assms(1) by auto
  fix T assume "T \<subseteq> {A}" and "T \<noteq> {}"
  then have teq: "T = {A}" by auto
  have "prob (A \<inter> (\<Inter>{A})) = prob A" by simp
  moreover have "prob A * (prob (\<Inter> {A})) = (prob A)^2"
    by (simp add: power2_eq_square) 
  ultimately show  "prob (A \<inter> (\<Inter> T)) = prob A * prob (\<Inter>T)" using teq assms by auto
qed

lemma mutual_indep_set_singleton: 
  assumes "indep_event A B"
  shows "mutual_indep_set A {B}"
  using indep_eventD_ev1 indep_eventD_ev2 assms 
  by (intro mutual_indep_event_defI) (simp_all add: subset_singleton_iff)

lemma mutual_indep_set_one_compl: 
  assumes "mutual_indep_set A S"
  assumes "finite S"
  assumes "B \<in> S"
  shows "mutual_indep_set A ({space M - B} \<union> S)"
proof (intro mutual_indep_event_defI)
  show "A \<in> events" using assms(1) mutual_indep_setD2 by auto
next
  show "{space M - B} \<union> (S) \<subseteq> events"
    using assms(1) assms(2) mutual_indep_setD3 assms(3) by blast 
next
  fix T assume jss: "T \<subseteq> {space M - B} \<union> (S)"
  assume tne: "T \<noteq> {}"
  let ?T' = "T - {space M - B}"
  show "indep_event A (\<Inter> T)"
  proof (cases "?T' = {}")
    case True
    then have "T = {space M - B}" using tne by blast
    moreover have "indep_event A B" using assms(1) assms(3) assms(3) mutual_indep_singleton_event by auto
    ultimately show ?thesis using indep_event_one_compl by auto
  next
    case tne2: False
    have finT: "finite T" using jss assms(2) finite_subset by fast
    have tss2: "?T' \<subseteq> S" using jss assms(2) by auto
    show ?thesis proof (cases "space M - B \<in> T")
      case True
      have "?T' \<union> {B} \<subseteq> S" using assms(3) tss2 by auto
      then have "indep_event A (\<Inter>(?T' \<union> {B}))" using assms(1) mutual_indep_event_set_defD tne2 finT
        by (meson Un_empty assms(2) finite_subset)
      moreover have "indep_event A (\<Inter>?T')" 
        using assms(1) mutual_indep_event_set_defD finT finite_subset tss2 tne2 by auto
      moreover have "\<Inter>(?T' \<union> {B}) = B \<inter> (\<Inter>?T')" by auto
      moreover have "B \<in> events" using assms(3) assms(1) mutual_indep_setD3 by auto
      ultimately have "indep_event A ((space M - B) \<inter> (\<Inter>?T'))" using indep_event_compl_inter by auto
      then show ?thesis
        by (metis Inter_insert True insert_Diff) 
    next
      case False
      then have "T \<subseteq> S" using jss by auto
      then show ?thesis using assms(1) mutual_indep_event_set_defD finT tne by auto
    qed
  qed
qed

lemma mutual_indep_events_set_update_compl: 
  assumes "mutual_indep_set X E"
  assumes "E = A \<union> B"
  assumes "A \<inter> B = {}"
  assumes "finite E"
  shows "mutual_indep_set X (((-) (space M) ` A) \<union> B)"
using assms(2) assms(3) proof (induct "card A" arbitrary: A B)
  case 0
  then show ?case using assms(1)
    using assms(4) by auto 
next
  case (Suc x)
  then obtain a A' where aeq: "A = insert a A'" and anotin: "a \<notin> A'"
    by (metis card_Suc_eq_finite)
  then have xcard: "card A' = x"
    using Suc(2) Suc(3) assms(4) by auto
  let ?B' = "B \<union> {a}" 
  have "E = A' \<union> ?B'" using aeq Suc.prems by auto
  moreover have "A' \<inter> ?B' = {}" using anotin Suc.prems(2) aeq by auto
  ultimately have ies: "mutual_indep_set X ((-) (space M) ` A' \<union> ?B')" 
    using Suc.hyps(1)[of "A'" ?B'] xcard by auto
  then have "a \<in> A \<union> B" using aeq by auto
  then show ?case 
  proof (cases "(A \<union> B) - {a} = {}")
    case True
    then have "A = {a}" "B = {}" using Suc.prems aeq by auto
    moreover have "indep_event X a" using mutual_indep_singleton_event ies by auto
    ultimately show ?thesis using mutual_indep_set_singleton indep_event_one_compl by simp
  next
    case False
    let ?c = "(-) (space M)"
    have un: "?c ` A \<union> B = ?c ` A' \<union> ({?c a}) \<union> (?B' - {a})"
      using Suc(4) aeq by force 
    moreover have "?B' - {a} \<subseteq> ?B'" by auto
    moreover have "?B' - {a} \<subseteq> ?c ` A' \<union> {?c a} \<union> (?B')" by auto
    moreover have "?c ` A' \<union> {?c a} \<subseteq> ?c ` A' \<union> {?c a} \<union> (?B')" by auto
    ultimately have ss: "?c ` A \<union> B \<subseteq> {?c a} \<union> (?c ` A' \<union> ?B')" 
      using Un_least by auto
    have "a \<in> (-) (space M) ` A' \<union> ?B'" using aeq by auto
    then have ie: "mutual_indep_set X ({?c a} \<union> (?c ` A' \<union> ?B'))" 
      using mutual_indep_set_one_compl[of  X "?c ` A' \<union> ?B'" a] ies \<open>E = A' \<union> (B \<union> {a})\<close> assms(4) by blast
    then show ?thesis using mutual_indep_subset ss by auto
  qed
qed

lemma mutual_indep_events_compl: 
  assumes "finite S"
  assumes "mutual_indep_set A S"
  shows "mutual_indep_set A ((\<lambda> s . space M - s) ` S)"
  using mutual_indep_events_set_update_compl[of A S S "{}"] assms by auto

lemma mutual_indep_set_all:
  assumes "A \<subseteq> events"
  assumes "\<And> Ai. Ai \<in> A \<Longrightarrow> (mutual_indep_set Ai (A - {Ai}))"
  shows "indep_events_set A"
proof (intro indep_events_setI)
  show "A \<subseteq> events"
    using assms(1) by auto
next
  fix J assume ss: "J \<subseteq> A" and fin: "finite J" and ne: "J \<noteq> {}"
  from fin ne ss show "prob (\<Inter>J) = prod prob J"
  proof (induct J rule: finite_ne_induct)
    case (singleton x)
    then show ?case by simp
  next
    case (insert x F)
    then have "mutual_indep_set x (A - {x})" using assms(2) by simp
    moreover have "F \<subseteq> (A - {x})" using insert.prems insert.hyps by auto
    ultimately have "prob (x \<inter> (\<Inter>F)) = prob x * prob (\<Inter>F)"
      by (simp add: local.insert(2) mutual_indep_setD) 
    then show ?case using insert.hyps insert.prems by simp
  qed
qed

text \<open>Prefered version using indexed notation \<close>
definition mutual_indep_events:: "'a set \<Rightarrow> (nat \<Rightarrow> 'a set) \<Rightarrow> nat set \<Rightarrow> bool"
  where "mutual_indep_events A F I \<longleftrightarrow> A \<in> events \<and> (F ` I \<subseteq> events) \<and> (\<forall> J \<subseteq> I . J \<noteq> {} \<longrightarrow> prob (A \<inter> (\<Inter>j \<in> J . F j)) = prob A * prob (\<Inter>j \<in> J . F j))"
(* Not condition about T not empty, only necessary due to Univ issue?*)
(* Use every subset, rather than the not version given by Zhao, should this include condition re prob *)

lemma mutual_indep_eventsI[intro]: "A \<in> events \<Longrightarrow> (F ` I \<subseteq> events) \<Longrightarrow> (\<And> J. J \<subseteq> I \<Longrightarrow> J \<noteq> {} \<Longrightarrow> 
    prob (A \<inter> (\<Inter>j \<in> J . F j)) = prob A * prob (\<Inter>j \<in> J . F j)) \<Longrightarrow> mutual_indep_events A F I" 
  using mutual_indep_events_def by simp

lemma mutual_indep_eventsD[dest]: "mutual_indep_events A F I \<Longrightarrow> J \<subseteq> I \<Longrightarrow> J \<noteq> {} \<Longrightarrow> prob (A \<inter> (\<Inter>j \<in> J . F j)) = prob A * prob (\<Inter>j \<in> J . F j)"
  using mutual_indep_events_def by simp

lemma mutual_indep_eventsD2[dest]: "mutual_indep_events A F I \<Longrightarrow> A \<in> events"
  using mutual_indep_events_def by simp

lemma mutual_indep_eventsD3[dest]: "mutual_indep_events A F I \<Longrightarrow> F ` I \<subseteq> events"
  using mutual_indep_events_def by simp

lemma mutual_indep_ev_subset: "mutual_indep_events A F I \<Longrightarrow> J \<subseteq> I \<Longrightarrow> mutual_indep_events A F J"
  using mutual_indep_events_def by (meson image_mono subset_trans)

lemma mutual_indep_event_defD: 
  assumes "mutual_indep_events A F I"
  assumes "finite J"
  assumes "J \<subseteq> I"
  assumes "J \<noteq> {}"
  shows "indep_event A (\<Inter>j \<in> J . F j)"
proof (intro indep_eventI)
  show "A \<in> events" using mutual_indep_setD2 assms(1) by auto
  show "prob (A \<inter> \<Inter> (F ` J)) = prob A * prob (\<Inter> (F ` J))" 
    using assms(1) mutual_indep_eventsD assms(3) assms(4) by simp
  have "finite (F ` J)" using finite_subset assms(2) by simp 
  then show "(\<Inter>j \<in> J . F j) \<in> events" 
    using Inter_event_ss[of "F ` J"] assms mutual_indep_eventsD3 by blast
qed

lemma mutual_ev_indep_event_defI: "A \<in> events \<Longrightarrow> F ` I \<subseteq> events \<Longrightarrow> (\<And> J. J \<subseteq> I \<Longrightarrow> J \<noteq> {} \<Longrightarrow> 
    indep_event A (\<Inter>(F` J))) \<Longrightarrow> mutual_indep_events A F I"
  using indep_eventD mutual_indep_events_def[of A F I] by auto

lemma mutual_indep_ev_singleton_event: 
  assumes "mutual_indep_events A F I"
  assumes "B \<in> F ` I"
  shows"indep_event A B" 
proof -
  obtain J where beq: "B = F J" and "J \<in> I" using assms(2) by blast
  then have "{J} \<subseteq> I" and "finite {J}" and "{J} \<noteq> {}" by auto
  moreover have "B = \<Inter> (F ` {J})" using beq by simp
  ultimately show ?thesis using mutual_indep_event_defD assms(1)
    by meson
qed

lemma mutual_indep_ev_singleton_event2: 
  assumes "mutual_indep_events A F I"
  assumes "i \<in> I"
  shows"indep_event A (F i)" 
  using  mutual_indep_event_defD[of A F I "{i}"] assms by auto 

lemma mutual_indep_iff: 
  shows "mutual_indep_events A F I \<longleftrightarrow> mutual_indep_set A (F ` I)"
proof (intro iffI mutual_indep_setI mutual_indep_eventsI)
  show "mutual_indep_events A F I \<Longrightarrow> A \<in> events" using mutual_indep_eventsD2 by simp
  show "mutual_indep_set A (F ` I) \<Longrightarrow> A \<in> events" using mutual_indep_setD2 by simp
  show "mutual_indep_events A F I \<Longrightarrow> F ` I \<subseteq> events" using mutual_indep_eventsD3 by simp
  show "mutual_indep_set A (F ` I) \<Longrightarrow> F ` I \<subseteq> events" using mutual_indep_setD3 by simp
  show "\<And>T. mutual_indep_events A F I \<Longrightarrow> T \<subseteq> F ` I \<Longrightarrow> T \<noteq> {} \<Longrightarrow> prob (A \<inter> \<Inter> T) = prob A * prob (\<Inter> T)"
    using mutual_indep_eventsD by (metis empty_is_image subset_imageE) 
  show "\<And>J. mutual_indep_set A (F ` I) \<Longrightarrow> J \<subseteq> I \<Longrightarrow> J \<noteq> {} \<Longrightarrow> prob (A \<inter> \<Inter> (F ` J)) = prob A * prob (\<Inter> (F ` J))"
    using mutual_indep_setD by (simp add: image_mono) 
qed

lemma mutual_indep_ev_cond: 
  assumes "A \<in> events" and "F ` J \<subseteq> events" and "finite J"
  and "mutual_indep_events A F I" and "J \<subseteq> I" and "J \<noteq> {}" and "prob (\<Inter>(F `J)) \<noteq> 0"
shows "\<P>(A |(\<Inter>(F ` J))) = prob A"
proof -
  have "\<Inter>(F ` J) \<in> events" using assms
    by (simp add: Inter_event_ss) 
  then have "\<P>(A | (\<Inter>(F ` J))) = prob ((\<Inter>(F ` J)) \<inter> A)/prob(\<Inter>(F ` J))" 
    using cond_prob_ev_def assms(1) by blast
  also have "... = prob (A \<inter> (\<Inter>(F ` J)))/prob(\<Inter>(F ` J))"
    by (simp add: inf_commute) 
  also have "... = prob A * prob (\<Inter>(F ` J))/prob(\<Inter>(F ` J))" 
    using assms mutual_indep_eventsD by auto
  finally show ?thesis using assms(7) by simp
qed

lemma mutual_indep_ev_cond_full:
  assumes "A \<in> events" and "F ` I \<subseteq> events" and "finite I"
  and "mutual_indep_events A F I" and  "I \<noteq> {}" and "prob (\<Inter>(F ` I)) \<noteq> 0"
shows "\<P>(A |(\<Inter>(F `I))) = prob A"
  using mutual_indep_ev_cond[of A F I I] assms by auto

lemma mutual_indep_ev_cond_single: 
  assumes "A \<in> events" and "B \<in> events"
  and "mutual_indep_events A F I" and "B \<in> F ` I" and "prob B \<noteq> 0"
shows "\<P>(A |B) = prob A"
proof -
  obtain i where "B = F i" and "i \<in> I" using assms by blast
  then show ?thesis using mutual_indep_ev_cond[of "A" F "{i}" I] assms by auto
qed

lemma mutual_indep_ev_empty: "A \<in> events \<Longrightarrow> mutual_indep_events A F {}"
  using mutual_indep_eventsI by auto

lemma not_mutual_indep_ev_itself: 
  assumes "prob A > 0" and "prob A < 1" and "A = F i"
  shows "\<not> mutual_indep_events A F {i}"
proof (rule ccontr)
  assume "\<not> \<not> mutual_indep_events A F {i}"
  then have "mutual_indep_events A F {i}"
    by simp
  then have "\<And> J . J \<subseteq> {i} \<Longrightarrow> J \<noteq> {} \<Longrightarrow> prob (A \<inter> (\<Inter> (F ` J))) = prob A * prob (\<Inter>(F ` J))"
    using mutual_indep_eventsD by simp
  then have eq: "prob (A \<inter> (\<Inter> (F `{i}))) = prob A * prob (\<Inter>(F ` {i}))"
    by blast 
  have "prob (A \<inter> (\<Inter>(F `{i}))) = prob A" using assms(3) by simp
  moreover have "prob A * (prob (\<Inter> {A})) = (prob A)^2"
    by (simp add: power2_eq_square) 
  ultimately show False using eq assms by auto
qed

lemma is_mutual_indep_ev_itself:
  assumes "A \<in> events" and "A = F i"
  assumes "prob A = 0 \<or> prob A = 1"
  shows "mutual_indep_events A F {i}"
proof (intro mutual_indep_eventsI)
  show "A \<in> events" "F ` {i} \<subseteq> events" using assms(1) assms(2)  by auto
  fix J assume "J \<subseteq> {i}" and "J \<noteq> {}"
  then have teq: "J = {i}" by auto
  have "prob (A \<inter> (\<Inter>(F `{i}))) = prob A" using assms(2) by simp
  moreover have "prob A * (prob (\<Inter> (F `{i}))) = (prob A)^2"
    using assms(2) by (simp add: power2_eq_square) 
  ultimately show  "prob (A \<inter> \<Inter> (F ` J)) = prob A * prob (\<Inter> (F ` J))" using teq assms by auto
qed

lemma mutual_indep_ev_singleton: 
  assumes "indep_event A (F i)"
  shows "mutual_indep_events A F {i}"
  using indep_eventD_ev1 indep_eventD_ev2 assms 
  by (intro mutual_ev_indep_event_defI) (simp_all add: subset_singleton_iff)

lemma mutual_indep_ev_one_compl: 
  assumes "mutual_indep_events A F I"
  assumes "finite I"
  assumes "i \<in> I"
  assumes "space M - F i = F j"
  shows "mutual_indep_events A F ({j} \<union>  I)"
proof (intro mutual_ev_indep_event_defI)
  show "A \<in> events" using assms(1) mutual_indep_setD2 by auto
next
  show "F ` ({j} \<union> I) \<subseteq> events"
    using assms(1) assms(2) mutual_indep_eventsD3 assms(3) assms(4)
    by (metis image_insert image_subset_iff insert_is_Un insert_subset sets.compl_sets)  
next
  fix J assume jss: "J \<subseteq> {j} \<union> I"
  assume tne: "J \<noteq> {}"
  let ?J' = "J - {j}"
  show "indep_event A (\<Inter> (F ` J))"
  proof (cases "?J' = {}")
    case True
    then have "J = {j}" using tne by blast
    moreover have "indep_event A (F i)" 
      using assms(1) assms mutual_indep_ev_singleton_event2 by simp
    ultimately show ?thesis using indep_event_one_compl assms(4) by fastforce 
  next
    case tne2: False
    have finT: "finite J" using jss assms(2) finite_subset by fast
    have tss2: "?J' \<subseteq> I" using jss assms(2) by auto
    show ?thesis proof (cases "j \<in> J")
      case True
      have "?J' \<union> {i} \<subseteq> I" using assms(3) tss2 by auto
      then have "indep_event A (\<Inter>(F ` ?J' \<union> { F i}))" 
        using assms(1) mutual_indep_event_defD tne2 finT  assms(2) finite_subset
        by (metis Diff_cancel Un_Diff_cancel Un_absorb Un_insert_right image_insert) 
      moreover have "indep_event A (\<Inter>(F ` ?J'))" 
        using assms(1) mutual_indep_event_defD finT finite_subset tss2 tne2 by auto
      moreover have "(\<Inter>(F ` ?J' \<union> { F i})) = F i \<inter> (\<Inter>(F ` ?J'))" by auto
      moreover have "F i \<in> events" using assms(3) assms(1) mutual_indep_eventsD3 by simp
      ultimately have "indep_event A (F j \<inter> (\<Inter>(F ` ?J')))" 
        using indep_event_compl_inter[of A "\<Inter>(F ` ?J')" "F i"] assms(4) by auto
      then show ?thesis using Inter_insert True insert_Diff by (metis image_insert) 
    next
      case False
      then have "J \<subseteq> I" using jss by auto
      then show ?thesis using assms(1) mutual_indep_event_defD finT tne by auto
    qed
  qed
qed

lemma mutual_indep_events_update_compl: 
  assumes "mutual_indep_events X F S"
  assumes "S = A \<union> B"
  assumes "A \<inter> B = {}"
  assumes "finite S"
  assumes "bij_betw G A A'"
  assumes "\<And> i. i \<in> A \<Longrightarrow> F (G i) = space M - F i"
  shows "mutual_indep_events X F (A' \<union> B)"
using assms(2) assms(3) assms(6) assms(5) proof (induct "card A" arbitrary: A B A')
  case 0
  then have aempty: "A = {}" using finite_subset assms(4) by simp
  then have "A' = {}" using "0.prems"(4) by (metis all_not_in_conv bij_betwE bij_betw_inv)
  then show ?case using assms(1) using "0.prems"(1) aempty by simp
next
  case (Suc x)
  then obtain a C where aeq: "C = A - {a}" and ain: "a \<in> A"
    by fastforce 
  then have xcard: "card C = x"
    using Suc(2) Suc(3) assms(4) by auto
  let ?C' = "A' - {G a}"
  have compl:  "(\<And>i. i \<in> C \<Longrightarrow> F (G i) = space M - F i)" using Suc.prems aeq by simp
  have bb: "bij_betw G C ?C'" using Suc.prems(4) aeq bij_betw_remove[of G A A' a] ain by simp
  let ?B' = "B \<union> {a}" 
  have "S = C \<union> ?B'" using aeq Suc.prems ain by auto
  moreover have "C \<inter> ?B' = {}" using ain Suc.prems(2) aeq by auto
  ultimately have ies: "mutual_indep_events X F (?C' \<union> ?B')" 
    using Suc.hyps(1)[of "C" ?B'] xcard compl bb by auto
  then have "a \<in> A \<union> B" using ain by auto
  then show ?case 
  proof (cases "(A \<union> B) - {a} = {}")
    case True
    then have aeq: "A = {a}" and beq: "B = {}" using Suc.prems ain by auto
    then have "A' = {G a}" using aeq Suc.prems ain aeq bb bij_betwE bij_betw_empty1 insert_Diff
      by (metis Un_Int_eq(4) Un_commute \<open>C \<inter> (B \<union> {a}) = {}\<close> \<open>S = C \<union> (B \<union> {a})\<close>)  
    moreover have "F (G a) = space M - (F a)" using Suc.prems ain by auto
    moreover have "indep_event X (F a)" using mutual_indep_ev_singleton_event ies by auto
    ultimately show ?thesis using mutual_indep_ev_singleton indep_event_one_compl beq by auto
  next
    case False
    have un: "A' \<union> B = ?C' \<union> {G a} \<union> (?B' - {a})" using Suc.prems aeq  
      by (metis Diff_insert_absorb Un_empty_right Un_insert_right ain bij_betwE 
          disjoint_iff_not_equal insert_Diff)
    moreover have "?B' - {a} \<subseteq> ?B'" by auto
    moreover have "?B' - {a} \<subseteq> ?C' \<union> {G a} \<union> (?B')" by auto
    moreover have "?C' \<union> {G a} \<subseteq> ?C' \<union> {G a} \<union> (?B')" by auto
    ultimately have ss: "A' \<union> B \<subseteq> {G a} \<union> (?C' \<union> ?B')" 
      using Un_least by auto
    have "a \<in> ?C' \<union> ?B'" using aeq by auto
    then have ie: "mutual_indep_events X F ({G a} \<union> (?C' \<union> ?B'))" 
      using mutual_indep_ev_one_compl[of X F "(?C' \<union> ?B')" "a" "G a"] using Suc.prems(3)
      by (metis \<open>S = C \<union> (B \<union> {a})\<close> ain assms(4) bb bij_betw_finite ies infinite_Un)  
    then show ?thesis using mutual_indep_ev_subset ss by auto
  qed
qed

lemma mutual_indep_ev_events_compl: 
  assumes "finite S"
  assumes "mutual_indep_events A F S"
  assumes "bij_betw G S S'"
  assumes "\<And> i. i \<in> S \<Longrightarrow> F (G i) = space M - F i"
  shows "mutual_indep_events A F S'"
  using mutual_indep_events_update_compl[of A F S S "{}"] assms by auto

text \<open>Important lemma on relation between independence and mutual independence of a set \<close>
lemma mutual_indep_ev_set_all:
  assumes "F ` I \<subseteq> events"
  assumes "\<And> i. i \<in> I \<Longrightarrow> (mutual_indep_events (F i) F (I - {i}))"
  shows "indep_events F I"
proof (intro indep_eventsI)
  show "\<And>i. i \<in> I \<Longrightarrow> F i \<in> events"
    using assms(1) by auto
next
  fix J assume ss: "J \<subseteq> I" and fin: "finite J" and ne: "J \<noteq> {}"
  from fin ne ss show "prob (\<Inter> (F ` J)) = (\<Prod>i\<in>J. prob (F i))"
  proof (induct J rule: finite_ne_induct)
    case (singleton x)
    then show ?case by simp
  next
    case (insert x X)
    then have "mutual_indep_events (F x) F (I - {x})" using assms(2) by simp
    moreover have "X \<subseteq> (I - {x})" using insert.prems insert.hyps by auto
    ultimately have "prob (F x \<inter> (\<Inter>(F `X))) = prob (F x) * prob (\<Inter>(F ` X))"
      by (simp add: local.insert(2) mutual_indep_eventsD) 
    then show ?case using insert.hyps insert.prems by simp
  qed
qed

end
end