(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

header {* Formalization of the Crowds-Protocol *}

theory Crowds_Protocol
  imports "../Discrete_Time_Markov_Chain"
begin

lemma PiE_cong: "I = J \<Longrightarrow> (\<And>i. i \<in> J \<Longrightarrow> f i = g i) \<Longrightarrow> Pi\<^isub>E I f = Pi\<^isub>E J g"
  by auto

lemma fun_if_distrib:
  "card (if P then A else B) = (if P then card A else card B)"
  "real (if P then x else y) = (if P then real x else real y)"
  "(if P then a else b) * c = (if P then a * c else b * c)"
  "(if P then a else b) / c = (if P then a / c else b / c)"
  by auto

syntax
  "_prob" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("('\<PP>'(_ in _. _'))")

translations
  "\<PP>(x in M. P)" => "CONST finite_measure.\<mu>' M {x \<in> CONST space M. P}"

definition
  "cond_prob M P Q = \<PP>(\<omega> in M. P \<omega> \<and> Q \<omega>) / \<PP>(\<omega> in M. Q \<omega>)"

syntax
  "_conditional_prob" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("('\<PP>'(_ in _. _ \<bar>/ _'))")

translations
  "\<PP>(x in M. P \<bar> Q)" => "CONST cond_prob M (\<lambda>x. P) (\<lambda>x. Q)"

lemma setsum_PiE_insert:
  "i \<notin> I \<Longrightarrow> (\<Sum>\<omega>\<in>Pi\<^isub>E (insert i I) X. f \<omega>) = (\<Sum>x\<in>(X i). \<Sum>\<omega>\<in>Pi\<^isub>E I X. f (\<omega>(i:=x)))"
  by (auto simp add: setsum_reindex setsum_cartesian_product inj_on_upd_PiE PiE_insert
           intro!: setsum_cong)

lemma PiE_mono: "(\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x) \<Longrightarrow> Pi\<^isub>E A B \<subseteq> Pi\<^isub>E A C"
  by auto

lemma (in Discrete_Time_Markov_Chain) prob_ball_cylinder:
  assumes "s \<in> S" "I \<noteq> {}" "finite I"
  shows "\<PP>(X' in path_space s. \<forall>i\<in>I. X' i \<in> Y i) =
    (\<Sum>\<omega>\<in>(\<Pi>\<^isub>E i\<in>{..Max I}. (if i \<in> I then Y i \<inter> S else S)). \<Prod>i\<le>Max I. \<tau> (nat_case s \<omega> i) (\<omega> i))"
  using assms
  by (subst prob_cylinder_eq_sum_prod'[symmetric])
     (auto intro!: arg_cong[where f="prob s"] simp: space_path_space)

lemma (in Discrete_Time_Markov_Chain) eq_sets_path_space[simp, intro]:
  "{X' \<in> space (path_space s). X' i = s'} \<in> events s"
  by (simp add: space_path_space)

lemma (in Discrete_Time_Markov_Chain) markov_property_with_\<tau>:
  assumes s: "s \<in> S" "\<And>i. i \<in> I \<Longrightarrow> t i \<in> S" "t (Suc (Max I)) \<in> S"
    and I: "finite I" "I \<noteq> {}"
    and neq0: "\<PP>(\<omega> in path_space s. \<forall>j\<in>I. \<omega> j = t j ) \<noteq> 0"
  shows "\<PP>(\<omega> in path_space s. \<omega> (Suc (Max I)) = t (Suc (Max I)) \<bar> \<forall>j\<in>I. \<omega> j = t j ) =
   \<tau> (t (Max I)) (t (Suc (Max I)))"
proof -
  let ?i = "Suc (Max I)"

  from Max_less_iff[OF I, of ?i]
  have "?i \<notin> I"
    by auto
  then have cylinder_forms:
    "\<And>\<omega>. (\<forall>j\<in>I. \<omega> j = t j) \<longleftrightarrow> (\<forall>j\<in>I. \<omega> j \<in> {t j})"
    "\<And>\<omega>. \<omega> ?i = t ?i \<and> (\<forall>j\<in>I. \<omega> j \<in> {t j}) \<longleftrightarrow> (\<forall>j\<in>insert ?i I. \<omega> j \<in> {t j})"
    by auto

  have *:
    "{.. max ?i (Max I)} = insert ?i (insert (Max I) {..<Max I})"
    "{..Max I} = insert (Max I) {..<Max I}"
    "(\<Pi>\<^isub>E j\<in>{..<Max I}. if j = Suc (Max I) \<or> j \<in> I then {t j} \<inter> S else S) =
     (\<Pi>\<^isub>E j\<in>{..<Max I}. if j \<in> I then {t j} \<inter> S else S)"
    by (auto simp: Pi_iff split: split_if_asm)

  show ?thesis unfolding cond_prob_def
    using s I neq0
    by (simp add: cylinder_forms prob_ball_cylinder del: ball_simps insert_iff)
       (simp add: setsum_PiE_insert * setsum_right_distrib[symmetric]
             cong: nat.case_cong)
qed

lemma (in Discrete_Time_Markov_Chain) markov_property:
  assumes s: "s \<in> S" and I: "finite I" "I \<noteq> {}"
    and neq0: "\<PP>(\<omega> in path_space s. \<forall>j\<in>I. \<omega> j = t j ) \<noteq> 0"
  shows "\<PP>(\<omega> in path_space s. \<omega> (Suc (Max I)) = t (Suc (Max I)) \<bar> \<forall>j\<in>I. \<omega> j = t j) =
         \<PP>(\<omega> in path_space s. \<omega> (Suc (Max I)) = t (Suc (Max I)) \<bar> \<omega> (Max I) = t (Max I) )"
  (is "?L = ?R")
proof cases
  have [simp]: "Max I \<in> I" using I by simp
  assume in_S: "t (Suc (Max I)) \<in> S \<and> (\<forall>j\<in>I. t j \<in> S)"
  with assms have "?L = \<tau> (t (Max I)) (t (Suc (Max I)))"
    by (intro markov_property_with_\<tau>) auto
  moreover
  { have "0 < prob s {\<omega>\<in>space (path_space s). (\<forall>j\<in>I. \<omega> j = t j) }"
      using neq0 by (simp add: less_le)
    also have "\<dots> \<le> prob s {\<omega>\<in>space (path_space s). \<omega> (Max I) = t (Max I) }"
      by (auto intro!: finite_measure_mono)
    finally have "?R = \<tau> (t (Max I)) (t (Suc (Max I)))"
      using assms in_S markov_property_with_\<tau>[of s "{Max I}" t] by simp }
  ultimately show "?L = ?R" by simp
next
  assume "\<not> (t (Suc (Max I)) \<in> S \<and> (\<forall>i\<in>I. t i \<in> S))"
  then have "t (Suc (Max I)) \<notin> S \<or> (\<exists>i\<in>I. t i \<notin> S)" by auto
  then show ?thesis
  proof
    assume "t (Suc (Max I)) \<notin> S"
    then have cylinders:
      "{\<omega>\<in>space (path_space s). \<omega> (Suc (Max I)) = t (Suc (Max I)) \<and> (\<forall>i\<in>I. \<omega> i = t i) } = {}"
      "{\<omega>\<in>space (path_space s). \<omega> (Suc (Max I)) = t (Suc (Max I)) \<and> \<omega> (Max I) = t (Max I) } = {}"
      by (auto simp: space_path_space Pi_iff) metis+
    show ?thesis
      unfolding cond_prob_def cylinders by simp
  next
    assume "\<exists>i\<in>I. t i \<notin> S"
    then have "{\<omega>\<in>space (path_space s). \<forall>i\<in>I. \<omega> i = t i } = {}"
      by (auto simp: space_path_space Pi_iff) metis
    with neq0 show ?thesis by simp
  qed
qed

lemma (in Discrete_Time_Markov_Chain) time_homogeneous:
  fixes s a b :: 's
  assumes S: "s \<in> S"
  and neq0:
    "\<PP>(\<omega> in path_space s. \<omega> i = a) \<noteq> 0"
    "\<PP>(\<omega> in path_space s. \<omega> j = a) \<noteq> 0"
  shows "\<PP>(\<omega> in path_space s. \<omega> (Suc i) = b \<bar> \<omega> i = a) =
         \<PP>(\<omega> in path_space s. \<omega> (Suc j) = b \<bar> \<omega> j = a)"
proof cases
  assume "a \<in> S \<and> b \<in> S"
  then show ?thesis
    using markov_property_with_\<tau>[OF `s \<in> S`, of "{i}" "\<lambda>k. if k = i then a else b"]
    using markov_property_with_\<tau>[OF `s \<in> S`, of "{j}" "\<lambda>k. if k = j then a else b"]
    using S neq0 by simp
next
  assume "\<not> (a \<in> S \<and> b \<in> S)"
  then have *: "\<And>i. {\<omega> \<in> space (path_space s). \<omega> (Suc i) = b \<and> \<omega> i = a } = {}"
    by (auto simp: space_path_space)
  show ?thesis
    unfolding cond_prob_def * by simp
qed

lemma (in Discrete_Time_Markov_Chain) sets_Collect_path_eq[simp, intro]:
  "{X' \<in> space (path_space s). X' i = s'} \<in> events s"
  unfolding space_path_space by simp

lemma (in Discrete_Time_Markov_Chain) sets_Collect_path_in[simp, intro]:
  "{X' \<in> space (path_space s). X' i \<in> X} \<in> events s"
  unfolding space_path_space by simp

lemma (in prob_space) AE_E_prob:
  assumes ae: "AE x. P x"
  obtains S where "S \<subseteq> {x \<in> space M. P x}" "S \<in> events" "prob S = 1"
proof -
  from ae[THEN AE_E] guess N .
  then show thesis
    by (intro that[of "space M - N"])
       (auto simp: measure_compl \<mu>'_def measure_space_1)
qed

lemma (in prob_space) prob_neg: "{x\<in>space M. P x} \<in> events \<Longrightarrow> \<PP>(x in M. \<not> P x) = 1 - \<PP>(x in M. P x)"
  by (auto intro!: arg_cong[where f=prob] simp add: prob_compl[symmetric])

lemma (in prob_space) prob_eq_AE:
  "(AE x. P x \<longleftrightarrow> Q x) \<Longrightarrow> {x\<in>space M. P x} \<in> events \<Longrightarrow> {x\<in>space M. Q x} \<in> events \<Longrightarrow> \<PP>(x in M. P x) = \<PP>(x in M. Q x)"
  by (rule finite_measure_eq_AE) auto

lemma (in prob_space) prob_eq_0_AE:
  assumes not: "AE x. \<not> P x" shows "\<PP>(x in M. P x) = 0"
proof cases
  assume "{x\<in>space M. P x} \<in> events"
  with not have "\<PP>(x in M. P x) = \<PP>(x in M. False)"
    by (intro prob_eq_AE) auto
  then show ?thesis by simp
qed (simp add: \<mu>'_def)

lemma (in prob_space) prob_sums:
  assumes P: "\<And>n. {x\<in>space M. P n x} \<in> events"
  assumes Q: "{x\<in>space M. Q x} \<in> events"
  assumes ae: "AE x. (\<forall>n. P n x \<longrightarrow> Q x) \<and> (Q x \<longrightarrow> (\<exists>!n. P n x))"
  shows "(\<lambda>n. \<PP>(x in M. P n x)) sums \<PP>(x in M. Q x)"
proof -
  from ae[THEN AE_E_prob] guess S . note S = this
  then have disj: "disjoint_family (\<lambda>n. {x\<in>space M. P n x} \<inter> S)"
    by (auto simp: disjoint_family_on_def)
  from S have ae_S:
    "AE x. x \<in> {x\<in>space M. Q x} \<longleftrightarrow> x \<in> (\<Union>n. {x\<in>space M. P n x} \<inter> S)"
    "\<And>n. AE x. x \<in> {x\<in>space M. P n x} \<longleftrightarrow> x \<in> {x\<in>space M. P n x} \<inter> S"
    using ae by (auto dest!: AE_prob_1)
  from ae_S have *:
    "\<PP>(x in M. Q x) = prob (\<Union>n. {x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) auto
  from ae_S have **:
    "\<And>n. \<PP>(x in M. P n x) = prob ({x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) auto
  show ?thesis
    unfolding * ** using S P disj
    by (intro finite_measure_UNION) auto
qed

lemma (in sigma_algebra) sets_Collect_Least:
  assumes Q: "\<And>n::nat. {x\<in>space M. Q n x} \<in> sets M"
  assumes P: "\<And>n::nat. {x\<in>space M. P n x} \<in> sets M"
  shows "{x\<in>space M. P (LEAST n. Q n x) x} \<in> sets M"
proof -
  have "{x\<in>space M. P (LEAST n. Q n x) x} =
    {x\<in>space M. \<forall>n. (LEAST n. Q n x) = n \<longrightarrow> P n x}" by auto
  moreover
  { fix n have "{x\<in>space M. (LEAST n. Q n x) = n} \<in> sets M"
      using measurable_Least[of Q "{n}"] Q by (simp add: vimage_def Collect_Int) }
  then have "{x\<in>space M. \<forall>n. (LEAST n. Q n x) = n \<longrightarrow> P n x} \<in> sets M"
    using measurable_Least[of Q]
    by (intro sets_Collect P) auto
  ultimately show ?thesis
    by simp
qed

lemma (in prob_space) cond_prob_eq_AE:
  assumes P: "AE x. Q x \<longrightarrow> P x \<longleftrightarrow> P' x" "{x\<in>space M. P x} \<in> events" "{x\<in>space M. P' x} \<in> events"
  assumes Q: "AE x. Q x \<longleftrightarrow> Q' x" "{x\<in>space M. Q x} \<in> events" "{x\<in>space M. Q' x} \<in> events"
  shows "cond_prob M P Q = cond_prob M P' Q'"
  using P Q
  by (auto simp: cond_prob_def elim!: AE_mp intro!: arg_cong2[where f="op /"] prob_eq_AE sets_Collect_conj)

subsection {* Definition of the Crowds-Protocol *}

datatype 'a state = Start | Init 'a | Mix 'a | End

lemma inj_Mix[simp]: "inj_on Mix A"
  by (auto intro: inj_onI)

lemma inj_Init[simp]: "inj_on Init A"
  by (auto intro: inj_onI)

locale Crowds_Protocol =
  fixes jondos :: "'a set" and colls :: "'a set" and p_f :: real and init :: "'a \<Rightarrow> real"
  assumes jondos_non_empty: "jondos \<noteq> {}" and finite_jondos[simp]: "finite jondos"
  assumes colls_smaller: "colls \<subset> jondos" and colls_non_empty: "colls \<noteq> {}"
  assumes p_f: "0 < p_f" "p_f < 1"
  assumes init_nonneg: "\<And>j. j \<in> jondos \<Longrightarrow> 0 \<le> init j"
  assumes init_distr: "(\<Sum>j\<in>jondos. init j) = 1"
  assumes init_coll: "\<And>j. j \<in> colls \<Longrightarrow> init j = 0"
begin

primrec jondo_of :: "'a state \<Rightarrow> 'a" where
  "jondo_of (Init j) = j"
| "jondo_of (Mix j) = j"

lemma finite_colls[simp]: "finite colls"
  using colls_smaller finite_jondos by (blast intro: finite_subset)

definition
  "valid_states = { Start } \<union> Init ` (jondos - colls) \<union> Mix ` jondos \<union> { End }"

lemma Init_cut_Mix[simp]:
  "Init ` (jondos - colls) \<inter> Mix ` jondos = {}"
  by auto

lemma setsum_init_colls[simp]: "setsum init colls = 0"
  by (auto intro: setsum_0' init_coll)

lemma setsum_init_jondos_m_colls[simp]: "setsum init (jondos - colls) = 1"
  using colls_smaller by (simp add: setsum_diff init_distr)

lemma setsum_valid_states[simp]:
  fixes f :: "'a state \<Rightarrow> real"
  shows "(\<Sum>s\<in>valid_states. f s) = f Start + f End +
  (\<Sum>j\<in>jondos - colls. f (Init j)) + (\<Sum>j\<in>jondos. f (Mix j))"
  by (simp add: valid_states_def image_iff setsum_reindex setsum_Un)

lemma valid_statesE:
  assumes "s \<in> valid_states"
  obtains (Start) "s = Start" | (End) "s = End"
        | (Mix) j where "j \<in> jondos" "s = Mix j"
        | (Init) j where "j \<in> jondos" "s = Init j"
  using assms by (auto simp: valid_states_def)

lemma Start_not_Mix[simp]: "Start \<notin> Mix ` A"
  by auto

lemma End_not_Mix[simp]: "End \<notin> Mix ` A"
  by auto

lemma Start_not_Init[simp]: "Start \<notin> Init ` A"
  by auto

lemma End_not_Init[simp]: "End \<notin> Init ` A"
  by auto

lemma Start_valid_state[iff]: "Start \<in> valid_states"
  by (auto simp: valid_states_def)

lemma End_valid_state[iff]: "End \<in> valid_states"
  by (auto simp: valid_states_def)

lemma Mix_in_valid_state[iff]: "Mix j \<in> valid_states \<longleftrightarrow> j \<in> jondos"
  by (auto simp: valid_states_def inj_image_mem_iff)

lemma Init_in_valid_state[iff]: "Init j \<in> valid_states \<longleftrightarrow> j \<in> jondos - colls"
  by (auto simp: valid_states_def inj_image_mem_iff)

lemma possible_jondo:
  obtains j where "j \<in> jondos" "j \<notin> colls" "init j \<noteq> 0"
proof (atomize_elim, rule ccontr)
  assume "\<not> (\<exists>j. j \<in> jondos \<and> j \<notin> colls \<and> init j \<noteq> 0)"
  with init_coll have "\<forall>j\<in>jondos. init j = 0"
    by auto
  then have "(\<Sum>j\<in>jondos. init j) = 0"
    by (rule setsum_0')
  with init_distr show False
    by simp
qed

definition "J = 1 / card jondos"
definition "H = card (jondos - colls) / card jondos"

lemma colls_le_jondos[simp]: "card colls < card jondos"
  using colls_smaller
  by (intro psubset_card_mono) auto

lemma H: "0 < H" "H < 1"
  using jondos_non_empty colls_smaller colls_non_empty
  by (simp_all add: H_def card_Diff_subset card_mono real_of_nat_diff
                    field_simps zero_less_divide_iff card_gt_0_iff)

lemma H_pf_0: "0 < H * p_f"
  using p_f H by (simp add: zero_less_mult_iff)

lemma H_pf_1: "H * p_f < 1"
proof -
  have "H * p_f < 1 * 1"
    using H p_f by (intro mult_strict_mono) auto
  then show "H * p_f < 1" by simp
qed

lemma H_compl: "1 - H = real (card colls) / real (card jondos)"
  using colls_non_empty jondos_non_empty colls_smaller
  by (simp add: H_def card_Diff_subset card_mono real_of_nat_diff divide_eq_eq field_simps)

lemma H_eq2: "card (jondos - colls) * J = H"
  unfolding J_def H_def by simp

primrec next_step :: "'a state \<Rightarrow> 'a state \<Rightarrow> real" where
  "next_step Start    = (\<lambda>Start \<Rightarrow> 0 | Init j \<Rightarrow> init j | Mix j \<Rightarrow> 0       | End \<Rightarrow> 0)"
| "next_step (Init j) = (\<lambda>Start \<Rightarrow> 0 | Init _ \<Rightarrow> 0      | Mix j \<Rightarrow> J       | End \<Rightarrow> 0)"
| "next_step (Mix j)  = (\<lambda>Start \<Rightarrow> 0 | Init _ \<Rightarrow> 0      | Mix j \<Rightarrow> p_f * J | End \<Rightarrow> 1 - p_f)"
| "next_step End      = (\<lambda>Start \<Rightarrow> 0 | Init _ \<Rightarrow> 0      | Mix j \<Rightarrow> 0       | End \<Rightarrow> 1)"

lemma next_step_to_Start_eq_0[simp]: "next_step s' Start = 0"
  by (cases s') auto

lemma next_step_to_Init[simp]: "next_step s (Init j) =
    (case s of Start \<Rightarrow> init j | _ \<Rightarrow> 0)"
  by (cases s) auto

lemma next_step_to_Mix[simp]: "next_step s (Mix j) =
    (case s of Init j \<Rightarrow> J | Mix j \<Rightarrow> p_f * J | _ \<Rightarrow> 0)"
  by (cases s) auto

lemma next_step_to_End[simp]: "next_step s End =
    (case s of Mix j \<Rightarrow> 1 - p_f | End \<Rightarrow> 1 | _ \<Rightarrow> 0)"
  by (cases s) auto

lemma next_step_neq_0_cases:
  "next_step s s' \<noteq> 0 \<longleftrightarrow>
    (s = Start \<longrightarrow> (\<exists>j. s' = Init j \<and> init j \<noteq> 0)) \<and>
    (s \<in> range Init \<longrightarrow> s' \<in> range Mix) \<and>
    (s \<in> range Mix \<longrightarrow> s' = End \<or> s' \<in> range Mix) \<and>
    (s = End \<longrightarrow> s' = End)"
  using p_f jondos_non_empty
  by (cases s) (auto split: state.split simp: J_def)

lemma next_step_from_End[simp]: "next_step End s = 0 \<longleftrightarrow> s \<noteq> End"
  by (cases s) auto

lemma next_step_Mix_MixI: "\<exists>j. s = Mix j \<Longrightarrow> \<exists>j. s' = Mix j \<Longrightarrow> next_step s s' = p_f * J"
  by (cases s) auto

end

subsection {* The Crowds-Protocol forms a DTMC *}

sublocale Crowds_Protocol \<subseteq> Discrete_Time_Markov_Chain valid_states next_step Start
proof
  show "finite valid_states" "Start \<in> valid_states"
    by (auto simp: valid_states_def)
next
  fix s s' assume "s \<in> valid_states" "s' \<in> valid_states" then show "0 \<le> next_step s s'"
    using p_f init_nonneg
    by (auto simp: valid_states_def J_def intro!: divide_nonneg_nonneg)
next
  fix s assume "s \<in> valid_states" then show "(\<Sum>s'\<in>valid_states. next_step s s') = 1"
    using p_f jondos_non_empty init_distr colls_smaller
    by (simp add: setsum_diff real_eq_of_nat[symmetric] J_def
             split: split_if_asm state.split)
qed

context Crowds_Protocol
begin

abbreviation
  "\<P> \<equiv> path_space Start"

text {*

What is the probability that the server sees a specific (including the initiator) as sender.

*}

definition "len \<omega> = (LEAST n :: nat. \<omega> n = End) - 2"
definition "first_jondo \<omega> = jondo_of (\<omega> 0)"
definition "last_jondo \<omega> = jondo_of (\<omega> (Suc (len \<omega>)))"

definition "term \<omega> \<longleftrightarrow>
  \<omega> \<in> space \<P> \<and>
  \<omega> 0 \<in> Init ` (jondos - colls) \<and>
  (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` jondos) \<and>
  (\<forall>i>len \<omega>. \<omega> (Suc i) = End)"

lemma term_imp_len:
  assumes "term \<omega>"
  shows "i \<le> len \<omega> \<Longrightarrow> \<omega> (Suc i) \<in> Mix ` jondos"
    and "\<omega> 0 \<in> Init ` (jondos - colls)"
    and "i > len \<omega> \<Longrightarrow> \<omega> (Suc i) = End"
  using assms by (auto simp: term_def)

lemma len_eq:
  "term \<omega> \<Longrightarrow> \<omega> (Suc n) = Mix j \<Longrightarrow> \<omega> (Suc (Suc n)) = End \<Longrightarrow> len \<omega> = n"
  by (rule ccontr) (auto simp add: term_def neq_iff intro: Suc_leI)

lemma le_lenI[intro]:
  "term \<omega> \<Longrightarrow> \<omega> (Suc i) \<noteq> End \<Longrightarrow> i \<le> len \<omega>"
  unfolding term_def by (rule ccontr) auto

lemma last_jondo_eq_iff:
  assumes "term \<omega>"
  shows "last_jondo \<omega> = j \<longleftrightarrow> \<omega> (Suc (len \<omega>)) = Mix j"
  unfolding last_jondo_def using `term \<omega>`
  by (auto simp: term_def)

lemma AE_terminating: "AE \<omega> in \<P>. \<exists>n. \<omega> n = End"
proof -
  from possible_jondo guess j . note j = this
  then have End_reachable_Start: "End \<in> reachable (valid_states - {End}) Start"
    unfolding reachable_def next_step_neq_0_cases
    by (auto intro!: exI[of _ "nat_case (Init j) (nat_case (Mix j) (\<lambda>i. End))"] exI[of _ 2]
             split: nat.split nat.split_asm)

  have "AE \<omega> in \<P>. nat_case Start \<omega> \<in> until valid_states {End}"
  proof (subst until_eq_1_if_reachable, safe)
    fix s assume *: "reachable (valid_states - {End}) s \<inter> {End} = {}"
    assume "s \<in> reachable (valid_states - {End}) Start"
    then have s: "s \<in> valid_states" by (auto simp: reachable_def)
    show False
    proof (cases rule: valid_statesE[OF s])
      case 1 with End_reachable_Start * show False by auto
    next
      case 2 with * show False by (force simp: reachable_def next_step_neq_0_cases)
    next
      case (3 j) with * show False
        by (force simp: reachable_def next_step_neq_0_cases)
    next
      case (4 i)
      moreover from j have "End \<in> reachable (valid_states - {End}) (Init i)"
        unfolding reachable_def next_step_neq_0_cases
        by (auto intro!: exI[of _ "nat_case (Mix j) (\<lambda>i. End)"] exI[of _ 1]
                 split: nat.split nat.split_asm)
      ultimately show False
        using * by auto
    qed
  next
    assume "reachable (valid_states - {End}) Start \<inter> {End} = {}"
    with End_reachable_Start show False by auto
  qed (auto simp: reachable_def next_step_neq_0_cases)
  then show ?thesis
    by (elim AE_mp)
       (auto simp: until_def intro!: AE_I2 split: nat.split_asm)
qed

subsection {* A Crowds-Protocol run terminates almost surely *}

lemma AE_term: "AE \<omega> in \<P>. term \<omega>"
  using AE_terminating AE_\<tau>_not_zero[OF Start_valid_state]
  unfolding term_def
proof (elim AE_mp, safe intro!: AE_I2)
  fix \<omega> n assume \<omega>: "\<omega> \<in> space \<P>" and "\<omega> n = End"
    and not_zero: "\<forall>i. next_step (nat_case Start \<omega> i) (\<omega> i) \<noteq> 0"
  from not_zero[THEN spec, of 0] not_zero[THEN spec, of 1]
  have "\<omega> 0 \<in> range Init" "\<omega> 1 \<in> range Mix"
    by (auto simp: next_step_neq_0_cases split: state.split_asm)
  moreover have \<omega>: "\<forall>i. \<omega> i \<in> valid_states"
    using \<omega> by (auto simp: space_path_space Pi_iff)
  ultimately have \<omega>0: "\<omega> 0 \<in> Init`(jondos - colls)" and \<omega>1: "\<omega> 1 \<in> Mix`jondos"
    apply (simp_all add: valid_states_def image_iff)
    apply (metis state.simps(4,10,12))
    apply (metis state.simps(2,6,10,14))
    done

  show "\<omega> 0 \<in> Init`(jondos - colls)" by fact

  from `\<omega> n = End` have len:
    "\<omega> (Suc (Suc (len \<omega>))) = End \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<noteq> End)"
    unfolding len_def
  proof (rule LeastI2_wellorder)
    fix i assume "\<omega> i = End" "\<forall>j. \<omega> j = End \<longrightarrow> i \<le> j"
    moreover
    then have "i \<noteq> 0 \<and> i \<noteq> 1"
      using \<omega>0 \<omega>1 by (intro notI conjI) auto
    then have "2 \<le> i"
      by simp
    then have "Suc (Suc (i - 2)) = i"
      by simp
    ultimately show "\<omega> (Suc (Suc (i - 2))) = End \<and> (\<forall>j\<le>i - 2. \<omega> (Suc j) \<noteq> End)"
      by auto
  qed

  { fix i assume "len \<omega> < i"
    with not_zero len show "\<omega> (Suc i) = End"
      by (induct i)
         (auto simp: less_Suc_eq next_step_neq_0_cases) }
  note tail = this

  { fix i assume "i \<le> len \<omega>"
    then show "\<omega> (Suc i) \<in> Mix ` jondos"
    proof (induct i)
      case (Suc n)
      moreover then obtain j where "\<omega> (Suc n) = Mix j" "j \<in> jondos" by auto
      moreover note not_zero[THEN spec, of "Suc (Suc n)"] len p_f \<omega>[THEN spec, of "Suc (Suc n)"]
      ultimately show ?case
        by (simp split: state.split_asm)
    qed (insert \<omega>1, simp) }
qed

lemma sets_Collect_len[intro]: "{\<omega>\<in>space (path_space s). len \<omega> = n} \<in> events s"
  unfolding len_def
  by (rule sets_Collect_Least) (auto intro: sets_Collect_const)

lemma sets_Collect_lenI[intro]:
  "(\<And>n. {\<omega>\<in>space (path_space s). P \<omega> n} \<in> events s) \<Longrightarrow> {\<omega>\<in>space (path_space s). P \<omega> (len \<omega>)} \<in> events s"
  unfolding len_def
  by (rule sets_Collect_Least) auto

lemma jondo_events2:
  assumes "\<And>s. s \<in> valid_states \<Longrightarrow> {\<omega> \<in> space \<P>. P \<omega> (jondo_of s)} \<in> sets \<P>"
  shows "{\<omega> \<in> space \<P>. P \<omega> (jondo_of (\<omega> i))} \<in> sets \<P>"
proof -
  have *: "{\<omega> \<in> space \<P>. P \<omega> (jondo_of (\<omega> i))} = {\<omega> \<in> space \<P>. \<exists>s\<in>valid_states. \<omega> i = s \<and> P \<omega> (jondo_of s)}"
    by (auto simp: space_path_space)
  show ?thesis unfolding *
    by (rule sets_Collect_finite_Ex) (auto intro!: sets_Collect assms)
qed

lemma jondo_events[intro]:
  "{\<omega> \<in> space \<P>. P (jondo_of (\<omega> i))} \<in> sets \<P>"
  by (rule jondo_events2) (auto intro!: sets_Collect_const)

lemma sets_Collect_last_jondo[intro]: "{\<omega>\<in>space \<P>. last_jondo \<omega> = j} \<in> events Start"
  unfolding last_jondo_def
  by (rule sets_Collect_lenI) auto

lemma prob_sums_len:
  assumes P: "\<And>n. {\<omega>\<in>space \<P>. P \<omega>} \<in> events Start"
  shows "(\<lambda>n. \<PP>(\<omega> in \<P>. len \<omega> = n \<and> P \<omega>)) sums \<PP>(\<omega> in \<P>. P \<omega>)"
  using AE_term
  by (intro prob_sums) (auto intro: P sets_Collect_conj)

lemma prob_sums_cyl_init:
  assumes S: "\<And>n i. S n i \<subseteq> jondos" and I: "I \<subseteq> jondos - colls"
  shows "(\<lambda>n. (\<Sum>j\<in>I. init j)* (\<Prod>i\<le>n. card (S n i) * J) * (p_f)^n * (1 - p_f)) sums
    \<PP>(\<omega> in \<P>. \<omega> 0 \<in> Init ` I \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` S (len \<omega>) i))"
proof -
  have S_valid: "\<And>n i. Mix ` S n i \<subseteq> valid_states"
    using S by auto
  have S_finite: "\<And>n i. finite (S n i)"
    using S finite_jondos by (blast dest: finite_subset)

  have I_valid: "Init ` I \<subseteq> valid_states"
    using I by auto
  have I_finite: "finite I"
    using I by (auto dest: finite_subset)

  let "?S n i" = "case i of 0 \<Rightarrow> Init ` I | Suc i \<Rightarrow> Mix ` S n i"
  let "?P n" = "\<PP>(\<omega> in \<P>. len \<omega> = n \<and> (\<forall>i\<le>Suc (len \<omega>). \<omega> i \<in> ?S (len \<omega>) i))"
  { fix n
    def T \<equiv> "\<lambda>i. nat_case (Init`I) (\<lambda>j. if j \<le> n then Mix ` S n j else {End}) i"
    with S[of n] I have valid_T: "\<And>i. T i \<subseteq> valid_states"
      by (auto simp: valid_states_def inj_image_mem_iff subset_eq split: nat.split)

    have T: "T (Suc (Suc n)) = {End}" "T 0 = Init ` I"
      "Pi\<^isub>E (Suc ` {.. n}) T = (\<Pi>\<^isub>E i\<in>{1..Suc n}. Mix ` S n (i - 1))"
      by (auto simp add: T_def Suc_le_eq gr0_conv_Suc split: nat.split nat.split_asm intro!: PiE_cong)

    have upto: "{.. Suc (Suc n)} = insert 0 (insert (Suc (Suc n)) (Suc ` {..n}))"
      by (metis atMost_Suc atMost_Suc_eq_insert_0 image_insert)

    have *:
      "finite (Suc ` {..n})"
      "Suc (Suc n) \<notin> Suc ` {..n}"
      by auto

    have "?P n = \<PP>(\<omega> in \<P>. \<forall>i\<in>{..Suc (Suc n)}. \<omega> i \<in> T i)"
      using AE_term
    proof (intro prob_eq_AE, elim AE_mp, intro AE_I2 impI iffI conjI ballI allI)
      fix \<omega> assume "term \<omega>"
      { fix i assume "len \<omega> = n \<and> (\<forall>i\<le>Suc (len \<omega>). \<omega> i \<in> ?S (len \<omega>) i)" "i \<in> {..Suc (Suc n)}"
        then show "\<omega> i \<in> T i"
          using `term \<omega>` term_imp_len[of \<omega>] by (auto simp: T_def split: nat.split) }
      assume T: "\<forall>i\<in>{..Suc (Suc n)}. \<omega> i \<in> T i"
      from `term \<omega>` this[THEN bspec, of "Suc n"] this[THEN bspec, of "Suc (Suc n)"] S[of n n]
      show "len \<omega> = n"
        by (auto intro: len_eq simp: T_def)
      { fix i assume "i \<le> Suc (len \<omega>)" then show "\<omega> i \<in> ?S (len \<omega>) i"
          using T[THEN bspec, of i] S[of "len \<omega>" "i - 1"] `len \<omega> = n`
          by (auto split: nat.split simp: T_def) }
    qed (auto intro!: sets_Collect simp: Ball_def)
    also have "\<dots> = (\<Sum>\<omega>\<in>(\<Pi>\<^isub>E i\<in>{..Suc (Suc n)}. T i).
        (\<Prod>i\<le>Suc (Suc n). next_step (nat_case Start \<omega> i) (\<omega> i)))"
      using valid_T by (auto intro!: setsum_cong PiE_cong simp add: prob_ball_cylinder subset_eq)
    also have "\<dots> = (\<Sum>s\<in>I. \<Sum>\<omega>\<in>(\<Pi>\<^isub>E i\<in>{1..Suc n}. Mix ` S n (i - 1)).
        init s * (\<Prod>i\<le>n. next_step (if i = 0 then Init s else \<omega> i) (\<omega> (Suc i))) * next_step (\<omega> (Suc n)) End)"
      by (simp add: upto T setsum_PiE_insert[OF *(2)] setprod_insert[OF *] zero_notin_Suc_image
                    setsum_PiE_insert setprod_reindex setsum_reindex mult_ac
               cong: if_cong)
    also have "\<dots> = (\<Sum>s\<in>I. \<Sum>\<omega>\<in>(\<Pi>\<^isub>E i\<in>{1..Suc n}. Mix ` S n (i - 1)).
        init s * (\<Prod>i\<le>n. if i = 0 then J else p_f * J) * (1 - p_f))"
      apply (intro setsum_cong arg_cong2[where f="op *"] setprod_cong refl)
      apply (auto simp add: Pi_iff Ball_def image_iff gr0_conv_Suc
                  split: state.split intro!: next_step_Mix_MixI)
      apply (metis Nat.diff_le_self Suc_le_lessD Suc_pred diff_is_0_eq le_trans not_less_eq_eq)
      done
    also have "\<dots> = (\<Sum>s\<in>I. init s) * (\<Prod>i\<in>{Suc 0..Suc n}. card (S n (i - 1))) * J * (p_f * J)^n * (1 - p_f)"
      by (simp add: setsum_left_distrib[symmetric] setsum_right_distrib[symmetric] zero_notin_Suc_image
                    lessThan_Suc_atMost[symmetric] lessThan_Suc_eq_insert_0 setprod_reindex
                    card_PiE S_finite real_eq_of_nat card_image setprod_constant)
    finally have "?P n = (\<Sum>s\<in>I. init s) * (\<Prod>i\<le>n. card (S n i) * J) * p_f^n * (1 - p_f)"
      by (simp add: image_Suc_atLeastAtMost[symmetric] setprod_reindex atLeast0AtMost
                    setprod_timesf setprod_constant power_mult_distrib
               del: image_Suc_atLeastAtMost) }
  moreover have "?P sums \<PP>(\<omega> in \<P>. (\<forall>i\<le>Suc (len \<omega>). \<omega> i \<in> ?S (len \<omega>) i))"
    by (intro prob_sums_len) (auto intro!: sets_Collect)
  moreover have "\<PP>(\<omega> in \<P>. (\<forall>i\<le>Suc (len \<omega>). \<omega> i \<in> ?S (len \<omega>) i)) =
    \<PP>(\<omega> in \<P>. \<omega> 0 \<in> Init ` I \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` S (len \<omega>) i))"
    by (simp add: all_Suc_split conj_commute)
  ultimately show ?thesis
    by simp
qed

lemma prob_sums_cyl:
  assumes S: "\<And>n i. S n i \<subseteq> jondos"
  shows "(\<lambda>n. (\<Prod>i\<le>n. card (S n i) * J) * (p_f)^n * (1 - p_f)) sums
    \<PP>(\<omega> in \<P>. (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` S (len \<omega>) i))"
proof -
  have "\<PP>(\<omega> in \<P>. (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` S (len \<omega>) i)) =
    \<PP>(\<omega> in \<P>. \<omega> 0 \<in> Init ` (jondos - colls) \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` S (len \<omega>) i))"
    using AE_term
    by (intro prob_eq_AE, elim AE_mp) (auto simp add: term_def intro!: sets_Collect)
  with prob_sums_cyl_init[of S, OF S subset_refl]
  show ?thesis
    by simp
qed

lemma (in prob_space) prob_setsum:
  assumes [simp, intro]: "finite I"
  assumes P: "\<And>n. n \<in> I \<Longrightarrow> {x\<in>space M. P n x} \<in> events"
  assumes Q: "{x\<in>space M. Q x} \<in> events"
  assumes ae: "AE x. (\<forall>n\<in>I. P n x \<longrightarrow> Q x) \<and> (Q x \<longrightarrow> (\<exists>!n\<in>I. P n x))"
  shows "\<PP>(x in M. Q x) = (\<Sum>n\<in>I. \<PP>(x in M. P n x))"
proof -
  from ae[THEN AE_E_prob] guess S . note S = this
  then have disj: "disjoint_family_on (\<lambda>n. {x\<in>space M. P n x} \<inter> S) I"
    by (auto simp: disjoint_family_on_def)
  from S have ae_S:
    "AE x. x \<in> {x\<in>space M. Q x} \<longleftrightarrow> x \<in> (\<Union>n\<in>I. {x\<in>space M. P n x} \<inter> S)"
    "\<And>n. n \<in> I \<Longrightarrow> AE x. x \<in> {x\<in>space M. P n x} \<longleftrightarrow> x \<in> {x\<in>space M. P n x} \<inter> S"
    using ae by (auto dest!: AE_prob_1)
  from ae_S have *:
    "\<PP>(x in M. Q x) = prob (\<Union>n\<in>I. {x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) (auto intro!: Int)
  from ae_S have **:
    "\<And>n. n \<in> I \<Longrightarrow> \<PP>(x in M. P n x) = prob ({x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) auto
  show ?thesis
    using S P disj
    by (auto simp add: * ** simp del: UN_simps intro!: finite_measure_finite_Union)
qed

subsection {* Server gets no information *}

lemma server_view:
  shows "\<PP>(\<omega> in \<P>. last_jondo \<omega> = first_jondo \<omega>) = J"
proof -
  let "?P j" = "\<PP>(\<omega> in \<P>. \<omega> 0 = Init j \<and> last_jondo \<omega> = j)"

  have [simp]: "{\<omega> \<in> space \<P>. last_jondo \<omega> = first_jondo \<omega>} \<in> events Start"
    unfolding last_jondo_def first_jondo_def
    apply (rule sets_Collect_lenI)
    apply (rule jondo_events2)
    apply (rule jondo_events)
    done

  have "\<PP>(\<omega> in \<P>. last_jondo \<omega> = first_jondo \<omega>) = (\<Sum>j\<in>jondos-colls. ?P j)"
  proof (rule prob_setsum)
    show "AE \<omega> in \<P>. (\<forall>j\<in>jondos - colls. \<omega> 0 = Init j \<and> last_jondo \<omega> = j \<longrightarrow> last_jondo \<omega> = first_jondo \<omega>) \<and>
               (last_jondo \<omega> = first_jondo \<omega> \<longrightarrow> (\<exists>!j. j \<in> jondos - colls \<and> \<omega> 0 = Init j \<and> last_jondo \<omega> = j))"
      using AE_term
      by (elim AE_mp)
         (auto simp: last_jondo_eq_iff first_jondo_def intro!: AE_I2 dest: term_imp_len)
  qed (auto intro!: sets_Collect)
  moreover
  { fix j assume j: "j \<in> jondos - colls"
    let "?S n i" = "if n = (i::nat) then {j} else jondos"
    have "?P j = \<PP>(\<omega> in \<P>. \<omega> 0 \<in> Init ` {j} \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` ?S (len \<omega>) i))"
      using AE_term
      by (auto simp: all_conj_distrib iff_conv_conj_imp last_jondo_eq_iff term_imp_len
               intro!: sets_Collect prob_eq_AE)
    moreover have "(\<lambda>n. (\<Sum>j\<in>{j}. init j) * (\<Prod>i\<le>n. card (?S n i) * J) * (p_f)^n * (1 - p_f)) sums \<dots>"
      using j by (intro prob_sums_cyl_init) auto
    moreover have "(\<lambda>n. init j * p_f ^ n * (1 - p_f) * J) sums (init j * (1 / (1 - p_f)) * (1 - p_f) * J)"
      using p_f by (intro sums_mult sums_mult2 geometric_sums) auto
    ultimately have "?P j = init j * J"
      using jondos_non_empty p_f
      by (simp add: lessThan_Suc_atMost[symmetric] lessThan_Suc setprod_constant sums_iff J_def) }
  ultimately
  show ?thesis
    by (simp add: setsum_left_distrib[symmetric])
qed

definition "hit_colls \<omega> \<longleftrightarrow> (\<exists>n::nat. \<omega> n \<in> Mix ` colls)"
definition "first_coll \<omega> = (LEAST n::nat. \<omega> n \<in> Mix ` colls) - 1"
definition "last_ncoll \<omega> = jondo_of (\<omega> (first_coll \<omega>))"

lemma hit_colls_eq:
  assumes "term \<omega>"
  shows "hit_colls \<omega> \<longleftrightarrow> (\<exists>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` colls)"
proof
  assume "hit_colls \<omega>"
then guess n unfolding hit_colls_def .. note n = this
  with `term \<omega>` have "n \<noteq> 0"
    by (intro notI) (auto simp add: term_def)
  with `term \<omega>` n show "\<exists>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` colls"
    by (intro exI[of _ "n - 1"])
       (auto simp: term_def gr0_conv_Suc)
qed (auto simp: hit_colls_def)

lemma first_collI2: "\<And>\<omega> i. i < first_coll \<omega> \<Longrightarrow> \<omega> (Suc i) \<notin> Mix`colls"
  by (simp add: first_coll_def less_diff_conv) (rule not_less_Least)

lemma first_collI:
  assumes "term \<omega>" and h: "hit_colls \<omega>"
  shows "\<omega> (Suc (first_coll \<omega>)) \<in> Mix ` colls"
  using h unfolding first_coll_def hit_colls_def
proof (rule LeastI2_ex)
  fix i assume "\<omega> i \<in> Mix ` colls"
  moreover with `term \<omega>` have "i \<noteq> 0"
    by (intro notI) (auto simp add: term_def)
  ultimately show "\<omega> (Suc (i - 1)) \<in> Mix ` colls"
    by auto
qed

lemma first_coll_le_len[intro]:
  assumes [intro]: "term \<omega>" and "hit_colls \<omega>"
  shows "first_coll \<omega> \<le> len \<omega>"
proof -
  from assms obtain n
    where n: "n \<le> len \<omega>" "\<omega> (Suc n) \<in> Mix ` colls"
    by (auto simp: hit_colls_eq)
  from this(2) show ?thesis
    unfolding first_coll_def
    apply (rule LeastI2_wellorder)
    apply (insert n)
    apply auto
    done
qed

lemma first_collI3:
  assumes "term \<omega>" "hit_colls \<omega>" "i < first_coll \<omega>"
  shows "\<omega> (Suc i) \<in> Mix`(jondos - colls)"
  using first_coll_le_len[OF `term \<omega>` `hit_colls \<omega>`] `i < first_coll \<omega>`
    first_collI2[OF `i < first_coll \<omega>`] term_imp_len(1)[OF `term \<omega>`, of i]
  by auto

lemma first_collI4: "term \<omega> \<Longrightarrow> hit_colls \<omega> \<Longrightarrow> last_ncoll \<omega> \<in> jondos - colls"
  using first_collI3[of \<omega> "first_coll \<omega> - 1"]
  by (cases "first_coll \<omega>") (auto simp: last_ncoll_def dest!: term_imp_len)

lemma events_hit_colls[intro]:
  "{\<omega>\<in>space \<P>. hit_colls \<omega>} \<in> events Start"
  by (auto simp: hit_colls_def intro!: sets_Collect)

lemma events_first_collI:
  "(\<And>n. {\<omega>\<in>space \<P>. P n \<omega>} \<in> events Start) \<Longrightarrow>
    {\<omega>\<in>space \<P>. P (first_coll \<omega>) \<omega>} \<in> events Start"
  using assms unfolding first_coll_def
  by (rule sets_Collect_Least) (auto intro!: sets_Collect)

lemma events_first_coll[intro]:
  "{\<omega>\<in>space \<P>. first_coll \<omega> = n} \<in> events Start"
  by (rule events_first_collI) (auto intro: sets_Collect)

lemma events_last_ncoll[intro]:
  "{\<omega>\<in>space \<P>. last_ncoll \<omega> = j} \<in> events Start"
  unfolding last_ncoll_def
proof (rule events_first_collI)
  case (goal1 n)
  have *: "{\<omega> \<in> space \<P>. jondo_of (\<omega> n) = j} =
    {\<omega> \<in> space \<P>. \<exists>s\<in>valid_states. \<omega> n = s \<and> jondo_of s = j}"
    by (auto simp: space_path_space)
  show ?case unfolding *
    apply (rule sets_Collect_finite_Ex)
    apply (auto intro: sets_Collect)
    done
qed

subsection {* The probability to hit a collaborateur *}

lemma hit: "\<PP>(\<omega> in \<P>. hit_colls \<omega>) = (1 - H) / (1 - H * p_f)"
  (is "?HIT = _")
proof -
  have "p_f * H \<noteq> 1"
    using H_pf_1 by (simp add: ac_simps)
  have "?HIT = 1 - \<PP>(\<omega> in \<P>. \<not> hit_colls \<omega>)"
    by (simp add: prob_neg events_hit_colls)
  moreover have "\<PP>(\<omega> in \<P>. \<not> hit_colls \<omega>) =
    \<PP>(\<omega> in \<P>. \<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` (jondos - colls))"
    using AE_term colls_smaller
    by (intro prob_eq_AE, elim AE_mp)
       (auto simp add: hit_colls_eq image_set_diff term_imp_len intro!: AE_I2 sets_Collect)
  moreover have "(\<lambda>n. (\<Prod>i\<le>n. card (jondos - colls) * J) * p_f^n * (1 - p_f)) sums \<dots>"
    by (rule prob_sums_cyl) auto
  moreover have "\<And>n. (\<Prod>i\<le>n. card (jondos - colls) * J) * p_f^n * (1 - p_f) =
    (H * p_f)^n * (H * (1 - p_f))"
    by (simp add: setprod_constant power_divide power_mult_distrib field_simps H_def J_def)
  moreover have "\<dots> sums (1 / (1 - H * p_f) * (H * (1 - p_f)))"
    using H_pf_0 H_pf_1
    by (intro sums_mult2 sums_divide geometric_sums) simp
  ultimately have "?HIT = 1 - (H * (1 - p_f) / (1 - H * p_f))"
    by (simp add: sums_iff)
  also have "\<dots> = (1 - H) / (1 - H * p_f)"
    by (simp add: field_simps diff_divide_distrib eq_divide_eq) fact
  finally show ?thesis .
qed

lemma hit_prob_sums_cyl:
  assumes S: "\<And>n i. S n i \<subseteq> jondos - colls" and I: "\<And>n. I n \<subseteq> jondos - colls"
  shows "(\<lambda>n. (\<Sum>j\<in>I n. init j) * (\<Prod>i<n. card (S n i) * J * p_f) * (1 - H * p_f)) sums
    \<PP>(\<omega> in \<P>. \<omega> 0 \<in> Init ` I (first_coll \<omega>) \<and> (\<forall>i<first_coll \<omega>. \<omega> (Suc i) \<in> Mix ` S (first_coll \<omega>) i) \<bar> hit_colls \<omega>)"
proof -
  have "(\<lambda>n. \<PP>(\<omega> in \<P>. first_coll \<omega> = n \<and> \<omega> 0 \<in> Init ` (I n) \<and> (\<forall>i<n. \<omega> (Suc i) \<in> Mix ` S n i) \<and> hit_colls \<omega>))
    sums \<PP>(\<omega> in \<P>. \<omega> 0 \<in> Init ` (I (first_coll \<omega>)) \<and>
                   (\<forall>i<first_coll \<omega>. \<omega> (Suc i) \<in> Mix ` S (first_coll \<omega>) i) \<and> hit_colls \<omega>)"
    (is "?P sums ?C")
    by (rule prob_sums) (auto intro!: sets_Collect intro: events_first_collI)
  moreover
  { fix n :: nat
    def T \<equiv> "\<lambda>l i. if l < n     then {}
              else if i < n     then S n i
              else if i = n     then colls
                                else jondos"

    have cards: "\<And>l. n \<le> l \<Longrightarrow> {..l} \<inter> - {x. x < n} \<inter> - {n} = {n<..l}"
        "\<And>l. n \<le> l \<Longrightarrow> {..l} \<inter> {x. x < n} = {..< n}"
      by auto

    have "?P n = \<PP>(\<omega> in \<P>. \<omega> 0 \<in> Init ` (I n) \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` T (len \<omega>) i))"
      using AE_term
    proof (intro prob_eq_AE, elim AE_mp, intro AE_I2 impI allI conjI iffI)
      fix \<omega> i assume "term \<omega>" "i \<le> len \<omega>"
        and coll: "first_coll \<omega> = n \<and> \<omega> 0 \<in> Init ` (I n) \<and> (\<forall>i<n. \<omega> (Suc i) \<in> Mix ` S n i) \<and> hit_colls \<omega>"
      then show "\<omega> (Suc i) \<in> Mix ` T (len \<omega>) i"
        by (auto simp: T_def not_le[symmetric] intro: first_collI first_coll_le_len term_imp_len)
    next
      fix \<omega> assume "\<omega> 0 \<in> Init ` (I n) \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` T (len \<omega>) i)" and "term \<omega>"
      then have "n \<le> len \<omega>" and T: "\<And>i. i \<le> len \<omega> \<Longrightarrow> \<omega> (Suc i) \<in> Mix ` T (len \<omega>) i"
        by (auto simp add: T_def not_less[symmetric])
      with T[of n] show "hit_colls \<omega>"
        by (auto simp add: T_def hit_colls_def)
      { fix i assume "i < n" then show "\<omega> (Suc i) \<in> Mix ` S n i"
          using T[of i] `n \<le> len \<omega>` by (auto simp: T_def) }
      have "\<omega> (Suc n) \<in> Mix ` colls"
        using T[of n] `n \<le> len \<omega>`
        by (auto simp: T_def)
      with first_collI2[of n \<omega>] have "first_coll \<omega> \<le> n"
        by (metis not_less)
      moreover have "n \<le> first_coll \<omega>"
        using T[of "first_coll \<omega>"] S[of n "first_coll \<omega>"]
        using first_collI[OF `term \<omega>` `hit_colls \<omega>`] `n \<le> len \<omega>`
        by (auto simp: not_less[symmetric] T_def split: split_if_asm)
      ultimately show "first_coll \<omega> = n" by simp
    qed (auto intro!: sets_Collect)
    moreover have "(\<lambda>l. (\<Sum>i\<in>I n. init i) * (\<Prod>i\<le>l. card (T l i) * J) * (p_f)^l * (1 - p_f)) sums \<dots>"
      using I[of n] S colls_non_empty colls_smaller by (intro prob_sums_cyl_init) (auto simp: T_def)
    moreover have "\<And>l. (\<Sum>i\<in>I n. init i) * (\<Prod>i\<le>l. card (T l i) * J) * (p_f)^l * (1 - p_f) =
      (if n \<le> l then (\<Sum>i\<in>I n. init i) * (1 - H) * p_f^l * (1 - p_f) * (\<Prod>i<n. card (S n i) * J) else 0)"
      (is "\<And>l. _ = (if n \<le> l then ?p l else 0)")
      using jondos_non_empty p_f colls_smaller unfolding H_compl
      by (simp add: J_def T_def H_def setprod_dividef fun_if_distrib setprod.If_cases
                    setprod_constant power_divide power_mult_distrib power_diff eq_divide_eq cards)
    ultimately have "(\<lambda>l. if n \<le> l then ?p l else 0) sums ?P n"
      by simp
    from sums_split_initial_segment[OF this, of n]
    have "(\<lambda>l. ?p (l + n)) sums ?P n" by simp
    moreover have "(\<lambda>l. ?p (l + n)) sums ((\<Sum>i\<in>I n. init i) * (1 - H) * (1 / (1 - p_f) * p_f ^ n) *
      (1 - p_f) * (\<Prod>i<n. card (S n i) * J))"
      unfolding power_add using p_f
      by (intro sums_mult sums_mult2 geometric_sums) simp
    ultimately have "?P n = (\<Sum>i\<in>I n. init i) * (1 - H) * (\<Prod>i<n. card (S n i) * J * p_f)"
      using p_f jondos_non_empty H by (simp add: sums_iff power_mult_distrib setprod_timesf setprod_constant) }
  ultimately have "(\<lambda>n. (\<Sum>i\<in>I n. init i) * (1 - H) * (\<Prod>i<n. card (S n i) * J * p_f)) sums ?C"
    by simp
  then have "(\<lambda>n. (\<Sum>i\<in>I n. init i) * (1 - H) * (\<Prod>i<n. card (S n i) * J * p_f) / ((1 - H) / (1 - H * p_f))) sums
    \<PP>(\<omega> in \<P>. \<omega> 0 \<in> Init ` I (first_coll \<omega>) \<and> (\<forall>i<first_coll \<omega>. \<omega> (Suc i) \<in> Mix ` S (first_coll \<omega>) i) \<bar> hit_colls \<omega>)"
    unfolding cond_prob_def hit by (simp only: conj_ac) (rule sums_divide)
  with H show ?thesis
    by (simp add: mult_ac)
qed

subsection {* The probability that the sender hits a collaborateur *}

lemma P_first_jondo_last_ncoll:
  assumes l: "l \<in> jondos - colls" and i: "i \<in> jondos - colls"
  shows "\<PP>(\<omega> in \<P>. first_jondo \<omega> = i \<and> last_ncoll \<omega> = l \<bar> hit_colls \<omega> ) =
    init i * (J * p_f + (if i = l then 1 - H * p_f else 0))"
  (is "?P = _")
proof -
  let "?S n k" = "if n = Suc k then {l} else jondos - colls"
  let "?I n" = "if (n::nat) = 0 then {i} \<inter> {l} else {i}"
  have [simp]: "\<And>n. {..<Suc n} \<inter> - {n} = {..<n}" by auto
  have "?P = \<PP>(\<omega> in \<P>. \<omega> 0 \<in> Init ` ?I (first_coll \<omega>) \<and>
        (\<forall>i<first_coll \<omega>. \<omega> (Suc i) \<in> Mix ` ?S (first_coll \<omega>) i) \<bar> hit_colls \<omega>)"
  proof (rule cond_prob_eq_AE)
    show "AE \<omega> in \<P>. hit_colls \<omega> \<longrightarrow>
      (first_jondo \<omega> = i \<and> last_ncoll \<omega> = l) =
      (\<omega> 0 \<in> Init ` ?I (first_coll \<omega>) \<and> (\<forall>i<first_coll \<omega>. \<omega> (Suc i) \<in> Mix ` ?S (first_coll \<omega>) i))"
      using AE_term
    proof (elim AE_mp, safe intro!: AE_I2)
      fix \<omega> assume \<omega>: "term \<omega>" "hit_colls \<omega>"
      then show "\<omega> 0 \<in> Init ` (if first_coll \<omega> = 0 then {first_jondo \<omega>} \<inter> {last_ncoll \<omega>} else {first_jondo \<omega>})"
        by (auto simp add: first_jondo_def last_ncoll_def term_def)
      fix i assume "i < first_coll \<omega>"
      then have "i \<le> len \<omega>" using first_coll_le_len[OF \<omega>] by simp
      from \<omega> first_collI2[OF `i < first_coll \<omega>`] term_imp_len(1)[OF \<omega>(1) this]
      show "\<omega> (Suc i) \<in> Mix ` (if first_coll \<omega> = Suc i then {last_ncoll \<omega>} else jondos - colls)"
        by (auto simp: image_set_diff last_ncoll_def)
    next
      fix \<omega> j assume j: "j \<in> (if first_coll \<omega> = 0 then {i} \<inter> {l} else {i})"
      then have [simp]: "j = i" by (cases "first_coll \<omega>") auto
      assume \<omega>: "term \<omega>" "hit_colls \<omega>" "\<omega> 0 = Init j"
      then show "first_jondo \<omega> = i"
        by (simp add: first_jondo_def)
      assume "\<forall>i<first_coll \<omega>. \<omega> (Suc i) \<in> Mix ` (if first_coll \<omega> = Suc i then {l} else jondos - colls)"
      with j \<omega> show "last_ncoll \<omega> = l"
        by (cases "first_coll \<omega>") (auto simp: last_ncoll_def)
    qed
  qed (auto simp: first_jondo_def split del: split_if
            intro!: sets_Collect intro: events_first_collI)
  also have "(\<lambda>n. (\<Sum>j\<in>?I n. init j) * (\<Prod>i<n. card (?S n i) * J * p_f) * (1 - H * p_f)) sums \<dots>"
    using i l by (intro hit_prob_sums_cyl) auto
  finally have "(\<lambda>n. (\<Sum>j\<in>?I n. init j) * (\<Prod>i<n. card (?S n i) * J * p_f) * (1 - H * p_f)) sums ?P" .
  from sums_split_initial_segment[OF this, of 1]
  have "(\<lambda>n. init i * (\<Prod>i<Suc n. if n = i then J * p_f else H * p_f) * (1 - H * p_f)) sums
    (?P - (if i = l then init i * (1 - H * p_f) else 0))"
    by (auto simp: fun_if_distrib H_def J_def cong: if_cong)
  moreover have "\<And>n. init i * (\<Prod>i<Suc n. if n = i then J * p_f else H * p_f) * (1 - H * p_f) =
    init i * J * p_f * (H*p_f)^n * (1 - H * p_f)"
    by (simp add: setprod.If_cases setprod_constant)
  moreover have "\<dots> sums (init i * J * p_f * (1 / (1 - H*p_f)) * (1 - H * p_f))"
    using H_pf_1 H_pf_0 by (intro sums_mult sums_mult2 geometric_sums) auto
  ultimately have "?P - (if i = l then init i * (1 - H * p_f) else 0) = init i * J * p_f"
    using H_pf_1 by (simp add: sums_iff)
  then show "?P = init i * (J * p_f + (if i = l then 1 - H * p_f else 0))"
    by (simp add: field_simps)
qed

lemma P_last_ncoll:
  assumes l: "l \<in> jondos - colls"
  shows "\<PP>(\<omega> in \<P>. last_ncoll \<omega> = l \<bar> hit_colls \<omega> ) = J * p_f + init l * (1 - H * p_f)"
proof -
  have "\<PP>(\<omega> in \<P>. last_ncoll \<omega> = l \<and> hit_colls \<omega>)
    = (\<Sum>i\<in>jondos - colls. \<PP>(\<omega> in \<P>. first_jondo \<omega> = i \<and> last_ncoll \<omega> = l \<and> hit_colls \<omega>))"
    apply (rule prob_setsum)
    using AE_term
    apply (auto intro!: sets_Collect simp: first_jondo_def)
    apply (auto intro!: AE_I2 simp: term_def)
    done
  then have "\<PP>(\<omega> in \<P>. last_ncoll \<omega> = l \<bar> hit_colls \<omega>)
    = (\<Sum>i\<in>jondos - colls. \<PP>(\<omega> in \<P>. first_jondo \<omega> = i \<and> last_ncoll \<omega> = l \<bar> hit_colls \<omega>))"
    unfolding cond_prob_def setsum_divide_distrib[symmetric] by simp
  also have "\<dots> = (\<Sum>i\<in>jondos - colls. init i * J * p_f + (if i = l then init i * (1 - H * p_f) else 0))"
    using l by (auto intro!: setsum_cong simp add: P_first_jondo_last_ncoll field_simps)
  also have "\<dots> = J * p_f + init l * (1 - H * p_f)"
    using l by (simp add: setsum_addf setsum_left_distrib[symmetric] setsum.If_cases)
  finally show ?thesis .
qed

lemma P_first_jondo:
  assumes i: "i \<in> jondos - colls"
  shows "\<PP>(\<omega> in \<P>. first_jondo \<omega> = i \<bar> hit_colls \<omega> ) = init i"
proof -
  have "\<PP>(\<omega> in \<P>. first_jondo \<omega> = i \<bar> hit_colls \<omega> ) =
    \<PP>(\<omega> in \<P>. \<omega> 0 \<in> Init ` {i} \<and> (\<forall>i<first_coll \<omega>. \<omega> (Suc i) \<in> Mix ` (jondos - colls)) \<bar> hit_colls \<omega>)"
    using AE_term i
    apply (intro cond_prob_eq_AE)
    apply (auto intro!: sets_Collect simp: first_jondo_def intro: events_first_collI)
    apply (auto intro!: AE_I2 dest: term_imp_len simp: first_collI3)
    done
  moreover have "(\<lambda>n. (\<Sum>j\<in>{i}. init j) * (\<Prod>i<n. card (jondos - colls) * J * p_f) * (1 - H * p_f)) sums \<dots>"
    using i by (intro hit_prob_sums_cyl) auto
  ultimately have "(\<lambda>n. init i * (H * p_f)^n * (1 - H * p_f)) sums \<PP>(\<omega> in \<P>. first_jondo \<omega> = i \<bar> hit_colls \<omega> )"
    by (simp add: sums_iff H_def J_def setprod_constant)
  moreover have "(\<lambda>n. init i * (H * p_f)^n * (1 - H * p_f)) sums (init i * (1/(1 - H*p_f)) * (1 - H*p_f))"
    using H_pf_0 H_pf_1 by (intro sums_mult sums_mult2 geometric_sums) simp
  ultimately show ?thesis
    using H_pf_1 by (simp add: sums_iff)
qed

subsection {* Probability space of hitting runs *}

definition  "C = \<P>\<lparr> measure := \<lambda>A. \<PP>(\<omega> in \<P>. \<omega> \<in> A \<bar> hit_colls \<omega>) \<rparr>"

end

lemma (in sigma_algebra) sets_in:
  "A \<inter> space M \<in> sets M \<Longrightarrow> {\<omega>\<in>space M. \<omega> \<in> A} \<in> sets M"
  unfolding Int_def by (simp add: conj_commute)

sublocale Crowds_Protocol \<subseteq> C!: information_space C 2
proof -
  interpret C!: sigma_algebra C
    unfolding C_def sigma_algebra_measure_update ..
  interpret C!: prob_space C
  proof
    show "positive C (measure C)"
      by (simp add: positive_def C_def cond_prob_def zero_le_divide_iff)
    show "countably_additive C (measure_space.measure C)"
    proof (simp add: countably_additive_def C_def, intro allI impI)
      fix A :: "nat \<Rightarrow> _" assume "range A \<subseteq> sets \<P>" "disjoint_family A"
      then have "(\<lambda>i. cond_prob \<P> (\<lambda>\<omega>. \<omega> \<in> A i) hit_colls) sums (cond_prob \<P> (\<lambda>\<omega>. \<exists>i. \<omega> \<in> A i) hit_colls)"
        unfolding cond_prob_def
        by (auto intro!: sums_divide prob_sums AE_I2 sets_Collect events_hit_colls sets_in simp: disjoint_family_on_def)
      then show "(\<Sum>i. ereal (cond_prob \<P> (\<lambda>\<omega>. \<omega> \<in> A i) hit_colls)) = cond_prob \<P> (\<lambda>\<omega>. \<exists>i. \<omega> \<in> A i) hit_colls"
        by (subst (asm) sums_ereal[symmetric]) (simp add: sums_iff)
    qed
    show "measure C (space C) = 1"
      using H_pf_1 H
      by (simp add: C_def one_ereal_def cond_prob_def hit)
  qed
  show "information_space C 2"
    by default simp
qed

context Crowds_Protocol
begin

abbreviation
  mutual_information_Pow_CP ("\<I>'(_ ; _')") where
  "\<I>(X ; Y) \<equiv> C.mutual_information 2
    \<lparr> space = X`space C, sets = Pow (X`space C), measure = ereal\<circ>C.distribution X \<rparr>
    \<lparr> space = Y`space C, sets = Pow (Y`space C), measure = ereal\<circ>C.distribution Y \<rparr> X Y"

lemma simple_functionI:
  assumes "finite (f`space \<P>)"
  assumes "\<And>x. {\<omega>\<in>space \<P>. f \<omega> = x} \<in> sets \<P>"
  shows "simple_function C f"
  using assms unfolding simple_function_def C_def by (simp add: vimage_def Int_def conj_commute)

subsection {* Estimate the information to the collaborateurs *}

lemma information_flow:
  defines "h \<equiv> real (card (jondos - colls))"
  assumes init_uniform: "\<And>i. i \<in> jondos - colls \<Longrightarrow> init i = 1 / card (jondos - colls)"
  shows "\<I>(first_jondo ; last_ncoll) \<le> (1 - (h - 1) * J * p_f) * log 2 h"
proof -
  let "?il i l" = "\<PP>(\<omega> in \<P>. first_jondo \<omega> = i \<and> last_ncoll \<omega> = l \<bar> hit_colls \<omega> )"
  let "?i i" = "\<PP>(\<omega> in \<P>. first_jondo \<omega> = i \<bar> hit_colls \<omega> )"
  let "?l l" = "\<PP>(\<omega> in \<P>. last_ncoll \<omega> = l \<bar> hit_colls \<omega> )"

  from init_uniform have init_H: "\<And>i. i \<in> jondos - colls \<Longrightarrow> init i = J / H"
    by (simp add: J_def H_def)

  from h_def have "1/h = J/H" "h = H / J" "H = h * J"
    by (auto simp: H_def J_def field_simps)
  from colls_smaller have h_pos: "0 < h"
    by (auto simp add: card_gt_0_iff h_def)

  let ?s = "(h - 1) * J"
  let ?f = "?s * p_f"

  from psubset_card_mono[OF _ colls_smaller]
  have "1 \<le> card jondos - card colls"
    by (simp del: colls_le_jondos)
  then have "1 \<le> h"
    using colls_smaller
    by (simp add: h_def card_Diff_subset real_of_nat_diff card_mono field_simps
             del: colls_le_jondos)

  have J_pos: "0 < J"
    unfolding J_def using colls_smaller by (auto simp add: card_gt_0_iff)

  have log_le_0: "?f * log 2 (H * p_f) \<le> ?f * log 2 1"
    using H_pf_1 H_pf_0 J_pos p_f `1 \<le> h`
    by (intro mult_left_mono log_le mult_nonneg_nonneg) auto

  have "(h - 1) * J < 1"
    using `1 \<le> h` colls_smaller
    by (auto simp: h_def J_def divide_less_eq card_Diff_subset real_of_nat_diff card_mono)
  then have 1: "(h - 1) * J * p_f < 1 * 1"
    using p_f by (intro mult_strict_mono) auto

  have sf_fj:
    "simple_function C first_jondo"
  proof (rule simple_functionI)
    have "first_jondo ` space \<P> \<subseteq> jondos \<union> {jondo_of Start, jondo_of End}"
      by (auto simp: first_jondo_def space_path_space Pi_iff elim!: allE[of _ 0] valid_statesE)
    then show "finite (first_jondo ` space \<P>)"
      by (rule finite_subset) auto
  qed (auto simp: first_jondo_def)

  have sf_lnc: "simple_function C last_ncoll"
  proof (rule simple_functionI)
    have "last_ncoll ` space \<P> \<subseteq> jondos \<union> {jondo_of Start, jondo_of End}"
      apply (auto simp: last_ncoll_def space_path_space Pi_iff)
      apply (erule_tac x="first_coll xa" in allE)
      apply (auto elim!: valid_statesE)
      done
    then show "finite (last_ncoll ` space \<P>)"
      by (rule finite_subset) auto
  qed auto

  let "?inner i" = "\<Sum>l\<in>jondos - colls. ?il i l * log 2 (?il i l / (?i i * ?l l))"
  { fix i assume i: "i \<in> jondos - colls"
    with h_pos have card_idx: "real_of_nat (card ((jondos - colls) - {i})) = H / J - 1"
      by (auto simp add: J_def H_def real_eq_of_nat[symmetric] h_def)

    have neq0: "J \<noteq> 0" "H \<noteq> 0"
      unfolding J_def H_def
      using colls_smaller i by auto

    from i have "?inner i =
      (\<Sum>l\<in>(jondos - colls) - {i}. ?il i l * log 2 (?il i l / (?i i * ?l l))) +
      ?il i i * log 2 (?il i i / (?i i * ?l i))"
      by (simp add: setsum_diff)
    also have "\<dots> =
      (\<Sum>l\<in>(jondos - colls) - {i}. J/H * J * p_f * log 2 (J * p_f / (J * p_f + J/H * (1 - H * p_f)))) +
      J/H * (J * p_f + (1 - H * p_f)) * log 2 ((J * p_f + (1 - H * p_f)) / (J * p_f + J/H * (1 - H * p_f)))"
      using i
      apply (auto simp add: P_first_jondo_last_ncoll P_first_jondo init_H P_last_ncoll simp del: setsum_constant)
      apply (intro setsum_cong)
      apply auto
      done
    also have "\<dots> = (?f * log 2 (h * J * p_f) + (1 - ?f) * log 2 ((1 - ?f) * h)) / h"
      using neq0 p_f by (simp add: card_idx field_simps `H = h * J`)
    finally have "?inner i = (?f * log 2 (h * J * p_f) + (1 - ?f) * log 2 ((1 - ?f) * h)) / h" . }
  then have "(\<Sum>i\<in>jondos - colls. ?inner i) = ?f * log 2 (h * J * p_f) + (1 - ?f) * log 2 ((1 - ?f) * h)"
    using h_pos by (simp add: h_def[symmetric] real_eq_of_nat[symmetric])
  also have "\<dots> = ?f * log 2 (H * p_f) + (1 - ?f) * log 2 ((1 - ?f) * h)"
    by (simp add: `h = H / J`)
  also have "\<dots> \<le> (1 - ?f) * log 2 ((1 - ?f) * h)"
    using log_le_0 by simp
  also have "\<dots> \<le> (1 - ?f) * log 2 h"
    using h_pos `1 \<le> h` 1 `0 < J` p_f
    by (intro mult_left_mono log_le mult_pos_pos mult_nonneg_nonneg)
       (auto simp: intro!: mult_nonneg_nonneg)
  finally have "(\<Sum>i\<in>jondos - colls. ?inner i) \<le> (1 - ?f) * log 2 h" .
  moreover have "\<I>(first_jondo ; last_ncoll) = (\<Sum>i\<in>jondos - colls. ?inner i)"
    unfolding setsum_cartesian_product C.mutual_information_eq[OF sf_fj sf_lnc]
  proof (safe intro!: setsum_mono_zero_cong_right del: DiffE)
    show "finite (first_jondo ` space C \<times> last_ncoll ` space C)"
      using sf_lnc sf_fj by (auto simp: simple_function_def)
  next
    fix j assume "j \<in> jondos - colls" then show "j \<in> first_jondo ` space C" "j \<in> last_ncoll ` space C"
      by (auto simp: image_iff C_def space_path_space last_ncoll_def first_jondo_def intro!: bexI[of _ "\<lambda>_. Mix j"])
  next
    fix i l assume "(i, l) \<in> first_jondo ` space C \<times> last_ncoll ` space C - (jondos - colls) \<times> (jondos - colls)"
    then have "i \<notin> jondos - colls \<or> l \<notin> jondos - colls"
      by auto
    then have "\<PP>(\<omega> in \<P>. first_jondo \<omega> = i \<and> last_ncoll \<omega> = l \<and> hit_colls \<omega>) = 0"
      using AE_term
      apply (intro prob_eq_0_AE)
      apply (elim AE_mp)
      by (auto  intro!: AE_I2 dest: term_imp_len first_collI4
        simp: first_jondo_def)
    then have "C.joint_distribution first_jondo last_ncoll {(i, l)} = 0"
      unfolding C.distribution_def C.\<mu>'_def
      by (simp add: vimage_def Int_def C_def cond_prob_def conj_ac)
    then show "C.joint_distribution first_jondo last_ncoll {(i, l)} *
          log 2 (C.joint_distribution first_jondo last_ncoll {(i, l)} /
                 (C.distribution first_jondo {i} * C.distribution last_ncoll {l})) = 0"
      by simp
  next
    fix i l assume "i \<in> jondos - colls" "l \<in> jondos - colls"
    have "{x\<in>space \<P>. first_jondo x = i \<and> last_ncoll x = l} \<in> sets \<P>"
      "{x\<in>space \<P>. first_jondo x = i} \<in> sets \<P>"
      "{x\<in>space \<P>. last_ncoll x = l} \<in> sets \<P>"
      by (auto intro!: sets_Collect simp: first_jondo_def)
    then have "C.joint_distribution first_jondo last_ncoll {(i, l)} = ?il i l"
      "C.distribution first_jondo {i} = ?i i"
      "C.distribution last_ncoll {l} = ?l l"
      unfolding C.distribution_def C.\<mu>'_def
      by (auto simp add: C_def conj_ac cond_prob_def vimage_def Int_def)
    then show "C.joint_distribution first_jondo last_ncoll {(i, l)} *
             log 2 (C.joint_distribution first_jondo last_ncoll {(i, l)} /
                    (C.distribution first_jondo {i} * C.distribution last_ncoll {l})) =
      ?il i l * log 2 (?il i l / (?i i * ?l l))"
      by simp
  qed
  ultimately show ?thesis by simp
qed

end

end
