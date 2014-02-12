(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

header {* Formalization of the Crowds-Protocol *}

theory Crowds_Protocol
  imports "../Discrete_Time_Markov_Chain"
begin

lemma fun_if_distrib:
  "card (if P then A else B) = (if P then card A else card B)"
  "real (if P then x else y) = (if P then real x else real y)"
  "(if P then a else b) * c = (if P then a * c else b * c)"
  "(if P then a else b) / c = (if P then a / c else b / c)"
  by auto

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

definition jondo_of :: "'a state \<Rightarrow> 'a" where
  "jondo_of = (\<lambda>Init j \<Rightarrow> j | Mix j \<Rightarrow> j | _ \<Rightarrow> SOME j. j\<in>jondos)"

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

lemma J_pos: "0 < J"
  unfolding J_def using jondos_non_empty by auto

lemma H_compl: "1 - H = real (card colls) / real (card jondos)"
  using colls_non_empty jondos_non_empty colls_smaller
  by (simp add: H_def card_Diff_subset card_mono real_of_nat_diff divide_eq_eq field_simps)

lemma H_eq2: "card (jondos - colls) * J = H"
  unfolding J_def H_def by simp

definition next_step :: "'a state \<Rightarrow> 'a state \<Rightarrow> real" where
  "next_step s t = (case (s, t) of (Start, Init j) \<Rightarrow> init j
                                 | (Init j, Mix j') \<Rightarrow> J
                                 | (Mix j, Mix j') \<Rightarrow> p_f * J
                                 | (Mix j, End) \<Rightarrow> 1 - p_f
                                 | (End, End) \<Rightarrow> 1
                                 | _ \<Rightarrow> 0)"

lemma next_step_to_Start_eq_0[simp]: "next_step s' Start = 0"
  by (cases s') (auto simp: next_step_def)

lemma next_step_to_Init[simp]: "next_step s (Init j) =
    (case s of Start \<Rightarrow> init j | _ \<Rightarrow> 0)"
  by (cases s) (auto simp: next_step_def)

lemma next_step_to_Mix[simp]: "next_step s (Mix j) =
    (case s of Init j \<Rightarrow> J | Mix j \<Rightarrow> p_f * J | _ \<Rightarrow> 0)"
  by (cases s) (auto simp: next_step_def)

lemma next_step_to_End[simp]: "next_step s End =
    (case s of Mix j \<Rightarrow> 1 - p_f | End \<Rightarrow> 1 | _ \<Rightarrow> 0)"
  by (cases s) (auto simp: next_step_def)

lemma next_step_neq_0_cases:
  "next_step s s' \<noteq> 0 \<longleftrightarrow>
    (s = Start \<longrightarrow> (\<exists>j. s' = Init j \<and> init j \<noteq> 0)) \<and>
    (s \<in> range Init \<longrightarrow> s' \<in> range Mix) \<and>
    (s \<in> range Mix \<longrightarrow> s' = End \<or> s' \<in> range Mix) \<and>
    (s = End \<longrightarrow> s' = End)"
  using p_f jondos_non_empty
  by (cases s) (auto split: state.split simp: J_def next_step_def)

lemma next_step_from_End[simp]: "next_step End s = 0 \<longleftrightarrow> s \<noteq> End"
  by (cases s) auto

lemma next_step_Mix_MixI: "\<exists>j. s = Mix j \<Longrightarrow> \<exists>j. s' = Mix j \<Longrightarrow> next_step s s' = p_f * J"
  by (cases s) auto

lemma measurable_jondo_of[measurable]:
  "jondo_of \<in> measurable (count_space valid_states) (count_space jondos)"
  using jondos_non_empty
  by (auto simp: measurable_count_space jondo_of_def intro!: someI_ex[of "\<lambda>j. j\<in>jondos"]
              elim!: valid_statesE)

lemma measurable_jondos_eq[measurable]:
  assumes f[measurable]: "f \<in> measurable M (count_space jondos)"
  assumes g[measurable]: "g \<in> measurable M (count_space jondos)"
  shows "{x\<in>space M. f x = g x} \<in> sets M"
proof -
  from measurable_space[OF f] measurable_space[OF g]
  have "{x\<in>space M. f x = g x} = {x\<in>space M. \<exists>j\<in>jondos. f x = j \<and> g x = j}"
    by auto
  also have "{x\<in>space M. \<exists>j\<in>jondos. f x = j \<and> g x = j} \<in> sets M" by measurable
  finally show ?thesis .
qed

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

abbreviation "\<PP> \<equiv> paths Start"

lemma E_Start: "E Start = {Init j | j. j \<in> jondos - colls \<and> init j \<noteq> 0 }"
  by (intro E_eqI) (auto intro: init_coll simp: next_step_neq_0_cases)

lemma E_Init: "j \<in> jondos - colls \<Longrightarrow> E (Init j) = {Mix j | j. j \<in> jondos }"
  using J_pos colls_smaller by (intro E_eqI) (auto simp: next_step_neq_0_cases)

lemma E_Mix: "j \<in> jondos \<Longrightarrow> E (Mix j) = {Mix j | j. j \<in> jondos } \<union> {End}"
  using J_pos by (intro E_eqI) (auto simp: next_step_neq_0_cases)

lemma E_End: "E End = {End}"
  by (intro E_eqI) (auto simp: next_step_neq_0_cases)
  
text {*

What is the probability that the server sees a specific (including the initiator) as sender.

*}

definition "len \<omega> = (LEAST n :: nat. \<omega> n = End) - 2"
definition "first_jondo (\<omega> :: nat \<Rightarrow> 'a state) = jondo_of (\<omega> 0)"
definition "last_jondo (\<omega> :: nat \<Rightarrow> 'a state) = jondo_of (\<omega> (Suc (len \<omega>)))"

lemma measurable_len[measurable]: "len \<in> measurable S_seq (count_space UNIV)"
  unfolding len_def[abs_def] by simp

lemma measurable_last_jondo[measurable]: "last_jondo \<in> measurable S_seq (count_space jondos)"
  unfolding last_jondo_def[abs_def] by measurable

lemma measurable_first_jondo[measurable]: "first_jondo \<in> measurable S_seq (count_space jondos)"
  unfolding first_jondo_def[abs_def] by measurable

definition "term \<omega> \<longleftrightarrow>
  \<omega> \<in> UNIV \<rightarrow> valid_states \<and>
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
  "term \<omega> \<Longrightarrow> \<exists>j. \<omega> (Suc n) = Mix j \<Longrightarrow> \<omega> (Suc (Suc n)) = End \<Longrightarrow> len \<omega> = n"
  by (rule ccontr) (auto simp add: term_def neq_iff intro: Suc_leI)

lemma le_lenI[intro]:
  "term \<omega> \<Longrightarrow> \<omega> (Suc i) \<noteq> End \<Longrightarrow> i \<le> len \<omega>"
  unfolding term_def by (rule ccontr) auto

lemma last_jondo_eq_iff:
  assumes "term \<omega>"
  shows "last_jondo \<omega> = j \<longleftrightarrow> \<omega> (Suc (len \<omega>)) = Mix j"
  unfolding last_jondo_def using `term \<omega>`
  by (auto simp: term_def jondo_of_def)

lemma AE_terminating: "AE \<omega> in paths Start. \<exists>n. \<omega> n = End"
proof -
  from possible_jondo guess j . note j = this
  then have End_reachable_Start: "End \<in> reachable (valid_states - {End}) Start"
    by (rule_tac reachable.step[OF reachable.step[OF reachable.start], of "Init j" _ "Mix j"])
       (auto simp: E_Start E_Init E_Mix)

  have "AE \<omega> in paths Start. case_nat Start \<omega> \<in> until valid_states {End}"
  proof (subst AE_until_iff_reachable, safe)
    fix s assume *: "reachable (valid_states - {End}) s \<inter> {End} = {}"
    assume "s \<in> reachable (valid_states - {End}) Start"
    then have s: "s \<in> valid_states" by auto
    then show False
    proof (cases rule: valid_statesE)
      case (Init i)
      moreover with j s have "End \<in> reachable (valid_states - {End}) (Init i)"
        by (rule_tac reachable.step[OF reachable.start, of "Mix j"])
           (auto simp: E_Start E_Init E_Mix)
      ultimately show False
        using * by auto
    qed (insert End_reachable_Start * E_End E_Mix, auto intro: reachable.intros)
  next
    assume "reachable (valid_states - {End}) Start \<inter> {End} = {}"
    with End_reachable_Start show False by auto
  qed (auto simp: next_step_neq_0_cases)
  then show ?thesis
    by eventually_elim (auto elim: untilE)
qed

subsection {* A Crowds-Protocol run terminates almost surely *}

lemma AE_term: "AE \<omega> in \<PP>. term \<omega>"
  using AE_terminating AE_all_enabled[OF Start_valid_state] AE_space
  apply eventually_elim
proof (safe intro!: term_def[THEN iffD2])
  fix \<omega> n assume \<omega>: "\<omega> \<in> space \<PP>" and "\<omega> n = End"
    and not_zero: "\<forall>i. \<omega> i \<in> E (case_nat Start \<omega> i)"
  from not_zero[THEN spec, of 0] not_zero[THEN spec, of 1]
  have "\<omega> 0 \<in> range Init" "\<omega> 1 \<in> range Mix"
    by (auto simp: E_Start E_Init)
  moreover have \<omega>: "\<forall>i. \<omega> i \<in> valid_states"
    using \<omega> by (auto simp: space_PiM Pi_iff)
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

  { fix i :: nat
    { fix j have "\<omega> j = End \<Longrightarrow> \<omega> (Suc j) = End"
        using not_zero[THEN spec, of "Suc j"] by (simp add: E_End) }
    note * = this
    assume "len \<omega> < i" with len show "\<omega> (Suc i) = End"
      by (induct i) (auto simp: less_Suc_eq intro: *) }
  note tail = this

  { fix i assume "i \<le> len \<omega>"
    then show "\<omega> (Suc i) \<in> Mix ` jondos"
    proof (induct i)
      case (Suc n)
      moreover then obtain j where "\<omega> (Suc n) = Mix j" "j \<in> jondos" by auto
      moreover note not_zero[THEN spec, of "Suc (Suc n)"] len p_f \<omega>[THEN spec, of "Suc (Suc n)"]
      ultimately show ?case
        by (auto simp add: E_Mix split: state.split_asm)
    qed (insert \<omega>1, simp) }
qed auto

lemma prob_sums_len:
  assumes P[measurable]: "\<And>n. {\<omega>\<in>space S_seq. P \<omega>} \<in> sets S_seq"
  shows "(\<lambda>n. \<P>(\<omega> in \<PP>. len \<omega> = n \<and> P \<omega>)) sums \<P>(\<omega> in \<PP>. P \<omega>)"
  using AE_term by (intro prob_sums) auto

lemma prob_sums_cyl_init:
  fixes S
  assumes S: "\<And>n i. S n i \<subseteq> jondos" and I: "I \<subseteq> jondos - colls"
  shows "(\<lambda>n. (\<Sum>j\<in>I. init j) * (\<Prod>i\<le>n. card (S n i) * J) * (p_f)^n * (1 - p_f)) sums
    \<P>(\<omega> in \<PP>. \<omega> 0 \<in> Init ` I \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` S (len \<omega>) i))"
proof -
  let ?P = "\<lambda>\<omega>. \<omega> 0 \<in> Init ` I \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` S (len \<omega>) i)"
  have "(\<lambda>n. \<P>(\<omega> in \<PP>. len \<omega> = n \<and> ?P \<omega>)) sums \<P>(\<omega> in \<PP>. ?P \<omega>)"
    by (rule prob_sums_len) simp
  moreover
  { fix n
    let ?A = "\<lambda>0 \<Rightarrow> Init`I | Suc i \<Rightarrow> if i \<le> n then Mix`(S n i) else {End}"
    let ?p = "\<lambda>0 \<Rightarrow> init \<circ> jondo_of | Suc 0 \<Rightarrow> \<lambda>j. J | Suc (Suc i) \<Rightarrow> \<lambda>j. if i < n then J * p_f else 1 - p_f"

    have [simp]: "\<And>f a b. (\<Prod>x\<in>{Suc a ..< Suc b}. f x) = (\<Prod>x\<in>{a ..< b}. f (Suc x))"
      "{.. n} = insert 0 {Suc 0..<Suc n}"
      unfolding image_Suc_atLeastLessThan[symmetric] by (subst setprod_reindex) auto

    have "\<P>(\<omega> in \<PP>. len \<omega> = n \<and> ?P \<omega>) = \<P>(\<omega> in \<PP>. (\<forall>i<Suc (Suc (Suc n)). \<omega> i \<in> ?A i))"
      apply (rule prob_eq_AE)
      using AE_term
      apply eventually_elim
    proof (intro iffI conjI allI impI)
      fix \<omega> assume "term \<omega>" and \<omega>: "\<forall>i<Suc (Suc (Suc n)). \<omega> i \<in> ?A i"
      show "\<omega> 0 \<in> Init ` I" using \<omega>[THEN spec, of 0] by auto
      show "len \<omega> = n"
        using `term \<omega>` \<omega>[THEN spec, of "Suc n"] \<omega>[THEN spec, of "Suc (Suc n)"]
        by (intro len_eq) auto
      { fix i assume "i \<le> len \<omega>" with `len \<omega> = n` show "\<omega> (Suc i) \<in> Mix ` S (len \<omega>) i"
          using \<omega>[THEN spec, of "Suc i"] by (auto simp: inj_image_mem_iff) }
    next
      fix \<omega> i assume \<omega>: "term \<omega>" "len \<omega> = n \<and> ?P \<omega>" "i <Suc (Suc (Suc n))"
      then have "i \<le> len \<omega> \<Longrightarrow> \<omega> (Suc i) \<in> Mix ` S (len \<omega>) i" by auto
      with \<omega> show "\<omega> i \<in> ?A i" by (auto split: nat.split)
    qed auto
    also have "\<dots> = (\<Prod>i<Suc (Suc (Suc n)). (\<Sum>a\<in>?A i. ?p i a))"
      using S I by (intro independent_cylinder) (auto simp: jondo_of_def split: nat.split)
    also have "\<dots> = (\<Prod>i\<in>{0, Suc 0} \<union> {Suc (Suc 0) ..< Suc (Suc n)} \<union> {Suc (Suc n)}. (\<Sum>a\<in>?A i. ?p i a))"
      by (intro setprod_cong) auto
    also have "\<dots> = (\<Sum>j\<in>I. init j) * (\<Prod>i\<le>n. card (S n i) * J) * (p_f)^n * (1 - p_f)"
      by (simp_all add: card_image setsum_reindex jondo_of_def real_eq_of_nat setprod_timesf setprod_constant)
    finally have "\<P>(\<omega> in \<PP>. len \<omega> = n \<and> ?P \<omega>) = \<dots>" . }
  ultimately show ?thesis by simp
qed

lemma prob_sums_cyl:
  fixes S assumes S: "\<And>n i. S n i \<subseteq> jondos"
  shows "(\<lambda>n. (\<Prod>i\<le>n. card (S n i) * J) * (p_f)^n * (1 - p_f)) sums
    \<P>(\<omega> in \<PP>. (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` S (len \<omega>) i))"
proof -
  have "\<P>(\<omega> in \<PP>. (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` S (len \<omega>) i)) =
    \<P>(\<omega> in \<PP>. \<omega> 0 \<in> Init ` (jondos - colls) \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` S (len \<omega>) i))"
    using AE_term
    by (intro prob_eq_AE, elim AE_mp) (auto simp add: term_def)
  with prob_sums_cyl_init[of S, OF S subset_refl]
  show ?thesis
    by simp
qed

lemma (in prob_space) prob_setsum:
  assumes [simp, intro]: "finite I"
  assumes P: "\<And>n. n \<in> I \<Longrightarrow> {x\<in>space M. P n x} \<in> events"
  assumes Q: "{x\<in>space M. Q x} \<in> events"
  assumes ae: "AE x in M. (\<forall>n\<in>I. P n x \<longrightarrow> Q x) \<and> (Q x \<longrightarrow> (\<exists>!n\<in>I. P n x))"
  shows "\<P>(x in M. Q x) = (\<Sum>n\<in>I. \<P>(x in M. P n x))"
proof -
  from ae[THEN AE_E_prob] guess S . note S = this
  then have disj: "disjoint_family_on (\<lambda>n. {x\<in>space M. P n x} \<inter> S) I"
    by (auto simp: disjoint_family_on_def)
  from S have ae_S:
    "AE x in M. x \<in> {x\<in>space M. Q x} \<longleftrightarrow> x \<in> (\<Union>n\<in>I. {x\<in>space M. P n x} \<inter> S)"
    "\<And>n. n \<in> I \<Longrightarrow> AE x in M. x \<in> {x\<in>space M. P n x} \<longleftrightarrow> x \<in> {x\<in>space M. P n x} \<inter> S"
    using ae by (auto dest!: AE_prob_1)
  from ae_S have *:
    "\<P>(x in M. Q x) = prob (\<Union>n\<in>I. {x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) (auto intro!: sets.Int)
  from ae_S have **:
    "\<And>n. n \<in> I \<Longrightarrow> \<P>(x in M. P n x) = prob ({x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) auto
  show ?thesis
    using S P disj
    by (auto simp add: * ** simp del: UN_simps intro!: finite_measure_finite_Union)
qed

subsection {* Server gets no information *}

lemma server_view1:
  assumes j: "j : jondos"
  shows "\<P>(\<omega> in \<PP>. last_jondo \<omega> = j) = J"
proof -
  let ?S = "% n i. if n = (i::nat) then {j} else jondos"

  have "\<P>(\<omega> in \<PP>. last_jondo \<omega> = j) = \<P>(\<omega> in \<PP>. (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` ?S (len \<omega>) i))"
    using AE_term
    by (intro prob_eq_AE) (auto simp: last_jondo_eq_iff term_imp_len)
  moreover have "(\<lambda>n. (\<Prod>i\<le>n. card (?S n i) * J) * (p_f)^n * (1 - p_f)) sums \<dots>"
    using j by (intro prob_sums_cyl) auto
  moreover have "(\<lambda>n. p_f ^ n * (1 - p_f) * J) sums ((1 / (1 - p_f)) * (1 - p_f) * J)"
    using p_f by (intro sums_mult sums_mult2 geometric_sums) auto
  ultimately show "\<P>(\<omega> in \<PP>. last_jondo \<omega> = j) = J"
    using jondos_non_empty p_f
    by (simp add: lessThan_Suc_atMost[symmetric] lessThan_Suc setprod_constant sums_iff J_def)
qed

lemma server_view_indep:
  assumes l: "l \<in> jondos" and i: "i \<in> jondos - colls"
  shows "\<P>(\<omega> in \<PP>. last_jondo \<omega> = l \<and> first_jondo \<omega> = i) =
    \<P>(\<omega> in \<PP>. last_jondo \<omega> = l) * \<P>(\<omega> in \<PP>. first_jondo \<omega> = i)"
proof -
  let ?S = "\<lambda>n i :: nat. if n = i then {l} else jondos"
  have 1: "
    \<P>(\<omega> in \<PP>. \<omega> 0 \<in> Init ` {i} \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` ?S (len \<omega>) i)) =
    \<P>(\<omega> in \<PP>. last_jondo \<omega> = l \<and> first_jondo \<omega> = i)"
    using AE_term
    apply (intro prob_eq_AE)
    apply (elim AE_mp)
    apply (auto simp: all_conj_distrib iff_conv_conj_imp last_jondo_eq_iff term_imp_len first_jondo_def jondo_of_def
            dest!: term_imp_len(2)
             intro!: AE_I2)
    done
  have 2: "(\<lambda>n. init i * p_f ^ n * (1 - p_f) * J) sums (init i * (1 / (1 - p_f)) * (1 - p_f) * J)"
    using p_f by (intro sums_mult sums_mult2 geometric_sums) auto
  have "(\<lambda>n. (\<Sum>j\<in>{i}. init j) * (\<Prod>i\<le>n. card (?S n i) * J) * (p_f)^n * (1 - p_f)) sums
    \<P>(\<omega> in \<PP>. \<omega> 0 \<in> Init ` {i} \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` ?S (len \<omega>) i))"
    using l i by (intro prob_sums_cyl_init) auto
  also have "(\<lambda>n. (\<Sum>j\<in>{i}. init j) * (\<Prod>i\<le>n. card (?S n i) * J) * (p_f)^n * (1 - p_f)) =
    (\<lambda>n. init i * p_f ^ n * (1 - p_f) * J)"
    using jondos_non_empty p_f
    by (simp add: lessThan_Suc_atMost[symmetric] lessThan_Suc setprod_constant sums_iff J_def) 
  finally have *: "\<P>(\<omega> in \<PP>. last_jondo \<omega> = l \<and> first_jondo \<omega> = i) = init i * J"
    unfolding 1 using jondos_non_empty p_f 2
    by (simp add: lessThan_Suc_atMost[symmetric] lessThan_Suc setprod_constant sums_iff J_def) 

  let ?S = "\<lambda>n i :: nat. if n = i then {l} else jondos"
  have 1: "
    \<P>(\<omega> in \<PP>. \<omega> 0 \<in> Init ` {i} \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` jondos)) =
    \<P>(\<omega> in \<PP>. first_jondo \<omega> = i)"
    using AE_term
    apply (intro prob_eq_AE)
    apply (elim AE_mp)
    apply (auto simp: all_conj_distrib iff_conv_conj_imp last_jondo_eq_iff term_imp_len first_jondo_def jondo_of_def
            dest!: term_imp_len(2)
             intro!: AE_I2)
    done
  have 2: "(\<lambda>n. init i * p_f ^ n * (1 - p_f)) sums (init i * (1 / (1 - p_f)) * (1 - p_f))"
    using p_f by (intro sums_mult sums_mult2 geometric_sums) auto
  have "(\<lambda>n. (\<Sum>j\<in>{i}. init j) * (\<Prod>i\<le>n. card jondos * J) * (p_f)^n * (1 - p_f)) sums
    \<P>(\<omega> in \<PP>. \<omega> 0 \<in> Init ` {i} \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` jondos))"
    using l i by (intro prob_sums_cyl_init) auto
  also have "(\<lambda>n. (\<Sum>j\<in>{i}. init j) * (\<Prod>i\<le>n. card jondos * J) * (p_f)^n * (1 - p_f)) =
    (\<lambda>n. init i * p_f ^ n * (1 - p_f))"
    using jondos_non_empty p_f
    by (simp add: lessThan_Suc_atMost[symmetric] lessThan_Suc setprod_constant sums_iff J_def) 
  finally have **: "\<P>(\<omega> in \<PP>. first_jondo \<omega> = i) = init i"
    unfolding 1 using jondos_non_empty p_f 2
    by (simp add: lessThan_Suc_atMost[symmetric] lessThan_Suc setprod_constant sums_iff J_def) 
  
  from server_view1[OF l] * ** i show ?thesis by simp
qed

lemma server_view:
  shows "\<P>(\<omega> in \<PP>. last_jondo \<omega> = first_jondo \<omega>) = J"
proof -
  let ?P = "\<lambda>j. \<P>(\<omega> in \<PP>. \<omega> 0 = Init j \<and> last_jondo \<omega> = j)"

  have "\<P>(\<omega> in \<PP>. last_jondo \<omega> = first_jondo \<omega>) = (\<Sum>j\<in>jondos-colls. ?P j)"
  proof (rule prob_setsum)
    show "AE \<omega> in \<PP>. (\<forall>j\<in>jondos - colls. \<omega> 0 = Init j \<and> last_jondo \<omega> = j \<longrightarrow> last_jondo \<omega> = first_jondo \<omega>) \<and>
               (last_jondo \<omega> = first_jondo \<omega> \<longrightarrow> (\<exists>!j. j \<in> jondos - colls \<and> \<omega> 0 = Init j \<and> last_jondo \<omega> = j))"
      using AE_term
      by (elim AE_mp)
         (auto simp: last_jondo_eq_iff first_jondo_def jondo_of_def intro!: AE_I2 dest: term_imp_len)
  qed auto
  moreover
  { fix j assume j: "j \<in> jondos - colls"
    let "?S n i" = "if n = (i::nat) then {j} else jondos"
    have "?P j = \<P>(\<omega> in \<PP>. \<omega> 0 \<in> Init ` {j} \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` ?S (len \<omega>) i))"
      using AE_term
      by (intro prob_eq_AE)
         (auto simp: all_conj_distrib iff_conv_conj_imp last_jondo_eq_iff term_imp_len)
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

lemma measurable_hit_colls[measurable]: "hit_colls \<in> measurable S_seq (count_space UNIV)"
  unfolding hit_colls_def[abs_def] by simp

lemma measurable_first_coll[measurable]: "first_coll \<in> measurable S_seq (count_space UNIV)"
  unfolding first_coll_def[abs_def] by simp

lemma measurable_last_ncoll[measurable]: "last_ncoll \<in> measurable S_seq (count_space jondos)"
  unfolding last_ncoll_def[abs_def] by simp

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
  by (cases "first_coll \<omega>") (auto simp: last_ncoll_def jondo_of_def dest!: term_imp_len)

subsection {* The probability to hit a collaborateur *}

lemma hit: "\<P>(\<omega> in \<PP>. hit_colls \<omega>) = (1 - H) / (1 - H * p_f)"
  (is "?HIT = _")
proof -
  have "p_f * H \<noteq> 1"
    using H_pf_1 by (simp add: ac_simps)
  have "?HIT = 1 - \<P>(\<omega> in \<PP>. \<not> hit_colls \<omega>)"
    by (subst prob_neg) simp_all
  moreover have "\<P>(\<omega> in \<PP>. \<not> hit_colls \<omega>) =
    \<P>(\<omega> in \<PP>. \<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` (jondos - colls))"
    using AE_term colls_smaller
    by (intro prob_eq_AE, elim AE_mp)
       (auto simp add: hit_colls_eq image_set_diff term_imp_len intro!: AE_I2)
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
  fixes S
  assumes S: "\<And>n i. S n i \<subseteq> jondos - colls" and I: "\<And>n. I n \<subseteq> jondos - colls"
  shows "(\<lambda>n. (\<Sum>j\<in>I n. init j) * (\<Prod>i<n. card (S n i) * J * p_f) * (1 - H * p_f)) sums
    \<P>(\<omega> in \<PP>. \<omega> 0 \<in> Init ` I (first_coll \<omega>) \<and> (\<forall>i<first_coll \<omega>. \<omega> (Suc i) \<in> Mix ` S (first_coll \<omega>) i) \<bar> hit_colls \<omega>)"
proof -
  have "(\<lambda>n. \<P>(\<omega> in \<PP>. first_coll \<omega> = n \<and> \<omega> 0 \<in> Init ` (I n) \<and> (\<forall>i<n. \<omega> (Suc i) \<in> Mix ` S n i) \<and> hit_colls \<omega>))
    sums \<P>(\<omega> in \<PP>. \<omega> 0 \<in> Init ` (I (first_coll \<omega>)) \<and>
                   (\<forall>i<first_coll \<omega>. \<omega> (Suc i) \<in> Mix ` S (first_coll \<omega>) i) \<and> hit_colls \<omega>)"
    (is "?P sums ?C")
    by (rule prob_sums) auto
  moreover
  { fix n :: nat
    def T \<equiv> "\<lambda>l i. if l < n     then {}
              else if i < n     then S n i
              else if i = n     then colls
                                else jondos"

    have cards: "\<And>l. n \<le> l \<Longrightarrow> {..l} \<inter> - {x. x < n} \<inter> - {n} = {n<..l}"
        "\<And>l. n \<le> l \<Longrightarrow> {..l} \<inter> {x. x < n} = {..< n}"
      by auto

    have "?P n = \<P>(\<omega> in \<PP>. \<omega> 0 \<in> Init ` (I n) \<and> (\<forall>i\<le>len \<omega>. \<omega> (Suc i) \<in> Mix ` T (len \<omega>) i))"
      using AE_term
    proof (intro prob_eq_AE, elim AE_mp, intro AE_I2 impI allI conjI iffI)
      fix \<omega> i assume "term \<omega>" "i \<le> len \<omega>"
        and coll: "first_coll \<omega> = n \<and> \<omega> 0 \<in> Init ` (I n) \<and> (\<forall>i<n. \<omega> (Suc i) \<in> Mix ` S n i) \<and> hit_colls \<omega>"
      then show "\<omega> (Suc i) \<in> Mix ` T (len \<omega>) i"
        by (auto simp: T_def not_le[symmetric] intro: first_collI term_imp_len)
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
    qed auto
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
    \<P>(\<omega> in \<PP>. \<omega> 0 \<in> Init ` I (first_coll \<omega>) \<and> (\<forall>i<first_coll \<omega>. \<omega> (Suc i) \<in> Mix ` S (first_coll \<omega>) i) \<bar> hit_colls \<omega>)"
    unfolding cond_prob_def hit by (simp only: conj_ac) (rule sums_divide)
  with H show ?thesis
    by (simp add: mult_ac)
qed

subsection {* The probability that the sender hits a collaborateur *}

lemma P_first_jondo_last_ncoll:
  assumes l: "l \<in> jondos - colls" and i: "i \<in> jondos - colls"
  shows "\<P>(\<omega> in \<PP>. first_jondo \<omega> = i \<and> last_ncoll \<omega> = l \<bar> hit_colls \<omega> ) =
    init i * (J * p_f + (if i = l then 1 - H * p_f else 0))"
  (is "?P = _")
proof -
  let "?S n k" = "if n = Suc k then {l} else jondos - colls"
  let "?I n" = "if (n::nat) = 0 then {i} \<inter> {l} else {i}"
  have [simp]: "\<And>n. {..<Suc n} \<inter> - {n} = {..<n}" by auto
  have "?P = \<P>(\<omega> in \<PP>. \<omega> 0 \<in> Init ` ?I (first_coll \<omega>) \<and>
        (\<forall>i<first_coll \<omega>. \<omega> (Suc i) \<in> Mix ` ?S (first_coll \<omega>) i) \<bar> hit_colls \<omega>)"
  proof (rule cond_prob_eq_AE)
    show "AE \<omega> in \<PP>. hit_colls \<omega> \<longrightarrow>
      (first_jondo \<omega> = i \<and> last_ncoll \<omega> = l) =
      (\<omega> 0 \<in> Init ` ?I (first_coll \<omega>) \<and> (\<forall>i<first_coll \<omega>. \<omega> (Suc i) \<in> Mix ` ?S (first_coll \<omega>) i))"
      using AE_term
    proof (elim AE_mp, safe intro!: AE_I2)
      fix \<omega> assume \<omega>: "term \<omega>" "hit_colls \<omega>"
      then show "\<omega> 0 \<in> Init ` (if first_coll \<omega> = 0 then {first_jondo \<omega>} \<inter> {last_ncoll \<omega>} else {first_jondo \<omega>})"
        by (auto simp add: first_jondo_def last_ncoll_def term_def jondo_of_def)
      fix i assume "i < first_coll \<omega>"
      then have "i \<le> len \<omega>" using first_coll_le_len[OF \<omega>] by simp
      from \<omega> first_collI2[OF `i < first_coll \<omega>`] term_imp_len(1)[OF \<omega>(1) this]
      show "\<omega> (Suc i) \<in> Mix ` (if first_coll \<omega> = Suc i then {last_ncoll \<omega>} else jondos - colls)"
        by (auto simp: image_set_diff last_ncoll_def jondo_of_def)
    next
      fix \<omega> j assume j: "j \<in> (if first_coll \<omega> = 0 then {i} \<inter> {l} else {i})"
      then have [simp]: "j = i" by (cases "first_coll \<omega>") auto
      assume \<omega>: "term \<omega>" "hit_colls \<omega>" "\<omega> 0 = Init j"
      then show "first_jondo \<omega> = i"
        by (simp add: first_jondo_def jondo_of_def)
      assume "\<forall>i<first_coll \<omega>. \<omega> (Suc i) \<in> Mix ` (if first_coll \<omega> = Suc i then {l} else jondos - colls)"
      with j \<omega> show "last_ncoll \<omega> = l"
        by (cases "first_coll \<omega>") (auto simp: last_ncoll_def jondo_of_def)
    qed
  qed auto
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

lemma P_first_jondo_eq_last_ncoll:
  "\<P>(\<omega> in \<PP>. first_jondo \<omega> = last_ncoll \<omega> \<bar> hit_colls \<omega> ) = 1 - (H - J) * p_f"
proof -
  have "\<P>(\<omega> in \<PP>. first_jondo \<omega> = last_ncoll \<omega> \<and> hit_colls \<omega> )
    = (\<Sum>i\<in>jondos - colls. \<P>(\<omega> in \<PP>. first_jondo \<omega> = i \<and> last_ncoll \<omega> = i \<and> hit_colls \<omega> ))"
  proof (rule prob_setsum)
    show "finite (jondos - colls)" by auto
  next
    fix i assume "i \<in> jondos - colls"
    show "{\<omega> \<in> space \<PP>. first_jondo \<omega> = i \<and> last_ncoll \<omega> = i \<and> hit_colls \<omega>} \<in> sets \<PP>"
      by (intro sets.sets_Collect sets.sets_Collect_finite_Ex) auto
  next
    { fix \<omega> :: "nat \<Rightarrow> _" assume \<omega>: "\<omega> \<in> UNIV \<rightarrow> valid_states"
      { fix i
        from \<omega> have "\<omega> i \<in> valid_states" by auto
        with jondos_non_empty have "jondo_of (\<omega> i) \<in> jondos"
          by (auto simp: Pi_iff jondo_of_def intro!: someI_ex[of "\<lambda>j. j \<in> jondos"] split: state.split) }
      from this[of 0] this[of "first_coll \<omega>"]
      have "first_jondo \<omega> = last_ncoll \<omega> \<longleftrightarrow> (\<exists>j\<in>jondos. first_jondo \<omega> = j \<and> last_ncoll \<omega> = j)"
        unfolding first_jondo_def last_ncoll_def by auto }
    then have "{\<omega> \<in> space \<PP>. (first_jondo \<omega> = last_ncoll \<omega>) \<and> hit_colls \<omega>} 
      = {\<omega> \<in> space \<PP>. (\<exists>j\<in>jondos. first_jondo \<omega> = j \<and> last_ncoll \<omega> = j) \<and> hit_colls \<omega>}"
      using measurable_space[OF measurable_last_ncoll] by auto
    also have "\<dots> \<in> sets \<PP>"
      by (intro sets.sets_Collect sets.sets_Collect_finite_Ex) auto
    finally show "{\<omega> \<in> space \<PP>. (first_jondo \<omega> = last_ncoll \<omega>) \<and> hit_colls \<omega>} \<in> sets \<PP>" .
  next
    show "AE \<omega> in \<PP>. (\<forall>i\<in>jondos - colls.
                   first_jondo \<omega> = i \<and> last_ncoll \<omega> = i \<and> hit_colls \<omega> \<longrightarrow>
                   first_jondo \<omega> = last_ncoll \<omega> \<and> hit_colls \<omega>) \<and>
               (first_jondo \<omega> = last_ncoll \<omega> \<and> hit_colls \<omega> \<longrightarrow>
                (\<exists>!i. i \<in> jondos - colls \<and> first_jondo \<omega> = i \<and> last_ncoll \<omega> = i \<and> hit_colls \<omega>)) "
      using AE_term
      by eventually_elim (auto simp: term_def first_jondo_def jondo_of_def)
  qed
  then have "\<P>(\<omega> in \<PP>. first_jondo \<omega> = last_ncoll \<omega> \<bar> hit_colls \<omega> )
    = (\<Sum>i\<in>jondos - colls. \<P>(\<omega> in \<PP>. first_jondo \<omega> = i \<and> last_ncoll \<omega> = i \<bar> hit_colls \<omega> ))"
    unfolding cond_prob_def setsum_divide_distrib[symmetric] by simp
  also have "\<dots> = J * p_f + 1 - H * p_f"
    by (simp add: P_first_jondo_last_ncoll setsum_left_distrib[symmetric])
  finally show ?thesis by (simp add: field_simps)
qed

lemma probably_innocent:
  assumes approx: "1 / (2 * (H - J)) \<le> p_f" and "H \<noteq> J"
  shows "\<P>(\<omega> in \<PP>. first_jondo \<omega> = last_ncoll \<omega> \<bar> hit_colls \<omega> ) \<le> 1 / 2"
  unfolding P_first_jondo_eq_last_ncoll
proof -
  have [simp]: "\<And>n :: nat. 1 \<le> real n \<longleftrightarrow> 1 \<le> n" by auto
  have "0 \<le> J" unfolding J_def by auto
  then have "1 * J \<le> H"
    unfolding H_eq2[symmetric] using colls_smaller
    by (intro mult_mono) (auto simp: Suc_le_eq card_Diff_subset not_le)
  with `H \<noteq> J` have "J < H" by auto
  with approx show "1 - (H - J) * p_f \<le> 1 / 2"
    by (auto simp add: field_simps divide_le_eq split: split_if_asm)
qed

lemma P_last_ncoll:
  assumes l: "l \<in> jondos - colls"
  shows "\<P>(\<omega> in \<PP>. last_ncoll \<omega> = l \<bar> hit_colls \<omega> ) = J * p_f + init l * (1 - H * p_f)"
proof -
  have "\<P>(\<omega> in \<PP>. last_ncoll \<omega> = l \<and> hit_colls \<omega>)
    = (\<Sum>i\<in>jondos - colls. \<P>(\<omega> in \<PP>. first_jondo \<omega> = i \<and> last_ncoll \<omega> = l \<and> hit_colls \<omega>))"
    apply (rule prob_setsum)
    using AE_term
    apply auto
    apply (auto intro!: AE_I2 simp: term_def jondo_of_def first_jondo_def)
    done
  then have "\<P>(\<omega> in \<PP>. last_ncoll \<omega> = l \<bar> hit_colls \<omega>)
    = (\<Sum>i\<in>jondos - colls. \<P>(\<omega> in \<PP>. first_jondo \<omega> = i \<and> last_ncoll \<omega> = l \<bar> hit_colls \<omega>))"
    unfolding cond_prob_def setsum_divide_distrib[symmetric] by simp
  also have "\<dots> = (\<Sum>i\<in>jondos - colls. init i * J * p_f + (if i = l then init i * (1 - H * p_f) else 0))"
    using l by (auto intro!: setsum_cong simp add: P_first_jondo_last_ncoll field_simps)
  also have "\<dots> = J * p_f + init l * (1 - H * p_f)"
    using l by (simp add: setsum_addf setsum_left_distrib[symmetric] setsum.If_cases)
  finally show ?thesis .
qed

lemma P_first_jondo:
  assumes i: "i \<in> jondos - colls"
  shows "\<P>(\<omega> in \<PP>. first_jondo \<omega> = i \<bar> hit_colls \<omega> ) = init i"
proof -
  have "\<P>(\<omega> in \<PP>. first_jondo \<omega> = i \<bar> hit_colls \<omega> ) =
    \<P>(\<omega> in \<PP>. \<omega> 0 \<in> Init ` {i} \<and> (\<forall>i<first_coll \<omega>. \<omega> (Suc i) \<in> Mix ` (jondos - colls)) \<bar> hit_colls \<omega>)"
    using AE_term i
    apply (intro cond_prob_eq_AE)
    apply auto
    apply (auto intro!: AE_I2 dest: term_imp_len simp: first_collI3 jondo_of_def first_jondo_def)
    done
  moreover have "(\<lambda>n. (\<Sum>j\<in>{i}. init j) * (\<Prod>i<n. card (jondos - colls) * J * p_f) * (1 - H * p_f)) sums \<dots>"
    using i by (intro hit_prob_sums_cyl) auto
  ultimately have "(\<lambda>n. init i * (H * p_f)^n * (1 - H * p_f)) sums \<P>(\<omega> in \<PP>. first_jondo \<omega> = i \<bar> hit_colls \<omega> )"
    by (simp add: sums_iff H_def J_def setprod_constant)
  moreover have "(\<lambda>n. init i * (H * p_f)^n * (1 - H * p_f)) sums (init i * (1/(1 - H*p_f)) * (1 - H*p_f))"
    using H_pf_0 H_pf_1 by (intro sums_mult sums_mult2 geometric_sums) simp
  ultimately show ?thesis
    using H_pf_1 by (simp add: sums_iff)
qed

subsection {* Probability space of hitting runs *}

definition "C = uniform_measure \<PP> {\<omega>\<in>space \<PP>. hit_colls \<omega>}"

lemma emeasure_hit_colls_not_0: "emeasure \<PP> {\<omega> \<in> space \<PP>. hit_colls \<omega>} \<noteq> 0"
  using H H_pf_1 unfolding hit emeasure_eq_measure by auto

lemma measurable_C[measurable (raw)]:
  "A \<in> sets S_seq \<Longrightarrow> A \<in> sets C"
  "f \<in> measurable M S_seq \<Longrightarrow> f \<in> measurable M C"
  "g \<in> measurable S_seq M \<Longrightarrow> g \<in> measurable C M"
  "A \<inter> space S_seq \<in> sets S_seq \<Longrightarrow> A \<inter> space C \<in> sets S_seq"
  unfolding C_def uniform_measure_def
  by simp_all

lemma vimage_Int_space_C[simp]:
  "f -` {x} \<inter> space C = {\<omega>\<in>space S_seq. f \<omega> = x}"
  by (auto simp: C_def)

end

sublocale Crowds_Protocol \<subseteq> C!: information_space C 2
proof -
  interpret C!: prob_space C
    unfolding C_def
    using emeasure_hit_colls_not_0
    by (intro prob_space_uniform_measure) auto
  show "information_space C 2"
    by default simp
qed

context Crowds_Protocol
begin

abbreviation
  mutual_information_Pow_CP ("\<I>'(_ ; _')") where
  "\<I>(X ; Y) \<equiv> C.mutual_information 2 (count_space (X`space C)) (count_space (Y`space C)) X Y"

lemma simple_functionI:
  assumes "finite (f`(UNIV \<rightarrow> valid_states))"
  assumes [measurable]: "\<And>x. {\<omega>\<in>space S_seq. f \<omega> = x} \<in> sets S_seq"
  shows "simple_function C f"
  using assms unfolding simple_function_def C_def
  by (simp add: vimage_def space_PiM PiE_def)

subsection {* Estimate the information to the collaborateurs *}

lemma measure_C[simp]:
  assumes A[measurable]: "A \<in> sets S_seq"
  shows "measure C A = \<P>(\<omega> in \<PP>. \<omega> \<in> A \<bar> hit_colls \<omega> )"
  unfolding C_def cond_prob_def
  using emeasure_hit_colls_not_0 A
  by (subst measure_uniform_measure) (simp_all add: emeasure_eq_measure Int_def conj_ac)

lemma information_flow:
  defines "h \<equiv> real (card (jondos - colls))"
  assumes init_uniform: "\<And>i. i \<in> jondos - colls \<Longrightarrow> init i = 1 / card (jondos - colls)"
  shows "\<I>(first_jondo ; last_ncoll) \<le> (1 - (h - 1) * J * p_f) * log 2 h"
proof -
  let "?il i l" = "\<P>(\<omega> in \<PP>. first_jondo \<omega> = i \<and> last_ncoll \<omega> = l \<bar> hit_colls \<omega> )"
  let "?i i" = "\<P>(\<omega> in \<PP>. first_jondo \<omega> = i \<bar> hit_colls \<omega> )"
  let "?l l" = "\<P>(\<omega> in \<PP>. last_ncoll \<omega> = l \<bar> hit_colls \<omega> )"

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
    have "first_jondo ` (UNIV \<rightarrow> valid_states) \<subseteq> jondos \<union> {jondo_of Start, jondo_of End}"
      by (auto simp: first_jondo_def Pi_iff jondo_of_def elim!: allE[of _ 0] valid_statesE)
    then show "finite (first_jondo ` (UNIV \<rightarrow> valid_states))"
      by (rule finite_subset) auto
  qed (auto simp: first_jondo_def)

  have sd_fj:
    "simple_distributed C first_jondo ?i"
    apply (rule C.simple_distributedI[OF sf_fj])
    apply (subst measure_C)
    apply simp
    apply (auto simp: first_jondo_def C_def vimage_def cond_prob_def Int_def conj_ac)
    done

  have sf_lnc: "simple_function C last_ncoll"
  proof (rule simple_functionI)
    have "last_ncoll ` (UNIV \<rightarrow> valid_states) \<subseteq> jondos \<union> {jondo_of Start, jondo_of End}"
      apply (auto simp: last_ncoll_def Pi_iff jondo_of_def)
      apply (erule_tac x="first_coll xa" in allE)
      apply (auto elim!: valid_statesE)
      done
    then show "finite (last_ncoll ` (UNIV \<rightarrow> valid_states))"
      by (rule finite_subset) auto
  qed auto

  have sd_lnc:
    "simple_distributed C last_ncoll ?l"
    apply (rule C.simple_distributedI[OF sf_lnc])
    apply (subst measure_C)
    apply simp
    apply (auto simp: C_def vimage_def cond_prob_def cong: conj_cong)
    done

  have sd_fj_lnc:
    "simple_distributed C (\<lambda>\<omega>. (first_jondo \<omega>, last_ncoll \<omega>)) (\<lambda>(i, l). ?il i l)"
    apply (rule C.simple_distributedI)
    apply (rule simple_function_Pair[OF sf_fj sf_lnc])
    apply (subst measure_C)
    apply (auto simp add: image_iff)
    apply (auto simp: first_jondo_def C_def vimage_def cond_prob_def)
    done

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
  also have "(\<Sum>i\<in>jondos - colls. ?inner i) =
      (\<Sum>(i, l)\<in>(first_jondo`space S_seq) \<times> (last_ncoll`space S_seq). ?il i l * log 2 (?il i l / (?i i * ?l l)))"
    unfolding setsum_cartesian_product
  proof (safe intro!: setsum_mono_zero_cong_left del: DiffE DiffI)
    show "finite ((first_jondo ` space S_seq) \<times> (last_ncoll ` space S_seq))"
      using sf_fj sf_lnc by (auto simp add: C_def dest!: simple_functionD(1))
  next
    fix i assume "i \<in> jondos - colls"
    then show "i \<in> first_jondo ` space S_seq" "i \<in> last_ncoll ` space S_seq"
      by (auto simp: space_PiM image_iff C_def last_ncoll_def first_jondo_def jondo_of_def intro!: bexI[of _ "\<lambda>_. Mix i"])
  next
    fix i l assume "(i, l) \<in> first_jondo ` space S_seq \<times> last_ncoll ` space S_seq - (jondos - colls) \<times> (jondos - colls)"
    then have "i \<notin> jondos - colls \<or> l \<notin> jondos - colls"
      by auto
    then have "\<P>(\<omega> in \<PP>. first_jondo \<omega> = i \<and> last_ncoll \<omega> = l \<and> hit_colls \<omega>) = 0"
      using AE_term
      apply (intro prob_eq_0_AE)
      apply (elim AE_mp)
      by (auto intro!: AE_I2 dest: term_imp_len first_collI4
        simp: first_jondo_def jondo_of_def)
    then show "?il i l * log 2 (?il i l / (?i i * ?l l)) = 0"
      by (simp add: cond_prob_def)
  qed
  also have "\<dots> = \<I>(first_jondo ; last_ncoll)"
    unfolding setsum_cartesian_product
    apply (subst C.mutual_information_simple_distributed[OF sd_fj sd_lnc sd_fj_lnc])
    apply (simp add: C_def)
  proof (safe intro!: setsum_mono_zero_right imageI)
    show "finite ((first_jondo ` space S_seq) \<times> (last_ncoll ` space S_seq))"
      using sf_fj sf_lnc by (auto simp add: C_def dest!: simple_functionD(1))
  next
    fix i l assume "(first_jondo i, last_ncoll l) \<notin> (\<lambda>x. (first_jondo x, last_ncoll x)) ` space S_seq"
    then have "{\<omega> \<in> space S_seq. first_jondo \<omega> = first_jondo i \<and> last_ncoll \<omega> = last_ncoll l \<and> hit_colls \<omega>} = {}"
      by (auto simp: image_iff)
    then have "?il (first_jondo i) (last_ncoll l) = 0"
      by (simp add: cond_prob_def del: Collect_empty_eq)
    then show "?il (first_jondo i) (last_ncoll l) *
      log 2 (?il (first_jondo i) (last_ncoll l) / (?i (first_jondo i) * ?l (last_ncoll l))) = 0"
      by simp
  qed
  finally show ?thesis by simp
qed

end

end
