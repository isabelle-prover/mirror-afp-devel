(* Author: Maximilian Schäffeler, adapted from Markov_Models.Discrete_Time_Markov_Process *)

section \<open>Discrete-Time Markov Decision Processes with Arbitrary State Spaces\<close>

text \<open>
  In this file we construct discrete-time Markov decision processes, 
  e.g. with arbitrary state spaces.
  Proofs and definitions are adapted from Markov\_Models.Discrete\_Time\_Markov\_Process.
\<close>

theory MDP_cont
  imports "HOL-Probability.Probability"
begin

lemma Ionescu_Tulcea_C_eq:
  assumes "\<And>i h. h \<in> space (PiM {0..<i} N) \<Longrightarrow> P i h = P' i h"
  assumes h: "Ionescu_Tulcea P N" "Ionescu_Tulcea P' N"
  shows "Ionescu_Tulcea.C P N 0 n (\<lambda>x. undefined) = Ionescu_Tulcea.C P' N 0 n (\<lambda>x. undefined)"
proof (induction n)
  case 0
  then show ?case using h by (auto simp: Ionescu_Tulcea.C_def)
next
  case (Suc n)
  have aux: "space (PiM {0..<0 + n} N) = space (rec_nat (\<lambda>n. return (Pi\<^sub>M {0..<n} N)) 
    (\<lambda>m ma n \<omega>. ma n \<omega> \<bind> Ionescu_Tulcea.eP P' N (n + m)) n 0 (\<lambda>x. undefined))"
    using h 
    by (subst Ionescu_Tulcea.space_C[symmetric, where P = P', where x = "(\<lambda>x. undefined)"]) 
      (auto simp add: Ionescu_Tulcea.C_def)  
  have "\<And>i h. h \<in> space (PiM {0..<i} N) \<Longrightarrow> Ionescu_Tulcea.eP P N i h = Ionescu_Tulcea.eP P' N i h"
    by (auto simp add: Ionescu_Tulcea.eP_def assms)
  then show ?case 
    using Suc.IH h
    using aux[symmetric]
    by (auto intro!: bind_cong simp: Ionescu_Tulcea.C_def)
qed

lemma Ionescu_Tulcea_CI_eq:
  assumes "\<And>i h. h \<in> space (PiM {0..<i} N) \<Longrightarrow> P i h = P' i h"
  assumes h: "Ionescu_Tulcea P N" "Ionescu_Tulcea P' N"
  shows "Ionescu_Tulcea.CI P N = Ionescu_Tulcea.CI P' N"
proof -
  have "\<And>J. Ionescu_Tulcea.CI P N J = Ionescu_Tulcea.CI P' N J"
    unfolding Ionescu_Tulcea.CI_def[OF h(1)] Ionescu_Tulcea.CI_def[OF h(2)]
    using assms 
    by (auto intro!: distr_cong Ionescu_Tulcea_C_eq)
  thus ?thesis by auto
qed

lemma measure_eqI_PiM_sequence:
  fixes M :: "nat \<Rightarrow> 'a measure"
  assumes *[simp]: "sets P = PiM UNIV M" "sets Q = PiM UNIV M"
  assumes eq: "\<And>A n. (\<And>i. A i \<in> sets (M i)) \<Longrightarrow>
    P (prod_emb UNIV M {..n} (Pi\<^sub>E {..n} A)) = Q (prod_emb UNIV M {..n} (Pi\<^sub>E {..n} A))"
  assumes A: "finite_measure P"
  shows "P = Q"
proof (rule measure_eqI_PiM_infinite[OF * _ A])
  fix J :: "nat set" and F'
  assume J: "finite J" "\<And>i. i \<in> J \<Longrightarrow> F' i \<in> sets (M i)"

  define n where "n = (if J = {} then 0 else Max J)"
  define F where "F i = (if i \<in> J then F' i else space (M i))" for i
  then have F[simp, measurable]: "F i \<in> sets (M i)" for i
    using J by auto
  have emb_eq: "prod_emb UNIV M J (Pi\<^sub>E J F') = prod_emb UNIV M {..n} (Pi\<^sub>E {..n} F)"
  proof cases
    assume "J = {}" then show ?thesis
      by (auto simp add: n_def F_def[abs_def] prod_emb_def PiE_def)
  next
    assume "J \<noteq> {}" then show ?thesis
      by (auto simp: prod_emb_def PiE_iff F_def n_def less_Suc_eq_le \<open>finite J\<close> split: if_split_asm)
  qed

  show "emeasure P (prod_emb UNIV M J (Pi\<^sub>E J F')) = emeasure Q (prod_emb UNIV M J (Pi\<^sub>E J F'))"
    unfolding emb_eq by (rule eq) fact
qed

lemma distr_cong_simp:
  "M = K \<Longrightarrow> sets N = sets L \<Longrightarrow> (\<And>x. x \<in> space M =simp=> f x = g x) \<Longrightarrow> distr M N f = distr K L g"
  unfolding simp_implies_def by (rule distr_cong)

subsection \<open>Definition and Basic Properties\<close>

locale discrete_MDP =
  fixes Ms :: "'s measure"
    and Ma :: "'a measure"
    and A :: "'s \<Rightarrow> 'a set"
    and K :: "'s \<times> 'a \<Rightarrow> 's measure"
    (* The valid actions are measurable subsets of all actions *)
  assumes A_s: "\<And>s. A s \<in> sets Ma"
    (* There always exists a valid action *)
  assumes A_ne: "\<And>s. A s \<noteq> {}"
    (* Assume the existence of at least 1 policy *)
  assumes ex_pol: "\<exists>\<delta> \<in> Ms \<rightarrow>\<^sub>M Ma. \<forall>s. \<delta> s \<in> A s"
    (* The kernel maps a state-action pair to a distribution over states *)
  assumes K[measurable]: "K \<in> Ms \<Otimes>\<^sub>M Ma \<rightarrow>\<^sub>M prob_algebra Ms"
begin

lemma space_prodI[intro]: "x \<in> space A' \<Longrightarrow> y \<in> space B \<Longrightarrow> (x,y) \<in> space (A' \<Otimes>\<^sub>M B)"
  by (auto simp add: space_pair_measure)

abbreviation "M \<equiv> Ms \<Otimes>\<^sub>M Ma"
abbreviation "Ma_A s \<equiv> restrict_space Ma (A s)"

lemma space_ma[intro]: "s \<in> space Ms \<Longrightarrow> a \<in> space Ma \<Longrightarrow> (s,a) \<in> space M"
  by (simp add: space_pair_measure)

lemma space_x0[simp]: "x0 \<in> space (prob_algebra Ms) \<Longrightarrow> space x0 = space Ms"
  by (metis (mono_tags, lifting) space_prob_algebra mem_Collect_eq sets_eq_imp_space_eq)

lemma A_subs_Ma: "A s \<subseteq> space Ma"
  by (simp add: A_s sets.sets_into_space)

lemma space_Ma_A_subset: "s \<in> space Ms \<Longrightarrow> space (Ma_A s) \<subseteq> A s"
  by (simp add: space_restrict_space)

lemma K_restrict [measurable]: "K \<in> (Ms \<Otimes>\<^sub>M Ma_A s) \<rightarrow>\<^sub>M prob_algebra Ms"
  by measurable (metis measurable_id measurable_pair_iff measurable_restrict_space2_iff)

lemma measurable_K_act[measurable, intro]: "s \<in> space Ms \<Longrightarrow> (\<lambda>a. K (s, a)) \<in> Ma \<rightarrow>\<^sub>M prob_algebra Ms"
  by measurable

lemma measurable_K_st[measurable, intro]: "a \<in> space Ma \<Longrightarrow> (\<lambda>s. K (s, a)) \<in> Ms \<rightarrow>\<^sub>M prob_algebra Ms"
  by measurable

lemma space_K[simp]: "sa \<in> space M \<Longrightarrow> space (K sa) = space Ms"
  using K unfolding prob_algebra_def measurable_restrict_space2_iff
  by (auto dest: subprob_measurableD)

lemma space_K2[simp]: "s \<in> space Ms \<Longrightarrow> a \<in> space Ma \<Longrightarrow> space (K (s, a)) = space Ms"
  by (simp add: space_pair_measure)

lemma space_K_E: "s' \<in> space (K (s,a)) \<Longrightarrow> s \<in> space Ms \<Longrightarrow> a \<in> space Ma \<Longrightarrow> s' \<in> space Ms"
  by auto

lemma sets_K: "sa \<in> space M \<Longrightarrow> sets (K sa) = sets Ms"
  using K unfolding prob_algebra_def unfolding measurable_restrict_space2_iff
  by (auto dest: subprob_measurableD)

lemma sets_K'[measurable_cong]: "s \<in> space Ms \<Longrightarrow> a \<in> space Ma \<Longrightarrow> sets (K (s,a)) = sets Ms"
  by (simp add: sets_K space_pair_measure)

lemma prob_space_K[intro]: "sa \<in> space M \<Longrightarrow> prob_space (K sa)"
  using measurable_space[OF K] by (simp add: space_prob_algebra)

lemma prob_space_K2[intro]: "s \<in> space Ms \<Longrightarrow> a \<in> space Ma \<Longrightarrow> prob_space (K (s,a))"
  using prob_space_K by (simp add: space_pair_measure)

lemma K_in_space [intro]: "m \<in> space M \<Longrightarrow> K m \<in> space (prob_algebra Ms)"
  by (meson K measurable_space)

subsection \<open>Policies\<close>
  (* This section represents our own developments. *)

type_synonym ('c, 'd) pol = "nat \<Rightarrow> ((nat \<Rightarrow> 'c \<times> 'd) \<times> 'c) \<Rightarrow> 'd measure"

(* History of i steps *)
abbreviation "H i \<equiv> Pi\<^sub>M {0..<i} (\<lambda>_. M)"
  (* + current state *)
abbreviation "Hs i \<equiv>  H i \<Otimes>\<^sub>M Ms"

lemma space_H1: "j < (i :: nat)  \<Longrightarrow> \<omega> \<in> space (H i) \<Longrightarrow> \<omega> j \<in> space M"
  using PiE_def 
  by (auto simp: space_PiM)

lemma space_case_nat[intro]: 
  assumes "\<omega> \<in> space (H i)" "s \<in> space Ms"  
  shows "case_nat s (fst \<circ> \<omega>) i \<in> space Ms"
  using assms 
  by (cases i) (auto intro!: space_H1 measurable_space[OF measurable_fst])

lemma undefined_in_H0: "(\<lambda>_. undefined) \<in> space (H (0 :: nat))"
  by auto

lemma sets_K_Suc[measurable_cong]: "h \<in> space (H (Suc n)) \<Longrightarrow> sets (K (h n)) = sets Ms"
  using sets_K space_H1 by blast

text\<open>A decision rule is a function from states to distributions over enabled actions.\<close>
definition "is_dec0 d \<equiv> d \<in> Ms \<rightarrow>\<^sub>M prob_algebra Ma "

definition "is_dec (t :: nat) d \<equiv> (d \<in> Hs t \<rightarrow>\<^sub>M prob_algebra Ma) "

lemma "is_dec0 d \<Longrightarrow> is_dec t (\<lambda>(_,s). d s)"
  unfolding is_dec0_def is_dec_def by auto

text\<open>A policy is a function from histories to valid decision rules.\<close>
definition is_policy :: "('s, 'a) pol \<Rightarrow> bool" where
  "is_policy p \<equiv> \<forall>i. is_dec i (p i)"

(* selects the next action without history *)
abbreviation p0 :: "('s, 'a) pol \<Rightarrow> 's \<Rightarrow> 'a measure" where
  "p0 p s \<equiv> p (0 ::nat) (\<lambda>_. undefined, s)"

context
  fixes p assumes p[simp]: "is_policy p"
begin

lemma is_policyD[measurable]: "p i \<in> Hs i \<rightarrow>\<^sub>M prob_algebra Ma"
  using p unfolding is_policy_def is_dec_def by auto

lemma space_policy[simp]: "hs \<in> space (Hs i) \<Longrightarrow> space (p i hs) = space Ma"
  using K is_policyD unfolding prob_algebra_def measurable_restrict_space2_iff
  by (auto dest: subprob_measurableD)

lemma space_policy'[simp]: "h \<in> space (H i) \<Longrightarrow> s \<in> space Ms \<Longrightarrow> space (p i (h,s)) = space Ma"
  using space_policy 
  by (simp add: space_pair_measure)

lemma space_policyI[intro]: 
  assumes "s \<in> space Ms" "h \<in> space (H i)" "a \<in> space Ma"
  shows "a \<in> space (p i (h,s))"
  using space_policy assms 
  by (auto simp: space_pair_measure)

lemma sets_policy[simp]: "hs \<in> space (Hs i) \<Longrightarrow> sets (p i hs) = sets Ma"
  using p K is_policyD
  unfolding prob_algebra_def measurable_restrict_space2_iff
  by (auto dest: subprob_measurableD)

lemma sets_policy'[measurable_cong, simp]: 
  "h \<in> space (H i) \<Longrightarrow> s \<in> space Ms \<Longrightarrow> sets (p i (h,s)) = sets Ma"
  using sets_policy 
  by (auto simp: space_pair_measure)

lemma sets_policy''[measurable_cong, simp]: 
  "h \<in> space ((Pi\<^sub>M {} (\<lambda>_. M))) \<Longrightarrow> s \<in> space Ms \<Longrightarrow> sets (p 0 (h,s)) = sets Ma"
  using sets_policy 
  by (auto simp: space_pair_measure)

lemma policy_prob_space: "hs \<in> space (Hs i) \<Longrightarrow> prob_space (p i hs)"
proof -
  assume h: "hs \<in> space (Hs i)"
  hence "p i hs \<in> space (prob_algebra Ma)" 
    using p by (auto intro: measurable_space)
  thus "prob_space (p i hs)"
    unfolding prob_algebra_def by (simp add: space_restrict_space)
qed

lemma policy_prob_space': "h \<in> space (H i) \<Longrightarrow> s \<in> space Ms \<Longrightarrow> prob_space (p i (h,s))"
  using policy_prob_space by (simp add: space_pair_measure)

lemma prob_space_p0: "x \<in> space Ms \<Longrightarrow> prob_space (p0 p x)"
  by (simp add: policy_prob_space')

lemma p0_sets[measurable_cong]: "x \<in> space Ms \<Longrightarrow> sets (p 0 (\<lambda>_. undefined,x)) = sets Ma"
  using subprob_measurableD(2) measurable_prob_algebraD by simp

lemma space_p0[simp]: "s \<in> space Ms \<Longrightarrow> space (p0 p s) = space Ma"
  by auto

lemma return_policy_prob_algebra [measurable]: 
  "h \<in> space (H n) \<Longrightarrow> x \<in> space Ms \<Longrightarrow> (\<lambda>a. return M (x, a)) \<in> p n (h, x) \<rightarrow>\<^sub>M prob_algebra M"
  by measurable
end

subsection \<open>Successor Policy\<close>
text \<open>To shift the policy by one step, we provide a single state-action pair as history\<close>
definition "Suc_policy p sa = (\<lambda>i (h, s). p (Suc i) (\<lambda>i'. case_nat sa h i', s))"

lemma p_as_Suc_policy: "p (Suc i) (h, s) = Suc_policy p ((h 0)) i (\<lambda>i. h (Suc i), s)"
proof -
  have *: "case_nat (f 0) (\<lambda>i. f (Suc i)) = f" for f
    by (auto split: nat.splits)
  show ?thesis
    unfolding Suc_policy_def
    by (auto simp: *)
qed

lemma is_policy_Suc_policy[intro]:
  assumes s: "sa \<in> space M" and p: "is_policy p"
  shows "is_policy (Suc_policy p sa)"
proof -
  have *: "(\<lambda>x. case_nat sa (fst x)) \<in> Pi\<^sub>M {0..<i} (\<lambda>_. M) \<Otimes>\<^sub>M Ms \<rightarrow>\<^sub>M Pi\<^sub>M {0..<Suc i} (\<lambda>_. M)" for i
    using s space_H1
    by (intro  measurable_PiM_single) (fastforce simp: space_PiM space_pair_measure split: nat.splits)+
  have "\<And>i. p i \<in> Pi\<^sub>M {0..<i} (\<lambda>_. M) \<Otimes>\<^sub>M Ms \<rightarrow>\<^sub>M prob_algebra Ma"
    using is_policyD p by blast
  hence "\<And>i. Suc_policy p sa i \<in> Pi\<^sub>M {0..<i} (\<lambda>_. M) \<Otimes>\<^sub>M Ms \<rightarrow>\<^sub>M prob_algebra Ma"
    unfolding Suc_policy_def
    using *
    by measurable
  thus ?thesis unfolding is_policy_def is_dec_def
    by blast
qed

lemma Suc_policy_measurable_step[measurable]: 
  assumes "is_policy p"
  shows "(\<lambda>x. Suc_policy p (fst (fst x)) n (snd (fst x), snd x)) \<in> 
    (M \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M)) \<Otimes>\<^sub>M Ms \<rightarrow>\<^sub>M prob_algebra Ma"
  unfolding Suc_policy_def
  using assms
  by measurable (auto 
      intro: measurable_PiM_single' 
      simp:  space_pair_measure PiE_iff space_PiM extensional_def 
      split: nat.split)

subsection \<open>Single-Step Distribution\<close>

text\<open>@{term "K'"} takes 
  a policy, 
  a distribution over 's, 
  the epoch,
  and a history, 
  produces a distribution over the next state-action pair.\<close>
definition K' :: "('s, 'a) pol \<Rightarrow> 's measure \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> ('s \<times> 'a)) \<Rightarrow> ('s \<times> 'a) measure"
  where
    "K' p s0 n \<omega> = do {
    s \<leftarrow> case_nat s0 (K \<circ> \<omega>) n;
    a \<leftarrow> p n (\<omega>, s);
    return M (s, a)
}"

lemma prob_space_K': 
  assumes p: "is_policy p" and x: "x0 \<in> space (prob_algebra Ms)" and h: "h \<in> space (H n)" 
  shows "prob_space (K' p x0 n h)"
  unfolding K'_def
proof (intro prob_space.prob_space_bind[where S = M])
  show "prob_space (case n of 0 \<Rightarrow> x0 | Suc x \<Rightarrow> (K \<circ> h) x)"
    using x h space_H1 by (auto split: nat.splits simp: space_prob_algebra)
next
  show "AE x in case n of 0 \<Rightarrow> x0 | Suc x \<Rightarrow> (K \<circ> h) x. 
    prob_space (p n (h, x) \<bind> (\<lambda>a. return M (x, a)))"
  proof (cases n)
    case 0
    then have h': "h \<in> space (Pi\<^sub>M {0..<0} (\<lambda>_. M))"
      using h by auto
    show ?thesis 
      using 0 p h x sets_policy'
      by (fastforce intro: prob_space.prob_space_bind[where S=M] 
          policy_prob_space prob_space_return 
          cong: measurable_cong_sets)
  next
    case (Suc nat)
    then show ?thesis
    proof (intro AE_I2 prob_space.prob_space_bind[of _ _ M], goal_cases)
      case (1 x)
      then show ?case 
        using p space_H1 h x
        by (fastforce intro!: policy_prob_space)
    next
      case (2 x a)
      then show ?case 
        using h p space_H1
        by (fastforce intro!: prob_space_return)
    next
      case (3 x)
      then show ?case
        using p h x space_K space_H1
        by (fastforce intro!: measurable_prob_algebraD return_policy_prob_algebra)
    qed
  qed
next
  show "(\<lambda>s. p n (h, s) \<bind> (\<lambda>a. return M (s, a))) \<in> 
    (case n of 0 \<Rightarrow> x0 | Suc x \<Rightarrow> (K \<circ> h) x) \<rightarrow>\<^sub>M subprob_algebra M"
  proof (intro measurable_bind[where N = Ma])
    show " (\<lambda>x. p n (h, x)) \<in> (case n of 0 \<Rightarrow> x0 | Suc x \<Rightarrow> (K \<circ> h) x) \<rightarrow>\<^sub>M subprob_algebra Ma"
      using p h x 
      by (auto split: nat.splits intro!: measurable_prob_algebraD simp: space_prob_algebra)
  next
    show "(\<lambda>s. return M (fst s, snd s)) \<in> 
      (case n of 0 \<Rightarrow> x0 | Suc x \<Rightarrow> (K \<circ> h) x) \<Otimes>\<^sub>M Ma \<rightarrow>\<^sub>M subprob_algebra M"
      using h x sets_K_Suc
      by (auto split: nat.splits simp: sets_K space_prob_algebra cong: measurable_cong_sets)
  qed
qed

lemma measurable_K'[measurable]:
  assumes p: "is_policy p" and x: "x \<in> space (prob_algebra Ms)" 
  shows "K' p x i \<in> H i \<rightarrow>\<^sub>M prob_algebra M"
proof -
  fix i
  show "K' p x i \<in> Pi\<^sub>M {0..<i} (\<lambda>_. M) \<rightarrow>\<^sub>M prob_algebra M"
    unfolding K'_def
  proof (intro measurable_bind_prob_space2[where N = Ms])
    show "(\<lambda>a. case i of 0 \<Rightarrow> x | Suc x \<Rightarrow> (K \<circ> a) x) \<in> Pi\<^sub>M {0..<i} (\<lambda>_. M) \<rightarrow>\<^sub>M prob_algebra Ms"
      using x by measurable auto
  next 
    show "(\<lambda>(\<omega>, y). p i (\<omega>, y) \<bind> (\<lambda>a. return M (y, a))) \<in> 
      Pi\<^sub>M {0..<i} (\<lambda>_. M) \<Otimes>\<^sub>M Ms \<rightarrow>\<^sub>M prob_algebra M"
      using x p by auto
  qed
qed

subsection \<open>Initial State-Action Distribution\<close>

text \<open>@{term "K0"} produces the initial state-action distribution from a state distribution
 and a policy.\<close>

definition "K0 p s0 = K' p s0 0 (\<lambda>_. undefined)"

lemma K0_def':
  "K0 p s0 = do {
    s \<leftarrow> s0;
    a \<leftarrow> p0 p s;
    return M (s, a)}"
  unfolding K0_def K'_def by auto

lemma K0_prob[measurable]: "is_policy p \<Longrightarrow> K0 p \<in> prob_algebra Ms \<rightarrow>\<^sub>M prob_algebra M"
  unfolding K0_def' 
  by measurable

lemma prob_space_K0: "is_policy p \<Longrightarrow> x0 \<in> space (prob_algebra Ms) \<Longrightarrow> prob_space (K0 p x0)"
  by (simp add: K0_def prob_space_K')

lemma space_K0[simp]: "is_policy p \<Longrightarrow> s \<in> space (prob_algebra Ms) \<Longrightarrow> space (K0 p s) = space M"
  by (meson K0_prob measurable_prob_algebraD sets_eq_imp_space_eq sets_kernel)

lemma sets_K0[measurable_cong]:
  assumes "is_policy p" "s \<in> space (prob_algebra Ms)" 
  shows "sets (K0 p s) = sets M"
  using assms by (meson K0_prob measurable_prob_algebraD subprob_measurableD(2))

lemma K0_return_eq_p0: 
  assumes "is_policy p" "s \<in> space Ms" 
  shows "K0 p (return Ms s) = p0 p s \<bind> (\<lambda>a. return M (s,a))"
  unfolding K0_def'
  using assms
  by (subst bind_return[where N = M]) (auto intro!: measurable_prob_algebraD)

lemma M_ne_policy[intro]: "is_policy p \<Longrightarrow> s \<in> space (prob_algebra Ms) \<Longrightarrow> space M \<noteq> {}"
  using space_K0 prob_space.not_empty prob_space_K0
  by force

subsection \<open>Sequence Space of the MDP\<close>
text\<open>We can instantiate @{const Ionescu_Tulcea} with @{const K'}.\<close>
lemma IT_K': "is_policy p \<Longrightarrow> x \<in> space (prob_algebra Ms) \<Longrightarrow> Ionescu_Tulcea (K' p x) (\<lambda>_. M)"
  unfolding Ionescu_Tulcea_def using measurable_K' prob_space_K'
  by (fast dest: measurable_prob_algebraD)

definition lim_sequence :: "('s, 'a) pol \<Rightarrow> 's measure \<Rightarrow> (nat \<Rightarrow> ('s \<times> 'a)) measure"
  where
    "lim_sequence p x = projective_family.lim UNIV (Ionescu_Tulcea.CI (K' p x) (\<lambda>_. M)) (\<lambda>_. M)"

lemma
  assumes x: "x \<in> space (prob_algebra Ms)" and p: "is_policy p"
  shows space_lim_sequence: "space (lim_sequence p x) = space (\<Pi>\<^sub>M i\<in>UNIV. M)"
    and sets_lim_sequence[measurable_cong]: "sets (lim_sequence p x) = sets (\<Pi>\<^sub>M i\<in>UNIV. M)"
    and emeasure_lim_sequence_emb: "\<And>J X. finite J \<Longrightarrow> X \<in> sets (\<Pi>\<^sub>M j\<in>J. M) \<Longrightarrow>
      emeasure (lim_sequence p x) (prod_emb UNIV (\<lambda>_. M) J X) =
      emeasure (Ionescu_Tulcea.CI (K' p x) (\<lambda>_. M) J) X"
    and emeasure_lim_sequence_emb_I0o: "\<And>n X. X \<in> sets (\<Pi>\<^sub>M i \<in> {0..<n}. M) \<Longrightarrow>
      emeasure (lim_sequence p x) (prod_emb UNIV (\<lambda>_. M) {0..<n} X) =
      emeasure (Ionescu_Tulcea.C (K' p x) (\<lambda>_. M) 0 n (\<lambda>x. undefined)) X"
proof -
  interpret Ionescu_Tulcea "K' p x" "\<lambda>_. M"
    using IT_K'[OF p x] .
  show "space (lim_sequence p x) = space (\<Pi>\<^sub>M i\<in>UNIV. M)"
    unfolding lim_sequence_def by simp
  show "sets (lim_sequence p x) = sets (\<Pi>\<^sub>M i\<in>UNIV. M)"
    unfolding lim_sequence_def by simp

  { fix J :: "nat set" and X assume "finite J" "X \<in> sets (\<Pi>\<^sub>M j\<in>J. M)"
    then show "emeasure (lim_sequence p x) (PF.emb UNIV J X) = emeasure (CI J) X"
      unfolding lim_sequence_def by (rule lim) }
  note emb = this

  have up_to_I0o[simp]: "up_to {0..<n} = n" for n
    unfolding up_to_def by (rule Least_equality) auto

  { fix n :: nat and X assume "X \<in> sets (\<Pi>\<^sub>M j\<in>{0..<n}. M)"
    thus "emeasure (lim_sequence p x) (PF.emb UNIV {0..<n} X) = emeasure (C 0 n (\<lambda>x. undefined)) X"
      by (simp add: space_C emb CI_def space_PiM distr_id2 sets_C cong: distr_cong_simp) }
qed

lemma lim_sequence_prob_space: 
  assumes "is_policy p" "s \<in> space (prob_algebra Ms)" 
  shows "prob_space (lim_sequence p s)"
  using assms proof -
  assume p: "is_policy p"
  fix s assume [simp]: "s \<in> space (prob_algebra Ms)"
  interpret Ionescu_Tulcea "K' p s" "\<lambda>_. M"
    using IT_K' p by simp
  have sp: 
    "space (lim_sequence p s) = prod_emb UNIV (\<lambda>_. M) {} (\<Pi>\<^sub>E j\<in>{}. space M)" 
    "space (CI {}) = {} \<rightarrow>\<^sub>E space M"
    by (auto simp: p space_lim_sequence space_PiM prod_emb_def PF.space_P)
  show "prob_space (lim_sequence p s)"
    using PF.prob_space_P[THEN prob_space.emeasure_space_1, of "{}"]
    by (auto intro!: prob_spaceI simp add: p sp emeasure_lim_sequence_emb simp del: PiE_empty_domain)
qed

subsection \<open>Measurablility of the Sequence Space\<close>
lemma lim_sequence[measurable]: 
  assumes p: "is_policy p"  
  shows "lim_sequence p \<in> prob_algebra Ms \<rightarrow>\<^sub>M prob_algebra (\<Pi>\<^sub>M i\<in>UNIV. M)"
proof (intro measurable_prob_algebra_generated[OF sets_PiM Int_stable_prod_algebra 
      prod_algebra_sets_into_space])
  show "\<And>a. a \<in> space (prob_algebra Ms) \<Longrightarrow> prob_space (lim_sequence p a)"
    using lim_sequence_prob_space p by blast
next
  fix a assume [simp]: "a \<in> space (prob_algebra Ms)"
  show "sets (lim_sequence p a) = sets (Pi\<^sub>M UNIV (\<lambda>i. M))"
    by (simp add: p sets_lim_sequence)
next
  fix X :: "(nat \<Rightarrow> 's \<times> 'a) set" assume "X \<in> prod_algebra UNIV (\<lambda>i. M)"
  then obtain J :: "nat set" and F where J: "J \<noteq> {}" "finite J" "F \<in> J \<rightarrow> sets M"
    and X: "X = prod_emb UNIV (\<lambda>_. M) J (Pi\<^sub>E J F)"
    unfolding prod_algebra_def by auto
  then have Pi_F: "finite J" "Pi\<^sub>E J F \<in> sets (Pi\<^sub>M J (\<lambda>_. M))"
    by (auto intro: sets_PiM_I_finite)

  define n where "n = (LEAST n. \<forall>i\<ge>n. i \<notin> J)"
  have J_le_n: "J \<subseteq> {0..<n}"
  proof -
    have "\<And>x. x \<in> J \<Longrightarrow> \<forall>i\<ge>Suc (Max J). i \<notin> J"
      using not_le Max_less_iff[OF \<open>finite J\<close>]
      by (auto simp: Suc_le_eq)
    moreover have "x \<in> J \<Longrightarrow> \<forall>i\<ge>a. i \<notin> J \<Longrightarrow> x < a" for x a
      using not_le by auto
    ultimately show ?thesis
      unfolding n_def
      by (fastforce intro!: LeastI2[of  "\<lambda>n. \<forall>i\<ge>n. i \<notin> J" "Suc (Max J)" "\<lambda>x. _ < x"])
  qed

  have C: "(\<lambda>x. Ionescu_Tulcea.C (K' p x) (\<lambda>_. M) 0 n (\<lambda>x. undefined)) \<in> prob_algebra Ms \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M {0..<n} (\<lambda>_. M))"
  proof (induction n)
    case 0
    thus ?case 
      by (auto simp: measurable_cong[OF Ionescu_Tulcea.C.simps(1)[OF IT_K', OF p]])
  next
    case (Suc n)
    have "(\<lambda>w. Ionescu_Tulcea.eP (K' p (fst w)) (\<lambda>_. M) n (snd w))
    \<in> prob_algebra Ms \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M) \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M {0..<Suc n} (\<lambda>_. M))"
    proof (subst measurable_cong)
      fix w assume "w \<in> space (prob_algebra Ms \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M))"
      then show "Ionescu_Tulcea.eP (K' p (fst w)) (\<lambda>_. M) n (snd w) = 
      distr (K' p (fst w) n (snd w)) (\<Pi>\<^sub>M i\<in>{0..<Suc n}. M) (fun_upd (snd w) n)"
        by (auto simp: p space_pair_measure Ionescu_Tulcea.eP_def[OF IT_K'] split: prod.split)
    next
      show "(\<lambda>w. distr (K' p (fst w) n (snd w)) (\<Pi>\<^sub>M i\<in>{0..<Suc n}. M) (fun_upd (snd w) n))
        \<in> prob_algebra Ms \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M) \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M {0..<Suc n} (\<lambda>_. M))"
      proof (rule measurable_distr2[where M = M])
        show "(\<lambda>(x, y). (snd x)(n := y)) \<in> (prob_algebra Ms \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M)) \<Otimes>\<^sub>M M \<rightarrow>\<^sub>M Pi\<^sub>M {0..<Suc n} (\<lambda>i. M)"
        proof (rule measurable_PiM_single')
          fix i assume "i \<in> {0..<Suc n}"
          then show "(\<lambda>\<omega>. (case \<omega> of (x, y) \<Rightarrow> (snd x)(n := y)) i) \<in> (prob_algebra Ms \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M)) \<Otimes>\<^sub>M M \<rightarrow>\<^sub>M M"
            unfolding split_beta' by (cases "i = n") auto
        next
          show "(\<lambda>\<omega>. case \<omega> of (x, y) \<Rightarrow> (snd x)(n := y)) \<in> space ((prob_algebra Ms \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M)) \<Otimes>\<^sub>M M) \<rightarrow> {0..<Suc n} \<rightarrow>\<^sub>E space M"
            by (auto simp: space_pair_measure space_PiM less_Suc_eq PiE_iff)
        qed
      next
        show "(\<lambda>x. K' p (fst x) n (snd x)) \<in> prob_algebra Ms \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M) \<rightarrow>\<^sub>M subprob_algebra M"
          unfolding K'_def comp_def
          using p
          by (auto intro!: measurable_prob_algebraD)
      qed
    qed
    then show ?case
      using Suc.IH
      by (subst measurable_cong[OF Ionescu_Tulcea.C.simps(2)[OF IT_K', where p1 = p, OF p]])
        (auto intro!: measurable_bind)
  qed
  have *: "(\<lambda>x. Ionescu_Tulcea.CI (K' p x) (\<lambda>_. M) J) \<in> prob_algebra Ms \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M J (\<lambda>_. M))"
    using measurable_distr[OF measurable_restrict_subset[OF J_le_n], of "(\<lambda>_. M)"] C p
    by (subst measurable_cong) 
      (auto simp: Ionescu_Tulcea.up_to_def[OF IT_K'] n_def Ionescu_Tulcea.CI_def[OF IT_K'])
  have "(\<lambda>a. emeasure (lim_sequence p a) X) \<in> borel_measurable (prob_algebra Ms) \<longleftrightarrow>
    (\<lambda>a. emeasure (Ionescu_Tulcea.CI (K' p a) (\<lambda>_. M) J) (Pi\<^sub>E J F)) \<in> 
      borel_measurable (prob_algebra Ms)"
    unfolding X using J Pi_F by (intro p measurable_cong emeasure_lim_sequence_emb) auto
  also have "\<dots>"
    using * measurable_emeasure_subprob_algebra Pi_F(2) by auto
  finally show "(\<lambda>a. emeasure (lim_sequence p a) X) \<in> borel_measurable (prob_algebra Ms)" .
qed

lemma lim_sequence_aux[measurable]: 
  assumes p: "is_policy p"
  assumes f : "\<And>x. x \<in> space M \<Longrightarrow> is_policy (f x)" 
  assumes f': "\<And>n. (\<lambda>x. f (fst (fst x)) n (snd (fst x), snd x)) \<in> 
    (M \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M)) \<Otimes>\<^sub>M Ms \<rightarrow>\<^sub>M prob_algebra Ma"
  assumes gm: "g \<in> M \<rightarrow>\<^sub>M prob_algebra Ms"
  shows "(\<lambda>x. lim_sequence (f x) (g x)) \<in> M \<rightarrow>\<^sub>M prob_algebra (Pi\<^sub>M UNIV (\<lambda>_. M))"
proof (intro measurable_prob_algebra_generated[OF sets_PiM Int_stable_prod_algebra prod_algebra_sets_into_space])
  fix a assume a[simp]: "a \<in> space M"
  have g: "\<And>x. x \<in> space M \<Longrightarrow> g x \<in> space (prob_algebra Ms)"
    by (meson gm measurable_space)
  interpret Ionescu_Tulcea "K' (f a) (g a)" "\<lambda>_. M"
    using IT_K' p
    using f[OF \<open>a \<in> space M\<close>] g by measurable
  have p': "is_policy (f a)"
    using \<open>a \<in> space M\<close> p f by auto
  have sp: 
    "space (lim_sequence (f a) (g a)) = prod_emb UNIV (\<lambda>_. M) {} (\<Pi>\<^sub>E j\<in>{}. space M)" 
    "space (CI {}) = {} \<rightarrow>\<^sub>E space M"
    using g a p' by (auto simp: space_lim_sequence p' space_PiM prod_emb_def PF.space_P)
  have "emeasure (lim_sequence (f a) (g a)) (space (lim_sequence (f a) (g a))) = 1"
    unfolding sp
    using g a p' sets.top[of "(Pi\<^sub>M {} (\<lambda>_. M))", unfolded space_PiM_empty] 
      PF.prob_space_P[THEN prob_space.emeasure_space_1, of "{}"]
    by (subst emeasure_lim_sequence_emb) (auto simp: emeasure_lim_sequence_emb sp)
  thus "prob_space (lim_sequence (f a) (g a))"
    by (auto intro: prob_spaceI)
  show "sets (lim_sequence (f a) (g a)) = sets (Pi\<^sub>M UNIV (\<lambda>i. M))"
    by (simp add: lim_sequence_def)
next
  fix X :: "(nat \<Rightarrow> 's \<times> 'a) set" assume "X \<in> prod_algebra UNIV (\<lambda>i. M)"
  then obtain J :: "nat set" and F where J: "J \<noteq> {}" "finite J" "F \<in> J \<rightarrow> sets M"
    and X: "X = prod_emb UNIV (\<lambda>_. M) J (Pi\<^sub>E J F)"
    unfolding prod_algebra_def by auto
  then have Pi_F: "finite J" "Pi\<^sub>E J F \<in> sets (Pi\<^sub>M J (\<lambda>_. M))"
    by (auto intro: sets_PiM_I_finite)

  define n where "n = (LEAST n. \<forall>i\<ge>n. i \<notin> J)"
  have J_le_n: "J \<subseteq> {0..<n}"
    unfolding n_def
    by (rule LeastI2[of _ "Suc (Max J)"]) (auto simp: \<open>finite J\<close> Suc_le_eq not_le[symmetric])

  have g: "\<And>x. x \<in> space M \<Longrightarrow> g x \<in> space (prob_algebra Ms)"
    by (meson gm measurable_space)

  have C: "(\<lambda>x. Ionescu_Tulcea.C (K' (f x) (g x)) (\<lambda>_. M) 0 n (\<lambda>x. undefined)) \<in> 
    M \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M {0..<n} (\<lambda>_. M))"
  proof (induction n)
    case 0
    then show ?case
      using g f
      by (auto simp: measurable_cong[OF  Ionescu_Tulcea.C.simps(1)[OF IT_K']])
  next
    case (Suc n)
    then show ?case
    proof (subst measurable_cong[OF Ionescu_Tulcea.C.simps(2)[OF IT_K']])
      show "(\<lambda>w. Ionescu_Tulcea.C (K' (f w) (g w)) (\<lambda>_. M) 0 n (\<lambda>x. undefined) \<bind> Ionescu_Tulcea.eP (K' (f w) (g w)) (\<lambda>_. M) (0 + n))
    \<in> M \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M {0..<Suc n} (\<lambda>_. M))"
        if h: "(\<lambda>x. Ionescu_Tulcea.C (K' (f x) (g x)) (\<lambda>_. M) 0 n (\<lambda>x. undefined)) \<in> M \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M {0..<n} (\<lambda>_. M))"
      proof (rule measurable_bind'[OF h])
        show "(\<lambda>(x, y). Ionescu_Tulcea.eP (K' (f x) (g x)) (\<lambda>_. M) (0 + n) y) \<in> M \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M) \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M {0..<Suc n} (\<lambda>_. M))"
        proof (subst measurable_cong)
          fix n :: nat and w assume "w \<in> space (M \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M))"
          then show "(case w of (x, a) \<Rightarrow> Ionescu_Tulcea.eP (K' (f x) (g x)) (\<lambda>_. M) (0 + n) a) =
          (case w of (x, a) \<Rightarrow> distr (K' (f x) (g x) n a) (\<Pi>\<^sub>M i\<in>{0..<Suc n}. M) (fun_upd a n))"
            by (auto simp: IT_K' Ionescu_Tulcea.eP_def f g space_ma p space_pair_measure 
                Ionescu_Tulcea.eP_def[OF IT_K'])
        next
          fix n 
          have "(\<lambda>w. distr (K' (f (fst w)) (g (fst w)) n (snd w)) (Pi\<^sub>M {0..<Suc n} (\<lambda>i. M)) (fun_upd (snd w) n))
              \<in> M \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M) \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M {0..<Suc n} (\<lambda>_. M))"
          proof (intro measurable_distr2[where M=M] measurable_PiM_single', goal_cases)
            case (1 i)
            then show ?case
              by (cases "i = n") (auto simp: split_beta')
          next
            case 2
            then show ?case
              by (auto simp: split_beta' PiE_iff extensional_def Pi_iff space_pair_measure space_PiM)
          next
            case 3
            then show ?case
              unfolding K'_def
            proof (intro measurable_bind[where N = Ms], goal_cases)
              case 1
              then show ?case
                unfolding measurable_pair_swap_iff[of _ M]
                by measurable (auto simp: gm  measurable_snd'' intro: measurable_prob_algebraD)
            next
              case 2
              then show ?case 
                unfolding Suc_policy_def
                using f'
                by (auto intro!: measurable_bind[where N = Ma] measurable_prob_algebraD)
            qed
          qed
          thus "(\<lambda>w. case w of (x, a) \<Rightarrow> distr ((K' (f x) (g x)) n a) (Pi\<^sub>M {0..<Suc n} (\<lambda>i. M)) (fun_upd a n)) \<in> M \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M) \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M {0..<Suc n} (\<lambda>_. M))"
            by measurable
        qed
      qed
    qed (auto simp: f g)
  qed

  have p': "\<And>a. a \<in> space M \<Longrightarrow> is_policy (f a)"
    using f by auto
  have "(\<lambda>a. emeasure (lim_sequence (f a) (g a)) X) \<in> borel_measurable M \<longleftrightarrow>
    (\<lambda>a. emeasure (Ionescu_Tulcea.CI (K' (f a) (g a)) (\<lambda>_. M) J) (Pi\<^sub>E J F)) \<in> borel_measurable M"
    unfolding X using J Pi_F
    by (fastforce simp add: g f K space_pair_measure intro!: p p' measurable_cong emeasure_lim_sequence_emb)
  also have "..."
  proof (intro measurable_compose[OF _ measurable_emeasure_subprob_algebra[OF Pi_F(2)]], 
      subst measurable_cong[where g = "(\<lambda>w. distr (Ionescu_Tulcea.C (K' (f w) (g w))
      (\<lambda>_. M) 0 n (\<lambda>x. undefined)) (Pi\<^sub>M J (\<lambda>_. M)) (\<lambda>f. restrict f J))"], goal_cases)
    case (1 w)
    then show ?case
      unfolding Ionescu_Tulcea.CI_def[OF IT_K'[OF f[OF 1] g[OF 1]]]
      using p
      by (subst Ionescu_Tulcea.up_to_def[OF IT_K'[of "Suc_policy p w" "K w"]])
        (auto simp add: n_def \<open>w \<in> space M\<close> prob_space_K sets_K space_prob_algebra)
  next
    case 2
    then show ?case
      using measurable_compose measurable_distr[OF measurable_restrict_subset[OF J_le_n]] C
      by blast
  qed
  thus "(\<lambda>a. emeasure (lim_sequence (f a) (g a)) X) \<in> borel_measurable M"
    using calculation by blast
qed

lemma lim_sequence_Suc_return[measurable]: 
  assumes p: "is_policy p"
  assumes s: "s \<in> space Ms"
  shows "(\<lambda>x. lim_sequence (Suc_policy p (s, snd x)) (return Ms (fst x))) \<in> 
    M \<rightarrow>\<^sub>M prob_algebra (Pi\<^sub>M UNIV (\<lambda>_. M))"
proof (intro lim_sequence_aux[OF p], goal_cases)
  case (1 x)
  then show ?case
    by (meson is_policy_Suc_policy measurable_snd measurable_space p s space_ma)
next
  case (2 n)
  then show ?case
    using p
    unfolding Suc_policy_def
    by measurable (auto intro: measurable_PiM_single' 
        simp: s space_pair_measure space_PiM PiE_iff extensional_def split: nat.split)
qed measurable

lemma lim_sequence_Suc_K[measurable]: 
  assumes "is_policy p"
  shows "(\<lambda>x. lim_sequence (Suc_policy p x) (K x)) \<in> M \<rightarrow>\<^sub>M prob_algebra (Pi\<^sub>M UNIV (\<lambda>_. M))"
  using assms
  by (fastforce intro!: lim_sequence_aux)

subsection \<open>Iteration Rule\<close>
lemma step_C:
  assumes x: "x \<in> space (prob_algebra Ms)" and p: "is_policy p"
  shows "Ionescu_Tulcea.C (K' p x) (\<lambda>_. M) 0 1 (\<lambda>_. undefined) \<bind> 
    Ionescu_Tulcea.C (K' p x) (\<lambda>_. M) 1 n =
    K0 p x \<bind> (\<lambda>a. Ionescu_Tulcea.C (K' p x) (\<lambda>_. M) 1 n (case_nat a (\<lambda>_. undefined)))"
proof -
  interpret Ionescu_Tulcea "K' p x" "\<lambda>_. M"
    using IT_K'[OF p x] .

  have [simp]: "space (K0 p x) \<noteq> {}"
    using space_K0[OF p x] x by auto

  have [simp]: "((\<lambda>_. undefined)(0 := x::('s \<times> 'a))) = case_nat x (\<lambda>_. undefined)" for x
    by (auto simp: fun_eq_iff split: nat.split)

  have "C 0 1 (\<lambda>_. undefined) \<bind> C 1 n = eP 0 (\<lambda>_. undefined) \<bind> C 1 n"
    using measurable_eP[of 0] measurable_C[of 1 n, measurable del]
    by (simp add: bind_return[where N="Pi\<^sub>M {0} (\<lambda>_. M)"])
  also have "\<dots> = K0 p x \<bind> (\<lambda>a. C 1 n (case_nat a (\<lambda>_. undefined)))"
    unfolding eP_def
  proof (subst bind_distr[where K = "Pi\<^sub>M {0..<Suc n} (\<lambda>_. M)"], goal_cases)
    case 1
    then show ?case 
      using measurable_C[of 1 n, measurable del] x[THEN sets_K0[OF p]] measurable_ident_sets[OF sets_P]
      unfolding K0_def
      by auto
  next
    case 2
    then show ?case
      using measurable_C[of 1 n]
      by auto
  next
    case 3
    then show ?case
      by (simp add: space_P)
  next
    case 4
    then show ?case
      unfolding K0_def
      by (auto intro!: bind_cong)
  qed
  finally show 
    "C 0 1 (\<lambda>_. undefined) \<bind> C 1 n = K0 p x \<bind> (\<lambda>a. C 1 n (case_nat a (\<lambda>_. undefined)))" .
qed

lemma lim_sequence_eq:
  assumes x: "x \<in> space (prob_algebra Ms)" assumes p: "is_policy p"
  shows "lim_sequence p x = 
    K0 p x \<bind> (\<lambda>y. distr (lim_sequence (Suc_policy p y) (K y)) (\<Pi>\<^sub>M _\<in>UNIV. M) (case_nat y))"
    (is "_ = ?B p x")
proof (rule measure_eqI_PiM_infinite)
  show "sets (lim_sequence p x) = sets (\<Pi>\<^sub>M j\<in>UNIV. M)"
    using x p by (rule sets_lim_sequence)
  have [simp]: "space (K' p x 0 (\<lambda>n. undefined)) \<noteq> {}"
    using p
    using IT_K' Ionescu_Tulcea.non_empty Ionescu_Tulcea.space_P x by fastforce
  show "sets (?B p x) = sets (Pi\<^sub>M UNIV (\<lambda>j. M))"
    using p x M_ne_policy space_K0 by auto

  interpret lim_sequence: prob_space "lim_sequence p x"
    using lim_sequence x p by (auto simp: measurable_restrict_space2_iff prob_algebra_def)
  show "finite_measure (lim_sequence p x)"
    by (rule lim_sequence.finite_measure)

  interpret Ionescu_Tulcea "K' p x" "\<lambda>_. M"
    using  IT_K'[OF p x] .

  let ?U = "\<lambda>_::nat. undefined :: ('s \<times> 'a)"

  fix J :: "nat set" and F'
  assume J: "finite J" "\<And>i. i \<in> J \<Longrightarrow> F' i \<in> sets M"

  define n where "n = (if J = {} then 0 else Max J)"
  define F where "F i = (if i \<in> J then F' i else space M)" for i
  then have F[simp, measurable]: "F i \<in> sets M" for i
    using J by auto
  have emb_eq: "PF.emb UNIV J (Pi\<^sub>E J F') = PF.emb UNIV {0..<Suc n} (Pi\<^sub>E {0..<Suc n} F)"
  proof cases
    assume "J = {}" then show ?thesis
      by (auto simp add: n_def F_def[abs_def] prod_emb_def PiE_def)
  next
    assume "J \<noteq> {}" then show ?thesis
      by (auto simp: prod_emb_def PiE_iff F_def n_def less_Suc_eq_le \<open>finite J\<close> split: if_split_asm)
  qed

  have "emeasure (lim_sequence p x) (PF.emb UNIV J (Pi\<^sub>E J F')) = 
    emeasure (C 0 (Suc n) ?U) (Pi\<^sub>E {0..<Suc n} F)"
    using x p unfolding emb_eq 
    by (rule emeasure_lim_sequence_emb_I0o) (auto intro!: sets_PiM_I_finite)
  also have "C 0 (Suc n) ?U = K0 p x \<bind> (\<lambda>y. C 1 n (case_nat y ?U))"
    using split_C[of ?U 0 "Suc 0" n] step_C[OF x p] by simp
  also have "emeasure (K0 p x \<bind> (\<lambda>y. C 1 n (case_nat y ?U))) (Pi\<^sub>E {0..<Suc n} F) =
    (\<integral>\<^sup>+y. C 1 n (case_nat y ?U) (Pi\<^sub>E {0..<Suc n} F) \<partial>K0 p x)"
    using measurable_C[of 1 n, measurable del] sets_K0[OF p x] F x p non_empty space_K0
    by (intro emeasure_bind[OF  _ measurable_compose[OF _ measurable_C]])
      (auto cong: measurable_cong_sets intro!: measurable_PiM_single' split: nat.split_asm)
  also have "\<dots> = (\<integral>\<^sup>+y. distr (lim_sequence (Suc_policy p y) (K y)) 
    (Pi\<^sub>M UNIV (\<lambda>j. M)) (case_nat y) (PF.emb UNIV J (Pi\<^sub>E J F')) \<partial>K0 p x)"
  proof (intro nn_integral_cong)
    fix y assume "y \<in> space (K0 p x)"
    then have y: "y \<in> space M"
      using x p space_K0 by blast
    then interpret y: Ionescu_Tulcea "K' (Suc_policy p y) (K y)" "\<lambda>_. M"
      using p by (auto intro!: IT_K')
    have "fst y \<in> space Ms"
      by (meson measurable_fst measurable_space y)
    let ?y = "case_nat y"
    have [simp]: "?y ?U \<in> space (Pi\<^sub>M {0} (\<lambda>i. M))"
      using y by (auto simp: space_PiM PiE_iff extensional_def split: nat.split)
    have yM[measurable]: "?y \<in> Pi\<^sub>M {0..<m} (\<lambda>_. M) \<rightarrow>\<^sub>M Pi\<^sub>M {0..<Suc m} (\<lambda>i. M)" for m
      using y 
      by (auto intro: measurable_PiM_single' simp: space_PiM PiE_iff extensional_def split: nat.split)
    have y': "?y ?U \<in> space (Pi\<^sub>M {0..<1} (\<lambda>i. M))"
      by (simp add: space_PiM PiE_def y extensional_def split: nat.split)

    have eq1: "?y -` Pi\<^sub>E {0..<Suc n} F \<inter> space (Pi\<^sub>M {0..<n} (\<lambda>_. M)) =
        (if y \<in> F 0 then Pi\<^sub>E {0..<n} (F\<circ>Suc) else {})"
      unfolding set_eq_iff using y sets.sets_into_space[OF F]
      by (auto simp: space_PiM PiE_iff extensional_def Ball_def split: nat.split nat.split_asm)

    have eq2: "?y -` PF.emb UNIV {0..<Suc n} (Pi\<^sub>E {0..<Suc n} F) \<inter> space (Pi\<^sub>M UNIV (\<lambda>_. M)) =
        (if y \<in> F 0 then PF.emb UNIV {0..<n} (Pi\<^sub>E {0..<n} (F\<circ>Suc)) else {})"
      unfolding set_eq_iff using y sets.sets_into_space[OF F]
      by (auto simp: space_PiM PiE_iff prod_emb_def extensional_def Ball_def split: nat.splits)

    let ?I = "indicator (F 0) y"    
    have "fst y \<in> space Ms"
      using y by (meson measurable_fst measurable_space)
    have "C 1 n (?y ?U) = distr (y.C 0 n ?U) (\<Pi>\<^sub>M i\<in>{0..<Suc n}. M) ?y"
    proof (induction n)
      case (Suc m)

      have "C 1 (Suc m) (?y ?U) = distr (y.C 0 m ?U) (Pi\<^sub>M {0..<Suc m} (\<lambda>i. M)) ?y \<bind> eP (Suc m)"
        using Suc by simp
      also have "\<dots> = y.C 0 m ?U \<bind> (\<lambda>x. eP (Suc m) (?y x))"
        by (auto intro!: bind_distr[where K="Pi\<^sub>M {0..<Suc (Suc m)} (\<lambda>_. M)"] simp: y y.space_C y.sets_C cong: measurable_cong_sets)
      also have "\<dots> = y.C 0 m ?U \<bind> (\<lambda>x. distr (y.eP m x) (Pi\<^sub>M {0..<Suc (Suc m)} (\<lambda>i. M)) ?y)"
      proof (intro bind_cong refl)
        fix \<omega>' assume \<omega>': "\<omega>' \<in> space (y.C 0 m ?U)"
        moreover have "K' p x (Suc m) (?y \<omega>') = K' (Suc_policy p y) (K y) m \<omega>'"
          unfolding K'_def Suc_policy_def
          by (auto split: nat.splits)
        ultimately show "eP (Suc m) (?y \<omega>') = distr (y.eP m \<omega>') (Pi\<^sub>M {0..<Suc (Suc m)} (\<lambda>i. M)) ?y"
          unfolding eP_def y.eP_def
          by (subst distr_distr) (auto simp: y.space_C y.sets_P split: nat.split cong: measurable_cong_sets
              intro!: distr_cong measurable_fun_upd[where J="{0..<m}"])
      qed
      also have "\<dots> = distr (y.C 0 m ?U \<bind> y.eP m) (Pi\<^sub>M {0..<Suc (Suc m)} (\<lambda>i. M)) ?y"
        by (auto intro!: distr_bind[symmetric, OF _ _ yM] simp: y.space_C y.sets_C cong: measurable_cong_sets)
      finally show ?case
        by simp
    qed (use y in \<open>simp add: PiM_empty distr_return\<close>)
    then have "C 1 n (case_nat y ?U) (Pi\<^sub>E {0..<Suc n} F) =
      (distr (y.C 0 n ?U) (\<Pi>\<^sub>M i\<in>{0..<Suc n}. M) ?y) (Pi\<^sub>E {0..<Suc n} F)" by simp
    also have "\<dots> = ?I * y.C 0 n ?U (Pi\<^sub>E {0..<n} (F \<circ> Suc))"
      by (subst emeasure_distr) (auto simp: y.sets_C y.space_C eq1 cong: measurable_cong_sets)
    also have 
      "\<dots> = ?I * lim_sequence (Suc_policy p y) (K y) (PF.emb UNIV {0..<n} (Pi\<^sub>E {0..<n} (F \<circ> Suc)))"
      using y sets_PiM_I_finite
      by (subst emeasure_lim_sequence_emb_I0o) (auto simp add:  p sets_PiM_I_finite)
    also have "\<dots> = distr (lim_sequence (Suc_policy p y) (K y)) (Pi\<^sub>M UNIV (\<lambda>j. M)) ?y
      (PF.emb UNIV {0..<Suc n} (Pi\<^sub>E {0..<Suc n} F))"
    proof (subst emeasure_distr, goal_cases)
      case 1
      thus ?case
        using y
        by measurable (simp add: lim_sequence_def measurable_ident_sets)
      case 2
      thus ?case
        by auto
      case 3
      thus ?case
        using y
        by (subst space_lim_sequence[OF _ is_policy_Suc_policy[OF _ p]]) (auto simp: eq2)
    qed
    finally show "emeasure (C 1 n (case_nat y (\<lambda>_. undefined))) (Pi\<^sub>E {0..<Suc n} F) = 
      emeasure (distr (lim_sequence (Suc_policy p y) (K y)) (Pi\<^sub>M UNIV (\<lambda>j. M)) (case_nat y)) 
        (y.PF.emb UNIV J (Pi\<^sub>E J F'))"
      unfolding emb_eq .
  qed
  also have "\<dots> = emeasure (K0 p x \<bind> (\<lambda>y. distr (lim_sequence (Suc_policy p y) (K y)) 
    (Pi\<^sub>M UNIV (\<lambda>j. M)) (case_nat y))) (PF.emb UNIV J (Pi\<^sub>E J F'))"
    using J sets_K0[OF \<open>is_policy p\<close> \<open>x \<in> space (prob_algebra Ms)\<close>] p
    by (subst emeasure_bind[where N="PiM UNIV (\<lambda>_. M)"]) (auto simp: sets_K x cong: measurable_cong_sets
        intro!: measurable_distr2[OF _ measurable_prob_algebraD[OF lim_sequence]] 
        measurable_prob_algebraD 
        measurable_distr2[where M = "PiM UNIV (\<lambda>_. M)"])
  finally show "emeasure (lim_sequence p x) (PF.emb UNIV J (Pi\<^sub>E J F')) = 
    emeasure (K0 p x \<bind> (\<lambda>y. distr (lim_sequence (Suc_policy p y) (K y)) (Pi\<^sub>M UNIV (\<lambda>j. M))
      (case_nat y))) (PF.emb UNIV J (Pi\<^sub>E J F'))".
qed

subsection \<open>Stream Space of the MDP\<close>
definition lim_stream :: "('s, 'a) pol \<Rightarrow> 's measure \<Rightarrow> ('s \<times> 'a) stream measure"
  where
    "lim_stream p x = distr (lim_sequence p x) (stream_space M) to_stream"

lemma space_lim_stream: "space (lim_stream p x) = streams (space M)"
  unfolding lim_stream_def by (simp add: space_stream_space)

lemma sets_lim_stream[measurable_cong]: "sets (lim_stream p x) = sets (stream_space M)"
  unfolding lim_stream_def by simp

lemma lim_stream[measurable]: 
  assumes "is_policy p" 
  shows "lim_stream p \<in> prob_algebra Ms \<rightarrow>\<^sub>M prob_algebra (stream_space M)"
  unfolding lim_stream_def[abs_def]
  using assms 
  by (auto intro: measurable_distr_prob_space2[OF lim_sequence])

lemma lim_stream_Suc[measurable]:
  assumes p: "is_policy p"
  shows "(\<lambda>a. lim_stream (Suc_policy p a) (K a)) \<in> M \<rightarrow>\<^sub>M prob_algebra (stream_space M)"
  unfolding lim_stream_def[abs_def] 
  using p 
  by (auto intro: measurable_distr_prob_space2[OF lim_sequence_Suc_K])

lemma space_stream_space_M_ne: "x \<in> space M \<Longrightarrow> space (stream_space M) \<noteq> {}"
  using sconst_streams[of x "space M"] by (auto simp: space_stream_space)

lemma prob_space_lim_stream[intro]: 
  assumes "is_policy p" "x \<in> space (prob_algebra Ms)" 
  shows "prob_space (lim_stream p x)"
  by (metis (no_types, lifting) space_prob_algebra measurable_space assms lim_stream mem_Collect_eq)

lemma prob_space_step: 
  assumes "is_policy p" "x \<in> space M"
  shows "prob_space (lim_stream (Suc_policy p x) (K x))"
  by (auto simp: assms K_in_space is_policy_Suc_policy)


lemma lim_stream_eq:
  assumes p: "is_policy p"
  assumes x: "x \<in> space (prob_algebra Ms)"
  shows "lim_stream p x = do {
    y \<leftarrow> K0 p x;
    \<omega> \<leftarrow> lim_stream (Suc_policy p y) (K y); 
    return (stream_space M) (y ## \<omega>)
  }"
  unfolding lim_stream_def lim_sequence_eq[OF x p]
proof (subst distr_bind[OF _ _ measurable_to_stream])
  show "(\<lambda>y. distr (lim_sequence (Suc_policy p y) (K y)) (Pi\<^sub>M UNIV (\<lambda>j. M)) (case_nat y)) \<in> 
    K0 p x \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M UNIV (\<lambda>i. M))"
  proof (intro measurable_prob_algebraD measurable_distr_prob_space2[where M="Pi\<^sub>M UNIV (\<lambda>j. M)"])
    show "(\<lambda>x. lim_sequence (Suc_policy p x) (K x)) \<in> K0 p x \<rightarrow>\<^sub>M prob_algebra (Pi\<^sub>M UNIV (\<lambda>j. M))"
      using lim_sequence_Suc_K[OF p] sets_K0[OF p x] measurable_cong_sets 
      by blast
  next show "(\<lambda>(ya, y). case_nat ya y) \<in> K0 p x \<Otimes>\<^sub>M Pi\<^sub>M UNIV (\<lambda>j. M) \<rightarrow>\<^sub>M Pi\<^sub>M UNIV (\<lambda>j. M)"
      using sets_K0[OF p x]
      by (subst measurable_cong_sets[of  _ "M \<Otimes>\<^sub>M Pi\<^sub>M UNIV (\<lambda>j. M)"]) auto
  qed
next 
  show "space (K0 p x) \<noteq> {}"
    using x p prob_space.not_empty prob_space_K0
    by blast
next 
  show "K0 p x \<bind> (\<lambda>x. distr (distr (lim_sequence (Suc_policy p x) (K x)) (Pi\<^sub>M UNIV (\<lambda>j. M)) 
    (case_nat x)) (stream_space M) to_stream) = K0 p x \<bind> (\<lambda>y. distr (lim_sequence (Suc_policy p y)
      (K y)) (stream_space M) to_stream \<bind> (\<lambda>\<omega>. return (stream_space M) (y ## \<omega>)))"
  proof (intro bind_cong refl, subst distr_distr)
    show "to_stream \<in> Pi\<^sub>M UNIV (\<lambda>j. M) \<rightarrow>\<^sub>M stream_space M"
      by measurable
  next 
    show "\<And>a. a \<in> space (K0 p x) \<Longrightarrow> 
      case_nat a \<in> lim_sequence (Suc_policy p a) (K a) \<rightarrow>\<^sub>M Pi\<^sub>M UNIV (\<lambda>j. M)"
      by measurable (auto simp: p x intro!: measurable_ident_sets sets_lim_sequence intro: measurable_space)
  next 
    show "\<And>a. a \<in> space (K0 p x) \<Longrightarrow>
      distr (lim_sequence (Suc_policy p a) (K a)) (stream_space M) (to_stream \<circ> case_nat a) =
      distr (lim_sequence (Suc_policy p a) (K a)) (stream_space M) to_stream \<bind> 
        (\<lambda>\<omega>. return (stream_space M) (a ## \<omega>))"
    proof (subst bind_return_distr', goal_cases)
      case (1 a)
      then show ?case by (simp add: p space_stream_space_M_ne x)
    next
      case (2 a)
      then show ?case using p x by (auto simp: sets_lim_sequence cong: measurable_cong_sets intro!: distr_cong)[1]
    next
      case (3 a)
      then show ?case
        using p x
        by (subst distr_distr) (auto simp: to_stream_nat_case intro!: measurable_compose[OF _ measurable_to_stream] 
            sets_lim_sequence distr_cong measurable_ident_sets)
    qed
  qed
qed

end
end