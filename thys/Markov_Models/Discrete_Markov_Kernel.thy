(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)
header {* Discrete-time Markov processes constructed using Markov kernels *}
theory Discrete_Markov_Kernel
  imports "~~/src/HOL/Probability/Probability"
begin

lemma integrableI_nonneg_bounded:
  fixes f :: "_ \<Rightarrow> real"
  assumes "f \<in> borel_measurable M" and f: "AE x in M. 0 \<le> f x" "(\<integral>\<^sup>+x. f x \<partial>M) < \<infinity>" 
  shows "integrable M f"
proof (rule integrableI_bounded)
  have "(\<integral>\<^sup>+ x. norm (f x) \<partial>M) = (\<integral>\<^sup>+ x. f x \<partial>M)"
    using f(1) by (intro positive_integral_cong_AE) auto
  also note f(2)
  finally show "(\<integral>\<^sup>+ x. norm (f x) \<partial>M) < \<infinity>" .
qed fact

lemma integral_norm_bound1:
  fixes f :: "_ \<Rightarrow> real"
  shows "integrable M f \<Longrightarrow> \<bar>integral\<^sup>L M f\<bar> \<le> (\<integral>x. \<bar>f x\<bar> \<partial>M)"
  using positive_integral_eq_integral[of M "\<lambda>x. \<bar>f x\<bar>"] integral_norm_bound[of M f]
  by (simp add: integrable_abs)

lemma (in wellorder) smallest:
  assumes "P i" obtains j where "P j" "\<And>i. i < j \<Longrightarrow> \<not> P i" "j \<le> i"
proof
  show "P (LEAST j. P j)" "\<And>i. i < (LEAST j. P j) \<Longrightarrow> \<not> P i" "(LEAST j. P j) \<le> i"
    using `P i` LeastI2_wellorder[of P i "\<lambda>j. j \<le> i", OF `P i`]
    by (auto intro: LeastI_ex dest: not_less_Least)
qed

lemma setsum_strict_mono_single: 
  fixes f :: "_ \<Rightarrow> 'a :: {comm_monoid_add,ordered_cancel_ab_semigroup_add}"
  shows "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> f a < g a \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> f a \<le> g a) \<Longrightarrow> setsum f A < setsum g A"
  using setsum_strict_mono_ex1[of A f g] by auto

lemma zero_notin_Suc_image: "0 \<notin> Suc ` A" by auto

lemma Ex_case_nat_eq: "(\<exists>n. P n (case_nat s f n)) \<longleftrightarrow> P 0 s \<or> (\<exists>n. P (Suc n) (f n))"
  by (auto split: nat.split simp: gr0_conv_Suc)

lemma case_nat_in_funcset: "case_nat x f \<in> (UNIV \<rightarrow> X) \<longleftrightarrow> x \<in> X \<and> f \<in> UNIV \<rightarrow> X"
  by (auto simp: Pi_def split: nat.split)

lemma case_nat_idem: "case_nat (f 0) (\<lambda>x. f (Suc x)) = f"
  by (auto split: nat.split)

lemma all_plus_split: 
  fixes P :: "nat \<Rightarrow> bool"
  shows "(\<forall>i\<le>k + n. P i) \<longleftrightarrow> (\<forall>i\<le>n. P (i + k)) \<and> (\<forall>i<k. P i)"
  apply (intro iffI allI)
   apply force
  apply (case_tac "k \<le> i")
   apply (erule conjE)
   apply (erule_tac x="i - k" in allE)
   apply (auto simp add: not_less)
  done

lemma all_Suc_split: "(\<forall>i\<le>Suc n. P i) \<longleftrightarrow> (\<forall>i\<le>n. P (Suc i)) \<and> P 0"
  by (metis le_eq_less_or_eq less_Suc_eq_0_disj)

lemma all_less_Suc_split: "(\<forall>i<Suc n. P i) \<longleftrightarrow> (\<forall>i<n. P (Suc i)) \<and> P 0"
  by (metis less_Suc_eq_0_disj)

lemma nat_boundary_cases[case_names less add]:
  fixes P :: bool and n l :: nat
  shows "(n < l \<Longrightarrow> P) \<Longrightarrow> (\<And>k. n = k + l \<Longrightarrow> P) \<Longrightarrow> P"
  using less_imp_add_positive[of l n]
  by (cases n l rule: linorder_cases) auto

lemma
  fixes S :: "'s set"
  assumes S: "countable S"
  assumes P[measurable]: "\<And>s. s \<in> S \<Longrightarrow> Measurable.pred M (P s)"
  shows sets_Collect_All_S[measurable (raw)]: "Measurable.pred M (\<lambda>x. \<forall>s\<in>S. P s x)" (is ?ALL)
    and sets_Collect_Ex_S[measurable (raw)]: "Measurable.pred M (\<lambda>x. \<exists>s\<in>S. P s x)" (is ?EX)
proof -
  let ?f = "from_nat_into S"
  have *: 
    "\<And>x. (\<forall>s\<in>S. P s x) \<longleftrightarrow> (\<forall>n. ?f n \<in> S \<longrightarrow> P (if ?f n \<in> S then ?f n else undefined) x)"
    "\<And>x. (\<exists>s\<in>S. P s x) \<longleftrightarrow> (\<exists>n. ?f n \<in> S \<and> P (if ?f n \<in> S then ?f n else undefined) x)"
    using subset_range_from_nat_into[OF S] by auto
  from subset_range_from_nat_into[OF S] show ?ALL ?EX unfolding * by measurable
qed

lemma measurable_compose_countable:
  assumes S[simp]: "countable S"
  assumes g[measurable]: "g \<in> measurable M (count_space S)"
  assumes f[measurable]: "\<And>i. i \<in> S \<Longrightarrow> f i \<in> measurable M N"
  shows "(\<lambda>x. f (g x) x) \<in> measurable M N"
  unfolding measurable_def
proof safe
  fix x assume "x \<in> space M" then show "f (g x) x \<in> space N"
    using measurable_space[OF f] measurable_space[OF g] by auto
next
  fix A assume [measurable]: "A \<in> sets N"
  have *: "(\<lambda>x. f (g x) x) -` A \<inter> space M = {x\<in>space M. \<exists>s\<in>S. g x = s \<and> f s x \<in> A}"
    using measurable_space[OF g] by auto
  show "(\<lambda>x. f (g x) x) -` A \<inter> space M \<in> sets M"
    unfolding * by measurable
qed

locale Discrete_Markov_Kernel =
  fixes S :: "'s set" and K :: "'s \<Rightarrow> 's measure"
  assumes countable_space[simp]: "countable S"
  assumes non_empty_space: "S \<noteq> {}"
  assumes sets_eq_S[simp]: "\<And>s. s \<in> S \<Longrightarrow> sets (K s) = Pow S"
  assumes markov_kernel: "\<And>s. prob_space (K s)"
begin

abbreviation
  "D \<equiv> (\<Pi>\<^sub>M s\<in>S. K s)"

abbreviation
  "D_seq \<equiv> (\<Pi>\<^sub>M n\<in>UNIV :: nat set. D)"

end

sublocale Discrete_Markov_Kernel \<subseteq> K: prob_space "K s" for s by (rule markov_kernel)

sublocale Discrete_Markov_Kernel \<subseteq> D: product_prob_space "\<lambda>s. K s" "S" ..

sublocale Discrete_Markov_Kernel \<subseteq> P: sequence_space D ..

context Discrete_Markov_Kernel
begin

definition "s0 = (SOME s. s \<in> S)"

lemma s0: "s0 \<in> S"
  using non_empty_space by (auto intro: someI_ex simp: s0_def)

lemma space_eq_S[simp]: "s \<in> S \<Longrightarrow> space (K s) = S"
  using sets_eq_imp_space_eq[of "K s" "count_space S"] sets_eq_S by simp

lemma K_measurable1: "s \<in> S \<Longrightarrow> measurable (K s) M = measurable (count_space S) M"
  unfolding measurable_def by auto

lemma K_measurable2: "s \<in> S \<Longrightarrow> measurable M (K s) = measurable M (count_space S)"
  unfolding measurable_def by auto

lemma K_measurable1_imp[measurable (raw)]:
  "s \<in> S \<Longrightarrow> f \<in> measurable (count_space S) M \<Longrightarrow> f \<in> measurable (K s) M"
  unfolding measurable_def by auto

lemma K_measurable2_imp[measurable (raw)]:
  "s \<in> S \<Longrightarrow> f \<in> measurable M (count_space S) \<Longrightarrow> f \<in> measurable M (K s)"
  unfolding measurable_def by auto

lemma AE_all_S: "(\<And>s. s \<in> S \<Longrightarrow> AE x in M. P s x) \<Longrightarrow> AE x in M. \<forall>s\<in>S. P s x"
  by (auto intro!: AE_impI simp: AE_all_countable countable_all[OF countable_space])

section {* Enabled states *}

definition "E s = {s' \<in> S. emeasure (K s) {s'} \<noteq> 0}"

lemma E_subset_S[simp]: "E s \<subseteq> S"
  unfolding E_def by auto

lemma E_in_S[dest]: "s' \<in> E s \<Longrightarrow> s' \<in> S"
  unfolding E_def by auto

lemma measurable_E[measurable (raw)]:
  assumes f[measurable]: "f \<in> measurable M (count_space S)"
    and g[measurable]: "g \<in> measurable M (count_space S)"
  shows "(\<lambda>x. f x \<in> E (g x)) \<in> measurable M (count_space UNIV)"
proof -
  have [measurable]: "\<And>s. E s \<in> sets (count_space S)" by simp

  have "{x \<in> space M. f x \<in> E (g x)} = {x\<in>space M. \<exists>s\<in>S. g x = s \<and> f x \<in> E s}"
    using measurable_space[OF g] by auto
  also have "\<dots> \<in> sets M"
    by measurable
  finally show ?thesis by (simp add: pred_def)
qed

lemma AE_K_iff:
  assumes [simp]: "s \<in> S"
  shows "(AE t in K s. P t) \<longleftrightarrow> (\<forall>t\<in>E s. P t)"
proof -
  let ?C = "to_nat_on S ` S" and ?f = "from_nat_into S"
  have "(AE t in K s. P t) \<longleftrightarrow> emeasure (K s) {t\<in>S. \<not> P t} = 0"
    by (rule AE_iff_measurable) auto
  also have "emeasure (K s) {t\<in>S. \<not> P t} =
      emeasure (K s) (\<Union>i. if i \<in> ?C \<and> \<not> P (?f i) then {?f i} else {})"
    by (intro arg_cong2[where f=emeasure])
       (auto split: split_if_asm cong: rev_conj_cong simp: eq_from_nat_into_iff)
  also have "\<dots> =  (\<Sum>i. emeasure (K s) (if i \<in> ?C \<and> \<not> P (?f i) then {?f i} else {}))"
    by (subst suminf_emeasure) (auto simp: disjoint_family_on_def)
  also have "(\<Sum>i. emeasure (K s) (if i \<in> ?C \<and> \<not> P (?f i) then {?f i} else {})) = 0 \<longleftrightarrow>
      (\<forall>i. emeasure (K s) (if i \<in> ?C \<and> \<not> P (?f i) then {?f i} else {}) = 0)"
    by (rule suminf_ereal_eq_0) auto
  also have "\<dots> \<longleftrightarrow> (\<forall>i. i \<in> ?C \<longrightarrow> ?f i \<in> E s \<longrightarrow> P (?f i))"
    by (auto simp add: E_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>t\<in>S. t \<in> E s \<longrightarrow> P t)"
    by (auto simp: bij_betw_def) 
  finally show ?thesis by auto
qed

lemma AE_enabled:
  assumes [simp]: "s \<in> S" shows "AE s' in K s. s' \<in> E s"
  by (simp add: AE_K_iff)

lemma AE_all_E:
  assumes *: "\<And>t. t \<in> E s \<Longrightarrow> AE x in M. P t x"
  shows "AE x in M. \<forall>t\<in>E s. P t x"
proof -
  have "\<And>P x. (\<forall>t\<in>E s. P t) \<longleftrightarrow> (\<forall>t\<in>S. t \<in> E s \<longrightarrow> P t)"
    by (auto simp: E_def)
  with * show ?thesis
    by (auto intro!: AE_all_S AE_impI)
qed

section {* The set of reachable states *}

inductive_set reachable :: "'s set \<Rightarrow> 's \<Rightarrow> 's set" for \<Phi> :: "'s set" and s :: "'s" where
  start: "t \<in> E s \<Longrightarrow> t \<in> reachable \<Phi> s"
| step: "t \<in> reachable \<Phi> s \<Longrightarrow> t' \<in> E t \<Longrightarrow> t \<in> \<Phi> \<Longrightarrow> t' \<in> reachable \<Phi> s"

lemma reachable_induct_trans[consumes 1, case_names start step]:
  assumes t: "t \<in> reachable \<Phi> s"
  assumes 1: "\<And>t s. t \<in> E s \<Longrightarrow> P t s"
  assumes 2: "\<And>t t' s. t' \<in> reachable \<Phi> s \<Longrightarrow> P t' s \<Longrightarrow> t' \<in> \<Phi> \<Longrightarrow> t \<in> reachable \<Phi> t' \<Longrightarrow>
    P t t' \<Longrightarrow> P t s"
  shows "P t s"
  using t
  by induct (blast intro: 1 2 reachable.intros)+

lemma reachable_trans:
  assumes "t \<in> reachable \<Phi> s" "t' \<in> reachable \<Phi> t" "t \<in> \<Phi>" shows "t' \<in> reachable \<Phi> s"
  using assms(2,1,3) by (induct t') (auto dest: reachable.step)

lemma reachable_step_rev:
  assumes "t \<in> reachable \<Phi> s" "s \<in> E s'" "s \<in> \<Phi>" shows "t \<in> reachable \<Phi> s'"
  using assms reachable_trans[of s \<Phi> s' t] by (auto intro: reachable.start)

lemma reachable_rev:
  assumes t: "t \<in> reachable \<Phi> s"
  obtains (start) "t \<in> E s" | (step) s' where "t \<in> reachable \<Phi> s'" "s' \<in> \<Phi>" "s' \<in> E s"
  using t by induct (auto intro: reachable.step reachable.start)

lemma reachable_induct_rev[consumes 1, case_names start step]:
  assumes t: "t \<in> reachable \<Phi> s"
  assumes 1: "\<And>s. t \<in> E s \<Longrightarrow> P s"
  assumes 2: "\<And>t' s. t' \<in> E s \<Longrightarrow> t' \<in> \<Phi> \<Longrightarrow> t \<in> reachable \<Phi> t' \<Longrightarrow> P t' \<Longrightarrow> P s"
  shows "P s"
  using t
proof cases
  case (step s')
  then have "t \<in> reachable \<Phi> s'" "P s'" "s' \<in> \<Phi>"
    by (auto intro: 1 reachable.start)
  with step(1) show ?thesis
    by (induct rule: reachable_induct_trans) (auto intro: 1 2 reachable_trans)
qed fact

lemma reachable_in_S[dest]:
  assumes "t \<in> reachable \<Phi> s" shows "t \<in> S"
  using assms by (induct t) auto

lemma reachable_closed:
  assumes "s \<in> R" "s \<in> \<Phi>" "\<forall>s\<in>R \<inter> \<Phi>. E s \<subseteq> R"
  shows "reachable (\<Phi> - \<Psi>) s \<subseteq> R"
proof
  fix x assume "x \<in> reachable (\<Phi> - \<Psi>) s"
  then show "x \<in> R"
    by induct (insert assms, auto)
qed

lemma reachable_closed_rev:
  assumes t: "t \<in> reachable (\<Phi> - \<Psi>) s"
    and R: "t \<in> R" "{s\<in>\<Phi>-\<Psi>. R \<inter> E s \<noteq> {}} \<subseteq> R"
    and s: "s \<in> \<Phi>" "s \<notin> \<Psi>"
  shows "s \<in> R"
  using t s by (induct rule: reachable_induct_rev) (insert R, auto)

lemma reachableE:
  assumes t: "t \<in> reachable \<Phi> s"
  obtains (path) \<omega> n where "\<And>i. i \<le> n \<Longrightarrow> \<omega> i \<in> E (case_nat s \<omega> i)" "\<And>i. i < n \<Longrightarrow> \<omega> i \<in> \<Phi>" "\<omega> n = t"
  using t
proof (induct arbitrary: thesis rule: reachable_induct_rev)
  case (start t')
  from start.hyps start.prems[of "0" "case_nat t (\<lambda>x. s0)"] show ?case by auto
next
  case (step t' s)
  from step(4) guess n \<omega> . note \<omega> = this
  let ?\<omega> = "case_nat t' \<omega>"
  show ?case
  proof (rule step.prems)
    fix i show "i < Suc n \<Longrightarrow> ?\<omega> i \<in> \<Phi>" "?\<omega> (Suc n) = t" "i \<le> Suc n \<Longrightarrow> ?\<omega> i \<in> E (case_nat s ?\<omega> i)"
      using \<omega>(1, 2)[of "i - 1"] \<omega>(3) step.hyps(1,2) by (auto split: nat.split)
  qed
qed

lemma reachableI:
  "(\<And>i. i \<le> n \<Longrightarrow> \<omega> i \<in> E (case_nat s \<omega> i)) \<Longrightarrow> (\<And>i. i < n \<Longrightarrow> \<omega> i \<in> \<Phi>) \<Longrightarrow> \<omega> n = t \<Longrightarrow>
    t \<in> reachable \<Phi> s"
proof (induct n arbitrary: t)
  case (Suc n)
  from Suc.prems Suc.hyps[of "\<omega> n"]
  have "\<omega> n \<in> reachable \<Phi> s" by auto
  with Suc.prems(1)[of "Suc n"] Suc.prems(2)[of n] Suc.prems(3)
  show ?case
    by (auto intro: reachable.intros)
qed (auto intro: reachable.intros)

lemma reachableI2:
  "(\<And>i. i \<le> n \<Longrightarrow> \<omega> i \<in> E (case_nat s \<omega> i)) \<Longrightarrow> (\<And>i. i < n \<Longrightarrow> \<omega> i \<in> \<Phi>) \<Longrightarrow> \<omega> n \<in> reachable \<Phi> s"
  by (rule reachableI[of n \<omega>]) auto

subsection {* The path generating function *}

primrec path :: "'s \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> (nat \<Rightarrow> 's)" where
  "path s x 0 = x 0 (if s \<in> S then s else s0)"
| "path s x (Suc n) = x (Suc n) (path s x n)"

abbreviation
  "S_seq \<equiv> (\<Pi>\<^sub>M n\<in>UNIV::nat set. count_space S)"

definition
  "paths s = distr D_seq S_seq (path s)"

lemma sets_paths[simp]: "sets (paths s) = sets S_seq" by (simp add: paths_def)
lemma space_paths[simp]: "space (paths s) = space S_seq" by (simp add: paths_def)
lemma measurable_paths1[simp]: 
  "measurable (paths s) M = measurable S_seq M" by (simp add: measurable_def)
lemma measurable_paths2[simp]:
  "measurable M (paths s) = measurable M S_seq" by (simp add: measurable_def)

lemma path_in_S: "x \<in> space D_seq \<Longrightarrow> path s x n \<in> S"
  by (induct n) (auto simp: s0 space_PiM PiE_iff)

lemma measurable_path:
  "path s \<in> measurable D_seq S_seq"
proof (rule measurable_PiM_single')
  fix i show "(\<lambda>\<omega>. path s \<omega> i) \<in> measurable D_seq (count_space S)"
  proof (induct i)
    case (Suc i)
    note measurable_compose_countable[OF countable_space this, measurable (raw)]
    show ?case
      unfolding path.simps by measurable
  qed (simp add: s0)
qed (simp add: path_in_S PiE_iff)

lemma measurable_path'[measurable (raw)]:
  assumes f: "f \<in> measurable M (count_space S)" and g: "g \<in> measurable M D_seq"
  shows "(\<lambda>x. path (f x) (g x)) \<in> measurable M S_seq"
  using measurable_compose_countable[OF countable_space f,
      OF measurable_compose[OF g measurable_path]] .

lemma path_case_nat:
  "s \<in> S \<Longrightarrow> s' \<in> S \<rightarrow> S \<Longrightarrow> path s (case_nat s' \<omega>) i = case_nat (s' s) (path (s' s) \<omega>) i"
  by (induct i) (auto split: nat.split)

lemma path_comb_seq:
  assumes "s \<in> S" and \<omega>: "\<omega> \<in> space D_seq"
  shows "path s (comb_seq i \<omega> \<omega>') = comb_seq i (path s \<omega>) (path (case_nat s (path s \<omega>) i) \<omega>')"
proof (induct i arbitrary: \<omega>')
  case 0 then show ?case by (simp add: comb_seq_0)
next
  case (Suc n)
  moreover have "path (case_nat s (path s \<omega>) n) (case_nat (\<omega> n) \<omega>') = case_nat (path s \<omega> n) (path (path s \<omega> n) \<omega>')" (is "?A = ?B")
  proof
    fix i show "?A i = ?B i" by (induct i) (simp_all split: nat.split add: \<omega> path_in_S)
  qed
  ultimately show ?case
    by (simp add: comb_seq_Suc)
qed

subsection {* @{const paths} is a probability space *}

end

sublocale Discrete_Markov_Kernel \<subseteq> prob_space "paths s" for s
  unfolding paths_def using measurable_path by (rule P.prob_space_distr)

lemma measurable_component_singleton_const[measurable_app]:
  assumes f: "f \<in> measurable N (Pi\<^sub>M I (\<lambda>i. M))"
  assumes i: "i \<in> I"
  shows "(\<lambda>x. (f x) i) \<in> measurable N M"
  using measurable_compose[OF f measurable_component_singleton, OF i] .

context Discrete_Markov_Kernel
begin

lemma borel_measurable_positive_integral_paths[measurable (raw)]:
  assumes f: "f \<in> measurable M (count_space S)"
  assumes g: "(\<lambda>(x, y). g x y) \<in> borel_measurable (M \<Otimes>\<^sub>M S_seq)"
  shows "(\<lambda>x. integral\<^sup>P (paths (f x)) (g x)) \<in> borel_measurable M"
  by (rule measurable_compose_countable[OF countable_space f])
     (simp add: g borel_measurable_positive_integral cong: measurable_cong_sets)

lemma borel_measurable_lebesgue_integral_paths[measurable (raw)]:
  fixes g :: "_ \<Rightarrow> _ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes f: "f \<in> measurable M (count_space S)"
  assumes g: "(\<lambda>(x, y). g x y) \<in> borel_measurable (M \<Otimes>\<^sub>M S_seq)"
  shows "(\<lambda>x. integral\<^sup>L (paths (f x)) (g x)) \<in> borel_measurable M"
  by (rule measurable_compose_countable[OF countable_space f])
     (simp add: g borel_measurable_lebesgue_integral cong: measurable_cong_sets)

subsection {* Show splitting rules *}

lemma positive_integral_split:
  assumes [simp]: "s \<in> S" and f[measurable]: "f \<in> borel_measurable S_seq"
  shows "(\<integral>\<^sup>+\<omega>. f \<omega> \<partial>paths s) = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. f (comb_seq i \<omega> \<omega>') \<partial>paths (case_nat s \<omega> i)) \<partial>paths s)"
proof -
  have "(\<integral>\<^sup>+\<omega>. f \<omega> \<partial>(paths s)) = (\<integral>\<^sup>+\<omega>. f (path s \<omega>) \<partial>D_seq)"
    unfolding paths_def positive_integral_distr[OF measurable_path f] ..
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. f (path s \<omega>) \<partial>distr (D_seq \<Otimes>\<^sub>M D_seq) D_seq (\<lambda>(\<omega>, \<omega>'). comb_seq i \<omega> \<omega>'))"
    unfolding PiM_comb_seq ..
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. f (path s ((\<lambda>(\<omega>, \<omega>'). comb_seq i \<omega> \<omega>') \<omega>)) \<partial>(D_seq \<Otimes>\<^sub>M D_seq))"
    by (subst positive_integral_distr) auto
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. f (path s (comb_seq i \<omega> \<omega>')) \<partial>D_seq) \<partial>D_seq)"
    by (subst P.positive_integral_fst[symmetric]) auto
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. f (comb_seq i (path s \<omega>) (path (case_nat s (path s \<omega>) i) \<omega>')) \<partial>D_seq) \<partial>D_seq)"
    by (intro positive_integral_cong) (simp add: path_comb_seq)
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. f (comb_seq i \<omega> (path (case_nat s \<omega> i) \<omega>')) \<partial>D_seq) \<partial>paths s)"
    unfolding paths_def by (simp add: positive_integral_distr)
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. f (comb_seq i \<omega> \<omega>') \<partial>paths (case_nat s \<omega> i)) \<partial>paths s)"
    unfolding paths_def by (intro positive_integral_cong) (simp add: positive_integral_distr)
  finally show ?thesis .
qed
  
lemma integrable_split_AE:
  fixes f :: "_ \<Rightarrow> _::{banach, second_countable_topology}"
  assumes [simp]: "s \<in> S" and f: "integrable (paths s) f"
  shows "AE \<omega> in paths s. integrable (paths (case_nat s \<omega> i)) (\<lambda>\<omega>'. f (comb_seq i \<omega> \<omega>'))"
proof -
  have [measurable]: "f \<in> borel_measurable S_seq"
    using f[THEN borel_measurable_integrable] by simp

  have "(\<integral>\<^sup>+ \<omega>. (\<integral>\<^sup>+ \<omega>'. norm (f (comb_seq i \<omega> \<omega>')) \<partial>paths (case_nat s \<omega> i)) \<partial>paths s) \<noteq> \<infinity>"
    using f unfolding integrable_iff_bounded
    by (subst (asm) positive_integral_split[of s "\<lambda>x. norm (f x)"]) auto
  then have "AE \<omega> in paths s. (\<integral>\<^sup>+ \<omega>'. norm (f (comb_seq i \<omega> \<omega>')) \<partial>paths (case_nat s \<omega> i)) \<noteq> \<infinity>"
    by (rule positive_integral_PInf_AE[rotated]) simp
  then show ?thesis
    unfolding integrable_iff_bounded by auto
qed

lemma integrable_split:
  fixes f :: "_ \<Rightarrow> real"
  assumes [simp]: "s \<in> S" and f: "integrable (paths s) f"
  shows "integrable (paths s) (\<lambda>\<omega>. integral\<^sup>L (paths (case_nat s \<omega> i)) (\<lambda>\<omega>'. f (comb_seq i \<omega> \<omega>')))"
proof -
  have [measurable]: "f \<in> borel_measurable S_seq"
    using f[THEN integrableD(1)] by simp
  have f_abs: "integrable (paths s) (\<lambda>x. \<bar>f x\<bar>)"
    using f by (rule integrable_abs)
  from integrableD[OF this]
  have "(\<integral>\<^sup>+ \<omega>. (\<integral>\<^sup>+ \<omega>'. ereal \<bar>f (comb_seq i \<omega> \<omega>')\<bar> \<partial>paths (case_nat s \<omega> i)) \<partial>paths s) \<noteq> \<infinity>"
    by (subst positive_integral_split[OF `s\<in>S`, symmetric]) auto
  also have "(\<integral>\<^sup>+ \<omega>. (\<integral>\<^sup>+ \<omega>'. ereal \<bar>f (comb_seq i \<omega> \<omega>')\<bar> \<partial>paths (case_nat s \<omega> i)) \<partial>paths s) =
      (\<integral>\<^sup>+ \<omega>. ereal (\<integral> \<omega>'. \<bar>f (comb_seq i \<omega> \<omega>')\<bar> \<partial>paths (case_nat s \<omega> i)) \<partial>paths s)"
    using integrable_split_AE[OF `s\<in>S` f_abs, of i]
    by (intro positive_integral_cong_AE) (auto simp: positive_integral_eq_integral)
  finally have
      "integrable (paths s) (\<lambda>\<omega>. integral\<^sup>L (paths (case_nat s \<omega> i)) (\<lambda>\<omega>'. \<bar>f (comb_seq i \<omega> \<omega>')\<bar>))"
    apply (intro integrableI_nonneg_bounded)
    apply simp
    using integrable_split_AE[OF `s\<in>S` f, of i]
    apply eventually_elim
    apply (auto intro!: integral_nonneg_AE)
    done
  then have "integrable (paths s) (\<lambda>\<omega>. \<bar>integral\<^sup>L (paths (case_nat s \<omega> i)) (\<lambda>\<omega>'. f (comb_seq i \<omega> \<omega>'))\<bar>)"
    apply (rule integrable_bound)
    apply simp
    using integrable_split_AE[OF `s\<in>S` f, of i]
    apply eventually_elim
    apply simp
    apply (subst (2) abs_of_nonneg)
    apply (intro integral_nonneg_AE)
    apply (auto simp: integral_norm_bound1)
    done
  then show ?thesis
    by (rule integrable_abs_cancel) simp
qed

lemma integral_split:
  fixes f :: "_ \<Rightarrow> real"
  assumes [simp]: "s \<in> S" and f: "integrable (paths s) f"
  shows "(\<integral>\<omega>. f \<omega> \<partial>(paths s)) = (\<integral>\<omega>. (\<integral>\<omega>'. f (comb_seq i \<omega> \<omega>') \<partial>(paths (case_nat s \<omega> i))) \<partial>paths s)"
proof -
  have [measurable]: "f \<in> borel_measurable S_seq"
    using f[THEN integrableD(1)] by simp

  { fix f :: "_ \<Rightarrow> real" assume f: "integrable (paths s) f" and nneg: "\<And>x. 0 \<le> f x"
    then have "(\<integral>\<omega>. f \<omega> \<partial>(paths s)) = real (\<integral>\<^sup>+\<omega>. f \<omega> \<partial>(paths s))"
      by (rule integral_eq_positive_integral)
    also have "\<dots> = real (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. f (comb_seq i \<omega> \<omega>') \<partial>(paths (case_nat s \<omega> i))) \<partial>paths s)"
      using integrableD(1)[OF f] by (subst positive_integral_split) auto
    also have "\<dots> = real (\<integral>\<^sup>+\<omega>. (\<integral>\<omega>'. f (comb_seq i \<omega> \<omega>') \<partial>(paths (case_nat s \<omega> i))) \<partial>paths s)"
      using integrable_split_AE[OF `s\<in>S` f, of i] AE_space
      by (intro positive_integral_cong_AE arg_cong[where f=real])
         (auto simp: nneg positive_integral_eq_integral)
    also have "\<dots> = (\<integral>\<omega>. (\<integral>\<omega>'. f (comb_seq i \<omega> \<omega>') \<partial>(paths (case_nat s \<omega> i))) \<partial>paths s)"
      using integrable_split_AE[OF `s \<in> S` f, of i] integrable_split[OF `s \<in> S` f, of i]
      by (subst positive_integral_eq_integral) (auto intro!: integral_nonneg_AE nneg)
    finally have "(\<integral>\<omega>. f \<omega> \<partial>(paths s)) =
      (\<integral>\<omega>. (\<integral>\<omega>'. f (comb_seq i \<omega> \<omega>') \<partial>(paths (case_nat s \<omega> i))) \<partial>paths s)" . }
  note nonneg = this
  def Pf \<equiv> "\<lambda>x. max 0 (f x)" and Nf \<equiv> "\<lambda>x. max 0 (- f x)"
  then have f_eq: "f = (\<lambda>x. Pf x - Nf x)"
    and Pf: "integrable (paths s) Pf" "\<And>x. 0 \<le> Pf x"
    and Nf: "integrable (paths s) Nf" "\<And>x. 0 \<le> Nf x"
    by (auto intro!: integrable_max f)
  then have "(\<integral>\<omega>. f \<omega> \<partial>(paths s)) = (\<integral>\<omega>. Pf \<omega> \<partial>(paths s)) - (\<integral>\<omega>. Nf \<omega> \<partial>(paths s))"
    by simp
  also have "\<dots> = (\<integral>\<omega>. (\<integral>\<omega>'. Pf (comb_seq i \<omega> \<omega>') \<partial>(paths (case_nat s \<omega> i))) \<partial>paths s) -
      (\<integral>\<omega>. (\<integral>\<omega>'. Nf (comb_seq i \<omega> \<omega>') \<partial>(paths (case_nat s \<omega> i))) \<partial>paths s)"
    using nonneg[OF Pf] nonneg[OF Nf] by simp
  also have "\<dots> = (\<integral>\<omega>. (\<integral>\<omega>'. Pf (comb_seq i \<omega> \<omega>') \<partial>(paths (case_nat s \<omega> i))) -
      (\<integral>\<omega>'. Nf (comb_seq i \<omega> \<omega>') \<partial>(paths (case_nat s \<omega> i))) \<partial>paths s)"
    by (intro integral_diff[symmetric] integrable_split Pf Nf `s\<in>S`)
  also have "\<dots> = (\<integral>\<omega>. (\<integral>\<omega>'. Pf (comb_seq i \<omega> \<omega>') - Nf (comb_seq i \<omega> \<omega>') \<partial>(paths (case_nat s \<omega> i))) \<partial>paths s)"
    using integrable_split_AE[OF `s\<in>S` Pf(1), of i] integrable_split_AE[OF `s\<in>S` Nf(1), of i]
    apply (intro integral_cong_AE borel_measurable_diff borel_measurable_lebesgue_integral_paths
      measurable_split_conv[THEN iffD2]
      measurable_compose[OF _ borel_measurable_integrable[OF Pf(1)]]
      measurable_compose[OF _ borel_measurable_integrable[OF Nf(1)]] )
    apply auto
    done
  finally show ?thesis
    by (simp add: f_eq)
qed

lemma emeasure_split:
  assumes [simp]: "s \<in> S" and A[measurable]: "A \<in> sets S_seq"
  shows "emeasure (paths s) A =
    (\<integral>\<^sup>+\<omega>. emeasure (paths (case_nat s \<omega> i)) (comb_seq i \<omega> -` A \<inter> space S_seq) \<partial>paths s)"
proof -
  have "emeasure (paths s) A = (\<integral>\<^sup>+ x. indicator A x \<partial>paths s)"
    using A by auto
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. indicator A (comb_seq i \<omega> \<omega>') \<partial>(paths (case_nat s \<omega> i))) \<partial>paths s)"
    by (subst positive_integral_split) auto
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. indicator (comb_seq i \<omega> -` A \<inter> space S_seq) \<omega>' \<partial>(paths (case_nat s \<omega> i))) \<partial>paths s)"
    by (auto intro!: positive_integral_cong simp: indicator_def)
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. emeasure (paths (case_nat s \<omega> i)) (comb_seq i \<omega> -` A \<inter> space S_seq) \<partial>paths s)"
    by (auto intro!: positive_integral_cong positive_integral_indicator)
  finally show ?thesis .
qed

lemma emeasure_split_Collect:
  assumes "s \<in> S" and P: "{x\<in>space S_seq. P x} \<in> sets S_seq"
  shows "emeasure (paths s) {x\<in>space (paths s). P x} =
      (\<integral>\<^sup>+\<omega>. emeasure (paths (case_nat s \<omega> i)) {\<omega>'\<in>space S_seq. P (comb_seq i \<omega> \<omega>')} \<partial>paths s)"
  using emeasure_split[OF assms, of i]
  using measurable_space[OF measurable_comb_seq, of _ "count_space S" i]
  by (auto intro!: positive_integral_cong arg_cong2[where f=emeasure]
           simp: space_PiM `s \<in> S` PiE_iff space_pair_measure split: nat.split)

lemma prob_split:
  assumes "s \<in> S" and A: "A \<in> sets S_seq"
  shows "prob s A =
    (\<integral>\<omega>. prob (case_nat s \<omega> i) (comb_seq i \<omega> -` A \<inter> space S_seq) \<partial>paths s)"
  using assms
  apply (simp add: integral_real_indicator[symmetric] del: integral_real_indicator)
  apply (subst integral_split)
  apply (auto intro!: integral_cong split: split_indicator
              simp add: integral_real_indicator[symmetric] simp del: integral_real_indicator)
  done

lemma prob_split_Collect:
  assumes "s \<in> S" and P: "{x\<in>space S_seq. P x} \<in> sets S_seq"
  shows "\<P>(x in paths s. P x) = (\<integral>\<omega>. \<P>(\<omega>' in paths (case_nat s \<omega> i). P (comb_seq i \<omega> \<omega>')) \<partial>paths s)"
  using prob_split[OF assms, of i]
  using measurable_space[OF measurable_comb_seq, of _ "count_space S" i]
  by (auto intro!: integral_cong arg_cong2[where f=measure]
           simp: space_PiM `s \<in> S` PiE_iff space_pair_measure split: nat.split)

lemma AE_split:
  assumes [simp]: "s \<in> S" and P[measurable]: "{x\<in>space S_seq. P x} \<in> sets S_seq"
  shows "(AE \<omega> in paths s. P \<omega>) \<longleftrightarrow>
    (AE \<omega> in paths s. AE \<omega>' in paths (case_nat s \<omega> i). P (comb_seq i \<omega> \<omega>'))"
proof -
  have "(AE x in paths s. P x) \<longleftrightarrow> integral\<^sup>P (paths s) (indicator {x. \<not> P x}) = 0"
    using P by (subst AE_iff_positive_integral) auto
  also have "integral\<^sup>P (paths s) (indicator {x. \<not> P x}) =
    (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. indicator {\<omega>. \<not> P \<omega>} (comb_seq i \<omega> \<omega>') \<partial>(paths (case_nat s \<omega> i))) \<partial>paths s)"
    by (subst positive_integral_split) auto
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. indicator {\<omega>'. \<not> P (comb_seq i \<omega> \<omega>')} \<omega>' \<partial>(paths (case_nat s \<omega> i))) \<partial>paths s)"
    by (auto intro!: positive_integral_cong split: split_indicator)
  also have "((\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. indicator {\<omega>'. \<not> P (comb_seq i \<omega> \<omega>')} \<omega>' \<partial>(paths (case_nat s \<omega> i))) \<partial>paths s) = 0) \<longleftrightarrow>
    (AE \<omega> in paths s. (\<integral>\<^sup>+\<omega>'. indicator {\<omega>'. \<not> P (comb_seq i \<omega> \<omega>')} \<omega>' \<partial>(paths (case_nat s \<omega> i))) = 0)"
    by (subst positive_integral_0_iff_AE) (simp, simp add: eq_iff positive_integral_positive)
  also have "\<dots> \<longleftrightarrow> (AE \<omega> in paths s. AE \<omega>' in paths (case_nat s \<omega> i). P (comb_seq i \<omega> \<omega>'))"
    by (intro AE_cong) (simp add: AE_iff_positive_integral)
  finally show ?thesis .
qed

subsection {* Specialize splitting rules to iteration rules *}

lemma distr_K:
  assumes [simp]: "s \<in> S" shows "distr (paths s) (K s) (\<lambda>\<omega>. \<omega> 0) = K s"
proof -
  have "distr (Pi\<^sub>M UNIV (\<lambda>n::nat. D)) (K s) (\<lambda>x. x 0 s) =
    distr (distr (Pi\<^sub>M UNIV (\<lambda>n::nat. D)) D (\<lambda>x. x 0)) (K s) (\<lambda>x. x s)"
    by (subst distr_distr) (auto simp: comp_def)
  also have "\<dots> = K s"
    by (simp add: PiM_component D.PiM_component)
  finally show ?thesis
    unfolding paths_def
    by (subst distr_distr) (auto simp: comp_def)
qed

lemma positive_integral_paths_0:
  assumes s[simp]: "s \<in> S" shows "(\<integral>\<^sup>+\<omega>. f (\<omega> 0) \<partial>paths s) = (\<integral>\<^sup>+s'. f s' \<partial>K s)"
  by (subst distr_K[symmetric, OF s]) (simp add: positive_integral_distr)

lemma emeasure_paths_0:
  assumes s[simp]: "s \<in> S"
  shows "emeasure (paths s) {\<omega>\<in>space S_seq. P (\<omega> 0)} = emeasure (K s) {s'\<in>space (count_space S). P s'}"
  apply (subst distr_K[symmetric, OF s]) 
  apply (subst emeasure_distr)
  apply (auto intro!: arg_cong2[where f=emeasure] simp: space_PiM)
  done

lemma measure_paths_0:
  assumes s[simp]: "s \<in> S"
  shows "measure (paths s) {\<omega>\<in>space S_seq. P (\<omega> 0)} = measure (K s) {s'\<in>space (count_space S). P s'}"
  using emeasure_paths_0[OF assms, of P] unfolding K.emeasure_eq_measure emeasure_eq_measure by simp

lemma prob_paths_0:
  assumes s[simp]: "s \<in> S"
  shows "\<P>(\<omega> in paths s. P (\<omega> 0)) = \<P>(t in K s. P t)"
  using emeasure_paths_0[OF assms, of P] unfolding K.emeasure_eq_measure emeasure_eq_measure by simp

lemma integrable_paths_0:
  fixes f :: "_ \<Rightarrow> real"
  assumes s[simp]: "s \<in> S"
  shows "integrable (paths s) (\<lambda>\<omega>. f (\<omega> 0)) = integrable (K s) f"
  apply (subst distr_K[symmetric, OF s]) 
  apply (rule integrable_distr_eq[symmetric])
  apply measurable
  done

lemma integral_paths_0:
  fixes f :: "_ \<Rightarrow> real"
  assumes s[simp]: "s \<in> S"
  shows "integral\<^sup>L (paths s) (\<lambda>\<omega>. f (\<omega> 0)) = integral\<^sup>L (K s) f"
  apply (subst distr_K[symmetric, OF s]) 
  apply (rule integral_distr[symmetric])
  apply measurable
  done

lemma AE_paths_0:
  assumes s[simp]: "s \<in> S"
  shows "(AE \<omega> in paths s. P (\<omega> 0)) = (AE s' in K s. P s')"
  apply (subst distr_K[symmetric, OF s])
  apply (subst AE_distr_iff)
  apply measurable
  done

lemma positive_integral_iterate:
  assumes [simp]: "s \<in> S" and f: "f \<in> borel_measurable S_seq"
  shows "(\<integral>\<^sup>+\<omega>. f \<omega> \<partial>(paths s)) = (\<integral>\<^sup>+s'. (\<integral>\<^sup>+\<omega>. f (case_nat s' \<omega>) \<partial>(paths s')) \<partial>K s)" 
  by (subst positive_integral_split[OF assms, where i=1])
     (simp add: positive_integral_paths_0[symmetric])

lemma integrable_iterate_AE:
  fixes f :: "_ \<Rightarrow> real"
  assumes s[simp]: "s \<in> S" and f: "integrable (paths s) f"
  shows "AE s' in K s. integrable (paths s') (\<lambda>\<omega>. f (case_nat s' \<omega>))"
  using integrable_split_AE[OF assms, where i=1]
  apply simp
  apply (subst (asm)  AE_paths_0)
  apply simp_all
  done

lemma integrable_iterate:
  fixes f :: "_ \<Rightarrow> real"
  assumes [simp]: "s \<in> S" and f: "integrable (paths s) f"
  shows "integrable (K s) (\<lambda>s'. integral\<^sup>L (paths s') (\<lambda>\<omega>. f (case_nat s' \<omega>)))"
  using integrable_split[OF assms, where i=1]
  by (simp add: integrable_paths_0[symmetric])

lemma integral_iterate:
  fixes f :: "_ \<Rightarrow> real"
  assumes [simp]: "s \<in> S" and f: "integrable (paths s) f"
  shows "(\<integral>\<omega>. f \<omega> \<partial>(paths s)) = (\<integral>s'. (\<integral>\<omega>. f (case_nat s' \<omega>) \<partial>(paths s')) \<partial>K s)"
  by (subst integral_split[OF assms, where i=1])
     (simp add: integral_paths_0[symmetric])
  
lemma emeasure_iterate:
  assumes [simp]: "s \<in> S" and A[measurable]: "A \<in> sets S_seq"
  shows "emeasure (paths s) A = (\<integral>\<^sup>+s'. emeasure (paths s') (case_nat s' -` A \<inter> space S_seq) \<partial>K s)"
  apply (subst emeasure_split[OF assms, where i=1])
  apply simp
  apply (subst positive_integral_paths_0)
  apply simp_all
  done

lemma prob_iterate:
  assumes "s \<in> S" and A: "A \<in> sets S_seq"
  shows "prob s A = (\<integral>s'. prob s' (case_nat s' -` A \<inter> space S_seq) \<partial>K s)"
  using assms
  apply (simp add: integral_real_indicator[symmetric] del: integral_real_indicator)
  apply (subst integral_iterate)
  apply (auto intro!: integral_cong split: split_indicator
              simp add: integral_real_indicator[symmetric] simp del: integral_real_indicator)
  done
  
lemma prob_iterate_Collect:
  assumes "s \<in> S" and P: "{x\<in>space S_seq. P x} \<in> sets S_seq"
  shows "\<P>(x in paths s. P x) = (\<integral>s'. \<P>(x in paths s'. P (case_nat s' x)) \<partial>K s)"
  using prob_iterate[OF assms]
  by (auto intro!: integral_cong arg_cong2[where f=measure] simp: space_PiM `s \<in> S` PiE_iff 
           split: nat.split)

lemma AE_iterate:
  assumes [simp]: "s \<in> S" and P[measurable]: "{x\<in>space S_seq. P x} \<in> sets S_seq"
  shows "(AE x in paths s. P x) \<longleftrightarrow> (AE s' in K s. AE x in paths s'. P (case_nat s' x))"
  apply (subst AE_split[OF assms, where i=1])
  apply (simp cong del: AE_cong)
  apply (subst AE_paths_0)
  apply simp_all
  done

lemma AE_all_enabled:
  assumes s[simp]: "s \<in> S" shows "AE \<omega> in paths s. \<forall>i. \<omega> i \<in> E (case_nat s \<omega> i)"
  unfolding AE_all_countable
proof
  fix i from s show "AE \<omega> in paths s. \<omega> i \<in> E (case_nat s \<omega> i)"
  proof (induct i arbitrary: s)
    case 0 with AE_enabled[of s] show ?case by (subst AE_iterate) auto
  next
    case (Suc i) then show ?case by (subst AE_iterate) auto
  qed
qed

subsection {* Show fairness *}

text {*

  The fairness proof is similar to Theorem~8.1.5 in Baier 1998 (Habilitation thesis).
  The differences are

  \begin{itemize}
    \item we only prove it for s-fairness (only one transition)
    \item our prove works for systems with arbitrary size, i.e.\ also countable infinite systems
  \end{itemize}

*}

definition "fair s t \<omega> \<longleftrightarrow> finite {i. \<omega> i = s \<and> \<omega> (Suc i) = t} \<longrightarrow> finite {i. \<omega> i = s}"

lemma fairI: 
  "(finite {i. case_nat s' \<omega> i = s \<and> \<omega> i = t} \<Longrightarrow> finite {i. case_nat s' \<omega> i = s}) \<Longrightarrow>
  fair s t (case_nat s' \<omega>)"
  unfolding fair_def by auto

lemma measurable_fair[measurable]: "{\<omega>\<in>space S_seq. fair s t \<omega>} \<in> sets S_seq"
  unfolding fair_def by simp

lemma positive_integral_prefixes:
  assumes s[simp]: "s \<in> S"
  assumes [measurable]: "i \<in> measurable S_seq (count_space UNIV)"
    and [measurable]: "f \<in> borel_measurable S_seq"
    and f: "AE x in paths s. 0 \<le> f x"
    and inv_i: "\<And>\<omega> \<omega>'. 0 < i \<omega> \<Longrightarrow> (\<And>j. j < i \<omega> \<Longrightarrow> \<omega> j = \<omega>' j) \<Longrightarrow> i \<omega> = i \<omega>'"
    and inv_f: "\<And>\<omega>. i \<omega> = 0 \<Longrightarrow> f \<omega> = 0"
  shows "(\<integral>\<^sup>+ \<omega>. f \<omega> \<partial>paths s) = (\<integral>\<^sup>+\<omega>. indicator {\<omega>. i \<omega> \<noteq> 0} \<omega> *
    (\<integral>\<^sup>+\<omega>'. f (comb_seq (i \<omega>) \<omega> \<omega>') \<partial>paths (case_nat s \<omega> (i \<omega>))) \<partial>paths s)"
proof -
  let ?A = "\<lambda>n. {\<omega>. i \<omega> = n \<and> i \<omega> \<noteq> 0}"
  have inv_i_eq: "\<And>\<omega> \<omega>'. 0 < i \<omega> \<Longrightarrow> 0 < i (comb_seq (i \<omega>) \<omega> \<omega>') \<Longrightarrow> i (comb_seq (i \<omega>) \<omega> \<omega>') = i \<omega>"
    by (rule inv_i[symmetric]) (simp_all add: comb_seq_def) 

  { fix \<omega> \<omega>' n assume "0 < n" and i: "i (comb_seq n \<omega> \<omega>') = n"
    with inv_i[of "comb_seq n \<omega> \<omega>'" \<omega>] have "i \<omega> = n"
      by (auto simp: comb_seq_def) }
  note inv_i' = this

  { fix \<omega> have "f \<omega> = (\<Sum>n. indicator (?A n) \<omega> * f \<omega>)"
      by (subst suminf_finite[where N="{i \<omega>}"]) (auto split: split_indicator simp: inv_f) }
  then have "(\<integral>\<^sup>+ \<omega>. f \<omega> \<partial>paths s) = (\<integral>\<^sup>+ \<omega>. (\<Sum>n. indicator (?A n) \<omega> * f \<omega>) \<partial>paths s)"
    by (rule positive_integral_cong)
  also have "\<dots> = (\<Sum>n. \<integral>\<^sup>+ \<omega>. indicator (?A n) \<omega> * f \<omega> \<partial>paths s)"
    using f by (intro positive_integral_suminf) auto
  also have "\<dots> = (\<Sum>n. \<integral>\<^sup>+ \<omega>. \<integral>\<^sup>+ \<omega>'. indicator (?A n) (comb_seq n \<omega> \<omega>') *
      f (comb_seq n \<omega> \<omega>') \<partial>paths (case_nat s \<omega> n) \<partial>paths s)"
    by (subst positive_integral_split[symmetric]) simp_all
  also have "\<dots> = (\<Sum>n. \<integral>\<^sup>+ \<omega>. \<integral>\<^sup>+ \<omega>'. indicator (?A n) \<omega> *
      f (comb_seq n \<omega> \<omega>') \<partial>paths (case_nat s \<omega> n) \<partial>paths s)"
    by (intro arg_cong[where f=suminf] ext positive_integral_cong)
       (auto split: split_indicator intro: inv_f inv_i' inv_i_eq)
  also have "\<dots> = (\<Sum>n. \<integral>\<^sup>+ \<omega>. indicator (?A n) \<omega> * \<integral>\<^sup>+ \<omega>'.
      f (comb_seq n \<omega> \<omega>') \<partial>paths (case_nat s \<omega> n) \<partial>paths s)"
    by (intro arg_cong[where f=suminf] ext positive_integral_cong)
       (simp add: positive_integral_cmult)
  also have "\<dots> = (\<Sum>n. \<integral>\<^sup>+ \<omega>. indicator (?A n) \<omega> * \<integral>\<^sup>+ \<omega>'.
      f (comb_seq (i \<omega>) \<omega> \<omega>') \<partial>paths (case_nat s \<omega> (i \<omega>)) \<partial>paths s)"
    by (intro arg_cong[where f=suminf] ext positive_integral_cong) (simp split: split_indicator)
  also have "\<dots> = (\<integral>\<^sup>+ \<omega>. (\<Sum>n. indicator (?A n) \<omega> * \<integral>\<^sup>+ \<omega>'.
      f (comb_seq (i \<omega>) \<omega> \<omega>') \<partial>paths (case_nat s \<omega> (i \<omega>))) \<partial>paths s)"
    by (simp add: positive_integral_positive positive_integral_suminf)
  also have "\<dots> = (\<integral>\<^sup>+ \<omega>. indicator {\<omega>. i \<omega> \<noteq> 0} \<omega> * \<integral>\<^sup>+ \<omega>'.
      f (comb_seq (i \<omega>) \<omega> \<omega>') \<partial>paths (case_nat s \<omega> (i \<omega>)) \<partial>paths s)" (is "integral\<^sup>P _ ?f = integral\<^sup>P _ ?g")
  proof (intro positive_integral_cong)
    fix \<omega> show "?f \<omega> = ?g \<omega>"
      by (subst suminf_finite[where N="{i \<omega>}"]) (auto split: split_indicator)
  qed
  finally show ?thesis .
qed

lemma AE_fair:
  assumes s[simp]: "s' \<in> S" and s[simp]: "s \<in> S" and t[simp]: "t \<in> E s"
  shows "AE \<omega> in paths s'. fair s t (case_nat s' \<omega>)"
proof -
  def unfair \<equiv> "\<lambda>s'. {\<omega>\<in>space S_seq. infinite {i. case_nat s' \<omega> i = s} \<and>
    (\<forall>i. case_nat s' \<omega> i = s \<longrightarrow> \<omega> i \<noteq> t)}"
  then have measurable_unfair[measurable]: "\<And>s. unfair s \<in> sets S_seq" by simp

  def i \<equiv> "\<lambda>\<omega>. if \<exists>i. \<omega> i = s then Suc (LEAST i. \<omega> i = s) else 0"
  then have measurable_i[measurable]: "i \<in> measurable S_seq (count_space UNIV)" by simp

  { fix \<omega> s' assume "0 < i \<omega>" then have "case_nat s' \<omega> (i \<omega>) = s"
      by (auto simp add: i_def intro: LeastI split: split_if_asm) }
  note i_eq = this

  { fix i have "(\<forall>n. i \<noteq> Suc n) \<longleftrightarrow> i = 0" by (cases i) auto }
  note this[simp]

  { fix s' assume [simp]: "s' \<in> S"
    have "emeasure (paths s') (unfair s') = (\<integral>\<^sup>+\<omega>. indicator (unfair s') \<omega> \<partial>paths s')"
      by simp
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. indicator {\<omega>. i \<omega> \<noteq> 0} \<omega> *
        (\<integral>\<^sup>+\<omega>'. indicator (unfair s') (comb_seq (i \<omega>) \<omega> \<omega>') \<partial>paths (case_nat s' \<omega> (i \<omega>))) \<partial>paths s')"
    proof (rule positive_integral_prefixes)
      fix \<omega> \<omega>' assume i: "0 < i \<omega>" and le: "\<And>j. j < i \<omega> \<Longrightarrow> \<omega> j = \<omega>' j"
      def j \<equiv> "i \<omega> - 1"
      from i have "\<exists>i. \<omega> i = s"
        unfolding i_def by (auto split: split_if_asm)
      then have "j < i \<omega>" "\<omega> j = s" "\<forall>k<j. \<omega> k \<noteq> s"
        by (auto simp: i_def j_def intro: LeastI_ex dest: not_less_Least split: split_if_asm)
      with le have "i \<omega>' = Suc j"
        by (subst i_def) (auto simp add: not_less[symmetric] intro!: Least_equality)
      then show "i \<omega> = i \<omega>'"
        using `0 < i \<omega>` by (simp add: j_def)
    next
      fix \<omega> assume "i \<omega> = 0"
      then have "\<And>k. \<omega> k \<noteq> s" by (auto simp: i_def split: split_if_asm)
      then show "indicator (unfair s') \<omega> = (0::ereal)"
        by (auto simp add: unfair_def nat.split[of "\<lambda>x. x = s"] split: split_indicator)
    qed simp_all
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. indicator {\<omega>. i \<omega> \<noteq> 0} \<omega> *
        (\<integral>\<^sup>+\<omega>'. indicator {\<omega>. s' = s \<longrightarrow> \<omega> 0 \<noteq> t} \<omega> * indicator (unfair s) \<omega>' \<partial>paths s) \<partial>paths s')"
    proof (intro positive_integral_cong ereal_left_mult_cong arg_cong2[where f="integral\<^sup>P"] ext)
      fix \<omega> \<omega>' assume \<omega>: "\<omega> : space (paths s')" and "indicator {\<omega>. i \<omega> \<noteq> 0} \<omega> \<noteq> 0"
      then have "0 < i \<omega>"
        by (simp add: indicator_def split: split_if_asm)
      with i_eq[of \<omega>] show "paths (case_nat s' \<omega> (i \<omega>)) = paths s"
        by simp
      
      from `0 < i \<omega>` have less_i: "\<And>n. n < i \<omega> \<Longrightarrow> \<omega> n = s \<longleftrightarrow> Suc n = i \<omega>"
        by (auto simp: i_def less_Suc_eq LeastI split: split_if_asm
                 intro: LeastI dest: not_less_Least)

      from  `0 < i \<omega>` have *: "{j. case_nat s' (comb_seq (i \<omega>) \<omega> \<omega>') j = s} =
          (if s' = s then {0} else {}) \<union> (op + (i \<omega>) ` {j. case_nat s \<omega>' j = s})"
        by (intro set_eqI)
           (auto simp add: less_i split: split_comb_seq nat.split)

      have "infinite {j. case_nat s' (comb_seq (i \<omega>) \<omega> \<omega>') j = s} \<longleftrightarrow>
          infinite {j. case_nat s \<omega>' j = s}"
        unfolding * by (auto dest!: finite_imageD simp: inj_on_def)
      moreover
      have "(\<forall>j. case_nat s' (comb_seq (i \<omega>) \<omega> \<omega>') j = s \<longrightarrow> comb_seq (i \<omega>) \<omega> \<omega>' j \<noteq> t) \<longleftrightarrow>
          (s = s' \<longrightarrow> \<omega> 0 \<noteq> t) \<and> (\<forall>j. case_nat s \<omega>' j = s \<longrightarrow> \<omega>' j \<noteq> t)"
        (is "(\<forall>j. ?P j) \<longleftrightarrow> ?t \<and> (\<forall>j. ?Q j)")
      proof (intro iffI allI conjI)
        fix j assume *: "\<forall>j. ?P j"
        show "?Q j"
          using *[THEN spec, where x="j + i \<omega>"] `0 < i \<omega>` less_i
          by (auto split: nat.splits simp: case_nat_comb_seq comb_seq_add)
        show ?t
          using *[THEN spec, of 0] `0 < i \<omega>` by (simp add: comb_seq_less)
      next
        fix j assume *: "?t \<and> (\<forall>j. ?Q j)"
        show "?P j"
        proof (cases j "i \<omega>" rule: nat_boundary_cases)
          case less with * show ?thesis
            by (simp add: comb_seq_less less_i split: nat.splits)
        next
          case (add k) with `0 < i \<omega>` conjunct2[OF *, THEN spec, of k] show ?thesis
            by (simp add: case_nat_comb_seq comb_seq_add split: nat.split_asm)
        qed
      qed
      moreover
      have "comb_seq (i \<omega>) \<omega> \<omega>' \<in> space S_seq \<longleftrightarrow> \<omega>' \<in> space S_seq"
        using \<omega> by (auto simp: space_PiM PiE_iff split: split_comb_seq)
      ultimately
      have "comb_seq (i \<omega>) \<omega> \<omega>' \<in> unfair s' \<longleftrightarrow> ?t \<and> \<omega>' \<in> unfair s"
        by (auto simp: unfair_def)
      then show "indicator (unfair s') (comb_seq (i \<omega>) \<omega> \<omega>') = 
          (indicator {\<omega>. s' = s \<longrightarrow> \<omega> 0 \<noteq> t} \<omega> * indicator (unfair s) \<omega>' :: ereal)"
        by (simp add: indicator_def)
    qed
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. indicator {\<omega>. i \<omega> \<noteq> 0 \<and> (s' = s \<longrightarrow> \<omega> 0 \<noteq> t)} \<omega> *
        (\<integral>\<^sup>+\<omega>'. indicator (unfair s) \<omega>' \<partial>paths s) \<partial>paths s')"
      by (auto simp: indicator_def intro!: positive_integral_cong)
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. indicator {\<omega>. i \<omega> \<noteq> 0 \<and> (s' = s \<longrightarrow> \<omega> 0 \<noteq> t)} \<omega> \<partial>paths s') *
        emeasure (paths s) (unfair s)"
      by (simp add: positive_integral_multc emeasure_nonneg)
    finally have "emeasure (paths s') (unfair s') = \<dots>" . }
  note split_unfair = this

  have "integral\<^sup>P (paths s) (indicator {\<omega>. i \<omega> \<noteq> 0 \<and> (s = s \<longrightarrow> \<omega> 0 \<noteq> t)}) \<le>
      (\<integral>\<^sup>+ \<omega>. indicator {s. s \<noteq> t} (\<omega> 0) \<partial>paths s)"
    by (auto split: split_indicator intro!: positive_integral_mono)
  also have "\<dots> = emeasure (K s) (space (K s) - {t})"
    by (auto simp add: positive_integral_paths_0 positive_integral_indicator'
             intro!: arg_cong2[where f=emeasure])
  also have "\<dots> = 1 - emeasure (K s) {t}"
    using K.emeasure_space_1[of s] emeasure_Diff[of "K s" "{t}" S] t unfolding E_def by auto
  also have "\<dots> < 1"
    using t measure_nonneg[of "K s" "{t}"] unfolding E_def by (simp add: K.emeasure_eq_measure one_ereal_def)
  finally have "integral\<^sup>P (paths s) (indicator {\<omega>. i \<omega> \<noteq> 0 \<and> (s = s \<longrightarrow> \<omega> 0 \<noteq> t)}) < 1" .
  with split_unfair[of s] have "emeasure (paths s) (unfair s) = 0"
    by (cases "integral\<^sup>P (paths s) (indicator {\<omega>. i \<omega> \<noteq> 0 \<and> (s = s \<longrightarrow> \<omega> 0 \<noteq> t)})")
       (auto simp: emeasure_eq_measure one_ereal_def)

  let ?P = "\<lambda>s' n \<omega>. (\<forall>i. case_nat s' \<omega> (i + n) = s \<longrightarrow> \<omega> (i + n) \<noteq> t) \<longrightarrow> 
    finite {i. case_nat s' \<omega> (i + n) = s}"
  { fix s' assume [simp]: "s' \<in> S"
    have "emeasure (paths s') {\<omega>\<in>space (paths s'). \<not> ?P s' 0 \<omega>} = emeasure (paths s') (unfair s')"
      by (auto simp: unfair_def intro!: arg_cong2[where f=emeasure])
    also have "\<dots> = 0"
      using split_unfair[of s'] `emeasure (paths s) (unfair s) = 0` by simp
    finally have "AE \<omega> in paths s'. ?P s' 0 \<omega>"
      by (rule AE_I[OF subset_refl]) auto }
  note AE_never = this

  have "AE \<omega> in paths s'. \<forall>n. ?P s' n \<omega>"
    unfolding AE_all_countable
  proof (rule, subst AE_split)
    fix n show "AE \<omega> in paths s'. AE \<omega>' in paths (case_nat s' \<omega> n). ?P s' n (comb_seq n \<omega> \<omega>')"
      by (rule AE_I2)
         (insert AE_never, simp add: comb_seq_add case_nat_comb_seq space_PiM PiE_iff split: nat.split)
  qed simp_all
  then show ?thesis
  proof (eventually_elim, intro fairI)
    fix \<omega> assume P: "\<forall>n. ?P s' n \<omega>" and fin: "finite {i. case_nat s' \<omega> i = s \<and> \<omega> i = t}"
    from fin[THEN finite_nat_bounded] obtain n where
        "\<And>i. case_nat s' \<omega> i = s \<Longrightarrow> \<omega> i = t \<Longrightarrow> i < n" 
      by auto
    with P[THEN spec, of n]
    have "finite ({n + i | i. case_nat s' \<omega> (n + i) = s} \<union> {..n})"
      by (auto simp: ac_simps)
    then show "finite {i. case_nat s' \<omega> i = s}"
      by (rule rev_finite_subset) (auto cong: conj_cong simp: not_le intro!: le_Suc_ex)
  qed
qed

lemma AE_all_fair:
  "s' \<in> S \<Longrightarrow> AE \<omega> in paths s'. \<forall>s\<in>S. \<forall>t\<in>E s. fair s t (case_nat s' \<omega>)"
  by (intro AE_all_E AE_all_S AE_fair)

lemma fair_eq: "fair sx tx \<omega> \<longleftrightarrow>
  (\<exists>j. \<forall>i\<ge>j. \<omega> i \<noteq> sx) \<or> (\<forall>i. \<exists>j\<ge>i. \<omega> j = sx \<and> \<omega> (Suc j) = tx)"
  unfolding fair_def finite_nat_set_iff_bounded disj_not2[symmetric]
  by (simp add: not_le not_less) blast

subsection {* @{text until} *}

definition until :: "'s set \<Rightarrow> 's set \<Rightarrow> (nat \<Rightarrow> 's) set" where
  "until \<Phi> \<Psi> = {\<omega>. \<exists>n. (\<forall>i<n. \<omega> i \<in> \<Phi>) \<and> \<omega> n \<in> \<Psi>}"

lemma untilI:
  "(\<And>i. i < n \<Longrightarrow> \<omega> i \<in> \<Phi>) \<Longrightarrow> \<omega> n \<in> \<Psi> \<Longrightarrow> \<omega> \<in> until \<Phi> \<Psi>"
  by (auto simp: until_def)

lemma untilE:
  assumes \<omega>: "\<omega> \<in> until \<Phi> \<Psi>"
  obtains (until) n where "\<And>i. i < n \<Longrightarrow> \<omega> i \<in> \<Phi> - \<Psi>" "\<omega> n \<in> \<Psi>"
proof -
  from \<omega> obtain n where n: "\<And>i. i < n \<Longrightarrow> \<omega> i \<in> \<Phi>" "\<omega> n \<in> \<Psi>"
    by (auto simp: until_def)
  from smallest[where P="\<lambda>n. \<omega> n \<in> \<Psi>", OF n(2)] guess n' .
  with n(1) that[of n'] show thesis by auto
qed

lemma until_iff:
  "\<omega> \<in> until \<Phi> \<Psi> \<longleftrightarrow> (\<exists>n. (\<forall>i < n. \<omega> i \<in> \<Phi> - \<Psi>) \<and> \<omega> n \<in> \<Psi>)"
  by (auto elim!: untilE intro: untilI)

lemma measurable_until[measurable]: "{\<omega>\<in>space S_seq. \<omega> \<in> until \<Phi> \<Psi>} \<in> sets S_seq"
  unfolding until_def by auto

lemma case_nat_until_iff[simp]:
  "case_nat s \<omega> \<in> until \<Phi> \<Psi> \<longleftrightarrow> (s \<in> \<Psi> \<or> (s \<in> \<Phi> \<and> \<omega> \<in> until \<Phi> \<Psi>))"
  by (auto simp add: all_conj_distrib set_eq_iff until_def gr0_conv_Suc split: nat.split) blast

lemma comb_seq_until:
  assumes \<omega>: "\<And>j. j < i \<Longrightarrow> \<omega> j \<in> \<Phi> - \<Psi>"
  shows "comb_seq i \<omega> \<omega>' \<in> until \<Phi> \<Psi> \<longleftrightarrow> \<omega>' \<in> until \<Phi> \<Psi>"
proof
  assume "\<omega>' \<in> until \<Phi> \<Psi>"
  from untilE[OF this] guess n .
  with \<omega> show "comb_seq i \<omega> \<omega>' \<in> until \<Phi> \<Psi>"
    by (intro untilI[of "i + n"]) (auto split: split_comb_seq)
next
  assume "comb_seq i \<omega> \<omega>' \<in> until \<Phi> \<Psi>"
  from untilE[OF this] guess n . note n = this
  moreover
  from \<omega>[of n] n(2) have "i \<le> n"
    by (auto simp: not_less[symmetric] split: split_comb_seq_asm)
  moreover
  { fix j assume "j < n - i"
    with n(1)[of "i + j"] have "\<omega>' j \<in> \<Phi> - \<Psi>"
      by (auto simp: less_diff_conv split: split_comb_seq_asm) }
  ultimately show "\<omega>' \<in> until \<Phi> \<Psi>"
    by (intro untilI[of "n - i"]) (auto split: split_comb_seq_asm)
qed

lemma single_K_measure_le_integral:
  assumes [simp]: "s \<in> S" and "t \<in> E s" and nneg: "AE t in K s. 0 \<le> f t"
    and int[measurable]: "integrable (K s) f"
  shows "measure (K s) {t} * f t \<le> (\<integral>t. f t \<partial>K s)"
proof -
  from `t \<in> E s` have [simp]: "t \<in> S" by auto
  have "measure (K s) {t} * f t = (\<integral>t'. f t * indicator {t} t' \<partial>K s)"
    by (simp add: K.emeasure_eq_measure)
  also have "\<dots> \<le> (\<integral>t'. f t' \<partial>K s)"
    using nneg by (intro integral_mono_AE) (auto intro: int split: split_indicator)
  finally show ?thesis .
qed

lemma AE_paths_iff:
  "s \<in> S \<Longrightarrow> {\<omega>\<in>space S_seq. P \<omega>} \<in> sets S_seq \<Longrightarrow> 
    (AE \<omega> in paths s. P \<omega>) \<longleftrightarrow> 
      (\<forall>\<omega>. (\<forall>j<i. \<omega> j \<in> E (case_nat s \<omega> j)) \<longrightarrow> (AE \<omega>' in paths (case_nat s \<omega> i). P (comb_seq i \<omega> \<omega>')))"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> _ \<longleftrightarrow> (\<forall>\<omega>. ?S i s P \<omega>)")
proof (induct i arbitrary: P s)
  case 0 then show ?case
    by (simp add: comb_seq_0 cong del: AE_cong)
next
  case (Suc i)
  note Suc.prems(1)[simp] and Suc.prems(2)[measurable]
  have "(AE \<omega> in paths s. P \<omega>) \<longleftrightarrow> (\<forall>t\<in>E s. AE \<omega> in paths t. P (case_nat t \<omega>))"
    by (subst AE_iterate) (auto simp: AE_K_iff cong del: AE_cong)
  also have "\<dots> \<longleftrightarrow> (\<forall>t\<in>E s. All (?S i t (\<lambda>\<omega>. P (case_nat t \<omega>))))"
    by (intro ball_cong[OF refl] Suc) auto
  also have "\<dots> \<longleftrightarrow> All (?S (Suc i) s P)"
  proof (intro iffI allI ballI)
    fix \<omega> :: "nat \<Rightarrow> 's" assume "(\<forall>t\<in>E s. All (?S i t (\<lambda>\<omega>. P (case_nat t \<omega>))))"
    from this[THEN bspec, of "\<omega> 0", THEN spec, of "\<lambda>i. \<omega> (Suc i)"]
    show "?S (Suc i) s P \<omega>"
      by (auto simp: case_nat_comb_seq' case_nat_idem all_less_Suc_split
                  cong del: AE_cong)
  next
    fix t :: 's and \<omega> :: "nat \<Rightarrow> 's" assume *: "All (?S (Suc i) s P)" and t: "t \<in> E s"
    from *[THEN spec, of "case_nat t \<omega>"] t
    show "?S i t (\<lambda>\<omega>. P (case_nat t \<omega>)) \<omega>"
      by (simp add: case_nat_comb_seq' all_less_Suc_split cong del: AE_cong)
  qed
  finally show ?case .
qed

lemma AE_nuntil_iff_not_reachable:
  assumes s[simp]: "s \<in> S"
  shows "(AE \<omega> in paths s. case_nat s \<omega> \<notin> until \<Phi> \<Psi>) \<longleftrightarrow>
      s \<notin> \<Psi> \<and> (s \<in> \<Phi> \<longrightarrow> reachable (\<Phi> - \<Psi>) s \<inter> \<Psi> = {})"
proof -
  have "\<And>\<omega>. case_nat s \<omega> \<notin> until \<Phi> \<Psi> \<longleftrightarrow> (\<forall>n. (\<forall>i<n. case_nat s \<omega> i \<in> \<Phi> - \<Psi>) \<longrightarrow> case_nat s \<omega> n \<notin> \<Psi>)"
    by (auto simp: until_iff)
  
  let ?\<omega> = "case_nat s"
  { fix x assume x: "x \<in> reachable (\<Phi> - \<Psi>) s" and "x \<in> \<Psi>" "s \<in> \<Phi>"
    from x[THEN reachableE] guess \<omega> n . note \<omega> = this
    assume "(AE \<omega> in paths s. ?\<omega> \<omega> \<notin> until \<Phi> \<Psi>)"
    with \<omega> `s\<in>\<Phi>` have "AE \<omega>' in paths (?\<omega> \<omega> (Suc n)). ?\<omega> (comb_seq (Suc n) \<omega> \<omega>') \<notin> until \<Phi> \<Psi>"
      by (subst (asm) AE_paths_iff[where i="Suc n"]) (auto elim!: allE[of _ \<omega>])
    moreover have "\<And>\<omega>'. ?\<omega> (comb_seq (Suc n) \<omega> \<omega>') \<in> until \<Phi> \<Psi>"
      using \<omega> `x \<in> \<Psi>` `s \<in> \<Phi>`
      by (auto simp: until_def intro!: exI[of _ "Suc n"] split: nat.split split_comb_seq)
    ultimately have False
      by (auto simp del: case_nat_until_iff simp add: AE_False) }
  moreover
  { assume s: "s \<notin> \<Psi>" "reachable (\<Phi> - \<Psi>) s \<inter> \<Psi> = {}"
    have "AE \<omega> in paths s. case_nat s \<omega> \<notin> until \<Phi> \<Psi>"
      using AE_all_enabled[OF `s \<in> S`]
    proof eventually_elim
      fix \<omega> assume E: "\<forall>i. \<omega> i \<in> E (case_nat s \<omega> i)"
      then have "\<And>n. (\<And>i. i < n \<Longrightarrow> \<omega> i \<in> \<Phi> - \<Psi>) \<Longrightarrow> \<omega> n \<in> reachable (\<Phi> - \<Psi>) s"
        by (intro reachableI2) auto
      with s have "\<omega> \<notin> until \<Phi> \<Psi>"
        by (auto elim!: untilE)
      then show "case_nat s \<omega> \<notin> until \<Phi> \<Psi>"
        using `s \<notin> \<Psi>` by auto
    qed }
  ultimately show ?thesis
    by (auto simp add: AE_False)
qed

lemma AE_until:
  assumes s: "s \<in> S" "s \<in> \<Phi>" and \<Phi>: "finite (\<Phi> - \<Psi>)" and closed: "reachable (\<Phi> - \<Psi>) s \<subseteq> \<Phi> \<union> \<Psi>"
  assumes enabled: "\<forall>t\<in>reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>. reachable (\<Phi> - \<Psi>) t \<inter> \<Psi> \<noteq> {}"
  shows "AE \<omega> in paths s. case_nat s \<omega> \<in> until \<Phi> \<Psi>"
  using AE_all_fair[OF `s\<in>S`] AE_all_enabled[OF `s\<in>S`]
proof eventually_elim
  fix \<omega> let ?\<omega> = "case_nat s \<omega>" and ?R = "reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>"
  assume fair: "\<forall>s\<in>S. \<forall>t\<in>E s. fair s t ?\<omega>" and E: "\<forall>i. \<omega> i \<in> E (?\<omega> i)"
  
  show "?\<omega> \<in> until \<Phi> \<Psi>"
  proof (rule ccontr)
    assume "?\<omega> \<notin> until \<Phi> \<Psi>"
    then have nuntil: "\<And>n. (\<And>i. i < n \<Longrightarrow> ?\<omega> i \<in> \<Phi> - \<Psi>) \<Longrightarrow> ?\<omega> n \<notin> \<Psi>"
      unfolding until_iff by auto
    { fix n have "?\<omega> n \<in> \<Phi> - \<Psi>"
      proof (induct n rule: nat_less_induct)
        case (1 n)
        with nuntil[of n] have "?\<omega> n \<notin> \<Psi>" by auto
        moreover
        { fix i have "i < n - 1 \<Longrightarrow> \<omega> i \<in> \<Phi> - \<Psi>"
            using 1[THEN spec, of "Suc i"] by auto }
        with E have "\<omega> (n - 1) \<in> reachable (\<Phi> - \<Psi>) s"
          by (intro reachableI2) auto
        with closed `s \<in> \<Phi>` have "?\<omega> n \<in> \<Phi> \<union> \<Psi>"
          by (cases n) auto
        ultimately show ?case by simp
      qed }
    moreover
    { fix n
      have "\<omega> n \<in> reachable (\<Phi> - \<Psi>) s"
      proof (intro reachableI2)
        fix i show "i < n \<Longrightarrow> \<omega> i \<in> \<Phi> - \<Psi>"
          using `?\<omega> (Suc i) \<in> \<Phi> - \<Psi>` by auto
      qed (insert E, auto)
      then have "\<omega> n \<in> reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>"
        using `?\<omega> (Suc n) \<in> \<Phi> - \<Psi>` by auto }
    with nuntil[of 0] have "\<And>n. ?\<omega> n \<in> ?R"
      by (auto split: nat.split)
    moreover have "finite ?R"
      using finite.insertI[OF \<Phi>, of s] by (rule rev_finite_subset) (insert closed, auto)
    moreover note pigeonhole_infinite_rel[of UNIV ?R "\<lambda>i s. ?\<omega> i = s"] \<Phi>

    ultimately obtain t where "t \<in> ?R" and t: "infinite {i. ?\<omega> i = t}"
      by auto
    with enabled obtain t' where t': "t' \<in> reachable (\<Phi> - \<Psi>) t" and "t' \<in> \<Psi>"
      by auto
    from `t \<in> ?R` have "t \<in> S"
      using closed s by auto

    from t' `t \<in> S` t have "infinite {i. ?\<omega> i = t'}"
    proof (induct rule: reachable_induct_trans)
      case (start t s)
      with fair have "infinite {i. ?\<omega> i = s \<and> \<omega> i = t}"
        by (auto simp: fair_def)
      then have "infinite (Suc ` {i. \<omega> i = t})"
        by (auto dest!: finite_imageD)
      moreover have "Suc ` {i. \<omega> i = t} \<subseteq> {i. ?\<omega> i = t}"
        by auto
      ultimately show ?case
        by (auto dest!: finite_subset)
    qed auto
    then have "{i. ?\<omega> i = t'} \<noteq> {}"
      by (intro notI) simp
    then obtain i where "?\<omega> i = t'" by auto
    with `t' \<in> \<Psi>` `?\<omega> i \<in> \<Phi> - \<Psi>` show False by auto
  qed
qed

lemma AE_until_iff_reachable:
  assumes [simp]: "s \<in> S" "finite (\<Phi> - \<Psi>)"
  shows "(AE \<omega> in paths s. case_nat s \<omega> \<in> until \<Phi> \<Psi>) \<longleftrightarrow>
    (s \<in> \<Phi> \<and> reachable (\<Phi> - \<Psi>) s \<subseteq> \<Phi> \<union> \<Psi> \<and>
      (\<forall>t\<in>reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>. reachable (\<Phi> - \<Psi>) t \<inter> \<Psi> \<noteq> {})) \<or> s \<in> \<Psi>"
proof (intro iffI disjCI conjI)
  let ?\<omega> = "case_nat s"
  assume until: "AE \<omega> in paths s. ?\<omega> \<omega> \<in> until \<Phi> \<Psi>" "s \<notin> \<Psi>"
  then show "s \<in> \<Phi>" by simp

  { fix t assume t: "t \<in> reachable (\<Phi> - \<Psi>) s"
    from t[THEN reachableE] guess \<omega> n . note \<omega> = this
    with until `s\<in>\<Phi>` have "AE \<omega>' in paths (?\<omega> \<omega> (Suc n)). comb_seq (Suc n) \<omega> \<omega>' \<in> until \<Phi> \<Psi>"
      by (subst (asm) AE_paths_iff[where i="Suc n"]) (auto elim!: allE[of _ \<omega>])
    moreover have "\<And>\<omega>'. comb_seq (Suc n) \<omega> \<omega>' \<in> until \<Phi> \<Psi> \<longleftrightarrow> case_nat t \<omega>' \<in> until \<Phi> \<Psi>"
      using \<omega> unfolding case_nat_comb_seq'
      by (subst comb_seq_Suc) (auto simp del: case_nat_until_iff intro!: comb_seq_until)
    moreover have "?\<omega> \<omega> (Suc n) = t"
      using \<omega> by simp
    ultimately have "AE \<omega>' in paths t. case_nat t \<omega>' \<in> until \<Phi> \<Psi>"
      by (simp cong del: AE_cong) }
  note shift_until = this

  { fix s assume "reachable (\<Phi> - \<Psi>) s \<inter> \<Psi> = {}" "s \<in> S" "s \<notin> \<Psi>" "s \<in> \<Phi>"
    with AE_nuntil_iff_not_reachable[of s \<Phi> \<Psi>] `s \<notin> \<Psi>` `s \<in> \<Phi>`
    have "AE \<omega> in paths s. case_nat s \<omega> \<notin> until \<Phi> \<Psi>" by auto
    moreover assume "AE \<omega> in paths s. case_nat s \<omega> \<in> until \<Phi> \<Psi>"
    ultimately have "AE \<omega> in paths s. False" by eventually_elim auto
    then have False by simp }
  note not_reachable = this

  { fix t have "t \<in> reachable (\<Phi> - \<Psi>) s \<Longrightarrow> t \<notin> \<Phi> \<union> \<Psi> \<Longrightarrow> False"
      using shift_until[of t] by auto }
  then show "reachable (\<Phi> - \<Psi>) s \<subseteq> \<Phi> \<union> \<Psi>" by auto

  show "\<forall>t\<in>reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>. reachable (\<Phi> - \<Psi>) t \<inter> \<Psi> \<noteq> {}"
  proof safe
    fix t assume "t \<in> reachable (\<Phi> - \<Psi>) s" "t \<notin> \<Psi>"
    moreover then have "AE \<omega>' in paths t. case_nat t \<omega>' \<in> until \<Phi> \<Psi>" 
      using shift_until[of t] by simp
    moreover assume "reachable (\<Phi> - \<Psi>) t \<inter> \<Psi> = {}"
    ultimately show False using not_reachable[of t] by auto
  qed (insert not_reachable[of s] `s \<in> S` `s \<in> \<Phi>` until, auto)
qed (insert AE_until[of s \<Phi> \<Psi>], auto)

subsection {* Hitting time *}

definition hitting_time :: "'s set \<Rightarrow> (nat \<Rightarrow> 's) \<Rightarrow> nat" where 
  "hitting_time \<Phi> \<omega> = (LEAST i. \<omega> i \<in> \<Phi>)"

lemma measurable_hitting_time[measurable]:
  "hitting_time \<Phi> \<in> measurable S_seq (count_space UNIV)"
  unfolding hitting_time_def[abs_def] by measurable

lemma hitting_time_eq:
  "\<omega> n \<in> \<Phi> \<Longrightarrow> (\<And>i. i < n \<Longrightarrow> \<omega> i \<notin> \<Phi>) \<Longrightarrow> hitting_time \<Phi> \<omega> = n"
  unfolding hitting_time_def
  by (rule Least_equality) (auto simp: not_less[symmetric])

lemma hitting_time_least: "i < hitting_time \<Phi> \<omega> \<Longrightarrow> \<omega> i \<notin> \<Phi>"
  unfolding hitting_time_def by (auto dest!: not_less_Least)

lemma
  assumes until: "\<omega> \<in> until S \<Phi>"
  shows hitting_time_in[intro]: "\<omega> (hitting_time \<Phi> \<omega>) \<in> \<Phi>"
proof -
  from untilE[OF until] guess n . note n = this
  moreover then have n_eq: "hitting_time \<Phi> \<omega> = n"
    by (intro hitting_time_eq) auto
  ultimately show "\<omega> (hitting_time \<Phi> \<omega>) \<in> \<Phi>"
    by auto
qed

lemma hitting_time_case_nat_Suc:
  assumes "\<omega> \<in> until S \<Phi>" "s \<notin> \<Phi>"
  shows "hitting_time \<Phi> (case_nat s \<omega>) = Suc (hitting_time \<Phi> \<omega>)"
proof -
  have "(LEAST i. (case_nat s \<omega>) i \<in> \<Phi>) = Suc (LEAST i. case_nat s \<omega> (Suc i) \<in> \<Phi>)"
    using assms by (intro Least_Suc[of _ "Suc (hitting_time \<Phi> \<omega>)"]) auto
  then show ?thesis unfolding hitting_time_def by simp
qed

lemma hitting_time_case_nat_0:
  "s \<in> \<Phi> \<Longrightarrow> hitting_time \<Phi> (case_nat s \<omega>) = 0"
  unfolding hitting_time_def by (auto intro!: Least_equality)

lemma positive_integral_hitting_time_finite:
  assumes [simp]: "s \<in> S" and \<Phi>: "finite (S - \<Phi>)"
  assumes until: "AE \<omega> in paths s. case_nat s \<omega> \<in> until S \<Phi>"
  shows "(\<integral>\<^sup>+ \<omega>. real (hitting_time \<Phi> (case_nat s \<omega>)) \<partial>paths s) \<noteq> \<infinity>"
proof cases
  assume s: "s \<in> \<Phi>" with `s \<in> S` show ?thesis by (simp add: hitting_time_case_nat_0)
next
  assume s: "s \<notin> \<Phi>"

  let ?R = "reachable (S - \<Phi>) s \<union> {s} - \<Phi>"
  let ?P = "\<lambda>n t. \<P>(\<omega> in paths t. \<forall>i<n. \<omega> i \<in> S - \<Phi>)"
  have "\<forall>t\<in>?R. \<exists>n. ?P n t < 1"
  proof
    fix t assume t: "t \<in> ?R"
    then have "t \<in> S" by auto
    from t AE_until_iff_reachable[of s S \<Phi>] `finite (S - \<Phi>)` until `s \<notin> \<Phi>`
    obtain t' where "t' \<in> reachable (S - \<Phi>) t" "t' \<in> \<Phi>" by auto
    from this `t \<in> S` 
    have "\<exists>n. \<not> (AE \<omega> in paths t. \<forall>i<n. \<omega> i \<in> S - \<Phi>)"
    proof (induct rule: reachable_induct_rev)
      case (start t)
      then show ?case
        using start `t \<in> S`
        by (auto simp add: AE_paths_0[of t "\<lambda>s. s \<notin> \<Phi>"] AE_K_iff intro!: exI[of _ "Suc 0"])
    next
      case (step t s)
      then obtain n where n: "\<not> (AE \<omega> in paths t. \<forall>i<n. \<omega> i \<in> S - \<Phi>)" by auto
      with step show ?case
        apply (intro exI[of _ "Suc n"])
        apply (simp add: all_less_Suc_split del: AE_conj_iff)
        apply (auto simp add: AE_K_iff AE_iterate[OF `s\<in>S`])
        done
    qed
    then guess n ..
    then show "\<exists>n. ?P n t < 1"
      using AE_in_set_eq_1[of "{\<omega>\<in>space (paths t). \<forall>i<n. \<omega> i \<in> S - \<Phi>}" t]
      by (auto simp add: less_le)
  qed
  from bchoice[OF this] guess N .. note N = this

  have "?R \<subseteq> S - \<Phi>" by auto
  with \<Phi> have "finite ?R" by (auto dest: finite_subset)
  have "s \<in> ?R" using `s \<notin> \<Phi>` by auto

  def n \<equiv> "Max (N ` ?R)"
  { fix s assume s: "s \<in> ?R"
    with `finite ?R` have M: "N s \<le> n" by (auto intro!: Max_ge simp: n_def)
    then have "?P n s \<le> ?P (N s) s"
      by (intro finite_measure_mono) auto
    also have "\<dots> < 1"
      using N s by auto
    finally have "?P n s < 1" . }
  note less_1 = this
  def d \<equiv> "Max (?P n`?R)"
  with `finite ?R` `s\<in>?R` less_1 have "d < 1" by (auto simp: Max_less_iff[THEN iffD1])

  have "0 < N s"
  proof (rule ccontr)
    assume "\<not> 0 < N s"
    then have "N s = 0" by simp
    with N[THEN bspec, OF `s \<in> ?R`] prob_space show False by simp
  qed
  with `s \<in> ?R` `finite ?R` have "0 < n"
    by (auto simp add: n_def Max_gr_iff intro!: bexI[of _ s])

  have d: "\<And>s. s\<in>?R \<Longrightarrow> ?P n s \<le> d"
    using `finite ?R` `s\<in>?R` unfolding d_def by (auto intro!: Max_ge)

  have "0 \<le> d"
    using d[OF `s \<in> ?R`] by (auto intro: order_trans measure_nonneg)

  { fix \<omega> t
    assume t: "t < hitting_time \<Phi> \<omega> div n"
    have "\<And>a i j. j < n \<Longrightarrow> a < i \<Longrightarrow> a * n + 0 < n * i + j"
      using `0 < n` by (intro add_less_le_mono) auto
    then have "t < hitting_time \<Phi> \<omega> div n \<longrightarrow> t * n < hitting_time \<Phi> \<omega>"
      using `0 < n` by (simp split: split_div)
    with t have "\<forall>i\<le>t*n. \<omega> i \<notin> \<Phi>"
      by (simp add: hitting_time_least) }
  note less_hitting_time = this

  { fix t
    def R \<equiv> "?R"
    then have "s \<in> R" using s `s \<in> S` by auto
    then have "emeasure (paths s) {\<omega>\<in>space (paths s). \<forall>i\<le>t * n. \<omega> i \<notin> \<Phi>} \<le> d ^ t"
    proof (induct t arbitrary: s)
      case (Suc t s')
      then have s: "s' \<in> S" unfolding R_def by auto
      let ?M = "\<lambda>\<omega>. emeasure (paths (case_nat s' \<omega> n))"
      let ?A = "\<lambda>\<omega>. {\<omega>' \<in> space S_seq. (\<forall>i\<le>Suc t * n. comb_seq n \<omega> \<omega>' i \<notin> \<Phi>)}"
      from `s'\<in>S` have "emeasure (paths s') {\<omega> \<in> space (paths s'). (\<forall>i\<le>Suc t * n. \<omega> i \<notin> \<Phi>)} =
          (\<integral>\<^sup>+\<omega>. ?M \<omega> (?A \<omega>) \<partial>paths s')"
        by (intro emeasure_split_Collect) auto
      also have "\<dots> \<le> (\<integral>\<^sup>+\<omega>. ereal (d^t) * indicator {\<omega>\<in>space (paths s'). \<forall>i<n. \<omega> i \<notin> \<Phi>} \<omega> \<partial>paths s')"
        apply (rule positive_integral_mono_AE)
        using AE_space AE_all_enabled[OF `s'\<in>S`]
      proof eventually_elim
        fix \<omega> assume \<omega>: "\<omega> \<in> space (paths s')" and E: "\<forall>i. \<omega> i \<in> E (case_nat s' \<omega> i)"
        
        { assume \<omega>: "\<And>i. i < n \<Longrightarrow> \<omega> i \<in> S - \<Phi>"
          with E have "\<omega> (n - 1) \<in> reachable (S - \<Phi>) s'"
            by (intro reachableI2) (auto split: nat.split)
          with \<omega> Suc(2) have "case_nat s' \<omega> n \<in> R"
            unfolding R_def by (auto intro: reachable_trans split: nat.split) }
        note in_R = this

        have "?A \<omega> \<subseteq> (if \<forall>i<n. \<omega> i \<notin> \<Phi> then {\<omega> \<in> space (paths s). (\<forall>i\<le>t * n. \<omega> i \<notin> \<Phi>)} else {})"
          (is "_ \<subseteq> ?B")
          by (simp add: space_PiM all_plus_split comb_seq_add comb_seq_less)
        then have "?M \<omega> (?A \<omega>) \<le> ?M \<omega> ?B"
          by (intro emeasure_mono) auto
        also have "\<dots> \<le> ereal (d^t) * indicator {\<omega>\<in>space (paths s'). \<forall>i<n. \<omega> i \<notin> \<Phi>} \<omega>"
          using Suc(1)[OF in_R] s \<omega>
          by (auto simp: less_Suc_eq_le space_PiM PiE_iff split: split_indicator nat.split)
        finally show "?M \<omega> (?A \<omega>) \<le> ereal (d^t) * indicator {\<omega>\<in>space (paths s'). \<forall>i<n. \<omega> i \<notin> \<Phi>} \<omega>" .
      qed
      also have "\<dots> = d^t * emeasure (paths s') {\<omega>\<in>space (paths s'). \<forall>i<n. \<omega> i \<notin> \<Phi>}"
        using `0 \<le> d` by (intro positive_integral_cmult_indicator) auto
      also have "\<dots> \<le> ereal (d^t) * d"
        using d[of s'] `0 \<le> d` Suc(2)
        by (intro ereal_mult_left_mono) (auto simp add: emeasure_eq_measure space_PiM PiE_iff R_def cong: conj_cong)
      finally show ?case
        by (simp add: ac_simps)
    qed (insert measure_le_1, simp add: one_ereal_def) }
  note upper_limit = this

  have "(\<integral>\<^sup>+ \<omega>. ereal (of_nat (hitting_time \<Phi> (case_nat s \<omega>))) \<partial>paths s) \<le>
      (\<integral>\<^sup>+ \<omega>. ereal (of_nat (hitting_time \<Phi> \<omega> div n)) * n + Suc n \<partial>paths s)"
    apply (rule positive_integral_mono_AE)
    using until
  proof eventually_elim
    fix \<omega> assume "case_nat s \<omega> \<in> until S \<Phi>"
    then have "ereal (of_nat (hitting_time \<Phi> (case_nat s \<omega>))) =
        ereal (of_nat (hitting_time \<Phi> \<omega> + 1))"
      using hitting_time_case_nat_Suc[of \<omega> \<Phi> s] `s \<notin> \<Phi>` by auto
    also have "\<dots> \<le> ereal (of_nat ((hitting_time \<Phi> \<omega> div n + 1) * n + 1))"
      using `0 < n`[THEN mod_le_divisor, of "hitting_time \<Phi> \<omega>"]
      by (simp del: of_nat_add add: div_mod_equality')
    also have "\<dots> = ereal (of_nat (hitting_time \<Phi> \<omega> div n)) * n + n + 1"
      by (simp add: field_simps real_eq_of_nat of_nat_mult)
    finally show "ereal (of_nat (hitting_time \<Phi> (case_nat s \<omega>))) \<le>
        ereal (of_nat (hitting_time \<Phi> \<omega> div n)) * n + Suc n" by simp
  qed
  also have "\<dots> = (\<integral>\<^sup>+ \<omega>. ereal (of_nat (hitting_time \<Phi> \<omega> div n)) \<partial>paths s) * n + Suc n"
    using emeasure_space_1[of s]
    by (simp add: positive_integral_add positive_integral_multc
             del: plus_ereal.simps times_ereal.simps)
  also have "\<dots> = (\<Sum>t. emeasure (paths s) {\<omega>\<in>space (paths s). t < hitting_time \<Phi> \<omega> div n}) * n + Suc n"
    by (simp add: positive_integral_nat_function)
  also have "\<dots> \<le> (\<Sum>t. emeasure (paths s) {\<omega>\<in>space (paths s). \<forall>i\<le>t * n. \<omega> i \<notin> \<Phi>}) * n + Suc n"
    by (intro ereal_add_mono ereal_mult_right_mono suminf_le_pos emeasure_mono_AE)
       (auto simp: less_hitting_time)
  also have "\<dots> \<le> (\<Sum>t. ereal (d^t)) * n + Suc n"
    by (intro ereal_add_mono ereal_mult_right_mono suminf_le_pos upper_limit) auto
  also have "\<dots> < \<infinity>"
  proof -
    have "\<exists>r. (op ^ d) sums r"
      using `0 \<le> d` `d < 1` summable_geometric[of d] by (auto simp: summable_def)
    then guess r ..
    then have "ereal r = (\<Sum>t. ereal (d^t))"
      by (intro sums_unique sums_ereal[THEN iffD2])
    then show ?thesis
      by auto
  qed
  finally show ?thesis
    by (simp add: real_eq_of_nat)
qed

end

end
