(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

theory Discrete_Time_Markov_Chain
  imports Probability
begin

section {* Preparations *}

lemma zero_notin_Suc_image: "0 \<notin> Suc ` A" by auto

lemma PiE_insert:
  "i \<notin> I \<Longrightarrow> (\<Pi>\<^isub>E i\<in>insert i I. A i) = (\<lambda>(x,f). f(i := x)) ` (A i \<times> (\<Pi>\<^isub>E i\<in>I. A i))"
  apply auto
  apply (rule_tac x="(x i, x(i := undefined))" in image_eqI)
  apply auto
  done

lemma inj_on_upd_PiE:
  assumes "i \<notin> I" shows "inj_on (\<lambda>(x,f). f(i := x)) (M \<times> (\<Pi>\<^isub>E i\<in>I. A i))"
proof (safe intro!: inj_onI ext)
  fix f g x y assume *: "f(i := x) = g(i := y)" "f \<in> extensional I" "g \<in> extensional I"
  then show "x = y" by (auto simp: fun_eq_iff split: split_if_asm)
  fix i' from * `i \<notin> I` show "f i' = g i'"
    by (cases "i' = i") (auto simp: fun_eq_iff extensional_def split: split_if_asm)
qed

lemma card_PiE:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> finite (A i)"
  shows "card (\<Pi>\<^isub>E i\<in>I. A i) = (\<Prod>i\<in>I. card (A i))"
using assms proof (induct I)
  case empty then show ?case by simp
next
  case (insert i I) then show ?case
    by (simp add: card_image inj_on_upd_PiE PiE_insert)
qed

lemma (in preorder) atMost_not_empty[simp]: "{..a} \<noteq> {}"
  by (auto simp: atMost_def)

lemma (in sigma_algebra) sets_Collect_eq:
  assumes f: "f \<in> measurable M N" "{i} \<in> sets N"
  shows "{x\<in>space M. f x = i} \<in> sets M"
proof -
  have "{x\<in>space M. f x = i} = f -` {i} \<inter> space M"
    by auto
  also have "f -` {i} \<inter> space M \<in> sets M"
    using f by (auto intro: measurable_sets)
  finally show ?thesis .
qed

interpretation pborel_sequence!: product_prob_space "\<lambda>i. pborel" "UNIV::nat set"
  by default simp

lemma space_pborel_sequence[simp]:
  "space (\<Pi>\<^isub>P i::nat\<in>UNIV. pborel) = UNIV \<rightarrow> {0 ..< 1}"
  by (simp add: extensional_def pborel_sequence.infprod_algebra_def pborel_sequence.generator_def)

lemma nat_case_in_funcset: "nat_case x f \<in> (UNIV \<rightarrow> X) \<longleftrightarrow> x \<in> X \<and> f \<in> UNIV \<rightarrow> X"
  by (auto simp: Pi_def split: nat.split)

lemma all_Suc_split: "\<And>n P. (\<forall>i\<le>Suc n. P i) \<longleftrightarrow> (\<forall>i\<le>n. P (Suc i)) \<and> P 0"
  by (metis le_eq_less_or_eq less_Suc_eq_0_disj)

lemma atMost_Suc_eq_insert_0: "{..Suc n} = insert 0 (Suc ` {..n})"
  by (metis lessThan_Suc_atMost lessThan_Suc_eq_insert_0)

lemma (in product_prob_space) measure_infprod_emb_Pi:
  assumes "J \<noteq> {}" "finite J" "J \<subseteq> I" "\<And>j. j \<in> J \<Longrightarrow> X j \<in> sets (M j)"
  shows "\<mu> (emb I J (Pi\<^isub>E J X)) = (\<Prod>j\<in>J. measure (M j) (X j))"
proof (subst measure_infprod_emb)
  interpret J: finite_product_prob_space M J
    by default fact+
  show "measure_space.measure (Pi\<^isub>M J M) (Pi\<^isub>E J X) =
    (\<Prod>j\<in>J. measure_space.measure (M j) (X j))"
    by (intro J.measure_times) fact
qed (insert assms, auto)

lemma suminf_setsum_ereal:
  fixes f :: "'i \<Rightarrow> nat \<Rightarrow> ereal"
  assumes nneg: "\<And>i x. i \<in> I \<Longrightarrow> 0 \<le> f i x"
  shows "(\<Sum>x. \<Sum>i\<in>I. f i x) = (\<Sum>i\<in>I. \<Sum>x. f i x)"
proof cases
  assume "finite I" from this nneg show ?thesis
  proof (induct I)
    case (insert i I) then show ?case
      using nneg by (simp add: suminf_add_ereal setsum_nonneg)
  qed simp
qed simp

lemma (in prob_space) weighted_prob_space:
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M \<lparr> measure := m i \<rparr>)" (is "\<And>i. _ \<Longrightarrow> prob_space (?m i)")
  assumes w: "(\<Sum>i\<in>I. w i) = 1" "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> w i"
  shows "prob_space (M \<lparr> measure := \<lambda>X. \<Sum>i\<in>I. w i * m i X \<rparr>)" (is "prob_space ?M'")
proof -
  interpret M': sigma_algebra ?M' by simp default
  { fix i assume "i \<in> I"
    then interpret m: prob_space "?m i" by fact
    from m.empty_measure m.positive_measure m.ca m.measure_space_1
    have "m i {} = 0" "\<And>A. A \<in> sets M \<Longrightarrow> 0 \<le> m i A" "countably_additive M (m i)" "m i (space M) = 1"
      by (simp_all add: countably_additive_def) }
  note m = this

  show ?thesis
  proof
    from m w show "positive ?M' (measure ?M')"
      by (auto intro!: setsum_nonneg ereal_0_le_mult simp: positive_def)
    show "countably_additive ?M' (measure ?M')"
    proof (rule countably_additiveI, simp)
      fix A :: "nat \<Rightarrow> _" assume A: "range A \<subseteq> events" "disjoint_family A" "UNION UNIV A \<in> events"
      { fix i assume "i \<in> I"
        note m(3)[unfolded countably_additive_def, rule_format, OF `i \<in> I` A, symmetric] }
      then show "(\<Sum>n. \<Sum>i\<in>I. w i * m i (A n)) = (\<Sum>i\<in>I. w i * m i (\<Union>x. A x))"
        apply (simp add: countably_additive_def subset_eq)
        apply (subst suminf_setsum_ereal)
        using m w A
        apply (auto intro!: setsum_nonneg ereal_0_le_mult setsum_cong suminf_cmult_ereal simp: subset_eq)
        done
    qed
    show "measure ?M' (space ?M') = 1"
      using m w by simp
  qed
qed

lemma prob_space_unique_Int_stable':
  assumes X: "X \<in> sets (sigma G)"
  assumes stable: "\<And>A B. A \<in> sets G \<Longrightarrow> B \<in> sets G \<Longrightarrow> A \<inter> B \<noteq> {} \<Longrightarrow> A \<inter> B \<in> sets G"
  assumes M: "prob_space M" "space M = space G" "sets M = sets (sigma G)"
  assumes N: "prob_space (M\<lparr>measure := m\<rparr>)"
  assumes " \<And>X. X \<in> sets G \<Longrightarrow> finite_measure.\<mu>' M X = m X"
  shows "finite_measure.\<mu>' M X = m X"
proof -
  interpret M: prob_space M by fact
  interpret N: prob_space "M\<lparr> measure := m \<rparr>" by fact
  let ?G = "\<lparr> space = space G, sets = insert {} (insert (space G) (sets G)) \<rparr>"

  have [simp]: "sets (sigma ?G) = sets (sigma G)"
  proof
    show "sets (sigma G) \<subseteq> sets (sigma ?G)"
      by (auto simp add: sets_sigma intro!: sigma_sets_mono sigma_sets.Basic)
    show "sets (sigma ?G) \<subseteq> sets (sigma G)"
    proof (simp add: sets_sigma, safe)
      fix A assume "A \<in> sigma_sets (space G) (insert {} (insert (space G) (sets G)))"
      then show "A \<in> sigma_sets (space G) (sets G)"
        by induct (auto intro: sigma_sets.intros sigma_sets_top)
    qed
  qed

  have [simp]: "m {} = 0" "m (space G) = 1"  "M.prob (space G) = 1"
    using N.empty_measure N.prob_space M.prob_space
    unfolding `space M = space G`[symmetric]
    by (simp_all add: N.\<mu>'_def)

  have [simp]: "space G \<in> sets (sigma G)"
    by (auto simp: sets_sigma intro: sigma_sets_top)

  { fix A assume "A \<in> sets G"
    then have "A \<in> sets M"
      by (auto simp: assms)
    then have "A \<subseteq> space G"
      using M.sets_into_space
      by (auto simp: assms) }
  with stable have "Int_stable ?G"
    by (simp add: Int_stable_def Int_absorb2 Int_absorb1) blast
  then have "M.\<mu>' X = finite_measure.\<mu>' (M \<lparr> measure := m\<rparr>) X"
    by (rule prob_space_unique_Int_stable)
       (auto simp add: assms N.\<mu>'_def M.prob_space)
  with X `sets M = sets (sigma G)`[symmetric] show ?thesis
    by (simp add: N.\<mu>'_def)
qed

lemma (in measure_space) measure_mono_AE:
  assumes imp: "AE x. x \<in> A \<longrightarrow> x \<in> B"
    and A: "A \<in> sets M" and B: "B \<in> sets M"
  shows "\<mu> A \<le> \<mu> B"
proof -
  from imp obtain N where N: "{x\<in>space M. \<not> (x \<in> A \<longrightarrow> x \<in> B)} \<subseteq> N" "N \<in> null_sets"
    by (auto simp: almost_everywhere_def)
  have "\<mu> A = \<mu> (A - N)"
    using N A by (subst measure_Diff_null_set) auto
  also have "\<mu> (A - N) \<le> \<mu> (B - N)"
    using N A B sets_into_space by (auto intro!: measure_mono)
  also have "\<mu> (B - N) = \<mu> B"
    using N B by (subst measure_Diff_null_set) auto
  finally show ?thesis .
qed

lemma (in measure_space) measure_eq_AE:
  assumes iff: "AE x. x \<in> A \<longleftrightarrow> x \<in> B"
  assumes A: "A \<in> sets M" and B: "B \<in> sets M"
  shows "\<mu> A = \<mu> B"
  using assms by (safe intro!: antisym measure_mono_AE elim!: AE_mp) auto

lemma (in finite_measure) finite_measure_mono_AE:
  assumes imp: "AE x. x \<in> A \<longrightarrow> x \<in> B" and B: "B \<in> sets M"
  shows "\<mu>' A \<le> \<mu>' B"
proof cases
  assume "A \<in> sets M"
  with assms measure_mono_AE[OF imp this B]
  show ?thesis by (simp add: finite_measure_eq)
next
  assume "A \<notin> sets M"
  then have "\<mu>' A = 0" unfolding \<mu>'_def by simp
  then show ?thesis by simp
qed

lemma (in finite_measure) finite_measure_eq_AE:
  assumes iff: "AE x. x \<in> A \<longleftrightarrow> x \<in> B"
  assumes A: "A \<in> sets M" and B: "B \<in> sets M"
  shows "\<mu>' A = \<mu>' B"
  using assms measure_eq_AE[OF assms] by (simp add: finite_measure_eq)

lemma all_less_Suc_split: "\<And>n P. (\<forall>i<Suc n. P i) \<longleftrightarrow> (\<forall>i<n. P (Suc i)) \<and> P 0"
  by (metis less_Suc_eq_0_disj)

lemma nat_case_idem: "nat_case (f 0) (\<lambda>i. f (Suc i)) = f"
  by (auto split: nat.split)

lemma setsum_strict_mono_single: 
  fixes f :: "_ \<Rightarrow> (_ :: ordered_cancel_ab_semigroup_add)"
  assumes "finite A" "a \<in> A" "f a < g a" "\<And>a. a \<in> A \<Longrightarrow> f a \<le> g a"
  shows "setsum f A < setsum g A"
proof -
  have "setsum f A = f a + setsum f (A - {a})"
    using `finite A` `a \<in> A` by (rule setsum_diff1')
  also have "\<dots> < g a + setsum g (A - {a})"
    using assms by (intro add_less_le_mono setsum_mono) auto
  also have "\<dots> = setsum g A"
    using `finite A` `a \<in> A` by (rule setsum_diff1'[symmetric])
  finally show ?thesis .
qed

lemma ereal_setsum_nonneg: 
  fixes f :: "_ \<Rightarrow> ereal" assumes nonneg: "\<And>a. a \<in> A \<Longrightarrow> 0 \<le> f a" shows "0 \<le> setsum f A"
proof cases
  assume "finite A" from this nonneg show ?thesis
    by (induct A) (auto intro!: ereal_add_nonneg_nonneg)
qed simp

lemma incseq_setsumI_le:
  fixes f :: "nat \<Rightarrow> 'a::{comm_monoid_add, ordered_ab_semigroup_add}"
  assumes "\<And>i. 0 \<le> f i"
  shows "incseq (\<lambda>i. setsum f {.. i})"
proof (intro incseq_SucI)
  fix n have "setsum f {.. n} + 0 \<le> setsum f {..n} + f (Suc n)"
    using assms by (rule add_left_mono)
  then show "setsum f {.. n} \<le> setsum f {.. Suc n}"
    by (auto simp: atMost_Suc ac_simps)
qed

lemma incseq_cmult_ereal:
  fixes f :: "nat \<Rightarrow> ereal"
  shows "incseq f \<Longrightarrow> 0 \<le> c \<Longrightarrow> incseq (\<lambda>i. c * f i)"
  by (auto simp: incseq_def intro!: ereal_mult_left_mono)

lemma incseq_fun:
  "incseq F \<longleftrightarrow> (\<forall>x. incseq (\<lambda>i. F i x))"
  by (auto simp: incseq_def le_fun_def)

lemma incseq_comp:
  "incseq F \<Longrightarrow> incseq (\<lambda>i. F i \<circ> f)"
  by (auto simp: incseq_def le_fun_def)

lemma (in measure_space) incseq_simple_integral:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  shows "incseq f \<Longrightarrow> (\<And>i. simple_function M (f i)) \<Longrightarrow> (\<And>i x. 0 \<le> f i x) \<Longrightarrow> incseq (\<lambda>i. integral\<^isup>S M (f i))"
  unfolding incseq_fun by (auto simp: incseq_def intro!: simple_integral_mono)

lemma sums_nonneg_eq_0_iff:
  fixes f :: "nat \<Rightarrow> real" and x :: real
  assumes f: "f sums x" "\<And>n. 0 \<le> f n"
  shows "x = 0 \<longleftrightarrow> (\<forall>n. f n = 0)"
proof
  assume "\<forall>n. f n = 0"
  then have "f = (\<lambda>n. 0)" by auto
  with sums_unique[OF `f sums x`]
  show "x = 0" by simp
next
  assume "x = 0"
  with assms have "f sums 0" by simp
  show "\<forall>n. f n = 0"
  proof
    fix n
    from f `x = 0` have "(\<Sum>i\<le>n. f i) \<le> 0"
      by (intro incseq_le) (auto intro!: incseq_setsumI_le simp: sums_def2)
    moreover have "0 \<le> (\<Sum>i\<le>n. f i)"
      using f by (auto intro!: setsum_nonneg)
    ultimately have "(\<Sum>i\<le>n. f i) = 0"
      by auto
    with f show "f n = 0"
      by (simp add: setsum_nonneg_eq_0_iff)
  qed
qed

lemma nat_case_in_S[intro, simp]: "s \<in> S \<Longrightarrow> \<omega> \<in> UNIV \<rightarrow> S \<Longrightarrow> nat_case s \<omega> i \<in> S"
  by (auto simp: Pi_mem split: nat.split)

lemma nat_case_in_space: "s \<in> S \<Longrightarrow> \<omega> \<in> UNIV \<rightarrow> S \<Longrightarrow> nat_case s \<omega> \<in> UNIV \<rightarrow> S"
  by auto

lemma (in sigma_algebra) simple_function_comp2: 
  fixes g :: "_ \<Rightarrow> _::t2_space"
  assumes "sigma_algebra M'"
  assumes f: "f \<in> measurable M M'"
    and g: "simple_function M' g"
  shows "simple_function M (g \<circ> f)"
proof (rule simple_function_borel_measurable)
  interpret M': sigma_algebra M' by fact
  note borel = M'.borel_measurable_simple_function[OF g]
  show "g \<circ> f \<in> borel_measurable M"
    using f borel by (rule measurable_comp)
  from f have "(g\<circ>f) ` space M \<subseteq> g ` space M'"
    unfolding measurable_def by auto
  from this M'.simple_functionD(1)[OF g] show "finite ((g \<circ> f) ` space M)"
    by (rule finite_subset)
qed

lemma (in sigma_algebra) simple_function_comp2':
  fixes g :: "_ \<Rightarrow> _::t2_space"
  shows "sigma_algebra M' \<Longrightarrow> f \<in> measurable M M' \<Longrightarrow> simple_function M' g \<Longrightarrow> simple_function M (\<lambda>x. g (f x))"
  using simple_function_comp2 by (simp add: comp_def)
 
lemma Collect_Int: "Collect P \<inter> A = {x\<in>A. P x}"
  by auto

lemma (in sigma_algebra) borel_measurable_setsum_dependent_index:
  fixes f :: "'a \<Rightarrow> nat" and g :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "\<And>i. f -` {i} \<inter> space M \<in> sets M"
  assumes "\<And>i. g i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Sum>i::nat<f x. g i x) \<in> borel_measurable M"
proof (unfold measurable_def, safe)
  fix A :: "real set" assume "A \<in> sets borel"
  moreover def X \<equiv> "\<lambda>i. (\<lambda>x. \<Sum>i::nat<i. g i x) -` A \<inter> space M"
  moreover note assms
  ultimately have "(\<lambda>x. \<Sum>i::nat<f x. g i x) -` A \<inter> space M = (\<Union>i. (f -` {i} \<inter> space M) \<inter> X i)" "\<And>i. X i \<in> sets M"
    by (auto intro!: measurable_sets[of _ M borel] borel_measurable_setsum)
  moreover then have "(\<Union>i. (f -` {i} \<inter> space M) \<inter> X i) \<in> sets M"
    using assms by blast
  ultimately show "(\<lambda>x. \<Sum>i::nat<f x. g i x) -` A \<inter> space M \<in> sets M" by simp
qed simp

lemma Max_atMost_nat[simp]: "Max {..n::nat} = n"
  by (rule Max_eqI) auto

lemma single_le_setsum:
  fixes f :: "_ \<Rightarrow> 'a::{ordered_ab_semigroup_add, comm_monoid_add}"
  shows "a \<in> A \<Longrightarrow> finite A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> 0 \<le> f a) \<Longrightarrow> f a \<le> setsum f A"
  using setsum_diff1'[of A a f] add_left_mono[OF setsum_nonneg, of "A - {a}" f]
  by auto

lemma smallest:
  fixes P :: "'a::wellorder \<Rightarrow> bool"
  assumes "P i"
  obtains j where "P j" "\<And>i. i < j \<Longrightarrow> \<not> P i" "j \<le> i"
proof -
  def j \<equiv> "LEAST j. P j"
  from `P i` have "P j \<and> (\<forall>i<j. \<not> P i)"
    unfolding j_def by (rule LeastI2_wellorder) auto
  moreover then have "j \<le> i"
    using `P i` by (auto simp: not_less[symmetric])
  ultimately show thesis using that by auto
qed

lemma Ex_nat_case_eq: "(\<exists>n. P n (nat_case s f n)) \<longleftrightarrow> P 0 s \<or> (\<exists>n. P (Suc n) (f n))"
  by (auto split: nat.split simp: gr0_conv_Suc)

lemma (in sigma_algebra) sets_Collect_in:
  assumes A: "A \<in> sets M" shows "{x\<in>space M. x \<in> A} \<in> sets M"
proof -
  have "{x\<in>space M. x \<in> A} = space M \<inter> A" by auto
  with A show ?thesis by auto
qed

lemma (in measure_space) AE_impI:
  "(P \<Longrightarrow> AE x. Q x) \<Longrightarrow> AE x. P \<longrightarrow> Q x"
  by (cases P) auto

lemma (in measure_space) AE_finite_allI:
  assumes "finite S"
  shows "(\<And>s. s \<in> S \<Longrightarrow> AE x. Q s x) \<Longrightarrow> AE x. \<forall>s\<in>S. Q s x"
  using AE_finite_all[OF `finite S`] by auto

lemma (in prob_space) AE_in_set_eq_1:
  assumes "A \<in> events" shows "(AE x. x \<in> A) \<longleftrightarrow> prob A = 1"
proof
  assume ae: "AE x. x \<in> A"
  have "{x \<in> space M. x \<in> A} = A" "{x \<in> space M. x \<notin> A} = space M - A"
    using `A \<in> events`[THEN sets_into_space] by auto
  with AE_E2[OF ae] `A \<in> events` have "1 - \<mu> A = 0"
    by (simp add: measure_compl measure_space_1)
  then show "prob A = 1"
    using `A \<in> events` by (simp add: finite_measure_eq one_ereal_def)
next
  assume prob: "prob A = 1"
  show "AE x. x \<in> A"
  proof (rule AE_I)
    show "{x \<in> space M. x \<notin> A} \<subseteq> space M - A" by auto
    show "\<mu> (space M - A) = 0"
      using `A \<in> events` prob
      by (simp add: measure_compl measure_space_1 finite_measure_eq one_ereal_def)
    show "space M - A \<in> events"
      using `A \<in> events` by auto
  qed
qed

lemma (in prob_space) AE_prob_1:
  assumes "prob A = 1" shows "AE x. x \<in> A"
proof -
  from `prob A = 1` have "A \<in> events"
    unfolding \<mu>'_def by (auto split: split_if_asm)
  with AE_in_set_eq_1 assms show ?thesis by simp
qed

lemma setsum_ereal_1: "setsum (\<lambda>_. 1) A = ereal (of_nat (card A))"
  unfolding one_ereal_def setsum_ereal by simp

lemma sums_ereal_If_finite:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes finite: "finite {r. P r}"
  shows "(\<lambda>r. if P r then f r else 0) sums (\<Sum>r\<in>{r. P r}. f r)" (is "?F sums _")
proof cases
  assume "{r. P r} = {}" hence "\<And>r. \<not> P r" by auto
  thus ?thesis by (simp add: sums_zero)
next
  assume not_empty: "{r. P r} \<noteq> {}"
  have "?F sums (\<Sum>r = 0..< Suc (Max {r. P r}). ?F r)"
    by (rule series_zero)
       (auto simp add: Max_less_iff[OF finite not_empty] less_eq_Suc_le[symmetric])
  also have "(\<Sum>r = 0..< Suc (Max {r. P r}). ?F r) = (\<Sum>r\<in>{r. P r}. f r)"
    by (subst setsum_cases)
       (auto intro!: setsum_cong simp: Max_ge_iff[OF finite not_empty] less_Suc_eq_le)
  finally show ?thesis .
qed

lemma (in measure_space) positive_integral_nat_function:
  assumes "(of_nat \<circ> f :: 'a \<Rightarrow> real) \<in> borel_measurable M"
  shows "(\<integral>\<^isup>+x. ereal (of_nat (f x)) \<partial>M) =
    (\<Sum>t. \<mu> ((of_nat \<circ> f) -` {of_nat t::real <..} \<inter> space M))"
proof -
  def F \<equiv> "\<lambda>i. (of_nat \<circ> f) -` {of_nat i::real <..} \<inter> space M"
  with assms have [simp, intro]: "\<And>i. F i \<in> sets M"
    by (auto intro: measurable_sets)

  { fix x assume "x \<in> space M"
    have "(\<lambda>i. if i < f x then 1 else 0) sums (of_nat (f x)::real)"
      using sums_If_finite[of "\<lambda>i. i < f x" "\<lambda>_. 1::real"] by simp
    then have "(\<lambda>i. ereal(if i < f x then 1 else 0)) sums (ereal(of_nat(f x)))"
      unfolding sums_ereal .
    moreover have "\<And>i. ereal (if i < f x then 1 else 0) = indicator (F i) x"
      using `x \<in> space M` by (simp add: one_ereal_def F_def)
    ultimately have "ereal(of_nat(f x)) = (\<Sum>i. indicator (F i) x)"
      by (simp add: sums_iff) }
  then have "(\<integral>\<^isup>+x. ereal (of_nat (f x)) \<partial>M) = (\<integral>\<^isup>+x. (\<Sum>i. indicator (F i) x) \<partial>M)"
    by (simp cong: positive_integral_cong)
  also have "\<dots> = (\<Sum>i. \<mu> (F i))"
    by (simp add: positive_integral_suminf)
  finally show ?thesis
    by (simp add: F_def)
qed

lemma path_inj:
  assumes \<omega>: "\<And>i. R (\<omega> i) (\<omega> (Suc i))"
  shows "\<exists>\<omega>' k. inj_on \<omega>' {.. k} \<and> (\<forall>i<k. R (\<omega>' i) (\<omega>' (Suc i))) \<and> (\<omega>' ` {..< k} \<subseteq> \<omega> ` {..< n'}) \<and> \<omega>' 0 = \<omega> 0 \<and> \<omega>' k = \<omega> n'"
proof (induct n')
  case 0 with \<omega>[of 0] show ?case
    by (auto intro!: inj_onI exI[of _ \<omega>] exI[of _ 0])
next
  case (Suc n')
  then obtain \<omega>' k where \<omega>': "inj_on \<omega>' {.. k}" "\<forall>i<k. R (\<omega>' i) (\<omega>' (Suc i))" "\<omega>' ` {..< k} \<subseteq> \<omega> ` {..< n'}"
    "\<omega>' 0 = \<omega> 0" "\<omega>' k = \<omega> n'"
    by auto
  show ?case
  proof cases
    assume "\<exists>i\<le>k. \<omega>' i = \<omega> (Suc n')"
    then obtain i where "i \<le> k" "\<omega>' i = \<omega> (Suc n')" by auto
    show ?thesis
    proof (intro exI[of _ \<omega>'] exI[of _ i] conjI allI impI)
      have subset: "{..i} \<subseteq> {..k}" using `i \<le> k` by auto
      with \<omega>'(1) show "inj_on \<omega>' {..i}" by (rule subset_inj_on)
      from subset have "\<omega>' ` {..<i} \<subseteq> \<omega>' ` {..<k}" by auto
      also note \<omega>'(3)
      also have "\<omega> ` {..<n'} \<subseteq> \<omega> ` {..<Suc n'}" by auto
      finally show "\<omega>' ` {..<i} \<subseteq> \<omega> ` {..<Suc n'}" .
      fix j assume "j < i" with \<omega>'(2) `i \<le> k` show "R (\<omega>' j) (\<omega>' (Suc j))" by auto
    qed fact+
  next
    assume *: "\<not> (\<exists>i\<le>k. \<omega>' i = \<omega> (Suc n'))"
    let ?\<omega>' = "\<omega>'(Suc k := \<omega> (Suc n'))"
    show ?thesis
    proof (intro exI[of _ ?\<omega>'] exI[of _ "Suc k"] conjI allI impI)
      show "?\<omega>' 0 = \<omega> 0" using \<omega>' by simp
      show "?\<omega>' (Suc k) = \<omega> (Suc n')" by simp
      have "inj_on ?\<omega>' {..k} \<longleftrightarrow> inj_on \<omega>' {..k}"
        by (rule inj_on_cong) simp
      with \<omega>' * have "inj_on ?\<omega>' ({Suc k} \<union> {..k})"
        by (auto simp: inj_on_Un)
      then show "inj_on ?\<omega>' {..Suc k}"
        unfolding atMost_Suc by simp
      show "?\<omega>' ` {..<Suc k} \<subseteq> \<omega> ` {..<Suc n'}"
        using \<omega>' by (simp add: subset_eq lessThan_Suc)
      fix i assume "i < Suc k"
      with \<omega>' \<omega> show "R (?\<omega>' i) (?\<omega>' (Suc i))"
        by auto
    qed
  qed
qed

lemma (in prob_space) AE_False: "(AE x. False) \<longleftrightarrow> False"
proof
  assume "AE x. False"
  then have "AE x. x \<in> {}" by simp
  then show False
    by (subst (asm) AE_in_set_eq_1) auto
qed simp

lemma sums_shift:
  fixes f :: "nat \<Rightarrow> real"
  shows "summable (\<lambda>i. f (i + k)) \<Longrightarrow> summable f"
proof (induct k)
  case (Suc k)
  then have "(\<lambda>i. f (Suc i + k)) sums (\<Sum>i. f (Suc (i + k)))"
    by (simp add: summable_sums)
  from sums_Suc[OF this]
  have "summable (\<lambda>i. f (i + k))" by (simp add: sums_iff)
  then show ?case by (rule Suc)
qed simp

lemma sums_0_iff:
  fixes f :: "nat \<Rightarrow> real"
  assumes "\<And>i. 0 \<le> f i"
  shows "f sums 0 \<longleftrightarrow> (\<forall>i. f i = 0)"
proof safe
  fix i assume "f sums 0"
  then have "f i \<le> 0"
    unfolding sums_def
    by (rule LIMSEQ_le_const)
       (auto intro!: exI[of _ "Suc i"] single_le_setsum assms)
  then show "f i = 0" using assms[of i] by simp
next
  assume "\<forall>i. f i = 0"
  then have "f = (\<lambda>_. 0)" by auto
  then show "f sums 0" by simp
qed

section {* Discrete-Time Markov Chain *}

text {*

@{term s} is an arbitrary state which should be in @{term Q}, however we do not
enforce this, this simplifies the usage of @{const prob_space} on DTMC.

*}

locale Discrete_Time_Markov_Chain =
  fixes S :: "'s set" and \<tau> :: "'s \<Rightarrow> 's \<Rightarrow> real" and s0 :: "'s"
  assumes finite_S[simp, intro]: "finite S"
    and s0: "s0 \<in> S"
    and \<tau>_nneg[simp, intro]: "\<And>s s'. s \<in> S \<Longrightarrow> s' \<in> S \<Longrightarrow> 0 \<le> \<tau> s s'"
    and \<tau>_distr: "\<And>s. s \<in> S \<Longrightarrow> (\<Sum>s'\<in>S. \<tau> s s') = 1"
begin

lemma S_not_empty: "S \<noteq> {}"
  using s0 by auto

lemma \<tau>_le_1:
  assumes [simp]: "s \<in> S" "s' \<in> S"
  shows "\<tau> s s' \<le> 1"
proof -
  have "\<tau> s s' \<le> (\<Sum>s'\<in>S. \<tau> s s')"
    by (rule single_le_setsum) auto
  then show ?thesis by (simp add: \<tau>_distr)
qed

lemma \<tau>_exists:
  assumes "s \<in> S" shows "\<exists>t\<in>S. \<tau> s t \<noteq> 0"
proof (rule ccontr)
  assume "\<not> (\<exists>t\<in>S. \<tau> s t \<noteq> 0)"
  with \<tau>_distr[of s] `s \<in> S`
  show False by auto
qed

subsection {* @{text order} and @{text select} *}

definition "order = (SOME f. bij_betw f {..< card S} S)"
definition "select s x = order (LEAST i. x < (\<Sum>j\<le>i. \<tau> s (order j)))"

lemma
  shows bij_order[simp]: "bij_betw order {..< card S} S"
    and inj_order[simp]: "inj_on order {..<card S}"
    and image_order[simp]: "order ` {..<card S} = S"
    and order_S[simp, intro]: "\<And>i. i < card S \<Longrightarrow> order i \<in> S"
proof -
  from finite_same_card_bij[OF _ finite_S] show "bij_betw order {..< card S} S"
    unfolding order_def by (rule someI_ex) auto
  then show "inj_on order {..<card S}" "order ` {..<card S} = S"
    unfolding bij_betw_def by auto
  then show "\<And>i. i < card S \<Longrightarrow> order i \<in> S"
    by auto
qed

lemma order_Ex:
  assumes "s \<in> S" obtains i where "i < card S" "s = order i"
proof -
  from `s \<in> S` have "s \<in> order ` {..<card S}"
    by simp
  with that show thesis
    by (auto simp del: image_order)
qed

lemma \<tau>_order_distr:
  "s \<in> S \<Longrightarrow> (\<Sum>j<card S. \<tau> s (order j)) = 1"
  using setsum_reindex[OF inj_order, of "\<tau> s"] \<tau>_distr by simp

lemma selectI:
  assumes "x < 1" "s \<in> S"
  assumes P: "\<And>i. \<lbrakk>x < (\<Sum>k\<le>i. \<tau> s (order k)); \<And>j. x < (\<Sum>k\<le>j. \<tau> s (order k)) \<Longrightarrow> i \<le> j ; i < card S \<rbrakk> \<Longrightarrow> P (order i)"
  shows "P (select s x)"
  unfolding select_def
proof (rule LeastI2_wellorder)
  have "{.. card S - 1} = {..< card S}"
    using finite_S `s \<in> S` by (cases "card S") auto
  with `x < 1` `s \<in> S` show *: "x < (\<Sum>j\<le>card S - 1. \<tau> s (order j))"
    by (simp add: \<tau>_order_distr)

  fix i assume "x < (\<Sum>k\<le>i. \<tau> s (order k))" "\<forall>j. x < (\<Sum>k\<le>j. \<tau> s (order k)) \<longrightarrow> i \<le> j"
  moreover with * have "i < card S"
    using finite_S `s \<in> S` by (cases "card S") auto
  ultimately show "P (order i)"
    using P by blast
qed

lemma select:
  assumes "0 \<le> x" "x < 1" "i < card S" "s \<in> S"
  shows "select s x = order i \<longleftrightarrow> (\<Sum>j<i. \<tau> s (order j)) \<le> x \<and> x < (\<Sum>j\<le>i. \<tau> s (order j))"
    (is "_ \<longleftrightarrow> ?sum i \<le> x \<and> x < ?sumeq i")
proof (rule selectI[OF `x < 1` `s \<in> S`])
  fix j assume "x < ?sumeq j" "j < card S" and least: "\<And>k. x < ?sumeq k \<Longrightarrow> j \<le> k"
  moreover
  with `i < card S` inj_order have "order j = order i \<longleftrightarrow> j = i"
    by (auto simp: inj_on_def)
  moreover have "?sum j \<le> x"
    using least[of "j - 1"] `0 \<le> x`
    by (cases j) (auto simp add: lessThan_Suc_atMost not_less[symmetric])
  moreover {
    assume *: "?sum i \<le> x \<and> x < ?sumeq i"
    have "j \<le> i"
      using * least by simp
    moreover {
      assume "j < i"
      with order_S `i < card S` `s \<in> S` have "?sumeq j \<le> ?sum i"
        by (auto simp: set_eq_iff intro!: \<tau>_nneg setsum_mono2)
      with `x < ?sumeq j` * have False by auto }
    ultimately have "i = j" by (metis antisym leI) }
  ultimately show "order j = order i \<longleftrightarrow> ?sum i \<le> x \<and> x < ?sumeq i"
    by auto
qed

lemma select_S:
  assumes *: "x < 1" "s \<in> S" shows "select s x \<in> S"
  by (rule selectI[OF *]) (rule order_S)

lemma \<tau>_sum_le_1:
  assumes "i < card S" "s \<in> S"
  shows "(\<Sum>j\<le>i. \<tau> s (order j)) \<le> 1"
  using `i < card S` `s \<in> S` order_S
  by (subst \<tau>_order_distr[symmetric, OF `s \<in> S`])
     (auto simp: set_eq_iff intro!: \<tau>_nneg setsum_mono2)

lemma select_vimage_singleton:
  assumes "i < card S" "s \<in> S"
  shows "select s -` {order i} \<inter> {0..<1} = {(\<Sum>j<i. \<tau> s (order j)) ..< (\<Sum>j\<le>i. \<tau> s (order j))}"
    (is "_ = ?I")
proof safe
  fix x assume "x \<in> {0..<1}" "select s x = order i"
  with select[OF _ _ assms, of x] show "x \<in> ?I" by auto
next
  fix x assume "x \<in> ?I"
  moreover
  have "0 \<le> (\<Sum>j<i. \<tau> s (order j))"
    using `i < card S` `s \<in> S`
    by (auto intro!: setsum_nonneg \<tau>_nneg order_S)
  ultimately show "x \<in> {0..< 1}"
    using `s \<in> S` \<tau>_sum_le_1[OF assms] by auto
  with `x \<in> ?I` show "x \<in> select s -` {order i}"
    using select[of x i s] `i < card S` `s \<in> S` by auto
qed

lemma select_sets:
  assumes [intro]: "s \<in> S"
  shows "select s -` X \<inter> {0..<1} \<in> sets pborel"
proof -
  have "select s -` X \<inter> {0..<1} = (\<Union>s'\<in>X \<inter> S. select s -` {s'} \<inter> {0..<1})"
    by (auto intro!: select_S)
  also have "\<dots> \<in> sets pborel"
  proof (rule pborel.finite_UN)
    show "finite (X \<inter> S)" using finite_S by auto
    fix s' assume "s' \<in> X \<inter> S"
    then obtain i where "s' = order i" "i < card S"
      using image_order[symmetric] by (auto simp del: image_order simp: set_eq_iff)
    moreover have "0 \<le> (\<Sum>j<i. \<tau> s (order j))"
      using `i < card S` by (auto intro!: setsum_nonneg \<tau>_nneg order_S)
    ultimately show "select s -` {s'} \<inter> {0..<1} \<in> sets pborel" 
      using `s \<in> S` `i < card S`
      by (auto simp: sets_pborel select_vimage_singleton \<tau>_sum_le_1)
  qed
  finally show ?thesis .
qed

lemma select_measurable:
  "s \<in> S \<Longrightarrow> select s \<in> measurable pborel \<lparr> space = UNIV, sets = UNIV \<rparr>"
  unfolding measurable_def
  by (auto intro: select_sets select_S)

subsection {* @{text path} *}

primrec path :: "'s \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> 's)" where
  "path s X 0 = select s (X 0)"
| "path s X (Suc n) = select (path s X n) (X (Suc n))"

lemma path_eq:
  "path s X n = select (case n of 0 \<Rightarrow> s | Suc n \<Rightarrow> path s X n) (X n)"
  by (cases n) simp_all

lemma path_S[intro, simp]:
  "X \<in> UNIV \<rightarrow> {0 ..< 1} \<Longrightarrow> s \<in> S \<Longrightarrow> path s X n \<in> S"
  using assms by (induct n) (auto intro!: select_S)

definition path_space_gen :: "'s \<Rightarrow> (nat \<Rightarrow> 's) measure_space" where
  "path_space_gen s =  \<lparr> space = UNIV \<rightarrow> S,
    sets = range (\<lambda>(X, n). {X' \<in> UNIV \<rightarrow> S. \<forall>i\<le>n. X' i = X i}),
    measure = \<lambda>A. measure (\<Pi>\<^isub>P i\<in>UNIV. pborel) (path s -` A \<inter> space (\<Pi>\<^isub>P i\<in>UNIV. pborel)) \<rparr>"

lemma path_space_genE:
  assumes "A \<in> sets (path_space_gen s)"
  obtains X n where "A = {X' \<in> UNIV \<rightarrow> S. \<forall>i\<le>n. X' i = X i}"
  using assms unfolding path_space_gen_def by auto

definition "path_space s =
  (if s \<in> S then sigma (path_space_gen s)
            else sigma (path_space_gen s0))"

end

sublocale Discrete_Time_Markov_Chain \<subseteq> sigma_algebra "path_space s" for s
  using s0
  by (auto intro!: sigma_algebra_sigma simp: path_space_gen_def path_space_def)

context Discrete_Time_Markov_Chain
begin

lemma space_path_space: "space (path_space s) = UNIV \<rightarrow> S"
  by (auto simp: path_space_def path_space_gen_def)

lemma paths_in_path_space[intro, simp]:
  "(UNIV \<rightarrow> S) \<in> sets (path_space s)"
  using top[of s] by (simp add: space_path_space)

lemma in_path_space: "{X' \<in> UNIV \<rightarrow> S. \<forall>i\<le>n. X' i = X i} \<in> sets (path_space s)"
  by (auto simp: path_space_def path_space_gen_def
           intro!: in_sigma image_eqI[of _ _ "(X, n)"])

lemma in_path_space': "{X' \<in> UNIV \<rightarrow> S. \<forall>i<n. X' i = X i} \<in> sets (path_space s)"
  using top[of s]
  by (cases n) (auto simp add: space_path_space less_Suc_eq_le in_path_space)

lemma in_path_space_le_in[intro, simp]:
 "{X'\<in>UNIV\<rightarrow>S. \<forall>i\<le>n. X' i \<in> Y i} \<in> sets (path_space s)"
proof -
  have "{X'\<in>UNIV\<rightarrow>S. \<forall>i\<le>n. X' i \<in> Y i} =
    (\<Union>X\<in>(\<Pi>\<^isub>E j\<in>{..n}. Y j \<inter> S). {X'\<in>UNIV\<rightarrow>S. \<forall>i\<le>n. X' i = X i})"
    apply auto
    apply (rule_tac x="restrict x {..n}" in bexI)
    apply auto
    done
  also have "\<dots> \<in> sets (path_space s)"
    by (auto intro: in_path_space)
  finally show ?thesis .
qed

lemma in_path_space_in[intro, simp]:
  "{X'\<in>UNIV\<rightarrow>S. \<forall>i\<in>I. X' i \<in> X i} \<in> sets (path_space s)"
proof -
  have "{X'\<in>UNIV\<rightarrow>S. \<forall>i\<in>I. X' i \<in> X i} =
    (\<Inter>n. {X'\<in>UNIV\<rightarrow>S. \<forall>i\<le>n. X' i \<in> (if i \<in> I then X i else S)})" by auto
  then show ?thesis
    by (auto split del: split_if)
qed

lemma in_path_space_in_single[simp, intro]:
  "{X' \<in> UNIV \<rightarrow> S. X' i \<in> A} \<in> sets (path_space s)"
  using in_path_space_in[of "{i}" "\<lambda>i. A"] by simp

lemma in_path_space_single[simp, intro]:
  "{X' \<in> UNIV \<rightarrow> S. X' i = s'} \<in> sets (path_space s)"
  using in_path_space_in[of "{i}" "\<lambda>i. {s'}"] by simp

lemma measurable_path:
  "(if s \<in> S then path s else path s0) \<in> measurable (\<Pi>\<^isub>P i\<in>UNIV. pborel) (path_space s)"
proof -
  { fix s assume "s \<in> S"
    have "path s \<in> measurable (\<Pi>\<^isub>P i\<in>UNIV. pborel) (sigma (path_space_gen s))"
    proof (rule pborel_sequence.measurable_sigma)
      show "sets (path_space_gen s) \<subseteq> Pow (space (path_space_gen s))"
        by (auto simp: path_space_gen_def)
      show "path s \<in> space (\<Pi>\<^isub>P i\<in>UNIV. pborel) \<rightarrow> space (path_space_gen s)"
        using `s \<in> S` by (auto simp: path_space_gen_def)
      fix A assume "A \<in> sets (path_space_gen s)"
      from path_space_genE[OF this] guess X n .
      moreover
      then have "path s -` A \<inter> space (\<Pi>\<^isub>P i\<in>UNIV. pborel) = 
        (\<Inter>i\<le>n. {X'\<in>space (\<Pi>\<^isub>P i\<in>UNIV. pborel). path s X' i = X i})"
        using `s \<in> S` by (auto intro!: path_S)
      moreover
      { fix n :: nat and i x
        assume "i \<in> S"
        with measurable_comp[OF pborel_sequence.measurable_component[of n] select_measurable[OF `i \<in> S`],
          THEN measurable_sets, of "{x}"]
        have "{X' \<in> space (\<Pi>\<^isub>P i\<in>UNIV. pborel). select i (X' n) = x} \<in> sets (\<Pi>\<^isub>P i\<in>UNIV. pborel)"
          by (simp add: vimage_def Int_def conj_commute del: space_pborel_sequence) }
      note select_component = this
      { fix x i
        from `s \<in> S` have "{X'\<in>space (\<Pi>\<^isub>P i\<in>UNIV. pborel). path s X' i = x} \<in> sets (\<Pi>\<^isub>P i\<in>UNIV. pborel)"
        proof (induct i arbitrary: x s)
          case (Suc n)
          then have "{X'\<in>space (\<Pi>\<^isub>P i\<in>UNIV. pborel). path s X' (Suc n) = x} =
              {X'\<in>space (\<Pi>\<^isub>P i\<in>UNIV. pborel). \<forall>s'\<in>S. path s X' n = s' \<longrightarrow> select s' (X' (Suc n)) = x}"
            by auto
          also have "\<dots> \<in> sets (\<Pi>\<^isub>P i\<in>UNIV. pborel)"
            using finite_S s0
            by (intro pborel_sequence.sets_Collect_finite_All pborel_sequence.sets_Collect Suc select_component) auto
          finally show ?case .
        qed (insert select_component, simp) }
      ultimately show "path s -` A \<inter> space (\<Pi>\<^isub>P i\<in>UNIV. pborel) \<in> sets (\<Pi>\<^isub>P i\<in>UNIV. pborel)"
        by (auto intro!: sets_Collect_finite_All)
    qed }
  with s0 show ?thesis
    by (simp add: path_space_def)
qed

lemma measurable_at_single[intro]:
  fixes f :: "'s \<Rightarrow> real"
  shows "(\<lambda>\<omega>. f (\<omega> i)) \<in> borel_measurable (path_space s)"
proof (unfold measurable_def space_path_space, safe)
  fix i :: nat and A :: "real set" assume "A \<in> sets borel"
  have "(\<lambda>\<omega>. f (\<omega> i)) -` A \<inter> (UNIV \<rightarrow> S) = {\<omega>\<in>UNIV\<rightarrow>S. \<forall>i\<in>{i}. \<omega> i \<in> f -` A}"
    by auto
  also have "\<dots> \<in> sets (path_space s)"
    by (rule in_path_space_in)
  finally show "(\<lambda>\<omega>. f (\<omega> i)) -` A \<inter> (UNIV \<rightarrow> S) \<in> sets (path_space s)" .
qed simp

lemma measurable_shift:
  "(\<lambda>\<omega> i. \<omega> (i + n)) \<in> measurable (path_space s) (path_space s')"
proof -
  { fix s s' assume "s' \<in> S"
    have "(\<lambda>\<omega> i. \<omega> (i + n)) \<in> measurable (path_space s) (sigma (path_space_gen s'))"
    proof (rule measurable_sigma)
      show "sets (path_space_gen s') \<subseteq> Pow (space (path_space_gen s'))"
        by (auto simp: path_space_gen_def)
      show "(\<lambda>\<omega> i. \<omega> (i + n)) \<in> space (path_space s) \<rightarrow> space (path_space_gen s')"
        by (auto simp: path_space_gen_def space_path_space)
      
      fix A assume "A \<in> sets (path_space_gen s')"
      from path_space_genE[OF this] guess \<omega>' :: "nat \<Rightarrow> 's" and k .
      then have "(\<lambda>\<omega> i. \<omega> (i + n)) -` A \<inter> space (path_space s) =
        {\<omega>\<in>UNIV\<rightarrow>S. \<forall>i\<in>{n .. n + k}. \<omega> i = \<omega>' (i - n)}"
        apply (auto simp: space_path_space)
        apply (erule_tac x="i - n" in allE)
        apply simp
        done
      then show "(\<lambda>\<omega> i. \<omega> (i + n)) -` A \<inter> space (path_space s) \<in> sets (path_space s)"
        using in_path_space_in[of "{n .. n+k}" "\<lambda>i. {\<omega>' (i - n)}" s]
        by (auto intro: in_path_space_in)
    qed }
  then show ?thesis
    using s0 by (auto simp: path_space_def)
qed

lemma nat_case_cylinder: 
  "s \<in> S \<Longrightarrow> nat_case s -` {X'\<in>UNIV \<rightarrow> S. \<forall>i\<le>n. X' i = X i} \<inter> (UNIV \<rightarrow> S) =
    (if X 0 = s then case n of 0 \<Rightarrow> UNIV \<rightarrow> S
                             | Suc n \<Rightarrow> {X'\<in>UNIV \<rightarrow> S. \<forall>i\<le>n. X' i = X (Suc i)} else {})"
  by (auto split: nat.split simp: Pi_def)

lemma measurable_nat_case:
  assumes "s' \<in> S" shows "nat_case s' \<in> measurable (path_space s') (path_space s)"
proof -
  { fix s assume "s \<in> S"
    have "nat_case s' \<in> measurable (path_space s') (path_space s)"
    proof (subst (2) path_space_def, simp add: `s \<in> S`, rule measurable_sigma)
      show "sets (path_space_gen s) \<subseteq> Pow (space (path_space_gen s))"
        by (auto simp add: path_space_gen_def)
      show "nat_case s' \<in> space (path_space s') \<rightarrow> space (path_space_gen s)"
        using `s' \<in> S` by (auto simp add: path_space_def path_space_gen_def Pi_def split: nat.split)
      fix A assume "A \<in> sets (path_space_gen s)"
      from path_space_genE[OF this] guess X n . note A = this
      show "nat_case s' -` A \<inter> space (path_space s') \<in> sets (path_space s')"
        using top[of s']
        unfolding A space_path_space nat_case_cylinder[OF `s' \<in> S`]
        by (simp add: in_path_space split: nat.split)
    qed }
  from this[of s] this[OF s0]
  show ?thesis unfolding path_space_def by auto
qed

subsection {* @{const path_space} is a probability space *}

end

sublocale Discrete_Time_Markov_Chain \<subseteq> prob_space "path_space s" for s
proof (rule pborel_sequence.P.prob_space_vimage)
  show "sigma_algebra (path_space s)" ..
  show "(if s \<in> S then path s else path s0) \<in> measure_preserving (\<Pi>\<^isub>P i\<in>UNIV. pborel) (path_space s)"
    using s0 measurable_path[of s]
    by (simp add: path_space_def path_space_gen_def measure_preserving_def)
qed

context Discrete_Time_Markov_Chain
begin

lemma path_space_1[simp]:
  "prob s (UNIV \<rightarrow> S) = 1"
  using prob_space unfolding space_path_space .

lemma finite_measure_path_space:
  assumes "s \<in> S" "X \<in> sets (path_space s)"
  shows "\<mu>' s X = pborel_sequence.\<mu>' (path s -` X \<inter> space (\<Pi>\<^isub>P i\<in>UNIV. pborel))"
proof -
  have path: "path s \<in> measurable (\<Pi>\<^isub>P i\<in>UNIV. pborel) (path_space s)"
    using `s \<in> S` measurable_path[of s] by auto
  have "path s -` X \<inter> (UNIV \<rightarrow> {0..<1}) \<in> sets (\<Pi>\<^isub>P i\<in>UNIV. pborel)"
    using measurable_sets[OF path] `X \<in> sets (path_space s)` by auto
  with assms show ?thesis
    unfolding \<mu>'_def pborel_sequence.\<mu>'_def
    by auto (simp add: path_space_def path_space_gen_def)
qed

lemma prob_generator:
  assumes s: "\<And>i. i < n \<Longrightarrow> s i \<in> S" "s' \<in> S"
  shows "\<mu>' s' {s'\<in>UNIV \<rightarrow> S. \<forall>i<n. s' i = s i} = (\<Prod>i<n. \<tau> (nat_case s' s i) (s i))"
proof cases
  assume "n = 0" then show ?thesis
    using prob_space by (simp add: space_path_space)
next
  assume "n \<noteq> 0"
  let ?s' = "nat_case s' s"
  { fix j assume "j < n"
    with s have s'[intro, simp]: "?s' j \<in> S"
      by (auto split: nat.split)
    from s(1)[OF `j < n`] obtain k where "s j = order k" "k < card S"
      by (auto elim: order_Ex)
    moreover
    { then have "(\<Sum>i\<le>k. \<tau> (?s' j) (order i)) \<le> (\<Sum>i<card S. \<tau> (?s' j) (order i))"
        by (intro setsum_mono2 \<tau>_nneg order_S) auto
      then have "(\<Sum>i\<le>k. \<tau> (?s' j) (order i)) \<le> 1"
        using \<tau>_order_distr by auto }
    ultimately
    have "pborel.\<mu>' (select (?s' j) -` {s j} \<inter> {0..<1}) = \<tau> (?s' j) (s j)"
      using s `j < n` `?s' j \<in> S`
      by (simp_all add: lessThan_Suc_atMost[symmetric] setsum_nonneg select_vimage_singleton) }
  note measure_select = this
  have "\<And>x. (\<forall>i<n. s i = path s' x i) \<longleftrightarrow> (\<forall>i<n. select (?s' i) (x i) = s i)"
  proof safe
    fix x i assume "\<forall>i<n. s i = path s' x i" "i < n"
    then show "select (nat_case s' s i) (x i) = s i"
      by (induct i) auto
  next
    fix x i assume "\<forall>i<n. select (?s' i) (x i) = s i" "i < n"
    then show "s i = path s' x i"
      by (induct i) auto
  qed
  with `s' \<in> S` have path: "path s' -` {s' \<in> UNIV \<rightarrow> S. \<forall>i<n. s' i = s i} \<inter> space (\<Pi>\<^isub>P i\<in>UNIV. pborel)
    = pborel_sequence.emb UNIV {..<n} (\<Pi>\<^isub>E i\<in>{..<n}. select (?s' i) -` {s i} \<inter> {0..<1})"
    by (auto simp: pborel_sequence.emb_def Pi_def extensional_def eq_commute)
  from s `n \<noteq> 0` show ?thesis
    unfolding finite_measure_path_space[OF `s' \<in> S` in_path_space'] path
    by (subst pborel_sequence.finite_measure_infprod_emb_Pi)
       (auto intro!: product_algebraI select_sets simp: measure_select split: nat.split)
qed 

lemma prob_generator_0:
  "s \<in> S \<Longrightarrow> s' \<in> S \<Longrightarrow> \<mu>' s' {s'\<in>UNIV \<rightarrow> S. s' 0 = s} = \<tau> s' s"
  using prob_generator[of "Suc 0" "\<lambda>_. s"]
  by (simp add: lessThan_Suc)

lemma prob_generator_le:
  "(\<And>i. i \<le> n \<Longrightarrow> s i \<in> S) \<Longrightarrow> s' \<in> S \<Longrightarrow>
    \<mu>' s' {s'\<in>UNIV \<rightarrow> S. \<forall>i\<le>n. s' i = s i} = (\<Prod>i\<le>n. \<tau> (nat_case s' s i) (s i))"
  using prob_generator[of "Suc n" s s']
  by (simp add: less_Suc_eq_le lessThan_Suc_atMost)

lemma AE_\<tau>_not_zero:
  assumes "s \<in> S"
  shows "AE \<omega> in path_space s. \<forall>i. \<tau> (nat_case s \<omega> i) (\<omega> i) \<noteq> 0"
proof (rule AE_I)
  let "?N k" = "{\<omega> \<in> space (path_space s). \<exists>i\<le>k. \<forall>t\<in>S. nat_case s \<omega> i = t \<longrightarrow> (\<exists>t'\<in>{t'\<in>S. \<tau> t t' = 0}. \<omega> i = t')}"
  show "{\<omega> \<in> space (path_space s). \<not> (\<forall>i. \<tau> (nat_case s \<omega> i) (\<omega> i) \<noteq> 0)} \<subseteq> (\<Union>i. ?N i)"
    (is "_ \<subseteq> ?allN")
    using `s \<in> S` by (force simp: space_path_space)

  have N: "\<And>i. ?N i \<in> events s"
    using S_not_empty
    apply (split nat.split)
    apply (intro sets_Collect_countable_Ex)
    apply (intro sets_Collect sets_Collect_finite_All sets_Collect_finite_Ex)
    apply (auto simp: space_path_space intro: in_path_space_single)
    done
  then show "?allN \<in> events s"
    by auto

  have "(SUP i. \<mu> s (?N i)) = \<mu> s ?allN"
  proof (rule continuity_from_below)
    show "range ?N \<subseteq> events s"
      using N by auto
    show "incseq ?N"
      using `s \<in> S` by (auto simp add: incseq_def space_path_space intro: order_trans)
  qed
  moreover
  { fix n
    have "?N n = (\<Union>\<omega>'\<in>(\<Pi>\<^isub>E i\<in>{..n}. S) \<inter> {\<omega>. \<exists>i\<le>n. \<tau> (nat_case s \<omega> i) (\<omega> i) = 0}. {\<omega>\<in>UNIV\<rightarrow>S. \<forall>i\<le>n. \<omega> i = \<omega>' i})"
       (is "_ = UNION ?I ?S")
      using `s \<in> S`
      apply (simp add: space_path_space Pi_iff set_eq_iff Bex_def)
      apply safe
      apply fastforce
      apply (rule_tac x="restrict x {..n}" in exI)
      apply simp
      apply (rule_tac x="i" in exI)
      apply (fastforce split: nat.split)
      apply (rule_tac x="i" in exI)
      apply (fastforce split: nat.split)
      done
    moreover have "(\<Sum>\<omega>\<in>?I. \<mu> s (?S \<omega>)) = \<mu> s (UNION ?I ?S)"
    proof (rule measure_setsum)
      show "finite ?I"
        by (auto intro: finite_PiE)
      show "disjoint_family_on ?S ?I"
      proof (unfold disjoint_family_on_def, intro ballI impI)
        fix \<omega>1 \<omega>2 :: "nat \<Rightarrow> 's" assume "\<omega>1 \<noteq> \<omega>2"
        then obtain i where i: "\<omega>1 i \<noteq> \<omega>2 i" by auto
        moreover assume "\<omega>1 \<in> ?I" "\<omega>2 \<in> ?I"
        ultimately have "i \<le> n" by (rule_tac ccontr) (auto simp: extensional_def)
        with i show "?S \<omega>1 \<inter> ?S \<omega>2 = {}" by auto
      qed
      show "\<And>\<omega>. ?S \<omega> \<in> events s"
        by (auto intro: in_path_space)
    qed
    moreover
    { fix \<omega> assume \<omega>: "\<omega> \<in> ?I"
      then have "\<mu> s (?S \<omega>) = ereal (prob s (?S \<omega>))"
        by (simp add: in_path_space finite_measure_eq)
      also have "\<dots> = ereal (\<Prod>i\<le>n. \<tau> (nat_case s \<omega> i) (\<omega> i))"
        using `s \<in> S` \<omega> by (subst prob_generator_le) auto
      also have "\<dots> = ereal 0"
        using \<omega> by (subst setprod_zero) auto
      finally have "\<mu> s (?S \<omega>) = 0" by simp }
    ultimately have "\<mu> s (?N n) = 0"
      by simp }
  ultimately show "\<mu> s ?allN = 0"
    by simp
qed

subsection {* Iterative equation for @{const \<mu>'} *}

lemma prob_eq_sum:
  assumes s: "s \<in> S" and X: "X \<in> sets (path_space s)"
  shows "\<mu>' s X = (\<Sum>s'\<in>S. \<tau> s s' * \<mu>' s' (nat_case s' -` X \<inter> (UNIV \<rightarrow> S)))"
proof (rule prob_space_unique_Int_stable')
  let ?G = "path_space_gen s"
  show "X \<in> sets (sigma ?G)"
    using s X unfolding path_space_def by simp
  { fix A B
    assume "A \<in> sets ?G"
    from path_space_genE[OF this] guess X n . note this[simp]
    assume "B \<in> sets ?G"
    from path_space_genE[OF this] guess Y m . note this[simp]
    assume "A \<inter> B \<noteq> {}"
    then have *: "\<And>i. i \<le> min n m \<Longrightarrow> X i = Y i"
      by auto
    then show "A \<inter> B \<in> sets ?G"
      by (auto simp: path_space_gen_def image_iff
               intro!:  exI[of _ "if m \<le> n then X else Y"] exI[of _ "max n m"]) }
  show "prob_space (path_space s)"
    by unfold_locales
  show "space (path_space s) = space (path_space_gen s)" "sets (path_space s) = sets (sigma (path_space_gen s))"
    using `s \<in> S` by (simp_all add: path_space_def)
  { fix X s' assume "s' \<in> S" "X \<in> sets (path_space s)"
    with `s \<in> S` have "s' \<in> S" "X \<in> sets (path_space s')"
      by (auto simp: path_space_def path_space_gen_def sets_sigma)
    then have "nat_case s' -` X \<inter> space (path_space s') \<in> sets (path_space s')"
      by (auto intro!: measurable_sets measurable_nat_case) }
  note nat_case_sets = this
  have space': "prob_space (path_space s\<lparr>measure := \<lambda>x. (\<Sum>s'\<in>S. \<tau> s s' * \<mu> s' (nat_case s' -` x \<inter> (UNIV \<rightarrow> S)))\<rparr>)"
  proof (rule weighted_prob_space, rule prob_space_vimage, simp)
    show "sigma_algebra (path_space s)" ..
    fix s' assume "s' \<in> S"
    then show "nat_case s' \<in> measure_preserving (path_space s')
                   (path_space s\<lparr>measure := \<lambda>X. \<mu> s' (nat_case s' -` X \<inter> (UNIV \<rightarrow> S))\<rparr>)"
      using measurable_nat_case `s \<in> S`
      by (simp add: measure_preserving_def space_path_space)
  qed (insert `s \<in> S`, simp_all add: \<tau>_distr one_ereal_def)
  show "prob_space (path_space s\<lparr>measure := \<lambda>x. ereal (\<Sum>s'\<in>S. \<tau> s s' * \<mu>' s' (nat_case s' -` x \<inter> (UNIV \<rightarrow> S)))\<rparr>)"
    by (rule prob_space.prob_space_cong[OF space'])
       (insert `s \<in> S` nat_case_sets, simp_all add: finite_measure_eq space_path_space)
next
  fix A assume "A \<in> sets (path_space_gen s)"
  from path_space_genE[OF this] guess X n . note A = this[simp]
  have \<mu>': "\<And>s'. s' \<in> S \<Longrightarrow> \<tau> s s' * \<mu>' s' (nat_case s' -` {X' \<in> UNIV \<rightarrow> S. \<forall>i\<le>n. X' i = X i} \<inter> (UNIV \<rightarrow> S)) =
    (if X 0 = s' then case n of 0 \<Rightarrow> \<tau> s s' | Suc n \<Rightarrow> \<tau> s s' * \<mu>' s' {X' \<in> UNIV \<rightarrow> S. \<forall>i\<le>n. X' i = X (Suc i)} else 0)"
    using prob_space by (simp split: nat.split add: space_path_space nat_case_cylinder del: vimage_Collect_eq)
  show "\<mu>' s A = (\<Sum>s'\<in>S. \<tau> s s' * \<mu>' s' (nat_case s' -` A \<inter> (UNIV \<rightarrow> S)))"
  proof cases
    have nat_case_idem: "\<And>f x. nat_case (f 0) (\<lambda>i. f (Suc i)) x = f x"
      by (simp split: nat.split)
    assume "\<forall>i\<le>n. X i \<in> S"
    moreover then have "S \<inter> {s. s = X 0} = {X 0}" by auto
    ultimately show ?thesis
      using finite_S `s \<in> S`
      by (simp add: \<mu>' setsum_cases prob_generator_0 prob_generator_le
                    atMost_Suc_eq_insert_0 setprod_reindex nat_case_idem zero_notin_Suc_image
               del: vimage_Collect_eq cong: setsum_cong split: nat.split)
  next
    assume "\<not> (\<forall>i\<le>n. X i \<in> S)"
    then obtain i where "X i \<notin> S" "i \<le> n" by auto
    with s0 have "A = {}"
      by (auto intro!: exI[of _ i] simp: Pi_def)
    then show ?thesis by (simp del: A)
  qed
qed

lemma measure_eq_sum:
  assumes "s \<in> S" and X: "X \<in> events s"
  shows "\<mu> s X = (\<Sum>s'\<in>S. \<tau> s s' * \<mu> s' (nat_case s' -` X \<inter> (UNIV \<rightarrow> S)))"
proof -
  { fix s' assume "s' \<in> S" then have "nat_case s' -` X \<inter> (UNIV \<rightarrow> S) \<in> sets (path_space s')"
      using measurable_nat_case[THEN measurable_sets, OF `s' \<in> S` X]
      by (simp add: space_path_space) }
  with assms show ?thesis
    by (simp add: finite_measure_eq prob_eq_sum)
qed

lemma prob_cylinder_eq_sum_prod:
  assumes Y: "\<And>i. i < n \<Longrightarrow> Y i \<subseteq> S" and "s \<in> S"
  shows "prob s {X'\<in>UNIV\<rightarrow>S. \<forall>i<n. X' i \<in> Y i} = (\<Sum>X\<in>Pi\<^isub>E {..<n} Y. \<Prod>i<n. \<tau> (nat_case s X i) (X i))"
proof -
  have "{X'\<in>UNIV\<rightarrow>S. \<forall>i<n. X' i \<in> Y i} = (\<Union>X\<in>Pi\<^isub>E {..<n} Y. {X'\<in>UNIV\<rightarrow>S. \<forall>i<n. X' i = X i})"
    by auto (rule_tac x="restrict x {..<n}" in bexI, auto)
  moreover
  have "prob s \<dots> = (\<Sum>X\<in>Pi\<^isub>E {..<n} Y. prob s {X'\<in>UNIV\<rightarrow>S. \<forall>i<n. X' i = X i})"
  proof (rule finite_measure_finite_Union)
    show "disjoint_family_on (\<lambda>i. {X' \<in> UNIV \<rightarrow> S. \<forall>ia<n. X' ia = i ia}) (Pi\<^isub>E {..<n} Y)"
    proof (unfold disjoint_family_on_def, safe, simp)
      fix A B assume "A \<in> extensional {..<n}" "B \<in> extensional {..<n}" "\<forall>i<n. B i = A i" 
      moreover assume "A \<noteq> B" then obtain i where "A i \<noteq> B i" by auto
      ultimately show False by (cases "i<n") (auto simp: extensional_def)
    qed
  qed (auto intro: finite_subset[OF Y] in_path_space')
  moreover {
    fix X assume "X\<in>Pi\<^isub>E {..<n} Y"
    with assms have "prob s {X'\<in>UNIV\<rightarrow>S. \<forall>i<n. X' i = X i} = (\<Prod>i<n. \<tau> (nat_case s X i) (X i))"
      by (intro prob_generator) (auto simp: Pi_def) }
  ultimately show ?thesis by simp
qed

lemma prob_cylinder_eq_sum_prod':
  assumes Y: "\<And>i. i \<le> n \<Longrightarrow> Y i \<subseteq> S" and "s \<in> S"
  shows "prob s {X'\<in>UNIV\<rightarrow>S. \<forall>i\<le>n. X' i \<in> Y i} = (\<Sum>X\<in>Pi\<^isub>E {..n} Y. \<Prod>i\<le>n. \<tau> (nat_case s X i) (X i))"
  using prob_cylinder_eq_sum_prod[of "Suc n", OF assms]
  by (auto simp: less_Suc_eq_le lessThan_Suc_atMost)

lemma prob_single_eq_sum:
  assumes "s \<in> S" "A \<subseteq> S"
  shows "prob s {\<omega> \<in> UNIV \<rightarrow> S. \<omega> 0 \<in> A} = (\<Sum>t\<in>A. \<tau> s t)"
proof -
  have "prob s {\<omega> \<in> UNIV \<rightarrow> S. \<omega> 0 \<in> A} =
    prob s (\<Union>s'\<in>A. {\<omega> \<in> UNIV \<rightarrow> S. \<omega> 0 = s'})"
    by (auto intro!: arg_cong[where f="prob s"])
  also have "\<dots> = (\<Sum>s'\<in>A. prob s {\<omega> \<in> UNIV \<rightarrow> S. \<omega> 0 = s'})"
    using `A \<subseteq> S` by (intro finite_measure_finite_Union) (auto simp: disjoint_family_on_def dest: finite_subset)
  also have "\<dots> = (\<Sum>s'\<in>A. \<tau> s s')"
    using prob_generator_0[OF _ `s \<in> S`] `A \<subseteq> S`
    by (simp add: subset_eq)
  finally show ?thesis .
qed

lemma prob_NT_eq_sum:
  assumes "s \<in> S" "A \<subseteq> S"
  shows "prob s {\<omega>\<in>UNIV\<rightarrow>S. \<forall>i. \<omega> i \<in> A} = 
    (\<Sum>s'\<in>A. \<tau> s s' * prob s' {\<omega>\<in>UNIV\<rightarrow>S. \<forall>i. \<omega> i \<in> A})"
proof -
  let "?V s'" = "nat_case s' -` {\<omega> \<in> UNIV \<rightarrow> S. \<forall>i. \<omega> i \<in> A} \<inter> (UNIV \<rightarrow> S)"
  from `s \<in> S` have "prob s {\<omega>\<in>UNIV\<rightarrow>S. \<forall>i. \<omega> i \<in> A} =
    (\<Sum>s'\<in>S. \<tau> s s' * prob s' (?V s'))"
    apply (rule prob_eq_sum)
    unfolding space_path_space [symmetric, of s]
    apply (auto intro!: sets_Collect)
    unfolding space_path_space
    apply auto
    done
  also have "\<dots> = (\<Sum>s'\<in>A. \<tau> s s' * prob s' {\<omega>\<in>UNIV\<rightarrow>S. \<forall>i. \<omega> i \<in> A})"
  proof (intro setsum_mono_zero_cong_right)
    show "finite S" by auto
    show "A \<subseteq> S" by fact
    { fix s' assume "s' \<notin> A"
      then have "?V s' = {}" by (auto split: nat.split) }
    then show "\<forall>s'\<in>S - A. \<tau> s s' * prob s' (?V s') = 0"
      by auto 
    fix s' assume "s' \<in> A"
    with `A \<subseteq> S` have "?V s' = {\<omega> \<in> UNIV \<rightarrow> S. \<forall>i. \<omega> i \<in> A}"
      by (auto split: nat.split)
    then show "\<tau> s s' * prob s' (?V s') =
      \<tau> s s' * prob s' {\<omega> \<in> UNIV \<rightarrow> S. \<forall>i. \<omega> i \<in> A}"
      by simp
  qed
  finally show ?thesis .
qed

lemma prob_eq_sum_single:
  assumes s: "s \<in> S" "s' \<in> S" and A: "A \<in> events s"
    and B: "\<And>s''. nat_case s'' -` A \<inter> (UNIV\<rightarrow>S) = (if s'' = s' then B else {})"
  shows "prob s A = \<tau> s s' * prob s' B"
proof -
  have "prob s A = (\<Sum>s''\<in>S. \<tau> s s'' * prob s'' (nat_case s'' -` A \<inter> (UNIV\<rightarrow>S)))"
    by (intro assms prob_eq_sum)
  also have "\<dots> = (\<Sum>s''\<in>S. if s'' = s' then \<tau> s s' * prob s' B else 0)"
    by (auto simp add: B intro!: setsum_cong)
  finally show ?thesis
    using `s' \<in> S` by (simp add: setsum_cases)
qed

lemma prob_shifted_eq:
  assumes s: "s \<in> S" "\<And>i. i < n \<Longrightarrow> \<omega> i \<in> S" and A: "A \<in> events s"
  shows "prob s ({\<omega>'\<in>UNIV\<rightarrow>S. \<forall>i<n. \<omega>' i = \<omega> i} \<inter> ((\<lambda>\<omega> i. \<omega> (i + n)) -` A \<inter> (UNIV\<rightarrow>S)))
    = (\<Prod>i<n. \<tau> (nat_case s \<omega> i) (\<omega> i)) * prob (nat_case s \<omega> n) A"
    (is "prob s (?A n s \<omega>) = _")
using s proof (induct n arbitrary: s \<omega>)
  case 0 then show ?case
    using sets_into_space[OF A] by (simp add: Int_absorb2 Int_absorb1 space_path_space)
next
  case (Suc n)
  from Suc.prems have "prob s (?A (Suc n) s \<omega>) = \<tau> s (\<omega> 0) * prob (\<omega> 0) (?A n (\<omega> 0) (\<lambda>i. \<omega> (Suc i)))"
    using sets_into_space[OF A]
    by (intro prob_eq_sum_single[OF _ _ Int[OF _ measurable_sets[OF measurable_shift A, unfolded space_path_space]]])
       (auto simp: space_path_space all_less_Suc_split intro!: sets_Collect[unfolded space_path_space])
  with Suc show ?case
    by (simp add: lessThan_Suc_eq_insert_0 setprod_reindex nat_case_idem zero_notin_Suc_image)
qed

lemma prob_shifted_sets_eq:
  assumes s: "s \<in> S" and F: "\<And>i. i < n \<Longrightarrow> F i \<subseteq> S" and A: "A \<in> events s"
  shows "prob s ({\<omega>'\<in>UNIV\<rightarrow>S. \<forall>i<n. \<omega>' i \<in> F i} \<inter> ((\<lambda>\<omega> i. \<omega> (i + n)) -` A \<inter> space (path_space s)))
    = (\<Sum>\<omega>\<in>Pi\<^isub>E {..<n} F. (\<Prod>i<n. \<tau> (nat_case s \<omega> i) (\<omega> i)) * prob (nat_case s \<omega> n) A)"
    (is "prob s (?A n s \<omega>) = _")
proof -
  let ?sA = "(\<lambda>\<omega> i. \<omega> (i + n)) -` A \<inter> space (path_space s)"
  let "?S \<omega>'" = "{\<omega>\<in>UNIV\<rightarrow>S. \<forall>i<n. \<omega> i = \<omega>' i} \<inter> ?sA"
  have eq_Union: "{\<omega>'\<in>UNIV\<rightarrow>S. \<forall>i<n. \<omega>' i \<in> F i} \<inter> ?sA
    = (\<Union>\<omega>'\<in>Pi\<^isub>E {..<n} F. ?S \<omega>')"
    apply auto
    apply (rule_tac x="restrict x {..<n}" in bexI)
    apply auto
    done
  have "prob s ({\<omega>'\<in>UNIV\<rightarrow>S. \<forall>i<n. \<omega>' i \<in> F i} \<inter> ?sA) =
    (\<Sum>\<omega>'\<in>Pi\<^isub>E {..<n} F. prob s (?S \<omega>'))"
    unfolding eq_Union
  proof (rule finite_measure_finite_Union)
    show "finite (Pi\<^isub>E {..<n} F)"
      using F by (auto intro!: finite_PiE dest: finite_subset)
    show "\<And>\<omega>'. ?S \<omega>' \<in> events s"
      by (auto intro!: Int[OF _ measurable_sets] measurable_shift A in_path_space')
    show "disjoint_family_on ?S (Pi\<^isub>E {..<n} F)"
    proof (unfold disjoint_family_on_def, intro ballI impI)
      fix \<omega>1 \<omega>2 :: "nat \<Rightarrow> 's" assume "\<omega>1 \<noteq> \<omega>2"
      then obtain i where i: "\<omega>1 i \<noteq> \<omega>2 i" by auto
      moreover assume "\<omega>1 \<in> (Pi\<^isub>E {..<n} F)" "\<omega>2 \<in> (Pi\<^isub>E {..<n} F)"
      ultimately have "i < n" by (rule_tac ccontr) (auto simp: extensional_def)
      with i show "?S \<omega>1 \<inter> ?S \<omega>2 = {}" by auto
    qed
  qed
  also have "\<dots> = (\<Sum>\<omega>'\<in>Pi\<^isub>E {..<n} F. (\<Prod>i<n. \<tau> (nat_case s \<omega>' i) (\<omega>' i)) * prob (nat_case s \<omega>' n) A)"
    using s F A unfolding space_path_space
    by (intro setsum_cong prob_shifted_eq) auto
  finally show ?thesis .
qed

subsection {* Iterative equation for simple integrals *}
  
lemma simple_integral_eq_sum:
  assumes "s \<in> S" and f: "simple_function (path_space s) f" and nonneg: "\<And>\<omega>. \<omega> \<in> UNIV \<rightarrow> S \<Longrightarrow> 0 \<le> f \<omega>"
  shows "(\<integral>\<^isup>Sx. f x \<partial>path_space s) = (\<Sum>s'\<in>S. \<tau> s s' * (\<integral>\<^isup>Sx. f (nat_case s' x) \<partial>path_space s'))"
proof -
  let "?M x s'" = "(\<lambda>\<omega>. f (nat_case s' \<omega>)) -` {x} \<inter> (UNIV \<rightarrow> S)"
  def \<mu>' \<equiv> "\<lambda>x s. \<mu> s (?M x s)"
  then have \<mu>': "\<And>x s. \<mu> s (?M x s) = \<mu>' x s" by simp
  { fix x s assume "\<mu>' x s \<noteq> 0"
    with \<mu>'[of s x] have "?M x s \<noteq> {}" by auto }
  note \<mu>'_eq_0_imp = this

  { fix s' x assume "s' \<in> S"
    then have "?M x s' = nat_case s' -` (f -` {x} \<inter> space (path_space s)) \<inter> space (path_space s')"
      by (auto simp: space_path_space)
    also have "\<dots> \<in> sets (path_space s')"
      using `s' \<in> S` `s \<in> S`
      by (intro measurable_sets[OF measurable_nat_case, OF `s' \<in> S`])
         (auto intro!: simple_functionD[OF f])
    finally have "?M x s' \<in> sets (path_space s')" . }
  note M_sets = this
  then have \<mu>'_nonneg[simp, intro!]: "\<And>s' x. s' \<in> S \<Longrightarrow> 0 \<le> \<mu>' x s'"
    by (auto intro!: positive_measure simp: \<mu>'_def)

  { fix x s' assume "s' \<in> S"
    then have "nat_case s' -` (f -` {x} \<inter> (UNIV \<rightarrow> S)) \<inter> (UNIV \<rightarrow> S) = ?M x s'"
      by (auto simp: space_path_space) }
  note nat_case_f_eq = this

  have f_image_nonneg: "\<And>x s. s \<in> S \<Longrightarrow> x \<in> (\<lambda>\<omega>. f (nat_case s \<omega>)) ` (UNIV \<rightarrow> S) \<Longrightarrow> 0 \<le> x"
    by (auto intro!: nonneg)

  have "\<And>s. s \<in> S \<Longrightarrow>((\<lambda>\<omega>. f (nat_case s \<omega>)) ` (UNIV \<rightarrow> S)) \<subseteq> f ` (UNIV \<rightarrow> S)"
    by auto
  with simple_functionD[OF f]
  have finite_f_nat_case: "\<And>s. s \<in> S \<Longrightarrow> finite ((\<lambda>\<omega>. f (nat_case s \<omega>)) ` (UNIV \<rightarrow> S))"
    by (simp add: space_path_space) (metis finite_subset)

  have "(\<Sum>s'\<in>S. ereal (\<tau> s s') * (\<Sum>x\<in>(\<lambda>\<omega>. f (nat_case s' \<omega>)) ` (UNIV \<rightarrow> S). x * \<mu>' x s')) =
    (\<Sum>s'\<in>S. (\<Sum>x\<in>(\<lambda>\<omega>. f (nat_case s' \<omega>)) ` (UNIV \<rightarrow> S). x * ereal (\<tau> s s') * \<mu>' x s'))"
    by (auto intro!: setsum_cong
             simp: setsum_ereal_right_distrib f_image_nonneg ereal_0_le_mult ac_simps)
  also have "\<dots> = (\<Sum>(s', x)\<in>(SIGMA s' : S. ((\<lambda>\<omega>. f (nat_case s' \<omega>)) ` (UNIV \<rightarrow> S))). x * ereal (\<tau> s s') * \<mu>' x s')"
    by (intro setsum_Sigma finite_S ballI finite_f_nat_case)
  also have "(SIGMA s:S. (\<lambda>\<omega>. f (nat_case s \<omega>)) ` (UNIV \<rightarrow> S)) = (\<lambda>(x,y). (y,x)) ` (f ` (UNIV \<rightarrow> S) \<times> S \<inter> {(x, s). \<exists>\<omega> \<in> UNIV\<rightarrow>S. f (nat_case s \<omega>) = x})"
    by (auto simp: image_iff intro!: nat_case_in_S)
  also have "(\<Sum>(s', x)\<in>(\<lambda>(x,y). (y,x)) ` (f ` (UNIV \<rightarrow> S) \<times> S \<inter> {(x, s). \<exists>\<omega> \<in> UNIV\<rightarrow>S. f (nat_case s \<omega>) = x}). x * ereal (\<tau> s s') * \<mu>' x s')
    = (\<Sum>(x, s')\<in>f ` (UNIV \<rightarrow> S) \<times> S. x * ereal (\<tau> s s') * \<mu>' x s')"
    using simple_functionD[OF f]
    by (auto simp add: swap_inj_on setsum_reindex space_path_space
             intro!: setsum_mono_zero_cong_left dest!: \<mu>'_eq_0_imp)
  also have "\<dots> = (\<Sum>x\<in>f ` (UNIV \<rightarrow> S). x * (\<Sum>s'\<in>S. ereal (\<tau> s s') * \<mu>' x s'))"
    using `s \<in> S`
    by (auto intro!: setsum_cong
             simp: setsum_cartesian_product[symmetric] setsum_ereal_right_distrib ereal_0_le_mult \<tau>_nneg ac_simps)
  finally have "(\<Sum>s'\<in>S. ereal (\<tau> s s') * (\<Sum>x\<in>(\<lambda>\<omega>. f (nat_case s' \<omega>)) ` (UNIV \<rightarrow> S). x * \<mu>' x s')) =
    (\<Sum>x\<in>f ` (UNIV \<rightarrow> S). x * (\<Sum>s'\<in>S. ereal (\<tau> s s') * \<mu>' x s'))" .
  then show ?thesis
    unfolding simple_integral_def
    by (subst measure_eq_sum[OF `s \<in> S` simple_functionD(2), OF f])
       (simp add: nat_case_f_eq space_path_space \<mu>' del: vimage_Int)
qed
  
subsection {* Iterative equation for the Lebesgue integral *}

lemma positive_integral_eq_sum:
  assumes "s \<in> S" and f: "f \<in> borel_measurable (path_space s)"
  shows "(\<integral>\<^isup>+x. f x \<partial>path_space s) = (\<Sum>s'\<in>S. \<tau> s s' * (\<integral>\<^isup>+x. f (nat_case s' x) \<partial>path_space s'))"
proof -
  have sa_s: "sigma_algebra (path_space s)" by default
  from borel_measurable_implies_simple_function_sequence'[OF f]
  guess g . note g = this
  then have "(\<integral>\<^isup>+x. f x \<partial>path_space s) = (\<integral>\<^isup>+x. (SUP i. g i x) \<partial>path_space s)"
    by (simp add: positive_integral_max_0)
  also have "\<dots> = (SUP i. \<integral>\<^isup>Sx. g i x \<partial>path_space s)"
    using positive_integral_monotone_convergence_simple[OF g(2,5,1)]
    by simp
  also have "\<dots> = (SUP i. \<Sum>s'\<in>S. \<tau> s s' * (\<integral>\<^isup>Sx. (g i \<circ> nat_case s') x \<partial>path_space s'))"
    using `s \<in> S` g(1,5) by (simp add: simple_integral_eq_sum)
  also have "\<dots> = (\<Sum>s'\<in>S. SUP i. \<tau> s s' * (\<integral>\<^isup>Sx. (g i \<circ> nat_case s') x \<partial>path_space s'))"
    using g `s \<in> S`
    by (intro SUPR_ereal_setsum incseq_cmult_ereal incseq_simple_integral g ereal_0_le_mult
              simple_function_comp2[OF sa_s measurable_nat_case] incseq_comp simple_integral_positive)
       auto
  also have "\<dots> = (\<Sum>s'\<in>S. \<tau> s s' * (SUP i. \<integral>\<^isup>Sx. (g i \<circ> nat_case s') x \<partial>path_space s'))"
    using g `s \<in> S`
    by (intro setsum_cong refl SUPR_ereal_cmult simple_integral_positive
                 simple_function_comp2[OF sa_s measurable_nat_case])
       auto
  also have "\<dots> = (\<Sum>s'\<in>S. \<tau> s s' * (\<integral>\<^isup>+x. (SUP i. (g i \<circ> nat_case s') x) \<partial>path_space s'))"
    using g `s \<in> S`
    apply (intro setsum_cong refl)
    apply (subst positive_integral_monotone_convergence_simple)
    apply (auto intro!: simple_function_comp2[OF sa_s measurable_nat_case] simple_integral_positive incseq_comp)
    done
  also have "\<dots> = (\<Sum>s'\<in>S. \<tau> s s' * (\<integral>\<^isup>+x. f (nat_case s' x) \<partial>path_space s'))"
    using g by (simp add: positive_integral_max_0)
  finally show ?thesis .
qed

lemma positive_integral_select_0:
  assumes "s \<in> S" "\<And>s. s \<in> S \<Longrightarrow> 0 \<le> f s"
  shows "(\<integral>\<^isup>+\<omega>. f (\<omega> 0) \<partial>path_space s) = (\<Sum>s'\<in>S. \<tau> s s' * f s')"
proof (subst positive_integral_eq_sum)
  show "(\<lambda>\<omega>. ereal (f (\<omega> 0))) \<in> borel_measurable (path_space s)"
    apply (intro borel_measurable_ereal)
  proof (unfold measurable_def space_path_space, safe)
    fix i :: nat and A :: "real set" assume "A \<in> sets borel"
    have "(\<lambda>\<omega>. f (\<omega> 0)) -` A \<inter> (UNIV \<rightarrow> S) = {\<omega>\<in>UNIV\<rightarrow>S. \<omega> 0 \<in> f -` A}"
      by auto
    also have "\<dots> \<in> events s"
      by (rule in_path_space_in_single)
    finally show "(\<lambda>\<omega>. f (\<omega> 0)) -` A \<inter> (UNIV \<rightarrow> S) \<in> events s" .
  qed simp
qed (insert assms, auto simp add: measure_space_1)

subsection {* Iterative equation for the AE-quantifier *}

lemma AE_split:
  assumes ae: "AE \<omega> in path_space s. \<omega> \<in> A" and A: "A \<in> events s"
    and s: "s \<in> S" "s' \<in> S" "\<tau> s s' \<noteq> 0"
  shows "AE \<omega> in path_space s'. \<omega> \<in> nat_case s' -` A \<inter> (UNIV\<rightarrow>S)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  with measurable_nat_case[THEN measurable_sets, OF `s' \<in> S` A]
  have neq_1: "prob s' (nat_case s' -` A \<inter> (UNIV\<rightarrow>S)) \<noteq> 1"
    by (subst (asm) AE_in_set_eq_1) (auto simp: space_path_space)
  
  from ae A
  have "1 = prob s A" by (simp add: AE_in_set_eq_1)
  also have "\<dots> = (\<Sum>s'\<in>S. \<tau> s s' * prob s' (nat_case s' -` A \<inter> (UNIV\<rightarrow>S)))"
    by (rule prob_eq_sum) fact+
  also have "\<dots> < (\<Sum>s'\<in>S. \<tau> s s' * 1)"
  proof (intro setsum_strict_mono_single mult_strict_left_mono mult_left_mono)
    show "0 < \<tau> s s'"
      using s by (auto simp: less_le)
    show "prob s' (nat_case s' -` A \<inter> (UNIV\<rightarrow>S)) < 1"
      using s neq_1 by (auto simp: less_le)
  qed (insert s, auto)
  finally show False
    using s by (simp add: \<tau>_distr)
qed

lemma AE_iff_AE_next:
  assumes s: "s \<in> S" and A: "{\<omega>\<in>space (path_space s). P \<omega>} \<in> events s"
  shows "(AE \<omega> in path_space s. P \<omega>) \<longleftrightarrow>
    (\<forall>s'\<in>S. \<tau> s s' \<noteq> 0 \<longrightarrow> (AE \<omega> in path_space s'. P (nat_case s' \<omega>)))"
proof safe
  fix s' assume s': "s' \<in> S" "\<tau> s s' \<noteq> 0" and ae: "AE \<omega> in path_space s. P \<omega>"
  from ae s A show "AE \<omega> in path_space s'. P (nat_case s' \<omega>)"
    using AE_split[OF _ A s s'] by simp
next
  assume *: "\<forall>s'\<in>S. \<tau> s s' \<noteq> 0 \<longrightarrow> (AE \<omega> in path_space s'. P (nat_case s' \<omega>))"

  show "AE \<omega> in path_space s. P \<omega>"
  proof (subst AE_iff_measurable[OF _ refl])
    show "{\<omega>\<in>space (path_space s). \<not> P \<omega>} \<in> sets (path_space s)"
      using A by (auto intro: sets_Collect)
    with s have "\<mu> s {\<omega>\<in>space (path_space s). \<not> P \<omega>} =
      (\<Sum>s'\<in>S. \<tau> s s' * \<mu> s' (nat_case s' -` {\<omega>\<in>space (path_space s). \<not> P \<omega>} \<inter> (UNIV\<rightarrow>S)))"
      by (rule measure_eq_sum)
    also have "\<dots> = (\<Sum>s'\<in>S. 0)"
    proof (safe intro!: setsum_cong)
      fix s' assume "s' \<in> S"
      show "\<tau> s s' * \<mu> s' (nat_case s' -` {\<omega>\<in>space (path_space s). \<not> P \<omega>} \<inter> (UNIV\<rightarrow>S)) = 0"
      proof cases
        assume "\<tau> s s' \<noteq> 0"
        with `s' \<in> S` * have ae: "AE \<omega> in path_space s'. P (nat_case s' \<omega>)" by auto
        have "{\<omega>\<in>space (path_space s'). P (nat_case s' \<omega>)} =
          nat_case s' -` {\<omega>\<in>space (path_space s). P \<omega>} \<inter> space (path_space s')"
          using `s' \<in> S` by (auto simp: space_path_space)
        also have "\<dots> \<in> sets (path_space s')"
          using `s' \<in> S` A
          by (intro measurable_sets[OF measurable_nat_case])
             (auto intro: sets_Collect)
        finally have "{\<omega>\<in>space (path_space s'). P (nat_case s' \<omega>)} \<in> sets (path_space s')" .
        from AE_E2[OF ae this] have "\<mu> s' {x \<in> space (path_space s'). \<not> P (nat_case s' x)} = 0" .
        also have "{x \<in> space (path_space s'). \<not> P (nat_case s' x)} =
          nat_case s' -` {\<omega>\<in>space (path_space s). \<not> P \<omega>} \<inter> (UNIV\<rightarrow>S)"
          using `s' \<in> S` by (auto simp: space_path_space)
        finally show "\<tau> s s' * \<mu> s' (nat_case s' -` {\<omega>\<in>space (path_space s). \<not> P \<omega>} \<inter> (UNIV\<rightarrow>S)) = 0"
          by simp
      qed simp
    qed
    finally show "\<mu> s {\<omega> \<in> space (path_space s). \<not> P \<omega>} = 0" by simp
  qed
qed

subsection {* @{text reachable} *}

definition "reachable \<Phi> s = {t\<in>S. \<exists>\<omega> n. (\<forall>i\<le>n. \<tau> (nat_case s \<omega> i) (\<omega> i) \<noteq> 0) \<and> (\<forall>i<n. \<omega> i \<in> \<Phi>) \<and> \<omega> n = t}"

lemma reachableE:
  assumes "t \<in> reachable \<Phi> s"
  obtains \<omega> n where "t \<in> S" "\<forall>i\<le>n. \<tau> (nat_case s \<omega> i) (\<omega> i) \<noteq> 0" "\<forall>i<n. \<omega> i \<in> \<Phi>" "\<omega> n = t"
  using assms unfolding reachable_def by auto

lemma finite_reachable[simp, intro]: "finite (reachable \<Phi> s)"
  unfolding reachable_def by auto

lemma reachable_mono:
  "S' \<subseteq> S \<Longrightarrow> reachable S' s \<subseteq> reachable S s"
  unfolding reachable_def by blast

lemma reachable_in:
  "\<lbrakk> \<omega> n \<in> S ; \<And>i. i \<le> n \<Longrightarrow> \<tau> (nat_case s' \<omega> i) (\<omega> i) \<noteq> 0 ;
     \<And>i. i < n \<Longrightarrow> \<omega> i \<in> F \<rbrakk> \<Longrightarrow> \<omega> n \<in> reachable F s'" 
  by (auto intro!: exI[of _ \<omega>] exI[of _ n] simp: reachable_def)

lemma reachable_closed:
  assumes R: "s \<in> R" "R \<subseteq> S" "R \<inter> \<Psi> = {}" "s \<in> \<Phi>"
    and subset: "\<Phi> \<subseteq> S"
    and closed: "\<forall>s\<in>R \<inter> \<Phi>. \<forall>s'\<in>S-R. \<tau> s s' = 0"
  shows "reachable (\<Phi> - \<Psi>) s \<subseteq> R"
proof
  fix t assume "t \<in> reachable (\<Phi> - \<Psi>) s"
  from this[THEN reachableE] guess \<omega> n . note \<omega> = this
  with subset have \<omega>_in_S: "\<And>i. i \<le> n \<Longrightarrow> \<omega> i \<in> S"
    by (auto simp add: le_less)
  { fix i assume "i \<le> n"
    then have "\<omega> i \<in> R"
    proof (induct i)
      case 0
      with closed \<omega>(2)[rule_format, of 0] `s \<in> R` `s \<in> \<Phi>` \<omega>_in_S
      show ?case by auto
    next
      case (Suc i)
      with closed \<omega>(2)[rule_format, of "Suc i"] \<omega>(3)[rule_format, of i] \<omega>_in_S
      show ?case
        by auto
    qed }
  then show "t \<in> R"
    using \<omega>(4)[symmetric] by simp
qed

lemma reachable_closed':
  assumes R: "s \<in> R" "s \<in> \<Phi>" "R \<subseteq> S" "\<Phi> \<subseteq> S"
    and closed: "\<forall>s\<in>R \<inter> \<Phi>. \<forall>s'\<in>S. \<tau> s s' \<noteq> 0 \<longrightarrow> s' \<in> R"
  shows "reachable \<Phi> s \<subseteq> R"
proof -
  have "reachable (\<Phi> - {}) s \<subseteq> R"
  proof (rule reachable_closed)
    show "\<forall>s\<in>R \<inter> \<Phi>. \<forall>s'\<in>S - R. \<tau> s s' = 0"
      using closed by auto
    show "R \<inter> {} = {}" by auto
  qed fact+
  then show ?thesis by simp
qed

lemma reachable_trans:
  assumes t: "t \<in> reachable \<Phi> s" and t': "t' \<in> reachable \<Phi> t" and "t \<in> \<Phi>"
  shows "t' \<in> reachable \<Phi> s"
proof -
  from t[THEN reachableE] guess \<omega>1 n1 . note \<omega>1 = this
  from t'[THEN reachableE] guess \<omega>2 n2 . note \<omega>2 = this
  let ?n = "n1 + n2 + 1"
  let "?\<omega> i" = "if i \<le> n1 then \<omega>1 i else \<omega>2 (i - n1 - 1)"
  from \<omega>1 have *: "nat_case s ?\<omega> =
    (\<lambda>i. if i \<le> n1 then nat_case s \<omega>1 i else nat_case t \<omega>2 (i - n1 - 1))"
    by (auto intro!: ext split: nat.split
             simp: le_imp_diff_is_add not_le less_Suc_eq)
  show "t' \<in> reachable \<Phi> s" unfolding reachable_def
  proof (safe intro!: exI[of _ ?n] exI[of _ ?\<omega>] del: notI)
    show "?\<omega> ?n = t'"
      using \<omega>2 \<omega>1 by simp
  next
    fix i assume "i \<le> ?n"
    show "\<tau> (nat_case s ?\<omega> i) (?\<omega> i) \<noteq> 0"
    proof cases
      assume "i \<le> n1" with \<omega>1 show ?thesis by (simp add: *)
    next
      assume "\<not> i \<le> n1" with `i \<le> ?n` \<omega>2 show ?thesis
        by (simp add: * not_le)
    qed
  next
    fix i assume "i < n1 + n2 + 1" with \<omega>1 \<omega>2 `t \<in> \<Phi>` show "?\<omega> i \<in> \<Phi>"
      by (auto simp: le_less)
  qed fact
qed

lemma reachable_outreach:
  assumes t: "t \<in> reachable S' s" and T: "T \<subseteq> S" "t \<in> T"
  shows "\<exists>t\<in>T. t \<in> reachable (S' - T) s"
proof -
  from t[THEN reachableE] guess \<omega> n' . note \<omega> = this
  then have "\<omega> n' \<in> T" using T by auto
  from smallest[where P="\<lambda>n. \<omega> n \<in> T", OF this]
  guess n . note n = this
  show ?thesis
  proof
    show "\<omega> n \<in> T" by fact
    show "\<omega> n \<in> reachable (S' - T) s"
      using \<omega> n T unfolding reachable_def
      by (auto intro!: exI[of _ \<omega>] exI[of _ n])
  qed
qed

lemma reachable_closed_rev:
  assumes t: "t \<in> reachable (\<Phi> - \<Psi>) s" and "t \<in> R"
    and R: "R \<subseteq> S" "{s\<in>\<Phi>-\<Psi>. \<exists>s'\<in>R. \<tau> s s' \<noteq> 0} \<subseteq> R" and s: "s \<in> \<Phi>" "s \<notin> \<Psi>"
  shows "s \<in> R"
proof -
  from t[THEN reachableE] guess \<omega> n . note \<omega> = this
  have "0 \<le> Suc n \<and> nat_case s \<omega> 0 \<in> R"
  proof (induct rule: zero_induct)
    show "Suc n \<le> Suc n \<and> nat_case s \<omega> (Suc n) \<in> R" using \<omega> `t \<in> R` by simp
  next
    fix i assume i: "Suc i \<le> Suc n \<and> nat_case s \<omega> (Suc i) \<in> R"
    moreover 
    with \<omega>(2)[rule_format, of i] have "\<tau> (nat_case s \<omega> i) (\<omega> i) \<noteq> 0" by simp
    moreover
    have "nat_case s \<omega> i \<in> \<Phi> - \<Psi>"
      using \<omega> i s by (auto split: nat.split)
    ultimately
    show "i \<le> Suc n \<and> nat_case s \<omega> i \<in> R"
      using R by (auto simp add: subset_eq)
  qed
  then show "s \<in> R" by simp
qed

lemma reachable_step:
  assumes "s'' \<in> reachable \<Phi> s'" and s': "s' \<in> \<Phi>" "\<tau> s s' \<noteq> 0"
  shows "s'' \<in> reachable \<Phi> s"
proof -
  from `s'' \<in> reachable \<Phi> s'` obtain \<omega> n where
    "s'' \<in> S" "\<forall>i\<le>n. \<tau> (nat_case s' \<omega> i) (\<omega> i) \<noteq> 0" "\<forall>i<n. \<omega> i \<in> \<Phi>" "\<omega> n = s''"
    by (auto simp: reachable_def)
  with s' have "s'' \<in> S" "\<forall>i\<le>Suc n. \<tau> (nat_case s (nat_case s' \<omega>) i) (nat_case s' \<omega> i) \<noteq> 0"
    "\<forall>i<Suc n. nat_case s' \<omega> i \<in> \<Phi>" "nat_case s' \<omega> (Suc n) = s''"
    unfolding all_Suc_split all_less_Suc_split by auto
  then show ?thesis
    unfolding reachable_def by blast
qed

lemma reachable_\<tau>:
  "\<tau> s s' \<noteq> 0 \<Longrightarrow> s' \<in> S \<Longrightarrow> s' \<in> reachable \<Phi> s"
  unfolding reachable_def by (auto intro!: exI[of _ 0] exI[of _ "\<lambda>_. s'"])

subsection {* @{text until} *}

definition until :: "'s set \<Rightarrow> 's set \<Rightarrow> (nat \<Rightarrow> 's) set" where
  "until \<Phi> \<Psi> = {\<omega>\<in>UNIV\<rightarrow>S. \<exists>n. (\<forall>i<n. \<omega> i \<in> \<Phi>) \<and> \<omega> n \<in> \<Psi>}"

lemma untilI:
  "\<lbrakk> \<omega> \<in> UNIV \<rightarrow> S ; \<And>i. i < n \<Longrightarrow> \<omega> i \<in> \<Phi> ; \<omega> n \<in> \<Psi> \<rbrakk> \<Longrightarrow> \<omega> \<in> until \<Phi> \<Psi>"
  unfolding until_def by auto

lemma untilE:
  assumes "\<omega> \<in> until \<Phi> \<Psi>"
  obtains n where "\<omega> \<in> UNIV \<rightarrow> S" "\<forall>i < n. \<omega> i \<in> \<Phi>" "\<omega> n \<in> \<Psi>"
  using assms  unfolding until_def by auto

lemma untilE2:
  assumes \<omega>: "\<omega> \<in> until \<Phi> \<Psi>"
  obtains n where "\<omega> \<in> UNIV \<rightarrow> S" "\<And>i. i < n \<Longrightarrow> \<omega> i \<in> \<Phi> - \<Psi>" "\<omega> n \<in> \<Psi>"
proof -
  from untilE[OF \<omega>] guess n . note n = this
  from smallest[where P="\<lambda>n. \<omega> n \<in> \<Psi>", OF n(3)] guess n' .
  with n(2) have "(\<forall>i<n'. \<omega> i \<in> \<Phi> - \<Psi>) \<and> \<omega> n' \<in> \<Psi>"
    by auto
  with that n(1) show thesis by auto
qed

lemma until_eq: "until \<Phi> \<Psi> = {\<omega>\<in>UNIV\<rightarrow>S. \<exists>n. (\<forall>i<n. \<omega> i \<in> \<Phi> - \<Psi>) \<and> \<omega> n \<in> \<Psi>}"
  by (safe intro!: untilI elim!: untilE2) auto

lemma until_eq2: "until (\<Phi> \<union> \<Psi>) \<Psi> = until \<Phi> \<Psi>"
  unfolding until_eq by auto

lemma untilI2:
  assumes "\<omega> \<in> UNIV \<rightarrow> S" "\<And>i. i < n \<Longrightarrow> \<omega> i \<in> \<Phi> \<union> \<Psi>" "\<omega> n \<in> \<Psi>"
  shows "\<omega> \<in> until \<Phi> \<Psi>"
  using untilI[of \<omega> n, OF assms] by (simp add: until_eq2)

lemma until_first[simp]:
  "\<Psi> \<subseteq> S \<Longrightarrow> s \<in> \<Psi> \<Longrightarrow> nat_case s -` until \<Phi> \<Psi> = UNIV\<rightarrow>S"
  by (auto simp: until_def Pi_iff split: nat.split)

lemma until_next[simp]:
  "\<Phi> \<subseteq> S \<Longrightarrow> s \<in> \<Phi> \<Longrightarrow> s \<notin> \<Psi> \<Longrightarrow> nat_case s -` until \<Phi> \<Psi> = until \<Phi> \<Psi>"
  by (simp add: all_conj_distrib set_eq_iff until_def gr0_conv_Suc Pi_iff split: nat.split) blast

lemma until_empty[simp]:
  "s \<notin> \<Psi> \<Longrightarrow> s \<notin> \<Phi> \<Longrightarrow> nat_case s -` until \<Phi> \<Psi> = {}"
  by (auto simp: until_def gr0_conv_Suc split: nat.split)

lemma sets_until[simp, intro]: "until \<Phi> \<psi> \<in> events s"
  by (auto simp: until_def intro!: sets_Collect[unfolded space_path_space])

lemma sets_nat_case_until[simp, intro]: "s \<in> S \<Longrightarrow> nat_case s -` until \<Phi> \<psi> \<inter> (UNIV\<rightarrow>S) \<in> events s"
  unfolding space_path_space[symmetric, of s] 
  using measurable_sets[OF measurable_nat_case sets_until] .

lemma prob_until_eq_sum:
  assumes s: "s \<in> \<Phi>" "s \<notin> \<Psi>" "\<Psi> \<subseteq> S" "\<Phi> \<subseteq> S"
  shows "prob s (nat_case s -` until \<Phi> \<Psi> \<inter> (UNIV \<rightarrow> S)) = (\<Sum>s'\<in>S. \<tau> s s' * prob s' (nat_case s' -` until \<Phi> \<Psi> \<inter> (UNIV \<rightarrow> S)))"
    (is "prob s (?U s) = _")
proof -
  { fix s' assume "s' \<in> S"
    with assms have "?U s' = nat_case s' -` (?U s) \<inter> (UNIV \<rightarrow> S)"
      by (cases "s' \<in> \<Psi>" "s' \<in> \<Phi>" rule: bool.exhaust[case_product bool.exhaust]) auto }
  with s assms show "prob s (?U s) = (\<Sum>s'\<in>S. \<tau> s s' * prob s' (?U s'))"
    by (subst prob_eq_sum) auto
qed

lemma until_eq_0_iff_not_reachable:
  assumes "s \<in> S" "\<Phi> \<subseteq> S" "\<Psi> \<subseteq> S"
  shows "prob s (nat_case s -` until \<Phi> \<Psi> \<inter> (UNIV\<rightarrow>S)) = 0 \<longleftrightarrow> s \<notin> \<Psi> \<and> (s \<in> \<Phi> \<longrightarrow> reachable (\<Phi> - \<Psi>) s \<inter> \<Psi> = {})"
proof cases
  assume "s \<in> \<Phi> - \<Psi>"
  def E \<equiv> "\<lambda>n i. if i = (n::nat) then \<Psi> else \<Phi> - \<Psi>"
  def X \<equiv> "\<lambda>n. {\<omega>\<in>UNIV\<rightarrow>S. \<forall>i\<le>n::nat. \<omega> i \<in> E n i}"

  have [simp]: "finite \<Phi>" "finite \<Psi>" using assms by (auto dest: finite_subset)
  then have [simp]: "\<And>n. finite (Pi\<^isub>E {.. n} (E n))" by (auto simp: E_def)
  have "\<And>n. \<forall>i\<le>n. E n i \<subseteq> S"
    using assms by (auto simp: E_def)
  then have E_subset: "\<And>x n i. x \<in> Pi\<^isub>E {.. n} (E n) \<Longrightarrow> i \<le> n \<Longrightarrow> x i \<in> S"
    by (auto simp: Pi_iff)

  have "(\<lambda>n. prob s (X n)) sums prob s (\<Union>n. X n)"
  proof (rule finite_measure_UNION)
    show "disjoint_family X"
    proof (unfold disjoint_family_on_def, intro ballI impI)
      fix m n :: nat assume "m \<noteq> n"
      then show "X m \<inter> X n = {}" unfolding X_def E_def
        by (safe elim!: allE[of _ "min m n"]) (auto split: split_if_asm)
    qed
  qed (auto split del: split_if simp: X_def)
  also have "(\<Union>n. X n) = nat_case s -` until \<Phi> \<Psi>"
    using `s \<in> \<Phi>-\<Psi>` `s \<in> S`
    apply (simp add: le_less until_eq set_eq_iff X_def E_def)
    apply (split nat.split)
    apply (simp add: all_less_Suc_split gr0_conv_Suc)
    apply (auto simp: Pi_iff split: nat.split_asm)
    done
  also have "\<dots> = nat_case s -` until \<Phi> \<Psi> \<inter> (UNIV \<rightarrow> S)"
    by (auto simp: until_def Pi_iff split: nat.split_asm)
  finally have "(\<lambda>n. prob s (X n)) sums prob s (nat_case s -` until \<Phi> \<Psi> \<inter> (UNIV \<rightarrow> S))" .
  then have "prob s (nat_case s -` until \<Phi> \<Psi> \<inter> (UNIV \<rightarrow> S)) = 0 \<longleftrightarrow> (\<forall>n. prob s (X n) = 0)"
    using sums_0_iff[OF positive_measure'[of s], of X]
    by (auto simp add: sums_iff)
  also have "\<dots> \<longleftrightarrow> (\<forall>n. (\<Sum>\<omega>\<in>Pi\<^isub>E {.. n} (E n). \<Prod>i\<le>n. \<tau> (nat_case s \<omega> i) (\<omega> i)) = 0)"
    using assms unfolding X_def E_def by (subst prob_cylinder_eq_sum_prod') auto
  also have "\<dots> \<longleftrightarrow> (\<forall>n. \<forall>\<omega>\<in>Pi\<^isub>E {.. n} (E n). \<exists>i\<le>n. \<tau> (nat_case s \<omega> i) (\<omega> i) = 0)"
    using assms E_subset
    apply (subst setsum_nonneg_eq_0_iff)
    apply (auto intro!: setprod_nonneg \<tau>_nneg
                simp: Bex_def split: nat.split)
    apply (auto intro!: E_subset)
    done
  also have "\<dots> \<longleftrightarrow> reachable (\<Phi> - \<Psi>) s \<inter> \<Psi> = {}"
  proof (safe, simp_all)
    assume *: "\<forall>n. \<forall>\<omega>\<in>Pi\<^isub>E {.. n} (E n). \<exists>i\<le>n. \<tau> (nat_case s \<omega> i) (\<omega> i) = 0"
    fix t assume t: "t \<in> reachable (\<Phi> - \<Psi>) s" "t \<in> \<Psi>"
    from t(1) guess \<omega> n by (rule reachableE) note \<omega> = this
    then have "restrict \<omega> {..n} \<in> Pi\<^isub>E {..n} (E n)"
      using `t \<in> \<Psi>` by (auto simp: E_def)
    from *[rule_format, OF this]
    obtain i where "i \<le> n" "\<tau> (nat_case s (restrict \<omega> {..n}) i) (\<omega> i) = 0"
      by auto
    with \<omega> show False by (auto split: nat.split_asm)
  next
    fix \<omega>' n assume "\<omega>' \<in> Pi {.. n} (E n)"
    then have "\<forall>i<n. \<omega>' i \<in> \<Phi> - \<Psi>" "\<omega>' n \<in> \<Psi>"
      unfolding E_def by (auto split: split_if_asm)
    moreover def \<omega> \<equiv> "\<lambda>i. if i \<le> n then \<omega>' i else s0"
    ultimately have "\<forall>i<n. \<omega> i \<in> \<Phi> - \<Psi>" "\<omega> n \<in> \<Psi>" "\<forall>i. \<omega> i \<in> S"
      using s0 assms unfolding E_def by (auto split: split_if simp: le_less)
    moreover assume "reachable (\<Phi> - \<Psi>) s \<inter> \<Psi> = {}"
    ultimately have "\<exists>i\<le>n. \<tau> (nat_case s \<omega> i) (\<omega> i) = 0"
      unfolding reachable_def
      apply (simp add: set_eq_iff)
      apply (erule allE[of _ "\<omega> n"])
      apply simp
      apply (erule allE[of _ \<omega>])
      apply auto
      done
    then guess i ..
    moreover then have "nat_case s \<omega> i = nat_case s \<omega>' i" "\<omega> i = \<omega>' i"
      by (auto simp: \<omega>_def split: nat.split)
    ultimately show "\<exists>i\<le>n. \<tau> (nat_case s \<omega>' i) (\<omega>' i) = 0" by auto
  qed
  finally show ?thesis using `s \<in> \<Phi> - \<Psi>` by auto
next
  assume s': "s \<notin> \<Phi> - \<Psi>"
  show ?thesis
  proof cases
    assume "s \<in> \<Psi>"
    then have "nat_case s -` until \<Phi> \<Psi> \<inter> (UNIV \<rightarrow> S) = space (path_space s)"
      using `s \<in> S` by (auto simp: until_def space_path_space split: nat.split)
    with `s \<in> \<Psi>` show ?thesis by (simp add: prob_space)
  next
    assume "s \<notin> \<Psi>"
    with s' have "nat_case s -` until \<Phi> \<Psi> \<inter> (UNIV \<rightarrow> S) = {}"
      using `s \<in> S` by (auto simp: until_def gr0_conv_Suc split: nat.split)
    with s' `s \<notin> \<Psi>` show ?thesis by simp
  qed
qed

lemma closed: 
  assumes R: "s \<in> R" "R \<subseteq> S" "R \<inter> \<Psi> = {}" and S: "\<Phi> \<subseteq> S" "\<Psi> \<subseteq> S"
    and closed: "\<forall>s\<in>R \<inter> \<Phi>. \<forall>s'\<in>S-R. \<tau> s s' = 0"
  shows "prob s (nat_case s -` until \<Phi> \<Psi> \<inter> (UNIV\<rightarrow>S)) = 0"
proof cases
  assume "s \<in> \<Phi>"
  have "s \<in> S" "s \<notin> \<Psi>" using R by auto
  have "reachable (\<Phi> - \<Psi>) s \<subseteq> R"
  proof (rule reachable_closed')
    show "\<forall>s\<in>R \<inter> (\<Phi> - \<Psi>). \<forall>s'\<in>S. \<tau> s s' \<noteq> 0 \<longrightarrow> s' \<in> R"
      using closed by auto
    show "s \<in> \<Phi> - \<Psi>" using `s \<notin> \<Psi>` `s \<in> \<Phi>` by auto
    show "\<Phi> - \<Psi> \<subseteq> S" using S by auto
  qed fact+
  then have "reachable (\<Phi> - \<Psi>) s \<inter> \<Psi> = {}"
    using R by auto
  then show ?thesis
    using `s \<in> S` `s \<in> \<Phi>` `s \<notin> \<Psi>` until_eq_0_iff_not_reachable S
    by (simp del: until_next)
next
  assume "s \<notin> \<Phi>"
  moreover have "s \<notin> \<Psi>" using R by auto
  ultimately show ?thesis by simp
qed

subsection {* @{text Fair} *}

definition "Fair sx tx \<omega> \<longleftrightarrow>
  (\<exists>j. \<forall>i\<ge>j. \<omega> i \<noteq> sx) \<or> (\<forall>i. \<exists>j\<ge>i. \<omega> j = sx \<and> \<omega> (Suc j) = tx)"

lemma AE_Fair:
  assumes "s \<in> S"
  shows "AE \<omega> in path_space s. \<forall>sx\<in>S. \<forall>tx\<in>S. \<tau> sx tx \<noteq> 0 \<longrightarrow> Fair sx tx (nat_case s \<omega>)"
proof (intro finite_S AE_finite_allI AE_impI)
  def c \<equiv> "Min ((\<lambda>(s,t). \<tau> s t) ` (S \<times> S) - {0})"
  moreover have "(\<lambda>(s,t). \<tau> s t) ` (S \<times> S) - {0} \<noteq> {}"
    using \<tau>_exists S_not_empty by auto
  ultimately have c: "0 < c" "\<And>s t. s \<in> S \<Longrightarrow> t \<in> S \<Longrightarrow> \<tau> s t \<noteq> 0 \<Longrightarrow> c \<le> \<tau> s t"
    by (auto intro!: Min_le simp: Min_gr_iff) (auto simp: less_le)

  fix sx tx assume "sx \<in> S" "tx \<in> S" "\<tau> sx tx \<noteq> 0"
  def Never \<equiv> "\<lambda>s. {\<omega>\<in>UNIV\<rightarrow>S. (\<forall>i. (\<exists>j\<ge>i. nat_case s \<omega> j = sx) \<and> (nat_case s \<omega> i = sx \<longrightarrow> \<omega> i \<noteq> tx)) }"
  { fix n have "\<And>s s' t. {\<omega> \<in> UNIV \<rightarrow> S. nat_case s' \<omega> n = t} \<in> events s"
      by (cases n) (auto intro: sets_Collect[unfolded space_path_space]) }
  note sets_nat_case = this
  have sets_Never: "\<And>s s'. Never s' \<in> events s"
    by (auto intro!: sets_Collect[unfolded space_path_space] sets_nat_case simp: Never_def)

  { fix s assume "s \<in> S"
    def Step \<equiv> "\<lambda>s n. Never s \<inter> {\<omega>\<in>UNIV\<rightarrow>S. (\<forall>i<n. \<omega> i \<noteq> sx) \<and> \<omega> n = sx}"
    then have sets_Step: "\<And>s' n. Step s' n \<in> events s"
      by (auto intro!: Int sets_Collect[unfolded space_path_space] sets_nat_case sets_Never)

    have "Never s = (\<Union>n. Step s n)"
      unfolding Step_def
    proof safe
      fix \<omega> assume \<omega>: "\<omega> \<in> Never s"
      moreover
      def n \<equiv> "LEAST n. \<omega> n = sx"
      from \<omega> have "(\<exists>j\<ge>Suc 0. nat_case s \<omega> j = sx)"
        by (auto simp: Never_def)
      then obtain j where "0 < j" "nat_case s \<omega> j = sx"
        by (auto simp: Suc_le_eq)
      then have "\<omega> (j - 1) = sx" by (auto simp: gr0_conv_Suc)
      then have "\<omega> n = sx \<and> (\<forall>i<n. \<omega> i \<noteq> sx)"
        unfolding n_def by (rule LeastI2_wellorder) auto
      moreover
      from \<omega> have "\<omega> \<in> UNIV \<rightarrow> S"
        by (auto simp: Never_def)
      ultimately
      show " \<omega> \<in> (\<Union>n. Never s \<inter> {\<omega> \<in> UNIV \<rightarrow> S. (\<forall>i<n. \<omega> i \<noteq> sx) \<and> \<omega> n = sx})"
        by auto
    qed
    moreover have "(\<lambda>n. prob s (Step s n)) sums prob s (\<Union>n. Step s n)"
    proof (rule finite_measure_UNION)
      show "disjoint_family (Step s)"
        by (auto simp: neq_iff Step_def disjoint_family_on_def)
      show "range (Step s) \<subseteq> events s"
        using sets_Step by auto
    qed
    moreover
    let "?T n" = "{\<omega>\<in>(\<Pi>\<^isub>E i\<in>{..<n}. S). (s = sx \<longrightarrow> (if n = 0 then sx \<noteq> tx else \<omega> 0 \<noteq> tx)) \<and> (\<forall>i<n::nat. \<omega> i \<noteq> sx) }"
    let "?P n \<omega>" = "{\<omega>' \<in> UNIV \<rightarrow> S. \<forall>i\<le>n::nat. \<omega>' i = (if i = n then sx else \<omega> i)}"
    { fix n
      have "Step s n \<subseteq> UNIV \<rightarrow> S" by (auto simp: Step_def)
      then have "Step s n = (\<Union>\<omega>'\<in>(\<Pi>\<^isub>E i\<in>{..<n}. S). Step s n \<inter> {\<omega>\<in>UNIV\<rightarrow>S. \<forall>i<n. \<omega> i = \<omega>' i})"
        (is "_ = UNION ?I ?S")
        apply (auto simp: subset_eq)
        apply (rule_tac x="restrict x {..<n}" in bexI)
        apply auto
        done
      moreover have "prob s (UNION ?I ?S) = (\<Sum>\<omega>\<in>?I. prob s (?S \<omega>))"
      proof (rule finite_measure_finite_Union)
        show "finite ?I" by auto
        show "\<And>\<omega>. ?S \<omega> \<in> events s"
          by (auto intro: in_path_space' sets_Step)
        show "disjoint_family_on ?S ?I"
        proof (unfold disjoint_family_on_def, intro ballI impI)
          fix \<omega>1 \<omega>2 assume *: "\<omega>1 \<in> ?I" "\<omega>2 \<in> ?I"
          assume "\<omega>1 \<noteq> \<omega>2"
          then obtain i where neq: "\<omega>1 i \<noteq> \<omega>2 i" by auto
          with * have "i < n"
            by (force simp: extensional_def)
          with neq show "?S \<omega>1 \<inter> ?S \<omega>2 = {}" by auto
        qed
      qed
      moreover
      { fix \<omega> assume "\<omega> \<in> ?I" and \<omega>: "\<forall>i<n. \<omega> i \<noteq> sx" "s = sx \<Longrightarrow> (n = 0 \<longrightarrow> sx \<noteq> tx) \<and> (n \<noteq> 0 \<longrightarrow> \<omega> 0 \<noteq> tx)"
        let "?\<omega> i" = "if i = n then sx else \<omega> i"

        (* BAD PROOF *)
        have "?S \<omega> = {\<omega>'\<in>UNIV\<rightarrow>S. (\<forall>i<n. \<omega>' i = \<omega> i) \<and> \<omega>' n = sx} \<inter> ((\<lambda>\<omega> i. \<omega> (i + Suc n)) -` Never sx \<inter> (UNIV \<rightarrow> S))"
        proof (intro set_eqI iffI CollectI IntI conjI)
          fix \<omega>' assume "\<omega>' \<in> ?S \<omega>"
          then have "\<omega>' n = sx" "\<omega>' \<in> Step s n" "\<And>i. i < n \<Longrightarrow> \<omega>' i = \<omega> i"
            and \<omega>': "\<omega>' \<in> Never s"
            by (auto simp: Step_def)
          then show "\<omega>' n = sx" by simp
          show "\<omega>' \<in> (\<lambda>\<omega> i. \<omega> (i + Suc n)) -` Never sx"
          proof (simp add: Never_def, intro conjI allI impI)
            show "(\<lambda>i. \<omega>' (Suc (i + n))) \<in> UNIV \<rightarrow> S"
              using \<omega>' by (auto simp: Never_def)
          next
            fix i
            from \<omega>' obtain j where "j \<ge> i + Suc n" "nat_case s \<omega>' j = sx"
              unfolding Never_def by simp blast
            then show "\<exists>j\<ge>i. nat_case sx (\<lambda>i. \<omega>' (Suc (i + n))) j = sx"
              by (auto intro!: exI[of _ "j - Suc n"] split: nat.split simp: le_imp_diff_is_add)
            assume eq: "nat_case sx (\<lambda>i. \<omega>' (Suc (i + n))) i = sx"
            moreover from \<omega>'
            have *: "nat_case s \<omega>' (Suc (i + n)) = sx \<longrightarrow> \<omega>' (Suc (i + n)) \<noteq> tx"
              unfolding Never_def by blast
            show "\<omega>' (Suc (i + n)) \<noteq> tx"
            proof (cases i)
              case 0 with * `\<omega>' \<in> Step s n` show ?thesis
                by (simp add: Step_def)
            next
              case (Suc n') with * eq show ?thesis
                by (simp split: nat.split_asm)
            qed
          qed
        next
          fix \<omega>' assume "\<omega>' \<in> {\<omega>'\<in>UNIV\<rightarrow>S. (\<forall>i<n. \<omega>' i = \<omega> i) \<and> \<omega>' n = sx} \<inter> ((\<lambda>\<omega> i. \<omega> (i + Suc n)) -` Never sx \<inter> (UNIV \<rightarrow> S))"
          then have \<omega>': "\<And>i. i < n \<Longrightarrow> \<omega>' i = \<omega> i" "\<omega>' n = sx" "(\<lambda>i. \<omega>' (i + Suc n)) \<in> Never sx" "\<omega>' \<in> UNIV\<rightarrow>S"
            by auto
          show "\<omega>' \<in> Step s n"
            unfolding Step_def
          proof (intro IntI CollectI conjI impI allI)
            show "\<omega>' \<in> Never s"
              unfolding Never_def
            proof (intro CollectI conjI allI impI)
              fix i
              from \<omega>' obtain j where "j \<ge> i" "nat_case sx (\<lambda>i. \<omega>' (i + Suc n)) j = sx"
                unfolding Never_def by blast
              then show "\<exists>j\<ge>i. nat_case s \<omega>' j = sx"
                using `\<omega>' n = sx`
                apply (auto intro!: exI[of _ "j + Suc n"])
                apply (cases j)
                apply auto
                done
              assume *: "nat_case s \<omega>' i = sx"
              show "\<omega>' i \<noteq> tx"
              proof (cases i)
                case 0 with * \<omega>' \<omega> show ?thesis by (cases "n = 0") simp_all
              next
                case (Suc j)
                show ?thesis
                proof cases
                  assume "j < n"
                  with * \<omega> \<omega>'(1)
                  show ?thesis by (simp add: Suc)
                next
                  assume "\<not> j < n"
                  then have "n \<le> j" by auto
                  with * \<omega>'(3)
                  show ?thesis
                    apply (simp add: Never_def Suc)
                    apply (elim conjE)
                    apply (elim allE[of _ "j - n"])
                    apply simp
                    apply (cases "j - n")
                    apply simp
                    apply (simp add: le_imp_diff_is_add)
                    done
                qed
              qed
            qed (insert \<omega>', auto)
            from \<omega>' \<omega> show "\<omega>' \<in> UNIV \<rightarrow> S" "\<And>i. i < n \<Longrightarrow> \<omega>' i \<noteq> sx" "\<omega>' n = sx"
              by auto
          qed
        qed auto
        then have S: "?S \<omega> = {\<omega>'\<in>UNIV\<rightarrow>S. (\<forall>i<Suc n. \<omega>' i = ?\<omega> i)} \<inter> ((\<lambda>\<omega> i. \<omega> (i + Suc n)) -` Never sx \<inter> (UNIV \<rightarrow> S))"
          by auto
        have "prob s (?S \<omega>) = (\<Prod>i<Suc n. \<tau> (nat_case s ?\<omega> i) (?\<omega> i)) *
          prob (case Suc n of 0 \<Rightarrow> s | Suc i \<Rightarrow> ?\<omega> i) (Never sx)"
          unfolding S
          apply (rule prob_shifted_eq)
          using `s \<in> S` `\<omega> \<in> ?I` `sx \<in> S` sets_Never
          apply auto
          done
        also have "\<dots> = (\<Prod>i<Suc n. \<tau> (nat_case s ?\<omega> i) (?\<omega> i)) * prob sx (Never sx)"
          by simp
        also have "\<dots> = prob s {\<omega>' \<in> UNIV \<rightarrow> S. \<forall>i\<le>n. \<omega>' i = ?\<omega> i} * prob sx (Never sx)"
          using `s \<in> S` `\<omega> \<in> ?I` `sx \<in> S`
          by (subst prob_generator_le)
            (auto simp: lessThan_Suc_atMost)
        finally have "prob s (?S \<omega>) = prob s {\<omega>' \<in> UNIV \<rightarrow> S. \<forall>i\<le>n. \<omega>' i = ?\<omega> i} * prob sx (Never sx)" .}
      note * = this
      have "(\<Sum>\<omega>\<in>?I. prob s (?S \<omega>)) = (\<Sum>\<omega>\<in>?T n. prob s (?P n \<omega>) * prob sx (Never sx))"
      proof (rule setsum_mono_zero_cong_right)
        show "\<forall>\<omega>'\<in>?I - ?T n. prob s (?S \<omega>') = 0"
        proof (intro ballI)
          fix \<omega> assume *: "\<omega> \<in> ?I - ?T n"
          then have "\<omega> \<in> ?I" and cases: "s = sx \<and> (n = 0 \<and> sx = tx \<or> n \<noteq> 0 \<and> \<omega> 0 = tx) \<or> (\<exists>i<n. \<omega> i = sx)"
            by (simp_all split: split_if_asm)
          from cases have "?S \<omega> = {}"
            unfolding Step_def Never_def by (auto split: nat.split_asm)
          then show "prob s (?S \<omega>) = 0" by simp
        qed
        fix \<omega> assume "\<omega> \<in> ?T n" with * show "prob s (?S \<omega>) = prob s (?P n \<omega>) * prob sx (Never sx)"
          by auto
      qed auto
      ultimately have "prob s (Step s n) = (\<Sum>\<omega>\<in>?T n. prob s (?P n \<omega>)) * prob sx (Never sx)"
        by (simp add: setsum_left_distrib)
      also have "(\<Sum>\<omega>\<in>?T n. prob s (?P n \<omega>)) = prob s (\<Union>\<omega>\<in>?T n. ?P n \<omega>)"
      proof (rule finite_measure_finite_Union[symmetric])
        show "disjoint_family_on (?P n) (?T n)"
        proof (unfold disjoint_family_on_def, intro ballI impI)
          fix \<omega>1 \<omega>2 assume *: "\<omega>1 \<in> ?T n" "\<omega>2 \<in> ?T n"
          assume "\<omega>1 \<noteq> \<omega>2" then obtain i where i: "\<omega>1 i \<noteq> \<omega>2 i" by auto
          with * have "i < n" by (rule_tac ccontr) (auto simp: extensional_def)
          with i show "?P n \<omega>1 \<inter> ?P n \<omega>2 = {}" by auto
        qed
        show "finite (?T n)"
          by (rule finite_subset[OF _  finite_PiE[of "{..<n}" "\<lambda>_. S"]]) auto
      qed (rule in_path_space)
      finally have "prob s (Step s n) = prob s (UNION (?T n) (?P n)) * prob sx (Never sx)" . }
    ultimately have sums_Never: "(\<lambda>n. prob s (UNION (?T n) (?P n)) * prob sx (Never sx)) sums (prob s (Never s))"
      by simp

    have alt: "(\<lambda>n. prob s (UNION (?T n) (?P n))) sums (prob s (\<Union>n. UNION (?T n) (?P n)))"
    proof (rule finite_measure_UNION)
      show "range (\<lambda>n. UNION (?T n) (?P n)) \<subseteq> events s"
      proof (safe intro!: finite_UN in_path_space)
        fix n show "finite (?T n)"
          by (rule finite_subset[OF _  finite_PiE[of "{..<n}" "\<lambda>_. S"]]) auto
      qed
      def U \<equiv> "\<lambda>n. UNION (?T n) (?P n)"
      then have "\<And>m n \<omega>. m < n \<Longrightarrow> \<omega> \<in> U n \<Longrightarrow> \<omega> \<notin> U m" by auto
      then show "disjoint_family (\<lambda>n. UNION (?T n) (?P n))"
        unfolding U_def[symmetric] by (auto simp: disjoint_family_on_def neq_iff)
    qed

    have Never_eq_0: "prob s (Never s) \<le> (if s = sx then (1 - c) * prob sx (Never sx) else prob sx (Never sx))"
    proof cases
      assume "prob sx (Never sx) = 0"
      with sums_Never show ?thesis by (simp add: sums_iff)
    next
      assume neq_0: "prob sx (Never sx) \<noteq> 0"
      moreover note sums_divide[OF sums_Never, of "prob sx (Never sx)"]
      ultimately have "(\<lambda>n. prob s (UNION (?T n) (?P n))) sums (prob s (Never s) / prob sx (Never sx))"
        by simp
      with alt have "prob s (Never s) / prob sx (Never sx) = prob s (\<Union>n. UNION (?T n) (?P n))"
        by (simp add: sums_iff)
      also have "\<dots> \<le> (if s = sx then prob s {\<omega>\<in>UNIV\<rightarrow>S. \<omega> 0 \<in> S - {tx}} else 1)"
      proof (split split_if, intro conjI impI finite_measure_mono in_path_space_in_single subsetI)
        fix \<omega> assume \<omega>: "\<omega> \<in> (\<Union>n. UNION (?T n) (?P n))" "s = sx"
        then obtain \<omega>' n where n: "\<omega>' \<in> ?T n" "\<omega> \<in> ?P n \<omega>'" by auto
        have "\<omega> 0 \<in> S - {tx}"
          using n `s = sx` `sx \<in> S` by (cases "n = 0") (auto simp: Pi_iff)
        with \<omega> show "\<omega> \<in> {\<omega>\<in>UNIV\<rightarrow>S. \<omega> 0 \<in> S - {tx}}" by simp
      qed simp
      also have "\<dots> = (if s = sx then (setsum (\<tau> s) (S-{tx})) else 1)"
        using `sx \<in> S` by (simp add: prob_single_eq_sum Diff_subset del: Diff_iff)
      also have "\<dots> \<le> (if s = sx then (1 - c) else 1)"
        using `tx \<in> S` `sx \<in> S` `\<tau> sx tx \<noteq> 0` by (simp add: setsum_diff \<tau>_distr c)
      finally show ?thesis using neq_0
        by (auto simp add: pos_divide_le_eq less_le)
    qed }
  note Never_bounded = this
    
  { fix s assume "s \<in> S"
    from Never_bounded[OF `sx \<in> S`]
    have "prob sx (Never sx) = 0"
      using `0 < c` positive_measure'[of sx "Never sx"]
      by (simp add: field_simps mult_le_0_iff del: positive_measure')
    with Never_bounded[OF `s \<in> S`] positive_measure'[of s "Never s"]
    have "prob s (Never s) = 0"
      by (simp split: split_if_asm del: positive_measure') }
  note Never_eq_0 = this

  have sets_Fair: "{\<omega>\<in>UNIV\<rightarrow>S. Fair sx tx (nat_case s \<omega>) } \<in> events s"
    unfolding Fair_def by (auto intro!: sets_Collect[unfolded space_path_space] sets_nat_case)
  have sets_sN: "\<And>n. {\<omega>\<in>UNIV\<rightarrow>S. nat_case s \<omega> n = sx} \<inter> ((\<lambda>\<omega> i. \<omega> (i + n)) -` Never sx \<inter> space (path_space s)) \<in> events s"
    (is "\<And>n. ?sN n \<in> _")
    by (auto intro!: countable_UN sets_nat_case Int[OF _ measurable_sets] measurable_shift sets_Never)

  { fix n
    have "prob s (?sN n) = 0"
    proof (cases n)
      case 0
      show "prob s (?sN n) = 0"
      proof cases
        assume "s = sx"
        then have sN_alt: "?sN 0 = Never sx"
          by (auto split: nat.split simp: space_path_space Never_def)
        then show ?thesis
          using Never_eq_0[OF `sx \<in> S`] `s = sx` `n = 0` by simp
      next
        assume "s \<noteq> sx" with `n = 0` show ?thesis by simp
      qed
    next
      case (Suc n')
      then have sN_alt:"?sN n =
        {\<omega>\<in>UNIV\<rightarrow>S. \<forall>i<Suc n'. \<omega> i \<in> (if i < n' then S else {sx})} \<inter> ((\<lambda>\<omega> i. \<omega> (i + Suc n')) -` Never sx \<inter> space (path_space s))"
        by (auto simp: not_less less_Suc_eq)
      have "prob s (?sN n) = (\<Sum>\<omega>\<in>(\<Pi>\<^isub>E i\<in>{..<Suc n'}. if i < n' then S else {sx}). 0)"
        unfolding sN_alt using sets_Never `s \<in> S` `sx \<in> S` Never_eq_0[of sx]
        by (subst prob_shifted_sets_eq)
           (auto intro!: setsum_cong simp del: setsum_0 setsum_constant
                 simp: Pi_iff split: split_if_asm)
      then show ?thesis by simp
    qed }
  with sets_sN have "AE \<omega> in path_space s. \<forall>n. \<omega> \<notin> ?sN n"
    unfolding AE_all_countable
    by (intro allI AE_not_in) (auto simp: finite_measure_eq)
  then show "AE \<omega> in path_space s. Fair sx tx (nat_case s \<omega>)"
  proof (elim AE_mp, safe intro!: AE_I2)
    fix \<omega> assume \<omega>: "\<omega> \<in> space (path_space s)" "\<forall>n. \<omega> \<notin> ?sN n"
    show "Fair sx tx (nat_case s \<omega>)"
      unfolding Fair_def
    proof (safe, simp)
      fix i assume i: "\<forall>j. \<exists>i\<ge>j. nat_case s \<omega> i = sx"
      then obtain n where n: "i \<le> n" "nat_case s \<omega> n = sx" by auto
      with \<omega> have "(\<lambda>i. \<omega> (i + n)) \<notin> Never sx"
        by (auto simp: space_path_space)
      with \<omega>(1) obtain k where "(\<forall>j\<ge>k. nat_case sx (\<lambda>i. \<omega> (i + n)) j \<noteq> sx) \<or>
        (nat_case sx (\<lambda>i. \<omega> (i + n)) k = sx \<and> \<omega> (k + n) = tx)"
        by (auto simp: Never_def space_path_space)
      then show "\<exists>j\<ge>i. nat_case s \<omega> j = sx \<and> \<omega> j = tx"
      proof
        assume *: "\<forall>j\<ge>k. nat_case sx (\<lambda>i. \<omega> (i + n)) j \<noteq> sx"
        from i obtain k' where "k + n \<le> k'" "nat_case s \<omega> k' = sx"
          by blast
        with *[THEN spec, of "k' - n"] show ?thesis
          by (auto split: nat.split_asm simp: le_imp_diff_is_add)
      next
        assume "nat_case sx (\<lambda>i. \<omega> (i + n)) k = sx \<and> \<omega> (k + n) = tx"
        with n show ?thesis
          by (intro exI[of _ "k + n"])
             (simp split: nat.split_asm add: le_imp_diff_is_add)
      qed
    qed
  qed
qed

lemma fair_implies_reachable_eq_inf:
  fixes s \<omega>
  assumes s: "s \<in> S"  "\<forall>i. \<exists>j\<ge>i. \<omega> j = s"
  assumes fair: "\<forall>sx\<in>S. \<forall>tx\<in>S. \<tau> sx tx \<noteq> 0 \<longrightarrow> Fair sx tx \<omega>"
  assumes \<omega>: "\<forall>i. \<omega> i \<in> S" "\<forall>i. \<tau> (\<omega> i) (\<omega> (Suc i)) \<noteq> 0"
  shows "reachable S s = {t. \<forall>i. \<exists>j\<ge>i. \<omega> j = t}"
proof (intro set_eqI iffI CollectI)
  fix t assume t: "t \<in> {t. \<forall>i. \<exists>j\<ge>i. \<omega> j = t}"
  from s obtain n_s where n_s: "s = \<omega> n_s" by auto
  from t obtain n_t where n_t: "Suc n_s \<le> n_t" "t = \<omega> n_t" by auto
  show "t \<in> reachable S s" unfolding n_t n_s
  proof (simp add: reachable_def, safe)
    show "\<omega> n_t \<in> S" using \<omega> by auto
    show "\<exists>\<omega>' n. (\<forall>i\<le>n. \<tau> (nat_case (\<omega> n_s) \<omega>' i) (\<omega>' i) \<noteq> 0) \<and> (\<forall>i<n. \<omega>' i \<in> S) \<and> \<omega>' n = \<omega> n_t"
      using `Suc n_s \<le> n_t` \<omega>
      by (intro exI[of _ "\<lambda>i. \<omega> (Suc (i + n_s))"] exI[of _ "n_t - n_s - 1"])
         (auto split: nat.split)
  qed
next
  fix t i assume "t \<in> reachable S s"
  from reachableE[OF this] guess \<omega>' n' . note \<omega>' = this
  from \<omega>' have "nat_case s \<omega>' (Suc n') = t" by auto
  from smallest[where P="\<lambda>i. nat_case s \<omega>' i = t", OF this] guess n . note n = this
  note n(1,2)
  moreover
  { fix i assume "i < n"
    have "\<omega>' i \<in> S"
    proof cases
      assume "i = n'" with \<omega>'(1,4) show ?thesis by simp
    next
      assume "i \<noteq> n'" with `i < n` `n \<le> Suc n'` \<omega>'(3)[rule_format, of i]
      show "\<omega>' i \<in> S" by simp
    qed }
  moreover have "t \<in> S" by fact
  moreover
  { fix i assume "i < n"
    then have "\<tau> (nat_case s \<omega>' i) (\<omega>' i) \<noteq> 0"
      using \<omega>'(2)[rule_format, of i] `n \<le> Suc n'` by auto }
  ultimately show "\<forall>i. \<exists>j\<ge>i. \<omega> j = t"
  proof (induct n arbitrary: t rule: less_induct)
    case (less n)
    show ?case
    proof (cases n)
      case 0 with less s show ?thesis by simp
    next
      case (Suc n')
      def s' \<equiv> "nat_case s \<omega>' n'"
      then have "\<tau> s' t \<noteq> 0"
        using less.prems(1)[symmetric] Suc less.prems(5)[of n'] by auto
      moreover have "s' \<in> S"
        unfolding s'_def using `s \<in> S` less.prems(3) Suc
        by (auto split: nat.split)
      moreover note `t \<in> S` fair
      ultimately have "Fair s' t \<omega>" by auto
      from Suc less.prems have "s' \<noteq> t" by (simp add: s'_def)
      have "nat_case s \<omega>' n' = s'" unfolding s'_def by auto
      from smallest[where P="\<lambda>n. nat_case s \<omega>' n = s'", OF this]
      guess n'' . note n'' = this
      have "nat_case s \<omega>' n'' \<in> S"
        using n''(3) Suc less.prems(3) `s \<in> S` by (auto split: nat.split)
      with n'' Suc less.prems have H: "\<forall>i. \<exists>j\<ge>i. \<omega> j = s'"
        by (intro less.hyps) auto
      from `Fair s' t \<omega>`
      show ?thesis
        unfolding Fair_def
      proof
        assume "\<exists>i. \<forall>j\<ge>i. \<omega> j \<noteq> s'" with H show ?thesis by auto
      next
        assume *: "\<forall>i. \<exists>j\<ge>i. \<omega> j= s' \<and> \<omega> (Suc j) = t"
        show ?thesis
        proof
          fix i
          from * obtain j where "i \<le> j" "\<omega> (Suc j) = t" by auto
          then show "\<exists>j\<ge>i. \<omega> j = t" by (auto intro!: exI[of _ "Suc j"])
        qed
      qed
    qed
  qed
qed

lemma AE_until:
  assumes s: "s \<in> \<Phi>" "\<Phi> \<subseteq> S" and closed: "reachable (\<Phi> - \<Psi>) s \<subseteq> \<Phi> \<union> \<Psi>"
  assumes enabled: "\<forall>t\<in>reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>. reachable (\<Phi> - \<Psi>) t \<inter> \<Psi> \<noteq> {}"
  shows "AE \<omega> in path_space s. nat_case s \<omega> \<in> until \<Phi> \<Psi>"
using AE_Fair[OF set_rev_mp[OF s]] AE_\<tau>_not_zero[OF set_rev_mp[OF s]]
proof (elim AE_mp, intro AE_I2 impI)
  fix \<omega> assume \<omega>: "\<omega> \<in> space (path_space s)"
    and possible: "\<forall>i. \<tau> (nat_case s \<omega> i) (\<omega> i) \<noteq> 0"
    and Fair: "\<forall>sx\<in>S. \<forall>tx\<in>S. \<tau> sx tx \<noteq> 0 \<longrightarrow> Fair sx tx (nat_case s \<omega>)"

  have "s \<in> S" "\<Phi> - \<Psi> \<subseteq> S" using s by auto

  show "nat_case s \<omega> \<in> until \<Phi> \<Psi>"
  proof cases
    assume "\<exists>t\<in>reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>. \<forall>i. \<exists>j\<ge>i. nat_case s \<omega> j = t"
    then obtain t where t: "t \<in> reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>" "\<forall>i. \<exists>j\<ge>i. nat_case s \<omega> j = t" by auto
    with enabled `s \<in> S` have *: "reachable (\<Phi> - \<Psi>) t \<inter> \<Psi> \<noteq> {}" by auto
    then obtain t' where "t' \<in> \<Psi>" "t' \<in> reachable (\<Phi> - \<Psi>) t"
      by (auto simp: set_eq_iff)
    with reachable_mono[OF `\<Phi> - \<Psi> \<subseteq> S`] have t': "t' \<in> reachable S t"
      by auto

    from t `s \<in> S` have "t \<in> S" by (auto simp: reachable_def)

    from possible \<omega> have "\<forall>i. nat_case s \<omega> i \<in> S" "\<forall>i. \<tau> (nat_case s \<omega> i) (nat_case s \<omega> (Suc i)) \<noteq> 0"
      using `s \<in> S` by (auto simp: space_path_space)
    from fair_implies_reachable_eq_inf[OF `t \<in> S` t(2) Fair this] t'
    have "\<forall>i. \<exists>j\<ge>i. nat_case s \<omega> j = t'"
      by auto
    then obtain i where "nat_case s \<omega> i = t'" by auto
    with `t' \<in> \<Psi>` have "nat_case s \<omega> i \<in> \<Psi>" by auto
    from smallest[where P="\<lambda>i. nat_case s \<omega> i \<in> \<Psi>", OF this]
    guess i . note i = this

    show "nat_case s \<omega> \<in> until \<Phi> \<Psi>"
    proof (rule untilI[of _ i])
      show "nat_case s \<omega> \<in> UNIV\<rightarrow>S"
        using \<omega> `s \<in> S` by (auto simp: space_path_space)
    next
      fix j :: nat assume "j < i"
      with i have not_\<Psi>: "nat_case s \<omega> j \<notin> \<Psi>" by auto
      show "nat_case s \<omega> j \<in> \<Phi>"
      proof (rule ccontr)
        assume contr: "nat_case s \<omega> j \<notin> \<Phi>"
        from smallest[where P="\<lambda>j. nat_case s \<omega> j \<notin> \<Phi>", OF this]
        guess k . note k = this

        show False
        proof (cases k)
          case 0 with k `s \<in> \<Phi>` show False by auto
        next
          case (Suc k')
          have "nat_case s \<omega> k \<in> reachable (\<Phi> - \<Psi>) s"
          proof (unfold reachable_def, safe intro!: exI[of _ \<omega>] exI[of _ k'] del: notI)
            show "nat_case s \<omega> k \<in> S"
              using \<omega> Suc by (simp add: space_path_space Pi_iff)
          next
            fix i' assume "i' < k'"
            then show "\<omega> i' \<in> \<Phi>"
              using k(2)[of "Suc i'"] Suc by simp
            with `i' < k'` show "\<omega> i' \<notin> \<Psi>"
              using k(3) `j < i` Suc i(2)[of "Suc i'"] by simp
          next
            fix i from possible show "\<tau> (nat_case s \<omega> i) (\<omega> i) \<noteq> 0"
              by simp
          qed (simp add: Suc)
          with closed k(1,3) `j < i` i(2)[of k]
          show False by auto
        qed
      qed
    qed fact
  next
    assume "\<not>(\<exists>t\<in>reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>. \<forall>i. \<exists>j\<ge>i. nat_case s \<omega> j = t)"
    then have "\<forall>t\<in>reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>. \<exists>i. \<forall>j\<ge>i. nat_case s \<omega> j \<noteq> t"
      by blast
    from bchoice[OF this] guess I .. note I = this

    def R \<equiv> "{n. nat_case s \<omega> n \<in> reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi> \<and> (\<forall>i\<le>n. nat_case s \<omega> i \<in> \<Phi> - \<Psi>) }"

    have "\<forall>i\<in>R. i \<le> Max (I ` (reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>))"
    proof
      fix i assume "i \<in> R"
      then have *: "nat_case s \<omega> i \<in> reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>"
        unfolding R_def by auto
      then have "i < I (nat_case s \<omega> i)"
        using I[rule_format, of "nat_case s \<omega> i" i]
        by (auto simp: not_le[symmetric])
      also have "\<dots> \<le> Max (I ` (reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>))"
        using * by (auto intro!: Max_ge)
      finally show "i \<le> Max (I ` (reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>))"
        by auto
    qed
    then have "R \<subseteq> {..Max (I ` (reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>))}"
      by auto
    then have "finite R" by (auto dest: finite_subset)
    
    show ?thesis
    proof cases
      assume "s \<in> \<Psi>" with `s \<in> \<Phi>` \<omega> `s \<in> S` show ?thesis
        by (auto simp: until_def space_path_space)
    next
      assume "s \<notin> \<Psi>"
      with `s \<in> \<Phi>` have "0 \<in> R" unfolding R_def by auto
      then have "R \<noteq> {}" by auto
      have in_R: "\<forall>i\<le>Max R. nat_case s \<omega> i \<in> \<Phi> - \<Psi>"
        unfolding Max_ge_iff[OF `finite R` `R \<noteq> {}`]
        by (auto simp: R_def)

      show ?thesis
      proof cases
        assume "nat_case s \<omega> (Suc (Max R)) \<in> \<Psi>"
        show "nat_case s \<omega> \<in> until \<Phi> \<Psi>"
        proof (rule untilI2)
          fix i assume "i < Suc (Max R)"
          then show "nat_case s \<omega> i \<in> \<Phi> \<union> \<Psi>"
            using Max_ge_iff[OF `finite R` `R \<noteq> {}`, of "Max R"]
            apply simp
            apply (subst (asm) (2) R_def)
            apply auto
            done
        next
          show "nat_case s \<omega> (Suc (Max R)) \<in> \<Psi>" by fact
        next
          show "nat_case s \<omega> \<in> UNIV \<rightarrow> S"
            using `s \<in> S` \<omega> by (auto simp add: space_path_space)
        qed
      next
        assume not_\<Psi>: "nat_case s \<omega> (Suc (Max R)) \<notin> \<Psi>"
        have Max_R1: "nat_case s \<omega> (Suc (Max R)) \<in> reachable (\<Phi> - \<Psi>) s"
        proof (unfold reachable_def, safe intro!: exI[of _ \<omega>] exI[of _ "Max R"] del: notI)
          fix i show "\<tau> (nat_case s \<omega> i) (\<omega> i) \<noteq> 0"
            using possible by auto
        next
          fix i assume "i < Max R"
          then have "Suc i \<le> Max R" by auto
          with in_R show "\<omega> i \<in> \<Phi>" "\<omega> i \<notin> \<Psi>" by auto
        next
          show "nat_case s \<omega> (Suc (Max R)) \<in> S"
            using `s \<in> S` \<omega> by (auto simp add: space_path_space)
        qed simp
        moreover
        from Max_ge_iff[OF `finite R` `R \<noteq> {}`, of "Suc (Max R)"]
        have "Suc (Max R) \<notin> R" by auto
        ultimately have "\<exists>i\<le>Suc (Max R). nat_case s \<omega> i \<notin> \<Phi> - \<Psi>"
          using not_\<Psi> by (subst (asm) (3) R_def) simp
        moreover
        from Max_in[OF `finite R` `R \<noteq> {}`] 
        have "\<forall>i\<le>Max R. nat_case s \<omega> i \<in> \<Phi> - \<Psi>"
          by (subst (asm) (2) R_def) simp
        ultimately have Max_R2: "nat_case s \<omega> (Suc (Max R)) \<notin> \<Phi> - \<Psi>"
          by (auto simp add: le_Suc_eq)

        from not_\<Psi> Max_R1 Max_R2 closed
        show ?thesis by auto
      qed
    qed
  qed
qed

lemma first_in_until[simp]:
  "\<Psi> \<subseteq> S \<Longrightarrow> s \<in> \<Psi> \<Longrightarrow> \<omega> \<in> UNIV\<rightarrow>S \<Longrightarrow> nat_case s \<omega> \<in> until \<Phi> \<Psi>"
  by (auto simp: until_def Pi_iff split: nat.split)

lemma next_in_until[simp]:
  "\<Phi> \<subseteq> S \<Longrightarrow> s \<in> \<Phi> \<Longrightarrow> s \<notin> \<Psi> \<Longrightarrow> nat_case s \<omega> \<in> until \<Phi> \<Psi> \<longleftrightarrow> \<omega> \<in> until \<Phi> \<Psi>"
  by (auto simp: until_def Pi_iff gr0_conv_Suc split: nat.split) blast

lemma never_in_until[simp]:
  "s \<notin> \<Psi> \<Longrightarrow> s \<notin> \<Phi> \<Longrightarrow> nat_case s \<omega> \<notin> until \<Phi> \<Psi>"
  by (auto simp: until_def Pi_iff split: nat.split)

lemma reachable_in_subpath:
  assumes "i < n" "\<omega> n \<in> S"
  assumes \<tau>: "\<And>j. i \<le> j \<Longrightarrow> j < n \<Longrightarrow> \<tau> (\<omega> j) (\<omega> (Suc j)) \<noteq> 0"
  assumes \<Phi>: "\<And>j. i < j \<Longrightarrow> j < n \<Longrightarrow> \<omega> j \<in> \<Phi>"
  shows "\<omega> n \<in> reachable \<Phi> (\<omega> i)"
proof -
  have "\<omega> (Suc i + (n - i - 1)) \<in> reachable \<Phi> (\<omega> i)"
    using assms
    by (intro reachable_in[of "\<lambda>j. \<omega> (Suc i + j)"]) (auto split: nat.split)
  with `i < n` show ?thesis by simp
qed

lemma until_eq_1_if_reachable:
  fixes s \<Phi> \<Psi>
  assumes in_S: "s \<in> S" "\<Phi> \<subseteq> S" "\<Psi> \<subseteq> S"
  shows "(AE \<omega> in path_space s. nat_case s \<omega> \<in> until \<Phi> \<Psi>) \<longleftrightarrow>
    s \<in> \<Psi> \<or> (s \<in> \<Phi> \<and> reachable (\<Phi> - \<Psi>) s \<subseteq> \<Phi> \<union> \<Psi> \<and> (\<forall>t\<in>reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>. reachable (\<Phi> - \<Psi>) t \<inter> \<Psi> \<noteq> {}))"
proof safe
  assume "s \<in> \<Phi>" "reachable (\<Phi> - \<Psi>) s \<subseteq> \<Phi> \<union> \<Psi>"
    "\<forall>t\<in>reachable (\<Phi> - \<Psi>) s \<union> {s} - \<Psi>. reachable (\<Phi> - \<Psi>) t \<inter> \<Psi> \<noteq> {}"
  with in_S show "AE \<omega> in path_space s. nat_case s \<omega> \<in> until \<Phi> \<Psi>"
    by (intro AE_until) auto
next
  assume "s \<in> \<Psi>" with in_S show "AE \<omega> in path_space s. nat_case s \<omega> \<in> until \<Phi> \<Psi>"
    by (auto simp: space_path_space[symmetric, of s])
next
  assume 1: "AE \<omega> in path_space s. nat_case s \<omega> \<in> until \<Phi> \<Psi>" "s \<notin> \<Psi>"
  show "s \<in> \<Phi>"
  proof (rule ccontr)
    assume "s \<notin> \<Phi>" with 1 show False by (simp add: AE_False)
  qed

  fix s' assume "s' \<notin> \<Psi>" "s' \<in> reachable (\<Phi> - \<Psi>) s"
  then obtain \<omega> n where \<omega>: "\<forall>i<n. \<omega> i \<in> \<Phi> - \<Psi>" "\<forall>i\<le>n. \<tau> (nat_case s \<omega> i) (\<omega> i) \<noteq> 0" "\<omega> n = s'" "s' \<in> S"
    by (auto elim: reachableE)
  with in_S have P_neq_0: "prob s {\<omega>' \<in> UNIV \<rightarrow> S. \<forall>i\<le>n. \<omega>' i = \<omega> i} \<noteq> 0"
    by (subst prob_generator_le) (auto simp: le_less[where 'a=nat])
 
  show "s' \<in> \<Phi>"
  proof (rule ccontr)
    assume "s' \<notin> \<Phi>"
 
    { fix \<omega>' assume eq: "\<forall>i\<le>n. \<omega>' i = \<omega> i"
      assume "nat_case s \<omega>' \<in> until \<Phi> \<Psi>"
      then have "\<omega>' \<in> until \<Phi> \<Psi>" using `s \<in> \<Phi>` `s \<notin> \<Psi>` in_S by simp
      then obtain n' where n': "\<And>i. i < n' \<Longrightarrow> \<omega>' i \<in> \<Phi> - \<Psi>" "\<omega>' n' \<in> \<Psi>" "\<omega>' \<in> UNIV \<rightarrow> S"
        by (auto elim!: untilE2)
      have "n' \<le> n" unfolding not_less[symmetric]
        using n'(1)[of n] \<omega> `s' \<notin> \<Phi>` eq by auto
      then have False
        using n' eq `s' \<notin> \<Psi>` `\<omega> n = s'` \<omega>(1)[THEN spec, of n'] by auto }
    note \<omega>'_notin_until = this
 
    have "prob s {\<omega>' \<in> UNIV \<rightarrow> S. \<forall>i\<le>n. \<omega>' i = \<omega> i} = prob s {}"
    proof (rule finite_measure_eq_AE)
      show "AE x in path_space s. (x \<in> {\<omega>' \<in> UNIV \<rightarrow> S. \<forall>i\<le>n. \<omega>' i = \<omega> i}) = (x \<in> {})"
        using 1 \<omega>'_notin_until by (elim AE_mp) (auto intro!: AE_I2)
    qed (auto intro: in_path_space)
    with P_neq_0 show False by auto
  qed

  assume not_reachable: "reachable (\<Phi> - \<Psi>) s' \<inter> \<Psi> = {}"
  have no_path: "AE \<omega>' in path_space s. \<not> (\<forall>i\<le>n. \<omega>' i = \<omega> i)"
    using 1 AE_\<tau>_not_zero[OF `s \<in> S`]
  proof (elim AE_mp, safe intro!: AE_I2, simp add: space_path_space)
    fix \<omega>' assume \<omega>': "\<omega>' \<in> UNIV \<rightarrow> S" "\<forall>i. \<tau> (nat_case s \<omega>' i) (\<omega>' i) \<noteq> 0"
    assume "nat_case s \<omega>' \<in> until \<Phi> \<Psi>" and eq: "\<forall>i\<le>n. \<omega>' i = \<omega> i"
    with `s \<in> \<Phi>` `s \<notin> \<Psi>` `\<Phi> \<subseteq> S`
    obtain m where m: "\<forall>i<m. \<omega>' i \<in> \<Phi> - \<Psi>" "\<omega>' m \<in> \<Psi>" by (auto elim: untilE2)
    have "n < m"
    proof (rule ccontr)
      assume "\<not> n < m"
      then have "m \<le> n" by simp
      then have "\<omega> m \<in> \<Psi>" using eq `\<omega>' m \<in> \<Psi>` by simp
      with `m \<le> n` \<omega>(1,3) `s' \<notin> \<Psi>` show False by (auto simp: le_less)
    qed
    with \<omega>' m have "\<omega>' m \<in> reachable (\<Phi> - \<Psi>) (\<omega>' n)"
      by (intro reachable_in_subpath) (auto split: nat.split_asm)
    with `\<omega>' m \<in> \<Psi>` `\<omega> n = s'` `s' \<notin> \<Psi>` `\<forall>i\<le>n. \<omega>' i = \<omega> i` not_reachable
    show False by auto
  qed
 
  have "prob s {\<omega>' \<in> UNIV \<rightarrow> S. \<forall>i\<le>n. \<omega>' i = \<omega> i} = prob s {}"
  proof (rule finite_measure_eq_AE)
    show "AE x in path_space s. (x \<in> {\<omega>' \<in> UNIV \<rightarrow> S. \<forall>i\<le>n. \<omega>' i = \<omega> i}) = (x \<in> {})"
      using no_path by (elim AE_mp, intro AE_I2) auto
  qed (auto intro: in_path_space)
  with P_neq_0 show False by simp
next
  assume 1: "AE \<omega> in path_space s. nat_case s \<omega> \<in> until \<Phi> \<Psi>" "s \<notin> \<Psi>"
  assume not_reachable: "reachable (\<Phi> - \<Psi>) s \<inter> \<Psi> = {}"

  have no_path: "AE \<omega>' in path_space s. False"
    using 1 AE_\<tau>_not_zero[OF `s \<in> S`]
  proof (elim AE_mp, safe intro!: AE_I2, simp add: space_path_space)
    fix \<omega>' assume \<omega>': "\<omega>' \<in> UNIV \<rightarrow> S" "\<forall>i. \<tau> (nat_case s \<omega>' i) (\<omega>' i) \<noteq> 0"
    assume *: "nat_case s \<omega>' \<in> until \<Phi> \<Psi>"
    with `s \<notin> \<Psi>` have "s \<in> \<Phi>" by (rule_tac ccontr) simp
    with * `s \<notin> \<Psi>` `\<Phi> \<subseteq> S` obtain m where
      m: "\<forall>i<m. \<omega>' i \<in> \<Phi> - \<Psi>" "\<omega>' m \<in> \<Psi>" by (auto elim: untilE2)
    with \<omega>' m `s \<in> S` `s \<notin> \<Psi>` have "\<omega>' m \<in> reachable (\<Phi> - \<Psi>) s"
      by (intro reachable_in) auto
    with `\<omega>' m \<in> \<Psi>` not_reachable show False by auto
  qed
  then show False by (simp add: AE_False)
qed

subsection {* Hitting time *}

definition hitting_time :: "'s set \<Rightarrow> (nat \<Rightarrow> 's) \<Rightarrow> nat" where 
  "hitting_time \<Phi> \<omega> = (LEAST i. \<omega> i \<in> \<Phi>)"

lemma measurable_hitting_time:
  "real_of_nat \<circ> hitting_time \<Phi> \<in> borel_measurable (path_space s)"
  unfolding borel_measurable_iff_le
proof
  fix c :: real
  show "{w \<in> space (path_space s). (of_nat \<circ> hitting_time \<Phi>) w \<le> c} \<in> events s"
  proof cases
    assume "0 \<le> c"
    have "(\<lambda>x. LEAST j. x j \<in> \<Phi>) -` {.. natfloor c} \<inter> space (path_space s) \<in> events s"
      by (rule measurable_Least) (auto simp: space_path_space)
    also have "(\<lambda>x. LEAST j. x j \<in> \<Phi>) -` {.. natfloor c} \<inter> space (path_space s) = 
      {w \<in> space (path_space s). (real \<circ> hitting_time \<Phi>) w \<le> c}"
      using `0 \<le> c` by (auto simp: hitting_time_def le_natfloor_eq not_le natfloor_neg less_imp_le)
    finally show "{w \<in> space (path_space s). (of_nat \<circ> hitting_time \<Phi>) w \<le> c} \<in> events s"
      by (simp add: real_eq_of_nat)
  next
    assume *: "\<not> 0 \<le> c"
    { fix x
      have "c < 0" using * by auto
      also have "0 \<le> real_of_nat (hitting_time \<Phi> x)" by simp
      finally have "\<not> real_of_nat (hitting_time \<Phi> x) \<le> c" by (simp add: not_le) }
    then have *: "{w \<in> space (path_space s). (of_nat \<circ> hitting_time \<Phi>) w \<le> c} = {}"
      by auto
    show "{w \<in> space (path_space s). (of_nat \<circ> hitting_time \<Phi>) w \<le> c} \<in> events s"
      unfolding * by simp
  qed
qed

lemma positive_integral_hitting_time_finite:
  assumes "s \<in> S" "\<Phi> \<subseteq> S"
  assumes until: "AE \<omega> in path_space s. nat_case s \<omega> \<in> until S \<Phi>"
  shows "(\<integral>\<^isup>+ \<omega>. real (hitting_time \<Phi> (nat_case s \<omega>)) \<partial>path_space s) \<noteq> \<infinity>"
proof cases
  assume s: "s \<in> \<Phi>"
  with `s \<in> S` have "\<And>\<omega>. hitting_time \<Phi> (nat_case s \<omega>) = 0"
    unfolding hitting_time_def by (intro Least_equality) auto
  with `s \<in> S` s show ?thesis by simp
next
  assume "s \<notin> \<Phi>"
  with `s \<in> S` have s: "s \<in> S - \<Phi>" by auto

  def n \<equiv> "Suc (card S)"
  with s have "n \<noteq> 0" by auto

  def N \<equiv> "\<lambda>s. prob s {\<omega>\<in>UNIV\<rightarrow>S. (\<forall>i<n. \<omega> i \<in> S-\<Phi>)}"
  let ?N = "{s' \<in> S. s' \<notin> \<Phi> \<and> (s' \<in> reachable (S - \<Phi>) s \<or> s' = s)}"
  def M \<equiv> "Max (N ` ?N)"
  
  have M_ge: "\<And>s'. s' \<in> S \<Longrightarrow> s' \<notin> \<Phi> \<Longrightarrow>
    (s' \<in> reachable (S - \<Phi>) s \<or> s' = s) \<Longrightarrow> N s' \<le> M"
    unfolding M_def by (auto intro!: Max_ge)
  
  have "0 \<le> N s" by (auto simp: N_def)
  also have "N s \<le> M" using s by (intro M_ge) auto
  finally have M_nneg: "0 \<le> M" by simp
    
  def T \<equiv> "\<lambda>k'::nat. {\<omega>\<in>UNIV\<rightarrow>S. (\<forall>i<k'. \<omega> i \<notin> \<Phi>)}"
  then have T_measurable[intro]: "\<And>k s. T k \<in> events s"
    by (auto intro!: sets_Collect[unfolded space_path_space])
  have T_Suc: "\<And>k s. T (n * Suc k) =
    {\<omega>'\<in>UNIV\<rightarrow>S. \<forall>i<n. \<omega>' i \<in> (S - \<Phi>)} \<inter>
    ((\<lambda>\<omega> i. \<omega> (i + n)) -` (T (n * k)) \<inter> space (path_space s))"
    apply (auto simp add: ac_simps space_path_space T_def)
    apply (case_tac "i < n")
    apply simp
    apply (erule_tac x="i - n" in allE)
    back
    apply auto
    done

  { fix s' assume s': "s' \<in> S" "s' \<notin> \<Phi>"
    assume "s' \<in> reachable (S - \<Phi>) s \<or> s' = s"
    then have until': "AE \<omega> in path_space s'. nat_case s' \<omega> \<in> until S \<Phi>"
    proof
      assume "s' = s" from until show ?thesis unfolding `s' = s` .
    next
      assume "s' \<in> reachable (S - \<Phi>) s"
      from reachableE[OF this] guess \<omega> n . note \<omega> = this
      with s' have "\<omega> n \<in> S - \<Phi>" by auto
      from \<omega>(2,3) this
      have "AE \<omega> in path_space (\<omega> n). \<omega> \<in> until S \<Phi>"
      proof (induct n)
        case 0
        have "AE \<omega> in path_space s. \<omega> \<in> until S \<Phi>"
          using until s
          by (subst until_next[symmetric, of _ s])
             (auto simp del: until_next)
        from AE_split[OF this sets_until, of "\<omega> 0"] 0 s
        show ?case
          by (simp del: vimage_eq)
      next
        case (Suc n)
        with `\<Phi> \<subseteq> S` have "AE \<omega> in path_space (\<omega> n). \<omega> \<in> until S \<Phi>"
          by (intro Suc) auto
        from AE_split[OF this sets_until, of "\<omega> (Suc n)"] Suc
        show ?case
          apply (simp del: vimage_eq)
          apply (erule_tac x="Suc n" in allE)
          apply simp
          done
      qed
      with \<omega> s' show ?thesis
        apply (subst (asm) until_next[symmetric, of _ s'])
        unfolding `\<omega> n = s'`
        apply (simp_all del: until_next)
        done
    qed

    have "\<exists>\<omega> k. k < n \<and> (\<forall>i\<le>k. \<omega> i \<in> S) \<and> (\<forall>i\<le>k. \<tau> (nat_case s' \<omega> i) (\<omega> i) \<noteq> 0) \<and> \<omega> k \<in> \<Phi>"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have *: "\<And>\<omega> k. k < n \<Longrightarrow> (\<forall>i\<le>k. \<omega> i \<in> S) \<Longrightarrow> (\<forall>i\<le>k. \<tau> (nat_case s' \<omega> i) (\<omega> i) \<noteq> 0) \<Longrightarrow> \<omega> k \<notin> \<Phi>"
        by blast
      from AE_\<tau>_not_zero[OF `s' \<in> S`] until'
      have "AE \<omega> in path_space s'. False"
      proof (elim AE_mp, intro AE_I2 impI)
        fix \<omega> assume \<omega>: "\<forall>i. \<tau> (nat_case s' \<omega> i) (\<omega> i) \<noteq> 0" and space: "\<omega> \<in> space (path_space s')"
        assume "nat_case s' \<omega> \<in> until S \<Phi>"
        from untilE2[OF this] guess n' . note n' = this
        from \<omega> path_inj[of "\<lambda>s s'. \<tau> s s' \<noteq> 0" "nat_case s' \<omega>" n']
        obtain \<omega>' k where \<omega>': "inj_on \<omega>' {..k}" "\<forall>i<k. \<tau> (\<omega>' i) (\<omega>' (Suc i)) \<noteq> 0"
          " \<omega>' ` {..<k} \<subseteq> nat_case s' \<omega> ` {..<n'}" "\<omega>' 0 = nat_case s' \<omega> 0" "\<omega>' k = nat_case s' \<omega> n'"
          by auto
        have "card {..k} = card (\<omega>' ` {..<Suc k})"
          using \<omega>'(1) by (simp add: card_image lessThan_Suc_atMost)
        also have "\<dots> \<le> card (nat_case s' \<omega> ` {..<Suc n'})"
          using \<omega>' by (intro card_mono) (auto simp: lessThan_Suc)
        also have "\<dots> < n"
          unfolding n_def less_Suc_eq_le using n' by (intro card_mono) auto
        finally have "k < n" by auto

        have "\<omega>' k \<notin> \<Phi>"
        proof (cases k)
          case 0 with \<omega>' s' show ?thesis by simp
        next
          case (Suc k')
          have "\<omega>' (Suc k') \<notin> \<Phi>"
          proof (intro allI impI *[where k="k'"])
            show "k' < n" using Suc `k < n` by simp
          next
            fix i assume "i \<le> k'"
            then have "i < k" using Suc by simp
            from \<omega>' have s'_eq: "s' = \<omega>' 0" by simp
            from \<omega>'(2)[rule_format, OF `i < k`]
            show "\<tau> (nat_case s' (\<lambda>i. \<omega>' (Suc i)) i) (\<omega>' (Suc i)) \<noteq> 0"
              unfolding s'_eq nat_case_idem by simp
          next
            fix i assume "i \<le> k'"
            then have "Suc i = k \<or> Suc i < k" by (auto simp add: Suc)
            then show "\<omega>' (Suc i) \<in> S"
              using \<omega>'(3,5) \<omega> space `s' \<in> S`
              by (auto split: nat.split simp: space_path_space)
          qed
          with Suc show ?thesis by simp
        qed
        then show False
          using \<omega>'(5) n' by simp
      qed
      then show False by (simp add: AE_False)
    qed
    then obtain \<omega> k where \<omega>: "k < n" "\<forall>i\<le>k. \<omega> i \<in> S"
      "\<forall>i\<le>k. \<tau> (nat_case s' \<omega> i) (\<omega> i) \<noteq> 0" "\<omega> k \<in> \<Phi>" by auto

    then have "0 < (\<Prod>i\<le>k. \<tau> (nat_case s' \<omega> i) (\<omega> i))"
      using s' \<omega>(2)
      by (intro setprod_pos) (auto simp: less_le intro!: \<tau>_nneg split: nat.split)
    also have "\<dots> = prob s' {\<omega>'\<in>UNIV\<rightarrow>S. \<forall>i\<le>k. \<omega>' i = \<omega> i}"
      using s' \<omega> by (simp add: prob_generator_le)
    finally have "N s' < N s' + prob s' {\<omega>'\<in>UNIV\<rightarrow>S. \<forall>i\<le>k. \<omega>' i = \<omega> i}"
      by simp
    also have "\<dots> = prob s' ({\<omega>\<in>UNIV\<rightarrow>S. (\<forall>i<n. \<omega> i \<in> S-\<Phi>)} \<union> {\<omega>'\<in>UNIV\<rightarrow>S. \<forall>i\<le>k. \<omega>' i = \<omega> i})"
      using  `k < n` `\<omega> k \<in> \<Phi>` unfolding N_def
      by (intro finite_measure_Union[symmetric])
         (auto intro!: sets_Collect[unfolded space_path_space])
    also have "\<dots> \<le> 1"
      by simp
    finally have "N s' < 1" . }
  note N_less_1 = this

  have "0 < n" using `n \<noteq> 0` by simp

  have "M < 1"
    unfolding M_def
  proof (subst Max_less_iff)
    show "finite (N`?N)" by auto
    show "N`?N \<noteq> {}" using s by auto
  next
    show "\<forall>n\<in>N`?N. n < 1"
      using N_less_1 by auto
  qed

  have T_mono: "\<And>n m. m \<le> n \<Longrightarrow> T n \<subseteq> T m"
    unfolding T_def by auto

  { fix s' k assume "s' \<in> S - \<Phi>" "s' \<in> reachable (S - \<Phi>) s \<or> s' = s"
    then have "prob s' (T (n * k)) \<le> M^k"
    proof (induct k arbitrary: s')
      case 0 show ?case by (simp add: T_def)
    next
      case (Suc k)
      have "prob s' (T (n * Suc k)) =
        (\<Sum>\<omega>\<in>Pi\<^isub>E {..<n} (\<lambda>i. S - \<Phi>). (\<Prod>i<n. \<tau> (nat_case s' \<omega> i) (\<omega> i)) *
        prob (nat_case s' \<omega> n) (T (n * k)))"
        unfolding T_Suc[of k s'] using Suc
        by (intro prob_shifted_sets_eq) auto
      also have "\<dots> \<le>
        (\<Sum>\<omega>\<in>Pi\<^isub>E {..<n} (\<lambda>i. S - \<Phi>). (\<Prod>i<n. \<tau> (nat_case s' \<omega> i) (\<omega> i)) * M^k)"
      proof (intro setsum_mono)
        fix \<omega> assume \<omega>: "\<omega> \<in> Pi\<^isub>E {..<n} (\<lambda>i. S - \<Phi>)"
        show "(\<Prod>i<n. \<tau> (nat_case s' \<omega> i) (\<omega> i)) * prob (nat_case s' \<omega> n) (T (n * k))
          \<le> (\<Prod>i<n. \<tau> (nat_case s' \<omega> i) (\<omega> i)) * M^k"
        proof cases
          assume "(\<Prod>i<n. \<tau> (nat_case s' \<omega> i) (\<omega> i)) = 0"
          then show ?thesis by (simp del: setprod_zero_iff)
        next
          assume "(\<Prod>i<n. \<tau> (nat_case s' \<omega> i) (\<omega> i)) \<noteq> 0"
          then have \<tau>: "\<forall>i<n. \<tau> (nat_case s' \<omega> i) (\<omega> i) \<noteq> 0"
            by simp
          have "nat_case s' \<omega> n \<in> S - \<Phi>"
            using \<omega> Suc.prems by (auto split: nat.split)
          moreover from Suc.prems(2)
          have "nat_case s' \<omega> n \<in> reachable (S - \<Phi>) s"
          proof 
            assume "s' \<in> reachable (S - \<Phi>) s"
            then show ?thesis
            proof (rule reachable_trans)
              show "s' \<in> S - \<Phi>" by fact
              show "nat_case s' \<omega> n \<in> reachable (S - \<Phi>) s'"
                using `n \<noteq> 0` \<omega> \<tau> 
                apply (auto simp add: gr0_conv_Suc)
                apply (rule reachable_in)
                apply (auto simp: Pi_iff)
                done
            qed
          next
            assume eq: "s' = s"
            then show ?thesis
              using `n \<noteq> 0` \<omega> \<tau> 
              apply (auto simp add: gr0_conv_Suc)
              apply (rule reachable_in)
              apply (auto simp: Pi_iff)
              done
          qed
          ultimately have "prob (nat_case s' \<omega> n) (T (n * k)) \<le> M^k"
            by (intro Suc.hyps) auto
          then show ?thesis
            using \<omega> Suc.prems
            by (auto intro!: mult_left_mono setprod_nonneg \<tau>_nneg
                     simp: Pi_iff split: nat.split)
        qed
      qed
      also have "\<dots> = N s' * M^k"
        using Suc unfolding N_def
        by (subst prob_cylinder_eq_sum_prod)
           (auto simp: setsum_left_distrib)
      also have "\<dots> \<le> M * M^k"
        using Suc.prems M_nneg by (intro M_ge mult_right_mono) auto
      finally show ?case
        by simp
    qed }
  then have estimate_aux: "\<And>k. prob s (T (k * n)) \<le> M^k"
    using s by (auto simp: ac_simps)
  { fix k :: nat
    have "k div n * n \<le> k div n * n + k mod n"
      by linarith
    also have "k div n * n + k mod n = k"
      by simp
    finally have "k div n * n \<le> k" .
    then have "prob s (T k) \<le> prob s (T (k div n * n))"
      by (intro finite_measure_mono T_mono) auto
    also have "\<dots> \<le> M^(k div n)"
      by (rule estimate_aux)
    also have "\<dots> = (root (Suc n) M)^(Suc n * (k div n))"
      unfolding power_mult
      using `0 \<le> M` by (subst real_root_pow_pos2) auto
    also have "\<dots> \<le> (root (Suc n) M)^(k - n)"
    proof (rule power_decreasing)
      show "k - n \<le> Suc n * (k div n)"
      proof cases
        assume "n \<le> k"
        have "k = k div n * n + k mod n" by simp
        also have "\<dots> \<le> k div n * n + n"
          using `0 < n` by (intro add_mono) simp_all
        also have "\<dots> \<le> Suc n * (k div n) + n" by simp
        finally show "k - n \<le> Suc n * (k div n)"
          by simp
      qed (simp add: not_le)
      show "0 \<le> root (Suc n) M" "root (Suc n) M \<le> 1"
        using `M < 1` `0 \<le> M` by auto
    qed
    finally have "prob s (T k) \<le> root (Suc n) M ^ (k - n)" . }
  note estimate_aux2 = this
  { fix k from estimate_aux2[of "k + n"]
    have "\<bar>prob s (T (k + n))\<bar> \<le> root (Suc n) M ^ k"
      by auto }
  then have estimate: "\<forall>k. \<bar>prob s (T (k + n))\<bar> \<le> root (Suc n) M ^ k" ..

  have "norm (root (Suc n) M) < 1"
    using `M < 1` `0 \<le> M` by auto
  from geometric_sums[OF this]
  have "summable (op ^ (root (Suc n) M))" by (simp add: sums_iff)
  from summable_le2[OF estimate this]
  have "summable (\<lambda>k. prob s (T (k + n)))" ..
  then have "summable (\<lambda>k. prob s (T k))"
    by (rule sums_shift)
  then have T_sums: "(\<lambda>k. \<mu> s (T k)) sums (ereal (\<Sum>k. prob s (T k)))"
    using T_measurable
    by (auto simp add: finite_measure_eq sums_ereal) (simp add: sums_iff)
  

  from until
  have t_imp_T: "\<And>N. AE \<omega> in path_space s. N < hitting_time \<Phi> \<omega> \<longrightarrow> \<omega> \<in> T N"
  proof (elim AE_mp, intro AE_I2 impI)
    fix \<omega> N assume \<omega>: "\<omega> \<in> space (path_space s)" "nat_case s \<omega> \<in> until S \<Phi>" "N < hitting_time \<Phi> \<omega>"
    show "\<omega> \<in> T N"
      unfolding T_def
    proof safe
      fix i
      assume "\<omega> i \<in> \<Phi>"
      then have "hitting_time \<Phi> \<omega> \<le> i"
        unfolding hitting_time_def by (rule Least_le)
      also assume "i < N"
      finally have "hitting_time \<Phi> \<omega> < N" .
      then show False using `N < hitting_time \<Phi> \<omega>` by simp
    qed (insert \<omega>, auto simp: space_path_space)
  qed

  note positive_integral_nat_function[OF measurable_hitting_time]
  moreover have "\<And>i. (real_of_nat \<circ> hitting_time \<Phi>) -` {of_nat i <..} \<inter> space (path_space s) =
    {\<omega>\<in>UNIV\<rightarrow>S. real_of_nat i < real_of_nat (hitting_time \<Phi> \<omega>)}"
    by (auto simp: space_path_space)
  ultimately have "(\<integral>\<^isup>+ \<omega>. ereal (of_nat (hitting_time \<Phi> \<omega>)) \<partial>path_space s) =
    (\<Sum>i. \<mu> s {\<omega>\<in>space (path_space s). real_of_nat i < real_of_nat (hitting_time \<Phi> \<omega>)})"
    by (simp add: space_path_space)
  also have "\<dots> \<le> (\<Sum>i. \<mu> s (T i))"
    using measurable_hitting_time
    by (intro suminf_le_pos positive_measure borel_measurable_less measure_mono_AE T_measurable)
       (simp_all add: comp_def t_imp_T)
  also have "\<dots> < \<infinity>"
    using T_sums unfolding sums_iff by simp
  finally have "integral\<^isup>P (path_space s) (real_of_nat \<circ> hitting_time \<Phi>) \<noteq> \<infinity>"
    by simp
  then have "\<infinity> \<noteq> (\<integral>\<^isup>+ \<omega>. 1 + ereal (real_of_nat (hitting_time \<Phi> \<omega>)) \<partial>path_space s)"
    using measurable_hitting_time by (subst positive_integral_add) (auto simp: comp_def)
  also have "(\<integral>\<^isup>+ \<omega>. 1 + ereal (real_of_nat (hitting_time \<Phi> \<omega>)) \<partial>path_space s) =
    (\<integral>\<^isup>+ \<omega>. real (hitting_time \<Phi> (nat_case s \<omega>)) \<partial>path_space s)"
    using until
  proof (intro positive_integral_cong_AE, elim AE_mp, intro AE_I2 impI)
    fix \<omega> assume \<omega>: "\<omega> \<in> space (path_space s)" "nat_case s \<omega> \<in> until S \<Phi>"
    from untilE2[OF \<omega>(2)] guess n . note n = this
    
    with s have "(LEAST i. nat_case s \<omega> i \<in> \<Phi>) = Suc (LEAST i. nat_case s \<omega> (Suc i) \<in> \<Phi>)"
      by (intro Least_Suc[where n=n]) auto
    then have "hitting_time \<Phi> (nat_case s \<omega>) = Suc (hitting_time \<Phi> \<omega>)"
      unfolding hitting_time_def by simp
    then show "1 + ereal (real_of_nat (hitting_time \<Phi> \<omega>)) = real (hitting_time \<Phi> (nat_case s \<omega>))"
      by (simp add: real_of_nat_Suc real_eq_of_nat)
  qed
  finally show ?thesis ..
qed

lemma until_Int_space_eq: "until \<Phi> \<Psi> \<inter> (UNIV \<rightarrow> S) = until \<Phi> \<Psi>"
  by (auto simp add: until_def)

lemma until_nat_case_first[simp]:
  "\<Psi> \<subseteq> S \<Longrightarrow> s \<in> \<Psi> \<Longrightarrow> nat_case s \<omega> \<in> until \<Phi> \<Psi> \<longleftrightarrow> \<omega> \<in> UNIV\<rightarrow>S"
  by (auto simp: until_def Pi_iff split: nat.split)

lemma hitting_time_eq:
  "\<omega> n \<in> \<Phi> \<Longrightarrow> (\<And>i. i < n \<Longrightarrow> \<omega> i \<notin> \<Phi>) \<Longrightarrow> hitting_time \<Phi> \<omega> = n"
  unfolding hitting_time_def
  by (rule Least_equality) (auto simp: not_less[symmetric])

lemma
  assumes until: "\<omega> \<in> until S \<Phi>"
  shows hitting_time_in[intro]: "\<omega> (hitting_time \<Phi> \<omega>) \<in> \<Phi>"
    and hitting_time_least: "\<And>i. i < hitting_time \<Phi> \<omega> \<Longrightarrow> \<omega> i \<notin> \<Phi>"
proof -
  from untilE2[OF until] guess n . note n = this
  moreover then have n_eq: "hitting_time \<Phi> \<omega> = n"
    by (intro hitting_time_eq) auto
  ultimately show "\<omega> (hitting_time \<Phi> \<omega>) \<in> \<Phi>"
    and "\<And>i. i < hitting_time \<Phi> \<omega> \<Longrightarrow> \<omega> i \<notin> \<Phi>"
    by auto
qed

lemma hitting_time_nat_case_Suc:
  assumes "\<omega> \<in> until S \<Phi>" "s \<notin> \<Phi>"
  shows "hitting_time \<Phi> (nat_case s \<omega>) = Suc (hitting_time \<Phi> \<omega>)"
proof -
  have "(LEAST i. (nat_case s \<omega>) i \<in> \<Phi>) = Suc (LEAST i. nat_case s \<omega> (Suc i) \<in> \<Phi>)"
    using assms by (intro Least_Suc[of _ "Suc (hitting_time \<Phi> \<omega>)"]) auto
  then show ?thesis unfolding hitting_time_def by simp
qed

lemma hitting_time_nat_case_0:
  "s \<in> \<Phi> \<Longrightarrow> hitting_time \<Phi> (nat_case s \<omega>) = 0"
  unfolding hitting_time_def by (auto intro!: Least_equality)

end

end
