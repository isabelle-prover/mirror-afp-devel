(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

theory Discrete_Time_Markov_Chain
  imports Probability
begin

section {* Preparations *}

lemma measurable_Least[measurable]:
  assumes [measurable]: "(\<And>i::nat. (\<lambda>x. P i x) \<in> measurable M (count_space UNIV))" 
  shows "(\<lambda>x. LEAST i. P i x) \<in> measurable M (count_space UNIV)"
  unfolding measurable_def by (safe intro!: sets_Least) simp_all

lemma measurable_real_of_nat[measurable]:
  "real_of_nat \<in> borel_measurable (count_space UNIV)"
  unfolding real_eq_of_nat[symmetric] by simp

lemma sets_count_space'[measurable]: "s \<in> S \<Longrightarrow> A \<in> sets (count_space S) \<Longrightarrow> insert s A \<in> sets (count_space S)" by auto

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

lemma sets_Collect_eq[measurable]:
  assumes f: "f \<in> measurable M N" "{i} \<in> sets N"
  shows "{x\<in>space M. f x = i} \<in> sets M"
proof -
  have "{x\<in>space M. f x = i} = f -` {i} \<inter> space M"
    by auto
  also have "f -` {i} \<inter> space M \<in> sets M"
    using f by (auto intro: measurable_sets)
  finally show ?thesis .
qed

lemma nat_case_in_funcset: "nat_case x f \<in> (UNIV \<rightarrow> X) \<longleftrightarrow> x \<in> X \<and> f \<in> UNIV \<rightarrow> X"
  by (auto simp: Pi_def split: nat.split)

lemma all_Suc_split: "\<And>n P. (\<forall>i\<le>Suc n. P i) \<longleftrightarrow> (\<forall>i\<le>n. P (Suc i)) \<and> P 0"
  by (metis le_eq_less_or_eq less_Suc_eq_0_disj)

lemma atMost_Suc_eq_insert_0: "{..Suc n} = insert 0 (Suc ` {..n})"
  by (metis lessThan_Suc_atMost lessThan_Suc_eq_insert_0)

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

lemma incseq_simple_integral:
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

lemma simple_function_comp2: 
  fixes g :: "_ \<Rightarrow> _::t2_space"
  assumes f: "f \<in> measurable M M'"
    and g: "simple_function M' g"
  shows "simple_function M (g \<circ> f)"
proof (rule simple_function_borel_measurable)
  note borel = borel_measurable_simple_function[OF g]
  show "g \<circ> f \<in> borel_measurable M"
    using f borel by (rule measurable_comp)
  from f have "(g\<circ>f) ` space M \<subseteq> g ` space M'"
    unfolding measurable_def by auto
  from this simple_functionD(1)[OF g] show "finite ((g \<circ> f) ` space M)"
    by (rule finite_subset)
qed

lemma simple_function_comp2':
  fixes g :: "_ \<Rightarrow> _::t2_space"
  shows "f \<in> measurable M M' \<Longrightarrow> simple_function M' g \<Longrightarrow> simple_function M (\<lambda>x. g (f x))"
  using simple_function_comp2 by (simp add: comp_def)
 
lemma Collect_Int: "Collect P \<inter> A = {x\<in>A. P x}"
  by auto

lemma Collect_Int2: "{x\<in>S. P x} \<inter> A = {x\<in>S. x \<in> A \<and> P x}"
  by auto

lemma borel_measurable_setsum_dependent_index:
  fixes f :: "'a \<Rightarrow> nat" and g :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "\<And>i. f -` {i} \<inter> space M \<in> sets M"
  assumes "\<And>i. g i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Sum>i::nat<f x. g i x) \<in> borel_measurable M"
proof (unfold measurable_def, safe)
  fix A :: "real set" assume "A \<in> sets borel"
  moreover def X \<equiv> "\<lambda>i. (\<lambda>x. \<Sum>i::nat<i. g i x) -` A \<inter> space M"
  moreover note assms
  ultimately have "(\<lambda>x. \<Sum>i::nat<f x. g i x) -` A \<inter> space M = (\<Union>i. (f -` {i} \<inter> space M) \<inter> X i)" "\<And>i. X i \<in> sets M"
    by (auto intro!: measurable_sets)
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

lemma sets_Collect_in:
  assumes A: "A \<in> sets M" shows "{x\<in>space M. x \<in> A} \<in> sets M"
proof -
  have "{x\<in>space M. x \<in> A} = space M \<inter> A" by auto
  with A show ?thesis by auto
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

lemma positive_integral_nat_function:
  assumes "(of_nat \<circ> f :: 'a \<Rightarrow> real) \<in> borel_measurable M"
  shows "(\<integral>\<^isup>+x. ereal (of_nat (f x)) \<partial>M) =
    (\<Sum>t. emeasure M ((of_nat \<circ> f) -` {of_nat t::real <..} \<inter> space M))"
proof -
  def F \<equiv> "\<lambda>i. (of_nat \<circ> f) -` {of_nat i::real <..} \<inter> space M"
  with assms have [measurable]: "\<And>i. F i \<in> sets M"
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
  also have "\<dots> = (\<Sum>i. emeasure M (F i))"
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

definition "state_space s = point_measure S (if s \<in> S then \<tau> s else \<tau> s0)"

lemma 
  shows space_state_space[simp]: "space (state_space s) = S"
    and sets_state_space[simp]: "sets (state_space s) = Pow S"
  unfolding state_space_def by (simp_all add: space_point_measure sets_point_measure)

lemma emeasure_state_space[simp]: "A \<subseteq> S \<Longrightarrow> s \<in> S \<Longrightarrow> emeasure (state_space s) A = (\<Sum>a\<in>A. \<tau> s a)"
  unfolding state_space_def
  by (subst emeasure_point_measure_finite) auto

lemma measure_state_space[simp]: "A \<subseteq> S \<Longrightarrow> s \<in> S \<Longrightarrow> measure (state_space s) A = (\<Sum>a\<in>A. \<tau> s a)"
  unfolding state_space_def measure_def
  by (subst emeasure_point_measure_finite) auto

lemma prob_space_state_space:
   "prob_space (state_space s)"
proof
  have "s \<notin> S \<Longrightarrow> state_space s = state_space s0"
    unfolding state_space_def by simp
  with s0 show "emeasure (state_space s) (space (state_space s)) = 1"
    by (cases "s \<in> S") (simp_all add: \<tau>_distr one_ereal_def)
qed

lemma measurable_S[measurable]: "{x \<in> space (count_space S). x \<in> \<Phi>} \<in> sets (count_space S)"
  by auto

subsection {* @{text path} *}

primrec path :: "'s \<Rightarrow> ((nat \<times> 's) \<Rightarrow> 's) \<Rightarrow> (nat \<Rightarrow> 's)" where
  "path s X 0 = X (0, if s \<notin> S then s0 else s)"
| "path s X (Suc n) = X (Suc n, path s X n)"

abbreviation
  "d_space \<equiv> (\<Pi>\<^isub>M (n, s) \<in> (UNIV :: nat set) \<times> S. state_space s)"

abbreviation
  "p_space \<equiv> (\<Pi>\<^isub>M n\<in>UNIV::nat set. count_space S)"

definition
  "path_space s = distr d_space p_space (path s)"

lemma space_p_space[simp]: "space p_space = UNIV \<rightarrow> S"
  by (simp add: space_PiM Pi_iff extensional_def)

lemma
  shows space_path_space[simp]: "space (path_space s) = UNIV \<rightarrow> S"
    and sets_path_space[simp]: "sets (path_space s) = sets p_space"
  by (auto simp add: path_space_def)

lemma sets_Collect_singleton:
   "A \<in> sets (M i) \<Longrightarrow> i \<in> I \<Longrightarrow> {\<omega> \<in> space (Pi\<^isub>M I M). \<omega> i \<in> A} \<in> sets (Pi\<^isub>M I M)"
   using measurable_component_singleton[of i I M,
      THEN measurable_sets, of A]
   by (simp add: vimage_def Int_def conj_commute)

lemma in_path_space_in_single[simp, intro]:
  "{\<omega>\<in>UNIV \<rightarrow> S. \<omega> i \<in> A} \<in> sets p_space"
  using sets_Collect_singleton[of "A \<inter> S" "\<lambda>i. count_space S" i UNIV]
  by (simp add: Pi_iff cong: conj_cong)

lemma in_path_space_single[simp, intro]:
  "{\<omega>\<in>UNIV \<rightarrow> S. \<omega> i = x} \<in> sets p_space"
  using in_path_space_in_single[of i "{x}"] by simp

lemma p_space_Collect_Bex_S: 
  assumes P: "\<And>s. s \<in> S \<Longrightarrow> {\<omega>\<in>UNIV \<rightarrow> S. P \<omega> s} \<in> sets p_space"
  shows "{\<omega>\<in>UNIV \<rightarrow> S. \<exists>s\<in>S. P \<omega> s} \<in> sets p_space"
  by (intro sets_Collect_finite_Ex[of _ p_space, unfolded space_p_space] P finite_S)

lemma p_space_Collect_Ball_S: 
  assumes P: "\<And>s. s \<in> S \<Longrightarrow> {\<omega>\<in>UNIV \<rightarrow> S. P \<omega> s} \<in> sets p_space"
  shows "{\<omega>\<in>UNIV \<rightarrow> S. \<forall>s\<in>S. P \<omega> s} \<in> sets p_space"
  by (intro sets_Collect_finite_All[of _ p_space, unfolded space_p_space] P finite_S S_not_empty)

lemma p_space_Collect_omega:
  "{\<omega>\<in>UNIV \<rightarrow> S. P (\<omega> i)} \<in> sets p_space"
proof -
  have "{\<omega>\<in>UNIV \<rightarrow> S. P (\<omega> i)} = {\<omega>\<in>UNIV \<rightarrow> S. \<forall>s\<in>S. \<omega> i = s \<longrightarrow> P s}"
    by (auto simp: Pi_iff)
  also have "\<dots> \<in> sets p_space"
    by (intro sets_Collect[of p_space, unfolded space_p_space] p_space_Collect_Ball_S in_path_space_single)
  finally show ?thesis .
qed

lemma p_space_measurable:
  assumes f: "f \<in> measurable p_space M" and A: "A \<in> sets M"
  shows "{\<omega>\<in>UNIV \<rightarrow> S. f \<omega> \<in> A} \<in> sets p_space"
  using measurable_sets[OF f A] by (simp add: vimage_def Collect_Int)

lemmas p_space_Collect =
    sets_Collect(1-5,7-)[of p_space, unfolded space_p_space]
    sets_Collect_countable_Ball[of p_space, unfolded space_p_space]
    sets_Collect_countable_Bex[of p_space, unfolded space_p_space]
    p_space_Collect_Bex_S
    p_space_Collect_Ball_S
    p_space_Collect_omega

lemma in_path_space_le[intro,simp]:
  "{X'\<in>UNIV \<rightarrow> S. \<forall>i\<le>n. X' i = X i} \<in> sets p_space"
  by (intro p_space_Collect)

lemma in_path_space_less[intro,simp]:
  "{X'\<in>UNIV \<rightarrow> S. \<forall>i<n. X' i = X i} \<in> sets p_space"
  by (intro p_space_Collect)

lemma in_path_space_le_in[intro, simp]:
  "{X'\<in>UNIV\<rightarrow>S. \<forall>i\<le>n. X' i \<in> Y i} \<in> sets p_space"
  by (intro p_space_Collect)

lemma in_path_space_less_in[intro, simp]:
  "{X'\<in>UNIV\<rightarrow>S. \<forall>i<n. X' i \<in> Y i} \<in> sets p_space"
  by (intro p_space_Collect)

lemma in_path_space_in[intro, simp]:
  "{X'\<in>UNIV\<rightarrow>S. \<forall>i\<in>I. X' i \<in> X i} \<in> sets p_space"
  by (intro p_space_Collect)

lemma path_in_S: "\<forall>i. \<forall>s'\<in>S. X (i, s') \<in> S \<Longrightarrow> path s X n \<in> S"
  by (induct n) (auto simp: s0)

lemma paths_in_path_space[intro, simp]:
  "(UNIV \<rightarrow> S) \<in> sets p_space"
  using top[of p_space] by simp
   
lemma measurable_path:
  "path s \<in> measurable d_space (\<Pi>\<^isub>M n \<in> (UNIV :: nat set). count_space S)"
proof (rule measurable_PiM_single)
  fix i :: nat and A assume "A \<in> sets (count_space S)"
  then show "{\<omega>\<in>space d_space. path s \<omega> i \<in> A} \<in> sets d_space"
  proof (induct i arbitrary: A)
    case (Suc i)
    have "{\<omega> \<in> space d_space. path s \<omega> (Suc i) \<in> A} =
      {\<omega> \<in> space d_space. \<forall>s'\<in>S. path s \<omega> i \<in> {s'} \<longrightarrow> \<omega> (Suc i, s') \<in> A }"
      using path_in_S by (auto simp add: space_PiM Pi_iff)
    also have "\<dots> \<in> sets d_space"
      using s0 Suc.prems
      by (intro sets_Collect_finite_All sets_Collect Suc.hyps sets_Collect_singleton) auto
    finally show ?case .
  qed (simp add: sets_Collect_singleton s0)
qed (auto simp add: space_PiM extensional_def Pi_iff path_in_S)

subsection {* @{const path_space} is a probability space *}

end

sublocale Discrete_Time_Markov_Chain \<subseteq> prob_space "path_space s" for s
proof -
  interpret S: prob_space "state_space s" for s by (rule prob_space_state_space)
  interpret P: product_prob_space "\<lambda>(n, s). state_space s" "(UNIV :: nat set) \<times> S" unfolding split_beta' ..
  show "prob_space (path_space s)"
    unfolding path_space_def using measurable_path by (rule P.prob_space_distr)
qed

lemma measure_distr:
  "f \<in> measurable M N \<Longrightarrow> S \<in> sets N \<Longrightarrow> measure (distr M N f) S = measure M (f -` S \<inter> space M)"
  by (simp add: emeasure_distr measure_def)

context Discrete_Time_Markov_Chain
begin

lemma prob_generator:
  assumes s: "\<And>i. i < n \<Longrightarrow> \<omega> i \<in> S" "s' \<in> S"
  shows "prob s' {s'\<in>UNIV \<rightarrow> S. \<forall>i<n. s' i = \<omega> i} = (\<Prod>i<n. \<tau> (nat_case s' \<omega> i) (\<omega> i))"
proof -
  interpret S: prob_space "state_space s''" for s'' by (rule prob_space_state_space)
  interpret Prod: product_prob_space "\<lambda>(n, s). state_space s" "(UNIV :: nat set) \<times> S"
    unfolding split_beta' ..

  let ?M = "(\<lambda>(n, s). state_space s)" and ?I = "(\<lambda>i. (i, nat_case s' \<omega> i)) ` {..< n}"
  
  have inj_I: "\<And>A. inj_on (\<lambda>i. (i, nat_case s' \<omega> i)) A"
    by (auto simp: inj_on_def)

  { fix X i assume "i < n" "\<forall>j<n. X (j, nat_case s' \<omega> j) = \<omega> j"
    with `s' \<in> S` have "path s' X i = \<omega> i"
      by (induct i) auto }
  moreover
  { fix X i assume X: "i < n" "\<forall>j<n. path s' X j = \<omega> j"
    then have "X (i, nat_case s' \<omega> i) = \<omega> i"
    proof (induct i)
      case (Suc i) then show ?case
        using Suc.prems(2)[rule_format, of "Suc i"] by simp
    qed (insert `s' \<in> S`, auto) }
  ultimately have "\<And>X. (\<forall>i<n. path s' X i = \<omega> i) \<longleftrightarrow> (\<forall>j<n. X (j, nat_case s' \<omega> j) = \<omega> j)"
    by blast
  then have eq: "path s' -` {s'\<in>space p_space. \<forall>i<n. s' i = \<omega> i} \<inter> space d_space =
    prod_emb (UNIV \<times> S) ?M ?I (\<Pi>\<^isub>E (n, _) \<in> ?I. {\<omega> n})" (is "_ = ?E")
    by (auto simp add: vimage_def space_PiM extensional_def Pi_iff prod_emb_def path_in_S)
  then have "prob s' {s'\<in>UNIV \<rightarrow> S. \<forall>i<n. s' i = \<omega> i} = 
    measure d_space ?E"
    unfolding path_space_def by (subst measure_distr[OF measurable_path in_path_space_less]) simp
  also have "\<dots> = (\<Prod> i<n. \<tau> (nat_case s' \<omega> i) (\<omega> i))"
    by (subst Prod.measure_PiM_emb)
       (auto simp: s setprod_reindex[OF inj_I] intro!: setprod_cong split: nat.split)
  finally show ?thesis by simp
qed 

lemma restrict_UNIV: "restrict f UNIV = f" by auto

lemma measurable_shift:
  "(\<lambda>\<omega> i. \<omega> (f i)) \<in> measurable p_space p_space"
  apply (rule measurable_restrict[of "UNIV :: nat set", unfolded restrict_UNIV ])
  apply (rule measurable_component_singleton)
  apply auto
  done

lemma nat_case_cylinder: 
  "s \<in> S \<Longrightarrow> nat_case s -` {X'\<in>UNIV \<rightarrow> S. \<forall>i\<le>n. X' i = X i} \<inter> (UNIV \<rightarrow> S) =
    (if X 0 = s then case n of 0 \<Rightarrow> UNIV \<rightarrow> S
                             | Suc n \<Rightarrow> {X'\<in>UNIV \<rightarrow> S. \<forall>i\<le>n. X' i = X (Suc i)} else {})"
  by (auto split: nat.split simp: Pi_def)

lemma measurable_nat_case[measurable]:
  "s' \<in> S \<Longrightarrow> nat_case s' \<in> measurable p_space p_space"
  apply (rule measurable_restrict[of "UNIV :: nat set", unfolded restrict_UNIV ])
  apply (case_tac i)
  apply simp_all
  done

lemma path_space_1[simp]:
  "prob s (UNIV \<rightarrow> S) = 1"
  using prob_space unfolding space_path_space .

lemma prob_generator_0:
  "s \<in> S \<Longrightarrow> s' \<in> S \<Longrightarrow> prob s' {s'\<in>UNIV \<rightarrow> S. s' 0 = s} = \<tau> s' s"
  using prob_generator[of "Suc 0" "\<lambda>_. s"]
  by (simp add: lessThan_Suc)

lemma prob_generator_le:
  "(\<And>i. i \<le> n \<Longrightarrow> s i \<in> S) \<Longrightarrow> s' \<in> S \<Longrightarrow>
    prob s' {s'\<in>UNIV \<rightarrow> S. \<forall>i\<le>n. s' i = s i} = (\<Prod>i\<le>n. \<tau> (nat_case s' s i) (s i))"
  using prob_generator[of "Suc n" s s']
  by (simp add: less_Suc_eq_le lessThan_Suc_atMost)

lemma AE_\<tau>_not_zero:
  assumes "s \<in> S"
  shows "AE \<omega> in path_space s. \<forall>i. \<tau> (nat_case s \<omega> i) (\<omega> i) \<noteq> 0"
proof (rule AE_I)
  let ?N = "\<lambda>k. {\<omega> \<in> UNIV \<rightarrow> S. \<exists>i\<le>k. \<forall>t\<in>S. nat_case s \<omega> i = t \<longrightarrow> (\<exists>t'\<in>{t'\<in>S. \<tau> t t' = 0}. \<omega> i = t')}"
  show "{\<omega> \<in> space (path_space s). \<not> (\<forall>i. \<tau> (nat_case s \<omega> i) (\<omega> i) \<noteq> 0)} \<subseteq> (\<Union>i. ?N i)"
    (is "_ \<subseteq> ?allN")
    using `s \<in> S` by force

  have N: "\<And>i. ?N i \<in> sets p_space"
    using S_not_empty unfolding space_p_space space_path_space
    by (split nat.split) (intro p_space_Collect)

  then show "?allN \<in> events s"
    by auto

  have "(SUP i. emeasure (path_space s) (?N i)) = emeasure (path_space s) ?allN"
  proof (rule SUP_emeasure_incseq)
    show "range ?N \<subseteq> events s"
      using N by auto
    show "incseq ?N"
      using `s \<in> S` by (auto simp add: incseq_def intro: order_trans)
  qed
  moreover
  { fix n
    have "?N n = (\<Union>\<omega>'\<in>(\<Pi>\<^isub>E i\<in>{..n}. S) \<inter> {\<omega>. \<exists>i\<le>n. \<tau> (nat_case s \<omega> i) (\<omega> i) = 0}. {\<omega>\<in>UNIV\<rightarrow>S. \<forall>i\<le>n. \<omega> i = \<omega>' i})"
       (is "_ = UNION ?I ?S")
      using `s \<in> S`
      apply (simp add: Pi_iff set_eq_iff Bex_def)
      apply safe
      apply fastforce
      apply (rule_tac x="restrict x {..n}" in exI)
      apply simp
      apply (rule_tac x="i" in exI)
      apply (fastforce split: nat.split)
      apply (rule_tac x="i" in exI)
      apply (fastforce split: nat.split)
      done
    moreover have "(\<Sum>\<omega>\<in>?I. emeasure (path_space s) (?S \<omega>)) = emeasure (path_space s) (UNION ?I ?S)"
    proof (rule setsum_emeasure)
      show "disjoint_family_on ?S ?I"
      proof (unfold disjoint_family_on_def, intro ballI impI)
        fix \<omega>1 \<omega>2 :: "nat \<Rightarrow> 's" assume "\<omega>1 \<noteq> \<omega>2"
        then obtain i where i: "\<omega>1 i \<noteq> \<omega>2 i" by auto
        moreover assume "\<omega>1 \<in> ?I" "\<omega>2 \<in> ?I"
        ultimately have "i \<le> n" by (rule_tac ccontr) (auto simp: extensional_def)
        with i show "?S \<omega>1 \<inter> ?S \<omega>2 = {}" by auto
      qed
    qed auto
    moreover
    { fix \<omega> assume \<omega>: "\<omega> \<in> ?I"
      then have "emeasure (path_space s) (?S \<omega>) = ereal (prob s (?S \<omega>))"
        by (simp add: emeasure_eq_measure)
      also have "\<dots> = ereal (\<Prod>i\<le>n. \<tau> (nat_case s \<omega> i) (\<omega> i))"
        using `s \<in> S` \<omega> by (subst prob_generator_le) auto
      also have "\<dots> = ereal 0"
        using \<omega> by (subst setprod_zero) auto
      finally have "emeasure (path_space s) (?S \<omega>) = 0" by simp }
    ultimately have "emeasure (path_space s) (?N n) = 0"
      by simp }
  ultimately show "emeasure (path_space s) ?allN = 0"
    by simp
qed

subsection {* Iterative equation for @{const prob} *}

definition "iterative_measure s =
  measure_of (space p_space) (sets p_space)
             (\<lambda>A. \<integral>\<^isup>+s'. emeasure (distr (path_space s') p_space (nat_case s')) A \<partial>state_space s)"

lemma space_iterative[simp]: "space (iterative_measure s) = UNIV \<rightarrow> S"
  unfolding iterative_measure_def space_measure_of[OF space_closed] by simp

lemma sets_iterative[simp]: "sets (iterative_measure s) = sets p_space"
  unfolding iterative_measure_def sets_measure_of[OF space_closed] sigma_sets_eq ..

lemma emeasure_iterative_measure:
  assumes A: "A \<in> sets p_space" 
  shows "emeasure (iterative_measure s) A = (\<integral>\<^isup>+s'. emeasure (distr (path_space s') p_space (nat_case s')) A \<partial>state_space s)"
    (is "_ = ?\<mu> A")
proof (rule emeasure_measure_of[OF iterative_measure_def space_closed])
  from A show "A \<in> sets (iterative_measure s)" by simp
  show "positive (sets (iterative_measure s)) ?\<mu>"
    by (simp add: positive_def positive_integral_positive)
  show "countably_additive (sets (iterative_measure s)) ?\<mu>"
  proof (cases rule: countably_additiveI)
    case (goal1 A) then show ?case
      apply (subst positive_integral_suminf[symmetric])
      apply (simp add: state_space_def)
      apply (simp add: emeasure_nonneg)
      apply (subst suminf_emeasure)
      apply auto
      done
  qed
qed

lemma emeasure_iterative_measure':
  assumes A: "A \<in> sets p_space" and "s \<in> S"
  shows "emeasure (iterative_measure s) A = (\<Sum>s'\<in>S. \<tau> s s' * prob s' (nat_case s' -` A \<inter> (UNIV \<rightarrow> S)))"
  using `s \<in> S` A
  apply (simp add: state_space_def emeasure_iterative_measure)
  apply (subst positive_integral_point_measure_finite)
  apply (simp_all add: emeasure_nonneg)
  apply (simp add: emeasure_distr measurable_nat_case emeasure_eq_measure cong: measurable_cong_sets)
  done

lemma prob_space_iterative_measure: assumes "s \<in> S" shows "prob_space (iterative_measure s)"
proof
  have eq: "\<And>s. s \<in> S \<Longrightarrow> nat_case s -` (UNIV \<rightarrow> S) \<inter> (UNIV \<rightarrow> S) = UNIV \<rightarrow> S" by auto 
  show "emeasure (iterative_measure s) (space (iterative_measure s)) = 1"
    using `s \<in> S` by (simp add: emeasure_iterative_measure' eq \<tau>_distr one_ereal_def)
qed

lemma measure_iterative_measure:
  assumes A: "A \<in> sets p_space" and "s \<in> S"
  shows "measure (iterative_measure s) A = (\<Sum>s'\<in>S. \<tau> s s' * prob s' (nat_case s' -` A \<inter> (UNIV \<rightarrow> S)))"
proof -
  interpret I: prob_space "iterative_measure s" using `s \<in> S` by (rule prob_space_iterative_measure)
  show ?thesis
    by (intro ereal.inject[THEN iffD1])
       (simp add: emeasure_iterative_measure'[OF A `s \<in> S`] I.emeasure_eq_measure[symmetric])
qed

definition "cylinders = range (\<lambda>(n::nat, \<omega>'). {\<omega>\<in>UNIV \<rightarrow> S. \<forall>i<n. \<omega> i = \<omega>' i}) \<union> {{}}"

lemma cylindersE:
  assumes "A \<in> cylinders"
  obtains (P1) \<omega>' n where "\<omega>' \<in> {..<n} \<rightarrow> S" "A = {\<omega>\<in>UNIV \<rightarrow> S. \<forall>i<n. \<omega> i = \<omega>' i}"
        | (empty) "A = {}"
proof (atomize_elim, cases)
  assume "A \<noteq> {}"
  with `A \<in> cylinders` obtain \<omega>' n where A: "A = {\<omega>\<in>UNIV \<rightarrow> S. \<forall>i<n. \<omega> i = \<omega>' i}"
    by (auto simp: cylinders_def)
  with `A \<noteq> {}` have "\<omega>' \<in> {..<n} \<rightarrow> S" by (auto simp: Pi_iff) metis
  with A `A \<noteq> {}`
  show "(\<exists>\<omega>' n. \<omega>' \<in> {..<n} \<rightarrow> S \<and> A = {\<omega> \<in> UNIV \<rightarrow> S. \<forall>i<n. \<omega> i = \<omega>' i}) \<or> A = {}"
    by blast
qed simp

lemma sets_p_space_cylinder:
  "sets p_space = sigma_sets (UNIV \<rightarrow> S) cylinders"
  (is "_ = sigma_sets ?\<Omega> ?A")
proof (rule antisym)
  show "sigma_sets ?\<Omega> ?A \<subseteq> sets p_space"
    unfolding space_p_space[symmetric] by (intro sigma_sets_subset) (auto simp: cylinders_def)
  interpret sigma_algebra ?\<Omega> "sigma_sets ?\<Omega> ?A"
    by (rule sigma_algebra_sigma_sets) (auto simp: cylinders_def)
  have eq: "UNIV \<rightarrow>\<^isub>E space (count_space S) = UNIV \<rightarrow> S" by (simp add: extensional_def)
  show "sets p_space \<subseteq> sigma_sets ?\<Omega> ?A"
    unfolding sets_PiM_single eq
  proof (safe intro!: sigma_sets_mono)
    fix i :: nat and A assume "A \<in> sets (count_space S)"
    then have "A \<subseteq> S" by simp
    then have "{f \<in> UNIV \<rightarrow> S. f i \<in> A} =
      (\<Union>x\<in>(\<Pi>\<^isub>E j\<in>{.. i}. if j = i then A else S). case (Suc i, x) of (n, x) \<Rightarrow> {f \<in> UNIV \<rightarrow> S. \<forall>j<n. f j = x j})"
      apply (auto simp: Pi_iff Ball_def split: split_if_asm)
      apply (rule_tac x="restrict x {..i}" in bexI)
      apply auto
      done
    also have "\<dots> \<in> sigma_sets ?\<Omega> ?A"
      using `A \<subseteq> S`
      by (intro finite_UN finite_PiE) (auto intro!: sigma_sets.Basic dest: finite_subset simp: cylinders_def)
    finally show "{f \<in> UNIV \<rightarrow> S. f i \<in> A} \<in> sigma_sets ?\<Omega> ?A" .
  qed
qed

lemma Int_stable_cylinders: "Int_stable cylinders"
proof (safe intro!: Int_stableI elim!: cylindersE)
  fix n m :: nat and X Y 
  let ?A = "{\<omega>\<in>UNIV \<rightarrow> S. \<forall>i<n. \<omega> i = X i}" and ?B = "{\<omega>\<in>UNIV \<rightarrow> S. \<forall>i<m. \<omega> i = Y i}"
  { assume "?A \<inter> ?B \<noteq> {}"
    then have "?A \<inter> ?B = {\<omega>\<in>UNIV \<rightarrow> S. \<forall>i<max n m. \<omega> i = (if m \<le> n then X else Y) i}"
      by auto
    also have "\<dots> \<in> cylinders"
      by (auto simp: cylinders_def)
    finally have "?A \<inter> ?B \<in> cylinders" . }
  then show "?A \<inter> ?B \<in> cylinders"
    by (auto simp: cylinders_def)
qed (auto simp: cylinders_def)

lemma path_space_eq_iterative_measure:
  assumes "s \<in> S" shows "path_space s = iterative_measure s"
proof (rule measure_eqI_generator_eq[OF Int_stable_cylinders])
  show "range (\<lambda>i. UNIV \<rightarrow>S ) \<subseteq> cylinders"
    by (auto simp: cylinders_def)
  show "sets (path_space s) = sigma_sets (UNIV \<rightarrow> S) cylinders"
   "sets (iterative_measure s) = sigma_sets (UNIV \<rightarrow> S) cylinders"
    by (simp_all add: sets_p_space_cylinder)
  interpret I: prob_space "iterative_measure s" using `s \<in> S` by (rule prob_space_iterative_measure)
  fix X assume "X \<in> cylinders"
  then show "emeasure (path_space s) X = emeasure (iterative_measure s) X"
  proof (safe elim!: cylindersE)
    fix n :: nat and \<omega>' assume \<omega>': "\<omega>' \<in> {..<n} \<rightarrow> S"
    let ?X = "{\<omega> \<in> UNIV \<rightarrow> S. \<forall>i<n. \<omega> i = \<omega>' i}"
    show "emeasure (path_space s) ?X = emeasure (iterative_measure s) ?X"
    proof (cases n)
      case 0
      then have "?X = space p_space" by auto
      then show ?thesis
        using emeasure_space_1 I.emeasure_space_1 by simp
    next
      case (Suc i)
      have eq: "\<And>s'. s' \<in> S \<Longrightarrow> nat_case s' -` {\<omega> \<in> UNIV \<rightarrow> S. \<forall>j<Suc i. \<omega> j = \<omega>' j} \<inter> (UNIV\<rightarrow>S) =
        (if s' = \<omega>' 0 then {\<omega> \<in> UNIV \<rightarrow> S. \<forall>j<i. \<omega> j = \<omega>' (Suc j)} else {})"
        using \<omega>' Suc by (auto split: nat.split)
      from \<omega>' `s \<in> S` have "prob s ?X = (\<Prod>i<n. \<tau> (nat_case s \<omega>' i) (\<omega>' i))"
        by (intro prob_generator) auto
      also have "\<dots> = (\<Sum>s'\<in>S. if s' = \<omega>' 0 then \<tau> s s' * (\<Prod>i<i. \<tau> (\<omega>' i) (\<omega>' (Suc i))) else 0)"
        using `n = Suc i` \<omega>'
        by (auto simp: lessThan_Suc_eq_insert_0 setprod_reindex zero_notin_Suc_image setsum_cases)
      also have "\<dots> = (\<Sum>s'\<in>S. \<tau> s s' * prob s' (nat_case s' -` ?X \<inter> (UNIV\<rightarrow>S)))"
        using \<omega>'[unfolded Pi_iff] Suc
        by (intro setsum_cong) (simp_all add: prob_generator nat_case_idem eq del: vimage_Collect_eq)
      also have "\<dots> = measure (iterative_measure s) ?X"
        using \<omega>' `s \<in> S` by (subst measure_iterative_measure) auto
      finally show ?thesis
        by (simp add: emeasure_eq_measure I.emeasure_eq_measure)
    qed
  qed simp
qed (auto simp: cylinders_def)

lemma prob_eq_sum:
  assumes s: "s \<in> S" and X: "X \<in> sets p_space"
  shows "prob s X = (\<Sum>s'\<in>S. \<tau> s s' * prob s' (nat_case s' -` X \<inter> (UNIV \<rightarrow> S)))"
  unfolding path_space_eq_iterative_measure[OF s]
  using measure_iterative_measure[OF X s] .

lemma measure_eq_sum:
  assumes s: "s \<in> S" and X: "X \<in> sets p_space"
  shows "emeasure (path_space s) X = (\<Sum>s'\<in>S. \<tau> s s' * prob s' (nat_case s' -` X \<inter> (UNIV \<rightarrow> S)))"
  unfolding path_space_eq_iterative_measure[OF s]
  using emeasure_iterative_measure'[OF X s] .
  
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
  qed (auto intro: finite_subset[OF Y])
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
  let ?V = "\<lambda>s'. nat_case s' -` {\<omega> \<in> UNIV \<rightarrow> S. \<forall>i. \<omega> i \<in> A} \<inter> (UNIV \<rightarrow> S)"
  from `s \<in> S` have "prob s {\<omega>\<in>UNIV\<rightarrow>S. \<forall>i. \<omega> i \<in> A} =
    (\<Sum>s'\<in>S. \<tau> s s' * prob s' (?V s'))"
    by (rule prob_eq_sum) (auto intro: p_space_Collect)
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
  assumes s: "s \<in> S" "s' \<in> S" and A: "A \<in> sets p_space"
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
  assumes s: "s \<in> S" "\<And>i. i < n \<Longrightarrow> \<omega> i \<in> S" and A: "A \<in> sets p_space"
  shows "prob s ({\<omega>'\<in>UNIV\<rightarrow>S. \<forall>i<n. \<omega>' i = \<omega> i} \<inter> ((\<lambda>\<omega> i. \<omega> (i + n)) -` A \<inter> (UNIV\<rightarrow>S)))
    = (\<Prod>i<n. \<tau> (nat_case s \<omega> i) (\<omega> i)) * prob (nat_case s \<omega> n) A"
    (is "prob s (?A n s \<omega>) = _")
using s proof (induct n arbitrary: s \<omega>)
  case 0 then show ?case
    using sets_into_space[OF A] by (simp add: Int_absorb2 Int_absorb1)
next
  case (Suc n)
  from Suc.prems A have "prob s (?A (Suc n) s \<omega>) = \<tau> s (\<omega> 0) * prob (\<omega> 0) (?A n (\<omega> 0) (\<lambda>i. \<omega> (Suc i)))"
    by (intro prob_eq_sum_single)
       (auto simp: all_less_Suc_split Collect_Int2
                intro!: p_space_Collect p_space_measurable measurable_shift)
  with Suc show ?case
    by (simp add: lessThan_Suc_eq_insert_0 setprod_reindex nat_case_idem zero_notin_Suc_image)
qed

lemma prob_shifted_sets_eq:
  assumes s: "s \<in> S" and F: "\<And>i. i < n \<Longrightarrow> F i \<subseteq> S" and A: "A \<in> sets p_space"
  shows "prob s ({\<omega>'\<in>UNIV\<rightarrow>S. \<forall>i<n. \<omega>' i \<in> F i} \<inter> ((\<lambda>\<omega> i. \<omega> (i + n)) -` A \<inter> space (path_space s)))
    = (\<Sum>\<omega>\<in>Pi\<^isub>E {..<n} F. (\<Prod>i<n. \<tau> (nat_case s \<omega> i) (\<omega> i)) * prob (nat_case s \<omega> n) A)"
    (is "prob s (?A n s \<omega>) = _")
proof -
  let ?sA = "(\<lambda>\<omega> i. \<omega> (i + n)) -` A \<inter> space (path_space s)"
  let ?S = "\<lambda>\<omega>'. {\<omega>\<in>UNIV\<rightarrow>S. \<forall>i<n. \<omega> i = \<omega>' i} \<inter> ?sA"
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
      using F by (auto dest: finite_subset)
    show "?S ` (Pi\<^isub>E {..<n} F) \<subseteq> events s"
      by (auto simp: Collect_Int2 intro!: p_space_Collect p_space_measurable measurable_shift A)
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
  let ?M = "\<lambda>x s'. (\<lambda>\<omega>. f (nat_case s' \<omega>)) -` {x} \<inter> (UNIV \<rightarrow> S)"
  def P \<equiv> "\<lambda>x s. emeasure (path_space s) (?M x s)"
  then have prob: "\<And>x s. emeasure (path_space s) (?M x s) = P x s" by simp
  { fix x s assume "P x s \<noteq> 0"
    with prob[of s x] have "?M x s \<noteq> {}" by auto }
  note prob_eq_0_imp = this

  { fix s' x assume "s' \<in> S"
    then have "?M x s' = nat_case s' -` (f -` {x} \<inter> space (path_space s)) \<inter> space p_space"
      by auto
    also have "\<dots> \<in> sets p_space"
      using `s' \<in> S` `s \<in> S` simple_functionD[OF f]
      by (intro measurable_sets[OF measurable_nat_case]) auto
    finally have "?M x s' \<in> sets p_space" . }
  note M_sets = this
  then have prob_nonneg[simp, intro!]: "\<And>s' x. s' \<in> S \<Longrightarrow> 0 \<le> P x s'"
    by (auto intro!: measure_nonneg simp: P_def)

  { fix x s' assume "s' \<in> S"
    then have "nat_case s' -` (f -` {x} \<inter> (UNIV \<rightarrow> S)) \<inter> (UNIV \<rightarrow> S) = ?M x s'" by auto }
  note nat_case_f_eq = this

  have f_image_nonneg: "\<And>x s. s \<in> S \<Longrightarrow> x \<in> (\<lambda>\<omega>. f (nat_case s \<omega>)) ` (UNIV \<rightarrow> S) \<Longrightarrow> 0 \<le> x"
    by (auto intro!: nonneg)

  have "\<And>s. s \<in> S \<Longrightarrow>((\<lambda>\<omega>. f (nat_case s \<omega>)) ` (UNIV \<rightarrow> S)) \<subseteq> f ` (UNIV \<rightarrow> S)"
    by auto
  with simple_functionD[OF f]
  have finite_f_nat_case: "\<And>s. s \<in> S \<Longrightarrow> finite ((\<lambda>\<omega>. f (nat_case s \<omega>)) ` (UNIV \<rightarrow> S))"
    by simp (metis finite_subset)

  have "(\<Sum>s'\<in>S. ereal (\<tau> s s') * (\<Sum>x\<in>(\<lambda>\<omega>. f (nat_case s' \<omega>)) ` (UNIV \<rightarrow> S). x * P x s')) =
    (\<Sum>s'\<in>S. (\<Sum>x\<in>(\<lambda>\<omega>. f (nat_case s' \<omega>)) ` (UNIV \<rightarrow> S). x * ereal (\<tau> s s') * P x s'))"
    by (auto intro!: setsum_cong simp: setsum_ereal_right_distrib f_image_nonneg ac_simps)
  also have "\<dots> = (\<Sum>(s', x)\<in>(SIGMA s' : S. ((\<lambda>\<omega>. f (nat_case s' \<omega>)) ` (UNIV \<rightarrow> S))). x * ereal (\<tau> s s') * P x s')"
    by (intro setsum_Sigma finite_S ballI finite_f_nat_case)
  also have "(SIGMA s:S. (\<lambda>\<omega>. f (nat_case s \<omega>)) ` (UNIV \<rightarrow> S)) = (\<lambda>(x,y). (y,x)) ` (f ` (UNIV \<rightarrow> S) \<times> S \<inter> {(x, s). \<exists>\<omega> \<in> UNIV\<rightarrow>S. f (nat_case s \<omega>) = x})"
    by (auto simp: image_iff intro!: nat_case_in_S)
  also have "(\<Sum>(s', x)\<in>(\<lambda>(x,y). (y,x)) ` (f ` (UNIV \<rightarrow> S) \<times> S \<inter> {(x, s). \<exists>\<omega> \<in> UNIV\<rightarrow>S. f (nat_case s \<omega>) = x}). x * ereal (\<tau> s s') * P x s')
    = (\<Sum>(x, s')\<in>f ` (UNIV \<rightarrow> S) \<times> S. x * ereal (\<tau> s s') * P x s')"
    using simple_functionD[OF f]
    by (auto simp add: swap_inj_on setsum_reindex
             intro!: setsum_mono_zero_cong_left dest!: prob_eq_0_imp)
  also have "\<dots> = (\<Sum>x\<in>f ` (UNIV \<rightarrow> S). x * (\<Sum>s'\<in>S. ereal (\<tau> s s') * P x s'))"
    using `s \<in> S`
    by (auto intro!: setsum_cong
             simp: setsum_cartesian_product[symmetric] setsum_ereal_right_distrib ac_simps ereal_zero_le_0_iff)
  finally have "(\<Sum>s'\<in>S. ereal (\<tau> s s') * (\<Sum>x\<in>(\<lambda>\<omega>. f (nat_case s' \<omega>)) ` (UNIV \<rightarrow> S). x * P x s')) =
    (\<Sum>x\<in>f ` (UNIV \<rightarrow> S). x * (\<Sum>s'\<in>S. ereal (\<tau> s s') * P x s'))" .
  then show ?thesis
    unfolding simple_integral_def using simple_functionD[OF f]
    by (subst measure_eq_sum[OF `s \<in> S`])
       (auto simp add: nat_case_f_eq P_def emeasure_eq_measure simp del: vimage_Int intro!: setsum_cong)
qed
  
subsection {* Iterative equation for the Lebesgue integral *}

lemma positive_integral_eq_sum:
  assumes "s \<in> S" and f: "f \<in> borel_measurable p_space"
  shows "(\<integral>\<^isup>+x. f x \<partial>path_space s) = (\<Sum>s'\<in>S. \<tau> s s' * (\<integral>\<^isup>+x. f (nat_case s' x) \<partial>path_space s'))"
proof -
  have f': "f \<in> borel_measurable (path_space s)"
    using f by (simp cong: measurable_cong_sets)
  from borel_measurable_implies_simple_function_sequence'[OF f']
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
              simple_function_comp2 measurable_nat_case incseq_comp simple_integral_positive)
       (auto intro: measurable_nat_case cong: measurable_cong_sets simp: simple_function_def)
  also have "\<dots> = (\<Sum>s'\<in>S. \<tau> s s' * (SUP i. \<integral>\<^isup>Sx. (g i \<circ> nat_case s') x \<partial>path_space s'))"
    using g `s \<in> S`
    by (intro setsum_cong refl SUPR_ereal_cmult simple_integral_positive
                 simple_function_comp2)
       (auto intro: measurable_nat_case cong: measurable_cong_sets simp: simple_function_def)
  also have "\<dots> = (\<Sum>s'\<in>S. \<tau> s s' * (\<integral>\<^isup>+x. (SUP i. (g i \<circ> nat_case s') x) \<partial>path_space s'))"
    using g `s \<in> S`
    apply (intro setsum_cong refl)
    apply (subst positive_integral_monotone_convergence_simple)
    apply (auto intro!: simple_function_comp2 measurable_nat_case simple_integral_positive incseq_comp
                cong: measurable_cong_sets)
    apply (simp add: simple_function_def)
    done
  also have "\<dots> = (\<Sum>s'\<in>S. \<tau> s s' * (\<integral>\<^isup>+x. f (nat_case s' x) \<partial>path_space s'))"
    using g by (simp add: positive_integral_max_0)
  finally show ?thesis .
qed

lemma positive_integral_select_0:
  assumes "s \<in> S" "\<And>s. s \<in> S \<Longrightarrow> 0 \<le> f s"
  shows "(\<integral>\<^isup>+\<omega>. f (\<omega> 0) \<partial>path_space s) = (\<Sum>s'\<in>S. \<tau> s s' * f s')"
proof (subst positive_integral_eq_sum)
  show "(\<lambda>\<omega>. ereal (f (\<omega> 0))) \<in> borel_measurable p_space"
    apply (intro borel_measurable_ereal)
  proof (unfold measurable_def space_p_space, safe)
    fix i :: nat and A :: "real set" assume "A \<in> sets borel"
    have "(\<lambda>\<omega>. f (\<omega> 0)) -` A \<inter> (UNIV \<rightarrow> S) = {\<omega>\<in>UNIV\<rightarrow>S. \<omega> 0 \<in> f -` A}"
      by auto
    also have "\<dots> \<in> sets p_space"
      by (rule in_path_space_in_single)
    finally show "(\<lambda>\<omega>. f (\<omega> 0)) -` A \<inter> (UNIV \<rightarrow> S) \<in> sets p_space" .
  qed simp
qed (insert assms, auto simp add: emeasure_eq_measure)

subsection {* Iterative equation for the AE-quantifier *}

lemma AE_split:
  assumes ae: "AE \<omega> in path_space s. \<omega> \<in> A" and A: "A \<in> sets p_space"
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
  assumes s: "s \<in> S" and A: "{\<omega>\<in>space (path_space s). P \<omega>} \<in> sets p_space"
  shows "(AE \<omega> in path_space s. P \<omega>) \<longleftrightarrow>
    (\<forall>s'\<in>S. \<tau> s s' \<noteq> 0 \<longrightarrow> (AE \<omega> in path_space s'. P (nat_case s' \<omega>)))"
proof safe
  fix s' assume s': "s' \<in> S" "\<tau> s s' \<noteq> 0" and ae: "AE \<omega> in path_space s. P \<omega>"
  from ae s A show "AE \<omega> in path_space s'. P (nat_case s' \<omega>)"
    using AE_split[OF _ A s s'] AE_space[of "path_space s"]
    by simp
next
  assume *: "\<forall>s'\<in>S. \<tau> s s' \<noteq> 0 \<longrightarrow> (AE \<omega> in path_space s'. P (nat_case s' \<omega>))"

  show "AE \<omega> in path_space s. P \<omega>"
  proof (subst AE_iff_measurable[OF _ refl])
    show nP: "{\<omega>\<in>space (path_space s). \<not> P \<omega>} \<in> sets (path_space s)"
      using A by (auto intro: p_space_Collect)
    with s have "prob s {\<omega>\<in>space (path_space s). \<not> P \<omega>} =
      (\<Sum>s'\<in>S. \<tau> s s' * measure (path_space s') (nat_case s' -` {\<omega>\<in>space (path_space s). \<not> P \<omega>} \<inter> (UNIV\<rightarrow>S)))"
      unfolding sets_path_space
      by (rule prob_eq_sum)
    also have "\<dots> = (\<Sum>s'\<in>S. 0)"
    proof (safe intro!: setsum_cong)
      fix s' assume "s' \<in> S"
      show "\<tau> s s' * measure (path_space s') (nat_case s' -` {\<omega>\<in>space (path_space s). \<not> P \<omega>} \<inter> (UNIV\<rightarrow>S)) = 0"
      proof cases
        assume "\<tau> s s' \<noteq> 0"
        with `s' \<in> S` * have ae: "AE \<omega> in path_space s'. P (nat_case s' \<omega>)" by auto
        have "{\<omega>\<in>space (path_space s'). P (nat_case s' \<omega>)} =
          nat_case s' -` {\<omega>\<in>space (path_space s). P \<omega>} \<inter> space p_space"
          using `s' \<in> S` by (auto simp: space_path_space)
        also have "\<dots> \<in> sets p_space"
          using `s' \<in> S` A by (rule measurable_sets[OF measurable_nat_case])
        finally have "{\<omega>\<in>space (path_space s'). P (nat_case s' \<omega>)} \<in> sets (path_space s')"
          by simp
        from AE_E2[OF ae this] have "prob s' {x \<in> space (path_space s'). \<not> P (nat_case s' x)} = 0"
          by (simp add: measure_def)
        also have "{x \<in> space (path_space s'). \<not> P (nat_case s' x)} =
          nat_case s' -` {\<omega>\<in>space (path_space s). \<not> P \<omega>} \<inter> (UNIV\<rightarrow>S)"
          using `s' \<in> S` by auto
        finally show "\<tau> s s' * prob s' (nat_case s' -` {\<omega>\<in>space (path_space s). \<not> P \<omega>} \<inter> (UNIV\<rightarrow>S)) = 0"
          by simp
      qed simp
    qed
    finally show "emeasure (path_space s) {\<omega> \<in> space (path_space s). \<not> P \<omega>} = 0"
      by (simp add: emeasure_eq_measure)
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

lemma sets_until[simp, intro]: "until \<Phi> \<psi> \<in> sets p_space"
  by (auto simp: until_def intro!: p_space_Collect)

lemma sets_nat_case_until[simp, intro]: "s \<in> S \<Longrightarrow> nat_case s -` until \<Phi> \<psi> \<inter> (UNIV\<rightarrow>S) \<in> sets p_space"
  unfolding space_path_space[symmetric, of s] 
  using measurable_sets[OF measurable_nat_case sets_until] by simp

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
    using sums_0_iff[OF measure_nonneg[of "path_space s"], of X]
    by (auto simp add: sums_iff)
  also have "\<dots> \<longleftrightarrow> (\<forall>n. (\<Sum>\<omega>\<in>Pi\<^isub>E {.. n} (E n). \<Prod>i\<le>n. \<tau> (nat_case s \<omega> i) (\<omega> i)) = 0)"
    using assms unfolding X_def E_def by (subst prob_cylinder_eq_sum_prod') auto
  also have "\<dots> \<longleftrightarrow> (\<forall>n. \<forall>\<omega>\<in>Pi\<^isub>E {.. n} (E n). \<exists>i\<le>n. \<tau> (nat_case s \<omega> i) (\<omega> i) = 0)"
    using assms E_subset
    apply (subst setsum_nonneg_eq_0_iff)
    apply (auto intro!: setprod_nonneg
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
      using s0 assms unfolding E_def by (auto simp: le_less)
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
      using `s \<in> S` by (auto simp: until_def split: nat.split)
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

definition "Fair s t \<omega> \<longleftrightarrow> finite {i. \<omega> i = s \<and> \<omega> (Suc i) = t} \<longrightarrow> finite {i. \<omega> i = s}"

lemma Fair_eq: "Fair sx tx \<omega> \<longleftrightarrow>
  (\<exists>j. \<forall>i\<ge>j. \<omega> i \<noteq> sx) \<or> (\<forall>i. \<exists>j\<ge>i. \<omega> j = sx \<and> \<omega> (Suc j) = tx)"
  unfolding Fair_def finite_nat_set_iff_bounded
  unfolding disj_not2[symmetric]
  by (simp add: not_le not_less) blast

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
  { fix n have "\<And>s s' t. {\<omega> \<in> UNIV \<rightarrow> S. nat_case s' \<omega> n = t} \<in> sets p_space"
      by (cases n) (auto intro: p_space_Collect) }
  note sets_nat_case = this
  have sets_Never: "\<And>s s'. Never s' \<in> sets p_space"
    by (auto intro!: p_space_Collect sets_nat_case simp: Never_def)

  { fix s assume "s \<in> S"
    def Step \<equiv> "\<lambda>s n. Never s \<inter> {\<omega>\<in>UNIV\<rightarrow>S. (\<forall>i<n. \<omega> i \<noteq> sx) \<and> \<omega> n = sx}"
    then have sets_Step: "\<And>s' n. Step s' n \<in> sets p_space"
      by (auto intro!: Int p_space_Collect sets_nat_case sets_Never)

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
      show "range (Step s) \<subseteq> sets (path_space s)"
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
        show "?S`?I \<subseteq> sets (path_space s)"
          by (auto intro: sets_Step p_space_Collect)
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
      qed (auto intro!: p_space_Collect)
      finally have "prob s (Step s n) = prob s (UNION (?T n) (?P n)) * prob sx (Never sx)" . }
    ultimately have sums_Never: "(\<lambda>n. prob s (UNION (?T n) (?P n)) * prob sx (Never sx)) sums (prob s (Never s))"
      by simp

    have alt: "(\<lambda>n. prob s (UNION (?T n) (?P n))) sums (prob s (\<Union>n. UNION (?T n) (?P n)))"
    proof (rule finite_measure_UNION)
      show "range (\<lambda>n. UNION (?T n) (?P n)) \<subseteq> events s"
        unfolding sets_path_space
      proof (safe intro!: finite_UN p_space_Collect)
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
        by (auto intro!: finite_measure_mono p_space_Collect)
      also have "\<dots> = (if s = sx then (setsum (\<tau> s) (S-{tx})) else 1)"
        using `sx \<in> S` by (simp add: prob_single_eq_sum Diff_subset del: Diff_iff)
      also have "\<dots> \<le> (if s = sx then (1 - c) else 1)"
        using `tx \<in> S` `sx \<in> S` `\<tau> sx tx \<noteq> 0` by (simp add: setsum_diff \<tau>_distr c)
      finally show ?thesis using neq_0
        by (auto simp add: pos_divide_le_eq less_le measure_nonneg)
    qed }
  note Never_bounded = this
    
  { fix s assume "s \<in> S"
    from Never_bounded[OF `sx \<in> S`]
    have "prob sx (Never sx) = 0"
      using `0 < c` measure_nonneg[of "path_space sx" "Never sx"]
      by (simp add: field_simps mult_le_0_iff)
    with Never_bounded[OF `s \<in> S`] measure_nonneg[of "path_space s" "Never s"]
    have "prob s (Never s) = 0"
      by (simp split: split_if_asm) }
  note Never_eq_0 = this

  have sets_Fair: "{\<omega>\<in>UNIV\<rightarrow>S. Fair sx tx (nat_case s \<omega>) } \<in> sets p_space"
    unfolding Fair_eq by (auto intro!: p_space_Collect sets_nat_case)
  have sets_sN: "\<And>n. {\<omega>\<in>UNIV\<rightarrow>S. nat_case s \<omega> n = sx} \<inter> ((\<lambda>\<omega> i. \<omega> (i + n)) -` Never sx \<inter> space (path_space s)) \<in> sets p_space"
    (is "\<And>n. ?sN n \<in> _")
    by (auto intro!: sets_nat_case measurable_shift sets_Never p_space_Collect p_space_measurable
             simp: Collect_Int2)

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
    by (intro allI AE_not_in) (auto simp: emeasure_eq_measure)
  then show "AE \<omega> in path_space s. Fair sx tx (nat_case s \<omega>)"
  proof (elim AE_mp, safe intro!: AE_I2)
    fix \<omega> assume \<omega>: "\<omega> \<in> space (path_space s)" "\<forall>n. \<omega> \<notin> ?sN n"
    show "Fair sx tx (nat_case s \<omega>)"
      unfolding Fair_eq
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
        unfolding Fair_eq
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
    by (auto simp:)
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
    qed (auto intro: p_space_Collect)
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
  qed (auto intro: p_space_Collect)
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

lemma measurable_hitting_time[measurable]:
  "hitting_time \<Phi> \<in> measurable p_space (count_space UNIV)"
  unfolding hitting_time_def[abs_def]
  by measurable

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
  
  have "0 \<le> N s" by (auto simp: N_def measure_nonneg)
  also have "N s \<le> M" using s by (intro M_ge) auto
  finally have M_nneg: "0 \<le> M" by simp
    
  def T \<equiv> "\<lambda>k'::nat. {\<omega>\<in>UNIV\<rightarrow>S. (\<forall>i<k'. \<omega> i \<notin> \<Phi>)}"
  then have T_measurable[simp, intro]: "\<And>k s. T k \<in> sets p_space"
    by (auto intro!: p_space_Collect)
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
         (auto intro!: p_space_Collect)
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
      by (auto simp: measure_nonneg) }
  then have estimate: "\<forall>k. \<bar>prob s (T (k + n))\<bar> \<le> root (Suc n) M ^ k" ..

  have "norm (root (Suc n) M) < 1"
    using `M < 1` `0 \<le> M` by auto
  from geometric_sums[OF this]
  have "summable (op ^ (root (Suc n) M))" by (simp add: sums_iff)
  from summable_le2[OF estimate this]
  have "summable (\<lambda>k. prob s (T (k + n)))" ..
  then have "summable (\<lambda>k. prob s (T k))"
    by (rule sums_shift)
  then have T_sums: "(\<lambda>k. emeasure (path_space s) (T k)) sums (ereal (\<Sum>k. prob s (T k)))"
    using T_measurable
    by (auto simp add: emeasure_eq_measure sums_ereal) (simp add: sums_iff)
  

  from until
  have t_imp_T: "\<And>N. AE \<omega> in path_space s. \<omega> \<in> UNIV \<rightarrow> S \<and> N < hitting_time \<Phi> \<omega> \<longrightarrow> \<omega> \<in> T N"
  proof (elim AE_mp, intro AE_I2 impI)
    fix \<omega> N assume \<omega>: "\<omega> \<in> space (path_space s)" "nat_case s \<omega> \<in> until S \<Phi>" "\<omega> \<in> UNIV \<rightarrow> S \<and> N < hitting_time \<Phi> \<omega>"
    show "\<omega> \<in> T N"
      unfolding T_def
    proof safe
      fix i
      assume "\<omega> i \<in> \<Phi>"
      then have "hitting_time \<Phi> \<omega> \<le> i"
        unfolding hitting_time_def by (rule Least_le)
      also assume "i < N"
      finally have "hitting_time \<Phi> \<omega> < N" .
      then show False using `\<omega> \<in> UNIV \<rightarrow> S \<and> N < hitting_time \<Phi> \<omega>` by simp
    qed (insert \<omega>, auto simp: space_path_space)
  qed

  note positive_integral_nat_function[of "hitting_time \<Phi>" "path_space s"] measurable_hitting_time
  moreover have "\<And>i. (real_of_nat \<circ> hitting_time \<Phi>) -` {of_nat i <..} \<inter> space (path_space s) =
    {\<omega>\<in>UNIV\<rightarrow>S. real_of_nat i < real_of_nat (hitting_time \<Phi> \<omega>)}"
    by (auto simp: )
  ultimately have "(\<integral>\<^isup>+ \<omega>. ereal (of_nat (hitting_time \<Phi> \<omega>)) \<partial>path_space s) =
    (\<Sum>i. emeasure (path_space s) {\<omega>\<in>space (path_space s). real_of_nat i < real_of_nat (hitting_time \<Phi> \<omega>)})"
    by (simp add: emeasure_nonneg cong: measurable_cong_sets)
  also have "\<dots> \<le> (\<Sum>i. emeasure (path_space s) (T i))"
    using measurable_hitting_time t_imp_T AE_space[of "path_space s"]
    by (intro suminf_le_pos emeasure_nonneg borel_measurable_less emeasure_mono_AE T_measurable)
       (auto simp add: comp_def cong: measurable_cong_sets)
  also have "\<dots> < \<infinity>"
    using T_sums unfolding sums_iff by simp
  finally have "integral\<^isup>P (path_space s) (real_of_nat \<circ> hitting_time \<Phi>) \<noteq> \<infinity>"
    by simp
  then have "\<infinity> \<noteq> (\<integral>\<^isup>+ \<omega>. 1 + ereal (real_of_nat (hitting_time \<Phi> \<omega>)) \<partial>path_space s)"
    by (subst positive_integral_add)  (auto simp: comp_def cong: measurable_cong_sets)
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
  "\<PP>(x in M. P)" => "CONST measure M {x \<in> CONST space M. P}"

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
    apply (simp add: cylinder_forms prob_ball_cylinder del: ball_simps insert_iff space_path_space)
    apply (simp add: setsum_PiE_insert * setsum_right_distrib[symmetric]
                cong: nat.case_cong)
    done
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
      using neq0 by (simp add: less_le measure_nonneg)
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
      by (auto simp: Pi_iff) metis
    with neq0 show ?thesis by (simp add: measure_nonneg del: space_path_space)
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

end
