(*  Title:       Countable Ordinals
    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Veblen Hierarchies\<close>

theory OrdinalVeblen
imports OrdinalOmega
begin

subsection \<open>Closed, unbounded sets\<close>

locale normal_set =
fixes A :: "ordinal set"
assumes closed:    "\<And>g. \<forall>n. g n \<in> A \<Longrightarrow> oLimit g \<in> A"
    and unbounded: "\<And>x. \<exists>y\<in>A. x < y"

lemma (in normal_set) less_next: "x < (LEAST z. z \<in> A \<and> x < z)"
  by (metis (no_types, lifting) LeastI unbounded)

lemma (in normal_set) mem_next: "(LEAST z. z \<in> A \<and> x < z) \<in> A"
  by (metis (no_types, lifting) LeastI unbounded)

lemma (in normal) normal_set_range: "normal_set (range F)"
proof (rule normal_set.intro)
  fix g :: "nat \<Rightarrow> ordinal"
  assume "\<forall>n. g n \<in> range F"
  then have "\<And>n. g n = F (LEAST z. g n = F z)"
    by (meson LeastI rangeE)
  then have "oLimit g = F (oLimit (\<lambda>n. LEAST z. g n = F z))"
    by (simp add: continuousD continuous_axioms)
  then show "oLimit g \<in> range F"
    by simp
next 
  show "\<And>x. \<exists>y\<in>range F. x < y"
    using oInv_bound2 by blast
qed

lemma oLimit_mem_INTER:
  assumes norm: "\<forall>n. normal_set (A n)" 
    and A: "\<forall>n. A (Suc n) \<subseteq> A n" "\<forall>n. f n \<in> A n" and "mono f"
  shows "oLimit f \<in> (\<Inter>n. A n)"
proof
  fix k
  have "f (n + k) \<in> A k" for n
    using A le_add2 lift_Suc_antimono_le by blast
  then have "oLimit (\<lambda>n. f (n + k)) \<in> A k"
    by (simp add: norm normal_set.closed)
  then show "oLimit f \<in> A k"
    by (simp add: \<open>mono f\<close> oLimit_shift_mono)
qed

lemma normal_set_INTER:
  assumes norm: "\<forall>n. normal_set (A n)"  and A: "\<forall>n. A (Suc n) \<subseteq> A n"
  shows "normal_set (\<Inter>n. A n)"
proof (rule normal_set.intro)
  fix g :: "nat \<Rightarrow> ordinal"
  assume "\<forall>n. g n \<in> \<Inter> (range A)"
  then show "oLimit g \<in> \<Inter> (range A)"
    using norm normal_set.closed by force
next
  fix x
  define F where "F \<equiv> \<lambda>n. LEAST y. y \<in> A n \<and> x < y"
  have "x < oLimit F"
    by (simp add: F_def less_oLimitI norm normal_set.less_next)
  moreover 
  have \<section>: "F n \<in> A n" for n
    by (simp add: F_def norm normal_set.mem_next)
  then have "F n \<le> F (Suc n)" for n
    unfolding F_def
    by (metis (no_types, lifting) A LeastI Least_le norm normal_set_def subsetD)
  then have "oLimit F \<in> \<Inter> (range A)"
    by (meson "\<section>" A mono_natI norm oLimit_mem_INTER)
  ultimately show "\<exists>y\<in>\<Inter> (range A). x < y"
    by blast
qed

subsection \<open>Ordering functions\<close>

text "There is a one-to-one correspondence between closed,
unbounded sets of ordinals and normal functions on ordinals."

definition
  ordering  :: "(ordinal set) \<Rightarrow> (ordinal \<Rightarrow> ordinal)" where
  "ordering A = ordinal_rec (LEAST z. z \<in> A) (\<lambda>p x. LEAST z. z \<in> A \<and> x < z)"

lemma ordering_0:
  "ordering A 0 = (LEAST z. z \<in> A)"
  by (simp add: ordering_def)

lemma ordering_oSuc:
  "ordering A (oSuc x) = (LEAST z. z \<in> A \<and> ordering A x < z)"
  by (simp add: ordering_def)

lemma (in normal_set) normal_ordering: "normal (ordering A)"
  by (simp add: OrdinalVeblen.ordering_def normal_ordinal_rec normal_set.less_next normal_set_axioms)

lemma (in normal_set) ordering_oLimit: "ordering A (oLimit f) = oLimit (\<lambda>n. ordering A (f n))"
  by (simp add: normal.oLimit normal_ordering)

lemma (in normal) ordering_range: "ordering (range F) = F"
proof
  fix x
  show "ordering (range F) x = F x"
  proof (induction x rule: oLimit_induct)
    case zero
    have "(LEAST z. z \<in> range F) = F 0"
      by (metis Least_equality Least_mono UNIV_I mono ordinal_0_le)
    then show ?case
      by (simp add: ordering_0)
  next
    case (suc x)
    have "ordering (range F) (oSuc x) = (LEAST z. z \<in> range F \<and> F x < z)"
      by (simp add: ordering_oSuc suc)
    also have "\<dots> = F (oSuc x)"
      using cancel_less less_oInvD oInv_inverse 
      by (bestsimp intro!: Least_equality local.strict_monoD)
    finally show ?case .
  next
    case (lim f)
    then show ?case
      using oLimit by (simp add: normal_set_range normal_set.ordering_oLimit)
  qed
qed

lemma (in normal_set) ordering_mem: "ordering A x \<in> A"
proof (induction x rule: oLimit_induct)
  case zero
  then show ?case
    by (metis LeastI ordering_0 unbounded)
 next
  case (suc x)
  then show ?case
    by (simp add: mem_next ordering_oSuc)
next
  case (lim f)
  then show ?case
    by (simp add: closed normal.oLimit normal_ordering)
qed

lemma (in normal_set) range_ordering: "range (ordering A) = A"
proof -
  have "\<forall>y. y \<in> A \<longrightarrow> y < ordering A x \<longrightarrow> y \<in> range (ordering A)" for x
  proof (induction x rule: oLimit_induct)
    case zero
    then show ?case
      using not_less_Least ordering_0 by auto
  next
    case (suc x)
    then show ?case
      using not_less_Least ordering_oSuc by fastforce
  next
    case (lim f)
    then show ?case
      by (metis less_oLimitD ordering_oLimit)
  qed
  then show ?thesis
    using normal.oInv_bound2 normal_ordering ordering_mem by fastforce
qed

lemma ordering_INTER_0:
  assumes norm: "\<forall>n. normal_set (A n)"  and A: "\<forall>n. A (Suc n) \<subseteq> A n"
  shows "ordering (\<Inter>n. A n) 0 = oLimit (\<lambda>n. ordering (A n) 0)"
proof -
  have "oLimit (\<lambda>n. OrdinalVeblen.ordering (A n) 0) \<in> \<Inter> (range A)"
    using assms
    by (metis (mono_tags, lifting) Least_le mono_natI normal_set.ordering_mem oLimit_mem_INTER ordering_0 subsetD)
  moreover have "\<And>y. y \<in> \<Inter> (range A) \<Longrightarrow> oLimit (\<lambda>n. ordering (A n) 0) \<le> y"
  by (simp add: Least_le oLimit_def ordering_0)
  ultimately show ?thesis
    by (metis LeastI Least_le nle_le ordering_0)
qed


subsection \<open>Critical ordinals\<close>

definition
  critical_set :: "ordinal set \<Rightarrow> ordinal \<Rightarrow> ordinal set" where
  "critical_set A =
     ordinal_rec0 A (\<lambda>p x. x \<inter> range (oDeriv (ordering x))) (\<lambda>f. \<Inter>n. f n)"

lemma critical_set_0 [simp]: "critical_set A 0 = A"
  by (simp add: critical_set_def)

lemma critical_set_oSuc_lemma:
  "critical_set A (oSuc n) = critical_set A n \<inter> range (oDeriv (ordering (critical_set A n)))"
  by (simp add: critical_set_def ordinal_rec0_oSuc)

lemma omega_complete_INTER: "omega_complete (\<lambda>x y. y \<subseteq> x) (\<lambda>f. \<Inter> (range f))"
  by (simp add: INF_greatest Inf_lower omega_complete_axioms_def omega_complete_def porder.flip porder_order)

lemma critical_set_oLimit: "critical_set A (oLimit f) = (\<Inter>n. critical_set A (f n))"
  unfolding critical_set_def
  by (best intro!: omega_complete.ordinal_rec0_oLimit omega_complete_INTER)

lemma critical_set_mono: "x \<le> y \<Longrightarrow> critical_set A y \<subseteq> critical_set A x"
  unfolding critical_set_def
  by (intro omega_complete.ordinal_rec0_mono [OF omega_complete_INTER]) force

lemma (in normal_set) range_oDeriv_subset: "range (oDeriv (ordering A)) \<subseteq> A"
  by (metis image_subsetI normal_ordering oDeriv_fixed rangeI range_ordering)

lemma normal_set_critical_set: "normal_set A \<Longrightarrow> normal_set (critical_set A x)"
proof (induction x rule: oLimit_induct)
  case zero
  then show ?case
    by simp
next
  case (suc x)
  then show ?case
    by (simp add: Int_absorb1 critical_set_oSuc_lemma normal.normal_set_range normal_oDeriv normal_set.range_oDeriv_subset)
next
  case (lim f)
  then show ?case
    unfolding critical_set_oLimit
    by (meson critical_set_mono lessI normal_set_INTER order_le_less strict_mono.strict_mono)
qed

lemma critical_set_oSuc: 
  "normal_set A \<Longrightarrow> critical_set A (oSuc x) = range (oDeriv (ordering (critical_set A x)))"
  by (metis critical_set_oSuc_lemma inf.absorb_iff2 normal_set.range_oDeriv_subset normal_set_critical_set)


subsection \<open>Veblen hierarchy over a normal function\<close>

definition
  oVeblen :: "(ordinal \<Rightarrow> ordinal) \<Rightarrow> ordinal \<Rightarrow> ordinal \<Rightarrow> ordinal" where
  "oVeblen F = (\<lambda>x. ordering (critical_set (range F) x))"

lemma (in normal) oVeblen_0: "oVeblen F 0 = F"
  by (simp add: normal.ordering_range normal_axioms oVeblen_def)

lemma (in normal) oVeblen_oSuc: "oVeblen F (oSuc x) = oDeriv (oVeblen F x)"
  using critical_set_oSuc normal.normal_set_range normal.ordering_range normal_axioms normal_oDeriv oVeblen_def by presburger

lemma (in normal) oVeblen_oLimit:
"oVeblen F (oLimit f) = ordering (\<Inter>n. range (oVeblen F (f n)))"
 unfolding oVeblen_def
  using critical_set_oLimit normal_set.range_ordering normal_set_critical_set normal_set_range by presburger

lemma (in normal) normal_oVeblen: "normal (oVeblen F x)"
 unfolding oVeblen_def
  by (simp add: normal_set.normal_ordering normal_set_critical_set normal_set_range)

lemma (in normal) continuous_oVeblen_0: "continuous (\<lambda>x. oVeblen F x 0)"
proof (rule continuousI)
  fix f:: "nat \<Rightarrow> ordinal"
  assume f: "OrdinalInduct.strict_mono f"
  have "normal_set (critical_set (range F) (f n))" for n
    using normal_set_critical_set normal_set_range by blast
  moreover
  have "critical_set (range F) (f (Suc n)) \<subseteq> critical_set (range F) (f n)" for n
    by (simp add: f critical_set_mono strict_mono_monoD)
  ultimately show "oVeblen F (oLimit f) 0 = oLimit (\<lambda>n. oVeblen F (f n) 0)"
    using ordering_INTER_0 by (simp add: oVeblen_def critical_set_oLimit)
next
  show "\<And>x. oVeblen F x 0 \<le> oVeblen F (oSuc x) 0"
    by (simp add: le_oFix1 oVeblen_oSuc)
qed

lemma (in normal) oVeblen_oLimit_0:
  "oVeblen F (oLimit f) 0 = oLimit (\<lambda>n. oVeblen F (f n) 0)"
  by (rule continuousD[OF continuous_oVeblen_0])

lemma (in normal) normal_oVeblen_0:
  assumes "0 < F 0" shows "normal (\<lambda>x. oVeblen F x 0)"
proof -
  { fix x
    have "0 < oVeblen F x 0"
      by (metis leD ordinal_0_le ordinal_neq_0 continuous.monoD continuous_oVeblen_0 oVeblen_0 assms)
    then have "oVeblen F x 0 < oVeblen F x (oDeriv (oVeblen F x) 0)"
      by (simp add: normal.strict_monoD normal_oVeblen zero_less_oFix_eq)
    then have "oVeblen F x 0 < oVeblen F (oSuc x) 0"
      by (metis normal_oVeblen oDeriv_fixed oVeblen_oSuc) 
  }
  then show ?thesis
    using continuous_def continuous_oVeblen_0 normalI by blast
qed

lemma (in normal) range_oVeblen:
  "range (oVeblen F x) = critical_set (range F) x"
  unfolding oVeblen_def
  using normal_set.range_ordering normal_set_critical_set normal_set_range by blast

lemma (in normal) range_oVeblen_subset:
  "x \<le> y \<Longrightarrow> range (oVeblen F y) \<subseteq> range (oVeblen F x)"
  using critical_set_mono range_oVeblen by presburger

lemma (in normal) oVeblen_fixed:
  assumes "x<y"
  shows "oVeblen F x (oVeblen F y a) = oVeblen F y a"
  using assms
proof (induction y arbitrary: x a rule: oLimit_induct)
  case zero
  then show ?case
    by auto
next
  case (suc u)
  then show ?case
    by (metis antisym_conv3 leD normal_oVeblen oDeriv_fixed oSuc_le_eq_less oVeblen_oSuc)
next
  case (lim f x a)
  then obtain n where "x < f n"
    using less_oLimitD by blast
  have "oVeblen F (oLimit f) a \<in> range (oVeblen F (f n))"
    by (simp add: range_oVeblen_subset range_subsetD)
  then show ?case
    using lim.IH \<open>x < f n\<close> by force
qed

lemma (in normal) critical_set_fixed:
  assumes "0 < z" 
  shows "range (oVeblen F z) = {x. \<forall>y<z. oVeblen F y x = x}" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R"
    using oVeblen_fixed by auto
  have "{x. \<forall>y<z. oVeblen F y x = x} \<subseteq> range (oVeblen F z)"
    using assms
  proof (induction z rule: oLimit_induct)
    case zero
    then show ?case by auto
  next
    case (suc x)
    then show ?case
      by (force simp: normal_oVeblen oVeblen_oSuc range_oDeriv)
  next
    case (lim f)
    show ?case
    proof clarsimp
      fix x
      assume "\<forall>y<oLimit f. oVeblen F y x = x"
      then have "x \<in> critical_set (range F) (f n)" for n
        by (metis lim.hyps rangeI range_oVeblen strict_mono_less_oLimit)
      then show "x \<in> range (oVeblen F (oLimit f))"
        by (simp add: range_oVeblen critical_set_oLimit)
    qed
  qed
  then show "?R \<subseteq> ?L"
    by blast
qed

subsection \<open>Veblen hierarchy over $\lambda x.\ 1 + x$\<close>

lemma oDeriv_id: "oDeriv id = id"
proof
  fix x show "oDeriv id x = id x"
    by (induction x rule: oLimit_induct) (auto simp add: oFix_eq_self)
qed

lemma oFix_plus: "oFix (\<lambda>x. a + x) 0 = a * \<omega>"
proof -
  have "iter n ((+) a) 0 = a * ordinal_of_nat n" for n
  proof (induction n)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    have "a + a * ordinal_of_nat n = a * ordinal_of_nat n + a" for n
      by (induction n) (simp_all flip: ordinal_plus_assoc)
    with Suc show ?case by simp
  qed
  then show ?thesis
    by (simp add: oFix_def omega_def)
qed

lemma oDeriv_plus: "oDeriv ((+) a) = ((+) (a * \<omega>))"
proof
  show "oDeriv ((+) a) x = a * \<omega> + x" for x
  proof (induction x rule: oLimit_induct)
    case (suc x)
    then show ?case 
      by (simp add: oFix_eq_self ordinal_plus_absorb)
  qed (auto simp: oFix_plus)
qed


lemma oVeblen_1_plus: "oVeblen ((+) 1) x = ((+) (\<omega> ** x))"
  using wf
proof (induction x rule: wf_induct_rule)
  case (less x)
  have "oVeblen ((+) (oSuc 0)) x = (+) (\<omega> ** x)"
  proof (cases x rule: ordinal_cases)
    case zero
    then show ?thesis
      by (simp add: normal.oVeblen_0 normal_plus)
  next
    case (suc y)
    with less show ?thesis
      by (simp add: normal.oVeblen_oSuc[OF normal_plus] oDeriv_plus)
  next
    case (lim f)
    show ?thesis
    proof (rule normal_range_eq)
      show "normal (oVeblen ((+) (oSuc 0)) x)"
        using normal.normal_oVeblen normal_plus by blast
      show "normal ((+) (\<omega> ** x))"
        using normal_plus by blast
      have "\<forall>y<oLimit f. \<omega> ** y + u = u \<Longrightarrow> u \<in> range ((+) (oLimit (\<lambda>n. \<omega> ** f n)))" for u
        by (metis rangeI lim oLimit_leI ordinal_le_plusR strict_mono_less_oLimit ordinal_plus_minus2)
      moreover 
      have "\<omega> ** y + (oLimit (\<lambda>n. \<omega> ** f n) + u) = oLimit (\<lambda>n. \<omega> ** f n) + u" 
        if "y < oLimit f" for u y
        by (metis absorb_omega_exp2 ordinal_exp_oLimit ordinal_plus_assoc that zero_less_omega)
      ultimately show "range (oVeblen ((+) (oSuc 0)) x) = range ((+) (\<omega> ** x))"
        using less lim
        by (force simp add: strict_mono_limit_ordinal normal.critical_set_fixed[OF normal_plus])
    qed
  qed
  then show ?case
    by simp
qed

end
