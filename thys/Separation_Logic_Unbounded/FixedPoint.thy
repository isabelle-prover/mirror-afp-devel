section \<open>(Co)Inductive Predicates\<close>

text \<open>This subsection corresponds to Section 4 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

theory FixedPoint
  imports Distributivity Combinability
begin

type_synonym ('d, 'c, 'a) chain = "nat \<Rightarrow> ('d, 'c, 'a) interp"

context logic
begin

subsection Definitions

definition smaller_interp :: "('d, 'c, 'a) interp \<Rightarrow> ('d, 'c, 'a) interp \<Rightarrow> bool" where
  "smaller_interp \<Delta> \<Delta>' \<longleftrightarrow> (\<forall>s. \<Delta> s \<subseteq> \<Delta>' s)"

lemma smaller_interpI:
  assumes "\<And>s x. x \<in> \<Delta> s \<Longrightarrow> x \<in> \<Delta>' s"
  shows "smaller_interp \<Delta> \<Delta>'"
  by (simp add: assms smaller_interp_def subsetI)

definition indep_interp where
  "indep_interp A \<longleftrightarrow> (\<forall>x s \<Delta> \<Delta>'. x, s, \<Delta> \<Turnstile> A \<longleftrightarrow> x, s, \<Delta>' \<Turnstile> A)"

fun applies_eq :: "('a, 'b, 'c, 'd) assertion \<Rightarrow> ('d, 'c, 'a) interp \<Rightarrow> ('d, 'c, 'a) interp" where
  "applies_eq A \<Delta> s = { a |a. a, s, \<Delta> \<Turnstile> A }"

definition monotonic :: "(('d, 'c, 'a) interp \<Rightarrow> ('d, 'c, 'a) interp) \<Rightarrow> bool" where
  "monotonic f \<longleftrightarrow> (\<forall>\<Delta> \<Delta>'. smaller_interp \<Delta> \<Delta>' \<longrightarrow> smaller_interp (f \<Delta>) (f \<Delta>'))"

lemma monotonicI:
  assumes "\<And>\<Delta> \<Delta>'. smaller_interp \<Delta> \<Delta>' \<Longrightarrow> smaller_interp (f \<Delta>) (f \<Delta>')"
  shows "monotonic f"
  by (simp add: assms monotonic_def)

definition non_increasing :: "(('d, 'c, 'a) interp \<Rightarrow> ('d, 'c, 'a) interp) \<Rightarrow> bool" where
  "non_increasing f \<longleftrightarrow> (\<forall>\<Delta> \<Delta>'. smaller_interp \<Delta> \<Delta>' \<longrightarrow> smaller_interp (f \<Delta>') (f \<Delta>))"

lemma non_increasingI:
  assumes "\<And>\<Delta> \<Delta>'. smaller_interp \<Delta> \<Delta>' \<Longrightarrow> smaller_interp (f \<Delta>') (f \<Delta>)"
  shows "non_increasing f"
  by (simp add: assms non_increasing_def)


lemma smaller_interp_refl:
  "smaller_interp \<Delta> \<Delta>"
  by (simp add: smaller_interp_def)


lemma smaller_interp_applies_cons:
  assumes "smaller_interp (applies_eq A \<Delta>) (applies_eq A \<Delta>')"
      and "a, s, \<Delta> \<Turnstile> A"
    shows "a, s, \<Delta>' \<Turnstile> A"
proof -
  have "a \<in> applies_eq A \<Delta> s"
    using assms(2) by force
  then have "a \<in> applies_eq A \<Delta>' s"
    by (metis assms(1) in_mono smaller_interp_def)
  then show ?thesis by auto
qed

definition empty_interp where
  "empty_interp s = {}"

definition full_interp :: "('d, 'c, 'a) interp" where
  "full_interp s = UNIV"

lemma smaller_interp_trans:
  assumes "smaller_interp a b"
      and "smaller_interp b c"
    shows "smaller_interp a c"
  by (metis assms(1) assms(2) dual_order.trans smaller_interp_def)

lemma smaller_empty:
  "smaller_interp empty_interp x"
  by (simp add: empty_interp_def smaller_interp_def)

text \<open>The definition of set-closure properties corresponds to Definition 8 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

definition set_closure_property :: "('a \<Rightarrow> 'a \<Rightarrow> 'a set) \<Rightarrow> ('d, 'c, 'a) interp \<Rightarrow> bool" where
  "set_closure_property S \<Delta> \<longleftrightarrow> (\<forall>a b s. a \<in> \<Delta> s \<and> b \<in> \<Delta> s \<longrightarrow> S a b \<subseteq> \<Delta> s)"

lemma set_closure_propertyI:
  assumes "\<And>a b s. a \<in> \<Delta> s \<and> b \<in> \<Delta> s \<Longrightarrow> S a b \<subseteq> \<Delta> s"
  shows "set_closure_property S \<Delta>"
  by (simp add: assms set_closure_property_def)

lemma set_closure_property_instantiate:
  assumes "set_closure_property S \<Delta>"
      and "a \<in> \<Delta> s"
      and "b \<in> \<Delta> s"
      and "x \<in> S a b"
    shows "x \<in> \<Delta> s"
  using assms subsetD set_closure_property_def by metis





























subsection \<open>Everything preserves monotonicity\<close>


lemma indep_implies_non_increasing:
  assumes "indep_interp A"
  shows "non_increasing (applies_eq A)"
  by (metis (no_types, lifting) applies_eq.simps assms indep_interp_def smaller_interp_def mem_Collect_eq non_increasingI subsetI)

subsubsection Monotonicity

lemma mono_instantiate:
  assumes "monotonic (applies_eq A)"
      and "x \<in> applies_eq A \<Delta> s"
      and "smaller_interp \<Delta> \<Delta>'"
    shows "x \<in> applies_eq A \<Delta>' s"
  using assms(1) assms(2) assms(3) monotonic_def smaller_interp_applies_cons by fastforce

lemma mono_star:
  assumes "monotonic (applies_eq A)"
      and "monotonic (applies_eq B)"
    shows "monotonic (applies_eq (Star A B))"
proof (rule monotonicI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (Star A B) \<Delta>) (applies_eq (Star A B) \<Delta>')"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Star A B) \<Delta> s"
    then obtain a b where "Some x = a \<oplus> b" "a \<in> applies_eq A \<Delta> s" "b \<in> applies_eq B \<Delta> s"
      by auto
    then have "a \<in> applies_eq A \<Delta>' s \<and> b \<in> applies_eq B \<Delta>' s"
      by (meson asm0 assms(1) assms(2) mono_instantiate)
    then show "x \<in> applies_eq (Star A B) \<Delta>' s"
      using \<open>Some x = a \<oplus> b\<close> by force
  qed
qed


lemma mono_wand:
  assumes "non_increasing (applies_eq A)"
      and "monotonic (applies_eq B)"
    shows "monotonic (applies_eq (Wand A B))"
proof (rule monotonicI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (Wand A B) \<Delta>) (applies_eq (Wand A B) \<Delta>')"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Wand A B) \<Delta> s"
    have "x, s, \<Delta>' \<Turnstile> Wand A B"
    proof (rule sat_wand)
      fix a b
      assume asm2: "a, s, \<Delta>' \<Turnstile> A \<and> Some b = x \<oplus> a"
      then have "a, s, \<Delta> \<Turnstile> A"
        by (meson asm0 assms(1) non_increasing_def smaller_interp_applies_cons)
      then have "b, s, \<Delta> \<Turnstile> B"
        using asm1 asm2 by auto
      then show "b, s, \<Delta>' \<Turnstile> B"
        by (meson asm0 assms(2) monotonic_def smaller_interp_applies_cons)
    qed
    then show "x \<in> applies_eq (Wand A B) \<Delta>' s"
      by simp
  qed
qed



lemma mono_and:
  assumes "monotonic (applies_eq A)"
      and "monotonic (applies_eq B)"
    shows "monotonic (applies_eq (And A B))"
proof (rule monotonicI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (And A B) \<Delta>) (applies_eq (And A B) \<Delta>')"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (And A B) \<Delta> s"
    then show "x \<in> applies_eq (And A B) \<Delta>' s"
      using asm0 assms(1) assms(2) monotonic_def logic_axioms mem_Collect_eq sat.simps(8) smaller_interp_applies_cons by fastforce
  qed
qed

lemma mono_or:
  assumes "monotonic (applies_eq A)"
      and "monotonic (applies_eq B)"
    shows "monotonic (applies_eq (Or A B))"
proof (rule monotonicI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (Or A B) \<Delta>) (applies_eq (Or A B) \<Delta>')"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Or A B) \<Delta> s"
    then show "x \<in> applies_eq (Or A B) \<Delta>' s"
      using asm0 assms(1) assms(2) monotonic_def logic_axioms mem_Collect_eq sat.simps(8) smaller_interp_applies_cons by fastforce
  qed
qed

lemma mono_sem:
  "monotonic (applies_eq (Sem B))"
  using monotonic_def smaller_interp_def by fastforce

lemma mono_interp:
  "monotonic (applies_eq Pred)"
proof (rule monotonicI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq Pred \<Delta>) (applies_eq Pred \<Delta>')"
  proof (rule smaller_interpI)
    fix s x assume "x \<in> applies_eq Pred \<Delta> s"
    then show "x \<in> applies_eq Pred \<Delta>' s"
      by (metis (mono_tags, lifting) \<open>smaller_interp \<Delta> \<Delta>'\<close> applies_eq.simps in_mono mem_Collect_eq sat.simps(10) smaller_interp_def)
  qed
qed


lemma mono_mult:
  assumes "monotonic (applies_eq A)"
  shows "monotonic (applies_eq (Mult \<pi> A))"
proof (rule monotonicI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (Mult \<pi> A) \<Delta>) (applies_eq (Mult \<pi> A) \<Delta>')"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Mult \<pi> A) \<Delta> s"
    then show "x \<in> applies_eq (Mult \<pi> A) \<Delta>' s"
      using asm0 assms monotonic_def smaller_interp_applies_cons by fastforce
  qed
qed

lemma mono_wild:
  assumes "monotonic (applies_eq A)"
  shows "monotonic (applies_eq (Wildcard A))"
proof (rule monotonicI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (Wildcard A) \<Delta>) (applies_eq (Wildcard A) \<Delta>')"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Wildcard A) \<Delta> s"
    then show "x \<in> applies_eq (Wildcard A) \<Delta>' s"
      using asm0 assms monotonic_def smaller_interp_applies_cons by fastforce
  qed
qed


lemma mono_imp:
  assumes "non_increasing (applies_eq A)"
      and "monotonic (applies_eq B)"
    shows "monotonic (applies_eq (Imp A B))"
proof (rule monotonicI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (Imp A B) \<Delta>) (applies_eq (Imp A B) \<Delta>')"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Imp A B) \<Delta> s"
    have "x, s, \<Delta>' \<Turnstile> Imp A B"
    proof (cases "x, s, \<Delta>' \<Turnstile> A")
      case True
      then have "x, s, \<Delta> \<Turnstile> A"
        by (meson asm0 assms(1) non_increasing_def smaller_interp_applies_cons)
      then have "x, s, \<Delta> \<Turnstile> B"
        using asm1 by auto
      then show ?thesis
        by (metis asm0 assms(2) monotonic_def sat.simps(5) smaller_interp_applies_cons)
    next
      case False
      then show ?thesis by simp
    qed
    then show "x \<in> applies_eq (Imp A B) \<Delta>' s"
      by simp
  qed
qed

lemma mono_bounded:
  assumes "monotonic (applies_eq A)"
  shows "monotonic (applies_eq (Bounded A))"
proof (rule monotonicI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (Bounded A) \<Delta>) (applies_eq (Bounded A) \<Delta>')"
  proof (rule smaller_interpI)
    fix s x assume "x \<in> applies_eq (Bounded A) \<Delta> s"
    then show "x \<in> applies_eq (Bounded A) \<Delta>' s"
      using asm assms monotonic_def smaller_interp_applies_cons by fastforce
  qed
qed

lemma mono_exists:
  assumes "monotonic (applies_eq A)"
    shows "monotonic (applies_eq (Exists v A))"
proof (rule monotonicI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (Exists v A) \<Delta>) (applies_eq (Exists v A) \<Delta>')"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Exists v A) \<Delta> s"
    then show "x \<in> applies_eq (Exists v A) \<Delta>' s"
      using asm0 assms monotonic_def smaller_interp_applies_cons by fastforce
  qed
qed


lemma mono_forall:
  assumes "monotonic (applies_eq A)"
    shows "monotonic (applies_eq (Forall v A))"
proof (rule monotonicI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (Forall v A) \<Delta>) (applies_eq (Forall v A) \<Delta>')"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Forall v A) \<Delta> s"
    then show "x \<in> applies_eq (Forall v A) \<Delta>' s"
      using asm0 assms monotonic_def smaller_interp_applies_cons by fastforce
  qed
qed














subsubsection \<open>Non-increasing\<close>

lemma non_increasing_instantiate:
  assumes "non_increasing (applies_eq A)"
      and "x \<in> applies_eq A \<Delta>' s"
      and "smaller_interp \<Delta> \<Delta>'"
    shows "x \<in> applies_eq A \<Delta> s"
  using assms(1) assms(2) assms(3) non_increasing_def smaller_interp_applies_cons by fastforce

lemma non_inc_star:
  assumes "non_increasing (applies_eq A)"
      and "non_increasing (applies_eq B)"
    shows "non_increasing (applies_eq (Star A B))"
proof (rule non_increasingI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (Star A B) \<Delta>') (applies_eq (Star A B) \<Delta>)"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Star A B) \<Delta>' s"
    then obtain a b where "Some x = a \<oplus> b" "a \<in> applies_eq A \<Delta>' s" "b \<in> applies_eq B \<Delta>' s"
      by auto
    then have "a \<in> applies_eq A \<Delta> s \<and> b \<in> applies_eq B \<Delta> s"
      by (meson asm0 assms(1) assms(2) non_increasing_instantiate)
    then show "x \<in> applies_eq (Star A B) \<Delta> s"
      using \<open>Some x = a \<oplus> b\<close> by force
  qed
qed


lemma non_increasing_wand:
  assumes "monotonic (applies_eq A)"
      and "non_increasing (applies_eq B)"
    shows "non_increasing (applies_eq (Wand A B))"
proof (rule non_increasingI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (Wand A B) \<Delta>') (applies_eq (Wand A B) \<Delta>)"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Wand A B) \<Delta>' s"
    have "x, s, \<Delta> \<Turnstile> Wand A B"
    proof (rule sat_wand)
      fix a b
      assume asm2: "a, s, \<Delta> \<Turnstile> A \<and> Some b = x \<oplus> a"
      then have "a, s, \<Delta>' \<Turnstile> A"
        by (meson asm0 assms(1) monotonic_def smaller_interp_applies_cons)
      then have "b, s, \<Delta>' \<Turnstile> B"
        using asm1 asm2 by auto
      then show "b, s, \<Delta> \<Turnstile> B"
        by (meson asm0 assms(2) non_increasing_def smaller_interp_applies_cons)
    qed
    then show "x \<in> applies_eq (Wand A B) \<Delta> s"
      by simp
  qed
qed



lemma non_increasing_and:
  assumes "non_increasing (applies_eq A)"
      and "non_increasing (applies_eq B)"
    shows "non_increasing (applies_eq (And A B))"
proof (rule non_increasingI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta>' \<Delta>"
  show "smaller_interp (applies_eq (And A B) \<Delta>) (applies_eq (And A B) \<Delta>')"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (And A B) \<Delta> s"
    then show "x \<in> applies_eq (And A B) \<Delta>' s"
      using asm0 assms(1) assms(2) non_increasing_def logic_axioms mem_Collect_eq sat.simps(8) smaller_interp_applies_cons by fastforce
  qed
qed

lemma non_increasing_or:
  assumes "non_increasing (applies_eq A)"
      and "non_increasing (applies_eq B)"
    shows "non_increasing (applies_eq (Or A B))"
proof (rule non_increasingI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (Or A B) \<Delta>') (applies_eq (Or A B) \<Delta>)"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Or A B) \<Delta>' s"
    then show "x \<in> applies_eq (Or A B) \<Delta> s"
      using asm0 assms(1) assms(2) non_increasing_def logic_axioms mem_Collect_eq sat.simps(8) smaller_interp_applies_cons by fastforce
  qed
qed

lemma non_increasing_sem:
  "non_increasing (applies_eq (Sem B))"
  using non_increasing_def smaller_interp_def by fastforce


lemma non_increasing_mult:
  assumes "non_increasing (applies_eq A)"
  shows "non_increasing (applies_eq (Mult \<pi> A))"
proof (rule non_increasingI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (Mult \<pi> A) \<Delta>') (applies_eq (Mult \<pi> A) \<Delta>)"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Mult \<pi> A) \<Delta>' s"
    then show "x \<in> applies_eq (Mult \<pi> A) \<Delta> s"
      using asm0 assms non_increasing_def smaller_interp_applies_cons by fastforce
  qed
qed

lemma non_increasing_wild:
  assumes "non_increasing (applies_eq A)"
  shows "non_increasing (applies_eq (Wildcard A))"
proof (rule non_increasingI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (Wildcard A) \<Delta>') (applies_eq (Wildcard A) \<Delta>)"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Wildcard A) \<Delta>' s"
    then show "x \<in> applies_eq (Wildcard A) \<Delta> s"
      using asm0 assms non_increasing_def smaller_interp_applies_cons by fastforce
  qed
qed


lemma non_increasing_imp:
  assumes "monotonic (applies_eq A)"
      and "non_increasing (applies_eq B)"
    shows "non_increasing (applies_eq (Imp A B))"
proof (rule non_increasingI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta> \<Delta>'"
  show "smaller_interp (applies_eq (Imp A B) \<Delta>') (applies_eq (Imp A B) \<Delta>)"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Imp A B) \<Delta>' s"
    have "x, s, \<Delta> \<Turnstile> Imp A B"
    proof (cases "x, s, \<Delta> \<Turnstile> A")
      case True
      then have "x, s, \<Delta>' \<Turnstile> A"
        by (meson asm0 assms(1) monotonic_def smaller_interp_applies_cons)
      then have "x, s, \<Delta>' \<Turnstile> B"
        using asm1 by auto
      then show ?thesis
        by (metis asm0 assms(2) non_increasing_def sat.simps(5) smaller_interp_applies_cons)
    next
      case False
      then show ?thesis by simp
    qed
    then show "x \<in> applies_eq (Imp A B) \<Delta> s"
      by simp
  qed
qed


lemma non_increasing_bounded:
  assumes "non_increasing (applies_eq A)"
  shows "non_increasing (applies_eq (Bounded A))"
proof (rule non_increasingI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm: "smaller_interp \<Delta>' \<Delta>"
  show "smaller_interp (applies_eq (Bounded A) \<Delta>) (applies_eq (Bounded A) \<Delta>')"
  proof (rule smaller_interpI)
    fix s x assume "x \<in> applies_eq (Bounded A) \<Delta> s"
    then show "x \<in> applies_eq (Bounded A) \<Delta>' s"
      using asm assms non_increasing_def smaller_interp_applies_cons by fastforce
  qed
qed


lemma non_increasing_exists:
  assumes "non_increasing (applies_eq A)"
    shows "non_increasing (applies_eq (Exists v A))"
proof (rule non_increasingI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta>' \<Delta>"
  show "smaller_interp (applies_eq (Exists v A) \<Delta>) (applies_eq (Exists v A) \<Delta>')"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Exists v A) \<Delta> s"
    then show "x \<in> applies_eq (Exists v A) \<Delta>' s"
      using asm0 assms non_increasing_def smaller_interp_applies_cons by fastforce
  qed
qed


lemma non_increasing_forall:
  assumes "non_increasing (applies_eq A)"
    shows "non_increasing (applies_eq (Forall v A))"
proof (rule non_increasingI)
  fix \<Delta> \<Delta>' :: "('c, 'd, 'a) interp"
  assume asm0: "smaller_interp \<Delta>' \<Delta>"
  show "smaller_interp (applies_eq (Forall v A) \<Delta>) (applies_eq (Forall v A) \<Delta>')"
  proof (rule smaller_interpI)
    fix s x assume asm1: "x \<in> applies_eq (Forall v A) \<Delta> s"
    then show "x \<in> applies_eq (Forall v A) \<Delta>' s"
      using asm0 assms non_increasing_def smaller_interp_applies_cons by fastforce
  qed
qed













subsection \<open>Tarski's fixed points\<close>

subsubsection \<open>Greatest Fixed Point\<close>

definition D :: "(('d, 'c, 'a) interp \<Rightarrow> ('d, 'c, 'a) interp) \<Rightarrow> ('d, 'c, 'a) interp set" where
  "D f = { \<Delta> |\<Delta>. smaller_interp \<Delta> (f \<Delta>) }"

fun GFP :: "(('d, 'c, 'a) interp \<Rightarrow> ('d, 'c, 'a) interp) \<Rightarrow> ('d, 'c, 'a) interp" where
  "GFP f s = { \<sigma> |\<sigma>. \<exists>\<Delta> \<in> D f. \<sigma> \<in> \<Delta> s }"

lemma smaller_interp_D:
  assumes "x \<in> D f"
  shows "smaller_interp x (GFP f)"
  by (metis (mono_tags, lifting) CollectI GFP.elims assms smaller_interpI)

lemma GFP_lub:
  assumes "\<And>x. x \<in> D f \<Longrightarrow> smaller_interp x y"
  shows "smaller_interp (GFP f) y"
proof (rule smaller_interpI)
  fix s x
  assume "x \<in> GFP f s"
  then obtain \<Delta> where "\<Delta> \<in> D f" "x \<in> \<Delta> s"
    by auto
  then show "x \<in> y s"
    by (metis assms in_mono smaller_interp_def)
qed

lemma smaller_interp_antisym:
  assumes "smaller_interp a b"
      and "smaller_interp b a"
    shows "a = b"
proof (rule ext)
  fix x show "a x = b x"
    by (metis assms(1) assms(2) set_eq_subset smaller_interp_def)
qed












subsubsection \<open>Least Fixed Point\<close>

definition DD :: "(('d, 'c, 'a) interp \<Rightarrow> ('d, 'c, 'a) interp) \<Rightarrow> ('d, 'c, 'a) interp set" where
  "DD f = { \<Delta> |\<Delta>. smaller_interp (f \<Delta>) \<Delta> }"

fun LFP :: "(('d, 'c, 'a) interp \<Rightarrow> ('d, 'c, 'a) interp) \<Rightarrow> ('d, 'c, 'a) interp" where
  "LFP f s = { \<sigma> |\<sigma>. \<forall>\<Delta> \<in> DD f. \<sigma> \<in> \<Delta> s }"

lemma smaller_interp_DD:
  assumes "x \<in> DD f"
  shows "smaller_interp (LFP f) x"
  using assms smaller_interp_def by fastforce


lemma LFP_glb:
  assumes "\<And>x. x \<in> DD f \<Longrightarrow> smaller_interp y x"
  shows "smaller_interp y (LFP f)"
proof (rule smaller_interpI)
  fix s x
  assume "x \<in> y s"
  then have "\<And>\<Delta>. \<Delta> \<in> DD f \<Longrightarrow> x \<in> \<Delta> s"
    by (metis assms smaller_interp_def subsetD)
  then show "x \<in> LFP f s"
    by simp
qed







subsection \<open>Combinability and (an assertion being) intuitionistic are set-closure properties\<close>


subsubsection \<open>Intuitionistic assertions\<close>

definition sem_intui :: "('d, 'c, 'a) interp \<Rightarrow> bool" where
  "sem_intui \<Delta> \<longleftrightarrow> (\<forall>s \<sigma> \<sigma>'. \<sigma>' \<succeq> \<sigma> \<and> \<sigma> \<in> \<Delta> s \<longrightarrow> \<sigma>' \<in> \<Delta> s)"

lemma sem_intuiI:
  assumes "\<And>s \<sigma> \<sigma>'. \<sigma>' \<succeq> \<sigma> \<and> \<sigma> \<in> \<Delta> s \<Longrightarrow> \<sigma>' \<in> \<Delta> s"
  shows "sem_intui \<Delta>"
  using assms sem_intui_def by blast

lemma instantiate_intui_applies:
  assumes "intuitionistic s \<Delta> A"
      and "\<sigma>' \<succeq> \<sigma>"
      and "\<sigma> \<in> applies_eq A \<Delta> s"
    shows "\<sigma>' \<in> applies_eq A \<Delta> s"
  using assms(1) assms(2) assms(3) intuitionistic_def by fastforce

lemma sem_intui_intuitionistic:
  "sem_intui (applies_eq A \<Delta>) \<longleftrightarrow> (\<forall>s. intuitionistic s \<Delta> A)" (is "?A \<longleftrightarrow> ?B")
proof
  show "?B \<Longrightarrow> ?A"
  proof -
    assume ?B
    show ?A
    proof (rule sem_intuiI)
      fix s \<sigma> \<sigma>'
      assume "\<sigma>' \<succeq> \<sigma> \<and> \<sigma> \<in> applies_eq A \<Delta> s"
      then show "\<sigma>' \<in> applies_eq A \<Delta> s"
        using \<open>\<forall>s. intuitionistic s \<Delta> A\<close> instantiate_intui_applies by blast
    qed
  qed
  assume ?A
  show ?B
  proof
    fix s show "intuitionistic s \<Delta> A"
    proof (rule intuitionisticI)
      fix a b
      assume "a \<succeq> b \<and> b, s, \<Delta> \<Turnstile> A"
      then have "b \<in> applies_eq A \<Delta> s" by simp
      then show "a, s, \<Delta> \<Turnstile> A"
        by (metis CollectD \<open>a \<succeq> b \<and> b, s, \<Delta> \<Turnstile> A\<close> \<open>sem_intui (applies_eq A \<Delta>)\<close> applies_eq.simps sem_intui_def)
    qed
  qed
qed



lemma intuitionistic_set_closure:
  "sem_intui = set_closure_property (\<lambda>a b. { \<sigma> |\<sigma>. \<sigma> \<succeq> a})"
proof (rule ext)
  fix \<Delta> :: "('c, 'd, 'a) interp"
  show "sem_intui \<Delta> = set_closure_property (\<lambda>a b. {\<sigma> |\<sigma>. \<sigma> \<succeq> a}) \<Delta>" (is "?A \<longleftrightarrow> ?B")
  proof
    show "?A \<Longrightarrow> ?B"
      by (metis (no_types, lifting) CollectD set_closure_propertyI sem_intui_def subsetI)
    assume ?B
    show ?A
    proof (rule sem_intuiI)
      fix s \<sigma> \<sigma>'
      assume "\<sigma>' \<succeq> \<sigma> \<and> \<sigma> \<in> \<Delta> s"
      moreover have "(\<lambda>a b. {\<sigma> |\<sigma>. \<sigma> \<succeq> a}) \<sigma> \<sigma> = {\<sigma>' |\<sigma>'. \<sigma>' \<succeq> \<sigma>}" by simp
      ultimately have "{\<sigma>' |\<sigma>'. \<sigma>' \<succeq> \<sigma>} \<subseteq> \<Delta> s"
        by (metis \<open>set_closure_property (\<lambda>a b. {\<sigma> |\<sigma>. \<sigma> \<succeq> a}) \<Delta>\<close> set_closure_property_def)
      show "\<sigma>' \<in> \<Delta> s"
        using \<open>\<sigma>' \<succeq> \<sigma> \<and> \<sigma> \<in> \<Delta> s\<close> \<open>{\<sigma>' |\<sigma>'. \<sigma>' \<succeq> \<sigma>} \<subseteq> \<Delta> s\<close> by fastforce
    qed
  qed
qed



subsubsection \<open>Combinable assertions\<close>

definition sem_combinable :: "('d, 'c, 'a) interp \<Rightarrow> bool" where
  "sem_combinable \<Delta> \<longleftrightarrow> (\<forall>s p q a b x. sadd p q = one \<and> a \<in> \<Delta> s \<and> b \<in> \<Delta> s \<and> Some x = p \<odot> a \<oplus> q \<odot> b \<longrightarrow> x \<in> \<Delta> s)"

lemma sem_combinableI:
  assumes "\<And>s p q a b x. sadd p q = one \<and> a \<in> \<Delta> s \<and> b \<in> \<Delta> s \<and> Some x = p \<odot> a \<oplus> q \<odot> b \<Longrightarrow> x \<in> \<Delta> s"
  shows "sem_combinable \<Delta>"
  using assms sem_combinable_def by blast

lemma sem_combinableE:
  assumes "sem_combinable \<Delta>"
      and "a \<in> \<Delta> s"
      and "b \<in> \<Delta> s"
      and "Some x = p \<odot> a \<oplus> q \<odot> b"
      and "sadd p q = one"
    shows "x \<in> \<Delta> s"
  using assms(1) assms(2) assms(3) assms(4) assms(5) sem_combinable_def[of \<Delta>]
  by blast

lemma applies_eq_equiv:
  "x \<in> applies_eq A \<Delta> s \<longleftrightarrow> x, s, \<Delta> \<Turnstile> A"
  by simp

lemma sem_combinable_appliesE:
  assumes "sem_combinable (applies_eq A \<Delta>)"
      and "a, s, \<Delta> \<Turnstile> A"
      and "b, s, \<Delta> \<Turnstile> A"
      and "Some x = p \<odot> a \<oplus> q \<odot> b"
      and "sadd p q = one"
    shows "x, s, \<Delta> \<Turnstile> A"
    using sem_combinableE[of "applies_eq A \<Delta>" a s b x p q] assms by simp

lemma sem_combinable_equiv:
  "sem_combinable (applies_eq A \<Delta>) \<longleftrightarrow> (combinable \<Delta> A)" (is "?A \<longleftrightarrow> ?B")
proof                                       
  show "?B \<Longrightarrow> ?A"
  proof -
    assume ?B
    show ?A
    proof (rule sem_combinableI)
      fix s p q a b x
      assume asm: "sadd p q = one \<and> a \<in> applies_eq A \<Delta> s \<and> b \<in> applies_eq A \<Delta> s \<and> Some x = p \<odot> a \<oplus> q \<odot> b"
      then show "x \<in> applies_eq A \<Delta> s"
        using \<open>combinable \<Delta> A\<close> applies_eq_equiv combinable_instantiate_one by blast
    qed
  qed
  assume ?A
  show ?B
  proof -
    fix s show "combinable \<Delta> A"
    proof (rule combinableI)
      fix a b p q x \<sigma> s
      assume "a, s, \<Delta> \<Turnstile> A \<and> b, s, \<Delta> \<Turnstile> A \<and> Some x = p \<odot> a \<oplus> q \<odot> b \<and> sadd p q = one"
      then show "x, s, \<Delta> \<Turnstile> A"
        using \<open>sem_combinable (applies_eq A \<Delta>)\<close> sem_combinable_appliesE by blast
    qed
  qed
qed


lemma combinable_set_closure:
  "sem_combinable = set_closure_property (\<lambda>a b. { \<sigma> |\<sigma> p q. sadd p q = one \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b})"
proof (rule ext)
  fix \<Delta> :: "('c, 'd, 'a) interp"
  show "sem_combinable \<Delta> = set_closure_property (\<lambda>a b. { \<sigma> |\<sigma> p q. sadd p q = one \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b}) \<Delta>" (is "?A \<longleftrightarrow> ?B")
  proof
    show "?A \<Longrightarrow> ?B"
    proof -
      assume ?A
      show ?B
      proof (rule set_closure_propertyI)
        fix a b s
        assume "a \<in> \<Delta> s \<and> b \<in> \<Delta> s"
        then show "{x. \<exists>\<sigma> p q. x = \<sigma> \<and> sadd p q = one \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b} \<subseteq> \<Delta> s"
          using \<open>sem_combinable \<Delta>\<close> sem_combinableE by blast
      qed
    qed
    assume ?B
    show ?A
    proof (rule sem_combinableI)
      fix s p q a b x
      assume asm: "sadd p q = one \<and> a \<in> \<Delta> s \<and> b \<in> \<Delta> s \<and> Some x = p \<odot> a \<oplus> q \<odot> b"

      then have "x \<in> (\<lambda>a b. { \<sigma> |\<sigma> p q. sadd p q = one \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b}) a b"
        by blast
      moreover have "(\<lambda>a b. { \<sigma> |\<sigma> p q. sadd p q = one \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b}) a b \<subseteq> \<Delta> s"
        using \<open>?B\<close> set_closure_property_def[of "(\<lambda>a b. { \<sigma> |\<sigma> p q. sadd p q = one \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b})" \<Delta>]
        asm by meson
      ultimately show "x \<in> \<Delta> s" by blast
    qed
  qed
qed







subsection \<open>Transfinite induction\<close>


definition Inf :: "('d, 'c, 'a) interp set \<Rightarrow> ('d, 'c, 'a) interp" where
  "Inf S s = { \<sigma> |\<sigma>. \<forall>\<Delta> \<in> S. \<sigma> \<in> \<Delta> s}"


definition Sup :: "('d, 'c, 'a) interp set \<Rightarrow> ('d, 'c, 'a) interp" where
  "Sup S s = { \<sigma> |\<sigma>. \<exists>\<Delta> \<in> S. \<sigma> \<in> \<Delta> s}"

definition inf :: "('d, 'c, 'a) interp \<Rightarrow> ('d, 'c, 'a) interp \<Rightarrow> ('d, 'c, 'a) interp" where
  "inf \<Delta> \<Delta>' s = \<Delta> s \<inter> \<Delta>' s"

definition less where
  "less a b \<longleftrightarrow> smaller_interp a b \<and> a \<noteq> b"

definition sup :: "('d, 'c, 'a) interp \<Rightarrow> ('d, 'c, 'a) interp \<Rightarrow> ('d, 'c, 'a) interp" where
  "sup \<Delta> \<Delta>' s = \<Delta> s \<union> \<Delta>' s"

lemma smaller_full:
  "smaller_interp x full_interp"
  by (simp add: full_interp_def smaller_interpI)


lemma inf_empty:
  "local.Inf {} = full_interp"
proof (rule ext)
  fix s :: "'c \<Rightarrow> 'd" show "local.Inf {} s = full_interp s"
    by (simp add: Inf_def full_interp_def)
qed

lemma sup_empty:
  "local.Sup {} = empty_interp"
proof (rule ext)
  fix s :: "'c \<Rightarrow> 'd" show "local.Sup {} s = empty_interp s"
    by (simp add: Sup_def empty_interp_def)
qed

lemma test_axiom_inf:
  assumes "\<And>x. x \<in> A \<Longrightarrow> smaller_interp z x"
  shows "smaller_interp z (local.Inf A)"
proof (rule smaller_interpI)
  fix s x
  assume "x \<in> z s"
  then have "\<And>y. y \<in> A \<Longrightarrow> x \<in> y s"
    by (metis assms in_mono smaller_interp_def)
  then show "x \<in> local.Inf A s"
    by (simp add: Inf_def)
qed


lemma test_axiom_sup:
  assumes "\<And>x. x \<in> A \<Longrightarrow> smaller_interp x z"
  shows "smaller_interp (local.Sup A) z"
proof (rule smaller_interpI)
  fix s x
  assume "x \<in> local.Sup A s"
  then obtain y where "y \<in> A" "x \<in> y s"
    using Sup_def[of A s] mem_Collect_eq[of x]
    by auto
  then show "x \<in> z s"
    by (metis assms smaller_interp_def subsetD)
qed

interpretation complete_lattice Inf Sup inf smaller_interp less sup empty_interp full_interp
  apply standard
  apply (metis less_def smaller_interp_antisym)
  apply (simp add: smaller_interp_refl)
  using smaller_interp_trans apply blast
  using smaller_interp_antisym apply blast
  apply (simp add: inf_def smaller_interp_def)
  apply (simp add: inf_def smaller_interp_def)
  apply (simp add: inf_def smaller_interp_def)
  apply (simp add: smaller_interpI sup_def)
  apply (simp add: smaller_interpI sup_def)
  apply (simp add: smaller_interp_def sup_def)
  apply (metis (mono_tags, lifting) CollectD Inf_def smaller_interpI)
  using test_axiom_inf apply blast
  apply (metis (mono_tags, lifting) CollectI Sup_def smaller_interpI)
  using test_axiom_sup apply auto[1]
  apply (simp add: inf_empty)
  by (simp add: sup_empty)

lemma mono_same:
  "monotonic f \<longleftrightarrow> order_class.mono f"
  by (metis (no_types, opaque_lifting) le_funE le_funI monotonic_def order_class.mono_def smaller_interp_def)

lemma "smaller_interp a b \<longleftrightarrow> a \<le> b"
  by (simp add: le_fun_def smaller_interp_def)



lemma set_closure_property_admissible:
  "ccpo.admissible Sup_class.Sup (\<le>) (set_closure_property S)"
proof (rule ccpo.admissibleI)
  fix A :: "('c, 'd, 'a) interp set"
  assume asm0: "Complete_Partial_Order.chain (\<le>) A"
  "A \<noteq> {}" "\<forall>x\<in>A. set_closure_property S x"

  show "set_closure_property S (Sup_class.Sup A)"
  proof (rule set_closure_propertyI)
    fix a b s
    assume asm: "a \<in> Sup_class.Sup A s \<and> b \<in> Sup_class.Sup A s"
    then obtain \<Delta>a \<Delta>b where "\<Delta>a \<in> A" "\<Delta>b \<in> A" "a \<in> \<Delta>a s" "b \<in> \<Delta>b s"
      by auto
    then show "S a b \<subseteq> Sup_class.Sup A s"
    proof (cases "\<Delta>a s \<subseteq> \<Delta>b s")
      case True
      then have "S a b \<subseteq> \<Delta>b s"
        by (metis \<open>\<Delta>b \<in> A\<close> \<open>a \<in> \<Delta>a s\<close> \<open>b \<in> \<Delta>b s\<close> asm0(3) set_closure_property_def subsetD)
      then show ?thesis
        using \<open>\<Delta>b \<in> A\<close> by auto
    next
      case False
      then have "\<Delta>b s \<subseteq> \<Delta>a s"
        by (metis \<open>\<Delta>a \<in> A\<close> \<open>\<Delta>b \<in> A\<close> asm0(1) chainD le_funD)
      then have "S a b \<subseteq> \<Delta>a s"
        by (metis \<open>\<Delta>a \<in> A\<close> \<open>a \<in> \<Delta>a s\<close> \<open>b \<in> \<Delta>b s\<close> asm0(3) subsetD set_closure_property_def)
      then show ?thesis using \<open>\<Delta>a \<in> A\<close> by auto
    qed
  qed
qed


definition supp :: "('d, 'c, 'a) interp \<Rightarrow> bool" where
  "supp \<Delta> \<longleftrightarrow> (\<forall>a b s. a \<in> \<Delta> s \<and> b \<in> \<Delta> s \<longrightarrow> (\<exists>x. a \<succeq> x \<and> b \<succeq> x \<and> x \<in> \<Delta> s))"

lemma suppI:
  assumes "\<And>a b s. a \<in> \<Delta> s \<and> b \<in> \<Delta> s \<Longrightarrow> (\<exists>x. a \<succeq> x \<and> b \<succeq> x \<and> x \<in> \<Delta> s)"
  shows "supp \<Delta>"
  by (simp add: assms supp_def)

lemma supp_admissible:
  "ccpo.admissible Sup_class.Sup (\<le>) supp"
proof (rule ccpo.admissibleI)
  fix A :: "('c, 'd, 'a) interp set"
  assume asm0: "Complete_Partial_Order.chain (\<le>) A"
  "A \<noteq> {}" "\<forall>x\<in>A. supp x"
  show "supp (Sup_class.Sup A)"
  proof (rule suppI)
    fix a b s
    assume asm: "a \<in> Sup_class.Sup A s \<and> b \<in> Sup_class.Sup A s"
    then obtain \<Delta>a \<Delta>b where "\<Delta>a \<in> A" "\<Delta>b \<in> A" "a \<in> \<Delta>a s" "b \<in> \<Delta>b s"
      by auto
    then show "\<exists>x. a \<succeq> x \<and> b \<succeq> x \<and> x \<in> Sup_class.Sup A s"
    proof (cases "\<Delta>a s \<subseteq> \<Delta>b s")
      case True
      then have "a \<in> \<Delta>b s"
        using \<open>a \<in> \<Delta>a s\<close> by blast
      then obtain x where "a \<succeq> x" "b \<succeq> x" "x \<in> \<Delta>b s"
        by (metis \<open>\<Delta>b \<in> A\<close> \<open>b \<in> \<Delta>b s\<close> asm0(3) supp_def)
      then show ?thesis
        using \<open>\<Delta>b \<in> A\<close> by auto
    next
      case False
      then have "b \<in> \<Delta>a s"
        by (metis \<open>\<Delta>a \<in> A\<close> \<open>\<Delta>b \<in> A\<close> \<open>b \<in> \<Delta>b s\<close> asm0(1) chainD le_funD subsetD)
      then obtain x where "a \<succeq> x" "b \<succeq> x" "x \<in> \<Delta>a s"
        using \<open>\<Delta>a \<in> A\<close> \<open>a \<in> \<Delta>a s\<close> asm0(3) supp_def by metis
      then show ?thesis using \<open>\<Delta>a \<in> A\<close> by auto
    qed
  qed
qed

lemma "Sup_class.Sup {} = empty_interp" using empty_interp_def
  by fastforce

lemma set_closure_prop_empty_all:
  shows "set_closure_property S empty_interp"
  and "set_closure_property S full_interp"
   apply (metis empty_interp_def equals0D set_closure_propertyI)
  by (simp add: full_interp_def set_closure_propertyI)

lemma LFP_preserves_set_closure_property_aux:
  assumes "monotonic f"
      and "set_closure_property S empty_interp"
      and "\<And>\<Delta>. set_closure_property S \<Delta> \<Longrightarrow> set_closure_property S (f \<Delta>)"
    shows "set_closure_property S (ccpo_class.fixp f)"
  using set_closure_property_admissible
proof (rule fixp_induct[of "set_closure_property S"])
  show "set_closure_property S (Sup_class.Sup {})"
    by (simp add: set_closure_property_def)
  show "monotone (\<le>) (\<le>) f"
    by (metis (full_types) assms(1) le_fun_def monotoneI monotonic_def smaller_interp_def)
  show "\<And>x. set_closure_property S x \<Longrightarrow> set_closure_property S (f x)"
    by (simp add: assms(3))
qed

lemma GFP_preserves_set_closure_property_aux:
  assumes "order_class.mono f"
      and "set_closure_property S full_interp"
      and "\<And>\<Delta>. set_closure_property S \<Delta> \<Longrightarrow> set_closure_property S (f \<Delta>)"
    shows "set_closure_property S (complete_lattice_class.gfp f)"
  using assms(1)
proof (rule gfp_ordinal_induct[of f "set_closure_property S"])
  show "\<And>Sa. set_closure_property S Sa \<Longrightarrow> complete_lattice_class.gfp f \<le> Sa \<Longrightarrow> set_closure_property S (f Sa)"
    using assms(3) by blast
  fix M :: "('c, 'd, 'a) interp set"
  assume "\<forall>Sa\<in>M. set_closure_property S Sa"
  show "set_closure_property S (Inf_class.Inf M)"
  proof (rule set_closure_propertyI)
    fix a b s
    assume "a \<in> Inf_class.Inf M s \<and> b \<in> Inf_class.Inf M s"
    then have "\<And>\<Delta>. \<Delta> \<in> M \<Longrightarrow> a \<in> \<Delta> s \<and> b \<in> \<Delta> s"
      by simp
    then have "\<And>\<Delta>. \<Delta> \<in> M \<Longrightarrow> S a b \<subseteq> \<Delta> s"
      by (metis \<open>\<forall>Sa\<in>M. set_closure_property S Sa\<close> set_closure_property_def)
    show "S a b \<subseteq> Inf_class.Inf M s"
      by (simp add: \<open>\<And>\<Delta>. \<Delta> \<in> M \<Longrightarrow> S a b \<subseteq> \<Delta> s\<close> complete_lattice_class.INF_greatest)
  qed
qed








subsection Theorems

subsubsection \<open>Greatest Fixed Point\<close>

theorem GFP_is_FP:
  assumes "monotonic f"
  shows "f (GFP f) = GFP f"
proof -
  let ?u = "GFP f"
  have "\<And>x. x \<in> D f \<Longrightarrow> smaller_interp x (f ?u)"
  proof -
    fix x
    assume "x \<in> D f"
    then have "smaller_interp (f x) (f ?u)"
      using assms monotonic_def smaller_interp_D by blast
    moreover have "smaller_interp x (f x)"
      using D_def \<open>x \<in> D f\<close> by fastforce
    ultimately show "smaller_interp x (f ?u)"
      using smaller_interp_trans by blast
  qed
  then have "?u \<in> D f"
    using D_def GFP_lub by blast
  then have "f ?u \<in> D f"
    by (metis CollectI D_def \<open>\<And>x. x \<in> D f \<Longrightarrow> smaller_interp x (f (GFP f))\<close> assms monotonic_def)
  then show ?thesis
    by (simp add: \<open>GFP f \<in> D f\<close> \<open>\<And>x. x \<in> D f \<Longrightarrow> smaller_interp x (f (GFP f))\<close> smaller_interp_D smaller_interp_antisym)
qed


theorem GFP_greatest:
  assumes "f u = u"
  shows "smaller_interp u (GFP f)"
  by (simp add: D_def assms smaller_interp_D smaller_interp_refl)


lemma same_GFP:
  assumes "monotonic f"
  shows "complete_lattice_class.gfp f = GFP f"
proof -
  have "f (GFP f) = GFP f"
    using GFP_is_FP assms by blast
  then have "smaller_interp (GFP f) (complete_lattice_class.gfp f)"
    by (metis complete_lattice_class.gfp_upperbound le_funD order_class.order.eq_iff smaller_interp_def)
  moreover have "f (complete_lattice_class.gfp f) = complete_lattice_class.gfp f"
    using assms gfp_fixpoint mono_same by blast
  then have "smaller_interp (complete_lattice_class.gfp f) (GFP f)"
    by (simp add: GFP_greatest)
  ultimately show ?thesis
    by simp
qed

subsubsection \<open>Least Fixed Point\<close>

theorem LFP_is_FP:
  assumes "monotonic f"
  shows "f (LFP f) = LFP f"
proof -
  let ?u = "LFP f"
  have "\<And>x. x \<in> DD f \<Longrightarrow> smaller_interp (f ?u) x"
  proof -
    fix x
    assume "x \<in> DD f"
    then have "smaller_interp (f ?u) (f x)"
      using assms monotonic_def smaller_interp_DD by blast
    moreover have "smaller_interp (f x) x"
      using DD_def \<open>x \<in> DD f\<close> by fastforce
    ultimately show "smaller_interp (f ?u) x"
      using smaller_interp_trans by blast
  qed
  then have "?u \<in> DD f"
    using DD_def LFP_glb by blast
  then have "f ?u \<in> DD f"
    by (metis (mono_tags, lifting) CollectI DD_def \<open>\<And>x. x \<in> DD f \<Longrightarrow> smaller_interp (f (LFP f)) x\<close> assms monotonic_def)
  then show ?thesis
    by (simp add: \<open>LFP f \<in> DD f\<close> \<open>\<And>x. x \<in> DD f \<Longrightarrow> smaller_interp (f (LFP f)) x\<close> smaller_interp_DD smaller_interp_antisym)
qed

theorem LFP_least:
  assumes "f u = u"
  shows "smaller_interp (LFP f) u"
  by (simp add: DD_def assms smaller_interp_DD smaller_interp_refl)



lemma same_LFP:
  assumes "monotonic f"
  shows "complete_lattice_class.lfp f = LFP f"
proof -
  have "f (LFP f) = LFP f"
    using LFP_is_FP assms by blast
  then have "smaller_interp (complete_lattice_class.lfp f) (LFP f)"
    by (metis complete_lattice_class.lfp_lowerbound le_funE preorder_class.order_refl smaller_interp_def)
  moreover have "f (complete_lattice_class.gfp f) = complete_lattice_class.gfp f"
    using assms gfp_fixpoint mono_same by blast
  then have "smaller_interp (LFP f) (complete_lattice_class.lfp f)"
    by (meson LFP_least assms lfp_fixpoint mono_same)
  ultimately show ?thesis
    by simp
qed


lemma LFP_same:
  assumes "monotonic f"
  shows "ccpo_class.fixp f = LFP f"
proof -
  have "f (ccpo_class.fixp f) = ccpo_class.fixp f"
    by (metis (mono_tags, lifting) assms fixp_unfold mono_same monotoneI order_class.mono_def)
  then have "smaller_interp (LFP f) (ccpo_class.fixp f)"
    by (simp add: LFP_least)
  moreover have "f (LFP f) = LFP f"
    using LFP_is_FP assms by blast
  then have "ccpo_class.fixp f \<le> LFP f"
    by (metis assms fixp_lowerbound mono_same monotoneI order_class.mono_def preorder_class.order_refl)
  ultimately show ?thesis
    by (metis assms lfp_eq_fixp mono_same same_LFP)
qed



text \<open>The following theorem corresponds to Theorem 5 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

theorem FP_preserves_set_closure_property:
  assumes "monotonic f"
      and "\<And>\<Delta>. set_closure_property S \<Delta> \<Longrightarrow> set_closure_property S (f \<Delta>)"
    shows "set_closure_property S (GFP f)"
      and "set_closure_property S (LFP f)"
  apply (metis GFP_preserves_set_closure_property_aux assms(1) assms(2) mono_same same_GFP set_closure_prop_empty_all(2))
  by (metis LFP_preserves_set_closure_property_aux LFP_same assms(1) assms(2) set_closure_prop_empty_all(1))

end

end