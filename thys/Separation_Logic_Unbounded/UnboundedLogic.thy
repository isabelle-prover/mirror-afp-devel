section \<open>Unbounded Separation Logic\<close>

theory UnboundedLogic
  imports Main
begin

subsection \<open>Assertions and state model\<close>

text \<open>We define our assertion language as described in Section 2.3 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

datatype ('a, 'b, 'c, 'd) assertion =
  Sem "('d \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> bool"
  | Mult 'b "('a, 'b, 'c, 'd) assertion"
  | Star "('a, 'b, 'c, 'd) assertion" "('a, 'b, 'c, 'd) assertion"
  | Wand "('a, 'b, 'c, 'd) assertion" "('a, 'b, 'c, 'd) assertion"
  | Or "('a, 'b, 'c, 'd) assertion" "('a, 'b, 'c, 'd) assertion"
  | And "('a, 'b, 'c, 'd) assertion" "('a, 'b, 'c, 'd) assertion"
  | Imp "('a, 'b, 'c, 'd) assertion" "('a, 'b, 'c, 'd) assertion"
  | Exists 'd "('a, 'b, 'c, 'd) assertion"
  | Forall 'd "('a, 'b, 'c, 'd) assertion"
  | Pred
  | Bounded "('a, 'b, 'c, 'd) assertion"
  | Wildcard "('a, 'b, 'c, 'd) assertion"

type_synonym 'a command = "('a \<times> 'a option) set"

locale pre_logic =
    fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option" (infixl "\<oplus>" 63)

begin

definition compatible :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "##" 60) where
  "a ## b \<longleftrightarrow> a \<oplus> b \<noteq> None"

definition larger :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<succeq>" 55) where
  "a \<succeq> b \<longleftrightarrow> (\<exists>c. Some a = b \<oplus> c)"

end

type_synonym ('a, 'b, 'c) interp = "('a \<Rightarrow> 'b) \<Rightarrow> 'c set"

text \<open>The following locale captures the state model described in Section 2.2 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

locale logic = pre_logic +

  fixes mult :: "'b \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<odot>" 64)

  fixes smult :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes sadd :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes sinv :: "'b \<Rightarrow> 'b"

  fixes one :: 'b

  fixes valid :: "'a \<Rightarrow> bool"


  assumes commutative: "a \<oplus> b = b \<oplus> a"
      and asso1: "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
      and asso2: "a \<oplus> b = Some ab \<and> \<not> b ## c \<Longrightarrow> \<not> ab ## c"

      and sinv_inverse: "smult p (sinv p) = one"
      and sone_neutral: "smult one p = p"
      and sadd_comm: "sadd p q = sadd q p"
      and smult_comm: "smult p q = smult q p"
      and smult_distrib: "smult p (sadd q r) = sadd (smult p q) (smult p r)"
      and smult_asso: "smult (smult p q) r = smult p (smult q r)"

      and double_mult: "p \<odot> (q \<odot> a) = (smult p q) \<odot> a"
      and plus_mult: "Some a = b \<oplus> c \<Longrightarrow> Some (p \<odot> a) = (p \<odot> b) \<oplus> (p \<odot> c)"
      and distrib_mult: "Some ((sadd p q) \<odot> x) = p \<odot> x \<oplus> q \<odot> x"
      and one_neutral: "one \<odot> a = a"

      and valid_mono: "valid a \<and> a \<succeq> b \<Longrightarrow> valid b"

begin

text \<open>The validity of assertions corresponds to Figure 3 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

fun sat :: "'a \<Rightarrow> ('d \<Rightarrow> 'c) \<Rightarrow> ('d, 'c, 'a) interp \<Rightarrow> ('a, 'b, 'c, 'd) assertion \<Rightarrow> bool" ("_, _, _ \<Turnstile> _" [51, 65, 68, 66] 50) where
  "\<sigma>, s, \<Delta> \<Turnstile> Mult p A \<longleftrightarrow> (\<exists>a. \<sigma> = p \<odot> a \<and> a, s, \<Delta> \<Turnstile> A)"
| "\<sigma>, s, \<Delta> \<Turnstile> Star A B \<longleftrightarrow> (\<exists>a b. Some \<sigma> = a \<oplus> b \<and> a, s, \<Delta> \<Turnstile> A \<and> b, s, \<Delta> \<Turnstile> B)"
| "\<sigma>, s, \<Delta> \<Turnstile> Wand A B \<longleftrightarrow> (\<forall>a \<sigma>'. a, s, \<Delta> \<Turnstile> A \<and> Some \<sigma>' = \<sigma> \<oplus> a \<longrightarrow> \<sigma>', s, \<Delta> \<Turnstile> B)"

| "\<sigma>, s, \<Delta> \<Turnstile> Sem b \<longleftrightarrow> b s \<sigma>"
| "\<sigma>, s, \<Delta> \<Turnstile> Imp A B \<longleftrightarrow> (\<sigma>, s, \<Delta> \<Turnstile> A \<longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> B)"
| "\<sigma>, s, \<Delta> \<Turnstile> Or A B \<longleftrightarrow> (\<sigma>, s, \<Delta> \<Turnstile> A \<or> \<sigma>, s, \<Delta> \<Turnstile> B)"
| "\<sigma>, s, \<Delta> \<Turnstile> And A B \<longleftrightarrow> (\<sigma>, s, \<Delta> \<Turnstile> A \<and> \<sigma>, s, \<Delta> \<Turnstile> B)"

| "\<sigma>, s, \<Delta> \<Turnstile> Exists x A \<longleftrightarrow> (\<exists>v. \<sigma>, s(x := v), \<Delta> \<Turnstile> A)"
| "\<sigma>, s, \<Delta> \<Turnstile> Forall x A \<longleftrightarrow> (\<forall>v. \<sigma>, s(x := v), \<Delta> \<Turnstile> A)"

| "\<sigma>, s, \<Delta> \<Turnstile> Pred \<longleftrightarrow> (\<sigma> \<in> \<Delta> s)"
| "\<sigma>, s, \<Delta> \<Turnstile> Bounded A \<longleftrightarrow> (valid \<sigma> \<longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> A)"
| "\<sigma>, s, \<Delta> \<Turnstile> Wildcard A \<longleftrightarrow> (\<exists>a p. \<sigma> = p \<odot> a \<and> a, s, \<Delta> \<Turnstile> A)"

definition intuitionistic :: "('d \<Rightarrow> 'c) \<Rightarrow> ('d, 'c, 'a) interp \<Rightarrow> ('a, 'b, 'c, 'd) assertion \<Rightarrow> bool" where
  "intuitionistic s \<Delta> A \<longleftrightarrow> (\<forall>a b. a \<succeq> b \<and> b, s, \<Delta> \<Turnstile> A \<longrightarrow> a, s, \<Delta> \<Turnstile> A)"

definition entails :: "('a, 'b, 'c, 'd) assertion \<Rightarrow> ('d, 'c, 'a) interp \<Rightarrow> ('a, 'b, 'c, 'd) assertion \<Rightarrow> bool" ("_, _ \<turnstile> _" [63, 66, 68] 52) where
  "A, \<Delta> \<turnstile> B \<longleftrightarrow> (\<forall>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> A \<longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> B)"

definition equivalent :: "('a, 'b, 'c, 'd) assertion \<Rightarrow> ('d, 'c, 'a) interp \<Rightarrow> ('a, 'b, 'c, 'd) assertion \<Rightarrow> bool" ("_, _ \<equiv> _" [63, 66, 68] 52) where
  "A, \<Delta> \<equiv> B \<longleftrightarrow> (A, \<Delta> \<turnstile> B \<and> B, \<Delta> \<turnstile> A)"

definition pure :: "('a, 'b, 'c, 'd) assertion \<Rightarrow> bool" where
  "pure A \<longleftrightarrow> (\<forall>\<sigma> \<sigma>' s \<Delta> \<Delta>'. \<sigma>, s, \<Delta> \<Turnstile> A \<longleftrightarrow> \<sigma>', s, \<Delta>' \<Turnstile> A)"


subsection \<open>Useful lemmas\<close>

lemma sat_forall:
  assumes "\<And>v. \<sigma>, s(x := v), \<Delta> \<Turnstile> A"
  shows "\<sigma>, s, \<Delta> \<Turnstile> Forall x A"
  by (simp add: assms)

lemma intuitionisticI:
  assumes "\<And>a b. a \<succeq> b \<and> b, s, \<Delta> \<Turnstile> A \<Longrightarrow> a, s, \<Delta> \<Turnstile> A"
  shows "intuitionistic s \<Delta> A"
  by (meson assms intuitionistic_def)

lemma can_divide:
  assumes "p \<odot> a = p \<odot> b"
  shows "a = b"
  by (metis assms double_mult logic.one_neutral logic_axioms sinv_inverse smult_comm)

lemma unique_inv:
  "a = p \<odot> b \<longleftrightarrow> b = (sinv p) \<odot> a"
  by (metis double_mult logic.can_divide logic_axioms sinv_inverse sone_neutral)

lemma entailsI:
  assumes "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> A \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> B"
  shows "A, \<Delta> \<turnstile> B"
  by (simp add: assms entails_def)

lemma equivalentI:
  assumes "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> A \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> B"
      and "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> B \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> A"
    shows "A, \<Delta> \<equiv> B"
  by (simp add: assms(1) assms(2) entailsI equivalent_def)

lemma compatible_imp:
  assumes "a ## b"
  shows "(p \<odot> a) ## (p \<odot> b)"
  by (metis assms compatible_def option.distinct(1) option.exhaust plus_mult)

lemma compatible_iff:
  "a ## b \<longleftrightarrow> (p \<odot> a) ## (p \<odot> b)"
  by (metis compatible_imp unique_inv)

lemma sat_wand:
  assumes "\<And>a \<sigma>'. a, s, \<Delta> \<Turnstile> A \<and> Some \<sigma>' = \<sigma> \<oplus> a \<Longrightarrow> \<sigma>', s, \<Delta> \<Turnstile> B"
  shows "\<sigma>, s, \<Delta> \<Turnstile> Wand A B"
  using assms by auto

lemma sat_imp:
  assumes "\<sigma>, s, \<Delta> \<Turnstile> A \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> B"
  shows "\<sigma>, s, \<Delta> \<Turnstile> Imp A B"
  using assms by auto

lemma sat_mult:
  assumes "\<And>a. \<sigma> = p \<odot> a \<Longrightarrow> a, s, \<Delta> \<Turnstile> A"
  shows "\<sigma>, s, \<Delta> \<Turnstile> Mult p A"
  by (metis assms logic.sat.simps(1) logic_axioms unique_inv)

lemma larger_same:
  "a \<succeq> b \<longleftrightarrow> p \<odot> a \<succeq> p \<odot> b"
proof -
  have "\<And>a b p. a \<succeq> b \<Longrightarrow> p \<odot> a \<succeq> p \<odot> b"
    by (meson larger_def plus_mult)
  then show ?thesis
    by (metis unique_inv)
qed

lemma asso3:
  assumes "\<not> a ## b"
      and "b \<oplus> c = Some bc"
    shows "\<not> a ## bc"
  by (metis (full_types) assms(1) assms(2) asso2 commutative compatible_def)

lemma compatible_smaller:
  assumes "a \<succeq> b"
      and "x ## a"
    shows "x ## b"
  by (metis assms(1) assms(2) asso3 larger_def)

lemma compatible_multiples:
  assumes "p \<odot> a ## q \<odot> b"
  shows "a ## b"
  by (metis (no_types, opaque_lifting) assms commutative compatible_def compatible_iff compatible_smaller distrib_mult larger_def one_neutral)

lemma move_sum:
  assumes "Some a = a1 \<oplus> a2"
      and "Some b = b1 \<oplus> b2"
      and "Some x = a \<oplus> b"
      and "Some x1 = a1 \<oplus> b1"
      and "Some x2 = a2 \<oplus> b2"
    shows "Some x = x1 \<oplus> x2"
proof -
  obtain ab1 where "Some ab1 = a \<oplus> b1"
    by (metis assms(2) assms(3) asso3 compatible_def not_Some_eq)
  then have "Some ab1 = x1 \<oplus> a2"
    by (metis assms(1) assms(4) asso1 commutative)
  then show ?thesis
    by (metis \<open>Some ab1 = a \<oplus> b1\<close> assms(2) assms(3) assms(5) asso1)
qed

lemma sum_both_larger:
  assumes "Some x' = a' \<oplus> b'"
      and "Some x = a \<oplus> b"
      and "a' \<succeq> a"
      and "b' \<succeq> b"
    shows "x' \<succeq> x"
proof -
  obtain ra rb where "Some a' = a \<oplus> ra" "Some b' = b \<oplus> rb"
    using assms(3) assms(4) larger_def by auto
  then obtain r where "Some r = ra \<oplus> rb"
    by (metis assms(1) asso3 commutative compatible_def option.collapse)
  then have "Some x' = x \<oplus> r"
    by (meson \<open>Some a' = a \<oplus> ra\<close> \<open>Some b' = b \<oplus> rb\<close> assms(1) assms(2) move_sum)
  then show ?thesis
    using larger_def by blast
qed

lemma larger_first_sum:
  assumes "Some y = a \<oplus> b"
      and "x \<succeq> y"
    shows "\<exists>a'. Some x = a' \<oplus> b \<and> a' \<succeq> a"
proof -
  obtain r where "Some x = y \<oplus> r"
    using assms(2) larger_def by auto
  then obtain a' where "Some a' = a \<oplus> r"
    by (metis assms(1) asso2 commutative compatible_def option.collapse)
  then show ?thesis
    by (metis \<open>Some x = y \<oplus> r\<close> assms(1) asso1 commutative larger_def)
qed

lemma larger_implies_compatible:
  assumes "x \<succeq> y"
  shows "x ## y"
  by (metis assms compatible_def compatible_smaller distrib_mult one_neutral option.distinct(1))







section \<open>Frame rule\<close>

text \<open>This section corresponds to Section 2.5 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

definition safe :: "('a \<times> ('d \<Rightarrow> 'c)) command \<Rightarrow> ('a \<times> ('d \<Rightarrow> 'c)) \<Rightarrow> bool" where
  "safe c \<sigma> \<longleftrightarrow> (\<sigma>, None) \<notin> c"

definition safety_monotonicity :: "('a \<times> ('d \<Rightarrow> 'c)) command \<Rightarrow> bool" where
  "safety_monotonicity c \<longleftrightarrow> (\<forall>\<sigma> \<sigma>' s. valid \<sigma>' \<and> \<sigma>' \<succeq> \<sigma> \<and> safe c (\<sigma>, s) \<longrightarrow> safe c (\<sigma>', s))"

definition frame_property :: "('a \<times> ('d \<Rightarrow> 'c)) command \<Rightarrow> bool" where
  "frame_property c \<longleftrightarrow> (\<forall>\<sigma> \<sigma>0 r \<sigma>' s s'. valid \<sigma> \<and> valid \<sigma>' \<and> safe c (\<sigma>0, s) \<and> Some \<sigma> = \<sigma>0 \<oplus> r \<and> ((\<sigma>, s), Some (\<sigma>', s')) \<in> c
  \<longrightarrow> (\<exists>\<sigma>0'. Some \<sigma>' = \<sigma>0' \<oplus> r \<and> ((\<sigma>0, s), Some (\<sigma>0', s')) \<in> c))"

definition valid_hoare_triple :: "('a, 'b, 'c, 'd) assertion \<Rightarrow> ('a \<times> ('d \<Rightarrow> 'c)) command \<Rightarrow> ('a, 'b, 'c, 'd) assertion \<Rightarrow> ('d, 'c, 'a) interp \<Rightarrow> bool" where
  "valid_hoare_triple P c Q \<Delta> \<longleftrightarrow> (\<forall>\<sigma> s. valid \<sigma> \<and> \<sigma>, s, \<Delta> \<Turnstile> P \<longrightarrow> safe c (\<sigma>, s) \<and> (\<forall>\<sigma>' s'. ((\<sigma>, s), Some (\<sigma>', s')) \<in> c \<longrightarrow> \<sigma>', s', \<Delta> \<Turnstile> Q))"

lemma valid_hoare_tripleI:
  assumes "\<And>\<sigma> s. valid \<sigma> \<and> \<sigma>, s, \<Delta> \<Turnstile> P \<Longrightarrow> safe c (\<sigma>, s)"
      and "\<And>\<sigma> s \<sigma>' s'. valid \<sigma> \<and> \<sigma>, s, \<Delta> \<Turnstile> P \<Longrightarrow> ((\<sigma>, s), Some (\<sigma>', s')) \<in> c \<Longrightarrow> \<sigma>', s', \<Delta> \<Turnstile> Q"
    shows "valid_hoare_triple P c Q \<Delta>"
  using assms(1) assms(2) valid_hoare_triple_def by blast

definition valid_command :: "('a \<times> ('d \<Rightarrow> 'c)) command \<Rightarrow> bool" where
  "valid_command c \<longleftrightarrow> (\<forall>a b sa sb. ((a, sa), Some (b, sb)) \<in> c \<and> valid a \<longrightarrow> valid b)"

definition modified :: "('a \<times> ('d \<Rightarrow> 'c)) command \<Rightarrow> 'd set" where
  "modified c = { x |x. \<exists>\<sigma> s \<sigma>' s'. ((\<sigma>, s), Some (\<sigma>', s')) \<in> c \<and> s x \<noteq> s' x }"

definition equal_outside :: "('d \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'c) \<Rightarrow> 'd set \<Rightarrow> bool" where
  "equal_outside s s' S \<longleftrightarrow> (\<forall>x. x \<notin> S \<longrightarrow> s x = s' x)"



definition not_in_fv :: "('a, 'b, 'c, 'd) assertion \<Rightarrow> 'd set \<Rightarrow> bool" where
  "not_in_fv A S \<longleftrightarrow> (\<forall>\<sigma> s \<Delta> s'. equal_outside s s' S \<longrightarrow> (\<sigma>, s, \<Delta> \<Turnstile> A \<longleftrightarrow> \<sigma>, s', \<Delta> \<Turnstile> A))"



lemma not_in_fv_mod:
  assumes "not_in_fv A (modified c)"
  and "((\<sigma>, s), Some (\<sigma>', s')) \<in> c"
  shows "x, s, \<Delta> \<Turnstile> A \<longleftrightarrow> x, s', \<Delta> \<Turnstile> A"
proof -
  have "\<And>x. x \<notin> (modified c) \<Longrightarrow> s x = s' x"
  proof -
    fix x assume "x \<notin> (modified c)"
    then show "s x = s' x"
      by (metis (mono_tags, lifting) CollectI assms(2) modified_def)
  qed
  then have "equal_outside s s' (modified c)"
    by (simp add: equal_outside_def)
  then show ?thesis
    using assms(1) not_in_fv_def by blast
qed


text \<open>This theorem corresponds to Theorem 2 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

theorem frame_rule:
  assumes "valid_command c"
      and "safety_monotonicity c"
      and "frame_property c"
      and "valid_hoare_triple P c Q \<Delta>"
      and "not_in_fv R (modified c)"
    shows "valid_hoare_triple (Star P R) c (Star Q R) \<Delta>"
proof (rule valid_hoare_tripleI)
  fix \<sigma> s assume asm0: "valid \<sigma> \<and> \<sigma>, s, \<Delta> \<Turnstile> Star P R"
  then obtain p r where "Some \<sigma> = p \<oplus> r" "p, s, \<Delta> \<Turnstile> P" "r, s, \<Delta> \<Turnstile> R"
    by auto
  then have "safe c (p, s)"
    by (metis asm0 assms(4) larger_def logic.valid_mono logic_axioms valid_hoare_triple_def)
  then show "safe c (\<sigma>, s)"
    using \<open>Some \<sigma> = p \<oplus> r\<close> assms(2) larger_def safety_monotonicity_def asm0 by blast
  fix \<sigma>' s' assume asm1: "((\<sigma>, s), Some (\<sigma>', s')) \<in> c"
  then obtain q where "Some \<sigma>' = q \<oplus> r" "((p, s), Some (q, s')) \<in> c"
    using \<open>Some \<sigma> = p \<oplus> r\<close> \<open>safe c (p, s)\<close> asm0 assms(1) assms(3) frame_property_def valid_command_def by blast
  moreover have "r, s', \<Delta> \<Turnstile> R"
    by (meson \<open>r, s, \<Delta> \<Turnstile> R\<close> assms(5) calculation(2) logic.not_in_fv_mod logic_axioms)
  ultimately show "\<sigma>', s', \<Delta> \<Turnstile> Star Q R"
    by (meson \<open>Some \<sigma> = p \<oplus> r\<close> \<open>p, s, \<Delta> \<Turnstile> P\<close> \<open>r, s, \<Delta> \<Turnstile> R\<close> asm0 assms(4) larger_def sat.simps(2) valid_hoare_triple_def valid_mono)
qed


lemma hoare_triple_input:
  "valid_hoare_triple P c Q \<Delta> \<longleftrightarrow> valid_hoare_triple (Bounded P) c Q \<Delta>"
  using sat.simps(11) valid_hoare_triple_def by blast


lemma hoare_triple_output:
  assumes "valid_command c"
  shows "valid_hoare_triple P c Q \<Delta> \<longleftrightarrow> valid_hoare_triple P c (Bounded Q) \<Delta>"
  using assms valid_command_def valid_hoare_triple_def by fastforce



end

end