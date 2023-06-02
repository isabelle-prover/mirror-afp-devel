section \<open>Hyper Hoare Logic\<close>

text \<open>In this file, we define concepts from the logic (section IV): hyper-assertions, hyper-triples,
and the syntactic rules. We also prove soundness (theorem 1), completeness (theorem 2), the ability
to disprove hyper-triples in the logic (theorem 4), and the synchronized if rule from appendix C.\<close>

theory Logic
  imports Language
begin

text \<open>Definition 4\<close>
type_synonym 'a hyperassertion = "('a set \<Rightarrow> bool)"

definition entails where
  "entails A B \<longleftrightarrow> (\<forall>S. A S \<longrightarrow> B S)"

lemma entailsI:
  assumes "\<And>S. A S \<Longrightarrow> B S"
  shows "entails A B"
  by (simp add: assms entails_def)

lemma entailsE:
  assumes "entails A B"
      and "A x"
    shows "B x"
  by (meson assms(1) assms(2) entails_def)

lemma bientails_equal:
  assumes "entails A B"
      and "entails B A"
    shows "A = B"
proof (rule ext)
  fix S show "A S = B S"
    by (meson assms(1) assms(2) entailsE)
qed

lemma entails_trans:
  assumes "entails A B"
      and "entails B C"
    shows "entails A C"
  by (metis assms(1) assms(2) entails_def)


definition setify_prop where
  "setify_prop b = { (l, \<sigma>) |l \<sigma>. b \<sigma>}"

lemma sem_assume_setify:
  "sem (Assume b) S = S \<inter> setify_prop b" (is "?A = ?B")
proof -
  have "\<And>l \<sigma>. (l, \<sigma>) \<in> ?A \<longleftrightarrow> (l, \<sigma>) \<in> ?B"
  proof -
    fix l \<sigma>
    have "(l, \<sigma>) \<in> ?A \<longleftrightarrow> (l, \<sigma>) \<in> S \<and> b \<sigma>"
      by (simp add: assume_sem)
    then show "(l, \<sigma>) \<in> ?A \<longleftrightarrow> (l, \<sigma>) \<in> ?B"
      by (simp add: setify_prop_def)
  qed
  then show ?thesis
    by auto
qed

definition over_approx :: "'a set \<Rightarrow> 'a hyperassertion" where
  "over_approx P S \<longleftrightarrow> S \<subseteq> P"

definition lower_closed :: "'a hyperassertion \<Rightarrow> bool" where
  "lower_closed P \<longleftrightarrow> (\<forall>S S'. P S \<and> S' \<subseteq> S \<longrightarrow> P S')"

lemma over_approx_lower_closed:
  "lower_closed (over_approx P)"
  by (metis (full_types) lower_closed_def order_trans over_approx_def)

definition under_approx :: "'a set \<Rightarrow> 'a hyperassertion" where
  "under_approx P S \<longleftrightarrow> P \<subseteq> S"

definition upper_closed :: "'a hyperassertion \<Rightarrow> bool" where
  "upper_closed P \<longleftrightarrow> (\<forall>S S'. P S \<and> S \<subseteq> S' \<longrightarrow> P S')"

lemma under_approx_upper_closed:
  "upper_closed (under_approx P)"
  by (metis (no_types, lifting) order.trans under_approx_def upper_closed_def)

definition closed_by_union :: "'a hyperassertion \<Rightarrow> bool" where
  "closed_by_union P \<longleftrightarrow> (\<forall>S S'. P S \<and> P S' \<longrightarrow> P (S \<union> S'))"

lemma closed_by_unionI:
  assumes "\<And>a b. P a \<Longrightarrow> P b \<Longrightarrow> P (a \<union> b)"
  shows "closed_by_union P"
  by (simp add: assms closed_by_union_def)

lemma closed_by_union_over:
  "closed_by_union (over_approx P)"
  by (simp add: closed_by_union_def over_approx_def)

lemma closed_by_union_under:
  "closed_by_union (under_approx P)"
  by (simp add: closed_by_union_def sup.coboundedI1 under_approx_def)

definition conj where
  "conj P Q S \<longleftrightarrow> P S \<and> Q S"

definition disj where
  "disj P Q S \<longleftrightarrow> P S \<or> Q S"

definition exists :: "('c \<Rightarrow> 'a hyperassertion) \<Rightarrow> 'a hyperassertion" where
  "exists P S \<longleftrightarrow> (\<exists>x. P x S)"

definition forall :: "('c \<Rightarrow> 'a hyperassertion) \<Rightarrow> 'a hyperassertion" where
  "forall P S \<longleftrightarrow> (\<forall>x. P x S)"

lemma over_inter:
  "entails (over_approx (P \<inter> Q)) (conj (over_approx P) (over_approx Q))"
  by (simp add: conj_def entails_def over_approx_def)

lemma over_union:
  "entails (disj (over_approx P) (over_approx Q)) (over_approx (P \<union> Q))"
  by (metis disj_def entailsI le_supI1 le_supI2 over_approx_def)

lemma under_union:
  "entails (under_approx (P \<union> Q)) (disj (under_approx P) (under_approx Q))"
  by (simp add: disj_def entails_def under_approx_def)

lemma under_inter:
  "entails (conj (under_approx P) (under_approx Q)) (under_approx (P \<inter> Q))"
  by (simp add: conj_def entails_def le_infI1 under_approx_def)


text \<open>Notation 1\<close>
definition join :: "'a hyperassertion \<Rightarrow> 'a hyperassertion \<Rightarrow> 'a hyperassertion" where
  "join A B S \<longleftrightarrow> (\<exists>SA SB. A SA \<and> B SB \<and> S = SA \<union> SB)"

definition general_join :: "('b \<Rightarrow> 'a hyperassertion) \<Rightarrow> 'a hyperassertion" where
  "general_join f S \<longleftrightarrow> (\<exists>F. S = (\<Union>x. F x) \<and> (\<forall>x. f x (F x)))"


lemma join_closed_by_union:
  assumes "closed_by_union Q"
  shows "join Q Q = Q"
proof
  fix S
  show "join Q Q S \<longleftrightarrow> Q S"
    by (metis assms closed_by_union_def join_def sup_idem)
qed

lemma entails_join_entails:
  assumes "entails A1 B1"
      and "entails A2 B2"
    shows "entails (join A1 A2) (join B1 B2)"
proof (rule entailsI)
  fix S assume "join A1 A2 S"
  then obtain S1 S2 where "A1 S1" "A2 S2" "S = S1 \<union> S2"
    by (metis join_def)
  then show "join B1 B2 S"
    by (metis assms(1) assms(2) entailsE join_def)
qed


text \<open>Notation 2\<close>
definition natural_partition where
  "natural_partition I S \<longleftrightarrow> (\<exists>F. S = (\<Union>n. F n) \<and> (\<forall>n. I n (F n)))"

lemma natural_partitionI:
  assumes "S = (\<Union>n. F n)"
      and "\<And>n. I n (F n)"
    shows "natural_partition I S"
  using assms(1) assms(2) natural_partition_def by blast

lemma natural_partitionE:
  assumes "natural_partition I S"
  obtains F where "S = (\<Union>n. F n)" "\<And>n. I n (F n)"
  by (meson assms natural_partition_def)


subsection \<open>Rules of the Logic\<close>

text \<open>Rules from figure 3\<close>

inductive syntactic_HHT ::
 "(('lvar, 'lval, 'pvar, 'pval) state hyperassertion) \<Rightarrow> ('pvar, 'pval) stmt \<Rightarrow> (('lvar, 'lval, 'pvar, 'pval) state hyperassertion) \<Rightarrow> bool"
   ("\<turnstile> {_} _ {_}" [51,0,0] 81) where
  RuleSkip: "\<turnstile> {P} Skip {P}"
| RuleCons: "\<lbrakk> entails P P' ; entails Q' Q ; \<turnstile> {P'} C {Q'} \<rbrakk> \<Longrightarrow> \<turnstile> {P} C {Q}"
| RuleSeq: "\<lbrakk> \<turnstile> {P} C1 {R} ; \<turnstile> {R} C2 {Q} \<rbrakk> \<Longrightarrow> \<turnstile> {P} (Seq C1 C2) {Q}"
| RuleIf: "\<lbrakk> \<turnstile> {P} C1 {Q1} ; \<turnstile> {P} C2 {Q2} \<rbrakk> \<Longrightarrow> \<turnstile> {P} (If C1 C2) {join Q1 Q2}"
| RuleWhile: "\<lbrakk> \<And>n. \<turnstile> {I n} C {I (Suc n)} \<rbrakk> \<Longrightarrow> \<turnstile> {I 0} (While C) {natural_partition I}"
| RuleAssume: "\<turnstile> { (\<lambda>S. P (Set.filter (b \<circ> snd) S)) } (Assume b) {P}"
| RuleAssign: "\<turnstile> { (\<lambda>S. P { (l, \<sigma>(x := e \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> S }) } (Assign x e) {P}"
| RuleHavoc: "\<turnstile> { (\<lambda>S. P { (l, \<sigma>(x := v)) |l \<sigma> v. (l, \<sigma>) \<in> S }) } (Havoc x) {P}"
| RuleExistsSet: "\<lbrakk>\<And>x::('lvar, 'lval, 'pvar, 'pval) state set. \<turnstile> {P x} C {Q x}\<rbrakk> \<Longrightarrow> \<turnstile> {exists P} C {exists Q}"


subsection \<open>Soundness\<close>

text \<open>Definition 6: Hyper-Triples\<close>
definition hyper_hoare_triple ("\<Turnstile> {_} _ {_}" [51,0,0] 81) where
  "\<Turnstile> {P} C {Q} \<longleftrightarrow> (\<forall>S. P S \<longrightarrow> Q (sem C S))"

lemma hyper_hoare_tripleI:
  assumes "\<And>S. P S \<Longrightarrow> Q (sem C S)"
  shows "\<Turnstile> {P} C {Q}"
  by (simp add: assms hyper_hoare_triple_def)

lemma hyper_hoare_tripleE:
  assumes "\<Turnstile> {P} C {Q}"
      and "P S"
    shows "Q (sem C S)"
  using assms(1) assms(2) hyper_hoare_triple_def
  by metis

lemma consequence_rule:
  assumes "entails P P'"
      and "entails Q' Q"
      and "\<Turnstile> {P'} C {Q'}"
    shows "\<Turnstile> {P} C {Q}"
  by (metis (no_types, opaque_lifting) assms(1) assms(2) assms(3) entails_def hyper_hoare_triple_def)

lemma skip_rule:
  "\<Turnstile> {P} Skip {P}"
  by (simp add: hyper_hoare_triple_def sem_skip)

lemma assume_rule:
  "\<Turnstile> { (\<lambda>S. P (Set.filter (b \<circ> snd) S)) } (Assume b) {P}"
proof (rule hyper_hoare_tripleI)
  fix S assume "P (Set.filter (b \<circ> snd) S)"
  then show "P (sem (Assume b) S)"
    by (simp add: assume_sem)
qed

lemma seq_rule:
  assumes "\<Turnstile> {P} C1 {R}"
    and "\<Turnstile> {R} C2 {Q}"
    shows "\<Turnstile> {P} Seq C1 C2 {Q}"
  using assms(1) assms(2) hyper_hoare_triple_def sem_seq
  by metis

lemma if_rule:
  assumes "\<Turnstile> {P} C1 {Q1}"
      and "\<Turnstile> {P} C2 {Q2}"
    shows "\<Turnstile> {P} If C1 C2 {join Q1 Q2}"
  by (metis (full_types) assms(1) assms(2) hyper_hoare_triple_def join_def sem_if)

lemma sem_assign:
  "sem (Assign x e) S = {(l, \<sigma>(x := e \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> S}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix l \<sigma>'
    assume "(l, \<sigma>') \<in> sem (Assign x e) S"
    then obtain \<sigma> where "(l, \<sigma>) \<in> S" "single_sem (Assign x e) \<sigma> \<sigma>'"
      by (metis fst_eqD in_sem snd_conv)
    then show "(l, \<sigma>') \<in> {(l, \<sigma>(x := e \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> S}"
      by blast
  qed
  show "?B \<subseteq> ?A"
  proof (rule subsetPairI)
    fix l \<sigma>'
    assume "(l, \<sigma>') \<in> ?B"
    then obtain \<sigma> where "\<sigma>' = \<sigma>(x := e \<sigma>)" "(l, \<sigma>) \<in> S"
      by blast
    then show "(l, \<sigma>') \<in> ?A"
      by (metis SemAssign fst_eqD in_sem snd_conv)
  qed
qed

lemma assign_rule:
  "\<Turnstile> { (\<lambda>S. P { (l, \<sigma>(x := e \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> S }) } (Assign x e) {P}"
proof (rule hyper_hoare_tripleI)
  fix S assume "P {(l, \<sigma>(x := e \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> S}"
  then show "P (sem (Assign x e) S)" using sem_assign
    by metis
qed

lemma sem_havoc:
  "sem (Havoc x) S = {(l, \<sigma>(x := v)) |l \<sigma> v. (l, \<sigma>) \<in> S}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix l \<sigma>'
    assume "(l, \<sigma>') \<in> sem (Havoc x) S"
    then obtain \<sigma> where "(l, \<sigma>) \<in> S" "single_sem (Havoc x) \<sigma> \<sigma>'"
      by (metis fst_eqD in_sem snd_conv)
    then show "(l, \<sigma>') \<in> {(l, \<sigma>(x := v)) |l \<sigma> v. (l, \<sigma>) \<in> S}"
      by blast
  qed
  show "?B \<subseteq> ?A"
  proof (rule subsetPairI)
    fix l \<sigma>'
    assume "(l, \<sigma>') \<in> ?B"
    then obtain \<sigma> v where "\<sigma>' = \<sigma>(x := v)" "(l, \<sigma>) \<in> S"
      by blast
    then show "(l, \<sigma>') \<in> ?A"
      by (metis SemHavoc fst_eqD in_sem snd_conv)
  qed
qed

lemma havoc_rule:
  "\<Turnstile> { (\<lambda>S. P { (l, \<sigma>(x := v)) |l \<sigma> v. (l, \<sigma>) \<in> S }) } (Havoc x) {P}"
proof (rule hyper_hoare_tripleI)
  fix S assume "P { (l, \<sigma>(x := v)) |l \<sigma> v. (l, \<sigma>) \<in> S }"
  then show "P (sem (Havoc x) S)" using sem_havoc by metis
qed


text \<open>Loops\<close>

lemma indexed_invariant_then_power:
  assumes "\<And>n. hyper_hoare_triple (I n) C (I (Suc n))"
      and "I 0 S"
  shows "I n (iterate_sem n C S)"
  using assms
proof (induct n arbitrary: S)
next
  case (Suc n)
  then have "I n (iterate_sem n C S)"
    by blast
  then have "I (Suc n) (sem C (iterate_sem n C S))"
    using Suc.prems(1) hyper_hoare_tripleE by blast
  then show ?case
    by (simp add: Suc.hyps Suc.prems(1))
qed (auto)

lemma while_rule:
  assumes "\<And>n. hyper_hoare_triple (I n) C (I (Suc n))"
  shows "hyper_hoare_triple (I 0) (While C) (natural_partition I)"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "I 0 S"
  show "natural_partition I (sem (While C) S)"
  proof (rule natural_partitionI)
    show "sem (While C) S = \<Union> (range (\<lambda>n. iterate_sem n C S))"
      by (simp add: sem_while)
    fix n show "I n (iterate_sem n C S)"
      by (simp add: asm0 assms indexed_invariant_then_power)
  qed
qed


text \<open>Additional rules\<close>

lemma empty_pre:
  "hyper_hoare_triple (\<lambda>_. False) C QQ"
  by (simp add: hyper_hoare_triple_def)

lemma full_post:
  "hyper_hoare_triple P C (\<lambda>_. True)"
  by (simp add: hyper_hoare_triple_def)


lemma rule_join:
  assumes "\<Turnstile> {P} C {Q}"
      and "hyper_hoare_triple P' C Q'"
    shows "hyper_hoare_triple (join P P') C (join Q Q')"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "join P P' S"
  then obtain S1 S2 where "S = S1 \<union> S2" "P S1" "P' S2"
    by (metis join_def)
  then have "sem C S = sem C S1 \<union> sem C S2"
    using sem_union by auto
  then show "join Q Q' (sem C S)"
    by (metis \<open>P S1\<close> \<open>P' S2\<close> assms(1) assms(2) hyper_hoare_tripleE join_def)
qed

lemma rule_general_join:
  assumes "\<And>x. \<Turnstile> {P x} C {Q x}"
  shows "hyper_hoare_triple (general_join P) C (general_join Q)"
proof (rule hyper_hoare_tripleI)
  fix S assume "general_join P S"
  then obtain F where asm0: "S = (\<Union>x. F x)" "\<And>x. P x (F x)"
    by (meson general_join_def)
  have "sem C S = (\<Union>x. sem C (F x))"
    by (simp add: asm0(1) sem_split_general)
  moreover have "\<And>x. Q x (sem C (F x))"
    using asm0(2) assms hyper_hoare_tripleE by blast
  ultimately show "general_join Q (sem C S)"
    by (metis general_join_def)
qed

lemma rule_conj:
  assumes "\<Turnstile> {P} C {Q}"
      and "hyper_hoare_triple P' C Q'"
    shows "hyper_hoare_triple (conj P P') C (conj Q Q')"
proof (rule hyper_hoare_tripleI)
  fix S assume "Logic.conj P P' S"
  then show "Logic.conj Q Q' (sem C S)"
    by (metis assms(1) assms(2) conj_def hyper_hoare_tripleE)
qed

text \<open>Generalization\<close>

lemma rule_forall:
  assumes "\<And>x. \<Turnstile> {P x} C {Q x}"
  shows "hyper_hoare_triple (forall P) C (forall Q)"
  by (metis assms forall_def hyper_hoare_triple_def)

lemma rule_disj:
  assumes "\<Turnstile> {P} C {Q}"
      and "\<Turnstile> {P'} C {Q'}"
    shows "hyper_hoare_triple (disj P P') C (disj Q Q')"
  by (metis assms(1) assms(2) disj_def hyper_hoare_triple_def)

text \<open>Generalization\<close>

lemma rule_exists:
  assumes "\<And>x. \<Turnstile> {P x} C {Q x}"
  shows "\<Turnstile> {exists P} C {exists Q}"
  by (metis assms exists_def hyper_hoare_triple_def)

corollary variant_if_rule:
  assumes "hyper_hoare_triple P C1 Q"
      and "hyper_hoare_triple P C2 Q"
      and "closed_by_union Q"
    shows "hyper_hoare_triple P (If C1 C2) Q"
  by (metis assms(1) assms(2) assms(3) if_rule join_closed_by_union)


text \<open>Simplifying the rule\<close>

definition stable_by_infinite_union :: "'a hyperassertion \<Rightarrow> bool" where
  "stable_by_infinite_union I \<longleftrightarrow> (\<forall>F. (\<forall>S \<in> F. I S) \<longrightarrow> I (\<Union>S \<in> F. S))"

lemma stable_by_infinite_unionE:
  assumes "stable_by_infinite_union I"
      and "\<And>S. S \<in> F \<Longrightarrow> I S"
    shows "I (\<Union>S \<in> F. S)"
  using assms(1) assms(2) stable_by_infinite_union_def by blast

lemma stable_by_union_and_constant_then_I:
  assumes "\<And>n. I n = I'"
      and "stable_by_infinite_union I'"
    shows "natural_partition I = I'"
proof (rule ext)
  fix S show "natural_partition I S = I' S"
  proof
    show "I' S \<Longrightarrow> natural_partition I S"
    proof -
      assume "I' S"
      show "natural_partition I S"
      proof (rule natural_partitionI)
        show "S = \<Union> (range (\<lambda>n. S))"
          by simp
        fix n show "I n S"
          by (simp add: \<open>I' S\<close> assms(1))
      qed
    qed
    assume asm0: "natural_partition I S"
    then obtain F where "S = (\<Union>n. F n)" "\<And>n. I n (F n)"
      using natural_partitionE by blast
    let ?F = "{F n |n. True}"
    have "I' (\<Union>S\<in>?F. S)"
      using assms(2)
    proof (rule stable_by_infinite_unionE[of I'])
      fix S assume "S \<in> {F n |n. True}"
      then show "I' S"
        using \<open>\<And>n. I n (F n)\<close> assms(1) by force
    qed
    moreover have "(\<Union>S\<in>?F. S) = S"
      using \<open>S = (\<Union>n. F n)\<close> by auto
    ultimately show "I' S" by blast
  qed
qed

corollary simpler_rule_while:
  assumes "hyper_hoare_triple I C I"
    and "stable_by_infinite_union I"
  shows "hyper_hoare_triple I (While C) I"
proof -
  let ?I = "\<lambda>n. I"
  have "hyper_hoare_triple (?I 0) (While C) (natural_partition ?I)"
    using while_rule[of ?I C]
    by (simp add: assms(1) assms(2) stable_by_union_and_constant_then_I)
  then show ?thesis
    by (simp add: assms(2) stable_by_union_and_constant_then_I)
qed


text \<open>Theorem 1\<close>

theorem soundness:
  assumes "\<turnstile> {A} C {B}"
    shows "\<Turnstile> {A} C {B}"
  using assms
proof (induct rule: syntactic_HHT.induct)
  case (RuleSkip P)
  then show ?case
    using skip_rule by auto
next
  case (RuleCons P P' Q' Q C)
  then show ?case
    using consequence_rule by blast
next
  case (RuleExistsSet P C Q)
  then show ?case
    using rule_exists by blast
next
  case (RuleSeq P C1 R C2 Q)
  then show ?case
    using seq_rule by meson
next
  case (RuleIf P C1 Q1 C2 Q2)
  then show ?case
    using if_rule by blast
next
  case (RuleAssume P b)
  then show ?case
    by (simp add: assume_rule)
next
  case (RuleWhile I C)
  then show ?case
    using while_rule by blast
next
  case (RuleAssign x e)
  then show ?case
    by (simp add: assign_rule)
next
  case (RuleHavoc x)
  then show ?case
    using havoc_rule by fastforce
qed



subsection \<open>Completeness\<close>

definition complete
  where
  "complete P C Q \<longleftrightarrow> (\<Turnstile> {P} C {Q} \<longrightarrow> \<turnstile> {P} C {Q})"

lemma completeI:
  assumes "\<Turnstile> {P} C {Q} \<Longrightarrow> \<turnstile> {P} C {Q}"
  shows "complete P C Q"
  by (simp add: assms complete_def)

lemma completeE:
  assumes "complete P C Q"
      and "\<Turnstile> {P} C {Q}"
    shows "\<turnstile> {P} C {Q}"
  using assms complete_def by auto

lemma complete_if_aux:
  assumes "hyper_hoare_triple A (If C1 C2) B"
  shows "entails (\<lambda>S'. \<exists>S. A S \<and> S' = sem C1 S \<union> sem C2 S) B"
proof (rule entailsI)
  fix S' assume "\<exists>S. A S \<and> S' = sem C1 S \<union> sem C2 S"
  then show "B S'"
    by (metis assms hyper_hoare_tripleE sem_if)
qed

lemma complete_if:
  fixes P Q :: "('lvar, 'lval, 'pvar, 'pval) state hyperassertion"
  assumes "\<And>P1 Q1 :: ('lvar, 'lval, 'pvar, 'pval) state hyperassertion. complete P1 C1 Q1"
      and "\<And>P2 Q2 :: ('lvar, 'lval, 'pvar, 'pval) state hyperassertion. complete P2 C2 Q2"
    shows "complete P (If C1 C2) Q"
proof (rule completeI)
  assume asm0: "\<Turnstile> {P} If C1 C2 {Q}"

  show "\<turnstile> {P} stmt.If C1 C2 {Q}"
  proof (rule RuleCons)
    show "\<turnstile> {exists (\<lambda>V S. P S \<and> S = V)} stmt.If C1 C2 {exists (\<lambda>V. join (\<lambda>S. S = sem C1 V \<and> P V) (\<lambda>S. S = sem C2 V))}"
    proof (rule RuleExistsSet)
      fix V
      show "\<turnstile> {(\<lambda>S. P S \<and> S = V)} stmt.If C1 C2 {join (\<lambda>S. S = sem C1 V \<and> P V) (\<lambda>S. S = sem C2 V)}"
      proof (rule RuleIf)
        show "\<turnstile> {(\<lambda>S. P S \<and> S = V)} C1 {\<lambda>S. S = sem C1 V \<and> P V}"
          by (simp add: assms(1) completeE hyper_hoare_triple_def)
        show "\<turnstile> {(\<lambda>S. P S \<and> S = V)} C2 {\<lambda>S. S = sem C2 V}"
          by (simp add: assms(2) completeE hyper_hoare_triple_def)
      qed
    qed
    show "entails P (exists (\<lambda>V S. P S \<and> S = V))"
      by (simp add: entailsI exists_def)
    show "entails (exists (\<lambda>V. join (\<lambda>S. S = sem C1 V \<and> P V) (\<lambda>S. S = sem C2 V))) Q"
    proof (rule entailsI)
      fix S assume "exists (\<lambda>V. join (\<lambda>S. S = sem C1 V \<and> P V) (\<lambda>S. S = sem C2 V)) S"
      then obtain V where "join (\<lambda>S. S = sem C1 V \<and> P V) (\<lambda>S. S = sem C2 V) S"
        by (meson exists_def)
      then obtain S1 S2 where "S = S1 \<union> S2" "S1 = sem C1 V \<and> P V" "S2 = sem C2 V"
        by (simp add: join_def)
      then show "Q S"
        by (metis asm0 hyper_hoare_tripleE sem_if)
    qed
  qed
qed

lemma complete_seq_aux:
  assumes "hyper_hoare_triple A (Seq C1 C2) B"
  shows "\<exists>R. hyper_hoare_triple A C1 R \<and> hyper_hoare_triple R C2 B"
proof -
  let ?R = "\<lambda>S. \<exists>S'. A S' \<and> S = sem C1 S'"
  have "hyper_hoare_triple A C1 ?R"
    using hyper_hoare_triple_def by blast
  moreover have "hyper_hoare_triple ?R C2 B"
  proof (rule hyper_hoare_tripleI)
    fix S assume "\<exists>S'. A S' \<and> S = sem C1 S'"
    then obtain S' where asm0: "A S'" "S = sem C1 S'"
      by blast
    then show "B (sem C2 S)"
      by (metis assms hyper_hoare_tripleE sem_seq)
  qed
  ultimately show ?thesis by blast
qed


lemma complete_assume:
  "complete P (Assume b) Q"
proof (rule completeI)
  assume asm0: "\<Turnstile> {P} Assume b {Q}"
  show "\<turnstile> {P} Assume b {Q}"
  proof (rule RuleCons)
    show "\<turnstile> { (\<lambda>S. Q (Set.filter (b \<circ> snd) S)) } (Assume b) {Q}"
      by (simp add: RuleAssume)
    show "entails P (\<lambda>S. Q (Set.filter (b \<circ> snd) S))"
      by (metis (mono_tags, lifting) asm0 assume_sem entails_def hyper_hoare_tripleE)
    show "entails Q Q"      
      by (simp add: entailsI)
  qed
qed

lemma complete_skip:
  "complete P Skip Q"
  using completeI RuleSkip
  by (metis (mono_tags, lifting) entails_def hyper_hoare_triple_def sem_skip RuleCons)

lemma complete_assign:
  "complete P (Assign x e) Q"
proof (rule completeI)
  assume asm0: "\<Turnstile> {P} Assign x e {Q}"
  show "\<turnstile> {P} Assign x e {Q}"
  proof (rule RuleCons)
    show "\<turnstile> {(\<lambda>S. Q {(l, \<sigma>(x := e \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> S})} Assign x e {Q}"
      by (simp add: RuleAssign)
    show "entails P (\<lambda>S. Q {(l, \<sigma>(x := e \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> S})"
    proof (rule entailsI)
      fix S assume "P S"
      then show "Q {(l, \<sigma>(x := e \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> S}"
        by (metis asm0 hyper_hoare_triple_def sem_assign)
    qed
    show "entails Q Q"
      by (simp add: entailsI)
  qed
qed

lemma complete_havoc:
  "complete P (Havoc x) Q"
proof (rule completeI)
  assume asm0: "\<Turnstile> {P} Havoc x {Q}"
  show "\<turnstile> {P} Havoc x {Q}"
  proof (rule RuleCons)
    show "\<turnstile> { (\<lambda>S. Q { (l, \<sigma>(x := v)) |l \<sigma> v. (l, \<sigma>) \<in> S }) } (Havoc x) {Q}"
      using RuleHavoc by fast
    show "entails P (\<lambda>S. Q {(l, \<sigma>(x := v)) |l \<sigma> v. (l, \<sigma>) \<in> S})"
    proof (rule entailsI)
      fix S assume "P S"
      then show "Q {(l, \<sigma>(x := v)) |l \<sigma> v. (l, \<sigma>) \<in> S}"
        by (metis asm0 hyper_hoare_triple_def sem_havoc)
    qed
    show "entails Q Q"
      by (simp add: entailsI)
  qed
qed

lemma complete_seq:
  assumes "\<And>R. complete P C1 R"
      and "\<And>R. complete R C2 Q"
    shows "complete P (Seq C1 C2) Q"
  by (meson RuleSeq assms(1) assms(2) completeE completeI complete_seq_aux)



fun construct_inv
  where
  "construct_inv P C 0 = P"
| "construct_inv P C (Suc n) = (\<lambda>S. (\<exists>S'. S = sem C S' \<and> construct_inv P C n S'))"

lemma iterate_sem_ind:
  assumes "construct_inv P C n S'"
  shows "\<exists>S. P S \<and> S' = iterate_sem n C S"
  using assms
by (induct n arbitrary: S') (auto)


lemma complete_while_aux:
  assumes "hyper_hoare_triple (\<lambda>S. P S \<and> S = V) (While C) Q"
  shows "entails (natural_partition (construct_inv (\<lambda>S. P S \<and> S = V) C)) Q"
proof (rule entailsI)
  fix S assume "natural_partition (construct_inv (\<lambda>S. P S \<and> S = V) C) S"

  then obtain F where asm0: "S = (\<Union>n. F n)" "\<And>n. construct_inv (\<lambda>S. P S \<and> S = V) C n (F n)"
    using natural_partitionE by blast
  then have "P (F 0) \<and> F 0 = V"
    by (metis (mono_tags, lifting) construct_inv.simps(1))
  then have "Q (\<Union>n. iterate_sem n C (F 0))"
    using assms hyper_hoare_triple_def[of "\<lambda>S. P S \<and> S = V" "While C" Q] sem_while
    by metis
  moreover have "\<And>n. F n = iterate_sem n C V"
  proof -
    fix n
    obtain S' where "P S' \<and> S' = V" "F n = iterate_sem n C S'"
      using asm0(2) iterate_sem_ind by blast
    then show "F n = iterate_sem n C V"
      by simp
  qed
  ultimately show "Q S"
    using asm0(1) by auto
qed

lemma complete_while:
  fixes P Q :: "('lvar, 'lval, 'pvar, 'pval) state hyperassertion"
  assumes "\<And>P' Q' :: ('lvar, 'lval, 'pvar, 'pval) state hyperassertion. complete P' C Q'"
    shows "complete P (While C) Q"
proof (rule completeI)
  assume asm0: "hyper_hoare_triple P (While C) Q"

  let ?I = "\<lambda>V. construct_inv (\<lambda>S. P S \<and> S = V) C"

  have r: "\<And>V. syntactic_HHT (?I V 0) (While C) (natural_partition (?I V))"
  proof (rule RuleWhile)
    fix V n show "syntactic_HHT (construct_inv (\<lambda>S. P S \<and> S = V) C n) C (construct_inv (\<lambda>S. P S \<and> S = V) C (Suc n))"
      by (meson assms completeE construct_inv.simps(2) hyper_hoare_tripleI)
  qed

  show "syntactic_HHT P (While C) Q"
  proof (rule RuleCons)
    show "syntactic_HHT (exists (\<lambda>V. ?I V 0)) (While C) (exists (\<lambda>V. ((natural_partition (?I V)))))"
      using r by (rule RuleExistsSet)
    show "entails P (exists (\<lambda>V. construct_inv (\<lambda>S. P S \<and> S = V) C 0))"
      by (simp add: entailsI exists_def)
    show "entails (exists (\<lambda>V. natural_partition (construct_inv (\<lambda>S. P S \<and> S = V) C))) Q"
    proof (rule entailsI)
      fix S' assume "exists (\<lambda>V. natural_partition (construct_inv (\<lambda>S. P S \<and> S = V) C)) S'"
      then obtain V where "natural_partition (construct_inv (\<lambda>S. P S \<and> S = V) C) S'"
        by (meson exists_def)
      moreover have "entails (natural_partition (construct_inv (\<lambda>S. P S \<and> S = V) C)) Q"
      proof (rule complete_while_aux)
        show "hyper_hoare_triple (\<lambda>S. P S \<and> S = V) (While C) Q"
          using asm0 hyper_hoare_triple_def[of "\<lambda>S. P S \<and> S = V"]
          hyper_hoare_triple_def[of P "While C" Q] by auto
      qed
      ultimately show "Q S'"
        by (simp add: entails_def)
    qed
  qed
qed


text \<open>Theorem 2\<close>

theorem completeness:
  fixes P Q :: "('lvar, 'lval, 'pvar, 'pval) state hyperassertion"
  assumes "\<Turnstile> {P} C {Q}"
  shows "\<turnstile> {P} C {Q}"
  using assms
proof (induct C arbitrary: P Q)
  case (Assign x1 x2)
  then show ?case
    using completeE complete_assign by fast
next
  case (Seq C1 C2)
  then show ?case
    using complete_def complete_seq by meson
next
  case (If C1 C2)
  then show ?case
    using complete_def complete_if by meson
next
  case Skip
  then show ?case
    using complete_def complete_skip by meson
next
  case (Havoc x)
  then show ?case
    by (simp add: completeE complete_havoc)
next
  case (Assume b)
  then show ?case
    by (simp add: completeE complete_assume)
next
  case (While C)
  then show ?case
    using complete_def complete_while by blast
qed


subsection \<open>Disproving Hyper-Triples\<close>

definition sat where "sat P \<longleftrightarrow> (\<exists>S. P S)"

text \<open>Theorem 4\<close>

theorem disproving_triple:
  "\<not> \<Turnstile> {P} C {Q} \<longleftrightarrow> (\<exists>P'. sat P' \<and> entails P' P \<and> \<Turnstile> {P'} C {\<lambda>S. \<not> Q S})" (is "?A \<longleftrightarrow> ?B")
proof
  assume "\<not> \<Turnstile> {P} C {Q}"
  then obtain S where asm0: "P S" "\<not> Q (sem C S)"
    using hyper_hoare_triple_def by blast
  let ?P = "\<lambda>S'. S = S'"
  have "entails ?P P"
    by (simp add: asm0(1) entails_def)
  moreover have "\<Turnstile> {?P} C {\<lambda>S. \<not> Q S}"
    by (simp add: asm0(2) hyper_hoare_triple_def)
  moreover have "sat ?P"
    by (simp add: sat_def)
  ultimately show ?B by blast
next
  assume "\<exists>P'. sat P' \<and> entails P' P \<and> \<Turnstile> {P'} C {\<lambda>S. \<not> Q S}"
  then obtain P' where asm0: "sat P'" "entails P' P" "\<Turnstile> {P'} C {\<lambda>S. \<not> Q S}"
    by blast
  then obtain S where "P' S"
    by (meson sat_def)
  then show ?A
    using asm0(2) asm0(3) entailsE hyper_hoare_tripleE
    by (metis (no_types, lifting))
qed

definition differ_only_by where
  "differ_only_by a b x \<longleftrightarrow> (\<forall>y. y \<noteq> x \<longrightarrow> a y = b y)"

lemma differ_only_byI:
  assumes "\<And>y. y \<noteq> x \<Longrightarrow> a y = b y"
  shows "differ_only_by a b x"
  by (simp add: assms differ_only_by_def)

lemma diff_by_update:
  "differ_only_by (a(x := v)) a x"
  by (simp add: differ_only_by_def)

lemma diff_by_comm:
  "differ_only_by a b x \<longleftrightarrow> differ_only_by b a x"
  by (metis (mono_tags, lifting) differ_only_by_def)

lemma diff_by_trans:
  assumes "differ_only_by a b x"
      and "differ_only_by b c x"
    shows "differ_only_by a c x"
  by (metis assms(1) assms(2) differ_only_by_def)


definition not_free_var_of where
  "not_free_var_of P x \<longleftrightarrow> (\<forall>states states'.
  (\<forall>i. differ_only_by (fst (states i)) (fst (states' i)) x \<and> snd (states i) = snd (states' i))
  \<longrightarrow> (states \<in> P \<longleftrightarrow> states' \<in> P))"


lemma not_free_var_ofE:
  assumes "not_free_var_of P x"
      and "\<And>i. differ_only_by (fst (states i)) (fst (states' i)) x"
      and "\<And>i. snd (states i) = snd (states' i)"
      and "states \<in> P"
    shows "states' \<in> P"
  using not_free_var_of_def[of P x] assms by blast


subsection \<open>Synchronized Rule for Branching\<close>

definition combine where
  "combine from_nat x P1 P2 S \<longleftrightarrow> P1 (Set.filter (\<lambda>\<phi>. fst \<phi> x = from_nat 1) S) \<and> P2 (Set.filter (\<lambda>\<phi>. fst \<phi> x = from_nat 2) S)"

lemma combineI:
  assumes "P1 (Set.filter (\<lambda>\<phi>. fst \<phi> x = from_nat 1) S) \<and> P2 (Set.filter (\<lambda>\<phi>. fst \<phi> x = from_nat 2) S)"
  shows "combine from_nat x P1 P2 S"
  by (simp add: assms combine_def)

definition modify_lvar_to where
  "modify_lvar_to x v \<phi> = ((fst \<phi>)(x := v), snd \<phi>)"

lemma logical_var_in_sem_same:
  assumes "\<And>\<phi>. \<phi> \<in> S \<Longrightarrow> fst \<phi> x = a"
      and "\<phi>' \<in> sem C S"
    shows "fst \<phi>' x = a"
  by (metis assms(1) assms(2) fst_conv in_sem)

lemma recover_after_sem:
  assumes "a \<noteq> b"
      and "\<And>\<phi>. \<phi> \<in> S1 \<Longrightarrow> fst \<phi> x = a"
      and "\<And>\<phi>. \<phi> \<in> S2 \<Longrightarrow> fst \<phi> x = b"
    shows "sem C S1 = Set.filter (\<lambda>\<phi>. fst \<phi> x = a) (sem C (S1 \<union> S2))" (is "?A = ?B")
proof
  have r: "sem C (S1 \<union> S2) = sem C S1 \<union> sem C S2"
    by (simp add: sem_union)
  moreover have r1: "\<And>\<phi>'. \<phi>' \<in> sem C S1 \<Longrightarrow> fst \<phi>' x = a"
    by (metis assms(2) fst_conv in_sem)
  moreover have r2: "\<And>\<phi>'. \<phi>' \<in> sem C S2 \<Longrightarrow> fst \<phi>' x = b"
    by (metis assms(3) fst_conv in_sem)
  show "?B \<subseteq> ?A"
  proof (rule subsetPairI)
    fix l \<sigma>
    assume "(l, \<sigma>) \<in> Set.filter (\<lambda>\<phi>. fst \<phi> x = a) (sem C (S1 \<union> S2))"
    then show "(l, \<sigma>) \<in> sem C S1"
      using assms(1) r r2 by auto
  qed
  show "?A \<subseteq> ?B"
    by (simp add: r r1 subsetI)
qed

lemma injective_then_ok:
  assumes "a \<noteq> b"
      and "S1' = (modify_lvar_to x a) ` S1"
      and "S2' = (modify_lvar_to x b) ` S2"
    shows "Set.filter (\<lambda>\<phi>. fst \<phi> x = a) (S1' \<union> S2') = S1'" (is "?A = ?B")
proof
  show "?B \<subseteq> ?A"
  proof (rule subsetI)
    fix y assume "y \<in> S1'"
    then have "fst y x = a" using modify_lvar_to_def assms(2)
      by (metis (mono_tags, lifting) fst_conv fun_upd_same image_iff)
    then show "y \<in> Set.filter (\<lambda>\<phi>. fst \<phi> x = a) (S1' \<union> S2')"
      by (simp add: \<open>y \<in> S1'\<close>)
  qed
  show "?A \<subseteq> ?B"
  proof
    fix y assume "y \<in> ?A"
    then have "y \<notin> S2'"
      by (metis (mono_tags, lifting) assms(1) assms(3) fun_upd_same image_iff member_filter modify_lvar_to_def prod.sel(1))
    then show "y \<in> ?B"
      using \<open>y \<in> Set.filter (\<lambda>\<phi>. fst \<phi> x = a) (S1' \<union> S2')\<close> by auto
  qed
qed

definition not_free_var_hyper where
  "not_free_var_hyper x P \<longleftrightarrow> (\<forall>S v. P S \<longleftrightarrow> P ((modify_lvar_to x v) ` S))"

definition injective where
  "injective f \<longleftrightarrow> (\<forall>a b. a \<noteq> b \<longrightarrow> f a \<noteq> f b)"

lemma sem_of_modify_lvar:
  "sem C ((modify_lvar_to r v) ` S) = (modify_lvar_to r v) ` (sem C S)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetI)
    fix y assume asm0: "y \<in> ?A"
    then obtain x where "x \<in> (modify_lvar_to r v) ` S" "single_sem C (snd x) (snd y)" "fst x = fst y"
      by (metis fst_conv in_sem snd_conv)
    then obtain xx where "xx \<in> S" "x = modify_lvar_to r v xx"
      by blast
    then have "(fst xx, snd y) \<in> sem C S"
      by (metis \<open>\<langle>C, snd x\<rangle> \<rightarrow> snd y\<close> fst_conv in_sem modify_lvar_to_def prod.collapse snd_conv)
    then show "y \<in> ?B"
      by (metis \<open>fst x = fst y\<close> \<open>x = modify_lvar_to r v xx\<close> fst_eqD modify_lvar_to_def prod.exhaust_sel rev_image_eqI snd_eqD)
  qed
  show "?B \<subseteq> ?A"
  proof (rule subsetI)
    fix y assume "y \<in> modify_lvar_to r v ` sem C S"
    then obtain yy where "y = modify_lvar_to r v yy" "yy \<in> sem C S"
      by blast
    then obtain x where "x \<in> S" "fst x = fst yy" "single_sem C (snd x) (snd yy)"
      by (metis fst_conv in_sem snd_conv)
    then have "fst (modify_lvar_to r v x) = fst y"
      by (simp add: \<open>y = modify_lvar_to r v yy\<close> modify_lvar_to_def)
    then show "y \<in> sem C (modify_lvar_to r v ` S)"
      by (metis (mono_tags, lifting) \<open>\<langle>C, snd x\<rangle> \<rightarrow> snd yy\<close> \<open>x \<in> S\<close> \<open>y = modify_lvar_to r v yy\<close> fst_conv
          image_eqI in_sem modify_lvar_to_def snd_conv)
  qed
qed

text \<open>Proposition 15 (appendix C).\<close>

theorem if_sync_rule:
  assumes "\<Turnstile> {P} C1 {P1}"
      and "\<Turnstile> {P} C2 {P2}"
      and "\<Turnstile> {combine from_nat x P1 P2} C {combine from_nat x R1 R2}"
      and "\<Turnstile> {R1} C1' {Q1}"
      and "\<Turnstile> {R2} C2' {Q2}"

      and "not_free_var_hyper x P1"
      and "not_free_var_hyper x P2"
      and "injective (from_nat :: nat \<Rightarrow> 'a)"

      and "not_free_var_hyper x R1"
      and "not_free_var_hyper x R2"

    shows "\<Turnstile> {P} If (Seq C1 (Seq C C1')) (Seq C2 (Seq C C2')) {join Q1 Q2}"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "P S"
  have r0: "sem (stmt.If (Seq C1 (Seq C C1')) (Seq C2 (Seq C C2'))) S
  = sem C1' (sem C (sem C1 S)) \<union> sem C2' (sem C (sem C2 S))"
    by (simp add: sem_if sem_seq)
  moreover have "P1 (sem C1 S) \<and> P2 (sem C2 S)"
    using asm0 assms(1) assms(2) hyper_hoare_tripleE by blast

  let ?S1 = "(modify_lvar_to x (from_nat 1)) ` (sem C1 S)"
  let ?S2 = "(modify_lvar_to x (from_nat 2)) ` (sem C2 S)"
  let ?f1 = "Set.filter (\<lambda>\<phi>. fst \<phi> x = from_nat 1)"
  let ?f2 = "Set.filter (\<lambda>\<phi>. fst \<phi> x = from_nat 2)"

  have r: "from_nat 1 \<noteq> from_nat 2"
    by (metis Suc_1 assms(8) injective_def n_not_Suc_n)

  have "P1 ?S1 \<and> P2 ?S2"
    by (meson \<open>P1 (sem C1 S) \<and> P2 (sem C2 S)\<close> assms(6) assms(7) not_free_var_hyper_def)
  moreover have rr1: "Set.filter (\<lambda>\<phi>. fst \<phi> x = from_nat 1) (?S1 \<union> ?S2) = ?S1"
    using injective_then_ok[of "from_nat 1" "from_nat 2" ?S1 x]
    by (metis (no_types, lifting) assms(8) injective_def num.simps(4) one_eq_numeral_iff)
  moreover have rr2: "Set.filter (\<lambda>\<phi>. fst \<phi> x = from_nat 2) (?S1 \<union> ?S2) = ?S2"
    using injective_then_ok[of "from_nat 2" "from_nat 1" ?S2 x]
    by (metis (no_types, lifting) assms(8) injective_def one_eq_numeral_iff sup_commute verit_eq_simplify(10))
  ultimately have "combine from_nat x P1 P2 (?S1 \<union> ?S2)"
    by (metis combineI)
  then have "combine from_nat x R1 R2 (sem C (?S1 \<union> ?S2))"
    using assms(3) hyper_hoare_tripleE by blast
  moreover have "?f1 (sem C (?S1 \<union> ?S2)) = sem C ?S1"
    using recover_after_sem[of "from_nat 1" "from_nat 2" ?S1 x ?S2] r rr1 rr2
      member_filter[of _ "\<lambda>\<phi>. fst \<phi> x = from_nat 1"] member_filter[of _ "\<lambda>\<phi>. fst \<phi> x = from_nat 2"]
    by metis
  then have "R1 (sem C ?S1)"
    by (metis (mono_tags) calculation combine_def)
  then have "R1 (sem C (sem C1 S))"
    by (metis assms(9) not_free_var_hyper_def sem_of_modify_lvar)
  moreover have "?f2 (sem C (?S1 \<union> ?S2)) = sem C ?S2"
    using recover_after_sem[of "from_nat 2" "from_nat 1" ?S2 x ?S1] r rr1 rr2 sup_commute[of ]
      member_filter[of _ "\<lambda>\<phi>. fst \<phi> x = from_nat 1" "?S1 \<union> ?S2"] member_filter[of _ "\<lambda>\<phi>. fst \<phi> x = from_nat 2" "?S1 \<union> ?S2"]
    by metis
  then have "R2 (sem C ?S2)"
    by (metis (mono_tags) calculation(1) combine_def)
  then have "R2 (sem C (sem C2 S))"
    by (metis assms(10) not_free_var_hyper_def sem_of_modify_lvar)

  then show "join Q1 Q2 (sem (stmt.If (Seq C1 (Seq C C1')) (Seq C2 (Seq C C2'))) S)"
    by (metis (full_types) r0 assms(4) assms(5) calculation(2) hyper_hoare_tripleE join_def)
qed

end