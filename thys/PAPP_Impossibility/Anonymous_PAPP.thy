(*
  File:     Anonymous_PAPP.thy
  Author:   Manuel Eberl, University of Innsbruck 
*)
section \<open>Anonymous Party Approval Rules\<close>
theory Anonymous_PAPP
  imports Complex_Main "Randomised_Social_Choice.Order_Predicates" PAPP_Multiset_Extras
begin

text \<open>
  In this section we will define (anonymous) P-APP rules and some basic desirable properties
  of P-APP rules.
\<close>

subsection \<open>Definition of the General Setting\<close>

text \<open>
  The following locale encapsulates an anonymous \<^emph>\<open>party approval election\<close>; that is:

    \<^item> a number of voters

    \<^item> a set of parties

    \<^item> the size of the desired committee

  The number of parties and voters is assumed to be finite and non-zero.
  As a modelling choice, we do not distinguish the voters at all; there is no explicit set
  of voters. We only care about their number.
\<close>
locale anon_papp_election = 
  fixes n_voters :: nat and parties :: "'a set" and committee_size :: nat
  assumes finite_parties [simp, intro]: "finite parties"
  assumes n_voters_pos: "n_voters > 0"
  assumes nonempty_parties [simp]: "parties \<noteq> {}"
begin

text \<open>
  The result of a P-APP election is a committee, i.e.\ a multiset of parties with
  the desired size.
\<close>
definition is_committee :: "'a multiset \<Rightarrow> bool" where
  "is_committee W \<longleftrightarrow> set_mset W \<subseteq> parties \<and> size W = committee_size"

end


text \<open>
  A \<^emph>\<open>preference profile\<close> for a P-APP collection consists of one approval list (i.e.\ a set of
  approved parties) for each voter. Since we are in an anonymous setting, this means that
  we have a \<^emph>\<open>multiset\<close> consisting of \<open>n\<close> sets of parties (where \<open>n\<close> is the number of voters).

  Moreover, we make the usual assumption that the approval lists must be non-empty.
\<close>
locale anon_papp_profile = anon_papp_election +
  fixes A :: "'a set multiset"
  assumes A_subset: "\<And>X. X \<in># A \<Longrightarrow> X \<subseteq> parties"
  assumes A_nonempty: "{} \<notin># A"
  assumes size_A: "size A = n_voters"
begin

lemma A_nonempty': "A \<noteq> {#}"
  using size_A n_voters_pos by auto

end


context anon_papp_election
begin

abbreviation
  is_pref_profile where "is_pref_profile \<equiv> anon_papp_profile n_voters parties"

lemma is_pref_profile_iff:
  "is_pref_profile A \<longleftrightarrow> set_mset A \<subseteq> Pow parties - {{}} \<and> size A = n_voters"
  unfolding anon_papp_profile_def anon_papp_profile_axioms_def
  using anon_papp_election_axioms by auto  


lemma not_is_pref_profile_empty [simp]: "\<not>is_pref_profile {#}"
  using anon_papp_profile.A_nonempty'[of n_voters]
  by auto



text \<open>
  The following relation is a key definition: it takes an approval list \<open>A\<close> and turns it
  into a preference relation on committees. A committee is to be at least as good as another
  if the number of approved parties in it is at least as big.

  This relation is a reflexive, transitive, and total.
\<close>
definition committee_preference :: "'a set \<Rightarrow> 'a multiset relation" ("Comm") where
  "W1 \<preceq>[Comm(A)] W2 \<longleftrightarrow> size {# x\<in>#W1. x \<in> A #} \<le> size {# x\<in>#W2. x \<in> A #}"

lemma not_strict_Comm [simp]: "\<not>(W1 \<prec>[Comm(A)] W2) \<longleftrightarrow> W1 \<succeq>[Comm(A)] W2"
  by (auto simp: committee_preference_def strongly_preferred_def)

lemma not_weak_Comm [simp]: "\<not>(W1 \<preceq>[Comm(A)] W2) \<longleftrightarrow> W1 \<succ>[Comm(A)] W2"
  by (auto simp: committee_preference_def strongly_preferred_def)

sublocale Comm: preorder "Comm(A)" "\<lambda>x y. x \<prec>[Comm(A)] y"
  by standard (auto simp: committee_preference_def strongly_preferred_def)

lemma strong_committee_preference_iff:
  "W1 \<prec>[Comm(A)] W2 \<longleftrightarrow> size {# x\<in>#W1. x \<in> A #} < size {# x\<in>#W2. x \<in> A #}"
  by (auto simp: committee_preference_def strongly_preferred_def)


text \<open>
  We also define the Pareto ordering on parties induced by a given preference profile:
  One party is at least as good (in the Pareto relation) as another if all voters agree that
  it is at least as good. That is, $y \succeq x$ in the Pareto ordering if all voters who
  approve $x$ also approve $y$.

  This relation is also reflexive and transitive.
\<close>
definition Pareto :: "'a set multiset \<Rightarrow> 'a relation" where
  "x \<preceq>[Pareto(A)] y \<longleftrightarrow> x \<in> parties \<and> y \<in> parties \<and> (\<forall>X\<in>#A. x \<in> X \<longrightarrow> y \<in> X)"

sublocale Pareto: preorder_on parties "Pareto A"
  by standard (auto simp: Pareto_def)


text \<open>
  Pareto losers are parties that are (strictly) Pareto-dominated, i.e.\ there
  exists some other party that all voters consider to be at least as good and at least
  one voter considers it to be strictly better.
\<close>
definition pareto_losers :: "'a set multiset \<Rightarrow> 'a set" where
  "pareto_losers A = {x. \<exists>y. y \<succ>[Pareto(A)] x}"

end



subsection \<open>P-APP rules and Desirable Properties\<close>

text \<open>
  The following locale describes a P-APP rule. This is simply a function that maps every
  preference profile to a committee of the desired size.

  Note that in our setting, a P-APP rule has a fixed number of voters, a fixed set of parties,
  and a fixed desired committee size.
\<close>
locale anon_papp = anon_papp_election +
  fixes r :: "'a set multiset \<Rightarrow> 'a multiset"
  assumes rule_wf: "is_pref_profile A \<Longrightarrow> is_committee (r A)"



subsection \<open>Efficiency\<close>

text \<open>
  Efficiency is a common notion in Social Choice Theory. The idea is that if a party is
  ``obviously bad'', then it should not be chosen. What ``obviously bad'' means depends on the
  precise notion of Efficiency that is used. We will talk about two notions: Weak Efficiency and
  Pareto Efficiency.

  A P-APP rule is \<^emph>\<open>weakly efficient\<close> if a party that is approved by no one is never
  part of the output committee.

  Note that approval lists must be non-empty, so there is always at least one party that
  is approved by at least one voter.
\<close>
locale weakly_efficient_anon_papp = anon_papp +
  assumes weakly_efficient: "is_pref_profile A \<Longrightarrow> \<forall>X\<in>#A. x \<notin> X \<Longrightarrow> x \<notin># r A"


text \<open>
  A P-APP rule is \<^emph>\<open>Pareto-efficient\<close> if a Pareto-dominated party is never part of
  the output committee.
\<close>
locale pareto_optimal_anon_papp = anon_papp +
  assumes pareto_optimal: "is_pref_profile A \<Longrightarrow> x \<in> pareto_losers A \<Longrightarrow> x \<notin># r A"
begin

text \<open>
  Pareto-efficiency implies weak efficiency:
\<close>
sublocale weakly_efficient_anon_papp
proof
  fix A x
  assume A: "is_pref_profile A" and x: "\<forall>X\<in>#A. x \<notin> X"
  interpret anon_papp_profile n_voters parties committee_size A
    by fact
  have "A \<noteq> {#}"
    using A_nonempty' .
  then obtain X where X: "X \<in># A"
    by auto
  with A_nonempty have "X \<noteq> {}"
    by auto
  then obtain y where y: "y \<in> X"
    by auto
  show "x \<notin># r A"
  proof (cases "x \<in> parties")
    case False
    thus ?thesis
      using rule_wf[OF A] by (auto simp: is_committee_def)
  next
    case True
    have "y \<succ>[Pareto(A)] x"
      unfolding Pareto_def using X x y True A_subset[of X]
      by (auto simp: strongly_preferred_def)
    hence "x \<in> pareto_losers A"
      by (auto simp: pareto_losers_def)
    thus ?thesis
      using pareto_optimal[OF A] by auto
  qed
qed

end


subsection \<open>Strategyproofness\<close>

text \<open>
  Strategyproofness is another common notion in Social Choice Theory that generally encapsulates
  the notion that an voter should not be able to manipulate the outcome of an election in their
  favour by (unilaterally) submitting fake preferences; i.e.\ reporting one's preferences 
  truthfully should always be the optimal choice.

  A P-APP rule is called \<^emph>\<open>cardinality-strategyproof\<close> if an voter cannot obtain a better committee
  (i.e.\ one that contains strictly more of their approved parties) by submitting an approval
  list that is different from their real approval list.
\<close>

text \<open>
  To make the definition simpler, we first define the notion of \<^emph>\<open>manipulability\<close>: in the context
  of a particular P-APP rule \<open>r\<close>, a preference profile \<open>A\<close> is said to be manipulable by the voter
  \<open>i\<close> with the fake preference list \<open>Y\<close> if \<open>r(A(i := Y))\<close> contains strictly more parties
  approved by \<open>i\<close> than \<open>r(A)\<close>.

  Since we have anonymous profiles and do not talk about particular voters, we replace \<open>i\<close> with
  their approval list \<open>X\<close>. Since \<open>A\<close> is a multiset, the definition of manipulability
  becomes $r(A-\{X\}+\{Y\}) \succ_{X} r(A)$.
\<close>
definition (in anon_papp) card_manipulable where
  "card_manipulable A X Y \<longleftrightarrow>
     is_pref_profile A \<and> X \<in># A \<and> Y \<noteq> {} \<and> Y \<subseteq> parties \<and> r (A - {#X#} + {#Y#}) \<succ>[Comm(X)] r A"

text \<open>
  A technical (and fairly obvious) lemma: replacing an voter's approval list with a different 
  approval list again yields a valid preference profile.
\<close>
lemma (in anon_papp) is_pref_profile_replace:
  assumes "is_pref_profile A" and "X \<in># A" and "Y \<noteq> {}" and "Y \<subseteq> parties"
  shows   "is_pref_profile (A - {#X#} + {#Y#})"
proof -
  interpret anon_papp_profile n_voters parties committee_size A
    by fact
  show ?thesis
    using assms A_subset A_nonempty unfolding is_pref_profile_iff
    by (auto dest: in_diffD simp: size_Suc_Diff1)
qed

locale card_stratproof_anon_papp = anon_papp +
  assumes not_manipulable: "\<not>card_manipulable A X Y"
begin

text \<open>
  The two following alternative versions of non-manipulability are somewhat nicer to use
  in practice.
\<close>
lemma not_manipulable':
  assumes "is_pref_profile A" "is_pref_profile A'" "A + {#Y#} = A' + {#X#}"
  shows   "\<not>(r A' \<succ>[Comm(X)] r A)"
proof (cases "X = Y")
  case True
  thus ?thesis
    using assms by (simp add: strongly_preferred_def)
next
  case False
  interpret A: anon_papp_profile n_voters parties committee_size A
    by fact
  interpret A': anon_papp_profile n_voters parties committee_size A'
    by fact
  from assms(3) False have *: "Y \<in># A'" "X \<in># A"
    by (metis add_mset_add_single insert_noteq_member)+

  have "\<not>card_manipulable A X Y"
    by (intro not_manipulable)
  hence "\<not>r (A - {#X#} + {#Y#}) \<succ>[Comm(X)] r A"
    using assms * A.A_subset A'.A_subset A.A_nonempty A'.A_nonempty
    by (auto simp: card_manipulable_def)
  also have "A - {#X#} + {#Y#} = A'"
    using assms(3) False by (metis add_eq_conv_diff add_mset_add_single)
  finally show ?thesis .
qed

lemma not_manipulable'':
  assumes "is_pref_profile A" "is_pref_profile A'" "A + {#Y#} = A' + {#X#}"
  shows   "r A' \<preceq>[Comm(X)] r A"
  using not_manipulable'[OF assms] by simp

end


subsection \<open>Representation\<close>

text \<open>
  \<^emph>\<open>Representation\<close> properties are in a sense the opposite of Efficiency properties: if a
  sufficiently high voters agree that certain parties are good, then these should, to some
  extent, be present in the result. For instance, if we have 20 voters and 5 of them approve
  parties \<open>A\<close> and \<open>B\<close>, then if the output committee has size 4, we would expect either
  \<open>A\<close> or \<open>B\<close> to be in the committee to ensure that these voters' preferences are represented fairly.
  
  Weak representation is a particularly weak variant of this that states that if at least one $k$-th
  of the voters (where $k$ is the size of the output committee) approve only a single
  party \<open>x\<close>, then \<open>x\<close> should be in the committee at least once:
\<close>

locale weak_rep_anon_papp =
  anon_papp n_voters parties committee_size r
  for n_voters and parties :: "'alt set" and committee_size :: nat and r +
  assumes weak_representation:
    "is_pref_profile A \<Longrightarrow> committee_size * count A {x} \<ge> n_voters \<Longrightarrow> x \<in># r A"

text \<open>
  The following alternative definition of Weak Representation is a bit closer to the definition
  given in the paper.
\<close>
lemma weak_rep_anon_papp_altdef:
  "weak_rep_anon_papp n_voters parties committee_size r \<longleftrightarrow>
     anon_papp n_voters parties committee_size r \<and> (committee_size = 0 \<or>
     (\<forall>A x. anon_papp_profile n_voters parties A \<longrightarrow>
              count A {x} \<ge> n_voters / committee_size \<longrightarrow> x \<in># r A))"
  by (cases "committee_size = 0")
     (auto simp: field_simps weak_rep_anon_papp_def
                 weak_rep_anon_papp_axioms_def 
                 anon_papp_def anon_papp_axioms_def anon_papp_election_def
           simp flip: of_nat_mult)


text \<open>
  \<^emph>\<open>Justified Representation\<close> is a stronger notion which demands that if there is a subgroup of
  voters that comprises at least one $k$-th of all voters and for which the intersection of their
  approval lists is some nonempty set \<open>X\<close>, then at least one of the parties approved by at least
  one voter in that subgroup must be in the result committee.
\<close>
locale justified_rep_anon_papp =
  anon_papp n_voters parties committee_size r
  for n_voters and parties :: "'alt set" and committee_size :: nat and r +
  assumes justified_representation:
    "is_pref_profile A \<Longrightarrow> G \<subseteq># A \<Longrightarrow> committee_size * size G \<ge> n_voters \<Longrightarrow>
       (\<Inter>X\<in>set_mset G. X) \<noteq> {} \<Longrightarrow> \<exists>X x. X \<in># G \<and> x \<in> X \<and> x \<in># r A"
begin

text \<open>
  Any rule that satisfies Justified Representation also satisfies Weak Representation
\<close>
sublocale weak_rep_anon_papp
proof
  fix A x
  assume *: "is_pref_profile A" "n_voters \<le> committee_size * count A {x}"
  define G where "G = replicate_mset (count A {x}) {x}"
  have [simp]: "size G = count A {x}"
    by (auto simp: G_def)
  have **: "set_mset G \<subseteq> {{x}}"
    by (auto simp: G_def)
  have ***: "G \<subseteq># A"
    unfolding G_def by (meson count_le_replicate_mset_subset_eq order_refl)
  have "\<exists>X x. X \<in># G \<and> x \<in> X \<and> x \<in># r A"
    by (rule justified_representation) (use * ** *** in auto)
  thus "x \<in># r A"
    using ** by auto
qed

end


locale card_stratproof_weak_rep_anon_papp =
  card_stratproof_anon_papp + weak_rep_anon_papp


subsection \<open>Proportional Representation\<close>

text \<open>
  The notions of Representation we have seen so far are fairly week in that they only demand
  that certain parties be in the committee at least once if enough voters approve them. Notions of
  Proportional Representation strengthen this by demanding that if a sufficiently large subgroup of
  voters approve some parties, then these voters must be represented in the result committe not 
  just once, but to a degree proportional to the size of that subgroup of voters.

  For Weak Representation, the proportional generalization is fairly simple: if a fraction of
  at least $\frac{ln}{k}$ of the voters uniquely approve a party \<open>x\<close>, then \<open>x\<close> must be in the
  committee at least \<open>l\<close> times.
\<close>

locale weak_prop_rep_anon_papp =
  anon_papp n_voters parties committee_size r
  for n_voters and parties :: "'alt set" and committee_size :: nat and r +
  assumes weak_proportional_representation:
    "is_pref_profile A \<Longrightarrow> committee_size * count A {x} \<ge> l * n_voters \<Longrightarrow> count (r A) x \<ge> l"
begin

sublocale weak_rep_anon_papp
proof
  fix A x
  assume "is_pref_profile A" "n_voters \<le> committee_size * count A {x}"
  thus "x \<in># r A"
    using weak_proportional_representation[of A 1] by auto
qed

end


text \<open>
  Similarly, Justified \<^emph>\<open>Proportional\<close> Representation demands that if the approval lists of
  a subgroup of at least $\frac{ln}{k}$ voters have a non-empty intersection, then at least \<open>l\<close>
  parties in the result committee are each approved by at least one of the voters in the subgroup.
\<close>
locale justified_prop_rep_anon_papp =
  anon_papp n_voters parties committee_size r
  for n_voters and parties :: "'alt set" and committee_size :: nat and r +
  assumes justified_proportional_representation:
    "is_pref_profile A \<Longrightarrow> G \<subseteq># A \<Longrightarrow> committee_size * size G \<ge> l * n_voters \<Longrightarrow>
       (\<Inter>X\<in>set_mset G. X) \<noteq> {} \<Longrightarrow> size {# x \<in># r A. x \<in> (\<Union>X\<in>set_mset G. X) #} \<ge> l"
begin

sublocale justified_rep_anon_papp
proof
  fix A G
  assume "is_pref_profile A" "G \<subseteq># A" "n_voters \<le> committee_size * size G" 
         "(\<Inter>X\<in>set_mset G. X) \<noteq> {}"
  hence "size {#x \<in># r A. \<exists>X\<in>#G. x \<in> X#} \<ge> 1"
    using justified_proportional_representation[of A G 1] by auto
  hence "{#x \<in># r A. \<exists>X\<in>#G. x \<in> X#} \<noteq> {#}"
    by auto
  thus "\<exists>X x. X \<in># G \<and> x \<in> X \<and> x \<in># r A"
    by fastforce
qed

sublocale weak_prop_rep_anon_papp
proof
  fix A l x
  assume *: "is_pref_profile A" "l * n_voters \<le> committee_size * count A {x}"
  define G where "G = replicate_mset (count A {x}) {x}"
  from * have "size {#x \<in># r A. x \<in> (\<Union>X\<in>set_mset G. X)#} \<ge> l"
    by (intro justified_proportional_representation)
       (auto simp: G_def simp flip: count_le_replicate_mset_subset_eq)
  also have "size {#x \<in># r A. x \<in> (\<Union>X\<in>set_mset G. X)#} \<le> count (r A) x"
    by (auto simp: G_def)
  finally show "count (r A) x \<ge> l" .
qed

end


locale card_stratproof_weak_prop_rep_anon_papp =
  card_stratproof_anon_papp + weak_prop_rep_anon_papp

end
