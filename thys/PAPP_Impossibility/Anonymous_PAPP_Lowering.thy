(*
  File:     Anonymous_PAPP_Lowering.thy
  Author:   Manuel Eberl, University of Innsbruck 
*)
section \<open>Lowering P-APP Rules to Smaller Settings\<close>
theory Anonymous_PAPP_Lowering
  imports Anonymous_PAPP
begin

text \<open>
  In this section, we prove a number of lemmas (corresponding to Lemma~1 in the paper) that allow
  us to take an anonymous P-APP rule with some additional properties (typically
  Cardinality-Strategyproofness and Weak Representation or Weak Proportional Representation) and 
  construct from it an anonymous P-APP rule for a different setting, i.e.\ different number of
  voters, parties, and/or result committee size.

  In the reverse direction, this also allows us to lift impossibility results from one setting 
  to another.
\<close>

subsection \<open>Preliminary Lemmas\<close>

context card_stratproof_anon_papp
begin

text \<open>
  The following lemma is obtained by applying Strategyproofness repeatedly. It shows that
  if we have \<open>l\<close> voters with identical approval lists, then this entire group of voters has no
  incentive to submit wrong preferences. That is, the outcome they obtain by submitting their 
  genuine approval lists is weakly preferred by them over all outcomes obtained where these \<open>l\<close>
  voters submit any other preferences (and the remaining $n - l$ voters submit the same preferences
  as before).

  This is stronger than regular Strategyproofness, where we only demand that no voter has an
  incentive to submit wrong preferences \<^emph>\<open>unilaterally\<close> (and everyone else keeps the same
  preferences). Here we know that the entire group of \<open>l\<close> voters has no incentive to submit
  wrong preferences in coordination with one another.
\<close>
lemma proposition2:
  assumes "size B = l" "size A + l = n_voters"
  assumes "X \<noteq> {}" "X \<subseteq> parties" "{} \<notin># A+B" "\<forall>X'\<in>#A+B. X' \<subseteq> parties"
  shows   "r (replicate_mset l X + A) \<succeq>[Comm(X)] r (B + A)"
  using assms
proof (induction l arbitrary: A B)
  case 0
  thus ?case
    by simp
next
  case (Suc l A B)
  from Suc.prems have "set_mset B \<noteq> {}"
    by auto
  then obtain Y where Y: "Y \<in># B"
    by blast
  define B' where "B' = B - {#Y#}"
  define A' where "A' = A + {#Y#}"
  have [simp]: "size B' = l"
    using Suc.prems Y by (simp add: B'_def size_Diff_singleton)
  have [simp]: "size A' = n_voters - l"
    using Suc.prems Y by (simp add: A'_def)

  have "r (B' + A') \<preceq>[Comm(X)] r (replicate_mset l X + A')"
    by (rule Suc.IH) (use Suc.prems Y in \<open>auto simp: A'_def B'_def size_Diff_singleton\<close>)
  also have "B' + A' = B + A"
    using Y by (simp add: B'_def A'_def)
  also have "r (replicate_mset l X + A') \<preceq>[Comm(X)] r (replicate_mset (Suc l) X + A)"
  proof (rule not_manipulable'')
    show "replicate_mset (Suc l) X + A + {#Y#} = replicate_mset l X + A' + {#X#}"
      by (simp add: A'_def)
  next
    show "is_pref_profile (replicate_mset (Suc l) X + A)"
     using Suc.prems by unfold_locales (auto split: if_splits)
  next
    show "is_pref_profile (replicate_mset l X + A')"
      using Suc.prems Y by unfold_locales (auto split: if_splits simp: A'_def)
  qed
  finally show ?case .
qed

end


context card_stratproof_weak_rep_anon_papp
begin

text \<open>
  In a setting with Weak Representation and Cardinality-Strategyproofness, Proposition 2 allows
  us to strengthen Weak Representation in the following way: Suppose we at least 
  $l \lfloor n/k\rfloor$ voters with the same approval list \<open>X\<close>, and \<open>X\<close> consists of at least \<open>l\<close>
  parties. Then at least \<open>l\<close> of the members of the result committee are in \<open>X\<close>.
\<close>
lemma proposition3:
  assumes "is_pref_profile A" "X \<subseteq> parties" "card X \<ge> l"
  assumes "committee_size > 0"
  assumes "count A X \<ge> l * \<lceil>n_voters / committee_size\<rceil>"
  shows   "size {# x\<in># r A. x \<in> X #} \<ge> l"
  using assms
proof (induction l arbitrary: A X rule: less_induct)
  case (less l A X)
  interpret A: anon_papp_profile n_voters parties committee_size A
    by fact
  consider "l = 0" | "l = 1" | "l > 1"
    by force
  thus ?case
  proof cases
    assume "l = 0"
    thus ?thesis by simp
  next
    assume [simp]: "l = 1"
    define n where "n = count A X"
    with less.prems have "X \<noteq> {}"
      by auto
    then obtain x where x: "x \<in> X"
      by blast
    have "n \<le> size A"
      unfolding n_def by (rule count_le_size)
    hence "n \<le> n_voters"
      by (simp add: A.size_A)

    have "count A X > 0"
      by (rule Nat.gr0I) (use n_voters_pos less.prems in \<open>auto simp: field_simps\<close>)
    hence "X \<in># A"
      by force
    have [simp]: "replicate_mset n X \<subseteq># A"
      by (simp add: n_def flip: count_le_replicate_mset_subset_eq)

    define A'' where "A'' = A - replicate_mset n X"
    define A' where "A' = A'' + replicate_mset n {x}"
    interpret A': anon_papp_profile n_voters parties committee_size A'
      using A.A_nonempty A.A_subset A.size_A x \<open>X \<in># A\<close>
      by unfold_locales
         (fastforce simp: A'_def A''_def size_Diff_submset subset_mset.add_increasing2 
                    split: if_splits dest!: in_diffD)+

    have "x \<in># r A'"
    proof (rule weak_representation)
      show "is_pref_profile A'"
        by (fact A'.anon_papp_profile_axioms)
    next
      have "n_voters \<le> committee_size * n"
        using less.prems by (simp add: n_def ceiling_le_iff field_simps flip: of_nat_mult)
      also have "n \<le> count A' {x}"
        by (simp add: A'_def)
      finally show "n_voters \<le> committee_size * count A' {x}"
        by simp
    qed
    hence "1 \<le> count (r A') x"
      by simp
    also have "\<dots> = size {# y \<in># r A'. y = x #}"
      by simp
    also have "\<dots> \<le> size {# y \<in># r A'. y \<in> X #}"
      by (intro size_mset_mono multiset_filter_mono') (use x in auto)

    also have "r A' \<preceq>[Comm(X)] r A"
    proof -
      have "r (replicate_mset n {x} + A'') \<preceq>[Comm(X)] r (replicate_mset n X + A'')"
      proof (rule proposition2)
        show "{} \<notin># A'' + replicate_mset n {x}"
          using A'.A_nonempty by (auto simp: A'_def)
        show "\<forall>X'\<in>#A'' + replicate_mset n {x}. X' \<subseteq> parties"
          using A'.A_subset x by (auto simp: A'_def dest: in_diffD)
        show "size A'' + n = n_voters"
          using \<open>n \<le> n_voters\<close> by (auto simp: A''_def size_Diff_submset A.size_A)
      qed (use less.prems in auto)
      also have "replicate_mset n X + A'' = A"
        by (simp add: A''_def n_def flip: count_le_replicate_mset_subset_eq)
      finally show ?thesis
        by (simp add: A'_def add_ac)
    qed
    hence "size {# y \<in># r A'. y \<in> X #} \<le> size {# y \<in># r A. y \<in> X #}"
      by (simp add: committee_preference_def)

    finally show ?thesis
      by simp

  next
    assume l: "l > 1"
    
    define n where "n = count A X"
    have "n \<le> size A"
      unfolding n_def by (rule count_le_size)
    hence "n \<le> n_voters"
      by (simp add: A.size_A)

    define m where "m = nat (ceiling (n_voters / committee_size))"
    have "n_voters / committee_size \<le> m"
      unfolding m_def by linarith
    hence m: "n_voters \<le> committee_size * m"
      using \<open>committee_size > 0\<close> by (simp add: field_simps flip: of_nat_mult)
    have "real n_voters / real committee_size > 0"
      using n_voters_pos less.prems by auto
    hence m': "\<lceil>real n_voters / real committee_size\<rceil> = int m"
      by (simp add: m_def)
    have "1 * m \<le> l * m"
      using l by (intro mult_right_mono) auto
    also have "l * m \<le> n"
      using less.prems by (simp add: m' n_def flip: of_nat_mult)
    finally have "m \<le> n"
      by simp

    with less.prems l have "X \<noteq> {}"
      by auto
    then obtain x where x: "x \<in> X"
      by blast
    have "card (X - {x}) > 0"
      using less.prems x l by simp
    hence "X - {x} \<noteq> {}"
      by force

    have "count A X > 0"
      by (rule Nat.gr0I) (use n_voters_pos less.prems l in \<open>auto simp: field_simps mult_le_0_iff\<close>)
    hence "X \<in># A"
      by force
    have [simp]: "replicate_mset n X \<subseteq># A"
      by (simp add: n_def flip: count_le_replicate_mset_subset_eq)

    define A'' where "A'' = A - replicate_mset n X"
    define A' where "A' = A'' + replicate_mset m {x} + replicate_mset (n - m) (X - {x})"
    interpret A': anon_papp_profile n_voters parties committee_size A'
    proof
      show "Y \<subseteq> parties" if "Y \<in># A'" for Y
        using that A.A_subset x \<open>X \<in># A\<close>
        by (fastforce simp: A'_def A''_def dest!: in_diffD split: if_splits)
    next
      show "{} \<notin># A'"
        using A.A_nonempty x \<open>X \<in># A\<close> \<open>X - {x} \<noteq> {}\<close>
        by (auto simp: A'_def A''_def dest!: in_diffD split: if_splits)
    next
      show "size A' = n_voters"
        using \<open>m \<le> n\<close>
        by (auto simp: A'_def A''_def A.size_A subset_mset.add_increasing2 size_Diff_submset)
    qed

    have "x \<in># r A'"
    proof (rule weak_representation)
      show "is_pref_profile A'"
        by (fact A'.anon_papp_profile_axioms)
    next
      have "n_voters \<le> committee_size * m"
        by (fact m)
      also have "m \<le> count A' {x}"
        by (simp add: A'_def)
      finally show "n_voters \<le> committee_size * count A' {x}"
        by simp
    qed
    hence "1 \<le> count (r A') x"
      by simp
    also have "\<dots> = size {# y \<in># r A'. y = x #}"
      by simp
    finally have 1: "size {#y \<in># r A'. y = x#} \<ge> 1" .

    have 2: "size {# y \<in># r A'. y \<in> X - {x} #} \<ge> l - 1"
    proof (rule less.IH)
      have "int (l - 1) * \<lceil>real n_voters / real committee_size\<rceil> = int ((l - 1) * m)"
        by (auto simp add: m' not_less)
      also have "(l - 1) * m = l * m - m"
        by (simp add: algebra_simps)
      also have "l * m \<le> n"
        using less.prems by (simp add: m' n_def flip: of_nat_mult)
      hence "l * m - m \<le> n - m"
        by (meson diff_le_mono)
      also have "n - m \<le> count A' (X - {x})"
        by (simp add: A'_def A''_def)
      finally show "int (l - 1) * \<lceil>real n_voters / real committee_size\<rceil> \<le> int (count A' (X - {x}))"
        by simp
    qed (use l A'.anon_papp_profile_axioms x less.prems in \<open>auto\<close>)

    have "1 + (l - 1) \<le> size {#y \<in># r A'. y = x#} + size {#y \<in># r A'. y \<in> X - {x}#}"
      by (intro add_mono 1 2)
    also have "\<dots> = size ({#y \<in># r A'. y = x#} + {#y \<in># r A'. y \<in> X - {x}#})"
      by simp
    also have "{#y \<in># r A'. y = x#} + {#y \<in># r A'. y \<in> X - {x}#} =
               {#y \<in># r A'. y = x \<or> y \<in> X - {x}#}"
      by (rule filter_mset_disjunction [symmetric]) auto
    also have "(\<lambda>y. y = x \<or> y \<in> X - {x}) = (\<lambda>y. y \<in> X)"
      using x by auto
    also have "1 + (l - 1) = l"
      using l by simp

    also have "r A' \<preceq>[Comm(X)] r A"
    proof -
      have "r (replicate_mset m {x} + replicate_mset (n - m) (X - {x}) + A'') \<preceq>[Comm(X)] 
            r (replicate_mset n X + A'')"
      proof (rule proposition2)
        show " {} \<notin># A'' + (replicate_mset m {x} + replicate_mset (n - m) (X - {x}))"
          using A'.A_nonempty by (auto simp: A'_def)
        show "\<forall>X'\<in># A'' + (replicate_mset m {x} + replicate_mset (n - m) (X - {x})). X' \<subseteq> parties"
          using A'.A_subset x by (auto simp: A'_def dest: in_diffD)
        show "size A'' + n = n_voters"
          using \<open>n \<le> n_voters\<close> by (auto simp: A''_def size_Diff_submset A.size_A)
      qed (use less.prems l \<open>m \<le> n\<close> in auto)
      also have "replicate_mset n X + A'' = A"
        by (simp add: A''_def n_def flip: count_le_replicate_mset_subset_eq)
      finally show ?thesis
        by (simp add: A'_def add_ac)
    qed
    hence "size {# y \<in># r A'. y \<in> X #} \<le> size {# y \<in># r A. y \<in> X #}"
      by (simp add: committee_preference_def)

    finally show ?thesis
      by simp
  qed
qed

end


subsection \<open>Dividing the number of voters\<close>

text \<open>
  If we have a PAPP rule that satisfies weak representation and cardinality strategyproofness,
  for $ln$ voters, we can turn it into one for \<open>n\<close> voters.
  This is done by simply cloning each voter \<open>l\<close> times.

  Consequently, if we have an impossibility result for $n$ voters, it also holds for any
  integer multiple of \<open>n\<close>.
\<close>
locale divide_voters_card_stratproof_weak_rep_anon_papp =
  card_stratproof_weak_rep_anon_papp "l * n_voters" parties committee_size r
  for l n_voters parties committee_size r
begin

definition lift_profile :: "'a set multiset \<Rightarrow> 'a set multiset" where
  "lift_profile A = (\<Sum>X\<in>#A. replicate_mset l X)"

sublocale lowered: anon_papp_election n_voters parties
  by standard (use n_voters_pos in auto)

lemma l_pos: "l > 0"
  using n_voters_pos by auto

lemma empty_in_lift_profile_iff [simp]: "{} \<in># lift_profile A \<longleftrightarrow> {} \<in># A"
  using l_pos by (auto simp: lift_profile_def)

lemma set_mset_lift_profile [simp]: "set_mset (lift_profile A) = set_mset A"
  using l_pos by (auto simp: lift_profile_def)

lemma size_lift_profile: "size (lift_profile A) = l * size A"
  by (simp add: size_mset_sum_mset lift_profile_def image_mset.compositionality o_def)

lemma count_lift_profile [simp]: "count (lift_profile A) x = l * count A x"
  unfolding lift_profile_def by (induction A) auto

lemma is_pref_profile_lift_profile [intro]:
  assumes "lowered.is_pref_profile A"
  shows   "is_pref_profile (lift_profile A)"
proof -
  interpret anon_papp_profile n_voters parties committee_size A
    by fact
  show ?thesis
    using A_nonempty A_subset size_A
    by unfold_locales
       (auto simp: lift_profile_def size_mset_sum_mset image_mset.compositionality o_def)
qed

sublocale lowered: anon_papp n_voters parties committee_size "r \<circ> lift_profile"
proof
  fix A assume "lowered.is_pref_profile A"
  hence "is_pref_profile (lift_profile A)"
    by blast
  hence "is_committee (r (lift_profile A))"
    using rule_wf by blast
  thus "lowered.is_committee ((r \<circ> lift_profile) A)"
    by simp
qed

sublocale lowered: weak_rep_anon_papp n_voters parties committee_size "r \<circ> lift_profile"
proof
  fix A x
  assume A: "lowered.is_pref_profile A" and x: "n_voters \<le> committee_size * count A {x}"
  from A have A': "is_pref_profile (lift_profile A)"
    by blast
  from x have "l * n_voters \<le> l * (committee_size * count A {x})"
    by (rule mult_left_mono) auto
  also have "\<dots> = committee_size * count (lift_profile A) {x}"
    by simp
  finally have "x \<in># r (lift_profile A)"
    by (intro weak_representation A')
  thus "x \<in># (r \<circ> lift_profile) A"
    by simp
qed

sublocale lowered: card_stratproof_anon_papp n_voters parties committee_size "r \<circ> lift_profile"
proof
  fix A X Y
  show "\<not>lowered.card_manipulable A X Y"
    unfolding lowered.card_manipulable_def
  proof (rule notI, elim conjE)
    assume A: "lowered.is_pref_profile A" and XY: "X \<in># A" "Y \<noteq> {}" "Y \<subseteq> parties"
    assume *: "(r \<circ> lift_profile) A \<prec>[lowered.committee_preference X] 
               (r \<circ> lift_profile) (A - {#X#} + {#Y#})"
    interpret anon_papp_profile n_voters parties committee_size A
      by fact
    have X: "X \<noteq> {}" "X \<subseteq> parties"
      using XY A_nonempty A_subset by auto

    define A' where "A' = A - {#X#}"
    have A': "A = A' + {#X#}"
      using XY by (simp add: A'_def)

    have "r (lift_profile A) \<prec>[committee_preference X]
          r (lift_profile (A - {#X#} + {#Y#}))"
      using * by simp
    also have "r (lift_profile (A - {#X#} + {#Y#})) \<preceq>[committee_preference X]
               r (lift_profile A - {#X#} + {#Y#})"
    proof -
      have "r (replicate_mset (l - 1) Y + (lift_profile A' + {#Y#})) \<preceq>[committee_preference X]
            r (replicate_mset (l - 1) X + (lift_profile A' + {#Y#}))"
      proof (rule proposition2)
        show "size (lift_profile A' + {#Y#}) + (l - 1) = l * n_voters"
          using XY l_pos n_voters_pos
          by (simp add: A'_def size_lift_profile size_Diff_singleton 
                        algebra_simps Suc_diff_le size_A)
      next
        show "{} \<notin># lift_profile A' + {#Y#} + replicate_mset (l - 1) Y"
          using XY A_nonempty by (auto simp: A'_def dest: in_diffD)
      next
        show "\<forall>X'\<in>#lift_profile A' + {#Y#} + replicate_mset (l - 1) Y. X' \<subseteq> parties"
          using XY A_subset by (auto simp: A'_def dest: in_diffD)
      qed (use X in auto)
      thus ?thesis
        by (simp add: A' replicate_mset_rec l_pos lift_profile_def)
    qed
    finally have "card_manipulable (lift_profile A) X Y"
      unfolding card_manipulable_def using XY A by auto
    with not_manipulable show False
      by blast
  qed
qed

sublocale lowered: card_stratproof_weak_rep_anon_papp n_voters parties committee_size "r \<circ> lift_profile"
  ..

end


locale divide_voters_card_stratproof_weak_prop_rep_anon_papp =
  card_stratproof_weak_prop_rep_anon_papp "l * n_voters" parties committee_size r
  for l n_voters parties committee_size r
begin

sublocale divide_voters_card_stratproof_weak_rep_anon_papp ..

sublocale lowered: card_stratproof_weak_prop_rep_anon_papp
  n_voters parties committee_size "r \<circ> lift_profile"
proof
  fix A x l'
  assume A: "lowered.is_pref_profile A" and x: "l' * n_voters \<le> committee_size * count A {x}"
  from A have A': "is_pref_profile (lift_profile A)"
    by blast
  from x have "l * (l' * n_voters) \<le> l * (committee_size * count A {x})"
    by (rule mult_left_mono) auto
  also have "\<dots> = committee_size * count (lift_profile A) {x}"
    by simp
  also have "l * (l' * n_voters) = l' * (l * n_voters)"
    by (simp add: algebra_simps)
  finally have "count (r (lift_profile A)) x \<ge> l'"
    by (intro weak_proportional_representation A')
  thus "count ((r \<circ> lift_profile) A) x \<ge> l'"
    by simp
qed

end



subsection \<open>Decreasing the number of parties\<close>

text \<open>
  If we have a PAPP rule that satisfies weak representation and cardinality strategyproofness,
  for $m$ parties, we can turn it into one for $m-1$ parties. This is done by simply
  duplicating one particular party (say \<open>x\<close>) in the preference profile, i.e.\ whenever
  \<open>x\<close> is part of an approval list, we add a clone of \<open>x\<close> (say \<open>y\<close>) as well. Should \<open>y\<close> then end up
  in the committee, we simply replace it with \<open>x\<close>.

  Consequently, if we have an impossibility result for $k$ parties, it also holds for
  $\geq m$ parties.
\<close>
locale remove_alt_card_stratproof_weak_rep_anon_papp =
  card_stratproof_weak_rep_anon_papp n_voters parties committee_size r
  for n_voters and parties :: "'a set" and committee_size r +
  fixes x y :: 'a
  assumes xy: "x \<in> parties" "y \<in> parties" "x \<noteq> y"
begin

definition lift_applist :: "'a set \<Rightarrow> 'a set" where
  "lift_applist X = (if x \<in> X then insert y X else X)"

definition lift_profile :: "'a set multiset \<Rightarrow> 'a set multiset" where
  "lift_profile A = image_mset lift_applist A"

definition lower_result where "lower_result C = image_mset (\<lambda>z. if z = y then x else z) C"

definition lowered where "lowered = lower_result \<circ> r \<circ> lift_profile"


lemma lift_profile_empty [simp]: "lift_profile {#} = {#}"
  by (simp add: lift_profile_def)

lemma lift_profile_add_mset [simp]:
  "lift_profile (add_mset X A) = add_mset (lift_applist X) (lift_profile A)"
  by (simp add: lift_profile_def)

lemma empty_in_lift_profile_iff [simp]: "{} \<in># lift_profile A \<longleftrightarrow> {} \<in># A"
  by (auto simp: lift_applist_def lift_profile_def)

lemma size_lift_profile [simp]: "size (lift_profile A) = size A"
  by (simp add: lift_profile_def)

lemma lift_applist_eq_self_iff [simp]: "lift_applist X = X \<longleftrightarrow> x \<notin> X \<or> y \<in> X"
  by (auto simp: lift_applist_def)

lemma lift_applist_eq_self_iff' [simp]: "lift_applist (X - {y}) = X \<longleftrightarrow> (x \<in> X \<longleftrightarrow> y \<in> X)"
  by (cases "y \<in> X") (auto simp: lift_applist_def xy)

lemma in_lift_applist_iff: "z \<in> lift_applist X \<longleftrightarrow> z \<in> X \<or> (z = y \<and> x \<in> X)"
  by (auto simp: lift_applist_def)

lemma count_lift_profile:
  assumes "\<forall>Y\<in>#A. y \<notin> Y"
  shows   "count (lift_profile A) X = (if x \<in> X \<longleftrightarrow> y \<in> X then count A (X - {y}) else 0)"
  using assms xy by (induction A) (auto simp: lift_applist_def)

lemma y_notin_lower_result [simp]: "y \<notin># lower_result C"
  using xy by (auto simp: lower_result_def)

lemma lower_result_subset: "set_mset (lower_result C) \<subseteq> insert x (set_mset C - {y})"
  using xy by (auto simp: lower_result_def)

lemma lower_result_subset': "set_mset C \<subseteq> parties \<Longrightarrow> set_mset (lower_result C) \<subseteq> parties"
  using xy by (auto simp: lower_result_def)

lemma size_lower_result [simp]: "size (lower_result C) = size C"
  by (simp add: lower_result_def)

lemma count_lower_result:
  "count (lower_result C) z =
     (if z = y then 0
      else if z = x then count C x + count C y
      else count C z)"
  using xy by (induction C) (auto simp: lower_result_def)

lemma in_lower_result_iff:
  "z \<in># lower_result C \<longleftrightarrow> z \<noteq> y \<and> (z \<in># C \<or> (z = x \<and> y \<in># C))"
  unfolding lower_result_def using xy by (induction C) auto


sublocale lowered: anon_papp_election n_voters "parties - {y}"
  by standard (use n_voters_pos xy in auto)

lemma is_pref_profile_lift_profile [intro]:
  assumes "lowered.is_pref_profile A"
  shows   "is_pref_profile (lift_profile A)"
proof -
  interpret anon_papp_profile n_voters "parties - {y}" committee_size A
    by fact
  show ?thesis
    using A_nonempty A_subset size_A
    by unfold_locales
       (auto simp: lift_profile_def lift_applist_def xy 
                   size_mset_sum_mset image_mset.compositionality o_def)
qed

sublocale lowered: anon_papp n_voters "parties - {y}" committee_size lowered
proof
  fix A assume "lowered.is_pref_profile A"
  hence "is_pref_profile (lift_profile A)"
    by blast
  hence "is_committee (r (lift_profile A))"
    using rule_wf by blast
  thus "lowered.is_committee (lowered A)"
    unfolding lowered.is_committee_def is_committee_def lowered_def
    using lower_result_subset'[of "r (lift_profile A)"] by auto
qed

sublocale lowered: weak_rep_anon_papp n_voters "parties - {y}" committee_size lowered
proof
  fix A z
  assume A: "lowered.is_pref_profile A" and z: "n_voters \<le> committee_size * count A {z}"
  interpret A: anon_papp_profile n_voters "parties - {y}" committee_size A
    by fact
  have "committee_size > 0"
    using z n_voters_pos by (intro Nat.gr0I) auto

  from A have A': "is_pref_profile (lift_profile A)"
    by blast
  have "count A {z} > 0"
    using z n_voters_pos by (intro Nat.gr0I) auto
  hence "{z} \<in># A"
    by simp
  hence z': "z \<in> parties - {y}"
    using A.A_subset z by auto

  define C where "C = r (lift_profile A)"

  show "z \<in># lowered A"
  proof (cases "z = x")
    case False
    have "n_voters \<le> committee_size * count A {z}"
      by fact
    also have "count A {z} \<le> count (lift_profile A) {z}"
      using A.A_subset z' False by (subst count_lift_profile) auto
    hence "committee_size * count A {z} \<le> committee_size * count (lift_profile A) {z}"
      by (intro mult_left_mono) auto
    finally have "z \<in># r (lift_profile A)"
      by (intro weak_representation A')
    thus "z \<in># lowered A"
      using False z' by (simp add: lowered_def in_lower_result_iff)
  next
    case [simp]: True
    have "1 \<le> size {#z \<in># C. z \<in> {x, y}#}"
      unfolding C_def
    proof (rule proposition3)
      have [simp]: "{x, y} - {y} = {x}"
        using xy by auto
      hence "n_voters \<le> committee_size * count (lift_profile A) {x, y}"
        using xy A.A_subset z by (subst count_lift_profile) auto
      thus "int 1 * \<lceil>real n_voters / real committee_size\<rceil> \<le> int (count (lift_profile A) {x, y})"
        using \<open>committee_size > 0\<close>
        by (auto simp: ceiling_le_iff field_simps simp flip: of_nat_mult)
    qed (use A' xy \<open>committee_size > 0\<close> in auto)
    also have "\<dots> = count C x + count C y"
      using xy by (induction C) auto
    also have "\<dots> = count (lowered A) x"
      using xy by (simp add: lowered_def count_lower_result C_def)
    finally show "z \<in># lowered A"
      by simp
  qed
qed

lemma filter_lower_result_eq:
  "y \<notin> X \<Longrightarrow> {#x \<in># lower_result C. x \<in> X#} = lower_result {#x \<in># C. x \<in> lift_applist X#}"
  by (induction C) (auto simp: lower_result_def lift_applist_def)

sublocale lowered: card_stratproof_anon_papp n_voters "parties - {y}" committee_size lowered
proof
  fix A X Y
  show "\<not>lowered.card_manipulable A X Y"
    unfolding lowered.card_manipulable_def
  proof (rule notI, elim conjE)
    assume A: "lowered.is_pref_profile A" and XY: "X \<in># A" "Y \<noteq> {}" "Y \<subseteq> parties - {y}"
    assume *: "lowered A \<prec>[lowered.committee_preference X] lowered (A - {#X#} + {#Y#})"
    interpret anon_papp_profile n_voters "parties - {y}" committee_size A
      by fact
    have X: "X \<noteq> {}" "X \<subseteq> parties - {y}"
      using XY A_nonempty A_subset by auto
    define A' where "A' = A - {#X#}"
    have A': "A = A' + {#X#}"
      using XY by (simp add: A'_def)

    from * have "size {#x \<in># lower_result (r (lift_profile A' + {#lift_applist X#})). x \<in> X#} <
                 size {#x \<in># lower_result (r (lift_profile A' + {#lift_applist Y#})). x \<in> X#}"
      by (simp add: lowered_def A' lowered.strong_committee_preference_iff)
    also have "{#x \<in># lower_result (r (lift_profile A' + {#lift_applist X#})). x \<in> X#} =
               lower_result {#x \<in># r (lift_profile A' + {#lift_applist X#}). x \<in> lift_applist X#}"
      using X by (subst filter_lower_result_eq) auto
    also have "{#x \<in># lower_result (r (lift_profile A' + {#lift_applist Y#})). x \<in> X#} =
               lower_result {#x \<in># r (lift_profile A' + {#lift_applist Y#}). x \<in> lift_applist X#}"
      using X by (subst filter_lower_result_eq) auto
    finally have "size {#x \<in># r (lift_profile A' + {#lift_applist X#}). x \<in> lift_applist X#} <
                  size {#x \<in># r (lift_profile A' + {#lift_applist Y#}). x \<in> lift_applist X#}"
      by simp
    hence "r (lift_profile A' + {#lift_applist X#}) \<prec>[committee_preference (lift_applist X)]
           r (lift_profile A' + {#lift_applist Y#})"
      by (simp add: strong_committee_preference_iff)
    moreover have "\<not>r (lift_profile A' + {#lift_applist X#}) \<prec>[committee_preference (lift_applist X)]
                    r (lift_profile A' + {#lift_applist Y#})"
    proof (rule not_manipulable' [where Y = "lift_applist Y"])
      have "is_pref_profile (lift_profile A)"
        using A by blast
      thus "is_pref_profile (lift_profile A' + {#lift_applist X#})"
        using A by (simp add: A')
    next
      have "is_pref_profile (lift_profile (A - {#X#} + {#Y#}))"
        using A  XY lowered.is_pref_profile_replace by blast
      thus "is_pref_profile (lift_profile A' + {#lift_applist Y#})"
        by (simp add: A')
    qed auto
    ultimately show False
      by contradiction
  qed
qed

sublocale lowered: card_stratproof_weak_rep_anon_papp n_voters "parties - {y}" committee_size lowered
  ..

end


text \<open>
  The following lemma is now simply an iterated application of the above. This allows us to
  restrict a P-APP rule to any non-empty subset of parties.
\<close>
lemma card_stratproof_weak_rep_anon_papp_restrict_parties:
  assumes "card_stratproof_weak_rep_anon_papp n parties k r" "parties' \<subseteq> parties" "parties' \<noteq> {}"
  shows   "\<exists>r. card_stratproof_weak_rep_anon_papp n parties' k r"
proof -
  have "finite parties"
  proof -
    interpret card_stratproof_weak_rep_anon_papp n parties k r
      by fact
    show ?thesis
      by (rule finite_parties)
  qed
  thus ?thesis
    using assms
  proof (induction parties arbitrary: r rule: finite_psubset_induct)
    case (psubset parties r)
    show ?thesis
    proof (cases "parties = parties'")
      case True
      thus ?thesis
        using psubset.prems by auto
    next
      case False
      obtain x where x: "x \<in> parties'"
        using psubset.prems by blast
      from False and psubset.prems have "parties - parties' \<noteq> {}"
        by auto
      then obtain y where y: "y \<in> parties - parties'"
        by blast

      interpret card_stratproof_weak_rep_anon_papp n parties k r
        by fact
      interpret remove_alt_card_stratproof_weak_rep_anon_papp n parties k r x y
        by standard (use x y psubset.prems in auto)
      show ?thesis
      proof (rule psubset.IH)
        show "parties - {y} \<subset> parties" and "parties' \<subseteq> parties - {y}" "parties' \<noteq> {}"
          using x y psubset.prems by auto
      next
        show "card_stratproof_weak_rep_anon_papp n (parties - {y}) k lowered"
          using lowered.card_stratproof_weak_rep_anon_papp_axioms .
      qed
    qed
  qed
qed



subsection \<open>Decreasing the committee size\<close>

text \<open>
  If we have a PAPP rule that satisfies weak representation and cardinality strategyproofness,
  for $l(k+1)$ voters, $m+1$ parties, and a committee size of $k+1$, we can turn it into
  one for $lk$ voters, $m$ parties, and a committee size of $k$.

  This is done by again cloning a party \<open>x\<close> into a new party \<open>y\<close> and additionally
  adding \<open>l\<close> new voters whose preferences are \<open>{x, y}\<close>. We again replace any \<open>y\<close> occuring in the
  output committee with \<open>x\<close>. Weak representation then ensures that \<open>x\<close> occurs in the output
  at least once, and we then simply remove one \<open>x\<close> from the committee to obtain an output
  committee of size \<open>k - 1\<close>.

  Consequently, if we have an impossibility result for a committee size of $m$, we can
  extend it to a larger committee size, but at the cost of introducing a new party
  and new voters, and with a restriction on the number of voters.
\<close>
(* n / k = l *)
locale decrease_committee_card_stratproof_weak_rep_anon_papp =
  card_stratproof_weak_rep_anon_papp "l * (k + 1)" "insert y parties" "k + 1" r
  for l k y and parties :: "'a set" and r +
  fixes x :: 'a
  assumes xy: "x \<in> parties" "y \<notin> parties"
  assumes k: "k > 0"
begin

definition lift_applist :: "'a set \<Rightarrow> 'a set" where
  "lift_applist X = (if x \<in> X then insert y X else X)"

definition lift_profile :: "'a set multiset \<Rightarrow> 'a set multiset" where
  "lift_profile A = image_mset lift_applist A + replicate_mset l {x, y}"

definition lower_result
  where "lower_result C = image_mset (\<lambda>z. if z = y then x else z) C - {#x#}"

definition lowered where "lowered = lower_result \<circ> r \<circ> lift_profile"


lemma l: "l > 0"
  using n_voters_pos by auto

lemma x_neq_y [simp]: "x \<noteq> y" "y \<noteq> x"
  using xy by auto

lemma lift_profile_empty [simp]: "lift_profile {#} = replicate_mset l {x, y}"
  by (simp add: lift_profile_def)

lemma lift_profile_add_mset [simp]:
  "lift_profile (add_mset X A) = add_mset (lift_applist X) (lift_profile A)"
  by (simp add: lift_profile_def)

lemma empty_in_lift_profile_iff [simp]: "{} \<in># lift_profile A \<longleftrightarrow> {} \<in># A"
  by (auto simp: lift_applist_def lift_profile_def)

lemma size_lift_profile [simp]: "size (lift_profile A) = size A + l"
  by (simp add: lift_profile_def)

lemma lift_applist_eq_self_iff [simp]: "lift_applist X = X \<longleftrightarrow> x \<notin> X \<or> y \<in> X"
  by (auto simp: lift_applist_def)

lemma lift_applist_eq_self_iff' [simp]: "lift_applist (X - {y}) = X \<longleftrightarrow> (x \<in> X \<longleftrightarrow> y \<in> X)"
  by (cases "y \<in> X") (auto simp: lift_applist_def xy)

lemma in_lift_applist_iff: "z \<in> lift_applist X \<longleftrightarrow> z \<in> X \<or> (z = y \<and> x \<in> X)"
  by (auto simp: lift_applist_def)

lemma count_lift_profile:
  assumes "\<forall>Y\<in>#A. y \<notin> Y"
  shows   "count (lift_profile A) X =
             (if x \<in> X \<longleftrightarrow> y \<in> X then count A (X - {y}) else 0) +
             (if X = {x, y} then l else 0)"
  using assms xy by (induction A) (auto simp: lift_applist_def)



lemma y_notin_lower_result [simp]: "y \<notin># lower_result C"
  using xy by (auto simp: lower_result_def dest: in_diffD)

lemma lower_result_subset: "set_mset (lower_result C) \<subseteq> insert x (set_mset C - {y})"
  using xy by (auto simp: lower_result_def dest: in_diffD)

lemma lower_result_subset': "set_mset C \<subseteq> insert y parties \<Longrightarrow> set_mset (lower_result C) \<subseteq> parties"
  by (rule order.trans[OF lower_result_subset]) (use xy in auto)

lemma size_lower_result [simp]:
  assumes "x \<in># C \<or> y \<in># C"
  shows   "size (lower_result C) = size C - 1"
  using assms by (auto simp: lower_result_def size_Diff_singleton)

lemma size_lower_result': "size (lower_result C) = size C - (if x \<in># C \<or> y \<in># C then 1 else 0)"
proof -
  define f where "f = (\<lambda>C. image_mset (\<lambda>z. if z = y then x else z) C)"
  have "size (lower_result C) = size (f C - {#x#})"
    by (simp add: lower_result_def f_def)
  also have "\<dots> = size (f C) - (if x \<in># f C then 1 else 0)"
    by (simp add: diff_single_trivial size_Diff_singleton)
  finally show ?thesis
    by (auto simp: f_def)
qed

lemma count_lower_result:
  "count (lower_result C) z =
     (if z = y then 0
      else if z = x then count C x + count C y - 1
      else count C z)" (is "_ = ?rhs")
proof -
  define f where "f = (\<lambda>C. image_mset (\<lambda>z. if z = y then x else z) C)"
  have "count (lower_result C) z = count (f C - {#x#}) z"
    by (simp add: lower_result_def f_def)
  also have "\<dots> = count (f C) z - (if z = x then 1 else 0)"
    by auto
  also have "count (f C) z = (if z = y then 0 else if z = x then count C x + count C y else count C z)"
    using xy by (induction C)  (auto simp: f_def)
  also have "\<dots> - (if z = x then 1 else 0) = ?rhs"
    by auto
  finally show ?thesis .
qed

lemma in_lower_resultD:
  "z \<in># lower_result C \<Longrightarrow> z = x \<or> z \<in># C"
  using xy by (auto simp: lower_result_def dest!: in_diffD)

lemma in_lower_result_iff:
  "z \<in># lower_result C \<longleftrightarrow> z \<noteq> y \<and> (if z = x then count C x + count C y > 1 else z \<in># C)"
  (is "_ = ?rhs")
proof -
  have "z \<in># lower_result C \<longleftrightarrow> count (lower_result C) z > 0"
    by auto
  also have "\<dots> \<longleftrightarrow> ?rhs"
    by (subst count_lower_result) auto
  finally show ?thesis .
qed

lemma filter_lower_result_eq:
  assumes "y \<notin> X"
  shows   "{#z \<in># lower_result C. z \<in> X#} = lower_result {#z \<in># C. z \<in> lift_applist X#}"
proof -
  define f where "f = (\<lambda>C. {#if z = y then x else z. z \<in># C#})"
  have "lower_result {#z \<in># C. z \<in> lift_applist X#} = f {#z \<in># C. z \<in> lift_applist X#} - {#x#}"
    by (simp add: f_def lower_result_def)
  also have "f {#z \<in># C. z \<in> lift_applist X#} = {#z \<in># f C. z \<in> X#}"
    using assms by (induction C) (auto simp: f_def lift_applist_def)
  also have "\<dots> - {#x#} = {#z \<in># f C - {#x#}. z \<in> X#}"
    by (subst filter_diff_mset') auto
  also have "f C - {#x#} = lower_result C"
    by (simp add: f_def lower_result_def)
  finally show ?thesis ..
qed


sublocale lowered: anon_papp_election "l * k" parties k
  by standard (use n_voters_pos xy finite_parties k in auto)

lemma is_pref_profile_lift_profile [intro]:
  assumes "lowered.is_pref_profile A"
  shows   "is_pref_profile (lift_profile A)"
proof -
  interpret A: anon_papp_profile "l * k" parties k A
    by fact
  show ?thesis
    using A.A_nonempty A.A_subset A.size_A l
    by unfold_locales
       (auto simp: lift_profile_def lift_applist_def xy 
                   size_mset_sum_mset image_mset.compositionality o_def)
qed

lemma is_committee_lower_result:
  assumes "is_committee C" "x \<in># C \<or> y \<in># C"
  shows   "lowered.is_committee (lower_result C)"
  using assms unfolding is_committee_def lowered.is_committee_def
  using lower_result_subset'[of C] by auto

lemma x_or_y_in_r_lift_profile:
  assumes "lowered.is_pref_profile A"
  shows   "x \<in># r (lift_profile A) \<or> y \<in># r (lift_profile A)"
proof -
  interpret A: anon_papp_profile "l * k" parties k A
    by fact
  have "size {#z \<in># r (lift_profile A). z \<in> {x, y}#} \<ge> 1"
  proof (rule proposition3)
    have "real (l * (k + 1)) / real (k + 1) = real l"
      by (simp add: field_simps)
    also have "int 1 * \<lceil>\<dots>\<rceil> = int l"
      by simp
    also have "l \<le> count (lift_profile A) {x, y}"
      using xy A.A_subset by (subst count_lift_profile) auto
    finally show "int 1 * \<lceil>real (l * (k + 1)) / real (k + 1)\<rceil> \<le> int (count (lift_profile A) {x, y})"
      by simp
  next
    show "is_pref_profile (lift_profile A)"
      by (intro is_pref_profile_lift_profile) fact
  qed (use xy in auto)
  hence "{#z \<in># r (lift_profile A). z \<in> {x, y}#} \<noteq> {#}"
    by force
  thus ?thesis
    by auto
qed

sublocale lowered: anon_papp "l * k" parties k lowered
proof
  fix A assume A: "lowered.is_pref_profile A"
  hence "is_pref_profile (lift_profile A)"
    by blast
  hence "is_committee (r (lift_profile A))"
    using rule_wf by blast
  thus "lowered.is_committee (lowered A)"
    unfolding lowered_def o_def using x_or_y_in_r_lift_profile[of A] A
    by (intro is_committee_lower_result) auto
qed

sublocale lowered: weak_rep_anon_papp "l * k" parties k lowered
proof
  fix A z
  assume A: "lowered.is_pref_profile A" and z: "l * k \<le> k * count A {z}"
  interpret A: anon_papp_profile "l * k" "parties" k A
    by fact

  from A have A': "is_pref_profile (lift_profile A)"
    by blast
  have "count A {z} > 0"
    using z k n_voters_pos by (intro Nat.gr0I) auto
  hence "{z} \<in># A"
    by simp
  hence z': "z \<in> parties"
    using A.A_subset z by auto
  hence [simp]: "y \<noteq> z" "z \<noteq> y"
    using xy by auto

  define C where "C = r (lift_profile A)"

  show "z \<in># lowered A"
  proof (cases "z = x")
    case False
    have "l \<le> count A {z}"
      using z k by (simp add: algebra_simps)
    hence "l * (k + 1) \<le> (k + 1) * count A {z}"
      by (subst mult.commute, intro mult_right_mono) auto
    also have "count A {z} = count (lift_profile A) {z}"
      using False A.A_subset xy by (subst count_lift_profile) auto
    finally have "z \<in># r (lift_profile A)"
      by (intro weak_representation A')
    thus "z \<in># lowered A"
      using False by (auto simp: lowered_def in_lower_result_iff)
  next
    case [simp]: True
    from xy have [simp]: "{x, y} - {y} = {x}"
      by auto

    have "size {#z \<in># C. z \<in> {x, y}#} \<ge> 2"
      unfolding C_def
    proof (rule proposition3)
      have "real (l * (k + 1)) / real (k + 1) = l"
        unfolding of_nat_mult using k by (simp add: divide_simps)
      also have "int 2 * \<lceil>\<dots>\<rceil> = int (2 * l)"
        by simp
      also have "\<dots> \<le> count (lift_profile A) {x, y}"
        using z k xy A.A_subset by (subst count_lift_profile) auto
      finally show "int 2 * \<lceil>real (l * (k + 1)) / real (k + 1)\<rceil> \<le> \<dots>" .
    qed (use A' xy in auto)
    also have "size {#z \<in># C. z \<in> {x, y}#} = count C x + count C y"
      by (induction C) auto
    finally have "x \<in># lower_result C"
      by (subst in_lower_result_iff) auto
    thus "z \<in># lowered A"
      by (simp add: lowered_def C_def)
  qed
qed

sublocale lowered: card_stratproof_anon_papp "l * k" parties k lowered
proof
  fix A X Y
  show "\<not>lowered.card_manipulable A X Y"
    unfolding lowered.card_manipulable_def
  proof (rule notI, elim conjE)
    assume A: "lowered.is_pref_profile A" and XY: "X \<in># A" "Y \<noteq> {}" "Y \<subseteq> parties"
    assume *: "lowered A \<prec>[lowered.committee_preference X] lowered (A - {#X#} + {#Y#})"
    interpret anon_papp_profile "l * k" "parties" k A
      by fact
    have X: "X \<noteq> {}" "X \<subseteq> parties"
      using XY A_nonempty A_subset by auto
    define A' where "A' = A - {#X#}"
    have A': "A = A' + {#X#}"
      using XY by (simp add: A'_def)
    from xy X XY have [simp]: "y \<notin> X" "y \<notin> Y"
      by auto

    define Al1 where "Al1 = lift_profile A"
    define Al2 where "Al2 = lift_profile (A' + {#Y#})"
    have A'_plus_Y: "lowered.is_pref_profile (A' + {#Y#})"
      unfolding A'_def using A XY lowered.is_pref_profile_replace by blast
    have Al1: "is_pref_profile Al1"
      unfolding Al1_def using A by blast
    have Al2: "is_pref_profile Al2"
      unfolding Al2_def unfolding A'_def using A XY lowered.is_pref_profile_replace by blast

    have size_aux: "size (lower_result {#x \<in># r (lift_profile A). x \<in> lift_applist X#}) =
                    size {#x \<in># r (lift_profile A). x \<in> lift_applist X#} - (if x \<in> X then 1 else 0)"
      if A: "lowered.is_pref_profile A" for A
      using x_or_y_in_r_lift_profile[OF A] 
      by (subst size_lower_result') (auto simp: lift_applist_def)

    from * have "size {#x \<in># lower_result (r Al1). x \<in> X#} <
                 size {#x \<in># lower_result (r Al2). x \<in> X#}"
      by (simp add: Al1_def Al2_def lowered_def A' lowered.strong_committee_preference_iff)
    also have "{#x \<in># lower_result (r Al1). x \<in> X#} = lower_result {#x \<in># r Al1. x \<in> lift_applist X#}"
      using X xy by (subst filter_lower_result_eq) auto
    also have "{#x \<in># lower_result (r Al2). x \<in> X#} = lower_result {#x \<in># r Al2. x \<in> lift_applist X#}"
      using X xy by (subst filter_lower_result_eq) auto
    also have "size (lower_result {#x \<in># r Al1. x \<in> lift_applist X#}) =
               size {#x \<in># r Al1. x \<in> lift_applist X#} - (if x \<in> X then 1 else 0)"
      unfolding Al1_def by (rule size_aux) fact
    also have "size (lower_result {#x \<in># r Al2. x \<in> lift_applist X#}) =
               size {#x \<in># r Al2. x \<in> lift_applist X#} - (if x \<in> X then 1 else 0)"
      unfolding Al2_def by (rule size_aux) fact
    finally have "size {#x \<in># r Al1. x \<in> lift_applist X#} < size {#x \<in># r Al2. x \<in> lift_applist X#}"
      by auto
    hence "r Al1 \<prec>[committee_preference (lift_applist X)] r Al2"
      by (simp add: strong_committee_preference_iff)

    moreover have "\<not>r Al1 \<prec>[committee_preference (lift_applist X)] r Al2"
      by (rule not_manipulable' [where Y = "lift_applist Y"])
         (use Al1 Al2 in \<open>auto simp: Al1_def Al2_def A'\<close>)

    ultimately show False
      by contradiction
  qed
qed

sublocale lowered: card_stratproof_weak_rep_anon_papp "l * k" parties k lowered
  ..

end


text \<open>
  For Weak \<^emph>\<open>Proportional\<close> Representation, the lowering argument to decrease the committee size
  is somewhat easier since it does not involve adding a new party; instead, we simply
  add \<open>l\<close> new voters whose preferences are \<open>{x}\<close>.
\<close>
locale decrease_committee_card_stratproof_weak_prop_rep_anon_papp =
  card_stratproof_weak_prop_rep_anon_papp "l * (k + 1)" parties "k + 1" r
  for l k and parties :: "'a set" and r +
  fixes x :: 'a
  assumes x: "x \<in> parties"
  assumes k: "k > 0"
begin

definition lift_profile :: "'a set multiset \<Rightarrow> 'a set multiset" where
  "lift_profile A = A + replicate_mset l {x}"

definition lower_result
  where "lower_result C = C - {#x#}"

definition lowered where "lowered = lower_result \<circ> r \<circ> lift_profile"


lemma l: "l > 0"
  using n_voters_pos by auto

lemma lift_profile_empty [simp]: "lift_profile {#} = replicate_mset l {x}"
  by (simp add: lift_profile_def)

lemma lift_profile_add_mset [simp]:
  "lift_profile (add_mset X A) = add_mset X (lift_profile A)"
  by (simp add: lift_profile_def)

lemma empty_in_lift_profile_iff [simp]: "{} \<in># lift_profile A \<longleftrightarrow> {} \<in># A"
  by (auto simp: lift_profile_def)

lemma size_lift_profile [simp]: "size (lift_profile A) = size A + l"
  by (simp add: lift_profile_def)

lemma count_lift_profile:
  "count (lift_profile A) X = count A X + (if X = {x} then l else 0)"
  by (auto simp: lift_profile_def)


lemma size_lower_result [simp]:
  assumes "x \<in># C"
  shows   "size (lower_result C) = size C - 1"
  using assms by (auto simp: lower_result_def size_Diff_singleton)

lemma size_lower_result': "size (lower_result C) = size C - (if x \<in># C then 1 else 0)"
  by (induction C) (auto simp: lower_result_def size_Diff_singleton)

lemma count_lower_result:
  "count (lower_result C) z = count C z - (if z = x then 1 else 0)"
  by (auto simp: lower_result_def)

lemma in_lower_resultD:
  "z \<in># lower_result C \<Longrightarrow> z \<in># C"
  by (auto simp: lower_result_def dest!: in_diffD)

lemma in_lower_result_iff:
  "z \<in># lower_result C \<longleftrightarrow> (if z = x then count C x > 1 else z \<in># C)"
  (is "_ = ?rhs")
proof -
  have "z \<in># lower_result C \<longleftrightarrow> count (lower_result C) z > 0"
    by auto
  also have "\<dots> \<longleftrightarrow> ?rhs"
    by (subst count_lower_result) auto
  finally show ?thesis .
qed


sublocale lowered: anon_papp_election "l * k" parties k
  by standard (use n_voters_pos finite_parties k in auto)

lemma is_pref_profile_lift_profile [intro]:
  assumes "lowered.is_pref_profile A"
  shows   "is_pref_profile (lift_profile A)"
proof -
  interpret A: anon_papp_profile "l * k" parties k A
    by fact
  show ?thesis
    using A.A_nonempty A.A_subset A.size_A l
    by unfold_locales
       (auto simp: lift_profile_def x size_mset_sum_mset image_mset.compositionality o_def)
qed

lemma is_committee_lower_result:
  assumes "is_committee C" "x \<in># C"
  shows   "lowered.is_committee (lower_result C)"
  using assms unfolding is_committee_def lowered.is_committee_def
  by (auto simp: lower_result_def size_Diff_singleton dest: in_diffD)

lemma x_in_r_lift_profile:
  assumes "lowered.is_pref_profile A"
  shows   "x \<in># r (lift_profile A)"
proof (rule weak_representation)
  show "is_pref_profile (lift_profile A)"
    using assms by blast
next
  have "(k + 1) * l \<le> (k + 1) * count (lift_profile A) {x}"
    by (intro mult_left_mono) (auto simp: count_lift_profile)
  thus "l * (k + 1) \<le> (k + 1) * count (lift_profile A) {x}"
    by (simp add: algebra_simps)
qed

sublocale lowered: anon_papp "l * k" parties k lowered
proof
  fix A assume A: "lowered.is_pref_profile A"
  hence "is_pref_profile (lift_profile A)"
    by blast
  hence "is_committee (r (lift_profile A))"
    using rule_wf by blast
  thus "lowered.is_committee (lowered A)"
    unfolding lowered_def o_def using x_in_r_lift_profile[of A] A
    by (intro is_committee_lower_result) auto
qed

sublocale lowered: weak_prop_rep_anon_papp "l * k" parties k lowered
proof
  fix A z l'
  assume A: "lowered.is_pref_profile A" and z: "l' * (l * k) \<le> k * count A {z}"
  interpret A: anon_papp_profile "l * k" "parties" k A
    by fact

  show "count (lowered A) z \<ge> l'"
  proof (cases "l' > 0")
    case False
    thus ?thesis by auto
  next
    case l: True

    from A have A': "is_pref_profile (lift_profile A)"
      by blast
    have "count A {z} > 0"
      using z k n_voters_pos l by (intro Nat.gr0I) auto
    hence "{z} \<in># A"
      by simp
    hence z': "z \<in> parties"
      using A.A_subset z by auto
  
    define C where "C = r (lift_profile A)"
  
    show "count (lowered A) z \<ge> l'"
    proof (cases "z = x")
      case False
      have "l' * l \<le> count A {z}"
        using z k by (simp add: algebra_simps)
      hence "l' * l * (k + 1) \<le> (k + 1) * count A {z}"
        by (subst mult.commute, intro mult_right_mono) auto
      also have "count A {z} = count (lift_profile A) {z}"
        using False A.A_subset by (subst count_lift_profile) auto
      finally have "count (r (lift_profile A)) z \<ge> l'"
        by (intro weak_proportional_representation A') (auto simp: algebra_simps)
      thus "l' \<le> count (lowered A) z"
        using False by (simp add: lowered_def lower_result_def)
    next
      case [simp]: True
      have "l' * l \<le> count A {x}"
        using z k by (simp add: algebra_simps)
      hence "l' * l * (k + 1) \<le> (k + 1) * count A {x}"
        by (subst mult.commute, intro mult_right_mono) auto
      also have "\<dots> + (k + 1) * l = (k + 1) * count (lift_profile A) {x}"
        by (simp add: count_lift_profile algebra_simps)
      finally have "(l' + 1) * (l * (k + 1)) \<le> (k + 1) * count (lift_profile A) {x}"
        by (simp add: algebra_simps)
      hence "count (r (lift_profile A)) x \<ge> l' + 1"
        by (intro weak_proportional_representation A')
      thus "l' \<le> count (lowered A) z"
        by (simp add: lowered_def lower_result_def)
    qed
  qed
qed

sublocale lowered: card_stratproof_anon_papp "l * k" parties k lowered
proof
  fix A X Y
  show "\<not>lowered.card_manipulable A X Y"
    unfolding lowered.card_manipulable_def
  proof (rule notI, elim conjE)
    assume A: "lowered.is_pref_profile A" and XY: "X \<in># A" "Y \<noteq> {}" "Y \<subseteq> parties"
    assume *: "lowered A \<prec>[lowered.committee_preference X] lowered (A - {#X#} + {#Y#})"
    interpret anon_papp_profile "l * k" "parties" k A
      by fact
    have X: "X \<noteq> {}" "X \<subseteq> parties"
      using XY A_nonempty A_subset by auto
    define A' where "A' = A - {#X#}"
    have A': "A = A' + {#X#}"
      using XY by (simp add: A'_def)

    define Al1 where "Al1 = lift_profile A"
    define Al2 where "Al2 = lift_profile (A' + {#Y#})"
    have A'_plus_Y: "lowered.is_pref_profile (A' + {#Y#})"
      unfolding A'_def using A XY lowered.is_pref_profile_replace by blast
    have Al1: "is_pref_profile Al1"
      unfolding Al1_def using A by blast
    have Al2: "is_pref_profile Al2"
      unfolding Al2_def unfolding A'_def using A XY lowered.is_pref_profile_replace by blast

    have size_aux: "size (lower_result {#x \<in># r (lift_profile A). x \<in> X#}) =
                    size {#x \<in># r (lift_profile A). x \<in> X#} - (if x \<in> X then 1 else 0)"
      if A: "lowered.is_pref_profile A" for A
      using x_in_r_lift_profile[OF A]  by (subst size_lower_result') auto

    from * have "size {#x \<in># lower_result (r Al1). x \<in> X#} <
                 size {#x \<in># lower_result (r Al2). x \<in> X#}"
      by (simp add: Al1_def Al2_def lowered_def A' lowered.strong_committee_preference_iff)
    also have "{#x \<in># lower_result (r Al1). x \<in> X#} = lower_result {#x \<in># r Al1. x \<in> X#}"
      using X x unfolding lower_result_def by (subst filter_diff_mset') auto
    also have "{#x \<in># lower_result (r Al2). x \<in> X#} = lower_result {#x \<in># r Al2. x \<in> X#}"
      using X x unfolding lower_result_def by (subst filter_diff_mset') auto
    also have "size (lower_result {#x \<in># r Al1. x \<in> X#}) =
               size {#x \<in># r Al1. x \<in> X#} - (if x \<in> X then 1 else 0)"
      unfolding Al1_def by (rule size_aux) fact
    also have "size (lower_result {#x \<in># r Al2. x \<in> X#}) =
               size {#x \<in># r Al2. x \<in> X#} - (if x \<in> X then 1 else 0)"
      unfolding Al2_def by (rule size_aux) fact
    finally have "size {#x \<in># r Al1. x \<in> X#} < size {#x \<in># r Al2. x \<in> X#}"
      by auto
    hence "r Al1 \<prec>[committee_preference X] r Al2"
      by (simp add: strong_committee_preference_iff)

    moreover have "\<not>r Al1 \<prec>[committee_preference X] r Al2"
      by (rule not_manipulable' [where Y = "Y"])
         (use Al1 Al2 in \<open>auto simp: Al1_def Al2_def A'\<close>)

    ultimately show False
      by contradiction
  qed
qed

sublocale lowered: card_stratproof_weak_prop_rep_anon_papp "l * k" parties k lowered
  ..

end

end
