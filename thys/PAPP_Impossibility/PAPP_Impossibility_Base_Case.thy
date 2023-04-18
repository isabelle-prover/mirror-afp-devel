(*
  File:     PAPP_Impossibility_Base_Case.thy
  Author:   Manuel Eberl, University of Innsbruck 
*)
section \<open>The Base Case of the Impossibility\<close>
theory PAPP_Impossibility_Base_Case
  imports Anonymous_PAPP SAT_Replay
begin

text \<open>
  In this section, we will prove the base case of our P-APP impossibility result, namely that
  there exists no anonymous P-APP rule \<open>f\<close> for 6 voters, 4 parties, and committee size 3 that
  satisfies Weak Representation and Cardinality Strategyproofness.

  The proof works by looking at some (comparatively small) set of preference profiles and the
  set of all 20 possible output committees. Each proposition $f(A) = C$ (where \<open>A\<close> is a profile
  from our set and \<open>C\<close> is one of the 20 possible output committees) is considered as a Boolean
  variable.

  All the conditions arising on these variables based on the fact that \<open>f\<close> is a function
  and the additional properties (Representation, Strategyproofness) are encoded as SAT clauses.
  This SAT problem is then proven unsatisfiable by an external SAT solver and the resulting
  proof re-imported into Isabelle/HOL.
\<close>

subsection \<open>Auxiliary Material\<close>

text \<open>
  We define the set of committees of the given size \<open>k\<close> for a given set of parties \<open>P\<close>.
\<close>
definition committees :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a multiset set" where
  "committees k P = {W. set_mset W \<subseteq> P \<and> size W = k}"

text \<open>
  We now prove a recurrence for this set so that we can more easily compute the set of all
  possible committees:
\<close>
lemma committees_0 [simp]: "committees 0 P = {{#}}"
  by (auto simp: committees_def)

lemma committees_Suc:
  "committees (Suc n) P = (\<Union>x\<in>P. \<Union>W\<in>committees n P. {{#x#} + W})"
proof safe
  fix C assume C: "C \<in> committees (Suc n) P"
  hence "size C = Suc n"
    by (auto simp: committees_def)
  hence "C \<noteq> {#}"
    by auto
  then obtain x where x: "x \<in># C"
    by auto
  define C' where "C' = C - {#x#}"
  have "C = {#x#} + C'" "x \<in> P" "C' \<in> committees n P"
    using C x  by (auto simp: committees_def C'_def size_Diff_singleton dest: in_diffD)
  thus "C \<in> (\<Union>x\<in>P. \<Union>W\<in>committees n P. {{#x#} + W})"
    by blast
qed (auto simp: committees_def)

text \<open>
  The following function takes a list $[a_1, \ldots, a_n]$ and computes the list of all pairs
  of the form $(a_i, a_j)$ with $i < j$:
\<close>
fun pairs :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
  "pairs [] = []"
| "pairs (x # xs) = map (\<lambda>y. (x, y)) xs @ pairs xs"

lemma distinct_conv_pairs: "distinct xs \<longleftrightarrow> list_all (\<lambda>(x,y). x \<noteq> y) (pairs xs)"
  by (induction xs) (auto simp: list_all_iff)

lemma list_ex_unfold: "list_ex P (x # y # xs) \<longleftrightarrow> P x \<or> list_ex P (y # xs)" "list_ex P [x] \<longleftrightarrow> P x"
  by simp_all

lemma list_all_unfold: "list_all P (x # y # xs) \<longleftrightarrow> P x \<and> list_all P (y # xs)" "list_all P [x] \<longleftrightarrow> P x"
  by simp_all


subsection \<open>Setup for the Base Case\<close>

text \<open>
  We define a locale for an anonymous P-APP rule for 6 voters, 4 parties, and committee size 3
  that satisfies weak representation and cardinality strategyproofness. Our goal is to prove
  the theorem \<^term>\<open>False\<close> inside this locale.
\<close>

locale papp_impossibility_base_case =
  card_stratproof_weak_rep_anon_papp 6 parties 3 r
  for parties :: "'a set" and r +
  assumes card_parties: "card parties = 4"
begin

text \<open>
  A slightly more convenient version of Weak Representation:
\<close>
lemma weak_representation':
  assumes "is_pref_profile A" "A' \<equiv> A" "\<forall>z\<in>Z. count A {z} \<ge> 2" "\<not>Z \<subseteq> set_mset W"
  shows   "r A' \<noteq> W"
  using weak_representation[OF assms(1)] assms(2-4) by auto

text \<open>
  The following lemma (Lemma~2 in the appendix of the paper) is a strengthening of Weak
  Representation and Strategyproofness in our concrete setting:

  Let \<open>A\<close> be a preference profile containing approval lists \<open>X\<close> and
  let \<open>Z\<close> be a set of parties such that each element of \<open>Z\<close> is uniquely approved by at least two
  voters in \<open>A\<close>. Due to Weak Representation, at least \<open>|X \<inter> Z|\<close> members of the committee are then
  approved by \<open>X\<close>.

  What the lemma now says is that if there exists another voter with approval list \<open>Y \<subseteq> X\<close> and
  $Y \nsubseteq Z$, then there is an additional committee member that is approved by \<open>X\<close>.

  This lemma will be used both in our symmetry-breaking argument and as a means to add more
  clauses to the SAT instance. Since these clauses are logical consequences of Strategyproofness
  and Weak Representation, they are technically redundant -- but their presence allows us to
  use consider a smaller set of profiles and still get a contradiction. Without using the lemma,
  we would need to feed more profiles to the SAT solver to obtain the same information.
\<close>
lemma lemma2:
  assumes A: "is_pref_profile A"
  assumes "X \<in># A" and "Y \<in># A - {#X#}" and "Y \<subseteq> X" and "\<not>Y \<subseteq> Z"
  assumes Z: "\<forall>z\<in>Z. count A {z} \<ge> 2"
  shows   "size (filter_mset (\<lambda>x. x \<in> X) (r A)) > card (X \<inter> Z)"
proof (rule ccontr)
  text \<open>
    For the sake of contradiction, suppose the number of elements approved by \<open>X\<close> were
    no larger than \<open>|X \<inter> Z|\<close>.
  \<close>
  assume "\<not>size (filter_mset (\<lambda>x. x \<in> X) (r A)) > card (X \<inter> Z)"
  hence le: "size (filter_mset (\<lambda>x. x \<in> X) (r A)) \<le> card (X \<inter> Z)"
    by linarith
  interpret anon_papp_profile 6 parties 3 A
    by fact
  have "Z \<subseteq> parties"
    using assms(1,6) by (meson is_committee_def order.trans rule_wf weak_representation')
  have [simp]: "finite Z"
    by (rule finite_subset[OF _ finite_parties]) fact

  text \<open>
    Due to Weak Representation, each member of \<open>X \<inter> Z\<close> must be chosen at least once. But due
    to the above, it cannot be chosen more than once. So it has to be chosen exactly once.
  \<close>
  have X_approved_A_eq: "filter_mset (\<lambda>x. x \<in> X) (r A) = mset_set (X \<inter> Z)"
  proof -
    have "mset_set Z \<subseteq># r A"
      using Z weak_representation[OF A] by (subst mset_set_subset_iff) auto
    hence "size (filter_mset (\<lambda>x. x \<in> X) (mset_set Z)) \<le> size (filter_mset (\<lambda>x. x \<in> X) (r A))"
      by (intro size_mset_mono multiset_filter_mono)
    also have "filter_mset (\<lambda>x. x \<in> X) (mset_set Z) = mset_set {x\<in>Z. x \<in> X}"
      by simp
    also have "{x\<in>Z. x \<in> X} = X \<inter> Z"
      by auto
    also have "size (mset_set (X \<inter> Z)) = card (X \<inter> Z)"
      by simp
    finally have "size (filter_mset (\<lambda>x. x \<in> X) (r A)) = card (X \<inter> Z)"
      using le by linarith
    moreover have "mset_set (X \<inter> Z) \<subseteq># filter_mset (\<lambda>x. x \<in> X) (r A)"
      using Z weak_representation[OF A] by (subst mset_set_subset_iff) auto
    ultimately show "filter_mset (\<lambda>x. x \<in> X) (r A) = mset_set (X \<inter> Z)"
      by (intro mset_subset_size_ge_imp_eq [symmetric]) auto
  qed

  have count_eq_1: "count (r A) x = 1" if "x \<in> X \<inter> Z" for x
    using that X_approved_A_eq
    by (metis \<open>finite Z\<close> count_filter_mset count_mset_set' diff_is_0_eq diff_zero 
              finite_subset inf_le2 not_one_le_zero)

  text \<open>
    Let \<open>x\<close> be some element of \<open>Y\<close> that is not in \<open>Z\<close>.
  \<close>
  obtain x where x: "x \<in> Y - Z"
    using \<open>\<not>Y \<subseteq> Z\<close> by blast
  with assms have x': "x \<in> X - Z"
    by auto
  have [simp]: "x \<in> parties"
    using A_subset assms(2) x' by blast

  text \<open>
    Let \<open>A'\<close> be the preference profile obtained by having voter \<open>X\<close> lying and pretending
    she only approves \<open>x\<close>.
  \<close>
  define A' where "A' = A - {#X#} + {#{x}#}"
  have A': "is_pref_profile A'"
    using is_pref_profile_replace[OF A \<open>X \<in># A\<close>, of "{x}"] by (auto simp: A'_def)

  text \<open>
    We now show that even with this manipulated profile, the committee members approved by \<open>X\<close>
    are exactly the same as before:
  \<close>
  have X_approved_A'_eq: "filter_mset (\<lambda>x. x \<in> X) (r A') = mset_set (X \<inter> Z)"
  proof -
    text \<open>
      Every element of \<open>Z\<close> must still be in the result committee due to Weak Representation.
    \<close>
    have "mset_set Z \<subseteq># r A'"
    proof (subst mset_set_subset_iff) 
      show "Z \<subseteq> set_mset (r A')"
      proof
        fix z assume z: "z \<in> Z"
        from x' z have [simp]: "x \<noteq> z"
          by auto
        have [simp]: "X \<noteq> {z}"
          using x' by auto
        show "z \<in># r A'"
          using Z weak_representation[OF A', of z] z x x' by (auto simp: A'_def)
      qed
    qed auto
  
    text \<open>
      Thus the parties in \<open>X \<inter> Z\<close> must be in the committee (and they are approved by \<open>X\<close>).
    \<close>
    have "mset_set (X \<inter> Z) \<subseteq># filter_mset (\<lambda>x. x \<in> X) (r A')"
    proof -
      have "filter_mset (\<lambda>x. x \<in> X) (mset_set Z) \<subseteq># filter_mset (\<lambda>x. x \<in> X) (r A')"
        using \<open>mset_set Z \<subseteq># r A'\<close> by (intro multiset_filter_mono) auto
      also have "filter_mset (\<lambda>x. x \<in> X) (mset_set Z) = mset_set (X \<inter> Z)"
        by auto
      finally show "mset_set (X \<inter> Z) \<subseteq># filter_mset (\<lambda>x. x \<in> X) (r A')" .
    qed
  
    text \<open>
      Due to Strategyproofness, no additional committee members can be approved by \<open>X\<close>,
      so indeed only \<open>X \<inter> Z\<close> is approved by \<open>X\<close>, and they each occur only once.
    \<close>
    moreover have "\<not>card_manipulable A X {x}"
      using not_manipulable by blast
    hence "size (mset_set (X \<inter> Z)) \<ge> size (filter_mset (\<lambda>x. x \<in> X) (r A'))" using assms
      by (simp add: card_manipulable_def A'_def strong_committee_preference_iff not_less
                    X_approved_A_eq)
    ultimately show "filter_mset (\<lambda>x. x \<in> X) (r A') = mset_set (X \<inter> Z)"
      by (metis mset_subset_size_ge_imp_eq)
  qed

  text \<open>
    Next, we show that the set of committee members approved by \<open>Y\<close> in the committee returned for
    the manipulated profile is exactly \<open>Y \<inter> Z\<close> (and again, each party only occurs once).
  \<close>
  have Y_approved_A'_eq: "filter_mset (\<lambda>x. x \<in> Y) (r A') = mset_set (Y \<inter> Z)"
  proof -
    have "filter_mset (\<lambda>x. x \<in> Y) (filter_mset (\<lambda>x. x \<in> X) (r A')) =
           filter_mset (\<lambda>x. x \<in> Y) (mset_set (X \<inter> Z))"
      by (simp only: X_approved_A'_eq)
    also have "filter_mset (\<lambda>x. x \<in> Y) (filter_mset (\<lambda>x. x \<in> X) (r A')) =
               filter_mset (\<lambda>x. x \<in> Y \<and> x \<in> X) (r A')"
      by (simp add: filter_filter_mset conj_commute)
    also have "(\<lambda>x. x \<in> Y \<and> x \<in> X) = (\<lambda>x. x \<in> Y)"
      using assms by auto
    also have "filter_mset (\<lambda>x. x \<in> Y) (mset_set (X \<inter> Z)) = mset_set (Y \<inter> Z)"
      using assms by auto
    finally show ?thesis .
  qed

  text \<open>
    Next, define the profile \<open>A''\<close> obtained from \<open>A'\<close> by also having \<open>Y\<close> pretend to approve
    only \<open>x\<close>.
  \<close>
  define A'' where "A'' = A' - {#Y#} + {#{x}#}"
  have "Y \<in># A'"
    using assms by (auto simp: A'_def)
  hence A'': "is_pref_profile A''"
    using is_pref_profile_replace[OF A', of Y "{x}"] by (auto simp: A''_def)

  text \<open>
    Again, the elements of \<open>Z\<close> must be chosen due to Weak Representation.
  \<close>
  have "Z \<subseteq> set_mset (r A'')"
  proof
    fix z assume z: "z \<in> Z"
    from x' z have [simp]: "x \<noteq> z"
      by auto
    have [simp]: "X \<noteq> {z}" "Y \<noteq> {z}"
      using x x' by auto
    show "z \<in># r A''"
      using Z weak_representation[OF A'', of z] z x x' 
      by (auto simp: A''_def A'_def)
  qed

  text \<open>
    But now additionally, \<open>x\<close> must be chosen, since both \<open>X\<close> and \<open>Y\<close> uniquely approve it.
  \<close>
  moreover have "x \<in># r A''"
    using x x' \<open>Y \<in># A - {#X#}\<close> by (intro weak_representation A'') (auto simp: A''_def A'_def)
  ultimately have "insert x (Y \<inter> Z) \<subseteq> set_mset (r A'') \<inter> Y"
    using x by blast

  text \<open>
    Now we have a contradiction due to Strategyproofness, since \<open>Y\<close> can force the additional
    member \<open>x\<close> into the committee by lying.
  \<close>
  hence "mset_set (insert x (Y \<inter> Z)) \<subseteq># filter_mset (\<lambda>w. w \<in> Y) (r A'')"
    by (subst mset_set_subset_iff) auto
  hence "size (mset_set (insert x (Y \<inter> Z))) \<le> size (filter_mset (\<lambda>w. w \<in> Y) (r A''))"
    by (rule size_mset_mono)
  hence "size (filter_mset (\<lambda>x. x \<in> Y) (r A'')) > size (filter_mset (\<lambda>x. x \<in> Y) (r A'))"
    using x by (simp add: Y_approved_A'_eq)
  hence "card_manipulable A' Y {x}"
    using A' x \<open>Y \<in># A'\<close>
    unfolding card_manipulable_def strong_committee_preference_iff A''_def by auto
  thus False
    using not_manipulable by blast
qed

text \<open>
  The following are merely reformulation of the above lemma for technical reasons.
\<close>
lemma lemma2':
  assumes "is_pref_profile A"
  assumes "\<forall>z\<in>Z. count A {z} \<ge> 2"
  assumes "X \<in># A \<and> (\<exists>Y. Y \<in># A - {#X#} \<and> Y \<subseteq> X \<and> \<not>Y \<subseteq> Z)"
  shows   "\<not>filter_mset (\<lambda>x. x \<in> X) (r A) \<subseteq># mset_set (X \<inter> Z)"
proof
  assume subset: "filter_mset (\<lambda>x. x \<in> X) (r A) \<subseteq># mset_set (X \<inter> Z)"
  from assms(3) obtain Y where Y: "X \<in># A" "Y \<in># A - {#X#}" "Y \<subseteq> X" "\<not>Y \<subseteq> Z"
    by blast
  have "card (X \<inter> Z) < size {#x \<in># r A. x \<in> X#}"
    by (rule lemma2[where Y = Y]) (use Y assms(1,2) in auto)
  with size_mset_mono[OF subset] show False
    by simp
qed

lemma lemma2'':
  assumes "is_pref_profile A"
  assumes "A' \<equiv> A"
  assumes "\<forall>z\<in>Z. count A {z} \<ge> 2"
  assumes "X \<in># A \<and> (\<exists>Y\<in>set_mset (A - {#X#}). Y \<subseteq> X \<and> \<not>Y \<subseteq> Z)"
  assumes "filter_mset (\<lambda>x. x \<in> X) W \<subseteq># mset_set (X \<inter> Z)"
  shows   "r A' \<noteq> W"
  using lemma2'[of A Z X] assms by auto


subsection \<open>Symmetry Breaking\<close>

text \<open>
  In the following, we formalize the symmetry-breaking argument that shows that we can
  reorder the four alternatives $C_1$ to $C_4$ in such a way that the preference profile
  \[ \{C_1\}\ \ \{C_2\}\ \  \{C_1, C_2\}\ \  \{C_3\}\ \  \{C_3\}\ \  \{C_3, C_4\} \]
  is mapped to one of the committees $[C_1, C_1, C_3]$ or $[C_1, C_2, C_3]$.

  We start with a simple technical lemma that states that if we have a multiset $A$ of size 3
  consisting of the elements $x$ and $y$ and $x$ occurs at least as often as $y$, then
  $A = [x, x, y]$.
\<close>

lemma papp_multiset_3_aux:
  assumes "size A = 3" "x \<in># A" "y \<in># A" "set_mset A \<subseteq> {x, y}" "x \<noteq> y" "count A x \<ge> count A y"
  shows   "A = {#x, x, y#}"
proof -
  have "count A x > 0"
    using assms by force
  have "size A = (\<Sum>z\<in>set_mset A. count A z)"
    by (rule size_multiset_overloaded_eq)
  also have "set_mset A = {x, y}"
    using assms by auto
  also have "(\<Sum>z\<in>\<dots>. count A z) = count A x + count A y"
    using assms by auto
  finally have "count A x + count A y = 3"
    by (simp add: assms(1))
  moreover from assms have "count A x > 0" "count A y > 0"
    by auto
  ultimately have *: "count A x = 2 \<and> count A y = 1"
    using \<open>count A x \<ge> count A y\<close> by linarith
  show ?thesis
  proof (rule multiset_eqI)
    fix z show "count A z = count {#x, x, y#} z"
    proof (cases "z \<in> {x, y}")
      case False
      with assms have "z \<notin> set_mset A"
        by auto
      hence "count A z = 0"
        by (simp add: Multiset.not_in_iff)
      thus ?thesis
        using False by auto
    qed (use * in auto)
  qed
qed

text \<open>
  The following is the main symmetry-breaking result. It shows that we can find parties
  $C_1$ to $C_4$ with the desired property.

  This is a somewhat ad-hoc argument; in the appendix of the paper this is done more
  systematically in Lemma~3.
\<close>
lemma symmetry_break_aux:
  obtains C1 C2 C3 C4 where
    "parties = {C1, C2, C3, C4}" "distinct [C1, C2, C3, C4]"
    "r ({#{C1}, {C2}, {C1, C2}, {C3}, {C4}, {C3, C4}#}) \<in> {{#C1, C1, C3#}, {#C1, C2, C3#}}"
proof -
  note I = that
  have "\<exists>xs. set xs = parties \<and> distinct xs"
    using finite_distinct_list[of parties] by blast
  then obtain xs where xs: "set xs = parties" "distinct xs"
    by blast
  from xs have "length xs = 4"
    using card_parties distinct_card[of xs] by auto
  then obtain C1 C2 C3 C4 where xs_eq: "xs = [C1, C2, C3, C4]"
    by (auto simp: eval_nat_numeral length_Suc_conv)
  have parties_eq: "parties = {C1, C2, C3, C4}"
    by (subst xs(1) [symmetric], subst xs_eq) auto
  have [simp]:
       "C1 \<noteq> C2" "C1 \<noteq> C3" "C1 \<noteq> C4"
       "C2 \<noteq> C1" "C2 \<noteq> C3" "C2 \<noteq> C4"
       "C3 \<noteq> C1" "C3 \<noteq> C2" "C3 \<noteq> C4"
       "C4 \<noteq> C1" "C4 \<noteq> C2" "C4 \<noteq> C3"
    using \<open>distinct xs\<close> unfolding xs_eq by auto

  define A where "A = {#{C1}, {C2}, {C1, C2}, {C3}, {C4}, {C3, C4}#}"
  define m where "m = Max (count (r A) ` parties)"

  have A: "is_pref_profile A"
    unfolding A_def is_pref_profile_iff by (simp add: parties_eq)
  hence "is_committee (r A)"
    by (rule rule_wf)
  hence rA: "size (r A) = 3" "set_mset (r A) \<subseteq> parties"
    unfolding is_committee_def by auto
  define X where "X = set_mset (r A)"
  have "X \<noteq> {}" "X \<subseteq> parties"
    using rA by (auto simp: X_def)

  have "m > 0"
  proof -
    obtain x where "x \<in> X"
      using \<open>X \<noteq> {}\<close> by blast
    with \<open>X \<subseteq> parties\<close> have "C1 \<in> X \<or> C2 \<in> X \<or> C3 \<in> X \<or> C4 \<in> X"
      unfolding parties_eq by blast
    thus ?thesis
      unfolding m_def X_def by (subst Max_gr_iff) (auto simp: parties_eq)
  qed

  have "m \<le> 3"
  proof -
    have "m \<le> size (r A)"
      unfolding m_def by (subst Max_le_iff) (auto simp: count_le_size)
    also have "\<dots> = 3"
      by fact
    finally show ?thesis .
  qed

  have "m \<in> (count (r A) ` parties)"
    unfolding m_def by (intro Max_in) auto
  then obtain C1' where C1': "count (r A) C1' = m" "C1' \<in> parties"
    by blast
  have "C1' \<in># r A"
    using \<open>m > 0\<close> C1'(1) by auto

  have "\<exists>C2'\<in>parties-{C1'}. {C1', C2'} \<in># A"
    using C1' unfolding A_def parties_eq
    by (elim insertE; simp add: insert_Diff_if insert_commute)
  then obtain C2' where C2': "C2' \<in> parties - {C1'}" "{C1', C2'} \<in># A"
    by blast
  have [simp]: "C1' \<noteq> C2'" "C2' \<noteq> C1'"
    using C2' by auto
  have disj: "C1' = C1 \<and> C2' = C2 \<or> C1' = C2 \<and> C2' = C1 \<or> C1' = C3 \<and> C2' = C4 \<or> C1' = C4 \<and> C2' = C3"
    using C1'(2) C2' unfolding A_def parties_eq 
    by (elim insertE; force simp: insert_commute)

  obtain C3' where C3': "C3' \<in> parties-{C1', C2'}"
    using C1'(2) C2' unfolding parties_eq by (fastforce simp: insert_Diff_if)
  obtain C4' where C4': "C4' \<in> parties-{C1', C2', C3'}"
    using C1'(2) C2' C3' unfolding parties_eq by (fastforce simp: insert_Diff_if)
  have A_eq: "A = {#{C1'}, {C2'}, {C1', C2'}, {C3'}, {C4'}, {C3', C4'}#}"
    using disj C3' C4'
    by (elim disjE) (auto simp: A_def parties_eq insert_commute)
  have distinct:
       "C1' \<noteq> C2'" "C1' \<noteq> C3'" "C1' \<noteq> C4'"
       "C2' \<noteq> C1'" "C2' \<noteq> C3'" "C2' \<noteq> C4'"
       "C3' \<noteq> C1'" "C3' \<noteq> C2'" "C3' \<noteq> C4'"
       "C4' \<noteq> C1'" "C4' \<noteq> C2'" "C4' \<noteq> C3'"
    using C1' C2' C3' C4' by blast+
  have parties_eq': "parties = {C1', C2', C3', C4'}"
    using C1'(2) C2'(1) C3' C4' distinct unfolding parties_eq by (elim insertE) auto

  have "\<not>{#x \<in># r A. x \<in> {C3', C4'}#} \<subseteq># mset_set ({C3', C4'} \<inter> {})"
    by (rule lemma2'[OF A]) (auto simp: A_eq)
  hence C34': "C3' \<in># r A \<or> C4' \<in># r A"
    by auto
  then consider "C3' \<in># r A" "C4' \<in># r A" | "C3' \<in># r A" "C4' \<notin># r A" | "C3' \<notin># r A" "C4' \<in># r A"
    by blast

  thus ?thesis
  proof cases
    assume *: "C3' \<in># r A" "C4' \<in># r A"
    have "r A = {#C3', C4', C1'#}"
      by (rule sym, rule mset_subset_size_ge_imp_eq)
         (use * \<open>C1' \<in># r A\<close> distinct in 
            \<open>auto simp: \<open>size (r A) = 3\<close> Multiset.insert_subset_eq_iff in_diff_multiset_absorb2\<close>)
    thus ?thesis using distinct
      by (intro that[of C3' C4' C1' C2'])
         (auto simp: parties_eq' A_eq add_mset_commute insert_commute)

  next

    assume *: "C3' \<in># r A" "C4' \<notin># r A"
    show ?thesis
    proof (cases "C2' \<in># r A")
      case True
      have "r A = {#C1', C2', C3'#}"
        by (rule sym, rule mset_subset_size_ge_imp_eq)
           (use * \<open>C1' \<in># r A\<close> distinct True in 
              \<open>auto simp: \<open>size (r A) = 3\<close> Multiset.insert_subset_eq_iff in_diff_multiset_absorb2\<close>)
      thus ?thesis using distinct
        by (intro that[of C1' C2' C3' C4'])
           (auto simp: parties_eq' A_eq add_mset_commute insert_commute)
    next
      case False
      have "r A = {#C1', C1', C3'#}"
      proof (rule papp_multiset_3_aux)
        show "set_mset (r A) \<subseteq> {C1', C3'}"
          using \<open>set_mset (r A) \<subseteq> _\<close> * False unfolding parties_eq' by auto
      next
        have "count (r A) C3' \<le> m"
          unfolding m_def by (subst Max_ge_iff) (auto simp: parties_eq')
        also have "m = count (r A) C1'"
          by (simp add: C1')
        finally show "count (r A) C3' \<le> count (r A) C1'" .
      qed (use C1' * False \<open>C1' \<in># r A\<close> distinct in \<open>auto simp: \<open>size (r A) = 3\<close>\<close>)
      thus ?thesis using distinct
        by (intro that[of C1' C2' C3' C4'])
           (auto simp: parties_eq' insert_commute add_mset_commute A_eq)
    qed

  next

    assume *: "C3' \<notin># r A" "C4' \<in># r A"
    show ?thesis
    proof (cases "C2' \<in># r A")
      case True
      have "r A = {#C1', C2', C4'#}"
        by (rule sym, rule mset_subset_size_ge_imp_eq)
           (use * \<open>C1' \<in># r A\<close> distinct True in 
              \<open>auto simp: \<open>size (r A) = 3\<close> Multiset.insert_subset_eq_iff in_diff_multiset_absorb2\<close>)
      thus ?thesis using distinct
        by (intro that[of C1' C2' C4' C3'])
           (auto simp: parties_eq' A_eq add_mset_commute insert_commute)
    next
      case False
      have "r A = {#C1', C1', C4'#}"
      proof (rule papp_multiset_3_aux)
        show "set_mset (r A) \<subseteq> {C1', C4'}"
          using \<open>set_mset (r A) \<subseteq> _\<close> * False unfolding parties_eq' by auto
      next
        have "count (r A) C4' \<le> m"
          unfolding m_def by (subst Max_ge_iff) (auto simp: parties_eq')
        also have "m = count (r A) C1'"
          by (simp add: C1')
        finally show "count (r A) C4' \<le> count (r A) C1'" .
      qed (use C1' * False \<open>C1' \<in># r A\<close> distinct in \<open>auto simp: \<open>size (r A) = 3\<close>\<close>)
      thus ?thesis using distinct
        by (intro that[of C1' C2' C4' C3'])
           (auto simp: parties_eq' insert_commute add_mset_commute A_eq)
    qed
  qed
qed

text \<open>
  We now use the choice operator to get our hands on such values $C_1$ to $C_4$.
\<close>
definition C1234 where
  "C1234 = (SOME xs. set xs = parties \<and> distinct xs \<and> 
              (case xs of [C1, C2, C3, C4] \<Rightarrow>
              r ({#{C1}, {C2}, {C1, C2}, {C3}, {C4}, {C3, C4}#}) \<in> {{#C1, C1, C3#}, {#C1, C2, C3#}}))"

definition C1 where "C1 = C1234 ! 0"
definition C2 where "C2 = C1234 ! 1"
definition C3 where "C3 = C1234 ! 2"
definition C4 where "C4 = C1234 ! 3"

lemma distinct: "distinct [C1, C2, C3, C4]"
  and parties_eq:  "parties = {C1, C2, C3, C4}"
  and symmetry_break:
        "r ({#{C1}, {C2}, {C1, C2}, {C3}, {C4}, {C3, C4}#}) \<in> {{#C1, C1, C3#}, {#C1, C2, C3#}}"
proof -
  have C1234:
        "set C1234 = parties \<and> distinct C1234 \<and> 
        (case C1234 of [C1', C2', C3', C4'] \<Rightarrow>
            r ({#{C1'}, {C2'}, {C1', C2'}, {C3'}, {C4'}, {C3', C4'}#}) \<in>
              {{#C1', C1', C3'#}, {#C1', C2', C3'#}})"
    unfolding C1234_def
  proof (rule someI_ex)
    obtain C1' C2' C3' C4' where *:
      "parties = {C1', C2', C3', C4'}" "distinct [C1', C2', C3', C4']"
      "r ({#{C1'}, {C2'}, {C1', C2'}, {C3'}, {C4'}, {C3', C4'}#}) \<in> 
         {{#C1', C1', C3'#}, {#C1', C2', C3'#}}"
      using symmetry_break_aux by blast    
    show "\<exists>xs. set xs = parties \<and> distinct xs \<and> 
            (case xs of [C1', C2', C3', C4'] \<Rightarrow>
              r ({#{C1'}, {C2'}, {C1', C2'}, {C3'}, {C4'}, {C3', C4'}#}) \<in> 
                {{#C1', C1', C3'#}, {#C1', C2', C3'#}})"
      by (intro exI[of _ "[C1', C2', C3', C4']"]) (use * in auto)
  qed

  have "length C1234 = 4"
    using C1234 card_parties distinct_card[of C1234] by simp
  then obtain C1' C2' C3' C4' where C1234_eq: "C1234 = [C1', C2', C3', C4']"
    by (auto simp: eval_nat_numeral length_Suc_conv)
  show "distinct [C1, C2, C3, C4]" "parties = {C1, C2, C3, C4}" 
       "r ({#{C1}, {C2}, {C1, C2}, {C3}, {C4}, {C3, C4}#}) \<in> {{#C1, C1, C3#}, {#C1, C2, C3#}}"
    using C1234 by (simp_all add: C1234_eq C1_def C2_def C3_def C4_def)
qed

lemma distinct' [simp]:
   "C1 \<noteq> C2" "C1 \<noteq> C3" "C1 \<noteq> C4" "C2 \<noteq> C1" "C2 \<noteq> C3" "C2 \<noteq> C4"
   "C3 \<noteq> C1" "C3 \<noteq> C2" "C3 \<noteq> C4" "C4 \<noteq> C1" "C4 \<noteq> C2" "C4 \<noteq> C3"
  using distinct by auto

lemma in_parties [simp]: "C1 \<in> parties" "C2 \<in> parties" "C3 \<in> parties" "C4 \<in> parties"
  by (subst (2) parties_eq; simp; fail)+


subsection \<open>The Set of Possible Committees\<close>

text \<open>
  Next, we compute the set of the 20 possible committees.
\<close>

abbreviation COM where "COM \<equiv> committees 3 parties"

definition COM' where "COM' =
  [{#C1, C1, C1#}, {#C1, C1, C2#}, {#C1, C1, C3#}, {#C1, C1, C4#},
   {#C1, C2, C2#}, {#C1, C2, C3#}, {#C1, C2, C4#}, {#C1, C3, C3#},
   {#C1, C3, C4#}, {#C1, C4, C4#}, {#C2, C2, C2#}, {#C2, C2, C3#},
   {#C2, C2, C4#}, {#C2, C3, C3#}, {#C2, C3, C4#}, {#C2, C4, C4#},
   {#C3, C3, C3#}, {#C3, C3, C4#}, {#C3, C4, C4#},
   {#C4, C4, C4#}]"

lemma distinct_COM': "distinct COM'"
  by (simp add: COM'_def add_mset_neq)

lemma COM_eq: "COM = set COM'"
  by (subst parties_eq)
     (simp_all add: COM'_def numeral_3_eq_3 committees_Suc add_ac insert_commute add_mset_commute)

lemma r_in_COM:
  assumes "is_pref_profile A"
  shows   "r A \<in> COM"
  using rule_wf[OF assms] unfolding committees_def is_committee_def by auto

lemma r_in_COM':
  assumes "is_pref_profile A" "A' \<equiv> A"
  shows   "list_ex (\<lambda>W. r A' = W) COM'"
  using r_in_COM[OF assms(1)] assms(2) by (auto simp: list_ex_iff COM_eq)

lemma r_right_unique:
  "list_all (\<lambda>(W1,W2). r A \<noteq> W1 \<or> r A \<noteq> W2) (pairs COM')"
proof -
  have "list_all (\<lambda>(W1,W2). W1 \<noteq> W2) (pairs COM')"
    using distinct_COM' unfolding distinct_conv_pairs by blast
  thus ?thesis
    unfolding list_all_iff by blast
qed

end



subsection \<open>Generating Clauses and Replaying the SAT Proof\<close>

text \<open>
  We now employ some custom-written ML code to generate all the SAT clauses arising from the
  given profiles (read from an external file) as Isabelle/HOL theorems. From these, we then
  derive \<^term>\<open>False\<close> by replaying an externally found SAT proof (also written from an external
  file).

  The proof was found with the glucose SAT solver, which outputs proofs in the DRUP format
  (a subset of the more powerful DRAT format). We then used the \<^emph>\<open>DRAT-trim\<close> tool by
  Wetzler et al.~\cite{wetzler_drat_trim} to make the proof smaller. This was done repeatedly
  until the proof size did not decrease any longer. Then, the proof was converted into the \<^emph>\<open>GRAT\<close>
  format introduced by Lammich~\cite{lammich_grat}, which is easier to check (or in our case
  replay) than the less explicit DRAT (or DRUP) format. 
\<close>

external_file "sat_data/profiles"
external_file "sat_data/papp_impossibility.grat.xz"

context papp_impossibility_base_case
begin

ML_file \<open>papp_impossibility.ML\<close>

text \<open>
  This invocation proves a theorem called \<^emph>\<open>contradiction\<close> whose statement is \<^term>\<open>False\<close>.
  Note that the DIMACS version of the SAT file that is being generated can be viewed by
  clicking on ``See theory exports'' in the messages output by the invocation below.

  On a 2021 desktop PC with 12 cores, proving all the clauses takes 8.4\,s (multithreaded;
  CPU time 55\,s). Replaying the proof takes 30\,s (singlethreaded).
\<close>

local_setup \<open>fn lthy =>
  let
    val thm =
      PAPP_Impossibility.derive_false lthy
        (\<^master_dir> + \<^path>\<open>sat_data/profiles\<close>)
        (\<^master_dir> + \<^path>\<open>sat_data/papp_impossibility.grat.xz\<close>)
  in
    Local_Theory.note ((\<^binding>\<open>contradiction\<close>, []), [thm]) lthy |> snd
  end
\<close>

end

text \<open>
  With this, we can now prove the impossibility result:
\<close>
lemma papp_impossibility_base_case:
  assumes "card parties = 4"
  shows   "\<not>card_stratproof_weak_rep_anon_papp 6 parties 3 r"
proof
  assume "card_stratproof_weak_rep_anon_papp 6 parties 3 r"
  then interpret card_stratproof_weak_rep_anon_papp 6 parties 3 r .
  interpret papp_impossibility_base_case parties r
    by unfold_locales fact+
  show False
    by (rule contradiction)
qed

end
