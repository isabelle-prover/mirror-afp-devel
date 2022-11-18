(*
  File:     PAPP_Impossibility.thy
  Author:   Manuel Eberl, University of Innsbruck 
*)
section \<open>Lifting the Impossibility Result to Larger Settings\<close>
theory PAPP_Impossibility
  imports PAPP_Impossibility_Base_Case Anonymous_PAPP_Lowering
begin

text \<open>
  In this section, we now prove the main results of this work by combining the base case
  with the lifting arguments formalized earlier.

  First, we prove the following very simple technical lemma: a set that is infinite or finite with
  cardinality at least 2 contains two different elements \<open>x\<close> and \<open>y\<close>.
\<close>

lemma obtain_2_elements:
  assumes "infinite X \<or> card X \<ge> 2"
  obtains x y where "x \<in> X" "y \<in> X" "x \<noteq> y"
proof -
  from assms have "X \<noteq> {}"
    by auto
  then obtain x where "x \<in> X"
    by blast
  with assms have "infinite X \<or> card (X - {x}) > 0"
    by (subst card_Diff_subset) auto
  hence "X - {x} \<noteq> {}"
    by (metis card_gt_0_iff finite.emptyI infinite_remove)
  then obtain y where "y \<in> X - {x}"
    by blast
  with \<open>x \<in> X\<close> show ?thesis
    using that[of x y] by blast
qed

text \<open>
  We now have all the ingredients to formalise the first main impossibility result: There is
  no P-APP rule that satisfies Anonymity, Cardinality-Strategyproofness, and Weak Representation
  if \<open>k \<ge> 3\<close> and \<open>m \<ge> k + 1\<close> and \<open>n\<close> is a multiple of \<open>2k\<close>.

  The proof simply uses the lowering lemmas we proved earlier to first reduce the committee size
  to 3, then reduce the voters to 6, and finally restrict the parties to 4. At that point,
  the base case we proved with SAT solving earlier kicks in.

  This corresponds to Theorem~1 in the paper.
\<close>
theorem papp_impossibility1:
  assumes "k \<ge> 3" and "card parties \<ge> k + 1" and "finite parties"
  shows   "\<not>card_stratproof_weak_rep_anon_papp (2 * k * l) parties k r"
  using assms
proof (induction k arbitrary: parties r rule: less_induct)
  case (less k parties r)
  show ?case
  proof (cases "k = 3")
    assume [simp]: "k = 3"
    text \<open>
      If the committee size is 3, we first use our voter-division lemma to
      go from a P-APP rule for $6l$ voters to one with just 6 voters. Next, we choose 4 arbitrary
      parties and use our party-restriction lemma to obtain a P-APP rule for just 4 parties.

      But this is exactly our base case, which we already know to be infeasible. 
    \<close>
    show ?thesis
    proof
      assume "card_stratproof_weak_rep_anon_papp (2 * k * l) parties k r"
      then interpret card_stratproof_weak_rep_anon_papp "l * 6" parties 3 r
        by (simp add: mult_ac)
      interpret divide_voters_card_stratproof_weak_rep_anon_papp l 6 parties 3 r ..

      have "card parties \<ge> 4"
        using less.prems by auto
      then obtain parties' where parties': "parties' \<subseteq> parties" "card parties' = 4"
        by (metis obtain_subset_with_card_n)
      have "\<exists>r. card_stratproof_weak_rep_anon_papp 6 parties' 3 r"
      proof (rule card_stratproof_weak_rep_anon_papp_restrict_parties)
        show "card_stratproof_weak_rep_anon_papp 6 parties 3 (r \<circ> lift_profile)"
          by (rule lowered.card_stratproof_weak_rep_anon_papp_axioms)
      qed (use parties' in auto)
      thus False
        using papp_impossibility_base_case[OF parties'(2)] by blast
    qed
  next
    assume "k \<noteq> 3"
    text \<open>
      If the committee size is greater than 3, we use our other lowering lemma to reduce the
      committee size by 1 (while also reducing the number of voters by $2l$ and the number of
      parties by 1).
    \<close>
    with less.prems have "k > 3"
      by simp

    obtain x y where xy: "x \<in> parties" "y \<in> parties" "x \<noteq> y"
      using obtain_2_elements[of parties] less.prems by auto
    define parties' where "parties' = parties - {y}"
    have [simp]: "card parties' = card parties - 1"
      unfolding parties'_def using xy by (subst card_Diff_subset) auto

    show ?thesis
    proof
      assume "card_stratproof_weak_rep_anon_papp (2 * k * l) parties k r"
      then interpret card_stratproof_weak_rep_anon_papp
        "2 * l * (k - 1 + 1)" "insert y parties'" "k - 1 + 1" r
        using \<open>k > 3\<close> xy by (simp add: parties'_def insert_absorb mult_ac)
      interpret decrease_committee_card_stratproof_weak_rep_anon_papp "2 * l" "k - 1" y parties' r x
        by unfold_locales (use \<open>k > 3\<close> xy in \<open>auto simp: parties'_def\<close>)
      have "\<not>card_stratproof_weak_rep_anon_papp (2 * (k - 1) * l) parties' (k - 1) lowered"
        by (rule less.IH) (use \<open>k > 3\<close> xy less.prems in auto)
      with lowered.card_stratproof_weak_rep_anon_papp_axioms show False
        by (simp add: mult_ac)
    qed
  qed
qed

text \<open>
  If Weak Representation is replaced with Weak Proportional Representation, we can strengthen
  the impossibility result by relaxing the conditions on the number of parties to \<open>m \<ge> 4\<close>.

  This works because with Weak Proportional Representation, we can reduce the size of the committee
  without changing the number of parties. We use this to again bring $k$ down to $3$ without
  changing $m$, at which point we can simply apply our previous impossibility result for
  Weak Representation.

  This corresponds to Theorem~2 in the paper.
\<close>
corollary papp_impossibility2:
  assumes "k \<ge> 3" and "card parties \<ge> 4" and "finite parties"
  shows   "\<not>card_stratproof_weak_prop_rep_anon_papp (2 * k * l) parties k r"
  using assms
proof (induction k arbitrary: parties r rule: less_induct)
  case (less k parties r)
  show ?case
  proof (cases "k = 3")
    assume [simp]: "k = 3"
    text \<open>
      For committee size 3, we simply employ our previous impossibility result:
    \<close>
    show ?thesis
    proof
      assume "card_stratproof_weak_prop_rep_anon_papp (2 * k * l) parties k r"
      then interpret card_stratproof_weak_prop_rep_anon_papp "l * 6" parties 3 r
        by (simp add: mult_ac)
      have "card_stratproof_weak_rep_anon_papp (l * 6) parties 3 r" ..
      moreover have "\<not>card_stratproof_weak_rep_anon_papp (l * 6) parties 3 r"
        using papp_impossibility1[of 3 parties l r] less.prems by (simp add: mult_ac)
      ultimately show False
        by contradiction
    qed
  next
    assume "k \<noteq> 3"
    text \<open>
      If the committee size is greater than 3, we use our other lowering lemma to reduce the
      committee size by 1 (while also reducing the number of voters by $2l$).
    \<close>

    with less.prems have "k > 3"
      by simp

    have "parties \<noteq> {}"
      using less.prems by auto
    then obtain x where x: "x \<in> parties"
      by blast

    show ?thesis
    proof
      assume "card_stratproof_weak_prop_rep_anon_papp (2 * k * l) parties k r"
      then interpret card_stratproof_weak_prop_rep_anon_papp
        "2 * l * (k - 1 + 1)" parties "k - 1 + 1" r
        using \<open>k > 3\<close> by (simp add:  mult_ac)
      interpret decrease_committee_card_stratproof_weak_prop_rep_anon_papp "2 * l" "k - 1" parties r x
        by unfold_locales (use \<open>k > 3\<close> x in auto)
      have "\<not>card_stratproof_weak_prop_rep_anon_papp (2 * (k - 1) * l) parties (k - 1) lowered"
        by (rule less.IH) (use \<open>k > 3\<close> less.prems in auto)
      with lowered.card_stratproof_weak_prop_rep_anon_papp_axioms show False
        by (simp add: mult_ac)
    qed
  qed
qed

end
