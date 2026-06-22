(*  Title:       Free_Group_F2.thy
    Author:      Arthur F. Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026

    The free group on two generators, F\<^sub>2, specialised from the AFP
    \<^session>\<open>Free-Groups\<close> entry. Provides the four "starts-with" classes
    and their basic combinatorics.
*)

theory Free_Group_F2
  imports
    BT_Prelim
    "Free-Groups.FreeGroups"
begin

section \<open>Two-element generator type\<close>

text \<open>
  We pick a concrete two-element type for the generators of \<open>F\<^sub>2\<close>.
\<close>

datatype gen2 = A | B

abbreviation Gen2 :: "gen2 set" where
  "Gen2 \<equiv> {A, B}"

lemma Gen2_finite [simp]: "finite Gen2"
  by simp

lemma Gen2_card [simp]: "card Gen2 = 2"
  by simp

lemma Gen2_UNIV: "Gen2 = (UNIV :: gen2 set)"
  using gen2.exhaust by auto


section \<open>The free group \<open>F\<^sub>2\<close> and its carrier\<close>

abbreviation F2 :: "(bool \<times> gen2) list monoid" where
  "F2 \<equiv> \<F>\<^bsub>Gen2\<^esub>"

text \<open>The carrier of \<open>F\<^sub>2\<close> consists of cancelled words over the alphabet
  \<open>UNIV \<times> Gen2 = UNIV \<times> UNIV\<close>.\<close>

lemma F2_is_group: "group F2"
  by (rule free_group_is_group)

lemma F2_carrier_iff:
  "w \<in> carrier F2 \<longleftrightarrow> w \<in> lists (UNIV \<times> Gen2) \<and> canceled w"
  by (auto simp: free_group_def)

lemma F2_carrier_alt:
  "carrier F2 = {w. canceled w}"
proof -
  have "lists (UNIV \<times> Gen2) = (UNIV :: (bool \<times> gen2) list set)"
    using Gen2_UNIV by auto
  thus ?thesis by (auto simp: free_group_def)
qed

lemma in_F2_canceled [dest]:
  assumes "w \<in> carrier F2"
  shows "canceled w"
  using assms by (simp add: F2_carrier_alt)

lemma canceled_in_F2 [intro]:
  assumes "canceled w"
  shows "w \<in> carrier F2"
  using assms by (simp add: F2_carrier_alt)

lemma canceled_iff_no_adjacent_canceling:
  "canceled w \<longleftrightarrow> (\<forall>i. Suc i < length w \<longrightarrow> \<not> canceling (w ! i) (w ! Suc i))"
proof
  assume c: "canceled w"
  show "\<forall>i. Suc i < length w \<longrightarrow> \<not> canceling (w ! i) (w ! Suc i)"
  proof (intro allI impI notI)
    fix i
    assume len: "Suc i < length w" and can: "canceling (w ! i) (w ! Suc i)"
    have "cancels_to_1_at i w (cancel_at i w)"
      using len can by (auto simp: cancels_to_1_at_def)
    hence "cancels_to_1 w (cancel_at i w)"
      unfolding cancels_to_1_def by blast
    hence "Domainp cancels_to_1 w"
      by auto
    with c show False
      by (simp add: canceled_def)
  qed
next
  assume no_adj: "\<forall>i. Suc i < length w \<longrightarrow> \<not> canceling (w ! i) (w ! Suc i)"
  show "canceled w"
  proof (simp add: canceled_def, intro notI)
    assume "Domainp cancels_to_1 w"
    then obtain w' where "cancels_to_1 w w'"
      by auto
    then obtain i where "cancels_to_1_at i w w'"
      unfolding cancels_to_1_def by auto
    hence "Suc i < length w" and "canceling (w ! i) (w ! Suc i)"
      by (auto simp: cancels_to_1_at_def)
    with no_adj show False
      by blast
  qed
qed

lemma canceled_Cons_iff:
  "canceled (p # w) \<longleftrightarrow> canceled w \<and> (w = [] \<or> \<not> canceling p (hd w))"
  unfolding canceled_iff_no_adjacent_canceling
  by (cases w)
    (auto simp: nth_Cons split: nat.splits)

lemma F2_ConsD:
  assumes "p # w \<in> carrier F2"
  shows "w \<in> carrier F2" and "w = [] \<or> \<not> canceling p (hd w)"
  using assms by (simp_all add: F2_carrier_alt canceled_Cons_iff)

lemma F2_ConsI:
  assumes "w \<in> carrier F2" and "w = [] \<or> \<not> canceling p (hd w)"
  shows "p # w \<in> carrier F2"
  using assms by (simp add: F2_carrier_alt canceled_Cons_iff)

lemma F2_one [simp]: "\<one>\<^bsub>F2\<^esub> = []"
  by (simp add: free_group_def)

lemma F2_mult: "x \<otimes>\<^bsub>F2\<^esub> y = normalize (x @ y)"
  by (simp add: free_group_def)


section \<open>The four ``starts-with'' classes of \<open>F\<^sub>2\<close>\<close>

text \<open>
  A non-empty reduced word in \<open>F\<^sub>2\<close> begins with one of four
  letters: \<open>a\<close>, \<open>a\<^sup>-\<^sup>1\<close>, \<open>b\<close>, or
  \<open>b\<^sup>-\<^sup>1\<close>. The corresponding ``starts-with'' classes
  partition \<open>F\<^sub>2 \\ {1}\<close>.
\<close>

definition starts_with :: "bool \<Rightarrow> gen2 \<Rightarrow> (bool \<times> gen2) list set" where
  "starts_with b x = {w \<in> carrier F2. w \<noteq> [] \<and> hd w = (b, x)}"

abbreviation S_a   :: "(bool \<times> gen2) list set" where "S_a   \<equiv> starts_with False A"
abbreviation S_aI  :: "(bool \<times> gen2) list set" where "S_aI  \<equiv> starts_with True  A"
abbreviation S_b   :: "(bool \<times> gen2) list set" where "S_b   \<equiv> starts_with False B"
abbreviation S_bI  :: "(bool \<times> gen2) list set" where "S_bI  \<equiv> starts_with True  B"

lemma starts_with_subset: "starts_with b x \<subseteq> carrier F2"
  by (auto simp: starts_with_def)

lemma starts_with_disjoint:
  assumes "(b1, x1) \<noteq> (b2, x2)"
  shows "starts_with b1 x1 \<inter> starts_with b2 x2 = {}"
  using assms by (auto simp: starts_with_def)

lemma starts_with_pairwise_disjoint:
  shows "S_a \<inter> S_aI = {}" "S_a \<inter> S_b = {}" "S_a \<inter> S_bI = {}"
        "S_aI \<inter> S_b = {}" "S_aI \<inter> S_bI = {}" "S_b \<inter> S_bI = {}"
        "[] \<notin> S_a" "[] \<notin> S_aI" "[] \<notin> S_b" "[] \<notin> S_bI"
  by (auto simp: starts_with_def)


text \<open>
  The four classes together with the singleton \<open>{1}\<close> partition the
  carrier of \<open>F\<^sub>2\<close>. The proof is a case analysis on the head
  of a reduced word.
\<close>

lemma F2_decomposition:
  "carrier F2 = {[]} \<union> S_a \<union> S_aI \<union> S_b \<union> S_bI"
proof
  show "{[]} \<union> S_a \<union> S_aI \<union> S_b \<union> S_bI \<subseteq> carrier F2"
    using starts_with_subset
    by (auto simp: F2_carrier_alt empty_canceled)
next
  show "carrier F2 \<subseteq> {[]} \<union> S_a \<union> S_aI \<union> S_b \<union> S_bI"
  proof
    fix w assume w: "w \<in> carrier F2"
    show "w \<in> {[]} \<union> S_a \<union> S_aI \<union> S_b \<union> S_bI"
    proof (cases w)
      case Nil thus ?thesis by simp
    next
      case (Cons a u)
      obtain b x where head: "a = (b, x)" by (cases a) auto
      from w have "x \<in> Gen2" using Cons head
        by (auto simp: F2_carrier_iff)
      hence "x = A \<or> x = B" by auto
      with Cons head w show ?thesis
        unfolding starts_with_def by auto
    qed
  qed
qed


section \<open>The two distinguished generators \<open>a\<close> and \<open>b\<close>\<close>

abbreviation a_elt :: "(bool \<times> gen2) list" where "a_elt  \<equiv> [(False, A)]"
abbreviation aI_elt :: "(bool \<times> gen2) list" where "aI_elt \<equiv> [(True,  A)]"
abbreviation b_elt :: "(bool \<times> gen2) list" where "b_elt  \<equiv> [(False, B)]"
abbreviation bI_elt :: "(bool \<times> gen2) list" where "bI_elt \<equiv> [(True,  B)]"

lemma single_letter_canceled:
  "canceled [(b, x)]"
  by simp

lemma a_elt_in_F2 [simp]: "a_elt \<in> carrier F2"
  by (intro canceled_in_F2 single_letter_canceled)

lemma aI_elt_in_F2 [simp]: "aI_elt \<in> carrier F2"
  by (intro canceled_in_F2 single_letter_canceled)

lemma b_elt_in_F2 [simp]: "b_elt \<in> carrier F2"
  by (intro canceled_in_F2 single_letter_canceled)

lemma bI_elt_in_F2 [simp]: "bI_elt \<in> carrier F2"
  by (intro canceled_in_F2 single_letter_canceled)

lemma inv_a_eq_aI: "inv\<^bsub>F2\<^esub> a_elt = aI_elt"
  by (simp add: inv_fg_def inv1_def)

lemma inv_b_eq_bI: "inv\<^bsub>F2\<^esub> b_elt = bI_elt"
  by (simp add: inv_fg_def inv1_def)

lemma inv_aI_eq_a: "inv\<^bsub>F2\<^esub> aI_elt = a_elt"
  by (simp add: inv_fg_def inv1_def)

lemma inv_bI_eq_b: "inv\<^bsub>F2\<^esub> bI_elt = b_elt"
  by (simp add: inv_fg_def inv1_def)

end
