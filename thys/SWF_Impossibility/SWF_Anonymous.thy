subsection \<open>Anonymised preference profiles\<close>
theory SWF_Anonymous
  imports Social_Welfare_Functions
begin

context anonymous_swf
begin

lemma anonymous':
  assumes R: "is_pref_profile R" and R': "is_pref_profile R'"
  assumes "image_mset R (mset_set agents) = image_mset R' (mset_set agents)"
  shows   "swf R = swf R'"
proof -
  interpret R: pref_profile_linorder_wf agents alts R by fact
  interpret R': pref_profile_linorder_wf agents alts R' by fact
  obtain \<pi> where \<pi>: "\<pi> permutes agents" "\<forall>x\<in>agents. R x = R' (\<pi> x)"
    by (rule image_mset_eq_implies_permutes[OF _ assms(3)]) (use finite_agents in auto)
  from \<pi>(1) R' have "swf (R' \<circ> \<pi>) = swf R'"
    by (rule anonymous)
  also have "R' \<circ> \<pi> = R"
    using R'.not_outside(1) R.not_outside(1) \<pi>(2) permutes_in_image[OF \<pi>(1)]
    unfolding fun_eq_iff o_def by blast
  finally show ?thesis .
qed

text \<open>
  For convenience we define a simpler view on SWFs where the input is not a regular preference
  profile but an ``anonymised'' profile. Formally, this is simply the multiset of the agents' 
  rankings without any information on the identities of the agents.
\<close>
definition is_apref_profile :: "'alt relation multiset \<Rightarrow> bool" where
  "is_apref_profile Rs \<longleftrightarrow> size Rs = card agents \<and> (\<forall>R\<in>#Rs. linorder_on alts R)"


text \<open>
  The following is the corresponding version of the SWF that takes an anonymised profile:
\<close>
definition aswf :: "'alt relation multiset \<Rightarrow> 'alt relation"
  where "aswf Rs = swf (SOME R. is_pref_profile R \<and> Rs = image_mset R (mset_set agents))"

text \<open>
  Every valid anonymised profile also has at least one corresponding "non-anonymised" version.
\<close>
lemma deanonymised_profile_exists:
  assumes "is_apref_profile Rs"
  obtains R where "is_pref_profile R" "Rs = image_mset R (mset_set agents)"
proof -
  have size_eq: "size (mset_set agents) = size Rs"
    using assms by (simp add: is_apref_profile_def)
  obtain agents' where agents': "distinct agents'" "set agents' = agents"
    using finite_distinct_list by blast
  obtain Rs' where Rs': "mset Rs' = Rs"
    using ex_mset by blast
  have length_Rs':  "length Rs' = card agents"
    using Rs' size_eq by auto
  have length_agents': "length agents' = card agents"
    using agents'(1,2) distinct_card by fastforce
  have index_less: "index agents' i < card agents" if "i \<in> agents" for i
    using that by (simp add: agents'(2) length_agents')

  define R where "R = (\<lambda>i. if i \<in> agents then Rs' ! index agents' i else (\<lambda>_ _. False))"
  show ?thesis
  proof (rule that[of R])
    show "is_pref_profile R"
    proof
      fix i assume i: "i \<in> agents"
      hence "R i = Rs' ! index agents' i"
        by (auto simp: R_def)
      also have "\<dots> \<in> set Rs'"
        using index_less[of i] i length_Rs' by auto
      also have "\<dots> = set_mset Rs"
        by (simp flip: Rs')
      finally show "linorder_on alts (R i)"
        using assms by (auto simp: is_apref_profile_def)
    qed (auto simp: R_def)
  next
    have "image_mset R (mset_set agents) = image_mset (\<lambda>i. Rs' ! index agents' i) (mset_set agents)"
      by (intro image_mset_cong) (auto simp: R_def)
    also have "mset_set agents = mset agents'"
      using agents' mset_set_set by blast
    also have "image_mset (\<lambda>i. Rs' ! index agents' i) (mset agents') =
               mset (map (\<lambda>i. Rs' ! index agents' i) agents')"
      by simp
    also have "map (\<lambda>i. Rs' ! index agents' i) agents' = 
               map ((\<lambda>i. Rs' ! index agents' i) \<circ> (\<lambda>i. agents' ! i)) [0..<length agents']"
      unfolding map_map [symmetric] by (subst map_nth) simp_all
    also have "\<dots> = map (\<lambda>i. Rs' ! i) [0..<length Rs']"
      using agents' by (intro map_cong) (auto simp: index_nth_id length_agents' length_Rs')
    also have "\<dots> = Rs'"
      by (rule map_nth)
    also have "mset agents' = mset_set agents"
      using agents' mset_set_set by metis
    also have "mset Rs' = Rs"
      using Rs' by simp
    finally show "Rs = image_mset R (mset_set agents)" ..
  qed
qed

text \<open>
  The anonymous version of the SWF is well-defined w.r.t.\ the regular version of the SWF,
  i.e.\ plugging in the anonymised version of a profile gives the same result as plugging the
  original profile into the original SWF.
\<close>
lemma aswf_welldefined:
  assumes "is_pref_profile R"
  defines "Rs \<equiv> image_mset R (mset_set agents)"
  shows   "aswf Rs = swf R"
proof -
  interpret R: pref_profile_linorder_wf agents alts R
    by fact

  define R' where "R' = (SOME R. is_pref_profile R \<and> Rs = image_mset R (mset_set agents))"
  have *: "\<exists>R. is_pref_profile R \<and> Rs = image_mset R (mset_set agents)"
    using assms by blast
  have R': "is_pref_profile R'" "Rs = image_mset R' (mset_set agents)"
    using someI_ex[OF *] unfolding R'_def by blast+
  interpret R': pref_profile_linorder_wf agents alts R'
    by fact

  have "aswf Rs = swf R'"
    by (simp add: aswf_def R'_def)
  also have "swf R' = swf R"
    by (rule anonymous') (use assms R' in simp_all)
  finally show ?thesis .
qed

text \<open>
  The anonymous version of the SWF always returns a valid ranking if the input is a valid
  anonymised profile.
\<close>
lemma aswf_wf:
  assumes "is_apref_profile Rs"
  shows   "linorder_on alts (aswf Rs)"
  using assms by (metis aswf_welldefined deanonymised_profile_exists swf_wf)

lemma aswf_wf':
  assumes "is_apref_profile Rs"
  shows   "finite_linorder_on alts (aswf Rs)"
proof -
  interpret linorder_on alts "aswf Rs"
    by (rule aswf_wf) fact
  show ?thesis
    by standard auto
qed



text \<open>
  For extra notational convenience, we define yet another version of our SWF that directly takes
  multisets of lists as inputs rather than multisets of preference relations.
\<close>
definition aswf' :: "'alt list multiset \<Rightarrow> 'alt list"
  where "aswf' Rs = ranking (aswf (image_mset of_ranking Rs))"

definition is_apref_profile' :: "'alt list multiset \<Rightarrow> bool" where
  "is_apref_profile' Rs \<longleftrightarrow> size Rs = card agents \<and> (\<forall>R\<in>#Rs. R \<in> permutations_of_set alts)"

lemma is_apref_profile'_imp_is_apref_profile:
  assumes "is_apref_profile' Rs"
  shows   "is_apref_profile (image_mset of_ranking Rs)"
  unfolding is_apref_profile_def
proof (intro ballI conjI)
  fix R assume "R \<in># image_mset of_ranking Rs"
  then obtain xs where xs: "xs \<in># Rs" "R = of_ranking xs"
    by auto
  hence xs': "xs \<in> permutations_of_set alts"
    using assms xs(1) by (auto simp: is_apref_profile'_def)
  show "linorder_on alts R"
    unfolding xs(2) by (rule linorder_of_ranking) (use xs' in \<open>auto simp: permutations_of_set_def\<close>)
qed (use assms in \<open>auto simp: is_apref_profile'_def\<close>)

lemma aswf'_wf:
  assumes "is_apref_profile' Rs"
  shows   "aswf' Rs \<in> permutations_of_set alts"
proof -
  interpret linorder_on alts "aswf (image_mset of_ranking Rs)"
    by (rule aswf_wf) (use assms in \<open>auto intro: is_apref_profile'_imp_is_apref_profile\<close>)
  interpret finite_linorder_on alts "aswf (image_mset of_ranking Rs)"
    by unfold_locales auto
  show ?thesis
    unfolding aswf'_def permutations_of_set_def using distinct_ranking set_ranking by force
qed

end



locale anonymous_unanimous_swf = 
  anonymous_swf agents alts swf +
  unanimous_swf agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf
begin

lemma unanimous_aswf:
  assumes "is_apref_profile Rs" "\<forall>R\<in>#Rs. x \<succ>[R] y"
  shows   "x \<succ>[aswf Rs] y"
  using assms
  by (metis aswf_welldefined deanonymised_profile_exists finite_agents
      finite_set_mset_mset_set image_eqI multiset.set_map unanimous)

lemma unanimous_aswf':
  assumes "is_apref_profile Rs" "\<forall>R\<in>#Rs. x \<succeq>[R] y"
  shows   "x \<succeq>[aswf Rs] y"
  using assms
  by (metis aswf_welldefined deanonymised_profile_exists finite_agents
      finite_set_mset_mset_set image_eqI multiset.set_map unanimous')

lemma is_apref_profile_unanimous_not_outside:
  assumes "is_apref_profile Rs" "\<forall>R\<in>#Rs. R x y"
  shows   "x \<in> alts \<and> y \<in> alts"
proof -
  from assms have "Rs \<noteq> {#}"
    by (auto simp: is_apref_profile_def)
  then obtain R where R: "R \<in># Rs"
    by auto
  with assms interpret R: linorder_on alts R
    by (auto simp: is_apref_profile_def)
  from assms have "R x y"
    using R by auto
  with R.not_outside show ?thesis
    by blast
qed

lemma unanimous_topo_sorts_Pareto_aswf:
  assumes Rs: "is_apref_profile Rs"
  shows   "aswf Rs \<in> of_ranking ` topo_sorts alts (\<lambda>x y. \<forall>R\<in>#Rs. R x y)"
proof -
  obtain R where R: "is_pref_profile R" "Rs = image_mset R (mset_set agents)"
    using Rs deanonymised_profile_exists by blast
  interpret R: pref_profile_linorder_wf agents alts R
    by fact

  have "aswf Rs = swf R"
    using R aswf_welldefined by blast
  also have "swf R \<in> of_ranking ` topo_sorts alts (Pareto(R))"
    by (rule unanimous_topo_sort_Pareto) fact+
  also have "Pareto(R) = (\<lambda>x y. \<forall>R\<in>#Rs. R x y)"
    unfolding R(2) by (auto simp: R.Pareto_iff fun_eq_iff)
  finally show ?thesis .
qed

end


locale anonymous_kemeny_strategyproof_swf = 
  anonymous_swf agents alts swf +
  kemeny_strategyproof_swf agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf
begin

lemma kemeny_strategyproof_aswf:
  assumes "is_apref_profile R1" "is_apref_profile R2"
  assumes "size (R1 - R2) = 1"
  assumes "\<exists>R\<in>#(R1-R2). swap_dist_relation R S1 > swap_dist_relation R S2"
  shows   "aswf R1 \<noteq> S1 \<or> aswf R2 \<noteq> S2"
proof (rule ccontr)
  assume "\<not>(aswf R1 \<noteq> S1 \<or> aswf R2 \<noteq> S2)"
  hence S12: "aswf R1 = S1" "aswf R2 = S2"
    by auto

  from assms(1) obtain R1' where R1': "is_pref_profile R1'" "R1 = image_mset R1' (mset_set agents)"
    using deanonymised_profile_exists by blast
  from assms(2) obtain R2' where R2': "is_pref_profile R2'" "R2 = image_mset R2' (mset_set agents)"
    using deanonymised_profile_exists by blast

  from \<open>size (R1 - R2) = 1\<close> obtain R where R: "R1 - R2 = {#R#}"
    using size_1_singleton_mset[of "R1 - R2"] by auto
  have "R \<in># R1"
    using R by (metis in_diffD multi_member_last)
  obtain i where i: "i \<in> agents" "R = R1' i"
    using R unfolding R1'(2) R2'(2)
    by (metis (no_types, lifting) Multiset.diff_right_commute add_mset_diff_bothsides
        diff_single_trivial finite_agents finite_set_mset_mset_set imageE
        multi_self_add_other_not_self multiset.set_map zero_diff)

  obtain S where S: "R2 - R1 = {#S#}"
  proof -
    have "size (R2 - R1) = 1"
      by (rule size_Diff_mset_same_size)
         (use assms in \<open>auto simp: is_apref_profile_def\<close>)
    thus ?thesis
      using that size_1_singleton_mset by blast
  qed
  have "S \<in># R2"
    using S by (metis in_diffD multi_member_last)

  have "swap_dist_relation R S1 \<le> swap_dist_relation R S2"
  proof -
    have "swap_dist_relation (R1' i) (swf R1') \<le> swap_dist_relation (R1' i) (swf (R1'(i := S)))"
    proof (rule kemeny_strategyproof)
      from \<open>S \<in># R2\<close> and assms show "linorder_on alts S"
        by (auto simp: is_apref_profile_def)
    qed fact+
    also have "swf R1' = aswf R1"
      unfolding R1'(2) by (rule aswf_welldefined [symmetric]) fact
    also have "swf (R1'(i := S)) = aswf R2"
    proof -
      from \<open>S \<in># R2\<close> and assms have "linorder_on alts S"
        by (auto simp: is_apref_profile_def)
      hence "is_pref_profile (R1'(i := S))"
        by (intro is_pref_profile_update) (use R1'(1) i in auto)
      hence "aswf (image_mset (R1'(i := S)) (mset_set agents)) = swf (R1'(i := S))"
        by (rule aswf_welldefined)
      also have "mset_set agents = add_mset i (mset_set agents - {#i#})"
        using i by simp
      also have "image_mset (R1'(i := S)) \<dots> = 
                   {#S#} + image_mset (R1'(i := S)) (mset_set agents - {#i#})"
        by simp
      also have "mset_set agents - {#i#} = mset_set (agents - {i})"
        by (subst mset_set_Diff) (use i in auto)
      also have "image_mset (R1'(i := S)) (mset_set (agents - {i})) =
                 image_mset R1' (mset_set (agents - {i}))"
        by (intro image_mset_cong) auto
      also have "image_mset R1' (mset_set (agents - {i})) = image_mset R1' (mset_set agents - {#i#})"
        by (subst mset_set_Diff) (use i in auto)
      also have "\<dots> = R1 - {#R#}"
        by (subst image_mset_Diff) (use i in \<open>auto simp: R1'(2)\<close>)
      also have "{#S#} + (R1 - {#R#}) = R2"
      proof (rule multiset_eqI)
        fix T :: "'alt relation"
        have "count (R1 - R2) T = count {#R#} T"
          by (subst R) auto
        moreover have "count (R2 - R1) T = count {#S#} T"
          by (subst S) auto
        ultimately show "count ({#S#} + (R1 - {#R#})) T = count R2 T"
          by auto
      qed
      finally show ?thesis ..
    qed
    also have "aswf R1 = S1"
      by fact
    also have "aswf R2 = S2"
      by fact
    also have "R1' i = R"
      using i by simp
    finally show ?thesis .
  qed

  moreover have "swap_dist_relation R S1 > swap_dist_relation R S2"
    using \<open>\<exists>R\<in>#(R1-R2). swap_dist_relation R S1 > swap_dist_relation R S2\<close> unfolding R by simp
  ultimately show False
    by linarith
qed

lemma kemeny_strategyproof_aswf_strong:
  assumes "is_apref_profile R1" "is_apref_profile R2"
  assumes "size (R1 - R2) = 1"
  assumes "(\<exists>R\<in>#R1-R2. swap_dist_relation R S1 > swap_dist_relation R S2) \<or>
           (\<exists>R\<in>#R2-R1. swap_dist_relation R S2 > swap_dist_relation R S1)"
  shows   "aswf R1 \<noteq> S1 \<or> aswf R2 \<noteq> S2"
proof -
  have sz: "size (R2 - R1) = 1"
    by (rule size_Diff_mset_same_size)
       (use assms in \<open>auto simp: is_apref_profile_def\<close>)
  show ?thesis
    using kemeny_strategyproof_aswf[OF assms(1-3), of S2 S1]
          kemeny_strategyproof_aswf[OF assms(2,1) sz, of S1 S2] assms(4)
    by blast
qed

lemma kemeny_strategyproof_aswf':
  assumes "is_apref_profile' R1" "is_apref_profile' R2"
  assumes "size (R1 - R2) = 1"
  assumes "\<exists>R\<in>#(R1-R2). swap_dist R S1 > swap_dist R S2"
  shows   "aswf' R1 \<noteq> S1 \<or> aswf' R2 \<noteq> S2"
proof (rule ccontr)
  assume "\<not> (aswf' R1 \<noteq> S1 \<or> aswf' R2 \<noteq> S2)"
  hence S12: "aswf' R1 = S1" "aswf' R2 = S2"
    by blast+
  have S12_wf: "S1 \<in> permutations_of_set alts" "S2 \<in> permutations_of_set alts"
    using S12 aswf'_wf assms(1,2) by blast+
  have "inj_on of_ranking (permutations_of_set alts)"
    by (metis inj_on_inverseI permutations_of_setD(2) ranking_of_ranking)
  hence inj: "inj_on of_ranking (set_mset (R1 + R2))"
    by (rule inj_on_subset) (use assms(1,2) in \<open>auto simp: is_apref_profile'_def is_apref_profile_def\<close>)

  have "aswf (image_mset of_ranking R1) \<noteq> of_ranking S1 \<or> aswf (image_mset of_ranking R2) \<noteq> of_ranking S2"
  proof (rule kemeny_strategyproof_aswf)
    have "image_mset of_ranking R1 - image_mset of_ranking R2 = image_mset of_ranking (R1 - R2)"
      using inj by (rule image_mset_diff_if_inj_on [symmetric])
    also have "size \<dots> = 1"
      using assms by simp
    finally show "size (image_mset of_ranking R1 - image_mset of_ranking R2) = 1" .
  next
    from assms(4) obtain R where R: "R \<in># R1 - R2" "swap_dist R S1 > swap_dist R S2"
      by blast
    have "of_ranking R \<in># image_mset of_ranking (R1 - R2)"
      using R(1) by simp
    also have "image_mset of_ranking (R1 - R2) = image_mset of_ranking R1 - image_mset of_ranking R2"
      using inj by (rule image_mset_diff_if_inj_on)
    finally have R': "of_ranking R \<in># image_mset of_ranking R1 - image_mset of_ranking R2" .

    have "R \<in># R1"
      using R by (meson in_diffD)
    hence "R \<in> permutations_of_set alts"
      using R(1) assms(1) by (auto simp: is_apref_profile'_def)
    hence "swap_dist_relation (of_ranking R) (of_ranking S1) > swap_dist_relation (of_ranking R) (of_ranking S2)"
      using S12_wf R(2) by (simp add: swap_dist_def permutations_of_set_def)
    with R' show  "\<exists>R\<in>#image_mset of_ranking R1 - image_mset of_ranking R2.
                     swap_dist_relation R (of_ranking S2) < swap_dist_relation R (of_ranking S1)"
      by blast
  qed (use assms in \<open>auto intro!: is_apref_profile'_imp_is_apref_profile\<close>)

  hence "aswf' R1 \<noteq> S1 \<or> aswf' R2 \<noteq> S2"
    unfolding aswf'_def
    by (metis aswf_wf' assms(1,2)  finite_linorder_on.of_ranking_ranking
        is_apref_profile'_imp_is_apref_profile)
  with S12 show False
    by blast
qed

lemma kemeny_strategyproof_aswf'_strong:
  assumes "is_apref_profile' R1" "is_apref_profile' R2"
  assumes "size (R1 - R2) = 1"
  assumes "(\<exists>R\<in>#(R1-R2). swap_dist R S1 > swap_dist R S2) \<or>
           (\<exists>R\<in>#(R2-R1). swap_dist R S2 > swap_dist R S1)"
  shows   "aswf' R1 \<noteq> S1 \<or> aswf' R2 \<noteq> S2"
proof -
  have sz: "size (R2 - R1) = 1"
    by (rule size_Diff_mset_same_size)
       (use assms in \<open>auto simp: is_apref_profile'_def\<close>)
  show ?thesis
    using kemeny_strategyproof_aswf'[OF assms(1-3), of S2 S1]
          kemeny_strategyproof_aswf'[OF assms(2,1) sz, of S1 S2] assms(4)
    by blast
qed

text \<open>
  A consequence of strategyproofness: if a profile contains clones (i.e.\ it contains the same
  ranking $A$ multiple times) then simultaneous deviations by the clones may not result in a
  better outcome w.r.t.\ $A$.

  This is simply proven using a chain of $n$ successive single-agent deviations, each replacing
  one copy of $A$ with another ranking.
\<close>
lemma kemeny_strategyproof_aswf'_clones_aux:
  assumes "is_apref_profile' R1" "is_apref_profile' R2"
  assumes "R1 - R2 = replicate_mset n A"
  shows   "swap_dist A (aswf' R1) \<le> swap_dist A (aswf' R2)"
  using assms
proof (induction n arbitrary: R1)
  case 0
  hence "R1 - R2 = {#}"
    by auto
  moreover have "size R1 = size R2"
    using 0 by (auto simp: is_apref_profile'_def)
  ultimately have "R1 = R2"
    by (metis Diff_eq_empty_iff_mset cancel_comm_monoid_add_class.diff_cancel
        nonempty_has_size size_Diff_submset subset_mset.add_diff_inverse)
  thus ?case using 0 by auto
next
  case (Suc n R1)
  have "A \<in># R1"
    using Suc.prems(3) by (metis in_diffD in_replicate_mset zero_less_Suc)

  define X where "X = R2 - R1"
  have "size R1 = size R2"
    using Suc.prems by (auto simp: is_apref_profile'_def)
  have eq: "R1 + X = R2 + replicate_mset (Suc n) A"
    using Suc.prems(3) unfolding X_def
    by (metis add.commute diff_intersect_left_idem diff_subset_eq_self inter_mset_def
        subset_mset.diff_add_assoc2 union_diff_inter_eq_sup union_mset_def)
  
  define R0 where "R0 = R1 - replicate_mset (Suc n) A"
  have R1_eq: "R1 = R0 + replicate_mset (Suc n) A"
    using Suc.prems(3) unfolding R0_def by (metis diff_subset_eq_self subset_mset.diff_add)
  have R2_eq: "R2 = R0 + X"
    using eq unfolding R1_eq by simp

  have "size X = Suc n"
    by (metis \<open>size R1 = size R2\<close> add_diff_cancel_left' eq size_replicate_mset size_union)
  hence "X \<noteq> {#}"
    by auto
  then obtain B where B: "B \<in># X"
    by blast
  have B': "B \<in># R2"
    using B by (auto dest: in_diffD simp: X_def)
  define R1' where "R1' = R1 - {#A#} + {#B#}"
  have R1': "is_apref_profile' R1'"
    using Suc.prems(1,2) B \<open>A \<in># R1\<close> B'
    by (auto simp: is_apref_profile'_def R1'_def size_Suc_Diff1 dest: in_diffD)
  have "A \<noteq> B" using B Suc.prems(3)
    unfolding X_def by (metis in_diff_count in_replicate_mset not_less_iff_gr_or_eq zero_less_Suc)

  have "swap_dist A (aswf' R1) \<le> swap_dist A (aswf' R1')"
  proof -
    have diff_eq: "R1 - R1' = {#A#}"
      using B \<open>A \<in># R1\<close> \<open>A \<noteq> B\<close> unfolding R1'_def
      by (metis Multiset.diff_add add_diff_cancel_left' diff_union_swap insert_DiffM2 zero_diff)      
    show ?thesis
      by (cases "swap_dist A (aswf' R1) \<le> swap_dist A (aswf' R1')")
         (use kemeny_strategyproof_aswf'[of R1 R1' "aswf' R1'" "aswf' R1"] Suc.prems(1) R1'
          in  \<open>simp_all add: diff_eq not_le\<close>)
  qed
  also have "\<dots> \<le> swap_dist A (aswf' R2)"
  proof (rule Suc.IH)
    have "R1' - R2 = add_mset B (replicate_mset n A) - X"
      by (simp add: R1'_def R2_eq R1_eq)
    also have "\<dots> = replicate_mset n A - X"
      using \<open>A \<noteq> B\<close> \<open>B \<in># X\<close>
      by (metis add_mset_diff_bothsides in_replicate_mset insert_DiffM minus_add_mset_if_not_in_lhs)
    also have "A \<notin># X"
      by (metis Suc.prems(3) X_def in_diff_count not_less_iff_gr_or_eq replicate_mset_Suc
          union_single_eq_member)
    hence "replicate_mset n A - X = replicate_mset n A"
      by (induction n) auto
    finally show "R1' - R2 = replicate_mset n A" .
  qed fact+
  finally show ?case .
qed

lemma kemeny_strategyproof_aswf'_clones:
  assumes "is_apref_profile' R1" "is_apref_profile' R2"
  assumes "R1 - R2 = replicate_mset n A"
  assumes "swap_dist A S1 > swap_dist A S2"
  shows   "aswf' R1 \<noteq> S1 \<or> aswf' R2 \<noteq> S2"
  using kemeny_strategyproof_aswf'_clones_aux[OF assms(1-3)] assms(4) by auto


text \<open>
  Another consequence of Kemeny strategyproofness: if an agent gets a non-optimal result (i.e.\ the
  result ranking is not the ranking of the agent), no deviation of the agent can yield the optimal 
  result either.
\<close>
lemma kemeny_strategyproof_aswf'_no_obtain_optimal:
  assumes "is_apref_profile' R" "is_apref_profile' R'" "add_mset S R' = add_mset S' R"
  shows   "aswf' R = S \<or> aswf' R' \<noteq> S"
proof (rule ccontr)
  assume "\<not>(aswf' R = S \<or> aswf' R' \<noteq> S)"
  hence *:" aswf' R \<noteq> S" "aswf' R' = S"
    by auto
  have "S \<noteq> S'"
    using * assms(3) by auto

  have "aswf' R \<noteq> aswf' R \<or> aswf' R' \<noteq> S"
  proof (rule kemeny_strategyproof_aswf')
    show "size (R - R') = 1"
      using assms(3) \<open>S \<noteq> S'\<close> count_add_mset[of S R' S] in_diff_count[of S R R']
            size_Suc_Diff1[of S "R - R'"] by auto
  next
    have "S \<in># R - R'"
      using *  assms(3) by (metis add_eq_conv_ex count_add_mset in_diff_count lessI)
    hence "S \<in># R"
      by (meson in_diffD)
    hence "S \<in> permutations_of_set alts"
      using assms(1) by (auto simp: is_apref_profile'_def)
    hence "swap_dist S (aswf' R) > 0"
      by (subst swap_dist_pos_iff)
         (use * aswf'_wf[OF assms(1)] in \<open>auto simp: permutations_of_set_def\<close>)
    with \<open>S \<in># R - R'\<close> show "\<exists>T\<in>#R - R'. swap_dist T S < swap_dist T (aswf' R)"
      by (intro bexI[of _ S]) auto
  qed fact+
  with * show False
    by auto
qed

end


(* TODO: get rid of this? *)
text \<open>
  The following relation says that the given anonymised set of preferences \<open>Rs\<close> has a majority 
  relation that is a linear order, and this linear order is exactly the one described by
  the ranking \<open>S\<close>.
\<close>
definition majority_rel_mset :: "'a list multiset \<Rightarrow> 'a list \<Rightarrow> bool" where
  "majority_rel_mset Rs S \<longleftrightarrow>
     majority_mset (image_mset of_ranking Rs) = of_ranking S \<and> distinct S"


locale anonymous_majority_consistent_swf = 
  anonymous_swf agents alts swf +
  majority_consistent_swf agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf
begin

lemma majority_consistent_aswf:
  assumes "is_apref_profile Rs" "linorder_on alts (majority_mset Rs)"
  shows   "aswf Rs = majority_mset Rs"
proof -
  obtain R where R: "is_pref_profile R" "Rs = image_mset R (mset_set agents)"
    using assms(1) deanonymised_profile_exists by blast
  interpret R: pref_profile_linorder_wf agents alts R by fact
  have maj_eq: "majority R = majority_mset Rs"
    by (subst R.majority_conv_majority_mset) (use R in simp_all)

  have "aswf Rs = swf R"
    using R aswf_welldefined by blast
  also have "\<dots> = majority R"
    by (rule majority_consistent) (use assms(2) R(1) maj_eq in simp_all)
  also have "\<dots> = majority_mset Rs"
    by fact
  finally show "aswf Rs = majority_mset Rs" .
qed

lemma majority_consistent_aswf':
  assumes "is_apref_profile' Rs" "majority_rel_mset Rs S"
  shows   "aswf' Rs = S"
proof -
  define Rs' where "Rs' = image_mset of_ranking Rs"
  define S' where "S' = of_ranking S"
  have "is_apref_profile Rs'"
    using assms(1) unfolding Rs'_def by (simp add: is_apref_profile'_imp_is_apref_profile)
  have "S' = majority_mset Rs'"
    using assms(2) unfolding majority_rel_mset_def by (auto simp: Rs'_def S'_def)
  have "distinct S"
    using assms(2) by (auto simp: majority_rel_mset_def)
  have "linorder_on alts S'"
  proof -
    have Rs'_wf: "\<And>R. R \<in># Rs' \<Longrightarrow> preorder_on alts R" "Rs' \<noteq> {#}"
      using \<open>is_apref_profile Rs'\<close> unfolding is_apref_profile_def
      using linorder_on_def order_on_def by fastforce+
    have "set S = alts"
    proof (rule set_eqI)
      fix x
      have "x \<in> set S \<longleftrightarrow> of_ranking S x x"
        by (metis of_ranking_imp_in_set(2) of_ranking_refl)
      also have "\<dots> \<longleftrightarrow> majority_mset Rs' x x"
        using assms(2) by (simp add: majority_rel_mset_def Rs'_def)
      also have "\<dots> \<longleftrightarrow> x \<in> alts"
        by (rule majority_mset_refl_iff) (use Rs'_wf in auto)
      finally show "x \<in> set S \<longleftrightarrow> x \<in> alts" .
    qed
    thus ?thesis
      unfolding S'_def using \<open>distinct S\<close> by (intro linorder_of_ranking)
  qed

  have "aswf' Rs = ranking (aswf Rs')"
    by (simp add: aswf'_def Rs'_def)
  also have "aswf Rs' = majority_mset Rs'"
    by (rule majority_consistent_aswf)
       (use \<open>is_apref_profile Rs'\<close> \<open>linorder_on alts S'\<close> \<open>S' = majority_mset Rs'\<close> in simp_all)
  also have "\<dots> = S'"
    by (rule sym) fact
  also have "ranking S' = S"
    using \<open>distinct S\<close> by (simp add: S'_def ranking_of_ranking)
  finally show ?thesis .
qed
  
end

end