subsection \<open>Lowering constructions for SWFs\<close>
theory SWF_Lowering
  imports SWF_Explicit
begin

text \<open>
  In this section, we will give constructions that turn an SWF for some number of alternatives
  into an SWF for fewer alternatives and agents.

  Concretely:

    \<^item> We can create an SWF for fewer alternatives by simply adding the missing alternatives
      at the very and of all the agents' rankings in some fixed orders. However, this only works
      if the SWF is unanimous, so that the dummy alternatives are guaranteed to be at the very
      end of the output ranking.

    \<^item> If the number of agents is $n = kn'$ for some $k > 0$, we can create an SWF for $n'$
      agents by simply cloning every agent in the input profile $k$ times.

  These constructions preserve anonymity, unanimity, and Kemeny-strategyproofness.
\<close>

subsubsection \<open>Decreasing the number of alternatives\<close>

locale swf_restrict_alts = social_welfare_function agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf +
  fixes dummy_alts alts'
  assumes alts'_nonempty: "alts' \<noteq> {}" and finite_alts': "finite alts'"
  assumes dummy_alts_alts': "mset_set alts = mset dummy_alts + mset_set alts'"
begin

lemma alts': "alts' \<subseteq> alts" "alts' \<noteq> {}"
proof -
  show "alts' \<subseteq> alts" using dummy_alts_alts'
    by (metis finite_alts finite_alts' mset_subset_eq_add_right msubset_mset_set_iff)
  show "alts' \<noteq> {}"
    by (rule alts'_nonempty)
qed

sublocale new: linorder_election agents alts'
  by standard (use alts' finite_subset[OF _ finite_alts] in auto)

lemma dummy_alts: "distinct dummy_alts" "set dummy_alts = alts - alts'"
proof -
  show "distinct dummy_alts" using dummy_alts_alts'
    by (metis add_diff_cancel_right' alts'(1) finite_Diff
        finite_alts mset_eq_mset_set_iff mset_set_Diff permutations_of_setD(2))
  show "set dummy_alts = alts - alts'"
    by (metis add_diff_cancel_right' alts'(1) dummy_alts_alts' finite_Diff2 finite_alts finite_alts'
        finite_set_mset_mset_set mset_set_Diff set_mset_mset)
qed


text \<open>
  The following lifts a ranking on the smaller set of alternatives to the full set, by adding
  the dummy alternatives at the end in the order we fixed.
\<close>
definition extend_ranking :: "'alt relation \<Rightarrow> 'alt relation" where
  "extend_ranking R =
     (\<lambda>x y. R x y \<or> of_ranking dummy_alts x y \<or> x \<in> alts - alts' \<and> y \<in> alts')"

lemma linorder_on_extend_ranking:
  assumes "linorder_on alts' R"
  shows   "linorder_on alts (extend_ranking R)"
proof -
  interpret R: linorder_on alts' R
    by fact
  have "linorder_on ((alts - alts') \<union> alts') 
          (\<lambda>x y. if x \<in> alts - alts' then of_ranking dummy_alts x y \<or> y \<in> alts' else R x y)"
  proof (rule linorder_on_concat)
    show "linorder_on (alts - alts') (of_ranking dummy_alts)"
      by (rule linorder_of_ranking) (use dummy_alts in auto)
  qed (use assms in auto)
  also have "\<dots> = extend_ranking R"
    using R.not_outside of_ranking_imp_in_set[of dummy_alts] dummy_alts
    by (auto simp: extend_ranking_def fun_eq_iff)
  also have "(alts - alts') \<union> alts' = alts"
    using alts' by auto
  finally show ?thesis .
qed  

lemma restrict_extend_ranking:
  assumes "linorder_on alts' R"
  shows   "restrict_relation alts' (extend_ranking R) = R"
proof -
  interpret R: linorder_on alts' R
    by fact
  show ?thesis
    using alts' R.not_outside of_ranking_imp_in_set[of dummy_alts] dummy_alts
    unfolding restrict_relation_def extend_ranking_def fun_eq_iff by auto
qed

lemma swap_dist_extend_ranking:
  assumes "linorder_on alts' R" "linorder_on alts' S"
  shows   "swap_dist_relation (extend_ranking R) (extend_ranking S) = swap_dist_relation R S"
proof -
  interpret R: linorder_on alts' R by fact
  have "swap_dist_relation_aux (extend_ranking R) (extend_ranking S) = swap_dist_relation_aux R S"
    unfolding swap_dist_relation_aux_def extend_ranking_def
    using R.not_outside of_ranking_imp_in_set[of dummy_alts] dummy_alts by fast
  thus ?thesis
    by (simp add: swap_dist_relation_def)
qed

lemma extend_ranking_eq_iff:
  assumes "\<And>x y. R x y \<Longrightarrow> x \<in> alts' \<and> y \<in> alts'" "\<And>x y. S x y \<Longrightarrow> x \<in> alts' \<and> y \<in> alts'"
  shows   "extend_ranking R = extend_ranking S \<longleftrightarrow> R = S"
  using of_ranking_imp_in_set[of dummy_alts] dummy_alts alts' assms
  unfolding extend_ranking_def fun_eq_iff by blast

text \<open>
  We extend a profile to the full set of alternatives by extending each ranking.
\<close>
definition extend_profile :: "('agent \<Rightarrow> 'alt relation) \<Rightarrow> 'agent \<Rightarrow> 'alt relation" where
  "extend_profile R i = (\<lambda>x y. i \<in> agents \<and> extend_ranking (R i) x y)"

lemma is_pref_profile_extend [intro]:
  assumes "new.is_pref_profile R"
  shows   "is_pref_profile (extend_profile R)"
proof
  fix i assume i: "i \<in> agents"
  interpret R: pref_profile_linorder_wf agents alts' R
    by fact
  have "linorder_on alts (extend_ranking (R i))"
    using i by (simp add: linorder_on_extend_ranking)
  thus "linorder_on alts (extend_profile R i)"
    using i by (simp add: extend_profile_def)
qed (auto simp: extend_profile_def)

lemma count_extend_ranking_multiset:
  assumes "\<And>R. R \<in># Rs \<Longrightarrow> linorder_on alts' R" and xy: "x \<in> alts" "y \<in> alts"
  shows   "size {#R\<in>#Rs. extend_ranking R x y#} =
           (if x \<in> alts' \<and> y \<in> alts' then size {#R\<in>#Rs. R x y#}
            else if x \<notin> alts' \<and> (y \<in> alts' \<or> of_ranking dummy_alts x y) then size Rs else 0)"
proof -
  have *: "x \<in> alts' \<and> y \<in> alts'" if "R x y" "R \<in># Rs" for R
  proof -
    interpret linorder_on alts' R
      using assms(1) that by blast
    show ?thesis
      using not_outside[OF that(1)] by auto
  qed
  have **: "x \<in> alts - alts' \<and> y \<in> alts - alts'" if "of_ranking dummy_alts x y"
    using of_ranking_imp_in_set[OF that] dummy_alts by simp

  have "{#R\<in>#Rs. extend_ranking R x y#} =
             (if x \<in> alts' \<and> y \<in> alts' then
                {#R\<in>#Rs. R x y#}
              else if x \<notin> alts' \<and> (y \<in> alts' \<or> of_ranking dummy_alts x y) then Rs else {#})"
    unfolding extend_ranking_def 
    using xy alts' by (auto intro!: filter_mset_cong simp: filter_mset_empty_conv dest: * **)
  also have "size \<dots> = (if x \<in> alts' \<and> y \<in> alts' then size {#R\<in>#Rs. R x y#}
                        else if x \<notin> alts' \<and> (y \<in> alts' \<or> of_ranking dummy_alts x y) then size Rs else 0)"
    by simp
  finally show ?thesis .
qed

lemma count_extend_profile:
  assumes "new.is_pref_profile R" and xy: "x \<in> alts" "y \<in> alts"
  shows   "card {i\<in>agents. extend_profile R i x y} =
           (if x \<in> alts' \<and> y \<in> alts' then card {i\<in>agents. R i x y}
            else if x \<notin> alts' \<and> (y \<in> alts' \<or> of_ranking dummy_alts x y) then card agents else 0)"
proof -
  interpret R: pref_profile_linorder_wf agents alts' R by fact
  have "card {i\<in>agents. extend_profile R i x y} =
          (card {i\<in>agents. extend_ranking (R i) x y})"
    using xy by (simp add: extend_profile_def extend_ranking_def)
  also have "{i\<in>agents. extend_ranking (R i) x y} =
             (if x \<in> alts' \<and> y \<in> alts' then
                {i\<in>agents. R i x y}
              else if x \<notin> alts' \<and> (y \<in> alts' \<or> of_ranking dummy_alts x y) then agents else {})"
    unfolding extend_ranking_def 
    using xy alts' dummy_alts of_ranking_imp_in_set[of dummy_alts x y] R.not_outside(2,3)[of _ x y]
    by force
  also have "card \<dots> = (if x \<in> alts' \<and> y \<in> alts' then card {i\<in>agents. R i x y}
                        else if x \<notin> alts' \<and> (y \<in> alts' \<or> of_ranking dummy_alts x y) then card agents else 0)"
    by simp
  finally show ?thesis .
qed

lemma majority_extend_profile:
  assumes "new.is_pref_profile R"
  shows   "majority (extend_profile R) = extend_ranking (majority R)"
proof (intro ext)
  fix x y
  interpret R: pref_profile_linorder_wf agents alts' R by fact
  interpret R': pref_profile_linorder_wf agents alts "extend_profile R"
    using assms(1) by auto
  show "majority (extend_profile R) x y = extend_ranking (majority R) x y"
  proof (cases "x \<in> alts \<and> y \<in> alts")
    case xy: True
    show ?thesis
      using xy assms(1) dummy_alts of_ranking_imp_in_set[of dummy_alts x y] R.not_outside(2,3)[of _ x y]
            of_ranking_imp_in_set[of dummy_alts y x] of_ranking_total[of x dummy_alts y]
      by (auto simp: R'.majority_iff' R.majority_iff' count_extend_profile card_gt_0_iff extend_ranking_def)
  next
    case False
    thus ?thesis using alts' dummy_alts of_ranking_imp_in_set[of dummy_alts x y]
      by (auto simp: R'.majority_iff' extend_ranking_def R.majority_iff')
  qed
qed

lemma majority_mset_extend_profile:
  assumes "\<And>R. R \<in># Rs \<Longrightarrow> linorder_on alts' R" "Rs \<noteq> {#}"
  shows   "majority_mset (image_mset extend_ranking Rs) = extend_ranking (majority_mset Rs)"
proof (intro ext)
  fix x y
  have linorder: "linorder_on alts (extend_ranking R)" if "R \<in># Rs" for R
    using assms(1)[OF that] by (rule linorder_on_extend_ranking)
  have *: "x \<in> alts' \<and> y \<in> alts'" if "majority_mset Rs x y"
    using assms by (meson linorder_on_def majority_mset_not_outside order_on_def that)
  have **: "x \<in> alts - alts' \<and> y \<in> alts - alts'" if "of_ranking dummy_alts x y"
    using of_ranking_imp_in_set[OF that] dummy_alts by simp

  show "majority_mset (image_mset extend_ranking Rs) x y = extend_ranking (majority_mset Rs) x y"
  proof (cases "x \<in> alts \<and> y \<in> alts")
    case xy: True
    have "majority_mset (image_mset extend_ranking Rs) x y \<longleftrightarrow> 
            2 * size {#R \<in># Rs. extend_ranking R x y#} \<ge> size Rs"
      by (subst majority_mset_iff_ge[of _ alts] *)
         (use linorder \<open>Rs \<noteq> {#}\<close> xy in \<open>auto simp: linorder_on_def order_on_def filter_mset_image_mset\<close>)
    also have "\<dots> = extend_ranking (majority_mset Rs) x y"
      by (subst count_extend_ranking_multiset) 
         (use assms xy in \<open>auto simp: extend_ranking_def majority_mset_iff_ge[of _ alts'] dest: * **\<close>)
    finally show ?thesis .
  next
    case xy: False
    have "\<not>majority_mset (image_mset extend_ranking Rs) x y"
      using majority_mset_not_outside[of "image_mset extend_ranking Rs" x y alts] xy linorder
      using linorder_on_def total_preorder_on.axioms(1) by fastforce
    moreover have "\<not>extend_ranking (majority_mset Rs) x y"
      using xy alts' by (auto simp: extend_ranking_def dest: * **)
    ultimately show ?thesis
      by simp
  qed
qed


text \<open>
  We define our new SWF on the full set of alternatives by extending the input profile and
  removing the extra alternatives from the output ranking.
\<close>
definition swf_low :: "('agent \<Rightarrow> 'alt relation) \<Rightarrow> 'alt relation" where
  "swf_low R = restrict_relation alts' (swf (extend_profile R))"

sublocale new: social_welfare_function agents alts' swf_low
proof
  fix R assume "new.is_pref_profile R"
  then interpret swf: linorder_on alts "swf (extend_profile R)"
    using is_pref_profile_extend swf_wf by blast
  show "linorder_on alts' (swf_low R)"
    unfolding swf_low_def by (rule swf.linorder_on_restrict_subset) (fact alts')
qed


text \<open>
  Our construction preserves anonymity, unanimity, and Kemeny-strategyproofness.
\<close>
lemma anonymous_restrict:
  assumes "anonymous_swf agents alts swf"
  shows   "anonymous_swf agents alts' swf_low"
proof
  interpret anonymous_swf agents alts swf
    by fact
  fix \<pi> R
  assume \<pi>: "\<pi> permutes agents" and R: "new.is_pref_profile R"
  have "swf_low (R \<circ> \<pi>) = restrict_relation alts' (swf (extend_profile (R \<circ> \<pi>)))"
    by (simp add: swf_low_def)
  also have "extend_profile (R \<circ> \<pi>) = extend_profile R \<circ> \<pi>"
    using permutes_in_image[OF \<pi>] by (simp add: extend_profile_def fun_eq_iff)
  also have "swf \<dots> = swf (extend_profile R)"
    by (rule anonymous) (use \<pi> R in auto)
  also have "restrict_relation alts' \<dots> = swf_low R"
    by (simp add: swf_low_def)
  finally show "swf_low (R \<circ> \<pi>) = swf_low R" .
qed

lemma unanimous_restrict:
  assumes "unanimous_swf agents alts swf"
  shows   "unanimous_swf agents alts' swf_low"
proof
  interpret unanimous_swf agents alts swf
    by fact
  fix R x y
  assume R: "new.is_pref_profile R" and xy: "\<forall>i\<in>agents. y \<prec>[R i] x"
  from R xy have xy': "x \<in> alts' \<and> y \<in> alts'"
    by (metis equals0I nonempty_agents pref_profile_linorder_wf.not_outside(2,3) 
              strongly_preferred_def)
  have "y \<prec>[swf (extend_profile R)] x"
    by (rule unanimous)
       (use R xy xy' of_ranking_imp_in_set[of dummy_alts] dummy_alts 
        in  \<open>auto simp: extend_profile_def extend_ranking_def strongly_preferred_def\<close>)
  thus "y \<prec>[swf_low R] x"
    unfolding swf_low_def using xy' by (auto simp: restrict_relation_def strongly_preferred_def)
qed


lemma majority_consistent_restrict:
  assumes "majority_consistent_swf agents alts swf"
  shows   "majority_consistent_swf agents alts' swf_low"
proof
  fix R assume R: "new.is_pref_profile R" "linorder_on alts' (majority R)"
  interpret majority_consistent_swf agents alts swf by fact
  have "swf_low R = restrict_relation alts' (swf (extend_profile R))"
    by (simp add: swf_low_def)
  also have "swf (extend_profile R) = majority (extend_profile R)"
    by (rule majority_consistent) 
       (use R in \<open>auto simp: majority_extend_profile linorder_on_extend_ranking\<close>)
  also have "\<dots> = extend_ranking (majority R)"
    by (rule majority_extend_profile) fact
  also have "restrict_relation alts' (extend_ranking (majority R)) = majority R"
    by (rule restrict_extend_ranking) fact
  finally show "swf_low R = majority R" .
qed

end


locale unanimous_swf_restrict_alts =
  swf_restrict_alts agents alts swf dummy_alts alts' +
  unanimous_swf agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf dummy_alts alts'
begin

sublocale new: unanimous_swf agents alts' swf_low
  by (rule unanimous_restrict) unfold_locales

lemma swf_dummy_alts_least_preferred:
  assumes "new.is_pref_profile R" "x \<in> alts'" "y \<in> alts - alts'"
  shows   "x \<succ>[swf (extend_profile R)] y"
proof (rule unanimous)
  interpret R: pref_profile_linorder_wf agents alts' R
    by fact
  show "\<forall>i\<in>agents. x \<succ>[extend_profile R i] y"
    using assms(2,3) alts' R.not_outside(3) of_ranking_imp_in_set[of dummy_alts] dummy_alts
    by (auto simp: extend_profile_def extend_ranking_def strongly_preferred_def)
qed (use assms in auto)


lemma swf_strongly_preferred_dummy_alts:
  assumes "new.is_pref_profile R" "x \<in> alts - alts'" "y \<in> alts - alts'"
  assumes "x \<succ>[of_ranking dummy_alts] y"
  shows   "x \<succ>[swf (extend_profile R)] y"
proof (rule unanimous)
  interpret R: pref_profile_linorder_wf agents alts'
    by fact
  show "\<forall>i\<in>agents. y \<prec>[extend_profile R i] x"
    using assms(2-) R.not_outside(3)
    by (auto simp: strongly_preferred_def extend_profile_def extend_ranking_def)
qed (use assms(1) in auto)

lemma swf_preferred_dummy_alts_iff:
  assumes "new.is_pref_profile R" "x \<in> alts - alts'" "y \<in> alts - alts'"
  shows "x \<succeq>[of_ranking dummy_alts] y \<longleftrightarrow> x \<succeq>[swf (extend_profile R)] y"
proof -
  interpret dummy_alts: linorder_on "alts - alts'" "of_ranking dummy_alts"
    by (rule linorder_of_ranking) (use dummy_alts in auto)
  interpret res: linorder_on alts "swf (extend_profile R)"
    by (rule swf_wf) (use assms(1) in auto)
  show ?thesis
    using swf_strongly_preferred_dummy_alts[OF assms(1-3)]
          swf_strongly_preferred_dummy_alts[OF assms(1,3,2)]
          dummy_alts.total res.total dummy_alts.antisymmetric res.antisymmetric assms(2,3)
    unfolding strongly_preferred_def by blast
qed

lemma swf_strongly_preferred_dummy_alts_iff:
  assumes "new.is_pref_profile R" "x \<in> alts - alts'" "y \<in> alts - alts'"
  shows   "x \<succ>[swf (extend_profile R)] y \<longleftrightarrow> x \<succ>[of_ranking dummy_alts] y"
proof -
  interpret dummy_alts: linorder_on "alts - alts'" "of_ranking dummy_alts"
    by (rule linorder_of_ranking) (use dummy_alts in auto)
  interpret res: linorder_on alts "swf (extend_profile R)"
    by (rule swf_wf) (use assms(1) in auto)
  show ?thesis
    using swf_strongly_preferred_dummy_alts[OF assms(1-3)]
          swf_strongly_preferred_dummy_alts[OF assms(1,3,2)]
          dummy_alts.total res.total dummy_alts.antisymmetric res.antisymmetric assms(2,3)
    unfolding strongly_preferred_def by blast
qed

lemma extend_ranking_swf_low:
  assumes "new.is_pref_profile R"
  shows   "extend_ranking (swf_low R) = swf (extend_profile R)"
proof -
  interpret lhs: linorder_on alts "extend_ranking (swf_low R)"
    using assms by (intro linorder_on_extend_ranking new.swf_wf)
  interpret rhs: linorder_on alts "swf (extend_profile R)"
    by (rule swf_wf) (use assms in auto)

  have "extend_ranking (swf_low R) x y \<longleftrightarrow> swf (extend_profile R) x y" 
    if "x \<in> alts" "y \<in> alts" for x y
  proof (cases "x \<in> alts'"; cases "y \<in> alts'")
    assume "x \<in> alts'" "y \<in> alts'"
    thus ?thesis using of_ranking_imp_in_set[of dummy_alts x y] dummy_alts
      by (auto simp: swf_low_def restrict_relation_def extend_ranking_def)
  next
    assume "x \<in> alts'" "y \<notin> alts'"
    thus ?thesis
      using that of_ranking_imp_in_set[of dummy_alts x y] dummy_alts 
            swf_dummy_alts_least_preferred[of R x y] assms
      by (auto simp: swf_low_def restrict_relation_def extend_ranking_def strongly_preferred_def)
  next
    assume "x \<notin> alts'" "y \<in> alts'"
    thus ?thesis
      using that swf_dummy_alts_least_preferred[of R y x] assms
      by (auto simp: swf_low_def restrict_relation_def extend_ranking_def strongly_preferred_def)
  next
    assume "x \<notin> alts'" "y \<notin> alts'"
    thus ?thesis using that swf_preferred_dummy_alts_iff[OF assms]
      by (auto simp: swf_low_def restrict_relation_def extend_ranking_def )
  qed
  thus ?thesis
    using lhs.not_outside rhs.not_outside unfolding fun_eq_iff by blast
qed

lemma kemeny_strategyproof_restrict:
  assumes "kemeny_strategyproof_swf agents alts swf"
  shows   "kemeny_strategyproof_swf agents alts' swf_low"
proof
  interpret kemeny_strategyproof_swf agents alts swf
    by fact
  fix R i S
  assume R: "new.is_pref_profile R" and i: "i \<in> agents" and S: "linorder_on alts' S"
  define R' where "R' = extend_profile R"
  define S' where "S' = extend_ranking S"

  interpret R: pref_profile_linorder_wf agents alts' R
    by fact
  interpret Ri: linorder_on alts' "R i"
    using i by simp

  have "swap_dist_relation (R i) (swf_low R) = swap_dist_relation (R' i) (swf R')"
  proof -
    have "swap_dist_relation (R i) (swf_low R) = 
          swap_dist_relation (extend_ranking (R i)) (extend_ranking (swf_low R))"
      by (rule swap_dist_extend_ranking [symmetric])
         (use R Ri.linorder_on_axioms in \<open>auto intro: new.swf_wf\<close>)
    also have "extend_ranking (R i) = R' i"
      using i by (simp add: R'_def extend_profile_def)
    also have "extend_ranking (swf_low R) = swf R'"
      by (subst extend_ranking_swf_low) (use R in \<open>simp_all add: R'_def\<close>)
    finally show "swap_dist_relation (R i) (swf_low R) = swap_dist_relation (R' i) (swf R')" .
  qed

  also have "swap_dist_relation (R' i) (swf R') \<le> swap_dist_relation (R' i) (swf (R'(i := S')))"
    by (rule kemeny_strategyproof)
       (use R S i in \<open>auto simp: R'_def S'_def linorder_on_extend_ranking\<close>)
  also have "swap_dist_relation (R' i) (swf (R'(i := S'))) =
             swap_dist_relation (R i) (swf_low (R(i := S)))"
  proof -
    have "swap_dist_relation (R i) (swf_low (R(i := S))) =
            swap_dist_relation (extend_ranking (R i)) (extend_ranking (swf_low (R(i := S))))"
      by (rule swap_dist_extend_ranking [symmetric])
         (use R S Ri.linorder_on_axioms i in \<open>auto intro: new.swf_wf\<close>)    
    also have "extend_ranking (R i) = R' i"
      using i by (simp add: R'_def extend_profile_def)
    also have "extend_ranking (swf_low (R(i := S))) = swf (extend_profile (R(i := S)))"
      by (subst extend_ranking_swf_low) (use R S i in auto)
    also have "extend_profile (R(i := S)) = R'(i := S')"
      using i unfolding R'_def S'_def extend_profile_def by (auto simp: fun_eq_iff)
    finally show "swap_dist_relation (R' i) (swf (R'(i := S'))) = 
                  swap_dist_relation (R i) (swf_low (R(i := S)))" ..
  qed
  finally show "swap_dist_relation (R i) (swf_low R) \<le> swap_dist_relation (R i) (swf_low (R(i := S)))" .
qed

end


locale majority_consistent_weak_kstratproof_swf_restrict_alts =
  majority_consistent_weak_kstratproof_swf agents alts swf +
  swf_restrict_alts  agents alts swf dummy_alts alts'
  for agents :: "'agent set" and alts :: "'alt set" and swf dummy_alts alts'
begin

sublocale new: majority_consistent_swf agents alts' swf_low
  by (rule majority_consistent_restrict) unfold_locales

sublocale new: majority_consistent_weak_kstratproof_swf agents alts' swf_low
proof
  fix R i S
  assume R: "new.is_pref_profile R" and i: "i \<in> agents" and S: "linorder_on alts' S"
  assume maj: "linorder_on alts' (majority (R(i := S)))"
  define R' where "R' = extend_profile R"
  define S' where "S' = extend_ranking S"
  interpret R: pref_profile_linorder_wf agents alts' R by fact
  interpret Ri: finite_linorder_on alts' "R i"
    using i by simp

  have maj': "linorder_on alts (majority (R'(i := S')))"
  proof -
    have "linorder_on alts (extend_ranking (majority (R(i := S))))"
      by (intro linorder_on_extend_ranking maj)
    also have "extend_ranking (majority (R(i := S))) = majority (extend_profile (R(i := S)))"
      by (rule majority_extend_profile [symmetric]) (use R i S in auto)
    also have "extend_profile (R(i := S)) = R'(i := S')"
      unfolding R'_def S'_def using i by (auto simp: extend_profile_def fun_eq_iff)
    finally show "linorder_on alts (majority (R'(i := S')))" .
  qed

  have "swap_dist_relation (R i) (swf_low R) = 
          swap_dist_relation (R i) (restrict_relation alts' (swf R'))"
    by (simp add: swf_low_def R'_def)
  also have "\<dots> = swap_dist_relation (restrict_relation alts' (R' i)) (restrict_relation alts' (swf R'))"
    using i Ri.linorder_on_axioms
    by (simp add: R'_def extend_profile_def restrict_extend_ranking)
  also have "\<dots> \<le> swap_dist_relation (R' i) (swf R')"
  proof (rule swap_dist_relation_restrict)
    show "linorder_on alts (R' i)"
      by (metis R R'_def i is_pref_profile_extend pref_profile_linorder_wf.prefs_wf')
  qed (use R in \<open>auto intro!: swf_wf simp: R'_def\<close>)
  also have "\<dots> \<le> swap_dist_relation (R' i) (majority (R'(i := S')))"
    by (rule majority_consistent_kemeny_strategyproof)
       (use R i S maj' in \<open>auto simp: R'_def S'_def linorder_on_extend_ranking\<close>)
  also have "R'(i := S') = extend_profile (R(i := S))"
    using i by (auto simp: S'_def R'_def extend_profile_def)
  also have "majority \<dots> = extend_ranking (majority (R(i := S)))"
    by (rule majority_extend_profile) (use R i S in auto)
  also have "R' i = extend_ranking (R i)"
    using i by (auto simp: R'_def extend_profile_def fun_eq_iff)
  also have "swap_dist_relation (extend_ranking (R i)) (extend_ranking (majority (R(i := S)))) =
             swap_dist_relation (R i) (majority (R(i := S)))"
    by (rule swap_dist_extend_ranking) (use R i S maj in auto)
  finally show "swap_dist_relation (R i) (swf_low R) \<le> 
                swap_dist_relation (R i) (majority (R(i := S)))" .
qed

end


locale swf_restrict_alts_explicit =
  swf_restrict_alts agents alts swf dummy_alts alts' +
  social_welfare_function_explicit agents alts swf agents_list alts_list
  for agents :: "'agent set" and alts :: "'alt set" 
  and swf dummy_alts alts' agents_list alts_list alts_list' +
  assumes alts_list_expand: "alts_list = alts_list' @ dummy_alts"
begin

lemma mset_alts_list: "mset alts_list = mset alts_list' + mset dummy_alts"
  by (simp add: alts_list_expand)

sublocale new: social_welfare_function_explicit agents alts' swf_low agents_list alts_list'
proof
  show "mset alts_list' = mset_set alts'"
    using alts_list dummy_alts_alts' mset_alts_list by auto
qed (fact agents_list)

definition extend :: "'alt list \<Rightarrow> 'alt list" where "extend = (\<lambda>xs. xs @ dummy_alts)"

lemma distinct_alts_list': "distinct alts_list'" 
  and alts_list'_not_in_dummy_alts: "set alts_list' \<inter> set dummy_alts = {}"
  using distinct_alts_list unfolding alts_list_expand by auto

lemma wf_extend:
  assumes "new.prefs_from_rankings_wf R"
  shows   "prefs_from_rankings_wf (map extend R)"
  using assms unfolding new.prefs_from_rankings_wf_def prefs_from_rankings_wf_def extend_def
  by (auto simp: list.pred_set mset_alts_list)

lemma of_ranking_extend:
  assumes "mset xs = mset alts_list'"
  shows   "of_ranking (extend xs) = extend_ranking (of_ranking xs)"
  unfolding extend_def of_ranking_append extend_ranking_def fun_eq_iff
  unfolding alts_conv_alts_list alts_list_expand 
  using alts_list'_not_in_dummy_alts new.mset_eq_alts_list_iff[of xs] assms new.alts_conv_alts_list
  by auto

lemma swap_dist_extend: 
  assumes "mset xs = mset alts_list'" "mset ys = mset alts_list'"
  shows   "swap_dist (extend xs) (extend ys) = swap_dist xs ys"
proof -
  have *: "distinct xs \<and> set xs = alts' \<and> distinct ys \<and> set ys = alts'"
    using assms by (metis new.mset_eq_alts_list_iff)
  show ?thesis unfolding extend_def
    by (rule swap_dist_append_right) (use * dummy_alts alts_list'_not_in_dummy_alts in auto)
qed

lemma prefs_from_rankings_extend:
  assumes R: "new.prefs_from_rankings_wf R"
  shows   "prefs_from_rankings (map extend R) = extend_profile (new.prefs_from_rankings R)"
  (is "?lhs = ?rhs")
proof
  fix i
  note R' = wf_extend[OF R]
  show "?lhs i = ?rhs i"
  proof (cases "i \<in> agents")
    case True
    then obtain j where j: "j < card agents" "i = agents_list ! j"
      by (metis agents_conv_agents_list card_agents index_less_size_conv nth_index)
    show ?thesis
      using j(1) new.prefs_from_rankings_nth[OF R, of j] prefs_from_rankings_nth[OF R', of j] R True
      unfolding j(2)
      by (simp add: extend_profile_def new.prefs_from_rankings_wf_def of_ranking_extend list.pred_set)
  qed (auto simp: extend_profile_def prefs_from_rankings_outside)
qed

lemma majority_rel_mset_extend:
  assumes R: "new.prefs_from_rankings_wf R" and S: "mset S = mset alts_list'"
  shows "majority_rel_mset (mset (map extend R)) (extend S) \<longleftrightarrow> majority_rel_mset (mset R) S"
proof -
  have S': "distinct S \<and> set S = alts'" using S unfolding extend_def
    by (metis new.mset_eq_alts_list_iff)
  have "majority_rel_mset (mset (map extend R)) (extend S) \<longleftrightarrow> 
          (majority_mset (image_mset (of_ranking \<circ> extend) (mset R)) = of_ranking (extend S) \<and>
           distinct (extend S))"
    by (simp add: majority_rel_mset_def image_mset.compositionality)
  also have "distinct (extend S) \<longleftrightarrow> distinct S"
    using S' alts_list'_not_in_dummy_alts dummy_alts by (auto simp: extend_def)
  also have "of_ranking (extend S) = extend_ranking (of_ranking S)"
    by (rule of_ranking_extend) (use S in simp_all)
  also have "image_mset (of_ranking \<circ> extend) (mset R) =
             image_mset (extend_ranking \<circ> of_ranking) (mset R)" unfolding o_def
    by (intro image_mset_cong of_ranking_extend)
       (use R in \<open>auto simp: new.prefs_from_rankings_wf_def list.pred_set\<close>)
  also have "\<dots> = image_mset extend_ranking (image_mset of_ranking (mset R))"
    by (simp add: image_mset.compositionality o_def)
  also have "majority_mset \<dots> = extend_ranking (majority_mset (image_mset of_ranking (mset R)))"
  proof -
    have [simp]: "R \<noteq> []"
      using R by (auto simp: new.prefs_from_rankings_wf_def)
    have "linorder_on alts' (of_ranking rs)" if "rs \<in> set R" for rs
      using that R new.mset_eq_alts_list_iff[of rs]
      by (intro linorder_of_ranking) (auto simp: new.prefs_from_rankings_wf_def list.pred_set)
    thus ?thesis
      by (intro majority_mset_extend_profile) auto
  qed
  also have "extend_ranking (majority_mset (image_mset of_ranking (mset R))) = 
                extend_ranking (of_ranking S) \<longleftrightarrow>
             majority_mset (image_mset of_ranking (mset R)) = of_ranking S"
  proof (rule extend_ranking_eq_iff)
    have *: "preorder_on alts' (of_ranking rs)" if "rs \<in> set R" for rs
    proof -
      have "distinct rs \<and> set rs = alts'"
        using that R new.mset_eq_alts_list_iff[of rs]
        by (auto simp: new.prefs_from_rankings_wf_def list.pred_set)
      then interpret linorder_on "alts'" "of_ranking rs"
        by (intro linorder_of_ranking) auto
      show ?thesis ..
    qed
    show "x \<in> alts' \<and> y \<in> alts'"
      if "majority_mset (image_mset of_ranking (mset R)) x y" for x y
      using majority_mset_not_outside[OF that, of "alts'"] * by auto
  next
    show "x \<in> alts' \<and> y \<in> alts'" if "of_ranking S x y" for x y
      using S' of_ranking_imp_in_set[OF that] by auto
  qed
  also have "\<dots> \<and> distinct S \<longleftrightarrow> majority_rel_mset (mset R) S"
    unfolding majority_rel_mset_def ..
  finally show ?thesis .
qed    

lemma new_swf'_eq: 
  assumes R: "new.prefs_from_rankings_wf R"
  shows "new.swf' R = filter (\<lambda>x. x \<in> alts') (swf' (map extend R))"
proof -
  have "mset (swf' (map extend R)) = mset_set alts"
    by (intro swf'_wf wf_extend R)
  hence "distinct (swf' (map extend R))"
    using distinct_alts_list mset_eq_imp_distinct_iff alts_list by metis
  have "new.swf' R = ranking (swf_low (new.prefs_from_rankings R))"
    by (simp add: new.swf'_def new.swf'_def new.prefs_from_rankings_def)
  also have "\<dots> = ranking (restrict_relation alts' (swf (prefs_from_rankings (map extend R))))"
    using R by (simp add: swf_low_def prefs_from_rankings_extend)
  also have "swf (prefs_from_rankings (map extend R)) =
               of_ranking (ranking (swf (prefs_from_rankings (map extend R))))"
    by (rule finite_linorder_on.of_ranking_ranking [OF swf_wf', symmetric])
       (use R in \<open>auto intro: wf_extend\<close>)
  also have "\<dots> = of_ranking (swf' (map extend R))"
    unfolding swf'_def by (simp add: new.prefs_from_rankings_def swf'_def)
  also have "restrict_relation alts' \<dots> =
               of_ranking (filter (\<lambda>x. x \<in> alts') (swf' (map extend R)))"
    unfolding of_ranking_filter Collect_mem_eq ..
  also have "ranking \<dots> = filter (\<lambda>x. x \<in> alts') (swf' (map extend R))"
    by (intro ranking_of_ranking distinct_filter)
       (use \<open>distinct (swf' (map extend R))\<close> in auto)
  finally show ?thesis .
qed

end


subsubsection \<open>Decreasing the number of agents by a factor\<close>

text \<open>
  The nicest way to formalise the cloning construction would be using the view where a profile is
  a multiset of rankings. However, this requires anonymity. For full generality, we show that the
  construction also works in the absence of anonymity.

  To this end, we first define the notion of a \<^emph>\<open>cloning\<close>. Let $A \subseteq B$. The idea is that
  $B\setminus A$ consists of clones of elements of $A$, and each element of $A$ is cloned equally
  often. We model this via a function called ``unclone'' which maps each element of $A$ to itself and
  every element of $A\setminus B$ to the original element in $B$ that it was cloned from.
\<close>
locale cloning =
  fixes A B unclone
  assumes subset: "A \<subseteq> B"
  assumes finite: "finite B"
  assumes unclone: "\<And>x. x \<in> B \<Longrightarrow> unclone x \<in> A"
  assumes unclone_ident: "\<And>x. x \<in> A \<Longrightarrow> unclone x = x"
  assumes card_unclone:
            "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> card (unclone -` {x} \<inter> B) = card (unclone -` {y} \<inter> B)"
begin

definition clones :: "'a \<Rightarrow> 'a set"
  where "clones i = unclone -` {i} \<inter> B"

definition factor :: nat
  where "factor = card B div card A"

lemma finite_clones: "finite (clones i)"
  by (rule finite_subset[OF _ finite]) (auto simp: clones_def)

lemma clones_outside: "i \<notin> A \<Longrightarrow> clones i = {}"
  unfolding clones_def using unclone by auto

lemma card_clones':
  assumes "i \<in> A"
  shows   "card (clones i) * card A = card B"
proof -
  have "B = (\<Union>i\<in>A. clones i)"
    using unclone unfolding clones_def by blast
  also from subset have "card \<dots> = (\<Sum>j\<in>A. card (clones j))"
    by (subst card_UN_disjoint) (auto simp: clones_def intro: finite_subset[OF _ finite])
  also have "\<dots> = (\<Sum>j\<in>A. card (clones i))"
    unfolding clones_def by (intro sum.cong card_unclone assms refl)
  also have "\<dots> = card A * card (clones i)"
    by simp
  finally show ?thesis by (simp add: mult_ac)
qed

lemma card_clones:
  assumes "i \<in> A"
  shows   "card (clones i) = factor"
proof (cases "B = {}")
  case True
  thus ?thesis
    unfolding clones_def factor_def by simp
next
  case False
  hence "A \<noteq> {}"
    using unclone by auto
  have "factor = card (clones i) * card A div card A"
    unfolding factor_def using card_clones'[OF assms] by simp
  also have "\<dots> = card (clones i)"
    by (rule nonzero_mult_div_cancel_right)
       (use finite_subset[OF subset finite] \<open>A \<noteq> {}\<close> in auto)
  finally show ?thesis ..
qed

lemma image_mset_unclone:
  "image_mset unclone (mset_set B) = repeat_mset factor (mset_set A)"
    (is "?lhs = ?rhs")
proof (rule multiset_eqI)
  fix i :: 'a
  have "count (image_mset unclone (mset_set B)) i =
          sum (count (mset_set B)) (clones i)"
    by (subst count_image_mset) (simp_all add: clones_def finite)
  also have "\<dots> = sum (\<lambda>_. 1) (clones i)"
    by (rule sum.cong) (auto simp: clones_def finite)
  also have "\<dots> = card (clones i)"
    by simp
  also have "\<dots> = (if i \<in> A then factor else 0)"
    using card_clones by (auto simp: clones_outside)
  also have "\<dots> = count (repeat_mset factor (mset_set A)) i"
    using finite_subset[OF subset finite] by (simp add: count_mset_set')
  finally show "count ?lhs i = count ?rhs i" .
qed

lemma factor_pos: "B \<noteq> {} \<Longrightarrow> factor > 0"
  using card_clones card_clones' local.finite unclone by fastforce

end


text \<open>
  It is easy to see (but somewhat tedious to show) that a cloning exists whenever $|B|$ 
  is a multiple of $|A|$
\<close>
lemma cloning_exists:
  assumes "A \<subseteq> B" "finite B" "A \<noteq> {}" "card A dvd card B"
  shows   "\<exists>unclone. cloning A B unclone"
  using assms(2,1,3,4)
proof (induction rule: finite_psubset_induct)
  case (psubset B)
  show ?case
  proof (cases "A = B")
    case True
    have "cloning A B id"
      by standard (use True psubset.hyps in auto)
    thus ?thesis
      by blast
  next
    case False
    have "card B \<ge> card A"
      using False psubset.prems card_mono psubset.hyps by blast
    hence "card (B - A) = card B - card A"
      by (subst card_Diff_subset) (use psubset.hyps psubset.prems in auto)
    also have "\<dots> \<ge> card A"
      using False psubset.prems psubset.hyps
      by (meson antisym_conv1 dvd_imp_le dvd_minus_self psubset_card_mono zero_less_diff)
    finally obtain X where X: "X \<subseteq> B - A" "card X = card A"
      by (meson obtain_subset_with_card_n)
    obtain f where f: "bij_betw f X A"
      using X(2) psubset.prems psubset.hyps
      by (metis card_gt_0_iff finite_same_card_bij finite_subset)

    have "\<exists>unclone. cloning A (B - X) unclone"
    proof (rule psubset.IH)
      have "X \<noteq> {}"
        using X psubset.hyps psubset.prems by force
      thus "B - X \<subset> B"
        using X(1) by blast
      have "card A dvd card B - card X"
        using X \<open>card B \<ge> card A\<close> dvd_minus_self psubset.prems(3) by metis
      also have "card B - card X = card (B - X)"
        by (subst card_Diff_subset) (use X finite_subset[OF X(1)] psubset.hyps in auto)
      finally show "card A dvd card (B - X)" .
    qed (use X psubset.hyps psubset.prems in auto)
    then obtain unclone where "cloning A (B - X) unclone" ..
    interpret cloning A "B - X" unclone by fact

    define unclone' where "unclone' = (\<lambda>x. if x \<in> X then f x else unclone x)"
    have "cloning A B unclone'"
    proof
      show "A \<subseteq> B" "finite B"
        by fact+
    next
      show "unclone' x \<in> A" if "x \<in> B" for x
        using unclone f that by (auto simp: unclone'_def bij_betw_def)
    next
      show "unclone' x = x" if "x \<in> A" for x
        using that X unclone_ident by (auto simp: unclone'_def)
    next
      have *: "card (unclone' -` {x} \<inter> B) = factor + 1" if "x \<in> A" for x
      proof -
        have "unclone' -` {x} \<inter> B = (unclone' -` {x} \<inter> (B - X)) \<union> (unclone' -` {x} \<inter> X)"
          using X by blast
        also have "card \<dots> = card (unclone' -` {x} \<inter> (B - X)) + card (unclone' -` {x} \<inter> X)"
          by (rule card_Un_disjoint) (use X psubset.hyps in \<open>auto intro: finite_subset\<close>)
        also have "unclone' -` {x} \<inter> (B - X) = clones x"
          by (auto simp: unclone'_def clones_def)
        also have "card (clones x) = factor"
          by (rule card_clones) fact
        also have "unclone' -` {x} \<inter> X = f -` {x} \<inter> X"
          by (auto simp: unclone'_def)
        also have "f -` {x} \<inter> X = {inv_into X f x}"
          using f bij_betw_inv_into_left[OF f] bij_betw_inv_into_right[OF f] that
          by (auto intro!: inv_into_into simp: bij_betw_def inj_on_def)
        finally show ?thesis
          by simp
      qed
      show "card (unclone' -` {x} \<inter> B) = card (unclone' -` {y} \<inter> B)" if "x \<in> A" "y \<in> A" for x y
        using that[THEN *] by simp
    qed
    thus ?thesis
      by blast
  qed
qed


text \<open>
  We are now ready to give the actual construction.
\<close>

locale swf_split_agents =
  social_welfare_function agents alts swf +
  clone: cloning agents' agents unclone
  for agents :: "'agent set" and alts :: "'alt set" and swf and agents' unclone
begin

lemmas agents' = clone.subset

lemma nonempty_agents': "agents' \<noteq> {}"
  using clone.unclone nonempty_agents by blast

sublocale new: linorder_election agents' alts
  by standard (use finite_subset[OF agents'] nonempty_agents' in auto)

text \<open>
  The profiles are extended in the obvious way: the ranking declared by a clone is the same
  as the ranking of its original.
\<close>
definition extend_profile :: "('agent \<Rightarrow> 'alt relation) \<Rightarrow> 'agent \<Rightarrow> 'alt relation" where
  "extend_profile R i = (if i \<in> agents then R (unclone i) else (\<lambda>_ _. False))"

lemma is_pref_profile_extend_profile [intro]:
  assumes "new.is_pref_profile R"
  shows   "is_pref_profile (extend_profile R)"
proof
  fix i assume i: "i \<in> agents"
  interpret R: pref_profile_linorder_wf agents' alts R
    by fact
  show "linorder_on alts (extend_profile R i)"
    using i clone.unclone unfolding extend_profile_def by auto
qed (auto simp: extend_profile_def)

lemma count_extend_profile:
  "card {i\<in>agents. extend_profile R i x y} = clone.factor * card {i\<in>agents'. R i x y}"
proof -
  have "card {i \<in> agents. extend_profile R i x y} = 
          size (filter_mset (\<lambda>i. extend_profile R i x y) (mset_set agents))"
    by simp
  also have "filter_mset (\<lambda>i. extend_profile R i x y) (mset_set agents) =
             filter_mset (\<lambda>i. R (unclone i) x y) (mset_set agents)"
    unfolding extend_profile_def by (intro filter_mset_cong) auto
  also have "size \<dots> = size (filter_mset (\<lambda>i. R i x y) (image_mset unclone (mset_set agents)))"
    by (simp add: filter_mset_image_mset)
  also have "image_mset unclone (mset_set agents) = repeat_mset clone.factor (mset_set agents')"
    by (simp add: clone.image_mset_unclone)
  also have "size (filter_mset (\<lambda>i. R i x y) \<dots>) =
               clone.factor * card {i \<in> agents'. R i x y}"
    by (simp add: filter_mset_repeat_mset)
  finally show ?thesis .
qed

lemma majority_extend_profile:
  assumes "new.is_pref_profile R"
  shows   "majority (extend_profile R) = majority R"
proof (intro ext)
  fix x y :: 'alt
  interpret R: pref_profile_linorder_wf agents' alts R by fact
  interpret R': pref_profile_linorder_wf agents alts "extend_profile R"
    using assms by auto
  show "majority (extend_profile R) x y = majority R x y"
    using clone.factor_pos by (simp add: R.majority_iff' R'.majority_iff' count_extend_profile)
qed


text \<open>
  Correspondingly, we define our new SWF by feeding the cloned profiles to the old one.
\<close>
definition swf_low :: "('agent \<Rightarrow> 'alt relation) \<Rightarrow> 'alt relation"
  where "swf_low R = swf (extend_profile R)"

sublocale new: social_welfare_function agents' alts swf_low
proof
  fix R assume R: "new.is_pref_profile R"
  thus "linorder_on alts (swf_low R)"
    unfolding swf_low_def by (intro swf_wf) auto
qed


text \<open>
  It is easy to see that cloning commutes with a permutation of the agents, so the resulting
  SWF is still anonymous if the original one was.
\<close>
lemma anonymous_clone:
  assumes "anonymous_swf agents alts swf"
  shows   "anonymous_swf agents' alts swf_low"
proof
  interpret anonymous_swf agents alts swf by fact
  fix \<pi> R assume \<pi>: "\<pi> permutes agents'" and R: "new.is_pref_profile R"
  interpret R: pref_profile_linorder_wf agents' alts R
    by fact
  have \<pi>': "\<pi> permutes agents"
    using \<pi> agents' by (rule permutes_subset)
  show "swf_low (R \<circ> \<pi>) = swf_low R"
    unfolding swf_low_def
  proof (rule anonymous')
    have "image_mset (extend_profile (R \<circ> \<pi>)) (mset_set agents) =
          image_mset (R \<circ> \<pi> \<circ> unclone) (mset_set agents)"
      by (intro image_mset_cong) (auto simp: extend_profile_def)
    also have "\<dots> = image_mset (R \<circ> \<pi>) (image_mset unclone (mset_set agents))"
      by (simp add: multiset.map_comp)
    also have "\<dots> = repeat_mset clone.factor (image_mset (R \<circ> \<pi>) (mset_set agents'))"
      by (simp add: clone.image_mset_unclone image_mset_repeat_mset)
    also have "image_mset (R \<circ> \<pi>) (mset_set agents') = image_mset R (mset_set agents')"
      using \<pi> by (simp add: permutes_image_mset flip: multiset.map_comp)
    also have "repeat_mset clone.factor \<dots> = image_mset (R \<circ> unclone) (mset_set agents)"
      by (simp add: image_mset_repeat_mset clone.image_mset_unclone flip: multiset.map_comp)
    also have "\<dots> = image_mset (extend_profile R) (mset_set agents)"
      by (rule image_mset_cong) (auto simp: extend_profile_def)
    finally show "image_mset (extend_profile (R \<circ> \<pi>)) (mset_set agents) =
                  image_mset (extend_profile R) (mset_set agents)" .
  qed (use R R.wf_permute_agents[OF \<pi>] in auto)
qed

text \<open>
  Unanimity is obviously preserved as well.
\<close>
lemma unanimous_clone:
  assumes "unanimous_swf agents alts swf"
  shows   "unanimous_swf agents' alts swf_low"
proof
  interpret unanimous_swf agents alts swf
    by fact
  fix R x y assume R: "new.is_pref_profile R" and xy: "\<forall>i\<in>agents'. y \<prec>[R i] x"
  show "y \<prec>[swf_low R] x"
    unfolding swf_low_def
  proof (rule unanimous)
    show "\<forall>i\<in>agents. y \<prec>[extend_profile R i] x"
      using xy clone.unclone by (auto simp: strongly_preferred_def extend_profile_def)
  qed (use R in auto)
qed

text \<open>
  Strategyproofness is slightly more involved. A manipulation by a single agent in an original
  profile corresponds to a simultaneous manipulation of them and all their clones. However, it can 
  be shown that the normal notion of Kemeny strategyproofness (where only one agent is allowed to 
  manipulate) also implies that no set of clones can obtain a better result by manipulating 
  simultaneously. This works by simply considering a chain of single-agent manipulations.

  This shows that strategyproofness is also preserved.
\<close>
lemma kemeny_strategyproof_clone:
  assumes "kemeny_strategyproof_swf agents alts swf"
  shows   "kemeny_strategyproof_swf agents' alts swf_low"
proof
  fix R i S assume R: "new.is_pref_profile R" and i: "i \<in> agents'" and S: "linorder_on alts S"
  interpret kemeny_strategyproof_swf agents alts swf by fact
  interpret R: pref_profile_linorder_wf agents' alts R by fact

  define C where "C = unclone -` {i} \<inter> agents"
  define R' where "R' = (\<lambda>X j. if j \<in> X then S else extend_profile R j)"

  have step: "swap_dist_relation (R i) (swf (R' X)) \<le> swap_dist_relation (R i) (swf (R' (insert x X)))"
    if x: "insert x X \<subseteq> C" "x \<notin> X" for x X
  proof -
    have "swap_dist_relation (R' X x) (swf (R' X)) \<le> swap_dist_relation (R' X x) (swf ((R' X)(x := S)))"
    proof (rule kemeny_strategyproof)
      show "x \<in> agents"
        using x by (auto simp: C_def)
    next
      show "is_pref_profile (R' X)"
      proof
        fix j assume "j \<in> agents"
        thus "linorder_on alts (R' X j)"
          unfolding R'_def using S R clone.unclone by (auto simp: extend_profile_def)
      qed (use x in \<open>auto simp: R'_def C_def extend_profile_def\<close>)
    qed fact+
    also have "R' X x = R i"
      using x by (auto simp: R'_def extend_profile_def C_def)
    also have "(R' X)(x := S) = R' (insert x X)"
      using x by (auto simp: R'_def)
    finally show ?thesis .
  qed

  show "swap_dist_relation (R i) (swf_low R) \<le> swap_dist_relation (R i) (swf_low (R(i := S)))"
  proof -
    define X where "X = C"
    have "finite C" unfolding C_def
      by (rule finite_subset[OF _ finite_agents]) auto
    moreover have "x \<in> agents" "unclone x = i" if "x \<in> C" for x
      using that unfolding C_def by blast+
    ultimately have "swap_dist_relation (R i) (swf_low R) \<le> swap_dist_relation (R i) (swf (R' C))"
    proof (induction rule: finite_induct)
      case (insert x X)
      have "swap_dist_relation (R i) (swf_low R) \<le> swap_dist_relation (R i) (swf (R' X))"
        by (rule insert.IH) (use insert.prems in auto)
      also have "swap_dist_relation (R i) (swf (R' X)) \<le> swap_dist_relation (R i) (swf (R' (insert x X)))"
        by (rule step) (use insert.hyps insert.prems in \<open>auto simp: C_def\<close>)
      finally show ?case .    
    qed (simp_all add: swf_low_def R'_def)
    also have "R' C = extend_profile (R(i := S))"
      unfolding extend_profile_def R'_def C_def fun_eq_iff by auto
    finally show ?thesis
      by (simp add: swf_low_def)
  qed
qed

lemma majority_consistent_clone:
  assumes "majority_consistent_swf agents alts swf"
  shows   "majority_consistent_swf agents' alts swf_low"
proof
  fix R assume R: "new.is_pref_profile R" "linorder_on alts (majority R)"
  interpret majority_consistent_swf agents alts swf by fact
  interpret R: pref_profile_linorder_wf agents' alts R by fact
  have "swf_low R = swf (extend_profile R)"
    unfolding swf_low_def ..
  also have "\<dots> = majority (extend_profile R)"
    by (rule majority_consistent) (use R in \<open>auto simp: majority_extend_profile\<close>)
  also have "\<dots> = majority R"
    by (rule majority_extend_profile) fact+
  finally show "swf_low R = majority R" .
qed

end


subsubsection \<open>Decreasing the number of agents by an even number\<close>

text \<open>
  Given an SWF for $m$ alternatives and $n$ agents, we can construct an SWF for $m$ alternatives
  and $n-2k$ agents by fixing some arbitrary ranking of alternatives and adding $k$ clones of it
  to the input profile as well as $k$ reversed clones.

  This construction clearly violates anonymity and unanimity. It does however preserve 
  strategyproofness (by a similar argument as for the cloning, but simpler) and
  majority consistency since the majority relation is preserved by our changes to the profile.
\<close>

locale swf_reduce_agents_even =
  social_welfare_function agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf +
  fixes agents1 agents2 :: "'agent set" and dummy_ord :: "'alt relation"
  assumes agents12:
    "agents1 \<union> agents2 \<subset> agents" "agents1 \<inter> agents2 = {}" "card agents1 = card agents2"
  assumes dummy_ord: "linorder_on alts dummy_ord"
begin

sublocale new: linorder_election "agents - agents1 - agents2" alts
  by standard (use agents12 in auto)

definition extend_profile :: "('agent \<Rightarrow> 'alt relation) \<Rightarrow> 'agent \<Rightarrow> 'alt relation" where
  "extend_profile R =
     (\<lambda>i. if i \<in> agents1 then dummy_ord else if i \<in> agents2 then \<lambda>x y. dummy_ord y x else R i)"

lemma dummy_ord': "linorder_on alts (\<lambda>x y. dummy_ord y x)"
proof -
  interpret linorder_on alts dummy_ord
    by (fact dummy_ord)
  show ?thesis ..
qed

lemma is_pref_profile_extend_profile [intro]:
  assumes "new.is_pref_profile R"
  shows   "is_pref_profile (extend_profile R)"
proof
  interpret R: pref_profile_linorder_wf "agents - agents1 - agents2" alts R
    by fact
  show "linorder_on alts (extend_profile R i)" if i: "i \<in> agents" for i
    using i agents12 dummy_ord dummy_ord' R.in_dom by (auto simp: extend_profile_def)
  show "extend_profile R i = (\<lambda>_ _. False)" if i: "i \<notin> agents" for i
    using i R.not_in_dom agents12 by (auto simp: extend_profile_def fun_eq_iff)
qed

lemma count_extend_profile:
  assumes "new.is_pref_profile R" "x \<in> alts" "y \<in> alts"
  shows   "card {i \<in> agents. extend_profile R i x y} =
             card {i \<in> agents - agents1 - agents2. R i x y} +
             (if x = y then 2 else 1) * card agents1"
proof -
  have fin: "finite agents1" "finite agents2"
    by (rule finite_subset[OF _ finite_agents]; use agents12 in blast)+
  interpret dummy_ord: linorder_on alts dummy_ord by (fact dummy_ord)
  have "{i \<in> agents. extend_profile R i x y} =
          {i\<in>agents-agents1-agents2. extend_profile R i x y} \<union> 
          {i\<in>agents1. extend_profile R i x y} \<union> {i\<in>agents2. extend_profile R i x y}"
    using agents12 by blast
  also have "\<dots> = {i\<in>agents-agents1-agents2. R i x y} \<union> 
                    ({i\<in>agents1. dummy_ord x y} \<union> {i\<in>agents2. dummy_ord y x})"
    using agents12 by (auto simp: extend_profile_def)
  also have "card \<dots> = card {i\<in>agents-agents1-agents2. R i x y} +
                         card ({i\<in>agents1. dummy_ord x y} \<union> {i\<in>agents2. dummy_ord y x})"
    by (rule card_Un_disjoint) (use agents12 fin in auto)
  also have "card ({i\<in>agents1. dummy_ord x y} \<union> {i\<in>agents2. dummy_ord y x}) =
               (if dummy_ord x y then card agents1 else 0) +
               (if dummy_ord y x then card agents1 else 0)"
    by (subst card_Un_disjoint) (use agents12 fin in auto)
  also have "\<dots> = (if x = y then 2 else 1) * card agents1"
    using dummy_ord.total[of x y] dummy_ord.antisymmetric[of x y] assms(2,3) by auto
  finally show ?thesis .
qed

lemma majority_extend_profile:
  assumes "new.is_pref_profile R"
  shows   "majority (extend_profile R) = majority R"
proof (intro ext)
  fix x y :: 'alt
  interpret R: pref_profile_linorder_wf "agents - agents1 - agents2" alts R by fact
  interpret R': pref_profile_linorder_wf agents alts "extend_profile R"
    using assms by auto
  show "majority (extend_profile R) x y = majority R x y"
  proof (cases "x \<in> alts \<and> y \<in> alts \<and> x \<noteq> y")
    case xy: True
    show ?thesis
      using xy  assms by (auto simp: R.majority_iff R'.majority_iff count_extend_profile)
  qed (auto simp: R.majority_iff' R'.majority_iff')
qed
      

definition swf_low :: "('agent \<Rightarrow> 'alt relation) \<Rightarrow> 'alt relation" where
  "swf_low R = swf (extend_profile R)"

sublocale new: social_welfare_function "agents - agents1 - agents2" alts swf_low
  by standard (auto simp: swf_low_def intro: swf_wf)

lemma kemeny_strategyproof_reduce:
  assumes "kemeny_strategyproof_swf agents alts swf"
  shows   "kemeny_strategyproof_swf (agents - agents1 - agents2) alts swf_low"
proof
  fix R i S 
  assume R: "new.is_pref_profile R"
  assume i: "i \<in> agents - agents1 - agents2"
  assume S: "linorder_on alts S"
  interpret kemeny_strategyproof_swf agents alts swf by fact
  interpret R: pref_profile_linorder_wf "agents - agents1 - agents2" alts R by fact

  have "swap_dist_relation (R i) (swf_low R) = 
          swap_dist_relation (extend_profile R i) (swf (extend_profile R))"
    using i agents12 by (simp add: swf_low_def extend_profile_def)
  also have "\<dots> \<le> swap_dist_relation (extend_profile R i) (swf ((extend_profile R)(i := S)))"
    by (rule kemeny_strategyproof) (use i agents12 S R in auto)
  also have "(extend_profile R)(i := S) = extend_profile (R(i := S))"
    using i agents12 by (auto simp: extend_profile_def)
  also have "swap_dist_relation (extend_profile R i) (swf \<dots>) =
             swap_dist_relation (R i) (swf_low (R(i := S)))"
    using i agents12 by (simp add: swf_low_def extend_profile_def)
  finally show "swap_dist_relation (R i) (swf_low R) \<le> swap_dist_relation (R i) (swf_low (R(i := S)))" .
qed

lemma majority_consistent_reduce:
  assumes "majority_consistent_swf agents alts swf"
  shows   "majority_consistent_swf (agents - agents1 - agents2) alts swf_low"
proof
  fix R assume R: "new.is_pref_profile R" "linorder_on alts (majority R)"
  interpret majority_consistent_swf agents alts swf by fact
  interpret R: pref_profile_linorder_wf "agents - agents1 - agents2" alts R by fact
  have "swf_low R = swf (extend_profile R)"
    unfolding swf_low_def ..
  also have "\<dots> = majority (extend_profile R)"
    by (rule majority_consistent) (use R in \<open>auto simp: majority_extend_profile\<close>)
  also have "\<dots> = majority R"
    by (rule majority_extend_profile) fact+
  finally show "swf_low R = majority R" .
qed

end

end