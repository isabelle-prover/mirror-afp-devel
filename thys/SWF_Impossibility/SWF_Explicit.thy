subsection \<open>Social Welfare Functions with explicit lists of agents and alternatives\<close>
theory SWF_Explicit
  imports SWF_Anonymous
begin

locale linorder_election_explicit =
  linorder_election agents alts
  for agents :: "'agent set" and alts :: "'alt set" +
  fixes agents_list :: "'agent list" and alts_list :: "'alt list"
  assumes agents_list: "mset agents_list = mset_set agents"
  assumes alts_list: "mset alts_list = mset_set alts"
begin

lemma distinct_alts_list: "distinct alts_list"
  using alts_list by (metis finite_alts mset_eq_mset_set_imp_distinct)

lemma alts_conv_alts_list: "alts = set alts_list"
  using alts_list by (metis finite_alts finite_set_mset_mset_set set_mset_mset)

lemma card_alts [simp]: "card alts = length alts_list"
  using alts_list by (metis size_mset size_mset_set)

lemma distinct_agents_list: "distinct agents_list"
  using agents_list by (metis finite_agents mset_eq_mset_set_imp_distinct)

lemma agents_conv_agents_list: "agents = set agents_list"
  using agents_list by (metis finite_agents finite_set_mset_mset_set set_mset_mset)

lemma card_agents: "card agents = length agents_list"
  using agents_list by (metis size_mset size_mset_set)

lemma mset_eq_alts_list_iff: "mset xs = mset alts_list \<longleftrightarrow> distinct xs \<and> set xs = alts"
  by (metis alts_conv_alts_list card_alts card_distinct
            mset_set_set set_mset_mset size_mset)

lemma mset_eq_agents_list_iff: "mset xs = mset agents_list \<longleftrightarrow> distinct xs \<and> set xs = agents"
  by (metis agents_conv_agents_list card_agents card_distinct
            mset_set_set set_mset_mset size_mset)

definition prefs_from_rankings 
    :: "'alt list list \<Rightarrow> ('agent \<Rightarrow> 'alt relation)" where
  "prefs_from_rankings rs =
     (\<lambda>i. if i \<in> agents then of_ranking (rs ! index agents_list i) else (\<lambda>_ _. False))"

definition prefs_from_rankings_wf  :: "'alt list list \<Rightarrow> bool" where
  "prefs_from_rankings_wf rs \<longleftrightarrow>
     length rs = card agents \<and> list_all (\<lambda>r. mset r = mset alts_list) rs"

lemma prefs_from_rankings_wf_imp_is_pref_profile [intro]:
  assumes "prefs_from_rankings_wf rs"
  shows   "is_pref_profile (prefs_from_rankings rs)"
proof
  fix i assume i: "i \<in> agents"
  hence "rs ! index agents_list i \<in> set rs"
    by (intro nth_mem) 
       (use assms in \<open>auto simp: prefs_from_rankings_wf_def card_agents index_less_size_conv 
                           simp flip: agents_conv_agents_list\<close>)
  hence "distinct (rs ! index agents_list i) \<and> set (rs ! index agents_list i) = alts"
    using assms unfolding prefs_from_rankings_wf_def list.pred_set mset_eq_alts_list_iff by blast
  thus "linorder_on alts (prefs_from_rankings rs i)"
    using assms i by (auto simp: prefs_from_rankings_def intro!: linorder_of_ranking)
qed (use assms in \<open>auto simp: prefs_from_rankings_def\<close>)

lemma prefs_from_rankings_nth:
  assumes "prefs_from_rankings_wf R1" "i < card agents"
  shows   "prefs_from_rankings R1 (agents_list ! i) = of_ranking (R1 ! i)"
  using assms card_agents agents_conv_agents_list distinct_agents_list
  unfolding prefs_from_rankings_def by (simp add: index_nth_id)

lemma prefs_from_rankings_outside:
  assumes "i \<notin> agents"
  shows   "prefs_from_rankings R1 i = (\<lambda>_ _. False)"
  using assms by (auto simp: prefs_from_rankings_def)

lemma prefs_from_rankings_update:
  assumes "prefs_from_rankings_wf R1" "i < card agents" "mset xs = mset alts_list"
  shows   "prefs_from_rankings (R1[i := xs]) =
           (prefs_from_rankings R1)(agents_list ! i := of_ranking xs)"
  using assms distinct_agents_list card_agents agents_conv_agents_list
        index_less_size_conv[of agents_list]
  unfolding prefs_from_rankings_def prefs_from_rankings_wf_def
  by (auto simp: fun_eq_iff index_nth_id nth_list_update)

lemma prefs_from_rankings_wf_update:
  assumes "prefs_from_rankings_wf R1" "i < card agents" "mset xs = mset alts_list"
  shows   "prefs_from_rankings_wf (R1[i := xs])"
  using assms set_update_subset_insert[of R1 i xs] unfolding prefs_from_rankings_wf_def
  by (auto simp: list.pred_set set_update_distinct)

lemma majority_prefs_from_rankings:
  assumes "prefs_from_rankings_wf R"
  shows   "majority (prefs_from_rankings R) = majority_mset (mset (map of_ranking R))"
proof -
  interpret R: pref_profile_linorder_wf agents alts "prefs_from_rankings R"
    using assms by blast
  have "majority (prefs_from_rankings R) = 
          majority_mset (image_mset (prefs_from_rankings R) (mset_set agents))"
    by (rule R.majority_conv_majority_mset) auto
  also have "image_mset (prefs_from_rankings R) (mset_set agents) =
             image_mset (of_ranking \<circ> (\<lambda>i. R ! i) \<circ> index agents_list) (mset_set agents)"
    by (intro image_mset_cong)
       (use assms in \<open>auto simp: prefs_from_rankings_wf_def prefs_from_rankings_def\<close>)
  also have "\<dots> = image_mset of_ranking (image_mset (\<lambda>i. R ! i) (image_mset (index agents_list) (mset agents_list)))"
    by (simp add: image_mset.compositionality o_def agents_list)
  also have "image_mset (\<lambda>i. R ! i) (image_mset (index agents_list) (mset agents_list)) =
             mset (map (\<lambda>i. R ! i) (map (index agents_list) agents_list))"
    unfolding mset_map by simp
  also have "map (index agents_list) agents_list = [0..<length R]"
    by (subst map_index_self)
       (use distinct_agents_list card_agents assms in \<open>simp_all add: prefs_from_rankings_wf_def\<close>)
  also have "map (\<lambda>i. R ! i) \<dots> = R"
    by (rule map_nth)
  finally show ?thesis by simp
qed

lemma majority_prefs_from_rankings_eq_of_ranking:
  assumes "prefs_from_rankings_wf R" "majority_rel_mset (mset R) ys"
  shows   "majority (prefs_from_rankings R) = of_ranking ys"
proof -
  have "of_ranking ys = majority_mset (image_mset of_ranking (mset R))"
    using assms(2) by (auto simp: majority_rel_mset_def)
  also have "\<dots> = majority (prefs_from_rankings R)"
    by (subst majority_prefs_from_rankings) (use assms in simp_all)
  finally show ?thesis ..
qed

lemma majority_rel_mset_imp_mset:
  assumes "prefs_from_rankings_wf R" "majority_rel_mset (mset R) xs"
  shows   "mset xs = mset alts_list"
proof -
  interpret R: pref_profile_linorder_wf agents alts "prefs_from_rankings R"
    by (rule prefs_from_rankings_wf_imp_is_pref_profile) fact
  have "majority (prefs_from_rankings R) = of_ranking xs"
    by (rule majority_prefs_from_rankings_eq_of_ranking) fact+
  thus ?thesis
    by (metis R.majority_not_outside(2) R.majority_refl assms(2) majority_rel_mset_def
          mset_eq_alts_list_iff of_ranking_imp_in_set(2) of_ranking_refl
          order_antisym_conv subset_iff)
qed

end


locale social_welfare_function_explicit =
  social_welfare_function agents alts swf +
  linorder_election_explicit agents alts agents_list alts_list
  for agents :: "'agent set" and alts :: "'alt set" and swf agents_list alts_list
begin

definition swf' :: "'alt list list \<Rightarrow> 'alt list" where
  "swf' R = ranking (swf (prefs_from_rankings R))"

lemma swf'_wf: "prefs_from_rankings_wf R \<Longrightarrow> mset (swf' R) = mset_set alts"
  unfolding swf'_def
  using finite_linorder_on.distinct_ranking finite_linorder_on.set_ranking alts_list finite_alts
        prefs_from_rankings_wf_imp_is_pref_profile mset_eq_alts_list_iff swf_wf' by metis

end


locale majority_consistent_swf_explicit =
  social_welfare_function_explicit agents alts swf agents_list alts_list +
  majority_consistent_swf agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf agents_list alts_list
begin

lemma majority_consistent_swf':
  assumes "prefs_from_rankings_wf R" "majority_rel_mset (mset R) ys"
  shows   "swf' R = ys"
  using assms
  by (metis linorder_of_ranking majority_consistent majority_prefs_from_rankings_eq_of_ranking
        majority_rel_mset_imp_mset mset_eq_alts_list_iff
        prefs_from_rankings_wf_imp_is_pref_profile ranking_of_ranking swf'_def)

end

locale majcons_kstratproof_swf_explicit =
  social_welfare_function_explicit agents alts swf agents_list alts_list +
   majcons_kstratproof_swf agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf agents_list alts_list
begin

sublocale majority_consistent_swf_explicit ..

sublocale majority_consistent_weak_kstratproof_swf
  by unfold_locales
     (metis kemeny_strategyproof majority_consistent pref_profile_linorder_wf.wf_update)

lemma distinct_alts_list_aux: "distinct alts_list"
  using alts_list by (metis finite_alts mset_eq_mset_set_imp_distinct)

lemma distinct_agents_list_aux: "distinct agents_list"
  using agents_list by (metis finite_agents mset_eq_mset_set_imp_distinct)

lemma prefs_from_rankings_wf_iff:
  "prefs_from_rankings_wf xss \<longleftrightarrow> 
     length xss = length agents_list \<and> list_all (\<lambda>ys. mset ys = mset alts_list) xss"
  unfolding prefs_from_rankings_wf_def using card_agents by simp

lemma swf'_in_all_rankings:
  assumes "prefs_from_rankings_wf xss" "permutations_of_set_list alts_list = yss"
  shows   "list_ex (\<lambda>ys. swf' xss = ys) yss"
proof -
  have "mset (swf' xss) = mset_set alts"
    by (rule swf'_wf) fact
  hence "swf' xss \<in> permutations_of_set alts"
    unfolding permutations_of_set_def using alts_list mset_eq_alts_list_iff by force
  also have "permutations_of_set alts = set yss"
    by (metis alts_conv_alts_list distinct_alts_list assms(2)
              permutations_of_list remdups_id_iff_distinct)
  finally show ?thesis
    unfolding list_ex_iff by blast
qed

lemma kemeny_strategyproof_swf':
  assumes "prefs_from_rankings_wf R1" "i < card agents"
  assumes "mset zs = mset alts_list"
  assumes "xs = R1 ! i" "R2 = R1[i := zs]"
  shows   "swap_dist xs (swf' R1) \<le> swap_dist xs (swf' R2)"
proof -
  define R1' where "R1' = prefs_from_rankings R1"
  define j where "j = agents_list ! i"
  have j: "j \<in> agents"
    unfolding j_def using assms agents_conv_agents_list card_agents by force
  have zs: "linorder_on alts (of_ranking zs)"
    using assms by (intro linorder_of_ranking) (auto simp: mset_eq_alts_list_iff)
  have "xs \<in> set R1"
    using assms card_agents by (auto simp: prefs_from_rankings_wf_def)
  hence xs: "mset xs = mset alts_list"
    using assms by (auto simp: prefs_from_rankings_wf_def list.pred_set)
  have R2: "prefs_from_rankings_wf R2"
    using assms prefs_from_rankings_wf_update by blast

  have "swap_dist_relation (R1' j) (swf (R1'(j := of_ranking zs))) \<ge> swap_dist_relation (R1' j) (swf R1')"
    by (rule kemeny_strategyproof) (use assms j zs in \<open>auto simp: R1'_def\<close>)
  also have "R1' j = of_ranking xs"
    using assms prefs_from_rankings_nth unfolding R1'_def j_def by metis
  also have "R1'(j := of_ranking zs) = prefs_from_rankings R2"
    using assms unfolding R1'_def j_def using prefs_from_rankings_update by metis
  also have "swf R1' = of_ranking (swf' R1)"
    unfolding swf'_def R1'_def
    by (metis assms(1) finite_linorder_on.of_ranking_ranking
              prefs_from_rankings_wf_imp_is_pref_profile swf_wf')
  also have "swf (prefs_from_rankings R2) = of_ranking (swf' R2)"
    unfolding swf'_def
    by (metis assms(1,2,3,5) finite_linorder_on.of_ranking_ranking prefs_from_rankings_wf_update
          prefs_from_rankings_wf_imp_is_pref_profile swf_wf')
  also have "swap_dist_relation (of_ranking xs) (of_ranking (swf' R1)) =
             swap_dist xs (swf' R1)"
    using swf'_wf[of R1] alts_list assms(1) mset_eq_alts_list_iff xs
    unfolding swap_dist_def by auto
  also have "swap_dist_relation (of_ranking xs) (of_ranking (swf' R2)) =
             swap_dist xs (swf' R2)"
    using xs swf'_wf[of R2] alts_list R2 mset_eq_alts_list_iff
    unfolding swap_dist_def by auto
  finally show ?thesis .
qed

lemma kemeny_strategyproof_swf'_aux:
  assumes "prefs_from_rankings_wf xss" "prefs_from_rankings_wf yss"
  assumes "map (index ys) S1 = S1'" "map (index ys) S2 = S2'"
  assumes "inversion_number S1' = d1" "inversion_number S2' = d2"
  assumes "d1 > d2 \<and> i < length agents_list \<and> ys = xss ! i \<and> yss = xss[i := zs]"
  shows   "swf' xss \<noteq> S1 \<or> swf' yss \<noteq> S2"
proof (rule ccontr)
  assume *: "\<not>(swf' xss \<noteq> S1 \<or> swf' yss \<noteq> S2)"
  with assms(1,2) have S12: "S1 \<in> permutations_of_set alts" "S2 \<in> permutations_of_set alts"
    using swf'_wf by (auto simp: permutations_of_set_conv_mset)
  have "ys \<in> set xss"
    using assms card_agents by (auto simp: prefs_from_rankings_wf_def)
  hence ys: "distinct ys" "set ys = alts"
    using assms by (auto simp: prefs_from_rankings_wf_def list.pred_set mset_eq_alts_list_iff)
  have d12: "swap_dist ys S1 = d1 \<and> swap_dist ys S2 = d2"
    using assms(3-6) S12 ys
    by (subst (1 2) swap_dist_conv_inversion_number) (simp_all add: permutations_of_set_def)

  have "zs \<in> set yss"
    using assms card_agents unfolding prefs_from_rankings_wf_def by (metis set_update_memI)
  hence zs: "mset zs = mset_set alts"
    using assms(2) by (auto simp: prefs_from_rankings_wf_def list.pred_set alts_list)
  have "swap_dist ys (swf' xss) \<le> swap_dist ys (swf' yss)"
    by (rule kemeny_strategyproof_swf'[where i = i]) (use zs assms card_agents alts_list in auto)
  with * d12 assms show False
    by simp
qed

end


locale majcons_weak_kstratproof_swf_explicit =
  social_welfare_function_explicit agents alts swf agents_list alts_list +
  majority_consistent_weak_kstratproof_swf agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf agents_list alts_list
begin

sublocale majority_consistent_swf_explicit agents alts swf agents_list alts_list ..

lemma majority_consistent_kemeny_strategyproof_swf':
  assumes "prefs_from_rankings_wf R1" "i < card agents" "mset zs = mset alts_list"
  assumes "xs = R1 ! i" "majority_rel_mset (mset (R1[i := zs])) ys"
  shows   "swap_dist xs (swf' R1) \<le> swap_dist xs ys"
proof -
  define R2 where "R2 = R1[i := zs]"
  interpret res: finite_linorder_on alts "swf (prefs_from_rankings R1)"
    by (intro swf_wf' prefs_from_rankings_wf_imp_is_pref_profile assms)
  have R2_eq: "prefs_from_rankings R2 = (prefs_from_rankings R1)(agents_list ! i := of_ranking zs)"
    unfolding \<open>R2 = _\<close> by (rule prefs_from_rankings_update) (use assms in auto)
  have R2_wf: "prefs_from_rankings_wf R2"
    unfolding \<open>R2 = _\<close> by (rule prefs_from_rankings_wf_update) (use assms in auto)
  interpret R2: pref_profile_linorder_wf agents alts "prefs_from_rankings R2"
    by (rule prefs_from_rankings_wf_imp_is_pref_profile) fact
  interpret res': finite_linorder_on alts "swf (prefs_from_rankings R2)"
    by (intro swf_wf' prefs_from_rankings_wf_imp_is_pref_profile R2_wf)

  have "xs \<in> set R1"
    using assms(1) \<open>xs = R1 ! i\<close> \<open>i < _\<close>
    unfolding prefs_from_rankings_wf_def by auto
  hence xs: "distinct xs" "set xs = alts"
    using assms(1) by (auto simp: prefs_from_rankings_wf_def list.pred_set mset_eq_alts_list_iff)
  have swf'_R1: "mset (swf' R1) = mset alts_list"
    using assms(1) by (simp add: swf'_wf alts_list)
  have swf'_R2: "mset (swf' R2) = mset alts_list"
    using R2_wf by (simp add: swf'_wf alts_list)

  have ys_eq: "majority (prefs_from_rankings R2) = of_ranking ys"
    by (rule majority_prefs_from_rankings_eq_of_ranking) (use assms R2_wf in \<open>auto simp: R2_def\<close>)
  have "mset ys = mset alts_list"
    by (rule majority_rel_mset_imp_mset) (use R2_wf \<open>majority_rel_mset _ _\<close> in \<open>auto simp: R2_def\<close>)
  have linorder_ys: "linorder_on alts (of_ranking ys)"
    by (intro linorder_of_ranking) (use \<open>mset ys = _\<close> in \<open>auto simp: mset_eq_alts_list_iff\<close>)

  have "swap_dist_relation (prefs_from_rankings R1 (agents_list ! i)) (swf (prefs_from_rankings R1)) \<le>
        swap_dist_relation (prefs_from_rankings R1 (agents_list ! i)) (majority (prefs_from_rankings R2))"
    unfolding R2_eq
  proof (rule majority_consistent_kemeny_strategyproof)
    show "is_pref_profile (prefs_from_rankings R1)"
      using assms(1) by auto
    show "agents_list ! i \<in> agents"
      using \<open>i < _\<close> card_agents by (metis agents_list finite_agents finite_set_mset_mset_set nth_mem_mset)
    show "linorder_on alts (of_ranking zs)"
      using \<open>mset zs = _\<close> alts_list finite_alts
      by (metis finite_set_mset_mset_set linorder_of_ranking mset_eq_mset_set_imp_distinct set_mset_mset)
    show "linorder_on alts (majority ((prefs_from_rankings R1) (agents_list ! i := of_ranking zs)))"
      unfolding R2_eq [symmetric] ys_eq by (rule linorder_ys)
  qed
  also have "prefs_from_rankings R1 (agents_list ! i) = of_ranking (R1 ! i)"
    by (rule prefs_from_rankings_nth) (use assms in auto)
  also have "R1 ! i = xs"
    using assms by simp
  also have "swf (prefs_from_rankings R1) = of_ranking (ranking (swf (prefs_from_rankings R1)))"
    by (simp add: res.of_ranking_ranking)
  also have "\<dots> = of_ranking (swf' R1)"
    by (simp add: swf'_def prefs_from_rankings_def)
  also have "swap_dist_relation (of_ranking xs) (of_ranking (swf' R1)) = swap_dist xs (swf' R1)"
    unfolding swap_dist_def using xs swf'_R1 by (auto simp: mset_eq_alts_list_iff)
  also have "majority (prefs_from_rankings R2) = of_ranking ys"
    by (rule ys_eq)
  also have "swap_dist_relation (of_ranking xs) \<dots> = swap_dist xs ys"
    unfolding swap_dist_def using xs swf'_R2 \<open>mset ys = _\<close> by (auto simp: mset_eq_alts_list_iff)
  finally show ?thesis 
    using assms by simp
qed

end

end