theory Anon_Unan_Stratproof_Impossibility
  imports SWF_Impossibility_Automation
begin

subsection \<open>For 5 alternatives and 2 agents\<close>

text \<open>
  We prove the impossibility for $m = 5$ and $n = 2$ via the SAT encoding using a fixed
  list of 198 profiles. For symmetry breaking, we assume that the profile
  $(abcde, acbed)$ is mapped to the ranking $abcde$. This assumption will be justified later on
  by picking the values of $a, b, c, d, e$ accordingly.
\<close>

external_file "sat_data/kemeny_profiles_5_2.xz"
external_file "sat_data/kemeny_5_2.grat.xz"

locale anonymous_unanimous_kemenysp_swf_explicit_5_2 =
  anonymous_unanimous_kemenysp_swf_explicit agents alts swf 2 "[a,b,c,d,e]"
  for agents :: "'agent set" and alts :: "'alt set" and swf and a b c d e +
  assumes symmetry_breaking: "aswf' {# [a,b,c,d,e], [a,c,b,e,d] #} = [a,b,c,d,e]"
begin

(*
  This call should by quite quick (about 3 seconds on a 2024-ish 12-core machine).
  It is forked to the background as well.
*)

local_setup \<open>fn lthy =>
  let 
    val params = {
      name = "kemeny_5_2",
      locale_thm = @{thm "anonymous_unanimous_kemenysp_swf_explicit_axioms"},
      profile_file = SOME \<^path>\<open>sat_data/kemeny_profiles_5_2.xz\<close>,
      sp_file = NONE,
      grat_file = \<^path>\<open>sat_data/kemeny_5_2.grat.xz\<close>,
      extra_clauses = @{thms symmetry_breaking}
    }
    val thm =
      Goal.prove_future lthy [] [] \<^prop>\<open>False\<close>
        (fn {context, ...} => 
          HEADGOAL (resolve_tac context [Anon_Unan_Stratproof_Impossibility.derive_false context params]))
  in
    Local_Theory.note ((\<^binding>\<open>contradiction\<close>, []), [thm]) lthy |> snd
  end
\<close>

end


text \<open>
  We now get rid of the symmetry-breaking assumption by choosing an appropriate permutation of
  the five alternatives.
\<close>

locale anonymous_unanimous_kemenysp_swf_5_2 = anonymous_unanimous_kemenysp_swf agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf +
  assumes card_agents: "card agents = 2"
  assumes card_alts:   "card alts = 5"
begin

sublocale anonymous_unanimous_swf agents alts swf ..
sublocale anonymous_kemeny_strategyproof_swf agents alts swf ..

lemma symmetry_breaking_aux1:
  assumes distinct: "distinct [a,b,c,d,e]" and alts_eq: "alts = {a,b,c,d,e}"
  defines "R \<equiv> {# [a,b,c,d,e], [a,c,b,e,d] #}"
  assumes R: "aswf' R = [a,c,b,d,e]"
  shows   "aswf' {# [a,b,c,e,d], [a,c,b,d,e] #} \<in> {[a,b,c,e,d], [a,c,b,d,e]}"
proof -
  have alts_eq': "alts = set [a,b,c,d,e]"
    by (simp add: alts_eq)
  have [simp]: "a \<noteq> b" "a \<noteq> c" "a \<noteq> d" "a \<noteq> e" "b \<noteq> a" "b \<noteq> c" "b \<noteq> d" "b \<noteq> e"
               "c \<noteq> a" "c \<noteq> b" "c \<noteq> d" "c \<noteq> e" "d \<noteq> a" "d \<noteq> b" "d \<noteq> c" "d \<noteq> e"
               "e \<noteq> a" "e \<noteq> b" "e \<noteq> c" "e \<noteq> d"
    using distinct by (simp_all add: eq_commute)
  interpret anonymous_unanimous_kemenysp_swf_explicit agents alts swf 2 "[a,b,c,d,e]"
    by standard (simp_all add: alts_eq card_agents)

  have R_wf: "is_apref_profile' R"
    unfolding is_apref_profile'_def by (auto simp: card_agents permutations_of_set_def alts_eq R_def)

  define R2 where "R2 = {# [a,c,b,d,e], [a,c,b,e,d] #}"
  define R3 where "R3 = {# [a,b,c,d,e], [a,c,b,d,e] #}"
  define R4 where "R4 = {# [a,b,c,e,d], [a,c,b,d,e] #}"
  note R_defs = R_def R2_def R3_def R4_def

  have wf: "is_apref_profile' R" "is_apref_profile' R2" "is_apref_profile' R3" "is_apref_profile' R4"
    by (simp_all add: is_apref_profile'_iff R_defs add_mset_commute)

  have R2: "aswf' R2 = [a,c,b,d,e]"
  proof -
    have "aswf' R2 = [a,c,b,d,e] \<or> aswf' R2 = [a,c,b,e,d]"
      using aswf'_in_allowed_results[OF wf(2)] unfolding R_defs
      by (simp add: eval_allowed_results del: Set.filter_eq)
    moreover have "aswf' R2 \<noteq> [a,c,b,e,d] \<or> aswf' R \<noteq> [a,c,b,d,e]"
      by (intro kemeny_strategyproof_aswf'_strong wf)
         (simp_all add: R_defs insert_commute swap_dist_code' inversion_number_Cons)
    ultimately show ?thesis using R
      by blast
  qed

  have R3: "aswf' R3 = [a,c,b,d,e]"
  proof -
    have "aswf' R3 = [a,b,c,d,e] \<or> aswf' R3 = [a,c,b,d,e]"
      using aswf'_in_allowed_results[OF wf(3)] unfolding R_defs
      by (simp add: eval_allowed_results del: Set.filter_eq)
    moreover have "aswf' R3 \<noteq> [a,b,c,d,e] \<or> aswf' R \<noteq> [a,c,b,d,e]"
      by (intro kemeny_strategyproof_aswf'_strong wf)
         (simp_all add: R_defs insert_commute swap_dist_code' inversion_number_Cons)
    ultimately show ?thesis using R
      by blast
  qed

  show ?thesis
  proof -
    have "aswf' R4 \<in> {[a,b,c,d,e], [a,c,b,e,d], [a,b,c,e,d], [a,c,b,d,e]}"
      using aswf'_in_allowed_results[OF wf(4)] unfolding R_defs
      by (simp add: eval_allowed_results del: Set.filter_eq)
    moreover have "aswf' R4 \<noteq> [a,b,c,d,e] \<or> aswf' R3 \<noteq> [a,c,b,d,e]"
      by (intro kemeny_strategyproof_aswf'_strong wf)
         (simp_all add: R_defs insert_commute swap_dist_code' inversion_number_Cons)
    moreover have "aswf' R4 \<noteq> [a,c,b,e,d] \<or> aswf' R2 \<noteq> [a,c,b,d,e]"
      by (intro kemeny_strategyproof_aswf'_strong wf)
         (simp_all add: R_defs insert_commute swap_dist_code' inversion_number_Cons)
    ultimately show ?thesis using R2 R3 unfolding R4_def
      by blast
  qed
qed

lemma symmetry_breaking_aux2:
  obtains abcde where 
    "distinct abcde" "alts = set abcde" "length abcde = 5"
    "case abcde of [a,b,c,d,e] \<Rightarrow> aswf' {# [a,b,c,d,e], [a,c,b,e,d] #} = [a,b,c,d,e]"
proof -
  obtain abcde where abcde: "distinct abcde" "set abcde = alts"
    using finite_distinct_list by blast
  have "length abcde = 5"
    using card_alts abcde distinct_card by metis
  obtain a b c d e where abcde_expand: "abcde = [a,b,c,d,e]"
    using \<open>length abcde = 5\<close> by (force simp: eval_nat_numeral length_Suc_conv)
  have [simp]: "a \<noteq> b" "a \<noteq> c" "a \<noteq> d" "a \<noteq> e" "b \<noteq> a" "b \<noteq> c" "b \<noteq> d" "b \<noteq> e"
               "c \<noteq> a" "c \<noteq> b" "c \<noteq> d" "c \<noteq> e" "d \<noteq> a" "d \<noteq> b" "d \<noteq> c" "d \<noteq> e"
               "e \<noteq> a" "e \<noteq> b" "e \<noteq> c" "e \<noteq> d"
    using abcde(1) unfolding abcde_expand by (simp_all add: eq_commute)
  have alts_eq: "alts = {a,b,c,d,e}"
    unfolding abcde(2) [symmetric] abcde_expand by simp
  interpret anonymous_unanimous_kemenysp_swf_explicit agents alts swf 2 "[a,b,c,d,e]"
    by standard (simp_all add: alts_eq card_agents)

  define R where "R = {# [a,b,c,d,e], [a,c,b,e,d] #}"
  have R_wf: "is_apref_profile' R"
    unfolding R_def is_apref_profile'_def
    by (auto simp: card_agents abcde_expand simp flip: abcde(2) intro!: linorder_of_ranking)

  have "aswf' R \<in> {[a,b,c,d,e], [a,c,b,e,d]} \<or> aswf' R \<in> {[a,b,c,e,d], [a,c,b,d,e]}"
    using aswf'_in_allowed_results[OF R_wf] unfolding R_def
    by (simp add: eval_allowed_results del: Set.filter_eq)

  thus ?thesis
  proof
    assume *: "aswf' R \<in> {[a,b,c,d,e], [a,c,b,e,d]}"
    show ?thesis
      by (rule that[of "aswf' R"])
         (use * in \<open>unfold R_def, auto simp add: alts_eq insert_commute add_mset_commute\<close>)
  next
    assume "aswf' R \<in> {[a,b,c,e,d], [a,c,b,d,e]}"
    hence "aswf' R = [a,b,c,e,d] \<or> aswf' R = [a,c,b,d,e]"
      by blast
    thus ?thesis
    proof
      assume *: "aswf' R = [a,c,b,d,e]"
      have **: "aswf' {#[a,b,c,e,d], [a,c,b,d,e]#} \<in> {[a,b,c,e,d], [a,c,b,d,e]}"
        by (rule symmetry_breaking_aux1[of a b c d e])
           (use * in \<open>simp_all add: R_def add_mset_commute alts_eq\<close>)
      show ?thesis
        by (rule that[of "aswf' {#[a,b,c,e,d], [a,c,b,d,e]#}"])
           (use ** in \<open>auto simp: alts_eq add_mset_commute insert_commute\<close>)
    next
      assume *: "aswf' R = [a,b,c,e,d]"
      have **: "aswf' {#[a,c,b,d,e], [a,b,c,e,d]#} \<in> {[a,c,b,d,e], [a,b,c,e,d]}"
        by (rule symmetry_breaking_aux1[of a c b e d])
           (use * in \<open>simp_all add: R_def add_mset_commute alts_eq insert_commute\<close>)
      show ?thesis
        by (rule that[of "aswf' {#[a,b,c,e,d], [a,c,b,d,e]#}"])
           (use ** in \<open>auto simp: alts_eq add_mset_commute insert_commute\<close>)
    qed
  qed
qed

lemma contradiction: False
proof -
  obtain abcde where abcde:
     "distinct abcde" "alts = set abcde" "length abcde = 5"
     "case abcde of [a,b,c,d,e] \<Rightarrow> aswf' {# [a,b,c,d,e], [a,c,b,e,d] #} = [a,b,c,d,e]"
    using symmetry_breaking_aux2 .
  from \<open>length abcde = 5\<close> obtain a b c d e where abcde_expand: "abcde = [a,b,c,d,e]"
    by (auto simp: length_Suc_conv eval_nat_numeral)
  interpret anonymous_unanimous_kemenysp_swf_explicit_5_2 agents alts swf a b c d e
  proof
    show "aswf' {#[a, b, c, d, e], [a, c, b, e, d]#} = [a, b, c, d, e]"
      using abcde unfolding abcde_expand by simp
  qed (use abcde(1) in \<open>simp_all add: card_agents abcde abcde_expand eq_commute\<close>)
  show ?thesis
    by (fact contradiction)
qed

end

text \<open>
  Finally, we employ the usual construction of padding with dummy alternatives and cloning voters
  to extend the impossibility to any setting with $m\geq 5$ and $n$ even.
\<close>
theorem (in anonymous_unanimous_kemenysp_swf) impossibility:
  assumes "even (card agents)" and "card alts \<ge> 5"
  shows   False
proof -
  have "card agents > 0"
    using assms(1) finite_agents nonempty_agents by fastforce
  with assms(1) have "card agents \<ge> 2"
    by presburger
  obtain agents' where agents': "agents' \<subseteq> agents" "card agents' = 2"
    using \<open>card agents \<ge> 2\<close> by (meson obtain_subset_with_card_n)
  have [simp]: "agents' \<noteq> {}"
    using agents' by auto
  obtain alts' where alts': "alts' \<subseteq> alts" "card alts' = 5"
    using \<open>card alts \<ge> 5\<close> by (meson obtain_subset_with_card_n)
  obtain dummy_alts where alts_list': "mset dummy_alts = mset_set (alts - alts')"
    using ex_mset by blast
  obtain unclone where "cloning agents' agents unclone"
    using cloning_exists[of agents' agents] agents' \<open>even (card agents)\<close> finite_agents by auto
  interpret cloning agents' agents unclone by fact

  interpret split: swf_split_agents agents alts swf agents' unclone ..
  interpret new1: anonymous_swf agents' alts split.swf_low
    by (rule split.anonymous_clone) unfold_locales
  interpret new1: unanimous_swf agents' alts split.swf_low
    by (rule split.unanimous_clone) unfold_locales
  interpret new1: kemeny_strategyproof_swf agents' alts split.swf_low
    by (rule split.kemeny_strategyproof_clone) unfold_locales

  interpret restrict: unanimous_swf_restrict_alts agents' alts split.swf_low dummy_alts alts'
  proof
    show "finite alts'"
      using alts'(1) finite_subset by blast
    show "mset_set alts = mset dummy_alts + mset_set alts'"
      by (simp add: \<open>finite alts'\<close> alts'(1) alts_list' mset_set_Diff)
    show "alts' \<noteq> {}"
      using alts'(2) by fastforce
  qed
  interpret new2: anonymous_swf agents' alts' restrict.swf_low
    by (rule restrict.anonymous_restrict) unfold_locales
  interpret new2: unanimous_swf agents' alts' restrict.swf_low ..
  interpret new2: kemeny_strategyproof_swf agents' alts' restrict.swf_low
    by (rule restrict.kemeny_strategyproof_restrict) unfold_locales

  interpret new2: anonymous_unanimous_kemenysp_swf_5_2 agents' alts' restrict.swf_low
    by standard fact+
  show False
    by (fact new2.contradiction)
qed


subsection \<open>For 4 alternatives and 4 agents\<close>

text \<open>
  We now similarly show the impossibility for $m = n = 4$. The main difference now is that the
  number of profiles involved is much larger, namely 9900, so the approach of simply generating
  all strategyproofness clauses that arise between these profiles is no longer feasible.

  Instead we work with an explicit list of the required 254269 strategyproofness clauses that was
  extracted from an unsatisfiable core found with MUSer2.

  The symmetry-breaking assumption we use this time is that the profile where two agents report
  $abcd$ and the other two report $badc$ is mapped to $abcd$.
\<close>

external_file "sat_data/kemeny_sp_4_4.xz"
external_file "sat_data/kemeny_4_4.grat.xz"

locale anonymous_unanimous_kemenysp_swf_explicit_4_4 =
  anonymous_unanimous_kemenysp_swf_explicit agents alts swf 4 "[a,b,c,d]"
  for agents :: "'agent set" and alts :: "'alt set" and swf and a b c d +
  assumes symmetry_breaking: "aswf' {# [a,b,c,d], [a,b,c,d], [b,a,d,c], [b,a,d,c]  #} = [a,b,c,d]"
begin

(*
  This call can take a while (about 1.5 minutes on a 2024-ish 12-core machine).
  It is forked to the background though, so processing can continue immediately.
*)

local_setup \<open>fn lthy =>
  let 
    val params = {
      name = "kemeny_4_4",
      locale_thm = @{thm "anonymous_unanimous_kemenysp_swf_explicit_axioms"},
      profile_file = NONE,
      sp_file = SOME \<^path>\<open>sat_data/kemeny_sp_4_4.xz\<close>,
      grat_file = \<^path>\<open>sat_data/kemeny_4_4.grat.xz\<close>,
      extra_clauses = @{thms symmetry_breaking}
    }
    val thm =
      Goal.prove_future lthy [] [] \<^prop>\<open>False\<close>
        (fn {context, ...} => 
          HEADGOAL (resolve_tac context [Anon_Unan_Stratproof_Impossibility.derive_false context params]))
  in
    Local_Theory.note ((\<^binding>\<open>contradiction\<close>, []), [thm]) lthy |> snd
  end
\<close>

end


text \<open>
  We again get rid of the symmetry-breaking assumption. The argument is almost exactly the same
  one as before, except that we remove the alternative $a$ and all agents get cloned.
  Consequently, the arguments involving strategyproofness have to use the stronger notion of
  strategyproofness considering simultaneous deviations by clones.
\<close>

locale anonymous_unanimous_kemenysp_swf_4_4 = anonymous_unanimous_kemenysp_swf agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf +
  assumes card_agents: "card agents = 4"
  assumes card_alts:   "card alts = 4"
begin

sublocale anonymous_unanimous_swf agents alts swf ..

sublocale anonymous_kemeny_strategyproof_swf agents alts swf ..

lemma symmetry_breaking_aux1:
  assumes distinct: "distinct [a,b,c,d]" and alts_eq: "alts = {a,b,c,d}"
  defines "R \<equiv> repeat_mset 2 {# [a,b,c,d], [b,a,d,c] #}"
  assumes R: "aswf' R = [b,a,c,d]"
  shows   "aswf' (repeat_mset 2  {# [a,b,d,c], [b,a,c,d] #}) \<in> {[a,b,d,c], [b,a,c,d]}"
proof -
  have alts_eq': "alts = set [a,b,c,d]"
    by (simp add: alts_eq)
  have [simp]: "a \<noteq> b" "a \<noteq> c" "a \<noteq> d" "b \<noteq> a" "b \<noteq> c" "b \<noteq> d"
               "c \<noteq> a" "c \<noteq> b" "c \<noteq> d" "d \<noteq> a" "d \<noteq> b" "d \<noteq> c"
    using distinct by (simp_all add: eq_commute)
  interpret anonymous_unanimous_kemenysp_swf_explicit agents alts swf 4 "[a,b,c,d]"
    by standard (simp_all add: alts_eq card_agents)

  have R_wf: "is_apref_profile' R"
    unfolding is_apref_profile'_def by (auto simp: card_agents permutations_of_set_def alts_eq R_def)

  define R2 where "R2 = repeat_mset 2 {# [b,a,c,d], [b,a,d,c] #}"
  define R3 where "R3 = repeat_mset 2 {# [a,b,c,d], [b,a,c,d] #}"
  define R4 where "R4 = repeat_mset 2 {# [a,b,d,c], [b,a,c,d] #}"
  note R_defs = R_def R2_def R3_def R4_def

  have wf: "is_apref_profile' R" "is_apref_profile' R2" "is_apref_profile' R3" "is_apref_profile' R4"
    by (simp_all add: is_apref_profile'_iff R_defs add_mset_commute)

  have R2: "aswf' R2 = [b,a,c,d]"
  proof -
    have "aswf' R2 = [b,a,c,d] \<or> aswf' R2 = [b,a,d,c]"
      using aswf'_in_allowed_results[OF wf(2)] unfolding R_defs
      by (simp add: eval_allowed_results del: Set.filter_eq)
    moreover have "aswf' R2 \<noteq> [b,a,d,c] \<or> aswf' R \<noteq> [b,a,c,d]"
      by (intro kemeny_strategyproof_aswf'_clones[where A = "[b,a,c,d]" and n = 2] wf)
         (simp_all add: R_defs insert_commute swap_dist_code' inversion_number_Cons eval_nat_numeral)
    ultimately show ?thesis using R
      by blast
  qed

  have R3: "aswf' R3 = [b,a,c,d]"
  proof -
    have "aswf' R3 = [a,b,c,d] \<or> aswf' R3 = [b,a,c,d]"
      using aswf'_in_allowed_results[OF wf(3)] unfolding R_defs
      by (simp add: eval_allowed_results del: Set.filter_eq)
    moreover have "aswf' R3 \<noteq> [a,b,c,d] \<or> aswf' R \<noteq> [b,a,c,d]"
      by (intro kemeny_strategyproof_aswf'_clones[where A = "[b,a,c,d]" and n = 2] wf)
         (simp_all add: R_defs insert_commute swap_dist_code' inversion_number_Cons eval_nat_numeral)
    ultimately show ?thesis using R
      by blast
  qed

  show ?thesis
  proof -
    have "aswf' R4 \<in> {[a,b,c,d], [b,a,d,c], [a,b,d,c], [b,a,c,d]}"
      using aswf'_in_allowed_results[OF wf(4)] unfolding R_defs
      by (simp add: eval_allowed_results del: Set.filter_eq)
    moreover have "aswf' R3 \<noteq> [b,a,c,d] \<or> aswf' R4 \<noteq> [a,b,c,d]"
      by (intro kemeny_strategyproof_aswf'_clones[where A = "[a,b,c,d]" and n = 2] wf)
         (simp_all add: R_defs insert_commute swap_dist_code' inversion_number_Cons eval_nat_numeral)
    moreover have " aswf' R2 \<noteq> [b,a,c,d] \<or> aswf' R4 \<noteq> [b,a,d,c]"
      by (intro kemeny_strategyproof_aswf'_clones[where A = "[b,a,d,c]" and n = 2] wf)
         (simp_all add: R_defs insert_commute swap_dist_code' inversion_number_Cons eval_nat_numeral)
    ultimately show ?thesis using R2 R3 unfolding R4_def
      by blast
  qed
qed

lemma symmetry_breaking_aux2:
  obtains abcd where 
    "distinct abcd" "alts = set abcd" "length abcd =4"
    "case abcd of [a,b,c,d] \<Rightarrow> aswf' (repeat_mset 2 {# [a,b,c,d], [b,a,d,c] #}) = [a,b,c,d]"
proof -
  obtain abcd where abcd: "distinct abcd" "set abcd = alts"
    using finite_distinct_list by blast
  have "length abcd = 4"
    using card_alts abcd distinct_card by metis
  obtain a b c d where abcd_expand: "abcd = [a,b,c,d]"
    using \<open>length abcd = 4\<close> by (force simp: eval_nat_numeral length_Suc_conv)
  have [simp]: "a \<noteq> b" "a \<noteq> c" "a \<noteq> d""b \<noteq> a" "b \<noteq> c" "b \<noteq> d"
               "c \<noteq> a" "c \<noteq> b" "c \<noteq> d" "d \<noteq> a" "d \<noteq> b" "d \<noteq> c"
    using abcd(1) unfolding abcd_expand by (simp_all add: eq_commute)
  have alts_eq: "alts = {a,b,c,d}"
    unfolding abcd(2) [symmetric] abcd_expand by simp
  interpret anonymous_unanimous_kemenysp_swf_explicit agents alts swf 4 "[a,b,c,d]"
    by standard (simp_all add: alts_eq card_agents)

  define R where "R = repeat_mset 2 {# [a,b,c,d], [b,a,d,c] #}"
  have R_wf: "is_apref_profile' R"
    unfolding R_def is_apref_profile'_def
    by (auto simp: card_agents abcd_expand simp flip: abcd(2) intro!: linorder_of_ranking)

  have "aswf' R \<in> {[a,b,c,d], [b,a,d,c]} \<or> aswf' R \<in> {[a,b,d,c], [b,a,c,d]}"
    using aswf'_in_allowed_results[OF R_wf] unfolding R_def
    by (simp add: eval_allowed_results del: Set.filter_eq)

  thus ?thesis
  proof
    assume *: "aswf' R \<in> {[a,b,c,d], [b,a,d,c]}"
    show ?thesis
      by (rule that[of "aswf' R"])
         (use * in \<open>unfold R_def, auto simp add: alts_eq insert_commute add_mset_commute eval_nat_numeral\<close>)
  next
    assume "aswf' R \<in> {[a,b,d,c], [b,a,c,d]}"
    hence "aswf' R = [a,b,d,c] \<or> aswf' R = [b,a,c,d]"
      by blast
    thus ?thesis
    proof
      assume *: "aswf' R = [b,a,c,d]"
      have **: "aswf' (repeat_mset 2 {#[a,b,d,c], [b,a,c,d]#}) \<in> {[a,b,d,c], [b,a,c,d]}"
        by (rule symmetry_breaking_aux1[of a b c d])
           (use * in \<open>simp_all add: R_def add_mset_commute alts_eq\<close>)
      show ?thesis
        by (rule that[of "aswf' (repeat_mset 2 {#[a,b,d,c], [b,a,c,d]#})"])
           (use ** in \<open>auto simp: alts_eq add_mset_commute insert_commute add.commute\<close>)
    next
      assume *: "aswf' R = [a,b,d,c]"
      have **: "aswf' (repeat_mset 2 {#[b,a,c,d], [a,b,d,c]#}) \<in> {[b,a,c,d], [a,b,d,c]}"
        by (rule symmetry_breaking_aux1[of b a d c])
           (use * in \<open>simp_all add: R_def add_mset_commute alts_eq insert_commute\<close>)
      show ?thesis
        by (rule that[of "aswf' (repeat_mset 2 {#[a,b,d,c], [b,a,c,d]#})"])
           (use ** in \<open>auto simp: alts_eq add_mset_commute insert_commute add.commute\<close>)
    qed
  qed
qed

lemma contradiction: False
proof -
  obtain abcd where abcd:
     "distinct abcd" "alts = set abcd" "length abcd = 4"
     "case abcd of [a,b,c,d] \<Rightarrow> aswf' (repeat_mset 2 {# [a,b,c,d], [b,a,d,c] #}) = [a,b,c,d]"
    using symmetry_breaking_aux2 .
  from \<open>length abcd = 4\<close> obtain a b c d where abcd_expand: "abcd = [a,b,c,d]"
    by (auto simp: length_Suc_conv eval_nat_numeral)
  interpret anonymous_unanimous_kemenysp_swf_explicit_4_4 agents alts swf a b c d
  proof
    show "aswf' {#[a, b, c, d], [a, b, c, d], [b, a, d, c], [b, a, d, c]#} = [a, b, c, d]"
      using abcd unfolding abcd_expand by (simp add: eval_nat_numeral add_mset_commute)
  qed (use abcd(1) in \<open>simp_all add: card_agents abcd abcd_expand eq_commute\<close>)
  show ?thesis
    by (fact contradiction)
qed

end

text \<open>
  The final result: extending the impossibility to $m\geq 2$ and $n$ a multiple of 4.
\<close>
theorem (in anonymous_unanimous_kemenysp_swf) impossibility':
  assumes "4 dvd card agents" and "card alts \<ge> 4"
  shows   False
proof -
  have "card agents \<ge> 4"
    using assms(1) nonempty_agents finite_agents by (meson card_0_eq dvd_imp_le not_gr0)
  obtain agents' where agents': "agents' \<subseteq> agents" "card agents' = 4"
    using \<open>card agents \<ge> 4\<close> by (meson obtain_subset_with_card_n)
  have [simp]: "agents' \<noteq> {}"
    using agents' by auto
  obtain alts' where alts': "alts' \<subseteq> alts" "card alts' = 4"
    using \<open>card alts \<ge> 4\<close> by (meson obtain_subset_with_card_n)
  obtain dummy_alts where alts_list': "mset dummy_alts = mset_set (alts - alts')"
    using ex_mset by blast
  obtain unclone where "cloning agents' agents unclone"
    using cloning_exists[of agents' agents] agents' \<open>4 dvd card agents\<close> finite_agents by auto
  interpret cloning agents' agents unclone by fact

  interpret split: swf_split_agents agents alts swf agents' unclone ..
  interpret new1: anonymous_swf agents' alts split.swf_low
    by (rule split.anonymous_clone) unfold_locales
  interpret new1: unanimous_swf agents' alts split.swf_low
    by (rule split.unanimous_clone) unfold_locales
  interpret new1: kemeny_strategyproof_swf agents' alts split.swf_low
    by (rule split.kemeny_strategyproof_clone) unfold_locales

  interpret restrict: unanimous_swf_restrict_alts agents' alts split.swf_low dummy_alts alts'
  proof
    show "finite alts'"
      using alts'(1) finite_subset by blast
    show "mset_set alts = mset dummy_alts + mset_set alts'"
      by (simp add: \<open>finite alts'\<close> alts'(1) alts_list' mset_set_Diff)
    show "alts' \<noteq> {}"
      using alts'(2) by fastforce
  qed
  interpret new2: anonymous_swf agents' alts' restrict.swf_low
    by (rule restrict.anonymous_restrict) unfold_locales
  interpret new2: unanimous_swf agents' alts' restrict.swf_low ..
  interpret new2: kemeny_strategyproof_swf agents' alts' restrict.swf_low
    by (rule restrict.kemeny_strategyproof_restrict) unfold_locales

  interpret new2: anonymous_unanimous_kemenysp_swf_4_4 agents' alts' restrict.swf_low
    by standard fact+
  show False
    by (fact new2.contradiction)
qed

text \<open>
  The following collects thw two impossibility results in one theorem.
\<close>
theorem anonymous_unanimous_kemenysp_impossibility:
  assumes "(card alts = 4 \<and> 4 dvd card agents) \<or> (card alts \<ge> 5 \<and> even (card agents))"
  assumes "anonymous_swf agents alts swf"
  assumes "unanimous_swf agents alts swf"
  assumes "kemeny_strategyproof_swf agents alts swf"
  shows   False
proof -
  interpret anonymous_swf agents alts swf by fact
  interpret unanimous_swf agents alts swf by fact
  interpret kemeny_strategyproof_swf agents alts swf by fact
  interpret anonymous_unanimous_kemenysp_swf agents alts swf ..
  show False using assms(1) impossibility impossibility' by linarith
qed

end
