(*  
  Title:    SDS_Lowering.thy
  Author:   Manuel Eberl, TU München

  Allows to lower an SDS, i.e. take an existing ex-post efficient SDS
  and construct from it an SDS for fewer agents and alternatives. (which is
  also ex-post efficient)
    The standard properties (anonymity, neutrality, SD efficiency, strategyproofness)
  are preserved by this construction.
*)

section \<open>Lowering Social Decision Schemes\<close>

theory SDS_Lowering
imports Social_Decision_Schemes
begin

definition lift_pref_profile :: 
    "'agent set \<Rightarrow> 'alt set \<Rightarrow> 'agent set \<Rightarrow> 'alt set \<Rightarrow>
       ('agent, 'alt) pref_profile \<Rightarrow> ('agent, 'alt) pref_profile" where
  "lift_pref_profile agents alts agents' alts' R = (\<lambda>i x y. 
     x \<in> alts' \<and> y \<in> alts' \<and> i \<in> agents' \<and>
     (x = y \<or> x \<notin> alts \<or> i \<notin> agents \<or> (y \<in> alts \<and> R i x y)))"

lemma lift_pref_profile_wf:
  assumes "pref_profile_wf agents alts R"
  assumes "agents \<subseteq> agents'" "alts \<subseteq> alts'" "finite alts'"
  defines "R' \<equiv> lift_pref_profile agents alts agents' alts' R"
  shows   "pref_profile_wf agents' alts' R'"
proof -
  from assms interpret R: pref_profile_wf agents alts by simp
  have "finite_total_preorder_on alts' (R' i)" 
    if i: "i \<in> agents'" for i
  proof (cases "i \<in> agents")
    case True
    then interpret finite_total_preorder_on alts "R i" by simp
    from True assms show ?thesis
      by unfold_locales (auto simp: lift_pref_profile_def dest: total intro: trans)
  next 
    case False
    with assms i show ?thesis
      by unfold_locales (simp_all add: lift_pref_profile_def)
  qed
  moreover have "R' i = (\<lambda>_ _. False)" if "i \<notin> agents'" for i
    unfolding lift_pref_profile_def R'_def using that by simp
  ultimately show ?thesis unfolding pref_profile_wf_def using assms by auto
qed

lemma lift_pref_profile_permute_agents:
  assumes "\<pi> permutes agents" "agents \<subseteq> agents'"
  shows   "lift_pref_profile agents alts agents' alts' (R \<circ> \<pi>) = 
             lift_pref_profile agents alts agents' alts' R \<circ> \<pi>"
  using assms permutes_subset[OF assms]
  by (auto simp add: lift_pref_profile_def o_def permutes_in_image)

lemma lift_pref_profile_permute_alts:
  assumes "\<sigma> permutes alts" "alts \<subseteq> alts'"
  shows   "lift_pref_profile agents alts agents' alts' (permute_profile \<sigma> R) = 
             permute_profile \<sigma> (lift_pref_profile agents alts agents' alts' R)"
proof -
  from assms have "inv \<sigma> permutes alts" by (intro permutes_inv)
  moreover from this and assms(2) have "inv \<sigma> permutes alts'" by (rule permutes_subset)
  ultimately show ?thesis using assms permutes_inj[OF \<open>inv \<sigma> permutes alts\<close>]
    by (fastforce simp add: lift_pref_profile_def permutes_in_image
          permute_profile_def fun_eq_iff dest: injD)
qed



context
  fixes agents alts R agents' alts' R'
  assumes R_wf: "pref_profile_wf agents alts R"
  assumes election: "agents \<subseteq> agents'" "alts \<subseteq> alts'" "alts \<noteq> {}" "agents \<noteq> {}" "finite alts'"
  defines "R' \<equiv> lift_pref_profile agents alts agents' alts' R"
begin

interpretation R: pref_profile_wf agents alts R by fact
interpretation R': pref_profile_wf agents' alts' R' 
  using election R_wf by (simp add: R'_def lift_pref_profile_wf)

lemma lift_pref_profile_strict_iff:
  "x \<prec>[lift_pref_profile agents alts agents' alts' R i] y \<longleftrightarrow>
     i \<in> agents \<and> ((y \<in> alts \<and> x \<in> alts' - alts) \<or> x \<prec>[R i] y)"
proof (cases "i \<in> agents")
  case True
  then interpret total_preorder_on alts "R i" by simp
  show ?thesis using not_outside election
    by (auto simp: lift_pref_profile_def strongly_preferred_def)
qed (simp_all add: lift_pref_profile_def strongly_preferred_def)

lemma preferred_alts_lift_pref_profile: 
  assumes i: "i \<in> agents'" and x: "x \<in> alts'"
  shows   "preferred_alts (R' i) x = 
             (if i \<in> agents \<and> x \<in> alts then preferred_alts (R i) x else alts')"
proof (cases "i \<in> agents")
  assume i: "i \<in> agents"
  then interpret Ri: total_preorder_on alts "R i" by simp
  show ?thesis
  using i x election Ri.not_outside
    by (auto simp: preferred_alts_def R'_def lift_pref_profile_def Ri.refl)
qed (auto simp: preferred_alts_def R'_def lift_pref_profile_def i x)


lemma pareto_losers_lift_pref_profile:
  shows   "pareto_losers R' = pareto_losers R \<union> (alts' - alts)"
proof safe
  fix x assume "x \<in> pareto_losers R'"
  thus "x \<in> alts'" using R'.pareto_loser_in_alts by blast
next
  fix x assume x: "x \<in> pareto_losers R'" "x \<notin> pareto_losers R" "x \<in> alts"
  from x(1) obtain y where y: "y \<succ>[Pareto(R')] x" by (auto simp: pareto_losers_def)

  have "y \<succeq>[R i] x" if i: "i \<in> agents" for i
  proof -
    from i interpret total_preorder_on alts "R i" by simp
    from y i election have "y \<succeq>[R' i] x" by (auto simp: R'.Pareto_strict_iff)
    with i x show "y \<succeq>[R i] x" by (auto simp: R'_def lift_pref_profile_def refl)
  qed
  moreover from y obtain i where "i \<in> agents'" "y \<succ>[R' i] x" by (auto simp: R'.Pareto_strict_iff)
  with x have "i \<in> agents" "y \<succ>[R i] x" by (auto simp: R'_def lift_pref_profile_strict_iff)
  ultimately have "y \<succ>[Pareto(R)] x" unfolding R.Pareto_strict_iff by auto
  with x show False by (simp add: pareto_losers_def)
next
  fix x assume "x \<in> pareto_losers R"
  then obtain y where y: "y \<succ>[Pareto(R)] x" by (auto simp: pareto_losers_def)
  hence [simp]: "x \<in> alts" "y \<in> alts"
    using R.Pareto.not_outside[of x y] by (simp_all add: strongly_preferred_def)
  
  have "y \<succeq>[R' i] x" if i: "i \<in> agents'" for i
  proof (cases "i \<in> agents")
    case True
    from y True election have "y \<succeq>[R i] x" by (auto simp: R.Pareto_strict_iff)
    with i election show "y \<succeq>[R' i] x" by (auto simp: R'_def lift_pref_profile_def refl)
  qed (insert election i, auto simp: R'_def lift_pref_profile_def)
  moreover from y obtain i where "i \<in> agents" "y \<succ>[R i] x" by (auto simp: R.Pareto_strict_iff)
  with election have "i \<in> agents'" "y \<succ>[R' i] x" 
    by (auto simp: R'_def lift_pref_profile_strict_iff)
  ultimately have "y \<succ>[Pareto(R')] x" unfolding R'.Pareto_strict_iff by auto
  thus "x \<in> pareto_losers R'" by (rule pareto_losersI)
next
  fix x assume x: "x \<in> alts'" "x \<notin> alts"
  from \<open>agents \<noteq> {}\<close> obtain i where i: "i \<in> agents" by blast
  from \<open>alts \<noteq> {}\<close> obtain y where y: "y \<in> alts" by blast
  from R_wf election interpret pref_profile_wf agents' alts' R'
    unfolding R'_def by (intro lift_pref_profile_wf) auto

  from x y election have "y \<succeq>[R' j] x" if "j \<in> agents'" for j
    using that by (auto simp: R'_def lift_pref_profile_def)
  moreover from i election have "i \<in> agents'" by blast
  moreover from x y i election have "y \<succ>[R' i] x"
    by (auto simp: strongly_preferred_def R'_def lift_pref_profile_def)
  ultimately show "x \<in> pareto_losers R'" by (rule pareto_losersI[OF R'.Pareto_strictI])
qed

end


locale sds_lowering = 
  ex_post_efficient_sds agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds +
  fixes agents' alts' 
  assumes agents'_subset: "agents' \<subseteq> agents" and alts'_subset: "alts' \<subseteq> alts"
      and agents'_nonempty [simp]: "agents' \<noteq> {}" and alts'_nonempty [simp]: "alts' \<noteq> {}"
begin

lemma finite_agents' [simp]: "finite agents'"
  using agents'_subset finite_agents by (rule finite_subset)

lemma finite_alts' [simp]: "finite alts'"
  using alts'_subset finite_alts by (rule finite_subset)

abbreviation lift :: "('agent, 'alt) pref_profile \<Rightarrow> ('agent, 'alt) pref_profile" where
  "lift \<equiv> lift_pref_profile agents' alts' agents alts"

definition lowered :: "('agent, 'alt) pref_profile \<Rightarrow> 'alt lottery" where
  "lowered = sds \<circ> lift"

lemma lift_wf [simp, intro]: 
  "pref_profile_wf agents' alts' R \<Longrightarrow> is_pref_profile (lift R)"
  using alts'_subset agents'_subset by (intro lift_pref_profile_wf) simp_all

sublocale lowered: election agents' alts'
  by unfold_locales simp_all

lemma preferred_alts_lift:
  "lowered.is_pref_profile R \<Longrightarrow> i \<in> agents \<Longrightarrow> x \<in> alts \<Longrightarrow>
     preferred_alts (lift R i) x = 
       (if i \<in> agents' \<and> x \<in> alts' then preferred_alts (R i) x else alts)"
  using alts'_subset agents'_subset
  by (intro preferred_alts_lift_pref_profile) simp_all

lemma pareto_losers_lift:
  "lowered.is_pref_profile R \<Longrightarrow> pareto_losers (lift R) = pareto_losers R \<union> (alts - alts')"
  using agents'_subset alts'_subset by (intro pareto_losers_lift_pref_profile) simp_all

lemma lowered_lotteries: "lowered.lotteries \<subseteq> lotteries"
  unfolding lotteries_on_def using alts'_subset by blast

sublocale lowered: social_decision_scheme agents' alts' lowered
proof
  fix R assume R_wf: "pref_profile_wf agents' alts' R"
  from R_wf have R'_wf: "pref_profile_wf agents alts (lift R)" by (rule lift_wf)
  show "lowered R \<in> lowered.lotteries" unfolding lotteries_on_def
  proof safe
    fix x assume "x \<in> set_pmf (lowered R)"
    hence x: "x \<in> set_pmf (sds (lift R))" by (simp add: lowered_def)
    with ex_post_efficient[OF R'_wf]
      have "x \<notin> pareto_losers (lift R)" by blast
    with pareto_losers_lift[OF R_wf]
      have "x \<notin> alts - alts'" by blast
    moreover from x have "x \<in> alts" using sds_wf[OF R'_wf] 
      by (auto simp: lotteries_on_def)
    ultimately show "x \<in> alts'" by simp
  qed
qed

sublocale ex_post_efficient_sds agents' alts' lowered
proof
  fix R assume R_wf: "lowered.is_pref_profile R"
  hence "is_pref_profile (lift R)" by simp
  have "set_pmf (lowered R) \<inter> pareto_losers (lift R) = {}"
    unfolding lowered_def o_def by (intro ex_post_efficient lift_wf R_wf)
  also have "pareto_losers (lift R) = pareto_losers R \<union> (alts - alts')"
    by (intro pareto_losers_lift R_wf)
  finally show "set_pmf (lowered R) \<inter> pareto_losers R = {}" by blast
qed

lemma lowered_in_lotteries [simp]: "lowered.is_pref_profile R \<Longrightarrow> lowered R \<in> lotteries"
  using lowered.sds_wf[of R] lowered_lotteries by blast

end



locale sds_lowering_anonymous =
  anonymous_sds agents alts sds +
  sds_lowering agents alts sds agents' alts'
  for agents :: "'agent set" and alts :: "'alt set" and sds agents' alts'
begin

sublocale lowered: anonymous_sds agents' alts' lowered
proof
  fix \<pi> R assume perm: "\<pi> permutes agents'" and R_wf: "lowered.is_pref_profile R"
  from perm have "lift (R \<circ> \<pi>) = lift R \<circ> \<pi>"
    using agents'_subset by (rule lift_pref_profile_permute_agents)
  hence "sds (lift (R \<circ> \<pi>)) = sds (lift R \<circ> \<pi>)" by simp
  also from perm R_wf have "\<pi> permutes agents" "is_pref_profile (lift R)"
    using agents'_subset by (auto dest: permutes_subset)
  from anonymous[OF this] have "sds (lift R \<circ> \<pi>) = sds (lift R)"
    by (simp add: lowered_def)
  finally show "lowered (R \<circ> \<pi>) = lowered R" unfolding lowered_def o_def .
qed

end

locale sds_lowering_neutral =
  neutral_sds agents alts sds +
  sds_lowering agents alts sds agents' alts'
  for agents :: "'agent set" and alts :: "'alt set" and sds agents' alts'
begin

sublocale lowered: neutral_sds agents' alts' lowered
proof
  fix \<sigma> R assume perm: "\<sigma> permutes alts'" and R_wf: "lowered.is_pref_profile R"
  from perm alts'_subset 
    have "lift (permute_profile \<sigma> R) = permute_profile \<sigma> (lift R)"
    by (rule lift_pref_profile_permute_alts)
  hence "sds (lift (permute_profile \<sigma> R)) = sds (permute_profile \<sigma> (lift R))" by simp
  also from R_wf perm have "is_pref_profile (lift R)" by simp
  with perm alts'_subset 
    have "sds (permute_profile \<sigma> (lift R)) = map_pmf \<sigma> (sds (lift R))"
    by (intro neutral) (auto intro: permutes_subset)
  finally show "lowered (permute_profile \<sigma> R) = map_pmf \<sigma> (lowered R)"
    by (simp add: lowered_def o_def)
qed

end

locale sds_lowering_sd_efficient =
  sd_efficient_sds agents alts sds +
  sds_lowering agents alts sds agents' alts'
  for agents :: "'agent set" and alts :: "'alt set" and sds agents' alts'
begin

sublocale sd_efficient_sds agents' alts' lowered
proof
  fix R assume R_wf: "lowered.is_pref_profile R"
  interpret R: pref_profile_wf agents' alts' R by fact
  show "SD_efficient R (lowered R)"
  proof (unfold R.SD_efficient_def, safe)
    fix q i 
    assume q: "q \<in> lowered.lotteries"
    assume i: "i \<in> agents'"
    assume weak: "\<forall>i\<in>agents'. q \<succeq>[SD(R i)] lowered R"
    assume strong: "q \<succ>[SD(R i)] lowered R"
    from R_wf interpret R': pref_profile_wf agents alts "lift R" by simp

    have pmf_zero: "pmf (lowered R) x = 0" if x: "x \<notin> alts'" for x
      using x lowered.sds_wf[OF R_wf]
      by (auto simp: lotteries_on_def set_pmf_eq lift_pref_profile_def)

    from SD_efficient have "SD_efficient (lift R) (lowered R)" unfolding lowered_def o_def
      using R_wf by simp
    moreover have q': "q \<in> lotteries" using q lowered_lotteries by blast
    moreover have "q \<succeq>[SD(lift R i)] lowered R" if i: "i \<in> agents" for i
    proof (cases "i \<in> agents'")
      assume i: "i \<in> agents'"
      with agents'_subset have [simp]: "i \<in> agents" by blast
      show ?thesis
      proof (rule R'.SD_pref_profileI) 
        fix x assume x: "x \<in> alts"
        show "lowered.lottery_prob (lowered R) (preferred_alts (lift R i) x)
                \<le> lowered.lottery_prob q (preferred_alts (lift R i) x)"
        using i bspec[OF weak i] agents'_subset R_wf x q' lowered_lotteries
          by (simp add: lottery_prob_alts R.SD_pref_profile preferred_alts_lift)
      qed (auto simp: lowered.sds_wf R_wf q')
    next
      assume i': "i \<notin> agents'"
      from i have "total_preorder_on alts (lift R i)" by simp
      with i' agents'_subset i q q' R_wf show ?thesis
        by (intro R'.SD_pref_profileI)
           (auto intro!: lowered.sds_wf 
                 simp: lift_pref_profile_def preferred_alts_def lottery_prob_alts)
    qed
    moreover have "\<exists>i\<in>agents. \<not>(q \<preceq>[SD(lift R i)] lowered R)"
    proof
      from i agents'_subset show i': "i \<in> agents" by blast
      from i interpret R: total_preorder_on alts' "R i"
        using R_wf by (simp add: i)
      from strong have "\<not>(q \<preceq>[SD(R i)] lowered R)" 
        by (simp add: strongly_preferred_def)
      then obtain x where x: "x \<in> alts'" and
         "lowered.lottery_prob (lowered R) (preferred_alts (R i) x)
           < lowered.lottery_prob q (preferred_alts (R i) x)"
        using q i R_wf by (force simp: R.SD_pref_profile lowered.sds_wf)
      moreover from x alts'_subset have "x \<in> alts" by blast
      ultimately show "\<not>(q \<preceq>[SD(lift R i)] lowered R)"
        using q i i' R_wf 
        by (auto intro!: bexI[of _ x] lowered.sds_wf 
                 simp: preferred_alts_lift not_le R'.SD_pref_profile)
    qed
    ultimately show False by (rule R'.SD_efficientD)
  qed
qed

end


locale sds_lowering_strategyproof =
  strategyproof_sds agents alts sds +
  sds_lowering agents alts sds agents' alts'
  for agents :: "'agent set" and alts :: "'alt set" and sds agents' alts'
begin

sublocale strategyproof_sds agents' alts' lowered
proof (unfold_locales, safe)
  fix R i Ri'
  assume R_wf: "lowered.is_pref_profile R" and i: "i \<in> agents'"
  assume Ri': "total_preorder_on alts' Ri'"
  assume manipulable: "lowered.manipulable_profile R i Ri'"
  from i agents'_subset have i': "i \<in> agents" by blast
  interpret R: pref_profile_wf agents' alts' R by fact
  from R_wf interpret liftR: pref_profile_wf agents alts "lift R" by simp
 
  def lift_Ri' \<equiv> "\<lambda>x y. x \<in> alts \<and> y \<in> alts \<and> (x = y \<or> x \<notin> alts' \<or> (y \<in> alts' \<and> Ri' x y))"
  def S \<equiv> "(lift R)(i := lift_Ri')"
  from Ri' interpret Ri': total_preorder_on alts' Ri' .
  have [simp]: "total_preorder_on alts lift_Ri'" using Ri'.total
    by unfold_locales (auto simp: lift_Ri'_def intro: Ri'.trans)
  from lift_wf[OF R_wf] Ri' i agents'_subset have [simp]: "sds S \<in> lotteries" 
    by (auto intro!: sds_wf simp: S_def pref_profile_wf_def)

  have "manipulable_profile (lift R) i lift_Ri'"
  proof -
    from manipulable have "sds (lift R) \<prec>[SD (R i)] sds (lift (R(i := Ri')))" 
      unfolding lowered.manipulable_profile_def unfolding lowered_def o_def .
    also from i agents'_subset have "lift (R(i := Ri')) = S"
      by (intro ext) (auto simp: lift_pref_profile_def lift_Ri'_def S_def)
    finally show ?thesis using i i' alts'_subset R_wf
      unfolding manipulable_profile_def S_def [symmetric] strongly_preferred_def
      by (auto simp: R.SD_pref_profile liftR.SD_pref_profile sds_wf
            lottery_prob_alts preferred_alts_lift)
  qed
  moreover from R_wf i agents'_subset
    have "\<not>manipulable_profile (lift R) i lift_Ri'"
    by (intro strategyproof) auto
  ultimately show False by contradiction
qed

end


locale sds_lowering_anonymous_neutral_sdeff_stratproof =
  sds_lowering_anonymous + sds_lowering_neutral + 
  sds_lowering_sd_efficient + sds_lowering_strategyproof

end