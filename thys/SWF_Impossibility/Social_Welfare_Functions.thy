section \<open>Social welfare functions\<close>
theory Social_Welfare_Functions
imports
  "Swap_Distance.Swap_Distance"
  "Rankings.Topological_Sortings_Rankings"
  "Randomised_Social_Choice.Preference_Profiles"
  SWF_Impossibility_Library
begin

subsection \<open>Preference profiles\<close>

text \<open>
  In the context of social welfare functions, a preference profile consists of a linear ordering
  (a \<^emph>\<open>ranking\<close>) of alternatives for each agent.
\<close>

locale pref_profile_linorder_wf =
  fixes agents :: "'agent set" and alts :: "'alt set" and R :: "('agent, 'alt) pref_profile"
  assumes nonempty_agents [simp]: "agents \<noteq> {}" and nonempty_alts [simp]: "alts \<noteq> {}"
  assumes prefs_wf [simp]: "i \<in> agents \<Longrightarrow> finite_linorder_on alts (R i)"
  assumes prefs_undefined [simp]: "i \<notin> agents \<Longrightarrow> \<not>R i x y"
begin

lemma finite_alts [simp]: "finite alts"
proof -
  from nonempty_agents obtain i where "i \<in> agents" by blast
  then interpret finite_linorder_on alts "R i" by simp
  show ?thesis by (rule finite_carrier)
qed

lemma prefs_wf' [simp]:
  "i \<in> agents \<Longrightarrow> linorder_on alts (R i)"
  using prefs_wf[of i] by (simp_all add: finite_linorder_on_def del: prefs_wf)

lemma not_outside: 
  assumes "x \<preceq>[R i] y"
  shows   "i \<in> agents" "x \<in> alts" "y \<in> alts"
proof -
  from assms show "i \<in> agents" by (cases "i \<in> agents") auto
  then interpret linorder_on alts "R i" by simp
  from assms show "x \<in> alts" "y \<in> alts" by (simp_all add: not_outside)
qed

sublocale linorder_family agents alts R
proof
  fix i assume "i \<in> agents"
  thus "linorder_on alts (R i)"
    by simp
qed auto

lemmas prefs_undefined' = not_in_dom'

lemma wf_update:
  assumes "i \<in> agents" "linorder_on alts Ri'"
  shows   "pref_profile_linorder_wf agents alts (R(i := Ri'))"
proof -
  interpret linorder_on alts Ri' by fact
  from finite_alts have "finite_linorder_on alts Ri'" by unfold_locales
  with assms show ?thesis
    by (auto intro!: pref_profile_linorder_wf.intro split: if_splits)
qed

lemma wf_permute_agents:
  assumes "\<sigma> permutes agents"
  shows   "pref_profile_linorder_wf agents alts (R \<circ> \<sigma>)"
  unfolding o_def using permutes_in_image[OF assms(1)]
  by (intro pref_profile_linorder_wf.intro prefs_wf) simp_all

lemma (in -) pref_profile_eqI:
  assumes "pref_profile_linorder_wf agents alts R1" "pref_profile_linorder_wf agents alts R2"
  assumes "\<And>x. x \<in> agents \<Longrightarrow> R1 x = R2 x"
  shows   "R1 = R2"
proof
  interpret R1: pref_profile_linorder_wf agents alts R1 by fact
  interpret R2: pref_profile_linorder_wf agents alts R2 by fact
  fix x show "R1 x = R2 x"
    by (cases "x \<in> agents"; intro ext) (simp_all add: assms(3)) 
qed

text \<open>
  An obvious fact: if the number of agents is at most 2 and there are no ties then the majority
  relation coincides with the unanimity relation.
\<close>
lemma card_agents_le_2_imp_majority_eq_unanimity:
  assumes "card agents \<le> 2" and [simp]: "finite agents"
  assumes "linorder_on alts (majority R)"
  shows   "majority R = Pareto R"
proof (intro ext)
  fix x y
  interpret maj: linorder_on alts "majority R" by fact
  show "majority R x y = Pareto R x y"
  proof (cases "x \<in> alts \<and> y \<in> alts")
    case xy: True
    define d where "d = card {i\<in>agents. R i x y}"
    have neq: "x \<noteq> y" if "d \<noteq> card agents"
    proof
      assume "x = y"
      hence "{i\<in>agents. R i x y} = agents"
        using preorder_on.refl[OF in_dom] xy by auto
      thus False
        using that by (simp add: d_def)
    qed

    have "d = 0 \<or> d = card agents"
    proof (rule ccontr)
      assume "\<not>(d = 0 \<or> d = card agents)"
      moreover have "d \<le> card agents"
        unfolding d_def by (rule card_mono) auto
      ultimately have "d > 0" "d < card agents"
        by simp_all
      hence "d = 1" "card agents = 2"
        using \<open>card agents \<le> 2\<close> by linarith+
      have "x \<noteq> y"
        by (rule neq) (use \<open>d < card agents\<close> in auto)
      have "majority R x y \<and> majority R y x"
        using \<open>d = 1\<close> \<open>card agents = 2\<close> \<open>x \<noteq> y\<close> xy majority_iff_ge_half[of x y]
              majority_iff_le_half[of y x]
        by (simp add: d_def)
      thus False
        using maj.antisymmetric xy \<open>x \<noteq> y\<close> by blast
    qed

    thus ?thesis
    proof
      assume "d = 0"
      have "majority R x y \<longleftrightarrow> 2 * d \<ge> card agents"
        unfolding d_def using xy by (auto simp: majority_iff_ge_half)
      with \<open>d = 0\<close> have "\<not>majority R x y"
        by simp
      moreover from \<open>d = 0\<close> have "\<forall>i\<in>agents. \<not>R i x y"
        unfolding d_def by simp
      hence "\<not>Pareto R x y"
        by (auto simp: Pareto_iff)
      ultimately show ?thesis
        by simp
    next
      assume "d = card agents"
      have "majority R x y \<longleftrightarrow> 2 * d \<ge> card agents"
        unfolding d_def using xy by (subst majority_iff_ge_half) auto
      with \<open>d = card agents\<close> have "majority R x y"
        by simp
      moreover have "{i\<in>agents. R i x y} = agents"
        by (rule card_subset_eq) (use \<open>d = card agents\<close> in \<open>simp_all add: d_def\<close>)
      hence "Pareto R x y"
        by (auto simp: Pareto_iff)
      ultimately show ?thesis
        by simp
    qed
  qed (use Pareto.not_outside in \<open>auto simp: majority_iff'\<close>)
qed

end


text \<open>
  An \<^emph>\<open>election\<close>, in our terminology, consists of a finite set of agents and a finite non-empty 
  set of alternatives. It is this context in which we then consider all the set of possible
  preference profiles and SWFs.
\<close>
locale linorder_election = 
  fixes agents :: "'agent set" and alts :: "'alt set"
  assumes finite_agents [simp, intro]: "finite agents"
  assumes finite_alts [simp, intro]: "finite alts"
  assumes nonempty_agents [simp]: "agents \<noteq> {}"
  assumes nonempty_alts [simp]: "alts \<noteq> {}"
begin

abbreviation "is_pref_profile \<equiv> pref_profile_linorder_wf agents alts"

lemma finite_linorder_on_iff' [simp]:
  "finite_linorder_on alts R \<longleftrightarrow> linorder_on alts R"
  by (simp add: finite_linorder_on_def finite_linorder_on_axioms_def)

lemma finite_pref_profiles [intro]: "finite {R. is_pref_profile R}"
  and card_pref_profiles:   "card {R. is_pref_profile R} = fact (card alts) ^ card agents"
proof -
  define f :: "('agent \<Rightarrow> 'alt relation) \<Rightarrow> 'agent \<Rightarrow> 'alt relation"
    where "f = (\<lambda>R i. if i \<in> agents then R i else (\<lambda>_ _. False))"
  define g :: "('agent \<Rightarrow> 'alt relation) \<Rightarrow> 'agent \<Rightarrow> 'alt relation"
    where "g = (\<lambda>R. restrict R agents)"
  have bij: "bij_betw f (agents \<rightarrow>\<^sub>E {R. linorder_on alts R}) {R. is_pref_profile R}"
    by (rule bij_betwI[of _  _ _ g])
       (auto simp: f_def g_def pref_profile_linorder_wf_def fun_eq_iff)
  have "finite (agents \<rightarrow>\<^sub>E {R. linorder_on alts R})"
    by (intro finite_PiE finite_linorders_on) auto
  thus "finite {R. is_pref_profile R}"
    using bij_betw_finite[OF bij] by simp
  show "card {R. is_pref_profile R} = fact (card alts) ^ card agents"
    using bij_betw_same_card[OF bij] by (simp add: card_PiE card_linorders_on)
qed

lemma pref_profile_exists: "\<exists>R. is_pref_profile R"
proof -
  have "card {R. is_pref_profile R} > 0"
    by (subst card_pref_profiles) auto
  thus ?thesis
    by (simp add: card_gt_0_iff)
qed

lemma pref_profile_wfI' [intro?]:
  "(\<And>i. i \<in> agents \<Longrightarrow> linorder_on alts (R i)) \<Longrightarrow>
   (\<And>i. i \<notin> agents \<Longrightarrow> R i = (\<lambda>_ _. False)) \<Longrightarrow> is_pref_profile R"
  by (simp add: pref_profile_linorder_wf_def finite_linorder_on_def finite_linorder_on_axioms_def)

lemma is_pref_profile_update [simp,intro]:
  assumes "is_pref_profile R" "linorder_on alts Ri'" "i \<in> agents"
  shows   "is_pref_profile (R(i := Ri'))"
  using assms by (auto intro!: pref_profile_linorder_wf.wf_update)

lemma election [simp,intro]: "linorder_election agents alts"
  by (rule linorder_election_axioms)

end



subsection \<open>Definition and desirable properties of SWFs\<close>

locale social_welfare_function = linorder_election agents alts
  for agents :: "'agent set" and alts :: "'alt set" +
  fixes swf :: "('agent, 'alt) pref_profile \<Rightarrow> 'alt relation"
  assumes swf_wf: "is_pref_profile R \<Longrightarrow> linorder_on alts (swf R)"
begin

lemma swf_wf':
  assumes "is_pref_profile R"
  shows   "finite_linorder_on alts (swf R)"
proof -
  interpret linorder_on alts "swf R"
    by (rule swf_wf) fact
  show ?thesis
    by standard auto
qed

end

lemma (in linorder_election) social_welfare_functionI [intro]:
  "(\<And>R. is_pref_profile R \<Longrightarrow> linorder_on alts (swf R)) \<Longrightarrow> social_welfare_function agents alts swf"
  unfolding social_welfare_function_def social_welfare_function_axioms_def 
  using linorder_election_axioms
  by blast


text \<open>
  Anonymity: the identities of the agents do not matter, i.e.\ the SWF is stable under renaming
  of the authors.
\<close>
locale anonymous_swf = social_welfare_function agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf +
  assumes anonymous: "\<pi> permutes agents \<Longrightarrow> is_pref_profile R \<Longrightarrow> swf (R \<circ> \<pi>) = swf R"

text \<open>
  An obvious fact: if there is only one agent, any SWF is anonymous.
\<close>
lemma (in social_welfare_function) one_agent_imp_anonymous:
  assumes "card agents = 1"
  shows   "anonymous_swf agents alts swf"
proof
  fix \<pi> R assume \<pi>: "\<pi> permutes agents" and R: "is_pref_profile R"
  from \<pi> have "\<pi> = id"
    by (metis assms card_1_singletonE permutes_sing)
  thus "swf (R \<circ> \<pi>) = swf R"
    by simp
qed


text \<open>
  Neutrality: the identities of the alternatives does not matter, i.e.\ the SWF commutes with
  renaming the alternatives.

  This is not a particularly interesting property since it clashes with anonymity whenever
  tie-breaking is required.
\<close>
locale neutral_swf = social_welfare_function agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf +
  assumes neutral: "\<sigma> permutes alts \<Longrightarrow> is_pref_profile R \<Longrightarrow> 
                      swf (map_relation \<sigma> \<circ> R) = map_relation \<sigma> (swf R)"


text \<open>
  Unanimity: any ordering of two alternatives that all agents agree on is also present in the
  result ranking.
\<close>
locale unanimous_swf = social_welfare_function agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf +
  assumes unanimous: "is_pref_profile R \<Longrightarrow> \<forall>i\<in>agents. x \<succ>[R i] y \<Longrightarrow> x \<succ>[swf R] y"
begin

lemma unanimous':
  assumes "is_pref_profile R" "\<forall>i\<in>agents. x \<succeq>[R i] y"
  shows   "x \<succeq>[swf R] y"
  using assms
  by (metis linorder_on_def order_on.antisymmetric order_on_def 
            pref_profile_linorder_wf.not_outside(2) pref_profile_linorder_wf.prefs_wf'
            preorder_on.refl strongly_preferred_def swf_wf unanimous)


text \<open>
  A more convenient form of unanimity for computation: the SWF must return a ranking that is
  a topological sorting of the Pareto dominance relation.

  In other words: we define the relation $P$ as the intersection of all the preference relations of
  the agents. This relation is a partial order that captures everything the agents agree on. Due to
  unanimity, the result returned by the SWF must be a linear ordering that extends $P$, i.e.\ a
  topological sorting of $P$.

  These topological sortings can be computed relatively easily using the standard algorithm, i.e.\ 
  repeatedly picking a maximal element nondeterministically and putting it as the next element of
  the result ranking.

  If the number of possible rankings is relatively small, this is more efficient
  than listing all $n!$ possible rankings and then weeding out the ones ruled out by unanimity.
\<close>
lemma unanimous_topo_sort_Pareto:
  assumes R: "is_pref_profile R"
  shows   "swf R \<in> of_ranking ` topo_sorts alts (Pareto(R))"
proof -
  interpret R: pref_profile_linorder_wf agents alts R
    by fact
  have "Pareto(R) \<le> swf R"
    using R unfolding le_fun_def R.Pareto_iff le_bool_def by (auto intro: unanimous')
  moreover have "finite_linorder_on alts (swf R)"
    using R by (rule swf_wf')
  ultimately have "swf R \<in> {R'. finite_linorder_on alts R' \<and> Pareto(R) \<le> R'}"
    by simp
  also have "bij_betw of_ranking (topo_sorts alts (Pareto(R))) {R'. finite_linorder_on alts R' \<and> Pareto(R) \<le> R'}"
    by (rule bij_betw_topo_sorts_linorders_on) (use R.Pareto.not_outside in auto)
  hence "{R'. finite_linorder_on alts R' \<and> Pareto(R) \<le> R'} = of_ranking ` topo_sorts alts (Pareto(R))"
    by (simp add: bij_betw_def)
  finally show ?thesis .
qed

end


text \<open>
  Kemeny strategyproofness: no agent can achieve a better outcome for themselves by unilaterally
  submitting a preference ranking different from their true one. Here, ``better'' is defined by
  the swap distance (also known as the Kendall tau distance).
\<close>
locale kemeny_strategyproof_swf = social_welfare_function agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf +
  assumes kemeny_strategyproof:
    "is_pref_profile R \<Longrightarrow> i \<in> agents \<Longrightarrow> linorder_on alts R' \<Longrightarrow>
       swap_dist_relation (R i) (swf R) \<le> swap_dist_relation (R i) (swf (R(i := R')))"



subsection \<open>Majority consistency\<close>

locale majority_consistent_swf = social_welfare_function agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf +
  assumes majority_consistent:
    "is_pref_profile R \<Longrightarrow> linorder_on alts (majority R) \<Longrightarrow> swf R = majority R"

locale majcons_kstratproof_swf =
  majority_consistent_swf agents alts swf +
  kemeny_strategyproof_swf agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf

text \<open>
  A unanimous SWF with at most 2 agents is always majority-consistent (since the only way
  for a preference relation to have no ties is for it to be unanimous).
\<close>

lemma (in unanimous_swf)
  assumes "card agents \<le> 2"
  shows   "majority_consistent_swf agents alts swf"
proof
  fix R assume R: "is_pref_profile R"
  assume maj: "linorder_on alts (majority R)"
  interpret R: pref_profile_linorder_wf agents alts R by fact
  interpret maj: linorder_on alts "majority R" by fact
  interpret S: linorder_on alts "swf R" by (rule swf_wf) fact

  have eq: "majority R = Pareto R"
    by (rule R.card_agents_le_2_imp_majority_eq_unanimity) (use assms maj in simp_all)
  have Pareto_imp_swf: "swf R x y" if "Pareto R x y" for x y
    using unanimous'[of R x y] R that by (auto simp: R.Pareto_iff)

  show "swf R = majority R"
  proof (intro ext)
    fix x y
    show "swf R x y = majority R x y"
    proof (cases "x \<in> alts \<and> y \<in> alts")
      case True
      show "swf R x y = majority R x y"
        using eq unanimous'[OF R] Pareto_imp_swf maj.total S.antisymmetric True by metis
    qed (use S.not_outside maj.not_outside in auto)
  qed
qed


text \<open>
  For a non-unanimous SWF, Kemeny strategyproofness does not survive the addition of dummy
  alternatives. However, a weaker notion does, namely Kemeny strategyproofness where only
  manipulations to profiles with a linear majority relation are forbidden.
\<close>
locale majority_consistent_weak_kstratproof_swf =
  majority_consistent_swf agents alts swf
  for agents :: "'agent set" and alts :: "'alt set" and swf +
  assumes majority_consistent_kemeny_strategyproof:
    "is_pref_profile R \<Longrightarrow> i \<in> agents \<Longrightarrow> linorder_on alts S \<Longrightarrow> 
       linorder_on alts (majority (R(i := S))) \<Longrightarrow>
       swap_dist_relation (R i) (swf R) \<le> swap_dist_relation (R i) (majority (R(i := S)))"



subsection \<open>Concrete classes of SWFs\<close>


subsubsection \<open>Dictatorships\<close>

text \<open>
  A dictatorship rule simply returns the ranking of one fixed agent (the dictator).
  It is clearly neutral, anonymous, and strategyproof, but neither anonymous (unless $n = 1$) nor
  majority-consistent (unless $n \leq 2$).
\<close>

locale dictatorship_swf = linorder_election agents alts
  for agents :: "'agent set" and alts :: "'alt set" +
  fixes dictator :: 'agent
  assumes dictator_in_agents: "dictator \<in> agents"
begin

sublocale social_welfare_function agents alts "\<lambda>R. R dictator"
proof
  fix R assume R: "is_pref_profile R"
  thus "linorder_on alts (R dictator)"
    by (simp add: dictator_in_agents pref_profile_linorder_wf.prefs_wf')
qed

sublocale neutral_swf agents alts "\<lambda>R. R dictator"
  by unfold_locales auto

sublocale unanimous_swf agents alts "\<lambda>R. R dictator"
  by unfold_locales (use dictator_in_agents in auto)

sublocale kemeny_strategyproof_swf agents alts "\<lambda>R. R dictator"
  by unfold_locales auto

end



subsubsection \<open>Fixed-result SWFs\<close>

text \<open>
  Another degenerate case is an SWF that always returns the same ranking, completely ignoring the
  preferences of the agents. Such an SWF is clearly anonymous and strategyproof, but not 
  unanimous (except for the degenerate case where $m = 1$).
\<close>

locale fixed_swf = linorder_election agents alts
  for agents :: "'agent set" and alts :: "'alt set" +
  fixes ranking :: "'alt relation"
  assumes ranking: "linorder_on alts ranking"
begin

sublocale social_welfare_function agents alts "\<lambda>_. ranking"
  by standard (use ranking in auto)

sublocale anonymous_swf agents alts "\<lambda>_. ranking"
  by unfold_locales auto

sublocale kemeny_strategyproof_swf agents alts "\<lambda>_. ranking"
  by unfold_locales auto

end

end
