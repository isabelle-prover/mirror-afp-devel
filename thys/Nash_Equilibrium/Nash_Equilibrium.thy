theory Nash_Equilibrium
  imports Main
begin

section \<open>Pure Nash Equilibria\<close>

text \<open>
  Nash's equilibrium concept says that a strategy profile is stable when no
  player can improve by changing only her own strategy.  This entry formalizes
  the pure-strategy version for finite strategic-form games with a common
  strategy type.

  The central locale below fixes a finite set of players, a finite nonempty
  strategy set for each player, and a payoff function.  The player and strategy
  types are finite; this keeps the profile space finite while still allowing
  player-indexed strategy restrictions.

  The development is intended as a reusable finite-game layer: the basic locale
  gives pure Nash equilibria and best responses, later locales derive existence
  from ordinal potentials and dominant strategies, and the companion mixed
  theory proves the finite mixed-equilibrium theorem using HOL-Analysis.
\<close>

locale finite_game =
  fixes players :: "'p::finite set"
    and strategies :: "'p \<Rightarrow> 's::finite set"
    and payoff :: "'p \<Rightarrow> ('p \<Rightarrow> 's) \<Rightarrow> 'u::preorder"
  assumes nonempty_strategies: "i \<in> players \<Longrightarrow> strategies i \<noteq> {}"
begin

definition profiles :: "('p \<Rightarrow> 's) set" where
  "profiles = {s. \<forall>i\<in>players. s i \<in> strategies i}"

definition deviation :: "('p \<Rightarrow> 's) \<Rightarrow> 'p \<Rightarrow> 's \<Rightarrow> ('p \<Rightarrow> 's)" where
  "deviation s i x = s(i := x)"

definition Nash_equilibrium :: "('p \<Rightarrow> 's) \<Rightarrow> bool" where
  "Nash_equilibrium s \<longleftrightarrow>
     s \<in> profiles \<and>
     (\<forall>i\<in>players. \<forall>x\<in>strategies i.
        payoff i (deviation s i x) \<le> payoff i s)"

definition best_response_to :: "('p \<Rightarrow> 's) \<Rightarrow> 'p \<Rightarrow> 's \<Rightarrow> bool" where
  "best_response_to s i x \<longleftrightarrow>
     i \<in> players \<and> x \<in> strategies i \<and>
     (\<forall>y\<in>strategies i. payoff i (deviation s i y) \<le> payoff i (deviation s i x))"

definition dominant_strategy :: "'p \<Rightarrow> 's \<Rightarrow> bool" where
  "dominant_strategy i x \<longleftrightarrow>
     i \<in> players \<and> x \<in> strategies i \<and>
     (\<forall>s\<in>profiles. \<forall>y\<in>strategies i.
        payoff i (deviation s i y) \<le> payoff i (deviation s i x))"

lemma profiles_iff:
  "s \<in> profiles \<longleftrightarrow> (\<forall>i\<in>players. s i \<in> strategies i)"
  by (auto simp: profiles_def)

lemma profile_strategy:
  assumes "s \<in> profiles" "i \<in> players"
  shows "s i \<in> strategies i"
  using assms by (simp add: profiles_iff)

lemma finite_profiles [simp, intro]: "finite profiles"
  by simp

lemma profiles_nonempty: "profiles \<noteq> {}"
proof -
  have "\<forall>i\<in>players. \<exists>x. x \<in> strategies i"
    using nonempty_strategies by auto
  then obtain f where f: "\<And>i. i \<in> players \<Longrightarrow> f i \<in> strategies i"
    by metis
  define g where "g i = f i" for i
  have "g \<in> profiles"
    using f by (auto simp: profiles_iff g_def)
  then show ?thesis
    by blast
qed

lemma deviation_apply [simp]:
  "deviation s i x j = (if j = i then x else s j)"
  by (simp add: deviation_def)

lemma deviation_self [simp]: "deviation s i (s i) = s"
  by (simp add: deviation_def)

lemma deviation_in_profiles:
  assumes "s \<in> profiles" "i \<in> players" "x \<in> strategies i"
  shows "deviation s i x \<in> profiles"
  using assms by (auto simp: profiles_iff)

lemma Nash_equilibriumI:
  assumes "s \<in> profiles"
    and "\<And>i x. i \<in> players \<Longrightarrow> x \<in> strategies i \<Longrightarrow>
      payoff i (deviation s i x) \<le> payoff i s"
  shows "Nash_equilibrium s"
  using assms by (auto simp: Nash_equilibrium_def)

lemma Nash_equilibrium_profile:
  assumes "Nash_equilibrium s"
  shows "s \<in> profiles"
  using assms by (simp add: Nash_equilibrium_def)

lemma Nash_equilibriumD:
  assumes "Nash_equilibrium s" "i \<in> players" "x \<in> strategies i"
  shows "payoff i (deviation s i x) \<le> payoff i s"
  using assms by (simp add: Nash_equilibrium_def)

lemma Nash_equilibrium_iff_best_responses:
  assumes "s \<in> profiles"
  shows "Nash_equilibrium s \<longleftrightarrow> (\<forall>i\<in>players. best_response_to s i (s i))"
  using assms by (auto simp: Nash_equilibrium_def best_response_to_def profile_strategy)

lemma dominant_strategy_profile_is_Nash:
  assumes "s \<in> profiles"
    and dominant: "\<And>i. i \<in> players \<Longrightarrow> dominant_strategy i (s i)"
  shows "Nash_equilibrium s"
proof (rule Nash_equilibriumI)
  show "s \<in> profiles"
    using assms by simp
next
  fix i x
  assume ix: "i \<in> players" "x \<in> strategies i"
  have dom: "dominant_strategy i (s i)"
    using dominant ix by blast
  then have "\<And>t y. t \<in> profiles \<Longrightarrow> y \<in> strategies i \<Longrightarrow>
      payoff i (deviation t i y) \<le> payoff i (deviation t i (s i))"
    by (simp add: dominant_strategy_def)
  from this[OF assms(1) ix(2)] show "payoff i (deviation s i x) \<le> payoff i s"
    by simp
qed

end


section \<open>Existence for Finite Potential Games\<close>

text \<open>
  Pure Nash equilibria need not exist in arbitrary finite games.  A standard
  positive result is that every finite game with an ordinal potential has a pure
  Nash equilibrium: choose a profile whose potential is maximal.  The definition
  used here is the one needed for the argument: every strict unilateral payoff
  improvement strictly increases the potential.  Exact and ordinal potential
  games in the sense of Monderer and Shapley satisfy this assumption.
\<close>

locale finite_potential_game =
  finite_game players strategies payoff
  for players :: "'p::finite set"
    and strategies :: "'p \<Rightarrow> 's::finite set"
    and payoff :: "'p \<Rightarrow> ('p \<Rightarrow> 's) \<Rightarrow> 'u::linorder" +
  fixes potential :: "('p \<Rightarrow> 's) \<Rightarrow> 'v::linorder"
  assumes potential_increases:
    "\<lbrakk>s \<in> profiles; i \<in> players; x \<in> strategies i;
      payoff i s < payoff i (deviation s i x)\<rbrakk>
     \<Longrightarrow> potential s < potential (deviation s i x)"
begin

lemma maximal_potential_profile:
  obtains s where
    "s \<in> profiles"
    "\<And>t. t \<in> profiles \<Longrightarrow> potential t \<le> potential s"
proof -
  let ?M = "Max (potential ` profiles)"
  have fin: "finite (potential ` profiles)"
    by simp
  have nonempty: "potential ` profiles \<noteq> {}"
    using profiles_nonempty by blast
  have M_in: "?M \<in> potential ` profiles"
    by (rule Max_in[OF fin nonempty])
  then obtain s where s_prof: "s \<in> profiles" and s_Max: "potential s = ?M"
    by (auto elim!: imageE)
  have max_s: "potential t \<le> potential s" if "t \<in> profiles" for t
    using Max_ge[OF fin, of "potential t"] s_Max that by auto
  show ?thesis
    using max_s s_prof that by auto
qed

theorem exists_Nash_equilibrium:
  "\<exists>s\<in>profiles. Nash_equilibrium s"
proof -
  obtain s where s: "s \<in> profiles"
    and max: "\<And>t. t \<in> profiles \<Longrightarrow> potential t \<le> potential s"
    using maximal_potential_profile by blast
  have "Nash_equilibrium s"
  proof (rule Nash_equilibriumI)
    show "s \<in> profiles"
      by fact
  next
    fix i x
    assume ix: "i \<in> players" "x \<in> strategies i"
    show "payoff i (deviation s i x) \<le> payoff i s"
    proof (rule ccontr)
      assume "\<not> payoff i (deviation s i x) \<le> payoff i s"
      then have improve: "payoff i s < payoff i (deviation s i x)"
        by simp
      have dev: "deviation s i x \<in> profiles"
        using s ix by (rule deviation_in_profiles)
      have "potential s < potential (deviation s i x)"
        using potential_increases[OF s ix improve] .
      moreover have "potential (deviation s i x) \<le> potential s"
        using max[OF dev] .
      ultimately show False
        by simp
    qed
  qed
  with s show ?thesis
    by blast
qed

end


section \<open>Dominant Strategies as a Degenerate Existence Result\<close>

text \<open>
  Dominant strategies give another elementary source of equilibria.  The next
  locale packages the hypothesis that every player has a distinguished dominant
  strategy and derives existence by constructing the corresponding profile.
\<close>

locale finite_dominant_strategy_game =
  finite_game players strategies payoff
  for players :: "'p::finite set"
    and strategies :: "'p \<Rightarrow> 's::finite set"
    and payoff :: "'p \<Rightarrow> ('p \<Rightarrow> 's) \<Rightarrow> 'u::preorder" +
  fixes dominant :: "'p \<Rightarrow> 's"
  assumes dominant: "i \<in> players \<Longrightarrow> dominant_strategy i (dominant i)"
begin

definition dominant_profile :: "'p \<Rightarrow> 's" where
  "dominant_profile i = (if i \<in> players then dominant i else undefined)"

lemma dominant_profile_in_profiles:
  "dominant_profile \<in> profiles"
  using dominant by (auto simp: dominant_profile_def profiles_iff dominant_strategy_def)

theorem dominant_profile_is_Nash:
  "Nash_equilibrium dominant_profile"
  by (simp add: dominant dominant_profile_def dominant_profile_in_profiles dominant_strategy_profile_is_Nash)

end


section \<open>Matching Pennies\<close>

text \<open>
  The following two-player zero-sum game shows why an existence theorem for pure
  Nash equilibria needs additional hypotheses.  The row player wants the two
  coins to match; the column player wants them to differ.  After every pure
  profile, exactly one player can improve by switching sides.
\<close>

datatype penny_player = Row | Column

datatype coin_side = Heads | Tails

instantiation penny_player :: finite
begin

instance
proof
  show "finite (UNIV :: penny_player set)"
    by (rule finite_subset[of _ "{Row, Column}"]) (auto intro: penny_player.exhaust)
qed

end

instantiation coin_side :: finite
begin

instance
proof
  show "finite (UNIV :: coin_side set)"
    by (rule finite_subset[of _ "{Heads, Tails}"]) (auto intro: coin_side.exhaust)
qed

end

definition matching_pennies_payoff :: "penny_player \<Rightarrow> (penny_player \<Rightarrow> coin_side) \<Rightarrow> int" where
  "matching_pennies_payoff p s =
     (case p of
        Row \<Rightarrow> if s Row = s Column then 1 else 0
      | Column \<Rightarrow> if s Row = s Column then 0 else 1)"

interpretation matching_pennies:
  finite_game UNIV "\<lambda>_. UNIV" matching_pennies_payoff
  by standard auto

definition switch_coin :: "coin_side \<Rightarrow> coin_side" where
  "switch_coin x = (case x of Heads \<Rightarrow> Tails | Tails \<Rightarrow> Heads)"

lemma switch_coin_neq [simp]: "switch_coin x \<noteq> x"
  by (cases x) (simp_all add: switch_coin_def)

lemma coin_side_switch:
  fixes x :: coin_side
  obtains y where "y \<noteq> x"
proof 
  show "switch_coin x \<noteq> x"
    by simp
qed

lemma matching_pennies_no_pure_Nash:
  "\<not> matching_pennies.Nash_equilibrium s"
proof
  assume ne: "matching_pennies.Nash_equilibrium s"
  then have profile: "s \<in> matching_pennies.profiles"
    by (rule matching_pennies.Nash_equilibrium_profile)
  show False
  proof (cases "s Row = s Column")
    case True
    obtain y where y: "y \<noteq> s Row"
      using coin_side_switch by blast
    have "matching_pennies_payoff Column (matching_pennies.deviation s Column y) = 1"
      using True y by (simp add: matching_pennies_payoff_def)
    moreover have "matching_pennies_payoff Column s = 0"
      using True by (simp add: matching_pennies_payoff_def)
    ultimately have "\<not> matching_pennies_payoff Column (matching_pennies.deviation s Column y)
                     \<le> matching_pennies_payoff Column s"
      by simp
    moreover have "y \<in> (UNIV :: coin_side set)"
      by simp
    ultimately show False
      using matching_pennies.Nash_equilibriumD[OF ne, of Column y] by simp
  next
    case False
    obtain y where y: "y = s Column"
      by simp
    have "matching_pennies_payoff Row (matching_pennies.deviation s Row y) = 1"
      using y by (simp add: matching_pennies_payoff_def)
    moreover have "matching_pennies_payoff Row s = 0"
      using False by (simp add: matching_pennies_payoff_def)
    ultimately have "\<not> matching_pennies_payoff Row (matching_pennies.deviation s Row y)
                     \<le> matching_pennies_payoff Row s"
      by simp
    moreover have "y \<in> (UNIV :: coin_side set)"
      by simp
    ultimately show False
      using matching_pennies.Nash_equilibriumD[OF ne, of Row y] by simp
  qed
qed

end
