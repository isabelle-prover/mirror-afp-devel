theory Nash_Equilibrium_Examples
  imports Mixed_Nash_Equilibrium
begin

lemma UNIV_penny_player: "(UNIV :: penny_player set) = {Row, Column}"
  by (auto intro: penny_player.exhaust)

lemma UNIV_coin_side [simp]: "(UNIV :: coin_side set) = {Heads, Tails}"
  by (auto intro: coin_side.exhaust)

lemma players_except_Row [simp]: "(UNIV :: penny_player set) - {Row} = {Column}"
  by (auto simp: UNIV_penny_player)

lemma players_except_Column [simp]: "(UNIV :: penny_player set) - {Column} = {Row}"
  by (auto simp: UNIV_penny_player)

lemma player_insert_except_Row [simp]: "{Row, Column} - {Row} = {Column}"
  by auto

lemma player_insert_except_Column [simp]: "{Row, Column} - {Column} = {Row}"
  by auto


section \<open>Prisoner's Dilemma\<close>

text \<open>
  The Prisoner's Dilemma gives a small example using the dominant-strategy
  existence result.  Defection is dominant for both players, hence the
  all-defect profile is a pure Nash equilibrium.
\<close>

datatype prisoner = Prisoner1 | Prisoner2

datatype prisoner_move = Cooperate | Defect

instantiation prisoner :: finite
begin

instance
proof
  show "finite (UNIV :: prisoner set)"
    by (rule finite_subset[of _ "{Prisoner1, Prisoner2}"]) (auto intro: prisoner.exhaust)
qed

end

instantiation prisoner_move :: finite
begin

instance
proof
  show "finite (UNIV :: prisoner_move set)"
    by (rule finite_subset[of _ "{Cooperate, Defect}"]) (auto intro: prisoner_move.exhaust)
qed

end

fun other_prisoner :: "prisoner \<Rightarrow> prisoner" where
  "other_prisoner Prisoner1 = Prisoner2"
| "other_prisoner Prisoner2 = Prisoner1"

definition prisoners_dilemma_payoff :: "prisoner \<Rightarrow> (prisoner \<Rightarrow> prisoner_move) \<Rightarrow> int" where
  "prisoners_dilemma_payoff p s =
     (case (s p, s (other_prisoner p)) of
        (Cooperate, Cooperate) \<Rightarrow> 3
      | (Defect, Cooperate) \<Rightarrow> 5
      | (Cooperate, Defect) \<Rightarrow> 0
      | (Defect, Defect) \<Rightarrow> 1)"

interpretation prisoners_dilemma:
  finite_game UNIV "\<lambda>_. UNIV" prisoners_dilemma_payoff
  by standard auto

interpretation prisoners_dilemma_dominant:
  finite_dominant_strategy_game UNIV "\<lambda>_. UNIV" prisoners_dilemma_payoff "\<lambda>_. Defect"
proof
  fix i :: prisoner
  show "prisoners_dilemma.dominant_strategy i ((\<lambda>_. Defect) i)"
    by (cases i)
      (auto simp: prisoners_dilemma.dominant_strategy_def prisoners_dilemma_payoff_def
        split: prisoner_move.splits)
qed

lemma prisoners_dilemma_defect_defect_Nash:
  "prisoners_dilemma.Nash_equilibrium (\<lambda>_. Defect)"
proof -
  have "prisoners_dilemma_dominant.dominant_profile = (\<lambda>_. Defect)"
    by (simp add: fun_eq_iff prisoners_dilemma_dominant.dominant_profile_def)
  then show ?thesis
    using prisoners_dilemma_dominant.dominant_profile_is_Nash by simp
qed


section \<open>Coordination Game\<close>

text \<open>
  A two-player coordination game has two pure equilibria.  Both players receive
  payoff one when their choices agree and zero otherwise.
\<close>

datatype coordination_choice = Choice_A | Choice_B

instantiation coordination_choice :: finite
begin

instance
proof
  show "finite (UNIV :: coordination_choice set)"
    by (rule finite_subset[of _ "{Choice_A, Choice_B}"])
      (auto intro: coordination_choice.exhaust)
qed

end

definition coordination_payoff ::
    "penny_player \<Rightarrow> (penny_player \<Rightarrow> coordination_choice) \<Rightarrow> int" where
  "coordination_payoff p s = (if s Row = s Column then 1 else 0)"

interpretation coordination:
  finite_game UNIV "\<lambda>_. UNIV" coordination_payoff
  by standard auto

lemma coordination_A_A_Nash:
  "coordination.Nash_equilibrium (\<lambda>_. Choice_A)"
proof (rule coordination.Nash_equilibriumI)
  show "(\<lambda>_. Choice_A) \<in> coordination.profiles"
    by (simp add: coordination.profiles_def)
next
  fix i :: penny_player
  fix x :: coordination_choice
  show "coordination_payoff i (coordination.deviation (\<lambda>_. Choice_A) i x)
      \<le> coordination_payoff i (\<lambda>_. Choice_A)"
    by (cases i; cases x) (simp_all add: coordination_payoff_def coordination.deviation_def)
qed

lemma coordination_B_B_Nash:
  "coordination.Nash_equilibrium (\<lambda>_. Choice_B)"
proof (rule coordination.Nash_equilibriumI)
  show "(\<lambda>_. Choice_B) \<in> coordination.profiles"
    by (simp add: coordination.profiles_def)
next
  fix i :: penny_player
  fix x :: coordination_choice
  show "coordination_payoff i (coordination.deviation (\<lambda>_. Choice_B) i x)
      \<le> coordination_payoff i (\<lambda>_. Choice_B)"
    by (cases i; cases x) (simp_all add: coordination_payoff_def coordination.deviation_def)
qed


section \<open>Two-Player Profile Sums\<close>

definition two_player_profile :: "'a \<Rightarrow> 'a \<Rightarrow> penny_player \<Rightarrow> 'a" where
  "two_player_profile r c p = (case p of Row \<Rightarrow> r | Column \<Rightarrow> c)"

lemma two_player_profile_simps [simp]:
  "two_player_profile r c Row = r"
  "two_player_profile r c Column = c"
  by (simp_all add: two_player_profile_def)

lemma sum_profiles_fixed_Row:
  fixes F :: "(penny_player \<Rightarrow> 'a::finite) \<Rightarrow> 'b::comm_monoid_add"
  shows "(\<Sum>s\<in>{s. s Row = x}. F s) =
    (\<Sum>y\<in>UNIV. F (two_player_profile x y))"
proof (rule sum.reindex_bij_witness[
    where i = "\<lambda>y. two_player_profile x y" and j = "\<lambda>s. s Column"])
  fix s :: "penny_player \<Rightarrow> 'a"
  assume s: "s \<in> {s. s Row = x}"
  show profile_eq: "two_player_profile x (s Column) = s"
  proof
    fix p
    show "two_player_profile x (s Column) p = s p"
      using s by (cases p) auto
  qed
  show "F (two_player_profile x (s Column)) = F s"
    by (simp add: profile_eq)
qed auto

lemma sum_profiles_fixed_Column:
  fixes F :: "(penny_player \<Rightarrow> 'a::finite) \<Rightarrow> 'b::comm_monoid_add"
  shows "(\<Sum>s\<in>{s. s Column = x}. F s) =
    (\<Sum>y\<in>UNIV. F (two_player_profile y x))"
proof (rule sum.reindex_bij_witness[
    where i = "\<lambda>y. two_player_profile y x" and j = "\<lambda>s. s Row"])
  fix s :: "penny_player \<Rightarrow> 'a"
  assume s: "s \<in> {s. s Column = x}"
  show profile_eq: "two_player_profile (s Row) x = s"
  proof
    fix p
    show "two_player_profile (s Row) x p = s p"
      using s by (cases p) auto
  qed
  show "F (two_player_profile (s Row) x) = F s"
    by (simp add: profile_eq)
qed auto


section \<open>Matching Pennies as a Mixed Equilibrium\<close>

definition matching_pennies_payoff_real ::
    "penny_player \<Rightarrow> (penny_player \<Rightarrow> coin_side) \<Rightarrow> real" where
  "matching_pennies_payoff_real p s = real_of_int (matching_pennies_payoff p s)"

interpretation matching_pennies_mixed:
  finite_type_game matching_pennies_payoff_real .

lemma matching_pennies_pure_deviation_Row:
  "matching_pennies_mixed.pure_deviation_payoff Row x m =
    (\<Sum>y\<in>UNIV.
      matching_pennies_mixed.prob m Column y *
      matching_pennies_payoff_real Row (two_player_profile x y))"
  by (simp add: matching_pennies_mixed.pure_deviation_payoff_def
      matching_pennies_mixed.opponent_weight_def sum_profiles_fixed_Row)

lemma matching_pennies_pure_deviation_Column:
  "matching_pennies_mixed.pure_deviation_payoff Column x m =
    (\<Sum>y\<in>UNIV.
      matching_pennies_mixed.prob m Row y *
      matching_pennies_payoff_real Column (two_player_profile y x))"
  by (simp add: matching_pennies_mixed.pure_deviation_payoff_def
      matching_pennies_mixed.opponent_weight_def sum_profiles_fixed_Column)

lemma matching_pennies_uniform_pure_deviation_payoff:
  "matching_pennies_mixed.pure_deviation_payoff i x
      matching_pennies_mixed.uniform_mixed_profile = 1 / 2"
  by (cases i; cases x)
    (simp_all add: matching_pennies_pure_deviation_Row
      matching_pennies_pure_deviation_Column matching_pennies_payoff_real_def
      matching_pennies_payoff_def)

lemma matching_pennies_uniform_mixed_payoff:
  "matching_pennies_mixed.mixed_payoff i matching_pennies_mixed.uniform_mixed_profile = 1 / 2"
  by (simp add: matching_pennies_mixed.mixed_payoff_def
      matching_pennies_uniform_pure_deviation_payoff)

lemma matching_pennies_uniform_mixed_Nash:
  "matching_pennies_mixed.mixed_Nash_equilibrium
    matching_pennies_mixed.uniform_mixed_profile"
  by (auto simp: matching_pennies_mixed.mixed_Nash_equilibrium_def
      matching_pennies_uniform_pure_deviation_payoff
      matching_pennies_uniform_mixed_payoff)


section \<open>Rock-Paper-Scissors\<close>

datatype rps = Rock | Paper | Scissors

instantiation rps :: finite
begin

instance
proof
  show "finite (UNIV :: rps set)"
    by (rule finite_subset[of _ "{Rock, Paper, Scissors}"]) (auto intro: rps.exhaust)
qed

end

lemma UNIV_rps [simp]: "(UNIV :: rps set) = {Rock, Paper, Scissors}"
  by (auto intro: rps.exhaust)

fun beats :: "rps \<Rightarrow> rps \<Rightarrow> bool" where
  "beats Rock Scissors = True"
| "beats Paper Rock = True"
| "beats Scissors Paper = True"
| "beats _ _ = False"

definition rps_payoff :: "penny_player \<Rightarrow> (penny_player \<Rightarrow> rps) \<Rightarrow> real" where
  "rps_payoff p s =
     (if s Row = s Column then 0
      else if beats (s Row) (s Column)
      then if p = Row then 1 else -1
      else if p = Row then -1 else 1)"

interpretation rps_mixed:
  finite_type_game rps_payoff .

lemma rps_pure_deviation_Row:
  "rps_mixed.pure_deviation_payoff Row x m =
    (\<Sum>y\<in>UNIV. rps_mixed.prob m Column y * rps_payoff Row (two_player_profile x y))"
  by (simp add: rps_mixed.pure_deviation_payoff_def rps_mixed.opponent_weight_def
      sum_profiles_fixed_Row)

lemma rps_pure_deviation_Column:
  "rps_mixed.pure_deviation_payoff Column x m =
    (\<Sum>y\<in>UNIV. rps_mixed.prob m Row y * rps_payoff Column (two_player_profile y x))"
  by (simp add: rps_mixed.pure_deviation_payoff_def rps_mixed.opponent_weight_def
      sum_profiles_fixed_Column)

lemma rps_uniform_pure_deviation_payoff:
  "rps_mixed.pure_deviation_payoff i x rps_mixed.uniform_mixed_profile = 0"
  by (cases i; cases x)
    (simp_all add: rps_pure_deviation_Row rps_pure_deviation_Column rps_payoff_def)

lemma rps_uniform_mixed_payoff:
  "rps_mixed.mixed_payoff i rps_mixed.uniform_mixed_profile = 0"
  by (simp add: rps_mixed.mixed_payoff_def rps_uniform_pure_deviation_payoff)

lemma rps_uniform_mixed_Nash:
  "rps_mixed.mixed_Nash_equilibrium rps_mixed.uniform_mixed_profile"
  by (auto simp: rps_mixed.mixed_Nash_equilibrium_def
      rps_uniform_pure_deviation_payoff rps_uniform_mixed_payoff)

end
