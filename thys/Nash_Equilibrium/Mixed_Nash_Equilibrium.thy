theory Mixed_Nash_Equilibrium
  imports
    Nash_Equilibrium
    "HOL-Analysis.Cartesian_Euclidean_Space"
    "HOL-Analysis.Brouwer_Fixpoint"
begin

section \<open>Mixed Nash Equilibria\<close>

text \<open>
  This theory develops the mixed-strategy version of Nash equilibrium for finite
  games whose players and pure strategies are represented by finite HOL types.
  A mixed profile is a Cartesian vector indexed by player/strategy pairs.

  This locale is deliberately more restrictive than the pure-game locale:
  every player has the same finite pure-strategy type.  In return, the profile
  space is a finite Cartesian product of real coordinates, so compactness,
  convexity, continuity, and Brouwer's fixed point theorem can be applied
  directly.
\<close>

type_synonym ('p, 's) mixed_profile = "real ^ ('p \<times> 's)"

locale finite_type_game =
  fixes payoff :: "'p::finite \<Rightarrow> ('p \<Rightarrow> 's::finite) \<Rightarrow> real"
begin

definition prob :: "('p, 's) mixed_profile \<Rightarrow> 'p \<Rightarrow> 's \<Rightarrow> real" where
  "prob m i x = m $ (i, x)"

definition mixed_profiles :: "('p, 's) mixed_profile set" where
  "mixed_profiles =
     {m \<in> cbox 0 1. \<forall>i. (\<Sum>x\<in>UNIV. prob m i x) = 1}"

definition uniform_mixed_profile :: "('p, 's) mixed_profile" where
  "uniform_mixed_profile = (\<chi> ix. 1 / real CARD('s))"

definition opponent_weight :: "'p \<Rightarrow> ('p, 's) mixed_profile \<Rightarrow> ('p \<Rightarrow> 's) \<Rightarrow> real" where
  "opponent_weight i m s = (\<Prod>j\<in>UNIV - {i}. prob m j (s j))"

definition pure_deviation_payoff ::
    "'p \<Rightarrow> 's \<Rightarrow> ('p, 's) mixed_profile \<Rightarrow> real" where
  "pure_deviation_payoff i x m =
     (\<Sum>s\<in>{s. s i = x}. opponent_weight i m s * payoff i s)"

definition mixed_payoff :: "'p \<Rightarrow> ('p, 's) mixed_profile \<Rightarrow> real" where
  "mixed_payoff i m =
     (\<Sum>x\<in>UNIV. prob m i x * pure_deviation_payoff i x m)"

definition mixed_Nash_equilibrium :: "('p, 's) mixed_profile \<Rightarrow> bool" where
  "mixed_Nash_equilibrium m \<longleftrightarrow>
     m \<in> mixed_profiles \<and>
     (\<forall>i x. pure_deviation_payoff i x m \<le> mixed_payoff i m)"

definition excess :: "'p \<Rightarrow> 's \<Rightarrow> ('p, 's) mixed_profile \<Rightarrow> real" where
  "excess i x m = max 0 (pure_deviation_payoff i x m - mixed_payoff i m)"

definition excess_sum :: "'p \<Rightarrow> ('p, 's) mixed_profile \<Rightarrow> real" where
  "excess_sum i m = (\<Sum>x\<in>UNIV. excess i x m)"

definition nash_map :: "('p, 's) mixed_profile \<Rightarrow> ('p, 's) mixed_profile" where
  "nash_map m = (\<chi> ix. (prob m (fst ix) (snd ix) + excess (fst ix) (snd ix) m) /
      (1 + excess_sum (fst ix) m))"

lemma prob_nash_map:
  "prob (nash_map m) i x = (prob m i x + excess i x m) / (1 + excess_sum i m)"
  by (simp add: prob_def nash_map_def)

lemma mixed_profiles_prob_nonneg:
  assumes "m \<in> mixed_profiles"
  shows "0 \<le> prob m i x"
  using assms by (auto simp: mixed_profiles_def prob_def mem_box_cart)

lemma mixed_profiles_prob_le_one:
  assumes "m \<in> mixed_profiles"
  shows "prob m i x \<le> 1"
  using assms by (auto simp: mixed_profiles_def prob_def mem_box_cart)

lemma mixed_profiles_sum_prob:
  assumes "m \<in> mixed_profiles"
  shows "(\<Sum>x\<in>UNIV. prob m i x) = 1"
  using assms by (auto simp: mixed_profiles_def)

lemma prob_uniform_mixed_profile [simp]:
  "prob uniform_mixed_profile i x = 1 / real CARD('s)"
  by (simp add: prob_def uniform_mixed_profile_def)

lemma uniform_mixed_profile_in_mixed_profiles [simp]:
  "uniform_mixed_profile \<in> mixed_profiles"
proof -
  have card_pos: "0 < real CARD('s)"
    by simp
  have prob_le_one: "1 / real CARD('s) \<le> 1"
    using card_pos by (simp add: divide_simps)
  have sum_one: "(\<Sum>x\<in>UNIV. prob uniform_mixed_profile i x) = 1" for i
    using card_pos by simp
  show ?thesis
    using card_pos prob_le_one sum_one
    by (auto simp: mixed_profiles_def prob_def uniform_mixed_profile_def mem_box_cart)
qed

lemma excess_nonneg [simp]: "0 \<le> excess i x m"
  by (simp add: excess_def)

lemma excess_sum_nonneg [simp]: "0 \<le> excess_sum i m"
  by (simp add: excess_sum_def sum_nonneg)

lemma denom_pos [simp]: "0 < 1 + excess_sum i m"
  using excess_sum_nonneg[of i m] by linarith

lemma nash_map_in_mixed_profiles:
  assumes m: "m \<in> mixed_profiles"
  shows "nash_map m \<in> mixed_profiles"
proof -
  have nonneg: "0 \<le> prob (nash_map m) i x" for i x
    using mixed_profiles_prob_nonneg[OF m, of i x]
    by (simp add: prob_nash_map divide_nonneg_pos)
  have le_one: "prob (nash_map m) i x \<le> 1" for i x
  proof -
    have ex_le: "excess i x m \<le> excess_sum i m"
      unfolding excess_sum_def by (intro member_le_sum) auto
    have "prob m i x + excess i x m \<le> 1 + excess_sum i m"
      using mixed_profiles_prob_le_one[OF m, of i x] ex_le by linarith
    then show ?thesis
      by (simp add: prob_nash_map field_simps)
  qed
  have sum_one: "(\<Sum>x\<in>UNIV. prob (nash_map m) i x) = 1" for i
  proof -
    have "(\<Sum>x\<in>UNIV. prob (nash_map m) i x) =
        (\<Sum>x\<in>UNIV. (prob m i x + excess i x m) / (1 + excess_sum i m))"
      by (simp add: prob_nash_map)
    also have "\<dots> =
        ((\<Sum>x\<in>UNIV. prob m i x) + excess_sum i m) / (1 + excess_sum i m)"
      by (simp add: sum_divide_distrib[symmetric] sum.distrib excess_sum_def)
    also have "\<dots> = 1"
      by (simp add: add_nonneg_eq_0_iff m mixed_profiles_sum_prob)
    finally show ?thesis .
  qed
  show ?thesis
    using nonneg le_one sum_one
    by (auto simp: mixed_profiles_def prob_def mem_box_cart)
qed

lemma continuous_prob:
  "continuous_on S (\<lambda>m. prob m i x)"
  by (simp add: prob_def) (intro continuous_intros)

lemma continuous_opponent_weight:
  "continuous_on S (\<lambda>m. opponent_weight i m s)"
  unfolding opponent_weight_def
  by (intro continuous_intros continuous_prob)

lemma continuous_pure_deviation_payoff:
  "continuous_on S (\<lambda>m. pure_deviation_payoff i x m)"
  unfolding pure_deviation_payoff_def
  by (intro continuous_intros continuous_opponent_weight)

lemma continuous_mixed_payoff:
  "continuous_on S (\<lambda>m. mixed_payoff i m)"
  unfolding mixed_payoff_def
  by (intro continuous_intros continuous_prob continuous_pure_deviation_payoff)

lemma continuous_excess:
  "continuous_on S (\<lambda>m. excess i x m)"
  unfolding excess_def
  by (intro continuous_intros continuous_pure_deviation_payoff continuous_mixed_payoff)

lemma continuous_excess_sum:
  "continuous_on S (\<lambda>m. excess_sum i m)"
  unfolding excess_sum_def
  by (intro continuous_intros continuous_excess)

lemma continuous_nash_map:
  "continuous_on mixed_profiles nash_map"
proof -
  have nz: "m \<in> mixed_profiles \<Longrightarrow> 1 + excess_sum (fst ix) m \<noteq> 0" for ix m
    using denom_pos[of "fst ix" m] by linarith
  show ?thesis
    unfolding nash_map_def
    apply (intro continuous_intros continuous_prob continuous_excess continuous_excess_sum)
    using nz by blast
qed

lemma mixed_profiles_closed: "closed mixed_profiles"
proof -
  have closed_constraint: "closed {m. (\<Sum>x\<in>UNIV. prob m i x) = 1}" for i
    by (intro closed_Collect_eq continuous_intros continuous_prob)
  have eq: "mixed_profiles =
      cbox 0 1 \<inter> (\<Inter>i\<in>(UNIV :: 'p set). {m. (\<Sum>x\<in>UNIV. prob m i x) = 1})"
    by (auto simp: mixed_profiles_def)
  show ?thesis
    unfolding eq using closed_constraint by (auto intro!: closed_Int closed_INT closed_cbox)
qed

lemma mixed_profiles_compact: "compact mixed_profiles"
proof -
  have "mixed_profiles \<subseteq> cbox 0 1"
    by (auto simp: mixed_profiles_def)
  then show ?thesis
    using compact_cbox mixed_profiles_closed compact_eq_bounded_closed bounded_cbox bounded_subset
    by blast
qed

lemma mixed_profiles_convex: "convex mixed_profiles"
proof (rule convexI)
  fix m n :: "('p, 's) mixed_profile"
  fix u v :: real
  assume mn: "m \<in> mixed_profiles" "n \<in> mixed_profiles"
    and uv: "0 \<le> u" "0 \<le> v" "u + v = 1"
  have in_box: "u *\<^sub>R m + v *\<^sub>R n \<in> cbox 0 1"
  proof (auto simp: mem_box_cart)
    fix a b
    have "0 \<le> m $ (a, b)" "0 \<le> n $ (a, b)"
      using mn by (auto simp: mixed_profiles_def mem_box_cart)
    then show "0 \<le> u * m $ (a, b) + v * n $ (a, b)"
      using uv by (intro add_nonneg_nonneg mult_nonneg_nonneg) auto
  next
    fix a b
    have m_le: "m $ (a, b) \<le> 1" and n_le: "n $ (a, b) \<le> 1"
      using mn by (auto simp: mixed_profiles_def mem_box_cart)
    have "u * m $ (a, b) \<le> u"
      using uv m_le by (metis mult.right_neutral mult_left_mono)
    moreover have "v * n $ (a, b) \<le> v"
      using uv n_le by (metis mult.right_neutral mult_left_mono)
    ultimately show "u * m $ (a, b) + v * n $ (a, b) \<le> 1"
      using uv by linarith
  qed
  have sum_one: "(\<Sum>x\<in>UNIV. prob (u *\<^sub>R m + v *\<^sub>R n) i x) = 1" for i
  proof -
    have "(\<Sum>x\<in>UNIV. prob (u *\<^sub>R m + v *\<^sub>R n) i x) =
        u * (\<Sum>x\<in>UNIV. prob m i x) + v * (\<Sum>x\<in>UNIV. prob n i x)"
      by (simp add: prob_def sum.distrib sum_distrib_left)
    also have "\<dots> = 1"
      by (simp add: mixed_profiles_sum_prob mn uv)
    finally show ?thesis .
  qed
  show "u *\<^sub>R m + v *\<^sub>R n \<in> mixed_profiles"
    using in_box sum_one by (auto simp: mixed_profiles_def)
qed

lemma mixed_profiles_nonempty: "mixed_profiles \<noteq> {}"
  using uniform_mixed_profile_in_mixed_profiles by blast

lemma mixed_Nash_equilibrium_profile:
  assumes "mixed_Nash_equilibrium m"
  shows "m \<in> mixed_profiles"
  using assms by (simp add: mixed_Nash_equilibrium_def)

lemma mixed_Nash_equilibriumD:
  assumes "mixed_Nash_equilibrium m"
  shows "pure_deviation_payoff i x m \<le> mixed_payoff i m"
  using assms by (simp add: mixed_Nash_equilibrium_def)

lemma mixed_Nash_support_payoff_eq:
  assumes ne: "mixed_Nash_equilibrium m" and px: "prob m i x > 0"
  shows "pure_deviation_payoff i x m = mixed_payoff i m"
proof -
  have m: "m \<in> mixed_profiles"
    using ne by (rule mixed_Nash_equilibrium_profile)
  have gap_nonneg:
    "0 \<le> prob m i y * (mixed_payoff i m - pure_deviation_payoff i y m)" for y
    using mixed_profiles_prob_nonneg[OF m, of i y] mixed_Nash_equilibriumD[OF ne, of i y]
    by (intro mult_nonneg_nonneg) auto
  have "(\<Sum>y\<in>UNIV. prob m i y * (mixed_payoff i m - pure_deviation_payoff i y m)) =
        (\<Sum>y\<in>UNIV. prob m i y * mixed_payoff i m) -
        (\<Sum>y\<in>UNIV. prob m i y * pure_deviation_payoff i y m)"
    by (simp add: algebra_simps sum_subtractf)
  also have "\<dots> =
      (\<Sum>y\<in>UNIV. prob m i y) * mixed_payoff i m - mixed_payoff i m"
    unfolding mixed_payoff_def by (simp add: sum_distrib_right)
  also have "\<dots> =
      mixed_payoff i m * (\<Sum>y\<in>UNIV. prob m i y) - mixed_payoff i m"
    by (simp add: mult.commute)
  also have "\<dots> = 0"
    using mixed_profiles_sum_prob[OF m, of i] by simp
  finally have gaps_zero:
    "\<And>y. y \<in> UNIV \<Longrightarrow>
      prob m i y * (mixed_payoff i m - pure_deviation_payoff i y m) = 0"
    using gap_nonneg by (simp add: sum_nonneg_eq_0_iff)
  have "mixed_payoff i m - pure_deviation_payoff i x m = 0"
    using gaps_zero[of x] px by simp
  then show ?thesis
    by simp
qed

lemma mixed_Nash_zero_probability_if_less:
  assumes ne: "mixed_Nash_equilibrium m"
    and less: "pure_deviation_payoff i x m < mixed_payoff i m"
  shows "prob m i x = 0"
proof (rule ccontr)
  assume "prob m i x \<noteq> 0"
  moreover have "0 \<le> prob m i x"
    using mixed_Nash_equilibrium_profile[OF ne] by (rule mixed_profiles_prob_nonneg)
  ultimately have "pure_deviation_payoff i x m = mixed_payoff i m"
    using mixed_Nash_support_payoff_eq[OF ne] by simp
  then show False
    using less by simp
qed

definition dirac_mixed_profile :: "('p \<Rightarrow> 's) \<Rightarrow> ('p, 's) mixed_profile" where
  "dirac_mixed_profile s = (\<chi> ix. if snd ix = s (fst ix) then 1 else 0)"

lemma prob_dirac_mixed_profile [simp]:
  "prob (dirac_mixed_profile s) i x = (if x = s i then 1 else 0)"
  by (simp add: prob_def dirac_mixed_profile_def)

lemma dirac_mixed_profile_in_mixed_profiles [simp]:
  "dirac_mixed_profile s \<in> mixed_profiles"
  by (auto simp: mixed_profiles_def prob_def dirac_mixed_profile_def mem_box_cart)

lemma opponent_weight_dirac_mixed_profile:
  "opponent_weight i (dirac_mixed_profile s) t =
    (if \<forall>j. j \<noteq> i \<longrightarrow> t j = s j then 1 else 0)"
proof (cases "\<forall>j. j \<noteq> i \<longrightarrow> t j = s j")
  case True
  then show ?thesis
    by (auto simp: opponent_weight_def)
next
  case False
  then obtain j where j: "j \<noteq> i" "t j \<noteq> s j"
    by blast
  have j_in: "j \<in> UNIV - {i}"
    using j by simp
  have j_zero: "prob (dirac_mixed_profile s) j (t j) = 0"
    using j by simp
  have zero_ex: "\<exists>k\<in>UNIV - {i}. prob (dirac_mixed_profile s) k (t k) = 0"
    using j_in j_zero by blast
  have fin: "finite (UNIV - {i})"
    by simp
  have "(\<Prod>j\<in>UNIV - {i}. prob (dirac_mixed_profile s) j (t j)) = 0"
    by (rule prod_zero[OF fin zero_ex])
  then show ?thesis
    using False by (simp add: opponent_weight_def)
qed

lemma pure_deviation_payoff_dirac_mixed_profile:
  "pure_deviation_payoff i x (dirac_mixed_profile s) = payoff i (s(i := x))"
proof -
  have term_eq:
    "\<And>t. t \<in> {t. t i = x} \<Longrightarrow>
      opponent_weight i (dirac_mixed_profile s) t * payoff i t =
        (if t = s(i := x) then payoff i (s(i := x)) else 0)"
  proof -
    fix t
    assume t_in: "t \<in> {t. t i = x}"
    show "opponent_weight i (dirac_mixed_profile s) t * payoff i t =
        (if t = s(i := x) then payoff i (s(i := x)) else 0)"
    proof (cases "\<forall>j. j \<noteq> i \<longrightarrow> t j = s j")
      case True
      then have "t = s(i := x)"
        using t_in by (auto simp: fun_eq_iff)
      then show ?thesis
        using True by (simp add: opponent_weight_dirac_mixed_profile)
    next
      case False
      then have "t \<noteq> s(i := x)"
        by (auto simp: fun_eq_iff)
      moreover have "opponent_weight i (dirac_mixed_profile s) t = 0"
        using False by (simp add: opponent_weight_dirac_mixed_profile)
      then show ?thesis
        using calculation by simp
    qed
  qed
  have "pure_deviation_payoff i x (dirac_mixed_profile s) =
      (\<Sum>t\<in>{t. t i = x}. if t = s(i := x) then payoff i (s(i := x)) else 0)"
    unfolding pure_deviation_payoff_def
    by (intro sum.cong) (auto simp: term_eq)
  also have "\<dots> = payoff i (s(i := x))"
    by simp
  finally show ?thesis .
qed

lemma mixed_payoff_dirac_mixed_profile:
  "mixed_payoff i (dirac_mixed_profile s) = payoff i s"
proof -
  have "mixed_payoff i (dirac_mixed_profile s) =
      (\<Sum>x\<in>UNIV. if x = s i then payoff i (s(i := x)) else 0)"
    unfolding mixed_payoff_def
    by (intro sum.cong) (simp_all add: pure_deviation_payoff_dirac_mixed_profile)
  also have "\<dots> = payoff i s"
    by simp
  finally show ?thesis .
qed

lemma dirac_mixed_Nash_equilibrium:
  assumes "\<And>i x. payoff i (s(i := x)) \<le> payoff i s"
  shows "mixed_Nash_equilibrium (dirac_mixed_profile s)"
  using assms
  by (auto simp: mixed_Nash_equilibrium_def
      pure_deviation_payoff_dirac_mixed_profile mixed_payoff_dirac_mixed_profile)

lemma fixed_point_imp_excess_zero:
  assumes m: "m \<in> mixed_profiles" and fp: "nash_map m = m"
  shows "excess i x m = 0"
proof -
  let ?G = "excess_sum i m"
  have ex_eq: "excess i y m = prob m i y * ?G" for y
  proof -
    have eq: "prob m i y = (prob m i y + excess i y m) / (1 + ?G)"
      using arg_cong[OF fp, of "\<lambda>m. prob m i y"] by (simp add: prob_nash_map)
    then have mult_eq: "prob m i y * (1 + ?G) = prob m i y + excess i y m"
      using denom_pos[of i m] by (simp add: field_simps)
    then show "excess i y m = prob m i y * ?G"
      by (simp add: algebra_simps)
  qed
  show ?thesis
  proof (cases "?G = 0")
    case True
    then show ?thesis
      using ex_eq[of x] by simp
  next
    case False
    then have G_pos: "?G > 0"
      using excess_sum_nonneg[of i m] by linarith
    have pos_imp:
      "pure_deviation_payoff i x m = mixed_payoff i m + prob m i x * ?G" 
      if "prob m i x > 0" for x
    proof -
      have ex_pos: "excess i x m > 0"
        using that G_pos ex_eq[of x] by simp
      then have "pure_deviation_payoff i x m - mixed_payoff i m = excess i x m"
        by (simp add: excess_def)
      then show ?thesis
        using ex_eq[of x] by simp
    qed
    have payoff_eq:
      "prob m i y * pure_deviation_payoff i y m =
        prob m i y * mixed_payoff i m + ?G * (prob m i y)\<^sup>2" for y
    proof (cases "prob m i y = 0")
      case True
      then show ?thesis
        by simp
    next
      case False
      have "0 \<le> prob m i y"
        by (rule mixed_profiles_prob_nonneg[OF m])
      with False have "prob m i y > 0"
        by simp
      then show ?thesis
        using pos_imp[of y] by (simp add: algebra_simps power2_eq_square)
    qed
    have payoff_average:
      "mixed_payoff i m =
        mixed_payoff i m * (\<Sum>y\<in>UNIV. prob m i y) +
        ?G * (\<Sum>y\<in>UNIV. (prob m i y)\<^sup>2)"
    proof -
      have "mixed_payoff i m =
          (\<Sum>y\<in>UNIV. prob m i y * pure_deviation_payoff i y m)"
        by (simp add: mixed_payoff_def)
      also have "\<dots> =
          (\<Sum>y\<in>UNIV.
            prob m i y * mixed_payoff i m + ?G * (prob m i y)\<^sup>2)"
        by (intro sum.cong) (simp_all add: payoff_eq)
      also have "\<dots> =
          (\<Sum>y\<in>UNIV. prob m i y * mixed_payoff i m) +
          (\<Sum>y\<in>UNIV. ?G * (prob m i y)\<^sup>2)"
        by (simp add: sum.distrib)
      also have "\<dots> =
          (\<Sum>y\<in>UNIV. prob m i y) * mixed_payoff i m +
          ?G * (\<Sum>y\<in>UNIV. (prob m i y)\<^sup>2)"
        by (simp add: sum_distrib_left sum_distrib_right)
      also have "\<dots> =
          mixed_payoff i m * (\<Sum>y\<in>UNIV. prob m i y) +
          ?G * (\<Sum>y\<in>UNIV. (prob m i y)\<^sup>2)"
        by (simp add: mult.commute)
      finally show ?thesis .
    qed
    have "mixed_payoff i m =
        mixed_payoff i m + ?G * (\<Sum>y\<in>UNIV. (prob m i y)\<^sup>2)"
      using payoff_average mixed_profiles_sum_prob[OF m, of i] by simp
    then have G_squares_zero: "?G * (\<Sum>y\<in>UNIV. (prob m i y)\<^sup>2) = 0"
      by simp
    have sq_zero: "(\<Sum>y\<in>UNIV. (prob m i y)\<^sup>2) = 0"
      using G_pos G_squares_zero by simp
    have "\<exists>x. prob m i x > 0"
    proof (rule ccontr)
      assume no_pos: "\<not> (\<exists>x. prob m i x > 0)"
      have zero: "prob m i x = 0" for x
        by (smt (verit) m mixed_profiles_prob_nonneg no_pos)
      have "(\<Sum>x\<in>UNIV. prob m i x) = 0"
        by (simp add: zero)
      then show False
        using mixed_profiles_sum_prob[OF m, of i] by simp
    qed
    then obtain y where y: "prob m i y > 0"
      by blast
    have "0 < (prob m i y)\<^sup>2"
      using y by simp
    moreover have "(prob m i y)\<^sup>2 \<le> (\<Sum>x\<in>UNIV. (prob m i x)\<^sup>2)"
      by (intro member_le_sum) auto
    ultimately show ?thesis
      using sq_zero by simp
  qed
qed

theorem exists_mixed_Nash_equilibrium:
  "\<exists>m\<in>mixed_profiles. mixed_Nash_equilibrium m"
proof -
  obtain m where m: "m \<in> mixed_profiles" and fp: "nash_map m = m"
  proof (rule brouwer[
      OF mixed_profiles_compact mixed_profiles_convex mixed_profiles_nonempty continuous_nash_map])
    show "nash_map \<in> mixed_profiles \<rightarrow> mixed_profiles"
      using nash_map_in_mixed_profiles by auto
  qed
  have no_excess: "excess i x m = 0" for i x
    by (rule fixed_point_imp_excess_zero[OF m fp])
  have deviation_le: "pure_deviation_payoff i x m \<le> mixed_payoff i m" for i x
  proof -
    have "pure_deviation_payoff i x m - mixed_payoff i m
        \<le> max 0 (pure_deviation_payoff i x m - mixed_payoff i m)"
      by simp
    also have "\<dots> = 0"
      using no_excess[of i x] by (simp add: excess_def)
    finally show ?thesis
      by simp
  qed
  have "mixed_Nash_equilibrium m"
    using m deviation_le by (auto simp: mixed_Nash_equilibrium_def)
  then show ?thesis
    using m by blast
qed

end

end
