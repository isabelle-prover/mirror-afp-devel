section \<open>Lower-Bound Certificates\<close>

theory Lower_Bound_Certificates
  imports Main
begin

subsection \<open>STRIPS Planning Tasks\<close>

type_synonym 'v state = "'v set"

record ('v) action =
  pre :: "'v set"
  add :: "'v set"
  del :: "'v set"
  cost :: nat

record ('v) strips_task =
  \<comment> \<open>In our formalisation the add and delete lists of an action may
      overlap.  This is intentional — the semantics (Def of
      the successor function) gives add priority over delete, matching the
      standard STRIPS semantics from the literature.\<close>
  vars :: "'v set"
  acts :: "('v action) set"
  init :: "'v state"
  goal :: "'v set"

definition evars :: "('v action) \<Rightarrow> 'v set" where
  "evars a \<equiv> add a \<union> del a"

definition applicable :: "('v action) \<Rightarrow> 'v state \<Rightarrow> bool" where
  "applicable a s \<equiv> pre a \<subseteq> s"

definition successor :: "('v action) \<Rightarrow> 'v state \<Rightarrow> 'v state" where
  "successor a s \<equiv> (s - del a) \<union> add a"

inductive path ::
  "('v action) set \<Rightarrow> 'v state \<Rightarrow> 'v state \<Rightarrow> ('v action) list \<Rightarrow> bool"
  for A :: "('v action) set"
  where
    path_nil: "path A s s []"
  | path_cons: "\<lbrakk>applicable a s; path A (successor a s) t \<pi>; a \<in> A\<rbrakk>
    \<Longrightarrow> path A s t (a # \<pi>)"

definition is_goal_state :: "('v strips_task) \<Rightarrow> 'v state \<Rightarrow> bool" where
  "is_goal_state \<Pi> s \<equiv> goal \<Pi> \<subseteq> s"

definition is_plan_for :: "('v strips_task) \<Rightarrow> ('v action) list \<Rightarrow> bool" where
  "is_plan_for \<Pi> \<pi> \<equiv> \<exists>s. path (acts \<Pi>) (init \<Pi>) s \<pi> \<and> is_goal_state \<Pi> s"

definition plan_cost :: "('v action) list \<Rightarrow> nat" where
  "plan_cost \<pi> \<equiv> sum_list (map cost \<pi>)"

definition optimal_plan :: "('v strips_task) \<Rightarrow> ('v action) list \<Rightarrow> bool" where
  "optimal_plan \<Pi> \<pi> \<equiv> is_plan_for \<Pi> \<pi> \<and>
    (\<forall>\<pi>'. is_plan_for \<Pi> \<pi>' \<longrightarrow> plan_cost \<pi> \<le> plan_cost \<pi>')"

definition solvable :: "('v strips_task) \<Rightarrow> bool" where
  "solvable \<Pi> \<equiv> \<exists>\<pi>. is_plan_for \<Pi> \<pi>"


subsection \<open>Pseudo-Boolean Formulas\<close>

datatype 'v literal = Pos 'v | Neg 'v

definition lit_neg :: "'v literal \<Rightarrow> 'v literal" where
  "lit_neg l \<equiv> case l of Pos v \<Rightarrow> Neg v | Neg v \<Rightarrow> Pos v"

type_synonym 'v pb_constraint = "(nat \<times> 'v literal) list \<times> nat"

definition eval_lit :: "'v literal \<Rightarrow> ('v \<Rightarrow> nat) \<Rightarrow> nat" where
  "eval_lit l rho \<equiv> case l of Pos v \<Rightarrow> rho v | Neg v \<Rightarrow> 1 - rho v"

fun pb_sum :: "(nat \<times> 'v literal) list \<Rightarrow> ('v \<Rightarrow> nat) \<Rightarrow> nat" where
  "pb_sum [] rho = 0"
| "pb_sum ((a, l) # coeffs) rho = a * eval_lit l rho + pb_sum coeffs rho"

definition satisfies :: "'v pb_constraint \<Rightarrow> ('v \<Rightarrow> nat) \<Rightarrow> bool" where
  "satisfies C rho \<equiv>
    let (coeffs, A) = C
    in pb_sum coeffs rho \<ge> A"

definition models :: "'v pb_constraint set \<Rightarrow> ('v \<Rightarrow> nat) \<Rightarrow> bool" where
  "models CC rho \<equiv> \<forall>C \<in> CC. satisfies C rho"

definition unsat_01 :: "'v pb_constraint set \<Rightarrow> bool" where
  "unsat_01 CC \<equiv> \<not> (\<exists> rho. (\<forall> v. rho v = 0 \<or> rho v = 1) \<and> models CC rho)"

definition implies_constraint :: "'v pb_constraint set \<Rightarrow> 'v pb_constraint \<Rightarrow> bool" (infix "\<Turnstile>" 55) where
  "CC \<Turnstile> C \<equiv> \<forall>rho. models CC rho \<longrightarrow> satisfies C rho"

definition implies_formula :: "'v pb_constraint set \<Rightarrow> 'v pb_constraint set \<Rightarrow> bool" (infix "\<Turnstile>.." 55) where
  "CC \<Turnstile>.. DD \<equiv> \<forall>D \<in> DD. CC \<Turnstile> D"

definition constraint_neg :: "'v pb_constraint \<Rightarrow> 'v pb_constraint" where
  "constraint_neg C \<equiv> case C of (coeffs, A) \<Rightarrow>
    let M = sum_list (map fst coeffs)
    in (map (\<lambda>(a, l). (a, lit_neg l)) coeffs, M - (A - 1))"

subsection \<open>Cutting Planes with Reification (CPR)\<close>

definition unit_clause :: "'v literal \<Rightarrow> 'v pb_constraint" where
  "unit_clause l \<equiv> ([(1, l)], 1)"

lemma eval_lit_lit_neg_ge_one:
  "eval_lit l rho + eval_lit (lit_neg l) rho \<ge> 1"
  by (cases l; simp add: eval_lit_def lit_neg_def; metis add.commute le_zero_eq not_one_le_zero)

lemma pb_sum_add_negated_ge_sum:
  "pb_sum coeffs rho + pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) coeffs) rho
   \<ge> sum_list (map fst coeffs)"
proof (induction coeffs)
  case Nil
  then show ?case by simp
next
  case (Cons a_l coeffs)
  obtain a l where [simp]: "a_l = (a, l)" by (cases a_l)
  have X_ge_1: "eval_lit l rho + eval_lit (lit_neg l) rho \<ge> 1"
    using eval_lit_lit_neg_ge_one[of l rho] by blast
  have IH: "pb_sum coeffs rho + pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) coeffs) rho \<ge> sum_list (map fst coeffs)"
    using Cons.IH by blast
  have "a + sum_list (map fst coeffs)
    \<le> a * (eval_lit l rho + eval_lit (lit_neg l) rho)
      + (pb_sum coeffs rho + pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) coeffs) rho)"
    using X_ge_1 IH by (intro add_mono mult_le_mono order_refl; simp)
  also have "... = a * eval_lit l rho + a * eval_lit (lit_neg l) rho
      + (pb_sum coeffs rho + pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) coeffs) rho)"
  proof -
    have "a * (eval_lit l rho + eval_lit (lit_neg l) rho) = a * eval_lit l rho + a * eval_lit (lit_neg l) rho"
      by (simp add: distrib_left)
    then show ?thesis by simp
  qed
  also have "... = pb_sum ((a, l) # coeffs) rho + pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) ((a, l) # coeffs)) rho"
    by (simp add: add_ac)
  finally show ?case by simp
qed

definition linear_combination :: "nat \<Rightarrow> 'v pb_constraint \<Rightarrow> nat \<Rightarrow> 'v pb_constraint \<Rightarrow> 'v pb_constraint" where
  "linear_combination cA C cB D \<equiv>
    case (C, D) of ((coeffsA, A), (coeffsB, B)) \<Rightarrow>
      (map (\<lambda>(a, l). (cA * a, l)) coeffsA @ map (\<lambda>(b, l). (cB * b, l)) coeffsB, cA * A + cB * B)"

definition division :: "nat \<Rightarrow> 'v pb_constraint \<Rightarrow> 'v pb_constraint" where
  "division c C \<equiv> case C of (coeffs, A) \<Rightarrow>
    (map (\<lambda>(a, l). ((a + c - 1) div c, l)) coeffs, (A + c - 1) div c)"

definition saturation :: "'v pb_constraint \<Rightarrow> 'v pb_constraint" where
  "saturation C \<equiv> case C of (coeffs, A) \<Rightarrow>
    (map (\<lambda>(a, l). (min a A, l)) coeffs, A)"

inductive cpr_derives :: "'v pb_constraint set \<Rightarrow> 'v pb_constraint \<Rightarrow> bool" where
  hyp: "C \<in> CC \<Longrightarrow> cpr_derives CC C"
| lit_ax: "cpr_derives CC ([(1, l)], 0)"
| lin_comb: "\<lbrakk>cpr_derives CC C; cpr_derives CC D\<rbrakk>
    \<Longrightarrow> cpr_derives CC (linear_combination cA C cB D)"
| div_rule: "\<lbrakk>cpr_derives CC C; c \<ge> 1\<rbrakk> \<Longrightarrow> cpr_derives CC (division c C)"
| sat_rule: "cpr_derives CC C \<Longrightarrow> cpr_derives CC (saturation C)"
  \<comment> \<open>The semantic RUP rule over-approximates actual unit-propagation-based
      RUP, but the over-approximation is still sound for proving unsatisfiability
      of 0-1-constrained constraint sets.\<close>
| rup: "unsat_01 (CC \<union> {constraint_neg C}) \<Longrightarrow> cpr_derives CC C"

lemma hyp_sound: "C \<in> CC \<Longrightarrow> models CC rho \<Longrightarrow> satisfies C rho"
  unfolding models_def by blast

lemma pb_sum_map_mul: "pb_sum (map (\<lambda>(a, l). (k * a, l)) xs) rho = k * pb_sum xs rho"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons p xs)
  then obtain a l where "p = (a, l)" by (cases p) auto
  then show ?case using Cons by (simp add: algebra_simps)
qed

lemma pb_sum_append: "pb_sum (xs @ ys) rho = pb_sum xs rho + pb_sum ys rho"
  by (induct xs) auto

lemma lin_comb_sound:
  assumes "satisfies C rho" "satisfies D rho"
  shows "satisfies (linear_combination nC C nD D) rho"
proof -
  obtain coeffsA A where C: "C = (coeffsA, A)" by (cases C)
  obtain coeffsB B where D: "D = (coeffsB, B)" by (cases D)
  have sum_distrib: "pb_sum (map (\<lambda>(a, l). (nC * a, l)) coeffsA @ map (\<lambda>(b, l). (nD * b, l)) coeffsB) rho
    = nC * pb_sum coeffsA rho + nD * pb_sum coeffsB rho"
    by (simp add: pb_sum_append pb_sum_map_mul)
  from assms have Ap: "pb_sum coeffsA rho \<ge> A" and Bp: "pb_sum coeffsB rho \<ge> B"
    unfolding satisfies_def C D by auto
  have "nC * pb_sum coeffsA rho + nD * pb_sum coeffsB rho \<ge> nC * A + nD * B"
    using Ap Bp by (simp add: add_mono mult_le_mono)
  then show ?thesis
    using sum_distrib unfolding satisfies_def linear_combination_def C D
    by simp
qed

lemma pb_sum_ge_term: "(a, l) \<in> set coeffs \<Longrightarrow> pb_sum coeffs rho \<ge> a * eval_lit l rho"
proof (induct coeffs arbitrary: a l)
  case Nil
  then show ?case by simp
next
  case (Cons p coeffs)
  then obtain a' l' where p_eq: "p = (a', l')" by (cases p) auto
  show ?case
  proof (cases "(a, l) = (a', l')")
    case True
    then show ?thesis unfolding p_eq by simp
  next
    case False
    then have "(a, l) \<in> set coeffs" using Cons.prems p_eq by auto
    then have "pb_sum coeffs rho \<ge> a * eval_lit l rho" using Cons.hyps by blast
    then show ?thesis unfolding p_eq
      by (simp add: le_trans le_add2)
  qed
qed

lemma ceil_ge:
  fixes a c :: nat
  assumes "c > 0"
  shows "((a + c - 1) div c) * c \<ge> a"
  using assms by (metis add.commute add_less_cancel_right bot_nat_0.not_eq_extremum dec_less_imp_less_eq diff_less
      dividend_less_times_div le_eq_less_or_eq mult.commute zero_less_one)

lemma mul_ge_imp_ceil_div_ge:
  fixes m n c :: nat
  assumes "c \<ge> 1" "m * c \<ge> n"
  shows "m \<ge> (n + c - 1) div c"
proof (cases "n = 0")
  case True    then show ?thesis using `c \<ge> 1` by simp
next
  case False
  then have "n > 0" by simp
  show ?thesis
  proof (rule ccontr)
    assume "\<not> m \<ge> (n + c - 1) div c"
    then have "m < (n + c - 1) div c" by simp
    then have "Suc m \<le> (n + c - 1) div c" by simp
    then have "Suc m * c \<le> ((n + c - 1) div c) * c"
      by (metis `Suc m \<le> (n + c - 1) div c` order_refl mult_le_mono)
    also have "... \<le> n + c - 1"
    proof -
      have *: "((n + c - 1) div c) * c + (n + c - 1) mod c = n + c - 1"
        by (simp add: div_mult_mod_eq)
      show ?thesis by (simp add: add_leE *)
    qed
    finally have "Suc m * c \<le> n + c - 1" .
    then have "m * c + c \<le> n + c - 1"
      by (metis `Suc m * c \<le> n + c - 1` mult_Suc add.commute)
    then have "m * c + c \<le> (n - 1) + c" using `n > 0` by (simp add: add_diff_inverse_nat)
    then have "m * c \<le> n - 1" using add_le_imp_le_right by blast
    then have "m * c < n" using `n > 0` by simp
    with assms(2) show False by simp
  qed
qed

lemma ceil_add_ineq:
  fixes a b c :: nat
  assumes "c \<ge> 1"
  shows "(a + c - 1) div c + (b + c - 1) div c \<ge> (a + b + c - 1) div c"
proof -
  have "((a + c - 1) div c + (b + c - 1) div c) * c = ((a + c - 1) div c) * c + ((b + c - 1) div c) * c"
    by (simp add: distrib_right)
  also have "... \<ge> a + b"
  proof -
    have "c > 0" using assms(1) by auto
    then have "((a + c - 1) div c) * c \<ge> a" and "((b + c - 1) div c) * c \<ge> b"
      using ceil_ge by blast+
    then show ?thesis by (simp add: add_le_mono)
  qed
  finally have sum_mul_ge: "((a + c - 1) div c + (b + c - 1) div c) * c \<ge> a + b" .
  show ?thesis
    using assms sum_mul_ge by (rule mul_ge_imp_ceil_div_ge)
qed

lemma div_rule_sound:
  assumes "c \<ge> 1" "satisfies C rho"
  shows "satisfies (division c C) rho"
proof -
  obtain coeffs A where C: "C = (coeffs, A)" by (cases C)
  have sum_ge_A: "pb_sum coeffs rho \<ge> A"
    using assms unfolding satisfies_def C by simp
  have "pb_sum (map (\<lambda>(a,l). ((a + c - 1) div c, l)) coeffs) rho \<ge> (pb_sum coeffs rho + c - 1) div c"
  proof (induct coeffs)
    case Nil
    then show ?case using `c \<ge> 1` by simp
  next
    case (Cons p coeffs)
    obtain a l where p_eq: "p = (a, l)" by (cases p) auto
    have IH: "pb_sum (map (\<lambda>(a,l). ((a + c - 1) div c, l)) coeffs) rho \<ge> (pb_sum coeffs rho + c - 1) div c"
      using Cons by auto
    have mul_ineq: "((a + c - 1) div c) * eval_lit l rho * c \<ge> a * eval_lit l rho"
    proof -
      have "((a + c - 1) div c) * eval_lit l rho * c = ((a + c - 1) div c) * c * eval_lit l rho"
        by (simp add: mult.commute mult.left_commute mult.assoc)
      also have "... \<ge> a * eval_lit l rho"
      proof -
        have "c > 0" using assms(1) by auto
        then have "((a + c - 1) div c) * c \<ge> a" using ceil_ge by blast
        then show ?thesis using mult_le_mono1 by blast
      qed
      finally show ?thesis .
    qed
    have div_ineq: "((a + c - 1) div c) * eval_lit l rho \<ge> (a * eval_lit l rho + c - 1) div c"
      by (rule mul_ge_imp_ceil_div_ge[OF assms(1) mul_ineq])
    have step1: "((a + c - 1) div c) * eval_lit l rho + pb_sum (map (\<lambda>(a,l). ((a + c - 1) div c, l)) coeffs) rho
      \<ge> (a * eval_lit l rho + c - 1) div c + (pb_sum coeffs rho + c - 1) div c"
      using div_ineq IH by (simp add: add_le_mono)
    have step2: "(a * eval_lit l rho + c - 1) div c + (pb_sum coeffs rho + c - 1) div c
      \<ge> (a * eval_lit l rho + pb_sum coeffs rho + c - 1) div c"
      using assms(1) by (rule ceil_add_ineq)
    show ?case unfolding p_eq
      using step1 step2 by auto
  qed
  then have *: "(pb_sum coeffs rho + c - 1) div c \<le> pb_sum (map (\<lambda>(a,l). ((a + c - 1) div c, l)) coeffs) rho"
    by simp
  have "A + c - 1 \<le> pb_sum coeffs rho + c - 1" using sum_ge_A by simp
  then have "(A + c - 1) div c \<le> (pb_sum coeffs rho + c - 1) div c" by (rule div_le_mono)
  then have "pb_sum (map (\<lambda>(a,l). ((a + c - 1) div c, l)) coeffs) rho \<ge> (A + c - 1) div c"
    using * by (meson le_trans)
  then show ?thesis unfolding satisfies_def division_def C by simp
qed

lemma sat_rule_sound:
  assumes "satisfies C rho"
  shows "satisfies (saturation C) rho"
proof -
  obtain coeffs A where C: "C = (coeffs, A)" by (cases C)
  have sum_ge_A: "pb_sum coeffs rho \<ge> A"
    using assms unfolding satisfies_def C by simp
  have "pb_sum (map (\<lambda>(a,l). (min a A, l)) coeffs) rho \<ge> A"
  proof (cases "\<exists>(a,l)\<in>set coeffs. a \<ge> A \<and> eval_lit l rho > 0")
    case True
    then obtain a l where "(a,l)\<in>set coeffs" "a \<ge> A" "eval_lit l rho > 0" by blast
    have "(min a A, l) \<in> set (map (\<lambda>(a,l). (min a A, l)) coeffs)"
      using `(a,l)\<in>set coeffs` by force
    then have "pb_sum (map (\<lambda>(a,l). (min a A, l)) coeffs) rho \<ge> (min a A) * eval_lit l rho"
      by (rule pb_sum_ge_term)
    moreover have "(min a A) * eval_lit l rho \<ge> A"
      using `a \<ge> A` `eval_lit l rho > 0` by (simp add: min_absorb2 mult_le_mono)
    ultimately show ?thesis by simp
  next
    case False
    then have "\<forall>(a,l)\<in>set coeffs. a < A \<or> eval_lit l rho = 0" by auto
    then have "pb_sum (map (\<lambda>(a,l). (min a A, l)) coeffs) rho = pb_sum coeffs rho"
    proof (induct coeffs)
      case Nil
      then show ?case by simp
    next
      case (Cons p coeffs)
      obtain a l where "p = (a, l)" by (cases p) auto
      then have "a < A \<or> eval_lit l rho = 0" using Cons by auto
      moreover have "pb_sum (map (\<lambda>(a,l). (min a A, l)) coeffs) rho = pb_sum coeffs rho"
        using Cons by auto
      ultimately show ?case unfolding `p = (a,l)`
        by (auto simp: min_def)
    qed
    then show ?thesis using sum_ge_A by simp
  qed
  then show ?thesis
    unfolding satisfies_def saturation_def C by simp
qed

theorem cpr_sound:
  assumes "cpr_derives CC C" and "models CC rho" and "\<forall> v. rho v = 0 \<or> rho v = 1"
  shows "satisfies C rho"
  using assms
proof (induct arbitrary: rho rule: cpr_derives.induct)
  case (hyp CC C)
  then show ?case by (simp add: hyp_sound)
next
  case (lit_ax CC l)
  then show ?case by (simp add: satisfies_def eval_lit_def)
next
  case (lin_comb CC C D cA cB)
  then have "satisfies C rho" and "satisfies D rho" by blast+
  then show ?case by (blast intro: lin_comb_sound)
next
  case (div_rule CC C c)
  then show ?case using div_rule_sound by blast
next
  case (sat_rule CC C)
  then show ?case using sat_rule_sound by blast
next
  case (rup CC C)
  then have unsat: "unsat_01 (CC \<union> {constraint_neg C})" by simp
  show ?case
  proof (rule ccontr)
    assume "\<not> satisfies C rho"
    obtain coeffs A where C: "C = (coeffs, A)" by (cases C)
    from `\<not> satisfies C rho` have X_lt_A: "pb_sum coeffs rho < A"
      unfolding satisfies_def C by simp
    let ?X = "pb_sum coeffs rho"
    let ?Y = "pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) coeffs) rho"
    let ?M = "sum_list (map fst coeffs)"
    have X_Y_ge_M: "?X + ?Y \<ge> ?M"
      using pb_sum_add_negated_ge_sum[of coeffs rho] by simp
    have "satisfies (constraint_neg C) rho"
    proof (cases "A = 0")
      case True
      then have "?X < 0" using X_lt_A by simp
      then show ?thesis by simp
    next
      case False
      then have "A \<ge> 1" by simp
      then have X_le_A_minus_1: "?X \<le> A - 1" using X_lt_A by linarith
      have "?Y \<ge> ?M - (A - 1)"
      proof -
        have "?M - ?X \<le> ?Y"
          using X_Y_ge_M by auto
        moreover have "?M - (A - 1) \<le> ?M - ?X"
          using X_le_A_minus_1 by (simp add: diff_le_mono2)
        ultimately show ?thesis by (meson order_trans)
      qed
      then show ?thesis
        by (simp add: constraint_neg_def C satisfies_def Let_def)
    qed
    then have sat_neg: "models (CC \<union> {constraint_neg C}) rho"
      using `models CC rho` unfolding models_def by auto
    have "\<not> unsat_01 (CC \<union> {constraint_neg C})"
      unfolding unsat_01_def
      using sat_neg `\<forall> v. rho v = 0 \<or> rho v = 1` by blast
    with unsat show False by blast
  qed
qed

subsection \<open>PB Task Encoding (Definition 1)\<close>

(* Combined variable type for PB encoding of a planning task *)
datatype 'v pvar =
  StateVar 'v
| CostBit nat | PrimedCostBit nat
| ReifI | ReifG | ReifT
| ReifEq 'v | ReifLeq 'v | ReifGeq 'v | ReifCostGe nat
| ReifAction nat
| ReifDeltaCostLower nat  \<comment> \<open>auxiliary reifying cost difference >= k\<close>
| ReifDeltaCostUpper nat  \<comment> \<open>auxiliary reifying cost difference <= k\<close>
| ReifDeltaCost nat   \<comment> \<open>from eq (3): reifies cost difference = k\<close>
| ReifPrimedCostGe nat  \<comment> \<open>from eq (5): reifies primed cost >= k\<close>
| ReifCert 'v  \<comment> \<open>fresh certificate variables, wrapped by Original/Primed when lifted\<close>

type_synonym 'v pconstraint = "'v pvar pb_constraint"

definition reif_fwd :: "'v pvar literal \<Rightarrow> (nat \<times> 'v pvar literal) list \<Rightarrow> nat \<Rightarrow> 'v pconstraint" where
  "reif_fwd r coeffs A \<equiv> ([(A, lit_neg r)] @ coeffs, A)"

definition reif_bwd :: "'v pvar literal \<Rightarrow> (nat \<times> 'v pvar literal) list \<Rightarrow> nat \<Rightarrow> 'v pconstraint" where
  "reif_bwd r coeffs A \<equiv>
    let M = sum_list (map fst coeffs); M' = M + 1 - A in
    ([(M', r)] @ map (\<lambda>(a, l). (a, lit_neg l)) coeffs, M')"

definition reification :: "'v pvar literal \<Rightarrow> (nat \<times> 'v pvar literal) list \<Rightarrow> nat \<Rightarrow> 'v pconstraint set" where
  "reification r coeffs A \<equiv> {reif_fwd r coeffs A, reif_bwd r coeffs A}"

definition state_lits :: "'v::linorder set \<Rightarrow> (nat \<times> 'v pvar literal) list" where
  "state_lits S \<equiv> map (\<lambda>v. (1, Pos (StateVar v))) (sorted_list_of_set S)"

definition neg_state_lits :: "'v::linorder set \<Rightarrow> (nat \<times> 'v pvar literal) list" where
  "neg_state_lits S \<equiv> map (\<lambda>v. (1, Neg (StateVar v))) (sorted_list_of_set S)"

(* Encoding of initial state: eq (1) r_I \<Leftrightarrow> \<Sigma>_{v\<in>I} v + \<Sigma>_{v\<in>V\I} \<not>v \<ge> |V| *)
definition encode_init :: "'v::linorder strips_task \<Rightarrow> 'v pconstraint set" where
  "encode_init \<Pi> \<equiv>
    let I = init \<Pi>; V = vars \<Pi> in
    reification (Pos ReifI)
      (state_lits I @ neg_state_lits (V - I)) (card V)"

(* goal encoding: eq (2) r_G \<Leftrightarrow> \<Sigma>_{v\<in>G} v \<ge> |G|. *)
definition encode_goal :: "'v::linorder strips_task \<Rightarrow> 'v pconstraint set" where
  "encode_goal \<Pi> \<equiv>
    let G = goal \<Pi> in
    reification (Pos ReifG) (state_lits G) (card G)"

(* Number of bits needed to represent values up to B (\<lceil>log₂(B+1)\<rceil>). *)
definition bits_needed :: "nat \<Rightarrow> nat" where
  "bits_needed B \<equiv> (LEAST k. B < 2^k)"

lemma bits_needed_sufficient: "B < 2^(bits_needed B)"
  unfolding bits_needed_def
proof (rule LeastI_ex)
  show "\<exists>k. B < 2^k"
  proof (induction B)
    case 0
    show ?case by (rule exI[of _ 1]) simp
  next
    case (Suc B)
    then obtain k where "B < 2^k" by blast
    then have "Suc B \<le> 2^k" by simp
    then have "Suc B < 2^(Suc k)" by (simp add: less_Suc_eq_le)
    then show ?case by blast
  qed
qed

lemma bits_needed_upper_bound: "bits_needed B \<le> B + 1"
proof -
  have "B < 2^(B+1)"
    by (metis add_lessD1 less_exp)
  then have "bits_needed B \<le> B+1"
    unfolding bits_needed_def by (rule Least_le)
  thus ?thesis by simp
qed

lemma c_mod_bits_needed: "c < 2^(bits_needed B) \<Longrightarrow> c mod (2::nat)^(bits_needed B) = c"
  by simp

(* binary threshold encoding using coefficients 2^i. *)
definition encode_cost_ge :: "nat \<Rightarrow> 'v pconstraint set" where
  "encode_cost_ge k \<equiv>
    reification (Pos (ReifCostGe k)) (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed k]) k"

subsection \<open>Transition Encoding (Equations 3--8)\<close>


(* Wrapper to distinguish original (unprimed) from primed planning variables.
   Used so that the primed circuit has genuinely fresh variables. *)
datatype 'v var = Original 'v | Primed 'v

instantiation var :: (linorder) linorder
begin
definition less_eq_var :: "'a var \<Rightarrow> 'a var \<Rightarrow> bool" where
  "less_eq_var x y \<equiv> case (x, y) of
    (Original a, Original b) \<Rightarrow> a \<le> b
  | (Original _, Primed _)   \<Rightarrow> True
  | (Primed _,  Original _)  \<Rightarrow> False
  | (Primed a,  Primed b)    \<Rightarrow> a \<le> b"
definition less_var :: "'a var \<Rightarrow> 'a var \<Rightarrow> bool" where
  "less_var x y \<equiv> x \<le> y \<and> \<not> y \<le> x"
instance by standard
  (auto simp: less_eq_var_def less_var_def split: var.splits)
end

(* Primed copies of state variables: maps Original v \<rightarrow> Primed v (idempotent on Primed) *)
definition prime_var :: "'v var \<Rightarrow> 'v var" where
  "prime_var x \<equiv> case x of Original v \<Rightarrow> Primed v | Primed v \<Rightarrow> Primed v"

(* Lift priming to pvar: uses map_pvar to prime all 'v-indexed constructors
   (StateVar, ReifEq, ReifLeq, ReifGeq); CostBit, PrimedCostBit, ReifT, etc. unchanged *)
definition primed_pvar :: "'v var pvar \<Rightarrow> 'v var pvar" where
  "primed_pvar x \<equiv> map_pvar prime_var x"



(* Lift a plain 'v pvar \<rightarrow> nat assignment to 'v var pvar \<rightarrow> nat for use with orig_circuit/primed_circuit.
   StateVar (Original v) and StateVar (Primed v) both map to f (StateVar v);
   PrimedCostBit i maps to f (CostBit i) (same cost, both sides of a transition step). *)
definition lift_to_var :: "('v pvar \<Rightarrow> nat) \<Rightarrow> ('v var pvar \<Rightarrow> nat)" where
  "lift_to_var f \<equiv> \<lambda>x. case x of
    StateVar v      \<Rightarrow> f (StateVar (case v of Original w \<Rightarrow> w | Primed w \<Rightarrow> w))
  | CostBit i       \<Rightarrow> f (CostBit i)
  | PrimedCostBit i \<Rightarrow> f (CostBit i)
  | y               \<Rightarrow> f (map_pvar (case_var id id) y)"

(* Assign each action a unique reification literal Pos (ReifAction i) *)
definition action_reifs :: "'v action list \<Rightarrow> 'v var pvar literal list" where
  "action_reifs as \<equiv> map (\<lambda>i. Pos (ReifAction i)) [0..<length as]"

(* Encoding of eq (3): \<Delta>C=k \<Leftrightarrow> \<Sigma> 2^i c'_i - \<Sigma> 2^i c_i = k.
   Three-level circuit:
     r_lower \<Leftrightarrow> c' \<ge> c+k  via reification with coeffs (cost'_lits @ neg_c_lits) and threshold k+M
     r_upper \<Leftrightarrow> c' \<le> c+k  via reification with coeffs (cost_lits @ neg_c'_lits) and threshold M-k
     r_\<Delta>    \<Leftrightarrow> r_lower \<and> r_upper  via reification on [r_lower, r_upper] with threshold 2 *)
definition encode_delta_cost :: "nat \<Rightarrow> nat \<Rightarrow> 'v var pconstraint set" where
  "encode_delta_cost k num_bits \<equiv>
    let cost_lits   = map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<num_bits];
        cost'_lits  = map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<num_bits];
        neg_c_lits  = map (\<lambda>i. (2^i, Neg (CostBit i))) [0..<num_bits];
        neg_c'_lits = map (\<lambda>i. (2^i, Neg (PrimedCostBit i))) [0..<num_bits];
        M           = 2^num_bits - 1
    in reification (Pos (ReifDeltaCostLower k)) (cost'_lits @ neg_c_lits) (k + M)
     \<union> reification (Pos (ReifDeltaCostUpper k)) (cost_lits @ neg_c'_lits) (M - k)
     \<union> reification (Pos (ReifDeltaCost k))
                   [(1, Pos (ReifDeltaCostLower k)), (1, Pos (ReifDeltaCostUpper k))] 2"

(* encoding of eq (5): cost'\<ge>k \<Leftrightarrow> \<Sigma> 2^i c'_i \<ge> k. *)
definition encode_cost_ge_primed :: "nat \<Rightarrow> 'v var pconstraint set" where
  "encode_cost_ge_primed k \<equiv>
    reification (Pos (ReifPrimedCostGe k))
      (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<bits_needed k]) k"

(* Eq (6): eq_{v,v'} \<Leftrightarrow> leq_{v,v'} + geq_{v,v'} \<ge> 2 *)
definition encode_eq_var :: "'v \<Rightarrow> 'v var pconstraint set" where
  "encode_eq_var v \<equiv>
    reification (Pos (ReifGeq (Original v))) [(1, Pos (StateVar (Original v))), (1, Neg (StateVar (Primed v)))] 1
  \<union> reification (Pos (ReifLeq (Original v))) [(1, Neg (StateVar (Original v))), (1, Pos (StateVar (Primed v)))] 1
  \<union> reification (Pos (ReifEq (Original v)))  [(1, Pos (ReifLeq (Original v))), (1, Pos (ReifGeq (Original v)))] 2"

(* Eq (7): single combined implication constraint per action *)
definition action_constraint ::
  "'v var pvar literal \<Rightarrow> 'v::linorder action \<Rightarrow> 'v set \<Rightarrow> nat \<Rightarrow> 'v var pconstraint" where
  "action_constraint r a V B \<equiv>
    let pre_lits   = map (\<lambda>v. (1, Pos (StateVar (Original v)))) (sorted_list_of_set (pre a));
        add_lits   = map (\<lambda>v. (1, Pos (StateVar (Primed v)))) (sorted_list_of_set (add a));
        del_lits   = map (\<lambda>v. (1, Neg (StateVar (Primed v)))) (sorted_list_of_set (del a));
        frame_lits = map (\<lambda>v. (1, Pos (ReifEq (Original v)))) (sorted_list_of_set (V - evars a));
        delta_lit  = [(1, Pos (ReifDeltaCost (cost a)))];
        bound_lit  = [(1, Neg (ReifPrimedCostGe B))];
        A   = 2 + card (pre a) + card V;
        lhs = [(A, lit_neg r)] @ delta_lit @ pre_lits @ add_lits @ del_lits @ frame_lits @ bound_lit
    in (lhs, A)"

(* Eq (8): r_T \<Leftrightarrow> \<Sigma>_{a\<in>\<A>} r_a \<ge> 1, using ReifT as the reification variable. *)
definition action_selection_reif ::
  "'v var pvar literal list \<Rightarrow> 'v var pconstraint set" where
  "action_selection_reif rs \<equiv>
    reification (Pos ReifT) (map (\<lambda>r. (1, r)) rs) 1"

(* full transition encoding for one step (eqs 3–8) *)
definition encode_transition ::
  "'v::linorder action list \<Rightarrow> 'v set \<Rightarrow> nat \<Rightarrow> 'v var pconstraint set" where
  "encode_transition as V B \<equiv>
    let rs          = action_reifs as;
        action_cs   = (\<Union>i<length as.
                        {action_constraint (rs!i) (as!i) V B});
        delta_cs    = (\<Union>a\<in>set as. encode_delta_cost (cost a) (bits_needed B));
        eq_cs       = (\<Union>v\<in>V. encode_eq_var v);
        primed_ge_c = encode_cost_ge_primed B;
        sel_cs      = action_selection_reif rs
    in action_cs \<union> delta_cs \<union> eq_cs \<union> primed_ge_c \<union> sel_cs"

subsection \<open>PB Circuits (Definition 2)\<close>

(* A PB circuit is a list of (reif-literal, constraint) pairs plus an output literal.
   The type parameter 'v is the planning variable type; all pvar constructors are plain 'v pvar.
   Lifting to 'v var pvar (for use alongside the transition encoding) is done separately
   via orig_circuit / primed_circuit. *)
type_synonym 'v pb_circuit = "('v pvar literal \<times> (nat \<times> 'v pvar literal) list \<times> nat) list \<times> 'v pvar literal"

definition models_circuit :: "'v pb_circuit \<Rightarrow> ('v pvar \<Rightarrow> nat) \<Rightarrow> bool" where
  "models_circuit C rho \<equiv>
    let (pairs, out) = C in
    eval_lit out rho = 1 \<and>
    (\<forall>(r, coeffs, A) \<in> set pairs. pb_sum coeffs rho \<ge> A)"

(* Extract the underlying pvar from a literal. *)
definition pvar_of_lit :: "'v pvar literal \<Rightarrow> 'v pvar" where
  "pvar_of_lit l \<equiv> case l of Pos x \<Rightarrow> x | Neg x \<Rightarrow> x"

(* Input variables of a PB circuit: state variables and cost bits.
   These may appear in any constraint \<phi>_i without restriction.
   (PrimedCostBit only arises in transition encodings, not in circuits.) *)
definition is_input_pvar :: "'v pvar \<Rightarrow> bool" where
  "is_input_pvar x \<equiv> (\<exists>v. x = StateVar v) \<or> (\<exists>i. x = CostBit i) \<or> (\<exists>i. x = PrimedCostBit i)"

(* Variables referenced (with any coefficient) in a constraint. *)
definition constraint_pvars :: "'v pconstraint \<Rightarrow> 'v pvar set" where
  "constraint_pvars \<phi> \<equiv> pvar_of_lit ` (snd ` set (fst \<phi>))"

(* Well-formedness of a PB circuit (paper Definition 2):
   each constraint \<phi>_i may only reference input variables or reification
   variables r_j defined strictly earlier (j < i) in the sequence.
   In particular r_i itself must NOT appear in \<phi>_i (strict acyclicity).
   The output variable must appear as a reification variable in the list. *)
definition wf_circuit :: "'v pb_circuit \<Rightarrow> bool" where
  "wf_circuit C \<equiv>
    let (pairs, out) = C in
    (\<forall>i < length pairs.
      let (r_i, cs_i, A_i) = pairs ! i;
          allowed = {x. is_input_pvar x} \<union>
                    (pvar_of_lit ` fst ` set (take i pairs))
      in (pvar_of_lit ` snd ` set cs_i) \<subseteq> allowed) \<and>
    (Pos (pvar_of_lit out) \<in> fst ` set pairs \<or> Neg (pvar_of_lit out) \<in> fst ` set pairs)"


subsection \<open>State-Cost Assignments and Certificate Conditions\<close>

definition state_rho :: "'v::linorder strips_task \<Rightarrow> 'v state \<Rightarrow> nat \<Rightarrow> ('v pvar \<Rightarrow> nat)" where
  "state_rho \<Pi> s c \<equiv> \<lambda>x. case x of
    StateVar v \<Rightarrow> if v \<in> s then 1 else 0
  | CostBit i \<Rightarrow> (c div 2^i) mod 2
  | ReifI \<Rightarrow> (let V = vars \<Pi>; I = init \<Pi> in
      if (\<forall>v\<in>V. (v\<in>I \<longleftrightarrow> v\<in>s)) then 1 else 0)
  | ReifG \<Rightarrow> if is_goal_state \<Pi> s then 1 else 0
  | ReifCostGe k \<Rightarrow> if c \<ge> k then 1 else 0
  | _ \<Rightarrow> 0"

subsection \<open>Lifting Circuits to the Primed/Unprimed Context\<close>

(* Lift a plain 'v pb_circuit to a 'v var pb_circuit by wrapping all pvars with f.
   Used with f = map_pvar Original (for the current-state circuit) and
   f = primed_pvar_map (for the next-state circuit). *)
definition lift_circuit :: "('v pvar \<Rightarrow> 'v var pvar) \<Rightarrow> 'v pb_circuit \<Rightarrow> 'v var pb_circuit" where
  "lift_circuit f C \<equiv>
    let (pairs, out) = C in
    (map (\<lambda>(r, cs, A). (map_literal f r,
                        map (\<lambda>(a, l). (a, map_literal f l)) cs,
                        A)) pairs,
     map_literal f out)"

(* Lift with Original: embeds the circuit into the unprimed ('v var) context *)
definition orig_circuit :: "'v pb_circuit \<Rightarrow> 'v var pb_circuit" where
  "orig_circuit C \<equiv> lift_circuit (map_pvar Original) C"

(* primed_pvar_map: maps each pvar to its primed counterpart.
   StateVar v \<rightarrow> StateVar (Primed v); CostBit i \<rightarrow> PrimedCostBit i;
   reification variables that carry 'v are primed; others stay the same. *)
primrec primed_pvar_map :: "'v pvar \<Rightarrow> 'v var pvar" where
  "primed_pvar_map (StateVar v) = StateVar (Primed v)"
| "primed_pvar_map (CostBit i) = PrimedCostBit i"
| "primed_pvar_map (PrimedCostBit i) = PrimedCostBit i"
| "primed_pvar_map ReifI = ReifI"
| "primed_pvar_map ReifG = ReifG"
| "primed_pvar_map ReifT = ReifT"
| "primed_pvar_map (ReifEq v) = ReifEq (Primed v)"
| "primed_pvar_map (ReifLeq v) = ReifLeq (Primed v)"
| "primed_pvar_map (ReifGeq v) = ReifGeq (Primed v)"
| "primed_pvar_map (ReifCostGe n) = ReifCostGe n"
| "primed_pvar_map (ReifAction n) = ReifAction n"
| "primed_pvar_map (ReifDeltaCostLower n) = ReifDeltaCostLower n"
| "primed_pvar_map (ReifDeltaCostUpper n) = ReifDeltaCostUpper n"
| "primed_pvar_map (ReifDeltaCost n) = ReifDeltaCost n"
| "primed_pvar_map (ReifPrimedCostGe n) = ReifPrimedCostGe n"
| "primed_pvar_map (ReifCert x) = ReifCert (Primed x)"

(* Lift with primed_pvar_map: embeds the circuit into the primed ('v var) context.
   CostBit i is mapped to PrimedCostBit i so the primed circuit references the next cost. *)
definition primed_circuit :: "'v pb_circuit \<Rightarrow> 'v var pb_circuit" where
  "primed_circuit C \<equiv> lift_circuit primed_pvar_map C"


(* Cost constraint: \<Sigma> 2^i \<sqdot> CostBit i \<ge> B *)
definition cost_ge_constraint :: "nat \<Rightarrow> 'v pconstraint" where
  "cost_ge_constraint B \<equiv>
    (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed B], B)"

lemma pb_sum_cost_bits:
  "pb_sum (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<k]) (state_rho \<Pi> s c) = c mod 2^k"
proof (induct k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have "pb_sum (map (\<lambda>i. (2^i, Pos (CostBit i))) ([0..<k] @ [k])) (state_rho \<Pi> s c)
    = pb_sum (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<k]) (state_rho \<Pi> s c)
      + pb_sum [(2^k, Pos (CostBit k))] (state_rho \<Pi> s c)"
    by (simp add: pb_sum_append)
  also have "... = c mod 2^k + 2^k * ((c div 2^k) mod 2)"
    using Suc by (simp add: eval_lit_def state_rho_def)
  also have "... = c mod 2^(Suc k)"
    by (metis add.commute mod_mult2_eq mult.commute power_Suc)
  finally show ?case by simp
qed

subsection \<open>Encoding Soundness Lemmas\<close>

lemma pb_sum_state_lits_aux:
  assumes "distinct xs"
  shows "pb_sum (map (\<lambda>v. (1, Pos (StateVar v))) xs) (state_rho \<Pi> s c) = card (set xs \<inter> s)"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then have "a \<notin> set xs" and "distinct xs" by auto
  have "pb_sum (map (\<lambda>v. (1, Pos (StateVar v))) (a # xs)) (state_rho \<Pi> s c)
    = 1 * eval_lit (Pos (StateVar a)) (state_rho \<Pi> s c)
      + pb_sum (map (\<lambda>v. (1, Pos (StateVar v))) xs) (state_rho \<Pi> s c)"
    by simp
  also have "eval_lit (Pos (StateVar a)) (state_rho \<Pi> s c) = (if a \<in> s then 1 else 0)"
    by (simp add: eval_lit_def state_rho_def)
  also have "pb_sum (map (\<lambda>v. (1, Pos (StateVar v))) xs) (state_rho \<Pi> s c) = card (set xs \<inter> s)"
    using Cons by simp
  also have "1 * (if a \<in> s then 1 else 0) + card (set xs \<inter> s) = card (set (a # xs) \<inter> s)"
    using \<open>a \<notin> set xs\<close> by (auto simp: card_insert_if)
  finally show ?case .
qed

lemma pb_sum_state_lits:
  fixes S :: "'v::linorder set"
  assumes "finite S"
  shows "pb_sum (state_lits S) (state_rho \<Pi> s c) = card (S \<inter> s)"
proof -
  have "distinct (sorted_list_of_set S)" by simp
  then have "pb_sum (map (\<lambda>v. (1, Pos (StateVar v))) (sorted_list_of_set S)) (state_rho \<Pi> s c)
    = card (set (sorted_list_of_set S) \<inter> s)"
    by (rule pb_sum_state_lits_aux)
  also have "set (sorted_list_of_set S) = S" using assms by simp
  finally show ?thesis unfolding state_lits_def by simp
qed

lemma pb_sum_neg_state_lits_aux:
  assumes "distinct xs"
  shows "pb_sum (map (\<lambda>v. (1, Neg (StateVar v))) xs) (state_rho \<Pi> s c) = card (set xs - s)"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "pb_sum (map (\<lambda>v. (1, Neg (StateVar v))) (a # xs)) (state_rho \<Pi> s c)
    = (if a \<in> s then 0 else 1) + pb_sum (map (\<lambda>v. (1, Neg (StateVar v))) xs) (state_rho \<Pi> s c)"
    by (simp add: eval_lit_def state_rho_def)
  also have "... = (if a \<in> s then 0 else 1) + card (set xs - s)"
    using Cons by simp
  also have "... = card (set (a # xs) - s)"
  proof (cases "a \<in> s")
    case True
    then show ?thesis by simp
  next
    case False
    then have notin_s: "a \<notin> s" by simp
    have "set (a # xs) - s = insert a (set xs - s)" using notin_s by auto
    then show ?thesis using Cons notin_s by (simp add: card_insert_if)
  qed
  finally show ?case .
qed

lemma pb_sum_neg_state_lits:
  fixes S :: "'v::linorder set"
  assumes "finite S"
  shows "pb_sum (neg_state_lits S) (state_rho \<Pi> s c) = card (S - s)"
proof -
  have "distinct (sorted_list_of_set S)" by simp
  then have "pb_sum (map (\<lambda>v. (1, Neg (StateVar v))) (sorted_list_of_set S)) (state_rho \<Pi> s c)
    = card (set (sorted_list_of_set S) - s)"
    by (rule pb_sum_neg_state_lits_aux)
  also have "set (sorted_list_of_set S) = S" using assms by simp
  finally show ?thesis unfolding neg_state_lits_def by simp
qed

lemma init_encoding_sound:
  fixes \<Pi> :: "'v::linorder strips_task"
  assumes "finite (vars \<Pi>)" "init \<Pi> \<subseteq> vars \<Pi>"
  shows "models (encode_init \<Pi>) (state_rho \<Pi> (init \<Pi>) 0)"
proof -
  let ?r = "Pos ReifI"
  let ?I = "init \<Pi>"
  let ?V = "vars \<Pi>"
  let ?coeffs = "state_lits ?I @ neg_state_lits (?V - ?I)"
  let ?A = "card ?V"
  have reifI_val: "eval_lit ?r (state_rho \<Pi> ?I 0) = 1"
    by (simp add: eval_lit_def state_rho_def)
  have sum_eq: "pb_sum ?coeffs (state_rho \<Pi> ?I 0) = ?A"
  proof -
    have "pb_sum (state_lits ?I) (state_rho \<Pi> ?I 0) = card (?I \<inter> ?I)"
      using assms(1) pb_sum_state_lits by (metis assms(2) rev_finite_subset)
    also have "?I \<inter> ?I = ?I" by simp
    finally have sum1: "pb_sum (state_lits ?I) (state_rho \<Pi> ?I 0) = card ?I" .
    have "pb_sum (neg_state_lits (?V - ?I)) (state_rho \<Pi> ?I 0) = card ((?V - ?I) - ?I)"
      using assms(1) pb_sum_neg_state_lits by blast
    also have "(?V - ?I) - ?I = ?V - ?I" by blast
    finally have sum2: "pb_sum (neg_state_lits (?V - ?I)) (state_rho \<Pi> ?I 0) = card (?V - ?I)" .
    have card_eq: "card ?I + card (?V - ?I) = card ?V"
    proof -
      have finV: "finite ?V" using assms(1) by simp
      have subIV: "?I \<subseteq> ?V" using assms(2) by simp
      have finI: "finite ?I" using finV subIV finite_subset by blast
      have disj: "?I \<inter> (?V - ?I) = {}" by blast
      have "card ?I + card (?V - ?I) = card (?I \<union> (?V - ?I))"
        using finI finV by (metis card_Un_disjoint disj finite_Diff)
      also have "?I \<union> (?V - ?I) = ?V" using subIV by auto
      finally show ?thesis .
    qed
    show ?thesis
      using sum1 sum2 card_eq by (simp add: pb_sum_append)
  qed
  have fwd_sound: "satisfies (reif_fwd ?r ?coeffs ?A) (state_rho \<Pi> ?I 0)"
  proof -
    have "pb_sum (fst (reif_fwd ?r ?coeffs ?A)) (state_rho \<Pi> ?I 0)
      = ?A * eval_lit (lit_neg ?r) (state_rho \<Pi> ?I 0) + pb_sum ?coeffs (state_rho \<Pi> ?I 0)"
      by (simp add: reif_fwd_def)
    also have "eval_lit (lit_neg ?r) (state_rho \<Pi> ?I 0) = 0"
      using reifI_val by (simp add: eval_lit_def lit_neg_def)
    also have "pb_sum ?coeffs (state_rho \<Pi> ?I 0) = ?A" by (rule sum_eq)
    finally have "pb_sum (fst (reif_fwd ?r ?coeffs ?A)) (state_rho \<Pi> ?I 0) = ?A" by simp
    then show ?thesis by (simp add: satisfies_def reif_fwd_def)
  qed
  have bwd_sound: "satisfies (reif_bwd ?r ?coeffs ?A) (state_rho \<Pi> ?I 0)"
    using reifI_val by (simp add: satisfies_def reif_bwd_def Let_def le_add1)
  show ?thesis
    unfolding models_def encode_init_def reification_def
    by (simp add: fwd_sound bwd_sound Let_def)
qed

lemma goal_encoding_sound:
  fixes \<Pi> :: "'v::linorder strips_task"
  assumes "finite (vars \<Pi>)" "goal \<Pi> \<subseteq> vars \<Pi>" "is_goal_state \<Pi> s"
  shows "models (encode_goal \<Pi>) (state_rho \<Pi> s c)"
proof -
  let ?r = "Pos ReifG"
  let ?G = "goal \<Pi>"
  let ?coeffs = "state_lits ?G"
  let ?A = "card ?G"
  have finG: "finite ?G"
    using assms(1,2) by (blast intro: finite_subset)
  have reifG_val: "eval_lit ?r (state_rho \<Pi> s c) = 1"
    using assms(3) by (simp add: eval_lit_def state_rho_def)
  have sum_eq: "pb_sum ?coeffs (state_rho \<Pi> s c) = ?A"
  proof -
    have "pb_sum ?coeffs (state_rho \<Pi> s c) = card (?G \<inter> s)"
      using finG by (simp add: pb_sum_state_lits)
    also have "?G \<inter> s = ?G"
      using assms(3) unfolding is_goal_state_def by auto
    finally show ?thesis .
  qed
  have fwd_sound: "satisfies (reif_fwd ?r ?coeffs ?A) (state_rho \<Pi> s c)"
    using reifG_val sum_eq
    by (simp add: satisfies_def reif_fwd_def eval_lit_def lit_neg_def)
  have bwd_sound: "satisfies (reif_bwd ?r ?coeffs ?A) (state_rho \<Pi> s c)"
    using reifG_val by (simp add: satisfies_def reif_bwd_def Let_def le_add1)
  show ?thesis
    unfolding models_def encode_goal_def reification_def
    by (simp add: fwd_sound bwd_sound Let_def)
qed

lemma state_rho_range:
  "state_rho \<Pi> s c x \<le> 1"
  unfolding state_rho_def
  by (cases x; simp)

lemma state_rho_01:
  "state_rho \<Pi> s c x = 0 \<or> state_rho \<Pi> s c x = 1"
  unfolding state_rho_def
  by (cases x; simp add: mod_2_eq_odd)

lemma eval_lit_plus_lit_neg:
  "eval_lit l (state_rho \<Pi> s c) + eval_lit (lit_neg l) (state_rho \<Pi> s c) = 1"
  using state_rho_range[of \<Pi> s c]
  by (simp add: eval_lit_def lit_neg_def split: literal.splits)

lemma pb_sum_add_negated:
  "pb_sum coeffs (state_rho \<Pi> s c)
   + pb_sum (map (\<lambda>(a,l). (a, lit_neg l)) coeffs) (state_rho \<Pi> s c)
   = sum_list (map fst coeffs)"
proof (induction coeffs)
  case Nil
  then show ?case by simp
next
  case (Cons ac coeffs)
  then have IH: "pb_sum coeffs (state_rho \<Pi> s c) + pb_sum (map (\<lambda>(a,l). (a, lit_neg l)) coeffs) (state_rho \<Pi> s c) = sum_list (map fst coeffs)"
    by blast
  obtain x l where ac: "ac = (x, l)" by (cases ac)
  have split: "pb_sum (ac # coeffs) (state_rho \<Pi> s c) = x * eval_lit l (state_rho \<Pi> s c) + pb_sum coeffs (state_rho \<Pi> s c)"
    and split_neg: "pb_sum (map (\<lambda>(a,l). (a, lit_neg l)) (ac # coeffs)) (state_rho \<Pi> s c) = x * eval_lit (lit_neg l) (state_rho \<Pi> s c) + pb_sum (map (\<lambda>(a,l). (a, lit_neg l)) coeffs) (state_rho \<Pi> s c)"
    by (simp_all add: ac)
  show ?case
  proof -
    have factor: "x * eval_lit l (state_rho \<Pi> s c) + x * eval_lit (lit_neg l) (state_rho \<Pi> s c) = x"
      by (simp add: distrib_left[symmetric] eval_lit_plus_lit_neg)
    have "pb_sum (ac # coeffs) (state_rho \<Pi> s c) + pb_sum (map (\<lambda>(a,l). (a, lit_neg l)) (ac # coeffs)) (state_rho \<Pi> s c)
       = (x * eval_lit l (state_rho \<Pi> s c) + pb_sum coeffs (state_rho \<Pi> s c)) +
         (x * eval_lit (lit_neg l) (state_rho \<Pi> s c) + pb_sum (map (\<lambda>(a,l). (a, lit_neg l)) coeffs) (state_rho \<Pi> s c))"
      by (simp add: ac split split_neg)
    also have "... = pb_sum coeffs (state_rho \<Pi> s c) + pb_sum (map (\<lambda>(a,l). (a, lit_neg l)) coeffs) (state_rho \<Pi> s c) +
                     x * eval_lit l (state_rho \<Pi> s c) + x * eval_lit (lit_neg l) (state_rho \<Pi> s c)"
      by (simp add: add_ac)
    also have "... = sum_list (map fst coeffs) + x"
      using IH factor by (simp add: add_ac)
    also have "... = x + sum_list (map fst coeffs)"
      by (simp add: add_ac)
    also have "... = sum_list (map fst (ac # coeffs))"
      by (simp add: ac)
    finally show ?thesis .
  qed
qed

lemma sum_list_exp: "sum_list (map ((^) 2) [0..<B]) = (2 :: nat) ^ B - 1"
  by (induct B) auto


lemma cost_ge_encoding_sound:
  assumes "c \<ge> k" "c < 2^(bits_needed k)"
  shows "models (encode_cost_ge k) (state_rho \<Pi> s c)"
proof -
  let ?r = "Pos (ReifCostGe k)"
  let ?coeffs = "map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed k]"
  let ?A = k
  have reif_val: "eval_lit ?r (state_rho \<Pi> s c) = 1"
    using assms(1) by (simp add: eval_lit_def state_rho_def)
  have sum_eq: "pb_sum ?coeffs (state_rho \<Pi> s c) = c"
  proof -
    have "pb_sum ?coeffs (state_rho \<Pi> s c) = c mod 2^(bits_needed k)"
      by (rule pb_sum_cost_bits)
    also have "... = c"
      using assms(2) by simp
    finally show ?thesis .
  qed
  have fwd_sound: "satisfies (reif_fwd ?r ?coeffs ?A) (state_rho \<Pi> s c)"
    using reif_val sum_eq assms(1)
    by (simp add: satisfies_def reif_fwd_def eval_lit_def lit_neg_def)
  have bwd_sound: "satisfies (reif_bwd ?r ?coeffs ?A) (state_rho \<Pi> s c)"
    using reif_val by (simp add: satisfies_def reif_bwd_def Let_def le_add1)
  show ?thesis
    using fwd_sound bwd_sound
    unfolding models_def encode_cost_ge_def reification_def by simp
qed

lemma cost_ge_encoding_below:
  assumes "c < k"
  shows "models (encode_cost_ge k) (state_rho \<Pi> s c)"
proof -
  let ?r = "Pos (ReifCostGe k)"
  let ?coeffs = "map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed k]"
  have reif_val: "state_rho \<Pi> s c (ReifCostGe k) = 0"
    using assms by (simp add: state_rho_def)
  have eval_r: "eval_lit ?r (state_rho \<Pi> s c) = 0"
    by (simp add: eval_lit_def reif_val)
  have eval_neg_r: "eval_lit (lit_neg ?r) (state_rho \<Pi> s c) = 1"
    by (simp add: eval_lit_def lit_neg_def reif_val)
  have c_lt_pow: "c < 2^(bits_needed k)"
  proof -
    have "c < k" using assms .
    also have "k < 2^(bits_needed k)" by (rule bits_needed_sufficient)
    finally show ?thesis .
  qed
  have pow_pos: "k < (2::nat)^(bits_needed k)"
    using bits_needed_sufficient by metis
  have sum_eq: "pb_sum ?coeffs (state_rho \<Pi> s c) = c"
  proof -
    have "pb_sum ?coeffs (state_rho \<Pi> s c) = c mod 2^(bits_needed k)"
      by (rule pb_sum_cost_bits)
    thus ?thesis using c_lt_pow by simp
  qed
  have sum_total: "sum_list (map fst ?coeffs) = 2^(bits_needed k) - (1 :: nat)"
    by (simp add: sum_list_exp o_def)
  have neg_sum_eq: "pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) ?coeffs) (state_rho \<Pi> s c)
      = 2^(bits_needed k) - 1 - c"
  proof -
    have eq: "pb_sum ?coeffs (state_rho \<Pi> s c)
        + pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) ?coeffs) (state_rho \<Pi> s c)
        = sum_list (map fst ?coeffs)"
      by (metis (mono_tags, lifting) pb_sum_add_negated sum_total)
    thus ?thesis using sum_eq sum_total c_lt_pow
      by (metis (no_types, lifting) diff_add_inverse)
  qed
  have fwd_sound: "satisfies (reif_fwd ?r ?coeffs k) (state_rho \<Pi> s c)"
    unfolding satisfies_def reif_fwd_def Let_def
    using eval_neg_r sum_eq by simp
  have bwd_lhs: "pb_sum (fst (reif_bwd ?r ?coeffs k)) (state_rho \<Pi> s c)
      = 2^(bits_needed k) - 1 - c"
  proof -
    have thresh: "sum_list (map fst ?coeffs) - k + 1 = 2^(bits_needed k) - k"
      using sum_total pow_pos
      by (metis Suc_diff_Suc Suc_eq_plus1 diff_diff_left plus_1_eq_Suc)
    show ?thesis
      unfolding reif_bwd_def Let_def
      using eval_r neg_sum_eq by auto
  qed
  have bwd_thresh: "snd (reif_bwd ?r ?coeffs k) = 2^(bits_needed k) - k"
    unfolding reif_bwd_def Let_def using sum_total pow_pos
    by (metis One_nat_def Suc_eq_plus1 Suc_pred snd_conv zero_less_numeral zero_less_power)
  have ineq: "(2^(bits_needed k) - 1) - c \<ge> 2^(bits_needed k) - k"
  proof -
    have "c+1 \<le> k" using assms by simp
    then have "2^(bits_needed k) - k \<le> 2^(bits_needed k) - (c+1)" by (simp add: diff_le_mono2)
    also have "2^(bits_needed k) - (c+1) = (2^(bits_needed k) - 1) - c" by simp
    finally show ?thesis .
  qed  have bwd_sound: "satisfies (reif_bwd ?r ?coeffs k) (state_rho \<Pi> s c)"
    by (metis (mono_tags, lifting) bwd_lhs bwd_thresh ineq satisfies_def split_beta)
  show ?thesis
    using fwd_sound bwd_sound
    unfolding models_def encode_cost_ge_def reification_def by simp
qed

definition cost_circuit :: "nat \<Rightarrow> 'v pb_circuit" where
  "cost_circuit k \<equiv>
    let r = Pos (ReifCostGe k);
        coeffs = map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed k]
    in ([(r, coeffs, k)], r)"

lemma cost_circuit_complete:
  assumes "c \<ge> k" "c < 2^(bits_needed k)"
  shows "models_circuit (cost_circuit k) (state_rho \<Pi> s c)"
proof -
  let ?r = "Pos (ReifCostGe k)"
  let ?coeffs = "map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed k]"
  have out: "eval_lit ?r (state_rho \<Pi> s c) = 1"
    using assms(1) by (simp add: eval_lit_def state_rho_def)
  have sum_eq: "pb_sum ?coeffs (state_rho \<Pi> s c) = c"
    by (simp add: pb_sum_cost_bits assms(2))
  show ?thesis
    unfolding models_circuit_def cost_circuit_def Let_def
    using out sum_eq assms(1) by simp
qed

lemma cost_circuit_sound:
  assumes "models_circuit (cost_circuit k) (state_rho \<Pi> s c)"
  shows "c \<ge> k"
proof (cases "c < k")
  case True
  then have "eval_lit (Pos (ReifCostGe k)) (state_rho \<Pi> s c) = 0"
    by (simp add: eval_lit_def state_rho_def)
  with assms show ?thesis
    unfolding models_circuit_def cost_circuit_def Let_def by simp
next
  case False
  then show ?thesis by simp
qed

subsection \<open>Lower-Bound Certificates (Definition 3)\<close>

record ('v) certificate =
  cert_circuit :: "'v pb_circuit"
  cert_actions :: "'v action list"

subsection \<open>Paper Theorem 1 from CPR Certificates\<close>

(* The set of variables that are "reified" by a circuit — the label variables r_i.
   Defined over plain 'v (polymorphic). When applied to orig_circuit/primed_circuit
   this gives 'v var pvar set. *)
definition circuit_reif_pvars :: "'v pb_circuit \<Rightarrow> 'v pvar set" where
  "circuit_reif_pvars C \<equiv> pvar_of_lit ` fst ` set (fst C)"

(* The set of constraints in a circuit (right components of each pair).
   Defined over plain 'v (polymorphic). *)
definition circuit_constraints :: "'v pb_circuit \<Rightarrow> 'v pconstraint set" where
  "circuit_constraints C \<equiv> \<Union> (r, cs, A) \<in> set (fst C). reification r cs A"

(* Each reification variable appears at most once in the circuit.
   Needed for realizability: given any 0/1 input assignment, there exists
   a 0/1 assignment to all circuit variables satisfying the constraints. *)
definition distinct_reif_vars :: "'v pb_circuit \<Rightarrow> bool" where
  "distinct_reif_vars C \<equiv>
    let pairs = fst C
    in \<forall> i < length pairs. \<forall> j < length pairs. i \<noteq> j \<longrightarrow>
         pvar_of_lit (fst (pairs ! i)) \<noteq> pvar_of_lit (fst (pairs ! j))"

(* paper Definition 3 P_init: overline{cost >= 1}, i.e. constraint_neg applied to
   (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<B+1], 1) using the full B+1-bit cost encoding.
   Satisfied iff all cost bits are 0, i.e. cost = 0. *)
definition neg_cost_ge_one :: "nat \<Rightarrow> 'v pconstraint" where
  "neg_cost_ge_one B \<equiv>
    (map (\<lambda>i. (2^i, Neg (CostBit i))) [0..<bits_needed B], 2^(bits_needed B) - 1)"

(* Paper Definition 3: certificate validity via CPR proof objects.
   The circuit C_\<phi> is a plain 'v pb_circuit — it uses only unprimed variables \<V> \<union> \<V>_c.
   Primed variables only appear in P_ind (via encode_transition and primed_circuit).

   Three CPR conditions (matching paper Def 3):
   P_init: at plain 'v level — proves initial state is in M(C_\<phi>)
   P_goal: at plain 'v level — proves any state in M(C_\<phi>) satisfying goal has cost \<ge> B
   P_ind:  at 'v var level — proves M(C_\<phi>) is inductive under transitions
           (only here do primed variables v' appear) *)
definition certificate_valid_cpr ::
  "nat \<Rightarrow> 'v::linorder strips_task \<Rightarrow> ('v certificate) \<Rightarrow> bool" where
  "certificate_valid_cpr B \<Pi> Cert \<equiv>
    let C_\<phi> = cert_circuit Cert in
    finite (vars \<Pi>) \<and>
    init \<Pi> \<subseteq> vars \<Pi> \<and>
    goal \<Pi> \<subseteq> vars \<Pi> \<and>
    finite (acts \<Pi>) \<and>
    acts \<Pi> \<subseteq> set (cert_actions Cert) \<and>
    (\<forall> a \<in> set (cert_actions Cert).
        pre a \<subseteq> vars \<Pi> \<and> add a \<subseteq> vars \<Pi> \<and> del a \<subseteq> vars \<Pi>) \<and>
    wf_circuit C_\<phi> \<and>
    distinct_reif_vars C_\<phi> \<and>
    (\<forall>(r, \<phi>) \<in> set (fst C_\<phi>). \<forall>v \<in> constraint_pvars \<phi>. \<forall>i. v \<noteq> PrimedCostBit i) \<and>
    (\<forall> v \<in> circuit_reif_pvars C_\<phi>.
        \<not> is_input_pvar v \<and> v \<noteq> ReifI \<and> (\<forall>k. v \<noteq> ReifCostGe k) \<and> v \<noteq> ReifG \<and>
        (\<forall>k. v \<noteq> ReifDeltaCost k) \<and> (\<forall>k. v \<noteq> ReifDeltaCostLower k) \<and>
        (\<forall>k. v \<noteq> ReifDeltaCostUpper k) \<and>
        (\<forall>k. v \<noteq> ReifPrimedCostGe k) \<and> v \<noteq> ReifT \<and>
        (\<forall>u. v \<noteq> ReifGeq u) \<and> (\<forall>u. v \<noteq> ReifLeq u) \<and> (\<forall>u. v \<noteq> ReifEq u) \<and>
        (\<forall>i. v \<noteq> ReifAction i) \<and> (\<forall>i. v \<noteq> PrimedCostBit i)) \<and>
    cpr_derives
      (encode_init \<Pi> \<union> circuit_constraints C_\<phi> \<union> encode_cost_ge B \<union>
       {unit_clause (Pos ReifI), neg_cost_ge_one B})
      (unit_clause (snd C_\<phi>)) \<and>
    cpr_derives
      (encode_goal \<Pi> \<union> circuit_constraints C_\<phi> \<union> encode_cost_ge B \<union>
       {unit_clause (snd C_\<phi>), unit_clause (Pos ReifG)})
      (cost_ge_constraint B) \<and>
    cpr_derives
      (encode_transition (cert_actions Cert) (vars \<Pi>) B \<union>
       circuit_constraints (orig_circuit C_\<phi>) \<union>
       circuit_constraints (primed_circuit C_\<phi>) \<union>
       encode_cost_ge B \<union>
       {unit_clause (snd (orig_circuit C_\<phi>)), unit_clause (Pos ReifT)})
      (unit_clause (snd (primed_circuit C_\<phi>)))"

lemma map_pvar_Original_inj:
  "map_pvar Original x = map_pvar Original y \<longleftrightarrow> (x :: 'v pvar) = y"
  by (cases x; cases y; auto)

lemma map_literal_eq_Pos_conv: "map_literal f x = Pos y \<longleftrightarrow> (\<exists>z. x = Pos z \<and> f z = y)"
  by (cases x; auto)
lemma map_literal_eq_Neg_conv: "map_literal f x = Neg y \<longleftrightarrow> (\<exists>z. x = Neg z \<and> f z = y)"
  by (cases x; auto)
lemmas map_literal_convs = map_literal_eq_Pos_conv map_literal_eq_Neg_conv

lemma not_Pos_Neg: "(\<forall>x. b \<noteq> Pos x) \<longleftrightarrow> (\<exists>x. b = Neg x)"
  by (cases b; simp)

lemma wf_orig_circuit:
  assumes "wf_circuit (C :: 'v pb_circuit)"
  shows "wf_circuit (orig_circuit C)"
proof -
  obtain pairs out where C: "C = (pairs, out)" by (cases C)
  have F1: "\<forall>i < length pairs. \<forall>r cs A. pairs ! i = (r, cs, A) \<longrightarrow>
      pvar_of_lit ` snd ` set cs \<subseteq>
      Collect is_input_pvar \<union> pvar_of_lit ` fst ` set (take i pairs)"
    using assms unfolding wf_circuit_def C Let_def by (fastforce simp: image_iff split: prod.splits)
  have F2: "Pos (pvar_of_lit out) \<in> fst ` set pairs \<or> Neg (pvar_of_lit out) \<in> fst ` set pairs"
    using assms unfolding wf_circuit_def C Let_def by auto
  have pof: "\<forall>l :: 'v pvar literal. pvar_of_lit (map_literal (map_pvar Original) l) =
      map_pvar Original (pvar_of_lit l)"
    by (simp add: pvar_of_lit_def split: literal.splits)
  have cs_map: "\<forall>cs :: (nat \<times> 'v pvar literal) list.
      pvar_of_lit ` snd ` set (map (\<lambda>(a,l). (a, map_literal (map_pvar Original) l)) cs) =
      (map_pvar Original ` (pvar_of_lit ` snd ` set cs) :: 'v var pvar set)"
    by (force simp: pvar_of_lit_def image_iff map_literal_convs split: literal.splits)
  have inp: "\<forall>v :: 'v pvar. is_input_pvar v \<longrightarrow> is_input_pvar (map_pvar Original v)"
    by (auto simp: is_input_pvar_def split: pvar.splits)
  have tk: "\<forall>i. pvar_of_lit ` fst `
      set (take i (map (\<lambda>(r, cs, A). (map_literal (map_pvar Original) r,
            map (\<lambda>(a, l). (a, map_literal (map_pvar Original) l)) cs, A)) pairs)) =
      map_pvar Original ` (pvar_of_lit ` fst ` set (take i pairs))"
    by (induction pairs; auto simp: pof take_Cons' split: if_splits)
  let ?f = "map_pvar Original"
  let ?lp = "map (\<lambda>(r, cs, A). (map_literal ?f r,
            map (\<lambda>(a, l). (a, map_literal ?f l)) cs, A)) pairs"
  have wf1: "\<forall>i < length ?lp.
      let (r_i, cs_i, A_i) = ?lp ! i;
          allowed = Collect is_input_pvar \<union> pvar_of_lit ` fst ` set (take i ?lp)
      in pvar_of_lit ` snd ` set cs_i \<subseteq> allowed"
  proof (intro allI impI)
    fix i assume i_lt: "i < length ?lp"
    have i_lt': "i < length pairs" using i_lt by simp
    obtain r cs A where pair_i: "pairs ! i = (r, cs, A)"
      by (metis prod_cases3)
    have sub: "pvar_of_lit ` snd ` set cs \<subseteq>
          Collect is_input_pvar \<union> pvar_of_lit ` fst ` set (take i pairs)"
      using F1 i_lt' pair_i by auto
    have lp_i: "?lp ! i = (map_literal ?f r,
        map (\<lambda>(a, l). (a, map_literal ?f l)) cs, A)"
      by (simp add: pair_i i_lt')
    have cs_eq: "pvar_of_lit ` snd ` set (map (\<lambda>(a, l). (a, map_literal ?f l)) cs) =
        map_pvar Original ` (pvar_of_lit ` snd ` set cs)"
      using cs_map by auto
    have rhs: "pvar_of_lit ` fst ` set (take i ?lp) =
          map_pvar Original ` (pvar_of_lit ` fst ` set (take i pairs))"
      using tk by simp
    show "let (r_i, cs_i, A_i) = ?lp ! i;
          allowed = Collect is_input_pvar \<union> pvar_of_lit ` fst ` set (take i ?lp)
      in pvar_of_lit ` snd ` set cs_i \<subseteq> allowed"
      unfolding Let_def lp_i fst_conv snd_conv cs_eq rhs
      using sub inp pof by (force simp: image_iff map_pvar_Original_inj)
  qed
  show ?thesis
    unfolding wf_circuit_def orig_circuit_def lift_circuit_def C Let_def prod.case
  proof (intro conjI allI impI, goal_cases)
    case (1 i)
    then show ?case using wf1 by (simp add: split_beta Let_def)
  next
    case 2
    then show ?case using F2 by (force simp: pvar_of_lit_def split: prod.splits literal.splits)
  qed
qed

(* A state-cost pair (s,c) is in the semantic invariant M(C) iff
   there exists a plain 'v model of circuit_constraints C that:
   (a) satisfies the circuit constraints,
   (b) makes the output literal evaluate to 1,
   (c) encodes state s and cost c correctly on all input variables.
   Everything stays at the plain 'v pvar level — no primed variables. *)
definition in_M :: "'v::linorder pb_circuit \<Rightarrow> 'v strips_task \<Rightarrow> 'v state \<Rightarrow> nat \<Rightarrow> bool" where
  "in_M C \<Pi> s c \<equiv>
    \<exists> rho. (\<forall> v. rho v = 0 \<or> rho v = 1)
      \<and> models (circuit_constraints C) rho
      \<and> eval_lit (snd C) rho = 1
      \<and> (\<forall> v. rho (StateVar v) = (if v \<in> s then 1 else 0))
      \<and> (\<forall> i. rho (CostBit i) = (c div 2^i) mod 2)
      \<and> (\<forall> i. rho (PrimedCostBit i) = 0)"

lemma state_rho_StateVar_eq:
  "state_rho \<Pi> s c (StateVar v) = (if v \<in> s then 1 else 0)"
  by (simp add: state_rho_def)

lemma state_rho_CostBit_eq:
  "state_rho \<Pi> s c (CostBit i) = (c div 2^i) mod 2"
  by (simp add: state_rho_def)

definition extend_rho :: "'v pb_circuit \<Rightarrow> ('v pvar \<Rightarrow> nat) \<Rightarrow> ('v pvar \<Rightarrow> nat) \<Rightarrow> ('v pvar \<Rightarrow> nat)" where
  "extend_rho C rho_circ rho_base \<equiv> \<lambda> x.
    if x \<in> circuit_reif_pvars C then rho_circ x else rho_base x"

lemma extend_rho_base_on_non_reif:
  assumes "x \<notin> circuit_reif_pvars C"
  shows "extend_rho C rho_circ rho_base x = rho_base x"
  unfolding extend_rho_def using assms by simp

lemma pb_sum_congr:
  assumes "\<forall> (a, l) \<in> set coeffs. eval_lit l f = eval_lit l g"
  shows "pb_sum coeffs f = pb_sum coeffs g"
  using assms
proof (induction coeffs)
  case Nil then show ?case by simp
next
  case (Cons p cs)
  obtain a l where pl: "p = (a, l)" by (cases p)
  with Cons have head: "eval_lit l f = eval_lit l g" by auto
  from Cons pl have "pb_sum cs f = pb_sum cs g" by auto
  with head pl show ?case by simp
qed

lemma pb_sum_add_negated_gen:
  assumes "\<forall> v. rho v = 0 \<or> rho v = 1"
  shows "pb_sum coeffs rho + pb_sum (map (\<lambda>(a,l). (a, lit_neg l)) coeffs) rho
         = sum_list (map fst coeffs)"
proof (induction coeffs)
  case Nil then show ?case by simp
next
  case (Cons ac cs)
  obtain x l where ac: "ac = (x, l)" by (cases ac)
  have step: "x * eval_lit l rho + x * eval_lit (lit_neg l) rho = x"
  proof (cases l)
    case (Pos v)
    have "rho v = 0 \<or> rho v = 1" using assms by simp
    then show ?thesis by (auto simp: Pos eval_lit_def lit_neg_def)
  next
    case (Neg v)
    have "rho v = 0 \<or> rho v = 1" using assms by simp
    then show ?thesis by (auto simp: Neg eval_lit_def lit_neg_def)
  qed
  show ?case using Cons.IH ac step by simp
qed

lemma pb_sum_extend_rho_eq_base:
  assumes "\<forall> (a, l) \<in> set coeffs. pvar_of_lit l \<notin> circuit_reif_pvars C"
  shows "pb_sum coeffs (extend_rho C rho_circ rho_base) = pb_sum coeffs rho_base"
  using assms
proof (induction coeffs)
  case Nil then show ?case by simp
next
  case (Cons p coeffs)
  obtain a l where "p = (a, l)" by (cases p)
  with Cons have "pvar_of_lit l \<notin> circuit_reif_pvars C" by auto
  then have "eval_lit l (extend_rho C rho_circ rho_base) = eval_lit l rho_base"
    by (cases l; simp add: eval_lit_def extend_rho_def pvar_of_lit_def)
  with Cons show ?case by (simp add: \<open>p = (a, l)\<close>)
qed

lemma satisfies_extend_rho_eq_base:
  assumes "\<forall> v \<in> constraint_pvars \<phi>. v \<notin> circuit_reif_pvars C"
  shows "satisfies \<phi> (extend_rho C rho_circ rho_base) = satisfies \<phi> rho_base"
proof -
  obtain coeffs A where "\<phi> = (coeffs, A)" by (cases \<phi>)
  with assms have "\<forall> (a, l) \<in> set coeffs. pvar_of_lit l \<notin> circuit_reif_pvars C"
    unfolding constraint_pvars_def by fastforce
  then show ?thesis
    unfolding \<open>\<phi> = (coeffs, A)\<close> satisfies_def
    by (simp add: pb_sum_extend_rho_eq_base)
qed

lemma models_circuit_constraints_extend:
  assumes "models (circuit_constraints C) rho_circ"
    and "\<forall> (r, \<phi>) \<in> set (fst C). \<forall> v \<in> constraint_pvars \<phi>. is_input_pvar v \<or> v \<in> circuit_reif_pvars C"
    and "\<forall> v. is_input_pvar v \<longrightarrow> rho_base v = rho_circ v"
  shows "models (circuit_constraints C) (extend_rho C rho_circ rho_base)"
proof (unfold models_def, intro ballI)
  fix \<phi> assume "\<phi> \<in> circuit_constraints C"
  then obtain r cs A where r\<phi>: "(r, cs, A) \<in> set (fst C)"
    and \<phi>_reif: "\<phi> \<in> reification r cs A"
    unfolding circuit_constraints_def by blast
  have cpvars: "\<forall> v \<in> constraint_pvars \<phi>. is_input_pvar v \<or> v \<in> circuit_reif_pvars C"
  proof (intro ballI)
    fix v assume vin: "v \<in> constraint_pvars \<phi>"
    have sub: "constraint_pvars \<phi> \<subseteq> {pvar_of_lit r} \<union> pvar_of_lit ` snd ` set cs"
      using \<phi>_reif
      unfolding reification_def reif_fwd_def reif_bwd_def constraint_pvars_def
      by (force simp: pvar_of_lit_def lit_neg_def Let_def split: if_splits literal.splits)
    then consider "v = pvar_of_lit r" | "v \<in> pvar_of_lit ` snd ` set cs"
      using vin by blast
    then show "is_input_pvar v \<or> v \<in> circuit_reif_pvars C"
    proof cases
      case 1
      have "pvar_of_lit r \<in> circuit_reif_pvars C"
        using r\<phi> unfolding circuit_reif_pvars_def by (force simp: image_iff)
      with 1 show ?thesis by blast
    next
      case 2
      have "\<forall> v \<in> pvar_of_lit ` snd ` set cs. is_input_pvar v \<or> v \<in> circuit_reif_pvars C"
        using assms(2) r\<phi> unfolding constraint_pvars_def by (fastforce split: prod.splits)
      with 2 show ?thesis by blast
    qed
  qed
  have sat_circ: "satisfies \<phi> rho_circ"
    using assms(1) \<open>\<phi> \<in> circuit_constraints C\<close> unfolding models_def by blast
  have coeffs_eq: "\<forall> (a, l) \<in> set (fst \<phi>). eval_lit l (extend_rho C rho_circ rho_base) = eval_lit l rho_circ"
  proof (safe)
    fix a l assume al: "(a, l) \<in> set (fst \<phi>)"
    have "pvar_of_lit l \<in> constraint_pvars \<phi>"
      unfolding constraint_pvars_def using al by force
    with cpvars have "is_input_pvar (pvar_of_lit l) \<or> pvar_of_lit l \<in> circuit_reif_pvars C" by auto
    then show "eval_lit l (extend_rho C rho_circ rho_base) = eval_lit l rho_circ"
      using assms(3)
      by (cases l; auto simp add: eval_lit_def extend_rho_def circuit_reif_pvars_def pvar_of_lit_def)
  qed
  have sum_eq: "pb_sum (fst \<phi>) (extend_rho C rho_circ rho_base) = pb_sum (fst \<phi>) rho_circ"
    using coeffs_eq by (rule pb_sum_congr)
  with sat_circ show "satisfies \<phi> (extend_rho C rho_circ rho_base)"
    unfolding satisfies_def by (cases \<phi>) simp
qed

lemma eval_output_extend_rho:
  assumes "pvar_of_lit (snd C) \<in> circuit_reif_pvars C"
  shows "eval_lit (snd C) (extend_rho C rho_circ rho_base) = eval_lit (snd C) rho_circ"
  proof -
  have "pvar_of_lit (snd C) \<in> circuit_reif_pvars C" using assms .
  then show ?thesis
    by (cases "snd C"; simp add: eval_lit_def extend_rho_def circuit_reif_pvars_def pvar_of_lit_def)
qed

lemma pb_sum_neg_cost_bits_zero:
  assumes "\<forall> i < k. rho (CostBit i) = 0"
  shows "pb_sum (map (\<lambda>i. (2^i, Neg (CostBit i))) [0..<k]) rho = 2^k - 1"
  using assms
  by (induction k) (auto simp: pb_sum_append eval_lit_def)

lemma satisfies_neg_cost_ge_one:
  assumes "\<forall> i. rho (CostBit i) = 0"
  shows "satisfies (neg_cost_ge_one B) rho"
  unfolding neg_cost_ge_one_def satisfies_def
  using pb_sum_neg_cost_bits_zero[of "bits_needed B" rho] assms by simp

lemma in_M_init:
  fixes \<Pi> :: "'v::linorder strips_task" and C_\<phi> :: "'v pb_circuit"
  assumes fin: "finite (vars \<Pi>)" and init_sub: "init \<Pi> \<subseteq> vars \<Pi>"
    and wf: "wf_circuit C_\<phi>"
    and out_reif: "pvar_of_lit (snd C_\<phi>) \<in> circuit_reif_pvars C_\<phi>"
    and circ_vars: "\<forall> (r, \<phi>) \<in> set (fst C_\<phi>).
        \<forall> v \<in> constraint_pvars \<phi>. is_input_pvar v \<or> v \<in> circuit_reif_pvars C_\<phi>"
    and disjoint: "\<forall> v \<in> circuit_reif_pvars C_\<phi>.
        \<not> is_input_pvar v \<and> v \<noteq> ReifI \<and> (\<forall> k. v \<noteq> ReifCostGe k)"
    and realiz: "\<forall> base. (\<forall> v. base v = 0 \<or> base v = 1) \<longrightarrow> (\<exists> rho.
        models (circuit_constraints C_\<phi>) rho
        \<and> (\<forall> v. is_input_pvar v \<longrightarrow> rho v = base v)
        \<and> (\<forall> v. rho v = 0 \<or> rho v = 1))"
    and B_pos: "B \<ge> 1"
    and cpr_init: "cpr_derives
      (encode_init \<Pi> \<union> circuit_constraints C_\<phi> \<union> encode_cost_ge B \<union>
       {unit_clause (Pos ReifI), neg_cost_ge_one B})
      (unit_clause (snd C_\<phi>))"
  shows "in_M C_\<phi> \<Pi> (init \<Pi>) 0"
proof -
  let ?s = "init \<Pi>"
  let ?base = "state_rho \<Pi> ?s 0"
  have base_01: "\<forall> v. ?base v = 0 \<or> ?base v = 1" using state_rho_01 by blast
  obtain rho_circ where
    circ_sat: "models (circuit_constraints C_\<phi>) rho_circ"
    and inp_eq: "\<forall> v. is_input_pvar v \<longrightarrow> rho_circ v = ?base v"
    and circ_01: "\<forall> v. rho_circ v = 0 \<or> rho_circ v = 1"
    using realiz base_01 by blast
  let ?rho = "extend_rho C_\<phi> rho_circ ?base"
  have inp_sym: "\<forall> v. is_input_pvar v \<longrightarrow> ?base v = rho_circ v"
    using inp_eq by auto
  have rho_circ_sat: "models (circuit_constraints C_\<phi>) ?rho"
    using models_circuit_constraints_extend[OF circ_sat circ_vars inp_sym] .
  have sv_rho: "\<forall> v. ?rho (StateVar v) = (if v \<in> ?s then 1 else 0)"
  proof
    fix v
    show "?rho (StateVar v) = (if v \<in> ?s then 1 else 0)"
    proof (cases "StateVar v \<in> circuit_reif_pvars C_\<phi>")
      case True
      then have "?rho (StateVar v) = rho_circ (StateVar v)"
        by (simp add: extend_rho_def)
      also have "... = ?base (StateVar v)"
        using inp_eq[rule_format, of "StateVar v"] unfolding is_input_pvar_def by auto
      also have "... = (if v \<in> ?s then 1 else 0)"
        by (simp add: state_rho_def)
      finally show ?thesis .
    next
      case False
      then have "?rho (StateVar v) = ?base (StateVar v)"
        by (simp add: extend_rho_base_on_non_reif)
      also have "... = (if v \<in> ?s then 1 else 0)"
        by (simp add: state_rho_def)
      finally show ?thesis .
    qed
  qed
  have cb_rho: "\<forall> i. ?rho (CostBit i) = (0 div 2^i) mod 2"
  proof
    fix i
    show "?rho (CostBit i) = (0 div 2^i) mod 2"
    proof (cases "CostBit i \<in> circuit_reif_pvars C_\<phi>")
      case True
      then have "?rho (CostBit i) = rho_circ (CostBit i)"
        by (simp add: extend_rho_def)
      also have "... = ?base (CostBit i)"
        using inp_eq[rule_format, of "CostBit i"] unfolding is_input_pvar_def by auto
      also have "... = (0 div 2^i) mod 2"
        by (simp add: state_rho_def)
      finally show ?thesis .
    next
      case False
      then have "?rho (CostBit i) = ?base (CostBit i)"
        by (simp add: extend_rho_base_on_non_reif)
      also have "... = (0 div 2^i) mod 2"
        by (simp add: state_rho_def)
      finally show ?thesis .
    qed
  qed
  have primed_cb_rho: "\<forall> i. ?rho (PrimedCostBit i) = (0 div 2^i) mod 2"
  proof
    fix i
    show "?rho (PrimedCostBit i) = (0 div 2^i) mod 2"
    proof (cases "PrimedCostBit i \<in> circuit_reif_pvars C_\<phi>")
      case True
      then have "?rho (PrimedCostBit i) = rho_circ (PrimedCostBit i)"
        by (simp add: extend_rho_def)
      also have "... = ?base (PrimedCostBit i)"
        using inp_eq[rule_format, of "PrimedCostBit i"] unfolding is_input_pvar_def by auto
      also have "... = (0 div 2^i) mod 2"
        by (simp add: state_rho_def)
      finally show ?thesis .
    next
      case False
      then have "?rho (PrimedCostBit i) = ?base (PrimedCostBit i)"
        by (simp add: extend_rho_base_on_non_reif)
      also have "... = (0 div 2^i) mod 2"
        by (simp add: state_rho_def)
      finally show ?thesis .
    qed
  qed
  have enc_init_sat: "models (encode_init \<Pi>) ?rho"
  proof (unfold models_def, intro ballI)
    fix \<phi> assume \<phi>_in: "\<phi> \<in> encode_init \<Pi>"
    have base_sat: "satisfies \<phi> ?base"
      using init_encoding_sound[OF fin init_sub] \<phi>_in unfolding models_def by auto
    have not_reif: "\<forall> v \<in> constraint_pvars \<phi>. v \<notin> circuit_reif_pvars C_\<phi>"
    proof
      fix v assume "v \<in> constraint_pvars \<phi>"
      with \<phi>_in have "v = ReifI \<or> (\<exists>u. v = StateVar u)"
        unfolding encode_init_def reification_def constraint_pvars_def
                  reif_fwd_def reif_bwd_def state_lits_def neg_state_lits_def pvar_of_lit_def
        by (auto split: literal.splits simp: lit_neg_def Let_def)
      then show "v \<notin> circuit_reif_pvars C_\<phi>"
        using disjoint unfolding is_input_pvar_def by auto
    qed
    from satisfies_extend_rho_eq_base[OF not_reif] base_sat
    show "satisfies \<phi> ?rho" by simp
  qed
  have base_cost_sat: "models (encode_cost_ge B :: 'v pconstraint set) ?base"
    by (rule cost_ge_encoding_below) (use B_pos in simp)
  have enc_cost_sat: "models (encode_cost_ge B :: 'v pconstraint set) ?rho"
  proof (unfold models_def, intro ballI)
    fix \<phi> :: "'v pconstraint" assume \<phi>_in: "\<phi> \<in> (encode_cost_ge B :: 'v pconstraint set)"
    have base_sat: "satisfies \<phi> ?base"
      using base_cost_sat \<phi>_in unfolding models_def by auto
    have not_reif: "\<forall> v \<in> constraint_pvars \<phi>. v \<notin> circuit_reif_pvars C_\<phi>"
    proof
      fix v assume "v \<in> constraint_pvars \<phi>"
      with \<phi>_in have "v = ReifCostGe B \<or> (\<exists>i. v = CostBit i)"
        unfolding encode_cost_ge_def reification_def constraint_pvars_def
                  reif_fwd_def reif_bwd_def pvar_of_lit_def
        by (auto split: literal.splits simp: lit_neg_def Let_def)
      then show "v \<notin> circuit_reif_pvars C_\<phi>"
        using disjoint unfolding is_input_pvar_def by auto
    qed
    from satisfies_extend_rho_eq_base[OF not_reif] base_sat
    show "satisfies \<phi> ?rho" by simp
  qed
  have reifI_rho: "?rho ReifI = 1"
  proof -
    have "ReifI \<notin> circuit_reif_pvars C_\<phi>" using disjoint by auto
    then have "?rho ReifI = ?base ReifI" by (simp add: extend_rho_base_on_non_reif)
    then show ?thesis by (simp add: state_rho_def)
  qed
  have axiom_rho: "models {unit_clause (Pos ReifI), neg_cost_ge_one B} ?rho"
  proof -
    have sat1: "satisfies (unit_clause (Pos ReifI)) ?rho"
      unfolding satisfies_def unit_clause_def
      by (simp add: eval_lit_def reifI_rho)
    have sat2: "satisfies (neg_cost_ge_one B) ?rho"
      by (rule satisfies_neg_cost_ge_one) (simp add: cb_rho)
    show ?thesis using sat1 sat2 by (simp add: models_def)
  qed
  have hyp_model: "\<forall> \<phi> \<in> encode_init \<Pi> \<union> circuit_constraints C_\<phi> \<union> encode_cost_ge B \<union>
      {unit_clause (Pos ReifI), neg_cost_ge_one B}. satisfies \<phi> ?rho"
    using enc_init_sat rho_circ_sat enc_cost_sat axiom_rho
    unfolding models_def circuit_constraints_def by auto
  have output_sat: "satisfies (unit_clause (snd C_\<phi>)) ?rho"
    using cpr_sound[OF cpr_init] hyp_model
    using models_def by (metis (no_types, lifting) base_01 circ_01 extend_rho_def)
  have rho_01: "\<forall> v. ?rho v = 0 \<or> ?rho v = 1"
      unfolding extend_rho_def
      using circ_01 by (auto simp: state_rho_def is_input_pvar_def split: pvar.splits var.splits) 
  have output_eval: "eval_lit (snd C_\<phi>) ?rho = 1"
    using output_sat unfolding satisfies_def unit_clause_def
  proof (cases "snd C_\<phi>")
    case (Pos x1)
    have h01: "?rho x1 = 0 \<or> ?rho x1 = 1" using rho_01 by blast
    moreover have hge: "1 \<le> ?rho x1"
      using output_sat unfolding satisfies_def unit_clause_def
      by (simp add: Pos eval_lit_def)
    ultimately show ?thesis by (simp add: Pos eval_lit_def)
  next
    case (Neg x2)
    have h01: "?rho x2 = 0 \<or> ?rho x2 = 1" using rho_01 by blast
    moreover have hge: "1 \<le> 1 - ?rho x2"
      using output_sat unfolding satisfies_def unit_clause_def
      by (simp add: Neg eval_lit_def)
    ultimately show ?thesis by (simp add: Neg eval_lit_def)
  qed
  show ?thesis
    unfolding in_M_def
    using rho_circ_sat output_eval sv_rho cb_rho primed_cb_rho rho_01 by auto
qed

lemma wf_circuit_out_reif:
  assumes "wf_circuit (C :: 'v pb_circuit)"
  shows "pvar_of_lit (snd C) \<in> circuit_reif_pvars C"
proof -
  obtain pairs out where C: "C = (pairs, out)" by (cases C)
  with assms have "Pos (pvar_of_lit out) \<in> fst ` set pairs \<or> Neg (pvar_of_lit out) \<in> fst ` set pairs"
    unfolding wf_circuit_def by auto
  then obtain r \<phi> where "(r, \<phi>) \<in> set pairs" and "r = Pos (pvar_of_lit out) \<or> r = Neg (pvar_of_lit out)"
    by (force simp: image_iff)
  then have "pvar_of_lit out = pvar_of_lit r"
    by (auto simp: pvar_of_lit_def)
  with \<open>(r, \<phi>) \<in> set pairs\<close> show ?thesis
    unfolding circuit_reif_pvars_def C
    by (force simp: image_iff)
qed

lemma satisfies_cong:
  assumes "\<forall> v \<in> constraint_pvars \<phi>. rho1 v = rho2 v"
  shows "satisfies \<phi> rho1 = satisfies \<phi> rho2"
proof (cases \<phi>)
  case (Pair coeffs A)
  have "\<forall> (a, l) \<in> set coeffs. eval_lit l rho1 = eval_lit l rho2"
  proof (safe)
    fix a l assume "(a, l) \<in> set coeffs"
    then have "pvar_of_lit l \<in> constraint_pvars \<phi>"
      unfolding Pair constraint_pvars_def by force
    with assms have "rho1 (pvar_of_lit l) = rho2 (pvar_of_lit l)" by auto
    then show "eval_lit l rho1 = eval_lit l rho2"      by (cases l; simp add: eval_lit_def pvar_of_lit_def)
  qed
  then show ?thesis
    unfolding Pair satisfies_def
    by (auto simp: pb_sum_congr)
qed

lemma pvar_of_lit_lit_neg: "pvar_of_lit (lit_neg l) = pvar_of_lit l"
  by (simp add: lit_neg_def pvar_of_lit_def split: literal.splits)

lemma wf_circuit_realizability:
  fixes C :: "'v pb_circuit"
  assumes wf: "wf_circuit C"
    and distinct: "distinct_reif_vars C"
    and reif_not_input: "\<forall> v \<in> circuit_reif_pvars C. \<not> is_input_pvar v"
  shows "\<forall> (base :: 'v pvar \<Rightarrow> nat). (\<forall> v. base v = 0 \<or> base v = 1) \<longrightarrow>
    (\<exists> rho.
      models (circuit_constraints C) rho
      \<and> (\<forall> v. is_input_pvar v \<longrightarrow> rho v = base v)
      \<and> (\<forall> v. rho v = 0 \<or> rho v = 1))"
proof (intro allI impI)
  fix base :: "'v pvar \<Rightarrow> nat"
  assume base_01: "\<forall> v. base v = 0 \<or> base v = 1"
  obtain pairs out where C: "C = (pairs, out)" by (cases C)
  have wf_conj: "wf_circuit C \<and> distinct_reif_vars C" using wf distinct ..
  have wf_deps: "\<forall>i < length pairs.
    pvar_of_lit ` snd ` set (fst (snd (pairs ! i)))
    \<subseteq> {x. is_input_pvar x} \<union> (pvar_of_lit ` fst ` set (take i pairs))"
    using wf unfolding wf_circuit_def C Let_def by (auto simp: split_beta)
  have distinct': "\<forall>i < length pairs. \<forall>j < length pairs. i \<noteq> j \<longrightarrow>
    pvar_of_lit (fst (pairs ! i)) \<noteq> pvar_of_lit (fst (pairs ! j))"
    using distinct unfolding distinct_reif_vars_def C Let_def by auto
  have reif_not_input':
    "\<forall>i < length pairs. \<not> is_input_pvar (pvar_of_lit (fst (pairs ! i)))"
  proof (intro allI impI)
    fix i
    assume "i < length pairs"
    then have mem: "pvar_of_lit (fst (pairs ! i)) \<in> circuit_reif_pvars C"
      unfolding circuit_reif_pvars_def C
      by (metis fst_conv image_eqI nth_mem)
    then show "\<not> is_input_pvar (pvar_of_lit (fst (pairs ! i)))"
      using reif_not_input by meson
  qed
  have "\<forall>k \<le> length pairs. \<exists>rho. (\<forall>v. rho v = 0 \<or> rho v = 1) \<and>
    (\<forall>v. is_input_pvar v \<longrightarrow> rho v = base v) \<and>
    (\<forall>j < k. \<forall>\<phi> \<in> reification (fst (pairs ! j)) (fst (snd (pairs ! j))) (snd (snd (pairs ! j))). satisfies \<phi> rho)"
  proof (intro allI impI)
    fix k
    assume "k \<le> length pairs"
    then show "\<exists>rho. (\<forall>v. rho v = 0 \<or> rho v = 1) \<and>
      (\<forall>v. is_input_pvar v \<longrightarrow> rho v = base v) \<and>
      (\<forall>j < k. \<forall>\<phi> \<in> reification (fst (pairs ! j)) (fst (snd (pairs ! j))) (snd (snd (pairs ! j))). satisfies \<phi> rho)"
    proof (induction k)
      case 0
      let ?rho = "\<lambda>v. if is_input_pvar v then base v else 0"
      have "\<forall>v. ?rho v = 0 \<or> ?rho v = 1" using base_01 by (simp split: if_splits)
      moreover have "\<forall>v. is_input_pvar v \<longrightarrow> ?rho v = base v" by simp
      moreover have "\<forall>j < 0. \<forall>\<phi> \<in> reification (fst (pairs ! j)) (fst (snd (pairs ! j))) (snd (snd (pairs ! j))). satisfies \<phi> ?rho" by simp
      ultimately show ?case by auto
    next
      case (Suc k)
      then have k_lt: "k < length pairs" by auto
      from Suc.IH[OF Suc_leD[OF Suc.prems]] obtain rho where
        rho_01: "\<forall>v. rho v = 0 \<or> rho v = 1"
        and rho_base: "\<forall>v. is_input_pvar v \<longrightarrow> rho v = base v"
        and rho_sat: "\<forall>j < k. \<forall>\<phi> \<in> reification (fst (pairs ! j)) (fst (snd (pairs ! j))) (snd (snd (pairs ! j))). satisfies \<phi> rho"
        by blast
      let ?r = "fst (pairs ! k)"
      let ?cs = "fst (snd (pairs ! k))"
      let ?A = "snd (snd (pairs ! k))"
      let ?v = "pvar_of_lit ?r"
      define val :: nat
        where "val \<equiv> if pb_sum ?cs rho \<ge> ?A then (case ?r of Pos _ \<Rightarrow> 1 | Neg _ \<Rightarrow> 0) else (case ?r of Pos _ \<Rightarrow> 0 | Neg _ \<Rightarrow> 1)"
      have val_01: "val = 0 \<or> val = 1"
        unfolding val_def by (cases ?r; auto)
      define rho' where "rho' \<equiv> rho(?v := val)"
      have rho'_01: "\<forall>v. rho' v = 0 \<or> rho' v = 1"
        using rho_01 val_01 unfolding rho'_def by auto
      have rho'_base: "\<forall>v. is_input_pvar v \<longrightarrow> rho' v = base v"
      proof (intro allI impI)
        fix v :: "'v pvar"
        assume v_inp: "is_input_pvar v"
        show "rho' v = base v"
        proof (cases "v = ?v")
          case True
          with reif_not_input' k_lt v_inp show ?thesis by auto
        next
          case False
          thus ?thesis using rho_base v_inp unfolding rho'_def by simp
        qed
      qed
      have eval_r: "eval_lit ?r rho' = (if pb_sum ?cs rho \<ge> ?A then 1 else 0)"
        by (cases ?r; simp add: rho'_def eval_lit_def val_def pvar_of_lit_def split: if_splits)
      have cs_no_v: "?v \<notin> pvar_of_lit ` snd ` set ?cs"
      proof
        assume "?v \<in> pvar_of_lit ` snd ` set ?cs"
        then have "?v \<in> {x. is_input_pvar x} \<union> (pvar_of_lit ` fst ` set (take k pairs))"
          using wf_deps k_lt by (auto simp: split_beta)
        then show False
        proof (elim UnE)
          assume "?v \<in> {x. is_input_pvar x}"
          then have "is_input_pvar ?v" by simp
          with reif_not_input' k_lt show False by auto
        next
          assume "?v \<in> pvar_of_lit ` fst ` set (take k pairs)"
          then obtain r' where "r' \<in> fst ` set (take k pairs)" "pvar_of_lit r' = ?v"
            by (auto simp: pvar_of_lit_def split: literal.splits)
          then obtain i where "i < k" "pvar_of_lit (fst (pairs ! i)) = ?v"
            by (auto simp: in_set_conv_nth)
          with distinct' k_lt show False by auto
        qed
      qed
      have rho'_cs_agree: "pb_sum ?cs rho' = pb_sum ?cs rho"
      proof (intro pb_sum_congr, safe)
        fix a l assume "(a, l) \<in> set ?cs"
        from cs_no_v this show "eval_lit l rho' = eval_lit l rho"
          by (force simp: rho'_def eval_lit_def pvar_of_lit_def fun_upd_def image_iff split: literal.splits)
      qed
      have neg_cs_agree: "\<forall>(a, l) \<in> set (map (\<lambda>(a, l). (a, lit_neg l)) ?cs). eval_lit l rho' = eval_lit l rho"
        unfolding set_map
      proof safe
        fix a l assume "(a, l) \<in> set ?cs"
        then show "eval_lit (lit_neg l) rho' = eval_lit (lit_neg l) rho"
          unfolding rho'_def eval_lit_def using cs_no_v
          by (cases l) (auto simp: lit_neg_def image_iff pvar_of_lit_def)
      qed
      have neg_sum_eq: "pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) ?cs) rho' = pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) ?cs) rho"
        by (rule pb_sum_congr[OF neg_cs_agree])
      have pb_le_M: "pb_sum ?cs rho \<le> sum_list (map fst ?cs)"
        using pb_sum_add_negated_gen[OF rho_01, of ?cs] by simp
      have pb_sum_neg_eq: "pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) ?cs) rho = sum_list (map fst ?cs) - pb_sum ?cs rho"
      proof -
        have eq: "sum_list (map fst ?cs) = pb_sum ?cs rho + pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) ?cs) rho"
          using pb_sum_add_negated_gen[OF rho_01, of ?cs] by auto
        then show ?thesis by simp
      qed
      have sat_fwd: "satisfies (reif_fwd ?r ?cs ?A) rho'"
      proof -
        have "eval_lit (lit_neg ?r) rho' = (if pb_sum ?cs rho \<ge> ?A then 0 else 1)"
          using eval_r rho'_01 by (force simp add: eval_lit_def lit_neg_def split: if_splits literal.splits)
        then have "pb_sum (fst (reif_fwd ?r ?cs ?A)) rho' = ?A * (if pb_sum ?cs rho \<ge> ?A then 0 else 1) + pb_sum ?cs rho'"
          unfolding reif_fwd_def by simp
        also have "... = ?A * (if pb_sum ?cs rho \<ge> ?A then 0 else 1) + pb_sum ?cs rho"
          using rho'_cs_agree by auto
        also have "... \<ge> ?A"
        proof (cases "pb_sum ?cs rho \<ge> ?A")
          case True
          then show ?thesis using rho'_cs_agree by auto
        next
          case False
          then have "?A * 1 + pb_sum ?cs rho \<ge> ?A" by simp
          then show ?thesis using False by auto
        qed
        finally show ?thesis unfolding satisfies_def reif_fwd_def by auto
      qed
      have sat_bwd: "satisfies (reif_bwd ?r ?cs ?A) rho'"
      proof (cases "pb_sum ?cs rho \<ge> ?A")
        case True
        then have "eval_lit ?r rho' = 1" using eval_r by simp
        then have "snd (reif_bwd ?r ?cs ?A) = (sum_list (map fst ?cs) + 1 - ?A)"
          unfolding reif_bwd_def Let_def by simp
        also have "... \<le> (sum_list (map fst ?cs) + 1 - ?A) * eval_lit ?r rho' + pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) ?cs) rho'"
          using `eval_lit ?r rho' = 1` by simp
        finally show ?thesis unfolding satisfies_def reif_bwd_def Let_def by simp
      next
        case False
        then have pb_lt_A: "pb_sum ?cs rho < ?A" by simp
        have eval_r0: "eval_lit ?r rho' = 0" using eval_r False by simp
        have "snd (reif_bwd ?r ?cs ?A) = sum_list (map fst ?cs) + 1 - ?A"
          unfolding reif_bwd_def Let_def by simp
        also have "... \<le> pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) ?cs) rho'"
        proof -
          have "pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) ?cs) rho' = pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) ?cs) rho"
            using neg_sum_eq .
          also have "... = sum_list (map fst ?cs) - pb_sum ?cs rho"
            using pb_sum_neg_eq .
          also have "... \<ge> sum_list (map fst ?cs) + 1 - ?A"
          proof -
            have "pb_sum ?cs rho + 1 \<le> ?A" using pb_lt_A by auto
            then show ?thesis
              using pb_le_M by linarith
          qed
          finally show ?thesis .
        qed
        finally show ?thesis
          unfolding satisfies_def reif_bwd_def Let_def using eval_r0 by auto
      qed
      have sat_k: "\<forall>\<phi> \<in> reification ?r ?cs ?A. satisfies \<phi> rho'"
        using sat_fwd sat_bwd unfolding reification_def by auto
      have rho'_sat: "\<forall>j < Suc k. \<forall>\<phi> \<in> reification (fst (pairs ! j)) (fst (snd (pairs ! j))) (snd (snd (pairs ! j))). satisfies \<phi> rho'"
      proof (intro allI impI ballI)
        fix j \<phi>
        assume j_lt: "j < Suc k"
        assume \<phi>_reif: "\<phi> \<in> reification (fst (pairs ! j)) (fst (snd (pairs ! j))) (snd (snd (pairs ! j)))"
        show "satisfies \<phi> rho'"
        proof (cases "j < k")
          case True
          then have j_lt_k: "j < k" .
          let ?r_j = "fst (pairs ! j)"
          let ?cs_j = "fst (snd (pairs ! j))"
          have not_dep: "?v \<notin> constraint_pvars \<phi>"
          proof
            assume dep: "?v \<in> constraint_pvars \<phi>"
            have "constraint_pvars \<phi> \<subseteq> {pvar_of_lit ?r_j} \<union> (pvar_of_lit ` snd ` set ?cs_j)"
              using \<phi>_reif unfolding reification_def
              by (fastforce simp: reif_fwd_def reif_bwd_def constraint_pvars_def Let_def
                lit_neg_def pvar_of_lit_def image_iff split: if_splits literal.splits)
            then have "?v = pvar_of_lit ?r_j \<or> ?v \<in> pvar_of_lit ` snd ` set ?cs_j"
              using dep by auto
            then show False
            proof
              assume "?v = pvar_of_lit ?r_j"
              with distinct' j_lt_k k_lt show False by auto
            next
              assume v_in: "?v \<in> pvar_of_lit ` snd ` set ?cs_j"
              then have "?v \<in> {x. is_input_pvar x} \<union> (pvar_of_lit ` fst ` set (take j pairs))"
              proof -
                have j_lt_len: "j < length pairs" using True k_lt by (simp add: order.strict_trans)
                have "pvar_of_lit ` snd ` set ?cs_j \<subseteq> {x. is_input_pvar x} \<union> (pvar_of_lit ` fst ` set (take j pairs))"
                  using wf_deps j_lt_len by simp
                then show ?thesis using v_in by blast
              qed
              then have "?v \<in> pvar_of_lit ` fst ` set (take j pairs)"
              proof (elim UnE)
                assume "?v \<in> {x. is_input_pvar x}"
                then have "is_input_pvar ?v" by simp
                with reif_not_input' k_lt show ?thesis by auto
              next
                assume "?v \<in> pvar_of_lit ` fst ` set (take j pairs)"
                then show ?thesis .
              qed
              then obtain r' where "r' \<in> fst ` set (take j pairs)" "pvar_of_lit r' = ?v"
                by (auto simp: pvar_of_lit_def split: literal.splits)
              then obtain i where "i < j" "pvar_of_lit (fst (pairs ! i)) = ?v"
                by (auto simp: in_set_conv_nth)
              with distinct' j_lt_k k_lt show False by auto
            qed
          qed
          have "satisfies \<phi> rho"
            using rho_sat j_lt_k \<phi>_reif by blast
          moreover have "\<forall>v' \<in> constraint_pvars \<phi>. rho v' = rho' v'"
            using not_dep unfolding rho'_def by auto
          ultimately show ?thesis
            using satisfies_cong by metis
        next
          case False
          then have "j = k" using j_lt by auto
          then show ?thesis using sat_k \<phi>_reif by simp
        qed
      qed
      thus ?case using rho'_01 rho'_base rho'_sat by blast
    qed
  qed
  then obtain rho where
    rho_01: "\<forall>v. rho v = 0 \<or> rho v = 1"
    and rho_base: "\<forall>v. is_input_pvar v \<longrightarrow> rho v = base v"
    and rho_sat: "\<forall>j < length pairs. \<forall>\<phi> \<in> reification (fst (pairs ! j)) (fst (snd (pairs ! j))) (snd (snd (pairs ! j))). satisfies \<phi> rho"
    by auto
  have "models (circuit_constraints C) rho"
    unfolding models_def circuit_constraints_def C fst_conv
  proof (intro ballI)
    fix \<phi>
    assume "\<phi> \<in> (\<Union>(r, x, y)\<in>set pairs. reification r x y)"
    then obtain x where x_in: "x \<in> set pairs" and x_reif: "\<phi> \<in> reification (fst x) (fst (snd x)) (snd (snd x))" by auto
    then obtain j where "j < length pairs" "pairs ! j = x"
      by (auto simp: in_set_conv_nth)
    then show "satisfies \<phi> rho" using rho_sat x_reif by auto
  qed
  then show "\<exists>rho. models (circuit_constraints C) rho
    \<and> (\<forall>v. is_input_pvar v \<longrightarrow> rho v = base v)
    \<and> (\<forall>v. rho v = 0 \<or> rho v = 1)"
    using rho_01 rho_base by blast
qed

lemma models_circuit_constraints_cong:
  assumes "models (circuit_constraints C) rho1"
    and "\<forall> \<phi> \<in> circuit_constraints C. \<forall> v \<in> constraint_pvars \<phi>. rho1 v = rho2 v"
  shows "models (circuit_constraints C) rho2"
  unfolding models_def
proof
  fix \<phi> assume "\<phi> \<in> circuit_constraints C"
  then have "satisfies \<phi> rho1" using assms(1) unfolding models_def by auto
  moreover have "satisfies \<phi> rho1 = satisfies \<phi> rho2"
    by (rule satisfies_cong) (insert assms(2) `\<phi> \<in> circuit_constraints C`, auto)
  ultimately show "satisfies \<phi> rho2" by simp
qed

lemma pb_sum_cost_bits_gen:
  assumes "\<forall> i < k. rho (CostBit i) = (c div 2^i) mod 2"
  shows "pb_sum (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<k]) rho = c mod 2^k"
  using assms
proof (induction k)
  case 0 show ?case by simp
next
  case (Suc k)
  have IH: "pb_sum (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<k]) rho = c mod 2^k"
    using Suc.IH Suc.prems by auto
  have step: "rho (CostBit k) = c div 2^k mod 2"
    using Suc.prems by simp
  have "pb_sum (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<Suc k]) rho
      = pb_sum (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<k]) rho
        + pb_sum [(2^k, Pos (CostBit k))] rho"
    by (simp add: pb_sum_append)
  also have "... = c mod 2^k + 2^k * ((c div 2^k) mod 2)"
    using IH step by (simp add: eval_lit_def)
  also have "... = c mod 2^(Suc k)"
    by (metis add.commute mod_mult2_eq mult.commute power_Suc)
  finally show ?case by simp
qed

lemma cost_ge_constraint_sound':
  assumes "satisfies (cost_ge_constraint B) rho"
    and "\<forall> i < bits_needed B. rho (CostBit i) = (c div 2^i) mod 2"
  shows "c \<ge> B"
proof -
  have sum_eq: "pb_sum (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed B]) rho = c mod 2^(bits_needed B)"
    by (rule pb_sum_cost_bits_gen) (use assms(2) in auto)
  have "B \<le> c mod 2^(bits_needed B)"
  proof -
    from assms(1) have "B \<le> pb_sum (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed B]) rho"
      unfolding satisfies_def cost_ge_constraint_def by simp
    with sum_eq show ?thesis by linarith
  qed
  then show ?thesis by (meson mod_less_eq_dividend order_trans)
qed

lemma in_M_goal_bound:
  fixes \<Pi> :: "'v::linorder strips_task"
  assumes "in_M C_\<phi> \<Pi> s c"
    and "wf_circuit C_\<phi>"
    and circ_vars: "\<forall>(r, \<phi>) \<in> set (fst C_\<phi>). \<forall>v \<in> constraint_pvars \<phi>. is_input_pvar v \<or> v \<in> circuit_reif_pvars C_\<phi>"
    and disjoint: "\<forall>v \<in> circuit_reif_pvars C_\<phi>. \<not> is_input_pvar v \<and> v \<noteq> ReifI \<and> (\<forall>k. v \<noteq> ReifCostGe k)"
    and reifG_not_circ: "ReifG \<notin> circuit_reif_pvars C_\<phi>"
    and goal_cpr: "cpr_derives (encode_goal \<Pi> \<union> circuit_constraints C_\<phi> \<union> encode_cost_ge B \<union>
                      {unit_clause (snd C_\<phi>), unit_clause (Pos ReifG)})
                      (cost_ge_constraint B)"
    and "is_goal_state \<Pi> s"
    and "finite (vars \<Pi>)"
    and "goal \<Pi> \<subseteq> vars \<Pi>"
  shows "c \<ge> B"
proof (cases "c < 2^(bits_needed B)")
  case True
  from assms(1) obtain rho_raw where
    rho_raw_circ: "models (circuit_constraints C_\<phi>) rho_raw"
    and rho_raw_out: "eval_lit (snd C_\<phi>) rho_raw = 1"
    and rho_raw_sv: "\<forall>v. rho_raw (StateVar v) = (if v \<in> s then 1 else 0)"
    and rho_raw_cb: "\<forall>i. rho_raw (CostBit i) = (c div 2^i) mod 2"
    and rho_raw_pb: "\<forall>i. rho_raw (PrimedCostBit i) = 0"
    and rho_raw_01: "\<forall>v. rho_raw v = 0 \<or> rho_raw v = 1"
    unfolding in_M_def by blast
  have out_reif: "pvar_of_lit (snd C_\<phi>) \<in> circuit_reif_pvars C_\<phi>"
    by (rule wf_circuit_out_reif[OF assms(2)])
  define base where "base = state_rho \<Pi> s c"
  define rho_adj where "rho_adj v \<equiv> if is_input_pvar v then base v else rho_raw v" for v
  have rho_adj_agrees: "\<forall> \<phi> \<in> circuit_constraints C_\<phi>. \<forall> v \<in> constraint_pvars \<phi>. rho_raw v = rho_adj v"
  proof (intro ballI allI impI)
    fix \<phi> v assume "\<phi> \<in> circuit_constraints C_\<phi>" and "v \<in> constraint_pvars \<phi>"
    show "rho_raw v = rho_adj v"
    proof (cases "is_input_pvar v")
      case True
      have "rho_adj v = base v" by (simp add: rho_adj_def True)
      also have "base v = rho_raw v"
        unfolding base_def state_rho_def
        using True rho_raw_sv rho_raw_cb rho_raw_pb
        by (cases v; auto simp: is_input_pvar_def state_rho_def split: var.splits)
      finally show ?thesis by simp
    next
      case False
      then show ?thesis by (simp add: rho_adj_def)
    qed
  qed
  have rho_circ: "models (circuit_constraints C_\<phi>) rho_adj"
    by (rule models_circuit_constraints_cong[OF rho_raw_circ rho_adj_agrees])
  have rho_out: "eval_lit (snd C_\<phi>) rho_adj = 1"
  proof -
    have "eval_lit (snd C_\<phi>) rho_adj = eval_lit (snd C_\<phi>) rho_raw"
      using out_reif disjoint
      by (cases "snd C_\<phi>") (simp_all add: eval_lit_def rho_adj_def pvar_of_lit_def)
    also have "... = 1" by (rule rho_raw_out)
    finally show ?thesis .
  qed
  define rho_ext where "rho_ext = extend_rho C_\<phi> rho_adj base"
  have base_on_input: "\<forall>(v :: 'v pvar). is_input_pvar v \<longrightarrow> base v = rho_adj v"
    by (auto simp: rho_adj_def)
  have rho_ext_circ: "models (circuit_constraints C_\<phi>) rho_ext"
    unfolding rho_ext_def
    by (rule models_circuit_constraints_extend[OF rho_circ circ_vars base_on_input])
  have rho_ext_out: "eval_lit (snd C_\<phi>) rho_ext = 1"
    using eval_output_extend_rho[OF out_reif] rho_out by (simp add: rho_ext_def)
  have cost_constraints_not_circ:
    "\<forall>\<phi> \<in> encode_cost_ge B. \<forall>v \<in> constraint_pvars \<phi>. v \<notin> circuit_reif_pvars C_\<phi>"
  proof (intro ballI allI impI)
    fix \<phi> and v :: "'v pvar"
    assume "\<phi> \<in> encode_cost_ge B" and "v \<in> constraint_pvars \<phi>"
    then have "\<phi> = reif_fwd (Pos (ReifCostGe B)) (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed B]) B \<or>
               \<phi> = reif_bwd (Pos (ReifCostGe B)) (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed B]) B"
      unfolding encode_cost_ge_def reification_def by auto
    then show "v \<notin> circuit_reif_pvars C_\<phi>"
    proof (elim disjE)
      assume "\<phi> = reif_fwd (Pos (ReifCostGe B)) (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed B]) B"
      then have "v = ReifCostGe B \<or> (\<exists>i < bits_needed B. v = CostBit i)"
        using `v \<in> constraint_pvars \<phi>`
        unfolding constraint_pvars_def reif_fwd_def by (auto simp: pvar_of_lit_def lit_neg_def)
      with disjoint show ?thesis by (auto simp: is_input_pvar_def)
    next
      assume "\<phi> = reif_bwd (Pos (ReifCostGe B)) (map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed B]) B"
      then have "v = ReifCostGe B \<or> (\<exists>i < bits_needed B. v = CostBit i)"
        using `v \<in> constraint_pvars \<phi>`        unfolding constraint_pvars_def reif_bwd_def
        by (clarsimp simp: pvar_of_lit_def Let_def lit_neg_def split: literal.splits; arith)
      with disjoint show ?thesis by (auto simp: is_input_pvar_def)
    qed
  qed
  have goal_constraints_not_circ:
    "\<forall>\<phi> \<in> encode_goal \<Pi>. \<forall>v \<in> constraint_pvars \<phi>. v \<notin> circuit_reif_pvars C_\<phi>"
  proof (intro ballI allI impI)
    fix \<phi> and v :: "'v pvar"
    assume "\<phi> \<in> encode_goal \<Pi>" and "v \<in> constraint_pvars \<phi>"
    then have "\<phi> = reif_fwd (Pos ReifG) (state_lits (goal \<Pi>)) (card (goal \<Pi>)) \<or>
               \<phi> = reif_bwd (Pos ReifG) (state_lits (goal \<Pi>)) (card (goal \<Pi>))"
      unfolding encode_goal_def reification_def
      by (auto simp: Let_def)
    then show "v \<notin> circuit_reif_pvars C_\<phi>"
    proof (elim disjE)
      assume "\<phi> = reif_fwd (Pos ReifG) (state_lits (goal \<Pi>)) (card (goal \<Pi>))"
      then have "v = ReifG \<or> (\<exists>v' \<in> goal \<Pi>. v = StateVar v')"
        using `v \<in> constraint_pvars \<phi>`
        unfolding constraint_pvars_def reif_fwd_def state_lits_def
        by (auto simp: pvar_of_lit_def lit_neg_def finite_subset[OF assms(9) assms(8)] split: literal.splits)
      with disjoint reifG_not_circ show ?thesis by (auto simp: is_input_pvar_def)
    next
      assume "\<phi> = reif_bwd (Pos ReifG) (state_lits (goal \<Pi>)) (card (goal \<Pi>))"
      then have "v = ReifG \<or> (\<exists>v' \<in> goal \<Pi>. v = StateVar v')"
        using `v \<in> constraint_pvars \<phi>`
        unfolding constraint_pvars_def reif_bwd_def state_lits_def
        by (auto simp: pvar_of_lit_def lit_neg_def Let_def finite_subset[OF assms(9) assms(8)] split: literal.splits)
      with disjoint reifG_not_circ show ?thesis by (auto simp: is_input_pvar_def)
    qed
  qed
  have enc_cost_sat: "models (encode_cost_ge B) base"
  proof (cases "c \<ge> B")
    case True
    from cost_ge_encoding_sound[OF True `c < 2^(bits_needed B)`]
    show ?thesis unfolding base_def .
  next
    case False
    then have "c < B" by (simp add: not_le)
    from cost_ge_encoding_below[OF this]
    show ?thesis unfolding base_def .
  qed
  have goal_sat: "models (encode_goal \<Pi>) base"
    unfolding base_def
    by (rule goal_encoding_sound[OF assms(8) assms(9) assms(7)])
  have lit_axiom_sat: "satisfies (unit_clause (Pos ReifG)) rho_ext"
  proof -
    have rho_eq: "rho_ext ReifG = 1"
      by (simp add: rho_ext_def extend_rho_def base_def state_rho_def
                    is_input_pvar_def assms(7) reifG_not_circ split: if_splits)
    then show ?thesis
      unfolding satisfies_def unit_clause_def
      by (simp add: eval_lit_def)
  qed
  have hyp_model:
    "\<forall>\<psi> \<in> encode_goal \<Pi> \<union> circuit_constraints C_\<phi> \<union> encode_cost_ge B \<union>
              {unit_clause (snd C_\<phi>), unit_clause (Pos ReifG)}. satisfies \<psi> rho_ext"
  proof (intro ballI)
    fix \<psi>
    assume "\<psi> \<in> encode_goal \<Pi> \<union> circuit_constraints C_\<phi> \<union> encode_cost_ge B \<union>
              {unit_clause (snd C_\<phi>), unit_clause (Pos ReifG)}"
    then consider (goal) "\<psi> \<in> encode_goal \<Pi>"
                  | (circ) "\<psi> \<in> circuit_constraints C_\<phi>"
                  | (cost) "\<psi> \<in> encode_cost_ge B"
                  | (ax1) "\<psi> = unit_clause (snd C_\<phi>)"
                  | (ax2) "\<psi> = unit_clause (Pos ReifG)"
      by auto
    then show "satisfies \<psi> rho_ext"
    proof cases
      case goal
      then show ?thesis
        using goal_sat goal_constraints_not_circ
        unfolding rho_ext_def models_def
        by (auto simp: satisfies_extend_rho_eq_base)
    next
      case circ
      then show ?thesis
        using rho_ext_circ by (auto simp: models_def)
    next
      case cost
      then show ?thesis
        using enc_cost_sat cost_constraints_not_circ
        unfolding rho_ext_def models_def
        by (auto simp: satisfies_extend_rho_eq_base)
    next
      case ax1
      then show ?thesis
        using rho_ext_out by (simp add: satisfies_def unit_clause_def)
    next
      case ax2
      then show ?thesis
        by (simp add: lit_axiom_sat)
    qed
  qed
  have rho_adj_01: "\<forall> v. rho_adj v = 0 \<or> rho_adj v = 1"
    unfolding rho_adj_def base_def state_rho_def
    using rho_raw_01 by (auto simp add: is_input_pvar_def split: pvar.splits)
  then have rho_ext_01: "\<forall> v. rho_ext v = 0 \<or> rho_ext v = 1"
    unfolding rho_ext_def extend_rho_def base_def using state_rho_01 by metis
  have bound_sat: "satisfies (cost_ge_constraint B) rho_ext"
    using cpr_sound goal_cpr hyp_model models_def rho_ext_01 by blast
  then show ?thesis
  proof (rule cost_ge_constraint_sound')
    show "\<forall>i < bits_needed B. rho_ext (CostBit i) = (c div 2 ^ i) mod 2"
      using rho_raw_cb disjoint base_on_input
      by (auto simp: rho_ext_def extend_rho_def rho_adj_def base_def state_rho_def
                     is_input_pvar_def)
  qed
next
  case False
  then have "c \<ge> 2^(bits_needed B)" by simp
  then show ?thesis by (meson bits_needed_sufficient order.strict_implies_order order_less_le_trans)
qed


subsection \<open>Transition Step Soundness and CPR Theorem\<close>

(* Two-state valuation: encodes state s and cost c (current) plus s' and c' (primed),
   along with specific reification values needed for the transition encoding. *)
definition two_state_rho ::
  "'v::linorder strips_task \<Rightarrow> 'v state \<Rightarrow> nat \<Rightarrow> 'v state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('v action) list \<Rightarrow>
   ('v var pvar \<Rightarrow> nat)" where
  "two_state_rho \<Pi> s c s' c' sel_i as \<equiv> \<lambda>x. case x of
    StateVar (Original v) \<Rightarrow> if v \<in> s then 1 else 0
  | StateVar (Primed v)   \<Rightarrow> if v \<in> s' then 1 else 0
  | CostBit i            \<Rightarrow> (c div 2^i) mod 2
  | PrimedCostBit i      \<Rightarrow> (c' div 2^i) mod 2
  | ReifT                \<Rightarrow> 1
  | ReifDeltaCostLower k \<Rightarrow> if c' \<ge> c + k then 1 else 0
  | ReifDeltaCostUpper k \<Rightarrow> if c' \<le> c + k then 1 else 0
  | ReifDeltaCost k      \<Rightarrow> if k = c' - c then 1 else 0
  | ReifPrimedCostGe k   \<Rightarrow> if c' \<ge> k then 1 else 0
  | ReifGeq (Original v) \<Rightarrow> if v \<in> s \<or> v \<notin> s' then 1 else 0
  | ReifLeq (Original v) \<Rightarrow> if v \<notin> s \<or> v \<in> s' then 1 else 0
  | ReifEq (Original v)  \<Rightarrow> if (v \<in> s \<longleftrightarrow> v \<in> s') then 1 else 0
  | ReifAction i         \<Rightarrow> if i = sel_i then 1 else 0
  | _                    \<Rightarrow> 0"

lemma two_state_rho_range:
  "\<forall>v. two_state_rho \<Pi> s c s' c' sel_i as v = 0 \<or> two_state_rho \<Pi> s c s' c' sel_i as v = 1"
  by (auto simp: two_state_rho_def split: pvar.splits var.splits)

lemma pb_sum_pos_pvar_aux:
  assumes "distinct xs"
    and "\<forall>v \<in> set xs. rho (g v) = (if v \<in> T then 1 else 0)"
  shows "pb_sum (map (\<lambda>v. (1, Pos (g v))) xs) rho = card (set xs \<inter> T)"
  using assms
proof (induction xs)
  case Nil show ?case by simp
next
  case (Cons a xs)
  then have a_not_xs: "a \<notin> set xs" and "distinct xs"
    and vals: "\<forall>v \<in> set (a # xs). rho (g v) = (if v \<in> T then 1 else 0)" by auto
  have step: "pb_sum (map (\<lambda>v. (1, Pos (g v))) (a # xs)) rho
    = (if a \<in> T then 1 else 0) + pb_sum (map (\<lambda>v. (1, Pos (g v))) xs) rho"
    using vals by (simp add: eval_lit_def)
  have IH: "pb_sum (map (\<lambda>v. (1, Pos (g v))) xs) rho = card (set xs \<inter> T)"
    by (rule Cons.IH) (use Cons.prems in auto)
  have card_step: "(if a \<in> T then 1 else 0) + card (set xs \<inter> T) = card (set (a # xs) \<inter> T)"
    using a_not_xs by (auto simp: card_insert_if)
  show ?case using step IH card_step by linarith
qed

lemma pb_sum_neg_pvar_aux:
  assumes "distinct xs"
    and "\<forall>v \<in> set xs. rho (g v) = (if v \<in> T then 1 else 0)"
  shows "pb_sum (map (\<lambda>v. (1, Neg (g v))) xs) rho = card (set xs - T)"
  using assms
proof (induction xs)
  case Nil show ?case by simp
next
  case (Cons a xs)
  then have a_not_xs: "a \<notin> set xs" and "distinct xs"
    and vals: "\<forall>v \<in> set (a # xs). rho (g v) = (if v \<in> T then 1 else 0)" by auto
  have step: "pb_sum (map (\<lambda>v. (1, Neg (g v))) (a # xs)) rho
    = (if a \<notin> T then 1 else 0) + pb_sum (map (\<lambda>v. (1, Neg (g v))) xs) rho"
    using vals by (simp add: eval_lit_def)
  have IH: "pb_sum (map (\<lambda>v. (1, Neg (g v))) xs) rho = card (set xs - T)"
    by (rule Cons.IH) (use Cons.prems in auto)
  have card_step: "(if a \<notin> T then 1 else 0) + card (set xs - T) = card (set (a # xs) - T)"
    using a_not_xs by (auto simp: insert_Diff_if)
  show ?case using step IH card_step by linarith
qed

lemma pb_sum_pos_pvar_sorted:
  assumes fin: "finite S"
    and vals: "\<forall>v \<in> S. rho (g v) = (if v \<in> T then 1 else 0)"
  shows "pb_sum (map (\<lambda>v. (1, Pos (g v))) (sorted_list_of_set S)) rho = card (S \<inter> T)"
proof -
  have "pb_sum (map (\<lambda>v. (1, Pos (g v))) (sorted_list_of_set S)) rho
      = card (set (sorted_list_of_set S) \<inter> T)"
    by (rule pb_sum_pos_pvar_aux) (use fin vals in simp_all)
  also have "set (sorted_list_of_set S) = S" using fin by simp
  finally show ?thesis .
qed

lemma pb_sum_neg_pvar_sorted:
  assumes fin: "finite S"
    and vals: "\<forall>v \<in> S. rho (g v) = (if v \<in> T then 1 else 0)"
  shows "pb_sum (map (\<lambda>v. (1, Neg (g v))) (sorted_list_of_set S)) rho = card (S - T)"
proof -
  have "pb_sum (map (\<lambda>v. (1, Neg (g v))) (sorted_list_of_set S)) rho
      = card (set (sorted_list_of_set S) - T)"
    by (rule pb_sum_neg_pvar_aux) (use fin vals in simp_all)
  also have "set (sorted_list_of_set S) = S" using fin by simp
  finally show ?thesis .
qed

lemma pb_sum_primed_cost_bits_gen:
  assumes "\<forall> i < k. rho (PrimedCostBit i) = (c div 2^i) mod 2"
  shows "pb_sum (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<k]) rho = c mod 2^k"
  using assms
proof (induction k)
  case 0 show ?case by simp
next
  case (Suc k)
  have IH: "pb_sum (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<k]) rho = c mod 2^k"
    using Suc.IH Suc.prems by auto
  have step: "rho (PrimedCostBit k) = c div 2^k mod 2"
    using Suc.prems by simp
  have "pb_sum (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<Suc k]) rho
      = pb_sum (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<k]) rho
        + pb_sum [(2^k, Pos (PrimedCostBit k))] rho"
    by (simp add: pb_sum_append)
  also have "... = c mod 2^k + 2^k * ((c div 2^k) mod 2)"
    using IH step by (simp add: eval_lit_def)
  also have "... = c mod 2^(Suc k)"
    by (metis add.commute mod_mult2_eq mult.commute power_Suc)
  finally show ?case by simp
qed

lemma encode_transition_sound:
  fixes \<Pi> :: "'v::linorder strips_task"
  assumes fin_V: "finite V"
    and sel_lt: "sel_i < length as"
    and appl: "applicable (as ! sel_i) s"
    and succ_eq: "s' = successor (as ! sel_i) s"
    and cost_eq: "c' = c + cost (as ! sel_i)"
    and c'_lt_B: "c' < B"
    and pre_sub: "pre (as ! sel_i) \<subseteq> V"
    and add_sub: "add (as ! sel_i) \<subseteq> V"
    and del_sub: "del (as ! sel_i) \<subseteq> V"
  shows "models (encode_transition as V B)
                (two_state_rho \<Pi> s c s' c' sel_i as)"
proof -
  have c'_bound: "c' < 2^(bits_needed B)"
  proof -
    have "c' < B" using c'_lt_B .
    also have "B < 2^(bits_needed B)" by (rule bits_needed_sufficient)
    finally show ?thesis .
  qed
  let ?rho = "two_state_rho \<Pi> s c s' c' sel_i as"
  let ?rs = "action_reifs as"
  have rho_StateVar: "\<forall>v. ?rho (StateVar (Original v)) = (if v \<in> s then 1 else 0)"
    by (simp add: two_state_rho_def)
  have rho_CostBit: "\<forall>i. ?rho (CostBit i) = (c div 2^i) mod 2"
    by (simp add: two_state_rho_def)
  have rho_PrimedStateVar: "\<forall>v. ?rho (StateVar (Primed v)) = (if v \<in> s' then 1 else 0)"
    by (simp add: two_state_rho_def)
  have rho_PrimedCostBit: "\<forall>i. ?rho (PrimedCostBit i) = (c' div 2^i) mod 2"
    by (simp add: two_state_rho_def)
  have rho_ReifT: "?rho ReifT = 1"
    by (simp add: two_state_rho_def)
  have rho_ReifDeltaCost: "\<forall>k. ?rho (ReifDeltaCost k) = (if k = c' - c then 1 else 0)"
    by (simp add: two_state_rho_def)
  have rho_ReifPrimedCostGe: "\<forall>k. ?rho (ReifPrimedCostGe k) = (if c' \<ge> k then 1 else 0)"
    by (simp add: two_state_rho_def)
  have rho_ReifGeq: "\<forall>v. ?rho (ReifGeq (Original v)) = (if v \<in> s \<or> v \<notin> s' then 1 else 0)"
    by (simp add: two_state_rho_def)
  have rho_ReifLeq: "\<forall>v. ?rho (ReifLeq (Original v)) = (if v \<notin> s \<or> v \<in> s' then 1 else 0)"
    by (simp add: two_state_rho_def)
  have rho_ReifEq: "\<forall>v. ?rho (ReifEq (Original v)) = (if (v \<in> s \<longleftrightarrow> v \<in> s') then 1 else 0)"
    by (simp add: two_state_rho_def)
  have rho_ReifAction: "\<forall>i. ?rho (ReifAction i) = (if i = sel_i then 1 else 0)"
    by (simp add: two_state_rho_def)

  have models_action_cs:
    "models (\<Union>i<length as. {action_constraint (?rs!i) (as!i) V B}) ?rho"
  proof (unfold models_def, intro ballI)
    fix \<phi>
    assume \<phi>_in: "\<phi> \<in> (\<Union>i<length as. {action_constraint (?rs!i) (as!i) V B})"
    then obtain i where i_lt: "i < length as"
      and \<phi>_eq: "\<phi> = action_constraint (?rs!i) (as!i) V B"
      by auto
    show "satisfies \<phi> ?rho"
    proof (cases "i = sel_i")
      case True
      have r_eq: "?rs ! i = Pos (ReifAction i)"
        unfolding action_reifs_def using i_lt by simp
      have a_eq: "as!i = as!sel_i" using True by simp
      have fin_pre: "finite (pre (as!i))"
        using fin_V pre_sub i_lt True by (blast intro: finite_subset)
      have fin_add: "finite (add (as!i))"
        using fin_V add_sub i_lt True by (blast intro: finite_subset)
      have fin_del: "finite (del (as!i))"
        using fin_V del_sub i_lt True by (blast intro: finite_subset)
      have fin_Vevars: "finite (V - evars (as!i))" using fin_V by simp
      have pre_sub_s: "pre (as!i) \<subseteq> s"
        using appl True i_lt unfolding applicable_def by auto
      have add_sub_s': "add (as!i) \<subseteq> s'"
        using succ_eq a_eq by (simp add: successor_def)
      have delta_val: "pb_sum [(1, Pos (ReifDeltaCost (cost (as!i))))] ?rho = 1"
        using cost_eq rho_ReifDeltaCost True by (simp add: eval_lit_def)
      have pre_val: "pb_sum (map (\<lambda>v. (1, Pos (StateVar (Original v)))) (sorted_list_of_set (pre (as!i)))) ?rho
        = card (pre (as!i))"
      proof -
        have "pb_sum (map (\<lambda>v. (1, Pos (StateVar (Original v)))) (sorted_list_of_set (pre (as!i)))) ?rho
          = card (pre (as!i) \<inter> s)"
          by (rule pb_sum_pos_pvar_sorted[OF fin_pre, where g="\<lambda>v. StateVar (Original v)" and T=s])
             (simp add: rho_StateVar)
        also have "pre (as!i) \<inter> s = pre (as!i)" using pre_sub_s by auto
        finally show ?thesis by simp
      qed
      have add_val: "pb_sum (map (\<lambda>v. (1, Pos (StateVar (Primed v)))) (sorted_list_of_set (add (as!i)))) ?rho
        = card (add (as!i))"
      proof -
        have "pb_sum (map (\<lambda>v. (1, Pos (StateVar (Primed v)))) (sorted_list_of_set (add (as!i)))) ?rho
          = card (add (as!i) \<inter> s')"
          by (rule pb_sum_pos_pvar_sorted[OF fin_add, where g="\<lambda>v. StateVar (Primed v)" and T=s'])
             (simp add: rho_PrimedStateVar)
        also have "add (as!i) \<inter> s' = add (as!i)" using add_sub_s' by auto
        finally show ?thesis by simp
      qed
      have del_val: "pb_sum (map (\<lambda>v. (1, Neg (StateVar (Primed v)))) (sorted_list_of_set (del (as!i)))) ?rho
        = card (del (as!i) - s')"
        by (rule pb_sum_neg_pvar_sorted[OF fin_del, where g="\<lambda>v. StateVar (Primed v)" and T=s'])
           (simp add: rho_PrimedStateVar)
      have not_evars_unchanged: "\<forall>v \<in> V - evars (as!i). (v \<in> s \<longleftrightarrow> v \<in> s')"
        unfolding succ_eq successor_def evars_def using True a_eq by auto
      have frame_val:
        "pb_sum (map (\<lambda>v. (1, Pos (ReifEq (Original v)))) (sorted_list_of_set (V - evars (as!i)))) ?rho
         = card (V - evars (as!i))"
      proof -
        have "pb_sum (map (\<lambda>v. (1, Pos (ReifEq (Original v)))) (sorted_list_of_set (V - evars (as!i)))) ?rho
          = card ((V - evars (as!i)) \<inter> (V - evars (as!i)))"
          by (rule pb_sum_pos_pvar_sorted[OF fin_Vevars, where g="\<lambda>v. ReifEq (Original v)" and T="V - evars (as!i)"])
             (auto simp: rho_ReifEq not_evars_unchanged)
        also have "(V - evars (as!i)) \<inter> (V - evars (as!i)) = V - evars (as!i)" by auto
        finally show ?thesis by simp
      qed
      have bound_val: "pb_sum [(1, Neg (ReifPrimedCostGe B))] ?rho = 1"
        using c'_lt_B rho_ReifPrimedCostGe by (simp add: eval_lit_def)
      have evars_sub_V: "evars (as!i) \<subseteq> V"
        unfolding evars_def using add_sub del_sub i_lt True by auto
      have card_add_del_frame:
        "card (add (as!i)) + card (del (as!i) - s') + card (V - evars (as!i)) = card V"
      proof -
        have disj_add_del: "add (as!i) \<inter> (del (as!i) - add (as!i)) = {}" by auto
        have union_add_del: "add (as!i) \<union> (del (as!i) - add (as!i)) = evars (as!i)"
          unfolding evars_def by auto
        have card_add_del_minus:
          "card (add (as!i)) + card (del (as!i) - add (as!i)) = card (evars (as!i))"
          using card_Un_disjoint[OF fin_add finite_Diff[OF fin_del] disj_add_del]
          unfolding union_add_del by simp
        have del_s'_eq_del_minus_add: "del (as!i) - s' = del (as!i) - add (as!i)"
          unfolding succ_eq successor_def using True a_eq by auto
        have card_V_part: "card V = card (V - evars (as!i)) + card (evars (as!i))"
          by (metis add.commute card_Int_Diff evars_sub_V fin_V inf.absorb_iff2)
        show ?thesis
          using card_add_del_minus del_s'_eq_del_minus_add card_V_part by simp
      qed
      have A_val: "snd \<phi> = 2 + card (pre (as!i)) + card V"
        unfolding \<phi>_eq action_constraint_def Let_def by simp
      have lhs_eq: "fst \<phi> = [(2 + card (pre (as!i)) + card V, lit_neg (?rs!i))] @
          [(1, Pos (ReifDeltaCost (cost (as!i))))] @
          map (\<lambda>v. (1, Pos (StateVar (Original v)))) (sorted_list_of_set (pre (as!i))) @
          map (\<lambda>v. (1, Pos (StateVar (Primed v)))) (sorted_list_of_set (add (as!i))) @
          map (\<lambda>v. (1, Neg (StateVar (Primed v)))) (sorted_list_of_set (del (as!i))) @
          map (\<lambda>v. (1, Pos (ReifEq (Original v)))) (sorted_list_of_set (V - evars (as!i))) @
          [(1, Neg (ReifPrimedCostGe B))]"
        unfolding \<phi>_eq action_constraint_def Let_def by simp
      have lit_neg_pb: "pb_sum [(2 + card (pre (as!i)) + card V, lit_neg (?rs!i))] ?rho = 0"
        using r_eq rho_ReifAction True by (simp add: lit_neg_def eval_lit_def)
      have total_sum: "pb_sum (fst \<phi>) ?rho = 2 + card (pre (as!i)) + card V"
      proof -
        have "pb_sum (fst \<phi>) ?rho =
          pb_sum [(2 + card (pre (as!i)) + card V, lit_neg (?rs!i))] ?rho +
          pb_sum ([(1, Pos (ReifDeltaCost (cost (as!i))))] @
            map (\<lambda>v. (1, Pos (StateVar (Original v)))) (sorted_list_of_set (pre (as!i))) @
            map (\<lambda>v. (1, Pos (StateVar (Primed v)))) (sorted_list_of_set (add (as!i))) @
            map (\<lambda>v. (1, Neg (StateVar (Primed v)))) (sorted_list_of_set (del (as!i))) @
            map (\<lambda>v. (1, Pos (ReifEq (Original v)))) (sorted_list_of_set (V - evars (as!i))) @
            [(1, Neg (ReifPrimedCostGe B))]) ?rho"
          by (simp add: lhs_eq pb_sum_append)
        also have "... = 1 + card (pre (as!i)) +
          (card (add (as!i)) + card (del (as!i) - s') + card (V - evars (as!i))) + 1"
          unfolding pb_sum_append delta_val pre_val add_val del_val frame_val bound_val lit_neg_pb
          by simp
        also have "... = 1 + card (pre (as!i)) + card V + 1"
          by (simp add: card_add_del_frame)
        also have "... = 2 + card (pre (as!i)) + card V" by simp
        finally show ?thesis .
      qed
      show "satisfies \<phi> ?rho"
        using total_sum A_val by (simp add: satisfies_def prod.case_eq_if)
    next
      case False
      have r_eq: "?rs ! i = Pos (ReifAction i)"
        unfolding action_reifs_def using i_lt by simp
      have eval_r_neg_1: "eval_lit (lit_neg (?rs ! i)) ?rho = 1"
        by (simp add: r_eq False lit_neg_def eval_lit_def rho_ReifAction)
      show "satisfies \<phi> ?rho"
      proof -
        have mem: "(2 + card (pre (as!i)) + card V, lit_neg (?rs!i)) \<in> set (fst \<phi>)"
          unfolding \<phi>_eq action_constraint_def Let_def by simp
        have sum_ge: "pb_sum (fst \<phi>) ?rho \<ge> 2 + card (pre (as!i)) + card V"
        proof -
          have "pb_sum (fst \<phi>) ?rho \<ge>
                (2 + card (pre (as!i)) + card V) * eval_lit (lit_neg (?rs!i)) ?rho"
            by (rule pb_sum_ge_term[OF mem])
          also have "(2 + card (pre (as!i)) + card V) * eval_lit (lit_neg (?rs!i)) ?rho
                   = 2 + card (pre (as!i)) + card V"
            using eval_r_neg_1 by simp
          finally show ?thesis .
        qed
        have A_eq: "snd \<phi> = 2 + card (pre (as!i)) + card V"
          unfolding \<phi>_eq action_constraint_def Let_def by simp
        show "satisfies \<phi> ?rho"
          using sum_ge A_eq by (simp add: satisfies_def prod.case_eq_if)
      qed
    qed
  qed

  have models_delta_cs:
    "models (\<Union>a\<in>set as. encode_delta_cost (cost a) (bits_needed B)) ?rho"
  unfolding models_def
  proof (intro ballI)
    fix \<phi> :: "'v var pconstraint"
    assume \<phi>_in: "\<phi> \<in> (\<Union>a\<in>set as. encode_delta_cost (cost a) (bits_needed B))"
    from \<phi>_in obtain a :: "'v action" where a_in: "a \<in> set as"
      and \<phi>_dc: "\<phi> \<in> encode_delta_cost (cost a) (bits_needed B)" by auto
    let ?k   = "cost a"
    let ?pcl  = "map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<bits_needed B]"
    let ?cl   = "map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed B]"
    let ?ncl  = "map (\<lambda>i. (2^i, Neg (CostBit i))) [0..<bits_needed B]"
    let ?ncl' = "map (\<lambda>i. (2^i, Neg (PrimedCostBit i))) [0..<bits_needed B]"
    let ?M    = "2^(bits_needed B) - (1::nat)"
    have c_bound: "c < 2^(bits_needed B)"
      using add_lessD1 c'_bound cost_eq by blast
    have all_01: "\<forall>v. ?rho v = 0 \<or> ?rho v = 1" by (rule two_state_rho_range)
    have pb_pcl: "pb_sum ?pcl ?rho = c'"
      by (metis (mono_tags, lifting) c'_bound mod_less pb_sum_primed_cost_bits_gen
          rho_PrimedCostBit)
    have pb_cl: "pb_sum ?cl ?rho = c"
      by (metis (mono_tags, lifting) c_bound div_less mod_eq_self_iff_div_eq_0 pb_sum_cost_bits_gen
          rho_CostBit)
    have pb_ncl: "pb_sum ?ncl ?rho = ?M - c"
    proof -
      have "pb_sum ?cl ?rho + pb_sum ?ncl ?rho = sum_list (map fst ?cl)"
        using pb_sum_add_negated_gen[OF all_01, of ?cl]
        by (auto simp: lit_neg_def o_def)
      moreover have "sum_list (map fst ?cl) = ?M" by (auto simp: sum_list_exp o_def)
      ultimately show ?thesis using pb_cl
        by (metis (no_types, lifting) diff_add_inverse)
    qed
    have pb_ncl': "pb_sum ?ncl' ?rho = ?M - c'"
    proof -
      have "pb_sum ?pcl ?rho + pb_sum ?ncl' ?rho = sum_list (map fst ?pcl)"
        using pb_sum_add_negated_gen[OF all_01, of ?pcl] by (auto simp: lit_neg_def o_def)
      moreover have "sum_list (map fst ?pcl) = ?M" by (auto simp: sum_list_exp o_def)
      ultimately show ?thesis using pb_pcl
        by (metis (no_types, lifting) diff_add_inverse)
    qed
    have rho_rl: "?rho (ReifDeltaCostLower ?k) = (if c' \<ge> c + ?k then 1 else 0)"
      by (simp add: two_state_rho_def)
    have rho_ru: "?rho (ReifDeltaCostUpper ?k) = (if c' \<le> c + ?k then 1 else 0)"
      by (simp add: two_state_rho_def)
    have rho_rd: "?rho (ReifDeltaCost ?k) = (if ?k = c' - c then 1 else 0)"
      using rho_ReifDeltaCost by simp
    have rd_iff: "?rho (ReifDeltaCost ?k) = 1 \<longleftrightarrow>
                  ?rho (ReifDeltaCostLower ?k) = 1 \<and> ?rho (ReifDeltaCostUpper ?k) = 1"
      using rho_rd rho_rl rho_ru cost_eq by (auto split: if_splits)
    from \<phi>_dc have \<phi>_cases:
      "\<phi> \<in> reification (Pos (ReifDeltaCostLower ?k)) (?pcl @ ?ncl) (?k + ?M) \<or>
       \<phi> \<in> reification (Pos (ReifDeltaCostUpper ?k)) (?cl @ ?ncl') (?M - ?k) \<or>
       \<phi> \<in> reification (Pos (ReifDeltaCost ?k))
                 [(1, Pos (ReifDeltaCostLower ?k)), (1, Pos (ReifDeltaCostUpper ?k))] 2"
      unfolding encode_delta_cost_def Let_def by auto
    show "satisfies \<phi> ?rho" using \<phi>_cases
    proof (elim disjE)
      assume h1: "\<phi> \<in> reification (Pos (ReifDeltaCostLower ?k)) (?pcl @ ?ncl) (?k + ?M)"
      from h1 have \<phi>_l: "\<phi> = reif_fwd (Pos (ReifDeltaCostLower ?k)) (?pcl @ ?ncl) (?k + ?M) \<or>
                          \<phi> = reif_bwd (Pos (ReifDeltaCostLower ?k)) (?pcl @ ?ncl) (?k + ?M)"
        unfolding reification_def by auto
      show "satisfies \<phi> ?rho" using \<phi>_l
      proof (elim disjE)
        assume eq: "\<phi> = reif_fwd (Pos (ReifDeltaCostLower ?k)) (?pcl @ ?ncl) (?k + ?M)"
        show ?thesis
          unfolding eq satisfies_def reif_fwd_def
          using rho_rl c_bound c'_bound pb_pcl pb_ncl
          by (auto simp: eval_lit_def lit_neg_def pb_sum_append)
      next
        assume eq: "\<phi> = reif_bwd (Pos (ReifDeltaCostLower ?k)) (?pcl @ ?ncl) (?k + ?M)"
        have "c + cost a > c' \<Longrightarrow> Suc (2^(bits_needed B) - Suc (cost a)) \<le> 2^(bits_needed B) + c - Suc c'"
          by (smt (verit, best) Nat.diff_cancel add.commute add.left_commute c'_lt_B
              diff_less_mono2 le_trans bits_needed_sufficient linorder_not_less
              not_less_eq plus_1_eq_Suc trans_less_add1)
        then show ?thesis
          unfolding eq satisfies_def reif_bwd_def Let_def
          using rho_rl c_bound c'_bound pb_cl pb_pcl pb_ncl pb_ncl'
          by (auto simp: eval_lit_def lit_neg_def pb_sum_append
            sum_list_exp o_def not_le simp del: upt.simps)
      qed
    next
      assume h2: "\<phi> \<in> reification (Pos (ReifDeltaCostUpper ?k)) (?cl @ ?ncl') (?M - ?k)"
      from h2 have \<phi>_u: "\<phi> = reif_fwd (Pos (ReifDeltaCostUpper ?k)) (?cl @ ?ncl') (?M - ?k) \<or>
                          \<phi> = reif_bwd (Pos (ReifDeltaCostUpper ?k)) (?cl @ ?ncl') (?M - ?k)"
        unfolding reification_def by auto
      show "satisfies \<phi> ?rho" using \<phi>_u
      proof (elim disjE)
        assume eq: "\<phi> = reif_fwd (Pos (ReifDeltaCostUpper ?k)) (?cl @ ?ncl') (?M - ?k)"
        show ?thesis
          unfolding eq satisfies_def reif_fwd_def
          using rho_ru c_bound c'_bound pb_cl pb_ncl'
          by (auto simp: eval_lit_def lit_neg_def pb_sum_append)
      next
        assume eq: "\<phi> = reif_bwd (Pos (ReifDeltaCostUpper ?k)) (?cl @ ?ncl') (?M - ?k)"
        show ?thesis
          unfolding eq satisfies_def reif_bwd_def Let_def
          using rho_ru c_bound c'_bound pb_pcl pb_ncl
          by (auto simp: eval_lit_def lit_neg_def pb_sum_append
                   sum_list_exp o_def simp del: upt.simps)
      qed
    next
      assume h3: "\<phi> \<in> reification (Pos (ReifDeltaCost ?k))
                       [(1, Pos (ReifDeltaCostLower ?k)), (1, Pos (ReifDeltaCostUpper ?k))] 2"
      from h3 have \<phi>_d:
        "\<phi> = reif_fwd (Pos (ReifDeltaCost ?k))
                      [(1, Pos (ReifDeltaCostLower ?k)), (1, Pos (ReifDeltaCostUpper ?k))] 2 \<or>
         \<phi> = reif_bwd (Pos (ReifDeltaCost ?k))
                      [(1, Pos (ReifDeltaCostLower ?k)), (1, Pos (ReifDeltaCostUpper ?k))] 2"
        unfolding reification_def by auto
      have rl01: "?rho (ReifDeltaCostLower ?k) = 0 \<or> ?rho (ReifDeltaCostLower ?k) = 1"
        using all_01 by blast
      have ru01: "?rho (ReifDeltaCostUpper ?k) = 0 \<or> ?rho (ReifDeltaCostUpper ?k) = 1"
        using all_01 by blast
      show "satisfies \<phi> ?rho" using \<phi>_d
      proof (elim disjE)
        assume eq: "\<phi> = reif_fwd (Pos (ReifDeltaCost ?k))
                         [(1, Pos (ReifDeltaCostLower ?k)), (1, Pos (ReifDeltaCostUpper ?k))] 2"
        show ?thesis
          unfolding eq satisfies_def reif_fwd_def
          using rd_iff rl01 ru01 rho_rd rho_rl rho_ru
          by (auto simp: eval_lit_def lit_neg_def cost_eq)
      next
        assume eq: "\<phi> = reif_bwd (Pos (ReifDeltaCost ?k))
                         [(1, Pos (ReifDeltaCostLower ?k)), (1, Pos (ReifDeltaCostUpper ?k))] 2"
        show ?thesis
          unfolding eq satisfies_def reif_bwd_def Let_def
          using rd_iff rl01 ru01
          by (auto simp: eval_lit_def lit_neg_def)
      qed

    qed
  qed

  have models_eq_cs: "models (\<Union>v\<in>V. encode_eq_var v) ?rho"
  proof (unfold models_def, intro ballI)
    fix \<phi> assume \<phi>_in: "\<phi> \<in> (\<Union>v\<in>V. encode_eq_var v)"
    then obtain u where u_in: "u \<in> V" and \<phi>_eq: "\<phi> \<in> encode_eq_var u" by auto
    from \<phi>_eq have disj:
      "\<phi> = reif_fwd (Pos (ReifGeq (Original u))) [(1, Pos (StateVar (Original u))), (1, Neg (StateVar (Primed u)))] 1 \<or>
       \<phi> = reif_bwd (Pos (ReifGeq (Original u))) [(1, Pos (StateVar (Original u))), (1, Neg (StateVar (Primed u)))] 1 \<or>
       \<phi> = reif_fwd (Pos (ReifLeq (Original u))) [(1, Neg (StateVar (Original u))), (1, Pos (StateVar (Primed u)))] 1 \<or>
       \<phi> = reif_bwd (Pos (ReifLeq (Original u))) [(1, Neg (StateVar (Original u))), (1, Pos (StateVar (Primed u)))] 1 \<or>
       \<phi> = reif_fwd (Pos (ReifEq (Original u))) [(1, Pos (ReifLeq (Original u))), (1, Pos (ReifGeq (Original u)))] 2 \<or>
       \<phi> = reif_bwd (Pos (ReifEq (Original u))) [(1, Pos (ReifLeq (Original u))), (1, Pos (ReifGeq (Original u)))] 2"
      unfolding encode_eq_var_def reification_def by auto
    show "satisfies \<phi> ?rho" using disj
    proof (elim disjE)
      assume eq: "\<phi> = reif_fwd (Pos (ReifGeq (Original u))) [(1, Pos (StateVar (Original u))), (1, Neg (StateVar (Primed u)))] 1"
      show ?thesis
        unfolding eq satisfies_def reif_fwd_def
        using rho_ReifGeq rho_StateVar rho_PrimedStateVar
        by (auto simp: eval_lit_def lit_neg_def)
    next
      assume eq: "\<phi> = reif_bwd (Pos (ReifGeq (Original u))) [(1, Pos (StateVar (Original u))), (1, Neg (StateVar (Primed u)))] 1"
      show ?thesis
        unfolding eq satisfies_def reif_bwd_def Let_def
        using rho_ReifGeq rho_StateVar rho_PrimedStateVar
        by (auto simp: eval_lit_def lit_neg_def)
    next
      assume eq: "\<phi> = reif_fwd (Pos (ReifLeq (Original u))) [(1, Neg (StateVar (Original u))), (1, Pos (StateVar (Primed u)))] 1"
      show ?thesis
        unfolding eq satisfies_def reif_fwd_def
        using rho_ReifLeq rho_StateVar rho_PrimedStateVar
        by (auto simp: eval_lit_def lit_neg_def)
    next
      assume eq: "\<phi> = reif_bwd (Pos (ReifLeq (Original u))) [(1, Neg (StateVar (Original u))), (1, Pos (StateVar (Primed u)))] 1"
      show ?thesis
        unfolding eq satisfies_def reif_bwd_def Let_def
        using rho_ReifLeq rho_StateVar rho_PrimedStateVar
        by (auto simp: eval_lit_def lit_neg_def)
    next
      assume eq: "\<phi> = reif_fwd (Pos (ReifEq (Original u))) [(1, Pos (ReifLeq (Original u))), (1, Pos (ReifGeq (Original u)))] 2"
      show ?thesis
        unfolding eq satisfies_def reif_fwd_def
        using rho_ReifEq rho_ReifLeq rho_ReifGeq
        by (auto simp: eval_lit_def lit_neg_def)
    next
      assume eq: "\<phi> = reif_bwd (Pos (ReifEq (Original u))) [(1, Pos (ReifLeq (Original u))), (1, Pos (ReifGeq (Original u)))] 2"
      show ?thesis
        unfolding eq satisfies_def reif_bwd_def Let_def
        using rho_ReifEq rho_ReifLeq rho_ReifGeq
        by (auto simp: eval_lit_def lit_neg_def)
    qed
  qed

  have models_primed_ge: "models (encode_cost_ge_primed B) ?rho"
  proof (unfold models_def, intro ballI)
    fix \<phi> :: "'v var pconstraint" assume \<phi>_in: "\<phi> \<in> encode_cost_ge_primed B"
    from \<phi>_in have disj:
      "\<phi> = reif_fwd (Pos (ReifPrimedCostGe B)) (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<bits_needed B]) B \<or>
       \<phi> = reif_bwd (Pos (ReifPrimedCostGe B)) (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<bits_needed B]) B"
      unfolding encode_cost_ge_primed_def reification_def by auto
    show "satisfies \<phi> ?rho" using disj
    proof (elim disjE)
      assume eq: "\<phi> = reif_fwd (Pos (ReifPrimedCostGe B))
              (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<bits_needed B]) B"
      show ?thesis
        unfolding eq satisfies_def reif_fwd_def Let_def split_beta snd_conv fst_conv
      proof (cases "c' \<ge> B")
        case True
        have r_eval: "eval_lit (lit_neg (Pos (ReifPrimedCostGe B))) ?rho = 0"
          using rho_ReifPrimedCostGe True by (simp add: eval_lit_def lit_neg_def)
        have pb_coeffs: "pb_sum (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<bits_needed B]) ?rho = c'"
          using rho_PrimedCostBit c'_bound
          by (metis (lifting) ext mod_less pb_sum_primed_cost_bits_gen)
        then show "pb_sum ([(B, lit_neg (Pos (ReifPrimedCostGe B)))] @
                    map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<bits_needed B]) ?rho \<ge> B"
          using r_eval True by (simp add: pb_sum_append)
      next
        case False
        have r_eval: "eval_lit (lit_neg (Pos (ReifPrimedCostGe B))) ?rho = 1"
          using rho_ReifPrimedCostGe False by (simp add: eval_lit_def lit_neg_def)
        show "pb_sum ([(B, lit_neg (Pos (ReifPrimedCostGe B)))] @
                    map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<bits_needed B]) ?rho \<ge> B"
          using r_eval by (simp add: pb_sum_append)
      qed
    next
      assume eq: "\<phi> = reif_bwd (Pos (ReifPrimedCostGe B))
              (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<bits_needed B]) B"
      let ?coeffs = "map (\<lambda>i. (2^i :: nat, Pos (PrimedCostBit i :: 'v var pvar))) [0..<bits_needed B]"
      let ?M = "sum_list (map fst ?coeffs)"
      have M_val: "?M = 2^(bits_needed B) - 1"
        by (auto simp: o_def sum_list_exp)
      have M'_val: "?M - B + 1 = 2^(bits_needed B) - B" unfolding M_val
        by (metis Suc_diff_Suc Suc_eq_plus1 diff_Suc_eq_diff_pred bits_needed_sufficient)
      have pb_coeffs: "pb_sum ?coeffs ?rho = c'"
        using rho_PrimedCostBit c'_bound
        by (metis (lifting) ext mod_less pb_sum_primed_cost_bits_gen)
      have pb_neg: "pb_sum (map (\<lambda>(a,l). (a, lit_neg l)) ?coeffs) ?rho = (2^(bits_needed B) - 1) - c'"
      proof -
        have all_01: "\<forall>v. ?rho v = 0 \<or> ?rho v = 1" by (rule two_state_rho_range)
        have "pb_sum ?coeffs ?rho + pb_sum (map (\<lambda>(a,l). (a, lit_neg l)) ?coeffs) ?rho = ?M"
          using all_01 pb_sum_add_negated_gen by blast
        then show ?thesis using pb_coeffs M_val by simp
      qed
      have r_eval: "eval_lit (Pos (ReifPrimedCostGe B)) ?rho = 0"
        using rho_ReifPrimedCostGe c'_lt_B by (simp add: eval_lit_def)
      have "pb_sum ([(?M - B + 1, Pos (ReifPrimedCostGe B))] @
                    map (\<lambda>(a,l). (a, lit_neg l)) ?coeffs) ?rho
          = (?M - B + 1) * 0 + ((2^(bits_needed B) - 1) - c')"
        using r_eval pb_neg M'_val by (simp add: pb_sum_append)
      moreover have "Suc c' < 2^(bits_needed B)"
      proof -
        have "Suc c' \<le> B" using c'_lt_B by simp
        also have "B < 2^(bits_needed B)" by (rule bits_needed_sufficient)
        finally show ?thesis .
      qed
      ultimately show ?thesis using c'_lt_B
        by (auto simp: satisfies_def reif_bwd_def r_eval eq Let_def o_def mult_2 Suc_le_eq sum_list_exp
          intro!: diff_less_mono2)
    qed
  qed

  have models_sel: "models (action_selection_reif ?rs) ?rho"
  proof (unfold models_def, intro ballI)
    fix \<phi> :: "'v var pconstraint" assume \<phi>_in: "\<phi> \<in> action_selection_reif ?rs"
    from \<phi>_in have disj:
      "\<phi> = reif_fwd (Pos ReifT) (map (\<lambda>i. (1, Pos (ReifAction i))) [0..<length as]) 1 \<or>
       \<phi> = reif_bwd (Pos ReifT) (map (\<lambda>i. (1, Pos (ReifAction i))) [0..<length as]) 1"
      unfolding action_selection_reif_def action_reifs_def reification_def
      by (auto simp: o_def)
    show "satisfies \<phi> ?rho" using disj
    proof (elim disjE)
      assume eq: "\<phi> = reif_fwd (Pos ReifT) (map (\<lambda>i. (1, Pos (ReifAction i))) [0..<length as]) 1"
      have sum_ge: "pb_sum (map (\<lambda>i. (1, Pos (ReifAction i))) [0..<length as]) ?rho \<ge> 1"
      proof -
        have mem: "(1, Pos (ReifAction sel_i)) \<in> set (map (\<lambda>i. (1, Pos (ReifAction i))) [0..<length as])"
          using sel_lt by auto
        have "pb_sum (map (\<lambda>i. (1, Pos (ReifAction i))) [0..<length as]) ?rho \<ge>
               1 * eval_lit (Pos (ReifAction sel_i)) ?rho"
          by (rule pb_sum_ge_term[OF mem])
        also have "1 * eval_lit (Pos (ReifAction sel_i)) ?rho = 1"
          by (simp add: eval_lit_def rho_ReifAction)
        finally show ?thesis by simp
      qed
      show ?thesis
        unfolding eq satisfies_def reif_fwd_def
        using rho_ReifT sum_ge
        by (simp add: eval_lit_def lit_neg_def)
    next
      assume eq: "\<phi> = reif_bwd (Pos ReifT) (map (\<lambda>i. (1, Pos (ReifAction i))) [0..<length as]) 1"
      show ?thesis
        unfolding eq satisfies_def reif_bwd_def Let_def
        using rho_ReifT by (simp add: eval_lit_def lit_neg_def)
    qed
  qed

  show ?thesis
    unfolding encode_transition_def Let_def models_def
    using models_action_cs models_delta_cs models_eq_cs models_primed_ge models_sel
    unfolding models_def by auto
qed

lemma constraint_pvars_reification:
  assumes "\<phi> \<in> reification r coeffs A"
  shows "constraint_pvars \<phi> \<subseteq> {pvar_of_lit r} \<union> (pvar_of_lit ` snd ` set coeffs)"
  using assms unfolding reification_def reif_fwd_def reif_bwd_def constraint_pvars_def
  by (force simp: pvar_of_lit_lit_neg Let_def split: if_splits literal.splits)
lemma constraint_pvars_action_constraint_mem:
  "v \<in> constraint_pvars (action_constraint r a V B) \<Longrightarrow>
   v = pvar_of_lit r \<or> v = ReifDeltaCost (cost a) \<or> is_input_pvar v \<or>
   (\<exists>u. v = ReifEq u) \<or> v = ReifPrimedCostGe B"
  unfolding action_constraint_def constraint_pvars_def Let_def
  by (auto simp: pvar_of_lit_def pvar_of_lit_lit_neg is_input_pvar_def lit_neg_def
                split: literal.splits)
lemma enc_trans_pvars_not_circ:
  fixes C_\<phi> :: "'v::linorder pb_circuit"
  assumes \<phi>_in: "\<phi> \<in> encode_transition as V B"
    and extra_disj: "\<forall>v \<in> circuit_reif_pvars C_\<phi>.
         (\<forall>k. v \<noteq> ReifDeltaCost k) \<and> (\<forall>k. v \<noteq> ReifDeltaCostLower k) \<and>
         (\<forall>k. v \<noteq> ReifDeltaCostUpper k) \<and>
         (\<forall>k. v \<noteq> ReifPrimedCostGe k) \<and> v \<noteq> ReifT \<and>
         (\<forall>u. v \<noteq> ReifGeq u) \<and> (\<forall>u. v \<noteq> ReifLeq u) \<and> (\<forall>u. v \<noteq> ReifEq u) \<and> (\<forall>i. v \<noteq> ReifAction i)"
  shows "\<forall> v \<in> constraint_pvars \<phi>. (\<exists>k. v = ReifDeltaCost k) \<or> (\<exists>k. v = ReifDeltaCostLower k) \<or>
         (\<exists>k. v = ReifDeltaCostUpper k) \<or>
         (\<exists>k. v = ReifPrimedCostGe k) \<or> v = ReifT \<or>
         (\<exists>u. v = ReifGeq u) \<or> (\<exists>u. v = ReifLeq u) \<or> (\<exists>u. v = ReifEq u) \<or>
         (\<exists>i. v = ReifAction i) \<or> is_input_pvar v"
proof
  fix v assume v_in: "v \<in> constraint_pvars \<phi>"
  from \<phi>_in show "(\<exists>k. v = ReifDeltaCost k) \<or> (\<exists>k. v = ReifDeltaCostLower k) \<or>
         (\<exists>k. v = ReifDeltaCostUpper k) \<or>
         (\<exists>k. v = ReifPrimedCostGe k) \<or> v = ReifT \<or>
         (\<exists>u. v = ReifGeq u) \<or> (\<exists>u. v = ReifLeq u) \<or> (\<exists>u. v = ReifEq u) \<or>
         (\<exists>i. v = ReifAction i) \<or> is_input_pvar v"
    unfolding encode_transition_def Let_def
  proof (elim UnE)
    assume "\<phi> \<in> (\<Union>i<length as. {action_constraint (action_reifs as ! i) (as ! i) V B})"
    then obtain i where "i < length as" and \<phi>_eq: "\<phi> = action_constraint (action_reifs as ! i) (as ! i) V B"
      by auto
    with v_in show ?thesis
      using constraint_pvars_action_constraint_mem[of v "action_reifs as ! i" "as ! i" V B]
      by (auto simp: action_reifs_def pvar_of_lit_def)
  next
    assume "\<phi> \<in> (\<Union>a\<in>set as. encode_delta_cost (cost a) (bits_needed B))"
    then obtain a where a_in: "a \<in> set as" and \<phi>_eq: "\<phi> \<in> encode_delta_cost (cost a) (bits_needed B)"
      by auto
    let ?k  = "cost a"
    let ?M  = "2^(bits_needed B) - (1::nat)"
    let ?pcl  = "map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<bits_needed B]"
    let ?cl   = "map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed B]"
    let ?ncl  = "map (\<lambda>i. (2^i, Neg (CostBit i))) [0..<bits_needed B]"
    let ?ncl' = "map (\<lambda>i. (2^i, Neg (PrimedCostBit i))) [0..<bits_needed B]"
    from \<phi>_eq have disj_dc:
      "\<phi> \<in> reification (Pos (ReifDeltaCostLower ?k)) (?pcl @ ?ncl) (?k + ?M) \<or>
       \<phi> \<in> reification (Pos (ReifDeltaCostUpper ?k)) (?cl @ ?ncl') (?M - ?k) \<or>
       \<phi> \<in> reification (Pos (ReifDeltaCost ?k))
               [(1, Pos (ReifDeltaCostLower ?k)), (1, Pos (ReifDeltaCostUpper ?k))] 2"
      unfolding encode_delta_cost_def Let_def by auto
    show ?thesis using disj_dc
    proof (elim disjE)
      assume h: "\<phi> \<in> reification (Pos (ReifDeltaCostLower ?k)) (?pcl @ ?ncl) (?k + ?M)"
      have "v = ReifDeltaCostLower ?k \<or> (\<exists>i. v = PrimedCostBit i) \<or> (\<exists>i. v = CostBit i)"
        using v_in constraint_pvars_reification[OF h]
        by (auto simp: pvar_of_lit_def is_input_pvar_def split: literal.splits)
      then show ?thesis by (auto simp: is_input_pvar_def)
    next
      assume h: "\<phi> \<in> reification (Pos (ReifDeltaCostUpper ?k)) (?cl @ ?ncl') (?M - ?k)"
      have "v = ReifDeltaCostUpper ?k \<or> (\<exists>i. v = CostBit i) \<or> (\<exists>i. v = PrimedCostBit i)"
        using v_in constraint_pvars_reification[OF h]
        by (auto simp: pvar_of_lit_def is_input_pvar_def split: literal.splits)
      then show ?thesis by (auto simp: is_input_pvar_def)
    next
      assume h: "\<phi> \<in> reification (Pos (ReifDeltaCost ?k))
                       [(1, Pos (ReifDeltaCostLower ?k)), (1, Pos (ReifDeltaCostUpper ?k))] 2"
      have "v = ReifDeltaCost ?k \<or> v = ReifDeltaCostLower ?k \<or> v = ReifDeltaCostUpper ?k"
        using v_in constraint_pvars_reification[OF h]
        by (auto simp: pvar_of_lit_def split: literal.splits)
      then show ?thesis by auto
    qed
  next
    assume "\<phi> \<in> (\<Union>v\<in>V. encode_eq_var v)"
    then obtain u where u_in: "u \<in> V" and \<phi>_eq: "\<phi> \<in> encode_eq_var u"
      by auto
    from \<phi>_eq have disj6:
      "\<phi> = reif_fwd (Pos (ReifGeq (Original u))) [(1, Pos (StateVar (Original u))), (1, Neg (StateVar (Primed u)))] 1 \<or>
       \<phi> = reif_bwd (Pos (ReifGeq (Original u))) [(1, Pos (StateVar (Original u))), (1, Neg (StateVar (Primed u)))] 1 \<or>
       \<phi> = reif_fwd (Pos (ReifLeq (Original u))) [(1, Neg (StateVar (Original u))), (1, Pos (StateVar (Primed u)))] 1 \<or>
       \<phi> = reif_bwd (Pos (ReifLeq (Original u))) [(1, Neg (StateVar (Original u))), (1, Pos (StateVar (Primed u)))] 1 \<or>
       \<phi> = reif_fwd (Pos (ReifEq (Original u))) [(1, Pos (ReifLeq (Original u))), (1, Pos (ReifGeq (Original u)))] 2 \<or>
       \<phi> = reif_bwd (Pos (ReifEq (Original u))) [(1, Pos (ReifLeq (Original u))), (1, Pos (ReifGeq (Original u)))] 2"
      unfolding encode_eq_var_def reification_def by auto
    show ?thesis using disj6
    proof (elim disjE)
      assume eq: "\<phi> = reif_fwd (Pos (ReifGeq (Original u))) [(1, Pos (StateVar (Original u))), (1, Neg (StateVar (Primed u)))] 1"
      have "v = ReifGeq (Original u) \<or> v = StateVar (Original u) \<or> v = StateVar (Primed u)"
        using v_in by (auto simp: eq constraint_pvars_def reif_fwd_def pvar_of_lit_def lit_neg_def
                            split: literal.splits)
      then show ?thesis by (auto simp: is_input_pvar_def)
    next
      assume eq: "\<phi> = reif_bwd (Pos (ReifGeq (Original u))) [(1, Pos (StateVar (Original u))), (1, Neg (StateVar (Primed u)))] 1"
      have "v = ReifGeq (Original u) \<or> v = StateVar (Original u) \<or> v = StateVar (Primed u)"
        using v_in by (auto simp: eq constraint_pvars_def reif_bwd_def pvar_of_lit_def lit_neg_def
                            pvar_of_lit_lit_neg Let_def split: literal.splits)
      then show ?thesis by (auto simp: is_input_pvar_def)
    next
      assume eq: "\<phi> = reif_fwd (Pos (ReifLeq (Original u))) [(1, Neg (StateVar (Original u))), (1, Pos (StateVar (Primed u)))] 1"
      have "v = ReifLeq (Original u) \<or> v = StateVar (Original u) \<or> v = StateVar (Primed u)"
        using v_in by (auto simp: eq constraint_pvars_def reif_fwd_def pvar_of_lit_def lit_neg_def
                            split: literal.splits)
      then show ?thesis by (auto simp: is_input_pvar_def)
    next
      assume eq: "\<phi> = reif_bwd (Pos (ReifLeq (Original u))) [(1, Neg (StateVar (Original u))), (1, Pos (StateVar (Primed u)))] 1"
      have "v = ReifLeq (Original u) \<or> v = StateVar (Original u) \<or> v = StateVar (Primed u)"
        using v_in by (auto simp: eq constraint_pvars_def reif_bwd_def pvar_of_lit_def lit_neg_def
                            pvar_of_lit_lit_neg Let_def split: literal.splits)
      then show ?thesis by (auto simp: is_input_pvar_def)
    next
      assume eq: "\<phi> = reif_fwd (Pos (ReifEq (Original u))) [(1, Pos (ReifLeq (Original u))), (1, Pos (ReifGeq (Original u)))] 2"
      have "v = ReifEq (Original u) \<or> v = ReifLeq (Original u) \<or> v = ReifGeq (Original u)"
        using v_in by (auto simp: eq constraint_pvars_def reif_fwd_def pvar_of_lit_def lit_neg_def
                            split: literal.splits)
      then show ?thesis by auto
    next
      assume eq: "\<phi> = reif_bwd (Pos (ReifEq (Original u))) [(1, Pos (ReifLeq (Original u))), (1, Pos (ReifGeq (Original u)))] 2"
      have "v = ReifEq (Original u) \<or> v = ReifLeq (Original u) \<or> v = ReifGeq (Original u)"
        using v_in by (auto simp: eq constraint_pvars_def reif_bwd_def pvar_of_lit_def lit_neg_def
                            pvar_of_lit_lit_neg Let_def split: literal.splits)
      then show ?thesis by auto
    qed
  next
    assume "\<phi> \<in> encode_cost_ge_primed B"
    then have disj3:
      "\<phi> = reif_fwd (Pos (ReifPrimedCostGe B))
              (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<bits_needed B]) B \<or>
       \<phi> = reif_bwd (Pos (ReifPrimedCostGe B))
              (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<bits_needed B]) B"
      unfolding encode_cost_ge_primed_def reification_def by auto
    show ?thesis using disj3
    proof (elim disjE)
      assume eq: "\<phi> = reif_fwd (Pos (ReifPrimedCostGe B))
                       (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<bits_needed B]) B"
      have "v = ReifPrimedCostGe B \<or> (\<exists>i. v = PrimedCostBit i)"
        using v_in by (auto simp: eq constraint_pvars_def reif_fwd_def pvar_of_lit_def lit_neg_def
                            split: literal.splits)
      then show ?thesis by (auto simp: is_input_pvar_def)
    next
      assume eq: "\<phi> = reif_bwd (Pos (ReifPrimedCostGe B))
                       (map (\<lambda>i. (2^i, Pos (PrimedCostBit i))) [0..<bits_needed B]) B"
      have "v = ReifPrimedCostGe B \<or> (\<exists>i. v = PrimedCostBit i)"
        using v_in by (clarsimp simp: eq constraint_pvars_def reif_bwd_def pvar_of_lit_def lit_neg_def
                                      Let_def split: literal.splits; arith)
      then show ?thesis by (auto simp: is_input_pvar_def)
    qed
  next
    assume "\<phi> \<in> action_selection_reif (action_reifs as)"
    then have disj2_sel:
      "\<phi> = reif_fwd (Pos ReifT) (map (\<lambda>i. (1, Pos (ReifAction i))) [0..<length as]) 1 \<or>
       \<phi> = reif_bwd (Pos ReifT) (map (\<lambda>i. (1, Pos (ReifAction i))) [0..<length as]) 1"
      unfolding action_selection_reif_def action_reifs_def reification_def
      by (auto simp: o_def)
    show ?thesis using disj2_sel
    proof (elim disjE)
      assume eq: "\<phi> = reif_fwd (Pos ReifT) (map (\<lambda>i. (1, Pos (ReifAction i))) [0..<length as]) 1"
      have "v = ReifT \<or> (\<exists>i. v = ReifAction i)"
        using v_in by (auto simp: eq constraint_pvars_def reif_fwd_def pvar_of_lit_def lit_neg_def
                            split: literal.splits)
      then show ?thesis by auto
    next
      assume eq: "\<phi> = reif_bwd (Pos ReifT) (map (\<lambda>i. (1, Pos (ReifAction i))) [0..<length as]) 1"
      have "v = ReifT \<or> (\<exists>i. v = ReifAction i)"
        using v_in by (auto simp: eq constraint_pvars_def reif_bwd_def pvar_of_lit_def lit_neg_def
                            pvar_of_lit_lit_neg Let_def split: literal.splits)
      then show ?thesis by auto
    qed
  qed
qed



lemma two_state_rho_encode_cost_ge_below:
  fixes \<Pi> :: "'v::linorder strips_task"
  assumes "c < B"
  shows "models (encode_cost_ge B) (two_state_rho \<Pi> s c s' c' sel_i as)"
proof -
  let ?\<rho> = "two_state_rho \<Pi> s c s' c' sel_i as"
  let ?r = "Pos (ReifCostGe B)"
  let ?coeffs = "map (\<lambda>i. (2^i, Pos (CostBit i))) [0..<bits_needed B] :: (nat \<times> 'v var pvar literal) list"
  have r_val: "?\<rho> (ReifCostGe B) = 0"
    by (simp add: two_state_rho_def)
  have eval_r: "eval_lit ?r ?\<rho> = 0"
    by (simp add: eval_lit_def r_val)
  have eval_neg_r: "eval_lit (lit_neg ?r) ?\<rho> = 1"
    by (simp add: eval_lit_def lit_neg_def r_val)
  have cost_bits: "\<forall>i < bits_needed B. ?\<rho> (CostBit i) = (c div 2^i) mod 2"
    by (simp add: two_state_rho_def)
  have c_lt_pow: "c < 2^(bits_needed B)"
  proof -
    have "c < B" using assms .
    also have "B < 2^(bits_needed B)" by (rule bits_needed_sufficient)
    finally show ?thesis .
  qed
  have sum_eq: "pb_sum ?coeffs ?\<rho> = c"
  proof -
    have "pb_sum ?coeffs ?\<rho> = c mod 2^(bits_needed B)"
      by (rule pb_sum_cost_bits_gen[OF cost_bits])
    thus ?thesis using c_lt_pow by simp
  qed
  have sum_total: "sum_list (map fst ?coeffs) = 2^(bits_needed B) - (1 :: nat)"
    by (auto simp: sum_list_exp o_def)
  have all_01: "\<forall>v. ?\<rho> v = 0 \<or> ?\<rho> v = 1" by (rule two_state_rho_range)
  have neg_sum_eq: "pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) ?coeffs) ?\<rho>
      = 2^(bits_needed B) - 1 - c"
  proof -
    have "pb_sum ?coeffs ?\<rho> + pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) ?coeffs) ?\<rho>
          = sum_list (map fst ?coeffs)"
      using all_01 pb_sum_add_negated_gen
      by (metis (mono_tags, lifting))
    thus ?thesis using sum_eq sum_total by (metis (no_types, lifting) diff_add_inverse)
  qed
  have fwd_sound: "satisfies (reif_fwd ?r ?coeffs B) ?\<rho>"
    unfolding satisfies_def reif_fwd_def Let_def
    using eval_neg_r sum_eq by simp
  have ineq: "(2^(bits_needed B)-1) - c \<ge> 2^(bits_needed B) - B"
  proof -
    have "c+1 \<le> B" using assms by simp
    then have "2^(bits_needed B) - B \<le> 2^(bits_needed B) - (c+1)" by (simp add: diff_le_mono2)
    also have "2^(bits_needed B) - (c+1) = (2^(bits_needed B)-1) - c"
      by simp
    finally show ?thesis .
  qed
  have M_val: "sum_list (map fst ?coeffs) + 1 - B = 2^(bits_needed B) - B"
    using sum_total by simp
  have bwd_sound: "satisfies (reif_bwd ?r ?coeffs B) ?\<rho>"
  proof -
    have snd_val: "snd (reif_bwd ?r ?coeffs B) = 2^(bits_needed B) - B"
      unfolding reif_bwd_def Let_def snd_conv
      using M_val by simp
    have fst_val: "pb_sum (fst (reif_bwd ?r ?coeffs B)) ?\<rho> = 2^(bits_needed B) - 1 - c"
    proof -
      have "pb_sum (fst (reif_bwd ?r ?coeffs B)) ?\<rho> =
            pb_sum ([(sum_list (map fst ?coeffs) + 1 - B, ?r)] @ map (\<lambda>(a,l). (a, lit_neg l)) ?coeffs) ?\<rho>"
        by (auto simp: reif_bwd_def Let_def o_def)
      also have "\<dots> = (sum_list (map fst ?coeffs) + 1 - B) * eval_lit ?r ?\<rho> + pb_sum (map (\<lambda>(a,l). (a, lit_neg l)) ?coeffs) ?\<rho>"
        by (simp add: pb_sum_append eval_r)
      also have "\<dots> = 0 + pb_sum (map (\<lambda>(a,l). (a, lit_neg l)) ?coeffs) ?\<rho>"
        using eval_r by simp
      also have "\<dots> = 2^(bits_needed B) - 1 - c"
        using neg_sum_eq by simp
      finally show ?thesis .
    qed
    show ?thesis
      unfolding satisfies_def
      using fst_val ineq snd_val by force
  qed
  show ?thesis
    unfolding models_def encode_cost_ge_def reification_def
    using fwd_sound bwd_sound by auto
qed

lemma lift_to_var_map_pvar_orig:
  assumes "\<And>i. p \<noteq> PrimedCostBit i"
  shows "lift_to_var rho (map_pvar Original p) = rho p"
  by (cases p; auto simp: lift_to_var_def assms split: var.splits)

lemma eval_lit_map_pvar_lift_to_var_orig:
  assumes "\<forall>i. pvar_of_lit l \<noteq> PrimedCostBit i"
  shows "eval_lit (map_literal (map_pvar Original) l) (lift_to_var rho) = eval_lit l rho"
  using assms
  by (cases l; simp add: eval_lit_def lift_to_var_map_pvar_orig pvar_of_lit_def)

lemma eval_lit_neg_lit_map_pvar_lift_to_var_orig:
  assumes "\<forall>i. pvar_of_lit l \<noteq> PrimedCostBit i"
  shows "eval_lit (lit_neg (map_literal (map_pvar Original) l)) (lift_to_var rho) = eval_lit (lit_neg l) rho"
  using assms
  by (cases l; simp add: eval_lit_def lift_to_var_map_pvar_orig pvar_of_lit_def lit_neg_def)

lemma lift_to_var_primed_pvar_map:
  assumes "\<And>i. p \<noteq> PrimedCostBit i"
  shows "lift_to_var rho (primed_pvar_map p) = rho p"
  by (cases p; auto simp: lift_to_var_def primed_pvar_map_def assms split: var.splits)

lemma eval_lit_primed_pvar_map_lift_to_var:
  assumes "\<forall>i. pvar_of_lit l \<noteq> PrimedCostBit i"
  shows "eval_lit (map_literal primed_pvar_map l) (lift_to_var rho) = eval_lit l rho"
  using assms
  by (cases l; simp add: eval_lit_def lift_to_var_primed_pvar_map pvar_of_lit_def)

lemma pb_sum_map_literal_lift_to_var_orig:
  assumes no_pcb: "\<forall>(a, l) \<in> set cs. \<forall>i. pvar_of_lit l \<noteq> PrimedCostBit i"
  shows "pb_sum (map (\<lambda>(a, l). (a, map_literal (map_pvar Original) l)) cs) (lift_to_var rho) = pb_sum cs rho"
  using assms
  by (induct cs) (auto simp: eval_lit_map_pvar_lift_to_var_orig)

lemma pb_sum_lit_neg_map_literal_lift_to_var_orig:
  assumes no_pcb: "\<forall>(a, l) \<in> set cs. \<forall>i. pvar_of_lit l \<noteq> PrimedCostBit i"
  shows "pb_sum (map (\<lambda>al. (fst al, lit_neg (map_literal (map_pvar Original) (snd al)))) cs) (lift_to_var rho) =
    pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) cs) rho"
  using assms
  by (induct cs) (auto simp: eval_lit_neg_lit_map_pvar_lift_to_var_orig)

lemma pb_sum_map_literal_lift_to_var_primed:
  assumes no_pcb: "\<forall>(a, l) \<in> set cs. \<forall>i. pvar_of_lit l \<noteq> PrimedCostBit i"
  shows "pb_sum (map (\<lambda>(a, l). (a, map_literal primed_pvar_map l)) cs) (lift_to_var rho) = pb_sum cs rho"
  using assms
proof (induct cs)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  obtain a l where x: "x = (a, l)" by force
  have no_pcb_l: "\<forall>i. pvar_of_lit l \<noteq> PrimedCostBit i"
    using Cons.prems unfolding x by auto
  have "eval_lit (map_literal primed_pvar_map l) (lift_to_var rho) = eval_lit l rho"
    using no_pcb_l by (rule eval_lit_primed_pvar_map_lift_to_var)
  then have hd: "a * eval_lit (map_literal primed_pvar_map l) (lift_to_var rho) = a * eval_lit l rho" by simp
  have IH: "pb_sum (map (\<lambda>(a, l). (a, map_literal primed_pvar_map l)) xs) (lift_to_var rho) = pb_sum xs rho"
    using Cons.prems by (intro Cons.hyps) auto
  show ?case by (simp add: x hd IH)
qed

lemma eval_lit_neg_lit_primed_pvar_map_lift_to_var:
  assumes "\<forall>i. pvar_of_lit l \<noteq> PrimedCostBit i"
  shows "eval_lit (lit_neg (map_literal primed_pvar_map l)) (lift_to_var rho) = eval_lit (lit_neg l) rho"
  using assms
  by (cases l; simp add: eval_lit_def lift_to_var_primed_pvar_map pvar_of_lit_def lit_neg_def)

lemma pb_sum_lit_neg_map_literal_lift_to_var_primed:
  assumes no_pcb: "\<forall>(a, l) \<in> set cs. \<forall>i. pvar_of_lit l \<noteq> PrimedCostBit i"
  shows "pb_sum (map (\<lambda>al. (fst al, lit_neg (map_literal primed_pvar_map (snd al)))) cs) (lift_to_var rho) =
    pb_sum (map (\<lambda>(a, l). (a, lit_neg l)) cs) rho"
  using assms
  by (induct cs) (auto simp: eval_lit_neg_lit_primed_pvar_map_lift_to_var)

lemma lift_to_var_models_circuit_constraints_orig:
  assumes "models (circuit_constraints C) rho"
    and no_pcb_cs: "\<forall>(r, cs, A) \<in> set (fst C). \<forall>v \<in> pvar_of_lit ` snd ` set cs. \<forall>i. v \<noteq> PrimedCostBit i"
    and no_pcb_r: "\<forall>(r, cs, A) \<in> set (fst C). \<forall>i. pvar_of_lit r \<noteq> PrimedCostBit i"
  shows "models (circuit_constraints (lift_circuit (map_pvar Original) C)) (lift_to_var rho)"
proof (unfold models_def, intro ballI)
  fix \<psi> assume "\<psi> \<in> circuit_constraints (lift_circuit (map_pvar Original) C)"
  then obtain r cs A where rcs: "(r, cs, A) \<in> set (fst C)"
    and \<psi>_reif: "\<psi> \<in> reification (map_literal (map_pvar Original) r)
                   (map (\<lambda>(a,l). (a, map_literal (map_pvar Original) l)) cs) A"
    unfolding circuit_constraints_def lift_circuit_def Let_def
    by (force simp: image_iff split_beta)
  have reif_sat: "\<forall>\<phi> \<in> reification r cs A. satisfies \<phi> rho"
    using assms(1) rcs unfolding models_def circuit_constraints_def by blast
  have no_primed_cs: "\<forall>(a, l) \<in> set cs. \<forall>i. pvar_of_lit l \<noteq> PrimedCostBit i"
    using no_pcb_cs rcs by (force simp: image_iff)
  have no_primed_r: "\<forall>i. pvar_of_lit r \<noteq> PrimedCostBit i"
    using no_pcb_r rcs by blast
  have "satisfies \<psi> (lift_to_var rho)"
  proof (cases "\<psi> = reif_fwd (map_literal (map_pvar Original) r)
                             (map (\<lambda>(a,l). (a, map_literal (map_pvar Original) l)) cs) A")
    case True
    then have \<psi>_fwd: "\<psi> = reif_fwd (map_literal (map_pvar Original) r)
                          (map (\<lambda>(a,l). (a, map_literal (map_pvar Original) l)) cs) A" .
    have "pb_sum (fst \<psi>) (lift_to_var rho) = pb_sum (fst (reif_fwd r cs A)) rho"
      unfolding \<psi>_fwd reif_fwd_def using no_primed_r
      by (auto simp: pb_sum_append pb_sum_map_literal_lift_to_var_orig no_primed_cs
                     eval_lit_neg_lit_map_pvar_lift_to_var_orig)
    moreover have "snd \<psi> = snd (reif_fwd r cs A)"
      unfolding \<psi>_fwd reif_fwd_def by simp
    ultimately show ?thesis
      using reif_sat[THEN ballE, where x = "reif_fwd r cs A"]
      by (force simp: satisfies_def reification_def)
  next
    case False
    then have \<psi>_bwd: "\<psi> = reif_bwd (map_literal (map_pvar Original) r)
                          (map (\<lambda>(a,l). (a, map_literal (map_pvar Original) l)) cs) A"
      using \<psi>_reif unfolding reification_def by auto
    have "pb_sum (fst \<psi>) (lift_to_var rho) = pb_sum (fst (reif_bwd r cs A)) rho"
      unfolding \<psi>_bwd reif_bwd_def Let_def using no_primed_r no_primed_cs
      by (auto simp: pb_sum_append split_beta o_def
        pb_sum_map_literal_lift_to_var_orig pb_sum_lit_neg_map_literal_lift_to_var_orig
        eval_lit_map_pvar_lift_to_var_orig eval_lit_neg_lit_map_pvar_lift_to_var_orig)
    moreover have "snd \<psi> = snd (reif_bwd r cs A)"
      unfolding \<psi>_bwd reif_bwd_def Let_def by (simp add: o_def split_beta)
    ultimately show ?thesis
      using reif_sat[THEN ballE, where x = "reif_bwd r cs A"]
      by (force simp: satisfies_def reification_def)
  qed
  then show "satisfies \<psi> (lift_to_var rho)" .
qed

lemma lift_to_var_models_circuit_constraints_primed:
  assumes "models (circuit_constraints C) rho"
    and no_pcb_cs: "\<forall>(r, cs, A) \<in> set (fst C). \<forall>v \<in> pvar_of_lit ` snd ` set cs. \<forall>i. v \<noteq> PrimedCostBit i"
    and no_pcb_r: "\<forall>(r, cs, A) \<in> set (fst C). \<forall>i. pvar_of_lit r \<noteq> PrimedCostBit i"
  shows "models (circuit_constraints (lift_circuit primed_pvar_map C)) (lift_to_var rho)"
proof (unfold models_def, intro ballI)
  fix \<psi> assume "\<psi> \<in> circuit_constraints (lift_circuit primed_pvar_map C)"
  then obtain r cs A where rcs: "(r, cs, A) \<in> set (fst C)"
    and \<psi>_reif: "\<psi> \<in> reification (map_literal primed_pvar_map r)
                   (map (\<lambda>(a,l). (a, map_literal primed_pvar_map l)) cs) A"
    unfolding circuit_constraints_def lift_circuit_def Let_def
    by (force simp: image_iff split_beta)
  have reif_sat: "\<forall>\<phi> \<in> reification r cs A. satisfies \<phi> rho"
    using assms(1) rcs unfolding models_def circuit_constraints_def by blast
  have no_primed_cs: "\<forall>(a, l) \<in> set cs. \<forall>i. pvar_of_lit l \<noteq> PrimedCostBit i"
    using no_pcb_cs rcs by (force simp: image_iff)
  have no_primed_r: "\<forall>i. pvar_of_lit r \<noteq> PrimedCostBit i"
    using no_pcb_r rcs by blast
  have "satisfies \<psi> (lift_to_var rho)"
  proof (cases "\<psi> = reif_fwd (map_literal primed_pvar_map r)
                             (map (\<lambda>(a,l). (a, map_literal primed_pvar_map l)) cs) A")
    case True
    then have \<psi>_fwd: "\<psi> = reif_fwd (map_literal primed_pvar_map r)
                          (map (\<lambda>(a,l). (a, map_literal primed_pvar_map l)) cs) A" .
    have "pb_sum (fst \<psi>) (lift_to_var rho) = pb_sum (fst (reif_fwd r cs A)) rho"
        unfolding \<psi>_fwd reif_fwd_def using no_primed_r no_primed_cs
        by (auto simp: pb_sum_append pb_sum_map_literal_lift_to_var_primed
                       eval_lit_primed_pvar_map_lift_to_var
                       eval_lit_neg_lit_primed_pvar_map_lift_to_var)
    moreover have "snd \<psi> = snd (reif_fwd r cs A)"
      unfolding \<psi>_fwd reif_fwd_def by simp
    ultimately show ?thesis
      using reif_sat[THEN ballE, where x = "reif_fwd r cs A"]
      by (force simp: satisfies_def reification_def)
  next
    case False
    then have \<psi>_bwd: "\<psi> = reif_bwd (map_literal primed_pvar_map r)
                          (map (\<lambda>(a,l). (a, map_literal primed_pvar_map l)) cs) A"
      using \<psi>_reif unfolding reification_def by auto      have "pb_sum (fst \<psi>) (lift_to_var rho) = pb_sum (fst (reif_bwd r cs A)) rho"
        unfolding \<psi>_bwd reif_bwd_def Let_def using no_primed_r no_primed_cs
        by (auto simp: pb_sum_append split_beta o_def
          pb_sum_map_literal_lift_to_var_primed
          pb_sum_lit_neg_map_literal_lift_to_var_primed
          eval_lit_primed_pvar_map_lift_to_var)
    moreover have "snd \<psi> = snd (reif_bwd r cs A)"
      unfolding \<psi>_bwd reif_bwd_def Let_def by (simp add: o_def split_beta)
    ultimately show ?thesis
      using reif_sat[THEN ballE, where x = "reif_bwd r cs A"]
      by (force simp: satisfies_def reification_def)
  qed
  then show "satisfies \<psi> (lift_to_var rho)" .
qed

lemma pvar_of_lit_map_literal_gen: "pvar_of_lit (map_literal f l) = f (pvar_of_lit l)"
  by (cases l; simp add: pvar_of_lit_def)

lemma lift_circuit_reif_eq[simp]:
  "circuit_reif_pvars (lift_circuit f C) = f ` circuit_reif_pvars C"
  unfolding circuit_reif_pvars_def lift_circuit_def
  by (force simp: pvar_of_lit_def image_iff split_beta split: prod.splits literal.splits)

lemma orig_reif_eq[simp]:
  "circuit_reif_pvars (orig_circuit C) = map_pvar Original ` circuit_reif_pvars C"
  unfolding orig_circuit_def by simp

lemma primed_reif_eq[simp]:
  "circuit_reif_pvars (primed_circuit C) = primed_pvar_map ` circuit_reif_pvars C"
  unfolding primed_circuit_def by simp

lemma snd_lift_circuit[simp]: "snd (lift_circuit f C) = map_literal f (snd C)"
  by (simp add: lift_circuit_def Let_def split: prod.split)

lemma snd_orig_circuit[simp]: "snd (orig_circuit C) = map_literal (map_pvar Original) (snd C)"
  unfolding orig_circuit_def by simp

lemma in_M_step:
  fixes \<Pi> :: "'v::linorder strips_task" and C_\<phi> :: "'v pb_circuit"
  assumes in_M_s: "in_M C_\<phi> \<Pi> s c"
    and appl: "applicable a s"
    and a_mem: "a \<in> acts \<Pi>"
    and as_cover_acts: "acts \<Pi> \<subseteq> set as"
    and wf: "wf_circuit C_\<phi>"
    and circ_vars: "\<forall>(r, \<phi>) \<in> set (fst C_\<phi>). \<forall>v \<in> constraint_pvars \<phi>. is_input_pvar v \<or> v \<in> circuit_reif_pvars C_\<phi>"
    and no_pcb: "\<forall>(r, \<phi>) \<in> set (fst C_\<phi>). \<forall>v \<in> constraint_pvars \<phi>. \<forall>i. v \<noteq> PrimedCostBit i"
    and disjoint: "\<forall>v \<in> circuit_reif_pvars C_\<phi>. \<not> is_input_pvar v \<and> v \<noteq> ReifI \<and> (\<forall>k. v \<noteq> ReifCostGe k)"
    and extra_disj: "\<forall>v \<in> circuit_reif_pvars C_\<phi>.
         (\<forall>k. v \<noteq> ReifDeltaCost k) \<and> (\<forall>k. v \<noteq> ReifDeltaCostLower k) \<and>
         (\<forall>k. v \<noteq> ReifDeltaCostUpper k) \<and>
         (\<forall>k. v \<noteq> ReifPrimedCostGe k) \<and> v \<noteq> ReifT \<and>
         (\<forall>u. v \<noteq> ReifGeq u) \<and> (\<forall>u. v \<noteq> ReifLeq u) \<and> (\<forall>u. v \<noteq> ReifEq u) \<and> (\<forall>i. v \<noteq> ReifAction i) \<and>
         (\<forall>i. v \<noteq> PrimedCostBit i) \<and> v \<noteq> ReifG"
    and realiz: "\<forall> (base :: 'v pvar \<Rightarrow> nat). (\<forall> v. base v = 0 \<or> base v = 1) \<longrightarrow> (\<exists> rho.
        models (circuit_constraints C_\<phi>) rho
        \<and> (\<forall> v. is_input_pvar v \<longrightarrow> rho v = base v)
        \<and> (\<forall> v. rho v = 0 \<or> rho v = 1))"
    and fin_V: "finite V"
    and pre_sub: "\<forall> a \<in> set as. pre a \<subseteq> V"
    and add_sub: "\<forall> a \<in> set as. add a \<subseteq> V"
    and del_sub: "\<forall> a \<in> set as. del a \<subseteq> V"
    and c_lt_B: "c + cost a < B"
    and cpr_ind: "cpr_derives
      (encode_transition as V B \<union> circuit_constraints (orig_circuit C_\<phi>) \<union>
       circuit_constraints (primed_circuit C_\<phi>) \<union> encode_cost_ge B \<union>
       {unit_clause (snd (orig_circuit C_\<phi>)), unit_clause (Pos ReifT)})
      (unit_clause (snd (primed_circuit C_\<phi>)))"
  shows "in_M C_\<phi> \<Pi> (successor a s) (c + cost a)"
proof -
  let ?s' = "successor a s"
  let ?c' = "c + cost a"
  obtain sel_i where sel_i_lt: "sel_i < length as" and as_sel: "as ! sel_i = a"
    using a_mem as_cover_acts by (metis in_set_conv_nth subset_eq)

  let ?rho_trans = "two_state_rho \<Pi> s c ?s' ?c' sel_i as"

  have rho_trans_01: "\<forall>v. ?rho_trans v = 0 \<or> ?rho_trans v = 1"
    by (rule two_state_rho_range)

  have appl_as_sel: "applicable (as ! sel_i) s"
    by (simp add: as_sel appl)
  have rho_trans_sat: "models (encode_transition as V B) ?rho_trans"
  proof (rule encode_transition_sound)
    show "finite V" by (rule fin_V)
    show "sel_i < length as" by (rule sel_i_lt)
    show "applicable (as ! sel_i) s" by (simp add: as_sel appl)
    show "successor a s = successor (as ! sel_i) s" by (simp add: as_sel)
    show "c + cost a = c + cost (as ! sel_i)" by (simp add: as_sel)
    show "c + cost a < B" by (rule c_lt_B)    show "pre (as ! sel_i) \<subseteq> V"
      by (metis pre_sub sel_i_lt in_set_conv_nth)
    show "add (as ! sel_i) \<subseteq> V"
      by (metis add_sub sel_i_lt in_set_conv_nth)
    show "del (as ! sel_i) \<subseteq> V"
      by (metis del_sub sel_i_lt in_set_conv_nth)
  qed

  have c_lt_B': "c < B"
    using c_lt_B by (simp add: trans_less_add2)
  have rho_trans_cost_ge: "models (encode_cost_ge B) ?rho_trans"
    by (rule two_state_rho_encode_cost_ge_below[OF c_lt_B'])

  have rho_trans_ReifT: "satisfies (unit_clause (Pos ReifT)) ?rho_trans"
    by (simp add: unit_clause_def satisfies_def eval_lit_def two_state_rho_def)

  obtain rho_circ where
    rho_circ_sat: "models (circuit_constraints C_\<phi>) rho_circ"
    and rho_circ_out: "eval_lit (snd C_\<phi>) rho_circ = 1"
    and rho_circ_inp: "\<forall>v. is_input_pvar v \<longrightarrow> rho_circ v = state_rho \<Pi> s c v"
    and rho_circ_01: "\<forall>v. rho_circ v = 0 \<or> rho_circ v = 1"
    using in_M_s
    by (auto simp: in_M_def state_rho_def is_input_pvar_def split: pvar.splits)

  let ?base_s' = "state_rho \<Pi> ?s' ?c'"
  have base_s'_01: "\<forall>v. ?base_s' v = 0 \<or> ?base_s' v = 1" using state_rho_01 by blast
  obtain rho_circ' where
    rho_circ'_sat: "models (circuit_constraints C_\<phi>) rho_circ'"
    and rho_circ'_inp: "\<forall>v. is_input_pvar v \<longrightarrow> rho_circ' v = ?base_s' v"
    and rho_circ'_01: "\<forall>v. rho_circ' v = 0 \<or> rho_circ' v = 1"
    using realiz base_s'_01 by blast

  let ?base_s'_old_c = "state_rho \<Pi> ?s' c"
  have base_s'_old_c_01: "\<forall>v. ?base_s'_old_c v = 0 \<or> ?base_s'_old_c v = 1"
    using state_rho_01 by blast
  obtain rho_circ'' where
    rho_circ''_sat: "models (circuit_constraints C_\<phi>) rho_circ''"
    and rho_circ''_inp: "\<forall>v. is_input_pvar v \<longrightarrow> rho_circ'' v = ?base_s'_old_c v"
    and rho_circ''_01: "\<forall>v. rho_circ'' v = 0 \<or> rho_circ'' v = 1"
    using realiz base_s'_old_c_01 by blast

  let ?rho_combined = "\<lambda>x. if x \<in> circuit_reif_pvars (orig_circuit C_\<phi>) then lift_to_var rho_circ x else if x \<in> circuit_reif_pvars (primed_circuit C_\<phi>) then lift_to_var rho_circ' x else ?rho_trans x"

  have circ_vars_orig:
    "\<forall>\<phi> \<in> circuit_constraints (orig_circuit C_\<phi>).
       \<forall>v \<in> constraint_pvars \<phi>. v \<in> circuit_reif_pvars (orig_circuit C_\<phi>) \<or>
         (\<exists>w. v = StateVar (Original w)) \<or> (\<exists>i. v = CostBit i)"
    using circ_vars no_pcb
  proof (intro ballI allI impI)
    fix \<phi> v
    assume \<phi>in: "\<phi> \<in> circuit_constraints (orig_circuit C_\<phi>)"
      and vin: "v \<in> constraint_pvars \<phi>"
    from \<phi>in obtain r0 cs0 A0 where
        r0_in: "(r0, cs0, A0) \<in> set (fst C_\<phi>)" and
        \<phi>_reif: "\<phi> \<in> reification (map_literal (map_pvar Original) r0)
                      (map (\<lambda>(a,l). (a, map_literal (map_pvar Original) l)) cs0) A0"
      unfolding circuit_constraints_def orig_circuit_def lift_circuit_def
      by (auto simp: split_beta)
    have r0_in_reif: "pvar_of_lit r0 \<in> circuit_reif_pvars C_\<phi>"
      unfolding circuit_reif_pvars_def using r0_in by (force simp: image_iff split_beta)
    have v_sub: "v \<in> {map_pvar Original (pvar_of_lit r0)} \<union>
                     map_pvar Original ` (pvar_of_lit ` snd ` set cs0)"
      using constraint_pvars_reification[OF \<phi>_reif] vin
      by (force simp: pvar_of_lit_map_literal_gen image_iff split_beta)
    show "v \<in> circuit_reif_pvars (orig_circuit C_\<phi>) \<or>
          (\<exists>w. v = StateVar (Original w)) \<or> (\<exists>i. v = CostBit i)"
    proof (cases "v = map_pvar Original (pvar_of_lit r0)")
      case True
      then have "v \<in> map_pvar Original ` circuit_reif_pvars C_\<phi>"
        using r0_in_reif by blast
      thus ?thesis using orig_reif_eq by auto
    next
      case False
      with v_sub obtain v0 where v0_in_cs: "v0 \<in> pvar_of_lit ` snd ` set cs0"
        and v_eq: "v = map_pvar Original v0" by auto
      have v0_cpv: "v0 \<in> constraint_pvars (cs0, A0)"
        using v0_in_cs unfolding constraint_pvars_def by simp
      from circ_vars r0_in v0_cpv have "is_input_pvar v0 \<or> v0 \<in> circuit_reif_pvars C_\<phi>"
        by blast
      thus ?thesis
      proof (elim disjE)
        assume "is_input_pvar v0"
        then consider (sv) "\<exists>w. v0 = StateVar w" | (cb) "\<exists>i. v0 = CostBit i" | (pcb) "\<exists>i. v0 = PrimedCostBit i"
          unfolding is_input_pvar_def by blast
        thus ?thesis
        proof cases
          case sv
          then obtain w where "v0 = StateVar w" by blast
          hence "v = StateVar (Original w)" using v_eq by simp
          thus ?thesis by blast
        next
          case cb
          then obtain i where "v0 = CostBit i" by blast
          hence "v = CostBit i" using v_eq by simp
          thus ?thesis by blast
        next
          case pcb
          then obtain i where "v0 = PrimedCostBit i" by blast
          with no_pcb r0_in v0_cpv show ?thesis by blast
        qed
      next
        assume "v0 \<in> circuit_reif_pvars C_\<phi>"
        then have "map_pvar Original v0 \<in> circuit_reif_pvars (orig_circuit C_\<phi>)"
          using orig_reif_eq by auto
        thus ?thesis using v_eq by blast
      qed
    qed
  qed

  have comb_circ: "models (circuit_constraints (orig_circuit C_\<phi>)) ?rho_combined"
  proof -
    have lv_sat: "models (circuit_constraints (orig_circuit C_\<phi>)) (lift_to_var rho_circ)"
      using lift_to_var_models_circuit_constraints_orig[OF rho_circ_sat] no_pcb disjoint
      unfolding orig_circuit_def by (auto simp: split_beta constraint_pvars_def is_input_pvar_def circuit_reif_pvars_def)
    show ?thesis
    proof (unfold models_def, intro ballI)
      fix \<psi> assume \<psi>in: "\<psi> \<in> circuit_constraints (orig_circuit C_\<phi>)"
      have "satisfies \<psi> (lift_to_var rho_circ)"
        using lv_sat \<psi>in unfolding models_def by auto
      moreover have "\<forall>v \<in> constraint_pvars \<psi>. ?rho_combined v = lift_to_var rho_circ v"
      proof (intro ballI)
        fix v assume "v \<in> constraint_pvars \<psi>"
        with \<psi>in have "v \<in> circuit_reif_pvars (orig_circuit C_\<phi>) \<or>
                       (\<exists>w. v = StateVar (Original w)) \<or> (\<exists>i. v = CostBit i)"
          using circ_vars_orig by blast
        thus "?rho_combined v = lift_to_var rho_circ v"
        proof (elim disjE exE)
          assume "v \<in> circuit_reif_pvars (orig_circuit C_\<phi>)"
          thus ?thesis by simp
        next
          fix w assume "v = StateVar (Original w)"
          have sv_not_orig: "StateVar (Original w) \<notin> circuit_reif_pvars (orig_circuit C_\<phi>)"
          proof
            assume "StateVar (Original w) \<in> circuit_reif_pvars (orig_circuit C_\<phi>)"
            then have "StateVar w \<in> circuit_reif_pvars C_\<phi>"
              using orig_reif_eq
            proof (auto simp: image_iff)
              fix x assume "x \<in> circuit_reif_pvars C_\<phi>"
                and "StateVar (Original w) = map_pvar Original x"
              thus "StateVar w \<in> circuit_reif_pvars C_\<phi>"
                by (cases x; auto)
            qed
            then have sv_not_inp: "\<not> is_input_pvar (StateVar w)"
              using disjoint by (fast dest!: bspec)
            then have "is_input_pvar (StateVar w)"
              unfolding is_input_pvar_def by auto
            then show False using sv_not_inp by blast
          qed
          have sv_not_primed: "StateVar (Original w) \<notin> circuit_reif_pvars (primed_circuit C_\<phi>)"
          proof
            assume "StateVar (Original w) \<in> circuit_reif_pvars (primed_circuit C_\<phi>)"
            then obtain v where "v \<in> circuit_reif_pvars C_\<phi>"
              and "primed_pvar_map v = StateVar (Original w)"
              using primed_reif_eq by auto
            thus False by (cases v; simp add: primed_pvar_map_def split: var.splits)
          qed
          have "?rho_combined (StateVar (Original w)) = ?rho_trans (StateVar (Original w))"
            using sv_not_orig sv_not_primed by simp
          also have "... = (if w \<in> s then 1 else 0)"
            by (simp add: two_state_rho_def)
          also have "... = rho_circ (StateVar w)"
            using rho_circ_inp by (auto simp: is_input_pvar_def state_rho_def)
          also have "... = lift_to_var rho_circ (StateVar (Original w))"
            by (simp add: lift_to_var_def)
          finally show ?thesis unfolding `v = StateVar (Original w)` .
        next
          fix i assume "v = CostBit i"
          have cb_not_orig: "CostBit i \<notin> circuit_reif_pvars (orig_circuit C_\<phi>)"
            by (smt (verit, ccfv_threshold) disjoint image_iff is_input_pvar_def orig_reif_eq
                map_pvar_Original_inj pvar.map(2))
          have cb_not_primed: "CostBit i \<notin> circuit_reif_pvars (primed_circuit C_\<phi>)"
          proof
            assume "CostBit i \<in> circuit_reif_pvars (primed_circuit C_\<phi>)"
            then obtain v where "v \<in> circuit_reif_pvars C_\<phi>"
              and "primed_pvar_map v = CostBit i"
              using primed_reif_eq by auto
            thus False by (cases v; simp add: primed_pvar_map_def split: pvar.splits var.splits)
          qed
          have "?rho_combined (CostBit i) = ?rho_trans (CostBit i)"
            using cb_not_orig cb_not_primed by simp
          also have "... = (c div 2^i) mod 2"
            by (simp add: two_state_rho_def)
          also have "... = rho_circ (CostBit i)"
            using rho_circ_inp by (auto simp: is_input_pvar_def state_rho_def)
          also have "... = lift_to_var rho_circ (CostBit i)"
            by (simp add: lift_to_var_def)
          finally show ?thesis unfolding `v = CostBit i` .
        qed
      qed
      ultimately show "satisfies \<psi> ?rho_combined"
        using satisfies_cong by fast
    qed
  qed

  have comb_primed_circ: "models (circuit_constraints (primed_circuit C_\<phi>)) ?rho_combined"
  proof -
    have lv_sat': "models (circuit_constraints (primed_circuit C_\<phi>)) (lift_to_var rho_circ')"
      using lift_to_var_models_circuit_constraints_primed[OF rho_circ'_sat] no_pcb disjoint
      unfolding primed_circuit_def by (auto simp: split_beta constraint_pvars_def is_input_pvar_def circuit_reif_pvars_def)
    show ?thesis
    proof (unfold models_def, intro ballI)
      fix \<psi> assume \<psi>in: "\<psi> \<in> circuit_constraints (primed_circuit C_\<phi>)"
      have "satisfies \<psi> (lift_to_var rho_circ')"
        using lv_sat' \<psi>in unfolding models_def by auto
      moreover have "\<forall>v \<in> constraint_pvars \<psi>. ?rho_combined v = lift_to_var rho_circ' v"
      proof (intro ballI)
        fix v assume "v \<in> constraint_pvars \<psi>"
        from \<psi>in obtain r0 cs0 A0 where
            r0_in: "(r0, cs0, A0) \<in> set (fst C_\<phi>)"
            and \<psi>_reif: "\<psi> \<in> reification (map_literal primed_pvar_map r0)
                              (map (\<lambda>(a,l). (a, map_literal primed_pvar_map l)) cs0) A0"
          unfolding circuit_constraints_def primed_circuit_def lift_circuit_def
          by (auto simp: split_beta)
        have r0_in_reif: "pvar_of_lit r0 \<in> circuit_reif_pvars C_\<phi>"
          unfolding circuit_reif_pvars_def using r0_in by (force simp: image_iff split_beta)
        have psi_pvars_sub: "constraint_pvars \<psi> \<subseteq> primed_pvar_map ` ({pvar_of_lit r0} \<union> constraint_pvars (cs0, A0))"
          using constraint_pvars_reification[OF \<psi>_reif]
          by (force simp: pvar_of_lit_map_literal_gen image_iff split_beta constraint_pvars_def)
        obtain u where u_in: "u \<in> {pvar_of_lit r0} \<union> constraint_pvars (cs0, A0)"
          and v_def: "v = primed_pvar_map u"
          using psi_pvars_sub `v \<in> constraint_pvars \<psi>` by blast

        have "?rho_combined v = lift_to_var rho_circ' v"
        proof (cases "v \<in> circuit_reif_pvars (primed_circuit C_\<phi>)")
          case True
          have u_in_reif: "u \<in> circuit_reif_pvars C_\<phi>"
          proof (rule ccontr)
            assume "u \<notin> circuit_reif_pvars C_\<phi>"
            have "u \<in> constraint_pvars (cs0, A0)" using u_in r0_in_reif `u \<notin> circuit_reif_pvars C_\<phi>` by blast
            with circ_vars r0_in `u \<notin> circuit_reif_pvars C_\<phi>` have "is_input_pvar u" by blast
            with True primed_reif_eq v_def show False
            proof (cases u)
              case (StateVar w)
              with `v \<in> circuit_reif_pvars (primed_circuit C_\<phi>)` primed_reif_eq v_def
              obtain x where "x \<in> circuit_reif_pvars C_\<phi>" "StateVar (Primed w) = primed_pvar_map x"
                by (auto simp: image_iff)
              with disjoint have "\<not> is_input_pvar x" by blast
              with `StateVar (Primed w) = primed_pvar_map x` show False
                by (cases x; simp_all add: is_input_pvar_def primed_pvar_map_def split: var.splits)
            next
              case (CostBit i)
              with `v \<in> circuit_reif_pvars (primed_circuit C_\<phi>)` primed_reif_eq v_def
              obtain x where "x \<in> circuit_reif_pvars C_\<phi>" "PrimedCostBit i = primed_pvar_map x"
                by (auto simp: image_iff)
              with disjoint have "\<not> is_input_pvar x" by blast
              with `PrimedCostBit i = primed_pvar_map x` show False
                by (cases x; simp_all add: is_input_pvar_def primed_pvar_map_def)
            next
              case (PrimedCostBit i)
              with `v \<in> circuit_reif_pvars (primed_circuit C_\<phi>)` primed_reif_eq v_def
              obtain x where "x \<in> circuit_reif_pvars C_\<phi>" "PrimedCostBit i = primed_pvar_map x"
                by (auto simp: image_iff)
              with disjoint have "\<not> is_input_pvar x" by blast
              with `PrimedCostBit i = primed_pvar_map x` show False
                by (cases x; simp_all add: is_input_pvar_def primed_pvar_map_def)
            qed (simp_all add: is_input_pvar_def)
          qed
          have v_not_in_orig: "v \<notin> circuit_reif_pvars (orig_circuit C_\<phi>)"
          proof
            assume "v \<in> circuit_reif_pvars (orig_circuit C_\<phi>)"
            with orig_reif_eq v_def obtain u' where "u' \<in> circuit_reif_pvars C_\<phi>"
              and eq: "map_pvar Original u' = primed_pvar_map u"
              by (auto simp: image_iff)
            from disjoint extra_disj u_in_reif
            have "\<not> is_input_pvar u" "u \<noteq> ReifI" "\<forall>k. u \<noteq> ReifCostGe k"
                 "u \<noteq> ReifG" "u \<noteq> ReifT"
                 "\<forall>k. u \<noteq> ReifDeltaCost k" "\<forall>k. u \<noteq> ReifDeltaCostLower k"
                 "\<forall>k. u \<noteq> ReifDeltaCostUpper k"
                 "\<forall>k. u \<noteq> ReifPrimedCostGe k"
                 "\<forall>y. u \<noteq> ReifGeq y" "\<forall>y. u \<noteq> ReifLeq y" "\<forall>y. u \<noteq> ReifEq y"
                 "\<forall>i. u \<noteq> ReifAction i"
              by auto
            then obtain x where "u = ReifCert x" by (cases u; auto simp: is_input_pvar_def)
            then have "primed_pvar_map u = ReifCert (Primed x)" by (simp add: primed_pvar_map_def)
            with eq have "map_pvar Original u' = ReifCert (Primed x)" by simp
            thus False by (cases u'; auto simp: is_input_pvar_def split: var.splits)
          qed
          thus ?thesis using True by (auto simp: Let_def)
        next
          case False
          have "is_input_pvar u"
          proof (rule ccontr)
            assume "\<not> is_input_pvar u"
            with circ_vars r0_in u_in r0_in_reif have "u \<in> circuit_reif_pvars C_\<phi>" by blast
            then have "v \<in> circuit_reif_pvars (primed_circuit C_\<phi>)"
              using primed_reif_eq v_def by (auto simp: image_iff)
            with False show False by blast
          qed
          have not_in_orig: "v \<notin> circuit_reif_pvars (orig_circuit C_\<phi>)"
          proof
            assume "v \<in> circuit_reif_pvars (orig_circuit C_\<phi>)"
            with orig_reif_eq v_def obtain u' where u'_reif: "u' \<in> circuit_reif_pvars C_\<phi>"
              and eq: "map_pvar Original u' = primed_pvar_map u"
              by (auto simp: image_iff)
            with disjoint have not_inp_u': "\<not> is_input_pvar u'" by blast
            from `is_input_pvar u` eq not_inp_u' show False
              by (cases u; cases u'; simp add: is_input_pvar_def primed_pvar_map_def split: var.splits)
          qed
          have "?rho_combined v = ?rho_trans v"
            using False not_in_orig by (auto simp: Let_def)
          also have "... = lift_to_var rho_circ' v" using `is_input_pvar u`
          proof (cases u)
            case (StateVar w)
            hence "v = StateVar (Primed w)" by (simp add: v_def primed_pvar_map_def)
            hence "?rho_trans v = (if w \<in> ?s' then 1 else 0)"
              by (simp add: two_state_rho_def)
            also have "... = rho_circ' (StateVar w)"
              using rho_circ'_inp `is_input_pvar u` StateVar
              by (simp add: is_input_pvar_def state_rho_StateVar_eq)
            also have "... = lift_to_var rho_circ' (StateVar (Primed w))"
              by (simp add: lift_to_var_def)
            finally show ?thesis using `v = StateVar (Primed w)` by blast
          next
            case (CostBit i)
            hence "v = PrimedCostBit i" by (simp add: v_def primed_pvar_map_def)
            hence "?rho_trans v = (?c' div 2^i) mod 2"
              by (simp add: two_state_rho_def)
            also have "... = rho_circ' (CostBit i)"
              using rho_circ'_inp `is_input_pvar u` CostBit
              by (simp add: is_input_pvar_def state_rho_CostBit_eq)
            also have "... = lift_to_var rho_circ' (PrimedCostBit i)"
              by (simp add: lift_to_var_def)
            finally show ?thesis using `v = PrimedCostBit i` by blast
          next
            case (PrimedCostBit i)
            with u_in no_pcb r0_in r0_in_reif extra_disj show ?thesis by blast
          qed (auto simp: is_input_pvar_def)
          finally show ?thesis .
        qed
        thus "?rho_combined v = lift_to_var rho_circ' v" .
      qed
      ultimately show "satisfies \<psi> ?rho_combined"
        using satisfies_cong by fast
    qed
  qed

  have enc_trans_not_reif: "\<forall>\<phi> \<in> encode_transition as V B.
      \<forall>v \<in> constraint_pvars \<phi>.
        v \<notin> circuit_reif_pvars (orig_circuit C_\<phi>) \<and>
        v \<notin> circuit_reif_pvars (primed_circuit C_\<phi>)"
  proof (intro ballI allI impI)
    fix \<phi> v
    assume "\<phi> \<in> encode_transition as V B" "v \<in> constraint_pvars \<phi>"
    have v_chars: "(\<exists>k. v = ReifDeltaCost k) \<or> (\<exists>k. v = ReifDeltaCostLower k) \<or>
         (\<exists>k. v = ReifDeltaCostUpper k) \<or>
         (\<exists>k. v = ReifPrimedCostGe k) \<or> v = ReifT \<or>
         (\<exists>u. v = ReifGeq u) \<or> (\<exists>u. v = ReifLeq u) \<or> (\<exists>u. v = ReifEq u) \<or>
         (\<exists>i. v = ReifAction i) \<or> is_input_pvar v"
    proof -
      have extra_disj': "\<forall>v \<in> circuit_reif_pvars C_\<phi>.
         (\<forall>k. v \<noteq> ReifDeltaCost k) \<and> (\<forall>k. v \<noteq> ReifDeltaCostLower k) \<and>
         (\<forall>k. v \<noteq> ReifDeltaCostUpper k) \<and>
         (\<forall>k. v \<noteq> ReifPrimedCostGe k) \<and> v \<noteq> ReifT \<and>
         (\<forall>u. v \<noteq> ReifGeq u) \<and> (\<forall>u. v \<noteq> ReifLeq u) \<and> (\<forall>u. v \<noteq> ReifEq u) \<and> (\<forall>i. v \<noteq> ReifAction i)"
        using extra_disj by auto
      show ?thesis
        using enc_trans_pvars_not_circ[OF `\<phi> \<in> encode_transition as V B` extra_disj']
              `v \<in> constraint_pvars \<phi>` by blast
    qed
    show "v \<notin> circuit_reif_pvars (orig_circuit C_\<phi>) \<and> v \<notin> circuit_reif_pvars (primed_circuit C_\<phi>)"
    proof
      show "v \<notin> circuit_reif_pvars (orig_circuit C_\<phi>)"
      proof
        assume "v \<in> circuit_reif_pvars (orig_circuit C_\<phi>)"
        then obtain w where "w \<in> circuit_reif_pvars C_\<phi>" and "v = map_pvar Original w"
          using orig_reif_eq by blast
        hence "\<not> is_input_pvar w" using disjoint by auto
        moreover have "is_input_pvar w \<or>
          (\<exists>k. w = ReifDeltaCost k) \<or> (\<exists>k. w = ReifDeltaCostLower k) \<or>
          (\<exists>k. w = ReifDeltaCostUpper k) \<or>
          (\<exists>k. w = ReifPrimedCostGe k) \<or> w = ReifT \<or>
          (\<exists>u. w = ReifGeq u) \<or> (\<exists>u. w = ReifLeq u) \<or> (\<exists>u. w = ReifEq u) \<or> (\<exists>i. w = ReifAction i)"
        proof (cases w)
          case (ReifCert x)
          with `v = map_pvar Original w` v_chars show ?thesis
            by (elim disjE exE) (auto simp: is_input_pvar_def)
        qed (use v_chars `v = map_pvar Original w` in \<open>auto simp: is_input_pvar_def split: pvar.splits var.splits\<close>)
        ultimately show False using extra_disj `w \<in> circuit_reif_pvars C_\<phi>` by auto
      qed
      show "v \<notin> circuit_reif_pvars (primed_circuit C_\<phi>)"
      proof
        assume "v \<in> circuit_reif_pvars (primed_circuit C_\<phi>)"
        then obtain w where "w \<in> circuit_reif_pvars C_\<phi>" and "v = primed_pvar_map w"
          using primed_reif_eq by auto
        hence "\<not> is_input_pvar w" using disjoint by auto
        moreover have "is_input_pvar w \<or>
          (\<exists>k. w = ReifDeltaCost k) \<or> (\<exists>k. w = ReifDeltaCostLower k) \<or>
          (\<exists>k. w = ReifDeltaCostUpper k) \<or>
          (\<exists>k. w = ReifPrimedCostGe k) \<or> w = ReifT \<or>
          (\<exists>u. w = ReifGeq u) \<or> (\<exists>u. w = ReifLeq u) \<or> (\<exists>u. w = ReifEq u) \<or> (\<exists>i. w = ReifAction i)"
        proof (cases w)
          case (ReifCert x)
          with `v = primed_pvar_map w` v_chars show ?thesis
            by (elim disjE exE) (auto simp: is_input_pvar_def)
        qed (use v_chars `v = primed_pvar_map w` in \<open>auto simp: is_input_pvar_def split: pvar.splits var.splits\<close>)
        ultimately show False using extra_disj `w \<in> circuit_reif_pvars C_\<phi>` by auto
      qed
    qed
  qed

  have comb_trans: "models (encode_transition as V B) ?rho_combined"
  proof (unfold models_def, intro ballI)
    fix \<phi> assume "\<phi> \<in> encode_transition as V B"
    have "satisfies \<phi> ?rho_trans"
      using rho_trans_sat[unfolded models_def] `\<phi> \<in> encode_transition as V B` by auto
    moreover have "\<forall>v \<in> constraint_pvars \<phi>. ?rho_combined v = ?rho_trans v"
      using enc_trans_not_reif `\<phi> \<in> encode_transition as V B`
      by auto
    ultimately show "satisfies \<phi> ?rho_combined"
      using satisfies_cong by fast
  qed

  have comb_cost_ge: "models (encode_cost_ge B) ?rho_combined"
  proof (unfold models_def, intro ballI)
    fix \<phi> :: "'v var pconstraint" assume \<phi>in: "\<phi> \<in> encode_cost_ge B"
    have not_reif: "\<forall>v \<in> constraint_pvars \<phi>.
        v \<notin> circuit_reif_pvars (orig_circuit C_\<phi>) \<and> v \<notin> circuit_reif_pvars (primed_circuit C_\<phi>)"
    proof (intro ballI)
      fix v assume "v \<in> constraint_pvars \<phi>"
      have v_from_ge: "v = ReifCostGe B \<or> (\<exists>i. v = CostBit i)"
        using `\<phi> \<in> encode_cost_ge B` `v \<in> constraint_pvars \<phi>`
        by (force simp: encode_cost_ge_def reification_def reif_fwd_def reif_bwd_def
                        constraint_pvars_def pvar_of_lit_def lit_neg_def Let_def
                  split: literal.splits)
      show "v \<notin> circuit_reif_pvars (orig_circuit C_\<phi>) \<and> v \<notin> circuit_reif_pvars (primed_circuit C_\<phi>)"
      proof
        show "v \<notin> circuit_reif_pvars (orig_circuit C_\<phi>)"
        proof
          assume "v \<in> circuit_reif_pvars (orig_circuit C_\<phi>)"
          then obtain w where "w \<in> circuit_reif_pvars C_\<phi>" and "v = map_pvar Original w"
            using orig_reif_eq by blast
          with v_from_ge show False
          proof (elim disjE exE)
            assume "v = ReifCostGe B"
            with `v = map_pvar Original w` `w \<in> circuit_reif_pvars C_\<phi>` disjoint show False
              by (cases w; auto simp add: is_input_pvar_def)
          next
            fix i assume "v = CostBit i"
            with `v = map_pvar Original w` `w \<in> circuit_reif_pvars C_\<phi>` disjoint show "False"
              by (cases w; auto simp add: is_input_pvar_def)
          qed
        qed
        show "v \<notin> circuit_reif_pvars (primed_circuit C_\<phi>)"
        proof
          assume "v \<in> circuit_reif_pvars (primed_circuit C_\<phi>)"
          then obtain w where "w \<in> circuit_reif_pvars C_\<phi>" and "v = primed_pvar_map w"
            using primed_reif_eq by auto
          with v_from_ge show False
          proof (elim disjE exE)
            assume "v = ReifCostGe B"
            with `v = primed_pvar_map w` `w \<in> circuit_reif_pvars C_\<phi>` disjoint show False
              by (cases w; auto simp add: is_input_pvar_def primed_pvar_map_def)
          next
            fix i assume "v = CostBit i"
            with `v = primed_pvar_map w` show "False"
              by (cases w; simp add: is_input_pvar_def primed_pvar_map_def)
          qed
        qed
      qed
    qed
    have "satisfies \<phi> ?rho_trans"
      using rho_trans_cost_ge[unfolded models_def] \<phi>in by auto
    moreover have "\<forall>v \<in> constraint_pvars \<phi>. ?rho_combined v = ?rho_trans v"
      using not_reif by auto
    ultimately show "satisfies \<phi> ?rho_combined"
      using satisfies_cong by fast
  qed
  have comb_ReifT: "satisfies (unit_clause (Pos ReifT)) ?rho_combined"
  proof -
    have not_reif: "ReifT \<notin> circuit_reif_pvars (orig_circuit C_\<phi>) \<and>
                    ReifT \<notin> circuit_reif_pvars (primed_circuit C_\<phi>)"
    proof
      show "ReifT \<notin> circuit_reif_pvars (orig_circuit C_\<phi>)"
      proof
        assume "ReifT \<in> circuit_reif_pvars (orig_circuit C_\<phi>)"
        then obtain w where "w \<in> circuit_reif_pvars C_\<phi>" and "ReifT = map_pvar Original w"
          using orig_reif_eq by blast
        hence "w = ReifT"
          by (cases w; simp)
        with extra_disj `w \<in> circuit_reif_pvars C_\<phi>` show False by auto
      qed
      show "ReifT \<notin> circuit_reif_pvars (primed_circuit C_\<phi>)"
      proof
        assume "ReifT \<in> circuit_reif_pvars (primed_circuit C_\<phi>)"
        then obtain w where "w \<in> circuit_reif_pvars C_\<phi>" and "ReifT = primed_pvar_map w"
          using primed_reif_eq by auto
        hence "w = ReifT"
          by (cases w; simp add: primed_pvar_map_def)
        with extra_disj `w \<in> circuit_reif_pvars C_\<phi>` show False by auto
      qed
    qed
    thus ?thesis
      using rho_trans_ReifT
      by (simp add: unit_clause_def satisfies_def eval_lit_def not_reif)
  qed
  have out_orig_reif:
    "pvar_of_lit (snd (orig_circuit C_\<phi>)) \<in> circuit_reif_pvars (orig_circuit C_\<phi>)"
  proof -
    have "pvar_of_lit (snd C_\<phi>) \<in> circuit_reif_pvars C_\<phi>"
      using wf_circuit_out_reif[OF wf] .
    then have "map_pvar Original (pvar_of_lit (snd C_\<phi>)) \<in>
               map_pvar Original ` circuit_reif_pvars C_\<phi>" by blast
    moreover
    have "pvar_of_lit (snd (orig_circuit C_\<phi>)) = map_pvar Original (pvar_of_lit (snd C_\<phi>))"
      by (simp add: orig_circuit_def lift_circuit_def Let_def split_beta
                    pvar_of_lit_map_literal_gen)
    ultimately show ?thesis using orig_reif_eq by simp
  qed

  have out_orig_not_primed:
    "pvar_of_lit (snd (orig_circuit C_\<phi>)) \<notin> circuit_reif_pvars (primed_circuit C_\<phi>)"
  proof
    assume "pvar_of_lit (snd (orig_circuit C_\<phi>)) \<in> circuit_reif_pvars (primed_circuit C_\<phi>)"
    then obtain w where "w \<in> circuit_reif_pvars C_\<phi>"
      and eq: "pvar_of_lit (snd (orig_circuit C_\<phi>)) = primed_pvar_map w"
      using primed_reif_eq by blast
    then have "map_pvar Original (pvar_of_lit (snd C_\<phi>)) = primed_pvar_map w"
      by (simp add: orig_circuit_def lift_circuit_def pvar_of_lit_map_literal_gen
                    Let_def split_beta)
    thus False
      using `w \<in> circuit_reif_pvars C_\<phi>` disjoint extra_disj
      by (cases "pvar_of_lit (snd C_\<phi>)"; cases w; auto simp: is_input_pvar_def)
  qed

  have comb_orig_out:
    "satisfies (unit_clause (snd (orig_circuit C_\<phi>))) ?rho_combined"
  proof -
    let ?l = "snd (orig_circuit C_\<phi>)"
    have sat_lift: "satisfies (unit_clause ?l) (lift_to_var rho_circ)"
    proof -
      have no_pcb_out: "\<forall>i. pvar_of_lit (snd C_\<phi>) \<noteq> PrimedCostBit i"
      proof
        fix i
        have "pvar_of_lit (snd C_\<phi>) \<in> circuit_reif_pvars C_\<phi>"
          by (rule wf_circuit_out_reif[OF wf])
        with extra_disj show "pvar_of_lit (snd C_\<phi>) \<noteq> PrimedCostBit i"
          by blast
      qed
      have "eval_lit ?l (lift_to_var rho_circ) = eval_lit (snd C_\<phi>) rho_circ"
        by (simp add: eval_lit_map_pvar_lift_to_var_orig[OF no_pcb_out])
      also have "... = 1" using rho_circ_out .
      finally show ?thesis
        by (auto simp: unit_clause_def satisfies_def)
    qed
    have "\<forall>v \<in> constraint_pvars (unit_clause ?l). ?rho_combined v = lift_to_var rho_circ v"
    proof
      fix v
      assume "v \<in> constraint_pvars (unit_clause ?l)"
      then have "v = pvar_of_lit ?l"
        by (auto simp: unit_clause_def constraint_pvars_def pvar_of_lit_def)
      thus "?rho_combined v = lift_to_var rho_circ v"
        using out_orig_reif out_orig_not_primed by simp
    qed
    thus ?thesis using sat_lift satisfies_cong
      by fast
  qed

  have hyp_model:
    "\<forall>\<psi> \<in> encode_transition as V B \<union>
            circuit_constraints (orig_circuit C_\<phi>) \<union>
            circuit_constraints (primed_circuit C_\<phi>) \<union>
            encode_cost_ge B \<union>
            {unit_clause (snd (orig_circuit C_\<phi>)), unit_clause (Pos ReifT)}. satisfies \<psi> ?rho_combined"
    using comb_trans comb_circ comb_primed_circ comb_cost_ge comb_orig_out comb_ReifT
    by (auto simp: models_def)

  have rho_comb_01: "\<forall> v. ?rho_combined v = 0 \<or> ?rho_combined v = 1"
    using rho_circ_01 rho_circ'_01 two_state_rho_range unfolding lift_to_var_def
    by (auto 10 0 split: pvar.splits var.splits)
  have output_sat: "satisfies (unit_clause (snd (primed_circuit C_\<phi>))) ?rho_combined"
    using cpr_sound[OF cpr_ind _ rho_comb_01] hyp_model models_def by auto

  have out_reif': "pvar_of_lit (snd (primed_circuit C_\<phi>)) \<in> circuit_reif_pvars (primed_circuit C_\<phi>)"
  proof -
    have "pvar_of_lit (snd C_\<phi>) \<in> circuit_reif_pvars C_\<phi>"
      using wf_circuit_out_reif[OF wf] .
    hence "primed_pvar_map (pvar_of_lit (snd C_\<phi>)) \<in>
           primed_pvar_map ` circuit_reif_pvars C_\<phi>" by blast
    moreover
    have "pvar_of_lit (snd (primed_circuit C_\<phi>)) = primed_pvar_map (pvar_of_lit (snd C_\<phi>))"
      by (simp add: primed_circuit_def lift_circuit_def Let_def split_beta pvar_of_lit_map_literal_gen)
    ultimately show ?thesis using primed_reif_eq by simp
  qed

  let ?rho_out = "extend_rho C_\<phi> rho_circ' ?base_s'"

  have out_circ_sat: "models (circuit_constraints C_\<phi>) ?rho_out"
    using models_circuit_constraints_extend[OF rho_circ'_sat circ_vars]
    by (simp add: rho_circ'_inp)

  have out_reif_val: "eval_lit (snd C_\<phi>) ?rho_out = 1"
  proof -
    let ?pov = "pvar_of_lit (snd (primed_circuit C_\<phi>))"
    let ?ov  = "pvar_of_lit (snd C_\<phi>)"
    have pov_primed: "?pov \<in> circuit_reif_pvars (primed_circuit C_\<phi>)" using out_reif' .
    have pov_not_orig: "?pov \<notin> circuit_reif_pvars (orig_circuit C_\<phi>)"
    proof
      assume "?pov \<in> circuit_reif_pvars (orig_circuit C_\<phi>)"
      then obtain w where "w \<in> circuit_reif_pvars C_\<phi>" "?pov = map_pvar Original w"
        using orig_reif_eq by blast
      then have "primed_pvar_map (pvar_of_lit (snd C_\<phi>)) = map_pvar Original w"
        by (simp add: lift_circuit_def primed_circuit_def prod.case_eq_if
            pvar_of_lit_map_literal_gen)
      thus False
        using `w \<in> circuit_reif_pvars C_\<phi>` disjoint extra_disj
        by (cases "pvar_of_lit (snd C_\<phi>)"; cases w; auto)
    qed
    have pov_eq: "?pov = primed_pvar_map ?ov"
      by (simp add: lift_circuit_def primed_circuit_def prod.case_eq_if
          pvar_of_lit_map_literal_gen)
    have comb_pov: "?rho_combined ?pov = rho_circ' ?ov"
    proof -
      have "?rho_combined ?pov = lift_to_var rho_circ' ?pov"
        using pov_primed pov_not_orig by simp
      also have "lift_to_var rho_circ' ?pov = rho_circ' ?ov"
        by (metis disjoint is_input_pvar_def lift_to_var_primed_pvar_map wf pov_eq
            wf_circuit_out_reif)
      finally show ?thesis .
    qed
    have rho_out_ov: "?rho_out ?ov = rho_circ' ?ov"
      by (simp add: extend_rho_def wf wf_circuit_out_reif)
    have eval_eq: "eval_lit (snd (primed_circuit C_\<phi>)) ?rho_combined =
        eval_lit (snd C_\<phi>) ?rho_out"
      using comb_pov rho_out_ov
      unfolding primed_circuit_def lift_circuit_def Let_def pvar_of_lit_def eval_lit_def
      by (auto split: prod.splits literal.splits simp: map_pvar_def)
    have eval_eq': "eval_lit (snd (primed_circuit C_\<phi>)) ?rho_combined = eval_lit (snd C_\<phi>) rho_circ'"
    proof -
      have "eval_lit (snd (primed_circuit C_\<phi>)) ?rho_combined = eval_lit (snd C_\<phi>) ?rho_out"
        by (rule eval_eq)
      also have "eval_lit (snd C_\<phi>) ?rho_out = eval_lit (snd C_\<phi>) rho_circ'"
      proof (cases "snd C_\<phi>")
        case (Pos v)
        then show ?thesis using rho_out_ov
          by (simp add: eval_lit_def pvar_of_lit_def)
      next
        case (Neg v)
        then show ?thesis using rho_out_ov
          by (simp add: eval_lit_def pvar_of_lit_def)
      qed
      finally show ?thesis .
    qed
    have "eval_lit (snd (primed_circuit C_\<phi>)) ?rho_combined = 1"
    proof -
      from output_sat have "eval_lit (snd (primed_circuit C_\<phi>)) ?rho_combined \<ge> 1"
        by (auto simp: unit_clause_def satisfies_def)
      moreover have "eval_lit (snd C_\<phi>) rho_circ' \<le> 1"
      proof (cases "snd C_\<phi>")
        case (Pos v)
        have "rho_circ' v = 0 \<or> rho_circ' v = 1" using rho_circ'_01 by auto
        then show ?thesis by (auto simp: Pos eval_lit_def)
      next
        case (Neg v)
        have "rho_circ' v = 0 \<or> rho_circ' v = 1" using rho_circ'_01 by auto
        then show ?thesis by (auto simp: Neg eval_lit_def)
      qed
      ultimately show ?thesis using eval_eq' by linarith
    qed
    with eval_eq show ?thesis by simp
  qed

  have out_sv: "\<forall>v. ?rho_out (StateVar v) = (if v \<in> ?s' then 1 else 0)"
  proof
    fix v
    have "StateVar v \<notin> circuit_reif_pvars C_\<phi>"
      using disjoint by (auto simp: is_input_pvar_def)
    thus "?rho_out (StateVar v) = (if v \<in> ?s' then 1 else 0)"
      by (simp add: extend_rho_base_on_non_reif state_rho_def)
  qed
  have out_cb: "\<forall>i. ?rho_out (CostBit i) = (?c' div 2^i) mod 2"
  proof
    fix i
    have "CostBit i \<notin> circuit_reif_pvars C_\<phi>"
      using disjoint by (auto simp: is_input_pvar_def)
    thus "?rho_out (CostBit i) = (?c' div 2^i) mod 2"
      by (simp add: extend_rho_base_on_non_reif state_rho_def)
  qed
  have out_pcb: "\<forall>i. ?rho_out (PrimedCostBit i) = 0"
  proof
    fix i
    have "PrimedCostBit i \<notin> circuit_reif_pvars C_\<phi>"
      using disjoint by (auto simp: is_input_pvar_def)
    thus "?rho_out (PrimedCostBit i) = 0"
      by (simp add: extend_rho_base_on_non_reif state_rho_def)
  qed

  show ?thesis
    unfolding in_M_def
    using out_circ_sat out_reif_val out_sv out_cb out_pcb
    by (smt (verit, best) base_s'_01 extend_rho_def rho_circ'_01)
qed

lemma in_M_path:
  fixes \<Pi> :: "'v::linorder strips_task" and C_\<phi> :: "'v pb_circuit"
  assumes base: "in_M C_\<phi> \<Pi> s0 0"
    and path_p: "path (acts \<Pi>) s0 sf \<pi>"
    and wf: "wf_circuit C_\<phi>"
    and circ_vars: "\<forall>(r, \<phi>) \<in> set (fst C_\<phi>). \<forall>v \<in> constraint_pvars \<phi>. is_input_pvar v \<or> v \<in> circuit_reif_pvars C_\<phi>"
    and no_pcb: "\<forall>(r, \<phi>) \<in> set (fst C_\<phi>). \<forall>v \<in> constraint_pvars \<phi>. \<forall>i. v \<noteq> PrimedCostBit i"
    and disjoint: "\<forall>v \<in> circuit_reif_pvars C_\<phi>. \<not> is_input_pvar v \<and> v \<noteq> ReifI \<and> (\<forall>k. v \<noteq> ReifCostGe k)"
    and extra_disj: "\<forall>v \<in> circuit_reif_pvars C_\<phi>.
         (\<forall>k. v \<noteq> ReifDeltaCost k) \<and> (\<forall>k. v \<noteq> ReifDeltaCostLower k) \<and>
         (\<forall>k. v \<noteq> ReifDeltaCostUpper k) \<and>
         (\<forall>k. v \<noteq> ReifPrimedCostGe k) \<and> v \<noteq> ReifT \<and>
         (\<forall>u. v \<noteq> ReifGeq u) \<and> (\<forall>u. v \<noteq> ReifLeq u) \<and> (\<forall>u. v \<noteq> ReifEq u) \<and> (\<forall>i. v \<noteq> ReifAction i) \<and>
         (\<forall>i. v \<noteq> PrimedCostBit i) \<and> v \<noteq> ReifG"
    and realiz: "\<forall> (base :: 'v pvar \<Rightarrow> nat). (\<forall> v. base v = 0 \<or> base v = 1) \<longrightarrow> (\<exists> rho.
        models (circuit_constraints C_\<phi>) rho
        \<and> (\<forall> v. is_input_pvar v \<longrightarrow> rho v = base v)
        \<and> (\<forall> v. rho v = 0 \<or> rho v = 1))"
    and fin_V: "finite V"
    and cost_bound: "plan_cost \<pi> < B"
    and pre_sub: "\<forall> a \<in> set as. pre a \<subseteq> V"
    and add_sub: "\<forall> a \<in> set as. add a \<subseteq> V"
    and del_sub: "\<forall> a \<in> set as. del a \<subseteq> V"
    and acts_sub_as: "acts \<Pi> \<subseteq> set as"
    and cpr_ind: "cpr_derives
      (encode_transition as V B \<union> circuit_constraints (orig_circuit C_\<phi>) \<union>
       circuit_constraints (primed_circuit C_\<phi>) \<union> encode_cost_ge B \<union>
       {unit_clause (snd (orig_circuit C_\<phi>)), unit_clause (Pos ReifT)})
      (unit_clause (snd (primed_circuit C_\<phi>)))"
  shows "in_M C_\<phi> \<Pi> sf (plan_cost \<pi>)"
proof -
  have strengthen: "\<And>s c sf'. \<lbrakk>in_M C_\<phi> \<Pi> s c; path (acts \<Pi>) s sf' \<pi>; c + plan_cost \<pi> < B\<rbrakk>
    \<Longrightarrow> in_M C_\<phi> \<Pi> sf' (c + plan_cost \<pi>)"
  proof (induction \<pi>)
    case Nil
    from Nil.prems(2) have "sf' = s" by (cases rule: path.cases) auto
    then show ?case using Nil(1) by (simp add: plan_cost_def)
  next
    case (Cons a \<pi>')
    from Cons.prems(2) have "applicable a s"
      by (cases rule: path.cases) auto
    from Cons.prems(2) have "path (acts \<Pi>) (successor a s) sf' \<pi>'"
      by (cases rule: path.cases) auto
    have a_in_acts: "a \<in> acts \<Pi>"
      using Cons.prems(2) by (cases rule: path.cases) auto
    have a_in_as: "a \<in> set as"
      using a_in_acts acts_sub_as by auto
    have pre_a_V: "pre a \<subseteq> V" using pre_sub a_in_as by auto
    have add_a_V: "add a \<subseteq> V" using add_sub a_in_as by auto
    have del_a_V: "del a \<subseteq> V" using del_sub a_in_as by auto
    have c_lt_B: "c + cost a < B"
    proof -
      have "(c + cost a) + plan_cost \<pi>' < B"
        using Cons.prems(3) by (simp add: plan_cost_def add_ac)
      then show ?thesis using add_lessD1 by blast
    qed
    have cost_prog: "(c + cost a) + plan_cost \<pi>' < B"
      using Cons.prems(3) by (simp add: plan_cost_def add_ac)
    have step: "in_M C_\<phi> \<Pi> (successor a s) (c + cost a)"
      using in_M_step[OF Cons.prems(1) \<open>applicable a s\<close> a_in_acts acts_sub_as
                       wf circ_vars no_pcb disjoint extra_disj realiz fin_V
                       pre_sub add_sub del_sub c_lt_B cpr_ind]
      by blast
    show ?case
      using Cons.IH[OF step \<open>path (acts \<Pi>) (successor a s) sf' \<pi>'\<close> cost_prog]
      by (simp add: plan_cost_def add_ac)
  qed
  show ?thesis
    using strengthen[OF base path_p] cost_bound by simp
qed

theorem theorem_1_from_cpr:
  fixes \<Pi> :: "'v::linorder strips_task"
  assumes cert: "certificate_valid_cpr B \<Pi> Cert"
    and plan: "is_plan_for \<Pi> \<pi>"
  shows "plan_cost \<pi> \<ge> B"
proof -
  let ?as   = "cert_actions Cert"
  let ?C_\<phi>  = "cert_circuit Cert"
  let ?r_\<phi>  = "snd ?C_\<phi>"
  from cert have fin:      "finite (vars \<Pi>)"
    unfolding certificate_valid_cpr_def Let_def by auto
  from cert have init_sub: "init \<Pi> \<subseteq> vars \<Pi>"
    unfolding certificate_valid_cpr_def Let_def by auto
  from cert have goal_sub: "goal \<Pi> \<subseteq> vars \<Pi>"
    unfolding certificate_valid_cpr_def Let_def by auto
  from cert have fin_acts: "finite (acts \<Pi>)"
    unfolding certificate_valid_cpr_def Let_def by auto
  from cert have as_cover: "acts \<Pi> \<subseteq> set ?as"
    unfolding certificate_valid_cpr_def Let_def by auto
  from cert have act_sub:
    "\<forall> a \<in> set ?as. pre a \<subseteq> vars \<Pi> \<and> add a \<subseteq> vars \<Pi> \<and> del a \<subseteq> vars \<Pi>"
    unfolding certificate_valid_cpr_def Let_def by auto
  from cert have wf: "wf_circuit ?C_\<phi>"
    unfolding certificate_valid_cpr_def Let_def by auto
  from cert have disjoint_full:
    "\<forall>v \<in> circuit_reif_pvars ?C_\<phi>.
        \<not> is_input_pvar v \<and> v \<noteq> ReifI \<and> (\<forall>k. v \<noteq> ReifCostGe k) \<and> v \<noteq> ReifG \<and>
        (\<forall>k. v \<noteq> ReifDeltaCost k) \<and> (\<forall>k. v \<noteq> ReifDeltaCostLower k) \<and>
        (\<forall>k. v \<noteq> ReifDeltaCostUpper k) \<and>
        (\<forall>k. v \<noteq> ReifPrimedCostGe k) \<and> v \<noteq> ReifT \<and>
        (\<forall>u. v \<noteq> ReifGeq u) \<and> (\<forall>u. v \<noteq> ReifLeq u) \<and> (\<forall>u. v \<noteq> ReifEq u) \<and>
        (\<forall>i. v \<noteq> ReifAction i) \<and> (\<forall>i. v \<noteq> PrimedCostBit i)"
    unfolding certificate_valid_cpr_def Let_def by auto
  from cert have distinct_reif: "distinct_reif_vars ?C_\<phi>"
    unfolding certificate_valid_cpr_def Let_def by auto
  have reif_not_input: "\<forall> v \<in> circuit_reif_pvars ?C_\<phi>. \<not> is_input_pvar v"
    using disjoint_full unfolding circuit_reif_pvars_def by auto
  note wf_circuit_realizability[OF wf distinct_reif reif_not_input]
  then have realiz': "\<forall> (base :: 'v pvar \<Rightarrow> nat). (\<forall>v. base v = 0 \<or> base v = 1) \<longrightarrow> (\<exists> rho.
      models (circuit_constraints ?C_\<phi>) rho
      \<and> (\<forall>v. is_input_pvar v \<longrightarrow> rho v = base v)
      \<and> (\<forall>v. rho v = 0 \<or> rho v = 1))"
    by blast
  from cert have cpr_init: "cpr_derives
      (encode_init \<Pi> \<union> circuit_constraints ?C_\<phi> \<union> encode_cost_ge B \<union>
       {unit_clause (Pos ReifI), neg_cost_ge_one B})
      (unit_clause (snd ?C_\<phi>))"
    unfolding certificate_valid_cpr_def Let_def by auto
  from cert have cpr_goal: "cpr_derives
      (encode_goal \<Pi> \<union> circuit_constraints ?C_\<phi> \<union> encode_cost_ge B \<union>
       {unit_clause (snd ?C_\<phi>), unit_clause (Pos ReifG)})
      (cost_ge_constraint B)"
    unfolding certificate_valid_cpr_def Let_def by auto
  from cert have cpr_ind: "cpr_derives
      (encode_transition ?as (vars \<Pi>) B \<union> circuit_constraints (orig_circuit ?C_\<phi>) \<union>
       circuit_constraints (primed_circuit ?C_\<phi>) \<union> encode_cost_ge B \<union>
       {unit_clause (snd (orig_circuit ?C_\<phi>)), unit_clause (Pos ReifT)})
      (unit_clause (snd (primed_circuit ?C_\<phi>)))"
    unfolding certificate_valid_cpr_def Let_def by auto
  have disjoint: "\<forall>v \<in> circuit_reif_pvars ?C_\<phi>. \<not> is_input_pvar v \<and> v \<noteq> ReifI \<and> (\<forall>k. v \<noteq> ReifCostGe k)"
    using disjoint_full unfolding circuit_reif_pvars_def by auto
  have extra_disj: "\<forall>v \<in> circuit_reif_pvars ?C_\<phi>.
       (\<forall>k. v \<noteq> ReifDeltaCost k) \<and> (\<forall>k. v \<noteq> ReifDeltaCostLower k) \<and>
       (\<forall>k. v \<noteq> ReifDeltaCostUpper k) \<and>
       (\<forall>k. v \<noteq> ReifPrimedCostGe k) \<and> v \<noteq> ReifT \<and>
       (\<forall>u. v \<noteq> ReifGeq u) \<and> (\<forall>u. v \<noteq> ReifLeq u) \<and> (\<forall>u. v \<noteq> ReifEq u) \<and> (\<forall>i. v \<noteq> ReifAction i) \<and>
       (\<forall>i. v \<noteq> PrimedCostBit i) \<and> v \<noteq> ReifG"
    using disjoint_full unfolding circuit_reif_pvars_def by auto
  have disjointG: "ReifG \<notin> circuit_reif_pvars ?C_\<phi>"
    using disjoint_full unfolding circuit_reif_pvars_def by auto
  have circ_vars: "\<forall>(r, \<phi>) \<in> set (fst ?C_\<phi>).
      \<forall>v \<in> constraint_pvars \<phi>. is_input_pvar v \<or> v \<in> circuit_reif_pvars ?C_\<phi>"
  proof -
    {
      fix r \<phi> v
      assume rin: "(r, \<phi>) \<in> set (fst ?C_\<phi>)" and vin: "v \<in> constraint_pvars \<phi>"
      obtain pairs out where cphi: "?C_\<phi> = (pairs, out)" by (cases ?C_\<phi>)
      have rin': "(r, \<phi>) \<in> set pairs" using rin cphi by simp
      from rin' obtain i where i_lt: "i < length pairs" and pairs_i: "pairs ! i = (r, \<phi>)"
        using in_set_conv_nth by metis
      from wf[unfolded cphi wf_circuit_def Let_def, simplified, THEN conjunct1, rule_format, OF i_lt]
      have sub: "constraint_pvars \<phi> - {pvar_of_lit r} \<subseteq> Collect is_input_pvar \<union> pvar_of_lit ` fst ` set (take i pairs)"
        using pairs_i  by (auto simp add: split_beta constraint_pvars_def)
      have rv_in: "pvar_of_lit r \<in> circuit_reif_pvars ?C_\<phi>"
        unfolding circuit_reif_pvars_def cphi using rin' by (auto simp: image_def)
      have take_sub: "pvar_of_lit ` fst ` set (take i pairs) \<subseteq> circuit_reif_pvars ?C_\<phi>"
        unfolding circuit_reif_pvars_def cphi using set_take_subset[of i pairs] by auto
      have "is_input_pvar v \<or> v \<in> circuit_reif_pvars ?C_\<phi>"
      proof (cases "v = pvar_of_lit r")
        case True thus ?thesis using rv_in by auto
      next
        case False
        then have "v \<in> Collect is_input_pvar \<union> pvar_of_lit ` fst ` set (take i pairs)"
          using sub vin by auto
        thus ?thesis using take_sub by auto
      qed
    }
    then show ?thesis by (auto simp: Ball_def split: prod.splits)
  qed
  have no_pcb: "\<forall>(r, \<phi>) \<in> set (fst ?C_\<phi>). \<forall>v \<in> constraint_pvars \<phi>. \<forall>i. v \<noteq> PrimedCostBit i"
    using cert unfolding certificate_valid_cpr_def Let_def by auto
  (* Get path from plan *)
  from plan obtain sf where
    path_p: "path (acts \<Pi>) (init \<Pi>) sf \<pi>"
    and goal_sf: "is_goal_state \<Pi> sf"
    unfolding is_plan_for_def by blast
  have pre_sub: "\<forall> a \<in> set ?as. pre a \<subseteq> vars \<Pi>" using act_sub by auto
  have add_sub: "\<forall> a \<in> set ?as. add a \<subseteq> vars \<Pi>" using act_sub by auto
  have del_sub: "\<forall> a \<in> set ?as. del a \<subseteq> vars \<Pi>" using act_sub by auto
  (* Case split: B = 0 is trivial *)
  show "plan_cost \<pi> \<ge> B"
  proof (cases "B = 0")
    case True thus ?thesis by simp
  next
    case False
    then have B_pos: "B \<ge> 1" by simp
    show "plan_cost \<pi> \<ge> B"
    proof (rule ccontr)
      assume "\<not> plan_cost \<pi> \<ge> B"
      then have cost_lt_B: "plan_cost \<pi> < B" by (simp add: not_le)
      have in_M_0: "in_M ?C_\<phi> \<Pi> (init \<Pi>) 0"
        using in_M_init[OF fin init_sub wf wf_circuit_out_reif[OF wf] circ_vars disjoint
                           realiz' B_pos cpr_init]
        .
      have in_M_final: "in_M ?C_\<phi> \<Pi> sf (plan_cost \<pi>)"
        using in_M_path[OF in_M_0 path_p wf circ_vars no_pcb disjoint extra_disj realiz'
                          fin cost_lt_B pre_sub add_sub del_sub as_cover cpr_ind]
        .
      have "plan_cost \<pi> \<ge> B"
        using in_M_goal_bound[OF in_M_final wf circ_vars disjoint disjointG cpr_goal goal_sf
                                 fin goal_sub]
        .
      thus False using cost_lt_B by simp
    qed
  qed
qed

end