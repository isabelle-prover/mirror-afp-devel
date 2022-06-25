subsection \<open>Simple Properties of Register Machines\<close>

theory RegisterMachineProperties
    imports "RegisterMachineSpecification"
begin

lemma step_commutative: "steps (step c p) p t = step (steps c p t) p"
  by (induction t; auto)

lemma step_fetch_correct:
  fixes t :: nat
    and c :: configuration
    and p :: program
  assumes "is_valid c p"
  defines "ct \<equiv> (steps c p t)"
  shows "fst (steps (step c p) p t) = fetch (fst ct) p (read (snd ct) p (fst ct))"
  using ct_def step_commutative step_def by auto

subsubsection \<open>From Configurations to a Protocol\<close>

text \<open>Register Values\<close>

definition R :: "configuration \<Rightarrow> program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "R c p n t = (snd (steps c p t)) ! n"

fun RL :: "configuration \<Rightarrow> program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"  where
  "RL c p b 0 l = ((snd c) ! l)" |
  "RL c p b (Suc t) l = ((snd c) ! l) + b * (RL (step c p) p b t l)"

lemma RL_simp_aux:
  \<open>snd c ! l + b * RL (step c p) p b t l =
    RL c p b t l + b * (b ^ t * snd (step (steps c p t) p) ! l)\<close>
  by (induction t arbitrary: c)
    (auto simp: step_commutative algebra_simps)

declare RL.simps[simp del]
lemma RL_simp:
  "RL c p b (Suc t) l = (snd (steps c p (Suc t)) ! l) * b ^ (Suc t) + (RL c p b t l)"
proof (induction t arbitrary: p c b)
  case 0
  thus ?case by (auto simp: RL.simps)
next
  case (Suc t p c b)
  show ?case
    by (subst RL.simps) (*  \<open>unfold one level\<close> *)
      (auto simp: Suc step_commutative algebra_simps RL_simp_aux)
qed

text \<open>State Values\<close>

definition S :: "configuration \<Rightarrow> program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "S c p k t = (if (fst (steps c p t) = k) then (Suc 0) else 0)"

definition S2 :: "configuration \<Rightarrow> nat \<Rightarrow> nat"
  where "S2 c k = (if (fst c) = k then 1 else 0)"

fun SK :: "configuration \<Rightarrow> program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "SK c p b 0 k = (S2 c k)" |
   "SK c p b (Suc t) k = (S2 c k) + b * (SK (step c p) p b t k)"

lemma SK_simp_aux:
  \<open>SK c p b (Suc (Suc t)) k =
    S2 (steps c p (Suc (Suc t))) k * b ^ Suc (Suc t) + SK c p b (Suc t) k\<close>
   by (induction t arbitrary: c) (auto simp: step_commutative algebra_simps)

declare SK.simps[simp del]
lemma SK_simp:
  "SK c p b (Suc t) k = (S2 (steps c p (Suc t)) k) * b ^ (Suc t) + (SK c p b t k)"
proof (induction t arbitrary: p c b k)
  case 0
  thus ?case by (auto simp: SK.simps)
next
  case (Suc t p c b k)
  show ?case
    by (auto simp: Suc algebra_simps step_commutative SK_simp_aux)
qed

text \<open>Zero-Indicator Values\<close>
 
definition Z :: "configuration \<Rightarrow> program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"  where
   "Z c p n t = (if (R c p n t > 0) then 1 else 0)"

definition Z2 :: "configuration \<Rightarrow> nat \<Rightarrow> nat" where
   "Z2 c n = (if (snd c) ! n > 0 then 1 else 0)"

fun ZL :: "configuration \<Rightarrow> program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "ZL c p b 0 l = (Z2 c l)" |
   "ZL c p b (Suc t) l = (Z2 c l) +  b * (ZL (step c p) p b t l)"

lemma ZL_simp_aux:
"Z2 c l + b * ZL (step c p) p b t l =
    ZL c p b t l + b * (b ^ t * Z2 (step (steps c p t) p) l)"
  by (induction t arbitrary: c) (auto simp: step_commutative algebra_simps)

declare ZL.simps[simp del]
lemma ZL_simp:
  "ZL c p b (Suc t) l = (Z2 (steps c p (Suc t)) l) * b ^ (Suc t) + (ZL c p b t l)"
proof (induction t arbitrary: p c b)
  case 0
  thus ?case by (auto simp: ZL.simps)
next
  case (Suc t p c b)
  show ?case
    by (subst ZL.simps) (auto simp: Suc step_commutative algebra_simps ZL_simp_aux)
qed

subsubsection \<open>Protocol Properties\<close>

lemma Z_bounded: "Z c p l t \<le> 1"
  by (auto simp: Z_def)

lemma S_bounded: "S c p k t \<le> 1"
  by (auto simp: S_def)

lemma S_unique: "\<forall>k\<le>length p. (k \<noteq> fst (steps c p t) \<longrightarrow> S c p k t = 0)"
  by (auto simp: S_def)


(* takes c :: nat, the exponent defining the base b *)
fun cells_bounded :: "configuration \<Rightarrow> program \<Rightarrow> nat \<Rightarrow> bool" where
  "cells_bounded conf p c = ((\<forall>l<(length (snd conf)). \<forall>t. 2^c > R conf p l t)
                          \<and>  (\<forall>k t. 2^c > S conf p k t)
                          \<and>  (\<forall>l t. 2^c > Z conf p l t))"

lemma steps_tape_length_invar:  "length (snd (steps c p t)) = length (snd c)"
  by (induction t; auto simp add: step_def update_def)

lemma step_is_valid_invar: "is_valid c p \<Longrightarrow> is_valid (step c p) p"
  by (auto simp add: step_def update_def is_valid_def)

fun fetch_old
  where
    "(fetch_old p s (Add r next) _) = next"
  | "(fetch_old p s (Sub r next nextalt) val) = (if val = 0 then nextalt else next)"
  | "(fetch_old p s Halt _) = s"

lemma fetch_equiv:
  assumes "i = p!s"
  shows "fetch s p v = fetch_old p s i v"
  by (cases i; auto simp: assms fetch_def)

(* Corollary: All states have instructions in the program list *)
lemma p_contains: "is_valid_initial ic p a \<Longrightarrow> (fst (steps ic p t)) < length p"
proof -
  assume asm: "is_valid_initial ic p a"
  hence "fst ic = 0" using is_valid_initial_def is_valid_def by blast
  hence 0: "ic = (0, snd ic)" by (metis prod.collapse)
  show ?thesis using 0 asm
  apply (induct t) apply auto[1]
  subgoal by (auto simp add: is_valid_initial_def is_valid_def)
  apply (cases "p ! fst (steps ic p t)")
  apply (auto simp add: list_all_length fetch_equiv step_def
                is_valid_initial_def is_valid_def fetch_old.elims)
  by (metis RegisterMachineSpecification.isc_add RegisterMachineSpecification.isc_sub 
      fetch_old.elims) +
qed

lemma steps_is_valid_invar: "is_valid c p \<Longrightarrow> is_valid (steps c p t) p"
  by (induction t; auto simp add: step_def update_def is_valid_def)

lemma terminates_halt_state: "terminates ic p q \<Longrightarrow> is_valid_initial ic p a
                               \<Longrightarrow> ishalt (p ! (fst (steps ic p q)))"
proof -
  assume terminate: "terminates ic p q"
  assume is_val: "is_valid_initial ic p a"
  have "1 < length p" using is_val is_valid_initial_def[of "ic" "p" "a"]
    is_valid_def[of "ic" "p"] program_includes_halt.simps
    by blast
  hence "p \<noteq> []" by auto
  hence "p ! (length p - 1) = last p" using List.last_conv_nth[of "p"] by auto
  thus ?thesis
    using terminate terminates_def correct_halt_def is_val is_valid_def[of "ic" "p"] by auto
qed

lemma R_termination:
  fixes l :: register and ic :: configuration
  assumes is_val: "is_valid ic p" and terminate: "terminates ic p q" and l: "l < length (snd ic)"
  shows "\<forall>t\<ge>q. R ic p l t = 0"
proof -
  have ishalt: "ishalt (p ! fst (steps ic p q))"
    using terminate terminates_def correct_halt_def is_valid_def is_val by auto
  have halt: "ishalt (p ! fst (steps ic p (q + t)))" for t
    apply (induction t)
    using terminate terminates_def ishalt step_def fetch_def by auto
  have "l<(length (snd ic)) \<longrightarrow>R ic p l (q+t) = 0" for t
    apply (induction t arbitrary: l)
    subgoal using terminate terminates_def correct_halt_def R_def by auto
    subgoal using R_def step_def halt update_def by auto
    done
  thus ?thesis using le_Suc_ex l by force
qed

lemma terminate_c_exists: "is_valid ic p \<Longrightarrow> terminates ic p q \<Longrightarrow> \<exists>c>1. cells_bounded ic p c"
proof -
  assume is_val: "is_valid ic p"
  assume terminate: "terminates ic p q"
  define n where "n \<equiv> length (snd ic)"
  define rmax where "rmax \<equiv> Max ({k. \<exists>l<n. \<exists>t<q. k = R ic p l t} \<union> {2})"
  have  "\<forall>l<n. \<forall>t<q. R ic p l t \<in> {k. \<exists>l<n. \<exists>t<q. k = R ic p l t}" by auto
  hence "\<forall>t<q. \<forall>l<n. R ic p l t \<le> rmax" using rmax_def by auto
  moreover have "\<forall>t\<ge>q. \<forall>l<n. R ic p l t \<le> rmax"
    using rmax_def R_termination terminate n_def is_val by auto
  ultimately have r: "\<forall>l<n. \<forall>t. R ic p l t \<le> rmax" using not_le_imp_less by blast
  have gt2: "rmax \<ge> 2" using rmax_def by auto
  hence sz: "(\<forall>k t. rmax > S ic p k t) \<and> (\<forall>l t. rmax > Z ic p l t)"
    using S_bounded Z_bounded S_def Z_def by auto
  have "(\<forall>l<n. \<forall>t. R ic p l t < 2^rmax) \<and> (\<forall>k t. S ic p k t < 2^rmax) 
         \<and> (\<forall>l t. Z ic p l t < 2^rmax)"
    using less_exp[of "rmax"] r sz by (metis le_neq_implies_less dual_order.strict_trans)
  moreover have "rmax > 1" using gt2 by auto
  ultimately show ?thesis using n_def by auto
qed

end
