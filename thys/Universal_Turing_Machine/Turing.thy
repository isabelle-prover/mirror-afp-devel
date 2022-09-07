(* Title: thys/Turing.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
   Modifications, comments by Franz Regensburger (FABR) 02/2022
 *)

chapter \<open>Turing Machines\<close>

theory Turing
  imports Main
begin

section \<open>Some lemmas about natural numbers used for rewriting\<close>

(* ------ Important properties used in subsequent theories ------ *)

(*
  Num.numeral_1_eq_Suc_0: Numeral1 = Suc 0
  Num.numeral_2_eq_2: 2 = Suc (Suc 0)
  Num.numeral_3_eq_3: 3 = Suc (Suc (Suc 0))
*)

lemma numeral_4_eq_4: "4 = Suc 3"
  by auto

lemma numeral_eqs_upto_12:
  shows "2 = Suc 1"
    and "3 = Suc 2"
    and "4 = Suc 3" 
    and "5 = Suc 4" 
    and "6 = Suc 5" 
    and "7 = Suc 6"
    and "8 = Suc 7" 
    and "9 = Suc 8" 
    and "10 = Suc 9"
    and "11 = Suc 10"
    and "12 = Suc 11"
  by simp_all


section \<open>Basic Definitions for Turing Machines\<close>

datatype action = WB | WO | L | R | Nop

datatype cell = Bk | Oc

text\<open>Remark: the constructors @{term W0} and @{term W1} were renamed into @{term WB} and @{term WO}
respectively because this makes a better match with the constructors @{term Bk} and @{term Oc} of 
type @{typ cell}.\<close>

type_synonym tape = "cell list \<times> cell list"

type_synonym state = nat

type_synonym instr = "action \<times> state"

type_synonym tprog = "instr list \<times> nat"

(* The type tprog0 is the type of un-shifted Turing machines (offset = 0).
 *
 * FABR note:
 * Every (tm:: instr list) is a proper Turing machine.
 *
 * However, tm may not be composable with other Turing machines.
 * For the sequential composition tm |+| tm' the machine tm must be 'well-formed'.
 * See theory ComposableTMs.thy for more details.
 *
 * We will prove in theory ComposableTMs.thy that for every 
 * Turing machine tm, which is not well-formed, there is a machine
 *    (mk_composable0 tm)
 * that is well-formed and has the same behaviour as tm.
 *
 * Thus, all Turing machines can be made composable :-)
 *)

type_synonym tprog0 = "instr list"

type_synonym config = "state \<times> tape"

fun nth_of where
  "nth_of xs i = (if i \<ge> length xs then None else Some (xs ! i))"

lemma nth_of_map (* [simp]*): (* this lemma is used nowhere *)
  shows "nth_of (map f p) n = (case (nth_of p n) of None \<Rightarrow> None | Some x \<Rightarrow> Some (f x))"
  by simp

fun 
  fetch :: "instr list \<Rightarrow> state \<Rightarrow> cell \<Rightarrow> instr"
  where
    "fetch p 0 b = (Nop, 0)"
  | "fetch p (Suc s) Bk = 
     (case nth_of p (2 * s) of
        Some i \<Rightarrow> i
      | None \<Rightarrow> (Nop, 0))"
  |"fetch p (Suc s) Oc = 
     (case nth_of p ((2 * s) + 1) of
         Some i \<Rightarrow> i
       | None \<Rightarrow> (Nop, 0))"

lemma fetch_Nil [simp]:
  shows "fetch [] s b = (Nop, 0)"
  by (cases s,force) (cases b;force)

(* Simpler code without usage of function nth_of *)
lemma fetch_imp [code]: "fetch p n b = (
    let len = length p
    in
    if n = 0
    then (Nop, 0)
    else if b = Bk
         then if len \<le> 2*n -2
              then (Nop,0)
              else (p ! (2*n-2))
         else if len \<le> 2*n-1
              then (Nop,0)
              else (p ! (2*n-1))
  )"
  by (cases n; cases b)(auto)

(* ------------------------------------ *)
(* Some arithmetic properties           *)
(* ------------------------------------ *)

lemma even_le_div2_imp_le_times_2: "m     div 2 < (Suc n) \<and> ((m::nat) mod 2 = 0) \<Longrightarrow> m \<le> 2*n" by arith

lemma odd_le_div2_imp_le_times_2: "(m+1) div 2 < (Suc n) \<and> ((m::nat) mod 2 \<noteq> 0) \<Longrightarrow> m \<le> 2*n" by arith

lemma odd_div2_plus_1_eq: "(n::nat) mod 2 \<noteq> 0 \<Longrightarrow> (n div 2) + 1 = (n+1) div 2"
proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case by arith
qed

(* ---------------------------------- *)
(* A lemma about the list function tl *)
(* ---------------------------------- *)

lemma list_length_tl_neq_Nil: "1 < length (nl::nat list) \<Longrightarrow> tl nl \<noteq> []"
proof
  assume "1 < length nl" and "tl nl = []"
  then have "length (tl nl) = 0" by auto
  with \<open>1 < length nl\<close> and length_tl
  show False by auto
qed

(* --- A function for executing actions on the tape --- *)

fun 
  update :: "action \<Rightarrow> tape \<Rightarrow> tape"
  where 
    "update WB (l, r) = (l, Bk # (tl r))" 
  | "update WO (l, r) = (l, Oc # (tl r))"
  | "update L (l, r) = (if l = [] then ([], Bk # r) else (tl l, (hd l) # r))" 
  | "update R (l, r) = (if r = [] then (Bk # l, []) else ((hd r) # l, tl r))" 
  | "update Nop (l, r) = (l, r)"

abbreviation 
  "read r == if (r = []) then Bk else hd r"

fun step :: "config \<Rightarrow> tprog \<Rightarrow> config"
  where 
    "step (s, l, r) (p, off) = 
     (let (a, s') = fetch p (s - off) (read r) in (s', update a (l, r)))"

abbreviation
  "step0 c p \<equiv> step c (p, 0)"

fun steps :: "config \<Rightarrow> tprog \<Rightarrow> nat \<Rightarrow> config"
  where
    "steps c p 0 = c" |
    "steps c p (Suc n) = steps (step c p) p n"

abbreviation
  "steps0 c p n \<equiv> steps c (p, 0) n"


lemma step_red [simp]: 
  shows "steps c p (Suc n) = step (steps c p n) p"
  by (induct n arbitrary: c) (auto)

lemma steps_add [simp]: 
  shows "steps c p (m + n) = steps (steps c p m) p n"
  by (induct m arbitrary: c) (auto)

lemma step_0 [simp]: 
  shows "step (0, (l, r)) p = (0, (l, r))"
  by (cases p, simp)

lemma step_0': "step (0, tap) p = (0, tap)" by (cases tap) auto


lemma steps_0 [simp]: 
  shows "steps (0, (l, r)) p n = (0, (l, r))"
  by (induct n) (simp_all)

fun
  is_final :: "config \<Rightarrow> bool"
  where
    "is_final (s, l, r) = (s = 0)"

lemma is_final_eq: 
  shows "is_final (s, tap) = (s = 0)"
  by (cases tap) (auto)

lemma is_finalI [intro]:
  shows "is_final (0, tap)"
  by (simp add: is_final_eq)

lemma after_is_final:
  assumes "is_final c"
  shows "is_final (steps c p n)"
  using assms 
  by(induct n;cases c;auto)

lemma is_final:
  assumes a: "is_final (steps c p n1)"
    and b: "n1 \<le> n2"
  shows "is_final (steps c p n2)"
proof - 
  obtain n3 where eq: "n2 = n1 + n3" using b by (metis le_iff_add)
  from a show "is_final (steps c p n2)" unfolding eq
    by (simp add: after_is_final)
qed

(* steps add *)
lemma stable_config_after_final_add:
  assumes "steps (1, l, r) p n1      = (0, l', r')"
  shows   "steps (1, l, r) p (n1+n2) = (0, l', r')"
proof -
  from assms have "is_final (steps (1, l, r) p n1)" by  (auto simp add: is_final_eq)
  moreover have "n1 \<le> (n1+n2)" by auto
  ultimately have "is_final (steps (1, l, r) p (n1+n2))" by (rule  is_final)
  with assms show ?thesis by (auto simp add: is_final_eq)
qed

lemma stable_config_after_final_add_2:
  assumes "steps (s, l, r) p n1      = (0, l', r')"
  shows   "steps (s, l, r) p (n1+n2) = (0, l', r')"
proof -
  from assms have "is_final (steps (s, l, r) p n1)" by  (auto simp add: is_final_eq)
  moreover have "n1 \<le> (n1+n2)" by auto
  ultimately have "is_final (steps (s, l, r) p (n1+n2))" by (rule  is_final)
  with assms show ?thesis by (auto simp add: is_final_eq)
qed

(* steps \<le> *)

lemma stable_config_after_final_ge:
  assumes a: "steps (1, l, r) p n1 = (0, l', r')" and b: "n1 \<le> n2"
  shows   "steps (1, l, r) p n2 = (0, l', r')"
proof -
  from b have "\<exists>k. n2 = n1 + k" by arith
  then obtain k where w: "n2 = n1 + k" by blast
  with a have "steps (1, l, r) p ( n1 + k) = (0, l', r')"
    by (auto simp add: stable_config_after_final_add)
  with w show ?thesis by auto
qed

lemma stable_config_after_final_ge_2:
  assumes a: "steps (s, l, r) p n1 = (0, l', r')" and b: "n1 \<le> n2"
  shows   "steps (s, l, r) p n2 = (0, l', r')"
proof -
  from b have "\<exists>k. n2 = n1 + k" by arith
  then obtain k where w: "n2 = n1 + k" by blast
  with a have "steps (s, l, r) p ( n1 + k) = (0, l', r')"
    by (auto simp add: stable_config_after_final_add)
  with w show ?thesis by auto
qed

(* steps0 \<le> *)

lemma stable_config_after_final_ge':
  assumes "steps0 (1, l, r) p n1 = (0, l', r')" and b: "n1 \<le> n2"
  shows   "steps0 (1, l, r) p n2 = (0, l', r')"
proof -
  from assms have "steps (1, l, r) (p, 0) n1 = (0, l', r')" by auto
  from this and  assms(2) show "steps (1, l, r) (p,0) n2 = (0, l', r')"
    by (rule stable_config_after_final_ge)
qed

lemma stable_config_after_final_ge_2':
  assumes "steps0 (s, l, r) p n1 = (0, l', r')" and b: "n1 \<le> n2"
  shows   "steps0 (s, l, r) p n2 = (0, l', r')"
proof -
  from assms have "steps (s, l, r) (p, 0) n1 = (0, l', r')" by auto
  from this and  assms(2) show "steps (s, l, r) (p,0) n2 = (0, l', r')"
    by (rule stable_config_after_final_ge_2)
qed

lemma not_is_final:
  assumes a: "\<not> is_final (steps c p n1)"
    and b: "n2 \<le> n1"
  shows "\<not> is_final (steps c p n2)"
proof (rule notI)
  obtain n3 where eq: "n1 = n2 + n3" using b by (metis le_iff_add)
  assume "is_final (steps c p n2)"
  then have "is_final (steps c p n1)" unfolding eq
    by (simp add: after_is_final)
  with a show "False" by simp
qed

(* if the machine is in the halting state, there must have 
   been a state just before the halting state *)

lemma before_final: 
  assumes "steps0 (1, tap) A n = (0, tap')"
  shows "\<exists> n'. \<not> is_final (steps0 (1, tap) A n') \<and> steps0 (1, tap) A (Suc n') = (0, tap')"
  using assms
proof(induct n arbitrary: tap')
  case (0 tap')
  have asm: "steps0 (1, tap) A 0 = (0, tap')" by fact
  then show "\<exists>n'. \<not> is_final (steps0 (1, tap) A n') \<and> steps0 (1, tap) A (Suc n') = (0, tap')"
    by simp
next
  case (Suc n tap')
  have ih: "\<And>tap'. steps0 (1, tap) A n = (0, tap') \<Longrightarrow>
    \<exists>n'. \<not> is_final (steps0 (1, tap) A n') \<and> steps0 (1, tap) A (Suc n') = (0, tap')" by fact
  have asm: "steps0 (1, tap) A (Suc n) = (0, tap')" by fact
  obtain s l r where cases: "steps0 (1, tap) A n = (s, l, r)"
    by (auto intro: is_final.cases)
  then show "\<exists>n'. \<not> is_final (steps0 (1, tap) A n') \<and> steps0 (1, tap) A (Suc n') = (0, tap')"
  proof (cases "s = 0")
    case True (* in halting state *)
    then have "steps0 (1, tap) A n = (0, tap')"
      using asm cases by (simp del: steps.simps)
    then show ?thesis using ih by simp
  next
    case False (* not in halting state *)
    then have "\<not> is_final (steps0 (1, tap) A n) \<and> steps0 (1, tap) A (Suc n) = (0, tap')"
      using asm cases by simp
    then show ?thesis by auto
  qed
qed

lemma least_steps: 
  assumes "steps0 (1, tap) A n = (0, tap')"
  shows "\<exists> n'. (\<forall>n'' < n'. \<not> is_final (steps0 (1, tap) A n'')) \<and> 
               (\<forall>n'' \<ge> n'. is_final (steps0 (1, tap) A n''))"
proof -
  from before_final[OF assms] 
  obtain n' where
    before: "\<not> is_final (steps0 (1, tap) A n')" and
    final: "steps0 (1, tap) A (Suc n') = (0, tap')" by auto
  from before
  have "\<forall>n'' < Suc n'. \<not> is_final (steps0 (1, tap) A n'')"
    using not_is_final by auto
  moreover
  from final 
  have "\<forall>n'' \<ge> Suc n'. is_final (steps0 (1, tap) A n'')" 
    using is_final[of _ _ "Suc n'"] by (auto simp add: is_final_eq)
  ultimately
  show "\<exists> n'. (\<forall>n'' < n'. \<not> is_final (steps0 (1, tap) A n'')) \<and> (\<forall>n'' \<ge> n'. is_final (steps0 (1, tap) A n''))"
    by blast
qed

lemma at_least_one_step:"steps0 (1, [], r) tm n = (0,tap) \<Longrightarrow> 0 < n"
  by (cases n)(auto)

end
