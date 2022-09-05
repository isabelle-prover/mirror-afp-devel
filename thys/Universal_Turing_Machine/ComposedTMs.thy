(* Title: thys/ComposedTMs.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
 
   Minor modifications, comments by Franz Regensburger (FABR) 02/2022
 *)

theory ComposedTMs
  imports ComposableTMs
begin

section \<open>Composition of Turing Machines\<close>

fun 
  shift :: "instr list \<Rightarrow> nat \<Rightarrow> instr list"
  where
    "shift p n = (map (\<lambda> (a, s). (a, (if s = 0 then 0 else s + n))) p)"

fun 
  adjust :: "instr list \<Rightarrow> nat \<Rightarrow> instr list"
  where
    "adjust p e = map (\<lambda> (a, s). (a, if s = 0 then e else s)) p"

abbreviation
  "adjust0 p \<equiv> adjust p (Suc (length p div 2))"

lemma length_shift [simp]: 
  shows "length (shift p n) = length p"
  by simp

lemma length_adjust [simp]: 
  shows "length (adjust p n) = length p"
  by (induct p) (auto)


(* composition of two Turing machines *)
fun
  seq_tm :: "instr list \<Rightarrow> instr list \<Rightarrow> instr list" (infixl "|+|" 60)
  where
    "seq_tm p1 p2 = ((adjust0 p1) @ (shift p2 (length p1 div 2)))"

lemma seq_tm_length:
  shows "length (A |+| B) = length A + length B"
  by auto

lemma seq_tm_composable[intro]: 
  "\<lbrakk>composable_tm (A, 0); composable_tm (B, 0)\<rbrakk> \<Longrightarrow> composable_tm (A |+| B, 0)"
  by (fastforce)

lemma seq_tm_step: 
  assumes unfinal: "\<not> is_final (step0 c A)"
  shows "step0 c (A |+| B) = step0 c A"
proof -
  obtain s l r where eq: "c = (s, l, r)" by (metis is_final.cases) 
  have "\<not> is_final (step0 (s, l, r) A)" using unfinal eq by simp
  then have "case (fetch A s (read r)) of (a, s) \<Rightarrow> s \<noteq> 0"
    by (auto simp add: is_final_eq)
  then have "fetch (A |+| B) s (read r) = fetch A s (read r)"
    apply (cases "read r";cases s)
    by (auto simp: seq_tm_length nth_append)
  then show "step0 c (A |+| B) = step0 c A" by (simp add: eq) 
qed

lemma seq_tm_steps:  
  assumes "\<not> is_final (steps0 c A n)" 
  shows "steps0 c (A |+| B) n = steps0 c A n"
  using assms
proof(induct n)
  case 0
  then show "steps0 c (A |+| B) 0 = steps0 c A 0" by auto
next 
  case (Suc n)
  have ih: "\<not> is_final (steps0 c A n) \<Longrightarrow> steps0 c (A |+| B) n = steps0 c A n" by fact
  have fin: "\<not> is_final (steps0 c A (Suc n))" by fact
  then have fin1: "\<not> is_final (step0 (steps0 c A n) A)" 
    by (auto simp only: step_red)
  then have fin2: "\<not> is_final (steps0 c A n)"
    by (metis is_final_eq step_0 surj_pair) 

  have "steps0 c (A |+| B) (Suc n) = step0 (steps0 c (A |+| B) n) (A |+| B)" 
    by (simp only: step_red)
  also have "... = step0 (steps0 c A n) (A |+| B)" by (simp only: ih[OF fin2])
  also have "... = step0 (steps0 c A n) A" by (simp only: seq_tm_step[OF fin1])
  finally show "steps0 c (A |+| B) (Suc n) = steps0 c A (Suc n)"
    by (simp only: step_red)
qed

lemma seq_tm_fetch_in_A:
  assumes h1: "fetch A s x = (a, 0)"
    and h2: "s \<le> length A div 2" 
    and h3: "s \<noteq> 0"
  shows "fetch (A |+| B) s x = (a, Suc (length A div 2))"
  using h1 h2 h3
  apply(cases s;cases x)
  by(auto simp: seq_tm_length nth_append)

lemma seq_tm_exec_after_first:
  assumes h1: "\<not> is_final c" 
    and h2: "step0 c A = (0, tap)"
    and h3: "fst c \<le> length A div 2"
  shows "step0 c (A |+| B) = (Suc (length A div 2), tap)"
  using h1 h2 h3
  apply(case_tac c)
  apply(auto simp del: seq_tm.simps)
   apply(case_tac "fetch A a Bk")
   apply(simp del: seq_tm.simps)
   apply(subst seq_tm_fetch_in_A;force)
  apply(case_tac "fetch A a (hd ca)")
  apply(simp del: seq_tm.simps)
  apply(subst seq_tm_fetch_in_A)
     apply(auto)[4]
  done

(* if A goes into the final state, then A |+| B will go into the first state of B *)
lemma seq_tm_next: 
  assumes a_ht: "steps0 (1, tap) A n = (0, tap')"
    and a_composable: "composable_tm (A, 0)"
  obtains n' where "steps0 (1, tap) (A |+| B) n' = (Suc (length A div 2), tap')"
proof -
  assume a: "\<And>n. steps (1, tap) (A |+| B, 0) n = (Suc (length A div 2), tap') \<Longrightarrow> thesis"
  obtain stp' where fin: "\<not> is_final (steps0 (1, tap) A stp')" and h: "steps0 (1, tap) A (Suc stp') = (0, tap')"
    using before_final[OF a_ht] by blast
  from fin have h1:"steps0 (1, tap) (A |+| B) stp' = steps0 (1, tap) A stp'"
    by (rule seq_tm_steps)
  from h have h2: "step0 (steps0 (1, tap) A stp') A = (0, tap')"
    by (simp only: step_red)

  have "steps0 (1, tap) (A |+| B) (Suc stp') = step0 (steps0 (1, tap) (A |+| B) stp') (A |+| B)" 
    by (simp only: step_red)
  also have "... = step0 (steps0 (1, tap) A stp') (A |+| B)" using h1 by simp
  also have "... = (Suc (length A div 2), tap')" 
    by (rule seq_tm_exec_after_first[OF fin h2 steps_in_range[OF fin a_composable]])
  finally show thesis using a by blast
qed

lemma seq_tm_fetch_second_zero:
  assumes h1: "fetch B s x = (a, 0)"
    and hs: "composable_tm (A, 0)" "s \<noteq> 0"
  shows "fetch (A |+| B) (s + (length A div 2)) x = (a, 0)"
  using h1 hs
  by(cases x; cases s; fastforce simp: seq_tm_length nth_append)

lemma seq_tm_fetch_second_inst:
  assumes h1: "fetch B sa x = (a, s)"
    and hs: "composable_tm (A, 0)" "sa \<noteq> 0" "s \<noteq> 0"
  shows "fetch (A |+| B) (sa + length A div 2) x = (a, s + length A div 2)"
  using h1 hs
  by(cases x; cases sa; fastforce simp: seq_tm_length nth_append)


lemma seq_tm_second:
  assumes a_composable: "composable_tm (A, 0)"
    and steps: "steps0 (1, l, r) B stp = (s', l', r')"
  shows "steps0 (Suc (length A div 2), l, r)  (A |+| B) stp 
    = (if s' = 0 then 0 else s' + length A div 2, l', r')"
  using steps
proof(induct stp arbitrary: s' l' r')
  case 0
  then show ?case by simp
next
  case (Suc stp s' l' r')
  obtain s'' l'' r'' where a: "steps0 (1, l, r) B stp = (s'', l'', r'')"
    by (metis is_final.cases)
  then have ih1: "s'' = 0 \<Longrightarrow> steps0 (Suc (length A div 2), l, r) (A |+| B) stp = (0, l'', r'')"
    and ih2: "s'' \<noteq> 0 \<Longrightarrow> steps0 (Suc (length A div 2), l, r) (A |+| B) stp = (s'' + length A div 2, l'', r'')"
    using Suc by (auto)
  have h: "steps0 (1, l, r) B (Suc stp) = (s', l', r')" by fact

  { assume "s'' = 0"
    then have ?case using a h ih1 by (simp del: steps.simps) 
  } moreover
  { assume as: "s'' \<noteq> 0" "s' = 0"
    from as a h 
    have "step0 (s'', l'', r'') B = (0, l', r')" by (simp del: steps.simps)
    with as have ?case
      apply(cases "fetch B s'' (read r'')")
      by (auto simp add: seq_tm_fetch_second_zero[OF _ a_composable] ih2[OF as(1)]
          simp del: seq_tm.simps steps.simps)
  } moreover
  { assume as: "s'' \<noteq> 0" "s' \<noteq> 0"
    from as a h
    have "step0 (s'', l'', r'') B = (s', l', r')" by (simp del: steps.simps)
    with as have ?case
      apply(simp add: ih2[OF as(1)] del: seq_tm.simps steps.simps)
      apply(case_tac "fetch B s'' (read r'')")
      apply(auto simp add: seq_tm_fetch_second_inst[OF _ a_composable as] simp del: seq_tm.simps)
      done
  }
  ultimately show ?case by blast
qed

lemma seq_tm_final:
  assumes "composable_tm (A, 0)"  
    and "steps0 (1, l, r) B stp = (0, l', r')"
  shows "steps0 (Suc (length A div 2), l, r)  (A |+| B) stp = (0, l', r')"
  using seq_tm_second[OF assms] by (simp)

end

