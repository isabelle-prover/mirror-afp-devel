(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
Termination for recursive functions.
*)
theory FactorialTest
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

(* A fun fact *)
function fact :: "('n :: len) word \<Rightarrow> ('n :: len) word" where
  "fact n = (if n = 0 then 1 else n * fact (n - 1))"
  by auto
termination by (metis "termination" in_measure measure_unat wf_measure)
declare fact.simps [simp del]

lemma fact0 [simp]: "fact 0 = 1"
  by (subst fact.simps) simp

(* Parse the input file. *)
install_C_file "factorial.c"

autocorres [ts_rules=nondet]"factorial.c"

context ts_definition_factorial
begin
lemma "factorial' n \<bullet> s \<lbrace>\<lambda>Res r _. r = fact n\<rbrace>"
proof (induct n arbitrary: s rule: word_induct2)
  case zero
  then show ?case 
    apply (subst factorial'.simps)
    apply (runs_to_vcg)
    done
next
  case (suc n)
  show ?case
    apply (subst factorial'.simps)
    apply (runs_to_vcg)
    subgoal using suc(1) by simp
    subgoal using suc(1) 
      apply simp
      apply (rule runs_to_weaken)
       apply (rule suc(2))
      apply (auto simp add: fact.simps)
      done
    done
qed
end

end


