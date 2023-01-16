(* Title: thys/DitherTM.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
 
   Further contributions by Franz Regensburger (FABR) 02/2022 :
   * Re-ordering of sections;
     Now, the dithering machine is discussed before the tm_copy machine
   * Added comments

   Editorial note FABR:
   this file was part of the theory file Uncomputable.thy
   in the original AFP entry. 

 *)

section \<open>A Variation of the theme due to Boolos, Burgess and, Jeffrey\<close>

text \<open>In sections \ref{sec_K1_H1} and \ref{sec_K1_v} we discussed two variants of the proof
of the undecidability of the Sepcial Halting Problem. There, we used the Turing Machines
 @{term "tm_semi_id_eq0"} and @{term "tm_semi_id_gt0"} for the construction a contradiction.

The machine @{term "tm_semi_id_gt0"} is identical to the machine {\em dither}, which is discussed
in length together with the Turing Machine {\em copy} in the book
by Boolos, Burgess, and Jeffrey~\<^cite>\<open>"Boolos07"\<close>.

For backwards compatibility with the original AFP entry, we again present the formalization of
the machines{\em dither} and {\em copy} here in this section.
This allows for reuse of theory CopyTM, which in turn is referenced
in the original proof about the existence of an uncomputable function in theory
TuringUnComputable\_H2\_original.

In addition we present an enhanced version in theory TuringUnComputable\_H2, which is in
line with the principles of Conservative Extension.
\<close>

subsection \<open>The Dithering Turing Machine\<close>
(*
The machine tm_dither
terminates on: Oc \<up> n  with result Oc \<up> n for 1 < n

     loops on: []     which is the empty input
     loops on: Oc \<up> 1 which is the numeral <0>

*)

text \<open>
  If the input is empty or the numeral $<\!0\!>$,
  the {\em Dithering} TM will loop forever,
  otherwise it will terminate.
\<close>

theory DitherTM
  imports Turing_Hoare
begin

(* Cleanup the global simpset for proofs of several theorems about tm_dither *)

declare adjust.simps[simp del]

declare seq_tm.simps [simp del] 
declare shift.simps[simp del]
declare composable_tm.simps[simp del]
declare step.simps[simp del]
declare steps.simps[simp del]

definition tm_dither :: "instr list"
  where
    "tm_dither \<equiv> [(WB, 1), (R, 2), (L, 1), (L, 0)]"

(* ------ Important properties used in subsequent theories ------ *)

(* The dithering machine is well-formed *)

lemma composable_tm0_tm_dither[intro, simp]: "composable_tm0 tm_dither"
  by (auto simp: composable_tm.simps tm_dither_def)

lemma tm_dither_loops_aux: 
  "(steps0 (1, Bk \<up> m, [Oc]) tm_dither stp = (1, Bk \<up> m, [Oc])) \<or> 
   (steps0 (1, Bk \<up> m, [Oc]) tm_dither stp = (2, Oc # Bk \<up> m, []))"
  by (induct stp) (auto simp: steps.simps step.simps tm_dither_def numeral_eqs_upto_12)

lemma tm_dither_loops_aux': 
  "(steps0 (1, Bk \<up> m, [Oc] @ Bk \<up> n) tm_dither stp = (1, Bk \<up> m, [Oc] @ Bk \<up> n)) \<or> 
   (steps0 (1, Bk \<up> m, [Oc] @ Bk \<up> n) tm_dither stp = (2, Oc # Bk \<up> m, Bk \<up> n))"
  by (induct stp) (auto simp: steps.simps step.simps tm_dither_def numeral_eqs_upto_12)

(* ------ Auxiliary properties for clarification           ------ *)

text \<open>
  If the input is @{term "Oc\<up>1"} the {\em Dithering} TM will loop forever,
  for other non-blank inputs @{term "Oc\<up>(n+1)"} with @{term "1 < (n::nat)"} it will 
  reach the final state in a standard configuration.

  Please note that our short notation  @{term "<n::nat>"} means @{term "Oc\<up>(n+1)"}
  where @{term "0 \<le> (n::nat)"}.
\<close>

lemma "<0::nat> = [Oc]" by (simp add: tape_of_nat_def)
lemma "Oc\<up>(0+1) = [Oc]" by (simp)
lemma "<n::nat> = Oc\<up>(n+1)" by (auto simp add: tape_of_nat_def)

lemma "<1::nat> = [Oc, Oc]" by (simp add: tape_of_nat_def)

subsubsection \<open>Dither in action.\<close>

(* steps0 (1, [], [Oc]) tm_dither n loops forever for 0 \<le> n *)
lemma "steps0 (1, [], [Oc]) tm_dither 0 = (1, [], [Oc])" by (simp add: step.simps steps.simps tm_dither_def)
lemma "steps0 (1, [], [Oc]) tm_dither 1 = (2, [Oc], [])" by (simp add: step.simps steps.simps tm_dither_def)
lemma "steps0 (1, [], [Oc]) tm_dither 2 = (1, [], [Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_dither_def)
lemma "steps0 (1, [], [Oc]) tm_dither 3 = (2, [Oc], [])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_dither_def)
lemma "steps0 (1, [], [Oc]) tm_dither 4 = (1, [], [Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_dither_def)

(* steps0 (1, [], [Oc, Oc]) tm_dither n  terminates after 2 steps with final configuration "(0, [], [Oc, Oc])" *)
lemma "steps0 (1, [], [Oc, Oc]) tm_dither 0 = (1, [], [Oc, Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_dither_def)
lemma "steps0 (1, [], [Oc, Oc]) tm_dither 1 = (2, [Oc], [Oc])"   by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_dither_def)
lemma "steps0 (1, [], [Oc, Oc]) tm_dither 2 = (0, [], [Oc, Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_dither_def)
lemma "steps0 (1, [], [Oc, Oc]) tm_dither 3 = (0, [], [Oc, Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_dither_def)

(* steps0 (1, [], [Oc, Oc, Oc]) tm_dither n  terminates after 2 steps with final configuration "(0, [], [Oc, Oc, Oc])" *)
lemma "steps0 (1, [], [Oc, Oc, Oc]) tm_dither 0 = (1, [], [Oc, Oc, Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_dither_def)
lemma "steps0 (1, [], [Oc, Oc, Oc]) tm_dither 1 = (2, [Oc], [Oc, Oc])"   by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_dither_def)
lemma "steps0 (1, [], [Oc, Oc, Oc]) tm_dither 2 = (0, [], [Oc, Oc, Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_dither_def)
lemma "steps0 (1, [], [Oc, Oc, Oc]) tm_dither 3 = (0, [], [Oc, Oc, Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_dither_def)

subsubsection \<open>Proving properties of tm\_dither with Hoare rules\<close>

text \<open>Using Hoare style rules is more elegant since they allow for compositional
 reasoning. Therefore, its preferable to use them, if the program that we reason about
 can be decomposed appropriately.\<close>

(* Assertions and invariants of tm_dither *)
abbreviation (input)
  "tm_dither_halt_inv \<equiv> \<lambda>tap. \<exists>k. tap = (Bk \<up> k, <1::nat>)"

abbreviation (input)
  "tm_dither_unhalt_ass \<equiv> \<lambda>tap. \<exists>k. tap = (Bk \<up> k, <0::nat>)"

lemma "<0::nat> = [Oc]" by (simp add: tape_of_nat_def)

lemma tm_dither_loops: 
  shows "\<lbrace>tm_dither_unhalt_ass\<rbrace> tm_dither \<up>"
  apply(rule Hoare_unhaltI)
  using tm_dither_loops_aux
  apply(auto simp add: numeral_eqs_upto_12 tape_of_nat_def)
  by (metis Suc_neq_Zero is_final_eq)

lemma tm_dither_loops'':
  shows "\<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk\<up>k, [Oc] @ Bk\<up> l)\<rbrace> tm_dither \<up>"
  apply(rule Hoare_unhaltI)
  using tm_dither_loops_aux'
  apply(auto simp add: numeral_eqs_upto_12 tape_of_nat_def)
  by (metis Zero_neq_Suc is_final_eq)


lemma tm_dither_halts_aux:
  shows "steps0 (1, Bk \<up> m, [Oc, Oc]) tm_dither 2 = (0, Bk \<up> m, [Oc, Oc])"
  unfolding tm_dither_def
  by (simp add: steps.simps step.simps numeral_eqs_upto_12)

lemma tm_dither_halts_aux':
  shows "steps0 (1, Bk \<up> m, [Oc, Oc]@Bk \<up> n) tm_dither 2 = (0, Bk \<up> m, [Oc, Oc]@Bk \<up> n)"
  unfolding tm_dither_def
  by (simp add: steps.simps step.simps numeral_eqs_upto_12)

lemma tm_dither_halts: 
  shows "\<lbrace>tm_dither_halt_inv\<rbrace> tm_dither \<lbrace>tm_dither_halt_inv\<rbrace>"
  apply(rule Hoare_haltI)
  using tm_dither_halts_aux
  apply(auto simp add: tape_of_nat_def)
  by (metis (lifting, mono_tags) holds_for.simps is_final_eq)

lemma tm_dither_halts'':
  shows "\<lbrace> \<lambda>tap. \<exists>k l. tap = (Bk\<up> k, [Oc, Oc] @ Bk\<up> l)\<rbrace> tm_dither \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk\<up> k, [Oc, Oc] @ Bk\<up> l)\<rbrace>"
  apply(rule Hoare_haltI)
  using tm_dither_halts_aux'
  apply(auto simp add: tape_of_nat_def)
  by (metis (mono_tags, lifting) Suc_1 holds_for.simps is_finalI numeral_1_eq_Suc_0 numeral_One)

end
