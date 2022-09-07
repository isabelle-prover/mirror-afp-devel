(* Title: thys/SemiIdTM.thy
   Author: Franz Regensburger (FABR) 02/2022
 *)

section \<open>SemiId: Turing machines acting as partial identity functions\<close>

theory SemiIdTM
  imports Turing_Hoare
begin

(* Cleanup the global simpset *)

declare adjust.simps[simp del]

declare seq_tm.simps [simp del] 
declare shift.simps[simp del]
declare composable_tm.simps[simp del]
declare step.simps[simp del]
declare steps.simps[simp del]

subsection \<open>The Turing Machine tm\_semi\_id\_eq0\<close>

(* ---------------------------------------------------------- *)
(* Machine tm_semi_id_eq0                                     *)
(* ---------------------------------------------------------- *)
(*
The machine tm_semi_id_eq0
terminates on: Oc \<up> 1 with result Oc \<up> 1, which is the numeral <0>

     loops on: []      which is the empty input
     loops on: Oc \<up> n, where n \<ge> 2
*)

text \<open>
  If the input is @{term "Oc\<up>1"} the machine @{term "tm_semi_id_eq0"} will reach the
  final state in a standard configuration with output identical to its input.
  For other inputs @{term "Oc\<up>n"} with @{term "1 \<noteq> (n::nat)"} it will 
  loop forever.

  Please note that our short notation  @{term "<n::nat>"} means @{term "Oc\<up>(n+1)"}
  where @{term "0 \<le> (n::nat)"}.
\<close>

definition tm_semi_id_eq0 :: "instr list"
  where
    "tm_semi_id_eq0 \<equiv> [(WB, 1), (R, 2), (L, 0), (L, 1)]"

(* ------ Important properties used in subsequent theories ------ *)

lemma composable_tm0_tm_semi_id_eq0[intro, simp]: "composable_tm0 tm_semi_id_eq0"
  by (auto simp: composable_tm.simps tm_semi_id_eq0_def)

lemma tm_semi_id_eq0_loops_aux: 
  "(steps0 (1, [], [Oc, Oc]) tm_semi_id_eq0 stp = (1, [], [Oc, Oc])) \<or> 
   (steps0 (1, [], [Oc, Oc]) tm_semi_id_eq0 stp = (2, Oc # [], [Oc]))"
  by (induct stp) (auto simp: steps.simps step.simps tm_semi_id_eq0_def numeral_eqs_upto_12)

lemma tm_semi_id_eq0_loops_aux': 
  "(steps0 (1, [], [Oc, Oc] @ (Bk \<up> q)) tm_semi_id_eq0 stp = (1, [], [Oc,Oc] @ Bk \<up> q)) \<or> 
   (steps0 (1, [], [Oc, Oc] @ (Bk \<up> q)) tm_semi_id_eq0 stp = (2, Oc # [], [Oc] @ (Bk \<up> q)))"
  by (induct stp) (auto simp: steps.simps step.simps tm_semi_id_eq0_def numeral_eqs_upto_12)

lemma tm_semi_id_eq0_loops_aux'': 
  "(steps0 (1, [], [Oc, Oc] @ (Oc \<up> q) @ (Bk \<up> q)) tm_semi_id_eq0 stp = (1, [], [Oc,Oc] @ (Oc \<up> q) @ Bk \<up> q)) \<or> 
   (steps0 (1, [], [Oc, Oc] @ (Oc \<up> q) @ (Bk \<up> q)) tm_semi_id_eq0 stp = (2, Oc # [], [Oc] @ (Oc \<up> q) @ (Bk \<up> q)))"
  by (induct stp) (auto simp: steps.simps step.simps tm_semi_id_eq0_def numeral_eqs_upto_12)

lemma tm_semi_id_eq0_loops_aux''': 
  "(steps0 (1, [], []) tm_semi_id_eq0 stp = (1, [], [])) \<or> 
   (steps0 (1, [], []) tm_semi_id_eq0 stp = (1, [], [Bk]))"
  by (induct stp) (auto simp: steps.simps step.simps tm_semi_id_eq0_def numeral_eqs_upto_12)

(* ------ Auxiliary properties for clarification           ------ *)

lemma "<0::nat> = [Oc]" by (simp add: tape_of_nat_def)
lemma "Oc\<up>(0+1) = [Oc]" by (simp)
lemma "<n::nat> = Oc\<up>(n+1)" by (auto simp add: tape_of_nat_def)
lemma "<1::nat> = [Oc, Oc]" by (simp add: tape_of_nat_def)

subsubsection \<open>The machine tm\_semi\_id\_eq0 in action\<close>

(* steps0 (1, [], []) tm_semi_id_eq0 n loops forever in state 1 *)
lemma "steps0 (1, [], []) tm_semi_id_eq0 0 = (1, [], [])"   by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_eq0_def)
lemma "steps0 (1, [], []) tm_semi_id_eq0 1 = (1, [], [Bk])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_eq0_def)
lemma "steps0 (1, [], []) tm_semi_id_eq0 2 = (1, [], [Bk])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_eq0_def)
lemma "steps0 (1, [], []) tm_semi_id_eq0 3 = (1, [], [Bk])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_eq0_def)

(*     steps0 (1, [], [Oc]) tm_semi_id_eq0 n terminates after 2 steps with final configuration "(0, [], [Oc])" *)
lemma "steps0 (1, [], [Oc]) tm_semi_id_eq0 0 = (1, [], [Oc])" by (simp add: step.simps steps.simps tm_semi_id_eq0_def)
lemma "steps0 (1, [], [Oc]) tm_semi_id_eq0 1 = (2, [Oc], [])" by (simp add: step.simps steps.simps tm_semi_id_eq0_def)
lemma "steps0 (1, [], [Oc]) tm_semi_id_eq0 2 = (0, [], [Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_eq0_def)

(* steps0 (1, [], [Oc, Oc]) tm_semi_id_eq0 loops forever *)
lemma "steps0 (1, [], [Oc, Oc]) tm_semi_id_eq0 0 = (1, [], [Oc, Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_eq0_def)
lemma "steps0 (1, [], [Oc, Oc]) tm_semi_id_eq0 1 = (2, [Oc], [Oc])"   by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_eq0_def)
lemma "steps0 (1, [], [Oc, Oc]) tm_semi_id_eq0 2 = (1, [], [Oc, Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_eq0_def)
lemma "steps0 (1, [], [Oc, Oc]) tm_semi_id_eq0 3 = (2, [Oc], [Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_eq0_def)
lemma "steps0 (1, [], [Oc, Oc]) tm_semi_id_eq0 4 = (1, [], [Oc, Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_eq0_def)

subsection \<open>The Turing Machine tm\_semi\_id\_gt0\<close>

(* ---------------------------------------------------------- *)
(* Machine tm_semi_id_gt0                                     *)
(* ---------------------------------------------------------- *)
(*
The machine tm_semi_id_gt0 (aka dither) has behaviour that is complementary
to the behaviour of tm_semi_id_eq0.

The machine tm_semi_id_gt0
terminates on: Oc \<up> n  with result Oc \<up> n for 1 < n

     loops on: []     , which is the empty input
     loops on: Oc \<up> 1 , which is the numeral <0>
*)

text \<open>
  If the input is @{term "Oc\<up>0"} or @{term "Oc\<up>1"} the machine @{term "tm_semi_id_gt0"}
  (aka dither) will loop forever.
  For other non-blank inputs @{term "Oc\<up>n"} with @{term  "1 < (n::nat)"} it will 
  reach the final state in a standard configuration with output identical to its input.

  Please note that our short notation  @{term "<n::nat>"} means @{term "Oc\<up>(n+1)"}
  where @{term "0 \<le> (n::nat)"}.
\<close>

definition tm_semi_id_gt0 :: "instr list"
  where
    "tm_semi_id_gt0 \<equiv> [(WB, 1), (R, 2), (L, 1), (L, 0)]"

(* ------ Important properties used in subsequent theories ------ *)

lemma tm_semi_id_gt0[intro, simp]: "composable_tm0 tm_semi_id_gt0"
  by (auto simp: composable_tm.simps tm_semi_id_gt0_def)

lemma tm_semi_id_gt0_loops_aux: 
  "(steps0 (1, [], [Oc]) tm_semi_id_gt0 stp = (1, [], [Oc])) \<or> 
   (steps0 (1, [], [Oc]) tm_semi_id_gt0 stp = (2, Oc # [], []))"
  by (induct stp) (auto simp: steps.simps step.simps tm_semi_id_gt0_def numeral_eqs_upto_12)

lemma tm_semi_id_gt0_loops_aux': 
  "(steps0 (1, [], [Oc] @ Bk \<up> n) tm_semi_id_gt0 stp = (1, [], [Oc] @ Bk \<up> n)) \<or> 
   (steps0 (1, [], [Oc] @ Bk \<up> n) tm_semi_id_gt0 stp = (2, Oc # [], Bk \<up> n))"
  by (induct stp) (auto simp: steps.simps step.simps tm_semi_id_gt0_def numeral_eqs_upto_12)

lemma tm_semi_id_gt0_loops_aux''': 
  "(steps0 (1, [], []) tm_semi_id_gt0 stp = (1, [], [])) \<or> 
   (steps0 (1, [], []) tm_semi_id_gt0 stp = (1, [], [Bk]))"
  by (induct stp) (auto simp: steps.simps step.simps tm_semi_id_gt0_def numeral_eqs_upto_12)

subsubsection \<open>The machine tm\_semi\_id\_gt0 in action\<close>

(* steps0 (1, [], []) tm_semi_id_gt0 n loops forever in state 1 *)
lemma "steps0 (1, [], []) tm_semi_id_gt0 0 = (1, [], [])"   by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_gt0_def)
lemma "steps0 (1, [], []) tm_semi_id_gt0 1 = (1, [], [Bk])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_gt0_def)
lemma "steps0 (1, [], []) tm_semi_id_gt0 2 = (1, [], [Bk])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_gt0_def)
lemma "steps0 (1, [], []) tm_semi_id_gt0 3 = (1, [], [Bk])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_gt0_def)

(* steps0 (1, [], [Oc]) tm_semi_id_gt0 n loops forever; it dithers between states 1 and 2 *)
lemma "steps0 (1, [], [Oc]) tm_semi_id_gt0 0 = (1, [], [Oc])" by (simp add: step.simps steps.simps tm_semi_id_gt0_def)
lemma "steps0 (1, [], [Oc]) tm_semi_id_gt0 1 = (2, [Oc], [])" by (simp add: step.simps steps.simps tm_semi_id_gt0_def)
lemma "steps0 (1, [], [Oc]) tm_semi_id_gt0 2 = (1, [], [Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_gt0_def)
lemma "steps0 (1, [], [Oc]) tm_semi_id_gt0 3 = (2, [Oc], [])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_gt0_def)
lemma "steps0 (1, [], [Oc]) tm_semi_id_gt0 4 = (1, [], [Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_gt0_def)

(* steps0 (1, [], [Oc, Oc]) tm_semi_id_gt0 n terminates after 2 steps with final configuration "(0, [], [Oc, Oc])" *)
lemma "steps0 (1, [], [Oc, Oc]) tm_semi_id_gt0 0 = (1, [], [Oc, Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_gt0_def)
lemma "steps0 (1, [], [Oc, Oc]) tm_semi_id_gt0 1 = (2, [Oc], [Oc])"   by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_gt0_def)
lemma "steps0 (1, [], [Oc, Oc]) tm_semi_id_gt0 2 = (0, [], [Oc, Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_gt0_def)
lemma "steps0 (1, [], [Oc, Oc]) tm_semi_id_gt0 3 = (0, [], [Oc, Oc])" by (simp add: step.simps steps.simps numeral_eqs_upto_12 tm_semi_id_gt0_def)


subsection \<open>Properties of the SemiId machines\<close>

(*
declare adjust.simps[simp del]

declare seq_tm.simps [simp del] 
declare shift.simps[simp del]
declare composable_tm.simps[simp del]
declare step.simps[simp del]
declare steps.simps[simp del]
*)

text \<open>Using Hoare style rules is more elegant since they allow for compositional
 reasoning. Therefore, its preferable to use them, if the program that we reason about
 can be decomposed appropriately.\<close>

subsubsection \<open>Proving properties of tm\_semi\_id\_eq0 with Hoare Rules\<close>

lemma tm_semi_id_eq0_loops_Nil:
  shows "\<lbrace>\<lambda>tap. tap = ([], [])\<rbrace> tm_semi_id_eq0 \<up>"
  apply(rule Hoare_unhaltI)
  using tm_semi_id_eq0_loops_aux'''
  apply(auto simp add: numeral_eqs_upto_12 tape_of_nat_def)
  by (metis Suc_neq_Zero is_final_eq)

lemma tm_semi_id_eq0_loops:
  shows "\<lbrace>\<lambda>tap. tap = ([], <1::nat>)\<rbrace> tm_semi_id_eq0 \<up>"
  apply(rule Hoare_unhaltI)
  using tm_semi_id_eq0_loops_aux
  apply(auto simp add: numeral_eqs_upto_12 tape_of_nat_def)
  by (metis Suc_neq_Zero is_final_eq)

lemma tm_semi_id_eq0_loops':
  shows "\<lbrace>\<lambda>tap. \<exists>l. tap = ([], [Oc, Oc] @ Bk\<up> l)\<rbrace> tm_semi_id_eq0 \<up>"
  apply(rule Hoare_unhaltI)
  using tm_semi_id_eq0_loops_aux'
  apply(auto simp add: numeral_eqs_upto_12 tape_of_nat_def )
  by (metis Suc_neq_Zero is_final_eq)

lemma tm_semi_id_eq0_loops'':
  shows "\<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk\<up>k, [Oc, Oc] @ Bk\<up> l)\<rbrace> tm_semi_id_eq0 \<up>"
  apply(rule Hoare_unhaltI)
  using tm_semi_id_eq0_loops_aux'
  apply(auto simp add: numeral_eqs_upto_12 tape_of_nat_def)
  by (metis is_final_del_Bks Zero_neq_Suc is_final_eq)



lemma tm_semi_id_eq0_halts_aux:
  shows "steps0 (1, Bk \<up> m, [Oc]) tm_semi_id_eq0 2 = (0, Bk \<up> m, [Oc])"
  unfolding tm_semi_id_eq0_def
  by (simp add: steps.simps step.simps numeral_eqs_upto_12)

lemma tm_semi_id_eq0_halts_aux':
  shows "steps0 (1, Bk \<up> m, [Oc]@Bk \<up> n) tm_semi_id_eq0 2 = (0, Bk \<up> m, [Oc]@Bk \<up> n)"
  unfolding tm_semi_id_eq0_def
  by (simp add: steps.simps step.simps numeral_eqs_upto_12)

lemma tm_semi_id_eq0_halts:
  shows "\<lbrace>\<lambda>tap. tap = ([], <0::nat>)\<rbrace> tm_semi_id_eq0 \<lbrace>\<lambda>tap. tap = ([], <0::nat>)\<rbrace>"
  apply(rule Hoare_haltI)
  using tm_semi_id_eq0_halts_aux
  apply(auto simp add: tape_of_nat_def)
  by (metis (full_types) holds_for.simps is_finalI  replicate_0)

lemma tm_semi_id_eq0_halts':
  shows "\<lbrace>\<lambda>tap. \<exists>l. tap = ([], [Oc] @ Bk\<up> l)\<rbrace> tm_semi_id_eq0 \<lbrace>\<lambda>tap. \<exists>l. tap = ([], [Oc] @ Bk\<up> l)\<rbrace>"
  apply(rule Hoare_haltI)
  using tm_semi_id_eq0_halts_aux'
  apply(auto simp add: tape_of_nat_def)
  by (metis (mono_tags, lifting) holds_for.simps is_finalI numeral_1_eq_Suc_0 numeral_One replicate_0)

lemma tm_semi_id_eq0_halts'':
  shows "\<lbrace> \<lambda>tap. \<exists>k l. tap = (Bk\<up> k, [Oc] @ Bk\<up> l) \<rbrace> tm_semi_id_eq0 \<lbrace> \<lambda>tap. \<exists>k l. tap = (Bk\<up> k, [Oc] @ Bk\<up> l) \<rbrace>"
  apply(rule Hoare_haltI)
  using tm_semi_id_eq0_halts_aux'
  apply(auto simp add: tape_of_nat_def)
  by (metis (mono_tags, lifting) holds_for.simps is_finalI numeral_1_eq_Suc_0 numeral_One)

subsubsection \<open>Proving properties of tm\_semi\_id\_gt0 with Hoare Rules\<close>

lemma tm_semi_id_gt0_loops_Nil:
  shows "\<lbrace>\<lambda>tap. tap = ([], [])\<rbrace> tm_semi_id_gt0 \<up>"
  apply(rule Hoare_unhaltI)
  using tm_semi_id_gt0_loops_aux'''
  apply(auto simp add: numeral_eqs_upto_12 tape_of_nat_def)
  by (metis Suc_neq_Zero is_final_eq)

lemma tm_semi_id_gt0_loops:
  shows "\<lbrace>\<lambda>tap. tap = ([], <0::nat>)\<rbrace> tm_semi_id_gt0 \<up>"
  apply(rule Hoare_unhaltI)
  using tm_semi_id_gt0_loops_aux
  apply(auto simp add: numeral_eqs_upto_12 tape_of_nat_def)
  by (metis Suc_neq_Zero is_final_eq)

lemma tm_semi_id_gt0_loops':
  shows "\<lbrace>\<lambda>tap. \<exists>l. tap = ([], [Oc] @ Bk\<up> l)\<rbrace> tm_semi_id_gt0 \<up>"
  apply(rule Hoare_unhaltI)
  using tm_semi_id_gt0_loops_aux'
  apply(auto simp add: numeral_eqs_upto_12 tape_of_nat_def)
  by (metis Suc_neq_Zero is_final_eq)

lemma tm_semi_id_gt0_loops'':
  shows "\<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk\<up>k, [Oc] @ Bk\<up> l)\<rbrace> tm_semi_id_gt0 \<up>"
  apply(rule Hoare_unhaltI)
  using tm_semi_id_gt0_loops_aux'
  apply(auto simp add: numeral_eqs_upto_12 tape_of_nat_def)
  by (metis is_final_del_Bks Zero_neq_Suc is_final_eq)

lemma tm_semi_id_gt0_halts_aux:
  shows "steps0 (1, Bk \<up> m, [Oc, Oc]) tm_semi_id_gt0 2 = (0, Bk \<up> m, [Oc, Oc])"
  unfolding tm_semi_id_gt0_def
  by (simp add: steps.simps step.simps numeral_eqs_upto_12)

lemma tm_semi_id_gt0_halts_aux':
  shows "steps0 (1, Bk \<up> m, [Oc, Oc]@Bk \<up> n) tm_semi_id_gt0 2 = (0, Bk \<up> m, [Oc, Oc]@Bk \<up> n)"
  unfolding tm_semi_id_gt0_def
  by (simp add: steps.simps step.simps numeral_eqs_upto_12)

lemma tm_semi_id_gt0_halts:
  shows "\<lbrace>\<lambda>tap. tap = ([], <1::nat>)\<rbrace> tm_semi_id_gt0 \<lbrace>\<lambda>tap. tap = ([], <1::nat>)\<rbrace>"
  apply(rule Hoare_haltI)
  using tm_semi_id_gt0_halts_aux
  apply(auto simp add: tape_of_nat_def)
  by (metis (full_types) empty_replicate holds_for.simps is_final_eq numeral_2_eq_2)

lemma tm_semi_id_gt0_halts':
  shows "\<lbrace>\<lambda>tap. \<exists>l. tap = ([], [Oc, Oc] @ Bk\<up> l)\<rbrace> tm_semi_id_gt0 \<lbrace>\<lambda>tap. \<exists>l. tap = ([], [Oc, Oc] @ Bk\<up> l)\<rbrace>"
  apply(rule Hoare_haltI)
  using tm_semi_id_gt0_halts_aux'
  apply(auto simp add: tape_of_nat_def)
  by (metis (mono_tags, lifting) Suc_1 holds_for.simps is_finalI numeral_1_eq_Suc_0 numeral_One replicate_0)

lemma tm_semi_id_gt0_halts'':
  shows "\<lbrace> \<lambda>tap. \<exists>k l. tap = (Bk\<up> k, [Oc, Oc] @ Bk\<up> l)\<rbrace> tm_semi_id_gt0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk\<up> k, [Oc, Oc] @ Bk\<up> l)\<rbrace>"
  apply(rule Hoare_haltI)
  using tm_semi_id_gt0_halts_aux'
  apply(auto simp add: tape_of_nat_def)
  by (metis (mono_tags, lifting) Suc_1 holds_for.simps is_finalI numeral_1_eq_Suc_0 numeral_One)

end
