(*  Title: thys/Recs_alt__Ex.thy
    Author: Franz Regensburger (FABR) 03/2022
 *)

section \<open>Examples for recursive functions using the alternative definitions\<close>

theory Recs_alt_Ex
  imports Recs_alt_Def
begin

(*
definition plus_2 :: "recf"
  where
    "plus_2 = (Cn 8 S [S])"      (* arity is deliberately and falsely set to 8 *)
*)

definition plus_2 :: "recf"
  where
    "plus_2 = (CN S [S])"  

lemma "rec_eval S [0] = Suc 0"
  by auto

lemma "rec_eval plus_2 [0] = rec_eval (Cn 8 S [S]) [0]" (* arity is not checked by rec_eval *)
  unfolding plus_2_def
  by auto

lemma "Cn 1 S [S] = CN S [S]"
  by auto

lemma "rec_eval plus_2 [0] = 2"
  unfolding plus_2_def
  by auto

lemma "rec_eval plus_2 [2] = 4"
  unfolding plus_2_def
  by auto

lemma "rec_eval plus_2 [0,4] = 2"  (* arity is not checked by rec_eval *)
  unfolding plus_2_def
  by auto

(* Q: what is the purpose of the arity parameter? 
 * A: the arity is needed for termination proofs.
 *    See the inductive predicate 'Recs.terminates'
 *)

(* --------------- from Recs.thy --------------- *)

(* 
definition
  "rec_add = PR (Id 1 0) (CN S [Id 3 1])"

lemma add_lemma:
  "rec_eval rec_add [x, y] =  x + y"
  by (induct x) (simp_all add: rec_add_def)

*)

(* but also *)

lemma add_lemma_more_args:
  "rec_eval rec_add ([x, y] @ z) =  x + y"
  by (induct x) (simp_all add: rec_add_def)

lemma "rec_eval (Pr v va vb) [] = undefined"
  by auto

lemma add_lemma_no_args:
  "rec_eval rec_add [] =  undefined"
  by (simp_all add: rec_add_def)


lemma add_lemma_one_arg:
  "rec_eval rec_add [x] =  undefined"
proof (induct x)
  case 0
(*
  then show ?case by (auto simp add: rec_add_def)

goal (1 subgoal):
 1. \<And>x. rec_eval rec_add [x] = undefined \<Longrightarrow> rec_eval rec_add [Suc x] = undefined 
Failed to finish proof\<^here>:
goal (1 subgoal):
 1. [] ! 0 = undefined
*)
  oops


lemma "[]!0 = undefined" (* how can we prove this one? *)
  oops

end
