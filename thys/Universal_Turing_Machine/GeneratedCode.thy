(* Title: thys/GeneratedCode.thy
   Author: Franz Regensburger (FABR) 03/2022
 *)

chapter \<open>Code extraction for interpreters and compilers\<close>

theory GeneratedCode
  imports HaltingProblems_K_H
          Abacus_Hoare
(*        "HOL-Library.Code_Target_Numeral" (* see doc codegen.pdf *) *)
          "HOL-Library.Code_Binary_Nat" (* see doc codegen.pdf *)

begin

(* Force full access to datatype cell by using a dummy function
 * This results in a modul export in Turing.hs
 *  force     :   Cell(..)
 *  instead of: Cell
 *)

fun 
  dummy_cellId :: "cell \<Rightarrow> cell"
  where
"dummy_cellId Oc = Oc" |
"dummy_cellId Bk = Bk"

(* Dito for abc_inst; Force full access to datatype *)

fun 
  dummy_abc_inst_Id :: " abc_inst \<Rightarrow> bool"
  where
"dummy_abc_inst_Id (Inc n) = True" |
"dummy_abc_inst_Id (Dec n s) = True" |
"dummy_abc_inst_Id (Goto n) = True"

(* Encoding of natural numbers as unary numerals *)

fun tape_of_nat_imp :: "nat \<Rightarrow> cell list"
  where
  "tape_of_nat_imp n = <n>"

fun tape_of_nat_list_imp :: "nat list \<Rightarrow> cell list"
  where
  "tape_of_nat_list_imp ns = <ns>"

(* ------------------- EXPORT CODE ------------------- *)

export_code  dummy_cellId
             step steps
             is_final
             mk_composable0 shift adjust seq_tm

             (* conversion of nat lists to numerals *)
             tape_of_nat_list_imp tape_of_nat_imp

             (* some Turing machines *)
             tm_semi_id_eq0 tm_semi_id_gt0
             tm_onestroke

             tm_copy_begin_orig tm_copy_loop_orig tm_copy_end_new
             tm_weak_copy

             tm_skip_first_arg tm_erase_right_then_dblBk_left
             tm_check_for_one_arg 

             tm_strong_copy

             (* interpreter for Abacus programs *)
             dummy_abc_inst_Id
             abc_step_l abc_steps_l
             abc_lm_v abc_lm_s abc_fetch
             abc_final abc_notfinal abc_out_of_prog

             (* --- compiler for Abacus programs *)
             layout_of start_of
             tinc tdec tgoto ci tpairs_of
             tm_of tms_of
             mopup_n_tm app_mopup

             (* --- SimpleGoedelEncoding --- *)
             tm_to_nat_list tm_to_nat
             nat_list_to_tm nat_to_tm

             num_of_nat num_of_integer

             list_encode list_decode prod_encode prod_decode
             triangle


  in Haskell file "HaskellCode/"

end
