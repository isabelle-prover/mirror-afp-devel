(*  Title:      nominal_eqvt.ML
    Author:     Stefan Berghofer (original code)
    Author:     Christian Urban

    Automatic proofs for equivariance of inductive predicates.
*)


signature NOMINAL_EQVT =
sig
  val raw_equivariance: term list -> thm -> thm list -> Proof.context -> thm list
  val equivariance_cmd: string -> Proof.context -> local_theory
end

structure Nominal_Eqvt : NOMINAL_EQVT =
struct

open Nominal_Permeq;
open Nominal_ThmDecls;

fun atomize_conv ctxt =
  Raw_Simplifier.rewrite_cterm (true, false, false) (K (K NONE))
    (put_simpset HOL_basic_ss ctxt addsimps @{thms induct_atomize});
fun atomize_intr ctxt = Conv.fconv_rule (Conv.prems_conv ~1 (atomize_conv ctxt));
fun atomize_induct ctxt = Conv.fconv_rule (Conv.prems_conv ~1
  (Conv.params_conv ~1 (K (Conv.prems_conv ~1 (atomize_conv ctxt))) ctxt));


(** equivariance tactics **)

fun eqvt_rel_single_case_tac ctxt pred_names pi intro  = 
  let
    val thy = Proof_Context.theory_of ctxt
    val cpi = Thm.cterm_of thy pi
    val pi_intro_rule = Drule.instantiate' [] [NONE, SOME cpi] @{thm permute_boolI}
    val eqvt_sconfig = eqvt_strict_config addexcls pred_names
    val simpset1 =
      put_simpset HOL_basic_ss ctxt addsimps @{thms permute_fun_def permute_self split_paired_all}
    val simpset2 =
      put_simpset HOL_basic_ss ctxt addsimps @{thms permute_bool_def  permute_minus_cancel(2)}
  in
    eqvt_tac ctxt eqvt_sconfig THEN'
    SUBPROOF (fn {prems, context as ctxt, ...} =>
      let
        val prems' = map (transform_prem2 ctxt pred_names) prems
        val prems'' = map (fn thm => eqvt_rule ctxt eqvt_sconfig (thm RS pi_intro_rule)) prems'
        val prems''' = map (simplify simpset2 o simplify simpset1) prems''

      in
        HEADGOAL (rtac intro THEN_ALL_NEW resolve_tac (prems' @ prems'' @ prems''')) 
      end) ctxt
  end

fun eqvt_rel_tac ctxt pred_names pi induct intros =
  let
    val cases = map (eqvt_rel_single_case_tac ctxt pred_names pi) intros
  in
    EVERY' ((DETERM o rtac induct) :: cases)
  end


(** equivariance procedure *)

fun prepare_goal pi pred =
  let
    val (c, xs) = strip_comb pred;
  in
    HOLogic.mk_imp (pred, list_comb (c, map (mk_perm pi) xs))
  end

(* stores thm under name.eqvt and adds [eqvt]-attribute *)

fun get_name (Const (a, _)) = a
  | get_name (Free  (a, _)) = a

fun raw_equivariance pred_trms raw_induct intrs ctxt = 
  let
    val is_already_eqvt = 
      filter (is_eqvt ctxt) pred_trms
      |> map (Syntax.string_of_term ctxt)
    val _ = if null is_already_eqvt then ()
      else error ("Already equivariant: " ^ commas is_already_eqvt)

    val pred_names = map get_name pred_trms
    val raw_induct' = atomize_induct ctxt raw_induct
    val intrs' = map (atomize_intr ctxt) intrs
  
    val (([raw_concl], [raw_pi]), ctxt') = 
      ctxt 
      |> Variable.import_terms false [concl_of raw_induct'] 
      ||>> Variable.variant_fixes ["p"]
    val pi = Free (raw_pi, @{typ perm})
  
    val preds = map (fst o HOLogic.dest_imp)
      (HOLogic.dest_conj (HOLogic.dest_Trueprop raw_concl));
  
    val goal = HOLogic.mk_Trueprop 
      (foldr1 HOLogic.mk_conj (map (prepare_goal pi) preds)) 
  in 
    Goal.prove ctxt' [] [] goal 
      (fn {context,...} => eqvt_rel_tac context pred_names pi raw_induct' intrs' 1)
      |> Datatype_Aux.split_conj_thm 
      |> Proof_Context.export ctxt' ctxt
      |> map (fn th => th RS mp)
      |> map zero_var_indexes
  end


fun note_named_thm (name, thm) ctxt = 
  let
    val thm_name = Binding.qualified_name 
      (Long_Name.qualify (Long_Name.base_name name) "eqvt")
    val attr = Attrib.internal (K eqvt_add)
    val ((_, [thm']), ctxt') =  Local_Theory.note ((thm_name, [attr]), [thm]) ctxt
  in
    (thm', ctxt')
  end

fun equivariance_cmd pred_name ctxt =
  let
    val thy = Proof_Context.theory_of ctxt
    val ({names, ...}, {preds, raw_induct, intrs, ...}) =
      Inductive.the_inductive ctxt (Sign.intern_const thy pred_name)
    val thms = raw_equivariance preds raw_induct intrs ctxt 
  in
    fold_map note_named_thm (names ~~ thms) ctxt |> snd
  end


val _ =
  Outer_Syntax.local_theory @{command_spec "equivariance"}
    "Proves equivariance for inductive predicate involving nominal datatypes." 
      (Parse.xname >> equivariance_cmd)


end (* structure *)
