(*  Title:      trac.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section\<open>Support for the Trac Format\<close>
theory
  "trac"
imports
  trac_fp_parser
  trac_protocol_parser
keywords
      "trac" :: thy_decl
  and "trac_import" :: thy_decl
  and "print_transaction_strand" :: thy_decl
  and "print_transaction_strand_list" :: thy_decl
  and "print_attack_trace" :: thy_decl
  and "print_fixpoint" :: thy_decl
  and "save_fixpoint" :: thy_decl
  and "load_fixpoint" :: thy_decl
  and "protocol_model_setup" :: thy_decl
  and "protocol_security_proof" :: thy_decl
  and "protocol_composition_proof" :: thy_decl
  and "manual_protocol_model_setup" :: thy_decl
  and "manual_protocol_security_proof" :: thy_decl
  and "manual_protocol_composition_proof" :: thy_decl
  and "compute_fixpoint" :: thy_decl
  and "compute_SMP" :: thy_decl
  and "compute_shared_secrets" :: thy_decl
  and "setup_protocol_checks" :: thy_decl
begin

ML\<open>
val pspsp_timing = let
  val (pspsp_timing_config, pspsp_timing_setup) =
      Attrib.config_bool (Binding.name "pspsp_timing") (K false)
in
  Context.>>(Context.map_theory pspsp_timing_setup);
  pspsp_timing_config
end

structure trac_time = struct
  fun ap_thy thy msg f x = if Config.get_global thy pspsp_timing 
                               then Timing.timeap_msg ("PSPSP Timing: "^msg) f x  
                               else f x  
  fun ap_lthy lthy = ap_thy (Proof_Context.theory_of lthy)
end
\<close>


ML \<open>
(* Some of this is based on code from the following files distributed with Isabelle 2018:
    * HOL/Tools/value_command.ML
    * HOL/Code_Evaluation.thy
    * Pure.thy
*)

fun assert_nonempty_name n =
  if n = "" then error "Error: No name given" else n

fun is_defined lthy name = 
  let
    val full_name = Local_Theory.full_name lthy (Binding.name name)
    val thy = Proof_Context.theory_of lthy
  in
    Sign.const_type thy full_name <> NONE
  end

fun protocol_model_interpretation_defs name = 
  let
    fun f s =
      (Binding.empty_atts:Attrib.binding, ((Binding.name s, NoSyn), name ^ "." ^ s))
  in
    (map f [
      "public", "arity", "Ana", "\<Gamma>", "\<Gamma>\<^sub>v", "timpls_transformable_to", "intruder_synth_mod_timpls",
      "analyzed_closed_mod_timpls", "timpls_transformable_to'", "intruder_synth_mod_timpls'",
      "analyzed_closed_mod_timpls'", "admissible_transaction_checks",
      "admissible_transaction_updates", "admissible_transaction_terms", "admissible_transaction",
      "admissible_transaction'", "admissible_transaction_no_occurs_msgs",
      "admissible_transaction_send_occurs_form", "admissible_transaction_occurs_checks",
      "has_initial_value_producing_transaction", "add_occurs_msgs",
      "abs_substs_set", "abs_substs_fun", "in_trancl", "transaction_poschecks_comp",
      "transaction_negchecks_comp", "transaction_check_comp", "transaction_check'",
      "transaction_check", "transaction_check_pre", "transaction_check_post",
      "compute_fixpoint_fun'", "compute_fixpoint_fun", "compute_fixpoint_with_trace",
      "compute_fixpoint_from_trace", "compute_reduced_attack_trace", "attack_notin_fixpoint",
      "protocol_covered_by_fixpoint", "reduce_fixpoint'", "reduce_fixpoint", "analyzed_fixpoint",
      "wellformed_protocol''", "wellformed_protocol'", "wellformed_protocol",
      "wellformed_protocol_SMP_set", "wellformed_fixpoint", "wellformed_fixpoint'",
      "wellformed_term_implication_graph", "wellformed_composable_protocols",
      "wellformed_composable_protocols'", "composable_protocols",
      "welltyped_leakage_free_invkey_conditions'", "welltyped_leakage_free_invkey_conditions",
      "fun_point_inter", "fun_point_Inter", "fun_point_union", "fun_point_Union", "ticl_abs",
      "ticl_abss", "match_abss'", "match_abss", "synth_abs_substs_constrs_aux",
      "synth_abs_substs_constrs", "transaction_check_coverage_rcv", "protocol_covered_by_fixpoint_coverage_rcv"
    ]):string Interpretation.defines
 end

fun assert_defined lthy def =
  if is_defined lthy def then ()
  else error ("Error: The constant " ^ def ^ " is not defined.")

fun assert_not_defined lthy def =
  if not (is_defined lthy def) then ()
  else error ("Error: The constant " ^ def ^ " has already been defined.")

fun assert_all_defined lthy name defs =
  let
    fun errmsg s =
      "Error: The following constants were expected to be defined, but are not:\n" ^
      String.concatWith ", " s ^
      "\n\nProbable causes:\n" ^
      "1. The trac command failed to parse the protocol specification.\n" ^
      "2. The provided protocol-specification name (" ^ name ^ ") " ^
      "does not match the name given in the trac specification.\n" ^
      "3. Manually provided parameters (e.g., " ^ name ^ "_fixpoint, " ^ name ^ "_SMP) " ^
      "may have been misspelled.\n" ^
      "4. Any of the following commands were used before a call to the (manual_)" ^
      "protocol_model_setup command:\n" ^
      "   compute_fixpoint, compute_SMP, protocol_security_proof, manual_protocol_security_proof"
    val undefs = filter (not o is_defined lthy) defs
  in
    if null undefs then defs else error (errmsg undefs)
  end

fun protocol_model_interpretation_params name lthy =
  let
    fun f s = name ^ "_" ^ s
    val defs = [f "arity", f "sets_arity", f "public", f "Ana", f "\<Gamma>"]
    val _ = assert_all_defined lthy name defs
  in
    map SOME (defs@["0::nat", "1::nat"])
  end

fun declare_thm_attr attribute name print lthy =
  let 
    val arg = [(Facts.named name, [[Token.make_string (attribute, Position.none)]])]
    val (_, lthy') = Specification.theorems_cmd "" [(Binding.empty_atts, arg)] [] print lthy
  in
    lthy'
  end

fun declare_def_attr attribute name = declare_thm_attr attribute (name ^ "_def")

val declare_code_eqn = declare_def_attr "code"

val declare_protocol_check = declare_def_attr "protocol_checks"

fun declare_protocol_checks print =
  declare_protocol_check "attack_notin_fixpoint" print #>
  declare_protocol_check "protocol_covered_by_fixpoint" print #>
  declare_protocol_check "protocol_covered_by_fixpoint_coverage_rcv" print #>
  declare_protocol_check "analyzed_fixpoint" print #>
  declare_protocol_check "has_initial_value_producing_transaction" print #>
  declare_protocol_check "wellformed_protocol''" print #>
  declare_protocol_check "wellformed_protocol'" print #>
  declare_protocol_check "wellformed_protocol" print #>
  declare_protocol_check "wellformed_fixpoint'" print #>
  declare_protocol_check "wellformed_fixpoint" print #>
  declare_protocol_check "compute_fixpoint_fun" print

fun eval_term lthy t =
  Code_Evaluation.dynamic_value_strict lthy t

fun eval_define_declare (name, t) print lthy = 
  let 
    val t' = eval_term lthy t
    val arg = ((Binding.name name, NoSyn), ((Binding.name (name ^ "_def"),@{attributes [code]}), t'))
    val lthy' =  snd ( Local_Theory.begin_nested lthy )
    val (_, lthy'') = Local_Theory.define arg lthy'
  in
    (t', Local_Theory.end_nested lthy'')
  end

fun eval_define_declare_nbe (name, t) print lthy = 
  let 
    val t' = Nbe.dynamic_value lthy t
    val arg = ((Binding.name name, NoSyn), ((Binding.name (name ^ "_def"),@{attributes [code]}), t'))
    val lthy' =  snd ( Local_Theory.begin_nested lthy )
    val (_, lthy'') = Local_Theory.define arg lthy'
  in
    (t', Local_Theory.end_nested lthy'')
  end
\<close>

ML\<open>
structure ml_isar_wrapper = struct
  fun define_constant_definition' (constname, trm) print lthy = 
    let
      val lthy' =  snd ( Local_Theory.begin_nested lthy )
      val arg = ((Binding.name constname, NoSyn), ((Binding.name (constname^"_def"),@{attributes [code]}), trm))
      val ((_, (_ , thm)), lthy'') = Local_Theory.define arg lthy'
    in
      (thm, Local_Theory.end_nested lthy'')
    end

  fun define_simple_abbrev (constname, trm) lthy = 
    let
      val arg = ((Binding.name constname, NoSyn), trm)
      val ((_, _), lthy') = Local_Theory.abbrev Syntax.mode_default arg lthy
    in
      lthy'
    end

  fun define_simple_type_synonym (name, typedecl) lthy = 
    let
      val (_, lthy') = Typedecl.abbrev_global (Binding.name name, [], NoSyn) typedecl lthy
    in
      lthy'
    end

  fun define_simple_datatype (dt_tyargs, dt_name) constructors =
    let
      val options = Plugin_Name.default_filter
      fun lift_c (tyargs, name) =  (((Binding.empty, Binding.name name), map (fn t => (Binding.empty, t)) tyargs), NoSyn)
      val c_spec = map lift_c constructors
      val datatyp = ((map (fn ty => (NONE, ty)) dt_tyargs, Binding.name dt_name), NoSyn) 
      val dtspec =
        ((options,false),
         [(((datatyp, c_spec), (Binding.empty, Binding.empty, Binding.empty)), [])])
    in
      BNF_FP_Def_Sugar.co_datatypes BNF_Util.Least_FP BNF_LFP.construct_lfp dtspec
    end

   fun define_simple_primrec pname precs lthy = 
     let
       val rec_eqs = map (fn (lhs,rhs) => (((Binding.empty,[]), HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs,rhs))),[],[])) precs 
     in
       snd (BNF_LFP_Rec_Sugar.primrec false [] [(Binding.name pname, NONE, NoSyn)] rec_eqs lthy)
     end

   fun define_simple_fun pname precs lthy = 
     let
       val rec_eqs = map (fn (lhs,rhs) => (((Binding.empty,[]), HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs,rhs))),[],[])) precs 
     in
       Function_Fun.add_fun [(Binding.name pname, NONE, NoSyn)] rec_eqs  Function_Common.default_config lthy
     end

   fun prove_simple name stmt tactic lthy = 
     let
       val thm = Goal.prove lthy [] [] stmt (fn {context, ...} => tactic context) 
                 |> Goal.norm_result lthy
                 |> Goal.check_finished lthy
     in 
       lthy |>
       snd o  Local_Theory.note ((Binding.name name, []), [thm])
     end

    fun prove_state_simple method proof_state = 
           Seq.the_result "error in proof state" ( (Proof.refine method proof_state))
               |> Proof.global_done_proof 

end
\<close>

ML\<open>

structure trac_definitorial_package = struct
  type hide_tvar_tab = (TracProtocol.protocol) Symtab.table
  fun trac_eq (a, a') = (#name a) = (#name a')
  fun merge_trac_tab (tab,tab') = Symtab.merge trac_eq (tab,tab')
  structure Data = Generic_Data
  (
    type T = hide_tvar_tab
    val empty  = Symtab.empty:hide_tvar_tab
    val extend = I
    fun merge(t1,t2)  = merge_trac_tab (t1, t2)
  );

  fun update  p thy = Context.theory_of 
                        ((Data.map (fn tab => Symtab.update (#name p, p) tab) (Context.Theory thy)))
  fun lookup name thy = (Symtab.lookup ((Data.get o Context.Theory) thy) name,thy)

  fun lookup_trac (pname:string) lthy =
    Option.valOf (fst (lookup pname (Proof_Context.theory_of lthy)))

  (* constant names *)
  open Trac_Utils
  val enum_constsN="enum_consts"
  val setsN="sets"
  val funN="fun"
  val atomN="atom"
  val arityN="arity"
  val set_arityN=setsN^"_"^arityN
  val publicN = "public"
  val gammaN = "\<Gamma>"
  val anaN = "Ana"

  fun mk_listT T =  Type ("List.list", [T])
  val mk_setT = HOLogic.mk_setT
  val boolT = HOLogic.boolT
  val natT = HOLogic.natT
  val mk_tupleT =  HOLogic.mk_tupleT
  val mk_prodT = HOLogic.mk_prodT

  val mk_set = HOLogic.mk_set
  val mk_list = HOLogic.mk_list
  val mk_nat = HOLogic.mk_nat
  val mk_eq = HOLogic.mk_eq
  val mk_Trueprop = HOLogic.mk_Trueprop
  val mk_tuple = HOLogic.mk_tuple
  val mk_prod = HOLogic.mk_prod

  fun mkN (a,b) = a^"_"^b

  val info = Output.information

  fun full_name name lthy =
    Local_Theory.full_name lthy (Binding.name name)

  fun full_name' n (trac:TracProtocolCert.cProtocol) lthy = full_name (mkN (#name trac, n)) lthy

  fun mk_prot_type name targs (trac:TracProtocolCert.cProtocol) lthy =
    Term.Type (full_name' name trac lthy, targs)

  val enum_constsT = mk_prot_type enum_constsN []

  fun mk_enum_const a trac lthy =
    Term.Const (full_name' enum_constsN trac lthy ^ "." ^ a, enum_constsT trac lthy)

  val setexprT = mk_prot_type setsN []

  val funT = mk_prot_type funN []

  val atomT = mk_prot_type atomN []

  fun messageT (trac:TracProtocolCert.cProtocol) lthy =
    Term.Type ("Transactions.prot_term", [funT trac lthy, atomT trac lthy, setexprT trac lthy, natT])

  fun message_funT (trac:TracProtocolCert.cProtocol) lthy =
    Term.Type ("Transactions.prot_fun", [funT trac lthy, atomT trac lthy, setexprT trac lthy, natT])

  fun message_varT (trac:TracProtocolCert.cProtocol) lthy =
    Term.Type ("Transactions.prot_var", [funT trac lthy, atomT trac lthy, setexprT trac lthy, natT])

  fun message_term_typeT (trac:TracProtocolCert.cProtocol) lthy =
    Term.Type ("Transactions.prot_term_type",
               [funT trac lthy, atomT trac lthy, setexprT trac lthy, natT])

  fun message_term_type_listT (trac:TracProtocolCert.cProtocol) lthy =
    mk_listT (message_term_typeT trac lthy)

  fun message_atomT (trac:TracProtocolCert.cProtocol) lthy =
    Term.Type ("Transactions.prot_atom", [atomT trac lthy])

  fun messageT' varT (trac:TracProtocolCert.cProtocol) lthy =
    Term.Type ("Term.term", [message_funT trac lthy, varT])

  fun message_listT (trac:TracProtocolCert.cProtocol) lthy =
    mk_listT (messageT trac lthy)

  fun message_listT' varT (trac:TracProtocolCert.cProtocol) lthy =
    mk_listT (messageT' varT trac lthy)

  fun absT (trac:TracProtocolCert.cProtocol) lthy =
    mk_setT (setexprT trac lthy)

  fun abssT (trac:TracProtocolCert.cProtocol) lthy =
    mk_setT (absT trac lthy)

  val poscheckvariantT =
    Term.Type ("Strands_and_Constraints.poscheckvariant", [])

  val strand_labelT =
    Term.Type ("Labeled_Strands.strand_label", [natT])

  fun strand_stepT (trac:TracProtocolCert.cProtocol) lthy =
    Term.Type ("Stateful_Strands.stateful_strand_step",
               [message_funT trac lthy, message_varT trac lthy])

  fun labeled_strand_stepT (trac:TracProtocolCert.cProtocol) lthy =
    mk_prodT (strand_labelT, strand_stepT trac lthy)

  fun prot_strandT (trac:TracProtocolCert.cProtocol) lthy =
    mk_listT (labeled_strand_stepT trac lthy)

  fun prot_transactionT (trac:TracProtocolCert.cProtocol) lthy =
    Term.Type ("Transactions.prot_transaction",
               [funT trac lthy, atomT trac lthy, setexprT trac lthy, natT])

  val mk_star_label =
    Term.Const ("Labeled_Strands.strand_label.LabelS", strand_labelT)

  fun mk_prot_label (lbl:int) =
    Term.Const ("Labeled_Strands.strand_label.LabelN", natT --> strand_labelT) $
      mk_nat lbl

  fun mk_labeled_step (label:term) (step:term) =
    mk_prod (label, step)

  fun mk_Send_step (trac:TracProtocolCert.cProtocol) lthy (label:term) (msgs:term list) =
    mk_labeled_step label
      (Term.Const ("Stateful_Strands.stateful_strand_step.Send",
                   mk_listT (messageT trac lthy) --> strand_stepT trac lthy) $
                    mk_list (messageT trac lthy) msgs)

  fun mk_Receive_step (trac:TracProtocolCert.cProtocol) lthy (label:term) (msgs:term list) =
    mk_labeled_step label
      (Term.Const ("Stateful_Strands.stateful_strand_step.Receive",
                   mk_listT (messageT trac lthy) --> strand_stepT trac lthy) $
                    mk_list (messageT trac lthy) msgs)

  fun mk_InSet_step (trac:TracProtocolCert.cProtocol) lthy psv (label:term) (elem:term) (set:term) =
    let
      val psT = [poscheckvariantT, messageT trac lthy, messageT trac lthy]
      val psvN =
        case psv of TracProtocolCert.cCheck => "Check" | TracProtocolCert.cAssignment => "Assign"
    in
      mk_labeled_step label
        (Term.Const ("Stateful_Strands.stateful_strand_step.InSet",
                     psT ---> strand_stepT trac lthy) $
         Term.Const ("Strands_and_Constraints.poscheckvariant." ^ psvN, poscheckvariantT) $
         elem $ set)
    end

  fun mk_NegChecks_step (trac:TracProtocolCert.cProtocol) lthy (label:term)
                        (bvars:term list) (ineqs:(term*term) list) (notins:(term*term) list) =
    let
      val msgT = messageT trac lthy
      val varT = message_varT trac lthy
      val trm_prodT = mk_prodT (messageT trac lthy, messageT trac lthy)
      val psT = [mk_listT varT, mk_listT trm_prodT, mk_listT trm_prodT]
    in
      mk_labeled_step label
        (Term.Const ("Stateful_Strands.stateful_strand_step.NegChecks",
                     psT ---> strand_stepT trac lthy) $
         (case bvars of
            [] => mk_list varT []
          | [x] => mk_list varT [Term.Const (@{const_name "the_Var"}, msgT --> varT) $ x]
          | xs =>
              Term.Const (@{const_name "map"}, [msgT --> varT, mk_listT msgT] ---> mk_listT varT) $
              Term.Const (@{const_name "the_Var"}, msgT --> varT) $
              mk_list msgT xs) $
         mk_list trm_prodT (map mk_prod ineqs) $
         mk_list trm_prodT (map mk_prod notins))
    end

  fun mk_NotInSet_step (trac:TracProtocolCert.cProtocol) lthy (label:term) (elem:term) (set:term) =
    mk_NegChecks_step trac lthy label [] [] [(elem,set)]

  fun mk_Equality_step (trac:TracProtocolCert.cProtocol) lthy psv (label:term) (t1:term) (t2:term) =
    let
      val psT = [poscheckvariantT, messageT trac lthy, messageT trac lthy]
      val psvN =
        case psv of TracProtocolCert.cCheck => "Check" | TracProtocolCert.cAssignment => "Assign"
    in
      mk_labeled_step label
        (Term.Const ("Stateful_Strands.stateful_strand_step.Equality",
                     psT ---> strand_stepT trac lthy) $
         Term.Const ("Strands_and_Constraints.poscheckvariant." ^ psvN, poscheckvariantT) $ t1 $ t2)
    end

  fun mk_Insert_step (trac:TracProtocolCert.cProtocol) lthy (label:term) (elem:term) (set:term) =
    mk_labeled_step label
      (Term.Const ("Stateful_Strands.stateful_strand_step.Insert",
                   [messageT trac lthy, messageT trac lthy] ---> strand_stepT trac lthy) $
       elem $ set)

  fun mk_Delete_step (trac:TracProtocolCert.cProtocol) lthy (label:term) (elem:term) (set:term) =
    mk_labeled_step label
      (Term.Const ("Stateful_Strands.stateful_strand_step.Delete",
                   [messageT trac lthy, messageT trac lthy] ---> strand_stepT trac lthy) $
       elem $ set)

  fun mk_Transaction (trac:TracProtocolCert.cProtocol) lthy S0 S1 S2 S3 S4 S5 S6 =
    let
      val varT = message_varT trac lthy
      val msgT = messageT trac lthy
      val var_listT = mk_listT varT
      val msg_listT = mk_listT msgT
      val fun_setT = mk_setT (funT trac lthy)
      val trT = prot_transactionT trac lthy
      val declT = mk_prodT (varT, fun_setT)
      val decl_listT = mk_listT declT
      val decl_list_funT = HOLogic.unitT --> decl_listT
      val stepT = labeled_strand_stepT trac lthy
      val strandT = prot_strandT trac lthy
      val strandsT = mk_listT strandT
      val paramsT = [decl_list_funT, var_listT, strandT, strandT, strandT, strandT]
    in
      Term.Const ("Transactions.prot_transaction.Transaction", paramsT ---> trT) $
      (Term.Const ("Product_Type.unit.case_unit", decl_listT --> decl_list_funT) $
       mk_list declT S0) $
      (if null S4 then mk_list varT []
       else Term.Const (@{const_name "map"}, [msgT --> varT, msg_listT] ---> var_listT) $
            Term.Const (@{const_name "the_Var"}, msgT --> varT) $
            mk_list msgT S4) $
      mk_list stepT S1 $
      (if null S3 then mk_list stepT S2
       else Term.Const (@{const_name "append"}, [strandT,strandT] ---> strandT) $
            mk_list stepT S2 $
            (Term.Const (@{const_name "concat"}, strandsT --> strandT) $ mk_list strandT S3)) $
      mk_list stepT S5 $
      mk_list stepT S6
    end

  fun get_funs (trac:TracProtocolCert.cProtocol) =
      case #function_spec trac of
        NONE => ([],[],[])
      | SOME ({public_funs=pub_funs, public_consts=pub_consts, private_consts=priv_consts}) =>
          (pub_funs, pub_consts, priv_consts)

  (* TODO: consider differentiating between "/" sets and "//" sets *)
  fun get_set_spec (trac:TracProtocolCert.cProtocol) =
    distinct (op =) (map (fn (s,n,_) => (s,n)) (#set_spec trac))

  fun get_general_set_family_set_spec (trac:TracProtocolCert.cProtocol) =
    distinct (op =) (map_filter (fn (s,n,b) => if b then SOME (s,n) else NONE) (#set_spec trac))

  fun is_general_set_family (trac:TracProtocolCert.cProtocol) s =
    List.exists (fn (s',_) => s = s') (get_general_set_family_set_spec trac)

  fun set_arity (trac:TracProtocolCert.cProtocol) s =
    case List.find (fn x => fst x = s) (get_set_spec trac) of
      SOME (_,n) => SOME n
    | NONE => NONE

  fun get_enum_consts (trac:TracProtocolCert.cProtocol) =
    distinct (op =) (List.concat (map #2 (#enum_spec trac)))

  fun get_finite_enum_spec (trac:TracProtocolCert.cProtocol) =
    filter (null o #3) (#enum_spec trac)

  fun get_infinite_enum_spec (trac:TracProtocolCert.cProtocol) =
    filter_out (null o #3) (#enum_spec trac)

  fun get_nonunion_infinite_enum_spec (trac:TracProtocolCert.cProtocol) =
    filter (fn (e,cs,ies) => null cs andalso ies = [e])
           (get_infinite_enum_spec trac)

  fun get_typed_constants_in_function_spec (trac:TracProtocolCert.cProtocol) =
    case #function_spec trac of
      SOME {private_consts=priv, public_consts=pub, ...} =>
        map_filter (fn (c,t) => Option.map (fn a => (c,a)) t) (priv@pub)
    | NONE => []

  fun get_user_atom_spec_pre (trac:TracProtocolCert.cProtocol) =
    map (fn s => (s,([boolT,natT],s^"_constant"))) (#type_spec trac)

  fun get_user_atom_spec (trac:TracProtocolCert.cProtocol) =
    map (fn (c,a) => (a,([],c))) (get_typed_constants_in_function_spec trac)@
    get_user_atom_spec_pre trac

  fun is_attack_transaction (tr:TracProtocolCert.cTransaction) =
    not (null (#attack_actions tr))

  fun get_transaction_name (tr:TracProtocolCert.cTransaction) =
    #1 (#transaction tr)

  fun get_transaction_head_variables (tr:TracProtocolCert.cTransaction) =
    #2 (#transaction tr)

  fun get_bound_variables (tr:TracProtocolCert.cTransaction) =
    let
      val a = map_filter (TracProtocolCert.maybe_the_NegChecks o snd) (#checksingle_actions tr)
    in
      distinct (op =) (List.concat (map fst a))
    end

  fun get_fresh_variables (tr:TracProtocolCert.cTransaction) =
    List.concat (map_filter (TracProtocolCert.maybe_the_Fresh o snd) (#fresh_actions tr))

  fun get_fresh_value_variables (tr:TracProtocolCert.cTransaction) =
    map_filter (fn (x,tau) => case tau of Trac_Term.ValueType => SOME x | _ => NONE)
               (get_fresh_variables tr)

  fun get_nonfresh_value_variables (tr:TracProtocolCert.cTransaction) =
    map fst (filter (fn x => snd x = Trac_Term.ValueType) (get_transaction_head_variables tr))

  fun get_value_variables (tr:TracProtocolCert.cTransaction) =
    get_nonfresh_value_variables tr@get_fresh_value_variables tr

  fun get_finite_enum_variables (tr:TracProtocolCert.cTransaction) =
    distinct (op =) (filter (fn (_,tau) => case tau of
                                              Trac_Term.Enumeration _ => true
                                            | _ => false)
                            (get_transaction_head_variables tr))

  fun get_infinite_enum_variables (tr:TracProtocolCert.cTransaction) =
    distinct (op =) (filter (fn (_,tau) => case tau of
                                              Trac_Term.InfiniteEnumeration _ => true
                                            | _ => false)
                            (get_transaction_head_variables tr))


  fun get_enumtype_variables (tr:TracProtocolCert.cTransaction) =
    distinct (op =) (filter (fn (_,tau) => tau = Trac_Term.EnumType)
                            (get_transaction_head_variables tr))

  fun get_nonenum_variables (tr:TracProtocolCert.cTransaction) =
    map_filter (fn (x,tau) => case tau of
                    Trac_Term.Enumeration _ => NONE
                  | Trac_Term.InfiniteEnumeration _ => NONE
                  | _ => SOME (x,tau))
               (get_transaction_head_variables tr@get_fresh_variables tr)

  fun get_variable_restrictions (tr:TracProtocolCert.cTransaction) =
    let
      val enum_vars = get_finite_enum_variables tr
      val value_vars = get_value_variables tr
      fun enum_member x = List.exists (fn y => x = fst y)
      fun value_member x = List.exists (fn y => x = y)
      fun aux [] = ([],[])
        | aux ((a,b)::rs) =
            if enum_member a enum_vars andalso enum_member b enum_vars
            then let val (es,vs) = aux rs in ((a,b)::es,vs) end
            else if value_member a value_vars andalso value_member b value_vars
            then let val (es,vs) = aux rs in (es,(a,b)::vs) end
            else error ("Error: Ill-formed or ill-typed variable restriction: " ^ a ^ " != " ^ b)
    in
      aux (#3 (#transaction tr))
    end

  fun setexpr_to_hol (db:string * Trac_Term.cMsg list) (trac:TracProtocolCert.cProtocol) lthy =
    let
      open Trac_Term
      fun mkN' n = mkN (#name trac, n)
      val s_prefix = full_name (mkN' setsN) lthy ^ "."
      val e_prefix = full_name (mkN' enum_constsN) lthy ^ "."
      val (s,es) = db
      val tau = enum_constsT trac lthy
      val setexprT = setexprT trac lthy
      val a = Term.Const (s_prefix ^ s, map (fn _ => tau) es ---> setexprT)
      fun param_to_hol (cVar (x,Enumeration _)) = Term.Free (x, tau)
        | param_to_hol (cVar (x,EnumType)) = Term.Free (x, tau)
        | param_to_hol (cEnum e) = Term.Const (e_prefix ^ e, tau)
        | param_to_hol t = error ("Error: Invalid set parameter: " ^ cMsg_str t)
    in
      fold (fn e => fn b => b $ param_to_hol e) es a
    end

  fun abs_to_hol (bs:(string * string list) list) (trac:TracProtocolCert.cProtocol) lthy =
    mk_set (setexprT trac lthy)
           (map (fn (s,cs) => setexpr_to_hol (s, map Trac_Term.cEnum cs) trac lthy) bs)

  fun cType_to_hol (t:Trac_Term.cType) trac lthy =
    let
      open Trac_Term
      val atomT = atomT trac lthy
      val prot_atomT = message_atomT trac lthy
      val tT = message_term_typeT trac lthy
      val fT = message_funT trac lthy
      val tsT = message_term_type_listT trac lthy
      val TAtomT = prot_atomT --> tT
      val TCompT = [fT, tsT] ---> tT
      val funT = funT trac lthy
      val setexprT = setexprT trac lthy
      val SetT = setexprT --> fT
      val FuT = funT --> fT
      val TAtomC = Term.Const (@{const_name "Var"}, TAtomT)
      val TCompC = Term.Const (@{const_name "Fun"}, TCompT)
      val AtomC = Term.Const ("Transactions.prot_atom.Atom", atomT --> prot_atomT)
      fun full_name'' n = full_name' n trac lthy
      fun mk_prot_fun_trm f tau = Term.Const ("Transactions.prot_fun." ^ f, tau)
      fun mk_Fu_trm f =
            mk_prot_fun_trm "Fu" FuT $ Term.Const (full_name'' funN ^ "." ^ f, funT)
      fun mk_Set_trm (s,ts) = (* TODO: use? *)
            mk_prot_fun_trm "Set" SetT $ setexpr_to_hol (s,ts) trac lthy
      fun c_to_h s = cType_to_hol s trac lthy
      fun c_list_to_h ts = mk_list tT (map c_to_h ts)

      fun mk_atom_trm n = Term.Const (full_name'' atomN ^ "." ^ n, atomT)
      val EnumType_trm = TAtomC $ (AtomC $ mk_atom_trm enum_typeN)
      val ValueType_trm = TAtomC $ Term.Const ("Transactions.prot_atom.Value", prot_atomT)
    in
      case t of
        Enumeration _ => EnumType_trm
      | InfiniteEnumeration _ => EnumType_trm
      | EnumType => EnumType_trm
      | ValueType => ValueType_trm
      | PrivFunSecType => TAtomC $ (AtomC $ mk_atom_trm secret_typeN)
      | AtomicType s => TAtomC $ (AtomC $ mk_atom_trm s)
      | ComposedType (f,ts) => TCompC $ mk_Fu_trm f $ c_list_to_h ts
      | Untyped => error "Error: Expected a type but got untyped"
    end

  fun cMsg_to_hol (t:Trac_Term.cMsg) lbl varT var_map free_enum_var free_message_var trac lthy =
    let
      open Trac_Term
      val tT = messageT' varT trac lthy
      val fT = message_funT trac lthy
      val enum_constsT = enum_constsT trac lthy
      val tsT = message_listT' varT trac lthy
      val VarT = varT --> tT
      val FunT = [fT, tsT] ---> tT
      val absT = absT trac lthy
      val setexprT = setexprT trac lthy
      val AbsT = absT --> fT
      val funT = funT trac lthy
      val FuT = funT --> fT
      val SetT = setexprT --> fT
      val enumT = enum_constsT --> funT
      val VarC = Term.Const (@{const_name "Var"}, VarT)
      val FunC = Term.Const (@{const_name "Fun"}, FunT)
      val NilC = Term.Const (@{const_name "Nil"}, tsT)
      val prot_label = mk_prot_label lbl
      fun full_name'' n = full_name' n trac lthy
      fun mk_enum_const' a = mk_enum_const a trac lthy
      fun mk_prot_fun_trm f tau = Term.Const ("Transactions.prot_fun." ^ f, tau)
      fun mk_enum_trm etrm =
        mk_prot_fun_trm "Fu" FuT $ (Term.Const (full_name'' funN ^ "." ^ enumN, enumT) $ etrm)
      fun mk_Fu_trm f =
        mk_prot_fun_trm "Fu" FuT $ Term.Const (full_name'' funN ^ "." ^ f, funT)
      fun c_to_h s = cMsg_to_hol s lbl varT var_map free_enum_var free_message_var trac lthy
      fun c_list_to_h ts = mk_list tT (map c_to_h ts)
    in
      case t of
        cVar x =>
          if free_enum_var x
          then FunC $ mk_enum_trm (Term.Free (fst x, enum_constsT)) $ NilC
          else if free_message_var x
          then (* Term.Free (fst x, tT) *) (* TODO: somehow Isabelle doesn't realize that tT is the
                                                    same as messageT when varT is the right type
                                                    - maybe it's the type synonym in messageT which
                                                    is to blame *)
               Term.Free (fst x, messageT trac lthy)
          else VarC $ var_map x
      | cConst f =>
          FunC $
          mk_Fu_trm f $
          NilC
      | cFun (f,ts) =>
          FunC $
          mk_Fu_trm f $
          c_list_to_h ts
      | cSet (s,ts) =>
          if is_general_set_family trac s
          then FunC $
               (mk_prot_fun_trm "Set" SetT $ setexpr_to_hol (s,[]) trac lthy) $
               mk_list tT (map c_to_h (cPrivFunSec::ts))
          else FunC $
               (mk_prot_fun_trm "Set" SetT $ setexpr_to_hol (s,ts) trac lthy) $
               NilC
      | cAttack =>
          FunC $
          (mk_prot_fun_trm "Attack" (strand_labelT --> fT) $ prot_label) $
          NilC
      | cAbs bs =>
          FunC $
          (mk_prot_fun_trm "Abs" AbsT $ abs_to_hol bs trac lthy) $
          NilC
      | cOccursFact bs =>
          FunC $
          mk_prot_fun_trm "OccursFact" fT $
          mk_list tT [
            FunC $ mk_prot_fun_trm "OccursSec" fT $ NilC,
            c_to_h bs]
      | cPrivFunSec =>
          FunC $
          mk_Fu_trm priv_fun_secN $
          NilC
      | cEnum a =>
          FunC $
          mk_enum_trm (mk_enum_const' a) $
          NilC
  end

  fun ground_cMsg_to_hol t lbl trac lthy =
    cMsg_to_hol t lbl (message_varT trac lthy) (fn _ => error "Error: Term not ground")
                (fn _ => false) (fn _ => false) trac lthy

  fun ana_cMsg_to_hol inc_vars t (ana_var_map:string list) =
    let
      open Trac_Term
      fun var_map (x,Untyped) = (
            case list_find (fn y => x = y) ana_var_map of
              SOME (_,n) => if inc_vars then mk_nat (1+n) else mk_nat n
            | NONE => error ("Error: Analysis variable " ^ x ^ " not found"))
        | var_map _ = error "Error: Analysis variables must be untyped"
      val lbl = 0 (* There's no constants in analysis messages requiring labels anyway *)
    in
      cMsg_to_hol t lbl natT var_map (fn _ => false) (fn _ => false)
    end

  fun transaction_cMsg_to_hol t lbl transaction_var_map free_vars trac lthy =
    let
      open Trac_Term
      val varT = message_varT trac lthy
      fun var_map (x,tau) =
            case list_find (fn y => (x,tau) = y) transaction_var_map of
              SOME (_,n) => HOLogic.mk_prod (cType_to_hol tau trac lthy, mk_nat n)
            | NONE => error ("Error: Transaction variable " ^ cMsg_str (cVar (x,tau)) ^ " not found")
      fun free_enum_var (_,Enumeration _) = true
        | free_enum_var _ = false
    in
      cMsg_to_hol t lbl varT var_map free_enum_var (fn _ => free_vars) trac lthy
    end

  fun fp_triple_to_hol (fp,occ,ti) trac lthy =
    let
      val prot_label = 0
      val tau_abs = absT trac lthy
      val tau_fp_elem = messageT trac lthy
      val tau_occ_elem = tau_abs
      val tau_ti_elem = mk_prodT (tau_abs, tau_abs)
      fun a_to_h bs = abs_to_hol bs trac lthy
      fun c_to_h t = ground_cMsg_to_hol t prot_label trac lthy
      val fp' = mk_list tau_fp_elem (map c_to_h fp)
      val occ' = mk_list tau_occ_elem (map a_to_h occ)
      val ti' = mk_list tau_ti_elem (map (mk_prod o map_prod a_to_h) ti)
    in
      mk_tuple [fp', occ', ti']
    end

  fun absfreeprod tau xs trm =
    let
      val tau_out = Term.fastype_of trm
      fun absfree' x = absfree (x,tau)
      fun aux _ [] = trm
        | aux _ [x] = absfree' x trm
        | aux len (x::y::xs) =
            Term.Const (@{const_name "case_prod"},
                   [[tau,mk_tupleT (replicate (len-1) tau)] ---> tau_out,
                    mk_tupleT (replicate len tau)] ---> tau_out) $
            absfree' x (aux (len-1) (y::xs))
    in
      aux (length xs) xs
    end

  fun abstract_over_finite_enum_vars enum_vars enum_ineqs trm trac lthy =
    let
      val enum_constsT = enum_constsT trac lthy
      val absfreeprod' = absfreeprod enum_constsT

      fun enumlistelemT n = mk_tupleT (replicate n enum_constsT)
      fun enumlistT n = mk_listT (enumlistelemT n)
      fun mk_enum_const' a = mk_enum_const a trac lthy

      fun mk_enumlist ns = mk_list enum_constsT (map mk_enum_const' ns)

      fun mk_enum_neq (a,b) = (HOLogic.mk_not o HOLogic.mk_eq)
        (Term.Free (a, enum_constsT), Term.Free (b, enum_constsT))

      fun mk_enum_neqs_list [] = Term.Const (@{const_name "True"}, HOLogic.boolT)
        | mk_enum_neqs_list [x] = mk_enum_neq x
        | mk_enum_neqs_list (x::y::xs) = HOLogic.mk_conj (mk_enum_neq x, mk_enum_neqs_list (y::xs))

      val enum_types =
        let
          open Trac_Term

          val flat_enum_spec = map (fn (a,b,_) => (a,b)) (get_finite_enum_spec trac)
          val err_pre = "Error: Expected a finite enumeration, but got "
          fun aux (Enumeration t) = (
                case List.find (fn (s,_) => t = s) flat_enum_spec of
                  SOME (_,cs) => (t,cs)
                | NONE => error ("Error: " ^ t ^ " has not been declared as an enumeration"))
            | aux Untyped = (enum_constsN,get_enum_consts trac)
            | aux (InfiniteEnumeration t) = error (err_pre ^ "an infinite enumeration: " ^ t)
            | aux tau = error (err_pre ^ "type " ^ cType_str tau)
        in
          map (aux o snd) enum_vars
        end

      fun enumlist_product f nil_case =
        let
          fun aux _ [] = nil_case ()
            | aux _ [ns] = f ns
            | aux len (ns::ms::elists) =
                Term.Const ("List.product", [enumlistT 1, enumlistT (len-1)] ---> enumlistT len) $
                f ns $ aux (len-1) (ms::elists)
        in
          aux (length enum_types) enum_types
        end

      val enable_let_bindings = false

      val absfp = absfreeprod' (map fst enum_vars) trm
      val eptrm = if length enum_vars > 1 andalso enable_let_bindings
                  then enumlist_product
                        (fn (x,_) => Term.Free (x, mk_listT enum_constsT))
                        (fn () => error "Error: Nil in enumlist_product")
                  else enumlist_product (mk_enumlist o snd) (fn () => mk_enumlist [])
      val typof = Term.fastype_of
      val evseT = enumlistelemT (length enum_vars)
      val evslT = enumlistT (length enum_vars)
      val eneqs = absfreeprod' (map fst enum_vars) (mk_enum_neqs_list enum_ineqs)
    in
      if null enum_vars
      then mk_list (typof trm) [trm]
      else let
        val a = Term.Const(@{const_name "map"},
                  [typof absfp, typof eptrm] ---> mk_listT (typof trm)) $
                absfp
        val b = if null enum_ineqs
                then eptrm
                else Term.Const (@{const_name "filter"},
                        [evseT --> HOLogic.boolT, evslT] ---> evslT) $
                     eneqs $ eptrm
        val c = absfreeprod (mk_listT enum_constsT) (distinct (op =) (map fst enum_types)) (a$b)
        val d = mk_tuple (map mk_enumlist (distinct (op =) (map snd enum_types)))
        val e = Term.Const (@{const_name "Let"}, [typof d, typof c] ---> typof (c$d))$d$c
      in if length enum_vars > 1 andalso enable_let_bindings then e else a $ b
      end
    end

  fun mk_type_of_name lthy pname name ty_args
      = Type(Local_Theory.full_name lthy (Binding.name (mkN(pname, name))), ty_args)

  fun mk_mt_list t = Term.Const (@{const_name "Nil"}, mk_listT t)

  fun name_of_typ (Type (s, _)) = s
    | name_of_typ (TFree _)     = error "name_of_type: unexpected TFree"
    | name_of_typ (TVar _ )     = error "name_of_type: unexpected TVAR"

  fun prove_UNIV name typ elems thmsN lthy =
    let 
      val rhs = mk_set typ elems
      val lhs = Const("Set.UNIV",mk_setT typ)
      val stmt = mk_Trueprop (mk_eq (lhs,rhs))
      val fq_tname = name_of_typ typ 
                          
      fun inst_and_prove_enum thy = 
        let
          val _ = writeln("Inst enum: "^name)
          val lthy = Class.instantiation ([fq_tname], [], @{sort enum}) thy
          val enum_eq = Const("Pure.eq",mk_listT typ --> mk_listT typ --> propT)
                             $Const(@{const_name "enum_class.enum"},mk_listT typ)
                             $(mk_list typ elems)

          val ((_, (_, enum_def')), lthy) = Specification.definition NONE [] [] 
                                                ((Binding.name ("enum_"^name),[]), enum_eq) lthy
          val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy)
          val enum_def = singleton (Proof_Context.export lthy ctxt_thy) enum_def'

          val enum_all_eq = Const("Pure.eq", boolT --> boolT --> propT)
                             $(Const(@{const_name "enum_class.enum_all"},(typ --> boolT) --> boolT)
                                                  $Free("P",typ --> boolT))
                             $(Const(@{const_name "list_all"},(typ --> boolT) --> (mk_listT typ) --> boolT)
                                    $Free("P",typ --> boolT)$(mk_list typ elems))
          val ((_, (_, enum_all_def')), lthy) = Specification.definition NONE [] [] 
                                                ((Binding.name ("enum_all_"^name),[]), enum_all_eq) lthy
          val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy)
          val enum_all_def = singleton (Proof_Context.export lthy ctxt_thy) enum_all_def'

          val enum_ex_eq = Const("Pure.eq", boolT --> boolT --> propT)
                             $(Const(@{const_name "enum_class.enum_ex"},(typ --> boolT) --> boolT)
                                                  $Free("P",typ --> boolT))
                             $(Const(@{const_name "list_ex"},(typ --> boolT) --> (mk_listT typ) --> boolT)
                                    $Free("P",typ --> boolT)$(mk_list typ elems))
          val ((_, (_, enum_ex_def')), lthy) = Specification.definition NONE [] [] 
                                                ((Binding.name ("enum_ex_"^name),[]), enum_ex_eq) lthy
          val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy)
          val enum_ex_def = singleton (Proof_Context.export lthy ctxt_thy) enum_ex_def'
        in
          Class.prove_instantiation_exit (fn ctxt => 
            (Class.intro_classes_tac ctxt [])  THEN
               ALLGOALS (simp_tac (ctxt addsimps  [Proof_Context.get_thm ctxt (name^"_UNIV"),  
                                                           enum_def, enum_all_def, enum_ex_def]) ) 
            )lthy
        end
      fun inst_and_prove_finite thy = 
        let
          val lthy = Class.instantiation ([fq_tname], [], @{sort finite}) thy
        in 
          Class.prove_instantiation_exit (fn ctxt => 
            (Class.intro_classes_tac ctxt []) THEN 
             (simp_tac (ctxt addsimps[Proof_Context.get_thm ctxt (name^"_UNIV")])) 1) lthy
        end
    in 
      lthy
      |> ml_isar_wrapper.prove_simple (name^"_UNIV") stmt 
         (fn c =>     (safe_tac c) 
                 THEN (ALLGOALS(simp_tac c))
                 THEN (ALLGOALS(Metis_Tactic.metis_tac ["full_types"] 
                                   "combs"  c 
                                   (map (Proof_Context.get_thm c) thmsN)))
         )
      |> Local_Theory.raw_theory inst_and_prove_finite 
      |> Local_Theory.raw_theory inst_and_prove_enum  
    end

  fun def_enum_consts (trac:TracProtocolCert.cProtocol) lthy = 
    let 
      val pname = #name trac
      val defname = mkN(pname, enum_constsN)
      val _ = info("  Defining "^defname)
      val enames = get_enum_consts trac
      val econsts = map (fn x => ([],x)) enames
    in 
      ([defname], ml_isar_wrapper.define_simple_datatype ([], defname) econsts lthy)
    end

  fun def_sets (trac:TracProtocolCert.cProtocol) lthy = 
    let 
      val pname = #name trac
      val defname = mkN(pname, setsN)
      val _ = info ("  Defining "^defname)

      val sspec = get_set_spec trac
      val gsspec = get_general_set_family_set_spec trac
      val tfqn = full_name' enum_constsN trac lthy
      val ttyp = Type(tfqn, [])
      val eqs =
        map (fn (x,n) => if member (op =) gsspec (x,n) then ([],x) else (replicate n ttyp,x)) sspec
    in
      lthy
      |> ml_isar_wrapper.define_simple_datatype ([], defname) eqs
    end

  fun def_funs (trac:TracProtocolCert.cProtocol) lthy = 
    let 
      val pname = #name trac
      val (pub_f, pub_c, priv_c) = get_funs trac
      val pub = (map (fn (f,n) => (f,n,NONE)) pub_f)@(map (fn (f,a) => (f,0,a)) pub_c)
      val priv = map (fn (f,a) => (f,0,a)) priv_c
      val declared_types = #type_spec trac

      fun def_atom lthy = 
        let 
          val def_atomname = mkN(pname, atomN) 
          val extra_types =
            if null pub_c
            then default_extra_types
            else extended_extra_types
          val types = declared_types@extra_types
          fun define_atom_dt lthy = 
            let
              val _ = info("  Defining "^def_atomname)
            in
              lthy
              |> ml_isar_wrapper.define_simple_datatype ([], def_atomname) (map (fn x => ([],x)) types)
            end
          fun prove_UNIV_atom lthy =
            let
              val _ = info ("    Proving "^def_atomname^"_UNIV")
              val thmsN = [def_atomname^".exhaust"]
              val fqn = full_name (mkN(pname, atomN)) lthy
              val typ = Type(fqn, [])  
            in
              lthy 
              |> prove_UNIV (def_atomname) typ (map (fn c => Const(fqn^"."^c,typ)) types) thmsN 
            end 
        in 
           lthy
           |> define_atom_dt
           |> prove_UNIV_atom
        end

      fun def_fun_dt lthy = 
        let
          val def_funname = mkN(pname, funN)
          val _ = info("  Defining "^def_funname)
          val decl_funs = map (fn x => ([],x)) (map #1 (pub@priv))
          val enum_fun = ([Type (full_name (mkN(pname, enum_constsN)) lthy, [])],enumN)

          val all_funs = decl_funs@enum_fun::map snd (get_user_atom_spec_pre trac)@
                         map (fn (e,_,_) => ([natT],infenumN e))
                             (get_nonunion_infinite_enum_spec trac)
        in
          ml_isar_wrapper.define_simple_datatype ([], def_funname) all_funs lthy
        end

      fun def_fun_arity lthy = 
        let 
          val fqn_name = full_name (mkN(pname, funN)) lthy
          val ctyp = Type (fqn_name, [])
          val ctyp' = Type (full_name (mkN(pname, enum_constsN)) lthy, [])
          val name = mkN(pname, arityN)

          fun mk_rec_eq typs (fname,arity,_) =
            let
              val a = Const(fqn_name^"."^fname, typs ---> ctyp)
              val b = fold (fn t => fn p => p$(Term.dummy_pattern t)) typs a
            in
              (Free(name,ctyp --> natT)$b, mk_nat(arity))
            end

          val _ = info("  Defining "^name)
        in
          ml_isar_wrapper.define_simple_fun name
              (map (mk_rec_eq []) (pub@priv)@
               mk_rec_eq [ctyp'] (enumN,0,NONE)::
               map (fn (_,(ts,f)) => mk_rec_eq ts (f,0,NONE)) (get_user_atom_spec_pre trac)@
               map (fn (e,_,_) => mk_rec_eq [natT] (infenumN e,0,NONE))
                   (get_nonunion_infinite_enum_spec trac))
              lthy
        end

      fun def_set_arity lthy = 
        let
          val fqn_name = full_name' setsN trac lthy
          val ctyp = Type (fqn_name, [])
          val ctyp' = Type (full_name' enum_constsN trac lthy, [])
          val name = mkN(pname, set_arityN)

          val sspec = get_set_spec trac
          val gsspec = get_general_set_family_set_spec trac

          val sspec' =
            map (fn (x,n) => if member (op =) gsspec (x,n)
                             then (x,n+1,[])
                             else (x,0,replicate n ctyp'))
                sspec

          fun mk_rec_eq (fname,arity,typs) =
            let
              val a = Const(fqn_name^"."^fname, typs ---> ctyp)
              val b = fold (fn t => fn p => p$(Term.dummy_pattern t)) typs a
            in
              (Free(name,ctyp --> natT)$b, mk_nat(arity))
            end

          val _ = info("  Defining "^name)
        in
          ml_isar_wrapper.define_simple_fun name
              (map mk_rec_eq sspec')
              lthy
        end

      fun def_public lthy = 
        let 
          val fqn_name = full_name (mkN(pname, funN)) lthy
          val ctyp = Type (fqn_name, [])
          val ctyp' = Type (full_name (mkN(pname, enum_constsN)) lthy, [])
          val name = mkN(pname, publicN)

          fun mk_rec_eq bool_trm typs fname =
            let
              val a = Const(fqn_name^"."^fname, typs ---> ctyp)
              val b = fold (fn t => fn p => p$(Term.dummy_pattern t)) typs a
            in
              (Free(name,ctyp --> boolT)$b, bool_trm)
            end

          fun mk_rec_eq' fname =
            let
              val a = Const(fqn_name^"."^fname, [boolT,natT] ---> ctyp)
              val b = a$Term.Free ("b", boolT)$Term.dummy_pattern natT
            in
              (Free(name,ctyp --> boolT)$b, Term.Free ("b", boolT))
            end

          val _ = info("  Defining "^name) 
        in
          ml_isar_wrapper.define_simple_fun name
              ((map (mk_rec_eq (@{term "False"}) []) (map #1 priv))
              @(map (mk_rec_eq (@{term "True"}) []) (map #1 pub))
              @mk_rec_eq (@{term "True"}) [ctyp'] enumN
              ::map (mk_rec_eq' o snd o snd) (get_user_atom_spec_pre trac)
              @map (fn (e,_,_) => mk_rec_eq (@{term "True"}) [natT] (infenumN e))
                   (get_nonunion_infinite_enum_spec trac)
              ) lthy
        end

      fun def_gamma lthy = 
        let 
          fun optionT t = Type (@{type_name "option"}, [t])
          fun mk_Some t = Const (@{const_name "Some"}, t --> optionT t)
          fun mk_None t = Const (@{const_name "None"},  optionT t)

          val fqn_name = full_name (mkN(pname, funN)) lthy
          val ctyp = Type (fqn_name, [])
          val atomFQN = full_name (mkN(pname, atomN)) lthy
          val atomT = Type (atomFQN, [])
          val ctyp' = Type (full_name (mkN(pname, enum_constsN)) lthy, [])
          val name = mkN(pname, gammaN)

          fun mk_atomT_trm tau = mk_Some atomT$Const(atomFQN^"."^tau, atomT)

          fun mk_rec_eq' (typname,(typs,fname)) =
            let
              val typtrm = case typname of NONE => mk_None atomT | SOME tau => mk_atomT_trm tau
              val a = Const(fqn_name^"."^fname, typs ---> ctyp)
              val b = fold (fn t => fn p => p$(Term.dummy_pattern t)) typs a
            in
              (Free(name,ctyp --> optionT atomT)$b, typtrm)
            end

          fun mk_rec_eq typname fname = mk_rec_eq' (typname,([],fname))

          val user_atom_spec = get_user_atom_spec trac
          val priv_rest = filter_out (member (op =) (map (snd o snd) user_atom_spec) o #1) priv
          val pub_c_rest = filter_out (member (op =) (map (snd o snd) user_atom_spec) o #1) pub_c

          val _ = info("  Defining "^name)
        in
          ml_isar_wrapper.define_simple_fun name
              (map (fn (s,p) => mk_rec_eq' (SOME s,p)) user_atom_spec
              @map (mk_rec_eq (SOME secret_typeN) o #1) priv_rest
              @map (mk_rec_eq (SOME other_pubconsts_typeN) o #1) pub_c_rest
              @mk_rec_eq' (SOME enum_typeN,([ctyp'],enumN))
              ::map (mk_rec_eq NONE o #1) pub_f
              @map (fn (e,_,_) => mk_rec_eq' (SOME enum_typeN,([natT],infenumN e)))
                   (get_nonunion_infinite_enum_spec trac)
              ) lthy
        end

      fun def_ana lthy = let
        val pname = #name trac
        val (pub_f, pub_c, priv_c) = get_funs trac
        val pub = (map (fn (f,n) => (f,n,NONE)) pub_f)@(map (fn (f,a) => (f,0,a)) pub_c)
        val priv = map (fn (f,a) => (f,0,a)) priv_c
  
        val keyT = messageT' natT trac lthy
  
        val fqn_name = full_name (mkN(pname, funN)) lthy
        val ctyp = Type (fqn_name, [])
        val ctyp' = Type (full_name (mkN(pname, enum_constsN)) lthy, [])
        val name = mkN(pname, anaN)

        val ana_outputT = mk_prodT (mk_listT keyT, mk_listT natT)
  
        val default_output = mk_prod (mk_list keyT [], mk_list natT [])
  
        fun mk_ana_output ks rs = mk_prod (mk_list keyT ks, mk_list natT rs)

        fun mk_rec_eq ana_output_trm typs fname =
          let
            val a = Const(fqn_name^"."^fname, typs ---> ctyp)
            val b = fold (fn t => fn p => p$(Term.dummy_pattern t)) typs a
          in
            (Free(name,ctyp --> ana_outputT)$b, ana_output_trm)
          end

        val _ = info("  Defining "^name) 

        val ana_spec =
          let
            fun var_to_nat is_priv_fun f xs x =
              let
                val n = snd (Option.valOf ((list_find (fn y => y = x) xs)))
              in
                if is_priv_fun then mk_nat (1+n) else mk_nat n
              end
            fun c_to_h is_priv_fun f xs t = ana_cMsg_to_hol is_priv_fun t xs trac lthy
            fun keys is_priv_fun f ps ks = map (c_to_h is_priv_fun f ps) ks
            fun results is_priv_fun f ps rs = map (var_to_nat is_priv_fun f ps) rs
            fun aux ({head=(f,ps), keys=ks, results=rs, is_priv_fun=b}:TracProtocolCert.cAnaRule) =
              (f, mk_ana_output (keys b f ps ks) (results b f ps rs))
          in
            map aux (#analysis_spec trac)
          end

        val other_funs =
          filter (fn f => not (List.exists (fn g => f = g) (map fst ana_spec))) (map #1 (pub@priv))
      in
        ml_isar_wrapper.define_simple_fun name
            (map (fn (f,out) => mk_rec_eq out [] f) ana_spec
            @map (mk_rec_eq default_output []) other_funs
            @mk_rec_eq default_output [ctyp'] enumN
            ::map (fn (_,(typs,f)) => mk_rec_eq default_output typs f) (get_user_atom_spec_pre trac)
            @map (fn (e,_,_) => mk_rec_eq default_output [natT] (infenumN e))
                 (get_nonunion_infinite_enum_spec trac)
          )
          lthy
      end

    in
      lthy |> def_atom
           |> def_fun_dt
           |> def_fun_arity
           |> def_set_arity
           |> def_public
           |> def_gamma
           |> def_ana
    end

  fun define_term_model (trac:TracProtocolCert.cProtocol) lthy =
    let 
      val _ = info("Defining term model")
    in
      lthy |> snd o def_enum_consts trac 
           |> def_sets trac
           |> def_funs trac
    end
  
  fun define_fixpoint fp_triple trac print lthy =
    let
      val fp_name = mkN (#name trac, "fixpoint")
      val _ = info("Defining fixpoint")
      val _ = info("  Defining "^fp_name)
      val fp_triple_trm = fp_triple_to_hol fp_triple trac lthy
    in
      (trac, #2 (ml_isar_wrapper.define_constant_definition' (fp_name, fp_triple_trm) print lthy))
    end

  fun define_protocol print ((trac:TracProtocolCert.cProtocol), lthy) = let
      val _ =
        if length (#transaction_spec trac) > 1
        then info("Defining protocols")
        else info("Defining protocol")
      val pname = #name trac

      val mk_Send = mk_Send_step trac lthy
      val mk_Receive = mk_Receive_step trac lthy
      val mk_InSet = mk_InSet_step trac lthy
      val mk_NotInSet = mk_NotInSet_step trac lthy
      val mk_NegChecks = mk_NegChecks_step trac lthy
      val mk_Equality = mk_Equality_step trac lthy
      val mk_Insert = mk_Insert_step trac lthy
      val mk_Delete = mk_Delete_step trac lthy

      val star_label = mk_star_label
      val prot_label = mk_prot_label

      fun mk_tname i tr =
        let
          val x = #1 tr
          val y = case i of NONE => x | SOME n => mkN(n, x)
          val z = mkN("transaction", y)
        in mkN(pname, z)
        end

      fun def_transaction name_prefix prot_num (transaction:TracProtocolCert.cTransaction) lthy = let
        val defname = mk_tname name_prefix (#transaction transaction)
        val _ = info("  Defining "^defname)

        val receives       = #receive_actions     transaction
        val checkssingle   = #checksingle_actions transaction
        val checksall      = #checkall_actions    transaction
        val updates        = #update_actions      transaction
        val sends          = #send_actions        transaction
        val fresh          = get_fresh_variables  transaction
        val attack_signals = #attack_actions      transaction

        val fresh_vars          = get_fresh_variables            transaction
        val nonfresh_value_vars = get_nonfresh_value_variables   transaction
        val finenum_vars        = get_finite_enum_variables      transaction
        val enumtype_vars       = get_enumtype_variables         transaction
        val nonenum_vars        = get_nonenum_variables          transaction
        val infenum_vars        = get_infinite_enum_variables    transaction
        val all_decl_vars       = get_transaction_head_variables transaction
        val bvars               = get_bound_variables            transaction

        val nonfinenum_vars =
          filter (member (op =) (nonenum_vars@infenum_vars)) (all_decl_vars@fresh_vars)

        val infenum_enumtype_vars =
          filter (member (op =) (enumtype_vars@infenum_vars)) (all_decl_vars@fresh_vars)

        val (enum_ineqs, value_ineqs) = get_variable_restrictions transaction

        val enable_let_bindings = true

        fun c_to_h' b trm = transaction_cMsg_to_hol
          trm prot_num
          (nonfinenum_vars@bvars)
          b trac lthy

        val c_to_h = c_to_h' enable_let_bindings

        val abstract_over_finenum_vars = fn x => fn y => fn z =>
          abstract_over_finite_enum_vars x y z trac lthy

        fun mk_transaction_term (rcvs, chcksingle, chckall, upds, snds, frsh, atcks) =
          let
            open Trac_Term TracProtocolCert
            fun action_filter f (lbl,a) = case f a of SOME x => SOME (lbl,x) | NONE => NONE

            fun lbl_to_h LabelS = star_label
              | lbl_to_h LabelN = prot_label prot_num

            fun lbl_trms_to_h f (lbl,ts) = f (lbl_to_h lbl) (map c_to_h ts)

            val S0 =
              let
                val msgT = messageT trac lthy
                val varT = message_varT trac lthy
                val funN = full_name' funN trac lthy
                val funT = funT trac lthy
                val enum_constsT = enum_constsT trac lthy
                val infenumspec = get_infinite_enum_spec trac
                val botinfenums = map #1 (get_nonunion_infinite_enum_spec trac)
                val enum_constructor = Term.Const (funN ^ "." ^ enumN, enum_constsT --> funT)
                fun mk_enum_const' a = mk_enum_const a trac lthy
                fun mk_union typ [] = Term.Const ("Set.empty", mk_setT typ)
                  | mk_union typ (t::ts) =
                      fold (fn s => fn u =>
                        Term.Const ("Set.union", [mk_setT typ, mk_setT typ] ---> mk_setT typ) $
                        u $ s) ts t
                val ran_trm_finenums =
                  Term.Const ("Set.range", (enum_constsT --> funT) --> mk_setT funT) $
                  enum_constructor
                fun ran_trm_botinfenum e =
                  Term.Const ("Set.range", (natT --> funT) --> mk_setT funT) $
                  Term.Const (funN ^ "." ^ infenumN e, natT --> funT)
                fun ran_trm_infenums e =
                  case List.find (fn (a,_,_) => a = e) infenumspec of
                    SOME (_,cs,es) => mk_union funT (map ran_trm_botinfenum es@
                      (if null cs then []
                       else [mk_set funT (map (fn c => enum_constructor $ mk_enum_const' c) cs)]))
                  | NONE => error ("Couldn't find enumeration " ^ e)
                fun consts (_,EnumType) =
                      mk_union funT (ran_trm_finenums::map ran_trm_botinfenum botinfenums)
                  | consts (_,InfiniteEnumeration e) = ran_trm_infenums e
                  | consts x = error ("Error: Expected an enumeration variable or a variable of " ^
                                      "type " ^ enum_typeN ^ ", but got " ^ cMsg_str (cVar x))
                fun var_trm x =
                  Term.Const (@{const_name "the_Var"}, msgT --> varT) $ c_to_h (cVar x)
              in
                map (fn x => mk_prod (var_trm x, consts x)) infenum_enumtype_vars
              end

            val S1 = map (lbl_trms_to_h mk_Receive)
                         (map_filter (action_filter maybe_the_Receive) rcvs)

            val S2 =
              let
                fun aux (lbl,cEquality (pcv,(x,y))) =
                      SOME (mk_Equality pcv (lbl_to_h lbl) (c_to_h x) (c_to_h y))
                  | aux (lbl,cInSet (pcv,(e,s))) =
                      SOME (mk_InSet pcv (lbl_to_h lbl) (c_to_h e) (c_to_h s))
                  | aux (lbl,cNegChecks (xs,ns)) =
                      let
                        fun f (a,b) = (c_to_h a, c_to_h b)
                        val ineqs = map f (map_filter maybe_the_Inequality ns)
                        val notins = map f (map_filter maybe_the_NotInSet ns)
                        val bvars = map (c_to_h o cVar) xs
                      in
                        SOME (mk_NegChecks (lbl_to_h lbl) bvars ineqs notins)
                      end
                  | aux _ = NONE
              in
                map_filter aux chcksingle
              end

            val S3 =
              let
                fun arity s = case set_arity trac s of
                    SOME n => n
                  | NONE => error ("Error: Not a set family: " ^ s)

                fun mk_evs s =
                  map (fn n => ("X" ^ Int.toString n, Untyped)) (0 upto ((arity s) -1))

                fun mk_trm (lbl,e,s) =
                  let
                    val ps = map (fn x => cVar (x,EnumType)) (map fst (mk_evs s))
                  in
                    mk_NotInSet (lbl_to_h lbl) (c_to_h e) (c_to_h (cSet (s,ps)))
                  end

                fun mk_trms (lbl,(e,s)) =
                  abstract_over_finenum_vars (mk_evs s) [] (mk_trm (lbl,e,s))
              in
                map mk_trms (map_filter (action_filter maybe_the_NotInAny) chckall)
              end

            val S4 = map (c_to_h o cVar) frsh

            val S5 =
              let
                fun aux (lbl,cInsert (e,s)) = SOME (mk_Insert (lbl_to_h lbl) (c_to_h e) (c_to_h s))
                  | aux (lbl,cDelete (e,s)) = SOME (mk_Delete (lbl_to_h lbl) (c_to_h e) (c_to_h s))
                  | aux _ = NONE
              in
                map_filter aux upds
              end

            val S6 =
              let val snds' = map_filter (action_filter maybe_the_Send) snds
              in map (lbl_trms_to_h mk_Send) (snds'@map (fn (lbl,_) => (lbl,[cAttack])) atcks) end
          in
            mk_Transaction trac lthy S0 S1 S2 S3 S4 S5 S6
              |> abstract_over_finenum_vars finenum_vars enum_ineqs
              |> (fn trm =>
                    if not (null nonfinenum_vars) andalso enable_let_bindings
                    then let
                      val typof = Term.fastype_of
                      val xs = nonfinenum_vars@bvars
                      val a = absfreeprod (messageT trac lthy) (map fst xs) trm
                      val b = mk_tuple (map (c_to_h' false o cVar) xs)
                      val c = Term.Const (@{const_name "Let"}, [typof b, typof a] ---> typof (a$b))
                    in c$b$a end
                    else trm)
          end

        fun def_trm trm print lthy =
          #2 (ml_isar_wrapper.define_constant_definition' (defname, trm) print lthy)

        val additional_value_ineqs =
          let
            open Trac_Term TracProtocolCert
            val poschecks = map_filter (maybe_the_InSet o snd) checkssingle
            val negchecks_single = List.concat (map (map_filter maybe_the_NotInSet o snd)
                                                    (map_filter (maybe_the_NegChecks o snd)
                                                                checkssingle))
            val negchecks_all = map_filter (maybe_the_NotInAny o snd) checksall

            fun aux' (cVar (x,ValueType),s) (cVar (y,ValueType),t) =
                  if s = t then SOME (x,y) else NONE
              | aux' _ _ = NONE

            fun aux (x,cSet (s,ps)) = SOME (
                  map_filter (aux' (x,cSet (s,ps))) negchecks_single@
                  map_filter (aux' (x,s)) negchecks_all
                )
              | aux _ = NONE
          in
            List.concat (map_filter aux poschecks)
          end

        val all_value_ineqs = distinct (op =) (value_ineqs@additional_value_ineqs)

        val valvarsprod =
              filter (fn p => not (List.exists (fn q => p = q orelse swap p = q) all_value_ineqs))
                     (list_triangle_product (fn x => fn y => (x,y)) nonfresh_value_vars)

        val transaction_trm0 = mk_transaction_term
                      (receives, checkssingle, checksall, updates, sends, fresh, attack_signals)
      in
        if null valvarsprod
        then def_trm transaction_trm0 print lthy
        else let
          open Trac_Term TracProtocolCert
          val partitions = list_partitions nonfresh_value_vars all_value_ineqs
          val ps = filter (not o null) (map (filter (fn x => length x > 1)) partitions)

          fun mk_subst ps =
            let 
              fun aux [] = NONE
                | aux (x::xs) = SOME (map (fn y => (y,cVar (x,ValueType))) xs)
            in
              List.concat (map_filter aux ps)
            end

          fun apply d =
            let
              val ap = subst_apply_cActions d
              val checksingle' =
                filter (fn (_,a) => case a of
                                      cNegChecks ([],[cInequality (x,y)]) => x <> y
                                    | _ => true)
                       (ap checkssingle)
            in
              (ap receives, checksingle', ap checksall, ap updates, ap sends, fresh, attack_signals)
            end

          val transaction_trms = transaction_trm0::map (mk_transaction_term o apply o mk_subst) ps
          val transaction_typ = Term.fastype_of transaction_trm0

          fun mk_concat_trm tau trms =
            Term.Const (@{const_name "concat"}, mk_listT tau --> tau) $ mk_list tau trms
        in
          def_trm (mk_concat_trm transaction_typ transaction_trms) print lthy
        end
      end

      val def_transactions =
        let
          val prots = map (fn (n,pr) => map (fn tr => (n,tr)) pr) (#transaction_spec trac)
          val lbls = list_upto (length prots)
          val lbl_prots = List.concat (map (fn i => map (fn tr => (i,tr)) (nth prots i)) lbls)
          val f = fold (fn (i,(n,tr)) => def_transaction n i tr)
        in 
          f lbl_prots
        end

      fun def_protocols lthy = let
          fun mk_prot_def (name,trm) lthy =
            let val _ = info("  Defining "^name)
            in #2 (ml_isar_wrapper.define_constant_definition' (name,trm) print lthy)
            end

          val prots = #transaction_spec trac
          val num_prots = length prots

          val pdefname = mkN(pname, "protocol")

          fun mk_tnames i =
            let
              val trs = case nth prots i of (j,prot) => map (fn tr => (j,tr)) prot
            in map (fn (j,s) => full_name (mk_tname j (#transaction s)) lthy) trs
            end

          val tnames = List.concat (map mk_tnames (list_upto num_prots))

          val pnames =
            let
              val f = fn i => (Int.toString i,nth prots i)
              val g = fn (i,(n,_)) => case n of NONE => i | SOME m => m
              val h = fn s => mkN (pdefname,s)
            in map (h o g o f) (list_upto num_prots)
            end

          val trtyp = prot_transactionT trac lthy
          val trstyp = mk_listT trtyp
    
          fun mk_prot_trm names =
            Term.Const (@{const_name "concat"}, mk_listT trstyp --> trstyp) $
            mk_list trstyp (map (fn x => Term.Const (x, trstyp)) names)
    
          val lthy =
            if num_prots > 1
            then fold (fn (i,pname) => mk_prot_def (pname, mk_prot_trm (mk_tnames i)))
                      (map (fn i => (i, nth pnames i)) (list_upto num_prots))
                      lthy
            else lthy

          val pnames' = map (fn n => full_name n lthy) pnames

          fun mk_prot_trm_with_star i =
            let
              fun f j =
                if j = i
                then Term.Const (nth pnames' j, trstyp)
                else (Term.Const (@{const_name "map"}, [trtyp --> trtyp, trstyp] ---> trstyp) $
                      Term.Const ("Transactions.transaction_star_proj", trtyp --> trtyp) $
                      Term.Const (nth pnames' j, trstyp))
            in
              Term.Const (@{const_name "concat"}, mk_listT trstyp --> trstyp) $
              mk_list trstyp (map f (list_upto num_prots))
            end

          fun mk_star_prot_trm () =
            let
              fun f j =
                (Term.Const (@{const_name "map"}, [trtyp --> trtyp, trstyp] ---> trstyp) $
                 Term.Const ("Transactions.transaction_star_proj", trtyp --> trtyp) $
                 Term.Const (nth pnames' j, trstyp))
            in
              Term.Const (@{const_name "concat"}, mk_listT trstyp --> trstyp) $
              mk_list trstyp (map f (list_upto num_prots))
            end

          val lthy =
            if num_prots > 1
            then fold (fn (i,pname) => mk_prot_def (pname, mk_prot_trm_with_star i))
                      (map (fn i => (i, nth pnames i ^ "_with_star_projs")) (list_upto num_prots))
                      lthy
            else lthy

          val lthy =
            if num_prots > 1
            then mk_prot_def (pdefname ^ "_star_projs", mk_star_prot_trm ()) lthy
            else lthy
      in
        mk_prot_def (pdefname, mk_prot_trm (if num_prots > 1 then pnames' else tnames)) lthy
      end
    in
      (trac, lthy |> def_transactions |> def_protocols)
    end
end
\<close>

ML\<open>

structure trac = struct
  open Trac_Term
  
  val info = Output.information

  fun mk_abs_filename thy filename =  
      let
        val filename = Path.explode filename
        val master_dir = Resources.master_directory thy
      in
        Path.implode (if (Path.is_absolute filename)
                      then filename
                      else Path.append master_dir filename)   
      end

  fun def_fp print (trac:TracProtocolCert.cProtocol, lthy) =
    case #fixed_point trac of
      SOME fp => trac_definitorial_package.define_fixpoint fp trac print lthy
    | NONE => (trac, lthy)
    (* let
      val fp = TracFpParser.parse_str fp_str
      val (trac,lthy) = trac_definitorial_package.define_fixpoint fp trac print lthy
      val lthy = Local_Theory.raw_theory (update trac) lthy
    in
      (trac, lthy)
    end *)

  fun def_trac_term_model trac lthy =
    let
      val lthy:local_theory = trac_definitorial_package.define_term_model trac lthy
    in
      (trac, lthy)
    end

  val def_trac_protocol = trac_definitorial_package.define_protocol

  fun def_trac trac_str opt_fp_str print lthy =
    let
      val trac = TracProtocolParser.parse_str trac_str
      val trac = case opt_fp_str of
                    SOME fp_str =>
                      TracProtocol.update_fixed_point trac (SOME (TracFpParser.parse_str fp_str))
                  | NONE => trac
      val lthy = Local_Theory.raw_theory (trac_definitorial_package.update trac) lthy
      val ctrac = TracProtocolCert.certifyProtocol trac
    in
      (def_fp print o def_trac_protocol print o def_trac_term_model ctrac) lthy
    end

  fun def_trac_file trac_filename opt_fp_filename print lthy = let
        fun read_file filename =
          File.read (Path.explode (mk_abs_filename (Proof_Context.theory_of lthy) filename))
        val trac_str = read_file trac_filename
        val opt_fp_str = Option.map (fn fp_filename => read_file fp_filename) opt_fp_filename
        val (trac,lthy) = def_trac trac_str opt_fp_str print lthy
      in
        (trac, lthy)
      end
end
\<close>


ML\<open>
  val fileNameP = Parse.name -- Parse.name

  val _ = Outer_Syntax.local_theory' @{command_keyword "trac"}
          "Define protocol and (optionally) fixpoint using trac format."
          ((Parse.cartouche -- Scan.optional Parse.cartouche "" >> (
            fn (trac,fp) => fn print => fn lthy =>
          let
            val opt_fp = if fp = "" then NONE else SOME fp
            val trac = trac.def_trac trac opt_fp print #> snd
          in
            trac_time.ap_lthy lthy ("trac") trac lthy 
          end)));

  val _ = Outer_Syntax.local_theory' @{command_keyword "trac_import"} 
          "Import protocol and (optionally) fixpoint from trac files." 
          ((Parse.name -- Scan.optional Parse.name "" >> (
            fn (trac_filename, fp_filename) => fn print => fn lthy =>
          let
            val opt_fp_filename = if fp_filename = "" then NONE else SOME fp_filename
            val trac = trac.def_trac_file trac_filename opt_fp_filename print #> snd
          in
            trac_time.ap_lthy lthy ("trac_import") trac lthy 
          end)));
\<close>

ML\<open>
val name_prefix_parser = Parse.!!! (Parse.name --| Parse.$$$ ":" -- Parse.name)

(* Original definition (opt_evaluator) copied from value_command.ml *)
val opt_proof_method_choice =
  Scan.optional (\<^keyword>\<open>[\<close> |-- Parse.name --| \<^keyword>\<open>]\<close>) "safe";

(* Original definition (locale_expression) copied from parse_spec.ML *)
val security_proof_locale_opt_defs_list = Scan.optional
  (\<^keyword>\<open>for\<close> |-- Scan.repeat1 Parse.name >>
      (fn xs => if length xs > 3 then error "Too many optional arguments" else xs))
  [];

val composed_protocol_locale_defs_list =
  (\<^keyword>\<open>for\<close> |-- Parse.!!! (
                      Parse.name --   (* The composed protocol *)
                      Parse.name --   (* Its SMP set *)
                      Parse.name)) -- (* The (symbolic) list of shared secrets *)
  (\<^keyword>\<open>and\<close> |-- Scan.repeat1 Parse.name >> (* The component protocols *)
      (fn xs => if length xs < 2 then error "Too few arguments" else xs)) --
  (\<^keyword>\<open>and\<close> |-- Scan.repeat1 Parse.name >> (* The component protocols with star projections *)
      (fn xs => if length xs < 2 then error "Too few arguments" else xs)) --
  (\<^keyword>\<open>and\<close> |-- Scan.repeat1 Parse.name >> (* Their GSMPs *)
      (fn xs => if length xs < 2 then error "Too few arguments" else xs));

val security_proof_locale_parser =
  name_prefix_parser -- security_proof_locale_opt_defs_list

val security_proof_locale_parser_with_method_choice =
  opt_proof_method_choice -- name_prefix_parser -- security_proof_locale_opt_defs_list

val composed_protocol_locale_parser =
  name_prefix_parser -- composed_protocol_locale_defs_list

val composed_protocol_locale_parser_with_method_choice =
  opt_proof_method_choice -- name_prefix_parser -- composed_protocol_locale_defs_list

fun protocol_model_setup_proof_state name prefix lthy =
  let
    fun f x y z = ([((x,Position.none),((y,true),(Expression.Positional z,[])))],[])
    val _ = assert_nonempty_name name
    val pexpr = f "stateful_protocol_model" name (protocol_model_interpretation_params prefix lthy)
    val pdefs = protocol_model_interpretation_defs name
    val proof_state = Interpretation.global_interpretation_cmd pexpr pdefs lthy
  in
    proof_state
  end

fun protocol_security_proof_defs manual_proof name prefix opt_defs opt_meth_level lthy =
  let
    fun f x y z = ([((x,Position.none),((y,true),(Expression.Positional z,[])))],[])
    val _ = assert_nonempty_name name
    val num_defs = length opt_defs
    val pparams = protocol_model_interpretation_params prefix lthy
    val default_defs = [prefix ^ "_" ^ "protocol", prefix ^ "_" ^ "fixpoint"]
    val meth_variant = if String.isSuffix "_coverage_rcv" opt_meth_level then "_coverage_rcv" else ""
    fun g locale_name extra_params = f locale_name name (pparams@map SOME extra_params)
    fun h locale_variant = g ("secure_stateful_protocol" ^ meth_variant ^ locale_variant)
    val (prot_fp_smp_names, pexpr) = if manual_proof
      then (case num_defs of
        0 => (default_defs, h "'" default_defs)
      | 1 => (opt_defs, h "''" opt_defs)
      | 2 => (opt_defs, h "'" opt_defs)
      | _ => (opt_defs, h "" opt_defs))
      else (case num_defs of
        0 => (default_defs, h "''''" default_defs)
      | 1 => (opt_defs, h "''" opt_defs)
      | 2 => (opt_defs, h "''''" opt_defs)
      | _ => (opt_defs, h "'''" opt_defs))
    val _ = assert_all_defined lthy prefix prot_fp_smp_names
  in
    (prot_fp_smp_names, pexpr)
  end

fun protocol_security_proof_proof_state manual_proof name prefix opt_defs opt_meth_level print lthy =
  let
    val (prot_fp_smp_names, pexpr) =
      protocol_security_proof_defs manual_proof name prefix opt_defs opt_meth_level lthy
    val proof_state = lthy |> declare_protocol_checks print
                           |> Interpretation.global_interpretation_cmd pexpr []
  in
    (prot_fp_smp_names, proof_state)
  end

fun protocol_composition_proof_defs name prefix remaining_params lthy =
  let
    fun f x y z = ([((x,Position.none),((y,true),(Expression.Positional z,[])))],[])
    fun g xs = "[" ^ String.concatWith ", " xs ^ "]"
    fun h xs = g (map_index (fn (i,x) => "(" ^ Int.toString i ^ ", " ^ x ^ ")") xs)
    val _ = assert_nonempty_name name
    val (((((pc,smp),sec),ps),psstarprojs),gsmps) = remaining_params
    val _ = assert_all_defined lthy prefix ([pc,smp,sec]@ps@psstarprojs@gsmps)
    val _ = if length ps = length psstarprojs andalso length ps = length gsmps then ()
            else error "Missing arguments"
    val pparams = protocol_model_interpretation_params prefix lthy
    val params = [pc, g ps, g psstarprojs, smp, sec, h gsmps]
    val pexpr = f "composable_stateful_protocols" name (pparams@map SOME params)
  in
    pexpr
  end

fun protocol_composition_proof_proof_state name prefix params print lthy =
  let
    val pexpr = protocol_composition_proof_defs name prefix params lthy
    val state = lthy |> (declare_protocol_check "wellformed_composable_protocols" print #>
                         declare_protocol_check "wellformed_composable_protocols'" print #>
                         declare_protocol_check "composable_protocols" print)
                     |> Interpretation.global_interpretation_cmd pexpr []
  in
    state
  end

val select_proof_method_error_prefix =
  "Error: Invalid option: "

fun select_proof_method_error msg opt_meth_level =
  error (
    select_proof_method_error_prefix ^ opt_meth_level ^ "\n\nValid options:\n" ^
    "1. safe: Instructs Isabelle to " ^ msg ^ " using \"code_simp\" " ^
    "(this is the default setting).\n" ^
    "2. nbe: Instructs Isabelle to use \"normalization\" instead of \"code_simp\".\n" ^
    "3. unsafe: Instructs Isabelle to use \"eval\" instead of \"code_simp\".")

fun select_proof_method _ "safe" = "check_protocol"
  | select_proof_method _ "safe_coverage_rcv" = "check_protocol"
  | select_proof_method _ "nbe" = "check_protocol_nbe"
  | select_proof_method _ "nbe_coverage_rcv" = "check_protocol_nbe"
  | select_proof_method _ "unsafe" = "check_protocol_unsafe"
  | select_proof_method _ "unsafe_coverage_rcv" = "check_protocol_unsafe"
  | select_proof_method msg opt_meth_level = error (
          select_proof_method_error_prefix ^ opt_meth_level ^ "\n\nValid options:\n" ^
          "1. safe: Instructs Isabelle to " ^ msg ^ " using \"code_simp\" " ^
          "(this is the default setting).\n" ^
          "2. nbe: Instructs Isabelle to use \"normalization\" instead of \"code_simp\".\n" ^
          "3. unsafe: Instructs Isabelle to use \"eval\" instead of \"code_simp\".\n" ^
          "4. safe_coverage_rcv: Instructs Isabelle to " ^ msg ^ " using \"code_simp\" " ^
          "(with alternative coverage check).\n" ^
          "5. nbe_coverage_rcv: Instructs Isabelle to use \"normalization\" instead of \"code_simp\" " ^
          "(with alternative coverage check).\n" ^
          "6. unsafe_coverage_rcv: Instructs Isabelle to use \"eval\" instead of \"code_simp\"" ^
          "(with alternative coverage check).")

  | select_proof_method msg opt_meth_level =
      select_proof_method_error msg opt_meth_level

fun select_proof_method_compositionality _ "safe" = "check_protocol_compositionality"
  | select_proof_method_compositionality _ "nbe" = "check_protocol_compositionality_nbe"
  | select_proof_method_compositionality _ "unsafe" = "check_protocol_compositionality_unsafe"
  | select_proof_method_compositionality msg opt_meth_level =
      select_proof_method_error msg opt_meth_level


val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>protocol_model_setup\<close>
    "prove interpretation of protocol model locale into global theory"
    (name_prefix_parser >> (fn (name,prefix) => fn lthy =>
    let fun protocol_model_setup ((name,prefix),lthy) = 
      let
        val proof_state = protocol_model_setup_proof_state name prefix lthy
        val meth =
          let
            val m = "protocol_model_interpretation"
            val _ = Output.information (
                      "Proving protocol model locale instance with proof method " ^ m)
          in
            Method.Source (Token.make_src (m, Position.none) [])
          end
      in
        ml_isar_wrapper.prove_state_simple meth proof_state
      end
    in 
      trac_time.ap_lthy lthy ("protocol_model_setup ("^name^")") protocol_model_setup ((name,prefix),lthy)
    end));

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>manual_protocol_model_setup\<close>
    "prove interpretation of protocol model locale into global theory"
    (name_prefix_parser >> (fn (name,prefix) => fn lthy =>
    let
      val proof_state = protocol_model_setup_proof_state name prefix lthy
      val subgoal_proof = "  subgoal by protocol_model_subgoal\n"
      val _ = Output.information ("Example proof:\n" ^
                Active.sendback_markup_command ("  apply unfold_locales\n"^
                                                subgoal_proof^
                                                subgoal_proof^
                                                subgoal_proof^
                                                subgoal_proof^
                                                subgoal_proof^
                                                "  done\n"))
    in
      proof_state
  end));

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>protocol_security_proof\<close>
    "prove interpretation of secure protocol locale into global theory"
    (security_proof_locale_parser_with_method_choice >> 
    (fn params => fn print => fn lthy =>
    let 
        val ((opt_meth_level,(name,prefix)),opt_defs) = params
        fun protocol_security_proof (params, print, lthy) = 
        let
          val ((opt_meth_level,(name,prefix)),opt_defs) = params
          val (defs, proof_state) =
            protocol_security_proof_proof_state false name prefix opt_defs opt_meth_level print lthy
          val num_defs = length defs
          val meth =
              let
                val m = select_proof_method "prove the protocol secure" opt_meth_level
                val info = Output.information
                val _ = info ("Proving security of protocol " ^ nth defs 0 ^
                              " with proof method " ^ m)
                val _ = if num_defs > 1 then info ("Using fixed point " ^ nth defs 1) else ()
                val _ = if num_defs > 2 then info ("Using SMP set " ^ nth defs 2) else ()
              in
                Method.Source (Token.make_src (m, Position.none) [])
              end
        in
           ml_isar_wrapper.prove_state_simple meth proof_state
        end
      fun protocol_security_proof_with_error_messages (params, print, lthy) =
        protocol_security_proof (params, print, lthy)
        handle
          ERROR msg =>
            if String.isPrefix "Duplicate fact declaration" msg
            then error (
              "Failed to finalize proof because of duplicate fact declarations.\n" ^
              "This might happen if \"" ^ name ^ "\" was used previously.\n" ^
              "\n\nOriginal error message:\n" ^ msg)
            else if String.isPrefix select_proof_method_error_prefix msg
            then error msg
            else (* if String.isPrefix "Wellsortedness error" msg orelse
                    String.isPrefix "Failed to finish proof" msg orelse
                    String.isPrefix "error in proof state" msg
            then *)
            let
              val (def_names,_) =
                protocol_security_proof_defs false name prefix opt_defs opt_meth_level lthy
              val (prot_name,fp_name,smp_name) = case length def_names of
                  0 => (prefix^"_protocol", prefix^"_fixpoint", prefix^"_SMP")
                | 1 => (nth def_names 0,    prefix^"_fixpoint", prefix^"_SMP")
                | 2 => (nth def_names 0,    nth def_names 1,    prefix^"_SMP")
                | _ => (nth def_names 0,    nth def_names 1,    nth def_names 2)
            in error (
              "Failed to prove the protocol secure.\n" ^
              "Click on the following to inspect which parts of the proof failed:\n" ^
              Active.sendback_markup_command (
                (if length def_names < 2
                 then "\<comment> \<open>First compute a fixed-point\<close>\n" ^
                      "compute_fixpoint "^prot_name^" "^fp_name^"\n\n"
                 else "")^
                "\<comment> \<open>Is the fixed point free of attack signals?\<close>\n" ^
                "value \"attack_notin_fixpoint "^fp_name^"\"\n\n" ^
                "\<comment> \<open>Is the protocol covered by the fixed point?\<close>\n" ^
                "value \"protocol_covered_by_fixpoint "^fp_name^" "^prot_name^"\"\n\n" ^
                "\<comment> \<open>Is the fixed point analyzed?\<close>\n" ^
                "value \"analyzed_fixpoint "^fp_name^"\"\n\n" ^
                "\<comment> \<open>Is the protocol well-formed?\<close>\n" ^
                (if length def_names < 3
                 then "value \"wellformed_protocol "^prot_name^"\"\n\n"
                 else "value \"wellformed_protocol' "^prot_name^" "^smp_name^"\"\n\n")^
                "\<comment> \<open>Is the fixed point well-formed?\<close>\n" ^
                "value \"wellformed_fixpoint "^fp_name^"\"") ^
              "\n\nOriginal error message:\n" ^ msg)
            end
            (* else error msg *)
    in 
      trac_time.ap_lthy lthy ("protocol_security_proof ("^name^")")
                        protocol_security_proof_with_error_messages (params, print, lthy)
    end));

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>manual_protocol_security_proof\<close>
    "prove interpretation of secure protocol locale into global theory"
    (security_proof_locale_parser >> (fn params => fn print => fn lthy =>
    let
      val ((name,prefix),opt_defs) = params
      val (defs, proof_state) =
        protocol_security_proof_proof_state true name prefix opt_defs "safe" print lthy
      val subgoal_proof =
        let
          val m = "code_simp" (* case opt_meth_level of
              "safe" => "code_simp"
            | "nbe" => "normalization"
            | "unsafe" => "eval"
            | _ => error ("Invalid option: " ^ opt_meth_level) *)
        in
          "  subgoal by " ^ m ^ "\n"
        end
      val _ = Output.information ("Example proof:\n" ^
                Active.sendback_markup_command ("  apply check_protocol_intro\n"^
                                                subgoal_proof^
                                                (if length defs = 1 then ""
                                                 else subgoal_proof^
                                                      subgoal_proof^
                                                      subgoal_proof^
                                                      subgoal_proof)^
                                                 "  done\n"))
    in
      proof_state
    end
    ));

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>protocol_composition_proof\<close>
    "prove interpretation of composed protocol locale into global theory"
    (composed_protocol_locale_parser_with_method_choice >> (fn params => fn print => fn lthy =>
    let val ((_,(name,_)),_) = params
        fun protocol_composition_proof (params,lthy) = 
      let
        val ((opt_meth_level,(name,prefix)),remaining_params) = params
        val proof_state =
              protocol_composition_proof_proof_state name prefix remaining_params print lthy
        val meth =
          let
            val m = select_proof_method_compositionality "use" opt_meth_level
            val _ = Output.information (
                      "Proving composability of protocol " ^ name ^ " with proof method " ^ m)
          in
            Method.Source (Token.make_src (m, Position.none) [])
          end
      in
        ml_isar_wrapper.prove_state_simple meth proof_state
      end
    in 
      trac_time.ap_lthy lthy
        ("protocol_composition_proof ("^name^")")
        protocol_composition_proof (params,lthy)
    end));

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>manual_protocol_composition_proof\<close>
    "prove interpretation of composed protocol locale into global theory"
    (composed_protocol_locale_parser >> (fn params => fn print => fn lthy =>
    let
      val ((name,prefix),remaining_params) = params
      val proof_state =
            protocol_composition_proof_proof_state name prefix remaining_params print lthy
      val subgoal_proof = "  subgoal by code_simp\n"
      val _ = Output.information ("Example proof:\n" ^
                Active.sendback_markup_command ("  apply check_protocol_intro\n"^
                                                subgoal_proof^
                                                subgoal_proof^
                                                subgoal_proof^
                                                subgoal_proof^
                                                subgoal_proof^
                                                subgoal_proof^
                                                "  done\n"))
    in
      proof_state
    end
    ));
\<close>

ML\<open>
fun listterm_to_list' _    (Const ("List.list.Nil",tau)) = ([],tau)
  | listterm_to_list' lthy ((Const ("List.list.Cons",_) $ t1) $ t2) =
    let val (s,tau) = listterm_to_list' lthy t2
    in (t1::s,tau) end
  | listterm_to_list' lthy t =
      error ("Unexpected term (expected a list constructor): " ^ Syntax.string_of_term lthy t)

fun listterm_to_list lthy = fst o listterm_to_list' lthy

fun pairterm_to_pair' _    ((Const ("Product_Type.Pair",tau) $ x) $ y) = ((x,y),tau)
  | pairterm_to_pair' lthy t =
      error ("Error: Expected a pair term but got " ^ Syntax.string_of_term lthy t)

fun pairterm_to_pair lthy = fst o pairterm_to_pair' lthy

fun constrexpr_to_string lthy protocol t = let
  val trac = trac_definitorial_package.lookup_trac protocol lthy
  val trac_name = #name trac

  val sets_type_name = Local_Theory.full_name lthy (Binding.name (trac_name ^ "_sets"))
  val enum_type_name = Local_Theory.full_name lthy (Binding.name (trac_name ^ "_enum_consts"))
  val fun_type_name = Local_Theory.full_name lthy (Binding.name (trac_name ^ "_fun"))
  val atom_type_name = Local_Theory.full_name lthy (Binding.name (trac_name ^ "_atom"))

  fun print_const_expr x =
        if String.isPrefix sets_type_name x
        then String.extract (x,size sets_type_name+1,NONE)
        else if String.isPrefix enum_type_name x
        then String.extract (x,size enum_type_name+1,NONE)
        else if String.isPrefix fun_type_name x
        then String.extract (x,size fun_type_name+1,NONE)
        else if String.isPrefix atom_type_name x
        then String.extract (x,size atom_type_name+1,NONE)
        else error ("Unexpected constant expression: " ^ x)
in print_const_expr t end

fun setexpr_to_string lthy protocol t = let
  fun err msg t = error (msg ^ ": " ^ Syntax.string_of_term lthy t)

  fun print_set_expr' (Const (x,_)) = [constrexpr_to_string lthy protocol x]
    | print_set_expr' (t1 $ t2) = print_set_expr' t1@print_set_expr' t2
    | print_set_expr' t = err "Unexpected set expression subterm" t

  fun print_set_expr t =
    case print_set_expr' t of
      [x] => x
    | x::xs => x ^ "(" ^ String.concatWith "," xs ^ ")"
    | _ => err "Unexpected set expression" t
in print_set_expr t end

fun abstractionexpr_to_list lthy protocol t = let
  fun print_abs (Const ("Orderings.bot_class.bot",_)) = []
    | print_abs (t $ Const ("Orderings.bot_class.bot",_)) = print_abs t
    | print_abs (Const ("Set.insert",_) $ t) = [setexpr_to_string lthy protocol t]
    | print_abs (t1 $ t2) = print_abs t1@print_abs t2
    | print_abs t = error ("Unexpected abstract value expression: " ^ Syntax.string_of_term lthy t)
in print_abs t end

fun protterm_to_string_no_eval var_printer protocol protterm lthy = let
  fun print_raw (Const (x,_)) = "Const (" ^ x ^ ",_)"
    | print_raw (t $ s) = "(" ^ print_raw t ^  " $ " ^ print_raw s ^ ")"
    | print_raw _ = "_"

  fun err msg t = error (msg ^ ": " ^ Syntax.string_of_term lthy t ^ "\n" ^ print_raw t)
  val trac = trac_definitorial_package.lookup_trac protocol lthy
  val trac_name = #name trac
  val trac_fun_spec = Option.getOpt (#function_spec trac, {private = [], public = []})
  val is_priv_fun = member (fn (s,t) => s = #1 t) (#private trac_fun_spec)
  
  val fun_type_name = Local_Theory.full_name lthy (Binding.name (trac_name ^ "_fun"))

  val print_list = listterm_to_list lthy
  val print_const_expr = constrexpr_to_string lthy protocol
  val print_set_expr = setexpr_to_string lthy protocol

  fun print_abs t =
      let val a = abstractionexpr_to_list lthy protocol t
      in "val(" ^ (if a = [] then "0" else String.concatWith "," a) ^ ")" end

  fun print_trm (Const ("Term.term.Var",_) $ t
        ) = (case t of
               ((Const ("Product_Type.Pair",_) $ _) $ _) => var_printer (pairterm_to_pair lthy t)
             | _ => print_trm t)
    | print_trm ((Const ("Term.term.Fun",_) $ (Const ("Transactions.prot_fun.Abs",_) $ t)) $
                   Const ("List.list.Nil",_)
        ) = print_abs t
    | print_trm (
          (Const ("Term.term.Fun",_)$Const ("Transactions.prot_fun.OccursFact",_))
          $((Const ("List.list.Cons",_)
            $((Const ("Term.term.Fun",_)$Const ("Transactions.prot_fun.OccursSec",_))
             $Const ("List.list.Nil",_)))
           $((Const ("List.list.Cons",_) $ t) $ Const ("List.list.Nil",_)))
        ) = "occurs(" ^ print_trm t ^ ")"
    | print_trm (
          (Const ("Term.term.Fun",_) $ (Const ("Transactions.prot_fun.Attack",_) $ _)) $ _
        ) = "attack"
    | print_trm (
          (Const ("Term.term.Fun",_) $ (Const ("Transactions.prot_fun.Set",_) $ f)) $ ts
        ) = let val gs = map print_trm (print_list ts)
            in (case gs of
                  [] => print_set_expr f
                | xs => print_trm f ^ "(" ^ String.concatWith "," xs ^ ")")
            end
    | print_trm (
          (Const ("Term.term.Fun",_) $ (Const ("Transactions.prot_fun.Fu",_) $ f)) $ ts
        ) = let val g = print_trm f; val gs = map print_trm (print_list ts)
            in (case (if is_priv_fun g then (case gs of [] => [] | _::gs' => gs') else gs) of
                  [] => g
                | xs => g ^ "(" ^ String.concatWith "," xs ^ ")")
            end
    | print_trm (
          (Const ("Transactions.prot_atom.Atom",_) $ Const (t,_))
        ) = print_const_expr t
    | print_trm ((Const ("Product_Type.Pair",_) $ t1) $ t2) =
        "(" ^ print_abs t1 ^ "," ^ print_abs t2 ^ ")"
    | print_trm (Const (x,tx) $ Const (y,ty)) =
        if x = fun_type_name ^ ".enum"
        then print_const_expr y
        else err "Unexpected protocol/fixpoint term" (Const (x,tx) $ Const (y,ty))
    | print_trm (Const (x,_)) =
        if String.isPrefix "Transactions.prot_atom" x
        then String.extract (x,size "Transactions.prot_atom"+1,NONE)
        else print_const_expr x
    | print_trm t = err "Unexpected protocol/fixpoint term" t;
in
  print_trm protterm
end

fun prottermtype_to_string_no_eval var_printer protocol protterm lthy =
  protterm_to_string_no_eval var_printer protocol protterm lthy

fun fixpoint_to_string protocol fixpoint lthy = let
  fun err msg t = error (msg ^ ": " ^ Syntax.string_of_term lthy t)
  val fpterm = "let (FP,_,TI) = (" ^ fixpoint ^ ") in (FP,TI)"

  fun print_fp' s = protterm_to_string_no_eval
          (fn _ => error "Unexpected term variable in fixpoint")
          protocol s lthy

  fun print_fp ((Const ("Product_Type.Pair",_) $ t1) $ t2) =
        String.concatWith "\n" (map print_fp' (listterm_to_list lthy t1)@
                                map (fn x => "timplies" ^ print_fp' x) (listterm_to_list lthy t2))
    | print_fp t = err "Unexpected fixpoint term pair" t;
in
  (print_fp o eval_term lthy o Syntax.read_term lthy) fpterm
end

fun transaction_label_to_string t lthy = let
    fun err msg t = error (msg ^ ": " ^ Syntax.string_of_term lthy t)
  
    fun print_label (Const ("Labeled_Strands.strand_label.LabelN",_) $ _) = " "
          (* Syntax.string_of_term lthy t *)
      | print_label (Const ("Labeled_Strands.strand_label.LabelS",_)) = "*"
      | print_label t = err "Unexpected action label term" t
  in print_label t end

fun transaction_action_to_string var_printer protocol t lthy = let
    fun err msg t = error (msg ^ ": " ^ Syntax.string_of_term lthy t)
    fun print_trm s = protterm_to_string_no_eval var_printer protocol s lthy

    fun print_action (Const ("Stateful_Strands.stateful_strand_step.Send",_) $ ts
          ) = "send " ^ String.concatWith ", " (map print_trm (listterm_to_list lthy ts))
      | print_action (Const ("Stateful_Strands.stateful_strand_step.Receive",_) $ ts
          ) = "receive " ^ String.concatWith ", " (map print_trm (listterm_to_list lthy ts))
      | print_action (((Const ("Stateful_Strands.stateful_strand_step.Equality",_) $ _) $ t1) $ t2
          ) = print_trm t1 ^ " == " ^ print_trm t2
      | print_action (((Const ("Stateful_Strands.stateful_strand_step.InSet",_) $ _) $ t1) $ t2
          ) = print_trm t1 ^ " in " ^ print_trm t2
      | print_action ((Const ("Stateful_Strands.stateful_strand_step.Insert",_) $ t1) $ t2
          ) = "insert " ^ print_trm t1 ^ " " ^ print_trm t2
      | print_action ((Const ("Stateful_Strands.stateful_strand_step.Delete",_) $ t1) $ t2
          ) = "delete " ^ print_trm t1 ^ " " ^ print_trm t2
      | print_action (((Const ("Stateful_Strands.stateful_strand_step.NegChecks",_) $ xs) $ ts1) $ ts2
          ) = let fun f (a,b) = print_trm a ^ " != " ^ print_trm b
                  fun g (a,b) = print_trm a ^ " notin " ^ print_trm b
                  val ys = map print_trm (listterm_to_list lthy xs)
                  val ss1 = map (f o pairterm_to_pair lthy) (listterm_to_list lthy ts1)
                  val ss2 = map (g o pairterm_to_pair lthy) (listterm_to_list lthy ts2)
              in (if ys = [] then "" else "forall " ^ String.concatWith ", " ys ^ " ") ^
                 String.concatWith " or " (ss1@ss2)
              end
      | print_action t = err "Unexpected transaction action term" t
  in print_action t end

fun transaction_labeled_action_to_string var_printer protocol t lthy = let
    fun err msg t = error (msg ^ ": " ^ Syntax.string_of_term lthy t)

    fun print_laction ((Const ("Product_Type.Pair",_) $ t1) $ t2) =
          transaction_label_to_string t1 lthy ^ " " ^
          transaction_action_to_string var_printer protocol t2 lthy
      | print_laction t = err "Unexpected labeled transaction action term" t
  in print_laction t end

fun transaction_to_string var_printer protocol transactionterm lthy = let
  val evaltrm = eval_term lthy o Syntax.read_term lthy

  val trfresh   = "Transactions.transaction_fresh (" ^ transactionterm ^ ")"
  val trreceive = "Transactions.transaction_receive (" ^ transactionterm ^ ")"
  val trchecks  = "Transactions.transaction_checks (" ^ transactionterm ^ ")"
  val trupdates = "Transactions.transaction_updates (" ^ transactionterm ^ ")"
  val trsend    = "Transactions.transaction_send (" ^ transactionterm ^ ")"

  fun print_fresh xs =
        if xs = [] then []
        else ["  new " ^ String.concatWith ", " (map (var_printer o pairterm_to_pair lthy) xs)]

  fun print_tr' s = transaction_labeled_action_to_string var_printer protocol s lthy

  val print_tr =
    String.concatWith "\n" (
      (map print_tr' o listterm_to_list lthy o evaltrm) trreceive@
      (map print_tr' o listterm_to_list lthy o evaltrm) trchecks@
      (print_fresh   o listterm_to_list lthy o evaltrm) trfresh@
      (map print_tr' o listterm_to_list lthy o evaltrm) trupdates@
      (map print_tr' o listterm_to_list lthy o evaltrm) trsend)
in
  print_tr
end

fun transaction_list_to_string var_printer protocol transactionlistterm lthy = let
  fun err msg t = error (msg ^ ": " ^ Syntax.string_of_term lthy t)
  val evaltrm = eval_term lthy o Syntax.read_term lthy

  fun print_fresh i xs =
        if xs = [] then []
        else ["  new " ^ String.concatWith ", " (map (var_printer i o pairterm_to_pair lthy) xs)]

  fun print_tr' i s = transaction_labeled_action_to_string (var_printer i) protocol s lthy

  fun print_tr i ((Const ("Product_Type.Pair",_) $ trfresh) $
                  ((Const ("Product_Type.Pair",_) $ trreceive) $
                   ((Const ("Product_Type.Pair",_) $ trchecks) $
                    ((Const ("Product_Type.Pair",_) $ trupdates) $ trsend)))
        ) = String.concatWith "\n" (
          (map (print_tr' i) o listterm_to_list lthy) trreceive@
          (map (print_tr' i) o listterm_to_list lthy) trchecks@
          (print_fresh i     o listterm_to_list lthy) trfresh@
          (map (print_tr' i) o listterm_to_list lthy) trupdates@
          (map (print_tr' i) o listterm_to_list lthy) trsend)
    | print_tr _ t = err "Unexpected term" t

  fun print_trs trs = String.concatWith "\n\n" (map_index (fn (i,x) => print_tr i x) trs)

  fun trfresh s   = "Transactions.transaction_fresh (" ^ s ^ ")"
  fun trreceive s = "Transactions.transaction_receive (" ^ s ^ ")"
  fun trchecks s  = "Transactions.transaction_checks (" ^ s ^ ")"
  fun trupdates s = "Transactions.transaction_updates (" ^ s ^ ")"
  fun trsend s    = "Transactions.transaction_send (" ^ s ^ ")"

  val f = "let f = \<lambda>X. (" ^ trfresh "X" ^ ", " ^ trreceive "X" ^ ", " ^ trchecks "X" ^ ", "
                                  ^ trupdates "X" ^ ", " ^ trsend "X" ^ ")" ^
          "in map f (" ^ transactionlistterm ^ ")"

  val transactiontermlist = listterm_to_list lthy (evaltrm f)
in
  print_trs transactiontermlist
end

val _ = Outer_Syntax.local_theory' @{command_keyword "print_transaction_strand"}
        "print protocol transaction as transaction strand"
        (Parse.name -- Parse.name >>
        (fn (protocol, transaction) => fn print => fn lthy =>
          let fun print_tr ((protocol,transaction), _, lthy) = 
            let
              val _ = assert_defined lthy transaction
              fun f a = protterm_to_string_no_eval (fn _ => error "Unexpected variable")
                                                   protocol a lthy
              fun g (a,b) =
                  if f a = "Value" orelse f a = "value"
                  then "X" ^ Syntax.string_of_term lthy b
                  else "Y[" ^ f a ^ ", " ^ Syntax.string_of_term lthy b ^ "]"
              val _ = Output.information (transaction_to_string g protocol transaction lthy)
            in
              lthy
            end
          in 
            trac_time.ap_lthy lthy
              ("print_transaction_strand ("^protocol^")")
              print_tr
              ((protocol,transaction), print, lthy)
          end ));


val _ = Outer_Syntax.local_theory' @{command_keyword "print_transaction_strand_list"}
        "print protocol transaction list as transaction strand list"
        (Parse.name -- Parse.name >>
        (fn (protocol, transaction_list) => fn print => fn lthy =>
          let fun print_tr ((protocol,transaction_list), _, lthy) = 
            let
              val _ = assert_defined lthy transaction_list
              fun f a = protterm_to_string_no_eval (fn _ => error "Unexpected variable")
                                                   protocol a lthy
              fun g i (a,b) =
                  if f a = "Value" orelse f a = "value"
                  then "X" ^ Syntax.string_of_term lthy b ^ "_" ^ Int.toString i
                  else "Y[" ^ f a ^ ", " ^ Syntax.string_of_term lthy b ^ "_" ^ Int.toString i ^ "]"
              val _ = Output.information (transaction_list_to_string g protocol transaction_list lthy)
            in
              lthy
            end
          in 
            trac_time.ap_lthy lthy
              ("print_transaction_strand_list ("^protocol^")")
              print_tr
              ((protocol,transaction_list), print, lthy)
          end ));

val _ = Outer_Syntax.local_theory' @{command_keyword "print_attack_trace"}
        "print attack trace"
        (Parse.name -- Parse.name -- Parse.name >>
        (fn ((protocol, protocol_def), attack_trace) => fn print => fn lthy =>
          let fun print_tr ((protocol,protocol_def,attack_trace), _, lthy) = 
            let
              val evaltrm = eval_term lthy o Syntax.read_term lthy
              val _ = assert_defined lthy protocol_def
              val _ = assert_defined lthy attack_trace
              fun f i b = "X" ^ b ^ "_" ^ Int.toString i
              fun g i (_,b) = f i (Syntax.string_of_term lthy b)
              val t1 = "map (\<lambda>(i,_). add_occurs_msgs (" ^ protocol_def ^ " ! i)) " ^ attack_trace
              val t2 = "map (map (\<lambda>((_,i),xs). (i,xs))) (map snd " ^ attack_trace ^ ")"
              val s = t2 |> evaltrm
                         |> listterm_to_list lthy
                         |> map (listterm_to_list lthy)
                         |> map (map (pairterm_to_pair lthy))
                         |> map (map (fn (a,b) => (Syntax.string_of_term lthy a,
                                                   abstractionexpr_to_list lthy protocol b)))
                         |> map_index (fn (i,ts) =>
                              map (fn (a,xs) => f i a ^ ": {" ^ String.concatWith ", " xs ^ "}") ts)
                         |> List.concat
              val u = transaction_list_to_string g protocol t1 lthy
              val _ = Output.information (
                        (if s <> []
                         then "Abstractions:\n" ^ String.concatWith "\n" s ^ "\n\n"
                         else "") ^
                        ("Attack trace:\n" ^ u))
            in
              lthy
            end
          in 
            trac_time.ap_lthy lthy
              ("print_attack_trace ("^protocol^","^protocol_def^","^attack_trace^")")
              print_tr
              ((protocol,protocol_def,attack_trace), print, lthy)
          end ));

val _ = Outer_Syntax.local_theory' @{command_keyword "print_fixpoint"} 
        "print protocol fixpoint"
        (Parse.name -- Parse.name >>
        (fn (protocol, fixpoint) => fn print => fn lthy =>
          let fun print_fixpoint ((protocol,fixpoint), _, lthy) = 
            let
              val _ = assert_defined lthy fixpoint
              val _ = Output.information (fixpoint_to_string protocol fixpoint lthy)
            in
              lthy
            end
          in 
            trac_time.ap_lthy lthy ("print_fixpoint ("^protocol^")") print_fixpoint ((protocol,fixpoint), print, lthy) 
          end ));

  val _ = Outer_Syntax.local_theory' @{command_keyword "save_fixpoint"} 
          "Write fixpoint to file." 
          ((Parse.name -- Parse.name -- Parse.name >> (
            fn ((protocol_name, fixpoint_filename), fixpoint_name) => fn _ => fn lthy =>
          let
            fun save_fixpoint ((protocol_name, fixpoint_name), fixpoint_filename, lthy) =
              let
                val _ = assert_defined lthy fixpoint_name
                fun write f s =
                      if File.exists f
                      then error ("Error: Cannot write to file: File already exists")
                      else File.write f s
                val filename =
                      Path.explode (
                        trac.mk_abs_filename (Proof_Context.theory_of lthy) fixpoint_filename)
                val _ = Output.information ("Evaluating fixed-point term " ^ fixpoint_name)
                val fp_str = fixpoint_to_string protocol_name fixpoint_name lthy
                val _ = Output.information (
                          "Writing fixed point to file " ^ Path.print filename)
                val _ = write filename fp_str
              in
                lthy
              end
          in
            trac_time.ap_lthy lthy ("save_fixpoint") save_fixpoint ((protocol_name, fixpoint_name), fixpoint_filename, lthy)
          end)));


  (* TODO: move? *)
  (* TODO: check that chunks are not defined before defining them *)
  fun eval_define_declare_fixpoint chunk_size chunk_suffix (name, t) print lthy = let 
    val mk_tuple = trac_definitorial_package.mk_tuple
    val mk_list = trac_definitorial_package.mk_list
    val mk_listT = trac_definitorial_package.mk_listT
    val full_name = trac_definitorial_package.full_name

    fun chunk_name n = name ^ chunk_suffix ^ Int.toString n

    fun arg name t =
      ((Binding.name name, NoSyn), ((Binding.name (name ^ "_def"),@{attributes [code]}), t))

    fun def_trm (name,trm) lthy = snd (Local_Theory.define (arg name trm) lthy)

    fun append_term tau = Term.Const (@{const_name "append"}, [tau,tau] ---> tau)
    fun nil_term tau = Term.Const (@{const_name "Nil"}, tau)

    val ((fp,fp_elemT),(occ,occ_elemT),(ti,ti_elemT)) =
      let fun chop (l,Type (_,[tau])) = (chop_groups chunk_size l, tau)
            | chop (_,tau) = error ("Expected type with one type-parameter but got " ^
                                    Syntax.string_of_typ lthy tau)
          val ltl = chop o listterm_to_list' lthy
          val (fp,occ_ti) = pairterm_to_pair lthy (eval_term lthy t)
          val (occ,ti) = pairterm_to_pair lthy occ_ti
      in (ltl fp, ltl occ, ltl ti) end

    fun mk_chunk_trm ch tau lthy = Term.Const (full_name ch lthy, mk_listT tau)

    datatype ChunksVariant =
      NoChunks | SingleChunk of term | MultipleChunks of (bstring * term) list

    fun chunk [] _ _ = NoChunks
      | chunk [ch] tau _ = SingleChunk (mk_list tau ch)
      | chunk trms tau i =
          MultipleChunks (map_index (fn (j,ch) => (chunk_name (i+j), mk_list tau ch)) trms)

    fun append_chunks NoChunks tau _ = mk_list tau []
      | append_chunks (SingleChunk ch) _ _ = ch
      | append_chunks (MultipleChunks chs) tau lthy = let
          fun f [] = nil_term (mk_listT tau)
            | f [ch] = mk_chunk_trm ch tau lthy
            | f (ch::chs) = append_term (mk_listT tau) $ mk_chunk_trm ch tau lthy $ f chs
        in f (map fst chs) end

    fun chunks_len (MultipleChunks chs) = length chs
      | chunks_len _ = 0

    fun def_chunks (MultipleChunks chs) lthy = fold def_trm chs lthy
      | def_chunks _ lthy = lthy (* we don't use chunks when there would be at most one *)

    val fp_chunks_trms  = chunk fp  fp_elemT  0
    val occ_chunks_trms = chunk occ occ_elemT (chunks_len fp_chunks_trms)
    val ti_chunks_trms  = chunk ti  ti_elemT  (chunks_len fp_chunks_trms+chunks_len occ_chunks_trms)

    val lthy = snd (Local_Theory.begin_nested lthy)
    val lthy = def_chunks fp_chunks_trms lthy
    val lthy = def_chunks occ_chunks_trms lthy
    val lthy = def_chunks ti_chunks_trms lthy
    val lthy = Local_Theory.end_nested lthy

    val lthy = snd (Local_Theory.begin_nested lthy)

    val fpt_trm = mk_tuple [
      append_chunks fp_chunks_trms fp_elemT lthy,
      append_chunks occ_chunks_trms occ_elemT lthy,
      append_chunks ti_chunks_trms ti_elemT lthy]

    val lthy = def_trm (name, fpt_trm) lthy
  in
    (fpt_trm, Local_Theory.end_nested lthy)
  end

  (* TODO: chunks *)
  val _ = Outer_Syntax.local_theory' @{command_keyword "load_fixpoint"} 
          "Import fixpoint from file." 
          ((Parse.name -- Parse.name -- Parse.name >> (
            fn ((protocol_name, fixpoint_filename), fixpoint_name) => fn print => fn lthy =>
          let
            fun load_fixpoint ((protocol_name, fixpoint_filename), fixpoint_name, lthy) =
              let
                val _ = assert_not_defined lthy fixpoint_name
                val filename =
                      Path.explode (
                        trac.mk_abs_filename (Proof_Context.theory_of lthy) fixpoint_filename)
                val _ = Output.information (
                          "Reading fixed point from file " ^ Path.print filename)
                fun read f =
                      if File.exists f
                      then File.read f
                      else error ("Error: Cannot read file: File does not exist")
                val fp_str = TracFpParser.parse_str (read filename)
                val trac = trac_definitorial_package.lookup_trac protocol_name lthy
                val cert_fp = TracProtocolCert.certify_fixpoint trac fp_str
                val cert_trac = TracProtocolCert.certifyProtocol trac
                val fp_trm = trac_definitorial_package.fp_triple_to_hol cert_fp cert_trac lthy
              in
                #2 (ml_isar_wrapper.define_constant_definition' (fixpoint_name, fp_trm) print lthy)
              end
          in
            trac_time.ap_lthy lthy ("load_fixpoint") load_fixpoint ((protocol_name, fixpoint_filename), fixpoint_name, lthy)
          end)));

val _ = Outer_Syntax.local_theory' @{command_keyword "compute_fixpoint"} 
        "evaluate and define protocol fixpoint"
        ((Scan.option (\<^keyword>\<open>[\<close> |-- Parse.name --| \<^keyword>\<open>]\<close>)) --
         Parse.name -- Parse.name -- Scan.option Parse.name >>
        (fn (((opt, protocol), fixpoint), opt_trace) => fn print => fn lthy =>
          let fun compute_fixpoint (((protocol,fixpoint),opt_trace), print, lthy) = 
            let
              val _ = assert_defined lthy protocol
              val _ = assert_not_defined lthy fixpoint
              val _ = Option.app (assert_not_defined lthy) opt_trace
              val _ = Output.information ("Computing a fixed point for protocol " ^ protocol)
              val _ = case opt of (* TODO: don't compute the fixpoint twice *)
                        NONE => ()
                      | SOME "check_for_attacks" => 
                        let val no_attack = eval_term lthy (Syntax.read_term lthy (
                              "(attack_notin_fixpoint \<circ> compute_fixpoint_fun) " ^ protocol))
                            val _ = case no_attack of
                                Term.Const ("HOL.True", _) =>
                                Output.information "The fixed point is free of attack signals."
                              | Term.Const ("HOL.False", _) =>
                                Output.information "The fixed point contains an attack signal."
                              | _ => error ("Error: Unexpected term: " ^ @{make_string} no_attack)
                        in () end
                      | SOME opt => error ("Error: Invalid option " ^ opt)
              val fp = (fixpoint, Syntax.read_term lthy ("compute_fixpoint_fun " ^ protocol))
              val opt_tr = Option.map (* TODO: don't compute the fixpoint twice *)
                            (fn trace =>
                              (trace, Syntax.read_term lthy
                                        ("(compute_reduced_attack_trace " ^ protocol ^
                                         " \<circ> snd \<circ> compute_fixpoint_with_trace) " ^ protocol)))
                            opt_trace
            in
              ((snd o eval_define_declare_fixpoint 15 "_chunk" fp print) lthy |>
               (fn lthy => case opt_tr of
                              SOME tr => (snd o eval_define_declare tr print) lthy
                            | NONE => lthy))
              handle
                ERROR msg =>
                  let
                    val _ = warning ("Failed to compute the set with eval. Retrying with NBE.\n" ^
                                     "Original error message:\n" ^ msg)
                  in
                    ((snd o eval_define_declare_nbe fp print) lthy |>
                     (fn lthy => case opt_tr of
                                    SOME tr => (snd o eval_define_declare_nbe tr print) lthy
                                  | NONE => lthy))
                  end
              
            end
          in 
            trac_time.ap_lthy lthy ("compute_fixpoint ("^protocol^")") compute_fixpoint (((protocol,fixpoint),opt_trace), print, lthy)  
          end ));

val _ = Outer_Syntax.local_theory' @{command_keyword "compute_SMP"} 
        "evaluate and define a finite representation of the sub-message patterns of a protocol"
        ((Scan.optional (\<^keyword>\<open>[\<close> |-- Parse.name --| \<^keyword>\<open>]\<close>) "no_optimizations") --
          Parse.name -- Parse.name >> (fn ((opt,prot), smp) => fn print => fn lthy =>
          let fun compute_smp (((opt, prot), smp), print, lthy) = 
          let
            val prot' = prot
            val rmd = "List.remdups"
            val f = "Stateful_Strands.trms_list\<^sub>s\<^sub>s\<^sub>t"
            val g =
              "(\<lambda>T. " ^ f ^ " T@map (pair' prot_fun.Pair) (Stateful_Strands.setops_list\<^sub>s\<^sub>s\<^sub>t T))"
            fun s trms =
              "(" ^ rmd ^ " (List.concat (List.map (" ^ trms ^
              " \<circ> Labeled_Strands.unlabel \<circ> transaction_strand) " ^ prot' ^ ")))"
            val opt1 = "remove_superfluous_terms \<Gamma>"
            val opt2 = "generalize_terms \<Gamma> is_Var"
            val gsmp_opt =
              "generalize_terms \<Gamma> (\<lambda>t. is_Var t \<and> t \<noteq> TAtom AttackType \<and> " ^
              "t \<noteq> TAtom SetType \<and> t \<noteq> TAtom OccursSecType \<and> \<not>is_Atom (the_Var t))"
            val smp_fun = "SMP0 Ana \<Gamma>"
            fun smp_fun' opts =
              "(\<lambda>T. let T' = (" ^ rmd ^ " \<circ> " ^ opts ^ " \<circ> " ^ smp_fun ^
              ") T in List.map (\<lambda>t. t \<cdot> Typed_Model.var_rename (Typed_Model.max_var_set " ^
              "(Messages.fv\<^sub>s\<^sub>e\<^sub>t (set (T@T'))))) T')"
            val cmd =
              if opt = "no_optimizations" then smp_fun ^ " " ^ s f
              else if opt = "optimized"
              then smp_fun' (opt1 ^ " \<circ> " ^ opt2) ^ " " ^ s f
              else if opt = "GSMP"
              then smp_fun' (opt1 ^ " \<circ> " ^ gsmp_opt) ^ " " ^ s g
              else if opt = "composition"
              then smp_fun ^ " " ^ s g
              else if opt = "composition_optimized"
              then smp_fun' (opt1 ^ " \<circ> " ^ opt2) ^ " " ^ s g
              else error ("Error: Invalid option: " ^ opt ^ "\n\nValid options:\n" ^
                    "1. no_optimizations: Computes the finite SMP representation set " ^
                    "without any optimizations (this is the default setting).\n" ^
                    "2. optimized: Applies optimizations to reduce the size of the computed " ^
                    "set, but this might not be sound.\n" ^
                    "3. GSMP: Computes a set suitable for use in checking GSMP disjointness.\n" ^
                    "4. composition: Computes a set suitable for checking type-flaw resistance " ^
                    "of composed protocols.\n" ^
                    "5. composition_optimized: An optimized variant of the previous setting.")
            val _ = assert_defined lthy prot
            val _ = assert_not_defined lthy smp
            val _ = Output.information (
                      "Computing a finite SMP representation set for protocol " ^ prot)
          in
            (snd o eval_define_declare (smp, Syntax.read_term lthy cmd) print) lthy
            handle
              ERROR msg =>
                let
                  val _ = warning ("Failed to compute the set with eval. Retrying with NBE.\n" ^
                                   "Original error message:\n" ^ msg)
                in
                  (snd o eval_define_declare_nbe (smp, Syntax.read_term lthy cmd) print) lthy
                end
          end 
        in
         trac_time.ap_lthy lthy ("compute_SMP ("^prot^")") compute_smp (((opt, prot), smp), print, lthy)
        end));

val _ = Outer_Syntax.local_theory' @{command_keyword "compute_shared_secrets"} 
        "evaluate and define a finite representation of shared secrets as the intersection of GSMP sets"
        (Scan.repeat1 Parse.name >> (fn params => fn print => fn lthy =>
          let fun compute_shared_secrets (params, print, lthy) = 
          let
            val _ = if length params < 3 then error "Not enough arguments" else ()
            val (gsmps, sec) = split_last params
            val xs = "xs"
            val cmd =
              "let " ^ xs ^ " = [" ^ String.concatWith ", " gsmps ^ "] in " ^
              "(" ^
                (* "remove_superfluous_terms \<Gamma> \<circ> generalize_terms \<Gamma> ((=) (TAtom SetType)) \<circ> " ^ *)
                "remove_superfluous_terms \<Gamma> \<circ> " ^
                "(" ^
                  "concat \<circ> map " ^
                  "(\<lambda>p. filter " ^
                    "(\<lambda>t. list_ex (\<lambda>s. \<Gamma> t = \<Gamma> s \<and> mgu t s \<noteq> None) (" ^ xs ^ " ! snd p))" ^
                    "(" ^ xs ^ " ! fst p)" ^
                  ")" ^
                ")" ^
              ") (" ^
                "filter (\<lambda>p. fst p \<noteq> snd p) ((\<lambda>p. List.product p p) [0..<length " ^ xs ^ "])" ^
              ")"

            val _ = map (assert_defined lthy) gsmps
            val _ = assert_not_defined lthy sec
            val _ = Output.information (
                      "Computing a finite representation of the shared secrets for the " ^
                      "protocols with GSMP sets " ^ String.concatWith ", " gsmps)
          in
            (snd o eval_define_declare (sec, Syntax.read_term lthy cmd) print) lthy
          end 
        in
         trac_time.ap_lthy lthy
          ("compute_shared_secrets (["^String.concatWith ", " params^"])")
          compute_shared_secrets (params, print, lthy)
        end));

val _ = Outer_Syntax.local_theory' @{command_keyword "setup_protocol_checks"}
        "setup protocol checks"
        (Parse.name -- Scan.repeat Parse.name >>
        (fn params => fn print => fn lthy =>
        let fun setup_protocol_checks ((protocol_model, protocol_names), print, lthy) =
          let
            fun f s = protocol_model ^ "." ^ s
            val a1 = "protocol_check_intro_lemmata"
            val a2 = "coverage_check_unfold_lemmata"
            val a3 = "coverage_check_unfold_protocol_lemma"
            val a4 = "protocol_checks'"
          in
            (declare_protocol_checks print #>
             declare_thm_attr a1 (f "protocol_covered_by_fixpoint_intros") print #>
             declare_def_attr a2 (f "protocol_covered_by_fixpoint") print #>
             fold (fn s => declare_def_attr a3 s print) protocol_names #>
             declare_def_attr a4 (f "wellformed_fixpoint") print #>
             declare_def_attr a4 (f "wellformed_protocol") print #>
             declare_def_attr a4 (f "wellformed_protocol'") print #>
             declare_def_attr a4 (f "wellformed_protocol''") print #>
             declare_def_attr a4 (f "composable_protocols") print) lthy
          end
        in 
          trac_time.ap_lthy lthy
            ("setup_protocol_checks (("^fst params^",["^String.concatWith "," (snd params)^"]))")
            setup_protocol_checks (params, print, lthy)
        end ));
\<close>

end
