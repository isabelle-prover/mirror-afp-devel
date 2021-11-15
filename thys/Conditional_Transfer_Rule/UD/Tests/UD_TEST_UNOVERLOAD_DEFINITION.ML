(* Title: UD/Tests/UD_TEST_UNOVERLOAD_DEFINITION.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

signature UD_TEST_UNOVERLOAD_DEFINITION =
sig
type unoverload_definition_in_type
val test_suite : Proof.context -> unit -> unit
end;

structure ud_test_unoverload_definition : UD_TEST_UNOVERLOAD_DEFINITION =
struct




(**** Background ****)

open SpecCheck;
structure Prop = SpecCheck_Property;
structure Show = SpecCheck_Show;




(**** Auxiliary ****)

fun mk_msg_unoverload_definition_error msg = "ud: " ^ msg



(*** Data ***)

type unoverload_definition_in_type = 
  (binding * mixfix) * (string * typ) * theory;



(*** Relation ***)

fun ud_test_eq_thm thy (act_c, exp_c) (act_ud_out, exp_ud_out) =
  let

    fun rel (act_thm, exp_thm) =
      let
        fun replace_const (Const (c, T)) =
            if c = exp_c then Const (act_c, T) else Const (c, T)
          | replace_const (t $ u) = replace_const t $ replace_const u
          | replace_const (Abs (c, T, t)) = Abs (c, T, replace_const t)
          | replace_const x = x
        val act_t = Thm.full_prop_of act_thm
        val exp_t = exp_thm |> Thm.full_prop_of |> replace_const
      in Pattern.equiv thy (act_t, exp_t) end;

    fun ud_test_eq_thm_impl ((UD.trivial act_thm), (UD.trivial exp_thm)) =
          rel (act_thm, exp_thm)
      | ud_test_eq_thm_impl ((UD.nontrivial act_thms), (UD.nontrivial exp_thms)) = 
          let
            val (act_with_def_thm, act_with_thm) = act_thms 
            val (exp_with_def_thm, exp_with_thm) = exp_thms
          in 
            rel (act_with_def_thm, exp_with_def_thm)
            andalso rel (act_with_thm, exp_with_thm) 
          end
     | ud_test_eq_thm_impl (_, _) = false

  in ud_test_eq_thm_impl (fst act_ud_out, fst exp_ud_out) end;




(**** Visualization ****)

(*FIXME: complete the migration to SpecCheck.Show*)

fun show_unoverload_definition_in 
  (unoverload_definition_in : unoverload_definition_in_type) = 
  let
    val ((b, _), (c, T), thy) = unoverload_definition_in
    val b_c = "binding: " ^ Binding.name_of b
    val const_c = 
      "constant: " ^ 
      c ^ 
      " :: " ^ 
      Syntax.string_of_typ (Proof_Context.init_global thy) T
    val thy_c = "thy: unknown theory" 
    val out_c = [b_c, const_c, thy_c] |> String.concatWith "\n"
  in Pretty.str out_c end;

fun show_unoverload_definition_out (ud_thm_out, thy) = 
  let
    val ctxt = Proof_Context.init_global thy
    val ud_thm_c = 
      let
        val with_thm_c = "with_thm: "
        val with_def_thm_c = "with_def_thm: "
      in
        case ud_thm_out of 
          UD.trivial with_thm => with_thm_c ^ Thm.string_of_thm ctxt with_thm
        | UD.nontrivial (with_def_thm, with_thm) =>
            with_def_thm_c ^ 
            Thm.string_of_thm ctxt with_def_thm ^ 
            "\n" ^
            with_thm_c ^ 
            Thm.string_of_thm ctxt with_thm
      end
    val thy_c = "thy: unknown theory"
    val out_c = [ud_thm_c, thy_c] |> String.concatWith "\n"
  in Pretty.str out_c end;

val show_unoverload_definition = 
  Show.zip show_unoverload_definition_in show_unoverload_definition_out;




(**** Tests ****)



(*** Wrapper ***)

fun unoverload_definition 
  (((b, mixfix), (c, T), thy) : unoverload_definition_in_type) = 
  UD.unoverload_definition (b, mixfix) (c, T) thy;



(*** Valid inputs ***)

fun test_eq_trivial thy _ = 
  let
    
    (*input*)
    val act_c = "UD_Tests.closed'.with"
    val exp_c = ""
    val b = Binding.name "closed'"
    val aT = TVar (("'a", 0), \<^sort>\<open>topological_space\<close>)
    val T = HOLogic.mk_setT aT --> HOLogic.boolT
    val closed_c = "Topological_Spaces.topological_space_class.closed"
    val ud_in = ((b, NoSyn), (closed_c, T), thy)
    
    (*output*)
    val ud_out = (UD.trivial (@{thm closed_with}), thy)
    
  in
    check_list_unit
      show_unoverload_definition
      [(ud_in, ud_out)]
      "trivial equality"
      (
        Prop.prop 
          (
            fn (ud_in, ud_out) => ud_test_eq_thm 
              thy (act_c, exp_c) (unoverload_definition ud_in, ud_out)
          )
       )
  end;

fun test_eq_nontrivial thy _ = 
  let
    
    (*input*)
    val act_c = "UD_Tests.closure.with"
    val exp_c = "UD_Tests.closure_with"
    val b = Binding.name "closure"
    val aT = TVar (("'a", 0), \<^sort>\<open>topological_space\<close>)
    val T = (HOLogic.mk_setT aT --> HOLogic.mk_setT aT)
    val closure_c = "UD_Tests.closure"
    val ud_in = ((b, NoSyn), (closure_c, T), thy)
    
    (*output*)
    val ud_out = 
      (UD.nontrivial (@{thm closure_with_def}, @{thm closure_with}), thy)
    
  in
    check_list_unit
      show_unoverload_definition
      [(ud_in, ud_out)]
      "nontrivial equality"
      (
        Prop.prop 
          (
            fn (ud_in, ud_out) => ud_test_eq_thm 
              thy (act_c, exp_c) (unoverload_definition ud_in, ud_out)
          )
       )
  end;



(*** Exceptions ***)

fun test_exc_extra_type_variables thy _ = 
  let
    val aT = TVar (("'a", 0), \<^sort>\<open>type\<close>)
    val Sup_class_c = "Complete_Lattices.Sup_class"
    val args : unoverload_definition_in_type =
      (
        (Binding.empty, NoSyn), 
        (Sup_class_c, Term.itselfT aT --> \<^typ>\<open>prop\<close>), 
        thy
      )
    val err_msg = mk_msg_unoverload_definition_error 
      "specification depends on extra type variables"
    val exn_prop = Prop.expect_failure (ERROR err_msg) unoverload_definition
  in
    check_list_unit
      show_unoverload_definition_in 
      [args] 
      "extra type variables"
      exn_prop 
  end;

fun test_exc_ud_ex thy _ = 
  let
    val aT = TVar (("'a", 0), \<^sort>\<open>type\<close>)
    val T = 
      (HOLogic.mk_setT aT --> HOLogic.boolT) --> 
      HOLogic.mk_setT aT --> 
      HOLogic.boolT
    val ts_c = "Topological_Spaces.topological_space.closed"
    val args : unoverload_definition_in_type =
      ((Binding.empty, NoSyn), (ts_c, T), thy)
    val err_msg = mk_msg_unoverload_definition_error 
      "unoverloaded constant already exists"
    val exn_prop = Prop.expect_failure (ERROR err_msg) unoverload_definition
  in 
    check_list_unit
      show_unoverload_definition_in 
      [args] 
      "constant already exists"
      exn_prop 
  end;

fun test_exc_no_cids thy _ = 
  let
    val aT = TVar (("'a", 0), \<^sort>\<open>type\<close>)
    val T = 
      (HOLogic.mk_setT aT --> HOLogic.boolT) --> 
      HOLogic.mk_setT aT --> 
      HOLogic.boolT
    val implies_c = "HOL.implies"
    val args : unoverload_definition_in_type =
      ((Binding.empty, NoSyn), (implies_c, T), thy)
    val err_msg = mk_msg_unoverload_definition_error
      "no suitable constant-instance definitions"
    val exn_prop = Prop.expect_failure (ERROR err_msg) unoverload_definition
  in 
    check_list_unit 
      show_unoverload_definition_in 
      [args] 
      "no suitable CIs"
      exn_prop
  end;




(**** Test Suite ****)

fun test_suite ctxt s = 
  let val thy = Proof_Context.theory_of ctxt
  in
    [
      test_eq_trivial,
      test_eq_nontrivial,
      test_exc_extra_type_variables,
      test_exc_ud_ex,
      test_exc_no_cids
    ]
    |> map (fn f => f thy s)
    |> Lecker.test_group ctxt s  
  end;

end;