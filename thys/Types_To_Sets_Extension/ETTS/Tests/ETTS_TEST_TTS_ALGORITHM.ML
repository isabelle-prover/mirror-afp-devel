(* Title: ETTS/Tests/ETTS_TEST_TTS_ALGORITHM.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

signature ETTS_TEST_TTS_ALGORITHM =
sig
type tts_algorithm_in_type
val test_suite : Proof.context -> unit -> unit
end;

structure etts_test_tts_algorithm : ETTS_TEST_TTS_ALGORITHM =
struct




(**** Background ****)

open SpecCheck;
structure Prop = SpecCheck_Property;
structure Show = SpecCheck_Show;




(**** Auxiliary ****)

fun mk_msg_tts_algorithm_error msg = "tts_algorithm: " ^ msg



(*** Data ***)

type tts_algorithm_in_type = 
  Proof.context *
  ETTS_Algorithm.etts_output_type *
  int list *
  (indexname * term) list *
  (term * term) list *
  (Facts.ref * Token.src list) option *
  (Facts.ref * Token.src list) list *
  (term list * (Proof.context -> tactic)) option * 
  Token.src list *
  thm;



(*** String I/O ***)

fun string_of_writer writer = writer 
  |> ML_Syntax.print_list Int.toString 
  |> curry op^ "writer: "



(*** Relation for the outputs ***)

fun rel_tts_algorithm_out
  (
    act_out : (thm * int list) * Proof.context, 
    exp_out : (thm * int list) * Proof.context
  ) =
  let
    val ((thm_act_out, writer_act_out), _) = act_out
    val ((thm_exp_out, writer_exp_out), _) = exp_out
    val t_act_out = Thm.full_prop_of thm_act_out 
    val t_exp_out = Thm.full_prop_of thm_exp_out
  in 
    t_act_out aconv t_exp_out 
    andalso writer_act_out = writer_exp_out
  end;




(**** Visualization ****)

(*FIXME: complete the migration to SpecCheck.Show*)

fun string_of_rispec ctxt = 
  ML_Syntax.print_pair (Term.string_of_vname) (Syntax.string_of_term ctxt)
  |> ML_Syntax.print_list;

fun string_of_sbtspec ctxt =
  let val string_of_term = Syntax.string_of_term ctxt
  in 
    ML_Syntax.print_pair string_of_term string_of_term 
    |> ML_Syntax.print_list
  end;

fun show_tts_algorithm_in (tts_algorithm_in : tts_algorithm_in_type) = 
  let
    val 
      (
        ctxt,
        tts_output_type, 
        writer, 
        rispec,
        sbtspec, 
        sbrr_opt, 
        subst_thms, 
        mpespc_opt,
        attrbs,
        thm
      ) = tts_algorithm_in
    val ctxt_c = "ctxt: unknown context" 
    val tts_output_type_c =
      ETTS_Algorithm.string_of_etts_output_type tts_output_type
    val writer_c = string_of_writer writer 
    val rispec_c = rispec |> string_of_rispec ctxt |> curry op^ "rispec: "
    val sbtspec_c = sbtspec |> string_of_sbtspec ctxt |> curry op^ "sbtspec: "
    val sbrr_opt_c = sbrr_opt 
      |> ETTS_Context.string_of_sbrr_opt 
      |> curry op^ "sbrr_opt: "
    val subst_thms_c = subst_thms
      |> ETTS_Context.string_of_subst_thms
      |> curry op^ "subst_thms: "
    val mpespc_opt_c = mpespc_opt
      |> ETTS_Context.string_of_mpespc_opt ctxt
      |> curry op^ "mpespc_opt: "
    val attrbs_c = attrbs |> string_of_token_src_list |> curry op^ "attrbs: "
    val thm_c = thm |> Thm.string_of_thm ctxt |> curry op^ "in_thm: "
    val out_c = 
      [
        ctxt_c,
        tts_output_type_c,
        writer_c,
        rispec_c,
        sbtspec_c,
        sbrr_opt_c,
        subst_thms_c,
        mpespc_opt_c,
        attrbs_c,
        thm_c
      ]
      |> String.concatWith "\n"
  in Pretty.str out_c end;

fun show_tts_algorithm_out
  (((thm, writer), ctxt) : (thm * int list) * Proof.context) = 
  let
    val ctxt_c = "ctxt: unknown context" 
    val thm_c = Thm.string_of_thm ctxt thm
    val writer_c = ML_Syntax.print_list Int.toString writer
    val out_c = [ctxt_c, thm_c, writer_c] |> String.concatWith "\n"
  in Pretty.str out_c end;

val show_tts_algorithm = Show.zip show_tts_algorithm_in show_tts_algorithm_out




(**** Tests ****)



(*** Wrapper ***)

fun tts_algorithm (tts_algorithm_in : tts_algorithm_in_type) =
  let
    val 
      (
        ctxt,
        tts_output_type, 
        writer, 
        rispec,
        sbtspec, 
        sbrr_opt, 
        subst_thms, 
        mpespc_opt,
        attrbs,
        thm
      ) = tts_algorithm_in
    val tts_algorithm_out = 
      ETTS_Algorithm.etts_algorithm
        ctxt 
        tts_output_type 
        writer
        rispec 
        sbtspec 
        sbrr_opt 
        subst_thms 
        mpespc_opt 
        attrbs
        thm
  in tts_algorithm_out end;



(*** Valid inputs ***)

fun test_eq_tts_algorithm (ctxt : Proof.context) _ = 
  let

    (*input*)
    val tts_ctxt_data = ETTS_Context.get_tts_ctxt_data ctxt
    val rispec = #rispec tts_ctxt_data
    val sbtspec = #sbtspec tts_ctxt_data
    val sbrr_opt = #sbrr_opt tts_ctxt_data
    val subst_thms = #subst_thms tts_ctxt_data
    val mpespc_opt = #mpespc_opt tts_ctxt_data
    val attrbs = #attrbs tts_ctxt_data
    val tts_output_type = ETTS_Algorithm.default
    val writer_in = [1, 1, 1, 1]
    val in_thm = @{thm tta_semigroup_hom.tta_left_ideal_closed}
    val tts_algorithm_in : tts_algorithm_in_type = 
      (
        ctxt,
        tts_output_type, 
        writer_in, 
        rispec,
        sbtspec,
        sbrr_opt, 
        subst_thms, 
        mpespc_opt,
        attrbs,
        in_thm
      )

    (*output*)
    val writer_out = [1, 3, 1, 1]
    val exp_tts_algorithm_out = 
      ((@{thm tta_left_ideal_ow_closed}, writer_out), ctxt)

  in
    check_list_unit
      show_tts_algorithm
      [(tts_algorithm_in, exp_tts_algorithm_out)]
      "equality"
      (
        Prop.prop 
          (
            fn (val_in, val_out) => 
              rel_tts_algorithm_out (tts_algorithm val_in, val_out)
          )
       )
  end;



(*** Exceptions ***)

fun test_exc_ftvs ctxt _ = 
  let
    val tts_ctxt_data = ETTS_Context.get_tts_ctxt_data ctxt
    val rispec = #rispec tts_ctxt_data
    val sbtspec = #sbtspec tts_ctxt_data
    val sbrr_opt = #sbrr_opt tts_ctxt_data
    val subst_thms = #subst_thms tts_ctxt_data
    val mpespc_opt = #mpespc_opt tts_ctxt_data
    val attrbs = #attrbs tts_ctxt_data
    val tts_output_type = ETTS_Algorithm.default
    val writer_in = [1, 1, 1, 1]
    val in_thm = @{thm exI'[where 'a='a]}
    val tts_algorithm_in : tts_algorithm_in_type = 
      (
        ctxt,
        tts_output_type, 
        writer_in, 
        rispec,
        sbtspec, 
        sbrr_opt, 
        subst_thms, 
        mpespc_opt,
        attrbs,
        in_thm
      )
    val err_msg = mk_msg_tts_algorithm_error
      "fixed type variables must not occur in the type-based theorems"
    val exn_prop = Prop.expect_failure (ERROR err_msg) tts_algorithm
  in
    check_list_unit
      show_tts_algorithm_in
      [tts_algorithm_in]
      "fixed type variables"
      exn_prop 
  end;

fun test_exc_fvs ctxt _ = 
  let
    val tts_ctxt_data = ETTS_Context.get_tts_ctxt_data ctxt
    val rispec = #rispec tts_ctxt_data
    val sbtspec = #sbtspec tts_ctxt_data
    val sbrr_opt = #sbrr_opt tts_ctxt_data
    val subst_thms = #subst_thms tts_ctxt_data
    val mpespc_opt = #mpespc_opt tts_ctxt_data
    val attrbs = #attrbs tts_ctxt_data
    val tts_output_type = ETTS_Algorithm.default
    val writer_in = [1, 1, 1, 1]
    val aT = TVar (("'a", 0), \<^sort>\<open>type\<close>)
    val xv = ("x", 0)
    val xt = Free ("x", aT) |> Thm.cterm_of ctxt
    val in_thm = Drule.instantiate_normalize 
      (TVars.empty, Vars.make [((xv, aT), xt)]) @{thm exI'}
    val tts_algorithm_in : tts_algorithm_in_type = 
      (
        ctxt,
        tts_output_type,
        writer_in,
        rispec,
        sbtspec,
        sbrr_opt,
        subst_thms,
        mpespc_opt,
        attrbs,
        in_thm
      )
    val err_msg = mk_msg_tts_algorithm_error
      "fixed variables must not occur in the type-based theorems"
    val exn_prop = Prop.expect_failure (ERROR err_msg) tts_algorithm
  in
    check_list_unit
      show_tts_algorithm_in
      [tts_algorithm_in]
      "fixed variables"
      exn_prop 
  end;

fun test_exc_not_risstv_subset ctxt _ = 
  let
    val tts_ctxt_data = ETTS_Context.get_tts_ctxt_data ctxt
    val rispec = #rispec tts_ctxt_data
    val sbtspec = #sbtspec tts_ctxt_data
    val sbrr_opt = #sbrr_opt tts_ctxt_data
    val subst_thms = #subst_thms tts_ctxt_data
    val mpespc_opt = #mpespc_opt tts_ctxt_data
    val attrbs = #attrbs tts_ctxt_data
    val tts_output_type = ETTS_Algorithm.default
    val writer_in = [1, 1, 1, 1]
    val in_thm = @{thm tta_semigroup.tta_assoc}
    val tts_algorithm_in : tts_algorithm_in_type = 
      (
        ctxt,
        tts_output_type,
        writer_in,
        rispec,
        sbtspec,
        sbrr_opt,
        subst_thms,
        mpespc_opt,
        attrbs,
        in_thm
      )
    val err_msg = mk_msg_tts_algorithm_error
      "risstv must be a subset of the schematic type " ^
      "variables that occur in the type-based theorems"
    val exn_prop = Prop.expect_failure (ERROR err_msg) tts_algorithm
  in
    check_list_unit
      show_tts_algorithm_in
      [tts_algorithm_in]
      "risstv is not a subset of the stvs of the type-based theorems"
      exn_prop 
  end;

fun test_not_tts_context thy _ = 
  let
    val ctxt = Proof_Context.init_global thy                    
    val tts_ctxt_data = ETTS_Context.get_tts_ctxt_data ctxt
    val rispec = #rispec tts_ctxt_data
    val sbtspec = #sbtspec tts_ctxt_data
    val sbrr_opt = #sbrr_opt tts_ctxt_data
    val subst_thms = #subst_thms tts_ctxt_data
    val mpespc_opt = #mpespc_opt tts_ctxt_data
    val attrbs = #attrbs tts_ctxt_data
    val tts_output_type = ETTS_Algorithm.default
    val writer_in = [1, 1, 1, 1]
    val in_thm = @{thm tta_semigroup_hom.tta_left_ideal_closed}
    val tts_algorithm_in : tts_algorithm_in_type = 
      (
        ctxt,
        tts_output_type, 
        writer_in, 
        rispec,
        sbtspec, 
        sbrr_opt, 
        subst_thms, 
        mpespc_opt,
        attrbs,
        in_thm
      )
    val err_msg = mk_msg_tts_algorithm_error
      "ERA can only be invoked from an appropriately parameterized tts context"
    val exn_prop = Prop.expect_failure (ERROR err_msg) tts_algorithm
  in
    check_list_unit
      show_tts_algorithm_in 
      [tts_algorithm_in] 
      "not tts context"
      exn_prop 
  end;




(**** Test Suite ****)

fun test_suite ctxt s = 
  let val thy = Proof_Context.theory_of ctxt
  in
    [
      test_eq_tts_algorithm ctxt s,
      test_exc_ftvs ctxt s,
      test_exc_fvs ctxt s,
      test_exc_not_risstv_subset ctxt s,
      test_not_tts_context thy s
    ]
    |> Lecker.test_group ctxt s
  end;

end;