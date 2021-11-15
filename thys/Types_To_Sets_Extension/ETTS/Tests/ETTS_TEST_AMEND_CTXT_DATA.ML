(* Title: ETTS/Tests/ETTS_TEST_AMEND_CTXT_DATA.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

signature ETTS_TEST_AMEND_CTXT_DATA =
sig
val test_suite : Proof.context -> unit -> unit
end;

structure etts_test_amend_ctxt_data : ETTS_TEST_AMEND_CTXT_DATA =
struct




(**** Background ****)

open SpecCheck;
structure Prop = SpecCheck_Property;
structure Show = SpecCheck_Show;




(**** Auxiliary ****)

fun mk_msg_tts_ctxt_error msg = "tts_context: " ^ msg

(* 
approximate comparison of Token.src values: should not be made public
and should be used with great care 
*)
local

val eq_eps_src_msg = "eq_eps_src: comparison is not possible"

in

fun eq_eps_src (src, src') = 
  let
    val eq_name = Token.name_of_src src = Token.name_of_src src'
    val eq_args = Token.args_of_src src ~~ Token.args_of_src src'
      |> map eq_eps_token
      |> List.all I
  in eq_name andalso eq_args end
and eq_eps_token (token : Token.T, token' : Token.T) =
  let
    val eq_kind = Token.kind_of token = Token.kind_of token'
    val eq_content = Token.content_of token = Token.content_of token'
    val eq_source = Token.source_of token = Token.source_of token'
    val eq_range =
      Input.range_of (Token.input_of token) = 
      Input.range_of (Token.input_of token')
    val eq_slot = (Token.get_value token, Token.get_value token')
      |> eq_option eq_eps_value
  in 
    eq_kind
    andalso eq_content 
    andalso eq_source 
    andalso eq_range
    andalso eq_slot
  end
and eq_eps_value (Token.Source src, Token.Source src') = eq_eps_src (src, src')
  | eq_eps_value (Token.Literal ltrl, Token.Literal ltrl') = ltrl = ltrl'
  | eq_eps_value (Token.Name _, Token.Name _) = error eq_eps_src_msg 
  | eq_eps_value (Token.Typ T, Token.Typ T') = T = T'
  | eq_eps_value (Token.Term t, Token.Term t') = t = t'
  | eq_eps_value (Token.Fact (c_opt, thms), Token.Fact (c_opt', thms')) = 
      let
        val eq_c = c_opt = c_opt' 
        val eq_thms = eq_list Thm.eq_thm (thms, thms')
      in eq_c andalso eq_thms end
  | eq_eps_value (Token.Attribute _, Token.Attribute _) = 
      error eq_eps_src_msg
  | eq_eps_value (Token.Declaration _, Token.Declaration _) = 
      error eq_eps_src_msg
  | eq_eps_value (Token.Files _, Token.Files _) = 
      error eq_eps_src_msg;

end;

(* 
approximate comparison of ctxt_def_type: should not be made public
and used with great care 
*)
fun eq_tts_ctxt_data
  (
    ctxt_data : ETTS_Context.ctxt_def_type, 
    ctxt_data' : ETTS_Context.ctxt_def_type
  ) = 
  let
    fun eq_subst_thm (rsrc, rsrc') = fst rsrc = fst rsrc' 
      andalso eq_list eq_eps_src (snd rsrc, snd rsrc') 
    val _ = (#mpespc_opt ctxt_data, #mpespc_opt ctxt_data')
      |> apply2 is_none
      |> (fn (x, y) => x = true andalso y = true)
      orelse error "eq_tts_ctxt_data: comparison is not possible"
    val eq_rispec = #rispec ctxt_data = #rispec ctxt_data'
    val eq_sbtspec = #sbtspec ctxt_data = #sbtspec ctxt_data'
    val eq_subst_thms = 
      eq_list eq_subst_thm (#subst_thms ctxt_data, #subst_thms ctxt_data')
    val eq_sbrr_opt = (#sbrr_opt ctxt_data, #sbrr_opt ctxt_data')
      |> eq_option eq_subst_thm
    val eq_attrbs = eq_list eq_eps_src (#attrbs ctxt_data, #attrbs ctxt_data')
  in 
    eq_rispec 
    andalso eq_sbtspec
    andalso eq_subst_thms
    andalso eq_sbrr_opt
    andalso eq_attrbs
  end;




(**** Visualization ****)

(*FIXME: complete the migration to SpecCheck.Show*)

fun show_amend_context_in (args, ctxt) = 
  let 
    val c =
      "ctxt : unknown context\n" ^ 
      ETTS_Context.string_of_amend_context_data_args ctxt args
  in Pretty.str c end;

fun show_amend_context_out (ctxt_data, ctxt) = 
  Pretty.str (ETTS_Context.string_of_tts_ctxt_data ctxt ctxt_data)

val show_amend_context = Show.zip show_amend_context_in show_amend_context_out




(**** Tests ****)



(*** Wrapper ***)

val test_amend_context_data = uncurry ETTS_Context.amend_context_data;



(*** Valid inputs ***)

fun test_eq_tts_context (ctxt : Proof.context) _ = 
  let
    
    (*input*)
    val risstv1_c = "?'a"
    val U1_c = "UA::'ao set"
    val risstv2_c = "?'b"
    val U2_c = "UB::'bo set"
    val rispec = [(risstv1_c, U1_c), (risstv2_c, U2_c)]
    val tbt_1 = "(\<le>)::?'a::ord\<Rightarrow>?'a::ord\<Rightarrow>bool"
    val sbt_1 = "(\<le>\<^sub>o\<^sub>w)"
    val tbt_2 = "(<)::?'b::ord\<Rightarrow>?'b::ord\<Rightarrow>bool"
    val sbt_2 = "(<\<^sub>o\<^sub>w)"
    val sbtspec = [(tbt_1, sbt_1), (tbt_2, sbt_2)]
    val args : ETTS_Context.amend_ctxt_data_input_type = 
      (((((rispec, sbtspec), NONE), []), NONE), [])
    
    (*output*)
    val s_a_ix : indexname = ("'a", 0)
    val s_a_T = TVar (s_a_ix, \<^sort>\<open>ord\<close>)
    val aT = TFree ("'ao", \<^sort>\<open>type\<close>)
    val U1 = Free ("UA", HOLogic.mk_setT aT)
    val s_b_ix : indexname = ("'b", 0)
    val s_b_T = TVar (s_b_ix, \<^sort>\<open>ord\<close>)
    val bT = TFree ("'bo", \<^sort>\<open>type\<close>)
    val U2 = Free ("UB", HOLogic.mk_setT bT)
    
    val less_eqt = 
      Const (\<^const_name>\<open>less_eq\<close>, s_a_T --> s_a_T --> HOLogic.boolT)
    val lesst = 
      Const (\<^const_name>\<open>less\<close>, s_b_T --> s_b_T --> HOLogic.boolT)
    val leqt = Free ("le", aT --> aT --> HOLogic.boolT)
    val lst = Free ("ls", bT --> bT --> HOLogic.boolT)
 
    val rispec = [(s_a_ix, U1), (s_b_ix, U2)]
    val sbtspec = [(less_eqt, leqt), (lesst, lst)]
    val subst_thms = []
    val sbrr_opt = NONE
    val mpespc_opt = NONE
    val attrbs = []

    val tts_ctxt_data_out : ETTS_Context.ctxt_def_type = 
      {
        rispec = rispec,
        sbtspec = sbtspec,
        subst_thms = subst_thms,
        sbrr_opt = sbrr_opt,
        mpespc_opt = mpespc_opt,
        attrbs = attrbs
      }

  in
    check_list_unit 
      show_amend_context
      [((args, ctxt), (tts_ctxt_data_out, ctxt))]
      "equality"
      (
        Prop.prop 
          (
            fn (val_in, val_out) => 
              eq_fst eq_tts_ctxt_data (test_amend_context_data val_in, val_out)
          )
       )
  end;



(*** Exceptions ***)


(** General **)

fun test_exc_tts_context_tts_context thy _ = 
  let

    val ctxt = Proof_Context.init_global thy;

    val risstv1_c = "?'a"
    val U1_c = "U1::'a set"
    val rispec1 = [(risstv1_c, U1_c)]
    val args1 : ETTS_Context.amend_ctxt_data_input_type = 
      (((((rispec1, []), NONE), []), NONE), [])
    val ctxt' = ETTS_Context.amend_context_data args1 ctxt |> snd

    val risstv2_c = "?'b"
    val U2_c = "U2::'b set"
    val rispec2 = [(risstv2_c, U2_c)]
    val args2 : ETTS_Context.amend_ctxt_data_input_type = 
      (((((rispec2, []), NONE), []), NONE), [])

    val err_msg = mk_msg_tts_ctxt_error "nested tts contexts"

    val exn_prop = Prop.expect_failure (ERROR err_msg) test_amend_context_data

  in
    check_list_unit
      (show_amend_context_in) 
      [(args2, ctxt')]
      "nested tts contexts"
      exn_prop 
  end;


(** tts **)

fun test_exc_rispec_empty thy _ = 
  let 
    val ctxt = Proof_Context.init_global thy;
    val args = ((((([], []), NONE), []), NONE), [])
    val err_msg = mk_msg_tts_ctxt_error "rispec must not be empty"
    val exn_prop = Prop.expect_failure (ERROR err_msg) test_amend_context_data
  in 
    check_list_unit
      (show_amend_context_in) 
      [(args, ctxt)]
      "rispec empty"
      exn_prop 
  end;

fun test_exc_rispec_not_set thy _ = 
  let 
    val ctxt = Proof_Context.init_global thy;
    val risstv1_c = "?'a"
    val U1_c = "U1::('b list) set"
    val risstv2_c = "?'b"
    val U2_c = "U2::'a set"
    val rispec = [(risstv1_c, U1_c), (risstv2_c, U2_c)]
    val args = (((((rispec, []), NONE), []), NONE), [])
    val err_msg = mk_msg_tts_ctxt_error 
      "risset must be terms of the type of the form ?'a set or 'a set"
    val exn_prop = Prop.expect_failure (ERROR err_msg) test_amend_context_data
  in 
    check_list_unit
      (show_amend_context_in) 
      [(args, ctxt)]
      "risset are not all sets"
      exn_prop 
  end;

fun test_exc_rispec_duplicate_risstvs thy _ = 
  let 
    val ctxt = Proof_Context.init_global thy;
    val risstv1_c = "?'a"
    val U1_c = "U1::'a set"
    val risstv2_c = "?'b"
    val U2_c = "U2::'b set"
    val risstv3_c = "?'a"
    val U3_c = "U3::'c set"
    val rispec = [(risstv1_c, U1_c), (risstv2_c, U2_c), (risstv3_c, U3_c)]
    val args = (((((rispec, []), NONE), []), NONE), [])
    val err_msg = "tts_context: risstvs must be distinct"
    val exn_prop = Prop.expect_failure (ERROR err_msg) test_amend_context_data
  in
    check_list_unit
      (show_amend_context_in) 
      [(args, ctxt)]
      "duplicate risstvs"
      exn_prop 
  end;

fun test_exc_rispec_not_ds_dtv thy _ = 
  let 
    val ctxt = Proof_Context.init_global thy;
    val risstv1_c = "?'a"
    val U1_c = "U1::'a set"
    val risstv2_c = "?'b"
    val U2_c = "U2::'b::{group_add, finite} set"
    val risstv3_c = "?'c"
    val U3_c = "U3::'c::{group_add, order} set"
    val risstv4_c = "?'d"
    val U4_c = "U4::'b::{group_add, order} set"
    val rispec = 
      [(risstv1_c, U1_c), (risstv2_c, U2_c), (risstv3_c, U3_c), (risstv4_c, U4_c)]
    val args = (((((rispec, []), NONE), []), NONE), [])
    val err_msg = 
      "tts_context: risset: type variables with distinct sorts must be distinct"
    val exn_prop = Prop.expect_failure (ERROR err_msg) test_amend_context_data
  in
    check_list_unit
      (show_amend_context_in) 
      [(args, ctxt)]
      "not distinct sorts \<longrightarrow> distinct types variables"
      exn_prop 
  end;

fun test_exc_rispec_not_dt_dv thy _ = 
  let 
    val ctxt = Proof_Context.init_global thy;
    val risstv1_c = "?'a"
    val U1_c = "U1::'a set"
    val risstv2_c = "?'b"
    val U2_c = "U2::'b::{group_add, finite} set"
    val risstv3_c = "?'c"
    val U3_c = "U3::'c::{group_add, order} set"
    val risstv4_c = "?'d"
    val U4_c = "U2::'c::{group_add, order} set"
    val rispec = 
      [
        (risstv1_c, U1_c), 
        (risstv2_c, U2_c), 
        (risstv3_c, U3_c), 
        (risstv4_c, U4_c)
      ]
    val args = (((((rispec, []), NONE), []), NONE), [])
    val err_msg = 
      "tts_context: risset: variables with distinct types must be distinct"
    val exn_prop = Prop.expect_failure (ERROR err_msg) test_amend_context_data
  in
    check_list_unit
      (show_amend_context_in) 
      [(args, ctxt)]
      "not distinct types \<longrightarrow> distinct variables"
      exn_prop 
  end;


(** sbterms **)

fun test_exc_distinct_sorts ctxt _ = 
  let 
    val risstv1_c = "?'a"
    val U1_c = "UA::'ao set"
    val risstv2_c = "?'b"
    val U2_c = "UB::'bo set"
    val rispec = [(risstv1_c, U1_c), (risstv2_c, U2_c)]
    val tbt_1 = "(<)::?'a::ord\<Rightarrow>?'a::ord\<Rightarrow>bool"
    val sbt_1 = "(<\<^sub>o\<^sub>w)"
    val tbt_2 = "?a::?'a::order\<Rightarrow>?'a::order\<Rightarrow>bool"
    val sbt_2 = "f"
    val sbtspec = [(tbt_1, sbt_1), (tbt_2, sbt_2)]
    val args = (((((rispec, sbtspec), NONE), []), NONE), [])
    val err_msg = mk_msg_tts_ctxt_error 
      "tbts: a single stv should not have two distinct sorts associated with it"
    val exn_prop = Prop.expect_failure (ERROR err_msg) test_amend_context_data
  in
    check_list_unit
      (show_amend_context_in) 
      [(args, ctxt)]
      "tbts: an stv with distinct sorts"
      exn_prop 
  end;

fun test_exc_sbts_no_tis ctxt _ = 
  let 
    val risstv1_c = "?'a"
    val U1_c = "UA::'ao set"
    val risstv2_c = "?'b"
    val U2_c = "UB::'bo set"
    val rispec = [(risstv1_c, U1_c), (risstv2_c, U2_c)]
    val tbt_1 = "(<)::?'a::ord\<Rightarrow>?'a::ord\<Rightarrow>bool"
    val sbt_1 = "(<\<^sub>o\<^sub>w)"
    val tbt_2 = "(\<le>)::?'a::ord\<Rightarrow>?'a::ord\<Rightarrow>bool"
    val sbt_2 = "(\<le>\<^sub>o\<^sub>w)"
    val sbtspec = [(tbt_1, sbt_1), (tbt_2, sbt_2)]
    val args = (((((rispec, sbtspec), NONE), []), NONE), [])
    val err_msg = mk_msg_tts_ctxt_error 
      "\n\t-the types of the sbts must be equivalent " ^ 
      "to the types of the tbts up to renaming of the type variables\n" ^
      "\t-to each type variable that occurs among the tbts must correspond " ^ 
      "exactly one type variable among all type " ^
      "variables that occur among all of the sbts"
    val exn_prop = Prop.expect_failure (ERROR err_msg) test_amend_context_data
  in 
    check_list_unit
      (show_amend_context_in) 
      [(args, ctxt)]
      "sbts are not type instances of tbts"
      exn_prop 
  end;

fun test_exc_tbt_fixed ctxt _ = 
  let 
    val risstv1_c = "?'a"
    val U1_c = "UA::'ao set"
    val risstv2_c = "?'b"
    val U2_c = "UB::'bo set"
    val rispec = [(risstv1_c, U1_c), (risstv2_c, U2_c)]
    val tbt_1 = "(<)::?'a::ord\<Rightarrow>?'a::ord\<Rightarrow>bool"
    val sbt_1 = "(<\<^sub>o\<^sub>w)"
    val tbt_2 = "g::?'a::ord\<Rightarrow>?'a::ord\<Rightarrow>bool"
    val sbt_2 = "(<\<^sub>o\<^sub>w)"
    val sbtspec = [(tbt_1, sbt_1), (tbt_2, sbt_2)]
    val args = (((((rispec, sbtspec), NONE), []), NONE), [])
    val err_msg = mk_msg_tts_ctxt_error 
      "tbts must consist of constants and schematic variables"
    val exn_prop = Prop.expect_failure (ERROR err_msg) test_amend_context_data
  in 
    check_list_unit
      (show_amend_context_in) 
      [(args, ctxt)]
      "tbts are not constants and schematic variables"
      exn_prop 
  end;

fun test_exc_sbts_not_registered ctxt _ = 
  let 
    val risstv1_c = "?'a"
    val U1_c = "UA::'ao set"
    val risstv2_c = "?'b"
    val U2_c = "UB::'bo set"
    val rispec = [(risstv1_c, U1_c), (risstv2_c, U2_c)]
    val tbt_1 = "(<)::?'a::ord\<Rightarrow>?'a::ord\<Rightarrow>bool"
    val sbt_1 = "(<\<^sub>o\<^sub>w)"
    val tbt_2 = "(\<le>)::?'a::ord\<Rightarrow>?'a::ord\<Rightarrow>bool"
    val sbt_2 = "g::'bo::type\<Rightarrow>'bo::type\<Rightarrow>bool"
    val sbtspec = [(tbt_1, sbt_1), (tbt_2, sbt_2)]
    val args = (((((rispec, sbtspec), NONE), []), NONE), [])
    val err_msg = mk_msg_tts_ctxt_error
      "sbts must be registered using the command tts_register_sbts"
    val exn_prop = Prop.expect_failure (ERROR err_msg) test_amend_context_data
  in
    check_list_unit
      (show_amend_context_in) 
      [(args, ctxt)]
      "sbts must be registered"
      exn_prop 
  end;

fun test_exc_tbts_not_distinct ctxt _ = 
  let 
    val risstv1_c = "?'a"
    val U1_c = "UA::'ao set"
    val risstv2_c = "?'b"
    val U2_c = "UB::'bo set"
    val rispec = [(risstv1_c, U1_c), (risstv2_c, U2_c)]
    val tbt_1 = "(\<le>)::?'a::ord\<Rightarrow>?'a::ord\<Rightarrow>bool"
    val sbt_1 = "(<\<^sub>o\<^sub>w)"
    val tbt_2 = "(\<le>)::?'a::ord\<Rightarrow>?'a::ord\<Rightarrow>bool"
    val sbt_2 = "(<\<^sub>o\<^sub>w)"
    val sbtspec = [(tbt_1, sbt_1), (tbt_2, sbt_2)]
    val args = (((((rispec, sbtspec), NONE), []), NONE), [])
    val err_msg = mk_msg_tts_ctxt_error "tbts must be distinct"
    val exn_prop = Prop.expect_failure (ERROR err_msg) test_amend_context_data
  in
    check_list_unit
      (show_amend_context_in) 
      [(args, ctxt)]
      "tbts must be distinct" 
      exn_prop 
  end;

fun test_exc_sbterms_subset_rispec (ctxt : Proof.context) _ = 
  let
    (* input *)
    val risstv1_c = "?'a"
    val U1_c = "UA::'ao set"
    val rispec = [(risstv1_c, U1_c)]
    val tbt_1 = "(\<le>)::?'a::ord\<Rightarrow>?'a::ord\<Rightarrow>bool"
    val sbt_1 = "(\<le>\<^sub>o\<^sub>w)"
    val tbt_2 = "(<)::?'b::ord\<Rightarrow>?'b::ord\<Rightarrow>bool"
    val sbt_2 = "(<\<^sub>o\<^sub>w)"
    val sbtspec = [(tbt_1, sbt_1), (tbt_2, sbt_2)]
    val args : ETTS_Context.amend_ctxt_data_input_type = 
      (((((rispec, sbtspec), NONE), []), NONE), [])
    val err_msg = mk_msg_tts_ctxt_error 
      "the collection of the (stv, ftv) pairs associated with the sbterms " ^
      "must form a subset of the collection of the (stv, ftv) pairs " ^
      "associated with the RI specification, provided that only the pairs " ^
      "(stv, ftv) associated with the sbterms such that ftv occurs in a " ^
      "premise of a theorem associated with an sbterm are taken into account"
    val exn_prop = Prop.expect_failure (ERROR err_msg) test_amend_context_data
  in
    check_list_unit
      (show_amend_context_in) 
      [(args, ctxt)]
      "stv-ftv subset"
      exn_prop 
  end;




(**** Test Suite ****)

fun test_suite ctxt s = 
  let val thy = Proof_Context.theory_of ctxt
  in
    [
      test_eq_tts_context ctxt s,
      test_exc_tts_context_tts_context thy s,
      test_exc_rispec_empty thy s,
      test_exc_rispec_not_set thy s,
      test_exc_rispec_duplicate_risstvs thy s,
      test_exc_rispec_not_ds_dtv thy s,
      test_exc_rispec_not_dt_dv thy s,
      test_exc_distinct_sorts ctxt s,
      test_exc_sbts_no_tis ctxt s,
      test_exc_tbt_fixed ctxt s,
      test_exc_sbts_not_registered ctxt s,
      test_exc_tbts_not_distinct ctxt s,
      test_exc_sbterms_subset_rispec ctxt s
    ]
    |> Lecker.test_group ctxt s
  end;

end;