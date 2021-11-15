(* Title: ETTS/Tests/ETTS_TEST_TTS_REGISTER_SBTS.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

signature ETTS_TEST_TTS_REGISTER_SBTS =
sig
type tts_register_sbts_in_type
val test_suite : Proof.context -> unit -> unit
end;

structure etts_test_tts_register_sbts : ETTS_TEST_TTS_REGISTER_SBTS =
struct




(**** Background ****)

open SpecCheck;
structure Prop = SpecCheck_Property;
structure Show = SpecCheck_Show;




(**** Auxiliary ****)

fun mk_msg_tts_register_sbts_error msg = "tts_register_sbts: " ^ msg



(*** Data ***)

type tts_register_sbts_in_type = 
  (string * string list) * Proof.context




(**** Visualization ****)

(*FIXME: complete the migration to SpecCheck.Show*)

fun show_tts_register_sbts_in 
  (tts_register_sbts_in : tts_register_sbts_in_type) = 
  let
    val ((sbt, risset), _) = tts_register_sbts_in
    val ctxt_c = "ctxt: unknown context" 
    val sbt_c = "sbt: " ^ sbt
    val risset_c = "risset: " ^ ML_Syntax.print_list I risset
    val out_c = [ctxt_c, sbt_c, risset_c] |> String.concatWith "\n"
  in Pretty.str out_c end;





(**** Tests ****)



(*** Wrapper ***)

fun tts_register_sbts ((args, ctxt) : tts_register_sbts_in_type) = 
  ETTS_Substitution.process_tts_register_sbts args ctxt;



(*** Exceptions ***)

fun test_exc_fvs ctxt _ = 
  let
    
    val sbt = "g::'q"
    val UA_c = "UA::'a set"
    val UB_c = "UB::'b set"
    val rissest = [UA_c, UB_c]

    val tts_register_sbts_in : tts_register_sbts_in_type = 
      ((sbt, rissest), ctxt)

    val err_msg = mk_msg_tts_register_sbts_error
      "all fixed variables that occur in the sbterm " ^
      "must be fixed in the context"

    val exn_prop = Prop.expect_failure (ERROR err_msg) tts_register_sbts

  in
    check_list_unit
      (show_tts_register_sbts_in) 
      [tts_register_sbts_in]
      "variables not fixed in the context"
      exn_prop 
  end;

fun test_exc_repeated_risset ctxt _ = 
  let
    
    val sbt = "f"
    val UA_c = "UA::'a set"
    val UB_c = "UA::'a set"
    val rissest = [UA_c, UB_c]

    val tts_register_sbts_in : tts_register_sbts_in_type = 
      ((sbt, rissest), ctxt)

    val err_msg = mk_msg_tts_register_sbts_error
      "the type variables associated with the risset must be distinct"

    val exn_prop = Prop.expect_failure (ERROR err_msg) tts_register_sbts

  in
    check_list_unit 
      show_tts_register_sbts_in 
      [tts_register_sbts_in]
      "repeated risset"
      exn_prop
  end;




(**** Test Suite ****)

fun test_suite ctxt s = [test_exc_fvs ctxt s, test_exc_repeated_risset ctxt s]
  |> Lecker.test_group ctxt s;

end;