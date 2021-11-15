(* Title: CTR/Tests/CTR_TEST_PROCESS_RELATIVIZATION.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

signature CTR_TEST_PROCESS_RELATIVIZATION =
sig
type process_relativization_in_type
val test_suite : Proof.context -> unit -> unit
end;

structure ctr_test_process_relativization : CTR_TEST_PROCESS_RELATIVIZATION =
struct




(**** Background ****)

open SpecCheck;
structure Prop = SpecCheck_Property;
structure Show = SpecCheck_Show;




(**** Auxiliary ****)

fun mk_msg_ctr_error msg = "ctr: " ^ msg



(*** Data ***)

type process_relativization_in_type = 
  (
    (string * thm list option) option *
    Element.context list *
    (string * string) list *
    ((binding option * thm) * mixfix) 
  ) * Proof.context;



(*** Relation ***)

local

fun map_const_name (oldc, newc) (Const (c, T)) = 
    if oldc = c then Const (newc, T) else Const (c, T)
  | map_const_name eqc (Abs (c, T, t)) = Abs (c, T, map_const_name eqc t)
  | map_const_name eqc (t $ u) = map_const_name eqc t $ map_const_name eqc u
  | map_const_name _ t = t

in 
 
fun process_relativization_test_eq 
    (PPRelativization args1, PPRelativization args2) = 
      let
        val act_lthy = #2 args1
        val exp_lthy = #2 args2
        val (act_ow_def_t, act_tr_t) = args1
          |> #1
          |>> Local_Defs.meta_rewrite_rule act_lthy 
          |> apply2 Thm.full_prop_of
        val (exp_ow_def_t, exp_tr_t) = args2
          |> #1
          |>> Local_Defs.meta_rewrite_rule act_lthy 
          |> apply2 Thm.full_prop_of
        val act_ow_def_lhst = act_ow_def_t |> Logic.dest_equals |> #1
        val exp_ow_def_lhst = exp_ow_def_t |> Logic.dest_equals |> #1
        val thy = Proof_Context.theory_of exp_lthy
        val mapc = 
          (
            act_ow_def_lhst |> head_of |> dest_Const |> #1, 
            exp_ow_def_lhst |> head_of |> dest_Const |> #1
          )
        val act_ow_def_t' = map_const_name mapc act_ow_def_t
        val act_tr_t' = map_const_name mapc act_tr_t
        val act_ow_def_eq = Pattern.equiv thy (act_ow_def_t', exp_ow_def_t)
        val tr_eq = Pattern.equiv thy (act_tr_t', exp_tr_t)
        val _ = act_ow_def_eq |> Bool.toString |> writeln
      in act_ow_def_eq andalso tr_eq end
  | process_relativization_test_eq 
      (PPParametricity args1, PPParametricity args2) = 
      (*careful: not needed; hence, a usable implementation is not provided*)
      Thm.eq_thm (fst args1, fst args2) 
  | process_relativization_test_eq (_, _) = false;

end;



(**** Visualization ****)

(*FIXME: complete the migration to SpecCheck.Show*)

fun string_of_elem_ctxt_fixes args = "fixes: " ^
  (
    args
    |> map (fn (x, y, _) => (x, y)) 
    |> ML_Syntax.print_list 
      (ML_Syntax.print_pair Binding.print (ML_Syntax.print_option I))
  );
fun string_of_elem_ctxt_assumes ctxt args =
  let
    val string_of_fst = ML_Syntax.print_pair 
      Binding.print 
      (ML_Syntax.print_list (Token.pretty_src ctxt #> Pretty.string_of))
    val string_of_snd = 
      ML_Syntax.print_list (ML_Syntax.print_pair I (ML_Syntax.print_list I))
  in 
    "assumes: " ^ 
    ML_Syntax.print_list (ML_Syntax.print_pair string_of_fst string_of_snd) args
  end;
fun string_of_elem_ctxt_constrains _ = "constrains: unknown constrains";
fun string_of_elem_ctxt_defines _ = "defines: unknown defines";
fun string_of_elem_ctxt_notes _ = "notes: unknown notes";
fun string_of_elem_ctxt_lazy_notes _ = "lazy notes: unknown lazy notes";

fun string_of_elem_ctxt _ (Element.Fixes args : Element.context) = 
      string_of_elem_ctxt_fixes args
  | string_of_elem_ctxt _ (Element.Constrains args) = 
      string_of_elem_ctxt_constrains args
  | string_of_elem_ctxt ctxt (Element.Assumes args) = 
      string_of_elem_ctxt_assumes ctxt args
  | string_of_elem_ctxt _ (Element.Defines args) = 
      string_of_elem_ctxt_defines args
  | string_of_elem_ctxt _ (Element.Notes args) = 
      string_of_elem_ctxt_notes args
  | string_of_elem_ctxt _ (Element.Lazy_Notes args) = 
      string_of_elem_ctxt_lazy_notes args

fun show_relativization_in 
  ctxt
  (process_relativization_in : process_relativization_in_type) = 
  let
    val ((synthesis_opt, elems, type_specs, thm_spec), lthy) =
      process_relativization_in
    val synthesis_opt_c =
      let val synthesis_c = "synthesis: "
      in
        case synthesis_opt of 
          SOME synthesis => 
            (
              case #2 synthesis of 
                  SOME _ => synthesis_c ^ "user-defined simpset"
                | NONE => synthesis_c ^ "default simpset"
            )
        | NONE => synthesis_c ^ "none"
      end
    val elems_c = "elements:" ^ 
      (
        if null elems 
        then " none" 
        else "\n" ^
          (
            elems
            |> map (string_of_elem_ctxt ctxt)
            |> map (fn c => "\t" ^ c)
            |> String.concatWith "\n"
          )
      )
    val type_specs_c = "type_specs: " ^
      ML_Syntax.print_list (ML_Syntax.print_pair I I) type_specs
    val thm_spec_c =
      "definition: " ^ (thm_spec |> #1 |> #2 |> Thm.string_of_thm lthy) 
    val lthy_c = "lthy: unknown local theory" 
    val out_c = [synthesis_opt_c, elems_c, type_specs_c, thm_spec_c, lthy_c] 
      |> String.concatWith "\n"
  in Pretty.str out_c end;

fun show_relativization ctxt = 
  Show.zip (show_relativization_in ctxt) (Pretty.str o string_of_pp_out)




(**** Tests ****)



(*** Wrapper ***)

fun process_relativization 
  (
    ((synthesis, assms, type_specs, thm_spec), lthy) : 
      process_relativization_in_type
  ) = CTR.process_relativization synthesis assms type_specs thm_spec lthy;



(*** Valid inputs ***)

fun test_eq_trivial ctxt _ = 
  let
    (*input*)
    val {synthesis, elems, type_specs, thm_specs, ...} = 
      ctr_test_data_of_proof ctxt "mono_with" |> the
    val process_relativization_in : process_relativization_in_type = 
      ((synthesis, elems, type_specs, the_single thm_specs), ctxt)
    (*output*)
    val process_relativization_out = 
      PPRelativization ((@{thm mono_ow_def}, @{thm mono_ow_transfer'}), ctxt)
  in
    check_list_unit
      (show_relativization ctxt)
      [(process_relativization_in, process_relativization_out)]
      "equality"
      (
        Prop.prop 
          (
            fn (val_in, exp_out) => 
              process_relativization_test_eq
                (process_relativization val_in, exp_out)
          )
       )
  end;



(*** Exceptions ***)

fun test_exc_template ctxt input_name_c err_msg_end_c test_name_c = 
  let
    val {synthesis, elems, type_specs, thm_specs, ...} = 
      ctr_test_data_of_proof ctxt input_name_c |> the
    val args = ((synthesis, elems, type_specs, the_single thm_specs), ctxt)
    val err_msg = mk_msg_ctr_error err_msg_end_c
    val exn_prop = Prop.expect_failure (ERROR err_msg) process_relativization
  in 
    check_list_unit
      (show_relativization_in ctxt) 
      [args]
      test_name_c
      exn_prop 
  end;

fun test_exc_def ctxt _ = 
  let
    val err_msg_end_c = 
      (
        Syntax.string_of_term ctxt (Thm.full_prop_of @{thm exI}) ^ 
        " is not a definition"
      )
  in test_exc_template ctxt "exI" err_msg_end_c "not a definition" end;

fun test_exc_binrel ctxt _ = 
  let val err_msg_end_c = "trp: trp must consist of (stv, binary relation) pairs"
  in test_exc_template ctxt "binrel" err_msg_end_c "binary relation" end;

fun test_exc_binrel_ftv ctxt _ = 
  let 
    val err_msg_end_c = 
      "trp: the user-specified binary relations must " ^
      "be defined over type variables"
  in test_exc_template ctxt "binrel_ftv" err_msg_end_c "binary relation ftv" end;

fun test_exc_dup_stvs ctxt _ = 
  let val err_msg_end_c = "trp: duplicate stvs"
  in test_exc_template ctxt "dup_stvs" err_msg_end_c "duplicate stv" end;

fun test_exc_dup_binrel_ftvs ctxt _ = 
  let 
    val err_msg_end_c = 
      "trp: duplicate ftvs in the specification of the binary relations"
  in 
    test_exc_template 
      ctxt "dup_binrel_ftvs" err_msg_end_c "duplicate binrel ftvs" 
  end;

fun test_exc_no_relator ctxt _ = 
  let val err_msg_end_c = "no relator found for the type constructor CTR_Tests.K"
  in test_exc_template ctxt "no_relator" err_msg_end_c "no relator" end;

fun test_exc_invalid_relator ctxt _ = 
  let
    val err_msg_end_c = 
      (
        "the relator found for the type constructor CTR_Tests.L " ^
        "is not suitable (is there is a mismatch of type variables?)" 
      )
  in
    test_exc_template ctxt "invalid_relator" err_msg_end_c "invalid relator" 
  end;




(**** Test Suite ****)

fun test_suite ctxt s = 
  [
    test_eq_trivial,
    test_exc_def,
    test_exc_binrel,
    test_exc_binrel_ftv,
    test_exc_dup_stvs,
    test_exc_dup_binrel_ftvs,
    test_exc_no_relator,
    test_exc_invalid_relator
  ]
  |> map (fn f => f ctxt s) 
  |> Lecker.test_group ctxt s;

end;