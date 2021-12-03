(*
  File: extra_hol.ML
  Author: Bohua Zhan

  Extra setup for HOL.
*)

signature EXTRA_HOL =
sig
  val add_forward_arg1_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_forward_arg1_prfstep: thm -> theory -> theory
  val add_forward_arg_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_forward_arg_prfstep: thm -> theory -> theory
  val add_rewrite_arg_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_arg_rule: thm -> theory -> theory

  val add_simple_datatype: string -> theory -> theory
  val del_simple_datatype: string -> theory -> theory
end;

functor Extra_HOL(
  structure Basic_UtilBase: BASIC_UTIL_BASE;
  structure Basic_UtilLogic: BASIC_UTIL_LOGIC;
  structure ProofStep: PROOFSTEP;
  structure ProofStepData: PROOFSTEP_DATA;
  ): EXTRA_HOL =
struct

fun add_forward_arg1_prfstep_cond th conds thy =
    let
      val concl = th |> Basic_UtilLogic.concl_of' |> Basic_UtilLogic.strip_conj |> hd
    in
      thy |> ProofStepData.add_forward_prfstep_cond
          th ([K (ProofStep.WithTerm (dest_arg1 concl))] @ conds)
    end

fun add_forward_arg1_prfstep th = add_forward_arg1_prfstep_cond th []

fun add_forward_arg_prfstep_cond th conds thy =
    let
      val concl = th |> Basic_UtilLogic.concl_of' |> Basic_UtilLogic.strip_conj |> hd
    in
      thy |> ProofStepData.add_forward_prfstep_cond
          th ([K (ProofStep.WithTerm (dest_arg concl))] @ conds)
    end

fun add_forward_arg_prfstep th = add_forward_arg_prfstep_cond th []

fun add_rewrite_arg_rule_cond th conds thy =
    let
      val concl = th |> Basic_UtilLogic.concl_of' |> Basic_UtilLogic.strip_conj |> hd
      val _ = assert (Basic_UtilBase.is_eq_term concl) "rewrite_arg"
      val (lhs, _) = Basic_UtilBase.dest_eq concl
    in
      thy |> ProofStepData.add_forward_prfstep_cond
          th ([K (ProofStep.WithTerm (dest_arg lhs))] @ conds)
    end

fun add_rewrite_arg_rule th = add_rewrite_arg_rule_cond th []

fun add_simple_datatype s thy =
    let
      val collapse_th = Global_Theory.get_thm thy (s ^ ".collapse")
      val case_th = Global_Theory.get_thm thy (s ^ ".case")
      val sel_th = Global_Theory.get_thms thy (s ^ ".sel")
      val simp_th = hd (Global_Theory.get_thms thy (s ^ ".simps"))
      val var = collapse_th |> Basic_UtilLogic.prop_of' |> dest_arg
      val (f, args) = collapse_th |> Basic_UtilLogic.prop_of' |> dest_arg1 |> Term.strip_comb
      val vars = map (fn (n, T) => Var (("x",n),T))
                     (tag_list 1 (map fastype_of args))
      val rhs = Term.list_comb (f, vars)
      val neq = Basic_UtilLogic.get_neg (Basic_UtilBase.mk_eq (var, rhs))
      val filt = [ProofStepData.with_filt (ProofStep.neq_filter neq)]
    in
      thy |> ProofStepData.add_rewrite_rule_back_cond collapse_th filt
          |> ProofStepData.add_rewrite_rule case_th
          |> fold ProofStepData.add_rewrite_rule sel_th
          |> ProofStepData.add_forward_prfstep (Basic_UtilLogic.equiv_forward_th simp_th)
    end

fun del_simple_datatype s thy =
    let
      val collapse_th = Global_Theory.get_thm thy (s ^ ".collapse")
      val case_th = Global_Theory.get_thm thy (s ^ ".case")
      val sel_th = Global_Theory.get_thms thy (s ^ ".sel")
      val simp_th = hd (Global_Theory.get_thms thy (s ^ ".simps"))
    in
      thy |> fold ProofStepData.del_prfstep_thm (collapse_th :: case_th :: simp_th :: sel_th)
    end

end  (* structure Extra_HOL *)
