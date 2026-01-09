(*  Title:      ML_Unification/mixed_unification.ML
    Author:     Kevin Kappelmann

Mixture of unification algorithms.
*)
signature MIXED_UNIFICATION =
sig
  include HAS_LOGGER

  (*first-order, then higher-order pattern, then fallback*)
  val fo_hop_e_match : Unification_Base.type_matcher -> Unification_Base.e_matcher
  val fo_hop_match : Unification_Base.matcher
  val norms_fo_hop_match : Unification_Base.normalisers

  val fo_hop_e_unify : Unification_Base.type_unifier -> Unification_Base.e_unifier
  val fo_hop_unify : Unification_Base.unifier
  val norms_fo_hop_unify : Unification_Base.normalisers

  (*fo_hop_e_unify with variable higher-order pattern unification fallback*)
  val fo_hop_var_hop_e_unify : Unification_Base.type_unifier -> Unification_Base.e_unifier
  val fo_hop_var_hop_unify : Unification_Base.unifier
  val norms_fo_hop_var_hop_unify : Unification_Base.normalisers

  (*fo_hop_var_hop_e_unify with higher-order unification fallback*)
  val fo_hop_var_hop_ho_e_unify : Unification_Base.type_unifier -> Unification_Base.e_unifier
  val fo_hop_var_hop_ho_unify : Unification_Base.unifier
  val norms_fo_hop_var_hop_ho_unify : Unification_Base.normalisers
end

structure Mixed_Unification : MIXED_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Mixed_Unification"

structure UUtil = Unification_Util
structure UCO = Unification_Combinator
structure Norm = Envir_Normalisation

fun pretty_unif_problem descr norm ctxt tp = Pretty.breaks [
    Pretty.str descr,
    UUtil.pretty_unif_problem ctxt (norm tp)
  ] |> Pretty.block |> Pretty.string_of

fun fo_hop_e_match match_types match_theory binders ctxt tp env = Seq.make (fn _ =>
  let
    val hop_comb_higher = Higher_Order_Pattern_Unification.e_match
        match_types match_theory match_theory
      |> Type_Unification.e_match match_types
    val fo_hop_comb_higher = First_Order_Unification.e_match match_types hop_comb_higher
  in
    (@{log Logger.DEBUG} ctxt (fn _ => pretty_unif_problem
      "First-order with higher-order pattern E-matching"
      (apfst (Norm.norm_term_match env)) ctxt tp);
    fo_hop_comb_higher binders ctxt tp env)
    |> Seq.pull
  end)
val fo_hop_match = fo_hop_e_match UUtil.match_types UCO.fail_match
val norms_fo_hop_match = UUtil.beta_eta_short_norms_match

fun fo_hop_e_unify unify_types unif_theory binders ctxt tp env = Seq.make (fn _ =>
  let
    val hop_comb_higher = Higher_Order_Pattern_Unification.e_unify
        unify_types unif_theory unif_theory
      |> Type_Unification.e_unify unify_types
    val fo_hop_comb_higher = First_Order_Unification.e_unify unify_types
      hop_comb_higher
  in
    (@{log Logger.DEBUG} ctxt (fn _ => pretty_unif_problem
      "First-order with higher-order pattern E-unifying"
      (apply2 (Norm.norm_term_unif env)) ctxt tp);
    fo_hop_comb_higher binders ctxt tp env)
    |> Seq.pull
  end)
val fo_hop_unify = fo_hop_e_unify UUtil.unify_types UCO.fail_unify
val norms_fo_hop_unify = UUtil.beta_eta_short_norms_unif

fun fo_hop_var_hop_e_unify unify_types unif_theory binders ctxt tp env = Seq.make (fn _ =>
  (@{log Logger.DEBUG} ctxt (fn _ => pretty_unif_problem
    "First-order with higher-order pattern with variable head higher-order pattern E-unifying"
    (apply2 (Norm.norm_term_unif env)) ctxt tp);
  UCO.add_fallback_unifier (fo_hop_e_unify unify_types)
    (UCO.norm_unifier (UUtil.inst_norm_term' norms_fo_hop_unify)
      (Var_Higher_Order_Pattern_Unification.e_unify unif_theory))
    binders ctxt tp env)
  |> Seq.pull)
val fo_hop_var_hop_unify = fo_hop_var_hop_e_unify UUtil.unify_types UCO.fail_unify
val norms_fo_hop_var_hop_unify = norms_fo_hop_unify

fun fo_hop_var_hop_ho_e_unify unify_types unif_theory binders ctxt tp env = Seq.make (fn _ =>
  (@{log Logger.DEBUG} ctxt (fn _ => pretty_unif_problem
    "First-order with higher-order pattern with variable head higher-order pattern with higher-order E-unifying"
    (apply2 (Norm.norm_term_unif env)) ctxt tp);
  UCO.add_fallback_unifier (fo_hop_var_hop_e_unify unify_types)
    (*Note: there is no higher-order E-unification as of 06.01.2026.
    We hence simply add the theory unifier as an alternative to the higher-order unifier*)
    (UCO.orelse_unifiers [Higher_Order_Unification.unify, unif_theory]) binders ctxt tp env)
  |> Seq.pull)
val fo_hop_var_hop_ho_unify = fo_hop_var_hop_ho_e_unify UUtil.unify_types UCO.fail_unify
val norms_fo_hop_var_hop_ho_unify = norms_fo_hop_var_hop_unify

end

signature MIXED_COMB_UNIFICATION =
sig
  include HAS_LOGGER

  structure UC : UNIFICATION_COMBINE

  (*first-order, then higher-order pattern with decomposition, then UC.e_unify*)
  val fo_hop_comb_e_unify : Unification_Base.type_unifier -> Unification_Base.e_unifier
  val fo_hop_comb_unify : Unification_Base.unifier
  val norms_fo_hop_comb_unify : Unification_Base.normalisers
end

functor Mixed_Comb_Unification_Functor(A :
  sig
    structure FI : FUNCTOR_INSTANCE_BASE
    structure UC : UNIFICATION_COMBINE
  end) : MIXED_COMB_UNIFICATION =
struct

structure FI = Functor_Instance(A.FI)
val logger = Logger.setup_new_logger Unification_Base.logger FI.name

structure UUtil = Unification_Util
structure UCO = Unification_Combinator
structure Norm = Envir_Normalisation
structure UC = A.UC

fun fo_hop_comb_e_unify unify_types unify_theory binders ctxt tp env = Seq.make (fn _ =>
  (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
      Pretty.block [Pretty.str "First-order with higher-order pattern with ",
        Binding.pretty UC.binding, Pretty.str " E-unifying"],
      UUtil.pretty_unif_problem ctxt (apply2 (Norm.norm_term_unif env) tp)
    ] |> Pretty.block |> Pretty.string_of);
  Mixed_Unification.fo_hop_e_unify unify_types (UC.e_unify unify_theory) binders ctxt tp env
  |> Seq.pull))
val fo_hop_comb_unify = fo_hop_comb_e_unify UUtil.unify_types UCO.fail_unify
val norms_fo_hop_comb_unify = Mixed_Unification.norms_fo_hop_unify
end
