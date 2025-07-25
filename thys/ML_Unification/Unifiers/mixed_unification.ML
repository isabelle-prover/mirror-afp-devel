(*  Title:      ML_Unification/mixed_unification.ML
    Author:     Kevin Kappelmann

Mixture of unification algorithms.
*)
signature MIXED_UNIFICATION =
sig
  include HAS_LOGGER

  structure UC : UNIFICATION_COMBINE

  (*first-order, then higher-order pattern with decomposition, then UC.e_unify,
  then higher-order unification fallback*)
  val first_higherp_decomp_comb_higher_unify : Unification_Base.unifier
  val norms_first_higherp_decomp_comb_higher_unify : Unification_Base.normalisers
end

functor Mixed_Unification (A :
  sig
    structure FI : FUNCTOR_INSTANCE_BASE
    structure UC : UNIFICATION_COMBINE
  end) : MIXED_UNIFICATION =
struct

structure FI = Functor_Instance(A.FI)
val logger = Logger.setup_new_logger Unification_Base.logger FI.name

structure UUtil = Unification_Util
structure UCO = Unification_Combinator
structure UC = A.UC

fun first_higherp_decomp_comb_higher_unify binders ctxt tp env = Seq.make (fn _ =>
  let
    val unify_types = UUtil.unify_types
    val comb_higher = UCO.add_fallback_unifier UC.e_unify Higher_Order_Unification.unify
    val decomp_comb_higher = UCO.add_fallback_unifier
      (Higher_Order_Pattern_Decomp_Unification.e_unify first_higherp_decomp_comb_higher_unify)
      comb_higher
    val higherp_decomp_comb_higher = UCO.add_fallback_unifier
        (Higher_Order_Pattern_Unification.e_unify unify_types decomp_comb_higher)
        comb_higher
      |> Type_Unification.e_unify unify_types
    val fo_higherp_decomp_comb_higher = UCO.add_fallback_unifier
      (First_Order_Unification.e_unify unify_types) higherp_decomp_comb_higher
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
      Pretty.str "First-order with higher-order pattern with decomposition with ",
      Binding.pretty UC.binding,
      Pretty.str " with higher-order fallback unifying ",
      UUtil.pretty_unif_problem ctxt (apply2 (Envir_Normalisation.norm_term_unif env) tp)]
      |> Pretty.string_of);
    fo_higherp_decomp_comb_higher binders ctxt tp env)
    |> Seq.pull
  end)

val norms_first_higherp_decomp_comb_higher_unify = UUtil.beta_eta_short_norms_unif

end
