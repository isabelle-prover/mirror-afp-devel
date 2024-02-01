(*  Title:      ML_Unification/var_higher_order_pattern_unification.ML
    Author:     Kevin Kappelmann

Unifies terms of the form ?H b1 ... bn \<equiv>\<^sup>? t where
(1) b1,...,bn are bound variables and
(2) ?H does not occur in t
with the higher-order pattern matcher. This pattern occurs frequently when unifying theorems with a
goal containing bound variables.

Example: If we want to solve the goal "\<And>x. ?P x 0" with a lemma ?Q by resolution,
the bound variables of the goal are first lifted to lemma, resulting in "?Q x".
Next, the terms "?Q x \<equiv>\<^sup>? ?P x 0" are unified. Unfortunately, this problem falls outside the
higher-order pattern fragment since 0 is a constant.
However, the problem seems essentially first-order before lifting the bound variables:
we should be able to use ?Q to solve any goal G by setting ?Q to G.
The unifier of this file returns the expected substitution "?Q := \<lambda>x. ?P x 0" in this case.
*)
signature VAR_HIGHER_ORDER_PATTERN_UNIFICATION =
sig
  include HAS_LOGGER

  val can_var_pattern_unif : term * term -> bool * term list
  val e_unify : Unification_Base.e_unifier
end

structure Var_Higher_Order_Pattern_Unification : VAR_HIGHER_ORDER_PATTERN_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Var_Higher_Order_Pattern_Unification"

structure Util = Unification_Util

fun can_var_pattern_unif (p, t) = let val (head, args) = strip_comb p
  in
    if is_Var head andalso forall is_Bound args andalso not (has_duplicates (op aconv) args)
      andalso not (Term.exists_subterm (curry (op =) head) t)
    then (true, args)
    else (false, [])
  end

fun e_unify unif_theory binders ctxt (tp as (t, p)) env =
  let
    exception FALLBACK of Pretty.T
    val hop_match_type_unif = Higher_Order_Pattern_Unification.e_match Util.unify_types
      Unification_Combinator.fail_match Unification_Combinator.fail_match binders ctxt
    val hop_match_type_unif_tp = hop_match_type_unif tp
    val hop_match_type_unif_pt = hop_match_type_unif (p, t) #> Seq.map (apsnd Unification_Base.symmetric)
    val seq_try = General_Util.seq_try (FALLBACK (Pretty.str "Higher-order pattern matching failed."))
  in
    (@{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
        Pretty.str "Variable head higher-order pattern unifying ",
        Util.pretty_unif_problem ctxt tp
      ] |> Pretty.string_of);
    case apply2 can_var_pattern_unif (tp, (p, t)) of
      ((true, boundst), (true, boundsp)) =>
        if length boundst >= length boundsp
        then hop_match_type_unif_tp env |> seq_try
        else hop_match_type_unif_pt env |> seq_try
    | ((true, _), _) => hop_match_type_unif_tp env |> seq_try
    | (_, (true, _)) => hop_match_type_unif_pt env |> seq_try
    | _ => raise FALLBACK
        (Pretty.str "Terms not of the form ?H b1 ... bn \<equiv>\<^sup>? t where ?H does not occur in t."))
    handle FALLBACK msg => (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
        msg,
        Util.pretty_call_theory_unif ctxt tp
      ] |> Pretty.block |> Pretty.string_of);
      unif_theory binders ctxt tp env)
  end

end
