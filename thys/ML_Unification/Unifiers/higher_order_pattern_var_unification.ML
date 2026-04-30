(*  Title:      ML_Unification/higher_order_pattern_var_unification.ML
    Author:     Kevin Kappelmann

Unifies terms of the form ?H b1 ... bn \<equiv>\<^sup>? t where
(1) b1,...,bn are distinct, bound variables and
(2) ?H does not occur in t
with the higher-order pattern matcher. This pattern occurs frequently when unifying theorems with a
goal containing bound variables.

Example: If we want to solve the goal "\<And>x. ?P x 0" with a lemma ?Q by resolution,
the bound variables of the goal are first lifted to the lemma, resulting in "?Q x".
Next, the terms "?Q x \<equiv>\<^sup>? ?P x 0" are unified. Unfortunately, this problem falls outside the
higher-order pattern fragment since 0 is a constant and outside the first-order fragment.
However, the problem is first-order before lifting the bound variables:
we should be able to use ?Q to solve any goal G by setting ?Q to G.
The unifier of this file returns the expected substitution "?Q := \<lambda>x. ?P x 0" in this case.
*)
signature HIGHER_ORDER_VAR_PATTERN_UNIFICATION =
sig
  include HAS_LOGGER

  (*is t a higher-order pattern variable,
  i.e. a term of the form ?H b1 ... bn where b_1,...,b_n are distinct, bound variables*)
  val is_hop_var : term -> bool * (term * term list)
  val can_hop_var_match : term * term -> bool * term list
  val e_unify : Unification_Base.e_unifier
end

structure Higher_Order_Pattern_Var_Unification : HIGHER_ORDER_VAR_PATTERN_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Higher_Order_Pattern_Var_Unification"

structure Util = Unification_Util
structure Comb = Unification_Combinator

fun is_hop_var t = let val t' as (head, args) = strip_comb t
  in (is_Var head andalso forall is_Bound args andalso not (has_duplicates (op aconv) args), t') end

fun can_hop_var_match (p, t) = let val (is_hop_var, (head, args)) = is_hop_var p
  in
    if is_hop_var andalso not (Term.exists_subterm (equal head) t) then (true, args)
    else (false, [])
  end

local
  exception FALLBACK of Pretty.T
  val form_msg = "?H b1 ... bn \<equiv>\<^sup>? t where ?H does not occur in t."
  fun seq_try msg = General_Util.seq_try (FALLBACK (Pretty.str msg))
in

(*pre-condition: (t, p) are normalised wrt. the passed environment*)
fun e_unify unif_theory binders ctxt (tp as (t, p)) env = Seq.make (fn _ =>
  let
    val hop_match_type_unif =
      Higher_Order_Pattern_Unification.e_match Util.unify_types Comb.fail_match Comb.fail_match
      |> Type_Unification.e_unify Util.unify_types
    val hop_match_type_unif_tp = hop_match_type_unif binders ctxt tp
    val hop_match_type_unif_pt = Comb.flip_unifier hop_match_type_unif binders ctxt tp
    val seq_try = seq_try "Higher-order pattern matching failed."
  in
    ((@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
        Pretty.str "Higher-order pattern variable E-unifying",
        Util.pretty_unif_problem binders ctxt tp
      ] |> Pretty.block |> Pretty.string_of);
    case apply2 can_hop_var_match (tp, (p, t)) of
      ((true, boundst), (true, boundsp)) => (if length boundst >= length boundsp
          then hop_match_type_unif_tp else hop_match_type_unif_pt) env
        |> seq_try
    | ((true, _), _) => hop_match_type_unif_tp env |> seq_try
    | (_, (true, _)) => hop_match_type_unif_pt env |> seq_try
    | _ => raise FALLBACK (Pretty.str ("Terms not of the form " ^ form_msg)))
    handle FALLBACK msg => (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
          msg,
          Util.pretty_call_theory_unif binders ctxt tp
        ] |> Pretty.block |> Pretty.string_of);
      unif_theory binders ctxt tp env))
    |> Seq.pull
  end)
end

end
