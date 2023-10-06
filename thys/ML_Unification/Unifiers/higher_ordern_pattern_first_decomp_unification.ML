(*  Title:      ML_Unification/higher_ordern_pattern_first_decomp_unification.ML
    Author:     Kevin Kappelmann

Higher-order pattern matching/unification with decomposition of non-pattern terms into a
higher-order pattern prefix and a list of remaining arguments. This is essentially
a combination of higher-order pattern and first-order matching/unification.

Example: Let 0, 1 be bound variables and f, g, c be constants.
The unification problem ?x 0 1 (?y c 0) \<equiv>\<^sup>? f (g c 0)
is decomposed into ?x 0 1 \<equiv>\<^sup>? f and (?y c 0) \<equiv>\<^sup>? (g c 0).
The latter, in turn, is decomposed into ?y \<equiv>\<^sup>? g and c \<equiv>\<^sup>? c and 0 \<equiv>\<^sup>? 0.
*)
signature HIGHER_ORDERN_PATTERN_FIRST_DECOMP_UNIFICATION =
sig
  include HAS_LOGGER

  val e_match : Unification_Base.type_matcher -> Unification_Base.matcher ->
    Unification_Base.e_matcher
  val match : Unification_Base.matcher
  val norms_match : Unification_Base.normalisers

  val e_unify : Unification_Base.type_unifier -> Unification_Base.unifier ->
    Unification_Base.e_unifier
  val unify : Unification_Base.unifier
  val norms_unify : Unification_Base.normalisers
end

structure Higher_Ordern_Pattern_First_Decomp_Unification :
  HIGHER_ORDERN_PATTERN_FIRST_DECOMP_UNIFICATION =
struct

val logger = Logger.setup_new_logger Unification_Base.logger
  "Higher_Ordern_Pattern_First_Decomp_Unification"

structure UUtil = Unification_Util
structure HOP = Higher_Order_Pattern_Unification
structure UC = Unification_Combinator

(*compute pattern prefixes*)
fun bounds_prefix bounds [] = (rev bounds, [])
  | bounds_prefix bounds (t :: ts) =
      if is_Bound t andalso not (member (op =) bounds t)
      then bounds_prefix (t :: bounds) ts
      else (rev bounds, t :: ts)
val bounds_prefix = bounds_prefix []

datatype ('a, 'b) either = Left of 'a | Right of 'b

fun bounds_prefix2 (bounds1, _) ([], _) = Left (rev bounds1, [])
  | bounds_prefix2 (_, bounds2) (_, []) = Right (rev bounds2, [])
  | bounds_prefix2 (bounds1, bounds2) (s :: ss, t :: ts)  =
      if is_Bound s andalso not (member (op =) bounds1 s)
      then if is_Bound t andalso not (member (op =) bounds2 t)
        then bounds_prefix2 (s :: bounds1, t :: bounds2) (ss, ts)
        else Right (rev bounds2, t :: ts)
      else Left (rev bounds1, s :: ss)
val bounds_prefix2 = bounds_prefix2 ([], [])

fun mk_decomp _ (_, []) = NONE (*no decomposition took place*)
  | mk_decomp h (args, rem) = SOME (list_comb (h, args), rem)

fun mk_bounds_decomp h args = bounds_prefix args |> mk_decomp h

fun pattern_prefix_match p = case strip_comb p of
    (v as Var _, args) => mk_bounds_decomp v args
  | _ => NONE

fun pattern_prefix_unif tp = case apply2 strip_comb tp of
    ((vl as Var _, argsl), (vr as Var _, argsr)) => (case bounds_prefix2 (argsl, argsr) of
        Left res => mk_decomp vl res |> Option.map Left
      | Right res => mk_decomp vr res |> Option.map Right)
  | ((v as Var _, args), _) => mk_bounds_decomp v args |> Option.map Left
  | (_, (v as Var _, args)) => mk_bounds_decomp v args |> Option.map Right
  | _ => NONE

fun mk_decomp_other ss t =
  let
    val (th, ts) = strip_comb t
    val n = length ts - length ss
  in if n < 0 then NONE else chop n ts |> mk_decomp th end

fun decompose_msg ctxt tp = Pretty.block [
    Pretty.str "Decomposing ",
    UUtil.pretty_unif_problem ctxt tp,
    Pretty.str " into higher-order pattern prefix and list of remaining arguments."
  ] |> Pretty.string_of

fun decomposed_msg ctxt (ph, th) (ps, ts) = Pretty.block [
    Pretty.str "Decomposition result ",
    map (UUtil.pretty_unif_problem ctxt) ((ph, th) :: (ps ~~ ts))
    |> Pretty.separate "," |> Pretty.block
  ] |> Pretty.string_of

fun e_match match_types match_pattern match_theory =
  let fun fallback_pattern binders ctxt (pt as (p, t)) =
    let fun failure () =
      (@{log Logger.DEBUG} ctxt (fn _ => "Decomposition failed. Calling theory matcher.");
      match_theory binders ctxt pt)
    in
      (@{log Logger.DEBUG} ctxt (fn _ => decompose_msg ctxt pt);
      case pattern_prefix_match p of
        SOME (ph, ps) => (case mk_decomp_other ps t of
          SOME (th, ts) =>
            (@{log Logger.TRACE} ctxt (fn _ => decomposed_msg ctxt (ph, th) (ps, ts));
            UUtil.strip_comb_strip_comb (K o K I) match_pattern
              binders ctxt (ph, th) (ps, ts))
        | NONE => failure ())
      | NONE => failure ())
    end
  in
    HOP.e_match match_types (UC.norm_matcher (#norm_term HOP.norms_match) fallback_pattern)
    match_theory
  end

val match = e_match UUtil.match_types UC.fail_match UC.fail_match
val norms_match = HOP.norms_match

fun e_unify unif_types unif_pattern unif_theory =
  let
    val unif_patterns =
      UUtil.strip_comb_strip_comb Envir_Normalisation.norm_thm_types_unif unif_pattern
    fun fallback_pattern binders ctxt (tp as (s, t)) =
      let fun failure () =
        (@{log Logger.DEBUG} ctxt (fn _ => "Decomposition failed. Calling theory unifier.");
        unif_theory binders ctxt tp)
      in
        (@{log Logger.DEBUG} ctxt (fn _ => decompose_msg ctxt tp);
        case pattern_prefix_unif tp of
          SOME (Left (sh, ss)) => (case mk_decomp_other ss t of
            SOME (th, ts) =>
              (@{log Logger.TRACE} ctxt (fn _ => decomposed_msg ctxt (sh, th) (ss, ts));
              unif_patterns binders ctxt (sh, th) (ss, ts))
          | NONE => failure ())
        | SOME (Right (th, ts)) => (case mk_decomp_other ts s of
            SOME (sh, ss) =>
              (@{log Logger.TRACE} ctxt (fn _ => decomposed_msg ctxt (sh, th) (ss, ts));
              unif_patterns binders ctxt (sh, th) (ss, ts))
          | NONE => failure ())
        | NONE => failure ())
      end
  in
    HOP.e_unify unif_types (UC.norm_unifier (#norm_term HOP.norms_unify) fallback_pattern)
    unif_theory
  end

val unify = e_unify UUtil.unify_types UC.fail_unify UC.fail_unify

val norms_unify = HOP.norms_unify

end
