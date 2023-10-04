(*  Title:      ML_Unification/unification_combinator.ML
    Author:     Kevin Kappelmann

Unification combinators.
*)
signature UNIFICATION_COMBINATOR =
sig
  (* failures *)
  val fail_closed_unify : Unification_Base.closed_unifier
  val fail_unify : Unification_Base.unifier
  val fail_e_unify : Unification_Base.e_unifier

  val fail_closed_match : Unification_Base.closed_matcher
  val fail_match : Unification_Base.matcher
  val fail_e_match : Unification_Base.e_matcher

  (* fallbacks *)
  (*"add_fallback_e_unifier u1 u2 u" creates a unifier that calls u1 with fallback unifier "u2 u"*)
  val add_fallback_e_unifier : Unification_Base.e_unifier -> Unification_Base.e_unifier ->
    Unification_Base.e_unifier
  (*"add_fallback_unifier u1 u2" creates a unifier that calls u1 with fallback unifier u2*)
  val add_fallback_unifier : Unification_Base.e_unifier -> Unification_Base.unifier ->
    Unification_Base.unifier

  val add_fallback_e_matcher : Unification_Base.e_matcher -> Unification_Base.e_matcher ->
    Unification_Base.e_matcher
  val add_fallback_matcher : Unification_Base.e_matcher -> Unification_Base.matcher ->
    Unification_Base.matcher

  (* sequential *)
  (*try all unifiers in sequence*)
  val concat_closed_unifiers : Unification_Base.closed_unifier list ->
    Unification_Base.closed_unifier
  val concat_closed_matchers : Unification_Base.closed_matcher list ->
    Unification_Base.closed_matcher
  val concat_unifiers : Unification_Base.unifier list -> Unification_Base.unifier
  val concat_matchers : Unification_Base.matcher list -> Unification_Base.matcher
  val concat_e_unifiers : Unification_Base.e_unifier list -> Unification_Base.e_unifier
  val concat_e_matchers : Unification_Base.e_matcher list -> Unification_Base.e_matcher

  (* normalisation *)
  (*apply normaliser before calling the matcher/unifier*)
  val norm_closed_unifier : Envir_Normalisation.term_normaliser -> Unification_Base.closed_unifier ->
    Unification_Base.closed_unifier
  val norm_closed_matcher : Envir_Normalisation.term_normaliser -> Unification_Base.closed_matcher ->
    Unification_Base.closed_matcher
  val norm_unifier : Envir_Normalisation.term_normaliser -> Unification_Base.unifier ->
    Unification_Base.unifier
  val norm_matcher : Envir_Normalisation.term_normaliser -> Unification_Base.matcher ->
    Unification_Base.matcher

  (* miscellaneous *)
  (*approximates a unifier (working with bound variables) from a closed unifier
    by replacing all bound variables with their associated free variables*)
  val unifier_from_closed_unifier : Unification_Base.closed_unifier -> Unification_Base.unifier
  val matcher_from_closed_matcher : Unification_Base.closed_matcher -> Unification_Base.matcher

end

structure Unification_Combinator : UNIFICATION_COMBINATOR =
struct

structure UB = Unification_Base

(* failures *)
val fail_closed_unify = K o K o K Seq.empty
val fail_unify = K fail_closed_unify
val fail_e_unify = K fail_unify

val fail_closed_match = fail_closed_unify
val fail_match = fail_unify
val fail_e_match = fail_e_unify

(* fallbacks *)
fun add_fallback_e_unifier e_unif1 e_unif2 = e_unif1 o e_unif2
fun add_fallback_unifier e_unif1 e_unif2 = add_fallback_e_unifier e_unif1 (K e_unif2) fail_unify

val add_fallback_e_matcher = add_fallback_e_unifier
fun add_fallback_matcher e_match1 e_match2 = add_fallback_e_matcher e_match1 (K e_match2) fail_match

(* sequential *)
fun concat_closed_unifiers unifiers ctxt tp =
  fold_rev (fn unify => curry Seq.APPEND (unify ctxt tp)) unifiers Seq.fail
val concat_closed_matchers = concat_closed_unifiers

fun concat_unifiers unifiers binders ctxt tp =
  fold_rev (fn unify => curry Seq.APPEND (unify binders ctxt tp)) unifiers Seq.fail
val concat_matchers = concat_unifiers

fun concat_e_unifiers unifiers unif binders ctxt tp =
  fold_rev (fn unify => curry Seq.APPEND (unify unif binders ctxt tp)) unifiers Seq.fail
val concat_e_matchers = concat_e_unifiers

(* normalisation *)
fun norm_closed_unifier norm_t unif ctxt tp env = unif ctxt (apply2 (norm_t env) tp) env
fun norm_closed_matcher norm_p match ctxt (p, t) env = match ctxt (norm_p env p, t) env

fun norm_unifier norm_t unif binders ctxt tp env =
  norm_closed_unifier norm_t (unif (Binders.norm_binders (norm_t env) binders)) ctxt tp env
fun norm_matcher norm_p match binders ctxt pt env =
  norm_closed_matcher norm_p (match (Binders.norm_binders (norm_p env) binders)) ctxt pt env

(* miscellaneous *)
fun unifier_from_closed_unifier unify binders ctxt =
  unify ctxt o apply2 (Binders.replace_binders binders)
val matcher_from_closed_matcher = unifier_from_closed_unifier

end
