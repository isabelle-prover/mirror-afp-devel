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

  (* symmetry *)
  (*try flipped unifier*)
  val flip_closed_unifier : Unification_Base.closed_unifier -> Unification_Base.closed_unifier
  val flip_unifier : Unification_Base.unifier -> Unification_Base.unifier
  val flip_e_unifier : Unification_Base.e_unifier -> Unification_Base.e_unifier

  val flip_closed_match : Unification_Base.closed_matcher -> Unification_Base.closed_matcher
  val flip_match : Unification_Base.matcher -> Unification_Base.matcher
  val flip_e_match : Unification_Base.e_matcher -> Unification_Base.e_matcher

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

  val orelse_closed_unifiers : Unification_Base.closed_unifier list ->
    Unification_Base.closed_unifier
  val orelse_closed_matchers : Unification_Base.closed_matcher list ->
    Unification_Base.closed_matcher
  val orelse_unifiers : Unification_Base.unifier list -> Unification_Base.unifier
  val orelse_matchers : Unification_Base.matcher list -> Unification_Base.matcher
  val orelse_e_unifiers : Unification_Base.e_unifier list -> Unification_Base.e_unifier
  val orelse_e_matchers : Unification_Base.e_matcher list -> Unification_Base.e_matcher

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

  (* binder replacements *)
  val replace_binders_closed_unifier : Unification_Base.closed_unifier -> Unification_Base.unifier
  val replace_binders_closed_matcher : Unification_Base.closed_matcher -> Unification_Base.matcher
  val replace_binders_unifier : Unification_Base.unifier -> Unification_Base.unifier
  val replace_binders_matcher : Unification_Base.matcher -> Unification_Base.matcher

  val replace_frees_closed_unifier : Unification_Base.closed_unifier -> Unification_Base.unifier
  val replace_frees_closed_matcher : Unification_Base.closed_matcher -> Unification_Base.matcher
  val replace_frees_unifier : Unification_Base.unifier -> Unification_Base.unifier
  val replace_frees_matcher : Unification_Base.matcher -> Unification_Base.matcher

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

(* symmetry *)
fun flip_closed_unifier unif ctxt tp = unif ctxt (swap tp)
  #> Seq.map (apsnd Unification_Base.symmetric)
fun flip_unifier unif = flip_closed_unifier o unif
fun flip_e_unifier unif = flip_unifier o unif

val flip_closed_match = flip_closed_unifier
val flip_match = flip_unifier
val flip_e_match = flip_e_unifier

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

fun orelse_closed_unifiers unifiers ctxt tp =
  fold_rev (fn unify => curry Tactic_Util.ORELSE (unify ctxt tp)) unifiers Seq.fail
val orelse_closed_matchers = orelse_closed_unifiers

fun orelse_unifiers unifiers binders ctxt tp =
  fold_rev (fn unify => curry Tactic_Util.ORELSE (unify binders ctxt tp)) unifiers Seq.fail
val orelse_matchers = orelse_unifiers

fun orelse_e_unifiers unifiers unif binders ctxt tp =
  fold_rev (fn unify => curry Tactic_Util.ORELSE (unify unif binders ctxt tp)) unifiers Seq.fail
val orelse_e_matchers = orelse_e_unifiers

(* normalisation *)
fun norm_closed_unifier norm_t unif ctxt tp env = unif ctxt (apply2 (Same.commit (norm_t env)) tp) env
fun norm_closed_matcher norm_p match ctxt (p, t) env = match ctxt (Same.commit (norm_p env) p, t) env

fun norm_unifier norm_t unif binders ctxt tp env =
  norm_closed_unifier norm_t (unif (Binders.norm_binders (norm_t env) binders)) ctxt tp env
fun norm_matcher norm_p match binders ctxt pt env =
  norm_closed_matcher norm_p (match (Binders.norm_binders (norm_p env) binders)) ctxt pt env

(* binder replacements *)
fun replace_binders_closed_unifier unif binders ctxt =
  unif ctxt o apply2 (Binders.replace_binders binders)
val replace_binders_closed_matcher = replace_binders_closed_unifier

fun replace_binders_unifier unif binders = replace_binders_closed_unifier (unif binders) binders
fun replace_binders_matcher match binders = replace_binders_closed_matcher (match binders) binders

fun replace_frees_closed_unifier unif binders ctxt =
  unif ctxt o apply2 (Binders.replace_frees binders)
val replace_frees_closed_matcher = replace_frees_closed_unifier

fun replace_frees_unifier unif binders = replace_frees_closed_unifier (unif binders) binders
fun replace_frees_matcher match binders = replace_frees_closed_matcher (match binders) binders

(* miscellaneous *)
val unifier_from_closed_unifier = replace_binders_closed_unifier
val matcher_from_closed_matcher = replace_binders_closed_matcher

end
