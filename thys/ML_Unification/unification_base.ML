(*  Title:      ML_Unification/unification_base.ML
    Author:     Kevin Kappelmann

Basic definitions for unifiers.
*)
signature UNIFICATION_BASE =
sig
  include HAS_LOGGER

  val reflexive : cterm -> thm
  val combination : thm -> thm -> thm
  val symmetric : thm -> thm
  val abstract_rule : Proof.context -> string -> cterm -> thm -> thm option
  val reflexive_term : Proof.context -> term -> thm

  (*raised on unsupported input*)
  exception PATTERN

  (*raised on unification failure for non-sequence outputs (e.g. type unification)*)
  exception UNIF

  type type_unifier = Proof.context -> typ * typ -> Envir.env -> Envir.env
  type type_matcher = type_unifier

  type closed_unifier = Proof.context -> term * term -> Envir.env -> (Envir.env * thm) Seq.seq
  (*term binders stores fresh free variables associated to each loose bound variable*)
  type unifier = term Binders.binders -> closed_unifier
  type e_unifier = unifier -> unifier

  type closed_matcher = closed_unifier
  type matcher = unifier
  type e_matcher = matcher -> matcher

  (* normalisers for matchers/unifiers *)
  type normalisers = {
    (*normaliser for result of unifier*)
    norm_unif_thm : Envir_Normalisation.thm_normaliser,
    (*normaliser for other theorems*)
    norm_thm : Envir_Normalisation.thm_normaliser,
    (*normaliser for terms*)
    norm_term : Envir_Normalisation.term_normaliser
  }

end

structure Unification_Base : UNIFICATION_BASE =
struct

val logger = Logger.setup_new_logger Logger.root "Unification_Base"

val reflexive = Thm.reflexive
val combination = Thm.combination
val symmetric = Thm.symmetric
val abstract_rule = Thm_Util.abstract_rule

val reflexive_term = reflexive oo Thm.cterm_of

exception PATTERN = Pattern.Pattern

exception UNIF = Pattern.Unif
type type_unifier = Proof.context -> typ * typ -> Envir.env -> Envir.env
type type_matcher = type_unifier
type closed_unifier = Proof.context -> term * term -> Envir.env ->
  (Envir.env * thm) Seq.seq
type unifier = term Binders.binders -> closed_unifier
type e_unifier = unifier -> unifier
type closed_matcher = closed_unifier
type matcher = unifier
type e_matcher = matcher -> matcher

type normalisers = {
  norm_unif_thm : Envir_Normalisation.thm_normaliser,
  norm_thm : Envir_Normalisation.thm_normaliser,
  norm_term : Envir_Normalisation.term_normaliser
}

end
