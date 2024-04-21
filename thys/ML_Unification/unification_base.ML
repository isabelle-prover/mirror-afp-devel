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

  (* normalisers for matching/unification results (\<sigma>, lhs \<equiv> rhs) of terms t1 \<equiv>\<^sup>? t2:
  it must hold (ignoring conversions between terms and theorems) that
  - inst_unif_thm(\<sigma>, lhs \<equiv> rhs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> (inst_term(\<sigma>, t1) \<equiv> inst_term(\<sigma>, t2))
  - norm_term(inst_unif_thm(\<sigma>, lhs \<equiv> rhs)) \<equiv>\<^sub>\<alpha> norm_term(inst_term(\<sigma>, t1) \<equiv> inst_term(\<sigma>, t2))
  *)
  type normalisers = {
    (*instantiation for equality theorem of unifier*)
    inst_unif_thm : Envir_Normalisation.thm_normaliser,
    (*instantiation for terms*)
    inst_term : Envir_Normalisation.term_normaliser,
    (*instantiation for theorems corresponding to inst_term*)
    inst_thm : Envir_Normalisation.thm_normaliser,
    (*normalisation for terms*)
    norm_term : Term_Normalisation.term_normaliser,
    (*normalisation conversion corresponding to norm_term*)
    conv : conv
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
  inst_unif_thm : Envir_Normalisation.thm_normaliser,
  inst_term : Envir_Normalisation.term_normaliser,
  inst_thm : Envir_Normalisation.thm_normaliser,
  norm_term : Term_Normalisation.term_normaliser,
  conv : conv
}

end
