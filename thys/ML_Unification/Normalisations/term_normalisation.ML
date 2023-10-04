(*  Title: ML_Unification/term_normalisation.ML
    Author: Kevin Kappelmann

Term normalisations.
*)
signature TERM_NORMALISATION =
sig
  type term_normaliser = term -> term
  val beta : term_normaliser
  val eta_short : term_normaliser
  val beta_eta_short : term_normaliser
end

structure Term_Normalisation : TERM_NORMALISATION =
struct

type term_normaliser = term -> term

val beta = Envir.beta_norm
val eta_short = Envir.eta_contract
val beta_eta_short = Envir.beta_eta_contract

end

