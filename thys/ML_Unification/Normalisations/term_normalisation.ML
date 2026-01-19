(*  Title: ML_Unification/term_normalisation.ML
    Author: Kevin Kappelmann

Term normalisations.
*)
signature TERM_NORMALISATION =
sig
  type term_normaliser = term Same.operation
  val beta : term_normaliser
  val eta_short : term_normaliser
  val beta_eta_short : term_normaliser
  val dummy_var : term
  val dummy_vars : term_normaliser
end

structure Term_Normalisation : TERM_NORMALISATION =
struct

type term_normaliser = term Same.operation

val beta = Envir.norm_term_same Envir.init

local (*copied from envir.ML*)
fun decr_same lev (Bound i) = if i >= lev then Bound (i - 1) else raise Same.SAME
  | decr_same lev (Abs (a, T, body)) = Abs (a, T, decr_same (lev + 1) body)
  | decr_same lev (t $ u) =
      (decr_same lev t $ Same.commit (decr_same lev) u
        handle Same.SAME => t $ decr_same lev u)
  | decr_same _ _ = raise Same.SAME
fun eta_same (Abs (a, T, body)) =
    ((case eta_same body of
        body' as (f $ Bound 0) =>
          if Term.is_dependent f then Abs (a, T, body')
          else Same.commit (decr_same 0) f
     | body' => Abs (a, T, body')) handle Same.SAME =>
        (case body of
          f $ Bound 0 =>
            if Term.is_dependent f then raise Same.SAME
            else Same.commit (decr_same 0) f
        | _ => raise Same.SAME))
  | eta_same (t $ u) =
      (eta_same t $ Same.commit eta_same u
        handle Same.SAME => t $ eta_same u)
  | eta_same _ = raise Same.SAME
in
fun eta_short t = (if Term.could_eta_contract t then eta_same else Same.same) t
end

val beta_eta_short = Same.compose eta_short beta

val dummy_var = Var (("____dummy", 0), dummyT)
val dummy_vars = (Term.map_aterms (fn Var _ => dummy_var | x => x))

end

