(*  Title:      ML_Unification/binders.ML
    Author:     Kevin Kappelmann

Binders with De Bruijn indexing.

When we traverse abstractions, e.g. in unification algorithms, we store a binder as
((name, typ), fresh Free variable). The fresh free variable can be used as a replacement for
the corresponding bound variable, e.g. when one has to create a reflexivity theorem for the
binder.
*)
signature BINDERS =
sig
  type 'a binder = (string * typ) * 'a
  type 'a binders = ('a binder) list
  (*add_binders bs1 bs2 adds binders bs1 to binders bs2*)
  val add_binders : 'a binders -> 'a binders -> 'a binders
  val fix_binders : (string * typ) list -> Proof.context -> term binders * Proof.context
  val fix_binder : (string * typ) -> Proof.context -> term binder * Proof.context
  (*returns types of binders*)
  val binder_types : 'a binders -> typ list
  (*returns free variable corresponding to the given binder*)
  val nth_binder_data : 'a binders -> int -> 'a
  (*replaces all binders by their corresponding free variable in the given term*)
  val replace_binders : term binders -> term -> term
  (*replaces all free variables that correspond to a binder by their binder*)
  val replace_frees : term binders -> term -> term
  (*normalises types and associated free variables*)
  val norm_binders : Term_Normalisation.term_normaliser -> term binders -> term binders
end

structure Binders : BINDERS =
struct

type 'a binder = (string * typ) * 'a
type 'a binders = ('a binder) list

fun add_binders binders1 binders2 = binders1 @ binders2

fun fix_binders nTs ctxt =
  Variable.variant_fixes (map fst nTs) ctxt
  |>> map2 (fn (n, T) => fn n' => ((n, T), Free (n', T))) nTs

val fix_binder = yield_singleton fix_binders

fun binder_types binders = map (snd o fst) binders

fun nth_binder_data binders = snd o nth binders

fun replace_binders binders t = let val bvars = map snd binders
  in subst_bounds (bvars, t) end

fun replace_frees binders =
  let val subst = General_Util.fold_rev_index (fn (i, (_, free)) => cons (free, Bound i)) binders []
  in subst_free subst end

fun norm_binders norm =
  map (fn ((n, _), t) => let val t' = norm t in ((n, snd (dest_Free t')), t') end)

end
