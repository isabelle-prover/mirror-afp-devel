(*  Title:      ML_Unification/unification_util.ML
    Author:     Kevin Kappelmann

Utilities used for e-unifications.
*)
signature UNIFICATION_UTIL =
sig
  include HAS_LOGGER

  (* pretty-printing *)
  val pretty_types : Proof.context -> typ list -> Pretty.T
  val pretty_terms : Proof.context -> term list -> Pretty.T

  val pretty_tyenv : Proof.context -> Type.tyenv -> Pretty.T
  val pretty_tenv : Proof.context -> Envir.tenv -> Pretty.T
  val pretty_env : Proof.context -> Envir.env -> Pretty.T

  val pretty_unif_problem : Proof.context -> (term * term) -> Pretty.T

  (* terms and environments *)
  val maxidx_of_terms : term list -> int
  (*returns empty environment with maxidx set to maximum of given terms*)
  val empty_envir : term * term -> Envir.env

  (* type unification *)

  (*raises Unification_Base.UNIF on failure*)
  val unify_types : Unification_Base.type_unifier
  (*raises Unification_Base.UNIF on failure*)
  val match_types : Unification_Base.type_matcher

  (* normalisers *)
  val eta_short_norms_match : Unification_Base.normalisers
  val beta_eta_short_norms_match : Unification_Base.normalisers
  val eta_short_norms_unif : Unification_Base.normalisers
  val beta_eta_short_norms_unif : Unification_Base.normalisers

  (* shared standard cases for unifiers *)
  val abstract_abstract : Envir_Normalisation.term_type_normaliser -> Unification_Base.unifier ->
    term Binders.binders -> Proof.context -> string -> typ ->
    (term * term) -> Envir.env -> (Envir.env * thm) Seq.seq
  (*raises UNIF if types do not unify*)
  val rigid_rigid : Envir_Normalisation.term_type_normaliser -> Unification_Base.type_unifier ->
    Proof.context -> term -> (string * typ) -> Envir.env -> (Envir.env * thm) Seq.seq
  val bound_bound : term Binders.binders -> Proof.context -> (int * int) ->
    thm Seq.seq
  val comb_comb : Envir_Normalisation.thm_type_normaliser -> Unification_Base.closed_unifier ->
    Proof.context -> (term * term) -> (term * term) -> Envir.env -> (Envir.env * thm) Seq.seq
  val args_args : Envir_Normalisation.thm_type_normaliser -> Unification_Base.closed_unifier ->
    Proof.context -> (term list * term list) -> (Envir.env * thm) Seq.seq -> (Envir.env * thm) Seq.seq
  val strip_comb_strip_comb : Envir_Normalisation.thm_type_normaliser -> Unification_Base.unifier ->
    term Binders.binders -> Proof.context -> (term * term) ->
    (term list * term list) -> Envir.env -> (Envir.env * thm) Seq.seq

  (* logging *)
  val log_unif_result : Proof.context -> term * term -> Envir.env * thm -> unit
  val log_unif_results : Proof.context -> term * term -> Unification_Base.closed_unifier -> unit
  val log_unif_results' : int -> Proof.context  -> term * term -> Unification_Base.closed_unifier -> unit

end

structure Unification_Util : UNIFICATION_UTIL =
struct

val logger = Logger.setup_new_logger Unification_Base.logger "Util"

structure Norm = Envir_Normalisation

(* pretty-printing *)
local
val pretty_term = Syntax.pretty_term
val pretty_type = Syntax.pretty_typ

fun pretty_env_aux show_entry =
  Vartab.dest
  #> map show_entry
  #> Pretty.list "[" "]"

fun pretty_env_entry show (s, t) = Pretty.block [show s, Pretty.str " := ", show t]

val pretty_record =
  map (fn (key, entry) => Pretty.block [Pretty.str key, Pretty.str "=", entry])
  #> Pretty.enum "," "{" "}"
in

fun pretty_types ctxt = Pretty.block o Pretty.commas o map (pretty_type ctxt)
fun pretty_terms ctxt = Pretty.block o Pretty.commas o map (pretty_term ctxt)

fun pretty_tyenv ctxt =
  let
    val show_entry = pretty_env_entry (pretty_type ctxt)
    fun get_typs (v, (s, T)) = (TVar (v, s), T)
  in pretty_env_aux (show_entry o get_typs) end

fun pretty_tenv ctxt =
  let
    val show_entry = pretty_env_entry (pretty_term ctxt)
    fun get_trms (v, (T, t)) = (Var (v, T), t)
  in pretty_env_aux (show_entry o get_trms) end

fun pretty_env ctxt (Envir.Envir {maxidx, tyenv, tenv}) =
  pretty_record [
    ("maxidx", Pretty.str (string_of_int maxidx)),
    ("tyenv", pretty_tyenv ctxt tyenv),
    ("tenv", pretty_tenv ctxt tenv)
  ]

end

fun pretty_unif_problem ctxt (t1, t2) =
  Pretty.block [pretty_terms ctxt [t1], Pretty.str " \<equiv>\<^sup>? " , pretty_terms ctxt [t2]]

(* terms and environments *)
fun maxidx_of_terms ts = fold (Integer.max o maxidx_of_term) ts ~1

fun empty_envir (t1, t2) = Envir.empty (maxidx_of_terms [t1, t2])

(* type unification *)

fun match_types ctxt (T, U) (env as Envir.Envir {maxidx, tenv, tyenv}) =
  (if pointer_eq (T, U) then env
  else
    let val tyenv' = Sign.typ_match (Proof_Context.theory_of ctxt) (T, U) tyenv
    in Envir.Envir {maxidx = maxidx, tenv = tenv, tyenv = tyenv'} end)
  handle Type.TYPE_MATCH =>
    (@{log Logger.DEBUG} ctxt
      (fn _ => Pretty.block [
          Pretty.str "Failed to match types ",
          pretty_types ctxt [Envir_Normalisation.norm_type_match tyenv T, U]
        ] |> Pretty.string_of);
    raise Unification_Base.UNIF)

fun unify_types ctxt (T, U) (env as Envir.Envir {maxidx, tenv, tyenv}) =
  (if pointer_eq (T, U) then env
  else
    let val (tyenv', maxidx') =
      Sign.typ_unify (Proof_Context.theory_of ctxt) (T, U) (tyenv, maxidx)
    in Envir.Envir {maxidx = maxidx', tenv = tenv, tyenv = tyenv'} end)
  handle Type.TUNIFY =>
    (@{log Logger.DEBUG} ctxt
      (fn _ => Pretty.block [
          Pretty.str "Failed to unify types ",
          pretty_types ctxt (map (Envir_Normalisation.norm_type_unif tyenv) [T, U])
        ] |> Pretty.string_of);
    raise Unification_Base.UNIF)

(* normalisers *)
val eta_short_norms_match = {
  (*Precondition: the matcher must already normalise the types in its theorem!*)
  norm_unif_thm = Norm.eta_short_norm_thm (K I) Norm.eta_short_norm_term_match,
  norm_thm = Norm.eta_short_norm_thm_match,
  norm_term = Norm.eta_short_norm_term_match
}
val beta_eta_short_norms_match = {
  (*Precondition: the matcher must already normalise the types in its theorem!*)
  norm_unif_thm = Norm.beta_eta_short_norm_thm (K I) Norm.beta_eta_short_norm_term_match,
  norm_thm = Norm.beta_eta_short_norm_thm_match,
  norm_term = Norm.beta_eta_short_norm_term_match
}
val eta_short_norms_unif = {
  norm_unif_thm = Norm.eta_short_norm_thm_unif,
  norm_thm = Norm.eta_short_norm_thm_unif,
  norm_term = Norm.eta_short_norm_term_unif
}
val beta_eta_short_norms_unif = {
  norm_unif_thm = Norm.beta_eta_short_norm_thm_unif,
  norm_thm = Norm.beta_eta_short_norm_thm_unif,
  norm_term = Norm.beta_eta_short_norm_term_unif
}

(* shared standard cases for unifiers *)

fun abstract_abstract norm_term_type unify binders ctxt name T tbp =
  let
    val (binder as (_, bvar), ctxt') = Binders.fix_binder (name, T) ctxt
    fun norm_abstract (Envir.Envir {tyenv,...}) thm =
      let val bvar' = norm_term_type tyenv bvar
      in Unification_Base.abstract_rule name (Thm.cterm_of ctxt' bvar') thm end
  in
    unify (binder :: binders) ctxt' tbp
    #> Seq.map (fn (env, thm) => (env, norm_abstract env thm))
  end

fun rigid_rigid norm_term_type unify_types ctxt s (nt, Tt) env =
  let val (ns, Ts) = (if is_Const s then dest_Const else dest_Free) s
  in
    if ns = nt then
      let val (env' as Envir.Envir {tyenv,...}) = unify_types ctxt (Ts, Tt) env
      in
        (env', Unification_Base.reflexive_term ctxt (norm_term_type tyenv s))
        |> Seq.single
      end
    else Seq.empty
  end

fun bound_bound binders ctxt (i, j) =
  if i = j
  then Binders.nth_binder_data binders i |> Unification_Base.reflexive_term ctxt |> Seq.single
  else Seq.empty

fun comb_comb norm_thm_types unify ctxt (f, x) (g, y) env =
  let
    val unif' = unify ctxt
    val env_thmq = unif' (f, g) env
      |> Seq.maps (fn (env, thm_fg) => unif' (x, y) env |> Seq.map (apsnd (pair thm_fg)))
    fun combine (env, thmp) =
      (*normalise types for the combination theorem to succeed*)
      apply2 (norm_thm_types ctxt env) thmp
      |> uncurry Unification_Base.combination
      |> pair env
  in Seq.map combine env_thmq end

fun args_args norm_thm_types unify ctxt (ss, ts) env_thmhq =
  (let
    val args = ss ~~ ts
    fun unif_arg tp = Seq.maps
      (fn (env, thms) => unify ctxt tp env |> Seq.map (apsnd (fn thm => thm :: thms)))
    fun unif_args env = fold unif_arg args (Seq.single (env, []))
    (*combine the theorems*)
    fun combine thmh (env_res, arg_thms) =
      let
        (*normalise types for the combination theorem to succeed*)
        val norm_thm_types' = norm_thm_types ctxt env_res
        fun norm_combine thm_arg thm = norm_thm_types' thm_arg |> Unification_Base.combination thm
      in (env_res, fold_rev norm_combine arg_thms (norm_thm_types' thmh)) end
  in Seq.maps (fn (env, thmh) => unif_args env |> Seq.map (combine thmh)) env_thmhq end)
  handle ListPair.UnequalLengths => Seq.empty

fun strip_comb_strip_comb norm_thm_types unify binders ctxt (sh, th) (ss, ts) =
  unify binders ctxt (sh, th)
  #> args_args norm_thm_types (unify binders) ctxt (ss, ts)

(* logging *)

fun log_unif_result ctxt _ (env, thm) =
  @{log Logger.INFO} ctxt (fn _ => Pretty.block [
    Pretty.str "Environment: ",
    pretty_env ctxt env,
    Pretty.fbrk,
    Pretty.str "Theorem: ",
    Thm.pretty_thm ctxt thm
  ] |> Pretty.string_of)

fun log_unif_results ctxt tp unify =
  let val res = unify ctxt tp (empty_envir tp) |> Seq.list_of
  in fold (log_unif_result ctxt tp #> K) res () end

fun log_unif_results' limit ctxt tp unify =
  let val res = unify ctxt tp (empty_envir tp) |> Seq.take limit |> Seq.list_of
  in fold (log_unif_result ctxt tp #> K) res () end

end

