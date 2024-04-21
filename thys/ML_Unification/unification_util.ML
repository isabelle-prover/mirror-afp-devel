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
  val pretty_unif_result : Proof.context -> (Envir.env * thm) -> Pretty.T

  val pretty_call_theory_match : Proof.context -> (term * term) -> Pretty.T
  val pretty_call_theory_unif : Proof.context -> (term * term) -> Pretty.T

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

  val inst_norm_term : Envir_Normalisation.term_normaliser -> Term_Normalisation.term_normaliser ->
    Envir_Normalisation.term_normaliser
  val inst_norm_term' : Unification_Base.normalisers -> Envir_Normalisation.term_normaliser
  val inst_norm_thm : Envir_Normalisation.thm_normaliser -> conv ->
    Envir_Normalisation.thm_normaliser
  val inst_norm_subgoal : Envir_Normalisation.thm_normaliser -> conv -> int ->
    Envir_Normalisation.thm_normaliser

  (* shared standard cases for unifiers *)
  val smash_tpairs_if_occurs : Proof.context -> term -> Envir.env * thm -> (Envir.env * thm) Seq.seq
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
structure UBase = Unification_Base
structure Show = SpecCheck_Show_Term

(* pretty-printing *)
val pretty_term = Show.term
val pretty_type = Show.typ

fun pretty_commas show = Pretty.block o Pretty.commas o map show
val pretty_types = pretty_commas o pretty_type
val pretty_terms = pretty_commas o pretty_term

val pretty_tyenv = Show.tyenv
val pretty_tenv = Show.tenv
val pretty_env = Show.env

fun pretty_unif_problem ctxt (t1, t2) =
  Pretty.block [pretty_term ctxt t1, Pretty.str " \<equiv>\<^sup>? " , pretty_term ctxt t2]

fun pretty_unif_result ctxt (env, thm) = Pretty.block [
    Pretty.str "Environment: ",
    pretty_env ctxt env,
    Pretty.fbrk,
    Pretty.str "Theorem: ",
    Thm.pretty_thm ctxt thm
  ]

fun pretty_call_theory_match ctxt pt = Pretty.block [
    Pretty.str "Calling theory matcher for ",
    pretty_unif_problem ctxt pt
  ]

fun pretty_call_theory_unif ctxt tp = Pretty.block [
    Pretty.str "Calling theory unifier for ",
    pretty_unif_problem ctxt tp
  ]

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
    raise UBase.UNIF)

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
    raise UBase.UNIF)

(* normalisers *)
val eta_short_norms_match = {
  (*Precondition: the matcher must already instantiate its theorem!*)
  inst_unif_thm = K o K I,
  inst_term = Norm.norm_term_match,
  inst_thm = Norm.norm_thm_match,
  norm_term = Term_Normalisation.eta_short,
  conv = Conversion_Util.eta_short_conv
}
val beta_eta_short_norms_match = {
  (*Precondition: the matcher must already normalise the types in its theorem!*)
  inst_unif_thm = (#inst_unif_thm eta_short_norms_match),
  inst_term = (#inst_term eta_short_norms_match),
  inst_thm = (#inst_thm eta_short_norms_match),
  norm_term = Term_Normalisation.beta_eta_short,
  conv = Conversion_Util.beta_eta_short_conv
}

val eta_short_norms_unif = {
  inst_unif_thm = Norm.norm_thm_unif,
  inst_term = Norm.norm_term_unif,
  inst_thm = Norm.norm_thm_unif,
  norm_term = Term_Normalisation.eta_short,
  conv = Conversion_Util.eta_short_conv
}
val beta_eta_short_norms_unif = {
  inst_unif_thm = (#inst_unif_thm eta_short_norms_unif),
  inst_term = (#inst_term eta_short_norms_unif),
  inst_thm = (#inst_thm eta_short_norms_unif),
  norm_term = Term_Normalisation.beta_eta_short,
  conv = Conversion_Util.beta_eta_short_conv
}

fun inst_norm_term inst_term norm_term = norm_term oo inst_term
fun inst_norm_term' norms = inst_norm_term (#inst_term norms) (#norm_term norms)
fun inst_norm_thm inst_thm conv = Conversion_Util.apply_thm_conv conv ooo inst_thm
fun inst_norm_subgoal inst_thm conv i = Conversion_Util.apply_subgoal_conv conv i ooo inst_thm

(* shared standard cases for unifiers *)
fun smash_tpairs_if_occurs ctxt t (env, thm) =
  let
    val tpairs = Thm.tpairs_of thm
    fun occs_t s = Logic.occs (t, s)
  in
    if exists (fn (t1, t2) => occs_t t1 orelse occs_t t2) tpairs
    then
      let
        (*in a perfect world, we would make the relevant tpairs of the theorem
          equality premises that can be solved by an arbitrary solver;
          however, Isabelle's kernel only allows one to solve tpairs
          with the built-in higher-order (pattern) unifier.*)
        (*only the kernel HO-unifier may add flex-flex pairs -> safe to normalise wrt. unification*)
        val normed_thm = Norm.norm_thm_unif ctxt env thm
        val normed_tpairs = Thm.tpairs_of normed_thm
      in
        (*note: we need to use the same unifier and environment as Thm.flexflex_rule here so that
          the final environment and theorem agree*)
        Unify.smash_unifiers (Context.Proof ctxt) normed_tpairs
          (Envir.empty (Thm.maxidx_of normed_thm))
        |> Seq.maps (fn smash_env =>
          (let val new_env = Envir.merge (smash_env, env)
          in Thm.flexflex_rule (SOME ctxt) normed_thm |> Seq.map (pair new_env) end)
          handle Vartab.DUP _ => (@{log Logger.INFO} ctxt
            (fn _ => Pretty.block [
                Pretty.str"Failed to merge environment for smashed tpairs and environment created by flexflex_rule: ",
                pretty_unif_result ctxt (env, thm)
              ]|> Pretty.string_of);
            Seq.empty))
      end
    else Seq.single (env, thm)
  end

fun abstract_abstract norm_term_type unify binders ctxt name T tbp =
  let
    val (binder as (_, bvar), ctxt') = Binders.fix_binder (name, T) ctxt
    fun norm_abstract (env, thm) =
      let fun norm_bvar env = norm_term_type (Envir.type_env env) bvar
      in
        smash_tpairs_if_occurs ctxt' (norm_bvar env) (env, thm)
        |> Seq.map_filter (fn (env, thm) =>
          UBase.abstract_rule ctxt' name (Thm.cterm_of ctxt' (norm_bvar env)) thm
          |> Option.map (pair env))
      end
  in unify (binder :: binders) ctxt' tbp #> Seq.maps norm_abstract end

fun rigid_rigid norm_term_type unify_types ctxt s (nt, Tt) env =
  let val (ns, Ts) = (if is_Const s then dest_Const else dest_Free) s
  in
    if ns = nt then
      let val (env' as Envir.Envir {tyenv,...}) = unify_types ctxt (Ts, Tt) env
      in
        (env', UBase.reflexive_term ctxt (norm_term_type tyenv s))
        |> Seq.single
      end
    else Seq.empty
  end

fun bound_bound binders ctxt (i, j) =
  if i = j
  then Binders.nth_binder_data binders i |> UBase.reflexive_term ctxt |> Seq.single
  else Seq.empty

fun comb_comb norm_thm_types unify ctxt (f, x) (g, y) env =
  let
    val unif = unify ctxt
    val env_thmq = unif (f, g) env
      |> Seq.maps (fn (env, thm_fg) => unif (x, y) env |> Seq.map (apsnd (pair thm_fg)))
    fun combine (env, thmp) =
      (*normalise types for the combination theorem to succeed*)
      apply2 (norm_thm_types ctxt env) thmp
      |> uncurry UBase.combination
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
        val norm_thm_types = norm_thm_types ctxt env_res
        fun norm_combine thm_arg thm = norm_thm_types thm_arg |> UBase.combination thm
      in (env_res, fold_rev norm_combine arg_thms (norm_thm_types thmh)) end
  in Seq.maps (fn (env, thmh) => unif_args env |> Seq.map (combine thmh)) env_thmhq end)
  handle ListPair.UnequalLengths => Seq.empty

fun strip_comb_strip_comb norm_thm_types unify binders ctxt (sh, th) (ss, ts) =
  unify binders ctxt (sh, th)
  #> args_args norm_thm_types (unify binders) ctxt (ss, ts)


(* logging *)

fun log_unif_result ctxt _ res =
  @{log Logger.INFO} ctxt (fn _ => pretty_unif_result ctxt res |> Pretty.string_of)

fun log_unif_results ctxt tp unify =
  let val res = unify ctxt tp (empty_envir tp) |> Seq.list_of
  in fold (log_unif_result ctxt tp #> K) res () end

fun log_unif_results' limit ctxt tp unify =
  let val res = unify ctxt tp (empty_envir tp) |> Seq.take limit |> Seq.list_of
  in fold (log_unif_result ctxt tp #> K) res () end

end

