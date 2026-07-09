(*  Title:      ML_Unification/unification_util.ML
    Author:     Kevin Kappelmann

Utilities used for E-unifications.
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

  val show_unif_problem_skolem : bool Config.T
  val pretty_unif_problem : term Binders.binders -> Proof.context -> (term * term) -> Pretty.T
  val pretty_unif_result : Proof.context -> (Envir.env * thm) -> Pretty.T

  val pretty_call_theory_match : term Binders.binders -> Proof.context -> (term * term) -> Pretty.T
  val pretty_call_theory_unif : term Binders.binders -> Proof.context -> (term * term) -> Pretty.T

  (* terms and environments *)
  val maxidx_of_terms : term list -> int
  (*returns empty environment with maxidx set to maximum of given terms*)
  val empty_envir : term * term -> Envir.env
  val update_maxidx_envir : int -> Envir.env -> Envir.env
  (*returns type and flag indicating whether the type is already normalised*)
  val fastype_match_lhs : Envir.env -> typ list -> term -> typ * bool
  val fastype_match_rhs : typ list -> term -> typ
  val fastype_unif : Envir.env -> typ list -> term -> typ

  (* type unification *)
  val match_types : Unification_Base.type_matcher
  val unify_types : Unification_Base.type_unifier
  val match_term_types : Unification_Base.term_type_matcher
  val unify_term_types : Unification_Base.term_type_unifier

  (* normalisers *)
  val beta_norms_match : Unification_Base.normalisers
  val eta_short_norms_match : Unification_Base.normalisers
  val beta_eta_short_norms_match : Unification_Base.normalisers
  val beta_norms_match_type_unify : Unification_Base.normalisers
  val eta_short_norms_match_type_unify : Unification_Base.normalisers
  val beta_eta_short_norms_match_type_unify : Unification_Base.normalisers
  val beta_norms_unif : Unification_Base.normalisers
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
  val gen_abstract : Envir_Normalisation.term_type_normaliser -> Unification_Base.unifier ->
    term Binders.binders -> Proof.context -> string -> typ ->
    (term * term) -> Envir.env -> (Envir.env * thm) Seq.seq
  val abstract_abstract : Envir_Normalisation.term_type_normaliser -> Unification_Base.unifier ->
    term Binders.binders -> Proof.context -> string * typ * term -> string * typ * term ->
    Envir.env -> (Envir.env * thm) Seq.seq
  val abstract_left : Envir_Normalisation.term_type_normaliser -> Unification_Base.unifier ->
    term Binders.binders -> Proof.context -> string * typ * term -> term ->
    Envir.env -> (Envir.env * thm) Seq.seq
  val abstract_right : Envir_Normalisation.term_type_normaliser -> Unification_Base.unifier ->
    term Binders.binders -> Proof.context -> term -> string * typ * term ->
    Envir.env -> (Envir.env * thm) Seq.seq
  val rigid_rigid : Unification_Base.type_unifier -> Proof.context -> (string * typ) -> term ->
    Envir.env -> (Envir.env * thm) Seq.seq
  val bound_bound : term Binders.binders -> Proof.context -> (int * int) ->
    thm Seq.seq
  val comb_comb : Envir_Normalisation.thm_type_normaliser -> Unification_Base.closed_unifier ->
    Proof.context -> (term * term) -> (term * term) -> Envir.env -> (Envir.env * thm) Seq.seq
  val args_args : Envir_Normalisation.thm_type_normaliser -> Unification_Base.closed_unifier ->
    Proof.context -> (term list * term list) -> (Envir.env * thm) Seq.seq -> (Envir.env * thm) Seq.seq
  val strip_comb_strip_comb : Envir_Normalisation.thm_type_normaliser -> Unification_Base.unifier ->
    term Binders.binders -> Proof.context -> (term * term) ->
    (term list * term list) -> Envir.env -> (Envir.env * thm) Seq.seq

  (*matches application "?f s1 ... sn" with t by abstracting s1,...,sn in t, resulting
  in \<lambda>x1 ... xn. t', and assigning ?f to it provided that it contains no loose bound variables*)
  (*precondition: types are matched and types paired with si normalised*)
  val match_var_args : (term * term -> bool) -> (indexname * typ) * (term * typ) list -> term ->
    Envir.env -> Envir.env option
  (*given target terms [t1,...,tn], lowers applications "?fi s1 ... s{mi}" to "?fi' t1 ... tn"
  using match_var_args*)
  (*precondition: types paired with si are normalised*)
  val lower_var_args : (term * term -> bool) -> (term * typ) list ->
    ((indexname * typ) * (term * typ) list) list -> Envir.env -> Envir.env option

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

val show_unif_problem_skolem = Attrib.setup_config_bool @{binding "show_unif_problem_skolem"} (K true)

fun pretty_unif_problem binders ctxt (t1, t2) =
  let val norm = Config.get ctxt show_unif_problem_skolem ? Binders.replace_binders binders
  in Pretty.breaks [
      pretty_term ctxt (norm t1),
      Pretty.str "\<equiv>\<^sup>?",
      pretty_term ctxt (norm t2)
    ] |> Pretty.block
  end

fun pretty_unif_result ctxt (env, thm) = Pretty.fbreaks [
    Pretty.block [Pretty.str "Environment: ", pretty_env ctxt env],
    Pretty.block [Pretty.str "Theorem: ", Thm.pretty_thm ctxt thm]
  ] |> Pretty.block

fun pretty_call_theory_match binders ctxt pt = Pretty.block [
    Pretty.str "Calling theory matcher for ",
    pretty_unif_problem binders ctxt pt
  ]

fun pretty_call_theory_unif binders ctxt tp = Pretty.block [
    Pretty.str "Calling theory unifier for ",
    pretty_unif_problem binders ctxt tp
  ]

(* terms and environments *)
fun maxidx_of_terms ts = fold (Integer.max o maxidx_of_term) ts ~1

fun empty_envir (t1, t2) = Envir.empty (maxidx_of_terms [t1, t2])
fun update_maxidx_envir maxidx' (Envir.Envir {maxidx, tenv = tenv, tyenv = tyenv}) =
  Envir.Envir {maxidx = Integer.max maxidx maxidx', tenv = tenv, tyenv = tyenv}

(*adapted from envir.ML*)
fun fastype_match_lhs (Envir.Envir {tyenv, ...}) =
  let
    val pure = rpair false
    val normed = rpair true
    fun err_app f u = raise TERM ("fastype_match_lhs: expected function type", [f $ u])
    fun fast Ts (f $ u) = (case fast Ts f |> apfst (`(try range_type)) of
          ((NONE, T), false) => (case try (Norm.norm_type_match tyenv #> range_type) T of
              SOME T' => normed T'
            | NONE => err_app f u)
        | ((NONE, _), true) => err_app f u
        | ((SOME T, _), normed) => (T, normed))
      | fast _ (Const (_, T)) = pure T
      | fast _ (Free (_, T)) = pure T
      | fast Ts (Bound i) = (normed (nth Ts i) (*precondition: bound type variables are normalised*)
          handle General.Subscript => raise TERM ("fastype_match_lhs: Bound", [Bound i]))
      | fast _ (Var (_, T)) = pure T
      | fast Ts (Abs (_, T, u)) = fast (T :: Ts) u |> apfst (fn T' => T --> T')
  in fast end
val fastype_match_rhs = curry fastype_of1
val fastype_unif = Envir.fastype

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
          pretty_types ctxt [Same.commit (Envir_Normalisation.norm_type_match tyenv) T, U]
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
          pretty_types ctxt (map (Same.commit (Envir_Normalisation.norm_type_unif tyenv)) [T, U])
        ] |> Pretty.string_of);
    raise UBase.UNIF)

fun match_term_types Ts ctxt (p, t) env =
  let
    val (pT, normed) = fastype_match_lhs env Ts p
    val tT = fastype_match_rhs Ts t
  in
    if normed then if pT = tT then env else raise UBase.UNIF
    else match_types ctxt (pT, tT) env
  end
fun unify_term_types Ts ctxt st env = unify_types ctxt (apply2 (fastype_unif env Ts) st) env

(* normalisers *)
val beta_norms_match = {
  (*precondition: the matcher must produce a normalised theorem*)
  inst_unif_thm = K o K I,
  inst_term = Norm.norm_term_match,
  inst_thm = Norm.norm_thm_match,
  norm_term = Term_Normalisation.beta,
  conv = Conversion_Util.beta_conv
}
val eta_short_norms_match = {
  (*precondition: the matcher must produce a normalised theorem*)
  inst_unif_thm = #inst_unif_thm beta_norms_match,
  inst_term = #inst_term beta_norms_match,
  inst_thm = #inst_thm beta_norms_match,
  norm_term = Term_Normalisation.eta_short,
  conv = Conversion_Util.eta_short_conv
}
val beta_eta_short_norms_match = {
  (*precondition: the matcher must produce a normalised theorem*)
  inst_unif_thm = #inst_unif_thm beta_norms_match,
  inst_term = #inst_term beta_norms_match,
  inst_thm = #inst_thm beta_norms_match,
  norm_term = Term_Normalisation.beta_eta_short,
  conv = Conversion_Util.beta_eta_short_conv
}
val beta_norms_match_type_unify =
  let val inst_term = Norm.gen_norm_term_match Norm.norm_type_unif
  in {
    inst_unif_thm = Norm.norm_thm_types_unif,
    inst_term = inst_term,
    inst_thm = Norm.norm_thm Norm.norm_type_unif inst_term,
    norm_term = #norm_term beta_norms_match,
    conv = #conv beta_norms_match}
  end
val eta_short_norms_match_type_unify = {
  inst_unif_thm = #inst_unif_thm beta_norms_match_type_unify,
  inst_term = #inst_term beta_norms_match_type_unify,
  inst_thm = #inst_thm beta_norms_match_type_unify,
  norm_term = #norm_term eta_short_norms_match,
  conv = #conv eta_short_norms_match
}
val beta_eta_short_norms_match_type_unify = {
  inst_unif_thm = #inst_unif_thm beta_norms_match_type_unify,
  inst_term = #inst_term beta_norms_match_type_unify,
  inst_thm = #inst_thm beta_norms_match_type_unify,
  norm_term = #norm_term beta_eta_short_norms_match,
  conv = #conv beta_eta_short_norms_match
}
val beta_norms_unif = {
  inst_unif_thm = Norm.norm_thm_unif,
  inst_term = Norm.norm_term_unif,
  inst_thm = Norm.norm_thm_unif,
  norm_term = #norm_term beta_norms_match,
  conv = #conv beta_norms_match
}
val eta_short_norms_unif = {
  inst_unif_thm = #inst_unif_thm beta_norms_unif,
  inst_term = #inst_term beta_norms_unif,
  inst_thm = #inst_thm beta_norms_unif,
  norm_term = #norm_term eta_short_norms_match,
  conv = #conv eta_short_norms_match
}
val beta_eta_short_norms_unif = {
  inst_unif_thm = #inst_unif_thm beta_norms_unif,
  inst_term = #inst_term beta_norms_unif,
  inst_thm = #inst_thm beta_norms_unif,
  norm_term = #norm_term beta_eta_short_norms_match,
  conv = #conv beta_eta_short_norms_match
}

fun inst_norm_term inst_term norm_term = Same.compose norm_term o inst_term
fun inst_norm_term' norms = inst_norm_term (#inst_term norms) (#norm_term norms)
fun inst_norm_thm inst_thm conv = Conversion_Util.apply_thm_conv conv ooo inst_thm
fun inst_norm_subgoal inst_thm conv i = Conversion_Util.apply_subgoal_conv conv i ooo inst_thm

(* shared standard cases for unifiers *)
fun smash_tpairs_if_occurs ctxt t (env, thm) = Seq.make (fn _ =>
  let
    val tpairs = Thm.tpairs_of thm
    fun occs_t s = Logic.occs (t, s)
  in
    (if exists (fn (t1, t2) => occs_t t1 orelse occs_t t2) tpairs
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
                Pretty.str "Failed to merge environment for smashed tpairs and environment created by flexflex_rule: ",
                pretty_unif_result ctxt (env, thm)
              ]|> Pretty.string_of);
            Seq.empty))
      end
    else Seq.single (env, thm))
    |> Seq.pull
  end)

fun gen_abstract norm_term_types unify binders ctxt name T tbp env = Seq.make (fn _ =>
  let
    val (binder as (_, bvar), ctxt') = Binders.fix_binder (name, T) ctxt
    fun norm_abstract (env, thm) =
      let fun norm_bvar env = Same.commit (norm_term_types (Envir.type_env env)) bvar
      in
        smash_tpairs_if_occurs ctxt' (norm_bvar env) (env, thm)
        |> Seq.map_filter (fn (env, thm) =>
          UBase.abstract_rule ctxt' name (Thm.cterm_of ctxt' (norm_bvar env)) thm
          |> Option.map (pair env))
      end
  in unify (binder :: binders) ctxt' tbp env |> Seq.maps norm_abstract |> Seq.pull end)

(*Note: in the following abs cases, we prefer to take the type of the right argument if available
so that it also works for matching*)
fun abstract_abstract norm_term_types unify binders ctxt (np, _, tp) (nt, Tt, tt) =
  let val name = if nt = "" then np else nt
  in gen_abstract norm_term_types unify binders ctxt name Tt (tp, tt) end

local fun eta_expand t = incr_boundvars 1 t $ Bound 0
in
fun abstract_left norm_term_types unify binders ctxt (np, Tp, tp) t env = env |>
  let val T = try (fastype_match_rhs (Binders.binder_types binders) #> domain_type) t
    (*returns NONE if type unification is used and a type in t got assigned to a function type*)
    |> the_default Tp
  in gen_abstract norm_term_types unify binders ctxt np T (tp, eta_expand t) end

fun abstract_right norm_term_types unify binders ctxt p (nt, Tt, tt) =
  gen_abstract norm_term_types unify binders ctxt nt Tt (eta_expand p, tt)
end

fun rigid_rigid unify_types ctxt (ns, Ts) t env = Seq.make (fn _ =>
  let val (nt, Tt) = (if is_Const t then dest_Const else dest_Free) t
  in
    if ns = nt then (unify_types ctxt (Ts, Tt) env, UBase.reflexive_term ctxt t)
      |> Seq.single |> Seq.pull
    else NONE
  end)

fun bound_bound binders ctxt (i, j) = Seq.make (fn _ => if i = j
  then Binders.nth_binder_data binders i |> UBase.reflexive_term ctxt |> Seq.single |> Seq.pull
  else NONE)

fun comb_comb norm_thm_types unify ctxt (f, x) (g, y) env = Seq.make (fn _ =>
  let
    val unif = unify ctxt
    val env_thmq = unif (f, g) env
      |> Seq.maps (fn (env, thm_fg) => unif (x, y) env |> Seq.map (apsnd (pair thm_fg)))
    fun combine (env, thmp) =
      (*normalise types for the combination theorem to succeed*)
      apply2 (norm_thm_types ctxt env) thmp
      |> uncurry UBase.combination
      |> pair env
  in Seq.map combine env_thmq |> Seq.pull end)

fun args_args norm_thm_types unify ctxt (ss, ts) env_thmhq = Seq.make (fn _ =>
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
  in Seq.maps (fn (env, thmh) => unif_args env |> Seq.map (combine thmh)) env_thmhq |> Seq.pull end)
  handle ListPair.UnequalLengths => NONE)

fun strip_comb_strip_comb norm_thm_types unify binders ctxt (sh, th) (ss, ts) env = Seq.make (fn _ =>
  unify binders ctxt (sh, th) env
  |> args_args norm_thm_types (unify binders) ctxt (ss, ts)
  |> Seq.pull)

fun match_var_args eq (f, tTs) t env =
  let val abst = fold_rev (curry (Term_Util.lambda eq) "") tTs t
  in if Term.is_open abst then NONE else SOME (Envir.update (f, abst) env) end

fun lower_var_args eq target_tTs =
  let
    val (target_ts, target_Ts) = split_list target_tTs
    fun run [] env = SOME env
      | run ((ftTs as (((n, _), T), tTs)) :: ftTss) env =
          let val (env, t) = (env, target_Ts ---> funpow (length tTs) range_type T)
            |> Envir.genvar n ||> (fn v => list_comb (v, target_ts))
          in match_var_args eq ftTs t env |> Option.mapPartial (run ftTss) end
  in run end

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

