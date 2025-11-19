(*  Title:      Zippy/zippy_goal_clusters.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTERS =
sig
  (*counting from 0 as is convention for indexing of datatypes*)
  type cluster_pos = int
  val init_cluster_pos : cluster_pos
  val pretty_cluster_pos : cluster_pos SpecCheck_Show.show
  (*counting from 1 as is convention for Isabelle goals*)
  type goal_pos = int
  val pretty_goal_pos : goal_pos SpecCheck_Show.show
  (*position of a state's goal in the created goal clusters*)
  type gcpos
  val get_gcpos_cluster : gcpos -> cluster_pos
  val get_gcpos_goal : gcpos -> goal_pos
  val mk_gcpos_index : goal_pos list list -> goal_pos -> gcpos
  val pretty_gcpos : gcpos SpecCheck_Show.show

  structure UF : IMPERATIVE_UNION_FIND
  (*meta variable equivalence class*)
  type mvar_eclass = (term, typ) Either.either UF.set
  val eq_opt_mvar_eclass: 'a UF.set option * 'a UF.set option -> bool
  val init_mvar_eclasses : term list -> mvar_eclass option list *
    (mvar_eclass Termtab.table * mvar_eclass Typtab.table)
  val group_mvar_eclasses : mvar_eclass option list -> (goal_pos * mvar_eclass option) list list
  val build_mvar_eclasses : term list -> (goal_pos * mvar_eclass option) list list *
    (mvar_eclass Termtab.table * mvar_eclass Typtab.table)

  type gclusters
  val pretty_gclusters : Proof.context -> gclusters SpecCheck_Show.show
  (*returns unaltered state*)
  type state = Zippy_Thm_State.state
  val get_state : gclusters -> state
  val get_thm : gclusters -> thm
  (*returns state where clusters are combined with Pure conjunctions (&&&)*)
  val get_clustered_state : gclusters -> state
  val get_cclusters : gclusters -> cterm list
  val get_clusters_goals : gclusters -> term list list
  val get_gcpos_index : gclusters -> goal_pos -> gcpos
  val get_nclusters : gclusters -> int
  (*returns clusters and associated equivalence classes for the state's goals, including their size*)
  val init : state -> gclusters * (goal_pos list * int) list

  val is_finished : gclusters -> bool
  val has_meta_vars : gclusters -> bool
  val meta_vars : gclusters -> Vars.set

  val finish_cluster_states : Proof.context -> state list -> gclusters -> state Seq.seq
  val finish_cluster_statesqs : Proof.context -> state Seq.seq list -> gclusters -> state Seq.seq
end

functor Zippy_Goal_Clusters(UF : IMPERATIVE_UNION_FIND) : ZIPPY_GOAL_CLUSTERS =
struct

structure UF = UF
structure GU = General_Util
structure TS = Zippy_Thm_State
structure Show = SpecCheck_Show_Base

type cluster_pos = int
val init_cluster_pos = 0
val pretty_cluster_pos = Show.int

type goal_pos = int
val pretty_goal_pos = Show.int

datatype gcpos = GCPos of {cluster : cluster_pos, goal : goal_pos}
fun gcpos cluster goal = GCPos {cluster = cluster, goal = goal}
fun get_gcpos_cluster (GCPos {cluster,...}) = cluster
fun get_gcpos_goal (GCPos {goal,...}) = goal

fun mk_gcpos_index mvar_eclasses = fold_index (fn (cpos, ps) => fold_index
    (fn (gpos, gpos_in) => General_Util.fun_update (equal gpos_in) (gcpos cpos (GU.succ gpos)))
    ps)
  mvar_eclasses (fn i => error (implode ["Goal position ", string_of_int i, " is out of bounds (1-",
    string_of_int (fold (length #> curry (op +)) mvar_eclasses 0), ")."]))

fun pretty_gcpos gcpos = Show.record [
    ("cluster", pretty_cluster_pos (get_gcpos_cluster gcpos)),
    ("goal", pretty_cluster_pos (get_gcpos_goal gcpos))
  ]

type mvar_eclass = (term, typ) Either.either UF.set
fun add_mvar_eclass goal index =
  let
    fun gen_merge constr lookup insert x (opt_mvar_eclass, index) =
      let
        val (mvar_eclass', index) = case lookup index x of
            NONE => let val mvar_eclass = UF.new (constr x)
              in (mvar_eclass, insert (K true) (x, mvar_eclass) index) end
          | SOME mvar_eclass => (mvar_eclass, index)
        val mvar_eclass = opt_mvar_eclass
          |> Option.map (fn mvar_eclass => (UF.union fst mvar_eclass mvar_eclass'; mvar_eclass))
          |> the_default mvar_eclass'
      in (SOME mvar_eclass, index) end
    val merge_term = gen_merge Either.Left Termtab.lookup Termtab.insert
    val merge_typ = gen_merge Either.Right Typtab.lookup Typtab.insert
    val merge_types = fold_atyps (fn v as TVar _ => merge_typ v | _ => I)
    fun merge t T (opt_mvar_eclass, (term_index, typ_index)) =
      (is_Var t ? merge_term t) (opt_mvar_eclass, term_index)
      |> (fn (opt_mvar_eclass, term_index) => merge_types T (opt_mvar_eclass, typ_index)
        |> apsnd (pair term_index))
    in fold_term_types merge goal (NONE, index) end
fun init_mvar_eclasses goals = fold_map add_mvar_eclass goals (Termtab.empty, Typtab.empty)

fun eq_opt_mvar_eclass (SOME mvar_eclass1, SOME mvar_eclass2) = UF.eq (mvar_eclass1, mvar_eclass2)
  | eq_opt_mvar_eclass _ = false

val group_mvar_eclasses = map_index (apfst GU.succ #> uncurry pair)
  #> Library.partition_eq (eq_snd eq_opt_mvar_eclass)
val build_mvar_eclasses = init_mvar_eclasses #> apfst group_mvar_eclasses

fun rearrange_mvar_eclasses_state mvar_eclasses = Drule.rearrange_prems (flat mvar_eclasses |> map GU.pred)
val mk_conj_list_state = fold (fn n => TS.mk_conj n #> Drule.rotate_prems 1)

type state = Zippy_Thm_State.state

datatype gclusters = GClusters of {
    state : state,
    clustered_state : state,
    gcpos_index : goal_pos -> gcpos,
    nclusters : int
  }

fun get_state (GClusters {state,...}) = state
fun get_clustered_state (GClusters {clustered_state,...}) = clustered_state
fun get_gcpos_index (GClusters {gcpos_index,...}) = gcpos_index
fun get_nclusters (GClusters {nclusters,...}) = nclusters

val get_thm = get_state #> TS.get_thm

fun pretty_gclusters ctxt gclusters = get_clustered_state gclusters |> TS.pretty ctxt

val get_cclusters = get_clustered_state #> TS.unprotect_prems #> Thm.cprems_of
val get_clusters_goals = get_cclusters #> map (Thm.term_of #> Logic.dest_conjunctions)

fun init state =
  (if TS.has_meta_vars state
  then Thm.prems_of state |> build_mvar_eclasses |> fst
    |> map (fn mvar_eclass => fold_map (apfst fst #> apsnd GU.succ |> curry) mvar_eclass 0)
  else Thm.nprems_of state |> map_range (GU.succ #> single #> rpair 1))
  |> `(fn mvss =>
    let
      val (mvar_eclasses, ss) = split_list mvss
      val clustered_state = rearrange_mvar_eclasses_state mvar_eclasses state
        |> mk_conj_list_state ss
        |> TS.protect_prems
      val gcpos_index = mk_gcpos_index mvar_eclasses
    in
      GClusters {state = state, clustered_state = clustered_state, gcpos_index = gcpos_index,
        nclusters = length mvar_eclasses}
    end)

val is_finished = get_state #> TS.is_finished
val has_meta_vars = get_state #> TS.has_meta_vars
val meta_vars = get_state #> TS.meta_vars

fun finish_cluster_state_tac cluster_state ctxt =
  let
    val norms = Mixed_Unification.norms_first_higherp_match
    val match = Mixed_Unification.first_higherp_e_match Unification_Combinator.fail_match
      |> Unification_Combinator.flip_match
  in
    Unify_Resolve_Base.unify_resolve_tac norms match cluster_state ctxt
    (*Note: above matcher and match in Thm.bicompose are incomplete. As a last resort, we use the
    unifier, though in principle, one only ought to match the cluster state*)
    ORELSE' let fun compose match = PRIMSEQ o Thm.bicompose (SOME ctxt)
        {flatten = true, match = match, incremented = false}
        (false, cluster_state, Thm.nprems_of cluster_state)
      in
        compose true
        ORELSE' compose false
        ORELSE' (fn i => fn state =>
          (warning (Pretty.breaks [
            Pretty.str "Failed to resolve cluster state",
            Thm.pretty_thm ctxt cluster_state,
            Pretty.str ("with subgoal " ^ string_of_int i ^ " from goal clusters state"),
            Thm.pretty_thm ctxt state,
            Pretty.str "This could be caused due to incompleteness of Thm.bicompose and/or unwanted flexflex pairs."
          ] |> Pretty.block0 |> Pretty.string_of);
          no_tac state))
      end
  end

fun finish_cluster_states ctxt cluster_states = get_clustered_state
  #> HEADGOAL (RANGE (List.map (fn cluster_state => finish_cluster_state_tac cluster_state ctxt)
    cluster_states))

local
  structure LTS = \<^eval>\<open>sfx_ParaT_nargs "Traversable"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "List_Traversable_Trans"\<close>(
      \<^eval>\<open>sfx_ParaT_nargs "Identity_Traversable"\<close>(\<^eval>\<open>sfx_ParaT_nargs "Seq_Monad"\<close>)))
in
fun finish_cluster_statesqs ctxt statesqs gcs =
  LTS.sequence statesqs |> Seq.maps (General_Util.flip (finish_cluster_states ctxt) gcs)
end

end

structure Standard_Zippy_Goal_Clusters = Zippy_Goal_Clusters(Imperative_Union_Find)