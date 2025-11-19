(*  Title:      Zippy/zippy_lists_goals_results_top_meta_vars_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_GOALS_RESULTS_TOP_META_VARS_MIXIN =
sig
  include ZIPPY_GOALS_RESULTS_TOP_META_VARS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  structure Co : ZIPPY_COROUTINE_MIXIN_BASE
  sharing type Co.M.t = M.t

  val mk_statesq :
    (*enumerate gcluster children of given gcluster*)
    (@{ParaT_args} @{AllT_args} GCluster.L.container,
      (@{ParaT_args} unit, @{AllT_args} GClusters.L.container) Co.Co.coroutine) morph ->
    Proof.context -> (@{ParaT_args} @{AllT_args} GClusters.L.container,
      GClusters.GCS.state Seq.seq) morph

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  type @{AllT_args} zipper{i}\<close>\<close>
  (*depth-first postorder enumeration of zipper1 children*)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val enum_df_post_children{i} : (unit -> @{ParaT_args encl: "(" ")"} Co.ME.exn) ->
    (@{ParaT_args} @{AllT_args} zipper{i},
      (@{ParaT_args} unit, @{AllT_args} zipper1) Co.Co.coroutine) morph\<close> start: 2\<close>

  val mk_statesq_df_post : (unit -> @{ParaT_args encl: "(" ")"} Co.ME.exn) ->
    Proof.context -> (@{ParaT_args} @{AllT_args} GClusters.L.container,
      GClusters.GCS.state  Seq.seq) morph
end

functor Zippy_Lists_Goals_Results_Top_Meta_Vars_Mixin(
    structure Z : ZIPPY_LISTS
    structure Goals_Results_Top_Meta_Vars : ZIPPY_GOALS_RESULTS_TOP_META_VARS_MIXIN_BASE
    sharing type Goals_Results_Top_Meta_Vars.GClusters.L.container = Z.Z1.zipper
    sharing type Goals_Results_Top_Meta_Vars.GCluster.L.container = Z.Z2.zipper
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t =Z.M.t
    structure Log_LGoals : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_LISTS_GOALS_RESULTS_TOP_META_VARS_MIXIN =
struct

open Z Goals_Results_Top_Meta_Vars
structure MU = Zippy_Monad_Util(M); open MU
structure ZE = Zippy_Enum_Mixin(Z)
structure Exn = Zippy_Exception_Mixin(Co)
structure GCluster = Zippy_Goal_Cluster_Mixin(GCluster)
structure GCluster_Results = Zippy_Goal_Results_Mixin(GCluster_Results)
structure LGoals = Zippy_Lists_Goals_Mixin(structure Z = Z
  structure Goals = Goals_Results_Top_Meta_Vars; structure Ctxt = Ctxt; structure Log = Log_LGoals)
structure TMV = Zippy_Goal_Results_Top_Meta_Vars_Mixin(
  structure Z = Z
  structure Goal_Results_Top_Meta_Vars = Zippy_Goal_Results_Top_Meta_Vars_Mixin_Base(
    structure Results = GCluster_Results; structure Top_Meta_Vars = Top_Meta_Vars))

local open SC A Mo Co Exn
  structure LTSM = \<^eval>\<open>sfx_ParaT_nargs "Traversable"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "List_Traversable_Trans"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Identity_Traversable"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Seq_Applicative_Trans"\<close>(M))))
  val empty = Seq.empty
  fun append x y = Seq.append x y
  val single = Seq.single
  val maps = Seq.maps
in
fun mk_statesq enum_gclusters_children ctxt z = let val gcs = GClusters.L.getter z
  in
    if GClusters.GCS.is_finished gcs
    then pure (single (GClusters.GCS.get_state gcs))
    else AE.catch'
      (get_gcluster_list_statesq enum_gclusters_children ctxt
      >>> arr (maps (fn gcluster_states =>
        GClusters.GCS.finish_cluster_states ctxt gcluster_states gcs)))
      (K empty) z
  end
and get_gcluster_list_statesq enum_gclusters_children ctxt =
  Down1.morph >>> LGoals.gcluster_list >>> mk_statesq_gcluster_list enum_gclusters_children ctxt
and mk_statesq_gcluster_list enum_gclusters_children ctxt =
  LTSM.traverse (mk_statesq_gcluster enum_gclusters_children ctxt)
and mk_statesq_gcluster enum_gclusters_children ctxt z = z |>
  (if TMV.may_take_more_results z
  then
    AE.catch'
      (enum_gclusters_children
      >>> (fn co => Co.repeat_step_res (K ())
        (first (mk_statesq enum_gclusters_children ctxt)
          >>> arr (fn (s, r) => append r s |> Co.continue))
        co ((), empty))
      >>> arr (Co.dest_res #> snd))
      (K empty)
    >>> arr (fn gcs_statesq => GCluster.get_state z |> single |> append gcs_statesq)
  else arr GCluster_Results.get_states)

local
  fun gen_enum_zippers mk_exn down enum_children enum_child = down
    >>> (fn z => Co.repeat_step_res (arr fst)
      (fn (z, co) => AE.catch' (enum_child mk_exn >>> arr (Co.append_co co #> Co.continue))
        (K (Co.continue co)) z)
      (enum_children mk_exn) (z, Co.throw (mk_exn ())))
    >>> arr (Co.dest_res #> snd)
in
\<^imap>\<open>\<open>{i}\<close> => \<open>
type @{AllT_args} zipper{i} = @{AllT_args} Z{i}.zipper\<close>\<close>

fun \<^imap>\<open>\<open>{i}\<close> => \<open>
enum_df_post_children{i} mk_exn = gen_enum_zippers mk_exn Down{i}.morph
  ZE.DF_Post\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>enum_zipper
  enum_df_post_children\<^eval>\<open>succ_mod_nzippers {i}\<close>\<close>
sep: "and" start: 2 stop: 4\<close>
and enum_df_post_children5 mk_exn z = z |>
  (Down5.morph >>> arr (Co.enum_co (ZE.DF_Post1.enum_zipper mk_exn)))

fun mk_statesq_df_post mk_exn = mk_statesq (enum_df_post_children2 mk_exn)
end
end

end

