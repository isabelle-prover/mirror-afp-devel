(*  Title:      Zippy/zippy_lists_goals_results_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_GOALS_RESULTS_MIXIN =
sig
  include ZIPPY_GOALS_RESULTS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>

  (*initialise results below and including the given zipper*)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  type @{AllT_args} zipper{i}
  val init_goal_results_down{i} : Proof.context -> (@{ParaT_args} @{AllT_args} zipper{i},
    @{AllT_args} zipper{i} * Results.results) morph\<close>\<close>

  (*update and return results upwards from the given zipper*)
  val update_goal_results_up : Proof.context -> (@{ParaT_args} @{AllT_args} zipper1,
    @{AllT_args} zipper1 * Results.results) morph
  (*invariants for update_goal_results_up{i}: passed result sequence for children is non-empty*)
  val update_goal_results_up1 : GClusters.GCS.cluster_pos -> GClusters.GCS.state Seq.seq ->
    Proof.context -> (@{ParaT_args} @{AllT_args} zipper1, @{AllT_args} zipper1 * Results.results) morph
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val update_goal_results_up{i} : GClusters.GCS.state Seq.seq -> Proof.context ->
    (@{ParaT_args} @{AllT_args} zipper{i}, @{AllT_args} zipper1 * Results.results) morph\<close>
  start: 2\<close>
end

functor Zippy_Lists_Goals_Results_Mixin(
    structure Z : ZIPPY_LISTS
    structure Goals_Results : ZIPPY_GOALS_RESULTS_MIXIN_BASE
    sharing type Goals_Results.GClusters.L.container = Z.Z1.zipper
    sharing type Goals_Results.GCluster.L.container = Z.Z2.zipper
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t =Z.M.t
    structure Log_LGoals : ZIPPY_LOGGER_MIXIN_BASE
  ) : ZIPPY_LISTS_GOALS_RESULTS_MIXIN =
struct

open Z Goals_Results
structure MU = Zippy_Monad_Util(M); open MU
structure Exn = Zippy_Exception_Mixin(Co)
structure GClusters = Zippy_Goal_Clusters_Mixin(GClusters)
structure GClusters_Results = Zippy_Goal_Results_Mixin(GClusters_Results)
structure GCluster_Results = Zippy_Goal_Results_Mixin(GCluster_Results)
structure LGoals = Zippy_Lists_Goals_Mixin(structure Z = Z; structure Goals = Goals_Results
  structure Ctxt = Ctxt; structure Log = Log_LGoals)

\<^imap>\<open>\<open>{i}\<close> => \<open>
type @{AllT_args} zipper{i} = @{AllT_args} Z{i}.zipper\<close>\<close>

local open SC A Mo Co Exn
  fun gen_init_goal_results_down init_goal_results_down_child enum_children up_child combine_res =
    let
      fun update_child (z, (_, results_acc)) = init_goal_results_down_child z
        >>= A.second (arr (fn results => combine_res results results_acc))
        >>= arr Co.continue
      fun update_children (z, co) = init_goal_results_down_child z
        >>= AE.try (fn res as (z, _) =>
          Co.repeat_step_res (arr (snd #> fst)) update_child co (z, res)
          >>= arr (Co.dest_res #> snd))
    in AE.catch' (enum_children >>> update_children >>> A.first up_child) end
  fun with_results x = Results.non_empty x |> rpair
  fun without_results x = x |> rpair Results.empty
in
fun init_goal_results_down1 ctxt z =
  let fun mk_nonempty_results statesq z =
    with_results statesq (GClusters_Results.set_non_empty_states statesq z)
  in
    if GClusters.is_finished z
    then pure (mk_nonempty_results (Seq.single (GClusters.get_state z)) z)
    else
      let fun update_zipper (z, results) = if Library.forall Results.has_results results
        then let val statesqs = List.map Results.get_states results
          in mk_nonempty_results (GClusters.finish_cluster_statesqs ctxt (rev statesqs) z) z end
        else without_results z
      in
        gen_init_goal_results_down
          (init_goal_results_down2 ctxt >>> A.second (arr single))
          (Down1.morph >>> Z2.ZM.Unzip.morph >>> LGoals.enum_gcluster) Up2.morph
          (fn results => cons (the_single results)) (arr (rpair [Results.empty])) z
        >>= arr update_zipper
      end
  end
and init_goal_results_down2 ctxt =
  let fun update_zipper (z, results) =
    (if Results.has_results results
    then GCluster_Results.set_non_empty_states (Results.get_states results) z
    else z,
    results)
  in
    gen_init_goal_results_down (init_goal_results_down3 ctxt)
      (Down2.morph >>> Z3.ZM.Unzip.morph >>> enum_zipper3) Up3.morph
      Results.append (arr without_results)
    >>> arr update_zipper
  end
\<^imap>\<open>\<open>{i}\<close> => \<open>
and init_goal_results_down{i} ctxt =
  gen_init_goal_results_down (init_goal_results_down\<^eval>\<open>succ_mod_nzippers {i}\<close> ctxt)
    (Down{i}.morph
    >>> Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.Unzip.morph
    >>> enum_zipper\<^eval>\<open>succ_mod_nzippers {i}\<close>)
    Up\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>morph Results.append (arr without_results)\<close>
start: 3\<close>

local fun go_top_no_goal_results x = x |> (top1 >>> arr without_results)
in
fun update_goal_results_up1 cpos statesq ctxt z =
  let fun update_results zippers =
    let val statesq =
      map_index
        (General_Util.fun_update (fst #> equal cpos) statesq (snd #> GCluster_Results.get_states))
        zippers
      |> (fn statesqs => GClusters.finish_cluster_statesqs ctxt statesqs z)
    in
      GClusters_Results.append_non_empty_states statesq z
      |> AE.catch'
        (Up1.morph >>> \<^eval>\<open>"update_goal_results_up" ^ pred_mod_nzippers 1\<close> statesq ctxt)
        (arr (with_results statesq))
    end
  in
    Down1.morph z >>= LGoals.gcluster_list
    >>= (fn zippers => if Library.forall GCluster_Results.has_results zippers
      then update_results zippers
      else go_top_no_goal_results z)
  end
and update_goal_results_up2 statesq ctxt z =
  let val cpos = (GCluster.L.getter #> GCluster.GC.get_pos) z
  in
    GCluster_Results.append_non_empty_states statesq z
    |> Up2.morph >>= update_goal_results_up1 cpos statesq ctxt
  end
\<^imap>\<open>\<open>{i}\<close> => \<open>
and update_goal_results_up{i} statesq ctxt = Up{i}.morph
  >>> update_goal_results_up\<^eval>\<open>pred_mod_nzippers {i}\<close> statesq ctxt\<close>
start: 3\<close>

fun update_goal_results_up ctxt z = if GClusters_Results.has_results z
  then let val statesq = GClusters_Results.get_states z
    in
      AE.catch'
        (Up1.morph >>> \<^eval>\<open>"update_goal_results_up" ^ pred_mod_nzippers 1\<close> statesq ctxt)
        (arr (with_results statesq)) z
    end
  else go_top_no_goal_results z
end
end

end

