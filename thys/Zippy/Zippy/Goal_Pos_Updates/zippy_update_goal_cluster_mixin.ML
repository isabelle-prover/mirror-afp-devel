(*  Title:      Zippy/zippy_update_goal_cluster_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_UPDATE_GOAL_CLUSTER_MIXIN =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  include ZIPPY_UPDATE_GOAL_CLUSTER_MIXIN_BASE
  structure Exn : ZIPPY_EXCEPTION_MIXIN
  sharing type Exn.M.t = M.t

  val update : update_gcluster
  type container2
  val update_all : (unit -> @{ParaT_args encl: "(" ")"} Exn.ME.exn) ->
    (@{ParaT_args} @{AllT_args} GCluster.L.container, GPU.F.focus) morph ->
    (@{ParaT_args} container2, @{AllT_args} GCluster.L.container) morph
end

functor Zippy_Update_Goal_Cluster_Mixin(
    structure Z : ZIPPY_ENUM_MIXIN
    structure UGC : ZIPPY_UPDATE_GOAL_CLUSTER_MIXIN_BASE
    sharing type UGC.GCluster.L.container = Z.Z2.zipper
    sharing type UGC.M.t = Z.M.t
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
    structure Log_Base : ZIPPY_LOGGER_MIXIN_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Show{i} : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show{i}.t = Z.Z{i}.zipper\<close>\<close>
  ) : ZIPPY_UPDATE_GOAL_CLUSTER_MIXIN =
struct

open Z UGC Log
structure MU = Zippy_Monad_Util(M); open MU
structure Exn = Zippy_Exception_Mixin(Z.Co)
structure ZB = Zippy_Base(structure Z = Z; structure Exn = Exn; structure Ctxt = Ctxt
  structure Log = Log_Base; \<^imap>\<open>\<open>{i}\<close> => \<open>structure Show{i} = Show{i}\<close>\<close>)
structure GCluster = Zippy_Goal_Cluster_Mixin(GCluster)

type container2 = @{AllT_args} Z.Z2.ZM.container

local open SC Mo A
in
fun update focus = Ctxt.with_ctxt (fn ctxt => fn z =>
  let
    val state = GCluster.get_state z
    val goals = GCluster.get_stripped_goals z
    fun update_args (_, update) = update (state, goals) focus
    val updates = Data.get_table (Context.Proof ctxt) |> Data.Table.dest |> List.map update_args
    val _ = @{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
        Pretty.str "Updating goal cluster with context update data",
        Show2.pretty ctxt z
      ] |> Pretty.block |> Pretty.string_of)
  in ZB.update_zipper2 updates z end)

fun update_all mk_exn mk_focus = Z2.ZM.Zip.morph
  >>> Co.Co.repeat_res (id ())
    (fn z => mk_focus z >>= (fn focus => update focus z) >>= arr Co.Co.continue)
    (Z.DF_Post2.enum_zipper mk_exn)
  >>> arr Co.Co.dest_res
end
end