\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Instance_Pure
  imports
    Zippy_Instance
    Zippy_Runs
begin

paragraph \<open>Summary\<close>
text \<open>Setup the standard instance of Zippy for proof search with short name "zippy".\<close>

ML\<open>
(* create monad *)
local
  (** exceptions **)
  structure ME = \<^eval>\<open>sfx_ParaT_nargs "Monad_Exception_Monad_Or"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Option_Monad_Or_Trans"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>))

  (** proof context **)
  structure Ctxt_MSTrans = \<^eval>\<open>sfx_ParaT_nargs "State_Trans"\<close>(
    type s = Proof.context; structure M = ME; structure SR = Pair_State_Result_Base)
  structure ME = \<^eval>\<open>sfx_ParaT_nargs "Monad_Exception_State_Trans"\<close>(
    structure M = ME; structure S = Ctxt_MSTrans)

  (** arbitrary state (not needed for now) **)
  (* structure MS = \<^eval>\<open>sfx_ParaT_nargs "IState_Trans"\<close>(
    structure M = Ctxt_MSTrans; structure SR = Pair_State_Result_Base)
  structure ME = \<^eval>\<open>sfx_ParaT_nargs "IMonad_Exception_State_Trans"\<close>(
    structure M = ME; structure S = MS)
  structure ME : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close> =
  struct open ME; type (@{ParaT_args} 'a) t = (unit, @{ParaT_arg 0}, @{ParaT_arg 0}, 'a) t end
  structure MCtxt = \<^eval>\<open>sfx_ParaT_nargs "IMonad_State_State_Trans"\<close>(
    type ParaT = unit; structure M = Ctxt_MSTrans; structure S = ME) *)

  structure Ctxt = Zippy_Ctxt_State_Mixin(Zippy_Ctxt_State_Mixin_Base(Ctxt_MSTrans))

  (** possibility to extract sequences from monad **)
  structure Seq_From_Monad = Zippy_Seq_From_Monad_Mixin_Base(structure M = ME
    type @{AllT_args} state = {ctxt : Proof.context(*, state : @{ParaT_arg 0}*)}
    fun seq_from_monad {ctxt(*, state*)} m = Seq.make (fn _ =>
      (*State_MSTrans.eval state m |>*) Ctxt_MSTrans.eval ctxt m |> the_default Seq.empty
      |> Seq.pull))

(* instance and utilities *)
  val exn : @{ParaT_args encl: "(" ")"} ME.exn = ()
  structure Zippy_Base = Zippy_Instance_Base(structure ME = ME
    type prio = Cost.cost
    type cost = Cost.cost
    val eq_cost = Cost.eq
    val pretty_cost = Cost.pretty
    fun update_cost c NONE = c
      | update_cost c (SOME (c', _)) = Cost.add (c, c'))
  structure Logging =
  struct
    val logger = Logger.setup_new_logger zippy_base_logger "Zippy"
    local structure Shared = struct val parent_logger = logger end
    in
    structure Base = Zippy_Logger_Mixin_Base(open Shared; val name = "Base")
    structure Copy = Zippy_Logger_Mixin_Base(open Shared; val name = "Copy")
    structure Enum_Copy = Zippy_Logger_Mixin_Base(open Shared; val name = "Enum_Copy")
    structure PAction = Zippy_Logger_Mixin_Base(open Shared; val name = "PAction")
    structure LGoals = Zippy_Logger_Mixin_Base(open Shared; val name = "LGoals")
    structure LGoals_Pos_Copy = Zippy_Logger_Mixin_Base(open Shared; val name = "LGoals_Pos_Copy")
    structure PAction_PResults = Zippy_Logger_Mixin_Base(open Shared; val name = "PAction_PResults")
    structure Result_Action = Zippy_Logger_Mixin_Base(open Shared; val name = "Result_Action")
    end
  end
  structure Zippy = Zippy_Instance(
    structure Z = Zippy_Base; structure Ctxt = Ctxt; structure Log_Base = Logging.Base
    structure Log_LGoals = Logging.LGoals; structure Log_LGoals_Pos_Copy = Logging.LGoals_Pos_Copy
    structure Show_Prio = Zippy_Show_Mixin_Base(
      type @{AllT_args} t = Zippy_Base.Base_Data.PAction.prio
      val pretty = Library.K Cost.pretty))
  structure Zippy_PAction = Zippy_Instance_PAction(
    structure Z = Zippy
    val mk_exn = Library.K exn
    structure Ctxt = Ctxt; structure Log_Base = Logging.Base;
    structure Log_PAction = Logging.PAction; structure Log_Result_Action = Logging.Result_Action
    structure Log_LGoals = Logging.LGoals; structure Log_LGoals_Pos_Copy = Logging.LGoals_Pos_Copy
    structure Log_Copy = Logging.Copy; structure Log_Enum_Copy = Logging.Enum_Copy)
  structure Zippy_PResults = Zippy_Instance_PResults(
    structure Z = Zippy_PAction
    structure Ctxt = Ctxt; structure Log_PAction = Logging.PAction
    structure Log_PAction_PResults = Logging.PAction_PResults)
  structure Zippy_Tactic = Zippy_Instance_Tactic(
    structure Z = Zippy_PResults; structure Ctxt = Ctxt; structure Log_PAction = Logging.PAction)
in
(* final creation of structure *)
structure Zippy =
struct
open Zippy_Base Zippy Zippy_PAction Zippy_PResults Zippy_Tactic
(** add loggers **)
structure Logging = Logging
(** add monads **)
(* structure State_MSTrans = MS
structure State = Zippy_State_Mixin(Zippy_State_Mixin_Base(MS)) *)
structure Ctxt_MSTrans = Ctxt_MSTrans
structure Ctxt = Ctxt
structure Seq_From_Monad = Seq_From_Monad
(** add base data **)
structure Base_Data = struct open Base_Data; structure Cost = Cost end
(** extend some basic and add some compound mixins **)
local
  structure Base_Mixins = struct structure Exn = Exn; structure Co = Co; structure Ctxt = Ctxt end
  structure Goals = Zippy_Goals_Mixin_Base(
    structure GClusters = Mixin_Base1.GClusters; structure GCluster = Mixin_Base2.GCluster)
  structure Goals_Pos = Zippy_Goals_Pos_Mixin(structure Z = ZLPC
    structure Goals_Pos = Zippy_Goals_Pos_Mixin_Base(open Goals; structure GPU = Base_Data.Tac_Res.GPU))
  structure Goals_Pos_Copy = Zippy_Goals_Pos_Copy_Mixin(Zippy_Goals_Pos_Copy_Mixin_Base(open Goals_Pos
    structure Copy = Mixin_Base3.Copy))
in
structure ZB = Zippy_Base(open Base_Mixins; structure Z = ZLPC; structure Log = Logging.Base
  \<^imap>\<open>\<open>{i}\<close> => \<open>structure Show{i} = Show.Zipper{i}\<close>\<close>)
structure ZN = Zippy_Node(open Base_Mixins; structure Z = ZLPC)
structure ZL = Zippy_Lists(open Base_Mixins; structure Z = ZLPC)
structure ZE = Zippy_Enum_Mixin(open Base_Mixins; open ZLPC)
structure ZP = Zippy_Positions_Mixin(open Base_Mixins; structure Z = ZLPC.ZP)
structure Mixin2 =
struct structure GCluster = Zippy_Goal_Cluster_Mixin(Zippy.Mixin_Base2.GCluster) end
structure LGoals = Zippy_Lists_Goals_Mixin(structure Z = ZL; structure Goals = Goals
  structure Ctxt = Ctxt; structure Log = Logging.LGoals)
structure LGoals_Pos_Copy = Zippy_Lists_Goals_Pos_Copy_Mixin(open Base_Mixins; structure Z = ZL
  structure GPC = Goals_Pos_Copy;
  structure Log = Logging.LGoals_Pos_Copy; structure Log_Base = Logging.Base;
  structure Log_LGoals = Logging.LGoals; \<^imap>\<open>\<open>{i}\<close> => \<open>structure Show{i} = Show.Zipper{i}\<close>\<close>)
structure Goals_Results = Zippy_Goals_Results_Mixin_Base(open LGoals_Pos_Copy
  structure GClusters_Results = Mixin_Base1.Results; structure GCluster_Results = Mixin_Base2.Results)
structure Goals_Results_TMV = Zippy_Goals_Results_Top_Meta_Vars_Mixin_Base(open Goals_Results
  structure Top_Meta_Vars = Mixin_Base2.Top_Meta_Vars)
structure PAction =
struct
  local structure PAction_More = Zippy_PAction_Mixin(open Base_Mixins
    structure PAction = Mixin_Base4.PAction; structure Log = Logging.PAction
    structure Show = Show.Zipper4)
  in open PAction_More PAction end
end
structure PResults =
struct
  local structure PResults_More = Zippy_PResults_Mixin(PResults)
  in open PResults_More PResults end
  (*exponential backoff with base s*)
  fun enum_scale_presultsq s = enum_presultsq (MU.A.arr (Cost.scale s))
end
end
(** add instance specific utilities **)
structure Util =
struct
  val exn = exn
  fun mk_exn _ = exn
  local
    open ZLPC
    structure ZN = Zippy_Node(structure Z = ZLPC; structure Exn = Exn)
    fun node_no_next1 gclusters = ZN.node_no_next1 exn (Node.co1 gclusters)
    fun node_no_next2 parent_top_meta_vars gcluster = ZN.node_no_next2 exn
      (Node.co2 parent_top_meta_vars gcluster)
  in
  fun run_monad {ctxt : Proof.context(*, state : @{ParaT_arg 0}*)} :
    (@{ParaT_args} 'a) M.t -> {ctxt : Proof.context(*, state : @{ParaT_arg 0}*), result : 'a} option =
    (*State_MSTrans.run state #>*) Ctxt_MSTrans.run ctxt #> Option.map (fn x =>
      let
        val ctxt = Ctxt_MSTrans.SR.state x
        (* val x = Ctxt_MSTrans.SR.value x
        val state = State_MSTrans.SR.state x
        val result = State_MSTrans.SR.value x *)
        val result = Ctxt_MSTrans.SR.value x
      in {ctxt = ctxt(*, state = state*), result = result} end)
  fun init_thm_state (st : Zippy_Thm_State.state) : (@{ParaT_args} @{AllT_args} Z1.zipper) M.t =
    LGoals.init_state
      (node_no_next1 #> ZN.container_no_parent exn #> Container.init_container1 #> Z1.ZM.Zip.morph)
      (node_no_next2 (Zippy_Thm_State.meta_vars st)) st
  end
end
end
end
\<close>

ML\<open>
(*add run and steps*)
structure Zippy =
struct open Zippy
local open MU; open SC A Mo
  structure Base_Mixins =
  struct
    structure Z = ZLPC
    structure Exn = Exn; structure Co = Co; structure Ctxt = Ctxt
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Show{i} = Show.Zipper{i}
    structure Show_Container{i} = Show.Container{i}\<close>\<close>
  end
in
(* steps *)
(** base **)
structure Step =
struct
  local structure Log = Zippy_Logger_Mixin_Base(val parent_logger = Logging.logger; val name =  "Step")
  in open Log end
  local structure ZCost = Zippy_Collect_Trace_Mixin(ZLPC.ZCollect)
  in
  fun check_depth_limit opt_limit = ZP.ZZDepth_Co4.getter
    #> (fn depth => case opt_limit of
        NONE => pure depth
      | SOME l => if depth <= l then pure depth else Exn.ME.throw Util.exn)
  structure AStar =
  struct
    structure Logging =
    struct
      val logger = Logger.setup_new_logger logger "AStar"
      local structure Base = struct val parent_logger = logger end
      in
      structure PAction_Queue = Zippy_Logger_Mixin_Base(open Base; val name = "PAction_Queue")
      structure Step = Zippy_Logger_Mixin_Base(open Base; val name = "Step")
      end
    end
    structure PAction_Queue = Zippy_PAction_Queue_Mixin_Base(
      structure PAction = PAction
      structure Queue = Leftist_Heap(type prio = PAction.prio; val ord = Cost.ord))
    structure Show =
    struct
      structure Queue_Entry = Zippy_Show_Mixin_Base(
        type @{AllT_args} t = @{AllT_args} PAction_Queue.entry
        fun pretty ctxt {prio, zipper,...} = SpecCheck_Show.record [
          ("Priority", Show.Prio.pretty ctxt prio),
          ("Zipper", Show.Zipper4.pretty ctxt zipper)])
      structure Prio = Show.Prio
    end
    structure PAction_Queue = Zippy_PAction_Queue_Mixin(open Base_Mixins
      structure Z = ZE; structure PAction_Queue = PAction_Queue
      val mk_exn = Util.mk_exn; structure Log = Logging.PAction_Queue
      structure Show_Queue_Entry = Show.Queue_Entry; structure Show_Prio = Show.Prio)
    structure Step = Zippy_Step_Mixin(open Base_Mixins
      structure Step = Zippy_Step_Mixin_Base(open Goals_Results_TMV
        structure PAction_Queue = PAction_Queue)
      val mk_exn = Util.mk_exn; structure Log = Logging.Step
      structure Log_LGoals = Zippy.Logging.LGoals
      structure Log_PAction_Queue = Logging.PAction_Queue
      structure Show_Queue_Entry = Show.Queue_Entry; structure Show_Prio = Show.Prio)
    fun mk_prio ({prio, zipper,...} : @{AllT_args} PAction_Queue.entry) =
      ZCost.ZZCollect_Co4.getter zipper |> ZCost.get_current
      |> Option.map (Library.curry Cost.add prio) |> the_default prio
    fun mk_prio_depth_limit opt_depth_limit (entry as {zipper,...}) =
      check_depth_limit opt_depth_limit zipper >>= arr (fn _ => mk_prio entry)
  end
  end

  structure Best_First =
  struct
    structure Logging =
    struct
      val logger = Logger.setup_new_logger logger "Best_First"
      local structure Base = struct val parent_logger = logger end
      in
      structure PAction_Queue = Zippy_Logger_Mixin_Base(open Base; val name = "PAction_Queue")
      structure Step = Zippy_Logger_Mixin_Base(open Base; val name = "Step")
      end
    end
    structure PAction_Queue = Zippy_PAction_Queue_Mixin_Base(
      structure PAction = PAction
      structure Queue = AStar.PAction_Queue.Queue)
    structure Show =
    struct
      structure Queue_Entry = Zippy_Show_Mixin_Base(
        type @{AllT_args} t = @{AllT_args} PAction_Queue.entry
        fun pretty ctxt {prio, zipper,...} = SpecCheck_Show.record [
          ("Priority", Show.Prio.pretty ctxt prio),
          ("Zipper", Show.Zipper4.pretty ctxt zipper)])
      structure Prio = AStar.Show.Prio
    end
    structure PAction_Queue = Zippy_PAction_Queue_Mixin(open Base_Mixins
      structure Z = ZE; structure PAction_Queue = PAction_Queue
      val mk_exn = Util.mk_exn; structure Log = Logging.PAction_Queue
      structure Show_Queue_Entry = Show.Queue_Entry; structure Show_Prio = Show.Prio)
    structure Step = Zippy_Step_Mixin(open Base_Mixins
      structure Step = Zippy_Step_Mixin_Base(open Goals_Results_TMV
        structure PAction_Queue = PAction_Queue)
      val mk_exn = Util.mk_exn; structure Log = Logging.Step
      structure Log_LGoals = Zippy.Logging.LGoals
      structure Log_PAction_Queue = Logging.PAction_Queue
      structure Show_Queue_Entry = Show.Queue_Entry; structure Show_Prio = Show.Prio)
    fun mk_prio ({prio,...} : @{AllT_args} PAction_Queue.entry) = prio
    fun mk_prio_depth_limit opt_depth_limit (entry as {zipper,...}) =
      check_depth_limit opt_depth_limit zipper >>= arr (fn _ => mk_prio entry)
  end

  local
    type prio = {depth : int, prio : PAction.prio}
    fun prio_ord depth_ord ({depth = depth1, prio = prio1}, {depth = depth2, prio = prio2}) =
    prod_ord depth_ord Cost.ord ((depth1, prio1), (depth2, prio2))
  in
  structure Depth_First =
  struct
    structure Logging =
    struct
      val logger = Logger.setup_new_logger logger "Depth_First"
      local structure Base = struct val parent_logger = logger end
      in
      structure PAction_Queue = Zippy_Logger_Mixin_Base(open Base; val name = "PAction_Queue")
      structure Step = Zippy_Logger_Mixin_Base(open Base; val name = "Step")
      end
    end
    structure PAction_Queue = Zippy_PAction_Queue_Mixin_Base(
      structure PAction = PAction
      structure Queue = Leftist_Heap(type prio = prio; val ord = prio_ord (int_ord #> rev_order)))
    structure Show =
    struct
      structure Queue_Entry = Zippy_Show_Mixin_Base(
        type @{AllT_args} t = @{AllT_args} PAction_Queue.entry
        fun pretty ctxt {prio, zipper,...} = SpecCheck_Show.record [
          ("Priority", Show.Prio.pretty ctxt prio),
          ("Zipper", Show.Zipper4.pretty ctxt zipper)])
      structure Prio = Zippy_Show_Mixin_Base(
        type @{AllT_args} t = PAction_Queue.Queue.prio
        fun pretty ctxt {depth, prio} = SpecCheck_Show.record [
          ("Depth", SpecCheck_Show.int depth),
          ("Priority", Show.Prio.pretty ctxt prio)])
    end
    structure PAction_Queue = Zippy_PAction_Queue_Mixin(open Base_Mixins
      structure Z = ZE; structure PAction_Queue = PAction_Queue
      val mk_exn = Util.mk_exn; structure Log = Logging.PAction_Queue
      structure Show_Queue_Entry = Show.Queue_Entry; structure Show_Prio = Show.Prio)
    structure Step = Zippy_Step_Mixin(open Base_Mixins
      structure Step = Zippy_Step_Mixin_Base(open Goals_Results_TMV
        structure PAction_Queue = PAction_Queue)
      val mk_exn = Util.mk_exn; structure Log = Logging.Step
      structure Log_LGoals = Zippy.Logging.LGoals
      structure Log_PAction_Queue = Logging.PAction_Queue
      structure Show_Queue_Entry = Show.Queue_Entry; structure Show_Prio = Show.Prio)
    fun mk_prio_depth_limit opt_depth_limit (entry as {zipper,...}) =
      check_depth_limit opt_depth_limit zipper
      >>= arr (fn depth => AStar.mk_prio entry |> (fn prio => {depth = depth, prio = prio}))
  end

  structure Breadth_First =
  struct
    structure Logging =
    struct
      val logger = Logger.setup_new_logger logger "Breadth_First"
      local structure Base = struct val parent_logger = logger end
      in
      structure PAction_Queue = Zippy_Logger_Mixin_Base(open Base; val name = "PAction_Queue")
      structure Step = Zippy_Logger_Mixin_Base(open Base; val name = "Step")
      end
    end
    structure PAction_Queue = Zippy_PAction_Queue_Mixin_Base(structure PAction = PAction
      structure Queue = Leftist_Heap(type prio = Depth_First.PAction_Queue.Queue.prio
        val ord = prio_ord int_ord))
    structure Show =
    struct
      structure Queue_Entry = Zippy_Show_Mixin_Base(
        type @{AllT_args} t = @{AllT_args} PAction_Queue.entry
        fun pretty ctxt {prio, zipper,...} = SpecCheck_Show.record [
          ("Priority", Show.Prio.pretty ctxt prio),
          ("Zipper", Show.Zipper4.pretty ctxt zipper)])
      structure Prio = Depth_First.Show.Prio
    end
    structure PAction_Queue = Zippy_PAction_Queue_Mixin(open Base_Mixins
      structure Z = ZE; structure PAction_Queue = PAction_Queue
      val mk_exn = Util.mk_exn; structure Log = Logging.PAction_Queue
      structure Show_Queue_Entry = Show.Queue_Entry; structure Show_Prio = Show.Prio)
    structure Step = Zippy_Step_Mixin(open Base_Mixins
      structure Step = Zippy_Step_Mixin_Base(open Goals_Results_TMV
        structure PAction_Queue = PAction_Queue)
      val mk_exn = Util.mk_exn; structure Log = Logging.Step
      structure Log_LGoals = Zippy.Logging.LGoals
      structure Log_PAction_Queue = Logging.PAction_Queue
      structure Show_Queue_Entry = Show.Queue_Entry; structure Show_Prio = Show.Prio)
    val mk_prio_depth_limit = Depth_First.mk_prio_depth_limit
  end
  end
  end

(* run *)
structure Run =
struct
(** base **)
fun with_state f = Ctxt.with_ctxt (fn ctxt => (*State.with_state (fn state =>*)
  f {ctxt = ctxt(*, state = state*)})
local structure Run = Zippy_Run_Mixin(open Base_Mixins
  structure Run = Zippy_Run_Mixin_Base(open Goals_Results
    structure Seq_From_Monad = Seq_From_Monad)
  val with_state = with_state
  structure Log = Zippy_Logger_Mixin_Base(val parent_logger = Logging.logger; val name =  "Run"))
in open Run end
(** utility functions **)
local
  structure GClusters = Zippy_Goal_Clusters_Mixin(GClusters)
  structure GClusters_Results = Zippy_Goal_Results_Mixin(GClusters_Results)
  structure LGoals_Results_TMV = Zippy_Lists_Goals_Results_Top_Meta_Vars_Mixin(open Base_Mixins
    structure Z = Zippy_Lists(open Base_Mixins)
    structure Goals_Results_Top_Meta_Vars = Goals_Results_TMV; structure Log_LGoals = Logging.LGoals)
  structure EAction_App_Meta = Zippy_Enum_Action_App_Metadata_Mixin(
    structure Z = ZE
    structure Meta = Zippy_Action_App_Metadata_Mixin(Zippy.Mixin_Base5.Meta))
in
fun run_statesq init_sstate step finish fuel c = init_sstate c
  >>= with_state (fn ms => arr (fn ss => repeat_step step finish finish fuel ss ms c
    |> Seq.maps (Zippy_Run_Result.cases #thm_states I)))
fun run_statesq' init_sstate step mk_unreturned_statesq = run_statesq init_sstate step (fn _ => fn _ =>
  ZLPC.Z1.ZM.Zip.morph >>> mk_unreturned_statesq >>> arr (Zippy_Run_Result.Unfinished #> Seq.single))
fun mk_df_post_unreturned_statesq x = mk_unreturned_statesq (Ctxt.with_ctxt
  (LGoals_Results_TMV.mk_statesq (LGoals_Results_TMV.enum_df_post_children2 Util.mk_exn))) x
fun mk_df_post_unreturned_promising_statesq x = mk_unreturned_statesq (Ctxt.with_ctxt
  (LGoals_Results_TMV.mk_statesq (EAction_App_Meta.enum_df_post_promising_children2 Util.mk_exn))) x

local
  fun mk_funs mk_prio_depth_limit init_pactions_queue step_queue =
  let
    fun gen finish opt_depth_limit =
      let val mk_prio = mk_prio_depth_limit opt_depth_limit
      in run_statesq' (init_pactions_queue mk_prio) (step_queue mk_prio) finish end
    fun mk_limit_variants f = (gen f, SOME #> gen f, gen f NONE)
  in
    (gen,
    mk_limit_variants mk_df_post_unreturned_statesq,
    mk_limit_variants mk_df_post_unreturned_promising_statesq)
  end
in
structure AStar =
struct
  local open Step.AStar
  in
  val (gen, (gen_all, all, all'), (gen_promising, promising, promising')) =
    mk_funs mk_prio_depth_limit PAction_Queue.init_pactions_queue Step.step_queue
  end
end
structure Best_First =
struct
  local open Step.Best_First
  in
  val (gen, (gen_all, all, all'), (gen_promising, promising, promising')) =
    mk_funs mk_prio_depth_limit PAction_Queue.init_pactions_queue Step.step_queue
  end
end
structure Depth_First =
struct
  local open Step.Depth_First
  in
  val (gen, (gen_all, all, all'), (gen_promising, promising, promising')) =
    mk_funs mk_prio_depth_limit PAction_Queue.init_pactions_queue Step.step_queue
  end
end
structure Breadth_First =
struct
  local open Step.Breadth_First
  in
  val (gen, (gen_all, all, all'), (gen_promising, promising, promising')) =
    mk_funs mk_prio_depth_limit PAction_Queue.init_pactions_queue Step.step_queue
  end
end
end

val are_thm_variants = apply2 (Thm.prop_of #> Same.commit Term_Normalisation.beta_eta_short)
  #> Term_Util.are_term_variants
fun changed_uniquesq st = Seq.filter (fn st' => not (are_thm_variants (st, st')))
  #> Tactic_Util.unique_thmsq are_thm_variants
end
end
end
end
\<close>

end
