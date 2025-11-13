\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Metis\<close>
theory Zip_Metis
  imports
    Extended_Metis_Data
    Zip_HOL
begin

ML\<open>
structure Zip =
struct open Zip
\<^functor_instance>\<open>struct_name: Metis
  functor_name: Extended_Metis_Data
  id: \<open>FI.prefix_id "metis"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    val init_args = {runs = SOME [], timeout = SOME 10.0}
    val parent_logger = Logging.logger
    \<close>\<close>
end
\<close>

declare [[zip_init_gc \<open>
  let
    open Zippy Zip; open ZLPC MU; open A Mo Base_Data
    val id = @{binding metis}
    val guard_name = FI.id
    val descr = Lazy.lazy (fn _ => implode_space [
      "metis in parallel if no promising progress by", guard_name, "is expected"])
    val logger = Zip.Metis.logger
    val (cost, progress, prio) = (Cost.VERY_LOW, AAMeta.P.promising, Cost.VERY_LOW)
    val madd = fst
    val mk_meta = Library.K (Library.K (AAMeta.metadata {cost = cost, progress = progress}))
    fun tac args ctxt i state =
      let
        (*Calling metis unconditionally often leads to loops. Before calling metis, we hence first
        gauge if zip would likely be able to make some promising progress without it. If it
        can, we skip the metis call.*)
        val zip_progress_tac =
          let
            val steps = 20 (*should be sufficient to get an estimation*)
            val _ = @{log Logger.TRACE} ctxt (fn _ => implode_space ["Checking if",
              guard_name, "can make any promising progress in", string_of_int steps, "steps."])
          in
            Context.proof_map (
              (*remove metis from test steps to avoid loops*)
              Run.Init_Goal_Cluster.Data.map_table (Run.Init_Goal_Cluster.Data.Table.delete_safe id)
              #> Run.Data.map_exec (Library.K Zippy.Run.AStar.promising'))
            #> Run.tac (SOME steps) #> CHANGED #> SELECT_GOAL
          end
        fun f_timeout n time = (@{log Logger.WARN} ctxt (fn _ => Pretty.breaks [
            Pretty.block [Pretty.str "metis timeout at pull number ", SpecCheck_Show.int n,
              Pretty.str " after ", Pretty.str (Time.print time), Pretty.str " seconds."],
            Pretty.block [Pretty.str "Called on subgoal ", SpecCheck_Show.term ctxt (Thm.prem_of state i)],
            Pretty.str "Consider removing metis for this proof or increase/disable the timeout."
          ] |> Pretty.block0 |> Pretty.string_of);
          NONE)
      in
        (if can (zip_progress_tac ctxt i #> Seq.hd) state
        then (@{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
            Pretty.str (guard_name ^ " made promising progress."),
            Pretty.str "Skipping metis."
          ] |> Pretty.block |> Pretty.string_of);
          no_tac)
        else (@{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
            Pretty.str (guard_name ^ "did not make promising progress."),
            Pretty.str "Calling metis."
          ] |> Pretty.block |> Pretty.string_of);
          Extended_Metis_Data_Args.metis_tac f_timeout args ctxt i)) state
      end
    fun ztac args _ = Ctxt.with_ctxt (tac args
      #> Tac_AAM.lift_tac mk_meta
      #> Tac_AAM.Tac.zTRY_EVERY_FOCUS1 madd
      #> arr)
    val presultsq = Zip.PResults.enum_scale_presultsq_default prio
    fun data args = {
      empty_action = Library.K Zippy.PAction.disable_action,
      meta = AMeta.metadata (id, descr),
      result_action = Result_Action.action (Library.K (C.id ())) Result_Action.copy_update_data,
      presultsq = presultsq,
      tac = ztac args}
    fun init _ focus z = Ctxt.get_ctxt () >>= (fn ctxt =>
      let
        val args = Zip.Metis.get_args (Context.Proof ctxt)
        val focus_data = if null (Extended_Metis_Data_Args.PA.get_runs args) then []
          else [(focus, data args)]
      in
        Tac.cons_action_cluster Util.exn (ACMeta.metadata (id, descr)) focus_data z
        >>= AC.opt (K z) Up3.morph
      end)
  in (id, init) end\<close>]]
declare [[zip_parse \<open>(@{binding metis}, Zip.Metis.parse_attribute
  :|-- (fn attr => Scan.depend (ML_Attribute_Util.attribute_map_context attr
    #> rpair () #> Scan.succeed)))\<close>]]

end
