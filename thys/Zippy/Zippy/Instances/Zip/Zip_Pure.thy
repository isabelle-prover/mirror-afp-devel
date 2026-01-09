\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Zip - Extensible White-Box Prover\<close>
theory Zip_Pure
  imports
    Context_Parsers
    Zippy_Instance_Resolves_Simp
    Zippy_Instance_Pure
    Zippy_Instance_Simp
begin

paragraph \<open>Summary\<close>
text \<open>Setup the the extensible white-box prover called "zip" based on Zippy.\<close>

ML\<open>
local structure Zippy_Simp = Zippy_Instance_Simp(structure Z = Zippy; structure Ctxt = Z.Ctxt)
in structure Zippy = struct open Zippy_Simp Zippy end end\<close>

ML\<open>
local open Zippy
  val default_presultsq_scale = Rat.make (12, 10)
  structure Resolve_Base =
  struct
    structure Z = Zippy
    val cost = Cost.MEDIUM
    structure TI = Discrimination_Tree
    open Base_Data.AAMeta
    fun init_args get_thm = {
      empty_action = SOME (Library.K PAction.disable_action),
      default_update = SOME (fn _ => @{undefined}), (*just a temporary placeholder*)
      mk_cud = SOME Result_Action.copy_update_data_empty_changed,
      presultsq = SOME (PResults.enum_scale_presultsq default_presultsq_scale cost),
      mk_meta = SOME (Library.K (Library.K (metadata {cost = cost, progress = P.promising}))),
      del_select = SOME (apsnd (snd #> get_thm) #> Thm.eq_thm)}
  end
in
\<^functor_instance>\<open>struct_name: Zip
  functor_name: Zippy_Instance_Resolves_Simp
  id: \<open>"zip"\<close>
  more_args: \<open>open Resolve_Base; open Z
    val resolve_init_args = init_args Zippy_Instance_Hom_Changed_Goals_Data_Args.PD.get_thm
    val simp_init_args = {timeout = SOME 10.0, depth = NONE}
    structure Log_Base = Z.Logging.Base\<close>\<close>
structure Zip =
struct open Zip
(*add resolution with proof-producing unification*)
structure Logging =
struct open Logging
  structure URule = Zippy_Logger_Mixin_Base(val parent_logger = logger; val name = "URule")
end

local val default_update = Run.init_gpos
in
val _ = Theory.setup (Rule.Resolve.map_default_update (K default_update)
  #> Rule.EResolve.map_default_update (K default_update)
  #> Rule.DResolve.map_default_update (K default_update)
  #> Rule.FResolve.map_default_update (K default_update)
  #> Match.Resolve.map_default_update (K default_update)
  #> Match.EResolve.map_default_update (K default_update)
  #> Match.DResolve.map_default_update (K default_update)
  #> Match.FResolve.map_default_update (K default_update)
  |> Context.theory_map)

\<^functor_instance>\<open>struct_name: URule
  functor_name: Zippy_Instance_UResolves_Data
  id: \<open>FI.prefix_id "urule"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Resolve_Base
    structure PDC = Zippy_Instance_Hom_Changed_Goals_Data_Args.PDC
    val init_args = init_args Zippy_Instance_UResolve_Data_Args.PD.get_rule |> (fn args => {
      normalisers = SOME Mixed_Comb_Unification.norms_fo_hop_comb_unify,
      unifier = SOME Mixed_Comb_Unification.fo_hop_comb_unify,
      mk_meta = SOME (PDC.get_mk_meta args),
      empty_action = SOME (PDC.get_empty_action args),
      default_update = SOME default_update,
      mk_cud = SOME (PDC.get_mk_cud args),
      presultsq = SOME (PDC.get_presultsq args),
      del_select = SOME (PDC.get_del_select args)})
    structure Log = Logging.URule\<close>\<close>
end

structure PResults =
struct
val default_presultsq_scale = default_presultsq_scale
val enum_scale_presultsq_default = Zippy.PResults.enum_scale_presultsq default_presultsq_scale
end
end
end
\<close>
local_setup\<open>Zip.Run.Init_Goal_Cluster.Data.setup_attribute
  (Either.Right "goal cluster initialisation")\<close>
local_setup\<open>Zip.Simp.Extended_Data.setup_attribute (Either.Right "extended simp")\<close>

ML\<open>
structure Zip =
struct open Zip(* add parsers *)
\<^functor_instance>\<open>struct_name: Context_Parsers
  functor_name: Context_Parsers
  id: \<open>FI.prefix_id "parse"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    val parent_logger = Logging.logger
    val parsers_separator = "where"\<close>\<close>

(* add instance specific utilities *)
structure Run =
struct open Run
local open Zippy; open ZLPC MU; open SC A
in
fun init st = st |>
  (Util.init_thm_state >>> Down1.morph >>> Z2.ZM.Unzip.morph
  >>> Init_Goal_Cluster.update_all (Library.K Util.exn)
    (arr (Mixin2.GCluster.get_ngoals #> Base_Data.Tac_Res.GPU.F.all_upto))
  >>> top2 >>> Z1.ZM.Unzip.morph)

\<^functor_instance>\<open>struct_name: Data
  functor_name: Zippy_Run_Data
  id: \<open>FI.prefix_id "run"\<close>
  path: \<open>FI.struct_op "Run"\<close>
  more_args: \<open>
    structure Z = ZLPC
    structure Ctxt = Ctxt
    structure Seq_From_Monad = Seq_From_Monad
    type exec_config = int option (*fuel*)
    val init_args = {
      init = SOME init,
      exec = SOME Run.AStar.promising',
      post = SOME (fn st => Ctxt.with_ctxt (fn ctxt =>
        arr (Run.changed_uniquesq st #> Seq.maps (prune_params_tac ctxt))))}\<close>\<close>
fun tac fuel ctxt = Data.tac fuel {ctxt = ctxt}
end
end

(** some convenience abbreviations **)
structure AStar = Zippy.Run.AStar
structure Depth_First = Zippy.Run.Depth_First
structure Breadth_First = Zippy.Run.Breadth_First
structure Best_First = Zippy.Run.Best_First
(** try all executors in parallel **)
structure Try =
struct
local open Zippy; open MU
  fun exec_all fs ctxt =
    let fun run (who, f) = Timing.timing
        (Seq_From_Monad.seq_from_monad {ctxt = ctxt} #> Seq.filter Thm.no_prems #> Seq.pull) f
      |> (fn (_, NONE) => NONE
        | (timing, x) => (warning (who ^ " finished. Timing: " ^ Timing.message timing); x))
      |> Library.K |> Seq.make
    in Par_List.map run fs |> Seq.of_list |> Seq.flat |> (fn sq => Mo.pure sq ctxt) end
in
val execs = ["AStar", "Depth_First", "Breadth_First", "Best_First"]
fun gen post depth fuel c = [AStar.gen, Depth_First.gen, Breadth_First.gen, Best_First.gen]
  |> List.map (fn f => f post depth fuel c) |> curry (op ~~) execs |> exec_all
fun gen_all depth fuel c = [AStar.gen_all, Depth_First.gen_all, Breadth_First.gen_all, Best_First.gen_all]
  |> List.map (fn f => f depth fuel c) |> curry (op ~~) execs |> exec_all
fun all depth fuel c = [AStar.all, Depth_First.all, Breadth_First.all, Best_First.all]
  |> List.map (fn f => f depth fuel c) |> curry (op ~~) execs |> exec_all
fun all' fuel c = [AStar.all', Depth_First.all', Breadth_First.all', Best_First.all']
  |> List.map (fn f => f fuel c) |> curry (op ~~) execs |> exec_all
end
end
end
\<close>
local_setup\<open>Zip.Context_Parsers.setup_attribute NONE\<close>
local_setup\<open>Zip.Run.Data.setup_attribute NONE\<close>
declare [[zip_parse add: \<open>(@{binding run}, Zip.Run.Data.parse_context_update)\<close>]]

subsubsection \<open>Method\<close>

local_setup \<open>
  let open Zippy Zip.Run
    val parse_fuel = Parse_Util.option Parse.nat
    val parse = Scan.lift parse_fuel --| Zip.Context_Parsers.parse
      >> (Method.SIMPLE_METHOD oo tac)
  in Method.local_setup Zip.binding parse "Extensible white-box prover based on Zippy" end\<close>

subsubsection \<open>Resolution\<close>

local_setup\<open>Zip.Rule.setup_attribute
  (Either.Right "(e/d/f-)resolution with higher-order unification")\<close>
local_setup\<open>Zip.Match.setup_attribute
  (Either.Right "(e/d/f-)resolution with higher-order matching")\<close>
local_setup\<open>Zip.URule.setup_attribute
  (Either.Right "(e/d/f-)resolution with proof-producing unification")\<close>

declare [[zip_init_gc \<open>
  let
    open Zippy Zip.Rule.Resolve; open ZLPC MU; open SC A Mo
    val id = @{binding resolve_ho_unif_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "resolution with higher-order unification on first possible goal")
    val tac = resolve_tac
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.unifiables
    fun lookup_goal ctxt = snd #> snd #> Data.TI.norm_term
      #> retrieval (Data.get_index (Context.Proof ctxt))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals =
        lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zip.Match.Resolve; open ZLPC MU; open SC A Mo
    val id = @{binding resolve_ho_match_first}
    val descr = Lazy.value "resolution with higher-order matching on first possible goal"
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "resolution with higher-order matching on first possible goal")
    val tac = match_tac
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.generalisations
    fun lookup_goal ctxt = snd #> snd #> Data.TI.norm_term
      #> retrieval (Data.get_index (Context.Proof ctxt))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zip.URule.Resolve; open ZLPC MU; open SC A Mo
    val id = @{binding resolve_proof_unif_first}
    val descr = Lazy.value "resolution with proof-producing unification on first possible goal"
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "resolution with proof-producing unification on first possible goal")
    val tac = Unify_Resolve_Base.unify_resolve_tac
    fun ztac normalisers unifier mk_meta thm _ = Ctxt.with_ctxt (tac normalisers unifier thm
      #> Tac_AAM.lift_tac mk_meta
      #> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      #> arr)
    (*Note: there is no complete, efficient retrieval other than taking all rules. In case of a
    large rule set, one can use an incomplete retrieval returning only those rules whose
    left-hand or right-hand side potentially higher-order unifies with a disagreement term.
    Cf. the retrieval used in ML_Unification.ML_Unification_Hints*)
    val retrieval = Data.TI.content
    fun lookup_goal ctxt _ = retrieval (Data.get_index (Context.Proof ctxt))
      |> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]
(*TODO: could be made more efficient: we already know the indices of possibly matching premises when
seraching the term index but do not use that information in the subsequent (d/e)resolution*)
declare [[zip_init_gc
  \<open>let
    open Zippy Zip.Rule.EResolve; open ZLPC MU; open SC A Mo
    val id = @{binding eresolve_ho_unif_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "e-resolution with higher-order unification on first possible goal")
    val tac = eresolve_tac
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.unifiables
    fun lookup_goal ctxt = snd #> fst #>
      maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zip.Match.EResolve; open ZLPC MU; open SC A Mo
    val id = @{binding eresolve_ho_match_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "e-resolution with higher-order matching on first possible goal")
    val tac = ematch_tac
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.generalisations
    fun lookup_goal ctxt = snd #> fst
      #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zip.URule.EResolve; open ZLPC MU; open SC A Mo
    val id = @{binding eresolve_proof_unif_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "e-resolution with proof-producing unification on first possible goal")
    fun tac norms unify = Unify_Resolve_Base.unify_eresolve_tac norms unify norms unify
    fun ztac normalisers unifier mk_meta thm _ = Ctxt.with_ctxt (tac normalisers unifier thm
      #> Tac_AAM.lift_tac mk_meta
      #> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      #> arr)
    val retrieval = Data.TI.content
    fun lookup_goal ctxt _ = retrieval (Data.get_index (Context.Proof ctxt))
      |> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]
declare [[zip_init_gc
  \<open>let
    open Zippy Zip.Rule.DResolve; open ZLPC MU; open SC A Mo
    val id = @{binding dresolve_ho_unif_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "d-resolution with higher-order unification on first possible goal")
    fun tac ctxt thms =
      let
        (*Tactic.make_elim allows no context passing but Thm.biresolution fails to certificate certain
        theorems without a context*)
        fun make_elim ctxt thm =
          let val resolve = Thm.biresolution (SOME ctxt) false [(false, thm)] |> HEADGOAL #> Seq.hd
          in zero_var_indexes (resolve revcut_rl) end
      in eresolve_tac ctxt (List.map (make_elim ctxt) thms) end
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.unifiables
    fun lookup_goal ctxt = snd #> fst #>
      maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zip.Match.DResolve; open ZLPC MU; open SC A Mo
    val id = @{binding dresolve_ho_match_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "d-resolution with higher-order matching on first possible goal")
    fun tac ctxt thms =
      let
        fun make_elim ctxt thm =
          let val resolve = Thm.biresolution (SOME ctxt) false [(false, thm)] |> HEADGOAL #> Seq.hd
          in zero_var_indexes (resolve revcut_rl) end
      in ematch_tac ctxt (List.map (make_elim ctxt) thms) end
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac ctxt [thm]
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.generalisations
    fun lookup_goal ctxt = snd #> fst #>
      maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zip.URule.DResolve; open ZLPC MU; open SC A Mo
    val id = @{binding dresolve_proof_unif_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "d-resolution with proof-producing unification on first possible goal")
    val tac = Unify_Resolve_Base.unify_dresolve_tac
    fun ztac normalisers unifier mk_meta thm _ = Ctxt.with_ctxt (tac normalisers unifier thm
      #> Tac_AAM.lift_tac mk_meta
      #> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      #> arr)
    val retrieval = Data.TI.content
    fun lookup_goal ctxt _ = retrieval (Data.get_index (Context.Proof ctxt))
      |> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]
declare [[zip_init_gc
  \<open>let
    open Zippy Zip.Rule.FResolve; open ZLPC MU; open SC A Mo
    val id = @{binding fresolve_ho_unif_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "f-resolution with higher-order unification on first possible goal")
    val tac = Unify_Resolve_Base.unify_fresolve_tac
      Higher_Order_Unification.norms_unify Higher_Order_Unification.unify
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac thm ctxt
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.unifiables
    fun lookup_goal ctxt = snd #> fst
      #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zip.Match.FResolve; open ZLPC MU; open SC A Mo
    val id = @{binding fresolve_ho_match_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "f-resolution with higher-order matching on first possible goal")
    (*FIXME: use same matcher as in other match tactics*)
    val tac = Unify_Resolve_Base.unify_fresolve_tac
      Mixed_Unification.norms_fo_hop_match Mixed_Unification.fo_hop_match
    fun ztac mk_meta thm _ = Ctxt.with_ctxt (fn ctxt => tac thm ctxt
      |> Tac_AAM.lift_tac mk_meta
      |> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      |> arr)
    val retrieval = Data.TI.generalisations
    fun lookup_goal ctxt = snd #> fst
      #> maps (Data.TI.norm_term #> retrieval (Data.get_index (Context.Proof ctxt)))
      #> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
     fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>
  \<open>let
    open Zippy Zip.URule.FResolve; open ZLPC MU; open SC A Mo
    val id = @{binding fresolve_proof_unif_first}
    val meta = Base_Data.ACMeta.metadata (id,
      Lazy.value "f-resolution with proof-producing unification on first possible goal")
    val tac = Unify_Resolve_Base.unify_fresolve_tac
    fun ztac normalisers unifier mk_meta thm _ = Ctxt.with_ctxt (tac normalisers unifier thm
      #> Tac_AAM.lift_tac mk_meta
      #> Tac_AAM.Tac.zFIRST_GOAL_FOCUS
      #> arr)
    val retrieval = Data.TI.content
    fun lookup_goal ctxt _ = retrieval (Data.get_index (Context.Proof ctxt))
      |> List.map (apsnd (transfer_data (Proof_Context.theory_of ctxt)))
    fun cons_actions focus = Ctxt.with_ctxt (fn ctxt => fn z =>
      let fun lookup_cons_goals goals = lookup_each_focused_data (lookup_goal ctxt) goals focus
        |> map_index (fn (i, (focus, data)) =>
          cons_nth_action Util.exn meta ztac ctxt i data focus >>> Up4.morph)
      in
        Up3.morph z >>= arr Mixin2.GCluster.get_stripped_goals
        >>= (fn goals => ZB.update_zipper3 (lookup_cons_goals goals) z)
      end)
    fun init _ focus z = Node.cons3 Util.exn meta [(focus, cons_actions)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]

declare [[zip_parse \<open>(@{binding rule}, Zip.Rule.parse_method)\<close>]]
declare [[zip_parse \<open>(@{binding match}, Zip.Match.parse_method)\<close>]]
declare [[zip_parse \<open>(@{binding urule}, Zip.URule.parse_method)\<close>]]

subsubsection \<open>Simplifier\<close>

declare [[zip_init_gc \<open>
  let
    open Zippy; open ZLPC MU; open A Mo
    val name = "asm_full_simp"
    val id = Zippy_Identifier.make (SOME @{here}) name
    val tacs = (safe_asm_full_simp_tac, asm_full_simp_tac)
    fun f_timeout ctxt i state n time = (@{log Logger.WARN Zip.Simp.logger} ctxt
      (fn _ => Pretty.breaks [
          Pretty.block [Pretty.str (name ^ " timeout at pull number "), SpecCheck_Show.int n,
            Pretty.str " after ", Pretty.str (Time.print time), Pretty.str " seconds."],
          Pretty.block [Pretty.str "Called on subgoal ", SpecCheck_Show.term ctxt (Thm.prem_of state i)],
          Pretty.str (implode ["Consider removing ", name,
            " for this proof, increase/disable the timeout, or check for looping simp rules."])
        ] |> Pretty.block0 |> Pretty.string_of);
      NONE)
    (*FIXME: why is the simplifier raising Option.Option and ERROR exceptions in some cases?*)
    fun handle_exn ctxt exn = (@{log Logger.WARN Zip.Simp.logger} ctxt
      (fn _ => "Simplifier raised unexpected " ^ exn ^ " exception. Returning NONE instead.");
      NONE)
    fun handle_exns_sq ctxt sq = Seq.make (fn _ =>
      sq |> Seq.pull |> Option.map (apsnd (handle_exns_sq ctxt))
      handle Option.Option => handle_exn ctxt "Option.Option" | ERROR _ => handle_exn ctxt "ERROR")
    fun wrap_tac tac ctxt i state = Zip.Simp.Extended_Data.wrap_simp_tac
      (f_timeout ctxt i state) (fn ctxt => handle_exns_sq ctxt oo tac ctxt) ctxt i state
    val (safe_tac, tac) = apply2 wrap_tac (safe_asm_full_simp_tac, asm_full_simp_tac)
    val update = Library.maps snd
      #> LGoals_Pos_Copy.partition_update_gcposs_gclusters_gclusters (Zip.Run.init_gposs true)
    val mk_cud = Result_Action.copy_update_data_empty_changed
    open Base_Data
    val costs_progress = ((Cost.LOW, AAMeta.P.promising), (Cost.LOW3, AAMeta.P.promising))
    val madd_safe = fst
    fun mk_meta (cost, progress) = A.K (Library.K (Library.K (AAMeta.metadata
      {cost = cost, progress = progress})))
    val (mk_meta_safe, mk_meta_unsafe) = apply2 mk_meta costs_progress
    val (presultsq_safe, presultsq_unsafe) =
      apply2 (fst #> Zip.PResults.enum_scale_presultsq_default) costs_progress
    val data = Simp.gen_data Util.exn id name safe_tac tac update mk_cud
      madd_safe mk_meta_safe mk_meta_unsafe presultsq_safe presultsq_unsafe
    fun init _ focus z =
      Tac.cons_action_cluster Util.exn (Base_Data.ACMeta.no_descr id) [(focus, data)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]

declare [[zip_parse add: \<open>(@{binding simp}, Zip.Simp.parse_extended [])\<close>
  and default: \<open>@{binding simp}\<close>]]

end
