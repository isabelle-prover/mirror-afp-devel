(*  Title:      Zippy/zippy_instance_resolves_simp.ML
    Author:     Kevin Kappelmann

Basic setup for a prover supporting resolution and simplification.
*)
functor Zippy_Instance_Resolves_Simp(
    structure FI : FUNCTOR_INSTANCE_BASE
    structure Z : ZIPPY_INSTANCE_TACTIC
    structure TI : TERM_INDEX
    val resolve_init_args : (Z.Tac_AAM.mk_meta,
      int -> @{AllT_args} Z.Base_Data.PAction.action,
      Z.Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z.ZLPC.Z2.zipper) Z.emorph,
      @{AllT_args} Z.Result_Action.mk_copy_update_data,
      @{AllT_args} Z.PResults.presultsq,
      thm * (term * (thm,
        Z.Tac_AAM.mk_meta,
        int -> @{AllT_args} Z.Base_Data.PAction.action,
        (Z.Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z.ZLPC.Z2.zipper) Z.emorph) list,
        @{AllT_args} Z.Result_Action.mk_copy_update_data,
        @{AllT_args} Z.PResults.presultsq)
        Zippy_Instance_Hom_Changed_Goals_Data_Args.PD.entries) -> bool)
        Zippy_Instance_Hom_Changed_Goals_Data_Args.PDC.entries
    val simp_init_args : Extended_Simp_Data_Args.args
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
    structure Log_Base : ZIPPY_LOGGER_MIXIN_BASE
  ) =
struct
structure FI =  Functor_Instance(FI)
structure Logging =
struct
  val logger = Logger.setup_new_logger zippy_base_logger FI.name
  structure Rule = Zippy_Logger_Mixin_Base(val parent_logger = logger; val name = "Rule")
  structure Match = Zippy_Logger_Mixin_Base(val parent_logger = logger; val name = "Match")
  structure Update_Goal_Cluster = Zippy_Logger_Mixin_Base(val parent_logger = logger
    val name = "Update_Goal_Cluster")
end

val binding = Binding.make (FI.id, FI.pos)

(* resolution with higher-order unification*)
\<^functor_instance>\<open>struct_name: Rule
  functor_name: Zippy_Instance_Resolves_Data
  id: \<open>FI.prefix_id "rule"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    structure Z = Z
    structure TI = Discrimination_Tree
    val init_args = resolve_init_args
    structure Log = Logging.Rule\<close>\<close>

(* resolution with higher-order matching*)
\<^functor_instance>\<open>struct_name: Match
  functor_name: Zippy_Instance_Resolves_Data
  id: \<open>FI.prefix_id "match"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    structure Z = Z
    structure TI = Discrimination_Tree
    val init_args = resolve_init_args
    structure Log = Logging.Match\<close>\<close>

(* simplification *)
structure Simp =
struct
  val logger = Logger.setup_new_logger Logging.logger "Simp"
  \<^functor_instance>\<open>struct_name: Extended_Data
    functor_name: Extended_Simp_Data
    id: \<open>FI.prefix_id "simp"\<close>
    path: \<open>FI.struct_op "Simp"\<close>
    more_args: \<open>
      structure Z = Z
      val init_args = simp_init_args
      val parent_logger = logger\<close>\<close>
  local
    (*modified version of old section parser in Method that allows backtracking to alternatives
    when parsing theorems*)
    fun app {init, attribute,...} thms context =
      fold_map (Thm.apply_attribute attribute) thms (Context.map_proof init context)
    fun section ss = Scan.lift (Scan.first ss) --
      (Scan.repeats (Scan.unless (Scan.lift (Scan.first ss)) Parse_Util.multi_thm))
      :|-- (fn (m, ths) => Scan.depend (fn context => Scan.succeed (snd (app m ths context), ())))

    fun parse_simp_modifiers more_mods = Simplifier.simp_modifiers' @ more_mods |> section
    val parse_extended_data = Scan.depend (fn context => Extended_Data.parse_attribute
      >> (fn attr => (ML_Attribute_Util.attribute_map_context attr context, ())))
  in
  fun parse_extended more_mods = Scan.repeat1 (parse_extended_data || parse_simp_modifiers more_mods
      || Parse_Util.fail (K "extended simp modifers expected"))
    >> K ()
  end
end

(* initialisation and runs *)
structure Run =
struct
local open Z
  structure Goals = Zippy_Goals_Mixin_Base(
    structure GClusters = Mixin_Base1.GClusters; structure GCluster = Mixin_Base2.GCluster)
  structure Goals_Pos = Zippy_Goals_Pos_Mixin_Base(open Goals; structure GPU = Base_Data.Tac_Res.GPU)
in
structure Init_Goal_Cluster = Zippy_Update_Goal_Cluster_Mixin(
  structure Z = Zippy_Enum_Mixin(Zippy_Enum_Mixin_Base(structure Z = ZLPC; structure Co = Co))
  structure UGC = \<^functor_instance>\<open>
    functor_name: Zippy_Update_Goal_Cluster_Mixin_Base
    id: \<open>FI.prefix_id "init_gc"\<close>
    path: \<open>FI.struct_op "Run.Init_Goal_Cluster"\<close>
    more_args: \<open>open Goals_Pos
      structure M = Z
      structure Log = Logging.Update_Goal_Cluster\<close>\<close>
  structure Ctxt = Ctxt; structure Log = Logging; structure Log_Base = Log_Base
  \<^imap>\<open>\<open>{i}\<close> => \<open>structure Show{i} = Show.Zipper{i}\<close>\<close>)

fun init_gposs sort = (if sort then Goals_Pos.GPU.F.sort_goals else Goals_Pos.GPU.F.goals)
  #> Init_Goal_Cluster.update
val init_gpos = Goals_Pos.GPU.F.single #> Init_Goal_Cluster.update
end
end
end
