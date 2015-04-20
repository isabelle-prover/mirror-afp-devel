theory SINVAR_BLPbasic_impl
imports SINVAR_BLPbasic "../TopoS_Interface_impl"
begin


subsubsection {* SecurityInvariant BLPbasic List Implementation *}

code_identifier code_module SINVAR_BLPbasic_impl => (Scala) SINVAR_BLPbasic

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> privacy_level) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> set (edgesL G). (nP e1) \<le> (nP e2))"

fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> privacy_level) \<Rightarrow> unit \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"

definition BLP_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> privacy_level) \<Rightarrow> ('v \<times> 'v) list list" where
  "BLP_offending_list G nP = (if sinvar G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> (nP e1) > (nP e2)] ])"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_BLPbasic.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_BLPbasic.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "BLP_eval G P = (wf_list_graph G \<and> 
  verify_globals G (SecurityInvariant.node_props SINVAR_BLPbasic.default_node_properties P) (model_global_properties P) \<and> 
  sinvar G (SecurityInvariant.node_props SINVAR_BLPbasic.default_node_properties P))"


interpretation BLPbasic_impl:TopoS_List_Impl
  where default_node_properties=SINVAR_BLPbasic.default_node_properties
  and sinvar_spec=SINVAR_BLPbasic.sinvar
  and sinvar_impl=sinvar
  and verify_globals_spec=SINVAR_BLPbasic.verify_globals
  and verify_globals_impl=verify_globals
  and receiver_violation=SINVAR_BLPbasic.receiver_violation
  and offending_flows_impl=BLP_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=BLP_eval
  apply(unfold TopoS_List_Impl_def)
  apply(rule conjI)
   apply(simp add: TopoS_BLPBasic)
   apply(simp add: list_graph_to_graph_def)
  apply(rule conjI)
   apply(simp add: list_graph_to_graph_def)
   apply(simp add: list_graph_to_graph_def BLP_offending_set BLP_offending_set_def BLP_offending_list_def)
  apply(rule conjI)
   apply(simp only: NetModel_node_props_def)
   apply(metis BLPbasic.node_props.simps BLPbasic.node_props_eq_node_props_formaldef)
  apply(simp only: BLP_eval_def)
  apply(simp add: TopoS_eval_impl_proofrule[OF TopoS_BLPBasic])
  apply(simp add: list_graph_to_graph_def)
 done



subsubsection {* BLPbasic packing *}
  definition SINVAR_LIB_BLPbasic :: "('v::vertex, privacy_level, unit) TopoS_packed" where
    "SINVAR_LIB_BLPbasic \<equiv> 
    \<lparr> nm_name = ''BLPbasic'', 
      nm_receiver_violation = SINVAR_BLPbasic.receiver_violation,
      nm_default = SINVAR_BLPbasic.default_node_properties, 
      nm_sinvar = sinvar,
      nm_verify_globals = verify_globals,
      nm_offending_flows = BLP_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = BLP_eval
      \<rparr>"
  interpretation SINVAR_LIB_BLPbasic_interpretation: TopoS_modelLibrary SINVAR_LIB_BLPbasic 
      SINVAR_BLPbasic.sinvar SINVAR_BLPbasic.verify_globals
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_BLPbasic_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)

subsubsection{* Example *}
  definition fabNet :: "vString list_graph" where
  "fabNet \<equiv> \<lparr> nodesL = [TopoS_Vertices.V ''Statistics'', TopoS_Vertices.V ''SensorSink'', TopoS_Vertices.V ''PresenceSensor'', TopoS_Vertices.V ''Webcam'', TopoS_Vertices.V ''TempSensor'', TopoS_Vertices.V ''FireSesnsor'',
                     TopoS_Vertices.V ''MissionControl1'', TopoS_Vertices.V ''MissionControl2'', TopoS_Vertices.V ''Watchdog'', TopoS_Vertices.V ''Bot1'', TopoS_Vertices.V ''Bot2''], 
              edgesL =[(TopoS_Vertices.V ''PresenceSensor'', TopoS_Vertices.V ''SensorSink''), (TopoS_Vertices.V ''Webcam'', TopoS_Vertices.V ''SensorSink''), 
                     (TopoS_Vertices.V ''TempSensor'', TopoS_Vertices.V ''SensorSink''),  (TopoS_Vertices.V ''FireSesnsor'', TopoS_Vertices.V ''SensorSink''),
                     (TopoS_Vertices.V ''SensorSink'', TopoS_Vertices.V ''Statistics''),
                     (TopoS_Vertices.V ''MissionControl1'', TopoS_Vertices.V ''Bot1''), (TopoS_Vertices.V ''MissionControl1'', TopoS_Vertices.V ''Bot2''),
                     (TopoS_Vertices.V ''MissionControl2'', TopoS_Vertices.V ''Bot2''),
                     (TopoS_Vertices.V ''Watchdog'', TopoS_Vertices.V ''Bot1''), (TopoS_Vertices.V ''Watchdog'', TopoS_Vertices.V ''Bot2'')] \<rparr>"
  value "wf_list_graph fabNet"


  definition sensorProps_try1 :: "vString \<Rightarrow> privacy_level" where
    "sensorProps_try1 \<equiv> (\<lambda> n. SINVAR_BLPbasic.default_node_properties)(TopoS_Vertices.V ''PresenceSensor'' := 2, TopoS_Vertices.V ''Webcam'' := 3)"
  value "BLP_offending_list fabNet sensorProps_try1"
  value "sinvar fabNet sensorProps_try1"

  definition sensorProps_try2 :: "vString \<Rightarrow> privacy_level" where
    "sensorProps_try2 \<equiv> (\<lambda> n. SINVAR_BLPbasic.default_node_properties)(TopoS_Vertices.V ''PresenceSensor'' := 2, TopoS_Vertices.V ''Webcam'' := 3, 
                                                       TopoS_Vertices.V ''SensorSink'' := 3)"
  value "BLP_offending_list fabNet sensorProps_try2"
  value "sinvar fabNet sensorProps_try2"

  definition sensorProps_try3 :: "vString \<Rightarrow> privacy_level" where
    "sensorProps_try3 \<equiv> (\<lambda> n. SINVAR_BLPbasic.default_node_properties)(TopoS_Vertices.V ''PresenceSensor'' := 2, TopoS_Vertices.V ''Webcam'' := 3, 
                                                       TopoS_Vertices.V ''SensorSink'' := 3, TopoS_Vertices.V ''Statistics'' := 3)"
  value "BLP_offending_list fabNet sensorProps_try3"
  value "sinvar fabNet sensorProps_try3"

  text {* Another parameter set for confidential controlling information*}
  definition sensorProps_conf :: "vString \<Rightarrow> privacy_level" where
    "sensorProps_conf \<equiv> (\<lambda> n. SINVAR_BLPbasic.default_node_properties)(TopoS_Vertices.V ''MissionControl1'' := 1, TopoS_Vertices.V ''MissionControl2'' := 2,
      TopoS_Vertices.V ''Bot1'' := 1, TopoS_Vertices.V ''Bot2'' := 2 )"
  value "BLP_offending_list fabNet sensorProps_conf"
  value "sinvar fabNet sensorProps_conf"


text {* Complete example:*}
  
  definition sensorProps_NMParams_try3 :: "(vString, nat, unit) TopoS_Params" where
  "sensorProps_NMParams_try3 \<equiv> \<lparr> node_properties = [TopoS_Vertices.V ''PresenceSensor'' \<mapsto> 2, 
                                                    TopoS_Vertices.V ''Webcam'' \<mapsto> 3, 
                                                    TopoS_Vertices.V ''SensorSink'' \<mapsto> 3,
                                                    TopoS_Vertices.V ''Statistics'' \<mapsto> 3],
                                model_global_properties = () \<rparr>"
  value "BLP_eval fabNet sensorProps_NMParams_try3"


export_code SINVAR_LIB_BLPbasic in Scala

hide_const (open) NetModel_node_props BLP_offending_list BLP_eval

hide_const (open) sinvar verify_globals

end
