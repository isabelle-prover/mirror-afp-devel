theory Example_BLP
imports TopoS_Library
begin

definition BLPexample1::"bool" where
  "BLPexample1 \<equiv> (nm_eval SINVAR_LIB_BLPbasic) fabNet \<lparr> node_properties = [TopoS_Vertices.V ''PresenceSensor'' \<mapsto> 2, 
                                                  TopoS_Vertices.V ''Webcam'' \<mapsto> 3, 
                                                  TopoS_Vertices.V ''SensorSink'' \<mapsto> 3,
                                                  TopoS_Vertices.V ''Statistics'' \<mapsto> 3], model_global_properties = () \<rparr>"
definition BLPexample3::"(vString \<times> vString) list list" where
  "BLPexample3 \<equiv> (nm_offending_flows SINVAR_LIB_BLPbasic) fabNet ((nm_node_props SINVAR_LIB_BLPbasic) sensorProps_NMParams_try3)"

value "BLPexample1"
value "BLPexample3"


end
