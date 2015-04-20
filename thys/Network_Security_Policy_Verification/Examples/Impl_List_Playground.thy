theory Impl_List_Playground
imports "../TopoS_Impl"
begin


text{*The executbale models and the composition theory. We can build examples here*}

abbreviation "V\<equiv>TopoS_Vertices.V"



definition testGraph :: "vString list_graph" where
  "testGraph \<equiv> \<lparr> nodesL = [V ''Master'', V ''Slave1'', V ''Slave2'', V ''other1'', V ''other2''], 
                 edgesL = [(V ''Master'', V ''Slave1'')] \<rparr>"

lemma "wf_list_graph testGraph" by eval

definition req1 ::"(vString SecurityInvariant)" where
  "req1 \<equiv> new_configured_list_SecurityInvariant SINVAR_SecGwExt_impl.SINVAR_LIB_SecurityGatewayExtended \<lparr> 
      node_properties = [V ''Master'' \<mapsto> SecurityGateway,
                         V ''Slave1'' \<mapsto> DomainMember,
                         V ''Slave2'' \<mapsto> DomainMember], 
      model_global_properties = () 
      \<rparr>"


definition "req2 \<equiv> new_configured_list_SecurityInvariant SINVAR_NoRefl_impl.SINVAR_LIB_NoRefl \<lparr> 
      node_properties = [V ''Master'' \<mapsto> Refl,
                         V ''other1'' \<mapsto> Refl,
                         V ''other2'' \<mapsto> Refl], 
      model_global_properties = () 
      \<rparr>"

definition "reqs = [req1, req2]"


definition "max_network = generate_valid_topology reqs 
      \<lparr>nodesL = nodesL testGraph, edgesL = List.product (nodesL testGraph) (nodesL testGraph) \<rparr>"

value "max_network"

ML{*
visualize_graph @{context} @{term "reqs"} @{term "max_network"};
*}

end
