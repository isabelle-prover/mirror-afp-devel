theory SINVAR_SecGwExt_impl
imports SINVAR_SecGwExt "../TopoS_Interface_impl"
begin

code_identifier code_module SINVAR_SecGwExt_impl => (Scala) SINVAR_SecGwExt

subsubsection {* SecurityInvariant SecurityGatewayExtended List Implementation *}

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> SINVAR_SecGwExt.secgw_member) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> set (edgesL G). e1 \<noteq> e2 \<longrightarrow> SINVAR_SecGwExt.allowed_secgw_flow (nP e1) (nP e2))"

fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> SINVAR_SecGwExt.secgw_member) \<Rightarrow> unit \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"


definition SecurityGatewayExtended_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> secgw_member) \<Rightarrow> ('v \<times> 'v) list list" where
  "SecurityGatewayExtended_offending_list G nP = (if sinvar G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> e1 \<noteq> e2 \<and> \<not> allowed_secgw_flow (nP e1) (nP e2)] ])"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_SecGwExt.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_SecGwExt.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "SecurityGateway_eval G P = (wf_list_graph G \<and> 
  verify_globals G (SecurityInvariant.node_props SINVAR_SecGwExt.default_node_properties P) (model_global_properties P) \<and> 
  sinvar G (SecurityInvariant.node_props SINVAR_SecGwExt.default_node_properties P))"


interpretation SecurityGateway_impl:TopoS_List_Impl 
  where default_node_properties=SINVAR_SecGwExt.default_node_properties
  and sinvar_spec=SINVAR_SecGwExt.sinvar
  and sinvar_impl=sinvar
  and verify_globals_spec=SINVAR_SecGwExt.verify_globals
  and verify_globals_impl=verify_globals
  and receiver_violation=SINVAR_SecGwExt.receiver_violation
  and offending_flows_impl=SecurityGatewayExtended_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=SecurityGateway_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(simp add: TopoS_SecurityGatewayExtended list_graph_to_graph_def)
 apply(rule conjI)
  apply(simp add: list_graph_to_graph_def SecurityGatewayExtended_offending_set SecurityGatewayExtended_offending_set_def SecurityGatewayExtended_offending_list_def)
 apply(rule conjI)
  apply(simp only: NetModel_node_props_def)
  apply(metis SecurityGatewayExtended.node_props.simps SecurityGatewayExtended.node_props_eq_node_props_formaldef)
 apply(simp only: SecurityGateway_eval_def)
 apply(simp add: TopoS_eval_impl_proofrule[OF TopoS_SecurityGatewayExtended])
 apply(simp_all add: list_graph_to_graph_def)
done


subsubsection {* SecurityGateway packing *}
  definition SINVAR_LIB_SecurityGatewayExtended :: "('v::vertex, secgw_member, unit) TopoS_packed" where
    "SINVAR_LIB_SecurityGatewayExtended \<equiv> 
    \<lparr> nm_name = ''SecurityGatewayExtended'', 
      nm_receiver_violation = SINVAR_SecGwExt.receiver_violation,
      nm_default = SINVAR_SecGwExt.default_node_properties, 
      nm_sinvar = sinvar,
      nm_verify_globals = verify_globals,
      nm_offending_flows = SecurityGatewayExtended_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = SecurityGateway_eval
      \<rparr>"
  interpretation SINVAR_LIB_SecurityGatewayExtended_interpretation: TopoS_modelLibrary SINVAR_LIB_SecurityGatewayExtended 
      SINVAR_SecGwExt.sinvar SINVAR_SecGwExt.verify_globals
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_SecurityGatewayExtended_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)


text {* Examples*}
  definition example_net_secgw :: "nat list_graph" where
  "example_net_secgw \<equiv> \<lparr> nodesL = [1::nat,2, 3, 8,9, 11,12], 
    edgesL = [(3,8),(8,3),(2,8),(8,1),(1,9),(9,2),(2,9),(9,1), (1,3), (8,11),(8,12), (11,9), (11,3), (11,12)] \<rparr>"
  value "wf_list_graph example_net_secgw"
  
  definition example_conf_secgw where
  "example_conf_secgw \<equiv> ((\<lambda>e. SINVAR_SecGwExt.default_node_properties)
    (1 := DomainMember, 2:= DomainMember, 3:= AccessibleMember,
     8:= SecurityGateway, 9:= SecurityGatewayIN))" 
  
  export_code sinvar in SML
  definition "test = sinvar \<lparr> nodesL=[1::nat], edgesL=[] \<rparr> (\<lambda>_. SINVAR_SecGwExt.default_node_properties)"
  export_code test in SML
  value(**) "sinvar \<lparr> nodesL=[1::nat], edgesL=[] \<rparr> (\<lambda>_. SINVAR_SecGwExt.default_node_properties)"

  value(**) "sinvar example_net_secgw example_conf_secgw"
  value(**) "SecurityGateway_offending_list example_net_secgw example_conf_secgw"


  definition example_net_secgw_invalid where
  "example_net_secgw_invalid \<equiv> example_net_secgw\<lparr>edgesL := (3,1)#(11,1)#(11,8)#(1,2)#(edgesL example_net_secgw)\<rparr>"

  value(**) "sinvar example_net_secgw_invalid example_conf_secgw"
  value(**) "SecurityGateway_offending_list example_net_secgw_invalid example_conf_secgw"


hide_const (open) NetModel_node_props
hide_const (open) sinvar verify_globals

end
