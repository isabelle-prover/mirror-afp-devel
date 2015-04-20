theory Example
imports "../TopoS_Interface" "../TopoS_Library"
begin

subsection {* Network Graph and Security Requirements *}

  text{*We define the network*}
  definition example_net_secgw :: "nat list_graph" where
  "example_net_secgw \<equiv> \<lparr> nodesL = [1::nat,2,3, 8, 11,12], 
    edgesL = [
      (1,8),(8,2),(2,8),(8,1), 
      (8,11),(8,12), 
      (11,12)] \<rparr>"
  value "wf_list_graph example_net_secgw"


  text{*We add two security requirements*}
  definition NMParams_secgw_1 :: "(nat, secgw_member, unit) TopoS_Params" where
  "NMParams_secgw_1 \<equiv> \<lparr> node_properties = [1 \<mapsto> DomainMember, 
                                     2 \<mapsto> DomainMember, 
                                     3 \<mapsto> DomainMember,
                                     8 \<mapsto> SecurityGateway],
                                model_global_properties = () \<rparr>"


  definition NMParams_blptrusted_1 :: "(nat, SINVAR_BLPtrusted.node_config, unit) TopoS_Params" where
  "NMParams_blptrusted_1 \<equiv> \<lparr> node_properties = [1 \<mapsto> \<lparr> privacy_level = 1, trusted = False \<rparr>, 
                                     2 \<mapsto> \<lparr> privacy_level = 1, trusted = False \<rparr>, 
                                     3 \<mapsto> \<lparr> privacy_level = 1, trusted = False \<rparr>,
                                     8 \<mapsto> \<lparr> privacy_level = 0, trusted = True \<rparr>],
                                model_global_properties = () \<rparr>"

  text{*Both security requirements fulfilled?*}
  value "SecurityGateway_eval example_net_secgw NMParams_secgw_1"
  value "SINVAR_BLPtrusted_impl.BLP_eval example_net_secgw NMParams_blptrusted_1"


text{*Add violations!*}
  definition example_net_secgw_invalid where
  "example_net_secgw_invalid \<equiv> example_net_secgw\<lparr>edgesL := (1,11)#(11,1)#(11,8)#(1,2)#(edgesL example_net_secgw)\<rparr>"

  text{*Security Requirement still fulfilled?*}
  value "SecurityGateway_eval example_net_secgw_invalid NMParams_secgw_1"
  text{*Whom to blame?*}
  value "SecurityGatewayExtended_offending_list example_net_secgw_invalid (SINVAR_SecGwExt_impl.NetModel_node_props NMParams_secgw_1)"

  text{*Security Requirement still fulfilled?*}
  value "SINVAR_BLPtrusted_impl.BLP_eval example_net_secgw_invalid NMParams_blptrusted_1"
  text{*Whom to blame?*}
  value "SINVAR_BLPtrusted_impl.BLP_offending_list example_net_secgw_invalid (SINVAR_BLPtrusted_impl.NetModel_node_props  NMParams_blptrusted_1)"


end
