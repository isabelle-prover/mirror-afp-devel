theory SINVAR_DomainHierarchyNG_impl
imports SINVAR_DomainHierarchyNG "../TopoS_Interface_impl"
begin


subsubsection {* SecurityInvariant DomainHierarchy List Implementation *}

code_identifier code_module SINVAR_DomainHierarchyNG_impl => (Scala) SINVAR_DomainHierarchyNG

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> domainNameTrust) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (s, r) \<in> set (edgesL G). (nP r) \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t (nP s))"


fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> domainNameTrust) \<Rightarrow> domainTree \<Rightarrow> bool" where
  "verify_globals G nP tree = (\<forall> v \<in> set (nodesL G). 
    case (nP v) of Unassigned \<Rightarrow> True | DN (level, trust) \<Rightarrow> valid_hierarchy_pos tree level
   )"




definition DomainHierarchyNG_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> domainNameTrust) \<Rightarrow> ('v \<times> 'v) list list" where
  "DomainHierarchyNG_offending_list G nP = (if sinvar G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (s,r) \<Rightarrow> \<not> (nP r) \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t (nP s) ] ])"



lemma "DomainHierarchyNG.node_props P = 
  (\<lambda>i. case node_properties P i of None \<Rightarrow> SINVAR_DomainHierarchyNG.default_node_properties | Some property \<Rightarrow> property)"
by(fact SecurityInvariant.node_props.simps[OF TopoS_DomainHierarchyNG, of "P"])

definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_DomainHierarchyNG.default_node_properties))"
(*lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_DomainHierarchy.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done*)

(*TODO does this work?*)
lemma[code_unfold]: "DomainHierarchyNG.node_props P = NetModel_node_props P"
by(simp add: NetModel_node_props_def)

definition "DomainHierarchyNG_eval G P = (wf_list_graph G \<and> 
  verify_globals G (SecurityInvariant.node_props SINVAR_DomainHierarchyNG.default_node_properties P) (model_global_properties P) \<and> 
  sinvar G (SecurityInvariant.node_props SINVAR_DomainHierarchyNG.default_node_properties P))"


interpretation DomainHierarchyNG_impl:TopoS_List_Impl 
  where default_node_properties=SINVAR_DomainHierarchyNG.default_node_properties
  and sinvar_spec=SINVAR_DomainHierarchyNG.sinvar
  and sinvar_impl=sinvar
  and verify_globals_spec=SINVAR_DomainHierarchyNG.verify_globals
  and verify_globals_impl=verify_globals
  and receiver_violation=SINVAR_DomainHierarchyNG.receiver_violation
  and offending_flows_impl=DomainHierarchyNG_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=DomainHierarchyNG_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(simp add: TopoS_DomainHierarchyNG list_graph_to_graph_def)
 apply(rule conjI)
  apply(simp add: list_graph_to_graph_def DomainHierarchyNG_offending_set DomainHierarchyNG_offending_set_def DomainHierarchyNG_offending_list_def)
 apply(rule conjI)
  apply(simp only: NetModel_node_props_def)
  apply(metis DomainHierarchyNG.node_props.simps DomainHierarchyNG.node_props_eq_node_props_formaldef)
 apply(simp only: DomainHierarchyNG_eval_def)
 apply(intro allI)
 apply(rule TopoS_eval_impl_proofrule[OF TopoS_DomainHierarchyNG])
 apply(simp_all add: list_graph_to_graph_def)
done


subsubsection {* DomainHierarchyNG packing *}
  definition SINVAR_LIB_DomainHierarchyNG :: "('v::vertex, domainNameTrust, domainTree) TopoS_packed" where
    "SINVAR_LIB_DomainHierarchyNG \<equiv> 
    \<lparr> nm_name = ''DomainHierarchyNG'', 
      nm_receiver_violation = SINVAR_DomainHierarchyNG.receiver_violation,
      nm_default = SINVAR_DomainHierarchyNG.default_node_properties, 
      nm_sinvar = sinvar,
      nm_verify_globals = verify_globals,
      nm_offending_flows = DomainHierarchyNG_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = DomainHierarchyNG_eval
      \<rparr>"
  interpretation SINVAR_LIB_DomainHierarchyNG_interpretation: TopoS_modelLibrary SINVAR_LIB_DomainHierarchyNG 
      SINVAR_DomainHierarchyNG.sinvar SINVAR_DomainHierarchyNG.verify_globals
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_DomainHierarchyNG_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)






text {*Examples:*}
definition example_TUM_net :: "vString list_graph" where
  "example_TUM_net \<equiv> \<lparr> nodesL=[TopoS_Vertices.V ''Gateway'', TopoS_Vertices.V ''LowerSVR'', TopoS_Vertices.V ''UpperSRV''], 
        edgesL=[
          (TopoS_Vertices.V ''Gateway'',TopoS_Vertices.V ''LowerSVR''), (TopoS_Vertices.V ''Gateway'',TopoS_Vertices.V ''UpperSRV''), 
          (TopoS_Vertices.V ''LowerSVR'', TopoS_Vertices.V ''Gateway''),
          (TopoS_Vertices.V ''UpperSRV'', TopoS_Vertices.V ''Gateway'')
        ] \<rparr>"
value "wf_list_graph example_TUM_net"

definition example_TUM_config :: "vString \<Rightarrow> domainNameTrust" where
  "example_TUM_config \<equiv> ((\<lambda> e. default_node_properties)
        (TopoS_Vertices.V ''Gateway'':= DN (''ACD''--''AISD''--Leaf, 1),
         TopoS_Vertices.V ''LowerSVR'':= DN (''ACD''--''AISD''--Leaf, 0),
         TopoS_Vertices.V ''UpperSRV'':= DN (''ACD''--Leaf, 0)
       ))"

definition example_TUM_hierarchy :: "domainTree" where
"example_TUM_hierarchy \<equiv> (Department ''ACD'' [
           Department ''AISD'' []
       ])"

value "verify_globals example_TUM_net example_TUM_config example_TUM_hierarchy"
value "sinvar     example_TUM_net example_TUM_config"

definition example_TUM_net_invalid where
"example_TUM_net_invalid \<equiv> example_TUM_net\<lparr>edgesL :=  
    (TopoS_Vertices.V ''LowerSRV'', TopoS_Vertices.V ''UpperSRV'')#(edgesL example_TUM_net)\<rparr>"

value "verify_globals example_TUM_net_invalid example_TUM_config example_TUM_hierarchy"
value "sinvar     example_TUM_net_invalid example_TUM_config"
value "DomainHierarchyNG_offending_list example_TUM_net_invalid example_TUM_config"


hide_const (open) NetModel_node_props

hide_const (open) sinvar verify_globals 

end
