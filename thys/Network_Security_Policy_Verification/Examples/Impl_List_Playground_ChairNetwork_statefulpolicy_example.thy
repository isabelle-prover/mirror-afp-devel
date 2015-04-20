theory Impl_List_Playground_ChairNetwork_statefulpolicy_example
imports "../TopoS_Impl"
begin


text{*An example of our chair network [simplified]*}

abbreviation "V\<equiv>TopoS_Vertices.V"

text{*Our access control view on the network*}
  definition ChairNetwork_empty :: "vString list_graph" where
    "ChairNetwork_empty \<equiv> \<lparr> nodesL = [V ''WebSrv'', V ''FilesSrv'', V ''Printer'',
                                V ''Students'',
                                V ''Employees'',
                                V ''Internet''],
                      edgesL = [] \<rparr>"
  
  lemma "wf_list_graph ChairNetwork_empty" by eval


subsection{*Our security requirements*}
  subsubsection{*We have a server with confidential data*}
    definition ConfidentialChairData::"(vString SecurityInvariant)" where
      "ConfidentialChairData \<equiv> new_configured_list_SecurityInvariant SINVAR_BLPtrusted_impl.SINVAR_LIB_BLPtrusted \<lparr> 
          node_properties = [V ''FilesSrv'' \<mapsto> \<lparr> privacy_level = 1, trusted = False \<rparr>,
                             V ''Employees'' \<mapsto> \<lparr> privacy_level = 0, trusted = True \<rparr>], 
          model_global_properties = () 
          \<rparr>"


  subsubsection{* accessibly by employees and students*}
    definition "PrintingACL \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [V ''Printer'' \<mapsto> Master [V ''Employees'', V ''Students''],
                             V ''Employees'' \<mapsto> Care,
                             V ''Students'' \<mapsto> Care], 
          model_global_properties = () 
          \<rparr>"

  subsubsection{* Printers are information sinks *}
    definition "PrintingSink \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_Sink \<lparr> 
          node_properties = [V ''Printer'' \<mapsto> Sink], 
          model_global_properties = () 
          \<rparr>"



  subsubsection{*Students and Employees may access each other but are not accessible from the outside*}
    definition "InternalSubnet \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = [V ''Students'' \<mapsto> Member, V ''Employees'' \<mapsto> Member], 
          model_global_properties = () 
          \<rparr>"


  subsubsection{* The files server is only accessibly by employees*}
    definition "FilesSrcACL \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [V ''FilesSrv'' \<mapsto> Master [V ''Employees''],
                             V ''Employees'' \<mapsto> Care], 
          model_global_properties = () 
          \<rparr>"


definition "ChairSecurityRequirements = [ConfidentialChairData, PrintingACL, PrintingSink, InternalSubnet, FilesSrcACL]"

lemma "\<forall>m \<in> set ChairSecurityRequirements. implc_sinvar m ChairNetwork_empty" by eval

value "implc_get_offending_flows ChairSecurityRequirements ChairNetwork_empty"
value "generate_valid_topology ChairSecurityRequirements ChairNetwork_empty"

value "List.product (nodesL ChairNetwork_empty) (nodesL ChairNetwork_empty)"

definition "ChairNetwork = generate_valid_topology ChairSecurityRequirements 
      \<lparr>nodesL = nodesL ChairNetwork_empty, edgesL = List.product (nodesL ChairNetwork_empty) (nodesL ChairNetwork_empty) \<rparr>"

value "ChairNetwork"


ML{*
visualize_graph @{context} @{term "ChairSecurityRequirements"} @{term "ChairNetwork"};
*}


definition "ChairNetwork_stateful_IFS = \<lparr> hostsL = nodesL ChairNetwork, flows_fixL = edgesL ChairNetwork, flows_stateL = filter_IFS_no_violations ChairNetwork ChairSecurityRequirements \<rparr>"
value "edgesL ChairNetwork"
value "filter_IFS_no_violations ChairNetwork ChairSecurityRequirements"
value "ChairNetwork_stateful_IFS"
lemma "set (flows_stateL ChairNetwork_stateful_IFS) \<subseteq> (set (flows_fixL ChairNetwork_stateful_IFS))" by eval (*must always hold*)
value "(set (flows_fixL ChairNetwork_stateful_IFS)) - set (flows_stateL ChairNetwork_stateful_IFS)"
(*only problems: printers!!!*)
value "stateful_list_policy_to_list_graph ChairNetwork_stateful_IFS"
lemma "set (filter_IFS_no_violations ChairNetwork [ConfidentialChairData]) = set (edgesL ChairNetwork)" by eval

definition "ChairNetwork_stateful_ACS = \<lparr> hostsL = nodesL ChairNetwork, flows_fixL = edgesL ChairNetwork, flows_stateL = filter_compliant_stateful_ACS ChairNetwork ChairSecurityRequirements \<rparr>"
value "edgesL ChairNetwork"
value "filter_compliant_stateful_ACS ChairNetwork ChairSecurityRequirements"
value "ChairNetwork_stateful_ACS"
lemma "set (flows_stateL ChairNetwork_stateful_ACS) \<subseteq> (set (flows_fixL ChairNetwork_stateful_ACS))" by eval (*must always hold*)
value "(set (flows_fixL ChairNetwork_stateful_ACS)) - set (flows_stateL ChairNetwork_stateful_ACS)"

(*flows that are already allowed in both directions are not marked as stateful*)
value "((set (flows_fixL ChairNetwork_stateful_ACS)) - set (flows_stateL ChairNetwork_stateful_ACS)) - set (backlinks (flows_fixL ChairNetwork_stateful_ACS))"

(*the new backflows*)
value "set (edgesL (stateful_list_policy_to_list_graph ChairNetwork_stateful_ACS)) - (set (edgesL ChairNetwork))"

(*the resulting ACS graph*)
value "stateful_list_policy_to_list_graph ChairNetwork_stateful_ACS"


value "generate_valid_stateful_policy_IFSACS ChairNetwork ChairSecurityRequirements"
value "generate_valid_stateful_policy_IFSACS_2 ChairNetwork ChairSecurityRequirements"
lemma "set (flows_fixL (generate_valid_stateful_policy_IFSACS ChairNetwork ChairSecurityRequirements)) = set (flows_fixL (generate_valid_stateful_policy_IFSACS_2 ChairNetwork ChairSecurityRequirements))" by eval
lemma "set (flows_stateL (generate_valid_stateful_policy_IFSACS ChairNetwork ChairSecurityRequirements)) = set (flows_stateL (generate_valid_stateful_policy_IFSACS_2 ChairNetwork ChairSecurityRequirements))" by eval


definition "ChairNetwork_stateful = generate_valid_stateful_policy_IFSACS ChairNetwork ChairSecurityRequirements"


ML_val{*
visualize_edges @{context} @{term "flows_fixL ChairNetwork_stateful"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]", @{term "flows_stateL ChairNetwork_stateful"})] ""; 
*}

(*these requirements impose no restrictoins on the stateful flows*)
definition "ChairNetwork_stateful_v2 = generate_valid_stateful_policy_IFSACS ChairNetwork [ConfidentialChairData, PrintingACL,  InternalSubnet, FilesSrcACL]"
ML_val{*
visualize_edges @{context} @{term "flows_fixL ChairNetwork_stateful_v2"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]", @{term "flows_stateL ChairNetwork_stateful_v2"})] ""; 
*}

(*The sink requirements imposes the restriction that the printer cannot answer*)
definition "ChairNetwork_stateful_v3 = generate_valid_stateful_policy_IFSACS ChairNetwork [PrintingSink]"
ML_val{*
visualize_edges @{context} @{term "flows_fixL ChairNetwork_stateful_v3"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]", @{term "flows_stateL ChairNetwork_stateful_v3"})] ""; 
*}

subsection{*An example of bad side-effects in access control policies*}

  definition ACL_not_with::"(vString SecurityInvariant)" where
    "ACL_not_with \<equiv> new_configured_list_SecurityInvariant SINVAR_ACLnotCommunicateWith_impl.SINVAR_LIB_ACLnotCommunicateWith \<lparr> 
        node_properties = [V ''A'' \<mapsto> {V ''C''},
                           V ''B'' \<mapsto> {},
                           V ''C'' \<mapsto> {}], 
        model_global_properties = () 
        \<rparr>"

  definition simple_network :: "vString list_graph" where
    "simple_network \<equiv> \<lparr> nodesL = [V ''A'', V ''B'', V ''C''],
                      edgesL = [(V ''B'', V ''A''), (V ''B'', V ''C'')] \<rparr>"
  
  lemma "wf_list_graph ChairNetwork_empty" by eval
  lemma "\<forall>m \<in> set [ACL_not_with]. implc_sinvar m simple_network" by eval


  lemma "implc_get_offending_flows [ACL_not_with] simple_network = []" by eval
  lemma "implc_get_offending_flows [ACL_not_with] 
    \<lparr> nodesL = [V ''A'', V ''B'', V ''C''], edgesL = [(V ''B'', V ''A''), (V ''B'', V ''C''), (V ''A'', V ''B'')] \<rparr> =
      [[(V ''B'', V ''C'')], [(V ''A'', V ''B'')]]" by eval
  lemma "implc_get_offending_flows [ACL_not_with] 
    \<lparr> nodesL = [V ''A'', V ''B'', V ''C''], edgesL = [(V ''B'', V ''A''), (V ''B'', V ''C''), (V ''C'', V ''B'')] \<rparr> =
      []" by eval

value "generate_valid_stateful_policy_IFSACS simple_network [ACL_not_with]"
value "generate_valid_stateful_policy_IFSACS_2 simple_network [ACL_not_with]"








subsection{*performance test*}
(*6 minutes , about 1.8k edges in graph, most of the times, no requirements apply, simply added some nodes, edges to the chair network. topology is valid*)
(*value "generate_valid_stateful_policy_IFSACS biggraph ChairSecurityRequirements"*)

end
