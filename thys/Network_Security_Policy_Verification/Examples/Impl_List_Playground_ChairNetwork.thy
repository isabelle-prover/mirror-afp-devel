theory Impl_List_Playground_ChairNetwork
imports "../TopoS_Impl"
begin


text{*An example of our chair network [simplified]*}

abbreviation "V\<equiv>TopoS_Vertices.V"

text{*Our access control view on the network*}
  definition ChairNetwork_empty :: "vString list_graph" where
    "ChairNetwork_empty \<equiv> \<lparr> nodesL = [V ''WebSrv'', V ''FilesSrv'', V ''PrinterBW'',
                                V ''PrinterColor'', V ''Students'',
                                V ''Employees'', V ''EReachable'',
                                V ''Internet''],
                      edgesL = [] \<rparr>"
  
  lemma "wf_list_graph ChairNetwork_empty" by eval


subsection{*Our security requirements*}
  subsubsection{*We have a server with confidential data*}
    definition ConfidentialChairData::"(vString SecurityInvariant)" where
      "ConfidentialChairData \<equiv> new_configured_list_SecurityInvariant SINVAR_BLPtrusted_impl.SINVAR_LIB_BLPtrusted \<lparr> 
          node_properties = [V ''FilesSrv'' \<mapsto> \<lparr> privacy_level = 1, trusted = False \<rparr>,
                             V ''Employees'' \<mapsto> \<lparr> privacy_level = 0, trusted = True \<rparr>,
                             V ''EReachable'' \<mapsto> \<lparr> privacy_level = 0, trusted = True \<rparr>], 
          model_global_properties = () 
          \<rparr>"


  (*
  subsubsection{*We have a hierarchical printing policy*}
    definition "PrintingHierarchy_nodes=[V ''Employees''\<mapsto> DN (''ColorPrinting''--Leaf, 0),
                           V ''PrinterColor''\<mapsto> DN (''ColorPrinting''--''Printer''--Leaf, 0),
                           V ''Students''\<mapsto> DN (''ColorPrinting''--''BwPrinting''--Leaf, 0),
                           V ''PrinterBW''\<mapsto> DN (''ColorPrinting''--''BwPrinting''--''Printer''--Leaf, 0)]"
    definition "PrintingHierarchy_tree=Department ''ColorPrinting'' [
              Department ''Printer'' [], 
              Department ''BwPrinting'' [
                  Department ''Printer'' []]]"
    definition PrintingHierarchy::"vString SecurityInvariant" where
      "PrintingHierarchy \<equiv> new_configured_list_SecurityInvariant SINVAR_DomainHierarchyNG_impl.SINVAR_LIB_DomainHierarchyNG \<lparr> 
        node_properties = PrintingHierarchy_nodes,
        model_global_properties = PrintingHierarchy_tree
        \<rparr>"
  
    --"verify globals, I admit, not very elegant"
    lemma "nm_verify_globals SINVAR_DomainHierarchyNG_impl.SINVAR_LIB_DomainHierarchyNG ChairNetwork_empty 
          (nm_node_props SINVAR_DomainHierarchyNG_impl.SINVAR_LIB_DomainHierarchyNG \<lparr> node_properties = PrintingHierarchy_nodes, model_global_properties = PrintingHierarchy_tree \<rparr>) PrintingHierarchy_tree" by eval
  *)
  subsubsection{* The color printer is only accessibly by employees, The black.white printer by employees and students*}
    definition "PrintingACL \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [V ''PrinterColor'' \<mapsto> Master [V ''Employees'', V ''EReachable''],
                             V ''PrinterBW'' \<mapsto> Master [V ''Employees'', V ''EReachable'', V ''Students''],
                             V ''Employees'' \<mapsto> Care,
                             V ''EReachable'' \<mapsto> Care,
                             V ''Students'' \<mapsto> Care], 
          model_global_properties = () 
          \<rparr>"

  subsubsection{* Printers are information sinks *}
    definition "PrintingSink \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_Sink \<lparr> 
          node_properties = [V ''PrinterColor'' \<mapsto> Sink,
                             V ''PrinterBW'' \<mapsto> Sink], 
          model_global_properties = () 
          \<rparr>"



  subsubsection{*Students may access each other but are not accessible from the outside*}
    definition "StudentSubnet \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = [V ''Students'' \<mapsto> Member, V ''Employees'' \<mapsto> Member, V ''EReachable'' \<mapsto> InboundGateway], 
          model_global_properties = () 
          \<rparr>"


  subsubsection{* The files server is only accessibly by employees*}
    definition "FilesSrcACL \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [V ''FilesSrv'' \<mapsto> Master [V ''Employees'', V ''EReachable''],
                             V ''Employees'' \<mapsto> Care,
                             V ''EReachable'' \<mapsto> Care], 
          model_global_properties = () 
          \<rparr>"


  subsubsection{*emplyees are reachable from the Internet*}
    (*nothing to do here*)

lemma "implc_sinvar ConfidentialChairData ChairNetwork_empty" by eval
lemma "implc_sinvar PrintingACL ChairNetwork_empty" by eval
lemma "implc_sinvar PrintingSink ChairNetwork_empty" by eval
lemma "implc_sinvar StudentSubnet ChairNetwork_empty" by eval
lemma "implc_sinvar FilesSrcACL ChairNetwork_empty" by eval

definition "ChairSecurityRequirements = [ConfidentialChairData, PrintingACL, PrintingSink, StudentSubnet, FilesSrcACL]"

value "implc_get_offending_flows ChairSecurityRequirements ChairNetwork_empty"
value "generate_valid_topology ChairSecurityRequirements ChairNetwork_empty"

value "List.product (nodesL ChairNetwork_empty) (nodesL ChairNetwork_empty)"

definition "ChairNetwork = generate_valid_topology ChairSecurityRequirements 
      \<lparr>nodesL = nodesL ChairNetwork_empty, edgesL = List.product (nodesL ChairNetwork_empty) (nodesL ChairNetwork_empty) \<rparr>"

lemma "all_security_requirements_fulfilled ChairSecurityRequirements ChairNetwork" by eval

value "ChairNetwork"

ML_val{*
visualize_graph @{context} @{term "ChairSecurityRequirements"} @{term "ChairNetwork"};
*}



end
