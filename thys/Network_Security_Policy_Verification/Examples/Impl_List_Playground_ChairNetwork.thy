theory Impl_List_Playground_ChairNetwork
imports "../TopoS_Impl"
begin


text{*An example of our chair network [simplified]*}

text{*Our access control view on the network*}
  definition ChairNetwork_empty :: "string list_graph" where
    "ChairNetwork_empty \<equiv> \<lparr> nodesL = [''WebSrv'', ''FilesSrv'', ''PrinterBW'',
                                ''PrinterColor'', ''Students'',
                                ''Employees'', ''EReachable'',
                                ''Internet''],
                      edgesL = [] \<rparr>"
  
  lemma "wf_list_graph ChairNetwork_empty" by eval


subsection{*Our security requirements*}
  subsubsection{*We have a server with confidential data*}
    definition ConfidentialChairData::"(string SecurityInvariant)" where
      "ConfidentialChairData \<equiv> new_configured_list_SecurityInvariant SINVAR_BLPtrusted_impl.SINVAR_LIB_BLPtrusted \<lparr> 
          node_properties = [''FilesSrv'' \<mapsto> \<lparr> privacy_level = 1, trusted = False \<rparr>,
                             ''Employees'' \<mapsto> \<lparr> privacy_level = 0, trusted = True \<rparr>,
                             ''EReachable'' \<mapsto> \<lparr> privacy_level = 0, trusted = True \<rparr>], 
          model_global_properties = () 
          \<rparr>"


  (*
  subsubsection{*We have a hierarchical printing policy*}
    definition "PrintingHierarchy_nodes=[''Employees''\<mapsto> DN (''ColorPrinting''--Leaf, 0),
                           ''PrinterColor''\<mapsto> DN (''ColorPrinting''--''Printer''--Leaf, 0),
                           ''Students''\<mapsto> DN (''ColorPrinting''--''BwPrinting''--Leaf, 0),
                           ''PrinterBW''\<mapsto> DN (''ColorPrinting''--''BwPrinting''--''Printer''--Leaf, 0)]"
    definition "PrintingHierarchy_tree=Department ''ColorPrinting'' [
              Department ''Printer'' [], 
              Department ''BwPrinting'' [
                  Department ''Printer'' []]]"
    definition PrintingHierarchy::"string SecurityInvariant" where
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
          node_properties = [''PrinterColor'' \<mapsto> Master [''Employees'', ''EReachable''],
                             ''PrinterBW'' \<mapsto> Master [''Employees'', ''EReachable'', ''Students''],
                             ''Employees'' \<mapsto> Care,
                             ''EReachable'' \<mapsto> Care,
                             ''Students'' \<mapsto> Care], 
          model_global_properties = () 
          \<rparr>"

  subsubsection{* Printers are information sinks *}
    definition "PrintingSink \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_Sink \<lparr> 
          node_properties = [''PrinterColor'' \<mapsto> Sink,
                             ''PrinterBW'' \<mapsto> Sink], 
          model_global_properties = () 
          \<rparr>"



  subsubsection{*Students may access each other but are not accessible from the outside*}
    definition "StudentSubnet \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = [''Students'' \<mapsto> Member, ''Employees'' \<mapsto> Member, ''EReachable'' \<mapsto> InboundGateway], 
          model_global_properties = () 
          \<rparr>"


  subsubsection{* The files server is only accessibly by employees*}
    definition "FilesSrcACL \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [''FilesSrv'' \<mapsto> Master [''Employees'', ''EReachable''],
                             ''Employees'' \<mapsto> Care,
                             ''EReachable'' \<mapsto> Care], 
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
