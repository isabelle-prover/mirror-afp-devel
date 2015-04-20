theory SINVAR_ACLcommunicateWith_impl
imports SINVAR_ACLcommunicateWith "../TopoS_Interface_impl"
begin

code_identifier code_module SINVAR_ACLcommunicateWith_impl => (Scala) SINVAR_ACLcommunicateWith


subsubsection {* List Implementation *}

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> 'v access_list) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> v \<in> set (nodesL G). accesses_okay (nP v) (set (succ_tran G v)))"

fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> 'v access_list) \<Rightarrow> unit \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"


definition "NetModel_node_props (P::('v::vertex, 'v access_list, 'b) TopoS_Params) = 
  (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_ACLcommunicateWith.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_ACLcommunicateWith.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "ACLcommunicateWith_offending_list = Generic_offending_list sinvar"

definition "ACLcommunicateWith_eval G P = (wf_list_graph G \<and> 
  verify_globals G (SecurityInvariant.node_props SINVAR_ACLcommunicateWith.default_node_properties P) (model_global_properties P) \<and> 
  sinvar G (SecurityInvariant.node_props SINVAR_ACLcommunicateWith.default_node_properties P))"


lemma sinvar_correct: "wf_list_graph G \<Longrightarrow> SINVAR_ACLcommunicateWith.sinvar (list_graph_to_graph G) nP = sinvar G nP"
by (metis SINVAR_ACLcommunicateWith.sinvar.simps SINVAR_ACLcommunicateWith_impl.sinvar.simps graph.select_convs(1) list_graph_to_graph_def succ_tran_correct)


interpretation SINVAR_ACLcommunicateWith_impl:TopoS_List_Impl 
  where default_node_properties=SINVAR_ACLcommunicateWith.default_node_properties
  and sinvar_spec=SINVAR_ACLcommunicateWith.sinvar
  and sinvar_impl=sinvar
  and verify_globals_spec=SINVAR_ACLcommunicateWith.verify_globals
  and verify_globals_impl=verify_globals
  and receiver_violation=SINVAR_ACLcommunicateWith.receiver_violation
  and offending_flows_impl=ACLcommunicateWith_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=ACLcommunicateWith_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(rule conjI)
   apply(simp add: TopoS_ACLcommunicateWith)
  apply(rule conjI)
   apply(intro allI impI)
   apply(fact sinvar_correct)
  apply(simp)
 apply(rule conjI)
  apply(unfold ACLcommunicateWith_offending_list_def)
  apply(intro allI impI)
  apply(rule Generic_offending_list_correct)
   apply(assumption)
  apply(simp only: sinvar_correct)
 apply(rule conjI)
  apply(intro allI)
  apply(simp only: NetModel_node_props_def)
  apply(metis ACLcommunicateWith.node_props.simps ACLcommunicateWith.node_props_eq_node_props_formaldef)
 apply(simp only: ACLcommunicateWith_eval_def)
 apply(intro allI impI)
 apply(rule TopoS_eval_impl_proofrule[OF TopoS_ACLcommunicateWith])
  apply(simp only: sinvar_correct)
 apply(simp)
done


subsubsection {* packing *}
  definition SINVAR_LIB_ACLcommunicateWith:: "('v::vertex, 'v access_list, unit) TopoS_packed" where
    "SINVAR_LIB_ACLcommunicateWith \<equiv> 
    \<lparr> nm_name = ''ACLcommunicateWith'', 
      nm_receiver_violation = SINVAR_ACLcommunicateWith.receiver_violation,
      nm_default = SINVAR_ACLcommunicateWith.default_node_properties, 
      nm_sinvar = sinvar,
      nm_verify_globals = verify_globals,
      nm_offending_flows = ACLcommunicateWith_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = ACLcommunicateWith_eval
      \<rparr>"
  interpretation SINVAR_LIB_ACLcommunicateWith_interpretation: TopoS_modelLibrary SINVAR_LIB_ACLcommunicateWith
      SINVAR_ACLcommunicateWith.sinvar SINVAR_ACLcommunicateWith.verify_globals
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_ACLcommunicateWith_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)



text {* Examples*}
  text{*
    1 can acceess 2 and 3
    2 can access 3
  *}
  definition exampleG :: "nat list_graph" where
    "exampleG \<equiv> \<lparr> nodesL = [1, 2, 3],
                    edgesL = [(1,2), (2,3)]\<rparr>"

  definition examplenP :: "nat \<Rightarrow> nat access_list" where
    "examplenP \<equiv> ((\<lambda>v. SINVAR_ACLcommunicateWith.default_node_properties)
                    (1 := AccessList [2,3]))
                    (2 := AccessList [3])"

  lemma "sinvar exampleG examplenP" by eval
  value "ACLcommunicateWith_offending_list exampleG examplenP"

  hide_const exampleG examplenP



hide_const (open) NetModel_node_props
hide_const (open) sinvar verify_globals

end
