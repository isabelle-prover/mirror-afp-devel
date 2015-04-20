section{*Network Security Policy Verification*}
theory Network_Security_Policy_Verification
imports
  TopoS_Interface
  TopoS_Interface_impl
  TopoS_Library
  TopoS_Composition_Theory
  TopoS_Stateful_Policy
  TopoS_Composition_Theory_impl
  TopoS_Stateful_Policy_Algorithm
  TopoS_Stateful_Policy_impl
  TopoS_Impl
begin



section{*A small Tutorial*}

text{*We demonstrate usage of the executable theory.*}
text{*Everything that is indented and starts with `Interlude:' summarizes the main correctness proofs and can be skipped if only the implementation is concerned*}

subsection{*Policy*}
text{*The secuity policy is a directed graph.*}
definition policy :: "nat list_graph" where
    "policy \<equiv> \<lparr> nodesL = [1,2,3],
                edgesL = [(1,2), (2,2), (2,3)] \<rparr>"

text{*It is syntactically well-formed *}
lemma wf_list_graph_policy: "wf_list_graph policy" by eval

text{*In contrast, this is not a syntactically well-formed graph. *}
lemma "\<not> wf_list_graph \<lparr> nodesL = [1,2]::nat list, edgesL = [(1,2), (2,2), (2,3)] \<rparr>" by eval

text{*Our @{const policy} has three rules. *}
lemma "length (edgesL policy) = 3" by eval

subsection{*Security Invariants*}
text{*We construct a security invariant. Node @{term "2::nat"} has confidential data*}

definition BLP_security_clearances :: "nat \<rightharpoonup> SINVAR_BLPtrusted.node_config"where
  "BLP_security_clearances \<equiv> [2 \<mapsto> \<lparr> privacy_level = 1, trusted = False \<rparr>]"

definition BLP_m::"(nat SecurityInvariant)" where
    "BLP_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_BLPtrusted \<lparr> 
          node_properties = BLP_security_clearances, 
          model_global_properties = () 
          \<rparr>"


  text{*Interlude: @{const BLP_m} is a valid implementation of a SecurityInvariant*}
  definition BLP_m_spec :: "nat SecurityInvariant_configured option"where
    "BLP_m_spec \<equiv> new_configured_SecurityInvariant (
        SINVAR_BLPtrusted.sinvar,
        SINVAR_BLPtrusted.default_node_properties,
        SINVAR_BLPtrusted.receiver_violation,
        SecurityInvariant.node_props SINVAR_BLPtrusted.default_node_properties \<lparr> 
          node_properties = BLP_security_clearances, 
          model_global_properties = () 
        \<rparr>)"
  text{*Fist, we need to show that the formal definition obeys all requirements, @{const new_configured_SecurityInvariant} verifies this. To double check, we manually give the configuration.*}
  lemma BLP_m_spec: assumes "nP = (\<lambda> v. (case BLP_security_clearances v of Some c \<Rightarrow> c | None \<Rightarrow> SINVAR_BLPtrusted.default_node_properties))"
      shows "BLP_m_spec = Some \<lparr> 
              c_sinvar = (\<lambda>G. SINVAR_BLPtrusted.sinvar G nP),
              c_offending_flows = (\<lambda>G. SecurityInvariant_withOffendingFlows.set_offending_flows SINVAR_BLPtrusted.sinvar G nP),
              c_isIFS = SINVAR_BLPtrusted.receiver_violation
            \<rparr>" (is "BLP_m_spec = Some ?Spec")
  proof - 
    have NetModelLib: "TopoS_modelLibrary SINVAR_LIB_BLPtrusted SINVAR_BLPtrusted.sinvar SINVAR_BLPtrusted.verify_globals"
    by(unfold_locales)
    from assms have nP: "nP = nm_node_props SINVAR_LIB_BLPtrusted \<lparr> 
              node_properties = BLP_security_clearances, 
              model_global_properties = () 
            \<rparr>" by(simp add: fun_eq_iff SINVAR_LIB_BLPtrusted_def SINVAR_BLPtrusted_impl.NetModel_node_props_def)
  
    have "BLP_m_spec = new_configured_SecurityInvariant (SINVAR_BLPtrusted.sinvar, SINVAR_BLPtrusted.default_node_properties, SINVAR_BLPtrusted.receiver_violation, nP)"
    unfolding BLP_m_spec_def nP by(simp add: SINVAR_BLPtrusted_impl.NetModel_node_props_def SINVAR_LIB_BLPtrusted_def)
    also with TopoS_modelLibrary_yields_new_configured_SecurityInvariant[OF NetModelLib nP]
    have "\<dots> = Some ?Spec" by (simp add: SINVAR_LIB_BLPtrusted_def)
    finally show ?thesis by blast
  qed
  lemma valid_reqs_BLP: "valid_reqs [the BLP_m_spec]"
    by(simp add: valid_reqs_def)(metis BLP_m_spec_def BLPtrusted_impl.spec new_configured_SecurityInvariant.simps new_configured_SecurityInvariant_sound option.distinct(1) option.exhaust_sel)


  text{*Interlude: While @{const BLP_m} is executable code, we will now show that this executable code complies with its formal definition.*}
  lemma complies_BLP: "SecurityInvariant_complies_formal_def BLP_m (the BLP_m_spec)"
    unfolding BLP_m_def
    apply(rule new_configured_list_SecurityInvariant_complies)
       apply(simp_all add: BLP_m_spec_def)
     apply(unfold_locales)
    by(simp add: fun_eq_iff SINVAR_LIB_BLPtrusted_def SINVAR_BLPtrusted_impl.NetModel_node_props_def)



text{*We define the list of all security invariants of type @{typ "nat SecurityInvariant list"}.
     The type @{typ nat} is because the policy's nodes are of type @{typ nat}.*}
definition "security_invariants = [BLP_m]"


text{*We can see that the policy does not fulfill the security invariants. *}
lemma "\<not> all_security_requirements_fulfilled security_invariants policy" by eval

text{*We ask why. Obviously, node 2 leaks confidential data to node 3.*}
value "implc_get_offending_flows security_invariants policy"
lemma "implc_get_offending_flows security_invariants policy = [[(2, 3)]]" by eval

  text{*Interlude: the implementation @{const implc_get_offending_flows} corresponds to the formal definition @{const get_offending_flows}*}
  lemma "set ` set (implc_get_offending_flows (get_impl [(BLP_m, the BLP_m_spec)]) policy) = get_offending_flows (get_spec [(BLP_m, the BLP_m_spec)]) (list_graph_to_graph policy)"
  apply(rule implc_get_offending_flows_complies)
   by(simp_all add: complies_BLP wf_list_graph_policy)
  

text{*
Visualization of the violation (only in interactive mode)
*}
ML_val{*
visualize_graph @{context} @{term "security_invariants"} @{term "policy"};
*}

text{*Experimental: the config (only one) can be added to the end.*}
ML_val{*
visualize_graph_header @{context} @{term "security_invariants"} @{term "policy"} @{term "BLP_security_clearances"};
*}


text{*
The policy has a flaw. We throw it away and generate a new one which fulfills the invariants.
*}
definition "max_policy = generate_valid_topology security_invariants \<lparr>nodesL = nodesL policy, edgesL = List.product (nodesL policy) (nodesL policy) \<rparr>"

  text{*Interlude: the implementation @{const implc_get_offending_flows} corresponds to the formal definition @{const get_offending_flows}*}
  thm generate_valid_topology_complies

  text{*Interlude: the formal definition is sound*}
  thm generate_valid_topology_sound

  text{*Here, it is also complete*}
  lemma "wf_graph G \<Longrightarrow> max_topo [the BLP_m_spec] (TopoS_Composition_Theory.generate_valid_topology [the BLP_m_spec] (fully_connected G))"
  apply(rule generate_valid_topology_max_topo[OF valid_reqs_BLP])
   apply(assumption)
  apply(simp add: BLP_m_spec)
  by blast


text{*Calculating the maximum policy*}
value "max_policy"
lemma "max_policy = \<lparr>nodesL = [1, 2, 3], edgesL = [(1, 1), (1, 2), (1, 3), (2, 2), (3, 1), (3, 2), (3, 3)]\<rparr>" by eval


text{*
Visualizing the maximum policy (only in interactive mode)
*}
ML{*
visualize_graph @{context} @{term "security_invariants"} @{term "max_policy"};
*}

text{*Of course, all security invariants hold for the maximum policy. *}
lemma "all_security_requirements_fulfilled security_invariants max_policy" by eval


subsection{*A stateful implementation*}
text{*We generate a stateful policy*}
definition "stateful_policy = generate_valid_stateful_policy_IFSACS_2 policy security_invariants"

text{*When thinking about it carefully, no flow can be stateful without introducing an information leakage here!*}
value "stateful_policy"
lemma "stateful_policy = \<lparr>hostsL = [1, 2, 3], flows_fixL = [(1, 2), (2, 2), (2, 3)], flows_stateL = []\<rparr>" by eval

  text{*Interlude: the stateful policy we are computing fulfills all the necessary properties*}
  thm generate_valid_stateful_policy_IFSACS_2_complies

  (*the individual algorithms fir IFS/ACS return a maximum policy*)
  thm filter_compliant_stateful_ACS_correct filter_compliant_stateful_ACS_maximal
  thm filter_IFS_no_violations_correct filter_IFS_no_violations_maximal

text{*
Visualizing the stateful policy (only in interactive mode)
*}
ML_val{*
visualize_edges @{context} @{term "flows_fixL stateful_policy"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]", @{term "flows_stateL stateful_policy"})] ""; 
*}


text{*This is how it would look like if @{term "(3,1)"} were a stateful flow*}
ML_val{*
visualize_edges @{context} @{term "flows_fixL stateful_policy"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]", @{term "[(3::nat,1::nat)]"})] ""; 
*}


hide_const policy security_invariants max_policy stateful_policy


end
