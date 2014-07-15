header{*Network Security Policy Verification*}
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

subsection{*Policy*}
text{*The secuity policy is a directed graph.*}
definition policy :: "nat list_graph" where
    "policy \<equiv> \<lparr> nodesL = [1,2,3],
                edgesL = [(1,2), (2,2), (2,3)] \<rparr>"

text{*It is syntactically valid. *}
lemma "valid_list_graph policy" by eval

text{*In contrast, this is not a syntactically valid graph. *}
lemma "\<not> valid_list_graph \<lparr> nodesL = [1,2]::nat list, edgesL = [(1,2), (2,2), (2,3)] \<rparr>" by eval

text{*Our @{const policy} has three rules. *}
lemma "length (edgesL policy) = 3" by eval

subsection{*Security Invariants*}
text{*We construct a security invariant. Node @{term "2::nat"} has confidential data*}
definition BLP_m::"(nat SecurityInvariant)" where
    "BLP_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_BLPtrusted \<lparr> 
          node_properties = [2 \<mapsto> \<lparr> privacy_level = 1, trusted = False \<rparr>], 
          model_global_properties = () 
          \<rparr>"

text{*We define the list of all security invariants of type @{typ "nat SecurityInvariant list"}.
     The type @{typ nat} is because the policy's nodes are of type @{typ nat}.*}
definition "security_invariants = [BLP_m]"

text{*We can see that the policy does not fulfill the security invariants. *}
lemma "\<not> all_security_requirements_fulfilled security_invariants policy" by eval

text{*We ask why. Obviously, node 2 leaks confidential data to node 3.*}
value "implc_get_offending_flows security_invariants policy"
lemma "implc_get_offending_flows security_invariants policy = [[(2, 3)]]" by eval


text{*
Visualization of the violation (only in interactive mode)
*}
ML{*
vizualize_graph @{context} @{term "security_invariants"} @{term "policy"};
*}


text{*
The policy has a flaw. We throw it away and generate a new one which fulfills the invariants.
*}
definition "max_policy = generate_valid_topology security_invariants \<lparr>nodesL = nodesL policy, edgesL = List.product (nodesL policy) (nodesL policy) \<rparr>"


text{*Calculating the maximum policy*}
value "max_policy"
lemma "max_policy = \<lparr>nodesL = [1, 2, 3], edgesL = [(1, 1), (1, 2), (1, 3), (2, 2), (3, 1), (3, 2), (3, 3)]\<rparr>" by eval


text{*
Visualizing the maximum policy (only in interactive mode)
*}
ML{*
vizualize_graph @{context} @{term "security_invariants"} @{term "max_policy"};
*}

text{*Of course, all security invariants hold for the maximum policy. *}
lemma "all_security_requirements_fulfilled security_invariants max_policy" by eval


subsection{*A stateful implementation*}
text{*We generate a stateful policy*}
definition "stateful_policy = generate_valid_stateful_policy_IFSACS policy security_invariants"

text{*When thinking about it carefully, no flow can be stateful without introducing an information leakage here!*}
value "stateful_policy"
lemma "stateful_policy = \<lparr>hostsL = [1, 2, 3], flows_fixL = [(1, 2), (2, 2), (2, 3)], flows_stateL = []\<rparr>" by eval

text{*
Visualizing the stateful policy (only in interactive mode)
*}
ML_val{*
visualize_edges @{context} @{term "flows_fixL stateful_policy"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]", @{term "flows_stateL stateful_policy"})]; 
*}

hide_const policy security_invariants max_policy stateful_policy


end
