theory Distributed_WebApp
imports "../TopoS_Impl"
begin

section{*Distributed Web Application Example*}

text{* 
    The symbolic policy names are of type @{typ vString}. This is just a wrapped string, e.g. @{term "V ''WebFrnt''"}
*}
abbreviation "V\<equiv>TopoS_Vertices.V"

text{*We start with the empty policy, only the entities are defined.*}
definition policy :: "vString list_graph" where
    "policy \<equiv> \<lparr> nodesL = [V ''WebFrnt'', V ''DB'', V ''Log'', V ''WebApp'', V ''INET''],
                edgesL = [] \<rparr>"

text{*Sanity check*}
lemma "wf_list_graph policy" by eval
(*proof by eval means we have executable code to show the lemma.*)


text{*Defining the security invariants*}
definition LogSink_m::"(vString SecurityInvariant)" where
  "LogSink_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_Sink \<lparr> 
          node_properties = [V ''Log'' \<mapsto> Sink], 
          model_global_properties = () 
          \<rparr>"

text{*
0 - unclassified
1 - confidential
*}
--"trusted: can access any security clearance, privacy-level 0: can reveal to anyone. I.e. can declassify"
definition BLP_m::"(vString SecurityInvariant)" where
    "BLP_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_BLPtrusted \<lparr> 
          node_properties = [V ''DB'' \<mapsto> \<lparr> privacy_level = 1, trusted = False \<rparr>,
                             V ''Log'' \<mapsto> \<lparr> privacy_level = 1, trusted = False \<rparr>,
                             V ''WebApp'' \<mapsto> \<lparr> privacy_level = 0, trusted = True \<rparr> 
                             ], 
          model_global_properties = () 
          \<rparr>"

definition Subnet_m::"(vString SecurityInvariant)" where
    "Subnet_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = [V ''DB'' \<mapsto> Member,
                             V ''Log'' \<mapsto> Member,
                             V ''WebApp'' \<mapsto> Member,
                             V ''WebFrnt'' \<mapsto> InboundGateway (*DMZ*)
                             ], 
          model_global_properties = () 
          \<rparr>"


definition DBACL_m::"(vString SecurityInvariant)" where
    "DBACL_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [V ''DB'' \<mapsto> Master [V ''WebApp''],
                             V ''WebApp'' \<mapsto> Care
                             ], 
          model_global_properties = () 
          \<rparr>"

text{*The list of security invariants*}
definition "security_invariants = [Subnet_m, BLP_m, LogSink_m, DBACL_m]"

text{*All security invariants are fulfilled (obviously, the policy permits no flows).*}
lemma "all_security_requirements_fulfilled security_invariants policy" by eval

text{*Obviously, no policy rules violate the security invariants.*}
lemma "implc_get_offending_flows security_invariants policy = []" by eval


text{*We generate the maximum security policy.*}
definition "max_policy = generate_valid_topology security_invariants \<lparr>nodesL = nodesL policy, edgesL = List.product (nodesL policy) (nodesL policy) \<rparr>"


text{*Calculating the maximum policy (executing it).*}
value "max_policy"
lemma "max_policy = 
   \<lparr>nodesL = [V ''WebFrnt'', V ''DB'', V ''Log'', V ''WebApp'', V ''INET''],
    edgesL = [(V ''WebFrnt'', V ''WebFrnt''), (V ''WebFrnt'', V ''Log''), (V ''WebFrnt'', V ''WebApp''), (V ''WebFrnt'', V ''INET''), (V ''DB'', V ''DB''),
              (V ''DB'', V ''Log''), (V ''DB'', V ''WebApp''), (V ''Log'', V ''Log''), (V ''WebApp'', V ''WebFrnt''), (V ''WebApp'', V ''DB''),
              (V ''WebApp'', V ''Log''), (V ''WebApp'', V ''WebApp''), (V ''WebApp'', V ''INET''), (V ''INET'', V ''WebFrnt''), (V ''INET'', V ''INET'')]\<rparr>"
by eval (*proof by eval means it can be directly executed*)

text{*
Visualizing the maximum policy
*}
ML{*
visualize_graph @{context} @{term "security_invariants"} @{term "max_policy"};
*}

text{*The maximum policy also fulfills all security invariants. *}
lemma "all_security_requirements_fulfilled security_invariants max_policy" by eval
text{*This holds in general: @{thm generate_valid_topology_sound}.*}

text{*fine-tuning generated policy.*}
definition "my_policy = \<lparr>nodesL = [V ''WebFrnt'', V ''DB'', V ''Log'', V ''WebApp'', V ''INET''],
    edgesL = [(V ''WebFrnt'', V ''WebFrnt''), (V ''WebFrnt'', V ''Log''), (V ''WebFrnt'', V ''WebApp''), (V ''DB'', V ''DB''), (V ''DB'', V ''Log''),
              (V ''DB'', V ''WebApp''), (V ''Log'', V ''Log''), (V ''WebApp'', V ''WebFrnt''), (V ''WebApp'', V ''DB''), (V ''WebApp'', V ''Log''), (V ''WebApp'', V ''WebApp''),
              (V ''WebApp'', V ''INET''), (V ''INET'', V ''WebFrnt''), (V ''INET'', V ''INET'')]\<rparr>"
lemma "all_security_requirements_fulfilled security_invariants my_policy" by eval
lemma "set (edgesL my_policy) \<subset> set (edgesL max_policy)" by eval

text{*
The diff to the maximum policy.
*}
ML_val{*
visualize_edges @{context} @{term "edgesL my_policy"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#3399FF\", constraint=false]", @{term "[e \<leftarrow> edgesL max_policy. e \<notin> set (edgesL my_policy)]"})] ""; 
*}



section{*A stateful implementation*}
definition "stateful_policy = generate_valid_stateful_policy_IFSACS my_policy security_invariants"
value "stateful_policy"

text{*the stateful compliance criteria*}

text{*No information flow violations*}
  lemma "all_security_requirements_fulfilled (get_IFS security_invariants) (stateful_list_policy_to_list_graph stateful_policy)" by eval
  
  text{*No access control side effects*}
  lemma "\<forall> F \<in> set (implc_get_offending_flows (get_ACS security_invariants) (stateful_list_policy_to_list_graph stateful_policy)).
            set F \<subseteq> set (backlinks (flows_stateL stateful_policy)) - (set (flows_fixL stateful_policy))" by eval

  text{*In general, the calculated stateful policy complies with the security policy: @{thm generate_valid_stateful_policy_IFSACS_stateful_policy_compliance}*}

text{*Visualizing the stateful policy.*}
ML_val{*
visualize_edges @{context} @{term "flows_fixL stateful_policy"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]", @{term "flows_stateL stateful_policy"})] ""; 
*}


subsection{*Exporting to Network Security Mechanism Configurations*}


text{*Space-separated policy dump*}
ML_val{*
iterate_edges_ML @{context} @{term "flows_fixL stateful_policy"}
  (fn (v1,v2) => writeln (""^v1^" "^v2) )
  (fn _ => () )
  (fn _ => () );

writeln "# stateful answers";
iterate_edges_ML @{context} @{term "flows_stateL stateful_policy"}
  (fn (v1,v2) => writeln (v2^" "^v1) )
  (fn _ => () )
  (fn _ => () )
*}

text{*firewall -- classical use case*}
ML_val{*

(*header*)
writeln ("echo 1 > /proc/sys/net/ipv4/ip_forward"^"\n"^
         "# flush all rules"^"\n"^
         "iptables -F"^"\n"^
         "#default policy for FORWARD chain:"^"\n"^
         "iptables -P FORWARD DROP");

iterate_edges_ML @{context}  @{term "flows_fixL stateful_policy"}
  (fn (v1,v2) => writeln ("iptables -A FORWARD -i $"^v1^"_iface -s $"^v1^"_ipv4 -o "^v2^"_iface -d $"^v2^"_ipv4 -j ACCEPT"^" # "^v1^" -> "^v2) )
  (fn _ => () )
  (fn _ => () );

iterate_edges_ML @{context} @{term "flows_stateL stateful_policy"}
  (fn (v1,v2) => writeln ("iptables -I FORWARD -m state --state ESTABLISHED -i $"^v2^"_iface -s $"^v2^"_ipv4 -o $"^v1^"_iface -d $"^v1^"_ipv4 # "^v2^" -> "^v1^" (answer)") )
  (fn _ => () )
  (fn _ => () )
*}

text{*firewall -- OpenVPN scenario*}
ML_val{*

(*header*)
writeln ("echo 1 > /proc/sys/net/ipv4/ip_forward"^"\n"^
         "# flush all rules"^"\n"^
         "iptables -F"^"\n"^
         "#default policy for FORWARD chain:"^"\n"^
         "iptables -P FORWARD DROP");

fun iface (s: string): string =
  if s = "INET" then "eth0" else "tun0";

iterate_edges_ML @{context} @{term "[(s,r) \<leftarrow> flows_fixL stateful_policy. s \<noteq> r]"}
  (fn (v1,v2) => writeln ("iptables -A FORWARD -i "^iface v1^" -s $"^v1^"_ipv4 -o "^iface v2^" -d $"^v2^"_ipv4 -j ACCEPT") )
  (fn _ => () )
  (fn _ => () );

iterate_edges_ML @{context} @{term "flows_stateL stateful_policy"}
  (fn (v1,v2) => writeln ("iptables -I FORWARD -m state --state ESTABLISHED -i "^iface v2^" -s $"^v2^"_ipv4 -o "^iface v1^" -d $"^v1^"_ipv4 -j ACCEPT") )
  (fn _ => () )
  (fn _ => () )
*}


lemma "set (flows_stateL stateful_policy) \<subseteq> set (flows_fixL stateful_policy)" by eval

definition stateful_flows :: "(vString \<times> vString) list" where
  "stateful_flows \<equiv> [(src, dst) \<leftarrow> flows_stateL stateful_policy. src \<noteq> dst]"
value "stateful_flows"

definition stateless_flows :: "(vString \<times> vString) list" where
  "stateless_flows \<equiv> [(src, dst) \<leftarrow> flows_fixL stateful_policy. src \<noteq> dst \<and> (src, dst) \<notin> set stateful_flows]"
value "stateless_flows"

text{*OpenFlow Flow table Rules*}
ML_val{*
fun ARP (src: string) (dst: string): string =
  "# ARP Request\n"^
  "in_port=${port_"^src^"} dl_src=${mac_"^src^"} dl_dst=ff:ff:ff:ff:ff:ff arp arp_sha=${mac_"^src^"} "^
  "arp_spa=${ip4_"^src^"} arp_tpa=${ip4_"^dst^"} priority=40000 action=mod_dl_dst:${mac_"^dst^"},output:${port_"^dst^"}"^"\n"^
  "# ARP Reply\n"^
  "dl_src=${mac_"^dst^"} dl_dst=${mac_"^src^"} arp arp_sha=${mac_"^dst^"} "^
  "arp_spa=${ip4_"^dst^"} arp_tpa=${ip4_"^src^"} priority=40000 action=output:${port_"^src^"}";

local
  fun IPv4_helper (priority: int) (nw_src_wildcard: bool) (nw_dst_wildcard: bool) (src: string) (dst: string): string =
    let
      val nw_src = (if nw_src_wildcard then "*" else "${ip4_"^src^"}");
      val nw_dst = (if nw_dst_wildcard then "*" else "${ip4_"^dst^"}");
    in
      "in_port=${port_"^src^"} dl_src=${mac_"^src^"} ip nw_src="^nw_src^" "^
      "nw_dst="^nw_dst^" priority="^(Int.toString priority)^" action=mod_dl_dst:${mac_"^dst^"},output:${port_"^dst^"}"
    end;
in
  fun IPv4 (src: string) (dst: string): string =
    if dst = "INET" then
      IPv4_helper 30000 false true src dst
    else if src = "INET" then
      IPv4_helper 30000 true false src dst
    else
      IPv4_helper 40000 false false src dst
      ;
end;

iterate_edges_ML @{context} @{term "stateful_flows"}
  (fn (v1,v2) => writeln ((ARP v1 v2) ^ "\n" ^ (ARP v2 v1) ^ "\n" ^ (IPv4 v1 v2) ^ "\n" ^ (IPv4 v2 v1) ^"\n"))
  (fn _ => () )
  (fn _ => () );

iterate_edges_ML @{context} @{term "stateless_flows"}
  (fn (v1,v2) =>  writeln ((ARP v1 v2) ^ "\n" ^ (IPv4 v1 v2) ^ "\n"))
  (fn _ => () )
  (fn _ => () )
*}


end
