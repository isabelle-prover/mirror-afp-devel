theory Distributed_WebApp
imports "../TopoS_Impl"
begin

section{*Distributed Web Application Example*}

text{* 
    The symbolic policy names are of type @{typ string}, e.g. @{term "''WebFrnt''"}
*}

text{*We start with the empty policy, only the entities are defined.*}
definition policy :: "string list_graph" where
    "policy \<equiv> \<lparr> nodesL = [''WebFrnt'', ''DB'', ''Log'', ''WebApp'', ''INET''],
                edgesL = [] \<rparr>"

text{*Sanity check*}
lemma "wf_list_graph policy" by eval
(*proof by eval means we have executable code to show the lemma. No need to show anything by hand*)


text{*Defining the security invariants*}
definition LogSink_m::"(string SecurityInvariant)" where
  "LogSink_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_Sink \<lparr> 
          node_properties = [''Log'' \<mapsto> Sink]
          \<rparr> ''No information must leave the logging server''"

text{*
0 - unclassified
1 - confidential
*}
\<comment> \<open>trusted: can access any security level, privacy-level 0: can reveal to anyone. I.e. can declassify\<close>
definition BLP_m::"(string SecurityInvariant)" where
    "BLP_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_BLPtrusted \<lparr> 
          node_properties = [''DB'' \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
                             ''Log'' \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
                             ''WebApp'' \<mapsto> \<lparr> security_level = 0, trusted = True \<rparr> 
                             ]
          \<rparr> ''The database and the logging server have confidential information''"

definition Subnet_m::"(string SecurityInvariant)" where
    "Subnet_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = [''DB'' \<mapsto> Member,
                             ''Log'' \<mapsto> Member,
                             ''WebApp'' \<mapsto> Member,
                             ''WebFrnt'' \<mapsto> InboundGateway \<comment> \<open>DMZ\<close>
                             ]
          \<rparr> ''internal/DMZ structure''"


definition DBACL_m::"(string SecurityInvariant)" where
    "DBACL_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [''DB'' \<mapsto> Master [''WebApp''],
                             ''WebApp'' \<mapsto> Care
                             ]
          \<rparr> ''ACL of db''"

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
   \<lparr>nodesL = [''WebFrnt'', ''DB'', ''Log'', ''WebApp'', ''INET''],
    edgesL = [(''WebFrnt'', ''WebFrnt''), (''WebFrnt'', ''Log''), (''WebFrnt'', ''WebApp''), (''WebFrnt'', ''INET''), (''DB'', ''DB''),
              (''DB'', ''Log''), (''DB'', ''WebApp''), (''Log'', ''Log''), (''WebApp'', ''WebFrnt''), (''WebApp'', ''DB''),
              (''WebApp'', ''Log''), (''WebApp'', ''WebApp''), (''WebApp'', ''INET''), (''INET'', ''WebFrnt''), (''INET'', ''INET'')]\<rparr>"
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
definition "my_policy = \<lparr>nodesL = [''WebFrnt'', ''DB'', ''Log'', ''WebApp'', ''INET''],
    edgesL = [(''WebFrnt'', ''WebFrnt''), (''WebFrnt'', ''Log''), (''WebFrnt'', ''WebApp''), (''DB'', ''DB''), (''DB'', ''Log''),
              (''DB'', ''WebApp''), (''Log'', ''Log''), (''WebApp'', ''WebFrnt''), (''WebApp'', ''DB''), (''WebApp'', ''Log''), (''WebApp'', ''WebApp''),
              (''WebApp'', ''INET''), (''INET'', ''WebFrnt''), (''INET'', ''INET'')]\<rparr>"
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
  (fn (v1,v2) => writeln ("iptables -A FORWARD -i $"^v1^"_iface -s $"^v1^"_ipv4 -o $"^v2^"_iface -d $"^v2^"_ipv4 -j ACCEPT"^" # "^v1^" -> "^v2) )
  (fn _ => () )
  (fn _ => () );

iterate_edges_ML @{context} @{term "flows_stateL stateful_policy"}
  (fn (v1,v2) => writeln ("iptables -I FORWARD -m state --state ESTABLISHED -i $"^v2^"_iface -s $"^v2^"_ipv4 -o $"^v1^"_iface -d $"^v1^"_ipv4 -j ACCEPT # "^v2^" -> "^v1^" (answer)") )
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

definition stateful_flows :: "(string \<times> string) list" where
  "stateful_flows \<equiv> [(src, dst) \<leftarrow> flows_stateL stateful_policy. src \<noteq> dst]"
value "stateful_flows"

definition stateless_flows :: "(string \<times> string) list" where
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


text{*Finally, all the functions demonstrated here can be exported to several programming languages
     to obtain a stand-alone tool.*}
export_code
  security_invariants
  policy
  all_security_requirements_fulfilled
  implc_get_offending_flows
  max_policy
  my_policy
  generate_valid_stateful_policy_IFSACS
  stateful_policy
  stateful_flows
  stateless_flows
in Scala






(*dockermynet4*)


definition dockermynet4policy :: "string list_graph" where
    "dockermynet4policy \<equiv> \<lparr> nodesL = [''WebFrnt'', ''DB'', ''Log'', ''WebApp'', ''INET''],
                edgesL = [(''INET'',''INET''),
                          (''INET'',''WebFrnt''),
                          (''WebApp'',''INET''),
                          (''WebApp'',''WebApp''),
                          (''WebApp'',''DB''),
                          (''WebApp'',''Log''),
                          (''WebApp'',''WebFrnt''),
                          (''DB'',''WebApp''),
                          (''DB'',''DB''),
                          (''DB'',''Log''),
                          (''Log'',''Log''),
                          (''Log'',''WebFrnt''),
                          (''WebFrnt'',''WebApp''),
                          (''WebFrnt'',''Log''),
                          (''WebFrnt'',''WebFrnt'')] \<rparr>"

lemma "wf_list_graph dockermynet4policy" by eval

ML{*
visualize_graph @{context} @{term "security_invariants"} @{term "dockermynet4policy"};
*}

ML_val{*
writeln ("*filter"^"\n"^
         ":INPUT ACCEPT [0:0]"^"\n"^
         ":FORWARD DROP [0:0]"^"\n"^
         ":OUTPUT ACCEPT [0:0]"^"\n");

fun mkiface s = if s = "INET" then "INET_iface" else "br-b74b417b331f";

iterate_edges_ML @{context}  @{term "flows_fixL (generate_valid_stateful_policy_IFSACS max_policy security_invariants)"}
  (fn (v1,v2) => writeln ("-A FORWARD -i "^mkiface v1^" -s $"^v1^"_ipv4 -o "^mkiface v2^" -d $"^v2^"_ipv4 -j ACCEPT") )
  (fn _ => () )
  (fn _ => () );

iterate_edges_ML @{context} @{term "flows_stateL (generate_valid_stateful_policy_IFSACS max_policy security_invariants)"}
  (fn (v1,v2) => writeln ("-I FORWARD -m state --state ESTABLISHED -i "^mkiface v2^" -s $"^v2^"_ipv4 -o "^mkiface v1^" -d $"^v1^"_ipv4 -j ACCEPT") )
  (fn _ => () )
  (fn _ => () );

writeln ("COMMIT"^"\n");
*}


ML_val{*
visualize_edges @{context} @{term "flows_fixL (generate_valid_stateful_policy_IFSACS max_policy security_invariants)"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]", @{term "flows_stateL (generate_valid_stateful_policy_IFSACS max_policy security_invariants)"})] ""; 
*}

(*dfwfw (docker firewall) rules: https://github.com/irsl/dfwfw*)

ML_val{*
writeln ("{"^"\n"^
         "\"container_to_container\": {"^"\n"^
         "\"rules\": ["^"\n"^
         "\n");

fun mkdfwfwrule filter v1 v2 = "{"^"\n"^
             "  \"network\": \"mynet\","^"\n"^
             "  \"src_container\": \"Name =~ ^"^ String.map Char.toLower v1 ^"-?\\\\d*$\","^"\n"^
             "  \"dst_container\": \"Name =~ ^"^ String.map Char.toLower v2 ^"-?\\\\d*$\","^"\n"^
             "  \"filter\": \""^filter^"\","^"\n"^
             "  \"action\": \"ACCEPT\""^"\n"^
          "},";

iterate_edges_ML @{context}  @{term "flows_fixL (generate_valid_stateful_policy_IFSACS max_policy security_invariants)"}
  (fn (v1,v2) => writeln (mkdfwfwrule "" v1 v2) )
  (fn _ => () )
  (fn _ => () );

iterate_edges_ML @{context} @{term "flows_stateL (generate_valid_stateful_policy_IFSACS max_policy security_invariants)"}
  (fn (v1,v2) => writeln (mkdfwfwrule "-m state --state ESTABLISHED" v2 v1))
  (fn _ => () )
  (fn _ => () );

writeln ("]}}"^"\n");
*}

end
