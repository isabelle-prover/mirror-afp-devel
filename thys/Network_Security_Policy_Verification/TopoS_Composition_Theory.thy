theory TopoS_Composition_Theory
imports TopoS_Interface TopoS_Helper
begin

section{*Composition Theory*}

text{*Several invariants may apply to one policy. *}

text{*The security invariants are all collected in a list. 
The list corresponds to the security requirements. 
The list should have the type @{typ "('v graph \<Rightarrow> bool) list"}, i.e.\ a list of predicates over the policy. 
We need in instantiated security invariant, i.e.\ get rid of @{typ "'a"} and @{typ "'b"}*}

 --{*An instance (configured) a security invariant I.e.\ a concrete security requirement, in different terminology. *}
 record ('v) SecurityInvariant_configured =
    c_sinvar::"('v) graph \<Rightarrow> bool"
    c_offending_flows::"('v) graph \<Rightarrow> ('v \<times> 'v) set set"
    c_isIFS::"bool"

  --{* First three parameters are the @{text "SecurityInvariant"}:
      @{text sinvar} @{text "\<bottom>"} @{text "receiver_violation"}

      Fourth parameter is the host attribute mapping @{text nP}

      
      TODO: probably check @{text "verify_globals"} and @{text "valid_graph"} here.
      *}
  fun new_configured_SecurityInvariant :: "((('v::vertex) graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool) \<times> 'a \<times> bool \<times> ('v \<Rightarrow> 'a)) \<Rightarrow> ('v SecurityInvariant_configured) option" where 
      "new_configured_SecurityInvariant (sinvar, defbot, receiver_violation, nP) = 
        ( 
        if SecurityInvariant sinvar defbot receiver_violation then 
          Some \<lparr> 
            c_sinvar = (\<lambda>G. sinvar G nP),
            c_offending_flows = (\<lambda>G. SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G nP),
            c_isIFS = receiver_violation
          \<rparr>
        else None
        )"

   declare new_configured_SecurityInvariant.simps[simp del]

   lemma new_configured_TopoS_sinvar_correct:
   "SecurityInvariant sinvar defbot receiver_violation \<Longrightarrow> 
   c_sinvar (the (new_configured_SecurityInvariant (sinvar, defbot, receiver_violation, nP))) = (\<lambda>G. sinvar G nP)"
   by(simp add: Let_def new_configured_SecurityInvariant.simps)

   lemma new_configured_TopoS_offending_flows_correct:
   "SecurityInvariant sinvar defbot receiver_violation \<Longrightarrow> 
   c_offending_flows (the (new_configured_SecurityInvariant (sinvar, defbot, receiver_violation, nP))) = 
   (\<lambda>G. SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G nP)"
   by(simp add: Let_def new_configured_SecurityInvariant.simps)


text{* We now collect all the core properties of a security invariant, but without the @{typ "'a"} @{typ "'b"} 
      types, so it is instantiated with a concrete configuration.*}
locale configured_SecurityInvariant =
  fixes m :: "('v::vertex) SecurityInvariant_configured"
  assumes
    --"As in SecurityInvariant definition"
    valid_c_offending_flows:
    "c_offending_flows m G = {F. F \<subseteq> (edges G) \<and> \<not> c_sinvar m G \<and> c_sinvar m (delete_edges G F) \<and> 
      (\<forall> (e1, e2) \<in> F. \<not> c_sinvar m (add_edge e1 e2 (delete_edges G F)))}"
  and
    --"A empty network can have no security violations"
    defined_offending:
    "\<lbrakk> valid_graph \<lparr> nodes = N, edges = {} \<rparr> \<rbrakk> \<Longrightarrow> c_sinvar m \<lparr> nodes = N, edges = {}\<rparr>"
  and
    --"prohibiting more does not decrease security"
    mono_sinvar:
    "\<lbrakk> valid_graph \<lparr> nodes = N, edges = E \<rparr>; E' \<subseteq> E; c_sinvar m \<lparr> nodes = N, edges = E \<rparr> \<rbrakk> \<Longrightarrow> 
      c_sinvar m \<lparr> nodes = N, edges = E' \<rparr>"
  begin
    (*compatibility with other definitions*)
    lemma sinvar_monoI: 
    "SecurityInvariant_withOffendingFlows.sinvar_mono (\<lambda> (G::('v::vertex) graph) (nP::'v \<Rightarrow> 'a). c_sinvar m G)"
      apply(simp add: SecurityInvariant_withOffendingFlows.sinvar_mono_def, clarify)
      by(fact mono_sinvar)

    text{* if the network where nobody communicates with anyone fulfilles its security requirement,
          the offending flows are always defined. *}
    lemma defined_offending': 
      "\<lbrakk> valid_graph G; \<not> c_sinvar m G \<rbrakk> \<Longrightarrow> c_offending_flows m G \<noteq> {}"
      proof -
        assume a1: "valid_graph G"
        and    a2: "\<not> c_sinvar m G"
        have subst_set_offending_flows: 
        "\<And>nP. SecurityInvariant_withOffendingFlows.set_offending_flows (\<lambda>G nP. c_sinvar m G) G nP = c_offending_flows m G"
        by(simp add: valid_c_offending_flows fun_eq_iff 
            SecurityInvariant_withOffendingFlows.set_offending_flows_def
            SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
            SecurityInvariant_withOffendingFlows.is_offending_flows_def)

        from a1 have validG_empty: "valid_graph \<lparr>nodes = nodes G, edges = {}\<rparr>" by(simp add:valid_graph_def)

        from a1 have "\<And>nP. \<not> c_sinvar m G \<Longrightarrow> SecurityInvariant_withOffendingFlows.set_offending_flows (\<lambda>G nP. c_sinvar m G) G nP \<noteq> {}"
          apply(frule_tac finite_distinct_list[OF valid_graph.finiteE])
          apply(erule_tac exE)
          apply(rename_tac list_edges)
          apply(rule_tac ff="list_edges" in SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_monoI])
          by(auto simp add: SecurityInvariant_withOffendingFlows.is_offending_flows_def delete_edges_simp2 defined_offending[OF validG_empty])
      
          thus ?thesis by(simp add: a2 subst_set_offending_flows)
    qed

    (* The offending flows definitions are equal, compatibility *)
    lemma subst_offending_flows: "\<And> nP. SecurityInvariant_withOffendingFlows.set_offending_flows (\<lambda>G nP. c_sinvar m G) G nP = c_offending_flows m G"
      apply (unfold SecurityInvariant_withOffendingFlows.set_offending_flows_def
            SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
            SecurityInvariant_withOffendingFlows.is_offending_flows_def)
      by(simp add: valid_c_offending_flows)

    text{* all the @{term SecurityInvariant_preliminaries} stuff must hold, for an arbitrary @{term nP} *}
    lemma SecurityInvariant_preliminariesD:
      "SecurityInvariant_preliminaries (\<lambda> (G::('v::vertex) graph) (nP::'v \<Rightarrow> 'a). c_sinvar m G)"
      apply(unfold_locales)
        apply(simp add: subst_offending_flows)
        apply(fact defined_offending')
       apply(fact mono_sinvar)
      apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_monoI])
      done

    lemma negative_mono:
     "\<And> N E' E. valid_graph \<lparr> nodes = N, edges = E \<rparr> \<Longrightarrow> 
        E' \<subseteq> E \<Longrightarrow> \<not> c_sinvar m \<lparr> nodes = N, edges = E' \<rparr> \<Longrightarrow> \<not> c_sinvar m \<lparr> nodes = N, edges = E \<rparr>"
     apply(clarify)
     apply(drule(2) mono_sinvar)
     by(blast)

    
    subsection{*Reusing Lemmata*}
      lemmas mono_extend_set_offending_flows =
      SecurityInvariant_preliminaries.mono_extend_set_offending_flows[OF SecurityInvariant_preliminariesD, simplified subst_offending_flows]
      text{*@{thm mono_extend_set_offending_flows [no_vars]}*}

      lemmas offending_flows_union_mono =
      SecurityInvariant_preliminaries.offending_flows_union_mono[OF SecurityInvariant_preliminariesD, simplified subst_offending_flows]
      text{*@{thm offending_flows_union_mono [no_vars]}*}

      lemmas sinvar_valid_remove_flattened_offending_flows =
      SecurityInvariant_preliminaries.sinvar_valid_remove_flattened_offending_flows[OF SecurityInvariant_preliminariesD, simplified subst_offending_flows]
      text{*@{thm sinvar_valid_remove_flattened_offending_flows [no_vars]}*}

      lemmas empty_offending_contra =
      SecurityInvariant_withOffendingFlows.empty_offending_contra[where sinvar="(\<lambda>G nP. c_sinvar m G)", simplified subst_offending_flows]
      text{*@{thm empty_offending_contra [no_vars]}*}

      lemmas Un_set_offending_flows_bound_minus_subseteq = 
      SecurityInvariant_preliminaries.Un_set_offending_flows_bound_minus_subseteq[OF SecurityInvariant_preliminariesD, simplified subst_offending_flows]
      text{*@{thm Un_set_offending_flows_bound_minus_subseteq [no_vars]}*}

      lemmas Un_set_offending_flows_bound_minus_subseteq' = 
      SecurityInvariant_preliminaries.Un_set_offending_flows_bound_minus_subseteq'[OF SecurityInvariant_preliminariesD, simplified subst_offending_flows]
      text{*@{thm Un_set_offending_flows_bound_minus_subseteq' [no_vars]}*}
end

thm configured_SecurityInvariant_def
text{*@{thm configured_SecurityInvariant_def [no_vars]}*}

thm configured_SecurityInvariant.mono_sinvar
text{*@{thm configured_SecurityInvariant.mono_sinvar [no_vars]}*}



text{* 
  Naming convention:
    m :: network security requirement
    M :: network security requirement list
*}

  text{* The function @{term new_configured_SecurityInvariant} takes some tuple and if it returns a result,
         the locale assumptions are automatically fulfilled. *}
  theorem new_configured_SecurityInvariant_sound: 
  "\<lbrakk> new_configured_SecurityInvariant (sinvar, defbot, receiver_violation, nP) = Some m \<rbrakk> \<Longrightarrow>
    configured_SecurityInvariant m"
    proof -
      assume a: "new_configured_SecurityInvariant (sinvar, defbot, receiver_violation, nP) = Some m"
      hence NetModel: "SecurityInvariant sinvar defbot receiver_violation"
        by(simp add: new_configured_SecurityInvariant.simps split: split_if_asm)
      hence NetModel_p: "SecurityInvariant_preliminaries sinvar" by(simp add: SecurityInvariant_def)

      from a have c_eval: "c_sinvar m = (\<lambda>G. sinvar G nP)"
         and c_offending: "c_offending_flows m = (\<lambda>G. SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G nP)"
         and "c_isIFS m = receiver_violation"
        by(auto simp add: new_configured_SecurityInvariant.simps NetModel split: split_if_asm)

      have monoI: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
        apply(simp add: SecurityInvariant_withOffendingFlows.sinvar_mono_def, clarify)
        by(fact SecurityInvariant_preliminaries.mono_sinvar[OF NetModel_p])
      from SecurityInvariant_withOffendingFlows.valid_empty_edges_iff_exists_offending_flows[OF monoI, symmetric]
            SecurityInvariant_preliminaries.defined_offending[OF NetModel_p]
      have eval_empty_graph: "\<And> N nP. valid_graph \<lparr>nodes = N, edges = {}\<rparr> \<Longrightarrow> sinvar \<lparr>nodes = N, edges = {}\<rparr> nP"
      by fastforce

       show ?thesis
        apply(unfold_locales)
          apply(simp add: c_eval c_offending SecurityInvariant_withOffendingFlows.set_offending_flows_def SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def SecurityInvariant_withOffendingFlows.is_offending_flows_def)
         apply(simp add: c_eval eval_empty_graph)
        apply(simp add: c_eval,drule(3) SecurityInvariant_preliminaries.mono_sinvar[OF NetModel_p])
        done
   qed

text{* All security invariants are valid according to the definition *}
definition valid_reqs :: "('v::vertex) SecurityInvariant_configured list \<Rightarrow> bool" where
  "valid_reqs M \<equiv> \<forall> m \<in> set M. configured_SecurityInvariant m"

 subsection {*Algorithms*}
    text{*A (generic) security invariant corresponds to a type of security requirements (type: @{typ "'v graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool"}).
          A configured security invariant is a security requirement in a scenario specific setting (type: @{typ "'v graph \<Rightarrow> bool"}).
          I.e., it is a security requirement as listed in the requirements document.
          All security requirements are fulfilled for a fixed policy @{term G} if all security requirements are fulfilled for @{term G}. *}


    text{*Get all possible offending flows from all security requirements *}
    definition get_offending_flows :: "('v::vertex) SecurityInvariant_configured list \<Rightarrow> 'v graph \<Rightarrow> (('v \<times> 'v) set set)" where
      "get_offending_flows M G = (\<Union>m\<in>set M. c_offending_flows m G)"  

    (*Note: only checks sinvar, not eval!! No 'a 'b type variables here*)
    definition all_security_requirements_fulfilled :: "('v::vertex) SecurityInvariant_configured list \<Rightarrow> 'v graph \<Rightarrow> bool" where
      "all_security_requirements_fulfilled M G \<equiv> \<forall>m \<in> set M. (c_sinvar m) G"
    
    text{* Generate a valid topology from the security requirements *}
    (*constant G, remove after algorithm*)
    fun generate_valid_topology :: "'v SecurityInvariant_configured list \<Rightarrow> 'v graph \<Rightarrow> 'v graph" where
      "generate_valid_topology [] G = G" |
      "generate_valid_topology (m#Ms) G = delete_edges (generate_valid_topology Ms G) (\<Union> (c_offending_flows m G))"

     -- "return all Access Control Strategy models from a list of models"
    definition get_ACS :: "('v::vertex) SecurityInvariant_configured list \<Rightarrow> 'v SecurityInvariant_configured list" where
      "get_ACS M \<equiv> [m \<leftarrow> M. \<not> c_isIFS m]"
     -- "return all Information Flows Strategy models from a list of models"
    definition get_IFS :: "('v::vertex) SecurityInvariant_configured list \<Rightarrow> 'v SecurityInvariant_configured list" where
      "get_IFS M \<equiv> [m \<leftarrow> M. c_isIFS m]"
    lemma get_ACS_union_get_IFS: "set (get_ACS M) \<union> set (get_IFS M) = set M"
      by(auto simp add: get_ACS_def get_IFS_def)
  

   subsection{*Lemmata*}
    lemma valid_reqs1: "valid_reqs (m # M) \<Longrightarrow> configured_SecurityInvariant m"
      by(simp add: valid_reqs_def)
    lemma valid_reqs2: "valid_reqs (m # M) \<Longrightarrow> valid_reqs M"
      by(simp add: valid_reqs_def)
    lemma get_offending_flows_alt1: "get_offending_flows M G = \<Union> {c_offending_flows m G | m. m \<in> set M}"
      apply(simp add: get_offending_flows_def) by fastforce
  
  
    lemma all_security_requirements_fulfilled_mono:
      "\<lbrakk> valid_reqs M; E' \<subseteq> E; valid_graph \<lparr> nodes = V, edges = E \<rparr> \<rbrakk> \<Longrightarrow>  
        all_security_requirements_fulfilled M \<lparr> nodes = V, edges = E \<rparr> \<Longrightarrow>
        all_security_requirements_fulfilled M \<lparr> nodes = V, edges = E' \<rparr>"
        apply(induction M arbitrary: E' E)
         apply(simp_all add: all_security_requirements_fulfilled_def)
        apply(rename_tac m M E' E)
        apply(rule conjI)
         apply(erule(2) configured_SecurityInvariant.mono_sinvar[OF valid_reqs1])
         apply(simp_all)
        apply(drule valid_reqs2)
        apply blast
        done

    subsection{* generate valid topology *}
    (*
      lemma generate_valid_topology_def_delete_multiple: 
        "generate_valid_topology M G = delete_edges (generate_valid_topology M G) (\<Union> (get_offending_flows M G))"
        proof(induction M arbitrary: G)
          case Nil
            thus ?case by(simp add: get_offending_flows_def)
          next
          case (Cons m M)
            from Cons[simplified delete_edges_simp2 get_offending_flows_def] 
            have "edges (generate_valid_topology M G) = edges (generate_valid_topology M G) - \<Union>(\<Union>m\<in>set M. c_offending_flows m G)"
              by (metis graph.select_convs(2))
            thus ?case
              apply(simp add: get_offending_flows_def delete_edges_simp2)
              by blast
        qed*)
      lemma generate_valid_topology_nodes:
      "nodes (generate_valid_topology M G) = (nodes G)"
        apply(induction M arbitrary: G)
         by(simp_all add: graph_ops)

      lemma generate_valid_topology_def_alt:
        "generate_valid_topology M G = delete_edges G (\<Union> (get_offending_flows M G))"
        proof(induction M arbitrary: G)
          case Nil
            thus ?case by(simp add: get_offending_flows_def)
          next
          case (Cons m M)
            from Cons[simplified delete_edges_simp2 get_offending_flows_def] 
            have "edges (generate_valid_topology M G) = edges G - \<Union>(\<Union>m\<in>set M. c_offending_flows m G)"
              by (metis graph.select_convs(2))
            thus ?case
              apply(simp add: get_offending_flows_def delete_edges_simp2)
              apply(rule)
               apply(simp add: generate_valid_topology_nodes)
              by blast
        qed
    
      lemma valid_graph_generate_valid_topology: "valid_graph G \<Longrightarrow> valid_graph (generate_valid_topology M G)"
        apply(induction M arbitrary: G)
        by(simp_all)
  
     lemma generate_valid_topology_mono_models:
      "edges (generate_valid_topology (m#M) \<lparr> nodes = V, edges = E \<rparr>) \<subseteq> edges (generate_valid_topology M \<lparr> nodes = V, edges = E \<rparr>)"
        apply(induction M arbitrary: E m)
         apply(simp add: delete_edges_simp2)
         apply fastforce
        apply(simp add: delete_edges_simp2)
        by blast
     
      lemma generate_valid_topology_subseteq_edges:
      "edges (generate_valid_topology M G) \<subseteq> (edges G)"
        apply(induction M arbitrary: G)
         apply(simp_all)
        apply(simp add: delete_edges_simp2)
        by blast

      text{* @{term generate_valid_topology} generates a valid topology (Policy)! *}
      theorem generate_valid_topology_sound:
      "\<lbrakk> valid_reqs M; valid_graph \<lparr>nodes = V, edges = E\<rparr> \<rbrakk> \<Longrightarrow> 
      all_security_requirements_fulfilled M (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>)"
        proof(induction M arbitrary: V E)
          case Nil
          thus ?case by(simp add: all_security_requirements_fulfilled_def)
        next
          case (Cons m M)
          from valid_reqs1[OF Cons(2)] have validReq: "configured_SecurityInvariant m" .

          from Cons(3) have valid_rmUnOff: "valid_graph \<lparr>nodes = V, edges = E - (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>) \<rparr>"
            by(simp add: valid_graph_remove_edges)
          
          from configured_SecurityInvariant.sinvar_valid_remove_flattened_offending_flows[OF validReq Cons(3)]
          have valid_eval_rmUnOff: "c_sinvar m \<lparr>nodes = V, edges = E - (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>) \<rparr>" .
    
          from generate_valid_topology_subseteq_edges have edges_gentopo_subseteq: 
            "(edges (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>)) - (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>)
               \<subseteq>
            E - (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>)"  by fastforce
    
          from configured_SecurityInvariant.mono_sinvar[OF validReq valid_rmUnOff edges_gentopo_subseteq valid_eval_rmUnOff]
          have "c_sinvar m \<lparr>nodes = V, edges = (edges (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>)) - (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>) \<rparr>" .
          from this have goal1: 
            "c_sinvar m (delete_edges (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>))"
               by(simp add: delete_edges_simp2 generate_valid_topology_nodes)
    
          from valid_reqs2[OF Cons(2)] have "valid_reqs M" .
          from Cons.IH[OF `valid_reqs M` Cons(3)] have IH:
            "all_security_requirements_fulfilled M (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>)" .

          have generate_valid_topology_EX_graph_record:
            "\<exists> hypE. (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) = \<lparr>nodes = V, edges = hypE\<rparr> "
              apply(induction M arbitrary: V E)
               by(simp_all add: delete_edges_simp2 generate_valid_topology_nodes)
              
          from generate_valid_topology_EX_graph_record obtain E_IH where  E_IH_prop:
            "(generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) = \<lparr>nodes = V, edges = E_IH\<rparr>" by blast
    
          from valid_graph_generate_valid_topology[OF Cons(3)] E_IH_prop
          have valid_G_E_IH: "valid_graph \<lparr>nodes = V, edges = E_IH\<rparr>" by metis
    
          -- "@{thm IH[simplified E_IH_prop]}"
          -- "@{thm all_security_requirements_fulfilled_mono[OF `valid_reqs M` _  valid_G_E_IH IH[simplified E_IH_prop]]}"
    
          from all_security_requirements_fulfilled_mono[OF `valid_reqs M` _  valid_G_E_IH IH[simplified E_IH_prop]] have mono_rule:
            "\<And> E'. E' \<subseteq> E_IH \<Longrightarrow> all_security_requirements_fulfilled M \<lparr>nodes = V, edges = E'\<rparr>" .
    
          have "all_security_requirements_fulfilled M 
            (delete_edges (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>))"
            apply(subst E_IH_prop)
            apply(simp add: delete_edges_simp2)
            apply(rule mono_rule)
            by fast
    
          from this have goal2:
            "(\<forall>ma\<in>set M.
            c_sinvar ma (delete_edges (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) (\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>)))"
            by(simp add: all_security_requirements_fulfilled_def)
    
          from goal1 goal2 
          show  "all_security_requirements_fulfilled (m # M) (generate_valid_topology (m # M) \<lparr>nodes = V, edges = E\<rparr>)" 
          by (simp add: all_security_requirements_fulfilled_def)
       qed

   (*TODO
    all offending flows uniquely defined \<Longrightarrow> generate_valid_topology is maximum topology
   *)
   (*
    add generate_valid_topology_max_topo from Composition_Theory_ENF to here!
   *)
  lemma generate_valid_topology_as_set: 
  "generate_valid_topology M G = delete_edges G (\<Union>m \<in> set M. (\<Union> (c_offending_flows m G)))"
   apply(induction M arbitrary: G)
    apply(simp_all add: delete_edges_simp2 generate_valid_topology_nodes) by fastforce

  (*text{*Does it also generate a maximum topology?*}
  definition max_topo :: "('v::vertex) SecurityInvariant_configured list \<Rightarrow> 'v graph \<Rightarrow> bool" where
    "max_topo M G \<equiv> all_security_requirements_fulfilled M G \<and> (
      \<forall> (v1, v2) \<in> (nodes G \<times> nodes G) - (edges G). \<not> all_security_requirements_fulfilled M (add_edge v1 v2 G))"*)

  (*end TODO*)



   subsection{* More Lemmata *}
     lemma (in configured_SecurityInvariant) c_sinvar_valid_imp_no_offending_flows: 
      "c_sinvar m G \<Longrightarrow> \<forall>x\<in>c_offending_flows m G. x = {}"
        by(simp add: valid_c_offending_flows)

     lemma all_security_requirements_fulfilled_imp_no_offending_flows:
        "valid_reqs M \<Longrightarrow> all_security_requirements_fulfilled M G \<Longrightarrow> (\<Union>m\<in>set M. \<Union>c_offending_flows m G) = {}"
        apply(induction M)
         apply(simp_all)
        apply(simp add: all_security_requirements_fulfilled_def)
        apply(clarify)
        apply(frule valid_reqs2, drule valid_reqs1)
        apply(drule(1) configured_SecurityInvariant.c_sinvar_valid_imp_no_offending_flows)
        by simp

    corollary all_security_requirements_fulfilled_imp_get_offending_empty:
      "valid_reqs M \<Longrightarrow> all_security_requirements_fulfilled M G \<Longrightarrow> get_offending_flows M G = {}"
      apply(frule(1) all_security_requirements_fulfilled_imp_no_offending_flows)
      apply(simp add: get_offending_flows_def)
      apply(thin_tac "all_security_requirements_fulfilled M G")
      apply(simp add: valid_reqs_def)
      apply(clarify)
      using configured_SecurityInvariant.empty_offending_contra
      by fastforce
  
    corollary generate_valid_topology_does_nothing_if_valid:
      "\<lbrakk> valid_reqs M; all_security_requirements_fulfilled M G\<rbrakk> \<Longrightarrow> 
          generate_valid_topology M G = G"
      by(simp add: generate_valid_topology_as_set graph_ops all_security_requirements_fulfilled_imp_no_offending_flows)


    lemma mono_extend_get_offending_flows: "\<lbrakk> valid_reqs M;
         valid_graph \<lparr>nodes = V, edges = E\<rparr>;
         E' \<subseteq> E;
         F' \<in> get_offending_flows M \<lparr>nodes = V, edges = E'\<rparr> \<rbrakk> \<Longrightarrow>
       \<exists>F\<in>get_offending_flows M \<lparr>nodes = V, edges = E\<rparr>. F' \<subseteq> F"
     apply(induction M)
      apply(simp add: get_offending_flows_def)
     apply(frule valid_reqs2, drule valid_reqs1)
     apply(simp add: get_offending_flows_def)
     apply(erule disjE)
      apply(drule(3) configured_SecurityInvariant.mono_extend_set_offending_flows)
      apply(erule bexE, rename_tac F)
      apply(rule_tac x="F" in bexI)
       apply(simp_all)
     apply blast
     done

     lemma get_offending_flows_subseteq_edges: "valid_reqs M \<Longrightarrow> F \<in> get_offending_flows M \<lparr>nodes = V, edges = E\<rparr> \<Longrightarrow> F \<subseteq> E"
      apply(induction M)
       apply(simp add: get_offending_flows_def)
      apply(simp add: get_offending_flows_def)
      apply(frule valid_reqs2, drule valid_reqs1)
      apply(simp add: configured_SecurityInvariant.valid_c_offending_flows)
      by blast

    thm configured_SecurityInvariant.offending_flows_union_mono
    lemma get_offending_flows_union_mono: "\<lbrakk>valid_reqs M; 
      valid_graph \<lparr>nodes = V, edges = E\<rparr>; E' \<subseteq> E \<rbrakk> \<Longrightarrow>
      \<Union>get_offending_flows M \<lparr>nodes = V, edges = E'\<rparr> \<subseteq> \<Union>get_offending_flows M \<lparr>nodes = V, edges = E\<rparr>"
      apply(induction M)
       apply(simp add: get_offending_flows_def)
      apply(frule valid_reqs2, drule valid_reqs1)
      apply(drule(2) configured_SecurityInvariant.offending_flows_union_mono)
      apply(simp add: get_offending_flows_def)
      by blast

    thm configured_SecurityInvariant.Un_set_offending_flows_bound_minus_subseteq'
    lemma Un_set_offending_flows_bound_minus_subseteq':"\<lbrakk>valid_reqs M; 
      valid_graph \<lparr>nodes = V, edges = E\<rparr>; E' \<subseteq> E;
      \<Union>get_offending_flows M \<lparr>nodes = V, edges = E\<rparr> \<subseteq> X \<rbrakk> \<Longrightarrow> \<Union>get_offending_flows M \<lparr>nodes = V, edges = E - E'\<rparr> \<subseteq> X - E'"
      proof(induction M)
      case Nil thus ?case by (simp add: get_offending_flows_def)
      next
      case (Cons m M)
        from Cons.prems(1) valid_reqs2 have "valid_reqs M" by force
        from Cons.prems(1) valid_reqs1 have "configured_SecurityInvariant m" by force
        from Cons.prems(4) have "\<Union>get_offending_flows M \<lparr>nodes = V, edges = E\<rparr> \<subseteq> X" by(simp add: get_offending_flows_def)
        from Cons.IH[OF `valid_reqs M` Cons.prems(2) Cons.prems(3) `\<Union>get_offending_flows M \<lparr>nodes = V, edges = E\<rparr> \<subseteq> X`] have IH: "\<Union>get_offending_flows M \<lparr>nodes = V, edges = E - E'\<rparr> \<subseteq> X - E'" .
        from Cons.prems(4) have "\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr> \<subseteq> X" by(simp add: get_offending_flows_def)
        from configured_SecurityInvariant.Un_set_offending_flows_bound_minus_subseteq'[OF `configured_SecurityInvariant m` Cons.prems(2) `\<Union>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr> \<subseteq> X`] have "\<Union>c_offending_flows m \<lparr>nodes = V, edges = E - E'\<rparr> \<subseteq> X - E'" .
        from this IH show ?case by(simp add: get_offending_flows_def)
      qed

      

end
