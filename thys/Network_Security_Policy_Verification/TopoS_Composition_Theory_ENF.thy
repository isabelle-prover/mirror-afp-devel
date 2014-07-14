theory TopoS_Composition_Theory_ENF
imports TopoS_Interface TopoS_Helper
begin



section{*Legacy: Composition of ENF-Structured Security Invariants *}
  text{*Composition theory for security invariants which look as follows: 
        @{term "\<forall> G nP. sinvar G nP = (\<forall> (e1, e2)\<in> edges G. P (nP e1) (nP e2))"}

  This theory only works for security invariants of the same type and is superseded by @{file "TopoS_Composition_Theory.thy"}.

  It still provides the @{text "generate_valid_topology_max_topo"} theorem at the end, which does not hold in the generic version.

  If you want executable code, you should not load this thy.
  *}


  (*'v should be of type ::vertex*)
  type_synonym ('v, 'a, 'b) network_security_requirement_ENF =
   "'a \<times> (('v) graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool) \<times> bool         \<times> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<times> ('v, 'a, 'b) TopoS_Params"
  (*\<bottom> \<times> sinvar                         \<times> receiver_violation \<times>  P                 \<times> scenario-specific information    *)



  definition valid_ENF :: "('v::vertex, 'a, 'b) network_security_requirement_ENF \<Rightarrow> bool" where
    "valid_ENF m \<equiv> (case m of (defbot, sinvar, receiver_violation, P, config) \<Rightarrow>
          SecurityInvariant sinvar defbot receiver_violation \<and>
          SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form sinvar P)"

  text{*WARNING!! @{typ "'a"} and @{typ "'b"} are the same for the complete list. 
              So the list of network security requirements does not model all requirements but only those of the 
              same type. The generic Composition theory does not have this problem. The @{text "generate_valid_topology_sound"} theorem holds for both!.
              However, the generic composition theory has no knowledge of the @{typ "('a \<Rightarrow> 'a \<Rightarrow> bool)"} predicate and hence cannot show maximality (so far). 
              Following the proof here, it should however be sufficient to have uniquely defined offending flows to get maximality. *}
  definition valid_ENFs :: "('v::vertex, 'a, 'b) network_security_requirement_ENF list \<Rightarrow> bool" where
    "valid_ENFs M \<equiv> \<forall> m \<in> set M. valid_ENF m"

  subsection {*Accessors*}
    definition c_nP :: "('v::vertex, 'a, 'b) network_security_requirement_ENF \<Rightarrow> ('v \<Rightarrow> 'a)" where
      "c_nP m = (case m of (defbot, sinvar, receiver_violation, P, config) \<Rightarrow> SecurityInvariant.node_props defbot config)"
  
    definition c_gP :: "('v::vertex, 'a, 'b) network_security_requirement_ENF \<Rightarrow> 'b" where
      "c_gP m = (case m of (defbot, sinvar, receiver_violation, P, config) \<Rightarrow> (model_global_properties config))"
    
    definition c_sinvar :: "('v::vertex, 'a, 'b) network_security_requirement_ENF \<Rightarrow> (('v) graph \<Rightarrow> bool)" where
      "c_sinvar m = (case m of (defbot, sinvar, receiver_violation, P, config) \<Rightarrow> \<lambda>G. sinvar G (c_nP m))"

    definition c_offending_flows :: "('v::vertex, 'a, 'b) network_security_requirement_ENF \<Rightarrow> (('v) graph \<Rightarrow> ('v \<times> 'v) set set)" where
      "c_offending_flows m = (case m of (defbot, sinvar, receiver_violation, P, config) \<Rightarrow> 
        (\<lambda>G. SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G (c_nP m)))"
    
    definition c_P :: "('v::vertex, 'a, 'b) network_security_requirement_ENF \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" where
      "c_P m \<equiv> (case m of (defbot, sinvar, receiver_violation, P, config) \<Rightarrow> P)"

  subsection {*Lemma*}
    
    lemma c_sinvar_simp: 
      "valid_ENF m \<Longrightarrow>
        c_sinvar m = (case m of (defbot, sinvar, receiver_violation, P, config) \<Rightarrow> 
          (\<lambda> G. (\<forall> (s, r)\<in> edges G. P (SecurityInvariant.node_props defbot config s) (SecurityInvariant.node_props defbot config r)))
          )"
      apply(simp add: valid_ENF_def)
      apply(clarify)
      apply(rename_tac defbot sinvar receiver_violation P config)
      apply(simp only: fun_eq_iff)
      apply(rule allI, rename_tac G)
      apply(simp add: SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form_def)
      by(simp add: c_sinvar_def c_nP_def)

    lemma c_sinvar_simp2: 
      "valid_ENF m \<Longrightarrow>
        m = (defbot, sinvar, receiver_violation, P, config) \<Longrightarrow>
        c_sinvar (defbot, sinvar, receiver_violation, P, config) G = 
        (\<forall> (s, r)\<in> edges G. P (SecurityInvariant.node_props defbot config s) (SecurityInvariant.node_props defbot config r))"
      apply(drule c_sinvar_simp)
      by force
    lemma c_sinvar_simp3: 
      "valid_ENF m \<Longrightarrow>
        c_sinvar m G = 
        (\<forall> (s, r)\<in> edges G. (c_P m) (c_nP m s) (c_nP m r))"
      apply(case_tac m)
      apply(rename_tac defbot sinvar receiver_violation P config)
      apply(drule_tac G=G and P=P and defbot=defbot and sinvar=sinvar and receiver_violation=receiver_violation and config=config in c_sinvar_simp2)
       apply simp
      apply(clarify)
      apply(simp only: c_nP_def c_gP_def c_P_def)
      by(clarify)
      
      
      


    lemma c_offending_flows_simp: 
      "valid_ENF m \<Longrightarrow> c_offending_flows m = 
      (\<lambda> G. (if (c_sinvar m G) then
          {}
         else 
          { {(e1,e2). (e1, e2) \<in> edges G \<and> \<not> (c_P m) (c_nP m e1) (c_nP m e2)} })
      )"
      apply(simp add: valid_ENF_def)
      apply(clarify)
      apply(rename_tac defbot sinvar receiver_violation P config)
      apply(simp only: fun_eq_iff)
      apply(rule allI, rename_tac G)
      apply(simp add: c_sinvar_def c_nP_def c_gP_def c_P_def c_offending_flows_def)
      thm SecurityInvariant_withOffendingFlows.ENF_offending_set
      apply(drule_tac G=G and P=P and nP="(SecurityInvariant.node_props defbot config)" 
          in SecurityInvariant_withOffendingFlows.ENF_offending_set)
      by simp

      lemma c_offending_flows_Union_simp: 
      "valid_ENF m \<Longrightarrow> \<Union> c_offending_flows m G = {(e1,e2). (e1, e2) \<in> edges G \<and> \<not> (c_P m) (c_nP m e1) (c_nP m e2)}"
      apply(frule c_offending_flows_simp)
      apply(simp split:split_if_asm)
      apply(clarify)
      apply(case_tac m)
      apply(rename_tac defbot sinvar receiver_violation P config)
      apply(drule_tac defbot=defbot and sinvar=sinvar and receiver_violation=receiver_violation and P=P 
          and config=config and G=G in c_sinvar_simp2)
       apply(simp)
      apply(simp)
      apply(simp add: c_nP_def c_gP_def c_P_def)
      apply(thin_tac "?a = ?b")
      by fastforce
      lemma c_offending_flows_Union_simp2: 
      "valid_ENF m \<Longrightarrow> 
      m = (defbot, sinvar, receiver_violation, P, config) \<Longrightarrow> 
      \<Union> c_offending_flows (defbot, sinvar, receiver_violation, P, config) G = 
        {(e1,e2). (e1, e2) \<in> edges G \<and> \<not> P (SecurityInvariant.node_props defbot config e1) (SecurityInvariant.node_props defbot config e2)}"
      apply(drule_tac G=G in c_offending_flows_Union_simp)
      by(simp add: c_nP_def c_gP_def c_P_def)
  

  subsection {*Algorithms*}
    (*Note: is only sinvar, not eval!!*)
    definition all_security_requirements_fulfilled :: "('v::vertex, 'a, 'b) network_security_requirement_ENF list \<Rightarrow> 'v graph \<Rightarrow> bool" where
      "all_security_requirements_fulfilled M G \<equiv> \<forall>m \<in> set M. (c_sinvar m) G"
  
  
    (*would be easier to remove at the end*)
    fun generate_valid_topology :: "('v::vertex, 'a, 'b) network_security_requirement_ENF list \<Rightarrow> 'v graph \<Rightarrow> 'v graph" where
      "generate_valid_topology [] G = G" |
      "generate_valid_topology (m#Ms) G = generate_valid_topology Ms (delete_edges G (\<Union> (c_offending_flows m G)))"



  subsection {*Lemmata*}
    lemma c_sinvar_mono:
    "\<lbrakk> valid_ENF m; E' \<subseteq> E; valid_graph \<lparr>nodes = V, edges = E\<rparr>; c_sinvar m \<lparr>nodes = V, edges = E\<rparr>\<rbrakk> \<Longrightarrow>
       c_sinvar m \<lparr>nodes = V, edges = E'\<rparr>"
     apply(cases m)
     apply(rename_tac defbot sinvar receiver_violation P config)
     apply(simp add: valid_ENF_def)
     apply(simp add: c_sinvar_def c_nP_def c_gP_def c_P_def c_offending_flows_def)
     apply clarify
     apply(subgoal_tac "SecurityInvariant_preliminaries sinvar")
      prefer 2
      apply(simp add: SecurityInvariant_def)
     apply(erule_tac SecurityInvariant_preliminaries.mono_sinvar)
       by simp_all

    lemma valid_ENFs1: "valid_ENFs (m # M) \<Longrightarrow> valid_ENF m"
      by(simp add: valid_ENFs_def)
    lemma valid_ENFs2: "valid_ENFs (m # M) \<Longrightarrow> valid_ENFs M"
      by(simp add: valid_ENFs_def)

    lemma all_security_requirements_fulfilled_mono:
    "\<lbrakk> valid_ENFs M; E' \<subseteq> E; valid_graph \<lparr> nodes = V, edges = E \<rparr> \<rbrakk> \<Longrightarrow>  
      all_security_requirements_fulfilled M \<lparr> nodes = V, edges = E \<rparr> \<Longrightarrow>
      all_security_requirements_fulfilled M \<lparr> nodes = V, edges = E' \<rparr>"
      apply(induction M arbitrary: E' E)
       apply(simp_all add: all_security_requirements_fulfilled_def)
      apply(rename_tac m M E' E)
      apply(rule conjI)
       apply(drule valid_ENFs1)
       apply(erule c_sinvar_mono)
         apply(simp_all)
       apply force
      apply(drule valid_ENFs2)
      apply blast
      done


    lemma c_sinvar_valid_imp_no_offending_flows: 
      "c_sinvar m G \<Longrightarrow> \<forall>x\<in>c_offending_flows m G. x = {}"
      apply(case_tac m)
      apply(rename_tac defbot sinvar receiver_violation P config)
      apply(simp add: c_sinvar_def)
      apply(simp add: c_nP_def c_gP_def)
      apply(simp add: c_offending_flows_def)
      apply(simp add: c_nP_def c_gP_def)
      apply(clarify)
      by(simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
          SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
          SecurityInvariant_withOffendingFlows.is_offending_flows_def)

    lemma all_security_requirements_fulfilled_imp_no_offending_flows:
      "all_security_requirements_fulfilled M G \<Longrightarrow> (\<Union>m\<in>set M. \<Union>c_offending_flows m G) = {}"
      apply(induction M)
       apply(simp_all)
      apply(simp add: all_security_requirements_fulfilled_def)
      using c_sinvar_valid_imp_no_offending_flows by metis


    lemma remove_offending_subseteq: "valid_ENF m \<Longrightarrow>
       E' \<subseteq> E \<Longrightarrow>
       {(e1, e2). (e1, e2) \<in> E' \<and> (\<forall>x\<in>c_offending_flows m \<lparr>nodes = V, edges = E'\<rparr>. (e1, e2) \<notin> x)}
        \<subseteq>
       {(e1, e2). (e1, e2) \<in> E \<and> (\<forall>x\<in>c_offending_flows m \<lparr>nodes = V, edges = E\<rparr>. (e1, e2) \<notin> x)}"
    apply(simp add: c_offending_flows_simp)
    apply auto
    apply(case_tac m)
    apply(simp add: c_sinvar_simp c_nP_def c_gP_def c_P_def) 
    by fast

    lemma generate_valid_topology_mono_edges:
    "\<lbrakk> valid_ENFs M; E' \<subseteq> E \<rbrakk> \<Longrightarrow>  
      edges (generate_valid_topology M \<lparr> nodes = V, edges = E' \<rparr>) \<subseteq> edges (generate_valid_topology M \<lparr> nodes = V, edges = E \<rparr>)"
      apply(induction M arbitrary: E' E)
       apply(simp_all)
      apply(simp add: delete_edges_def)
      apply(simp add: valid_ENFs_def)
      apply(rename_tac m M E' E)
      apply(simp add: remove_offending_subseteq)
      done


    lemma generate_valid_topology_subseteq_edges:
    "edges (generate_valid_topology M G) \<subseteq> (edges G)"
      apply(induction M arbitrary: G)
       apply(simp_all)
      apply(simp add: graph_ops)
      by force
  
    lemma generate_valid_topology_nodes:
    "nodes (generate_valid_topology M G) = (nodes G)"
      apply(induction M arbitrary: G)
       by(simp_all add: graph_ops)
  

    lemma valid_graph_generate_valid_topology: "valid_graph G \<Longrightarrow> valid_graph (generate_valid_topology M G)"
      apply(induction M arbitrary: G)
       by(simp_all)


  lemma generate_valid_topology_EX_graph_record:
  "\<exists> hypE. (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>) = \<lparr>nodes = V, edges = hypE\<rparr> "
    apply(induction M arbitrary: V E)
     apply(simp_all)
    by(simp add: graph_ops)

   
   subsection{*An easier generate topology function!*}
   text{*removing the offending flows at the end is easier to deal with as the Graph does not change during computation!! *}

        fun generate_valid_topology_2 :: "('v::vertex, 'a, 'b) network_security_requirement_ENF list \<Rightarrow> 'v graph \<Rightarrow> 'v graph" where
          "generate_valid_topology_2 [] G = G" |
          "generate_valid_topology_2 (m#Ms) G = delete_edges (generate_valid_topology_2 Ms G) (\<Union> (c_offending_flows m G))"
    
        lemma generate_valid_topology_2_nodes:
        "nodes (generate_valid_topology_2 M G) = (nodes G)"
          apply(induction M arbitrary: G)
           by(simp_all add: graph_ops)
    
        lemma generate_valid_topology_12_eq_rule: "edges (generate_valid_topology M G) = edges (generate_valid_topology_2 M G) 
          \<Longrightarrow> generate_valid_topology M G = generate_valid_topology_2 M G"
          apply(induction M arbitrary: G)
           apply(simp_all)
          apply(rule graph_eq_intro)
           by(simp add:generate_valid_topology_nodes generate_valid_topology_2_nodes delete_edges_simp2)+
    
    
        lemma helper_union_offending_different_models: "valid_ENF m \<Longrightarrow> valid_ENF a \<Longrightarrow> 
            (\<Union>c_offending_flows m G) \<union> (\<Union>c_offending_flows a \<lparr>nodes = nodes G, edges = edges G - \<Union>c_offending_flows m G\<rparr>)
            = (\<Union>c_offending_flows a G) \<union> (\<Union>c_offending_flows m G)"
        apply(simp add: c_offending_flows_Union_simp)
        by fast
    
        lemma generate_valid_topology_2_step_swap: 
          "valid_ENF m \<Longrightarrow> valid_ENFs M \<Longrightarrow>
            edges (generate_valid_topology_2 M \<lparr>nodes = nodes G, edges = edges G - (\<Union>c_offending_flows m G)\<rparr>) = 
            edges (generate_valid_topology_2 M G) - (\<Union>c_offending_flows m G)"
        apply(induction M arbitrary: G)
         apply(simp_all)
        apply(frule valid_ENFs2)
        apply(drule valid_ENFs1)
        apply(simp add: delete_edges_simp2)
        using helper_union_offending_different_models by blast
    
        lemma generate_valid_topology_1_2_eq: "\<lbrakk> valid_ENFs M\<rbrakk> \<Longrightarrow>
          generate_valid_topology M G = generate_valid_topology_2 M G"
        apply(rule generate_valid_topology_12_eq_rule)
        apply(induction M arbitrary: G)
         apply(simp_all)
        apply(frule valid_ENFs2)
        apply(simp)
        apply(drule valid_ENFs1)
        apply(simp add: delete_edges_simp2)
        apply(simp add: generate_valid_topology_2_step_swap)
        done


  
    lemma generate_valid_topology_2_mono_models:
    "\<lbrakk> valid_ENFs (m#M) \<rbrakk> \<Longrightarrow>  
      edges (generate_valid_topology_2 (m#M) \<lparr> nodes = V, edges = E \<rparr>) \<subseteq> edges (generate_valid_topology_2 M \<lparr> nodes = V, edges = E \<rparr>)"
      apply(induction M arbitrary: E m)
       apply(simp add: delete_edges_simp2)
       apply fastforce
      apply(simp add: delete_edges_simp2)
      by blast
    corollary generate_valid_topology_mono_models:
    "\<lbrakk> valid_ENFs (m#M) \<rbrakk> \<Longrightarrow>  
      edges (generate_valid_topology (m#M) \<lparr> nodes = V, edges = E \<rparr>) \<subseteq> edges (generate_valid_topology M \<lparr> nodes = V, edges = E \<rparr>)"
      apply(frule valid_ENFs2)
      apply(subst generate_valid_topology_1_2_eq, simp)
      apply(subst generate_valid_topology_1_2_eq, simp)
      using generate_valid_topology_2_mono_models by fastforce 

    lemma generate_valid_topology_2_subseteq_edges:
    "edges (generate_valid_topology_2 M G) \<subseteq> (edges G)"
      apply(induction M arbitrary: G)
       apply(simp_all)
      apply(simp add: delete_edges_simp2)
      by blast
    

  lemma generate_valid_topology_2_EX_graph_record:
  "\<exists> hypE. (generate_valid_topology_2 M \<lparr>nodes = V, edges = E\<rparr>) = \<lparr>nodes = V, edges = hypE\<rparr> "
    apply(induction M arbitrary: V E)
     apply(simp_all)
    apply(simp add: graph_ops generate_valid_topology_2_nodes)
    done

  text{* @{term generate_valid_topology} generates a valid topology! *}
  theorem generate_valid_topology_sound:
  "\<lbrakk> valid_ENFs M; valid_graph \<lparr>nodes = V, edges = E\<rparr> \<rbrakk> \<Longrightarrow> 
  all_security_requirements_fulfilled M (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>)"
    proof(induction M arbitrary: V E)
      case Nil thus ?case by(simp add: all_security_requirements_fulfilled_def)
    next
      case (Cons m M)
      assume hyp: "\<And>V E. valid_ENFs M \<Longrightarrow>
              valid_graph \<lparr>nodes = V, edges = E\<rparr> \<Longrightarrow> 
              all_security_requirements_fulfilled M (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>)"
      and a2: "valid_ENFs (m # M)"
      and a3: "valid_graph \<lparr>nodes = V, edges = E\<rparr>"
      
      from a2 have a2_hyp: "valid_ENFs M" by(simp add: valid_ENFs_def)
      from a2 have a2': "valid_ENF m" using valid_ENFs_def by force
      from this obtain defbot sinvar receiver_violation P config where m_components: 
          "m = (defbot, sinvar, receiver_violation, P, config) \<and>
          SecurityInvariant sinvar defbot receiver_violation \<and>
          SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form sinvar P"
          apply(simp add:valid_ENF_def)
          apply(case_tac m)
          by blast

      obtain hypE where hypE_prop: "\<lparr>nodes = V, edges = hypE\<rparr> = (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>)" 
        using generate_valid_topology_EX_graph_record by metis
      from valid_graph_generate_valid_topology[OF a3] hypE_prop
      have valid_hypE: "valid_graph \<lparr>nodes = V, edges = hypE\<rparr>" by force
      from generate_valid_topology_subseteq_edges[of M "\<lparr>nodes = V, edges = E\<rparr>"] hypE_prop 
      have hypE_subseteq_E: "hypE \<subseteq> E" by (metis graph.select_convs(2))


      obtain hypE' where hypE'_prop: "\<lparr>nodes = V, edges = hypE'\<rparr> = (generate_valid_topology (m#M) \<lparr>nodes = V, edges = E\<rparr>)" 
        using generate_valid_topology_EX_graph_record by metis
      from valid_graph_generate_valid_topology[OF a3, of "m#M"] hypE'_prop
      have valid_hypE': "valid_graph \<lparr>nodes = V, edges = hypE'\<rparr>" by force
      from generate_valid_topology_subseteq_edges[of "m#M" "\<lparr>nodes = V, edges = E\<rparr>"] hypE'_prop 
      have hypE_subseteq_E: "hypE' \<subseteq> E" by (metis graph.select_convs(2))

      from generate_valid_topology_mono_models[OF a2] hypE_prop hypE'_prop
      have "hypE' \<subseteq> hypE" by (metis graph.select_convs(2))


      from hyp[OF a2_hyp a3] have "all_security_requirements_fulfilled M (generate_valid_topology M \<lparr>nodes = V, edges = E\<rparr>)" by simp
      from all_security_requirements_fulfilled_mono[OF a2_hyp `hypE' \<subseteq> hypE` valid_hypE]
      hypE'_prop hypE_prop this
      have goal2: "all_security_requirements_fulfilled M (generate_valid_topology (m # M) \<lparr>nodes = V, edges = E\<rparr>)" by (metis)


      have goal1: "all_security_requirements_fulfilled [m] (generate_valid_topology (m # M) \<lparr>nodes = V, edges = E\<rparr>)"
        apply(subst generate_valid_topology_1_2_eq[OF a2])
        apply(simp add: all_security_requirements_fulfilled_def)
        apply(simp add: delete_edges_simp2 generate_valid_topology_2_nodes)
        apply(simp add: c_sinvar_simp2[OF a2'] m_components)
        apply(simp add: c_offending_flows_Union_simp2[OF a2' conjunct1[OF m_components]])
        using generate_valid_topology_2_subseteq_edges by fastforce
      

      have all_security_requirements_fulfilled_split:
      "\<And> X. all_security_requirements_fulfilled (m # M) (generate_valid_topology (m # M) \<lparr>nodes = V, edges = E\<rparr>) =
        (all_security_requirements_fulfilled [m] (generate_valid_topology (m # M) \<lparr>nodes = V, edges = E\<rparr>) \<and>
        all_security_requirements_fulfilled M (generate_valid_topology (m # M) \<lparr>nodes = V, edges = E\<rparr>))"
      by(simp add: all_security_requirements_fulfilled_def)

      show "all_security_requirements_fulfilled (m # M) (generate_valid_topology (m # M) \<lparr>nodes = V, edges = E\<rparr>)"
        apply(subst all_security_requirements_fulfilled_split)
        apply(rule conjI)
         apply(metis goal1)
        apply(metis goal2)
       done
      qed


  text{* We can also write @{term generate_valid_topology_2} as simply removing all offending flows *}  
  lemma generate_valid_topology_2_as_set: 
  "generate_valid_topology_2 M G = delete_edges G (\<Union>m \<in> set M. (\<Union> (c_offending_flows m G)))"
   apply(induction M arbitrary: G)
    apply(simp_all add: delete_edges_simp2 generate_valid_topology_2_nodes)
   by fastforce



  text{*Does it also generate a maximum topology?*}
  definition max_topo :: "('v::vertex, 'a, 'b) network_security_requirement_ENF list \<Rightarrow> 'v graph \<Rightarrow> bool" where
    "max_topo M G \<equiv> all_security_requirements_fulfilled M G \<and> (
      \<forall> (v1, v2) \<in> (nodes G \<times> nodes G) - (edges G). \<not> all_security_requirements_fulfilled M (add_edge v1 v2 G))"

  lemma "(nodes G \<times> nodes G) - (edges G) = edges (fully_connected G) - edges G" by(simp add: fully_connected_def)

  lemma generate_valid_topology_does_nothing_if_valid:
  "\<lbrakk> valid_ENFs M; valid_graph G; all_security_requirements_fulfilled M G\<rbrakk> \<Longrightarrow> 
      generate_valid_topology M G = G"
  apply(subst generate_valid_topology_1_2_eq, simp)
  apply(subst generate_valid_topology_2_as_set)
  apply(simp add: delete_edges_simp2)
  by(simp add: all_security_requirements_fulfilled_imp_no_offending_flows)


  lemma generate_valid_topology_generates_max_topo: "\<lbrakk> valid_ENFs M; valid_graph G; 
    \<not> all_security_requirements_fulfilled M (fully_connected G)\<rbrakk> \<Longrightarrow> 
      max_topo M (generate_valid_topology M (fully_connected G))"
  proof -
    assume valid_models: "valid_ENFs M"
    and    validG:       "valid_graph G"
    and    not_valid_by_default: "\<not> all_security_requirements_fulfilled M (fully_connected G)"

    obtain V E where VE_prop: "\<lparr> nodes = V, edges = E \<rparr> = generate_valid_topology M (fully_connected G)" by (metis graph.cases)
    hence VE_prop_2: "\<lparr> nodes = V, edges = E \<rparr> = generate_valid_topology_2 M (fully_connected G)" by(metis generate_valid_topology_1_2_eq[OF valid_models])
    hence VE_prop_asset:
      "\<lparr> nodes = V, edges = E \<rparr> = \<lparr> nodes = V, edges = V \<times> V - (\<Union>m\<in>set M. \<Union>c_offending_flows m (fully_connected G))\<rparr>"
      apply(simp)
      apply(subst(asm) generate_valid_topology_2_as_set)
      apply(subst generate_valid_topology_2_as_set)
      by(simp add: fully_connected_def delete_edges_simp2)

    from VE_prop_asset have E_prop: "E =  V \<times> V - (\<Union>m\<in>set M. \<Union>c_offending_flows m (fully_connected G))" by fast
    from VE_prop have V_prop: "nodes G =  V"
      apply(simp add: fully_connected_def) using generate_valid_topology_nodes by (metis graph.select_convs(1))

    from VE_prop valid_graph_generate_valid_topology[OF fully_connected_valid[OF validG]]
    have validG_VE: "valid_graph \<lparr> nodes = V, edges = E \<rparr>" by force

    from generate_valid_topology_sound[OF valid_models validG_VE] fully_connected_valid[OF validG]
         generate_valid_topology_1_2_eq[OF valid_models, simplified generate_valid_topology_2_as_set]
    have VE_all_valid: 
      "all_security_requirements_fulfilled M \<lparr> nodes = V, edges = V \<times> V - (\<Union>m\<in>set M. \<Union>c_offending_flows m (fully_connected G))\<rparr>"
      by (metis VE_prop VE_prop_asset fully_connected_def generate_valid_topology_sound valid_models)

    have "\<forall>(v1, v2) \<in> V \<times> V - E.
       \<not> all_security_requirements_fulfilled M \<lparr> nodes = V, edges = E \<union> {(v1, v2)}\<rparr>"
    proof(clarify, simp only: HOL.atomize_not)
      fix a b
      assume "(a, b) \<notin> E" and "a \<in> V" and "b \<in> V"

      have subst_hlp1: "(\<Union>m\<in>set M. \<Union>c_offending_flows m \<lparr>nodes = V, edges = V \<times> V\<rparr>) = 
            (\<Union>m\<in>set M. {(e1, e2). e1 \<in> V \<and> e2 \<in> V \<and> \<not> c_P m (c_nP m e1) (c_nP m e2)})"
      using c_offending_flows_Union_simp[of _ "\<lparr>nodes = V, edges = V \<times> V\<rparr>", simplified] valid_models[unfolded valid_ENFs_def]
      by blast

      have subst_hlp2: "\<And>G. \<forall>m\<in>set M. c_sinvar m G = (\<forall>(s, r)\<in>edges G. c_P m (c_nP m s) (c_nP m r))"      
      using c_sinvar_simp3 valid_models[unfolded valid_ENFs_def] by fast

      from not_valid_by_default 
      have EX_invalid_fully_connected: "\<exists> m \<in> set M. \<not> c_sinvar m \<lparr>nodes = V, edges = V \<times> V\<rparr>" 
        by(simp add: all_security_requirements_fulfilled_def fully_connected_def V_prop)
      hence EX_invalid_fully_connected_simp:
        "\<exists> m \<in> set M. \<not> (\<forall>(s, r)\<in> V \<times> V. c_P m (c_nP m s) (c_nP m r))" using subst_hlp2 by auto

      from `(a, b) \<notin> E`[simplified E_prop] have ab_prop:
        "(a, b) \<notin> V \<times> V - (\<Union>m\<in>set M. {(e1, e2). e1 \<in> V \<and> e2 \<in> V \<and> \<not> c_P m (c_nP m e1) (c_nP m e2)})"
      apply(simp only: fully_connected_def V_prop)
      apply(subst(asm) subst_hlp1) .

      from VE_all_valid have "\<forall>m\<in>set M. c_sinvar m 
        \<lparr>nodes = V, 
         edges = V \<times> V - (\<Union>m\<in>set M. {(e1, e2). (e1, e2) \<in> V \<times> V \<and> \<not> c_P m (c_nP m e1) (c_nP m e2)})
        \<rparr>"
        apply(simp add: all_security_requirements_fulfilled_def fully_connected_def)
        apply(simp add: V_prop)
        by(subst(asm) subst_hlp1)

      hence "\<forall>m\<in>set M. 
        (\<forall> (s,r) \<in> V \<times> V - (\<Union>m\<in>set M. {(e1, e2). (e1, e2) \<in> V \<times> V \<and> \<not> c_P m (c_nP m e1) (c_nP m e2)}). 
          c_P m (c_nP m s) (c_nP m r))"
      using c_sinvar_simp3 valid_models[unfolded valid_ENFs_def] by blast
      hence "(\<Union>m\<in>set M. {(e1, e2). (e1, e2) \<in> V \<times> V \<and> \<not> c_P m (c_nP m e1) (c_nP m e2)}) \<noteq> {}"
      using EX_invalid_fully_connected_simp by blast

      hence "\<exists> m \<in> set M. \<not> c_sinvar m \<lparr>nodes = V, edges = E \<union> {(a, b)}\<rparr>"
        apply(simp add: all_security_requirements_fulfilled_def)
        apply(simp add: E_prop)
        apply(simp add: fully_connected_def V_prop)
        apply(simp add: subst_hlp2)
        using `a \<in> V` `b \<in> V` ab_prop EX_invalid_fully_connected_simp
        by blast
        
      thus "\<not> all_security_requirements_fulfilled M \<lparr>nodes = V, edges = E \<union> {(a, b)}\<rparr>"
      by(simp add: all_security_requirements_fulfilled_def)
    qed 

    hence "\<forall>(v1, v2) \<in> V \<times> V - E.
       \<not> all_security_requirements_fulfilled M (add_edge v1 v2 \<lparr> nodes = V, edges = E \<rparr>)" 
        by(auto simp add: add_edge_def insert_absorb)
    from this VE_prop
    have "\<forall>(v1, v2)\<in>nodes (generate_valid_topology M (fully_connected G)) \<times> nodes (generate_valid_topology M (fully_connected G)) -
              edges (generate_valid_topology M (fully_connected G)).
       \<not> all_security_requirements_fulfilled M (add_edge v1 v2 (generate_valid_topology M (fully_connected G)))"
      by (metis graph.select_convs(1) graph.select_convs(2))
    thus "max_topo M (generate_valid_topology M (fully_connected G))"
      apply(simp add: max_topo_def)
      using generate_valid_topology_sound[OF valid_models] fully_connected_valid[OF validG] apply (metis graph.cases)
      done
  qed


  theorem generate_valid_topology_max_topo: "\<lbrakk> valid_ENFs M; valid_graph G \<rbrakk> \<Longrightarrow> 
      max_topo M (generate_valid_topology M (fully_connected G))"
  apply(case_tac "\<not> all_security_requirements_fulfilled M (fully_connected G)")
   apply(simp add: generate_valid_topology_generates_max_topo)
  apply(simp)
  apply(drule generate_valid_topology_does_nothing_if_valid)
    apply(auto simp add: fully_connected_valid)
  by(simp add: fully_connected_def max_topo_def)

end
