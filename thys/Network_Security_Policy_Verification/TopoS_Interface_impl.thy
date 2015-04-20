theory TopoS_Interface_impl
imports "Lib/FiniteGraph" "Lib/FiniteListGraph" TopoS_Interface TopoS_Helper
begin

section{*Executable Implementation with Lists*}
  text {*Correspondence List Implementation and set Specification*}
  
  subsection{*Abstraction from list implementation to set specification*}
  text{*Nomenclature: @{text "_spec"} is the specification, @{text "_impl"} the corresponding implementation.*}

  text{*@{text "_spec"} and @{text "_impl"} only need to comply for @{const wf_graph}s. 
   We will always require the stricter @{const wf_list_graph}, which implies @{const wf_graph}.
  *}
  lemma "wf_list_graph G \<Longrightarrow> wf_graph (list_graph_to_graph G)"
    by %invisible (metis wf_list_graph_def wf_list_graph_iff_wf_graph)

  locale TopoS_List_Impl = 
    fixes default_node_properties :: "'a" ("\<bottom>") 
    and sinvar_spec::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool"
    and sinvar_impl::"('v::vertex) list_graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool"
    and verify_globals_spec::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool"
    and verify_globals_impl::"('v::vertex) list_graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool"
    and receiver_violation :: "bool"
    and offending_flows_impl::"('v::vertex) list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<times> 'v) list list"
    and node_props_impl::"('v::vertex, 'a, 'b) TopoS_Params \<Rightarrow> ('v \<Rightarrow> 'a)"
    and eval_impl::"('v::vertex) list_graph \<Rightarrow> ('v, 'a, 'b)TopoS_Params \<Rightarrow> bool"
    assumes
      spec: "SecurityInvariant sinvar_spec default_node_properties receiver_violation" --"specification is valid"
    and
      sinvar_spec_impl: "wf_list_graph G \<Longrightarrow> 
        (sinvar_spec (list_graph_to_graph G) nP) = (sinvar_impl G nP)"
    and
      verify_globals_spec_impl: "wf_list_graph G \<Longrightarrow> 
        (verify_globals_spec (list_graph_to_graph G) nP gP) = (verify_globals_impl G nP gP)"
    and
      offending_flows_spec_impl: "wf_list_graph G \<Longrightarrow> 
      (SecurityInvariant_withOffendingFlows.set_offending_flows sinvar_spec (list_graph_to_graph G) nP) = 
      set`set (offending_flows_impl G nP)"
    and 
      node_props_spec_impl: 
     "SecurityInvariant.node_props_formaldef default_node_properties P = node_props_impl P"
    and
      eval_spec_impl:
     "(distinct (nodesL G) \<and> distinct (edgesL G) \<and> 
     SecurityInvariant.eval sinvar_spec verify_globals_spec default_node_properties (list_graph_to_graph G) P ) = 
     (eval_impl G P)"

  subsection {* Security Invariants Packed*}

  text {* We pack all necessary functions and properties of a security invariant in a struct-like data structure.*}
  record ('v::vertex, 'a, 'b) TopoS_packed =
    nm_name :: "string"
    nm_receiver_violation :: "bool"
    nm_default :: "'a"
    nm_sinvar::"('v::vertex) list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool"
    nm_verify_globals::"('v::vertex) list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool"
    nm_offending_flows::"('v::vertex) list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<times> 'v) list list"
    nm_node_props::"('v::vertex, 'a, 'b) TopoS_Params \<Rightarrow> ('v \<Rightarrow> 'a)" 
    nm_eval::"('v::vertex) list_graph \<Rightarrow> ('v, 'a, 'b)TopoS_Params \<Rightarrow> bool"
    


   text{*The packed list implementation must comply with the formal definition. *}
   locale TopoS_modelLibrary =
    fixes m :: "('v::vertex, 'a, 'b) TopoS_packed" -- "concrete model implementation"
    and sinvar_spec::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool" --"specification"
    and verify_globals_spec::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool" --"specification"
    assumes
       name_not_empty: "length (nm_name m) > 0"
     and
       impl_spec: "TopoS_List_Impl 
        (nm_default m)
        sinvar_spec
        (nm_sinvar m)
        verify_globals_spec
        (nm_verify_globals m)
        (nm_receiver_violation m)
        (nm_offending_flows m)
        (nm_node_props m)
        (nm_eval m)"



  subsection{*Helpful Lemmata*}

  text{*show that @{term "sinvar"} complies*}
  lemma TopoS_eval_impl_proofrule: 
    assumes inst: "SecurityInvariant sinvar_spec default_node_properties receiver_violation"
    assumes ev: "\<And>nP. wf_list_graph G \<Longrightarrow> sinvar_spec (list_graph_to_graph G) nP = sinvar_impl G nP"
    assumes ver: "\<And> nP gP. wf_list_graph G \<Longrightarrow> verify_globals_spec (list_graph_to_graph G) nP gP = verify_globals_impl G nP gP"
    shows "
      (distinct (nodesL G) \<and> distinct (edgesL G) \<and> SecurityInvariant.eval sinvar_spec verify_globals_spec default_node_properties (list_graph_to_graph G) P) =
      (wf_list_graph G \<and> verify_globals_impl G (SecurityInvariant.node_props default_node_properties P) (model_global_properties P) \<and>
       sinvar_impl G (SecurityInvariant.node_props default_node_properties P))"
  proof (cases "wf_list_graph G")
    case True
    hence "(verify_globals_spec (list_graph_to_graph G) (SecurityInvariant.node_props default_node_properties P) (model_global_properties P) \<and>
       sinvar_spec (list_graph_to_graph G) (SecurityInvariant.node_props default_node_properties P)) =
      (verify_globals_impl G (SecurityInvariant.node_props default_node_properties P) (model_global_properties P) \<and>
       sinvar_impl G (SecurityInvariant.node_props default_node_properties P))"
      using ev ver by blast

    with inst show ?thesis
      unfolding wf_list_graph_def 
      by (simp add: wf_list_graph_iff_wf_graph SecurityInvariant.eval_def)
  next
    case False
    hence "(distinct (nodesL G) \<and> distinct (edgesL G) \<and> wf_list_graph_axioms G) = False"
      unfolding wf_list_graph_def by blast
    with False show ?thesis
      unfolding SecurityInvariant.eval_def[OF inst]
      by (fastforce simp: wf_list_graph_iff_wf_graph)
  qed


subsection {*Helper lemmata*}

  text{* Provide @{term sinvar} function and get back a function that computes the list of offending flows
  
  Exponential time!
  *}
  definition Generic_offending_list:: "('v list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool )\<Rightarrow> 'v list_graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<times> 'v) list list" where
    "Generic_offending_list sinvar G nP = [f \<leftarrow> (sublists (edgesL G)). 
    (\<not> sinvar G nP \<and> sinvar (FiniteListGraph.delete_edges G f) nP) \<and> 
      (\<forall>(e1, e2)\<in>set f. \<not> sinvar (add_edge e1 e2 (FiniteListGraph.delete_edges G f)) nP)]"
  
  
  text{*proof rule: if @{term sinvar} complies, @{const Generic_offending_list} complies *}
  lemma Generic_offending_list_correct: 
    assumes valid: "wf_list_graph G"
    assumes spec_impl: "\<And>G nP. wf_list_graph G \<Longrightarrow> sinvar_spec (list_graph_to_graph G) nP = sinvar_impl G nP"
    shows "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar_spec (list_graph_to_graph G) nP = 
      set`set( Generic_offending_list sinvar_impl G nP )"
  proof -
    have "\<And> P G. set ` {x \<in> set (sublists (edgesL G)). P G (set x)} = {x \<in> set ` set (sublists (edgesL G)). P G (x)}"
      by fastforce
    hence subset_sublists_filter: "\<And> G P. {f. f \<subseteq> edges (list_graph_to_graph G) \<and> P G f} 
    = set ` set [f\<leftarrow>sublists (edgesL G) . P G (set f)]"
      unfolding list_graph_to_graph_def
      by (auto simp: sublists_powset)

    from valid delete_edges_wf have "\<forall>f. wf_list_graph(FiniteListGraph.delete_edges G f)" by fast
    with spec_impl[symmetric] FiniteListGraph.delete_edges_correct[of "G"] have impl_spec_delete:
      "\<forall>f. sinvar_impl (FiniteListGraph.delete_edges G f) nP = 
          sinvar_spec (FiniteGraph.delete_edges (list_graph_to_graph G) (set f)) nP" by simp

    from spec_impl[OF valid, symmetric] have impl_spec_not:
      "(\<not> sinvar_impl G nP) = (\<not> sinvar_spec (list_graph_to_graph G) nP)" by auto

    from spec_impl[symmetric, OF FiniteListGraph.add_edge_wf[OF FiniteListGraph.delete_edges_wf[OF valid]]] have impl_spec_allE:
    "\<forall> e1 e2 E. sinvar_impl (FiniteListGraph.add_edge e1 e2 (FiniteListGraph.delete_edges G E)) nP =
    sinvar_spec (list_graph_to_graph (FiniteListGraph.add_edge e1 e2 (FiniteListGraph.delete_edges G E))) nP" by simp

    have list_graph: "\<And> e1 e2 G f. (list_graph_to_graph (FiniteListGraph.add_edge e1 e2 (FiniteListGraph.delete_edges G f))) = 
      (FiniteGraph.add_edge e1 e2 (FiniteGraph.delete_edges (list_graph_to_graph G) (set f)))"
    by(simp add: FiniteListGraph.add_edge_correct FiniteListGraph.delete_edges_correct)
    
    show ?thesis 
      unfolding SecurityInvariant_withOffendingFlows.set_offending_flows_def 
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def 
      SecurityInvariant_withOffendingFlows.is_offending_flows_def
      Generic_offending_list_def
        apply(subst impl_spec_delete)
        apply(subst impl_spec_not)
        apply(subst impl_spec_allE)
        apply(subst list_graph)
        apply(rule subset_sublists_filter)
        done
  qed

  lemma all_edges_list_I: "P (list_graph_to_graph G) = Pl G \<Longrightarrow> 
    (\<forall>(e1, e2)\<in> (edges (list_graph_to_graph G)). P (list_graph_to_graph G) e1 e2) = (\<forall>(e1, e2)\<in>set (edgesL G). Pl G e1 e2)"
  unfolding list_graph_to_graph_def
  by simp

  lemma all_nodes_list_I: "P (list_graph_to_graph G) = Pl G \<Longrightarrow> 
    (\<forall>n \<in> (nodes (list_graph_to_graph G)). P (list_graph_to_graph G) n) = (\<forall> n \<in>set (nodesL G). Pl G n)"
  unfolding list_graph_to_graph_def
  by simp




(*TODO: this should be a header of TopoS_Libary. The header should be printed BEFORE the imports are processed. *)
section{*Security Invariant Library*}
(*The SINVAR_* theory files all use the "subsection" command. Here is the top-section.*)

end
