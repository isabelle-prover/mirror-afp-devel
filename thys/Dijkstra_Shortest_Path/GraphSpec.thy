header "Graph Interface"
theory GraphSpec
imports Main Graph "../Refine_Monadic/Refine" 
  (*"../Refine_Monadic/Refine_Autodet"*)
begin
  text {*
    This theory defines an ICF-style interface for graphs.
    *}

  type_synonym ('V,'W,'G) graph_\<alpha> = "'G \<Rightarrow> ('V,'W) graph"

  locale graph =
    fixes \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes invar :: "'G \<Rightarrow> bool"
    assumes finite[simp, intro!]:
      "invar g \<Longrightarrow> finite (nodes (\<alpha> g))"
      "invar g \<Longrightarrow> finite (edges (\<alpha> g))"
    assumes valid: "invar g \<Longrightarrow> valid_graph (\<alpha> g)"

  type_synonym ('V,'W,'G) graph_empty = 'G
  locale graph_empty = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes empty :: "'G"
    assumes empty_correct:
      "\<alpha> empty = Graph.empty"
      "invar empty"

  type_synonym ('V,'W,'G) graph_add_node = "'V \<Rightarrow> 'G \<Rightarrow> 'G"
  locale graph_add_node = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes add_node :: "'V \<Rightarrow> 'G \<Rightarrow> 'G"
    assumes add_node_correct:
      "invar g \<Longrightarrow> invar (add_node v g)"
      "invar g \<Longrightarrow> \<alpha> (add_node v g) = Graph.add_node v (\<alpha> g)"

  type_synonym ('V,'W,'G) graph_delete_node = "'V \<Rightarrow> 'G \<Rightarrow> 'G"
  locale graph_delete_node = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes delete_node :: "'V \<Rightarrow> 'G \<Rightarrow> 'G"
    assumes delete_node_correct:
      "invar g \<Longrightarrow> invar (delete_node v g)"
      "invar g \<Longrightarrow> \<alpha> (delete_node v g) = Graph.delete_node v (\<alpha> g)"

  type_synonym ('V,'W,'G) graph_add_edge = "'V \<Rightarrow>'W \<Rightarrow> 'V \<Rightarrow> 'G \<Rightarrow> 'G"
  locale graph_add_edge = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes add_edge :: "'V \<Rightarrow> 'W \<Rightarrow> 'V \<Rightarrow> 'G \<Rightarrow> 'G"
    assumes add_edge_correct:
      "invar g \<Longrightarrow> invar (add_edge v e v' g)"
      "invar g \<Longrightarrow> \<alpha> (add_edge v e v' g) = Graph.add_edge v e v' (\<alpha> g)"

  type_synonym ('V,'W,'G) graph_delete_edge = "'V \<Rightarrow>'W \<Rightarrow> 'V \<Rightarrow> 'G \<Rightarrow> 'G"
  locale graph_delete_edge = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes delete_edge :: "'V \<Rightarrow> 'W \<Rightarrow> 'V \<Rightarrow> 'G \<Rightarrow> 'G"
    assumes delete_edge_correct:
      "invar g \<Longrightarrow> invar (delete_edge v e v' g)"
      "invar g \<Longrightarrow> \<alpha> (delete_edge v e v' g) = Graph.delete_edge v e v' (\<alpha> g)"

  type_synonym ('V,'W,'\<sigma>,'G) graph_nodes_it = "'G \<Rightarrow> ('V,'\<sigma>) iteratori_tmpl"
  locale graph_nodes_it = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes nodes_it :: "'G \<Rightarrow> ('V,'\<sigma>) iteratori_tmpl"
    assumes nodes_it_correct:
      "invar g \<Longrightarrow> set_iteratori (nodes_it g) (Graph.nodes (\<alpha> g))"

  type_synonym ('V,'W,'\<sigma>,'G) graph_edges_it 
    = "'G \<Rightarrow> (('V\<times>'W\<times>'V),'\<sigma>) iteratori_tmpl"
  locale graph_edges_it = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes edges_it :: "('V,'W,'\<sigma>,'G) graph_edges_it"
    assumes edges_it_correct:
      "invar g \<Longrightarrow> set_iteratori (edges_it g) (Graph.edges (\<alpha> g))"

  type_synonym ('V,'W,'\<sigma>,'G) graph_succ_it = 
    "'G \<Rightarrow> 'V \<Rightarrow> ('W\<times>'V,'\<sigma>) iteratori_tmpl"
  locale graph_succ_it = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes succ_it :: "'G \<Rightarrow> 'V \<Rightarrow> ('W\<times>'V,'\<sigma>) iteratori_tmpl"
    assumes succ_it_correct:
      "invar g \<Longrightarrow> set_iteratori (succ_it g v) (Graph.succ (\<alpha> g) v)"

  subsection "Adjacency Lists"
  type_synonym ('V,'W) adj_list = "'V list \<times> ('V\<times>'W\<times>'V) list"

  definition adjl_\<alpha> :: "('V,'W) adj_list \<Rightarrow> ('V,'W) graph" where
    "adjl_\<alpha> l \<equiv> let (nl,el) = l in \<lparr>
      nodes = set nl \<union> fst`set el \<union> snd`snd`set el,
      edges = set el
    \<rparr>"

  (* TODO: Do we have naming conventions for such a lemma ? *)
  lemma adjl_is_graph: "graph adjl_\<alpha> (\<lambda>_. True)"
    apply (unfold_locales)
    unfolding adjl_\<alpha>_def
    by force+

  type_synonym ('V,'W,'G) graph_from_list = "('V,'W) adj_list \<Rightarrow> 'G"
  locale graph_from_list = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes from_list :: "('V,'W) adj_list \<Rightarrow> 'G"
    assumes from_list_correct:
      "invar (from_list l)"
      "\<alpha> (from_list l) = adjl_\<alpha> l"

  type_synonym ('V,'W,'G) graph_to_list = "'G \<Rightarrow> ('V,'W) adj_list"
  locale graph_to_list = graph +
    constrains \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    fixes to_list :: "'G \<Rightarrow> ('V,'W) adj_list"
    assumes to_list_correct:
      "invar g \<Longrightarrow> adjl_\<alpha> (to_list g) = \<alpha> g"

  subsection {* Record Based Interface *}
  record ('V,'W,'G) graph_ops =
    gop_\<alpha> :: "('V,'W,'G) graph_\<alpha>"
    gop_invar :: "'G \<Rightarrow> bool"
    gop_empty :: "('V,'W,'G) graph_empty"
    gop_add_node :: "('V,'W,'G) graph_add_node"
    gop_delete_node :: "('V,'W,'G) graph_delete_node"
    gop_add_edge :: "('V,'W,'G) graph_add_edge"
    gop_delete_edge :: "('V,'W,'G) graph_delete_edge"
    gop_from_list :: "('V,'W,'G) graph_from_list"
    gop_to_list :: "('V,'W,'G) graph_to_list"

  locale StdGraphDefs =
    fixes ops :: "('V,'W,'G,'m) graph_ops_scheme"
  begin
    abbreviation \<alpha> where "\<alpha> \<equiv> gop_\<alpha> ops"
    abbreviation invar where "invar \<equiv> gop_invar ops"
    abbreviation empty where "empty \<equiv> gop_empty ops"
    abbreviation add_node where "add_node \<equiv> gop_add_node ops"
    abbreviation delete_node where "delete_node \<equiv> gop_delete_node ops"
    abbreviation add_edge where "add_edge \<equiv> gop_add_edge ops"
    abbreviation delete_edge where "delete_edge \<equiv> gop_delete_edge ops"
    abbreviation from_list where "from_list \<equiv> gop_from_list ops"
    abbreviation to_list where "to_list \<equiv> gop_to_list ops"
  end

  locale StdGraph = StdGraphDefs +
    graph \<alpha> invar +
    graph_empty \<alpha> invar empty +
    graph_add_node \<alpha> invar add_node +
    graph_delete_node \<alpha> invar delete_node +
    graph_add_edge \<alpha> invar add_edge +
    graph_delete_edge \<alpha> invar delete_edge +
    graph_from_list \<alpha> invar from_list +
    graph_to_list \<alpha> invar to_list
  begin
    lemmas correct = empty_correct add_node_correct delete_node_correct 
      add_edge_correct delete_edge_correct
      from_list_correct to_list_correct 

  end

  subsection {* Refinement Framework Bindings *}
  lemma (in graph_nodes_it) nodes_it_is_iteratori[refine_transfer]:
    "invar g \<Longrightarrow> set_iteratori (nodes_it g) (nodes (\<alpha> g))"
    by (rule nodes_it_correct)

  lemma (in graph_edges_it) edges_it_is_iteratori[refine_transfer]:
    "invar g \<Longrightarrow> set_iteratori (edges_it g) (edges (\<alpha> g))"
    by (rule edges_it_correct)
    
  lemma (in graph_succ_it) succ_it_is_iteratori[refine_transfer]:
    "invar g \<Longrightarrow> set_iteratori (succ_it g v) (Graph.succ (\<alpha> g) v)"
    by (rule succ_it_correct)

  lemma (in graph) drh[refine_dref_RELATES]: "RELATES (build_rel \<alpha> invar)"
    by (simp add: RELATES_def)

  (*text {* Autodet bindings: *}

  lemma (in graph_nodes_it) graph_nodes_it_t[trans_uc]:
    "DETREFe g (build_rel \<alpha> invar) g' \<Longrightarrow> 
      set_iteratori (nodes_it g) (nodes g')"
    using nodes_it_correct by auto

  lemma (in graph_succ_it) graph_succ_it_t[trans_uc]:
    "DETREFe g (build_rel \<alpha> invar) g' \<Longrightarrow> DETREFe v Id v' \<Longrightarrow>
      set_iteratori (succ_it g v) (succ g' v')"
    using succ_it_correct by auto

  lemma (in graph_edges_it) graph_edges_it_t[trans_uc]:
    "DETREFe g (build_rel \<alpha> invar) g' \<Longrightarrow> 
      set_iteratori (edges_it g) (edges g')"
    using edges_it_correct by auto*)

end
