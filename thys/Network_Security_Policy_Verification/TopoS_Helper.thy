theory TopoS_Helper
imports Main TopoS_Interface 
  TopoS_ENF
  vertex_example_simps
begin

lemma (in SecurityInvariant_preliminaries) sinvar_valid_remove_flattened_offending_flows:
  assumes "wf_graph \<lparr>nodes = nodesG, edges = edgesG\<rparr>"
  shows "sinvar \<lparr>nodes = nodesG, edges = edgesG - \<Union> (set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP) \<rparr> nP"
proof -
  { fix f
    assume *: "f\<in>set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP"

    from * have 1: "sinvar \<lparr>nodes = nodesG, edges = edgesG - f \<rparr> nP"
      by (metis (hide_lams, mono_tags) SecurityInvariant_withOffendingFlows.valid_without_offending_flows delete_edges_simp2 graph.select_convs(1) graph.select_convs(2))
    from * have 2: "edgesG - \<Union> (set_offending_flows \<lparr>nodes = nodesG, edges = edgesG\<rparr> nP) \<subseteq> edgesG - f"
      by blast
    note 1 2
  }
  with assms show ?thesis 
    by (metis (hide_lams, no_types) Diff_empty Union_empty defined_offending equals0I mono_sinvar wf_graph_remove_edges)
qed

end
