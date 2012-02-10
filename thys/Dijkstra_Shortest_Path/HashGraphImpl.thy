header {* Graphs by Hashmaps *}
theory HashGraphImpl
imports GraphByMap "../Collections/Collections"
begin

text {*
  Abbreviation: hlg
*}

type_synonym ('V,'E) hlg = 
  "('V,('V,'E ls) HashMap.hashmap) HashMap.hashmap"


interpretation hlg_defs!: gbm_defs hm_ops hm_ops ls_ops hh_map_value_image_filter
  using hh_map_value_image_filter_impl
  apply intro_locales
  apply (simp add: hm_ops_def)
  done

definition hlg_\<alpha> :: "('V::hashable,'E) hlg \<Rightarrow> ('V,'E) graph" 
  where "hlg_\<alpha> \<equiv> hlg_defs.gbm_\<alpha>"
definition "hlg_invar \<equiv> hlg_defs.gbm_invar"
definition "hlg_empty \<equiv> hlg_defs.gbm_empty"
definition "hlg_add_node \<equiv> hlg_defs.gbm_add_node"
definition "hlg_delete_node \<equiv> hlg_defs.gbm_delete_node"
definition "hlg_add_edge \<equiv> hlg_defs.gbm_add_edge"
definition "hlg_delete_edge \<equiv> hlg_defs.gbm_delete_edge"
definition "hlg_from_list \<equiv> hlg_defs.gbm_from_list"

definition "hlg_nodes_it \<equiv> hlg_defs.gbm_nodes_it hm_iteratei"
definition "hlg_edges_it \<equiv> hlg_defs.gbm_edges_it hm_iteratei hm_iteratei ls_iteratei"
definition "hlg_succ_it \<equiv> hlg_defs.gbm_succ_it hm_iteratei ls_iteratei"

definition "hlg_to_list \<equiv> gga_to_list hlg_nodes_it hlg_edges_it"

lemmas hlg_gbm_defs = 
  hlg_defs.gbm_empty_def_raw
  hlg_defs.gbm_add_node_def_raw
  hlg_defs.gbm_delete_node_def_raw
  hlg_defs.gbm_add_edge_def_raw
  hlg_defs.gbm_delete_edge_def_raw
  hlg_defs.gbm_from_list_def_raw
  hlg_defs.gbm_nodes_it_def_raw
  hlg_defs.gbm_succ_it_def_raw
  hlg_defs.gbm_edges_it_def_raw

lemmas hlg_defs = 
  hlg_\<alpha>_def
  hlg_invar_def
  hlg_empty_def
  hlg_add_node_def
  hlg_delete_node_def
  hlg_add_edge_def
  hlg_delete_edge_def
  hlg_from_list_def
  hlg_to_list_def
  hlg_nodes_it_def
  hlg_edges_it_def
  hlg_succ_it_def


lemmas [code] = hlg_defs[unfolded hlg_gbm_defs]


lemmas hlg_empty_impl = hlg_defs.gbm_empty_correct[folded hlg_defs]
interpretation hlg!: graph_empty hlg_\<alpha> hlg_invar hlg_empty 
  using hlg_empty_impl .
lemmas hlg_add_node_impl = hlg_defs.gbm_add_node_correct[folded hlg_defs]
interpretation hlg!: graph_add_node hlg_\<alpha> hlg_invar hlg_add_node 
  using hlg_add_node_impl .
lemmas hlg_delete_node_impl = hlg_defs.gbm_delete_node_correct[folded hlg_defs]
interpretation hlg!: graph_delete_node hlg_\<alpha> hlg_invar hlg_delete_node 
  using hlg_delete_node_impl .
lemmas hlg_add_edge_impl = hlg_defs.gbm_add_edge_correct[folded hlg_defs]
interpretation hlg!: graph_add_edge hlg_\<alpha> hlg_invar hlg_add_edge 
  using hlg_add_edge_impl .
lemmas hlg_delete_edge_impl = hlg_defs.gbm_delete_edge_correct[folded hlg_defs]
interpretation hlg!: graph_delete_edge hlg_\<alpha> hlg_invar hlg_delete_edge 
  using hlg_delete_edge_impl .
lemmas hlg_from_list_impl = hlg_defs.gbm_from_list_correct[folded hlg_defs]
interpretation hlg!: graph_from_list hlg_\<alpha> hlg_invar hlg_from_list 
  using hlg_from_list_impl .

lemmas hlg_nodes_it_impl = hlg_defs.gbm_nodes_it_correct[
  folded hlg_defs,
  unfolded hm_ops_def, simplified, OF hm_iteratei_impl, folded hlg_defs
]
interpretation hlg!: graph_nodes_it hlg_\<alpha> hlg_invar hlg_nodes_it 
  using hlg_nodes_it_impl .

lemmas hlg_edges_it_impl = hlg_defs.gbm_edges_it_correct[folded hlg_defs, 
  unfolded hm_ops_def ls_ops_def, simplified, 
  OF hm_iteratei_impl hm_iteratei_impl ls_iteratei_impl, folded hlg_defs]
interpretation hlg!: graph_edges_it hlg_\<alpha> hlg_invar hlg_edges_it 
  using hlg_edges_it_impl .

lemmas hlg_succ_it_impl = hlg_defs.gbm_succ_it_correct[of hm_iteratei ls_iteratei,
  folded hlg_defs, unfolded hm_ops_def ls_ops_def, simplified,
  OF hm_iteratei_impl ls_iteratei_impl]
interpretation hlg!: graph_succ_it hlg_\<alpha> hlg_invar hlg_succ_it 
  using hlg_succ_it_impl .

lemmas hlg_to_list_impl = gga_to_list_correct[OF 
  hlg_nodes_it_impl hlg_edges_it_impl, simplified hlg_defs[symmetric]]
interpretation hlg!: graph_to_list hlg_\<alpha> hlg_invar hlg_to_list 
  using hlg_to_list_impl .

definition "hlg_ops \<equiv> \<lparr>
  gop_\<alpha> = hlg_\<alpha>,
  gop_invar = hlg_invar,
  gop_empty = hlg_empty,
  gop_add_node = hlg_add_node,
  gop_delete_node = hlg_delete_node,
  gop_add_edge = hlg_add_edge,
  gop_delete_edge = hlg_delete_edge,
  gop_from_list = hlg_from_list,
  gop_to_list = hlg_to_list
\<rparr>"

lemma hlg_ops_unfold[code_unfold]:
  "gop_\<alpha> hlg_ops = hlg_\<alpha>"
  "gop_invar hlg_ops = hlg_invar"
  "gop_empty hlg_ops = hlg_empty"
  "gop_add_node hlg_ops = hlg_add_node"
  "gop_delete_node hlg_ops = hlg_delete_node"
  "gop_add_edge hlg_ops = hlg_add_edge"
  "gop_delete_edge hlg_ops = hlg_delete_edge"
  "gop_from_list hlg_ops = hlg_from_list"
  "gop_to_list hlg_ops = hlg_to_list"
  by (simp_all add: hlg_ops_def)

lemma hlgr_impl: "StdGraph hlg_ops"
  apply (rule StdGraph.intro)
  apply (simp_all add: hlg_ops_def)
  apply unfold_locales
  done

interpretation hlgr!: StdGraph hlg_ops using hlgr_impl .

end
