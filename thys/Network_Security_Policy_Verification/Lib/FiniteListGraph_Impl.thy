theory FiniteListGraph_Impl
imports 
  FiniteListGraph
  "../../Collections/ICF/impl/RBTSetImpl" (*red black trees*)
  (*maybe import the following only at the end*)
  "Efficient_Distinct"
  "~~/src/HOL/Library/Code_Char"
  "~~/src/HOL/Library/Code_Target_Nat"
begin



text {* A graph's validity can be tested with an executable function. *}  
  fun valid_list_graph_impl::"'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> bool" where
    "valid_list_graph_impl V [] = True" |
    "valid_list_graph_impl V ((v1,v2)#Es) = (v1 \<in> set V \<and> v2 \<in> set V \<and> valid_list_graph_impl V Es)"


  lemma valid_list_graph_impl_axioms_locale_props: 
    "valid_list_graph_impl V E \<longleftrightarrow> fst` set E \<subseteq> set V \<and> snd` set E \<subseteq> set V"
  by (induction E) auto

  (*making the \<in> more efficient*)
  fun valid_list_graph_impl_rs::"('v::linorder) rs \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> bool" where
    "valid_list_graph_impl_rs V [] = True" |
    "valid_list_graph_impl_rs V ((v1,v2)#Es) = (rs.memb v1 V \<and> rs.memb v2 V \<and> valid_list_graph_impl_rs V Es)"

  lemma[code]: "valid_list_graph_impl V E = valid_list_graph_impl_rs (rs.from_list V) E"
   apply(induction E)
    apply(simp add: rs.correct)
   apply(rename_tac e Es)
   apply(case_tac e)
   by(simp add: rs.correct)

  lemma[code]: "FiniteListGraph.valid_list_graph_axioms G = valid_list_graph_impl (nodesL G) (edgesL G)"
    by(simp add: FiniteListGraph.valid_list_graph_axioms_def valid_list_graph_impl_axioms_locale_props)

  text{*The list implementation matches the @{term "valid_graph"} definition*}
  theorem valid_list_graph_iff_valid_graph: 
    "valid_graph (list_graph_to_graph G) \<longleftrightarrow> valid_list_graph_axioms G"
  apply(unfold list_graph_to_graph_def valid_graph_def valid_list_graph_axioms_def valid_list_graph_impl_axioms_locale_props)
    by simp
  corollary valid_list_graph_iff_valid_graph_simplified: 
  "valid_graph \<lparr>nodes = set (nodesL G), edges = set (edgesL G)\<rparr> \<longleftrightarrow> valid_list_graph_axioms G"
  apply(simp add: valid_list_graph_iff_valid_graph[unfolded list_graph_to_graph_def, simplified])
  done


 
text {* Code examples. *}
  definition valid_graph_example where
  "valid_graph_example \<equiv> \<lparr> nodesL = [1::nat,4,6], edgesL = [(1,4), (1,6), (6,4)] \<rparr>"

  value[code] "valid_list_graph valid_graph_example"

  definition valid_graph_impl_example where
  "valid_graph_impl_example \<equiv> valid_list_graph valid_graph_example"


  export_code valid_list_graph empty add_node delete_node add_edge delete_edge in Scala


end
