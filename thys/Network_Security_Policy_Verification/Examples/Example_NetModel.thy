theory Example_NetModel
imports "../TopoS_Interface" "../TopoS_Helper"
begin

text{* A toy example that defines a valid network security requirement model *}

definition default_node_properties :: "bool"
  where  "default_node_properties \<equiv> False"

fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> (edges G). (nP e1) \<and> (nP e2))"

fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"

(* we will not define receiver_violation!! Works for both! *)


lemma sinvar_mono: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
  apply(simp only: SecurityInvariant_withOffendingFlows.sinvar_mono_def)
  apply(clarify)
  by auto

 
-- "The preliminaries: mostly, sinvar is monotonic"
interpretation SecurityInvariant_preliminaries
where sinvar = sinvar
and verify_globals = verify_globals
  apply unfold_locales
  apply(frule_tac finite_distinct_list[OF wf_graph.finiteE])
  apply(erule_tac exE)
  apply(rename_tac list_edges)
  apply(rule_tac ff="list_edges" in SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_mono])
  apply(auto)[6]
  apply(auto simp add: SecurityInvariant_withOffendingFlows.is_offending_flows_def graph_ops)[2]
  apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_mono])
done


-- "With generic target focus"
interpretation Example_NetModel: SecurityInvariant
where default_node_properties = default_node_properties
and sinvar = sinvar
and verify_globals = verify_globals
and receiver_violation = receiver_violation (*yep, that's a variable*)
  unfolding default_node_properties_def
  apply unfold_locales

  -- "Secure bydefault"
  apply(simp)
  apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_def)
  apply (simp add: graph_ops)
  apply (simp split: prod.split_asm prod.split)
    apply blast

 -- "Uniqueness"
 apply(simp add:default_node_properties_def)
  apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_def)
  apply (simp add: graph_ops)
  apply (simp split: prod.split_asm prod.split)
  -- "proof by counter example: assume False is not the unique default parameter"
  apply(rule_tac x="\<lparr> nodes={vertex_1}, edges = {(vertex_1,vertex_1)} \<rparr>" in exI, simp)
  apply(rule conjI)
  apply(simp add: wf_graph_def)
  apply(rule_tac x="(\<lambda> x. default_node_properties)(vertex_1 := False)" in exI, simp add:default_node_properties_def)
  apply(case_tac receiver_violation)
    apply(simp_all)
    apply(rule_tac x="{(vertex_1,vertex_1)}" in exI, simp)+
done


text{*And we end up with a totally useless network security requirement model. I hope this was instructive.*}

end
