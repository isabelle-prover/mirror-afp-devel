theory SINVAR_BLPbasic
imports "../TopoS_Helper"
begin

subsection {* SecurityInvariant Basic Bell LaPadula  *}

type_synonym privacy_level = nat

definition default_node_properties :: "privacy_level"
  where  "default_node_properties \<equiv> 0"

fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> privacy_level) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> edges G. (nP e1) \<le> (nP e2))"

fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> privacy_level) \<Rightarrow> 'b \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"

definition receiver_violation :: "bool" where "receiver_violation \<equiv> True"


lemma sinvar_mono: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
  apply(simp only: SecurityInvariant_withOffendingFlows.sinvar_mono_def)
  apply(clarify)
  by auto


interpretation SecurityInvariant_preliminaries
where sinvar = sinvar
and verify_globals = verify_globals
  apply unfold_locales
    apply(frule_tac finite_distinct_list[OF wf_graph.finiteE])
    apply(erule_tac exE)
    apply(rename_tac list_edges)
    apply(rule_tac ff="list_edges" in SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_mono])
        apply(auto)[6]
   apply(auto simp add: SecurityInvariant_withOffendingFlows.is_offending_flows_def graph_ops)[1]
  apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_mono])
 done


lemma BLP_def_unique: "otherbot \<noteq> 0 \<Longrightarrow>
    \<exists>G p i f. wf_graph G \<and> \<not> sinvar G p \<and> f \<in> (SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G p) \<and>
       sinvar (delete_edges G f) p \<and>
        i \<in> snd ` f \<and> sinvar G (p(i := otherbot)) "
  apply(simp)
  apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_def)
  apply (simp add:graph_ops)
  apply (simp split: prod.split_asm prod.split)
  apply(rule_tac x="\<lparr> nodes=set [vertex_1,vertex_2], edges = set [(vertex_1,vertex_2)] \<rparr>" in exI, simp)
  apply(rule conjI)
   apply(simp add: wf_graph_def)
  apply(rule_tac x="(\<lambda> x. 0)(vertex_1 := 1, vertex_2 := 0)" in exI, simp)
  apply(rule_tac x="vertex_2" in exI, simp)
  apply(rule_tac x="set [(vertex_1,vertex_2)]" in exI, simp)
  done


(*Test instantiation without any fancy lemmata*)
(*
interpretation SecurityInvariant
where default_node_properties = default_node_properties
and sinvar = sinvar
and verify_globals = verify_globals
and receiver_violation = receiver_violation
  unfolding default_node_properties_def
  unfolding receiver_violation_def
  apply unfold_locales
  
  apply(simp)
  apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_def)
  apply (simp add:graph_ops)
  apply (simp split: prod.split_asm prod.split add:case_prod_beta)
   apply(auto intro!:bexI)[1]
   (*apply (smt image_iff offending_in_edges prod.collapse)*)
  apply(blast intro: BLP_def_unique)
done
*)
 

subsubsection {*ENF*}
  lemma zero_default_candidate: "\<And> nP e1 e2. \<not> (op \<le>::privacy_level \<Rightarrow> privacy_level \<Rightarrow> bool) (nP e1) (nP e2) \<Longrightarrow> \<not> (op \<le>) (nP e1) 0"
    by simp_all
  lemma zero_default_candidate_rule: "\<And> (nP::('v \<Rightarrow> privacy_level)) e1 e2. \<not> (nP e1) \<le> (nP e2) \<Longrightarrow> \<not> (nP e1) \<le> 0"
    by simp_all
  lemma privacylevel_refl: "(op \<le>::privacy_level \<Rightarrow> privacy_level \<Rightarrow> bool) e e"
    by(simp_all)
  lemma BLP_ENF: "SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form sinvar (op \<le>)"
    unfolding SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form_def
    by simp
  lemma BLP_ENF_refl: "SecurityInvariant_withOffendingFlows.ENF_refl sinvar (op \<le>)"
    unfolding SecurityInvariant_withOffendingFlows.ENF_refl_def
    apply(rule conjI)
     apply(simp add: BLP_ENF)
    apply(simp add: privacylevel_refl)
  done

  definition BLP_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> privacy_level) \<Rightarrow> ('v \<times> 'v) set set" where
  "BLP_offending_set G nP = (if sinvar G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> (nP e1) > (nP e2)} })"
  lemma BLP_offending_set: "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = BLP_offending_set"
    apply(simp only: fun_eq_iff SecurityInvariant_withOffendingFlows.ENF_offending_set[OF BLP_ENF] BLP_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto)
  done
   

  interpretation BLPbasic: SecurityInvariant_IFS sinvar verify_globals default_node_properties
  rewrites "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = BLP_offending_set"
    unfolding receiver_violation_def
    unfolding default_node_properties_def
    apply(unfold_locales)
      apply(rule ballI)
      apply(rule SecurityInvariant_withOffendingFlows.ENF_snds_refl_instance[OF BLP_ENF_refl])
         apply(simp_all add: BLP_ENF BLP_ENF_refl)[3]
     apply(erule default_uniqueness_by_counterexample_IFS)
     apply(fact BLP_def_unique)
    apply(fact BLP_offending_set)
   done


  lemma TopoS_BLPBasic: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by unfold_locales
   
hide_fact (open) sinvar_mono
hide_fact BLP_def_unique zero_default_candidate zero_default_candidate_rule privacylevel_refl BLP_ENF BLP_ENF_refl

hide_const (open) sinvar verify_globals receiver_violation default_node_properties

end
