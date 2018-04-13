section {* Exploration of Nondeterministic Büchi Automata *}

theory NBA_Nodes
imports
  DFS_Framework.Reachable_Nodes
  NBA_Implement
begin

  definition nba_G :: "('label, 'state) nba \<Rightarrow> 'state graph_rec" where
    "nba_G A \<equiv> \<lparr> g_V = UNIV, g_E = E_of_succ (successors A), g_V0 = initial A \<rparr>"

  lemma nba_G_graph[simp]: "graph (nba_G A)" unfolding nba_G_def graph_def by simp
  lemma nba_G_reachable_nodes: "op_reachable (nba_G A) = nodes A"
  unfolding op_reachable_def nba_G_def graph_rec.simps E_of_succ_def
  proof safe
    show "q \<in> nodes A" if "p \<in> initial A" "(p, q) \<in> {(u, v). v \<in> successors A u}\<^sup>*" for p q
      using that(2, 1) by induct auto
    show "p \<in> {(u, v). v \<in> successors A u}\<^sup>* `` initial A" if "p \<in> nodes A" for p
      using that rtrancl_image_advance by induct fast+
  qed

  context
  begin

    interpretation autoref_syn by this

    (* TODO: can these (synthetization + definition + autoref_rule) be done with less boilerplate? *)

    (* TODO: 90% of the time is spent in insert_glist for the successors set *)
    schematic_goal nbai_Gi:
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
      assumes [autoref_rules]: "(Ai, A) \<in> \<langle>L, S\<rangle> nbai_nba_rel"
      shows "(?f :: ?'a, nba_G A) \<in> ?A" unfolding nba_G_def successors_alt_def by autoref
    concrete_definition nbai_Gi uses nbai_Gi
    (* TODO: why are term local.nbai_Gi and term BA_Nodes.nbai_Gi not the same *)
    lemma nbai_Gi_refine[autoref_rules]:
      assumes "GEN_OP state_eq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      shows "(NBA_Nodes.nbai_Gi state_eq, nba_G) \<in> \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> \<langle>unit_rel, S\<rangle> g_impl_rel_ext"
      using nbai_Gi.refine assms unfolding autoref_tag_defs by blast

    schematic_goal nba_nodes:
      fixes S :: "('statei \<times> 'state) set"
      assumes [simp]: "finite ((g_E (nba_G A))\<^sup>* `` g_V0 (nba_G A))"
      assumes [autoref_ga_rules]: "is_bounded_hashcode S seq bhc"
      assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('statei) hms"
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
      assumes [autoref_rules]: "(Ai, A) \<in> \<langle>L, S\<rangle> nbai_nba_rel"
      shows "(?f :: ?'a, op_reachable (nba_G A)) \<in> ?R" by autoref
    concrete_definition nba_nodes uses nba_nodes
    lemma nba_nodes_refine[autoref_rules]:
      fixes S :: "('statei \<times> 'state) set"
      assumes "SIDE_PRECOND (finite (nodes A))"
      assumes "SIDE_GEN_ALGO (is_bounded_hashcode S seq bhc)"
      assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('statei) hms)"
      assumes "GEN_OP seq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      assumes "(Ai, A) \<in> \<langle>L, S\<rangle> nbai_nba_rel"
      shows "(NBA_Nodes.nba_nodes seq bhc hms Ai,
        (OP nodes ::: \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> \<langle>S\<rangle> ahs_rel bhc) $ A) \<in> \<langle>S\<rangle> ahs_rel bhc"
    proof -
      have "finite ((g_E (nba_G A))\<^sup>* `` g_V0 (nba_G A))"
        using assms(1) unfolding autoref_tag_defs nba_G_reachable_nodes[symmetric] by simp
      then show ?thesis using nba_nodes.refine assms
        unfolding autoref_tag_defs nba_G_reachable_nodes[symmetric] by blast
    qed

  end

end