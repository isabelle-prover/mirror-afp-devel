section {* Exploration of Büchi Automata *}

theory BA_Nodes
imports
  DFS_Framework.Reachable_Nodes
  BA_Implement
begin

  definition ba_G :: "('label, 'state, 'more) ba_scheme \<Rightarrow> ('state, 'more) graph_rec_scheme" where
    "ba_G A \<equiv> \<lparr> g_V = UNIV, g_E = E_of_succ (successors A), g_V0 = initial A, \<dots> = ba.more A \<rparr>"

  lemma ba_G_graph[simp]: "graph (ba_G A)" unfolding ba_G_def graph_def by simp
  lemma ba_G_reachable_nodes: "op_reachable (ba_G A) = nodes A"
  unfolding op_reachable_def ba_G_def graph_rec.simps E_of_succ_def
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

    schematic_goal bai_Gi:
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
      assumes [autoref_rules]: "(Ai, A) \<in> \<langle>L, S, M\<rangle> bai_ba_rel"
      shows "(?f :: ?'a, ba_G A) \<in> ?A" unfolding ba_G_def successors_alt_def by autoref
    concrete_definition bai_Gi uses bai_Gi
    (* TODO: why are term local.bai_Gi and term BA_Nodes.bai_Gi not the same *)
    lemma bai_Gi_refine[autoref_rules]:
      assumes "GEN_OP state_eq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      shows "(BA_Nodes.bai_Gi state_eq, ba_G) \<in> \<langle>L, S, M\<rangle> bai_ba_rel \<rightarrow> \<langle>M, S\<rangle> g_impl_rel_ext"
      using bai_Gi.refine assms unfolding autoref_tag_defs by blast

    schematic_goal ba_nodes:
      fixes S :: "('statei \<times> 'state) set"
      assumes [simp]: "finite ((g_E (ba_G A))\<^sup>* `` g_V0 (ba_G A))"
      assumes [autoref_ga_rules]: "is_bounded_hashcode S seq bhc"
      assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('statei) hms"
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
      assumes [autoref_rules]: "(Ai, A) \<in> \<langle>L, S, M\<rangle> bai_ba_rel"
      shows "(?f :: ?'a, op_reachable (ba_G A)) \<in> ?R" by autoref
    concrete_definition ba_nodes uses ba_nodes
    lemma ba_nodes_refine[autoref_rules]:
      fixes S :: "('statei \<times> 'state) set"
      assumes "SIDE_PRECOND (finite (nodes A))"
      assumes "SIDE_GEN_ALGO (is_bounded_hashcode S seq bhc)"
      assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('statei) hms)"
      assumes "GEN_OP seq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      assumes "(Ai, A) \<in> \<langle>L, S, M\<rangle> bai_ba_rel"
      shows "(BA_Nodes.ba_nodes seq bhc hms Ai,
        (OP nodes ::: \<langle>L, S, M\<rangle> bai_ba_rel \<rightarrow> \<langle>S\<rangle> ahs_rel bhc) $ A) \<in> \<langle>S\<rangle> ahs_rel bhc"
    proof -
      have "finite ((g_E (ba_G A))\<^sup>* `` g_V0 (ba_G A))"
        using assms(1) unfolding autoref_tag_defs ba_G_reachable_nodes[symmetric] by simp
      then show ?thesis using ba_nodes.refine assms
        unfolding autoref_tag_defs ba_G_reachable_nodes[symmetric] by blast
    qed

  end

end