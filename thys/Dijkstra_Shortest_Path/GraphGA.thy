header {* Generic Algorithms for Graphs *}
theory GraphGA
imports GraphSpec "../Collections/iterator/SetIteratorOperations"
begin

  definition gga_from_list :: 
    "('V,'W,'G) graph_empty \<Rightarrow> ('V,'W,'G) graph_add_node 
      \<Rightarrow> ('V,'W,'G) graph_add_edge 
    \<Rightarrow> ('V,'W,'G) graph_from_list"
    where 
    "gga_from_list e a u l \<equiv> 
      let (nl,el) = l;
        g1 = foldl (\<lambda>g v. a v g) (e ()) nl
      in foldl (\<lambda>g (v,e,v'). u v e v' g) g1 el"
  
  lemma gga_from_list_correct:
    fixes \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    assumes "graph_empty \<alpha> invar e"
    assumes "graph_add_node \<alpha> invar a"
    assumes "graph_add_edge \<alpha> invar u"
    shows "graph_from_list \<alpha> invar (gga_from_list e a u)"
  proof -
    interpret 
      graph_empty \<alpha> invar e + 
      graph_add_node \<alpha> invar a + 
      graph_add_edge \<alpha> invar u
      by fact+

    {
      fix nl el
      def g1\<equiv>"(foldl (\<lambda>g v. a v g) (e ()) nl)"
      def g2\<equiv>"(foldl (\<lambda>g (v,e,v'). u v e v' g) g1 el)"
      have "invar g1 \<and> \<alpha> g1 = \<lparr> nodes = set nl, edges = {} \<rparr>"
        unfolding g1_def
        by (induct nl rule: rev_induct)
           (auto simp: empty_correct add_node_correct empty_def add_node_def)
      hence "invar g2 
        \<and> \<alpha> g2 = \<lparr> nodes = set nl \<union> fst`set el \<union> snd`snd`set el,
                    edges = set el \<rparr>"
        unfolding g2_def
        by (induct el rule: rev_induct) (auto simp: add_edge_correct add_edge_def)
      hence "invar g2 \<and> adjl_\<alpha> (nl,el) = \<alpha> g2"
        unfolding adjl_\<alpha>_def by auto
    }
    thus ?thesis
      unfolding gga_from_list_def [abs_def]
      apply unfold_locales
      apply auto
      done
  qed
      
  term map_iterator_product

  definition gga_edges_it ::
    "('V,'W,'\<sigma>,'G) graph_nodes_it \<Rightarrow> ('V,'W,'\<sigma>,'G) graph_succ_it 
    \<Rightarrow> ('V,'W,'\<sigma>,'G) graph_edges_it"
    where "gga_edges_it ni si G \<equiv> set_iterator_product (ni G) (\<lambda>v. si G v)"

(*
    "gga_edges_it ni si G c f \<sigma>0 \<equiv> 
      ni G c (
        \<lambda>v \<sigma>. si G v c (\<lambda>(w,v') \<sigma>. f (v,w,v') \<sigma>) \<sigma>
      ) \<sigma>0
    "
*)

  lemma gga_edges_it_correct:
    fixes ni::"('V,'W,'\<sigma>,'G) graph_nodes_it"
    fixes \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    assumes "graph_nodes_it \<alpha> invar ni"
    assumes "graph_succ_it \<alpha> invar si"
    shows "graph_edges_it \<alpha> invar (gga_edges_it ni si)"
  proof -
    interpret graph_nodes_it \<alpha> invar ni +
      graph_succ_it \<alpha> invar si by fact+

    show ?thesis
    proof
      fix g
      assume INV: "invar g"
      
      from set_iterator_product_correct[OF 
        nodes_it_correct[OF INV] succ_it_correct[OF INV]]
      have "set_iterator (set_iterator_product (ni g) (\<lambda>v. si g v))
        (SIGMA v:nodes (\<alpha> g). succ (\<alpha> g) v)
        " .
      also have "(SIGMA v:nodes (\<alpha> g). succ (\<alpha> g) v) = edges (\<alpha> g)" 
        unfolding succ_def 
        by (auto dest: valid_graph.E_validD[OF valid[OF INV]])
      finally show "set_iterator (gga_edges_it ni si g) (edges (\<alpha> g))"
        unfolding gga_edges_it_def .
    qed
  qed
        
  definition gga_to_list :: 
    "('V,'W,_,'G) graph_nodes_it \<Rightarrow> ('V,'W,_,'G) graph_edges_it \<Rightarrow> 
     ('V,'W,'G) graph_to_list"
    where 
    "gga_to_list ni ei g \<equiv> 
      (ni g (\<lambda>_. True) (op #) [], ei g (\<lambda>_. True) (op #) [])
    "

  lemma gga_to_list_correct:
    fixes \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    assumes "graph_nodes_it \<alpha> invar ni"
    assumes "graph_edges_it \<alpha> invar ei"
    shows "graph_to_list \<alpha> invar (gga_to_list ni ei)"
  proof -
    interpret graph_nodes_it \<alpha> invar ni + 
      graph_edges_it \<alpha> invar ei
      by fact+

    show ?thesis
    proof 
      fix g
      assume [simp, intro!]: "invar g"
      then interpret valid_graph "\<alpha> g" by (rule valid)

      have "set (ni g (\<lambda>_. True) (op #) []) = V"
        apply (rule_tac I="\<lambda>it \<sigma>. set \<sigma> = V - it" 
          in set_iterator_rule_P[OF nodes_it_correct])
        by auto
      moreover have "set (ei g (\<lambda>_. True) (op #) []) = E"
        apply (rule_tac I="\<lambda>it \<sigma>. set \<sigma> = E - it" 
          in set_iterator_rule_P[OF edges_it_correct])
        by auto
      ultimately show "adjl_\<alpha> (gga_to_list ni ei g) = \<alpha> g"
        unfolding adjl_\<alpha>_def gga_to_list_def
        apply simp
        apply (rule graph.equality)
        apply (auto intro: E_validD)
        done
    qed
  qed

end
