header {* Generic Algorithms for Graphs *}
theory GraphGA
imports GraphSpec
begin

  definition gga_from_list :: 
    "('V,'W,'G) graph_empty \<Rightarrow> ('V,'W,'G) graph_add_node 
      \<Rightarrow> ('V,'W,'G) graph_add_edge 
    \<Rightarrow> ('V,'W,'G) graph_from_list"
    where 
    "gga_from_list e a u l \<equiv> 
      let (nl,el) = l;
        g1 = foldl (\<lambda>g v. a v g) e nl
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
      def g1\<equiv>"(foldl (\<lambda>g v. a v g) e nl)"
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
      
  definition gga_edges_it ::
    "('V,'W,'\<sigma>,'G) graph_nodes_it \<Rightarrow> ('V,'W,'\<sigma>,'G) graph_succ_it 
    \<Rightarrow> ('V,'W,'\<sigma>,'G) graph_edges_it"
    where
    "gga_edges_it ni si G c f \<sigma>0 \<equiv> 
      ni G c (
        \<lambda>v \<sigma>. si G v c (\<lambda>(w,v') \<sigma>. f (v,w,v') \<sigma>) \<sigma>
      ) \<sigma>0
    "

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
      fix g I and \<sigma>0::'\<sigma> and c f
      assume GI[simp, intro!]: "invar g"
      and I0: "I (edges (\<alpha> g)) \<sigma>0"
      and RULE: "\<And>S \<sigma> e. \<lbrakk>c \<sigma>; e\<in>S; I S \<sigma>; S\<subseteq>edges (\<alpha> g)\<rbrakk> 
                    \<Longrightarrow> I (S-{e}) (f e \<sigma>)"

      from valid[OF GI] interpret valid_graph "\<alpha> g" .

      show " I {} (gga_edges_it ni si g c f \<sigma>0) \<or>
        (\<exists>S\<subseteq>E. S \<noteq> {} \<and> \<not> c (gga_edges_it ni si g c f \<sigma>0) 
          \<and> I S (gga_edges_it ni si g c f \<sigma>0))"
        unfolding gga_edges_it_def
      proof (rule_tac 
          I="\<lambda>it \<sigma>. I (E \<inter> it\<times>UNIV\<times>UNIV) \<sigma> \<or>
            (\<not>c \<sigma> \<and> (\<exists>S\<subseteq>E. S\<noteq>{} \<and> I S \<sigma>))
          " 
          in
          set_iteratori.iterate_rule_P[OF nodes_it_correct[OF GI]])
        
        from E_valid have 
          "E \<inter> V\<times>UNIV\<times>UNIV
           = E" by auto
        with I0 show 
          "I (E \<inter> V\<times>UNIV\<times>UNIV) \<sigma>0 \<or> (\<not> c \<sigma>0 \<and> (\<exists>S\<subseteq>E. S\<noteq>{} \<and> I S \<sigma>0))"
          by simp
      next
        fix itV \<sigma> vt
        assume [simp, intro!]: "c \<sigma>" 
          and [simp, intro!]: "vt\<in>itV" 
          and IS0: "I (E \<inter> itV\<times>UNIV\<times>UNIV) \<sigma> 
            \<or> (\<not>c \<sigma> \<and> (\<exists>S\<subseteq>E. S\<noteq>{} \<and> I S \<sigma>))"
          and itV_SS: "itV \<subseteq> V"
        let ?inner = "(si g vt c (\<lambda>(w, v'). f (vt, w, v')) \<sigma>)"
        show "I (E \<inter> (itV-{vt})\<times>UNIV\<times>UNIV) ?inner \<or>
          (\<not> c ?inner \<and> (\<exists>S\<subseteq>E. S\<noteq>{} \<and> I S ?inner))
          "
        proof (rule_tac I="\<lambda>itS \<sigma>. I 
            ((E \<inter> (itV-{vt})\<times>UNIV\<times>UNIV) \<union> {vt}\<times>itS)
            \<sigma>" in 
          set_iteratori.iterate_rule_P[OF succ_it_correct[OF GI]])
          have "((E \<inter> (itV-{vt})\<times>UNIV\<times>UNIV) \<union> {vt}\<times>succ (\<alpha> g) vt)
            = (E \<inter> itV\<times>UNIV\<times>UNIV)"
            unfolding succ_def by auto
          with IS0 show 
            "I ((E \<inter> (itV-{vt})\<times>UNIV\<times>UNIV) \<union> {vt}\<times>succ (\<alpha> g) vt) \<sigma>" 
            by simp
        next
          fix itS \<sigma> wv
          assume [simp, intro!]: "c \<sigma>" 
            and [simp, intro!]: "wv\<in>itS" 
            and "I (E \<inter> (itV - {vt}) \<times> UNIV \<times> UNIV \<union> {vt} \<times> itS) \<sigma>"
          (is "I ?S _")
            and itS_SS: "itS \<subseteq> succ (\<alpha> g) vt"

          have "(vt,wv) \<in> ?S"
            using itS_SS unfolding succ_def by auto
          moreover have "?S\<subseteq>E"
            using itS_SS unfolding succ_def by auto
          moreover note `I ?S \<sigma>`
          ultimately have "I (?S-{(vt,wv)}) (f (vt,wv) \<sigma>)"
            by (auto intro!: RULE)
          also have "(?S-{(vt,wv)}) 
            = (E \<inter> (itV-{vt}) \<times> UNIV \<times> UNIV \<union> {vt} \<times> (itS-{wv}))"
            by auto
          also have "(f (vt,wv) \<sigma>) = (\<lambda>(w, v'). f (vt, w, v')) wv \<sigma>"
            by auto
          finally show 
            "I (E \<inter> (itV-{vt}) \<times> UNIV \<times> UNIV \<union> {vt} \<times> (itS-{wv})) 
               ((\<lambda>(w, v'). f (vt, w, v')) wv \<sigma>)" .
        next
          fix \<sigma>
          assume "I (E \<inter> (itV - {vt}) \<times> UNIV \<times> UNIV \<union> {vt} \<times> {}) \<sigma>"
          thus "I (E \<inter> (itV - {vt}) \<times> UNIV \<times> UNIV) \<sigma> \<or> 
            (\<not>c \<sigma> \<and> (\<exists>S\<subseteq>E. S\<noteq>{} \<and> I S \<sigma>))"
            by auto
        next
          fix \<sigma> S
          assume "S\<subseteq>succ (\<alpha> g) vt"
          and "S\<noteq>{}"
          and "\<not> c \<sigma>"
          and "I (E \<inter> (itV - {vt}) \<times> UNIV \<times> UNIV \<union> {vt} \<times> S) \<sigma>"
          thus "I (E \<inter> (itV - {vt}) \<times> UNIV \<times> UNIV) \<sigma> \<or> 
            (\<not>c \<sigma> \<and> (\<exists>S\<subseteq>E. S\<noteq>{} \<and> I S \<sigma>))"
            by (auto intro!: exI[where 
              x="(E \<inter> (itV - {vt}) \<times> UNIV \<times> UNIV \<union> {vt} \<times> S)" ]
              simp: succ_def)
        qed
      next
        fix \<sigma>
        assume "I (edges (\<alpha> g) \<inter> {} \<times> UNIV \<times> UNIV) \<sigma> 
          \<or> \<not> c \<sigma> \<and> (\<exists>S\<subseteq>edges (\<alpha> g). S \<noteq> {} \<and> I S \<sigma>)"
        thus "I {} \<sigma> \<or> (\<exists>S. S \<subseteq> edges (\<alpha> g) \<and> S \<noteq> {} \<and> \<not> c \<sigma> \<and> I S \<sigma>)"
          by auto
      next
        fix \<sigma> S
        assume "S \<subseteq> nodes (\<alpha> g)" 
          and [simp]: "S \<noteq> {}" 
          and [simp]: "\<not> c \<sigma>"
          and C: "I (edges (\<alpha> g) \<inter> S \<times> UNIV \<times> UNIV) \<sigma> 
               \<or> \<not> c \<sigma> \<and> (\<exists>S\<subseteq>edges (\<alpha> g). S \<noteq> {} \<and> I S \<sigma>)"
        from C show "I {} \<sigma> \<or> (\<exists>S. S \<subseteq> edges (\<alpha> g) \<and> S \<noteq> {} \<and> \<not> c \<sigma> \<and> I S \<sigma>)"
        proof 
          txt {* The case that the inner iterator was interrupted is trivial.
            Thus, we regard the case that the outer iterator was interrupted.
            In this case, the remaining nodes may or may not have outgoing edges.
            In the former case, we get a proper interrupt result. In the latter
            case, we are already finished.
            *}
          assume "I (edges (\<alpha> g) \<inter> S \<times> UNIV \<times> UNIV) \<sigma>"
          thus "I {} \<sigma> \<or> (\<exists>S\<subseteq>edges (\<alpha> g). S \<noteq> {} \<and> \<not> c \<sigma> \<and> I S \<sigma>)"
            apply (cases "(edges (\<alpha> g) \<inter> S \<times> UNIV \<times> UNIV) = {}")
            apply simp
            apply (rule disjI2)
            apply (rule_tac x="(edges (\<alpha> g) \<inter> S \<times> UNIV \<times> UNIV)" in exI)
            apply auto
            done
        qed simp
      qed
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
          in set_iteratori.iterate_rule_P[OF nodes_it_correct])
        by auto
      moreover have "set (ei g (\<lambda>_. True) (op #) []) = E"
        apply (rule_tac I="\<lambda>it \<sigma>. set \<sigma> = E - it" 
          in set_iteratori.iterate_rule_P[OF edges_it_correct])
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
