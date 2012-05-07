header {* Implementing Graphs by Maps *}
theory GraphByMap
imports "../Collections/Collections"
  GraphSpec GraphGA
begin


locale gbm_defs = 
  m1!: StdMap m1_ops +
  m2!: StdMap m2_ops +
  s3!: StdSet s3_ops +
  m1!: map_value_image_filter m1.\<alpha> m1.invar m1.\<alpha> m1.invar m1_mvif
  for m1_ops::"('V,'m2,'m1,_) map_ops_scheme"
  and m2_ops::"('V,'s3,'m2,_) map_ops_scheme"
  and s3_ops::"('W,'s3,_) set_ops_scheme"
  and m1_mvif :: "('V \<Rightarrow> 'm2 \<rightharpoonup> 'm2) \<Rightarrow> 'm1 \<Rightarrow> 'm1"
begin
  definition gbm_\<alpha> :: "('V,'W,'m1) graph_\<alpha>" where
    "gbm_\<alpha> m1 \<equiv>
    \<lparr> nodes = dom (m1.\<alpha> m1),
      edges = {(v,w,v'). 
        \<exists>m2 s3. m1.\<alpha> m1 v = Some m2 
          \<and> m2.\<alpha> m2 v' = Some s3
          \<and> w\<in>s3.\<alpha> s3
      }
    \<rparr>"

  definition "gbm_invar m1 \<equiv>
    m1.invar m1 \<and>
    (\<forall>m2\<in>ran (m1.\<alpha> m1). m2.invar m2 \<and>
      (\<forall>s3\<in>ran (m2.\<alpha> m2). s3.invar s3)
    ) \<and> valid_graph (gbm_\<alpha> m1)"


  lemma gbm_invar_split: 
    assumes "gbm_invar g"
    shows
    "m1.invar g"
    "\<And>v m2. m1.\<alpha> g v = Some m2 \<Longrightarrow> m2.invar m2"
    "\<And>v m2 v' s3. m1.\<alpha> g v = Some m2 \<Longrightarrow> m2.\<alpha> m2 v' = Some s3 \<Longrightarrow> s3.invar s3"
    "valid_graph (gbm_\<alpha> g)"
    using assms unfolding gbm_invar_def 
    by (auto intro: ranI)

end

definition "map_Sigma M1 F2 \<equiv> {
  (x,y). \<exists>v. M1 x = Some v \<and> y\<in>F2 v
}"

lemma map_Sigma_alt: "map_Sigma M1 F2 = Sigma (dom M1) (\<lambda>x.
  F2 (the (M1 x)))"
  unfolding map_Sigma_def
  by auto
  
sublocale gbm_defs < graph gbm_\<alpha> gbm_invar
proof
  fix g
  assume INV: "gbm_invar g"
  then interpret vg!: valid_graph "(gbm_\<alpha> g)" by (simp add: gbm_invar_def)
  
  from vg.E_valid
  show "fst ` edges (gbm_\<alpha> g) \<subseteq> nodes (gbm_\<alpha> g)" and
    "snd ` snd ` edges (gbm_\<alpha> g) \<subseteq> nodes (gbm_\<alpha> g)" .

  from INV show "finite (nodes (gbm_\<alpha> g))"
    unfolding gbm_invar_def gbm_\<alpha>_def by auto

  note [simp] = gbm_invar_split[OF INV]

  show "finite (edges (gbm_\<alpha> g))"
    apply (rule finite_imageD[where f="\<lambda>(v,e,v'). (v,v',e)"])
    apply (rule finite_subset[where B=
      "map_Sigma (m1.\<alpha> g) (\<lambda>m2. map_Sigma (m2.\<alpha> m2) (s3.\<alpha>))"])
    apply (auto simp add: map_Sigma_def gbm_\<alpha>_def) []
    apply (unfold map_Sigma_alt)
    apply (auto intro!: finite_SigmaI inj_onI)
    done
qed




(* TODO: Move to Misc *)
lemma ranE: 
  assumes "v\<in>ran m"
  obtains k where "m k = Some v"
  using assms
by (metis ran_restrictD restrict_map_self)
lemma option_bind_alt:
  "Option.bind x f = (case x of None \<Rightarrow> None | Some v \<Rightarrow> f v)"
  by (auto split: option.split)

context gbm_defs
begin

  definition gbm_empty :: "('V,'W,'m1) graph_empty" where 
    "gbm_empty \<equiv> m1.empty"

  lemma gbm_empty_correct: 
    "graph_empty gbm_\<alpha> gbm_invar gbm_empty"
    apply (unfold_locales)
    unfolding gbm_\<alpha>_def gbm_invar_def gbm_empty_def
    apply (auto simp: m1.correct Graph.empty_def)
    apply (unfold_locales)
    apply auto
    done

  definition gbm_add_node :: "('V,'W,'m1) graph_add_node" where
    "gbm_add_node v g \<equiv> case m1.lookup v g of
    None \<Rightarrow> m1.update v (m2.empty ()) g |
    Some _ \<Rightarrow> g"

  lemma gbm_add_node_correct:
    "graph_add_node gbm_\<alpha> gbm_invar gbm_add_node"
  proof
    fix g v
    assume INV: "gbm_invar g"
    note [simp]= gbm_invar_split[OF INV]
    show "gbm_\<alpha> (gbm_add_node v g) = add_node v (gbm_\<alpha> g)"
      unfolding gbm_\<alpha>_def gbm_add_node_def
      by (auto simp: m1.correct m2.correct s3.correct add_node_def
        split: option.split split_if_asm)
    
    thus "gbm_invar (gbm_add_node v g)"  
      unfolding gbm_invar_def
      apply (simp)
      unfolding gbm_\<alpha>_def gbm_add_node_def add_node_def 
      apply (auto simp: m1.correct m2.correct s3.correct add_node_def
        split: option.split split_if_asm elim!: ranE)
      done
  qed

  definition gbm_delete_node :: "('V,'W,'m1) graph_delete_node" where
    "gbm_delete_node v g \<equiv> let g=m1.delete v g in
    m1_mvif (\<lambda>_ m2. Some (m2.delete v m2)) g"

  lemma gbm_delete_node_correct:
    "graph_delete_node gbm_\<alpha> gbm_invar gbm_delete_node"
  proof
    fix g v
    assume INV: "gbm_invar g"
    note [simp]= gbm_invar_split[OF INV]
    show "gbm_\<alpha> (gbm_delete_node v g) = delete_node v (gbm_\<alpha> g)"
      unfolding gbm_\<alpha>_def gbm_delete_node_def
      by (auto simp: restrict_map_def option_bind_alt
        m1.correct m2.correct s3.correct m1.map_value_image_filter_correct
        delete_node_def
        split: option.split split_if_asm option.split_asm)

    thus "gbm_invar (gbm_delete_node v g)"  
      unfolding gbm_invar_def
      apply (simp)
      unfolding gbm_\<alpha>_def gbm_delete_node_def delete_node_def 
      apply (auto simp: restrict_map_def option_bind_alt
        m1.correct m2.correct s3.correct m1.map_value_image_filter_correct
        split: option.split split_if_asm option.split_asm elim!: ranE)
      done
  qed

  definition gbm_add_edge :: "('V,'W,'m1) graph_add_edge" where
    "gbm_add_edge v e v' g \<equiv> 
    let g = (case m1.lookup v' g of 
      None \<Rightarrow> m1.update v' (m2.empty ()) g | Some _ \<Rightarrow> g
    ) in
    case m1.lookup v g of 
      None \<Rightarrow> (m1.update v (m2.sng v' (s3.sng e)) g) |
      Some m2 \<Rightarrow> (case m2.lookup v' m2 of
        None \<Rightarrow> m1.update v (m2.update v' (s3.sng e) m2) g |
        Some s3 \<Rightarrow> m1.update v (m2.update v' (s3.ins e s3) m2) g)
    "

  lemma gbm_add_edge_correct:
    "graph_add_edge gbm_\<alpha> gbm_invar gbm_add_edge"
  proof
    fix g v e v'
    assume INV: "gbm_invar g"
    note [simp]= gbm_invar_split[OF INV]
    show "gbm_\<alpha> (gbm_add_edge v e v' g) = add_edge v e v' (gbm_\<alpha> g)"
      unfolding gbm_\<alpha>_def gbm_add_edge_def
      apply (auto simp: m1.correct m2.correct s3.correct 
        Let_def
        split: option.split split_if_asm)
      unfolding add_edge_def
      (* Strange: This is at the limit of auto's capabilities:
        Iterated auto [] works., but auto on all goals seems not to
        terminate. Using fastforce instead.
        *)
      apply (fastforce split: split_if_asm
        simp: m1.correct m2.correct s3.correct 
      )+
      done
    
    thus "gbm_invar (gbm_add_edge v e v' g)"  
      unfolding gbm_invar_def
      apply (simp)
      unfolding gbm_\<alpha>_def gbm_add_edge_def
      apply (force simp: m1.correct m2.correct s3.correct
        Let_def
        split: option.split split_if_asm elim!: ranE)
      done
  qed


  definition gbm_delete_edge :: "('V,'W,'m1) graph_delete_edge" where
    "gbm_delete_edge v e v' g \<equiv>
    case m1.lookup v g of
      None \<Rightarrow> g |
      Some m2 \<Rightarrow> (
        case m2.lookup v' m2 of
          None \<Rightarrow> g |
          Some s3 \<Rightarrow> m1.update v (m2.update v' (s3.delete e s3) m2) g
      )
    "

  lemma gbm_delete_edge_correct:
    "graph_delete_edge gbm_\<alpha> gbm_invar gbm_delete_edge"
  proof
    fix g v e v'
    assume INV: "gbm_invar g"
    note [simp]= gbm_invar_split[OF INV]
    show "gbm_\<alpha> (gbm_delete_edge v e v' g) = delete_edge v e v' (gbm_\<alpha> g)"
      unfolding gbm_\<alpha>_def gbm_delete_edge_def delete_edge_def
      apply (auto simp: m1.correct m2.correct s3.correct 
        Let_def
        split: option.split split_if_asm)
      done
    
    thus "gbm_invar (gbm_delete_edge v e v' g)"  
      unfolding gbm_invar_def
      apply (simp)
      unfolding gbm_\<alpha>_def gbm_delete_edge_def
      apply (auto simp: m1.correct m2.correct s3.correct
        Let_def
        split: option.split split_if_asm elim!: ranE)
      done
  qed

  definition gbm_nodes_it 
    :: "('m1 \<Rightarrow> ('V\<times>'m2,'\<sigma>) set_iterator) \<Rightarrow> ('V,'W,'\<sigma>,'m1) graph_nodes_it"
    where
    "gbm_nodes_it mit g \<equiv> map_iterator_dom (mit g)"

  lemma gbm_nodes_it_correct:
    assumes mit: "map_iteratei m1.\<alpha> m1.invar mit"
    shows "graph_nodes_it gbm_\<alpha> gbm_invar (gbm_nodes_it mit)"
  proof 
    interpret m: map_iteratei m1.\<alpha> m1.invar mit by fact

    fix g
    assume "gbm_invar g"
    hence MINV: "map_op_invar m1_ops g" unfolding gbm_invar_def by auto
    from map_iterator_dom_correct[OF m.iteratei_rule[OF MINV]]
    show "set_iterator (gbm_nodes_it mit g) (nodes (gbm_\<alpha> g))"
      unfolding gbm_nodes_it_def gbm_\<alpha>_def by simp
  qed
    
  term set_iterator_product

  definition gbm_edges_it 
    :: "
      ('m1 \<Rightarrow> ('V\<times>'m2,'\<sigma>) set_iterator) \<Rightarrow>
      ('m2 \<Rightarrow> ('V\<times>'s3,'\<sigma>) set_iterator) \<Rightarrow>
      ('s3 \<Rightarrow> ('W,'\<sigma>) set_iterator) \<Rightarrow>
      ('V,'W,'\<sigma>,'m1) graph_edges_it"
    where
    "gbm_edges_it mit1 mit2 sit g \<equiv> set_iterator_image 
      (\<lambda>((v1,m1),(v2,m2),w). (v1,w,v2)) 
      (set_iterator_product (mit1 g) 
        (\<lambda>(v,m2). set_iterator_product (mit2 m2) (\<lambda>(w,s3). sit s3)))
    "

  lemma gbm_edges_it_correct:
    assumes mit1: "map_iteratei m1.\<alpha> m1.invar mit1"
    assumes mit2: "map_iteratei m2.\<alpha> m2.invar mit2"
    assumes sit: "set_iteratei s3.\<alpha> s3.invar sit"
    shows "graph_edges_it gbm_\<alpha> gbm_invar (gbm_edges_it mit1 mit2 sit)"
  proof 
    fix g
    assume INV: "gbm_invar g"

    from INV have I1: "m1.invar g" unfolding gbm_invar_def by auto
    from INV have I2: "\<And>v m2. (v,m2)\<in>map_to_set (m1.\<alpha> g) \<Longrightarrow> m2.invar m2"
      unfolding gbm_invar_def map_to_set_def
      by (auto simp: ran_def)
    from INV have I3: "\<And>v m2 v' s. \<lbrakk>
      (v,m2)\<in>map_to_set (m1.\<alpha> g); 
      (v',s)\<in>map_to_set (m2.\<alpha> m2)\<rbrakk> 
      \<Longrightarrow> s3.invar s"
      unfolding gbm_invar_def map_to_set_def
      by (auto simp: ran_def)

    show "set_iterator (gbm_edges_it mit1 mit2 sit g) (edges (gbm_\<alpha> g))"
      unfolding gbm_edges_it_def
      apply (rule set_iterator_image_correct)
      apply (rule set_iterator_product_correct)
      apply (rule map_iteratei.iteratei_rule[OF mit1])
      apply (rule I1)
      apply (case_tac a)
      apply clarsimp
      apply (rule set_iterator_product_correct)
      apply (drule I2)
      apply (subgoal_tac "map_iterator (mit2 ba) 
        (map_op_\<alpha> m2_ops (snd (aa,ba)))")
      apply assumption
      apply (simp add: map_iteratei.iteratei_rule[OF mit2])

      apply (case_tac a)
      apply clarsimp
      apply (subgoal_tac "set_iterator (sit bb) 
        (s3.\<alpha> (snd (ab,bb)))")
      apply assumption
      apply (simp add: set_iteratei.iteratei_rule[OF sit] I3)
      
      apply (auto simp: inj_on_def map_to_set_def) []

      apply (force simp: gbm_\<alpha>_def map_to_set_def) []
      done
    qed

  definition gbm_succ_it ::
    "('m2 \<Rightarrow> ('V\<times>'s3,'\<sigma>) set_iterator) \<Rightarrow>
      ('s3 \<Rightarrow> ('W,'\<sigma>) set_iterator) \<Rightarrow>
      ('V,'W,'\<sigma>,'m1) graph_succ_it"
    where
  "gbm_succ_it mit2 sit g v \<equiv> case m1.lookup v g of
    None \<Rightarrow> set_iterator_emp |
    Some m2 \<Rightarrow> 
      set_iterator_image (\<lambda>((v',m2),w). (w,v')) 
        (set_iterator_product (mit2 m2) (\<lambda>(v',s). sit s))
    "
  
  lemma gbm_succ_it_correct:
    assumes mit2: "map_iteratei m2.\<alpha> m2.invar mit2"
    assumes sit: "set_iteratei s3.\<alpha> s3.invar sit"
    shows "graph_succ_it gbm_\<alpha> gbm_invar (gbm_succ_it mit2 sit)"
  proof 
    fix g v
    assume INV: "gbm_invar g"
    hence I1[simp]: "m1.invar g" unfolding gbm_invar_def by auto

    show "set_iterator (gbm_succ_it mit2 sit g v) (succ (gbm_\<alpha> g) v)"
    proof (cases "m1.lookup v g")
      case None hence "(succ (gbm_\<alpha> g) v) = {}"
        unfolding succ_def gbm_\<alpha>_def by (auto simp: m1.lookup_correct)
      with None show ?thesis unfolding gbm_succ_it_def
        by (auto simp: set_iterator_emp_correct)
    next
      case (Some m2)
      hence [simp]: "m2.invar m2" using gbm_invar_split[OF INV] 
        by (simp add: m1.lookup_correct)

      from INV Some have 
        I2: "\<And>v' s. (v', s) \<in> map_to_set (map_op_\<alpha> m2_ops m2) \<Longrightarrow> s3.invar s"
        unfolding gbm_invar_def
        by (auto simp: map_to_set_def ran_def m1.lookup_correct)
      
      from Some show ?thesis
        unfolding gbm_succ_it_def apply simp
        apply (rule set_iterator_image_correct)
        apply (rule set_iterator_product_correct)
        apply (rule map_iteratei.iteratei_rule)
        apply (rule mit2)
        apply simp
        apply (case_tac a, simp)
        apply (subgoal_tac "set_iterator (sit b) (s3.\<alpha> (snd (aa, b)))")
        apply assumption
        apply simp
        apply (rule set_iteratei.iteratei_rule[OF sit])
        apply (simp add: I2)

        apply (auto simp: inj_on_def map_to_set_def) []

        apply (force simp: succ_def gbm_\<alpha>_def map_to_set_def m1.lookup_correct)
        done
    qed
  qed
    

  definition 
    "gbm_from_list \<equiv> gga_from_list gbm_empty gbm_add_node gbm_add_edge"
  
  lemmas gbm_from_list_correct = gga_from_list_correct[
    OF gbm_empty_correct gbm_add_node_correct gbm_add_edge_correct,
    folded gbm_from_list_def]
  
end

end
