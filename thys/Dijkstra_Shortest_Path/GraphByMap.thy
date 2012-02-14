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
    None \<Rightarrow> m1.update v m2.empty g |
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
      None \<Rightarrow> m1.update v' m2.empty g | Some _ \<Rightarrow> g
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
    :: "('m1,'V,'m2,'\<sigma>) map_iteratori \<Rightarrow> ('V,'W,'\<sigma>,'m1) graph_nodes_it"
    where
    "gbm_nodes_it mit g c f \<sigma>0 \<equiv> mit c (\<lambda>k v \<sigma>. f k \<sigma>) g \<sigma>0"

  lemma gbm_nodes_it_correct:
    assumes mit: "map_iteratei m1.\<alpha> m1.invar mit"
    shows "graph_nodes_it gbm_\<alpha> gbm_invar (gbm_nodes_it mit)"
  proof 
    fix g::'m1 and I::"('V set) \<Rightarrow> 'd \<Rightarrow> bool" and \<sigma>0::"'d" and 
      c::"'d \<Rightarrow> bool" and f::"'V \<Rightarrow> 'd \<Rightarrow> 'd"

    assume INV: "gbm_invar g"
      and I0: "I (nodes (gbm_\<alpha> g)) \<sigma>0"
      and IS: "\<And>S \<sigma> x. \<lbrakk>c \<sigma>; x \<in> S; I S \<sigma>; S \<subseteq> nodes (gbm_\<alpha> g)\<rbrakk> 
               \<Longrightarrow> I (S - {x}) (f x \<sigma>)"
    note [simp]=gbm_invar_split[OF INV]

    show "I {} (gbm_nodes_it mit g c f \<sigma>0) \<or>
          (\<exists>S\<subseteq>nodes (gbm_\<alpha> g).
              S \<noteq> {} \<and> \<not> c (gbm_nodes_it mit g c f \<sigma>0) 
              \<and> I S (gbm_nodes_it mit g c f \<sigma>0))"
      unfolding gbm_nodes_it_def
      apply (rule_tac I=I in 
        map_iteratei.iteratei_rule_P[OF mit])
      apply simp
      using I0 unfolding gbm_\<alpha>_def apply simp
      apply (rule IS, simp_all add: gbm_\<alpha>_def) []
      apply simp
      apply auto []
      done
  qed

  definition gbm_edges_it 
    :: "
      ('m1,'V,'m2,'\<sigma>) map_iteratori \<Rightarrow>
      ('m2,'V,'s3,'\<sigma>) map_iteratori \<Rightarrow>
      ('s3,'W,'\<sigma>) iteratori \<Rightarrow>
      ('V,'W,'\<sigma>,'m1) graph_edges_it"
    where
    "gbm_edges_it mit1 mit2 sit g c f \<sigma>0 \<equiv> 
      mit1 c (\<lambda>v m2 \<sigma>. 
        mit2 c (\<lambda>v' s3 \<sigma>. 
          sit c (\<lambda>w \<sigma>. f (v,w,v') \<sigma>) s3 \<sigma>
        ) m2 \<sigma>
      ) g \<sigma>0
    "

  lemma gbm_edges_it_correct:
    assumes mit1: "map_iteratei m1.\<alpha> m1.invar mit1"
    assumes mit2: "map_iteratei m2.\<alpha> m2.invar mit2"
    assumes sit: "set_iteratei s3.\<alpha> s3.invar sit"
    shows "graph_edges_it gbm_\<alpha> gbm_invar (gbm_edges_it mit1 mit2 sit)"
  proof 
    fix g::'m1 and I::"(('V\<times>'W\<times>'V) set) \<Rightarrow> 'd \<Rightarrow> bool" and \<sigma>0::"'d" and 
      c::"'d \<Rightarrow> bool" and f::"('V\<times>'W\<times>'V) \<Rightarrow> 'd \<Rightarrow> 'd"

    have SUB: "\<And>it it' \<sigma>. I it \<sigma> \<Longrightarrow> it=it' \<Longrightarrow> I it' \<sigma>" by auto

    assume INV: "gbm_invar g"
      and I0: "I (edges (gbm_\<alpha> g)) \<sigma>0"
      and IS: "\<And>S \<sigma> x. \<lbrakk>c \<sigma>; x \<in> S; I S \<sigma>; S \<subseteq> edges (gbm_\<alpha> g)\<rbrakk> 
               \<Longrightarrow> I (S - {x}) (f x \<sigma>)"
    note [simp]=gbm_invar_split[OF INV]

    {
      fix \<sigma> it S thesis
      assume "I it \<sigma> \<or> (\<exists>it\<subseteq>S. I it \<sigma> \<and> \<not>c \<sigma>)"
      and "it\<subseteq>S"
      and "\<And>it. \<lbrakk>it\<subseteq>S; I it \<sigma>; it\<noteq>{}\<rbrakk> \<Longrightarrow> thesis"
      and "I {} \<sigma> \<Longrightarrow> thesis"
      hence thesis
        by auto
    } note AUX=this

    show "I {} (gbm_edges_it mit1 mit2 sit g c f \<sigma>0) \<or>
          (\<exists>S\<subseteq>edges (gbm_\<alpha> g).
              S \<noteq> {} \<and> \<not> c (gbm_edges_it mit1 mit2 sit g c f \<sigma>0) 
              \<and> I S (gbm_edges_it mit1 mit2 sit g c f \<sigma>0))"
      unfolding gbm_edges_it_def
      apply (rule_tac I="\<lambda>V \<sigma>. 
        I (edges (gbm_\<alpha> g) \<inter> V\<times>UNIV\<times>UNIV) \<sigma> \<or>
        (\<exists>it\<subseteq>edges (gbm_\<alpha> g). I it \<sigma> \<and> \<not>c \<sigma>)" 
        in 
        map_iteratei.iteratei_rule_P[OF mit1])
        apply simp

        apply (rule disjI1)
        using I0
        apply (erule_tac SUB)
        apply (auto simp add: gbm_\<alpha>_def) []

        prefer 2
        apply (erule disjE)
        apply simp
        apply (erule exE)
        apply (case_tac "it={}")
        apply simp
        apply auto []

        prefer 2 
        apply (erule AUX)
        apply auto [3]

        apply (rename_tac v m2 V \<sigma>)
        apply (rule_tac I="\<lambda>V' \<sigma>. I (edges (gbm_\<alpha> g) \<inter> (
          (V-{v})\<times>UNIV\<times>UNIV \<union>
          {v}\<times>UNIV\<times>V'
          )) \<sigma> \<or> (\<exists>it\<subseteq>edges (gbm_\<alpha> g). I it \<sigma> \<and> \<not>c \<sigma>)"
          in 
          map_iteratei.iteratei_rule_P[OF mit2])
          apply simp

          apply (erule disjE)
            apply (rule disjI1)
            apply (erule SUB)
            apply (auto simp: gbm_\<alpha>_def) []

            apply auto []

          prefer 2
          apply simp

          prefer 2
          apply (erule AUX)
          apply auto [3]

          apply (rename_tac v' s3 V' \<sigma>')
          apply (rule_tac I="\<lambda>W \<sigma>. I (edges (gbm_\<alpha> g) \<inter> (
            (V-{v})\<times>UNIV\<times>UNIV \<union>
            {v}\<times>UNIV\<times>(V'-{v'}) \<union>
            {v}\<times>W\<times>{v'}
            )) \<sigma> \<or> (\<exists>it\<subseteq>edges (gbm_\<alpha> g). I it \<sigma> \<and> \<not>c \<sigma>)"
            in 
            set_iteratei.iteratei_rule_P[OF sit])
            apply simp
          
            apply (rotate_tac -1 )
            apply (erule disjE)
              apply (rule disjI1)
              apply (erule SUB)
              apply (auto simp: gbm_\<alpha>_def) []

              apply auto []

            prefer 2
            apply (rotate_tac -1 )
            apply (erule disjE)
              apply (rule disjI1)
              apply simp

              apply auto []

            apply (rotate_tac -1 )
            apply (erule disjE)
              apply (rule disjI1)
              apply simp

              apply (rule_tac S1="(edges (gbm_\<alpha> g) \<inter> (
                (V-{v})\<times>UNIV\<times>UNIV \<union>
                {v}\<times>UNIV\<times>(V'-{v'}) \<union>
                {v}\<times>it\<times>{v'}
                ))" in IS[THEN SUB])
                apply (auto simp: gbm_\<alpha>_def) [5]
                
              apply auto []

            apply auto []
      done
  qed

  definition gbm_succ_it ::
    "('m2,'V,'s3,'\<sigma>) map_iteratori \<Rightarrow>
      ('s3,'W,'\<sigma>) iteratori \<Rightarrow>
      ('V,'W,'\<sigma>,'m1) graph_succ_it"
    where
  "gbm_succ_it mit2 sit g v c f \<sigma>0 \<equiv>
    case m1.lookup v g of
      None \<Rightarrow> \<sigma>0 |
      Some m2 \<Rightarrow> mit2 c (\<lambda>v' s3 \<sigma>. 
        sit c (\<lambda>w \<sigma>. f (w,v') \<sigma>) s3 \<sigma>
      ) m2 \<sigma>0
    "


  lemma gbm_succ_it_correct:
    assumes mit2: "map_iteratei m2.\<alpha> m2.invar mit2"
    assumes sit: "set_iteratei s3.\<alpha> s3.invar sit"
    shows "graph_succ_it gbm_\<alpha> gbm_invar (gbm_succ_it mit2 sit)"
  proof 
    fix g::'m1 and v::"'V" 
      and I::"(('W\<times>'V) set) \<Rightarrow> 'd \<Rightarrow> bool" and \<sigma>0::"'d" and 
      c::"'d \<Rightarrow> bool" and f::"('W\<times>'V) \<Rightarrow> 'd \<Rightarrow> 'd"

    have SUB: "\<And>it it' \<sigma>. I it \<sigma> \<Longrightarrow> it=it' \<Longrightarrow> I it' \<sigma>" by auto

    assume INV: "gbm_invar g"
      and I0: "I (succ (gbm_\<alpha> g) v) \<sigma>0"
      and IS: "\<And>S \<sigma> x. \<lbrakk>c \<sigma>; x \<in> S; I S \<sigma>; S \<subseteq> succ (gbm_\<alpha> g) v\<rbrakk> 
               \<Longrightarrow> I (S - {x}) (f x \<sigma>)"
    note [simp]=gbm_invar_split[OF INV]

    {
      fix \<sigma> it S thesis
      assume "I it \<sigma> \<or> (\<exists>it\<subseteq>S. I it \<sigma> \<and> \<not>c \<sigma>)"
      and "it\<subseteq>S"
      and "\<And>it. \<lbrakk>it\<subseteq>S; I it \<sigma>; it\<noteq>{}\<rbrakk> \<Longrightarrow> thesis"
      and "I {} \<sigma> \<Longrightarrow> thesis"
      hence thesis
        by auto
    } note AUX=this

    show "I {} (gbm_succ_it mit2 sit g v c f \<sigma>0) \<or>
          (\<exists>S\<subseteq>succ (gbm_\<alpha> g) v.
              S \<noteq> {} \<and> \<not> c (gbm_succ_it mit2 sit g v c f \<sigma>0) 
              \<and> I S (gbm_succ_it mit2 sit g v c f \<sigma>0))"
    proof (cases "m1.lookup v g")
      case None hence "succ (gbm_\<alpha> g) v = {}"
        by (auto simp add: gbm_\<alpha>_def succ_def
          m1.correct)
      moreover from None have "gbm_succ_it mit2 sit g v c f \<sigma>0 = \<sigma>0"
        by (auto simp: gbm_succ_it_def)
      ultimately show ?thesis using I0 by auto
    next
      case (Some m2)
      hence [simp]: "m2.invar m2"
        "\<And>v s3. m2.\<alpha> m2 v = Some s3 \<Longrightarrow> s3.invar s3"
        by (auto simp: m1.correct)
      
      show ?thesis
        unfolding gbm_succ_it_def apply (simp add: Some)

        apply (rule_tac I="\<lambda>V' \<sigma>. 
          I (succ (gbm_\<alpha> g) v \<inter> UNIV\<times>V') \<sigma> \<or>
          (\<exists>it\<subseteq>succ (gbm_\<alpha> g) v. I it \<sigma> \<and> \<not>c \<sigma>)" 
          in 
          map_iteratei.iteratei_rule_P[OF mit2])
          
          apply simp

          apply (rule disjI1)
          using I0
          apply (erule_tac SUB)
          using Some apply (auto simp add: gbm_\<alpha>_def succ_def m1.correct) []

          prefer 2
          apply (erule disjE)
          apply simp
          apply (erule exE)
          apply (case_tac "it={}")
          apply simp
          apply auto []

          prefer 2
          apply (erule AUX)
          apply auto [3]

          apply (rename_tac v' s3 V' \<sigma>')
          apply (rule_tac I="\<lambda>W \<sigma>. I (succ (gbm_\<alpha> g) v \<inter> (
            UNIV\<times>(V'-{v'}) \<union>
            W\<times>{v'}
            )) \<sigma> \<or> (\<exists>it\<subseteq>succ (gbm_\<alpha> g) v. I it \<sigma> \<and> \<not>c \<sigma>)"
            in 
            set_iteratei.iteratei_rule_P[OF sit])
            apply (simp)
          
            apply (erule disjE)
              apply (rule disjI1)
              apply (erule SUB)
              using Some
              apply (auto simp: succ_def gbm_\<alpha>_def m1.correct) []

              apply auto []

            apply (rotate_tac -1 )
            apply (erule disjE)
              apply (rule disjI1)
              apply simp
              thm IS[rotated -2, THEN SUB]
              apply (erule IS[rotated -2, THEN SUB])
                apply auto [2]
                using Some apply (auto simp: gbm_\<alpha>_def succ_def m1.correct) []
                apply auto []
              
              using Some apply (auto simp: m1.correct) []
              
            apply auto []

            apply auto []
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
