theory Sepref_ICF_Bindings
imports Sepref_Tool 
  "../Collections/Refine_Dflt_ICF"
  "IICF/IICF"
begin

  subsection \<open>Sets by List\<close>

  (* TODO: Move to Collections *)
  lemma lsr_finite[simp, intro]: "(l,s)\<in>\<langle>R\<rangle>list_set_rel \<Longrightarrow> finite s"
    by (auto simp: list_set_rel_def br_def)

  lemma it_to_sorted_list_triv:  
    assumes "distinct l"
    shows "RETURN l \<le> it_to_sorted_list (\<lambda>_ _. True) (set l)"
    using assms unfolding it_to_sorted_list_def
    by refine_vcg auto

  lemma [sepref_gen_algo_rules]: "GEN_ALGO (return) (IS_TO_SORTED_LIST (\<lambda>_ _. True) (pure (\<langle>A\<rangle>list_set_rel)) (pure A))"
    unfolding GEN_ALGO_def IS_TO_SORTED_LIST_def
    apply (simp add: list_assn_pure_conv)
    apply rule
    apply rule
    apply (sep_auto simp: pure_def intro: it_to_sorted_list_triv simp: list_set_rel_def br_def)
    done

  lemma list_set_rel_compp:
    assumes "IS_LEFT_UNIQUE A" "IS_RIGHT_UNIQUE A"  
    shows "\<langle>Id\<rangle>list_set_rel O \<langle>A\<rangle>set_rel = \<langle>A\<rangle>list_set_rel"
  proof
    show "\<langle>Id\<rangle>list_set_rel O \<langle>A\<rangle>set_rel \<subseteq> \<langle>A\<rangle>list_set_rel"
    proof (clarsimp simp: list_set_rel_def in_br_conv set_rel_def)
      fix l
      assume "distinct l" "set l \<subseteq> Domain A"
      thus "(l, A `` set l) \<in> \<langle>A\<rangle>list_rel O br set distinct"
      proof (induction l)
        case (Cons x l)
        hence IH: "(l, A `` set l) \<in> \<langle>A\<rangle>list_rel O br set distinct" by simp
        then obtain m where LMR: "(l,m)\<in>\<langle>A\<rangle>list_rel" and MD: "(m,A``set l)\<in>br set distinct" by auto
        from Cons.prems obtain y where "(x,y)\<in>A" by auto
    
        have [simp]: "y\<notin>set m" 
        proof
          assume "y\<in>set m"
          with LMR obtain x' where "x'\<in>set l" "(x',y)\<in>A"
            by (fastforce simp: in_set_conv_decomp list_rel_append2 list_rel_split_left_iff)
          from \<open>(x',y)\<in>A\<close> \<open>(x,y)\<in>A\<close> have "x'=x" by (auto simp: IS_LEFT_UNIQUED[OF assms(1)])
          with \<open>x'\<in>set l\<close> \<open>distinct (x#l)\<close> show False by simp
        qed  
    
        from \<open>(x,y)\<in>A\<close> LMR have 1: "(x#l,y#m)\<in>\<langle>A\<rangle>list_rel" by simp
        also from MD Cons.prems \<open>(x,y)\<in>A\<close> have 2: "(y#m,A``set (x#l))\<in>br set distinct"
          by (auto simp: in_br_conv IS_RIGHT_UNIQUED[OF assms(2)]) 
        finally (relcompI) show ?case .
      qed (auto simp: in_br_conv)
    qed  
  next
    {
      fix x y
      have "(x,y) \<in> br set distinct O \<langle>A\<rangle>set_rel \<longleftrightarrow> distinct x \<and> (set x, y)\<in>\<langle>A\<rangle>set_rel"
        by (auto simp: in_br_conv)
    } note [simp] = this
  
    show "\<langle>Id\<rangle>list_set_rel O \<langle>A\<rangle>set_rel \<supseteq> \<langle>A\<rangle>list_set_rel"
      apply (clarsimp simp: list_set_rel_def in_br_conv; safe)
      using param_distinct[OF assms, param_fo] apply auto []
      using assms apply parametricity
      done
  qed


  lemma GEN_OP_EQ_Id: "GEN_OP op= op= (Id\<rightarrow>Id\<rightarrow>bool_rel)" by simp

  hide_const (open) Intf_Set.op_set_isEmpty Intf_Set.op_set_delete

  lemma autoref_import_set_unfolds:
    "{} = op_set_empty"
    "uncurry (RETURN oo op\<in>) = uncurry (RETURN oo op_set_member)"
    "Intf_Set.op_set_isEmpty = IICF_Set.op_set_is_empty"
    "Intf_Set.op_set_delete = IICF_Set.op_set_delete"
    "insert = IICF_Set.op_set_insert"
    by (auto intro!: ext)


  context fixes A :: "'a \<Rightarrow> 'ai \<Rightarrow> assn" begin
    private lemma APA: "\<lbrakk>PROP Q; CONSTRAINT is_pure A\<rbrakk> \<Longrightarrow> PROP Q" .
    private lemma APAru: "\<lbrakk>PROP Q; CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) A\<rbrakk> \<Longrightarrow> PROP Q" .
    private lemma APAlu: "\<lbrakk>PROP Q; CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) A\<rbrakk> \<Longrightarrow> PROP Q" .
    private lemma APAbu: "\<lbrakk>PROP Q; CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) A; CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) A\<rbrakk> \<Longrightarrow> PROP Q" .
    definition "list_set_assn = pure (\<langle>Id\<rangle>list_set_rel O \<langle>the_pure A\<rangle>set_rel)"
    context
      notes [fcomp_norm_unfold] = list_set_assn_def[symmetric]
      notes [simp] = IS_LEFT_UNIQUE_def
    begin

      lemmas hnr_op_ls_empty = list_set_autoref_empty[of Id, sepref_param, unfolded autoref_import_set_unfolds,
        FCOMP op_set_empty.fref[of "the_pure A"]]
      lemmas hnr_mop_ls_empty = hnr_op_ls_empty[FCOMP mk_mop_rl0_np[OF mop_set_empty_alt]]

      definition [simp]: "op_ls_empty = op_set_empty"
      sepref_register op_ls_empty
    
      lemmas hnr_op_ls_is_empty[sepref_fr_rules] = list_set_autoref_isEmpty[of Id, sepref_param, THEN APA, unfolded autoref_import_set_unfolds,
        FCOMP op_set_is_empty.fref[of "the_pure A"]]
      lemmas hnr_mop_ls_is_empty[sepref_fr_rules] = hnr_op_ls_is_empty[FCOMP mk_mop_rl1_np[OF mop_set_is_empty_alt]]

      lemmas hnr_op_ls_member[sepref_fr_rules] = list_set_autoref_member[OF GEN_OP_EQ_Id, sepref_param, THEN APAlu, unfolded autoref_import_set_unfolds,
        FCOMP op_set_member.fref[of "the_pure A"]]
      lemmas hnr_mop_ls_member[sepref_fr_rules] = hnr_op_ls_member[FCOMP mk_mop_rl2_np[OF mop_set_member_alt]]

      lemmas hnr_op_ls_insert[sepref_fr_rules] = list_set_autoref_insert[OF GEN_OP_EQ_Id, sepref_param, THEN APAru, unfolded autoref_import_set_unfolds,
        FCOMP op_set_insert.fref[of "the_pure A"]]
      lemmas hnr_mop_ls_insert[sepref_fr_rules] = hnr_op_ls_insert[FCOMP mk_mop_rl2_np[OF mop_set_insert_alt]]

      lemmas hnr_op_ls_delete[sepref_fr_rules] = list_set_autoref_delete[OF GEN_OP_EQ_Id, sepref_param, THEN APAbu, unfolded autoref_import_set_unfolds,
        FCOMP op_set_delete.fref[of "the_pure A"]]
      lemmas hnr_mop_ls_delete[sepref_fr_rules] = hnr_op_ls_delete[FCOMP mk_mop_rl2_np[OF mop_set_delete_alt]]

      text \<open>Adapting this optimization from Autoref. \<close>
      sepref_decl_op set_insert_dj: "insert" :: "[\<lambda>(x,s). x\<notin>s]\<^sub>f K \<times>\<^sub>r \<langle>K\<rangle>set_rel \<rightarrow> \<langle>K\<rangle>set_rel" 
        where "IS_RIGHT_UNIQUE K" "IS_LEFT_UNIQUE K" .
  
      lemma fold_set_insert_dj: "Set.insert = op_set_insert_dj" by simp

      lemma ls_insert_dj_hnr_aux: 
        "(uncurry (return oo Cons), uncurry mop_set_insert_dj) \<in> (pure Id)\<^sup>k *\<^sub>a (pure (\<langle>Id\<rangle>list_set_rel))\<^sup>k \<rightarrow>\<^sub>a pure (\<langle>Id\<rangle>list_set_rel)"
        using list_set_autoref_insert_dj[where R=Id,param_fo]
        apply (sep_auto intro!: hfrefI hn_refineI simp: pure_def refine_pw_simps eintros del: exI)
        apply force
        done

      lemmas ls_insert_dj_hnr[sepref_fr_rules] = ls_insert_dj_hnr_aux[THEN APAbu, FCOMP mop_set_insert_dj.fref[of "the_pure A"]]  
      lemmas ls_insert_dj_hnr_mop[sepref_fr_rules] 
        = ls_insert_dj_hnr[FCOMP mk_op_rl2[OF mop_set_insert_dj_alt]]

      private lemma hd_in_set_conv: "hd l \<in> set l \<longleftrightarrow> l\<noteq>[]" by auto
    
      lemma ls_pick_hnr_aux: "(return o hd, mop_set_pick) \<in> (pure (\<langle>Id\<rangle>list_set_rel))\<^sup>k \<rightarrow>\<^sub>a id_assn"
        apply (sep_auto 
          intro!: hfrefI hn_refineI 
          simp: pure_def IS_PURE_def IS_ID_def list_set_rel_def refine_pw_simps
          eintros del: exI)
        apply (auto simp: in_br_conv hd_in_set_conv)
        done    

      lemmas ls_pick_hnr[sepref_fr_rules] = ls_pick_hnr_aux[THEN APA,FCOMP mop_set_pick.fref[of "the_pure A"]]
      lemma ls_pick_hnr_mop[sepref_fr_rules]: "CONSTRAINT is_pure A \<Longrightarrow> (return \<circ> hd, op_set_pick) \<in> [\<lambda>s. s\<noteq>{}]\<^sub>a list_set_assn\<^sup>k \<rightarrow> A"
        using ls_pick_hnr
        by (simp add: hfref_to_ASSERT_conv mop_set_pick_alt[abs_def])

    end
  end    

  interpretation ls: set_custom_empty "return []" op_ls_empty
    by unfold_locales simp
  lemmas [sepref_fr_rules] = hnr_op_ls_empty[folded op_ls_empty_def]
    

end

