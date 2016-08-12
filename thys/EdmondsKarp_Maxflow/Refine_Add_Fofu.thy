theory Refine_Add_Fofu
imports Fofu_Impl_Base Refine_Monadic_Syntax_Sugar
  "../DFS_Framework/Misc/DFS_Framework_Refine_Aux"
begin

  notation Heap_Monad.return ("return")



  (* TODO: Integrate into Refinement Framework! *)

  lemma LFO_pre_refine: (* TODO: Move and generalize! *)
    assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
    assumes "(ci,c)\<in>R \<rightarrow> bool_rel"
    assumes "(fi,f)\<in>A\<rightarrow>R\<rightarrow>\<langle>R\<rangle>nres_rel"
    assumes "(s0i,s0)\<in>R"
    shows "LIST_FOREACH' (RETURN li) ci fi s0i \<le> \<Down>R (FOREACHci I l c f s0)"
  proof -
    from assms(1) have [simp]: "finite l" by (auto simp: list_set_rel_def br_def)
    show ?thesis
      unfolding FOREACHc_def FOREACHci_def FOREACHoci_by_LIST_FOREACH
      apply simp
      apply (rule LIST_FOREACH_autoref[param_fo, THEN nres_relD])
      using assms
      apply auto
      apply (auto simp: it_to_sorted_list_def nres_rel_def pw_le_iff refine_pw_simps
        list_set_rel_def br_def)
      done
  qed    
      

  lemma LFOci_refine: (* TODO: Move and generalize! *)
    assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
    assumes "\<And>s si. (si,s)\<in>R \<Longrightarrow> ci si \<longleftrightarrow> c s"
    assumes "\<And>x xi s si. \<lbrakk>(xi,x)\<in>A; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
    assumes "(s0i,s0)\<in>R"
    shows "nfoldli li ci fi s0i \<le> \<Down>R (FOREACHci I l c f s0)"
  proof -
    from assms LFO_pre_refine[of li l A ci c R fi f s0i s0] show ?thesis
      unfolding fun_rel_def nres_rel_def LIST_FOREACH'_def
      apply (simp add: pw_le_iff refine_pw_simps)
      apply blast+
      done
  qed    

  lemma LFOc_refine: (* TODO: Move and generalize! *)
    assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
    assumes "\<And>s si. (si,s)\<in>R \<Longrightarrow> ci si \<longleftrightarrow> c s"
    assumes "\<And>x xi s si. \<lbrakk>(xi,x)\<in>A; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
    assumes "(s0i,s0)\<in>R"
    shows "nfoldli li ci fi s0i \<le> \<Down>R (FOREACHc l c f s0)"
    unfolding FOREACHc_def
    by (rule LFOci_refine[OF assms])

    
  lemma LFO_refine: (* TODO: Move and generalize! *)
    assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
    assumes "\<And>x xi s si. \<lbrakk>(xi,x)\<in>A; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
    assumes "(s0i,s0)\<in>R"
    shows "nfoldli li (\<lambda>_. True) fi s0i \<le> \<Down>R (FOREACH l f s0)"
    unfolding FOREACH_def
    apply (rule LFOc_refine)
    apply (rule assms | simp)+
    done

  lemma LFOi_refine: (* TODO: Move and generalize! *)
    assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
    assumes "\<And>x xi s si. \<lbrakk>(xi,x)\<in>A; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
    assumes "(s0i,s0)\<in>R"
    shows "nfoldli li (\<lambda>_. True) fi s0i \<le> \<Down>R (FOREACHi I l f s0)"
    unfolding FOREACHi_def
    apply (rule LFOci_refine)
    apply (rule assms | simp)+
    done

  (* TODO: Move to refinement framework. Combine with select from CAVA-Base. *)
  definition "SELECTp P \<equiv> if Ex P then RES {Some x | x. P x} else RETURN None"

  lemma selectp_rule[refine_vcg]: 
    assumes "\<forall>x. \<not>P x \<Longrightarrow> RETURN None \<le> SPEC \<Phi>"
    assumes "\<And>x. P x \<Longrightarrow> RETURN (Some x) \<le> SPEC \<Phi>"
    shows "SELECTp P \<le> SPEC \<Phi>"
    using assms unfolding SELECTp_def
    by (auto)

  lemma selectp_refine_eq:
    "SELECTp P \<le> \<Down>(\<langle>R\<rangle>option_rel) (SELECTp Q) \<longleftrightarrow> 
    (\<forall>x. P x \<longrightarrow> (\<exists>y. (x,y)\<in>R \<and> Q y)) \<and> ((\<forall>x. \<not>P x) \<longrightarrow> (\<forall>y. \<not>Q y))"
    by (auto simp: SELECTp_def option_rel_def
      simp: pw_le_iff refine_pw_simps)

  lemma selectp_refine[refine]:
    assumes "SPEC P \<le>\<Down>R (SPEC Q)"  
    assumes "\<And>y. \<forall>x. \<not>P x \<Longrightarrow> \<not>Q y"
    shows "SELECTp P \<le> \<Down>(\<langle>R\<rangle>option_rel) (SELECTp Q)"
    unfolding selectp_refine_eq
    using assms by (auto simp: pw_le_iff refine_pw_simps)

  lemma selectp_refine_Id[refine]:  
    assumes "\<And>x. P x \<Longrightarrow> Q x"
    assumes "\<And>y. \<forall>x. \<not>P x \<Longrightarrow> \<not>Q y"
    shows "SELECTp P \<le> \<Down>Id (SELECTp Q)"
    using selectp_refine[where R=Id, of P Q] assms by auto
    
  lemma selectp_pw[refine_pw_simps]:
    "nofail (SELECTp P)"  
    "inres (SELECTp P) r \<longleftrightarrow> (r=None \<longrightarrow> (\<forall>x. \<not>P x)) \<and> (\<forall>x. r=Some x \<longrightarrow> P x)"
    unfolding SELECTp_def
    by auto

  lemma selectp_pw_simps[simp]:
    "nofail (SELECTp P)"
    "inres (SELECTp P) None \<longleftrightarrow> (\<forall>x. \<not>P x)"
    "inres (SELECTp P) (Some x) \<longleftrightarrow> P x"
    by (auto simp: refine_pw_simps)

  context Refine_Monadic_Syntax begin 
    notation SELECTp (binder "selectp " 10)

    term "selectp x. P x"
  end


definition setsum_impl :: "('a \<Rightarrow> 'b::comm_monoid_add nres) \<Rightarrow> 'a set \<Rightarrow> 'b nres" where
  "setsum_impl g S \<equiv> foreach S (\<lambda>x a. do { b \<leftarrow> g x; return (a+b)}) 0"

lemma setsum_imp_correct: 
  assumes [simp]: "finite S"
  assumes [THEN order_trans, refine_vcg]: "\<And>x. x\<in>S \<Longrightarrow> gi x \<le> (spec r. r=g x)"
  shows "setsum_impl gi S \<le> (spec r. r=setsum g S)"
  unfolding setsum_impl_def
  apply (refine_vcg FOREACH_rule[where I="\<lambda>it a. a = setsum g (S - it)"])
  apply (auto simp: it_step_insert_iff algebra_simps)
  done



    (* TODO: Move *)



    (* TODO: Move. Should this replace hn_refine_cons? *)
      
    



  (* TODO: This messes up code generation with some odd error msg! Why?  
  (* TODO: Move to imperative-HOL. Or at least to imp-hol-add *)
  context begin
    setup_lifting type_definition_integer 
  
    lift_definition integer_encode :: "integer \<Rightarrow> nat" is int_encode .
  
    lemma integer_encode_eq: "integer_encode x = integer_encode y \<longleftrightarrow> x = y"
      apply transfer
      by (rule inj_int_encode [THEN inj_eq])

    lifting_update integer.lifting
    lifting_forget integer.lifting
  end  

  instance integer :: countable
    by (rule countable_classI [of integer_encode]) (simp add: integer_encode_eq)

  instance integer :: heap ..
  *)

  lemma int_of_integer_less_iff: "int_of_integer x < int_of_integer y \<longleftrightarrow> x<y"
    by (simp add: less_integer_def)

  lemma nat_of_integer_less_iff: "x\<ge>0 \<Longrightarrow> y\<ge>0 \<Longrightarrow> nat_of_integer x < nat_of_integer y \<longleftrightarrow> x<y"
    unfolding nat_of_integer.rep_eq
    by (auto simp: int_of_integer_less_iff nat_less_eq_zless int_of_integer_less_iff[of 0, simplified])
    
  (*(* TODO: Move *)
  lemma param_integer[param]:
    "(0, 0::integer) \<in> Id"
    "(1, 1::integer) \<in> Id"
    "(numeral n::integer,numeral n::integer) \<in> Id"
    "(op <, op <::integer \<Rightarrow> _) \<in> Id \<rightarrow> Id \<rightarrow> Id"
    "(op \<le>, op \<le>::integer \<Rightarrow> _) \<in> Id \<rightarrow> Id \<rightarrow> Id"
    "(op =, op =::integer \<Rightarrow> _) \<in> Id \<rightarrow> Id \<rightarrow> Id"
    "(op +::integer\<Rightarrow>_,op +)\<in>Id\<rightarrow>Id\<rightarrow>Id"
    "(op -::integer\<Rightarrow>_,op -)\<in>Id\<rightarrow>Id\<rightarrow>Id"
    "(op *::integer\<Rightarrow>_,op * )\<in>Id\<rightarrow>Id\<rightarrow>Id"
    "(op div::integer\<Rightarrow>_,op div)\<in>Id\<rightarrow>Id\<rightarrow>Id"
    "(op mod::integer\<Rightarrow>_,op mod)\<in>Id\<rightarrow>Id\<rightarrow>Id"
    by auto
  
  lemmas [sepref_import_param] = param_integer  
  
  lemmas [id_rules] = 
    itypeI[Pure.of 0 "TYPE (integer)"]
  *)  

end
