theory Refine_Add_Fofu
imports 
  Fofu_Impl_Base 
  Refine_Monadic_Syntax_Sugar
  "DRAT_Misc"
  "../../DFS_Framework/Misc/DFS_Framework_Refine_Aux"
begin

  hide_type (open) List_Seg.node    
    
  notation Heap_Monad.return ("return")

  (* TODO: Move to Refine_Basic convenience *)  

  lemma strengthen_SPEC': "m \<le> SPEC \<Phi> \<Longrightarrow> m \<le> SPEC(\<lambda>s. inres m s \<and> nofail m \<and> \<Phi> s)"
    -- "Strengthen SPEC by adding trivial upper bound for result"
    by (auto simp: pw_le_iff refine_pw_simps)

lemma (in -) refine2spec_aux:
  "a \<le> \<Down>R b \<longleftrightarrow> ( (nofail b \<longrightarrow> a \<le> SPEC ( \<lambda>r. (\<exists>x. inres b x \<and> (r,x)\<in>R) )) )"
  by (auto simp: pw_le_iff refine_pw_simps)
  
lemma (in -) refine2specI:
  assumes "nofail b \<Longrightarrow> a \<le> SPEC (\<lambda>r. (\<exists>x. inres b x \<and> (r,x)\<in>R) )"
  shows "a \<le> \<Down>R b"  
  using assms by (simp add: refine2spec_aux)  
  
(* TODO: Move *)  
lemma specify_left:
  assumes "m \<le> SPEC \<Phi>"
  assumes "\<And>x. \<Phi> x \<Longrightarrow> f x \<le> M"  
  shows "do { x \<leftarrow> m; f x } \<le> M"
  using assms by (auto simp: pw_le_iff refine_pw_simps)  


(* Refinement Framework VCG control:
  Idea: Put a frame around stuff in the program where the VCG shall not look into
    on outermost pass, and discharge the frame's content with nested vcg call.
    Very useful with subgoal command, to set up some auxiliary context before
    discharging, e.g., interpret locales, etc.
 
*)  
(* TODO: Make this a generic technique:
  Problems: 
    * Splitter will split inside VCG_FRAME (e.g., ifs)

*)  
  
definition VCG_FRAME :: "_ nres \<Rightarrow> _ nres" where "VCG_FRAME m \<equiv> m"
lemma VCG_FRAME_cong[cong]: "VCG_FRAME x \<equiv> VCG_FRAME x" by simp

lemma vcg_intro_frame: "m \<equiv> VCG_FRAME m" unfolding VCG_FRAME_def by simp
lemma vcg_rem_frame: "m\<le>m' \<Longrightarrow> VCG_FRAME m \<le> m'" unfolding VCG_FRAME_def by simp
  
  
  
      
      

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
  shows "setsum_impl gi S \<le> (spec r. r=sum g S)"
  unfolding setsum_impl_def
  apply (refine_vcg FOREACH_rule[where I="\<lambda>it a. a = sum g (S - it)"])
  apply (auto simp: it_step_insert_iff algebra_simps)
  done


  lemma int_of_integer_less_iff: "int_of_integer x < int_of_integer y \<longleftrightarrow> x<y"
    by (simp add: less_integer_def)

  lemma nat_of_integer_less_iff: "x\<ge>0 \<Longrightarrow> y\<ge>0 \<Longrightarrow> nat_of_integer x < nat_of_integer y \<longleftrightarrow> x<y"
    unfolding nat_of_integer.rep_eq
    by (auto simp: int_of_integer_less_iff nat_less_eq_zless int_of_integer_less_iff[of 0, simplified])
    
      
(* TODO: Move *)  
  
lemma uminus_hnr[sepref_import_param]: "(uminus,uminus)\<in>int_rel \<rightarrow> int_rel" by auto  
  
  (* TODO: Move *)  
  lemma (in -) rev_append_hnr[param,sepref_import_param]:
    "(rev_append, rev_append) \<in> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel"
    unfolding rev_append_def by parametricity
    
      
(* TODO: Move. Allow monadic_nfoldli to be used in abstract programs *)      
(* Refinement Setup for nfoldli  *)
lemma monadic_nfoldli_arities[sepref_monadify_arity]:
  "monadic_nfoldli \<equiv> \<lambda>\<^sub>2s c f \<sigma>. SP (monadic_nfoldli)$s$(\<lambda>\<^sub>2x. c$x)$(\<lambda>\<^sub>2x \<sigma>. f$x$\<sigma>)$\<sigma>"
  by (simp_all)

lemma monadic_nfoldli_comb[sepref_monadify_comb]:
  "\<And>s c f \<sigma>. (monadic_nfoldli)$s$c$f$\<sigma> \<equiv> 
    Refine_Basic.bind$(EVAL$s)$(\<lambda>\<^sub>2s. Refine_Basic.bind$(EVAL$\<sigma>)$(\<lambda>\<^sub>2\<sigma>. 
      SP (monadic_nfoldli)$s$c$f$\<sigma>
    ))"
  by (simp_all)
      

(* TODO: Move *)    
lemma triv_exI[simp, intro!]: "Q x \<Longrightarrow>\<^sub>A \<exists>\<^sub>Ax. Q x"
  by sep_auto
    
    
(* TODO: Move. Add rule for imp_for! *)    
lemma imp_for'_rule:
  assumes LESS: "l\<le>u"
  assumes PRE: "P \<Longrightarrow>\<^sub>A I l s"
  assumes STEP: "\<And>i s. \<lbrakk> l\<le>i; i<u \<rbrakk> \<Longrightarrow> <I i s> f i s <I (i+1)>"
  shows "<P> imp_for' l u f s <I u>"
  apply (rule Hoare_Triple.cons_pre_rule[OF PRE])  
  using LESS 
proof (induction arbitrary: s rule: inc_induct)  
  case base thus ?case by sep_auto  
next
  case (step k)
  show ?case using step.hyps 
    by (sep_auto heap: STEP step.IH)  
qed 
    
    
lemma monadic_WHILEIT_refine[refine]:  
  assumes [refine]: "(s',s) \<in> R"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s \<rbrakk> \<Longrightarrow> I' s'"  
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s' \<rbrakk> \<Longrightarrow> b' s' \<le>\<Down>bool_rel (b s)"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s'; nofail (b s); inres (b s) True \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (f s)"
  shows "monadic_WHILEIT I' b' f' s' \<le>\<Down>R (monadic_WHILEIT I b f s)"
  unfolding monadic_WHILEIT_def
  by (refine_rcg bind_refine'; assumption?; auto)
  
lemma monadic_WHILEIT_refine_WHILEIT[refine]:  
  assumes [refine]: "(s',s) \<in> R"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s \<rbrakk> \<Longrightarrow> I' s'"  
  assumes [THEN order_trans,refine_vcg]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s' \<rbrakk> \<Longrightarrow> b' s' \<le> SPEC (\<lambda>r. r = b s)"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s'; b s \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (f s)"
  shows "monadic_WHILEIT I' b' f' s' \<le>\<Down>R (WHILEIT I b f s)"
  unfolding WHILEIT_to_monadic
  by (refine_vcg; assumption?; auto)
  
lemma monadic_WHILEIT_refine_WHILET[refine]:  
  assumes [refine]: "(s',s) \<in> R"
  assumes [THEN order_trans,refine_vcg]: "\<And>s' s. \<lbrakk> (s',s)\<in>R \<rbrakk> \<Longrightarrow> b' s' \<le> SPEC (\<lambda>r. r = b s)"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; b s \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (f s)"
  shows "monadic_WHILEIT (\<lambda>_. True) b' f' s' \<le>\<Down>R (WHILET b f s)"
  unfolding WHILET_def
  by (refine_vcg; assumption?)  

lemma monadic_WHILEIT_pat[def_pat_rules]:
  "monadic_WHILEIT$I \<equiv> UNPROTECT (monadic_WHILEIT I)"
  by auto  
    
lemma id_monadic_WHILEIT[id_rules]: 
  "PR_CONST (monadic_WHILEIT I) ::\<^sub>i TYPE(('a \<Rightarrow> bool nres) \<Rightarrow> ('a \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> 'a nres)"
  by simp
    
lemma monadic_WHILEIT_arities[sepref_monadify_arity]:
  "PR_CONST (monadic_WHILEIT I) \<equiv> \<lambda>\<^sub>2b f s. SP (PR_CONST (monadic_WHILEIT I))$(\<lambda>\<^sub>2s. b$s)$(\<lambda>\<^sub>2s. f$s)$s"
  by (simp)

lemma monadic_WHILEIT_comb[sepref_monadify_comb]:
  "PR_CONST (monadic_WHILEIT I)$b$f$s \<equiv> 
    Refine_Basic.bind$(EVAL$s)$(\<lambda>\<^sub>2s. 
      SP (PR_CONST (monadic_WHILEIT I))$b$f$s
    )"
  by (simp)

lemma nfoldli_filter_deforestation: 
  "nfoldli (filter P xs) c f s = nfoldli xs c (\<lambda>x s. if P x then f x s else return s) s"
  apply (induction xs arbitrary: s)
  by (auto simp: pw_eq_iff refine_pw_simps) 
    
lemma extend_list_of_filtered_set:
  assumes [simp, intro!]: "finite S" 
    and A: "distinct xs'" "set xs' = {x \<in> S. P x}"
  obtains xs where "xs' = filter P xs" "distinct xs" "set xs = S"
proof -
  obtain xs2 where "{x\<in>S. \<not>P x} = set xs2" "distinct xs2"
    using finite_distinct_list[where A="{x\<in>S. \<not>P x}"] by auto
  with A have "xs' = filter P (xs'@xs2)" "distinct (xs'@xs2)" "set (xs'@xs2) = S"  
    by (auto simp: filter_empty_conv)
  from that[OF this] show ?thesis .
qed    

    
lemma FOREACHc_filter_deforestation:
  assumes FIN[simp, intro!]: "finite S"
  shows "(FOREACHc {x\<in>S. P x} c f s) 
    = FOREACHc S c (\<lambda>x s. if P x then f x s else RETURN s) s"
  unfolding FOREACHc_def FOREACHci_def FOREACHoci_by_LIST_FOREACH LIST_FOREACH'_eq
      LIST_FOREACH'_def it_to_sorted_list_def
  subgoal       
  proof (induction rule: antisym[consumes 0, case_names 1 2])
    case 1
    then show ?case
      apply (rule le_ASSERTI)  
      apply (rule ASSERT_leI, simp)  
      apply (rule intro_spec_refine[where R=Id, simplified]; clarsimp)
      apply (rule extend_list_of_filtered_set[OF FIN _ sym], assumption, assumption)
      subgoal for xs' xs
        apply (rule rhs_step_bind_SPEC[where R=Id and x'="xs", simplified])
        applyS simp  
        applyS (simp add: nfoldli_filter_deforestation)
        done
      done
  next
    case 2
    then show ?case
    apply (rule le_ASSERTI)  
    apply (rule ASSERT_leI, (simp; fail))  
    apply (rule intro_spec_refine[where R=Id, simplified]; clarsimp)
    subgoal for xs  
      apply (rule rhs_step_bind_SPEC[where R=Id and x'="filter P xs", simplified])
      apply simp  
      apply (simp add: nfoldli_filter_deforestation)
      done
    done  
  qed
  done    

lemma FOREACHc_filter_deforestation2:
  assumes [simp]: "distinct xs"
  shows "(FOREACHc (set (filter P xs)) c f s) 
    = FOREACHc (set xs) c (\<lambda>x s. if P x then f x s else RETURN s) s"
  using FOREACHc_filter_deforestation[of "set xs", simplified, folded set_filter]
  .  

(* TODO: Move *)
lemma list_case_refine[refine]: 
  assumes "(li,l)\<in>\<langle>S\<rangle>list_rel"
  assumes "fni \<le>\<Down>R fn"  
  assumes "\<And>xi x xsi xs. \<lbrakk> (xi,x)\<in>S; (xsi,xs)\<in>\<langle>S\<rangle>list_rel; li=xi#xsi; l=x#xs \<rbrakk> \<Longrightarrow> fci xi xsi \<le>\<Down>R (fc x xs)"  
  shows "(case li of [] \<Rightarrow> fni | xi#xsi \<Rightarrow> fci xi xsi) \<le> \<Down>R (case l of [] \<Rightarrow> fn | x#xs \<Rightarrow> fc x xs)"  
  using assms by (auto split: list.split)  
    
lemma list_rel_congD: 
  assumes A: "(li,l)\<in>\<langle>S\<rangle>list_rel" 
  shows "(li,l)\<in>\<langle>S\<inter>(set li\<times>set l)\<rangle>list_rel"
proof -
  {
    fix Si0 S0
    assume "set li \<subseteq> Si0" "set l \<subseteq> S0"
    with A have "(li,l)\<in>\<langle>S\<inter>(Si0\<times>S0)\<rangle>list_rel"
      by (induction rule: list_rel_induct) auto  
  } from this[OF order_refl order_refl] show ?thesis .
qed      
    
lemma monadic_nfoldli_refine[refine]:
  assumes L: "(li, l) \<in> \<langle>S\<rangle>list_rel"
    and  [simp]: "(si, s) \<in> R"
    and CR[refine]: "\<And>si s. (si,s)\<in>R \<Longrightarrow> ci si \<le>\<Down>bool_rel (c s)"
    and [refine]: "\<And>xi x si s. \<lbrakk> (xi,x)\<in>S; x\<in>set l; (si,s)\<in>R; inres (c s) True \<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
  shows "monadic_nfoldli li ci fi si \<le> \<Down> R (monadic_nfoldli l c f s)"
    
  supply RELATESI[of "S\<inter>(set li\<times>set l)", refine_dref_RELATES]
  supply RELATESI[of R, refine_dref_RELATES]
  unfolding monadic_nfoldli_def  
  apply (refine_rcg bind_refine')
  apply refine_dref_type  
  apply (vc_solve simp: list_rel_congD[OF L]) 
  done
  
  
  
  
  
  
  
  
  
  
(************ Patch to make amtx_new more efficient, by avoiding div and mod. 
  TODO: Integrate/replace in IICF_Array_Matrix.thy ! *)    
    
definition "mtx_tabulate N M c \<equiv> do {
  m \<leftarrow> Array.new (N*M) 0;
  (_,_,m) \<leftarrow> imp_for' 0 (N*M) (\<lambda>k (i,j,m). do {
    Array.upd k (c (i,j)) m;
    let j=j+1;
    if j<M then return (i,j,m)
    else return (i+1,0,m)
  }) (0,0,m);
  return m
}"
    

lemma mtx_idx_unique_conv[simp]: 
  fixes M :: nat
  assumes "j<M" "j'<M"
  shows "(i * M + j = i' * M + j') \<longleftrightarrow> (i=i' \<and> j=j')"
  using assms  
  apply auto  
  subgoal
    by (metis div_if msrevs(1) nat_add_left_cancel not_gr0 not_less0)  
  subgoal
    using \<open>\<lbrakk>j < M; j' < M; i * M + j = i' * M + j'\<rbrakk> \<Longrightarrow> i = i'\<close> by auto  
  done
    
lemma mtx_tabulate_rule[sep_heap_rules]:
  assumes NONZ: "mtx_nonzero c \<subseteq> {0..<N}\<times>{0..<M}"
  shows "<emp> mtx_tabulate N M c <IICF_Array_Matrix.is_amtx N M c>"
proof (cases "M=0")
  case True thus ?thesis
    unfolding mtx_tabulate_def  
    using mtx_nonzeroD[OF _ NONZ]  
    by (sep_auto simp: is_amtx_def)
next
  case False hence M_POS: "0<M" by auto
  show ?thesis
    unfolding mtx_tabulate_def  
    apply (sep_auto 
      decon: 
        imp_for'_rule[where 
          I="\<lambda>k (i,j,mi). \<exists>\<^sub>Am. mi \<mapsto>\<^sub>a m 
          * \<up>( k=i*M+j \<and> j<M \<and> k\<le>N*M \<and> length m = N*M )
          * \<up>( \<forall>i'<i. \<forall>j<M. m!(i'*M+j) = c (i',j) )
          * \<up>( \<forall>j'<j. m!(i*M+j') = c (i,j') )
        "]
      simp: nth_list_update M_POS dest: Suc_lessI
    )
    unfolding is_amtx_def
    using mtx_nonzeroD[OF _ NONZ] 
    apply sep_auto  
    by (metis add.right_neutral M_POS mtx_idx_unique_conv)  
qed

lemma mtx_tabulate_aref: 
  "(mtx_tabulate N M, RETURN o op_mtx_new) 
    \<in> [\<lambda>c. mtx_nonzero c \<subseteq> {0..<N}\<times>{0..<M}]\<^sub>a id_assn\<^sup>k \<rightarrow> IICF_Array_Matrix.is_amtx N M"  
  by sepref_to_hoare sep_auto
  
sepref_decl_impl (no_register) amtx_new_by_tab: mtx_tabulate_aref uses op_mtx_new_fref'
  by (auto simp: mtx_nonzero_zu_eq)
    
declare amtx_new_hnr'[sepref_fr_rules del]    

lemma amtx_new_hnr_by_tab'[sepref_fr_rules]: 
  fixes A :: "'a::zero \<Rightarrow> 'b::{zero,heap} \<Rightarrow> assn"
  shows "CONSTRAINT (IS_PURE PRES_ZERO_UNIQUE) A \<Longrightarrow>
  (mtx_tabulate N M, (RETURN \<circ> PR_CONST (op_amtx_new N M)))
  \<in> [\<lambda>x. mtx_nonzero x \<subseteq> {0..<N} \<times> {0..<M}]\<^sub>a (pure (nat_rel \<times>\<^sub>r nat_rel \<rightarrow> the_pure A))\<^sup>k \<rightarrow> amtx_assn N M A"
  using amtx_new_by_tab_hnr[of A N M] by simp
    
end
