(*  Title:      HOL/MicroJava/BV/LBVComplete.thy
    ID:         $Id: LBVComplete.thy,v 1.1 2005-05-31 23:21:04 lsf37 Exp $
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

header {* \isaheader{Completeness of the LBV} *}

theory LBVComplete = LBVSpec + Typing_Framework:

constdefs
  is_target :: "['s step_type, 's list, nat] \<Rightarrow> bool" 
  "is_target step \<tau>s pc' \<equiv>
     \<exists>pc s'. pc' \<noteq> pc+1 \<and> pc < size \<tau>s \<and> (pc',s') \<in> set (step pc (\<tau>s!pc))"

  make_cert :: "['s step_type, 's list, 's] \<Rightarrow> 's certificate"
  "make_cert step \<tau>s B \<equiv> 
     map (\<lambda>pc. if is_target step \<tau>s pc then \<tau>s!pc else B) [0..<size \<tau>s] @ [B]"

text {*
  For the code generator:
*}
constdefs
  list_ex :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  "list_ex P xs \<equiv> \<exists>x \<in> set xs. P x"

lemma [code]: "list_ex P [] = False" by (simp add: list_ex_def)
lemma [code]: "list_ex P (x#xs) = (P x \<or> list_ex P xs)" by (simp add: list_ex_def)

lemma [code]:
  "is_target step \<tau>s pc' =
  list_ex (\<lambda>pc. pc' \<noteq> pc+1 \<and> pc' mem (map fst (step pc (\<tau>s!pc)))) [0..<size \<tau>s]"
(*<*)
  apply (simp add: list_ex_def is_target_def set_mem_eq)
  apply force
  done
(*>*)

locale (open) lbvc = lbv + 
  fixes \<tau>s :: "'a list" 
  fixes c :: "'a list" 
  defines cert_def: "c \<equiv> make_cert step \<tau>s \<bottom>"

  assumes mono: "mono r step (size \<tau>s) A"
  assumes pres: "pres_type step (size \<tau>s) A" 
  assumes \<tau>s:  "\<forall>pc < size \<tau>s. \<tau>s!pc \<in> A \<and> \<tau>s!pc \<noteq> \<top>"
  assumes bounded: "bounded step (size \<tau>s)"

  assumes B_neq_T: "\<bottom> \<noteq> \<top>" 


lemma (in lbvc) cert: "cert_ok c (size \<tau>s) \<top> \<bottom> A"
(*<*)
proof (unfold cert_ok_def, intro strip conjI)  
  note [simp] = make_cert_def cert_def nth_append 

  show "c!size \<tau>s = \<bottom>" by simp

  fix pc assume pc: "pc < size \<tau>s" 
  from pc \<tau>s B_A show "c!pc \<in> A" by simp
  from pc \<tau>s B_neq_T show "c!pc \<noteq> \<top>" by simp
qed
(*>*)

lemmas [simp del] = split_paired_Ex

lemma (in lbvc) cert_target [intro?]:
  "\<lbrakk> (pc',s') \<in> set (step pc (\<tau>s!pc));
      pc' \<noteq> pc+1; pc < size \<tau>s; pc' < size \<tau>s \<rbrakk>
  \<Longrightarrow> c!pc' = \<tau>s!pc'"
(*<*) by (auto simp add: cert_def make_cert_def nth_append is_target_def) (*>*)

lemma (in lbvc) cert_approx [intro?]:
  "\<lbrakk> pc < size \<tau>s; c!pc \<noteq> \<bottom> \<rbrakk> \<Longrightarrow> c!pc = \<tau>s!pc"
(*<*) by (auto simp add: cert_def make_cert_def nth_append) (*>*)

lemma (in lbv) le_top [simp, intro]: "x <=_r \<top>"
(*<*) by (insert top) simp (*>*)
  
lemma (in lbv) merge_mono:
  assumes less:  "set ss\<^isub>2 {\<sqsubseteq>\<^bsub>r\<^esub>} set ss\<^isub>1"
  assumes x:     "x \<in> A"
  assumes ss\<^isub>1:   "snd`set ss\<^isub>1 \<subseteq> A"
  assumes ss\<^isub>2:   "snd`set ss\<^isub>2 \<subseteq> A"
  shows "merge c pc ss\<^isub>2 x \<sqsubseteq>\<^sub>r merge c pc ss\<^isub>1 x" (is "?s\<^isub>2 \<sqsubseteq>\<^sub>r ?s\<^isub>1")
(*<*)
proof-
  have "?s\<^isub>1 = \<top> \<Longrightarrow> ?thesis" by simp
  moreover {
    assume merge: "?s\<^isub>1 \<noteq> T" 
    from x ss\<^isub>1 have "?s\<^isub>1 =
      (if \<forall>(pc',s')\<in>set ss\<^isub>1. pc' \<noteq> pc + 1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc'
      then (map snd [(p', t')\<in>ss\<^isub>1 . p'=pc+1]) \<Squnion>\<^bsub>f\<^esub> x
      else \<top>)" by (rule merge_def)  
    with merge obtain
      app: "\<forall>(pc',s')\<in>set ss\<^isub>1. pc' \<noteq> pc+1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc'" 
           (is "?app ss\<^isub>1") and
      sum: "(map snd [(p',t')\<in>ss\<^isub>1 . p' = pc+1] \<Squnion>\<^bsub>f\<^esub> x) = ?s\<^isub>1" 
           (is "?map ss\<^isub>1 \<Squnion>\<^bsub>f\<^esub> x = _" is "?sum ss\<^isub>1 = _")
      by (simp split: split_if_asm)
    from app less have "?app ss\<^isub>2" by (blast dest: trans_r lesub_step_typeD)
    moreover {
      from ss\<^isub>1 have map1: "set (?map ss\<^isub>1) \<subseteq> A" by auto
      with x have "?sum ss\<^isub>1 \<in> A" by (auto intro!: plusplus_closed)
      with sum have "?s\<^isub>1 \<in> A" by simp
      moreover    
      have mapD: "\<And>x ss. x \<in> set (?map ss) \<Longrightarrow> \<exists>p. (p,x) \<in> set ss \<and> p=pc+1" by auto
      from x map1 have "\<forall>x \<in> set (?map ss\<^isub>1). x \<sqsubseteq>\<^sub>r ?sum ss\<^isub>1" by clarify (rule pp_ub1)
      with sum have "\<forall>x \<in> set (?map ss\<^isub>1). x \<sqsubseteq>\<^sub>r ?s\<^isub>1" by simp
      with less have "\<forall>x \<in> set (?map ss\<^isub>2). x \<sqsubseteq>\<^sub>r ?s\<^isub>1"
        by (fastsimp dest!: mapD lesub_step_typeD intro: trans_r)
      moreover from map1 x have "x \<sqsubseteq>\<^sub>r (?sum ss\<^isub>1)" by (rule pp_ub2)
      with sum have "x \<sqsubseteq>\<^sub>r ?s\<^isub>1" by simp
      moreover from ss\<^isub>2 have "set (?map ss\<^isub>2) \<subseteq> A" by auto
      ultimately  have "?sum ss\<^isub>2 \<sqsubseteq>\<^sub>r ?s\<^isub>1" using x by - (rule pp_lub)
    }
    moreover from x ss\<^isub>2 have "?s\<^isub>2 =
      (if \<forall>(pc', s')\<in>set ss\<^isub>2. pc' \<noteq> pc + 1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc'
      then map snd [(p', t')\<in>ss\<^isub>2 . p' = pc + 1] \<Squnion>\<^bsub>f\<^esub> x
      else \<top>)" by (rule merge_def)
    ultimately have ?thesis by simp
  }
  ultimately show ?thesis by (cases "?s\<^isub>1 = \<top>") auto
qed
(*>*)

lemma (in lbvc) wti_mono:
  assumes less: "s\<^isub>2 \<sqsubseteq>\<^sub>r s\<^isub>1"
  assumes pc: "pc < size \<tau>s" and s\<^isub>1: "s\<^isub>1 \<in> A" and s\<^isub>2: "s\<^isub>2 \<in> A"
  shows "wti c pc s\<^isub>2 \<sqsubseteq>\<^sub>r wti c pc s\<^isub>1" (is "?s\<^isub>2' \<sqsubseteq>\<^sub>r ?s\<^isub>1'")
(*<*)
proof -
  from mono s\<^isub>2 have "set (step pc s\<^isub>2) {\<sqsubseteq>\<^bsub>r\<^esub>} set (step pc s\<^isub>1)" by - (rule monoD)
  moreover from pc cert have "c!Suc pc \<in> A" by - (rule cert_okD3)
  moreover from pres s\<^isub>1 pc have "snd`set (step pc s\<^isub>1) \<subseteq> A" by (rule pres_typeD2)
  moreover from pres s\<^isub>2 pc have "snd`set (step pc s\<^isub>2) \<subseteq> A" by (rule pres_typeD2)
  ultimately show ?thesis by (simp add: wti merge_mono)
qed 
(*>*)

lemma (in lbvc) wtc_mono:
  assumes less: "s\<^isub>2 \<sqsubseteq>\<^sub>r s\<^isub>1"
  assumes pc: "pc < size \<tau>s" and s\<^isub>1: "s\<^isub>1 \<in> A" and s\<^isub>2: "s\<^isub>2 \<in> A"
  shows "wtc c pc s\<^isub>2 \<sqsubseteq>\<^sub>r wtc c pc s\<^isub>1" (is "?s\<^isub>2' \<sqsubseteq>\<^sub>r ?s\<^isub>1'")
(*<*)
proof (cases "c!pc = \<bottom>")
  case True 
  moreover have "wti c pc s\<^isub>2 \<sqsubseteq>\<^sub>r wti c pc s\<^isub>1" by (rule wti_mono)
  ultimately show ?thesis by (simp add: wtc)
next
  case False
  have "?s\<^isub>1' = \<top> \<Longrightarrow> ?thesis" by simp
  moreover {
    assume "?s\<^isub>1' \<noteq> \<top>" 
    with False have c: "s\<^isub>1 \<sqsubseteq>\<^sub>r c!pc" by (simp add: wtc split: split_if_asm)
    with less have "s\<^isub>2 \<sqsubseteq>\<^sub>r c!pc" ..
    with False c have ?thesis by (simp add: wtc)
  }
  ultimately show ?thesis by (cases "?s\<^isub>1' = \<top>") auto
qed
(*>*)

lemma (in lbv) top_le_conv [simp]: "\<top> \<sqsubseteq>\<^sub>r x = (x = \<top>)"
(*<*) by (insert semilat) (simp add: top top_le_conv)  (*>*)

lemma (in lbv) neq_top [simp, elim]: "\<lbrakk> x \<sqsubseteq>\<^sub>r y; y \<noteq> \<top> \<rbrakk> \<Longrightarrow> x \<noteq> \<top>"
(*<*) by (cases "x = T") auto (*>*)

lemma (in lbvc) stable_wti:
  assumes stable:  "stable r step \<tau>s pc" and pc: "pc < size \<tau>s"
  shows "wti c pc (\<tau>s!pc) \<noteq> \<top>"
(*<*)
proof -
  let ?step = "step pc (\<tau>s!pc)"
  from stable 
  have less: "\<forall>(q,s')\<in>set ?step. s' \<sqsubseteq>\<^sub>r \<tau>s!q" by (simp add: stable_def)
  
  from cert pc have cert_suc: "c!Suc pc \<in> A" by - (rule cert_okD3)
  moreover from \<tau>s pc have "\<tau>s!pc \<in> A" by simp
  with pres pc have stepA: "snd`set ?step \<subseteq> A" by - (rule pres_typeD2)
  ultimately
  have "merge c pc ?step (c!Suc pc) =
    (if \<forall>(pc',s')\<in>set ?step. pc'\<noteq>pc+1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc'
    then map snd [(p',t')\<in>?step.p'=pc+1] \<Squnion>\<^bsub>f\<^esub> c!Suc pc
    else \<top>)" by (rule merge_def)
  moreover {
    fix pc' s' assume s': "(pc',s') \<in> set ?step" and suc_pc: "pc' \<noteq> pc+1"
    with less have "s' \<sqsubseteq>\<^sub>r \<tau>s!pc'" by auto
    also from bounded pc s' have "pc' < size \<tau>s" by (rule boundedD)
    with s' suc_pc pc have "c!pc' = \<tau>s!pc'" ..
    hence "\<tau>s!pc' = c!pc'" ..
    finally have "s' \<sqsubseteq>\<^sub>r c!pc'" .
  } hence "\<forall>(pc',s')\<in>set ?step. pc'\<noteq>pc+1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc'" by auto
  moreover from pc have "Suc pc = size \<tau>s \<or> Suc pc < size \<tau>s" by auto
  hence "map snd [(p',t')\<in>?step.p'=pc+1] \<Squnion>\<^bsub>f\<^esub> c!Suc pc \<noteq> \<top>" (is "?map \<Squnion>\<^bsub>f\<^esub> _ \<noteq> _")
  proof (rule disjE)
    assume pc': "Suc pc = size \<tau>s"
    with cert have "c!Suc pc = \<bottom>" by (simp add: cert_okD2)
    moreover 
    from pc' bounded pc 
    have "\<forall>(p',t')\<in>set ?step. p'\<noteq>pc+1" by clarify (drule boundedD, auto)
    hence "[(p',t')\<in>?step. p'=pc+1] = []" by (blast intro: filter_False)
    hence "?map = []" by simp
    ultimately show ?thesis by (simp add: B_neq_T)
  next
    assume pc': "Suc pc < size \<tau>s"
    from pc' \<tau>s have "\<tau>s!Suc pc \<in> A" by simp
    moreover note cert_suc
    moreover from stepA have "set ?map \<subseteq> A" by auto
    moreover have "\<And>s. s \<in> set ?map \<Longrightarrow> \<exists>t. (Suc pc, t) \<in> set ?step" by auto
    with less have "\<forall>s' \<in> set ?map. s' \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by auto
    moreover from pc' have "c!Suc pc \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" 
      by (cases "c!Suc pc = \<bottom>") (auto dest: cert_approx)
    ultimately have "?map \<Squnion>\<^bsub>f\<^esub> c!Suc pc \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by (rule pp_lub)
    moreover from pc' \<tau>s have "\<tau>s!Suc pc \<noteq> \<top>" by simp
    ultimately show ?thesis by auto
  qed
  ultimately have "merge c pc ?step (c!Suc pc) \<noteq> \<top>" by simp
  thus ?thesis by (simp add: wti)  
qed
(*>*)

lemma (in lbvc) wti_less:
  assumes stable: "stable r step \<tau>s pc" and suc_pc: "Suc pc < size \<tau>s"
  shows "wti c pc (\<tau>s!pc) \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" (is "?wti \<sqsubseteq>\<^sub>r _")
(*<*)
proof -
  let ?step = "step pc (\<tau>s!pc)"

  from stable
  have less: "\<forall>(q,s')\<in>set ?step. s' \<sqsubseteq>\<^sub>r \<tau>s!q" by (simp add: stable_def)
   
  from suc_pc have pc: "pc < size \<tau>s" by simp
  with cert have cert_suc: "c!Suc pc \<in> A" by - (rule cert_okD3)
  moreover from \<tau>s pc have "\<tau>s!pc \<in> A" by simp
  with pres pc have stepA: "snd`set ?step \<subseteq> A" by - (rule pres_typeD2)
  moreover from stable pc have "?wti \<noteq> \<top>" by (rule stable_wti)
  hence "merge c pc ?step (c!Suc pc) \<noteq> \<top>" by (simp add: wti)
  ultimately
  have "merge c pc ?step (c!Suc pc) =
    map snd [(p',t')\<in>?step.p'=pc+1] \<Squnion>\<^bsub>f\<^esub> c!Suc pc" by (rule merge_not_top_s) 
  hence "?wti = \<dots>" (is "_ = (?map \<Squnion>\<^bsub>f\<^esub> _)" is "_ = ?sum") by (simp add: wti)
  also {
    from suc_pc \<tau>s have "\<tau>s!Suc pc \<in> A" by simp
    moreover note cert_suc
    moreover from stepA have "set ?map \<subseteq> A" by auto
    moreover have "\<And>s. s \<in> set ?map \<Longrightarrow> \<exists>t. (Suc pc, t) \<in> set ?step" by auto
    with less have "\<forall>s' \<in> set ?map. s' \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by auto
    moreover from suc_pc have "c!Suc pc \<sqsubseteq>\<^sub>r \<tau>s!Suc pc"
      by (cases "c!Suc pc = \<bottom>") (auto dest: cert_approx)
    ultimately have "?sum \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by (rule pp_lub)
  }
  finally show ?thesis .
qed
(*>*)

lemma (in lbvc) stable_wtc:
  assumes stable: "stable r step \<tau>s pc" and pc: "pc < size \<tau>s"
  shows "wtc c pc (\<tau>s!pc) \<noteq> \<top>"
(*<*)
proof -
  have wti: "wti c pc (\<tau>s!pc) \<noteq> \<top>" by (rule stable_wti)   
  show ?thesis
  proof (cases "c!pc = \<bottom>")
    case True with wti show ?thesis by (simp add: wtc)
  next
    case False
    with pc have "c!pc = \<tau>s!pc" ..    
    with False wti show ?thesis by (simp add: wtc)
  qed
qed
(*>*)

lemma (in lbvc) wtc_less:
  assumes stable: "stable r step \<tau>s pc" and suc_pc: "Suc pc < size \<tau>s"
  shows "wtc c pc (\<tau>s!pc) \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" (is "?wtc \<sqsubseteq>\<^sub>r _")
(*<*)
proof (cases "c!pc = \<bottom>")
  case True
  moreover have "wti c pc (\<tau>s!pc) \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by (rule wti_less)
  ultimately show ?thesis by (simp add: wtc)
next
  case False
  from suc_pc have pc: "pc < size \<tau>s" by simp
  hence "?wtc \<noteq> \<top>" by - (rule stable_wtc)
  with False have "?wtc = wti c pc (c!pc)" 
    by (unfold wtc) (simp split: split_if_asm)
  also from pc False have "c!pc = \<tau>s!pc" .. 
  finally have "?wtc = wti c pc (\<tau>s!pc)" .
  also have "wti c pc (\<tau>s!pc) \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by (rule wti_less)
  finally show ?thesis .
qed
(*>*)

lemma (in lbvc) wt_step_wtl_lemma:
  assumes wt_step: "wt_step r \<top> step \<tau>s"
  shows "\<And>pc s. pc+size ls = size \<tau>s \<Longrightarrow> s \<sqsubseteq>\<^sub>r \<tau>s!pc \<Longrightarrow> s \<in> A \<Longrightarrow> s\<noteq>\<top> \<Longrightarrow>
                wtl ls c pc s \<noteq> \<top>"
  (is "\<And>pc s. _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?wtl ls pc s \<noteq> _")
(*<*)
proof (induct ls)
  fix pc s assume "s\<noteq>\<top>" thus "?wtl [] pc s \<noteq> \<top>" by simp
next
  fix pc s i ls
  assume "\<And>pc s. pc+size ls=size \<tau>s \<Longrightarrow> s \<sqsubseteq>\<^sub>r \<tau>s!pc \<Longrightarrow> s \<in> A \<Longrightarrow> s\<noteq>\<top> \<Longrightarrow> 
                  ?wtl ls pc s \<noteq> \<top>"
  moreover
  assume pc_l: "pc + size (i#ls) = size \<tau>s"
  hence suc_pc_l: "Suc pc + size ls = size \<tau>s" by simp
  ultimately
  have IH: "\<And>s. s \<sqsubseteq>\<^sub>r \<tau>s!Suc pc \<Longrightarrow> s \<in> A \<Longrightarrow> s \<noteq> \<top> \<Longrightarrow> ?wtl ls (Suc pc) s \<noteq> \<top>" .

  from pc_l obtain pc: "pc < size \<tau>s" by simp
  with wt_step have stable: "stable r step \<tau>s pc" by (simp add: wt_step_def)
  moreover assume s_\<tau>s: "s \<sqsubseteq>\<^sub>r \<tau>s!pc"
  ultimately have wt_\<tau>s: "wtc c pc (\<tau>s!pc) \<noteq> \<top>" by - (rule stable_wtc)

  from \<tau>s pc have \<tau>s_pc: "\<tau>s!pc \<in> A" by simp
  moreover assume s: "s \<in> A"
  ultimately 
  have wt_s_\<tau>s: "wtc c pc s \<sqsubseteq>\<^sub>r wtc c pc (\<tau>s!pc)" using s_\<tau>s by - (rule wtc_mono)
  with wt_\<tau>s have wt_s: "wtc c pc s \<noteq> \<top>" by simp
  moreover assume s: "s \<noteq> \<top>" 
  ultimately have "ls = [] \<Longrightarrow> ?wtl (i#ls) pc s \<noteq> \<top>" by simp
  moreover {
    assume "ls \<noteq> []" 
    with pc_l have suc_pc: "Suc pc < size \<tau>s" by (auto simp add: neq_Nil_conv)
    with stable have "wtc c pc (\<tau>s!pc) \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by (rule wtc_less)
    with wt_s_\<tau>s have "wtc c pc s \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by (rule trans_r)      
    moreover from cert suc_pc have "c!pc \<in> A" "c!(pc+1) \<in> A" 
      by (auto simp add: cert_ok_def)
    with pres have "wtc c pc s \<in> A" by (rule wtc_pres)
    ultimately have "?wtl ls (Suc pc) (wtc c pc s) \<noteq> \<top>" using IH wt_s by blast
    with s wt_s have "?wtl (i#ls) pc s \<noteq> \<top>" by simp 
  }
  ultimately show "?wtl (i#ls) pc s \<noteq> \<top>" by (cases ls) blast+
qed
(*>*)

theorem (in lbvc) wtl_complete:
  assumes "wt_step r \<top> step \<tau>s"
  assumes "s \<sqsubseteq>\<^sub>r \<tau>s!0" and "s \<in> A" and "s \<noteq> \<top>" and "size ins = size \<tau>s"
  shows "wtl ins c 0 s \<noteq> \<top>"
(*<*)
proof -  
  have "0+size ins = size \<tau>s" by simp
  thus ?thesis by - (rule wt_step_wtl_lemma)
qed
(*>*)

end
