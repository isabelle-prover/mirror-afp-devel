(*  Title:      HOL/MicroJava/BV/JVM.thy
    ID:         $Id: LBVJVM.thy,v 1.1 2008-04-23 08:43:28 alochbihler Exp $
    Author:     Tobias Nipkow, Gerwin Klein
    Copyright   2000 TUM
*)

header {* \isaheader{LBV for the JVM}\label{sec:JVM} *}

theory LBVJVM
imports "../DFA/Abstract_BV" TF_JVM
begin

types prog_cert = "cname \<Rightarrow> mname \<Rightarrow> ty\<^isub>i' err list"

constdefs
  check_cert :: "jvm_prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ty\<^isub>i' err list \<Rightarrow> bool"
  "check_cert P mxs mxl n cert \<equiv> check_types P mxs mxl cert \<and> size cert = n+1 \<and>
                                 (\<forall>i<n. cert!i \<noteq> Err) \<and> cert!n = OK None"

  lbvjvm :: "jvm_prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> ex_table \<Rightarrow> 
             ty\<^isub>i' err list \<Rightarrow> instr list \<Rightarrow> ty\<^isub>i' err \<Rightarrow> ty\<^isub>i' err"
  "lbvjvm P mxs maxr T\<^isub>r et cert bs \<equiv>
  wtl_inst_list bs cert (JVM_SemiType.sup P mxs maxr) (JVM_SemiType.le P mxs maxr) Err (OK None) (exec P mxs T\<^isub>r et bs) 0"

  wt_lbv :: "jvm_prog \<Rightarrow> cname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
             ex_table \<Rightarrow> ty\<^isub>i' err list \<Rightarrow> instr list \<Rightarrow> bool"
  "wt_lbv P C Ts T\<^isub>r mxs mxl\<^isub>0 et cert ins \<equiv>
   check_cert P mxs (1+size Ts+mxl\<^isub>0) (size ins) cert \<and>
   0 < size ins \<and> 
   (let start  = Some ([],(OK (Class C))#((map OK Ts))@(replicate mxl\<^isub>0 Err));
        result = lbvjvm P mxs (1+size Ts+mxl\<^isub>0) T\<^isub>r et cert ins (OK start)
    in result \<noteq> Err)"

  wt_jvm_prog_lbv :: "jvm_prog \<Rightarrow> prog_cert \<Rightarrow> bool"
  "wt_jvm_prog_lbv P cert \<equiv>
  wf_prog (\<lambda>P C (mn,Ts,T\<^isub>r,(mxs,mxl\<^isub>0,b,et)). wt_lbv P C Ts T\<^isub>r mxs mxl\<^isub>0 et (cert C mn) b) P"

  mk_cert :: "jvm_prog \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> ex_table \<Rightarrow> instr list 
              \<Rightarrow> ty\<^isub>m \<Rightarrow> ty\<^isub>i' err list"
  "mk_cert P mxs T\<^isub>r et bs phi \<equiv> make_cert (exec P mxs T\<^isub>r et bs) (map OK phi) (OK None)"

  prg_cert :: "jvm_prog \<Rightarrow> ty\<^isub>P \<Rightarrow> prog_cert"
  "prg_cert P phi C mn \<equiv> let (C,Ts,T\<^isub>r,(mxs,mxl\<^isub>0,ins,et)) = method P C mn
                         in  mk_cert P mxs T\<^isub>r et ins (phi C mn)"
   
lemma check_certD [intro?]:
  "check_cert P mxs mxl n cert \<Longrightarrow> cert_ok cert n Err (OK None) (states P mxs mxl)"
  by (unfold cert_ok_def check_cert_def check_types_def) auto


lemma (in start_context) wt_lbv_wt_step:
  assumes lbv: "wt_lbv P C Ts T\<^isub>r mxs mxl\<^isub>0 xt cert is"
  shows "\<exists>\<tau>s \<in> list (size is) A. wt_step r Err step \<tau>s \<and> OK first \<sqsubseteq>\<^sub>r \<tau>s!0"
(*<*)
proof -
  from wf have "semilat (JVM_SemiType.sl P mxs mxl)" ..
  hence "semilat (A, r, f)" by (simp add: sl_def2)
  moreover have "top r Err" by (simp add: JVM_le_Err_conv)
  moreover have "Err \<in> A" by (simp add: JVM_states_unfold)
  moreover have "bottom r (OK None)" 
    by (simp add: JVM_le_Err_conv bottom_def lesub_def Err.le_def split: err.split)
  moreover have "OK None \<in> A" by (simp add: JVM_states_unfold)
  moreover note bounded_step
  moreover from lbv have "cert_ok cert (size is) Err (OK None) A"
    by (unfold wt_lbv_def) (auto dest: check_certD)
  moreover note exec_pres_type
  moreover
  from lbv 
  have "wtl_inst_list is cert f r Err (OK None) step 0 (OK first) \<noteq> Err"
    by (simp add: wt_lbv_def lbvjvm_def step_def_exec [symmetric])    
  moreover note first_in_A
  moreover from lbv have "0 < size is" by (simp add: wt_lbv_def)
  ultimately show ?thesis by (rule lbvs.wtl_sound_strong)
qed
(*>*)


lemma (in start_context) wt_lbv_wt_method:
  assumes lbv: "wt_lbv P C Ts T\<^isub>r mxs mxl\<^isub>0 xt cert is"  
  shows "\<exists>\<tau>s. wt_method P C Ts T\<^isub>r mxs mxl\<^isub>0 is xt \<tau>s"
(*<*)
proof -
  from lbv have l: "is \<noteq> []" by (simp add: wt_lbv_def)
  moreover
  from wf lbv C Ts obtain \<tau>s where 
    list:  "\<tau>s \<in> list (size is) A" and
    step:  "wt_step r Err step \<tau>s" and    
    start: "OK first \<sqsubseteq>\<^sub>r \<tau>s!0" 
    by (blast dest: wt_lbv_wt_step)
  from list have [simp]: "size \<tau>s = size is" by simp
  have "size (map ok_val \<tau>s) = size is" by simp  
  moreover from l have 0: "0 < size \<tau>s" by simp
  with step obtain \<tau>s0 where "\<tau>s!0 = OK \<tau>s0"
    by (unfold wt_step_def) blast
  with start 0 have "wt_start P C Ts mxl\<^isub>0 (map ok_val \<tau>s)"
    by (simp add: wt_start_def JVM_le_Err_conv lesub_def Err.le_def)    
  moreover {
    from list have "check_types P mxs mxl \<tau>s" by (simp add: check_types_def)
    also from step  have "\<forall>x \<in> set \<tau>s. x \<noteq> Err" 
      by (auto simp add: all_set_conv_all_nth wt_step_def)    
    hence [symmetric]: "map OK (map ok_val \<tau>s) = \<tau>s"
      by (auto intro!: map_idI simp add: map_compose [symmetric])
    finally have "check_types P mxs mxl (map OK (map ok_val \<tau>s))" .
  }
  moreover {  
    note bounded_step
    moreover from list have "set \<tau>s \<subseteq> A" by simp
    moreover from step have "wt_err_step (sup_state_opt P) step \<tau>s"
      by (simp add: wt_err_step_def JVM_le_Err_conv)
    ultimately have "wt_app_eff (sup_state_opt P) app eff (map ok_val \<tau>s)"
      by (auto intro: wt_err_imp_wt_app_eff simp add: exec_def states_def)
  }    
  ultimately have "wt_method P C Ts T\<^isub>r mxs mxl\<^isub>0 is xt (map ok_val \<tau>s)"
    by (simp add: wt_method_def2 check_types_def)
  thus ?thesis ..
qed
(*>*)

  
lemma (in start_context) wt_method_wt_lbv:
  assumes wt: "wt_method P C Ts T\<^isub>r mxs mxl\<^isub>0 is xt \<tau>s" 
  defines [simp]: "cert \<equiv> mk_cert P mxs T\<^isub>r xt is \<tau>s"
  
  shows "wt_lbv P C Ts T\<^isub>r mxs mxl\<^isub>0 xt cert is" 
(*<*)
proof -
  let ?\<tau>s  = "map OK \<tau>s"
  let ?cert = "make_cert step ?\<tau>s (OK None)"

  from wt obtain 
    0:        "0 < size is" and
    size:     "size is = size ?\<tau>s" and
    ck_types: "check_types P mxs mxl ?\<tau>s" and
    wt_start: "wt_start P C Ts mxl\<^isub>0 \<tau>s" and
    app_eff:  "wt_app_eff (sup_state_opt P) app eff \<tau>s"
    by (force simp add: wt_method_def2 check_types_def) 
  
  from wf have "semilat (JVM_SemiType.sl P mxs mxl)" ..
  hence "semilat (A, r, f)" by (simp add: sl_def2)
  moreover have "top r Err" by (simp add: JVM_le_Err_conv)
  moreover have "Err \<in> A" by (simp add: JVM_states_unfold)
  moreover have "bottom r (OK None)" 
    by (simp add: JVM_le_Err_conv bottom_def lesub_def Err.le_def split: err.split)
  moreover have "OK None \<in> A" by (simp add: JVM_states_unfold)
  moreover from wf have "mono r step (size is) A" by (rule step_mono)
  hence "mono r step (size ?\<tau>s) A" by (simp add: size)
  moreover from exec_pres_type 
  have "pres_type step (size ?\<tau>s) A" by (simp add: size) 
  moreover
  from ck_types have \<tau>s_in_A: "set ?\<tau>s \<subseteq> A" by (simp add: check_types_def)
  hence "\<forall>pc. pc < size ?\<tau>s \<longrightarrow> ?\<tau>s!pc \<in> A \<and> ?\<tau>s!pc \<noteq> Err" by auto
  moreover from bounded_step 
  have "bounded step (size ?\<tau>s)" by (simp add: size)
  moreover have "OK None \<noteq> Err" by simp
  moreover from bounded_step size \<tau>s_in_A app_eff
  have "wt_err_step (sup_state_opt P) step ?\<tau>s"
    by (auto intro: wt_app_eff_imp_wt_err simp add: exec_def states_def)    
  hence "wt_step r Err step ?\<tau>s"
    by (simp add: wt_err_step_def JVM_le_Err_conv)
  moreover
  from 0 size have "0 < size \<tau>s" by auto
  hence "?\<tau>s!0 = OK (\<tau>s!0)" by simp
  with wt_start have "OK first \<sqsubseteq>\<^sub>r ?\<tau>s!0"
    by (clarsimp simp add: wt_start_def lesub_def Err.le_def JVM_le_Err_conv)
  moreover note first_in_A
  moreover have "OK first \<noteq> Err" by simp
  moreover note size 
  ultimately
  have "wtl_inst_list is ?cert f r Err (OK None) step 0 (OK first) \<noteq> Err"
    by (rule lbvc.wtl_complete) 
  moreover from 0 size have "\<tau>s \<noteq> []" by auto
  moreover from ck_types have "check_types P mxs mxl ?cert"
    by (auto simp add: make_cert_def check_types_def JVM_states_unfold)
  moreover note 0 size
  ultimately show ?thesis 
    by (simp add: wt_lbv_def lbvjvm_def mk_cert_def step_def_exec [symmetric]
                  check_cert_def make_cert_def nth_append)
qed  
(*>*)


theorem jvm_lbv_correct:
  "wt_jvm_prog_lbv P Cert \<Longrightarrow> wf_jvm_prog P"
(*<*)
proof -  
  let ?\<Phi> = "\<lambda>C mn. let (C,Ts,T\<^isub>r,(mxs,mxl\<^isub>0,is,xt)) = method P C mn in 
              SOME \<tau>s. wt_method P C Ts T\<^isub>r mxs mxl\<^isub>0 is xt \<tau>s"
    
  assume wt: "wt_jvm_prog_lbv P Cert"
  hence "wf_jvm_prog\<^bsub>?\<Phi>\<^esub> P"
    apply (unfold wf_jvm_prog_phi_def wt_jvm_prog_lbv_def) 
    apply (erule wf_prog_lift)
    apply (auto dest!: start_context.wt_lbv_wt_method [OF start_context.intro] 
                intro: someI)
    apply (erule sees_method_is_class)
    done
  thus ?thesis by (unfold wf_jvm_prog_def) blast
qed
(*>*)

theorem jvm_lbv_complete:
  assumes wt: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P" 
  shows "wt_jvm_prog_lbv P (prg_cert P \<Phi>)"
(*<*)
  using wt
  apply (unfold wf_jvm_prog_phi_def wt_jvm_prog_lbv_def)
  apply (erule wf_prog_lift)
  apply (auto simp add: prg_cert_def 
              intro!: start_context.wt_method_wt_lbv start_context.intro)
  apply (erule sees_method_is_class)                                     
  done
(*>*)

end  
