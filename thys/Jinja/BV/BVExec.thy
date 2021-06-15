(*  Title:      HOL/MicroJava/BV/JVM.thy

    Author:     Tobias Nipkow, Gerwin Klein
    Copyright   2000 TUM
*)

section \<open>Kildall for the JVM \label{sec:JVM}\<close>

theory BVExec
imports "../DFA/Abstract_BV" TF_JVM
begin

definition kiljvm :: "jvm_prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> 
             instr list \<Rightarrow> ex_table \<Rightarrow> ty\<^sub>i' err list \<Rightarrow> ty\<^sub>i' err list"
where
  "kiljvm P mxs mxl T\<^sub>r is xt \<equiv>
  kildall (JVM_SemiType.le P mxs mxl) (JVM_SemiType.sup P mxs mxl) 
          (exec P mxs T\<^sub>r xt is)"

definition wt_kildall :: "jvm_prog \<Rightarrow> cname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
                 instr list \<Rightarrow> ex_table \<Rightarrow> bool"
where
  "wt_kildall P C' Ts T\<^sub>r mxs mxl\<^sub>0 is xt \<equiv>
   0 < size is \<and> 
   (let first  = Some ([],[OK (Class C')]@(map OK Ts)@(replicate mxl\<^sub>0 Err));
        start  = OK first#(replicate (size is - 1) (OK None));
        result = kiljvm P mxs (1+size Ts+mxl\<^sub>0) T\<^sub>r is xt  start
    in \<forall>n < size is. result!n \<noteq> Err)"

definition wf_jvm_prog\<^sub>k :: "jvm_prog \<Rightarrow> bool"
where
  "wf_jvm_prog\<^sub>k P \<equiv>
  wf_prog (\<lambda>P C' (M,Ts,T\<^sub>r,(mxs,mxl\<^sub>0,is,xt)). wt_kildall P C' Ts T\<^sub>r mxs mxl\<^sub>0 is xt) P"


theorem (in start_context) is_bcv_kiljvm:
  "is_bcv r Err step (size is) A (kiljvm P mxs mxl T\<^sub>r is xt)"
(*<*)
proof -
  let ?n = "length is"
  have "Semilat A r f" using semilat_JVM[OF wf]
    by (simp add: Semilat.intro sl_def2)
  moreover have "acc r" using wf by simp blast
  moreover have "top r Err" by (simp add: JVM_le_unfold)
  moreover have "pres_type step ?n A" by (rule exec_pres_type)
  moreover have "bounded step ?n" by (rule bounded_step)
  moreover have "mono r step ?n A" using step_mono[OF wf] by simp
  ultimately have "is_bcv r Err step ?n A (kildall r f step)"
    by(rule is_bcv_kildall)
  moreover have kileq: "kiljvm P mxs mxl T\<^sub>r is xt = kildall r f step"
    using f_def kiljvm_def r_def step_def_exec by blast
  ultimately show ?thesis by simp
qed
(*>*)

(* FIXME: move? *)
lemma subset_replicate [intro?]: "set (replicate n x) \<subseteq> {x}"
  by (induct n) auto

lemma in_set_replicate:
  assumes "x \<in> set (replicate n y)"
  shows "x = y"
(*<*)
proof -
  note assms
  also have "set (replicate n y) \<subseteq> {y}" ..
  finally show ?thesis by simp
qed
(*>*)

lemma (in start_context) start_in_A [intro?]:
  "0 < size is \<Longrightarrow> start \<in> list (size is) A"
  using Ts C
(*<*)
 by (force simp add: JVM_states_unfold intro!: listI list_appendI
           dest!: in_set_replicate)
(*>*)


theorem (in start_context) wt_kil_correct:
  assumes wtk: "wt_kildall P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt"
  shows "\<exists>\<tau>s. wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt \<tau>s"
(*<*)
proof -
  from wtk obtain res where    
    result:   "res = kiljvm P mxs mxl T\<^sub>r is xt start" and
    success:  "\<forall>n < size is. res!n \<noteq> Err" and
    instrs:   "0 < size is" 
    by (unfold wt_kildall_def) simp
      
  have bcv: "is_bcv r Err step (size is) A (kiljvm P mxs mxl T\<^sub>r is xt)"
    by (rule is_bcv_kiljvm)
    
  from instrs have "start \<in> list (size is) A" ..
  with bcv success result have 
    "\<exists>ts\<in>list (size is) A. start [\<sqsubseteq>\<^sub>r] ts \<and> wt_step r Err step ts"
    by (unfold is_bcv_def) blast
  then obtain \<tau>s' where
    in_A: "\<tau>s' \<in> list (size is) A" and
    s:    "start [\<sqsubseteq>\<^sub>r] \<tau>s'" and
    w:    "wt_step r Err step \<tau>s'"
    by blast
  hence wt_err_step: "wt_err_step (sup_state_opt P) step \<tau>s'"
    by (simp add: wt_err_step_def JVM_le_Err_conv)

  from in_A have l: "size \<tau>s' = size is" by simp  
  moreover {
    from in_A  have "check_types P mxs mxl \<tau>s'" by (simp add: check_types_def)
    also from w have "\<forall>x \<in> set \<tau>s'. x \<noteq> Err" 
      by (auto simp add: wt_step_def all_set_conv_all_nth)
    hence [symmetric]: "map OK (map ok_val \<tau>s') = \<tau>s'" 
      by (auto intro!: map_idI simp add: wt_step_def)
    finally  have "check_types P mxs mxl (map OK (map ok_val \<tau>s'))" .
  } 
  moreover {  
    from s have "start!0 \<sqsubseteq>\<^sub>r \<tau>s'!0" by (rule le_listD) simp
    moreover
    from instrs w l 
    have "\<tau>s'!0 \<noteq> Err" by (unfold wt_step_def) simp
    then obtain \<tau>s0 where "\<tau>s'!0 = OK \<tau>s0" by auto
    ultimately
    have "wt_start P C Ts mxl\<^sub>0 (map ok_val \<tau>s')" using l instrs
      by (unfold wt_start_def) 
         (simp add: lesub_def JVM_le_Err_conv Err.le_def)
  }
  moreover 
  from in_A have "set \<tau>s' \<subseteq> A" by simp  
  with wt_err_step bounded_step
  have "wt_app_eff (sup_state_opt P) app eff (map ok_val \<tau>s')"
    by (auto intro: wt_err_imp_wt_app_eff simp add: l)
  ultimately
  have "wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt (map ok_val \<tau>s')"
    using instrs by (simp add: wt_method_def2 check_types_def del: map_map)
  thus ?thesis by blast
qed
(*>*)


theorem (in start_context) wt_kil_complete:
  assumes wtm: "wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt \<tau>s"
  shows "wt_kildall P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt"
(*<*)
proof -
  from wtm obtain
    instrs:   "0 < size is" and
    length:   "length \<tau>s = length is" and 
    ck_type:  "check_types P mxs mxl (map OK \<tau>s)" and
    wt_start: "wt_start P C Ts mxl\<^sub>0 \<tau>s" and
    app_eff:  "wt_app_eff (sup_state_opt P) app eff \<tau>s"
    by (simp add: wt_method_def2 check_types_def)

  from ck_type
  have in_A: "set (map OK \<tau>s) \<subseteq> A" 
    by (simp add: check_types_def)  
  with app_eff in_A bounded_step
  have "wt_err_step (sup_state_opt P) (err_step (size \<tau>s) app eff) (map OK \<tau>s)"
    by - (erule wt_app_eff_imp_wt_err,
          auto simp add: exec_def length states_def)
  hence wt_err: "wt_err_step (sup_state_opt P) step (map OK \<tau>s)" 
    by (simp add: length)
  have is_bcv: "is_bcv r Err step (size is) A (kiljvm P mxs mxl T\<^sub>r is xt)"
    by (rule is_bcv_kiljvm)
  moreover from instrs have "start \<in> list (size is) A" ..
  moreover
  let ?\<tau>s = "map OK \<tau>s"  
  have less_\<tau>s: "start [\<sqsubseteq>\<^sub>r] ?\<tau>s"
  proof (rule le_listI)
    from length instrs
    show "length start = length (map OK \<tau>s)" by simp
  next
    fix n
    from wt_start have "P \<turnstile> ok_val (start!0) \<le>' \<tau>s!0" 
      by (simp add: wt_start_def)
    moreover from instrs length have "0 < length \<tau>s" by simp
    ultimately have "start!0 \<sqsubseteq>\<^sub>r ?\<tau>s!0" 
      by (simp add: JVM_le_Err_conv lesub_def)
    moreover {
      fix n'
      have "OK None \<sqsubseteq>\<^sub>r ?\<tau>s!n"
        by (auto simp add: JVM_le_Err_conv Err.le_def lesub_def 
                 split: err.splits)
      hence "\<lbrakk>n = Suc n'; n < size start\<rbrakk> \<Longrightarrow> start!n \<sqsubseteq>\<^sub>r ?\<tau>s!n" by simp
    }
    ultimately
    show "n < size start \<Longrightarrow> start!n \<sqsubseteq>\<^sub>r ?\<tau>s!n" by (cases n, blast+)   
  qed
  moreover
  from ck_type length
  have "?\<tau>s \<in> list (size is) A"
    by (auto intro!: listI simp add: check_types_def)
  moreover
  from wt_err have "wt_step r Err step ?\<tau>s" 
    by (simp add: wt_err_step_def JVM_le_Err_conv)
  ultimately
  have "\<forall>p. p < size is \<longrightarrow> kiljvm P  mxs mxl T\<^sub>r is xt start ! p \<noteq> Err" 
    by (unfold is_bcv_def) blast
  with instrs 
  show "wt_kildall P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt" by (unfold wt_kildall_def) simp
qed
(*>*)


theorem jvm_kildall_correct:
  "wf_jvm_prog\<^sub>k P = wf_jvm_prog P"
(*<*)
proof -
  let ?\<Phi> = "\<lambda>C M. let (C,Ts,T\<^sub>r,(mxs,mxl\<^sub>0,is,xt)) = method P C M in 
              SOME \<tau>s. wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt \<tau>s"
  let ?A = "\<lambda>P C' (M, Ts, T\<^sub>r, mxs, mxl\<^sub>0, is, xt). wt_kildall P C' Ts T\<^sub>r mxs mxl\<^sub>0 is xt"
  let ?B\<^sub>\<Phi> = "\<lambda>\<Phi>. (\<lambda>P C (M,Ts,T\<^sub>r,(mxs,mxl\<^sub>0,is,xt)). 
                wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt (\<Phi> C M))"

  show ?thesis proof(rule iffI)
    \<comment> \<open>soundness\<close>
    assume wt: "wf_jvm_prog\<^sub>k P"
    then have "wf_prog ?A P" by(simp add: wf_jvm_prog\<^sub>k_def)
    moreover {
      fix wf_md C M Ts Ca T m bd
      assume "wf_prog wf_md P" and sees: "P \<turnstile> Ca sees M :  Ts\<rightarrow>T = m in Ca" and
             "set Ts \<subseteq> types P" and "bd = (M, Ts, T, m)" and
             "?A P Ca bd"
      then have "(?B\<^sub>\<Phi> ?\<Phi>) P Ca bd" using sees_method_is_class[OF sees]
        by (auto dest!: start_context.wt_kil_correct [OF start_context.intro] 
                 intro: someI)
    }
    ultimately have "wf_prog (?B\<^sub>\<Phi> ?\<Phi>) P" by(rule wf_prog_lift)
    then have "wf_jvm_prog\<^bsub>?\<Phi>\<^esub> P" by (simp add: wf_jvm_prog_phi_def)
    thus "wf_jvm_prog P" by (unfold wf_jvm_prog_def) fast
  next  
    \<comment> \<open>completeness\<close>
    assume wt: "wf_jvm_prog P"
    then obtain \<Phi> where "wf_prog (?B\<^sub>\<Phi> \<Phi>) P" by(clarsimp simp: wf_jvm_prog_def wf_jvm_prog_phi_def)
    moreover {
      fix wf_md C M b Ts Ca T m bd
      assume "wf_prog wf_md P" and sees: "P \<turnstile> Ca sees M:  Ts\<rightarrow>T = m in Ca" and
             "set Ts \<subseteq> types P" and "bd = (M, Ts, T, m)" and
             "(?B\<^sub>\<Phi> \<Phi>) P Ca bd"
      then have "?A P Ca bd" using sees_method_is_class[OF sees]
        by (auto intro!: start_context.wt_kil_complete start_context.intro)
    }
    ultimately have "wf_prog ?A P" by(rule wf_prog_lift)
    thus "wf_jvm_prog\<^sub>k P" by (simp add: wf_jvm_prog\<^sub>k_def)
  qed
qed
(*>*)

end
