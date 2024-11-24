(*  Title:      HOL/MicroJava/BV/JVM.thy

    Author:     Tobias Nipkow, Gerwin Klein
    Copyright   2000 TUM
*)

section \<open>Kildall for the JVM \label{sec:JVM}\<close>

theory BVExec
imports "../DFA/Abstract_BV" TF_JVM "../DFA/Typing_Framework_2"
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

context start_context
begin

lemma Cons_less_Conss3 [simp]:
  "x#xs [\<sqsubset>\<^bsub>r\<^esub>] y#ys = (x \<sqsubset>\<^bsub>r\<^esub> y \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys \<or> x = y \<and> xs [\<sqsubset>\<^bsub>r\<^esub>] ys)"
  unfolding lesssub_def r_def
  by (metis JVM_le_Err_conv lesub_def sup_state_opt_err Cons_le_Cons list.inject)

lemma acc_le_listI3 [intro!]:
  " acc r \<Longrightarrow> acc (Listn.le r)"
  apply (unfold acc_def)
  apply (subgoal_tac
      "wf(UN n. {(ys,xs). size xs = n \<and> size ys = n \<and> xs <_(Listn.le r) ys})")
   apply (erule wf_subset)
   apply (blast intro: lesssub_lengthD)
  apply (rule wf_UN)
   prefer 2
  apply fastforce
  apply (rename_tac n)
  apply (induct_tac n)
   apply (simp add: lesssub_def cong: conj_cong)
  apply (rename_tac k)
  apply (simp add: wf_eq_minimal del: r_def f_def step_def A_def)
  apply (simp (no_asm) add: length_Suc_conv cong: conj_cong del: r_def f_def step_def A_def)
  apply clarify
  apply (rename_tac M m)
  apply (case_tac "\<exists>x xs. size xs = k \<and> x#xs \<in> M")
   prefer 2
   apply metis
  apply (erule_tac x = "{a. \<exists>xs. size xs = k \<and> a#xs:M}" in allE)
  apply (erule impE)
   apply blast
  apply (thin_tac "\<exists>x xs. P x xs" for P)
  apply clarify
  apply (rename_tac maxA xs)
  apply (erule_tac x = "{ys. size ys = size xs \<and> maxA#ys \<in> M}" in allE)
  apply (erule impE)
   apply blast
  apply clarify
  using Cons_less_Conss3 by blast


lemma wf_jvm: " wf {(ss', ss). ss [\<sqsubset>\<^bsub>r\<^esub>] ss'}"
  using Semilat.acc_def acc_le_listI3 local.wf r_def by blast

lemma iter_properties_bv[rule_format]:
  shows "\<lbrakk> \<forall>p\<in>w0. p < n; ss0 \<in> nlists n A; \<forall>p<n. p \<notin> w0 \<longrightarrow> stable r step ss0 p \<rbrakk> \<Longrightarrow>
         iter f step ss0 w0 = (ss',w') \<longrightarrow>
         ss' \<in> nlists n A \<and> stables r step ss' \<and> ss0 [\<sqsubseteq>\<^sub>r] ss' \<and>
         (\<forall>ts\<in>nlists n A. ss0 [\<sqsubseteq>\<^sub>r] ts \<and> stables r step ts \<longrightarrow> ss' [\<sqsubseteq>\<^sub>r] ts)"
    (*<*)

  apply (insert semi bounded_step exec_pres_type step_mono[OF wf])  
  apply (unfold iter_def stables_def)

  apply (rule_tac P = "\<lambda>(ss,w).
                ss \<in> nlists n A \<and> (\<forall>p<n. p \<notin> w \<longrightarrow> stable r step ss p) \<and> ss0 [\<sqsubseteq>\<^sub>r] ss \<and>
   (\<forall>ts\<in>nlists n A. ss0 [\<sqsubseteq>\<^sub>r] ts \<and> stables r step ts \<longrightarrow> ss [\<sqsubseteq>\<^sub>r] ts) \<and>
   (\<forall>p\<in>w. p < n)" and
      r = "{(ss',ss) . ss [\<sqsubset>\<^sub>r] ss'} <*lex*> finite_psubset"
      in while_rule)

\<comment> \<open>Invariant holds initially:\<close>  
      apply (simp add:stables_def  semilat_Def   del: n_def A_def r_def f_def step_def)
      apply (blast intro:le_list_refl')     

\<comment> \<open>Invariant is preserved:\<close>
     apply(simp add: stables_def split_paired_all del: A_def r_def f_def step_def n_def)
     apply(rename_tac ss w)
     apply(subgoal_tac "\<forall>(q,t) \<in> set (step (some_elem w) (ss ! (some_elem w))). q < length ss \<and> t \<in> A")
      prefer 2
      apply clarify
      apply (metis boundedD n_def nlistsE_length nlistsE_nth_in pres_typeD some_elem_nonempty)
     apply (subst decomp_propa)
      apply (metis bounded_def n_def nlistsE_length some_elem_def
      some_elem_nonempty)
     apply (simp del:A_def r_def f_def step_def n_def)
     apply (rule conjI)
      apply (metis Semilat.intro[of A r f] nlistsE_length[of _ n A]
      Semilat.merges_preserves_type[of A r f _ n
        "step (some_elem _) (_ ! some_elem _)"])
     apply (simp only:n_def)
     apply (rule conjI)
      apply clarify
      apply (smt (verit, best) Semilat.intro Semilat.stable_pres_lemma some_elem_nonempty)
     apply (rule conjI)
      apply (subgoal_tac "ss \<in> nlists (length is) A" 
      "\<forall>(q,t)\<in>set (step (some_elem w) (ss ! (some_elem w))). q < length is \<and> t \<in> A"
      "ss [\<sqsubseteq>\<^bsub>r\<^esub>] merges f (step (some_elem w) (ss ! (some_elem w))) ss" "ss0\<in> nlists (size is) A"
      "merges f (step (some_elem w) (ss ! (some_elem w))) ss \<in> nlists (size is) A" 
      "ss \<in>nlists (size is) A" "order r A" "ss0 [\<sqsubseteq>\<^bsub>r\<^esub>] ss ")
              apply (blast dest: le_list_trans)
             apply simp
            apply (simp only:semilat_Def)
           apply (simp only:n_def)
          apply (fastforce simp only: n_def dest:Semilat.merges_preserves_type[OF Semilat.intro, OF semi] )
         apply (simp only:n_def)
        apply (blast intro:Semilat.merges_incr[OF Semilat.intro, OF semi])
       apply (metis nlistsE_length)
       apply (simp only:n_def)
     apply(rule conjI)
      apply (clarsimp simp del: A_def r_def f_def step_def)
      apply (blast intro!: some_elem_nonempty Semilat.merges_bounded_lemma[OF Semilat.intro, OF semi])
  apply (smt (verit, best) Un_def case_prod_conv mem_Collect_eq nlists_def set_diff_eq)

\<comment> \<open>Postcondition holds upon termination:\<close>
    apply(clarsimp simp add: stables_def split_paired_all)

\<comment> \<open>Well-foundedness of the termination relation:\<close>
  using wf_finite_psubset wf_jvm apply blast  

\<comment> \<open>Loop decreases along termination relation:\<close>
  apply(simp add: stables_def split_paired_all del: A_def r_def f_def step_def)
  apply(rename_tac ss w)
  apply(subgoal_tac "(some_elem w) \<in> w")
   prefer 2 apply (fast intro: some_elem_nonempty)
  apply(subgoal_tac "\<forall>(q,t) \<in> set (step (some_elem w) (ss ! (some_elem w))). q < length ss \<and> t \<in> A")
   prefer 2
   apply clarify
   apply (metis boundedD nlistsE_length nlistsE_nth_in pres_typeD)
  apply (subst decomp_propa)
   apply blast
  apply clarify
  apply (simp del: nlistsE_length  A_def r_def f_def step_def
      add: lex_prod_def finite_psubset_def 
      bounded_nat_set_is_finite)
  by (intro termination_lemma [OF Semilat.intro], auto)

(*>*)


lemma kildall_properties_bv: 
shows "\<lbrakk> ss0 \<in> nlists n A \<rbrakk> \<Longrightarrow>
  kildall r f step ss0 \<in> nlists n A \<and>
  stables r step (kildall r f step ss0) \<and>
  ss0 [\<sqsubseteq>\<^sub>r] kildall r f step ss0 \<and>
  (\<forall>ts\<in>nlists n A. ss0 [\<sqsubseteq>\<^sub>r] ts \<and> stables r step ts \<longrightarrow>
                 kildall r f step ss0 [\<sqsubseteq>\<^sub>r] ts)"
(*<*) 
  unfolding kildall_def
  by (smt (verit, ccfv_SIG) in_nlistsE iter_properties_bv mem_Collect_eq prod.collapse
      unstables_def)

end

lemma (in start_context) is_bcv_kiljvm: 
shows "is_bcv r Err step (size is) A (kiljvm P mxs mxl T\<^sub>r is xt)" 
  using wf semi kildall_properties_bv
  unfolding kiljvm_def
  apply (fold r_def f_def step_def_exec n_def)
  apply(unfold is_bcv_def wt_step_def)
  unfolding stables_def
  by (metis Err_le_conv JVM_le_Err_conv le_listD nlistsE_length r_def)

(* FIXME: move? *)
lemma subset_replicate [intro?]: "set (replicate n x) \<subseteq> {x}"
  by auto

lemma in_set_replicate:
  assumes "x \<in> set (replicate n y)"
  shows "x = y"
(*<*)
  using assms by force
(*>*)

lemma (in start_context) start_in_A [intro?]:
  "0 < size is \<Longrightarrow> start \<in> nlists (size is) A"
  using Ts C
(*<*)
  apply (simp add: JVM_states_unfold) 
  apply (force intro!: nlistsI nlists_appendI dest!: in_set_replicate)
  done   
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
    
  from instrs have "start \<in> nlists (size is) A" ..
  with bcv success result have 
    "\<exists>ts\<in>nlists (size is) A. start [\<sqsubseteq>\<^sub>r] ts \<and> wt_step r Err step ts"
    by (unfold is_bcv_def) blast
  then obtain \<tau>s' where
    in_A: "\<tau>s' \<in> nlists (size is) A" and
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
  moreover from instrs have "start \<in> nlists (size is) A" ..
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
  have "?\<tau>s \<in> nlists (size is) A"
    by (auto intro!: nlistsI simp add: check_types_def)
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
proof 
  let ?\<Phi> = "\<lambda>C M. let (C,Ts,T\<^sub>r,(mxs,mxl\<^sub>0,is,xt)) = method P C M in 
              SOME \<tau>s. wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt \<tau>s"

  \<comment> \<open>soundness\<close>
  assume wt: "wf_jvm_prog\<^sub>k P"
  hence "wf_jvm_prog\<^bsub>?\<Phi>\<^esub> P"
    apply (unfold wf_jvm_prog_phi_def wf_jvm_prog\<^sub>k_def)    
    apply (erule wf_prog_lift)
    apply (auto dest!: start_context.wt_kil_correct [OF start_context.intro] 
                intro: someI)
    apply (erule sees_method_is_class)
    done
  thus "wf_jvm_prog P" by (unfold wf_jvm_prog_def) fast
next
  \<comment> \<open>completeness\<close>
  assume wt: "wf_jvm_prog P"
  thus "wf_jvm_prog\<^sub>k P"
    apply (unfold wf_jvm_prog_def wf_jvm_prog_phi_def wf_jvm_prog\<^sub>k_def)
    apply (clarify)
    apply (erule wf_prog_lift)
    apply (auto intro!: start_context.wt_kil_complete start_context.intro)
    apply (erule sees_method_is_class)
    done
qed
(*>*)

end
