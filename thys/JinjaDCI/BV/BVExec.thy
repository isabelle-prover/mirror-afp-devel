(*  Title:      JinjaDCI/BV/BVExec.thy

    Author:     Tobias Nipkow, Gerwin Klein, Susannah Mansky
    Copyright   2000 TUM, 2020 UIUC

    Based on the Jinja theory BV/BVExec.thy by Tobias Nipkow and Gerwin Klein
*)

section \<open> Kildall for the JVM \label{sec:JVM} \<close>

theory BVExec
imports Jinja.Abstract_BV TF_JVM Jinja.Typing_Framework_2
begin

definition kiljvm :: "jvm_prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> 
             instr list \<Rightarrow> ex_table \<Rightarrow> ty\<^sub>i' err list \<Rightarrow> ty\<^sub>i' err list"
where
  "kiljvm P mxs mxl T\<^sub>r is xt \<equiv>
  kildall (JVM_SemiType.le P mxs mxl) (JVM_SemiType.sup P mxs mxl) 
          (exec P mxs T\<^sub>r xt is)"

definition wt_kildall :: "jvm_prog \<Rightarrow> cname \<Rightarrow> staticb \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
                 instr list \<Rightarrow> ex_table \<Rightarrow> bool"
where
  "wt_kildall P C' b Ts T\<^sub>r mxs mxl\<^sub>0 is xt \<equiv> (b = Static \<or> b = NonStatic) \<and>
   0 < size is \<and>  
   (let first  = Some ([],(case b of Static \<Rightarrow> [] | NonStatic \<Rightarrow> [OK (Class C')])
                            @(map OK Ts)@(replicate mxl\<^sub>0 Err));
        start  = (OK first)#(replicate (size is - 1) (OK None));
        result = kiljvm P mxs
                   ((case b of Static \<Rightarrow> 0 | NonStatic \<Rightarrow> 1)+size Ts+mxl\<^sub>0)
                     T\<^sub>r is xt start
    in \<forall>n < size is. result!n \<noteq> Err)"

definition wf_jvm_prog\<^sub>k :: "jvm_prog \<Rightarrow> bool"
where
  "wf_jvm_prog\<^sub>k P \<equiv>
  wf_prog (\<lambda>P C' (M,b,Ts,T\<^sub>r,(mxs,mxl\<^sub>0,is,xt)). wt_kildall P C' b Ts T\<^sub>r mxs mxl\<^sub>0 is xt) P"


context start_context
begin

lemma Cons_less_Conss3 [simp]:
  "x#xs [\<sqsubset>\<^bsub>r\<^esub>] y#ys = (x \<sqsubset>\<^bsub>r\<^esub> y \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys \<or> x = y \<and> xs [\<sqsubset>\<^bsub>r\<^esub>] ys)"
  apply (unfold lesssub_def )
  apply auto
  apply (insert sup_state_opt_err)
  apply (unfold lesssub_def lesub_def sup_state_opt_def sup_state_def sup_ty_opt_def)
  apply (simp only: JVM_le_unfold )
  apply fastforce
  done

lemma acc_le_listI3 [intro!]:
  " acc r \<Longrightarrow> acc (Listn.le r)"
apply (unfold acc_def)
apply (subgoal_tac
 "wf(UN n. {(ys,xs). size xs = n \<and> size ys = n \<and> xs <_(Listn.le r) ys})")
   apply (erule wf_subset)
 apply (blast intro: lesssub_lengthD)
apply (rule wf_UN)
 prefer 2
 apply (rename_tac m n)
 apply (case_tac "m=n")
  apply simp
 apply (fast intro!: equals0I dest: not_sym)
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
 apply (erule thin_rl)
 apply (erule thin_rl)
 apply blast
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
apply (thin_tac "m \<in> M")
apply (thin_tac "maxA#xs \<in> M")
apply (rule bexI)
 prefer 2
 apply assumption
apply clarify
apply (simp del: r_def f_def step_def A_def)
apply blast
  done


lemma wf_jvm: " wf {(ss', ss). ss [\<sqsubset>\<^bsub>r\<^esub>] ss'}"
  apply (insert acc_le_listI3 acc_JVM [OF wf])
  by (simp add: acc_def r_def) 

lemma iter_properties_bv[rule_format]:
shows "\<lbrakk> \<forall>p\<in>w0. p < n; ss0 \<in> nlists n A; \<forall>p<n. p \<notin> w0 \<longrightarrow> stable r step ss0 p \<rbrakk> \<Longrightarrow>
         iter f step ss0 w0 = (ss',w') \<longrightarrow>
         ss' \<in> nlists n A \<and> stables r step ss' \<and> ss0 [\<sqsubseteq>\<^sub>r] ss' \<and>
         (\<forall>ts\<in>nlists n A. ss0 [\<sqsubseteq>\<^sub>r] ts \<and> stables r step ts \<longrightarrow> ss' [\<sqsubseteq>\<^sub>r] ts)"
(*<*) (is "PROP ?P")

proof -
  show "PROP ?P"
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
       apply(subgoal_tac "(SOME p. p \<in> w) \<in> w")
        prefer 2 apply (fast intro: someI)
       apply(subgoal_tac "\<forall>(q,t) \<in> set (step (SOME p. p \<in> w) (ss ! (SOME p. p \<in> w))). q < length ss \<and> t \<in> A")
        prefer 2
        apply clarify
        apply (rule conjI)
         apply(clarsimp, blast dest!: boundedD)
        apply (subgoal_tac "(SOME p. p \<in> w) < n")
         apply (subgoal_tac "(ss ! (SOME p. p \<in> w)) \<in> A")
          apply (fastforce simp only:n_def dest:pres_typeD )   
         apply simp
        apply simp
       apply (subst decomp_propa)
        apply blast
       apply (simp del:A_def r_def f_def step_def n_def)
       apply (rule conjI)
        apply (rule Semilat.merges_preserves_type[OF Semilat.intro, OF semi])
         apply blast
        apply clarify
        apply (rule conjI)
         apply(clarsimp, blast dest!: boundedD)
        apply (erule pres_typeD)
          prefer 3
          apply assumption
         apply (erule nlistsE_nth_in)
         apply blast
        apply (simp only:n_def)
       apply (rule conjI)
        apply clarify
        apply (subgoal_tac "ss \<in> nlists (length is) A" "\<forall>p\<in>w. p <  (length is) " "\<forall>p<(length is). p \<notin> w \<longrightarrow> stable r step ss p "
 "p < length is")
            apply (blast   intro!: Semilat.stable_pres_lemma[OF Semilat.intro, OF semi])
           apply (simp only:n_def)
          apply (simp only:n_def)
         apply (simp only:n_def)
        apply (simp only:n_def)
       apply (rule conjI)
        apply (subgoal_tac "ss \<in> nlists (length is) A" 
               "\<forall>(q,t)\<in>set (step (SOME p. p \<in> w) (ss ! (SOME p. p \<in> w))). q < length is \<and> t \<in> A"
               "ss [\<sqsubseteq>\<^bsub>r\<^esub>] merges f (step (SOME p. p \<in> w) (ss ! (SOME p. p \<in> w))) ss" "ss0\<in> nlists (size is) A"
               "merges f (step (SOME p. p \<in> w) (ss ! (SOME p. p \<in> w))) ss \<in> nlists (size is) A" 
               "ss \<in>nlists (size is) A" "order r A" "ss0 [\<sqsubseteq>\<^bsub>r\<^esub>] ss ")
                apply (blast dest: le_list_trans)
               apply simp
              apply (simp only:semilat_Def)
             apply (simp only:n_def)
            apply (fastforce simp only: n_def dest:Semilat.merges_preserves_type[OF Semilat.intro, OF semi] )
           apply (simp only:n_def)
          apply (blast intro:Semilat.merges_incr[OF Semilat.intro, OF semi])
         apply (subgoal_tac "length ss = n")
          apply (simp only:n_def)
         apply (subgoal_tac "ss \<in>nlists n A")
          defer
          apply simp
         apply (simp only:n_def)
        prefer 5
        apply (simp only:nlistsE_length n_def)
       apply(rule conjI)
        apply (clarsimp simp del: A_def r_def f_def step_def)
        apply (blast intro!: Semilat.merges_bounded_lemma[OF Semilat.intro, OF semi])       
       apply (subgoal_tac "bounded step n")
        apply (blast dest!: boundedD)
       apply (simp only:n_def)

  \<comment> \<open>Postcondition holds upon termination:\<close>
      apply(clarsimp simp add: stables_def split_paired_all)
  
  \<comment> \<open>Well-foundedness of the termination relation:\<close>    
      apply (rule wf_lex_prod)
     apply (simp only:wf_jvm) 
    apply (rule wf_finite_psubset) 

  \<comment> \<open>Loop decreases along termination relation:\<close>
     apply(simp add: stables_def split_paired_all del: A_def r_def f_def step_def)
     apply(rename_tac ss w)
     apply(subgoal_tac "(SOME p. p \<in> w) \<in> w")
      prefer 2 apply (fast intro: someI)
     apply(subgoal_tac "\<forall>(q,t) \<in> set (step (SOME p. p \<in> w) (ss ! (SOME p. p \<in> w))). q < length ss \<and> t \<in> A")
      prefer 2
      apply clarify
      apply (rule conjI)
       apply(clarsimp, blast dest!: boundedD)
      apply (erule pres_typeD)
        prefer 3
        apply assumption
       apply (erule nlistsE_nth_in)
       apply blast
      apply blast
     apply (subst decomp_propa)
      apply blast
     apply clarify
  apply (simp del: nlistsE_length  A_def r_def f_def step_def
      add: lex_prod_def finite_psubset_def 
           bounded_nat_set_is_finite)
     apply (rule termination_lemma)
        apply (insert Semilat.intro)
        apply assumption+
      defer
      apply assumption
     defer
     apply clarsimp   
    done
qed

(*>*)


lemma kildall_properties_bv: 
shows "\<lbrakk> ss0 \<in> nlists n A \<rbrakk> \<Longrightarrow>
  kildall r f step ss0 \<in> nlists n A \<and>
  stables r step (kildall r f step ss0) \<and>
  ss0 [\<sqsubseteq>\<^sub>r] kildall r f step ss0 \<and>
  (\<forall>ts\<in>nlists n A. ss0 [\<sqsubseteq>\<^sub>r] ts \<and> stables r step ts \<longrightarrow>
                 kildall r f step ss0 [\<sqsubseteq>\<^sub>r] ts)"
(*<*) (is "PROP ?P")
proof -
  show "PROP ?P"
  apply (unfold kildall_def)
    apply(case_tac "iter f step ss0 (unstables r step ss0)")
    apply (simp del:r_def f_def n_def step_def A_def)
    apply (rule iter_properties_bv)      
     apply (simp_all add: unstables_def stable_def)
    done
qed

end

theorem (in start_context) is_bcv_kiljvm:
  "is_bcv r Err step (size is) A (kiljvm P mxs mxl T\<^sub>r is xt)"
(*<*)
  apply (insert wf)
  apply (unfold kiljvm_def)
  apply (fold r_def f_def step_def_exec n_def)
  apply(unfold is_bcv_def wt_step_def)
  apply(insert semi  kildall_properties_bv)
  apply(simp only:stables_def)
  apply clarify
  apply(subgoal_tac "kildall r f step \<tau>s\<^sub>0 \<in> nlists n A")
   prefer 2
   apply (fastforce intro: kildall_properties_bv)
  apply (rule iffI)
   apply (rule_tac x = "kildall r f step \<tau>s\<^sub>0" in bexI) 
    apply (rule conjI)
     apply (fastforce intro: kildall_properties_bv)
  apply (force intro: kildall_properties_bv)
   apply simp
  apply clarify
  apply(subgoal_tac "kildall r f step \<tau>s\<^sub>0!pa <=_r \<tau>s!pa")
   defer
   apply (blast intro!: le_listD less_lengthI)
  apply (subgoal_tac "\<tau>s!pa \<noteq> Err")
   defer
   apply simp
  apply (rule ccontr)
  apply (simp only:top_def r_def JVM_le_unfold)
  apply fastforce
  done
(*
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
*)
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
  "0 < size is \<Longrightarrow> start \<in> nlists (size is) A"
  using Ts C
(*<*)
proof(cases b)
qed (force simp: JVM_states_unfold intro!: nlistsI nlists_appendI
           dest!: in_set_replicate)+
(*>*)


theorem (in start_context) wt_kil_correct:
  assumes wtk: "wt_kildall P C b Ts T\<^sub>r mxs mxl\<^sub>0 is xt"
  shows "\<exists>\<tau>s. wt_method P C b Ts T\<^sub>r mxs mxl\<^sub>0 is xt \<tau>s"
(*<*)
proof -
  from wtk obtain res where    
    result:   "res = kiljvm P mxs mxl T\<^sub>r is xt start" and
    success:  "\<forall>n < size is. res!n \<noteq> Err" and
    instrs:   "0 < size is" and
    stab:     "b = Static \<or> b = NonStatic" 
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
    have "wt_start P C b Ts mxl\<^sub>0 (map ok_val \<tau>s')" using l instrs
      by (unfold wt_start_def) 
         (cases b; simp add: lesub_def JVM_le_Err_conv Err.le_def)
  }
  moreover 
  from in_A have "set \<tau>s' \<subseteq> A" by simp  
  with wt_err_step bounded_step
  have "wt_app_eff (sup_state_opt P) app eff (map ok_val \<tau>s')"
    by (auto intro: wt_err_imp_wt_app_eff simp add: l)
  ultimately
  have "wt_method P C b Ts T\<^sub>r mxs mxl\<^sub>0 is xt (map ok_val \<tau>s')"
    using instrs stab by (simp add: wt_method_def2 check_types_def del: map_map)
  thus ?thesis by blast
qed
(*>*)


theorem (in start_context) wt_kil_complete:
  assumes wtm: "wt_method P C b Ts T\<^sub>r mxs mxl\<^sub>0 is xt \<tau>s"
  shows "wt_kildall P C b Ts T\<^sub>r mxs mxl\<^sub>0 is xt"
(*<*)
proof -
  from wtm obtain
    instrs:   "0 < size is" and
    length:   "length \<tau>s = length is" and 
    ck_type:  "check_types P mxs mxl (map OK \<tau>s)" and
    wt_start: "wt_start P C b Ts mxl\<^sub>0 \<tau>s" and
    app_eff:  "wt_app_eff (sup_state_opt P) app eff \<tau>s"  and
    stab: "b = Static \<or> b = NonStatic" 
    by (simp add: wt_method_def2 check_types_def )

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
      by (cases b; simp add: wt_start_def)
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
  show "wt_kildall P C b Ts T\<^sub>r mxs mxl\<^sub>0 is xt" 
    using start_context_intro_auxi[OF staticb] using stab by (unfold wt_kildall_def) simp
qed
(*>*)


theorem jvm_kildall_correct:
  "wf_jvm_prog\<^sub>k P = wf_jvm_prog P"
(*<*)
proof -
  let ?\<Phi> = "\<lambda>C M. let (C,b,Ts,T\<^sub>r,(mxs,mxl\<^sub>0,is,xt)) = method P C M in 
              SOME \<tau>s. wt_method P C b Ts T\<^sub>r mxs mxl\<^sub>0 is xt \<tau>s"
  let ?A = "\<lambda>P C' (M, b, Ts, T\<^sub>r, mxs, mxl\<^sub>0, is, xt). wt_kildall P C' b Ts T\<^sub>r mxs mxl\<^sub>0 is xt"
  let ?B\<^sub>\<Phi> = "\<lambda>\<Phi>. (\<lambda>P C (M,b,Ts,T\<^sub>r,(mxs,mxl\<^sub>0,is,xt)). 
                wt_method P C b Ts T\<^sub>r mxs mxl\<^sub>0 is xt (\<Phi> C M))"

  show ?thesis proof(rule iffI)
    \<comment> \<open>soundness\<close>
    assume wt: "wf_jvm_prog\<^sub>k P"
    then have wt': "wf_prog ?A P" by(simp add: wf_jvm_prog\<^sub>k_def)
    moreover {
      fix wf_md C M b Ts Ca T m bd

      assume ass1: "wf_prog wf_md P" and sees: "P \<turnstile> Ca sees M, b :  Ts\<rightarrow>T = m in Ca" and
             ass2: "set Ts \<subseteq> types P" and ass3: "bd = (M, b, Ts, T, m)" and
             ass4: "?A P Ca bd" 
      from ass3 ass4 have stab: "b = Static \<or> b = NonStatic" by (simp add:wt_kildall_def)
      from ass1 sees ass2 ass3 ass4 have "(?B\<^sub>\<Phi> ?\<Phi>) P Ca bd" using sees_method_is_class[OF sees]
        by (auto dest!: start_context.wt_kil_correct[OF start_context_intro_auxi[OF stab]]
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
      assume ass1: "wf_prog wf_md P" and sees: "P \<turnstile> Ca sees M, b :  Ts\<rightarrow>T = m in Ca" and
             ass2: "set Ts \<subseteq> types P" and ass3: "bd = (M, b, Ts, T, m)" and
             ass4: "(?B\<^sub>\<Phi> \<Phi>) P Ca bd"
      from ass3 ass4 have stab: "b = Static \<or> b = NonStatic"  by (simp add:wt_method_def)
      from ass1 sees ass2 ass3 ass4 have "?A P Ca bd" using sees_method_is_class[OF sees] using JVM_sl.staticb
        by (auto intro!: start_context.wt_kil_complete start_context_intro_auxi[OF stab])
    }
    ultimately have "wf_prog ?A P" by(rule wf_prog_lift)
    thus "wf_jvm_prog\<^sub>k P" by (simp add: wf_jvm_prog\<^sub>k_def)
  qed
qed
(*>*)

end
