(*  Title:      JinjaThreads/BV/BVNoTypeError.thy
    Author:     Gerwin Klein, Andreas Lochbihler
*)

header {* \isaheader{Welltyped Programs produce no Type Errors} *}

theory BVNoTypeError
imports "../JVM/JVMDefensive" BVSpecTypeSafe
begin


declare is_IntgI[intro, simp]
declare is_BoolI[intro, simp]
declare is_RefI [simp]
declare defs1 [simp del]

lemma wt_jvm_prog_states:
  "\<lbrakk> wf_jvm_prog\<^sub>\<Phi> P; P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl, ins, et) in C; 
     \<Phi> C M ! pc = \<tau>; pc < size ins \<rbrakk>
  \<Longrightarrow> OK \<tau> \<in> states P mxs (1+size Ts+mxl)"
(*<*)
  apply (unfold wf_jvm_prog_phi_def)
  apply (drule (1) sees_wf_mdecl)
  apply (simp add: wf_mdecl_def wt_method_def check_types_def)
  apply (blast intro: nth_in)
  done
(*>*)

text {*
  The main theorem: welltyped programs do not produce type errors if they
  are started in a conformant state.
*}
theorem no_type_error:
  fixes \<sigma> :: jvm_state
  assumes welltyped: "wf_jvm_prog\<^sub>\<Phi> P" and conforms: "P,\<Phi> \<turnstile> \<sigma> \<surd>"
  shows "exec_d P \<sigma> \<noteq> TypeError"
(*<*)
proof -
  from welltyped obtain mb where wf: "wf_prog mb P" by (fast dest: wt_jvm_progD)
  
  obtain xcp h frs where s [simp]: "\<sigma> = (xcp, h, frs)" by (cases \<sigma>)

  from conforms have "xcp \<noteq> None \<or> frs = [] \<Longrightarrow> check P \<sigma>" 
    by (unfold correct_state_def check_def) auto
  moreover {
    assume "\<not>(xcp \<noteq> None \<or> frs = [])"
    then obtain stk reg C M pc frs' where
      xcp [simp]: "xcp = None" and
      frs [simp]: "frs = (stk,reg,C,M,pc)#frs'" 
      by (clarsimp simp add: neq_Nil_conv) fast

    from conforms obtain  ST LT Ts T mxs mxl ins xt where
      hconf:  "P \<turnstile> h \<surd>" and
      meth:   "P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl, ins, xt) in C" and
      \<Phi>:      "\<Phi> C M ! pc = Some (ST,LT)" and
      frame:  "conf_f P h (ST,LT) ins (stk,reg,C,M,pc)" and
      frames: "conf_fs P h \<Phi> M (size Ts) T frs'"
      by (fastsimp simp add: correct_state_def dest: sees_method_fun)
    
    from frame obtain
      stk: "P,h \<turnstile> stk [:\<le>] ST" and
      reg: "P,h \<turnstile> reg [:\<le>\<^sub>\<top>] LT" and
      pc:  "pc < size ins" 
      by (simp add: conf_f_def)

    from welltyped meth \<Phi> pc
    have "OK (Some (ST, LT)) \<in> states P mxs (1+size Ts+mxl)"
      by (rule wt_jvm_prog_states)
    hence "size ST \<le> mxs" by (auto simp add: JVM_states_unfold)
    with stk have mxs: "size stk \<le> mxs" 
      by (auto dest: list_all2_lengthD)

    from welltyped meth pc
    have "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
      by (rule wt_jvm_prog_impl_wt_instr)
    hence app\<^isub>0: "app (ins!pc) P mxs T pc (size ins) xt (\<Phi> C M!pc) "
      by (simp add: wt_instr_def)
    with \<Phi> have eff: 
      "\<forall>(pc',s')\<in>set (eff (ins ! pc) P pc xt (\<Phi> C M ! pc)). pc' < size ins"
      by (unfold app_def) simp

    from app\<^isub>0 \<Phi> have app:
      "xcpt_app (ins!pc) P pc mxs xt (ST,LT) \<and> app\<^isub>i (ins!pc, P, pc, mxs, T, (ST,LT))"
      by (clarsimp simp add: app_def)

    with eff stk reg 
    have "check_instr (ins!pc) P h stk reg C M pc frs'"
    proof (cases "ins!pc")
      case ALoad
      with app stk reg \<Phi> obtain T ST' where
	ST: "ST = Integer # T # ST'" and
	TNT: "T \<noteq> NT \<longrightarrow> (\<exists>T'. T = T'\<lfloor>\<rceil>)"
	by auto
      from stk ST obtain i stk' ref where
	stk': "stk = Intg i # ref # stk'" and
	ref: "P,h \<turnstile> ref :\<le> T"
	by(auto simp add: conf_def)

      from ref TNT have is_Ref: "is_Ref ref"
	by(auto)
      moreover
      { assume refN: "ref \<noteq> Null"
	with ref have "T \<noteq> NT" by auto
	with TNT obtain T' where T': "T = T'\<lfloor>\<rceil>" by auto
        with ref refN is_Ref wf
	have "\<exists>T si el. h (the_Addr ref) = \<lfloor>Arr T si el\<rfloor>"
	  by(auto simp add:conf_def widen_Array) }
      ultimately show ?thesis using ALoad stk'
	by(auto)
    next
      case AStore
      with app stk reg \<Phi> obtain T U ST' where
	ST: "ST = T # Integer # U # ST'" and
	TNT: "U \<noteq> NT \<longrightarrow> (\<exists>T'. U = T'\<lfloor>\<rceil>)"
	by auto
      from stk ST obtain e i stk' ref where
	stk': "stk = e # Intg i # ref # stk'" and
	ref: "P,h \<turnstile> ref :\<le> U" and
	e: "P,h \<turnstile> e :\<le> T"
	by(fastsimp simp add: conf_def)

      from ref TNT have is_Ref: "is_Ref ref"
	by(auto)
      moreover
      { assume refN: "ref \<noteq> Null"
	with ref have "U \<noteq> NT" by auto
	with TNT obtain T' where T': "U = T'\<lfloor>\<rceil>" by auto
        with ref refN is_Ref wf
	have "\<exists>T si el. h (the_Addr ref) = \<lfloor>Arr T si el\<rfloor>"
	  by(auto simp add:conf_def widen_Array) }
      ultimately show ?thesis using AStore stk'
	by(auto)
    next
      case (Getfield F C) 
      with app stk reg \<Phi> obtain v vT stk' where
        field: "P \<turnstile> C sees F:vT in C" and
        stk:   "stk = v # stk'" and
        conf:  "P,h \<turnstile> v :\<le> Class C"
        by auto
      from field wf have CObject: "C \<noteq> Object"
	by(auto dest: wf_Object_field_empty has_fields_fun simp add: sees_field_def)
      from conf have is_Ref: "is_Ref v" by auto
      moreover {
        assume "v \<noteq> Null" 
        with conf field is_Ref wf CObject
        have "\<exists>D vs. h (the_Addr v) = Some (Obj D vs) \<and> P \<turnstile> D \<preceq>\<^sup>* C"
	  by (auto dest!: non_npD)
      }
      ultimately show ?thesis using Getfield field stk hconf
        apply clarsimp
        apply (rule conjI, fastsimp)
        apply clarsimp
        apply (drule has_visible_field)
        apply (drule (1) has_field_mono)
	      apply (drule (1) hconfD)
	      apply (unfold oconf_def has_field_def)
        apply clarsimp
        apply (fastsimp dest: has_fields_fun)
        done                            
    next
      case (Putfield F C)
      with app stk reg \<Phi> obtain v ref vT stk' where
        field: "P \<turnstile> C sees F:vT in C" and
        stk:   "stk = v # ref # stk'" and
        confv: "P,h \<turnstile> v :\<le> vT" and
        confr: "P,h \<turnstile> ref :\<le> Class C"
        by fastsimp
      from field wf have CObject: "C \<noteq> Object"
	by(auto dest: wf_Object_field_empty has_fields_fun simp add: sees_field_def)
      from confr have is_Ref: "is_Ref ref" by simp
      moreover {
        assume "ref \<noteq> Null" 
        with confr field is_Ref wf CObject
        have "\<exists>D vs. h (the_Addr ref) = Some (Obj D vs) \<and> P \<turnstile> D \<preceq>\<^sup>* C"
          by (auto dest: non_npD)
      }
      ultimately show ?thesis using Putfield field stk confv by fastsimp
    next      
      case (Invoke M' n)
      with app have n: "n < size ST" by simp

      from stk have [simp]: "size stk = size ST" by (rule list_all2_lengthD)
      
      { assume "stk!n = Null" with n Invoke have ?thesis by simp }
      moreover { 
        assume "ST!n = NT"
        with n stk have "stk!n = Null" by (auto simp: list_all2_conv_all_nth)
        with n Invoke have ?thesis by simp
      }
      moreover {
        assume Null: "stk!n \<noteq> Null" and NT: "ST!n \<noteq> NT"

	from NT app Invoke 
	have "(\<exists>D D' Ts T m. ST!n = Class D \<and> P \<turnstile> D sees M': Ts\<rightarrow>T = m in D' \<and> P \<turnstile> rev (take n ST) [\<le>] Ts) \<or>
	      (\<exists>D. ST!n = Class D \<and> (M' = start \<or> M' = join) \<and> P \<turnstile> D \<preceq>\<^sup>* Thread \<and> n = 0 \<and> is_class P Thread) \<or>
	      (is_refT (ST ! n) \<and> (M' = wait \<or> M' = notify \<or> M' = notifyAll) \<and> n = 0)" by(fastsimp)
	moreover
	{ fix D D' Ts T m
	  assume D: "ST!n = Class D"
	    and M': "P \<turnstile> D sees M': Ts\<rightarrow>T = m in D'"
	    and Ts: "P \<turnstile> rev (take n ST) [\<le>] Ts"
          from M' wf have DObject: "D \<noteq> Object"
	    by(auto dest: wf_Object_method_empty)
          from D stk n have "P,h \<turnstile> stk!n :\<le> Class D" 
            by (auto simp: list_all2_conv_all_nth)
          with Null DObject obtain a C' fs where 
            [simp]: "stk!n = Addr a" "h a = Some (Obj C' fs)" and
              "P \<turnstile> C' \<preceq>\<^sup>* D"
	    apply(auto dest!: conf_ClassD)
	    by(case_tac obj, auto simp add: widen_Class)
	  with `P \<turnstile> C' \<preceq>\<^sup>* D` wf M' obtain m' Ts' T' D'' where 
            C': "P \<turnstile> C' sees M': Ts'\<rightarrow>T' = m' in D''" and
            Ts': "P \<turnstile> Ts [\<le>] Ts'"
	    by (auto dest!: sees_method_mono)

          from stk have "P,h \<turnstile> take n stk [:\<le>] take n ST" ..
          hence "P,h \<turnstile> rev (take n stk) [:\<le>] rev (take n ST)" ..
          also note Ts also note Ts'
          finally have "P,h \<turnstile> rev (take n stk) [:\<le>] Ts'" .

          with Invoke Null n C'
          have ?thesis by (auto simp add: is_Ref_def2 has_methodI) }
	moreover
	{ fix D
	  assume D: "ST!n = Class D"
	    and [simp]: "is_class P Thread" "n = 0"
	    and M: "M' = start \<or> M' = join"
	    and M': "P \<turnstile> D \<preceq>\<^sup>* Thread"
          from M' wf have DObject: "D \<noteq> Object"
	    by(auto dest: wf_Object_method_empty)
          from D stk n have "P,h \<turnstile> stk!n :\<le> Class D" 
            by (auto simp: list_all2_conv_all_nth)
          with Null DObject obtain a C' fs where 
            [simp]: "stk!n = Addr a" "h a = Some (Obj C' fs)" and
              "P \<turnstile> C' \<preceq>\<^sup>* D"
	    apply(auto dest!: conf_ClassD)
	    by(case_tac obj, auto simp add: widen_Class)
	  from `P \<turnstile> C' \<preceq>\<^sup>* D` `P \<turnstile> D \<preceq>\<^sup>* Thread`
	  have "P \<turnstile> C' \<preceq>\<^sup>* Thread" by auto
          with Invoke Null n `stk!n = Addr a` `h a = Some (Obj C' fs)` M
          have ?thesis by (auto simp add: is_Ref_def2) }
	moreover
	{ assume "is_refT (ST ! n)"
	  and M': "M' = wait \<or> M' = notify \<or> M' = notifyAll"
	  and [simp]: "n = 0"
	  from n stk NT `is_refT (ST ! n)` Null
	  obtain a where "stk!n = Addr a"
	    by(auto dest!: conf_ClassD simp add: neq_Nil_conv list_all2_Cons2 conf_def widen_Array widen_Class elim!: refTE)
	  with Invoke Null stk n M' have ?thesis
	    by(auto simp add: neq_Nil_conv is_Ref_def conf_def) }
	ultimately have ?thesis by(blast) }
      ultimately show ?thesis by blast      
    next
      case Return with stk app \<Phi> meth frames 
      show ?thesis by (auto simp add: has_methodI)
    qed (auto simp add: list_all2_lengthD)
    hence "check P \<sigma>" using meth pc mxs by (simp add: check_def has_methodI)
  } ultimately
  have "check P \<sigma>" by blast
  thus "exec_d P \<sigma> \<noteq> TypeError" ..
qed
(*>*)

lemma welltyped_commute:
  "\<lbrakk>wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; P,\<Phi> \<turnstile> \<sigma> \<surd>\<rbrakk> \<Longrightarrow> P \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>' = P \<turnstile> \<sigma> -ta-jvm\<rightarrow> \<sigma>'"
apply(rule iffI)
 apply(erule exec_1_d.cases, simp, fastsimp simp add: exec_d_def exec_1_iff split: split_if_asm)
by(auto dest!: no_type_error intro!: exec_1_d.intros simp add: exec_d_def exec_1_iff split: split_if_asm)


lemma BV_correct_d_1:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; P \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'; P,\<Phi> \<turnstile> \<sigma> \<surd> \<rbrakk> \<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>' \<surd>"
  unfolding welltyped_commute
  by(rule BV_correct_1)


text {*
  The theorem above tells us that, in welltyped programs, the
  defensive machine reaches the same result as the aggressive
  one (after arbitrarily many steps).
*}
theorem welltyped_aggressive_imp_defensive:
  "P \<turnstile> \<sigma> -tas-jvm\<rightarrow>* \<sigma>' \<Longrightarrow> wf_jvm_prog\<^sub>\<Phi> P \<Longrightarrow> P,\<Phi> \<turnstile> \<sigma> \<surd>
  \<Longrightarrow> P \<turnstile> (Normal \<sigma>) -tas-jvmd\<rightarrow>* (Normal \<sigma>')"
apply(simp only: exec_star_def)
apply(induct rule: stepify_pred.induct)
 apply(simp add: exec_star_d_def)
 apply(rule stepify_pred_refl)
apply(simp)
apply(simp only: exec_star_def[symmetric])
apply(frule BV_correct, assumption+)
apply (drule_tac \<sigma>="a'" in no_type_error)
 apply(assumption)
apply(drule no_type_error_commutes)
apply (simp add: exec_star_d_def)
apply(rule stepify_pred_trans)
 apply(assumption)
apply (drule exec_1_d_NormalI)
apply(unfold exec_1_iff)
apply(assumption)
apply(rule stepify_pred_step_converse)
 apply(assumption)
apply(rule stepify_pred_refl)
done


text {*
  As corollary we get that the aggressive and the defensive machine
  are equivalent for welltyped programs (if started in a conformant
  state or in the canonical start state)
*} 
corollary welltyped_commutes:
  fixes \<sigma> :: jvm_state
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P" and conforms: "P,\<Phi> \<turnstile> \<sigma> \<surd>" 
  shows "P \<turnstile> (Normal \<sigma>) -tas-jvmd\<rightarrow>* (Normal \<sigma>') = P \<turnstile> \<sigma> -tas-jvm\<rightarrow>* \<sigma>'"
  apply (rule iffI)
  apply (erule defensive_imp_aggressive)
  apply (erule welltyped_aggressive_imp_defensive)
  apply (rule wf)
  apply (rule conforms)
  done

corollary welltyped_initial_commutes:
  assumes wf: "wf_jvm_prog P"  
  assumes meth: "P \<turnstile> C sees M:[]\<rightarrow>T = b in C" 
  defines start: "\<sigma> \<equiv> start_state P C M"
  shows "P \<turnstile> (Normal \<sigma>) -tas-jvmd\<rightarrow>* (Normal \<sigma>') = P \<turnstile> \<sigma> -tas-jvm\<rightarrow>* \<sigma>'"
proof -
  from wf obtain \<Phi> where wf': "wf_jvm_prog\<^sub>\<Phi> P" by (auto simp: wf_jvm_prog_def)
  from this meth have "P,\<Phi> \<turnstile> \<sigma> \<surd>" unfolding start by (rule BV_correct_initial)
  with wf' show ?thesis by (rule welltyped_commutes)
qed


lemma not_TypeError_eq [iff]:
  "x \<noteq> TypeError = (\<exists>t. x = Normal t)"
  by (cases x) auto

locale cnf =
  fixes P and \<Phi> and \<sigma>
  assumes wf: "wf_jvm_prog\<^sub>\<Phi> P"  
  assumes cnf: "correct_state P \<Phi> \<sigma>" 


theorem (in cnf) no_type_errors:
  "P \<turnstile> (Normal \<sigma>) -tas-jvmd\<rightarrow>* \<sigma>' \<Longrightarrow> \<sigma>' \<noteq> TypeError"
apply (unfold exec_star_d_def)
apply(insert cnf)
apply(erule stepify_pred_induct1)
 apply(simp)
apply(fold exec_star_d_def)
apply(insert wf)
apply(clarsimp)
apply(drule defensive_imp_aggressive)
apply (frule (2) BV_correct)
apply (drule (1) no_type_error) back
apply(erule exec_1_d.cases)
 apply(simp)
apply(fastsimp)
done

locale start =
  fixes P and C and M and \<sigma> and T and b
  assumes wf: "wf_jvm_prog P"  
  assumes sees: "P \<turnstile> C sees M:[]\<rightarrow>T = b in C" 
  defines "\<sigma> \<equiv> Normal (start_state P C M)"

corollary (in start) bv_no_type_error:
  shows "P \<turnstile> \<sigma> -tas-jvmd\<rightarrow>* \<sigma>' \<Longrightarrow> \<sigma>' \<noteq> TypeError"
proof -
  from wf obtain \<Phi> where "wf_jvm_prog\<^sub>\<Phi> P" by (auto simp: wf_jvm_prog_def)
  moreover
  with sees have "correct_state P \<Phi> (start_state P C M)" 
    by - (rule BV_correct_initial)
  ultimately have "cnf P \<Phi> (start_state P C M)" by (rule cnf.intro)
  moreover assume "P \<turnstile> \<sigma> -tas-jvmd\<rightarrow>* \<sigma>'"
  ultimately show ?thesis by (unfold \<sigma>_def) (rule cnf.no_type_errors) 
qed

 
end  
