(*  Title:      JinjaThreads/BV/BVNoTypeError.thy
    Author:     Gerwin Klein, Andreas Lochbihler
*)

header {* \isaheader{Welltyped Programs produce no Type Errors} *}

theory BVNoTypeError
imports "../JVM/JVMDefensive" BVSpecTypeSafe
begin

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

context JVM_heap_conf_base' begin

declare is_IntgI [simp, intro]
declare is_BoolI [simp, intro]
declare is_RefI [simp]

text {*
  The main theorem: welltyped programs do not produce type errors if they
  are started in a conformant state.
*}
theorem no_type_error:
  assumes welltyped: "wf_jvm_prog\<^sub>\<Phi> P" and conforms: "\<Phi> \<turnstile> t:\<sigma> \<surd>"
  shows "exec_d P t \<sigma> \<noteq> TypeError"
(*<*)
proof -
  from welltyped obtain mb where wf: "wf_prog mb P" by (fast dest: wt_jvm_progD)
  
  obtain xcp h frs where s [simp]: "\<sigma> = (xcp, h, frs)" by (cases \<sigma>)

  have "check P \<sigma>"
  proof(cases frs)
    case Nil with conforms show ?thesis by (unfold correct_state_def check_def) auto
  next
    case (Cons f frs')
    then obtain stk reg C M pc where frs [simp]: "frs = (stk,reg,C,M,pc)#frs'"
      and f: "f = (stk,reg,C,M,pc)" by(cases f) fastsimp

    from conforms obtain  ST LT Ts T mxs mxl ins xt where
      hconf:  "hconf h" and
      tconf:  "P,h \<turnstile> t \<surd>t" and
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
    hence "size ST \<le> mxs" by (auto simp add: JVM_states_unfold listE_length)
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

    show ?thesis
    proof(cases xcp)
      case None
      note xcp[simp] = this

      from app eff stk reg 
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
	  by(auto simp add: conf_def list_all2_Cons2)
	
	from ref TNT have is_Ref: "is_Ref ref"
          by(cases ref)(auto simp add: is_Ref_def conf_def)
	moreover
	{ assume refN: "ref \<noteq> Null"
	  with ref have "T \<noteq> NT" by auto
	  with TNT obtain T' where T': "T = T'\<lfloor>\<rceil>" by auto
          with ref refN is_Ref wf
	  have "\<exists>T. typeof_addr h (the_Addr ref) = \<lfloor>Array T\<rfloor>"
            by(cases ref)(auto simp add:conf_def widen_Array dest: typeof_addr_eq_Some_conv) }
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
	  by(fastsimp simp add: conf_def list_all2_Cons2)
	
	from ref TNT have is_Ref: "is_Ref ref"
	  by(cases ref)(auto simp add: is_Ref_def conf_def)
	moreover
	{ assume refN: "ref \<noteq> Null"
	  with ref have "U \<noteq> NT" by auto
	  with TNT obtain T' where T': "U = T'\<lfloor>\<rceil>" by auto
          with ref refN is_Ref wf
	  have "\<exists>T. typeof_addr h (the_Addr ref) = \<lfloor>Array T\<rfloor>"
	    by(cases ref)(auto simp add:conf_def widen_Array dest: typeof_addr_eq_Some_conv) }
	ultimately show ?thesis using AStore stk'
	  by(auto)
      next
	case ALength
	with app stk reg \<Phi> obtain T ST' where
	  ST: "ST = T # ST'" and
	  TNT: "T \<noteq> NT \<longrightarrow> (\<exists>T'. T = T'\<lfloor>\<rceil>)"
	  by auto
	from stk ST obtain stk' ref where
	  stk': "stk = ref # stk'" and
	  ref: "P,h \<turnstile> ref :\<le> T"
	  by(auto simp add: conf_def list_all2_Cons2)
      
	from ref TNT have is_Ref: "is_Ref ref"
	  by(cases ref)(auto simp add: is_Ref_def conf_def)
	moreover
	{ assume refN: "ref \<noteq> Null"
	  with ref have "T \<noteq> NT" by auto
	  with TNT obtain T' where T': "T = T'\<lfloor>\<rceil>" by auto
          with ref refN is_Ref wf
	  have "\<exists>T. typeof_addr h (the_Addr ref) = \<lfloor>Array T\<rfloor>"
	    by(cases ref)(auto simp add:conf_def widen_Array dest: typeof_addr_eq_Some_conv) }
	ultimately show ?thesis using ALength stk'
	  by(auto)
      next
	case (Getfield F C) 
	with app stk reg \<Phi> obtain v vT stk' where
          field: "P \<turnstile> C sees F:vT in C" and
          stk:   "stk = v # stk'" and
          conf:  "P,h \<turnstile> v :\<le> Class C"
          by(fastsimp simp add: list_all2_Cons2)
	from field wf have CObject: "C \<noteq> Object"
	  by(auto dest: wf_Object_field_empty has_fields_fun simp add: sees_field_def)
	from conf have is_Ref: "is_Ref v" by(cases v)(auto simp add: is_Ref_def conf_def)
	moreover {
          assume "v \<noteq> Null" 
          with conf field is_Ref wf CObject
          have "\<exists>D. typeof_addr h (the_Addr v) = Some (Class D) \<and> P \<turnstile> D \<preceq>\<^sup>* C"
	    by (auto dest!: non_npD)
	}
	ultimately show ?thesis using Getfield field stk by auto
      next
	case (Putfield F C)
	with app stk reg \<Phi> obtain v ref vT stk' where
          field: "P \<turnstile> C sees F:vT in C" and
          stk:   "stk = v # ref # stk'" and
          confv: "P,h \<turnstile> v :\<le> vT" and
          confr: "P,h \<turnstile> ref :\<le> Class C"
          by(fastsimp simp add: list_all2_Cons2)
	from field wf have CObject: "C \<noteq> Object"
	  by(auto dest: wf_Object_field_empty has_fields_fun simp add: sees_field_def)
	from confr have is_Ref: "is_Ref ref"
          by(cases ref)(auto simp add: is_Ref_def conf_def)
	moreover {
          assume "ref \<noteq> Null" 
          with confr field is_Ref wf CObject
          have "\<exists>D. typeof_addr h (the_Addr ref) = Some (Class D) \<and> P \<turnstile> D \<preceq>\<^sup>* C"
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
	  have "if is_external_call P (ST ! n) M' then \<exists>U Ts. P \<turnstile> rev (take n ST) [\<le>] Ts \<and> P \<turnstile> ST ! n\<bullet>M'(Ts) :: U
	        else \<exists>D D' Ts T m. ST!n = Class D \<and> P \<turnstile> D sees M': Ts\<rightarrow>T = m in D' \<and> P \<turnstile> rev (take n ST) [\<le>] Ts"
	    by auto
 	  moreover
	  { fix D D' Ts T m
	    assume D: "ST!n = Class D"
	      and M': "P \<turnstile> D sees M': Ts\<rightarrow>T = m in D'"
	      and Ts: "P \<turnstile> rev (take n ST) [\<le>] Ts"
	      and nec: "\<not> is_external_call P (ST ! n) M'"
            from M' wf have DObject: "D \<noteq> Object"
	      by(auto dest: wf_Object_method_empty)
            from D stk n have "P,h \<turnstile> stk!n :\<le> Class D" 
              by (auto simp: list_all2_conv_all_nth)
            with Null DObject obtain a C' where 
              [simp]: "stk!n = Addr a" "typeof_addr h a = Some (Class C')" and
		"P \<turnstile> C' \<preceq>\<^sup>* D"
              by(cases "stk ! n")(auto simp add: conf_def widen_Class dest: typeof_addr_eq_Some_conv)
	    with `P \<turnstile> C' \<preceq>\<^sup>* D` wf M' obtain m' Ts' T' D'' where 
              C': "P \<turnstile> C' sees M': Ts'\<rightarrow>T' = m' in D''" and
              Ts': "P \<turnstile> Ts [\<le>] Ts'"
	      by (auto dest!: sees_method_mono)
	    
            from stk have "P,h \<turnstile> take n stk [:\<le>] take n ST" ..
            hence "P,h \<turnstile> rev (take n stk) [:\<le>] rev (take n ST)" ..
            also note Ts also note Ts'
            finally have "P,h \<turnstile> rev (take n stk) [:\<le>] Ts'" .
	    moreover from C' have "\<not> is_external_call P (Class C') M'"
	      by(auto dest: external_call_not_sees_method)
	    ultimately have ?thesis using Invoke Null n C' nec
	      by (auto simp add: is_Ref_def2 has_methodI) }
	  moreover
	  { fix U Ts'
	    assume iec: "is_external_call P (ST ! n) M'"
	      and wtext: "P \<turnstile> ST ! n\<bullet>M'(Ts') :: U" and sub: "P \<turnstile> rev (take n ST) [\<le>] Ts'"
	    from iec have "is_refT (ST ! n)" by(rule is_external_call_is_refT)
	    moreover from stk n have "P,h \<turnstile> stk ! n :\<le> ST ! n" by(rule list_all2_nthD2)
	    ultimately obtain a where a: "stk ! n = Addr a" "typeof_addr h a \<noteq> None"
	      using Null
              by(cases "stk ! n")(auto simp add: conf_def elim!: is_refT.cases simp add: widen_Class widen_Array)
	    with `P,h \<turnstile> stk ! n :\<le> ST ! n` obtain Ta
	      where Ta: "P \<turnstile> Ta \<le> ST ! n" "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>" "Ta \<noteq> NT"
	      by(auto simp add: conf_def dest: typeof_addr_eq_Some_conv)
            have ?thesis
            proof(cases "is_external_call P Ta M'")
              case True
              moreover
	      with wtext `P,h \<turnstile> stk ! n :\<le> ST ! n` Ta
              obtain U' where "P \<turnstile> Ta\<bullet>M'(Ts') :: U'" "P \<turnstile> U' \<le> U"
	        by(auto dest: external_WT_widen_mono split: ty.splits simp add: is_external_call_def)
              moreover from stk have "P,h \<turnstile> take n stk [:\<le>] take n ST" by(rule list_all2_takeI)
	      then obtain Us where "map typeof\<^bsub>h\<^esub> (take n stk) = map Some Us" "P \<turnstile> Us [\<le>] take n ST"
	        by(auto simp add: confs_conv_map)
	      moreover with sub have "P \<turnstile> rev Us [\<le>] Ts'" by(auto intro: widens_trans)
	      moreover note Invoke Null n `stk ! n = Addr a` `typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>`
	      ultimately show ?thesis
	        by(force simp add: is_Ref_def rev_map[symmetric] intro!: external_WT'.intros)
            next
              case False
              then obtain C' where C': "Ta = Class C'" and "P \<turnstile> C' has M'"
                using wtext sub Ta
                apply(auto simp add: is_external_call_def split: ty.splits)
                apply(auto elim!: external_WT.cases)
                apply(erule allE, erule (2) impE[OF _ widen_trans], fastsimp)+
                done
              then obtain Ts'' T'' meth D''
                where sees'': "P \<turnstile> C' sees M':Ts'' \<rightarrow> T''=meth in D''"
                unfolding has_method_def by auto
              moreover 
              from C' Ta obtain C'' where C'': "ST ! n = Class C''" by(auto dest: Class_widen)
              with C' Ta have "P \<turnstile> C' \<preceq>\<^sup>* C''" by simp
              from external_WT_widen_sees_method_contravariant[OF wf sees'' this, of Ts' U] wtext C''
              have "P \<turnstile> Ts' [\<le>] Ts''" by simp
              from stk have "P,h \<turnstile> take n stk [:\<le>] take n ST" ..
              hence "P,h \<turnstile> rev (take n stk) [:\<le>] rev (take n ST)" by simp
              with sub `P \<turnstile> Ts' [\<le>] Ts''`
              have "P,h \<turnstile> rev (take n stk) [:\<le>] Ts''" by(auto intro: widens_trans)
              ultimately show ?thesis using Invoke Null n `stk ! n = Addr a` Ta False C'
                by(simp add: is_Ref_def has_methodI)
            qed }
	  ultimately have ?thesis by(auto split: split_if_asm) }
	ultimately show ?thesis by blast      
      next
	case Return with stk app \<Phi> meth frames 
	show ?thesis by (fastsimp simp add: has_methodI list_all2_Cons2)
      next
	case ThrowExc with stk app \<Phi> meth frames
	show ?thesis
	  by(fastsimp simp add: xcpt_app_def conf_def list_all2_Cons2 intro: widen_trans[OF _ widen_subcls])
      next
	case (BinOpInstr bop) with stk app \<Phi> meth frames
	show ?thesis by(auto simp add: conf_def list_all2_Cons2)(force dest: WTrt_binop_widen_mono)
      qed (auto simp add: list_all2_lengthD list_all2_Cons2)
      thus "check P \<sigma>" using meth pc mxs by (simp add: check_def has_methodI)
    next
      case (Some a)
      with meth pc mxs show ?thesis by(simp add: check_def has_methodI)
    qed
  qed
  thus "exec_d P t \<sigma> \<noteq> TypeError" ..
qed

lemma welltyped_commute:
  "\<lbrakk>wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; \<Phi> \<turnstile> t:\<sigma> \<surd>\<rbrakk> \<Longrightarrow> P,t \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>' = P,t \<turnstile> \<sigma> -ta-jvm\<rightarrow> \<sigma>'"
apply(rule iffI)
 apply(erule exec_1_d.cases, simp, fastsimp simp add: exec_d_def exec_1_iff split: split_if_asm)
by(auto dest!: no_type_error intro!: exec_1_d.intros simp add: exec_d_def exec_1_iff split: split_if_asm)

end

lemma (in JVM_conf_read) BV_correct_d_1:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; P,t \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'; \<Phi> \<turnstile> t:\<sigma> \<surd> \<rbrakk> \<Longrightarrow> \<Phi> \<turnstile> t:\<sigma>' \<surd>"
  unfolding welltyped_commute
  by(rule BV_correct_1)


lemma not_TypeError_eq [iff]:
  "x \<noteq> TypeError = (\<exists>t. x = Normal t)"
  by (cases x) auto

end  
