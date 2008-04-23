(*  Title:      JinjaThreads/BV/EffMono.thy
    Author:     Gerwin Klein, Andreas Lochbihler
*)

header {* \isaheader{Monotonicity of eff and app} *}

theory EffectMono imports Effect begin

declare not_Err_eq [iff]

lemma wf_method_Object_empty:
  assumes wf: "wf_prog wf_md P"
  shows "\<not> P \<turnstile> C sees M: Ts\<rightarrow>T = m in Object"
proof
  assume sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = m in Object"
  from wf obtain O' fs ms where classO: "class P Object = \<lfloor>(O', fs, ms)\<rfloor>"
    apply -
    apply(drule is_class_Object)
    by(unfold is_class_def, auto)
  from wf classO have "ms = []"
    by(auto simp add: wf_prog_def wf_cdecl_def class_def dest: map_of_is_SomeD bspec)
  with classO sees show False
    apply(clarsimp simp add: Method_def)
    by(drule visible_methods_exist, auto)
qed

declare widens_trans[trans]

lemma app\<^isub>i_mono: 
  assumes wf: "wf_prog p P"
  assumes less: "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  shows "app\<^isub>i (i,P,mxs,mpc,rT,\<tau>') \<Longrightarrow> app\<^isub>i (i,P,mxs,mpc,rT,\<tau>)"
(*<*)
proof -
  assume app: "app\<^isub>i (i,P,mxs,mpc,rT,\<tau>')"
  
  obtain ST LT ST' LT' where
    [simp]: "\<tau> = (ST,LT)" and
    [simp]: "\<tau>' = (ST',LT')" 
    by (cases \<tau>, cases \<tau>')

  from less have [simp]: "size ST = size ST'" and [simp]: "size LT = size LT'"
    by (auto dest: list_all2_lengthD)

  note [iff] = list_all2_Cons2 widen_Class  
  note [simp] = fun_of_def 

  from app less show "app\<^isub>i (i,P,mxs,mpc,rT,\<tau>)"
  proof (cases i)
    case Load
    with app less show ?thesis by (auto dest!: list_all2_nthD)
  next
    case (Invoke M n)
    with app have n: "n < size ST'" by simp
    
    { assume "ST!n = NT" hence ?thesis using n app Invoke by simp }
    moreover {
      assume "ST'!n = NT"
      moreover with n less have "ST!n = NT" 
        by (auto dest: list_all2_nthD)
      ultimately have ?thesis using n app Invoke by simp
    }
    moreover {
      assume ST: "ST!n \<noteq> NT" and ST': "ST'!n \<noteq> NT" 

      from ST' app Invoke
      have  "(\<exists>D Ts T m C'. ST' ! n = Class D \<and> P \<turnstile> D sees M:Ts \<rightarrow> T = m in C' \<and> P \<turnstile> rev (take n ST') [\<le>] Ts) \<or>
	     (\<exists>D. ST' ! n = Class D \<and> P \<turnstile> D \<preceq>\<^sup>* Thread \<and> (M = start \<or> M = join) \<and> n = 0 \<and> is_class P Thread) \<or>
	     (is_refT (ST' ! n) \<and> (M = wait \<or> M = notify \<or> M = notifyAll) \<and> n = 0)"
	by(simp, blast)
      moreover
      from less have "P \<turnstile> ST!n \<le> ST'!n"
	by(auto dest: list_all2_nthD2[OF _ n])
      { fix D Ts T m C'
	assume D: "ST' ! n = Class D"
	  and Ts: "P \<turnstile> rev (take n ST') [\<le>] Ts"
	  and D_M: "P \<turnstile> D sees M: Ts\<rightarrow>T = m in C'"
	from D_M wf_Object_method_empty[OF wf]
	have "D \<noteq> Object" by(auto)
	with `P \<turnstile> ST!n \<le> ST'!n`
	obtain D' where
          D': "ST!n = Class D'" and DsubC: "P \<turnstile> D' \<preceq>\<^sup>* D"
	  using D ST by auto

	from wf D_M DsubC obtain Ts' T' m' C'' where
          D'_M: "P \<turnstile> D' sees M: Ts'\<rightarrow>T' = m' in C''" and
          Ts': "P \<turnstile> Ts [\<le>] Ts'"
          by (blast dest: sees_method_mono) 
	
	from less have "P \<turnstile> rev (take n ST) [\<le>] rev (take n ST')" by simp
	also note Ts also note Ts' 
	finally have "P \<turnstile> rev (take n ST) [\<le>] Ts'" .
	with D'_M D' app less Invoke D have ?thesis by fastsimp }
      moreover
      { fix D
	assume D: "ST' ! n = Class D"
	  and "P \<turnstile> D \<preceq>\<^sup>* Thread" "M = start \<or> M = join" "n = 0" "is_class P Thread"
	with `P \<turnstile> ST!n \<le> ST'!n`
	obtain D' where
          D': "ST!n = Class D'" and DsubC: "P \<turnstile> D' \<preceq>\<^sup>* D"
	  using D ST by auto
	with `P \<turnstile> D \<preceq>\<^sup>* Thread` have "P \<turnstile> D' \<preceq>\<^sup>* Thread" by auto
	with app less Invoke `M = start \<or> M = join` `n = 0` D' `is_class P Thread`
	have ?thesis by auto }
      moreover
      { assume "is_refT (ST' ! n)"
	and [simp]: "M = wait \<or> M = notify \<or> M = notifyAll" "n = 0"
	with `P \<turnstile> ST!n \<le> ST'!n`
	have "is_refT (ST ! n)"
	  by(auto elim!: refTE simp add: widen_Array)
	with app less Invoke ST have ?thesis by(simp) }
      ultimately have ?thesis by blast }
    ultimately show ?thesis by blast
  next 
    case (Getfield F C)
    with app less wf_Object_field_empty[OF wf] show ?thesis
      by(fastsimp simp add: sees_field_def dest: has_fields_fun)
  next
    case (Putfield F C)
    with app less wf_Object_field_empty[OF wf] show ?thesis
      by (fastsimp intro: widen_trans rtrancl_trans simp add: sees_field_def dest: has_fields_fun)
  next
    case Return
    with app less show ?thesis by (fastsimp intro: widen_trans)
  next
    case ALoad
    with app less show ?thesis
      apply(clarsimp)
      by(case_tac "T = NT", auto simp add: widen_Array)
  next
    case AStore
    with app less show ?thesis
      apply(clarsimp)
      by(case_tac "U = NT", auto simp add: widen_Array)
  next
    case (Checkcast T)
    with app less show ?thesis
      by(auto elim!: refTE simp: widen_Array)
  next
    case Throw
    with app less show ?thesis
      by(auto elim!: refTE simp: widen_Array)
  next
    case MEnter
    with app less show ?thesis
      by(auto elim!: refTE simp: widen_Array)
  next
    case MExit
    with app less show ?thesis
      by(auto elim!: refTE simp: widen_Array)
  qed (auto elim!: refTE not_refTE)
qed
(*>*)

lemma succs_mono:
  assumes wf: "wf_prog p P" and app\<^isub>i: "app\<^isub>i (i,P,mxs,mpc,rT,\<tau>')"
  shows "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>' \<Longrightarrow> set (succs i \<tau> pc) \<subseteq> set (succs i \<tau>' pc)"
(*<*)
proof (cases i)
  case (Invoke M n)
  obtain ST LT ST' LT' where 
    [simp]: "\<tau> = (ST,LT)" and [simp]: "\<tau>' = (ST',LT')" by (cases \<tau>, cases \<tau>') 
  assume "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  moreover
  with app\<^isub>i Invoke have "n < size ST" by (auto dest: list_all2_lengthD)
  ultimately
  have "P \<turnstile> ST!n \<le> ST'!n" by (auto simp add: fun_of_def dest: list_all2_nthD)
  with Invoke show ?thesis by auto 
next
  case ALoad
  obtain ST LT ST' LT' where 
    [simp]: "\<tau> = (ST,LT)" and [simp]: "\<tau>' = (ST',LT')" by (cases \<tau>, cases \<tau>') 
  assume "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  moreover
  with app\<^isub>i ALoad have "1 < size ST" by (auto dest: list_all2_lengthD)
  ultimately
  have "P \<turnstile> ST!1 \<le> ST'!1" by (auto simp add: fun_of_def dest: list_all2_nthD)
  with ALoad show ?thesis by auto
next 
  case AStore
  obtain ST LT ST' LT' where 
    [simp]: "\<tau> = (ST,LT)" and [simp]: "\<tau>' = (ST',LT')" by (cases \<tau>, cases \<tau>') 
  assume "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  moreover
  with app\<^isub>i AStore have "2 < size ST" by (auto dest: list_all2_lengthD)
  ultimately
  have "P \<turnstile> ST!2 \<le> ST'!2" by (auto simp add: fun_of_def dest: list_all2_nthD)
  with AStore show ?thesis by auto
next
  case MEnter
  obtain ST LT ST' LT' where 
    [simp]: "\<tau> = (ST,LT)" and [simp]: "\<tau>' = (ST',LT')" by (cases \<tau>, cases \<tau>') 
  assume "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  moreover
  with app\<^isub>i MEnter have "0 < size ST" by (auto dest: list_all2_lengthD)
  ultimately
  have "P \<turnstile> ST!0 \<le> ST'!0" by (auto simp add: fun_of_def dest: list_all2_nthD)
  with MEnter show ?thesis by auto
next
  case MExit
  obtain ST LT ST' LT' where 
    [simp]: "\<tau> = (ST,LT)" and [simp]: "\<tau>' = (ST',LT')" by (cases \<tau>, cases \<tau>') 
  assume "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  moreover
  with app\<^isub>i MExit have "0 < size ST" by (auto dest: list_all2_lengthD)
  ultimately
  have "P \<turnstile> ST!0 \<le> ST'!0" by (auto simp add: fun_of_def dest: list_all2_nthD)
  with MExit show ?thesis by auto
qed auto
(*>*)
  

lemma app_mono: 
  assumes wf: "wf_prog p P"
  assumes less': "P \<turnstile> \<tau> \<le>' \<tau>'"
  shows "app i P m rT pc mpc xt \<tau>' \<Longrightarrow> app i P m rT pc mpc xt \<tau>"
(*<*)
proof (cases \<tau>)
  case None thus ?thesis by simp
next
  case (Some \<tau>\<^isub>1) 
  moreover
  with less' obtain \<tau>\<^isub>2 where \<tau>\<^isub>2: "\<tau>' = Some \<tau>\<^isub>2" by (cases \<tau>') auto
  ultimately have less: "P \<turnstile> \<tau>\<^isub>1 \<le>\<^sub>i \<tau>\<^isub>2" using less' by simp
  
  assume "app i P m rT pc mpc xt \<tau>'"
  with Some \<tau>\<^isub>2 obtain
    app\<^isub>i: "app\<^isub>i (i, P, pc, m, rT, \<tau>\<^isub>2)" and
    xcpt: "xcpt_app i P pc m xt \<tau>\<^isub>2" and
    succs: "\<forall>(pc',s')\<in>set (eff i P pc xt (Some \<tau>\<^isub>2)). pc' < mpc"
    by (auto simp add: app_def)
  
  from wf less app\<^isub>i have "app\<^isub>i (i, P, pc, m, rT, \<tau>\<^isub>1)" by (rule app\<^isub>i_mono)
  moreover
  from less have "size (fst \<tau>\<^isub>1) = size (fst \<tau>\<^isub>2)" 
    by (cases \<tau>\<^isub>1, cases \<tau>\<^isub>2) (auto dest: list_all2_lengthD)
  with xcpt have "xcpt_app i P pc m xt \<tau>\<^isub>1" by (simp add: xcpt_app_def)
  moreover
  from wf app\<^isub>i less have "\<forall>pc. set (succs i \<tau>\<^isub>1 pc) \<subseteq> set (succs i \<tau>\<^isub>2 pc)"
    by (blast dest: succs_mono)
  with succs
  have "\<forall>(pc',s')\<in>set (eff i P pc xt (Some \<tau>\<^isub>1)). pc' < mpc"
    by (cases \<tau>\<^isub>1, cases \<tau>\<^isub>2)
       (auto simp add: eff_def norm_eff_def xcpt_eff_def dest: bspec)
  ultimately
  show ?thesis using Some by (simp add: app_def)
qed
(*>*)


lemma eff\<^isub>i_mono:
  assumes wf: "wf_prog p P"
  assumes less: "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  assumes app\<^isub>i: "app i P m rT pc mpc xt (Some \<tau>')"
  assumes succs: "succs i \<tau> pc \<noteq> []"  "succs i \<tau>' pc \<noteq> []"
  shows "P \<turnstile> eff\<^isub>i (i,P,\<tau>) \<le>\<^sub>i eff\<^isub>i (i,P,\<tau>')"
(*<*)
proof -
  obtain ST LT ST' LT' where
    [simp]: "\<tau> = (ST,LT)" and
    [simp]: "\<tau>' = (ST',LT')" 
    by (cases \<tau>, cases \<tau>')
  
  note [simp] = eff_def app_def fun_of_def 

  from less have "P \<turnstile> (Some \<tau>) \<le>' (Some \<tau>')" by simp
  from wf this app\<^isub>i 
  have app: "app i P m rT pc mpc xt (Some \<tau>)" by (rule app_mono)

  from less app app\<^isub>i show ?thesis
  proof (cases i)
    case Throw with succs have False by simp
    thus ?thesis ..
  next
    case Return with succs have False by simp
    thus ?thesis ..
  next
    case (Load i)
    from Load app obtain y where
       y:  "i < size LT" "LT!i = OK y" by clarsimp
    from Load app\<^isub>i obtain y' where
       y': "i < size LT'" "LT'!i = OK y'" by clarsimp

    from less have "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" by simp
    with y y' have "P \<turnstile> y \<le> y'" by (auto dest: list_all2_nthD)    
    with Load less y y' app app\<^isub>i
    show ?thesis by auto
  next
    case Store with less app app\<^isub>i
    show ?thesis by (auto simp add: list_all2_update_cong) 
  next
    case (Invoke M n) 
    with app\<^isub>i have n: "n < size ST'" by simp
    from less have [simp]: "size ST = size ST'" 
      by (auto dest: list_all2_lengthD)

    from Invoke succs have ST: "ST!n \<noteq> NT" and ST': "ST'!n \<noteq> NT"
      by (auto)
    
    from ST' app\<^isub>i Invoke
    have  "(\<exists>D Ts T m C'. ST' ! n = Class D \<and> P \<turnstile> D sees M:Ts \<rightarrow> T = m in C' \<and> P \<turnstile> rev (take n ST') [\<le>] Ts) \<or>
           (\<exists>D. ST' ! n = Class D \<and> P \<turnstile> D \<preceq>\<^sup>* Thread \<and> (M = start \<or> M = join) \<and> n = 0 \<and> is_class P Thread) \<or>
	    (is_refT (ST' ! n) \<and> (M = wait \<or> M = notify \<or> M = notifyAll) \<and> n = 0)"
      by(simp, blast)
    moreover
    from less have "P \<turnstile> ST!n \<le> ST'!n"
      by(auto dest: list_all2_nthD2[OF _ n])
    { fix D Ts T m C'
      assume D: "ST' ! n = Class D"
	and D_M: "P \<turnstile> D sees M: Ts\<rightarrow>T = m in C'"
      from D_M wf_Object_method_empty[OF wf]
      have "D \<noteq> Object" by(auto)
      with `P \<turnstile> ST!n \<le> ST'!n` obtain D' where
	D': "ST!n = Class D'" and DsubC: "P \<turnstile> D' \<preceq>\<^sup>* D"
	using D ST by(auto simp: widen_Class)

      from D_M have "\<lbrakk> M = start \<or> M = join; P \<turnstile> D \<preceq>\<^sup>* Thread \<rbrakk> \<Longrightarrow> False"
	by(auto dest: Thread_not_sees_method_start[OF wf] Thread_not_sees_method_join[OF wf])
      moreover
      from wf D_M DsubC obtain Ts' T' m' C'' where
	D'_M: "P \<turnstile> D' sees M: Ts'\<rightarrow>T' = m' in C''" and
	Ts': "P \<turnstile> T' \<le> T"
	by (blast dest: sees_method_mono)
      moreover
      hence "\<lbrakk> M = start \<or> M = join; P \<turnstile> D' \<preceq>\<^sup>* Thread \<rbrakk> \<Longrightarrow> False"
	by(auto dest: Thread_not_sees_method_start[OF wf] Thread_not_sees_method_join[OF wf])
      ultimately have ?thesis using Invoke n D D' D_M less
	by(auto intro: list_all2_dropI) }
    moreover
    { fix D
      assume D: "ST' ! n = Class D" 
	and "P \<turnstile> D \<preceq>\<^sup>* Thread" "M = start \<or> M = join" "n = 0"
      with `P \<turnstile> ST!n \<le> ST'!n` obtain D' where
	D': "ST!n = Class D'" and DsubC: "P \<turnstile> D' \<preceq>\<^sup>* D"
	using D ST by(auto simp: widen_Class)
      with `P \<turnstile> D \<preceq>\<^sup>* Thread` have "P \<turnstile> D' \<preceq>\<^sup>* Thread" by auto
      with Invoke D ST less `P \<turnstile> D \<preceq>\<^sup>* Thread` `M = start \<or> M = join` `n = 0`
      have ?thesis
	apply(cases ST, simp)
	apply(cases ST', simp)
	apply(auto simp add: widen_Class)
 	 apply(erule notE)
	 apply(erule rtranclp_trans, assumption)
	apply(erule notE)
	by(rule rtranclp_trans) }
    moreover
    { assume "is_refT (ST' ! n)"
      and "M = wait \<or> M = notify \<or> M = notifyAll" "n = 0"
      with app less Invoke ST have ?thesis by simp }
    ultimately show ?thesis by blast
  next
    case ALoad with less app app\<^isub>i succs
    show ?thesis by(auto split: split_if_asm dest: Array_Array_widen)
  next
    case AStore with less app app\<^isub>i succs
    show ?thesis by(auto split: split_if_asm dest: Array_Array_widen)
  qed auto
qed
(*>*)

end

