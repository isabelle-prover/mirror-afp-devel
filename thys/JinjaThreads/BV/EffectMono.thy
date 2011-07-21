(*  Title:      JinjaThreads/BV/EffectMono.thy
    Author:     Gerwin Klein, Andreas Lochbihler
*)

header {* \isaheader{Monotonicity of eff and app} *}

theory EffectMono imports Effect begin

declare not_Err_eq [iff]

declare widens_trans[trans]

lemma app\<^isub>i_mono: 
  assumes wf: "wf_prog p P"
  assumes less: "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  shows "app\<^isub>i (i,P,mxs,mpc,rT,\<tau>') \<Longrightarrow> app\<^isub>i (i,P,mxs,mpc,rT,\<tau>)"
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
      ultimately have ?thesis using n app Invoke by simp }
    moreover {
      assume ST: "ST!n \<noteq> NT" and ST': "ST'!n \<noteq> NT" 

      from ST' app Invoke
      have "if is_native P (ST' ! n) M then \<exists>U Ts. P \<turnstile> rev (take n ST') [\<le>] Ts \<and> P \<turnstile> ST' ! n\<bullet>M(Ts) :: U
	    else \<exists>D Ts T m C'. class_type_of (ST' ! n) = \<lfloor>D\<rfloor> \<and> P \<turnstile> D sees M:Ts \<rightarrow> T = m in C' \<and> P \<turnstile> rev (take n ST') [\<le>] Ts"
	by fastsimp
      moreover
      from less have "P \<turnstile> ST!n \<le> ST'!n"
	by(auto dest: list_all2_nthD2[OF _ n])
      { fix D Ts T m C'
	assume D: "class_type_of (ST' ! n) = \<lfloor>D\<rfloor>"
	  and Ts: "P \<turnstile> rev (take n ST') [\<le>] Ts"
	  and D_M: "P \<turnstile> D sees M: Ts\<rightarrow>T = m in C'"
	  and nec: "\<not> is_native P (ST' ! n) M"
        
        from D `P \<turnstile> ST!n \<le> ST'!n` ST
        obtain D' where D': "class_type_of (ST ! n) = \<lfloor>D'\<rfloor>" 
          and DsubC: "P \<turnstile> D' \<preceq>\<^sup>* D"
          unfolding is_class_type_of_conv_class_type_of_Some[symmetric]
          by(rule widen_is_class_type_of)
	from wf D_M DsubC obtain Ts' T' m' C'' where
          D'_M: "P \<turnstile> D' sees M: Ts'\<rightarrow>T' = m' in C''" and
          Ts': "P \<turnstile> Ts [\<le>] Ts'"
          by (blast dest: sees_method_mono) 
	
        have ?thesis
        proof(cases "is_native P (ST ! n) M")
          case False
	  from less have "P \<turnstile> rev (take n ST) [\<le>] rev (take n ST')" by simp
	  also note Ts also note Ts' 
	  finally have "P \<turnstile> rev (take n ST) [\<le>] Ts'" .
	  with False D'_M D' app less Invoke D show ?thesis by(auto)
        next
          case True
          with D' D'_M obtain Ts'' Tr''
            where wtext: "P \<turnstile> ST ! n\<bullet>M(Ts'') :: Tr''" 
            and "P \<turnstile> Ts' [\<le>] Ts''" "P \<turnstile> Tr'' \<le> T'"
            unfolding is_class_type_of_conv_class_type_of_Some[symmetric]
            by(auto dest: is_native_sees_method_overriding[OF wf])
          from less have "P \<turnstile> rev (take n ST) [\<le>] rev (take n ST')" by simp
          also note Ts also note Ts' also note `P \<turnstile> Ts' [\<le>] Ts''`
          finally have "P \<turnstile> rev (take n ST) [\<le>] Ts''" .
          with D'_M D' app less Invoke D Ts' D' nec ST wtext `P \<turnstile> Tr'' \<le> T'` True
          show ?thesis by(auto)
        qed
      } moreover {
	fix Ts U
	assume exc: "is_native P (ST' ! n) M"
	  and wtext: "P \<turnstile> ST' ! n\<bullet>M(Ts) :: U"
          and sub: "P \<turnstile> rev (take n ST') [\<le>] Ts"
        from wtext obtain T' where native': "P \<turnstile> ST' ! n native M:Ts\<rightarrow>U in T'"
          unfolding is_native_def2 by(auto simp add: external_WT.simps)
        have ?thesis
        proof(cases "is_native P (ST ! n) M")
          case True
          then obtain Ts' Tr' T'
            where native: "P \<turnstile> ST ! n native M:Ts'\<rightarrow>Tr' in T'"
            unfolding is_native_def2 by blast
          moreover {
            from less have "P \<turnstile> rev (take n ST) [\<le>] rev (take n ST')" by simp
            also note sub also from native' native `P \<turnstile> ST!n \<le> ST'!n`
            have "P \<turnstile> Ts [\<le>] Ts'" by(rule native_native_overriding)
            finally have "P \<turnstile> rev (take n ST) [\<le>] Ts'" . }
          ultimately show ?thesis using app Invoke ST' exc True wtext
            by(auto simp add: external_WT.simps)
        next
          case False
          with native_not_native_overriding[OF wf native' this `P \<turnstile> ST ! n \<le> ST' ! n` ST]
          obtain C Ts' Tr' body D where "is_class_type_of (ST ! n) C"
            and "P \<turnstile> C sees M: Ts'\<rightarrow>Tr' = body in D"
            and "P \<turnstile> Ts [\<le>] Ts'" and "P \<turnstile> Tr' \<le> U" " P \<turnstile> Class C \<le> T'"
            by blast
          moreover {
            from less have "P \<turnstile> rev (take n ST) [\<le>] rev (take n ST')" by simp
            also note sub also note `P \<turnstile> Ts [\<le>] Ts'`
            finally have "P \<turnstile> rev (take n ST) [\<le>] Ts'" .
          }
          ultimately show ?thesis using app Invoke False 
            by(auto simp add: is_class_type_of_conv_class_type_of_Some)
        qed }
      ultimately have ?thesis by(auto split: split_if_asm) }
    ultimately show ?thesis by blast
  next 
    case Getfield
    with app less show ?thesis
      by(fastsimp simp add: sees_field_def widen_Array dest: has_fields_fun)
  next
    case Putfield
    with app less show ?thesis
      by (fastsimp intro: widen_trans rtrancl_trans simp add: sees_field_def widen_Array dest: has_fields_fun)
  next
    case Return
    with app less show ?thesis by (fastsimp intro: widen_trans)
  next
    case ALoad
    with app less show ?thesis by(auto simp add: widen_Array)
  next
    case AStore
    with app less show ?thesis by(auto simp add: widen_Array)
  next
    case ALength
    with app less show ?thesis by(auto simp add: widen_Array)
  next
    case (Checkcast T)
    with app less show ?thesis
      by(auto elim!: refTE simp: widen_Array)
  next
    case (Instanceof T)
    with app less show ?thesis
      by(auto elim!: refTE simp: widen_Array)
  next
    case ThrowExc
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
  next
    case (BinOpInstr bop)
    with app less show ?thesis by(force dest: WTrt_binop_widen_mono)
  next
    case Dup
    with app less show ?thesis
      by(auto dest: list_all2_lengthD)
  next
    case Swap
    with app less show ?thesis
      by(auto dest: list_all2_lengthD)
  qed (auto elim!: refTE not_refTE)
qed

lemma succs_mono:
  assumes wf: "wf_prog p P" and app\<^isub>i: "app\<^isub>i (i,P,mxs,mpc,rT,\<tau>')"
  shows "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>' \<Longrightarrow> set (succs i \<tau> pc) \<subseteq> set (succs i \<tau>' pc)"
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
  case ALength
  obtain ST LT ST' LT' where 
    [simp]: "\<tau> = (ST,LT)" and [simp]: "\<tau>' = (ST',LT')" by (cases \<tau>, cases \<tau>') 
  assume "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  moreover
  with app\<^isub>i ALength have "0 < size ST" by (auto dest: list_all2_lengthD)
  ultimately
  have "P \<turnstile> ST!0 \<le> ST'!0" by (auto simp add: fun_of_def dest: list_all2_nthD)
  with ALength show ?thesis by auto
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

lemma app_mono: 
  assumes wf: "wf_prog p P"
  assumes less': "P \<turnstile> \<tau> \<le>' \<tau>'"
  shows "app i P m rT pc mpc xt \<tau>' \<Longrightarrow> app i P m rT pc mpc xt \<tau>"
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

lemma eff\<^isub>i_mono:
  assumes wf: "wf_prog p P"
  assumes less: "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  assumes app\<^isub>i: "app i P m rT pc mpc xt (Some \<tau>')"
  assumes succs: "succs i \<tau> pc \<noteq> []"  "succs i \<tau>' pc \<noteq> []"
  shows "P \<turnstile> eff\<^isub>i (i,P,\<tau>) \<le>\<^sub>i eff\<^isub>i (i,P,\<tau>')"
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
    case ThrowExc with succs have False by simp
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
    have "if is_native P (ST' ! n) M then \<exists>U Ts. P \<turnstile> rev (take n ST') [\<le>] Ts \<and> P \<turnstile> ST' ! n\<bullet>M(Ts) :: U
          else \<exists>D Ts T m C'. class_type_of (ST' ! n) = \<lfloor>D\<rfloor> \<and> P \<turnstile> D sees M:Ts \<rightarrow> T = m in C' \<and> P \<turnstile> rev (take n ST') [\<le>] Ts"
      by fastsimp
    moreover
    from less have "P \<turnstile> ST!n \<le> ST'!n"
      by(auto dest: list_all2_nthD2[OF _ n])
    { fix D Ts T m C'
      assume D: "class_type_of (ST' ! n) = \<lfloor>D\<rfloor>"
        and Ts: "P \<turnstile> rev (take n ST') [\<le>] Ts"
	and D_M: "P \<turnstile> D sees M: Ts\<rightarrow>T = m in C'"
	and nec: "\<not> is_native P (ST' ! n) M"

        from D `P \<turnstile> ST!n \<le> ST'!n` ST
        obtain D' where D': "class_type_of (ST ! n) = \<lfloor>D'\<rfloor>" 
          and DsubC: "P \<turnstile> D' \<preceq>\<^sup>* D"
          unfolding is_class_type_of_conv_class_type_of_Some[symmetric]
          by(rule widen_is_class_type_of)

      from wf D_M DsubC obtain Ts' T' m' C'' where
	D'_M: "P \<turnstile> D' sees M: Ts'\<rightarrow>T' = m' in C''" and
	Ts': "P \<turnstile> Ts [\<le>] Ts'" and "P \<turnstile> T' \<le> T" by (blast dest: sees_method_mono)


      have ?thesis
      proof(cases "is_native P (ST ! n) M")
        case False
        thus ?thesis using Invoke n D D' D_M less nec D'_M Ts' `P \<turnstile> T' \<le> T`
          by(auto intro: list_all2_dropI)
      next
        case True
        with D' D'_M obtain Ts'' Tr''
          where wtext: "P \<turnstile> ST ! n\<bullet>M(Ts'') :: Tr''" 
          and "P \<turnstile> Ts' [\<le>] Ts''" "P \<turnstile> Tr'' \<le> T'"
          unfolding is_class_type_of_conv_class_type_of_Some[symmetric]
          by(auto dest: is_native_sees_method_overriding[OF wf])
        from `P \<turnstile> Tr'' \<le> T'` `P \<turnstile> T' \<le> T` have "P \<turnstile> Tr'' \<le> T" by(rule widen_trans)
        from less have "P \<turnstile> rev (take n ST) [\<le>] rev (take n ST')" by simp
        also note Ts also note Ts' also note `P \<turnstile> Ts' [\<le>] Ts''`
        finally have "P \<turnstile> rev (take n ST) [\<le>] Ts''" .
        thus ?thesis using Invoke n D D' D_M less nec D'_M Ts' wtext `P \<turnstile> Tr'' \<le> T` `P \<turnstile> T' \<le> T`
          by(auto simp add: is_native_def2 elim!: external_WT.cases dest: native_call_fun)
      qed }
    moreover
    { fix Ts U
      assume nexc': "is_native P (ST' ! n) M"
	and wtext: "P \<turnstile> ST' ! n\<bullet>M(Ts) :: U"
        and sub: "P \<turnstile> rev (take n ST') [\<le>] Ts"

      from wtext obtain T' where native': "P \<turnstile> ST' ! n native M:Ts\<rightarrow>U in T'"
        unfolding is_native_def2 by(auto simp add: external_WT.simps)
      have ?thesis
      proof(cases "is_native P (ST ! n) M")
        case True
        then obtain Ts' Tr' T'
          where native: "P \<turnstile> ST ! n native M:Ts'\<rightarrow>Tr' in T'"
          unfolding is_native_def2 by blast
        hence "P \<turnstile> ST ! n\<bullet>M(Ts') :: Tr'" ..
        
        from less have "P \<turnstile> rev (take n ST) [\<le>] rev (take n ST')" by auto
        also note sub 
        also from native' native `P \<turnstile> ST!n \<le> ST'!n`
        have "P \<turnstile> Ts [\<le>] Ts'" by(rule native_native_overriding)
        finally have "P \<turnstile> rev (take n ST) [\<le>] Ts'" .
        moreover from native' native `P \<turnstile> ST!n \<le> ST'!n`
        have "P \<turnstile> Tr' \<le> U" by(rule native_native_overriding)
        ultimately show ?thesis using Invoke ST less nexc' wtext True native
          by(auto elim: external_WT.cases)
      next
        case False
        from native_not_native_overriding[OF wf native' this `P \<turnstile> ST ! n \<le> ST' ! n` ST]
        obtain C Ts' Tr' body D where "is_class_type_of (ST ! n) C"
          and "P \<turnstile> C sees M: Ts'\<rightarrow>Tr' = body in D"
          and "P \<turnstile> Ts [\<le>] Ts'" and "P \<turnstile> Tr' \<le> U" " P \<turnstile> Class C \<le> T'" by blast
        thus ?thesis using Invoke ST less nexc' False wtext
          by(auto simp add: is_class_type_of_conv_class_type_of_Some elim: external_WT.cases)
      qed }
    ultimately show ?thesis by(auto split: split_if_asm)
  next
    case ALoad with less app app\<^isub>i succs
    show ?thesis by(auto split: split_if_asm dest: Array_Array_widen)
  next
    case AStore with less app app\<^isub>i succs
    show ?thesis by(auto split: split_if_asm dest: Array_Array_widen)
  next
    case (BinOpInstr bop)
    with less app app\<^isub>i succs show ?thesis
      by auto(force dest: WTrt_binop_widen_mono WTrt_binop_fun)
  qed auto
qed

end
