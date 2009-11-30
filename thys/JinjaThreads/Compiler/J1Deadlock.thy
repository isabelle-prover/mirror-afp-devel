theory J1Deadlock imports
  Correctness1Threaded
  "../Framework/FWDeadlock"
begin

lemma IUF_red_taD:
  "\<lbrakk> P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; IUF e ta e' \<rbrakk>
  \<Longrightarrow> \<exists>e' ta' s'. P \<turnstile>1 \<langle>e, s\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle> \<and> \<not> IUF e ta' e' \<and>
     collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"

  and IUFs_reds_taD:
  "\<lbrakk> P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; IUFs es ta es' \<rbrakk>
  \<Longrightarrow> \<exists>es' ta' s'. P \<turnstile>1 \<langle>es, s\<rangle> [-ta'\<rightarrow>] \<langle>es', s'\<rangle> \<and> \<not> IUFs es ta' es' \<and>
     collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
proof(induct rule: red1_reds1.inducts)
  case (Synchronized1Red2 e s ta e' s' V a)
  from `IUF (insync\<^bsub>V\<^esub> (a) e) ta (insync\<^bsub>V\<^esub> (a) e')` have "IUF e ta e'" by auto
  from Synchronized1Red2(2)[OF this] obtain e' ta' s'
    where "P \<turnstile>1 \<langle>e,s\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle>" "\<not> IUF e ta' e'" 
    and L: "collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" by blast
  from `P \<turnstile>1 \<langle>e,s\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle>` have "P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) e, s\<rangle> -ta'\<rightarrow> \<langle>insync\<^bsub>V\<^esub> (a) e', s'\<rangle>"
    by(rule red1_reds1.Synchronized1Red2)
  moreover from `\<not> IUF e ta' e'` have "\<not> IUF (insync\<^bsub>V\<^esub> (a) e) ta' (insync\<^bsub>V\<^esub> (a) e')" by auto
  ultimately show ?case using L by blast
next
  case (Unlock1SynchronizedNull xs V a v)
  have "\<not> IUF (insync\<^bsub>V\<^esub> (a) Val v) \<epsilon> (THROW NullPointer)"
    by(auto simp add: expand_finfun_eq expand_fun_eq finfun_upd_apply split: split_if_asm)
  with `IUF (insync\<^bsub>V\<^esub> (a) Val v) \<epsilon> (THROW NullPointer)` show ?case by contradiction
next
  case (Unlock1SynchronizedFail xs V a' a v h)
  from `xs ! V = Addr a'` `V < length xs` 
  have "P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Val v,(h, xs)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a'\<rbrace>\<lbrace>\<^bsub>o\<^esub>Synchronization a'\<rbrace>\<rightarrow> \<langle>Val v,(h, xs)\<rangle>"
    by(rule Unlock1Synchronized)
  thus ?case by(auto intro!: exI simp add: collect_locks_def finfun_upd_apply split: split_if_asm)
next
  case (Synchronized1Throw2Fail xs V a' a ad h)
  from `xs ! V = Addr a'` `V < length xs`
  have "P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw ad, (h, xs)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a' \<rbrace>\<lbrace>\<^bsub>o\<^esub> Synchronization a'\<rbrace>\<rightarrow> \<langle>Throw ad, (h, xs)\<rangle>"
    by(rule Synchronized1Throw2)
  thus ?case by(auto intro!: exI simp add: collect_locks_def finfun_upd_apply split: split_if_asm)
next
  case (Synchronized1Throw2Null xs V a ad h)
  from `IUF (insync\<^bsub>V\<^esub> (a) Throw ad) \<epsilon> (THROW NullPointer)` have False
    by(auto simp add: expand_finfun_eq expand_fun_eq finfun_upd_apply split: split_if_asm)
  thus ?case ..
qed(fastsimp intro: red1_reds1.intros)+

lemma
  fixes e :: "('a, 'b) exp" and es :: "('a, 'b) exp list" and ta :: external_thread_action
  shows IUF_extTA2J1D: "IUF e (extTA2J1 P ta) e' \<Longrightarrow> IUF e ta e'"
  and IUFs_extTA2J1D: "IUFs es (extTA2J1 P ta) es' \<Longrightarrow> IUFs es ta es'"
apply(induct e ta'\<equiv>"extTA2J1 P ta" e' and es ta'\<equiv>"extTA2J1 P ta" es' rule: IUF_IUFs.inducts)
apply(auto)
apply(cases ta)
apply(auto dest: IUFFail)
done

lemma mred1'_mred1_must_sync_eq:
  "multithreaded_base.must_sync (mred1' P) x (shr s) = multithreaded_base.must_sync (mred1 P) x (shr s)"
apply(auto)
 apply(erule multithreaded_base.must_syncE)
 apply(rule multithreaded_base.must_syncI)
 apply(fastsimp simp add: split_def)
apply(rule multithreaded_base.must_syncI)
apply(erule multithreaded_base.must_syncE)
apply(auto simp add: split_def)
apply(erule Red1.cases)
  apply auto
  apply(rename_tac e xs las tas was cas obs e' h' x')
  apply(case_tac "IUF e (las, tas, was, cas, obs) e'")
   apply(drule (1) IUF_red_taD)
   apply clarify
   apply(rule exI conjI)+
    apply(drule red1Red)
    apply fastsimp
   apply(simp add: IUFL_def)
   apply(erule contrapos_nn)
   apply(rule IUF_extTA2J1D[where P=P])
   apply simp
  apply(rule exI conjI)+
   apply(drule red1Red)
   apply simp
  apply(erule contrapos_nn)
  apply(rule IUF_extTA2J1D[where P=P])
  apply(simp add: IUFL_def)
 apply(rule exI conjI)+
  apply(erule (4) red1Call)
 apply(simp add: IUFL_def)
apply(rule exI conjI)+
 apply(erule red1Return)
apply(simp add: IUFL_def)
done

lemma Red1_Red1'_deadlock_inv:
  "multithreaded_base.deadlock final_expr1 (mred1 P) s = multithreaded_base.deadlock final_expr1 (mred1' P) s"
proof(rule iffI)
  assume dead: "multithreaded_base.deadlock final_expr1 (mred1 P) s"
  then obtain t where "final_thread.not_final_thread final_expr1 s t"
    by(auto simp add: multithreaded_base.deadlock_def)
  thus "multithreaded_base.deadlock final_expr1 (mred1' P) s"
  proof(rule final_thread_wf.deadlockI[OF Red1'_mthr.final_thread_wf_axioms])
    fix t x
    assume tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and nfin: "\<not> final_expr1 x"
      and wst: "wset s t = None"
    with dead obtain ms: "multithreaded_base.must_sync (mred1 P) x (shr s)"
      and cs: "\<forall>LT. multithreaded_base.can_sync (mred1 P) x (shr s) LT \<longrightarrow>
               (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt t'))"
      by(rule final_thread_wf.deadlockD1[OF Red1_mthr.final_thread_wf_axioms])
    from cs have cs: "\<And>LT. multithreaded_base.can_sync (mred1 P) x (shr s) LT \<Longrightarrow> \<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt t')" by blast
    from ms[folded mred1'_mred1_must_sync_eq]
    show "multithreaded_base.must_sync (mred1' P) x (shr s) \<and>
             (\<forall>LT. multithreaded_base.can_sync (mred1' P) x (shr s) LT \<longrightarrow>
                   (\<exists>t'. thr s t' \<noteq> None \<and>
                         (\<exists>lt\<in>LT.
                             final_thread.must_wait final_expr1 s t lt t')))"
    proof
      show "\<forall>LT. multithreaded_base.can_sync (mred1' P) x (shr s) LT \<longrightarrow>
         (\<exists>t'. thr s t' \<noteq> None \<and>
               (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt t'))"
      proof(intro strip)
	fix LT
	assume "multithreaded_base.can_sync (mred1' P) x (shr s) LT"
	then obtain ta x' m' where "mred1' P (x, shr s) ta (x', m')" 
	  and [simp]: "LT = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>}"
	  by(rule multithreaded_base.can_syncE)
	hence "mred1 P (x, shr s) ta (x', m')" by(auto simp add: split_beta)
	hence "multithreaded_base.can_sync (mred1 P) x (shr s) LT" by(rule multithreaded_base.can_syncI) simp
	thus "\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt t')" by(rule cs)
      qed
    qed
  next
    fix t x ln l
    assume "thr s t = \<lfloor>(x, ln)\<rfloor>" "0 < ln\<^sub>f l" "wset s t = None"
    thus "\<exists>l t'. 0 < ln\<^sub>f l \<and> t \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock ((locks s)\<^sub>f l) t'"
      by(rule final_thread_wf.deadlockD2[OF Red1_mthr.final_thread_wf_axioms dead]) blast
  qed
next
  assume dead: "multithreaded_base.deadlock final_expr1 (mred1' P) s"
  then obtain t where "final_thread.not_final_thread final_expr1 s t"
    by(auto simp add: multithreaded_base.deadlock_def)
  thus "multithreaded_base.deadlock final_expr1 (mred1 P) s"
  proof(rule final_thread_wf.deadlockI[OF Red1_mthr.final_thread_wf_axioms])
    fix t x
    assume tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and nfin: "\<not> final_expr1 x"
      and wst: "wset s t = None"
    with dead obtain ms: "multithreaded_base.must_sync (mred1' P) x (shr s)"
      and cs [rule_format]: "\<forall>LT. multithreaded_base.can_sync (mred1' P) x (shr s) LT \<longrightarrow>
               (\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt t'))"
      by(rule final_thread_wf.deadlockD1[OF Red1'_mthr.final_thread_wf_axioms])
    from ms[unfolded mred1'_mred1_must_sync_eq]
    show "multithreaded_base.must_sync (mred1 P) x (shr s) \<and>
             (\<forall>LT. multithreaded_base.can_sync (mred1 P) x (shr s) LT \<longrightarrow>
                   (\<exists>t'. thr s t' \<noteq> None \<and>
                         (\<exists>lt\<in>LT.
                             final_thread.must_wait final_expr1 s t lt t')))"
    proof
      show "\<forall>LT. multithreaded_base.can_sync (mred1 P) x (shr s) LT \<longrightarrow>
         (\<exists>t'. thr s t' \<noteq> None \<and>
               (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt t'))"
      proof(intro strip)
	fix LT
	assume "multithreaded_base.can_sync (mred1 P) x (shr s) LT"
	then obtain ta x' m' where "mred1 P (x, shr s) ta (x', m')" 
	  and [simp]: "LT = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>}"
	  by(rule multithreaded_base.can_syncE)
	then obtain e xs exs e' xs' exs' where x [simp]: "x = ((e, xs), exs)" "x' = ((e', xs'), exs')"
	  and red: "P \<turnstile>1 \<langle>(e, xs)/exs, shr s\<rangle> -ta\<rightarrow> \<langle>(e', xs')/exs', m'\<rangle>" by(cases x, cases x') fastsimp
	moreover have "\<not> IUFL (e, xs) exs ta (e', xs') exs'"
	proof
	  assume "IUFL (e, xs) exs ta (e', xs') exs'"
	  hence "IUF e ta e'" and [simp]: "exs' = exs" by(auto simp add: IUFL_def)
	  then obtain l where ta: "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail \<rightarrow>l\<rbrace>" by(auto dest: IUF_taD)
	  hence "LT = {}" by(auto simp add: finfun_upd_apply collect_locks_def)
	  from red ta have red: "P \<turnstile>1 \<langle>e, (shr s, xs)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail \<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', (m', xs')\<rangle>"
	    by(auto elim: Red1.cases)
	  { fix es es' :: "expr1 list"
	    have "IUF e ta e' \<Longrightarrow> IUF e (\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail \<rightarrow>l\<rbrace> :: external_thread_action) e'"
	      and "IUFs es ta es' \<Longrightarrow> IUFs es (\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail \<rightarrow>l\<rbrace> :: external_thread_action) es'"
	    by(induct rule: IUF_IUFs.inducts)(auto dest: IUFFail)
	    with `IUF e ta e'` have "IUF e (\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail \<rightarrow>l\<rbrace> :: external_thread_action) e'" by blast }
	  from IUF_red_taD[OF red this] obtain e' ta' s'
	    where "P \<turnstile>1 \<langle>e,(shr s, xs)\<rangle> -ta'\<rightarrow> \<langle>e',(fst s', snd s')\<rangle>" "\<not> IUF e ta' e'"
	    and L: "collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>l\<^esub>" "set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> set \<lbrace>\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>c\<^esub>"
	    by auto
	  let ?LT' = "collect_locks \<lbrace>extTA2J1 P ta'\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>extTA2J1 P ta'\<rbrace>\<^bsub>c\<^esub>}"
	  from `P \<turnstile>1 \<langle>e,(shr s, xs)\<rangle> -ta'\<rightarrow> \<langle>e',(fst s', snd s')\<rangle>`
	  have "P \<turnstile>1 \<langle>(e, xs)/exs, shr s\<rangle> -extTA2J1 P ta'\<rightarrow> \<langle>(e', snd s')/exs, fst s'\<rangle>" by(rule red1Red)
	  moreover from `\<not> IUF e ta' e'` have "\<not> IUF e (extTA2J1 P ta') e'" by auto
	  ultimately have "mred1' P (((e, xs), exs), shr s) (extTA2J1 P ta') (((e', snd s'), exs), fst s')"
	    by(auto simp add: IUFL_def)
	  hence "multithreaded_base.can_sync (mred1' P) x (shr s) ?LT'" unfolding x
	    by(rule multithreaded_base.can_syncI) simp
	  from cs[OF this] L show False
	    by(auto elim!: final_thread.must_wait.cases simp add: collect_locks_def finfun_upd_apply split: split_if_asm)
	qed
	ultimately have "mred1' P (((e, xs), exs), shr s) ta (((e', xs'), exs'), m')" by auto
	hence "multithreaded_base.can_sync (mred1' P) x (shr s) LT" unfolding x
	  by(rule multithreaded_base.can_syncI) simp
	thus "\<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt t')" by(rule cs)
      qed
    qed
  next
    fix t x ln l
    assume "thr s t = \<lfloor>(x, ln)\<rfloor>" "0 < ln\<^sub>f l" "wset s t = None"
    thus "\<exists>l t'. 0 < ln\<^sub>f l \<and> t \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock ((locks s)\<^sub>f l) t'"
      by(rule final_thread_wf.deadlockD2[OF Red1'_mthr.final_thread_wf_axioms dead]) blast
  qed
qed


end