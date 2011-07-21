(*  Title:      JinjaThreads/Compiler/J1Deadlock.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Deadlock perservation for the intermediate language} *}

theory J1Deadlock imports
  J1
  "../Framework/FWDeadlock"
begin

context J1_heap_base begin

lemma IUF_red_taD:
  "\<lbrakk> P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; IUF e ta e' \<rbrakk>
  \<Longrightarrow> \<exists>e' ta' s'. P,t \<turnstile>1 \<langle>e, s\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle> \<and> \<not> IUF e ta' e' \<and>
     collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<and> collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub> \<subseteq> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> \<and>
     (\<exists>s. Red1_mthr.actions_ok s t ta')"

  and IUFs_reds_taD:
  "\<lbrakk> P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; IUFs es ta es' \<rbrakk>
  \<Longrightarrow> \<exists>es' ta' s'. P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta'\<rightarrow>] \<langle>es', s'\<rangle> \<and> \<not> IUFs es ta' es' \<and>
     collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<and> collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub> \<subseteq> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> \<and>
     (\<exists>s. Red1_mthr.actions_ok s t ta')"
proof(induct rule: red1_reds1.inducts)
  case (Synchronized1Red2 e s ta e' s' V a)
  from `IUF (insync\<^bsub>V\<^esub> (a) e) ta (insync\<^bsub>V\<^esub> (a) e')` have "IUF e ta e'" by auto
  from Synchronized1Red2(2)[OF this] obtain e' ta' s'
    where "P,t \<turnstile>1 \<langle>e,s\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle>" "\<not> IUF e ta' e'" 
    and L: "collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<and> collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub> \<subseteq> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
    and aok: "\<exists>s. Red1_mthr.actions_ok s t ta'"
    by blast
  from `P,t \<turnstile>1 \<langle>e,s\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle>` have "P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) e, s\<rangle> -ta'\<rightarrow> \<langle>insync\<^bsub>V\<^esub> (a) e', s'\<rangle>"
    by(rule red1_reds1.Synchronized1Red2)
  moreover from `\<not> IUF e ta' e'` have "\<not> IUF (insync\<^bsub>V\<^esub> (a) e) ta' (insync\<^bsub>V\<^esub> (a) e')" by auto
  ultimately show ?case using L aok by blast
next
  case (Unlock1SynchronizedNull xs V a v)
  have "\<not> IUF (insync\<^bsub>V\<^esub> (a) Val v) \<epsilon> (THROW NullPointer)"
    by(auto simp add: expand_finfun_eq fun_eq_iff finfun_upd_apply ta_upd_simps split: split_if_asm)
  with `IUF (insync\<^bsub>V\<^esub> (a) Val v) \<epsilon> (THROW NullPointer)` show ?case by contradiction
next
  case (Unlock1SynchronizedFail xs V a' a v h)
  from `xs ! V = Addr a'` `V < length xs` 
  have "P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Val v,(h, xs)\<rangle> -\<lbrace>Unlock\<rightarrow>a', SyncUnlock a'\<rbrace>\<rightarrow> \<langle>Val v,(h, xs)\<rangle>"
    by(rule Unlock1Synchronized)
  thus ?case
    by(fastsimp simp add: collect_locks_def finfun_upd_apply ta_upd_simps lock_ok_las_def exI[where x="\<lambda>\<^isup>f \<lfloor>(t, 0)\<rfloor>"] split: split_if_asm)
next
  case (Synchronized1Throw2Fail xs V a' a ad h)
  from `xs ! V = Addr a'` `V < length xs`
  have "P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw ad, (h, xs)\<rangle> -\<lbrace>Unlock\<rightarrow>a', SyncUnlock a'\<rbrace>\<rightarrow> \<langle>Throw ad, (h, xs)\<rangle>"
    by(rule Synchronized1Throw2)
  thus ?case
    by(fastsimp simp add: collect_locks_def finfun_upd_apply ta_upd_simps lock_ok_las_def exI[where x="\<lambda>\<^isup>f \<lfloor>(t, 0)\<rfloor>"] split: split_if_asm)
next
  case (Synchronized1Throw2Null xs V a ad h)
  from `IUF (insync\<^bsub>V\<^esub> (a) Throw ad) \<epsilon> (THROW NullPointer)` have False
    by(auto simp add: expand_finfun_eq fun_eq_iff finfun_upd_apply ta_upd_simps split: split_if_asm)
  thus ?case ..
qed(fastsimp intro: red1_reds1.intros simp add: ta_upd_simps)+

lemma
  fixes e :: "('a, 'b, 'addr) exp" and es :: "('a, 'b, 'addr) exp list"
  and ta :: "('addr, 'thread_id, 'heap) external_thread_action"
  shows IUF_extTA2J1D: "IUF e (extTA2J1 P ta) e' \<Longrightarrow> IUF e ta e'"
  and IUFs_extTA2J1D: "IUFs es (extTA2J1 P ta) es' \<Longrightarrow> IUFs es ta es'"
apply(induct e ta'\<equiv>"extTA2J1 P ta" e' and es ta'\<equiv>"extTA2J1 P ta" es' rule: IUF_IUFs.inducts)
apply(auto simp add: ta_upd_simps)
apply(cases ta)
apply(auto dest: IUFFail simp add: ta_upd_simps)
done

lemma mred1'_mred1_must_sync_eq:
  "Red1'_mthr.must_sync P t x (shr s) = Red1_mthr.must_sync P t x (shr s)"
proof
  assume "Red1'_mthr.must_sync P t x (shr s)"
  thus "Red1_mthr.must_sync P t x (shr s)"
    by(rule Red1'_mthr.must_syncE)(rule Red1_mthr.must_syncI, auto simp add: split_def simp del: split_paired_Ex)
next
  assume "Red1_mthr.must_sync P t x (shr s)"
  thus "Red1'_mthr.must_sync P t x (shr s)"
    apply(rule Red1_mthr.must_syncE)
    apply(rule Red1'_mthr.must_syncI)
    apply(cases x)
    apply(auto simp add: split_def split_paired_Ex)
    apply(erule Red1.cases)
     apply auto
     apply(rename_tac e xs las tas was cas ias obs e' h' x' exs)
     apply(case_tac "IUF e (las, tas, was, cas, ias, obs) e'")
      apply(drule (1) IUF_red_taD)
      apply(clarsimp)
      apply(rule exI conjI)+
       apply(drule red1Red)
       apply fastsimp
      apply(rule conjI)
       apply(simp add: IUFL_def)
       apply(erule contrapos_nn)
       apply(rule IUF_extTA2J1D[where P=P])
       apply simp
      apply(thin_tac "final_thread.actions_ok ?final ?s ?t ?ta")
      apply(simp add: final_thread.actions_ok_iff split_def)
      apply blast
     apply(rule exI conjI)+
      apply(drule red1Red)
      apply fastsimp
     apply(rule conjI)
      apply(erule contrapos_nn)
      apply(rule IUF_extTA2J1D[where P=P])
      apply(simp add: IUFL_def)
     apply(fastsimp)
   apply(auto intro!: red1Call red1Return exI simp add: IUFL_def)
   done
qed

lemma Red1_Red1'_deadlock_inv:
  "Red1_mthr.deadlock P s = Red1'_mthr.deadlock P s"
proof(rule iffI)
  assume dead: "Red1_mthr.deadlock P s"
  show "Red1'_mthr.deadlock P s"
  proof(rule multithreaded_base.deadlockI)
    fix t x
    assume tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and nfin: "\<not> final_expr1 x"
      and wst: "wset s t = None"
    with dead obtain ms: "Red1_mthr.must_sync P t x (shr s)"
      and cs [rule_format]: "\<forall>LT. Red1_mthr.can_sync P t x (shr s) LT \<longrightarrow>
               (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s)))"
      by(rule Red1_mthr.deadlockD1)
    from ms[folded mred1'_mred1_must_sync_eq]
    show "Red1'_mthr.must_sync P t x (shr s) \<and>
             (\<forall>LT. Red1'_mthr.can_sync P t x (shr s) LT \<longrightarrow>
                   (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s))))"
    proof
      show "\<forall>LT. Red1'_mthr.can_sync P t x (shr s) LT \<longrightarrow>
         (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s)))"
      proof(intro strip)
	fix LT
	assume "Red1'_mthr.can_sync P t x (shr s) LT"
	then obtain ta x' m' where "mred1' P t (x, shr s) ta (x', m')" 
	  and [simp]: "LT = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> <+> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
	  by(rule Red1'_mthr.can_syncE)
	hence "mred1 P t (x, shr s) ta (x', m')" by(auto simp add: split_beta)
	hence "Red1_mthr.can_sync P t x (shr s) LT" by(rule Red1_mthr.can_syncI) simp
	thus "\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s))" by(rule cs)
      qed
    qed
  next
    fix t x ln l
    assume "thr s t = \<lfloor>(x, ln)\<rfloor>" "0 < ln\<^sub>f l" "\<not> waiting (wset s t)"
    thus "\<exists>l t'. 0 < ln\<^sub>f l \<and> t \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock ((locks s)\<^sub>f l) t'"
      by(rule Red1_mthr.deadlockD2[OF dead]) blast
  next
    fix t x w
    assume "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    thus "wset s t \<noteq> \<lfloor>PostWS w\<rfloor>"
      by(rule Red1_mthr.deadlockD3[OF dead, rule_format])
  qed
next
  assume dead: "Red1'_mthr.deadlock P s"
  show "Red1_mthr.deadlock P s"
  proof(rule Red1_mthr.deadlockI)
    fix t x
    assume tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and nfin: "\<not> final_expr1 x"
      and wst: "wset s t = None"
    with dead obtain ms: "Red1'_mthr.must_sync P t x (shr s)"
      and cs [rule_format]: "\<forall>LT. Red1'_mthr.can_sync P t x (shr s) LT \<longrightarrow>
               (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s)))"
      by(rule Red1'_mthr.deadlockD1)
    from ms[unfolded mred1'_mred1_must_sync_eq]
    show "Red1_mthr.must_sync P t x (shr s) \<and>
             (\<forall>LT. Red1_mthr.can_sync P t x (shr s) LT \<longrightarrow>
                   (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s))))"
    proof
      show "\<forall>LT. Red1_mthr.can_sync P t x (shr s) LT \<longrightarrow>
         (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s)))"
      proof(intro strip)
	fix LT
	assume "Red1_mthr.can_sync P t x (shr s) LT"
	then obtain ta x' m' where "mred1 P t (x, shr s) ta (x', m')" 
	  and [simp]: "LT = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> <+> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
	  by(rule Red1_mthr.can_syncE)
	then obtain e xs exs e' xs' exs' where x [simp]: "x = ((e, xs), exs)" "x' = ((e', xs'), exs')"
	  and red: "P,t \<turnstile>1 \<langle>(e, xs)/exs, shr s\<rangle> -ta\<rightarrow> \<langle>(e', xs')/exs', m'\<rangle>" by(cases x, cases x') fastsimp
	moreover have "\<not> IUFL (e, xs) exs ta (e', xs') exs'"
	proof
	  assume "IUFL (e, xs) exs ta (e', xs') exs'"
	  hence "IUF e ta e'" and [simp]: "exs' = exs" by(auto simp add: IUFL_def)
	  then obtain l where ta: "ta = \<lbrace>UnlockFail \<rightarrow>l\<rbrace>" by(auto dest: IUF_taD)
	  hence "LT = {}" by(auto simp add: finfun_upd_apply collect_locks_def collect_interrupts_def)
	  from red ta have red: "P,t \<turnstile>1 \<langle>e, (shr s, xs)\<rangle> -\<lbrace>UnlockFail \<rightarrow>l\<rbrace>\<rightarrow> \<langle>e', (m', xs')\<rangle>"
	    by(auto elim: Red1.cases simp add: ta_upd_simps)
	  { fix es es' :: "'addr expr1 list"
	    have "IUF e ta e' \<Longrightarrow> IUF e (\<lbrace>UnlockFail \<rightarrow>l\<rbrace> :: ('addr, 'thread_id, 'heap) external_thread_action) e'"
	      and "IUFs es ta es' \<Longrightarrow> IUFs es (\<lbrace>UnlockFail \<rightarrow>l\<rbrace> :: ('addr, 'thread_id, 'heap) external_thread_action) es'"
	      by(induct rule: IUF_IUFs.inducts)(auto dest: IUFFail)
	    with `IUF e ta e'` have "IUF e (\<lbrace>UnlockFail \<rightarrow>l\<rbrace> :: ('addr, 'thread_id, 'heap) external_thread_action) e'"
              by blast }
	  from IUF_red_taD[OF red this] obtain e' ta' s'
	    where "P,t \<turnstile>1 \<langle>e,(shr s, xs)\<rangle> -ta'\<rightarrow> \<langle>e',(fst s', snd s')\<rangle>" "\<not> IUF e ta' e'"
	    and L: "collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>\<lbrace>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>l\<^esub>" "set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> set \<lbrace>\<lbrace>UnlockFail\<rightarrow>l\<rbrace>\<rbrace>\<^bsub>c\<^esub>" "collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub> \<subseteq> collect_interrupts \<lbrace>\<lbrace>(UnlockFail, l)\<rbrace>\<rbrace>\<^bsub>i\<^esub>"
	    by auto
	  let ?LT' = "collect_locks \<lbrace>extTA2J1 P ta'\<rbrace>\<^bsub>l\<^esub> <+> collect_cond_actions \<lbrace>extTA2J1 P ta'\<rbrace>\<^bsub>c\<^esub> <+> collect_interrupts \<lbrace>extTA2J1 P ta'\<rbrace>\<^bsub>i\<^esub>"
	  from `P,t \<turnstile>1 \<langle>e,(shr s, xs)\<rangle> -ta'\<rightarrow> \<langle>e',(fst s', snd s')\<rangle>`
	  have "P,t \<turnstile>1 \<langle>(e, xs)/exs, shr s\<rangle> -extTA2J1 P ta'\<rightarrow> \<langle>(e', snd s')/exs, fst s'\<rangle>" by(rule red1Red)
	  moreover from `\<not> IUF e ta' e'` have "\<not> IUF e (extTA2J1 P ta') e'" by auto
	  ultimately have "mred1' P t (((e, xs), exs), shr s) (extTA2J1 P ta') (((e', snd s'), exs), fst s')"
	    by(auto simp add: IUFL_def)
	  hence "Red1'_mthr.can_sync P t x (shr s) ?LT'" unfolding x
	    by(rule Red1'_mthr.can_syncI) simp
	  from cs[OF this] L show False
            by(auto elim!: final_thread.must_wait.cases simp add: collect_locks_def finfun_upd_apply collect_interrupts_def split: split_if_asm)
	qed
	ultimately have "mred1' P t (((e, xs), exs), shr s) ta (((e', xs'), exs'), m')" by auto
	hence "Red1'_mthr.can_sync P t x (shr s) LT" unfolding x
	  by(rule Red1'_mthr.can_syncI) simp
	thus "\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s))" by(rule cs)
      qed
    qed
  next
    fix t x ln l
    assume "thr s t = \<lfloor>(x, ln)\<rfloor>" "0 < ln\<^sub>f l" "\<not> waiting (wset s t)"
    thus "\<exists>l t'. 0 < ln\<^sub>f l \<and> t \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock ((locks s)\<^sub>f l) t'"
      by(rule Red1'_mthr.deadlockD2[OF dead]) blast
  next
    fix t x w
    assume "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    thus "wset s t \<noteq> \<lfloor>PostWS w\<rfloor>"
      by(rule Red1'_mthr.deadlockD3[OF dead, rule_format])
  qed
qed

end

end