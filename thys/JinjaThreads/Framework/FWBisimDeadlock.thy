(*  Title:      JinjaThreads/Framework/FWBisimDeadlock.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Preservation of deadlock across bisimulations} *}

theory FWBisimDeadlock imports FWBisimulation FWDeadlock begin

context FWdelay_bisimulation_diverge begin

lemma no_\<tau>move1_\<tau>s_to_no_\<tau>move2:
  assumes "t \<turnstile> (x1, m1) \<approx> (x2, m2)"
  and no_\<tau>moves: "\<And>x1' m1'. \<not> r1.silent_move t (x1, m1) (x1', m1')"
  shows "\<exists>x2' m2'. r2.silent_moves t (x2, m2) (x2', m2') \<and> 
                  (\<forall>x2'' m2''. \<not> r2.silent_move t (x2', m2') (x2'', m2'')) \<and> t \<turnstile> (x1, m1) \<approx> (x2', m2')"
proof -
  def x2m2 == "(x2, m2)"
  have "\<not> r1.\<tau>diverge t (x1, m1)"
  proof
    assume "r1.\<tau>diverge t (x1, m1)"
    then obtain x1' m1' where "r1.silent_move t (x1, m1) (x1', m1')" by cases auto
    with no_\<tau>moves[of x1' m1'] show False by contradiction
  qed
  with `t \<turnstile> (x1, m1) \<approx> (x2, m2)` have "\<not> r2.\<tau>diverge t (x2, m2)" by(simp add: \<tau>diverge_bisim_inv)
  from r2.not_\<tau>diverge_to_no_\<tau>move[OF this] obtain x2' m2'
    where "r2.silent_moves t (x2, m2) (x2', m2')" 
    and "\<forall>x2'' m2''. \<not> r2.silent_move t (x2', m2') (x2'', m2'')" by auto
  moreover from simulation_silents2[OF `t \<turnstile> (x1, m1) \<approx> (x2, m2)` `r2.silent_moves t (x2, m2) (x2', m2')`]
  obtain x1' m1' where "r1.silent_moves t (x1, m1) (x1', m1')" "t \<turnstile> (x1', m1') \<approx> (x2', m2')" by auto
  from `r1.silent_moves t (x1, m1) (x1', m1')` no_\<tau>moves
  have "x1' = x1" "m1' = m1" by(auto elim: converse_rtranclpE)
  ultimately show ?thesis using `t \<turnstile> (x1', m1') \<approx> (x2', m2')` by blast
qed

lemma no_\<tau>move2_\<tau>s_to_no_\<tau>move1:
  "\<lbrakk> t \<turnstile> (x1, m1) \<approx> (x2, m2); \<And>x2' m2'. \<not> r2.silent_move t (x2, m2) (x2', m2') \<rbrakk>
  \<Longrightarrow> \<exists>x1' m1'. r1.silent_moves t (x1, m1) (x1', m1') \<and> 
               (\<forall>x1'' m1''. \<not> r1.silent_move t (x1', m1') (x1'', m1'')) \<and> t \<turnstile> (x1', m1') \<approx> (x2, m2)"
using FWdelay_bisimulation_diverge.no_\<tau>move1_\<tau>s_to_no_\<tau>move2[OF FWdelay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma no_\<tau>Move1_\<tau>s_to_no_\<tau>Move2:
  fixes no_\<tau>moves1 no_\<tau>moves2
  defines "no_\<tau>moves1 \<equiv> \<lambda>s1 t. wset s1 t = None \<and> (\<exists>x. thr s1 t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> (\<forall>x' m'. \<not> r1.silent_move t (x, shr s1) (x', m')))"
  defines "no_\<tau>moves2 \<equiv> \<lambda>s2 t. wset s2 t = None \<and> (\<exists>x. thr s2 t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> (\<forall>x' m'. \<not> r2.silent_move t (x, shr s2) (x', m')))"
  assumes mbisim: "s1 \<approx>m (ls2, (ts2, m2), ws2)"
  
  shows "\<exists>ts2'. r2.mthr.silent_moves (ls2, (ts2, m2), ws2) (ls2, (ts2', m2), ws2) \<and> 
                (\<forall>t. no_\<tau>moves1 s1 t \<longrightarrow> no_\<tau>moves2 (ls2, (ts2', m2), ws2) t) \<and> s1 \<approx>m (ls2, (ts2', m2), ws2)"
proof -
  from mbisim have "finite (dom (thr s1))" by(simp add: mbisim_def)
  hence "finite {t. no_\<tau>moves1 s1 t}" unfolding no_\<tau>moves1_def
    by-(rule finite_subset, auto)
  thus ?thesis using `s1 \<approx>m (ls2, (ts2, m2), ws2)`
  proof(induct A\<equiv>"{t. no_\<tau>moves1 s1 t}" arbitrary: s1 ts2 rule: finite_induct)
    case empty
    from `{} = {t. no_\<tau>moves1 s1 t}`[symmetric] have "no_\<tau>moves1 s1 = (\<lambda>t. False)"
      by(auto intro: ext simp add: mem_def)
    thus ?case using `s1 \<approx>m (ls2, (ts2, m2), ws2)` by auto
  next
    case (insert t A)
    note mbisim = `s1 \<approx>m (ls2, (ts2, m2), ws2)`
    from `insert t A = {t. no_\<tau>moves1 s1 t}`
    have "no_\<tau>moves1 s1 t" by auto
    then obtain x1 where ts1t: "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>"
      and ws1t: "wset s1 t = None"
      and \<tau>1: "\<And>x1' m1'. \<not> r1.silent_move t (x1, shr s1) (x1', m1')"
      by(auto simp add: no_\<tau>moves1_def)

    from ts1t mbisim obtain x2 where ts2t: "ts2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>"
      and "t \<turnstile> (x1, shr s1) \<approx> (x2, m2)" by(auto dest: mbisim_thrD1)
    from mbisim ws1t have "ws2 t = None" by(simp add: mbisim_def)

    let ?s1 = "(locks s1, ((thr s1)(t := None), shr s1), wset s1)"
    let ?s2 = "(ls2, (ts2(t := None), m2), ws2)"
    from `insert t A = {t. no_\<tau>moves1 s1 t}` `t \<notin> A`
    have A: "A = {t. no_\<tau>moves1 ?s1 t}" by(auto simp add: no_\<tau>moves1_def)
    have "?s1 \<approx>m ?s2"
    proof(rule mbisimI)
      from mbisim show "finite (dom (thr ?s1))" "locks ?s1 = locks ?s2" "wset ?s1 = wset ?s2"
	by(simp_all add: mbisim_def)
    next
      from mbisim_wset_thread_ok1[OF mbisim] ws1t show "wset_thread_ok (wset ?s1) (thr ?s1)"
        by(auto intro!: wset_thread_okI dest: wset_thread_okD split: split_if_asm)
    next
      fix t'
      assume "thr ?s1 t' = None"
      with mbisim_thrNone_eq[OF mbisim, of t']
      show "thr ?s2 t' = None" by auto
    next
      fix t' x1 ln
      assume "thr ?s1 t' = \<lfloor>(x1, ln)\<rfloor>"
      hence "thr s1 t' = \<lfloor>(x1, ln)\<rfloor>" "t' \<noteq> t" by(auto split: split_if_asm)
      with mbisim_thrD1[OF mbisim `thr s1 t' = \<lfloor>(x1, ln)\<rfloor>`] mbisim
      show "\<exists>x2. thr ?s2 t' = \<lfloor>(x2, ln)\<rfloor> \<and> t' \<turnstile> (x1, shr ?s1) \<approx> (x2, shr ?s2) \<and> (wset ?s2 t' = None \<or> x1 \<approx>w x2)"
        by(auto simp add: mbisim_def)
    qed
    with A have "\<exists>ts2'. r2.mthr.silent_moves ?s2 (ls2, (ts2', m2), ws2) \<and> (\<forall>t. no_\<tau>moves1 ?s1 t \<longrightarrow> no_\<tau>moves2 (ls2, (ts2', m2), ws2) t) \<and> ?s1 \<approx>m (ls2, (ts2', m2), ws2)" by(rule insert)
    then obtain ts2' where "r2.mthr.silent_moves ?s2 (ls2, (ts2', m2), ws2)"
      and no_\<tau>: "\<And>t. no_\<tau>moves1 ?s1 t \<Longrightarrow> no_\<tau>moves2 (ls2, (ts2', m2), ws2) t"
      and "?s1 \<approx>m (ls2, (ts2', m2), ws2)" by auto
    let ?s2' = "(ls2, (ts2'(t \<mapsto> (x2, no_wait_locks)), m2), ws2)"
    from ts2t have "ts2(t \<mapsto> (x2, no_wait_locks)) = ts2" by(auto intro: ext)
    with r2.\<tau>mRedT_add_thread_inv[OF `r2.mthr.silent_moves ?s2 (ls2, (ts2', m2), ws2)`, of t "(x2, no_wait_locks)"]
    have "r2.mthr.silent_moves (ls2, (ts2, m2), ws2) ?s2'" by simp
    from no_\<tau>move1_\<tau>s_to_no_\<tau>move2[OF `t \<turnstile> (x1, shr s1) \<approx> (x2, m2)` \<tau>1]
    obtain x2' m2' where "r2.silent_moves t (x2, m2) (x2', m2')" 
      and "\<And>x2'' m2''. \<not> r2.silent_move t (x2', m2') (x2'', m2'')" 
      and "t \<turnstile> (x1, shr s1) \<approx> (x2', m2')" by blast
    let ?s2'' = "(ls2, (ts2'(t \<mapsto> (x2', no_wait_locks)), m2'), ws2)"
    from red2_rtrancl_\<tau>_heapD[OF `r2.silent_moves t (x2, m2) (x2', m2')` `t \<turnstile> (x1, shr s1) \<approx> (x2, m2)`]
    have "m2' = m2" by simp
    with `r2.silent_moves t (x2, m2) (x2', m2')` have "r2.silent_moves t (x2, shr ?s2') (x2', m2)" by simp
    hence "r2.mthr.silent_moves ?s2' (redT_upd ?s2' t \<epsilon> x2' m2)"
      by(rule red2_rtrancl_\<tau>_into_RedT_\<tau>)(auto simp add: `ws2 t = None` intro: `t \<turnstile> (x1, shr s1) \<approx> (x2, m2)`)
    also have "redT_upd ?s2' t \<epsilon> x2' m2 = ?s2''" using `m2' = m2`
      by(auto simp add: ext_iff redT_updLns_def finfun_Diag_const2 o_def)
    finally have "r2.mthr.silent_moves (ls2, (ts2, m2), ws2) ?s2''" 
      using `r2.mthr.silent_moves (ls2, (ts2, m2), ws2) ?s2'` by-(rule rtranclp_trans)
    moreover {
      fix t'
      assume no_\<tau>1: "no_\<tau>moves1 s1 t'"
      have "no_\<tau>moves2 ?s2'' t'"
      proof(cases "t' = t")
	case True thus ?thesis
	  using `ws2 t = None` `\<And>x2'' m2''. \<not> r2.silent_move t (x2', m2') (x2'', m2'')` by(simp add: no_\<tau>moves2_def)
      next
	case False
	with no_\<tau>1 have "no_\<tau>moves1 ?s1 t'" by(simp add: no_\<tau>moves1_def)
	hence "no_\<tau>moves2 (ls2, (ts2', m2), ws2) t'"
	  by(rule `no_\<tau>moves1 ?s1 t' \<Longrightarrow> no_\<tau>moves2 (ls2, (ts2', m2), ws2) t'`)
	with False `m2' = m2` show ?thesis by(simp add: no_\<tau>moves2_def)
      qed }
    moreover have "s1 \<approx>m ?s2''"
    proof(rule mbisimI)
      from mbisim show "finite (dom (thr s1))" "locks s1 = locks ?s2''" "wset s1 = wset ?s2''"
        by(simp_all add: mbisim_def)
    next
      from mbisim show "wset_thread_ok (wset s1) (thr s1)" by(rule mbisim_wset_thread_ok1)
    next
      fix t'
      assume "thr s1 t' = None"
      hence "thr ?s1 t' = None" "t' \<noteq> t" using ts1t by auto
      with mbisim_thrNone_eq[OF `?s1 \<approx>m (ls2, (ts2', m2), ws2)`, of t']
      show "thr ?s2'' t' = None" by simp
    next
      fix t' x1' ln'
      assume "thr s1 t' = \<lfloor>(x1', ln')\<rfloor>"
      show "\<exists>x2. thr ?s2'' t' = \<lfloor>(x2, ln')\<rfloor> \<and> t' \<turnstile> (x1', shr s1) \<approx> (x2, shr ?s2'') \<and> (wset ?s2'' t' = None \<or> x1' \<approx>w x2)"
      proof(cases "t = t'")
	case True
	with `thr s1 t' = \<lfloor>(x1', ln')\<rfloor>` ts1t `t \<turnstile> (x1, shr s1) \<approx> (x2', m2')` `m2' = m2` `ws2 t = None`
	show ?thesis by auto
      next
	case False
	with mbisim_thrD1[OF `?s1 \<approx>m (ls2, (ts2', m2), ws2)`, of t' x1' ln'] `thr s1 t' = \<lfloor>(x1', ln')\<rfloor>` `m2' = m2` mbisim
	show ?thesis by(auto simp add: mbisim_def)
      qed
    qed
    ultimately show ?case unfolding `m2' = m2` by blast
  qed
qed

lemma no_\<tau>Move2_\<tau>s_to_no_\<tau>Move1:
  fixes no_\<tau>moves1 no_\<tau>moves2
  defines "no_\<tau>moves1 \<equiv> \<lambda>s1 t. wset s1 t = None \<and> (\<exists>x. thr s1 t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> (\<forall>x' m'. \<not> r1.silent_move t (x, shr s1) (x', m')))"
  defines "no_\<tau>moves2 \<equiv> \<lambda>s2 t. wset s2 t = None \<and> (\<exists>x. thr s2 t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> (\<forall>x' m'. \<not> r2.silent_move t (x, shr s2) (x', m')))"
  assumes "(ls1, (ts1, m1), ws1) \<approx>m s2"
  
  shows "\<exists>ts1'. r1.mthr.silent_moves (ls1, (ts1, m1), ws1) (ls1, (ts1', m1), ws1) \<and>
                (\<forall>t. no_\<tau>moves2 s2 t \<longrightarrow> no_\<tau>moves1 (ls1, (ts1', m1), ws1) t) \<and> (ls1, (ts1', m1), ws1) \<approx>m s2"
using assms FWdelay_bisimulation_diverge.no_\<tau>Move1_\<tau>s_to_no_\<tau>Move2[OF FWdelay_bisimulation_diverge_flip]
unfolding flip_simps by blast

lemma deadlock_mbisim_not_final_thread_pres:
  assumes dead: "r1.deadlocked s1 t \<or> r1.deadlock s1"
  and nfin: "r1.not_final_thread s1 t"
  and fin: "r1.final_thread s1 t \<Longrightarrow> r2.final_thread s2 t"
  and mbisim: "s1 \<approx>m s2"
  shows "r2.not_final_thread s2 t"
proof -
  from nfin obtain x1 ln where "thr s1 t = \<lfloor>(x1, ln)\<rfloor>" by cases auto
  with mbisim obtain x2 where "thr s2 t = \<lfloor>(x2, ln)\<rfloor>" "t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2)" "wset s1 t = None \<or> x1 \<approx>w x2" 
    by(auto dest: mbisim_thrD1)
  show "r2.not_final_thread s2 t"
  proof(cases "wset s1 t = None \<and> ln = no_wait_locks")
    case False
    with `r1.not_final_thread s1 t` `thr s1 t = \<lfloor>(x1, ln)\<rfloor>` `thr s2 t = \<lfloor>(x2, ln)\<rfloor>` mbisim 
    show ?thesis by cases(auto simp add: mbisim_def r2.not_final_thread_iff)
  next
    case True
    with `r1.not_final_thread s1 t` `thr s1 t = \<lfloor>(x1, ln)\<rfloor>` have "\<not> final1 x1" by(cases) auto
    have "\<not> final2 x2"
    proof
      assume "final2 x2"
      with final2_simulation[OF `t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2)`]
      obtain x1' m1' where "r1.silent_moves t (x1, shr s1) (x1', m1')" "t \<turnstile> (x1', m1') \<approx> (x2, shr s2)" "final1 x1'" by auto
      from `r1.silent_moves t (x1, shr s1) (x1', m1')` have "x1' = x1"
      proof(cases rule: converse_rtranclpE2[consumes 1, case_names refl step])
	case (step x1'' m1'')
	from `r1.silent_move t (x1, shr s1) (x1'', m1'')`
	have "t \<turnstile> (x1, shr s1) -1-\<epsilon>\<rightarrow> (x1'', m1'')" by(auto dest: r1.silent_tl)
	hence "r1.redT s1 (t, observable_ta_of \<epsilon>) (redT_upd s1 t (\<epsilon> :: ('l,'t,'x1,'m1,'w,'o list) thread_action) x1'' m1'')"
	  using `thr s1 t = \<lfloor>(x1, ln)\<rfloor>` True by -(erule r1.redT_normal, auto)
	hence False using dead by(auto intro: r1.deadlock_no_red r1.red_no_deadlock)
	thus ?thesis ..
      qed simp
      with `\<not> final1 x1` `final1 x1'` show False by simp
    qed
    thus ?thesis using `thr s2 t = \<lfloor>(x2, ln)\<rfloor>` by(auto simp add: r2.not_final_thread_iff)
  qed
qed

lemma deadlocked1_imp_\<tau>s_deadlocked2:
  assumes mbisim: "s1 \<approx>m s2"
  and dead: "r1.deadlocked s1 t"
  shows "\<exists>s2'. r2.mthr.silent_moves s2 s2' \<and> r2.deadlocked s2' t \<and> s1 \<approx>m s2'"
proof -
  from mfinal1_inv_simulation[OF bisim_inv_wfs_inv2[OF bisim_inv] mbisim]
  obtain ls2 ts2 m2 ws2 where red1: "r2.mthr.silent_moves s2 (ls2, (ts2, m2), ws2)"
    and "s1 \<approx>m (ls2, (ts2, m2), ws2)" and "m2 = shr s2" 
    and fin: "\<And>t. r1.final_thread s1 t \<Longrightarrow> r2.final_thread (ls2, (ts2, m2), ws2) t" by auto
  from no_\<tau>Move1_\<tau>s_to_no_\<tau>Move2[OF `s1 \<approx>m (ls2, (ts2, m2), ws2)`]
  obtain ts2' where red2: "r2.mthr.silent_moves (ls2, (ts2, m2), ws2) (ls2, (ts2', m2), ws2)"
    and no_\<tau>: "\<And>t x1 x2 x2' m2'. \<lbrakk> wset s1 t = None; thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>; ts2' t = \<lfloor>(x2, no_wait_locks)\<rfloor>;
                           \<And>x' m'. r1.silent_move t (x1, shr s1) (x', m') \<Longrightarrow> False \<rbrakk>
              \<Longrightarrow>  \<not> r2.silent_move t (x2, m2) (x2', m2')"
    and mbisim: "s1 \<approx>m (ls2, (ts2', m2), ws2)" by fastsimp
  let ?s2 = "(ls2, (ts2', m2), ws2)"
  from red2 have fin': "\<And>t. r1.final_thread s1 t \<Longrightarrow> r2.final_thread ?s2 t"
    by(rule r2.\<tau>mRedT_preserves_final_thread)(rule fin)
  from dead
  have "r2.deadlocked ?s2 t"
  proof(coinduct)
    case (deadlocked t)
    thus ?case
    proof(cases rule: r1.deadlocked_elims)
      case (lock x1)
      hence csmw: "\<And>LT. r1.can_sync t x1 (shr s1) LT \<Longrightarrow>
                   \<exists>t'. (r1.deadlocked s1 t' \<or> r1.final_thread s1 t') \<and>
                        (\<exists>lt\<in>LT. r1.must_wait s1 t lt t')" by blast
      from `thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>` mbisim obtain x2
	where "ts2' t = \<lfloor>(x2, no_wait_locks)\<rfloor>" and bisim: "t \<turnstile> (x1, shr s1) \<approx> (x2, m2)"
	by(auto dest: mbisim_thrD1)
      note `ts2' t = \<lfloor>(x2, no_wait_locks)\<rfloor>` moreover
      { from `r1.must_sync t x1 (shr s1)` obtain ta1 x1' m1'
	  where r1: "t \<turnstile> (x1, shr s1) -1-ta1\<rightarrow> (x1', m1')" by(auto elim: r1.must_syncE)
	have "\<not> \<tau>move1 (x1, shr s1) ta1 (x1', m1')" (is "\<not> ?\<tau>")
	proof
	  assume "?\<tau>"
	  hence "ta1 = \<epsilon>" by(rule r1.silent_tl)
	  with r1 have "r1.can_sync t x1 (shr s1) {}"
	    by(auto intro: r1.can_syncI simp add: collect_locks_def)
	  from csmw[OF this] show False by blast
	qed
	from simulation1[OF bisim r1 this] have "\<exists>ta2 x2' m2'. t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2')"
	  by(clarsimp)(erule converse_rtranclpE, fastsimp+)
	hence "r2.must_sync t x2 m2" by(auto intro: r2.must_syncI) }
      moreover
      { fix LT
	assume "r2.can_sync t x2 m2 LT"
	then obtain ta2 x2' m2' where r2: "t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2')"
	  and LT: "LT = collect_locks \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>}"
	  by(auto elim: r2.can_syncE)
	from `wset s1 t = None` `thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>` `ts2' t = \<lfloor>(x2, no_wait_locks)\<rfloor>`
	have "\<not> r2.silent_move t (x2, m2) (x2', m2')"
	proof(rule no_\<tau>)
	  fix x1' m1'
	  assume "r1.silent_move t (x1, shr s1) (x1', m1')"
	  hence "t \<turnstile> (x1, shr s1) -1-\<epsilon>\<rightarrow> (x1', m1')" by(auto dest: r1.silent_tl)
	  hence "r1.can_sync t x1 (shr s1) {}"
	    by(auto intro: r1.can_syncI simp add: collect_locks_def)
	  with csmw[OF this] show False by blast
	qed
	with r2 have "\<not> \<tau>move2 (x2, m2) ta2 (x2', m2')" by auto
	from simulation2[OF bisim r2 this] obtain x1' m1' x1'' m1'' ta1
	  where \<tau>r1: "r1.silent_moves t (x1, shr s1) (x1', m1')"
	  and r1: "t \<turnstile> (x1', m1') -1-ta1\<rightarrow> (x1'', m1'')"
	  and n\<tau>1: "\<not> \<tau>move1 (x1', m1') ta1 (x1'', m1'')"
	  and bisim': "t \<turnstile> (x1'', m1'') \<approx> (x2', m2')"
	  and tlsim: "ta1 \<sim>m ta2" by auto
	from \<tau>r1 obtain [simp]: "x1' = x1" "m1' = shr s1"
	proof(cases rule: converse_rtranclpE2[consumes 1, case_names refl step])
	  case (step X M)
	  from `r1.silent_move t (x1, shr s1) (X, M)`
	  have "t \<turnstile> (x1, shr s1) -1-\<epsilon>\<rightarrow> (X, M)" by(auto dest: r1.silent_tl)
	  hence "r1.can_sync t x1 (shr s1) {}"
	    by(auto intro: r1.can_syncI simp add: collect_locks_def)
	  with csmw[OF this] have False by blast
	  thus ?thesis ..
	qed blast
	from tlsim LT have "LT = collect_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta1\<rbrace>\<^bsub>c\<^esub>}"
	  by(auto simp add: ta_bisim_def)
	with r1 have "r1.can_sync t x1 (shr s1) LT" by(auto intro: r1.can_syncI)
	from csmw[OF this] obtain t' lt 
	  where t': "r1.deadlocked s1 t' \<or> r1.final_thread s1 t'"
	  and lt: "lt \<in> LT" "r1.must_wait s1 t lt t'" by blast
	from t' have "r1.deadlocked s1 t' \<or> r2.deadlocked ?s2 t' \<or> r2.final_thread ?s2 t'" (is "?dead t'")
	proof
	  assume "r1.final_thread s1 t'"
	  hence "r2.final_thread ?s2 t'" by(rule fin')
	  thus ?thesis by blast
	qed blast
	moreover from lt(2)
	have "r2.must_wait ?s2 t lt t'"
	proof(cases rule: r1.must_wait_elims)
	  case (lock l)
	  with mbisim show ?thesis by(auto simp add: mbisim_def)
	next
	  case thread
	  from `r1.not_final_thread s1 t'` obtain x1 ln
	    where "thr s1 t' = \<lfloor>(x1, ln)\<rfloor>" by cases auto
	  with mbisim obtain x2 where "ts2' t' = \<lfloor>(x2, ln)\<rfloor>" "t' \<turnstile> (x1, shr s1) \<approx> (x2, m2)" by(auto dest: mbisim_thrD1)
	  show ?thesis
	  proof(cases "wset s1 t' = None \<and> ln = no_wait_locks")
	    case False
	    with `r1.not_final_thread s1 t'` `thr s1 t' = \<lfloor>(x1, ln)\<rfloor>` `ts2' t' = \<lfloor>(x2, ln)\<rfloor>` mbisim `lt = Inr t'`
	    show ?thesis by cases(auto simp add: mbisim_def r2.not_final_thread_iff)
	  next
	    case True
	    with `r1.not_final_thread s1 t'` `thr s1 t' = \<lfloor>(x1, ln)\<rfloor>` have "\<not> final1 x1" by(cases) auto
	    with t' `thr s1 t' = \<lfloor>(x1, ln)\<rfloor>` have "r1.deadlocked s1 t'" by(auto simp add: r1.final_thread_def)
	    have "\<not> final2 x2"
	    proof
	      assume "final2 x2"
	      with final2_simulation[OF `t' \<turnstile> (x1, shr s1) \<approx> (x2, m2)`]
	      obtain x1' m1' where "r1.silent_moves t' (x1, shr s1) (x1', m1')"
                and "t' \<turnstile> (x1', m1') \<approx> (x2, m2)" "final1 x1'" by auto
	      from `r1.silent_moves t' (x1, shr s1) (x1', m1')` have "x1' = x1"
	      proof(cases rule: converse_rtranclpE2[consumes 1, case_names refl step])
		case (step x1'' m1'')
		from `r1.silent_move t' (x1, shr s1) (x1'', m1'')`
		have "t' \<turnstile> (x1, shr s1) -1-\<epsilon>\<rightarrow> (x1'', m1'')" by(auto dest: r1.silent_tl)
		hence "r1.redT s1 (t', observable_ta_of \<epsilon>) (redT_upd s1 t' (\<epsilon> :: ('l,'t,'x1,'m1,'w,'o list) thread_action) x1'' m1'')"
		  using `thr s1 t' = \<lfloor>(x1, ln)\<rfloor>` True by -(erule r1.redT_normal, auto)
		hence False using `r1.deadlocked s1 t'` by(rule r1.red_no_deadlock)
		thus ?thesis ..
	      qed simp
	      with `\<not> final1 x1` `final1 x1'` show False by simp
	    qed
	    thus ?thesis using `ts2' t' = \<lfloor>(x2, ln)\<rfloor>` `lt = Inr t'` by(auto simp add: r2.not_final_thread_iff)
	  qed
	qed
	ultimately have "\<exists>t'. ?dead t' \<and> (\<exists>lt\<in>LT. r2.must_wait ?s2 t lt t')" using `lt \<in> LT` by blast }
      moreover from mbisim `wset s1 t = None` have "wset ?s2 t = None" by(simp add: mbisim_def)
      ultimately have ?deadlockedLock by simp
      thus ?thesis ..
    next
      case (wait x1 ln)
      from mbisim `thr s1 t = \<lfloor>(x1, ln)\<rfloor>`
      obtain x2 where "ts2' t = \<lfloor>(x2, ln)\<rfloor>" by(auto dest: mbisim_thrD1)
      moreover
      have "r2.all_final_except ?s2 (r1.deadlocked s1)"
      proof(rule r2.all_final_exceptI)
	fix t
	assume "r2.not_final_thread ?s2 t"
	then obtain x2 ln where "ts2' t = \<lfloor>(x2, ln)\<rfloor>" by(auto simp add: r2.not_final_thread_iff)
	with mbisim obtain x1 where "thr s1 t = \<lfloor>(x1, ln)\<rfloor>" "t \<turnstile> (x1, shr s1) \<approx> (x2, m2)" by(auto dest: mbisim_thrD2)
	hence "r1.not_final_thread s1 t" using `r2.not_final_thread ?s2 t` `ts2' t = \<lfloor>(x2, ln)\<rfloor>` mbisim fin'[of t]
	  by(cases "wset s1 t")(auto simp add: r1.not_final_thread_iff r2.not_final_thread_iff mbisim_def r1.final_thread_def r2.final_thread_def)
	with `thr s1 t = \<lfloor>(x1, ln)\<rfloor>` `r1.all_final_except s1 (r1.deadlocked s1)`
	show "r1.deadlocked s1 t" by -(erule r1.all_final_exceptD)
      qed
      hence "r2.all_final_except ?s2 (\<lambda>t. r1.deadlocked s1 t \<or> r2.deadlocked ?s2 t)"
	by(rule r2.all_final_except_mono') blast
      moreover
      from `waiting (wset s1 t)` mbisim
      have "waiting (wset ?s2 t)" by(simp add: mbisim_def)
      ultimately have ?deadlockedWait by simp
      thus ?thesis by blast
    next
      case (acquire x1 ln l t')
      from mbisim `thr s1 t = \<lfloor>(x1, ln)\<rfloor>`
      obtain x2 where "ts2' t = \<lfloor>(x2, ln)\<rfloor>" by(auto dest: mbisim_thrD1)
      moreover
      from `r1.deadlocked s1 t' \<or> r1.final_thread s1 t'`
      have "(r1.deadlocked s1 t' \<or> r2.deadlocked ?s2 t') \<or> r2.final_thread ?s2 t'" by(blast dest: fin')
      moreover
      from mbisim `has_lock ((locks s1)\<^sub>f l) t'`
      have "has_lock ((locks ?s2)\<^sub>f l) t'" by(simp add: mbisim_def)
      ultimately have ?deadlockedAcquire
        using `0 < ln\<^sub>f l` `t \<noteq> t'` `\<not> waiting (wset s1 t)` `s1 \<approx>m (ls2, (ts2', m2), ws2)`
        by(auto simp add: mbisim_def)
      thus ?thesis by blast
    qed
  qed
  with red1 red2 mbisim show ?thesis by(blast intro: rtranclp_trans)
qed

lemma deadlocked2_imp_\<tau>s_deadlocked1:
  "\<lbrakk> s1 \<approx>m s2; r2.deadlocked s2 t \<rbrakk>
  \<Longrightarrow> \<exists>s1'. r1.mthr.silent_moves s1 s1' \<and> r1.deadlocked s1' t \<and> s1' \<approx>m s2"
using FWdelay_bisimulation_diverge.deadlocked1_imp_\<tau>s_deadlocked2[OF FWdelay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma deadlock1_imp_\<tau>s_deadlock2:
  assumes mbisim: "s1 \<approx>m s2"
  and dead: "r1.deadlock s1"
  shows "\<exists>s2'. r2.mthr.silent_moves s2 s2' \<and> r2.deadlock s2' \<and> s1 \<approx>m s2'"
proof -
  from mfinal1_inv_simulation[OF bisim_inv_wfs_inv2[OF bisim_inv] mbisim]
  obtain ls2 ts2 m2 ws2 where red1: "r2.mthr.silent_moves s2 (ls2, (ts2, m2), ws2)"
    and "s1 \<approx>m (ls2, (ts2, m2), ws2)" and "m2 = shr s2" 
    and fin: "\<And>t. r1.final_thread s1 t \<Longrightarrow> r2.final_thread (ls2, (ts2, m2), ws2) t" by auto
  from no_\<tau>Move1_\<tau>s_to_no_\<tau>Move2[OF `s1 \<approx>m (ls2, (ts2, m2), ws2)`]
  obtain ts2' where red2: "r2.mthr.silent_moves (ls2, (ts2, m2), ws2) (ls2, (ts2', m2), ws2)"
    and no_\<tau>: "\<And>t x1 x2 x2' m2'. \<lbrakk> wset s1 t = None; thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>; ts2' t = \<lfloor>(x2, no_wait_locks)\<rfloor>;
                           \<And>x' m'. r1.silent_move t (x1, shr s1) (x', m') \<Longrightarrow> False \<rbrakk>
              \<Longrightarrow>  \<not> r2.silent_move t (x2, m2) (x2', m2')"
    and mbisim: "s1 \<approx>m (ls2, (ts2', m2), ws2)" by fastsimp
  let ?s2 = "(ls2, (ts2', m2), ws2)"
  from red2 have fin': "\<And>t. r1.final_thread s1 t \<Longrightarrow> r2.final_thread ?s2 t"
    by(rule r2.\<tau>mRedT_preserves_final_thread)(rule fin)
  from dead obtain t where nfin1: "r1.not_final_thread s1 t" by(auto elim: r1.deadlockE)
  from dead deadlock_mbisim_not_final_thread_pres[OF _ `r1.not_final_thread s1 t` fin' mbisim]
  have "r2.not_final_thread ?s2 t" by simp
  hence "r2.deadlock ?s2"
  proof(cases rule: r2.deadlockI[consumes 1, case_names lock acquire wsok])
    case (lock t x2)
    note ts2t = `thr ?s2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>`
    with mbisim obtain x1 where ts1t: "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>"
      and bisim: "t \<turnstile> (x1, shr s1) \<approx> (x2, m2)" by(auto dest: mbisim_thrD2)
    from `wset ?s2 t = None` mbisim have ws1t: "wset s1 t = None" by(simp add: mbisim_def)
    have "\<not> final1 x1"
    proof
      assume "final1 x1"
      with ts1t ws1t have "r1.final_thread s1 t" by(simp add: r1.final_thread_def)
      hence "r2.final_thread ?s2 t" by(rule fin')
      with `\<not> final2 x2` ts2t `wset ?s2 t = None` show False by(simp add: r2.final_thread_def)
    qed
    from r1.deadlockD1[OF dead ts1t this `wset s1 t = None`]
    have ms: "r1.must_sync t x1 (shr s1)"
      and csmw: "\<And>LT. r1.can_sync t x1 (shr s1) LT \<Longrightarrow> \<exists>t'. thr s1 t' \<noteq> None \<and> (\<exists>lt\<in>LT. r1.must_wait s1 t lt t')"
      by blast+
    { 
      from `r1.must_sync t x1 (shr s1)` obtain ta1 x1' m1'
        where r1: "t \<turnstile> (x1, shr s1) -1-ta1\<rightarrow> (x1', m1')" by(auto elim: r1.must_syncE)
      have "\<not> \<tau>move1 (x1, shr s1) ta1 (x1', m1')" (is "\<not> ?\<tau>")
      proof
	assume "?\<tau>"
	hence "ta1 = \<epsilon>" by(rule r1.silent_tl)
	with r1 have "r1.can_sync t x1 (shr s1) {}"
	  by(auto intro: r1.can_syncI simp add: collect_locks_def)
	from csmw[OF this] show False by blast
      qed
      from simulation1[OF bisim r1 this] have "\<exists>ta2 x2' m2'. t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2')"
	by(clarsimp)(erule converse_rtranclpE, fastsimp+)
      hence "r2.must_sync t x2 m2" by(auto intro: r2.must_syncI) }
    moreover
    { fix LT
      assume "r2.can_sync t x2 m2 LT"
      then obtain ta2 x2' m2' where r2: "t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2')"
	and LT: "LT = collect_locks \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>}"
	by(auto elim: r2.can_syncE)
      from ts2t have "ts2' t = \<lfloor>(x2, no_wait_locks)\<rfloor>" by simp
      with ws1t ts1t have "\<not> r2.silent_move t (x2, m2) (x2', m2')"
      proof(rule no_\<tau>)
	fix x1' m1'
	assume "r1.silent_move t (x1, shr s1) (x1', m1')"
	hence "t \<turnstile> (x1, shr s1) -1-\<epsilon>\<rightarrow> (x1', m1')" by(auto dest: r1.silent_tl)
	hence "r1.can_sync t x1 (shr s1) {}"
	  by(auto intro: r1.can_syncI simp add: collect_locks_def)
	with csmw[OF this] show False by blast
      qed
      with r2 have "\<not> \<tau>move2 (x2, m2) ta2 (x2', m2')" by auto
      from simulation2[OF bisim r2 this] obtain x1' m1' x1'' m1'' ta1
	where \<tau>r1: "r1.silent_moves t (x1, shr s1) (x1', m1')"
	and r1: "t \<turnstile> (x1', m1') -1-ta1\<rightarrow> (x1'', m1'')"
	and n\<tau>1: "\<not> \<tau>move1 (x1', m1') ta1 (x1'', m1'')"
	and bisim': "t \<turnstile> (x1'', m1'') \<approx> (x2', m2')"
	and tlsim: "ta1 \<sim>m ta2" by auto
      from \<tau>r1 obtain [simp]: "x1' = x1" "m1' = shr s1"
      proof(cases rule: converse_rtranclpE2[consumes 1, case_names refl step])
	case (step X M)
	from `r1.silent_move t (x1, shr s1) (X, M)`
	have "t \<turnstile> (x1, shr s1) -1-\<epsilon>\<rightarrow> (X, M)" by(auto dest: r1.silent_tl)
	hence "r1.can_sync t x1 (shr s1) {}"
	  by(auto intro: r1.can_syncI simp add: collect_locks_def)
	with csmw[OF this] have False by blast
	thus ?thesis ..
      qed blast
      from tlsim LT have "LT = collect_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta1\<rbrace>\<^bsub>c\<^esub>}"
	by(auto simp add: ta_bisim_def)
      with r1 have "r1.can_sync t x1 (shr s1) LT" by(auto intro: r1.can_syncI)
      from csmw[OF this] obtain t' lt 
	where t': "thr s1 t' \<noteq> None" and lt: "lt \<in> LT" "r1.must_wait s1 t lt t'" by blast
      from mbisim_thrNone_eq[OF mbisim, of t'] t' have "thr ?s2 t' \<noteq> None" by simp
      from `r1.must_wait s1 t lt t'` have "r2.must_wait ?s2 t lt t'"
      proof(cases rule: r1.must_wait_elims)
	case (lock l)
	with mbisim show ?thesis by(auto simp add: mbisim_def)
      next
	case thread
	from dead deadlock_mbisim_not_final_thread_pres[OF _ `r1.not_final_thread s1 t'` fin' mbisim]
	have "r2.not_final_thread ?s2 t'" by auto
	thus ?thesis using thread by auto
      qed
      with lt `thr ?s2 t' \<noteq> None` have "\<exists>t'. thr ?s2 t' \<noteq> None \<and> (\<exists>lt\<in>LT. r2.must_wait ?s2 t lt t')" by blast }
    ultimately show ?case by fastsimp
  next
    case (acquire t x2 ln l)
    note dead moreover
    from mbisim `thr ?s2 t = \<lfloor>(x2, ln)\<rfloor>`
    obtain x1 where "thr s1 t = \<lfloor>(x1, ln)\<rfloor>" by(auto dest: mbisim_thrD2)
    moreover note `0 < ln\<^sub>f l`
    moreover from `\<not> waiting (wset ?s2 t)` mbisim
    have "\<not> waiting (wset s1 t)" by(simp add: mbisim_def)
    ultimately obtain l' t' where "0 < ln\<^sub>f l'" "t \<noteq> t'" "thr s1 t' \<noteq> None" "has_lock ((locks s1)\<^sub>f l') t'"
      by(rule r1.deadlockD2)
    thus ?case using mbisim_thrNone_eq[OF mbisim, of t'] mbisim by(auto simp add: mbisim_def)
  next
    case (wsok t x2 w)
    from mbisim_thrD2[OF mbisim this]
    obtain x1 where "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>" by auto
    with dead have "wset s1 t \<noteq> \<lfloor>WokenUp w\<rfloor>" by(rule r1.deadlockD3[rule_format])
    with mbisim show ?case by(simp add: mbisim_def)
  qed
  with red1 red2 mbisim show ?thesis by(blast intro: rtranclp_trans)
qed

lemma deadlock2_imp_\<tau>s_deadlock1:
  "\<lbrakk> s1 \<approx>m s2; r2.deadlock s2 \<rbrakk>
  \<Longrightarrow> \<exists>s1'. r1.mthr.silent_moves s1 s1' \<and> r1.deadlock s1' \<and> s1' \<approx>m s2"
using FWdelay_bisimulation_diverge.deadlock1_imp_\<tau>s_deadlock2[OF FWdelay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma deadlocked'1_imp_\<tau>s_deadlocked'2:
  "\<lbrakk> s1 \<approx>m s2; r1.deadlocked' s1 \<rbrakk> \<Longrightarrow> \<exists>s2'. r2.mthr.silent_moves s2 s2' \<and> r2.deadlocked' s2' \<and> s1 \<approx>m s2'"
unfolding r1.deadlock_eq_deadlocked'[symmetric] r2.deadlock_eq_deadlocked'[symmetric]
by(rule deadlock1_imp_\<tau>s_deadlock2)

lemma deadlocked'2_imp_\<tau>s_deadlocked'1:
  "\<lbrakk> s1 \<approx>m s2; r2.deadlocked' s2 \<rbrakk> \<Longrightarrow> \<exists>s1'. r1.mthr.silent_moves s1 s1' \<and> r1.deadlocked' s1' \<and> s1' \<approx>m s2"
unfolding r1.deadlock_eq_deadlocked'[symmetric] r2.deadlock_eq_deadlocked'[symmetric]
by(rule deadlock2_imp_\<tau>s_deadlock1)
  
end


context FWbisimulation begin

lemma mbisim_final_thread_preserve1:
  assumes mbisim: "s1 \<approx>m s2" and fin: "r1.final_thread s1 t"
  shows "r2.final_thread s2 t"
proof -
  from fin obtain x1 where ts1t: "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>"
    and fin1: "final1 x1" and ws1t: "wset s1 t = None"
    by(auto elim: r1.final_threadE)
  from mbisim ts1t obtain x2 
    where ts2t: "thr s2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>"
    and bisim: "t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2)" by(auto dest: mbisim_thrD1)
  note ts2t moreover from fin1 bisim have "final2 x2" by(auto dest: bisim_final)
  moreover from mbisim ws1t have "wset s2 t = None" by(simp add: mbisim_def)
  ultimately show ?thesis by(rule r2.final_threadI)
qed

lemma mbisim_final_thread_preserve2:
  "\<lbrakk> s1 \<approx>m s2; r2.final_thread s2 t \<rbrakk> \<Longrightarrow> r1.final_thread s1 t"
using FWbisimulation.mbisim_final_thread_preserve1[OF FWbisimulation_flip]
unfolding flip_simps .

lemma mbisim_final_thread_inv:
  "s1 \<approx>m s2 \<Longrightarrow> r1.final_thread s1 t \<longleftrightarrow> r2.final_thread s2 t"
by(blast intro: mbisim_final_thread_preserve1 mbisim_final_thread_preserve2)

lemma mbisim_not_final_thread_inv:
  assumes bisim: "mbisim s1 s2"
  shows "r1.not_final_thread s1 = r2.not_final_thread s2"
proof(rule ext)
  fix t
  show "r1.not_final_thread s1 t = r2.not_final_thread s2 t"
  proof(cases "thr s1 t")
    case None
    with mbisim_thrNone_eq[OF bisim, of t] have "thr s2 t = None" by simp
    with None show ?thesis
      by(auto elim!: r2.not_final_thread.cases r1.not_final_thread.cases
             intro: r2.not_final_thread.intros r1.not_final_thread.intros)
  next
    case (Some a)
    then obtain x1 ln where tst1: "thr s1 t = \<lfloor>(x1, ln)\<rfloor>" by(cases a) auto
    from mbisim_thrD1[OF bisim tst1] obtain x2
      where tst2: "thr s2 t = \<lfloor>(x2, ln)\<rfloor>" and bisimt: "t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2)" by blast
    from bisim have "wset s2 = wset s1" by(simp add: mbisim_def)
    with tst2 tst1 bisim_final[OF bisimt] show ?thesis
      by(simp add: r1.not_final_thread_conv r2.not_final_thread_conv)(rule mbisim_final_thread_inv[OF bisim])
  qed
qed

lemma mbisim_deadlocked_preserve1:
  assumes mbisim: "s1 \<approx>m s2" and dead: "r1.deadlocked s1 t"
  shows "r2.deadlocked s2 t"
proof -
  from deadlocked1_imp_\<tau>s_deadlocked2[OF mbisim dead]
  obtain s2' where "r2.mthr.silent_moves s2 s2'"
    and "r2.deadlocked s2' t" by blast
  from `r2.mthr.silent_moves s2 s2'` have "s2' = s2"
    by(rule converse_rtranclpE)(auto elim: r2.m\<tau>move.cases)
  with `r2.deadlocked s2' t` show ?thesis by simp
qed

lemma mbisim_deadlocked_preserve2:
  "\<lbrakk> s1 \<approx>m s2; r2.deadlocked s2 t \<rbrakk> \<Longrightarrow> r1.deadlocked s1 t"
using FWbisimulation.mbisim_deadlocked_preserve1[OF FWbisimulation_flip]
unfolding flip_simps .

lemma mbisim_deadlocked_inv:
  "s1 \<approx>m s2 \<Longrightarrow> r1.deadlocked s1 = r2.deadlocked s2"
by(blast intro!: ext mbisim_deadlocked_preserve1 mbisim_deadlocked_preserve2)

lemma mbisim_deadlocked'_inv:
  "s1 \<approx>m s2 \<Longrightarrow> r1.deadlocked' s1 \<longleftrightarrow> r2.deadlocked' s2"
unfolding r1.deadlocked'_def r2.deadlocked'_def
by(simp add: mbisim_not_final_thread_inv mbisim_deadlocked_inv)

lemma mbisim_deadlock_inv:
  "s1 \<approx>m s2 \<Longrightarrow> r1.deadlock s1 = r2.deadlock s2"
unfolding r1.deadlock_eq_deadlocked' r2.deadlock_eq_deadlocked'
by(rule mbisim_deadlocked'_inv)

end

(* Nice to have, but not needed any more *)

context FWbisimulation begin

lemma bisim_can_sync_preserve1:
  assumes bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)" and cs: "t \<turnstile> \<langle>x1, m1\<rangle> LT \<wrong>1"
  shows "t \<turnstile> \<langle>x2, m2\<rangle> LT \<wrong>2"
proof -
  from cs obtain ta1 x1' m1' where red1: "t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1')"
    and LT: "LT = collect_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta1\<rbrace>\<^bsub>c\<^esub>}" by(rule r1.can_syncE)
  from bisimulation.simulation1[OF bisimulation_axioms, OF bisim red1] obtain x2' ta2 m2'
    where red2: "t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2')" 
    and tasim: "ta1 \<sim>m ta2" by fastsimp
  from tasim LT have "LT = collect_locks \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub> <+> {t. Join t \<in> set \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>}"
    by(auto simp add: ta_bisim_def)
  with red2 show ?thesis by(rule r2.can_syncI)
qed

lemma bisim_can_sync_preserve2:
  "\<lbrakk> t \<turnstile> (x1, m1) \<approx> (x2, m2); t \<turnstile> \<langle>x2, m2\<rangle> LT \<wrong>2 \<rbrakk> \<Longrightarrow> t \<turnstile> \<langle>x1, m1\<rangle> LT \<wrong>1"
using FWbisimulation.bisim_can_sync_preserve1[OF FWbisimulation_flip]
unfolding flip_simps .

lemma bisim_can_sync_inv:
  "t \<turnstile> (x1, m1) \<approx> (x2, m2) \<Longrightarrow> t \<turnstile> \<langle>x1, m1\<rangle> LT \<wrong>1 \<longleftrightarrow> t \<turnstile> \<langle>x2, m2\<rangle> LT \<wrong>2"
by(blast intro: bisim_can_sync_preserve1 bisim_can_sync_preserve2)

lemma bisim_must_sync_inv:
  assumes bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)"
  shows "t \<turnstile> \<langle>x1, m1\<rangle> \<wrong>1 \<longleftrightarrow> t \<turnstile> \<langle>x2, m2\<rangle> \<wrong>2"
unfolding r1.must_sync_can_sync_conv r2.must_sync_can_sync_conv
by(auto simp add: bisim_can_sync_inv[OF bisim])

end


end