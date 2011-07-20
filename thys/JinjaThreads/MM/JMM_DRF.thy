(*  Title:      JinjaThreads/MM/JMM_DRF.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{The data race free guarantee of the JMM} *}

theory JMM_DRF imports
  JMM_Spec
begin

context executions begin

lemma drf_lemma:
  assumes wf: "P \<turnstile> (E, ws) \<surd>"
  and E: "E \<in> \<E>"
  and sync: "correctly_synchronized P \<E>"
  and read_before: "\<And>r. r \<in> read_actions E \<Longrightarrow> P,E \<turnstile> ws r \<le>hb r"
  shows "sequentially_consistent P (E, ws)"
proof(rule ccontr)
  let ?Q = "{r. r \<in> read_actions E \<and> \<not> P,E \<turnstile> r \<leadsto>mrw ws r}"

  assume "\<not> ?thesis"
  then obtain r where "r \<in> read_actions E" "\<not> P,E \<turnstile> r \<leadsto>mrw ws r"
    by(auto simp add: sequentially_consistent_def)
  hence "r \<in> ?Q" by simp
  with wf_action_order[of E] obtain r' 
    where "r' \<in> ?Q"  
    and "(action_order E)\<^sup>\<noteq>\<^sup>\<noteq>^** r' r"
    and r'_min: "\<And>a. (action_order E)\<^sup>\<noteq>\<^sup>\<noteq> a r' \<Longrightarrow> a \<notin> ?Q"
    by(rule wfP_minimalE) blast
  from `r' \<in> ?Q` have r': "r' \<in> read_actions E"
    and not_mrw: "\<not> P,E \<turnstile> r' \<leadsto>mrw ws r'" by blast+

  from r' obtain ad al v where obs_r': "action_obs E r' = NormalAction (ReadMem ad al v)"
    by(cases) auto
  from wf have ws: "is_write_seen P E ws" 
    and tsa_ok: "thread_start_actions_ok E" 
    by(rule wf_exec_is_write_seenD wf_exec_thread_start_actions_okD)+
  from is_write_seenD[OF ws r' obs_r']
  have ws_r: "ws r' \<in> write_actions E"
    and adal: "(ad, al) \<in> action_loc P E (ws r')"
    and v: "v = value_written P E (ws r') (ad, al)"
    and not_hb: "\<not> P,E \<turnstile> r' \<le>hb ws r'" by blast+
  from r' have "P,E \<turnstile> ws r' \<le>hb r'" by(rule read_before)
  hence "E \<turnstile> ws r' \<le>a r'" by(rule happens_before_into_action_order)
  from not_mrw
  have "\<exists>w'. w' \<in> write_actions E \<and> (ad, al) \<in> action_loc P E w' \<and> \<not> P,E \<turnstile> w' \<le>hb ws r' \<and> \<not> P,E \<turnstile> r' \<le>hb w' \<and> E \<turnstile> w' \<le>a r'"
  proof(rule contrapos_np)
    assume inbetween: "\<not> ?thesis"
    note r'
    moreover from obs_r' have "(ad, al) \<in> action_loc P E r'" by simp
    moreover note `E \<turnstile> ws r' \<le>a r'` ws_r adal
    moreover
    { fix w'
      assume "w' \<in> write_actions E" "(ad, al) \<in> action_loc P E w'"
      with inbetween have "P,E \<turnstile> w' \<le>hb ws r' \<or> P,E \<turnstile> r' \<le>hb w' \<or> \<not> E \<turnstile> w' \<le>a r'" by simp
      moreover from total_onPD[OF total_action_order, of w' E r'] `w' \<in> write_actions E` r'
      have "E \<turnstile> w' \<le>a r' \<or> E \<turnstile> r' \<le>a w'" by(auto dest: read_actions_not_write_actions)
      ultimately have "E \<turnstile> w' \<le>a ws r' \<or> E \<turnstile> r' \<le>a w'" 
        by(blast intro: happens_before_into_action_order) }
    ultimately show "P,E \<turnstile> r' \<leadsto>mrw ws r'" by(rule most_recent_write_for.intros)
  qed
  then obtain w' where w': "w' \<in> write_actions E"
    and adal_w': "(ad, al) \<in> action_loc P E w'"
    and "\<not> P,E \<turnstile> w' \<le>hb ws r'" "\<not> P,E \<turnstile> r' \<le>hb w'" "E \<turnstile> w' \<le>a r'" by blast

  { fix a
    assume "a < r'" and "a \<in> read_actions E"
    hence "(action_order E)\<^sup>\<noteq>\<^sup>\<noteq> a r'" using r' obs_r' by(auto intro: action_orderI)
    from r'_min[OF this] `a \<in> read_actions E`
    have "P,E \<turnstile> a \<leadsto>mrw ws a" by simp }

  from \<E>_sequential_completion[OF E wf this, of r'] r'
  obtain E' ws' where "E' \<in> \<E>" "P \<turnstile> (E', ws') \<surd>"
    and eq: "ltake (enat r') E = ltake (enat r') E'"
    and sc': "sequentially_consistent P (E', ws')" 
    and r'': "action_tid E r' = action_tid E' r'" "action_obs E r' \<approx> action_obs E' r'"
    and "r' \<in> actions E'"
    by auto

  from `P \<turnstile> (E', ws') \<surd>` have tsa_ok': "thread_start_actions_ok E'"
    by(rule wf_exec_thread_start_actions_okD)

  from `r' \<in> read_actions E` have "enat r' < llength E" by(auto elim: read_actions.cases actionsE)
  moreover from `r' \<in> actions E'` have "enat r' < llength E'" by(auto elim: actionsE)
  ultimately have eq': "ltake (enat (Suc r')) E [\<approx>] ltake (enat (Suc r')) E'"
    using eq[THEN eq_into_sim_actions] r''
    by(auto simp add: ltake_Suc_conv_snoc_lnth sim_actions_def split_beta action_tid_def action_obs_def intro!: llist_all2_lappendI)
  from r' have r'': "r' \<in> read_actions E'"
    by(rule read_actions_change_prefix[OF _eq']) simp
  from obs_r' have "(ad, al) \<in> action_loc P E r'" by simp
  hence adal_r'': "(ad, al) \<in> action_loc P E' r'"
    by(subst (asm) action_loc_change_prefix[OF eq']) simp

  from `\<not> P,E \<turnstile> w' \<le>hb ws r'`
  have "\<not> is_new_action (action_obs E w')"
  proof(rule contrapos_nn)
    assume new_w': "is_new_action (action_obs E w')"
    show "P,E \<turnstile> w' \<le>hb ws r'"
    proof(cases "is_new_action (action_obs E (ws r'))")
      case True
      with adal new_w' adal_w' w' ws_r
      have "ws r' \<in> new_actions_for P E (ad, al)" "w' \<in> new_actions_for P E (ad, al)"
        by(auto simp add: new_actions_for_def)
      with `E \<in> \<E>` have "ws r' = w'" by(rule \<E>_new_actions_for_fun)
      thus ?thesis using w' by(auto intro: happens_before_refl)
    next
      case False
      with tsa_ok w' ws_r new_w'
      show ?thesis by(auto intro: happens_before_new_not_new)
    qed
  qed
  with `E \<turnstile> w' \<le>a r'` have "w' \<le> r'" by(auto elim!: action_orderE)
  moreover from w' r' have "w' \<noteq> r'" by(auto intro: read_actions_not_write_actions)
  ultimately have "w' < r'" by simp
  with w' have "w' \<in> write_actions E'"
    by(auto intro: write_actions_change_prefix[OF _ eq'])
  hence "w' \<in> actions E'" by simp

  from adal_w' `w' < r'`
  have "(ad, al) \<in> action_loc P E' w'"
    by(subst action_loc_change_prefix[symmetric, OF eq']) simp_all
  from `r' \<in> read_actions E'` `w' \<in> write_actions E'` `(ad, al) \<in> action_loc P E' w'` adal_r''
  have "P,E' \<turnstile> r' \<dagger> w'" unfolding conflict_def by auto
  with sync `E' \<in> \<E>` `P \<turnstile> (E', ws') \<surd>` sc' `r' \<in> actions E'` `w' \<in> actions E'`
  have hb'_r'_w': "P,E' \<turnstile> r' \<le>hb w' \<or> P,E' \<turnstile> w' \<le>hb r'"
    by(rule correctly_synchronizedD[rule_format])
  hence "P,E \<turnstile> r' \<le>hb w' \<or> P,E \<turnstile> w' \<le>hb r'" using `w' < r'`
    by(auto intro: happens_before_change_prefix[OF _ tsa_ok eq'[symmetric]])
  with `\<not> P,E \<turnstile> r' \<le>hb w'` have "P,E \<turnstile> w' \<le>hb r'" by simp

  have "P,E \<turnstile> ws r' \<le>hb w'"
  proof(cases "is_new_action (action_obs E (ws r'))")
    case False
    with `E \<turnstile> ws r' \<le>a r'` have "ws r' \<le> r'" by(auto elim!: action_orderE)
    moreover from ws_r r' have "ws r' \<noteq> r'" by(auto dest: read_actions_not_write_actions)
    ultimately have "ws r' < r'" by simp
    with ws_r have "ws r' \<in> write_actions E'"
      by(auto intro: write_actions_change_prefix[OF _ eq'])
    hence "ws r' \<in> actions E'" by simp

    from adal `ws r' < r'`
    have "(ad, al) \<in> action_loc P E' (ws r')"
      by(subst action_loc_change_prefix[symmetric, OF eq']) simp_all
    hence "P,E' \<turnstile> ws r' \<dagger> w'"
      using `ws r' \<in> write_actions E'` `w' \<in> write_actions E'` `(ad, al) \<in> action_loc P E' w'`
      unfolding conflict_def by auto
    with sync `E' \<in> \<E>` `P \<turnstile> (E', ws') \<surd>` sc' `ws r' \<in> actions E'` `w' \<in> actions E'`
    have "P,E' \<turnstile> ws r' \<le>hb w' \<or> P,E' \<turnstile> w' \<le>hb ws r'"
      by(rule correctly_synchronizedD[rule_format])
    thus "P,E \<turnstile> ws r' \<le>hb w'" using `w' < r'` `ws r' < r'` `\<not> P,E \<turnstile> w' \<le>hb ws r'`
      by(auto dest: happens_before_change_prefix[OF _ tsa_ok eq'[symmetric]])
  next
    case True 
    with tsa_ok ws_r w' `\<not> is_new_action (action_obs E w')`
    show "P,E \<turnstile> ws r' \<le>hb w'" by(auto intro: happens_before_new_not_new)
  qed
  moreover
  from wf have "is_write_seen P E ws" by(rule wf_exec_is_write_seenD)
  ultimately have "w' = ws r'"
    using is_write_seenD[OF `is_write_seen P E ws` `r' \<in> read_actions E` obs_r']
      `w' \<in> write_actions E` `(ad, al) \<in> action_loc P E w'` `P,E \<turnstile> w' \<le>hb r'`
    by auto
  with porder_happens_before[of E P] `\<not> P,E \<turnstile> w' \<le>hb ws r'` ws_r show False
    by(auto dest: refl_onPD[where a="ws r'"] elim!: porder_onE)
qed

lemma justified_action_committedD:
  assumes justified: "P \<turnstile> (E, ws) justified_by J"
  and a: "a \<in> actions E"
  obtains n a' where "a = action_translation (J n) a'" "a' \<in> committed (J n)"
proof(atomize_elim)
  from justified have "actions E = (\<Union>n. action_translation (J n) ` committed (J n))"
    by(simp add: is_justified_by.simps)
  with a show "\<exists>n a'. a = action_translation (J n) a' \<and> a' \<in> committed (J n)" by auto
qed

theorem drf:
  assumes E: "E \<in> \<E>"
  and sync: "correctly_synchronized P \<E>"
  and legal: "legal_execution P \<E> (E, ws)"
  shows "sequentially_consistent P (E, ws)"
using legal_wf_execD[OF legal] E sync
proof(rule drf_lemma)
  fix r
  assume "r \<in> read_actions E"

  from legal obtain J where wf_exec: "P \<turnstile> (E, ws) \<surd>"
    and J: "P \<turnstile> (E, ws) justified_by J"
    and range_J: "range (justifying_exec \<circ> J) \<subseteq> \<E>"
    by(rule legal_executionE)

  let ?E = "\<lambda>n. justifying_exec (J n)"
    and ?ws = "\<lambda>n. justifying_ws (J n)"
    and ?C = "\<lambda>n. committed (J n)"
    and ?\<phi> = "\<lambda>n. action_translation (J n)"
  
  from `r \<in> read_actions E` have "r \<in> actions E" by simp
  with J obtain n r' where r: "r = action_translation (J n) r'"
    and r': "r' \<in> ?C n" by(rule justified_action_committedD)

  note `r \<in> read_actions E`
  moreover from J have wfan: "wf_action_translation_on (?E n) E (?C n) (?\<phi> n)"
    by(simp add: is_justified_by.simps)
  hence "action_obs (?E n) r' \<approx> action_obs E r" using r' unfolding r
    by(blast dest: wf_action_translation_on_actionD)
  moreover from wfan r' have "r' \<in> actions (?E n)"
    by(auto simp add: wf_action_translation_on_def)
  ultimately have "r' \<in> read_actions (?E n)" unfolding r 
    by cases(auto intro: read_actions.intros)
  hence "P,E \<turnstile> ws (?\<phi> n r') \<le>hb ?\<phi> n r'" using `r' \<in> ?C n`
  proof(induct n arbitrary: r')
    case 0
    from J have "?C 0 = {}" by(simp add: is_justified_by.simps)
    with 0 have False by simp
    thus ?case ..
  next
    case (Suc n r)
    note r = `r \<in> read_actions (?E (Suc n))`
    from J have wfan: "wf_action_translation_on (?E n) E (?C n) (?\<phi> n)"
      and wfaSn: "wf_action_translation_on (?E (Suc n)) E (?C (Suc n)) (?\<phi> (Suc n))"
      by(simp_all add: is_justified_by.simps)

    from wfaSn have injSn: "inj_on (?\<phi> (Suc n)) (actions (?E (Suc n)))"
      by(rule wf_action_translation_on_inj_onD)
    from J have C_sub_A: "?C (Suc n) \<subseteq> actions (?E (Suc n))"
      by(simp add: is_justified_by.simps)

    from J have hb_eq: "happens_before P (?E (Suc n)) |` ?C (Suc n) = inv_imageP (happens_before P E) (?\<phi> (Suc n)) |` ?C (Suc n)"
      by(simp add: is_justified_by.simps)
      
    from J have wf: "P \<turnstile> (?E (Suc n), ?ws (Suc n)) \<surd>" by(simp add: is_justified_by.simps)
    moreover from range_J have "?E (Suc n) \<in> \<E>" by auto
    ultimately have "sequentially_consistent P (?E (Suc n), ?ws (Suc n))" using sync
    proof(rule drf_lemma)
      fix r'
      assume r': "r' \<in> read_actions (?E (Suc n))"
      hence "r' \<in> actions (?E (Suc n))" by simp
      
      show "P,?E (Suc n) \<turnstile> ?ws (Suc n) r' \<le>hb r'"
      proof(cases "?\<phi> (Suc n) r' \<in> ?\<phi> n ` ?C n")
        case True
        then obtain r'' where r'': "r'' \<in> ?C n"
          and r'_r'': "?\<phi> (Suc n) r' = ?\<phi> n r''" by(auto)
        from r'' wfan have "action_tid (?E n) r'' = action_tid E (?\<phi> n r'')"
          and "action_obs (?E n) r'' \<approx> action_obs E (?\<phi> n r'')"
          by(blast dest: wf_action_translation_on_actionD)+
        moreover from J have "?\<phi> n ` ?C n \<subseteq> ?\<phi> (Suc n) ` ?C (Suc n)"
          by(simp add: is_justified_by.simps)
        with r'' have "?\<phi> (Suc n) r' \<in> ?\<phi> (Suc n) ` ?C (Suc n)" 
          unfolding r'_r'' by auto
        hence "r' \<in> ?C (Suc n)"
          unfolding inj_on_image_mem_iff[OF injSn C_sub_A `r' \<in> actions (?E (Suc n))`] .
        with wfaSn have "action_tid (?E (Suc n)) r' = action_tid E (?\<phi> (Suc n) r')"
          and "action_obs (?E (Suc n)) r' \<approx> action_obs E (?\<phi> (Suc n) r')"
          by(blast dest: wf_action_translation_on_actionD)+
        ultimately have tid: "action_tid (?E n) r'' = action_tid (?E (Suc n)) r'"
          and obs: "action_obs (?E n) r'' \<approx> action_obs (?E (Suc n)) r'"
          unfolding r'_r'' by(auto intro: sim_action_trans sim_action_sym)
        
        from J have "?C n \<subseteq> actions (?E n)" by(simp add: is_justified_by.simps)
        with r'' have "r'' \<in> actions (?E n)" by blast
        with r' obs have "r'' \<in> read_actions (?E n)"
          by cases(auto intro: read_actions.intros)
        hence hb'': "P,E \<turnstile> ws (?\<phi> n r'') \<le>hb ?\<phi> n r''"
          using `r'' \<in> ?C n` by(rule Suc)

        have r_conv_inv: "r' = inv_into (actions (?E (Suc n))) (?\<phi> (Suc n)) (?\<phi> n r'')"
          using `r' \<in> actions (?E (Suc n))` unfolding r'_r''[symmetric]
          by(simp add: inv_into_f_f[OF injSn])
        with `r'' \<in> ?C n` r' J
        have ws_eq[symmetric]: "?\<phi> (Suc n) (?ws (Suc n) r') = ws (?\<phi> n r'')"
          by(simp add: is_justified_by.simps Let_def)
        with r'_r''[symmetric] hb'' have "P,E \<turnstile> ?\<phi> (Suc n) (?ws (Suc n) r') \<le>hb ?\<phi> (Suc n) r'" by simp
        moreover
        from J r' `r' \<in> committed (J (Suc n))`
        have "?ws (Suc n) r' \<in> ?C (Suc n)"
          and "ws (?\<phi> (Suc n) r') \<in> ?\<phi> (Suc n) ` ?C (Suc n)"
          by(rule justified_write_seen_hb_read_committed)+
        ultimately have "(inv_imageP (happens_before P E) (?\<phi> (Suc n)) |` ?C (Suc n)) (?ws (Suc n) r') r'" 
          using `r' \<in> ?C (Suc n)` by auto
        with hb_eq have "(happens_before P (?E (Suc n)) |` ?C (Suc n)) (?ws (Suc n) r') r'" by simp
        thus ?thesis by auto
      next
        case False
        with J r' show ?thesis
          unfolding is_justified_by.simps by blast
      qed
    qed
    moreover from r have "r \<in> actions (?E (Suc n))" by simp
    moreover let ?w = "inv_into (actions (?E (Suc n))) (?\<phi> (Suc n)) (ws (?\<phi> (Suc n) r))"
    from J r `r \<in> ?C (Suc n)` have ws_rE_comm: "ws (?\<phi> (Suc n) r) \<in> ?\<phi> (Suc n) ` ?C (Suc n)"
      by(rule justified_write_seen_hb_read_committed)
    hence "?w \<in> ?C (Suc n)" using C_sub_A by(auto simp add: inv_into_f_f[OF injSn])
    with C_sub_A have "?w \<in> actions (?E (Suc n))" by blast
    moreover from ws_rE_comm C_sub_A have w_eq: "?\<phi> (Suc n) ?w = ws (?\<phi> (Suc n) r)"
      by(auto simp: f_inv_into_f[where f="?\<phi> (Suc n)"])
    from r obtain ad al v
      where obsr: "action_obs (?E (Suc n)) r = NormalAction (ReadMem ad al v)" by cases
    hence adal_r: "(ad, al) \<in> action_loc P (?E (Suc n)) r" by simp
    from wfaSn `r \<in> ?C (Suc n)`
    have obs_sim: "action_obs (?E (Suc n)) r \<approx> action_obs E (?\<phi> (Suc n) r)" "?\<phi> (Suc n) r \<in> actions E"
      by(blast dest: wf_action_translation_on_actionD)+
    with obsr have rE: "?\<phi> (Suc n) r \<in> read_actions E" by(fastsimp intro: read_actions.intros)
    from obs_sim obsr obtain v' 
      where obsrE: "action_obs E (?\<phi> (Suc n) r) = NormalAction (ReadMem ad al v')" by auto
    from wf_exec have "is_write_seen P E ws" by(rule wf_exec_is_write_seenD)
    from is_write_seenD[OF this rE obsrE]
    have "ws (?\<phi> (Suc n) r) \<in> write_actions E" 
      and "(ad, al) \<in> action_loc P E (ws (?\<phi> (Suc n) r))"
      and nhb: "\<not> P,E \<turnstile> ?\<phi> (Suc n) r \<le>hb ws (?\<phi> (Suc n) r)" by simp_all

    from wf_action_translation_on_actionD[OF wfaSn `?w \<in> ?C (Suc n)`]
    have "action_obs (?E (Suc n)) ?w \<approx> action_obs E (?\<phi> (Suc n) ?w)" by simp
    with w_eq have obs_sim_w: "action_obs (?E (Suc n)) ?w \<approx> action_obs E (ws (?\<phi> (Suc n) r))" by simp
    with `ws (?\<phi> (Suc n) r) \<in> write_actions E` `?w \<in> actions (?E (Suc n))`
    have "?w \<in> write_actions (?E (Suc n))"
      by cases(fastsimp intro: write_actions.intros is_write_action.intros elim!: is_write_action.cases)
    from `(ad, al) \<in> action_loc P E (ws (?\<phi> (Suc n) r))` obs_sim_w 
    have "(ad, al) \<in> action_loc P (?E (Suc n)) ?w" by cases(auto intro: action_loc_aux_intros)
    with r adal_r `?w \<in> write_actions (?E (Suc n))`
    have "P,?E (Suc n) \<turnstile> r \<dagger> ?w" by(auto simp add: conflict_def)
    ultimately have "P,?E (Suc n) \<turnstile> r \<le>hb ?w \<or> P,?E (Suc n) \<turnstile> ?w \<le>hb r"
      by(rule correctly_synchronizedD[rule_format, OF sync `?E (Suc n) \<in> \<E>` wf])
    with `?w \<in> ?C (Suc n)` `r \<in> ?C (Suc n)`
    have "(happens_before P (?E (Suc n)) |` ?C (Suc n)) r ?w \<or> (happens_before P (?E (Suc n)) |` ?C (Suc n)) ?w r" by auto
    with hb_eq have "P,E \<turnstile> ?\<phi> (Suc n) r \<le>hb ?\<phi> (Suc n) ?w \<or> P,E \<turnstile> ?\<phi> (Suc n) ?w \<le>hb ?\<phi> (Suc n) r" by auto
    also note w_eq
    finally show ?case using nhb by simp
  qed
  thus "P,E \<turnstile> ws r \<le>hb r" unfolding r .
qed

end

end
