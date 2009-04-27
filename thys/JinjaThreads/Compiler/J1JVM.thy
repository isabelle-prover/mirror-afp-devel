(*  Title:      JinjaThreads/Compiler/J1JVM.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Correctness of Stage: From intermediate language to JVM} *}

theory J1JVM imports J1JVMBisim begin


lemma bisim1_insync_Throw_exec:
  assumes wf: "wf_prog wf_md P"
  and bisim2: "P,e2,Suc V,h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
  and wt: "P,E \<turnstile>1 e2 :: T2"
  and wt': "P,Env,h \<turnstile>1 Throw ad : T"
  shows "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), xcp) ([Addr ad], loc, 6 + length (compE2 e1) + length (compE2 e2), None)"
proof -
  from wt' have subcls: "P \<turnstile> cname_of h ad \<preceq>\<^sup>* Throwable" by(auto split: heapobj.split_asm simp add: widen_Class)
  from bisim2 have pc: "pc < length (compE2 e2)" and [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
  let ?pc = "6 + length (compE2 e1) + length (compE2 e2)"
  let ?stk = "Addr ad # drop (size stk - 0) stk"
  from bisim2 have "xcp = \<lfloor>ad\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
  thus ?thesis
  proof
    assume [simp]: "xcp = \<lfloor>ad\<rfloor>"
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), \<lfloor>ad\<rfloor>) (?stk, loc, ?pc, None)"
    proof(rule \<tau>Exec1step[unfolded exec_move_def, OF exec_catch])
      from bisim1_xcp_Some_not_caught[OF bisim2[simplified], of compMb2 "Suc (Suc (Suc (length (compE2 e1))))" 0]
      have "match_ex_table (compP2 P) (cname_of h ad) (Suc (Suc (Suc (length (compE2 e1) + pc)))) (compxE2 e2 (Suc (Suc (Suc (length (compE2 e1))))) 0) = None"
	by(simp add: compP2_def)
      thus "match_ex_table (compP2 P) (cname_of h ad) (Suc (Suc (Suc (length (compE2 e1) + pc)))) (compxE2 (sync\<^bsub>V\<^esub> (e1) e2) 0 0) = \<lfloor>(6 + length (compE2 e1) + length (compE2 e2), 0)\<rfloor>"
	using pc subcls
	by(auto simp add: compP2_def match_ex_table_append matches_ex_entry_def nat_number
                dest: match_ex_table_pc_length_compE2)
    qed(insert pc, auto intro: \<tau>move2xcp)
    thus ?thesis by simp
  next
    assume [simp]: "xcp = None"
    with bisim2 wt obtain pc'
      where "\<tau>Exec_move P e2 h (stk, loc, pc, None) ([Addr ad], loc, pc', \<lfloor>ad\<rfloor>)"
      and bisim': "P, e2, Suc V, h \<turnstile> (Throw ad, xs) \<leftrightarrow> ([Addr ad], loc, pc', \<lfloor>ad\<rfloor>)" and [simp]: "xs = loc"
      by(auto dest: bisim1_Throw_\<tau>Exec_move)
    hence "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), None) ([Addr ad], loc, Suc (Suc (Suc (length (compE2 e1) + pc'))), \<lfloor>ad\<rfloor>)"
      by-(rule Insync_\<tau>Exec_meth_xt)
    also let ?stk = "Addr ad # drop (size [Addr ad] - 0) [Addr ad]"
    from bisim' have pc': "pc' < length (compE2 e2)" by(auto dest: bisim1_ThrowD)
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr ad], loc, Suc (Suc (Suc (length (compE2 e1) + pc'))), \<lfloor>ad\<rfloor>) (?stk, loc, ?pc, None)"
    proof(rule \<tau>Exec1step[unfolded exec_move_def, OF exec_catch])
      from bisim1_xcp_Some_not_caught[OF bisim', of compMb2 "Suc (Suc (Suc (length (compE2 e1))))" 0]
      have "match_ex_table (compP2 P) (cname_of h ad) (Suc (Suc (Suc (length (compE2 e1) + pc')))) (compxE2 e2 (Suc (Suc (Suc (length (compE2 e1))))) 0) = None"
	by(simp add: compP2_def)
      thus "match_ex_table (compP2 P) (cname_of h ad) (Suc (Suc (Suc (length (compE2 e1) + pc')))) (compxE2 (sync\<^bsub>V\<^esub> (e1) e2) 0 0) = \<lfloor>(6 + length (compE2 e1) + length (compE2 e2), 0)\<rfloor>"
	using pc' subcls
	by(auto simp add: compP2_def match_ex_table_append matches_ex_entry_def nat_number
                dest: match_ex_table_pc_length_compE2)
    qed(insert pc', auto intro: \<tau>move2xcp)
    finally show ?thesis by simp
  qed
qed

lemma exec_move_length_compE2D [dest]:
  "exec_move P e h (stk, loc, pc, xcp) ta h' s' \<Longrightarrow> pc < length (compE2 e)"
by(cases s')(auto simp add: exec_move_def)

lemma exec_moves_length_compEs2D [dest]:
  "exec_moves P es h (stk, loc, pc, xcp) ta h' s' \<Longrightarrow> pc < length (compEs2 es)"
by(cases s')(auto simp add: exec_moves_def)

lemma assumes wf: "wf_J1_prog P"
  and hconf: "P \<turnstile> h \<surd>"
  shows exec_instr_simulates_red1:
  "\<lbrakk> P, E, n, h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp); P \<turnstile>1 \<langle>e, (h, xs)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle>; P,Env \<turnstile>1 E :: T; P,Env',h \<turnstile>1 e : T' \<rbrakk>
  \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P, E, n, h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
      (if \<tau>move1 e then h = h' \<and> \<tau>Exec_move P E h (stk, loc, pc, xcp) (stk'', loc'', pc'', xcp'')
       else \<exists>ta' pc' stk' loc' xcp'. \<tau>Exec_move P E h (stk, loc, pc, xcp) (stk', loc', pc', xcp') \<and>
                                     exec_move P E h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'') \<and>
                                     \<not> \<tau>move2 E pc' xcp' \<and> ta_bisim (wbisim1 P) ta ta')"
  (is "\<lbrakk> _; _; _; _ \<rbrakk>
       \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. _ \<and> ?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''")

  and exec_instr_simulates_reds1:  
  "\<lbrakk> P, Es, n, h \<turnstile> (es, xs) [\<leftrightarrow>] (stk, loc, pc, xcp); P \<turnstile>1 \<langle>es, (h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es', (h', xs')\<rangle>; P,Env \<turnstile>1 Es [::] Ts; P,Env',h \<turnstile>1 es [:] Ts' \<rbrakk>
  \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P, Es, n, h' \<turnstile> (es', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'') \<and>
      (if \<tau>moves1 es then h = h' \<and> \<tau>Exec_moves P Es h (stk, loc, pc, xcp) (stk'', loc'', pc'', xcp'')
       else \<exists>ta' pc' stk' loc' xcp'. \<tau>Exec_moves P Es h (stk, loc, pc, xcp) (stk', loc', pc', xcp') \<and>
                                     exec_moves P Es h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'') \<and>
                                     \<not> \<tau>moves2 Es pc' xcp' \<and> ta_bisim (wbisim1 P) ta ta')"
  (is "\<lbrakk> _; _; _; _ \<rbrakk>
       \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. _ \<and> ?execs ta Es es h stk loc pc xcp h' pc'' stk'' loc'' xcp''")
proof(induct arbitrary: e' h' xs' Env T Env' T' and es' h' xs' Env Ts Env' Ts' rule: bisim1_bisims1_inducts_split)
  case (bisim1Call1 obj n obj' xs stk loc pc xcp ps M')
  note IHobj = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>obj',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 obj :: T; P,Env',h \<turnstile>1 obj' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,obj,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta obj obj' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note IHparam = `\<And>xs es' h' xs' Env Ts Env' Ts'. \<lbrakk>P \<turnstile>1 \<langle>ps,(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es',(h', xs')\<rangle>; P,Env \<turnstile>1 ps [::] Ts; P,Env',h \<turnstile>1 ps [:] Ts'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,ps,n,h' \<turnstile> (es', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'') \<and>
                  ?execs ta ps ps h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,obj,n,h \<turnstile> (obj', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,ps,n,h \<turnstile> (ps, xs) [\<leftrightarrow>] ([], xs, 0, None)`
  note red = `P \<turnstile>1 \<langle>obj'\<bullet>M'(ps),(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 obj\<bullet>M'(ps) :: T` obtain Tobj Tps
    where wtobj: "P,Env \<turnstile>1 obj :: Tobj" and wtps: "P,Env \<turnstile>1 ps [::] Tps" by auto
  from `P,Env',h \<turnstile>1 obj'\<bullet>M'(ps) : T'` obtain Tobj' Tps'
    where wtobj': "P,Env',h \<turnstile>1 obj' : Tobj'" and wtps': "P,Env',h \<turnstile>1 ps [:] Tps'" by auto
  from red show ?case
  proof(cases)
    case (Call1Obj E s TA E' s' MM es)
    hence [simp]: "E = obj'" "MM = M'" "es = ps" "s = (h, xs)" "s' = (h', xs')" "TA = ta" "e' = E'\<bullet>M'(ps)"
      and red: "P \<turnstile>1 \<langle>obj',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by auto
    from red have \<tau>: "\<tau>move1 obj' = \<tau>move1 (obj'\<bullet>M'(ps))" by(auto intro: \<tau>move1CallObj)
    with IHobj[OF red wtobj wtobj'] bisims1_bsoks[OF bisim2]
    show ?thesis by(fastsimp intro: Call_\<tau>Exec_meth_xtObj bisim1_bisims1.bisim1Call1 exec_move_CallI1)
  next
    case (Call1Params es s TA es' s' v MM)
    hence [simp]: "obj' = Val v" "MM = M'" "es = ps" "s = (h, xs)" "TA = ta" "e' = Val v\<bullet>M'(es')" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>ps, (h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es', (h', xs')\<rangle>" by auto
    from red have \<tau>: "\<tau>move1 (obj'\<bullet>M'(ps)) = \<tau>moves1 ps" by(auto intro: \<tau>move1CallParams)
    from bisim1 wtobj have s: "xcp = None" "lcl s = loc"
      and "\<tau>Exec_move P obj h (stk, loc, pc, xcp) ([v], loc, length (compE2 obj), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (obj\<bullet>M'(es)) h (stk, loc, pc, xcp) ([v], loc, length (compE2 obj), None)"
      by-(rule Call_\<tau>Exec_meth_xtObj)
    moreover from IHparam[OF red wtps wtps'] obtain ta' pc'' stk'' loc'' xcp''
      where bisim': "P,ps,n,h' \<turnstile> (es', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'')"
      and exec': "?execs ta ps ps h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (obj\<bullet>M'(ps)) (obj'\<bullet>M'(ps)) h [v] loc (length (compE2 obj)) None h' (length (compE2 obj) + pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>move1 (obj'\<bullet>M'(ps))")
      case True
      with exec' \<tau> have [simp]: "h = h'" and e: "\<tau>Exec_moves P ps h ([], xs, 0, None) (stk'', loc'', pc'', xcp'')" by auto
      from e have "\<tau>Exec_move P (obj\<bullet>M'(ps)) h ([] @ [v], xs, length (compE2 obj) + 0, None) (stk'' @ [v], loc'', length (compE2 obj) + pc'', xcp'')" by(rule Call_\<tau>Exec_meth_xtParams)
      with s True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain ta' pc' stk' loc' xcp'
	where e: "\<tau>Exec_moves P ps h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_moves P ps h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>moves2 ps pc' xcp'" and ta': "ta_bisim (wbisim1 P) ta ta'" by auto
      from e have "\<tau>Exec_move P (obj\<bullet>M'(ps)) h ([] @ [v], xs, length (compE2 obj) + 0, None) (stk' @ [v], loc', length (compE2 obj) + pc', xcp')" by(rule Call_\<tau>Exec_meth_xtParams)
      moreover from e' have "exec_move P (obj\<bullet>M'(ps)) h (stk' @ [v], loc', length (compE2 obj) + pc', xcp') ta' h' (stk'' @ [v], loc'', length (compE2 obj) + pc'', xcp'')"
	by(rule exec_move_CallI2)
      moreover from \<tau>' e' have "\<tau>move2 (obj\<bullet>M'(es)) (length (compE2 obj) + pc') xcp' \<Longrightarrow> False"
	by -(erule \<tau>move2.cases,auto dest: \<tau>move2_pc_length_compE2 intro: \<tau>moves2xcp)
      ultimately show ?thesis using False s ta' by(force simp del: split_paired_Ex)
    qed
    moreover from bisim' `bsok obj n`
    have "P,obj\<bullet>M'(ps),n,h' \<turnstile> (Val v\<bullet>M'(es'), xs') \<leftrightarrow> ((stk'' @ [v]), loc'', length (compE2 obj) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1CallParams)
    ultimately show ?thesis using \<tau> by(fastsimp elim!: \<tau>Exec_move_trans intro: \<tau>Exec_refl simp del: split_paired_Ex)
  next
    case (Call1ThrowObj a MM es s)
    hence [simp]: "obj' = Throw a" "MM = M'" "es = ps" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw a" "h' = h" "xs' = xs" by auto
    have \<tau>: "\<tau>move1 (Throw a\<bullet>M'(es))" by(rule \<tau>move1CallThrowObj)
    from bisim1 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 bisims1_bsoks[OF bisim2]
      have "P, obj\<bullet>M'(es), n, hp s \<turnstile> (Throw a, lcl s) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1CallThrowObj)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim1 wtobj obtain pc'
	where "\<tau>Exec_move P obj h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, obj, n, hp s \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (obj\<bullet>M'(es)) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule Call_\<tau>Exec_meth_xtObj)
      moreover from bisim' bisims1_bsoks[OF bisim2]
      have "P, obj\<bullet>M'(es), n, hp s \<turnstile> (Throw a, lcl s) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1CallThrowObj, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  next
    case Call1ThrowParams
    with wtps have False by(auto elim: WTs1_append)
    thus ?thesis ..
  next
    case (Red1CallExternal s a Ta M vs TA va H' ta' E' s')
    hence [simp]: "obj' = addr a" "M' = M" "ps = map Val vs" "s = (h, xs)" "ta' = ta" "E' = e'"
      "s' = (h', xs')" "e' = extRet2J va" "H' = h'" "xs' = xs"
      and ta: "ta = extTA2J1 P TA"
      and Ta: "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>"
      and iec: "is_external_call P Ta M (length vs)"
      and redex: "P \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -TA\<rightarrow>ext \<langle>va,h'\<rangle>" by auto
    from bisim1 have [simp]: "xs = loc" by(auto dest: bisim_Val_loc_eq_xcp_None)
    have \<tau>: "\<not> \<tau>move1 (addr a\<bullet>M(map Val vs))" by(fastsimp simp add: map_eq_append_conv)
    from bisim1 wtobj have s: "xcp = None" "lcl s = loc"
      and "\<tau>Exec_move P obj h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 obj), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (obj\<bullet>M(ps)) h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 obj), None)"
      by-(rule Call_\<tau>Exec_meth_xtObj)
    also from wtps have "\<tau>Exec_moves P ps h ([], loc, 0, None) (rev vs, loc, length (compEs2 ps), None)"
      unfolding `ps = map Val vs` by(rule \<tau>Exec_moves_map_Val)
    from Call_\<tau>Exec_meth_xtParams[OF this, of obj M "Addr a"]
    have "\<tau>Exec_move P (obj\<bullet>M(ps)) h ([Addr a], loc, length (compE2 obj), None) (rev vs @ [Addr a], loc, length (compE2 obj) + length (compEs2 ps), None)" by simp
    also let ?ret = "extRet2JVM (length ps) h' (rev vs @ [Addr a]) loc arbitrary arbitrary (length (compE2 obj) + length (compEs2 ps)) [] va"
    let ?stk' = "fst (hd (snd (snd ?ret)))"
    let ?xcp' = "fst ?ret"
    let ?pc' = "snd (snd (snd (snd (hd (snd (snd ?ret))))))"
    from redex have redex': "(TA, va, h') \<in> set (red_external_list (compP2 P) a M vs h)"
      unfolding red_external_list_conv[symmetric] by(simp add: compP2_def)
    from `P,Env',h \<turnstile>1 obj'\<bullet>M'(ps) : T'` Ta iec obtain Ts U
      where wtext: "map typeof\<^bsub>h\<^esub> vs = map Some Ts" "P \<turnstile> Ta\<bullet>M(Ts) :: U"
      by(auto split: heapobj.split_asm simp add: compP2_def)
    with Ta iec redex'
    have "exec_move P (obj\<bullet>M(ps)) h (rev vs @ [Addr a], loc, length (compE2 obj) + length (compEs2 ps), None) (extTA2JVM (compP2 P) TA) h' (?stk', loc, ?pc', ?xcp')"
      unfolding exec_move_def
      by -(rule exec_instr,cases va,(force simp add: compP2_def red_external_list_conv is_Ref_def)+)
    moreover have "\<not> \<tau>move2 (obj\<bullet>M'(ps)) (length (compE2 obj) + length (compEs2 ps)) None"
      by(fastsimp dest: \<tau>move2_pc_length_compE2 \<tau>moves2_pc_length_compEs2 elim: \<tau>move2_cases)
    moreover have "P,obj\<bullet>M(ps),n,h' \<turnstile> (extRet2J1 va, loc) \<leftrightarrow> (?stk', loc, ?pc', ?xcp')"
    proof(cases va)
      case (Inl v)
      from `bsok obj n` `bsoks ps n` have "P,obj\<bullet>M(ps),n,h' \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (obj\<bullet>M(ps))), None)"
	by-(rule bisim1Val2, simp)
      thus ?thesis unfolding Inl by simp
    next
      case (Inr ad)
      with `bsok obj n` `bsoks ps n` show ?thesis by(auto intro: bisim1CallThrow)
    qed
    moreover from Ta have "h a \<noteq> None" by auto
    with ta external_call_hconf[OF redex Ta wtext hconf]
    have "ta_bisim (wbisim1 P) ta (extTA2JVM (compP2 P) TA)" by(auto intro: red_external_ta_bisim21[OF wf redex])
    ultimately show ?thesis using \<tau> by(force simp del: split_paired_Ex)
  next
    case (Red1CallNull MM vs s)
    hence [simp]: "s = (h, xs)" "h' = h" "xs' = xs" "ta = \<epsilon>" "obj' = null" "MM = M'" "ps = map Val vs" "e' = THROW NullPointer" by auto
    have "\<not> \<tau>move1 (null\<bullet>M'(map Val vs))"
      by(rule notI, erule \<tau>move1.cases \<tau>moves1.cases, auto)(drule sym, auto simp add: append_eq_conv_conj drop_map)
    moreover from bisim1 wtobj have s: "xcp = None" "lcl s = loc"
      and "\<tau>Exec_move P obj h (stk, loc, pc, xcp) ([Null], loc, length (compE2 obj), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (obj\<bullet>M'(map Val vs)) h (stk, loc, pc, xcp) ([Null], loc, length (compE2 obj), None)"
      by-(rule Call_\<tau>Exec_meth_xtObj)
    moreover have "\<tau>Exec_moves P (map Val vs) h ([], loc, 0, None) (rev vs, loc, length (compEs2 (map Val vs)), None)"
    proof(cases "vs")
      case Nil thus ?thesis by(auto intro: \<tau>Execs_refl)
    next
      case Cons 
      with bisims1_refl[of "map Val vs" n P "hp s" loc, simplified bsoks_def, simplified] wtps  show ?thesis
	by -(drule bisims1_Val_\<tau>Exec_moves, auto)
    qed
    from Call_\<tau>Exec_meth_xtParams[OF this, of obj M' Null]
    have "\<tau>Exec_move P (obj\<bullet>M'(map Val vs)) h ([Null], loc, length (compE2 obj), None) (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 (map Val vs)), None)" by simp
    moreover have "exec_move P (obj\<bullet>M'(map Val vs)) h (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 (map Val vs)), None) \<epsilon> h (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 (map Val vs)), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(cases vs)(auto intro: exec_instr)
    moreover have "\<tau>move2 (obj\<bullet>M'(map Val vs)) (length (compE2 obj) + length (compEs2 (map Val vs))) None \<Longrightarrow> False"
      by(erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2 \<tau>moves2_pc_length_compEs2)
    moreover from bisim1 have "bsok obj n" by(auto dest: bisim1_bsok)
    hence "P,obj\<bullet>M'(map Val vs),n,hp s \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ((rev vs @ [Null]), loc, length (compE2 obj) + length (compEs2 (map Val vs)), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by-(rule bisim1CallThrow,auto simp add: bsoks_def)
    ultimately show ?thesis using s by(fastsimp elim!: \<tau>Exec_move_trans intro: \<tau>Exec_refl simp del: split_paired_Ex)
  qed auto
next
  case bisim1Val2 thus ?case by fastsimp
next
  case (bisim1New C' n xs)
  have \<tau>: "\<not> \<tau>move1 (new C')" by(auto elim: \<tau>move1.cases)
  from `P \<turnstile>1 \<langle>new C',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Red1New H a C'' FDTs H' XS')
    with `P,Env \<turnstile>1 new C' :: T`
    have "exec_meth (compP2 P) [New C'] [] h ([], xs, 0, None) \<epsilon> h' ([Addr a], xs, Suc 0, None)"
      and [simp]: "e' = addr a" "xs' = xs" "ta = \<epsilon>"
      by(auto intro!: exec_instr simp add: blank_def compP2_def simp del: fun_upd_apply)
    moreover have "P, new C', n, h' \<turnstile> (addr a, xs) \<leftrightarrow> ([Addr a], xs, length (compE2 (new C')), None)"
      by(rule bisim1Val2)(auto)
    moreover have "\<not> \<tau>move2 (new C') 0 None" by(auto elim: \<tau>move2.cases)
    ultimately show ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl simp add: exec_move_def)
  next
    case (Red1NewFail s C'')
    with `P,Env \<turnstile>1 new C' :: T`
    have "exec_meth (compP2 P) [New C'] [] h ([], xs, 0, None) \<epsilon> h ([], xs, 0, \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"
      and [simp]: "ta = \<epsilon>" "s = (h, xs)" "h' = h" "xs' = xs" "e' = THROW OutOfMemory"
      by(auto intro!:exec_instr simp add: blank_def compP2_def simp del: fun_upd_apply)
    moreover have "P, new C', n, h \<turnstile> (THROW OutOfMemory, xs) \<leftrightarrow> ([], xs, 0, \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"
      by(rule bisim1NewThrow)
    moreover have "\<not> \<tau>move2 (new C') 0 None" by(auto elim: \<tau>move2.cases)
    ultimately show ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl simp add: exec_move_def)
  qed auto
next
  case bisim1NewThrow thus ?case by fastsimp
next
  case (bisim1NewArray E n e xs stk loc pc xcp U)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 E :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P \<turnstile>1 \<langle>newA U\<lfloor>e\<rceil>,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 newA U\<lfloor>E\<rceil> :: T` have wtE: "P,Env \<turnstile>1 E :: Integer" and U: "is_type P U" by auto
  from `P,Env',h \<turnstile>1 newA U\<lfloor>e\<rceil> : T'` have wte: "P,Env',h \<turnstile>1 e : Integer" by auto
  from red show ?case
  proof cases
    case (New1ArrayRed ee s TA ee' s' UU)
    hence [simp]: "UU = U" "ee = e" "s = (h, xs)" "TA = ta" "e' = newA U\<lfloor>ee'\<rceil>" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>ee', (h', xs')\<rangle>" by auto
    from red have "\<tau>move1 (newA U\<lfloor>e\<rceil>) = \<tau>move1 e" by(auto intro: \<tau>move1NewArray)
    with IH[OF red wtE wte] show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisim1NewArray exec_move_newArrayI)
  next
    case (Red1NewArray H a i H' UU XS)
    hence [simp]: "UU = U" "e = Val (Intg i)" "H = h" "XS = xs" "ta = \<epsilon>" "e' = addr a" "H' = h'" "xs' = xs"
      "h' = h(a \<mapsto> Arr U (replicate (nat i) (default_val U)))" by auto
    from bisim have s: "xcp = None" "xs = loc" by(auto dest: bisim_Val_loc_eq_xcp_None)
    from bisim wtE have "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([Intg i], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (newA U\<lfloor>E\<rceil>) h (stk, loc, pc, xcp) ([Intg i], loc, length (compE2 E), None)"
      by(rule NewArray_\<tau>Exec_meth_xt)
    moreover from `new_Addr H = \<lfloor>a\<rfloor>` `i \<ge> 0` U
    have "exec_move P (newA U\<lfloor>E\<rceil>) h ([Intg i], loc, length (compE2 E), None) \<epsilon> h' ([Addr a], loc, Suc (length (compE2 E)), None)"
      by(auto intro!: exec_instr simp add: compP2_def exec_move_def)
    moreover have "\<tau>move2 (newA U\<lfloor>E\<rceil>) (length (compE2 E)) None \<Longrightarrow> False"
      by(erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (newA U\<lfloor>Val (Intg i)\<rceil>)" by auto
    moreover from `bsok E n`
    have "P, newA U\<lfloor>E\<rceil>, n, h' \<turnstile> (addr a, loc) \<leftrightarrow> ([Addr a], loc, length (compE2 (newA U\<lfloor>E\<rceil>)), None)"
      by-(rule bisim1Val2, simp)
    ultimately show ?thesis using s by(auto simp del: fun_upd_apply) fastsimp 
  next
    case (Red1NewArrayNegative i UU s)
    hence [simp]: "s = (h, xs)" "UU = U" "e = Val (Intg i)" "e' = THROW NegativeArraySize" "h' = h" "xs' = xs" "ta = \<epsilon>" by auto

    have "\<not> \<tau>move1 (newA U\<lfloor>Val (Intg i)\<rceil>)" by auto
    moreover from bisim wtE have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([Intg i], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    moreover from U `i < 0`
    have "exec_meth (compP2 P) (compE2 (newA U\<lfloor>E\<rceil>)) (compxE2 (newA U\<lfloor>E\<rceil>) 0 0) h ([Intg i], loc, length (compE2 E), None) \<epsilon> h ([Intg i], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt NegativeArraySize\<rfloor>)"
      by -(rule exec_instr, auto simp add: compP2_def)
    moreover have "\<tau>move2 (newA U\<lfloor>E\<rceil>) (length (compE2 E)) None \<Longrightarrow> False"
      by(erule \<tau>move2.cases)(auto elim: \<tau>moves2.cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok E n`
    have "P,newA U\<lfloor>E\<rceil>,n,h \<turnstile> (THROW NegativeArraySize, loc) \<leftrightarrow> ([Intg i], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt NegativeArraySize\<rfloor>)"
      by(auto intro!: bisim1_bisims1.bisim1NewArrayNegative)
    ultimately show ?thesis using s by(auto simp add: exec_move_def) fastsimp
  next
    case (Red1NewArrayFail H i UU XS)
    hence [simp]: "H = h" "XS = xs" "UU = U" "e = Val (Intg i)" "e' = THROW OutOfMemory" "h' = h" "xs' = xs" "ta = \<epsilon>" by auto
    have "\<not> \<tau>move1 (newA U\<lfloor>Val (Intg i)\<rceil>)" by auto
    moreover from bisim wtE have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([Intg i], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    moreover from U `i \<ge> 0` `new_Addr H = None`
    have "exec_meth (compP2 P) (compE2 (newA U\<lfloor>E\<rceil>)) (compxE2 (newA U\<lfloor>E\<rceil>) 0 0) h ([Intg i], loc, length (compE2 E), None) \<epsilon> h ([Intg i], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"
      by -(rule exec_instr, auto simp add: compP2_def)
    moreover have "\<tau>move2 (newA U\<lfloor>E\<rceil>) (length (compE2 E)) None \<Longrightarrow> False"
      by(erule \<tau>move2.cases)(auto elim: \<tau>moves2.cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok E n`
    have "P,newA U\<lfloor>E\<rceil>,n,h \<turnstile> (THROW OutOfMemory, loc) \<leftrightarrow> ([Intg i], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"
      by(auto intro!: bisim1_bisims1.bisim1NewArrayFail)
    ultimately show ?thesis using s by (auto simp add: exec_move_def) fastsimp
  next
    case (New1ArrayThrow UU a s)
    hence [simp]: "UU = U" "e = Throw a" "s = (h, xs)" "h' = h" "xs' = xs" "ta = \<epsilon>" "e' = Throw a" by auto
    have \<tau>: "\<tau>move1 (newA U\<lfloor>e\<rceil>)" by(auto intro: \<tau>move1NewArrayThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim have "P,newA U\<lfloor>E\<rceil>, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.bisim1NewArrayThrow)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim wtE obtain pc'
	where "\<tau>Exec_move P E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (newA U\<lfloor>E\<rceil>) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule NewArray_\<tau>Exec_meth_xt)
      moreover from bisim' have "P, newA U\<lfloor>E\<rceil>, n, hp s \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1_bisims1.bisim1NewArrayThrow, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed simp_all
next
  case bisim1NewArrayThrow thus ?case by auto
next
  case bisim1NewArrayNegative thus ?case by auto
next
  case bisim1NewArrayFail thus ?case by auto
next
  case (bisim1Cast E n e xs stk loc pc xcp U)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 E :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P \<turnstile>1 \<langle>Cast U e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 Cast U E :: T` obtain Te where wtE: "P,Env \<turnstile>1 E :: Te" and U: "is_type P U" by auto
  from `P,Env',h \<turnstile>1 Cast U e : T'` obtain Te' where wte: "P,Env',h \<turnstile>1 e : Te'" by auto
  from red show ?case
  proof cases
    case (Cast1Red ee s TA ee' s' UU)
    hence [simp]: "UU = U" "ee = e" "s = (h, xs)" "TA = ta" "e' = Cast U ee'" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>ee', (h', xs')\<rangle>" by auto
    from red have "\<tau>move1 (Cast U e) = \<tau>move1 e" by(auto intro: \<tau>move1Cast)
    with IH[OF red wtE wte] show ?thesis by(fastsimp intro: bisim1_bisims1.bisim1Cast exec_move_CastI)
  next
    case (Red1Cast s c U' UU)
    hence [simp]: "UU = U" "e = Val c" "s = (h, xs)" "ta = \<epsilon>" "e' = Val c" "h' = h" "xs' = xs"
      and type: "typeof\<^bsub>h\<^esub> c = \<lfloor>U'\<rfloor>" "P \<turnstile> U' \<le> U" by auto
    from bisim have s: "xcp = None" "xs = loc" by(auto dest: bisim_Val_loc_eq_xcp_None)
    from bisim wtE have "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([c], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (Cast U E) h (stk, loc, pc, xcp) ([c], loc, length (compE2 E), None)"
      by(rule Cast_\<tau>Exec_meth_xt)
    moreover from type U
    have "exec_meth (compP2 P) (compE2 (Cast U E)) (compxE2 (Cast U E) 0 0) h ([c], loc, length (compE2 E), None) \<epsilon> h' ([c], loc, Suc (length (compE2 E)), None)"
      by(auto intro!: exec_instr simp add: compP2_def cast_ok_def)
    moreover have "\<tau>move2 (Cast U E) (length (compE2 E)) None \<Longrightarrow> False"
      by(erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (Cast U (Val c))" by auto
    moreover from `bsok E n`
    have "P, Cast U E, n, h' \<turnstile> (Val c, loc) \<leftrightarrow> ([c], loc, length (compE2 (Cast U E)), None)"
      by-(rule bisim1Val2, simp)
    ultimately show ?thesis using s by(auto simp add: exec_move_def) fastsimp 
  next
    case (Red1CastFail s v U' UU)
    hence [simp]: "s = (h, xs)" "UU = U" "e = Val v" "e' = THROW ClassCast" "h' = h" "xs' = xs" "ta = \<epsilon>" by auto
    have "\<not> \<tau>move1 (Cast U (Val c))" by auto
    moreover from bisim wtE have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    moreover from U `typeof\<^bsub>hp s\<^esub> v = \<lfloor>U'\<rfloor>` `\<not> P \<turnstile> U' \<le> UU`
    have "exec_meth (compP2 P) (compE2 (Cast U E)) (compxE2 (Cast U E) 0 0) h ([v], loc, length (compE2 E), None) \<epsilon> h ([v], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt ClassCast\<rfloor>)"
      by -(rule exec_instr, auto simp add: compP2_def cast_ok_def)
    moreover have "\<tau>move2 (Cast U E) (length (compE2 E)) None \<Longrightarrow> False"
      by(erule \<tau>move2.cases)(auto elim: \<tau>moves2.cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok E n`
    have "P,Cast U E,n,h \<turnstile> (THROW ClassCast, loc) \<leftrightarrow> ([v], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt ClassCast\<rfloor>)"
      by(auto intro!: bisim1_bisims1.bisim1CastFail)
    ultimately show ?thesis using s by(auto simp add: exec_move_def) fastsimp
  next
    case (Cast1Throw UU a s)
    hence [simp]: "UU = U" "e = Throw a" "s = (h, xs)" "h' = h" "xs' = xs" "ta = \<epsilon>" "e' = Throw a" by auto
    have \<tau>: "\<tau>move1 (Cast U e)" by(auto intro: \<tau>move1CastThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim have "P,Cast U E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.bisim1CastThrow)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim wtE obtain pc'
	where "\<tau>Exec_move P E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (Cast U E) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule Cast_\<tau>Exec_meth_xt)
      moreover from bisim' have "P, Cast U E, n, hp s \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1_bisims1.bisim1CastThrow, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed simp_all
next
  case bisim1CastThrow thus ?case by auto
next
  case bisim1CastFail thus ?case by auto
next
  case bisim1Val thus ?case by fastsimp
next
  case (bisim1Var V n xs)
  from `P \<turnstile>1 \<langle>Var V,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Red1Var s V' v)
    hence "exec_meth (compP2 P) [Load V] [] h ([], xs, 0, None) \<epsilon> h ([v], xs, 1, None)"
      and [simp]: "ta = \<epsilon>" "s = (h, xs)" "h' = h" "xs' = xs" "e' = Val v"
      by(auto intro: exec_instr)
    moreover have "\<tau>move2 (Var V) 0 None \<Longrightarrow> False" by(auto elim: \<tau>move2.cases)
    moreover have "P, Var V, n, h \<turnstile> (Val v, xs) \<leftrightarrow> ([v], xs, length (compE2 (Var V)), None)"
      by(rule bisim1Val2)(auto)
    moreover have "\<not> \<tau>move1 (Var V)" by(auto elim: \<tau>move1.cases)
    ultimately show ?thesis by(fastsimp intro: \<tau>Exec_refl simp add: exec_move_def)
  qed auto
next
  case (bisim1BinOp1 e1 n e1' xs stk loc pc xcp e2 bop)
  note IH1 = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e1 :: T; P,Env',h \<turnstile>1 e1' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e1,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e1 e1' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note IH2 = `\<And>xs e' h' xs' Env T Env' T'. \<lbrakk>P \<turnstile>1 \<langle>e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e2 :: T; P,Env',h \<turnstile>1 e2 : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta e2 e2 h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,e1,n,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,e2,n,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,Env',h \<turnstile>1 e1' \<guillemotleft>bop\<guillemotright> e2 : T'` obtain T1' T2'
    where wte1': "P,Env',h \<turnstile>1 e1' : T1'"  and wte2': "P,Env',h \<turnstile>1 e2 : T2'" by auto
  from `P,Env \<turnstile>1 e1 \<guillemotleft>bop\<guillemotright> e2 :: T` obtain T1 T2
    where wte1: "P,Env \<turnstile>1 e1 :: T1" and wte2: "P,Env \<turnstile>1 e2 :: T2" by auto
  from `P \<turnstile>1 \<langle>e1' \<guillemotleft>bop\<guillemotright> e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Bin1OpRed1 e s TA E' s' BOP E2)
    hence [simp]: "s = (h, xs)" "TA = ta" "s' = (h', xs')" "e = e1'" "BOP = bop" "E2 = e2" "e' = E' \<guillemotleft>bop\<guillemotright> e2"
      and red: "P \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by simp_all
    from red have "\<tau>move1 (e1' \<guillemotleft>bop\<guillemotright> e2) = \<tau>move1 e1'" by(auto intro: \<tau>move1BinOp1)
    with IH1[OF red wte1 wte1'] bisim1_bsok[OF bisim2] show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisim1BinOp1 exec_move_BinOpI1)
  next
    case (Bin1OpRed2 e s TA E' s' v BOP)
    hence [simp]: "s = (h, xs)" "TA = ta" "s' = (h', xs')" "e = e2" "BOP = bop" "e1' = Val v" "e' = Val v \<guillemotleft>bop\<guillemotright> E'"
      and red: "P \<turnstile>1 \<langle>e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by simp_all
    from red have \<tau>: "\<tau>move1 (Val v \<guillemotleft>bop\<guillemotright> e2) = \<tau>move1 e2" by(auto intro: \<tau>move1BinOp2)
    from bisim1 wte1 have s: "xcp = None" "xs = loc"
      and exec1: "\<tau>Exec_move P (e1\<guillemotleft>bop\<guillemotright>e) h (stk, loc, pc, None) ([v], xs, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    from IH2[OF red wte2 wte2'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e2,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e2 e2 h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (e1\<guillemotleft>bop\<guillemotright>e2) (Val v\<guillemotleft>bop\<guillemotright>e2) h ([] @ [v]) xs (length (compE2 e1) + 0) None h' (length (compE2 e1) + pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>move1 (Val v \<guillemotleft>bop\<guillemotright> e2)")
      case True
      with exec' \<tau> have [simp]: "h = h'" and e: "\<tau>Exec_move P e2 h ([], xs, 0, None) (stk'', loc'', pc'', xcp'')" by auto
      from e have "\<tau>Exec_move P (e1 \<guillemotleft>bop\<guillemotright> e2) h ([] @ [v], xs, length (compE2 e1) + 0, None) (stk'' @ [v], loc'', length (compE2 e1) + pc'', xcp'')" by(rule BinOp_\<tau>Exec_meth_xt2)
      with True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain ta' pc' stk' loc' xcp'
	where e: "\<tau>Exec_move P e2 h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_move P e2 h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 e2 pc' xcp'" and ta': "ta_bisim (wbisim1 P) ta ta'" by auto
      from e have "\<tau>Exec_move P (e1 \<guillemotleft>bop\<guillemotright> e2) h ([] @ [v], xs, length (compE2 e1) + 0, None) (stk' @ [v], loc', length (compE2 e1) + pc', xcp')" by(rule BinOp_\<tau>Exec_meth_xt2)
      moreover from e' have "exec_move P (e1 \<guillemotleft>bop\<guillemotright> e2) h (stk' @ [v], loc', length (compE2 e1) + pc', xcp') ta' h' (stk'' @ [v], loc'', length (compE2 e1) + pc'', xcp'')"
	by(rule exec_move_BinOpI2)
      moreover from e' have "pc' < length (compE2 e2)" by auto
      with \<tau>' have "\<not> \<tau>move2 (e1 \<guillemotleft>bop\<guillemotright> e2) (length (compE2 e1) + pc') xcp'" by auto
      ultimately show ?thesis using False ta' by(fastsimp simp del: split_paired_Ex)
    qed
    with exec1 \<tau> bisim' s bisim1_bsok[OF bisim1] show ?thesis
      by auto(rule exI conjI|erule \<tau>Exec_move_trans bisim1_bisims1.bisim1BinOp2|rule \<tau>Exec_refl|assumption)+
  next
    case (Red1BinOp BOP v1 v2 v s)
    hence [simp]: "e1' = Val v1" "BOP = bop" "e2 = Val v2" "s = (h, xs)" "ta = \<epsilon>" "e' = Val v" "h' = h" "xs' = xs"
      and binop: "binop (bop, v1, v2) = \<lfloor>v\<rfloor>" by auto
    have \<tau>: "\<not> \<tau>move1 (Val v1 \<guillemotleft>bop\<guillemotright> Val v2)" by(auto)
    from bisim1 wte1 have s: "xcp = None" "lcl s = loc"
      and "\<tau>Exec_move P e1 h (stk, loc, pc, xcp) ([v1], loc, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (e1\<guillemotleft>bop\<guillemotright>Val v2) h (stk, loc, pc, xcp) ([v1], loc, length (compE2 e1), None)"
      by-(rule BinOp_\<tau>Exec_meth_xt1)
    also have "\<tau>move2 (e1 \<guillemotleft>bop\<guillemotright> Val v2) (length (compE2 e1) + 0) None"
      by(rule \<tau>move2BinOp2)(rule \<tau>move2Val)
    with binop wte2 have "\<tau>Exec_move P (e1\<guillemotleft>bop\<guillemotright>Val v2) h ([v1], loc, length (compE2 e1), None) ([v2, v1], loc, Suc (length (compE2 e1)), None)"
      by-(rule \<tau>Exec1step, auto intro!: exec_instr simp add: exec_move_def split: bop.split)
    also from binop
    have "exec_meth (compP2 P) (compE2 (e1\<guillemotleft>bop\<guillemotright>Val v2)) (compxE2 (e1\<guillemotleft>bop\<guillemotright>Val v2) 0 0)
                               h ([v2, v1], loc, Suc (length (compE2 e1)), None) \<epsilon>
                               h ([v], loc, Suc (Suc (length (compE2 e1))), None)"
      by-(rule exec_instr, auto simp add: nth_append split: bop.split)
    moreover have "\<tau>move2 (e1\<guillemotleft>bop\<guillemotright>Val v2) (Suc (length (compE2 e1))) None \<Longrightarrow> False" 
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from bisim1_bsok[OF bisim1]
    have "P, e1 \<guillemotleft>bop\<guillemotright> Val v2, n, hp s \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (e1 \<guillemotleft>bop\<guillemotright> Val v2)), None)"
      by-(rule bisim1Val2,auto)
    ultimately show ?thesis using s by(fastsimp simp add: exec_move_def split: bop.split)
  next
    case (Bin1OpThrow1 a BOP E2 s)
    hence [simp]: "e1' = Throw a" "BOP = bop" "E2 = e2" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw a" "h' = h" "xs' = xs" by auto
    have \<tau>: "\<tau>move1 (Throw a \<guillemotleft>bop\<guillemotright> e2)" by(rule \<tau>move1BinOpThrow1)
    from bisim1 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 bisim1_bsok[OF bisim2]
      have "P, e1\<guillemotleft>bop\<guillemotright>e2, n, hp s \<turnstile> (Throw a, lcl s) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.intros)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim1 wte1 obtain pc' where "\<tau>Exec_move P e1 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, e1, n, hp s \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (e1\<guillemotleft>bop\<guillemotright>e2) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule BinOp_\<tau>Exec_meth_xt1)
      moreover from bisim' bisim1_bsok[OF bisim2]
      have "P, e1\<guillemotleft>bop\<guillemotright>e2, n, hp s \<turnstile> (Throw a, lcl s) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1BinOpThrow1)
      ultimately show ?thesis using \<tau> by auto
    qed
  next
    case Bin1OpThrow2 with wte2 have False by auto thus ?thesis ..
  qed simp_all
next
  case (bisim1BinOp2 e2 n e2' xs stk loc pc xcp e1 bop v1)
  note IH2 = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e2 :: T; P,Env',h \<turnstile>1 e2' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e2 e2' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `\<And>xs. P,e1,n,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,e2,n,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P \<turnstile>1 \<langle>Val v1 \<guillemotleft>bop\<guillemotright> e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 e1 \<guillemotleft>bop\<guillemotright> e2 :: T` obtain T1 T2 where wte1: "P,Env \<turnstile>1 e1 :: T1" and wte2: "P,Env \<turnstile>1 e2 :: T2" by auto
  from `P,Env',h \<turnstile>1 Val v1 \<guillemotleft>bop\<guillemotright> e2' : T'` obtain T2' where wte2': "P,Env',h \<turnstile>1 e2' : T2'" by auto
  from red show ?case
  proof cases
    case (Bin1OpRed2 e s TA E' s' v BOP)
    hence [simp]: "s = (h, xs)" "TA = ta" "s' = (h', xs')" "v = v1" "BOP = bop" "e = e2'" "e' = Val v \<guillemotleft>bop\<guillemotright> E'"
      and red: "P \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by simp_all
    from IH2[OF red wte2 wte2'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e2,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e2 e2' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    from red have \<tau>: "\<tau>move1 (Val v1 \<guillemotleft>bop\<guillemotright> e2') = \<tau>move1 e2'" by(auto intro: \<tau>move1BinOp2)
    have "?exec ta (e1\<guillemotleft>bop\<guillemotright>e2) (Val v1\<guillemotleft>bop\<guillemotright>e2') h (stk @ [v]) loc (length (compE2 e1) + pc) xcp h' (length (compE2 e1) + pc'') (stk'' @ [v]) loc'' xcp''"
      using exec' \<tau> by(cases "\<tau>move1 (Val v1 \<guillemotleft>bop\<guillemotright> e2')")(fastsimp intro: BinOp_\<tau>Exec_meth_xt2 exec_move_BinOpI2)+
    with \<tau> bisim' bisim1_bsok[OF bisim1] show ?thesis
      by auto(rule exI conjI|erule \<tau>Exec_move_trans bisim1_bisims1.bisim1BinOp2|rule \<tau>Exec_refl|assumption)+
  next
    case (Red1BinOp BOP V1 v2 v s)
    hence [simp]: "V1 = v1" "BOP = bop" "e2' = Val v2" "s = (h, xs)" "ta = \<epsilon>" "e' = Val v" "h' = h" "xs' = xs"
      and binop: "binop (bop, v1, v2) = \<lfloor>v\<rfloor>" by auto
    have \<tau>: "\<not> \<tau>move1 (Val v1 \<guillemotleft>bop\<guillemotright> Val v2)" by(auto)
    from bisim2 wte2 have s: "xcp = None" "lcl s = loc" 
      and "\<tau>Exec_move P e2 h (stk, loc, pc, xcp) ([v2], loc, length (compE2 e2), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (e1\<guillemotleft>bop\<guillemotright>e2) h (stk @ [v1], loc, length (compE2 e1) + pc, xcp) ([v2] @ [v1], loc, length (compE2 e1) + length (compE2 e2), None)"
      by-(rule BinOp_\<tau>Exec_meth_xt2)
    moreover from binop
    have "exec_move P (e1\<guillemotleft>bop\<guillemotright>e2) h ([v2, v1], loc, length (compE2 e1) + length (compE2 e2), None) \<epsilon>
                                  h ([v], loc, Suc (length (compE2 e1) + length (compE2 e2)), None)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: nth_append split: bop.split)
    moreover have "\<tau>move2 (e1\<guillemotleft>bop\<guillemotright>e2) (length (compE2 e1) + length (compE2 e2)) None \<Longrightarrow> False"
      by(erule \<tau>move2.cases)(auto elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
    moreover from bisim2 have "bsok e2 n" by(auto dest: bisim1_bsok)
    with bisim1_bsok[OF bisim1] have "P, e1 \<guillemotleft>bop\<guillemotright> e2, n, hp s \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (e1 \<guillemotleft>bop\<guillemotright> e2)), None)"
      by-(rule bisim1Val2, auto)
    ultimately show ?thesis using s by(fastsimp split: bop.splits intro!: exI)
  next
    case (Bin1OpThrow2 V1 BOP a s)
    hence [simp]: "V1 = v1" "BOP = bop" "e2' = Throw a" "ta = \<epsilon>" "h' = h" "xs' = xs" "s = (h, xs)" "e' = Throw a" by auto
    have \<tau>: "\<tau>move1 (Val v1 \<guillemotleft>bop\<guillemotright> Throw a)" by(rule \<tau>move1BinOpThrow2)
    from bisim2 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim2 bisim1_bsok[OF bisim1]
      have "P, e1\<guillemotleft>bop\<guillemotright>e2, n, hp s \<turnstile> (Throw a, lcl s) \<leftrightarrow> (stk @ [v1], loc, length (compE2 e1) + pc, xcp)"
	by(auto intro: bisim1BinOpThrow2)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim2 wte2 obtain pc'
	where "\<tau>Exec_move P e2 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, e2, n, hp s \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (e1\<guillemotleft>bop\<guillemotright>e2) h (stk @ [v1], loc, length (compE2 e1) + pc, None) ([Addr a] @ [v1], loc, length (compE2 e1) + pc', \<lfloor>a\<rfloor>)"
	by-(rule BinOp_\<tau>Exec_meth_xt2)
      moreover from bisim' bisim1_bsok[OF bisim1]
      have "P, e1\<guillemotleft>bop\<guillemotright>e2, n, hp s \<turnstile> (Throw a, lcl s) \<leftrightarrow> ([Addr a]@[v1], loc, length (compE2 e1) + pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1BinOpThrow2, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case bisim1BinOpThrow1 thus ?case by fastsimp
next
  case bisim1BinOpThrow2 thus ?case by fastsimp
next
  case (bisim1LAss1 E n e xs stk loc pc xcp V)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 E :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P \<turnstile>1 \<langle>V:=e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 V:=E :: T` obtain TE where wtE: "P,Env \<turnstile>1 E :: TE" by auto
  from `P,Env',h \<turnstile>1 V:=e : T'` obtain Te' where wte: "P,Env',h \<turnstile>1 e : Te'" by auto
  from red show ?case
  proof cases
    case (LAss1Red ee s TA ee' s' VV)
    hence [simp]: "VV = V" "ee = e" "s = (h, xs)" "TA = ta" "e' = V := ee'" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>ee', (h', xs')\<rangle>" by auto
    from red have "\<tau>move1 (V:=e) = \<tau>move1 e" by(auto intro: \<tau>move1LAss)
    with IH[OF red wtE wte] show ?thesis by(fastsimp intro: bisim1_bisims1.bisim1LAss1 exec_move_LAssI)
  next
    case (Red1LAss VV XS v H)
    hence [simp]: "VV = V" "e = Val v" "H = h" "XS = xs" "ta = \<epsilon>" "e' = unit" "h' = h" "xs' = xs[V := v]"
      and V: "V < length xs" by auto
    from bisim have s: "xcp = None" "xs = loc" by(auto dest: bisim_Val_loc_eq_xcp_None)
    from bisim wtE have "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (V:=E) h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      by(rule LAss_\<tau>Exec_meth_xt)
    moreover have "exec_move P (V:=E) h ([v], loc, length (compE2 E), None) \<epsilon> h ([], loc[V := v], Suc (length (compE2 E)), None)"
      using V s by(auto intro: exec_instr simp add: exec_move_def)
    moreover have "\<tau>move2 (V := E) (length (compE2 E)) None \<Longrightarrow> False"
      by(erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (V := Val v)" by auto
    moreover from bisim have "bsok E n" by(auto dest: bisim1_bsok)
    hence "P, V:=E, n, h \<turnstile> (unit, loc[V := v]) \<leftrightarrow> ([], loc[V := v], Suc (length (compE2 E)), None)"
      by(rule bisim1LAss2)
    ultimately show ?thesis using s by auto fastsimp
  next
    case (LAss1Throw VV a s)
    hence [simp]: "VV = V" "e = Throw a" "s = (h, xs)" "h' = h" "xs' = xs" "ta = \<epsilon>" "e' = Throw a" by auto
    have \<tau>: "\<tau>move1 (V:=e)" by(auto intro: \<tau>move1LAssThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim have "P, V:=E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)" by(auto intro: bisim1LAssThrow)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim wtE obtain pc'
	where "\<tau>Exec_move P E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, n, hp s \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (V:=E) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule LAss_\<tau>Exec_meth_xt)
      moreover from bisim' have "P, V:=E, n, hp s \<turnstile> (Throw a, lcl s) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1LAssThrow, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed simp_all
next
  case bisim1LAss2 thus ?case by fastsimp
next
  case bisim1LAssThrow thus ?case by fastsimp
next 
  case (bisim1AAcc1 a n a' xs stk loc pc xcp i)
  note IH1 = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>a',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 a :: T; P,Env',h \<turnstile>1 a' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,a,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta a a' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note IH2 = `\<And>xs e' h' xs' Env T Env' T'. \<lbrakk>P \<turnstile>1 \<langle>i,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 i :: T; P,Env',h \<turnstile>1 i : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,i,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta i i h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,a,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,i,n,h \<turnstile> (i, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,Env',h \<turnstile>1 a'\<lfloor>i\<rceil> : T'` obtain T1'
    where wte1': "P,Env',h \<turnstile>1 a' : T1'" and wte2': "P,Env',h \<turnstile>1 i : Integer" by auto
  from `P,Env \<turnstile>1 a\<lfloor>i\<rceil> :: T` obtain T1
    where wte1: "P,Env \<turnstile>1 a :: T1" and wte2: "P,Env \<turnstile>1 i :: Integer" by auto
  from `P \<turnstile>1 \<langle>a'\<lfloor>i\<rceil>,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (AAcc1Red1 e s TA E' s' I)
    hence [simp]: "s = (h, xs)" "TA = ta" "s' = (h', xs')" "e = a'" "I = i" "e' = E'\<lfloor>i\<rceil>"
      and red: "P \<turnstile>1 \<langle>a',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by simp_all
    from red have "\<tau>move1 (a'\<lfloor>i\<rceil>) = \<tau>move1 a'" by(auto intro: \<tau>move1AAcc1)
    with IH1[OF red wte1 wte1'] `bsok i n` show ?thesis by(fastsimp intro: bisim1_bisims1.bisim1AAcc1 exec_move_AAccI1)
  next
    case (AAcc1Red2 e s TA E' s' v)
    hence [simp]: "s = (h, xs)" "TA = ta" "s' = (h', xs')" "e = i" "a' = Val v" "e' = Val v\<lfloor>E'\<rceil>"
      and red: "P \<turnstile>1 \<langle>i,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by simp_all
    from red have \<tau>: "\<tau>move1 (Val v\<lfloor>i\<rceil>) = \<tau>move1 i" by(auto intro: \<tau>move1AAcc2)
    from bisim1 wte1 have s: "xcp = None" "xs = loc"
      and exec1: "\<tau>Exec_move P (a\<lfloor>i\<rceil>) h (stk, loc, pc, None) ([v], xs, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    from IH2[OF red wte2 wte2'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,i,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta i i h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (a\<lfloor>i\<rceil>) (Val v\<lfloor>i\<rceil>) h ([] @ [v]) xs (length (compE2 a) + 0) None h' (length (compE2 a) + pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>move1 (Val v\<lfloor>i\<rceil>)")
      case True
      with exec' \<tau> have [simp]: "h = h'" and e: "\<tau>Exec_move P i h ([], xs, 0, None) (stk'', loc'', pc'', xcp'')" by auto
      from e have "\<tau>Exec_move P (a\<lfloor>i\<rceil>) h ([] @ [v], xs, length (compE2 a) + 0, None) (stk'' @ [v], loc'', length (compE2 a) + pc'', xcp'')" by(rule AAcc_\<tau>Exec_meth_xt2)
      with True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain ta' pc' stk' loc' xcp'
	where e: "\<tau>Exec_move P i h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_move P i h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 i pc' xcp'" and ta': "ta_bisim (wbisim1 P) ta ta'" by auto
      from e have "\<tau>Exec_move P (a\<lfloor>i\<rceil>) h ([] @ [v], xs, length (compE2 a) + 0, None) (stk' @ [v], loc', length (compE2 a) + pc', xcp')"
	by(rule AAcc_\<tau>Exec_meth_xt2)
      moreover from e' have "exec_move P (a\<lfloor>i\<rceil>) h (stk' @ [v], loc', length (compE2 a) + pc', xcp') ta' h' (stk'' @ [v], loc'', length (compE2 a) + pc'', xcp'')"
	by(rule exec_move_AAccI2)
      moreover from e' \<tau>' have "\<not> \<tau>move2 (a\<lfloor>i\<rceil>) (length (compE2 a) + pc') xcp'" by auto
      ultimately show ?thesis using False ta' by(fastsimp simp del: split_paired_Ex)
    qed
    with exec1 \<tau> bisim' s `bsok a n` show ?thesis
      by auto(rule exI conjI|erule \<tau>Exec_move_trans bisim1_bisims1.bisim1AAcc2|rule \<tau>Exec_refl|assumption)+
  next
    case (Red1AAcc s A U el I)
    hence [simp]: "a' = addr A" "e' = Val (el ! nat I)" "i = Val (Intg I)" "s = (h, xs)" "ta = \<epsilon>" "h' = h" "xs' = xs"
      and hA: "h A = \<lfloor>Arr U el\<rfloor>" and I: "0 \<le> I" "I < int (length el)" by auto
    have \<tau>: "\<not> \<tau>move1 (addr A\<lfloor>Val (Intg I)\<rceil>)" by(auto)
    from bisim1 wte1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P a h (stk, loc, pc, xcp) ([Addr A], loc, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>Val (Intg I)\<rceil>) h (stk, loc, pc, xcp) ([Addr A], loc, length (compE2 a), None)"
      by-(rule AAcc_\<tau>Exec_meth_xt1)
    also have "\<tau>move2 (a\<lfloor>Val (Intg I)\<rceil>) (length (compE2 a) + 0) None"
      by(rule \<tau>move2AAcc2)(rule \<tau>move2Val)
    with wte2 have "\<tau>Exec_move P (a\<lfloor>Val (Intg I)\<rceil>) h ([Addr A], loc, length (compE2 a), None) ([Intg I, Addr A], loc, Suc (length (compE2 a)), None)"
      by-(rule \<tau>Exec1step, auto intro!: exec_instr simp add: exec_move_def)
    also from hA I
    have "exec_move P (a\<lfloor>Val (Intg I)\<rceil>) h ([Intg I, Addr A], loc, Suc (length (compE2 a)), None) \<epsilon>
                                        h ([el ! nat I], loc, Suc (Suc (length (compE2 a))), None)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (a\<lfloor>Val (Intg I)\<rceil>) (Suc (length (compE2 a))) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n`
    have "P, a\<lfloor>Val (Intg I)\<rceil>, n, h \<turnstile> (Val (el ! nat I), loc) \<leftrightarrow> ([el ! nat I], loc, length (compE2 (a\<lfloor>Val (Intg I)\<rceil>)), None)"
      by-(rule bisim1Val2,auto)
    ultimately show ?thesis using s \<tau> by auto fastsimp
  next
    case (Red1AAccNull v s)
    hence [simp]: "a' = null" "i = Val v" "s = (h, xs)" "ta = \<epsilon>" "e' = THROW NullPointer" "h' = h" "xs' = xs" by auto
    from bisim1 wte1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P a h (stk, loc, pc, xcp) ([Null], loc, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil>) h (stk, loc, pc, xcp) ([Null], loc, length (compE2 a), None)"
      by-(rule AAcc_\<tau>Exec_meth_xt1)
    also from bisim2[of loc] wte2 have "\<tau>Exec_move P i h ([], loc, 0, None) ([v], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil>) h ([] @ [Null], loc, length (compE2 a) + 0, None) ([v] @ [Null], loc, length (compE2 a) + length (compE2 i), None)"
      by(rule AAcc_\<tau>Exec_meth_xt2)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil>) h ([Null], loc, length (compE2 a), None) ([v, Null], loc, length (compE2 a) + length (compE2 i), None)" by simp
    also from wte2 have "exec_move P (a\<lfloor>i\<rceil>) h ([v, Null], loc, length (compE2 a) + length (compE2 i), None) \<epsilon> h ([v, Null], loc, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto)
    moreover have "\<not> \<tau>move2 (a\<lfloor>i\<rceil>) (length (compE2 a) + length (compE2 i)) None"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (a'\<lfloor>i\<rceil>)" by(auto)
    moreover from `bsok a n` `bsok i n`
    have "P,a\<lfloor>i\<rceil>,n,h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([v, Null], xs, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAccNull)
    ultimately show ?thesis using s by auto fastsimp
  next
    case (Red1AAccBounds s A U el I)
    hence [simp]: "a' = addr A" "e' = THROW ArrayIndexOutOfBounds" "i = Val (Intg I)"
      "s = (h, xs)" "ta = \<epsilon>" "h' = h" "xs' = xs"
      and hA: "h A = \<lfloor>Arr U el\<rfloor>" and I: "I < 0 \<or> int (length el) \<le> I" by auto
    from bisim1 wte1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P a h (stk, loc, pc, xcp) ([Addr A], loc, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil>) h (stk, loc, pc, xcp) ([Addr A], loc, length (compE2 a), None)"
      by-(rule AAcc_\<tau>Exec_meth_xt1)
    also from bisim2[of loc] wte2 have "\<tau>Exec_move P i h ([], loc, 0, None) ([Intg I], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil>) h ([] @ [Addr A], loc, length (compE2 a) + 0, None) ([Intg I] @ [Addr A], loc, length (compE2 a) + length (compE2 i), None)"
      by(rule AAcc_\<tau>Exec_meth_xt2)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil>) h ([Addr A], loc, length (compE2 a), None) ([Intg I, Addr A], loc, length (compE2 a) + length (compE2 i), None)" by simp
    also from I hA
    have "exec_move P (a\<lfloor>i\<rceil>) h ([Intg I, Addr A], loc, length (compE2 a) + length (compE2 i), None) \<epsilon> h ([Intg I, Addr A], loc, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (a\<lfloor>i\<rceil>) (length (compE2 a) + length (compE2 i)) None"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (a'\<lfloor>i\<rceil>)" by(auto)
    moreover from `bsok a n` `bsok i n`
    have "P,a\<lfloor>i\<rceil>,n,h \<turnstile> (THROW ArrayIndexOutOfBounds, xs) \<leftrightarrow> ([Intg I, Addr A], xs, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAccBounds)
    ultimately show ?thesis using s by auto fastsimp
  next
    case (AAcc1Throw1 A I s)
    hence [simp]: "a' = Throw A" "I = i" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw A" "h' = h" "xs' = xs" by auto
    have \<tau>: "\<tau>move1 (Throw A\<lfloor>i\<rceil>)" by(rule \<tau>move1AAccThrow1)
    from bisim1 have "xcp = \<lfloor>A\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>A\<rfloor>"
      with bisim1 `bsok i n`
      have "P, a\<lfloor>i\<rceil>, n, hp s \<turnstile> (Throw A, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.intros)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim1 wte1 obtain pc' where "\<tau>Exec_move P a h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and bisim': "P, a, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (a\<lfloor>i\<rceil>) h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	by-(rule AAcc_\<tau>Exec_meth_xt1)
      moreover from bisim' `bsok i n`
      have "P, a\<lfloor>i\<rceil>, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1AAccThrow1)
      ultimately show ?thesis using \<tau> by auto
    qed
  next
    case AAcc1Throw2 with wte2 have False by auto thus ?thesis ..
  qed auto
next
  case (bisim1AAcc2 i n i' xs stk loc pc xcp a v1)
  note IH2 = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>i',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 i :: T; P,Env',h \<turnstile>1 i' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,i,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta i i' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `\<And>xs. P,a,n,h \<turnstile> (a, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,i,n,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P \<turnstile>1 \<langle>Val v1\<lfloor>i'\<rceil>,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 a\<lfloor>i\<rceil> :: T` obtain T1 where wte1: "P,Env \<turnstile>1 a :: T1" and wte2: "P,Env \<turnstile>1 i :: Integer" by auto
  from `P,Env',h \<turnstile>1 Val v1\<lfloor>i'\<rceil> : T'` have wte2': "P,Env',h \<turnstile>1 i' : Integer" by auto
  from red show ?case
  proof cases
    case (AAcc1Red2 e s TA E' s' v)
    hence [simp]: "s = (h, xs)" "TA = ta" "s' = (h', xs')" "v = v1" "e = i'" "e' = Val v1\<lfloor>E'\<rceil>"
      and red: "P \<turnstile>1 \<langle>i',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by simp_all
    from IH2[OF red wte2 wte2'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,i,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta i i' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    from red have \<tau>: "\<tau>move1 (Val v1\<lfloor>i'\<rceil>) = \<tau>move1 i'" by(auto intro: \<tau>move1AAcc2)
    have "?exec ta (a\<lfloor>i\<rceil>) (Val v1\<lfloor>i'\<rceil>) h (stk @ [v]) loc (length (compE2 a) + pc) xcp h' (length (compE2 a) + pc'') (stk'' @ [v]) loc'' xcp''"
      using exec' \<tau> by(cases "\<tau>move1 (Val v1\<lfloor>i'\<rceil>)")(fastsimp intro: AAcc_\<tau>Exec_meth_xt2 exec_move_AAccI2)+
    with \<tau> bisim' `bsok a n` show ?thesis
      by auto(rule exI conjI|erule \<tau>Exec_move_trans bisim1_bisims1.bisim1AAcc2|rule \<tau>Exec_refl|assumption)+
  next
    case (Red1AAcc s A U el I)
    hence [simp]: "v1 = Addr A" "e' = Val (el ! nat I)" "i' = Val (Intg I)" "s = (h, xs)" "ta = \<epsilon>" "h' = h" "xs' = xs"
      and hA: "h A = \<lfloor>Arr U el\<rfloor>" and I: "0 \<le> I" "I < int (length el)" by auto
    have \<tau>: "\<not> \<tau>move1 (addr A\<lfloor>Val (Intg I)\<rceil>)" by(auto)
    from bisim2 wte2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P i h (stk, loc, pc, xcp) ([Intg I], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil>) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([Intg I] @ [Addr A], loc, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAcc_\<tau>Exec_meth_xt2)
    moreover from hA I
    have "exec_move P (a\<lfloor>i\<rceil>) h ([Intg I, Addr A], loc, length (compE2 a) + length (compE2 i), None) \<epsilon>
                            h ([el ! nat I], loc, Suc (length (compE2 a) + length (compE2 i)), None)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (a\<lfloor>i\<rceil>) (length (compE2 a) + length (compE2 i)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n` `bsok i n`
    have "P, a\<lfloor>i\<rceil>, n, h \<turnstile> (Val (el ! nat I), loc) \<leftrightarrow> ([el ! nat I], loc, length (compE2 (a\<lfloor>i\<rceil>)), None)"
      by-(rule bisim1Val2,auto)
    ultimately show ?thesis using s \<tau> by auto fastsimp
  next
    case (Red1AAccNull v s)
    hence [simp]: "v1 = Null" "i' = Val v" "s = (h, xs)" "ta = \<epsilon>" "e' = THROW NullPointer" "h' = h" "xs' = xs" by auto
    from bisim2 wte2 have [simp]: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P i h (stk, loc, pc, xcp) ([v], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil>) h (stk @ [Null], loc, length (compE2 a) + pc, xcp) ([v] @ [Null], loc, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAcc_\<tau>Exec_meth_xt2)
    moreover from wte2' have "exec_move P (a\<lfloor>i\<rceil>) h ([v, Null], loc, length (compE2 a) + length (compE2 i), None) \<epsilon> h ([v, Null], loc, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto)
    moreover have "\<not> \<tau>move2 (a\<lfloor>i\<rceil>) (length (compE2 a) + length (compE2 i)) None"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (null\<lfloor>i'\<rceil>)" by(auto)
    moreover from `bsok a n` `bsok i n`
    have "P,a\<lfloor>i\<rceil>,n,h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([v, Null], xs, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAccNull)
    ultimately show ?thesis by auto fastsimp
  next
    case (Red1AAccBounds s A U el I)
    hence [simp]: "v1 = Addr A" "e' = THROW ArrayIndexOutOfBounds" "i' = Val (Intg I)"
      "s = (h, xs)" "ta = \<epsilon>" "h' = h" "xs' = xs"
      and hA: "h A = \<lfloor>Arr U el\<rfloor>" and I: "I < 0 \<or> int (length el) \<le> I" by auto
    from bisim2 wte2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P i h (stk, loc, pc, xcp) ([Intg I], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil>) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([Intg I] @ [Addr A], loc, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAcc_\<tau>Exec_meth_xt2)
    moreover from I hA
    have "exec_move P (a\<lfloor>i\<rceil>) h ([Intg I, Addr A], loc, length (compE2 a) + length (compE2 i), None) \<epsilon> h ([Intg I, Addr A], loc, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (a\<lfloor>i\<rceil>) (length (compE2 a) + length (compE2 i)) None"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (addr A\<lfloor>i'\<rceil>)" by(auto)
    moreover from `bsok a n` `bsok i n`
    have "P,a\<lfloor>i\<rceil>,n,h \<turnstile> (THROW ArrayIndexOutOfBounds, xs) \<leftrightarrow> ([Intg I, Addr A], xs, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAccBounds)
    ultimately show ?thesis using s by auto fastsimp
  next
    case AAcc1Throw1 with wte1 have False by auto thus ?thesis ..
  next
    case (AAcc1Throw2 v A s)
    hence [simp]: "v = v1" "i' = Throw A" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw A" "h' = h" "xs' = xs" by auto
    have \<tau>: "\<tau>move1 (Val v1\<lfloor>Throw A\<rceil>)" by(rule \<tau>move1AAccThrow2)
    from bisim2 have "xcp = \<lfloor>A\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>A\<rfloor>"
      with bisim2 `bsok a n`
      have "P, a\<lfloor>i\<rceil>, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> (stk @ [v], loc, length (compE2 a) + pc, xcp)"
	by(auto intro: bisim1_bisims1.intros)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim2 wte2 obtain pc' where "\<tau>Exec_move P i h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and bisim': "P, i, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (a\<lfloor>i\<rceil>) h (stk @ [v1], loc, length (compE2 a) + pc, None) ([Addr A] @ [v1], loc, length (compE2 a) + pc', \<lfloor>A\<rfloor>)"
	by-(rule AAcc_\<tau>Exec_meth_xt2)
      moreover from bisim' `bsok a n`
      have "P, a\<lfloor>i\<rceil>, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A] @ [v], loc, length (compE2 a) + pc', \<lfloor>A\<rfloor>)"
	by(rule bisim1_bisims1.bisim1AAccThrow2)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case bisim1AAccThrow1 thus ?case by auto
next
  case bisim1AAccThrow2 thus ?case by auto
next
  case bisim1AAccNull thus ?case by auto
next
  case bisim1AAccBounds thus ?case by auto
next
  case (bisim1AAss1 a n a' xs stk loc pc xcp i e)
  note IH1 = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>a',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 a :: T; P,Env',h \<turnstile>1 a' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,a,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta a a' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note IH2 = `\<And>xs e' h' xs' Env T Env' T'. \<lbrakk>P \<turnstile>1 \<langle>i,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 i :: T; P,Env',h \<turnstile>1 i : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,i,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta i i h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note IH3 = `\<And>xs e' h' xs' Env T Env' T'. \<lbrakk>P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta e e h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,a,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,i,n,h \<turnstile> (i, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim3 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,Env',h \<turnstile>1 a'\<lfloor>i\<rceil> := e : T'` obtain T1' T3'
    where wte1': "P,Env',h \<turnstile>1 a' : T1'" and wte2': "P,Env',h \<turnstile>1 i : Integer" 
    and wte3': "P,Env',h \<turnstile>1 e : T3'" by auto
  from `P,Env \<turnstile>1 a\<lfloor>i\<rceil> := e :: T` obtain T1 T3
    where wte1: "P,Env \<turnstile>1 a :: T1" and wte2: "P,Env \<turnstile>1 i :: Integer" and wte3: "P,Env \<turnstile>1 e :: T3" by auto
  from `P \<turnstile>1 \<langle>a'\<lfloor>i\<rceil> := e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (AAss1Red1 aa s TA E' s' I E)
    hence [simp]: "s = (h, xs)" "TA = ta" "s' = (h', xs')" "aa = a'" "I = i" "E = e" "e' = E'\<lfloor>i\<rceil> := e"
      and red: "P \<turnstile>1 \<langle>a',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by simp_all
    from red have "\<tau>move1 (a'\<lfloor>i\<rceil> := e) = \<tau>move1 a'" by(auto intro: \<tau>move1AAss1)
    with wte1 IH1[OF red wte1 wte1'] `bsok i n` `bsok e n`
    show ?thesis by(fastsimp intro: bisim1_bisims1.bisim1AAss1 exec_move_AAssI1)
  next
    case (AAss1Red2 ii s TA E' s' v E)
    hence [simp]: "s = (h, xs)" "TA = ta" "s' = (h', xs')" "ii = i" "a' = Val v" "e' = Val v\<lfloor>E'\<rceil> := e" "E = e"
      and red: "P \<turnstile>1 \<langle>i,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by simp_all
    from red have \<tau>: "\<tau>move1 (Val v\<lfloor>i\<rceil> := e) = \<tau>move1 i" by(auto intro: \<tau>move1AAss2)
    from bisim1 wte1 have s: "xcp = None" "xs = loc"
      and exec1: "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk, loc, pc, None) ([v], xs, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    from IH2[OF red wte2 wte2'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,i,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta i i h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (a\<lfloor>i\<rceil> := e) (Val v\<lfloor>i\<rceil> := e) h ([] @ [v]) xs (length (compE2 a) + 0) None h' (length (compE2 a) + pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>move1 (Val v\<lfloor>i\<rceil> := e)")
      case True
      with exec' \<tau> have [simp]: "h = h'" and e: "\<tau>Exec_move P i h ([], xs, 0, None) (stk'', loc'', pc'', xcp'')" by auto
      from e have "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [v], xs, length (compE2 a) + 0, None) (stk'' @ [v], loc'', length (compE2 a) + pc'', xcp'')" by(rule AAss_\<tau>Exec_meth_xt2)
      with True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain ta' pc' stk' loc' xcp'
	where e: "\<tau>Exec_move P i h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_move P i h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 i pc' xcp'" and ta': "ta_bisim (wbisim1 P) ta ta'" by auto
      from e have "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [v], xs, length (compE2 a) + 0, None) (stk' @ [v], loc', length (compE2 a) + pc', xcp')" by(rule AAss_\<tau>Exec_meth_xt2)
      moreover from e' have "exec_move P (a\<lfloor>i\<rceil> := e) h (stk' @ [v], loc', length (compE2 a) + pc', xcp') ta' h' (stk'' @ [v], loc'', length (compE2 a) + pc'', xcp'')"
	by(rule exec_move_AAssI2)
      moreover from e' have "pc' < length (compE2 i)" by(auto elim: exec_meth.cases)
      with \<tau>' have "\<not> \<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + pc') xcp'" by auto
      ultimately show ?thesis using False ta' by(fastsimp simp add: shift_compxE2 stack_xlift_compxE2 simp del: split_paired_Ex)
    qed
    with exec1 \<tau> bisim' s `bsok a n` `bsok e n` show ?thesis
      by auto(rule exI conjI|erule \<tau>Exec_move_trans bisim1_bisims1.bisim1AAss2|rule \<tau>Exec_refl|assumption)+
  next
    case (AAss1Red3 ee s TA E' s' v v')
    hence [simp]: "s = (h, xs)" "TA = ta" "s' = (h', xs')" "i = Val v'" "a' = Val v" "e' = Val v\<lfloor>Val v'\<rceil> := E'" "ee = e"
      and red: "P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by simp_all
    from red have \<tau>: "\<tau>move1 (Val v\<lfloor>Val v'\<rceil> := e) = \<tau>move1 e" by(auto intro: \<tau>move1AAss3)
    from bisim1 wte1 have s: "xcp = None" "xs = loc"
      and exec1: "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk, loc, pc, None) ([] @ [v], xs, length (compE2 a) + 0, None)"
      by(auto dest: bisim1Val2D1)
    note exec1 also from bisim2[of xs] wte2 have "\<tau>Exec_move P i h ([], xs, 0, None) ([v'], xs, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [v], xs, length (compE2 a) + 0, None) ([v'] @ [v], xs, length (compE2 a) + length (compE2 i), None)"
      by(rule AAss_\<tau>Exec_meth_xt2)
    also from IH3[OF red wte3 wte3'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e e h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (a\<lfloor>i\<rceil> := e) (Val v\<lfloor>Val v'\<rceil> := e) h ([] @ [v', v]) xs (length (compE2 a) + length (compE2 i) + 0) None h' (length (compE2 a) + length (compE2 i) + pc'') (stk'' @ [v', v]) loc'' xcp''"
    proof(cases "\<tau>move1 (Val v\<lfloor>Val v'\<rceil> := e)")
      case True
      with exec' \<tau> have [simp]: "h = h'" and e: "\<tau>Exec_move P e h ([], xs, 0, None) (stk'', loc'', pc'', xcp'')" by auto
      from e have "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [v', v], xs, length (compE2 a) + length (compE2 i) + 0, None) (stk'' @ [v', v], loc'', length (compE2 a) + length (compE2 i) + pc'', xcp'')" by(rule AAss_\<tau>Exec_meth_xt3)
      with True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain ta' pc' stk' loc' xcp'
	where e: "\<tau>Exec_move P e h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_move P e h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 e pc' xcp'" and ta': "ta_bisim (wbisim1 P) ta ta'" by auto
      from e have "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [v', v], xs, length (compE2 a) + length (compE2 i) + 0, None) (stk' @ [v', v], loc', length (compE2 a) + length (compE2 i) + pc', xcp')" by(rule AAss_\<tau>Exec_meth_xt3)
      moreover from e' have "exec_move P (a\<lfloor>i\<rceil> := e) h (stk' @ [v', v], loc', length (compE2 a) + length (compE2 i) + pc', xcp') ta' h' (stk'' @ [v', v], loc'', length (compE2 a) + length (compE2 i) + pc'', xcp'')"
	by(rule exec_move_AAssI3)
      moreover from e' \<tau>' have "\<not> \<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + pc') xcp'"
	by(auto simp del: `i = Val v'`)
      ultimately show ?thesis using False ta' by(fastsimp simp add: shift_compxE2 stack_xlift_compxE2 simp del: split_paired_Ex)
    qed
    ultimately show ?thesis using \<tau> bisim' s `bsok a n` `bsok i n` s
      by auto (rule exI conjI|erule \<tau>Exec_move_trans bisim1_bisims1.bisim1AAss3|rule \<tau>Exec_refl|assumption|simp)+
  next
    case (Red1AAss H A U el I v U' H' XS)
    hence [simp]: "a' = addr A" "e' = unit" "i = Val (Intg I)" "H = h" "XS = xs" "ta = \<epsilon>" "H' = h'" "xs' = xs" "e = Val v"
      and hA: "h A = \<lfloor>Arr U el\<rfloor>" and I: "0 \<le> I" "I < int (length el)" and v: "typeof\<^bsub>h\<^esub> v = \<lfloor>U'\<rfloor>" "P \<turnstile> U' \<le> U"
      and h': "h' = h(A \<mapsto> Arr U (el[nat I := v]))" by auto
    have \<tau>: "\<not> \<tau>move1 (AAss (addr A) (Val (Intg I)) (Val v))" by(auto)
    from bisim1 wte1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P a h (stk, loc, pc, xcp) ([] @ [Addr A], loc, length (compE2 a) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk, loc, pc, xcp) ([] @ [Addr A], loc, length (compE2 a) + 0, None)"
      by-(rule AAss_\<tau>Exec_meth_xt1)
    also from bisim2[of loc] wte2 have "\<tau>Exec_move P i h ([], loc, 0, None) ([Intg I], loc, length (compE2 i) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [Addr A], loc, length (compE2 a) + 0, None) ([Intg I] @ [Addr A], loc, length (compE2 a) + (length (compE2 i) + 0), None)"
      by(rule AAss_\<tau>Exec_meth_xt2)
    also have "[Intg I] @ [Addr A] = [] @ [Intg I, Addr A]" by simp
    also note add_assoc[symmetric]
    also from bisim3[of loc] wte3 have "\<tau>Exec_move P e h ([], loc, 0, None) ([v], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>Exec_meth_xt3)
    also from hA I v h'
    have "exec_move P (a\<lfloor>i\<rceil> := e) h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h' ([], loc, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: cast_ok_def compP2_def is_Ref_def)
    moreover have "\<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (unit, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"
      by(rule bisim1_bisims1.bisim1AAss4)
    ultimately show ?thesis using s \<tau> by auto fastsimp
  next
    case (Red1AAssNull v v' s)
    hence [simp]: "a' = null" "e' = THROW NullPointer" "i = Val v" "s = (h, xs)" "xs' = xs" "ta = \<epsilon>" "h' = h" "e = Val v'" by auto
    have \<tau>: "\<not> \<tau>move1 (AAss null (Val v) (Val v'))" by(auto)
    from bisim1 wte1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P a h (stk, loc, pc, xcp) ([] @ [Null], loc, length (compE2 a) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk, loc, pc, xcp) ([] @ [Null], loc, length (compE2 a) + 0, None)"
      by-(rule AAss_\<tau>Exec_meth_xt1)
    also from bisim2[of loc] wte2 have "\<tau>Exec_move P i h ([], loc, 0, None) ([v], loc, length (compE2 i) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [Null], loc, length (compE2 a) + 0, None) ([v] @ [Null], loc, length (compE2 a) + (length (compE2 i) + 0), None)"
      by(rule AAss_\<tau>Exec_meth_xt2)
    also have "[v] @ [Null] = [] @ [v, Null]" by simp
    also note add_assoc[symmetric]
    also from bisim3[of loc] wte3 have "\<tau>Exec_move P e h ([], loc, 0, None) ([v'], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [v, Null], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v'] @ [v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>Exec_meth_xt3)
    also from wte2
    have "exec_move P (a\<lfloor>i\<rceil> := e) h ([v', v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([v', v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([v', v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssNull)
    ultimately show ?thesis using s \<tau> by auto fastsimp
  next
    case (Red1AAssBounds s A U el I v)
    hence [simp]: "a' = addr A" "e' = THROW ArrayIndexOutOfBounds" "i = Val (Intg I)" "s = (h, xs)" "xs' = xs" "ta = \<epsilon>" "h' = h" "e = Val v"
      and hA: "h A = \<lfloor>Arr U el\<rfloor>" and I: "I < 0 \<or> int (length el) \<le> I" by auto
    have \<tau>: "\<not> \<tau>move1 (AAss (addr A) i e)" by(auto)
    from bisim1 wte1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P a h (stk, loc, pc, xcp) ([] @ [Addr A], loc, length (compE2 a) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk, loc, pc, xcp) ([] @ [Addr A], loc, length (compE2 a) + 0, None)"
      by-(rule AAss_\<tau>Exec_meth_xt1)
    also from bisim2[of loc] wte2 have "\<tau>Exec_move P i h ([], loc, 0, None) ([Intg I], loc, length (compE2 i) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [Addr A], loc, length (compE2 a) + 0, None) ([Intg I] @ [Addr A], loc, length (compE2 a) + (length (compE2 i) + 0), None)"
      by(rule AAss_\<tau>Exec_meth_xt2)
    also have "[Intg I] @ [Addr A] = [] @ [Intg I, Addr A]" by simp
    also note add_assoc[symmetric]
    also from bisim3[of loc] wte3 have "\<tau>Exec_move P e h ([], loc, 0, None) ([v], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>Exec_meth_xt3)
    also from hA I
    have "exec_move P (a\<lfloor>i\<rceil> := e) h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW ArrayIndexOutOfBounds, loc) \<leftrightarrow> ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssBounds)
    ultimately show ?thesis using s \<tau> by auto fastsimp
  next
    case (Red1AAssStore s A U el I v U')
    hence [simp]: "a' = addr A" "e' = THROW ArrayStore" "i = Val (Intg I)" "s = (h, xs)" "xs' = xs" "ta = \<epsilon>" "h' = h" "e = Val v"
      and hA: "h A = \<lfloor>Arr U el\<rfloor>" and I: "0 \<le> I" "I < int (length el)" and U: "\<not> P \<turnstile> U' \<le> U" "typeof\<^bsub>h\<^esub> v = \<lfloor>U'\<rfloor>" by auto
    have \<tau>: "\<not> \<tau>move1 (AAss (addr A) i e)" by(auto)
    from bisim1 wte1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P a h (stk, loc, pc, xcp) ([] @ [Addr A], loc, length (compE2 a) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk, loc, pc, xcp) ([] @ [Addr A], loc, length (compE2 a) + 0, None)"
      by-(rule AAss_\<tau>Exec_meth_xt1)
    also from bisim2[of loc] wte2 have "\<tau>Exec_move P i h ([], loc, 0, None) ([Intg I], loc, length (compE2 i) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [Addr A], loc, length (compE2 a) + 0, None) ([Intg I] @ [Addr A], loc, length (compE2 a) + (length (compE2 i) + 0), None)"
      by(rule AAss_\<tau>Exec_meth_xt2)
    also have "[Intg I] @ [Addr A] = [] @ [Intg I, Addr A]" by simp
    also note add_assoc[symmetric]
    also from bisim3[of loc] wte3 have "\<tau>Exec_move P e h ([], loc, 0, None) ([v], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>Exec_meth_xt3)
    also from hA I U
    have "exec_move P (a\<lfloor>i\<rceil> := e) h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                  h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def cast_ok_def compP2_def)
    moreover have "\<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW ArrayStore, loc) \<leftrightarrow> ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssStore)
    ultimately show ?thesis using s \<tau> by auto fastsimp
  next
    case (AAss1Throw1 A I E s)
    hence [simp]: "a' = Throw A" "I = i" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw A" "h' = h" "xs' = xs" "E = e" by auto
    have \<tau>: "\<tau>move1 (Throw A\<lfloor>i\<rceil> := e)" by(rule \<tau>move1AAssThrow1)
    from bisim1 have "xcp = \<lfloor>A\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>A\<rfloor>"
      with bisim1 `bsok i n` `bsok e n`
      have "P, a\<lfloor>i\<rceil> := e, n, hp s \<turnstile> (Throw A, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.intros)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim1 wte1 obtain pc' where "\<tau>Exec_move P a h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and bisim': "P, a, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	by-(rule AAss_\<tau>Exec_meth_xt1)
      moreover from bisim' `bsok i n` `bsok e n`
      have "P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1AAssThrow1)
      ultimately show ?thesis using \<tau> by auto
    qed
  next
    case AAss1Throw2 with wte2 have False by auto thus ?thesis ..
  next
    case AAss1Throw3 with wte3 have False by auto thus ?thesis ..
  qed auto
next
  case (bisim1AAss2 i n i' xs stk loc pc xcp a e v1)
  note IH2 = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>i',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 i :: T; P,Env',h \<turnstile>1 i' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,i,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta i i' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note IH3 = `\<And>xs e' h' xs' Env T Env' T'. \<lbrakk>P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta e e h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note bisim2 = `P,i,n,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim1 = `\<And>xs. P,a,n,h \<turnstile> (a, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim3 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,Env',h \<turnstile>1 Val v1\<lfloor>i'\<rceil> := e : T'` obtain T1' T3'
    where wte1': "P,Env',h \<turnstile>1 Val v1 : T1'" and wte2': "P,Env',h \<turnstile>1 i' : Integer" 
    and wte3': "P,Env',h \<turnstile>1 e : T3'" by auto
  from `P,Env \<turnstile>1 a\<lfloor>i\<rceil> := e :: T` obtain T1 T3
    where wte1: "P,Env \<turnstile>1 a :: T1" and wte2: "P,Env \<turnstile>1 i :: Integer" and wte3: "P,Env \<turnstile>1 e :: T3" by auto
  from `P \<turnstile>1 \<langle>Val v1\<lfloor>i'\<rceil> := e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (AAss1Red2 ii s TA E' s' v E)
    hence [simp]: "s = (h, xs)" "TA = ta" "s' = (h', xs')" "ii = i'" "v = v1" "E = e" "e' = Val v1\<lfloor>E'\<rceil> := e"
      and red: "P \<turnstile>1 \<langle>i',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by simp_all
    from red have \<tau>: "\<tau>move1 (Val v1\<lfloor>i'\<rceil> := e) = \<tau>move1 i'" by(auto intro: \<tau>move1AAss2)
    from IH2[OF red wte2 wte2'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,i,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta i i' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (a\<lfloor>i\<rceil> := e) (Val v1\<lfloor>i'\<rceil> := e) h (stk @ [v1]) loc (length (compE2 a) + pc) xcp h' (length (compE2 a) + pc'') (stk'' @ [v1]) loc'' xcp''"
    proof(cases "\<tau>move1 (Val v1\<lfloor>i'\<rceil> := e)")
      case True
      with exec' \<tau> have [simp]: "h = h'" and e: "\<tau>Exec_move P i h (stk, loc, pc, xcp) (stk'', loc'', pc'', xcp'')" by auto
      from e have "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [v1], loc, length (compE2 a) + pc, xcp) (stk'' @ [v1], loc'', length (compE2 a) + pc'', xcp'')" by(rule AAss_\<tau>Exec_meth_xt2)
      with True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain ta' pc' stk' loc' xcp'
	where e: "\<tau>Exec_move P i h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
	and e': "exec_move P i h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 i pc' xcp'" and ta': "ta_bisim (wbisim1 P) ta ta'" by auto
      from e have "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [v1], loc, length (compE2 a) + pc, xcp) (stk' @ [v1], loc', length (compE2 a) + pc', xcp')" by(rule AAss_\<tau>Exec_meth_xt2)
      moreover from e' have "exec_move P (a\<lfloor>i\<rceil> := e) h (stk' @ [v1], loc', length (compE2 a) + pc', xcp') ta' h' (stk'' @ [v1], loc'', length (compE2 a) + pc'', xcp'')"
	by(rule exec_move_AAssI2)
      moreover from e' have "pc' < length (compE2 i)" by(auto elim: exec_meth.cases)
      with \<tau>' have "\<not> \<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + pc') xcp'" by auto
      ultimately show ?thesis using False ta' by(fastsimp simp add: shift_compxE2 stack_xlift_compxE2 simp del: split_paired_Ex)
    qed
    with \<tau> bisim' `bsok a n` `bsok e n` show ?thesis
      by auto(rule exI conjI|erule \<tau>Exec_move_trans bisim1_bisims1.bisim1AAss2|rule \<tau>Exec_refl|assumption)+
  next
    case (AAss1Red3 ee s TA E' s' v v')
    hence [simp]: "s = (h, xs)" "TA = ta" "s' = (h', xs')" "i' = Val v'" "v1 = v" "e' = Val v\<lfloor>Val v'\<rceil> := E'" "ee = e"
      and red: "P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by simp_all
    from red have \<tau>: "\<tau>move1 (Val v\<lfloor>Val v'\<rceil> := e) = \<tau>move1 e" by(auto intro: \<tau>move1AAss3)
    from bisim2 wte2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P i h (stk, loc, pc, xcp) ([v'], xs, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [v], loc, length (compE2 a) + pc, xcp) ([v'] @ [v], xs, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAss_\<tau>Exec_meth_xt2)
    moreover from IH3[OF red wte3 wte3'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e e h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (a\<lfloor>i\<rceil> := e) (Val v\<lfloor>Val v'\<rceil> := e) h ([] @ [v', v]) xs (length (compE2 a) + length (compE2 i) + 0) None h' (length (compE2 a) + length (compE2 i) + pc'') (stk'' @ [v', v]) loc'' xcp''"
    proof(cases "\<tau>move1 (Val v\<lfloor>Val v'\<rceil> := e)")
      case True
      with exec' \<tau> have [simp]: "h = h'" and e: "\<tau>Exec_move P e h ([], xs, 0, None) (stk'', loc'', pc'', xcp'')" by auto
      from e have "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [v', v], xs, length (compE2 a) + length (compE2 i) + 0, None) (stk'' @ [v', v], loc'', length (compE2 a) + length (compE2 i) + pc'', xcp'')" by(rule AAss_\<tau>Exec_meth_xt3)
      with True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain ta' pc' stk' loc' xcp'
	where e: "\<tau>Exec_move P e h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_move P e h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 e pc' xcp'" and ta': "ta_bisim (wbisim1 P) ta ta'" by auto
      from e have "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [v', v], xs, length (compE2 a) + length (compE2 i) + 0, None) (stk' @ [v', v], loc', length (compE2 a) + length (compE2 i) + pc', xcp')" by(rule AAss_\<tau>Exec_meth_xt3)
      moreover from e' have "exec_move P (a\<lfloor>i\<rceil> := e) h (stk' @ [v', v], loc', length (compE2 a) + length (compE2 i) + pc', xcp') ta' h' (stk'' @ [v', v], loc'', length (compE2 a) + length (compE2 i) + pc'', xcp'')"
	by(rule exec_move_AAssI3)
      moreover from e' \<tau>' have "\<not> \<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + pc') xcp'" by(auto)
      ultimately show ?thesis using False ta' by(fastsimp simp add: shift_compxE2 stack_xlift_compxE2 simp del: split_paired_Ex)
    qed
    ultimately show ?thesis using \<tau> bisim' s `bsok a n` `bsok i n` s
      by auto (rule exI conjI|erule \<tau>Exec_move_trans bisim1_bisims1.bisim1AAss3|rule \<tau>Exec_refl|assumption|simp)+
  next
    case (Red1AAss H A U el I v U' H' XS)
    hence [simp]: "v1 = Addr A" "e' = unit" "i' = Val (Intg I)" "H = h" "XS = xs" "ta = \<epsilon>" "H' = h'" "xs' = xs" "e = Val v"
      and hA: "h A = \<lfloor>Arr U el\<rfloor>" and I: "0 \<le> I" "I < int (length el)" and v: "typeof\<^bsub>h\<^esub> v = \<lfloor>U'\<rfloor>" "P \<turnstile> U' \<le> U"
      and h': "h' = h(A \<mapsto> Arr U (el[nat I := v]))" by auto
    have \<tau>: "\<not> \<tau>move1 (AAss (addr A) (Val (Intg I)) (Val v))" by(auto)
    from bisim2 wte2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P i h (stk, loc, pc, xcp) ([Intg I], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([Intg I] @ [Addr A], loc, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAss_\<tau>Exec_meth_xt2)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None)" by simp
    also from bisim3[of loc] wte3 have "\<tau>Exec_move P e h ([], loc, 0, None) ([v], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>Exec_meth_xt3)
    also from hA I v h'
    have "exec_move P (a\<lfloor>i\<rceil> := e) h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h' ([], loc, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: cast_ok_def compP2_def is_Ref_def)
    moreover have "\<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (unit, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"
      by(rule bisim1_bisims1.bisim1AAss4)
    ultimately show ?thesis using s \<tau> by auto fastsimp
  next
    case (Red1AAssNull v v' s)
    hence [simp]: "v1 = Null" "e' = THROW NullPointer" "i' = Val v" "s = (h, xs)" "xs' = xs" "ta = \<epsilon>" "h' = h" "e = Val v'" by auto
    have \<tau>: "\<not> \<tau>move1 (AAss null (Val v) (Val v'))" by(auto)
    from bisim2 wte2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P i h (stk, loc, pc, xcp) ([v], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [Null], loc, length (compE2 a) + pc, xcp) ([v] @ [Null], loc, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAss_\<tau>Exec_meth_xt2)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [Null], loc, length (compE2 a) + pc, xcp) ([] @ [v, Null], loc, length (compE2 a) + length (compE2 i) + 0, None)" by simp
    also from bisim3[of loc] wte3 have "\<tau>Exec_move P e h ([], loc, 0, None) ([v'], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [v, Null], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v'] @ [v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>Exec_meth_xt3)
    also from wte2'
    have "exec_move P (a\<lfloor>i\<rceil> := e) h ([v', v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([v', v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([v', v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssNull)
    ultimately show ?thesis using s \<tau> by auto fastsimp
  next
    case (Red1AAssBounds s A U el I v)
    hence [simp]: "v1 = Addr A" "e' = THROW ArrayIndexOutOfBounds" "i' = Val (Intg I)" "s = (h, xs)" "xs' = xs" "ta = \<epsilon>" "h' = h" "e = Val v"
      and hA: "h A = \<lfloor>Arr U el\<rfloor>" and I: "I < 0 \<or> int (length el) \<le> I" by auto
    have \<tau>: "\<not> \<tau>move1 (addr A\<lfloor>i'\<rceil> := e)" by(auto)
    from bisim2 wte2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P i h (stk, loc, pc, xcp) ([Intg I], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([Intg I] @ [Addr A], loc, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAss_\<tau>Exec_meth_xt2)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None)" by simp
    also from bisim3[of loc] wte3 have "\<tau>Exec_move P e h ([], loc, 0, None) ([v], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>Exec_meth_xt3)
    also from hA I
    have "exec_move P (a\<lfloor>i\<rceil> := e) h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW ArrayIndexOutOfBounds, loc) \<leftrightarrow> ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssBounds)
    ultimately show ?thesis using s \<tau> by auto fastsimp
  next
    case (Red1AAssStore s A U el I v U')
    hence [simp]: "v1 = Addr A" "e' = THROW ArrayStore" "i' = Val (Intg I)" "s = (h, xs)" "xs' = xs" "ta = \<epsilon>" "h' = h" "e = Val v"
      and hA: "h A = \<lfloor>Arr U el\<rfloor>" and I: "0 \<le> I" "I < int (length el)" and U: "\<not> P \<turnstile> U' \<le> U" "typeof\<^bsub>h\<^esub> v = \<lfloor>U'\<rfloor>" by auto
    have \<tau>: "\<not> \<tau>move1 (addr A\<lfloor>i'\<rceil> := e)" by(auto)
    from bisim2 wte2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P i h (stk, loc, pc, xcp) ([Intg I], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([Intg I] @ [Addr A], loc, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAss_\<tau>Exec_meth_xt2)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None)" by simp
    also from bisim3[of loc] wte3 have "\<tau>Exec_move P e h ([], loc, 0, None) ([v], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>Exec_meth_xt3)
    also from hA I U
    have "exec_move P (a\<lfloor>i\<rceil> := e) h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>)"
      unfolding exec_move_def by- (rule exec_instr, auto simp add: is_Ref_def cast_ok_def compP2_def)
    moreover have "\<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW ArrayStore, loc) \<leftrightarrow> ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssStore)
    ultimately show ?thesis using s \<tau> by auto fastsimp
  next
    case (AAss1Throw2 aa A E s)
    hence [simp]: "aa = v1" "i' = Throw A" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw A" "h' = h" "xs' = xs" "E = e" by auto
    have \<tau>: "\<tau>move1 (Val v1\<lfloor>Throw A\<rceil> := e)" by(rule \<tau>move1AAssThrow2)
    from bisim2 have "xcp = \<lfloor>A\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>A\<rfloor>"
      with bisim2 `bsok a n` `bsok e n`
      have "P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> (stk @ [v1], loc, length (compE2 a) + pc, xcp)"
	by(auto intro: bisim1_bisims1.intros)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim2 wte2 obtain pc' where "\<tau>Exec_move P i h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and bisim': "P, i, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [v1], loc, length (compE2 a) + pc, None) ([Addr A] @ [v1], loc, length (compE2 a) + pc', \<lfloor>A\<rfloor>)"
	by-(rule AAss_\<tau>Exec_meth_xt2)
      moreover from bisim' `bsok a n` `bsok e n`
      have "P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A] @ [v1], loc, length (compE2 a) +  pc', \<lfloor>A\<rfloor>)"
	by(rule bisim1_bisims1.bisim1AAssThrow2)
      ultimately show ?thesis using \<tau> by auto
    qed
  next
    case AAss1Throw3 with wte3 have False by auto thus ?thesis ..
  qed auto
next
  case (bisim1AAss3 e n ee xs stk loc pc xcp a i v v')
  note IH3 = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>ee,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e :: T; P,Env',h \<turnstile>1 ee : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e ee h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim3 = `P,e,n,h \<turnstile> (ee, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  from `P,Env',h \<turnstile>1 Val v\<lfloor>Val v'\<rceil> := ee : T'` obtain T1' T3'
    where wte1': "P,Env',h \<turnstile>1 Val v : T1'" and wte2': "P,Env',h \<turnstile>1 Val v' : Integer" 
    and wte3': "P,Env',h \<turnstile>1 ee : T3'" by auto
  from `P,Env \<turnstile>1 a\<lfloor>i\<rceil> := e :: T` obtain T1 T3
    where wte1: "P,Env \<turnstile>1 a :: T1" and wte2: "P,Env \<turnstile>1 i :: Integer" and wte3: "P,Env \<turnstile>1 e :: T3" by auto
  from `P \<turnstile>1 \<langle>Val v\<lfloor>Val v'\<rceil> := ee,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (AAss1Red3 eee s TA E' s' V V')
    hence [simp]: "s = (h, xs)" "TA = ta" "s' = (h', xs')" "V' = v'" "V = v" "e' = Val v\<lfloor>Val v'\<rceil> := E'" "eee = ee"
      and red: "P \<turnstile>1 \<langle>ee,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by simp_all
    from red have \<tau>: "\<tau>move1 (Val v\<lfloor>Val v'\<rceil> := ee) = \<tau>move1 ee" by(auto intro: \<tau>move1AAss3)
    from IH3[OF red wte3 wte3'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e ee h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (a\<lfloor>i\<rceil> := e) (Val v\<lfloor>Val v'\<rceil> := ee) h (stk @ [v', v]) loc (length (compE2 a) + length (compE2 i) + pc) xcp h' (length (compE2 a) + length (compE2 i) + pc'') (stk'' @ [v', v]) loc'' xcp''"
      using exec' \<tau> by(cases "\<tau>move1 (Val v\<lfloor>Val v'\<rceil> := ee)")(fastsimp intro: AAss_\<tau>Exec_meth_xt3 exec_move_AAssI3)+
    thus ?thesis using \<tau> bisim' `bsok a n` `bsok i n`
      by auto (rule exI conjI|erule \<tau>Exec_move_trans bisim1_bisims1.bisim1AAss3|rule \<tau>Exec_refl|assumption|simp)+
  next
    case (Red1AAss H A U el I V U' H' XS)
    hence [simp]: "v = Addr A" "e' = unit" "v' = Intg I" "H = h" "XS = xs" "ta = \<epsilon>" "H' = h'" "xs' = xs" "ee = Val V"
      and hA: "h A = \<lfloor>Arr U el\<rfloor>" and I: "0 \<le> I" "I < int (length el)" and v: "typeof\<^bsub>h\<^esub> V = \<lfloor>U'\<rfloor>" "P \<turnstile> U' \<le> U"
      and h': "h' = h(A \<mapsto> Arr U (el[nat I := V]))" by auto
    have \<tau>: "\<not> \<tau>move1 (AAss (addr A) (Val (Intg I)) (Val V))" by(auto)
    from bisim3 wte3 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P e h (stk, loc, pc, xcp) ([V], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + pc, xcp) ([V] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by-(rule AAss_\<tau>Exec_meth_xt3)
    moreover from hA I v h'
    have "exec_move P (a\<lfloor>i\<rceil> := e) h ([V, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h' ([], loc, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"
     unfolding exec_move_def by-(rule exec_instr, auto simp add: cast_ok_def compP2_def is_Ref_def)
    moreover have "\<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (unit, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"
      by(rule bisim1_bisims1.bisim1AAss4)
    ultimately show ?thesis using s \<tau> by auto fastsimp
  next
    case (Red1AAssNull V V' s)
    hence [simp]: "v = Null" "e' = THROW NullPointer" "V = v'" "s = (h, xs)" "xs' = xs" "ta = \<epsilon>" "h' = h" "ee = Val V'" by auto
    have \<tau>: "\<not> \<tau>move1 (AAss null (Val v') (Val V'))" by(auto)
    from bisim3 wte3 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P e h (stk, loc, pc, xcp) ([V'], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [v', Null], loc, length (compE2 a) + length (compE2 i) + pc, xcp) ([V'] @ [v', Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by-(rule AAss_\<tau>Exec_meth_xt3)
    moreover from wte2'
    have "exec_move P (a\<lfloor>i\<rceil> := e) h ([V', v', Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([V', v', Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([V', v', Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssNull)
    ultimately show ?thesis using s \<tau> by auto fastsimp
  next
    case (Red1AAssBounds s A U el I V)
    hence [simp]: "v = Addr A" "e' = THROW ArrayIndexOutOfBounds" "v' = Intg I" "s = (h, xs)" "xs' = xs" "ta = \<epsilon>" "h' = h" "ee = Val V"
      and hA: "h A = \<lfloor>Arr U el\<rfloor>" and I: "I < 0 \<or> int (length el) \<le> I" by auto
    have \<tau>: "\<not> \<tau>move1 (addr A\<lfloor>Val (Intg I)\<rceil> := ee)" by(auto)
    from bisim3 wte3 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P e h (stk, loc, pc, xcp) ([V], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + pc, xcp) ([V] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by-(rule AAss_\<tau>Exec_meth_xt3)
    moreover from hA I
    have "exec_move P (a\<lfloor>i\<rceil> := e) h ([V, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([V, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW ArrayIndexOutOfBounds, loc) \<leftrightarrow> ([V, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssBounds)
    ultimately show ?thesis using s \<tau> by auto fastsimp
  next 
    case (Red1AAssStore s A U el I V U')
    hence [simp]: "v = Addr A" "e' = THROW ArrayStore" "v' = Intg I" "s = (h, xs)" "xs' = xs" "ta = \<epsilon>" "h' = h" "ee = Val V"
      and hA: "h A = \<lfloor>Arr U el\<rfloor>" and I: "0 \<le> I" "I < int (length el)" and U: "\<not> P \<turnstile> U' \<le> U" "typeof\<^bsub>h\<^esub> V = \<lfloor>U'\<rfloor>" by auto
    have \<tau>: "\<not> \<tau>move1 (addr A\<lfloor>Val (Intg I)\<rceil> := ee)" by(auto)
    from bisim3 wte3 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P e h (stk, loc, pc, xcp) ([V], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + pc, xcp) ([V] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by-(rule AAss_\<tau>Exec_meth_xt3)
    moreover from hA I U
    have "exec_move P (a\<lfloor>i\<rceil> := e) h ([V, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([V, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def cast_ok_def compP2_def)
    moreover have "\<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW ArrayStore, loc) \<leftrightarrow> ([V, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssStore)
    ultimately show ?thesis using s \<tau> by auto fastsimp
  next
    case (AAss1Throw3 aa V A s)
    hence [simp]: "aa = v" "V = v'" "ee = Throw A" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw A" "h' = h" "xs' = xs" by auto
    have \<tau>: "\<tau>move1 (AAss (Val v) (Val v') (Throw A))" by(rule \<tau>move1AAssThrow3)
    from bisim3 have "xcp = \<lfloor>A\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>A\<rfloor>"
      with bisim3 `bsok a n` `bsok i n`
      have "P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> (stk @ [v', v], loc, length (compE2 a) + length (compE2 i) + pc, xcp)"
	by(auto intro: bisim1_bisims1.intros)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim3 wte3 obtain pc' where "\<tau>Exec_move P e h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and bisim': "P, e, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h (stk @ [v', v], loc, length (compE2 a) + length (compE2 i) + pc, None) ([Addr A] @ [v', v], loc, length (compE2 a) + length (compE2 i) + pc', \<lfloor>A\<rfloor>)"
	by-(rule AAss_\<tau>Exec_meth_xt3)
      moreover from bisim' `bsok a n` `bsok i n`
      have "P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A] @ [v', v], loc, length (compE2 a) +  length (compE2 i) + pc', \<lfloor>A\<rfloor>)"
	by(rule bisim1_bisims1.bisim1AAssThrow3)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case bisim1AAssThrow1 thus ?case by auto
next
  case bisim1AAssThrow2 thus ?case by auto
next
  case bisim1AAssThrow3 thus ?case by auto
next
  case bisim1AAssNull thus ?case by auto
next
  case bisim1AAssStore thus ?case by auto
next
  case bisim1AAssBounds thus ?case by auto
next
  case bisim1AAss4 thus ?case by auto
next
  case (bisim1ALength a n a' xs stk loc pc xcp)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>a',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 a :: T; P,Env',h \<turnstile>1 a' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,a,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta a a' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,a,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P \<turnstile>1 \<langle>a'\<bullet>length,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 a\<bullet>length :: T` obtain Te where wtE: "P,Env \<turnstile>1 a :: Te" by auto
  from `P,Env',h \<turnstile>1 a'\<bullet>length : T'` obtain Te' where wte: "P,Env',h \<turnstile>1 a' : Te'" by auto
  from red show ?case
  proof cases
    case (ALength1Red ee s TA ee' s')
    hence [simp]: "ee = a'" "s = (h, xs)" "TA = ta" "e' = ee'\<bullet>length" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>a',(h, xs)\<rangle> -ta\<rightarrow> \<langle>ee', (h', xs')\<rangle>" by auto
    from red have "\<tau>move1 (a'\<bullet>length) = \<tau>move1 a'" by(auto intro: \<tau>move1ALength)
    with IH[OF red wtE wte] show ?thesis by(fastsimp intro: bisim1_bisims1.bisim1ALength exec_move_ALengthI)
  next
    case (Red1ALength s A U el)
    hence [simp]: "a' = addr A" "s = (h, xs)" "ta = \<epsilon>" "e' = Val (Intg (int (length el)))" "h' = h" "xs' = xs"
      and hA: "h A = \<lfloor>Arr U el\<rfloor>" by auto
    from bisim have s: "xcp = None" "xs = loc" by(auto dest: bisim_Val_loc_eq_xcp_None)
    from bisim wtE have "\<tau>Exec_move P a h (stk, loc, pc, xcp) ([Addr A], loc, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (a\<bullet>length) h (stk, loc, pc, xcp) ([Addr A], loc, length (compE2 a), None)"
      by(rule ALength_\<tau>Exec_meth_xt)
    moreover from hA
    have "exec_move P (a\<bullet>length) h ([Addr A], loc, length (compE2 a), None) \<epsilon> h' ([Intg (int (length el))], loc, Suc (length (compE2 a)), None)"
      by(auto intro!: exec_instr simp add: is_Ref_def exec_move_def)
    moreover have "\<tau>move2 (a\<bullet>length) (length (compE2 a)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (addr A\<bullet>length)" by auto
    moreover from `bsok a n`
    have "P, a\<bullet>length, n, h' \<turnstile> (Val (Intg (int (length el))), loc) \<leftrightarrow> ([Intg (int (length el))], loc, length (compE2 (a\<bullet>length)), None)"
      by-(rule bisim1Val2, auto)
    ultimately show ?thesis using s by(auto) fastsimp 
  next
    case (Red1ALengthNull s)
    hence [simp]: "s = (h, xs)" "a' = null" "e' = THROW NullPointer" "h' = h" "xs' = xs" "ta = \<epsilon>" by auto
    have "\<not> \<tau>move1 (null\<bullet>length)" by auto
    moreover from bisim wtE have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P a h (stk, loc, pc, xcp) ([Null], loc, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    moreover have "exec_move P (a\<bullet>length) h ([Null], loc, length (compE2 a), None) \<epsilon> h ([Null], loc, length (compE2 a), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by -(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (a\<bullet>length) (length (compE2 a)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n`
    have "P,a\<bullet>length,n,h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([Null], loc, length (compE2 a), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro!: bisim1_bisims1.bisim1ALengthNull)
    ultimately show ?thesis using s by auto fastsimp
  next
    case (ALength1Throw A s)
    hence [simp]: "a' = Throw A" "s = (h, xs)" "h' = h" "xs' = xs" "ta = \<epsilon>" "e' = Throw A" by auto
    have \<tau>: "\<tau>move1 (Throw A\<bullet>length)" by(auto intro: \<tau>move1ALengthThrow)
    from bisim have "xcp = \<lfloor>A\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>A\<rfloor>"
      with bisim have "P,a\<bullet>length, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.bisim1ALengthThrow)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim wtE obtain pc'
	where "\<tau>Exec_move P a h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and bisim': "P, a, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (a\<bullet>length) h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	by-(rule ALength_\<tau>Exec_meth_xt)
      moreover from bisim' have "P, a\<bullet>length, n, hp s \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	by-(rule bisim1_bisims1.bisim1ALengthThrow, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed simp_all
next
  case bisim1ALengthThrow thus ?case by auto
next
  case bisim1ALengthNull thus ?case by auto
next
  case (bisim1FAcc E n e xs stk loc pc xcp F D)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 E :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P \<turnstile>1 \<langle>e\<bullet>F{D},(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 E\<bullet>F{D} :: T` obtain Te where wtE: "P,Env \<turnstile>1 E :: Te" by auto
  from `P,Env',h \<turnstile>1 e\<bullet>F{D} : T'` obtain Te' where wte: "P,Env',h \<turnstile>1 e : Te'" by auto
  from red show ?case
  proof cases
    case (FAcc1Red ee s TA ee' s' FF DD)
    hence [simp]: "FF = F" "DD = D" "ee = e" "s = (h, xs)" "TA = ta" "e' = ee'\<bullet>F{D}" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>ee', (h', xs')\<rangle>" by auto
    from red have "\<tau>move1 (e\<bullet>F{D}) = \<tau>move1 e" by(auto intro: \<tau>move1FAcc)
    with IH[OF red wtE wte] show ?thesis by(fastsimp intro: bisim1_bisims1.bisim1FAcc exec_move_FAccI)
  next
    case (Red1FAcc s a C fs FF DD v)
    hence [simp]: "FF = F" "DD = D" "e = addr a" "s = (h, xs)" "ta = \<epsilon>" "e' = Val v" "h' = h" "xs' = xs"
      and hA: "h a = \<lfloor>Obj C fs\<rfloor>" and fs: "fs (F, D) = \<lfloor>v\<rfloor>" by auto
    from bisim have s: "xcp = None" "xs = loc" by(auto dest: bisim_Val_loc_eq_xcp_None)
    from bisim wtE have "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (E\<bullet>F{D}) h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 E), None)"
      by(rule FAcc_\<tau>Exec_meth_xt)
    moreover from hA fs `P,Env',h \<turnstile>1 e\<bullet>F{D} : T'` hconf
    have "exec_move P (E\<bullet>F{D}) h ([Addr a], loc, length (compE2 E), None) \<epsilon> h' ([v], loc, Suc (length (compE2 E)), None)"
      unfolding exec_move_def
      apply(auto intro!: exec_instr simp add: is_Ref_def compP2_def intro: has_field_decl_above)
      apply(fastsimp dest: has_field_idemp_sees_field[OF wf wf_has_field_idemp[OF wf]] intro: has_field_decl_above)+
      apply(fastsimp dest!: hconfD simp add: oconf_def conf_def dest: has_field_idemp_sees_field[OF wf wf_has_field_idemp[OF wf]])
      done
    moreover have "\<tau>move2 (E\<bullet>F{D}) (length (compE2 E)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (addr a\<bullet>F{D})" by auto
    moreover from `bsok E n`
    have "P, E\<bullet>F{D}, n, h' \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (E\<bullet>F{D})), None)"
      by-(rule bisim1Val2, simp)
    ultimately show ?thesis using s by(auto) fastsimp 
  next
    case (Red1FAccNull FF DD s)
    hence [simp]: "s = (h, xs)" "FF = F" "DD = D" "e = null" "e' = THROW NullPointer" "h' = h" "xs' = xs" "ta = \<epsilon>" by auto
    have "\<not> \<tau>move1 (null\<bullet>F{D})" by auto
    moreover from bisim wtE have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([Null], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    moreover from `P,Env \<turnstile>1 E\<bullet>F{D} :: T`
    have "exec_move P (E\<bullet>F{D}) h ([Null], loc, length (compE2 E), None) \<epsilon> h ([Null], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by -(rule exec_instr, auto simp add: compP2_def dest: sees_field_idemp)
    moreover have "\<tau>move2 (E\<bullet>F{D}) (length (compE2 E)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok E n`
    have "P,E\<bullet>F{D},n,h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([Null], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro!: bisim1_bisims1.bisim1FAccNull)
    ultimately show ?thesis using s by auto fastsimp
  next
    case (FAcc1Throw a FF DD s)
    hence [simp]: "FF = F" "DD = D" "e = Throw a" "s = (h, xs)" "h' = h" "xs' = xs" "ta = \<epsilon>" "e' = Throw a" by auto
    have \<tau>: "\<tau>move1 (e\<bullet>F{D})" by(auto intro: \<tau>move1FAccThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim have "P,E\<bullet>F{D}, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.bisim1FAccThrow)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim wtE obtain pc'
	where "\<tau>Exec_move P E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (E\<bullet>F{D}) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule FAcc_\<tau>Exec_meth_xt)
      moreover from bisim' have "P, E\<bullet>F{D}, n, hp s \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1_bisims1.bisim1FAccThrow, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed simp_all
next
  case bisim1FAccThrow thus ?case by auto
next
  case bisim1FAccNull thus ?case by auto
next
  case (bisim1FAss1 e1 n e1' xs stk loc pc xcp e2 F D)
  note IH1 = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e1 :: T; P,Env',h \<turnstile>1 e1' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e1,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e1 e1' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note IH2 = `\<And>xs e' h' xs' Env T Env' T'. \<lbrakk>P \<turnstile>1 \<langle>e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e2 :: T; P,Env',h \<turnstile>1 e2 : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta e2 e2 h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,e1,n,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,e2,n,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,Env',h \<turnstile>1 e1'\<bullet>F{D} := e2 : T'` obtain T1' T2'
    where wte1': "P,Env',h \<turnstile>1 e1' : T1'"  and wte2': "P,Env',h \<turnstile>1 e2 : T2'" by auto
  from `P,Env \<turnstile>1 e1\<bullet>F{D} := e2 :: T` obtain T1 T2
    where wte1: "P,Env \<turnstile>1 e1 :: T1" and wte2: "P,Env \<turnstile>1 e2 :: T2" by auto
  from `P \<turnstile>1 \<langle>e1'\<bullet>F{D} := e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (FAss1Red1 e s TA E' s' FF DD E2)
    hence [simp]: "s = (h, xs)" "TA = ta" "s' = (h', xs')" "e = e1'" "FF = F" "DD = D" "E2 = e2" "e' = E'\<bullet>F{D} := e2"
      and red: "P \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by simp_all
    from red have "\<tau>move1 (e1'\<bullet>F{D} := e2) = \<tau>move1 e1'" by(auto intro: \<tau>move1FAss1)
    with IH1[OF red wte1 wte1'] `bsok e2 n` show ?thesis by(fastsimp intro: bisim1_bisims1.bisim1FAss1 exec_move_FAssI1)
  next
    case (FAss1Red2 e s TA E' s' v FF DD)
    hence [simp]: "s = (h, xs)" "TA = ta" "s' = (h', xs')" "e = e2" "FF = F" "DD = D" "e1' = Val v" "e' = Val v\<bullet>F{D} := E'"
      and red: "P \<turnstile>1 \<langle>e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by simp_all
    from red have \<tau>: "\<tau>move1 (Val v\<bullet>F{D} := e2) = \<tau>move1 e2" by(auto intro: \<tau>move1FAss2)
    from bisim1 wte1 have s: "xcp = None" "xs = loc"
      and exec1: "\<tau>Exec_move P (e1\<bullet>F{D} := e2) h (stk, loc, pc, None) ([v], xs, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    from IH2[OF red wte2 wte2'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e2,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e2 e2 h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (e1\<bullet>F{D} := e2) (Val v\<bullet>F{D} := e2) h ([] @ [v]) xs (length (compE2 e1) + 0) None h' (length (compE2 e1) + pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>move1 (Val v\<bullet>F{D} := e2)")
      case True
      with exec' \<tau> have [simp]: "h = h'" and e: "\<tau>Exec_move P e2 h ([], xs, 0, None) (stk'', loc'', pc'', xcp'')" by auto
      from e have "\<tau>Exec_move P (e1\<bullet>F{D} := e2) h ([] @ [v], xs, length (compE2 e1) + 0, None) (stk'' @ [v], loc'', length (compE2 e1) + pc'', xcp'')" by(rule FAss_\<tau>Exec_meth_xt2)
      with True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain ta' pc' stk' loc' xcp'
	where e: "\<tau>Exec_move P e2 h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_move P e2 h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 e2 pc' xcp'" and ta': "ta_bisim (wbisim1 P) ta ta'" by auto
      from e have "\<tau>Exec_move P (e1\<bullet>F{D} := e2) h ([] @ [v], xs, length (compE2 e1) + 0, None) (stk' @ [v], loc', length (compE2 e1) + pc', xcp')" by(rule FAss_\<tau>Exec_meth_xt2)
      moreover from e' have "exec_move P (e1\<bullet>F{D} := e2) h (stk' @ [v], loc', length (compE2 e1) + pc', xcp') ta' h' (stk'' @ [v], loc'', length (compE2 e1) + pc'', xcp'')"
	by(rule exec_move_FAssI2)
      moreover from e' have "pc' < length (compE2 e2)" by(auto elim: exec_meth.cases)
      with \<tau>' have "\<not> \<tau>move2 (e1\<bullet>F{D} := e2) (length (compE2 e1) + pc') xcp'" by auto
      ultimately show ?thesis using False ta' by(fastsimp simp add: stack_xlift_compxE2 shift_compxE2 simp del: split_paired_Ex)
    qed
    with exec1 \<tau> bisim' s `bsok e1 n` show ?thesis
      by auto(rule exI conjI|erule \<tau>Exec_move_trans bisim1_bisims1.bisim1FAss2|rule \<tau>Exec_refl|assumption)+
  next
    case (Red1FAss H a C fs FF DD v XS)
    hence [simp]: "e1' = addr a" "FF = F" "DD = D" "e2 = Val v" "H = h" "XS = xs" "ta = \<epsilon>" "e' = unit"
      "h' = h(a \<mapsto> Obj C (fs((F, D) \<mapsto> v)))" "xs' = xs"
      and ha: "h a = \<lfloor>Obj C fs\<rfloor>" by auto
    have \<tau>: "\<not> \<tau>move1 (e1'\<bullet>F{D} := e2)" by(auto)
    from bisim1 wte1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P e1 h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (e1\<bullet>F{D} := e2) h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 e1), None)"
      by-(rule FAss_\<tau>Exec_meth_xt1)
    also have "\<tau>move2 (e1\<bullet>F{D} := Val v) (length (compE2 e1) + 0) None"
      by(rule \<tau>move2FAss2)(rule \<tau>move2Val)
    with wte2 have "\<tau>Exec_move P (e1\<bullet>F{D} := e2) h ([Addr a], loc, length (compE2 e1), None) ([v, Addr a], loc, Suc (length (compE2 e1)), None)"
      by-(rule \<tau>Exec1step, auto intro!: exec_instr simp add: exec_move_def)
    also from ha `P,Env',h \<turnstile>1 e1'\<bullet>F{D} := e2 : T'`
    have "exec_move P (e1\<bullet>F{D} := e2) h ([v, Addr a], loc, Suc (length (compE2 e1)), None) \<epsilon>
                                      h' ([], loc, Suc (Suc (length (compE2 e1))), None)"
      unfolding exec_move_def
      apply(auto intro!: exec_instr simp add: is_Ref_def compP2_def intro: has_field_decl_above)
      apply(force dest: has_field_idemp_sees_field[OF wf wf_has_field_idemp[OF wf]] intro: has_field_decl_above)+
      apply(fastsimp dest!: hconfD simp add: oconf_def conf_def dest: has_field_idemp_sees_field[OF wf wf_has_field_idemp[OF wf]])
      done
    moreover have "\<tau>move2 (e1\<bullet>F{D} := e2) (Suc (length (compE2 e1))) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok e1 n` `bsok e2 n`
    have "P, e1\<bullet>F{D} := e2, n, h' \<turnstile> (unit, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 e1) + length (compE2 e2)), None)"
      by(rule bisim1_bisims1.bisim1FAss3)
    ultimately show ?thesis using s \<tau> by(auto simp del: fun_upd_apply) blast
  next
    case (Red1FAssNull FF DD v s)
    hence [simp]: "e1' = null" "FF = F" "DD = D" "e2 = Val v" "s = (h, xs)" "xs' = xs" "ta = \<epsilon>" "e' = THROW NullPointer" "h' = h" by auto
    have \<tau>: "\<not> \<tau>move1 (e1'\<bullet>F{D} := e2)" by(auto)
    from bisim1 wte1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P e1 h (stk, loc, pc, xcp) ([Null], loc, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (e1\<bullet>F{D} := e2) h (stk, loc, pc, xcp) ([Null], loc, length (compE2 e1), None)"
      by-(rule FAss_\<tau>Exec_meth_xt1)
    also have "\<tau>move2 (e1\<bullet>F{D} := Val v) (length (compE2 e1) + 0) None"
      by(rule \<tau>move2FAss2)(rule \<tau>move2Val)
    with wte2 have "\<tau>Exec_move P (e1\<bullet>F{D} := e2) h ([Null], loc, length (compE2 e1), None) ([v, Null], loc, Suc (length (compE2 e1)), None)"
      by-(rule \<tau>Exec1step, auto intro!: exec_instr simp add: exec_move_def)
    also from `P,Env \<turnstile>1 e1\<bullet>F{D} := e2 :: T`
    have "exec_move P (e1\<bullet>F{D} := e2) h ([v, Null], loc, Suc (length (compE2 e1)), None) \<epsilon>
                                      h' ([v, Null], loc, Suc (length (compE2 e1)), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      apply(auto intro!: exec_instr simp add: is_Ref_def compP2_def exec_move_def intro: has_field_decl_above)
      apply(blast dest: sees_field_idemp)
      apply(fastsimp dest: sees_field_idemp)
      done
    moreover have "\<tau>move2 (e1\<bullet>F{D} := e2) (Suc (length (compE2 e1))) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok e1 n` `bsok e2 n`
    have "P, e1\<bullet>F{D} := e2, n, h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([v, Null], loc, length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1_bisims1.bisim1FAssNull)
    ultimately show ?thesis using s \<tau> by(auto simp del: fun_upd_apply) blast
  next
    case (FAss1Throw1 a FF DD E2 s)
    hence [simp]: "e1' = Throw a" "FF = F" "DD = D" "E2 = e2" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw a" "h' = h" "xs' = xs" by auto
    have \<tau>: "\<tau>move1 (Throw a\<bullet>F{D} := e2)" by(rule \<tau>move1FAssThrow1)
    from bisim1 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 `bsok e2 n`
      have "P, e1\<bullet>F{D} := e2, n, hp s \<turnstile> (Throw a, lcl s) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.intros)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim1 wte1 obtain pc' where "\<tau>Exec_move P e1 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, e1, n, hp s \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (e1\<bullet>F{D} := e2) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule FAss_\<tau>Exec_meth_xt1)
      moreover from bisim' `bsok e2 n`
      have "P, e1\<bullet>F{D} := e2, n, h\<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1FAssThrow1)
      ultimately show ?thesis using \<tau> by auto
    qed
  next
    case FAss1Throw2 with wte2 have False by auto thus ?thesis ..
  qed simp_all
next
  case (bisim1FAss2 e2 n e2' xs stk loc pc xcp e1 F D v1)
  note IH2 = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e2 :: T; P,Env',h \<turnstile>1 e2' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e2 e2' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `\<And>xs. P,e1,n,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,e2,n,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P \<turnstile>1 \<langle>Val v1\<bullet>F{D} := e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 e1\<bullet>F{D} := e2 :: T` obtain T1 T2 where wte1: "P,Env \<turnstile>1 e1 :: T1" and wte2: "P,Env \<turnstile>1 e2 :: T2" by auto
  from `P,Env',h \<turnstile>1 Val v1\<bullet>F{D} := e2' : T'` obtain T2' where wte2': "P,Env',h \<turnstile>1 e2' : T2'" by auto
  from red show ?case
  proof cases
    case (FAss1Red2 e s TA E' s' v FF DD)
    hence [simp]: "s = (h, xs)" "TA = ta" "s' = (h', xs')" "v = v1" "FF = F" "DD = D" "e = e2'" "e' = Val v\<bullet>F{D} := E'"
      and red: "P \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by simp_all
    from IH2[OF red wte2 wte2'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e2,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e2 e2' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    from red have \<tau>: "\<tau>move1 (Val v1\<bullet>F{D} := e2') = \<tau>move1 e2'" by(auto intro: \<tau>move1FAss2)
    with exec' have "?exec ta (e1\<bullet>F{D} := e2) (Val v1\<bullet>F{D} := e2') h (stk @ [v]) loc (length (compE2 e1) + pc) xcp h' (length (compE2 e1) + pc'') (stk'' @ [v]) loc'' xcp''"
      by(cases "\<tau>move1 (Val v1\<bullet>F{D} := e2')")(fastsimp intro: FAss_\<tau>Exec_meth_xt2 exec_move_FAssI2)+
    with \<tau> bisim' `bsok e1 n` show ?thesis
      by auto(rule exI conjI|erule \<tau>Exec_move_trans bisim1_bisims1.bisim1FAss2|rule \<tau>Exec_refl|assumption)+
  next
    case (Red1FAss H a C fs FF DD v XS)
    hence [simp]: "v1 = Addr a" "FF = F" "DD = D" "e2' = Val v" "H = h" "XS = xs" "ta = \<epsilon>" "e' = unit"
      "h' = h(a \<mapsto> Obj C (fs((F, D) \<mapsto> v)))" "xs' = xs"
      and ha: "h a = \<lfloor>Obj C fs\<rfloor>" by auto
    have \<tau>: "\<not> \<tau>move1 (addr a\<bullet>F{D} := e2')" by(auto)
    from bisim2 wte2 have s: "xcp = None" "xs = loc" 
      and "\<tau>Exec_move P e2 h (stk, loc, pc, xcp) ([v], loc, length (compE2 e2), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (e1\<bullet>F{D} := e2) h (stk @ [v1], loc, length (compE2 e1) + pc, xcp) ([v] @ [v1], loc, length (compE2 e1) + length (compE2 e2), None)"
      by-(rule FAss_\<tau>Exec_meth_xt2)
    moreover from ha `P,Env',h \<turnstile>1 Val v1\<bullet>F{D} := e2' : T'`
    have "exec_move P (e1\<bullet>F{D} := e2) h ([v, Addr a], loc, length (compE2 e1) + length (compE2 e2), None) \<epsilon>
                                      h' ([], loc, Suc (length (compE2 e1) + length (compE2 e2)), None)"
      apply(auto intro!: exec_instr simp add: is_Ref_def compP2_def exec_move_def intro: has_field_decl_above)
      apply(force dest: has_field_idemp_sees_field[OF wf wf_has_field_idemp[OF wf]] intro: has_field_decl_above)+
      apply(fastsimp dest!: hconfD simp add: oconf_def conf_def dest: has_field_idemp_sees_field[OF wf wf_has_field_idemp[OF wf]])
      done
    moreover have "\<tau>move2 (e1\<bullet>F{D} := e2) (length (compE2 e1) + length (compE2 e2)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok e1 n` `bsok e2 n`
    have "P, e1\<bullet>F{D} := e2, n, h' \<turnstile> (unit, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 e1) + length (compE2 e2)), None)"
      by(rule bisim1_bisims1.bisim1FAss3)
    ultimately show ?thesis using s \<tau> by(auto simp del: fun_upd_apply) blast
  next
    case (Red1FAssNull FF DD v s)
    hence [simp]: "v1 = Null" "FF = F" "DD = D" "e2' = Val v" "s = (h, xs)" "xs' = xs" "ta = \<epsilon>" "e' = THROW NullPointer" "h' = h" by auto
    have \<tau>: "\<not> \<tau>move1 (null\<bullet>F{D} := e2')" by(auto)
    from bisim2 wte2 have s: "xcp = None" "xs = loc" 
      and "\<tau>Exec_move P e2 h (stk, loc, pc, xcp) ([v], loc, length (compE2 e2), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (e1\<bullet>F{D} := e2) h (stk @ [Null], loc, length (compE2 e1) + pc, xcp) ([v] @ [Null], loc, length (compE2 e1) + length (compE2 e2), None)"
      by-(rule FAss_\<tau>Exec_meth_xt2)
    moreover from `P,Env \<turnstile>1 e1\<bullet>F{D} := e2 :: T`
    have "exec_move P (e1\<bullet>F{D} := e2) h ([v, Null], loc, length (compE2 e1) + length (compE2 e2), None) \<epsilon>
                                      h' ([v, Null], loc, length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      apply(auto intro!: exec_instr simp add: is_Ref_def compP2_def exec_move_def intro: has_field_decl_above)
      apply(blast dest: sees_field_idemp)
      apply(fastsimp dest: sees_field_idemp)
      done
    moreover have "\<tau>move2 (e1\<bullet>F{D} := e2) (length (compE2 e1) + length (compE2 e2)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok e1 n` `bsok e2 n`
    have "P, e1\<bullet>F{D} := e2, n, h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([v, Null], loc, length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1_bisims1.bisim1FAssNull)
    ultimately show ?thesis using s \<tau> by(auto simp del: fun_upd_apply) blast
  next
    case (FAss1Throw2 V1 FF DD a s)
    hence [simp]: "V1 = v1" "FF = F" "DD = D" "e2' = Throw a" "ta = \<epsilon>" "h' = h" "xs' = xs" "s = (h, xs)" "e' = Throw a" by auto
    have \<tau>: "\<tau>move1 (FAss (Val v1) F D (Throw a))" by(rule \<tau>move1FAssThrow2)
    from bisim2 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim2 `bsok e1 n`
      have "P, e1\<bullet>F{D} := e2, n, hp s \<turnstile> (Throw a, xs) \<leftrightarrow> (stk @ [v1], loc, length (compE2 e1) + pc, xcp)"
	by(auto intro: bisim1FAssThrow2)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim2 wte2 obtain pc'
	where "\<tau>Exec_move P e2 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, e2, n, hp s \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (e1\<bullet>F{D} := e2) h (stk @ [v1], loc, length (compE2 e1) + pc, None) ([Addr a] @ [v1], loc, length (compE2 e1) + pc', \<lfloor>a\<rfloor>)"
	by-(rule FAss_\<tau>Exec_meth_xt2)
      moreover from bisim' `bsok e1 n`
      have "P, e1\<bullet>F{D} := e2, n, h \<turnstile> (Throw a, lcl s) \<leftrightarrow> ([Addr a]@[v1], loc, length (compE2 e1) + pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1FAssThrow2, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case bisim1FAssThrow1 thus ?case by fastsimp
next
  case bisim1FAssThrow2 thus ?case by fastsimp
next
  case bisim1FAssNull thus ?case by fastsimp
next
  case bisim1FAss3 thus ?case by fastsimp
next
  case (bisim1CallParams ps n ps' xs stk loc pc xcp obj M' v)
  note IHparam = `\<And>es' h' xs' Env Ts Env' Ts'. \<lbrakk> P \<turnstile>1 \<langle>ps',(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es',(h', xs')\<rangle>; P,Env \<turnstile>1 ps [::] Ts; P,Env',h \<turnstile>1 ps' [:] Ts'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,ps,n,h' \<turnstile> (es', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'') \<and>
                 ?execs ta ps ps' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `\<And>xs. P,obj,n,h \<turnstile> (obj, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,ps,n,h \<turnstile> (ps', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)`
  note red = `P \<turnstile>1 \<langle>Val v\<bullet>M'(ps'),(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 obj\<bullet>M'(ps) :: T` obtain Tobj Tps where wtobj: "P,Env \<turnstile>1 obj :: Tobj" and wtps: "P,Env \<turnstile>1 ps [::] Tps" by auto
  from `P,Env',h \<turnstile>1 Val v\<bullet>M'(ps') : T'` obtain Tobj' Tps'
    where wtobj': "P,Env',h \<turnstile>1 Val v : Tobj'" and wtps': "P,Env',h \<turnstile>1 ps' [:] Tps'" by auto
  from bisim2 `ps \<noteq> []` have ps': "ps' \<noteq> []" by(auto dest: bisims1_lengthD)
  from red show ?case
  proof cases
    case (Call1Params es s TA es' s' vv MM)
    hence [simp]: "vv = v" "MM = M'" "es = ps'" "s = (h, xs)" "TA = ta" "e' = Val v\<bullet>M'(es')" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>ps', (h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es', (h', xs')\<rangle>" by auto
    from red have \<tau>: "\<tau>move1 (Val v\<bullet>M'(ps')) = \<tau>moves1 ps'" by(auto intro: \<tau>move1CallParams)
    from IHparam[OF red wtps wtps'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,ps,n,h' \<turnstile> (es', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'')"
      and exec': "?execs ta ps ps' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (obj\<bullet>M'(ps)) (Val v\<bullet>M'(ps')) h (stk @ [v]) loc (length (compE2 obj) + pc) xcp  h' (length (compE2 obj) + pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>move1 (Val v\<bullet>M'(ps'))")
      case True
      with exec' \<tau> show ?thesis by(auto)
    next
      case False
      with exec' \<tau> obtain ta' pc' stk' loc' xcp'
	where e: "\<tau>Exec_moves P ps h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
	and e': "exec_moves P ps h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>moves2 ps pc' xcp'" and ta': "ta_bisim (wbisim1 P) ta ta'" by auto
      from e have "\<tau>Exec_move P (obj\<bullet>M'(ps)) h (stk @ [v], loc, length (compE2 obj) + pc, xcp) (stk' @ [v], loc', length (compE2 obj) + pc', xcp')" by(rule Call_\<tau>Exec_meth_xtParams)
      moreover from e' have "exec_move P (obj\<bullet>M'(ps)) h (stk' @ [v], loc', length (compE2 obj) + pc', xcp') ta' h' (stk'' @ [v], loc'', length (compE2 obj) + pc'', xcp'')"
	by(rule exec_move_CallI2)
      moreover from \<tau>' e' have "\<tau>move2 (obj\<bullet>M'(ps)) (length (compE2 obj) + pc') xcp' \<Longrightarrow> False"
	by -(erule \<tau>move2.cases,auto dest: \<tau>move2_pc_length_compE2 intro: \<tau>moves2xcp)
      ultimately show ?thesis using False ta' by(fastsimp simp del: split_paired_Ex)
    qed
    moreover from bisim' bisim1_bsok[OF bisim1]
    have "P,obj\<bullet>M'(ps),n,h' \<turnstile> (Val v\<bullet>M'(es'), xs') \<leftrightarrow> ((stk'' @ [v]), loc'', length (compE2 obj) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1CallParams)
    ultimately show ?thesis using \<tau> by(fastsimp elim!: \<tau>Exec_move_trans intro: \<tau>Exec_refl)
  next
    case (Red1CallNull MM vs s)
    hence [simp]: "s = (h, xs)" "h' = h" "xs' = xs" "ta = \<epsilon>" "v = Null" "MM = M'" "ps' = map Val vs" "e' = THROW NullPointer" by auto
    have "\<not> \<tau>move1 (null\<bullet>M'(map Val vs))"
      by(rule notI, erule \<tau>move1.cases \<tau>moves1.cases, auto)(drule sym, auto simp add: append_eq_conv_conj drop_map)
    moreover from bisim2 have length: "length ps = length vs" by(auto dest: bisims1_lengthD)
    have "lcl s = loc \<and> xcp = None \<and> \<tau>Exec_moves P ps h (stk, loc, pc, xcp) (rev vs, loc, length (compEs2 ps), None)"
    proof(cases "pc < length (compEs2 ps)")
      case True
      with bisim2 wtps show ?thesis by(auto dest: bisims1_Val_\<tau>Exec_moves)
    next
      case False
      with bisim2 have "pc = length (compEs2 ps)"
	by(auto dest: bisims1_pc_length_compEs2)
      with bisim2 show ?thesis by(auto dest: bisims1_Val_length_compEs2D intro: \<tau>Execs_refl)
    qed
    hence s: "lcl s = loc" "xcp = None"
      and "\<tau>Exec_moves P ps h (stk, loc, pc, xcp) (rev vs, loc, length (compEs2 ps), None)" by auto
    hence "\<tau>Exec_move P (obj\<bullet>M'(ps)) h (stk @ [Null], loc, length (compE2 obj) + pc, xcp) (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 ps), None)"
      by -(rule Call_\<tau>Exec_meth_xtParams)
    moreover from length have "exec_move P (obj\<bullet>M'(ps)) h (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 ps), None) \<epsilon> h (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 ps), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(cases ps)(auto intro: exec_instr)
    moreover have "\<tau>move2 (obj\<bullet>M'(ps)) (length (compE2 obj) + length (compEs2 ps)) None \<Longrightarrow> False"
      by(erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2 \<tau>moves2_pc_length_compEs2)
    moreover from bisim1 bisim2 have "bsok obj n" "bsoks ps n" by(auto dest: bisims1_bsoks bisim1_bsok)
    with length have "P,obj\<bullet>M'(ps),n,hp s \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ((rev vs @ [Null]), loc, length (compE2 obj) + length (compEs2 ps), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by-(rule bisim1CallThrow,auto)
    ultimately show ?thesis using s by(fastsimp intro: \<tau>Exec_refl)
  next
    case (Call1ThrowParams es vs a es' vv MM s)
    hence [simp]: "vv = v" "MM = M'" "es = ps'" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw a" "ps' = map Val vs @ Throw a # es'" "h' = h" "xs' = xs" by auto
    have \<tau>: "\<tau>move1 (Val v\<bullet>M'(map Val vs @ Throw a # es'))" by(rule \<tau>move1CallThrowParams)
    from bisim2 have [simp]: "xs = loc" and "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisims1_ThrowD)
    from `xcp = \<lfloor>a\<rfloor> \<or> xcp = None` show ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim2 bisim1_bsok[OF bisim1]
      have "P,obj\<bullet>M'(ps),n,hp s \<turnstile> (Throw a, loc) \<leftrightarrow> (stk @ [v], loc, length (compE2 obj) + pc, \<lfloor>a\<rfloor>)"
	by -(rule bisim1CallThrowParams, auto)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim2 wtps obtain pc'
	where exec: "\<tau>Exec_moves P ps h (stk, loc, pc, None) (Addr a # rev vs, loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, ps, n, h \<turnstile> (map Val vs @ Throw a # es', loc) [\<leftrightarrow>] (Addr a # rev vs, loc, pc', \<lfloor>a\<rfloor>)"
	by(auto dest: bisims1_Throw_\<tau>Exec_moves)
      from bisim' bisim1_bsok[OF bisim1]
      have "P,obj\<bullet>M'(ps),n,hp s \<turnstile> (Throw a, loc) \<leftrightarrow> ((Addr a # rev vs) @ [v], loc, length (compE2 obj) + pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1CallThrowParams, auto)
      with Call_\<tau>Exec_meth_xtParams[OF exec, of obj M' v] \<tau>
      show ?thesis by auto
    qed
  next
    case (Red1CallExternal s a Ta M vs TA va H' ta' E' s')
    hence [simp]: "v = Addr a" "M' = M" "ps' = map Val vs" "s = (h, xs)" "ta' = ta" "E' = e'"
      "s' = (h', xs')" "e' = extRet2J va" "H' = h'" "xs' = xs"
      and ta: "ta = extTA2J1 P TA"
      and Ta: "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>"
      and iec: "is_external_call P Ta M (length vs)"
      and redex: "P \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -TA\<rightarrow>ext \<langle>va,h'\<rangle>" by auto
    from bisim2 have [simp]: "xs = loc" by(auto dest: bisims_Val_loc_eq_xcp_None)
    have \<tau>: "\<not> \<tau>move1 (addr a\<bullet>M(map Val vs))" by(fastsimp simp add: map_eq_append_conv)
    obtain s: "xcp = None" "lcl s = loc"
      and "\<tau>Exec_moves P ps h (stk, loc, pc, xcp) (rev vs, loc, length (compEs2 ps), None)"
    proof(cases "pc < length (compEs2 ps)")
      case True
      with wtps bisim2 show ?thesis by(auto dest: bisims1_Val_\<tau>Exec_moves intro: that)
    next
      case False
      with bisim2 have "pc = length (compEs2 ps)" by(auto dest: bisims1_pc_length_compEs2)
      with bisim2 show ?thesis by -(rule that, auto dest!: bisims1_pc_length_compEs2D intro: \<tau>Exec_moves.\<tau>Execs_refl)
    qed
    from Call_\<tau>Exec_meth_xtParams[OF this(3), of obj M v]
    have "\<tau>Exec_move P (obj\<bullet>M(ps)) h (stk @ [Addr a], loc, length (compE2 obj) + pc, xcp) (rev vs @ [Addr a], loc, length (compE2 obj) + length (compEs2 ps), None)" by simp
    moreover let ?ret = "extRet2JVM (length ps) h' (rev vs @ [Addr a]) loc arbitrary arbitrary (length (compE2 obj) + length (compEs2 ps)) [] va"
    let ?stk' = "fst (hd (snd (snd ?ret)))"
    let ?xcp' = "fst ?ret"
    let ?pc' = "snd (snd (snd (snd (hd (snd (snd ?ret))))))"
    from bisim2 have [simp]: "length ps = length vs" by(auto dest: bisims1_lengthD)
    from redex have redex': "(TA, va, h') \<in> set (red_external_list (compP2 P) a M vs h)"
      unfolding red_external_list_conv[symmetric] by(simp add: compP2_def)
    from `P,Env',h \<turnstile>1 Val v\<bullet>M'(ps') : T'` Ta iec obtain Ts U
      where wtext: "map typeof\<^bsub>h\<^esub> vs = map Some Ts" "P \<turnstile> Ta\<bullet>M(Ts) :: U"
      by(auto split: heapobj.split_asm simp add: compP2_def)
    with Ta iec redex'
    have "exec_move P (obj\<bullet>M(ps)) h (rev vs @ [Addr a], loc, length (compE2 obj) + length (compEs2 ps), None) (extTA2JVM (compP2 P) TA) h' (?stk', loc, ?pc', ?xcp')"
      unfolding exec_move_def
      by -(rule exec_instr,cases va,(force simp add: compP2_def red_external_list_conv is_Ref_def)+)
    moreover have "\<not> \<tau>move2 (obj\<bullet>M'(ps)) (length (compE2 obj) + length (compEs2 ps)) None"
      by(fastsimp dest: \<tau>move2_pc_length_compE2 \<tau>moves2_pc_length_compEs2 elim: \<tau>move2_cases)
    moreover have "P,obj\<bullet>M(ps),n,h' \<turnstile> (extRet2J1 va, loc) \<leftrightarrow> (?stk', loc, ?pc', ?xcp')"
    proof(cases va)
      case (Inl v)
      from `bsok obj n` `bsoks ps n` have "P,obj\<bullet>M(ps),n,h' \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (obj\<bullet>M(ps))), None)"
	by-(rule bisim1Val2, simp)
      thus ?thesis unfolding Inl by simp
    next
      case (Inr ad)
      with `bsok obj n` `bsoks ps n` show ?thesis by(auto intro: bisim1CallThrow)
    qed
    moreover from Ta have "h a \<noteq> None" by auto
    with ta external_call_hconf[OF redex Ta wtext hconf]
    have "ta_bisim (wbisim1 P) ta (extTA2JVM (compP2 P) TA)" by(auto intro: red_external_ta_bisim21[OF wf redex])
    ultimately show ?thesis using \<tau> by(force simp del: split_paired_Ex)
  qed(insert ps', auto)
next
  case bisim1CallThrowObj thus ?case by fastsimp
next
  case bisim1CallThrowParams thus ?case by auto
next
  case bisim1CallThrow thus ?case by fastsimp
next
  case (bisim1BlockSome1 e V Ty v xs e')
  note IH = `\<And>xs e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e,Suc V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e e h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  from `P,Env \<turnstile>1 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> :: T` have wte: "P,Env@[Ty] \<turnstile>1 e :: T" and v: "\<not> is_Addr v" by auto
  from `P,Env',h \<turnstile>1 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> : T'` have wte': "P,Env'@[Ty],h \<turnstile>1 e : T'" by auto
  note bisim = `\<And>xs. P,e,Suc V,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P \<turnstile>1 \<langle>{V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof(cases)
    case (Block1RedSome E H XS VV vv TA E' H' XS' TT cr)
    hence [simp]: "VV = V" "TT =Ty" "vv = v" "E = e" "H = h" "XS = xs" "TA = ta" "e' = {V:Ty=None; E'}\<^bsub>False\<^esub>" "H' = h'" "XS' = xs'" "cr = False"
      and red: "P \<turnstile>1 \<langle>e,(h, xs[V := v])\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" and V: "V < length xs" by auto
    from red have \<tau>: "\<tau>move1 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> = \<tau>move1 e" by(auto intro: \<tau>move1Block)
    from V v have exec: "\<tau>Exec_move P {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> h ([], xs, 0, None) ([], xs[V := v], Suc (Suc 0), None)"
      by-(rule \<tau>Exec2step, auto intro: exec_instr \<tau>move2BlockSome1 \<tau>move2BlockSome2 simp add: exec_move_def)
    from IH[OF red wte wte'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e,Suc V,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e e h [] (xs[V := v]) 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> h [] xs 0 None h' (Suc (Suc pc'')) stk'' loc'' xcp''"
      using exec' \<tau> exec
      by(cases "\<tau>move1 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>")(fastsimp intro: Block_\<tau>Exec_meth_xtSome exec_move_BlockSomeI \<tau>Exec_refl elim!: \<tau>Exec_move_trans)+
    with bisim' \<tau> show ?thesis by(fastsimp intro: bisim1BlockSome4)
  next
    case (Red1BlockSome VV XS TT vv u cr H)
    hence [simp]: "VV = V" "vv = v" "TT = Ty" "e = Val u" "H = h" "XS = xs" "ta = \<epsilon>" "e' = Val u" "h' = h" "xs' = xs[V := v]" "cr = False"
      and V: "V < length xs" by auto
    have "\<tau>move1 {V:Ty=\<lfloor>v\<rfloor>; Val u}\<^bsub>False\<^esub>" by(rule \<tau>move1BlockRed)
    moreover from V wte v
    have exec: "\<tau>Exec_move P {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> h ([], xs, 0, None) ([u], xs[V := v], Suc (Suc (Suc 0)), None)"
      by-(rule \<tau>Exec3step, auto intro: exec_instr \<tau>move2BlockSome1 \<tau>move2BlockSome2 \<tau>move2BlockSome \<tau>move2Val simp add: exec_move_def)
    ultimately show ?thesis by(fastsimp intro: bisim1Val2)
  next
    case Block1ThrowSome with wte have False by auto
    thus ?thesis ..
  qed auto
next
  case (bisim1BlockSome2 e V Ty v xs)
  note IH = `\<And>xs e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e,Suc V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e e h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  from `P,Env \<turnstile>1 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> :: T` have wte: "P,Env@[Ty] \<turnstile>1 e :: T" and v: "\<not> is_Addr v" by auto
  from `P,Env',h \<turnstile>1 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> : T'` have wte': "P,Env'@[Ty],h \<turnstile>1 e : T'" by auto
  note bisim = `\<And>xs. P,e,Suc V,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P \<turnstile>1 \<langle>{V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof(cases)
    case (Block1RedSome E H XS VV vv TA E' H' XS' TT cr)
    hence [simp]: "VV = V" "TT =Ty" "vv = v" "E = e" "H = h" "XS = xs" "TA = ta" 
      "e' = {V:Ty=None; E'}\<^bsub>False\<^esub>" "H' = h'" "XS' = xs'" "cr = False"
      and red: "P \<turnstile>1 \<langle>e,(h, xs[V := v])\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" and V: "V < length xs" by auto
    from red have \<tau>: "\<tau>move1 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> = \<tau>move1 e" by(auto intro: \<tau>move1Block)
    from V have exec: "\<tau>Exec_move P {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> h ([v], xs, Suc 0, None) ([], xs[V := v], Suc (Suc 0), None)"
      by-(rule \<tau>Exec1step, auto intro: exec_instr \<tau>move2BlockSome2 simp: exec_move_def)
    from IH[OF red wte wte'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e,Suc V,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e e h [] (xs[V := v]) 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> h [v] xs (Suc 0) None h' (Suc (Suc pc'')) stk'' loc'' xcp''"
      using exec' \<tau> exec
      by(cases "\<tau>move1 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>")(fastsimp intro: Block_\<tau>Exec_meth_xtSome exec_move_BlockSomeI \<tau>Exec_refl elim!: \<tau>Exec_move_trans)+
    with bisim' \<tau> show ?thesis by(fastsimp intro: bisim1BlockSome4)
  next
    case (Red1BlockSome VV XS TT vv u cr H)
    hence [simp]: "VV = V" "vv = v" "TT = Ty" "e = Val u" "H = h" "XS = xs"
      "ta = \<epsilon>" "e' = Val u" "h' = h" "xs' = xs[V := v]" "cr = False"
      and V: "V < length xs" by auto
    have "\<tau>move1 {V:Ty=\<lfloor>v\<rfloor>; Val u}\<^bsub>False\<^esub>" by(rule \<tau>move1BlockRed)
    moreover from V v wte
    have exec: "\<tau>Exec_move P {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> h ([v], xs, Suc 0, None) ([u], xs[V := v], Suc (Suc (Suc 0)), None)"
      by-(rule \<tau>Exec2step, auto intro: exec_instr \<tau>move2BlockSome2 \<tau>move2BlockSome \<tau>move2Val simp: exec_move_def)
    ultimately show ?thesis by(fastsimp intro: bisim1Val2)
  next
    case Block1ThrowSome with wte have False by auto
    thus ?thesis ..
  qed auto
next
  case (bisim1BlockSome3 E V e xs v stk loc pc xcp Ty)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e,(h, xs[V := v])\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 E :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,Suc V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  from `P,Env \<turnstile>1 {V:Ty=\<lfloor>v\<rfloor>; E}\<^bsub>False\<^esub> :: T` have wte: "P,Env@[Ty] \<turnstile>1 E :: T" and v: "\<not> is_Addr v" by auto
  from `P,Env',h \<turnstile>1 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> : T'` have wte': "P,Env'@[Ty],h \<turnstile>1 e : T'" by auto
  note bisim = `P,E,Suc V,h \<turnstile> (e, xs[V := v]) \<leftrightarrow> (stk, loc, pc, xcp)`
  from `P \<turnstile>1 \<langle>{V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Block1RedSome EE H XS VV vv TA E' H' XS' TT cr)
    hence [simp]: "VV = V" "TT =Ty" "vv = v" "EE = e" "H = h" "XS = xs" "TA = ta"
      "e' = {V:Ty=None; E'}\<^bsub>False\<^esub>" "H' = h'" "XS' = xs'" "cr = False"
      and red: "P \<turnstile>1 \<langle>e,(h, xs[V := v])\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" and V: "V < length xs" by auto
    from red have \<tau>: "\<tau>move1 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> = \<tau>move1 e" by(auto intro: \<tau>move1Block)
    from IH[OF red wte wte'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,E,Suc V,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta {V:Ty=\<lfloor>v\<rfloor>; E}\<^bsub>False\<^esub> {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> h stk loc (Suc (Suc pc)) xcp h' (Suc (Suc pc'')) stk'' loc'' xcp''"
      using exec' \<tau>  by(cases "\<tau>move1 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>")(fastsimp intro: Block_\<tau>Exec_meth_xtSome exec_move_BlockSomeI)+
    with bisim' \<tau> show ?thesis by(fastsimp intro: bisim1BlockSome4)
  next
    case (Red1BlockSome VV XS TT vv u cr H)
    hence [simp]: "VV = V" "vv = v" "TT = Ty" "e = Val u" "H = h" "XS = xs"
      "ta = \<epsilon>" "e' = Val u" "h' = h" "xs' = xs[V := v]" "cr = False"
      and V: "V < length xs" by auto
    have "\<tau>move1 {V:Ty=\<lfloor>v\<rfloor>; Val u}\<^bsub>False\<^esub>" by(rule \<tau>move1BlockRed)
    moreover from bisim wte v have [simp]: "xcp = None" "loc = xs[V := v]"
      and exec: "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([u], loc, length (compE2 E), None)" by(auto dest: bisim1Val2D1)
    moreover from bisim1_bsok[OF bisim]
    have "P,{V:Ty=\<lfloor>v\<rfloor>; E}\<^bsub>False\<^esub>,V,h \<turnstile> (Val u, xs[V := v]) \<leftrightarrow> ([u], xs[V := v], length (compE2 {V:Ty=\<lfloor>v\<rfloor>; E}\<^bsub>False\<^esub>), None)"
      by-(rule bisim1Val2, simp) 
    ultimately show ?thesis by fastsimp
  next
    case (Block1ThrowSome VV XS TT vv a cr H)
    hence [simp]: "VV = V" "TT = Ty" "vv = v" "e = Throw a" "ta = \<epsilon>" "H = h" "XS = xs"
      "e' = Throw a" "h' = h" "xs' = xs[V := v]" "cr = False"
      and V: "V < length xs" by auto
    from V have \<tau>: "\<tau>move1 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>" by(auto intro: \<tau>move1BlockThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim have "P, {V:Ty=\<lfloor>v\<rfloor>; E}\<^bsub>False\<^esub>, V, h \<turnstile> (Throw a, xs[V := v]) \<leftrightarrow> (stk, loc, Suc (Suc pc), xcp)"
	by(auto intro: bisim1BlockThrowSome)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim wte obtain pc'
	where "\<tau>Exec_move P E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, Suc V, h \<turnstile> (Throw a, xs[V := v]) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs[V := v] = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P {V:Ty=\<lfloor>v\<rfloor>; E}\<^bsub>False\<^esub> h (stk, loc, Suc (Suc pc), None) ([Addr a], loc, Suc (Suc pc'), \<lfloor>a\<rfloor>)"
	by auto
      moreover from bisim' have "P, {V:Ty=\<lfloor>v\<rfloor>; E}\<^bsub>False\<^esub>, V, h \<turnstile> (Throw a, xs[V := v]) \<leftrightarrow> ([Addr a], loc, Suc (Suc pc'), \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1BlockThrowSome)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case (bisim1BlockSome4 E V e xs stk loc pc xcp Ty v)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 E :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,Suc V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  from `P,Env \<turnstile>1 {V:Ty=\<lfloor>v\<rfloor>; E}\<^bsub>False\<^esub> :: T` have wte: "P,Env@[Ty] \<turnstile>1 E :: T" by auto
  from `P,Env',h \<turnstile>1 {V:Ty=None; e}\<^bsub>False\<^esub> : T'` have wte': "P,Env'@[Ty],h \<turnstile>1 e : T'" by auto
  note bisim = `P,E,Suc V,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  from `P \<turnstile>1 \<langle>{V:Ty=None; e}\<^bsub>False\<^esub>,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Block1RedNone EE H XS TA E' H' XS' VV TT cr)
    hence [simp]: "VV = V" "TT =Ty" "EE = e" "H = h" "XS = xs" "TA = ta"
      "e' = {V:Ty=None; E'}\<^bsub>False\<^esub>" "H' = h'" "XS' = xs'" "cr = False"
      and red: "P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" and V: "V < length xs" by auto
    from red have \<tau>: "\<tau>move1 {V:Ty=None; e}\<^bsub>False\<^esub> = \<tau>move1 e" by(auto intro: \<tau>move1Block)
    from IH[OF red wte wte'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,E,Suc V,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta {V:Ty=\<lfloor>v\<rfloor>; E}\<^bsub>False\<^esub> {V:Ty=None; e}\<^bsub>False\<^esub> h stk loc (Suc (Suc pc)) xcp h' (Suc (Suc pc'')) stk'' loc'' xcp''"
      using exec' \<tau> by(cases "\<tau>move1 {V:Ty=None; e}\<^bsub>False\<^esub>")(fastsimp intro: exec_move_BlockSomeI)+
    with bisim' \<tau> show ?thesis by(fastsimp intro: bisim1_bisims1.bisim1BlockSome4)
  next
    case (Red1BlockNone VV s TT u)
    hence [simp]: "VV = V" "TT = Ty" "e = Val u" "s = (h, xs)" "ta = \<epsilon>" "e' = Val u" "h' = h" "xs' = xs"
      and V: "V < length xs" by auto
    have "\<tau>move1 {V:Ty=None; Val u}\<^bsub>False\<^esub>" by(rule \<tau>move1BlockRed)
    moreover from bisim wte have [simp]: "xcp = None" "loc = xs"
      and exec: "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([u], loc, length (compE2 E), None)" by(auto dest: bisim1Val2D1)
    moreover from bisim1_bsok[OF bisim]
    have "P,{V:Ty=\<lfloor>v\<rfloor>; E}\<^bsub>False\<^esub>,V,h \<turnstile> (Val u, xs) \<leftrightarrow> ([u], xs, length (compE2 {V:Ty=\<lfloor>v\<rfloor>; E}\<^bsub>False\<^esub>), None)"
      by-(rule bisim1Val2, simp) 
    ultimately show ?thesis by fastsimp
  next
    case (Block1ThrowNone VV s TT a cr)
    hence [simp]: "VV = V" "TT = Ty" "e = Throw a" "ta = \<epsilon>" "s = (h, xs)" "e' = Throw a" "h' = h" "xs' = xs" "cr = False"
      and V: "V < length xs" by auto
    from V have \<tau>: "\<tau>move1 {V:Ty=None; e}\<^bsub>False\<^esub>" by(auto intro: \<tau>move1BlockThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim have "P, {V:Ty=\<lfloor>v\<rfloor>; E}\<^bsub>False\<^esub>, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (Suc pc), xcp)"
	by(auto intro: bisim1BlockThrowSome)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim wte obtain pc'
	where "\<tau>Exec_move P E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, Suc V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P {V:Ty=\<lfloor>v\<rfloor>; E}\<^bsub>False\<^esub> h (stk, loc, Suc (Suc pc), None) ([Addr a], loc, Suc (Suc pc'), \<lfloor>a\<rfloor>)" by auto
      moreover from bisim' have "P, {V:Ty=\<lfloor>v\<rfloor>; E}\<^bsub>False\<^esub>, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, Suc (Suc pc'), \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1BlockThrowSome)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case bisim1BlockThrowSome thus ?case by auto
next
  case (bisim1BlockNone E V e xs stk loc pc xcp Ty)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 E :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,Suc V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  from `P,Env \<turnstile>1 {V:Ty=None; E}\<^bsub>False\<^esub> :: T` have wte: "P,Env@[Ty] \<turnstile>1 E :: T" by auto
  from `P,Env',h \<turnstile>1 {V:Ty=None; e}\<^bsub>False\<^esub> : T'` have wte': "P,Env'@[Ty],h \<turnstile>1 e : T'" by auto
  note bisim = `P,E,Suc V,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  from `P \<turnstile>1 \<langle>{V:Ty=None; e}\<^bsub>False\<^esub>,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Block1RedNone EE H XS TA E' H' XS' VV TT cr)
    hence [simp]: "VV = V" "TT =Ty" "EE = e" "H = h" "XS = xs" "TA = ta"
      "e' = {V:Ty=None; E'}\<^bsub>False\<^esub>" "H' = h'" "XS' = xs'" "cr = False"
      and red: "P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" and V: "V < length xs" by auto
    from red have \<tau>: "\<tau>move1 {V:Ty=None; e}\<^bsub>False\<^esub> = \<tau>move1 e" by(auto intro: \<tau>move1Block)
    with IH[OF red wte wte'] show ?thesis
      by(auto simp add: exec_move_BlockNone) (assumption|rule exI conjI Block_\<tau>Exec_meth_xtNone contrapos_nn[OF _ \<tau>move2_BlockNoneD] bisim1_bisims1.bisim1BlockNone)+
  next
    case (Red1BlockNone VV s TT u cr)
    hence [simp]: "VV = V" "TT = Ty" "e = Val u" "s = (h, xs)" "ta = \<epsilon>" "e' = Val u" "h' = h" "xs' = xs" "cr = False"
      and V: "V < length xs" by auto
    have "\<tau>move1 {V:Ty=None; Val u}\<^bsub>False\<^esub>" by(rule \<tau>move1BlockRed)
    moreover from bisim wte have [simp]: "xcp = None" "loc = xs"
      and exec: "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([u], loc, length (compE2 E), None)" by(auto dest: bisim1Val2D1)
    moreover from bisim1_bsok[OF bisim]
    have "P,{V:Ty=None; E}\<^bsub>False\<^esub>,V,h \<turnstile> (Val u, xs) \<leftrightarrow> ([u], xs, length (compE2 {V:Ty=None; E}\<^bsub>False\<^esub>), None)"
      by-(rule bisim1Val2, simp) 
    ultimately show ?thesis by fastsimp
  next
    case (Block1ThrowNone VV s TT a)
    hence [simp]: "VV = V" "TT = Ty" "e = Throw a" "ta = \<epsilon>" "s = (h, xs)" "e' = Throw a" "h' = h" "xs' = xs"
      and V: "V < length xs" by auto
    from V have \<tau>: "\<tau>move1 {V:Ty=None; e}\<^bsub>False\<^esub>" by(auto intro: \<tau>move1BlockThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim have "P, {V:Ty=None; E}\<^bsub>False\<^esub>, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1BlockThrowNone)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim wte obtain pc'
	where "\<tau>Exec_move P E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, Suc V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P {V:Ty=None; E}\<^bsub>False\<^esub> h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" by auto
      moreover from bisim' have "P, {V:Ty=None; E}\<^bsub>False\<^esub>, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1BlockThrowNone)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case bisim1BlockThrowNone thus ?case by auto
next
  case (bisim1Sync1 e1 V e1' xs stk loc pc xcp e2)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e1 :: T; P,Env',h \<turnstile>1 e1' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e1,V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e1 e1' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,e1,V,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note red = `P \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (e1') e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 sync\<^bsub>V\<^esub> (e1) e2 :: T` obtain T1 where wte1: "P,Env \<turnstile>1 e1 :: T1" by auto
  from `P,Env',h \<turnstile>1 sync\<^bsub>V\<^esub> (e1') e2 : T'` obtain T1' where wte1': "P,Env',h \<turnstile>1 e1' : T1'" by auto
  from red show ?case
  proof cases
    case (Synchronized1Red1 E1 s TA E1' s' VV E2)
    hence [simp]: "VV = V" "E1 = e1'" "E2 = e2" "s = (h, xs)" "TA = ta" "e' = sync\<^bsub>V\<^esub> (E1') e2" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>e1', (h, xs)\<rangle> -ta\<rightarrow> \<langle>E1', (h', xs')\<rangle>" by auto
    from red have \<tau>: "\<tau>move1 (sync\<^bsub>V\<^esub> (e1') e2) = \<tau>move1 e1'" by(auto intro: \<tau>move1Sync)
    from IH[OF red wte1 wte1'] \<tau> bisim1_bsok[OF bisim2] show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisim1Sync1 exec_move_SyncI1)
  next
    case (Synchronized1Null VV XS E H)
    hence [simp]: "VV = V" "e1' = null" "E = e2" "H = h" "XS = xs" "e' = THROW NullPointer" "ta = \<epsilon>" "h' = h"
      "xs' = xs[V := Null]" and V: "V < length xs" by auto
    from bisim1 wte1 have [simp]: "xcp = None" "xs = loc"
      and exec: "\<tau>Exec_move P e1 h (stk, loc, pc, xcp) ([Null], loc, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    from Sync_\<tau>Exec_meth_xt[OF exec]
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, pc, xcp) ([Null], loc, length (compE2 e1), None)" by simp
    also from V
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Null], loc, length (compE2 e1), None) ([Null], loc[V := Null], Suc (Suc (length (compE2 e1))), None)"
      by -(rule \<tau>Exec2step,auto intro: exec_instr \<tau>move2_\<tau>moves2.intros simp add: exec_move_def)
    also have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Null], loc[V := Null], Suc (Suc (length (compE2 e1))), None) \<epsilon>
                        h ([Null], loc[V := Null], Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr) auto
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (length (compE2 e1)))) None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW NullPointer, loc[V := Null]) \<leftrightarrow> ([Null], (loc[V := Null]), Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro: bisim1Sync11)
    moreover have "\<not> \<tau>move1 (sync\<^bsub>V\<^esub> (null) e2)" by auto
    ultimately show ?thesis by fastsimp
  next
    case (Lock1Synchronized H a arrobj VV XS E2)
    hence [simp]: "VV = V" "e1' = addr a" "E2 = e2" "H = h" "XS = xs" "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Lock\<rightarrow>a\<rbrace>" "e' = insync\<^bsub>V\<^esub> (a) e2"
      "h' = h" "xs' = xs[V := Addr a]" and V: "V < length xs" and ha: "h a = \<lfloor>arrobj\<rfloor>" by auto
    from bisim1 wte1 have [simp]: "xcp = None" "xs = loc"
      and exec: "\<tau>Exec_move P e1 h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    from Sync_\<tau>Exec_meth_xt[OF exec]
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 e1), None)" by simp
    also from V
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a], loc, length (compE2 e1), None) ([Addr a], loc[V := Addr a], Suc (Suc (length (compE2 e1))), None)"
      by -(rule \<tau>Exec2step,auto intro: exec_instr \<tau>move2_\<tau>moves2.intros simp add: exec_move_def)
    also from ha
    have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a], loc[V := Addr a], Suc (Suc (length (compE2 e1))), None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a\<rbrace>)
                        h ([], loc[V := Addr a], Suc (Suc (Suc (length (compE2 e1)))), None)"
      unfolding exec_move_def by -(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (length (compE2 e1)))) None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover from bisim1 bisim2 have "bsok E2 (Suc V)" "bsok e1 V"  by(auto dest: bisim1_bsok)
    from bisim1Sync4[OF bisim1_refl, OF this, of P h a "loc[V := Addr a]"]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (insync\<^bsub>V\<^esub> (a) e2, loc[V := Addr a]) \<leftrightarrow> ([], loc[V := Addr a], Suc (Suc (Suc (length (compE2 e1)))), None)" by simp
    moreover have "\<not> \<tau>move1 (sync\<^bsub>V\<^esub> (addr a) e2)" by(rule notI)(erule \<tau>move1.cases, auto elim: \<tau>move1.cases)
    ultimately show ?thesis by(fastsimp simp add: nat_number ta_bisim_def)
  next
    case (Synchronized1Throw1 VV a E s)
    hence [simp]: "VV = V" "e1' = Throw a" "E = e2" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw a" "h' = h" "xs' = xs" by auto
    have \<tau>: "\<tau>move1 (sync\<^bsub>V\<^esub> (Throw a) e2)" by(rule \<tau>move1SyncThrow)
    from bisim1 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 bisim1_bsok[OF bisim2]
      have "P, sync\<^bsub>V\<^esub> (e1) e2, V, hp s \<turnstile> (Throw a, lcl s) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1SyncThrow)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim1 wte1 obtain pc'
	where "\<tau>Exec_move P e1 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, e1, V, hp s \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule Sync_\<tau>Exec_meth_xt)
      moreover from bisim' bisim1_bsok[OF bisim2]
      have "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by -(rule bisim1_bisims1.bisim1SyncThrow, auto)
      ultimately show ?thesis using \<tau> by fastsimp
    qed
  qed auto
next
  case (bisim1Sync2 e1 V e2 v xs)
  note bisim1 = `\<And>xs. P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (Val v) e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Lock1Synchronized H a arrobj VV XS E2)
    hence [simp]: "VV = V" "v = Addr a" "E2 = e2" "H = h" "XS = xs" "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Lock\<rightarrow>a\<rbrace>" "e' = insync\<^bsub>V\<^esub> (a) e2"
      "h' = h" "xs' = xs[V := Addr a]" and V: "V < length xs" and ha: "h a = \<lfloor>arrobj\<rfloor>" by auto
    from V
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([], xs[V := Addr a], Suc (length (compE2 e1)), None) ([Addr a], xs[V := Addr a], Suc (Suc (length (compE2 e1))), None)"
      by -(rule \<tau>Exec1step,auto intro: exec_instr \<tau>move2_\<tau>moves2.intros simp add: exec_move_def)
    moreover from ha
    have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a], xs[V := Addr a], Suc (Suc (length (compE2 e1))), None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a\<rbrace>)
                        h ([], xs[V := Addr a], Suc (Suc (Suc (length (compE2 e1)))), None)"
      unfolding exec_move_def by -(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (length (compE2 e1)))) None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover from bisim1 bisim2 have "bsok E2 (Suc V)" "bsok e1 V"  by(auto dest: bisim1_bsok)
    from bisim1Sync4[OF bisim1_refl, OF this, of P h a "xs[V := Addr a]"]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (insync\<^bsub>V\<^esub> (a) e2, xs[V := Addr a]) \<leftrightarrow> ([], xs[V := Addr a], Suc (Suc (Suc (length (compE2 e1)))), None)" by simp
    moreover have "\<not> \<tau>move1 (sync\<^bsub>V\<^esub> (addr a) e2)" by(rule notI)(erule \<tau>move1.cases, auto elim: \<tau>move1.cases)
    ultimately show ?thesis by(fastsimp simp add: nat_number ta_bisim_def)
  next
    case (Synchronized1Null VV XS E H)
    hence [simp]: "VV = V" "v = Null" "E = e2" "H = h" "XS = xs" "e' = THROW NullPointer" "ta = \<epsilon>" "h' = h"
      "xs' = xs[V := Null]" and V: "V < length xs" by auto
    from V
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([], xs[V := Null], Suc (length (compE2 e1)), None) ([Null], xs[V := Null], Suc (Suc (length (compE2 e1))), None)"
      by -(rule \<tau>Exec1step,auto intro: exec_instr \<tau>move2_\<tau>moves2.intros simp add: exec_move_def)
    also have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Null], xs[V := Null], Suc (Suc (length (compE2 e1))), None) \<epsilon>
                        h ([Null], xs[V := Null], Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr) auto
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (length (compE2 e1)))) None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW NullPointer, xs[V := Null]) \<leftrightarrow> ([Null], (xs[V := Null]), Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro: bisim1Sync11)
    moreover have "\<not> \<tau>move1 (sync\<^bsub>V\<^esub> (null) e2)" by auto
    ultimately show ?thesis by(fastsimp simp add: nat_number)
  qed auto
next
  case (bisim1Sync3 e1 V e2 v xs)
  note bisim1 = `\<And>xs. P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (Val v) e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Lock1Synchronized H a arrobj VV XS E2)
    hence [simp]: "VV = V" "v = Addr a" "E2 = e2" "H = h" "XS = xs" "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Lock\<rightarrow>a\<rbrace>" "e' = insync\<^bsub>V\<^esub> (a) e2"
      "h' = h" "xs' = xs[V := Addr a]" and V: "V < length xs" and ha: "h a = \<lfloor>arrobj\<rfloor>" by auto
    from ha
    have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a], xs[V := Addr a], Suc (Suc (length (compE2 e1))), None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a\<rbrace>)
                        h ([], xs[V := Addr a], Suc (Suc (Suc (length (compE2 e1)))), None)"
      unfolding exec_move_def by -(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (length (compE2 e1)))) None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover from bisim1 bisim2 have "bsok E2 (Suc V)" "bsok e1 V"  by(auto dest: bisim1_bsok)
    from bisim1Sync4[OF bisim1_refl, OF this, of P h a "xs[V := Addr a]"]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (insync\<^bsub>V\<^esub> (a) e2, xs[V := Addr a]) \<leftrightarrow> ([], xs[V := Addr a], Suc (Suc (Suc (length (compE2 e1)))), None)" by simp
    moreover have "\<not> \<tau>move1 (sync\<^bsub>V\<^esub> (addr a) e2)" by(rule notI)(erule \<tau>move1.cases, auto elim: \<tau>move1.cases)
    ultimately show ?thesis by(fastsimp simp add: nat_number ta_bisim_def intro: \<tau>Exec_refl)
  next
    case (Synchronized1Null VV XS E H)
    hence [simp]: "VV = V" "v = Null" "E = e2" "H = h" "XS = xs" "e' = THROW NullPointer" "ta = \<epsilon>" "h' = h"
      "xs' = xs[V := Null]" and V: "V < length xs" by auto
    have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Null], xs[V := Null], Suc (Suc (length (compE2 e1))), None) \<epsilon>
                        h ([Null], xs[V := Null], Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr) auto
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (length (compE2 e1)))) None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW NullPointer, xs[V := Null]) \<leftrightarrow> ([Null], (xs[V := Null]), Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro: bisim1Sync11)
    moreover have "\<not> \<tau>move1 (sync\<^bsub>V\<^esub> (null) e2)" by auto
    ultimately show ?thesis by(fastsimp simp add: nat_number intro: \<tau>Exec_refl)
  qed auto
next
  case (bisim1Sync4 e2 V e2' xs stk loc pc xcp e1 a)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e2 :: T; P,Env',h \<turnstile>1 e2' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,Suc V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e2 e2' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim2 = `P,e2,Suc V,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim1 = `\<And>xs. P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note red = `P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 sync\<^bsub>V\<^esub> (e1) e2 :: T` have wte2: "P,Env@[Class Object] \<turnstile>1 e2 :: T" by auto
  from `P,Env',h \<turnstile>1 insync\<^bsub>V\<^esub> (a) e2' : T'` have wte2': "P,Env'@[Class Object],h \<turnstile>1 e2' : T'" by auto
  from red show ?case
  proof cases
    case (Synchronized1Red2 E s TA E' s' VV aa)
    hence [simp]: "VV = V" "aa = a" "E = e2'" "s = (h, xs)" "TA = ta" "e' = insync\<^bsub>V\<^esub> (a) E'" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>e2', (h, xs)\<rangle> -ta\<rightarrow> \<langle>E', (h', xs')\<rangle>" by auto
    from red have \<tau>: "\<tau>move1 (insync\<^bsub>V\<^esub> (a) e2') = \<tau>move1 e2'" by(auto intro: \<tau>move1InSync)
    from IH[OF red wte2 wte2'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e2,Suc V,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e2 e2' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (sync\<^bsub>V\<^esub> (e1) e2) (insync\<^bsub>V\<^esub> (a) e2') h stk loc (Suc (Suc (Suc (length (compE2 e1) + pc)))) xcp h' (Suc (Suc (Suc (length (compE2 e1) + pc'')))) stk'' loc'' xcp''"
      using exec' \<tau> by(cases "\<tau>move1 (insync\<^bsub>V\<^esub> (a) e2')")(fastsimp intro: exec_move_SyncI2)+
    moreover from bisim' bisim1_bsok[OF bisim1]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h' \<turnstile> (insync\<^bsub>V\<^esub> (a) E', xs') \<leftrightarrow> (stk'', loc'', (Suc (Suc (Suc (length (compE2 e1) + pc'')))), xcp'')"
      by(auto intro: bisim1_bisims1.bisim1Sync4)
    ultimately show ?thesis using \<tau> by fastsimp
  next
    case (Unlock1Synchronized XS VV a' aa v H)
    hence [simp]: "VV = V" "aa = a" "e2' = Val v" "H = h" "XS = xs" "e' = Val v" "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a'\<rbrace>" "h' = h" "xs' = xs"
      and V: "V < length xs" and xsV: "xs ! V = Addr a'" by auto
    from bisim2 wte2 have [simp]: "xcp = None" "xs = loc"
      and exec: "\<tau>Exec_move P e2 h (stk, loc, pc, xcp) ([v], loc, length (compE2 e2), None)"
      by(auto dest: bisim1Val2D1)
    let ?pc1 = "(Suc (Suc (Suc (length (compE2 e1) + length (compE2 e2)))))"
    note Insync_\<tau>Exec_meth_xt[OF exec, of V e1]
    also from V xsV have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([v], loc, ?pc1, None) ([Addr a', v], loc, Suc ?pc1, None)"
      by -(rule \<tau>Exec1step,auto simp add: exec_move_def intro: exec_instr \<tau>move2_\<tau>moves2.intros)
    also have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', v], loc, Suc ?pc1, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a'\<rbrace>) h ([v], loc, Suc (Suc ?pc1), None)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc1) None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover from bisim2 bisim1 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    from bisim1Sync6[OF this, of P h v xs]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (Val v, xs) \<leftrightarrow> ([v], xs, Suc (Suc ?pc1), None)"
      by(auto simp add: nat_number)
    ultimately show ?thesis by(fastsimp simp add: ta_bisim_def)
  next
    case (Unlock1SynchronizedNull XS VV aa v H)
    hence [simp]: "VV = V" "aa = a" "e2' = Val v" "H = h" "XS = xs" "e' = THROW NullPointer" "ta = \<epsilon>" "h' = h" "xs' = xs"
      and V: "V < length xs" and xsV: "xs ! V = Null" by auto
    from bisim2 wte2 have [simp]: "xcp = None" "xs = loc"
      and exec: "\<tau>Exec_move P e2 h (stk, loc, pc, xcp) ([v], loc, length (compE2 e2), None)"
      by(auto dest: bisim1Val2D1)
    let ?pc1 = "(Suc (Suc (Suc (length (compE2 e1) + length (compE2 e2)))))"
    note Insync_\<tau>Exec_meth_xt[OF exec, of V e1]
    also from V xsV have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([v], loc, ?pc1, None) ([Null, v], loc, Suc ?pc1, None)"
      by -(rule \<tau>Exec1step,auto intro: exec_instr \<tau>move2_\<tau>moves2.intros simp add: exec_move_def)
    also have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Null, v], loc, Suc ?pc1, None) \<epsilon> h ([Null, v], loc, Suc ?pc1, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc1) None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover from bisim2 bisim1 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    from bisim1Sync12[OF this, of P h xs v]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW NullPointer,xs) \<leftrightarrow> ([Null, v],xs,Suc ?pc1,\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto simp add: nat_number)
    ultimately show ?thesis by(fastsimp)
  next
    case (Unlock1SynchronizedFail XS VV a' aa v H)
    hence [simp]: "VV = V" "aa = a" "e2' = Val v" "H = h" "XS = xs" "e' = THROW IllegalMonitorState" "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a'\<rbrace>" "xs' = xs" "h' = h"
      and V: "V < length xs" and xsV: "xs ! V = Addr a'" by auto
    from bisim2 wte2 have [simp]: "xcp = None" "xs = loc"
      and exec: "\<tau>Exec_move P e2 h (stk, loc, pc, xcp) ([v], loc, length (compE2 e2), None)"
      by(auto dest: bisim1Val2D1)
    let ?pc1 = "(Suc (Suc (Suc (length (compE2 e1) + length (compE2 e2)))))"
    note Insync_\<tau>Exec_meth_xt[OF exec, of V e1]
    also from V xsV have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([v], loc, ?pc1, None) ([Addr a', v], loc, Suc ?pc1, None)"
      by -(rule \<tau>Exec1step,auto intro: exec_instr \<tau>move2_\<tau>moves2.intros simp add: exec_move_def)
    also have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', v], loc, Suc ?pc1, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a'\<rbrace>) h ([Addr a', v], loc, Suc ?pc1, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc1) None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover from bisim2 bisim1 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    from bisim1Sync13[OF this, of P h xs "Addr a'" v]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW IllegalMonitorState,xs) \<leftrightarrow> ([Addr a', v],xs,Suc ?pc1,\<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      by(auto simp add: nat_number)
    moreover have "\<not> \<tau>move1 (insync\<^bsub>V\<^esub> (a) Val v)" by auto
    ultimately show ?thesis by(fastsimp simp add: ta_bisim_def)
  next
    case (Synchronized1Throw2 XS VV a' aa ad H)
    hence [simp]: "VV = V" "aa = a" "e2' = Throw ad" "H = h" "XS = xs"  "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a'\<rbrace>" "e' = Throw ad"
      "h' = h" "xs' = xs" and xsV: "xs ! V = Addr a'" and V: "V < length xs" by auto
    let ?pc = "6 + length (compE2 e1) + length (compE2 e2)"
    let ?stk = "Addr ad # drop (size stk - 0) stk"
    from bisim2 have [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
    from wf bisim2 wte2' hconf wte2
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), xcp) ([Addr ad], loc, ?pc, None)"    
      by(auto intro: bisim1_insync_Throw_exec)
    also from xsV V 
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr ad], loc, ?pc, None) ([Addr a', Addr ad], loc, Suc ?pc, None)"
      by -(rule \<tau>Exec1step,auto intro: exec_instr \<tau>move2Sync7 simp add: exec_move_def)
    also have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', Addr ad], loc, Suc ?pc, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a'\<rbrace>) h ([Addr ad], loc, Suc (Suc ?pc), None)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc) None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (Throw ad, loc) \<leftrightarrow> ([Addr ad], loc, 8 + length (compE2 e1) + length (compE2 e2), None)"
      by(auto intro: bisim1Sync9)
    ultimately show ?thesis by(fastsimp simp add: add_assoc ta_bisim_def)
  next
    case (Synchronized1Throw2Fail XS VV a' aa ad H)
    hence [simp]: "VV = V" "aa = a" "e2' = Throw ad" "H = h" "XS = xs" "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a'\<rbrace>"
      "e' = THROW IllegalMonitorState" "h' = h" "xs' = xs" and xsV: "xs ! V = Addr a'" and V: "V < length xs" by auto
    let ?pc = "6 + length (compE2 e1) + length (compE2 e2)"
    let ?stk = "Addr ad # drop (size stk - 0) stk"
    from bisim2 have [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
    from wf bisim2 wte2' hconf wte2
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), xcp) ([Addr ad], loc, ?pc, None)"
      by(auto intro: bisim1_insync_Throw_exec)
    also from xsV V
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr ad], loc, ?pc, None) ([Addr a', Addr ad], loc, Suc ?pc, None)"
      by -(rule \<tau>Exec1step,auto intro: exec_instr \<tau>move2Sync7 simp add: exec_move_def)
    also have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', Addr ad], loc, Suc ?pc, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a'\<rbrace>) h ([Addr a', Addr ad], loc, Suc ?pc, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc) None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2) 
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW IllegalMonitorState, loc) \<leftrightarrow> ([Addr a', Addr ad], loc, 7 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      by(auto intro: bisim1Sync14)
    ultimately show ?thesis by(fastsimp simp add: add_assoc ta_bisim_def)
  next
    case (Synchronized1Throw2Null XS VV aa ad H)
    hence [simp]: "VV = V" "aa = a" "e2' = Throw ad" "H = h" "XS = xs" "ta = \<epsilon>" "e' = THROW NullPointer" "h' = h" "xs' = xs"
      and xsV: "xs ! V = Null" and V: "V < length xs" by auto
    let ?pc = "6 + length (compE2 e1) + length (compE2 e2)"
    let ?stk = "Addr ad # drop (size stk - 0) stk"
    from bisim2 have [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
    from wf bisim2 wte2' hconf wte2
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), xcp) ([Addr ad], loc, ?pc, None)"
      by(auto intro: bisim1_insync_Throw_exec)
    also from xsV V 
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr ad], loc, ?pc, None) ([Null, Addr ad], loc, Suc ?pc, None)"
      by -(rule \<tau>Exec1step,auto intro: exec_instr \<tau>move2Sync7 simp add: exec_move_def)
    also have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Null, Addr ad], loc, Suc ?pc, None) \<epsilon> h ([Null, Addr ad], loc, Suc ?pc, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc) None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2) 
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([Null, Addr ad], loc, 7 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro: bisim1Sync15)
    ultimately show ?thesis by(fastsimp simp add: add_assoc ta_bisim_def)
  qed auto
next
  case (bisim1Sync5 e1 V e2 a v xs)
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim1 = `\<And>xs. P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Val v,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Unlock1Synchronized XS VV a' aa vv H)
    hence [simp]: "VV = V" "aa = a" "vv = v" "H = h" "XS = xs" "e' = Val v" "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a'\<rbrace>" "h' = h" "xs' = xs"
      and V: "V < length xs" and xsV: "xs ! V = Addr a'" by auto
    let ?pc1 = "4 + length (compE2 e1) + length (compE2 e2)"
    have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', v], xs, ?pc1, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a'\<rbrace>) h ([v], xs, Suc ?pc1, None)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) ?pc1 None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover from bisim2 bisim1 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    from bisim1Sync6[OF this, of P h v xs]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (Val v, xs) \<leftrightarrow> ([v], xs, Suc ?pc1, None)"
      by(auto simp add: nat_number)
    moreover have "\<not> \<tau>move1 (insync\<^bsub>V\<^esub> (a) Val v)" by auto
    ultimately show ?thesis using xsV by(fastsimp simp add: nat_number ta_bisim_def intro: \<tau>Exec_refl)
  next
    case (Unlock1SynchronizedNull XS VV aa vv H)
    hence [simp]: "VV = V" "aa = a" "vv = v" "H = h" "XS = xs" "e' = THROW NullPointer" "ta = \<epsilon>" "h' = h" "xs' = xs"
      and V: "V < length xs" and xsV: "xs ! V = Null" by auto
    let ?pc1 = "4 + length (compE2 e1) + length (compE2 e2)"
    have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Null, v], xs, ?pc1, None) \<epsilon> h ([Null, v], xs, ?pc1, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) ?pc1 None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover from bisim2 bisim1 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    from bisim1Sync12[OF this, of P h xs v]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW NullPointer,xs) \<leftrightarrow> ([Null, v],xs,?pc1,\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto simp add: nat_number)
    moreover have "\<not> \<tau>move1 (insync\<^bsub>V\<^esub> (a) Val v)" by auto
    ultimately show ?thesis using xsV by(fastsimp simp add: nat_number intro: \<tau>Exec_refl)
  next
    case (Unlock1SynchronizedFail XS VV a' aa vv H)
    hence [simp]: "VV = V" "aa = a" "vv = v" "H = h" "XS = xs" "e' = THROW IllegalMonitorState" "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a'\<rbrace>" "xs' = xs" "h' = h"
      and V: "V < length xs" and xsV: "xs ! V = Addr a'" by auto
    let ?pc1 = "4 + length (compE2 e1) + length (compE2 e2)"
    have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', v], xs, ?pc1, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a'\<rbrace>) h ([Addr a', v], xs, ?pc1, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) ?pc1 None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover from bisim2 bisim1 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    from bisim1Sync13[OF this, of P h xs "Addr a'" v]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW IllegalMonitorState,xs) \<leftrightarrow> ([Addr a', v],xs,?pc1,\<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      by(auto simp add: nat_number)
    moreover have "\<not> \<tau>move1 (insync\<^bsub>V\<^esub> (a) Val v)" by auto
    ultimately show ?thesis using xsV by(fastsimp simp add: nat_number ta_bisim_def intro: \<tau>Exec_refl)
  qed auto
next
  case bisim1Sync6 thus ?case by auto
next
  case (bisim1Sync7 e1 V e2 a ad xs)
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim1 = `\<And>xs. P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw ad,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Synchronized1Throw2 XS VV a' aa ad' H)
    hence [simp]: "VV = V" "aa = a" "ad' = ad" "H = h" "XS = xs"  "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a'\<rbrace>" "e' = Throw ad"
      "h' = h" "xs' = xs" and xsV: "xs ! V = Addr a'" and V: "V < length xs" by auto
    let ?pc = "6 + length (compE2 e1) + length (compE2 e2)"
    from xsV V
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr ad], xs, ?pc, None) ([Addr a', Addr ad], xs, Suc ?pc, None)"
      by -(rule \<tau>Exec1step,auto intro: exec_instr \<tau>move2Sync7 simp add: exec_move_def)
    moreover have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', Addr ad], xs, Suc ?pc, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a'\<rbrace>) h ([Addr ad], xs, Suc (Suc ?pc), None)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc) None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (Throw ad, xs) \<leftrightarrow> ([Addr ad], xs, 8 + length (compE2 e1) + length (compE2 e2), None)"
      by(auto intro: bisim1Sync9)
    moreover have "\<not> \<tau>move1 (insync\<^bsub>V\<^esub> (a) Throw ad)" by fastsimp
    ultimately show ?thesis by(fastsimp simp add: add_assoc nat_number ta_bisim_def)
  next
    case (Synchronized1Throw2Fail XS VV a' aa ad' H)
    hence [simp]: "VV = V" "aa = a" "ad' = ad" "H = h" "XS = xs" "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a'\<rbrace>"
      "e' = THROW IllegalMonitorState" "h' = h" "xs' = xs" and xsV: "xs ! V = Addr a'" and V: "V < length xs" by auto
    let ?pc = "6 + length (compE2 e1) + length (compE2 e2)"
    from xsV V
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr ad], xs, ?pc, None) ([Addr a', Addr ad], xs, Suc ?pc, None)"
      by -(rule \<tau>Exec1step,auto intro: exec_instr \<tau>move2Sync7 simp add: exec_move_def)
    moreover have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', Addr ad], xs, Suc ?pc, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a'\<rbrace>) h ([Addr a', Addr ad], xs, Suc ?pc, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc) None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2) 
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW IllegalMonitorState, xs) \<leftrightarrow> ([Addr a', Addr ad], xs, 7 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      by(auto intro: bisim1Sync14)
    moreover have "\<not> \<tau>move1 (insync\<^bsub>V\<^esub> (a) Throw ad)" by fastsimp
    ultimately show ?thesis by(fastsimp simp add: add_assoc ta_bisim_def)
  next
    case (Synchronized1Throw2Null XS VV aa ad' H)
    hence [simp]: "VV = V" "aa = a" "ad' = ad" "H = h" "XS = xs" "ta = \<epsilon>" "e' = THROW NullPointer" "h' = h" "xs' = xs"
      and xsV: "xs ! V = Null" and V: "V < length xs" by auto
    let ?pc = "6 + length (compE2 e1) + length (compE2 e2)"
    from xsV V 
    have "\<tau>Exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr ad], xs, ?pc, None) ([Null, Addr ad], xs, Suc ?pc, None)"
      by -(rule \<tau>Exec1step,auto intro: exec_instr \<tau>move2Sync7 simp add: exec_move_def)
    also have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Null, Addr ad], xs, Suc ?pc, None) \<epsilon> h ([Null, Addr ad], xs, Suc ?pc, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc) None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2) 
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([Null, Addr ad], xs, 7 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro: bisim1Sync15)
    moreover have "\<not> \<tau>move1 (insync\<^bsub>V\<^esub> (a) Throw ad)" by fastsimp
    ultimately show ?thesis by(fastsimp simp add: add_assoc ta_bisim_def)
  qed auto
next
  case (bisim1Sync8 e1 V e2 a ad xs)
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim1 = `\<And>xs. P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw ad,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Synchronized1Throw2 XS VV a' aa ad' H)
    hence [simp]: "VV = V" "aa = a" "ad' = ad" "H = h" "XS = xs"  "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a'\<rbrace>" "e' = Throw ad"
      "h' = h" "xs' = xs" and xsV: "xs ! V = Addr a'" and V: "V < length xs" by auto
    let ?pc = "7 + length (compE2 e1) + length (compE2 e2)"
    have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', Addr ad], xs, ?pc, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a'\<rbrace>) h ([Addr ad], xs, Suc ?pc, None)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) ?pc None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (Throw ad, xs) \<leftrightarrow> ([Addr ad], xs, 8 + length (compE2 e1) + length (compE2 e2), None)"
      by(auto intro: bisim1Sync9)
    moreover have "\<not> \<tau>move1 (insync\<^bsub>V\<^esub> (a) Throw ad)" by fastsimp
    ultimately show ?thesis using xsV by(fastsimp simp add: add_assoc nat_number ta_bisim_def intro: \<tau>Exec_refl)
  next
    case (Synchronized1Throw2Fail XS VV a' aa ad' H)
    hence [simp]: "VV = V" "aa = a" "ad' = ad" "H = h" "XS = xs" "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a'\<rbrace>"
      "e' = THROW IllegalMonitorState" "h' = h" "xs' = xs" and xsV: "xs ! V = Addr a'" and V: "V < length xs" by auto
    let ?pc = "7 + length (compE2 e1) + length (compE2 e2)"
    have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', Addr ad], xs, ?pc, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a'\<rbrace>) h ([Addr a', Addr ad], xs, ?pc, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) ?pc None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2) 
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW IllegalMonitorState, xs) \<leftrightarrow> ([Addr a', Addr ad], xs, ?pc, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      by(auto intro: bisim1Sync14)
    moreover have "\<not> \<tau>move1 (insync\<^bsub>V\<^esub> (a) Throw ad)" by fastsimp
    ultimately show ?thesis using xsV by(fastsimp simp add: add_assoc ta_bisim_def intro: \<tau>Exec_refl)
  next
    case (Synchronized1Throw2Null XS VV aa ad' H)
    hence [simp]: "VV = V" "aa = a" "ad' = ad" "H = h" "XS = xs" "ta = \<epsilon>" "e' = THROW NullPointer" "h' = h" "xs' = xs"
      and xsV: "xs ! V = Null" and V: "V < length xs" by auto
    let ?pc = "7 + length (compE2 e1) + length (compE2 e2)"
    have "exec_move P (sync\<^bsub>V\<^esub> (e1) e2) h ([Null, Addr ad], xs, ?pc, None) \<epsilon> h ([Null, Addr ad], xs, ?pc, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) ?pc None"
      by(rule notI, erule \<tau>move2.cases)(auto dest: \<tau>move2_pc_length_compE2) 
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([Null, Addr ad], xs, ?pc, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro: bisim1Sync15)
    moreover have "\<not> \<tau>move1 (insync\<^bsub>V\<^esub> (a) Throw ad)" by fastsimp
    ultimately show ?thesis using xsV by(fastsimp simp add: add_assoc ta_bisim_def intro: \<tau>Exec_refl)
  qed auto
next
  case bisim1Sync9 thus ?case by auto
next
  case bisim1Sync10 thus ?case by auto
next
  case bisim1Sync11 thus ?case by auto
next
  case bisim1Sync12 thus ?case by auto
next
  case bisim1Sync13 thus ?case by auto
next
  case bisim1Sync14 thus ?case by auto
next
  case bisim1Sync15 thus ?case by auto
next
  case bisim1SyncThrow thus ?case by auto
next
  case (bisim1Seq1 e1 n e1' xs stk loc pc xcp e2)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e1 :: T; P,Env',h \<turnstile>1 e1' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e1,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e1 e1' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,e1,n,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,e2,n,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note red = `P \<turnstile>1 \<langle>e1';; e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 e1;; e2 :: T` obtain T1 where wte1: "P,Env \<turnstile>1 e1 :: T1" by auto
  from `P,Env',h \<turnstile>1 e1';; e2 : T'` obtain T1' where wte1': "P,Env',h \<turnstile>1 e1' : T1'" by auto
  from red show ?case
  proof cases
    case (Seq1Red E s TA E' s' E2)
    hence [simp]: "E = e1'" "E2 = e2" "s = (h, xs)" "TA = ta" "e' = E';;e2" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>e1', (h, xs)\<rangle> -ta\<rightarrow> \<langle>E', (h', xs')\<rangle>" by auto
    from red have \<tau>: "\<tau>move1 (e1';; e2) = \<tau>move1 e1'" by(auto intro: \<tau>move1Seq)
    with IH[OF red wte1 wte1'] `bsok e2 n` show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisim1Seq1 exec_move_SeqI1)
  next
    case (Red1Seq v E s)
    hence [simp]: "e1' = Val v" "E = e2" "s = (h, xs)" "ta = \<epsilon>" "e' = e2" "h' = h" "xs' = xs" by auto
    from bisim1 wte1 have s: "xcp = None" "lcl s = loc"
      and "\<tau>Exec_move P e1 h (stk, loc, pc, xcp) ([v], loc, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (e1;; e2) h (stk, loc, pc, xcp) ([v], loc, length (compE2 e1), None)"
      by-(rule Seq_\<tau>Exec_meth_xt1)
    moreover have "exec_move P (e1;; e2) h ([v], loc, length (compE2 e1), None) \<epsilon> h ([], loc, Suc (length (compE2 e1)), None)"
      unfolding exec_move_def by(rule exec_instr, auto)
    moreover have "\<tau>move2 (e1;;e2) (length (compE2 e1)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from bisim1 bisim2 have "bsok e1 n" "bsok e2 n" by(auto dest: bisim1_bsok)
    with bisim1_refl[of e2 n P h loc]
    have "P, e1;; e2, n, hp s \<turnstile> (e2, lcl s) \<leftrightarrow> ([], loc, Suc (length (compE2 e1) + 0), None)"
      unfolding s by-(rule bisim1Seq2, auto)
    moreover have "\<not> \<tau>move1 (Val v;; e2)" by(auto)
    ultimately show ?thesis by(fastsimp)
  next
    case (Seq1Throw a E s)
    hence [simp]: "e1' = Throw a" "E = e2" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw a" "h' = h" "xs' = xs" by auto
    have \<tau>: "\<tau>move1 (Throw a;; e2)" by(rule \<tau>move1SeqThrow)
    from bisim1 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 bisim1_bsok[OF bisim2]
      have "P, e1;; e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1SeqThrow1)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim1 wte1 obtain pc'
	where "\<tau>Exec_move P e1 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, e1, n, hp s \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (e1;;e2) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule Seq_\<tau>Exec_meth_xt1)
      moreover from bisim' bisim1_bsok[OF bisim2]
      have "P, e1;;e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1SeqThrow1, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case bisim1SeqThrow1 thus ?case by fastsimp
next
  case (bisim1Seq2 e2 n e2' xs stk loc pc xcp e1)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e2 :: T; P,Env',h \<turnstile>1 e2' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e2 e2' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim2 = `P,e2,n,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim1 = `\<And>xs. P,e1,n,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note red = `P \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 e1;; e2 :: T` have wte2: "P,Env \<turnstile>1 e2 :: T" by auto
  from IH[OF red wte2 `P,Env',h \<turnstile>1 e2' : T'`] obtain pc'' stk'' loc'' xcp''
    where bisim': "P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
    and exec': "?exec ta e2 e2' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
  have "?exec ta (e1;; e2) e2' h stk loc (Suc (length (compE2 e1) + pc)) xcp h' (Suc (length (compE2 e1) + pc'')) stk'' loc'' xcp''"
    using exec' by(cases "\<tau>move1 e2'")(fastsimp intro: Seq_\<tau>Exec_meth_xt2 exec_move_SeqI2)+
  with bisim' `bsok e1 n` show ?case by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1Seq2)
next
  case (bisim1Cond1 E n e xs stk loc pc xcp e1 e2)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 E :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim1 = `\<And>xs. P,e1,n,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e2,n,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,Env \<turnstile>1 if (E) e1 else e2 :: T` have wtE: "P,Env \<turnstile>1 E :: Boolean" by auto
  from `P,Env',h \<turnstile>1 if (e) e1 else e2 : T'` have wtE': "P,Env',h \<turnstile>1 e : Boolean" by auto
  from `P \<turnstile>1 \<langle>if (e) e1 else e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Cond1Red b s TA b' s' E1 E2)
    hence [simp]: "b = e" "E1 = e1" "E2 = e2" "s = (h, xs)" "TA = ta" "e' = if (b') e1 else e2" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>b',(h', xs')\<rangle>" by auto
    from red have "\<tau>move1 (if (e) e1 else e2) = \<tau>move1 e" by(auto intro: \<tau>move1Cond)
    with IH[OF red wtE wtE'] bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2] show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisim1Cond1 exec_move_CondI1)
  next
    case (Red1CondT E1 E2 s)
    hence [simp]: "e = true" "E1 = e1" "E2 = e2" "s = (h, xs)" "e' = e1" "ta = \<epsilon>" "h' = h" "xs' = xs" by auto
    have "\<not> \<tau>move1 (if (true) e1 else e2)" by auto
    moreover from bisim wtE have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([Bool True], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (if (E) e1 else e2) h (stk, loc, pc, xcp) ([Bool True], loc, length (compE2 E), None)"
      by-(rule Cond_\<tau>Exec_meth_xt_Cond)
    moreover have "exec_move P (if (E) e1 else e2) h ([Bool True], loc, length (compE2 E), None) \<epsilon> h ([], loc, Suc (length (compE2 E)), None)"
      unfolding exec_move_def by(rule exec_instr, auto)
    moreover have "\<tau>move2 (if (E) e1 else e2) (length (compE2 E)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from bisim bisim1 bisim2 have "bsok E n" "bsok e1 n" "bsok e2 n" by(auto dest: bisim1_bsok)
    with bisim1_refl[of e1 n P h loc]
    have "P, if (E) e1 else e2, n, h \<turnstile> (e1, xs) \<leftrightarrow> ([], loc, Suc (length (compE2 E) + 0), None)"
      unfolding s by-(rule bisim1CondThen, auto)
    ultimately show ?thesis by (fastsimp intro: \<tau>Exec_refl)
  next
    case (Red1CondF E1 E2 s)
    hence [simp]: "e = false" "E1 = e1" "E2 = e2" "s = (h, xs)" "e' = e2" "ta = \<epsilon>" "h' = h" "xs' = xs" by auto
    have "\<not> \<tau>move1 (if (false) e1 else e2)" by auto
    moreover from bisim wtE have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([Bool False], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (if (E) e1 else e2) h (stk, loc, pc, xcp) ([Bool False], loc, length (compE2 E), None)"
      by-(rule Cond_\<tau>Exec_meth_xt_Cond)
    moreover have "exec_move P (if (E) e1 else e2) h ([Bool False], loc, length (compE2 E), None) \<epsilon> h ([], loc, Suc (Suc (length (compE2 E) + length (compE2 e1))), None)"
      unfolding exec_move_def by(rule exec_instr)(auto)
    moreover have "\<tau>move2 (if (E) e1 else e2) (length (compE2 E)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from bisim bisim1 bisim2 have "bsok E n" "bsok e1 n" "bsok e2 n" by(auto dest: bisim1_bsok)
    with bisim1_refl[of e2 n P h loc]
    have "P, if (E) e1 else e2, n, h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, (Suc (Suc (length (compE2 E) + length (compE2 e1) + 0))), None)"
      unfolding s by-(rule bisim1CondElse, auto)
    ultimately show ?thesis using s by auto fastsimp
  next
    case (Cond1Throw a E1 E2 s)
    hence [simp]: "e = Throw a" "E1 = e1" "E2 = e2" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw a" "h' = h" "xs' = xs" by auto
    have \<tau>: "\<tau>move1 (if (Throw a) e1 else e2)" by(rule \<tau>move1CondThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
      have "P, if (E) e1 else e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1CondThrow)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim wtE obtain pc'
	where "\<tau>Exec_move P E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (if (E) e1 else e2) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule Cond_\<tau>Exec_meth_xt_Cond)
      moreover from bisim' bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
      have "P, if (E) e1 else e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1CondThrow, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case (bisim1CondThen e1 n e1' xs stk loc pc xcp e e2)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e1 :: T; P,Env',h \<turnstile>1 e1' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e1,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e1 e1' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,e1,n,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e2,n,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,Env \<turnstile>1 if (e) e1 else e2 :: T` obtain T1 where wte1: "P,Env \<turnstile>1 e1 :: T1" by auto
  from IH[OF `P \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` wte1 `P,Env',h \<turnstile>1 e1' : T'`] obtain pc'' stk'' loc'' xcp''
    where bisim': "P,e1,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
    and exec': "?exec ta e1 e1' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
  have "?exec ta (if (e) e1 else e2) e1' h stk loc (Suc (length (compE2 e) + pc)) xcp h' (Suc (length (compE2 e) + pc'')) stk'' loc'' xcp''"
    using exec' by(cases "\<tau>move1 e1'")(fastsimp intro: Cond_\<tau>Exec_meth_xt_then exec_move_CondI2)+
  with bisim' `bsok e n` `bsok e2 n` show ?case
    by(fastsimp intro: bisim1_bisims1.bisim1CondThen split: split_if_asm)
next
  case (bisim1CondElse e2 n e2' xs stk loc pc xcp e e1)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e2 :: T; P,Env',h \<turnstile>1 e2' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e2 e2' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim2 = `P,e2,n,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim1 = `\<And>xs. P,e1,n,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,Env \<turnstile>1 if (e) e1 else e2 :: T` obtain T2 where wte2: "P,Env \<turnstile>1 e2 :: T2" by auto
  from IH[OF `P \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` wte2 `P,Env',h \<turnstile>1 e2' : T'`] obtain pc'' stk'' loc'' xcp''
    where bisim': "P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
    and exec': "?exec ta e2 e2' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
  have "?exec ta (if (e) e1 else e2) e2' h stk loc (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc))) xcp h' (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc''))) stk'' loc'' xcp''"
    using exec' by(cases "\<tau>move1 e2'")(fastsimp intro: Cond_\<tau>Exec_meth_xt_else exec_move_CondI3)+
  with bisim' `bsok e n` `bsok e1 n` show ?case
    by(fastsimp intro: bisim1_bisims1.bisim1CondElse split: split_if_asm)
next
  case bisim1CondThrow thus ?case by auto
next
  case (bisim1While1 c n e xs)
  note bisim1 = `\<And>xs. P,c,n,h \<turnstile> (c, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P \<turnstile>1 \<langle>while (c) e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Red1While C E s)
    hence [simp]: "C = c" "E = e" "s = (h, xs)" "ta = \<epsilon>" "e' = if (c) (e;; while (c) e) else unit" "h' = h" "xs' = xs" by auto
    have "\<tau>move1 (while (c) e)" by(rule \<tau>move1WhileRed)
    moreover from `bsok c n` `bsok e n`
    have "P,while (c) e,n,h \<turnstile> (if (c) (e;; while (c) e) else unit, xs) \<leftrightarrow> ([], xs, 0, None)"
      by(rule bisim1_bisims1.bisim1While3[OF bisim1_refl])
    ultimately show ?thesis by(fastsimp intro: \<tau>Exec_refl)
  qed auto
next
  case (bisim1While3 c n c' xs stk loc pc xcp e)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>c',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 c :: T; P,Env',h \<turnstile>1 c' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,c,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta c c' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,c,n,h \<turnstile> (c', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,Env \<turnstile>1 while (c) e :: T` have wtc: "P,Env \<turnstile>1 c :: Boolean" by auto
  from `P,Env',h \<turnstile>1 if (c') (e;; while (c) e) else unit : T'` have wtc': "P,Env',h \<turnstile>1 c' : Boolean" by auto
  from `P \<turnstile>1 \<langle>if (c') (e;; while (c) e) else unit,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Cond1Red b s TA b' s' E1 E2)
    hence [simp]: "b = c'" "E1 = e;; while (c) e" "E2 = unit" "s = (h, xs)" "TA = ta" "e' = if (b') (e;; while (c) e) else unit" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>c',(h, xs)\<rangle> -ta\<rightarrow> \<langle>b',(h', xs')\<rangle>" by auto
    from red have "\<tau>move1 (if (c') (e;; while (c) e) else unit) = \<tau>move1 c'" by(auto intro: \<tau>move1Cond)
    with IH[OF red wtc wtc'] bisim1_bsok[OF bisim2] show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisim1While3 exec_move_WhileI1)
  next
    case (Red1CondT E1 E2 s)
    hence [simp]: "c' = true" "E1 = (e;; while (c) e)" "E2 = unit" "s = (h, xs)" "e' = e;; while (c) e" "ta = \<epsilon>" "h' = h" "xs' = xs" by auto
    have "\<not> \<tau>move1 (if (c') (e;; while (c) e) else unit)" by auto
    moreover from wtc bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P c h (stk, loc, pc, xcp) ([Bool True], loc, length (compE2 c), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (while (c) e) h (stk, loc, pc, xcp) ([Bool True], loc, length (compE2 c), None)"
      by-(rule While_\<tau>Exec_meth_xt1)
    moreover have "exec_move P (while (c) e) h ([Bool True], loc, length (compE2 c), None) \<epsilon> h ([], loc, Suc (length (compE2 c)), None)"
      unfolding exec_move_def by(rule exec_instr, auto)
    moreover have "\<tau>move2 (while (c) e) (length (compE2 c)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from bisim1 bisim2 have "bsok c n" "bsok e n" by(auto dest: bisim1_bsok)
    with bisim1_refl[of e n P h loc]
    have "P, while (c) e, n, h \<turnstile> (e;; while (c) e, xs) \<leftrightarrow> ([], loc, Suc (length (compE2 c) + 0), None)"
      unfolding s by-(rule bisim1While4, auto)
    ultimately show ?thesis by (fastsimp intro: \<tau>Exec_refl)
  next
    case (Red1CondF E1 E2 s)
    hence [simp]: "c' = false" "E1 = e;; while (c) e" "E2 = unit" "s = (h, xs)" "e' = unit" "ta = \<epsilon>" "h' = h" "xs' = xs" by auto
    have "\<not> \<tau>move1 (if (false) (e;;while (c) e) else unit)" by auto
    moreover from bisim1 wtc have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P c h (stk, loc, pc, xcp) ([Bool False], loc, length (compE2 c), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (while (c) e) h (stk, loc, pc, xcp) ([Bool False], loc, length (compE2 c), None)"
      by-(rule While_\<tau>Exec_meth_xt1)
    moreover have "exec_move P (while (c) e) h ([Bool False], loc, length (compE2 c), None) \<epsilon> h ([], loc, Suc (Suc (Suc (length (compE2 c) + length (compE2 e)))), None)"
      by(auto intro!: exec_instr simp add: exec_move_def)
    moreover have "\<tau>move2 (while (c) e) (length (compE2 c)) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from bisim1 bisim2 have "bsok c n" "bsok e n" by(auto dest: bisim1_bsok)
    hence "P, while (c) e, n, h \<turnstile> (unit, xs) \<leftrightarrow> ([], loc, (Suc (Suc (Suc (length (compE2 c) + length (compE2 e))))), None)"
      unfolding s by-(rule bisim1While7, auto)
    ultimately show ?thesis using s by auto fastsimp
  next
    case (Cond1Throw a E1 E2 s)
    hence [simp]: "c' = Throw a" "E1 = e;; while (c) e" "E2 = unit" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw a" "h' = h" "xs' = xs" by auto
    have \<tau>: "\<tau>move1 (if (c') (e;; while (c) e) else unit)" by(auto intro: \<tau>move1CondThrow)
    from bisim1 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 bisim1_bsok[OF bisim2]
      have "P, while (c) e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1WhileThrow1)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim1 wtc obtain pc'
	where "\<tau>Exec_move P c h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, c, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (while (c) e) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule While_\<tau>Exec_meth_xt1)
      moreover from bisim' bisim1_bsok[OF bisim2]
      have "P, while (c) e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1WhileThrow1, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case (bisim1While4 E n e xs stk loc pc xcp c)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 E :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim2 = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim1 = `\<And>xs. P,c,n,h \<turnstile> (c, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,Env \<turnstile>1 while (c) E :: T` obtain TE where wte: "P,Env \<turnstile>1 E :: TE" by auto
  from `P,Env',h \<turnstile>1 e;; while (c) E : T'` obtain TE' where wte': "P,Env',h \<turnstile>1 e : TE'" by auto
  from `P \<turnstile>1 \<langle>e;; while (c) E,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Seq1Red EE s TA E' s' E2)
    hence [simp]: "EE = e" "E2 = while (c) E" "s = (h, xs)" "TA = ta" "e' = E';;while (c) E" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>e, (h, xs)\<rangle> -ta\<rightarrow> \<langle>E', (h', xs')\<rangle>" by auto
    from red have \<tau>: "\<tau>move1 (e;; while (c) E) = \<tau>move1 e" by(auto intro: \<tau>move1Seq)
    with IH[OF red wte wte'] obtain pc'' stk'' loc'' xcp''
      where bisim: "P,E,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (while (c) E) (e;;while (c) E) h stk loc (Suc (length (compE2 c) + pc)) xcp h' (Suc (length (compE2 c) + pc'')) stk'' loc'' xcp''"
    proof(cases "\<tau>move1 (e;; while (c) E)")
      case True
      with exec' show ?thesis using \<tau> by(fastsimp intro: While_\<tau>Exec_meth_xt2)
    next
      case False
      with exec' \<tau> obtain ta' pc' stk' loc' xcp'
	where e: "\<tau>Exec_move P E h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
	and e': "exec_move P E h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 E pc' xcp'" and ta': "ta_bisim (wbisim1 P) ta ta'" by auto
      from e' have "exec_move P (while (c) E) h (stk', loc', Suc (length (compE2 c) + pc'), xcp') ta' h' (stk'', loc'', Suc (length (compE2 c) + pc''), xcp'')"
	by(rule exec_move_WhileI2)
      moreover from \<tau>' e' have "\<tau>move2 (while (c) E) (Suc (length (compE2 c) + pc')) xcp' \<Longrightarrow> False"
	by(fastsimp elim: \<tau>move2_cases intro: \<tau>move2xcp dest: \<tau>move2_pc_length_compE2)
      ultimately show ?thesis using e False ta' by(fastsimp intro: While_\<tau>Exec_meth_xt2 simp del: split_paired_Ex)
    qed
    with bisim \<tau> bisim1_bsok[OF bisim1] show ?thesis by(fastsimp intro: bisim1_bisims1.bisim1While4)
  next
    case (Red1Seq v EE s)
    hence [simp]: "e = Val v" "EE = while (c) E" "s = (h, xs)" "ta = \<epsilon>" "e' = while (c) E" "h' = h" "xs' = xs" by auto
    from bisim2 wte have s: "xcp = None" "lcl s = loc"
      and "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (while (c) E) h (stk, loc, Suc (length (compE2 c) + pc), xcp) ([v], loc, Suc (length (compE2 c) + length (compE2 E)), None)"
      by-(rule While_\<tau>Exec_meth_xt2)
    moreover
    have "exec_move P (while (c) E) h ([v], loc, Suc (length (compE2 c) + length (compE2 E)), None) \<epsilon> h ([], loc, Suc (Suc (length (compE2 c) + length (compE2 E))), None)"
      unfolding exec_move_def by(rule exec_instr, auto)
    moreover have "\<tau>move2 (while (c) E) (Suc (length (compE2 c) + length (compE2 E))) None \<Longrightarrow> False"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover from bisim1 bisim2 have "bsok c n" "bsok E n" by(auto dest: bisim1_bsok)
    hence "P, while (c) E, n, h \<turnstile> (while (c) E, xs) \<leftrightarrow> ([], xs, (Suc (Suc (length (compE2 c) + length (compE2 E)))), None)"
      unfolding s by(auto intro: bisim1While6)
    moreover have "\<not> \<tau>move1 (e;; while (c) E)" by(auto)
    ultimately show ?thesis using s by(fastsimp)
  next
    case (Seq1Throw a EE s)
    hence [simp]: "e = Throw a" "EE = while (c) E" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw a" "h' = h" "xs' = xs" by auto
    have \<tau>: "\<tau>move1 (e;; while (c) E)" by(auto intro: \<tau>move1SeqThrow)
    from bisim2 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim2 bisim1_bsok[OF bisim1]
      have "P, while (c) E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (length (compE2 c) + pc), xcp)"
	by(auto intro: bisim1WhileThrow2)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim2 wte obtain pc'
	where "\<tau>Exec_move P E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, n, hp s \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (while (c) E) h (stk, loc, Suc (length (compE2 c) + pc), None) ([Addr a], loc, Suc (length (compE2 c) + pc'), \<lfloor>a\<rfloor>)"
	by-(rule While_\<tau>Exec_meth_xt2)
      moreover from bisim' bisim1_bsok[OF bisim1]
      have "P, while (c) E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, Suc (length (compE2 c) + pc'), \<lfloor>a\<rfloor>)"
	by-(rule bisim1WhileThrow2, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case (bisim1While6 c n e xs)
  note bisim1 = `\<And>xs. P,c,n,h \<turnstile> (c, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P \<turnstile>1 \<langle>while (c) e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Red1While C' E s)
    hence [simp]: "C' = c" "E = e" "s = (h, xs)" "ta = \<epsilon>" "e' = if (c) (e;; while (c) e) else unit" "h' = h" "xs' = xs" by auto
    have "\<tau>move1 (while (c) e)" by(rule \<tau>move1WhileRed)
    moreover from bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
    have "P,while (c) e,n,h \<turnstile> (if (c) (e;; while (c) e) else unit, xs) \<leftrightarrow> ([], xs, 0, None)"
      by(rule bisim1_bisims1.bisim1While3[OF bisim1_refl])
    moreover have "\<tau>Exec_move P (while (c) e) h ([], xs, Suc (Suc (length (compE2 c) + length (compE2 e))), None) ([], xs, 0, None)"
      by(rule \<tau>Exec1step)(auto simp add: exec_move_def intro: exec_instr \<tau>move2_\<tau>moves2.intros)
    ultimately show ?thesis by(fastsimp)
  qed auto
next
  case bisim1While7 thus ?case by fastsimp
next
  case bisim1WhileThrow1 thus ?case by auto
next
  case bisim1WhileThrow2 thus ?case by auto
next
  case (bisim1Throw1 E n e xs stk loc pc xcp)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 E :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P \<turnstile>1 \<langle>throw e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 throw E :: T` obtain TE where wtE: "P,Env \<turnstile>1 E :: TE" by auto
  from `P,Env',h \<turnstile>1 throw e : T'` obtain Te' where wte: "P,Env',h \<turnstile>1 e : Te'" by auto
  from red show ?case
  proof cases
    case (Throw1Red ee s TA E' s')
    hence [simp]: "ee = e" "s = (h, xs)" "TA = ta" "e' = throw E'" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>e, (h, xs)\<rangle> -ta\<rightarrow> \<langle>E', (h', xs')\<rangle>" by auto
    from red have "\<tau>move1 (throw e) = \<tau>move1 e" by(auto intro: \<tau>move1Throw)
    with IH[OF red wtE wte] show ?thesis by(fastsimp intro: bisim1_bisims1.bisim1Throw1 exec_move_ThrowI)
  next
    case (Red1ThrowNull s)
    hence [simp]: "e = null" "s = (h, xs)" "ta = \<epsilon>" "e' = THROW NullPointer" "h' = h" "xs' = xs" by auto
    from bisim wtE have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([Null], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (throw E) h (stk, loc, pc, xcp) ([Null], loc, length (compE2 E), None)"
      by-(rule Throw_\<tau>Exec_meth_xt)
    also have "\<tau>Exec_move P (throw E) h ([Null], loc, length (compE2 E), None) ([Null], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule \<tau>Exec1step)(auto intro: exec_instr \<tau>move2_\<tau>moves2.intros simp add: exec_move_def)
    also from bisim have "bsok E n" by(auto dest: bisim1_bsok)
    hence "P, throw E, n, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([Null], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding s by(rule bisim1ThrowNull)
    moreover have "\<tau>move1 (throw e)" by(auto intro: \<tau>move1ThrowNull)
    ultimately show ?thesis by auto
  next
    case (Throw1Throw a s)
    hence [simp]: "e = Throw a" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw a" "h' = h" "xs' = xs" by auto
    have \<tau>: "\<tau>move1 (throw (Throw a))" by(rule \<tau>move1ThrowThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume "xcp = \<lfloor>a\<rfloor>"
      with bisim show ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl bisim1ThrowThrow)
    next
      assume [simp]: "xcp = None"
      from bisim wtE obtain pc'
	where "\<tau>Exec_move P E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim: "P, E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and s: "lcl s = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (throw E) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by -(rule Throw_\<tau>Exec_meth_xt)
      moreover from bisim have "P, throw E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by(rule bisim1ThrowThrow)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed(auto)
next
  case bisim1Throw2 thus ?case by auto
next
  case bisim1ThrowNull thus ?case by auto
next
  case bisim1ThrowThrow thus ?case by auto
next
  case (bisim1Try E V e xs stk loc pc xcp e2 C')
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 E :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,E,V,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note red = `P \<turnstile>1 \<langle>try e catch(C' V) e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 try E catch(C' V) e2 :: T` obtain TE
    where wtE: "P,Env \<turnstile>1 E :: TE" by auto
  from `P,Env',h \<turnstile>1 try e catch(C' V) e2 : T'` obtain Te'
    where wte: "P,Env',h \<turnstile>1 e : Te'" by auto
  from red show ?case
  proof cases
    case (Try1Red EE s TA E' s' CC VV E2)
    hence [simp]: "EE = e" "CC = C'" "VV = V" "E2 = e2" "s = (h, xs)" "TA = ta" "e' = try E' catch(C' V) e2"
      "s' = (h', xs')" and red: "P \<turnstile>1 \<langle>e, (h, xs)\<rangle> -ta\<rightarrow> \<langle>E', (h', xs')\<rangle>" by auto
    from red have "\<tau>move1 (try e catch(C' V) e2) = \<tau>move1 e" by(auto intro: \<tau>move1Try)
    with IH[OF red wtE wte] bisim1_bsok[OF bisim2] show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisim1Try exec_move_TryI1)
  next
    case (Red1Try v CC VV E2 s)
    hence [simp]: "e = Val v" "CC = C'" "VV = V" "E2 = e2" "s = (h, xs)" "ta = \<epsilon>" "e' = Val v" "h' = h" "xs' = xs" by auto
    have \<tau>: "\<tau>move1 (try Val v catch(C' V) e2)" by(rule \<tau>move1TryRed)
    from bisim1 wtE have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      and B: "bsok E V" by(auto dest: bisim1Val2D1 bisim1_bsok)
    hence "\<tau>Exec_move P (try E catch(C' V) e2) h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      by-(rule Try_\<tau>Exec_meth_xt1)
    also have "\<tau>Exec_move P (try E catch(C' V) e2) h ([v], loc, length (compE2 E), None) ([v], loc, length (compE2 (try E catch(C' V) e2)), None)"
      by(rule \<tau>Exec1step)(auto intro: \<tau>move2_\<tau>moves2.intros exec_instr simp add: exec_move_def)
    also from B bisim1_bsok[OF bisim2]
    have "P, try E catch(C' V) e2, V, h \<turnstile> (Val v, xs) \<leftrightarrow> ([v], xs, length (compE2 (try E catch(C' V) e2)), None)"
      by -(rule bisim1Val2, auto)
    ultimately show ?thesis using s \<tau> by(auto)
  next
    case (Red1TryCatch H a D fs CC VV XS E2)
    hence [simp]: "e = Throw a" "CC = C'" "VV = V" "E2 = e2" "H = h" "XS = xs" "ta = \<epsilon>" "e' = {V:Class C'=None; e2}\<^bsub>False\<^esub>"
      "h' = h" "xs' = xs[V := Addr a]" and ha: "h a = \<lfloor>Obj D fs\<rfloor>" and sub: "P \<turnstile> D \<preceq>\<^sup>* C'" and V: "V < length xs" by auto
    from bisim1 have [simp]: "xs = loc" and xcp: "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" 
      and B: "bsok E V" by(auto dest: bisim1_ThrowD bisim1_bsok)
    from xcp have "\<tau>Exec_move P (try E catch(C' V) e2) h (stk, loc, pc, xcp) ([Addr a], loc, Suc (length (compE2 E)), None)"
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 have "match_ex_table (compP2 P) (cname_of h a) pc (compxE2 E 0 0) = None"
	by(auto dest: bisim1_xcp_Some_not_caught[where pc'=0] simp add: compP2_def)
      moreover from bisim1 have "pc < length (compE2 E)"
	by(auto dest: bisim1_ThrowD)
      ultimately show ?thesis using ha sub unfolding `xcp = \<lfloor>a\<rfloor>`
	by-(rule \<tau>Exec1step[unfolded exec_move_def, OF exec_catch[where d=0, simplified]],
            auto intro: \<tau>move2_\<tau>moves2.intros simp add: matches_ex_entry_def compP2_def match_ex_table_append_not_pcs)
    next
      assume [simp]: "xcp = None"
      with bisim1 wtE obtain pc' where "\<tau>Exec_move P E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and s: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (try E catch(C' V) e2) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule Try_\<tau>Exec_meth_xt1)
      also from bisim' have "match_ex_table (compP2 P) (cname_of h a) pc' (compxE2 E 0 0) = None"
	by(auto dest: bisim1_xcp_Some_not_caught[where pc'=0] simp add: compP2_def)
      with ha sub bisim1_ThrowD[OF bisim']
      have "\<tau>Exec_move P (try E catch(C' V) e2) h ([Addr a], loc, pc', \<lfloor>a\<rfloor>) ([Addr a], loc, Suc (length (compE2 E)), None)"
	by-(rule \<tau>Exec1step[unfolded exec_move_def, OF exec_catch[where d=0, simplified]], auto intro: \<tau>move2_\<tau>moves2.intros simp add: matches_ex_entry_def compP2_def match_ex_table_append_not_pcs)
      finally show ?thesis by simp
    qed
    also let ?pc' = "Suc (length (compE2 E))" from V
    have exec: "\<tau>Exec_move P (try E catch(C' V) e2) h ([Addr a], loc, ?pc', None) ([], loc[V := Addr a], Suc ?pc', None)"
      by-(rule \<tau>Exec1step[unfolded exec_move_def, OF exec_instr], auto simp add: nth_append intro: \<tau>move2_\<tau>moves2.intros)
    also from bisim1_bsok[OF bisim2] B
    have bisim': "P,try E catch(C' V) e2, V, h \<turnstile> ({V:Class C'=None; e2}\<^bsub>False\<^esub>, xs[V := Addr a]) \<leftrightarrow> ([], loc[V := Addr a], Suc ?pc', None)"
      unfolding `xs = loc` by-(rule bisim1TryCatch2[OF bisim1_refl, simplified], auto)
    moreover have "\<tau>move1 (try Throw a catch(C' V) e2)" by(rule \<tau>move1TryCatch)
    ultimately show ?thesis by(auto)
  next
    case (Red1TryFail s a D fs CC VV E2)
    hence [simp]: "e = Throw a" "CC = C'" "VV = V" "E2 = e2" "s = (h, xs)" "ta = \<epsilon>" "e' = Throw a" "h' = h" "xs' = xs"
      and ha: "h a = \<lfloor>Obj D fs\<rfloor>" and sub: "\<not> P \<turnstile> D \<preceq>\<^sup>* C'" by auto
    have \<tau>: "\<tau>move1 (try Throw a catch(C' V) e2)" by(rule \<tau>move1TryFail)
    from bisim1 have [simp]:  "xs = loc" and "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    from bisim1 have pc: "pc \<le> length (compE2 E)" by(rule bisim1_pc_length_compE2)
    from `xcp = \<lfloor>a\<rfloor> \<or> xcp = None` show ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 ha sub bisim1_bsok[OF bisim2]
      have "P,try E catch(C' V) e2,V,hp s \<turnstile> (Throw a, lcl s) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1TryFail)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim1 wtE obtain pc' 
	where "\<tau>Exec_move P E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (try E catch(C' V) e2) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule Try_\<tau>Exec_meth_xt1)
      moreover from bisim' ha sub bisim1_bsok[OF bisim2]
      have "P,try E catch(C' V) e2,V,h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1TryFail)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case (bisim1TryCatch1 e V a xs stk loc pc D fs C' e2)
  note bisim1 = `P,e,V,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note IH2 = `\<And>xs e' h' xs' Env T Env' T'. \<lbrakk>P \<turnstile>1 \<langle>e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e2 :: T; P,Env',h \<turnstile>1 e2 : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,Suc V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta e2 e2 h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note ha = `h a = \<lfloor>Obj D fs\<rfloor>`
  note sub = `P \<turnstile> D \<preceq>\<^sup>* C'`
  note red = `P \<turnstile>1 \<langle>{V:Class C'=None; e2}\<^bsub>False\<^esub>,(h, xs[V := Addr a])\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 try e catch(C' V) e2 :: T` obtain T2 where wt2: "P,Env@[Class C'] \<turnstile>1 e2 :: T2" by auto
  from `P,Env',h \<turnstile>1 {V:Class C'=None; e2}\<^bsub>False\<^esub> : T'` obtain T2' where wt2': "P,Env'@[Class C'],h \<turnstile>1 e2 : T2'" by auto
  from bisim1 have [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
  from red show ?case
  proof cases
    case (Block1RedNone E H XS TA E' H' XS' VV Ty cr)
    hence [simp]: "VV = V" "Ty = Class C'" "E = e2" "H = h" "XS = xs[V := Addr a]" "TA = ta" "e' = {V:Class C'=None; E'}\<^bsub>False\<^esub>"
      "H' = h'" "XS' = xs'" "cr = False" 
      and red: "P \<turnstile>1 \<langle>e2, (h, xs[V := Addr a])\<rangle> -ta\<rightarrow> \<langle>E', (h', xs')\<rangle>" and V: "V < length xs" by auto
    from red have \<tau>: "\<tau>move1 {V:Class C'=None; e2}\<^bsub>False\<^esub> = \<tau>move1 e2" by(auto intro: \<tau>move1Block)
    from V have exec: "\<tau>Exec_move P (try e catch(C' V) e2) h ([Addr a], xs, Suc (length (compE2 e) + 0), None) ([], xs[V := Addr a], Suc (Suc (length (compE2 e) + 0)), None)"
      by -(rule \<tau>Exec1step, auto simp add: exec_move_def intro: exec_instr \<tau>move2_\<tau>moves2.intros)
    moreover from IH2[OF red wt2 wt2'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e2,Suc V,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e2 e2 h [] (xs[V := Addr a]) 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (try e catch(C' V) e2) {V:Class C'=None; e2}\<^bsub>False\<^esub> h [] (xs[V := Addr a]) (Suc (Suc (length (compE2 e))))  None h' (Suc (Suc (length (compE2 e) + pc''))) stk'' loc'' xcp''"
    proof(cases "\<tau>move1 {V:Class C'=None; e2}\<^bsub>False\<^esub>")
      case True with \<tau> exec' show ?thesis by(auto dest: Try_\<tau>Exec_meth_xt2)
    next
      case False
      with \<tau> exec' obtain ta' pc' stk' loc' xcp'
	where e: "\<tau>Exec_move P e2 h ([], xs[V := Addr a], 0, None) (stk', loc', pc', xcp')"
	and e': "exec_move P e2 h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 e2 pc' xcp'" and ta': "ta_bisim (wbisim1 P) ta ta'" by auto
      from e' have "exec_move P (try e catch(C' V) e2) h (stk', loc', Suc (Suc (length (compE2 e) + pc')), xcp') ta' h' (stk'', loc'', Suc (Suc (length (compE2 e) + pc'')), xcp'')"
	by(rule exec_move_TryI2)
      moreover from \<tau>' have "\<tau>move2 (try e catch(C' V) e2) (Suc (Suc (length (compE2 e) + pc'))) xcp' \<Longrightarrow> False"
	by -(erule \<tau>move2.cases,auto intro: \<tau>move2xcp dest: \<tau>move2_pc_length_compE2)
      ultimately show ?thesis using \<tau> False e ta'
	by(auto simp add: shift_compxE2 simp del: split_paired_Ex intro!: exI)(fastsimp dest: Try_\<tau>Exec_meth_xt2)
    qed
    moreover from bisim' bisim1_bsok[OF bisim1]
    have "P, try e catch(C' V) e2, V, h' \<turnstile> ({V:Class C'=None; E'}\<^bsub>False\<^esub>, xs') \<leftrightarrow> (stk'', loc'', Suc (Suc (length (compE2 e) + pc'')), xcp'')"
      by-(rule bisim1TryCatch2, auto)
    ultimately show ?thesis using \<tau> by(fastsimp simp add: shift_compxE2 elim!: \<tau>Exec_move_trans intro: \<tau>Exec_refl)
  next
    case (Red1BlockNone VV s Ty u)
    hence [simp]: "VV = V" "Ty = Class C'" "e2 = Val u" "s = (h, xs[V := Addr a])" "ta = \<epsilon>" "e' = Val u"
      "h' = h" "xs' = xs[V := Addr a]" and V: "V < length xs" by auto
    from V have "\<tau>Exec_move P (try e catch(C' V) Val u) h ([Addr a], xs, Suc (length (compE2 e) + 0), None) ([], xs[V := Addr a], Suc (Suc (length (compE2 e) + 0)), None)"
      by -(rule \<tau>Exec1step, auto simp add: exec_move_def intro: exec_instr \<tau>move2_\<tau>moves2.intros)
    also from wt2 have "\<tau>Exec_move P (try e catch(C' V) Val u) h ([], xs[V := Addr a], Suc (Suc (length (compE2 e) + 0)), None) ([u], xs[V := Addr a], Suc (Suc (length (compE2 e) + 1)), None)"
      by -(rule Try_\<tau>Exec_meth_xt2[OF \<tau>Exec1step[unfolded exec_move_def, OF exec_instr]], auto intro: \<tau>move2_\<tau>moves2.intros)
    also from bisim1_bsok[OF bisim1]
    have "P, try e catch(C' V) Val u, V, h \<turnstile> (Val u, xs[V := Addr a]) \<leftrightarrow> ([u], xs[V := Addr a], length (compE2 (try e catch(C' V) Val u)), None)"
      by-(rule bisim1Val2, auto)
    moreover have "\<tau>move1 {V:Class C'=None; Val u}\<^bsub>False\<^esub>" by(rule \<tau>move1BlockRed)
    ultimately show ?thesis by(auto)
  next
    case (Block1ThrowNone VV s TT a')
    with wt2 have False by auto
    thus ?thesis ..
  qed auto
next
  case (bisim1TryCatch2 e2 V e2' xs stk loc pc xcp e C')
  note bisim2 = `P,e2,Suc V,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim1 = `\<And>xs. P,e,V,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  note IH2 = `\<And>e' h' xs' Env T Env' T'. \<lbrakk>P \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 e2 :: T; P,Env',h \<turnstile>1 e2' : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,Suc V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta e2 e2' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note red = `P \<turnstile>1 \<langle>{V:Class C'=None; e2'}\<^bsub>False\<^esub>,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from `P,Env \<turnstile>1 try e catch(C' V) e2 :: T` obtain T2 where wt2: "P,Env@[Class C'] \<turnstile>1 e2 :: T2" by auto
  from `P,Env',h \<turnstile>1 {V:Class C'=None; e2'}\<^bsub>False\<^esub> : T'` obtain T2' where wt2': "P,Env'@[Class C'],h \<turnstile>1 e2' : T2'" by auto
  from red show ?case
  proof cases
    case (Block1RedNone E H XS TA E' H' XS' VV Ty cr)
    hence [simp]: "VV = V" "Ty = Class C'" "E = e2'" "H = h" "XS = xs" "TA = ta" "e' = {V:Class C'=None; E'}\<^bsub>False\<^esub>"
      "H' = h'" "XS' = xs'" "cr = False" and red: "P \<turnstile>1 \<langle>e2', (h, xs)\<rangle> -ta\<rightarrow> \<langle>E', (h', xs')\<rangle>" and V: "V < length xs" by auto
    from red have \<tau>: "\<tau>move1 {V:Class C'=None; e2'}\<^bsub>False\<^esub> = \<tau>move1 e2'" by(auto intro: \<tau>move1Block)
    from IH2[OF red wt2 wt2'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e2,Suc V,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e2 e2' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (try e catch(C' V) e2) {V:Class C'=None; e2'}\<^bsub>False\<^esub> h stk loc (Suc (Suc (length (compE2 e) + pc))) xcp h' (Suc (Suc (length (compE2 e) + pc''))) stk'' loc'' xcp''"
    proof (cases "\<tau>move1 {V:Class C'=None; e2'}\<^bsub>False\<^esub>")
      case True with \<tau> exec' show ?thesis by(auto intro: Try_\<tau>Exec_meth_xt2)
    next
      case False
      with \<tau> exec' obtain ta' pc' stk' loc' xcp'
	where e: "\<tau>Exec_move P e2 h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
	and e': "exec_move P e2 h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 e2 pc' xcp'" and ta': "ta_bisim (wbisim1 P) ta ta'" by auto
      from e' have "exec_move P (try e catch(C' V) e2) h (stk', loc', Suc (Suc (length (compE2 e) + pc')), xcp') ta' h' (stk'', loc'', Suc (Suc (length (compE2 e) +  pc'')), xcp'')"
	by(rule exec_move_TryI2)
      moreover from \<tau>' have "\<tau>move2 (try e catch(C' V) e2) (Suc (Suc (length (compE2 e) + pc'))) xcp' \<Longrightarrow> False"
	by -(erule \<tau>move2.cases,auto intro: \<tau>move2xcp dest: \<tau>move2_pc_length_compE2)
      ultimately show ?thesis using \<tau> False e ta'
	by(auto simp add: shift_compxE2 simp del: split_paired_Ex intro!: exI)(fastsimp dest: Try_\<tau>Exec_meth_xt2)
    qed
    moreover from bisim' bisim1_bsok[OF bisim1]
    have "P, try e catch(C' V) e2, V, h' \<turnstile> ({V:Class C'=None; E'}\<^bsub>False\<^esub>, xs') \<leftrightarrow> (stk'', loc'', Suc (Suc (length (compE2 e) + pc'')), xcp'')"
      by -(rule bisim1_bisims1.bisim1TryCatch2, auto)
    ultimately show ?thesis using \<tau> by(fastsimp simp add: shift_compxE2 elim!: \<tau>Exec_move_trans intro: \<tau>Exec_refl)
  next
    case (Red1BlockNone VV s Ty u)
    hence [simp]: "VV = V" "Ty = Class C'" "e2' = Val u" "s = (h, xs)" "ta = \<epsilon>" "e' = Val u"
      "h' = h" "xs' = xs" and V: "V < length xs" by auto
    from bisim2 wt2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_move P e2 h (stk, loc, pc, xcp) ([u], loc, length (compE2 e2), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_move P (try e catch(C' V) e2) h (stk, loc, Suc (Suc (length (compE2 e) + pc)), xcp) ([u], loc, Suc (Suc (length (compE2 e) + length (compE2 e2))), None)"
      by -(rule Try_\<tau>Exec_meth_xt2)
    moreover from `bsok e V` `bsok e2 (Suc V)`
    have "P, try e catch(C' V) e2, V, h \<turnstile> (Val u, xs) \<leftrightarrow> ([u], xs, length (compE2 (try e catch(C' V) e2)), None)"
      by-(rule bisim1Val2, auto)
    moreover have "\<tau>move1 {V:Class C'=None; Val u}\<^bsub>False\<^esub>" by(rule \<tau>move1BlockRed)
    ultimately show ?thesis using s by auto
  next
    case (Block1ThrowNone VV s TT a cr)
    hence [simp]: "VV = V" "TT = Class C'" "e2' = Throw a" "s = (h, xs)" "ta = \<epsilon>"
      "e' = Throw a" "h' = h" "xs' = xs" "cr = False"
      and V: "V < length xs" by auto
    have \<tau>: "\<tau>move1 {V:Class C'=None; e2'}\<^bsub>False\<^esub>" by(auto intro: \<tau>move1BlockThrow)
    from bisim2 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim2 bisim1_bsok[OF bisim1]
      have "P, try e catch(C' V) e2, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (Suc (length (compE2 e) + pc)), xcp)"
	by(auto intro: bisim1TryCatchThrow)
      thus ?thesis using \<tau> by(fastsimp intro: \<tau>Exec_refl)
    next
      assume [simp]: "xcp = None"
      with bisim2 wt2 obtain pc' 
	where "\<tau>Exec_move P e2 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, e2, Suc V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_move)
      hence "\<tau>Exec_move P (try e catch(C' V) e2) h (stk, loc, Suc (Suc (length (compE2 e) + pc)), None) ([Addr a], loc, Suc (Suc (length (compE2 e) + pc')), \<lfloor>a\<rfloor>)"
	by-(rule Try_\<tau>Exec_meth_xt2)
      moreover from bisim' bisim1_bsok[OF bisim1]
      have "P, try e catch(C' V) e2, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, Suc (Suc (length (compE2 e) + pc')), \<lfloor>a\<rfloor>)"
	by-(rule bisim1TryCatchThrow, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case bisim1TryFail thus ?case by auto
next
  case bisim1TryCatchThrow thus ?case by auto
next
  case bisims1Nil thus ?case by(auto elim!: reds1.cases)
next
  case (bisims1List1 E n e xs stk loc pc xcp es)
  note IH1 = `\<And>e' h' xs' Env T Env' T'. \<lbrakk>P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>; P,Env \<turnstile>1 E :: T; P,Env',h \<turnstile>1 e : T'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta E e h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note IH2 = `\<And>xs es' h' xs' Env Ts Env' Ts'. \<lbrakk> P \<turnstile>1 \<langle>es,(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es',(h', xs')\<rangle>; P,Env \<turnstile>1 es [::] Ts; P,Env',h \<turnstile>1 es [:] Ts'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,es,n,h' \<turnstile> (es', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'') \<and>
                 ?execs ta es es h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,es,n,h \<turnstile> (es, xs) [\<leftrightarrow>] ([], xs, 0, None)`
  from `P,Env \<turnstile>1 E # es [::] Ts` obtain T Tes where wtE: "P,Env \<turnstile>1 E :: T" and wtes: "P,Env \<turnstile>1 es [::] Tes"
    and Ts: "Ts = T # Tes" by auto
  from `P,Env',h \<turnstile>1 e # es [:] Ts'` obtain T' Tes' where wtE': "P,Env',h \<turnstile>1 e : T'"
    and wtes': "P,Env',h \<turnstile>1 es [:] Tes'" and Ts': "Ts' = T' # Tes'" by auto
  from `P \<turnstile>1 \<langle>e # es,(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es',(h', xs')\<rangle>` show ?case
  proof cases
    case (List1Red1 EE s TA E' s' ES)
    hence [simp]: "EE = e" "ES = es" "s = (h, xs)" "TA = ta" "es' = E' # es" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>" by auto
    from red have \<tau>: "\<tau>moves1 (e # es) = \<tau>move1 e" by(auto intro: \<tau>moves1Hd)
    with IH1[OF red wtE wtE'] bisims1_bsoks[OF bisim2] show ?thesis
      by(fastsimp intro: \<tau>Exec_move_\<tau>Exec_moves bisim1_bisims1.bisims1List1 elim: \<tau>moves2.cases simp add: exec_move_def exec_moves_def)
  next
    case (List1Red2 ES s TA ES' s' v)
    hence [simp]: "e = Val v" "ES = es" "s = (h, xs)" "TA = ta" "es' = Val v # ES'" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>es,(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>ES',(h', xs')\<rangle>" by auto
    from bisim1 wtE have s: "xs = loc" "xcp = None"
      and "\<tau>Exec_move P E h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_moves P (E # es) h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      by -(rule \<tau>Exec_move_\<tau>Exec_moves)
    moreover from IH2[OF red wtes wtes'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,es,n,h' \<turnstile> (ES', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'')"
      and exec': "?execs ta es es h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have \<tau>: "\<tau>moves1 (Val v # es) = \<tau>moves1 es" by(auto intro: \<tau>moves1Tl)
    have "?execs ta (E # es) (Val v # es) h [v] xs (length (compE2 E)) None h' (length (compE2 E) +  pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>moves1 (Val v # es)")
      case True with \<tau> exec' show ?thesis
	using append_\<tau>Exec_moves[where es' = "[E]" and stk = "[]" and vs ="[v]"] by fastsimp
    next
      case False with \<tau> exec' obtain ta' pc' stk' loc' xcp'
	where e: "\<tau>Exec_moves P es h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_moves P es h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>moves2 es pc' xcp'" and ta': "ta_bisim (wbisim1 P) ta ta'" by auto
      from append_\<tau>Exec_moves[OF _ e, where vs="[v]" and es' = "[E]"]
      have "\<tau>Exec_moves P (E # es) h ([v], xs, length (compE2 E), None) (stk' @ [v], loc', length (compE2 E) + pc', xcp')" by simp
      moreover from append_exec_moves[OF _ e', of "[v]" "[E]"]
      have "exec_moves P (E # es) h (stk' @ [v], loc', length (compE2 E) + pc', xcp') ta' h' (stk'' @ [v], loc'', length (compE2 E) + pc'', xcp'')"
	by simp
      moreover from \<tau>' have "\<tau>moves2 (E # es) (length (compE2 E) + pc') xcp' \<Longrightarrow> False"
	by(auto elim: \<tau>moves2.cases dest: \<tau>move2_pc_length_compE2)
      ultimately show ?thesis using False s ta' by(fastsimp simp del: split_paired_Ex)
    qed
    moreover from bisim' bisim1_bsok[OF bisim1]
    have "P,E # es,n,h' \<turnstile> (Val v # ES', xs') [\<leftrightarrow>] (stk'' @ [v], loc'', length (compE2 E) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisims1List2)
    ultimately show ?thesis using \<tau> s by(fastsimp elim!: \<tau>Exec_moves_trans intro: \<tau>Execs_refl)
  qed
next
  case (bisims1List2 ES n es xs stk loc pc xcp e v)
  note IH2 = `\<And>es' h' xs' Env Ts Env' Ts'. \<lbrakk>P \<turnstile>1 \<langle>es,(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es',(h', xs')\<rangle>; P,Env \<turnstile>1 ES [::] Ts; P,Env',h \<turnstile>1 es [:] Ts'\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,ES,n,h' \<turnstile> (es', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'') \<and>
                  ?execs ta ES es h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,ES,n,h \<turnstile> (es, xs) [\<leftrightarrow>] (stk, loc, pc, xcp)`
  from `P,Env \<turnstile>1 e # ES [::] Ts` obtain Tes where wtes: "P,Env \<turnstile>1 ES [::] Tes" by auto
  from `P,Env',h \<turnstile>1 Val v # es [:] Ts'` obtain Tes' where wtes': "P,Env',h \<turnstile>1 es [:] Tes'" by auto
  from `P \<turnstile>1 \<langle>Val v # es,(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es',(h', xs')\<rangle>` show ?case
  proof cases
    case (List1Red2 EES s TA ES' s' vv)
    hence [simp]: "vv = v" "EES = es" "s = (h, xs)" "TA = ta" "es' = Val v # ES'" "s' = (h', xs')"
      and red: "P \<turnstile>1 \<langle>es,(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>ES',(h', xs')\<rangle>" by auto
    from IH2[OF red wtes wtes'] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,ES,n,h' \<turnstile> (ES', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'')"
      and exec': "?execs ta ES es h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have \<tau>: "\<tau>moves1 (Val v # es) = \<tau>moves1 es" by(auto intro: \<tau>moves1Tl)
    have "?execs ta (e # ES) (Val v # es) h (stk @ [v]) loc (length (compE2 e) + pc) xcp h' (length (compE2 e) +  pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>moves1 (Val v # es)")
      case True with \<tau> exec' show ?thesis
	using append_\<tau>Exec_moves[where es' = "[e]" and stk = "stk" and vs ="[v]"] by auto
    next
      case False with \<tau> exec' obtain ta' pc' stk' loc' xcp'
	where e: "\<tau>Exec_moves P ES h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
	and e': "exec_moves P ES h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>moves2 ES pc' xcp'" and ta': "ta_bisim (wbisim1 P) ta ta'" by auto
      from append_\<tau>Exec_moves[OF _ e, where vs="[v]" and es' = "[e]"]
      have "\<tau>Exec_moves P (e # ES) h (stk @ [v], loc, length (compE2 e) + pc, xcp) (stk' @ [v], loc', length (compE2 e) + pc', xcp')" by simp
      moreover from append_exec_moves[OF _ e', of "[v]" "[e]"]
      have "exec_moves P (e # ES) h (stk' @ [v], loc', length (compE2 e) + pc', xcp') ta' h' (stk'' @ [v], loc'', length (compE2 e) + pc'', xcp'')" by simp
      moreover from \<tau>' have "\<tau>moves2 (e # ES) (length (compE2 e) + pc') xcp' \<Longrightarrow> False"
	by(auto elim: \<tau>moves2.cases dest: \<tau>move2_pc_length_compE2)
      ultimately show ?thesis using False ta' by(fastsimp simp add: shift_compxEs2 simp del: split_paired_Ex)
    qed
    moreover from bisim' bisim1_bsok[OF bisim1]
    have "P,e # ES,n,h' \<turnstile> (Val v # ES', xs') [\<leftrightarrow>] (stk'' @ [v], loc'', length (compE2 e) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisims1List2)
    ultimately show ?thesis using \<tau> by(fastsimp elim!: \<tau>Exec_moves_trans intro: \<tau>Execs_refl)
  qed auto
qed


lemma exec_1_simulates_Red1_\<tau>:
  assumes wf: "wf_J1_prog P"
  and Red1: "P \<turnstile>1 \<langle>(e, xs)/exs, h\<rangle> -ta\<rightarrow> \<langle>(e', xs')/exs', h\<rangle>"
  and bisim: "bisim1_list1 P h (e, xs) exs xcp frs"
  and \<tau>: "\<tau>Move1 ((e, xs), exs)"
  shows "\<exists>xcp' frs'. \<tau>Exec_1 P (xcp, h, frs) (xcp', h, frs') \<and> bisim1_list1 P h (e',xs') exs' xcp' frs'"
using Red1
proof(cases)
  case (red1Red E H X TA E' H' X' EXS)
  hence [simp]: "E = e" "X = xs" "EXS = exs" "H = h" "ta = TA"
    "exs' = exs" "H' = h" "E' = e'" "X' =xs'" by auto
  from `P \<turnstile>1 \<langle>E,(H, X)\<rangle> -TA\<rightarrow> \<langle>E',(H', X')\<rangle>`
  have red: "P \<turnstile>1 \<langle>e, (h, xs)\<rangle> -TA\<rightarrow> \<langle>e', (h, xs')\<rangle>" by simp
  from \<tau> red have \<tau>': "\<tau>move1 e" by(auto elim: red1_cases)
  from bisim show ?thesis
  proof(cases)
    case (bl1_Normal C M Ts EXS frs' T body D EX' stk loc pc XCP)
    hence [simp]: "EX' = (e, xs)" "EXS = exs" "frs = (stk, loc, C, M, pc) # frs'" "XCP = xcp"
      and bl: "bisim1_list P h C M (length Ts) exs frs'" 
      and b: "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
      and exsconf: "exsconf P h T (e, xs)" by simp_all
    note sees = `P \<turnstile> C sees M: Ts\<rightarrow>T = body in D` note hconf = `P \<turnstile> h \<surd>`

    from wf sees obtain Tb where wtbody: "P,[Class D] @ Ts \<turnstile>1 body :: Tb" and Ts_type: "set Ts \<subseteq> is_type P"
      by(fastsimp dest!: sees_wf_mdecl simp add: wf_mdecl_def mem_def dest: bspec)
    from blocks1_WT[OF this] have wtblocks: "P,[Class D] \<turnstile>1 blocks1 (length [Class D]) Ts body :: Tb" .

    from red b \<tau>' exsconf hconf wtblocks obtain pc' stk' loc' xcp'
      where exec: "\<tau>Exec_move P body h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
      and b': "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (e', xs') \<leftrightarrow> (stk', loc', pc', xcp')"
      by(fastsimp dest!: exec_instr_simulates_red1[OF wf] elim!: exsconf.cases)
    from exsconf red have exsconf': "exsconf P h T (e', xs')"
      by(rule red1_preserves_exsconf[OF wf hconf])

    from exec sees have "\<tau>Exec_1 P (xcp, h, frs) (xcp', h, (stk', loc', C, M, pc') # frs')"
      by(auto intro: \<tau>Exec_move_\<tau>Exec_1)
    moreover from bl sees b' exsconf' hconf
    have "bisim1_list1 P h (e', xs') exs' xcp' ((stk', loc', C, M, pc') # frs')"
      unfolding `exs' = exs` by(rule bisim1_list1.bl1_Normal)
    ultimately show ?thesis by(auto)
  qed(insert red, auto elim: red1_cases)
next
  case (red1Call E a M' vs H C' fs' Ts' T' body' D' X EXS)
  with \<tau> `call E = \<lfloor>(a, M', vs)\<rfloor>` have False by(auto dest: \<tau>move1_not_call)
  thus ?thesis ..
next
  case (red1Return E aMvs E' X' X EXS H)
  with \<tau> have False by(auto elim!: final.cases elim: \<tau>move1.cases)
  thus ?thesis ..
qed

lemma exec_1_simulates_Red1_not_\<tau>:
  assumes wf: "wf_J1_prog P"
  and Red1: "P \<turnstile>1 \<langle>(e, xs)/exs, h\<rangle> -ta\<rightarrow> \<langle>(e', xs')/exs', h'\<rangle>"
  and bisim: "bisim1_list1 P h (e, xs) exs xcp frs"
  and \<tau>: "\<not> \<tau>Move1 ((e, xs), exs)"
  shows "\<exists>ta' xcp' frs'. \<tau>Exec_1 P (xcp, h, frs) (xcp', h, frs') \<and>
           (\<exists>xcp'' frs''. exec_1' (compP2 P) (xcp', h, frs') ta' (xcp'', h', frs'') \<and>
                          \<not> \<tau>Move2 P (xcp', h, frs') \<and> ta_bisim (wbisim1 P) ta ta' \<and>
                  bisim1_list1 P h' (e',xs') exs' xcp'' frs'')"
using Red1
proof(cases)
  case (red1Red E H X TA E' H' X' EXS)
  hence [simp]: "E = e" "X = xs" "EXS = exs" "H = h" "ta = TA"
    "exs' = exs" "H' = h'" "E' = e'" "X' =xs'" by auto
  from `P \<turnstile>1 \<langle>E,(H, X)\<rangle> -TA\<rightarrow> \<langle>E',(H', X')\<rangle>`
  have red: "P \<turnstile>1 \<langle>e, (h, xs)\<rangle> -TA\<rightarrow> \<langle>e', (h', xs')\<rangle>" by simp
  hence hext: "hext h h'" by(auto dest: red1_hext_incr)
  from \<tau> have \<tau>': "\<not> \<tau>move1 e" by(auto)
  from bisim show ?thesis
  proof(cases)
    case (bl1_Normal C M Ts EXS frs' T body D EX' stk loc pc XCP)
    hence [simp]: "EX' = (e, xs)" "EXS = exs" "XCP = xcp"
      and [simp]: "frs = (stk, loc, C, M, pc) # frs'"
      and bl: "bisim1_list P h C M (length Ts) exs frs'"
      and b: "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
      and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D"
      and exsconf: "exsconf P h T (e, xs)"
      and hconf: "P \<turnstile> h \<surd>" by auto
    from bl hext have bl': "bisim1_list P h' C M (length Ts) exs frs'"
      by(rule bisim1_list_hext_mono)
    from hconf red exsconf have hconf': "P \<turnstile> h' \<surd>"
      by(auto dest: red1_preserves_hconf elim!: exsconf.cases)
    from wf sees obtain Tb where wtbody: "P,[Class D] @ Ts \<turnstile>1 body :: Tb" and Ts_type: "set Ts \<subseteq> is_type P"
      by(fastsimp dest!: sees_wf_mdecl simp add: wf_mdecl_def mem_def dest: bspec)
    from blocks1_WT[OF this] have wtblocks: "P,[Class D] \<turnstile>1 blocks1 (Suc 0) Ts body :: Tb" by simp
    with exec_instr_simulates_red1[OF wf hconf b red this] \<tau>' exsconf
    obtain pc' stk' loc' xcp' ta' pc'' stk'' loc'' xcp''
      where exec1: "\<tau>Exec_move P body h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
      and exec2: "exec_move P body h (stk', loc', pc', xcp') ta' h' (stk'', loc'', pc'', xcp'')"
      and \<tau>2: "\<not> \<tau>move2 body pc' xcp'"
      and b': "P,blocks1 (Suc 0) Ts body,Suc 0, h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and ta': "ta_bisim (wbisim1 P) TA ta'"
      by(fastsimp elim!: exsconf.cases simp add: exec_move_def)
    from exec2 have pc'body: "pc' < length (compE2 body)" by(auto)
    from wf hconf exsconf red have exsconf': "exsconf P h' T (e', xs')" by(rule red1_preserves_exsconf)

    from exec1 sees have exec1': "\<tau>Exec_1 P (xcp, h, frs) (xcp', h, (stk', loc', C, M, pc') # frs')"
      by(auto intro: \<tau>Exec_move_\<tau>Exec_1)
    moreover { fix a
      assume [simp]: "xcp' = \<lfloor>a\<rfloor>"
      from exec2 sees_method_compP[OF sees, of compMb2] pc'body
      have "match_ex_table (compP2 P) (cname_of h a) pc' (ex_table_of (compP2 P) C M) \<noteq> None"
	by(auto simp add: exec_move_def compP2_def compMb2_def elim!: exec_meth.cases) }
    with \<tau>2 sees pc'body have \<tau>2': "\<not> \<tau>Move2 P (xcp', h, (stk', loc', C, M, pc') # frs')"
      by(simp add: compP2_def compMb2_def)
    moreover from exec2 sees
    have exec2': "exec_1' (compP2 P) (xcp', h, (stk', loc', C, M, pc') # frs') ta' (xcp'', h', (stk'', loc'', C, M, pc'') # frs')"
      by(rule exec_move_exec_1')
    moreover from bl' sees b' exsconf' hconf'
    have "bisim1_list1 P h' (e', xs') exs xcp'' ((stk'', loc'', C, M, pc'') # frs')"
      by(rule bisim1_list1.bl1_Normal)
    moreover from ta' have "ta_bisim (wbisim1 P) ta ta'" by simp
    ultimately show ?thesis by(force simp del: split_paired_Ex)
  next
    case (bl1_finalVal v XS)
    with red show ?thesis by auto
  next
    case (bl1_finalThrow a XS)
    with red show ?thesis by(auto elim: red1_cases)
  qed
next
  case (red1Call E a' M' vs' H C' fs' Ts' T' body' D' X EXS)
  hence [simp]: "E = e" "X = xs" "H = h" "ta = \<epsilon>" "h' = h" "EXS = exs" "exs' = clearInitBlock e xs # exs"
    and e': "e' = blocks1 (Suc 0) Ts' body'"
    and xs': "xs' = Addr a' # vs' @ replicate (max_vars body') arbitrary"
    and ha': "h a' = \<lfloor>Obj C' fs'\<rfloor>"
    and call: "call e = \<lfloor>(a', M', vs')\<rfloor>" by auto
  note sees' = `P \<turnstile> C' sees M': Ts'\<rightarrow>T' = body' in D'`
  note lenvs'Ts' = `length vs' = length Ts'`
  from ha' sees_method_decl_above[OF sees'] have conf: "P,h \<turnstile> Addr a' :\<le> Class D'" by(auto simp add: conf_def)
  from bisim show ?thesis
  proof(cases)
    case (bl1_Normal C M Ts EXS frs' T body D EX' stk loc pc XCP)
    hence [simp]: "EX' = (e, xs)" "EXS = exs" "XCP = xcp" "frs = (stk, loc, C, M, pc) # frs'"
      and bl: "bisim1_list P h C M (length Ts) exs frs'"
      and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D"
      and bisim: "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
      and exsconf: "exsconf P h T (e, xs)"
      and hconf: "P \<turnstile> h \<surd>" by(auto simp add: clearInitBlock_length)
    from call bisim have [simp]: "xcp = None" by(cases xcp, auto dest: bisim1_call_xcpNone)
    from bisim have b: "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, None)" by simp
    from wf sees obtain Tb where wtbody: "P,[Class D] @ Ts \<turnstile>1 body :: Tb" and Ts_type: "set Ts \<subseteq> is_type P"
      by(fastsimp dest!: sees_wf_mdecl simp add: wf_mdecl_def mem_def dest: bspec)
    from blocks1_WT[OF this] have wtblocks: "P,[Class D] \<turnstile>1 blocks1 (length [Class D]) Ts body :: Tb" .
    with bisim1_call_\<tau>Exec_move[OF b call] exsconf obtain pc' loc' stk'
      where exec: "\<tau>Exec_move P body h (stk, loc, pc, None) (rev vs' @ Addr a' # stk', loc', pc', None)"
      and pc': "pc' < length (compE2 body)" and ins: "compE2 body ! pc' = Invoke M' (length vs')"
      and bisim': "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> clearInitBlock e xs \<leftrightarrow> (rev vs' @ Addr a' # stk', loc', pc', None)"
      by(auto simp add: blocks1_max_vars clearInitBlock_length elim!: exsconf.cases)
    let ?f = "(rev vs' @ Addr a' # stk', loc', C, M, pc')"
    from exec sees
    have exec1: "\<tau>Exec_1 P (None, h, (stk, loc, C, M, pc) # frs') (None, h, ?f  # frs')"
      by(rule \<tau>Exec_move_\<tau>Exec_1)
    let ?f' = "([], Addr a' # vs' @ (replicate (max_vars body') arbitrary), D', M', 0)"
    from pc' ins sees sees' ha'
    have "(\<epsilon>, None, h, ?f' # ?f # frs') \<in> set (exec_instr (instrs_of (compP2 P) C M ! pc') (compP2 P) h (rev vs' @ Addr a' # stk') loc' C M pc' frs')"
      by(auto simp add: compP2_def compMb2_def nth_append split_beta dest: external_call_not_sees_method[OF wf])
    moreover from ha' exsconf have vs': "P,h \<turnstile> vs' [:\<le>] Ts'"
      by(auto elim!: exsconf.cases intro: call_WTrt_vs_conform[OF wf _ sees' _ call])
    from sees' have "compP2 P \<turnstile> C' has M'"
      by(fastsimp simp add: has_method_def compMb2_def compP2_def dest: sees_method_compP[where f=compMb2])
    with pc' ins sees ha' sees' vs'
    have "check_instr (instrs_of (compP2 P) C M ! pc') (compP2 P) h (rev vs' @ Addr a' # stk') loc' C M pc' frs'"
      by(clarsimp simp add: compP2_def compMb2_def is_Ref_def compP_confs)
    ultimately have exec2: "exec_1' (compP2 P) (None, h, ?f # frs') \<epsilon> (None, h, ?f' # ?f # frs')"
      using pc' sees by -(erule exec_1_Normal, simp add: compP2_def compMb2_def)
    from call have "call (fst (clearInitBlock e xs)) = \<lfloor>(a', M', vs')\<rfloor>" by simp
    with bl sees bisim'
    have "bisim1_list P h D' M' (length Ts') (clearInitBlock e xs # exs) (?f # frs')"
      using ha' sees' ins exsconf_clearInitBlock[OF exsconf]
      unfolding lenvs'Ts'[symmetric] by(rule bl1_Cons)
    moreover note sees_method_idemp[OF sees']
    moreover from sees' exsconf have "bsok body' (Suc 0 + length Ts')"
      by(auto dest!: sees_wf_mdecl[OF wf] simp add: wf_mdecl_def bsok_def intro: WT1_expr_locks WT1_noRetBlock elim!: exsconf.cases)
    hence "bsok (blocks1 (Suc 0) Ts' body') (Suc 0)" by(auto simp add: bsok_def)
    with e' xs' have "P,blocks1 (Suc 0) Ts' body',Suc 0,h \<turnstile> (e', xs') \<leftrightarrow> ([], Addr a' # vs' @ replicate (max_vars body') arbitrary, 0, None)"
      by simp(rule bisim1_refl)
    moreover from exsconf have "P,h \<turnstile> vs' [:\<le>] Ts'"
      by(auto intro: call_WTrt_vs_conform[where h=h, OF wf ha' sees' _ call] elim!: exsconf.cases)
    with lenvs'Ts'[symmetric] sees' conf have "exsconf P h T' (e', xs')" unfolding e' xs'
      by(rule exsconf_Call[OF wf]) simp
    ultimately have "bisim1_list1 P h (e', xs') (clearInitBlock e xs # exs) None (?f' # ?f # frs')"
      using hconf by(rule bisim1_list1.bl1_Normal)
    moreover have "\<not> \<tau>move2 body pc' None" using pc' ins by(auto intro: \<tau>move2_Invoke)
    with sees pc' ins have "\<not> \<tau>Move2 P (None, h, (rev vs' @ Addr a' # stk', loc', C, M, pc') # frs')"
      by(auto simp add: compP2_def compMb2_def)
    ultimately show ?thesis using exec2 exec1 sees
      by(fastsimp intro: \<tau>Exec_1_refl)
  next
    case bl1_finalVal 
    with call show ?thesis by simp
  next
    case bl1_finalThrow
    with call show ?thesis by simp
  qed
next
  case (red1Return E aMvs E' X' X EXS H)
  hence [simp]: "E' = e" "X' = xs" "exs = (E, X) # exs'" "H = h" "ta = \<epsilon>" "e' = inline_call E' (fst (clearInitBlock E X))"
    "xs' = snd (clearInitBlock E X)" "EXS = exs'" "h' = h" by auto
  obtain a' M' vs' where [simp]: "aMvs = (a', M', vs')" by(cases aMvs, auto)
  with `call E = \<lfloor>aMvs\<rfloor>` have call: "call E = \<lfloor>(a', M', vs')\<rfloor>" by simp
  from bisim have bisim: "bisim1_list1 P h (e, xs) ((E, X) # exs') xcp frs" by simp
  thus ?thesis
  proof cases
    case (bl1_Normal C M Ts EXS' frs' T body D EX' stk loc pc XCP)
    hence [simp]: "EX' = (e, xs)" "EXS' = (E, X) # exs'" "XCP = xcp" "frs = (stk, loc, C, M, pc) # frs'"
      and bl: "bisim1_list P h C M (length Ts) ((E, X) # exs') frs'"
      and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D"
      and b: "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)" 
      and exsconf: "exsconf P h T (e, xs)"
      and hconf: "P \<turnstile> h \<surd>" by auto
    from wf sees obtain Tb where wtbody: "P,[Class D] @ Ts \<turnstile>1 body :: Tb" and Ts_type: "set Ts \<subseteq> is_type P"
      by(fastsimp dest!: sees_wf_mdecl simp add: wf_mdecl_def mem_def dest: bspec)
    from blocks1_WT[OF this] have wtblocks: "P,[Class D] \<turnstile>1 blocks1 (length [Class D]) Ts body :: Tb" .

    show ?thesis
    proof(cases "exs' = []")
      case False
      with bl call obtain M'' Ts'' frs'' C'' T'' body'' D'' pc'' stk'' loc'' fs C' Ts''' T''' meth
	where len'': "length Ts = length vs'"
	and bl'': "bisim1_list P h C'' M'' (length Ts'') exs' frs''"
	and sees'': "P \<turnstile> C'' sees M'': Ts''\<rightarrow>T'' = body'' in D''"
	and bisim'': "P,blocks1 (Suc 0) Ts'' body'',Suc 0,h \<turnstile> (E, X) \<leftrightarrow> (rev vs' @ Addr a' # stk'', loc'', pc'', None)"
	and ins: "compE2 body'' ! pc'' = Invoke M' (length vs')"
	and ha: "h a' = \<lfloor>Obj C' fs\<rfloor>"
	and sees''': "P \<turnstile> C' sees M:Ts''' \<rightarrow> T''' = meth in C"
	and [simp]: "frs' = (rev vs' @ Addr a' # stk'',loc'',C'',M'',pc'') # frs''" "M' = M"
	and exsconf'': "exsconf P h T'' (E, X)"
	by(fastsimp elim: bisim1_list.cases)
      let ?ex' = "(inline_call E' (fst (clearInitBlock E X)), snd (clearInitBlock E X))"
      
      from `final E'`[simplified] show ?thesis
      proof(cases)
	fix v
	assume [simp]: "e = Val v"
	with b have [simp]: "xcp = None" by(auto dest: bisim_Val_loc_eq_xcp_None)
	
	note bl'' sees'' moreover from bisim'' call ins
	have "P,blocks1 (Suc 0) Ts'' body'',Suc 0,h \<turnstile> ?ex' \<leftrightarrow> (v # stk'',loc'',Suc pc'',None)"
	  by(auto intro: bisim1_inline_call_Val)
	moreover from exsconf sees_method_idemp[OF sees'''] sees have "P,h \<turnstile> v :\<le> T'''"
	  by(auto elim!: exsconf.cases simp add: conf_def dest: sees_method_fun)
	with call ha sees''' exsconf'' exsconf have "exsconf P h T'' ?ex'" unfolding `E' = e` `e = Val v`
	  by-(rule exsconf_inline_call_Val[OF wf], auto intro: exsconf_clearInitBlock)
	ultimately have "bisim1_list1 P h ?ex' exs' None ((v # stk'', loc'', C'', M'', Suc pc'') # frs'')"
	  using hconf by(rule bisim1_list1.bl1_Normal)
	moreover from bisim1Val2D1[OF b[simplified]] wtblocks 
	have "\<tau>Exec_move P body h (stk, loc, pc, None) ([v], loc, length (compE2 body), None)"
	  and [simp]: "xs = loc" by auto
	with sees have "\<tau>Exec_1 P (None, h, (stk, loc, C, M, pc) # frs') (None, h, ([v], loc, C, M, length (compE2 body)) # frs')"
	  by-(rule \<tau>Exec_move_\<tau>Exec_1)
	moreover from sees sees'' len'' exsconf
	have "exec_1' (compP2 P) (None, h, ([v], loc, C, M, length (compE2 body)) # frs') \<epsilon> (None, h, (v # stk'', loc'', C'', M'', Suc pc'') # frs'')"
	  by(fastsimp intro!: exec_1_Normal simp add: compP2_def compMb2_def has_method_def conf_def elim!: exsconf.cases dest: sees_method_compP[where f="compMb2"])
	moreover from sees have "\<not> \<tau>Move2 P (None, h, ([v], loc, C, M, length (compE2 body)) # frs')"
	  by(auto dest: \<tau>move2_pc_length_compE2)
	ultimately show ?thesis using \<tau>Exec_1_refl[of P "(None, h, (v # stk'', loc'', C'', M'', Suc pc'') # frs'')"]
	  by(fastsimp)
      next
	fix a
	assume [simp]: "e = Throw a"

	have "\<exists>stk' pc'. \<tau>Exec_move P body h (stk, loc, pc, xcp) (stk', loc, pc', \<lfloor>a\<rfloor>) \<and>
                         P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk', loc, pc', \<lfloor>a\<rfloor>)"
	proof(cases xcp)
	  case None[simp]
	  from wtblocks bisim1_Throw_\<tau>Exec_move[OF b[simplified]] obtain pc'
	    where exec: "\<tau>Exec_move P body h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	    and bisim': "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	    and [simp]: "xs = loc" by auto
	  thus ?thesis by fastsimp
	next
	  case (Some a')
	  with b have "a' = a" "xs = loc" by(auto dest: bisim1_ThrowD)
	  thus ?thesis using b Some by(auto intro: \<tau>Exec_refl)
	qed
	then obtain stk' pc' where exec: "\<tau>Exec_move P body h (stk, loc, pc, xcp) (stk', loc, pc', \<lfloor>a\<rfloor>)"
	  and bisim': "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk', loc, pc', \<lfloor>a\<rfloor>)" by blast

	let ?frs = "(rev vs' @ Addr a' # stk'', loc'', C'', M'', pc'') # frs''"
	let ?\<sigma>' = "(\<lfloor>a\<rfloor>, h, ?frs)"

	note bl'' sees'' moreover from bisim'' call
	have "pc'' < length (compE2 (blocks1 (Suc 0) Ts'' body''))" by(rule bisim1_call_pcD)
	with bisim1_inline_call_Throw[OF bisim'' call, of a] ins
	have "P,blocks1 (Suc 0) Ts'' body'',Suc 0,h \<turnstile> ?ex' \<leftrightarrow> (rev vs' @ Addr a' # stk'', loc'', pc'', \<lfloor>a\<rfloor>)" by simp
	moreover from exsconf have conf: "P,h \<turnstile> Addr a :\<le> Class Throwable" by(auto elim!: exsconf.cases simp add: conf_def)
	from exsconf'' have exsconfc: "exsconf P h T'' (clearInitBlock E X)" by(rule exsconf_clearInitBlock)
	hence "exsconf P h T'' ?ex'" using call ha sees''' conf unfolding `e = Throw a` `E' = e`
	  by -(rule exsconf_inline_call_Throw[OF wf], auto)
	ultimately have "bisim1_list1 P h ?ex' exs' \<lfloor>a\<rfloor> ?frs"
	  using hconf by(rule bisim1_list1.bl1_Normal)
	moreover from \<tau>Exec_move_\<tau>Exec_1[OF exec sees]
	have "\<tau>Exec_1 P (xcp, h, (stk, loc, C, M, pc) # frs') (\<lfloor>a\<rfloor>, h, (stk', loc, C, M, pc') # frs')" by simp
	moreover from bisim1_xcp_Some_not_caught[OF bisim', of compMb2 0 0] sees
	have match: "match_ex_table (compP2 P) (cname_of h a) pc' (ex_table_of (compP2 P) C M) = None"
	  by(simp add: compP2_def compMb2_def)
	hence xcp_step: "exception_step (compP2 P) (\<epsilon>, \<lfloor>a\<rfloor>, h, (stk', loc, C, M, pc') # frs') = (\<epsilon>, ?\<sigma>')" by simp
	hence "exec_1' (compP2 P) (\<lfloor>a\<rfloor>, h, (stk', loc, C, M, pc') # frs') \<epsilon> ?\<sigma>'"
	  by(auto intro: exec_1_Throw)
	moreover from match have "\<not> \<tau>Move2 P (\<lfloor>a\<rfloor>, h, (stk', loc, C, M, pc') # frs')" by simp
	ultimately show ?thesis by(fastsimp simp del: \<tau>Move2.simps split_paired_Ex)
      qed
    next
      case True[simp]
      with bl call have [simp]: "E = addr a'\<bullet>M(map Val vs')" "frs' = []"
	  and lenvs: "length vs' = length Ts" by(auto elim: bisim1_list.cases split: split_if_asm)
      
      from `final E'`[simplified] show ?thesis
      proof(cases)
	fix v
	assume [simp]: "e = Val v"
	with b have [simp]: "xcp = None" by(auto dest: bisim_Val_loc_eq_xcp_None)
	
	from bisim1Val2D1[OF b[simplified]] wtblocks 
	have "\<tau>Exec_move P body h (stk, loc, pc, None) ([v], loc, length (compE2 body), None)"
	  and [simp]: "xs = loc" by auto
	with sees have "\<tau>Exec_1 P (None, h, (stk, loc, C, M, pc) # frs') (None, h, ([v], loc, C, M, length (compE2 body)) # frs')"
	  by-(rule \<tau>Exec_move_\<tau>Exec_1)
	moreover from sees 
	have "exec_1' (compP2 P) (None, h, [([v], loc, C, M, length (compE2 body))]) \<epsilon> (None, h, [])"
	  by(auto intro!: exec_1_Normal simp add: compP2_def compMb2_def)
	moreover from sees have "\<not> \<tau>Move2 P (None, h, [([v], loc, C, M, length (compE2 body))])"
	  by(auto dest: \<tau>move2_pc_length_compE2)
	moreover from hconf have "bisim1_list1 P h (Val v, X) [] None []" by(rule bl1_finalVal)
	ultimately show ?thesis by fastsimp
      next
	fix a
	assume [simp]: "e = Throw a"

	have "\<exists>stk' pc'. \<tau>Exec_move P body h (stk, loc, pc, xcp) (stk', loc, pc', \<lfloor>a\<rfloor>) \<and>
                         P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk', loc, pc', \<lfloor>a\<rfloor>)"
	proof(cases xcp)
	  case None[simp]
	  from wtblocks bisim1_Throw_\<tau>Exec_move[OF b[simplified]] obtain pc'
	    where exec: "\<tau>Exec_move P body h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	    and bisim': "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	    and [simp]: "xs = loc" by auto
	  thus ?thesis by fastsimp
	next
	  case (Some a')
	  with b have "a' = a" "xs = loc" by(auto dest: bisim1_ThrowD)
	  thus ?thesis using b Some by(auto intro: \<tau>Exec_refl)
	qed
	then obtain stk' pc' where exec: "\<tau>Exec_move P body h (stk, loc, pc, xcp) (stk', loc, pc', \<lfloor>a\<rfloor>)"
	  and bisim': "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk', loc, pc', \<lfloor>a\<rfloor>)" by blast
	from exec sees have "\<tau>Exec_1 P (xcp, h, [(stk, loc, C, M, pc)]) (\<lfloor>a\<rfloor>, h, [(stk', loc, C, M, pc')])"
	  by(rule \<tau>Exec_move_\<tau>Exec_1)
	moreover from bisim1_xcp_Some_not_caught[OF bisim', of compMb2 0 0] sees
	have match: "match_ex_table (compP2 P) (cname_of h a) pc' (ex_table_of (compP2 P) C M) = None"
	  by(simp add: compP2_def compMb2_def)
	hence xcp_step: "exception_step (compP2 P) (\<epsilon>, \<lfloor>a\<rfloor>, h, (stk', loc, C, M, pc') # frs') = (\<epsilon>, \<lfloor>a\<rfloor>, h, [])" by simp
	hence "exec_1' (compP2 P) (\<lfloor>a\<rfloor>, h, (stk', loc, C, M, pc') # frs') \<epsilon> (\<lfloor>a\<rfloor>, h, [])"
	  by(auto intro: exec_1_Throw)
	moreover from match have "\<not> \<tau>Move2 P (\<lfloor>a\<rfloor>, h, [(stk', loc, C, M, pc')])" by simp
	moreover from hconf have "bisim1_list1 P h (Throw a, X) [] \<lfloor>a\<rfloor> []" by(rule bl1_finalThrow)
	ultimately show ?thesis by(fastsimp simp del: \<tau>Move2.simps)
      qed
    qed
  qed auto
qed

end