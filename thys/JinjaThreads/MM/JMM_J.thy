(*  Title:      JinjaThreads/MM/JMM_J.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{JMM instantiation with Jinja source code} *}

theory JMM_J imports
  "JMM_Common"
  "../J/ProgressThreaded"
  "../Compiler/J0"
begin

sublocale J_heap_base < red_mthr!: 
  if_\<tau>multithreaded_wf
    final_expr
    "mred P"
    convert_RA
    "\<tau>MOVE P"
    wfs
  for P wfs
by(unfold_locales)

sublocale J_heap_base < red_mthr_if!: jmm_\<tau>multithreaded
  "red_mthr.init_fin_final"
  "red_mthr.init_fin P"
  "map NormalAction \<circ> convert_RA"
  "red_mthr.init_fin_\<tau>move P"
.

section {* Locale @{text executions_aux} *}
  
context J_heap begin

lemma init_fin_hext: 
  assumes "red_mthr.init_fin P t (x, m) ta (x', m')"
  shows "m \<unlhd> m'"
using assms
by cases(auto dest: red_hext_incr)

lemma init_fin_redT_hext:
  assumes "red_mthr.if.redT P \<sigma> (t, ta) \<sigma>'"
  shows "shr \<sigma> \<unlhd> shr \<sigma>'"
using assms
by cases(auto dest: init_fin_hext)

lemma init_fin_silent_moves_hext:
  assumes "red_mthr.if.mthr.silent_moves P \<sigma> \<sigma>'"
  shows "shr \<sigma> \<unlhd> shr \<sigma>'"
using assms
by induct(auto dest!: init_fin_redT_hext elim: hext_trans)

lemma init_fin_\<tau>rtrancl3p_hext:
  assumes "red_mthr.if.mthr.\<tau>rtrancl3p P \<sigma> ttas \<sigma>'"
  shows "shr \<sigma> \<unlhd> shr \<sigma>'"
using assms
by induct(auto dest!: init_fin_redT_hext elim: hext_trans)

lemma red_New_typeof_addrD:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewHeapElem a x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr (hp s) a = None \<and> typeof_addr (hp s') a = Some (ty_of_htype x)"
  and reds_New_typeof_addrD:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewHeapElem a x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr (hp s) a = None \<and> typeof_addr (hp s') a = Some (ty_of_htype x)"
apply(induct rule: red_reds.inducts)
apply(auto dest: new_obj_SomeD new_arr_SomeD red_external_New_typeof_addrD)
done

lemma red_NewArr_lengthD:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewArr a T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> array_length (hp s') a = n"
  and reds_NewARr_lengthD:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewArr a T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> array_length (hp s') a = n"
apply(induct rule: red_reds.inducts)
apply(auto dest: new_arr_SomeD red_external_NewArr_lengthD)
done

lemma red_New_same_addr_same:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
  and reds_New_same_addr_same:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
apply(induct rule: red_reds.inducts)
apply(auto dest: red_external_New_same_addr_same)
done

lemma \<E>_new_actions_for_unique:
  assumes E: "E \<in> lappend init_obs ` red_mthr.if.\<E> P \<sigma>"
  and init_obs: "{a. (\<exists>CTn. NormalAction (NewHeapElem a CTn) \<in> snd ` lset init_obs)} \<subseteq> dom (typeof_addr (shr \<sigma>))"
  and distinct: "ldistinct (lfilter (\<lambda>obs. \<exists>a CTn. obs = NormalAction (NewHeapElem a CTn)) (lmap snd init_obs))"
  and inj: "\<And>a CTn CTn'. \<lbrakk> NormalAction (NewHeapElem a CTn) \<in> snd ` lset init_obs; NormalAction (NewHeapElem a CTn') \<in> snd ` lset init_obs \<rbrakk> \<Longrightarrow> CTn = CTn'"
  and a: "a \<in> new_actions_for P E adal"
  and a': "a' \<in> new_actions_for P E adal"
  shows "a = a'"
using a a'
proof(induct a a' rule: wlog_linorder_le)
  case symmetry thus ?case by simp
next
  case (le a a')
  note a = `a \<in> new_actions_for P E adal`
    and a' = `a' \<in> new_actions_for P E adal`
    and a_a' = `a \<le> a'`
  obtain ad al where adal: "adal = (ad, al)" by(cases adal)
  
  show ?case
  proof(cases "Fin a' < llength init_obs")
    case True
    with a' adal E obtain t_a' CTn_a'
      where CTn_a': "lnth init_obs a' = (t_a', NormalAction (NewHeapElem ad CTn_a'))"
      by(cases "lnth init_obs a'")(fastsimp elim!: is_new_action.cases action_loc_aux_cases simp add: action_obs_def lnth_lappend1 new_actions_for_def )+
    from True a_a' have len_a: "Fin a < llength init_obs"
      by(cases "llength init_obs") simp_all
    with a adal E obtain t_a CTn_a
      where CTn_a: "lnth init_obs a = (t_a, NormalAction (NewHeapElem ad CTn_a))"
      by(cases "lnth init_obs a")(fastsimp elim!: is_new_action.cases action_loc_aux_cases simp add: action_obs_def lnth_lappend1 new_actions_for_def )+
    from CTn_a CTn_a' True len_a
    have "NormalAction (NewHeapElem ad CTn_a') \<in> snd ` lset init_obs"
      and "NormalAction (NewHeapElem ad CTn_a) \<in> snd ` lset init_obs" unfolding lset_def
      by(fastsimp intro: rev_image_eqI)+
    hence [simp]: "CTn_a' = CTn_a" by(rule inj)
    from ldistinct_lfilterD[OF distinct, of a' a "NormalAction (NewHeapElem ad CTn_a)"]
      len_a True CTn_a CTn_a'
    show "a = a'" by simp
  next
    case False
    then obtain n where n: "llength init_obs = Fin n"
      by(cases "llength init_obs") auto
    with False have "n \<le> a'" by simp

    from E obtain E'' where E: "E = lappend init_obs E''"
      and E'': "E'' \<in> red_mthr.if.\<E> P \<sigma>" by auto
    from E'' obtain E' where E': "E'' = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
      and Runs: "red_mthr.if.mthr.Runs P \<sigma> E'"
      by(rule red_mthr.if.\<E>.cases)

    from E E'' a' n `n \<le> a'` adal have a': "a' - n \<in> new_actions_for P E'' adal"
      by(auto simp add: new_actions_for_def lnth_lappend2 action_obs_def actions_lappend elim: actionsE)

    from a' have "a' - n \<in> actions E''" by(auto elim: new_actionsE)
    hence "Fin (a' - n) < llength E''" by(rule actionsE)
    with Runs obtain a'_m a'_n t_a' ta_a'
      where E_a': "lnth E'' (a' - n) = (t_a', \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n)"
      and a'_n: "a'_n < length \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>" and a'_m: "Fin a'_m < tlength E'"
      and a'_conv: "a' - n = (\<Sum>i<a'_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + a'_n"
      and E'_a'_m: "tnth E' a'_m = (t_a', ta_a')"
      unfolding E' by(rule red_mthr.if.actions_\<E>E_aux)

    from a' have "is_new_action (action_obs E'' (a' - n))"
      and "(ad, al) \<in> action_loc P E'' (a' - n)"
      unfolding adal by(auto elim: new_actionsE)
    then obtain CTn'
      where "action_obs E'' (a' - n) = NormalAction (NewHeapElem ad CTn')"
      by cases(fastsimp)+
    hence New_ta_a': "\<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n = NormalAction (NewHeapElem ad CTn')"
      using E_a' a'_n unfolding action_obs_def by simp


    show ?thesis
    proof(cases "a < n")
      case True
      with a adal E n obtain t_a CTn_a where "lnth init_obs a = (t_a, NormalAction (NewHeapElem ad CTn_a))"
        by(cases "lnth init_obs a")(fastsimp elim!: is_new_action.cases simp add: action_obs_def lnth_lappend1 new_actions_for_def)+
      with subsetD[OF init_obs, of ad] n True
      have a_shr_\<sigma>: "ad \<in> dom (typeof_addr (shr \<sigma>))" by(fastsimp simp add: lset_def intro: rev_image_eqI)
      then obtain T where T: "typeof_addr (shr \<sigma>) ad = \<lfloor>T\<rfloor>" by auto
      
      have E'_unfold': "E' = lappendt (ltake (Fin a'_m) (llist_of_tllist E')) (TCons (tnth E' a'_m) (tdropn (Suc a'_m) E'))"
        unfolding tdropn_Suc_conv_tdropn[OF a'_m] lappendt_ltake_tdropn ..
      hence "red_mthr.if.mthr.Runs P \<sigma> (lappendt (ltake (Fin a'_m) (llist_of_tllist E')) (TCons (tnth E' a'_m) (tdropn (Suc a'_m) E')))"
        using Runs by simp
      then obtain \<sigma>'
        where \<sigma>_\<sigma>': "red_mthr.if.mthr.\<tau>rtrancl3p P \<sigma> (list_of (ltake (Fin a'_m) (llist_of_tllist E'))) \<sigma>'"
        and Runs': "red_mthr.if.mthr.Runs P \<sigma>' (TCons (tnth E' a'_m) (tdropn (Suc a'_m) E'))"
        by(rule red_mthr.if.mthr.Runs_lappendtE) simp
      from Runs' obtain \<sigma>'' \<sigma>'''
        where \<sigma>'_\<sigma>'': "red_mthr.if.mthr.silent_moves P \<sigma>' \<sigma>''"
        and red_a': "red_mthr.if.redT P \<sigma>'' (t_a', ta_a') \<sigma>'''"
        and "\<not> red_mthr.if.m\<tau>move P \<sigma>'' (t_a', ta_a') \<sigma>'''"
        and Runs'': "red_mthr.if.mthr.Runs P \<sigma>''' (tdropn (Suc a'_m) E')"
        unfolding E'_a'_m by cases
      from New_ta_a' a'_n have "NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>"
        unfolding in_set_conv_nth by blast
      with red_a' obtain x_a' x'_a' m'_a' 
        where red'_a': "red_mthr.init_fin P t_a' (x_a', shr \<sigma>'') ta_a' (x'_a', m'_a')"
        and \<sigma>''': "redT_upd \<sigma>'' t_a' ta_a' x'_a' m'_a' \<sigma>'''"
        and ts_t_a': "thr \<sigma>'' t_a' = \<lfloor>(x_a', no_wait_locks)\<rfloor>"
        by cases auto
      from red'_a' `NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>`
      obtain ta'_a' e_a' xs_a' e'_a' xs'_a'
        where x_a': "x_a' = (Running, (e_a', xs_a'))"
        and x'_a': "x'_a' = (Running, (e'_a', xs'_a'))"
        and ta_a': "ta_a' = convert_TA_initial (convert_obs_initial ta'_a')"
        and red''_a': "P,t_a' \<turnstile> \<langle>e_a', (shr \<sigma>'', xs_a')\<rangle> -ta'_a'\<rightarrow> \<langle>e'_a', (m'_a', xs'_a')\<rangle>"
        by cases fastsimp+
      from ta_a' New_ta_a' a'_n have New_ta'_a': "\<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n = NewHeapElem ad CTn'"
        and a'_n': "a'_n < length \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" by auto
      hence "NewHeapElem ad CTn' \<in> set \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" unfolding in_set_conv_nth by blast
      with red''_a' have typeof_ad': "typeof_addr (shr \<sigma>'') ad = None"
        by(auto dest: red_New_typeof_addrD)
    
      have "shr \<sigma> \<unlhd> shr \<sigma>'" using \<sigma>_\<sigma>' by(rule init_fin_\<tau>rtrancl3p_hext)
      also from \<sigma>'_\<sigma>'' have "shr \<sigma>' \<unlhd> shr \<sigma>''" by(rule init_fin_silent_moves_hext)
      finally have "typeof_addr (shr \<sigma>'') ad = \<lfloor>T\<rfloor>" using T by(auto dest: typeof_addr_hext_mono)
      with typeof_ad' have False by simp
      thus ?thesis ..
    next
      case False
      hence "n \<le> a" by simp

      from E E'' a n `n \<le> a` adal have a: "a - n \<in> new_actions_for P E'' adal"
        by(auto simp add: new_actions_for_def lnth_lappend2 action_obs_def actions_lappend elim: actionsE)

      from a have "a - n \<in> actions E''" by(auto elim: new_actionsE)
      hence "Fin (a - n) < llength E''" by(rule actionsE)


      with Runs obtain a_m a_n t_a ta_a 
        where E_a: "lnth E'' (a - n) = (t_a, \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub> ! a_n)"
        and a_n: "a_n < length \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>" and a_m: "Fin a_m < tlength E'"
        and a_conv: "a - n = (\<Sum>i<a_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + a_n"
        and E'_a_m: "tnth E' a_m = (t_a, ta_a)"
        unfolding E' by(rule red_mthr.if.actions_\<E>E_aux)
  
      from a have "is_new_action (action_obs E'' (a - n))" 
        and "(ad, al) \<in> action_loc P E'' (a - n)" 
        unfolding adal by(auto elim: new_actionsE)
      then obtain CTn where "action_obs E'' (a - n) = NormalAction (NewHeapElem ad CTn)"
        by cases(fastsimp)+
      hence New_ta_a: " \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub> ! a_n = NormalAction (NewHeapElem ad CTn)"
        using E_a a_n unfolding action_obs_def by simp
      
      let ?E' = "tdropn (Suc a_m) E'"
  
      have E'_unfold: "E' = lappendt (ltake (Fin a_m) (llist_of_tllist E')) (TCons (tnth E' a_m) ?E')"
        unfolding tdropn_Suc_conv_tdropn[OF a_m] lappendt_ltake_tdropn ..
      hence "red_mthr.if.mthr.Runs P \<sigma> (lappendt (ltake (Fin a_m) (llist_of_tllist E')) (TCons (tnth E' a_m) ?E'))"
        using Runs by simp
      then obtain \<sigma>' where \<sigma>_\<sigma>': "red_mthr.if.mthr.\<tau>rtrancl3p P \<sigma> (list_of (ltake (Fin a_m) (llist_of_tllist E'))) \<sigma>'"
        and Runs': "red_mthr.if.mthr.Runs P \<sigma>' (TCons (tnth E' a_m) ?E')"
        by(rule red_mthr.if.mthr.Runs_lappendtE) simp
      from Runs' obtain \<sigma>'' \<sigma>''' where "red_mthr.if.mthr.silent_moves P \<sigma>' \<sigma>''"
        and red_a: "red_mthr.if.redT P \<sigma>'' (t_a, ta_a) \<sigma>'''"
        and "\<not> red_mthr.if.m\<tau>move P \<sigma>'' (t_a, ta_a) \<sigma>'''"
        and Runs'': "red_mthr.if.mthr.Runs P \<sigma>''' ?E'"
        unfolding E'_a_m by cases
      from New_ta_a a_n have "NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>"
        unfolding in_set_conv_nth by blast
      with red_a obtain x_a x'_a m'_a 
        where red'_a: "red_mthr.init_fin P t_a (x_a, shr \<sigma>'') ta_a (x'_a, m'_a)"
        and \<sigma>''': "redT_upd \<sigma>'' t_a ta_a x'_a m'_a \<sigma>'''"
        and ts_t_a: "thr \<sigma>'' t_a = \<lfloor>(x_a, no_wait_locks)\<rfloor>"
        by cases auto
      from red'_a `NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>`
      obtain ta'_a e_a xs_a e'_a xs'_a
        where x_a: "x_a = (Running, (e_a, xs_a))"
        and x'_a: "x'_a = (Running, (e'_a, xs'_a))"
        and ta_a: "ta_a = convert_TA_initial (convert_obs_initial ta'_a)"
        and red''_a: "P,t_a \<turnstile> \<langle>e_a, (shr \<sigma>'', xs_a)\<rangle> -ta'_a\<rightarrow> \<langle>e'_a, (m'_a, xs'_a)\<rangle>"
        by cases fastsimp+
      from ta_a New_ta_a a_n have New_ta'_a: "\<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub> ! a_n = NewHeapElem ad CTn"
        and a_n': "a_n < length \<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub>" by auto
      hence "NewHeapElem ad CTn \<in> set \<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub>" unfolding in_set_conv_nth by blast
      with red''_a have typeof_m'_a_ad: "typeof_addr m'_a ad \<noteq> None"
        by(auto dest: red_New_typeof_addrD)
      
      have "a_m \<le> a'_m"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence "a'_m < a_m" by simp
        hence "(\<Sum>i<a_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) = (\<Sum>i<a'_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i = a'_m..<a_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
          by(simp add: setsum_upto_add_nat)
        hence "a' - n < a - n" using `a'_m < a_m` a'_n E'_a'_m unfolding a_conv a'_conv
          by(subst (asm) setsum_head_upt_Suc) simp_all
        with a_a' show False by simp
      qed
  
      have a'_less: "a' - n < (a - n) - a_n + length \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence a'_greater: "(a - n) - a_n + length \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub> \<le> a' - n" by simp
        
        have "a_m < a'_m"
        proof(rule ccontr)
          assume "\<not> ?thesis"
          with `a_m \<le> a'_m` have "a_m = a'_m" by simp
          with a'_greater a_n a'_n E'_a'_m E'_a_m show False
            unfolding a_conv a'_conv by simp
        qed
        hence a'_m_a_m: "Fin (a'_m - Suc a_m) < tlength ?E'" using a'_m
          by(cases "tlength E'") simp_all
        from `a_m < a'_m` a'_m E'_a'_m
        have E'_a'_m': "tnth ?E' (a'_m - Suc a_m) = (t_a', ta_a')" by simp
    
        have E'_unfold': "?E' = lappendt (ltake (Fin (a'_m - Suc a_m)) (llist_of_tllist ?E')) (TCons (tnth ?E' (a'_m - Suc a_m)) (tdropn (Suc (a'_m - Suc a_m)) ?E'))"
          unfolding tdropn_Suc_conv_tdropn[OF a'_m_a_m] lappendt_ltake_tdropn ..
        hence "red_mthr.if.mthr.Runs P \<sigma>''' (lappendt (ltake (Fin (a'_m - Suc a_m)) (llist_of_tllist ?E')) (TCons (tnth ?E' (a'_m - Suc a_m)) (tdropn (Suc (a'_m - Suc a_m)) ?E')))"
          using Runs'' by simp
        then obtain \<sigma>''''
          where \<sigma>'''_\<sigma>'''': "red_mthr.if.mthr.\<tau>rtrancl3p P \<sigma>''' (list_of (ltake (Fin (a'_m - Suc a_m)) (llist_of_tllist ?E'))) \<sigma>''''"
          and Runs''': "red_mthr.if.mthr.Runs P \<sigma>'''' (TCons (tnth ?E' (a'_m - Suc a_m)) (tdropn (Suc (a'_m - Suc a_m)) ?E'))"
          by(rule red_mthr.if.mthr.Runs_lappendtE) simp
        from Runs''' obtain \<sigma>''''' \<sigma>''''''
          where \<sigma>''''_\<sigma>''''': "red_mthr.if.mthr.silent_moves P \<sigma>'''' \<sigma>'''''"
          and red_a': "red_mthr.if.redT P \<sigma>''''' (t_a', ta_a') \<sigma>''''''"
          and "\<not> red_mthr.if.m\<tau>move P \<sigma>''''' (t_a', ta_a') \<sigma>''''''"
          and Runs''''': "red_mthr.if.mthr.Runs P \<sigma>'''''' (tdropn (Suc (a'_m - Suc a_m)) ?E')"
          unfolding E'_a'_m' by cases
        from New_ta_a' a'_n have "NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>"
          unfolding in_set_conv_nth by blast
        with red_a' obtain x_a' x'_a' m'_a' 
          where red'_a': "red_mthr.init_fin P t_a' (x_a', shr \<sigma>''''') ta_a' (x'_a', m'_a')"
          and \<sigma>'''''': "redT_upd \<sigma>''''' t_a' ta_a' x'_a' m'_a' \<sigma>''''''"
          and ts_t_a': "thr \<sigma>''''' t_a' = \<lfloor>(x_a', no_wait_locks)\<rfloor>"
          by cases auto
        from red'_a' `NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>`
        obtain ta'_a' e_a' xs_a' e'_a' xs'_a'
          where x_a': "x_a' = (Running, (e_a', xs_a'))"
          and x'_a': "x'_a' = (Running, (e'_a', xs'_a'))"
          and ta_a': "ta_a' = convert_TA_initial (convert_obs_initial ta'_a')"
          and red''_a': "P,t_a' \<turnstile> \<langle>e_a', (shr \<sigma>''''', xs_a')\<rangle> -ta'_a'\<rightarrow> \<langle>e'_a', (m'_a', xs'_a')\<rangle>"
          by cases fastsimp+
        from ta_a' New_ta_a' a'_n have New_ta'_a': "\<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n = NewHeapElem ad CTn'"
          and a'_n': "a'_n < length \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" by auto
        hence "NewHeapElem ad CTn' \<in> set \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" unfolding in_set_conv_nth by blast
        with red''_a' have typeof_ad': "typeof_addr (shr \<sigma>''''') ad = None"
          by(auto dest: red_New_typeof_addrD)
    
        have "m'_a = shr \<sigma>'''" using \<sigma>''' by auto
        also have "shr \<sigma>''' \<unlhd> shr \<sigma>''''" using \<sigma>'''_\<sigma>'''' by(rule init_fin_\<tau>rtrancl3p_hext)
        also from \<sigma>''''_\<sigma>''''' have "shr \<sigma>'''' \<unlhd> shr \<sigma>'''''" by(rule init_fin_silent_moves_hext)
        finally have "typeof_addr (shr \<sigma>''''') ad \<noteq> None" using typeof_m'_a_ad by(auto dest: typeof_addr_hext_mono)
        with typeof_ad' show False by contradiction
      qed
      
      from `a_m \<le> a'_m` have [simp]: "a_m = a'_m"
      proof(rule le_antisym)
        show "a'_m \<le> a_m"
        proof(rule ccontr)
          assume "\<not> ?thesis"
          hence "a_m < a'_m" by simp
          hence "(\<Sum>i<a'_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) = (\<Sum>i<a_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i = a_m..<a'_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
            by(simp add: setsum_upto_add_nat)
          with a'_less `a_m < a'_m` E'_a_m a_n a'_n show False
            unfolding a'_conv a_conv by(subst (asm) setsum_head_upt_Suc) simp_all
        qed
      qed
      with E'_a_m E'_a'_m have [simp]: "t_a' = t_a" "ta_a' = ta_a" by simp_all
      from New_ta_a' a'_n ta_a have a'_n': "a'_n < length \<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub>"
        and New_ta'_a': "\<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub> ! a'_n = NewHeapElem ad CTn'" by auto
      with red''_a New_ta'_a a_n' have "a'_n = a_n"
        by(auto dest: red_New_same_addr_same)
      with `a_m = a'_m` have "a - n = a' - n" unfolding a_conv a'_conv by simp
      thus ?thesis using `n \<le> a` `n \<le> a'` by simp
    qed
  qed
qed

lemma assumes wf: "wf_prog wf_md P"
  shows red_read_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,E,hp s \<turnstile> e : T; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>T'. P,hp s \<turnstile> ad@al : T'"
  and reds_read_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; P,E,hp s \<turnstile> es [:] Ts; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>T'. P,hp s \<turnstile> ad@al : T'"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case RedAAcc thus ?case
    by(fastsimp intro: addr_loc_type.intros simp add: nat_less_iff word_sle_def)
next
  case RedFAcc thus ?case
    by(fastsimp intro: addr_loc_type.intros dest: typeof_addr_eq_Some_conv)
next
  case RedCallExternal thus ?case
    by(auto intro: red_external_read_mem_typeable[OF wf])
qed auto

lemma assumes minimal: "heap_ops_typeof_minimal"
  shows red_create_object:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; typeof_addr (hp s') a = \<lfloor>T\<rfloor>; typeof_addr (hp s) a = None \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> ty_of_htype CTn = T \<and> hp s' \<turnstile>a a : CTn"
  and reds_create_object:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; typeof_addr (hp s') a = \<lfloor>T\<rfloor>; typeof_addr (hp s) a = None \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem a CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> ty_of_htype CTn = T \<and> hp s' \<turnstile>a a : CTn"
proof(induct rule: red_reds.inducts)
  case RedNewArray thus ?case
    apply -
    apply(frule new_arr_SomeD)
    apply(drule heap_ops_typeof_minimalD'[OF minimal])
    apply(auto split: split_if_asm)
    done
qed(auto dest: heap_ops_typeof_minimalD'[OF minimal] new_arr_SomeD red_external_new_heap_ops_obs[OF minimal] split: split_if_asm)

lemma redT_\<tau>rtrancl3p_created_objects:
  assumes minimal: "heap_ops_typeof_minimal"
  and red: "red_mthr.if.mthr.\<tau>rtrancl3p P \<sigma> ttas \<sigma>'"
  and type: "typeof_addr (shr \<sigma>') a = \<lfloor>T\<rfloor>" "typeof_addr (shr \<sigma>) a = None"
  shows "\<exists>t ta CTn. (t, ta) \<in> set ttas \<and> NormalAction (NewHeapElem a CTn) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> ty_of_htype CTn = T \<and> shr \<sigma>' \<turnstile>a a : CTn"
using red type
proof induct
  case \<tau>rtrancl3p_refl thus ?case by simp
next
  case (\<tau>rtrancl3p_\<tau>step \<sigma> \<sigma>' ttls \<sigma>'' ttl)
  obtain t tl where ttl: "ttl = (t, tl)" by(cases ttl)
  from `red_mthr.if.redT P \<sigma> ttl \<sigma>'` `red_mthr.if.m\<tau>move P \<sigma> ttl \<sigma>'`
  have "shr \<sigma>' = shr \<sigma>" using red_mthr.if.m\<tau>move_heap[of "\<lambda>_ _. True" t \<sigma> P tl \<sigma>']
    unfolding ttl by simp
  with ttl \<tau>rtrancl3p_\<tau>step show ?case by simp
next
  case (\<tau>rtrancl3p_step \<sigma> \<sigma>' ttls \<sigma>'' ttl)
  note type_\<sigma>_a = `typeof_addr (shr \<sigma>) a = None`

  show ?case
  proof(cases "typeof_addr (shr \<sigma>') a = None")
    case True
    with \<tau>rtrancl3p_step show ?thesis by fastsimp
  next
    case False
    
    from `red_mthr.if.mthr.\<tau>rtrancl3p P \<sigma>' ttls \<sigma>''`
    have hext: "shr \<sigma>' \<unlhd> shr \<sigma>''" by(rule init_fin_\<tau>rtrancl3p_hext)
    with False `typeof_addr (shr \<sigma>'') a = \<lfloor>T\<rfloor>`
    have type_\<sigma>'_a: "typeof_addr (shr \<sigma>') a = \<lfloor>T\<rfloor>"
      by(auto dest: typeof_addr_hext_mono)

    with `red_mthr.if.redT P \<sigma> ttl \<sigma>'` type_\<sigma>_a
    obtain t ta x x' where ttl: "ttl = (t, ta)"
      and red_if: "red_mthr.init_fin P t (x, shr \<sigma>) ta (x', shr \<sigma>')"
      by cases fastsimp+
    
    from red_if type_\<sigma>_a type_\<sigma>'_a obtain e xs ta' e' xs'
      where x: "x = (Running, e, xs)" and x': "x' = (Running, e', xs')"
      and ta: "ta = convert_TA_initial (convert_obs_initial ta')"
      and red: "P,t \<turnstile> \<langle>e, (shr \<sigma>, xs)\<rangle> -ta'\<rightarrow> \<langle>e', (shr \<sigma>', xs')\<rangle>"
      by cases fastsimp+
    
    from minimal red type_\<sigma>'_a type_\<sigma>_a obtain CTn
      where "NewHeapElem a CTn \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>" "ty_of_htype CTn = T" "shr \<sigma>' \<turnstile>a a : CTn"
      by(auto dest: red_create_object)
    with hext show ?thesis using ta ttl
      by(fastsimp simp del: split_paired_Ex intro: htypeof_addr_hext_mono)
  qed
qed

end

context J_conf_read begin

lemma JMM_inst_aux: 
  assumes wf_prog: "wf_J_prog P"
  and minimal: "heap_ops_typeof_minimal"
  and start_heap: "start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D"
  and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
  shows "executions_aux (lappend (llist_of (lift_start_obs start_tid start_heap_obs)) ` 
                        red_mthr.if.\<E> P (init_fin_lift_state Running (J_start_state P C M vs)))
                        P"
  (is "executions_aux ?E _")
proof -
  let ?wt_ok = "init_fin_lift_inv (\<lambda>ET t (e, x) m. sconf_type_ok ET e m x)"
  let ?thread_ok = "init_fin_lift (\<lambda>t x m. P,m \<turnstile> t \<surd>t)"
  let ?start_state = "init_fin_lift_state Running (J_start_state P C M vs)"
  let ?obs_prefix = "llist_of (lift_start_obs start_tid start_heap_obs)"
  let ?ET_start = "J_sconf_type_ET_start P C M"

  interpret wt_red!: lifting_inv
    final_expr
    "mred P"
    convert_RA
    "\<lambda>t x m. P,m \<turnstile> t \<surd>t"
    "\<lambda>ET t (e, x) m. sconf_type_ok ET e m x"
    using wf_prog by(rule lifting_inv_sconf_subject_ok)

  interpret wt_red!: if_lifting_inv
    final_expr
    "mred P"
    convert_RA
    "\<lambda>t x m. P,m \<turnstile> t \<surd>t"
    "\<lambda>ET t (e, x) m. sconf_type_ok ET e m x"
    by(unfold_locales)

  interpret wt_if!: \<tau>lifting_inv
    red_mthr.init_fin_final
    "red_mthr.init_fin P"
    "map NormalAction \<circ> convert_RA" 
    "red_mthr.init_fin_\<tau>move P"
    "\<lambda>t ((s, x), m). wfs t (x, m)"
    "?thread_ok"
    "?wt_ok"
    for wfs
    by unfold_locales

  from sconf_type_ts_ok_J_start_state[OF wf_prog start_heap sees conf]
  have wt: "ts_inv ?wt_ok ?ET_start (thr ?start_state) (shr ?start_state)" by(simp)

  from start_heap have thread_ok: "ts_ok ?thread_ok (thr ?start_state) (shr ?start_state)"
    by(simp add: thread_conf_start_state)

  show ?thesis
  proof
    fix E a adal a'
    assume E: "E \<in> ?E"
      and a: "a \<in> new_actions_for P E adal"
      and a': "a' \<in> new_actions_for P E adal"
    from E show "a = a'"
    proof(rule \<E>_new_actions_for_unique)
      from dom_typeof_addr_start_heap
      show "{a. \<exists>CTn. NormalAction (NewHeapElem a CTn) \<in> snd ` lset ?obs_prefix} \<subseteq> dom (typeof_addr (shr ?start_state))"
        by(fastsimp simp add: init_fin_lift_state_conv_simps shr_start_state dest: NewHeapElem_start_heap_obs_start_addrsD subsetD)
    next
      show "ldistinct (lfilter (\<lambda>obs. \<exists>a CTn. obs = NormalAction (NewHeapElem a CTn)) (lmap snd ?obs_prefix))"
        unfolding start_heap_obs_def
        by(fastsimp intro: inj_onI intro!: distinct_filter simp add: distinct_map distinct_zipI1 distinct_initialization_list)
    next
      fix a CTn CTn'
      assume "NormalAction (NewHeapElem a CTn) \<in> snd ` lset ?obs_prefix"
        and "NormalAction (NewHeapElem a CTn') \<in> snd ` lset ?obs_prefix"
      thus "CTn = CTn'" using distinct_start_addrs
        unfolding start_heap_obs_def start_addrs_def
        by(fastsimp simp add: in_set_conv_nth distinct_conv_nth)
    qed fact+
  next
    fix E ra adal
    assume E: "E \<in> ?E"
      and ra: "ra \<in> read_actions E"
      and adal: "adal \<in> action_loc P E ra"

    obtain ad al where ad_al: "adal = (ad, al)" by(cases adal)

    from E obtain E'' where E: "E = lappend ?obs_prefix E''"
      and E'': "E'' \<in> red_mthr.if.\<E> P ?start_state" by auto
    from E'' obtain E' where E': "E'' = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
      and Runs: "red_mthr.if.mthr.Runs P ?start_state E'"
      by(rule red_mthr.if.\<E>.cases)

    have ra_len: "length (lift_start_obs start_tid start_heap_obs) \<le> ra"
    proof(rule ccontr)
      assume "\<not> ?thesis"
      hence "ra < length (lift_start_obs start_tid start_heap_obs)" by simp
      moreover with ra E obtain ra' ad al v 
        where "start_heap_obs ! ra' = ReadMem ad al v" "ra' < length start_heap_obs"
        unfolding lift_start_obs_def
        by cases(auto elim!: actionsE simp add: action_obs_def lnth_lappend1 lnth_llist_of lnth_LCons split: nat.split_asm)
      ultimately have "ReadMem ad al v \<in> set start_heap_obs" unfolding in_set_conv_nth by blast
      thus False by(simp add: start_heap_obs_not_Read)
    qed
    let ?n = "length (lift_start_obs start_tid start_heap_obs)"
    from ra ra_len E have ra: "ra - ?n \<in> read_actions E''"
      by cases(auto simp add: actions_lappend action_obs_def lnth_lappend2 elim: actionsE intro: read_actions.intros)

    from ra ra_len adal ad_al E obtain v
      where ra_obs: "action_obs E'' (ra - ?n) = NormalAction (ReadMem ad al v)"
      by(auto elim!: read_actions.cases simp add: action_obs_def lnth_lappend2)
      
    from ra have "ra - ?n \<in> actions E''" by(auto)
    hence "Fin (ra - ?n) < llength E''" by(rule actionsE)
    with Runs obtain ra_m ra_n t_ra ta_ra 
      where E_ra: "lnth E'' (ra - ?n) = (t_ra, \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub> ! ra_n)"
      and ra_n: "ra_n < length \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>" and ra_m: "Fin ra_m < tlength E'"
      and ra_conv: "ra - ?n = (\<Sum>i<ra_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + ra_n"
      and E'_ra_m: "tnth E' ra_m = (t_ra, ta_ra)"
      unfolding E' by(rule red_mthr.if.actions_\<E>E_aux)
    
    let ?E' = "tdropn (Suc ra_m) E'"
    
    have E'_unfold: "E' = lappendt (ltake (Fin ra_m) (llist_of_tllist E')) (TCons (tnth E' ra_m) ?E')"
      unfolding tdropn_Suc_conv_tdropn[OF ra_m] lappendt_ltake_tdropn ..
    hence "red_mthr.if.mthr.Runs P ?start_state (lappendt (ltake (Fin ra_m) (llist_of_tllist E')) (TCons (tnth E' ra_m) ?E'))"
      using Runs by simp
    then obtain \<sigma>' where \<sigma>_\<sigma>': "red_mthr.if.mthr.\<tau>rtrancl3p P ?start_state (list_of (ltake (Fin ra_m) (llist_of_tllist E'))) \<sigma>'"
      and Runs': "red_mthr.if.mthr.Runs P \<sigma>' (TCons (tnth E' ra_m) ?E')"
      by(rule red_mthr.if.mthr.Runs_lappendtE) simp
    from Runs' obtain \<sigma>'' \<sigma>''' where \<sigma>'_\<sigma>'': "red_mthr.if.mthr.silent_moves P \<sigma>' \<sigma>''"
      and red_ra: "red_mthr.if.redT P \<sigma>'' (t_ra, ta_ra) \<sigma>'''"
      and "\<not> red_mthr.if.m\<tau>move P \<sigma>'' (t_ra, ta_ra) \<sigma>'''"
      and Runs'': "red_mthr.if.mthr.Runs P \<sigma>''' ?E'"
      unfolding E'_ra_m by cases

    note \<sigma>_\<sigma>'
    also note red_mthr.if.mthr.silent_moves_into_\<tau>rtrancl3p[OF \<sigma>'_\<sigma>'']
    finally have \<sigma>_\<sigma>'': "red_mthr.if.mthr.\<tau>rtrancl3p P ?start_state (list_of (ltake (Fin ra_m) (llist_of_tllist E'))) \<sigma>''"
      by simp

    from \<sigma>_\<sigma>'' thread_ok have thread_ok': "ts_ok ?thread_ok (thr \<sigma>'') (shr \<sigma>'')"
      by(rule wt_if.redT_\<tau>rtrancl3p_preserves)

    let ?ETs' = "upd_invs ?ET_start ?wt_ok (concat (map (thr_a \<circ> snd) (list_of (ltake (Fin ra_m) (llist_of_tllist E')))))"
    from \<sigma>_\<sigma>'' wt thread_ok have wt': "ts_inv ?wt_ok ?ETs' (thr \<sigma>'') (shr \<sigma>'')"
      by(rule wt_if.redT_\<tau>rtrancl3p_invariant)

    from \<sigma>_\<sigma>'' have "shr ?start_state \<unlhd> shr \<sigma>''" by(rule init_fin_\<tau>rtrancl3p_hext)
    hence hext: "start_heap \<unlhd> shr \<sigma>''" unfolding init_fin_lift_state_conv_simps shr_start_state .

    from E_ra ra_n ra_obs have "NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>"
      by(auto simp add: action_obs_def in_set_conv_nth)
    with red_ra obtain x_ra x'_ra m'_ra 
      where red'_ra: "red_mthr.init_fin P t_ra (x_ra, shr \<sigma>'') ta_ra (x'_ra, m'_ra)"
      and \<sigma>''': "redT_upd \<sigma>'' t_ra ta_ra x'_ra m'_ra \<sigma>'''"
      and ts_t_a: "thr \<sigma>'' t_ra = \<lfloor>(x_ra, no_wait_locks)\<rfloor>"
      by cases auto
    from red'_ra `NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>`
    obtain ta'_ra e_ra xs_ra e'_ra xs'_ra
      where x_ra: "x_ra = (Running, (e_ra, xs_ra))"
      and x'_ra: "x'_ra = (Running, (e'_ra, xs'_ra))"
      and ta_ra: "ta_ra = convert_TA_initial (convert_obs_initial ta'_ra)"
      and red''_ra: "P,t_ra \<turnstile> \<langle>e_ra, (shr \<sigma>'', xs_ra)\<rangle> -ta'_ra\<rightarrow> \<langle>e'_ra, (m'_ra, xs'_ra)\<rangle>"
      by cases fastsimp+

    from wt' ts_t_a x_ra obtain TEnv T where wt_ra: "P,TEnv,shr \<sigma>'' \<turnstile> e_ra : T"
      by(fastsimp dest: ts_invD simp add: sconf_type_ok_def type_ok_def)

    from `NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>` ta_ra 
    have "ReadMem ad al v \<in> set \<lbrace>ta'_ra\<rbrace>\<^bsub>o\<^esub>" by auto

    with red''_ra wt_ra obtain T' where wt_adal: "P,shr \<sigma>'' \<turnstile> ad@al : T'"
      by(auto dest: red_read_typeable[OF wf_prog])
    
    show "\<exists>wa. wa \<in> new_actions_for P E adal \<and> wa < ra"
    proof(cases "ad \<in> set start_addrs")
      case True
      then obtain CTn where CTn: "NewHeapElem ad CTn \<in> set start_heap_obs"
        by(blast dest: start_addrs_NewHeapElem_start_heap_obsD)
      then obtain wa where wa: "wa < length start_heap_obs" "start_heap_obs ! wa = NewHeapElem ad CTn"
        unfolding in_set_conv_nth by blast
      hence wa_action: "Suc wa \<in> actions E" unfolding E lift_start_obs_def
        by(auto simp add: lnth_lappend1 actions_def Fin_less_Fin_plusI iSuc_Fin[symmetric] intro: ileI1)
      moreover
      from wa E have new_wa: "is_new_action (action_obs E (Suc wa))"
        by(simp add: action_obs_def lnth_lappend1 lift_start_obs_def)
      moreover
      have "(ad, al) \<in> action_loc P E (Suc wa)"
      proof(cases CTn)
        case (Class_type C)
        with CTn have "typeof_addr start_heap ad = \<lfloor>Class C\<rfloor>" by(simp add: NewObj_start_heap_obsD)
        with typeof_addr_hext_mono[OF hext this] wt_adal wa ad_al ra_obs ra_len adal Class_type E
        show ?thesis
          by(fastsimp elim!: addr_loc_type.cases simp add: action_obs_def lnth_lappend1 lift_start_obs_def)
      next
        case (Array_type U n)
        with CTn have "typeof_addr start_heap ad = \<lfloor>Array U\<rfloor>" "n = array_length start_heap ad"
          by(simp_all add: NewArr_start_heap_obsD)
        with typeof_addr_hext_mono[OF hext this(1)] hext_arrD[OF hext this(1)]
          wt_adal wa ad_al ra_obs ra_len adal Array_type E
        show ?thesis
          by(auto elim!: addr_loc_type.cases simp add: action_obs_def lnth_lappend1 lnth_lappend2 lift_start_obs_def)
      qed
      ultimately have "Suc wa \<in> new_actions_for P E adal" unfolding ad_al by(simp add: new_actions_for_def)
      moreover have "Suc wa < ra" using wa ra_len by(simp add: lift_start_obs_def)
      ultimately show ?thesis by blast
    next
      case False
      from wt_adal obtain T_ad where T_ad: "typeof_addr (shr \<sigma>'') ad = \<lfloor>T_ad\<rfloor>" by cases

      from False have "typeof_addr start_heap ad = None"
        using dom_typeof_addr_start_heap_eq_start_addrs[OF minimal] by auto
      hence "typeof_addr (shr ?start_state) ad = None" unfolding init_fin_lift_state_conv_simps shr_start_state .
      from redT_\<tau>rtrancl3p_created_objects[OF minimal \<sigma>_\<sigma>'' T_ad this]
      obtain t_wa ta_wa CTn 
        where t_wa_ta_wa: "(t_wa, ta_wa) \<in> set (list_of (ltake (Fin ra_m) (llist_of_tllist E')))"
        and CTn: "NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta_wa\<rbrace>\<^bsub>o\<^esub>"
        and type_wa: "ty_of_htype CTn = T_ad" "shr \<sigma>'' \<turnstile>a ad : CTn" by blast
      from t_wa_ta_wa ra_m obtain wa_m
        where wa_m: "wa_m < ra_m" and E'_wa_m: "tnth E' wa_m = (t_wa, ta_wa)"
        unfolding in_set_conv_nth
        by(auto simp add: lnth_ltake length_list_of_conv_the_Fin min_def split: split_if_asm)
      from wa_m ra_m have wa_m_len: "Fin wa_m < tlength E'"
        by(simp add: less_trans[where y="Fin ra_m"])

      from CTn obtain wa_n where wa_n: "wa_n < length \<lbrace>ta_wa\<rbrace>\<^bsub>o\<^esub>"
        and ta_wa_n: "\<lbrace>ta_wa\<rbrace>\<^bsub>o\<^esub> ! wa_n = NormalAction (NewHeapElem ad CTn)"
        unfolding in_set_conv_nth by blast
      let ?wa = "(\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n + length (lift_start_obs start_tid start_heap_obs)"

      have "llength (lconcat (ltake (Fin (Suc wa_m)) (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')))) =
            (\<Sum>i | i < Suc wa_m \<and> Fin i < tlength E'. (Fin \<circ> (\<lambda>i. length \<lbrace>snd (lnth (ltake (Fin (Suc wa_m)) (llist_of_tllist E')) i)\<rbrace>\<^bsub>o\<^esub>)) i)"
        by(subst llength_lconcat_lfinite_conv_sum)(simp_all add: split_beta)
      also have "\<dots> = Fin (\<Sum>i | i < Suc wa_m \<and> Fin i < tlength E'. length \<lbrace>snd (lnth (ltake (Fin (Suc wa_m)) (llist_of_tllist E')) i)\<rbrace>\<^bsub>o\<^esub>)"
        by(rule setsum_hom)(simp_all add: zero_inat_def)
      also have "\<dots> = Fin (\<Sum>i<Suc wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
        unfolding inat.inject by(rule setsum_cong)(auto intro: le_less_trans[OF _ wa_m_len] simp add: lnth_ltake)
      finally have "Fin ((\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n) < 
            llength (lconcat (ltake (Fin (Suc wa_m)) (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))
                                                           (llist_of_tllist E'))))"
        using wa_n E'_wa_m by simp
      also have "\<dots> \<le> llength E''" unfolding E'
        by(blast intro: lprefix_llength_le lprefix_lconcatI ltake_is_lprefix)
      finally have wa'_len: "Fin ((\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n) < llength E''" .
      from lnth_lconcat_conv[OF this[unfolded E']]
      obtain wa_m' wa_n'
        where E''_wa: "lnth E'' ((\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n) = 
                       lnth (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) wa_m') wa_n'"
        and wa_n': "Fin wa_n' < llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) wa_m')"
        and wa_m': "Fin wa_m' < llength (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
        and wa': "Fin ((\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n) =
                  (\<Sum>i<wa_m'. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) i)) + Fin wa_n'"
        unfolding E' by blast

      from wa_m' have wa_m': "Fin wa_m' < tlength E'" by simp
      with wa_n' have wa_n': "wa_n' < length \<lbrace>snd (tnth E' wa_m')\<rbrace>\<^bsub>o\<^esub>" by(simp add: split_beta)
      have "(\<Sum>i<wa_m'. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')) i)) =
            (\<Sum>i<wa_m'. (Fin \<circ> (\<lambda>i. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)) i)"
        by(rule setsum_cong)(simp_all add: less_trans[where y="Fin wa_m'"] split_beta wa_m')
      also have "\<dots> = Fin (\<Sum>i<wa_m'. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
        by(rule setsum_hom)(simp_all add: zero_inat_def)
      finally have wa': "(\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n = (\<Sum>i<wa_m'. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n'"
        using wa' by simp
      moreover have [simp]: "wa_m' = wa_m"
      proof(rule ccontr)
        assume "wa_m' \<noteq> wa_m"
        thus False unfolding neq_iff
        proof
          assume "wa_m' < wa_m"
          hence "(\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) = 
                 (\<Sum>i<wa_m'. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i=wa_m'..<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
            unfolding atLeast0LessThan[symmetric] by(subst setsum_add_nat_ivl) simp_all
          with wa' have "(\<Sum>i=wa_m'..<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n = wa_n'" by simp
          moreover have "(\<Sum>i=wa_m'..<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) \<ge> length \<lbrace>snd (tnth E' wa_m')\<rbrace>\<^bsub>o\<^esub>"
            by(subst setsum_head_upt_Suc[OF `wa_m' < wa_m`]) simp
          ultimately show False using wa_n' by simp
        next
          assume "wa_m < wa_m'"
          hence "(\<Sum>i<wa_m'. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) = 
                 (\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i=wa_m..<wa_m'. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
            unfolding atLeast0LessThan[symmetric] by(subst setsum_add_nat_ivl) simp_all
          with wa' have "(\<Sum>i=wa_m..<wa_m'. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n' = wa_n" by simp
          moreover have "(\<Sum>i=wa_m..<wa_m'. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) \<ge> length \<lbrace>snd (tnth E' wa_m)\<rbrace>\<^bsub>o\<^esub>"
            by(subst setsum_head_upt_Suc[OF `wa_m < wa_m'`]) simp
          ultimately show False using wa_n E'_wa_m by simp
        qed
      qed
      ultimately have [simp]: "wa_n' = wa_n" by simp
      from E''_wa wa_m_len wa_n E'_wa_m ta_wa_n
      have "lnth E'' ((\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n) = (t_wa, NormalAction (NewHeapElem ad CTn))"
        by(simp add: split_beta lnth_llist_of)
      hence "action_obs E ?wa = NormalAction (NewHeapElem ad CTn)" unfolding E
        by(simp add: action_obs_def lnth_lappend2)
      moreover hence "adal \<in> action_loc P E ?wa" using ad_al adal type_wa wt_adal
        by(cases CTn)(fastsimp elim!: addr_loc_type.cases)+
      moreover from wa'_len have "?wa \<in> actions E" 
        unfolding actions_def E by(cases "llength E''")(auto)
      ultimately have "?wa \<in> new_actions_for P E adal" by(simp add: new_actions_for_def)
      moreover
      {
        have "(\<Sum>i<ra_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) =
              (\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i=wa_m..<ra_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
          using wa_m unfolding atLeast0LessThan[symmetric] by(subst setsum_add_nat_ivl) simp_all
        also have "\<dots> > (\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n"
          using wa_n E'_wa_m by(subst setsum_head_upt_Suc[OF wa_m]) simp
        finally have "ra - length (lift_start_obs start_tid start_heap_obs) > (\<Sum>i<wa_m. length \<lbrace>snd (tnth E' i)\<rbrace>\<^bsub>o\<^esub>) + wa_n"
          unfolding ra_conv by simp
        hence "?wa < ra" using ra_len by simp }
      ultimately show ?thesis by blast
    qed
  qed
qed

section {* Locale @{text exeuctions} *}

lemma assumes wf: "wf_prog wf_md P"
  shows red_write_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,E,hp s \<turnstile> e : T; hconf (hp s); WriteMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>T'. P,hp s' \<turnstile> ad@al : T' \<and> P,hp s' \<turnstile> v :\<le> T'"
  and reds_write_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; P,E,hp s \<turnstile> es [:] Ts; hconf (hp s); WriteMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>T'. P,hp s' \<turnstile> ad@al : T' \<and> P,hp s' \<turnstile> v :\<le> T'"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case RedAAss thus ?case
    by(fastsimp intro: addr_loc_type.intros simp add: nat_less_iff word_sle_def conf_def hext_arrD dest!: hext_heap_write intro: typeof_addr_hext_mono hext_typeof_mono)
next
  case RedFAss thus ?case
    by(fastsimp intro: addr_loc_type.intros simp add: conf_def dest: typeof_addr_eq_Some_conv dest!: hext_heap_write elim: typeof_addr_hext_mono hext_typeof_mono)
next
  case RedCallExternal thus ?case
    by(auto intro: red_external_write_typeable[OF wf])
qed auto

lemma red_mrw_values_typeable:
  assumes wf: "wf_prog wf_md P"
  and vs: "vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,h \<turnstile> ad@al : T \<and> P,h \<turnstile> v :\<le> T"
  and red: "P,t \<turnstile> \<langle>e, (h, xs)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle>"
  and wt: "P,E,h \<turnstile> e : T" "hconf h"
  and vs': "mrw_values P vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ad, al) = \<lfloor>(v, b)\<rfloor>"
  shows "\<exists>T. P,h' \<turnstile> ad@al : T \<and> P,h' \<turnstile> v :\<le> T"
proof(cases "vs (ad, al) = \<lfloor>(v, b)\<rfloor>")
  case True
  hence "\<exists>T. P,h \<turnstile> ad@al : T \<and> P,h \<turnstile> v :\<le> T" by(rule vs)
  moreover from red have "h \<unlhd> h'" by(auto dest: red_hext_incr)
  ultimately show ?thesis by(auto intro: conf_hext addr_loc_type_hext_mono)
next
  case False
  with mrw_values_eq_SomeD[OF vs']
  obtain obs' wa obs'' 
    where eq: "map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = obs' @ wa # obs''"
    and "is_write_action wa"
    and adal: "(ad, al) \<in> action_loc_aux P wa"
    and vwa: "value_written_aux P wa al = v"
    by blast
  show ?thesis
  proof(cases "is_new_action wa")
    case False with `is_write_action wa`
    obtain ad' al' v' where "wa = NormalAction (WriteMem ad' al' v')"
      by cases auto
    with vwa adal eq have "WriteMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
      by(auto simp add: map_eq_append_conv)
    with red wt show ?thesis by(auto dest!: red_write_typeable[OF wf])
  next
    case True
    then obtain ad' CTn where wa: "wa = NormalAction (NewHeapElem ad' CTn)"
      by cases auto
    with vwa adal eq have new: "NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" and [simp]: "ad' = ad"
      by(auto simp add: map_eq_append_conv)
    from red_New_typeof_addrD[OF red this(1)]
    have "typeof_addr h' ad = \<lfloor>ty_of_htype CTn\<rfloor>" by simp
    moreover {
      fix T n
      assume "CTn = Array_type T n"
      with new have "NewArr ad T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" by simp
      from red_NewArr_lengthD[OF red this]
      have "array_length h' ad = n" by(simp) }
    ultimately show ?thesis using adal wa vwa
      by(fastsimp simp add: has_field_def intro: addr_loc_type.intros)
  qed
qed

lemma if_red_mrw_values_typeable:
  assumes wf: "wf_prog wf_md P"
  and vs: "vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,h \<turnstile> ad@al : T \<and> P,h \<turnstile> v :\<le> T"
  and red: "red_mthr.init_fin P t ((s, e, xs), h) ta ((s', e', xs'), h')"
  and wt: "P,E,h \<turnstile> e : T" "hconf h"
  and vs': "mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> (ad, al) = \<lfloor>(v, b)\<rfloor>"
  shows "\<exists>T. P,h' \<turnstile> ad@al : T \<and> P,h' \<turnstile> v :\<le> T"
using red vs' vs
by cases(auto intro: red_mrw_values_typeable[OF wf vs _ wt])

lemma redT_mrw_values_typeable:
  assumes wf: "wf_prog wf_md P"
  and vs: "vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,shr s \<turnstile> ad@al : T \<and> P,shr s \<turnstile> v :\<le> T"
  and red: "red_mthr.if.redT P s (t,ta) s'"
  and wt: "ts_inv (init_fin_lift_inv (\<lambda>ET t (e, x) m. sconf_type_ok ET e m x)) I (thr s) (shr s)"
  and convert_RA_not_write: "\<And>ln ob. ob \<in> set (convert_RA ln) \<Longrightarrow> \<not> is_write_action (NormalAction ob)"
  and vs': "mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> (ad, al) = \<lfloor>(v, b)\<rfloor>"
  shows "\<exists>T. P,shr s' \<turnstile> ad@al : T \<and> P,shr s' \<turnstile> v :\<le> T"
using red
proof(cases)
  case (redT_normal x x' m')
  then obtain \<sigma> e xs \<sigma>' e' xs' 
    where x: "x = (\<sigma>, e, xs)" "x' = (\<sigma>', e', xs')"
    and red: "red_mthr.init_fin P t ((\<sigma>, e, xs), shr s) ta ((\<sigma>', e', xs'), m')"
    and m': "m' = shr s'"
    and tst: "thr s t = \<lfloor>((\<sigma>, e, xs), no_wait_locks)\<rfloor>"
    by(cases x)(cases x', fastsimp)
  from wt tst obtain E T where wt: "P,E,shr s \<turnstile> e : T" and hconf: "hconf (shr s)"
    by(auto dest!: ts_invD simp add: sconf_type_ok_def sconf_def type_ok_def)
  with wf vs red show ?thesis using vs' unfolding m' by(rule if_red_mrw_values_typeable)
next
  case (redT_acquire x ln n)
  have "mrw_values P vs (map NormalAction (convert_RA ln)) (ad, al) = vs (ad, al)"
    by(rule mrw_values_no_write_unchanged)(auto dest: convert_RA_not_write)
  with redT_acquire vs' show ?thesis by(auto intro: vs)
qed

lemma \<tau>RedT_mrw_values_typeable:
  assumes wf: "wf_J_prog P"
  and vs: "vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,shr s \<turnstile> ad@al : T \<and> P,shr s \<turnstile> v :\<le> T"
  and red: "red_mthr.if.mthr.\<tau>rtrancl3p P s ttas s'"
  and thread_ok: "ts_ok (init_fin_lift (\<lambda>t x m. P,m \<turnstile> t \<surd>t)) (thr s) (shr s)"
    (is "?thread_ok (thr s) (shr s)")
  and wt: "ts_inv (init_fin_lift_inv (\<lambda>ET t (e, x) m. sconf_type_ok ET e m x)) I (thr s) (shr s)"
    (is "?wt_ok I (thr s) (shr s)")
  and convert_RA_not_write: "\<And>ln ob. ob \<in> set (convert_RA ln) \<Longrightarrow> \<not> is_write_action (NormalAction ob)"
  and vs': "mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)) (ad, al) = \<lfloor>(v, b)\<rfloor>"
    (is "mrw_values _ _ (?conv ttas) _ = _")
  shows "\<exists>T. P,shr s' \<turnstile> ad@al : T \<and> P,shr s' \<turnstile> v :\<le> T"
proof -

  interpret wt_red!: lifting_inv
    final_expr
    "mred P"
    convert_RA
    "\<lambda>t x m. P,m \<turnstile> t \<surd>t"
    "\<lambda>ET t (e, x) m. sconf_type_ok ET e m x"
    using wf by(rule lifting_inv_sconf_subject_ok)

  interpret wt_red!: if_lifting_inv
    final_expr
    "mred P"
    convert_RA
    "\<lambda>t x m. P,m \<turnstile> t \<surd>t"
    "\<lambda>ET t (e, x) m. sconf_type_ok ET e m x"
    by(unfold_locales)

  from red thread_ok wt vs vs' show ?thesis
  proof(induct arbitrary: vs I)
    case (\<tau>rtrancl3p_refl s)
    thus ?case by simp
  next
    case (\<tau>rtrancl3p_step s s' tls s'' tl)
    from `red_mthr.if.redT P s tl s'` obtain t ta
      where tl: "tl = (t, ta)"
      and red: "red_mthr.if.redT P s (t, ta) s'"
      by(cases tl) fastsimp

    note vs = `vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,shr s \<turnstile> ad@al : T \<and> P,shr s \<turnstile> v :\<le> T`
    note wt_ok = `?wt_ok I (thr s) (shr s)`
    note thread_ok = `?thread_ok (thr s) (shr s)`
    with red have thread_ok': "?thread_ok (thr s') (shr s')"
      by(rule wt_red.if.redT_preserves)
    moreover from red wt_ok thread_ok
    obtain I' where "?wt_ok I' (thr s') (shr s')"
      by(blast dest: wt_red.if.redT_invariant)
    moreover {
      assume "mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> (ad, al) = \<lfloor>(v, b)\<rfloor>"
      with wf vs red wt_ok convert_RA_not_write
      have "\<exists>T. P,shr s' \<turnstile> ad@al : T \<and> P,shr s' \<turnstile> v :\<le> T" by(rule redT_mrw_values_typeable) }
    moreover from `mrw_values P vs (?conv (tl # tls)) (ad, al) = \<lfloor>(v, b)\<rfloor>`
    have "mrw_values P (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (?conv tls) (ad, al) = \<lfloor>(v, b)\<rfloor>"
      unfolding tl by simp
    ultimately show ?case by(rule \<tau>rtrancl3p_step.hyps)
  next
    case (\<tau>rtrancl3p_\<tau>step s s' tls s'' tl vs)
    from `red_mthr.if.redT P s tl s'` obtain t ta
      where tl: "tl = (t, ta)"
      and red: "red_mthr.if.redT P s (t, ta) s'"
      by(cases tl) fastsimp

    note vs = `vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,shr s \<turnstile> ad@al : T \<and> P,shr s \<turnstile> v :\<le> T`
    note wt_ok = `?wt_ok I (thr s) (shr s)`
    note thread_ok = `?thread_ok (thr s) (shr s)`
    with red have thread_ok': "?thread_ok (thr s') (shr s')"
      by(rule wt_red.if.redT_preserves)
    moreover from red wt_ok thread_ok
    obtain I' where "?wt_ok I' (thr s') (shr s')"
      by(blast dest: wt_red.if.redT_invariant)
    moreover {
      assume "mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> (ad, al) = \<lfloor>(v, b)\<rfloor>"
      with wf vs red wt_ok convert_RA_not_write
      have "\<exists>T. P,shr s' \<turnstile> ad@al : T \<and> P,shr s' \<turnstile> v :\<le> T" 
        by(rule redT_mrw_values_typeable) }
    moreover from `red_mthr.if.m\<tau>move P s tl s'`
    have "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = []" unfolding tl
      by(auto elim!: red_mthr.if.m\<tau>move.cases red_mthr.init_fin_\<tau>move.cases)
    with `mrw_values P vs (?conv tls) (ad, al) = \<lfloor>(v, b)\<rfloor>`
    have "mrw_values P (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (?conv tls) (ad, al) = \<lfloor>(v, b)\<rfloor>" by simp
    ultimately show ?case by(rule \<tau>rtrancl3p_\<tau>step.hyps)
  qed
qed

end

interpretation jmm'!: J_typesafe 
  jmm_empty
  jmm_new_obj
  jmm_new_arr
  jmm_typeof_addr
  jmm_array_length
  "jmm_heap_read' P"
  "jmm_heap_write' P"
  "jmm'_hconf P"
  P
  for P
by unfold_locales

abbreviation jmm'_red' :: "J_prog \<Rightarrow> nat \<Rightarrow> expr \<Rightarrow> JMM_heap \<times> locals \<Rightarrow> JMM_heap J_thread_action \<Rightarrow> expr \<Rightarrow> JMM_heap \<times> locals \<Rightarrow> bool"
  ("_,_ \<turnstile>jmm' ((1\<langle>_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0,0,0] 81)
where "jmm'_red' P \<equiv> jmm'.red' P P"

abbreviation jmm'_reds' :: "J_prog \<Rightarrow> nat \<Rightarrow> expr list \<Rightarrow> JMM_heap \<times> locals \<Rightarrow> JMM_heap J_thread_action \<Rightarrow> expr list \<Rightarrow> JMM_heap \<times> locals \<Rightarrow> bool"
  ("_,_ \<turnstile>jmm' ((1\<langle>_,/_\<rangle>) [-_\<rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0,0,0] 81)
where "jmm'_reds' P \<equiv> jmm'.reds' P P"

notation jmm'.WTrt_syntax ("_,_,_ \<turnstile>jmm' _ : _"   [51,51,51]50)
notation jmm'.WTrts_syntax ("_,_,_ \<turnstile>jmm' _ [:] _"   [51,51,51]50)

subsection {* Cut and update *}

declare split_paired_Ex [simp del]
declare eq_upto_seq_inconsist_simps [simp]

lemma assumes wf: "wf_prog wf_md P"
  and vs: "\<And>ad al v b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>T. P,shr s \<turnstile>jmm' ad@al : T \<and> P,shr s \<turnstile>jmm' v :\<le> T"
  and dom_vs: "{(ad, al). \<exists>T. P,shr s \<turnstile>jmm' ad@al : T} \<subseteq> dom vs"
  and hconf: "P \<turnstile>jmm' shr s \<surd>"
  shows red_cut_and_update:
  "\<lbrakk> P,t \<turnstile>jmm' \<langle>e, (shr s, xs)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle>; P,E,shr s \<turnstile>jmm' e : T;
 (* thr s t = \<lfloor>((\<sigma>, e, xs), no_wait_locks)\<rfloor>; *)
    jmm'.red_mthr.if.actions_ok s t ta \<rbrakk>
  \<Longrightarrow> \<exists>ta' e'' xs'' h''. P,t \<turnstile>jmm' \<langle>e, (shr s, xs)\<rangle> -ta'\<rightarrow> \<langle>e'', (h'', xs'')\<rangle> \<and> 
           jmm'.red_mthr.if.actions_ok s t ta' \<and> 
           ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) \<and>
           eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) vs"
  and reds_cut_and_update:
  "\<lbrakk> P,t \<turnstile>jmm' \<langle>es, (shr s, xs)\<rangle> [-ta\<rightarrow>] \<langle>es', (h', xs')\<rangle>; P,E,shr s \<turnstile>jmm' es [:] Ts;
 (* thr s t = \<lfloor>((\<sigma>, e, xs), no_wait_locks)\<rfloor>; *)
    jmm'.red_mthr.if.actions_ok s t ta \<rbrakk>
  \<Longrightarrow> \<exists>ta' es'' xs'' h''. P,t \<turnstile>jmm' \<langle>es, (shr s, xs)\<rangle> [-ta'\<rightarrow>] \<langle>es'', (h'', xs'')\<rangle> \<and> 
           jmm'.red_mthr.if.actions_ok s t ta' \<and> 
           ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) \<and>
           eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) vs"
proof(induct e hxs\<equiv>"(shr s, xs)" ta e' hxs'\<equiv>"(h', xs')" 
         and es hxs\<equiv>"(shr s, xs)" ta es' hxs'\<equiv>"(h', xs')"
      arbitrary: xs xs' E T and xs xs' E Ts rule: jmm'.red_reds.inducts)
  case (RedInstanceOf v U b T)
  thus ?case by(intro exI conjI)(rule jmm'.RedInstanceOf, simp_all)
next
  case (RedAAcc a U i v e)
  hence adal: "P,shr s \<turnstile>jmm' a@ACell (nat (sint i)) : U"
    by(auto intro: jmm'.addr_loc_type.intros simp add: nat_less_iff word_sle_def)
  then obtain b v' where bv': "vs (a, ACell (nat (sint i))) = \<lfloor>(v', b)\<rfloor>"
    using subsetD[OF dom_vs, where c="(a, ACell (nat (sint i)))"] by fastsimp
  with adal have "P,shr s \<turnstile>jmm' v' :\<le> U" by(auto dest: vs jmm'.addr_loc_type_fun)
  with adal have "jmm_heap_read' P (shr s) a (ACell (nat (sint i))) v'"
    by(auto simp add: jmm_heap_read'_def dest: jmm'.addr_loc_type_fun)
  with bv' `jmm_typeof_addr (shr s) a = \<lfloor>U\<lfloor>\<rceil>\<rfloor>` `0 <=s i` `sint i < int (jmm_array_length (shr s) a)` 
    `jmm'.red_mthr.if.actions_ok s t \<epsilon>\<lbrace>\<^bsub>o\<^esub>ReadMem a (ACell (nat (sint i))) v\<rbrace>`
  show ?case by(fastsimp intro: jmm'.RedAAcc)
next
  case (RedFAcc a D F v)
  hence adal: "P,shr s \<turnstile>jmm' a@CField D F : T"
    by(auto dest: jmm'.typeof_addr_eq_Some_conv intro: jmm'.addr_loc_type.intros)
  then obtain b v' where bv': "vs (a, CField D F) = \<lfloor>(v', b)\<rfloor>"
    using subsetD[OF dom_vs, where c="(a, CField D F)"] by fastsimp
  with adal have "P,shr s \<turnstile>jmm' v' :\<le> T" by(auto dest: vs jmm'.addr_loc_type_fun)
  with adal have "jmm_heap_read' P (shr s) a (CField D F) v'"
    by(auto simp add: jmm_heap_read'_def dest: jmm'.addr_loc_type_fun)
  with bv' `jmm'.red_mthr.if.actions_ok s t \<epsilon>\<lbrace>\<^bsub>o\<^esub>ReadMem a (CField D F) v\<rbrace>`
  show ?case by(fastsimp intro: jmm'.RedFAcc)
next
  case (RedCallExternal a U M vs ta' va h' ta e')
  from `P,t \<turnstile>jmm' \<langle>a\<bullet>M(vs),hp (shr s, xs)\<rangle> -ta'\<rightarrow>ext \<langle>va,h'\<rangle>`
  have red: "P,t \<turnstile>jmm' \<langle>a\<bullet>M(vs),shr s\<rangle> -ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by simp
  from RedCallExternal have "jmm'.red_mthr.if.actions_ok s t ta'" by simp
  from jmm'.red_mthr.if.red_external_cut_and_update[OF wf vs dom_vs red this hconf, of "\<lambda>_ _ _ b. b"]
    `jmm_typeof_addr (hp (shr s, xs)) a = \<lfloor>U\<rfloor>` `is_external_call P U M` `ta = extTA2J P ta'`
  show ?case by(fastsimp intro: jmm'.red_reds.RedCallExternal)
next 
  case NewArrayRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next 
  case CastRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case InstanceOfRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case BinOpRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case BinOpRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case LAssRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case AAccRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case AAccRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case AAssRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case AAssRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case AAssRed3 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case ALengthRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case FAccRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case FAssRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case FAssRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case CallObj thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case CallParams thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case BlockRed thus ?case by(fastsimp intro: jmm'.red_reds.intros)
next
  case SynchronizedRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case SynchronizedRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case SeqRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case CondRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case ThrowRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case TryRed thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case ListRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
next
  case ListRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex)(blast intro: jmm'.red_reds.intros)
qed(fastsimp intro: jmm'.red_reds.intros)+


declare split_paired_Ex [simp]
declare eq_upto_seq_inconsist_simps [simp del]

lemma cut_and_update:
  assumes wf_prog: "wf_J_prog P"
  and start_heap: "jmm'.start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D"
  and conf: "P,jmm'.start_heap \<turnstile>jmm' vs [:\<le>] Ts"
  shows "jmm'.red_mthr_if.cut_and_update P (init_fin_lift_state Running (jmm'.J_start_state P C M vs)) 
                                        (mrw_values P empty (map snd (lift_start_obs jmm'.start_tid jmm'.start_heap_obs)))"
  (is "jmm'.red_mthr_if.cut_and_update _ ?start_state ?start_vs")
proof(rule jmm'.red_mthr_if.cut_and_updateI)
  fix ttas s' t x ta x' m'
  assume \<tau>Red: "jmm'.red_mthr.if.mthr.\<tau>rtrancl3p P P ?start_state ttas s'"
    and sc: "ta_seq_consist P ?start_vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    and ts't: "thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and red: "jmm'.red_mthr.init_fin P P t (x, shr s') ta (x', m')"
    and aok: "jmm'.red_mthr.if.actions_ok s' t ta"
    and n\<tau>: "\<not> jmm'.red_mthr.init_fin_\<tau>move P (x, shr s') ta (x', m')"

  let ?conv = "\<lambda>ttas. concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)"
  let ?vs' = "mrw_values P ?start_vs (?conv ttas)"
  let ?wt_ok = "init_fin_lift_inv (\<lambda>ET t (e, x) m. jmm'.sconf_type_ok P ET e m x)"
  let ?thread_ok = "init_fin_lift (\<lambda>t x m. P,m \<turnstile>jmm' t \<surd>t)"
  let ?ET_start = "jmm'.J_sconf_type_ET_start P C M"
  let ?start_obs = "map snd (lift_start_obs jmm'.start_tid jmm'.start_heap_obs)"


  interpret wt_red!: lifting_inv
    final_expr
    "jmm'.mred P P"
    convert_RA
    "\<lambda>t x m. P,m \<turnstile>jmm' t \<surd>t"
    "\<lambda>ET t (e, x) m. jmm'.sconf_type_ok P ET e m x"
    using wf_prog by(rule jmm'.lifting_inv_sconf_subject_ok)

  interpret wt_red!: if_lifting_inv
    final_expr
    "jmm'.mred P P"
    convert_RA
    "\<lambda>t x m. P,m \<turnstile>jmm' t \<surd>t"
    "\<lambda>ET t (e, x) m. jmm'.sconf_type_ok P ET e m x"
    by(unfold_locales)

  interpret wt_if!: \<tau>lifting_inv
    jmm'.red_mthr.init_fin_final
    "jmm'.red_mthr.init_fin P P"
    "map NormalAction \<circ> convert_RA" 
    "jmm'.red_mthr.init_fin_\<tau>move P"
    "\<lambda>t ((s, x), m). wfs t (x, m)"
    "?thread_ok"
    "?wt_ok"
    for wfs
    by unfold_locales

  from jmm'.sconf_type_ts_ok_J_start_state[OF wf_prog start_heap sees conf]
  have wt: "ts_inv ?wt_ok ?ET_start (thr ?start_state) (shr ?start_state)" by(simp)

  from start_heap have thread_ok: "ts_ok ?thread_ok (thr ?start_state) (shr ?start_state)"
    by(simp add: jmm'.thread_conf_start_state)

  from \<tau>Red wt thread_ok obtain ET'
    where wt': "ts_inv ?wt_ok ET' (thr s') (shr s')"
    by(blast dest: wt_if.redT_\<tau>rtrancl3p_invariant)

  from \<tau>Red have hext: "shr ?start_state \<unlhd>jmm' shr s'"
    by(rule jmm'.init_fin_\<tau>rtrancl3p_hext)

  show "\<exists>ta' x'' m''. jmm'.red_mthr.init_fin P P t (x, shr s') ta' (x'', m'') \<and>
                      jmm'.red_mthr.if.actions_ok s' t ta' \<and>
                      \<not> jmm'.red_mthr.init_fin_\<tau>move P (x, shr s') ta' (x'', m'') \<and>
                      ta_seq_consist P ?vs' (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                      eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ?vs'"
  proof(cases "ta_seq_consist P ?vs' (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)")
    case True
    hence "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ?vs'"
      by(rule ta_seq_consist_imp_eq_upto_seq_inconsist_refl)
    with red aok n\<tau> True show ?thesis by blast
  next
    case False
    with red obtain e xs e' xs' ta'
      where x: "x = (Running, e, xs)" and x': "x' = (Running, e', xs')"
      and ta: "ta = convert_TA_initial (convert_obs_initial ta')"
      and red': "P,t \<turnstile>jmm' \<langle>e, (shr s', xs)\<rangle> -ta'\<rightarrow> \<langle>e', (m', xs')\<rangle>"
      by cases fastsimp+

    from ts't wt' x obtain E T where wte: "P,E,shr s' \<turnstile>jmm' e : T"
      and hconf: "P \<turnstile>jmm' shr s' \<surd>"
      by(auto dest!: ts_invD simp add: jmm'.sconf_type_ok_def jmm'.sconf_def jmm'.type_ok_def)

    have aok': "jmm'.red_mthr.if.actions_ok s' t ta'"
      using aok unfolding ta by simp

    { fix ad al v b
      assume "?vs' (ad, al) = \<lfloor>(v, b)\<rfloor>"
      moreover
      { assume "?start_vs (ad, al) = \<lfloor>(v, b)\<rfloor>"
        hence "\<exists>T. P,jmm'.start_heap \<turnstile>jmm' ad@al : T \<and> P,jmm'.start_heap \<turnstile>jmm' v :\<le> T" 
          by -(rule heap.mrw_values_start_heap_obs_typeable[OF jmm'_heap], simp add: lift_start_obs_def o_def)
        hence "\<exists>T. P,shr ?start_state \<turnstile>jmm' ad@al : T \<and> P,shr ?start_state \<turnstile>jmm' v :\<le> T"
          by(simp add: init_fin_lift_state_conv_simps jmm'.start_state_def split_beta) }
      ultimately have "\<exists>T. P,shr s' \<turnstile>jmm' ad@al : T \<and> P,shr s' \<turnstile>jmm' v :\<le> T"
        using \<tau>Red thread_ok wt convert_RA_not_write
        by -(rule jmm'.\<tau>RedT_mrw_values_typeable[OF wf_prog]) }
    note wt_vs = this

    { fix ad al T
      assume adal: "P,shr s' \<turnstile>jmm' ad@al : T"
      then obtain U where U: "jmm_typeof_addr (shr s') ad = \<lfloor>U\<rfloor>" by cases
      have "(ad, al) \<in> dom ?vs'"
      proof(cases "jmm_typeof_addr (shr ?start_state) ad")
        case None
        from jmm'.redT_\<tau>rtrancl3p_created_objects[OF jmm'_heap_ops_typeof_minimal \<tau>Red U None]
        obtain CTn where CTn: "NormalAction (NewHeapElem ad CTn) \<in> set (?conv ttas)"
          and "U = ty_of_htype CTn" "jmm'.htypeof_addr (shr s') ad CTn" by(fastsimp)
        with U adal have "(ad, al) \<in> action_loc_aux P (NormalAction (NewHeapElem ad CTn))"
          by(cases CTn)(fastsimp elim!: jmm'.addr_loc_type.cases)+
        from mrw_values_new_actionD[OF CTn _ this, where ?vs0.0="?start_vs"]
        show ?thesis by auto
      next
        case (Some U')
        hence "ad \<in> set jmm'.start_addrs"
          
          using subsetD[OF jmm'.dom_typeof_addr_start_heap_eq_start_addrs[OF jmm'_heap_ops_typeof_minimal, THEN equalityD1], where c="ad"]
          by(auto simp add: init_fin_lift_state_conv_simps jmm'.start_state_def split_def)
        from jmm'.start_addrs_NewHeapElem_start_heap_obsD[OF this]
        obtain CTn where CTn: "NewHeapElem ad CTn \<in> set jmm'.start_heap_obs" ..
        hence CTn': "NormalAction (NewHeapElem ad CTn) \<in> set ?start_obs" by(auto simp add: image_image)
        have "(ad, al) \<in> action_loc_aux P (NormalAction (NewHeapElem ad CTn))"
        proof(cases CTn)
          case (Class_type C)
          with CTn have "jmm_typeof_addr jmm'.start_heap ad = \<lfloor>Class C\<rfloor>"
            by(auto dest: jmm'.NewObj_start_heap_obsD)
          with hext have "jmm_typeof_addr (shr s') ad = \<lfloor>Class C\<rfloor>"
            by(simp add: init_fin_lift_state_conv_simps jmm'.start_state_def split_def jmm'.typeof_addr_hext_mono)
          with adal U Class_type show ?thesis by cases auto
        next
          case (Array_type T n)
          with CTn have "jmm_typeof_addr jmm'.start_heap ad = \<lfloor>Array T\<rfloor>"
            and "jmm_array_length jmm'.start_heap ad = n"
            by(auto dest: jmm'.NewArr_start_heap_obsD)
          with hext have "jmm_typeof_addr (shr s') ad = \<lfloor>Array T\<rfloor>"
            and "jmm_array_length (shr s') ad = n"
            by(auto simp add: init_fin_lift_state_conv_simps jmm'.start_state_def split_def dest: jmm'.hext_arrD)
          with adal U Array_type show ?thesis by cases auto
        qed
        from mrw_values_new_actionD[OF CTn' _ this, where ?vs0.0=empty]
        have "(ad, al) \<in> dom ?start_vs" by auto
        also note mrw_values_dom_mono
        finally show ?thesis .
      qed }
    hence "{(ad, al). \<exists>T. P,shr s' \<turnstile>jmm' ad@al : T} \<subseteq> dom ?vs'" by blast

    from red_cut_and_update[OF wf_prog wt_vs this hconf red' wte aok', where ?b3="\<lambda>_ _ _ b. b"]
    obtain ta'' e'' xs'' h''
      where red'': "P,t \<turnstile>jmm' \<langle>e, (shr s', xs)\<rangle> -ta''\<rightarrow> \<langle>e'', (h'', xs'')\<rangle>"
      and aok'': "jmm'.red_mthr.if.actions_ok s' t ta''"
      and sc'': "ta_seq_consist P ?vs' (llist_of (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>))"
      and eq'': "eq_upto_seq_inconsist P (map NormalAction \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (map NormalAction \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>) ?vs'"
      by blast

    from n\<tau> x x' have "\<not> jmm'.\<tau>move0 P (shr s') e \<or> ta \<noteq> \<epsilon>"
      by(auto intro: jmm'.red_mthr.init_fin_\<tau>move.intros)
    with red x x' have "\<not> jmm'.\<tau>move0 P (shr s') e"
      by(auto dest: jmm'.red_\<tau>_taD[where extTA="extTA2J P", simplified])
    hence n\<tau>'': "\<not> jmm'.\<tau>MOVE P ((e, xs), shr s') ta'' ((e'', xs''), h'')" by auto 

    let ?x' = "(Running, e'', xs'')"
    let ?ta' = "convert_TA_initial (convert_obs_initial ta'')"
    from red'' have "jmm'.red_mthr.init_fin P P t (x, shr s') ?ta' (?x', h'')"
      unfolding x by -(rule jmm'.red_mthr.init_fin.NormalAction, simp)
    moreover from aok'' have "jmm'.red_mthr.if.actions_ok s' t ?ta'" by simp
    moreover from n\<tau>'' have "\<not> jmm'.red_mthr.init_fin_\<tau>move P (x, shr s') ?ta' (?x', h'')"
      unfolding x by auto
    moreover from sc'' have "ta_seq_consist P ?vs' (llist_of \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub>)" by simp
    moreover from eq'' have "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub> ?vs'" unfolding ta by simp
    ultimately show ?thesis by blast
  qed
qed

lemma JMM_inst: 
  assumes wf_prog: "wf_J_prog P"
  and minimal: "jmm'_heap_ops_typeof_minimal P"
  and start_heap: "jmm'.start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns, body) in D"
  and conf: "P,jmm'.start_heap \<turnstile>jmm' vs [:\<le>] Ts"
  shows "executions (lappend (llist_of (lift_start_obs jmm'.start_tid jmm'.start_heap_obs)) ` 
                     jmm'.red_mthr.if.\<E> P P (init_fin_lift_state Running (jmm'.J_start_state P C M vs)))
                    P"
  (is "executions ?E _")
proof -
  let ?wt_ok = "init_fin_lift_inv (\<lambda>ET t (e, x) m. jmm'.sconf_type_ok P ET e m x)"
  let ?thread_ok = "init_fin_lift (\<lambda>t x m. P,m \<turnstile>jmm' t \<surd>t)"
  let ?start_state = "init_fin_lift_state Running (jmm'.J_start_state P C M vs)"
  let ?ET_start = "jmm'.J_sconf_type_ET_start P C M"

  interpret wt_red!: lifting_inv
    final_expr
    "jmm'.mred P P"
    convert_RA
    "\<lambda>t x m. P,m \<turnstile>jmm' t \<surd>t"
    "\<lambda>ET t (e, x) m. jmm'.sconf_type_ok P ET e m x"
    using wf_prog by(rule jmm'.lifting_inv_sconf_subject_ok)

  interpret wt_red!: if_lifting_inv
    final_expr
    "jmm'.mred P P"
    convert_RA
    "\<lambda>t x m. P,m \<turnstile>jmm' t \<surd>t"
    "\<lambda>ET t (e, x) m. jmm'.sconf_type_ok P ET e m x"
    by(unfold_locales)

  interpret wt_if!: \<tau>lifting_inv
    jmm'.red_mthr.init_fin_final
    "jmm'.red_mthr.init_fin P P"
    "map NormalAction \<circ> convert_RA" 
    "jmm'.red_mthr.init_fin_\<tau>move P"
    "\<lambda>t ((s, x), m). wfs t (x, m)"
    "?thread_ok"
    "?wt_ok"
    for wfs
    by unfold_locales

  interpret J_jmm!: executions_aux ?E P
    by(rule jmm'.JMM_inst_aux) fact+

  interpret Jinja_executions_aux
    final_expr
    "jmm'.mred P P"
    "jmm'.\<tau>MOVE P"
    "lift_start_obs jmm'.start_tid jmm'.start_heap_obs"
    "?start_state" P
    by unfold_locales (clarsimp simp add: jmm'.start_heap_obs_not_Read)

  from wf_prog start_heap sees conf
  show ?thesis by(rule executions[OF cut_and_update])
qed

end