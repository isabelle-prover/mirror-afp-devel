(*  Title:      JinjaThreads/J/Deadlocked.thy
    Author:     Andreas Lochbihler
*)

header{* \isaheader{Preservation of Deadlock} *}

theory Deadlocked imports ProgressThreaded begin

context J_progress begin

lemma assumes wf: "wf_prog wf_md P"
  and hconf: "hconf h"
  shows red_Lock_hext:
  "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l); hext (hp s) h \<rbrakk>
  \<Longrightarrow> \<exists>ta' e' s'. convert_extTA extNTA,P,t \<turnstile> \<langle>e, (h, lcl s)\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle> \<and>
                 collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>} = {t. Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>}"
  and reds_Lock_hext:
  "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l); hext (hp s) h \<rbrakk>
  \<Longrightarrow> \<exists>ta' es' s'. convert_extTA extNTA,P,t \<turnstile> \<langle>es, (h, lcl s)\<rangle> [-ta'\<rightarrow>] \<langle>es', s'\<rangle> \<and>
                  collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>} = {t. Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>}"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  from `hext (hp s) h` `typeof_addr (hp s) a = \<lfloor>T\<rfloor>` have "typeof_addr h a = \<lfloor>T\<rfloor>"
    by-(rule typeof_addr_hext_mono)
  moreover
  from red_external_Lock_hext[OF wf `P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>` _ `hp s \<unlhd> h` hconf, of l]
    `Lock \<in> set (\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)` `ta' = convert_extTA extNTA ta`
  obtain va' ta'' h''' where "P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -ta''\<rightarrow>ext \<langle>va',h'''\<rangle>" "collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = collect_locks \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>"
    "{t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>} = {t. Join t \<in> set \<lbrace>ta''\<rbrace>\<^bsub>c\<^esub>}" by auto
  ultimately show ?case using `ta' = convert_extTA extNTA ta` `e' = extRet2J (addr a\<bullet>M(map Val vs)) va` `s' = (h', lcl s)`
    `is_external_call P T M` by(fastsimp intro: red_reds.RedCallExternal simp del: split_paired_Ex)
next
  case CallParams thus ?case by(fastsimp intro: red_reds.CallParams)
qed(fastsimp intro: red_reds.intros simp add: ta_upd_simps)+

lemma red_Join_hext:
  "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Join t' \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>; hext (hp s) h \<rbrakk>
  \<Longrightarrow> convert_extTA extNTA,P,t \<turnstile> \<langle>e, (h, lcl s)\<rangle> -ta\<rightarrow> \<langle>e', (h, lcl s')\<rangle>"

  and reds_Join_hext:
  "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; Join t' \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>; hext (hp s) h \<rbrakk>
  \<Longrightarrow> convert_extTA extNTA,P,t \<turnstile> \<langle>es, (h, lcl s)\<rangle> [-ta\<rightarrow>] \<langle>es', (h, lcl s')\<rangle>"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  from `typeof_addr (hp s) a = \<lfloor>T\<rfloor>` `hext (hp s) h` have "typeof_addr h a = \<lfloor>T\<rfloor>"
    by(blast intro: typeof_addr_hext_mono)
  moreover from `P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>` `Join t' \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>` `hext (hp s) h`
    `ta' = convert_extTA extNTA ta` `typeof_addr (hp s) a = \<lfloor>T\<rfloor>`
  have "P,t \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -ta\<rightarrow>ext \<langle>va,h\<rangle>" by(auto intro: red_external_Join_hext)
  ultimately show ?case using `ta' = convert_extTA extNTA ta` `e' = extRet2J (addr a\<bullet>M(map Val vs)) va` `s' = (h', lcl s)`
    `is_external_call P T M` by(auto intro: red_reds.RedCallExternal)
qed(fastsimp intro: red_reds.intros simp add: ta_upd_simps)+

lemma red_wt_hconf_hext:
  assumes wf: "wf_J_prog P"
  and hconf: "hconf H"
  and tconf: "P,H \<turnstile> t \<surd>t"
  shows "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,E,H \<turnstile> e : T; hext H (hp s) \<rbrakk>
        \<Longrightarrow> \<exists>ta' e' s'. convert_extTA extNTA,P,t \<turnstile> \<langle>e, (H, lcl s)\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle> \<and>
           collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>} = {t. Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>}"
  and "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; P,E,H \<turnstile> es [:] Ts; hext H (hp s) \<rbrakk>
        \<Longrightarrow> \<exists>ta' es' s'. convert_extTA extNTA,P,t \<turnstile> \<langle>es, (H, lcl s)\<rangle> [-ta'\<rightarrow>] \<langle>es', s'\<rangle> \<and> 
                        collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>} = {t. Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>}"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case (RedNew h C h' a l)
  obtain H' ao where "new_obj H C = (H', ao)" by(cases "new_obj H C")
  with RedNew show ?case
    by(cases ao)(fastsimp simp add: ta_upd_simps intro: RedNewFail red_reds.RedNew)+
next
  case (RedNewFail h C h' l)
  obtain H' ao where "new_obj H C = (H', ao)" by(cases "new_obj H C")
  with RedNewFail show ?case
    by(cases ao)(fastsimp simp add: ta_upd_simps intro: red_reds.RedNewFail RedNew)+
next 
  case NewArrayRed thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedNewArray i h T h' a l E T')
  obtain H' ao where "new_arr H T (nat (sint i)) = (H', ao)" by(cases "new_arr H T (nat (sint i))")
  with RedNewArray show ?case
    by(cases ao)(fastsimp simp add: ta_upd_simps intro: red_reds.RedNewArray RedNewArrayFail)+
next
  case RedNewArrayNegative thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedNewArrayFail i h T h' l E T')
  obtain H' ao where "new_arr H T (nat (sint i)) = (H', ao)" by(cases "new_arr H T (nat (sint i))")
  with RedNewArrayFail show ?case
    by(cases ao)(fastsimp simp add: ta_upd_simps intro: RedNewArray red_reds.RedNewArrayFail)+
next
  case CastRed thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedCast s v U T E T')
  from `P,E,H \<turnstile> Cast T (Val v) : T'` show ?case
  proof(rule WTrt_elim_cases)
    fix T''
    assume wt: "P,E,H \<turnstile> Val v : T''" "T = T'"
    thus ?thesis
      by(cases "P \<turnstile> T'' \<le> T")(fastsimp intro: red_reds.RedCast red_reds.RedCastFail)+
  qed
next 
  case (RedCastFail s v U T E T')
  from `P,E,H \<turnstile> Cast T (Val v) : T'` 
  obtain T'' where "P,E,H \<turnstile> Val v : T''" "T = T'" by auto
  thus ?case
    by(cases "P \<turnstile> T'' \<le> T")(fastsimp intro: red_reds.RedCast red_reds.RedCastFail)+
next
  case InstanceOfRed thus ?case by(fastsimp intro: red_reds.intros)
next
  case RedInstanceOf thus ?case by auto((rule exI conjI red_reds.RedInstanceOf)+, auto)
next
  case BinOpRed1 thus ?case by(fastsimp intro: red_reds.intros)
next
  case BinOpRed2 thus ?case by(fastsimp intro: red_reds.intros)
next
  case RedBinOp thus ?case by(fastsimp intro: red_reds.intros)
next
  case RedVar thus ?case by(fastsimp intro: red_reds.intros)
next
  case LAssRed thus ?case by(fastsimp intro: red_reds.intros)
next
  case RedLAss thus ?case by(fastsimp intro: red_reds.intros)
next
  case AAccRed1 thus ?case by(fastsimp intro: red_reds.intros)
next
  case AAccRed2 thus ?case by(fastsimp intro: red_reds.intros)
next
  case RedAAccNull thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedAAccBounds s a T i E T')
  from `P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> : T'` 
  have wt: "P,E,H \<turnstile> addr a : T'\<lfloor>\<rceil>"
    by(auto dest: typeof_addr_eq_Some_conv)
  hence Ha: "typeof_addr H a = \<lfloor>Array T'\<rfloor>" by auto
  with `hext H (hp s)` `typeof_addr (hp s) a = \<lfloor>T\<lfloor>\<rceil>\<rfloor>`
  have si': "array_length H a = array_length (hp s) a"
    by(auto dest: hext_arrD)
  with Ha `i <s 0 \<or> int (array_length (hp s) a) \<le> sint i` show ?case
    by(fastsimp intro: red_reds.RedAAccBounds)
next 
  case (RedAAcc s a T i v E T')
  from `P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> : T'` 
  have wt: "P,E,H \<turnstile> addr a : T'\<lfloor>\<rceil>"
    by(auto dest: typeof_addr_eq_Some_conv)
  hence Ha: "typeof_addr H a = \<lfloor>Array T'\<rfloor>" by(auto)
  with `hext H (hp s)` `typeof_addr (hp s) a = \<lfloor>Array T\<rfloor>`
  have si': "array_length H a = array_length (hp s) a" and [simp]: "T' = T"
    by(auto dest: hext_arrD)
  with `0 <=s i` `sint i < int (array_length (hp s) a)`
  have "nat (sint i) < array_length (hp s) a"
    by(metis nat_less_iff si' sint_0 word_sle_def)
  with Ha si' have "P,H \<turnstile> a@ACell (nat (sint i)) : T"
    by(auto intro: addr_loc_type.intros)
  from heap_read_total[OF hconf this]
  obtain v where "heap_read H a (ACell (nat (sint i))) v" by blast
  with si' Ha `0 <=s i` `sint i < int (array_length (hp s) a)` show ?case
    by(fastsimp intro: red_reds.RedAAcc simp add: ta_upd_simps)
next
  case AAssRed1 thus ?case by(fastsimp intro: red_reds.intros)
next
  case AAssRed2 thus ?case by(fastsimp intro: red_reds.intros)
next
  case AAssRed3 thus ?case by(fastsimp intro: red_reds.intros)
next
  case RedAAssNull thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedAAssBounds s a T i e E T')
  from `P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> := Val e : T'` 
  obtain T'' where wt: "P,E,H \<turnstile> addr a : T''\<lfloor>\<rceil>"
    by(auto dest: typeof_addr_eq_Some_conv)
  hence Ha: "typeof_addr H a = \<lfloor>Array T''\<rfloor>" by(auto)
  with `typeof_addr (hp s) a = \<lfloor>T\<lfloor>\<rceil>\<rfloor>` `H \<unlhd> hp s`
  have si': "array_length H a = array_length (hp s) a" and [simp]: "T'' = T"
    by(auto dest: hext_arrD)
  with `i <s 0 \<or> int (array_length (hp s) a) \<le> sint i` Ha show ?case
    by(fastsimp intro: red_reds.RedAAssBounds)
next
  case (RedAAssStore s a T i w U E T')
  from `P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> := Val w : T'` 
  obtain T'' T''' where wt: "P,E,H \<turnstile> addr a : T''\<lfloor>\<rceil>"
    and wtw: "P,E,H \<turnstile> Val w : T'''"
    by(auto dest: typeof_addr_eq_Some_conv)
  hence Ha: "typeof_addr H a = \<lfloor>Array T''\<rfloor>" by(auto)
  with `H \<unlhd> hp s` `typeof_addr (hp s) a = \<lfloor>Array T\<rfloor>`
  have si': "array_length H a = array_length (hp s) a" and T'': "T'' = T"
    by(auto dest: hext_arrD)
  from `typeof\<^bsub>hp s\<^esub> w = \<lfloor>U\<rfloor>` wtw `H \<unlhd> hp s` have "typeof\<^bsub>H\<^esub> w = \<lfloor>U\<rfloor>" 
    by(auto dest: type_of_hext_type_of)
  with Ha `0 <=s i` `sint i < int (array_length (hp s) a)` `\<not> P \<turnstile> U \<le> T` T'' si' show ?case
    by(fastsimp intro: red_reds.RedAAssStore)
next
  case (RedAAss h a T i w U h' l E T')
  from `P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> := Val w : T'`
  obtain T'' T''' where wt: "P,E,H \<turnstile> addr a : T''\<lfloor>\<rceil>"
      and wtw: "P,E,H \<turnstile> Val w : T'''"
    by(auto dest: typeof_addr_eq_Some_conv)
  hence Ha: "typeof_addr H a = \<lfloor>Array T''\<rfloor>" by(auto)
  with `H \<unlhd> hp (h, l)` `typeof_addr h a = \<lfloor>Array T\<rfloor>`
  have si': "array_length H a = array_length h a" and T'': "T'' = T"
    by(auto dest: hext_arrD)
  from `0 <=s i` `sint i < int (array_length h a)`
  have "nat (sint i) < array_length h a"
    by (metis nat_less_iff si' sint_0 word_sle_def)
  with si' T'' Ha have "P,H \<turnstile> a@ACell (nat (sint i)) : T"
    by(auto intro: addr_loc_type.intros)
  from heap_write_total[OF this, of w]
  obtain H' where "heap_write H a (ACell (nat (sint i))) w H'" ..
  moreover from `typeof\<^bsub>h\<^esub> w = \<lfloor>U\<rfloor>` wtw `H \<unlhd> hp (h, l)` have "typeof\<^bsub>H\<^esub> w = \<lfloor>U\<rfloor>" 
    by(auto dest: type_of_hext_type_of)
  ultimately show ?case using `0 <=s i` `sint i < int (array_length h a)` Ha T'' `P \<turnstile> U \<le> T` si'
    by(fastsimp simp del: split_paired_Ex intro: red_reds.RedAAss)
next
  case ALengthRed thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedALength h a T l E T')
  from `P,E,H \<turnstile> addr a\<bullet>length : T'`
  obtain T'' where [simp]: "T' = Integer"
      and wta: "P,E,H \<turnstile> addr a : T''\<lfloor>\<rceil>"
    by(auto dest: typeof_addr_eq_Some_conv)
  hence "typeof_addr H a = \<lfloor>Array T''\<rfloor>" by(auto)
  thus ?case by(fastsimp intro: red_reds.RedALength)
next
  case RedALengthNull show ?case by(fastsimp intro: red_reds.RedALengthNull)
next
  case FAccRed thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedFAcc s a D F v E T)
  from `P,E,H \<turnstile> addr a\<bullet>F{D} : T` obtain C'
    where wt: "P,E,H \<turnstile> addr a : Class C'"
      and has: "P \<turnstile> C' has F:T in D"
    by(auto dest: typeof_addr_eq_Some_conv)
  hence Ha: "typeof_addr H a = \<lfloor>Class C'\<rfloor>" by(auto)
  with `P \<turnstile> C' has F:T in D` have "P,H \<turnstile> a@CField D F : T"
    by(auto intro: addr_loc_type.intros)
  from heap_read_total[OF hconf this]
  obtain v where "heap_read H a (CField D F) v" by blast
  thus ?case by(fastsimp intro: red_reds.RedFAcc simp add: ta_upd_simps)
next
  case RedFAccNull thus ?case by(fastsimp intro: red_reds.intros)
next
  case FAssRed1 thus ?case by(fastsimp intro: red_reds.intros)
next
  case FAssRed2 thus ?case by(fastsimp intro: red_reds.intros)
next
  case RedFAssNull thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedFAss h a D F v h' l E T)
  from `P,E,H \<turnstile> addr a\<bullet>F{D} := Val v : T` obtain C' T' T2
    where wt: "P,E,H \<turnstile> addr a : Class C'"
      and has: "P \<turnstile> C' has F:T' in D"
      and wtv: "P,E,H \<turnstile> Val v : T2"
      and T2T: "P \<turnstile> T2 \<le> T'"
    by(auto dest: typeof_addr_eq_Some_conv)
  moreover from wt have Ha: "typeof_addr H a = \<lfloor>Class C'\<rfloor>" by(auto)
  with has have "P,H \<turnstile> a@CField D F : T'" by(auto intro: addr_loc_type.intros)
  from heap_write_total[OF this, of v]
  obtain h' where "heap_write H a (CField D F) v h'" ..
  thus ?case by(fastsimp intro: red_reds.RedFAss)
next
  case CallObj thus ?case by(fastsimp intro: red_reds.intros)
next
  case CallParams thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedCall s a C M Ts T pns body D vs E T')
  from `P,E,H \<turnstile> addr a\<bullet>M(map Val vs) : T'` show ?case
  proof(rule WTrt_elim_cases)
    fix C' Ts' pns' body' D' Ts''
    assume wta: "P,E,H \<turnstile> addr a : Class C'"
      and sees: "P \<turnstile> C' sees M: Ts'\<rightarrow>T' = (pns', body') in D'"
      and wtes: "P,E,H \<turnstile> map Val vs [:] Ts''"
      and widens: "P \<turnstile> Ts'' [\<le>] Ts'"
      and nexc: "\<not> is_external_call P (Class C') M"
    from wta have Ha: "typeof_addr H a = \<lfloor>Class C'\<rfloor>" by(auto)
    moreover from wtes have "length vs = length Ts''"
      by(auto intro: map_eq_imp_length_eq')
    moreover from widens have "length Ts'' = length Ts'"
      by(auto dest: widens_lengthD)
    moreover from sees wf have "wf_mdecl wf_J_mdecl P D' (M, Ts', T', pns', body')"
      by(auto intro: sees_wf_mdecl)
    hence "length pns' = length Ts'"
      by(simp add: wf_mdecl_def)
    moreover from `typeof_addr (hp s) a = \<lfloor>Class C\<rfloor>` `H \<unlhd> hp s` Ha
    have "C = C'" by(auto dest: hext_objD)
    ultimately show ?thesis using sees nexc
      by(fastsimp intro: red_reds.RedCall)
  next
    fix Ts
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(auto dest: typeof_addr_eq_Some_conv)
    thus ?thesis ..
  next
    fix T Ts' Ts''
    assume "P \<turnstile> T\<bullet>M(Ts'') :: T'" "P,E,H \<turnstile> addr a : T" "P,E,H \<turnstile> map Val vs [:] Ts'" "P \<turnstile> Ts' [\<le>] Ts''"
    with `typeof_addr (hp s) a = \<lfloor>Class C\<rfloor>` `H \<unlhd> hp s` have "is_external_call P (Class C) M"
      by(auto dest!: typeof_addr_hext_mono intro: external_WT_is_external_call)
    then show ?case using `\<not> is_external_call P (Class C) M` by simp
  qed
next
  case (RedCallExternal s a U M vs ta va h' ta' e' s')
  from `P,E,H \<turnstile> addr a\<bullet>M(map Val vs) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C ts pns body D Ts'
    assume "P,E,H \<turnstile> addr a : Class C" "\<not> is_external_call P (Class C) M"
    with `is_external_call P U M` `typeof_addr (hp s) a = \<lfloor>U\<rfloor>` `hext H (hp s)` have False
      by(auto dest: hext_objD)
    thus ?thesis ..
  next
    fix Ts
    assume "P,E,H \<turnstile> addr a : NT" thus ?thesis by(auto dest: typeof_addr_eq_Some_conv)
  next
    fix T' Ts Ts'
    assume wta: "P,E,H \<turnstile> addr a : T'" and wtvs: "P,E,H \<turnstile> map Val vs [:] Ts"
      and wtext: "P \<turnstile> T'\<bullet>M(Ts') :: T" "P \<turnstile> Ts [\<le>] Ts'"
    from wta `typeof_addr (hp s) a = \<lfloor>U\<rfloor>` `hext H (hp s)` have [simp]: "T' = U"
      by(auto dest: typeof_addr_hext_mono)
    with wta have "typeof_addr H a = \<lfloor>U\<rfloor>" by simp
    hence "P,H \<turnstile> a\<bullet>M(vs) : T" using wtext `P,E,H \<turnstile> map Val vs [:] Ts` by(auto intro: external_WT'.intros)
    from red_external_wt_hconf_hext[OF wf `P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>` `H \<unlhd> hp s` this tconf hconf]
      wta `is_external_call P U M` `ta' = convert_extTA extNTA ta` `e' = extRet2J (addr a\<bullet>M(map Val vs)) va` `s' = (h', lcl s)`
    show ?thesis by(fastsimp intro: red_reds.RedCallExternal simp del: split_paired_Ex)
  qed
next
  case RedCallNull thus ?case by(fastsimp intro: red_reds.intros)
next
  case (BlockRed e h l V vo ta e' h' l' T E T')
  note IH = `\<And>E T. \<lbrakk>P,E,H \<turnstile> e : T; hext H (hp (h, l(V := vo)))\<rbrakk>
              \<Longrightarrow> \<exists>ta' e' s'.
        convert_extTA
         extNTA,P,t \<turnstile> \<langle>e,(H, lcl (h, l(V := vo)))\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle> \<and>
        collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and>
        {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>} = {t. Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>}`
  from IH[of "E(V \<mapsto> T)" T'] `P,E,H \<turnstile> {V:T=vo; e} : T'` `hext H (hp (h, l))`
  show ?case by(fastsimp dest: red_reds.BlockRed)
next
  case RedBlock thus ?case by(fastsimp intro: red_reds.intros)
next
  case SynchronizedRed1 thus ?case by(fastsimp intro: red_reds.intros)
next
  case SynchronizedNull thus ?case by(fastsimp intro: red_reds.intros)
next
  case LockSynchronized thus ?case by(fastsimp intro: red_reds.intros)
next
  case SynchronizedRed2 thus ?case by(fastsimp intro: red_reds.intros)
next
  case UnlockSynchronized thus ?case by(fastsimp intro: red_reds.intros)
next
  case SeqRed thus ?case by(fastsimp intro: red_reds.intros)
next
  case RedSeq thus ?case by(fastsimp intro: red_reds.intros)
next
  case CondRed thus ?case by(fastsimp intro: red_reds.intros)
next
  case RedCondT thus ?case by(fastsimp intro: red_reds.intros)
next
  case RedCondF thus ?case by(fastsimp intro: red_reds.intros)
next
  case RedWhile thus ?case by(fastsimp intro: red_reds.intros)
next
  case ThrowRed thus ?case by(fastsimp intro: red_reds.intros)
next
  case RedThrowNull thus ?case by(fastsimp intro: red_reds.intros)
next
  case TryRed thus ?case by(fastsimp intro: red_reds.intros)
next
  case RedTry thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedTryCatch s a D C V e2 E T)
  from `P,E,H \<turnstile> try Throw a catch(C V) e2 : T`
  obtain T' where "P,E,H \<turnstile> addr a : T'" by auto
  with `typeof_addr (hp s) a = \<lfloor>Class D\<rfloor>` `hext H (hp s)`
  have Ha: "typeof_addr H a = \<lfloor>Class D\<rfloor>"
    by(auto dest: typeof_addr_hext_mono)
  with `P \<turnstile> D \<preceq>\<^sup>* C` show ?case
    by(fastsimp intro: red_reds.RedTryCatch)
next
  case (RedTryFail s a D C V e2 E T)
  from `P,E,H \<turnstile> try Throw a catch(C V) e2 : T`
  obtain T' where "P,E,H \<turnstile> addr a : T'" by auto
  with `typeof_addr (hp s) a = \<lfloor>Class D\<rfloor>` `hext H (hp s)`
  have Ha: "typeof_addr H a = \<lfloor>Class D\<rfloor>" 
    by(auto dest: typeof_addr_hext_mono)
  with `\<not> P \<turnstile> D \<preceq>\<^sup>* C` show ?case
    by(fastsimp intro: red_reds.RedTryFail)
next
  case ListRed1 thus ?case by(fastsimp intro: red_reds.intros)
next
  case ListRed2 thus ?case by(fastsimp intro: red_reds.intros)
next
  case NewArrayThrow thus ?case by(fastsimp intro: red_reds.intros)
next
  case CastThrow thus ?case by(fastsimp intro: red_reds.intros)
next
  case InstanceOfThrow thus ?case by(fastsimp intro: red_reds.intros)
next
  case BinOpThrow1 thus ?case by(fastsimp intro: red_reds.intros)
next
  case BinOpThrow2 thus ?case by(fastsimp intro: red_reds.intros)
next
  case LAssThrow thus ?case by(fastsimp intro: red_reds.intros)
next
  case AAccThrow1 thus ?case by(fastsimp intro: red_reds.intros)
next
  case AAccThrow2 thus ?case by(fastsimp intro: red_reds.intros)
next
  case AAssThrow1 thus ?case by(fastsimp intro: red_reds.intros)
next
  case AAssThrow2 thus ?case by(fastsimp intro: red_reds.intros)
next
  case AAssThrow3 thus ?case by(fastsimp intro: red_reds.intros)
next
  case ALengthThrow thus ?case by(fastsimp intro: red_reds.intros)
next
  case FAccThrow thus ?case by(fastsimp intro: red_reds.intros)
next
  case FAssThrow1 thus ?case by(fastsimp intro: red_reds.intros)
next 
  case FAssThrow2 thus ?case by(fastsimp intro: red_reds.intros)
next
  case CallThrowObj thus ?case by(fastsimp intro: red_reds.intros)
next
  case CallThrowParams thus ?case by(fastsimp intro: red_reds.intros)
next
  case BlockThrow thus ?case by(fastsimp intro: red_reds.intros)
next
  case SynchronizedThrow1 thus ?case by(fastsimp intro: red_reds.intros)
next
  case SynchronizedThrow2 thus ?case by(fastsimp intro: red_reds.intros)
next
  case SeqThrow thus ?case by(fastsimp intro: red_reds.intros)
next
  case CondThrow thus ?case by(fastsimp intro: red_reds.intros)
next
  case ThrowThrow thus ?case by(fastsimp intro: red_reds.intros)
qed

lemma can_lock_devreserp:
  "\<lbrakk> wf_J_prog P; red_mthr.can_sync P t (e, l) h' L; P,E,h \<turnstile> e : T; P,h \<turnstile> t \<surd>t; hconf h; h \<unlhd> h' \<rbrakk> 
  \<Longrightarrow> red_mthr.can_sync P t (e, l) h L"
apply(erule red_mthr.can_syncE)
apply(clarsimp)
apply(drule red_wt_hconf_hext, assumption+)
 apply(simp)
apply(fastsimp intro!: red_mthr.can_syncI)
done

lemma can_sync_preserved:
  assumes "wf_prog wf_md P"
  and "red_mthr.can_sync P t (e, l) h LT"
  and "hext h h'"
  and "hconf h'"
  and "P,h' \<turnstile> t \<surd>t"
  and "LT \<noteq> {}"
  shows "red_mthr.must_sync P t (e, l) h'"
using assms
apply -
apply(rule red_mthr.must_syncI)
apply(erule red_mthr.can_syncE)
apply(clarsimp)
apply(auto simp add: collect_locks_def ta_upd_simps)
apply(drule (2) red_Lock_hext)
   apply(simp)
  apply(simp)
 apply simp
apply(drule red_Join_hext)
   apply(simp)
  apply(simp)
 apply simp
apply fastsimp
done

end

context J_typesafe begin

lemma preserve_deadlocked:
  assumes wf: "wf_J_prog P"
  and st: "sconf_type_ts_ok Es (thr S) (shr S)"
  and da: "def_ass_ts_ok (thr S) (shr S)"
  and lto: "lock_thread_ok (locks S) (thr S)"
  and wto: "wset_thread_ok (wset S) (thr S)"
  and tc: "thread_conf P (thr S) (shr S)"
  shows "preserve_deadlocked final_expr (mred P) S"
proof -
  { fix tta s t' ta' s' t x ln
    assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>* s"
      and red: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow> s'"
      and tst: "thr s t = \<lfloor>(x, ln)\<rfloor>"
    obtain e l where x [simp]: "x = (e, l)" by(cases x, auto)
    let ?Es' = "upd_invs Es (\<lambda>ET t (e, x) m. sconf_type_ok ET e m x) (\<down>map (thr_a \<circ> snd) tta\<down>)"
    from st Red tc have st': "sconf_type_ts_ok ?Es' (thr s) (shr s)"
      by(auto dest: lifting_inv.RedT_invariant[OF lifting_inv_sconf_subject_ok, OF wf])
    with tst obtain E T where Est: "?Es' t = \<lfloor>(E, T)\<rfloor>" 
      and stt: "sconf_type_ok (E, T) e (shr s) l" by(auto dest!: ts_invD)
    from stt have hconf: "hconf (shr s)"
      by(simp add: sconf_type_ok_def sconf_def)
    from stt obtain T' where wte: "P,E,shr s \<turnstile> e : T'"
      by(auto simp add: sconf_type_ok_def type_ok_def)
    from red have hext: "hext (shr s) (shr s')"
      by(cases s, cases s')(auto dest: redT_hext_incr)
    from Red tc have tc': "thread_conf P (thr s) (shr s)" by(rule red_tconf.RedT_preserves)
    from tst red obtain x' ln' where ts't: "thr s' t = \<lfloor>(x', ln')\<rfloor>"
      by(cases "thr s' t")(cases s, cases s', auto dest: red_mthr.redT_thread_not_disappear)
    with lifting_inv.redT_invariant[OF lifting_inv_sconf_subject_ok, OF wf red st' tc'] Est
    obtain E' T' where "sconf_type_ok (E', T') (fst x') (shr s') (snd x')"
      by(auto dest: ts_invD)
    hence hconf': "hconf (shr s')" by(simp add: sconf_type_ok_def sconf_def)
    from tc' tst have tct: "P,shr s \<turnstile> t \<surd>t" by(auto dest: ts_okD)
    from red tc' have "thread_conf P (thr s') (shr s')" by(rule red_tconf.redT_preserves)
    with ts't have tct': "P,shr s' \<turnstile> t \<surd>t" by(auto dest: ts_okD)

    { fix LT
      assume "red_mthr.can_sync P t x (shr s) LT"
        and LT: "LT \<noteq> {}"
      with hext hconf' LT tct' have "red_mthr.must_sync P t (e, l) (shr s')"
	by(auto intro: can_sync_preserved[OF wf])
      hence "red_mthr.must_sync P t x (shr s')" by simp }
    note ml = this
    { fix LT
      assume "red_mthr.can_sync P t x (shr s') LT"
      with wf wte hext hconf tct have "red_mthr.can_sync P t (e, l) (shr s) LT"
        by(auto intro: can_lock_devreserp)
      hence "\<exists>LT'\<subseteq>LT. red_mthr.can_sync P t x (shr s) LT'" by(auto) }
    note this ml }
  with lto wto show ?thesis by(unfold_locales)
qed

theorem preserve_deadlock_start:
  assumes wf: "wf_J_prog P"
  and start_heap: "start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T=(pns, body) in D"
  and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
  shows "preserve_deadlocked final_expr (mred P) (J_start_state P C M vs)"
using wf
apply(rule preserve_deadlocked)
    apply(rule sconf_type_ts_ok_J_start_state[OF wf start_heap sees conf])
   apply(rule def_ass_ts_ok_J_start_state[OF wf sees])
   apply(rule list_all2_lengthD[OF conf])
  apply(rule lock_thread_ok_start_state)
 apply(rule wset_thread_ok_start_state)
apply(rule thread_conf_start_state[OF start_heap])
done

end

end
