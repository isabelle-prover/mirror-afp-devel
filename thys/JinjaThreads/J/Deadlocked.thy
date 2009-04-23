(*  Title:      JinjaThreads/J/Deadlocked.thy
    Author:     Andreas Lochbihler
*)

header{* Preservation of Deadlock *}

theory Deadlocked imports ProgressThreaded begin

lemma red_Lock_hext:
  "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l); hext (hp s) h \<rbrakk>
  \<Longrightarrow> convert_extTA extNTA,P \<turnstile> \<langle>e, (h, lcl s)\<rangle> -ta\<rightarrow> \<langle>e', (h, lcl s')\<rangle>"
  and reds_Lock_hext:
  "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l); hext (hp s) h \<rbrakk>
  \<Longrightarrow> convert_extTA extNTA,P \<turnstile> \<langle>es, (h, lcl s)\<rangle> [-ta\<rightarrow>] \<langle>es', (h, lcl s')\<rangle>"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  from `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>T\<rfloor>` `hext (hp s) h` have "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>T\<rfloor>"
    by(auto split: heapobj.splits dest: hext_objD hext_arrD)
  moreover from `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>` `Lock \<in> set (\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)` `hext (hp s) h` `ta' = convert_extTA extNTA ta`
  have "P \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -ta\<rightarrow>ext \<langle>va,h\<rangle>" by(auto intro: red_external_Lock_hext)
  ultimately show ?case using `ta' = convert_extTA extNTA ta` `e' = extRet2J va` `s' = (h', lcl s)`
    `is_external_call P T M (length vs)` by(auto intro: red_reds.RedCallExternal)
qed(fastsimp intro: red_reds.intros dest: hext_objarrD)+

lemma red_Join_hext:
  "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>; hext (hp s) h \<rbrakk>
  \<Longrightarrow> convert_extTA extNTA,P \<turnstile> \<langle>e, (h, lcl s)\<rangle> -ta\<rightarrow> \<langle>e', (h, lcl s')\<rangle>"

  and reds_Join_hext:
  "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>; hext (hp s) h \<rbrakk>
  \<Longrightarrow> convert_extTA extNTA,P \<turnstile> \<langle>es, (h, lcl s)\<rangle> [-ta\<rightarrow>] \<langle>es', (h, lcl s')\<rangle>"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  from `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>T\<rfloor>` `hext (hp s) h` have "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>T\<rfloor>"
    by(auto split: heapobj.splits dest: hext_objD hext_arrD)
  moreover from `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>` `Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>` `hext (hp s) h`
    `ta' = convert_extTA extNTA ta` `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>T\<rfloor>`
  have "P \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -ta\<rightarrow>ext \<langle>va,h\<rangle>" by(auto intro: red_external_Join_hext)
  ultimately show ?case using `ta' = convert_extTA extNTA ta` `e' = extRet2J va` `s' = (h', lcl s)`
    `is_external_call P T M (length vs)` by(auto intro: red_reds.RedCallExternal)
qed(fastsimp intro: red_reds.intros)+


lemma red_Lock_wth:
  "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l); P,E,h \<turnstile> e : T; hext h (hp s) \<rbrakk>
  \<Longrightarrow> convert_extTA extNTA,P \<turnstile> \<langle>e, (h, lcl s)\<rangle> -ta\<rightarrow> \<langle>e', (h, lcl s')\<rangle>"

  and reds_Lock_wth:
  "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>\<^sub>f l); P,E,h \<turnstile> es [:] Ts; hext h (hp s) \<rbrakk>
  \<Longrightarrow> convert_extTA extNTA,P \<turnstile> \<langle>es, (h, lcl s)\<rangle> [-ta\<rightarrow>] \<langle>es', (h, lcl s')\<rangle>"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case (RedCallExternal s a U M vs ta va h' ta' e' s')
  from `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>U\<rfloor>` `P,E,h \<turnstile> addr a\<bullet>M(map Val vs) : T` `hext h (hp s)`
  have "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>U\<rfloor>" by(fastsimp split: heapobj.split_asm dest: hext_objD hext_arrD)
  moreover with `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>` `P,E,h \<turnstile> addr a\<bullet>M(map Val vs) : T` 
    `Lock \<in> set (\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>\<^sub>f l)` `hext h (hp s)` `ta' = convert_extTA extNTA ta` `is_external_call P U M (length vs)`
  have "P \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -ta\<rightarrow>ext \<langle>va,h\<rangle>" by(auto intro: red_external_Lock_wth split: heapobj.split_asm)
  ultimately show ?case using `is_external_call P U M (length vs)` `ta' = convert_extTA extNTA ta`
    `e' = extRet2J va` `s' = (h', lcl s)` by(auto intro: red_reds.RedCallExternal)
next
  case (LockSynchronized s a arrobj e E T)
  from `P,E,h \<turnstile> sync(addr a) e : T`
  have "\<exists>arrobj. h a = \<lfloor>arrobj\<rfloor>"
    by(auto elim: WTrt_elim_cases)
  thus ?case by(fastsimp intro: red_reds.LockSynchronized)
qed(fastsimp intro: red_reds.intros split: split_if_asm simp: finfun_upd_apply)+

lemma red_Join_wth:
  "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>; P,E,h \<turnstile> e : T; hext h (hp s) \<rbrakk>
  \<Longrightarrow> convert_extTA extNTA,P \<turnstile> \<langle>e, (h, lcl s)\<rangle> -ta\<rightarrow> \<langle>e', (h, lcl s')\<rangle>"
  and reds_Join_wth:
  "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>; P,E,h \<turnstile> es [:] Ts; hext h (hp s) \<rbrakk>
  \<Longrightarrow> convert_extTA extNTA,P \<turnstile> \<langle>es, (h, lcl s)\<rangle> [-ta\<rightarrow>] \<langle>es', (h, lcl s')\<rangle>"
(* apply(induct arbitrary: E T and E Ts rule: red_reds.inducts)
apply(fastsimp intro: red_reds.intros split: split_if_asm)+
defer -- Join
apply(fastsimp intro: red_reds.intros split: split_if_asm)+
. *)
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case (RedCallExternal s a U M vs ta va h' ta' e' s')
  from `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>U\<rfloor>` `P,E,h \<turnstile> addr a\<bullet>M(map Val vs) : T` `hext h (hp s)`
  have "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>U\<rfloor>" by(fastsimp split: heapobj.split_asm dest: hext_objD hext_arrD)
  moreover with `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>` `P,E,h \<turnstile> addr a\<bullet>M(map Val vs) : T` 
    `Join t \<in> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub>` `hext h (hp s)` `ta' = convert_extTA extNTA ta` `is_external_call P U M (length vs)`
  have "P \<turnstile> \<langle>a\<bullet>M(vs),h\<rangle> -ta\<rightarrow>ext \<langle>va,h\<rangle>" by(auto intro: red_external_Join_wth split: heapobj.split_asm)
  ultimately show ?case using `is_external_call P U M (length vs)` `ta' = convert_extTA extNTA ta`
    `e' = extRet2J va` `s' = (h', lcl s)` by(auto intro: red_reds.RedCallExternal)
qed(fastsimp intro: red_reds.intros split: split_if_asm)+

lemma red_wt_hconf_hext:
  assumes wf: "wf_J_prog P"
  and hconf: "P \<turnstile> H \<surd>"
  shows "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,E,H \<turnstile> e : T; hext H (hp s) \<rbrakk>
        \<Longrightarrow> \<exists>ta' e' s'. convert_extTA extNTA,P \<turnstile> \<langle>e, (H, lcl s)\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle> \<and> locks_a ta' = locks_a ta \<and> wset_a ta' = wset_a ta \<and> cond_a ta' = cond_a ta"
  and "\<lbrakk> convert_extTA extNTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; P,E,H \<turnstile> es [:] Ts; hext H (hp s) \<rbrakk>
        \<Longrightarrow> \<exists>ta' es' s'. convert_extTA extNTA,P \<turnstile> \<langle>es, (H, lcl s)\<rangle> [-ta'\<rightarrow>] \<langle>es', s'\<rangle> \<and> locks_a ta' = locks_a ta \<and> wset_a ta' = wset_a ta \<and> cond_a ta' = cond_a ta"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case (RedNew h a C FDTs h' l E T)
  show ?case
  proof(cases "new_Addr H")
    case None thus ?thesis
      by(fastsimp intro: RedNewFail)
  next
    case (Some a)
    with `P \<turnstile> C has_fields FDTs` show ?thesis
      by(fastsimp intro: red_reds.RedNew)
  qed
next
  case (RedNewFail s C E T)
  show ?case
  proof(cases "new_Addr H")
    case None thus ?thesis
      by(fastsimp intro: red_reds.RedNewFail)
  next
    case (Some a)
    with `P,E,H \<turnstile> new C : T` wf show ?thesis
      by(fastsimp del:exE intro!:RedNew simp add:new_Addr_def elim!:wf_Fields_Ex[THEN exE])
  qed
next 
  case NewArrayRed thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedNewArray h a i h' T l E T')
  show ?case
  proof(cases "new_Addr H")
    case None thus ?thesis using `0 \<le> i`
      by(fastsimp intro: red_reds.RedNewArrayFail)
  next
    case (Some a)
    with `0 \<le> i` show ?thesis
      by(fastsimp intro: red_reds.RedNewArray)
  qed
next 
  case (RedNewArrayFail h i T l E T')
  show ?case
  proof(cases "new_Addr H")
    case None thus ?thesis using `0 \<le> i`
      by(fastsimp intro: red_reds.RedNewArrayFail)
  next
    case (Some a)
    with `0 \<le> i` show ?thesis
      by(fastsimp intro: red_reds.RedNewArray)
  qed
next
  case RedNewArrayNegative thus ?case by(fastsimp intro: red_reds.intros)
next
  case CastRed thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedCast s v U T E T')
  from `P,E,H \<turnstile> Cast T (Val v) : T'` show ?case
  proof(rule WTrt_elim_cases)
    fix T''
    assume wt: "P,E,H \<turnstile> Val v : T''" "T = T'"
    show ?thesis
    proof(cases "P \<turnstile> T'' \<le> T")
      case True
      with wt show ?thesis
	by(fastsimp intro: red_reds.RedCast)
    next
      case False
      with wt show ?thesis
	by(fastsimp intro: red_reds.RedCastFail)
    qed
  qed
next 
  case (RedCastFail s v U T E T')
  from `P,E,H \<turnstile> Cast T (Val v) : T'` show ?case
  proof(rule WTrt_elim_cases)
    fix T''
    assume wt: "P,E,H \<turnstile> Val v : T''" "T = T'"
    show ?thesis
    proof(cases "P \<turnstile> T'' \<le> T")
      case True
      with wt show ?thesis
	by(fastsimp intro: red_reds.RedCast)
    next
      case False
      with wt show ?thesis
	by(fastsimp intro: red_reds.RedCastFail)
    qed
  qed
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
  case (RedAAccBounds s a T el i E T')
  from `P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> : T'` show ?case
  proof(rule WTrt_elim_cases)
    assume wt: "P,E,H \<turnstile> addr a : T'\<lfloor>\<rceil>"
    then obtain el' where Ha: "H a = \<lfloor>Arr T' el'\<rfloor>" by(auto split: heapobj.split_asm)
    with `hext H (hp s)` `hp s a = \<lfloor>Arr T el\<rfloor>` have si': "length el' = length el"
      by(auto dest!: hext_arrD)
    with Ha `i < 0 \<or> int (length el) \<le> i` show ?thesis
      by(fastsimp intro: red_reds.RedAAccBounds)
  next
    assume wt: "P,E,H \<turnstile> addr a : NT"
    hence False by(auto split: heapobj.split_asm)
    thus ?thesis ..
  qed
next 
  case (RedAAcc s a T el i E T')
  from `P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> : T'` show ?case
  proof(rule WTrt_elim_cases)
    assume wt: "P,E,H \<turnstile> addr a : T'\<lfloor>\<rceil>"
    then obtain el' where Ha: "H a = \<lfloor>Arr T' el'\<rfloor>" by(auto split: heapobj.split_asm)
    with `hext H (hp s)` `hp s a = \<lfloor>Arr T el\<rfloor>` have si': "length el' = length el"
      by(auto dest!: hext_arrD)
    with Ha `0 \<le> i` `i < int (length el)` show ?thesis
      by(fastsimp intro: red_reds.RedAAcc)
  next
    assume wt: "P,E,H \<turnstile> addr a : NT"
    hence False by(auto split: heapobj.split_asm)
    thus ?thesis ..
  qed
next
  case AAssRed1 thus ?case by(fastsimp intro: red_reds.intros)
next
  case AAssRed2 thus ?case by(fastsimp intro: red_reds.intros)
next
  case AAssRed3 thus ?case by(fastsimp intro: red_reds.intros)
next
  case RedAAssNull thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedAAssBounds s a T el i e E T')
  from `P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> := Val e : T'` show ?case
  proof(rule WTrt_elim_cases)
    fix T'' T'''
    assume wt: "P,E,H \<turnstile> addr a : T''\<lfloor>\<rceil>"
    then obtain el' where Ha: "H a = \<lfloor>Arr T'' el'\<rfloor>" by(auto split: heapobj.split_asm)
    with `hext H (hp s)` `hp s a = \<lfloor>Arr T el\<rfloor>` have si': "length el' = length el" and T'': "T'' = T"
      by(auto dest!: hext_arrD)
    with Ha `i < 0 \<or> int (length el) \<le> i` show ?thesis
      by(fastsimp intro: red_reds.RedAAssBounds)
  next
    fix T''
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(auto split: heapobj.split_asm)
    thus ?thesis ..
  qed
next
  case (RedAAssStore s a T el i w U E T')
  from `P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> := Val w : T'` show ?case
  proof(rule WTrt_elim_cases)
    fix T'' T'''
    assume wt: "P,E,H \<turnstile> addr a : T''\<lfloor>\<rceil>"
      and wtw: "P,E,H \<turnstile> Val w : T'''"
    then obtain el' where Ha: "H a = \<lfloor>Arr T'' el'\<rfloor>" by(auto split: heapobj.split_asm)
    with `hext H (hp s)` `hp s a = \<lfloor>Arr T el\<rfloor>` have si': "length el' = length el" and T'': "T'' = T"
      by(auto dest!: hext_arrD)
    from `typeof\<^bsub>hp s\<^esub> w = \<lfloor>U\<rfloor>` wtw `hext H (hp s)` have "typeof\<^bsub>H\<^esub> w = \<lfloor>U\<rfloor>" 
      by(auto dest: type_of_hext_type_of)
    with Ha `0 \<le> i` `i < int (length el)` `\<not> P \<turnstile> U \<le> T` T'' si' show ?thesis
      by(fastsimp intro: red_reds.RedAAssStore)
  next
    fix T''
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(auto split: heapobj.split_asm)
    thus ?thesis ..
  qed
next
  case (RedAAss h a T el i w U h' l E T')
  from `P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> := Val w : T'` show ?case
  proof(rule WTrt_elim_cases)
    fix T'' T'''
    assume wt: "P,E,H \<turnstile> addr a : T''\<lfloor>\<rceil>"
      and wtw: "P,E,H \<turnstile> Val w : T'''"
    then obtain el' where Ha: "H a = \<lfloor>Arr T'' el'\<rfloor>" by(auto split: heapobj.split_asm)
    with `hext H (hp (h, l))` `h a = \<lfloor>Arr T el\<rfloor>` have si': "length el' = length el" and T'': "T'' = T"
      by(auto dest!: hext_arrD)
    from `typeof\<^bsub>h\<^esub> w = \<lfloor>U\<rfloor>` wtw `hext H (hp (h, l))` have "typeof\<^bsub>H\<^esub> w = \<lfloor>U\<rfloor>" 
      by(auto dest: type_of_hext_type_of)
    with Ha `0 \<le> i` `i < int (length el)` `P \<turnstile> U \<le> T` T'' si' show ?thesis
      by(fastsimp intro: red_reds.RedAAss)
  next
    fix T''
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(auto split: heapobj.split_asm)
    thus ?thesis ..
  qed
next
  case ALengthRed thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedALength s a T elem E T')
  from `P,E,H \<turnstile> addr a\<bullet>length : T'`
  show ?case
  proof(rule WTrt_elim_cases)
    fix T''
    assume [simp]: "T' = Integer"
      and wta: "P,E,H \<turnstile> addr a : T''\<lfloor>\<rceil>"
    then obtain len' elem' where "H a = \<lfloor>Arr T'' elem'\<rfloor>" by(auto split: heapobj.split_asm)
    thus ?thesis by(fastsimp intro: red_reds.RedALength)
  next
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(auto split: heapobj.split_asm)
    thus ?thesis ..
  qed
next
  case (RedALengthNull s E T)
  show ?case by(fastsimp intro: red_reds.RedALengthNull)
next
  case FAccRed thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedFAcc s a C fs F D v E T)
  from `P,E,H \<turnstile> addr a\<bullet>F{D} : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C'
    assume wt: "P,E,H \<turnstile> addr a : Class C'"
      and has: "P \<turnstile> C' has F:T in D"
    then obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(auto split: heapobj.split_asm)
    with hconf have "P,H \<turnstile> Obj C' fs' \<surd>" by(auto simp: hconf_def)
    with has have "\<exists>v. fs' (F, D) = \<lfloor>v\<rfloor>"
      by(fastsimp simp: oconf_def)
    with has fs' show ?thesis
      by(fastsimp intro: red_reds.RedFAcc)
  next
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(auto split: heapobj.split_asm)
    thus ?thesis ..
  qed
next
  case RedFAccNull thus ?case by(fastsimp intro: red_reds.intros)
next
  case FAssRed1 thus ?case by(fastsimp intro: red_reds.intros)
next
  case FAssRed2 thus ?case by(fastsimp intro: red_reds.intros)
next
  case RedFAssNull thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedFAss h a C fs F D v l E T)
  from `P,E,H \<turnstile> addr a\<bullet>F{D} := Val v : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C' T' T2
    assume wt: "P,E,H \<turnstile> addr a : Class C'"
      and has: "P \<turnstile> C' has F:T' in D"
      and wtv: "P,E,H \<turnstile> Val v : T2"
      and T2T: "P \<turnstile> T2 \<le> T'"
    moreover from wt obtain fs' where "H a = \<lfloor>Obj C' fs'\<rfloor>" by(auto split: heapobj.split_asm)
    ultimately show ?thesis
      by(fastsimp intro: red_reds.RedFAss)
  next
    fix T2
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(auto split: heapobj.split_asm)
    thus ?thesis ..
  qed
next
  case CallObj thus ?case by(fastsimp intro: red_reds.intros)
next
  case CallParams thus ?case by(fastsimp intro: red_reds.intros)
next
  case (RedCall s a C fs M vs Ts T pns body D E T')
  from `P,E,H \<turnstile> addr a\<bullet>M(map Val vs) : T'` show ?case
  proof(rule WTrt_elim_cases)
    fix C' Ts' pns' body' D' Ts''
    assume wta: "P,E,H \<turnstile> addr a : Class C'"
      and sees: "P \<turnstile> C' sees M: Ts'\<rightarrow>T' = (pns', body') in D'"
      and wtes: "P,E,H \<turnstile> map Val vs [:] Ts''"
      and widens: "P \<turnstile> Ts'' [\<le>] Ts'"
      and nexc: "\<not> is_external_call P (Class C') M (length (map Val vs))"
    from wta obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(auto split: heapobj.split_asm)
    moreover from wtes have "length vs = length Ts''"
      by(auto intro: map_eq_imp_length_eq')
    moreover from widens have "length Ts'' = length Ts'"
      by(auto dest: widens_lengthD)
    moreover from sees wf have "wf_mdecl wf_J_mdecl P D' (M, Ts', T', pns', body')"
      by(auto intro: sees_wf_mdecl)
    hence "length pns' = length Ts'"
      by(simp add: wf_mdecl_def)
    moreover from `hp s a = \<lfloor>Obj C fs\<rfloor>` `hext H (hp s)` fs' have "C = C'"
      by(auto dest: hext_objD)
    ultimately show ?thesis using sees nexc
      by(fastsimp intro: red_reds.RedCall)
  next
    fix Ts
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(auto split: heapobj.split_asm)
    thus ?thesis ..
  next
    fix T Ts'
    assume "P \<turnstile> T\<bullet>M(Ts') :: T'" "P,E,H \<turnstile> addr a : T" "P,E,H \<turnstile> map Val vs [:] Ts'"
    with `hp s a = \<lfloor>Obj C fs\<rfloor>` `hext H (hp s)` have "is_external_call P (Class C) M (length Ts')"
      by(fastsimp split: heapobj.split_asm intro: external_WT_is_external_call dest: hext_objD hext_arrD)
    moreover from `P,E,H \<turnstile> map Val vs [:] Ts'` have "map typeof\<^bsub>H\<^esub> vs = map Some Ts'" by auto
    hence "length (map typeof\<^bsub>H\<^esub> vs) = length Ts'" by simp
    with `length vs = length pns` `length Ts = length pns` 
    have "length Ts' = length vs" by simp
    ultimately show ?case using `\<not> is_external_call P (Class C) M (length vs)` by simp
  qed
(*    fix C'
    assume sub: "P \<turnstile> C' \<preceq>\<^sup>* Thread"
      and start: "M = start"
      and wt: "P,E,H \<turnstile> addr a : Class C'"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(auto split: heapobj.split_asm)
    with `hp s a = \<lfloor>Obj C fs\<rfloor>` `hext H (hp s)` have "C = C'"
      by(auto dest: hext_objD)
    with sub start have False using `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
      by(auto dest: Thread_not_sees_method_start[OF wf])
    thus ?thesis ..
  next
    fix T'
    assume "M = wait"
    moreover
    from `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D` 
    obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(M, Ts, T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    ultimately have False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  next
    fix T'
    assume "M = notify"
    moreover
    from `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D` 
    obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(M, Ts, T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    ultimately have False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  next
    fix T'
    assume "M = notifyAll"
    moreover
    from `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D` 
    obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(M, Ts, T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    ultimately have False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  next
    fix C'
    assume sub: "P \<turnstile> C' \<preceq>\<^sup>* Thread"
      and start: "M = join"
      and wt: "P,E,H \<turnstile> addr a : Class C'"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(auto split: heapobj.split_asm)
    with `hp s a = \<lfloor>Obj C fs\<rfloor>` `hext H (hp s)` have "C = C'"
      by(auto dest: hext_objD)
    with sub start have False using `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
      by(auto dest: Thread_not_sees_method_join[OF wf])
    thus ?thesis ..
  qed *)
next
  case (RedCallExternal s a U M vs ta va h' ta' e' s')
  from `P,E,H \<turnstile> addr a\<bullet>M(map Val vs) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C ts pns body D Ts'
    assume "P,E,H \<turnstile> addr a : Class C" "\<not> is_external_call P (Class C) M (length (map Val vs))"
    with `is_external_call P U M (length vs)` `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>U\<rfloor>` `hext H (hp s)` have False
      by(auto split: heapobj.split_asm dest: hext_objD hext_arrD)
    thus ?thesis ..
  next
    fix Ts
    assume "P,E,H \<turnstile> addr a : NT" thus ?thesis by(auto split: heapobj.split_asm)
  next
    fix T' Ts
    assume wta: "P,E,H \<turnstile> addr a : T'" and wtvs: "P,E,H \<turnstile> map Val vs [:] Ts"
      and wtext: "P \<turnstile> T'\<bullet>M(Ts) :: T"
    from wta `typeof\<^bsub>hp s\<^esub> (Addr a) = \<lfloor>U\<rfloor>` `hext H (hp s)` have [simp]: "T' = U"
      by(auto split: heapobj.split_asm dest: hext_objD hext_arrD)
    with wta have "typeof\<^bsub>H\<^esub> (Addr a) = \<lfloor>U\<rfloor>" by simp
    with red_external_wt_hconf_hext[OF `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>` this, of Ts]
      `P,E,H \<turnstile> map Val vs [:] Ts` `hext H (hp s)` `is_external_call P U M (length vs)` `ta' = convert_extTA extNTA ta`
      `e' = extRet2J va` `s' = (h', lcl s)`
    show ?thesis by(fastsimp intro: red_reds.RedCallExternal)
  qed
(*  case (RedNewThread s a C fs body D)
  from `P,E,H \<turnstile> addr a\<bullet>start([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C' pns' body' D'
    assume sees: "P \<turnstile> C' sees start: []\<rightarrow>T = (pns', body') in D'"
      and wt: "P,E,H \<turnstile> addr a : Class C'"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(auto split: heapobj.split_asm)
    with `hp s a = \<lfloor>Obj C fs\<rfloor>` `hext H (hp s)` have "C = C'" by(auto dest: hext_objD)
    with `P \<turnstile> C \<preceq>\<^sup>* Thread` fs' sees wf have False
      by(auto simp: Method_def intro: Thread_no_sees_method_start[OF wf])
    thus ?thesis ..
  next
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(auto split: heapobj.split_asm)
    thus ?thesis ..
  next
    fix C'
    assume wt: "P,E,H \<turnstile> addr a : Class C'"
      and sub: "P \<turnstile> C' \<preceq>\<^sup>* Thread"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(auto split: heapobj.split_asm)
    moreover with `hp s a = \<lfloor>Obj C fs\<rfloor>` `hext H (hp s)` have "C = C'" by(auto dest: hext_objD)
    moreover note sub `P \<turnstile> C sees run: []\<rightarrow>Void = ([], body) in D`
    ultimately show ?thesis by(fastsimp intro: red_reds.RedNewThread)
  qed
next
  case (RedNewThreadFail s a C fs E T)
  from `P,E,H \<turnstile> addr a\<bullet>start([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C' pns' body' D'
    assume sees: "P \<turnstile> C' sees start: []\<rightarrow>T = (pns', body') in D'"
      and wt: "P,E,H \<turnstile> addr a : Class C'"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(auto split: heapobj.split_asm)
    with `hp s a = \<lfloor>Obj C fs\<rfloor>` `hext H (hp s)` have "C = C'"
      by(auto dest: hext_objD)
    with `P \<turnstile> C \<preceq>\<^sup>* Thread` fs' sees wf have False
      by(auto simp: Method_def intro: Thread_no_sees_method_start[OF wf])
    thus ?thesis ..
  next
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(auto split: heapobj.split_asm)
    thus ?thesis ..
  next
    fix C'
    assume wt: "P,E,H \<turnstile> addr a : Class C'"
      and sub: "P \<turnstile> C' \<preceq>\<^sup>* Thread"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(auto split: heapobj.split_asm)
    with sub show ?thesis
      by(fastsimp intro: red_reds.RedNewThreadFail)
  qed
next
  case (RedWait s a arrobj E T)
  from `P,E,H \<turnstile> addr a\<bullet>wait([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C pns body D
    assume "P \<turnstile> C sees wait: []\<rightarrow>T = (pns, body) in D"
    then obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(wait, [], T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    hence False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  qed(fastsimp split: heapobj.split_asm intro: red_reds.RedWait)+
next
  case (RedWaitFail s a arrobj E T)
  from `P,E,H \<turnstile> addr a\<bullet>wait([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C pns body D
    assume "P \<turnstile> C sees wait: []\<rightarrow>T = (pns, body) in D"
    then obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(wait, [], T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    hence False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  qed(fastsimp split: heapobj.split_asm intro: red_reds.RedWaitFail)+
next
  case (RedNotify s a arrobj E T)
  from `P,E,H \<turnstile> addr a\<bullet>notify([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C pns body D
    assume "P \<turnstile> C sees notify: []\<rightarrow>T = (pns, body) in D"
    then obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(notify, [], T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    hence False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  qed(fastsimp split: heapobj.split_asm intro: red_reds.RedNotify)+
next
  case (RedNotifyFail s a arrobj E T)
  from `P,E,H \<turnstile> addr a\<bullet>notify([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C pns body D
    assume "P \<turnstile> C sees notify: []\<rightarrow>T = (pns, body) in D"
    then obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(notify, [], T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    hence False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  qed(fastsimp split: heapobj.split_asm intro: red_reds.RedNotifyFail)+
next
  case (RedNotifyAll s a arrobj E T)
  from `P,E,H \<turnstile> addr a\<bullet>notifyAll([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C pns body D
    assume "P \<turnstile> C sees notifyAll: []\<rightarrow>T = (pns, body) in D"
    then obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(notifyAll, [], T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    hence False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  qed(fastsimp split: heapobj.split_asm intro: red_reds.RedNotifyAll)+
next
  case (RedNotifyAllFail s a arrobj E T)
  from `P,E,H \<turnstile> addr a\<bullet>notifyAll([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C pns body D
    assume "P \<turnstile> C sees notifyAll: []\<rightarrow>T = (pns, body) in D"
    then obtain D' fs' ms' where c: "class P D = \<lfloor>(D', fs', ms')\<rfloor>" and ms: "(notifyAll, [], T, pns, body) \<in> set ms'"
      by(auto dest!: visible_method_exists map_of_SomeD)
    hence False using wf
      by(auto dest: class_wf simp add: wf_cdecl_def)
    thus ?thesis ..
  qed(fastsimp split: heapobj.split_asm intro: red_reds.RedNotifyAllFail)+
next
  case (RedJoin s a C fs E T)
  from `P,E,H \<turnstile> addr a\<bullet>join([]) : T` show ?case
  proof(rule WTrt_elim_cases)
    fix C' pns' body' D'
    assume sees: "P \<turnstile> C' sees join: []\<rightarrow>T = (pns', body') in D'"
      and wt: "P,E,H \<turnstile> addr a : Class C'"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(auto split: heapobj.split_asm)
    with `hp s a = \<lfloor>Obj C fs\<rfloor>` `hext H (hp s)` have "C = C'"
      by(auto dest: hext_objD)
    with `P \<turnstile> C \<preceq>\<^sup>* Thread` fs' sees wf have False
      by(auto dest: Thread_not_sees_method_join[OF wf])
    thus ?thesis ..
  next
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(auto split: heapobj.split_asm)
    thus ?thesis ..
  next
    fix C'
    assume wt: "P,E,H \<turnstile> addr a : Class C'"
      and sub: "P \<turnstile> C' \<preceq>\<^sup>* Thread"
    from wt obtain fs' where fs': "H a = \<lfloor>Obj C' fs'\<rfloor>" by(auto split: heapobj.split_asm)
    with sub show ?thesis
      by(fastsimp intro: red_reds.RedJoin)
  qed *)
next
  case RedCallNull thus ?case by(fastsimp intro: red_reds.intros)
next
  case (BlockRed e h l V vo ta e' h' l' T cr E T')
  note IH = `\<And>E T. \<lbrakk>P,E,H \<turnstile> e : T; hext H (hp (h, l(V := vo)))\<rbrakk>
              \<Longrightarrow> \<exists>ta' e' s'. convert_extTA extNTA,P \<turnstile> \<langle>e,(H, lcl (h, l(V := vo)))\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle> \<and> \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>`
  from IH[of "E(V \<mapsto> T)" T'] `P,E,H \<turnstile> {V:T=vo; e}\<^bsub>cr\<^esub> : T'` `hext H (hp (h, l))`
  obtain ta' e' s' where "convert_extTA extNTA,P \<turnstile> \<langle>e,(H, lcl (h, l(V := vo)))\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle>" "\<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" "\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" "\<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
    by auto
  thus ?case by(cases s', cases ta', fastsimp dest: red_reds.BlockRed)
next
  case RedBlock thus ?case by(fastsimp intro: red_reds.intros)
next
  case SynchronizedRed1 thus ?case by(fastsimp intro: red_reds.intros)
next
  case SynchronizedNull thus ?case by(fastsimp intro: red_reds.intros)
next
  case (LockSynchronized s a arrobj e E T)
  from `P,E,H \<turnstile> sync(addr a) e : T` show ?case
  proof(rule WTrt_elim_cases)
    fix T
    assume "P,E,H \<turnstile> addr a : T" "is_refT T" "T \<noteq> NT"
    then obtain arrobj where "H a = \<lfloor>arrobj\<rfloor>"
      by(auto)
    thus ?thesis by(fastsimp intro: red_reds.LockSynchronized)
  next
    fix T
    assume "P,E,H \<turnstile> addr a : NT"
    hence False by(clarsimp split: heapobj.split_asm)
    thus ?thesis ..
  qed
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
  case (RedTryCatch s a D fs C V e2 E T)
  from `P,E,H \<turnstile> try Throw a catch(C V) e2 : T`
  show ?case
  proof(rule WTrt_elim_cases)
    fix T1
    assume "P,E,H \<turnstile> Throw a : T1"
    thus ?thesis
    proof(rule WTrt_elim_cases)
      fix T'
      assume "P,E,H \<turnstile> addr a : T'"
      with `hp s a = \<lfloor>Obj D fs\<rfloor>` `hext H (hp s)`
      obtain fs' where Ha: "H a = \<lfloor>Obj D fs'\<rfloor>"
	by(auto dest: hext_objD hext_arrD split: split:heapobj.split_asm)
      with `P \<turnstile> D \<preceq>\<^sup>* C` show ?thesis
	by(fastsimp intro: red_reds.RedTryCatch)
    qed
  qed
next
  case (RedTryFail s a D fs C V e2 E T)
  from `P,E,H \<turnstile> try Throw a catch(C V) e2 : T`
  show ?case
  proof(rule WTrt_elim_cases)
    fix T1
    assume "P,E,H \<turnstile> Throw a : T1"
    thus ?thesis
    proof(rule WTrt_elim_cases)
      fix T'
      assume "P,E,H \<turnstile> addr a : T'"
      with `hp s a = \<lfloor>Obj D fs\<rfloor>` `hext H (hp s)`
      obtain fs' where Ha: "H a = \<lfloor>Obj D fs'\<rfloor>" 
	by(clarsimp, case_tac aa, auto dest: hext_objD hext_arrD)
      with `\<not> P \<turnstile> D \<preceq>\<^sup>* C` show ?thesis
	apply -
	apply(rule exI)+
	apply(rule conjI)
	apply(rule red_reds.RedTryFail)
	by(fastsimp)+
    qed
  qed
next
  case ListRed1 thus ?case by(fastsimp intro: red_reds.intros)
next
  case ListRed2 thus ?case by(fastsimp intro: red_reds.intros)
next
  case NewArrayThrow thus ?case by(fastsimp intro: red_reds.intros)
next
  case CastThrow thus ?case by(fastsimp intro: red_reds.intros)
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
  "\<lbrakk> wf_J_prog P; P \<turnstile> \<langle>e, (h', l)\<rangle> L \<wrong>; P,E,h \<turnstile> e : T; P \<turnstile> h \<surd>; hext h h' \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>e, (h, l)\<rangle> L \<wrong>"
apply(cases "L = {}")
 apply(clarsimp)
 apply(erule multithreaded.can_syncE[OF red_mthr])
 apply(clarsimp)
 apply(drule sym)
 apply(clarsimp simp add: Plus_eq_empty_conv)
 apply(drule red_wt_hconf_hext, assumption+)
  apply(simp)
 apply(clarsimp)
 apply(rule multithreaded.can_syncI[OF red_mthr])
 apply(fastsimp)
 apply(rule sym)
 apply(simp add: Plus_eq_empty_conv)
apply(erule multithreaded.can_syncE[OF red_mthr])
apply(case_tac x', auto elim!: collect_locksE)
 apply(drule red_Lock_wth)
 apply(auto intro: multithreaded.can_syncI[OF red_mthr])
apply(drule red_Join_wth)
apply(auto intro: multithreaded.can_syncI[OF red_mthr])
done


lemma can_sync_preserved:
  assumes "P \<turnstile> \<langle>e, (h, l)\<rangle> LT \<wrong>"
  and "hext h h'"
  and "LT \<noteq> {}"
  shows "P \<turnstile> \<langle>e, (h', l)\<rangle> \<wrong>"
using assms
apply -
apply(rule multithreaded.must_syncI[OF red_mthr])
apply(erule multithreaded.can_syncE[OF red_mthr])
apply(clarsimp)
apply(auto simp add: collect_locks_def)
apply(drule red_Lock_hext)
   apply(simp)
  apply(simp)
 apply(simp)
apply(drule red_Join_hext)
  apply(simp)
 apply(simp)
apply(simp)
done

lemma preserve_deadlocked:
  assumes wf: "wf_J_prog P"
  and st: "sconf_type_ts_ok P Es (thr S) (shr S)"
  and da: "def_ass_ts_ok (thr S) (shr S)"
  and lto: "lock_thread_ok (locks S) (thr S)"
  shows "preserve_deadlocked final_expr (mred P) S"
proof -
  { fix tta s t' ta' s' t x ln
    assume Red: "P \<turnstile> S -\<triangleright>tta\<rightarrow>* s"
      and red: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow> s'"
      and tst: "thr s t = \<lfloor>(x, ln)\<rfloor>"
    obtain e l where x [simp]: "x = (e, l)" by(cases x, auto)
    let ?Es' = "upd_invs Es (\<lambda>ET (e, x) m. sconf_type_ok P ET e m x) (\<down>map (thr_a \<circ> snd) tta\<down>)"
    from st Red have st': "sconf_type_ts_ok P ?Es' (thr s) (shr s)"
      by(auto dest: RedT_invariant_sconf_type[OF wf])
    with tst obtain E T where Est: "?Es' t = \<lfloor>(E, T)\<rfloor>" 
      and stt: "sconf_type_ok P (E, T) e (shr s) l" by(auto dest!: ts_invD)
    from stt have hconf: "P \<turnstile> shr s \<surd>"
      by(simp add: sconf_type_ok_def sconf_def)
    from stt obtain T' where wte: "P,E,shr s \<turnstile> e : T'"
      by(auto simp add: sconf_type_ok_def type_ok_def)
    from red have hext: "hext (shr s) (shr s')"
      by(cases s, cases s')(auto dest: redT_hext_incr)

    { fix LT
      assume "multithreaded.can_sync (mred P) x (shr s) LT"
        and LT: "LT \<noteq> {}"
      hence cl: "P \<turnstile> \<langle>e, (shr s, l)\<rangle> LT \<wrong>" by auto
      with hext hconf LT have "P \<turnstile> \<langle>e, (shr s', l)\<rangle> \<wrong>"
	by-(rule can_sync_preserved)
      hence "multithreaded.must_sync (mred P) x (shr s')" by simp }
    note ml = this
    { fix LT
      assume "multithreaded.can_sync (mred P) x (shr s') LT"
      hence cl: "P \<turnstile> \<langle>e, (shr s', l)\<rangle> LT \<wrong>" by auto
      with wf wte hext hconf have "P \<turnstile> \<langle>e, (shr s, l)\<rangle> LT \<wrong>"
	by -(rule can_lock_devreserp)
      hence "\<exists>LT'\<subseteq>LT. multithreaded.can_sync (mred P) x (shr s) LT'"
	by(auto) }
    note this ml }
  with lto show ?thesis by(unfold_locales)
qed

end
