(*  Title:      JinjaThreads/J/SmallTypeSafe.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Type Safety Proof} *}

theory TypeSafe
imports
  Progress
  JWellForm
  DefAssPreservation
  "../Common/ExternalCallWF"
begin

subsection{*Basic preservation lemmas*}

text{* First two easy preservation lemmas. *}

theorem red_preserves_hconf: "\<lbrakk> extTA,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; P,E,hp s \<turnstile> e : T; P \<turnstile> hp s \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> hp s' \<surd>"
  and reds_preserves_hconf: "\<lbrakk> extTA,P \<turnstile> \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>; P,E,hp s \<turnstile> es [:] Ts; P \<turnstile> hp s \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> hp s' \<surd>"
proof (induct arbitrary: T E and Ts E rule: red_reds.inducts)
  case (RedNew h a C FDTs h' l T E)
  have new: "new_Addr h = Some a" and fields: "P \<turnstile> C has_fields FDTs" by fact+
  have h': "h' = h(a\<mapsto>(Obj C (init_fields FDTs)))" by fact
  have hconf: "P \<turnstile> hp (h, l) \<surd>" by fact
  from new have None: "h a = None" by(rule new_Addr_SomeD)
  moreover have "P,h \<turnstile> (Obj C (init_fields FDTs)) \<surd>"
    using fields by(rule oconf_init_fields)
  ultimately show "P \<turnstile> hp (h', l) \<surd>" using h' hconf by(simp)(rule hconf_new)
next
  case (RedNewArray h a i h' T l T' E)
  have new: "new_Addr h = Some a"
    and isize: "0 \<le> i"
    and h': "h' = h(a \<mapsto> Arr T (replicate (nat i) (default_val T)))"
    and hconf: "P \<turnstile> hp (h, l) \<surd>" by fact+
  have wt: "P,E,hp (h, l) \<turnstile> newA T\<lfloor>Val (Intg i)\<rceil> : T'" by fact
  from new have None: "h a = None" by(rule new_Addr_SomeD)
  moreover 
  from wt have "is_type P T" by(auto)
  hence "P,h \<turnstile> (Arr T (replicate (nat i) (default_val T))) \<surd>"
    by -(rule oconf_init_arr)
  ultimately show "P \<turnstile> hp (h', l) \<surd>" using h' hconf by(simp)(rule hconf_new)
next
  case (RedAAss h a T el i w U h' l T' E)
  let ?el' = "el[nat i := w]"
  have hconf: "P \<turnstile> hp (h, l) \<surd>" and ha: "h a = Some(Arr T el)"
    and "0 \<le> i" and "i < int (length el)"
    and "typeof\<^bsub>h\<^esub> w = \<lfloor>U\<rfloor>" and "P \<turnstile> U \<le> T"
    and h': "h' = h(a \<mapsto> Arr T (el[nat i := w]))"
    and wt: "P,E,hp (h,l) \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> := Val w : T'"  by fact+
  have "P,h \<turnstile> (Arr T ?el') \<surd>"
  proof (rule oconf_fupd_arr)
    from `typeof\<^bsub>h\<^esub> w = \<lfloor>U\<rfloor>` `P \<turnstile> U \<le> T` show "P,h \<turnstile> w :\<le> T" by (simp add: conf_def)
  next
    from `h a = \<lfloor>Arr T el\<rfloor>` `P \<turnstile> hp (h, l) \<surd>`
    show "P,h \<turnstile> Arr T el \<surd>" by (simp add: hconf_def)
  qed
  with hconf ha h' have "P \<turnstile> h(a\<mapsto>(Arr T (el[nat i := w]))) \<surd>" by - (rule hconf_upd_arr, auto)
  with h' show ?case by(simp del: fun_upd_apply)
next
  case (RedFAss h a C fs F D v l T E)
  let ?fs' = "fs((F,D)\<mapsto>v)"
  have hconf: "P \<turnstile> hp(h, l) \<surd>" and ha: "h a = Some(Obj C fs)"
   and wt: "P,E,hp (h, l) \<turnstile> addr a\<bullet>F{D}:=Val v : T" by fact+
  from wt ha obtain TF Tv where typeofv: "typeof\<^bsub>h\<^esub> v = Some Tv"
    and has: "P \<turnstile> C has F:TF in D"
    and sub: "P \<turnstile> Tv \<le> TF" by auto
  have "P,h \<turnstile> (Obj C ?fs') \<surd>"
  proof (rule oconf_fupd[OF has])
    show "P,h \<turnstile> (Obj C fs) \<surd>" using hconf ha by(simp add:hconf_def)
    show "P,h \<turnstile> v :\<le> TF" using sub typeofv by(simp add:conf_def)
  qed
  with hconf ha show ?case by(simp del: fun_upd_apply)(rule hconf_upd_obj)
next
  case (RedCallExternal s a U M vs ta va h' ta' e' s')
  hence "P,hp s \<turnstile> a\<bullet>M(vs) : T" by(auto intro: external_WT'.intros split: heapobj.split_asm)
  with RedCallExternal show ?case by(auto split: heapobj.split_asm dest: external_call_hconf)
qed auto


theorem red_preserves_lconf:
  "\<lbrakk> extTA,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; P,E,hp s \<turnstile> e:T; P,hp s \<turnstile> lcl s (:\<le>) E \<rbrakk> \<Longrightarrow> P,hp s' \<turnstile> lcl s' (:\<le>) E"
  and reds_preserves_lconf:
  "\<lbrakk> extTA,P \<turnstile> \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>; P,E,hp s \<turnstile> es[:]Ts; P,hp s \<turnstile> lcl s (:\<le>) E \<rbrakk> \<Longrightarrow> P,hp s' \<turnstile> lcl s' (:\<le>) E"
proof(induct arbitrary: T E and Ts E rule:red_reds.inducts)
  case RedNew thus ?case
    by(fastsimp intro:lconf_hext red_hext_incr[OF red_reds.RedNew, simplified] simp del: fun_upd_apply)
next
  case RedNewArray thus ?case
    by(fastsimp intro:lconf_hext red_hext_incr[OF red_reds.RedNewArray, simplified] simp del: fun_upd_apply)
next
  case RedLAss thus ?case 
    by(fastsimp elim: lconf_upd simp add: conf_def simp del: fun_upd_apply )
next
  case RedAAss thus ?case
    by(fastsimp intro:lconf_hext red_hext_incr[OF red_reds.RedAAss, simplified] simp del: fun_upd_apply)
next
  case RedFAss thus ?case
    by(fastsimp intro:lconf_hext red_hext_incr[OF red_reds.RedFAss, simplified] simp del: fun_upd_apply)
next
  case (BlockRed e h x V vo ta e' h' x' T T' E)
  note red = `extTA,P \<turnstile> \<langle>e,(h, x(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>`
  note IH = `\<And>T E. \<lbrakk>P,E,hp (h, x(V := vo)) \<turnstile> e : T;
               P,hp (h, x(V := vo)) \<turnstile> lcl (h, x(V := vo)) (:\<le>) E\<rbrakk>
              \<Longrightarrow> P,hp (h', x') \<turnstile> lcl (h', x') (:\<le>) E`
  note wt = `P,E,hp (h, x) \<turnstile> {V:T=vo; e} : T'`
  note lconf = `P,hp (h, x) \<turnstile> lcl (h, x) (:\<le>) E`
  from lconf_hext[OF lconf[simplified] red_hext_incr[OF red, simplified]]
  have "P,h' \<turnstile> x (:\<le>) E" .
  moreover from wt have "P,E(V\<mapsto>T),h \<turnstile> e : T'" by(cases vo, auto)
  moreover from lconf wt have "P,h \<turnstile> x(V := vo) (:\<le>) E(V \<mapsto> T)"
    by(cases vo)(simp add: lconf_def,auto intro: lconf_upd2 simp add: conf_def)
  ultimately have "P,h' \<turnstile> x' (:\<le>) E(V\<mapsto>T)" 
    by(auto intro: IH[simplified])
  with `P,h' \<turnstile> x (:\<le>) E` show ?case
    by(auto simp add: lconf_def split: split_if_asm)
next
  case (RedCallExternal s a U M vs ta va h' ta' e' s')
  from `P \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>` have "hp s \<unlhd> h'" by(rule red_external_hext)
  with `s' = (h', lcl s)` `P,hp s \<turnstile> lcl s (:\<le>) E` show ?case by(auto intro: lconf_hext)
qed auto

text{* Combining conformance of heap and local variables: *}

constdefs
  sconf :: "J_prog \<Rightarrow> env \<Rightarrow> Jstate \<Rightarrow> bool"   ("_,_ \<turnstile> _ \<surd>"   [51,51,51]50)
  "P,E \<turnstile> s \<surd>  \<equiv>  let (h,l) = s in P \<turnstile> h \<surd> \<and> P,h \<turnstile> l (:\<le>) E"

lemma red_preserves_sconf:
  "\<lbrakk> extTA,P \<turnstile> \<langle>e,s\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>; P,E,hp s \<turnstile> e : T; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"
(*<*)
by(auto dest:red_preserves_hconf red_preserves_lconf
            simp add:sconf_def)
(*>*)

lemma reds_preserves_sconf:
  "\<lbrakk> extTA,P \<turnstile> \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>; P,E,hp s \<turnstile> es [:] Ts; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"
by(auto dest: reds_preserves_hconf reds_preserves_lconf simp add: sconf_def)


subsection "Subject reduction"

lemma wt_blocks:
 "\<And>E. \<lbrakk> length Vs = length Ts; length vs = length Ts \<rbrakk> \<Longrightarrow>
       (P,E,h \<turnstile> blocks(Vs,Ts,vs,e) : T) =
       (P,E(Vs[\<mapsto>]Ts),h \<turnstile> e:T \<and> (\<exists>Ts'. map (typeof\<^bsub>h\<^esub>) vs = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] Ts))"
apply(induct Vs Ts vs e rule:blocks.induct)
prefer 5 apply (force)
apply simp_all
done

lemma wt_external_call:
  "conf_extRet P h va T \<Longrightarrow> \<exists>T'. P,E,h \<turnstile> extRet2J va : T' \<and> P \<turnstile> T' \<le> T"
by(cases va)(auto simp add: conf_def)


theorem assumes wf: "wf_J_prog P"
  shows subject_reduction:
  "\<lbrakk> extTA,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e:T \<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> e':T' \<and> P \<turnstile> T' \<le> T"
  and subjects_reduction:
  "\<lbrakk> extTA,P \<turnstile> \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>; P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> es[:]Ts \<rbrakk> \<Longrightarrow> \<exists>Ts'. P,E,hp s' \<turnstile> es'[:]Ts' \<and> P \<turnstile> Ts' [\<le>] Ts"
proof (induct arbitrary: T E and Ts E rule:red_reds.inducts)
  case RedNew
  thus ?case by fastsimp
next
  case RedNewFail thus ?case
  by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_OutOfMemory simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case NewArrayRed
  thus ?case by fastsimp
next
  case RedNewArray
  thus ?case by fastsimp
next
  case RedNewArrayNegative thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_NegativeArraySize simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case RedNewArrayFail thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_OutOfMemory simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case (CastRed e s ta e' s' C T E)
  have esse: "extTA,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" 
    and IH: "\<And>T E. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T"
    and hconf: "P,E \<turnstile> s \<surd>"
    and wtc: "P,E,hp s \<turnstile> Cast C e : T" by fact+
  thus ?case
  proof(clarsimp)
    fix T'
    assume wte: "P,E,hp s \<turnstile> e : T'" "is_type P T"
    from wte and hconf and IH have "\<exists>U. P,E,hp s' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T'" by simp
    then obtain U where wtee: "P,E,hp s' \<turnstile> e' : U" and UsTT: "P \<turnstile> U \<le> T'" by blast
    from wtee `is_type P T` have "P,E,hp s' \<turnstile> Cast T e' : T" by(rule WTrtCast)
    thus "\<exists>T'. P,E,hp s' \<turnstile> Cast T e' : T' \<and> P \<turnstile> T' \<le> T" by blast
  qed
next
  case RedCast thus ?case
    by(clarsimp simp add: is_refT_def)
next
  case RedCastFail thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_ClassCast simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case (BinOpRed1 e\<^isub>1 s ta e\<^isub>1' s' bop e\<^isub>2 T E)
  have red: "extTA,P \<turnstile> \<langle>e\<^isub>1, s\<rangle> -ta\<rightarrow> \<langle>e\<^isub>1', s'\<rangle>"
   and IH: "\<And>T E. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e\<^isub>1:T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,hp s' \<turnstile> e\<^isub>1' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> s \<surd>" and wt: "P,E,hp s \<turnstile> e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 : T" by fact+
  from wt obtain T1 T2 where wt1: "P,E,hp s \<turnstile> e\<^isub>1 : T1"
    and wt2: "P,E,hp s \<turnstile> e\<^isub>2 : T2" and wtbop: "P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T" by auto
  from IH[OF conf wt1] obtain T1' where wt1': "P,E,hp s' \<turnstile> e\<^isub>1' : T1'"
    and sub: "P \<turnstile> T1' \<le> T1" by blast
  from WTrt_binop_widen_mono[OF wtbop sub widen_refl]
  obtain T' where wtbop': "P \<turnstile> T1'\<guillemotleft>bop\<guillemotright>T2 : T'" and sub': "P \<turnstile> T' \<le> T" by blast
  from wt1' WTrt_hext_mono[OF wt2 red_hext_incr[OF red]] wtbop'
  have "P,E,hp s' \<turnstile> e\<^isub>1' \<guillemotleft>bop\<guillemotright> e\<^isub>2 : T'" by(rule WTrtBinOp)
  with sub' show ?case by blast
next
  case (BinOpRed2 e\<^isub>2 s ta e\<^isub>2' s' v\<^isub>1 bop T E)
  have red: "extTA,P \<turnstile> \<langle>e\<^isub>2,s\<rangle> -ta\<rightarrow> \<langle>e\<^isub>2',s'\<rangle>" by fact
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e\<^isub>2:T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,hp s' \<turnstile> e\<^isub>2' : U \<and> P \<turnstile> U \<le> T" by fact
  have conf: "P,E \<turnstile> s \<surd>" and wt: "P,E,hp s \<turnstile> (Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> e\<^isub>2 : T" by fact+
  from wt obtain T1 T2 where wt1: "P,E,hp s \<turnstile> Val v\<^isub>1 : T1"
    and wt2: "P,E,hp s \<turnstile> e\<^isub>2 : T2" and wtbop: "P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T" by auto
  from IH[OF conf wt2] obtain T2' where wt2': "P,E,hp s' \<turnstile> e\<^isub>2' : T2'"
    and sub: "P \<turnstile> T2' \<le> T2" by blast
  from WTrt_binop_widen_mono[OF wtbop widen_refl sub]
  obtain T' where wtbop': "P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2' : T'" and sub': "P \<turnstile> T' \<le> T" by blast
  from WTrt_hext_mono[OF wt1 red_hext_incr[OF red]] wt2' wtbop'
  have "P,E,hp s' \<turnstile> Val v\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2' : T'" by(rule WTrtBinOp)
  with sub' show ?case by blast
next
  case (RedBinOp bop v1 v2 v s)
  from `P,E,hp s \<turnstile> Val v1 \<guillemotleft>bop\<guillemotright> Val v2 : T` obtain T1 T2
    where "typeof\<^bsub>hp s\<^esub> v1 = \<lfloor>T1\<rfloor>" "typeof\<^bsub>hp s\<^esub> v2 = \<lfloor>T2\<rfloor>" "P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T" by auto
  from binop_progress[OF this] `binop bop v1 v2 = \<lfloor>v\<rfloor>` 
  have "P,hp s \<turnstile> v :\<le> T" by auto
  thus ?case by(auto simp add: conf_def)
next
  case RedVar thus ?case by (fastsimp simp:sconf_def lconf_def conf_def)
next
  case LAssRed thus ?case by(blast intro:widen_trans)
next
  case RedLAss thus ?case by fastsimp
next
  case (AAccRed1 a s ta a' s' i T E)
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> a : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> a' : T' \<and> P \<turnstile> T' \<le> T"
    and assa: "extTA,P \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>"
    and wt: "P,E,hp s \<turnstile> a\<lfloor>i\<rceil> : T"
    and hconf: "P,E \<turnstile> s \<surd>" by fact+
  from wt have wti: "P,E,hp s \<turnstile> i : Integer" by auto
  from wti red_hext_incr[OF assa] have wti': "P,E,hp s' \<turnstile> i : Integer" by - (rule WTrt_hext_mono)
  { assume wta: "P,E,hp s \<turnstile> a : T\<lfloor>\<rceil>"
    from IH[OF hconf wta]
    obtain U where wta': "P,E,hp s' \<turnstile> a' : U" and UsubT: "P \<turnstile> U \<le> T\<lfloor>\<rceil>" by fastsimp
    with wta' wti' have ?case by(cases U, auto simp add: widen_Array) }
  moreover
  { assume wta: "P,E,hp s \<turnstile> a : NT"
    from IH[OF hconf wta] have "P,E,hp s' \<turnstile> a' : NT" by fastsimp
    from this wti' have ?case
      by(fastsimp intro:WTrtAAccNT) }
  ultimately show ?case using wt by auto
next
  case (AAccRed2 i s ta i' s' a T E)
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> i : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> i' : T' \<and> P \<turnstile> T' \<le> T"
    and issi: "extTA,P \<turnstile> \<langle>i,s\<rangle> -ta\<rightarrow> \<langle>i',s'\<rangle>"
    and wt: "P,E,hp s \<turnstile> Val a\<lfloor>i\<rceil> : T"
    and hconf: "P,E \<turnstile> s \<surd>" by fact+
  from wt have wti: "P,E,hp s \<turnstile> i : Integer" by auto
  from wti IH hconf have wti': "P,E,hp s' \<turnstile> i' : Integer" by blast
  from wt show ?case
  proof (rule WTrt_elim_cases)
    assume wta: "P,E,hp s \<turnstile> Val a : T\<lfloor>\<rceil>"
    from wta red_hext_incr[OF issi] have wta': "P,E,hp s' \<turnstile> Val a : T\<lfloor>\<rceil>" by (rule WTrt_hext_mono)
    from wta' wti' show ?case by(fastsimp)
  next
    assume wta: "P,E,hp s \<turnstile> Val a : NT"
    from wta red_hext_incr[OF issi] have wta': "P,E,hp s' \<turnstile> Val a : NT" by (rule WTrt_hext_mono)
    from wta' wti' show ?case
      by(fastsimp elim:WTrtAAccNT)
  qed
next
  case RedAAccNull thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_NullPointer simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case RedAAccBounds thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_ArrayIndexOutOfBounds simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case (RedAAcc s a T el i T' E)
  hence "P,hp s \<turnstile> Arr T el \<surd>" by (auto simp add: sconf_def hconf_def)
  moreover from `0 \<le> i` `i < int (length el)` have "el ! nat i \<in> set el" by auto
  ultimately obtain U where "typeof\<^bsub>hp s\<^esub> (el ! nat i) = \<lfloor>U\<rfloor>" and "P \<turnstile> U \<le> T'"
    using `P,E,hp s \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> : T'` `hp s a = \<lfloor>Arr T el\<rfloor>`
    by(auto simp add: oconf_def conf_def split: heapobj.split_asm)
  with RedAAcc show ?case by(auto simp del:fun_upd_apply)
next
  case (AAssRed1 a s ta a' s' i e T E)
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> a : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> a' : T' \<and> P \<turnstile> T' \<le> T"
    and assa: "extTA,P \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>"
    and wt: "P,E,hp s \<turnstile> a\<lfloor>i\<rceil> := e : T"
    and hconf: "P,E \<turnstile> s \<surd>" by fact+
  from wt have void: "T = Void" by blast
  from wt have wti: "P,E,hp s \<turnstile> i : Integer" by auto
  from wti red_hext_incr[OF assa] have wti': "P,E,hp s' \<turnstile> i : Integer" by - (rule WTrt_hext_mono)
  { assume wta: "P,E,hp s \<turnstile> a : NT"
    from IH[OF hconf wta] have wta': "P,E,hp s' \<turnstile> a' : NT" by fastsimp
    from wt wta obtain V where wte: "P,E,hp s \<turnstile> e : V" by(auto)
    from wte red_hext_incr[OF assa] have wte': "P,E,hp s' \<turnstile> e : V" by - (rule WTrt_hext_mono)
    from wta' wti' wte' void have ?case
      by(fastsimp elim: WTrtAAssNT) }
  moreover
  { fix U
    assume wta: "P,E,hp s \<turnstile> a : U\<lfloor>\<rceil>"
    from IH[OF hconf wta]
    obtain U' where wta': "P,E,hp s' \<turnstile> a' : U'" and UsubT: "P \<turnstile> U' \<le> U\<lfloor>\<rceil>" by fastsimp
    from wta' have ?case
    proof(cases U')
      case Void
      from prems show ?thesis by simp
    next
      case Boolean
      from prems show ?thesis by simp
    next
      case Integer
      from prems show ?thesis by simp
    next
      case NT
      assume UNT: "U' = NT"
      from UNT wt wta obtain V where wte: "P,E,hp s \<turnstile> e : V" by(auto)
      from wte red_hext_incr[OF assa] have wte': "P,E,hp s' \<turnstile> e : V" by - (rule WTrt_hext_mono)
      from wta' UNT wti' wte' void show ?thesis
	by(fastsimp elim: WTrtAAssNT)
    next
      case (Class C)
      from prems show ?thesis by(simp add: widen_Array)
    next
      case (Array A)
      have UA: "U' = A\<lfloor>\<rceil>" by fact
      with UA UsubT wt wta obtain V where wte: "P,E,hp s \<turnstile> e : V" by auto
      from wte red_hext_incr[OF assa] have wte': "P,E,hp s' \<turnstile> e : V" by - (rule WTrt_hext_mono)
      with wta' wte' UA wti' void show ?thesis by (fast elim:WTrtAAss)
    qed }
  ultimately show ?case using wt by blast
next
  case (AAssRed2 i s ta i' s' a e T E)
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> i : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> i' : T' \<and> P \<turnstile> T' \<le> T" 
    and issi: "extTA,P \<turnstile> \<langle>i,s\<rangle> -ta\<rightarrow> \<langle>i',s'\<rangle>" 
    and wt: "P,E,hp s \<turnstile> Val a\<lfloor>i\<rceil> := e : T" 
    and hconf: "P,E \<turnstile> s \<surd>" by fact+
  from wt have void: "T = Void" by blast
  from wt have wti: "P,E,hp s \<turnstile> i : Integer" by auto
  from IH[OF hconf wti] have wti': "P,E,hp s' \<turnstile> i' : Integer" by fastsimp
  from wt show ?case
  proof(rule WTrt_elim_cases)
    fix U T'
    assume wta: "P,E,hp s \<turnstile> Val a : U\<lfloor>\<rceil>"
      and wte: "P,E,hp s \<turnstile> e : T'"
    from wte red_hext_incr[OF issi] have wte': "P,E,hp s' \<turnstile> e : T'" by - (rule WTrt_hext_mono)
    from wta red_hext_incr[OF issi] have wta': "P,E,hp s' \<turnstile> Val a : U\<lfloor>\<rceil>" by - (rule WTrt_hext_mono)
    from wta' wti' wte' void show ?case by (fastsimp elim:WTrtAAss)
  next
    fix T'
    assume wta: "P,E,hp s \<turnstile> Val a : NT"
      and wte: "P,E,hp s \<turnstile> e : T'"
    from wte red_hext_incr[OF issi] have wte': "P,E,hp s' \<turnstile> e : T'" by - (rule WTrt_hext_mono)
    from wta red_hext_incr[OF issi] have wta': "P,E,hp s' \<turnstile> Val a : NT" by - (rule WTrt_hext_mono)
    from wta' wti' wte' void show ?case by (fastsimp elim:WTrtAAss)
  qed
next
  case (AAssRed3 e s ta e' s' a i T E)
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T" 
    and issi: "extTA,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" 
    and wt: "P,E,hp s \<turnstile> Val a\<lfloor>Val i\<rceil> := e : T" 
    and hconf: "P,E \<turnstile> s \<surd>" by fact+
  from wt have void: "T = Void" by blast
  from wt have wti: "P,E,hp s \<turnstile> Val i : Integer" by auto
  from wti red_hext_incr[OF issi] have wti': "P,E,hp s' \<turnstile> Val i : Integer" by - (rule WTrt_hext_mono)
  from wt show ?case
  proof(rule WTrt_elim_cases)
    fix U T'
    assume wta: "P,E,hp s \<turnstile> Val a : U\<lfloor>\<rceil>"
      and wte: "P,E,hp s \<turnstile> e : T'"
    from wta red_hext_incr[OF issi] have wta': "P,E,hp s' \<turnstile> Val a : U\<lfloor>\<rceil>" by - (rule WTrt_hext_mono)
    from IH[OF hconf wte]
    obtain V where wte': "P,E,hp s' \<turnstile> e' : V" by fastsimp
    from wta' wti' wte' void show ?case by (fastsimp elim:WTrtAAss)
  next
    fix T'
    assume wta: "P,E,hp s \<turnstile> Val a : NT"
      and wte: "P,E,hp s \<turnstile> e : T'"
    from wta red_hext_incr[OF issi] have wta': "P,E,hp s' \<turnstile> Val a : NT" by - (rule WTrt_hext_mono)
    from IH[OF hconf wte]
    obtain V where wte': "P,E,hp s' \<turnstile> e' : V" by fastsimp
    from wta' wti' wte' void show ?case by (fastsimp elim:WTrtAAss)
  qed
next
  case RedAAssNull thus ?case
    by (unfold sconf_def hconf_def) (auto elim!:typeof_NullPointer simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case RedAAssBounds thus ?case
    by (unfold sconf_def hconf_def) (auto elim!:typeof_ArrayIndexOutOfBounds simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case RedAAssStore thus ?case
    by (unfold sconf_def hconf_def) (auto elim!:typeof_ArrayStore simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case RedAAss thus ?case
    by(auto simp del:fun_upd_apply)
next
  case (ALengthRed a s ta a' s' T E)
  note IH = `\<And>T'. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> a : T'\<rbrakk>
      \<Longrightarrow> \<exists>T''. P,E,hp s' \<turnstile> a' : T'' \<and> P \<turnstile> T'' \<le> T'`
  from `P,E,hp s \<turnstile> a\<bullet>length : T`
  show ?case
  proof(rule WTrt_elim_cases)
    fix T'
    assume [simp]: "T = Integer"
      and wta: "P,E,hp s \<turnstile> a : T'\<lfloor>\<rceil>"
    from wta `P,E \<turnstile> s \<surd>` IH
    obtain T'' where wta': "P,E,hp s' \<turnstile> a' : T''" 
      and sub: "P \<turnstile> T'' \<le> T'\<lfloor>\<rceil>" by blast
    from sub have "P,E,hp s' \<turnstile> a'\<bullet>length : Integer"
      unfolding widen_Array
    proof(rule disjE)
      assume "T'' = NT"
      with wta' show ?thesis by(auto)
    next
      assume "\<exists>V. T'' = V\<lfloor>\<rceil> \<and> P \<turnstile> V \<le> T' \<and> (is_NT_Array V \<longrightarrow> V = T')"
      then obtain V where "T'' = V\<lfloor>\<rceil>" "P \<turnstile> V \<le> T'" by blast
      with wta' show ?thesis by -(rule WTrtALength, simp)
    qed
    thus ?thesis by(simp)
  next
    assume "P,E,hp s \<turnstile> a : NT"
    with `P,E \<turnstile> s \<surd>` IH
    obtain T'' where wta': "P,E,hp s' \<turnstile> a' : T''" 
      and sub: "P \<turnstile> T'' \<le> NT" by blast
    from sub have "T'' = NT" by auto
    with wta' show ?thesis by(auto)
  qed
next
  case (RedALength s a T elem T' E)
  from `hp s a = \<lfloor>Arr T elem\<rfloor>` `P,E,hp s \<turnstile> addr a\<bullet>length : T'`
  have [simp]: "T' = Integer" by(auto)
  thus ?case by(auto)
next
  case (RedALengthNull s T E)
  from `P,E \<turnstile> s \<surd>` have "preallocated (hp s)"
    by(clarsimp simp add: hconf_def sconf_def)
  hence "P,E,hp s \<turnstile> THROW NullPointer : T"
    by(auto elim:typeof_NullPointer simp add: xcpt_subcls_Throwable[OF _ wf])
  thus ?case by blast
next
  case (FAccRed e s ta e' s' F D T E)
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,hp s' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> s \<surd>" and wt: "P,E,hp s \<turnstile> e\<bullet>F{D} : T" by fact+
  -- "The goal: ?case = @{prop ?case}"
  -- "Now distinguish the two cases how wt can have arisen."
  { fix C assume wte: "P,E,hp s \<turnstile> e : Class C"
             and has: "P \<turnstile> C has F:T in D"
    from IH[OF conf wte]
    obtain U where wte': "P,E,hp s' \<turnstile> e' : U" and UsubC: "P \<turnstile> U \<le> Class C"
      by auto
    -- "Now distinguish what @{term U} can be."
    with UsubC have ?case
    proof(cases U)
      case Void
      from prems show ?thesis by simp
    next
      case Boolean
      from prems show ?thesis by simp
    next
      case Integer
      from prems show ?thesis by simp
    next
      case NT
      from prems show ?thesis using wte'
	by(blast intro:WTrtFAccNT widen_refl) 
    next
      case (Class C')
      assume U: "U = Class C'" and C'subC': "P \<turnstile> U \<le> Class C"
      from U C'subC' have C'subC: "P \<turnstile> C' \<preceq>\<^sup>* C" by fastsimp
      from has_field_mono[OF has C'subC] wte' U
      show ?thesis by(blast intro:WTrtFAcc) 
    next
      case (Array A)
      assume U: "U = A\<lfloor>\<rceil>"
      from U and UsubC have "\<exists>B. Class C = Array B \<or> Class C = Class Object"
	by(auto dest: Array_widen)
      hence "C = Object" by auto
      with has wf_Object_field_empty[OF wf] have False
	by(auto simp add: has_field_def dest: has_fields_fun)
      thus ?thesis by simp
    qed }
  moreover
  { assume "P,E,hp s \<turnstile> e : NT"
    hence "P,E,hp s' \<turnstile> e' : NT" using IH[OF conf] by fastsimp
    hence ?case  by(fastsimp intro:WTrtFAccNT widen_refl) }
  ultimately show ?case using wt by blast
next
  case RedFAcc thus ?case
    by(fastsimp simp:sconf_def hconf_def oconf_def conf_def has_field_def
                dest:has_fields_fun)
next
  case RedFAccNull thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_NullPointer simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case (FAssRed1 e s ta e' s' F D e\<^isub>2)
  have red: "extTA,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,hp s' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> s \<surd>" and wt: "P,E,hp s \<turnstile> e\<bullet>F{D}:=e\<^isub>2 : T" by fact+
  from wt have void: "T = Void" by blast
  -- "We distinguish if @{term e} has type @{term NT} or a Class type"
  -- "Remember ?case = @{term ?case}"
  { assume "P,E,hp s \<turnstile> e : NT"
    hence "P,E,hp s' \<turnstile> e' : NT" using IH[OF conf] by fastsimp
    moreover obtain T\<^isub>2 where "P,E,hp s \<turnstile> e\<^isub>2 : T\<^isub>2" using wt by auto
    from this red_hext_incr[OF red] have  "P,E,hp s' \<turnstile> e\<^isub>2 : T\<^isub>2"
      by(rule WTrt_hext_mono)
    ultimately have ?case using void by(blast intro!:WTrtFAssNT)
  }
  moreover
  { fix C TF T\<^isub>2 assume wt\<^isub>1: "P,E,hp s \<turnstile> e : Class C" and wt\<^isub>2: "P,E,hp s \<turnstile> e\<^isub>2 : T\<^isub>2"
    and has: "P \<turnstile> C has F:TF in D" and sub: "P \<turnstile> T\<^isub>2 \<le> TF"
    obtain U where wt\<^isub>1': "P,E,hp s' \<turnstile> e' : U" and UsubC: "P \<turnstile> U \<le> Class C"
      using IH[OF conf wt\<^isub>1] by blast
    have wt\<^isub>2': "P,E,hp s' \<turnstile> e\<^isub>2 : T\<^isub>2"
      by(rule WTrt_hext_mono[OF wt\<^isub>2 red_hext_incr[OF red]])
    -- "Is @{term U} the null type or a class type?"
    { assume "U = NT" with wt\<^isub>1' wt\<^isub>2' void have ?case
	by(blast intro!:WTrtFAssNT) }
    moreover
    { fix C' assume UClass: "U = Class C'" and "subclass": "P \<turnstile> C' \<preceq>\<^sup>* C"
      have "P,E,hp s' \<turnstile> e' : Class C'" using wt\<^isub>1' UClass by auto
      moreover have "P \<turnstile> C' has F:TF in D"
	by(rule has_field_mono[OF has "subclass"])
      ultimately have ?case using wt\<^isub>2' sub void by(blast intro:WTrtFAss) }
    moreover
    { fix A
      assume "U = A\<lfloor>\<rceil>"
      with UsubC have "C = Object" by(auto dest: Array_widen)
      with has wf_Object_field_empty[OF wf] have False
	by(auto simp add: has_field_def dest: has_fields_fun) }
    ultimately have ?case using UsubC by(auto simp add:widen_Class Array_widen) }
  ultimately show ?case using wt by blast
next
  case (FAssRed2 e\<^isub>2 s ta e\<^isub>2' s' v F D T E)
  have red: "extTA,P \<turnstile> \<langle>e\<^isub>2,s\<rangle> -ta\<rightarrow> \<langle>e\<^isub>2',s'\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e\<^isub>2 : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,hp s' \<turnstile> e\<^isub>2' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> s \<surd>" and wt: "P,E,hp s \<turnstile> Val v\<bullet>F{D}:=e\<^isub>2 : T" by fact+
  from wt have [simp]: "T = Void" by auto
  from wt show ?case
  proof (rule WTrt_elim_cases)
    fix C TF T\<^isub>2
    assume wt\<^isub>1: "P,E,hp s \<turnstile> Val v : Class C"
      and has: "P \<turnstile> C has F:TF in D"
      and wt\<^isub>2: "P,E,hp s \<turnstile> e\<^isub>2 : T\<^isub>2" and TsubTF: "P \<turnstile> T\<^isub>2 \<le> TF"
    have wt\<^isub>1': "P,E,hp s' \<turnstile> Val v : Class C"
      by(rule WTrt_hext_mono[OF wt\<^isub>1 red_hext_incr[OF red]])
    obtain T\<^isub>2' where wt\<^isub>2': "P,E,hp s' \<turnstile> e\<^isub>2' : T\<^isub>2'" and T'subT: "P \<turnstile> T\<^isub>2' \<le> T\<^isub>2"
      using IH[OF conf wt\<^isub>2] by blast
    have "P,E,hp s' \<turnstile> Val v\<bullet>F{D}:=e\<^isub>2' : Void"
      by(rule WTrtFAss[OF wt\<^isub>1' has wt\<^isub>2' widen_trans[OF T'subT TsubTF]])
    thus ?case by auto
  next
    fix T\<^isub>2 assume null: "P,E,hp s \<turnstile> Val v : NT" and wt\<^isub>2: "P,E,hp s \<turnstile> e\<^isub>2 : T\<^isub>2"
    from null have "v = Null" by simp
    moreover
    obtain T\<^isub>2' where "P,E,hp s' \<turnstile> e\<^isub>2' : T\<^isub>2' \<and> P \<turnstile> T\<^isub>2' \<le> T\<^isub>2"
      using IH[OF conf wt\<^isub>2] by blast
    ultimately show ?thesis by(fastsimp intro:WTrtFAssNT)
  qed
next
  case RedFAss thus ?case by(auto simp del:fun_upd_apply)
next
  case RedFAssNull thus ?case
    by (unfold sconf_def hconf_def) (auto elim!:typeof_NullPointer simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case (CallObj e s ta e' s' M es T E)
  have red: "extTA,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,hp s' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> s \<surd>" and wt: "P,E,hp s \<turnstile> e\<bullet>M(es) : T" by fact+
  -- "We distinguish if @{term e} has type @{term NT} or a Class type"
  -- "Remember ?case = @{term ?case}"
  from wt show ?case
  proof(rule WTrt_elim_cases)
    fix C Ts pns body D Us
    assume wte: "P,E,hp s \<turnstile> e : Class C"
      and method: "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D"
      and wtes: "P,E,hp s \<turnstile> es [:] Us" and subs: "P \<turnstile> Us [\<le>] Ts"
      and nexc: "\<not> is_external_call P (Class C) M"
    obtain U where wte': "P,E,hp s' \<turnstile> e' : U" and UsubC: "P \<turnstile> U \<le> Class C"
      using IH[OF conf wte] by blast
    -- "Is @{term U} the null type or a class type?"
    { assume "U = NT"
      moreover have "P,E,hp s' \<turnstile> es [:] Us"
	by(rule WTrts_hext_mono[OF wtes red_hext_incr[OF red]])
      ultimately have ?case using wte' by(blast intro!:WTrtCallNT) }
    moreover
    { fix C' assume UClass: "U = Class C'" and "subclass": "P \<turnstile> C' \<preceq>\<^sup>* C"
      have "P,E,hp s' \<turnstile> e' : Class C'" using wte' UClass by auto
      moreover obtain Ts' T' pns' body' D'
	where method': "P \<turnstile> C' sees M:Ts'\<rightarrow>T' = (pns',body') in D'"
	and subs': "P \<turnstile> Ts [\<le>] Ts'" and sub': "P \<turnstile> T' \<le> T"
	using Call_lemma[OF method "subclass" wf] by fast
      moreover have "P,E,hp s' \<turnstile> es [:] Us"
	by(rule WTrts_hext_mono[OF wtes red_hext_incr[OF red]])
      moreover from method' "subclass" have "\<not> is_external_call P (Class C') M"
	by(blast dest: external_call_not_sees_method[OF wf])
      ultimately have ?thesis
	using subs by(blast intro:WTrtCall rtrancl_trans widens_trans) }
    moreover
    { fix A assume "U = A\<lfloor>\<rceil>"
      with UsubC have "C = Object" by(auto dest: Array_widen)
      with method have False by(auto intro: wf_Object_method_empty[OF wf]) }
    ultimately show ?thesis using UsubC by(auto simp add:widen_Class)
  next
    fix Ts
    assume "P,E,hp s \<turnstile> e:NT"
    hence "P,E,hp s' \<turnstile> e' : NT" using IH[OF conf] by fastsimp
    moreover
    fix Ts assume wtes: "P,E,hp s \<turnstile> es [:] Ts"
    have "P,E,hp s' \<turnstile> es [:] Ts"
      by(rule WTrts_hext_mono[OF wtes red_hext_incr[OF red]])
    ultimately show ?thesis by(blast intro!:WTrtCallNT)
  next
    fix U Ts
    assume wte: "P,E,hp s \<turnstile> e : U" and wtes: "P,E,hp s \<turnstile> es [:] Ts"
      and wtext: "P \<turnstile> U\<bullet>M(Ts) :: T"
    from IH[OF conf wte] obtain U' where wte': "P,E,hp s' \<turnstile> e' : U'" 
      and U': "P \<turnstile> U' \<le> U" by(blast)
    note wtes' = WTrts_hext_mono[OF wtes red_hext_incr[OF red]]
    show ?thesis
    proof(cases "U' = NT")
      case True
      with wte' wtes' show ?thesis by(blast intro: WTrtCallNT)
    next
      case False
      with wtext U' have "\<exists>T'. P \<turnstile> U'\<bullet>M(Ts) :: T' \<and> P \<turnstile> T' \<le> T"
	by(blast intro: external_WTrt_widen_mono widens_refl)
      with wte' wtes' show ?thesis by(blast intro: WTrtCallExternal)
    qed
  qed
next
  case (CallParams es s ta es' s' v M T E)
  have reds: "extTA,P \<turnstile> \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>"
   and IH: "\<And>Ts E. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> es [:] Ts\<rbrakk>
           \<Longrightarrow> \<exists>Ts'. P,E,hp s' \<turnstile> es' [:] Ts' \<and> P \<turnstile> Ts' [\<le>] Ts"
   and conf: "P,E \<turnstile> s \<surd>" and wt: "P,E,hp s \<turnstile> Val v\<bullet>M(es) : T" by fact+
  from wt show ?case
  proof (rule WTrt_elim_cases)
    fix C Ts pns body D Us
    assume wte: "P,E,hp s \<turnstile> Val v : Class C"
      and "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D"
      and wtes: "P,E,hp s \<turnstile> es [:] Us" and "P \<turnstile> Us [\<le>] Ts"
      and nexc: "\<not> is_external_call P (Class C) M"
    moreover have "P,E,hp s' \<turnstile> Val v : Class C"
      by(rule WTrt_hext_mono[OF wte reds_hext_incr[OF reds]])
    moreover obtain Us' where "P,E,hp s' \<turnstile> es' [:] Us'" "P \<turnstile> Us' [\<le>] Us"
      using IH[OF conf wtes] by blast
    ultimately show ?thesis using nexc by(fastsimp intro:WTrtCall widens_trans)
  next
    fix Us
    assume null: "P,E,hp s \<turnstile> Val v : NT" and wtes: "P,E,hp s \<turnstile> es [:] Us"
    from null have "v = Null" by simp
    moreover
    obtain Us' where "P,E,hp s' \<turnstile> es' [:] Us' \<and> P \<turnstile> Us' [\<le>] Us"
      using IH[OF conf wtes] by blast
    ultimately show ?thesis by(fastsimp intro:WTrtCallNT)
  next
    fix U Ts
    assume wte: "P,E,hp s \<turnstile> Val v : U" 
      and wtes: "P,E,hp s \<turnstile> es [:] Ts"
      and wtext: "P \<turnstile> U\<bullet>M(Ts) :: T"
    from IH[OF conf wtes] obtain Ts' where wtes': "P,E,hp s' \<turnstile> es' [:] Ts'"
      and sub: "P \<turnstile> Ts' [\<le>] Ts" by blast
    from wte reds_hext_incr[OF reds] have wte': "P,E,hp s' \<turnstile> Val v : U"
      by(rule WTrt_hext_mono)
    show ?thesis
    proof(cases "U = NT")
      case True
      with wtes' wte' show ?thesis by(fastsimp intro: WTrtCallNT)
    next
      case False
      with wtext sub wtes' wte' have "\<exists>T'. P \<turnstile> U\<bullet>M(Ts') :: T' \<and> P \<turnstile> T' \<le> T"
	by(blast intro: external_WTrt_widen_mono)
      with wtes' wte' show ?thesis by(auto intro: WTrtCallExternal)
    qed
  qed
next
  case (RedCall s a C fs M Ts T pns body D vs T' E)
  have hp: "hp s a = Some(Obj C fs)"
    and method: "P \<turnstile> C sees M: Ts\<rightarrow>T = (pns,body) in D"
    and wt: "P,E,hp s \<turnstile> addr a\<bullet>M(map Val vs) : T'" 
    and nexc: "\<not> is_external_call P (Class C) M" by fact+
  obtain Ts' where wtes: "P,E,hp s \<turnstile> map Val vs [:] Ts'"
    and subs: "P \<turnstile> Ts' [\<le>] Ts" and T'isT: "T' = T"
    using wt method hp wf nexc
    by(fastsimp elim!: WTrt_elim_cases dest: sees_method_fun external_WT_is_external_call map_eq_imp_length_eq' intro: widens_refl)
  from wtes subs have length_vs: "length vs = length Ts"
    by(auto simp add: WTrts_conv_list_all2 dest!: list_all2_lengthD)
  from sees_wf_mdecl[OF wf method] obtain T''
    where wtabody: "P,[this#pns [\<mapsto>] Class D#Ts] \<turnstile> body :: T''"
    and T''subT: "P \<turnstile> T'' \<le> T" and length_pns: "length pns = length Ts"
    by(fastsimp simp:wf_mdecl_def simp del:map_upds_twist)
  from wtabody have "P,empty(this#pns [\<mapsto>] Class D#Ts),hp s \<turnstile> body : T''"
    by(rule WT_implies_WTrt)
  hence "P,E(this#pns [\<mapsto>] Class D#Ts),hp s \<turnstile> body : T''"
    by(rule WTrt_env_mono) simp
  hence "P,E,hp s \<turnstile> blocks(this#pns, Class D#Ts, Addr a#vs, body) : T''"
    using wtes subs hp sees_method_decl_above[OF method] length_vs length_pns
    by(fastsimp simp add:wt_blocks rel_list_all2_Cons2)
  with T''subT T'isT show ?case by blast
next
  case RedCallExternal thus ?case
    by(auto split: heapobj.split_asm dest: red_external_conf_extRet[OF wf] intro: wt_external_call intro!: external_WT'.intros simp add: sconf_def hconf_def)
next
  case RedCallNull thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_NullPointer simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case (BlockRed e h x V vo ta e' h' x' T T' E)
  note IH = `\<And>T E. \<lbrakk>P,E \<turnstile> (h, x(V := vo)) \<surd>; P,E,hp (h, x(V := vo)) \<turnstile> e : T\<rbrakk>
             \<Longrightarrow> \<exists>T'. P,E,hp (h', x') \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T`[simplified]
  from `P,E,hp (h, x) \<turnstile> {V:T=vo; e} : T'` have "P,E(V\<mapsto>T),h \<turnstile> e : T'" by(cases vo, auto)
  moreover from `P,E \<turnstile> (h, x) \<surd>` `P,E,hp (h, x) \<turnstile> {V:T=vo; e} : T'`
  have "P,(E(V \<mapsto> T)) \<turnstile> (h, x(V := vo)) \<surd>"
    by(cases vo)(simp add: lconf_def sconf_def,auto simp add: sconf_def conf_def intro: lconf_upd2)
  ultimately obtain T'' where wt': "P,E(V\<mapsto>T),h' \<turnstile> e' : T''" "P \<turnstile> T'' \<le> T'"
    by(auto dest: IH)
  { fix v
    assume vo: "x' V = \<lfloor>v\<rfloor>"
    from `P,(E(V \<mapsto> T)) \<turnstile> (h, x(V := vo)) \<surd>` `extTA,P \<turnstile> \<langle>e,(h, x(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>` `P,E(V\<mapsto>T),h \<turnstile> e : T'`
    have "P,(E(V \<mapsto> T)) \<turnstile> (h', x') \<surd>" by(auto simp add: sconf_def dest: red_preserves_hconf red_preserves_lconf)
    with vo have "\<exists>T'. typeof\<^bsub>h'\<^esub> v = \<lfloor>T'\<rfloor> \<and> P \<turnstile> T' \<le> T" by(fastsimp simp add: sconf_def lconf_def conf_def)
    then obtain T' where "typeof\<^bsub>h'\<^esub> v = \<lfloor>T'\<rfloor>" "P \<turnstile> T' \<le> T" by blast
    hence ?case using wt' vo by(auto) }
  moreover
  { assume "x' V = None" with wt' have ?case by(auto) }
  ultimately show ?case by blast
next 
  case RedBlock thus ?case by auto
next
  case (SynchronizedRed1 o' s ta o'' s' e T E)
  have red: "extTA,P \<turnstile> \<langle>o',s\<rangle> -ta\<rightarrow> \<langle>o'',s'\<rangle>" by fact
  have IH: "\<And>T E. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> o' : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> o'' : T' \<and> P \<turnstile> T' \<le> T" by fact
  have conf: "P,E \<turnstile> s \<surd>" by fact
  have wt: "P,E,hp s \<turnstile> sync(o') e : T" by fact+
  thus ?case
  proof(rule WTrt_elim_cases)
    fix To
    assume wto: "P,E,hp s \<turnstile> o' : To"
      and refT: "is_refT To" 
      and wte: "P,E,hp s \<turnstile> e : T"
    from IH[OF conf wto] obtain To' where "P,E,hp s' \<turnstile> o'' : To'" and sub: "P \<turnstile> To' \<le> To" by auto
    moreover have "P,E,hp s' \<turnstile> e : T"
      by(rule WTrt_hext_mono[OF wte red_hext_incr[OF red]])
    moreover have "is_refT To'" using refT sub by(auto intro: widen_refT)
    ultimately show ?thesis
      apply(cases "To' = NT")
       apply(fastsimp intro: WTrtSynchronizedNT widen_refl)
      apply(rule exI)
      apply(rule conjI[OF _ widen_refl])
      by(erule WTrtSynchronized)
  next
    fix Te
    assume wto: "P,E,hp s \<turnstile> o' : NT"
      and wte: "P,E,hp s \<turnstile> e : Te"
    from IH[OF conf wto] have "P,E,hp s' \<turnstile> o'' : NT" by(clarsimp)
    moreover have "P,E,hp s' \<turnstile> e : Te"
      by(rule WTrt_hext_mono[OF wte red_hext_incr[OF red]])
    ultimately show ?thesis by(auto)
  qed
next
  case SynchronizedNull thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_NullPointer simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case (LockSynchronized s a arrobj e T E) thus ?case 
    by(cases arrobj)(auto)
next
  case (SynchronizedRed2 e s ta e' s' a T E)
  have red: "extTA,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by fact
  have IH: "\<And>T E. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T" by fact
  have conf: "P,E \<turnstile> s \<surd>" by fact
  have wt: "P,E,hp s \<turnstile> insync(a) e : T" by fact
  thus ?case
  proof(rule WTrt_elim_cases)
    fix Ta arrobj
    assume "P,E,hp s \<turnstile> e : T"
      and hpa: "hp s a = \<lfloor>arrobj\<rfloor>"
      and arrobj: "(case arrobj of Obj C fs \<Rightarrow> \<lfloor>Class C\<rfloor> | Arr t e \<Rightarrow> \<lfloor>t\<lfloor>\<rceil>\<rfloor>) = \<lfloor>Ta\<rfloor>"
    from `P,E,hp s \<turnstile> e : T` conf obtain T'
      where "P,E,hp s' \<turnstile> e' : T'" "P \<turnstile> T' \<le> T" by(blast dest: IH)
    moreover from conf red have hext: "hp s \<unlhd> hp s'" by(auto dest: red_hext_incr)
    from hpa arrobj have "P,E,hp s' \<turnstile> addr a : Ta"
      by-(rule WTrt_hext_mono[OF _ hext], auto)
    ultimately show ?thesis by auto
  qed
next
  case UnlockSynchronized thus ?case
    by(auto split: heapobj.split_asm)
next
  case SeqRed thus ?case
    apply(auto)
    apply(drule WTrt_hext_mono[OF _ red_hext_incr], assumption)
    by auto
next
  case (CondRed b s ta b' s' e1 e2 T E)
  have red: "extTA,P \<turnstile> \<langle>b,s\<rangle> -ta\<rightarrow> \<langle>b',s'\<rangle>" by fact
  have IH: "\<And>T E. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> b : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> b' : T' \<and> P \<turnstile> T' \<le> T" by fact
  have conf: "P,E \<turnstile> s \<surd>" by fact
  have wt: "P,E,hp s \<turnstile> if (b) e1 else e2 : T" by fact
  thus ?case
  proof(rule WTrt_elim_cases)
    fix T1 T2
    assume wtb: "P,E,hp s \<turnstile> b : Boolean"
      and wte1: "P,E,hp s \<turnstile> e1 : T1"
      and wte2: "P,E,hp s \<turnstile> e2 : T2"
      and comp: "P \<turnstile> T1 \<le> T2 \<or> P \<turnstile> T2 \<le> T1"
      and tt2: "P \<turnstile> T1 \<le> T2 \<longrightarrow> T = T2"
      and tt1: "P \<turnstile> T2 \<le> T1 \<longrightarrow> T = T1"
    from IH[OF conf wtb] have "P,E,hp s' \<turnstile> b' : Boolean" by(auto)
    moreover have "P,E,hp s' \<turnstile> e1 : T1"
      by(rule WTrt_hext_mono[OF wte1 red_hext_incr[OF red]])
    moreover have "P,E,hp s' \<turnstile> e2 : T2"
      by(rule WTrt_hext_mono[OF wte2 red_hext_incr[OF red]])
    ultimately show ?thesis using comp tt2 tt1 by(fastsimp)
  qed
next
  case (ThrowRed e s ta e' s' T E)
  have IH: "\<And>T E. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T" by fact
  have conf: "P,E \<turnstile> s \<surd>" by fact
  have wt: "P,E,hp s \<turnstile> throw e : T" by fact
  then obtain T'
    where wte: "P,E,hp s \<turnstile> e : T'" 
    and nobject: "P \<turnstile> T' \<le> Class Throwable" by auto
  from IH[OF conf wte] obtain T'' 
    where wte': "P,E,hp s' \<turnstile> e' : T''"
    and PT'T'': "P \<turnstile> T'' \<le> T'" by blast
  from nobject PT'T'' have "P \<turnstile> T'' \<le> Class Throwable"
    by(auto simp add: widen_Class)(erule notE, rule rtranclp_trans)
  hence "P,E,hp s' \<turnstile> throw e' : T" using wte' PT'T''
    by -(erule WTrtThrow)
  thus ?case by(auto)
next
  case RedThrowNull thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_NullPointer simp add: xcpt_subcls_Throwable[OF _ wf])
next
  case (TryRed e s ta e' s' C V e2 T E)
  have red: "extTA,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by fact
  have IH: "\<And>T E. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T" by fact
  have conf: "P,E \<turnstile> s \<surd>" by fact
  have wt: "P,E,hp s \<turnstile> try e catch(C V) e2 : T" by fact
  thus ?case
  proof(rule WTrt_elim_cases)
    fix T1
    assume wte: "P,E,hp s \<turnstile> e : T1"
      and wte2: "P,E(V \<mapsto> Class C),hp s \<turnstile> e2 : T"
      and sub: "P \<turnstile> T1 \<le> T"
    from IH[OF conf wte] obtain T1' where "P,E,hp s' \<turnstile> e' : T1'" and "P \<turnstile> T1' \<le> T1" by(auto)
    moreover have "P,E(V \<mapsto> Class C),hp s' \<turnstile> e2 : T"
      by(rule WTrt_hext_mono[OF wte2 red_hext_incr[OF red]])
    ultimately show ?thesis using sub by(auto elim: widen_trans)
  qed
next
  case RedTryFail thus ?case
    by(fastsimp intro: WTrtThrow[OF WTrtVal] simp:sconf_def hconf_def)
next
  case RedSeq thus ?case by auto
next
  case RedCondT thus ?case by auto
next
  case RedCondF thus ?case by auto
next
  case RedWhile thus ?case by(fastsimp) 
next
  case RedTry thus ?case by auto
next
  case RedTryCatch thus ?case by(fastsimp)
next
  case (ListRed1 e s ta e' s' es Ts E)
  note IH = `\<And>T E. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T`
  from `P,E,hp s \<turnstile> e # es [:] Ts` obtain T Ts' where "Ts = T # Ts'" "P,E,hp s \<turnstile> e : T" "P,E,hp s \<turnstile> es [:] Ts'" by auto
  with IH[of E T] `P,E \<turnstile> s \<surd>` WTrts_hext_mono[OF `P,E,hp s \<turnstile> es [:] Ts'` red_hext_incr[OF `extTA,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`]]
  show ?case by(auto simp add: list_all2_Cons2 intro: widens_refl)
next
  case ListRed2 thus ?case
    by(fastsimp dest: hext_typeof_mono[OF reds_hext_incr])
qed(fastsimp)+

subsection {* Lifting to @{text"\<rightarrow>*"} *}

text{* Now all these preservation lemmas are first lifted to the transitive
closure \dots *}

lemma Step_induct' [consumes 1, case_names refl step]:
  assumes red: "extTA,P \<turnstile> \<langle>e, s\<rangle> -tas\<rightarrow>* \<langle>e', s'\<rangle>"
  and refl: "\<And>e s. Q e s [] e s"
  and step: "\<And>e s tas e' s' ta e'' s''. \<lbrakk> extTA,P \<turnstile> \<langle>e, s\<rangle> -tas\<rightarrow>* \<langle>e', s'\<rangle>; Q e s tas e' s'; extTA,P \<turnstile> \<langle>e', s'\<rangle> -ta\<rightarrow> \<langle>e'', s''\<rangle> \<rbrakk> \<Longrightarrow> Q e s (tas @ [ta]) e'' s''"
  shows "Q e s tas e' s'"
using red
apply -
apply(drule rtrancl3p.induct[where P="\<lambda>(e, s) ta (e', s'). Q e s ta e' s'"])
 apply(case_tac a, fastsimp intro: refl)
by(auto intro: step)


lemma Red_preserves_sconf_and_WT:
assumes wf: "wf_J_prog P"
shows "\<lbrakk> extTA,P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow>* \<langle>e',s'\<rangle>; P,E,hp s \<turnstile> e : T; P,E \<turnstile> s \<surd> \<rbrakk> 
       \<Longrightarrow> P,E \<turnstile> s' \<surd> \<and> (\<exists>T'. P,E,hp s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)"
(*<*)
proof(induct arbitrary: T rule: Step_induct')
  case refl thus ?case by blast
next
  case (step e s tas e' s' ta e'' s'' T)
  have Red: "extTA,P \<turnstile> \<langle>e, s\<rangle> -tas\<rightarrow>* \<langle>e', s'\<rangle>" by fact
  have IH: "\<And>T. \<lbrakk>P,E,hp s \<turnstile> e : T; P,E \<turnstile> s \<surd>\<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd> \<and> (\<exists>T'. P,E,hp s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)" by fact
  have red: "extTA,P \<turnstile> \<langle>e',s'\<rangle> -ta\<rightarrow> \<langle>e'',s''\<rangle>" by fact
  have wt: "P,E,hp s \<turnstile> e : T" by fact
  have conf: "P,E \<turnstile> s \<surd>" by fact
  from IH[OF wt conf] have conf': "P,E \<turnstile> s' \<surd>" and "\<exists>T'. P,E,hp s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T " by(auto)
  then obtain T' where wte': "P,E,hp s' \<turnstile> e' : T'" and sub: "P \<turnstile> T' \<le> T" by blast
  with red conf' wf have "\<exists>T''. P,E,hp s'' \<turnstile> e'' : T'' \<and> P \<turnstile> T'' \<le> T'" by-(rule subject_reduction)
  with red conf' wte' sub show ?case by(auto intro: red_preserves_sconf widen_trans)
qed

lemma Red_preserves_defass:
assumes wf: "wf_J_prog P" and reds: "extTA,P \<turnstile> \<langle>e,s\<rangle> -tas\<rightarrow>* \<langle>e',s'\<rangle>"
shows "\<D> e \<lfloor>dom(lcl s)\<rfloor> \<Longrightarrow> \<D> e' \<lfloor>dom(lcl s')\<rfloor>"
using reds
proof (induct rule:Step_induct')
  case refl thus ?case .
next
  case step
  thus ?case
    by(fastsimp intro:red_preserves_defass[OF wf])
qed

lemma Red_preserves_type:
  "\<lbrakk> wf_J_prog P; extTA,P \<turnstile> \<langle>e,s\<rangle> -tas\<rightarrow>* \<langle>e',s'\<rangle>; P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e:T \<rbrakk>
    \<Longrightarrow> \<exists>T'. P \<turnstile> T' \<le> T \<and> P,E,hp s' \<turnstile> e':T'"
by(auto dest!: Red_preserves_sconf_and_WT)


subsection "The final polish"

text{* The above preservation lemmas are now combined and packed nicely. *}

constdefs
  wf_config :: "J_prog \<Rightarrow> env \<Rightarrow> Jstate \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"   ("_,_,_ \<turnstile> _ : _ \<surd>"   [51,0,0,0,0]50)
  "P,E,s \<turnstile> e:T \<surd>  \<equiv>  P,E \<turnstile> s \<surd> \<and> P,E,hp s \<turnstile> e:T"

theorem Subject_reduction: assumes wf: "wf_J_prog P"
shows "extTA,P \<turnstile> \<langle>e,s\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P,E,s \<turnstile> e : T \<surd>
       \<Longrightarrow> \<exists>T'. P,E,s' \<turnstile> e' : T' \<surd> \<and> P \<turnstile> T' \<le> T"
(*<*)
by(force simp add: wf_config_def
   elim:red_preserves_sconf dest:subject_reduction[OF wf])
(*>*)


theorem Subject_reductions:
assumes wf: "wf_J_prog P" and reds: "extTA,P \<turnstile> \<langle>e,s\<rangle> -tas\<rightarrow>* \<langle>e',s'\<rangle>"
shows "\<And>T. P,E,s \<turnstile> e:T \<surd> \<Longrightarrow> \<exists>T'. P,E,s' \<turnstile> e':T' \<surd> \<and> P \<turnstile> T' \<le> T"
(*<*)
using reds
proof (induct rule:Step_induct')
  case refl thus ?case by blast
next
  case step thus ?case
    by(blast dest:Subject_reduction[OF wf] intro:widen_trans)
qed
(*>*)


corollary Progress: assumes wf: "wf_J_prog P"
shows "\<lbrakk> P,E,s  \<turnstile> e : T \<surd>; \<D> e \<lfloor>dom(lcl s)\<rfloor>; \<not> final e \<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P \<turnstile> \<langle>e,s\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
(*<*)
using progress[OF wf_prog_wwf_prog[OF wf]]
by(auto simp:wf_config_def sconf_def)
(*>*)


corollary TypeSafety:
  "\<lbrakk> wf_J_prog P; P,E \<turnstile> s \<surd>; P,E \<turnstile> e::T; \<D> e \<lfloor>dom(lcl s)\<rfloor>;
     extTA,P \<turnstile> \<langle>e,s\<rangle> -tas\<rightarrow>* \<langle>e',s'\<rangle>; \<not>(\<exists>e'' s'' ta. extTA,P \<turnstile> \<langle>e',s'\<rangle> -ta\<rightarrow> \<langle>e'',s''\<rangle>) \<rbrakk>
 \<Longrightarrow> (\<exists>v. e' = Val v \<and> P,hp s' \<turnstile> v :\<le> T) \<or>
      (\<exists>a. e' = Throw a \<and> a \<in> dom(hp s'))"
(*<*)
apply(subgoal_tac " P,E,s \<turnstile> e:T \<surd>")
 prefer 2
 apply(fastsimp simp:wf_config_def dest:WT_implies_WTrt)
apply(frule (2) Subject_reductions)
apply(erule exE conjE)+
apply(frule (2) Red_preserves_defass)
apply(subgoal_tac "final e'")
 prefer 2
 apply(blast dest: Progress)
apply(erule finalE)
 apply(fastsimp simp add: wf_config_def elim: conf_widen dest: typeof_conf)
by(clarsimp simp add: wf_config_def conf_def)
(*>*)


end
