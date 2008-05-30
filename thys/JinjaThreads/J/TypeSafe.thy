(*  Title:      Jinja/J/SmallTypeSafe.thy
    ID:         $Id: TypeSafe.thy,v 1.4 2008-05-30 00:29:30 makarius Exp $
    Author:     Tobias Nipkow, Andreas Lochbihler
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* \isaheader{Type Safety Proof} *}

theory TypeSafe
imports Progress JWellForm
begin
subsection{*Basic preservation lemmas*}

text{* First two easy preservation lemmas. *}

theorem red_preserves_hconf:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; P,E,hp s \<turnstile> e : T; P \<turnstile> hp s \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> hp s' \<surd>"
proof (induct arbitrary: T E rule: red.induct)
  case (RedNew h a C FDTs h' l T E)
  have new: "new_Addr h = Some a" and fields: "P \<turnstile> C has_fields FDTs" by fact+
  have h': "h' = h(a\<mapsto>(Obj C (init_fields FDTs)))" by fact
  have hconf: "P \<turnstile> hp (h, l) \<surd>" by fact
  from new have None: "h a = None" by(rule new_Addr_SomeD)
  moreover have "P,h \<turnstile> (Obj C (init_fields FDTs)) \<surd>"
    using fields by(rule oconf_init_fields)
  ultimately show "P \<turnstile> hp (h', l) \<surd>" using h' hconf apply(simp) by(rule hconf_new)
next
  case (RedNewArray h a i h' T l T' E)
  have new: "new_Addr h = Some a"
    and isize: "0 \<le> i"
    and h': "h' = h(a \<mapsto> Arr T i (\<lambda>i. default_val T))"
    and hconf: "P \<turnstile> hp (h, l) \<surd>" by fact+
  have wt: "P,E,hp (h, l) \<turnstile> newA T\<lfloor>Val (Intg i)\<rceil> : T'" by fact
  from new have None: "h a = None" by(rule new_Addr_SomeD)
  moreover 
  from wt have "is_type P T" by(auto)
  hence "P,h \<turnstile> (Arr T i (\<lambda>i. default_val T)) \<surd>"
    by -(rule oconf_init_arr)
  ultimately show "P \<turnstile> hp (h', l) \<surd>" using h' hconf apply(simp) by(rule hconf_new)
next
  case (RedAAss h a T s el i w U h' l T' E)
  let ?el' = "el(i := w)"
  have hconf: "P \<turnstile> hp (h, l) \<surd>" and ha: "h a = Some(Arr T s el)"
    and "0 \<le> i" and "i < s"
    and "typeof\<^bsub>h\<^esub> w = \<lfloor>U\<rfloor>" and "P \<turnstile> U \<le> T"
    and h': "h' = h(a \<mapsto> Arr T s (el(i := w)))"
    and wt: "P,E,hp (h,l) \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> := Val w : T'" by fact+
  have "P,h \<turnstile> (Arr T s ?el') \<surd>"
  proof (rule oconf_fupd_arr)
    from prems show "0 \<le> i" by simp
  next
    from prems show "i < s" by simp
  next
    from prems show "P,h \<turnstile> w :\<le> T" by (simp add: conf_def)
  next
    from prems show "P,h \<turnstile> Arr T s el \<surd>" by (simp add: hconf_def)
  qed
  with hconf ha h' have "P \<turnstile> h(a\<mapsto>(Arr T s (el(i := w)))) \<surd>" by - (rule hconf_upd_arr, auto)
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
  with hconf ha show ?case  apply (simp del: fun_upd_apply) by(rule hconf_upd_obj)
next
  case (CallParams e s ta e' s' v M vs es T E)
  have IH: "\<And>T E. \<lbrakk>P,E,hp s \<turnstile> e : T; P \<turnstile> hp s \<surd>\<rbrakk> \<Longrightarrow> P \<turnstile> hp s' \<surd>" by fact
  have wte: "P,E,hp s \<turnstile> Val v\<bullet>M(map Val vs @ e # es) : T" by fact
  have hconf: "P \<turnstile> hp s \<surd>" by fact
  from hconf wte show ?case
    apply -
    apply(erule WTrt_elim_cases)
       apply(clarsimp simp add: list_all2_append1 list_all2_Cons1 simp del: hp_def)
       apply(erule IH, assumption)
      apply(clarsimp simp add: list_all2_append1 list_all2_Cons1 simp del: hp_def)
      apply(erule IH, assumption)
     apply(auto)
    done
qed auto
(*>*)


theorem red_preserves_lconf:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>; P,E,hp s \<turnstile> e:T; P,hp s \<turnstile> lcl s (:\<le>) E \<rbrakk> \<Longrightarrow> P,hp s' \<turnstile> lcl s' (:\<le>) E"
proof(induct arbitrary: T E rule:red.induct)
  case RedNew thus ?case
    by(fastsimp intro:lconf_hext red_hext_incr[OF red.RedNew, simplified] simp del: fun_upd_apply)
next
  case RedNewArray thus ?case
    by(fastsimp intro:lconf_hext red_hext_incr[OF red.RedNewArray, simplified] simp del: fun_upd_apply)
next
  case RedLAss thus ?case 
    by(fastsimp elim: lconf_upd simp add: conf_def simp del: fun_upd_apply )
next
  case RedAAss thus ?case
    by(fastsimp intro:lconf_hext red_hext_incr[OF red.RedAAss, simplified] simp del: fun_upd_apply)
next
  case RedFAss thus ?case
    by(fastsimp intro:lconf_hext red_hext_incr[OF red.RedFAss, simplified] simp del: fun_upd_apply)
next
  case CallParams
  thus ?case by(auto simp add: list_all2_append1 list_all2_Cons1)
next
  case (InitBlockRed  e h l V v ta e' h' l' v' T T' E)
  have red: "P \<turnstile> \<langle>e, (h, l(V\<mapsto>v))\<rangle> -ta\<rightarrow> \<langle>e',(h', l')\<rangle>"
   and IH: " \<And>T E. \<lbrakk>P,E,hp (h, l(V \<mapsto> v)) \<turnstile> e : T; P,hp (h, l(V \<mapsto> v)) \<turnstile> lcl (h, l(V \<mapsto> v)) (:\<le>) E\<rbrakk>
              \<Longrightarrow> P,hp (h', l') \<turnstile> lcl (h', l') (:\<le>) E"
   and l'V: "l' V = Some v'" and lconf: "P,hp (h, l) \<turnstile> lcl (h, l) (:\<le>) E"
   and wt: "P,E,hp (h, l) \<turnstile> {V:T := Val v; e} : T'" by fact+
  from lconf_hext[OF lconf[simplified] red_hext_incr[OF red, simplified]]
  have "P,h' \<turnstile> l (:\<le>) E" .
  moreover from IH lconf wt have "P,h' \<turnstile> l' (:\<le>) E(V\<mapsto>T)"
    by(auto simp del: fun_upd_apply simp: fun_upd_same lconf_upd2 conf_def)
  ultimately show ?case
    by (fastsimp simp:lconf_def split:split_if_asm)
next
  case (BlockRedNone e h l V ta e' h' l' T T' E)
  have red: "P \<turnstile> \<langle>e,(h, l(V := None))\<rangle> -ta\<rightarrow> \<langle>e',(h', l')\<rangle>"
   and IH: "\<And>E T. \<lbrakk> P,E,hp (h, l(V := None)) \<turnstile> e : T; P,hp (h, l(V := None)) \<turnstile> lcl (h, l(V:=None)) (:\<le>) E \<rbrakk>
                   \<Longrightarrow> P,hp (h', l') \<turnstile> lcl (h', l') (:\<le>) E"
   and lconf: "P,hp (h, l) \<turnstile> lcl (h, l) (:\<le>) E" and wt: "P,E,hp (h, l) \<turnstile> {V:T; e} : T'" by fact+
  from lconf_hext[OF lconf[simplified] red_hext_incr[OF red, simplified]]
  have "P,h' \<turnstile> l (:\<le>) E" .
  moreover have "P,h' \<turnstile> l' (:\<le>) E(V\<mapsto>T)"
    by(rule IH[simplified], insert lconf wt, auto simp:lconf_def)
  ultimately show ?case
    by (fastsimp simp:lconf_def split:split_if_asm)
next
  case (BlockRedSome e h l V ta e' h' l' v T T' E)
  have red: "P \<turnstile> \<langle>e,(h, l(V := None))\<rangle> -ta\<rightarrow> \<langle>e',(h', l')\<rangle>"
   and IH: "\<And>T E. \<lbrakk>P,E,hp (h, l(V := None)) \<turnstile> e : T; P,hp (h, l(V := None)) \<turnstile> lcl (h, l(V := None)) (:\<le>) E\<rbrakk>
              \<Longrightarrow> P,hp (h', l') \<turnstile> lcl (h', l') (:\<le>) E"
   and lconf: "P,hp (h, l) \<turnstile> lcl (h, l) (:\<le>) E" and wt: "P,E,hp (h, l) \<turnstile> {V:T; e} : T'" by fact+
  from lconf_hext[OF lconf[simplified] red_hext_incr[OF red, simplified]]
  have "P,h' \<turnstile> l (:\<le>) E" .
  moreover have "P,h' \<turnstile> l' (:\<le>) E(V\<mapsto>T)"
    by(rule IH[simplified], insert lconf wt, auto simp:lconf_def)
  ultimately show ?case
    by (fastsimp simp:lconf_def split:split_if_asm)
qed auto



text{* Preservation of definite assignment more complex and requires a
few lemmas first. *}

lemma [iff]: "\<And>A. \<lbrakk> length Vs = length Ts; length vs = length Ts\<rbrakk> \<Longrightarrow>
 \<D> (blocks (Vs,Ts,vs,e)) A = \<D> e (A \<squnion> \<lfloor>set Vs\<rfloor>)"
(*<*)
apply(induct Vs Ts vs e rule:blocks.induct)
apply(simp_all add:hyperset_defs)
done
(*>*)

lemma red_lA_incr: "P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> \<lfloor>dom (lcl s)\<rfloor> \<squnion> \<A> e \<sqsubseteq>  \<lfloor>dom (lcl s')\<rfloor> \<squnion> \<A> e'"
(*<*)
apply(induct rule:red.inducts)
apply(simp_all del:fun_upd_apply add:hyperset_defs)
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply force
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
  apply(fastsimp dest:red_lcl_incr)
 apply(clarsimp)
 apply(rule conjI)
  apply(frule red_lcl_incr)
  apply(fastsimp)
 apply(rule subsetI)
 apply(clarsimp)
 apply(drule_tac A=aca in subsetD)
  apply(assumption)
 apply(fastsimp)
apply(fastsimp dest: red_lcl_incr)
done
(*>*)

text{* Now preservation of definite assignment. *}

lemma assumes wf: "wf_J_prog P"
shows red_preserves_defass: "P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> \<D> e \<lfloor>dom (lcl s)\<rfloor> \<Longrightarrow> \<D> e' \<lfloor>dom (lcl s')\<rfloor>"
proof (induct rule:red.induct)
  case BinOpRed1 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case AAccRed1 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case (AAssRed1 a s ta a' s' i e)
  have ss: "P \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>"
    and IH: "\<D> a \<lfloor>dom (lcl s)\<rfloor> \<Longrightarrow> \<D> a' \<lfloor>dom (lcl s')\<rfloor>"
    and D: "\<D> (a\<lfloor>i\<rceil> := e) \<lfloor>dom (lcl s)\<rfloor>" by fact+
  from D have "\<D> a \<lfloor>dom (lcl s)\<rfloor>" by simp
  with IH have Da: "\<D> a' \<lfloor>dom (lcl s')\<rfloor>" by simp
  from ss have domgrow: "\<lfloor>dom (lcl s)\<rfloor> \<squnion> \<A> a \<sqsubseteq>  \<lfloor>dom (lcl s')\<rfloor> \<squnion> \<A> a'" by - (erule red_lA_incr)
  from D have "\<D> i (\<lfloor>dom (lcl s)\<rfloor> \<squnion> \<A> a)" by simp
  with domgrow have Di: "\<D> i (\<lfloor>dom (lcl s')\<rfloor> \<squnion> \<A> a')" by - (erule D_mono)
  from domgrow have domgrow2: "\<lfloor>dom (lcl s)\<rfloor> \<squnion> \<A> a \<squnion> \<A> i \<sqsubseteq> \<lfloor>dom (lcl s')\<rfloor> \<squnion> \<A> a' \<squnion> \<A> i" by - (rule sqUn_lem)
  from D have "\<D> e (\<lfloor>dom (lcl s)\<rfloor> \<squnion> \<A> a \<squnion> \<A> i)" by simp
  with domgrow2 have De: "\<D> e (\<lfloor>dom (lcl s')\<rfloor> \<squnion> \<A> a' \<squnion> \<A> i)" by - (erule D_mono)
  from Da Di De show ?case by simp
next
  case AAssRed2 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case FAssRed1 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case CallObj thus ?case by (auto elim!: Ds_mono[OF red_lA_incr])
next
  case CallParams thus ?case by(auto elim!: Ds_mono[OF red_lA_incr])
next
  case RedCall thus ?case
    apply (auto dest!:sees_wf_mdecl[OF wf] simp:wf_mdecl_def elim!:D_mono')
    by(auto simp:hyperset_defs)
next
  case InitBlockRed thus ?case
    by(auto simp:hyperset_defs elim!:D_mono' simp del:fun_upd_apply)
next
  case BlockRedNone thus ?case
    by(auto simp:hyperset_defs elim!:D_mono' simp del:fun_upd_apply)
next
  case BlockRedSome thus ?case
    by(auto simp:hyperset_defs elim!:D_mono' simp del:fun_upd_apply)
next
  case SynchronizedRed1 thus ?case by(auto elim!: D_mono[OF red_lA_incr])
next
  case SeqRed thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case CondRed thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case TryRed thus ?case
    by (fastsimp dest:red_lcl_incr intro:D_mono' simp:hyperset_defs)
next
  case RedWhile thus ?case by(auto simp:hyperset_defs elim!:D_mono')
qed (auto simp:hyperset_defs)



text{* Combining conformance of heap and local variables: *}

constdefs
  sconf :: "J_prog \<Rightarrow> env \<Rightarrow> Jstate \<Rightarrow> bool"   ("_,_ \<turnstile> _ \<surd>"   [51,51,51]50)
  "P,E \<turnstile> s \<surd>  \<equiv>  let (h,l) = s in P \<turnstile> h \<surd> \<and> P,h \<turnstile> l (:\<le>) E"

lemma red_preserves_sconf:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>; P,E,hp s \<turnstile> e : T; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"
(*<*)
by(fastsimp dest:red_preserves_hconf red_preserves_lconf
            simp add:sconf_def)
(*>*)


subsection "Subject reduction"

lemma wt_blocks:
 "\<And>E. \<lbrakk> length Vs = length Ts; length vs = length Ts \<rbrakk> \<Longrightarrow>
       (P,E,h \<turnstile> blocks(Vs,Ts,vs,e) : T) =
       (P,E(Vs[\<mapsto>]Ts),h \<turnstile> e:T \<and> (\<exists>Ts'. map (typeof\<^bsub>h\<^esub>) vs = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] Ts))"
apply(induct Vs Ts vs e rule:blocks.induct)
prefer 5 apply (force)
apply simp_all
done

theorem assumes wf: "wf_J_prog P"
shows subject_reduction: "\<lbrakk> P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>; P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e:T \<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> e':T' \<and> P \<turnstile> T' \<le> T"
proof (induct arbitrary: T E rule:red.induct)
  case RedNew
  thus ?case by fastsimp
next
  case RedNewFail thus ?case
  by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_OutOfMemory)
next
  case NewArrayRed
  thus ?case by fastsimp
next
  case RedNewArray
  thus ?case by fastsimp
next
  case RedNewArrayNegative thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_NegativeArraySize)
next
  case RedNewArrayFail thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_OutOfMemory)
next
  case (CastRed e s ta e' s' C T E)
  have esse: "P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" 
    and IH: "\<And>T E. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T"
    and hconf: "P,E \<turnstile> s \<surd>"
    and wtc: "P,E,hp s \<turnstile> Cast C e : T" by fact+
  thus ?case
  proof(clarsimp simp del: hp_def)
    fix T'
    assume wte: "P,E,hp s \<turnstile> e : T'"
    from wte and hconf and IH have "\<exists>U. P,E,hp s' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T'" by simp
    then obtain U where wtee: "P,E,hp s' \<turnstile> e' : U" and UsTT: "P \<turnstile> U \<le> T'" by blast
    from wtee have "P,E,hp s' \<turnstile> Cast T e' : T" by - (rule WTrtCast)
    thus "\<exists>T'. P,E,hp s' \<turnstile> Cast T e' : T' \<and> P \<turnstile> T' \<le> T" by blast
  qed
next
  case RedCast thus ?case
    by(clarsimp simp add: is_refT_def)
next
  case RedCastFail thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_ClassCast)
next
  case (BinOpRed1 e\<^isub>1 s ta e\<^isub>1' s' bop e\<^isub>2 T E)
  have red: "P \<turnstile> \<langle>e\<^isub>1, s\<rangle> -ta\<rightarrow> \<langle>e\<^isub>1', s'\<rangle>"
   and IH: "\<And>T E. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e\<^isub>1:T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,hp s' \<turnstile> e\<^isub>1' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> s \<surd>" and wt: "P,E,hp s \<turnstile> e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 : T" by fact+
  have "P,E,hp s' \<turnstile> e\<^isub>1' \<guillemotleft>bop\<guillemotright> e\<^isub>2 : T"
  proof (cases bop)
    assume [simp]: "bop = Eq"
    from wt obtain T\<^isub>1 T\<^isub>2 where [simp]: "T = Boolean"
      and wt\<^isub>1: "P,E,hp s \<turnstile> e\<^isub>1 : T\<^isub>1" and wt\<^isub>2: "P,E,hp s \<turnstile> e\<^isub>2 : T\<^isub>2" by auto
    show ?thesis
      using WTrt_hext_mono[OF wt\<^isub>2 red_hext_incr[OF red]] IH[OF conf wt\<^isub>1]
      by auto
  next
    assume  [simp]: "bop = Add"
    from wt have [simp]: "T = Integer"
      and wt\<^isub>1: "P,E,hp s \<turnstile> e\<^isub>1 : Integer" and wt\<^isub>2: "P,E,hp s \<turnstile> e\<^isub>2 : Integer"
      by auto
    show ?thesis
      using IH[OF conf wt\<^isub>1] WTrt_hext_mono[OF wt\<^isub>2 red_hext_incr[OF red]]
      by auto
  qed
  thus ?case by auto
next
  case (BinOpRed2 e\<^isub>2 s ta e\<^isub>2' s' v\<^isub>1 bop T E)
  have red: "P \<turnstile> \<langle>e\<^isub>2,s\<rangle> -ta\<rightarrow> \<langle>e\<^isub>2',s'\<rangle>" by fact
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e\<^isub>2:T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,hp s' \<turnstile> e\<^isub>2' : U \<and> P \<turnstile> U \<le> T" by fact
  have conf: "P,E \<turnstile> s \<surd>" and wt: "P,E,hp s \<turnstile> (Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> e\<^isub>2 : T" by fact+
  have "P,E,hp s' \<turnstile> (Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> e\<^isub>2' : T"
  proof (cases bop)
    assume [simp]: "bop = Eq"
    from wt obtain T\<^isub>1 T\<^isub>2 where [simp]: "T = Boolean"
      and wt\<^isub>1: "P,E,hp s \<turnstile> Val v\<^isub>1 : T\<^isub>1" and wt\<^isub>2: "P,E,hp s \<turnstile> e\<^isub>2:T\<^isub>2" by auto
    show ?thesis
      using IH[OF conf wt\<^isub>2] WTrt_hext_mono[OF wt\<^isub>1 red_hext_incr[OF red]]
      by auto
  next
    assume  [simp]: "bop = Add"
    from wt have [simp]: "T = Integer"
      and wt\<^isub>1: "P,E,hp s \<turnstile> Val v\<^isub>1 : Integer" and wt\<^isub>2: "P,E,hp s \<turnstile> e\<^isub>2 : Integer"
      by auto
    show ?thesis
      using IH[OF conf wt\<^isub>2] WTrt_hext_mono[OF wt\<^isub>1 red_hext_incr[OF red]]
      by auto
  qed
  thus ?case by auto
next
  case (RedBinOp bop) thus ?case
  proof (cases bop)
    case Eq thus ?thesis using RedBinOp by auto
  next
    case Add thus ?thesis using RedBinOp by auto
  qed
next
  case RedVar thus ?case by (fastsimp simp:sconf_def lconf_def conf_def)
next
  case LAssRed thus ?case by(blast intro:widen_trans)
next
  case RedLAss thus ?case by fastsimp
next
  case (AAccRed1 a s ta a' s' i T E)
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> a : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> a' : T' \<and> P \<turnstile> T' \<le> T"
    and assa: "P \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>"
    and wt: "P,E,hp s \<turnstile> a\<lfloor>i\<rceil> : T"
    and hconf: "P,E \<turnstile> s \<surd>" by fact+
  from wt have wti: "P,E,hp s \<turnstile> i : Integer" by auto
  from wti red_hext_incr[OF assa] have wti': "P,E,hp s' \<turnstile> i : Integer" by - (rule WTrt_hext_mono)
  { assume wta: "P,E,hp s \<turnstile> a : T\<lfloor>\<rceil>"
    from IH[OF hconf wta]
    obtain U where wta': "P,E,hp s' \<turnstile> a' : U" and UsubT: "P \<turnstile> U \<le> T\<lfloor>\<rceil>" by fastsimp
    with wta' wti' have ?case
      apply(cases U, simp_all add: widen_Array)
      apply(fastsimp intro:WTrtAAccNT)
      apply(rule_tac x="ty" in exI)
      apply(erule conjE)
      apply(rule conjI)
      by(erule WTrtAAcc) }
  moreover
  { assume wta: "P,E,hp s \<turnstile> a : NT"
    from IH[OF hconf wta] have "P,E,hp s' \<turnstile> a' : NT" by fastsimp
    from this wti' have ?case
      by(fastsimp intro:WTrtAAccNT) }
  ultimately show ?case using wt by auto
next
  case (AAccRed2 i s ta i' s' a T E)
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> i : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> i' : T' \<and> P \<turnstile> T' \<le> T"
    and issi: "P \<turnstile> \<langle>i,s\<rangle> -ta\<rightarrow> \<langle>i',s'\<rangle>"
    and wt: "P,E,hp s \<turnstile> Val a\<lfloor>i\<rceil> : T"
    and hconf: "P,E \<turnstile> s \<surd>" by fact+
  from wt have wti: "P,E,hp s \<turnstile> i : Integer" by auto
  from wti IH hconf have wti': "P,E,hp s' \<turnstile> i' : Integer" by blast
  from wt show ?case
  proof (rule WTrt_elim_cases)
    assume wta: "P,E,hp s \<turnstile> Val a : T\<lfloor>\<rceil>"
    from wta red_hext_incr[OF issi] have wta': "P,E,hp s' \<turnstile> Val a : T\<lfloor>\<rceil>" by (rule WTrt_hext_mono)
    from wta' wti' show ?case
      apply -
      apply(rule_tac x="T" in exI)
      apply(rule conjI)
      apply(erule WTrtAAcc)
      apply(assumption)
      by(simp add: widen_refl)
  next
    assume wta: "P,E,hp s \<turnstile> Val a : NT"
    from wta red_hext_incr[OF issi] have wta': "P,E,hp s' \<turnstile> Val a : NT" by (rule WTrt_hext_mono)
    from wta' wti' show ?case
      by(fastsimp elim:WTrtAAccNT)
  qed
next
  case RedAAccNull thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_NullPointer)
next
  case RedAAccBounds thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_ArrayIndexOutOfBounds)
next
  case (RedAAcc s a T si el i T' E)
  with prems have "P,hp s \<turnstile> Arr T si el \<surd>" by (auto simp add: sconf_def hconf_def)
  with prems obtain U where "typeof\<^bsub>hp s\<^esub> (el i) = \<lfloor>U\<rfloor>" and "P \<turnstile> U \<le> T'"
    by(auto simp add: oconf_def conf_def simp del: hp_def)
  with prems show ?case by(auto simp del:fun_upd_apply)
next
  case (AAssRed1 a s ta a' s' i e T E)
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> a : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> a' : T' \<and> P \<turnstile> T' \<le> T"
    and assa: "P \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>"
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
    and issi: "P \<turnstile> \<langle>i,s\<rangle> -ta\<rightarrow> \<langle>i',s'\<rangle>" 
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
    and issi: "P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" 
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
    by (unfold sconf_def hconf_def) (auto elim!:typeof_NullPointer)
next
  case RedAAssBounds thus ?case
    by (unfold sconf_def hconf_def) (auto elim!:typeof_ArrayIndexOutOfBounds)
next
  case RedAAssStore thus ?case
    by (unfold sconf_def hconf_def) (auto elim!:typeof_ArrayStore)
next
  case RedAAss thus ?case
    by(auto simp del:fun_upd_apply)
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
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_NullPointer)
next
  case (FAssRed1 e s ta e' s' F D e\<^isub>2)
  have red: "P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>"
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
  have red: "P \<turnstile> \<langle>e\<^isub>2,s\<rangle> -ta\<rightarrow> \<langle>e\<^isub>2',s'\<rangle>"
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
    by (unfold sconf_def hconf_def) (auto elim!:typeof_NullPointer)
next
  case (CallObj e s ta e' s' M es T E)
  have red: "P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,hp s' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> s \<surd>" and wt: "P,E,hp s \<turnstile> e\<bullet>M(es) : T" by fact+
  -- "We distinguish if @{term e} has type @{term NT} or a Class type"
  -- "Remember ?case = @{term ?case}"
  from wt
  show ?case
  proof(rule WTrt_elim_cases)
    fix C D Ts Us body pns
    assume wte: "P,E,hp s \<turnstile> e : Class C"
      and method: "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D"
      and wtes: "list_all2 (\<lambda>e T. P,E,hp s \<turnstile> e : T) es Us" and subs: "P \<turnstile> Us [\<le>] Ts"
    obtain U where wte': "P,E,hp s' \<turnstile> e' : U" and UsubC: "P \<turnstile> U \<le> Class C"
      using IH[OF conf wte] by blast
    -- "Is @{term U} the null type or a class type?"
    { assume "U = NT"
      moreover from wtes have "list_all2 (\<lambda>e T. P,E,hp s' \<turnstile> e : T) es Us"
	apply(induct es arbitrary: Us)
	 apply(simp)
	apply(clarsimp simp add: list_all2_Cons1 list_all2_Cons2 simp del: hp_def)
	by(rule WTrt_hext_mono[OF _ red_hext_incr[OF red]])
      ultimately have ?thesis using wte' by(blast intro!:WTrtCallNT) }
    moreover
    { fix C' assume UClass: "U = Class C'" and "subclass": "P \<turnstile> C' \<preceq>\<^sup>* C"
      have "P,E,hp s' \<turnstile> e' : Class C'" using wte' UClass by auto
      moreover obtain Ts' T' pns' body' D'
	where method': "P \<turnstile> C' sees M:Ts'\<rightarrow>T' = (pns',body') in D'"
	and subs': "P \<turnstile> Ts [\<le>] Ts'" and sub': "P \<turnstile> T' \<le> T"
	using Call_lemma[OF method "subclass" wf] by fast
      moreover from wtes have "list_all2 (\<lambda>e T. P,E,hp s' \<turnstile> e : T) es Us"
	apply(induct es arbitrary: Us)
	 apply(simp)
	apply(clarsimp simp add: list_all2_Cons1 list_all2_Cons2 simp del: hp_def)
	by(rule WTrt_hext_mono[OF _ red_hext_incr[OF red]])
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
    fix Ts assume wtes: "list_all2 (\<lambda>e T. P,E,hp s \<turnstile> e : T) es Ts"
    hence "list_all2 (\<lambda>e T. P,E,hp s' \<turnstile> e : T) es Ts"
      apply(induct es arbitrary: Ts)
       apply(simp)
      apply(clarsimp simp add: list_all2_Cons1 list_all2_Cons2 simp del: hp_def)
      by(rule WTrt_hext_mono[OF _ red_hext_incr[OF red]])
    ultimately show ?thesis by(blast intro!:WTrtCallNT)
  next
    fix C
    assume wte: "P,E,hp s \<turnstile> e : Class C"
    and PCThread: "P \<turnstile> C \<preceq>\<^sup>* Thread"
    and TVoid: "T = Void"
    and Mstart: "M = start"
    and es: "es = []"
    obtain U where wte': "P,E,hp s' \<turnstile> e' : U" and UsubC: "P \<turnstile> U \<le> Class C"
      using IH[OF conf wte] by blast
    -- "Is @{term U} the null type or a class type?"
    { assume "U = NT"
      hence ?thesis using wte' TVoid Mstart es
	apply(simp del: hp_def)
	by(fastsimp elim: WTrtCallNT) }
    moreover
    { fix C' assume UClass: "U = Class C'" and "subclass": "P \<turnstile> C' \<preceq>\<^sup>* C"
      have "P,E,hp s' \<turnstile> e' : Class C'" using wte' UClass by auto
      hence ?thesis using TVoid Mstart es PCThread "subclass"
	apply(simp)
	apply(erule WTrtNewThread)
	by(auto) }
    moreover
    { fix A assume "U = A\<lfloor>\<rceil>"
      with UsubC have "C = Object" by(auto dest: Array_widen)
      with PCThread have False by(auto simp: Object_widen) }
    ultimately show ?thesis using UsubC by(auto simp add:widen_Class)
  next
    fix T'
    assume wte: "P,E,hp s \<turnstile> e : T'"
      and refT: "is_refT T'"
      and TVoid: "T = Void"
      and M: "M = wait"
      and es: "es = []"
    from IH[OF conf wte] obtain U where U: "P,E,hp s' \<turnstile> e' : U" and sub: "P \<turnstile> U \<le> T'" by blast
    show ?thesis
    proof(cases "U = NT")
      case True
      thus ?thesis using U M es
	by(auto intro: WTrtCallNT simp del: hp_def)
    next
      case False 
      from refT sub have "is_refT U"
	by(auto elim: widen_refT)
      with U M es False TVoid show ?thesis
	by(fastsimp intro: WTrtWait simp del: hp_def)
    qed
  next
    fix T'
    assume wte: "P,E,hp s \<turnstile> e : T'"
      and refT: "is_refT T'"
      and TVoid: "T = Void"
      and M: "M = notify"
      and es: "es = []"
    from IH[OF conf wte] obtain U where U: "P,E,hp s' \<turnstile> e' : U" and sub: "P \<turnstile> U \<le> T'" by blast
    show ?thesis
    proof(cases "U = NT")
      case True
      thus ?thesis using U M es
	by(auto intro: WTrtCallNT simp del: hp_def)
    next
      case False 
      from refT sub have "is_refT U"
	by(auto elim: widen_refT)
      with U M es False TVoid show ?thesis
	by(fastsimp intro: WTrtNotify simp del: hp_def)
    qed
  next
    fix T'
    assume wte: "P,E,hp s \<turnstile> e : T'"
      and refT: "is_refT T'"
      and TVoid: "T = Void"
      and M: "M = notifyAll"
      and es: "es = []"
    from IH[OF conf wte] obtain U where U: "P,E,hp s' \<turnstile> e' : U" and sub: "P \<turnstile> U \<le> T'" by blast
    show ?thesis
    proof(cases "U = NT")
      case True
      thus ?thesis using U M es
	by(auto intro: WTrtCallNT simp del: hp_def)
    next
      case False 
      from refT sub have "is_refT U"
	by(auto elim: widen_refT)
      with U M es False TVoid show ?thesis
	by(fastsimp intro: WTrtNotifyAll simp del: hp_def)
    qed
  next
    fix C
    assume wte: "P,E,hp s \<turnstile> e : Class C"
    and PCThread: "P \<turnstile> C \<preceq>\<^sup>* Thread"
    and TVoid: "T = Void"
    and Mstart: "M = join"
    and es: "es = []"
    obtain U where wte': "P,E,hp s' \<turnstile> e' : U" and UsubC: "P \<turnstile> U \<le> Class C"
      using IH[OF conf wte] by blast
    -- "Is @{term U} the null type or a class type?"
    { assume "U = NT"
      hence ?thesis using wte' TVoid Mstart es
	apply(simp del: hp_def)
	by(fastsimp elim: WTrtCallNT) }
    moreover
    { fix C' assume UClass: "U = Class C'" and "subclass": "P \<turnstile> C' \<preceq>\<^sup>* C"
      have "P,E,hp s' \<turnstile> e' : Class C'" using wte' UClass by auto
      hence ?thesis using TVoid Mstart es PCThread "subclass"
	apply(simp)
	apply(erule WTrtJoin)
	by(auto) }
    moreover
    { fix A assume "U = A\<lfloor>\<rceil>"
      with UsubC have "C = Object" by(auto dest: Array_widen)
      with PCThread have False by(auto simp: Object_widen) }
    ultimately show ?thesis using UsubC by(auto simp add:widen_Class)
  qed
next
  case (CallParams e s ta e' s' v M vs es T E)
  have red: "P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by fact
  have IH: "\<And>T E. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T" by fact
  have sconf: "P,E \<turnstile> s \<surd>" by fact
  have wt: "P,E,hp s \<turnstile> Val v\<bullet>M(map Val vs @ e # es) : T" by fact
  from wt show ?case
  proof (rule WTrt_elim_cases)
    fix C D Ts Us pns body
    assume wte: "P,E,hp s \<turnstile> Val v : Class C"
      and "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D"
      and wtes: "list_all2 (\<lambda>e T. P,E,hp s \<turnstile> e : T) (map Val vs @ e # es) Us" and UsSubTs: "P \<turnstile> Us [\<le>] Ts"
    moreover have "P,E,hp s' \<turnstile> Val v : Class C"
      by(rule WTrt_hext_mono[OF wte red_hext_incr[OF red]])
    moreover
    from wtes obtain Uvs Ue Ues
      where wtvs: "list_all2 (\<lambda>e T. P,E,hp s \<turnstile> e : T) (map Val vs) Uvs"
      and wtee: "P,E,hp s \<turnstile> e : Ue"
      and wtes: "list_all2 (\<lambda>e T. P,E,hp s \<turnstile> e : T) es Ues"
      and Us: "Us = Uvs @ Ue # Ues"
      and lUs: "length vs = length Uvs"
      by(clarsimp simp add: list_all2_append1 list_all2_Cons1)
    from wtvs have wtvs': "list_all2 (\<lambda>e T. P,E,hp s' \<turnstile> e : T) (map Val vs) Uvs"
      apply(induct vs arbitrary: Uvs)
       apply(simp)
      apply(clarsimp simp add: list_all2_Cons1 list_all2_Cons2 simp del: hp_def)
      by(rule  hext_typeof_mono[OF red_hext_incr[OF red]])
    from IH[OF sconf wtee] obtain T' where wte': "P,E,hp s' \<turnstile> e' : T'" and T'subUe: "P \<turnstile> T' \<le> Ue" by(clarsimp)
    from wtes have wtes': "list_all2 (\<lambda>e T. P,E,hp s' \<turnstile> e : T) es Ues"
      apply(induct es arbitrary: Ues)
       apply(simp)
      apply(clarsimp simp add: list_all2_Cons1 list_all2_Cons2 simp del: hp_def)
      by(rule WTrt_hext_mono[OF _ red_hext_incr[OF red]])
    from Us UsSubTs T'subUe have uvstuessubts: "P \<turnstile> (Uvs @ T' # Ues) [\<le>] Ts"
      apply(clarsimp simp add: widen_append1)
      apply(rule_tac x="Ts1" in exI)
      apply(rule_tac x="z # zs" in exI)
      by(auto intro: widen_trans)
    moreover have "list_all2 (\<lambda>e T. P,E,hp s' \<turnstile> e : T) (map Val vs @ e' # es) (Uvs @ T' # Ues)"
      using wtvs' wte' wtes' lUs
      by(simp add: list_all2_append)
    ultimately show ?thesis by(blast intro:WTrtCall widens_trans)
  next
    fix Us
    assume null: "P,E,hp s \<turnstile> Val v : NT"
      and wtes: "list_all2 (\<lambda>e T. P,E,hp s \<turnstile> e : T) (map Val vs @ e # es) Us"
    from null have "v = Null" by simp
    moreover
    from wtes obtain Uvs Ue Ues
      where wtvs: "list_all2 (\<lambda>e T. P,E,hp s \<turnstile> e : T) (map Val vs) Uvs"
      and wtee: "P,E,hp s \<turnstile> e : Ue"
      and wtes: "list_all2 (\<lambda>e T. P,E,hp s \<turnstile> e : T) es Ues"
      and Us: "Us = Uvs @ Ue # Ues"
      and lUs: "length vs = length Uvs"
      by(clarsimp simp add: list_all2_append1 list_all2_Cons1)
    from wtvs have wtvs': "list_all2 (\<lambda>e T. P,E,hp s' \<turnstile> e : T) (map Val vs) Uvs"
      apply(induct vs arbitrary: Uvs)
       apply(simp)
      apply(clarsimp simp add: list_all2_Cons1 list_all2_Cons2 simp del: hp_def)
      by(rule  hext_typeof_mono[OF red_hext_incr[OF red]])
    from IH[OF sconf wtee] obtain T' where wte': "P,E,hp s' \<turnstile> e' : T'" and T'subUe: "P \<turnstile> T' \<le> Ue" by(clarsimp)
    from wtes have wtes': "list_all2 (\<lambda>e T. P,E,hp s' \<turnstile> e : T) es Ues"
      apply(induct es arbitrary: Ues)
       apply(simp)
      apply(clarsimp simp add: list_all2_Cons1 list_all2_Cons2 simp del: hp_def)
      by(rule WTrt_hext_mono[OF _ red_hext_incr[OF red]])
    have "list_all2 (\<lambda>e T. P,E,hp s' \<turnstile> e : T) (map Val vs @ e' # es) (Uvs @ T' # Ues)"
      using wtvs' wte' wtes' lUs
      by(simp add: list_all2_append)
    ultimately show ?thesis 
      by(fastsimp intro:WTrtCallNT widens_refl)
  next
    fix C
    assume "map Val vs @ e # es = []"
    thus ?thesis by simp
  next
    assume "map Val vs @ e # es = []"
    thus ?thesis by simp
  qed(simp_all)
next
  case (RedCall s a C fs M Ts T pns body D vs T' E)
  have hp: "hp s a = Some(Obj C fs)"
   and method: "P \<turnstile> C sees M: Ts\<rightarrow>T = (pns,body) in D"
   and wt: "P,E,hp s \<turnstile> addr a\<bullet>M(map Val vs) : T'" by fact+
  obtain Ts' where wtes: "list_all2 (\<lambda>e T. P,E,hp s \<turnstile> e : T) (map Val vs) Ts'"
    and subs: "P \<turnstile> Ts' [\<le>] Ts" and T'isT: "T' = T"
    using wt method hp wf
    apply -
    apply(erule WTrt_elim_cases)
          apply(fastsimp dest: sees_method_fun)
         apply(fastsimp dest: sees_method_fun)
        apply(fastsimp dest: Thread_not_sees_method_start[OF wf])
       apply(fastsimp dest: visible_method_exists class_wf map_of_SomeD simp add: wf_cdecl_def)
      apply(fastsimp dest: visible_method_exists class_wf map_of_SomeD simp add: wf_cdecl_def)
     apply(fastsimp dest: visible_method_exists class_wf map_of_SomeD simp add: wf_cdecl_def)
    apply(fastsimp dest: Thread_not_sees_method_join[OF wf])
    done
  from wtes subs have length_vs: "length vs = length Ts"
    apply -
    apply(drule list_all2_lengthD)
    apply(drule widens_lengthD)
    apply(simp)
    done
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
  case RedNewThread thus ?case 
    by(auto dest: Thread_not_sees_method_start[OF wf])
next
  case RedNewThreadFail thus ?case using wf
    apply(simp add: sconf_def hconf_def) 
    apply(rule exI)
    apply(rule conjI)
     apply(rule WTrtThrow)
       apply(fastsimp intro: typeof_IllegalThreadState)
      apply(simp)
     apply(simp)
    by(rule widen_refl)
next
  case (RedWait s a arrobj T E) thus ?case using wf
    apply -
    apply(erule WTrt_elim_cases)
    apply(fastsimp dest: visible_method_exists class_wf map_of_SomeD simp add: wf_cdecl_def)
    by(cases arrobj, auto)+
next
  case RedWaitFail thus ?case using wf
    by(fastsimp intro: WTrtThrow typeof_IllegalMonitorState widen_refl simp add: sconf_def hconf_def)
next
  case (RedNotify s a arrobj T E) thus ?case using wf
    apply -
    apply(erule WTrt_elim_cases)
    apply(fastsimp dest: visible_method_exists class_wf map_of_SomeD simp add: wf_cdecl_def)
    by(cases arrobj, auto)+
next
  case RedNotifyFail thus ?case using wf
    by(fastsimp intro: WTrtThrow typeof_IllegalMonitorState widen_refl simp add: sconf_def hconf_def)
next
  case (RedNotifyAll s a arrobj T E) thus ?case using wf
    apply -
    apply(erule WTrt_elim_cases)
    apply(fastsimp dest: visible_method_exists class_wf map_of_SomeD simp add: wf_cdecl_def)
    by(cases arrobj, auto)+
next
  case RedNotifyAllFail thus ?case using wf
    by(fastsimp intro: WTrtThrow typeof_IllegalMonitorState widen_refl simp add: sconf_def hconf_def)
next
  case RedJoin thus ?case
    by(auto dest: Thread_not_sees_method_join[OF wf])
next
  case RedCallNull thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_NullPointer)
next
  case BlockRedNone thus ?case
    by(auto simp del:fun_upd_apply)(fastsimp simp:sconf_def lconf_def)
next
  case (BlockRedSome e h l V ta e' h' l' v T Te E)
  have red: "P \<turnstile> \<langle>e,(h,l(V:=None))\<rangle> -ta\<rightarrow> \<langle>e',(h',l')\<rangle>" 
   and IH: "\<And>T E. \<lbrakk>P,E \<turnstile> (h, l(V := None)) \<surd>; P,E,hp (h, l(V := None)) \<turnstile> e : T\<rbrakk>
            \<Longrightarrow> \<exists>T'. P,E,hp (h', l') \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T"
   and Some: "l' V = Some v"
   and conf: "P,E \<turnstile> (h,l) \<surd>"
   and wt: "P,E,hp (h, l) \<turnstile> {V:T; e} : Te" by fact+
  obtain Te' where IH': "P,E(V\<mapsto>T),h' \<turnstile> e' : Te' \<and> P \<turnstile> Te' \<le> Te"
    using IH conf wt by(fastsimp simp:sconf_def lconf_def)
  have "P,h' \<turnstile> l' (:\<le>) E(V\<mapsto>T)" using conf wt
    apply -
    apply(simp)
    apply(erule red_preserves_lconf[OF red, simplified])
    by(simp add: sconf_def lconf_def)
  hence "P,h' \<turnstile> v :\<le> T" using Some by(fastsimp simp:lconf_def)
  with IH' show ?case
    by(fastsimp simp:sconf_def conf_def fun_upd_same simp del:fun_upd_apply)
next
  case (InitBlockRed e h l V v ta e' h' l' v' T T' E)
  have red: "P \<turnstile> \<langle>e, (h,l(V\<mapsto>v))\<rangle> -ta\<rightarrow> \<langle>e',(h',l')\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l(V\<mapsto>v)) \<surd>; P,E,hp (h, l(V \<mapsto> v)) \<turnstile> e : T\<rbrakk>
                    \<Longrightarrow> \<exists>U. P,E,hp (h', l') \<turnstile> e' : U \<and> P \<turnstile> U \<le> T"
   and v': "l' V = Some v'" and conf: "P,E \<turnstile> (h,l) \<surd>"
   and wt: "P,E,hp (h, l) \<turnstile> {V:T := Val v; e} : T'" by fact+
  from wt obtain T\<^isub>1 where wt\<^isub>1: "typeof\<^bsub>h\<^esub> v = Some T\<^isub>1"
    and T1subT: "P \<turnstile> T\<^isub>1 \<le> T" and wt\<^isub>2: "P,E(V\<mapsto>T),h \<turnstile> e : T'" by auto
  have lconf\<^isub>2: "P,h \<turnstile> l(V\<mapsto>v) (:\<le>) E(V\<mapsto>T)" using conf wt\<^isub>1 T1subT
    by(simp add:sconf_def lconf_upd2 conf_def)
  have "\<exists>T\<^isub>1'. typeof\<^bsub>h'\<^esub> v' = Some T\<^isub>1' \<and> P \<turnstile> T\<^isub>1' \<le> T"
    using v' red_preserves_lconf[OF red] wt\<^isub>2 lconf\<^isub>2
    by(fastsimp simp:lconf_def conf_def)
  with IH conf lconf\<^isub>2 wt\<^isub>2 show ?case by (fastsimp simp add:sconf_def)
next
  case RedBlock thus ?case by auto
next
  case RedInitBlock thus ?case by auto
next
  case (SynchronizedRed1 o' s ta o'' s' e T E)
  have red: "P \<turnstile> \<langle>o',s\<rangle> -ta\<rightarrow> \<langle>o'',s'\<rangle>" by fact
  have IH: "\<And>T E. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> o' : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> o'' : T' \<and> P \<turnstile> T' \<le> T" by fact
  have conf: "P,E \<turnstile> s \<surd>" by fact
  have wt: "P,E,hp s \<turnstile> sync(o') e : T" by fact
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
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_NullPointer)
next
  case (LockSynchronized s a arrobj e T E) thus ?case 
    by(cases arrobj)(auto)
next
  case (SynchronizedRed2 e s ta e' s' a T E)
  have red: "P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by fact
  have IH: "\<And>T E. \<lbrakk>P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T" by fact
  have conf: "P,E \<turnstile> s \<surd>" by fact
  have wt: "P,E,hp s \<turnstile> insync(a) e : T" by fact
  thus ?case
  proof(rule WTrt_elim_cases)
    fix Ta arrobj
    assume "P,E,hp s \<turnstile> e : T"
      and hpa: "hp s a = \<lfloor>arrobj\<rfloor>"
      and arrobj: "(case arrobj of Obj C fs \<Rightarrow> \<lfloor>Class C\<rfloor> | Arr t s e \<Rightarrow> \<lfloor>t\<lfloor>\<rceil>\<rfloor>) = \<lfloor>Ta\<rfloor>"
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
  have red: "P \<turnstile> \<langle>b,s\<rangle> -ta\<rightarrow> \<langle>b',s'\<rangle>" by fact
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
    and nobject: "T' \<noteq> Class Object"
    and refT: "is_refT_class T'" by(auto)
  from IH[OF conf wte] obtain T'' 
    where wte': "P,E,hp s' \<turnstile> e' : T''"
    and PT'T'': "P \<turnstile> T'' \<le> T'" by blast
  from nobject PT'T'' have "T'' \<noteq> Class Object"
    by(auto dest: Object_widen)
  moreover from refT PT'T'' nobject have "is_refT_class T''" 
    by(auto simp add: widen_Class elim: is_refT_class.cases)
  ultimately have "P,E,hp s' \<turnstile> throw e' : T" using wte' PT'T''
    by -(erule WTrtThrow)
  thus ?case by(auto)
next
  case RedThrowNull thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_NullPointer)
next
  case (TryRed e s ta e' s' C V e2 T E)
  have red: "P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by fact
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
  case (CallThrowParams es vs a es' v M s T E)
  have es: "es = map Val vs @ throw a # es'"
    and conf: "P,E \<turnstile> s \<surd>" by fact+
  have wt: "P,E,hp s \<turnstile> Val v\<bullet>M(es) : T" by fact
  thus ?case
  proof(rule WTrt_elim_cases)
    fix C D Ts Ts' body pns
    assume "list_all2 (\<lambda>e T. P,E,hp s \<turnstile> e : T) es Ts'"
    with es obtain Ta where "P,E,hp s \<turnstile> throw a : Ta" by(auto simp add: list_all2_append1 list_all2_Cons1)
    thus ?thesis by(auto)
  next
    fix Ts
    assume "list_all2 (\<lambda>e T. P,E,hp s \<turnstile> e : T) es Ts"
    with es obtain Ta where "P,E,hp s \<turnstile> throw a : Ta" by(auto simp add: list_all2_append1 list_all2_Cons1)
    thus ?thesis by(auto)
  qed(simp_all add: es)
qed fastsimp+ (* esp all Throw propagation rules are dealt with here *)
(*>*)

subsection {* Lifting to @{text"\<rightarrow>*"} *}

text{* Now all these preservation lemmas are first lifted to the transitive
closure \dots *}

lemma Step_induct' [consumes 1, case_names refl step]:
  assumes red: "P \<turnstile> \<langle>e, s\<rangle> -tas\<rightarrow>* \<langle>e', s'\<rangle>"
  and refl: "\<And>e s. Q e s [] e s"
  and step: "\<And>e s tas e' s' ta e'' s''. \<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -tas\<rightarrow>* \<langle>e', s'\<rangle>; Q e s tas e' s'; P \<turnstile> \<langle>e', s'\<rangle> -ta\<rightarrow> \<langle>e'', s''\<rangle> \<rbrakk> \<Longrightarrow> Q e s (tas @ [ta]) e'' s''"
  shows "Q e s tas e' s'"
using red
apply -
apply(drule stepify_pred.induct[where P="\<lambda>(e, s) ta (e', s'). Q e s ta e' s'"])
 apply(case_tac a, fastsimp intro: refl)
by(auto intro: step)


lemma Red_preserves_sconf_and_WT:
assumes wf: "wf_J_prog P"
shows "\<lbrakk> P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow>* \<langle>e',s'\<rangle>; P,E,hp s \<turnstile> e : T; P,E \<turnstile> s \<surd> \<rbrakk> 
       \<Longrightarrow> P,E \<turnstile> s' \<surd> \<and> (\<exists>T'. P,E,hp s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)"
(*<*)
proof(induct arbitrary: T rule: Step_induct')
  case refl thus ?case by blast
next
  case (step e s tas e' s' ta e'' s'' T)
  have Red: "P \<turnstile> \<langle>e, s\<rangle> -tas\<rightarrow>* \<langle>e', s'\<rangle>" by fact
  have IH: "\<And>T. \<lbrakk>P,E,hp s \<turnstile> e : T; P,E \<turnstile> s \<surd>\<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd> \<and> (\<exists>T'. P,E,hp s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)" by fact
  have red: "P \<turnstile> \<langle>e',s'\<rangle> -ta\<rightarrow> \<langle>e'',s''\<rangle>" by fact
  have wt: "P,E,hp s \<turnstile> e : T" by fact
  have conf: "P,E \<turnstile> s \<surd>" by fact
  from IH[OF wt conf] have conf': "P,E \<turnstile> s' \<surd>" and "\<exists>T'. P,E,hp s' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T " by(auto)
  then obtain T' where wte': "P,E,hp s' \<turnstile> e' : T'" and sub: "P \<turnstile> T' \<le> T" by blast
  with red conf' wf have "\<exists>T''. P,E,hp s'' \<turnstile> e'' : T'' \<and> P \<turnstile> T'' \<le> T'" by-(rule subject_reduction)
  with red conf' wte' sub show ?case by(auto intro: red_preserves_sconf widen_trans)
qed

lemma Red_preserves_defass:
assumes wf: "wf_J_prog P" and reds: "P \<turnstile> \<langle>e,s\<rangle> -tas\<rightarrow>* \<langle>e',s'\<rangle>"
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
  "\<lbrakk> wf_J_prog P; P \<turnstile> \<langle>e,s\<rangle> -tas\<rightarrow>* \<langle>e',s'\<rangle>; P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e:T \<rbrakk>
    \<Longrightarrow> \<exists>T'. P \<turnstile> T' \<le> T \<and> P,E,hp s' \<turnstile> e':T'"
by(auto dest!: Red_preserves_sconf_and_WT)


subsection "The final polish"

text{* The above preservation lemmas are now combined and packed nicely. *}

constdefs
  wf_config :: "J_prog \<Rightarrow> env \<Rightarrow> Jstate \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"   ("_,_,_ \<turnstile> _ : _ \<surd>"   [51,0,0,0,0]50)
  "P,E,s \<turnstile> e:T \<surd>  \<equiv>  P,E \<turnstile> s \<surd> \<and> P,E,hp s \<turnstile> e:T"

theorem Subject_reduction: assumes wf: "wf_J_prog P"
shows "P \<turnstile> \<langle>e,s\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P,E,s \<turnstile> e : T \<surd>
       \<Longrightarrow> \<exists>T'. P,E,s' \<turnstile> e' : T' \<surd> \<and> P \<turnstile> T' \<le> T"
(*<*)
by(force simp add: wf_config_def
   elim:red_preserves_sconf dest:subject_reduction[OF wf])
(*>*)


theorem Subject_reductions:
assumes wf: "wf_J_prog P" and reds: "P \<turnstile> \<langle>e,s\<rangle> -tas\<rightarrow>* \<langle>e',s'\<rangle>"
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
shows "\<lbrakk> P,E,s  \<turnstile> e : T \<surd>; \<D> e \<lfloor>dom(lcl s)\<rfloor>; \<not> final e \<rbrakk> \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>e,s\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
(*<*)
using progress[OF wf_prog_wwf_prog[OF wf]]
by(auto simp:wf_config_def sconf_def)
(*>*)


corollary TypeSafety:
  "\<lbrakk> wf_J_prog P; P,E \<turnstile> s \<surd>; P,E \<turnstile> e::T; \<D> e \<lfloor>dom(lcl s)\<rfloor>;
     P \<turnstile> \<langle>e,s\<rangle> -tas\<rightarrow>* \<langle>e',s'\<rangle>; \<not>(\<exists>e'' s'' ta. P \<turnstile> \<langle>e',s'\<rangle> -ta\<rightarrow> \<langle>e'',s''\<rangle>) \<rbrakk>
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
