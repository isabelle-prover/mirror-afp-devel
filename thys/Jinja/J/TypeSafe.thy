(*  Title:      Jinja/J/SmallTypeSafe.thy
    ID:         $Id: TypeSafe.thy,v 1.3 2007-02-07 17:19:08 stefanberghofer Exp $
    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* \isaheader{Type Safety Proof} *}

theory TypeSafe
imports Progress JWellForm
begin

subsection{*Basic preservation lemmas*}

text{* First two easy preservation lemmas. *}

theorem red_preserves_hconf:
  "P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> (\<And>T E. \<lbrakk> P,E,h \<turnstile> e : T; P \<turnstile> h \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h' \<surd>)"
and reds_preserves_hconf:
  "P \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> (\<And>Ts E. \<lbrakk> P,E,h \<turnstile> es [:] Ts; P \<turnstile> h \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h' \<surd>)"
(*<*)
proof (induct rule:red_reds_inducts)
  case (RedNew h a C FDTs h' l)
  have new: "new_Addr h = Some a" and fields: "P \<turnstile> C has_fields FDTs"
   and h': "h' = h(a\<mapsto>(C, init_fields FDTs))"
   and hconf: "P \<turnstile> h \<surd>" .
  from new have None: "h a = None" by(rule new_Addr_SomeD)
  moreover have "P,h \<turnstile> (C,init_fields FDTs) \<surd>"
    using fields by(rule oconf_init_fields)
  ultimately show "P \<turnstile> h' \<surd>" using h' by(fast intro: hconf_new[OF hconf])
next
  case (RedFAss h a C fs F D v l)
  let ?fs' = "fs((F,D)\<mapsto>v)"
  have hconf: "P \<turnstile> h \<surd>" and ha: "h a = Some(C,fs)"
   and wt: "P,E,h \<turnstile> addr a\<bullet>F{D}:=Val v : T" .
  from wt ha obtain TF Tv where typeofv: "typeof\<^bsub>h\<^esub> v = Some Tv"
    and has: "P \<turnstile> C has F:TF in D"
    and sub: "P \<turnstile> Tv \<le> TF" by auto
  have "P,h \<turnstile> (C, ?fs') \<surd>"
  proof (rule oconf_fupd[OF has])
    show "P,h \<turnstile> (C, fs) \<surd>" using hconf ha by(simp add:hconf_def)
    show "P,h \<turnstile> v :\<le> TF" using sub typeofv by(simp add:conf_def)
  qed
  with hconf ha show "P \<turnstile> h(a\<mapsto>(C, ?fs')) \<surd>"  by (rule hconf_upd_obj)
qed auto
(*>*)


theorem red_preserves_lconf:
  "P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow>
  (\<And>T E. \<lbrakk> P,E,h \<turnstile> e:T; P,h \<turnstile> l (:\<le>) E \<rbrakk> \<Longrightarrow> P,h' \<turnstile> l' (:\<le>) E)"
and reds_preserves_lconf:
  "P \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow>
  (\<And>Ts E. \<lbrakk> P,E,h \<turnstile> es[:]Ts; P,h \<turnstile> l (:\<le>) E \<rbrakk> \<Longrightarrow> P,h' \<turnstile> l' (:\<le>) E)"
(*<*)
proof(induct rule:red_reds_inducts)
  case RedNew thus ?case
    by(fast intro:lconf_hext red_hext_incr[OF red_reds.RedNew])
next
  case RedLAss thus ?case by(fastsimp elim: lconf_upd simp:conf_def)
next
  case RedFAss thus ?case
    by(fast intro:lconf_hext red_hext_incr[OF red_reds.RedFAss])
next
  case (InitBlockRed e h l V v e' h' l' v' T T')
  have red: "P \<turnstile> \<langle>e, (h, l(V\<mapsto>v))\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
   and IH: "\<And>T E . \<lbrakk> P,E,h \<turnstile> e:T; P,h \<turnstile> l(V\<mapsto>v) (:\<le>) E \<rbrakk>
                     \<Longrightarrow> P,h' \<turnstile> l' (:\<le>) E"
   and l'V: "l' V = Some v'" and lconf: "P,h \<turnstile> l (:\<le>) E"
   and wt: "P,E,h \<turnstile> {V:T := Val v; e} : T'" .
  from lconf_hext[OF lconf red_hext_incr[OF red]]
  have "P,h' \<turnstile> l (:\<le>) E" .
  moreover from IH lconf wt have "P,h' \<turnstile> l' (:\<le>) E(V\<mapsto>T)"
    by(auto simp del: fun_upd_apply simp: fun_upd_same lconf_upd2 conf_def)
  ultimately show "P,h' \<turnstile> l'(V := l V) (:\<le>) E"
    by (fastsimp simp:lconf_def split:split_if_asm)
next
  case (BlockRedNone e h l V e' h' l' T T')
  have red: "P \<turnstile> \<langle>e,(h, l(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
   and IH: "\<And>E T. \<lbrakk> P,E,h \<turnstile> e : T; P,h \<turnstile> l(V:=None) (:\<le>) E \<rbrakk>
                   \<Longrightarrow> P,h' \<turnstile> l' (:\<le>) E"
   and lconf: "P,h \<turnstile> l (:\<le>) E" and wt: "P,E,h \<turnstile> {V:T; e} : T'" .
  from lconf_hext[OF lconf red_hext_incr[OF red]]
  have "P,h' \<turnstile> l (:\<le>) E" .
  moreover have "P,h' \<turnstile> l' (:\<le>) E(V\<mapsto>T)"
    by(rule IH, insert lconf wt, auto simp:lconf_def)
  ultimately show "P,h' \<turnstile> l'(V := l V) (:\<le>) E"
    by (fastsimp simp:lconf_def split:split_if_asm)
next
  case (BlockRedSome e h l V e' h' l' v T T')
  have red: "P \<turnstile> \<langle>e,(h, l(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E,h \<turnstile> e : T; P,h \<turnstile> l(V:=None) (:\<le>) E\<rbrakk>
                   \<Longrightarrow> P,h' \<turnstile> l' (:\<le>) E"
   and lconf: "P,h \<turnstile> l (:\<le>) E" and wt: "P,E,h \<turnstile> {V:T; e} : T'" .
  from lconf_hext[OF lconf red_hext_incr[OF red]]
  have "P,h' \<turnstile> l (:\<le>) E" .
  moreover have "P,h' \<turnstile> l' (:\<le>) E(V\<mapsto>T)"
    by(rule IH, insert lconf wt, auto simp:lconf_def)
  ultimately show "P,h' \<turnstile> l'(V := l V) (:\<le>) E"
    by (fastsimp simp:lconf_def split:split_if_asm)
qed auto
(*>*)


text{* Preservation of definite assignment more complex and requires a
few lemmas first. *}

lemma [iff]: "\<And>A. \<lbrakk> length Vs = length Ts; length vs = length Ts\<rbrakk> \<Longrightarrow>
 \<D> (blocks (Vs,Ts,vs,e)) A = \<D> e (A \<squnion> \<lfloor>set Vs\<rfloor>)"
(*<*)
apply(induct Vs Ts vs e rule:blocks.induct)
apply(simp_all add:hyperset_defs)
done
(*>*)


lemma red_lA_incr: "P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> \<lfloor>dom l\<rfloor> \<squnion> \<A> e \<sqsubseteq>  \<lfloor>dom l'\<rfloor> \<squnion> \<A> e'"
and reds_lA_incr: "P \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> \<lfloor>dom l\<rfloor> \<squnion> \<A>s es \<sqsubseteq>  \<lfloor>dom l'\<rfloor> \<squnion> \<A>s es'"
(*<*)
apply(induct rule:red_reds_inducts)
apply(simp_all del:fun_upd_apply add:hyperset_defs)
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
apply(blast dest:red_lcl_incr)
apply(blast dest:red_lcl_incr)
apply blast
apply blast
apply blast
done
(*>*)


text{* Now preservation of definite assignment. *}

lemma assumes wf: "wf_J_prog P"
shows red_preserves_defass:
  "P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> \<D> e \<lfloor>dom l\<rfloor> \<Longrightarrow> \<D> e' \<lfloor>dom l'\<rfloor>"
and "P \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> \<D>s es \<lfloor>dom l\<rfloor> \<Longrightarrow> \<D>s es' \<lfloor>dom l'\<rfloor>"
(*<*)
proof (induct rule:red_reds_inducts)
  case BinOpRed1 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case FAssRed1 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case CallObj thus ?case by (auto elim!: Ds_mono[OF red_lA_incr])
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
  case SeqRed thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case CondRed thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case TryRed thus ?case
    by (fastsimp dest:red_lcl_incr intro:D_mono' simp:hyperset_defs)
next
  case ListRed1 thus ?case by (auto elim!: Ds_mono[OF red_lA_incr])
next
  case RedWhile thus ?case by(auto simp:hyperset_defs elim!:D_mono')
qed (auto simp:hyperset_defs)
(*>*)


text{* Combining conformance of heap and local variables: *}

constdefs
  sconf :: "J_prog \<Rightarrow> env \<Rightarrow> state \<Rightarrow> bool"   ("_,_ \<turnstile> _ \<surd>"   [51,51,51]50)
  "P,E \<turnstile> s \<surd>  \<equiv>  let (h,l) = s in P \<turnstile> h \<surd> \<and> P,h \<turnstile> l (:\<le>) E"

lemma red_preserves_sconf:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>; P,E,hp s \<turnstile> e : T; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"
(*<*)
by(fastsimp intro:red_preserves_hconf red_preserves_lconf
            simp add:sconf_def)
(*>*)

lemma reds_preserves_sconf:
  "\<lbrakk> P \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>; P,E,hp s \<turnstile> es [:] Ts; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"
(*<*)
by(fastsimp intro:reds_preserves_hconf reds_preserves_lconf
            simp add:sconf_def)
(*>*)


subsection "Subject reduction"

lemma wt_blocks:
 "\<And>E. \<lbrakk> length Vs = length Ts; length vs = length Ts \<rbrakk> \<Longrightarrow>
       (P,E,h \<turnstile> blocks(Vs,Ts,vs,e) : T) =
       (P,E(Vs[\<mapsto>]Ts),h \<turnstile> e:T \<and> (\<exists>Ts'. map (typeof\<^bsub>h\<^esub>) vs = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] Ts))"
(*<*)
apply(induct Vs Ts vs e rule:blocks.induct)
prefer 5; apply (force simp add:rel_list_all2_Cons2)
apply simp_all
done
(*>*)


theorem assumes wf: "wf_J_prog P"
shows subject_reduction2: "P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow>
  (\<And>E T. \<lbrakk> P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e:T \<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,h' \<turnstile> e':T' \<and> P \<turnstile> T' \<le> T)"
and subjects_reduction2: "P \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow>
  (\<And>E Ts. \<lbrakk> P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> es [:] Ts \<rbrakk>
            \<Longrightarrow> \<exists>Ts'. P,E,h' \<turnstile> es' [:] Ts' \<and> P \<turnstile> Ts' [\<le>] Ts)"
(*<*)
proof (induct rule:red_reds_inducts)
  case (RedCall h l a C fs M Ts T pns body D vs E T')
  have hp: "hp(h,l) a = Some(C,fs)"
   and method: "P \<turnstile> C sees M: Ts\<rightarrow>T = (pns,body) in D"
   and wt: "P,E,h \<turnstile> addr a\<bullet>M(map Val vs) : T'" .
  obtain Ts' where wtes: "P,E,h \<turnstile> map Val vs [:] Ts'"
    and subs: "P \<turnstile> Ts' [\<le>] Ts" and T'isT: "T' = T"
    using wt method hp by (auto dest:sees_method_fun)
  from wtes subs have length_vs: "length vs = length Ts"
    by(fastsimp simp:list_all2_def dest!:WTrts_same_length)
  from sees_wf_mdecl[OF wf method] obtain T''
    where wtabody: "P,[this#pns [\<mapsto>] Class D#Ts] \<turnstile> body :: T''"
    and T''subT: "P \<turnstile> T'' \<le> T" and length_pns: "length pns = length Ts"
    by(fastsimp simp:wf_mdecl_def simp del:map_upds_twist)
  from wtabody have "P,empty(this#pns [\<mapsto>] Class D#Ts),h \<turnstile> body : T''"
    by(rule WT_implies_WTrt)
  hence "P,E(this#pns [\<mapsto>] Class D#Ts),h \<turnstile> body : T''"
    by(rule WTrt_env_mono) simp
  hence "P,E,h \<turnstile> blocks(this#pns, Class D#Ts, Addr a#vs, body) : T''"
  using wtes subs hp sees_method_decl_above[OF method] length_vs length_pns
    by(fastsimp simp add:wt_blocks rel_list_all2_Cons2)
  with T''subT T'isT show ?case by blast
next
  case RedNewFail thus ?case
    by (unfold sconf_def hconf_def) (fastsimp elim!:typeof_OutOfMemory)
next
  case CastRed thus ?case
    by(clarsimp simp:is_refT_def)
      (blast intro: widens_trans dest!:widen_Class[THEN iffD1])
next
  case RedCastFail thus ?case
    by (unfold sconf_def hconf_def)  (fastsimp elim!:typeof_ClassCast)
next
  case (BinOpRed1 e\<^isub>1 h l e\<^isub>1' h' l' bop e\<^isub>2)
  have red: "P \<turnstile> \<langle>e\<^isub>1,(h,l)\<rangle> \<rightarrow> \<langle>e\<^isub>1',(h',l')\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e\<^isub>1:T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h' \<turnstile> e\<^isub>1' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> (h,l) \<surd>" and wt: "P,E,h \<turnstile> e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 : T" .
  have "P,E,h' \<turnstile> e\<^isub>1' \<guillemotleft>bop\<guillemotright> e\<^isub>2 : T"
  proof (cases bop)
    assume [simp]: "bop = Eq"
    from wt obtain T\<^isub>1 T\<^isub>2 where [simp]: "T = Boolean"
      and wt\<^isub>1: "P,E,h \<turnstile> e\<^isub>1 : T\<^isub>1" and wt\<^isub>2: "P,E,h \<turnstile> e\<^isub>2 : T\<^isub>2" by auto
    show ?thesis
      using WTrt_hext_mono[OF wt\<^isub>2 red_hext_incr[OF red]] IH[OF conf wt\<^isub>1]
      by auto
  next
    assume  [simp]: "bop = Add"
    from wt have [simp]: "T = Integer"
      and wt\<^isub>1: "P,E,h \<turnstile> e\<^isub>1 : Integer" and wt\<^isub>2: "P,E,h \<turnstile> e\<^isub>2 : Integer"
      by auto
    show ?thesis
      using IH[OF conf wt\<^isub>1] WTrt_hext_mono[OF wt\<^isub>2 red_hext_incr[OF red]]
      by auto
  qed
  thus ?case by auto
next
  case (BinOpRed2 e\<^isub>2 h l e\<^isub>2' h' l' v\<^isub>1 bop)
  have red: "P \<turnstile> \<langle>e\<^isub>2,(h,l)\<rangle> \<rightarrow> \<langle>e\<^isub>2',(h',l')\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e\<^isub>2:T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h' \<turnstile> e\<^isub>2' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> (h,l) \<surd>" and wt: "P,E,h \<turnstile> (Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> e\<^isub>2 : T" .
  have "P,E,h' \<turnstile> (Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> e\<^isub>2' : T"
  proof (cases bop)
    assume [simp]: "bop = Eq"
    from wt obtain T\<^isub>1 T\<^isub>2 where [simp]: "T = Boolean"
      and wt\<^isub>1: "P,E,h \<turnstile> Val v\<^isub>1 : T\<^isub>1" and wt\<^isub>2: "P,E,h \<turnstile> e\<^isub>2:T\<^isub>2" by auto
    show ?thesis
      using IH[OF conf wt\<^isub>2] WTrt_hext_mono[OF wt\<^isub>1 red_hext_incr[OF red]]
      by auto
  next
    assume  [simp]: "bop = Add"
    from wt have [simp]: "T = Integer"
      and wt\<^isub>1: "P,E,h \<turnstile> Val v\<^isub>1 : Integer" and wt\<^isub>2: "P,E,h \<turnstile> e\<^isub>2 : Integer"
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
  case (FAccRed e h l e' h' l' F D)
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> (h,l) \<surd>" and wt: "P,E,h \<turnstile> e\<bullet>F{D} : T" .
  -- "The goal: ?case = @{prop ?case}"
  -- "Now distinguish the two cases how wt can have arisen."
  { fix C assume wte: "P,E,h \<turnstile> e : Class C"
             and has: "P \<turnstile> C has F:T in D"
    from IH[OF conf wte]
    obtain U where wte': "P,E,h' \<turnstile> e' : U" and UsubC: "P \<turnstile> U \<le> Class C"
      by auto
    -- "Now distinguish what @{term U} can be."
    { assume "U = NT" hence ?case using wte'
	by(blast intro:WTrtFAccNT widen_refl) }
    moreover
    { fix C' assume U: "U = Class C'" and C'subC: "P \<turnstile> C' \<preceq>\<^sup>* C"
      from has_field_mono[OF has C'subC] wte' U
      have ?case by(blast intro:WTrtFAcc) }
    ultimately have ?case using UsubC by(simp add: widen_Class) blast }
  moreover
  { assume "P,E,h \<turnstile> e : NT"
    hence "P,E,h' \<turnstile> e' : NT" using IH[OF conf] by fastsimp
    hence ?case  by(fastsimp intro:WTrtFAccNT widen_refl) }
  ultimately show ?case using wt by blast
next
  case RedFAcc thus ?case
    by(fastsimp simp:sconf_def hconf_def oconf_def conf_def has_field_def
                dest:has_fields_fun)
next
  case RedFAccNull thus ?case
    by(fastsimp intro: widen_refl WTThrow[OF WTVal] elim!: typeof_NullPointer
                simp: sconf_def hconf_def)
next
  case (FAssRed1 e h l e' h' l' F D e\<^isub>2)
  have red: "P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> (h,l) \<surd>" and wt: "P,E,h \<turnstile> e\<bullet>F{D}:=e\<^isub>2 : T" .
  from wt have void: "T = Void" by blast
  -- "We distinguish if @{term e} has type @{term NT} or a Class type"
  -- "Remember ?case = @{term ?case}"
  { assume "P,E,h \<turnstile> e : NT"
    hence "P,E,h' \<turnstile> e' : NT" using IH[OF conf] by fastsimp
    moreover obtain T\<^isub>2 where "P,E,h \<turnstile> e\<^isub>2 : T\<^isub>2" using wt by auto
    from this red_hext_incr[OF red] have  "P,E,h' \<turnstile> e\<^isub>2 : T\<^isub>2"
      by(rule WTrt_hext_mono)
    ultimately have ?case using void by(blast intro!:WTrtFAssNT)
  }
  moreover
  { fix C TF T\<^isub>2 assume wt\<^isub>1: "P,E,h \<turnstile> e : Class C" and wt\<^isub>2: "P,E,h \<turnstile> e\<^isub>2 : T\<^isub>2"
    and has: "P \<turnstile> C has F:TF in D" and sub: "P \<turnstile> T\<^isub>2 \<le> TF"
    obtain U where wt\<^isub>1': "P,E,h' \<turnstile> e' : U" and UsubC: "P \<turnstile> U \<le> Class C"
      using IH[OF conf wt\<^isub>1] by blast
    have wt\<^isub>2': "P,E,h' \<turnstile> e\<^isub>2 : T\<^isub>2"
      by(rule WTrt_hext_mono[OF wt\<^isub>2 red_hext_incr[OF red]])
    -- "Is @{term U} the null type or a class type?"
    { assume "U = NT" with wt\<^isub>1' wt\<^isub>2' void have ?case
	by(blast intro!:WTrtFAssNT) }
    moreover
    { fix C' assume UClass: "U = Class C'" and subclass: "P \<turnstile> C' \<preceq>\<^sup>* C"
      have "P,E,h' \<turnstile> e' : Class C'" using wt\<^isub>1' UClass by auto
      moreover have "P \<turnstile> C' has F:TF in D"
	by(rule has_field_mono[OF has subclass])
      ultimately have ?case using wt\<^isub>2' sub void by(blast intro:WTrtFAss) }
    ultimately have ?case using UsubC by(auto simp add:widen_Class) }
  ultimately show ?case using wt by blast
next
  case (FAssRed2 e\<^isub>2 h l e\<^isub>2' h' l' v F D)
  have red: "P \<turnstile> \<langle>e\<^isub>2,(h,l)\<rangle> \<rightarrow> \<langle>e\<^isub>2',(h',l')\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e\<^isub>2 : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h' \<turnstile> e\<^isub>2' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> (h,l) \<surd>" and wt: "P,E,h \<turnstile> Val v\<bullet>F{D}:=e\<^isub>2 : T" .
  from wt have [simp]: "T = Void" by auto
  from wt show ?case
  proof (rule WTrt_elim_cases)
    fix C TF T\<^isub>2
    assume wt\<^isub>1: "P,E,h \<turnstile> Val v : Class C"
      and has: "P \<turnstile> C has F:TF in D"
      and wt\<^isub>2: "P,E,h \<turnstile> e\<^isub>2 : T\<^isub>2" and TsubTF: "P \<turnstile> T\<^isub>2 \<le> TF"
    have wt\<^isub>1': "P,E,h' \<turnstile> Val v : Class C"
      by(rule WTrt_hext_mono[OF wt\<^isub>1 red_hext_incr[OF red]])
    obtain T\<^isub>2' where wt\<^isub>2': "P,E,h' \<turnstile> e\<^isub>2' : T\<^isub>2'" and T'subT: "P \<turnstile> T\<^isub>2' \<le> T\<^isub>2"
      using IH[OF conf wt\<^isub>2] by blast
    have "P,E,h' \<turnstile> Val v\<bullet>F{D}:=e\<^isub>2' : Void"
      by(rule WTrtFAss[OF wt\<^isub>1' has wt\<^isub>2' widen_trans[OF T'subT TsubTF]])
    thus ?case by auto
  next
    fix T\<^isub>2 assume null: "P,E,h \<turnstile> Val v : NT" and wt\<^isub>2: "P,E,h \<turnstile> e\<^isub>2 : T\<^isub>2"
    from null have "v = Null" by simp
    moreover
    obtain T\<^isub>2' where "P,E,h' \<turnstile> e\<^isub>2' : T\<^isub>2' \<and> P \<turnstile> T\<^isub>2' \<le> T\<^isub>2"
      using IH[OF conf wt\<^isub>2] by blast
    ultimately show ?thesis by(fastsimp intro:WTrtFAssNT)
  qed
next
  case RedFAss thus ?case by(auto simp del:fun_upd_apply)
next
  case RedFAssNull thus ?case
    by(fastsimp intro: WTThrow[OF WTVal] elim!:typeof_NullPointer simp:sconf_def hconf_def)
next
  case (CallObj e h l e' h' l' M es)
  have red: "P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> (h,l) \<surd>" and wt: "P,E,h \<turnstile> e\<bullet>M(es) : T" .
  -- "We distinguish if @{term e} has type @{term NT} or a Class type"
  -- "Remember ?case = @{term ?case}"
  { assume "P,E,h \<turnstile> e:NT"
    hence "P,E,h' \<turnstile> e' : NT" using IH[OF conf] by fastsimp
    moreover
    fix Ts assume wtes: "P,E,h \<turnstile> es [:] Ts"
    have "P,E,h' \<turnstile> es [:] Ts"
      by(rule WTrts_hext_mono[OF wtes red_hext_incr[OF red]])
    ultimately have ?case by(blast intro!:WTrtCallNT) }
  moreover
  { fix C D Ts Us pns body
    assume wte: "P,E,h \<turnstile> e : Class C"
      and method: "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D"
      and wtes: "P,E,h \<turnstile> es [:] Us" and subs: "P \<turnstile> Us [\<le>] Ts"
    obtain U where wte': "P,E,h' \<turnstile> e' : U" and UsubC: "P \<turnstile> U \<le> Class C"
      using IH[OF conf wte] by blast
    -- "Is @{term U} the null type or a class type?"
    { assume "U = NT"
      moreover have "P,E,h' \<turnstile> es [:] Us"
	by(rule WTrts_hext_mono[OF wtes red_hext_incr[OF red]])
      ultimately have ?case using wte' by(blast intro!:WTrtCallNT) }
    moreover
    { fix C' assume UClass: "U = Class C'" and subclass: "P \<turnstile> C' \<preceq>\<^sup>* C"
      have "P,E,h' \<turnstile> e' : Class C'" using wte' UClass by auto
      moreover obtain Ts' T' pns' body' D'
	where method': "P \<turnstile> C' sees M:Ts'\<rightarrow>T' = (pns',body') in D'"
	and subs': "P \<turnstile> Ts [\<le>] Ts'" and sub': "P \<turnstile> T' \<le> T"
	using Call_lemma[OF method subclass wf] by fast
      moreover have "P,E,h' \<turnstile> es [:] Us"
	by(rule WTrts_hext_mono[OF wtes red_hext_incr[OF red]])
      ultimately have ?case
	using subs by(blast intro:WTrtCall rtrancl_trans widens_trans) }
    ultimately have ?case using UsubC by(auto simp add:widen_Class) }
  ultimately show ?case using wt by auto
next
  case (CallParams es h l es' h' l' v M)
  have reds: "P \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle>"
   and IH: "\<And>E Ts. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> es [:] Ts\<rbrakk>
                 \<Longrightarrow> \<exists>Us. P,E,h' \<turnstile> es' [:] Us \<and> P \<turnstile> Us [\<le>] Ts"
   and conf: "P,E \<turnstile> (h,l) \<surd>" and wt: "P,E,h \<turnstile> Val v\<bullet>M(es) : T" .
  from wt show ?case
  proof (rule WTrt_elim_cases)
    fix C D Ts Us pns body
    assume wte: "P,E,h \<turnstile> Val v : Class C"
      and "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D"
      and wtes: "P,E,h \<turnstile> es [:] Us" and "P \<turnstile> Us [\<le>] Ts"
    moreover have "P,E,h' \<turnstile> Val v : Class C"
      by(rule WTrt_hext_mono[OF wte reds_hext_incr[OF reds]])
    moreover
    obtain Us' where "P,E,h' \<turnstile> es' [:] Us' \<and> P \<turnstile> Us' [\<le>] Us"
      using IH[OF conf wtes] by blast
    ultimately show ?thesis by(blast intro:WTrtCall widens_trans)
  next
    fix Us
    assume null: "P,E,h \<turnstile> Val v : NT" and wtes: "P,E,h \<turnstile> es [:] Us"
    from null have "v = Null" by simp
    moreover
    obtain Us' where "P,E,h' \<turnstile> es' [:] Us' \<and> P \<turnstile> Us' [\<le>] Us"
      using IH[OF conf wtes] by blast
    ultimately show ?thesis by(fastsimp intro:WTrtCallNT)
  qed
next
  case RedCallNull thus ?case
    by(fastsimp intro: WTThrow[OF WTVal] elim!:typeof_NullPointer simp: sconf_def hconf_def)
next
  case (InitBlockRed e h l V v e' h' l' v' T E T')
  have red: "P \<turnstile> \<langle>e, (h,l(V\<mapsto>v))\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l(V\<mapsto>v)) \<surd>; P,E,h \<turnstile> e : T\<rbrakk>
                    \<Longrightarrow> \<exists>U. P,E,h' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T"
   and v': "l' V = Some v'" and conf: "P,E \<turnstile> (h,l) \<surd>"
   and wt: "P,E,h \<turnstile> {V:T := Val v; e} : T'" .
  from wt obtain T\<^isub>1 where wt\<^isub>1: "typeof\<^bsub>h\<^esub> v = Some T\<^isub>1"
    and T1subT: "P \<turnstile> T\<^isub>1 \<le> T" and wt\<^isub>2: "P,E(V\<mapsto>T),h \<turnstile> e : T'" by auto
  have lconf\<^isub>2: "P,h \<turnstile> l(V\<mapsto>v) (:\<le>) E(V\<mapsto>T)" using conf wt\<^isub>1 T1subT
    by(simp add:sconf_def lconf_upd2 conf_def)
  have "\<exists>T\<^isub>1'. typeof\<^bsub>h'\<^esub> v' = Some T\<^isub>1' \<and> P \<turnstile> T\<^isub>1' \<le> T"
    using v' red_preserves_lconf[OF red wt\<^isub>2 lconf\<^isub>2]
    by(fastsimp simp:lconf_def conf_def)
  with IH conf lconf\<^isub>2 wt\<^isub>2 show ?case by (fastsimp simp add:sconf_def)
next
  case BlockRedNone thus ?case
    by(auto simp del:fun_upd_apply)(fastsimp simp:sconf_def lconf_def)
next
  case (BlockRedSome e h l V e' h' l' v T E Te)
  have red: "P \<turnstile> \<langle>e,(h,l(V:=None))\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l(V:=None)) \<surd>; P,E,h \<turnstile> e : T\<rbrakk>
                   \<Longrightarrow> \<exists>T'. P,E,h' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T"
   and Some: "l' V = Some v" and conf: "P,E \<turnstile> (h,l) \<surd>"
   and wt: "P,E,h \<turnstile> {V:T; e} : Te" .
  obtain Te' where IH': "P,E(V\<mapsto>T),h' \<turnstile> e' : Te' \<and> P \<turnstile> Te' \<le> Te"
    using IH conf wt by(fastsimp simp:sconf_def lconf_def)
  have "P,h' \<turnstile> l' (:\<le>) E(V\<mapsto>T)" using conf wt
    by(fastsimp intro:red_preserves_lconf[OF red] simp:sconf_def lconf_def)
  hence "P,h' \<turnstile> v :\<le> T" using Some by(fastsimp simp:lconf_def)
  with IH' show ?case
    by(fastsimp simp:sconf_def conf_def fun_upd_same simp del:fun_upd_apply)
next
  case SeqRed thus ?case
    by auto (blast dest:WTrt_hext_mono[OF _ red_hext_incr])
next
  case CondRed thus ?case
    by auto (blast intro:WTrt_hext_mono[OF _ red_hext_incr])+
next
  case ThrowRed thus ?case
    by(auto simp:is_refT_def)(blast dest:widen_Class[THEN iffD1])+
next
  case RedThrowNull thus ?case
    by(fastsimp intro: WTThrow[OF WTVal] elim!:typeof_NullPointer simp:sconf_def hconf_def)
next
  case TryRed thus ?case
    by auto (blast intro:widen_trans WTrt_hext_mono[OF _ red_hext_incr])
next
  case RedTryFail thus ?case
    by(fastsimp intro: WTrtThrow[OF WTrtVal] simp:sconf_def hconf_def)
next
  case ListRed1 thus ?case
    by(fastsimp dest: WTrts_hext_mono[OF _ red_hext_incr])
next
  case ListRed2 thus ?case
    by(fastsimp dest: hext_typeof_mono[OF reds_hext_incr])
qed fastsimp+ (* esp all Throw propagation rules are dealt with here *)
(*>*)


corollary subject_reduction:
  "\<lbrakk> wf_J_prog P; P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>; P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e:T \<rbrakk>
  \<Longrightarrow> \<exists>T'. P,E,hp s' \<turnstile> e':T' \<and> P \<turnstile> T' \<le> T"
(*<*)by(cases s, cases s', fastsimp dest:subject_reduction2)(*>*)

corollary subjects_reduction:
  "\<lbrakk> wf_J_prog P; P \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>; P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> es[:]Ts \<rbrakk>
  \<Longrightarrow> \<exists>Ts'. P,E,hp s' \<turnstile> es'[:]Ts' \<and> P \<turnstile> Ts' [\<le>] Ts"
(*<*)by(cases s, cases s', fastsimp dest:subjects_reduction2)(*>*)


subsection {* Lifting to @{text"\<rightarrow>*"} *}

text{* Now all these preservation lemmas are first lifted to the transitive
closure \dots *}

lemma Red_preserves_sconf:
assumes wf: "wf_J_prog P" and Red: "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
shows "\<And>T. \<lbrakk> P,E,hp s \<turnstile> e : T; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"
(*<*)
using Red
proof (induct rule:converse_rtrancl_induct2')
  case refl show ?case .
next
  case step thus ?case
    by(blast intro:red_preserves_sconf dest: subject_reduction[OF wf])
qed
(*>*)


lemma Red_preserves_defass:
assumes wf: "wf_J_prog P" and reds: "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
shows "\<D> e \<lfloor>dom(lcl s)\<rfloor> \<Longrightarrow> \<D> e' \<lfloor>dom(lcl s')\<rfloor>"
using reds
proof (induct rule:converse_rtrancl_induct2')
  case refl thus ?case .
next
  case (step e s e' s') thus ?case
    by(cases s,cases s')(auto dest:red_preserves_defass[OF wf])
qed


lemma Red_preserves_type:
assumes wf: "wf_J_prog P" and Red: "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
shows "!!T. \<lbrakk> P,E \<turnstile> s\<surd>; P,E,hp s \<turnstile> e:T \<rbrakk>
    \<Longrightarrow> \<exists>T'. P \<turnstile> T' \<le> T \<and> P,E,hp s' \<turnstile> e':T'"
(*<*)
using Red
proof (induct rule:converse_rtrancl_induct2')
  case refl thus ?case by blast
next
  case step thus ?case
    by(blast intro:widen_trans red_preserves_sconf
             dest:subject_reduction[OF wf])
qed
(*>*)


subsection {* Lifting to @{text"\<Rightarrow>"} *}

text{* \dots and now to the big step semantics, just for fun. *}

lemma eval_preserves_sconf:
  "\<lbrakk> wf_J_prog P; P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>; P,E \<turnstile> e::T; P,E \<turnstile> s\<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s'\<surd>"
(*<*)
by(blast intro:Red_preserves_sconf big_by_small WT_implies_WTrt wf_prog_wwf_prog)
(*>*)


lemma eval_preserves_type: assumes wf: "wf_J_prog P"
shows "\<lbrakk> P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>; P,E \<turnstile> s\<surd>; P,E \<turnstile> e::T \<rbrakk>
   \<Longrightarrow> \<exists>T'. P \<turnstile> T' \<le> T \<and> P,E,hp s' \<turnstile> e':T'"
(*<*)
by(blast dest:big_by_small[OF wf_prog_wwf_prog[OF wf]]
              WT_implies_WTrt Red_preserves_type[OF wf])
(*>*)


subsection "The final polish"

text{* The above preservation lemmas are now combined and packed nicely. *}

constdefs
  wf_config :: "J_prog \<Rightarrow> env \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"   ("_,_,_ \<turnstile> _ : _ \<surd>"   [51,0,0,0,0]50)
  "P,E,s \<turnstile> e:T \<surd>  \<equiv>  P,E \<turnstile> s \<surd> \<and> P,E,hp s \<turnstile> e:T"

theorem Subject_reduction: assumes wf: "wf_J_prog P"
shows "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P,E,s \<turnstile> e : T \<surd>
       \<Longrightarrow> \<exists>T'. P,E,s' \<turnstile> e' : T' \<surd> \<and> P \<turnstile> T' \<le> T"
(*<*)
by(force simp add: wf_config_def
   elim:red_preserves_sconf dest:subject_reduction[OF wf])
(*>*)


theorem Subject_reductions:
assumes wf: "wf_J_prog P" and reds: "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
shows "\<And>T. P,E,s \<turnstile> e:T \<surd> \<Longrightarrow> \<exists>T'. P,E,s' \<turnstile> e':T' \<surd> \<and> P \<turnstile> T' \<le> T"
(*<*)
using reds
proof (induct rule:converse_rtrancl_induct2')
  case refl thus ?case by blast
next
  case step thus ?case
    by(blast dest:Subject_reduction[OF wf] intro:widen_trans)
qed
(*>*)


corollary Progress: assumes wf: "wf_J_prog P"
shows "\<lbrakk> P,E,s  \<turnstile> e : T \<surd>; \<D> e \<lfloor>dom(lcl s)\<rfloor>; \<not> final e \<rbrakk> \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
(*<*)
using progress[OF wf_prog_wwf_prog[OF wf]]
by(auto simp:wf_config_def sconf_def)
(*>*)


corollary TypeSafety:
  "\<lbrakk> wf_J_prog P; P,E \<turnstile> s \<surd>; P,E \<turnstile> e::T; \<D> e \<lfloor>dom(lcl s)\<rfloor>;
     P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>; \<not>(\<exists>e'' s''. P \<turnstile> \<langle>e',s'\<rangle> \<rightarrow> \<langle>e'',s''\<rangle>) \<rbrakk>
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
apply (fastsimp simp:wf_config_def final_def conf_def dest: Progress)
done
(*>*)


end
