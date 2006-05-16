(* Author: Daniel Wasserrab
   Based on the Jinja theory J/TypeSafe.thy by Tobias Nipkow *)

header {* Type Safety Proof *}

theory TypeSafe imports HeapExtension CWellForm begin

subsection{*Basic preservation lemmas*}

lemma assumes wf:"wwf_prog P" and casts:"P \<turnstile> T casts v to v'"
  and typeof:"P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T'" and leq:"P \<turnstile> T' \<le> T"
  shows casts_conf:"P,h \<turnstile> v' :\<le> T"

proof -
  { fix a' C Cs S'
    assume leq:"P \<turnstile> Class (last Cs) \<le> T" and subo:"(C,Cs) \<in> Subobjs P"
      and casts':"P \<turnstile> T casts Ref (a',Cs) to v'" and h:"h a' = Some(C,S')"
    from subo wf have "is_class P (last Cs)" by(fastsimp intro:Subobj_last_isClass)
    with leq wf obtain C' where T:"T = Class C'"
      and path_unique:"P \<turnstile> Path (last Cs) to C' unique"
      by(auto dest:Class_widen)
    from path_unique obtain Cs' where path_via:"P \<turnstile> Path (last Cs) to C' via Cs'"
      by(auto simp:path_via_def path_unique_def)
    with T path_unique casts' have v':"v' = Ref (a',Cs@\<^sub>pCs')"
      by -(erule casts_to.elims,auto simp:path_unique_def path_via_def)
    from subo path_via wf have "(C,Cs@\<^sub>pCs') \<in> Subobjs P"
      and "last (Cs@\<^sub>pCs') = C'"
      apply(auto intro:Subobjs_appendPath simp:path_via_def)
      apply(drule_tac Cs="Cs'" in Subobjs_nonempty)
      by(rule sym[OF appendPath_last])
    with T h v' have ?thesis by auto }
  with casts typeof wf typeof leq show ?thesis
    by(cases v,auto elim:casts_to.elims split:split_if_asm)
qed



theorem assumes wf:"wwf_prog P"
shows red_preserves_hconf:
  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> (\<And>T. \<lbrakk> P,E,h \<turnstile> e : T; P \<turnstile> h \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h' \<surd>)"
and reds_preserves_hconf:
  "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> (\<And>Ts. \<lbrakk> P,E,h \<turnstile> es [:] Ts; P \<turnstile> h \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h' \<surd>)"

proof (induct rule:red_reds_induct)
  case (RedNew C E a h h' l)
  have new: "new_Addr h = Some a" and h':"h' = h(a \<mapsto> (C, init_obj P C))"
    and hconf:"P \<turnstile> h \<surd>" and wt_New:"P,E,h \<turnstile> new C : T" .
  from new have None: "h a = None" by(rule new_Addr_SomeD)
  with wf have oconf:"P,h \<turnstile> (C,init_obj P C) \<surd>"
    apply (auto simp:oconf_def)
    apply (rule_tac x="init_class_fieldmap P (last Cs)" in exI)
    by (fastsimp intro:init_obj.intros fconf_init_fields 
                 elim: init_obj.elims dest!:Subobj_last_isClass simp:is_class_def)+
  thus ?case using h' None by(fast intro: hconf_new[OF hconf])
next
  case (RedFAss Cs Cs' D Ds E F S T a fs' h l v v' T')
  let ?fs' = "fs'(F \<mapsto> v')"
  let ?S' = "insert (Ds, ?fs') (S - {(Ds, fs')})"
  have ha:"h a = Some(D,S)" and hconf:"P \<turnstile> h \<surd>"
    and field:"P \<turnstile> last Cs' has least F:T via Cs"
    and casts:"P \<turnstile> T casts v to v'"
    and Ds:"Ds = Cs' @\<^sub>p Cs" and S:"(Ds,fs') \<in> S"
    and wte:"P,E,h \<turnstile> ref(a,Cs')\<bullet>F{Cs} := Val v : T'" .
  from wte have "P \<turnstile> last Cs' has least F:T' via Cs" by (auto split:split_if_asm)
  with field have eq:"T = T'" by (rule sees_field_fun)
  with casts wte wf have conf:"P,h \<turnstile> v' :\<le> T'"
    by(auto intro:casts_conf)
  from hconf ha have oconf:"P,h \<turnstile> (D,S) \<surd>" by (fastsimp simp:hconf_def)
  with S have suboD:"(D,Ds) \<in> Subobjs P" by (fastsimp simp:oconf_def)
  from field obtain Bs fs ms
    where subo:"(last Cs',Cs) \<in> Subobjs P"
    and class:"class P (last Cs) = Some(Bs,fs,ms)"
    and map:"map_of fs F = Some T"
    by (auto simp:LeastFieldDecl_def FieldDecls_def)
  from Ds subo have last:"last Cs = last Ds"
    by(fastsimp dest:Subobjs_nonempty intro:appendPath_last simp:appendPath_last)
  with class have classDs:"class P (last Ds) = Some(Bs,fs,ms)" by simp
  with S suboD oconf have "P,h \<turnstile> fs' (:\<le>) map_of fs"
    apply (auto simp:oconf_def)
    apply (erule allE)
    apply (erule_tac x="Ds" in allE)
    apply (erule_tac x="fs'" in allE)
    apply clarsimp
    done
  with map conf eq have fconf:"P,h \<turnstile> fs'(F \<mapsto> v') (:\<le>) map_of fs"
    by (simp add:fconf_def)
  from oconf have "\<forall>Cs fs'. (Cs,fs') \<in> S \<longrightarrow> (D,Cs) \<in> Subobjs P \<and> 
	            (\<exists>fs Bs ms. class P (last Cs) = Some (Bs,fs,ms) \<and> 
                                P,h \<turnstile> fs' (:\<le>) map_of fs)"
    by(simp add:oconf_def)
  with suboD classDs fconf 
  have oconf':"\<forall>Cs fs'. (Cs,fs') \<in> ?S' \<longrightarrow> (D,Cs) \<in> Subobjs P \<and> 
	            (\<exists>fs Bs ms. class P (last Cs) = Some (Bs,fs,ms) \<and> 
                                P,h \<turnstile> fs' (:\<le>) map_of fs)"
    by auto
  from oconf have all:"\<forall>Cs. (D,Cs) \<in> Subobjs P \<longrightarrow> (\<exists> fs'. (Cs,fs') \<in> S)"
    by(simp add:oconf_def)
  hence "\<forall>Cs. (D,Cs) \<in> Subobjs P \<longrightarrow> (\<exists> fs'. (Cs,fs') \<in> ?S')" by blast
  with oconf' have oconf':"P,h \<turnstile> (D,?S') \<surd>"
    by (simp add:oconf_def)
  with hconf ha show ?case by (rule hconf_upd_obj)
qed auto




theorem assumes wf:"wwf_prog P"
shows red_preserves_lconf:
  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow>
  (\<And>T. \<lbrakk> P,E,h \<turnstile> e:T; P,h \<turnstile> l (:\<le>)\<^sub>w E; envconf P E \<rbrakk> \<Longrightarrow> P,h' \<turnstile> l' (:\<le>)\<^sub>w E)"
and reds_preserves_lconf:
  "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow>
  (\<And>Ts. \<lbrakk> P,E,h \<turnstile> es[:]Ts; P,h \<turnstile> l (:\<le>)\<^sub>w E; envconf P E \<rbrakk> \<Longrightarrow> P,h' \<turnstile> l' (:\<le>)\<^sub>w E)"

proof(induct rule:red_reds_induct)
  case RedNew thus ?case
    by(fast intro:lconf_hext red_hext_incr[OF red_reds.RedNew])
next
  case (RedLAss E T V h l v v' T')
  have casts:"P \<turnstile> T casts v to v'" and env:"E V = Some T"
    and wt:"P,E,h \<turnstile> V:=Val v : T'" and lconf:"P,h \<turnstile> l (:\<le>)\<^sub>w E" .
  from wt env have eq:"T = T'" by auto
  with casts wt wf have conf:"P,h \<turnstile> v' :\<le> T'"
    by(auto intro:casts_conf)
  with lconf env eq show ?case
    by (simp del:fun_upd_apply)(erule lconf_upd,simp_all)
next
  case RedFAss thus ?case
    by(auto intro:lconf_hext red_hext_incr[OF red_reds.RedFAss] 
         simp del:fun_upd_apply)
next
  case (BlockRedNone E T V e e' h h' l l' T')
  have red:"P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and IH: "\<And>T''. \<lbrakk> P,E(V \<mapsto> T),h \<turnstile> e : T''; P,h \<turnstile> l(V:=None) (:\<le>)\<^sub>w E(V \<mapsto> T);
                      envconf P (E(V \<mapsto> T)) \<rbrakk>
                   \<Longrightarrow> P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V \<mapsto> T)"
    and lconf: "P,h \<turnstile> l (:\<le>)\<^sub>w E" and wte: "P,E,h \<turnstile> {V:T; e} : T'"
    and envconf:"envconf P E" .
  from lconf_hext[OF lconf red_hext_incr[OF red]]
  have lconf':"P,h' \<turnstile> l (:\<le>)\<^sub>w E" .
  from wte have wte':"P,E(V\<mapsto>T),h \<turnstile> e : T'" and type:"is_type P T"
    by (auto elim:WTrt_WTrts.elims)
  from envconf type have envconf':"envconf P (E(V \<mapsto> T))"
    by(auto simp:envconf_def)
  from lconf have "P,h \<turnstile> (l(V := None)) (:\<le>)\<^sub>w E(V\<mapsto>T)"
    by (simp add:lconf_def fun_upd_apply)
  from IH[OF wte' this envconf'] have "P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V\<mapsto>T)" .
  with lconf' show ?case
    by (fastsimp simp:lconf_def fun_upd_apply split:split_if_asm)
next
  case (BlockRedSome E T V e e' h h' l l' v T')
  have red:"P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and IH: "\<And>T''. \<lbrakk> P,E(V \<mapsto> T),h \<turnstile> e : T''; P,h \<turnstile> l(V:=None) (:\<le>)\<^sub>w E(V \<mapsto> T);
                      envconf P (E(V \<mapsto> T)) \<rbrakk>
                   \<Longrightarrow> P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V \<mapsto> T)"
    and lconf: "P,h \<turnstile> l (:\<le>)\<^sub>w E" and wte: "P,E,h \<turnstile> {V:T; e} : T'"
    and envconf:"envconf P E" .
  from lconf_hext[OF lconf red_hext_incr[OF red]]
  have lconf':"P,h' \<turnstile> l (:\<le>)\<^sub>w E" .
  from wte have wte':"P,E(V\<mapsto>T),h \<turnstile> e : T'" and type:"is_type P T"
    by (auto elim:WTrt_WTrts.elims)
  from envconf type have envconf':"envconf P (E(V \<mapsto> T))"
    by(auto simp:envconf_def)
  from lconf have "P,h \<turnstile> (l(V := None)) (:\<le>)\<^sub>w E(V\<mapsto>T)"
    by (simp add:lconf_def fun_upd_apply)
  from IH[OF wte' this envconf'] have "P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V\<mapsto>T)" .
  with lconf' show ?case
    by (fastsimp simp:lconf_def fun_upd_apply split:split_if_asm)
next
  case (InitBlockRed E T V e e' h h' l l' v v' v'' T')
  have red: "P,E(V \<mapsto> T) \<turnstile> \<langle>e, (h, l(V\<mapsto>v'))\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
     and IH: "\<And>T''. \<lbrakk> P,E(V \<mapsto> T),h \<turnstile> e : T''; P,h \<turnstile> l(V \<mapsto> v') (:\<le>)\<^sub>w E(V \<mapsto> T); 
                       envconf P (E(V \<mapsto> T)) \<rbrakk>
                   \<Longrightarrow> P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V \<mapsto> T)"
    and lconf:"P,h \<turnstile> l (:\<le>)\<^sub>w E" and l':"l' V = Some v''"
    and wte:"P,E,h \<turnstile> {V:T; V:=Val v;; e} : T'"
    and casts:"P \<turnstile> T casts v to v'" and envconf:"envconf P E" .
  from lconf_hext[OF lconf red_hext_incr[OF red]]
  have lconf':"P,h' \<turnstile> l (:\<le>)\<^sub>w E" .
  from wte obtain T'' where wte':"P,E(V\<mapsto>T),h \<turnstile> e : T'"
    and wt:"P,E(V \<mapsto> T),h \<turnstile> V:=Val v : T''"
    and type:"is_type P T"
    by (auto elim:WTrt_WTrts.elims)
  from envconf type have envconf':"envconf P (E(V \<mapsto> T))"
    by(auto simp:envconf_def)
  from wt have "T'' = T" by auto
  with wf casts wt have "P,h \<turnstile> v' :\<le> T"
    by(auto intro:casts_conf)
  with lconf have "P,h \<turnstile> l(V \<mapsto> v') (:\<le>)\<^sub>w E(V\<mapsto>T)"
    by -(rule lconf_upd2)
  from IH[OF wte' this envconf'] have "P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V \<mapsto> T)" .
  with lconf' show ?case
    by (fastsimp simp:lconf_def fun_upd_apply split:split_if_asm)
qed auto




text{* Preservation of definite assignment more complex and requires a
few lemmas first. *}

lemma [iff]: "\<And>A. \<lbrakk> length Vs = length Ts; length vs = length Ts\<rbrakk> \<Longrightarrow>
 \<D> (blocks (Vs,Ts,vs,e)) A = \<D> e (A \<squnion> \<lfloor>set Vs\<rfloor>)"

apply(induct Vs Ts vs e rule:blocks.induct)
apply(simp_all add:hyperset_defs)
done



lemma red_lA_incr: "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> \<lfloor>dom l\<rfloor> \<squnion> \<A> e \<sqsubseteq>  \<lfloor>dom l'\<rfloor> \<squnion> \<A> e'"
and reds_lA_incr: "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> \<lfloor>dom l\<rfloor> \<squnion> \<A>s es \<sqsubseteq>  \<lfloor>dom l'\<rfloor> \<squnion> \<A>s es'"

apply(induct rule:red_reds_induct)
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
apply blast+
done



text{* Now preservation of definite assignment. *}

lemma assumes wf: "wf_C_prog P"
shows red_preserves_defass:
  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> \<D> e \<lfloor>dom l\<rfloor> \<Longrightarrow> \<D> e' \<lfloor>dom l'\<rfloor>"
and "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> \<D>s es \<lfloor>dom l\<rfloor> \<Longrightarrow> \<D>s es' \<lfloor>dom l'\<rfloor>"

proof (induct rule:red_reds_induct)
  case BinOpRed1 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case FAssRed1 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case CallObj thus ?case by (auto elim!: Ds_mono[OF red_lA_incr])
next
  case (RedCall C Cs Cs' Ds E M S T T' Ts Ts' a body body' new_body pns pns' h l vs )
  thus ?case
    apply (auto dest!:select_method_wf_mdecl[OF wf] simp:wf_mdecl_def elim!:D_mono')
    apply(cases T') apply auto
    by(rule_tac A="\<lfloor>insert this (set pns)\<rfloor>" in D_mono,clarsimp simp:hyperset_defs,
          assumption)+
(*next
  case RedCallClass thus ?case
    apply (auto dest!:select_method_wf_mdecl[OF wf] simp:wf_mdecl_def elim!:D_mono')
    by(auto simp:hyperset_defs)*)
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
  case RedWhile thus ?case by(auto simp:hyperset_defs elim!:D_mono')
next
  case ListRed1 thus ?case by (auto elim!: Ds_mono[OF red_lA_incr])
qed (auto simp:hyperset_defs)




text{* Combining conformance of heap and local variables: *}

constdefs
  sconf :: "prog \<Rightarrow> env \<Rightarrow> state \<Rightarrow> bool"   ("_,_ \<turnstile> _ \<surd>"   [51,51,51]50)
  "P,E \<turnstile> s \<surd>  \<equiv>  let (h,l) = s in P \<turnstile> h \<surd> \<and> P,h \<turnstile> l (:\<le>)\<^sub>w E \<and> envconf P E"

lemma red_preserves_sconf:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>; P,E,hp s \<turnstile> e : T; P,E \<turnstile> s \<surd>; wwf_prog P\<rbrakk> 
\<Longrightarrow> P,E \<turnstile> s' \<surd>"

by(fastsimp intro:red_preserves_hconf red_preserves_lconf
            simp add:sconf_def)


lemma reds_preserves_sconf:
  "\<lbrakk> P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>; P,E,hp s \<turnstile> es [:] Ts; P,E \<turnstile> s \<surd>; wwf_prog P\<rbrakk> 
\<Longrightarrow> P,E \<turnstile> s' \<surd>"

by(fastsimp intro:reds_preserves_hconf reds_preserves_lconf
            simp add:sconf_def)





subsection "Subject reduction"

lemma wt_blocks:
 "\<And>E. \<lbrakk> length Vs = length Ts; length vs = length Ts;
         \<forall>T' \<in> set Ts. is_type P T'\<rbrakk> \<Longrightarrow>
       (P,E,h \<turnstile> blocks(Vs,Ts,vs,e) : T) =
  (P,E(Vs[\<mapsto>]Ts),h \<turnstile> e:T \<and> 
  (\<exists>Ts'. map (P \<turnstile> typeof\<^bsub>h\<^esub>) vs = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] Ts))"

proof(induct Vs Ts vs e rule:blocks.induct)
  case (5 V Vs T' Ts v vs e)
  have length:"length (V#Vs) = length (T'#Ts)" "length (v#vs) = length (T'#Ts)"
    and type:"\<forall>S \<in> set (T'#Ts). is_type P S"
    and IH:"\<And>E. \<lbrakk>length Vs = length Ts; length vs = length Ts;
                  \<forall>S \<in> set Ts. is_type P S\<rbrakk>
     \<Longrightarrow> (P,E,h \<turnstile> blocks (Vs, Ts, vs, e) : T) =
         (P,E(Vs [\<mapsto>] Ts),h \<turnstile> e : T \<and>
            (\<exists>Ts'. map P \<turnstile> typeof\<^bsub>h\<^esub> vs = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] Ts))" .
  from type have typeT':"is_type P T'" and type':"\<forall>S \<in> set Ts. is_type P S"
    by simp_all
  from length have "length Vs = length Ts" "length vs = length Ts"
    by simp_all
  from IH[OF this type'] have eq:"(P,E(V \<mapsto> T'),h \<turnstile> blocks (Vs,Ts,vs,e) : T) =
  (P,E(V \<mapsto> T')(Vs [\<mapsto>] Ts),h \<turnstile> e : T \<and>
   (\<exists>Ts'. map P \<turnstile> typeof\<^bsub>h\<^esub> vs = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] Ts))" .
  show ?case
  proof(rule iffI)
    assume "P,E,h \<turnstile> blocks (V#Vs,T'#Ts,v#vs,e) : T"
    then have wt:"P,E(V \<mapsto> T'),h \<turnstile> V:=Val v : T'"
      and blocks:"P,E(V \<mapsto> T'),h \<turnstile> blocks (Vs,Ts,vs,e) : T" by auto
    from blocks eq obtain Ts' where wte:"P,E(V \<mapsto> T')(Vs [\<mapsto>] Ts),h \<turnstile> e : T"
      and typeof:"map P \<turnstile> typeof\<^bsub>h\<^esub> vs = map Some Ts'" and subs:"P \<turnstile> Ts' [\<le>] Ts"
      by auto
    from wt obtain T'' where "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T''" and "P \<turnstile> T'' \<le> T'"
      by auto
    with wte typeof subs
    show "P,E(V # Vs [\<mapsto>] T' # Ts),h \<turnstile> e : T \<and>
          (\<exists>Ts'. map P \<turnstile> typeof\<^bsub>h\<^esub> (v # vs) = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] (T' # Ts))"
      by auto
  next
    assume "P,E(V # Vs [\<mapsto>] T' # Ts),h \<turnstile> e : T \<and>
      (\<exists>Ts'. map P \<turnstile> typeof\<^bsub>h\<^esub> (v # vs) = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] (T' # Ts))"
    then obtain Ts' where wte:"P,E(V # Vs [\<mapsto>] T' # Ts),h \<turnstile> e : T"
      and typeof:"map P \<turnstile> typeof\<^bsub>h\<^esub> (v # vs) = map Some Ts'"
      and subs:"P \<turnstile> Ts' [\<le>] (T'#Ts)" by auto
    from subs obtain U Us where Ts':"Ts' = U#Us" by(cases Ts') auto
    with wte typeof subs eq have blocks:"P,E(V \<mapsto> T'),h \<turnstile> blocks (Vs,Ts,vs,e) : T"
      by auto
    from Ts' typeof subs have "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some U"
      and "P \<turnstile> U \<le> T'" by (auto simp:fun_of_def)
    hence wtval:"P,E(V \<mapsto> T'),h \<turnstile> V:=Val v : T'" by auto
    with blocks typeT' show "P,E,h \<turnstile> blocks (V#Vs,T'#Ts,v#vs,e) : T" by auto
  qed
qed auto




theorem assumes wf: "wf_C_prog P"
shows subject_reduction2: "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow>
  (\<And>T. \<lbrakk> P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T \<rbrakk> \<Longrightarrow> type_conf P E T h' e')"
and subjects_reduction2: "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow>
  (\<And>Ts.\<lbrakk> P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> es [:] Ts \<rbrakk> \<Longrightarrow> types_conf (P,E,Ts,h',es'))"

proof (induct rule:red_reds_induct)
  case (RedNew C E a h h' l)
  have new:"new_Addr h = Some a" and h':"h' = h(a \<mapsto> (C, init_obj P C))" 
    and wt:"P,E,h \<turnstile> new C : T" .
  from wt have eq:"T = Class C" and class:"is_class P C" by auto
  from class have subo:"(C,[C]) \<in> Subobjs P" by(rule Subobjs_Base)
  from h' have "h' a = Some(C, init_obj P C)" by(simp add:map_upd_Some_unfold)
  with subo have "P,E,h' \<turnstile> ref(a,[C]) : Class C" by auto
  with eq show ?case by auto
next
  case (RedNewFail C E h l)
  have sconf:"P,E \<turnstile> (h, l) \<surd>" .
  from wf have "is_class P OutOfMemory" 
    by (fastsimp intro:is_class_xcpt wf_prog_wwf_prog)
  hence "preallocated h \<Longrightarrow> P \<turnstile> typeof\<^bsub>h\<^esub> (Ref (addr_of_sys_xcpt OutOfMemory,[OutOfMemory])) = Some(Class OutOfMemory)"
    by (auto elim: preallocatedE dest!:preallocatedD Subobjs_Base)
  with sconf have "P,E,h \<turnstile> THROW OutOfMemory : T" by(auto simp:sconf_def hconf_def)
  thus ?case by (fastsimp intro:wt_same_type_typeconf)
next
  case (StaticCastRed C E e e' h l h' l')
  have wt:"P,E,h \<turnstile> \<lparr>C\<rparr>e : T"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> 
            \<Longrightarrow> type_conf P E T' h' e'"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" .
  from wt obtain T' where wte:"P,E,h \<turnstile> e : T'" and isref:"is_refT T'" 
    and class:"is_class P C" and T:"T = Class C"
    by auto
  from isref have "P,E,h' \<turnstile> \<lparr>C\<rparr>e' : Class C"
  proof(rule refTE)
    assume "T' = NT"
    with IH[OF sconf wte] isref class show ?thesis by auto
  next
    fix D assume "T' = Class D"
    with IH[OF sconf wte] isref class show ?thesis by auto
  qed
  with T show ?case by (fastsimp intro:wt_same_type_typeconf)
next
  case RedStaticCastNull
  thus ?case by (auto elim:WTrt_WTrts.elims)
next
  case (RedStaticUpCast C Cs Cs' Ds E a h l)
  have wt:"P,E,h \<turnstile> \<lparr>C\<rparr>ref (a,Cs) : T"
    and path_via:"P \<turnstile> Path last Cs to C via Cs'"
    and Ds:"Ds = Cs @\<^sub>p Cs'" .
  from wt have typeof:"P \<turnstile> typeof\<^bsub>h\<^esub> (Ref(a,Cs)) = Some(Class(last Cs))"
    and class:"is_class P C" and T:"T = Class C"
    by auto
  from typeof obtain D S where h:"h a = Some(D,S)" and subo:"(D,Cs) \<in> Subobjs P"
    by (auto dest:typeof_Class_Subo split:split_if_asm)
  from path_via subo wf Ds have "(D,Ds) \<in> Subobjs P" and last:"last Ds = C"
    by(auto intro!:Subobjs_appendPath appendPath_last[THEN sym] Subobjs_nonempty
            simp:path_via_def)
  with h have "P,E,h \<turnstile> ref (a,Ds) : Class C" by auto
  with T show ?case by (fastsimp intro:wt_same_type_typeconf)
next
  case (RedStaticDownCast C Cs Cs' E a h l)
  have wt:"P,E,h \<turnstile> \<lparr>C\<rparr>ref (a,Cs@[C]@Cs') : T"
    and notin:"C \<notin> set Cs'" .
  from wt have typeof:"P \<turnstile> typeof\<^bsub>h\<^esub> (Ref(a,Cs@[C]@Cs')) = 
                       Some(Class(last(Cs@[C]@Cs')))"
    and class:"is_class P C" and T:"T = Class C"
    by auto
  from typeof obtain D S where h:"h a = Some(D,S)" 
    and subo:"(D,Cs@[C]@Cs') \<in> Subobjs P"
    by (auto dest:typeof_Class_Subo split:split_if_asm)
  from subo have "(D,Cs@[C]) \<in> Subobjs P" by(fastsimp intro:appendSubobj)
  with h have "P,E,h \<turnstile> ref (a,Cs@[C]) : Class C" by auto
  with T show ?case by (fastsimp intro:wt_same_type_typeconf)
next
  case (RedStaticCastFail C Cs E a h l)
  have sconf:"P,E \<turnstile> (h, l) \<surd>" .
  from wf have "is_class P ClassCast" 
    by (fastsimp intro:is_class_xcpt wf_prog_wwf_prog)
  hence "preallocated h \<Longrightarrow> P \<turnstile> typeof\<^bsub>h\<^esub> (Ref (addr_of_sys_xcpt ClassCast,[ClassCast])) = Some(Class ClassCast)"
    by (auto elim: preallocatedE dest!:preallocatedD Subobjs_Base)
  with sconf have "P,E,h \<turnstile> THROW ClassCast : T" by(auto simp:sconf_def hconf_def)
  thus ?case by (fastsimp intro:wt_same_type_typeconf)
next
  case (DynCastRed C E e e' h l h' l')
  have wt:"P,E,h \<turnstile> Cast C e : T"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> 
            \<Longrightarrow> type_conf P E T' h' e'"
    and sconf:"P,E \<turnstile> (h,l) \<surd>" .
  from wt obtain T' where wte:"P,E,h \<turnstile> e : T'" and isref:"is_refT T'" 
    and class:"is_class P C" and T:"T = Class C"
    by auto
  from isref have "P,E,h' \<turnstile> Cast C e' : Class C"
  proof(rule refTE)
    assume "T' = NT"
    with IH[OF sconf wte] isref class show ?thesis by auto
  next
    fix D assume "T' = Class D"
    with IH[OF sconf wte] isref class show ?thesis by auto
  qed
  with T show ?case by (fastsimp intro:wt_same_type_typeconf)
next
  case RedDynCastNull
  thus ?case by (auto elim:WTrt_WTrts.elims)
next
  case (RedDynCast C Cs Cs' D E S a h l)
  have wt:"P,E,h \<turnstile> Cast C (ref (a,Cs)) : T"
    and path_via:"P \<turnstile> Path D to C via Cs'"
    and hp:"hp (h,l) a = Some(D,S)" .
  from wt have typeof:"P \<turnstile> typeof\<^bsub>h\<^esub> (Ref(a,Cs)) = Some(Class(last Cs))"
    and class:"is_class P C" and T:"T = Class C"
    by auto
  from typeof hp have subo:"(D,Cs) \<in> Subobjs P"
    by (auto dest:typeof_Class_Subo split:split_if_asm)
  from path_via subo have "(D,Cs') \<in> Subobjs P" 
    and last:"last Cs' = C" by (auto simp:path_via_def)
  with hp have "P,E,h \<turnstile> ref (a,Cs') : Class C" by auto
  with T show ?case by (fastsimp intro:wt_same_type_typeconf)
next
  case (RedStaticUpDynCast C Cs Cs' Ds E a h l)
  have wt:"P,E,h \<turnstile> Cast C (ref (a,Cs)) : T"
    and path_via:"P \<turnstile> Path last Cs to C via Cs'"
    and Ds:"Ds = Cs @\<^sub>p Cs'" .
  from wt have typeof:"P \<turnstile> typeof\<^bsub>h\<^esub> (Ref(a,Cs)) = Some(Class(last Cs))"
    and class:"is_class P C" and T:"T = Class C"
    by auto
  from typeof obtain D S where h:"h a = Some(D,S)" and subo:"(D,Cs) \<in> Subobjs P"
    by (auto dest:typeof_Class_Subo split:split_if_asm)
  from path_via subo wf Ds have "(D,Ds) \<in> Subobjs P" and last:"last Ds = C"
    by(auto intro!:Subobjs_appendPath appendPath_last[THEN sym] Subobjs_nonempty
            simp:path_via_def)
  with h have "P,E,h \<turnstile> ref (a,Ds) : Class C" by auto
  with T show ?case by (fastsimp intro:wt_same_type_typeconf)
next
  case (RedStaticDownDynCast C Cs Cs' E a h l)
  have wt:"P,E,h \<turnstile> Cast C (ref (a,Cs@[C]@Cs')) : T"
    and notin:"C \<notin> set Cs'" .
  from wt have typeof:"P \<turnstile> typeof\<^bsub>h\<^esub> (Ref(a,Cs@[C]@Cs')) = 
                       Some(Class(last(Cs@[C]@Cs')))"
    and class:"is_class P C" and T:"T = Class C"
    by auto
  from typeof obtain D S where h:"h a = Some(D,S)" 
    and subo:"(D,Cs@[C]@Cs') \<in> Subobjs P"
    by (auto dest:typeof_Class_Subo split:split_if_asm)
  from subo have "(D,Cs@[C]) \<in> Subobjs P" by(fastsimp intro:appendSubobj)
  with h have "P,E,h \<turnstile> ref (a,Cs@[C]) : Class C" by auto
  with T show ?case by (fastsimp intro:wt_same_type_typeconf)
next
  case RedDynCastFail thus ?case by fastsimp
next
  case (BinOpRed1 E bop e e' e\<^isub>2 h l h' l')
  have red:"P,E \<turnstile> \<langle>e,(h, l)\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and wt:"P,E,h \<turnstile> e \<guillemotleft>bop\<guillemotright> e\<^isub>2 : T"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> 
            \<Longrightarrow> type_conf P E T' h' e'"
    and sconf:"P,E \<turnstile> (h,l) \<surd>" .
  from wt obtain T\<^isub>1 T\<^isub>2 where wte:"P,E,h \<turnstile> e : T\<^isub>1" and wte2:"P,E,h \<turnstile> e\<^isub>2 : T\<^isub>2"
    and binop:"case bop of Eq \<Rightarrow> T = Boolean
                        | Add \<Rightarrow> T\<^isub>1 = Integer \<and> T\<^isub>2 = Integer \<and> T = Integer"
    by auto
  from WTrt_hext_mono[OF wte2 red_hext_incr[OF red]] have wte2':"P,E,h' \<turnstile> e\<^isub>2 : T\<^isub>2" .
  have "P,E,h' \<turnstile> e' \<guillemotleft>bop\<guillemotright> e\<^isub>2 : T"
  proof (cases bop)
    assume Eq:"bop = Eq"
    from IH[OF sconf wte] obtain T' where "P,E,h' \<turnstile> e' : T'"
      by (cases "T\<^isub>1") auto
    with wte2' binop Eq show ?thesis by(cases bop) auto
  next
    assume Add:"bop = Add"
    with binop have Intg:"T\<^isub>1 = Integer" by simp
    with IH[OF sconf wte] have "P,E,h' \<turnstile> e' : Integer" by simp
    with wte2' binop Add show ?thesis by(cases bop) auto
  qed
  with binop show ?case by(cases bop) simp_all
next
  case (BinOpRed2 E bop e e' h l h' l' v\<^isub>1)
  have red:"P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
    and wt:"P,E,h \<turnstile> Val v\<^isub>1 \<guillemotleft>bop\<guillemotright> e : T"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> 
            \<Longrightarrow> type_conf P E T' h' e'"
    and sconf:"P,E \<turnstile> (h,l) \<surd>" .
  from wt obtain T\<^isub>1 T\<^isub>2 where wtval:"P,E,h \<turnstile> Val v\<^isub>1 : T\<^isub>1" and wte:"P,E,h \<turnstile> e : T\<^isub>2"
    and binop:"case bop of Eq \<Rightarrow> T = Boolean
                        | Add \<Rightarrow> T\<^isub>1 = Integer \<and> T\<^isub>2 = Integer \<and> T = Integer"
    by auto
  from WTrt_hext_mono[OF wtval red_hext_incr[OF red]]
  have wtval':"P,E,h' \<turnstile> Val v\<^isub>1 : T\<^isub>1" .
  have "P,E,h' \<turnstile> Val v\<^isub>1 \<guillemotleft>bop\<guillemotright> e' : T"
  proof (cases bop)
    assume Eq:"bop = Eq"
    from IH[OF sconf wte] obtain T' where "P,E,h' \<turnstile> e' : T'"
      by (cases "T\<^isub>2") auto
    with wtval' binop Eq show ?thesis by(cases bop) auto
  next
    assume Add:"bop = Add"
    with binop have Intg:"T\<^isub>2 = Integer" by simp
    with IH[OF sconf wte] have "P,E,h' \<turnstile> e' : Integer" by simp
    with wtval' binop Add show ?thesis by(cases bop) auto
  qed
  with binop show ?case by(cases bop) simp_all
next
  case (RedBinOp E bop) thus ?case
  proof (cases bop)
    case Eq thus ?thesis using RedBinOp by auto
  next
    case Add thus ?thesis using RedBinOp by auto
  qed
next
  case (RedVar E V h l v)
  have l:"lcl (h, l) V = Some v" and sconf:"P,E \<turnstile> (h, l) \<surd>"
    and wt:"P,E,h \<turnstile> Var V : T" .
  hence conf:"P,h \<turnstile> v :\<le> T" by(force simp:sconf_def lconf_def)
  show ?case
  proof(cases "\<forall>C. T \<noteq> Class C")
    case True 
    with conf have "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T" by(cases T) auto
    hence "P,E,h \<turnstile> Val v : T" by auto
    thus ?thesis by(rule wt_same_type_typeconf)
  next
    case False
    then obtain C where T:"T = Class C" by auto
    with conf have "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some(Class C) \<or> P \<turnstile> typeof\<^bsub>h\<^esub> v = Some NT"
      by simp
    with T show ?thesis by simp
  qed
next
  case (LAssRed E V e e' h l h' l')
  have wt:"P,E,h \<turnstile> V:=e : T" and sconf:"P,E \<turnstile> (h, l) \<surd>"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h, l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> \<Longrightarrow> type_conf P E T' h' e'" .
  from wt obtain T' where wte:"P,E,h \<turnstile> e : T'" and env:"E V = Some T" 
    and sub:"P \<turnstile> T' \<le> T" by auto
  from sconf env have "is_type P T" by(auto simp:sconf_def envconf_def)
  from sub this wf show ?case
  proof(rule subE)
    assume eq:"T' = T" and notclass:"\<forall>C. T' \<noteq> Class C"
    with IH[OF sconf wte] have "P,E,h' \<turnstile> e' : T" by(cases T) auto
    with eq env have "P,E,h' \<turnstile> V:=e' : T" by auto
    with eq show ?thesis by(cases T) auto
  next
    fix C D
    assume T':"T' = Class C" and T:"T = Class D" 
      and path_unique:"P \<turnstile> Path C to D unique"
    with IH[OF sconf wte] have "P,E,h' \<turnstile> e' : Class C \<or> P,E,h' \<turnstile> e' : NT"
      by simp
    hence "P,E,h' \<turnstile> V:=e' : T"
    proof(rule disjE)
      assume "P,E,h' \<turnstile> e' : Class C"
      with env T' sub show ?thesis by (fastsimp intro:WTrtLAss)
    next
      assume "P,E,h' \<turnstile> e' : NT"
      with env T show ?thesis by (fastsimp intro:WTrtLAss)
    qed
    with T show ?thesis by(cases T) auto
  next
    fix C
    assume T':"T' = NT" and T:"T = Class C"
    with IH[OF sconf wte] have "P,E,h' \<turnstile> e' : NT" by simp
    with env T show ?thesis by (fastsimp intro:WTrtLAss)
  qed
next
  case (RedLAss E T V h l v v' T')
  have env:"E V = Some T" and casts:"P \<turnstile> T casts v to v'"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> V:=Val v : T'" .
  show ?case
  proof(cases "\<forall>C. T \<noteq> Class C")
    case True
    with casts wt env show ?thesis
      by(cases T',auto elim!:casts_to.elims)
  next
    case False
    then obtain C where "T = Class C" by auto
    with casts wt env wf show ?thesis
      by(auto elim!:casts_to.elims,
	 auto intro!:sym[OF appendPath_last] Subobjs_nonempty split:split_if_asm 
              simp:path_via_def,drule_tac Cs="Cs" in Subobjs_appendPath,auto)
  qed
next
  case (FAccRed Cs E F e e' h l h' l')
  have red:"P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
    and wt:"P,E,h \<turnstile> e\<bullet>F{Cs} : T"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> 
            \<Longrightarrow> type_conf P E T' h' e'"
    and sconf:"P,E \<turnstile> (h,l) \<surd>" .
  from wt have "P,E,h' \<turnstile> e'\<bullet>F{Cs} : T"
  proof(rule WTrt_elim_cases)
    fix C assume wte: "P,E,h \<turnstile> e : Class C"
      and field:"P \<turnstile> C has least F:T via Cs"
      and notemptyCs:"Cs \<noteq> []"
    from field have class:"is_class P C"
      by (fastsimp intro:Subobjs_isClass simp add:LeastFieldDecl_def FieldDecls_def)
    from IH[OF sconf wte] have "P,E,h' \<turnstile> e' : NT \<or> P,E,h' \<turnstile> e' : Class C" by auto
    thus ?thesis
    proof(rule disjE)
      assume "P,E,h' \<turnstile> e' : NT"
      thus ?thesis by (fastsimp intro!:WTrtFAccNT)
    next
      assume wte':"P,E,h' \<turnstile> e' : Class C"
      from wte' notemptyCs field show ?thesis by(rule WTrtFAcc)
    qed
  next
    assume wte: "P,E,h \<turnstile> e : NT"
    from IH[OF sconf wte] have "P,E,h' \<turnstile> e' : NT" by auto
    thus ?thesis by (rule WTrtFAccNT)
  qed
  thus ?case by(rule wt_same_type_typeconf)
next
  case (RedFAcc Cs Cs' D Ds E F S a fs' h l v)
  have h:"hp (h,l) a = Some(D,S)" 
    and Ds:"Ds = Cs'@\<^sub>pCs" and S:"(Ds,fs') \<in> S"
    and fs':"fs' F = Some v" and sconf:"P,E \<turnstile> (h,l) \<surd>"
    and wte:"P,E,h \<turnstile> ref (a,Cs')\<bullet>F{Cs} : T" .
  from wte have field:"P \<turnstile> last Cs' has least F:T via Cs"
    and notemptyCs:"Cs \<noteq> []"
    by (auto split:split_if_asm)
  from h S sconf obtain Bs fs ms where classDs:"class P (last Ds) = Some (Bs,fs,ms)"
    and fconf:"P,h \<turnstile> fs' (:\<le>) map_of fs"
    by (simp add:sconf_def hconf_def oconf_def) blast
  from field Ds have "last Cs = last Ds"
    by (fastsimp intro!:appendPath_last Subobjs_nonempty 
                   simp:LeastFieldDecl_def FieldDecls_def)
  with field classDs have map:"map_of fs F =  Some T"
    by (simp add:LeastFieldDecl_def FieldDecls_def)
  with fconf fs' have conf:"P,h \<turnstile> v :\<le> T"
    by (simp add:fconf_def,erule_tac x="F" in allE,fastsimp)
  thus ?case by (cases T) auto
next
  case (RedFAccNull Cs E F h l)
  have sconf:"P,E \<turnstile> (h, l) \<surd>" .
  from wf have "is_class P NullPointer" 
    by (fastsimp intro:is_class_xcpt wf_prog_wwf_prog)
  hence "preallocated h \<Longrightarrow> P \<turnstile> typeof\<^bsub>h\<^esub> (Ref (addr_of_sys_xcpt NullPointer,[NullPointer])) = Some(Class NullPointer)"
    by (auto elim: preallocatedE dest!:preallocatedD Subobjs_Base)
  with sconf have "P,E,h \<turnstile> THROW NullPointer : T" by(auto simp:sconf_def hconf_def)
  thus ?case by (fastsimp intro:wt_same_type_typeconf wf_prog_wwf_prog)
next
  case (FAssRed1 Cs E F e e' e\<^isub>2 h l h' l')
  have red:"P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
    and wt:"P,E,h \<turnstile> e\<bullet>F{Cs} := e\<^isub>2 : T"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> 
            \<Longrightarrow> type_conf P E T' h' e'"
    and sconf:"P,E \<turnstile> (h,l) \<surd>" .
  from wt have "P,E,h' \<turnstile> e'\<bullet>F{Cs} := e\<^isub>2 : T"
  proof (rule WTrt_elim_cases)
    fix C T' assume wte: "P,E,h \<turnstile> e : Class C"
      and field:"P \<turnstile> C has least F:T via Cs"
      and notemptyCs:"Cs \<noteq> []"
      and wte2:"P,E,h \<turnstile> e\<^isub>2 : T'" and sub:"P \<turnstile> T' \<le> T"
    have wte2': "P,E,h' \<turnstile> e\<^isub>2 : T'"
      by(rule WTrt_hext_mono[OF wte2 red_hext_incr[OF red]])
    from IH[OF sconf wte] have "P,E,h' \<turnstile> e' : Class C \<or> P,E,h' \<turnstile> e' : NT"
      by simp
    thus ?thesis
    proof(rule disjE)
      assume wte':"P,E,h' \<turnstile> e' : Class C"
      from wte' notemptyCs field wte2' sub show ?thesis by (rule WTrtFAss)
    next
      assume wte':"P,E,h' \<turnstile> e' : NT"
      from wte' wte2' show ?thesis by (rule WTrtFAssNT)
    qed
  next
    fix T' assume wte:"P,E,h \<turnstile> e : NT"
      and wte2:"P,E,h \<turnstile> e\<^isub>2 : T'" and sub:"P \<turnstile> T' \<le> T"
    have wte2': "P,E,h' \<turnstile> e\<^isub>2 : T'"
      by(rule WTrt_hext_mono[OF wte2 red_hext_incr[OF red]])
    from IH[OF sconf wte] have wte':"P,E,h' \<turnstile> e' : NT" by simp
    from wte' wte2' show ?thesis by (rule WTrtFAssNT)
  qed
  thus ?case by(rule wt_same_type_typeconf)
next
  case (FAssRed2 Cs E F e e' h l h' l' v)
  have red:"P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
    and wt:"P,E,h \<turnstile> Val v\<bullet>F{Cs} := e : T"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> 
            \<Longrightarrow> type_conf P E T' h' e'"
    and sconf:"P,E \<turnstile> (h,l) \<surd>" .
  from wt have "P,E,h' \<turnstile> Val v\<bullet>F{Cs}:=e' : T"
  proof (rule WTrt_elim_cases)
    fix C T' assume wtval:"P,E,h \<turnstile> Val v : Class C"
      and field:"P \<turnstile> C has least F:T via Cs"
      and notemptyCs:"Cs \<noteq> []"
      and wte:"P,E,h \<turnstile> e : T'"
      and sub:"P \<turnstile> T' \<le> T"
    have wtval':"P,E,h' \<turnstile> Val v : Class C"
      by(rule WTrt_hext_mono[OF wtval red_hext_incr[OF red]])
    from field wf have type:"is_type P T" by(rule least_field_is_type)
    from sub type wf show ?thesis
    proof(rule subE)
      assume "T' = T" and notclass:"\<forall>C. T' \<noteq> Class C"
      from IH[OF sconf wte] notclass have wte':"P,E,h' \<turnstile> e' : T'" 
	by(cases T') auto
      from wtval' notemptyCs field wte' sub show ?thesis
	by(rule WTrtFAss)
    next
      fix C' D assume T':"T' = Class C'" and T:"T = Class D" 
	and path_unique:"P \<turnstile> Path C' to D unique"
      from IH[OF sconf wte] T' have "P,E,h' \<turnstile> e' : Class C' \<or> P,E,h' \<turnstile> e' : NT"
	by simp
      thus ?thesis
      proof(rule disjE)
	assume wte':"P,E,h' \<turnstile> e' : Class C'"
	from wtval' notemptyCs field wte' sub T' show ?thesis 
	  by (fastsimp intro: WTrtFAss)
      next
	assume wte':"P,E,h' \<turnstile> e' : NT"
	from wtval' notemptyCs field wte' sub T show ?thesis
	  by (fastsimp intro: WTrtFAss)
      qed
    next
      fix C' assume T':"T' = NT" and T:"T = Class C'"
      from IH[OF sconf wte] T' have wte':"P,E,h' \<turnstile> e' : NT" by simp
      from wtval' notemptyCs field wte' sub T show ?thesis
	by (fastsimp intro: WTrtFAss)
    qed
  next
    fix T' assume wtval:"P,E,h \<turnstile> Val v : NT"
      and wte:"P,E,h \<turnstile> e : T'"
      and sub:"P \<turnstile> T' \<le> T"
    have wtval':"P,E,h' \<turnstile> Val v : NT"
      by(rule WTrt_hext_mono[OF wtval red_hext_incr[OF red]])
    from IH[OF sconf wte] sub obtain T'' where wte':"P,E,h' \<turnstile> e' : T''"
      and sub':"P \<turnstile> T'' \<le> T" by (cases T',auto,cases T,auto)
    from wtval' wte' sub' show ?thesis
      by(rule WTrtFAssNT)
  qed
  thus ?case by(rule wt_same_type_typeconf)
next
  case (RedFAss Cs Cs' D Ds E F S T a fs h l v v' T')
  let ?fs' = "fs(F \<mapsto> v')"
  let ?S' = "insert (Ds, ?fs') (S - {(Ds, fs)})"
  let ?h' = "h(a \<mapsto> (D,?S'))"
  have h:"h a = Some(D,S)" and casts:"P \<turnstile> T casts v to v'"
    and field:"P \<turnstile> last Cs' has least F:T via Cs"
    and wt:"P,E,h \<turnstile> ref (a,Cs')\<bullet>F{Cs} := Val v : T'" .
  from wt wf have type:"is_type P T'" 
    by (auto dest:least_field_is_type split:split_if_asm)
  from wt field obtain T'' where wtval:"P,E,h \<turnstile> Val v : T''" and eq:"T = T'" 
    and leq:"P \<turnstile> T'' \<le> T'"
    by (auto dest:sees_field_fun split:split_if_asm)
  from casts eq wtval show ?case
  proof(induct rule:casts_to.induct)
    case (casts_prim T\<^isub>0 w)
    have "T\<^isub>0 = T'" and "\<forall>C. T\<^isub>0 \<noteq> Class C" and wtval':"P,E,h \<turnstile> Val w : T''" .
    with leq have "T' = T''" by(cases T',auto)
    with wtval' have "P,E,h \<turnstile> Val w : T'" by simp
    with h have "P,E,(h(a\<mapsto>(D,insert(Ds,fs(F \<mapsto> w))(S-{(Ds,fs)})))) \<turnstile> Val w : T'"
      by(cases w,auto split:split_if_asm)
    thus "type_conf P E T' (h(a\<mapsto>(D,insert(Ds,fs(F \<mapsto> w))(S-{(Ds,fs)})))) (Val w)"
      by(rule wt_same_type_typeconf)
  next
    case (casts_null C'')
    have T':"Class C'' = T'" .
    have "P,E,(h(a\<mapsto>(D,insert(Ds,fs(F \<mapsto> Null))(S-{(Ds,fs)})))) \<turnstile> null : NT"
      by simp
    with sym[OF T']
    show "type_conf P E T' (h(a\<mapsto>(D,insert(Ds,fs(F \<mapsto> Null))(S-{(Ds,fs)})))) null"
      by simp
  next
    case (casts_ref C'' Xs Xs' Ds'' a')
    have "Class C'' = T'" and "Ds'' = Xs @\<^sub>p Xs'"
      and "P \<turnstile> Path last Xs to C'' via Xs'"
      and "P,E,h \<turnstile> ref (a', Xs) : T''" .
    with wf have "P,E,h \<turnstile> ref (a',Ds'') : T'"
      by (auto intro!:appendPath_last[THEN sym] Subobjs_nonempty
        split:split_if_asm simp:path_via_def,
	drule_tac Cs="Xs" in Subobjs_appendPath,auto)
    with h have "P,E,(h(a\<mapsto>(D,insert(Ds,fs(F \<mapsto> Ref(a',Ds'')))(S-{(Ds,fs)})))) \<turnstile> 
      ref (a',Ds'') : T'"
      by auto
    thus "type_conf P E T' (h(a\<mapsto>(D,insert(Ds,fs(F \<mapsto> Ref(a',Ds'')))(S-{(Ds,fs)}))))
      (ref (a', Ds''))"
      by(rule wt_same_type_typeconf)
  qed
next
  case (RedFAssNull Cs E F h l)
  have sconf:"P,E \<turnstile> (h, l) \<surd>" .
  from wf have "is_class P NullPointer"
    by (fastsimp intro:is_class_xcpt wf_prog_wwf_prog)
  hence "preallocated h \<Longrightarrow> P \<turnstile> typeof\<^bsub>h\<^esub> (Ref (addr_of_sys_xcpt NullPointer,[NullPointer])) = Some(Class NullPointer)"
    by (auto elim: preallocatedE dest!:preallocatedD Subobjs_Base)
  with sconf have "P,E,h \<turnstile> THROW NullPointer : T" by(auto simp:sconf_def hconf_def)
  thus ?case by (fastsimp intro:wt_same_type_typeconf wf_prog_wwf_prog)
next
  case (CallObj E M e e' es h l h' l')
  have red: "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
   and IH: "\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk>
                 \<Longrightarrow> type_conf P E T' h' e'"
   and sconf: "P,E \<turnstile> (h,l) \<surd>" and wt: "P,E,h \<turnstile> e\<bullet>M(es) : T" .
  from wt have "P,E,h' \<turnstile> e'\<bullet>M(es) : T"
  proof(rule WTrt_elim_cases)
    fix C Cs Ts Ts' m
    assume wte:"P,E,h \<turnstile> e : Class C"
      and method:"P \<turnstile> C has least M = (Ts, T, m) via Cs"
      and wtes:"P,E,h \<turnstile> es [:] Ts'" and subs: "P \<turnstile> Ts' [\<le>] Ts"
    from IH[OF sconf wte] have "P,E,h' \<turnstile> e' : NT \<or> P,E,h' \<turnstile> e' : Class C" by auto
    thus ?thesis
    proof(rule disjE)
      assume wte':"P,E,h' \<turnstile> e' : NT"
      have "P,E,h' \<turnstile> es [:] Ts'"
	by(rule WTrts_hext_mono[OF wtes red_hext_incr[OF red]])
      with wte' show ?thesis by(rule WTrtCallNT)
    next
      assume wte':"P,E,h' \<turnstile> e' : Class C"
      have wtes':"P,E,h' \<turnstile> es [:] Ts'"
	by(rule WTrts_hext_mono[OF wtes red_hext_incr[OF red]])
      from wte' method wtes' subs show ?thesis by(rule WTrtCall)
    qed
  next
    fix Ts 
    assume wte:"P,E,h \<turnstile> e : NT" and wtes:"P,E,h \<turnstile> es [:] Ts"
    from IH[OF sconf wte] have wte':"P,E,h' \<turnstile> e' : NT" by simp
    have "P,E,h' \<turnstile> es [:] Ts"
      by(rule WTrts_hext_mono[OF wtes red_hext_incr[OF red]])
    with wte' show ?thesis by(rule WTrtCallNT)
  qed
  thus ?case by (rule wt_same_type_typeconf)
next
  case (CallParams E M es es' h l h' l' v)
  have reds: "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle>"
   and IH: "\<And>Ts. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> es [:] Ts\<rbrakk>
                 \<Longrightarrow> types_conf (P,E,Ts,h',es')"
   and sconf: "P,E \<turnstile> (h,l) \<surd>" and wt: "P,E,h \<turnstile> Val v\<bullet>M(es) : T" .
  from wt have "P,E,h' \<turnstile> Val v\<bullet>M(es') : T"
  proof (rule WTrt_elim_cases)
    fix C Cs Ts Ts' m
    assume wte: "P,E,h \<turnstile> Val v : Class C"
      and method:"P \<turnstile> C has least M = (Ts,T,m) via Cs"
      and wtes: "P,E,h \<turnstile> es [:] Ts'" and subs:"P \<turnstile> Ts' [\<le>] Ts"
    from wtes have "length es = length Ts'" by(rule WTrts_same_length)
    with reds have "length es' = length Ts'"
      by -(drule reds_length,simp)
    with IH[OF sconf wtes] subs obtain Ts'' where wtes':"P,E,h' \<turnstile> es' [:] Ts''"
      and subs':"P \<turnstile> Ts'' [\<le>] Ts" by(auto dest:types_conf_smaller_types)
    have wte':"P,E,h' \<turnstile> Val v : Class C"
      by(rule WTrt_hext_mono[OF wte reds_hext_incr[OF reds]])
    from wte' method wtes' subs' show ?thesis
      by(rule WTrtCall)
  next
    fix Ts
    assume wte:"P,E,h \<turnstile> Val v : NT" 
      and wtes:"P,E,h \<turnstile> es [:] Ts"
    from wtes have "length es = length Ts" by(rule WTrts_same_length)
    with reds have "length es' = length Ts"
      by -(drule reds_length,simp)
    with IH[OF sconf wtes] obtain Ts' where wtes':"P,E,h' \<turnstile> es' [:] Ts'"
      and "P \<turnstile> Ts' [\<le>] Ts" by(auto dest:types_conf_smaller_types)
    have wte':"P,E,h' \<turnstile> Val v : NT"
      by(rule WTrt_hext_mono[OF wte reds_hext_incr[OF reds]])
    from wte' wtes' show ?thesis by(rule WTrtCallNT)
  qed
  thus ?case by (rule wt_same_type_typeconf)
next
  case (RedCall C Cs Cs' Ds E M S T T' Ts Ts' a body body' new_body 
                pns pns' h l vs T'')
  have hp:"hp (h,l) a = Some(C,S)"
    and method:"P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds"
    and select:"P \<turnstile> (C,Cs@\<^sub>pDs) selects M = (Ts,T,pns,body) via Cs'"
    and length1:"length vs = length pns" and length2:"length Ts = length pns"
    and body_case:"new_body = 
   (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>blocks(this#pns,Class(last Cs')#Ts,Ref(a,Cs')#vs,body)
                   | _ \<Rightarrow> blocks(this#pns,Class(last Cs')#Ts,Ref(a,Cs')#vs,body))"
    and wt:"P,E,h \<turnstile> ref (a,Cs)\<bullet>M(map Val vs) : T''" .
  from wt hp method wf obtain Ts''
    where wtref:"P,E,h \<turnstile> ref (a,Cs) : Class (last Cs)" and eq:"T'' = T'"
    and wtes:"P,E,h \<turnstile> map Val vs [:] Ts''" and subs: "P \<turnstile> Ts'' [\<le>] Ts'"
    by(auto dest:wf_sees_method_fun split:split_if_asm)
  from wtref hp have subcls:"P \<turnstile> C \<preceq>\<^sup>* last Cs"
    by (auto intro:Subobjs_subclass split:split_if_asm)
  from method have has:"P \<turnstile> last Cs has M = (Ts',T',pns',body') via Ds"
    by(rule has_least_method_has_method)
  from select wf have "is_class P (last Cs')"
    by(induct rule:SelectMethodDef.induct,
       auto intro:Subobj_last_isClass simp:FinalOverriderMethodDef_def 
      OverriderMethodDefs_def MinimalMethodDefs_def LeastMethodDef_def MethodDefs_def)
  with select_method_wf_mdecl[OF wf select]
  have length_pns:"length (this#pns) = length (Class(last Cs')#Ts)" 
    and notNT:"T \<noteq> NT" and type:"\<forall>T\<in>set (Class(last Cs')#Ts). is_type P T"
    and wtabody:"P,[this\<mapsto>Class(last Cs'),pns[\<mapsto>]Ts] \<turnstile> body :: T"
    by(auto simp:wf_mdecl_def)
  from wtes hp select
  have map:"map (P \<turnstile> typeof\<^bsub>h\<^esub>) (Ref(a,Cs')#vs) = map Some (Class(last Cs')#Ts'')"
    by(auto elim:SelectMethodDef.elims split:split_if_asm 
            simp:FinalOverriderMethodDef_def OverriderMethodDefs_def 
                 MinimalMethodDefs_def LeastMethodDef_def MethodDefs_def)
  from select have "Ts' = Ts \<and> P \<turnstile> T \<le> T'"
  proof(rule SelectMethodDef.elims)
    fix X Xs Xs' M' mthd'
    assume "((C,Cs@\<^sub>pDs),M,(Ts,T,pns,body),Cs') = ((X,Xs),M',mthd',Xs')"
      and "P \<turnstile> X has least M' = mthd' via Xs'"
    hence dyn:"P \<turnstile> C has least M = (Ts,T,pns,body) via Cs'" by simp
    with subcls has wf show ?thesis
      by -(drule leq_method_subtypes,assumption,simp,blast)+
  next
    fix X Xs Xs' M' mthd'
    assume "((C,Cs@\<^sub>pDs),M,(Ts,T,pns,body),Cs') = ((X,Xs),M',mthd',Xs')"
      and "P \<turnstile> (X,Xs) has overrider M' = mthd' via Xs'"
    hence overrider:"P \<turnstile> (C,Cs@\<^sub>pDs) has overrider M = (Ts,T,pns,body) via Cs'" 
      by simp
    from method have notempty:"Ds \<noteq> []"
      by(auto intro!:Subobjs_nonempty simp:LeastMethodDef_def MethodDefs_def)
    from notempty have "last Cs = hd Ds \<Longrightarrow> last (Cs @ tl Ds) = last Ds"
    proof(cases "tl Ds = []")
      case True
      assume last:"last Cs = hd Ds" and notempty:"Ds \<noteq> []"
      with True have "Ds = [last Cs]" by (fastsimp dest:hd_Cons_tl)
      hence "last Ds = last Cs" by simp
      with True show ?thesis by simp
    next
      case False
      assume last:"last Cs = hd Ds" and notempty:"Ds \<noteq> []"
      from notempty False have "last (tl Ds) = last Ds"
	by -(drule hd_Cons_tl,drule_tac x="hd Ds" in last_ConsR,simp)
      with False show ?thesis by simp
    qed
    hence eq:"(Cs @\<^sub>p Ds) @\<^sub>p [last Ds] = (Cs @\<^sub>p Ds)"
      by(simp add:appendPath_def)
    from wtref hp have path:"P \<turnstile> Path C to (last Cs) via Cs"
      by (auto simp:path_via_def split:split_if_asm)
    from method wf
    have "P \<turnstile> last Ds has least M = (Ts',T',pns',body') via [last Ds]"
      by(auto dest:Subobj_last_isClass intro:Subobjs_Base subobjs_rel
	      simp:LeastMethodDef_def MethodDefs_def)
    with notempty
    have "P \<turnstile> last (Cs@\<^sub>pDs) has least M = (Ts',T',pns',body') via [last Ds]"
      by -(drule_tac Cs'="Cs" in appendPath_last,simp)
    with overrider wf eq have "(Cs',Ts,T,pns,body) \<in> MinimalMethodDefs P C M"
      and "P,C \<turnstile> Cs' \<sqsubseteq> Cs @\<^sub>p Ds"
      by -(auto simp:FinalOverriderMethodDef_def OverriderMethodDefs_def,
           drule wf_sees_method_fun,auto)
    with subcls wf path notempty has show ?thesis
      by -(drule leq_methods_subtypes,simp_all,blast)+
  qed
  hence eqs:"Ts' = Ts" and sub:"P \<turnstile> T \<le> T'" by auto
  from wf wtabody have "P,empty(this\<mapsto>Class(last Cs'),pns[\<mapsto>]Ts),h \<turnstile> body : T"
    by -(rule WT_implies_WTrt,simp_all)
  hence wtbody:"P,E(this#pns [\<mapsto>] Class (last Cs')#Ts),h \<turnstile> body : T"
    by(rule WTrt_env_mono) simp
  from wtes have "length vs = length Ts''"
    by (fastsimp dest:WTrts_same_length)
  with eqs subs
  have length_vs:"length (Ref(a,Cs')#vs) = length (Class(last Cs')#Ts)"
    by (simp add:list_all2_def)
  from subs eqs have "P \<turnstile> (Class(last Cs')#Ts'') [\<le>] (Class(last Cs')#Ts)"
    by (simp add:fun_of_def)
  with wt_blocks[OF length_pns length_vs type] wtbody map eq
  have blocks:"P,E,h \<turnstile> blocks(this#pns,Class(last Cs')#Ts,Ref(a,Cs')#vs,body) : T"
    by auto
  have "P,E,h \<turnstile> new_body : T'"
  proof(cases "\<forall>C. T' \<noteq> Class C")
    case True
    with sub notNT have "T = T'" by (cases T') auto
    with blocks True body_case show ?thesis by(cases T') auto
  next
    case False
    then obtain D where T':"T' = Class D" by auto
    with method sub wf have class:"is_class P D"
      by (auto elim!:widen.elims dest:least_method_is_type 
               intro:Subobj_last_isClass simp:path_unique_def)
    with blocks T' body_case class sub show ?thesis
      by(cases T',auto,cases T,auto)
  qed
  with eq show ?case by(fastsimp intro:wt_same_type_typeconf)
next
  case (RedCallNull E M h l)
  have sconf:"P,E \<turnstile> (h, l) \<surd>" .
  from wf have "is_class P NullPointer" 
    by (fastsimp intro:is_class_xcpt wf_prog_wwf_prog)
  hence "preallocated h \<Longrightarrow> P \<turnstile> typeof\<^bsub>h\<^esub> (Ref (addr_of_sys_xcpt NullPointer,[NullPointer])) = Some(Class NullPointer)"
    by (auto elim: preallocatedE dest!:preallocatedD Subobjs_Base)
  with sconf have "P,E,h \<turnstile> THROW NullPointer : T" by(auto simp:sconf_def hconf_def)
  thus ?case by (fastsimp intro:wt_same_type_typeconf)
next
  case (BlockRedNone E T V e e' h h' l l' T')
  have IH:"\<And>T'. \<lbrakk>P,E(V \<mapsto> T) \<turnstile> (h, l(V := None)) \<surd>; P,E(V \<mapsto> T),h \<turnstile> e : T'\<rbrakk>
    \<Longrightarrow> type_conf P (E(V \<mapsto> T)) T' h' e'"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> {V:T; e} : T'" .
  from wt have type:"is_type P T" and wte:"P,E(V\<mapsto>T),h \<turnstile> e : T'" by auto
  from sconf type have "P,E(V \<mapsto> T) \<turnstile> (h, l(V := None)) \<surd>"
    by (auto simp:sconf_def lconf_def envconf_def)
  from IH[OF this wte] type show ?case by (cases T') auto
next
  case (BlockRedSome E T V e e' h h' l l' v T')
  have red:"P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and IH:"\<And>T'. \<lbrakk>P,E(V \<mapsto> T) \<turnstile> (h, l(V := None)) \<surd>; P,E(V \<mapsto> T),h \<turnstile> e : T'\<rbrakk>
                  \<Longrightarrow> type_conf P (E(V \<mapsto> T)) T' h' e'"
    and Some:"l' V = Some v"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> {V:T; e} : T'" .
  from wt have wte:"P,E(V\<mapsto>T),h \<turnstile> e : T'"  and type:"is_type P T" by auto
  with sconf wf red type have "P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V \<mapsto> T)"
    by -(auto simp:sconf_def,rule red_preserves_lconf,
         auto intro:wf_prog_wwf_prog simp:envconf_def lconf_def)
  hence conf:"P,h' \<turnstile> v :\<le> T" using Some 
    by(auto simp:lconf_def,erule_tac x="V" in allE,clarsimp)
  have wtval:"P,E(V \<mapsto> T),h' \<turnstile> V:=Val v : T"
  proof(cases T)
    case Void with conf show ?thesis by auto
  next
    case Boolean with conf show ?thesis by auto
  next
    case Integer with conf show ?thesis by auto
  next
    case NT with conf show ?thesis by auto
  next
    case (Class C)
    with conf have "P,E(V \<mapsto> T),h' \<turnstile> Val v : T \<or> P,E(V \<mapsto> T),h' \<turnstile> Val v : NT"
      by auto
    with Class show ?thesis by auto
  qed
  from sconf type have "P,E(V \<mapsto> T) \<turnstile> (h, l(V := None)) \<surd>"
    by (auto simp:sconf_def lconf_def envconf_def)
  from IH[OF this wte] wtval type show ?case by(cases T') auto
next
  case (InitBlockRed E T V e e' h h' l l' v v' v'' T')
  have red:"P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l(V \<mapsto> v'))\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and IH:"\<And>T'. \<lbrakk>P,E(V \<mapsto> T) \<turnstile> (h, l(V \<mapsto> v')) \<surd>; P,E(V \<mapsto> T),h \<turnstile> e : T'\<rbrakk>
              \<Longrightarrow> type_conf P (E(V \<mapsto> T)) T' h' e'"
    and Some:"l' V = Some v''" and casts:"P \<turnstile> T casts v to v'"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> {V:T := Val v; e} : T'" .
  from wt have wte:"P,E(V \<mapsto> T),h \<turnstile> e : T'" and wtval:"P,E(V \<mapsto> T),h \<turnstile> V:=Val v : T"
    and type:"is_type P T"
    by auto
  from wf casts wtval have "P,h \<turnstile> v' :\<le> T"
    by(fastsimp intro!:casts_conf wf_prog_wwf_prog)
  with sconf have lconf:"P,h \<turnstile> l(V \<mapsto> v') (:\<le>)\<^sub>w E(V \<mapsto> T)"
    by (fastsimp intro!:lconf_upd2 simp:sconf_def)
  from sconf type have "envconf P (E(V \<mapsto> T))" by(simp add:sconf_def envconf_def)
  from red_preserves_lconf[OF wf_prog_wwf_prog[OF wf] red wte lconf this]
  have "P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V \<mapsto> T)" .
  with Some have "P,h' \<turnstile> v'' :\<le> T"
    by(simp add:lconf_def,erule_tac x="V" in allE,auto)
  hence wtval':"P,E(V \<mapsto> T),h' \<turnstile> V:=Val v'' : T"
    by(cases T) auto
  from lconf sconf type have "P,E(V \<mapsto> T) \<turnstile> (h, l(V \<mapsto> v')) \<surd>"
    by(auto simp:sconf_def envconf_def)
  from IH[OF this wte] wtval' type show ?case by(cases T') auto
next
  case RedBlock thus ?case by (fastsimp intro:wt_same_type_typeconf)
next
  case RedInitBlock thus ?case by (fastsimp intro:wt_same_type_typeconf)
next
  case (SeqRed E e e' e\<^isub>2 h l h' l' T)
  have red:"P,E \<turnstile> \<langle>e,(h, l)\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h, l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> \<Longrightarrow> type_conf P E T' h' e'"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> e;; e\<^isub>2 : T" .
  from wt obtain T' where wte:"P,E,h \<turnstile> e : T'" and wte2:"P,E,h \<turnstile> e\<^isub>2 : T" by auto
  from WTrt_hext_mono[OF wte2 red_hext_incr[OF red]] have wte2':"P,E,h' \<turnstile> e\<^isub>2 : T" .
  from IH[OF sconf wte] obtain T'' where "P,E,h' \<turnstile> e' : T''" by(cases T') auto
  with wte2' have "P,E,h' \<turnstile> e';; e\<^isub>2 : T" by auto
  thus ?case by(rule wt_same_type_typeconf)
next
  case RedSeq thus ?case by (fastsimp intro:wt_same_type_typeconf)
next
  case (CondRed E e e' e\<^isub>1 e\<^isub>2 h l h' l')
  have red:"P,E \<turnstile> \<langle>e,(h, l)\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and IH: "\<And>T. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T\<rbrakk>
                     \<Longrightarrow> type_conf P E T h' e'"
    and wt:"P,E,h \<turnstile> if (e) e\<^isub>1 else e\<^isub>2 : T"
    and sconf:"P,E \<turnstile> (h,l) \<surd>" .
  from wt have wte:"P,E,h \<turnstile> e : Boolean"
      and wte1:"P,E,h \<turnstile> e\<^isub>1 : T" and wte2:"P,E,h \<turnstile> e\<^isub>2 : T" by auto
  from IH[OF sconf wte] have wte':"P,E,h' \<turnstile> e' : Boolean" by auto
  from wte' WTrt_hext_mono[OF wte1 red_hext_incr[OF red]]
    WTrt_hext_mono[OF wte2 red_hext_incr[OF red]]
  have "P,E,h' \<turnstile> if (e') e\<^isub>1 else e\<^isub>2 : T"
    by (rule WTrtCond)
  thus ?case by(rule wt_same_type_typeconf)
next
  case RedCondT thus ?case by (fastsimp intro: wt_same_type_typeconf)
next
  case RedCondF thus ?case by (fastsimp intro: wt_same_type_typeconf)
next
  case RedWhile thus ?case by (fastsimp intro: wt_same_type_typeconf)
next
  case (ThrowRed E e e' h l h' l' T)
  have IH:"\<And>T. \<lbrakk>P,E \<turnstile> (h, l) \<surd>; P,E,h \<turnstile> e : T\<rbrakk> \<Longrightarrow> type_conf P E T h' e'"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> throw e : T" .
  from wt obtain T' where wte:"P,E,h \<turnstile> e : T'" and ref:"is_refT T'"
    by auto
  from ref have "P,E,h' \<turnstile> throw e' : T"
  proof(rule refTE)
    assume T':"T' = NT"
    with wte have "P,E,h \<turnstile> e : NT" by simp
    from IH[OF sconf this] ref T' show ?thesis by auto
    
  next
    fix C assume T':"T' = Class C"
    with wte have "P,E,h \<turnstile> e : Class C" by simp
    from IH[OF sconf this] have "P,E,h' \<turnstile> e' : Class C \<or> P,E,h' \<turnstile> e' : NT"
      by simp
    thus ?thesis
    proof(rule disjE)
      assume wte':"P,E,h' \<turnstile> e' : Class C"
      have "is_refT (Class C)" by simp
      with wte' show ?thesis by auto
    next
      assume wte':"P,E,h' \<turnstile> e' : NT"
      have "is_refT NT" by simp
      with wte' show ?thesis by auto
    qed
  qed
  thus ?case by (rule wt_same_type_typeconf)
next
  case (RedThrowNull E h l)
  have sconf:"P,E \<turnstile> (h, l) \<surd>" .
  from wf have "is_class P NullPointer"
    by (fastsimp intro:is_class_xcpt wf_prog_wwf_prog)
  hence "preallocated h \<Longrightarrow> P \<turnstile> typeof\<^bsub>h\<^esub> (Ref (addr_of_sys_xcpt NullPointer,[NullPointer])) = Some(Class NullPointer)"
    by (auto elim: preallocatedE dest!:preallocatedD Subobjs_Base)
  with sconf have "P,E,h \<turnstile> THROW NullPointer : T" by(auto simp:sconf_def hconf_def)
  thus ?case by (fastsimp intro:wt_same_type_typeconf wf_prog_wwf_prog)
next
  case (ListRed1 E e e' es h l h' l' Ts)
  have red:"P,E \<turnstile> \<langle>e,(h, l)\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and IH:"\<And>T. \<lbrakk>P,E \<turnstile> (h, l) \<surd>; P,E,h \<turnstile> e : T\<rbrakk> \<Longrightarrow> type_conf P E T h' e'"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> e # es [:] Ts" .
  from wt obtain U Us where Ts:"Ts = U#Us" by(cases Ts) auto
  with wt have wte:"P,E,h \<turnstile> e : U" and wtes:"P,E,h \<turnstile> es [:] Us" by simp_all
  from WTrts_hext_mono[OF wtes red_hext_incr[OF red]] 
  have wtes':"P,E,h' \<turnstile> es [:] Us" .
  hence "length es = length Us" by (rule WTrts_same_length)
  with wtes' have "types_conf(P,E,Us,h',es)"
    by (fastsimp intro:wts_same_types_typesconf)
  with IH[OF sconf wte] Ts show ?case by simp
next
  case (ListRed2 E es es' h l h' l' v Ts)
  have reds:"P,E \<turnstile> \<langle>es,(h, l)\<rangle> [\<rightarrow>] \<langle>es',(h', l')\<rangle>"
    and IH:"\<And>Ts. \<lbrakk>P,E \<turnstile> (h, l) \<surd>; P,E,h \<turnstile> es [:] Ts\<rbrakk> \<Longrightarrow> types_conf (P,E,Ts,h',es')"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> Val v#es [:] Ts" .
  from wt obtain U Us where Ts:"Ts = U#Us" by(cases Ts) auto
  with wt have wtval:"P,E,h \<turnstile> Val v : U" and wtes:"P,E,h \<turnstile> es [:] Us" by simp_all
  from WTrt_hext_mono[OF wtval reds_hext_incr[OF reds]]
  have "P,E,h' \<turnstile> Val v : U" .
  hence "type_conf P E U h' (Val v)" by(rule wt_same_type_typeconf)
  with IH[OF sconf wtes] Ts show ?case by simp
qed (fastsimp intro:wt_same_type_typeconf)+



corollary subject_reduction:
  "\<lbrakk> wf_C_prog P; P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>; P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e:T \<rbrakk>
  \<Longrightarrow> type_conf P E T (hp s') e'"
by(cases s, cases s', fastsimp dest:subject_reduction2)

corollary subjects_reduction:
  "\<lbrakk> wf_C_prog P; P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>; P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> es[:]Ts \<rbrakk>
  \<Longrightarrow> types_conf(P,E,Ts,hp s',es')"
by(cases s, cases s', fastsimp dest:subjects_reduction2)


subsection {* Lifting to @{text"\<rightarrow>*"} *}

text{* Now all these preservation lemmas are first lifted to the transitive
closure \dots *}

lemma step_preserves_sconf:
assumes wf: "wf_C_prog P" and step: "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
shows "\<And>T. \<lbrakk> P,E,hp s \<turnstile> e : T; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"

using step
proof (induct rule:converse_rtrancl_induct2)
  case refl show ?case .
next
  case step
  thus ?case using wf
    by simp(frule subject_reduction[OF wf],assumption,assumption,cases T,
            auto dest:red_preserves_sconf intro:wf_prog_wwf_prog)
qed



lemma step_preserves_defass:
assumes wf: "wf_C_prog P" and step: "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
shows "\<D> e \<lfloor>dom(lcl s)\<rfloor> \<Longrightarrow> \<D> e' \<lfloor>dom(lcl s')\<rfloor>"

using step
proof (induct rule:converse_rtrancl_induct2)
  case refl thus ?case .
next
  case (step e s e' s') thus ?case
    by(cases s,cases s')(auto dest:red_preserves_defass[OF wf])
qed



lemma step_preserves_type:
assumes wf: "wf_C_prog P" and step: "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
shows "\<And>T. \<lbrakk> P,E \<turnstile> s\<surd>; P,E,hp s \<turnstile> e:T \<rbrakk>
    \<Longrightarrow> type_conf P E T (hp s') e'"

using step
proof (induct rule:converse_rtrancl_induct2)
  case refl thus ?case by -(rule wt_same_type_typeconf)
next
  case step thus ?case using wf
    apply simp
    apply (frule subject_reduction[OF wf])
    apply (auto dest!:red_preserves_sconf intro:wf_prog_wwf_prog)
    apply(cases T) apply fastsimp+
    done
qed



subsection {* Lifting to @{text"\<Rightarrow>"} *}

text{* \dots and now to the big step semantics, just for fun. *}

lemma eval_preserves_sconf:
  "\<lbrakk> wf_C_prog P; P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>; P,E \<turnstile> e::T; P,E \<turnstile> s\<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s'\<surd>"

by(blast intro:step_preserves_sconf big_by_small WT_implies_WTrt wf_prog_wwf_prog)



lemma eval_preserves_type: assumes wf: "wf_C_prog P"
shows "\<lbrakk> P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>; P,E \<turnstile> s\<surd>; P,E \<turnstile> e::T \<rbrakk>
   \<Longrightarrow> type_conf P E T (hp s') e'"

  using wf
  by (auto dest!:big_by_small[OF wf_prog_wwf_prog[OF wf]] WT_implies_WTrt 
           intro:wf_prog_wwf_prog
           dest!:step_preserves_type[OF wf])



subsection "The final polish"

text{* The above preservation lemmas are now combined and packed nicely. *}

constdefs
  wf_config :: "prog \<Rightarrow> env \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"   ("_,_,_ \<turnstile> _ : _ \<surd>"   [51,0,0,0,0]50)
  "P,E,s \<turnstile> e:T \<surd>  \<equiv>  P,E \<turnstile> s \<surd> \<and> P,E,hp s \<turnstile> e:T"

theorem Subject_reduction: assumes wf: "wf_C_prog P"
shows "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P,E,s \<turnstile> e : T \<surd>
       \<Longrightarrow> type_conf P E T (hp s') e'"

  using wf
  by (force elim!:red_preserves_sconf intro:wf_prog_wwf_prog 
            dest:subject_reduction[OF wf] simp:wf_config_def)



theorem Subject_reductions:
assumes wf: "wf_C_prog P" and reds: "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
shows "\<And>T. P,E,s \<turnstile> e:T \<surd> \<Longrightarrow> type_conf P E T (hp s') e'"

using reds
proof (induct rule:converse_rtrancl_induct2)
  case refl thus ?case
    by (fastsimp intro:wt_same_type_typeconf simp:wf_config_def)
next
  case (step e s e'' s'' T)
  have Red:"((e, s), e'', s'') \<in> Red P E"
    and IH:"\<And>T. P,E,s'' \<turnstile> e'' : T \<surd> \<Longrightarrow> type_conf P E T (hp s') e'"
    and wte:"P,E,s \<turnstile> e : T \<surd>" .
  from Red have red:"P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e'',s''\<rangle>" by simp
  from red_preserves_sconf[OF red] wte wf have sconf:"P,E \<turnstile> s'' \<surd>"
    by(fastsimp dest:wf_prog_wwf_prog simp:wf_config_def)
  from wf red wte have type_conf:"type_conf P E T (hp s'') e''" 
    by(rule Subject_reduction)
  show ?case
  proof(cases T)
    case Void
    with type_conf have "P,E,hp s'' \<turnstile> e'' : T" by simp
    with sconf have "P,E,s'' \<turnstile> e'' : T \<surd>" by(simp add:wf_config_def)
    from IH[OF this] show ?thesis .
  next
    case Boolean
    with type_conf have "P,E,hp s'' \<turnstile> e'' : T" by simp
    with sconf have "P,E,s'' \<turnstile> e'' : T \<surd>" by(simp add:wf_config_def)
    from IH[OF this] show ?thesis .
  next
    case Integer
    with type_conf have "P,E,hp s'' \<turnstile> e'' : T" by simp
    with sconf have "P,E,s'' \<turnstile> e'' : T \<surd>" by(simp add:wf_config_def)
    from IH[OF this] show ?thesis .
  next
    case NT
    with type_conf have "P,E,hp s'' \<turnstile> e'' : T" by simp
    with sconf have "P,E,s'' \<turnstile> e'' : T \<surd>" by(simp add:wf_config_def)
    from IH[OF this] show ?thesis .
  next
    case (Class C)
    with type_conf have "P,E,hp s'' \<turnstile> e'' : T \<or> P,E,hp s'' \<turnstile> e'' : NT" by simp
    thus ?thesis
    proof(rule disjE)
      assume "P,E,hp s'' \<turnstile> e'' : T"
      with sconf have "P,E,s'' \<turnstile> e'' : T \<surd>" by(simp add:wf_config_def)
      from IH[OF this] show ?thesis .
    next
      assume "P,E,hp s'' \<turnstile> e'' : NT"
      with sconf have "P,E,s'' \<turnstile> e'' : NT \<surd>" by(simp add:wf_config_def)
      from IH[OF this] have "P,E,hp s' \<turnstile> e' : NT" by simp
      with Class show ?thesis by simp
    qed
  qed
qed



corollary Progress: assumes wf: "wf_C_prog P"
shows "\<lbrakk> P,E,s  \<turnstile> e : T \<surd>; \<D> e \<lfloor>dom(lcl s)\<rfloor>; \<not> final e \<rbrakk> \<Longrightarrow> \<exists>e' s'. P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"

using progress[OF wf_prog_wwf_prog[OF wf]]
by(auto simp:wf_config_def sconf_def)



corollary TypeSafety:
assumes wf:"wf_C_prog P" and sconf:"P,E \<turnstile> s \<surd>" and wte:"P,E \<turnstile> e :: T"
  and D:"\<D> e \<lfloor>dom(lcl s)\<rfloor>" and step:"P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
  and nored:"\<not>(\<exists>e'' s''. P,E \<turnstile> \<langle>e',s'\<rangle> \<rightarrow> \<langle>e'',s''\<rangle>)"
shows "(\<exists>v. e' = Val v \<and> P,hp s' \<turnstile> v :\<le> T) \<or>
      (\<exists>r. e' = Throw r \<and> the_addr (Ref r) \<in> dom(hp s'))"
proof -
  from sconf wte wf have wf_config:"P,E,s \<turnstile> e : T \<surd>"
    by(fastsimp intro:WT_implies_WTrt simp:wf_config_def)
  with wf step have type_conf:"type_conf P E T (hp s') e'"
    by(rule Subject_reductions)
  from step_preserves_sconf[OF wf step wte[THEN WT_implies_WTrt] sconf] wf
  have sconf':"P,E \<turnstile> s' \<surd>" by simp
  from wf step D have D':"\<D> e' \<lfloor>dom(lcl s')\<rfloor>" by(rule step_preserves_defass)
  show ?thesis
  proof(cases T)
    case Void 
    with type_conf have wte':"P,E,hp s' \<turnstile> e' : T" by simp
    with sconf' have wf_config':"P,E,s' \<turnstile> e' : T \<surd>" by(simp add:wf_config_def)
    { assume "\<not> final e'"
      from Progress[OF wf wf_config' D' this] nored have False
	by simp }
    hence "final e'" by fast
    with wte' show ?thesis by(auto simp:final_def)
  next
    case Boolean
    with type_conf have wte':"P,E,hp s' \<turnstile> e' : T" by simp
    with sconf' have wf_config':"P,E,s' \<turnstile> e' : T \<surd>" by(simp add:wf_config_def)
    { assume "\<not> final e'"
      from Progress[OF wf wf_config' D' this] nored have False
	by simp }
    hence "final e'" by fast
    with wte' show ?thesis by(auto simp:final_def)
  next
    case Integer
    with type_conf have wte':"P,E,hp s' \<turnstile> e' : T" by simp
    with sconf' have wf_config':"P,E,s' \<turnstile> e' : T \<surd>" by(simp add:wf_config_def)
    { assume "\<not> final e'"
      from Progress[OF wf wf_config' D' this] nored have False
	by simp }
    hence "final e'" by fast
    with wte' show ?thesis by(auto simp:final_def)
  next
    case NT
    with type_conf have wte':"P,E,hp s' \<turnstile> e' : T" by simp
    with sconf' have wf_config':"P,E,s' \<turnstile> e' : T \<surd>" by(simp add:wf_config_def)
    { assume "\<not> final e'"
      from Progress[OF wf wf_config' D' this] nored have False
	by simp }
    hence "final e'" by fast
    with wte' show ?thesis by(auto simp:final_def)
  next
    case (Class C)
    with type_conf have wte':"P,E,hp s' \<turnstile> e' : T \<or> P,E,hp s' \<turnstile> e' : NT" by simp
    thus ?thesis
    proof(rule disjE)
      assume wte':"P,E,hp s' \<turnstile> e' : T"
      with sconf' have wf_config':"P,E,s' \<turnstile> e' : T \<surd>" by(simp add:wf_config_def)
      { assume "\<not> final e'"
	from Progress[OF wf wf_config' D' this] nored have False
	  by simp }
      hence "final e'" by fast
      with wte' show ?thesis by(auto simp:final_def)
    next
      assume wte':"P,E,hp s' \<turnstile> e' : NT"
      with sconf' have wf_config':"P,E,s' \<turnstile> e' : NT \<surd>" by(simp add:wf_config_def)
      { assume "\<not> final e'"
	from Progress[OF wf wf_config' D' this] nored have False
	  by simp }
      hence "final e'" by fast
      with wte' Class show ?thesis by(auto simp:final_def)
    qed
  qed
qed



end
