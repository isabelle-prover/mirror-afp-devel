(*  Title:      Jinja/J/SmallProgress.thy
    ID:         $Id: Progress.thy,v 1.6 2008-06-12 06:57:22 lsf37 Exp $
    Author:     Tobias Nipkow, Andreas Lochbihler
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* \isaheader{Progress of Small Step Semantics} *}
theory Progress
imports WellTypeRT DefAss SmallStep "../Common/Conform" WWellForm
begin


lemma final_addrE:
  "\<lbrakk> P,E,h \<turnstile> e : Class C; final e;
    \<And>a. e = addr a \<Longrightarrow> R;
    \<And>a. e = Throw a \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
by(auto elim!: final.cases)

lemma finalRefE:
 "\<lbrakk> P,E,h \<turnstile> e : T; is_refT T; final e;
   e = null \<Longrightarrow> R;
   \<And>a C. \<lbrakk> e = addr a; T = Class C \<rbrakk> \<Longrightarrow> R;
   \<And>a U. \<lbrakk> e = addr a; T = U\<lfloor>\<rceil> \<rbrakk> \<Longrightarrow> R;
   \<And>a. e = Throw a \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
by(auto simp:final_iff elim!: refTE)


inductive WTrt' :: "J_prog \<Rightarrow> heap \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"
  for P :: "J_prog" and h :: "heap" where
  "is_class P C  \<Longrightarrow> WTrt' P h E (new C) (Class C)"

| "\<lbrakk> WTrt' P h E e Integer; is_type P T \<rbrakk> \<Longrightarrow> WTrt' P h E (newA T\<lfloor>e\<rceil>) (T\<lfloor>\<rceil>)"

| "WTrt' P h E e  T \<Longrightarrow> WTrt' P h E (Cast U e) U"

| "typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow> WTrt' P h E (Val v) T"

| "E V = Some T  \<Longrightarrow> WTrt' P h E (Var V) T"

| "\<lbrakk> WTrt' P h E e1 T1; WTrt' P h E e2 T2 \<rbrakk> \<Longrightarrow> WTrt' P h E (e1 \<guillemotleft>Eq\<guillemotright> e2) Boolean"

| "\<lbrakk> WTrt' P h E e1 Integer; WTrt' P h E e2 Integer \<rbrakk> \<Longrightarrow> WTrt' P h E (e1 \<guillemotleft>Add\<guillemotright> e2) Integer"

| "\<lbrakk> WTrt' P h E (Var V) T; WTrt' P h E e T'; P \<turnstile> T' \<le> T \<rbrakk> \<Longrightarrow> WTrt' P h E (V:=e) Void"

| "\<lbrakk> WTrt' P h E a (T\<lfloor>\<rceil>); WTrt' P h E i Integer \<rbrakk> \<Longrightarrow> WTrt' P h E (a\<lfloor>i\<rceil>) T"

| "\<lbrakk> WTrt' P h E a NT; WTrt' P h E i Integer \<rbrakk> \<Longrightarrow> WTrt' P h E (a\<lfloor>i\<rceil>) T"

| "\<lbrakk> WTrt' P h E a (T\<lfloor>\<rceil>); WTrt' P h E i Integer; WTrt' P h E e T' \<rbrakk> \<Longrightarrow> WTrt' P h E (a\<lfloor>i\<rceil> := e) Void"

| "\<lbrakk> WTrt' P h E a NT; WTrt' P h E i Integer; WTrt' P h E e T' \<rbrakk> \<Longrightarrow> WTrt' P h E (a\<lfloor>i\<rceil> := e) Void"

| "\<lbrakk> WTrt' P h E e (Class C); P \<turnstile> C has F:T in D \<rbrakk> \<Longrightarrow> WTrt' P h E (e\<bullet>F{D}) T"

| "WTrt' P h E e NT \<Longrightarrow> WTrt' P h E (e\<bullet>F{D}) T"

| "\<lbrakk> WTrt' P h E e1 (Class C); P \<turnstile> C has F:T in D; WTrt' P h E e2 T2; P \<turnstile> T2 \<le> T \<rbrakk> \<Longrightarrow> WTrt' P h E (e1\<bullet>F{D}:=e2) Void"

| "\<lbrakk> WTrt' P h E e1 NT; WTrt' P h E e2 T2 \<rbrakk> \<Longrightarrow> WTrt' P h E (e1\<bullet>F{D}:=e2) Void"

| "\<lbrakk> WTrt' P h E e (Class C); P \<turnstile> C sees M:Ts \<rightarrow> T = (pns,body) in D; list_all2 (WTrt' P h E) es Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk> \<Longrightarrow> WTrt' P h E (e\<bullet>M(es)) T"

| "\<lbrakk> WTrt' P h E e NT; list_all2 (WTrt' P h E) es Ts \<rbrakk> \<Longrightarrow> WTrt' P h E (e\<bullet>M(es)) T"

| "\<lbrakk> WTrt' P h E e (Class C); P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk> \<Longrightarrow> WTrt' P h E (e\<bullet>start([])) Void"

| "\<lbrakk> WTrt' P h E e T; is_refT T; T \<noteq> NT \<rbrakk> \<Longrightarrow> WTrt' P h E (e\<bullet>wait([])) Void"

| "\<lbrakk> WTrt' P h E e T; is_refT T; T \<noteq> NT \<rbrakk> \<Longrightarrow> WTrt' P h E (e\<bullet>notify([])) Void"

| "\<lbrakk> WTrt' P h E e T; is_refT T; T \<noteq> NT \<rbrakk> \<Longrightarrow> WTrt' P h E (e\<bullet>notifyAll([])) Void"

| "\<lbrakk> WTrt' P h E e (Class C); P \<turnstile> C \<preceq>\<^sup>* Thread \<rbrakk> \<Longrightarrow> WTrt' P h E (e\<bullet>join([])) Void"

| "\<lbrakk> typeof\<^bsub>h\<^esub> v = Some T1; P \<turnstile> T1 \<le> T; WTrt' P h (E(V\<mapsto>T)) e2 T2 \<rbrakk> \<Longrightarrow> WTrt' P h E {V:T := Val v; e2} T2"

| "\<lbrakk> WTrt' P h (E(V\<mapsto>T)) e T'; \<not> assigned V e \<rbrakk> \<Longrightarrow> WTrt' P h E {V:T; e} T'"

| "\<lbrakk> WTrt' P h E o' T; is_refT T; T \<noteq> NT; WTrt' P h E e T' \<rbrakk> \<Longrightarrow> WTrt' P h E (sync(o') e) T'"

| "\<lbrakk> WTrt' P h E o' NT; WTrt' P h E e T \<rbrakk> \<Longrightarrow> WTrt' P h E (sync(o') e) T'"

| "\<lbrakk> WTrt' P h E (addr a) T; WTrt' P h E e T' \<rbrakk> \<Longrightarrow> WTrt' P h E (insync(a) e) T'"

| "\<lbrakk> WTrt' P h E e1 T1; WTrt' P h E e2 T2 \<rbrakk> \<Longrightarrow> WTrt' P h E (e1;;e2) T2"

| "\<lbrakk> WTrt' P h E e Boolean; WTrt' P h E e1 T1; WTrt' P h E e2 T2; 
       P \<turnstile> T1 \<le> T2 \<or> P \<turnstile> T2 \<le> T1; P \<turnstile> T1 \<le> T2 \<longrightarrow> T = T2; P \<turnstile> T2 \<le> T1 \<Longrightarrow> T = T1 \<rbrakk>
    \<Longrightarrow> WTrt' P h E (if (e) e1 else e2) T"

| "\<lbrakk> WTrt' P h E e Boolean; WTrt' P h E c T \<rbrakk> \<Longrightarrow> WTrt' P h E (while(e) c) Void"

| "\<lbrakk> WTrt' P h E e T; is_refT_class T; T \<noteq> Class Object \<rbrakk> \<Longrightarrow> WTrt' P h E (throw e) T'"

| "\<lbrakk> WTrt' P h E e1 T1; WTrt' P h (E(V \<mapsto> Class C)) e2 T2; P \<turnstile> T1 \<le> T2 \<rbrakk> \<Longrightarrow> WTrt' P h E (try e1 catch(C V) e2) T2"
monos WTrtCall_mono

abbreviation
  WTrt_syntax :: "J_prog \<Rightarrow> env \<Rightarrow> heap \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" ("_,_,_ \<turnstile> _ :' _"   [51,51,51]50)
where
  "P,E,h \<turnstile> e :' T \<equiv> WTrt' P h E e T"

inductive_cases WTrt'_elim_cases[elim!]:
  "P,E,h \<turnstile> V :=e :' T"

lemma [iff]: "P,E,h \<turnstile> e\<^isub>1;;e\<^isub>2 :' T\<^isub>2 = (\<exists>T\<^isub>1. P,E,h \<turnstile> e\<^isub>1:' T\<^isub>1 \<and> P,E,h \<turnstile> e\<^isub>2:' T\<^isub>2)"
apply(rule iffI)
apply (auto elim: WTrt'.cases intro!:WTrt'.intros)
done

lemma [iff]: "P,E,h \<turnstile> Val v :' T = (typeof\<^bsub>h\<^esub> v = Some T)"
apply(rule iffI)
apply (auto elim: WTrt'.cases intro!:WTrt'.intros)
done

lemma [iff]: "P,E,h \<turnstile> Var v :' T = (E v = Some T)"
apply(rule iffI)
apply (auto elim: WTrt'.cases intro!:WTrt'.intros)
done


lemma wt_wt': "P,E,h \<turnstile> e : T \<Longrightarrow> P,E,h \<turnstile> e :' T"
apply (induct rule:WTrt.induct)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(erule WTrt'.intros)
  apply(assumption)
 apply(erule list_all2_mono)
 apply(blast)
apply(assumption)
apply(erule WTrt'.intros)
apply(erule list_all2_mono)
apply(blast)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(blast intro:WTrt'.intros)
apply(case_tac "assigned V e")
apply(clarsimp simp add:fun_upd_same assigned_def simp del:fun_upd_apply)
apply(erule (2) WTrt'.intros)
apply(erule (1) WTrt'.intros)
apply(blast intro:WTrt'.intros)+
done



lemma wt'_wt: "P,E,h \<turnstile> e :' T \<Longrightarrow> P,E,h \<turnstile> e : T"
apply (induct rule:WTrt'.induct)
apply(blast intro:WTrt.intros)+
apply(rule WTrtAAcc)
 apply(simp)
apply(simp)
apply(blast intro:WTrt.intros)
apply(rule WTrtAAss)
  apply(simp)
 apply(simp)
apply(simp)
apply(blast intro:WTrt.intros)
apply(blast intro:WTrt.intros)
apply(blast intro:WTrt.intros)
apply(blast intro:WTrt.intros)
apply(blast intro:WTrt.intros)
apply(erule WTrt.intros)
  apply(assumption)
 apply(erule list_all2_mono)
 apply(blast)
apply(assumption)
apply(erule WTrt.intros)
apply(erule list_all2_mono)
apply(blast)
apply(erule WTrtNewThread, assumption)
apply(erule WTrtWait, assumption, assumption)
apply(erule WTrtNotify, assumption, assumption)
apply(erule WTrtNotifyAll, assumption, assumption)
apply(erule WTrtJoin, assumption)
apply(rule WTrt.intros)
apply(rule WTrt.intros)
apply(rule WTrt.intros)
apply simp
apply(simp)
apply(assumption)+
apply(blast intro:WTrt.intros)+
apply(erule WTrt.intros)
apply(assumption)+
apply(erule WTrtSynchronizedNT, assumption)
apply(blast intro: WTrt.intros)+
done



corollary wt'_iff_wt: "(P,E,h \<turnstile> e :' T) = (P,E,h \<turnstile> e : T)"
by(blast intro:wt_wt' wt'_wt)


(*<*)
lemmas WTrt_induct2 = WTrt'.inducts[unfolded wt'_iff_wt,
 case_names WTrtNew WTrtNewArray WTrtCast WTrtVal WTrtVar WTrtBinOpEq WTrtBinOpAdd WTrtLAss
 WTrtAAcc WTrtAAccNT WTrtAAss WTrtAAssNT WTrtFAcc WTrtFAccNT WTrtFAss
 WTrtFAssNT WTrtCall WTrtCallNT WTrtNewThread WTrtWait WTrtNotify WTrtNotifyAll WTrtJoin
 WTrtInitBlock WTrtBlock WTrtSynchronized WTrtSynchronizedNT WTrtInSynchronized WTrtSeq WTrtCond
 WTrtWhile WTrtThrow WTrtTry, consumes 1]
(*>*)


theorem red_progress:
  assumes wf: "wwf_J_prog P" and hconf: "P \<turnstile> h \<surd>"
  shows progress: "\<lbrakk> P,E,h \<turnstile> e : T; \<D> e \<lfloor>dom l\<rfloor>; \<not> final e \<rbrakk> \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>e,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
proof (induct arbitrary: l rule:WTrt_induct2)
  case WTrtNew
  show ?case
  proof cases
    assume "\<exists>a. h a = None"
    from prems show ?thesis
      by (fastsimp del:exE intro!:RedNew simp add:new_Addr_def
                   elim!:wf_Fields_Ex[THEN exE])
  next
    assume "\<not>(\<exists>a. h a = None)"
    from prems show ?thesis
      by(fastsimp intro:RedNewFail simp add:new_Addr_def)
  qed
next
  case (WTrtNewArray E e T l)
  have IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>e,(h,l)\<rangle> -tas\<rightarrow> \<langle>e', s'\<rangle>"
   and D: "\<D> (newA T\<lfloor>e\<rceil>) \<lfloor>dom l\<rfloor>"
   and ei: "P,E,h \<turnstile> e : Integer" by fact+
  from D have De: "\<D> e \<lfloor>dom l\<rfloor>" by auto
  show ?case
  proof cases
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v
      assume [simp]: "e = Val v"
      with ei have "typeof\<^bsub>h\<^esub> v = Some Integer" by fastsimp
      hence exei: "\<exists>i. v = Intg i" by fastsimp
      then obtain i where "v = Intg i" by blast
      thus ?thesis
      proof (cases "i \<ge> 0")
	assume "0 \<le> i"
	thus ?thesis
	proof (cases "new_Addr h")
	  assume "new_Addr h = None"
	  from prems have "P \<turnstile> \<langle>newA T\<lfloor>Val(Intg i)\<rceil>,(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW OutOfMemory,(h, l)\<rangle>"
	    by - (rule RedNewArrayFail, auto)
	  with prems show ?thesis by blast
	next
	  fix a
	  assume "new_Addr h = \<lfloor>a\<rfloor>"
	  from prems have "P \<turnstile> \<langle>newA T\<lfloor>Val(Intg i)\<rceil>,(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>addr a,(h(a\<mapsto>(Arr T i (\<lambda>i. default_val T))), l)\<rangle>"
	    by - (rule RedNewArray, auto)
	  with prems show ?thesis by blast
	qed
      next
	assume "\<not> i \<ge> 0"
	hence "i < 0" by arith
	with prems have "P \<turnstile> \<langle>newA T\<lfloor>Val(Intg i)\<rceil>,(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NegativeArraySize,(h, l)\<rangle>"
	  by - (rule RedNewArrayNegative, auto)
	with prems show ?thesis by blast
      qed
    next
      fix exa
      assume "e = Throw exa"
      with prems have "P \<turnstile> \<langle>newA T\<lfloor>Throw exa\<rceil>,(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw exa,(h, l)\<rangle>"
	by - (rule NewArrayThrow)
      with prems show ?thesis by blast
    qed
  next
    assume "\<not> final e"
    with IH De have exes: "\<exists>e' s' ta. P \<turnstile> \<langle>e,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by simp
    then obtain e' s' ta where "P \<turnstile> \<langle>e,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by blast
    hence "P \<turnstile> \<langle>newA T\<lfloor>e\<rceil>,(h, l)\<rangle> -ta\<rightarrow> \<langle>newA T\<lfloor>e'\<rceil>,s'\<rangle>" by - (rule NewArrayRed)
    thus ?thesis by blast
  qed
next
  case (WTrtCast E e T U l)
  have wte: "P,E,h \<turnstile> e : T"
   and IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>e,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and D: "\<D> (Cast U e) \<lfloor>dom l\<rfloor>" by fact+
  from D have De: "\<D> e \<lfloor>dom l\<rfloor>" by auto
  show ?case
  proof (cases "final e")
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v
      assume ev: "e = Val v"
      with prems obtain V where thvU: "typeof\<^bsub>h\<^esub> v = \<lfloor>V\<rfloor>" by fastsimp
      thus ?thesis
      proof (cases "P \<turnstile> V \<le> U")
	assume "P \<turnstile> V \<le> U"
	with prems have "P \<turnstile> \<langle>Cast U (Val v),(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v,(h,l)\<rangle>"
	  by - (rule RedCast, auto)
	with ev show ?thesis by blast
      next
	assume "\<not> P \<turnstile> V \<le> U"
	with prems have "P \<turnstile> \<langle>Cast U (Val v),(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ClassCast,(h,l)\<rangle>"
	  by - (rule RedCastFail, auto)
	with ev show ?thesis by blast
      qed
    next
      fix a
      assume "e = Throw a"
      thus ?thesis by(blast intro!:CastThrow)
    qed
  next
    assume nf: "\<not> final e"
    from IH[OF De nf] show ?thesis by (blast intro:CastRed)
  qed
next
  case WTrtVal thus ?case by(simp add:final_iff)
next
  case WTrtVar thus ?case by(fastsimp intro:RedVar simp:hyper_isin_def)
next
  case (WTrtBinOpEq E e1 T1 e2 T2)
  show ?case
  proof cases
    assume "final e1"
    thus ?thesis
    proof (rule finalE)
      fix v1 assume [simp]: "e1 = Val v1"
      show ?thesis
      proof cases
	assume "final e2"
	thus ?thesis
	proof (rule finalE)
	  fix v2 assume "e2 = Val v2"
	  thus ?thesis using WTrtBinOpEq by(fastsimp intro:RedBinOp)
	next
	  fix a assume "e2 = Throw a"
	  thus ?thesis by(fastsimp intro:BinOpThrow2)
	qed
      next
	assume "\<not> final e2" from prems show ?thesis
	  by simp (fast intro!:BinOpRed2)
      qed
    next
      fix a assume "e1 = Throw a"
      thus ?thesis by simp (fast intro:BinOpThrow1)
    qed
  next
    assume "\<not> final e1" from prems show ?thesis
      by simp (fast intro:BinOpRed1)
  qed
next
  case (WTrtBinOpAdd E e1 e2 l)
  show ?case
  proof cases
    assume "final e1"
    thus ?thesis
    proof (rule finalE)
      fix v1 assume [simp]: "e1 = Val v1"
      show ?thesis
      proof cases
	assume "final e2"
	thus ?thesis
	proof (rule finalE)
	  fix v2 assume "e2 = Val v2"
	  thus ?thesis using WTrtBinOpAdd by(fastsimp intro:RedBinOp)
	next
	  fix a assume "e2 = Throw a"
	  thus ?thesis by(fastsimp intro:BinOpThrow2)
	qed
      next
	assume "\<not> final e2" from prems show ?thesis
	  by simp (fast intro!:BinOpRed2)
      qed
    next
      fix a assume "e1 = Throw a"
      thus ?thesis by simp (fast intro:BinOpThrow1)
    qed
  next
    assume "\<not> final e1" from prems show ?thesis
      by simp (fast intro:BinOpRed1)
  qed
next
  case (WTrtLAss E V T e T')
  show ?case
  proof cases
    assume "final e" from prems show ?thesis
      by(fastsimp simp:final_iff intro!:RedLAss LAssThrow)
  next
    assume "\<not> final e" from prems show ?thesis
      by simp (fast intro:LAssRed)
  qed
next
  case (WTrtAAcc E a T i l)
  have wte: "P,E,h \<turnstile> a : T\<lfloor>\<rceil>"
   and wtei: "P,E,h \<turnstile> i : Integer"
   and IHa: "\<And>l. \<lbrakk>\<D> a \<lfloor>dom l\<rfloor>; \<not> final a\<rbrakk>
                 \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>a,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and IHi: "\<And>l. \<lbrakk>\<D> i \<lfloor>dom l\<rfloor>; \<not> final i\<rbrakk>
                 \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>i,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and D: "\<D> (a\<lfloor>i\<rceil>) \<lfloor>dom l\<rfloor>" by fact+
  have ref: "is_refT (T\<lfloor>\<rceil>)" by simp
  from D have Da: "\<D> a \<lfloor>dom l\<rfloor>" by simp
  show ?case
  proof (cases "final a")
    assume "final a"
    with wte ref show ?case
    proof (rule finalRefE)
      assume "a = null"
      thus ?case
      proof (cases "final i")
	assume "final i"
	thus ?thesis
	proof (rule finalE)
	  fix v
	  assume "i = Val v"
	  with prems have "P \<turnstile> \<langle>null\<lfloor>Val v\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, (h,l)\<rangle>"
	    by - (rule RedAAccNull)
	  with prems show ?thesis by blast
	next
	  fix ex
	  assume "i = Throw ex"
	  with prems have "P \<turnstile> \<langle>null\<lfloor>Throw ex\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw ex, (h,l)\<rangle>"
	    by - (rule AAccThrow2)
	  with prems show ?thesis by blast
	qed
      next
	assume "\<not> final i"
	from prems show ?thesis
	  by simp
      qed
    next
      fix ad C
      assume "a = addr ad" "T\<lfloor>\<rceil> = Class C"
      thus ?case by simp
    next
      fix ad U
      assume "a = addr ad" "T\<lfloor>\<rceil> = U\<lfloor>\<rceil>"
      thus ?case
      proof (cases "final i")
	assume "final i"
	thus ?thesis
	proof(rule finalE)
	  fix v
	  assume "i = Val v"
	  with wtei have "typeof\<^bsub>h\<^esub> v = Some Integer" by fastsimp
	  hence "\<exists>i. v = Intg i" by fastsimp
	  then obtain i where "v = Intg i" by blast
	  thus ?thesis
	  proof (cases "h ad")
	    assume "h ad = None"
	    from prems show ?thesis by fastsimp
	  next
	    fix arrobj
	    assume had: "h ad = Some arrobj"
	    with wte prems have "typeof\<^bsub>h\<^esub> (Addr ad) = Some (T\<lfloor>\<rceil>)" by fastsimp
	    with had have "\<exists>si el. h ad = Some(Arr T si el)" apply(auto) apply(cases arrobj) by(auto)
	    then obtain T si el where "h ad = Some(Arr T si el)" by blast
	    thus ?thesis
	    proof (cases "i < 0")
	      assume "i < 0"
	      from prems show ?thesis by (fastsimp intro: RedAAccBounds)
	    next
	      assume "\<not> i < 0"
	      hence "i \<ge> 0" by arith
	      thus ?thesis
	      proof (cases "i \<ge> si")
		assume "i \<ge> si"
		from prems show ?thesis by (fastsimp intro: RedAAccBounds)
	      next
		assume "\<not> i \<ge> si"
		hence "i < si" by arith
		with prems show ?thesis by (fastsimp intro: RedAAcc)
	      qed
	    qed
	  qed
	next
	  fix ex
	  assume "i = Throw ex"
	  with prems show ?thesis by (fastsimp intro: AAccThrow2)
	qed
      next
	assume "\<not> final i"
	with prems show ?thesis by (fastsimp intro: AAccRed2)
      qed
    next
      fix ex
      assume "a = Throw ex"
      with prems show ?thesis by (fastsimp intro: AAccThrow1)
    qed
  next
    assume "\<not> final a"
    with prems Da show ?thesis by (fastsimp intro: AAccRed1)
  qed
next
  case (WTrtAAccNT E a i T l)
  have wte: "P,E,h \<turnstile> a : NT"
   and wtei: "P,E,h \<turnstile> i : Integer"
   and IHa: "\<And>l. \<lbrakk>\<D> a \<lfloor>dom l\<rfloor>; \<not> final a\<rbrakk>
                 \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>a,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and IHi: "\<And>l. \<lbrakk>\<D> i \<lfloor>dom l\<rfloor>; \<not> final i\<rbrakk>
                 \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>i,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact+
  have ref: "is_refT NT" by simp
  with prems have Da: "\<D> a \<lfloor>dom l\<rfloor>" by simp
  thus ?case
  proof (cases "final a")
    assume "final a"
    with wte ref show ?thesis
    proof (rule finalRefE)
      assume "a = null"
      thus ?case
      proof (cases "final i")
	assume "final i"
	thus ?thesis
	proof (rule finalE)
	  fix v
	  assume "i = Val v"
	  with prems have "P \<turnstile> \<langle>null\<lfloor>Val v\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, (h,l)\<rangle>"
	    by - (rule RedAAccNull)
	  with prems show ?thesis by blast
	next
	  fix ex
	  assume "i = Throw ex"
	  with prems have "P \<turnstile> \<langle>null\<lfloor>Throw ex\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw ex, (h,l)\<rangle>"
	    by - (rule AAccThrow2)
	  with prems show ?thesis by blast
	qed
      next
	assume "\<not> final i"
	from prems show ?thesis
	  by(fastsimp intro: AAccRed2)
      qed
    next
      fix ad C
      assume "NT = Class C"
      thus ?thesis by simp
    next
      fix ad U
      assume "NT = U\<lfloor>\<rceil>"
      thus ?thesis by simp
    next
      fix ex
      assume "a = Throw ex"
      thus ?thesis by (fastsimp intro: AAccThrow1)
    qed
  next
    assume "\<not> final a"
    with prems Da show ?thesis by (fastsimp intro:AAccRed1)
  qed
next
  case (WTrtAAss E a T i e T' l)
  have wta: "P,E,h \<turnstile> a : T\<lfloor>\<rceil>"
    and wti: "P,E,h \<turnstile> i : Integer"
    and wte: "P,E,h \<turnstile> e : T'"
    and D: "\<D> (a\<lfloor>i\<rceil> := e) \<lfloor>dom l\<rfloor>"
    and IH1: "\<And>l. \<lbrakk>\<D> a \<lfloor>dom l\<rfloor>; \<not> final a\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>a,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
    and IH2: "\<And>l. \<lbrakk>\<D> i \<lfloor>dom l\<rfloor>; \<not> final i\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>i,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
    and IH3: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact+
  have ref: "is_refT (T\<lfloor>\<rceil>)" by simp
  show ?case
  proof (cases "final a")
    assume fa: "final a"
    with wta ref show ?thesis
    proof(rule finalRefE)
      assume "a = null"
      show ?case
      proof(cases "final i")
	assume "final i"
	thus ?case
	proof (rule finalE)
	  fix v
	  assume "i = Val v"
	  with wti have "typeof\<^bsub>h\<^esub> v = Some Integer" by fastsimp
	  hence "\<exists>idx. v = Intg idx" by fastsimp
	  then obtain idx where "v = Intg idx" by blast
	  thus ?thesis
	  proof (cases "final e")
	    assume "final e"
	    thus ?case
	    proof (rule finalE)
	      fix w
	      assume "e = Val w"
	      with prems show ?thesis by (fastsimp intro: RedAAssNull)
	    next
	      fix ex
	      assume "e = Throw ex"
	      with prems show ?thesis by (fastsimp intro: AAssThrow3)
	    qed
	  next
	    assume "\<not> final e"
	    with prems show ?thesis by (fastsimp intro: AAssRed3)
	  qed
	next
	  fix ex
	  assume "i = Throw ex"
	  with prems show ?thesis by (fastsimp intro: AAssThrow2)
	qed
      next
	assume "\<not> final i"
	with prems show ?thesis by (fastsimp intro: AAssRed2)
      qed
    next
      fix ad C
      assume "T\<lfloor>\<rceil> = Class C"
      thus ?case by simp
    next
      fix ad U
      assume aad: "a = addr ad" "T\<lfloor>\<rceil> = U\<lfloor>\<rceil>"
      thus ?case
      proof (cases "final i")
	assume fi: "final i"
	thus ?case
	proof (rule finalE)
	  fix v
	  assume ivalv: "i = Val v"
	  with wti have "typeof\<^bsub>h\<^esub> v = Some Integer" by fastsimp
	  hence "\<exists>idx. v = Intg idx" by fastsimp
	  then obtain idx where vidx: "v = Intg idx" by blast
	  thus ?thesis
	  proof (cases "final e")
	    assume fe: "final e"
	    thus ?case
	    proof(rule finalE)
	      fix w
	      assume evalw: "e = Val w"
	      show ?case
	      proof (cases "h ad")
		assume "h ad = None"
		from prems show ?thesis by fastsimp
	      next
		fix arrobj
		assume had: "h ad = Some arrobj"
		with wta prems have "typeof\<^bsub>h\<^esub> (Addr ad) = Some (T\<lfloor>\<rceil>)" by fastsimp
		with had have "\<exists>si el. h ad = Some(Arr T si el)" apply(auto) apply(cases arrobj) by(auto)
		then obtain si el where "h ad = Some(Arr T si el)" by blast
		thus ?thesis
		proof (cases "idx < 0")
		  assume "idx < 0"
		  from prems show ?case by (fastsimp intro:RedAAssBounds)
		next
		  assume "\<not> idx < 0"
		  hence idxg0: "idx \<ge> 0" by arith
		  thus ?case
		  proof (cases "idx \<ge> si")
		    assume "idx \<ge> si"
		    from prems show ?case by (fastsimp intro:RedAAssBounds)
		  next
		    assume "\<not> idx \<ge> si"
		    hence idxlsi: "idx < si" by arith
		    from wte evalw have "typeof\<^bsub>h\<^esub> w = Some T'" by fastsimp
		    with prems idxlsi idxg0 show ?case
		    proof(cases "P \<turnstile> T' \<le> T")
		      assume "P \<turnstile> T' \<le> T"
		      with prems show ?thesis by(fastsimp intro: RedAAss)
		    next
		      assume "\<not> P \<turnstile> T' \<le> T"
		      with prems show ?thesis by(fastsimp intro: RedAAssStore)
		    qed
		  qed
		qed
	      qed
	    next
	      fix ex
	      assume "e = Throw ex"
	      with prems show ?case by (fastsimp intro: AAssThrow3)
	    qed
	  next
	    assume "\<not> final e"
	    from prems show ?case by (fastsimp intro: AAssRed3)
	  qed
	next
	  fix ex
	  assume "i = Throw ex"
	  from prems show ?case by (fastsimp intro: AAssThrow2)
	qed
      next
	assume "\<not> final i"
	from prems show ?case by (fastsimp intro: AAssRed2)
      qed
    next
      fix ex
      assume "a = Throw ex"
      from prems show ?case by (fastsimp intro:AAssThrow1)
    qed
  next
    assume "\<not> final a"
    from prems show ?case by (fastsimp intro: AAssRed1)
  qed
next
  case (WTrtAAssNT E a i e T' l)
  have wta: "P,E,h \<turnstile> a : NT"
    and wti: "P,E,h \<turnstile> i : Integer"
    and wte: "P,E,h \<turnstile> e : T'"
    and D: "\<D> (a\<lfloor>i\<rceil> := e) \<lfloor>dom l\<rfloor>"
    and IH1: "\<And>l. \<lbrakk>\<D> a \<lfloor>dom l\<rfloor>; \<not> final a\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>a,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
    and IH2: "\<And>l. \<lbrakk>\<D> i \<lfloor>dom l\<rfloor>; \<not> final i\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>i,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
    and IH3: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact+
  have ref: "is_refT NT" by simp
  show ?case
  proof (cases "final a")
    assume fa: "final a"
    show ?case
    proof (cases "final i")
      assume fi: "final i"
      show ?case
      proof (cases "final e")
	assume fe: "final e"
	from prems show ?thesis
	  by(fastsimp simp:final_iff intro: RedAAssNull AAssThrow1 AAssThrow2 AAssThrow3)
      next
	assume "\<not> final e"
	from prems show ?thesis by (fastsimp simp: final_iff intro!:AAssRed3 AAssThrow1 AAssThrow2)
      qed
    next
      assume "\<not> final i"
      from prems show ?thesis by (fastsimp simp: final_iff intro!:AAssRed2 AAssThrow1)
    qed
  next
    assume "\<not> final a"
    from prems show ?thesis by (fastsimp simp: final_iff intro!:AAssRed1)
  qed
next
  case (WTrtFAcc E e C F T D l)
  have wte: "P,E,h \<turnstile> e : Class C"
   and field: "P \<turnstile> C has F:T in D" by fact+
  show ?case
  proof cases
    assume "final e"
    with wte show ?thesis
    proof (rule final_addrE)
      fix a assume e: "e = addr a"
      with wte obtain fs where hp: "h a = Some(Obj C fs)" apply (auto) apply(case_tac aa) by auto
      with hconf have "P,h \<turnstile> (Obj C fs) \<surd>" using hconf_def by fastsimp
      then obtain v where "fs(F,D) = Some v" using field
	by(fastsimp dest:has_fields_fun simp:oconf_def has_field_def)
      with hp e show ?thesis by(fastsimp intro:RedFAcc)
    next
      fix a assume "e = Throw a"
      thus ?thesis by(fastsimp intro:FAccThrow)
    qed
  next
    assume "\<not> final e" from prems show ?thesis
      by(fastsimp intro!:FAccRed)
  qed
next
  case (WTrtFAccNT E e F D T l)
  show ?case
  proof cases
    assume "final e"  --"@{term e} is @{term null} or @{term throw}"
    from prems show ?thesis
      by(fastsimp simp:final_iff intro: RedFAccNull FAccThrow)
  next
    assume "\<not> final e" --"@{term e} reduces by IH"
    from prems show ?thesis by simp (fast intro:FAccRed)
  qed
next
  case (WTrtFAss E e1 C F T D e2 T2 l)
  have wte1: "P,E,h \<turnstile> e1 : Class C" by fact
  show ?case
  proof cases
    assume "final e1"
    with wte1 show ?thesis
    proof (rule final_addrE)
      fix a assume e1: "e1 = addr a"
      show ?thesis
      proof cases
	assume "final e2"
	thus ?thesis
	proof (rule finalE)
	  fix v assume "e2 = Val v"
	  thus ?thesis using e1 wte1
	    apply(auto)
	    apply(case_tac aa)
	    by(fastsimp intro:RedFAss)+
        next
	  fix a assume "e2 = Throw a"
	  thus ?thesis using e1 by(fastsimp intro:FAssThrow2)
	qed
      next
	assume "\<not> final e2" from prems show ?thesis
	  by simp (fast intro!:FAssRed2)
      qed
    next
      fix a assume "e1 = Throw a"
      thus ?thesis by(fastsimp intro:FAssThrow1)
    qed
  next
    assume "\<not> final e1" from prems show ?thesis
      by simp (blast intro!:FAssRed1)
  qed
next
  case (WTrtFAssNT E e\<^isub>1 e\<^isub>2 T\<^isub>2 F D l)
  show ?case
  proof cases
    assume "final e\<^isub>1"  --"@{term e\<^isub>1} is @{term null} or @{term throw}"
    show ?thesis
    proof cases
      assume "final e\<^isub>2"  --"@{term e\<^isub>2} is @{term Val} or @{term throw}"
      from prems show ?thesis
	by(fastsimp simp:final_iff intro: RedFAssNull FAssThrow1 FAssThrow2)
    next
      assume  "\<not> final e\<^isub>2" --"@{term e\<^isub>2} reduces by IH"
      from prems show ?thesis
	by (fastsimp  simp:final_iff intro!:FAssRed2 FAssThrow1)
    qed
  next
    assume "\<not> final e\<^isub>1" --"@{term e\<^isub>1} reduces by IH"
    from prems show ?thesis by (fastsimp intro:FAssRed1)
  qed
next
  case (WTrtCall E e C M Ts T pns body D es Ts' l)
  have wte: "P,E,h \<turnstile> e : Class C" by fact
  have IHe: "\<And>l. \<lbrakk> \<D> e \<lfloor>dom l\<rfloor>; \<not> final e \<rbrakk>
             \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact
  have sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D" by fact
  have IHes: "list_all2 (\<lambda>e T. P,E,h \<turnstile> e : T \<and> (\<forall>x. \<D> e \<lfloor>dom x\<rfloor> \<longrightarrow> \<not> final e \<longrightarrow> (\<exists>e' s' ta. P \<turnstile> \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>))) es Ts'" by fact
  have subtype: "P \<turnstile> Ts' [\<le>] Ts" by fact
  have dae: "\<D> (e\<bullet>M(es)) \<lfloor>dom l\<rfloor>" by fact
  show ?case
  proof(cases "final e")
    assume fine: "final e"
    with wte show ?thesis
    proof (rule final_addrE)
      fix a assume e_addr: "e = addr a"
      show ?thesis
      proof(cases "\<exists>vs. es = map Val vs")
	assume es: "\<exists>vs. es = map Val vs"
	from wte e_addr obtain fs where ha: "h a = Some(Obj C fs)" apply(auto) apply(case_tac aa) by auto
	have "length es = length Ts'" using IHes by -(rule list_all2_lengthD)
	moreover
	{ fix xs ys
	  have "P \<turnstile> xs [\<le>] ys \<Longrightarrow> length xs = length ys"
	    apply(induct xs arbitrary: ys) by(auto) }
	ultimately have esTs: "length es = length Ts" using subtype by(auto)
	thus ?thesis using e_addr ha sees subtype esTs es wf
	  apply(clarify)
	  apply(frule sees_wf_mdecl)
 	   apply(assumption)
	  apply(clarsimp simp add: wf_mdecl_def)
	  apply(rule exI)+
	  apply(rule RedCall)
	      by(fastsimp)
      next
	assume nav: "\<not>(\<exists>vs. es = map Val vs)"
	hence not_all_Val: "\<not>(\<forall>e \<in> set es. \<exists>v. e = Val v)"
	  by(simp add:ex_map_conv)
	{ fix xs
	  have "\<not>(\<exists>vs. xs = map Val vs) \<Longrightarrow> \<exists>vs ex rst. (xs = map Val vs @ ex # rst \<and> \<not> (\<exists>v. ex = Val v))"
	  proof(induct xs)
	    case Nil
	    thus ?case by simp
	  next
	    case (Cons x xes)
	    have IH: "\<not> (\<exists>vs. xes = map Val vs)
	              \<Longrightarrow> \<exists>vs ex rst. xes = map Val vs @ ex # rst \<and> \<not> (\<exists>v. ex = Val v)" by fact
	    have neq: "\<not> (\<exists>vs. x # xes = map Val vs)" by fact
	    { assume xval: "\<exists>v. x = Val v"
	      with neq have "\<not> (\<exists>vs. xes = map Val vs)"
		apply -
		apply(erule contrapos_nn)
		apply(clarsimp)
		apply(rule_tac x="v # vs" in exI)
		by(simp)
	      hence ?case using xval
		apply -
		apply(drule IH)
		apply(clarify)
		apply(rule_tac x="v#vs" in exI)
		by(auto) }
	    moreover
	    { assume xnval: "\<not> (\<exists>v. x = Val v)"
	      hence ?case
		apply -
		apply(rule_tac x="[]" in exI)
		by(auto) }
	    ultimately show ?case by blast
	  qed }
	with nav have "\<exists>vs ex rst. (es = map Val vs @ ex # rst \<and> \<not> (\<exists>v. ex = Val v))" by(blast)
	then obtain vs ex rst where es: "es = map Val vs @ ex # rst" and exnval: "\<not> (\<exists>v. ex = Val v)" by blast
	let ?pred = "(\<lambda>e T. P,E,h \<turnstile> e : T \<and> (\<forall>x. \<D> e \<lfloor>dom x\<rfloor> \<longrightarrow> \<not> final e \<longrightarrow> (\<exists>e' s' ta. P \<turnstile> \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>)))"
	show ?thesis
	proof (cases "final ex")
	  assume "final ex"
	  with exnval obtain b where ex_Throw: "ex = Throw b"
	    by(fast elim!:finalE)
	  show ?thesis using e_addr es ex_Throw
	    by(fastsimp intro:CallThrowParams)
	next
	  assume not_fin: "\<not> final ex"
	  from IHes es have "\<exists>Ts1 Ts2. Ts' = Ts1 @ Ts2 \<and> length Ts1 = length (map Val vs) \<and> length Ts2 = length (ex # rst) \<and>
                list_all2 ?pred (map Val vs) Ts1 \<and> list_all2 ?pred (ex # rst) Ts2"
	    apply(auto)
	    apply(drule list_all2_append1[THEN iffD1])
	    apply(auto)
	    done
	  then obtain Ts1 Ts2 where TsTs1Ts2: "Ts' = Ts1 @ Ts2"
	                        and lengthTs1: "length Ts1 = length (map Val vs)"
	                        and lengthTs2: "length Ts2 = length (ex # rst)"
                                and lsaTs1: "list_all2 ?pred (map Val vs) Ts1"
	                        and lsaTs2: "list_all2 ?pred (ex # rst) Ts2" by fast
	  from lsaTs2 have "\<exists>T' Ts2'. Ts2 = T' # Ts2' \<and> ?pred ex T' \<and> list_all2 ?pred rst Ts2'" 
	    by - (rule list_all2_Cons1[THEN iffD1])
	  then obtain T' Ts2' where Ts2TTs2': "Ts2 = T' # Ts2'"
	                      and IHex: "?pred ex T'"
	                      and lsaTs2': "list_all2 ?pred rst Ts2'" by(auto)
	  with dae TsTs1Ts2 es e_addr have "\<D> ex \<lfloor>dom l\<rfloor>" by(clarsimp)
	  with not_fin IHex have "\<exists>e' s' ta. P \<turnstile> \<langle>ex,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by(clarsimp) 
	  with es e_addr show ?thesis by(fastsimp intro: CallParams)
	qed
      qed
    next
      fix a assume "e = Throw a"
      thus ?thesis by(fast intro!:CallThrowObj)
    qed
  next
    assume "\<not> final e"
    with prems show ?thesis by simp (blast intro!:CallObj)
  qed
next
  case (WTrtCallNT E e es Ts M T l)
  have wte: "P,E,h \<turnstile> e : NT" by fact
  have IHe: "\<And>l. \<lbrakk> \<D> e \<lfloor>dom l\<rfloor>; \<not> final e \<rbrakk>
             \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact
  have IHes: "list_all2 (\<lambda>e T. P,E,h \<turnstile> e : T \<and> (\<forall>x. \<D> e \<lfloor>dom x\<rfloor> \<longrightarrow> \<not> final e \<longrightarrow> (\<exists>e' s' ta. P \<turnstile> \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>))) es Ts" by fact
  have dae: "\<D> (e\<bullet>M(es)) \<lfloor>dom l\<rfloor>" by fact
  show ?case
  proof(cases "final e")
    assume fine: "final e"
    { fix v assume "e = Val v"
      hence enull: "e = null" using wte by simp
      have ?case
      proof (cases "(\<exists>vs. es = map Val vs) \<or> (\<exists>vs a es'. es = map Val vs @ Throw a # es')")
	assume "(\<exists>vs. es = map Val vs) \<or> (\<exists>vs a es'. es = map Val vs @ Throw a # es')"
	moreover
	{ fix vs assume "es = map Val vs"
	  with enull have ?thesis by(fastsimp intro: RedCallNull) }
	moreover
	{ fix vs a es' assume "es = map Val vs @ Throw a # es'"
	  with enull have ?thesis by(fastsimp intro: CallThrowParams) }
	ultimately show ?thesis by(fastsimp)
      next
	assume "\<not> ((\<exists>vs. es = map Val vs) \<or> (\<exists>vs a es'. es = map Val vs @ Throw a # es'))"
	hence nav: "\<not>(\<exists>vs. es = map Val vs)" by auto
	hence not_all_Val: "\<not>(\<forall>e \<in> set es. \<exists>v. e = Val v)"
	  by(simp add:ex_map_conv)
	{ fix xs
	  have "\<not>(\<exists>vs. xs = map Val vs) \<Longrightarrow> \<exists>vs ex rst. (xs = map Val vs @ ex # rst \<and> \<not> (\<exists>v. ex = Val v))"
	  proof(induct xs)
	    case Nil
	    thus ?case by simp
	  next
	    case (Cons x xes)
	    have IH: "\<not> (\<exists>vs. xes = map Val vs) \<Longrightarrow> \<exists>vs ex rst. xes = map Val vs @ ex # rst \<and> \<not> (\<exists>v. ex = Val v)" by fact
	    have neq: "\<not> (\<exists>vs. x # xes = map Val vs)" by fact
	    { assume xval: "\<exists>v. x = Val v"
	      with neq have "\<not> (\<exists>vs. xes = map Val vs)"
		apply -
		apply(erule contrapos_nn)
		apply(clarsimp)
		apply(rule_tac x="v # vs" in exI)
		by(simp)
	      hence ?case using xval
		apply -
		apply(drule IH)
		apply(clarify)
		apply(rule_tac x="v#vs" in exI)
		by(auto) }
	    moreover
	    { assume xnval: "\<not> (\<exists>v. x = Val v)"
	      hence ?case
		apply -
		apply(rule_tac x="[]" in exI)
		by(auto) }
	    ultimately show ?case by blast
	  qed }
	with nav have "\<exists>vs ex rst. (es = map Val vs @ ex # rst \<and> \<not> (\<exists>v. ex = Val v))" by(blast)
	then obtain vs ex rst where es: "es = map Val vs @ ex # rst" and exnval: "\<not> (\<exists>v. ex = Val v)" by blast
	let ?pred = "(\<lambda>e T. P,E,h \<turnstile> e : T \<and> (\<forall>x. \<D> e \<lfloor>dom x\<rfloor> \<longrightarrow> \<not> final e \<longrightarrow> (\<exists>e' s' ta. P \<turnstile> \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>)))"
	show ?thesis
	proof (cases "final ex")
	  assume "final ex"
	  with exnval obtain b where ex_Throw: "ex = Throw b"
	    by(fast elim!:finalE)
	  show ?thesis using enull es ex_Throw
	    by(fastsimp intro:CallThrowParams)
	next
	  assume not_fin: "\<not> final ex"
	  from IHes es
	  have "\<exists>Ts1 Ts2. Ts = Ts1 @ Ts2 \<and> length Ts1 = length (map Val vs) \<and> length Ts2 = length (ex # rst) \<and>
                list_all2 ?pred (map Val vs) Ts1 \<and> list_all2 ?pred (ex # rst) Ts2"
	    apply(auto)
	    apply(drule list_all2_append1[THEN iffD1])
	    apply(auto)
	    done
	  then obtain Ts1 Ts2 where TsTs1Ts2: "Ts = Ts1 @ Ts2"
	                        and lengthTs1: "length Ts1 = length (map Val vs)"
	                        and lengthTs2: "length Ts2 = length (ex # rst)"
                                and lsaTs1: "list_all2 ?pred (map Val vs) Ts1"
	                        and lsaTs2: "list_all2 ?pred (ex # rst) Ts2" by fast
	  from lsaTs2 have "\<exists>T' Ts2'. Ts2 = T' # Ts2' \<and> ?pred ex T' \<and> list_all2 ?pred rst Ts2'"
	    by - (rule list_all2_Cons1[THEN iffD1])
	  then obtain T' Ts2' where Ts2TTs2': "Ts2 = T' # Ts2'"
	                      and IHex: "?pred ex T'"
	                      and lsaTs2': "list_all2 ?pred rst Ts2'" by(auto)
	  with dae TsTs1Ts2 es enull have "\<D> ex \<lfloor>dom l\<rfloor>" by(clarsimp)
	  with not_fin IHex have "\<exists>e' s' ta. P \<turnstile> \<langle>ex,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by(clarsimp) 
	  with es enull show ?thesis by(fastsimp intro: CallParams)
	qed
      qed
    }
    moreover
    { fix a assume "e = Throw a"
      hence ?case by(fastsimp intro: CallThrowObj) }
    ultimately show ?thesis using fine by(fastsimp simp:final_iff)
  next
    assume "\<not> final e"
    with prems show ?thesis by simp (blast intro!:CallObj)
  qed
next
  case (WTrtNewThread E e C l)
  have wt: "P,E,h \<turnstile> e : Class C" by fact
  have IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' ta. P \<turnstile> \<langle>e,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by fact
  have PCThread: "P \<turnstile> C \<preceq>\<^sup>* Thread" by fact
  have "\<D> (e\<bullet>start([])) \<lfloor>dom l\<rfloor>" by fact
  hence da: "\<D> e \<lfloor>dom l\<rfloor>" by simp
  show ?case
  proof(cases "final e")
    assume fine: "final e"
    with wt show ?thesis
    proof (rule final_addrE)
      fix a assume e_addr: "e = addr a"
      with wt obtain fs where ha: "h a = Some(Obj C fs)" apply(auto) apply(case_tac aa) by auto
      with PCThread e_addr show ?thesis by(fastsimp intro: RedNewThread)
    next
      fix a assume ethrow: "e = Throw a"
      thus ?thesis by(fastsimp intro: CallThrowObj)
    qed
  next
    assume nfine: "\<not> final e"
    show ?thesis using IH[OF da nfine] by (fastsimp intro: CallObj)
  qed
next
  case (WTrtWait E e T l)
  have wt: "P,E,h \<turnstile> e : T" by fact
  have IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact
  have refT: "is_refT T" by fact
  have TNT: "T \<noteq> NT" by fact
  have dae: "\<D> (e\<bullet>wait([])) \<lfloor>dom l\<rfloor>" by fact
  show ?case
  proof(cases "final e")
    case True
    have fine: "final e" .
    with wt refT show ?thesis
    proof (rule finalRefE)
      assume enull: "e = null"
      with wt have "T = NT" by(auto)
      with TNT show ?thesis by contradiction
    next
      fix a C
      assume eaddr: "e = addr a"
      from wt eaddr obtain arrobj where ha: "h a = \<lfloor>arrobj\<rfloor>" by auto
      with eaddr show ?thesis by(fastsimp intro: RedWait)
    next
      fix a U
      assume eaddr: "e = addr a"
      from wt eaddr obtain arrobj where ha: "h a = \<lfloor>arrobj\<rfloor>" by auto
      with eaddr show ?thesis by(fastsimp intro: RedWait)
    next
      fix a
      assume ethrow: "e = Throw a"
      thus ?thesis by(fastsimp intro: CallThrowObj)
    qed
  next
    assume nfine: "\<not> final e"
    show ?thesis using IH[OF _ nfine] dae by (fastsimp intro: CallObj)
  qed
next
  case (WTrtNotify E e T l)
  have wt: "P,E,h \<turnstile> e : T" by fact
  have IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact
  have refT: "is_refT T" by fact
  have TNT: "T \<noteq> NT" by fact
  have dae: "\<D> (e\<bullet>notify([])) \<lfloor>dom l\<rfloor>" by fact
  show ?case
  proof(cases "final e")
    case True
    have fine: "final e" by fact
    with wt refT show ?thesis
    proof (rule finalRefE)
      assume enull: "e = null"
      with wt have "T = NT" by(auto)
      with TNT show ?thesis by contradiction
    next
      fix a C
      assume eaddr: "e = addr a"
      from wt eaddr obtain arrobj where ha: "h a = \<lfloor>arrobj\<rfloor>" by auto
      with eaddr show ?thesis by(fastsimp intro: RedNotify)
    next
      fix a U
      assume eaddr: "e = addr a"
      from wt eaddr obtain arrobj where ha: "h a = \<lfloor>arrobj\<rfloor>" by auto
      with eaddr show ?thesis by(fastsimp intro: RedNotify)
    next
      fix a
      assume ethrow: "e = Throw a"
      thus ?thesis by(fastsimp intro: CallThrowObj)
    qed
  next
    assume nfine: "\<not> final e"
    show ?thesis using IH[OF _ nfine] dae by (fastsimp intro: CallObj)
  qed
next
  case (WTrtNotifyAll E e T l)
  have wt: "P,E,h \<turnstile> e : T" by fact
  have IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact
  have refT: "is_refT T" by fact
  have TNT: "T \<noteq> NT" by fact
  have dae: "\<D> (e\<bullet>notifyAll([])) \<lfloor>dom l\<rfloor>" by fact
  show ?case
  proof(cases "final e")
    case True
    have fine: "final e" by fact
    with wt refT show ?thesis
    proof (rule finalRefE)
      assume enull: "e = null"
      with wt have "T = NT" by(auto)
      with TNT show ?thesis by contradiction
    next
      fix a C
      assume eaddr: "e = addr a"
      from wt eaddr obtain arrobj where ha: "h a = \<lfloor>arrobj\<rfloor>" by auto
      with eaddr show ?thesis by(fastsimp intro: RedNotifyAll)
    next
      fix a U
      assume eaddr: "e = addr a"
      from wt eaddr obtain arrobj where ha: "h a = \<lfloor>arrobj\<rfloor>" by auto
      with eaddr show ?thesis by(fastsimp intro: RedNotifyAll)
    next
      fix a
      assume ethrow: "e = Throw a"
      thus ?thesis by(fastsimp intro: CallThrowObj)
    qed
  next
    assume nfine: "\<not> final e"
    show ?thesis using IH[OF _ nfine] dae by (fastsimp intro: CallObj)
  qed
next
  case (WTrtJoin E e C l)
  have wt: "P,E,h \<turnstile> e : Class C" by fact
  have IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' ta. P \<turnstile> \<langle>e,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by fact
  have PCThread: "P \<turnstile> C \<preceq>\<^sup>* Thread" by fact
  have "\<D> (e\<bullet>join([])) \<lfloor>dom l\<rfloor>" by fact
  hence da: "\<D> e \<lfloor>dom l\<rfloor>" by simp
  show ?case
  proof(cases "final e")
    assume fine: "final e"
    with wt show ?thesis
    proof (rule final_addrE)
      fix a assume e_addr: "e = addr a"
      with wt obtain fs where ha: "h a = Some(Obj C fs)" apply(auto) apply(case_tac aa) by auto
      with PCThread e_addr show ?thesis by(fastsimp intro: RedJoin)
    next
      fix a assume ethrow: "e = Throw a"
      thus ?thesis by(fastsimp intro: CallThrowObj)
    qed
  next
    assume nfine: "\<not> final e"
    show ?thesis using IH[OF da nfine] by (fastsimp intro: CallObj)
  qed
next
  case (WTrtInitBlock v T\<^isub>1 T E V e\<^isub>2 T\<^isub>2 l)
  have IH2: "\<And>l. \<lbrakk>\<D> e\<^isub>2 \<lfloor>dom l\<rfloor>; \<not> final e\<^isub>2\<rbrakk>
                  \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>e\<^isub>2,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and D: "\<D> {V:T := Val v; e\<^isub>2} \<lfloor>dom l\<rfloor>" by fact
  show ?case
  proof cases
    assume "final e\<^isub>2"
    then show ?thesis
    proof (rule finalE)
      fix v\<^isub>2 assume "e\<^isub>2 = Val v\<^isub>2"
      thus ?thesis by(fast intro:RedInitBlock)
    next
      fix a assume "e\<^isub>2 = Throw a"
      thus ?thesis by(fast intro:InitBlockThrow)
    qed
  next
    assume not_fin2: "\<not> final e\<^isub>2"
    from D have D2: "\<D> e\<^isub>2 \<lfloor>dom(l(V\<mapsto>v))\<rfloor>" by (auto simp:hyperset_defs)
    from IH2[OF D2 not_fin2]
    obtain h' l' e' tas where red2: "P \<turnstile> \<langle>e\<^isub>2,(h, l(V\<mapsto>v))\<rangle> -tas\<rightarrow> \<langle>e',(h', l')\<rangle>"
      by fast
    from red_lcl_incr[OF red2] have "V \<in> dom l'" by auto
    with red2 show ?thesis by(fastsimp intro:InitBlockRed)
  qed
next
  case (WTrtBlock E V T e T' l)
  have IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                 \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>e,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and unass: "\<not> assigned V e" and D: "\<D> {V:T; e} \<lfloor>dom l\<rfloor>" by fact+
  show ?case
  proof cases
    assume "final e"
    then show ?thesis
    proof (rule finalE)
      fix v assume "e = Val v" thus ?thesis by(fast intro:RedBlock)
    next
      fix a assume "e = Throw a"
      thus ?thesis by(fast intro:BlockThrow)
    qed
  next
    assume not_fin: "\<not> final e"
    from D have De: "\<D> e \<lfloor>dom(l(V:=None))\<rfloor>" by(simp add:hyperset_defs)
    from IH[OF De not_fin]
    obtain h' l' e' tas where red: "P \<turnstile> \<langle>e,(h,l(V:=None))\<rangle> -tas\<rightarrow> \<langle>e',(h',l')\<rangle>"
      by auto
    show ?thesis
    proof (cases "l' V")
      assume "l' V = None"
      with red unass show ?thesis by(blast intro: BlockRedNone)
    next
      fix v assume "l' V = Some v"
      with red unass show ?thesis by(blast intro: BlockRedSome)
    qed
  qed
next
  case (WTrtSynchronized E o' T e T' l)
  note wto = `P,E,h \<turnstile> o' : T`
  note IHe = `\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e \<rbrakk> \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>`
  note wte = `P,E,h \<turnstile> e : T'`
  note IHo = `\<And>l. \<lbrakk>\<D> o' \<lfloor>dom l\<rfloor>; \<not> final o' \<rbrakk> \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>o',(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>`
  note refT = `is_refT T`
  note TNT = `T \<noteq> NT`
  note dae = `\<D> (sync(o') e) \<lfloor>dom l\<rfloor>`
  show ?case
  proof(cases "final o'")
    assume fino: "final o'" 
    thus ?thesis
    proof (rule finalE)
      fix v
      assume oval: "o' = Val v"
      with wto refT show ?thesis
      proof(cases "v")
	assume vnull: "v = Null"
	with oval vnull show ?thesis
	  by(fastsimp intro: SynchronizedNull)
      next
	fix ad
	assume vaddr: "v = Addr ad"
	from wto oval vaddr obtain arrobj where ha: "h ad = \<lfloor>arrobj\<rfloor>" by auto
	thus ?thesis using oval vaddr
	  by(fastsimp intro: LockSynchronized)
      qed(auto elim: refTE)
    next
      fix a
      assume othrow: "o' = Throw a"
      thus ?thesis by(fastsimp intro: SynchronizedThrow1)
    qed
  next
    assume nfino: "\<not> final o'"
    with dae IHo show ?case by(fastsimp intro: SynchronizedRed1)
  qed
next
  case (WTrtSynchronizedNT E o' e T T' l)
  have wto: "P,E,h \<turnstile> o' : NT" by fact
  have IHo: "\<And>l. \<lbrakk>\<D> o' \<lfloor>dom l\<rfloor>; \<not> final o' \<rbrakk>
                  \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>o',(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact
  have dae: "\<D> (sync(o') e) \<lfloor>dom l\<rfloor>" by fact
  show ?case
  proof(cases "final o'")
    assume "final o'" thus ?thesis using wto
      by(fastsimp elim!: finalE intro: SynchronizedNull SynchronizedThrow1)
  next
    assume nfino: "\<not> final o'"
    with dae IHo nfino show ?thesis by(fastsimp intro: SynchronizedRed1)
  qed
next
  case (WTrtInSynchronized E a T e T' l)
  show ?case
  proof(cases "final e")
    case True thus ?thesis
      by(fastsimp elim!: finalE intro: UnlockSynchronized SynchronizedThrow2)
  next
    case False 
    moreover  from `\<D> (insync(a) e) \<lfloor>dom l\<rfloor>` have "\<D> e \<lfloor>dom l\<rfloor>" by simp
    moreover note IHe = `\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. P \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>`
    ultimately show ?thesis by(fastsimp intro: SynchronizedRed2)
  qed
next
  case (WTrtSeq E e1 T1 e2 T2 l)
  show ?case
  proof cases
    assume "final e1"
    thus ?thesis
      by(fast elim:finalE intro:intro:RedSeq SeqThrow)
  next
    assume "\<not> final e1" from prems show ?thesis
      by simp (blast intro:SeqRed)
  qed
next
  case (WTrtCond E e e1 T1 e2 T2 T l)
  have wt: "P,E,h \<turnstile> e : Boolean" by fact
  show ?case
  proof cases
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v assume val: "e = Val v"
      then obtain b where v: "v = Bool b" using wt by auto
      show ?thesis
      proof (cases b)
	case True with val v show ?thesis by(fastsimp intro:RedCondT)
      next
	case False with val v show ?thesis by(fastsimp intro:RedCondF)
      qed
    next
      fix a assume "e = Throw a"
      thus ?thesis by(fast intro:CondThrow)
    qed
  next
    assume "\<not> final e" from prems show ?thesis
      by simp (fast intro:CondRed)
  qed
next
  case WTrtWhile show ?case by(fast intro:RedWhile)
next
  case (WTrtThrow E e T T' l)
  show ?case
  proof cases
    assume "final e" -- {*Then @{term e} must be @{term throw} or @{term null}*}
    thus ?thesis
    proof(induct rule: finalE)
      case (Val v)
      with `is_refT_class T` `\<not> final (throw e)` `P,E,h \<turnstile> e : T`
      have "v = Null" by(auto elim!: final.cases refT_classE)
      thus ?thesis using Val by(fastsimp intro: RedThrowNull)
    next
      case (Throw a)
      thus ?thesis by(fastsimp intro: ThrowThrow)
    qed
  next
    assume "\<not> final e" -- {*Then @{term e} must reduce*}
    from prems show ?thesis by simp (blast intro:ThrowRed)
  qed
next
  case (WTrtTry E e1 T1 V C e2 T2 l)
  have wt1: "P,E,h \<turnstile> e1 : T1" by fact
  show ?case
  proof cases
    assume "final e1"
    thus ?thesis
    proof (rule finalE)
      fix v assume "e1 = Val v"
      thus ?thesis by(fast intro:RedTry)
    next
      fix a
      assume e1_Throw: "e1 = Throw a"
      with wt1 obtain D fs where ha: "h a = Some(Obj D fs)"
	by(fastsimp split: heapobj.split_asm elim!: is_refT_class.cases)
      show ?thesis
      proof cases
	assume "P \<turnstile> D \<preceq>\<^sup>* C"
	with e1_Throw ha show ?thesis by(fastsimp intro!:RedTryCatch)
      next
	assume "\<not> P \<turnstile> D \<preceq>\<^sup>* C"
	with e1_Throw ha show ?thesis by(force intro!:RedTryFail)
      qed
    qed
  next
    assume "\<not> final e1"
    show ?thesis using prems by simp (fast intro:TryRed)
  qed
qed

end