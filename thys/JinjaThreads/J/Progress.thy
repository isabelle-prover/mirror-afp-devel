(*  Title:      JinjaThreads/J/SmallProgress.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Progress of Small Step Semantics} *}
theory Progress imports
  WellTypeRT
  DefAss
  SmallStep
  "../Common/ExternalCallWF"
  WWellForm
begin

lemma (in J_heap_base) final_addrE [consumes 2, case_names addr Throw]:
  "\<lbrakk> P,E,h \<turnstile> e : Class C; final e;
    \<And>a. e = addr a \<Longrightarrow> R;
    \<And>a. e = Throw a \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
apply(auto elim!: final.cases)
apply(case_tac v)
apply auto
done

lemma (in J_heap) finalRefE [consumes 3, case_names null Class Array Throw]:
 "\<lbrakk> P,E,h \<turnstile> e : T; is_refT T; final e;
   e = null \<Longrightarrow> R;
   \<And>a C. \<lbrakk> e = addr a; T = Class C \<rbrakk> \<Longrightarrow> R;
   \<And>a U. \<lbrakk> e = addr a; T = U\<lfloor>\<rceil> \<rbrakk> \<Longrightarrow> R;
   \<And>a. e = Throw a \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
apply(auto simp:final_iff)
apply(case_tac v)
apply(auto elim!: is_refT.cases dest: typeof_addr_eq_Some_conv)
done

context J_heap_base begin

inductive WTrt' :: "J_prog \<Rightarrow> 'heap \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"
  and WTrts' :: "J_prog \<Rightarrow> 'heap \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> bool"
  for P :: "J_prog" and h :: "'heap" where
  "is_class P C  \<Longrightarrow> WTrt' P h E (new C) (Class C)"

| "\<lbrakk> WTrt' P h E e Integer; is_type P T \<rbrakk> \<Longrightarrow> WTrt' P h E (newA T\<lfloor>e\<rceil>) (T\<lfloor>\<rceil>)"

| "\<lbrakk> WTrt' P h E e T; is_type P U \<rbrakk> \<Longrightarrow> WTrt' P h E (Cast U e) U"

| "\<lbrakk> WTrt' P h E e T; is_type P U \<rbrakk> \<Longrightarrow> WTrt' P h E (e instanceof U) Boolean"

| "typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow> WTrt' P h E (Val v) T"

| "E V = Some T  \<Longrightarrow> WTrt' P h E (Var V) T"

| "\<lbrakk> WTrt' P h E e1 T1; WTrt' P h E e2 T2; P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T \<rbrakk> \<Longrightarrow> WTrt' P h E (e1\<guillemotleft>bop\<guillemotright>e2) T"

| "\<lbrakk> WTrt' P h E (Var V) T; WTrt' P h E e T'; P \<turnstile> T' \<le> T \<rbrakk> \<Longrightarrow> WTrt' P h E (V:=e) Void"

| "\<lbrakk> WTrt' P h E a (T\<lfloor>\<rceil>); WTrt' P h E i Integer \<rbrakk> \<Longrightarrow> WTrt' P h E (a\<lfloor>i\<rceil>) T"

| "\<lbrakk> WTrt' P h E a NT; WTrt' P h E i Integer \<rbrakk> \<Longrightarrow> WTrt' P h E (a\<lfloor>i\<rceil>) T"

| "\<lbrakk> WTrt' P h E a (T\<lfloor>\<rceil>); WTrt' P h E i Integer; WTrt' P h E e T' \<rbrakk> \<Longrightarrow> WTrt' P h E (a\<lfloor>i\<rceil> := e) Void"

| "\<lbrakk> WTrt' P h E a NT; WTrt' P h E i Integer; WTrt' P h E e T' \<rbrakk> \<Longrightarrow> WTrt' P h E (a\<lfloor>i\<rceil> := e) Void"

| "WTrt' P h E a (T\<lfloor>\<rceil>) \<Longrightarrow> WTrt' P h E (a\<bullet>length) Integer"

| "WTrt' P h E a NT \<Longrightarrow> WTrt' P h E (a\<bullet>length) T"

| "\<lbrakk> WTrt' P h E e (Class C); P \<turnstile> C has F:T in D \<rbrakk> \<Longrightarrow> WTrt' P h E (e\<bullet>F{D}) T"

| "WTrt' P h E e NT \<Longrightarrow> WTrt' P h E (e\<bullet>F{D}) T"

| "\<lbrakk> WTrt' P h E e1 (Class C); P \<turnstile> C has F:T in D; WTrt' P h E e2 T2; P \<turnstile> T2 \<le> T \<rbrakk> \<Longrightarrow> WTrt' P h E (e1\<bullet>F{D}:=e2) Void"

| "\<lbrakk> WTrt' P h E e1 NT; WTrt' P h E e2 T2 \<rbrakk> \<Longrightarrow> WTrt' P h E (e1\<bullet>F{D}:=e2) Void"

| "\<lbrakk> WTrt' P h E e (Class C); \<not> is_external_call P (Class C) M; P \<turnstile> C sees M:Ts \<rightarrow> T = (pns,body) in D;
     WTrts' P h E es Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk> \<Longrightarrow> WTrt' P h E (e\<bullet>M(es)) T"

| "\<lbrakk> WTrt' P h E e NT; WTrts' P h E es Ts \<rbrakk> \<Longrightarrow> WTrt' P h E (e\<bullet>M(es)) T"

| "\<lbrakk> WTrt' P h E e T; WTrts' P h E es Ts; P \<turnstile> T\<bullet>M(Ts') :: U; P \<turnstile> Ts [\<le>] Ts' \<rbrakk> \<Longrightarrow> WTrt' P h E (e\<bullet>M(es)) U"

| "\<lbrakk> typeof\<^bsub>h\<^esub> v = Some T1; P \<turnstile> T1 \<le> T; WTrt' P h (E(V\<mapsto>T)) e2 T2 \<rbrakk> \<Longrightarrow> WTrt' P h E {V:T=\<lfloor>v\<rfloor>; e2} T2"

| "\<lbrakk> WTrt' P h (E(V\<mapsto>T)) e T' \<rbrakk> \<Longrightarrow> WTrt' P h E {V:T=None; e} T'"

| "\<lbrakk> WTrt' P h E o' T; is_refT T; WTrt' P h E e T' \<rbrakk> \<Longrightarrow> WTrt' P h E (sync(o') e) T'"

| "\<lbrakk> WTrt' P h E (addr a) T; WTrt' P h E e T' \<rbrakk> \<Longrightarrow> WTrt' P h E (insync(a) e) T'"

| "\<lbrakk> WTrt' P h E e1 T1; WTrt' P h E e2 T2 \<rbrakk> \<Longrightarrow> WTrt' P h E (e1;;e2) T2"

| "\<lbrakk> WTrt' P h E e Boolean; WTrt' P h E e1 T1; WTrt' P h E e2 T2; 
       P \<turnstile> T1 \<le> T2 \<or> P \<turnstile> T2 \<le> T1; P \<turnstile> T1 \<le> T2 \<longrightarrow> T = T2; P \<turnstile> T2 \<le> T1 \<Longrightarrow> T = T1 \<rbrakk>
    \<Longrightarrow> WTrt' P h E (if (e) e1 else e2) T"

| "\<lbrakk> WTrt' P h E e Boolean; WTrt' P h E c T \<rbrakk> \<Longrightarrow> WTrt' P h E (while(e) c) Void"

| "\<lbrakk> WTrt' P h E e T; P \<turnstile> T \<le> Class Throwable \<rbrakk> \<Longrightarrow> WTrt' P h E (throw e) T'"

| "\<lbrakk> WTrt' P h E e1 T1; WTrt' P h (E(V \<mapsto> Class C)) e2 T2; P \<turnstile> T1 \<le> T2 \<rbrakk> \<Longrightarrow> WTrt' P h E (try e1 catch(C V) e2) T2"

| "WTrts' P h E [] []"

| "\<lbrakk> WTrt' P h E e T; WTrts' P h E es Ts \<rbrakk> \<Longrightarrow> WTrts' P h E (e # es) (T # Ts)"

abbreviation
  WTrt'_syntax :: "J_prog \<Rightarrow> env \<Rightarrow> 'heap \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" ("_,_,_ \<turnstile> _ :' _"   [51,51,51]50)
where
  "P,E,h \<turnstile> e :' T \<equiv> WTrt' P h E e T"

abbreviation
  WTrts'_syntax :: "J_prog \<Rightarrow> env \<Rightarrow> 'heap \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> bool" ("_,_,_ \<turnstile> _ [:''] _"   [51,51,51]50)
where
  "P,E,h \<turnstile> e [:'] T \<equiv> WTrts' P h E e T"

inductive_cases WTrt'_elim_cases[elim!]:
  "P,E,h \<turnstile> V :=e :' T"

lemma [iff]: "P,E,h \<turnstile> e\<^isub>1;;e\<^isub>2 :' T\<^isub>2 = (\<exists>T\<^isub>1. P,E,h \<turnstile> e\<^isub>1:' T\<^isub>1 \<and> P,E,h \<turnstile> e\<^isub>2:' T\<^isub>2)"
by (auto elim: WTrt'.cases intro!:WTrt'_WTrts'.intros)

lemma [iff]: "P,E,h \<turnstile> Val v :' T = (typeof\<^bsub>h\<^esub> v = Some T)"
by (auto elim: WTrt'.cases intro!:WTrt'_WTrts'.intros)

lemma [iff]: "P,E,h \<turnstile> Var v :' T = (E v = Some T)"
by (auto elim: WTrt'.cases intro!:WTrt'_WTrts'.intros)


lemma wt_wt': "P,E,h \<turnstile> e : T \<Longrightarrow> P,E,h \<turnstile> e :' T"
  and wts_wts': "P,E,h \<turnstile> es [:] Ts \<Longrightarrow> P,E,h \<turnstile> es [:'] Ts"
apply (induct rule:WTrt_WTrts.inducts)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)
apply(clarsimp split: option.split_asm simp del: fun_upd_apply)
 apply(erule WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)+
done



lemma wt'_wt: "P,E,h \<turnstile> e :' T \<Longrightarrow> P,E,h \<turnstile> e : T"
  and wts'_wts: "P,E,h \<turnstile> es [:'] Ts \<Longrightarrow> P,E,h \<turnstile> es [:] Ts"
apply (induct rule:WTrt'_WTrts'.inducts)
apply(blast intro:WTrt_WTrts.intros)+
apply(erule WTrt_WTrts.intros, simp)
apply(erule WTrt_WTrts.intros, simp)
apply(erule WTrt_WTrts.intros, assumption+)
apply(blast intro: WTrt_WTrts.intros)+
done


corollary wt'_iff_wt: "(P,E,h \<turnstile> e :' T) = (P,E,h \<turnstile> e : T)"
  and  wts'_iff_wts: "(P,E,h \<turnstile> es [:'] Ts) = (P,E,h \<turnstile> es [:] Ts)"
by(blast intro:wt_wt' wt'_wt wts_wts' wts'_wts)+


(*<*)
lemmas WTrt_induct2 = WTrt'_WTrts'.inducts[unfolded wt'_iff_wt wts'_iff_wts,
 case_names WTrtNew WTrtNewArray WTrtCast WTrtInstanceOf WTrtVal WTrtVar WTrtBinOp WTrtLAss
 WTrtAAcc WTrtAAccNT WTrtAAss WTrtAAssNT WTrtALength WTrtALengthNT WTrtFAcc WTrtFAccNT WTrtFAss
 WTrtFAssNT WTrtCall WTrtCallNT WTrtCallExternal
 WTrtInitBlock WTrtBlock WTrtSynchronized WTrtInSynchronized WTrtSeq WTrtCond
 WTrtWhile WTrtThrow WTrtTry WTrtNil WTrtCons, consumes 1]
(*>*)

end

context J_progress begin 

theorem red_progress:
  assumes wf: "wwf_J_prog P" and hconf: "hconf h"
  shows progress: "\<lbrakk> P,E,h \<turnstile> e : T; \<D> e \<lfloor>dom l\<rfloor>; \<not> final e \<rbrakk> \<Longrightarrow> \<exists>e' s' ta. extTA,P,t \<turnstile> \<langle>e,(h,l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>"
  and progresss: "\<lbrakk> P,E,h \<turnstile> es [:] Ts; \<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es \<rbrakk> \<Longrightarrow> \<exists>es' s' ta. extTA,P,t \<turnstile> \<langle>es,(h,l)\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>"
proof (induct arbitrary: l and l rule:WTrt_induct2)
  case (WTrtNew C)
  obtain h' ao where h': "new_obj h C = (h', ao)" by(cases "new_obj h C")
  thus ?case using WTrtNew
    by(cases ao)(fastsimp intro: RedNewFail RedNew)+
next
  case (WTrtNewArray E e T l)
  have IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h,l)\<rangle> -tas\<rightarrow> \<langle>e', s'\<rangle>"
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
      proof (cases "0 <=s i")
	case True
        obtain h' ao where "new_arr h T (nat (sint i)) = (h', ao)"
          by(cases "new_arr h T (nat (sint i))")
	thus ?thesis using True `v = Intg i` WTrtNewArray.prems
          by(cases ao)(auto simp del: split_paired_Ex,(blast intro: RedNewArrayFail RedNewArray)+)
      next
	assume "\<not> 0 <=s i"
	hence "i <s 0" by simp
	with prems have "extTA,P,t \<turnstile> \<langle>newA T\<lfloor>Val(Intg i)\<rceil>,(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NegativeArraySize,(h, l)\<rangle>"
	  by - (rule RedNewArrayNegative, auto)
	with prems show ?thesis by blast
      qed
    next
      fix exa
      assume "e = Throw exa"
      with prems have "extTA,P,t \<turnstile> \<langle>newA T\<lfloor>Throw exa\<rceil>,(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw exa,(h, l)\<rangle>"
	by - (rule NewArrayThrow)
      with prems show ?thesis by blast
    qed
  next
    assume "\<not> final e"
    with IH De have exes: "\<exists>e' s' ta. extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by simp
    then obtain e' s' ta where "extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by blast
    hence "extTA,P,t \<turnstile> \<langle>newA T\<lfloor>e\<rceil>,(h, l)\<rangle> -ta\<rightarrow> \<langle>newA T\<lfloor>e'\<rceil>,s'\<rangle>" by - (rule NewArrayRed)
    thus ?thesis by blast
  qed
next
  case (WTrtCast E e T U l)
  have wte: "P,E,h \<turnstile> e : T"
   and IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
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
	with prems have "extTA,P,t \<turnstile> \<langle>Cast U (Val v),(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v,(h,l)\<rangle>"
	  by - (rule RedCast, auto)
	with ev show ?thesis by blast
      next
	assume "\<not> P \<turnstile> V \<le> U"
	with prems have "extTA,P,t \<turnstile> \<langle>Cast U (Val v),(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ClassCast,(h,l)\<rangle>"
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
  case (WTrtInstanceOf E e T U l)
  have wte: "P,E,h \<turnstile> e : T"
   and IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and D: "\<D> (e instanceof U) \<lfloor>dom l\<rfloor>" by fact+
  from D have De: "\<D> e \<lfloor>dom l\<rfloor>" by auto
  show ?case
  proof (cases "final e")
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v
      assume ev: "e = Val v"
      with prems obtain V where thvU: "typeof\<^bsub>h\<^esub> v = \<lfloor>V\<rfloor>" by fastsimp
      hence "extTA,P,t \<turnstile> \<langle>(Val v) instanceof U,(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>Val (Bool (v \<noteq> Null \<and> P \<turnstile> V \<le> U)),(h,l)\<rangle>"
        by -(rule RedInstanceOf, auto)
      with ev show ?thesis by blast
    next
      fix a
      assume "e = Throw a"
      thus ?thesis by(blast intro!:InstanceOfThrow)
    qed
  next
    assume nf: "\<not> final e"
    from IH[OF De nf] show ?thesis by (blast intro:InstanceOfRed)
  qed
next
  case WTrtVal thus ?case by(simp add:final_iff)
next
  case WTrtVar thus ?case by(fastsimp intro:RedVar simp:hyper_isin_def)
next
  case (WTrtBinOp E e1 T1 e2 T2 bop T)
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
	  fix v2 assume [simp]: "e2 = Val v2"
	  with WTrtBinOp have "typeof\<^bsub>h\<^esub> v1 = \<lfloor>T1\<rfloor>" "typeof\<^bsub>h\<^esub> v2 = \<lfloor>T2\<rfloor>" by auto
	  from binop_progress[OF this `P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T`] obtain v
	    where "binop bop v1 v2 = \<lfloor>v\<rfloor>" by blast
	  thus ?thesis by(fastsimp intro: RedBinOp)
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
                 \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>a,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and IHi: "\<And>l. \<lbrakk>\<D> i \<lfloor>dom l\<rfloor>; \<not> final i\<rbrakk>
                 \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>i,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and D: "\<D> (a\<lfloor>i\<rceil>) \<lfloor>dom l\<rfloor>" by fact+
  have ref: "is_refT (T\<lfloor>\<rceil>)" by simp
  from D have Da: "\<D> a \<lfloor>dom l\<rfloor>" by simp
  show ?case
  proof (cases "final a")
    assume "final a"
    with wte ref show ?case
    proof (cases rule: finalRefE)
      case null
      thus ?thesis
      proof (cases "final i")
	assume "final i"
	thus ?thesis
	proof (rule finalE)
	  fix v
	  assume i: "i = Val v"
	  have "extTA,P,t \<turnstile> \<langle>null\<lfloor>Val v\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, (h,l)\<rangle>"
	    by(rule RedAAccNull)
	  with i null show ?thesis by blast
	next
	  fix ex
	  assume i: "i = Throw ex"
	  have "extTA,P,t \<turnstile> \<langle>null\<lfloor>Throw ex\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw ex, (h,l)\<rangle>"
	    by(rule AAccThrow2)
	  with i null show ?thesis by blast
	qed
      next
	assume "\<not> final i"
	from WTrtAAcc null show ?thesis
	  by simp
      qed
    next
      case (Array ad U)
      with wte have ty: "typeof_addr h ad = \<lfloor>Array U\<rfloor>" by auto
      thus ?thesis
      proof (cases "final i")
	assume "final i"
	thus ?thesis
	proof(rule finalE)
	  fix v
	  assume [simp]: "i = Val v"
	  with wtei have "typeof\<^bsub>h\<^esub> v = Some Integer" by fastsimp
	  hence "\<exists>i. v = Intg i" by fastsimp
	  then obtain i where [simp]: "v = Intg i" by blast
	  thus ?thesis
	  proof (cases "i <s 0 \<or> sint i \<ge> int (array_length h ad)")
            case True
	    from prems show ?thesis by (fastsimp intro: RedAAccBounds)
          next
            case False
            hence "nat (sint i) < array_length h ad"
              by(metis int_le_0_conv linorder_not_less nat_int.Rep_inverse' sint_0 transfer_int_nat_numerals(1) word_sless_alt zless_nat_conj)
            with ty have "P,h \<turnstile> ad@ACell (nat (sint i)) : U" by(auto intro!: addr_loc_type.intros)
            from heap_read_total[OF hconf this]
            obtain v where "heap_read h ad (ACell (nat (sint i))) v" by blast
            with False Array ty show ?thesis by(fastsimp intro: RedAAcc)
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
    qed simp
  next
    assume "\<not> final a"
    with prems Da show ?thesis by (fastsimp intro: AAccRed1)
  qed
next
  case (WTrtAAccNT E a i T l)
  have wte: "P,E,h \<turnstile> a : NT"
   and wtei: "P,E,h \<turnstile> i : Integer"
   and IHa: "\<And>l. \<lbrakk>\<D> a \<lfloor>dom l\<rfloor>; \<not> final a\<rbrakk>
                 \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>a,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and IHi: "\<And>l. \<lbrakk>\<D> i \<lfloor>dom l\<rfloor>; \<not> final i\<rbrakk>
                 \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>i,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact+
  have ref: "is_refT NT" by simp
  with prems have Da: "\<D> a \<lfloor>dom l\<rfloor>" by simp
  thus ?case
  proof (cases "final a")
    case True
    with wte ref show ?thesis
    proof (cases rule: finalRefE)
      case null
      thus ?thesis
      proof (cases "final i")
	assume "final i"
	thus ?thesis
	proof (rule finalE)
	  fix v
	  assume "i = Val v"
	  have "extTA,P,t \<turnstile> \<langle>null\<lfloor>Val v\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, (h,l)\<rangle>"
	    by (rule RedAAccNull)
	  with prems show ?thesis by blast
	next
	  fix ex
	  assume "i = Throw ex"
	  have "extTA,P,t \<turnstile> \<langle>null\<lfloor>Throw ex\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw ex, (h,l)\<rangle>"
	    by(rule AAccThrow2)
	  with prems show ?thesis by blast
	qed
      next
	assume "\<not> final i"
	from prems show ?thesis
	  by(fastsimp intro: AAccRed2)
      qed
    next
      case Throw thus ?thesis by (fastsimp intro: AAccThrow1)
    qed simp_all
  next
    case False
    with prems Da show ?thesis by (fastsimp intro:AAccRed1)
  qed
next
  case (WTrtAAss E a T i e T' l)
  have wta: "P,E,h \<turnstile> a : T\<lfloor>\<rceil>"
    and wti: "P,E,h \<turnstile> i : Integer"
    and wte: "P,E,h \<turnstile> e : T'"
    and D: "\<D> (a\<lfloor>i\<rceil> := e) \<lfloor>dom l\<rfloor>"
    and IH1: "\<And>l. \<lbrakk>\<D> a \<lfloor>dom l\<rfloor>; \<not> final a\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>a,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
    and IH2: "\<And>l. \<lbrakk>\<D> i \<lfloor>dom l\<rfloor>; \<not> final i\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>i,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
    and IH3: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact+
  have ref: "is_refT (T\<lfloor>\<rceil>)" by simp
  show ?case
  proof (cases "final a")
    assume fa: "final a"
    with wta ref show ?thesis
    proof(cases rule: finalRefE)
      case null
      show ?thesis
      proof(cases "final i")
	assume "final i"
	thus ?thesis
	proof (rule finalE)
	  fix v
	  assume "i = Val v"
	  with wti have "typeof\<^bsub>h\<^esub> v = Some Integer" by fastsimp
	  hence "\<exists>idx. v = Intg idx" by fastsimp
	  then obtain idx where "v = Intg idx" by blast
	  thus ?thesis
	  proof (cases "final e")
	    assume "final e"
	    thus ?thesis
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
      case (Array ad U)
      with wta have ty: "typeof_addr h ad = \<lfloor>Array U\<rfloor>" by auto
      thus ?thesis
      proof (cases "final i")
	assume fi: "final i"
	thus ?thesis
	proof (rule finalE)
	  fix v
	  assume ivalv: "i = Val v"
	  with wti have "typeof\<^bsub>h\<^esub> v = Some Integer" by fastsimp
	  hence "\<exists>idx. v = Intg idx" by fastsimp
	  then obtain idx where vidx: "v = Intg idx" by blast
	  thus ?thesis
	  proof (cases "final e")
	    assume fe: "final e"
	    thus ?thesis
	    proof(rule finalE)
	      fix w
	      assume evalw: "e = Val w"
	      show ?thesis
              proof(cases "idx <s 0 \<or> sint idx \<ge> int (array_length h ad)")
                case True
                with ty evalw Array ivalv vidx show ?thesis by(fastsimp intro: RedAAssBounds)
              next
                case False
                hence "nat (sint idx) < array_length h ad"
                  by(metis int_le_0_conv linorder_not_less nat_int.Rep_inverse' sint_0 transfer_int_nat_numerals(1) word_sless_alt zless_nat_conj)
                with ty have "P,h \<turnstile> ad@ACell (nat (sint idx)) : U"
                  by(auto intro!: addr_loc_type.intros)
                from heap_write_total[OF this, of w]
                obtain h' where h': "heap_write h ad (ACell (nat (sint idx))) w h'" ..
                with ty False vidx ivalv evalw Array wte
                show ?thesis
                  by(cases "P \<turnstile> T' \<le> U")(fastsimp intro: RedAAss RedAAssStore)+
              qed
	    next
	      fix ex
	      assume "e = Throw ex"
	      with prems show ?thesis by (fastsimp intro: AAssThrow3)
	    qed
	  next
	    assume "\<not> final e"
	    from prems show ?thesis by (fastsimp intro: AAssRed3)
	  qed
	next
	  fix ex
	  assume "i = Throw ex"
	  from prems show ?thesis by (fastsimp intro: AAssThrow2)
	qed
      next
	assume "\<not> final i"
	from prems show ?thesis by (fastsimp intro: AAssRed2)
      qed
    next
      fix ex
      assume "a = Throw ex"
      from prems show ?thesis by (fastsimp intro:AAssThrow1)
    qed simp_all
  next
    assume "\<not> final a"
    from prems show ?thesis by (fastsimp intro: AAssRed1)
  qed
next
  case (WTrtAAssNT E a i e T' l)
  have wta: "P,E,h \<turnstile> a : NT"
    and wti: "P,E,h \<turnstile> i : Integer"
    and wte: "P,E,h \<turnstile> e : T'"
    and D: "\<D> (a\<lfloor>i\<rceil> := e) \<lfloor>dom l\<rfloor>"
    and IH1: "\<And>l. \<lbrakk>\<D> a \<lfloor>dom l\<rfloor>; \<not> final a\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>a,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
    and IH2: "\<And>l. \<lbrakk>\<D> i \<lfloor>dom l\<rfloor>; \<not> final i\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>i,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
    and IH3: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact+
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
  case (WTrtALength E a T l)
  show ?case
  proof(cases "final a")
    case True
    note wta = `P,E,h \<turnstile> a : T\<lfloor>\<rceil>`
    thus ?thesis 
    proof(rule finalRefE[OF _ _ True])
      show "is_refT (T\<lfloor>\<rceil>)" by simp
    next
      assume "a = null"
      thus ?thesis by(fastsimp intro: RedALengthNull)
    next
      fix ad U
      assume "a = addr ad" and "T\<lfloor>\<rceil> = U\<lfloor>\<rceil>"
      with wta show ?thesis by(fastsimp intro: RedALength)
    next
      fix ad
      assume "a = Throw ad"
      thus ?thesis by (fastsimp intro: ALengthThrow)
    qed simp
  next
    case False
    from `\<D> (a\<bullet>length) \<lfloor>dom l\<rfloor>` have "\<D> a \<lfloor>dom l\<rfloor>" by simp
    with False `\<lbrakk>\<D> a \<lfloor>dom l\<rfloor>; \<not> final a\<rbrakk> \<Longrightarrow> \<exists>e' s' ta. extTA,P,t \<turnstile> \<langle>a,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
    obtain e' s' ta where "extTA,P,t \<turnstile> \<langle>a,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by blast
    thus ?thesis by(blast intro: ALengthRed)
  qed
next
  case (WTrtALengthNT E a T l)
  show ?case
  proof(cases "final a")
    case True
    note wta = `P,E,h \<turnstile> a : NT`
    thus ?thesis
    proof(rule finalRefE[OF _ _ True])
      show "is_refT NT" by simp
    next
      assume "a = null"
      thus ?thesis by(blast intro: RedALengthNull)
    next
      fix ad
      assume "a = Throw ad"
      thus ?thesis by(blast intro: ALengthThrow)
    qed simp_all
  next
    case False
    from `\<D> (a\<bullet>length) \<lfloor>dom l\<rfloor>` have "\<D> a \<lfloor>dom l\<rfloor>" by simp
    with False `\<lbrakk>\<D> a \<lfloor>dom l\<rfloor>; \<not> final a\<rbrakk> \<Longrightarrow> \<exists>e' s' ta. extTA,P,t \<turnstile> \<langle>a,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
    obtain e' s' ta where "extTA,P,t \<turnstile> \<langle>a,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by blast
    thus ?thesis by(blast intro: ALengthRed)
  qed
next
  case (WTrtFAcc E e C F T D l)
  have wte: "P,E,h \<turnstile> e : Class C"
   and field: "P \<turnstile> C has F:T in D" by fact+
  show ?case
  proof cases
    assume "final e"
    with wte show ?thesis
    proof (cases rule: final_addrE)
      case (addr a)
      with wte have ty: "typeof_addr h a = \<lfloor>Class C\<rfloor>" by auto
      with field have "P,h \<turnstile> a@CField D F : T" by(auto intro: addr_loc_type.intros)
      from heap_read_total[OF hconf this]
      obtain v where "heap_read h a (CField D F) v" by blast
      with addr ty show ?thesis by(fastsimp intro: RedFAcc)
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
  have wte1: "P,E,h \<turnstile> e1 : Class C"
    and field: "P \<turnstile> C has F:T in D" by fact+
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
	  fix v assume e2: "e2 = Val v"
          from wte1 field e1 have "P,h \<turnstile> a@CField D F : T"
            by(auto intro: addr_loc_type.intros)
          from heap_write_total[OF this, of v] obtain h' 
            where "heap_write h a (CField D F) v h'" ..
          with wte1 field e1 e2 show ?thesis
	    by(fastsimp intro: RedFAss)
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
             \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact
  have sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D" by fact
  have nexc: "\<not> is_external_call P (Class C) M" by fact
  have wtes: "P,E,h \<turnstile> es [:] Ts'" by fact
  have IHes: "\<And>l. \<lbrakk>\<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es\<rbrakk> \<Longrightarrow> \<exists>es' s' ta. extTA,P,t \<turnstile> \<langle>es,(h, l)\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>" by fact
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
	from wte e_addr have ha: "typeof_addr h a = \<lfloor>Class C\<rfloor>"  by(auto)
	have "length es = length Ts'" using wtes by(auto simp add: WTrts_conv_list_all2 dest: list_all2_lengthD)
	moreover from subtype have "length Ts' = length Ts" by(auto dest: list_all2_lengthD)
	ultimately have esTs: "length es = length Ts" by(auto)
	thus ?thesis using e_addr ha sees subtype es sees_wf_mdecl[OF wf sees] nexc
	  by (fastsimp intro!: RedCall simp:list_all2_def wf_mdecl_def)
      next
	assume "\<not>(\<exists>vs. es = map Val vs)"
	hence not_all_Val: "\<not>(\<forall>e \<in> set es. \<exists>v. e = Val v)"
	  by(simp add:ex_map_conv)
	let ?ves = "takeWhile (\<lambda>e. \<exists>v. e = Val v) es"
        let ?rest = "dropWhile (\<lambda>e. \<exists>v. e = Val v) es"
	let ?ex = "hd ?rest" let ?rst = "tl ?rest"
	from not_all_Val have nonempty: "?rest \<noteq> []" by auto
	hence es: "es = ?ves @ ?ex # ?rst" by simp
	have "\<forall>e \<in> set ?ves. \<exists>v. e = Val v" by(fastsimp dest:set_takeWhileD)
	then obtain vs where ves: "?ves = map Val vs"
	  using ex_map_conv by blast
	show ?thesis
	proof cases
	  assume "final ?ex"
	  moreover from nonempty have "\<not>(\<exists>v. ?ex = Val v)"
	    by(auto simp:neq_Nil_conv simp del:dropWhile_eq_Nil_conv)
              (simp add:dropWhile_eq_Cons_conv)
	  ultimately obtain b where ex_Throw: "?ex = Throw b"
	    by(fast elim!:finalE)
	  show ?thesis using e_addr es ex_Throw ves
	    by(fastsimp intro:CallThrowParams)
	next
	  assume not_fin: "\<not> final ?ex"
	  have "finals es = finals(?ves @ ?ex # ?rst)" using es
	    by(rule arg_cong)
	  also have "\<dots> = finals(?ex # ?rst)" using ves by simp
	  finally have "finals es = finals(?ex # ?rst)" .
	  hence "\<not> finals es" using not_finals_ConsI[OF not_fin] by blast
	  thus ?thesis using e_addr dae IHes  by(fastsimp intro!:CallParams)
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
             \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"  by fact
  have IHes: "\<And>l. \<lbrakk>\<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es\<rbrakk> \<Longrightarrow> \<exists>es' s' ta. extTA,P,t \<turnstile> \<langle>es,(h, l)\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>" by fact
  have wtes: "P,E,h \<turnstile> es [:] Ts" by fact
  have dae: "\<D> (e\<bullet>M(es)) \<lfloor>dom l\<rfloor>" by fact
  show ?case
  proof(cases "final e")
    assume "final e"
    moreover
    { fix v assume "e = Val v"
      hence "e = null" using prems by simp
      have ?case
      proof cases
	assume "finals es"
	moreover
	{ fix vs assume "es = map Val vs"
	  from prems have ?thesis by(fastsimp intro: RedCallNull) }
	moreover
	{ fix vs a es' assume "es = map Val vs @ Throw a # es'"
	  from prems have ?thesis by(fastsimp intro: CallThrowParams) }
	ultimately show ?thesis by(fastsimp simp:finals_def)
      next
	assume "\<not> finals es" --"@{term es} reduces by IH"
	from prems show ?thesis by(fastsimp intro: CallParams)
      qed
    }
    moreover
    { fix a assume "e = Throw a"
      from prems have ?case by(fastsimp intro: CallThrowObj) }
    ultimately show ?thesis by(fastsimp simp:final_iff)
  next
    assume "\<not> final e" --"@{term e} reduces by IH"
    from prems show ?thesis by (fastsimp intro:CallObj)
  qed
next
  case (WTrtCallExternal E e T es Ts M Ts' U l)
  have wte: "P,E,h \<turnstile> e : T" by fact
  have IHe: "\<And>l. \<lbrakk> \<D> e \<lfloor>dom l\<rfloor>; \<not> final e \<rbrakk>
             \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact
  have wtes: "P,E,h \<turnstile> es [:] Ts" by fact
  have IHes: "\<And>l. \<lbrakk>\<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es\<rbrakk> \<Longrightarrow> \<exists>es' s' ta. extTA,P,t \<turnstile> \<langle>es,(h, l)\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>" by fact
  have wtext: "P \<turnstile> T\<bullet>M(Ts') :: U" by fact
  have dae: "\<D> (e\<bullet>M(es)) \<lfloor>dom l\<rfloor>" by fact
  show ?case
  proof(cases "final e")
    assume fine: "final e"
    from wtext have "T \<noteq> NT" by(rule external_WT_not_NT)
    with is_external_call_is_refT[OF external_WT_is_external_call[OF wtext]] fine wte
    obtain a where e: "e = addr a \<or> e = Throw a" 
      by -(rule finalRefE, auto)
    thus ?thesis
    proof
      assume e: "e = addr a"
      from e wte have tya: "typeof_addr h a = \<lfloor>T\<rfloor>" by simp
      show ?thesis
      proof(cases "finals es")
	case True
	hence "(\<exists>vs. es = map Val vs) \<or> (\<exists>vs a es'. es = map Val vs @ Throw a # es')" unfolding finals_def .
	thus ?thesis
	proof
	  assume "\<exists>vs. es = map Val vs"
	  then obtain vs where es: "es = map Val vs" ..
	  with wtes have tyes: "map typeof\<^bsub>h\<^esub> vs = map Some Ts" by simp
	  with tya have "P,h \<turnstile> a\<bullet>M(vs) : U" using wtext `P \<turnstile> Ts [\<le>] Ts'` by(rule external_WT'.intros)
          from external_call_progress[OF wf this hconf] obtain ta va h'
	    where "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>" by blast
	  thus ?thesis using tya external_WT_is_external_call[OF wtext] e es
	    by(fastsimp intro: RedCallExternal simp del: split_paired_Ex)
	next
	  assume "\<exists>vs a es'. es = map Val vs @ Throw a # es'"
	  with e show ?thesis by(auto intro: CallThrowParams simp del: split_paired_Ex)
	qed
      next
	case False
	from dae IHes[OF _ this, of l] e show ?thesis by(fastsimp intro!: CallParams)
      qed
    next
      assume "e = Throw a"
      thus ?thesis by(auto intro: CallThrowObj simp del: split_paired_Ex)
    qed
  next
    case False
    with dae IHe[OF _ False, of l] show ?thesis by(fastsimp intro: CallObj)
  qed
next
  case (WTrtInitBlock v T1 T E V e2 T2 l)
  have IH2: "\<And>l.  \<lbrakk>\<D> e2 \<lfloor>dom l\<rfloor>; \<not> final e2\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e2,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and D: "\<D> {V:T=\<lfloor>v\<rfloor>; e2} \<lfloor>dom l\<rfloor>" by fact+
  show ?case
  proof cases
    assume "final e2"
    thus ?thesis
    proof (rule finalE)
      fix v\<^isub>2 assume "e2 = Val v\<^isub>2"
      thus ?thesis by(fast intro:RedBlock)
    next
      fix a assume "e2 = Throw a"
      thus ?thesis by(fast intro:BlockThrow)
    qed
  next
    assume not_fin2: "\<not> final e2"
    from D have D2: "\<D> e2 \<lfloor>dom(l(V\<mapsto>v))\<rfloor>" by (auto simp:hyperset_defs)
    from IH2[OF D2 not_fin2]
    obtain h' l' e' tas where red2: "extTA,P,t \<turnstile> \<langle>e2,(h, l(V\<mapsto>v))\<rangle> -tas\<rightarrow> \<langle>e',(h', l')\<rangle>"
      by fast
    from red_lcl_incr[OF red2] have "V \<in> dom l'" by auto
    with red2 show ?thesis by(fastsimp intro:BlockRed)
  qed
next
  case (WTrtBlock E V T e T' l)
  have IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                 \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and D: "\<D> {V:T=None; e} \<lfloor>dom l\<rfloor>" by fact+
  show ?case
  proof cases
    assume "final e"
    thus ?thesis
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
    obtain h' l' e' tas where red: "extTA,P,t \<turnstile> \<langle>e,(h,l(V:=None))\<rangle> -tas\<rightarrow> \<langle>e',(h',l')\<rangle>"
      by auto
    thus ?thesis by(blast intro: BlockRed)
  qed
next
  case (WTrtSynchronized E o' T e T' l)
  note wto = `P,E,h \<turnstile> o' : T`
  note IHe = `\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e \<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>`
  note wte = `P,E,h \<turnstile> e : T'`
  note IHo = `\<And>l. \<lbrakk>\<D> o' \<lfloor>dom l\<rfloor>; \<not> final o' \<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>o',(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>`
  note refT = `is_refT T`
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
	thus ?thesis using oval 
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
  case (WTrtInSynchronized E a T e T' l)
  show ?case
  proof(cases "final e")
    case True thus ?thesis
      by(fastsimp elim!: finalE intro: UnlockSynchronized SynchronizedThrow2)
  next
    case False 
    moreover from `\<D> (insync(a) e) \<lfloor>dom l\<rfloor>` have "\<D> e \<lfloor>dom l\<rfloor>" by simp
    moreover note IHe = `\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>`
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
      with `P \<turnstile> T \<le> Class Throwable` `\<not> final (throw e)` `P,E,h \<turnstile> e : T`
      have "v = Null" by(cases v)(auto simp add: final_iff widen_Class)
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
      with wt1 obtain D where ha: "typeof_addr h a = \<lfloor>Class D\<rfloor>"
	by(auto simp add: widen_Class dest: typeof_addr_eq_Some_conv)
      thus ?thesis using e1_Throw
        by(cases "P \<turnstile> D \<preceq>\<^sup>* C")(fastsimp intro:RedTryCatch RedTryFail)+
    qed
  next
    assume "\<not> final e1"
    show ?thesis using prems by simp (fast intro:TryRed)
  qed
next
  case WTrtNil thus ?case by simp
next
  case (WTrtCons E e T es Ts)
  have IHe: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                \<Longrightarrow> \<exists>e' s' ta. extTA,P,t \<turnstile> \<langle>e,(h,l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>"
   and IHes: "\<And>l. \<lbrakk>\<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es\<rbrakk>
             \<Longrightarrow> \<exists>es' s' ta. extTA,P,t \<turnstile> \<langle>es,(h,l)\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>"
   and D: "\<D>s (e#es) \<lfloor>dom l\<rfloor>" and not_fins: "\<not> finals(e # es)" by fact+
  have De: "\<D> e \<lfloor>dom l\<rfloor>" and Des: "\<D>s es (\<lfloor>dom l\<rfloor> \<squnion> \<A> e)"
    using D by auto
  show ?case
  proof cases
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v assume e: "e = Val v"
      hence Des': "\<D>s es \<lfloor>dom l\<rfloor>" using De Des by auto
      have not_fins_tl: "\<not> finals es" using not_fins e by simp
      show ?thesis using e IHes[OF Des' not_fins_tl]
	by (blast intro!:ListRed2)
    next
      fix a assume "e = Throw a"
      hence False using not_fins by simp
      thus ?thesis ..
    qed
  next
    assume "\<not> final e"
    with IHe[OF De] show ?thesis by(fast intro!:ListRed1)
  qed
qed

end

end