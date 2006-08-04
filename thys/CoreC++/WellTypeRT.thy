(*  Title:       CoreC++
    ID:          $Id: WellTypeRT.thy,v 1.7 2006-08-04 10:56:50 wasserra Exp $
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Based on the Jinja theory J/WellTypeRT.thy by Tobias Nipkow 
*)


header {* \isaheader{Runtime Well-typedness} *}

theory WellTypeRT imports WellType begin


section {* Run time types *}

consts
  typeof_h :: "prog \<Rightarrow> heap \<Rightarrow> val \<Rightarrow> ty option" ("_ \<turnstile> typeof\<^bsub>_\<^esub>")

primrec
  "P \<turnstile> typeof\<^bsub>h\<^esub> Unit     = Some Void"
  "P \<turnstile> typeof\<^bsub>h\<^esub> Null     = Some NT"
  "P \<turnstile> typeof\<^bsub>h\<^esub> (Bool b) = Some Boolean"
  "P \<turnstile> typeof\<^bsub>h\<^esub> (Intg i) = Some Integer"
  "P \<turnstile> typeof\<^bsub>h\<^esub> (Ref r)  = (case h (the_addr (Ref r)) of None \<Rightarrow> None 
                            | Some(C,S) \<Rightarrow> (if (C,the_path(Ref r)) \<in> Subobjs P then
                                   Some(Class(last(the_path(Ref r))))
                                            else None))"


lemma type_eq_type: "typeof v = Some T \<Longrightarrow> P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T"
by(induct v)auto

lemma typeof_Void [simp]: "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some Void \<Longrightarrow> v = Unit"
by(induct v,auto split:split_if_asm)

lemma typeof_NT [simp]: "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some NT \<Longrightarrow> v = Null"
by(induct v,auto split:split_if_asm)

lemma typeof_Boolean [simp]: "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some Boolean \<Longrightarrow> \<exists>b. v = Bool b"
by(induct v,auto split:split_if_asm)

lemma typeof_Integer [simp]: "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some Integer \<Longrightarrow> \<exists>i. v = Intg i"
by(induct v,auto split:split_if_asm)

lemma typeof_Class_Subo: 
"P \<turnstile> typeof\<^bsub>h\<^esub> v = Some (Class C) \<Longrightarrow> 
\<exists>a Cs D S. v = Ref(a,Cs) \<and> h a = Some(D,S) \<and> (D,Cs) \<in> Subobjs P \<and> last Cs = C"
by(induct v,auto split:split_if_asm)

section {* The rules *}

consts
  WTrt :: "prog \<Rightarrow> (env \<times> heap \<times> expr      \<times> ty     )set"
  WTrts:: "prog \<Rightarrow> (env \<times> heap \<times> expr list \<times> ty list)set"


syntax (xsymbols)
  WTrt :: "[prog,env,heap,expr,     ty     ] \<Rightarrow> bool"
        ("_,_,_ \<turnstile> _ : _"   [51,51,51]50)
  WTrts:: "[prog,env,heap,expr list,ty list] \<Rightarrow> bool"
        ("_,_,_ \<turnstile> _ [:] _" [51,51,51]50)


translations
  "P,E,h \<turnstile> e : T"  ==  "(E,h,e,T) \<in> WTrt P"
  "P,E,h \<turnstile> es [:] Ts"  ==  "(E,h,es,Ts) \<in> WTrts P"

inductive "WTrt P" "WTrts P"
intros
  
WTrtNew:
  "is_class P C  \<Longrightarrow> 
  P,E,h \<turnstile> new C : Class C"

WTrtDynCast:
  "\<lbrakk> P,E,h \<turnstile> e : T; is_refT T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> Cast C e : Class C"

WTrtStaticCast:
  "\<lbrakk> P,E,h \<turnstile> e : T; is_refT T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> \<lparr>C\<rparr>e : Class C"

WTrtVal:
  "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow>
  P,E,h \<turnstile> Val v : T"

WTrtVar:
  "E V = Some T \<Longrightarrow>
  P,E,h \<turnstile> Var V : T"

WTrtBinOp:
  "\<lbrakk> P,E,h \<turnstile> e\<^isub>1 : T\<^isub>1;  P,E,h \<turnstile> e\<^isub>2 : T\<^isub>2;
     case bop of Eq \<Rightarrow> T = Boolean
               | Add \<Rightarrow> T\<^isub>1 = Integer \<and> T\<^isub>2 = Integer \<and> T = Integer \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 : T"

WTrtLAss:
  "\<lbrakk> E V = Some T;  P,E,h \<turnstile> e : T'; P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> V:=e : T"

WTrtFAcc:
"\<lbrakk>P,E,h \<turnstile> e : Class C; Cs \<noteq> []; P \<turnstile> C has least F:T via Cs \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<bullet>F{Cs} : T"

WTrtFAccNT:
  "P,E,h \<turnstile> e : NT \<Longrightarrow> P,E,h \<turnstile> e\<bullet>F{Cs} : T"

WTrtFAss:
"\<lbrakk>P,E,h \<turnstile> e\<^isub>1 : Class C; Cs \<noteq> [];
  P \<turnstile> C has least F:T via Cs; P,E,h \<turnstile> e\<^isub>2 : T'; P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<^isub>1\<bullet>F{Cs}:=e\<^isub>2 : T"

WTrtFAssNT:
  "\<lbrakk> P,E,h \<turnstile> e\<^isub>1 : NT; P,E,h \<turnstile> e\<^isub>2 : T'; P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<^isub>1\<bullet>F{Cs}:=e\<^isub>2 : T"

WTrtCall:
  "\<lbrakk> P,E,h \<turnstile> e : Class C;  P \<turnstile> C has least M = (Ts,T,m) via Cs;
     P,E,h \<turnstile> es [:] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<bullet>M(es) : T" 

WTrtCallNT:
  "\<lbrakk>P,E,h \<turnstile> e : NT; P,E,h \<turnstile> es [:] Ts\<rbrakk> \<Longrightarrow> P,E,h \<turnstile> e\<bullet>M(es) : T"

WTrtBlock:
  "\<lbrakk>P,E(V\<mapsto>T),h \<turnstile> e : T'; is_type P T\<rbrakk> \<Longrightarrow> 
  P,E,h \<turnstile> {V:T; e} : T'"

WTrtSeq:
  "\<lbrakk> P,E,h \<turnstile> e\<^isub>1 : T\<^isub>1;  P,E,h \<turnstile> e\<^isub>2 : T\<^isub>2 \<rbrakk>  \<Longrightarrow>  P,E,h \<turnstile> e\<^isub>1;;e\<^isub>2 : T\<^isub>2"

WTrtCond:
  "\<lbrakk> P,E,h \<turnstile> e : Boolean;  P,E,h \<turnstile> e\<^isub>1 : T;  P,E,h \<turnstile> e\<^isub>2 : T \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> if (e) e\<^isub>1 else e\<^isub>2 : T"

WTrtWhile:
  "\<lbrakk> P,E,h \<turnstile> e : Boolean;  P,E,h \<turnstile> c : T \<rbrakk>
  \<Longrightarrow>  P,E,h \<turnstile> while(e) c : Void"

WTrtThrow:
  "\<lbrakk>P,E,h \<turnstile> e : T'; is_refT T'\<rbrakk>  
 \<Longrightarrow>  P,E,h \<turnstile> throw e : T"


WTrtNil:
"P,E,h \<turnstile> [] [:] []"

WTrtCons:
 "\<lbrakk> P,E,h \<turnstile> e : T;  P,E,h \<turnstile> es [:] Ts \<rbrakk> \<Longrightarrow>  P,E,h \<turnstile> e#es [:] T#Ts"




declare
  WTrt_WTrts.intros[intro!]
  WTrtNil[iff]
declare
  WTrtFAcc[rule del] WTrtFAccNT[rule del]
  WTrtFAss[rule del] WTrtFAssNT[rule del]
  WTrtCall[rule del] WTrtCallNT[rule del]

lemmas WTrt_induct = WTrt_WTrts.induct [split_format (complete)]
  and WTrt_inducts = WTrt_WTrts.inducts [split_format (complete)]


section{*Easy consequences*}

lemma [iff]: "(P,E,h \<turnstile> [] [:] Ts) = (Ts = [])"

apply(rule iffI)
apply (auto elim: WTrt_WTrts.elims)
done


lemma [iff]: "(P,E,h \<turnstile> e#es [:] T#Ts) = (P,E,h \<turnstile> e : T \<and> P,E,h \<turnstile> es [:] Ts)"

apply(rule iffI)
apply (auto elim: WTrt_WTrts.elims)
done


lemma [iff]: "(P,E,h \<turnstile> (e#es) [:] Ts) =
  (\<exists>U Us. Ts = U#Us \<and> P,E,h \<turnstile> e : U \<and> P,E,h \<turnstile> es [:] Us)"

apply(rule iffI)
apply (auto elim: WTrt_WTrts.elims)
done


lemma [simp]: "\<forall>Ts. (P,E,h \<turnstile> es\<^isub>1 @ es\<^isub>2 [:] Ts) =
  (\<exists>Ts\<^isub>1 Ts\<^isub>2. Ts = Ts\<^isub>1 @ Ts\<^isub>2 \<and> P,E,h \<turnstile> es\<^isub>1 [:] Ts\<^isub>1 & P,E,h \<turnstile> es\<^isub>2 [:] Ts\<^isub>2)"

apply(induct_tac es\<^isub>1)
 apply simp
apply clarsimp
apply(erule thin_rl)
apply (rule iffI)
 apply clarsimp
 apply(rule exI)+
 apply(rule conjI)
  prefer 2 apply blast
 apply simp
apply fastsimp
done


lemma [iff]: "P,E,h \<turnstile> Val v : T = (P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T)"

apply(rule iffI)
apply (auto elim: WTrt_WTrts.elims)
done


lemma [iff]: "P,E,h \<turnstile> Var V : T = (E V = Some T)"

apply(rule iffI)
apply (auto elim: WTrt_WTrts.elims)
done


lemma [iff]: "P,E,h \<turnstile> e\<^isub>1;;e\<^isub>2 : T\<^isub>2 = (\<exists>T\<^isub>1. P,E,h \<turnstile> e\<^isub>1:T\<^isub>1 \<and> P,E,h \<turnstile> e\<^isub>2:T\<^isub>2)"

apply(rule iffI)
apply (auto elim: WTrt_WTrts.elims)
done


lemma [iff]: "P,E,h \<turnstile> {V:T; e} : T'  =  (P,E(V\<mapsto>T),h \<turnstile> e : T' \<and> is_type P T)"

apply(rule iffI)
apply (auto elim: WTrt_WTrts.elims)
done



inductive_cases WTrt_elim_cases[elim!]:
  "P,E,h \<turnstile> new C : T"
  "P,E,h \<turnstile> Cast C e : T"
  "P,E,h \<turnstile> \<lparr>C\<rparr>e : T"
  "P,E,h \<turnstile> e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 : T"
  "P,E,h \<turnstile> V:=e : T"
  "P,E,h \<turnstile> e\<bullet>F{Cs} : T"
  "P,E,h \<turnstile> e\<bullet>F{Cs} := v : T"
  "P,E,h \<turnstile> e\<bullet>M(es) : T"
  "P,E,h \<turnstile> if (e) e\<^isub>1 else e\<^isub>2 : T"
  "P,E,h \<turnstile> while(e) c : T"
  "P,E,h \<turnstile> throw e : T"


section{*Some interesting lemmas*}


lemma WTrts_Val[simp]:
 "\<And>Ts. (P,E,h \<turnstile> map Val vs [:] Ts) = (map (\<lambda>v. (P \<turnstile> typeof\<^bsub>h\<^esub>) v) vs = map Some Ts)"

apply(induct vs)
 apply fastsimp
apply(case_tac Ts)
 apply simp
apply simp
done



lemma WTrts_same_length: "\<And>Ts. P,E,h \<turnstile> es [:] Ts \<Longrightarrow> length es = length Ts"
by(induct es type:list)auto


lemma WTrt_env_mono:
  "P,E,h \<turnstile> e : T \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E',h \<turnstile> e : T)" and
  "P,E,h \<turnstile> es [:] Ts \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E',h \<turnstile> es [:] Ts)"

apply(induct rule: WTrt_inducts)
apply(simp add: WTrtNew)
apply(fastsimp simp: WTrtDynCast)
apply(fastsimp simp: WTrtStaticCast)
apply(fastsimp simp: WTrtVal)
apply(simp add: WTrtVar map_le_def dom_def)
apply(fastsimp simp add: WTrtBinOp)
apply (force simp:map_le_def)
apply(fastsimp simp: WTrtFAcc)
apply(simp add: WTrtFAccNT)
apply(fastsimp simp: WTrtFAss)
apply(fastsimp simp: WTrtFAssNT)
apply(fastsimp simp: WTrtCall)
apply(fastsimp simp: WTrtCallNT)
apply(fastsimp simp: map_le_def)
apply(fastsimp)
apply(fastsimp simp: WTrtCond)
apply(fastsimp simp: WTrtWhile)
apply(fastsimp simp: WTrtThrow)
apply(simp add: WTrtNil)
apply(simp add: WTrtCons)
done


lemma WT_implies_WTrt: "P,E \<turnstile> e :: T \<Longrightarrow> P,E,h \<turnstile> e : T"
and WTs_implies_WTrts: "P,E \<turnstile> es [::] Ts \<Longrightarrow> P,E,h \<turnstile> es [:] Ts"

proof(induct rule: WT_WTs_inducts)
  case WTVal thus ?case by (fastsimp dest:type_eq_type)
next
  case WTBinOp thus ?case by (fastsimp split:bop.splits)
next
  case WTFAcc thus ?case
    by(fastsimp intro!:WTrtFAcc dest:Subobjs_nonempty 
                  simp:LeastFieldDecl_def FieldDecls_def)
next
  case WTFAss thus ?case
    by(fastsimp intro!:WTrtFAss dest:Subobjs_nonempty
                  simp:LeastFieldDecl_def FieldDecls_def)
next
  case WTCall thus ?case by (fastsimp intro:WTrtCall)
qed (auto simp del:fun_upd_apply)


end
