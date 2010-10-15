(*  Title:      Jinja/J/Annotate.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Program annotation} *}

theory Annotate imports
  WellType_Exec
begin

abbreviation (output)
  unanFAcc :: "expr \<Rightarrow> vname \<Rightarrow> expr" ("(_\<bullet>_)" [10,10] 90)
where
  "unanFAcc e F \<equiv> FAcc e F (STR [])"

abbreviation (output)
  unanFAss :: "expr \<Rightarrow> vname \<Rightarrow> expr \<Rightarrow> expr" ("(_\<bullet>_ := _)" [10,0,90] 90)
where
  "unanFAss e F e' \<equiv> FAss e F (STR []) e'"

definition array_length_field_name :: vname
where "array_length_field_name = STR ''length''"

notation (output) array_length_field_name ("length")

definition super :: vname
where "super = STR ''super''"

lemma super_neq_this [simp]: "super \<noteq> this" "this \<noteq> super"
by(simp_all add: this_def super_def)

inductive Anno :: "J_prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> bool" ("_,_ \<turnstile> _ \<leadsto> _"   [51,0,0,51]50)
  and Annos :: "J_prog \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> bool" ("_,_ \<turnstile> _ [\<leadsto>] _" [51,0,0,51]50)
for P :: J_prog
where
  AnnoNew: "P,E \<turnstile> new C \<leadsto> new C"
| AnnoNewArray: "P,E \<turnstile> i \<leadsto> i' \<Longrightarrow> P,E \<turnstile> newA T\<lfloor>i\<rceil> \<leadsto> newA T\<lfloor>i'\<rceil>"
| AnnoCast: "P,E \<turnstile> e \<leadsto> e' \<Longrightarrow> P,E \<turnstile> Cast C e \<leadsto> Cast C e'"
| AnnoInstanceOf: "P,E \<turnstile> e \<leadsto> e' \<Longrightarrow> P,E \<turnstile> e instanceof T \<leadsto> e' instanceof T"
| AnnoVal: "P,E \<turnstile> Val v \<leadsto> Val v"
| AnnoVarVar: "\<lbrakk> E V = \<lfloor>T\<rfloor>; V \<noteq> super \<rbrakk> \<Longrightarrow> P,E \<turnstile> Var V \<leadsto> Var V"
| AnnoVarField:
  "\<lbrakk> E V = None; V \<noteq> super; E this = \<lfloor>Class C\<rfloor>; P \<turnstile> C sees V:T (fm) in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> Var V \<leadsto> Var this\<bullet>V{D}"
| AnnoBinOp:
  "\<lbrakk> P,E \<turnstile> e1 \<leadsto> e1';  P,E \<turnstile> e2 \<leadsto> e2' \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 \<leadsto> e1' \<guillemotleft>bop\<guillemotright> e2'"
| AnnoLAssVar:
  "\<lbrakk> E V = \<lfloor>T\<rfloor>; P,E \<turnstile> e \<leadsto> e' \<rbrakk> \<Longrightarrow> P,E \<turnstile> V:=e \<leadsto> V:=e'"
| AnnoLAssField:
  "\<lbrakk> E V = None; E this = \<lfloor>Class C\<rfloor>; P \<turnstile> C sees V:T (fm) in D; P,E \<turnstile> e \<leadsto> e' \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> V:=e \<leadsto> Var this\<bullet>V{D} := e'"
| AnnoAAcc:
  "\<lbrakk> P,E \<turnstile> a \<leadsto> a'; P,E \<turnstile> i \<leadsto> i' \<rbrakk> \<Longrightarrow> P,E \<turnstile> a\<lfloor>i\<rceil> \<leadsto> a'\<lfloor>i'\<rceil>"
| AnnoAAss:
  "\<lbrakk> P,E \<turnstile> a \<leadsto> a'; P,E \<turnstile> i \<leadsto> i'; P,E \<turnstile> e \<leadsto> e' \<rbrakk> \<Longrightarrow> P,E \<turnstile> a\<lfloor>i\<rceil> := e \<leadsto> a'\<lfloor>i'\<rceil> := e'"
| AnnoALength:
  "P,E \<turnstile> a \<leadsto> a' \<Longrightarrow> P,E \<turnstile> a\<bullet>length \<leadsto> a'\<bullet>length"
| AnnoFAcc:
  "\<lbrakk> P,E \<turnstile> e \<leadsto> e';  P,E \<turnstile> e' :: Class C;  P \<turnstile> C sees F:T (fm) in D \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> e\<bullet>F{STR []} \<leadsto> e'\<bullet>F{D}"
| AnnoFAccALength:
  "\<lbrakk> P,E \<turnstile> e \<leadsto> e'; P,E \<turnstile> e' :: T\<lfloor>\<rceil> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>array_length_field_name{STR []} \<leadsto> e'\<bullet>length"
| AnnoFAccSuper:
  -- {* In class C with super class D, "super" is syntactic sugar for "((D) this)" (cf. JLS, 15.11.2) *}
  "\<lbrakk> E this = \<lfloor>Class C\<rfloor>; C \<noteq> Object; class P C = \<lfloor>(D, fs, ms)\<rfloor>; 
     P \<turnstile> D sees F:T (fm) in D' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> Var super\<bullet>F{STR []} \<leadsto> (Cast (Class D) (Var this))\<bullet>F{D'}"
| AnnoFAss:
  "\<lbrakk> P,E \<turnstile> e1 \<leadsto> e1';  P,E \<turnstile> e2 \<leadsto> e2';
     P,E \<turnstile> e1' :: Class C; P \<turnstile> C sees F:T (fm) in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e1\<bullet>F{STR []} := e2 \<leadsto> e1'\<bullet>F{D} := e2'"
| AnnoFAssSuper:
  "\<lbrakk> E this = \<lfloor>Class C\<rfloor>; C \<noteq> Object; class P C = \<lfloor>(D, fs, ms)\<rfloor>;
     P \<turnstile> D sees F:T (fm) in D'; P,E \<turnstile> e \<leadsto> e' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> Var super\<bullet>F{STR []} := e \<leadsto> (Cast (Class D) (Var this))\<bullet>F{D'} := e'"
| AnnoCall:
  "\<lbrakk> P,E \<turnstile> e \<leadsto> e';  P,E \<turnstile> es [\<leadsto>] es' \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> Call e M es \<leadsto> Call e' M es'"
| AnnoBlock:
  "P,E(V \<mapsto> T) \<turnstile> e \<leadsto> e'  \<Longrightarrow>  P,E \<turnstile> {V:T=vo; e} \<leadsto> {V:T=vo; e'}"
| AnnoSync:
  "\<lbrakk> P,E \<turnstile> e1 \<leadsto> e1'; P,E \<turnstile> e2 \<leadsto> e2' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> sync(e1) e2 \<leadsto> sync(e1') e2'"
| AnnoComp:
  "\<lbrakk> P,E \<turnstile> e1 \<leadsto> e1';  P,E \<turnstile> e2 \<leadsto> e2' \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> e1;;e2 \<leadsto> e1';;e2'"
| AnnoCond:
  "\<lbrakk> P,E \<turnstile> e \<leadsto> e'; P,E \<turnstile> e1 \<leadsto> e1';  P,E \<turnstile> e2 \<leadsto> e2' \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> if (e) e1 else e2 \<leadsto> if (e') e1' else e2'"
| AnnoLoop:
  "\<lbrakk> P,E \<turnstile> e \<leadsto> e';  P,E \<turnstile> c \<leadsto> c' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> while (e) c \<leadsto> while (e') c'"
| AnnoThrow:
  "P,E \<turnstile> e \<leadsto> e' \<Longrightarrow> P,E \<turnstile> throw e \<leadsto> throw e'"
| AnnoTry:
  "\<lbrakk> P,E \<turnstile> e1 \<leadsto> e1';  P,E(V \<mapsto> Class C) \<turnstile> e2 \<leadsto> e2' \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> try e1 catch(C V) e2 \<leadsto> try e1' catch(C V) e2'"

| AnnoNil:
  "P,E \<turnstile> [] [\<leadsto>] []"
| AnnoCons:
  "\<lbrakk> P,E \<turnstile> e \<leadsto> e';  P,E \<turnstile> es [\<leadsto>] es' \<rbrakk> \<Longrightarrow>  P,E \<turnstile> e#es [\<leadsto>] e'#es'"

inductive_cases Anno_cases [elim!]:
  "P,E \<turnstile> new C \<leadsto> e"
  "P,E \<turnstile> newA T\<lfloor>e\<rceil> \<leadsto> e'"
  "P,E \<turnstile> Cast T e \<leadsto> e'"
  "P,E \<turnstile> e instanceof T \<leadsto> e'"
  "P,E \<turnstile> Val v \<leadsto> e'"
  "P,E \<turnstile> Var V \<leadsto> e'"
  "P,E \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 \<leadsto> e'"
  "P,E \<turnstile> V := e \<leadsto> e'"
  "P,E \<turnstile> e1\<lfloor>e2\<rceil> \<leadsto> e'"
  "P,E \<turnstile> e1\<lfloor>e2\<rceil> := e3 \<leadsto> e'"
  "P,E \<turnstile> e\<bullet>length \<leadsto> e'"
  "P,E \<turnstile> e\<bullet>F{D} \<leadsto> e'"
  "P,E \<turnstile> e1\<bullet>F{D} := e2 \<leadsto> e'"
  "P,E \<turnstile> e\<bullet>M(es) \<leadsto> e'"
  "P,E \<turnstile> {V:T=vo; e} \<leadsto> e'"
  "P,E \<turnstile> sync(e1) e2 \<leadsto> e'"
  "P,E \<turnstile> insync(a) e2 \<leadsto> e'"
  "P,E \<turnstile> e1;; e2 \<leadsto> e'"
  "P,E \<turnstile> if (e) e1 else e2 \<leadsto> e'"
  "P,E \<turnstile> while(e1) e2 \<leadsto> e'"
  "P,E \<turnstile> throw e \<leadsto> e'"
  "P,E \<turnstile> try e1 catch(C V) e2 \<leadsto> e'"

inductive_cases Annos_cases [elim!]:
  "P,E \<turnstile> [] [\<leadsto>] es'"
  "P,E \<turnstile> e # es [\<leadsto>] es'"

definition annotate :: "J_prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> expr"
where "annotate P E e = THE_default e (\<lambda>e'. P,E \<turnstile> e \<leadsto> e')"

lemma assumes wf: "wf_prog wfmd P"
  shows  Anno_fun: "\<lbrakk> P,E \<turnstile> e \<leadsto> e'; P,E \<turnstile> e \<leadsto> e'' \<rbrakk> \<Longrightarrow> e' = e''"
  and Annos_fun: "\<lbrakk> P,E \<turnstile> es [\<leadsto>] es'; P,E \<turnstile> es [\<leadsto>] es'' \<rbrakk> \<Longrightarrow> es' = es''"
proof(induct arbitrary: e'' and es'' rule: Anno_Annos.inducts)
  case (AnnoFAcc E e e' C F T fm D)
  from `P,E \<turnstile> e\<bullet>F{STR []} \<leadsto> e''` show ?case
  proof(rule Anno_cases)
    fix e''' C' T' fm' D'
    assume "P,E \<turnstile> e \<leadsto> e'''" "P,E \<turnstile> e''' :: Class C'"
      and "P \<turnstile> C' sees F:T' (fm') in D'" "e'' = e'''\<bullet>F{D'}"
    from `P,E \<turnstile> e \<leadsto> e'''` have "e' = e'''" by(rule AnnoFAcc)
    with `P,E \<turnstile> e' :: Class C` `P,E \<turnstile> e''' :: Class C'`
    have "C = C'" by(auto dest: WT_unique[OF wf])
    with `P \<turnstile> C' sees F:T' (fm') in D'` `P \<turnstile> C sees F:T (fm) in D`
    have "D' = D" by(auto dest: sees_field_fun)
    with `e'' = e'''\<bullet>F{D'}` `e' = e'''` show ?thesis by simp
  next
    fix e''' T
    assume "e'' = e'''\<bullet>length"
      and "P,E \<turnstile> e''' :: T\<lfloor>\<rceil>"
      and "P,E \<turnstile> e \<leadsto> e'''"
    from `P,E \<turnstile> e \<leadsto> e'''` have "e' = e'''" by(rule AnnoFAcc)
    with `P,E \<turnstile> e' :: Class C` `P,E \<turnstile> e''' :: T\<lfloor>\<rceil>` have False by(auto dest: WT_unique[OF wf])
    thus ?thesis ..
  next
    fix C' D' fs ms T D''
    assume "E this = \<lfloor>Class C'\<rfloor>"
      and "class P C' = \<lfloor>(D', fs, ms)\<rfloor>"
      and "e = Var super"
      and "e'' = Cast (Class D') (Var this)\<bullet>F{D''}"
    with `P,E \<turnstile> e \<leadsto> e'` have False by(auto)
    thus ?thesis ..
  qed
next
  case AnnoFAccALength thus ?case by(fastsimp dest: WT_unique[OF wf])
next
  case (AnnoFAss E e1 e1' e2 e2' C F T fm D)
  from `P,E \<turnstile> e1\<bullet>F{STR []} := e2 \<leadsto> e''` 
  show ?case
  proof(rule Anno_cases)
    fix e1'' e2'' C' T' fm' D'
    assume "P,E \<turnstile> e1 \<leadsto> e1''" "P,E \<turnstile> e2 \<leadsto> e2''"
      and "P,E \<turnstile> e1'' :: Class C'" "P \<turnstile> C' sees F:T' (fm') in D'"
      and "e'' = e1''\<bullet>F{D'} := e2''"
    from `P,E \<turnstile> e1 \<leadsto> e1''` have "e1' = e1''" by(rule AnnoFAss)
    moreover with `P,E \<turnstile> e1' :: Class C` `P,E \<turnstile> e1'' :: Class C'`
    have "C = C'" by(auto dest: WT_unique[OF wf])
    with `P \<turnstile> C' sees F:T' (fm') in D'` `P \<turnstile> C sees F:T (fm) in D`
    have "D' = D" by(auto dest: sees_field_fun)
    moreover from `P,E \<turnstile> e2 \<leadsto> e2''` have "e2' = e2''" by(rule AnnoFAss)
    ultimately show ?thesis using `e'' = e1''\<bullet>F{D'} := e2''` by simp
  next
    fix C' D' fs ms T' fm' D'' e'''
    assume "e'' = Cast (Class D') (Var this)\<bullet>F{D''} := e'''"
      and "E this = \<lfloor>Class C'\<rfloor>"
      and "class P C' = \<lfloor>(D', fs, ms)\<rfloor>"
      and "P \<turnstile> D' sees F:T' (fm') in D''"
      and "P,E \<turnstile> e2 \<leadsto> e'''"
      and "e1 = Var super"
    with `P,E \<turnstile> e1 \<leadsto> e1'` have False by(auto elim: Anno_cases)
    thus ?thesis ..
  qed
qed(fastsimp dest: sees_field_fun)+

subsection {* Code generation *}

text {*
  The same as @{term Anno} and @{term Annos} but with @{term WT} replaced by @{term WT_code}. 
  Since @{term WT} and @{term WT_code} are not identical, these relations aren't either.
  But for well-formed programs @{term "P"} and environments whose ranges contains only
  types @{term "T"} with @{term "is_type P T"}, they are equal, see below.
*}

inductive Anno_code :: "J_prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> bool" ("_,_ \<turnstile> _ \<leadsto>' _"   [51,0,0,51]50)
  and Annos_code :: "J_prog \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> bool" ("_,_ \<turnstile> _ [\<leadsto>''] _" [51,0,0,51]50)
for P :: J_prog
where
  Anno_codeNew: "P,E \<turnstile> new C \<leadsto>' new C"
| Anno_codeNewArray: "P,E \<turnstile> i \<leadsto>' i' \<Longrightarrow> P,E \<turnstile> newA T\<lfloor>i\<rceil> \<leadsto>' newA T\<lfloor>i'\<rceil>"
| Anno_codeCast: "P,E \<turnstile> e \<leadsto>' e' \<Longrightarrow> P,E \<turnstile> Cast C e \<leadsto>' Cast C e'"
| Anno_codeInstanceOf: "P,E \<turnstile> e \<leadsto>' e' \<Longrightarrow> P,E \<turnstile> e instanceof T \<leadsto>' e' instanceof T"
| Anno_codeVal: "P,E \<turnstile> Val v \<leadsto>' Val v"
| Anno_codeVarVar: "\<lbrakk> E V = \<lfloor>T\<rfloor>; V \<noteq> super \<rbrakk> \<Longrightarrow> P,E \<turnstile> Var V \<leadsto>' Var V"
| Anno_codeVarField:
  "\<lbrakk> E V = None; V \<noteq> super; E this = \<lfloor>Class C\<rfloor>; P \<turnstile> C sees V:T (fm) in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> Var V \<leadsto>' Var this\<bullet>V{D}"
| Anno_codeBinOp:
  "\<lbrakk> P,E \<turnstile> e1 \<leadsto>' e1';  P,E \<turnstile> e2 \<leadsto>' e2' \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 \<leadsto>' e1' \<guillemotleft>bop\<guillemotright> e2'"
| Anno_codeLAssVar:
  "\<lbrakk> E V = \<lfloor>T\<rfloor>; P,E \<turnstile> e \<leadsto>' e' \<rbrakk> \<Longrightarrow> P,E \<turnstile> V:=e \<leadsto>' V:=e'"
| Anno_codeLAssField:
  "\<lbrakk> E V = None; E this = \<lfloor>Class C\<rfloor>; P \<turnstile> C sees V:T (fm) in D; P,E \<turnstile> e \<leadsto>' e' \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> V:=e \<leadsto>' Var this\<bullet>V{D} := e'"
| Anno_codeAAcc:
  "\<lbrakk> P,E \<turnstile> a \<leadsto>' a'; P,E \<turnstile> i \<leadsto>' i' \<rbrakk> \<Longrightarrow> P,E \<turnstile> a\<lfloor>i\<rceil> \<leadsto>' a'\<lfloor>i'\<rceil>"
| Anno_codeAAss:
  "\<lbrakk> P,E \<turnstile> a \<leadsto>' a'; P,E \<turnstile> i \<leadsto>' i'; P,E \<turnstile> e \<leadsto>' e' \<rbrakk> \<Longrightarrow> P,E \<turnstile> a\<lfloor>i\<rceil> := e \<leadsto>' a'\<lfloor>i'\<rceil> := e'"
| Anno_codeALength:
  "P,E \<turnstile> a \<leadsto>' a' \<Longrightarrow> P,E \<turnstile> a\<bullet>length \<leadsto>' a'\<bullet>length"
| Anno_codeFAcc:
  "\<lbrakk> P,E \<turnstile> e \<leadsto>' e'; WT_code P E e' = OK (Class C); P \<turnstile> C sees F:T (fm) in D \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> e\<bullet>F{STR []} \<leadsto>' e'\<bullet>F{D}"
| Anno_codeFAccALength:
  "\<lbrakk> P,E \<turnstile> e \<leadsto>' e'; WT_code P E e' = OK (T\<lfloor>\<rceil>) \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>array_length_field_name{STR []} \<leadsto>' e'\<bullet>length"
| Anno_codeFAccSuper:
  -- {* In class C with super class D, "super" is syntactic sugar for "((D) this)" (cf. JLS, 15.11.2) *}
  "\<lbrakk> E this = \<lfloor>Class C\<rfloor>; C \<noteq> Object; class P C = \<lfloor>(D, fs, ms)\<rfloor>; 
     P \<turnstile> D sees F:T (fm) in D' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> Var super\<bullet>F{STR []} \<leadsto>' (Cast (Class D) (Var this))\<bullet>F{D'}"
| Anno_codeFAss:
  "\<lbrakk> P,E \<turnstile> e1 \<leadsto>' e1';  P,E \<turnstile> e2 \<leadsto>' e2';
     WT_code P E e1' = OK (Class C); P \<turnstile> C sees F:T (fm) in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e1\<bullet>F{STR []} := e2 \<leadsto>' e1'\<bullet>F{D} := e2'"
| Anno_codeFAssSuper:
  "\<lbrakk> E this = \<lfloor>Class C\<rfloor>; C \<noteq> Object; class P C = \<lfloor>(D, fs, ms)\<rfloor>;
     P \<turnstile> D sees F:T (fm) in D'; P,E \<turnstile> e \<leadsto>' e' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> Var super\<bullet>F{STR []} := e \<leadsto>' (Cast (Class D) (Var this))\<bullet>F{D'} := e'"
| Anno_codeCall:
  "\<lbrakk> P,E \<turnstile> e \<leadsto>' e';  P,E \<turnstile> es [\<leadsto>'] es' \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> Call e M es \<leadsto>' Call e' M es'"
| Anno_codeBlock:
  "P,E(V \<mapsto> T) \<turnstile> e \<leadsto>' e'  \<Longrightarrow>  P,E \<turnstile> {V:T=vo; e} \<leadsto>' {V:T=vo; e'}"
| Anno_codeSync:
  "\<lbrakk> P,E \<turnstile> e1 \<leadsto>' e1'; P,E \<turnstile> e2 \<leadsto>' e2' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> sync(e1) e2 \<leadsto>' sync(e1') e2'"
| Anno_codeComp:
  "\<lbrakk> P,E \<turnstile> e1 \<leadsto>' e1';  P,E \<turnstile> e2 \<leadsto>' e2' \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> e1;;e2 \<leadsto>' e1';;e2'"
| Anno_codeCond:
  "\<lbrakk> P,E \<turnstile> e \<leadsto>' e'; P,E \<turnstile> e1 \<leadsto>' e1';  P,E \<turnstile> e2 \<leadsto>' e2' \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> if (e) e1 else e2 \<leadsto>' if (e') e1' else e2'"
| Anno_codeLoop:
  "\<lbrakk> P,E \<turnstile> e \<leadsto>' e';  P,E \<turnstile> c \<leadsto>' c' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> while (e) c \<leadsto>' while (e') c'"
| Anno_codeThrow:
  "P,E \<turnstile> e \<leadsto>' e' \<Longrightarrow> P,E \<turnstile> throw e \<leadsto>' throw e'"
| Anno_codeTry:
  "\<lbrakk> P,E \<turnstile> e1 \<leadsto>' e1';  P,E(V \<mapsto> Class C) \<turnstile> e2 \<leadsto>' e2' \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> try e1 catch(C V) e2 \<leadsto>' try e1' catch(C V) e2'"

| Anno_codeNil:
  "P,E \<turnstile> [] [\<leadsto>'] []"
| Anno_codeCons:
  "\<lbrakk> P,E \<turnstile> e \<leadsto>' e';  P,E \<turnstile> es [\<leadsto>'] es' \<rbrakk> \<Longrightarrow>  P,E \<turnstile> e#es [\<leadsto>'] e'#es'"

primrec block_types :: "('a, 'b) exp \<Rightarrow> ty list" 
  and blocks_types :: "('a, 'b) exp list \<Rightarrow> ty list"
where 
  "block_types (new C) = []"
| "block_types (newA T\<lfloor>e\<rceil>) = block_types e"
| "block_types (Cast U e) = block_types e"
| "block_types (e instanceof U) = block_types e"
| "block_types (e1\<guillemotleft>bop\<guillemotright>e2) = block_types e1 @ block_types e2"
| "block_types (Val v) = []"
| "block_types (Var V) = []"
| "block_types (V := e) = block_types e"
| "block_types (a\<lfloor>i\<rceil>) = block_types a @ block_types i"
| "block_types (a\<lfloor>i\<rceil> := e) = block_types a @ block_types i @ block_types e"
| "block_types (a\<bullet>length) = block_types a"
| "block_types (e\<bullet>F{D}) = block_types e"
| "block_types (e\<bullet>F{D} := e') = block_types e @ block_types e'"
| "block_types (e\<bullet>M(es)) = block_types e @ blocks_types es"
| "block_types {V:T=vo; e} = T # block_types e"
| "block_types (sync\<^bsub>V\<^esub>(e) e') = block_types e @ block_types e'"
| "block_types (insync\<^bsub>V\<^esub>(a) e) = block_types e"
| "block_types (e;;e') = block_types e @ block_types e'"
| "block_types (if (e) e1 else e2) = block_types e @ block_types e1 @ block_types e2"
| "block_types (while (b) c) = block_types b @ block_types c"
| "block_types (throw e) = block_types e"
| "block_types (try e catch(C V) e') = block_types e @ Class C # block_types e'"

| "blocks_types [] = []"
| "blocks_types (e#es) = block_types e @ blocks_types es"

lemma assumes wf: "wf_prog wf_md P"
  shows Anno_into_Anno_code: "\<lbrakk> P,E \<turnstile> e \<leadsto> e'; ran E \<union> set (block_types e) \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> e \<leadsto>' e'"
  and Annos_into_Annos_code: "\<lbrakk> P,E \<turnstile> es [\<leadsto>] es'; ran E \<union> set (blocks_types es) \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> es [\<leadsto>'] es'"
proof(induct rule: Anno_Annos.inducts)
  case (AnnoBlock E V T e e' vo)
  from `ran E \<union> set (block_types {V:T=vo; e}) \<subseteq> types P`
  have "ran (E(V \<mapsto> T)) \<union> set (block_types e) \<subseteq> types P"
    by(auto simp add: ran_def)
  thus ?case using AnnoBlock by(blast intro: Anno_code_Annos_code.intros)
next
  case (AnnoTry E e1 e1' V C e2 e2')
  from `ran E \<union> set (block_types (try e1 catch(C V) e2)) \<subseteq> types P`
  have "ran (E(V \<mapsto> Class C)) \<union> set (block_types e2) \<subseteq> types P"
    by(auto simp add: ran_def)
  thus ?case using AnnoTry by(simp del: fun_upd_apply)(blast intro: Anno_code_Annos_code.intros)
qed(simp_all,(blast intro: Anno_code_Annos_code.intros WT_into_WT_code_OK[OF wf])+)

lemma assumes wf: "wf_prog wf_md P"
  shows Anno_code_into_Anno: "\<lbrakk> P,E \<turnstile> e \<leadsto>' e'; ran E \<union> set (block_types e) \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> e \<leadsto> e'"
  and Annos_code_into_Annos: "\<lbrakk> P,E \<turnstile> es [\<leadsto>'] es'; ran E \<union> set (blocks_types es) \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> es [\<leadsto>] es'"
proof(induct rule: Anno_code_Annos_code.inducts)
  case (Anno_codeBlock E V T e e' vo)
  from `ran E \<union> set (block_types {V:T=vo; e}) \<subseteq> types P`
  have "ran (E(V \<mapsto> T)) \<union> set (block_types e) \<subseteq> types P"
    by(auto simp add: ran_def)
  thus ?case using Anno_codeBlock by(blast intro: Anno_Annos.intros)
next
  case (Anno_codeTry E e1 e1' V C e2 e2')
  from `ran E \<union> set (block_types (try e1 catch(C V) e2)) \<subseteq> types P`
  have "ran (E(V \<mapsto> Class C)) \<union> set (block_types e2) \<subseteq> types P"
    by(auto simp add: ran_def)
  thus ?case using Anno_codeTry by(simp del: fun_upd_apply)(blast intro: Anno_Annos.intros)
qed(simp_all,(blast intro: Anno_Annos.intros WT_code_OK_into_WT[OF wf])+)

lemma assumes wf: "wf_prog wf_md P"
  shows WT_block_types_is_type: "P,E \<turnstile> e :: T \<Longrightarrow> set (block_types e) \<subseteq> types P"
  and WTs_blocks_types_is_type: "P,E \<turnstile> es [::] Ts \<Longrightarrow> set (blocks_types es) \<subseteq> types P"
apply(induct rule: WT_WTs.inducts)
apply(auto intro: is_class_sub_Throwable[OF wf])
done

lemma Anno_code_block_types: "P,E \<turnstile> e \<leadsto>' e' \<Longrightarrow> block_types e = block_types e'"
  and Annos_code_blocks_types: "P,E \<turnstile> es [\<leadsto>'] es' \<Longrightarrow> blocks_types es = blocks_types es'"
by(induct rule: Anno_code_Annos_code.inducts) auto

code_pred [detect_switches, skip_proof] Anno_code .

definition annotate_code :: "J_prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> expr"
where "annotate_code P E e = THE_default e (\<lambda>e'. P,E \<turnstile> e \<leadsto>' e')"
 
lemma eval_Anno_i_i_i_o_conv:
  "Predicate.eval (Anno_code_i_i_i_o P E e) = (\<lambda>e'. P,E \<turnstile> e \<leadsto>' e')"
by(auto intro!: ext intro: Anno_code_i_i_i_oI elim: Anno_code_i_i_i_oE)
 
lemma annotate_code [code]:
  "annotate_code P E e = Predicate.singleton (\<lambda>_. FinFun.code_abort (\<lambda>_. e)) (Anno_code_i_i_i_o P E e)"
by(simp add: THE_default_def Predicate.singleton_def annotate_code_def eval_Anno_i_i_i_o_conv)
 
end
