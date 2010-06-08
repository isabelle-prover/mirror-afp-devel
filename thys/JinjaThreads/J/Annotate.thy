(*  Title:      Jinja/J/Annotate.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Program annotation} *}

theory Annotate imports
  WellType 
  "../Common/WellForm"
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
  "\<lbrakk> E V = None; V \<noteq> super; E this = \<lfloor>Class C\<rfloor>; P \<turnstile> C sees V:T in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> Var V \<leadsto> Var this\<bullet>V{D}"
| AnnoBinOp:
  "\<lbrakk> P,E \<turnstile> e1 \<leadsto> e1';  P,E \<turnstile> e2 \<leadsto> e2' \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 \<leadsto> e1' \<guillemotleft>bop\<guillemotright> e2'"
| AnnoLAssVar:
  "\<lbrakk> E V = \<lfloor>T\<rfloor>; P,E \<turnstile> e \<leadsto> e' \<rbrakk> \<Longrightarrow> P,E \<turnstile> V:=e \<leadsto> V:=e'"
| AnnoLAssField:
  "\<lbrakk> E V = None; E this = \<lfloor>Class C\<rfloor>; P \<turnstile> C sees V:T in D; P,E \<turnstile> e \<leadsto> e' \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> V:=e \<leadsto> Var this\<bullet>V{D} := e'"
| AnnoAAcc:
  "\<lbrakk> P,E \<turnstile> a \<leadsto> a'; P,E \<turnstile> i \<leadsto> i' \<rbrakk> \<Longrightarrow> P,E \<turnstile> a\<lfloor>i\<rceil> \<leadsto> a'\<lfloor>i'\<rceil>"
| AnnoAAss:
  "\<lbrakk> P,E \<turnstile> a \<leadsto> a'; P,E \<turnstile> i \<leadsto> i'; P,E \<turnstile> e \<leadsto> e' \<rbrakk> \<Longrightarrow> P,E \<turnstile> a\<lfloor>i\<rceil> := e \<leadsto> a'\<lfloor>i'\<rceil> := e'"
| AnnoALength:
  "P,E \<turnstile> a \<leadsto> a' \<Longrightarrow> P,E \<turnstile> a\<bullet>length \<leadsto> a'\<bullet>length"
| AnnoFAcc:
  "\<lbrakk> P,E \<turnstile> e \<leadsto> e';  P,E \<turnstile> e' :: Class C;  P \<turnstile> C sees F:T in D \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> e\<bullet>F{STR []} \<leadsto> e'\<bullet>F{D}"
| AnnoFAccALength:
  "\<lbrakk> P,E \<turnstile> e \<leadsto> e'; P,E \<turnstile> e' :: T\<lfloor>\<rceil> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>array_length_field_name{STR []} \<leadsto> e'\<bullet>length"
| AnnoFAccSuper:
  -- {* In class C with super class D, "super" is syntactic sugar for "((D) this)" (cf. JLS, 15.11.2) *}
  "\<lbrakk> E this = \<lfloor>Class C\<rfloor>; C \<noteq> Object; class P C = \<lfloor>(D, fs, ms)\<rfloor>; 
     P \<turnstile> D sees F:T in D' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> Var super\<bullet>F{STR []} \<leadsto> (Cast (Class D) (Var this))\<bullet>F{D'}"
| AnnoFAss:
  "\<lbrakk> P,E \<turnstile> e1 \<leadsto> e1';  P,E \<turnstile> e2 \<leadsto> e2';
     P,E \<turnstile> e1' :: Class C; P \<turnstile> C sees F:T in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e1\<bullet>F{STR []} := e2 \<leadsto> e1'\<bullet>F{D} := e2'"
| AnnoFAssSuper:
  "\<lbrakk> E this = \<lfloor>Class C\<rfloor>; C \<noteq> Object; class P C = \<lfloor>(D, fs, ms)\<rfloor>;
     P \<turnstile> D sees F:T in D'; P,E \<turnstile> e \<leadsto> e' \<rbrakk>
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
where "annotate P E e = (THE e'. P,E \<turnstile> e \<leadsto> e')"

lemma Anno_fun: "\<lbrakk> P,E \<turnstile> e \<leadsto> e'; P,E \<turnstile> e \<leadsto> e'' \<rbrakk> \<Longrightarrow> e' = e''"
  and Annos_fun: "\<lbrakk> P,E \<turnstile> es [\<leadsto>] es'; P,E \<turnstile> es [\<leadsto>] es'' \<rbrakk> \<Longrightarrow> es' = es''"
proof(induct arbitrary: e'' and es'' rule: Anno_Annos.inducts)
  case (AnnoFAcc E e e' C F T D)
  from `P,E \<turnstile> e\<bullet>F{STR []} \<leadsto> e''` show ?case
  proof(rule Anno_cases)
    fix e''' C' T' D'
    assume "P,E \<turnstile> e \<leadsto> e'''" "P,E \<turnstile> e''' :: Class C'"
      and "P \<turnstile> C' sees F:T' in D'" "e'' = e'''\<bullet>F{D'}"
    from `P,E \<turnstile> e \<leadsto> e'''` have "e' = e'''" by(rule AnnoFAcc)
    with `P,E \<turnstile> e' :: Class C` `P,E \<turnstile> e''' :: Class C'`
    have "C = C'" by(auto dest: WT_unique)
    with `P \<turnstile> C' sees F:T' in D'` `P \<turnstile> C sees F:T in D`
    have "D' = D" by(auto dest: sees_field_fun)
    with `e'' = e'''\<bullet>F{D'}` `e' = e'''` show ?thesis by simp
  next
    fix e''' T
    assume "e'' = e'''\<bullet>length"
      and "P,E \<turnstile> e''' :: T\<lfloor>\<rceil>"
      and "P,E \<turnstile> e \<leadsto> e'''"
    from `P,E \<turnstile> e \<leadsto> e'''` have "e' = e'''" by(rule AnnoFAcc)
    with `P,E \<turnstile> e' :: Class C` `P,E \<turnstile> e''' :: T\<lfloor>\<rceil>` have False by(auto dest: WT_unique)
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
  case AnnoFAccALength thus ?case by(fastsimp dest: WT_unique)
next
  case (AnnoFAss E e1 e1' e2 e2' C F T D)
  from `P,E \<turnstile> e1\<bullet>F{STR []} := e2 \<leadsto> e''` 
  show ?case
  proof(rule Anno_cases)
    fix e1'' e2'' C' T' D'
    assume "P,E \<turnstile> e1 \<leadsto> e1''" "P,E \<turnstile> e2 \<leadsto> e2''"
      and "P,E \<turnstile> e1'' :: Class C'" "P \<turnstile> C' sees F:T' in D'"
      and "e'' = e1''\<bullet>F{D'} := e2''"
    from `P,E \<turnstile> e1 \<leadsto> e1''` have "e1' = e1''" by(rule AnnoFAss)
    moreover with `P,E \<turnstile> e1' :: Class C` `P,E \<turnstile> e1'' :: Class C'`
    have "C = C'" by(auto dest: WT_unique)
    with `P \<turnstile> C' sees F:T' in D'` `P \<turnstile> C sees F:T in D`
    have "D' = D" by(auto dest: sees_field_fun)
    moreover from `P,E \<turnstile> e2 \<leadsto> e2''` have "e2' = e2''" by(rule AnnoFAss)
    ultimately show ?thesis using `e'' = e1''\<bullet>F{D'} := e2''` by simp
  next
    fix C' D' fs ms T' D'' e'''
    assume "e'' = Cast (Class D') (Var this)\<bullet>F{D''} := e'''"
      and "E this = \<lfloor>Class C'\<rfloor>"
      and "class P C' = \<lfloor>(D', fs, ms)\<rfloor>"
      and "P \<turnstile> D' sees F:T' in D''"
      and "P,E \<turnstile> e2 \<leadsto> e'''"
      and "e1 = Var super"
    with `P,E \<turnstile> e1 \<leadsto> e1'` have False by(auto elim: Anno_cases)
    thus ?thesis ..
  qed
qed(fastsimp dest: sees_field_fun)+

subsection {* Code generator setup *}

code_pred [detect_switches, skip_proof] Anno .

(* FIXME: code_pred performs case_split on String.literal.
   Hence, code equations for Anno are illegal *)

lemma eval_Anno_i_i_i_o_conv:
  "Predicate.eval (Anno_i_i_i_o P E e) = (\<lambda>e'. P,E \<turnstile> e \<leadsto> e')"
by(auto intro!: ext intro: Anno_i_i_i_oI elim: Anno_i_i_i_oE)

lemma annotate_code [code]:
  "annotate P E e = Predicate.the (Anno_i_i_i_o P E e)"
by(simp add: annotate_def Predicate.the_def Predicate.bind_def Predicate.single_def eval_Anno_i_i_i_o_conv)

end
