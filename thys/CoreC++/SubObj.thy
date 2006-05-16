(* Author: Daniel Wasserrab *)

header {* Definition of Subobjects *}

theory SubObj imports ClassRel begin

subsection {* General definitions *}

types
  subobj = "cname  \<times> path"

consts 
  mdc :: "subobj \<Rightarrow> cname"
  ldc :: "subobj \<Rightarrow> cname"
defs mdc_def:
  "mdc S == fst S"
defs ldc_def:
  "ldc S == last (snd S)"


lemma mdc_tuple [simp]: "mdc (C,Cs) = C"
by(simp add:mdc_def)

lemma ldc_tuple [simp]: "ldc (C,Cs) = last Cs"
by(simp add:ldc_def)


subsection {* Subobjects according to Rossie-Friedman *}

consts
  is_subobj :: "prog \<times> subobj \<Rightarrow> bool" -- "legal subobject to class hierarchie"

recdef is_subobj "measure (\<lambda> (P,(C,Xs)).length Xs)"
  "is_subobj (P,(C,[])) = False"
  "is_subobj (P,(C,[D])) = ((is_class P C \<and> C = D) 
                                \<or> (\<exists> X. P \<turnstile> C \<preceq>\<^sup>* X \<and> P \<turnstile> X \<prec>\<^sub>S D))"
  "is_subobj (P, (C,D#E#Xs)) = (let Ys=butlast(D#E#Xs); 
                                    Y=last (D#E#Xs); 
                                    X=last Ys 
                                in is_subobj (P, (C,Ys)) \<and> P \<turnstile> X \<prec>\<^sub>R Y)"


lemma subobj_aux_rev:
assumes 1:"is_subobj(P,(C,C'#rev Cs@[C'']))"
shows "is_subobj(P,(C,C'#rev Cs))"
proof -
  obtain Cs' where Cs':"Cs' = rev Cs" by simp
  hence rev:"Cs'@[C''] = rev Cs@[C'']" by simp
  from this obtain D Ds where DDs:"Cs'@[C''] = D#Ds" by (cases Cs') auto
  with 1 rev have subo:"is_subobj(P,(C,C'#D#Ds))" by simp
  from DDs have "butlast (C'#D#Ds) = C'#Cs'" by (cases Cs') auto
  with subo have "is_subobj(P,(C,C'#Cs'))" by simp
  with Cs' show ?thesis by simp
qed



lemma subobj_aux:
assumes 1:"is_subobj(P,(C,C'#Cs@[C'']))"
shows "is_subobj(P,(C,C'#Cs))"
proof -
  from 1 obtain Cs' where Cs':"Cs' = rev Cs" by simp
  with 1 have "is_subobj (P,(C,C'#rev Cs'@[C'']))" by simp
  hence "is_subobj (P,(C,C'#rev Cs'))" by (rule subobj_aux_rev)
  with Cs' show ?thesis by simp
qed



lemma isSubobj_isClass:
assumes 1:"is_subobj (P,R)"
shows "is_class P (mdc R)"

proof -
  obtain C' Cs' where R:"R = (C',Cs')" by(cases R) auto
  with 1 have ne:"Cs' \<noteq> []" by (cases Cs') auto
  from this obtain C'' Cs'' where C''Cs'':"Cs' = C''#Cs''" by (cases Cs') auto
  from this obtain Ds where "Ds = rev Cs''" by simp
  with 1 R C''Cs'' have subo1:"is_subobj(P,(C',C''#rev Ds))" by simp
  with R show ?thesis
    by (induct Ds,auto simp:mdc_def split:split_if_asm dest:subobj_aux,
      auto elim:converse_rtranclE dest!:subclsS_subcls1 elim:subcls1_class)
qed




lemma isSubobjs_subclsR_rev:
assumes 1:"is_subobj (P,(C,Cs@[D,D']@(rev Cs')))"
shows "P \<turnstile> D \<prec>\<^sub>R D'"
using 1
proof (induct Cs')
  case Nil
  from this obtain Cs' X Y Xs where Cs'1:"Cs' = Cs@[D,D']" 
    and "X = hd(Cs@[D,D'])" and "Y = hd(tl(Cs@[D,D']))"
    and "Xs =  tl(tl(Cs@[D,D']))" by simp
  hence Cs'2:"Cs' = X#Y#Xs" by (cases Cs) auto
  from Cs'1 have last:"last Cs' = D'" by simp
  from Cs'1 have butlast:"last(butlast Cs') = D" by (simp add:butlast_tail)
  from Nil Cs'1 Cs'2 have "is_subobj (P,(C,X#Y#Xs))" by simp
  with last butlast Cs'2 show ?case by simp
next
  case (Cons C'' Cs'')
  have IH:"is_subobj (P, C, Cs @ [D, D'] @ rev Cs'') \<Longrightarrow> P \<turnstile> D \<prec>\<^sub>R D'" .
  from Cons obtain Cs' X Y Xs where Cs'1:"Cs' = Cs@[D,D']@(rev (C''#Cs''))" 
    and "X = hd(Cs@[D,D']@(rev (C''#Cs'')))" 
    and "Y = hd(tl(Cs@[D,D']@(rev (C''#Cs''))))"
    and "Xs =  tl(tl(Cs@[D,D']@(rev (C''#Cs''))))" by simp
  hence Cs'2:"Cs' = X#Y#Xs" by (cases Cs) auto
  from Cons Cs'1 Cs'2 have "is_subobj (P,(C,X#Y#Xs))" by simp
  hence sub:"is_subobj (P,(C,butlast (X#Y#Xs)))" by simp
  from Cs'1 obtain E Es where Cs'3:"Cs' = Es@[E]" by (cases Cs') auto
  with Cs'1 have butlast:"Es = Cs@[D,D']@(rev Cs'')" by simp
  from Cs'3 have "butlast Cs' = Es" by simp
  with butlast have "butlast Cs' = Cs@[D,D']@(rev Cs'')" by simp
  with Cs'2 sub have "is_subobj (P,(C,Cs@[D,D']@(rev Cs'')))"
    by simp
  with IH show ?case by simp
qed



lemma isSubobjs_subclsR:
assumes 1:"is_subobj (P,(C,Cs@[D,D']@Cs'))"
shows "P \<turnstile> D \<prec>\<^sub>R D'"

proof -
  from 1 obtain Cs'' where "Cs'' = rev Cs'" by simp
  with 1 have "is_subobj (P,(C,Cs@[D,D']@(rev Cs'')))" by simp
  thus ?thesis by (rule isSubobjs_subclsR_rev)
qed




lemma mdc_leq_ldc_aux:
assumes 1:"is_subobj(P,(C,C'#rev Cs'))"
shows "P \<turnstile> C \<preceq>\<^sup>* last (C'#rev Cs')"
using 1
proof (induct Cs')
  case Nil
  from 1 have "is_class P C"
    by (drule_tac R="(C,C'#rev Cs')" in isSubobj_isClass, simp add:mdc_def)
  with Nil show ?case
    proof (cases "C=C'")
      case True
      thus ?thesis by simp
    next
      case False
      with Nil show ?thesis 
	by (auto dest!:subclsS_subcls1)
    qed
  next
    case (Cons C'' Cs'')
    have IH:"is_subobj (P, C, C' # rev Cs'') \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* last (C' # rev Cs'')"
      and subo:"is_subobj (P, C, C' # rev (C'' # Cs''))" .
    hence "is_subobj (P, C, C' # rev Cs'')" by (simp add:subobj_aux_rev)
    with IH have rel:"P \<turnstile> C \<preceq>\<^sup>* last (C' # rev Cs'')" by simp
    from subo obtain D Ds where DDs:"C' # rev Cs'' = Ds@[D]"
      by (cases Cs'') auto
    hence " C' # rev (C'' # Cs'') = Ds@[D,C'']" by simp
    with subo have "is_subobj(P,(C,Ds@[D,C'']))" by (cases Ds) auto
    hence "P \<turnstile> D \<prec>\<^sub>R C''" by (rule_tac Cs'="[]" in isSubobjs_subclsR) simp
    hence rel1:"P \<turnstile> D \<prec>\<^sup>1 C''" by (rule subclsR_subcls1)
    from DDs have "D = last (C' # rev Cs'')" by simp
    with rel1 have lastrel1:"P \<turnstile> last (C' # rev Cs'') \<prec>\<^sup>1 C''" by simp
    with rel have "P \<turnstile> C \<preceq>\<^sup>* C''"
      by(rule_tac b="last (C' # rev Cs'')" in rtrancl_into_rtrancl) simp
    thus ?case by simp
qed



lemma mdc_leq_ldc:
assumes 1:"is_subobj(P,R)"
shows "P \<turnstile> mdc R \<preceq>\<^sup>* ldc R"

proof -
  from 1 obtain C Cs where R:"R = (C,Cs)" by (cases R) auto
  with 1 have ne:"Cs \<noteq> []" by (cases Cs) auto
  from this obtain C' Cs' where Cs:"Cs = C'#Cs'" by (cases Cs) auto
  from this obtain Cs'' where Cs':"Cs'' = rev Cs'" by simp
  with R Cs 1 have "is_subobj(P,(C,C'#rev Cs''))" by simp
  hence rel:"P \<turnstile> C \<preceq>\<^sup>* last (C'#rev Cs'')" by (rule mdc_leq_ldc_aux)
  from R Cs Cs' have ldc:"last (C'#rev Cs'') = ldc R" by(simp add:ldc_def)
  from R have "mdc R = C" by(simp add:mdc_def)
  with ldc rel show ?thesis by simp
qed



text{* Next three lemmas show subobject property as presented in literature *}

lemma class_isSubobj:
  "is_class P C \<Longrightarrow> is_subobj (P,(C,[C]))"
by simp


lemma repSubobj_isSubobj:
assumes 1:"is_subobj (P,(C,Xs@[X]))" and 2:"P \<turnstile> X \<prec>\<^sub>R Y"
shows "is_subobj (P,(C,Xs@[X,Y]))"

using 1
proof -
  obtain Cs D E Cs' where Cs1:"Cs = Xs@[X,Y]" and  "D = hd(Xs@[X,Y])"
    and "E = hd(tl(Xs@[X,Y]))" and "Cs' = tl(tl(Xs@[X,Y]))"by simp
  hence Cs2:"Cs = D#E#Cs'" by (cases Xs) auto
  with 1 Cs1 have subobj_butlast:"is_subobj (P,(C,butlast(D#E#Cs')))" 
    by (simp add:butlast_tail)
  with 2 Cs1 Cs2 have "P \<turnstile> (last(butlast(D#E#Cs'))) \<prec>\<^sub>R last(D#E#Cs')"
    by (simp add:butlast_tail)
  with subobj_butlast have "is_subobj (P,(C,(D#E#Cs')))" by simp
  with Cs1 Cs2 show ?thesis by simp
qed



lemma shSubobj_isSubobj:
assumes 1:  "is_subobj (P,(C,Xs@[X]))" and 2:"P \<turnstile> X \<prec>\<^sub>S Y"
shows "is_subobj (P,(C,[Y]))"

using 1
proof -
  from 1 have classC:"is_class P C" 
    by (drule_tac R="(C,Xs@[X])" in isSubobj_isClass, simp add:mdc_def)
  from 1 have "P \<turnstile> C \<preceq>\<^sup>* X" 
    by (drule_tac R="(C,Xs@[X])" in mdc_leq_ldc, simp add:mdc_def ldc_def)
  with classC 2 show ?thesis by fastsimp
qed



text{* Auxiliary lemmas *}


lemma build_rec_isSubobj_rev:
assumes 1:"is_subobj (P,(D,D#rev Cs))" and 2:" P \<turnstile> C \<prec>\<^sub>R D"
shows "is_subobj (P,(C,C#D#rev Cs))"
using 1
proof (induct Cs)
  case Nil
  from 2 have "is_class P C" by (auto dest:subclsRD simp add:is_class_def)
  with 1 2 show ?case by simp
next
  case (Cons C' Cs')
  have suboD:"is_subobj (P,(D,D#rev (C'#Cs')))" 
    and IH:"is_subobj (P,(D,D#rev Cs')) \<Longrightarrow> is_subobj (P,(C,C#D#rev Cs'))" .
  obtain E Es where E:"E = hd (rev (C'#Cs'))" and Es:"Es = tl (rev (C'#Cs'))"
    by simp
  with E have E_Es:"rev (C'#Cs') = E#Es" by simp
  with E Es have butlast:"butlast (D#E#Es) = D#rev Cs'" by simp
  from E_Es suboD have suboDE:"is_subobj (P,(D,D#E#Es))" by simp
  hence "is_subobj (P,(D,butlast (D#E#Es)))" by simp
  with butlast have "is_subobj (P,(D,D#rev Cs'))" by simp
  with IH have suboCD:"is_subobj (P, C, C#D#rev Cs')" by simp
  from suboDE obtain Xs X Y Xs' where Xs':"Xs' = D#E#Es"
    and bb:"Xs = butlast (butlast (D#E#Es))" 
    and lb:"X = last(butlast (D#E#Es))" and l:"Y = last (D#E#Es)" by simp
  from this obtain Xs'' where Xs'':"Xs'' = Xs@[X]" by simp
  with bb lb have "Xs'' = butlast (D#E#Es)" by simp
  with l have "D#E#Es = Xs''@[Y]" by simp
  with Xs'' have "D#E#Es = Xs@[X]@[Y]" by simp
  with suboDE have "is_subobj (P,(D,Xs@[X,Y]))" by simp
  hence subR:"P \<turnstile> X \<prec>\<^sub>R Y"  by(rule_tac Cs="Xs" and Cs'="[]" in isSubobjs_subclsR) simp
  from E_Es Es have "last (D#E#Es) = C'" by simp
  with subR lb l butlast have "P \<turnstile> last(D#rev Cs') \<prec>\<^sub>R C'"
    by (auto split:split_if_asm)
  with suboCD show ?case by simp
qed



lemma build_rec_isSubobj:
assumes 1:"is_subobj (P,(D,D#Cs))" and 2:" P \<turnstile> C \<prec>\<^sub>R D" 
shows "is_subobj (P,(C,C#D#Cs))"

proof -
  obtain Cs' where Cs':"Cs' = rev Cs" by simp
  with 1 have "is_subobj (P,(D,D#rev Cs'))" by simp
  with 2 have "is_subobj (P,(C,C#D#rev Cs'))" 
    by - (rule build_rec_isSubobj_rev) 
  with Cs' show ?thesis by simp
qed





lemma isSubobj_isSubobj_isSubobj_rev:
assumes 1:"is_subobj(P,(C,[D]))" and 2:"is_subobj(P,(D,D#(rev Cs)))" 
shows "is_subobj(P,(C,D#(rev Cs)))"
using 2
proof (induct Cs)
 case Nil
 with 1 show ?case by simp
next
  case (Cons C' Cs')
  have IH:"is_subobj (P,(D,D#rev Cs')) \<Longrightarrow> is_subobj (P,(C,D#rev Cs'))"
    and "is_subobj (P,(D,D#rev (C'#Cs')))" .
  hence suboD:"is_subobj (P,(D,D#rev Cs'@[C']))" by simp
  hence "is_subobj (P,(D,D#rev Cs'))" by (rule subobj_aux_rev)
  with IH have suboC:"is_subobj (P,(C,D#rev Cs'))" by simp
  obtain C'' where C'':"C'' = last(D#rev Cs')" by simp
  hence butlast:"D#rev Cs' = butlast(D#rev Cs')@[C'']" by simp
  hence butlast2:"D#rev Cs'@[C'] = butlast(D#rev Cs')@[C'']@[C']" by simp
  with suboD have "is_subobj (P,(D,butlast(D#rev Cs')@[C'']@[C']))"
    by simp
  with C'' have subR:"P \<turnstile> C'' \<prec>\<^sub>R C'"
    by (rule_tac Cs="butlast(D#rev Cs')" and Cs'="[]" in isSubobjs_subclsR)simp
  with C'' suboC butlast have "is_subobj (P,(C,butlast(D#rev Cs')@[C'']@[C']))"
    by (auto intro:repSubobj_isSubobj simp del:butlast.simps)
  with butlast2 have "is_subobj (P,(C,D#rev Cs'@[C']))"
    by (cases Cs')auto
  thus ?case by simp
qed


lemma isSubobj_isSubobj_isSubobj:
assumes 1:"is_subobj(P,(C,[D]))" and 2:"is_subobj(P,(D,D#Cs))" 
shows "is_subobj(P,(C,D#Cs))"

proof -
  obtain Cs' where Cs':"Cs' = rev Cs" by simp
  with 2 have "is_subobj(P,(D,D#rev Cs'))" by simp
  with 1 have "is_subobj(P,(C,D#rev Cs'))"
  by - (rule isSubobj_isSubobj_isSubobj_rev)
with Cs' show ?thesis by simp
qed



subsection {* Subobject handling and lemmas *}

consts
  Subobjs\<^isub>R :: "prog \<Rightarrow> subobj set"
  Subobjs :: "prog \<Rightarrow> subobj set"

text{* Subobjects consisting of repeated inheritance relations only: *}

inductive "Subobjs\<^isub>R P"
intros
SubobjsR_Base: "is_class P C \<Longrightarrow> (C,[C]) \<in> Subobjs\<^isub>R P"
SubobjsR_Rep: "\<lbrakk>P \<turnstile> C \<prec>\<^sub>R D; (D, Cs) \<in> Subobjs\<^isub>R P\<rbrakk> \<Longrightarrow> (C, C # Cs) \<in> Subobjs\<^isub>R P"

text{* All subobjects: *}

inductive "Subobjs P"
intros
Subobjs_Rep: "(C, Cs) \<in> Subobjs\<^isub>R P \<Longrightarrow> (C, Cs) \<in> Subobjs P"
Subobjs_Sh: "\<lbrakk>P \<turnstile> C \<preceq>\<^sup>* C'; P \<turnstile> C' \<prec>\<^sub>S D; (D, Cs) \<in> Subobjs\<^isub>R P\<rbrakk>
             \<Longrightarrow> (C, Cs) \<in> Subobjs P"


lemma Subobjs_Base:"is_class P C \<Longrightarrow> (C,[C]) \<in> Subobjs P"
by (fastsimp intro:Subobjs_Rep SubobjsR_Base)

lemma SubobjsR_nonempty: "(C,Cs) \<in> Subobjs\<^isub>R P \<Longrightarrow> Cs \<noteq> []"
by (induct rule: Subobjs\<^isub>R.induct, simp_all)

lemma Subobjs_nonempty: "(C,Cs) \<in> Subobjs P \<Longrightarrow> Cs \<noteq> []"
by (erule Subobjs.induct)(erule SubobjsR_nonempty)+


lemma hd_SubobjsR:
  "(C,Cs) \<in> Subobjs\<^isub>R P \<Longrightarrow> \<exists>Cs'. Cs = C#Cs'"
by(erule Subobjs\<^isub>R.induct,simp+)


lemma SubobjsR_subclassRep: 
  "(C,Cs) \<in> Subobjs\<^isub>R P \<Longrightarrow> (C,last Cs) \<in> (subclsR P)\<^sup>*"

apply(erule Subobjs\<^isub>R.induct)
 apply simp
apply(simp add: SubobjsR_nonempty)
done


lemma SubobjsR_subclass: "(C,Cs) \<in> Subobjs\<^isub>R P \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* last Cs"

apply(erule Subobjs\<^isub>R.induct)
 apply simp
apply(simp add: SubobjsR_nonempty)
apply(blast intro:subclsR_subcls1 rtrancl_trans)
done


lemma Subobjs_subclass: "(C,Cs) \<in> Subobjs P \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* last Cs"

apply(erule Subobjs.induct)
 apply(erule SubobjsR_subclass)
apply(erule rtrancl_trans)
apply(blast intro:subclsS_subcls1 SubobjsR_subclass rtrancl_trans)
done




lemma Subobjs_notSubobjsR:
  "\<lbrakk>(C,Cs) \<in> Subobjs P; (C,Cs) \<notin> Subobjs\<^isub>R P\<rbrakk>
\<Longrightarrow> \<exists>C' D. P \<turnstile> C \<preceq>\<^sup>* C' \<and> P \<turnstile> C' \<prec>\<^sub>S D \<and> (D, Cs) \<in> Subobjs\<^isub>R P"
apply (induct rule: Subobjs.induct)
 apply clarsimp
apply fastsimp
done



lemma assumes subo:"(hd (Cs@ C'#Cs'),Cs@ C'#Cs') \<in> Subobjs\<^isub>R P"
  shows SubobjsR_Subobjs:"(C',C'#Cs') \<in> Subobjs P"
  using subo
proof (induct Cs)
  case Nil
  thus ?case by -(frule hd_SubobjsR,fastsimp intro:Subobjs_Rep)
next
  case (Cons D Ds)
  have subo':"(hd ((D#Ds) @ C'#Cs'), (D#Ds) @ C'#Cs') \<in> Subobjs\<^isub>R P"
    and IH:"(hd (Ds @ C'#Cs'), Ds @ C'#Cs') \<in> Subobjs\<^isub>R P \<Longrightarrow> (C', C'#Cs') \<in> Subobjs P" .
  from subo' have "(hd (Ds @ C' # Cs'),Ds @ C' # Cs') \<in> Subobjs\<^isub>R P"
    apply -
    apply (drule Subobjs\<^isub>R.elims)
    apply auto
    apply (rename_tac D')
    apply (subgoal_tac "D' = hd (Ds @ C' # Cs')")
    apply (auto dest:hd_SubobjsR)
    done
  with IH show ?case by simp
qed

lemma Subobjs_Subobjs:"(C,Cs@ C'#Cs') \<in> Subobjs P \<Longrightarrow> (C',C'#Cs') \<in> Subobjs P"
  
  apply -
  apply (drule Subobjs.elims)
  apply auto
   apply (subgoal_tac "C = hd(Cs @ C' # Cs')")
    apply (fastsimp intro:SubobjsR_Subobjs)
   apply (fastsimp dest:hd_SubobjsR)
  apply (subgoal_tac "D = hd(Cs @ C' # Cs')")
   apply (fastsimp intro:SubobjsR_Subobjs)
  apply (fastsimp dest:hd_SubobjsR)
  done
  


lemma SubobjsR_isClass:
assumes subo:"(C,Cs) \<in> Subobjs\<^isub>R P"
shows "is_class P C"

using subo
proof (induct rule:Subobjs\<^isub>R.induct)
  case SubobjsR_Base thus ?case by assumption
next
  case SubobjsR_Rep thus ?case by (fastsimp intro:subclsR_subcls1 subcls1_class)
qed


lemma Subobjs_isClass:
assumes subo:"(C,Cs) \<in> Subobjs P"
shows "is_class P C"

using subo
proof (induct rule:Subobjs.induct)
  case Subobjs_Rep thus ?case by (rule SubobjsR_isClass)
next
  case (Subobjs_Sh C C' Cs D)
  have leq:"P \<turnstile> C \<preceq>\<^sup>* C'" and leqS:"P \<turnstile> C' \<prec>\<^sub>S D" .
  hence "(C,D) \<in> (subcls1 P)\<^sup>+" by (fastsimp intro:rtrancl_into_trancl1 subclsS_subcls1)
  thus ?case by (induct rule:trancl.induct, fastsimp intro:subcls1_class)
qed


lemma Subobjs_subclsR:
assumes subo:"(C,Cs@[D,D']@Cs') \<in> Subobjs P"
shows "P \<turnstile> D \<prec>\<^sub>R D'"

using subo
proof -
  from subo have "(D,D#D'#Cs') \<in> Subobjs P" by -(rule Subobjs_Subobjs,simp)
  then obtain C' where subo':"(C',D#D'#Cs') \<in> Subobjs\<^isub>R P"
    by (induct rule:Subobjs.induct,blast+)
  hence "C' = D" by -(drule hd_SubobjsR,simp)
  with subo' have "(D,D#D'#Cs') \<in> Subobjs\<^isub>R P" by simp
  thus ?thesis by (fastsimp elim:Subobjs\<^isub>R.elims dest:hd_SubobjsR)
qed




lemma assumes subo:"(hd Cs,Cs@[D]) \<in> Subobjs\<^isub>R P" and notempty:"Cs \<noteq> []"
  shows butlast_Subobjs_Rep:"(hd Cs,Cs) \<in> Subobjs\<^isub>R P"
using subo notempty
proof (induct Cs)
  case Nil thus ?case by simp
next
  case (Cons C' Cs')
  have subo:"(hd(C'#Cs'), (C'#Cs')@[D]) \<in> Subobjs\<^isub>R P"
    and IH:"\<lbrakk>(hd Cs',Cs'@[D]) \<in> Subobjs\<^isub>R P; Cs' \<noteq> []\<rbrakk> \<Longrightarrow> (hd Cs',Cs') \<in> Subobjs\<^isub>R P" .
  from subo have subo':"(C',C'#Cs'@[D]) \<in> Subobjs\<^isub>R P" by simp
  show ?case
  proof (cases "Cs' = []")
    case True
    with subo' have "(C',[C',D]) \<in> Subobjs\<^isub>R P" by simp
    hence "is_class P C'" by(rule SubobjsR_isClass)
    hence "(C',[C']) \<in> Subobjs\<^isub>R P" by (rule SubobjsR_Base)
    with True show ?thesis by simp
  next
    case False
    with subo' obtain D' where subo'':"(D',Cs'@[D]) \<in> Subobjs\<^isub>R P"
      and subR:"P \<turnstile> C' \<prec>\<^sub>R D'"
      by (auto elim:Subobjs\<^isub>R.elims)
    from False subo'' have hd:"D' = hd Cs'"
      by (induct Cs',auto dest:hd_SubobjsR)
    with subo'' False IH have "(hd Cs',Cs') \<in> Subobjs\<^isub>R P" by simp 
    with subR hd have "(C',C'#Cs') \<in> Subobjs\<^isub>R P" by (fastsimp intro:SubobjsR_Rep)
    thus ?thesis by simp
  qed
qed



lemma assumes subo:"(C,Cs@[D]) \<in> Subobjs P" and notempty:"Cs \<noteq> []"
  shows butlast_Subobjs:"(C,Cs) \<in> Subobjs P"

using subo
proof (rule Subobjs.elims,auto)
  assume suboR:"(C,Cs@[D]) \<in> Subobjs\<^isub>R P" and "(C,Cs@[D]) \<in> Subobjs P"
  from suboR notempty have hd:"C = hd Cs"
    by (induct Cs,auto dest:hd_SubobjsR)
  with suboR notempty have "(hd Cs,Cs) \<in> Subobjs\<^isub>R P"
    by(fastsimp intro:butlast_Subobjs_Rep)
  with hd show "(C,Cs) \<in> Subobjs P" by (fastsimp intro:Subobjs_Rep)
next
  fix C' D' assume leq:"P \<turnstile> C \<preceq>\<^sup>* C'" and subS:"P \<turnstile> C' \<prec>\<^sub>S D'"
  and suboR:"(D',Cs@[D]) \<in> Subobjs\<^isub>R P" and "(C,Cs@[D]) \<in> Subobjs P"
  from suboR notempty have hd:"D' = hd Cs"
    by (induct Cs,auto dest:hd_SubobjsR)
  with suboR notempty have "(hd Cs,Cs) \<in> Subobjs\<^isub>R P"
    by(fastsimp intro:butlast_Subobjs_Rep)
  with hd leq subS show "(C,Cs) \<in> Subobjs P"
    by(fastsimp intro:Subobjs_Sh)
qed




lemma assumes subo:"(C,Cs@(rev Cs')) \<in> Subobjs P" and notempty:"Cs \<noteq> []"
  shows rev_appendSubobj:"(C,Cs) \<in> Subobjs P"
using subo
proof(induct Cs')
  case Nil thus ?case by simp
next
  case (Cons D Ds)
  have subo':"(C,Cs@rev(D#Ds)) \<in> Subobjs P"
    and IH:"(C,Cs@rev Ds) \<in> Subobjs P \<Longrightarrow> (C,Cs) \<in> Subobjs P" .
  from notempty subo' have "(C,Cs@rev Ds) \<in> Subobjs P"
    by (fastsimp intro:butlast_Subobjs)
  with IH show ?case by simp
qed



lemma appendSubobj:
assumes subo:"(C,Cs@Cs') \<in> Subobjs P" and notempty:"Cs \<noteq> []"
shows "(C,Cs) \<in> Subobjs P"

proof -
  obtain Cs'' where Cs'':"Cs'' = rev Cs'" by simp
  with subo have "(C,Cs@(rev Cs'')) \<in> Subobjs P" by simp
  with notempty show ?thesis by - (rule rev_appendSubobj)
qed




lemma SubobjsR_isSubobj:
  "(C,Cs) \<in> Subobjs\<^isub>R P \<Longrightarrow> is_subobj(P,(C,Cs))"
by(erule Subobjs\<^isub>R.induct,simp,
  auto dest:hd_SubobjsR intro:build_rec_isSubobj)

lemma leq_SubobjsR_isSubobj:
  "\<lbrakk>P \<turnstile> C \<preceq>\<^sup>* C'; P \<turnstile> C' \<prec>\<^sub>S D; (D,Cs) \<in> Subobjs\<^isub>R P\<rbrakk> 
\<Longrightarrow> is_subobj (P,(C,Cs))"

apply (subgoal_tac "is_subobj(P,(C,[D]))")
 apply (frule hd_SubobjsR)
 apply (drule SubobjsR_isSubobj)
 apply (erule exE)
 apply (simp del:is_subobj.simps)
 apply (erule isSubobj_isSubobj_isSubobj)
 apply simp
apply auto
done


lemma Subobjs_isSubobj:
  "(C,Cs) \<in> Subobjs P \<Longrightarrow> is_subobj(P,(C,Cs))"
by (auto elim:Subobjs.induct SubobjsR_isSubobj 
  simp add:leq_SubobjsR_isSubobj)



subsection {* Paths *}


subsubsection {* Appending paths *}

text{* Avoided name clash by calling one path Path. *}

constdefs
  path_via    :: "prog \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> path \<Rightarrow> bool"
      ("_ \<turnstile> Path _ to _ via _ " [51,51,51,51] 50)
  "P \<turnstile> Path C to D via Cs \<equiv> (C,Cs) \<in> Subobjs P \<and> last Cs = D"

  path_unique :: "prog \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> bool"
      ("_ \<turnstile> Path _ to _ unique" [51,51,51] 50)
  "P \<turnstile> Path C to D unique \<equiv> \<exists>!Cs. (C,Cs) \<in> Subobjs P \<and> last Cs = D"

  appendPath :: "path \<Rightarrow> path \<Rightarrow> path"  (infixr "@\<^sub>p" 65)
	"Cs @\<^sub>p Cs' \<equiv> if (last Cs = hd Cs') then Cs @ (tl Cs') else Cs'"


lemma appendPath_last: "Cs \<noteq> [] \<Longrightarrow> last Cs = last (Cs'@\<^sub>pCs)"
by(auto simp:appendPath_def last_append)(cases Cs, simp_all)+



consts
  casts_to :: "prog \<Rightarrow> (ty \<times> val \<times> val) set"

syntax
  casts_to :: "prog \<Rightarrow> ty \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool"
    ("_ \<turnstile> _ casts _ to _ " [51,51,51,51] 50)

translations
  "P \<turnstile> T casts v to v'" == "(T,v,v') \<in> casts_to P"


inductive "casts_to P"
intros

casts_prim: "\<forall>C. T \<noteq> Class C \<Longrightarrow> P \<turnstile> T casts v to v"

casts_null: "P \<turnstile> Class C casts Null to Null"

casts_ref: "\<lbrakk> P \<turnstile> Path last Cs to C via Cs'; Ds = Cs@\<^sub>pCs' \<rbrakk>
\<Longrightarrow> P \<turnstile> Class C casts Ref(a,Cs) to Ref(a,Ds)"


consts
  Casts_to :: "prog \<Rightarrow> (ty list \<times> val list \<times> val list) set"

syntax
  Casts_to :: "prog \<Rightarrow> ty list \<Rightarrow> val list \<Rightarrow> val list \<Rightarrow> bool"
    ("_ \<turnstile> _ Casts _ to _ " [51,51,51,51] 50)

translations
  "P \<turnstile> Ts Casts vs to vs'" == "(Ts,vs,vs') \<in> Casts_to P"


inductive "Casts_to P"
intros

Casts_Nil: "P \<turnstile> [] Casts [] to []"

Casts_Cons: "\<lbrakk> P \<turnstile> T casts v to v'; P \<turnstile> Ts Casts vs to vs' \<rbrakk>
\<Longrightarrow> P \<turnstile> (T#Ts) Casts (v#vs) to (v'#vs')"



lemma length_Casts_vs:
  "P \<turnstile> Ts Casts vs to vs' \<Longrightarrow> length Ts = length vs"
by (induct rule:Casts_to.induct,simp_all)

lemma length_Casts_vs':
  "P \<turnstile> Ts Casts vs to vs' \<Longrightarrow> length Ts = length vs'"
by (induct rule:Casts_to.induct,simp_all)



subsubsection {* The relation on paths *}

consts 
  leq_path1 :: "prog \<Rightarrow> cname \<Rightarrow> (path \<times> path) set" 

syntax (xsymbols)
  "_leq_path1" :: "prog \<Rightarrow> cname \<Rightarrow> [path, path] \<Rightarrow> bool" ("_,_ \<turnstile> _ \<sqsubset>\<^sup>1 _" [71,71,71] 70)
  "_leq_path"  :: "prog \<Rightarrow> cname \<Rightarrow> [path, path] \<Rightarrow> bool" ("_,_ \<turnstile> _ \<sqsubseteq> _"  [71,71,71] 70)

translations
  "P,C \<turnstile> Cs \<sqsubset>\<^sup>1 Ds" == "(Cs,Ds) \<in> leq_path1 P C"
  "P,C \<turnstile> Cs \<sqsubseteq> Ds" == "(Cs,Ds) \<in> (leq_path1 P C)\<^sup>*"
  "\<not> P,C \<turnstile> Cs \<sqsubseteq> Ds" <= "(Cs,Ds) \<notin> (leq_path1 P C)\<^sup>*"

inductive "leq_path1 P C"
intros
leq_pathRep: "\<lbrakk> (C,Cs) \<in> Subobjs P; (C,Ds) \<in> Subobjs P; Cs = butlast Ds\<rbrakk> 
\<Longrightarrow> P,C \<turnstile> Cs \<sqsubset>\<^sup>1 Ds"
leq_pathSh:  "\<lbrakk> (C,Cs) \<in> Subobjs P; P \<turnstile> last Cs \<prec>\<^sub>S D \<rbrakk> 
\<Longrightarrow> P,C \<turnstile> Cs \<sqsubset>\<^sup>1 [D]"


lemma leq_path_rep:
  "\<lbrakk> (C,Cs@[C']) \<in> Subobjs P; (C,Cs@[C',C'']) \<in> Subobjs P\<rbrakk> 
\<Longrightarrow> P,C \<turnstile> (Cs@[C']) \<sqsubset>\<^sup>1 (Cs@[C',C''])"
by(rule leq_pathRep,simp_all add:butlast_tail)

lemma leq_path_sh:
  "\<lbrakk> (C,Cs@[C']) \<in> Subobjs P; P \<turnstile> C' \<prec>\<^sub>S C''\<rbrakk> 
\<Longrightarrow> P,C \<turnstile> (Cs@[C']) \<sqsubset>\<^sup>1 [C'']"
by(erule leq_pathSh)simp




subsection{* Member lookups *}

constdefs
  FieldDecls      :: "prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> (path \<times> ty) set"
  "FieldDecls P C F \<equiv> 
   {(Cs,T). (C,Cs) \<in> Subobjs P \<and> (\<exists>Bs fs ms. class P (last Cs) = Some(Bs,fs,ms)
                                    \<and> map_of fs F = Some T)}"

  LeastFieldDecl  :: "prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> ty \<Rightarrow> path \<Rightarrow> bool"
    ("_ \<turnstile> _ has least _:_ via _" [51,0,0,0,51] 50)
  "P \<turnstile> C has least F:T via Cs \<equiv>
   (Cs,T) \<in> FieldDecls P C F \<and>
   (\<forall>(Cs',T') \<in> FieldDecls P C F. P,C \<turnstile> Cs \<sqsubseteq> Cs')"



  MethodDefs     :: "prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> (path \<times> method)set"
  "MethodDefs P C M \<equiv>
   {(Cs,mthd). (C,Cs) \<in> Subobjs P \<and> (\<exists>Bs fs ms. class P (last Cs) = Some(Bs,fs,ms)
                                    \<and> map_of ms M = Some mthd)}"

  -- "needed for well formed criterion"
  HasMethodDef :: "prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> method \<Rightarrow> path \<Rightarrow> bool"
    ("_ \<turnstile> _ has _ = _ via _" [51,0,0,0,51] 50)
  "P \<turnstile> C has M = mthd via Cs \<equiv> (Cs,mthd) \<in> MethodDefs P C M"

  LeastMethodDef :: "prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> method \<Rightarrow> path \<Rightarrow> bool"
    ("_ \<turnstile> _ has least _ = _ via _" [51,0,0,0,51] 50)
  "P \<turnstile> C has least M = mthd via Cs \<equiv>
   (Cs,mthd) \<in> MethodDefs P C M \<and>
   (\<forall>(Cs',mthd') \<in> MethodDefs P C M. P,C \<turnstile> Cs \<sqsubseteq> Cs')"

  MinimalMethodDefs :: "prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> (path \<times> method)set"
  "MinimalMethodDefs P C M \<equiv> 
      {(Cs,mthd). (Cs,mthd) \<in> MethodDefs P C M \<and> 
         (\<forall>(Cs',mthd')\<in> MethodDefs P C M. P,C \<turnstile> Cs' \<sqsubseteq> Cs \<longrightarrow> Cs' = Cs)}"

  OverriderMethodDefs :: "prog \<Rightarrow> subobj \<Rightarrow> mname \<Rightarrow> (path \<times> method)set"
  "OverriderMethodDefs P R M \<equiv>
      {(Cs,mthd). \<exists>Cs' mthd'. P \<turnstile> (ldc R) has least M = mthd' via Cs' \<and>
                      (Cs,mthd) \<in> MinimalMethodDefs P (mdc R) M \<and> 
                      P,mdc R \<turnstile> Cs \<sqsubseteq> (snd R)@\<^sub>pCs'}"

  FinalOverriderMethodDef :: "prog \<Rightarrow> subobj \<Rightarrow> mname \<Rightarrow> method \<Rightarrow> path \<Rightarrow> bool"
    ("_ \<turnstile> _ has overrider _ = _ via _" [51,0,0,0,51] 50)
  "P \<turnstile> R has overrider M = mthd via Cs \<equiv> 
      (Cs,mthd) \<in> OverriderMethodDefs P R M \<and> 
      card(OverriderMethodDefs P R M) = 1"
      (*(\<forall>(Cs',mthd') \<in> OverriderMethodDefs P R M. Cs = Cs' \<and> mthd = mthd')"*)


consts
  SelectMethodDef :: "prog \<Rightarrow> (subobj \<times> mname \<times> method \<times> path) set" 

syntax
  SelectMethodDef :: "prog \<Rightarrow> subobj \<Rightarrow> mname \<Rightarrow> method \<Rightarrow> path \<Rightarrow> bool"
     ("_ \<turnstile> _ selects _ = _ via _" [51,0,0,0,51] 50)

translations
  "P \<turnstile> (C,Cs) selects M = mthd via Cs'" == "((C,Cs),M,mthd,Cs') \<in> SelectMethodDef P"

inductive "SelectMethodDef P"
intros

dyn_unique:
  "P \<turnstile> C has least M = mthd via Cs' \<Longrightarrow> P \<turnstile> (C,Cs) selects M = mthd via Cs'"

dyn_ambiguous:
  "\<lbrakk>\<forall>mthd Cs'. \<not> P \<turnstile> C has least M = mthd via Cs'; 
    P \<turnstile> (C,Cs) has overrider M = mthd via Cs'\<rbrakk>
\<Longrightarrow> P \<turnstile> (C,Cs) selects M = mthd via Cs'"



lemma sees_fields_fun:
  "(Cs,T) \<in> FieldDecls P C F \<Longrightarrow> (Cs,T') \<in> FieldDecls P C F \<Longrightarrow> T = T'"
by(fastsimp simp:FieldDecls_def)

lemma sees_field_fun:
  "\<lbrakk>P \<turnstile> C has least F:T via Cs; P \<turnstile> C has least F:T' via Cs\<rbrakk>
  \<Longrightarrow> T = T'"
by (fastsimp simp:LeastFieldDecl_def dest:sees_fields_fun)


lemma has_least_method_has_method:
  "P \<turnstile> C has least M = mthd via Cs \<Longrightarrow> P \<turnstile> C has M = mthd via Cs"
by (simp add:LeastMethodDef_def HasMethodDef_def)


lemma visible_methods_exist:
  "(Cs,mthd) \<in> MethodDefs P C M \<Longrightarrow>
  (\<exists>Bs fs ms. class P (last Cs) = Some(Bs,fs,ms) \<and> map_of ms M = Some mthd)"
by(auto simp:MethodDefs_def)


lemma sees_methods_fun:
  "(Cs,mthd) \<in> MethodDefs P C M \<Longrightarrow> (Cs,mthd') \<in> MethodDefs P C M \<Longrightarrow> mthd = mthd'"
by(fastsimp simp:MethodDefs_def)

lemma sees_method_fun:
  "\<lbrakk>P \<turnstile> C has least M = mthd via Cs; P \<turnstile> C has least M = mthd' via Cs\<rbrakk>
  \<Longrightarrow> mthd = mthd'"
by (fastsimp simp:LeastMethodDef_def dest:sees_methods_fun)


end
