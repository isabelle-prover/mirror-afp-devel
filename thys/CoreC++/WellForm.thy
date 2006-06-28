(*  Title:       CoreC++
    ID:          $Id: WellForm.thy,v 1.5 2006-06-28 09:09:19 wasserra Exp $
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Based on the Jinja theory Common/WellForm.thy by Tobias Nipkow 
*)


header {* Generic Well-formedness of programs *}

theory WellForm imports SystemClasses TypeRel WellType begin

text {*\noindent This theory defines global well-formedness conditions
for programs but does not look inside method bodies. Well-typing of 
expressions is defined elsewhere (in theory @{text WellType}). 

CoreC++ allows covariant return types *}


types wf_mdecl_test = "prog \<Rightarrow> cname \<Rightarrow> mdecl \<Rightarrow> bool"

constdefs
  wf_fdecl :: "prog \<Rightarrow> fdecl \<Rightarrow> bool"
  "wf_fdecl P \<equiv> \<lambda>(F,T). is_type P T"

  wf_mdecl :: "wf_mdecl_test \<Rightarrow> wf_mdecl_test"
  "wf_mdecl wf_md P C \<equiv> \<lambda>(M,Ts,T,mb).
  (\<forall>T\<in>set Ts. is_type P T) \<and> is_type P T \<and> T \<noteq> NT \<and> wf_md P C (M,Ts,T,mb)"

  wf_cdecl :: "wf_mdecl_test \<Rightarrow> prog \<Rightarrow> cdecl \<Rightarrow> bool"
  "wf_cdecl wf_md P  \<equiv>  \<lambda>(C,(Bs,fs,ms)).
  (\<forall>M mthd Cs. P \<turnstile> C has M = mthd via Cs \<longrightarrow> 
               (\<exists>mthd' Cs'. P \<turnstile> (C,Cs) has overrider M = mthd' via Cs')) \<and> 
  (\<forall>f\<in>set fs. wf_fdecl P f) \<and>  distinct_fst fs \<and>
  (\<forall>m\<in>set ms. wf_mdecl wf_md P C m) \<and>  distinct_fst ms \<and>
  (\<forall>D \<in> baseClasses Bs.
   is_class P D \<and> \<not> P \<turnstile> D \<preceq>\<^sup>* C \<and>
   (\<forall>(M,Ts,T,m)\<in>set ms.
      \<forall>Ts' T' m' Cs. P \<turnstile> D has M = (Ts',T',m') via Cs \<longrightarrow>
                     Ts' = Ts \<and> P \<turnstile> T \<le> T'))"

  wf_syscls :: "prog \<Rightarrow> bool"
  "wf_syscls P  \<equiv>  sys_xcpts \<subseteq> set(map fst P)"

  wf_prog :: "wf_mdecl_test \<Rightarrow> prog \<Rightarrow> bool"
  "wf_prog wf_md P \<equiv> wf_syscls P \<and> distinct_fst P \<and> 
                     (\<forall>c \<in> set P. wf_cdecl wf_md P c)"



subsection{* Well-formedness lemmas *}

lemma class_wf: 
  "\<lbrakk>class P C = Some c; wf_prog wf_md P\<rbrakk> \<Longrightarrow> wf_cdecl wf_md P (C,c)"

apply (unfold wf_prog_def class_def)
apply (fast dest: map_of_SomeD)
done



lemma is_class_xcpt:
  "\<lbrakk> C \<in> sys_xcpts; wf_prog wf_md P \<rbrakk> \<Longrightarrow> is_class P C"

  apply (simp add: wf_prog_def wf_syscls_def is_class_def class_def)
  apply (fastsimp intro!: map_of_SomeI)
  done



lemma is_type_pTs:
assumes "wf_prog wf_md P" and "(C,S,fs,ms) \<in> set P" and "(M,Ts,T,m) \<in> set ms"
shows "set Ts \<subseteq> types P"

proof
  from prems have "wf_mdecl wf_md P C (M,Ts,T,m)"
    by (unfold wf_prog_def wf_cdecl_def) auto
  hence "\<forall>t \<in> set Ts. is_type P t" by (unfold wf_mdecl_def) auto
  moreover fix t assume "t \<in> set Ts"
  ultimately have "is_type P t" by blast
  thus "t \<in> types P" ..
qed



subsection{* Well-formedness subclass lemmas *}

lemma subcls1_wfD:
  "\<lbrakk> P \<turnstile> C \<prec>\<^sup>1 D; wf_prog wf_md P \<rbrakk> \<Longrightarrow> D \<noteq> C \<and> (D,C) \<notin> (subcls1 P)\<^sup>+"

apply( frule r_into_trancl)
apply( drule subcls1D)
apply(clarify)
apply( drule (1) class_wf)
apply( unfold wf_cdecl_def baseClasses_def)
apply(force simp add: reflcl_trancl [THEN sym] simp del: reflcl_trancl)
done



lemma wf_cdecl_supD: 
  "\<lbrakk>wf_cdecl wf_md P (C,Bs,r); D \<in> baseClasses Bs\<rbrakk> \<Longrightarrow> is_class P D"
by (auto simp: wf_cdecl_def baseClasses_def)


lemma subcls_asym:
  "\<lbrakk> wf_prog wf_md P; (C,D) \<in> (subcls1 P)\<^sup>+ \<rbrakk> \<Longrightarrow> (D,C) \<notin> (subcls1 P)\<^sup>+"

apply(erule tranclE)
apply(fast dest!: subcls1_wfD )
apply(fast dest!: subcls1_wfD intro: trancl_trans)
done



lemma subcls_irrefl:
  "\<lbrakk> wf_prog wf_md P; (C,D) \<in> (subcls1 P)\<^sup>+ \<rbrakk> \<Longrightarrow> C \<noteq> D"

apply (erule trancl_trans_induct)
apply  (auto dest: subcls1_wfD subcls_asym)
done



lemma subcls_asym2:
  "\<lbrakk> (C,D) \<in> (subcls1 P)\<^sup>*; wf_prog wf_md P; (D,C) \<in> (subcls1 P)\<^sup>* \<rbrakk> \<Longrightarrow> C = D"

apply (induct rule:rtrancl.induct)
apply simp
apply (drule rtrancl_into_trancl1)
apply simp
apply (drule subcls_asym)
apply simp
apply (drule_tac a="c" and b="a" in rtrancl_is_eq_or_trancl)
apply simp
done



lemma acyclic_subcls1:
  "wf_prog wf_md P \<Longrightarrow> acyclic (subcls1 P)"

apply (unfold acyclic_def)
apply (fast dest: subcls_irrefl)
done



lemma wf_subcls1:
  "wf_prog wf_md P \<Longrightarrow> wf ((subcls1 P)\<inverse>)"

apply (rule finite_acyclic_wf)
apply ( subst finite_converse)
apply ( rule finite_subcls1)
apply (subst acyclic_converse)
apply (erule acyclic_subcls1)
done



lemma subcls_induct: 
  "\<lbrakk> wf_prog wf_md P; \<And>C. \<forall>D. (C,D) \<in> (subcls1 P)\<^sup>+ \<longrightarrow> Q D \<Longrightarrow> Q C \<rbrakk> \<Longrightarrow> Q C"

  (is "?A \<Longrightarrow> PROP ?P \<Longrightarrow> _")

proof -
  assume p: "PROP ?P"
  assume ?A thus ?thesis apply -
apply(drule wf_subcls1)
apply(drule wf_trancl)
apply(simp only: trancl_converse)
apply(erule_tac a = C in wf_induct)
apply(rule p)
apply(auto)
done
qed




subsection{* Well-formedness leq\_path lemmas *}

lemma last_leq_path:
assumes leq:"P,C \<turnstile> Cs \<sqsubset>\<^sup>1 Ds" and wf:"wf_prog wf_md P"
shows "P \<turnstile> last Cs \<prec>\<^sup>1 last Ds"

using leq
proof (induct rule:leq_path1.induct)
  fix Cs Ds assume suboCs:"(C, Cs) \<in> Subobjs P" and suboDs:"(C, Ds) \<in> Subobjs P"
  and butlast:"Cs = butlast Ds"
  from suboDs have notempty:"Ds \<noteq> []" by -(drule Subobjs_nonempty)
  with butlast have DsCs:"Ds = Cs @ [last Ds]" by simp
  from suboCs have notempty:"Cs \<noteq> []" by -(drule Subobjs_nonempty)
  with DsCs have "Ds = ((butlast Cs) @ [last Cs]) @ [last Ds]" by simp
  with suboDs have "(C,(butlast Cs) @ [last Cs,last Ds]) \<in> Subobjs P"
    by simp
  thus "P \<turnstile> last Cs \<prec>\<^sup>1 last Ds" by (fastsimp intro:subclsR_subcls1 Subobjs_subclsR)
next
  fix Cs D assume "P \<turnstile> last Cs \<prec>\<^sub>S D"
  thus "P \<turnstile> last Cs \<prec>\<^sup>1 last [D]" by (fastsimp intro:subclsS_subcls1)
qed



lemma last_leq_paths:
assumes leq:"(Cs,Ds) \<in> (leq_path1 P C)\<^sup>+" and wf:"wf_prog wf_md P"
shows "(last Cs,last Ds) \<in> (subcls1 P)\<^sup>+"

using leq
proof (induct rule:trancl.induct)
  fix Cs Ds assume "P,C \<turnstile> Cs \<sqsubset>\<^sup>1 Ds"
  thus "(last Cs, last Ds) \<in> (subcls1 P)\<^sup>+" using wf
    by (fastsimp intro:r_into_trancl elim:last_leq_path)
next
  fix Cs Cs' Ds assume "(last Cs, last Cs') \<in> (subcls1 P)\<^sup>+"
    and "P,C \<turnstile> Cs' \<sqsubset>\<^sup>1 Ds"
  thus "(last Cs, last Ds) \<in> (subcls1 P)\<^sup>+" using wf
    by (fastsimp dest:last_leq_path)
qed



lemma leq_path1_wfD:
"\<lbrakk> P,C \<turnstile> Cs \<sqsubset>\<^sup>1 Cs'; wf_prog wf_md P \<rbrakk> \<Longrightarrow> Cs \<noteq> Cs' \<and> (Cs',Cs) \<notin> (leq_path1 P C)\<^sup>+"

apply (rule conjI)
 apply (erule leq_path1.elims) 
  apply simp
  apply (drule_tac Cs="Ds" in Subobjs_nonempty)
  apply (rule butlast_noteq) apply assumption
 apply clarsimp
 apply (drule subclsS_subcls1)
 apply (drule subcls1_wfD) apply simp_all
apply clarsimp
apply (frule last_leq_path)
 apply simp
apply (drule last_leq_paths)
 apply simp
apply (drule_tac r="subcls1 P" in r_into_trancl)
apply (drule subcls_asym) 
apply auto
done



lemma leq_path_asym:
"\<lbrakk>(Cs,Cs') \<in> (leq_path1 P C)\<^sup>+; wf_prog wf_md P\<rbrakk> \<Longrightarrow> (Cs',Cs) \<notin> (leq_path1 P C)\<^sup>+"

apply(erule tranclE)
apply(fast dest!:leq_path1_wfD )
apply(fast dest!:leq_path1_wfD intro: trancl_trans)
done



lemma leq_path_asym2:"\<lbrakk>P,C \<turnstile> Cs \<sqsubseteq> Cs'; P,C \<turnstile> Cs' \<sqsubseteq> Cs; wf_prog wf_md P\<rbrakk> \<Longrightarrow> Cs = Cs'"

apply (induct rule:rtrancl.induct)
 apply simp
apply (drule rtrancl_into_trancl1)
 apply simp
apply (drule leq_path_asym)
 apply simp
apply (drule_tac a="c" and b="a" in rtrancl_is_eq_or_trancl)
apply simp
done



lemma leq_path_Subobjs:
"\<lbrakk>P,C \<turnstile> [C] \<sqsubseteq> Cs; is_class P C; wf_prog wf_md P\<rbrakk> \<Longrightarrow> (C,Cs) \<in> Subobjs P"
by (induct rule:rtrancl_induct,auto intro:Subobjs_Base elim!:leq_path1.elims,
         auto dest!:Subobjs_subclass intro!:Subobjs_Sh SubobjsR_Base dest!:subclsSD
              intro:wf_cdecl_supD class_wf ShBaseclass_isBaseclass subclsSI)


lemma path_hd_appendPath:
  assumes path:"P,C \<turnstile> Cs \<sqsubseteq> Cs'@\<^sub>pCs" and last:"last Cs' = hd Cs"
  and notemptyCs:"Cs \<noteq> []" and notemptyCs':"Cs' \<noteq> []" and wf:"wf_prog wf_md P"
  shows "Cs' = [hd Cs]"

using path
proof -
  from path notemptyCs last have path2:"P,C \<turnstile> Cs \<sqsubseteq> Cs'@ tl Cs"
    by (simp add:appendPath_def)
  thus ?thesis
  proof (auto dest!:rtrancl_is_eq_or_trancl)
    assume "Cs = Cs'@ tl Cs"
    with notemptyCs show "Cs' = [hd Cs]" by (rule app_hd_tl)
  next
    assume trancl:"(Cs,Cs'@ tl Cs) \<in> (leq_path1 P C)\<^sup>+"
    from notemptyCs' last have butlastLast:"Cs' = butlast Cs' @ [hd Cs]"
      by -(drule append_butlast_last_id,simp)
    with trancl have trancl':"(Cs, (butlast Cs' @ [hd Cs]) @ tl Cs) \<in> (leq_path1 P C)\<^sup>+"
      by simp
    from notemptyCs have "(butlast Cs' @ [hd Cs]) @ tl Cs = butlast Cs' @ Cs"
      by simp
    with trancl' have "(Cs, butlast Cs' @ Cs) \<in> (leq_path1 P C)\<^sup>+" by simp
    hence "(last Cs, last (butlast Cs' @ Cs)) \<in> (subcls1 P)\<^sup>+" using wf
      by (rule last_leq_paths)
    with notemptyCs have "(last Cs, last Cs) \<in> (subcls1 P)\<^sup>+"
      by -(drule_tac xs="butlast Cs'" in last_appendR,simp)
    with wf show ?thesis by (auto dest:subcls_irrefl)
  qed
qed




subsection{* Lemmas concerning Subobjs *}

lemma Subobj_last_isClass:"\<lbrakk>wf_prog wf_md P; (C,Cs) \<in> Subobjs P\<rbrakk> \<Longrightarrow> is_class P (last Cs)"

apply (frule Subobjs_isClass)
apply (drule Subobjs_subclass)
apply (drule rtrancl_is_eq_or_trancl)
apply (erule disjE)
 apply simp
apply (subgoal_tac "is_class P (last Cs)")
 apply simp
apply (erule trancl_induct)
 apply (fastsimp dest:subcls1D class_wf elim:wf_cdecl_supD)
apply (fastsimp dest:subcls1D class_wf elim:wf_cdecl_supD)
done



lemma converse_SubobjsR_Rep:
  "\<lbrakk>(C,Cs) \<in> Subobjs\<^isub>R P; P \<turnstile> last Cs \<prec>\<^sub>R C'; wf_prog wf_md P\<rbrakk> 
\<Longrightarrow> (C,Cs@[C']) \<in> Subobjs\<^isub>R P"

apply (induct rule:Subobjs\<^isub>R.induct)
 apply (frule subclsR_subcls1)
 apply (fastsimp dest!:subcls1D class_wf wf_cdecl_supD SubobjsR_Base SubobjsR_Rep)
apply (fastsimp elim:SubobjsR_Rep simp: SubobjsR_nonempty split:split_if_asm)
done



lemma converse_Subobjs_Rep:
  "\<lbrakk>(C,Cs) \<in> Subobjs P; P \<turnstile> last Cs \<prec>\<^sub>R C';  wf_prog wf_md P\<rbrakk> 
\<Longrightarrow> (C,Cs@[C']) \<in> Subobjs P"
by (induct rule:Subobjs.induct, fastsimp dest:converse_SubobjsR_Rep Subobjs_Rep, 
  fastsimp dest:converse_SubobjsR_Rep Subobjs_Sh)



lemma isSubobj_Subobjs_rev:
assumes subo:"is_subobj(P,(C,C'#rev Cs'))" and wf:"wf_prog wf_md P"
shows "(C,C'#rev Cs') \<in> Subobjs P"
using subo
proof (induct Cs')
  case Nil
  show ?case
  proof (cases "C=C'")
    case True
    have "is_subobj (P,(C,C'#rev []))" .
    with True have "is_subobj (P,(C,[C]))" by simp
    hence "is_class P C"
      by (fastsimp elim:converse_rtranclE dest:subclsS_subcls1 elim:subcls1_class)
    with True show ?thesis by (fastsimp intro:Subobjs_Base)
  next
    case False
    have "is_subobj (P,(C,C'#rev []))" .
    with False obtain D where sup:"P \<turnstile> C \<preceq>\<^sup>* D" and subS:"P \<turnstile> D \<prec>\<^sub>S C'"
      by fastsimp
    with wf have "is_class P C'"
      by (fastsimp dest:subclsS_subcls1 subcls1D class_wf elim:wf_cdecl_supD)
    hence "(C',[C']) \<in> Subobjs\<^isub>R P" by (fastsimp elim:SubobjsR_Base)
    with sup subS have "(C,[C']) \<in> Subobjs P" by -(erule Subobjs_Sh, simp)
    thus ?thesis by simp
  qed 
next 
  case (Cons C'' Cs'')
  have IH:"is_subobj (P,(C,C'#rev Cs'')) \<Longrightarrow> (C,C'#rev Cs'') \<in> Subobjs P"
    and subo:"is_subobj (P,(C,C'#rev(C''# Cs'')))" .
  obtain Ds' where Ds':"Ds' = rev Cs''" by simp
  obtain D Ds where DDs:"D#Ds = Ds'@[C'']" by (cases Ds') auto
  with Ds' subo have "is_subobj(P,(C,C'#D#Ds))" by simp
  hence subobl:"is_subobj(P,(C,butlast(C'#D#Ds)))" 
    and subRbl:"P \<turnstile> last(butlast(C'#D#Ds)) \<prec>\<^sub>R last(C'#D#Ds)" by simp+
  with DDs Ds' have "is_subobj(P,(C,C'#rev Cs''))" by (simp del:is_subobj.simps)
  with IH have suborev:"(C,C'#rev Cs'') \<in> Subobjs P" by simp
  from subRbl DDs Ds' have subR:"P \<turnstile> last(C'#rev Cs'') \<prec>\<^sub>R C''" by simp
  with suborev wf show ?case by (fastsimp dest:converse_Subobjs_Rep)
qed



lemma isSubobj_Subobjs:
assumes subo:"is_subobj(P,(C,Cs))" and wf:"wf_prog wf_md P"
shows "(C,Cs) \<in> Subobjs P"

using subo
proof (induct Cs)
  case Nil
  thus ?case by simp
next
  case (Cons C' Cs')
  have subo:"is_subobj(P,(C,C'#Cs'))" .
  obtain Cs'' where Cs'':"Cs'' = rev Cs'" by simp
  with subo have "is_subobj(P,(C,C'#rev Cs''))" by simp
  with wf have "(C,C'#rev Cs'') \<in> Subobjs P" by - (rule isSubobj_Subobjs_rev)
  with Cs'' show ?case by simp
qed



lemma isSubobj_eq_Subobjs:
  "wf_prog wf_md P \<Longrightarrow> is_subobj(P,(C,Cs)) = ((C,Cs) \<in> Subobjs P)"
by(auto elim:isSubobj_Subobjs Subobjs_isSubobj)



lemma subo_trans_subcls:
  assumes subo:"(C,Cs@ C'#rev Cs') \<in> Subobjs P"
  shows "\<forall>C'' \<in> set Cs'. (C',C'') \<in> (subcls1 P)\<^sup>+"

using subo
proof (induct Cs')
  case Nil
  thus ?case by simp
next
  case (Cons D Ds)
  have IH:"(C, Cs @ C' # rev Ds) \<in> Subobjs P \<Longrightarrow>
           \<forall>C''\<in>set Ds. (C', C'') \<in> (subcls1 P)\<^sup>+"
    and "(C, Cs @ C' # rev (D # Ds)) \<in> Subobjs P" .
  hence subo':"(C,Cs@ C'#rev Ds @ [D]) \<in> Subobjs P" by simp
  hence "(C,Cs@ C'#rev Ds) \<in> Subobjs P"
    by -(rule appendSubobj,simp_all)
  with IH have set:"\<forall>C''\<in>set Ds. (C', C'') \<in> (subcls1 P)\<^sup>+" by simp
  hence revset:"\<forall>C''\<in>set (rev Ds). (C', C'') \<in> (subcls1 P)\<^sup>+" by simp
  have "(C',D) \<in> (subcls1 P)\<^sup>+"
  proof (cases "Ds = []")
    case True
    with subo' have "(C,Cs@[C',D]) \<in> Subobjs P" by simp
    thus ?thesis
      by (fastsimp intro:trancl.intros subclsR_subcls1 Subobjs_subclsR)
  next
    case False
    with revset have hd:"(C',hd Ds) \<in> (subcls1 P)\<^sup>+"
      apply -
      apply (erule ballE)
       apply simp
      apply (simp add:in_set_conv_decomp)
      apply (erule_tac x="[]" in allE)
      apply (erule_tac x="tl Ds" in allE)
      apply simp
      done
    from False subo' have "(hd Ds,D) \<in> (subcls1 P)\<^sup>+"
      apply (cases Ds)
       apply simp
      apply simp
      apply (rule trancl.intros)
      apply (rule subclsR_subcls1)
      apply (rule_tac Cs="Cs @ C' # rev list" in Subobjs_subclsR)
      apply simp
      done
    with hd show ?thesis by (rule trancl_trans)
  qed
  with set show ?case by simp
qed



lemma unique1:
  assumes subo:"(C,Cs@ C'#Cs') \<in> Subobjs P" and wf:"wf_prog wf_md P"
  shows "C' \<notin> set Cs'"

proof -
  obtain Ds where Ds:"Ds = rev Cs'" by simp
  hence "(C,Cs@ C'#rev Ds) \<in> Subobjs P" by simp
  with Ds subo have "\<forall>C'' \<in> set Cs'. (C',C'') \<in> (subcls1 P)\<^sup>+"
    by (fastsimp dest:subo_trans_subcls)
  with wf have "\<forall>C'' \<in> set Cs'. C' \<noteq> C''"
    by (auto dest:subcls_irrefl)
  thus ?thesis by fastsimp
qed



lemma subo_subcls_trans:
  assumes subo:"(C,Cs@ C'#Cs') \<in> Subobjs P"
  shows "\<forall>C'' \<in> set Cs. (C'',C') \<in> (subcls1 P)\<^sup>+"

proof -
  from wf subo have "\<And>C''. C'' \<in> set Cs \<Longrightarrow> (C'',C') \<in> (subcls1 P)\<^sup>+"
    apply (auto simp:in_set_conv_decomp)
    apply (case_tac zs)
     apply (fastsimp intro:r_into_trancl' subclsR_subcls1 Subobjs_subclsR)
    apply simp
    apply (rule_tac b="a" in trancl_rtrancl_trancl)
     apply (fastsimp intro:r_into_trancl' subclsR_subcls1 Subobjs_subclsR)
    apply (subgoal_tac "P \<turnstile> a \<preceq>\<^sup>* last (a # list @ [C'])")
     apply simp
    apply (rule Subobjs_subclass)
    apply (rule_tac C="C" and Cs=" ys @[C'']" in Subobjs_Subobjs)
    apply (rule_tac Cs'="Cs'" in appendSubobj)
    apply simp_all
    done
  thus ?thesis by fastsimp
qed



lemma unique2:
  assumes subo:"(C,Cs@ C'#Cs') \<in> Subobjs P" and wf:"wf_prog wf_md P"
  shows "C' \<notin> set Cs"

proof -
  from subo wf have "\<forall>C'' \<in> set Cs. (C'',C') \<in> (subcls1 P)\<^sup>+"
    by (fastsimp dest:subo_subcls_trans)
  with wf have "\<forall>C'' \<in> set Cs. C' \<noteq> C''"
    by (auto dest:subcls_irrefl)
  thus ?thesis by fastsimp
qed




lemma mdc_hd_path:
assumes subo:"(C,Cs) \<in> Subobjs P" and set:"C \<in> set Cs" and wf:"wf_prog wf_md P"
shows "C = hd Cs"

proof -
  from subo set obtain Ds Ds' where Cs:"Cs = Ds@ C#Ds'"
    by (auto simp:in_set_conv_decomp)
  then obtain Cs' where Cs':"Cs' = rev Ds" by simp
  with Cs subo have subo':"(C,(rev Cs')@ C#Ds') \<in> Subobjs P" by simp
  thus ?thesis
  proof (cases Cs')
    case Nil
    with Cs Cs' show ?thesis by simp
  next
    case (Cons X Xs)
    with subo' have suboX:"(C,(rev Xs)@[X,C]@Ds') \<in> Subobjs P" by simp
    hence leq:"P \<turnstile> X \<prec>\<^sup>1 C"
      by (fastsimp intro:subclsR_subcls1 Subobjs_subclsR)
    from suboX wf have "P \<turnstile> C \<preceq>\<^sup>* last ((rev Xs)@[X])"
      by (fastsimp intro:Subobjs_subclass appendSubobj)
    with leq have "(C,C) \<in> (subcls1 P)\<^sup>+" by simp
    with wf show ?thesis by (fastsimp dest:subcls_irrefl)
  qed
qed



lemma mdc_eq_last:
  assumes subo:"(C,Cs) \<in> Subobjs P" and last:"last Cs = C" and wf:"wf_prog wf_md P"
shows "Cs = [C]"

proof -
  from subo have notempty:"Cs \<noteq> []" by - (drule Subobjs_nonempty)
  hence lastset:"last Cs \<in> set Cs"
    apply (auto simp add:in_set_conv_decomp)
    apply (rule_tac x="butlast Cs" in exI)
    apply (rule_tac x="[]" in exI)
    apply simp
    done
  with last have C:"C \<in> set Cs" by simp
  with subo wf have hd:"C = hd Cs" by -(rule mdc_hd_path)
  then obtain Cs' where Cs':"Cs' = tl Cs" by simp
  thus ?thesis
  proof (cases Cs')
    case Nil
    with hd subo Cs' show ?thesis by (fastsimp dest:Subobjs_nonempty hd_Cons_tl)
  next
    case (Cons D Ds)
    with Cs' hd notempty have Cs:"Cs=C#D#Ds" by simp
    with subo have "(C,C#D#Ds) \<in> Subobjs P" by simp
    with wf have notset:"C \<notin> set (D#Ds)" by -(rule_tac Cs="[]" in unique1,simp_all)
    from Cs last have "last Cs = last (D#Ds)" by simp
    hence "last Cs \<in> set (D#Ds)"
      apply (auto simp add:in_set_conv_decomp)
      apply (erule_tac x="butlast Ds" in allE)
      apply (erule_tac x="[]" in allE)
      apply simp
      done
    with last have "C \<in> set (D#Ds)" by simp
    with notset show ?thesis by simp
  qed
qed



lemma assumes leq:"P \<turnstile> C \<preceq>\<^sup>* D" and wf:"wf_prog wf_md P"
  shows subcls_leq_path:"\<exists>Cs. P,C \<turnstile> [C] \<sqsubseteq> Cs@[D]"

using leq
proof (induct rule:rtrancl.induct)
  fix C show "\<exists>Cs. P,C \<turnstile> [C] \<sqsubseteq> Cs@[C]" by (rule_tac x="[]" in exI,simp)
next
  fix C C' D assume leq':"P \<turnstile> C \<preceq>\<^sup>* C'" and IH:"\<exists>Cs. P,C \<turnstile> [C] \<sqsubseteq> Cs@[C']"
    and sub:"P \<turnstile> C' \<prec>\<^sup>1 D"
  from sub have "is_class P C'" by (rule subcls1_class)
  with leq' have "class": "is_class P C" by (rule subcls_is_class)
  from IH obtain Cs where steps:"P,C \<turnstile> [C] \<sqsubseteq> Cs@[C']" by auto
  hence subo:"(C,Cs@[C']) \<in> Subobjs P" using "class" wf 
    by (fastsimp intro:leq_path_Subobjs)
  { assume "P \<turnstile> C' \<prec>\<^sub>R D"
    with subo wf have "(C,Cs@[C',D]) \<in> Subobjs P"
      by (fastsimp dest:converse_Subobjs_Rep)
    with subo have "P,C \<turnstile> (Cs@[C']) \<sqsubset>\<^sup>1 (Cs@[C']@[D])"
      by (fastsimp intro:leq_path_rep) }
  moreover 
  { assume "P \<turnstile> C' \<prec>\<^sub>S D"
    with subo have "P,C \<turnstile> (Cs@[C']) \<sqsubset>\<^sup>1 [D]" by (rule leq_path_sh) }
  ultimately show "\<exists>Cs. P,C \<turnstile> [C] \<sqsubseteq> Cs@[D]" using sub steps
    apply (auto dest!:subcls1_subclsR_or_subclsS)
    apply (rule_tac x="Cs@[C']" in exI) apply simp
    apply (rule_tac x="[]" in exI) apply simp
    done
qed

    


lemma assumes subo:"(C,rev Cs) \<in> Subobjs P" and wf:"wf_prog wf_md P"
  shows subobjs_rel_rev:"P,C \<turnstile> [C] \<sqsubseteq> (rev Cs)"
using subo
proof (induct Cs)
  case Nil
  thus ?case by (fastsimp dest:Subobjs_nonempty)
next
  case (Cons C' Cs')
  have subo':"(C,rev (C'#Cs')) \<in> Subobjs P"
    and IH:"(C,rev Cs') \<in> Subobjs P \<Longrightarrow> P,C \<turnstile> [C] \<sqsubseteq> rev Cs'" .
  from subo' have "class": "is_class P C" by(rule Subobjs_isClass)
  show ?case
  proof (cases "Cs' = []")
    case True hence empty:"Cs' = []" .
    with subo' have subo'':"(C,[C']) \<in> Subobjs P" by simp
    thus ?thesis
    proof (cases "C = C'")
      case True
      with empty show ?thesis by simp
    next
      case False
      with subo'' obtain D D' where leq:"P \<turnstile> C \<preceq>\<^sup>* D" and subS:"P \<turnstile> D \<prec>\<^sub>S D'"
	and suboR:"(D',[C']) \<in> Subobjs\<^isub>R P"
	by (auto elim:Subobjs.elims dest:hd_SubobjsR)
      from suboR have C':"C' = D'" by (fastsimp dest:hd_SubobjsR)
      from leq wf obtain Ds where steps:"P,C \<turnstile> [C] \<sqsubseteq> Ds@[D]"
	by (auto dest:subcls_leq_path)
      hence suboSteps:"(C,Ds@[D]) \<in> Subobjs P" using "class" wf
	apply (induct rule:rtrancl_induct)
	 apply (erule Subobjs_Base)
	apply (auto elim!:leq_path1.elims)
	apply (subgoal_tac "(D,[D]) \<in> Subobjs\<^isub>R P")
	 apply (fastsimp dest:Subobjs_subclass intro:Subobjs_Sh)
	apply (fastsimp dest!:subclsSD intro:SubobjsR_Base wf_cdecl_supD 
	                                     class_wf ShBaseclass_isBaseclass)
	done
      hence step:"P,C \<turnstile> (Ds@[D]) \<sqsubset>\<^sup>1 [D']" using subS by (rule leq_path_sh)
      with steps empty False C' show ?thesis by simp
    qed
  next
    case False
    with subo' have subo'':"(C,rev Cs') \<in> Subobjs P"
      by (fastsimp intro:butlast_Subobjs)
    with IH have steps:"P,C \<turnstile> [C] \<sqsubseteq> rev Cs'" by simp
    from subo' subo'' have "P,C \<turnstile> rev Cs' \<sqsubset>\<^sup>1 rev (C'#Cs')"
      by (fastsimp intro:leq_pathRep)
    with steps show ?thesis by simp
  qed
qed



lemma subobjs_rel:
assumes subo:"(C,Cs) \<in> Subobjs P" and wf:"wf_prog wf_md P"
shows "P,C \<turnstile> [C] \<sqsubseteq> Cs"

proof -
  obtain Cs' where Cs':"Cs' = rev Cs" by simp
  with subo have "(C,rev Cs') \<in> Subobjs P" by simp
  hence "P,C \<turnstile> [C] \<sqsubseteq> rev Cs'" using wf by (rule subobjs_rel_rev)
  with Cs' show ?thesis by simp
qed



lemma assumes wf:"wf_prog wf_md P"
  shows leq_path_last:"\<lbrakk>P,C \<turnstile> Cs \<sqsubseteq> Cs'; last Cs = last Cs'\<rbrakk> \<Longrightarrow> Cs = Cs'"

proof(induct rule:rtrancl_induct)
  show "Cs = Cs" by simp
next
  fix Cs' Cs''
  assume leqs:"P,C \<turnstile> Cs \<sqsubseteq> Cs'" and leq:"P,C \<turnstile> Cs' \<sqsubset>\<^sup>1 Cs''"
    and last:"last Cs = last Cs''"
    and IH:"last Cs = last Cs' \<Longrightarrow> Cs = Cs'"
  from leq wf have sup1:"P \<turnstile> last Cs' \<prec>\<^sup>1 last Cs''"
    by(rule last_leq_path)
  { assume "Cs = Cs'"
    with last have eq:"last Cs'' = last Cs'" by simp
    with eq wf sup1 have "Cs = Cs''" by(fastsimp dest:subcls1_wfD) }
  moreover
  { assume "(Cs,Cs') \<in> (leq_path1 P C)\<^sup>+"
    hence sub:"(last Cs,last Cs') \<in> (subcls1 P)\<^sup>+" using wf
      by(rule last_leq_paths)
    with sup1 last have "(last Cs'',last Cs'') \<in> (subcls1 P)\<^sup>+" by simp
    with wf have "Cs = Cs''" by(fastsimp dest:subcls_irrefl) }
  ultimately show "Cs = Cs''" using leqs
    by(fastsimp dest:rtrancl_is_eq_or_trancl)
qed
 



subsection{* Well-formedness and appendPath *}


lemma appendPath1:
  "\<lbrakk>(C,Cs) \<in> Subobjs P; (last Cs,Ds) \<in> Subobjs P; last Cs \<noteq> hd Ds\<rbrakk>
\<Longrightarrow> (C,Ds) \<in> Subobjs P"

apply(subgoal_tac "(last Cs,Ds) \<notin> Subobjs\<^isub>R P")
 apply (subgoal_tac "\<exists>C' D. P \<turnstile> last Cs \<preceq>\<^sup>* C' \<and> P \<turnstile> C' \<prec>\<^sub>S D \<and> (D, Ds) \<in> Subobjs\<^isub>R P")
  apply clarsimp
  apply (drule Subobjs_subclass)
  apply (subgoal_tac "P \<turnstile> C \<preceq>\<^sup>* C'")
   apply (erule_tac C'="C'" and D="D" in Subobjs_Sh)
    apply simp
   apply simp
  apply fastsimp
 apply (erule Subobjs_notSubobjsR)
 apply simp
apply (fastsimp dest:hd_SubobjsR)
done
 



lemma appendPath2_rev:
assumes subo1:"(C,Cs) \<in> Subobjs P" and subo2:"(last Cs,last Cs#rev Ds) \<in> Subobjs P"
  and wf:"wf_prog wf_md P"
shows "(C,Cs@(tl (last Cs#rev Ds))) \<in> Subobjs P"
using subo2
proof (induct Ds)
case Nil
  thus ?case by simp
next
  case (Cons D' Ds')
  have IH:"(last Cs,last Cs#rev Ds') \<in> Subobjs P 
    \<Longrightarrow> (C,Cs@tl(last Cs#rev Ds')) \<in> Subobjs P"
    and subo:"(last Cs,last Cs#rev (D'#Ds')) \<in> Subobjs P" .
  from subo have "(last Cs,last Cs#rev Ds') \<in> Subobjs P"
    by (fastsimp intro:butlast_Subobjs)
  with IH have subo':"(C,Cs@tl(last Cs#rev Ds')) \<in> Subobjs P"
    by simp
  have last:"last(last Cs#rev Ds') = last (Cs@tl(last Cs#rev Ds'))"
    by (cases Ds')auto
  obtain C' Cs' where C':"C' = last(last Cs#rev Ds')" and
    "Cs' = butlast(last Cs#rev Ds')" by simp
  hence "Cs'@[C'] = last Cs#rev Ds'" by simp
  hence "last Cs#rev (D'#Ds') = Cs'@[C',D']" by simp
  with subo have "(last Cs,Cs'@[C',D']) \<in> Subobjs P" by (cases Cs') auto
  hence "P \<turnstile> C' \<prec>\<^sub>R D'" by - (rule Subobjs_subclsR,simp)
  with C' last have "P \<turnstile> last (Cs@tl(last Cs#rev Ds')) \<prec>\<^sub>R D'" by simp
  with subo' wf have "(C,(Cs@tl(last Cs#rev Ds'))@[D']) \<in> Subobjs P"
    by (erule_tac Cs="(Cs@tl(last Cs#rev Ds'))" in converse_Subobjs_Rep) simp
  thus ?case by simp
qed



lemma appendPath2:
assumes subo1:"(C,Cs) \<in> Subobjs P" and subo2:"(last Cs,Ds) \<in> Subobjs P" 
  and eq:"last Cs = hd Ds" and wf:"wf_prog wf_md P"
shows "(C,Cs@(tl Ds)) \<in> Subobjs P"

using subo2
proof (cases Ds)
  case Nil
  thus ?thesis by simp
next
  case (Cons D' Ds')
  with subo2 eq have subo:"(last Cs,last Cs#Ds') \<in> Subobjs P" by simp
  obtain Ds'' where Ds'':"Ds'' = rev Ds'" by simp
  with subo have "(last Cs,last Cs#rev Ds'') \<in> Subobjs P" by simp
  with subo1 wf have "(C,Cs@(tl (last Cs#rev Ds''))) \<in> Subobjs P"
    by -(rule appendPath2_rev)
  with Ds'' eq Cons show ?thesis by simp
qed



lemma Subobjs_appendPath:
  "\<lbrakk>(C,Cs) \<in> Subobjs P; (last Cs,Ds) \<in> Subobjs P;wf_prog wf_md P\<rbrakk>
\<Longrightarrow> (C,Cs@\<^sub>pDs) \<in> Subobjs P"
by(fastsimp elim:appendPath2 appendPath1 simp:appendPath_def)


subsection{* Path and program size *}

lemma assumes subo:"(C,Cs) \<in> Subobjs P" and wf:"wf_prog wf_md P"
  shows path_contains_classes:"\<forall>C' \<in> set Cs. is_class P C'"
using subo

proof clarsimp
  fix C' assume subo:"(C,Cs) \<in> Subobjs P" and set:"C' \<in> set Cs"
  from set obtain Ds Ds' where Cs:"Cs = Ds@C'#Ds'"
    by (fastsimp simp:in_set_conv_decomp)
  with Cs show "is_class P C'"
  proof (cases "Ds = []")
    case True
    with Cs subo have subo':"(C,C'#Ds') \<in> Subobjs P" by simp
    thus ?thesis by (rule Subobjs.elims,
      auto dest:hd_SubobjsR intro:SubobjsR_isClass)
  next
    case False
    then obtain C'' Cs'' where Cs'':"Cs'' = butlast Ds"
      and last:"C'' = last Ds" by auto
    with False have Ds:"Ds = Cs''@[C'']" by simp
    with Cs subo have subo':"(C,Cs''@[C'',C']@Ds') \<in> Subobjs P"
      by simp
    hence "P \<turnstile> C'' \<prec>\<^sub>R C'" by(fastsimp intro:isSubobjs_subclsR Subobjs_isSubobj)
    with wf show ?thesis
      by (fastsimp dest!:subclsRD
                   intro:wf_cdecl_supD class_wf RepBaseclass_isBaseclass subclsSI)
  qed
qed


lemma path_subset_classes:"\<lbrakk>(C,Cs) \<in> Subobjs P; wf_prog wf_md P\<rbrakk> 
  \<Longrightarrow> set Cs \<subseteq> {C. is_class P C}"
by (auto dest:path_contains_classes)


lemma assumes subo:"(C,rev Cs) \<in> Subobjs P" and wf:"wf_prog wf_md P"
  shows rev_path_distinct_classes:"distinct Cs"
  using subo
proof (induct Cs)
  case Nil thus ?case by(fastsimp dest:Subobjs_nonempty)
next
  case (Cons C' Cs')
  have subo':"(C,rev(C'#Cs')) \<in> Subobjs P"
    and IH:"(C,rev Cs') \<in> Subobjs P \<Longrightarrow> distinct Cs'" .
  show ?case
  proof (cases "Cs' = []")
    case True thus ?thesis by simp
  next
    case False
    hence rev:"rev Cs' \<noteq> []" by simp
    from subo' have subo'':"(C,rev Cs'@[C']) \<in> Subobjs P" by simp
    hence "(C,rev Cs') \<in> Subobjs P" using rev wf
      by(fastsimp dest:appendSubobj)
    with IH have dist:"distinct Cs'" by simp
    from subo'' wf have "C' \<notin> set (rev Cs')"
      by(fastsimp dest:unique2)
    with dist show ?thesis by simp
  qed
qed


lemma assumes subo:"(C,Cs) \<in> Subobjs P" and wf:"wf_prog wf_md P"
  shows path_distinct_classes:"distinct Cs"

proof -
  obtain Cs' where Cs':"Cs' = rev Cs" by simp
  with subo have "(C,rev Cs') \<in> Subobjs P" by simp
  with wf have "distinct Cs'"
    by -(rule rev_path_distinct_classes)
  with Cs' show ?thesis by simp
qed



lemma assumes wf:"wf_prog wf_md P" 
  shows prog_length:"length P = card {C. is_class P C}"

proof -
  from wf have dist_fst:"distinct_fst P" by (simp add:wf_prog_def)
  hence "distinct P" by (simp add:distinct_fst_def,induct P,auto)
  hence card_set:"card (set P) = length P" by (rule distinct_card)
  from dist_fst have set:"{C. is_class P C} = fst ` (set P)"
    by (simp add:is_class_def class_def,auto simp:distinct_fst_def,
      auto dest:map_of_eq_Some_iff intro!:image_eqI)
  from dist_fst have "card(fst ` (set P)) = card (set P)"
    by(auto intro:card_image simp:distinct_map distinct_fst_def)
  with card_set set show ?thesis by simp
qed




lemma assumes subo:"(C,Cs) \<in> Subobjs P" and wf:"wf_prog wf_md P"
  shows path_length:"length Cs \<le> length P"

proof -
  from subo wf have "distinct Cs" by (rule path_distinct_classes)
  hence card_eq_length:"card (set Cs) = length Cs" by (rule distinct_card)
  from subo wf have "card (set Cs) \<le> card {C. is_class P C}"
    by (auto dest:path_subset_classes intro:card_mono finite_is_class)
  with card_eq_length have "length Cs \<le> card {C. is_class P C}" by simp
  with wf show ?thesis by(fastsimp dest:prog_length)
qed



lemma empty_path_empty_set:"{Cs. (C,Cs) \<in> Subobjs P \<and> length Cs \<le> 0} = {}" 
by (auto dest:Subobjs_nonempty)

lemma split_set_path_length:"{Cs. (C,Cs) \<in> Subobjs P \<and> length Cs \<le> Suc(n)} = 
{Cs. (C,Cs) \<in> Subobjs P \<and> length Cs \<le> n} \<union> {Cs. (C,Cs) \<in> Subobjs P \<and> length Cs = Suc(n)}"
by auto

lemma empty_list_set:"{xs. set xs \<subseteq> F \<and> xs = []} = {[]}"
by auto

lemma suc_n_union_of_union:"{xs. set xs \<subseteq> F \<and> length xs = Suc n} = (UN x:F. UN xs : {xs. set xs \<le> F \<and> length xs = n}. {x#xs})"
by (auto simp:length_Suc_conv)

lemma max_length_finite_set:"finite F \<Longrightarrow> finite{xs. set xs <= F \<and> length xs = n}"
by(induct n,simp add:empty_list_set, simp add:suc_n_union_of_union)

lemma path_length_n_finite_set:
"wf_prog wf_md P \<Longrightarrow> finite{Cs. (C,Cs) \<in> Subobjs P \<and> length Cs = n}"
by (rule_tac B="{Cs. set Cs <= {C. is_class P C} \<and> length Cs = n}" in finite_subset,
  auto dest:path_contains_classes intro:max_length_finite_set simp:finite_is_class)

lemma path_finite_leq:
"wf_prog wf_md P \<Longrightarrow> finite{Cs. (C,Cs) \<in> Subobjs P \<and> length Cs \<le> length P}"
  by (induct "length P",simp only:empty_path_empty_set,
    auto intro:path_length_n_finite_set simp:split_set_path_length)



lemma path_finite:"wf_prog wf_md P \<Longrightarrow> finite{Cs. (C,Cs) \<in> Subobjs P}"
by (subgoal_tac "{Cs. (C,Cs) \<in> Subobjs P} = 
  {Cs. (C,Cs) \<in> Subobjs P \<and> length Cs \<le> length P}",
  auto intro:path_finite_leq path_length)




subsection{* Well-formedness and Path *}


lemma subo_no_path:
  assumes subo:"(C',Cs @ C#Cs') \<in> Subobjs P" and wf:"wf_prog wf_md P"
  and notempty:"Cs' \<noteq> []"
  shows "\<not> P \<turnstile> Path last Cs' to C via Ds"

proof
  assume "P \<turnstile> Path last Cs' to C via Ds"
  hence subo':"(last Cs',Ds) \<in> Subobjs P" and last:"last Ds = C"
    by (auto simp:path_via_def)
  hence notemptyDs:"Ds \<noteq> []" by -(drule Subobjs_nonempty)
  then obtain D' Ds' where D'Ds':"Ds = D'#Ds'" by(cases Ds)auto
  from subo have suboC:"(C,C#Cs') \<in> Subobjs P" by (rule Subobjs_Subobjs)
  with wf subo' notempty have suboapp:"(C,(C#Cs')@\<^sub>pDs) \<in> Subobjs P"
    by -(rule Subobjs_appendPath,simp_all)
  with notemptyDs last have last':"last ((C#Cs')@\<^sub>pDs) = C"
    by -(drule_tac Cs'="(C#Cs')" in appendPath_last,simp)
  from notemptyDs have "(C#Cs')@\<^sub>pDs \<noteq> []"
    by (simp add:appendPath_def)
  with last' have "C \<in> set ((C#Cs')@\<^sub>pDs)"
    apply (auto simp add:in_set_conv_decomp)
    apply (rule_tac x="butlast((C#Cs')@\<^sub>pDs)" in exI)
    apply (rule_tac x="[]" in exI)
    apply (drule append_butlast_last_id)
    apply simp
    done
  with suboapp wf have hd:"C = hd ((C#Cs')@\<^sub>pDs)" by -(rule  mdc_hd_path)
  thus "False"
  proof (cases "last (C#Cs') = hd Ds")
    case True
    hence eq:"(C#Cs')@\<^sub>pDs = (C#Cs')@(tl Ds)" by (simp add:appendPath_def)
    show ?thesis
    proof (cases Ds')
      case Nil
      with D'Ds' have Ds:"Ds = [D']" by simp
      with last have "C = D'" by simp
      with True notempty Ds have "last (C#Cs') = C" by simp
      with notempty have "last Cs' = C" by simp
      with notempty have Cset:"C \<in> set Cs'"
	apply (auto simp add:in_set_conv_decomp)
	apply (rule_tac x="butlast Cs'" in exI)
	apply (rule_tac x="[]" in exI)
	apply (drule append_butlast_last_id)
	apply simp
	done
      from subo wf have "C \<notin> set Cs'" by (rule unique1)
      with Cset show ?thesis by simp
    next
      case (Cons X Xs)
      with D'Ds' have tlnotempty:"tl Ds \<noteq> []" by simp
      with Cons last D'Ds' have "last (tl Ds) = C" by simp
      with tlnotempty have "C \<in> set (tl Ds)"
	apply (auto simp add:in_set_conv_decomp)
	apply (rule_tac x="butlast (tl Ds)" in exI)
	apply (rule_tac x="[]" in exI)
	apply (drule append_butlast_last_id)
	apply simp
	done
      hence Cset:"C \<in> set (Cs'@(tl Ds))" by simp
      from suboapp eq wf have "C \<notin> set (Cs'@(tl Ds))"
	by (subgoal_tac "(C,C#(Cs'@(tl Ds))) \<in> Subobjs P",
	  rule_tac Cs="[]" in unique1,simp_all)
      with Cset show ?thesis by simp
    qed
  next
    case False
    with notemptyDs have eq:"(C#Cs')@\<^sub>pDs = Ds" by (simp add:appendPath_def)
    with subo' last have lastleq:"P \<turnstile> last Cs' \<preceq>\<^sup>* C" 
      by (fastsimp dest:Subobjs_subclass)
    from notempty obtain X Xs where X:"X = last Cs'" and "Xs = butlast Cs'"
      by auto
    with notempty have XXs:"Cs' = Xs@[X]" by simp
    hence CleqX:"(C,X) \<in> (subcls1 P)\<^sup>+"
    proof (cases Xs)
      case Nil
      with suboC XXs have "(C,[C,X]) \<in> Subobjs P" by simp
      thus ?thesis
	apply -
	apply (rule r_into_trancl')
	apply (rule subclsR_subcls1)
	apply (rule_tac Cs="[]" in Subobjs_subclsR)
	apply simp
	done
    next
      case (Cons Y Ys)
      with suboC XXs have subo'':"(C,[C,Y]@Ys@[X]) \<in> Subobjs P" by simp
      hence plus:"(C,Y) \<in> (subcls1 P)\<^sup>+"
	apply -
	apply (rule r_into_trancl')
	apply (rule subclsR_subcls1)
	apply (rule_tac Cs="[]" in Subobjs_subclsR)
	apply simp
	done
      from subo'' have "P \<turnstile> Y \<preceq>\<^sup>* X"
	apply -
	apply (subgoal_tac "(C,[C]@Y#(Ys@[X])) \<in> Subobjs P")
	 apply (drule Subobjs_Subobjs)
	 apply (drule_tac C="Y" in Subobjs_subclass) apply simp_all
	done
      with plus show ?thesis by (fastsimp elim:trancl_rtrancl_trancl)
    qed
    from lastleq X have leq:"P \<turnstile> X \<preceq>\<^sup>* C" by simp
    with CleqX have "(C,C) \<in> (subcls1 P)\<^sup>+"
      by (rule trancl_rtrancl_trancl)
    with wf show ?thesis by (fastsimp dest:subcls_irrefl)
  qed
qed



lemma leq_implies_path:
  assumes leq:"P \<turnstile> C \<preceq>\<^sup>* D" and "class": "is_class P C"
  and wf:"wf_prog wf_md P"
shows "\<exists>Cs. P \<turnstile> Path C to D via Cs"

using leq "class"
proof(induct rule:rtrancl.induct)
  fix C assume "is_class P C"
  thus "\<exists>Cs. P \<turnstile> Path C to C via Cs"
    by (rule_tac x="[C]" in exI,fastsimp intro:Subobjs_Base simp:path_via_def)
next
  fix C C' D assume CleqC':"P \<turnstile> C \<preceq>\<^sup>* C'" and C'leqD:"P \<turnstile> C' \<prec>\<^sup>1 D"
    and classC:"is_class P C" and IH:"is_class P C \<Longrightarrow> \<exists>Cs. P \<turnstile> Path C to C' via Cs"
  from IH[OF classC] obtain Cs where subo:"(C,Cs) \<in> Subobjs P" and last:"last Cs = C'"
    by (auto simp:path_via_def)
  with C'leqD show "\<exists>Cs. P \<turnstile> Path C to D via Cs"
  proof (auto dest!:subcls1_subclsR_or_subclsS)
    assume "P \<turnstile> last Cs \<prec>\<^sub>R D"
    with subo have "(C,Cs@[D]) \<in> Subobjs P" using wf
      by (rule converse_Subobjs_Rep)
    thus ?thesis by (fastsimp simp:path_via_def)
  next
    assume subS:"P \<turnstile> last Cs \<prec>\<^sub>S D"
    from CleqC' last have Cleqlast:"P \<turnstile> C \<preceq>\<^sup>* last Cs" by simp
    from subS have classLast:"is_class P (last Cs)"
      by (auto intro:subcls1_class subclsS_subcls1)
    then obtain Bs fs ms where "class P (last Cs) = Some(Bs,fs,ms)"
      by (fastsimp simp:is_class_def)
    hence classD:"is_class P D" using subS wf
      by (auto intro:wf_cdecl_supD dest:class_wf dest!:subclsSD 
	       elim:ShBaseclass_isBaseclass)
    with Cleqlast subS have "(C,[D]) \<in> Subobjs P"
      by (fastsimp intro:Subobjs_Sh SubobjsR_Base)
    thus ?thesis by (fastsimp simp:path_via_def)
  qed
qed


lemma least_method_implies_path_unique:
assumes least:"P \<turnstile> C has least M = (Ts,T,m) via Cs" and wf:"wf_prog wf_md P"
shows "P \<turnstile> Path C to (last Cs) unique"

proof (auto simp add:path_unique_def)
  (* Existence *)
  from least have "(C,Cs) \<in> Subobjs P"
    by (simp add:LeastMethodDef_def MethodDefs_def)
  thus "\<exists>Cs'. (C,Cs') \<in> Subobjs P \<and> last Cs' = last Cs"
    by fastsimp
next
  (* Uniqueness *)
  fix Cs' Cs''
  assume suboCs':"(C,Cs') \<in> Subobjs P" and suboCs'':"(C,Cs'') \<in> Subobjs P"
    and lastCs':"last Cs' = last Cs" and lastCs'':"last Cs'' = last Cs"
  from suboCs' have notemptyCs':"Cs' \<noteq> []" by (rule Subobjs_nonempty)
  from suboCs'' have notemptyCs'':"Cs'' \<noteq> []" by (rule Subobjs_nonempty)
  from least have suboCs:"(C,Cs) \<in> Subobjs P"
    and all:"\<forall>Ds. (C,Ds) \<in> Subobjs P \<and> 
     (\<exists>Ts T m Bs ms. (\<exists>fs. class P (last Ds) = Some (Bs, fs, ms)) \<and> 
                 map_of ms M = Some(Ts,T,m)) \<longrightarrow> P,C \<turnstile> Cs \<sqsubseteq> Ds"
    by (auto simp:LeastMethodDef_def MethodDefs_def)
  from least obtain Bs fs ms T Ts m where 
    "class": "class P (last Cs) = Some(Bs, fs, ms)" and map:"map_of ms M = Some(Ts,T,m)"
    by (auto simp:LeastMethodDef_def MethodDefs_def)
  from suboCs' lastCs' "class" map all have pathCs':"P,C \<turnstile> Cs \<sqsubseteq> Cs'"
    by simp
  with wf lastCs' have eq:"Cs = Cs'" by(fastsimp intro:leq_path_last)
  from suboCs'' lastCs'' "class" map all have pathCs'':"P,C \<turnstile> Cs \<sqsubseteq> Cs''"
    by simp
  with wf lastCs'' have "Cs = Cs''" by(fastsimp intro:leq_path_last)
  with eq show "Cs' = Cs''" by simp
qed



lemma least_field_implies_path_unique:
assumes least:"P \<turnstile> C has least F:T via Cs" and wf:"wf_prog wf_md P"
shows "P \<turnstile> Path C to (hd Cs) unique"

proof (auto simp add:path_unique_def)
  (* Existence *)
  from least have "(C,Cs) \<in> Subobjs P"
    by (simp add:LeastFieldDecl_def FieldDecls_def)
  hence "(C,[hd Cs]@tl Cs) \<in> Subobjs P"
    by - (frule Subobjs_nonempty,simp)
  with wf have "(C,[hd Cs]) \<in> Subobjs P"
    by (fastsimp intro:appendSubobj)
  thus "\<exists>Cs'. (C,Cs') \<in> Subobjs P \<and> last Cs' = hd Cs"
    by fastsimp
next
  (* Uniqueness *)
  fix Cs' Cs''
  assume suboCs':"(C,Cs') \<in> Subobjs P" and suboCs'':"(C,Cs'') \<in> Subobjs P"
    and lastCs':"last Cs' = hd Cs" and lastCs'':"last Cs'' = hd Cs"
  from suboCs' have notemptyCs':"Cs' \<noteq> []" by (rule Subobjs_nonempty)
  from suboCs'' have notemptyCs'':"Cs'' \<noteq> []" by (rule Subobjs_nonempty)
  from least have suboCs:"(C,Cs) \<in> Subobjs P"
    and all:"\<forall>Ds. (C,Ds) \<in> Subobjs P \<and> 
     (\<exists>T Bs fs. (\<exists>ms. class P (last Ds) = Some (Bs, fs, ms)) \<and> 
                 map_of fs F = Some T) \<longrightarrow> P,C \<turnstile> Cs \<sqsubseteq> Ds"
    by (auto simp:LeastFieldDecl_def FieldDecls_def)
  from least obtain Bs fs ms T where 
    "class": "class P (last Cs) = Some(Bs, fs, ms)" and map:"map_of fs F = Some T"
    by (auto simp:LeastFieldDecl_def FieldDecls_def)
  from suboCs have notemptyCs:"Cs \<noteq> []" by (rule Subobjs_nonempty)
  from suboCs notemptyCs have suboHd:"(hd Cs,hd Cs#tl Cs) \<in> Subobjs P"
    by -(rule_tac C="C" and Cs="[]" in Subobjs_Subobjs,simp)
  with suboCs' notemptyCs lastCs' wf have suboCs'App:"(C,Cs'@\<^sub>pCs) \<in> Subobjs P"
    by -(rule Subobjs_appendPath,simp_all)
  from suboHd suboCs'' notemptyCs lastCs'' wf 
  have suboCs''App:"(C,Cs''@\<^sub>pCs) \<in> Subobjs P"
    by -(rule Subobjs_appendPath,simp_all)
  from suboCs'App all "class" map notemptyCs have pathCs':"P,C \<turnstile> Cs \<sqsubseteq> Cs'@\<^sub>pCs"
    by -(erule_tac x="Cs'@\<^sub>pCs" in allE,drule_tac Cs'="Cs'" in appendPath_last,simp)
  from suboCs''App all "class" map notemptyCs have pathCs'':"P,C \<turnstile> Cs \<sqsubseteq> Cs''@\<^sub>pCs"
    by -(erule_tac x="Cs''@\<^sub>pCs" in allE,drule_tac Cs'="Cs''" in appendPath_last,simp)
  from pathCs' lastCs' notemptyCs notemptyCs' wf have Cs':"Cs' = [hd Cs]"
    by (rule path_hd_appendPath)
  from pathCs'' lastCs'' notemptyCs notemptyCs'' wf have "Cs'' = [hd Cs]"
    by (rule path_hd_appendPath)
  with Cs' show "Cs' = Cs''" by simp
qed



lemma least_field_implies_path_via_hd: 
"\<lbrakk>P \<turnstile> C has least F:T via Cs; wf_prog wf_md P\<rbrakk> 
\<Longrightarrow> P \<turnstile> Path C to (hd Cs) via [hd Cs]"

apply (simp add:LeastFieldDecl_def FieldDecls_def)
apply clarsimp
apply (simp add:path_via_def)
apply (frule Subobjs_nonempty)
apply (rule_tac Cs'="tl Cs" in appendSubobj)
apply auto
done



lemma path_via_C: "\<lbrakk>P \<turnstile> Path C to C via Cs; wf_prog wf_md P\<rbrakk> \<Longrightarrow> Cs = [C]"
by (fastsimp intro:mdc_eq_last simp:path_via_def)


lemma path_C_to_C_unique:
"\<lbrakk>wf_prog wf_md P; is_class P C\<rbrakk> \<Longrightarrow> P \<turnstile> Path C to C unique"

apply (unfold path_unique_def)
apply (rule_tac a="[C]" in ex1I)
apply (auto intro:Subobjs_Base mdc_eq_last)
done


lemma leqR_SubobjsR:"\<lbrakk>(C,D) \<in> (subclsR P)\<^sup>*; is_class P C; wf_prog wf_md P\<rbrakk> 
\<Longrightarrow> \<exists>Cs. (C,Cs@[D]) \<in> Subobjs\<^isub>R P"

apply (induct rule:rtrancl_induct)
 apply (drule SubobjsR_Base)
 apply (rule_tac x="[]" in exI)
 apply simp
apply (auto dest:converse_SubobjsR_Rep)
done



lemma assumes path_unique:"P \<turnstile> Path C to D unique" and leq:"P \<turnstile> C \<preceq>\<^sup>* C'"
  and leqR:"(C',D) \<in> (subclsR P)\<^sup>*" and wf:"wf_prog wf_md P"
  shows "P \<turnstile> Path C to C' unique"

proof -
  from path_unique have "is_class P C"
    by (auto intro:Subobjs_isClass simp:path_unique_def)
  with leq wf obtain Cs where path_via:"P \<turnstile> Path C to C' via Cs"
    by (auto dest:leq_implies_path)
  with wf have classC':"is_class P C'"
    by (fastsimp intro:Subobj_last_isClass simp:path_via_def)
  with leqR wf obtain Cs' where subo:"(C',Cs') \<in> Subobjs\<^isub>R P" and last:"last Cs' = D"
    by (auto dest:leqR_SubobjsR)
  hence hd:"hd Cs' = C'"
    by (fastsimp dest:hd_SubobjsR)
  with path_via subo wf have suboApp:"(C,Cs@tl Cs') \<in> Subobjs P"
    by (auto dest!:Subobjs_Rep dest:Subobjs_appendPath 
                simp:path_via_def appendPath_def)
  hence last':"last (Cs@tl Cs') = D"
    proof (cases "tl Cs' = []")
      case True
      with subo hd last have "C' = D"
	by (subgoal_tac "Cs' = [C']",auto dest!:SubobjsR_nonempty hd_Cons_tl)
      with path_via have "last Cs = D"
	by (auto simp:path_via_def)
      with True show ?thesis by simp
    next
      case False
      from subo have Cs':"Cs' = hd Cs'#tl Cs'"
	by (auto dest:SubobjsR_nonempty)
      from False have "last(hd Cs'#tl Cs') = last (tl Cs')"
	by (rule last_ConsR)
      with False Cs' last show ?thesis by simp
    qed
  with path_unique suboApp 
  have all:"\<forall>Ds. (C,Ds) \<in> Subobjs P \<and> last Ds = D \<longrightarrow> Ds = Cs@tl Cs'"
    by (auto simp add:path_unique_def)
  { fix Cs'' assume path_via2:"P \<turnstile> Path C to C' via Cs''" and noteq:"Cs'' \<noteq> Cs"
    with suboApp have "last (Cs''@tl Cs') = D"
    proof (cases "tl Cs' = []")
      case True
      with subo hd last have "C' = D"
	by (subgoal_tac "Cs' = [C']",auto dest!:SubobjsR_nonempty hd_Cons_tl)
      with path_via2 have "last Cs'' = D"
	by (auto simp:path_via_def)
      with True show ?thesis by simp
    next
      case False
      from subo have Cs':"Cs' = hd Cs'#tl Cs'"
	by (auto dest:SubobjsR_nonempty)
      from False have "last(hd Cs'#tl Cs') = last (tl Cs')"
	by (rule last_ConsR)
      with False Cs' last show ?thesis by simp
    qed
    with path_via2 noteq have False using all subo hd wf
      apply (auto simp:path_via_def)
      apply (drule Subobjs_Rep)
      apply (drule Subobjs_appendPath)
      apply (auto simp:appendPath_def)
      done }
  with path_via show ?thesis
    by (auto simp:path_via_def path_unique_def)
qed



subsection{* Well-formedness and member lookup *}

lemma has_path_has:
"\<lbrakk>P \<turnstile> Path D to C via Ds; P \<turnstile> C has M = (Ts,T,m) via Cs; wf_prog wf_md P\<rbrakk> 
  \<Longrightarrow> P \<turnstile> D has M = (Ts,T,m) via Ds@\<^sub>pCs"
by (clarsimp simp:HasMethodDef_def MethodDefs_def,frule Subobjs_nonempty,
         drule_tac Cs'="Ds" in appendPath_last,
         fastsimp intro:Subobjs_appendPath simp:path_via_def)


lemma has_least_wf_mdecl:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> C has least M = m via Cs \<rbrakk> 
\<Longrightarrow> wf_mdecl wf_md P (last Cs) (M,m)"
by(fastsimp dest:visible_methods_exist class_wf map_of_SomeD 
                 simp:LeastMethodDef_def wf_cdecl_def)



lemma has_overrider_wf_mdecl:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> (C,Cs) has overrider M = m via Cs' \<rbrakk> 
\<Longrightarrow> wf_mdecl wf_md P (last Cs') (M,m)"
by(fastsimp dest:visible_methods_exist map_of_SomeD class_wf
                 simp:FinalOverriderMethodDef_def OverriderMethodDefs_def 
                      MinimalMethodDefs_def wf_cdecl_def)


lemma select_method_wf_mdecl:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> (C,Cs) selects M = m via Cs' \<rbrakk> 
\<Longrightarrow> wf_mdecl wf_md P (last Cs') (M,m)"
by(fastsimp elim:SelectMethodDef.induct 
                 intro:has_least_wf_mdecl has_overrider_wf_mdecl)



lemma wf_sees_method_fun:
"\<lbrakk>P \<turnstile> C has least M = mthd via Cs; P \<turnstile> C has least M = mthd' via Cs'; 
  wf_prog wf_md P\<rbrakk>
  \<Longrightarrow> mthd = mthd' \<and> Cs = Cs'"

apply (auto simp:LeastMethodDef_def)
apply (erule_tac x="(Cs', mthd')" in ballE)
apply (erule_tac x="(Cs, mthd)" in ballE)
apply auto
apply (drule leq_path_asym2) apply simp_all
apply (rule sees_methods_fun) apply simp_all
apply (erule_tac x="(Cs', mthd')" in ballE)
apply (erule_tac x="(Cs, mthd)" in ballE)
apply (auto intro:leq_path_asym2)
done



lemma least_field_is_type:
assumes field:"P \<turnstile> C has least F:T via Cs" and wf:"wf_prog wf_md P"
shows "is_type P T"

proof -
  from field have "(Cs,T) \<in> FieldDecls P C F"
    by (simp add:LeastFieldDecl_def)
  from this obtain Bs fs ms 
    where "map_of fs F = Some T" 
    and "class": "class P (last Cs) = Some (Bs,fs,ms)"
    by (auto simp add:FieldDecls_def)
  hence "(F,T) \<in> set fs" by (simp add:map_of_SomeD)
  with "class" wf show ?thesis
    by(fastsimp dest!: class_wf simp: wf_cdecl_def wf_fdecl_def)
qed 



lemma least_method_is_type:
assumes method:"P \<turnstile> C has least M = (Ts,T,m) via Cs" and wf:"wf_prog wf_md P"
shows "is_type P T"

proof -
  from method have "(Cs,Ts,T,m) \<in> MethodDefs P C M"
    by (simp add:LeastMethodDef_def)
  from this obtain Bs fs ms 
    where "map_of ms M = Some(Ts,T,m)" 
    and "class": "class P (last Cs) = Some (Bs,fs,ms)"
    by (auto simp add:MethodDefs_def)
  hence "(M,Ts,T,m) \<in> set ms" by (simp add:map_of_SomeD)
  with "class" wf show ?thesis
    by(fastsimp dest!: class_wf simp: wf_cdecl_def wf_mdecl_def)
qed 



lemma least_overrider_is_type:
assumes method:"P \<turnstile> (C,Cs) has overrider M = (Ts,T,m) via Cs'" 
  and wf:"wf_prog wf_md P"
shows "is_type P T"

proof -
  from method have "(Cs',Ts,T,m) \<in> MethodDefs P C M"
    by(clarsimp simp:FinalOverriderMethodDef_def OverriderMethodDefs_def 
                     MinimalMethodDefs_def)
  from this obtain Bs fs ms 
    where "map_of ms M = Some(Ts,T,m)" 
    and "class": "class P (last Cs') = Some (Bs,fs,ms)"
    by (auto simp add:MethodDefs_def)
  hence "(M,Ts,T,m) \<in> set ms" by (simp add:map_of_SomeD)
  with "class" wf show ?thesis
    by(fastsimp dest!: class_wf simp: wf_cdecl_def wf_mdecl_def)
qed 



lemma select_method_is_type:
"\<lbrakk> P \<turnstile> (C,Cs) selects M = (Ts,T,m) via Cs'; wf_prog wf_md P\<rbrakk> \<Longrightarrow> is_type P T"
by(auto elim:SelectMethodDef.elims 
             intro:least_method_is_type least_overrider_is_type)


lemma base_subtype:
"\<lbrakk>wf_cdecl wf_md P (C,Bs,fs,ms); C' \<in> baseClasses Bs; 
  P \<turnstile> C' has M = (Ts',T',m') via Cs@\<^sub>p[D]; (M,Ts,T,m)\<in>set ms\<rbrakk>
  \<Longrightarrow> Ts' = Ts \<and> P \<turnstile> T \<le> T'"

apply (simp add:wf_cdecl_def)
apply clarsimp
apply (rotate_tac -1)
apply (erule_tac x="C'" in ballE)
 apply clarsimp
 apply (rotate_tac -1)
 apply (erule_tac x="(M, Ts, T, m)" in ballE)
  apply clarsimp
  apply (erule_tac x="Ts'" in allE)
  apply (erule_tac x="T'" in allE)
  apply (auto simp:HasMethodDef_def)
 apply (erule_tac x="fst m'" in allE)
 apply (erule_tac x="snd m'" in allE)
 apply (erule_tac x="Cs@\<^sub>p[D]" in allE)
 apply simp
apply (erule_tac x="fst m'" in allE)
apply (erule_tac x="snd m'" in allE)
apply (erule_tac x="Cs@\<^sub>p[D]" in allE)
apply simp
done



lemma subclsPlus_subtype:
  assumes classD:"class P D = Some(Bs',fs',ms')" 
  and mapMs':"map_of ms' M = Some(Ts',T',m')"
  and leq:"(C,D) \<in> (subcls1 P)\<^sup>+" and wf:"wf_prog wf_md P"
shows "\<forall>Bs fs ms Ts T m. class P C = Some(Bs,fs,ms) \<and> map_of ms M = Some(Ts,T,m) 
    \<longrightarrow> Ts' = Ts \<and> P \<turnstile> T \<le> T'"

using leq classD mapMs'
proof (erule_tac a="C" and b="D" in converse_trancl_induct)
  fix C
  assume CleqD:"P \<turnstile> C \<prec>\<^sup>1 D" and classD1:"class P D = Some(Bs',fs',ms')"
  { fix Bs fs ms Ts T m
    assume classC:"class P C = Some(Bs,fs,ms)" and mapMs:"map_of ms M = Some(Ts,T,m)"
    from classD1 mapMs' have hasViaD:"P \<turnstile> D has M = (Ts',T',m') via [D]"
      by (fastsimp intro:Subobjs_Base simp:HasMethodDef_def MethodDefs_def is_class_def)
    from CleqD classC have base:"D \<in> baseClasses Bs"
      by (fastsimp dest:subcls1D)
    from classC wf have cdecl:"wf_cdecl wf_md P (C,Bs,fs,ms)"
      by (rule class_wf)
    from classC mapMs have "(M,Ts,T,m)\<in>set ms"
      by -(drule map_of_is_SomeD)
    with cdecl base hasViaD have "Ts' = Ts \<and> P \<turnstile> T \<le> T'"
      by -(rule_tac Cs="[D]" in base_subtype,auto simp:appendPath_def) }
  thus "\<forall>Bs fs ms Ts T m. class P C = Some(Bs, fs, ms) \<and> map_of ms M = Some(Ts,T,m) 
             \<longrightarrow> Ts' = Ts \<and> P \<turnstile> T \<le> T'" by blast
next
  fix C C'
  assume  classD1:"class P D = Some(Bs',fs',ms')" and CleqC':"P \<turnstile> C \<prec>\<^sup>1 C'"
    and subcls:"(C',D) \<in> (subcls1 P)\<^sup>+"
    and IH:"\<forall>Bs fs ms Ts T m. class P C' = Some(Bs,fs,ms) \<and> 
                          map_of ms M = Some(Ts,T,m) \<longrightarrow> 
                  Ts' = Ts \<and> P \<turnstile> T \<le> T'"
  { fix Bs fs ms Ts T m
    assume classC:"class P C = Some(Bs,fs,ms)" and mapMs:"map_of ms M = Some(Ts,T,m)"
    from classD1 mapMs' have hasViaD:"P \<turnstile> D has M = (Ts',T',m') via [D]"
      by (fastsimp intro:Subobjs_Base simp:HasMethodDef_def MethodDefs_def is_class_def)
    from subcls have C'leqD:"P \<turnstile> C' \<preceq>\<^sup>* D" by simp
    from classC wf CleqC' have "is_class P C'"
      by (fastsimp intro:wf_cdecl_supD class_wf dest:subcls1D)
    with C'leqD wf obtain Cs where "P \<turnstile> Path C' to D via Cs"
      by (auto dest!:leq_implies_path simp:is_class_def)
    hence hasVia:"P \<turnstile> C' has M = (Ts',T',m') via Cs@\<^sub>p[D]" using hasViaD wf
      by (rule has_path_has)
    from CleqC' classC have base:"C' \<in> baseClasses Bs"
      by (fastsimp dest:subcls1D)
    from classC wf have cdecl:"wf_cdecl wf_md P (C,Bs,fs,ms)"
      by (rule class_wf)
    from classC mapMs have "(M,Ts,T,m)\<in>set ms"
      by -(drule map_of_is_SomeD)
    with cdecl base hasVia have "Ts' = Ts \<and> P \<turnstile> T \<le> T'"
      by(rule base_subtype) }
  thus "\<forall>Bs fs ms Ts T m. class P C = Some(Bs, fs, ms) \<and> map_of ms M = Some(Ts,T,m) 
             \<longrightarrow> Ts' = Ts \<and> P \<turnstile> T \<le> T'" by blast
qed



lemma leq_method_subtypes:
  assumes leq:"P \<turnstile> D \<preceq>\<^sup>* C" and least:"P \<turnstile> D has least M = (Ts',T',m') via Ds"
  and wf:"wf_prog wf_md P"
  shows "\<forall>Ts T m Cs. P \<turnstile> C has M = (Ts,T,m) via Cs \<longrightarrow> 
                       Ts = Ts' \<and> P \<turnstile> T' \<le> T"

using prems
proof (induct rule:rtrancl.induct)
  fix C
  assume Cleast:"P \<turnstile> C has least M = (Ts',T',m') via Ds"
  { fix Ts T m Cs
    assume Chas:"P \<turnstile> C has M = (Ts,T,m) via Cs"
    with Cleast have path:"P,C \<turnstile> Ds \<sqsubseteq> Cs"
      by (fastsimp simp:LeastMethodDef_def HasMethodDef_def)
    { assume "Ds = Cs"
      with Cleast Chas have "Ts = Ts' \<and> T' = T"
	by (auto simp:LeastMethodDef_def HasMethodDef_def MethodDefs_def)
      hence "Ts = Ts' \<and> P \<turnstile> T' \<le> T" by auto }
    moreover
    { assume "(Ds,Cs) \<in> (leq_path1 P C)\<^sup>+"
      hence subcls:"(last Ds,last Cs) \<in> (subcls1 P)\<^sup>+" using wf
	by -(rule last_leq_paths)
      from Chas obtain Bs fs ms where "class P (last Cs) = Some(Bs,fs,ms)" 
	and "map_of ms M = Some(Ts,T,m)"
	by (auto simp:HasMethodDef_def MethodDefs_def)
      hence ex:"\<forall>Bs' fs' ms' Ts' T' m'. class P (last Ds) = Some(Bs',fs',ms') \<and> 
        map_of ms' M = Some(Ts',T',m') \<longrightarrow> Ts = Ts' \<and> P \<turnstile> T' \<le> T"
	using subcls wf
	by -(rule subclsPlus_subtype,auto)
      from Cleast obtain Bs' fs' ms' where "class P (last Ds) = Some(Bs',fs',ms')" 
	and "map_of ms' M = Some(Ts',T',m')"
	by (auto simp:LeastMethodDef_def MethodDefs_def)
      with ex have "Ts = Ts'" and "P \<turnstile> T' \<le> T" by auto }
      ultimately have "Ts = Ts'" and "P \<turnstile> T' \<le> T" using path
	by (auto dest!:rtrancl_is_eq_or_trancl) }
  thus "\<forall>Ts T m Cs. P \<turnstile> C has M = (Ts, T, m) via Cs \<longrightarrow> 
                      Ts = Ts' \<and> P \<turnstile> T' \<le> T"
    by (simp add:HasMethodDef_def MethodDefs_def)
next
  fix D C' C
  assume DleqC':"P \<turnstile> D \<preceq>\<^sup>* C'" and C'leqC:"P \<turnstile> C' \<prec>\<^sup>1 C"
  and Dleast:"P \<turnstile> D has least M = (Ts',T',m') via Ds"
  and IH:"\<lbrakk>P \<turnstile> D has least M = (Ts',T',m') via Ds; wf_prog wf_md P\<rbrakk>
   \<Longrightarrow> \<forall>Ts T m Cs. P \<turnstile> C' has M = (Ts, T, m) via Cs \<longrightarrow> 
            Ts = Ts' \<and> P \<turnstile> T' \<le> T"
  { fix Ts T m Cs
    assume Chas:"P \<turnstile> C has M = (Ts,T,m) via Cs"
    from Dleast have classD:"is_class P D"
      by (auto intro:Subobjs_isClass simp:LeastMethodDef_def MethodDefs_def)
    from DleqC' C'leqC have "P \<turnstile> D \<preceq>\<^sup>* C" by simp
    then obtain Cs' where "P \<turnstile> Path D to C via Cs'" using classD wf
      by (auto dest:leq_implies_path)
    hence Dhas:"P \<turnstile> D has M = (Ts,T,m) via Cs'@\<^sub>pCs" using Chas wf
      by (fastsimp intro:has_path_has)
    with Dleast have path:"P,D \<turnstile> Ds \<sqsubseteq> Cs'@\<^sub>pCs"
      by (auto simp:LeastMethodDef_def HasMethodDef_def)
    { assume "Ds = Cs'@\<^sub>pCs"
      with Dleast Dhas have "Ts = Ts' \<and> T' = T"
	by (auto simp:LeastMethodDef_def HasMethodDef_def MethodDefs_def)
      hence "Ts = Ts' \<and> T' = T" by auto }
    moreover
    { assume "(Ds,Cs'@\<^sub>pCs) \<in> (leq_path1 P D)\<^sup>+"
      hence subcls:"(last Ds,last (Cs'@\<^sub>pCs)) \<in> (subcls1 P)\<^sup>+" using wf
	by -(rule last_leq_paths)
      from Dhas obtain Bs fs ms where "class P (last (Cs'@\<^sub>pCs)) = Some(Bs,fs,ms)" 
	and "map_of ms M = Some(Ts,T,m)"
	by (auto simp:HasMethodDef_def MethodDefs_def)
      hence ex:"\<forall>Bs' fs' ms' Ts' T' m'. class P (last Ds) = Some(Bs',fs',ms') \<and> 
                 map_of ms' M = Some(Ts',T',m') \<longrightarrow> 
	             Ts = Ts' \<and> P \<turnstile> T' \<le> T"
	using subcls wf
	by -(rule subclsPlus_subtype,auto)
      from Dleast obtain Bs' fs' ms' where "class P (last Ds) = Some(Bs',fs',ms')" 
	and "map_of ms' M = Some(Ts',T',m')"
	by (auto simp:LeastMethodDef_def MethodDefs_def)
      with ex have "Ts = Ts'" and "P \<turnstile> T' \<le> T" by auto }
    ultimately have "Ts = Ts'" and "P \<turnstile> T' \<le> T" using path
      by (auto dest!:rtrancl_is_eq_or_trancl) }
  thus "\<forall>Ts T m Cs. P \<turnstile> C has M = (Ts, T, m) via Cs \<longrightarrow> 
            Ts = Ts' \<and> P \<turnstile> T' \<le> T"
    by simp
qed



lemma leq_methods_subtypes:
  assumes leq:"P \<turnstile> D \<preceq>\<^sup>* C" and least:"(Ds,(Ts',T',m')) \<in> MinimalMethodDefs P D M"
  and wf:"wf_prog wf_md P"
  shows "\<forall>Ts T m Cs Cs'. P \<turnstile> Path D to C via Cs' \<and> P,D \<turnstile> Ds \<sqsubseteq> Cs'@\<^sub>pCs \<and> Cs \<noteq> [] \<and> 
                         P \<turnstile> C has M = (Ts,T,m) via Cs 
                                \<longrightarrow>  Ts = Ts' \<and> P \<turnstile> T' \<le> T"

using prems
proof (induct rule:rtrancl.induct)
  fix C
  assume Cleast:"(Ds,(Ts',T',m')) \<in> MinimalMethodDefs P C M"
  { fix Ts T m Cs Cs'
    assume path':"P \<turnstile> Path C to C via Cs'"
      and leq_path:"P,C \<turnstile> Ds \<sqsubseteq> Cs' @\<^sub>p Cs" and notempty:"Cs \<noteq> []"
      and Chas:"P \<turnstile> C has M = (Ts,T,m) via Cs"
    from path' wf have Cs':"Cs' = [C]" by(rule path_via_C)
    from leq_path Cs' notempty have leq':"P,C \<turnstile> Ds \<sqsubseteq> Cs"
      by(auto simp:appendPath_def split:split_if_asm)
    { assume "Ds = Cs"
      with Cleast Chas have "Ts = Ts' \<and> T' = T"
	by (auto simp:MinimalMethodDefs_def HasMethodDef_def MethodDefs_def)
      hence "Ts = Ts' \<and> P \<turnstile> T' \<le> T" by auto }
    moreover
    { assume "(Ds,Cs) \<in> (leq_path1 P C)\<^sup>+"
      hence subcls:"(last Ds,last Cs) \<in> (subcls1 P)\<^sup>+" using wf
	by -(rule last_leq_paths)
      from Chas obtain Bs fs ms where "class P (last Cs) = Some(Bs,fs,ms)" 
	and "map_of ms M = Some(Ts,T,m)"
	by (auto simp:HasMethodDef_def MethodDefs_def)
      hence ex:"\<forall>Bs' fs' ms' Ts' T' m'. class P (last Ds) = Some(Bs',fs',ms') \<and> 
        map_of ms' M = Some(Ts',T',m') \<longrightarrow> Ts = Ts' \<and> P \<turnstile> T' \<le> T"
	using subcls wf
	by -(rule subclsPlus_subtype,auto)
      from Cleast obtain Bs' fs' ms' where "class P (last Ds) = Some(Bs',fs',ms')" 
	and "map_of ms' M = Some(Ts',T',m')"
	by (auto simp:MinimalMethodDefs_def MethodDefs_def)
      with ex have "Ts = Ts'" and "P \<turnstile> T' \<le> T" by auto }
      ultimately have "Ts = Ts'" and "P \<turnstile> T' \<le> T" using leq'
	by (auto dest!:rtrancl_is_eq_or_trancl) }
  thus "\<forall>Ts T m Cs Cs'. P \<turnstile> Path C to C via Cs' \<and> P,C \<turnstile> Ds \<sqsubseteq> Cs' @\<^sub>p Cs \<and> Cs \<noteq> [] \<and> 
                        P \<turnstile> C has M = (Ts, T, m) via Cs \<longrightarrow> 
                            Ts = Ts' \<and> P \<turnstile> T' \<le> T" by blast
next
  fix D C' C
  assume DleqC':"P \<turnstile> D \<preceq>\<^sup>* C'" and C'leqC:"P \<turnstile> C' \<prec>\<^sup>1 C"
    and Dleast:"(Ds, Ts', T', m') \<in> MinimalMethodDefs P D M"
    and IH:"\<lbrakk>(Ds,Ts',T',m') \<in> MinimalMethodDefs P D M; wf_prog wf_md P\<rbrakk>
   \<Longrightarrow> \<forall>Ts T m Cs Cs'. P \<turnstile> Path D to C' via Cs' \<and>
              P,D \<turnstile> Ds \<sqsubseteq> Cs' @\<^sub>p Cs \<and> Cs \<noteq> [] \<and> P \<turnstile> C' has M = (Ts, T, m) via Cs \<longrightarrow> 
                             Ts = Ts' \<and> P \<turnstile> T' \<le> T"
  { fix Ts T m Cs Cs'
    assume path:"P \<turnstile> Path D to C via Cs'"
      and leq_path:"P,D \<turnstile> Ds \<sqsubseteq> Cs' @\<^sub>p Cs"
      and notempty:"Cs \<noteq> []"
      and Chas:"P \<turnstile> C has M = (Ts,T,m) via Cs"
    from Dleast have classD:"is_class P D"
      by (auto intro:Subobjs_isClass simp:MinimalMethodDefs_def MethodDefs_def)
    from path have Dhas:"P \<turnstile> D has M = (Ts,T,m) via Cs'@\<^sub>pCs" using Chas wf
      by (fastsimp intro:has_path_has)
    { assume "Ds = Cs'@\<^sub>pCs"
      with Dleast Dhas have "Ts = Ts' \<and> T' = T"
	by (auto simp:MinimalMethodDefs_def HasMethodDef_def MethodDefs_def)
      hence "Ts = Ts' \<and> T' = T" by auto }
    moreover
    { assume "(Ds,Cs'@\<^sub>pCs) \<in> (leq_path1 P D)\<^sup>+"
      hence subcls:"(last Ds,last (Cs'@\<^sub>pCs)) \<in> (subcls1 P)\<^sup>+" using wf
	by -(rule last_leq_paths)
      from Dhas obtain Bs fs ms where "class P (last (Cs'@\<^sub>pCs)) = Some(Bs,fs,ms)" 
	and "map_of ms M = Some(Ts,T,m)"
	by (auto simp:HasMethodDef_def MethodDefs_def)
      hence ex:"\<forall>Bs' fs' ms' Ts' T' m'. class P (last Ds) = Some(Bs',fs',ms') \<and> 
                 map_of ms' M = Some(Ts',T',m') \<longrightarrow> 
	             Ts = Ts' \<and> P \<turnstile> T' \<le> T"
	using subcls wf
	by -(rule subclsPlus_subtype,auto)
      from Dleast obtain Bs' fs' ms' where "class P (last Ds) = Some(Bs',fs',ms')" 
	and "map_of ms' M = Some(Ts',T',m')"
	by (auto simp:MinimalMethodDefs_def MethodDefs_def)
      with ex have "Ts = Ts'" and "P \<turnstile> T' \<le> T" by auto }
    ultimately have "Ts = Ts'" and "P \<turnstile> T' \<le> T" using leq_path
      by (auto dest!:rtrancl_is_eq_or_trancl) }
  thus "\<forall>Ts T m Cs Cs'. P \<turnstile> Path D to C via Cs' \<and> P,D \<turnstile> Ds \<sqsubseteq> Cs' @\<^sub>p Cs \<and> Cs \<noteq> [] \<and> 
                    P \<turnstile> C has M = (Ts, T, m) via Cs \<longrightarrow> 
                           Ts = Ts' \<and> P \<turnstile> T' \<le> T"
    by blast
qed




lemma wf_syscls:
  "set SystemClasses \<subseteq> set P \<Longrightarrow> wf_syscls P"
by (simp add: image_def SystemClasses_def wf_syscls_def sys_xcpts_def
          NullPointerC_def ClassCastC_def OutOfMemoryC_def,force intro:conjI)


subsection{* Well formedness and widen *}

lemma Class_widen: "\<lbrakk>P \<turnstile> Class C \<le> T; wf_prog wf_md P; is_class P C\<rbrakk>  
  \<Longrightarrow>  \<exists>D. T = Class D \<and> P \<turnstile> Path C to D unique"

apply (ind_cases "P \<turnstile> T \<le> T'")
apply (auto intro:path_C_to_C_unique)
done


lemma Class_widen_Class [iff]: "\<lbrakk>wf_prog wf_md P; is_class P C\<rbrakk> \<Longrightarrow> 
  (P \<turnstile> Class C \<le> Class D) = (P \<turnstile> Path C to D unique)"

apply (rule iffI)
apply (ind_cases " P \<turnstile> T \<le> T'")
apply (auto elim: widen_subcls intro:path_C_to_C_unique)
done


lemma widen_Class: "\<lbrakk>wf_prog wf_md P; is_class P C\<rbrakk> \<Longrightarrow> 
  (P \<turnstile> T \<le> Class C) = 
    (T = NT \<or> (\<exists>D. T = Class D \<and> P \<turnstile> Path D to C unique))"

apply(induct T) apply (auto intro:widen_subcls)
apply (ind_cases "P \<turnstile> T \<le> T'") apply (auto intro:path_C_to_C_unique)
done



subsection{* Well formedness and well typing *}

lemma assumes wf:"wf_prog wf_md P" 
shows WT_determ: "P,E \<turnstile> e :: T \<Longrightarrow> (\<And>T'. P,E \<turnstile> e :: T' \<Longrightarrow> T = T')"
and WTs_determ: "P,E \<turnstile> es [::] Ts \<Longrightarrow> (\<And>Ts'. P,E \<turnstile> es [::] Ts' \<Longrightarrow> Ts = Ts')"

proof(induct rule:WT_WTs_inducts)
  case (WTDynCast C D E e)
  have "P,E \<turnstile> Cast C e :: T'" .
  thus ?case by (fastsimp elim:WT_WTs.elims)
next
  case (WTStaticCast C D E e)
  have "P,E \<turnstile> \<lparr>C\<rparr>e :: T'" .
  thus ?case by (fastsimp elim:WT_WTs.elims)
next
  case (WTBinOp E T T\<^isub>1 T\<^isub>2 bop e\<^isub>1 e\<^isub>2)
  have bop:"case bop of Eq \<Rightarrow> T\<^isub>1 = T\<^isub>2 \<and> T = Boolean
    | Add \<Rightarrow> T\<^isub>1 = Integer \<and> T\<^isub>2 = Integer \<and> T = Integer"
    and wt:"P,E \<turnstile> e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 :: T'" .
  from wt obtain T1' T2' where
    bop':"case bop of Eq \<Rightarrow> T1' = T2' \<and> T' = Boolean
    | Add \<Rightarrow> T1' = Integer \<and> T2' = Integer \<and> T' = Integer"
    by auto
  from bop show ?case
  proof (cases bop)
    assume Eq:"bop = Eq"
    with bop have "T = Boolean" by auto
    with Eq bop' show ?thesis by simp
  next
    assume Add:"bop = Add"
    with bop have "T = Integer"
      by auto
    with Add bop' show ?thesis by simp
  qed
next
  case (WTLAss E T T' V e T'')
  have "P,E \<turnstile> V:=e :: T''" 
    and "E V = Some T" .
  thus ?case by auto
next
  case (WTFAcc C Cs E F T e)
  have IH:"\<And>T'. P,E \<turnstile> e :: T' \<Longrightarrow> Class C = T'"
    and least:"P \<turnstile> C has least F:T via Cs"
    and wt:"P,E \<turnstile> e\<bullet>F{Cs} :: T'" .
  from wt obtain C' where wte':"P,E \<turnstile> e :: Class C'"
    and least':"P \<turnstile> C' has least F:T' via Cs" by auto
  from IH[OF wte'] have "C = C'" by simp
  with least least' show ?case
    by (fastsimp simp:sees_field_fun)
next
  case (WTFAss C Cs E F T T' e\<^isub>1 e\<^isub>2 T'')
  have least:"P \<turnstile> C has least F:T via Cs"
    and wt:"P,E \<turnstile> e\<^isub>1\<bullet>F{Cs} := e\<^isub>2 :: T''" 
    and IH:"\<And>S. P,E \<turnstile> e\<^isub>1 :: S \<Longrightarrow> Class C = S" .
  from wt obtain C' where wte':"P,E \<turnstile> e\<^isub>1 :: Class C'" 
    and least':"P \<turnstile> C' has least F:T'' via Cs" by auto
  from IH[OF wte'] have "C = C'" by simp
  with least least' show ?case
    by (fastsimp simp:sees_field_fun)
next
  case (WTCall C Cs E M T Ts Ts' e es pns body T')
  have IH:"\<And>T'. P,E \<turnstile> e :: T' \<Longrightarrow> Class C = T'"
    and least:"P \<turnstile> C has least M = (Ts, T, pns, body) via Cs"
    and wt:"P,E \<turnstile> e\<bullet>M(es) :: T'" .
  from wt obtain C' Ts' pns' body' Cs' where wte':"P,E \<turnstile> e :: Class C'"
    and least':"P \<turnstile> C' has least M = (Ts',T',pns',body') via Cs'" by auto
  from IH[OF wte'] have "C = C'" by simp
  with least least' wf show ?case by (auto dest:wf_sees_method_fun)
next
  case WTBlock thus ?case by (clarsimp simp del:fun_upd_apply)
next
  case (WTSeq E T\<^isub>1 T\<^isub>2 e\<^isub>1 e\<^isub>2)
  have IH:"\<And>T'. P,E \<turnstile> e\<^isub>2 :: T' \<Longrightarrow> T\<^isub>2 = T'"
    and wt:"P,E \<turnstile> e\<^isub>1;; e\<^isub>2 :: T'" .
  from wt have wt':"P,E \<turnstile> e\<^isub>2 :: T'" by auto
  from IH[OF wt'] show ?case .
next
  case (WTCond E T e e\<^isub>1 e\<^isub>2 T')
  have IH:"\<And>S. P,E \<turnstile> e\<^isub>1 :: S \<Longrightarrow> T = S"
    and wt:"P,E \<turnstile> if (e) e\<^isub>1 else e\<^isub>2 :: T'" .
  from wt have "P,E \<turnstile> e\<^isub>1 :: T'" by auto
  from IH[OF this] show ?case .
next
  case (WTCons E T Ts e es)
  have IHe:"\<And>T'. P,E \<turnstile> e :: T' \<Longrightarrow> T = T'"
    and IHes:"\<And>Ts'. P,E \<turnstile> es [::] Ts' \<Longrightarrow> Ts = Ts'"
    and wt:"P,E \<turnstile> e # es [::] Ts'" .
  from wt show ?case
  proof (cases Ts')
    case Nil with wt show ?thesis by simp
  next
    case (Cons T'' Ts'')
    with wt have wte':"P,E \<turnstile> e :: T''" and wtes':"P,E \<turnstile> es [::] Ts''"
      by auto
    from IHe[OF wte'] IHes[OF wtes'] Cons show ?thesis by simp
  qed
qed clarsimp+

end
