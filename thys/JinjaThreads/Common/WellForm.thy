(*  Title:      JinjaThreads/Common/WellForm.thy
    Author:     Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja theory Common/WellForm.thy by Tobias Nipkow
*)

header {* \isaheader{Generic Well-formedness of programs} *}

theory WellForm imports TypeRel SystemClasses begin

text {*\noindent This theory defines global well-formedness conditions
for programs but does not look inside method bodies.  Hence it works
for both Jinja and JVM programs. Well-typing of expressions is defined
elsewhere (in theory @{text WellType}).

Because Jinja does not have method overloading, its policy for method
overriding is the classical one: \emph{covariant in the result type
but contravariant in the argument types.} This means the result type
of the overriding method becomes more specific, the argument types
become more general.
*}

types 'm wf_mdecl_test = "'m prog \<Rightarrow> cname \<Rightarrow> 'm mdecl \<Rightarrow> bool"

constdefs
  wf_fdecl :: "'m prog \<Rightarrow> fdecl \<Rightarrow> bool"
  "wf_fdecl P \<equiv> \<lambda>(F,T). is_type P T"

  wf_mdecl :: "'m wf_mdecl_test \<Rightarrow> 'm wf_mdecl_test"
  "wf_mdecl wf_md P C \<equiv> \<lambda>(M,Ts,T,mb).
  (\<forall>T\<in>set Ts. is_type P T) \<and> is_type P T \<and> wf_md P C (M,Ts,T,mb)"

  wf_cdecl :: "'m wf_mdecl_test \<Rightarrow> 'm prog \<Rightarrow> 'm cdecl \<Rightarrow> bool"
  "wf_cdecl wf_md P  \<equiv>  \<lambda>(C,(D,fs,ms)).
  (\<forall>f\<in>set fs. wf_fdecl P f) \<and>  distinct_fst fs \<and>
  (\<forall>m\<in>set ms. wf_mdecl wf_md P C m) \<and>  distinct_fst ms \<and>
  (C \<noteq> Object \<longrightarrow>
   is_class P D \<and> \<not> P \<turnstile> D \<preceq>\<^sup>* C \<and>
   (\<forall>(M,Ts,T,m)\<in>set ms.
      \<forall>D' Ts' T' m'. P \<turnstile> D sees M:Ts' \<rightarrow> T' = m' in D' \<longrightarrow>
                       P \<turnstile> Ts' [\<le>] Ts \<and> P \<turnstile> T \<le> T')) \<and>
  (C = Object \<longrightarrow> (fs = []) \<and> (ms = [])) \<and>  (* require object to have no fields/methods because of array subtype of object *)
  (C = Thread \<longrightarrow> (\<exists>m. (run, [], Void, m) \<in> set ms)) \<and>
  (P \<turnstile> C \<preceq>\<^sup>* Thread \<or> P \<turnstile> Thread \<preceq>\<^sup>* C \<longrightarrow> \<not> (\<exists>m Ts T. (start, Ts, T, m) \<in> set ms) \<and> \<not> (\<exists>m Ts T. (join, Ts, T, m) \<in> set ms)) \<and>
  (\<not> (\<exists>m Ts T. (wait, Ts, T, m) \<in> set ms)) \<and> 
  (\<not> (\<exists>m Ts T. (notify, Ts, T, m) \<in> set ms)) \<and>
  (\<not> (\<exists>m Ts T. (notifyAll, Ts, T, m) \<in> set ms))"

  wf_syscls :: "'m prog \<Rightarrow> bool"
  "wf_syscls P  \<equiv>  {Object} \<union> sys_xcpts \<subseteq> set(map fst P)"

  wf_prog :: "'m wf_mdecl_test \<Rightarrow> 'm prog \<Rightarrow> bool"
  "wf_prog wf_md P  \<equiv>  wf_syscls P \<and> (\<forall>c \<in> set P. wf_cdecl wf_md P c) \<and> distinct_fst P"


subsection{* Well-formedness lemmas *}

lemma class_wf: 
  "\<lbrakk>class P C = Some c; wf_prog wf_md P\<rbrakk> \<Longrightarrow> wf_cdecl wf_md P (C,c)"
(*<*)
apply (unfold wf_prog_def class_def)
apply (fast dest: map_of_SomeD)
done
(*>*)


lemma class_Object [simp]: 
  "wf_prog wf_md P \<Longrightarrow> \<exists>C fs ms. class P Object = Some (C,fs,ms)"
(*<*)
apply (unfold wf_prog_def wf_syscls_def class_def)
apply (auto simp: map_of_SomeI)
done
(*>*)


lemma is_class_Object [simp]:
  "wf_prog wf_md P \<Longrightarrow> is_class P Object"
(*<*)by (simp add: is_class_def)(*>*)

lemma is_class_xcpt:
  "\<lbrakk> C \<in> sys_xcpts; wf_prog wf_md P \<rbrakk> \<Longrightarrow> is_class P C"
(*<*)
  apply (simp add: wf_prog_def wf_syscls_def is_class_def class_def)
  apply (fastsimp intro!: map_of_SomeI)
  done
(*>*)


lemma subcls1_wfD:
  "\<lbrakk> P \<turnstile> C \<prec>\<^sup>1 D; wf_prog wf_md P \<rbrakk> \<Longrightarrow> D \<noteq> C \<and> \<not> (subcls1 P)\<^sup>+\<^sup>+ D C"
apply( frule tranclp.r_into_trancl[where r="subcls1 P"])
apply( drule subcls1D)
apply(clarify)
apply( drule (1) class_wf)
apply( unfold wf_cdecl_def)
apply(rule conjI)
 apply(force)
apply(unfold reflcl_tranclp[symmetric, where r="subcls1 P"])
apply(blast)
done


lemma wf_cdecl_supD: 
  "\<lbrakk>wf_cdecl wf_md P (C,D,r); C \<noteq> Object\<rbrakk> \<Longrightarrow> is_class P D"
(*<*)by (auto simp: wf_cdecl_def)(*>*)


lemma subcls_asym:
  "\<lbrakk> wf_prog wf_md P; (subcls1 P)\<^sup>+\<^sup>+ C D \<rbrakk> \<Longrightarrow> \<not> (subcls1 P)\<^sup>+\<^sup>+ D C"
(*<*)
apply(erule tranclp.cases)
apply(fast dest!: subcls1_wfD )
apply(fast dest!: subcls1_wfD intro: tranclp_trans)
done
(*>*)


lemma subcls_irrefl:
  "\<lbrakk> wf_prog wf_md P; (subcls1 P)\<^sup>+\<^sup>+ C D\<rbrakk> \<Longrightarrow> C \<noteq> D"
(*<*)
apply (erule tranclp_trans_induct)
apply  (auto dest: subcls1_wfD subcls_asym)
done
(*>*)

lemma acyclicP_def:
  "acyclicP r \<longleftrightarrow> (\<forall>x. \<not> r^++ x x)"
  unfolding acyclic_def trancl_def
by(auto)

lemma acyclic_subcls1:
  "wf_prog wf_md P \<Longrightarrow> acyclicP (subcls1 P)"
(*<*)
apply (unfold acyclicP_def)
apply (fast dest: subcls_irrefl)
done
(*>*)



lemma wf_subcls1:
  "wf_prog wf_md P \<Longrightarrow> wfP ((subcls1 P)\<inverse>\<inverse>)"
unfolding wfP_def
apply (rule finite_acyclic_wf)
 apply(subst finite_converse[unfolded converse_def, symmetric])
 apply(simp)
 apply(rule finite_subcls1)
apply(subst acyclic_converse[unfolded converse_def, symmetric])
apply(simp)
apply (erule acyclic_subcls1)
done
(*>*)


lemma single_valued_subcls1:
  "wf_prog wf_md G \<Longrightarrow> single_valuedP (subcls1 G)"
(*<*)
by(auto simp:wf_prog_def distinct_fst_def single_valued_def dest!:subcls1D)
(*>*)


lemma subcls_induct: 
  "\<lbrakk> wf_prog wf_md P; \<And>C. \<forall>D. (subcls1 P)\<^sup>+\<^sup>+ C D \<longrightarrow> Q D \<Longrightarrow> Q C \<rbrakk> \<Longrightarrow> Q C"
(*<*)
  (is "?A \<Longrightarrow> PROP ?P \<Longrightarrow> _")
proof -
  assume p: "PROP ?P"
  assume ?A thus ?thesis apply -
apply(drule wf_subcls1)
apply(drule wfP_trancl)
apply(simp only: tranclp_converse)
apply(erule_tac a = C in wfP_induct)
apply(rule p)
apply(auto)
done
qed
(*>*)


lemma subcls1_induct_aux:
  "\<lbrakk> is_class P C; wf_prog wf_md P; Q Object;
    \<And>C D fs ms.
    \<lbrakk> C \<noteq> Object; is_class P C; class P C = Some (D,fs,ms) \<and>
      wf_cdecl wf_md P (C,D,fs,ms) \<and> P \<turnstile> C \<prec>\<^sup>1 D \<and> is_class P D \<and> Q D\<rbrakk> \<Longrightarrow> Q C \<rbrakk>
  \<Longrightarrow> Q C"
(*<*)
  (is "?A \<Longrightarrow> ?B \<Longrightarrow> ?C \<Longrightarrow> PROP ?P \<Longrightarrow> _")
proof -
  assume p: "PROP ?P"
  assume ?A ?B ?C thus ?thesis apply -
apply(unfold is_class_def)
apply( rule impE)
prefer 2
apply(   assumption)
prefer 2
apply(  assumption)
apply( erule thin_rl)
apply( rule subcls_induct)
apply(  assumption)
apply( rule impI)
apply( case_tac "C = Object")
apply(  fast)
apply safe
apply( frule (1) class_wf)
apply( frule (1) wf_cdecl_supD)

apply( subgoal_tac "P \<turnstile> C \<prec>\<^sup>1 a")
apply( erule_tac [2] subcls1I)
apply(  rule p)
apply (unfold is_class_def)
apply auto
done
qed
(*>*)

(* FIXME can't we prove this one directly?? *)
lemma subcls1_induct [consumes 2, case_names Object Subcls]:
  "\<lbrakk> wf_prog wf_md P; is_class P C; Q Object;
    \<And>C D. \<lbrakk>C \<noteq> Object; P \<turnstile> C \<prec>\<^sup>1 D; is_class P D; Q D\<rbrakk> \<Longrightarrow> Q C \<rbrakk>
  \<Longrightarrow> Q C"
(*<*)
  apply (erule subcls1_induct_aux, assumption, assumption)
  apply blast
  done
(*>*)


lemma subcls_C_Object:
  "\<lbrakk> is_class P C; wf_prog wf_md P \<rbrakk> \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* Object"
(*<*)
apply(erule (1) subcls1_induct)
 apply( fast)
apply(erule (1) converse_rtranclp_into_rtranclp)
done
(*>*)

lemma converse_subcls_is_class:
  assumes wf: "wf_prog wf_md P"
  shows "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* D; is_class P C \<rbrakk> \<Longrightarrow> is_class P D"
proof(induct rule: rtranclp_induct)
  assume "is_class P C"
  thus "is_class P C" .
next
  fix D E
  assume PDE: "P \<turnstile> D \<prec>\<^sup>1 E"
    and IH: "is_class P C \<Longrightarrow> is_class P D"
    and iPC: "is_class P C"
  have "is_class P D" by (rule IH[OF iPC])
  with PDE obtain fsD MsD where classD: "class P D = \<lfloor>(E, fsD, MsD)\<rfloor>"
    by(auto simp add: is_class_def elim!: subcls1.cases)
  thus "is_class P E" using wf PDE
    apply -
    apply(erule subcls1.cases, clarsimp)
    apply(clarsimp simp: wf_prog_def)
    apply(drule_tac x="(D, E, fsD, MsD)" in bspec)
    apply(clarsimp simp add: class_def)
    apply(erule map_of_is_SomeD)
    apply(erule_tac C="D" in wf_cdecl_supD)
    .
qed

lemma is_class_is_subcls:
  "wf_prog m P \<Longrightarrow> is_class P C = P \<turnstile> C \<preceq>\<^sup>* Object"
(*<*)by (fastsimp simp:is_class_def
                  elim: subcls_C_Object converse_rtranclpE subcls1I
                  dest: subcls1D)
(*>*)

lemma subcls_antisym:
  "\<lbrakk>wf_prog m P; P \<turnstile> C \<preceq>\<^sup>* D; P \<turnstile> D \<preceq>\<^sup>* C\<rbrakk> \<Longrightarrow> C = D"
apply(drule acyclic_subcls1)
apply(drule acyclic_impl_antisym_rtrancl)
apply(drule antisymD)
apply(unfold rtrancl_def)
apply(auto)
done

lemma is_type_pTs:
assumes "wf_prog wf_md P" and "(C,S,fs,ms) \<in> set P" and "(M,Ts,T,m) \<in> set ms"
shows "set Ts \<subseteq> types P"
(*<*)
proof
  from prems have "wf_mdecl wf_md P C (M,Ts,T,m)" 
    by (unfold wf_prog_def wf_cdecl_def) auto  
  hence "\<forall>t \<in> set Ts. is_type P t" by (unfold wf_mdecl_def) auto
  moreover fix t assume "t \<in> set Ts"
  ultimately have "is_type P t" by blast
  thus "t \<in> types P" ..
qed
(*>*)

lemma widen_asym_1: 
  assumes wfP: "wf_prog wf_md P"
  shows "P \<turnstile> C \<le> D \<Longrightarrow> C = D \<or> \<not> (P \<turnstile> D \<le> C)"
proof (erule widen.induct)
  fix T
  show "T = T \<or> \<not> (P \<turnstile> T \<le> T)" by simp
next
  fix C D
  assume CscD: "P \<turnstile> C \<preceq>\<^sup>* D"
  then have CpscD: "C = D \<or> (C \<noteq> D \<and> (subcls1 P)\<^sup>+\<^sup>+ C D)" by (simp add: rtranclpD)
  { assume "P \<turnstile> D \<preceq>\<^sup>* C"
    then have DpscC: "D = C \<or> (D \<noteq> C \<and> (subcls1 P)\<^sup>+\<^sup>+ D C)" by (simp add: rtranclpD)
    { assume "(subcls1 P)\<^sup>+\<^sup>+ D C"
      with wfP have CnscD: "\<not> (subcls1 P)\<^sup>+\<^sup>+ C D" by (rule subcls_asym)
      with CpscD have "C = D" by simp
    }
    with DpscC have "C = D" by blast
  }
  hence "Class C = Class D \<or> \<not> (P \<turnstile> D \<preceq>\<^sup>* C)" by blast
  thus "Class C = Class D \<or> \<not> P \<turnstile> Class D \<le> Class C" by simp
next
  fix C
  show "NT = Class C \<or> \<not> P \<turnstile> Class C \<le> NT" by simp
next
  fix A
  { assume "P \<turnstile> A\<lfloor>\<rceil> \<le> NT"
    hence "A\<lfloor>\<rceil> = NT" by fastsimp
    with prems have "False" by simp }
  hence "\<not> (P \<turnstile> A\<lfloor>\<rceil> \<le> NT)" by blast
  thus "NT = A\<lfloor>\<rceil> \<or> \<not> P \<turnstile> A\<lfloor>\<rceil> \<le> NT" by simp
next
  fix A
  show "A\<lfloor>\<rceil> = Class Object \<or> \<not> P \<turnstile> Class Object \<le> A\<lfloor>\<rceil>"
    by(auto dest: Object_widen)
next
  fix A B
  assume AsU: "P \<turnstile> A \<le> B" and BnpscA: "A = B \<or> \<not> P \<turnstile> B \<le> A"
  { assume "P \<turnstile> B\<lfloor>\<rceil> \<le> A\<lfloor>\<rceil>"
    hence "P \<turnstile> B \<le> A" by (auto dest: Array_Array_widen)
    with BnpscA have "A = B" by blast
    hence "A\<lfloor>\<rceil> = B\<lfloor>\<rceil>" by simp }
  thus "A\<lfloor>\<rceil> = B\<lfloor>\<rceil> \<or> \<not> P \<turnstile> B\<lfloor>\<rceil> \<le> A\<lfloor>\<rceil>" by blast
qed

lemma widen_asym: "\<lbrakk> wf_prog wf_md P; P \<turnstile> C \<le> D; C \<noteq> D \<rbrakk> \<Longrightarrow> \<not> (P \<turnstile> D \<le> C)"
proof -
  assume wfP: "wf_prog wf_md P" and CsD: "P \<turnstile> C \<le> D" and CneqD: "C \<noteq> D"
  from wfP CsD have "C = D \<or> \<not> (P \<turnstile> D \<le> C)" by (rule widen_asym_1)
  with CneqD show ?thesis by simp
qed

lemma widen_antisym:
  "\<lbrakk> wf_prog m P; P \<turnstile> T \<le> U; P \<turnstile> U \<le> T \<rbrakk> \<Longrightarrow> T = U"
by(auto dest: widen_asym)

lemma widen_C_Object: "\<lbrakk> wf_prog wf_md P; is_class P C \<rbrakk> \<Longrightarrow> P \<turnstile> Class C \<le> Class Object"
by(simp add: subcls_C_Object)

lemma is_refType_widen_Object:
  assumes wfP: "wf_prog wfmc P"
  shows "\<lbrakk> is_type P A; is_refT A \<rbrakk> \<Longrightarrow> P \<turnstile> A \<le> Class Object"
by(induct A)(auto elim: refTE intro: subcls_C_Object[OF _ wfP] widen_array_object)

subsection{* Well-formedness and method lookup *}

lemma sees_wf_mdecl:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<rbrakk> \<Longrightarrow> wf_mdecl wf_md P D (M,Ts,T,m)"
(*<*)
apply(drule visible_method_exists)
apply(clarify)
apply(drule class_wf, assumption)
apply(drule map_of_SomeD)
apply(simp add: wf_cdecl_def)
done
(*>*)


lemma sees_method_mono [rule_format (no_asm)]: 
  "\<lbrakk> P \<turnstile> C' \<preceq>\<^sup>* C; wf_prog wf_md P \<rbrakk> \<Longrightarrow>
  \<forall>D Ts T m. P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<longrightarrow>
     (\<exists>D' Ts' T' m'. P \<turnstile> C' sees M:Ts'\<rightarrow>T' = m' in D' \<and> P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T' \<le> T)"
(*<*)
apply( drule rtranclpD)
apply( erule disjE)
apply(  fastsimp intro: widen_refl widens_refl)
apply( erule conjE)
apply( erule tranclp_trans_induct)
prefer 2
apply(  clarify)
apply(  drule spec, drule spec, drule spec, drule spec, erule (1) impE)
apply clarify
apply(  fast elim: widen_trans widens_trans)
apply( clarify)
apply( drule subcls1D)
apply( clarify)
apply(clarsimp simp:Method_def)
apply(frule (2) sees_methods_rec)
apply(rule refl)
apply(case_tac "map_of ms M")
apply(rule_tac x = D in exI)
apply(rule_tac x = Ts in exI)
apply(rule_tac x = T in exI)
apply(clarsimp simp add: widens_refl)
apply(rule_tac x = m in exI)
apply(fastsimp simp add:map_add_def split:option.split)
apply clarsimp
apply(rename_tac Ts' T' m')
apply( drule (1) class_wf)
apply( unfold wf_cdecl_def Method_def)
apply( frule map_of_SomeD)
apply(clarsimp)
apply(drule (1) bspec, simp, erule_tac x=D in allE, erule_tac x=Ts in allE, erule_tac x=T in allE, fastsimp simp:map_add_def split:option.split)+
done
(*>*)


lemma sees_method_mono2:
  "\<lbrakk> P \<turnstile> C' \<preceq>\<^sup>* C; wf_prog wf_md P;
     P \<turnstile> C sees M:Ts\<rightarrow>T = m in D; P \<turnstile> C' sees M:Ts'\<rightarrow>T' = m' in D' \<rbrakk>
  \<Longrightarrow> P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T' \<le> T"
(*<*)by(blast dest:sees_method_mono sees_method_fun)(*>*)


lemma mdecls_visible:
assumes wf: "wf_prog wf_md P" and "class": "is_class P C"
shows "\<And>D fs ms. class P C = Some(D,fs,ms)
         \<Longrightarrow> \<exists>Mm. P \<turnstile> C sees_methods Mm \<and> (\<forall>(M,Ts,T,m) \<in> set ms. Mm M = Some((Ts,T,m),C))"
(*<*)
using wf "class"
proof (induct rule:subcls1_induct)
  case Object
  with wf have "distinct_fst ms"
    by (unfold class_def wf_prog_def wf_cdecl_def) (fastsimp dest:map_of_SomeD)
  with Object show ?case by(fastsimp intro!: sees_methods_Object map_of_SomeI)
next
  case Subcls
  with wf have "distinct_fst ms"
    by (unfold class_def wf_prog_def wf_cdecl_def) (fastsimp dest:map_of_SomeD)
  with Subcls show ?case
    by(fastsimp elim:sees_methods_rec dest:subcls1D map_of_SomeI
                simp:is_class_def)
qed
(*>*)


lemma mdecl_visible:
assumes wf: "wf_prog wf_md P" and C: "(C,S,fs,ms) \<in> set P" and  m: "(M,Ts,T,m) \<in> set ms"
shows "P \<turnstile> C sees M:Ts\<rightarrow>T = m in C"
(*<*)
proof -
  from wf C have "class": "class P C = Some (S,fs,ms)"
    by (auto simp add: wf_prog_def class_def is_class_def intro: map_of_SomeI)
  from "class" have "is_class P C" by(auto simp:is_class_def)                   
  with prems "class" show ?thesis
    by(bestsimp simp:Method_def dest:mdecls_visible)
qed
(*>*)

lemma Thread_no_sees_method_start:
  assumes wf: "wf_prog wf_md P"
  shows "\<lbrakk> P \<turnstile> C sees_methods Mm; Mm start = \<lfloor>((Ts, T, mthd), D)\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<or> P \<turnstile> Thread \<preceq>\<^sup>* C \<rbrakk> \<Longrightarrow> False"
proof(induct rule: Methods.induct)
  case (sees_methods_Object D' fs ms Mm) 
  have classO: "class P Object = \<lfloor>(D', fs, ms)\<rfloor>" by fact
  have Mm: "Mm = option_map (\<lambda>m. (m, Object)) \<circ> map_of ms" by fact
  have Mmstart: "Mm start = \<lfloor>((Ts, T, mthd), D)\<rfloor>" by fact
  have "P \<turnstile> Object \<preceq>\<^sup>* Thread \<or> P \<turnstile> Thread \<preceq>\<^sup>* Object" by fact
  hence PTO: "P \<turnstile> Thread \<preceq>\<^sup>* Object" by(auto)
  with wf classO have "\<not> (\<exists>Ts T m. (start, Ts, T, m) \<in> set ms)"
    apply -
    apply(auto simp add: wf_prog_def)
    apply(auto dest!: bspec map_of_is_SomeD simp: class_def)
    by(clarsimp simp: wf_cdecl_def)
  with Mm Mmstart show ?case
    by (auto dest: map_of_is_SomeD)
next
  case (sees_methods_rec C D' fs ms Mm Mm')
  have classC: "class P C = \<lfloor>(D', fs, ms)\<rfloor>" by fact
  have CnObject: "C \<noteq> Object" by fact
  have PD'Mm: "P \<turnstile> D' sees_methods Mm" by fact
  have IH: "\<lbrakk>Mm start = \<lfloor>((Ts, T, mthd), D)\<rfloor>; P \<turnstile> D' \<preceq>\<^sup>* Thread \<or> P \<turnstile> Thread \<preceq>\<^sup>* D'\<rbrakk> \<Longrightarrow> False" by fact
  have Mm': "Mm' = Mm ++ (option_map (\<lambda>m. (m, C)) \<circ> map_of ms)" by fact
  have Mm'start: "Mm' start = \<lfloor>((Ts, T, mthd), D)\<rfloor>" by fact
  have "P \<turnstile> C \<preceq>\<^sup>* Thread \<or> P \<turnstile> Thread \<preceq>\<^sup>* C" by fact
  thus ?case
  proof(rule disjE)
    assume PCThread: "P \<turnstile> C \<preceq>\<^sup>* Thread"
    show ?thesis
    proof(cases "(option_map (\<lambda>m. (m, C)) \<circ> map_of ms) start")
      case None
      with Mm' Mm'start have Mmstart: "Mm start = \<lfloor>((Ts, T, mthd), D)\<rfloor>"
	by(auto)
      from classC have PCs1D: "P \<turnstile> C \<prec>\<^sup>1 D'" using CnObject by(auto intro: subcls1I)
      with wf classC have "is_class P D'" 
	apply -
	apply(drule r_into_rtranclp[where r="subcls1 P"])
	apply(erule converse_subcls_is_class, assumption)
	by (simp add: is_class_def)
      then obtain E fsD MsD where classD': "class P D' = \<lfloor>(E, fsD, MsD)\<rfloor>" by(auto simp: is_class_def)
      show ?thesis
      proof(cases "P \<turnstile> D' \<preceq>\<^sup>* Thread")
	assume "P \<turnstile> D' \<preceq>\<^sup>* Thread"
	thus ?thesis by(auto intro: IH[OF Mmstart])
      next
	assume "\<not> P \<turnstile> D' \<preceq>\<^sup>* Thread"
	with PCThread PCs1D wf have "C = Thread"
	  apply -
	  apply(erule converse_rtranclpE)
	  by(auto elim!: subcls1.cases)
	hence "P \<turnstile> Thread \<preceq>\<^sup>* D'" using PCs1D by auto
	thus ?thesis by(auto intro: IH[OF Mmstart])
      qed
    next
      case (Some a)
      with Mm'start Mm' have "(start, Ts, T, mthd) \<in> set ms"
	by(auto dest: map_of_is_SomeD)
      with wf classC PCThread show ?thesis
	apply -
	apply(auto simp add: wf_prog_def)
	apply(auto dest!: bspec map_of_is_SomeD simp: class_def)
	by(clarsimp simp: wf_cdecl_def)
    qed
  next
    assume PThreadC: "P \<turnstile> Thread \<preceq>\<^sup>* C"
    show ?thesis
    proof(cases "(option_map (\<lambda>m. (m, C)) \<circ> map_of ms) start")
      case None
      with Mm' Mm'start have Mmstart: "Mm start = \<lfloor>((Ts, T, mthd), D)\<rfloor>"
	by(auto)
      from classC have PCs1D: "P \<turnstile> C \<prec>\<^sup>1 D'" using CnObject by(auto intro: subcls1I)
      with wf classC have "is_class P D'" 
	apply -
	apply(drule r_into_rtranclp[where r="subcls1 P"])
	apply(erule converse_subcls_is_class, assumption)
	by (simp add: is_class_def)
      then obtain E fsD MsD where classD': "class P D' = \<lfloor>(E, fsD, MsD)\<rfloor>" by(auto simp: is_class_def)
      from PCs1D PThreadC have "P \<turnstile> Thread \<preceq>\<^sup>* D'" by(auto)
      thus ?thesis by(auto intro: IH[OF Mmstart])
    next
      case (Some a)
      with Mm'start Mm' have "(start, Ts, T, mthd) \<in> set ms"
	by(auto dest: map_of_is_SomeD)
      with wf classC PThreadC show ?thesis
	apply -
	apply(auto simp add: wf_prog_def)
	apply(auto dest!: bspec map_of_is_SomeD simp: class_def)
	by(clarsimp simp: wf_cdecl_def)
    qed
  qed
qed

lemma Thread_not_sees_method_start:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> C sees start: Ts \<rightarrow> T = mthd in D; P \<turnstile> C \<preceq>\<^sup>* Thread \<or> P \<turnstile> Thread \<preceq>\<^sup>* C \<rbrakk> \<Longrightarrow> False"
by(auto simp add: Method_def del: disjE elim: Thread_no_sees_method_start)

lemma Thread_no_sees_method_join:
  assumes wf: "wf_prog wf_md P"
  shows "\<lbrakk> P \<turnstile> C sees_methods Mm; Mm join = \<lfloor>((Ts, T, mthd), D)\<rfloor>; P \<turnstile> C \<preceq>\<^sup>* Thread \<or> P \<turnstile> Thread \<preceq>\<^sup>* C \<rbrakk> \<Longrightarrow> False"
proof(induct rule: Methods.induct)
  case (sees_methods_Object D' fs ms Mm) 
  have classO: "class P Object = \<lfloor>(D', fs, ms)\<rfloor>" by fact
  have Mm: "Mm = option_map (\<lambda>m. (m, Object)) \<circ> map_of ms" by fact
  have Mmstart: "Mm join = \<lfloor>((Ts, T, mthd), D)\<rfloor>" by fact
  have "P \<turnstile> Object \<preceq>\<^sup>* Thread \<or> P \<turnstile> Thread \<preceq>\<^sup>* Object" by fact
  hence PTO: "P \<turnstile> Thread \<preceq>\<^sup>* Object" by(auto)
  with wf classO have "\<not> (\<exists>Ts T m. (join, Ts, T, m) \<in> set ms)"
    apply -
    apply(auto simp add: wf_prog_def)
    apply(auto dest!: bspec map_of_is_SomeD simp: class_def)
    by(clarsimp simp: wf_cdecl_def)
  with Mm Mmstart show ?case
    by (auto dest: map_of_is_SomeD)
next
  case (sees_methods_rec C D' fs ms Mm Mm')
  have classC: "class P C = \<lfloor>(D', fs, ms)\<rfloor>" by fact
  have CnObject: "C \<noteq> Object" by fact
  have PD'Mm: "P \<turnstile> D' sees_methods Mm" by fact
  have IH: "\<lbrakk>Mm join = \<lfloor>((Ts, T, mthd), D)\<rfloor>; P \<turnstile> D' \<preceq>\<^sup>* Thread \<or> P \<turnstile> Thread \<preceq>\<^sup>* D'\<rbrakk> \<Longrightarrow> False" by fact
  have Mm': "Mm' = Mm ++ (option_map (\<lambda>m. (m, C)) \<circ> map_of ms)" by fact
  have Mm'start: "Mm' join = \<lfloor>((Ts, T, mthd), D)\<rfloor>" by fact
  have "P \<turnstile> C \<preceq>\<^sup>* Thread \<or> P \<turnstile> Thread \<preceq>\<^sup>* C" by fact
  thus ?case
  proof(rule disjE)
    assume PCThread: "P \<turnstile> C \<preceq>\<^sup>* Thread"
    show ?thesis
    proof(cases "(option_map (\<lambda>m. (m, C)) \<circ> map_of ms) join")
      case None
      with Mm' Mm'start have Mmstart: "Mm join = \<lfloor>((Ts, T, mthd), D)\<rfloor>"
	by(auto)
      from classC have PCs1D: "P \<turnstile> C \<prec>\<^sup>1 D'" using CnObject by(auto intro: subcls1I)
      with wf classC have "is_class P D'" 
	apply -
	apply(drule r_into_rtranclp[where r="subcls1 P"])
	apply(erule converse_subcls_is_class, assumption)
	by (simp add: is_class_def)
      then obtain E fsD MsD where classD': "class P D' = \<lfloor>(E, fsD, MsD)\<rfloor>" by(auto simp: is_class_def)
      show ?thesis
      proof(cases "P \<turnstile> D' \<preceq>\<^sup>* Thread")
	assume "P \<turnstile> D' \<preceq>\<^sup>* Thread"
	thus ?thesis by(auto intro: IH[OF Mmstart])
      next
	assume "\<not> P \<turnstile> D' \<preceq>\<^sup>* Thread"
	with PCThread PCs1D wf have "C = Thread"
	  apply -
	  apply(erule converse_rtranclpE)
	  by(auto elim!: subcls1.cases)
	hence "P \<turnstile> Thread \<preceq>\<^sup>* D'" using PCs1D by auto
	thus ?thesis by(auto intro: IH[OF Mmstart])
      qed
    next
      case (Some a)
      with Mm'start Mm' have "(join, Ts, T, mthd) \<in> set ms"
	by(auto dest: map_of_is_SomeD)
      with wf classC PCThread show ?thesis
	apply -
	apply(auto simp add: wf_prog_def)
	apply(auto dest!: bspec map_of_is_SomeD simp: class_def)
	by(clarsimp simp: wf_cdecl_def)
    qed
  next
    assume PThreadC: "P \<turnstile> Thread \<preceq>\<^sup>* C"
    show ?thesis
    proof(cases "(option_map (\<lambda>m. (m, C)) \<circ> map_of ms) join")
      case None
      with Mm' Mm'start have Mmstart: "Mm join = \<lfloor>((Ts, T, mthd), D)\<rfloor>"
	by(auto)
      from classC have PCs1D: "P \<turnstile> C \<prec>\<^sup>1 D'" using CnObject by(auto intro: subcls1I)
      with wf classC have "is_class P D'" 
	apply -
	apply(drule r_into_rtranclp[where r="subcls1 P"])
	apply(erule converse_subcls_is_class, assumption)
	by (simp add: is_class_def)
      then obtain E fsD MsD where classD': "class P D' = \<lfloor>(E, fsD, MsD)\<rfloor>" by(auto simp: is_class_def)
      from PCs1D PThreadC have "P \<turnstile> Thread \<preceq>\<^sup>* D'" by(auto)
      thus ?thesis by(auto intro: IH[OF Mmstart])
    next
      case (Some a)
      with Mm'start Mm' have "(join, Ts, T, mthd) \<in> set ms"
	by(auto dest: map_of_is_SomeD)
      with wf classC PThreadC show ?thesis
	apply -
	apply(auto simp add: wf_prog_def)
	apply(auto dest!: bspec map_of_is_SomeD simp: class_def)
	by(clarsimp simp: wf_cdecl_def)
    qed
  qed
qed

lemma Thread_not_sees_method_join:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> C sees join: Ts \<rightarrow> T = mthd in D; P \<turnstile> C \<preceq>\<^sup>* Thread \<or> P \<turnstile> Thread \<preceq>\<^sup>* C \<rbrakk> \<Longrightarrow> False"
by(auto simp add: Method_def del: disjE elim: Thread_no_sees_method_join)

lemma Call_lemma:
  "\<lbrakk> P \<turnstile> C sees M:Ts\<rightarrow>T = m in D; P \<turnstile> C' \<preceq>\<^sup>* C; wf_prog wf_md P \<rbrakk>
  \<Longrightarrow> \<exists>D' Ts' T' m'.
       P \<turnstile> C' sees M:Ts'\<rightarrow>T' = m' in D' \<and> P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T' \<le> T \<and> P \<turnstile> C' \<preceq>\<^sup>* D'
       \<and> is_type P T' \<and> (\<forall>T\<in>set Ts'. is_type P T) \<and> wf_md P D' (M,Ts',T',m')"
(*<*)
apply(frule (2) sees_method_mono)
apply(fastsimp intro:sees_method_decl_above dest:sees_wf_mdecl
               simp: wf_mdecl_def)
done
(*>*)

lemma sub_Thread_sees_run:
  assumes wf: "wf_prog wf_md P"
  and PCThread: "P \<turnstile> C \<preceq>\<^sup>* Thread"
  and isclassThread: "is_class P Thread"
  shows "\<exists>D mthd. P \<turnstile> C sees run: []\<rightarrow>Void = mthd in D"
proof -
  from isclassThread obtain T' fsT MsT where classT: "class P Thread = \<lfloor>(T', fsT, MsT)\<rfloor>"
    by(auto simp: is_class_def)
  with wf have wfcThread: "wf_cdecl wf_md P (Thread, T', fsT, MsT)"
    by(auto dest: map_of_is_SomeD bspec simp add: wf_prog_def class_def)
  then obtain mrunT where runThread: "(run, [], Void, mrunT) \<in> set MsT"
    by(auto simp add: wf_cdecl_def)
  moreover have "\<exists>MmT. P \<turnstile> Thread sees_methods MmT \<and>
                       (\<forall>(M,Ts,T,m) \<in> set MsT. MmT M = Some((Ts,T,m),Thread))"
    by(rule mdecls_visible[OF wf isclassThread classT])
  then obtain MmT where ThreadMmT: "P \<turnstile> Thread sees_methods MmT"
    and MmT: "\<forall>(M,Ts,T,m) \<in> set MsT. MmT M = Some((Ts,T,m),Thread)"
    by blast
  ultimately obtain mthd
    where "MmT run = \<lfloor>(([], Void, mthd), Thread)\<rfloor>"
    by(fastsimp)
  with ThreadMmT have Tseesrun: "P \<turnstile> Thread sees run: []\<rightarrow>Void = mthd in Thread"
    by(auto simp add: Method_def)
  from sees_method_mono[OF PCThread wf Tseesrun] show ?thesis by auto
qed

lemma wf_Object_method_empty:
  assumes wf: "wf_prog wf_md P"
  and sees: "P \<turnstile> Object sees M: Ts\<rightarrow>T = m in D"
  shows False
proof -
  from wf obtain O' fs ms
    where classO: "class P Object = \<lfloor>(O', fs, ms)\<rfloor>"
    by(fastsimp dest!: is_class_Object simp add: is_class_def)
  from wf classO have "ms = []"
    by(auto simp add: wf_prog_def wf_cdecl_def class_def dest: map_of_is_SomeD bspec)
  with classO sees show False
    by(auto elim: Methods.cases simp: Method_def)
qed

lemma no_sees_wait: "\<lbrakk> wf_prog wfmd P; P \<turnstile> C sees wait: Ts\<rightarrow>Ta = mthd in D \<rbrakk> \<Longrightarrow> False"
by(fastsimp dest: visible_method_exists class_wf map_of_SomeD simp add: wf_cdecl_def)

lemma no_sees_notify: "\<lbrakk> wf_prog wfmd P; P \<turnstile> C sees notify: Ts\<rightarrow>Ta = mthd in D \<rbrakk> \<Longrightarrow> False"
by(fastsimp dest: visible_method_exists class_wf map_of_SomeD simp add: wf_cdecl_def)

lemma no_sees_notifyAll: "\<lbrakk> wf_prog wfmd P; P \<turnstile> C sees notifyAll: Ts\<rightarrow>Ta = mthd in D \<rbrakk> \<Longrightarrow> False"
by(fastsimp dest: visible_method_exists class_wf map_of_SomeD simp add: wf_cdecl_def)

lemma wf_prog_lift:
  assumes wf: "wf_prog (\<lambda>P C bd. A P C bd) P"
  and rule:
  "\<And>wf_md C M Ts C T m bd.
   wf_prog wf_md P \<Longrightarrow>
   P \<turnstile> C sees M:Ts\<rightarrow>T = m in C \<Longrightarrow>   
   set Ts \<subseteq>  types P \<Longrightarrow>
   bd = (M,Ts,T,m) \<Longrightarrow>
   A P C bd \<Longrightarrow>
   B P C bd"
  shows "wf_prog (\<lambda>P C bd. B P C bd) P"
(*<*)
proof -
  from wf show ?thesis
    apply (unfold wf_prog_def wf_cdecl_def)
    apply clarsimp
    apply (drule bspec, assumption)
    apply (unfold wf_mdecl_def)
    apply clarsimp
    apply (drule bspec, assumption)
    apply clarsimp
    apply (frule mdecl_visible [OF wf], assumption+)
    apply (frule is_type_pTs [OF wf], assumption+)
    apply (drule rule [OF wf], assumption+)
    apply auto
    done
qed
(*>*)


subsection{* Well-formedness and field lookup *}

lemma wf_Fields_Ex:
  "\<lbrakk> wf_prog wf_md P; is_class P C \<rbrakk> \<Longrightarrow> \<exists>FDTs. P \<turnstile> C has_fields FDTs"
(*<*)
apply(frule class_Object)
apply(erule (1) subcls1_induct)
 apply(blast intro:has_fields_Object)
apply(blast intro:has_fields_rec dest:subcls1D)
done
(*>*)


lemma has_fields_types:
  "\<lbrakk> P \<turnstile> C has_fields FDTs; (FD,T) \<in> set FDTs; wf_prog wf_md P \<rbrakk> \<Longrightarrow> is_type P T"
(*<*)
apply(induct rule:Fields.induct)
 apply(fastsimp dest!: class_wf simp: wf_cdecl_def wf_fdecl_def)
apply(fastsimp dest!: class_wf simp: wf_cdecl_def wf_fdecl_def)
done
(*>*)


lemma sees_field_is_type:
  "\<lbrakk> P \<turnstile> C sees F:T in D; wf_prog wf_md P \<rbrakk> \<Longrightarrow> is_type P T"
(*<*)
by(fastsimp simp: sees_field_def
            elim: has_fields_types map_of_SomeD[OF map_of_remap_SomeD])
(*>*)


lemma wf_Object_field_empty:
  assumes wf: "wf_prog wf_md P"
  shows "P \<turnstile> Object has_fields []"
proof -
  from wf obtain O' fs ms where classO: "class P Object = \<lfloor>(O', fs, ms)\<rfloor>"
    by -(drule is_class_Object,auto simp add: is_class_def)
  from wf classO have "fs = []"
    by(auto simp add: wf_prog_def wf_cdecl_def class_def dest: map_of_is_SomeD bspec)
  with classO show ?thesis
    by(auto intro: has_fields_Object)
qed

lemma wf_Object_not_has_field [dest]:
  "\<lbrakk> P \<turnstile> Object has F:T in D; wf_prog wf_md P \<rbrakk> \<Longrightarrow> False"
by(auto dest: wf_Object_field_empty has_fields_fun simp add: has_field_def)


end
