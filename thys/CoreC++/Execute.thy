(*  Title:       CoreC++
    Author:      Daniel Wasserrab, Stefan Berghofer
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
*)


header {* \isaheader{Code generation for Semantics and Type System} *}

theory Execute
imports BigStep WellType Executable_Set Efficient_Nat
begin

section{* General redefinitions *}

lemma [code_unfold del]: "op = = Executable_Set.set_eq"
  by simp

lemma [code_unfold]: "List.member = (\<lambda> xs x. ListMem x xs)"
  by (simp add: ListMem_iff member_def expand_fun_eq)

inductive app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "app [] ys ys"
| "app xs ys zs \<Longrightarrow> app (x # xs) ys (x # zs)"

theorem app_eq1: "\<And>ys zs. zs = xs @ ys \<Longrightarrow> app xs ys zs"
  apply (induct xs)
   apply simp
   apply (rule app.intros)
  apply simp
  apply (iprover intro: app.intros)
  done

theorem app_eq2: "app xs ys zs \<Longrightarrow> zs = xs @ ys"
  by (erule app.induct) simp_all

theorem app_eq: "app xs ys zs = (zs = xs @ ys)"
  apply (rule iffI)
   apply (erule app_eq2)
  apply (erule app_eq1)
  done

lemmas [code_ind_set] = rtrancl.rtrancl_refl converse_rtrancl_into_rtrancl


inductive
  casts_aux :: "prog \<Rightarrow> ty \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool"
  for P :: prog
where
  "(case T of Class C \<Rightarrow> False | _ \<Rightarrow> True) \<Longrightarrow> casts_aux P T v v"
| "casts_aux P (Class C) Null Null"
| "\<lbrakk>Subobjs P (last Cs) Cs'; last Cs' = C;
    last Cs = hd Cs'; Cs @ tl Cs' = Ds\<rbrakk> 
  \<Longrightarrow> casts_aux P (Class C) (Ref(a,Cs)) (Ref(a,Ds))"
| "\<lbrakk>Subobjs P (last Cs) Cs'; last Cs' = C; last Cs \<noteq> hd Cs'\<rbrakk>
  \<Longrightarrow> casts_aux P (Class C) (Ref(a,Cs)) (Ref(a,Cs'))"

lemma casts_aux_eq:
"(P \<turnstile> T casts v to v') = casts_aux P T v v'"
apply (rule iffI)
 apply(induct rule:casts_to.induct)
 apply(case_tac T) apply (auto intro:casts_aux.intros)
 apply(simp add:appendPath_def path_via_def) apply (auto intro:casts_aux.intros)
apply(induct rule:casts_aux.induct)
apply(auto intro!:casts_to.intros simp:path_via_def appendPath_def)
done

inductive
  Casts_aux :: "prog \<Rightarrow> ty list \<Rightarrow> val list \<Rightarrow> val list \<Rightarrow> bool"
  for P :: prog
where
  "Casts_aux P [] [] []"
| "\<lbrakk>casts_aux P T v v'; Casts_aux P Ts vs vs'\<rbrakk>
  \<Longrightarrow> Casts_aux P (T#Ts) (v#vs) (v'#vs')"

lemma Casts_aux_eq:
"(P \<turnstile> Ts Casts vs to vs') = Casts_aux P Ts vs vs'"
apply(rule iffI)
 apply(induct rule:Casts_to.induct)
  apply(rule Casts_aux.intros)
 apply(fastsimp intro:Casts_aux.intros simp:casts_aux_eq)
apply(induct rule:Casts_aux.induct)
 apply(rule Casts_Nil)
apply(fastsimp intro:Casts_Cons simp:casts_aux_eq)
done



text{* Redefine map Val vs *}

inductive map_val :: "expr list \<Rightarrow> val list \<Rightarrow> bool"
where
  Nil: "map_val [] []"
| Cons: "map_val xs ys \<Longrightarrow> map_val (Val y # xs) (y # ys)"

inductive map_val2 :: "expr list \<Rightarrow> val list \<Rightarrow> expr list \<Rightarrow> bool"
where
  Nil: "map_val2 [] [] []"
| Cons: "map_val2 xs ys zs \<Longrightarrow> map_val2 (Val y # xs) (y # ys) zs"
| Throw: "map_val2 (throw e # xs) [] (throw e # xs)"

theorem map_val_conv: "(xs = map Val ys) = map_val xs ys"
(*<*)
proof -
  have "\<And>ys. xs = map Val ys \<Longrightarrow> map_val xs ys"
    apply (induct xs type:list)
     apply (case_tac ys)
      apply simp
      apply (rule map_val.Nil)
     apply simp
    apply (case_tac ys)
     apply simp
    apply simp
    apply (erule conjE)
    apply (rule map_val.Cons)
    apply simp
    done
  moreover have "map_val xs ys \<Longrightarrow> xs = map Val ys"
    by (erule map_val.induct) simp+
  ultimately show ?thesis ..
qed
(*>*)

theorem map_val2_conv:
 "(xs = map Val ys @ throw e # zs) = map_val2 xs ys (throw e # zs)"
(*<*)
proof -
  have "\<And>ys. xs = map Val ys @ throw e # zs \<Longrightarrow> map_val2 xs ys (throw e # zs)"
    apply (induct xs type:list)
     apply (case_tac ys)
      apply simp
     apply simp
    apply simp
    apply (case_tac ys)
     apply simp
     apply (rule map_val2.Throw)
    apply simp
    apply (rule map_val2.Cons)
    apply simp
    done
  moreover have "map_val2 xs ys (throw e # zs) \<Longrightarrow> xs = map Val ys @ throw e # zs"
    by (erule map_val2.induct) simp+
  ultimately show ?thesis ..
qed
(*>*)

text {* Redefine MethodDefs and FieldDecls *}

(* FIXME: These predicates should be defined inductively in the first place! *)

definition MethodDefs' :: "prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> path \<Rightarrow> method \<Rightarrow> bool" where
  "MethodDefs' P C M Cs mthd \<equiv> (Cs, mthd) \<in> MethodDefs P C M"

definition FieldDecls' :: "prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> path \<Rightarrow> ty \<Rightarrow> bool" where
  "FieldDecls' P C F Cs T \<equiv> (Cs, T) \<in> FieldDecls P C F"

definition MinimalMethodDefs' :: "prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> path \<Rightarrow> method \<Rightarrow> bool" where
  "MinimalMethodDefs' P C M Cs mthd \<equiv> (Cs, mthd) \<in> MinimalMethodDefs P C M"

lemma [code_ind params: 3]:
  "Subobjs P C Cs \<Longrightarrow> class P (last Cs) = \<lfloor>(Bs,fs,ms)\<rfloor> \<Longrightarrow> map_of ms M =  \<lfloor>mthd\<rfloor> \<Longrightarrow>
   MethodDefs' P C M Cs mthd"
 by (simp add: MethodDefs_def MethodDefs'_def)

lemma [code_ind params: 3]:
  "Subobjs P C Cs \<Longrightarrow> class P (last Cs) = \<lfloor>(Bs,fs,ms)\<rfloor> \<Longrightarrow> map_of fs F =  \<lfloor>T\<rfloor> \<Longrightarrow>
   FieldDecls' P C F Cs T"
 by (simp add: FieldDecls_def FieldDecls'_def)

lemma [code_ind params: 3]:
  "MethodDefs' P C M Cs mthd \<Longrightarrow> 
   \<forall>(Cs', mthd)\<in>{(Cs', mthd). MethodDefs' P C M Cs' mthd}. P,C \<turnstile> Cs' \<sqsubseteq> Cs \<longrightarrow> Cs' = Cs \<Longrightarrow>
   MinimalMethodDefs' P C M Cs mthd"
  by (simp add:MinimalMethodDefs_def MinimalMethodDefs'_def MethodDefs'_def)

lemma ForallMethodDefs_eq:
  "(\<forall>(Cs, mthd)\<in>MethodDefs P C M. Q Cs) = (\<forall>(Cs, mthd)\<in>{(Cs, mthd). MethodDefs' P C M Cs mthd}. Q Cs)"
  by (auto simp add: MethodDefs'_def)

lemma ForallFieldDecls_eq:
  "(\<forall>(Cs, T)\<in>FieldDecls P C F. Q Cs) = (\<forall>(Cs, T)\<in>{(Cs, T). FieldDecls' P C F Cs T}. Q Cs)"
  by (auto simp add: FieldDecls'_def)

definition OverriderMethodDefs' :: "prog \<Rightarrow> subobj \<Rightarrow> mname \<Rightarrow> path \<Rightarrow> method \<Rightarrow> bool" where
  "OverriderMethodDefs' P R M Cs mthd \<equiv> (Cs, mthd) \<in> OverriderMethodDefs P R M"

lemma OverriderMethodDefs_card_eq:
  "card (OverriderMethodDefs P R M) = card {(Cs, mthd). OverriderMethodDefs' P R M Cs mthd}"
  by (simp add: OverriderMethodDefs'_def)

lemmas codegen_simps = MethodDefs'_def [symmetric] ForallMethodDefs_eq
  FieldDecls'_def [symmetric] ForallFieldDecls_eq OverriderMethodDefs'_def [symmetric]
  OverriderMethodDefs_card_eq


section {* Rewriting lemmas for Semantic rules *}

text {* Cast *}

lemma StaticUpCast_new1:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>;
    Subobjs P (last Cs) Cs'; last Cs' = C;
    last Cs = hd Cs'; Cs @ tl Cs' = Ds\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Ds),(h,l)\<rangle>"
apply(rule StaticUpCast)
  apply assumption
 apply(fastsimp simp:path_via_def)
apply(simp add:appendPath_def)
done

lemma StaticUpCast_new2:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>;
    Subobjs P (last Cs) Cs'; last Cs' = C;
    last Cs \<noteq> hd Cs'\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),(h,l)\<rangle>"
apply(rule StaticUpCast)
  apply assumption
 apply(fastsimp simp:path_via_def)
apply(simp add:appendPath_def)
done

lemma StaticDownCast_new: 
  "\<lbrakk>P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Ds),s\<^isub>1\<rangle>; app Cs [C] Ds'; app Ds' Cs' Ds\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref(a,Cs@[C]),s\<^isub>1\<rangle>"
apply (rule StaticDownCast)
apply (simp add: app_eq)
done

lemma StaticCastFail_new:
"\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle>\<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>;  \<not> P \<turnstile> (last Cs) \<preceq>\<^sup>* C; C \<notin> set Cs\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW ClassCast,(h,l)\<rangle>"
by (fastsimp intro:StaticCastFail)

lemma StaticUpDynCast_new1:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>;
    Subobjs P (last Cs) Cs'; last Cs' = C;
    \<forall>Cs''\<in>{Cs''. Subobjs P (last Cs) Cs''}. last Cs'' = C \<longrightarrow> Cs' = Cs'';
    last Cs = hd Cs'; Cs @ tl Cs' = Ds\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Ds),(h,l)\<rangle>"
apply(rule StaticUpDynCast)
   apply assumption
  apply(unfold path_unique_def path_via_def)
  apply(rule_tac a="Cs'" in ex1I) apply blast
  apply blast
 apply blast
apply(thin_tac "\<forall>x\<in>?S. ?P x")
apply(simp add:appendPath_def)
done

lemma StaticUpDynCast_new2:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>;
    Subobjs P (last Cs) Cs'; last Cs' = C;
    \<forall>Cs''\<in>{Cs''. Subobjs P (last Cs) Cs''}. last Cs'' = C \<longrightarrow> Cs' = Cs'';
    last Cs \<noteq> hd Cs'\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),(h,l)\<rangle>"
apply(rule StaticUpDynCast)
   apply assumption
  apply(unfold path_unique_def path_via_def)
  apply(rule_tac a="Cs'" in ex1I) apply blast
  apply blast
 apply blast
apply(thin_tac "\<forall>x\<in>?S. ?P x")
apply(simp add:appendPath_def)
done

lemma StaticDownDynCast_new: 
  "\<lbrakk>P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Ds),s\<^isub>1\<rangle>; app Cs [C] Ds'; app Ds' Cs' Ds\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref(a,Cs@[C]),s\<^isub>1\<rangle>"
apply (rule StaticDownDynCast)
apply (simp add: app_eq)
done

lemma DynCast_new:
"\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>; h a = Some(D,S);
   Subobjs P D Cs'; last Cs' = C;
    \<forall>Cs''\<in>{Cs''. Subobjs P D Cs''}. last Cs'' = C \<longrightarrow> Cs' = Cs''\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),(h,l)\<rangle>"
apply(rule DynCast)
apply(unfold path_via_def path_unique_def)
apply blast+
done

lemma DynCastFail_new:
"\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle>\<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>; h a = Some(D,S);
  \<forall>Cs'\<in>{Cs'. Subobjs P D Cs'}. last Cs' = C \<longrightarrow> 
       (\<exists>Cs''\<in>{Cs''. Subobjs P D Cs''}. last Cs'' = C \<and> Cs' \<noteq> Cs'');
  \<forall>Cs'\<in>{Cs'. Subobjs P (last Cs) Cs'}. last Cs' = C \<longrightarrow> 
       (\<exists>Cs''\<in>{Cs''. Subobjs P (last Cs) Cs''}. last Cs'' = C \<and> Cs' \<noteq> Cs'');
  C \<notin> set Cs \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,(h,l)\<rangle>"
apply(rule DynCastFail)
    apply assumption
   apply assumption
  apply (fastsimp simp:path_unique_def)
 apply (fastsimp simp:path_unique_def)
apply assumption
done

text {* Assignment *}

lemma LAss_new:
  "\<lbrakk>P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,(h, l)\<rangle>; E V = \<lfloor>T\<rfloor>;
    casts_aux P T v v'; l' = l(V \<mapsto> v')\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>V:=e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v',(h, l')\<rangle>"
  apply (rule LAss)
  apply assumption+
  apply(simp add:casts_aux_eq)
  apply assumption
  done

text {* Fields *}

lemma FAcc_new1:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),(h,l)\<rangle>; h a = Some(D,S);
     last Cs' = hd Cs; Cs' @ tl Cs = Ds; (Ds,fs) \<in> S; fs F = Some v \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,l)\<rangle>"
apply(rule FAcc)
apply assumption+
apply(simp add:appendPath_def)
apply assumption+
done

lemma FAcc_new2:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),(h,l)\<rangle>; h a = Some(D,S);
     last Cs' \<noteq> hd Cs; (Cs,fs) \<in> S; fs F = Some v \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,l)\<rangle>"
apply(rule FAcc)
apply assumption+
apply(simp add:appendPath_def)
apply assumption+
done

lemma FAss_new1:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),s\<^isub>1\<rangle>; P,E \<turnstile> \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^isub>2,l\<^isub>2)\<rangle>;
     h\<^isub>2 a = Some(D,S); P \<turnstile> (last Cs') has least F:T via Cs; 
     casts_aux P T v v'; last Cs' = hd Cs; Cs' @ tl Cs = Ds; 
     (Ds,fs) \<in> S; fs' = fs(F\<mapsto>v'); 
     S' = S - {(Ds,fs)} \<union> {(Ds,fs')}; h\<^isub>2' = h\<^isub>2(a\<mapsto>(D,S'))\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^isub>1\<bullet>F{Cs}:=e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v',(h\<^isub>2',l\<^isub>2)\<rangle>"
apply(rule FAss)
apply assumption+
apply(simp add:casts_aux_eq)
apply(simp add:appendPath_def)
apply assumption+
done

lemma FAss_new2:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),s\<^isub>1\<rangle>; P,E \<turnstile> \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^isub>2,l\<^isub>2)\<rangle>;
     h\<^isub>2 a = Some(D,S); P \<turnstile> (last Cs') has least F:T via Cs; 
     casts_aux P T v v'; last Cs' \<noteq> hd Cs; (Cs,fs) \<in> S; fs' = fs(F\<mapsto>v'); 
     S' = S - {(Cs,fs)} \<union> {(Cs,fs')}; h\<^isub>2' = h\<^isub>2(a\<mapsto>(D,S'))\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^isub>1\<bullet>F{Cs}:=e\<^isub>2,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v',(h\<^isub>2',l\<^isub>2)\<rangle>"
apply(rule FAss)
apply assumption+
apply(simp add:casts_aux_eq)
apply(simp add:appendPath_def)
apply assumption+
done

text {* Call *}

lemma CallParamsThrow_new:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>1\<rangle>; P,E \<turnstile> \<langle>es,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,s\<^isub>2\<rangle>;
     map_val2 evs vs (throw ex # es') \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> \<langle>Call e Copt M es,s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^isub>2\<rangle>"
apply(rule eval_evals.CallParamsThrow, assumption+)
apply(simp add: map_val2_conv[symmetric])
done

lemma CallNull_new:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle>;  P,E \<turnstile> \<langle>es,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,s\<^isub>2\<rangle>; map_val evs vs \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Call e Copt M es,s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>2\<rangle>"
apply(rule CallNull, assumption+)
apply(simp add: map_val_conv[symmetric])
done

lemma Call_new:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^isub>1\<rangle>;  P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^isub>2,l\<^isub>2)\<rangle>;
     map_val evs vs; h\<^isub>2 a = Some(C,S); 
     P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds;
     P \<turnstile> C has least M = (Ts,T,pns,body) via Cs'; length vs = length pns; 
     Casts_aux P Ts vs vs'; l\<^isub>2' = [this\<mapsto>Ref (a,Cs'), pns[\<mapsto>]vs'];
     new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body   | _  \<Rightarrow> body);
     P,E(this\<mapsto>Class(last Cs'), pns[\<mapsto>]Ts) \<turnstile> \<langle>new_body,(h\<^isub>2,l\<^isub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>2)\<rangle>"
apply(rule Call, assumption+)
apply(simp add: map_val_conv[symmetric])
apply assumption+
apply(rule dyn_unique)
apply assumption+
apply(simp add:Casts_aux_eq)
apply assumption+
done


lemma Overrider1:
  "P \<turnstile> (ldc R) has least M = mthd' via Cs' \<Longrightarrow> 
   MinimalMethodDefs' P (mdc R) M Cs mthd \<Longrightarrow>
   last (snd R) = hd Cs' \<Longrightarrow> P,mdc R \<turnstile> Cs \<sqsubseteq> (snd R)@tl Cs' \<Longrightarrow>
   OverriderMethodDefs' P R M Cs mthd"
apply(simp add:OverriderMethodDefs_def OverriderMethodDefs'_def MinimalMethodDefs'_def appendPath_def)
apply(rule_tac x="Cs'" in exI)
apply clarsimp
apply(cases mthd')
apply blast
done

lemma Overrider2:
  "P \<turnstile> (ldc R) has least M = mthd' via Cs' \<Longrightarrow> 
   MinimalMethodDefs' P (mdc R) M Cs mthd \<Longrightarrow>
   last (snd R) \<noteq> hd Cs' \<Longrightarrow> P,mdc R \<turnstile> Cs \<sqsubseteq> Cs' \<Longrightarrow>
   OverriderMethodDefs' P R M Cs mthd"
apply(simp add:OverriderMethodDefs_def OverriderMethodDefs'_def MinimalMethodDefs'_def appendPath_def)
apply(rule_tac x="Cs'" in exI) 
apply clarsimp
apply(cases mthd')
apply blast
done


lemma ambiguous: "(\<not> P \<turnstile> C has least M = mthd via Cs') = 
  (MethodDefs' P C M Cs' mthd \<longrightarrow> (\<exists>(Cs'', mthd')\<in>{(Cs'', mthd'). MethodDefs' P C M Cs'' mthd'}. \<not> P,C \<turnstile> Cs' \<sqsubseteq> Cs''))"
  by (auto simp:LeastMethodDef_def MethodDefs'_def)

lemma CallOverrider_new1:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^isub>1\<rangle>;  P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^isub>2,l\<^isub>2)\<rangle>;
     map_val evs vs; h\<^isub>2 a = Some(C,S);
     P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds;
     \<forall>(Cs',mthd)\<in>{(Cs',mthd). MethodDefs' P (last Cs) M Cs' mthd}. P,last Cs \<turnstile> Ds \<sqsubseteq> Cs';
     \<forall>(Cs',mthd)\<in>{(Cs',mthd). MethodDefs' P C M Cs' mthd}. \<exists>(Cs'',mthd)\<in>{(Cs'',mthd). MethodDefs' P C M Cs'' mthd}. \<not> P,C \<turnstile> Cs' \<sqsubseteq> Cs'';
     last Cs = hd Ds; P \<turnstile> (C,Cs@tl Ds) has overrider M = (Ts,T,pns,body) via Cs';
     length vs = length pns; Casts_aux P Ts vs vs'; 
     l\<^isub>2' = [this\<mapsto>Ref (a,Cs'), pns[\<mapsto>]vs']; 
     new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body   | _  \<Rightarrow> body);
     P,E(this\<mapsto>Class(last Cs'), pns[\<mapsto>]Ts) \<turnstile> \<langle>new_body,(h\<^isub>2,l\<^isub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>2)\<rangle>"
apply(rule Call,assumption)
apply(simp add: map_val_conv[symmetric])
apply assumption+
apply(rule dyn_ambiguous)
apply(simp add:ambiguous,blast)
apply(simp add:appendPath_def)
apply assumption
apply(simp add:Casts_aux_eq)
apply assumption+
done

lemma CallOverrider_new2:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^isub>1\<rangle>;  P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^isub>2,l\<^isub>2)\<rangle>;
     map_val evs vs; h\<^isub>2 a = Some(C,S);
     P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds;
     \<forall>(Cs',mthd)\<in>{(Cs',mthd). MethodDefs' P (last Cs) M Cs' mthd}. P,last Cs \<turnstile> Ds \<sqsubseteq> Cs';
     \<forall>(Cs',mthd)\<in>{(Cs',mthd). MethodDefs' P C M Cs' mthd}. \<exists>(Cs'',mthd)\<in>{(Cs',mthd). MethodDefs' P C M Cs' mthd}. \<not> P,C \<turnstile> Cs' \<sqsubseteq> Cs'';
     last Cs \<noteq> hd Ds; P \<turnstile> (C,Ds) has overrider M = (Ts,T,pns,body) via Cs';
     length vs = length pns; Casts_aux P Ts vs vs';
     l\<^isub>2' = [this\<mapsto>Ref (a,Cs'), pns[\<mapsto>]vs']; 
     new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body   | _  \<Rightarrow> body);
     P,E(this\<mapsto>Class(last Cs'), pns[\<mapsto>]Ts) \<turnstile> \<langle>new_body,(h\<^isub>2,l\<^isub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>2)\<rangle>"
apply(rule Call,assumption)
apply(simp add: map_val_conv[symmetric])
apply assumption+
apply(rule dyn_ambiguous)
apply(simp add:ambiguous,blast)
apply(simp add:appendPath_def)
apply assumption
apply(simp add:Casts_aux_eq)
apply assumption+
done

lemma StaticCall_new1:
  assumes evals:"P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^isub>2,l\<^isub>2)\<rangle>" and map:"map_val evs vs"
  and path:"Subobjs P (last Cs) Cs''" "last Cs'' = C"
  and unique:"\<forall>Xs\<in>{Xs. Subobjs P (last Cs) Xs}. last Xs = C \<longrightarrow> Cs'' = Xs"
  and eq1:"last Cs = hd Cs''" and eq2:"last Cs'' = hd Cs'"
  and append:"Ds = (Cs@tl Cs'')@tl Cs'" and casts:"Casts_aux P Ts vs vs'"
  and rest:"P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^isub>1\<rangle>"  "length vs = length pns"
    "l\<^isub>2' = [this\<mapsto>Ref (a,Ds), pns[\<mapsto>]vs']"
    "P \<turnstile> C has least M = (Ts,T,pns,body) via Cs'"
    "P,E(this\<mapsto>Class(last Ds), pns[\<mapsto>]Ts) \<turnstile> \<langle>body,(h\<^isub>2,l\<^isub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>3)\<rangle>"
  shows "P,E \<turnstile> \<langle>e\<bullet>(C::)M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>2)\<rangle>"
proof -
  from evals map have evalsVals:"P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^isub>2,l\<^isub>2)\<rangle>"
    by(simp add: map_val_conv[symmetric])
  from path have path_via:"P \<turnstile> Path (last Cs) to C via Cs''"
    by(simp add:path_via_def)
  from path unique have path_unique:"P \<turnstile> Path (last Cs) to C unique"
    by(auto simp:path_unique_def)
  from path have notempty:"Cs'' \<noteq> []" by -(rule Subobjs_nonempty)
  have "last(Cs@tl Cs'') = hd Cs'"
  proof(cases "tl Cs'' = []")
    case True 
    with notempty have Cs'':"Cs'' = [hd Cs'']" by(fastsimp dest:hd_Cons_tl)
    hence "last Cs'' = hd Cs''" by(cases Cs'') auto
    with eq1 eq2 True show ?thesis by simp
  next
    case False
    from notempty eq2 have "last(hd Cs''#tl Cs'') = hd Cs'"
      by(fastsimp dest:hd_Cons_tl)
    with False show ?thesis by(simp add:last_append)
  qed
  with eq1 eq2 append have Ds:"Ds = (Cs@\<^sub>pCs'')@\<^sub>pCs'"
    by(simp add:appendPath_def)
  from casts have "P \<turnstile> Ts Casts vs to vs'" by(simp add:Casts_aux_eq)
  with evalsVals path_via path_unique Ds rest show ?thesis
    by -(rule StaticCall)
qed

lemma StaticCall_new2:
  assumes evals:"P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^isub>2,l\<^isub>2)\<rangle>" and map:"map_val evs vs"
  and path:"Subobjs P (last Cs) Cs''" "last Cs'' = C"
  and unique:"\<forall>Xs\<in>{Xs. Subobjs P (last Cs) Xs}. last Xs = C \<longrightarrow> Cs'' = Xs"
  and eq1:"last Cs = hd Cs''" and eq2:"last Cs'' \<noteq> hd Cs'"
  and append:"Ds = Cs'" and casts:"Casts_aux P Ts vs vs'"
  and rest:"P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^isub>1\<rangle>"  "length vs = length pns"
    "l\<^isub>2' = [this\<mapsto>Ref (a,Ds), pns[\<mapsto>]vs']"
    "P \<turnstile> C has least M = (Ts,T,pns,body) via Cs'"
    "P,E(this\<mapsto>Class(last Ds), pns[\<mapsto>]Ts) \<turnstile> \<langle>body,(h\<^isub>2,l\<^isub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>3)\<rangle>"
  shows "P,E \<turnstile> \<langle>e\<bullet>(C::)M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>2)\<rangle>"
proof -
  from evals map have evalsVals:"P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^isub>2,l\<^isub>2)\<rangle>"
    by(simp add: map_val_conv[symmetric])
  from path have path_via:"P \<turnstile> Path (last Cs) to C via Cs''"
    by(simp add:path_via_def)
  from path unique have path_unique:"P \<turnstile> Path (last Cs) to C unique"
    by(auto simp:path_unique_def)
  from path have notempty:"Cs'' \<noteq> []" by -(rule Subobjs_nonempty)
  have "last(Cs@tl Cs'') \<noteq> hd Cs'"
  proof(cases "tl Cs'' = []")
    case True 
    with notempty have Cs'':"Cs'' = [hd Cs'']" by(fastsimp dest:hd_Cons_tl)
    hence "last Cs'' = hd Cs''" by(cases Cs'') auto
    with eq1 eq2 True show ?thesis by simp
  next
    case False
    from notempty eq2 have "last(hd Cs''#tl Cs'') \<noteq> hd Cs'"
      by(fastsimp dest:hd_Cons_tl)
    with False show ?thesis by(simp add:last_append)
  qed
  with eq1 eq2 append have Ds:"Ds = (Cs@\<^sub>pCs'')@\<^sub>pCs'"
    by(simp add:appendPath_def)
  from casts have "P \<turnstile> Ts Casts vs to vs'" by(simp add:Casts_aux_eq)
  with evalsVals path_via path_unique Ds rest show ?thesis
    by -(rule StaticCall)
qed

lemma StaticCall_new3:
  assumes evals:"P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^isub>2,l\<^isub>2)\<rangle>" and map:"map_val evs vs"
  and path:"Subobjs P (last Cs) Cs''" "last Cs'' = C"
  and unique:"\<forall>Xs\<in>{Xs. Subobjs P (last Cs) Xs}. last Xs = C \<longrightarrow> Cs'' = Xs"
  and eq1:"last Cs \<noteq> hd Cs''" and eq2:"last Cs'' = hd Cs'"
  and append:"Ds = Cs''@tl Cs'" and casts:"Casts_aux P Ts vs vs'"
  and rest:"P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^isub>1\<rangle>"  "length vs = length pns"
    "l\<^isub>2' = [this\<mapsto>Ref (a,Ds), pns[\<mapsto>]vs']"
    "P \<turnstile> C has least M = (Ts,T,pns,body) via Cs'"
    "P,E(this\<mapsto>Class(last Ds), pns[\<mapsto>]Ts) \<turnstile> \<langle>body,(h\<^isub>2,l\<^isub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>3)\<rangle>"
  shows "P,E \<turnstile> \<langle>e\<bullet>(C::)M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>2)\<rangle>"
proof -
  from evals map have evalsVals:"P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^isub>2,l\<^isub>2)\<rangle>"
    by(simp add: map_val_conv[symmetric])
  from path have path_via:"P \<turnstile> Path (last Cs) to C via Cs''"
    by(simp add:path_via_def)
  from path unique have path_unique:"P \<turnstile> Path (last Cs) to C unique"
    by(auto simp:path_unique_def)
  from eq1 eq2 append have Ds:"Ds = (Cs@\<^sub>pCs'')@\<^sub>pCs'"
    by(simp add:appendPath_def)
  from casts have "P \<turnstile> Ts Casts vs to vs'" by(simp add:Casts_aux_eq)
  with evalsVals path_via path_unique Ds rest show ?thesis
    by -(rule StaticCall)
qed

lemma StaticCall_new4:
  assumes evals:"P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^isub>2,l\<^isub>2)\<rangle>" and map:"map_val evs vs"
  and path:"Subobjs P (last Cs) Cs''" "last Cs'' = C"
  and unique:"\<forall>Xs\<in>{Xs. Subobjs P (last Cs) Xs}. last Xs = C \<longrightarrow> Cs'' = Xs"
  and eq1:"last Cs \<noteq> hd Cs''" and eq2:"last Cs'' \<noteq> hd Cs'"
  and append:"Ds = Cs'" and casts:"Casts_aux P Ts vs vs'"
  and rest:"P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^isub>1\<rangle>"  "length vs = length pns"
    "l\<^isub>2' = [this\<mapsto>Ref (a,Ds), pns[\<mapsto>]vs']"
    "P \<turnstile> C has least M = (Ts,T,pns,body) via Cs'"
    "P,E(this\<mapsto>Class(last Ds), pns[\<mapsto>]Ts) \<turnstile> \<langle>body,(h\<^isub>2,l\<^isub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>3)\<rangle>"
  shows "P,E \<turnstile> \<langle>e\<bullet>(C::)M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>2)\<rangle>"
proof -
  from evals map have evalsVals:"P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^isub>2,l\<^isub>2)\<rangle>"
    by(simp add: map_val_conv[symmetric])
  from path have path_via:"P \<turnstile> Path (last Cs) to C via Cs''"
    by(simp add:path_via_def)
  from path unique have path_unique:"P \<turnstile> Path (last Cs) to C unique"
    by(auto simp:path_unique_def)
  from eq1 eq2 append have Ds:"Ds = (Cs@\<^sub>pCs'')@\<^sub>pCs'"
    by(simp add:appendPath_def)
  from casts have "P \<turnstile> Ts Casts vs to vs'" by(simp add:Casts_aux_eq)
  with evalsVals path_via path_unique Ds rest show ?thesis
    by -(rule StaticCall)
qed

section{* Rewriting lemmas for Type rules *}


lemma WTDynCast_new1:
  "\<lbrakk> P,E \<turnstile> e :: Class D; is_class P C;
    Subobjs P D Cs'; last Cs' = C;
    \<forall>Cs''\<in>{Cs''. Subobjs P D Cs''}. last Cs'' = C \<longrightarrow> Cs' = Cs''\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> Cast C e :: Class C"
  by (rule WTDynCast,auto simp add: path_unique_def)

lemma WTDynCast_new2:
  "\<lbrakk> P,E \<turnstile> e :: Class D; is_class P C;
     \<forall>Cs''\<in>{Cs''. Subobjs P D Cs''}. last Cs'' = C \<longrightarrow> False\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> Cast C e :: Class C"
  by (rule WTDynCast,auto simp add: path_via_def)

lemma WTStaticCast_new1:
  "\<lbrakk> P,E \<turnstile> e :: Class D; is_class P C;
    Subobjs P D Cs'; last Cs' = C;
    \<forall>Cs''\<in>{Cs'. Subobjs P D Cs'}. last Cs'' = C \<longrightarrow> Cs' = Cs''\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<lparr>C\<rparr>e :: Class C"
  by (rule WTStaticCast,auto simp add: path_unique_def)

lemma WTStaticCast_new2:
"\<lbrakk>P,E \<turnstile> e :: Class D; is_class P C; P \<turnstile> C \<preceq>\<^sup>* D;
  \<forall>Cs\<in>{Cs. Subobjs P C Cs}. last Cs = D \<longrightarrow> Subobjs\<^isub>R P C Cs \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<lparr>C\<rparr>e :: Class C"
  by (rule WTStaticCast,auto simp:path_via_def)

lemma WTBinOp1: "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: T;  P,E \<turnstile> e\<^isub>2 :: T\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^isub>1 \<guillemotleft>Eq\<guillemotright> e\<^isub>2 :: Boolean"
  apply (rule WTBinOp)
  apply assumption+
  apply simp
  done

lemma WTBinOp2: "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: Integer;  P,E \<turnstile> e\<^isub>2 :: Integer \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^isub>1 \<guillemotleft>Add\<guillemotright> e\<^isub>2 :: Integer"
  apply (rule WTBinOp)
  apply assumption+
  apply simp
  done

lemma WTStaticCall_new:
  "\<lbrakk> P,E \<turnstile> e :: Class C'; Subobjs P C' Cs'; last Cs' = C;
    \<forall>Cs''\<in>{Cs''. Subobjs P C' Cs''}. last Cs'' = C \<longrightarrow> Cs' = Cs'';
     P \<turnstile> C has least M = (Ts,T,m) via Cs; P,E \<turnstile> es [::] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>(C::)M(es) :: T"
  apply(rule WTStaticCall)
  apply assumption
  apply(auto simp:path_unique_def)
  done

lemma [code_ind]:
  "\<lbrakk>Subobjs P C Cs'; last Cs' = D;
    \<forall>Cs''\<in>{Cs''. Subobjs P C Cs''}. last Cs'' = D \<longrightarrow> Cs' = Cs'' \<rbrakk> 
\<Longrightarrow> P \<turnstile> Class C \<le> Class D"
by(rule widen_subcls,auto simp:path_unique_def)

lemmas [code_ind] = widen_refl widen_null


section{* Code generation *}

lemmas [code_ind] = 
 Overrider1[simplified LeastMethodDef_def codegen_simps, OF conjI]
 Overrider2[simplified LeastMethodDef_def codegen_simps, OF conjI]

 (* Semantic rules *)
 eval_evals.New eval_evals.NewFail
 StaticUpCast_new1 StaticUpCast_new2 StaticDownCast_new
 eval_evals.StaticCastNull StaticCastFail_new eval_evals.StaticCastThrow
 StaticUpDynCast_new1 StaticUpDynCast_new2 StaticDownDynCast_new
 DynCast_new eval_evals.DynCastNull
 DynCastFail_new eval_evals.DynCastThrow
 eval_evals.Val eval_evals.Var
 eval_evals.BinOp eval_evals.BinOpThrow1 eval_evals.BinOpThrow2
 LAss_new eval_evals.LAssThrow FAcc_new1 FAcc_new2 
 FAss_new1[simplified LeastFieldDecl_def codegen_simps, OF _ _ _ conjI]
 FAss_new2[simplified LeastFieldDecl_def codegen_simps, OF _ _ _ conjI]
 eval_evals.FAssNull eval_evals.FAssThrow1 eval_evals.FAssThrow2
 eval_evals.CallObjThrow CallNull_new CallParamsThrow_new 
 Call_new[simplified LeastMethodDef_def codegen_simps, OF _ _ _ _ conjI conjI]
 CallOverrider_new1[simplified FinalOverriderMethodDef_def LeastMethodDef_def codegen_simps,
                    OF _ _ _ _ conjI _ _ _ conjI]
 CallOverrider_new2[simplified FinalOverriderMethodDef_def LeastMethodDef_def codegen_simps,
                    OF _ _ _ _ conjI _ _ _ conjI]
 StaticCall_new1[simplified FinalOverriderMethodDef_def LeastMethodDef_def codegen_simps,
                 OF _ _ _ _ _ _ _ _ _ _ _ _ conjI]
 StaticCall_new2[simplified FinalOverriderMethodDef_def LeastMethodDef_def codegen_simps,
                 OF _ _ _ _ _ _ _ _ _ _ _ _ conjI]
 StaticCall_new3[simplified FinalOverriderMethodDef_def LeastMethodDef_def codegen_simps,
                 OF _ _ _ _ _ _ _ _ _ _ _ _ conjI]
 StaticCall_new4[simplified FinalOverriderMethodDef_def LeastMethodDef_def codegen_simps,
                 OF _ _ _ _ _ _ _ _ _ _ _ _ conjI]
 eval_evals.Block eval_evals.Seq eval_evals.SeqThrow
 eval_evals.CondT eval_evals.CondF eval_evals.CondThrow
 eval_evals.WhileF eval_evals.WhileT 
 eval_evals.WhileCondThrow eval_evals.WhileBodyThrow
 eval_evals.Throw eval_evals.ThrowNull eval_evals.ThrowThrow
 eval_evals.Nil eval_evals.Cons eval_evals.ConsThrow

 (* Type rules *)
 WT_WTs.WTNew WTDynCast_new1 WTDynCast_new2
 WTStaticCast_new1 WTStaticCast_new2
 WT_WTs.WTVal WT_WTs.WTVar WTBinOp1 WTBinOp2 WT_WTs.WTLAss
 WT_WTs.WTFAcc[unfolded LeastFieldDecl_def codegen_simps, OF _ conjI]
 WT_WTs.WTFAss[unfolded LeastFieldDecl_def codegen_simps, OF _ conjI]
 WT_WTs.WTCall[unfolded LeastMethodDef_def codegen_simps, OF _ conjI]
 WTStaticCall_new[unfolded LeastMethodDef_def codegen_simps, OF _ _ _ _ conjI]
 WT_WTs.WTBlock WT_WTs.WTSeq WT_WTs.WTCond WT_WTs.WTWhile WT_WTs.WTThrow
 WT_WTs.WTNil WT_WTs.WTCons

(* A hack to make set operations work on sets with function types *)

consts_code
  "insert :: ('a \<times> ('b \<Rightarrow> 'c)) \<Rightarrow> ('a \<times> ('b \<Rightarrow> 'c)) set \<Rightarrow> ('a \<times> ('b \<Rightarrow> 'c)) set"
    ("(fn x => fn {*Set*} xs => {*Set*} (Library.insert (eq'_fst (op =)) x xs))")
  "Executable_Set.union :: ('a \<times> ('b \<Rightarrow> 'c)) set \<Rightarrow> ('a \<times> ('b \<Rightarrow> 'c)) set => ('a \<times> ('b \<Rightarrow> 'c)) set"
    ("(fn {*Set*} xs => fn {*Set*} ys => {*Set*} (Library.union (eq'_fst (op =)) xs ys))")
  "Executable_Set.subtract :: ('a \<times> ('b \<Rightarrow> 'c)) set \<Rightarrow> ('a \<times> ('b \<Rightarrow> 'c)) set \<Rightarrow> ('a \<times> ('b \<Rightarrow> 'c)) set"
    ("(fn {*Set*} xs => fn {*Set*} ys => {*Set*} (Library.subtract (eq'_fst (op =)) xs ys))")

consts_code
  "new_Addr"
   ("\<module>new'_addr {* 0::nat *} {* Suc *}
               {* %x. case x of None => True | Some y => False *} {* Some *}")
attach {*
fun new_addr z s alloc some hp =
  let fun nr i = if alloc (hp i) then some i else nr (s i);
  in nr z end;
*}

  "undefined" ("(raise ERROR \"undefined\")")


text{* Definition of program examples *}



text{* {\ldots}and off we go *}

  (* Examples with no prog needed *)
code_module NoProg
contains
  test0 = "[],empty \<turnstile> \<langle>{''V'':Integer; ''V'' :=  Val(Intg 5);; Var ''V''},(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
  test1 = "[],empty \<turnstile> \<langle>Val(Intg 5),(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
  test2 = "[],empty \<turnstile> \<langle>(Val(Intg 5)) \<guillemotleft>Add\<guillemotright> (Val(Intg 6)),(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
  test3 = "[],[''V''\<mapsto>Integer] \<turnstile> \<langle>(Var ''V'') \<guillemotleft>Add\<guillemotright> (Val(Intg 6)),
                                       (empty,[''V''\<mapsto>Intg 77])\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
  test4 = "[],[''V''\<mapsto>Integer] \<turnstile> \<langle>''V'' := Val(Intg 6),(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
  testWhile = "[],[''V''\<mapsto>Integer,''a''\<mapsto>Integer,''b''\<mapsto>Integer,''mult''\<mapsto>Integer]
  \<turnstile> \<langle>(''a'' := Val(Intg 3));;(''b'' := Val(Intg 4));;(''mult'' := Val(Intg 0));;
     (''V'' := Val(Intg 1));;
     while (Var ''V'' \<guillemotleft>Eq\<guillemotright> Val(Intg 1))((''mult'' := Var ''mult'' \<guillemotleft>Add\<guillemotright> Var ''b'');;
     (''a'' := Var ''a'' \<guillemotleft>Add\<guillemotright> Val(Intg -1));;
     (''V'' := (if(Var ''a'' \<guillemotleft>Eq\<guillemotright> Val(Intg 0)) Val(Intg 0) else Val(Intg 1)))),
     (empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

  testIf = "[],[''a''\<mapsto>Integer, ''b''\<mapsto>Integer, ''c''\<mapsto> Integer, ''cond''\<mapsto>Boolean] \<turnstile> \<langle>''a'' := Val(Intg 17);; ''b'' := Val(Intg 13);; ''c'' := Val(Intg 42);; ''cond'' := true;; if (Var ''cond'') (Var ''a'' \<guillemotleft>Add\<guillemotright> Var ''b'') else (Var ''a'' \<guillemotleft>Add\<guillemotright> Var ''c''),(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

  V = "''V''"
  mult = "''mult''"

ML {* local open NoProg in val Val (Intg 5) = fst (DSeq.hd test1) end *}
ML {* local open NoProg in val Val (Intg 11) = fst (DSeq.hd test2) end *}
ML {* local open NoProg in val Val (Intg 83) = fst (DSeq.hd test3) end *}
ML {* local open NoProg in val Some (Intg 6) = 
      let val (_,(h,l)) = DSeq.hd test4 in l V end end *}
ML {* local open NoProg in val Some (Intg 12) = 
      let val (_,(h,l)) = DSeq.hd testWhile in l mult end end *}
ML {* local open NoProg in val Val (Intg 30) = fst (DSeq.hd testIf) end *}


  (* progOverrider examples *)

constdefs
  -- "Overrider example"

  classBottom :: "cdecl"
  "classBottom == (''Bottom'', [Repeats ''Left'', Repeats ''Right''],
                   [(''x'',Integer)],[])" 

  classLeft :: "cdecl"
  "classLeft == (''Left'', [Repeats ''Top''],[],[(''f'', [Class ''Top'', Integer],Integer, [''V'',''W''],Var this \<bullet> ''x'' {[''Left'',''Top'']} \<guillemotleft>Add\<guillemotright> Val (Intg 5))])"

  classRight :: "cdecl"
  "classRight == (''Right'', [Shares ''Right2''],[],
    [(''f'', [Class ''Top'', Integer], Integer,[''V'',''W''],Var this \<bullet> ''x'' {[''Right2'',''Top'']} \<guillemotleft>Add\<guillemotright> Val (Intg 7)),(''g'',[],Class ''Left'',[],new ''Left'')])"

  classRight2 :: "cdecl"
  "classRight2 == (''Right2'', [Repeats ''Top''],[],
    [(''f'', [Class ''Top'', Integer], Integer,[''V'',''W''],Var this \<bullet> ''x'' {[''Right2'',''Top'']} \<guillemotleft>Add\<guillemotright> Val (Intg 9)),(''g'',[],Class ''Top'',[],new ''Top'')])"

  classTop :: "cdecl"
  "classTop == (''Top'', [], [(''x'',Integer)],[])"

  progOverrider :: "cdecl list"
  "progOverrider == [classBottom, classLeft, classRight, classRight2, classTop]"


code_module ProgOverrider
contains
  dynCastSide = "progOverrider,[''V''\<mapsto>Class ''Right''] \<turnstile>
    \<langle>''V'' := new ''Bottom'' ;; Cast ''Left'' (Var ''V''),(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

  dynCastViaSh = "progOverrider,[''V''\<mapsto>Class ''Right2''] \<turnstile> 
    \<langle>''V'' := new ''Right'' ;; Cast ''Right'' (Var ''V''),(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

  block = "progOverrider,[''V''\<mapsto>Integer] \<turnstile> \<langle>''V'' := Val(Intg 42) ;; {''V'':Class ''Left''; ''V'' := new ''Bottom''} ;; Var ''V'',(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

  staticCall = "progOverrider,[''V''\<mapsto>Class ''Right'',''W''\<mapsto>Class ''Bottom''] \<turnstile>
   \<langle>''V'' := new ''Bottom'' ;; ''W'' := new ''Bottom'' ;; 
    ((Cast ''Left'' (Var ''W''))\<bullet>''x''{[''Left'',''Top'']} := Val(Intg 3));;
    (Var ''W''\<bullet>(''Left''::)''f''([Var ''V'',Val(Intg 2)])),(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

  call = "progOverrider,[''V''\<mapsto>Class ''Right2'',''W''\<mapsto>Class ''Left''] \<turnstile> 
  \<langle>''V'' := new ''Right'' ;; ''W'' := new ''Left'' ;; (Var ''V''\<bullet>''f''([Var ''W'',Val(Intg 42)])) \<guillemotleft>Add\<guillemotright> (Var ''W''\<bullet>''f''([Var ''V'',Val(Intg 13)])),(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

  callOverrider = "progOverrider,[''V''\<mapsto>Class ''Right2'',''W''\<mapsto>Class ''Left''] \<turnstile>
  \<langle>''V'' := new ''Bottom'';; (Var ''V'' \<bullet> ''x'' {[''Right2'',''Top'']} := Val(Intg 6));; ''W'' := new ''Left'' ;; Var ''V''\<bullet>''f''([Var ''W'',Val(Intg 42)]),(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

  callClass = "progOverrider,[''V''\<mapsto>Class ''Right2''] \<turnstile>
  \<langle>''V'' := new ''Right'' ;; Var ''V''\<bullet>''g''([]),(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

  fieldAss = "progOverrider,[''V''\<mapsto>Class ''Right2''] \<turnstile> \<langle>''V'' := new ''Right'' ;; 
     (Var ''V''\<bullet>''x''{[''Right2'',''Top'']} := (Val(Intg 42))) ;; 
     (Var ''V''\<bullet>''x''{[''Right2'',''Top'']}),(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

  typeNew = "progOverrider,empty \<turnstile> new ''Bottom'' :: _"
  typeDynCast = "progOverrider,empty \<turnstile> Cast ''Left'' (new ''Bottom'') :: _"
  typeStaticCast = "progOverrider,empty \<turnstile> \<lparr>''Left''\<rparr> (new ''Bottom'') :: _"
  typeVal = "[],empty \<turnstile> Val(Intg 17) :: _"
  typeVar = "[],[''V'' \<mapsto> Integer] \<turnstile> Var ''V'' :: _"
  typeBinOp = "[],empty \<turnstile> (Val(Intg 5)) \<guillemotleft>Eq\<guillemotright> (Val(Intg 6)) :: _" 
  typeLAss = "progOverrider,[''V'' \<mapsto> Class ''Top''] \<turnstile> ''V'' := (new ''Left'') :: _"
  typeFAcc = "progOverrider,empty \<turnstile> (new ''Right'')\<bullet>''x''{[''Right2'',''Top'']} :: _"
  typeFAss = "progOverrider,empty \<turnstile> 
                  (new ''Right'')\<bullet>''x''{[''Right2'',''Top'']} := (Val(Intg 17)) :: _"
  typeStaticCall = "progOverrider,[''V''\<mapsto>Class ''Left''] \<turnstile> ''V'' := new ''Left'' ;; Var ''V''\<bullet>(''Left''::)''f''([new ''Top'', Val(Intg 13)]) :: _"
  typeCall = "progOverrider,[''V''\<mapsto>Class ''Right2''] \<turnstile> ''V'' := new ''Right'' ;; Var ''V''\<bullet>''g''([]) :: _"
  typeBlock = "progOverrider,empty \<turnstile> {''V'':Class ''Top''; ''V'' := new ''Left''} :: _"
  typeCond = "[],empty \<turnstile> if (true) Val(Intg 6) else Val(Intg 9) :: _"
  typeWhile = "[],empty \<turnstile> while (false) Val(Intg 17) :: _"
  typeThrow = "progOverrider,empty \<turnstile> throw (new ''Bottom'') :: _"

  typeBig = "progOverrider,[''V''\<mapsto>Class ''Right2'',''W''\<mapsto>Class ''Left''] \<turnstile> 
  ''V'' := new ''Right'' ;; ''W'' := new ''Left'' ;; (Var ''V''\<bullet>''f''([Var ''W'', Val(Intg 7)])) \<guillemotleft>Add\<guillemotright> (Var ''W''\<bullet>''f''([Var ''V'', Val(Intg 13)])) :: _"

Bottom = "''Bottom''"
Left = "''Left''"
Right = "''Right''"
Top = "''Top''"


ML {* local open ProgOverrider in val Val(Ref(0,[Bottom,Left])) = 
      fst (DSeq.hd dynCastSide) end *}
ML {* local open ProgOverrider in val Val(Ref(0,[Right])) = 
      fst (DSeq.hd dynCastViaSh) end *}
ML {* local open ProgOverrider in val Val(Intg 42) = fst (DSeq.hd block) end *}
ML {* local open ProgOverrider in val Val(Intg 8)  = fst (DSeq.hd staticCall) end *}
ML {* local open ProgOverrider in val Val(Intg 12) = fst (DSeq.hd call) end *}
ML {* local open ProgOverrider in val Val(Ref(1,[Left,Top])) = 
      fst (DSeq.hd callClass) end *}
ML {* local open ProgOverrider in val Val(Intg 42) = fst (DSeq.hd fieldAss) end *}


(* Typing rules *)
ML {* local open ProgOverrider in val Class Bottom = DSeq.hd typeNew end *}
ML {* local open ProgOverrider in val Class Left   = DSeq.hd typeDynCast end *}
ML {* local open ProgOverrider in val Class Left   = DSeq.hd typeStaticCast end *}
ML {* local open ProgOverrider in val Integer      = DSeq.hd typeVal end *}
ML {* local open ProgOverrider in val Integer      = DSeq.hd typeVar end *}
ML {* local open ProgOverrider in val Boolean      = DSeq.hd typeBinOp end *}
ML {* local open ProgOverrider in val Class Top    = DSeq.hd typeLAss end *}
ML {* local open ProgOverrider in val Integer      = DSeq.hd typeFAcc end *}
ML {* local open ProgOverrider in val Integer      = DSeq.hd typeFAss end *}
ML {* local open ProgOverrider in val Integer      = DSeq.hd typeStaticCall end *}
ML {* local open ProgOverrider in val Class Top    = DSeq.hd typeCall end *}
ML {* local open ProgOverrider in val Class Top    = DSeq.hd typeBlock end *}
ML {* local open ProgOverrider in val Integer      = DSeq.hd typeCond end *}
ML {* local open ProgOverrider in val Void         = DSeq.hd typeThrow end *}
ML {* local open ProgOverrider in val Integer      = DSeq.hd typeBig end *}



  (* progDiamond examples *)

constdefs
  --"Diamond class-name DAG"

  classDiamondBottom :: "cdecl"
  "classDiamondBottom == (''Bottom'', [Repeats ''Left'', Repeats ''Right''],[(''x'',Integer)],
    [(''g'', [],Integer, [],Var this \<bullet> ''x'' {[''Bottom'']} \<guillemotleft>Add\<guillemotright> Val (Intg 5))])" 

  classDiamondLeft :: "cdecl"
  "classDiamondLeft == (''Left'', [Repeats ''TopRep'',Shares ''TopSh''],[],[])"

  classDiamondRight :: "cdecl"
  "classDiamondRight == (''Right'', [Repeats ''TopRep'',Shares ''TopSh''],[],
    [(''f'', [Integer], Boolean,[''i''], Var ''i'' \<guillemotleft>Eq\<guillemotright> Val (Intg 7))])"

  classDiamondTopRep :: "cdecl"
  "classDiamondTopRep == (''TopRep'', [], [(''x'',Integer)],
    [(''g'', [],Integer, [], Var this \<bullet> ''x'' {[''TopRep'']} \<guillemotleft>Add\<guillemotright> Val (Intg 10))])"

  classDiamondTopSh :: "cdecl"
  "classDiamondTopSh == (''TopSh'', [], [], 
    [(''f'', [Integer], Boolean,[''i''], Var ''i'' \<guillemotleft>Eq\<guillemotright> Val (Intg 3))])"


  progDiamond :: "cdecl list"
  "progDiamond == [classDiamondBottom, classDiamondLeft, classDiamondRight, classDiamondTopRep, classDiamondTopSh]"


code_module ProgDiamond
contains
  cast1 = "progDiamond,[''V''\<mapsto>Class ''Left''] \<turnstile> \<langle>''V'' := new ''Bottom'',
                                                      (empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
  cast2 = "progDiamond,[''V''\<mapsto>Class ''TopSh''] \<turnstile> \<langle>''V'' := new ''Bottom'',
                                                      (empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
  cast3 = "progDiamond,[''V''\<mapsto>Class ''TopRep''] \<turnstile> \<langle>''V'' := new ''Bottom'', 
                                                      (empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
  typeCast3 = "progDiamond,[''V''\<mapsto>Class ''TopRep''] \<turnstile> ''V'' := new ''Bottom'' :: _"

  fieldAss = "progDiamond,[''V''\<mapsto>Class ''Bottom''] \<turnstile> \<langle>''V'' := new ''Bottom'' ;; 
              ((Var ''V'')\<bullet>''x''{[''Bottom'']} := (Val(Intg 17))) ;; 
              ((Var ''V'')\<bullet>''x''{[''Bottom'']}),(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

  dynCastNull = "progDiamond,empty \<turnstile> \<langle>Cast ''Right'' null,(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

  dynCastViaSh = "progDiamond,[''V''\<mapsto>Class ''TopSh''] \<turnstile> 
    \<langle>''V'' := new ''Right'' ;; Cast ''Right'' (Var ''V''),(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"


  dynCastFail = "progDiamond,[''V''\<mapsto>Class ''TopRep''] \<turnstile>
    \<langle>''V'' := new ''Right'' ;; Cast ''Bottom'' (Var ''V''),(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"


  dynCastSide = "progDiamond,[''V''\<mapsto>Class ''Right''] \<turnstile>
    \<langle>''V'' := new ''Bottom'' ;; Cast ''Left'' (Var ''V''),(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

Bottom = "''Bottom''"
Left = "''Left''"
TopSh = "''TopSh''"
TopRep = "''TopRep''"



ML {* local open ProgDiamond in val Val(Ref(0,[Bottom,Left])) = 
      fst (DSeq.hd cast1) end *}
ML {* local open ProgDiamond in val Val(Ref(0,[TopSh])) = fst (DSeq.hd cast2) end *}
(* ML {* local open ProgDiamond in val Val(Ref(0,[Bottom,Left,TopRep])) =
       if DSeq.hd typeCast3 = Class TopRep then fst (DSeq.hd cast3) else error "" end *}
 error! cast3 not typeable! *)
ML {* local open ProgDiamond in val Val(Intg 17) = fst (DSeq.hd fieldAss) end *}
ML {* local open ProgDiamond in val Val Null = fst (DSeq.hd dynCastNull) end *}
ML {* local open ProgDiamond in val Val Null = fst (DSeq.hd dynCastFail) end *}
ML {* local open ProgDiamond in val Val(Ref(0,[Bottom,Left])) = 
      fst (DSeq.hd dynCastSide) end *}



  (* failing g++ example *)

constdefs
  -- "failing example"

  classD :: "cdecl"
  "classD == (''D'', [Shares ''A'', Shares ''B'', Repeats ''C''],[],[])"

  classC :: "cdecl"
  "classC == (''C'', [Shares ''A'', Shares ''B''],[],
              [(''f'',[],Integer,[],Val(Intg 42))])"

  classB :: "cdecl"
  "classB == (''B'', [],[],
              [(''f'',[],Integer,[],Val(Intg 17))])"

  classA :: "cdecl"
  "classA == (''A'', [],[],
              [(''f'',[],Integer,[],Val(Intg 13))])"

  ProgFailing :: "cdecl list"
  "ProgFailing == [classA,classB,classC,classD]"

code_module Fail
contains

  callFailGplusplus = "ProgFailing,empty \<turnstile>
    \<langle>{''V'':Class ''D''; ''V'' := new ''D'';; Var ''V''\<bullet>''f''([])},(empty,empty)\<rangle> 
                                                                       \<Rightarrow> \<langle>_,_\<rangle>"

ML {* local open Fail in val Val(Intg 42) = 
      fst (DSeq.hd callFailGplusplus) end *}

end
