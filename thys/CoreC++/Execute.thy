(*  Title:       CoreC++
    ID:          $Id: Execute.thy,v 1.5 2006-06-09 08:28:51 wasserra Exp $
    Author:      Daniel Wasserrab, Stefan Berghofer
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
*)


header {* \isaheader{Code generation for Semantics and Type Sysytem} *}

theory Execute imports BigStep WellType ExecutableSet EfficientNat begin

subsection{* General redefinitions *}

consts
  Subobjs_aux :: "prog \<Rightarrow> cname \<Rightarrow> path set"

inductive "Subobjs_aux P C"
intros
  "(C, Cs) \<in> Subobjs P \<Longrightarrow> Cs \<in> Subobjs_aux P C"

theorem Subobjs_aux: "{Cs. (C, Cs) \<in> Subobjs P} = Subobjs_aux P C"
  apply (rule subset_antisym)
   apply (rule subsetI)
   apply (simp add: split_paired_all)
   apply (erule Subobjs_aux.intros)
  apply (rule subsetI)
  apply (simp add: split_paired_all)
  apply (erule Subobjs_aux.elims)
  apply simp
  done

consts
  SubobjsR_aux :: "prog \<Rightarrow> cname \<Rightarrow> path set"

inductive "SubobjsR_aux P C"
intros
  "(C, Cs) \<in> Subobjs\<^isub>R P \<Longrightarrow> Cs \<in> SubobjsR_aux P C"

theorem SubobjsR_aux: "{Cs. (C, Cs) \<in> Subobjs\<^isub>R P} = SubobjsR_aux P C"
  apply (rule subset_antisym)
   apply (rule subsetI)
   apply (simp add: split_paired_all)
   apply (erule SubobjsR_aux.intros)
  apply (rule subsetI)
  apply (simp add: split_paired_all)
  apply (erule SubobjsR_aux.elims)
  apply simp
  done



consts app :: "('a list \<times> 'a list \<times> 'a list) set"

inductive app
intros
  "([], ys, ys) \<in> app"
  "(xs, ys, zs) \<in> app \<Longrightarrow> (x # xs, ys, x # zs) \<in> app"

theorem app_eq1: "\<And>ys zs. zs = xs @ ys \<Longrightarrow> (xs, ys, zs) \<in> app"
  apply (induct xs)
   apply simp
   apply (rule app.intros)
  apply simp
  apply (iprover intro: app.intros)
  done

theorem app_eq2: "(xs, ys, zs) \<in> app \<Longrightarrow> zs = xs @ ys"
  by (erule app.induct) simp_all

theorem app_eq: "((xs, ys, zs) \<in> app) = (zs = xs @ ys)"
  apply (rule iffI)
   apply (erule app_eq2)
  apply (erule app_eq1)
  done


consts casts_aux :: "prog \<Rightarrow> (ty \<times> val \<times> val) set"

inductive "casts_aux P"
intros
"(case T of Class C \<Rightarrow> False | _ \<Rightarrow> True) \<Longrightarrow> (T,v,v) \<in> casts_aux P"
"(Class C,Null,Null) \<in> casts_aux P"
"\<lbrakk>(last Cs, Cs') \<in> Subobjs P; last Cs' = C;
  last Cs = hd Cs'; Cs @ tl Cs' = Ds\<rbrakk> 
\<Longrightarrow> (Class C,Ref(a,Cs),Ref(a,Ds)) \<in> casts_aux P"
"\<lbrakk>(last Cs, Cs') \<in> Subobjs P; last Cs' = C; last Cs \<noteq> hd Cs'\<rbrakk>
\<Longrightarrow> (Class C,Ref(a,Cs),Ref(a,Cs')) \<in> casts_aux P"

lemma casts_aux_eq:
"(P \<turnstile> T casts v to v') = ((T,v,v') \<in> casts_aux P)"
apply (rule iffI)
 apply(induct rule:casts_to.induct)
 apply(case_tac T) apply (auto intro:casts_aux.intros)
 apply(simp add:appendPath_def path_via_def) apply (auto intro:casts_aux.intros)
apply(induct rule:casts_aux.induct)
apply(auto intro!:casts_to.intros simp:path_via_def appendPath_def)
done

consts Casts_aux :: "prog \<Rightarrow> (ty list \<times> val list \<times> val list) set"

inductive "Casts_aux P"
intros
"([],[],[]) \<in> Casts_aux P"
"\<lbrakk>(T,v,v') \<in> casts_aux P; (Ts,vs,vs') \<in> Casts_aux P\<rbrakk>
\<Longrightarrow> (T#Ts,v#vs,v'#vs') \<in> Casts_aux P"

lemma Casts_aux_eq:
"(P \<turnstile> Ts Casts vs to vs') = ((Ts,vs,vs') \<in> Casts_aux P)"
apply(rule iffI)
 apply(induct rule:Casts_to.induct)
  apply(rule Casts_aux.intros)
 apply(fastsimp intro:Casts_aux.intros simp:casts_aux_eq)
apply(induct rule:Casts_aux.induct)
 apply(rule Casts_Nil)
apply(fastsimp intro:Casts_Cons simp:casts_aux_eq)
done



text{* Redefine map Val vs *}

consts map_val :: "(expr list \<times> val list) set"

inductive map_val
intros
  Nil: "([], []) \<in> map_val"
  Cons: "(xs, ys) \<in> map_val \<Longrightarrow> (Val y # xs, y # ys) \<in> map_val"

consts map_val2 :: "(expr list \<times> val list \<times> expr list) set"

inductive map_val2
intros
  Nil: "([], [], []) \<in> map_val2"
  Cons: "(xs, ys, zs) \<in> map_val2 \<Longrightarrow> (Val y # xs, y # ys, zs) \<in> map_val2"
  Throw: "(throw e # xs, [], throw e # xs) \<in> map_val2"

theorem map_val_conv: "(xs = map Val ys) = ((xs, ys) \<in> map_val)"
(*<*)
proof -
  have "\<And>ys. xs = map Val ys \<Longrightarrow> (xs, ys) \<in> map_val"
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
  moreover have "(xs, ys) \<in> map_val \<Longrightarrow> xs = map Val ys"
    by (erule map_val.induct) simp+
  ultimately show ?thesis ..
qed
(*>*)

theorem map_val2_conv:
 "(xs = map Val ys @ throw e # zs) = ((xs, ys, throw e # zs) \<in> map_val2)"
(*<*)
proof -
  have "\<And>ys. xs = map Val ys @ throw e # zs \<Longrightarrow> (xs, ys, throw e # zs) \<in> map_val2"
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
  moreover have "(xs, ys, throw e # zs) \<in> map_val2 \<Longrightarrow> xs = map Val ys @ throw e # zs"
    by (erule map_val2.induct) simp+
  ultimately show ?thesis ..
qed
(*>*)

text {* Redefine MethodDefs and FieldDecls *}

lemma [code ind]:
  "(C,Cs) \<in> Subobjs P \<Longrightarrow> class P (last Cs) = \<lfloor>(Bs,fs,ms)\<rfloor> \<Longrightarrow> map_of ms M =  \<lfloor>mthd\<rfloor> \<Longrightarrow>
   (Cs, mthd) \<in> MethodDefs P C M"
 by (simp add: MethodDefs_def)

lemma [code ind]:
  "(C,Cs) \<in> Subobjs P \<Longrightarrow> class P (last Cs) = \<lfloor>(Bs,fs,ms)\<rfloor> \<Longrightarrow> map_of fs F =  \<lfloor>T\<rfloor> \<Longrightarrow>
   (Cs, T) \<in> FieldDecls P C F"
 by (simp add: FieldDecls_def)



subsection {* Rewriting lemmas for Semantic rules *}

text {* Cast *}

lemma StaticUpCast_new1:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>;
    (last Cs, Cs') \<in> Subobjs P; last Cs' = C;
    last Cs = hd Cs'; Cs @ tl Cs' = Ds\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Ds),(h,l)\<rangle>"
apply(rule StaticUpCast)
  apply assumption
 apply(fastsimp simp:path_via_def)
apply(simp add:appendPath_def)
done

lemma StaticUpCast_new2:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>;
    (last Cs, Cs') \<in> Subobjs P; last Cs' = C;
    last Cs \<noteq> hd Cs'\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),(h,l)\<rangle>"
apply(rule StaticUpCast)
  apply assumption
 apply(fastsimp simp:path_via_def)
apply(simp add:appendPath_def)
done

lemma StaticDownCast_new: 
  "\<lbrakk>P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Ds),s\<^isub>1\<rangle>; (Cs, [C], Ds') \<in> app; (Ds',Cs',Ds) \<in> app; 
    is_class P C; C \<notin> set Cs'\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref(a,Cs@[C]),s\<^isub>1\<rangle>"
apply (rule StaticDownCast)
apply (simp add: app_eq)
apply assumption+
done

lemma StaticCastFail_new:
"\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle>\<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>; 
  \<forall>Cs'\<in>Subobjs_aux P (last Cs). last Cs' = C \<longrightarrow> 
       (\<exists>Cs''\<in>Subobjs_aux P (last Cs). last Cs'' = C \<and> Cs' \<noteq> Cs'');
  C \<notin> set Cs \<or> \<not> distinct Cs \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW ClassCast,(h,l)\<rangle>"
by (fastsimp intro:StaticCastFail simp:path_unique_def Subobjs_aux [symmetric])

lemma StaticUpDynCast_new1:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>;
    (last Cs, Cs') \<in> Subobjs P; last Cs' = C;
    last Cs = hd Cs'; Cs @ tl Cs' = Ds\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Ds),(h,l)\<rangle>"
apply(rule StaticUpDynCast)
  apply assumption
 apply(fastsimp simp:path_via_def)
apply(simp add:appendPath_def)
done

lemma StaticUpDynCast_new2:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>;
    (last Cs, Cs') \<in> Subobjs P; last Cs' = C;
    last Cs \<noteq> hd Cs'\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),(h,l)\<rangle>"
apply(rule StaticUpDynCast)
  apply assumption
 apply(fastsimp simp:path_via_def)
apply(simp add:appendPath_def)
done

lemma StaticDownDynCast_new: 
  "\<lbrakk>P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Ds),s\<^isub>1\<rangle>; (Cs, [C], Ds') \<in> app; (Ds',Cs',Ds) \<in> app; 
    is_class P C; C \<notin> set Cs'\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref(a,Cs@[C]),s\<^isub>1\<rangle>"
apply (rule StaticDownDynCast)
apply (simp add: app_eq)
apply assumption+
done

lemma DynCast_new:
"\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>; h a = Some(D,S);
   (D, Cs') \<in> Subobjs P; last Cs' = C;
    \<forall>Cs''\<in>Subobjs_aux P D. last Cs'' = C \<longrightarrow> Cs' = Cs''\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),(h,l)\<rangle>"
apply(rule DynCast)
apply(auto simp add:path_via_def path_unique_def)
done

lemma DynCastFail_new:
"\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle>\<Rightarrow> \<langle>ref (a,Cs),(h,l)\<rangle>; h a = Some(D,S);
  \<forall>Cs'\<in>Subobjs_aux P D. last Cs' = C \<longrightarrow> 
       (\<exists>Cs''\<in>Subobjs_aux P D. last Cs'' = C \<and> Cs' \<noteq> Cs'');
  \<forall>Ds\<in>Subobjs_aux P (last Cs). last Ds = C \<longrightarrow> 
       (\<exists>Cs''\<in>Subobjs_aux P (last Cs). last Cs'' = C \<and> Ds \<noteq> Cs'');
  C \<notin> set Cs \<or> \<not> distinct Cs \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,(h,l)\<rangle>"
apply(rule DynCastFail)
    apply assumption
   apply assumption
  apply (fastsimp simp:path_unique_def Subobjs_aux [symmetric])
 apply (fastsimp simp:path_unique_def Subobjs_aux [symmetric])
apply assumption
done


text {* Assignment *}

lemma LAss_new:
  "\<lbrakk>P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,(h, l)\<rangle>; E V = \<lfloor>T\<rfloor>;
    (T,v,v') \<in> casts_aux P; l' = l(V \<mapsto> v')\<rbrakk>
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

lemma [code ind]:
  "(C,Cs) \<in> Subobjs P \<Longrightarrow> class P (last Cs) = \<lfloor>(Bs,fs,ms)\<rfloor> \<Longrightarrow> map_of fs F =  \<lfloor>T\<rfloor> \<Longrightarrow>
   (Cs, T) \<in> FieldDecls P C F"
 by (simp add: FieldDecls_def)

lemma FAss_new1:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^isub>1,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),s\<^isub>1\<rangle>; P,E \<turnstile> \<langle>e\<^isub>2,s\<^isub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^isub>2,l\<^isub>2)\<rangle>;
     h\<^isub>2 a = Some(D,S); P \<turnstile> (last Cs') has least F:T via Cs; 
     (T,v,v') \<in> casts_aux P; last Cs' = hd Cs; Cs' @ tl Cs = Ds; 
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
     (T,v,v') \<in> casts_aux P; last Cs' \<noteq> hd Cs; (Cs,fs) \<in> S; fs' = fs(F\<mapsto>v'); 
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
     (evs, vs, throw ex # es') : map_val2 \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>M(es),s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^isub>2\<rangle>"
apply(rule eval_evals.CallParamsThrow, assumption+)
apply(simp add: map_val2_conv[symmetric])
done

lemma CallNull_new:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle>;  P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,s\<^isub>2\<rangle>; (evs,vs) : map_val \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>2\<rangle>"
apply(rule CallNull, assumption+)
apply(simp add: map_val_conv[symmetric])
done

lemma [code ind]:
  "(C,Cs) \<in> Subobjs P \<Longrightarrow> class P (last Cs) = \<lfloor>(Bs,fs,ms)\<rfloor> \<Longrightarrow> map_of ms M =  \<lfloor>mthd\<rfloor> \<Longrightarrow>
   (Cs, mthd) \<in> MethodDefs P C M"
 by (simp add: MethodDefs_def)

lemma Call_new:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^isub>1\<rangle>;  P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^isub>2,l\<^isub>2)\<rangle>;
     (evs,vs) : map_val; h\<^isub>2 a = Some(C,S); 
     P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds;
     P \<turnstile> C has least M = (Ts,T,pns,body) via Cs'; length vs = length pns; 
     (Ts,vs,vs') \<in> Casts_aux P; l\<^isub>2' = [this\<mapsto>Ref (a,Cs'), pns[\<mapsto>]vs'];
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


lemma [code ind]:
  "(Cs,mthd) \<in> MethodDefs P C M \<Longrightarrow> 
   \<forall>(Cs',mthd')\<in> MethodDefs P C M. P,C \<turnstile> Cs' \<sqsubseteq> Cs \<longrightarrow> Cs' = Cs \<Longrightarrow>
   (Cs,mthd) \<in> MinimalMethodDefs P C M"
by(simp add:MinimalMethodDefs_def)

lemma Overrider1:
  "P \<turnstile> (ldc R) has least M = mthd' via Cs' \<Longrightarrow> 
   (Cs,mthd) \<in> MinimalMethodDefs P (mdc R) M \<Longrightarrow>
   last (snd R) = hd Cs' \<Longrightarrow> P,mdc R \<turnstile> Cs \<sqsubseteq> (snd R)@tl Cs' \<Longrightarrow>
   (Cs,mthd) \<in> OverriderMethodDefs P R M"
apply(simp add:OverriderMethodDefs_def appendPath_def)
apply(rule_tac x="Cs'" in exI)
apply clarsimp
apply(cases mthd')
apply blast
done

lemma Overrider2:
  "P \<turnstile> (ldc R) has least M = mthd' via Cs' \<Longrightarrow> 
   (Cs,mthd) \<in> MinimalMethodDefs P (mdc R) M \<Longrightarrow>
   last (snd R) \<noteq> hd Cs' \<Longrightarrow> P,mdc R \<turnstile> Cs \<sqsubseteq> Cs' \<Longrightarrow>
   (Cs,mthd) \<in> OverriderMethodDefs P R M"
apply(simp add:OverriderMethodDefs_def appendPath_def)
apply(rule_tac x="Cs'" in exI) 
apply clarsimp
apply(cases mthd')
apply blast
done


consts ambiguous_aux :: "prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> path \<Rightarrow> Product_Type.unit set"
inductive "ambiguous_aux P C M Cs'"
intros
  "(Cs'',mdecl) \<in> MethodDefs P C M \<Longrightarrow> \<not> P,C \<turnstile> Cs' \<sqsubseteq> Cs'' 
  \<Longrightarrow> () \<in> ambiguous_aux P C M Cs'"

lemma ambiguous: "(\<not> P \<turnstile> C has least M = mthd via Cs') = 
  ((Cs',mthd) \<in> MethodDefs P C M \<longrightarrow> () \<in> ambiguous_aux P C M Cs')"
apply (auto simp:LeastMethodDef_def)
 apply (rule ambiguous_aux.intros) 
  apply (rotate_tac 1) apply simp_all
apply (erule ambiguous_aux.elims)
apply auto
done

lemma CallOverrider_new1:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^isub>1\<rangle>;  P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^isub>2,l\<^isub>2)\<rangle>;
     (evs,vs) : map_val; h\<^isub>2 a = Some(C,S);
     P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds;
     \<forall>(Cs', mthd')\<in>MethodDefs P (last Cs) M. P,last Cs \<turnstile> Ds \<sqsubseteq> Cs';
     \<forall>(Cs', mthd)\<in>MethodDefs P C M. () \<in> ambiguous_aux P C M Cs';
     last Cs = hd Ds; P \<turnstile> (C,Cs@tl Ds) has overrider M = (Ts,T,pns,body) via Cs';
     length vs = length pns; (Ts,vs,vs') \<in> Casts_aux P; 
     l\<^isub>2' = [this\<mapsto>Ref (a,Cs'), pns[\<mapsto>]vs']; 
     new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body   | _  \<Rightarrow> body);
     P,E(this\<mapsto>Class(last Cs'), pns[\<mapsto>]Ts) \<turnstile> \<langle>new_body,(h\<^isub>2,l\<^isub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>2)\<rangle>"
apply(rule Call,assumption+)
apply(simp add: map_val_conv[symmetric])
apply assumption+
apply(rule dyn_ambiguous)
apply(simp add:ambiguous,fastsimp)
apply(simp add:appendPath_def)
apply assumption+
apply(simp add:Casts_aux_eq)
apply assumption+
done

lemma CallOverrider_new2:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^isub>1\<rangle>;  P,E \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^isub>2,l\<^isub>2)\<rangle>;
     (evs,vs) : map_val; h\<^isub>2 a = Some(C,S);
     P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds;
     \<forall>(Cs', mthd')\<in>MethodDefs P (last Cs) M. P,last Cs \<turnstile> Ds \<sqsubseteq> Cs';
     \<forall>(Cs', mthd)\<in>MethodDefs P C M. () \<in> ambiguous_aux P C M Cs';
     last Cs \<noteq> hd Ds; P \<turnstile> (C,Ds) has overrider M = (Ts,T,pns,body) via Cs';
     length vs = length pns; (Ts,vs,vs') \<in> Casts_aux P;
     l\<^isub>2' = [this\<mapsto>Ref (a,Cs'), pns[\<mapsto>]vs']; 
     new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body   | _  \<Rightarrow> body);
     P,E(this\<mapsto>Class(last Cs'), pns[\<mapsto>]Ts) \<turnstile> \<langle>new_body,(h\<^isub>2,l\<^isub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>2)\<rangle>"
apply(rule Call,assumption+)
apply(simp add: map_val_conv[symmetric])
apply assumption+
apply(rule dyn_ambiguous)
apply(simp add:ambiguous,fastsimp)
apply(simp add:appendPath_def)
apply assumption+
apply(simp add:Casts_aux_eq)
apply assumption+
done


subsection{* Rewriting lemmas for Type rules *}


lemma WTStaticCast_new1:
  "\<lbrakk> P,E \<turnstile> e :: Class D; is_class P C;
   (D, Cs') \<in> Subobjs P; last Cs' = C;
    \<forall>Cs''\<in>Subobjs_aux P D. last Cs'' = C \<longrightarrow> Cs' = Cs''\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<lparr>C\<rparr>e :: Class C"
  by (rule WTStaticCast,auto simp add: path_unique_def Subobjs_aux [symmetric])


lemma WTStaticCast_new2:
"\<lbrakk>P,E \<turnstile> e :: Class D; is_class P C;
  \<forall>Cs \<in> Subobjs_aux P C. last Cs = D \<longrightarrow> (C,Cs) \<in> Subobjs\<^isub>R P \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<lparr>C\<rparr>e :: Class C"
  by (rule WTStaticCast,auto simp:path_via_def Subobjs_aux [symmetric])

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

lemma [code ind]:
  "\<lbrakk>(C,Cs') \<in> Subobjs P; last Cs' = D;
    \<forall>Cs''\<in>Subobjs_aux P C. last Cs'' = D \<longrightarrow> Cs' = Cs'' \<rbrakk> 
\<Longrightarrow> P \<turnstile> Class C \<le> Class D"
by(rule widen_subcls,auto simp:path_unique_def Subobjs_aux [symmetric])

lemmas [code ind] = widen_refl widen_null



subsection{* Code generation *}

lemmas [code ind] = 
 Overrider1[simplified LeastMethodDef_def, OF conjI]
 Overrider2[simplified LeastMethodDef_def, OF conjI]

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
 FAss_new1[simplified LeastFieldDecl_def, OF _ _ _ conjI]
 FAss_new2[simplified LeastFieldDecl_def, OF _ _ _ conjI]
 eval_evals.FAssNull eval_evals.FAssThrow1 eval_evals.FAssThrow2
 eval_evals.CallObjThrow CallNull_new CallParamsThrow_new 
 Call_new[simplified LeastMethodDef_def, OF _ _ _ _ conjI conjI]
 CallOverrider_new1[simplified FinalOverriderMethodDef_def LeastMethodDef_def,
                    OF _ _ _ _ conjI _ _ _ conjI]
 CallOverrider_new2[simplified FinalOverriderMethodDef_def LeastMethodDef_def,
                    OF _ _ _ _ conjI _ _ _ conjI]
 eval_evals.Block eval_evals.Seq eval_evals.SeqThrow
 eval_evals.CondT eval_evals.CondF eval_evals.CondThrow
 eval_evals.WhileF eval_evals.WhileT 
 eval_evals.WhileCondThrow eval_evals.WhileBodyThrow
 eval_evals.Throw eval_evals.ThrowNull eval_evals.ThrowThrow
 eval_evals.Nil eval_evals.Cons eval_evals.ConsThrow

 (* Type rules *)
 WT_WTs.WTNew WT_WTs.WTDynCast WTStaticCast_new1 WTStaticCast_new2
 WT_WTs.WTVal WT_WTs.WTVar WTBinOp1 WTBinOp2 WT_WTs.WTLAss
 WT_WTs.WTFAcc[unfolded LeastFieldDecl_def, OF _ conjI]
 WT_WTs.WTFAss[unfolded LeastFieldDecl_def, OF _ conjI]
 WT_WTs.WTCall[unfolded LeastMethodDef_def, OF _ conjI,simplified fun_of_def]
 WT_WTs.WTBlock WT_WTs.WTSeq WT_WTs.WTCond WT_WTs.WTWhile WT_WTs.WTThrow
 WT_WTs.WTNil WT_WTs.WTCons



lemmas [code ind] = rtrancl_refl converse_rtrancl_into_rtrancl

(* A hack to make set operations work on sets with function types *)

consts_code
  "insert" :: "('a \<times> ('b \<Rightarrow> 'c)) \<Rightarrow> ('a \<times> ('b \<Rightarrow> 'c)) set \<Rightarrow> ('a \<times> ('b \<Rightarrow> 'c)) set"
    ("insert (op = o pairself fst)")
  "minus" :: "('a \<times> ('b \<Rightarrow> 'c)) set \<Rightarrow> ('a \<times> ('b \<Rightarrow> 'c)) set \<Rightarrow> ('a \<times> ('b \<Rightarrow> 'c)) set"
    ("(gen'_rems (op = o pairself fst)/ (_,/ _))")
  "op Un" :: "('a * ('b => 'c)) set => ('a * ('b => 'c)) set => ('a * ('b => 'c)) set"
    ("(gen'_union (op = o pairself fst)/ (_,/ _))")

consts_code
  "card"   ("\<module>card")
attach {*
fun card S = length (distinct op = S);
*}

ML {*
fun new_addr z s alloc some hp =
  let fun nr i = if alloc (hp i) then some i else nr (s i);
  in nr z end;
*}

consts_code
  "new_Addr"
   ("new'_addr {* 0::nat *} {* Suc *}
               {* %x. case x of None => True | Some y => False *} {* Some *}")

  "arbitrary" ("(raise ERROR \"arbitrary\")")


text{* Definition of program examples *}



declare ListMem_iff [symmetric, THEN eq_reflection, code unfold]


text{* \<dots>and off we go *}

  (* Examples with no prog needed *)
code_module NoProg
contains
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

ML {* if fst (Seq.hd NoProg.test1) = NoProg.Val (NoProg.Intg 5) then () 
      else error "" *}
ML {* if fst (Seq.hd NoProg.test2) = NoProg.Val (NoProg.Intg 11) then ()  
      else error "" *}
ML {* if fst (Seq.hd NoProg.test3) = NoProg.Val (NoProg.Intg 83) then () 
      else error "" *}
ML {* if let val (_,(h,l)) = Seq.hd NoProg.test4 in l NoProg.V end = 
      NoProg.Some (NoProg.Intg 6) then () else error "" *}
ML {* if let val (_,(h,l)) = Seq.hd NoProg.testWhile in l NoProg.mult end =
      NoProg.Some (NoProg.Intg 12) then () else error "" *}
ML {* if fst (Seq.hd NoProg.testIf) = NoProg.Val (NoProg.Intg 30) then () 
      else error "" *} 



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


ML {* if fst (Seq.hd ProgOverrider.dynCastSide) = ProgOverrider.Val(
      ProgOverrider.Ref(0,[ProgOverrider.Bottom,ProgOverrider.Left])) then () 
      else error "" *}
ML {* if fst (Seq.hd ProgOverrider.dynCastViaSh) = ProgOverrider.Val(
      ProgOverrider.Ref(0,[ProgOverrider.Right])) then () else error "" *}
ML {* if fst (Seq.hd ProgOverrider.block) = ProgOverrider.Val(ProgOverrider.Intg 42)  
      then () else error "" *}
ML {* if fst (Seq.hd ProgOverrider.call) = ProgOverrider.Val(ProgOverrider.Intg 12) 
      then () else error "" *}
ML {* if fst (Seq.hd ProgOverrider.callClass) = ProgOverrider.Val(
      ProgOverrider.Ref(1,[ProgOverrider.Left,ProgOverrider.Top])) then () 
      else error "" *}
ML {* if fst (Seq.hd ProgOverrider.fieldAss) = ProgOverrider.Val(
      ProgOverrider.Intg 42) then () else error "" *}

(* Typing rules *)
ML {* if Seq.hd ProgOverrider.typeNew = ProgOverrider.Class ProgOverrider.Bottom 
      then () else error "" *}
ML {* if Seq.hd ProgOverrider.typeDynCast = ProgOverrider.Class ProgOverrider.Left
      then () else error "" *}
ML {* if Seq.hd ProgOverrider.typeStaticCast = ProgOverrider.Class ProgOverrider.Left
      then () else error "" *}
ML {* if Seq.hd ProgOverrider.typeVal = ProgOverrider.Integer then () else error "" *}
ML {* if Seq.hd ProgOverrider.typeVar = ProgOverrider.Integer then () else error "" *}
ML {* if Seq.hd ProgOverrider.typeBinOp = ProgOverrider.Boolean then () 
      else error "" *}
ML {* if Seq.hd ProgOverrider.typeLAss = ProgOverrider.Class ProgOverrider.Top
      then () else error "" *}
ML {* if Seq.hd ProgOverrider.typeFAcc = ProgOverrider.Integer then () 
      else error "" *}
ML {* if Seq.hd ProgOverrider.typeFAss = ProgOverrider.Integer then () 
      else error "" *}
ML {* if Seq.hd ProgOverrider.typeCall = ProgOverrider.Class ProgOverrider.Top
      then () else error "" *}
ML {* if Seq.hd ProgOverrider.typeBlock = ProgOverrider.Class ProgOverrider.Top
      then () else error "" *}
ML {* if Seq.hd ProgOverrider.typeCond = ProgOverrider.Integer then () 
      else error "" *}
ML {* if Seq.hd ProgOverrider.typeThrow = ProgOverrider.Void then () 
      else error "" *}
ML {* if Seq.hd ProgOverrider.typeBig = ProgOverrider.Integer then () else error "" *}



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

ML {* if fst (Seq.hd ProgDiamond.cast1) = ProgDiamond.Val(
      ProgDiamond.Ref(0,[ProgDiamond.Bottom,ProgDiamond.Left])) then () 
      else error "" *}
ML {* if fst (Seq.hd ProgDiamond.cast2) = ProgDiamond.Val(
      ProgDiamond.Ref(0,[ProgDiamond.TopSh])) then () else error "" *}
(*ML {* if Seq.hd ProgDiamond.typeCast3 = ProgDiamond.Class ProgDiamond.TopRep
      then (if fst (Seq.hd ProgDiamond.cast3) =  ProgDiamond.Val(
            ProgDiamond.Ref(0,
              [ProgDiamond.Bottom,ProgDiamond.Left,ProgDiamond.TopRep])) then ()
            else error "") else error "" *} *)
ML {* if fst (Seq.hd ProgDiamond.fieldAss) = ProgDiamond.Val(ProgDiamond.Intg 17) 
      then () else error "" *}
ML {* if fst (Seq.hd ProgDiamond.dynCastNull) = ProgDiamond.Val ProgDiamond.Null
      then () else error "" *}
ML {* if fst (Seq.hd ProgDiamond.dynCastFail) = ProgDiamond.Val ProgDiamond.Null
      then () else error "" *}
ML {* if fst (Seq.hd ProgDiamond.dynCastSide) = ProgDiamond.Val(
      ProgDiamond.Ref(0,[ProgDiamond.Bottom,ProgDiamond.Left])) then () 
      else error "" *}



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

  progFailing :: "cdecl list"
  "progFailing == [classA,classB,classC,classD]"

code_module Fail
contains

  callFailGplusplus = "progFailing,empty \<turnstile>
    \<langle>{''V'':Class ''D''; ''V'' := new ''D'';; Var ''V''\<bullet>''f''([])},(empty,empty)\<rangle> 
                                                                       \<Rightarrow> \<langle>_,_\<rangle>"

ML {* if fst (Seq.hd Fail.callFailGplusplus) = Fail.Val(Fail.Intg 42) then () 
      else error "" *}



end
