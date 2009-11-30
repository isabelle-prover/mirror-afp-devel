(*  Title:      JinjaThread/Compiler/PCompiler.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Program Compilation} *}

theory PCompiler
imports "../Common/WellForm" "../Common/BinOp" "../Common/Conform"
begin

constdefs
  compM :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a mdecl \<Rightarrow> 'b mdecl"
  "compM f  \<equiv>  \<lambda>(M, Ts, T, m). (M, Ts, T, f m)"

  compC :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a cdecl \<Rightarrow> 'b cdecl"
  "compC f  \<equiv>  \<lambda>(C,D,Fdecls,Mdecls). (C,D,Fdecls, map (compM f) Mdecls)"

  compP :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a prog \<Rightarrow> 'b prog"
  "compP f  \<equiv>  map (compC f)"

text{* Compilation preserves the program structure.  Therfore lookup
functions either commute with compilation (like method lookup) or are
preserved by it (like the subclass relation). *}

lemma map_of_map4:
  "map_of (map (\<lambda>(x,a,b,c).(x,a,b,f c)) ts) =
  Option.map (\<lambda>(a,b,c).(a,b,f c)) \<circ> (map_of ts)"
(*<*)
apply(induct ts)
 apply simp
apply(rule ext)
apply fastsimp
done
(*>*)


lemma class_compP:
  "class P C = Some (D, fs, ms)
  \<Longrightarrow> class (compP f P) C = Some (D, fs, map (compM f) ms)"
(*<*)by(simp add:class_def compP_def compC_def map_of_map4)(*>*)


lemma class_compPD:
  "class (compP f P) C = Some (D, fs, cms)
  \<Longrightarrow> \<exists>ms. class P C = Some(D,fs,ms) \<and> cms = map (compM f) ms"
(*<*)by(clarsimp simp add:class_def compP_def compC_def map_of_map4)(*>*)


lemma [simp]: "is_class (compP f P) C = is_class P C"
(*<*)by(auto simp:is_class_def dest: class_compP class_compPD)(*>*)


lemma [simp]: "class (compP f P) C = Option.map (\<lambda>c. snd(compC f (C,c))) (class P C)"
(*<*)
apply(simp add:compP_def compC_def class_def map_of_map4)
apply(simp add:split_def)
done
(*>*)


lemma sees_methods_compP:
  "P \<turnstile> C sees_methods Mm \<Longrightarrow>
  compP f P \<turnstile> C sees_methods (Option.map (\<lambda>((Ts,T,m),D). ((Ts,T,f m),D)) \<circ> Mm)"
(*<*)
apply(erule Methods.induct)
 apply(rule sees_methods_Object)
  apply(erule class_compP)
 apply(rule ext)
 apply(simp add:compM_def map_of_map4 option_map_comp)
 apply(case_tac "map_of ms x")
  apply simp
 apply fastsimp
apply(rule sees_methods_rec)
   apply(erule class_compP)
  apply assumption
 apply assumption
apply(rule ext)
apply(simp add:map_add_def compM_def map_of_map4 option_map_comp split:option.split)
done
(*>*)


lemma sees_method_compP:
  "P \<turnstile> C sees M: Ts\<rightarrow>T = m in D \<Longrightarrow>
  compP f P \<turnstile> C sees M: Ts\<rightarrow>T = (f m) in D"
(*<*)by(fastsimp elim:sees_methods_compP simp add:Method_def)(*>*)


lemma [simp]:
  "P \<turnstile> C sees M: Ts\<rightarrow>T = m in D \<Longrightarrow>
  method (compP f P) C M = (D,Ts,T,f m)"
(*<*)
apply(drule sees_method_compP)
apply(simp add:method_def)
apply(rule the_equality)
 apply simp
apply(fastsimp dest:sees_method_fun)
done
(*>*)


lemma sees_methods_compPD:
  "\<lbrakk> cP \<turnstile> C sees_methods Mm'; cP = compP f P \<rbrakk> \<Longrightarrow>
  \<exists>Mm. P \<turnstile> C sees_methods Mm \<and>
        Mm' = (Option.map (\<lambda>((Ts,T,m),D). ((Ts,T,f m),D)) \<circ> Mm)"
(*<*)
apply(erule Methods.induct)
 apply(clarsimp simp:compC_def)
 apply(rule exI)
 apply(rule conjI, erule sees_methods_Object)
 apply(rule refl)
 apply(rule ext)
 apply(simp add:compM_def map_of_map4 option_map_comp)
 apply(case_tac "map_of b x")
  apply simp
 apply fastsimp
apply(clarsimp simp:compC_def)
apply(rule exI, rule conjI)
apply(erule (2) sees_methods_rec)
 apply(rule refl)
apply(rule ext)
apply(simp add:map_add_def compM_def map_of_map4 option_map_comp split:option.split)
done
(*>*)


lemma sees_method_compPD:
  "compP f P \<turnstile> C sees M: Ts\<rightarrow>T = fm in D \<Longrightarrow>
  \<exists>m. P \<turnstile> C sees M: Ts\<rightarrow>T = m in D \<and> f m = fm"
(*<*)
apply(simp add:Method_def)
apply clarify
apply(drule sees_methods_compPD[OF _ refl])
apply clarsimp
apply blast
done
(*>*)


lemma [simp]: "subcls1(compP f P) = subcls1 P"
by(fastsimp simp add: is_class_def compC_def intro:subcls1I order_antisym dest:subcls1D)

lemma [simp]: "is_type (compP f P) T = is_type P T"
by(induct T, auto)



lemma compP_widen[simp]:
  "(compP f P \<turnstile> T \<le> T') = (P \<turnstile> T \<le> T')"
by(induct T' arbitrary: T)(simp_all add: widen_Class widen_Array)

lemma [simp]: "(compP f P \<turnstile> Ts [\<le>] Ts') = (P \<turnstile> Ts [\<le>] Ts')"
(*<*)
apply(induct Ts)
 apply simp
apply(cases Ts')
apply(auto simp:fun_of_def)
done
(*>*)



lemma [simp]: "(compP (f::'a\<Rightarrow>'b) P \<turnstile> C has_fields FDTs) = (P \<turnstile> C has_fields FDTs)"
(*<*)
 (is "?A = ?B")
proof
  { fix cP::"'b prog" assume "cP \<turnstile> C has_fields FDTs"
    hence "cP = compP f P \<Longrightarrow> P \<turnstile> C has_fields FDTs"
    proof induct
      case has_fields_Object
      thus ?case by(fast intro:Fields.has_fields_Object dest:class_compPD)
    next
      case has_fields_rec
      thus ?case by(fast intro:Fields.has_fields_rec dest:class_compPD)
    qed
  } note lem = this
  assume ?A
  with lem show ?B by blast
next
  assume ?B
  thus ?A
  proof induct
    case has_fields_Object
    thus ?case by(fast intro:Fields.has_fields_Object class_compP)
  next
    case has_fields_rec
    thus ?case by(fast intro:Fields.has_fields_rec class_compP)
  qed
qed
(*>*)


lemma [simp]: "fields (compP f P) C = fields P C"
(*<*)by(simp add:fields_def)(*>*)


lemma [simp]: "(compP f P \<turnstile> C sees F:T in D) = (P \<turnstile> C sees F:T in D)"
(*<*)by(simp add:sees_field_def)(*>*)


lemma [simp]: "field (compP f P) F D = field P F D"
(*<*)by(simp add:field_def)(*>*)


section{*Invariance of @{term wf_prog} under compilation *}

lemma [iff]: "distinct_fst (compP f P) = distinct_fst P"
(*<*)
apply(simp add:distinct_fst_def compP_def compC_def)
apply(induct P)
apply (auto simp:image_iff)
done
(*>*)


lemma [iff]: "distinct_fst (map (compM f) ms) = distinct_fst ms"
(*<*)
apply(simp add:distinct_fst_def compM_def)
apply(induct ms)
apply (auto simp:image_iff)
done
(*>*)


lemma [iff]: "wf_syscls (compP f P) = wf_syscls P"
by(auto simp add:wf_syscls_def)(auto simp add: compP_def compC_def image_def Bex_def)

lemma [iff]: "wf_fdecl (compP f P) = wf_fdecl P"
(*<*)by(simp add:wf_fdecl_def)(*>*)


lemma set_compP:
 "((C,D,fs,ms') \<in> set(compP f P)) =
  (\<exists>ms. (C,D,fs,ms) \<in> set P \<and> ms' = map (compM f) ms)"
(*<*)by(fastsimp simp add:compP_def compC_def image_iff Bex_def)(*>*)

lemma is_external_call_compP [simp]: "is_external_call (compP f P) = is_external_call P"
by(auto simp add: expand_fun_eq elim!: is_external_call.cases intro: is_external_call.intros)

lemma red_external_compP [simp]:
  "compP f P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<longleftrightarrow> P \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
by(auto elim!: red_external.cases intro: red_external.intros)

lemma external_WT_compP [simp]:
  "compP f P \<turnstile> T\<bullet>M(vs) :: U \<longleftrightarrow> P \<turnstile> T\<bullet>M(vs) :: U"
by(auto elim!: external_WT.cases intro: external_WT.intros)


lemma wf_extCall_compP [simp]: "wf_extCall (compP f P) C M = wf_extCall P C M"
unfolding wf_extCall_def by auto

lemma wf_cdecl_compPI:
  assumes wf1_imp_wf2: 
    "\<And>C M Ts T m. \<lbrakk> wf_mdecl wf\<^isub>1 P C (M,Ts,T,m); P \<turnstile> C sees M:Ts\<rightarrow>T = m in C \<rbrakk> \<Longrightarrow> wf_mdecl wf\<^isub>2 (compP f P) C (M,Ts,T, f m)"
  and wfcP1: "\<forall>x\<in>set P. wf_cdecl wf\<^isub>1 P x"
  and xcomp: "x \<in> set (compP f P)"
  and wf: "wf_prog p P"
  shows "wf_cdecl wf\<^isub>2 (compP f P) x"
proof -
  obtain C D fs ms' where x: "x = (C, D, fs, ms')"
    by(cases x, auto)
  with xcomp obtain ms where xsrc: "(C,D,fs,ms) \<in> set P"
    and ms': "ms' = map (compM f) ms"
    by(auto simp add: set_compP)
  from xsrc wfcP1 have wf1: "wf_cdecl wf\<^isub>1 P (C,D,fs,ms)" by blast
  { fix field
    assume "field \<in> set fs"
    with wf1 have "wf_fdecl (compP f P) field" by(simp add: wf_cdecl_def) 
  }
  moreover from wf1 have "distinct_fst fs" by(simp add: wf_cdecl_def)
  moreover
  { fix m
    assume mset': "m \<in> set ms'"
    then obtain M Ts' T' body' where m: "m = (M, Ts', T', body')" by(cases m, auto)
    with mset' ms' obtain body where mf: "m = (M, Ts', T', f body)"
      and mset: "(M, Ts', T', body) \<in> set ms"
      by(clarsimp simp add: image_iff compM_def)
    moreover from mset xsrc wfcP1 have "wf_mdecl wf\<^isub>1 P C (M,Ts',T',body)"
      by(auto simp add: wf_cdecl_def)
    moreover from wf xsrc mset x have "P \<turnstile> C sees M:Ts'\<rightarrow>T' = body in C"
      by(auto intro: mdecl_visible)
    ultimately have "wf_mdecl wf\<^isub>2 (compP f P) C m"
      by(auto intro: wf1_imp_wf2) }
  moreover from wf1 have "distinct_fst ms" by(simp add: wf_cdecl_def)
  with ms' have "distinct_fst ms'" by(auto)
  moreover
  { assume CObj: "C \<noteq> Object"
    with xsrc wfcP1
    have part1: "is_class (compP f P) D" "\<not> compP f P \<turnstile> D \<preceq>\<^sup>* C"
      by(auto simp add: wf_cdecl_def)
    { fix m'
      assume mset': "m' \<in> set ms'"
      then obtain M Ts T body' where m: "m' = (M, Ts, T, body')" by(cases m', auto)
      with mset' ms' obtain body where mf: "m' = (M, Ts, T, f body)"
	and mset: "(M, Ts, T, body) \<in> set ms"
	by(clarsimp simp add: image_iff compM_def)
      from wf1 CObj
      have wfms: "\<forall>x\<in>set ms. (\<lambda>(M, Ts, T, m). wf_extCall P C M \<and> (\<forall>D' Ts' T'. (\<exists>m'. P \<turnstile> D sees M: Ts'\<rightarrow>T' = m' in D') \<longrightarrow> P \<turnstile> Ts' [\<le>] Ts \<and> P \<turnstile> T \<le> T')) x"
	by(clarsimp simp add: wf_cdecl_def)
      hence "wf_extCall P C M" using m mset by auto
      hence "wf_extCall (compP f P) C M" by(simp)
      moreover {
	fix D' Ts' T' body''
	assume "compP f P \<turnstile> D sees M: Ts'\<rightarrow>T' = body'' in D'"
	then obtain body''' where "P \<turnstile> D sees M: Ts'\<rightarrow>T' = body''' in D'"
	  by(auto dest: sees_method_compPD)
	with wfms have "compP f P \<turnstile> Ts' [\<le>] Ts" "compP f P \<turnstile> T \<le> T'" using mset
	  by(fastsimp)+ }
      ultimately have "wf_extCall (compP f P) C (fst m') \<and> 
                    (\<forall>D' Ts' T' body'. compP f P \<turnstile> D sees fst m': Ts'\<rightarrow>T' = body' in D' \<longrightarrow>
                                       compP f P \<turnstile> Ts' [\<le>] fst (snd m') \<and>
                                       compP f P \<turnstile> fst (snd (snd m')) \<le> T')"
	using m by(clarsimp) }
    note this part1 }
  moreover
  { assume CObj: "C = Object"
    with wf1 ms' have "fs = []" "ms' = []"
      by(auto simp add: wf_cdecl_def) }
  moreover
  { assume "C = Thread"
    with wf1 ms' have "\<exists>m. (run, [], Void, m) \<in> set ms'"
      by(fastsimp simp add: wf_cdecl_def image_iff compM_def) }
  ultimately show ?thesis unfolding x wf_cdecl_def split_beta fst_conv snd_conv Ball_def
    by(blast)
qed


lemma wf_prog_compPI:
assumes lift: 
  "\<And>C M Ts T m. 
    \<lbrakk> P \<turnstile> C sees M:Ts\<rightarrow>T = m in C; wf_mdecl wf\<^isub>1 P C (M,Ts,T,m) \<rbrakk>
    \<Longrightarrow> wf_mdecl wf\<^isub>2 (compP f P) C (M,Ts,T, f m)"
and wf: "wf_prog wf\<^isub>1 P"
shows "wf_prog wf\<^isub>2 (compP f P)"
(*<*)
using wf
by (simp add:wf_prog_def) (blast intro:wf_cdecl_compPI lift wf)
(*>*)

lemma WT_binop_compP [simp]: "compP f P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T \<longleftrightarrow> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T"
by(fastsimp)

lemma WTrt_binop_compP [simp]: "compP f P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T \<longleftrightarrow> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T"
by(fastsimp)

lemma is_class_compP [simp]:
  "is_class (compP f P) = is_class P"
by(simp add: is_class_def expand_fun_eq)

lemma has_field_compP [simp]:
  "compP f P \<turnstile> C has F:T in D \<longleftrightarrow> P \<turnstile> C has F:T in D"
by(auto simp add: has_field_def)

lemma conf_compP [simp]:
  "compP f P,h \<turnstile> v :\<le> T \<longleftrightarrow> P,h \<turnstile> v :\<le> T"
by(simp add: conf_def)

lemma oconf_compP [simp]:
  "oconf (compP f P) h obj = oconf P h obj"
by(auto simp add: oconf_def split: heapobj.split)

lemma hconf_compP [simp]:
  "compP f P \<turnstile> h \<surd> \<longleftrightarrow> P \<turnstile> h \<surd>"
by(auto simp add: hconf_def)

lemma compP_conf: "conf (compP f P) = conf P"
by(auto simp add: conf_def intro!: ext)

lemma compP_confs: "compP f P,h \<turnstile> vs [:\<le>] Ts \<longleftrightarrow> P,h \<turnstile> vs [:\<le>] Ts"
by(simp add: compP_conf)

lemma compP_has_method: "compP f P \<turnstile> C has M \<longleftrightarrow> P \<turnstile> C has M"
unfolding has_method_def
by(fastsimp dest: sees_method_compPD intro: sees_method_compP)

end
