(*  Title:      JinjaDCI/Compiler/PCompiler.thy

    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   TUM 2003, UIUC 2019-20

    Based on the Jinja theory Common/PCompiler.thy by Tobias Nipkow
*)

section \<open> Program Compilation \<close>

theory PCompiler
imports "../Common/WellForm"
begin

definition compM :: "(staticb \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a mdecl \<Rightarrow> 'b mdecl"
where
  "compM f  \<equiv>  \<lambda>(M, b, Ts, T, m). (M, b, Ts, T, f b m)"

definition compC :: "(staticb \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a cdecl \<Rightarrow> 'b cdecl"
where
  "compC f  \<equiv>  \<lambda>(C,D,Fdecls,Mdecls). (C,D,Fdecls, map (compM f) Mdecls)"

definition compP :: "(staticb \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a prog \<Rightarrow> 'b prog"
where
  "compP f  \<equiv>  map (compC f)"

text\<open> Compilation preserves the program structure.  Therefore lookup
functions either commute with compilation (like method lookup) or are
preserved by it (like the subclass relation). \<close>

lemma map_of_map4:
  "map_of (map (\<lambda>(x,a,b,c).(x,a,b,f c)) ts) =
  map_option (\<lambda>(a,b,c).(a,b,f c)) \<circ> (map_of ts)"
(*<*)
proof(induct ts)
  case Nil then show ?case by simp
qed fastforce
(*>*)

lemma map_of_map245:
  "map_of (map (\<lambda>(x,a,b,c,d).(x,a,b,c,f a c d)) ts) =
  map_option (\<lambda>(a,b,c,d).(a,b,c,f a c d)) \<circ> (map_of ts)"
(*<*)
proof(induct ts)
  case Nil then show ?case by simp
qed fastforce
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


lemma [simp]: "class (compP f P) C = map_option (\<lambda>c. snd(compC f (C,c))) (class P C)"
(*<*)
by(simp add:compP_def compC_def class_def map_of_map4)
  (simp add:split_def)
(*>*)


lemma sees_methods_compP:
  "P \<turnstile> C sees_methods Mm \<Longrightarrow>
  compP f P \<turnstile> C sees_methods (map_option (\<lambda>((b,Ts,T,m),D). ((b,Ts,T,f b m),D)) \<circ> Mm)"
(*<*)(is "?P \<Longrightarrow> compP f P \<turnstile> C sees_methods (?map Mm)")
proof(induct rule: Methods.induct)
  case Object: (sees_methods_Object D fs ms Mm)
  let ?Mm1 = "\<lambda>x. map_option ((\<lambda>m. (m, Object)) \<circ> (\<lambda>(b, Ts, T, m). (b, Ts, T, f b m))) (map_of ms x)"
  let ?Mm2 = "\<lambda>x. map_option (case_prod (\<lambda>(b, Ts, T, m).
                   Pair (b, Ts, T, f b m)) \<circ> (\<lambda>m. (m, Object))) (map_of ms x)"
  have Mm_eq: "\<And>x. ?Mm1 x = ?Mm2 x"
  proof -
    fix x show "?Mm1 x = ?Mm2 x"
    proof(cases "map_of ms x")
      case None then show ?thesis by simp
    qed fastforce
  qed

  have Mm: "Mm = map_option (\<lambda>m. (m, Object)) \<circ> map_of ms" by fact
  let ?Mm = "map_option (\<lambda>m. (m, Object)) \<circ> map_of (map (compM f) ms)"
  let ?Mm' = "?map Mm"
  have "?Mm' = ?Mm"
    by(rule ext) (simp add:Mm Mm_eq compM_def map_of_map245 option.map_comp)
  then show ?case by(rule sees_methods_Object[OF class_compP[OF Object(1)]])
next
  case rec: (sees_methods_rec C D fs ms Mm Mm')
  have Mm': "Mm' = Mm ++ (map_option (\<lambda>m. (m, C)) \<circ> map_of ms)" by fact
  let ?Mm' = "?map Mm'"
  let ?Mm'' = "(?map Mm) ++ (map_option (\<lambda>m. (m, C)) \<circ> map_of (map (compM f) ms))"
  have "?Mm' = ?Mm''"
    by(rule ext) (simp add:Mm' map_add_def compM_def map_of_map245)
  moreover have "compP f P \<turnstile> C sees_methods ?Mm''"
    using sees_methods_rec[OF class_compP[OF rec(1)] rec(2,4)] by fast
  ultimately show "compP f P \<turnstile> C sees_methods ?Mm'" by simp
qed
(*>*)


lemma sees_method_compP:
  "P \<turnstile> C sees M,b: Ts\<rightarrow>T = m in D \<Longrightarrow>
  compP f P \<turnstile> C sees M,b: Ts\<rightarrow>T = (f b m) in D"
(*<*)by(fastforce elim:sees_methods_compP simp add:Method_def)(*>*)


lemma [simp]:
  "P \<turnstile> C sees M,b: Ts\<rightarrow>T = m in D \<Longrightarrow>
  method (compP f P) C M = (D,b,Ts,T,f b m)"
(*<*)
proof -
  let ?P = "\<lambda>(D, b, Ts, T, m). compP f P \<turnstile> C sees M, b :  Ts\<rightarrow>T = m in D"
  let ?a = "(D, b, Ts, T, f b m)"
  assume cM: "P \<turnstile> C sees M,b: Ts\<rightarrow>T = m in D"
  have compP_cM: "?P ?a" using sees_method_compP[OF cM] by simp
  moreover {
    fix x assume "?P x" then have "x = ?a"
      using compP_cM by(fastforce dest:sees_method_fun)
  }
  ultimately have "(THE x. ?P x) = ?a" by(rule the_equality)
  then show ?thesis by(simp add:method_def)
qed
(*>*)


lemma sees_methods_compPD:
  "\<lbrakk> cP \<turnstile> C sees_methods Mm'; cP = compP f P \<rbrakk> \<Longrightarrow>
  \<exists>Mm. P \<turnstile> C sees_methods Mm \<and>
        Mm' = (map_option (\<lambda>((b,Ts,T,m),D). ((b,Ts,T,f b m),D)) \<circ> Mm)"
(*<*)(is "\<lbrakk> ?P; ?Q \<rbrakk> \<Longrightarrow> \<exists>Mm. P \<turnstile> C sees_methods Mm \<and> Mm' = (?map Mm)")
proof(induct rule: Methods.induct)
  case Object: (sees_methods_Object D fs ms Mm)
  then obtain ms' where P_Obj: "class P Object = \<lfloor>(D, fs, ms')\<rfloor>"
    and ms: "ms = map (compM f) ms'" by(clarsimp simp:compC_def)

  let ?Mm1 = "\<lambda>x. map_option ((\<lambda>m. (m, Object)) \<circ> (\<lambda>(b, Ts, T, m). (b, Ts, T, f b m))) (map_of ms' x)"
  let ?Mm2 = "\<lambda>x. map_option (case_prod (\<lambda>(b, Ts, T, m). Pair (b, Ts, T, f b m)) \<circ> (\<lambda>m. (m, Object)))
          (map_of ms' x)"
  have Mm_eq: "\<And>x. ?Mm1 x = ?Mm2 x"
  proof -
    fix x show "?Mm1 x = ?Mm2 x"
    proof(cases "map_of ms' x")
      case None then show ?thesis by simp
    qed fastforce
  qed

  let ?Mm = "map_option (\<lambda>m. (m,Object)) \<circ> map_of ms'"
  let ?Mm' = "?map ?Mm"
  have Mm: "Mm = map_option (\<lambda>m. (m, Object)) \<circ> map_of ms" by fact
  have "P \<turnstile> Object sees_methods ?Mm"
    using sees_methods_Object[OF P_Obj] by simp
  moreover have "Mm = ?Mm'"
    by(rule ext) (simp add:Mm_eq Mm ms compM_def map_of_map245 option.map_comp)
  ultimately show ?case by fast
next
  case rec: (sees_methods_rec C D fs ms Mm Mm')
  then obtain ms' Mm\<^sub>D where P_D: "class P C = \<lfloor>(D, fs, ms')\<rfloor>"
     and ms: "ms = map (compM f) ms'" and C_nObj: "C \<noteq> Object"
     and Mm\<^sub>D: "P \<turnstile> D sees_methods Mm\<^sub>D"
     and Mm: "Mm = (\<lambda>a. map_option (case_prod (\<lambda>(b, Ts, T, m). Pair (b, Ts, T, f b m))) (Mm\<^sub>D a))"
    by(clarsimp simp:compC_def)

  let ?Mm = "Mm\<^sub>D ++ (map_option (\<lambda>m. (m, C)) \<circ> map_of ms')"
  let ?Mm1 = "Mm ++ (map_option (\<lambda>m. (m, C)) \<circ> map_of ms)"
  let ?Mm2 = "Mm ++ (map_option (\<lambda>m. (m, C)) \<circ> map_of (map (compM f) ms'))"
  let ?Mm3 = "?map ?Mm"
  have "Mm' = ?Mm1" by fact
  also have "\<dots> = ?Mm2" using ms by simp
  also have "\<dots> = ?Mm3"
    by(rule ext)(simp add:Mm map_add_def compM_def map_of_map245)
  moreover have "P \<turnstile> C sees_methods ?Mm"
    using sees_methods_rec[OF P_D C_nObj Mm\<^sub>D] by simp
  ultimately show ?case by fast
qed
(*>*)


lemma sees_method_compPD:
  "compP f P \<turnstile> C sees M,b: Ts\<rightarrow>T = fm in D \<Longrightarrow>
  \<exists>m. P \<turnstile> C sees M,b: Ts\<rightarrow>T = m in D \<and> f b m = fm"
(*<*)
proof -
  assume "compP f P \<turnstile> C sees M,b: Ts\<rightarrow>T = fm in D"
  then obtain Mm where Mm: "compP f P \<turnstile> C sees_methods Mm"
     and MmM: "Mm M = \<lfloor>((b, Ts, T, fm), D)\<rfloor>"
    by(clarsimp simp:Method_def)
  show ?thesis using sees_methods_compPD[OF Mm refl] MmM
    by(fastforce simp: Method_def)
qed
(*>*)


lemma [simp]: "subcls1(compP f P) = subcls1 P"
(*<*)
by(fastforce simp add: is_class_def compC_def intro:subcls1I order_antisym dest:subcls1D)
(*>*)


lemma compP_widen[simp]: "(compP f P \<turnstile> T \<le> T') = (P \<turnstile> T \<le> T')"
(*<*)by(cases T')(simp_all add:widen_Class)(*>*)


lemma [simp]: "(compP f P \<turnstile> Ts [\<le>] Ts') = (P \<turnstile> Ts [\<le>] Ts')"
(*<*)
proof(induct Ts)
  case (Cons a Ts)
  then show ?case by(cases Ts')(auto simp:fun_of_def)
qed simp
(*>*)


lemma [simp]: "is_type (compP f P) T = is_type P T"
(*<*)by(cases T) simp_all(*>*)


lemma [simp]: "(compP (f::staticb\<Rightarrow>'a\<Rightarrow>'b) P \<turnstile> C has_fields FDTs) = (P \<turnstile> C has_fields FDTs)"
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


lemma fields_compP [simp]: "fields (compP f P) C = fields P C"
(*<*)by(simp add:fields_def)(*>*)

lemma ifields_compP [simp]: "ifields (compP f P) C = ifields P C"
(*<*)by(simp add:ifields_def)(*>*)

lemma blank_compP [simp]: "blank (compP f P) C = blank P C"
(*<*)by(simp add:blank_def)(*>*)

lemma isfields_compP [simp]: "isfields (compP f P) C = isfields P C"
(*<*)by(simp add:isfields_def)(*>*)

lemma sblank_compP [simp]: "sblank (compP f P) C = sblank P C"
(*<*)by(simp add:sblank_def)(*>*)

lemma sees_fields_compP [simp]: "(compP f P \<turnstile> C sees F,b:T in D) = (P \<turnstile> C sees F,b:T in D)"
(*<*)by(simp add:sees_field_def)(*>*)

lemma has_field_compP [simp]: "(compP f P \<turnstile> C has F,b:T in D) = (P \<turnstile> C has F,b:T in D)"
(*<*)by(simp add:has_field_def)(*>*)

lemma field_compP [simp]: "field (compP f P) F D = field P F D"
(*<*)by(simp add:field_def)(*>*)


subsection\<open>Invariance of @{term wf_prog} under compilation \<close>

lemma [iff]: "distinct_fst (compP f P) = distinct_fst P"
(*<*)
by (induct P)
   (auto simp:distinct_fst_def compP_def compC_def image_iff)
(*>*)


lemma [iff]: "distinct_fst (map (compM f) ms) = distinct_fst ms"
(*<*)
by (induct ms)
   (auto simp:distinct_fst_def compM_def image_iff)
(*>*)


lemma [iff]: "wf_syscls (compP f P) = wf_syscls P"
(*<*)by(simp add:wf_syscls_def compP_def compC_def image_def Bex_def)(*>*)


lemma [iff]: "wf_fdecl (compP f P) = wf_fdecl P"
(*<*)by(simp add:wf_fdecl_def)(*>*)


lemma wf_clinit_compM [iff]: "wf_clinit (map (compM f) ms) = wf_clinit ms"
(*<*)
proof(rule iffI)
  assume "wf_clinit (map (compM f) ms)"
  then obtain m where "(clinit, Static, [], Void, m) \<in> set ms"
    by(clarsimp simp: wf_clinit_def compM_def)
  then show "wf_clinit ms" by(fastforce simp: wf_clinit_def)
next
  assume "wf_clinit ms"
  then obtain m where "(clinit, Static, [], Void, m) \<in> set ms"
    by(clarsimp simp: wf_clinit_def compM_def)
  then have "\<exists>m. (clinit, Static, [], Void, m)
        \<in> (\<lambda>x. case x of (M, b, Ts, T, m) \<Rightarrow> (M, b, Ts, T, f b m)) ` set ms"
    by(rule_tac x = "f Static m" in exI) (simp add: rev_image_eqI)
  then show "wf_clinit (map (compM f) ms)"
    by(simp add: wf_clinit_def compM_def)
qed
(*>*)

lemma set_compP:
 "((C,D,fs,ms') \<in> set(compP f P)) =
  (\<exists>ms. (C,D,fs,ms) \<in> set P \<and> ms' = map (compM f) ms)"
(*<*)by(fastforce simp add:compP_def compC_def image_iff Bex_def)(*>*)

lemma wf_cdecl_compPI:
  "\<lbrakk> \<And>C M b Ts T m. 
     \<lbrakk> wf_mdecl wf\<^sub>1 P C (M,b,Ts,T,m); P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in C \<rbrakk>
     \<Longrightarrow> wf_mdecl wf\<^sub>2 (compP f P) C (M,b,Ts,T, f b m);
    \<forall>x\<in>set P. wf_cdecl wf\<^sub>1 P x; x \<in> set (compP f P); wf_prog p P \<rbrakk>
  \<Longrightarrow> wf_cdecl wf\<^sub>2 (compP f P) x"
(*<*)
proof -
  assume
   wfm: "\<And>C M b Ts T m. \<lbrakk> wf_mdecl wf\<^sub>1 P C (M,b,Ts,T,m); P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in C \<rbrakk>
     \<Longrightarrow> wf_mdecl wf\<^sub>2 (compP f P) C (M,b,Ts,T, f b m)"
    and wfc: "\<forall>x\<in>set P. wf_cdecl wf\<^sub>1 P x"
    and compP: "x \<in> set (compP f P)" and wf: "wf_prog p P"
  obtain C D fs ms where x: "x = (C, D, fs, map (compM f) ms)"
    and x_set: "(C, D, fs, ms) \<in> set P"
   using compP by(case_tac x) (clarsimp simp: set_compP)
  have wfc': "wf_cdecl wf\<^sub>1 P (C, D, fs, ms)" using wfc x_set by fast
  let ?P = "compP f P" and ?ms = "compM f ` set ms"
  { fix M b Ts T m
    assume M: "(M,b,Ts,T,m) \<in> set ms"
    then have "wf_mdecl wf\<^sub>1 P C (M, b, Ts, T, m)" using wfc'
      by(simp add:wf_cdecl_def)
    moreover have cM: "P \<turnstile> C sees M, b :  Ts\<rightarrow>T = m in C" using M
      by(rule mdecl_visible[OF wf x_set])
    ultimately have "wf_mdecl wf\<^sub>2 (compP f P) C (M, b, Ts, T, f b m)"
      by(rule wfm)
  }
  then have "\<forall>m \<in> ?ms. wf_mdecl wf\<^sub>2 ?P C m"
    by (clarsimp simp:compM_def)
  moreover have "C \<noteq> Object \<longrightarrow>
   (\<forall>(M,b,Ts,T,m)\<in>?ms.
      \<forall>D' b' Ts' T' m'. ?P \<turnstile> D sees M,b':Ts' \<rightarrow> T' = m' in D' \<longrightarrow>
                       b = b' \<and> P \<turnstile> Ts' [\<le>] Ts \<and> P \<turnstile> T \<le> T')"
  proof -
    { fix M b Ts T m D' b' Ts' T' m'
      assume "C \<noteq> Object" and "(M,b,Ts,T,m)\<in>?ms"
        and dM: "?P \<turnstile> D sees M,b':Ts' \<rightarrow> T' = m' in D'"
      then have "b = b' \<and> P \<turnstile> Ts' [\<le>] Ts \<and> P \<turnstile> T \<le> T'"
       using wfc' sees_method_compPD[OF dM]
        by(fastforce simp:wf_cdecl_def image_iff compM_def)
    }
    then show ?thesis by fast
  qed
  moreover have "(\<forall>f\<in>set fs. wf_fdecl P f) \<and> distinct_fst fs
     \<and> distinct_fst ms \<and> wf_clinit ms
     \<and> (C \<noteq> Object \<longrightarrow> is_class P D \<and> \<not> P \<turnstile> D \<preceq>\<^sup>* C)" using wfc'
    by(simp add: wf_cdecl_def)
  ultimately show ?thesis using x by(simp add:wf_cdecl_def)
qed
(*>*)


lemma wf_prog_compPI:
assumes lift: 
  "\<And>C M b Ts T m. 
    \<lbrakk> P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in C; wf_mdecl wf\<^sub>1 P C (M,b,Ts,T,m) \<rbrakk>
    \<Longrightarrow> wf_mdecl wf\<^sub>2 (compP f P) C (M,b,Ts,T, f b m)"
and wf: "wf_prog wf\<^sub>1 P"
shows "wf_prog wf\<^sub>2 (compP f P)"
(*<*)
using wf
by (simp add:wf_prog_def) (blast intro:wf_cdecl_compPI lift wf)
(*>*)


end
