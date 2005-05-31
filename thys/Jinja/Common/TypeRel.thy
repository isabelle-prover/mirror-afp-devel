(*  Title:      Jinja/Common/TypeRel.thy
    ID:         $Id: TypeRel.thy,v 1.1 2005-05-31 23:21:04 lsf37 Exp $
    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* \isaheader{Relations between Jinja Types} *}

theory TypeRel = Decl:

subsection{* The subclass relations *}

consts
  subcls1 :: "'m prog \<Rightarrow> (cname \<times> cname) set"  -- "subclass"

(*<*)
syntax (xsymbols)
  subcls1 :: "'m prog \<Rightarrow> [cname, cname] \<Rightarrow> bool" ("_ \<turnstile> _ \<prec>\<^sup>1 _" [71,71,71] 70)
  subcls  :: "'m prog \<Rightarrow> [cname, cname] \<Rightarrow> bool" ("_ \<turnstile> _ \<preceq>\<^sup>* _"  [71,71,71] 70)
(*>*)

translations
  "P \<turnstile> C  \<prec>\<^sup>1 D"  ==  "(C,D) \<in> subcls1 P"
  "P \<turnstile> C  \<preceq>\<^sup>*  D"  ==  "(C,D) \<in> (subcls1 P)\<^sup>*"
 (*<*)
  "\<not> P \<turnstile> C  \<preceq>\<^sup>*  D" <= "(C,D) \<notin> (subcls1 P)\<^sup>*"
(*>*)

inductive "subcls1 P"
intros subcls1I: "\<lbrakk>class P C = Some (D,rest); C \<noteq> Object\<rbrakk> \<Longrightarrow> P \<turnstile> C \<prec>\<^sup>1 D"

lemma subcls1D: "P \<turnstile> C \<prec>\<^sup>1 D \<Longrightarrow> C \<noteq> Object \<and> (\<exists>fs ms. class P C = Some (D,fs,ms))"
(*<*)by(erule subcls1.induct)(fastsimp simp add:is_class_def)(*>*)

lemma [iff]: "\<not> P \<turnstile> Object \<prec>\<^sup>1 C"
(*<*)by(fastsimp dest:subcls1D)(*>*)

lemma [iff]: "(P \<turnstile> Object \<preceq>\<^sup>* C) = (C = Object)"
(*<*)
apply(rule iffI)
 apply(erule converse_rtranclE)
  apply simp_all
done
(*>*)

lemma finite_subcls1: "finite (subcls1 P)"
(*<*)
apply(subgoal_tac "subcls1 P =
 (SIGMA C:{C. is_class P C}. {D. C\<noteq>Object \<and> fst (the (class P C))=D})")
 prefer 2
 apply(fastsimp simp:is_class_def dest: subcls1D elim: subcls1I)
apply simp
apply(rule finite_SigmaI [OF finite_is_class])
apply(rule_tac B = "{fst (the (class P C))}" in finite_subset)
apply  auto
done
(*>*)
(*
lemma subcls_is_class: "(C,D) \<in> (subcls1 P)\<^sup>+ \<Longrightarrow> is_class P C"
apply (unfold is_class_def)
apply(erule trancl_trans_induct)
apply (auto dest!: subcls1D)
done

lemma subcls_is_class: "P \<turnstile> C \<preceq>\<^sup>* D \<Longrightarrow> is_class P D \<longrightarrow> is_class P C"
apply (unfold is_class_def)
apply (erule rtrancl_induct)
apply  (drule_tac [2] subcls1D)
apply  auto
done
*)


subsection{* The subtype relations *}

consts
  widen   :: "'m prog \<Rightarrow> (ty \<times> ty) set"  -- "widening"

(*<*)
syntax (xsymbols)
  widen   :: "'m prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ \<le> _"   [71,71,71] 70)
  widens  :: "'m prog \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> bool" ("_ \<turnstile> _ [\<le>] _" [71,71,71] 70)
(*>*)

translations
  "P \<turnstile> S \<le> T"  ==  "(S,T) \<in> widen P"
  "P \<turnstile> Ts [\<le>] Ts'"  ==  "list_all2 (fun_of (widen P)) Ts Ts'"

inductive "widen P"
intros
  widen_refl[iff]: "P \<turnstile> T \<le> T"
  widen_subcls: "P \<turnstile> C \<preceq>\<^sup>* D  \<Longrightarrow>  P \<turnstile> Class C \<le> Class D"
  widen_null[iff]: "P \<turnstile> NT \<le> Class C"

lemma [iff]: "(P \<turnstile> T \<le> Void) = (T = Void)"
(*<*)by (auto elim: widen.elims)(*>*)

lemma [iff]: "(P \<turnstile> T \<le> Boolean) = (T = Boolean)"
(*<*)by (auto elim: widen.elims)(*>*)

lemma [iff]: "(P \<turnstile> T \<le> Integer) = (T = Integer)"
(*<*)by (auto elim: widen.elims)(*>*)

lemma [iff]: "(P \<turnstile> Void \<le> T) = (T = Void)"
(*<*)by (auto elim: widen.elims)(*>*)

lemma [iff]: "(P \<turnstile> Boolean \<le> T) = (T = Boolean)"
(*<*)by (auto elim: widen.elims)(*>*)

lemma [iff]: "(P \<turnstile> Integer \<le> T) = (T = Integer)"
(*<*)by (auto elim: widen.elims)(*>*)


lemma Class_widen: "P \<turnstile> Class C \<le> T  \<Longrightarrow>  \<exists>D. T = Class D"
(*<*)
apply (ind_cases "P\<turnstile>S\<le>T")
apply auto
done
(*>*)

lemma [iff]: "(P \<turnstile> T \<le> NT) = (T = NT)"
(*<*)
apply(cases T)
apply(auto dest:Class_widen)
done
(*>*)

lemma Class_widen_Class [iff]: "(P \<turnstile> Class C \<le> Class D) = (P \<turnstile> C \<preceq>\<^sup>* D)"
(*<*)
apply (rule iffI)
apply (ind_cases " P \<turnstile> S \<le> T")
apply (auto elim: widen_subcls)
done
(*>*)

lemma widen_Class: "(P \<turnstile> T \<le> Class C) = (T = NT \<or> (\<exists>D. T = Class D \<and> P \<turnstile> D \<preceq>\<^sup>* C))"
(*<*)by(induct T, auto)(*>*)


lemma widen_trans[trans]: "\<lbrakk>P \<turnstile> S \<le> U; P \<turnstile> U \<le> T\<rbrakk> \<Longrightarrow> P \<turnstile> S \<le> T"
(*<*)
proof -
  assume "P\<turnstile>S \<le> U" thus "\<And>T. P \<turnstile> U \<le> T \<Longrightarrow> P \<turnstile> S \<le> T"
  proof induct
    case (widen_refl T T') thus "P \<turnstile> T \<le> T'" .
  next
    case (widen_subcls C D T)
    then obtain E where "T = Class E" by (blast dest: Class_widen)
    with widen_subcls show "P \<turnstile> Class C \<le> T" by (auto elim: rtrancl_trans)
  next
    case (widen_null C RT)
    then obtain D where "RT = Class D" by (blast dest: Class_widen)
    thus "P \<turnstile> NT \<le> RT" by auto
  qed
qed
(*>*)

lemma widens_trans [trans]: "\<lbrakk>P \<turnstile> Ss [\<le>] Ts; P \<turnstile> Ts [\<le>] Us\<rbrakk> \<Longrightarrow> P \<turnstile> Ss [\<le>] Us"
(*<*)by (rule rel_list_all2_trans, rule widen_trans)(*>*)


(*<*)
lemmas widens_refl [iff] = rel_list_all2_refl [OF widen_refl]
lemmas widens_Cons [iff] = rel_list_all2_Cons1 [of "widen P", standard]
(*>*)


subsection{* Method lookup *}

consts
  Methods :: "'m prog \<Rightarrow> (cname \<times> (mname \<rightharpoonup> (ty list \<times> ty \<times> 'm) \<times> cname))set"

(*<*)
syntax
  "_sees_methods" :: "['m prog, cname, mname \<rightharpoonup> (ty list \<times> ty \<times> 'm) \<times> cname] \<Rightarrow> bool"
                    ("_ \<turnstile> _ sees'_methods _" [51,51,51] 50)
(*>*)

translations "P \<turnstile> C sees_methods Mm"  ==  "(C,Mm) \<in> Methods P"

inductive "Methods P"
intros
sees_methods_Object:
 "\<lbrakk> class P Object = Some(D,fs,ms); Mm = option_map (\<lambda>m. (m,Object)) \<circ> map_of ms \<rbrakk>
  \<Longrightarrow> P \<turnstile> Object sees_methods Mm"
sees_methods_rec:
 "\<lbrakk> class P C = Some(D,fs,ms); C \<noteq> Object; P \<turnstile> D sees_methods Mm;
    Mm' = Mm ++ (option_map (\<lambda>m. (m,C)) \<circ> map_of ms) \<rbrakk>
  \<Longrightarrow> P \<turnstile> C sees_methods Mm'";

lemma sees_methods_fun:
assumes 1: "P \<turnstile> C sees_methods Mm"
shows "\<And>Mm'. P \<turnstile> C sees_methods Mm' \<Longrightarrow> Mm' = Mm"
 (*<*)
using 1
proof induct
  case (sees_methods_rec C D Dres Cres fs ms Cres')
  have class: "class P C = Some (D, fs, ms)"
   and notObj: "C \<noteq> Object" and Dmethods: "P \<turnstile> D sees_methods Dres"
   and IH: "\<And>Dres'. P \<turnstile> D sees_methods Dres' \<Longrightarrow> Dres' = Dres"
   and Cres: "Cres = Dres ++ (option_map (\<lambda>m. (m,C)) \<circ> map_of ms)"
   and Cmethods': "P \<turnstile> C sees_methods Cres'" .
  from Cmethods' notObj class obtain Dres'
    where Dmethods': "P \<turnstile> D sees_methods Dres'"
     and Cres': "Cres' = Dres' ++ (option_map (\<lambda>m. (m,C)) \<circ> map_of ms)"
    by(auto elim: Methods.elims)
  from Cres Cres' IH[OF Dmethods'] show "Cres' = Cres" by simp
next
  case sees_methods_Object thus ?case by(auto elim: Methods.elims)
qed
(*>*)

lemma visible_methods_exist:
  "P \<turnstile> C sees_methods Mm \<Longrightarrow> Mm M = Some(m,D) \<Longrightarrow>
   (\<exists>D' fs ms. class P D = Some(D',fs,ms) \<and> map_of ms M = Some m)"
 (*<*)by(induct rule:Methods.induct) auto(*>*)

lemma sees_methods_decl_above:
assumes Csees: "P \<turnstile> C sees_methods Mm"
shows "Mm M = Some(m,D) \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
 (*<*)
using Csees
proof induct
  case sees_methods_Object thus ?case by auto
next
  case sees_methods_rec thus ?case
    by(fastsimp simp:option_map_def split:option.splits
                elim:converse_rtrancl_into_rtrancl[OF subcls1I])
qed
(*>*)

lemma sees_methods_idemp:
assumes Cmethods: "P \<turnstile> C sees_methods Mm"
shows "\<And>m D. Mm M = Some(m,D) \<Longrightarrow>
              \<exists>Mm'. (P \<turnstile> D sees_methods Mm') \<and> Mm' M = Some(m,D)"
(*<*)
using Cmethods
proof induct
  case sees_methods_Object thus ?case
    by(fastsimp dest: Methods.sees_methods_Object)
next
  case sees_methods_rec thus ?case
    by(fastsimp split:option.splits dest: Methods.sees_methods_rec)
qed
(*>*)

(*FIXME something wrong with induct: need to attache [consumes 1]
directly to proof of thm, declare does not work. *)

lemma sees_methods_decl_mono:
assumes sub: "P \<turnstile> C' \<preceq>\<^sup>* C"
shows "P \<turnstile> C sees_methods Mm \<Longrightarrow>
       \<exists>Mm' Mm\<^isub>2. P \<turnstile> C' sees_methods Mm' \<and> Mm' = Mm ++ Mm\<^isub>2 \<and>
                 (\<forall>M m D. Mm\<^isub>2 M = Some(m,D) \<longrightarrow> P \<turnstile> D \<preceq>\<^sup>* C)"
(*<*)
      (is "_ \<Longrightarrow> \<exists>Mm' Mm2. ?Q C' C Mm' Mm2")
using sub
proof (induct rule:converse_rtrancl_induct)
  assume "P \<turnstile> C sees_methods Mm"
  hence "?Q C C Mm empty" by simp
  thus "\<exists>Mm' Mm2. ?Q C C Mm' Mm2" by blast
next
  fix C'' C'
  assume sub1: "P \<turnstile> C'' \<prec>\<^sup>1 C'" and sub: "P \<turnstile> C' \<preceq>\<^sup>* C"
  and IH: "P \<turnstile> C sees_methods Mm \<Longrightarrow>
           \<exists>Mm' Mm2. P \<turnstile> C' sees_methods Mm' \<and>
                Mm' = Mm ++ Mm2 \<and> (\<forall>M m D. Mm2 M = Some(m,D) \<longrightarrow> P \<turnstile> D \<preceq>\<^sup>* C)"
  and Csees: "P \<turnstile> C sees_methods Mm"
  from IH[OF Csees] obtain Mm' Mm2 where C'sees: "P \<turnstile> C' sees_methods Mm'"
    and Mm': "Mm' = Mm ++ Mm2"
    and subC:"\<forall>M m D. Mm2 M = Some(m,D) \<longrightarrow> P \<turnstile> D \<preceq>\<^sup>* C" by blast
  obtain fs ms where class: "class P C'' = Some(C',fs,ms)" "C'' \<noteq> Object"
    using subcls1D[OF sub1] by blast
  let ?Mm3 = "option_map (\<lambda>m. (m,C'')) \<circ> map_of ms"
  have "P \<turnstile> C'' sees_methods (Mm ++ Mm2) ++ ?Mm3"
    using sees_methods_rec[OF class C'sees refl] Mm' by simp
  hence "?Q C'' C ((Mm ++ Mm2) ++ ?Mm3) (Mm2++?Mm3)"
    using converse_rtrancl_into_rtrancl[OF sub1 sub]
    by simp (simp add:map_add_def subC split:option.split)
  thus "\<exists>Mm' Mm2. ?Q C'' C Mm' Mm2" by blast
qed
(*>*)


constdefs
  Method :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'm \<Rightarrow> cname \<Rightarrow> bool"
            ("_ \<turnstile> _ sees _: _\<rightarrow>_ = _ in _" [51,51,51,51,51,51,51] 50)
  "P \<turnstile> C sees M: Ts\<rightarrow>T = m in D  \<equiv>
  \<exists>Mm. P \<turnstile> C sees_methods Mm \<and> Mm M = Some((Ts,T,m),D)"

  has_method :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> bool" ("_ \<turnstile> _ has _" [51,0,51] 50)
  "P \<turnstile> C has M \<equiv> \<exists>Ts T m D. P \<turnstile> C sees M:Ts\<rightarrow>T = m in D"

lemma sees_method_fun:
  "\<lbrakk>P \<turnstile> C sees M:TS\<rightarrow>T = m in D; P \<turnstile> C sees M:TS'\<rightarrow>T' = m' in D' \<rbrakk>
   \<Longrightarrow> TS' = TS \<and> T' = T \<and> m' = m \<and> D' = D"
 (*<*)by(fastsimp dest: sees_methods_fun simp:Method_def)(*>*)

lemma sees_method_decl_above:
  "P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
 (*<*)by(clarsimp simp:Method_def sees_methods_decl_above)(*>*)

lemma visible_method_exists:
  "P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<Longrightarrow>
  \<exists>D' fs ms. class P D = Some(D',fs,ms) \<and> map_of ms M = Some(Ts,T,m)"
(*<*)by(fastsimp simp:Method_def dest!: visible_methods_exist)(*>*)


lemma sees_method_idemp:
  "P \<turnstile> C sees M:Ts\<rightarrow>T=m in D \<Longrightarrow> P \<turnstile> D sees M:Ts\<rightarrow>T=m in D"
 (*<*)by(fastsimp simp: Method_def intro:sees_methods_idemp)(*>*)

lemma sees_method_decl_mono:
  "\<lbrakk> P \<turnstile> C' \<preceq>\<^sup>* C; P \<turnstile> C sees M:Ts\<rightarrow>T = m in D;
     P \<turnstile> C' sees M:Ts'\<rightarrow>T' = m' in D' \<rbrakk> \<Longrightarrow> P \<turnstile> D' \<preceq>\<^sup>* D"
 (*<*)
apply(frule sees_method_decl_above)
apply(unfold Method_def)
apply clarsimp
apply(drule (1) sees_methods_decl_mono)
apply clarsimp
apply(drule (1) sees_methods_fun)
apply clarsimp
apply(blast intro:rtrancl_trans)
done
(*>*)

lemma sees_method_is_class:
  "\<lbrakk> P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<rbrakk> \<Longrightarrow> is_class P C"
(*<*)by (auto simp add: is_class_def Method_def elim: Methods.induct)(*>*)


subsection{* Field lookup *}

consts
  Fields :: "'m prog \<Rightarrow> (cname \<times> ((vname \<times> cname) \<times> ty) list)set"

(*<*)
syntax
  "_has_fields" :: "['m prog, cname, ((vname \<times> cname) \<times> ty) list] \<Rightarrow> bool"
                  ("_ \<turnstile> _ has'_fields _" [51,51,51] 50)
(*>*)

translations
  "P \<turnstile> C has_fields FDTs"  ==  "(C,FDTs) \<in> Fields P"

inductive "Fields P"
intros
has_fields_rec:
"\<lbrakk> class P C = Some(D,fs,ms); C \<noteq> Object; P \<turnstile> D has_fields FDTs;
   FDTs' = map (\<lambda>(F,T). ((F,C),T)) fs @ FDTs \<rbrakk>
 \<Longrightarrow> P \<turnstile> C has_fields FDTs'"
has_fields_Object:
"\<lbrakk> class P Object = Some(D,fs,ms); FDTs = map (\<lambda>(F,T). ((F,Object),T)) fs \<rbrakk>
 \<Longrightarrow> P \<turnstile> Object has_fields FDTs"

lemma has_fields_fun:
assumes 1: "P \<turnstile> C has_fields FDTs"
shows "\<And>FDTs'. P \<turnstile> C has_fields FDTs' \<Longrightarrow> FDTs' = FDTs"
 (*<*)
using 1
proof induct
  case (has_fields_rec C D Dres Cres fs ms Cres')
  have class: "class P C = Some (D, fs, ms)"
   and notObj: "C \<noteq> Object" and DFields: "P \<turnstile> D has_fields Dres"
   and IH: "\<And>Dres'. P \<turnstile> D has_fields Dres' \<Longrightarrow> Dres' = Dres"
   and Cres: "Cres = map (\<lambda>(F,T). ((F,C),T)) fs @ Dres"
   and CFields': "P \<turnstile> C has_fields Cres'" .
  from CFields' notObj class obtain Dres'
    where DFields': "P \<turnstile> D has_fields Dres'"
     and Cres': "Cres' = map (\<lambda>(F,T). ((F,C),T)) fs @ Dres'"
    by(auto elim: Fields.elims)
  from Cres Cres' IH[OF DFields'] show "Cres' = Cres" by simp
next
  case has_fields_Object thus ?case by(auto elim: Fields.elims)
qed
(*>*)

lemma all_fields_in_has_fields:
assumes sub: "P \<turnstile> C has_fields FDTs"
shows "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* D; class P D = Some(D',fs,ms); (F,T) \<in> set fs \<rbrakk>
       \<Longrightarrow> ((F,D),T) \<in> set FDTs"
(*<*)
using sub apply(induct)
 apply(simp add:image_def)
 apply(erule converse_rtranclE)
  apply(force)
 apply(drule subcls1D)
 apply fastsimp
apply(force simp:image_def)
done
(*>*)


lemma has_fields_decl_above:
assumes fields: "P \<turnstile> C has_fields FDTs"
shows "((F,D),T) \<in> set FDTs \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
(*<*)
using fields apply(induct)
 prefer 2 apply(fastsimp dest: tranclD)
apply clarsimp
apply(erule disjE)
 apply(clarsimp simp add:image_def)
apply simp
apply(blast dest:subcls1I converse_rtrancl_into_rtrancl)
done
(*>*)


lemma subcls_notin_has_fields:
assumes fields: "P \<turnstile> C has_fields FDTs"
shows "((F,D),T) \<in> set FDTs \<Longrightarrow> (D,C) \<notin> (subcls1 P)\<^sup>+"
(*<*)
using fields apply(induct)
 prefer 2 apply(fastsimp dest: tranclD)
apply clarsimp
apply(erule disjE)
 apply(clarsimp simp add:image_def)
 apply(drule tranclD)
 apply clarify
 apply(frule subcls1D)
 apply(fastsimp dest:tranclD all_fields_in_has_fields)
apply simp
apply(blast dest:subcls1I trancl_into_trancl)
done
(*>*)


lemma has_fields_mono_lem:
assumes sub: "P \<turnstile> D \<preceq>\<^sup>* C"
shows "P \<turnstile> C has_fields FDTs
         \<Longrightarrow> \<exists>pre. P \<turnstile> D has_fields pre@FDTs \<and> dom(map_of pre) \<inter> dom(map_of FDTs) = {}"
(*<*)
using sub apply(induct rule:converse_rtrancl_induct)
 apply(rule_tac x = "[]" in exI)
 apply simp
apply clarsimp
apply(rename_tac D' D pre)
apply(subgoal_tac "(D',C) : (subcls1 P)^+")
 prefer 2 apply(erule (1) rtrancl_into_trancl2)
apply(drule subcls1D)
apply clarsimp
apply(rename_tac fs ms)
apply(drule (2) has_fields_rec)
 apply(rule refl)
apply(rule_tac x = "map (\<lambda>(F,T). ((F,D'),T)) fs @ pre" in exI)
apply simp
apply(simp add:Int_Un_distrib2)
apply(rule equals0I)
apply(auto dest: subcls_notin_has_fields simp:dom_map_of image_def)
done
(*>*)

(* FIXME why is Field not displayed correctly? TypeRel qualifier seems to confuse printer*)
constdefs
  has_field :: "'m prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> ty \<Rightarrow> cname \<Rightarrow> bool"
                   ("_ \<turnstile> _ has _:_ in _" [51,51,51,51,51] 50)
  "P \<turnstile> C has F:T in D  \<equiv>
  \<exists>FDTs. P \<turnstile> C has_fields FDTs \<and> map_of FDTs (F,D) = Some T"

lemma has_field_mono:
  "\<lbrakk> P \<turnstile> C has F:T in D; P \<turnstile> C' \<preceq>\<^sup>* C \<rbrakk> \<Longrightarrow> P \<turnstile> C' has F:T in D"
(*<*)
apply(clarsimp simp:has_field_def)
apply(drule (1) has_fields_mono_lem)
apply(fastsimp simp: map_add_def split:option.splits)
done
(*>*)


constdefs
  sees_field :: "'m prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> ty \<Rightarrow> cname \<Rightarrow> bool"
                  ("_ \<turnstile> _ sees _:_ in _" [51,51,51,51,51] 50)
  "P \<turnstile> C sees F:T in D  \<equiv>
  \<exists>FDTs. P \<turnstile> C has_fields FDTs \<and>
            map_of (map (\<lambda>((F,D),T). (F,(D,T))) FDTs) F = Some(D,T)"

lemma map_of_remap_SomeD:
  "map_of (map (\<lambda>((k,k'),x). (k,(k',x))) t) k = Some (k',x) \<Longrightarrow> map_of t (k, k') = Some x"
(*<*)by (induct t) (auto simp:fun_upd_apply split: split_if_asm)(*>*)


lemma has_visible_field:
  "P \<turnstile> C sees F:T in D \<Longrightarrow> P \<turnstile> C has F:T in D"
(*<*)by(auto simp add:has_field_def sees_field_def map_of_remap_SomeD)(*>*)


lemma sees_field_fun:
  "\<lbrakk>P \<turnstile> C sees F:T in D; P \<turnstile> C sees F:T' in D'\<rbrakk> \<Longrightarrow> T' = T \<and> D' = D"
(*<*)by(fastsimp simp:sees_field_def dest:has_fields_fun)(*>*)


lemma sees_field_decl_above:
  "P \<turnstile> C sees F:T in D \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
(*<*)
apply(auto simp:sees_field_def)
apply(blast  intro: has_fields_decl_above map_of_SomeD map_of_remap_SomeD)
done
(*>*)

(* FIXME ugly *)  
lemma sees_field_idemp:
  "P \<turnstile> C sees F:T in D \<Longrightarrow> P \<turnstile> D sees F:T in D"
(*<*)
  apply (unfold sees_field_def)
  apply clarsimp
  apply (rule_tac P = "map_of ?xs F = ?y" in mp)
   prefer 2 
   apply assumption 
  apply (thin_tac "map_of ?xs F = ?y")
  apply (erule Fields.induct)
   apply clarsimp
   apply (frule map_of_SomeD)
   apply clarsimp
   apply (fastsimp intro: has_fields_rec)
  apply clarsimp
  apply (frule map_of_SomeD)
  apply clarsimp
  apply (fastsimp intro: has_fields_Object)
  done
(*>*)

subsection "Functional lookup"

constdefs
  method :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> cname \<times> ty list \<times> ty \<times> 'm"
  "method P C M  \<equiv>  THE (D,Ts,T,m). P \<turnstile> C sees M:Ts \<rightarrow> T = m in D"

  field  :: "'m prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> cname \<times> ty"
  "field P C F  \<equiv>  THE (D,T). P \<turnstile> C sees F:T in D"
                                                        
  fields :: "'m prog \<Rightarrow> cname \<Rightarrow> ((vname \<times> cname) \<times> ty) list" 
  "fields P C  \<equiv>  THE FDTs. P \<turnstile> C has_fields FDTs"                

lemma [simp]: "P \<turnstile> C has_fields FDTs \<Longrightarrow> fields P C = FDTs"
(*<*)by (unfold fields_def) (auto dest: has_fields_fun)(*>*)

lemma field_def2 [simp]: "P \<turnstile> C sees F:T in D \<Longrightarrow> field P C F = (D,T)"
(*<*)by (unfold field_def) (auto dest: sees_field_fun)(*>*)

lemma method_def2 [simp]: "P \<turnstile> C sees M: Ts\<rightarrow>T = m in D \<Longrightarrow> method P C M = (D,Ts,T,m)"
(*<*)by (unfold method_def) (auto dest: sees_method_fun)(*>*)
(*<*)
end
(*>*)