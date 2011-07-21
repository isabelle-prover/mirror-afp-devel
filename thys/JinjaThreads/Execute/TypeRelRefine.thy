theory TypeRelRefine imports
  "../Common/TypeRel"
  "~~/src/HOL/Library/AssocList"
  "~~/src/HOL/Library/Cset"
begin

subsection {* Auxiliary lemmata *}

lemma rtranclp_tranclpE:
  assumes "r^** x y"
  obtains (refl) "x = y"
  | (trancl) "r^++ x y"
using assms
by(cases)(blast dest: rtranclp_into_tranclp1)+

lemma map_of_map2: "map_of (map (\<lambda>(k, v). (k, f k v)) xs) k = Option.map (f k) (map_of xs k)"
by(induct xs) auto

lemma map_of_map_K: "map_of (map (\<lambda>k. (k, c)) xs) k = (if k \<in> set xs then Some c else None)"
by(induct xs) auto

definition map_values :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'c) mapping"
where "map_values f m = Mapping.Mapping (\<lambda>k. Option.map (f k) (Mapping.lookup m k))"

lemma map_values_Mapping [simp]: "map_values f (Mapping.Mapping m) = Mapping.Mapping (\<lambda>k. Option.map (f k) (m k))"
by(rule mapping_eqI)(simp add: map_values_def)

lemma assoc_list_map_values [code]:
  "map_values f (Mapping xs) = Mapping (map (\<lambda>(k, v). (k, f k v)) xs)"
by(rule mapping_eqI)(simp add: map_values_def map_of_map2 fun_eq_iff)

definition assoc_list_to_mapping :: "('k \<times> 'v) list \<Rightarrow> ('k, 'v) mapping"
where "assoc_list_to_mapping xs = Mapping.Mapping (map_of xs)"

lemma assoc_list_to_mapping_code [code]:
  "assoc_list_to_mapping xs = foldr (\<lambda>(k, v) m. Mapping.update k v m) xs Mapping.empty"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = Mapping.Mapping (foldr (\<lambda>(k, v) m. m(k \<mapsto> v)) xs empty)"
    by(simp add: assoc_list_to_mapping_def) (metis empty_map_add map_add_map_of_foldr)
  moreover have "?rhs = \<dots>"
    by(induct xs)(auto simp add: Mapping.empty_def Mapping.update_def simp del: fun_upd_apply)
  ultimately show ?thesis by simp
qed

lemma map_Mapping: "Mapping.map f g (Mapping.Mapping m) = Mapping.Mapping (Option.map g \<circ> m \<circ> f)"
by(rule mapping_eqI) simp

abbreviation subclst :: "'m prog \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> bool"
where "subclst P \<equiv> (subcls1 P)^++"

subsection {* Representation type for tabulated lookup functions *}

type_synonym
  'm prog_impl' = 
  "'m cdecl list \<times>
   (cname, 'm class) mapping \<times>
   (cname, cname Cset.set) mapping \<times> 
   (cname, (vname, cname \<times> ty \<times> fmod) mapping) mapping \<times> 
   (cname, (mname, cname \<times> ty list \<times> ty \<times> 'm) mapping) mapping"

definition tabulate_class :: "'m cdecl list \<Rightarrow> (cname, 'm class) mapping"
where "tabulate_class P = Mapping.Mapping (class (Program P))"

definition tabulate_subcls :: "'m cdecl list \<Rightarrow> (cname, cname Cset.set) mapping"
where 
  "tabulate_subcls P = 
  Mapping.Mapping 
    (\<lambda>C. if is_class (Program P) C then
        Some (Cset.Set (\<lambda>D. Program P \<turnstile> C \<preceq>\<^sup>* D)) 
      else None)"

definition tabulate_sees_field :: "'m cdecl list \<Rightarrow> (cname, (vname, cname \<times> ty \<times> fmod) mapping) mapping"
where
  "tabulate_sees_field P =
  Mapping.Mapping
    (\<lambda>C. if is_class (Program P) C then
        Some (Mapping.Mapping (\<lambda>F. if \<exists>T fm D. Program P \<turnstile> C sees F:T (fm) in D then Some (field (Program P) C F) else None)) 
      else None)"

definition tabulate_Method :: "'m cdecl list \<Rightarrow> (cname, (mname, cname \<times> ty list \<times> ty \<times> 'm) mapping) mapping"
where
  "tabulate_Method P =
  Mapping.Mapping 
    (\<lambda>C. if is_class (Program P) C then
         Some (Mapping.Mapping (\<lambda>M. if \<exists>Ts T mthd D. Program P \<turnstile> C sees M:Ts\<rightarrow>T=mthd in D then Some (method (Program P) C M) else None))
      else None)"

fun wf_prog_impl' :: "'m prog_impl' \<Rightarrow> bool"
where
  "wf_prog_impl' (P, c, s, f, m) \<longleftrightarrow>
  c = tabulate_class P \<and>
  s = tabulate_subcls P \<and>
  f = tabulate_sees_field P \<and>
  m = tabulate_Method P"

subsection {* Implementation type for tabulated lookup functions *}

typedef (open) 'm prog_impl = "{P :: 'm prog_impl'. wf_prog_impl' P}"
  morphisms impl_of ProgRefine 
proof
  show "([], Mapping.Mapping (\<lambda>C. None), Mapping.Mapping (\<lambda>C. None), Mapping.Mapping (\<lambda>C. None), Mapping.Mapping (\<lambda>C. None)) \<in> ?prog_impl"
    by(auto simp add: fun_eq_iff is_class_def tabulate_class_def tabulate_subcls_def tabulate_sees_field_def tabulate_Method_def)
qed

lemma impl_of_ProgImpl [simp]:
  "wf_prog_impl' Pfsm \<Longrightarrow> impl_of (ProgRefine Pfsm) = Pfsm"
by(simp add: ProgRefine_inverse)

definition program :: "'m prog_impl \<Rightarrow> 'm prog"
where "program = Program \<circ> fst \<circ> impl_of"

code_datatype program

lemma prog_impl_eq_iff:
  "Pi = Pi' \<longleftrightarrow> program Pi = program Pi'"
apply(cases Pi)
apply(cases Pi')
apply(auto simp add: ProgRefine_inverse program_def ProgRefine_inject)
done

lemma wf_prog_impl'_impl_of [simp, intro!]:
  "wf_prog_impl' (impl_of Pi)"
using impl_of[of Pi] by simp

lemma ProgImpl_impl_of [simp, code abstype]:
  "ProgRefine (impl_of Pi) = Pi"
by(rule impl_of_inverse)

lemma program_ProgRefine [simp]: "wf_prog_impl' Psfm \<Longrightarrow> program (ProgRefine Psfm) = Program (fst Psfm)"
by(simp add: program_def)

lemma classes_program [code]: "classes (program P) = fst (impl_of P)"
by(simp add: program_def)

lemma class_program [code]: "class (program Pi) = Mapping.lookup (fst (snd (impl_of Pi)))"
by(cases Pi)(clarsimp simp add: tabulate_class_def)

subsection {* Refining sub class and lookup functions to use precomputed mappings *}

declare subcls'.equation [code del]

lemma subcls'_program [code]: 
  "subcls' (program Pi) C D \<longleftrightarrow> 
  C = D \<or>
  (case Mapping.lookup (fst (snd (snd (impl_of Pi)))) C of None \<Rightarrow> False
   | Some m \<Rightarrow> Cset.member m D)"
apply(cases Pi)
apply(clarsimp simp add: subcls'_def tabulate_subcls_def)
apply(auto elim!: rtranclp_tranclpE dest: subcls_is_class intro: tranclp_into_rtranclp)
done

lemma subcls'_i_i_i_program [code]:
  "subcls'_i_i_i P C D = (if subcls' P C D then Predicate.single () else bot)"
by(rule pred_eqI)(auto elim: subcls'_i_i_iE intro: subcls'_i_i_iI)

lemma subcls'_i_i_o_program [code]:
  "subcls'_i_i_o (program Pi) C = 
  sup (Predicate.single C) (case Mapping.lookup (fst (snd (snd (impl_of Pi)))) C of None \<Rightarrow> bot | Some m \<Rightarrow> pred_of_cset m)"
by(cases Pi)(fastsimp simp add: subcls'_i_i_o_def subcls'_def tabulate_subcls_def intro!: pred_eqI split: split_if_asm elim: rtranclp_tranclpE dest: subcls_is_class intro: tranclp_into_rtranclp)

lemma rtranclp_FioB_i_i_subcls1_i_i_o_code [code_inline]:
  "rtranclp_FioB_i_i (subcls1_i_i_o P) = subcls'_i_i_i P"
by(auto simp add: fun_eq_iff subcls1_i_i_o_def subcls'_def rtranclp_FioB_i_i_def subcls'_i_i_i_def)

declare Method.equation[code del]
lemma Method_program [code]:
  "program Pi \<turnstile> C sees M:Ts\<rightarrow>T=meth in D \<longleftrightarrow> 
  (case Mapping.lookup (snd (snd (snd (snd (impl_of Pi))))) C of 
    None \<Rightarrow> False
  | Some m \<Rightarrow> 
    (case Mapping.lookup m M of 
       None \<Rightarrow> False
     | Some (D', Ts', T', meth') \<Rightarrow> Ts = Ts' \<and> T = T' \<and> meth = meth' \<and> D = D'))"
by(cases Pi)(auto split: split_if_asm dest: sees_method_is_class simp add: tabulate_Method_def)

lemma Method_i_i_i_o_o_o_o_program [code]:
  "Method_i_i_i_o_o_o_o (program Pi) C M = 
  (case Mapping.lookup (snd (snd (snd (snd (impl_of Pi))))) C of
    None \<Rightarrow> bot
  | Some m \<Rightarrow>
    (case Mapping.lookup m M of
      None \<Rightarrow> bot
    | Some (D, Ts, T, meth) \<Rightarrow> Predicate.single (Ts, T, meth, D)))"
by(auto simp add: Method_i_i_i_o_o_o_o_def Method_program intro!: pred_eqI)

lemma Method_i_i_i_o_o_o_i_program [code]:
  "Method_i_i_i_o_o_o_i (program Pi) C M D = 
  (case Mapping.lookup (snd (snd (snd (snd (impl_of Pi))))) C of
    None \<Rightarrow> bot
  | Some m \<Rightarrow>
    (case Mapping.lookup m M of
      None \<Rightarrow> bot
    | Some (D', Ts, T, meth) \<Rightarrow> if D = D' then Predicate.single (Ts, T, meth) else bot))"
by(auto simp add: Method_i_i_i_o_o_o_i_def Method_program intro!: pred_eqI)

declare sees_field.equation[code del]

lemma sees_field_program [code]:
  "program Pi \<turnstile> C sees F:T (fd) in D \<longleftrightarrow>
  (case Mapping.lookup (fst (snd (snd (snd (impl_of Pi))))) C of
    None \<Rightarrow> False
  | Some m \<Rightarrow> 
    (case Mapping.lookup m F of 
       None \<Rightarrow> False
     | Some (D', T', fd') \<Rightarrow> T = T' \<and> fd = fd' \<and> D = D'))"
by(cases Pi)(auto split: split_if_asm dest: has_visible_field[THEN has_field_is_class] simp add: tabulate_sees_field_def)

lemma sees_field_i_i_i_o_o_o_program [code]:
  "sees_field_i_i_i_o_o_o (program Pi) C F =
  (case Mapping.lookup (fst (snd (snd (snd (impl_of Pi))))) C of
    None \<Rightarrow> bot
  | Some m \<Rightarrow>
    (case Mapping.lookup m F of
       None \<Rightarrow> bot
    | Some (D, T, fd) \<Rightarrow> Predicate.single(T, fd, D)))"
by(auto simp add: sees_field_program sees_field_i_i_i_o_o_o_def intro: pred_eqI)

lemma sees_field_i_i_i_o_o_i_program [code]:
  "sees_field_i_i_i_o_o_i (program Pi) C F D =
  (case Mapping.lookup (fst (snd (snd (snd (impl_of Pi))))) C of
    None \<Rightarrow> bot
  | Some m \<Rightarrow>
    (case Mapping.lookup m F of
       None \<Rightarrow> bot
    | Some (D', T, fd) \<Rightarrow> if D = D' then Predicate.single(T, fd) else bot))"
by(auto simp add: sees_field_program sees_field_i_i_i_o_o_i_def intro: pred_eqI)

lemma field_program [code]:
  "field (program Pi) C F = 
  (case Mapping.lookup (fst (snd (snd (snd (impl_of Pi))))) C of 
    None \<Rightarrow> Predicate.not_unique bot
  | Some m \<Rightarrow> 
    (case Mapping.lookup m F of
       None \<Rightarrow> Predicate.not_unique bot
     | Some (D', T, fd) \<Rightarrow> (D', T, fd)))"
unfolding field_def not_unique_def
by(cases Pi)(fastsimp simp add: tabulate_sees_field_def mem_def split: split_if_asm intro: arg_cong[where f=The] dest: has_visible_field[THEN has_field_is_class] sees_field_fun)

subsection {* Implementation for precomputing mappings *}

definition tabulate_program :: "'m cdecl list \<Rightarrow> 'm prog_impl"
where "tabulate_program P = ProgRefine (P, tabulate_class P, tabulate_subcls P, tabulate_sees_field P, tabulate_Method P)"

lemma impl_of_tabulate_program [code abstract]:
  "impl_of (tabulate_program P) = (P, tabulate_class P, tabulate_subcls P, tabulate_sees_field P, tabulate_Method P)"
by(simp add: tabulate_program_def)

lemma Program_code [code]:
  "Program = program \<circ> tabulate_program"
by(simp add: program_def fun_eq_iff tabulate_program_def)

subsubsection {* @{term "class" } *}

lemma tabulate_class_code [code]:
  "tabulate_class = assoc_list_to_mapping"
by(rule ext)(simp add: tabulate_class_def assoc_list_to_mapping_def)

subsubsection {* @{term "subcls" } *}

inductive subcls1' :: "'m cdecl list \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> bool"
where 
  find: "C \<noteq> Object \<Longrightarrow> subcls1' ((C, D, rest) # P) C D"
| step: "\<lbrakk> C \<noteq> Object; C \<noteq> C'; subcls1' P C D  \<rbrakk> \<Longrightarrow> subcls1' ((C', D', rest) # P) C D"

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  subcls1' .

lemma subcls1_into_subcls1':
  assumes "subcls1 (Program P) C D"
  shows "subcls1' P C D"
proof -
  from assms obtain rest where "map_of P C = \<lfloor>(D, rest)\<rfloor>" "C \<noteq> Object" by cases simp
  thus ?thesis by(induct P)(auto split: split_if_asm intro: subcls1'.intros)
qed

lemma subcls1'_into_subcls1:
  assumes "subcls1' P C D"
  shows "subcls1 (Program P) C D"
using assms
proof(induct)
  case find thus ?case by(auto intro: subcls1.intros)
next
  case step thus ?case by(auto elim!: subcls1.cases intro: subcls1.intros)
qed

lemma subcls1_eq_subcls1':
  "subcls1 (Program P) = subcls1' P"
by(auto simp add: fun_eq_iff intro: subcls1_into_subcls1' subcls1'_into_subcls1)

definition subcls'' :: "'m cdecl list \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> bool"
where "subcls'' P = (subcls1' P)^**"

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  [inductify] 
  subcls'' .

lemma subcls''_eq_subcls: "subcls'' P = subcls (Program P)"
by(simp add: subcls''_def subcls1_eq_subcls1')

lemma subclst_snd_classD: 
  assumes "subclst (Program P) C D"
  shows "D \<in> fst ` snd ` set P"
using assms
by(induct)(fastsimp elim!: subcls1.cases dest!: map_of_SomeD intro: rev_image_eqI)+

definition check_acyclicity :: "(cname, cname Cset.set) mapping \<Rightarrow> 'm cdecl list \<Rightarrow> unit"
where "check_acyclicity _ _ = ()"

definition cyclic_class_hierarchy :: unit 
where [code del]: "cyclic_class_hierarchy = ()"

code_abort cyclic_class_hierarchy

lemma check_acyclicity_code:
  "check_acyclicity mapping P =
   (let _ = 
     map (\<lambda>(C, D, _).
       if C = Object then () 
       else
         (case Mapping.lookup mapping D of 
            None \<Rightarrow> ()
          | Some Cs \<Rightarrow> if Cset.member Cs C then cyclic_class_hierarchy else ()))
       P
    in ())"
by simp

lemma tablulate_subcls_code [code]:
  "tabulate_subcls P = 
  (let cnames = map fst P;
       cnames' = map (fst \<circ> snd) P;
       mapping = Mapping.tabulate cnames (\<lambda>C. Cset.set (C # [D \<leftarrow> cnames'. subcls'' P C D]));
       _ = check_acyclicity mapping P
   in mapping
  )"
apply(auto simp add: tabulate_subcls_def Mapping.tabulate_def fun_eq_iff is_class_def o_def map_of_map2[simplified split_def])
apply(subst map_of_map2[simplified split_def])
apply(auto simp add: fun_eq_iff subcls''_eq_subcls map_of_map_K Cset.set_def Set.insert_code Collect_def dest: subclst_snd_classD elim: rtranclp_tranclpE)
apply(subst map_of_map2[simplified split_def])
apply(rule sym)
apply simp
apply(case_tac "map_of P x")
apply auto
done

subsubsection {* @{term Fields} *}

text {* Problem: Terminiert bei zyklischer Klassenhierarchie nicht! Existiert bereits in Jinja in Wohlgeformtheitspruefung: @{text wf_cdecl} ruft @{text wf_mdecl} vor Azyklizitaetstest auf, @{text wf_J_mdecl} braucht Typsystem, das wiederum Fields (ueber @{text sees_field}) benoetigt.
  Azyklizitaetstest vor Ausfuehrung schwierig, da dann Vorberechnung mit Wohlgeformtheitstest verschraenkt werden muesste.
  Loesungsmoeglichkeiten: zusaetzlicher Terminierungsparameter + list option als Rueckgabe mit Fallunterscheidung in der Regel
*}
inductive
  Fields' :: "'m cdecl list \<Rightarrow> cname \<Rightarrow> ((vname \<times> cname) \<times> (ty \<times> fmod)) list \<Rightarrow> bool"
for P :: "'m cdecl list"
where 
  rec:
  "\<lbrakk> map_of P C = Some(D,fs,ms); C \<noteq> Object; Fields' P D FDTs;
     FDTs' = map (\<lambda>(F,Tm). ((F,C),Tm)) fs @ FDTs \<rbrakk>
  \<Longrightarrow> Fields' P C FDTs'"
| Object:
  "\<lbrakk> map_of P Object = Some(D,fs,ms); FDTs = map (\<lambda>(F,T). ((F,Object),T)) fs \<rbrakk>
  \<Longrightarrow> Fields' P Object FDTs"

lemma Fields'_into_Fields:
  assumes "Fields' P C FDTs"
  shows "Program P \<turnstile> C has_fields FDTs"
using assms
by induct(auto intro: Fields.intros)

lemma Fields_into_Fields':
  assumes "Program P \<turnstile> C has_fields FDTs"
  shows "Fields' P C FDTs"
using assms
by induct(auto intro: Fields'.intros)

lemma Fields'_eq_Fields:
  "Fields' P = Fields (Program P)"
by(auto simp add: fun_eq_iff intro: Fields'_into_Fields Fields_into_Fields')

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  Fields' .

definition fields' :: "'m cdecl list \<Rightarrow> cname \<Rightarrow> ((vname \<times> cname) \<times> (ty \<times> fmod)) list"
where "fields' P C = (if \<exists>FDTs. Fields' P C FDTs then THE FDTs. Fields' P C FDTs else [])"

lemma eval_Fields'_conv:
  "Predicate.eval (Fields'_i_i_o P C) = Fields' P C"
by(auto intro: Fields'_i_i_oI elim: Fields'_i_i_oE intro!: ext)

lemma fields'_code [code]:
  "fields' P C = 
  (let FDTs = Fields'_i_i_o P C in if Predicate.holds (FDTs \<guillemotright>= (\<lambda>_. Predicate.single ())) then Predicate.the FDTs else [])"
by(auto simp add: fields'_def holds_eq Fields'_i_i_o_def intro: Fields'_i_i_oI Predicate.the_eqI[THEN sym])

lemma The_Fields [simp]:
  "P \<turnstile> C has_fields FDTs \<Longrightarrow> The (Fields P C) = FDTs"
by(auto dest: has_fields_fun)

lemma tabulate_sees_field_code [code]:
  "tabulate_sees_field P =
   Mapping.tabulate (map fst P) (\<lambda>C. assoc_list_to_mapping (map (\<lambda>((F, D), Tfm). (F, (D, Tfm))) (fields' P C)))"
apply(simp add: tabulate_sees_field_def tabulate_def is_class_def fields'_def Fields'_eq_Fields)
apply(rule ext)
apply auto
apply(simp add: o_def)
apply(subst map_of_map2[unfolded split_def])
apply simp
apply(auto simp add: assoc_list_to_mapping_def)
apply(rule ext)
apply auto
apply(simp_all add: sees_field_def)
apply auto
apply(simp_all add: Fields'_eq_Fields)
apply(drule (1) has_fields_fun, clarsimp)
apply(rule sym)
apply(rule ccontr)
apply(clarsimp)
apply(rule ext)
apply(clarsimp)
apply(clarsimp simp add: sees_field_def)
apply(clarsimp simp add: o_def)
apply(subst map_of_map2[simplified split_def])
apply(rule sym)
apply(auto)
apply(rule ccontr)
apply auto
done

subsubsection {* @{term "Methods" } *}

inductive Methods' :: "'m cdecl list \<Rightarrow> cname \<Rightarrow> (mname \<times> (ty list \<times> ty \<times> 'm) \<times> cname) list \<Rightarrow> bool"
  for P :: "'m cdecl list"
where 
  "\<lbrakk> map_of P Object = Some(D,fs,ms); Mm = map (\<lambda>(M, rest). (M, (rest, Object))) ms \<rbrakk>
   \<Longrightarrow> Methods' P Object Mm"
| "\<lbrakk> map_of P C = Some(D,fs,ms); C \<noteq> Object; Methods' P D Mm;
     Mm' = map (\<lambda>(M, rest). (M, (rest, C))) ms @ Mm \<rbrakk>
   \<Longrightarrow> Methods' P C Mm'"

lemma Methods'_into_Methods:
  assumes "Methods' P C Mm"
  shows "Program P \<turnstile> C sees_methods (map_of Mm)"
using assms
apply induct
apply(auto intro: Methods.intros simp add: o_def split_def)
apply(rule sees_methods_Object)
apply fastsimp
apply(rule ext)
apply(subst map_of_map2[unfolded split_def])
apply(simp add: o_def)

apply(rule sees_methods_rec)
apply fastsimp
apply simp
apply assumption
apply(rule ext)
apply(unfold map_add_def)
apply auto
apply(subst (asm) map_of_map2[unfolded split_def], simp)
apply(subst (asm) map_of_map2[unfolded split_def], simp)
apply(subst (asm) map_of_map2[unfolded split_def], simp)
apply(subst (asm) map_of_map2[unfolded split_def], simp)
apply(subst (asm) map_of_map2[unfolded split_def], simp)
apply(subst (asm) map_of_map2[unfolded split_def], simp)
done

lemma Methods_into_Methods':
  assumes "Program P \<turnstile> C sees_methods Mm"
  shows "\<exists>Mm'. Methods' P C Mm' \<and> Mm = map_of Mm'"
using assms
by induct(auto intro: Methods'.intros ext simp add: map_of_map2 map_add_def)

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  Methods'
.

definition methods' :: "'m cdecl list \<Rightarrow> cname \<Rightarrow> (mname \<times> (ty list \<times> ty \<times> 'm) \<times> cname) list"
where "methods' P C = (if \<exists>Mm. Methods' P C Mm then THE Mm. Methods' P C Mm else [])"

lemma methods'_code [code]:
  "methods' P C =
  (let Mm = Methods'_i_i_o P C
   in if Predicate.holds (Mm \<guillemotright>= (\<lambda>_. Predicate.single ())) then Predicate.the Mm else [])"
unfolding methods'_def
by(auto simp add: holds_eq Methods'_i_i_o_def Predicate.the_def)

lemma Methods'_fun:
  assumes "Methods' P C Mm"
  shows "Methods' P C Mm' \<Longrightarrow> Mm = Mm'"
using assms
apply(induct arbitrary: Mm')
 apply(fastsimp elim: Methods'.cases)
apply(rotate_tac -1)
apply(erule Methods'.cases)
 apply(fastsimp)
apply clarify
apply(simp)
done

lemma The_Methods' [simp]: "Methods' P C Mm \<Longrightarrow> The (Methods' P C) = Mm"
by(auto dest: Methods'_fun)

lemma methods_def2 [simp]: "Methods' P C Mm \<Longrightarrow> methods' P C = Mm"
by(auto simp add: methods'_def)

lemma tabulate_Method_code [code]:
  "tabulate_Method P =
   Mapping.tabulate (map fst P) (\<lambda>C. assoc_list_to_mapping (map (\<lambda>(M, (rest, D)). (M, D, rest)) (methods' P C)))"
apply(simp add: tabulate_Method_def tabulate_def o_def)
apply(rule ext)
apply auto
 apply(rule sym)
 apply(subst map_of_map2[unfolded split_def])
 apply simp
  apply(simp add: is_class_def)
 apply(simp add: assoc_list_to_mapping_def)
 apply(rule ext)
 apply(simp add: map_of_map2)
 apply(rule conjI)
  apply(clarsimp simp add: map_of_map2 Method_def)
  apply(drule Methods_into_Methods')
  apply clarsimp
  apply(simp add: split_def)
  apply(subst map_of_map2[unfolded split_def])
  apply simp
 apply clarify
 apply(clarsimp simp add: methods'_def)
 apply(frule Methods'_into_Methods)
 apply(clarsimp simp add: Method_def)
 apply(simp add: split_def)
 apply(subst map_of_map2[unfolded split_def])
 apply(fastsimp intro: ccontr)
apply(rule sym)
apply(simp add: map_of_eq_None_iff is_class_def)
apply(simp only: set_map[symmetric] map_map o_def fst_conv)
apply simp
done

text {* Merge modules TypeRel, Decl and TypeRelRefine to avoid cyclic modules *}

code_modulename SML
  TypeRel TypeRel
  TypeRelRefine TypeRel
  Decl TypeRel

code_modulename OCaml
  TypeRel TypeRel
  TypeRelRefine TypeRel
  Decl TypeRel

code_modulename Haskell
  TypeRel TypeRel
  TypeRelRefine TypeRel
  Decl TypeRel

ML {* @{code Program} *}

end