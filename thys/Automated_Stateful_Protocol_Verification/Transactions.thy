(*  Title:      Transactions.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section\<open>Protocol Transactions\<close>
theory Transactions
  imports
    Stateful_Protocol_Composition_and_Typing.Typed_Model
    Stateful_Protocol_Composition_and_Typing.Labeled_Stateful_Strands 
begin

subsection \<open>Definitions\<close>
datatype 'b prot_atom =
  is_Atom: Atom 'b
| Value
| SetType
| AttackType
| Bottom
| OccursSecType
| AbsValue

datatype ('a,'b,'c,'d) prot_fun =
  Fu (the_Fu: 'a)
| Set (the_Set: 'c)
| Val (the_Val: "nat")
| Abs (the_Abs: "'c set")
| Attack (the_Attack_label: "'d strand_label")
| Pair
| PubConst (the_PubConst_type: "'b prot_atom") nat
| OccursFact
| OccursSec

definition "is_Fun_Set t \<equiv> is_Fun t \<and> args t = [] \<and> is_Set (the_Fun t)"

definition "is_Fun_Attack t \<equiv> is_Fun t \<and> args t = [] \<and> is_Attack (the_Fun t)"

definition "is_PubConstValue f \<equiv> is_PubConst f \<and> the_PubConst_type f = Value"

abbreviation occurs where
  "occurs t \<equiv> Fun OccursFact [Fun OccursSec [], t]"

type_synonym ('a,'b,'c,'d) prot_term_type = "(('a,'b,'c,'d) prot_fun,'b prot_atom) term_type"

type_synonym ('a,'b,'c,'d) prot_var = "('a,'b,'c,'d) prot_term_type \<times> nat"

type_synonym ('a,'b,'c,'d) prot_term = "(('a,'b,'c,'d) prot_fun,('a,'b,'c,'d) prot_var) term"
type_synonym ('a,'b,'c,'d) prot_terms = "('a,'b,'c,'d) prot_term set"

type_synonym ('a,'b,'c,'d) prot_subst = "(('a,'b,'c,'d) prot_fun, ('a,'b,'c,'d) prot_var) subst"

type_synonym ('a,'b,'c,'d) prot_strand_step =
  "(('a,'b,'c,'d) prot_fun, ('a,'b,'c,'d) prot_var, 'd) labeled_stateful_strand_step"
type_synonym ('a,'b,'c,'d) prot_strand = "('a,'b,'c,'d) prot_strand_step list"
type_synonym ('a,'b,'c,'d) prot_constr = "('a,'b,'c,'d) prot_strand_step list"

(* TODO: rename transaction_decl *)
datatype ('a,'b,'c,'d) prot_transaction =
  Transaction
    (transaction_decl:    "unit \<Rightarrow> (('a,'b,'c,'d) prot_var \<times> 'a set) list")
    (transaction_fresh:   "('a,'b,'c,'d) prot_var list")
    (transaction_receive: "('a,'b,'c,'d) prot_strand")
    (transaction_checks:  "('a,'b,'c,'d) prot_strand")
    (transaction_updates: "('a,'b,'c,'d) prot_strand")
    (transaction_send:    "('a,'b,'c,'d) prot_strand")

definition transaction_strand where
  "transaction_strand T \<equiv>
    transaction_receive T@transaction_checks T@
    transaction_updates T@transaction_send T"

fun transaction_proj where
  "transaction_proj l (Transaction A B C D E F) = (
  let f = proj l
  in Transaction A B (f C) (f D) (f E) (f F))"

fun transaction_star_proj where
  "transaction_star_proj (Transaction A B C D E F) = (
  let f = filter has_LabelS
  in Transaction A B (f C) (f D) (f E) (f F))"

abbreviation fv_transaction where
  "fv_transaction T \<equiv> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)"

abbreviation bvars_transaction where
  "bvars_transaction T \<equiv> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)"

abbreviation vars_transaction where
  "vars_transaction T \<equiv> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)"

abbreviation trms_transaction where
  "trms_transaction T \<equiv> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)"

abbreviation setops_transaction where
  "setops_transaction T \<equiv> setops\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T))"

definition wellformed_transaction where
  "wellformed_transaction T \<equiv>
    list_all is_Receive (unlabel (transaction_receive T)) \<and>
    list_all is_Check_or_Assignment (unlabel (transaction_checks T)) \<and>
    list_all is_Update (unlabel (transaction_updates T)) \<and>
    list_all is_Send (unlabel (transaction_send T)) \<and>
    distinct (map fst (transaction_decl T ())) \<and>
    distinct (transaction_fresh T) \<and>
    set (transaction_fresh T) \<inter> fst ` set (transaction_decl T ()) = {} \<and>
    set (transaction_fresh T) \<inter> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) = {} \<and>
    set (transaction_fresh T) \<inter> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) = {} \<and>
    set (transaction_fresh T) \<inter> bvars_transaction T = {} \<and>
    fv_transaction T \<inter> bvars_transaction T = {} \<and>
    wf'\<^sub>s\<^sub>s\<^sub>t (fst ` set (transaction_decl T ()) \<union> set (transaction_fresh T))
          (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)))"

type_synonym ('a,'b,'c,'d) prot = "('a,'b,'c,'d) prot_transaction list"

abbreviation Var_Value_term ("\<langle>_: value\<rangle>\<^sub>v") where
  "\<langle>n: value\<rangle>\<^sub>v \<equiv> Var (Var Value, n)::('a,'b,'c,'d) prot_term"

abbreviation Var_SetType_term ("\<langle>_: SetType\<rangle>\<^sub>v") where
  "\<langle>n: SetType\<rangle>\<^sub>v \<equiv> Var (Var SetType, n)::('a,'b,'c,'d) prot_term"

abbreviation Var_AttackType_term ("\<langle>_: AttackType\<rangle>\<^sub>v") where
  "\<langle>n: AttackType\<rangle>\<^sub>v \<equiv> Var (Var AttackType, n)::('a,'b,'c,'d) prot_term"

abbreviation Var_Atom_term ("\<langle>_: _\<rangle>\<^sub>v") where
  "\<langle>n: a\<rangle>\<^sub>v \<equiv> Var (Var (Atom a), n)::('a,'b,'c,'d) prot_term"

abbreviation Var_Comp_Fu_term ("\<langle>_: _\<langle>_\<rangle>\<rangle>\<^sub>v") where
  "\<langle>n: f\<langle>T\<rangle>\<rangle>\<^sub>v \<equiv> Var (Fun (Fu f) T, n)::('a,'b,'c,'d) prot_term"

abbreviation TAtom_Atom_term ("\<langle>_\<rangle>\<^sub>\<tau>\<^sub>a") where
  "\<langle>a\<rangle>\<^sub>\<tau>\<^sub>a \<equiv> Var (Atom a)::('a,'b,'c,'d) prot_term_type"

abbreviation TComp_Fu_term ("\<langle>_ _\<rangle>\<^sub>\<tau>") where
  "\<langle>f T\<rangle>\<^sub>\<tau> \<equiv> Fun (Fu f) T::('a,'b,'c,'d) prot_term_type"

abbreviation Fun_Fu_term ("\<langle>_ _\<rangle>\<^sub>t") where
  "\<langle>f T\<rangle>\<^sub>t \<equiv> Fun (Fu f) T::('a,'b,'c,'d) prot_term"

abbreviation Fun_Fu_const_term ("\<langle>_\<rangle>\<^sub>c") where
  "\<langle>c\<rangle>\<^sub>c \<equiv> Fun (Fu c) []::('a,'b,'c,'d) prot_term"

abbreviation Fun_Set_const_term ("\<langle>_\<rangle>\<^sub>s") where
  "\<langle>f\<rangle>\<^sub>s \<equiv> Fun (Set f) []::('a,'b,'c,'d) prot_term"

abbreviation Fun_Set_composed_term ("\<langle>_\<langle>_\<rangle>\<rangle>\<^sub>s") where
  "\<langle>f\<langle>T\<rangle>\<rangle>\<^sub>s \<equiv> Fun (Set f) T::('a,'b,'c,'d) prot_term"

abbreviation Fun_Abs_const_term ("\<langle>_\<rangle>\<^sub>a\<^sub>b\<^sub>s") where
  "\<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s \<equiv> Fun (Abs a) []::('a,'b,'c,'d) prot_term"

abbreviation Fun_Attack_const_term ("attack\<langle>_\<rangle>") where
  "attack\<langle>n\<rangle> \<equiv> Fun (Attack n) []::('a,'b,'c,'d) prot_term"

abbreviation prot_transaction1 ("transaction\<^sub>1 _ _ new _ _ _") where
  "transaction\<^sub>1 (S1::('a,'b,'c,'d) prot_strand) S2 new (B::('a,'b,'c,'d) prot_term list) S3 S4
  \<equiv> Transaction (\<lambda>(). []) (map the_Var B) S1 S2 S3 S4"

abbreviation prot_transaction2 ("transaction\<^sub>2 _ _  _ _") where
  "transaction\<^sub>2 (S1::('a,'b,'c,'d) prot_strand) S2 S3 S4
  \<equiv> Transaction (\<lambda>(). []) [] S1 S2 S3 S4"


subsection \<open>Lemmata\<close>

lemma prot_atom_UNIV:
  "(UNIV::'b prot_atom set) = range Atom \<union> {Value, SetType, AttackType, Bottom, OccursSecType, AbsValue}"
proof -
  have "a \<in> range Atom \<or> a = Value \<or> a = SetType \<or> a = AttackType \<or>
        a = Bottom \<or> a = OccursSecType \<or> a = AbsValue"
    for a::"'b prot_atom"
    by (cases a) auto
  thus ?thesis by auto
qed

instance prot_atom::(finite) finite
by intro_classes (simp add: prot_atom_UNIV)

instantiation prot_atom::(enum) enum
begin
definition "enum_prot_atom == map Atom enum_class.enum@[Value, SetType, AttackType, Bottom, OccursSecType, AbsValue]"
definition "enum_all_prot_atom P == list_all P (map Atom enum_class.enum@[Value, SetType, AttackType, Bottom, OccursSecType, AbsValue])"
definition "enum_ex_prot_atom P == list_ex P (map Atom enum_class.enum@[Value, SetType, AttackType, Bottom, OccursSecType, AbsValue])"

instance
proof intro_classes
  have *: "set (map Atom (enum_class.enum::'a list)) = range Atom"
          "distinct (enum_class.enum::'a list)"
    using UNIV_enum enum_distinct by auto

  show "(UNIV::'a prot_atom set) = set enum_class.enum"
    using *(1) by (simp add: prot_atom_UNIV enum_prot_atom_def)

  have "set (map Atom enum_class.enum) \<inter> set [Value, SetType, AttackType, Bottom, OccursSecType, AbsValue] = {}" by auto
  moreover have "inj_on Atom (set (enum_class.enum::'a list))" unfolding inj_on_def by auto
  hence "distinct (map Atom (enum_class.enum::'a list))" by (metis *(2) distinct_map)
  ultimately show "distinct (enum_class.enum::'a prot_atom list)" by (simp add: enum_prot_atom_def)

  have "Ball UNIV P \<longleftrightarrow> Ball (range Atom) P \<and> Ball {Value, SetType, AttackType, Bottom, OccursSecType, AbsValue} P"
    for P::"'a prot_atom \<Rightarrow> bool"
    by (metis prot_atom_UNIV UNIV_I UnE) 
  thus "enum_class.enum_all P = Ball (UNIV::'a prot_atom set) P" for P
    using *(1) Ball_set[of "map Atom enum_class.enum" P]
    by (auto simp add: enum_all_prot_atom_def)

  have "Bex UNIV P \<longleftrightarrow> Bex (range Atom) P \<or> Bex {Value, SetType, AttackType, Bottom, OccursSecType, AbsValue} P"
    for P::"'a prot_atom \<Rightarrow> bool"
    by (metis prot_atom_UNIV UNIV_I UnE) 
  thus "enum_class.enum_ex P = Bex (UNIV::'a prot_atom set) P" for P
    using *(1) Bex_set[of "map Atom enum_class.enum" P]
    by (auto simp add: enum_ex_prot_atom_def)
qed
end

lemma wellformed_transaction_cases:
  assumes "wellformed_transaction T"
  shows 
      "(l,x) \<in> set (transaction_receive T) \<Longrightarrow> \<exists>t. x = receive\<langle>t\<rangle>" (is "?A \<Longrightarrow> ?A'")
      "(l,x) \<in> set (transaction_checks T) \<Longrightarrow>
              (\<exists>ac t s. x = \<langle>ac: t \<doteq> s\<rangle>) \<or> (\<exists>ac t s. x = \<langle>ac: t \<in> s\<rangle>) \<or>
              (\<exists>X F G. x = \<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>)"
          (is "?B \<Longrightarrow> ?B'")
      "(l,x) \<in> set (transaction_updates T) \<Longrightarrow>
              (\<exists>t s. x = insert\<langle>t,s\<rangle>) \<or> (\<exists>t s. x = delete\<langle>t,s\<rangle>)" (is "?C \<Longrightarrow> ?C'")
      "(l,x) \<in> set (transaction_send T) \<Longrightarrow> \<exists>t. x = send\<langle>t\<rangle>" (is "?D \<Longrightarrow> ?D'")
proof -
  have a:
      "list_all is_Receive (unlabel (transaction_receive T))"
      "list_all is_Check_or_Assignment (unlabel (transaction_checks T))"
      "list_all is_Update (unlabel (transaction_updates T))"
      "list_all is_Send (unlabel (transaction_send T))"
    using assms unfolding wellformed_transaction_def by metis+

  note b = Ball_set unlabel_in
  note c = stateful_strand_step.collapse

  show "?A \<Longrightarrow> ?A'" by (metis (mono_tags, lifting) a(1) b c(2))
  show "?B \<Longrightarrow> ?B'" by (metis (no_types, lifting) a(2) b c(3,6,7))
  show "?C \<Longrightarrow> ?C'" by (metis (mono_tags, lifting) a(3) b c(4,5))
  show "?D \<Longrightarrow> ?D'" by (metis (mono_tags, lifting) a(4) b c(1))
qed

lemma wellformed_transaction_unlabel_cases:
  assumes "wellformed_transaction T"
  shows 
      "x \<in> set (unlabel (transaction_receive T)) \<Longrightarrow> \<exists>t. x = receive\<langle>t\<rangle>" (is "?A \<Longrightarrow> ?A'")
      "x \<in> set (unlabel (transaction_checks T)) \<Longrightarrow>
              (\<exists>ac t s. x = \<langle>ac: t \<doteq> s\<rangle>) \<or> (\<exists>ac t s. x = \<langle>ac: t \<in> s\<rangle>) \<or>
              (\<exists>X F G. x = \<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>)"
        (is "?B \<Longrightarrow> ?B'")
      "x \<in> set (unlabel (transaction_updates T)) \<Longrightarrow>
              (\<exists>t s. x = insert\<langle>t,s\<rangle>) \<or> (\<exists>t s. x = delete\<langle>t,s\<rangle>)" (is "?C \<Longrightarrow> ?C'")
      "x \<in> set (unlabel (transaction_send T)) \<Longrightarrow> \<exists>t. x = send\<langle>t\<rangle>" (is "?D \<Longrightarrow> ?D'")
proof -
  have a:
      "list_all is_Receive (unlabel (transaction_receive T))"
      "list_all is_Check_or_Assignment (unlabel (transaction_checks T))"
      "list_all is_Update (unlabel (transaction_updates T))"
      "list_all is_Send (unlabel (transaction_send T))"
    using assms unfolding wellformed_transaction_def by metis+

  note b = Ball_set
  note c = stateful_strand_step.collapse

  show "?A \<Longrightarrow> ?A'" by (metis (mono_tags, lifting) a(1) b c(2))
  show "?B \<Longrightarrow> ?B'" by (metis (no_types, lifting) a(2) b c(3,6,7))
  show "?C \<Longrightarrow> ?C'" by (metis (mono_tags, lifting) a(3) b c(4,5))
  show "?D \<Longrightarrow> ?D'" by (metis (mono_tags, lifting) a(4) b c(1))
qed

lemma transaction_strand_subsets[simp]:
  "set (transaction_receive T) \<subseteq> set (transaction_strand T)"
  "set (transaction_checks T) \<subseteq> set (transaction_strand T)"
  "set (transaction_updates T) \<subseteq> set (transaction_strand T)"
  "set (transaction_send T) \<subseteq> set (transaction_strand T)"
  "set (unlabel (transaction_receive T)) \<subseteq> set (unlabel (transaction_strand T))"
  "set (unlabel (transaction_checks T)) \<subseteq> set (unlabel (transaction_strand T))"
  "set (unlabel (transaction_updates T)) \<subseteq> set (unlabel (transaction_strand T))"
  "set (unlabel (transaction_send T)) \<subseteq> set (unlabel (transaction_strand T))"
unfolding transaction_strand_def unlabel_def by force+

lemma transaction_strand_subst_subsets[simp]:
  "set (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<subseteq> set (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "set (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<subseteq> set (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "set (transaction_updates T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<subseteq> set (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "set (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<subseteq> set (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "set (unlabel (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<subseteq> set (unlabel (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
  "set (unlabel (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<subseteq> set (unlabel (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
  "set (unlabel (transaction_updates T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<subseteq> set (unlabel (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
  "set (unlabel (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<subseteq> set (unlabel (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
unfolding transaction_strand_def unlabel_def subst_apply_labeled_stateful_strand_def by force+

lemma transaction_strand_dual_unfold:
  defines "f \<equiv> \<lambda>S. dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S"
  shows "f (transaction_strand T) = 
         f (transaction_receive T)@f (transaction_checks T)@
         f (transaction_updates T)@f (transaction_send T)"
using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_append unfolding f_def transaction_strand_def by auto

lemma transaction_strand_unlabel_dual_unfold:
  defines "f \<equiv> \<lambda>S. unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S)"
  shows "f (transaction_strand T) = 
         f (transaction_receive T)@f (transaction_checks T)@
         f (transaction_updates T)@f (transaction_send T)"
using unlabel_append dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_append unfolding f_def transaction_strand_def by auto

lemma transaction_dual_subst_unfold:
  "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) =
    dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)@
    dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)@
    dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)@
    dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
by (simp add: transaction_strand_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_append subst_lsst_append)

lemma transaction_dual_subst_unlabel_unfold:
  "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) =
    unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))@
    unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))@
    unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))@
    unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
by (simp add: transaction_dual_subst_unfold unlabel_append)

lemma trms_transaction_unfold:
  "trms_transaction T =
      trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<union> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) \<union>
      trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T) \<union> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
by (metis trms\<^sub>s\<^sub>s\<^sub>t_append unlabel_append append_assoc transaction_strand_def)

lemma trms_transaction_subst_unfold:
  "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) =
      trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<union> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<union>
      trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<union> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
by (metis trms\<^sub>s\<^sub>s\<^sub>t_append unlabel_append append_assoc transaction_strand_def subst_lsst_append)

lemma vars_transaction_unfold:
  "vars_transaction T =
      vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) \<union>
      vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T) \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
by (metis vars\<^sub>s\<^sub>s\<^sub>t_append unlabel_append append_assoc transaction_strand_def)

lemma vars_transaction_subst_unfold:
  "vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) =
      vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<union>
      vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
by (metis vars\<^sub>s\<^sub>s\<^sub>t_append unlabel_append append_assoc transaction_strand_def subst_lsst_append)

lemma fv_transaction_unfold:
  "fv_transaction T =
      fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) \<union>
      fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
by (metis fv\<^sub>s\<^sub>s\<^sub>t_append unlabel_append append_assoc transaction_strand_def)

lemma fv_transaction_subst_unfold:
  "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) =
      fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<union>
      fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
by (metis fv\<^sub>s\<^sub>s\<^sub>t_append unlabel_append append_assoc transaction_strand_def subst_lsst_append)

lemma bvars_transaction_unfold:
  "bvars_transaction T =
      bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<union> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) \<union>
      bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T) \<union> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
by (metis bvars\<^sub>s\<^sub>s\<^sub>t_append unlabel_append append_assoc transaction_strand_def)

lemma bvars_transaction_subst_unfold:
  "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) =
      bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<union> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<union>
      bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<union> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
by (metis bvars\<^sub>s\<^sub>s\<^sub>t_append unlabel_append append_assoc transaction_strand_def subst_lsst_append)

lemma bvars_wellformed_transaction_unfold:
  assumes "wellformed_transaction T"
  shows "bvars_transaction T = bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T)" (is ?A)
    and "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) = {}" (is ?B)
    and "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T) = {}" (is ?C)
    and "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) = {}" (is ?D)
proof -
  have 0: "list_all is_Receive (unlabel (transaction_receive T))"
          "list_all is_Update (unlabel (transaction_updates T))"
          "list_all is_Send (unlabel (transaction_send T))"
    using assms unfolding wellformed_transaction_def by metis+

  have "filter is_NegChecks (unlabel (transaction_receive T)) = []"
       "filter is_NegChecks (unlabel (transaction_updates T)) = []"
       "filter is_NegChecks (unlabel (transaction_send T)) = []"
    using list_all_filter_nil[OF 0(1), of is_NegChecks]
          list_all_filter_nil[OF 0(2), of is_NegChecks]
          list_all_filter_nil[OF 0(3), of is_NegChecks]
          stateful_strand_step.distinct_disc(11,21,29,35,39,41)
    by blast+
  thus ?A ?B ?C ?D
    using bvars_transaction_unfold[of T]
          bvars\<^sub>s\<^sub>s\<^sub>t_NegChecks[of "unlabel (transaction_receive T)"]
          bvars\<^sub>s\<^sub>s\<^sub>t_NegChecks[of "unlabel (transaction_updates T)"]
          bvars\<^sub>s\<^sub>s\<^sub>t_NegChecks[of "unlabel (transaction_send T)"]
    by (metis bvars\<^sub>s\<^sub>s\<^sub>t_def UnionE emptyE list.set(1) list.simps(8) subsetI subset_Un_eq sup_commute)+
qed

lemma transaction_strand_memberD[dest]:
  assumes "x \<in> set (transaction_strand T)"
  shows "x \<in> set (transaction_receive T) \<or> x \<in> set (transaction_checks T) \<or>
         x \<in> set (transaction_updates T) \<or> x \<in> set (transaction_send T)"
using assms by (simp add: transaction_strand_def)

lemma transaction_strand_unlabel_memberD[dest]:
  assumes "x \<in> set (unlabel (transaction_strand T))"
  shows "x \<in> set (unlabel (transaction_receive T)) \<or> x \<in> set (unlabel (transaction_checks T)) \<or>
         x \<in> set (unlabel (transaction_updates T)) \<or> x \<in> set (unlabel (transaction_send T))"
using assms by (simp add: unlabel_def transaction_strand_def)

lemma wellformed_transaction_strand_memberD[dest]:
  assumes "wellformed_transaction T" and "(l,x) \<in> set (transaction_strand T)"
  shows
    "x = receive\<langle>ts\<rangle> \<Longrightarrow> (l,x) \<in> set (transaction_receive T)" (is "?A \<Longrightarrow> ?A'")
    "x = select\<langle>t,s\<rangle> \<Longrightarrow> (l,x) \<in> set (transaction_checks T)" (is "?B \<Longrightarrow> ?B'")
    "x = \<langle>t == s\<rangle> \<Longrightarrow> (l,x) \<in> set (transaction_checks T)" (is "?C \<Longrightarrow> ?C'")
    "x = \<langle>t in s\<rangle> \<Longrightarrow> (l,x) \<in> set (transaction_checks T)" (is "?D \<Longrightarrow> ?D'")
    "x = \<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>  \<Longrightarrow> (l,x) \<in> set (transaction_checks T)" (is "?E \<Longrightarrow> ?E'")
    "x = insert\<langle>t,s\<rangle> \<Longrightarrow> (l,x) \<in> set (transaction_updates T)" (is "?F \<Longrightarrow> ?F'")
    "x = delete\<langle>t,s\<rangle> \<Longrightarrow> (l,x) \<in> set (transaction_updates T)" (is "?G \<Longrightarrow> ?G'")
    "x = send\<langle>ts\<rangle> \<Longrightarrow> (l,x) \<in> set (transaction_send T)" (is "?H \<Longrightarrow> ?H'")
    "x = \<langle>ac: t \<doteq> s\<rangle> \<Longrightarrow> (l,x) \<in> set (transaction_checks T)" (is "?I \<Longrightarrow> ?I'")
    "x = \<langle>ac: t \<in> s\<rangle> \<Longrightarrow> (l,x) \<in> set (transaction_checks T)" (is "?J \<Longrightarrow> ?J'")
proof -
  have "(l,x) \<in> set (transaction_receive T) \<or> (l,x) \<in> set (transaction_checks T) \<or>
        (l,x) \<in> set (transaction_updates T) \<or> (l,x) \<in> set (transaction_send T)"
    using assms(2) by auto
  thus "?A \<Longrightarrow> ?A'" "?B \<Longrightarrow> ?B'" "?C \<Longrightarrow> ?C'" "?D \<Longrightarrow> ?D'" "?E \<Longrightarrow> ?E'"
       "?F \<Longrightarrow> ?F'" "?G \<Longrightarrow> ?G'" "?H \<Longrightarrow> ?H'" "?I \<Longrightarrow> ?I'" "?J \<Longrightarrow> ?J'"
    using wellformed_transaction_cases[OF assms(1)] by fast+
qed

lemma wellformed_transaction_strand_unlabel_memberD[dest]:
  assumes "wellformed_transaction T" and "x \<in> set (unlabel (transaction_strand T))"
  shows
    "x = receive\<langle>ts\<rangle> \<Longrightarrow> x \<in> set (unlabel (transaction_receive T))" (is "?A \<Longrightarrow> ?A'")
    "x = select\<langle>t,s\<rangle> \<Longrightarrow> x \<in> set (unlabel (transaction_checks T))" (is "?B \<Longrightarrow> ?B'")
    "x = \<langle>t == s\<rangle> \<Longrightarrow> x \<in> set (unlabel (transaction_checks T))" (is "?C \<Longrightarrow> ?C'")
    "x = \<langle>t in s\<rangle> \<Longrightarrow> x \<in> set (unlabel (transaction_checks T))" (is "?D \<Longrightarrow> ?D'")
    "x = \<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>  \<Longrightarrow> x \<in> set (unlabel (transaction_checks T))" (is "?E \<Longrightarrow> ?E'")
    "x = insert\<langle>t,s\<rangle> \<Longrightarrow> x \<in> set (unlabel (transaction_updates T))" (is "?F \<Longrightarrow> ?F'")
    "x = delete\<langle>t,s\<rangle> \<Longrightarrow> x \<in> set (unlabel (transaction_updates T))" (is "?G \<Longrightarrow> ?G'")
    "x = send\<langle>ts\<rangle> \<Longrightarrow> x \<in> set (unlabel (transaction_send T))" (is "?H \<Longrightarrow> ?H'")
    "x = \<langle>ac: t \<doteq> s\<rangle> \<Longrightarrow> x \<in> set (unlabel (transaction_checks T))" (is "?I \<Longrightarrow> ?I'")
    "x = \<langle>ac: t \<in> s\<rangle> \<Longrightarrow> x \<in> set (unlabel (transaction_checks T))" (is "?J \<Longrightarrow> ?J'")
proof -
  have "x \<in> set (unlabel (transaction_receive T)) \<or> x \<in> set (unlabel (transaction_checks T)) \<or>
        x \<in> set (unlabel (transaction_updates T)) \<or> x \<in> set (unlabel (transaction_send T))"
    using assms(2) by auto
  thus "?A \<Longrightarrow> ?A'" "?B \<Longrightarrow> ?B'" "?C \<Longrightarrow> ?C'" "?D \<Longrightarrow> ?D'" "?E \<Longrightarrow> ?E'"
       "?F \<Longrightarrow> ?F'" "?G \<Longrightarrow> ?G'" "?H \<Longrightarrow> ?H'" "?I \<Longrightarrow> ?I'" "?J \<Longrightarrow> ?J'"
    using wellformed_transaction_unlabel_cases[OF assms(1)] by fast+
qed

lemma wellformed_transaction_send_receive_trm_cases:
  assumes T: "wellformed_transaction T"
  shows "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<Longrightarrow> \<exists>ts. t \<in> set ts \<and> receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_receive T))"
    and "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<Longrightarrow> \<exists>ts. t \<in> set ts \<and> send\<langle>ts\<rangle> \<in> set (unlabel (transaction_send T))"
using wellformed_transaction_unlabel_cases(1,4)[OF T]
      trms\<^sub>s\<^sub>s\<^sub>t_in[of t "unlabel (transaction_receive T)"]
      trms\<^sub>s\<^sub>s\<^sub>t_in[of t "unlabel (transaction_send T)"]
by fastforce+

lemma wellformed_transaction_send_receive_subst_trm_cases:
  assumes T: "wellformed_transaction T"
  shows "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> \<Longrightarrow> \<exists>ts. t \<in> set ts \<and> receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
    and "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> \<Longrightarrow> \<exists>ts. t \<in> set ts \<and> send\<langle>ts\<rangle> \<in> set (unlabel (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
proof -
  assume "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
  then obtain s where s: "s \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)" "t = s \<cdot> \<theta>"
    by blast
  hence "\<exists>ts. s \<in> set ts \<and> receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_receive T))"
    using wellformed_transaction_send_receive_trm_cases(1)[OF T] by simp
  thus "\<exists>ts. t \<in> set ts \<and> receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
    using s(2) unlabel_subst[of _ \<theta>] subst_set_map[of s _ \<theta>]
          stateful_strand_step_subst_inI(2)[of _ "unlabel (transaction_receive T)" \<theta>]
    by metis
next
  assume "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
  then obtain s where s: "s \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" "t = s \<cdot> \<theta>"
    by blast
  hence "\<exists>ts. s \<in> set ts \<and> send\<langle>ts\<rangle> \<in> set (unlabel (transaction_send T))"
    using wellformed_transaction_send_receive_trm_cases(2)[OF T] by simp
  thus "\<exists>ts. t \<in> set ts \<and> send\<langle>ts\<rangle> \<in> set (unlabel (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
    using s(2) unlabel_subst[of _ \<theta>] subst_set_map[of s _ \<theta>]
          stateful_strand_step_subst_inI(1)[of _ "unlabel (transaction_send T)" \<theta>]
    by metis
qed

lemma wellformed_transaction_send_receive_fv_subset:
  assumes T: "wellformed_transaction T"
  shows "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<Longrightarrow> fv t \<subseteq> fv_transaction T" (is "?A \<Longrightarrow> ?A'")
    and "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<Longrightarrow> fv t \<subseteq> fv_transaction T" (is "?B \<Longrightarrow> ?B'")
proof -
  let ?P = "\<exists>ts. t \<in> set ts \<and> receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_strand T))"
  let ?Q = "\<exists>ts. t \<in> set ts \<and> send\<langle>ts\<rangle> \<in> set (unlabel (transaction_strand T))"

  have *: "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<Longrightarrow> ?P" "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<Longrightarrow> ?Q"
    using wellformed_transaction_send_receive_trm_cases[OF T, of t]
    unfolding transaction_strand_def by force+
  
  show "?A \<Longrightarrow> ?A'" using *(1) by (induct "transaction_strand T") (simp, force)
  show "?B \<Longrightarrow> ?B'" using *(2) by (induct "transaction_strand T") (simp, force)
qed

lemma dual_wellformed_transaction_ident_cases[dest]:
  "list_all is_Assignment (unlabel S) \<Longrightarrow> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S = S"
  "list_all is_Check (unlabel S) \<Longrightarrow> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S = S"
  "list_all is_Update (unlabel S) \<Longrightarrow> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S = S"
proof (induction S)
  case (Cons s S)
  obtain l x where s: "s = (l,x)" by moura
  { case 1 thus ?case using Cons s unfolding unlabel_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by (cases x) auto }
  { case 2 thus ?case using Cons s unfolding unlabel_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by (cases x) auto }
  { case 3 thus ?case using Cons s unfolding unlabel_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by (cases x) auto }
qed simp_all

lemma wellformed_transaction_wf\<^sub>s\<^sub>s\<^sub>t:
  fixes T::"('a, 'b, 'c, 'd) prot_transaction"
  assumes T: "wellformed_transaction T"
  shows "wf'\<^sub>s\<^sub>s\<^sub>t (fst ` set (transaction_decl T ()) \<union> set (transaction_fresh T))
               (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)))"
    and "fv_transaction T \<inter> bvars_transaction T = {}"
using T unfolding wellformed_transaction_def by simp_all

lemma dual_wellformed_transaction_ident_cases'[dest]:
  assumes "wellformed_transaction T"
  shows "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) = transaction_checks T" (is ?A)
        "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T) = transaction_updates T" (is ?B)
proof -
  have "list_all is_Check_or_Assignment (unlabel (transaction_checks T))"
       "list_all is_Update (unlabel (transaction_updates T))"
    using assms is_Check_or_Assignment_iff unfolding wellformed_transaction_def by auto
  thus ?A ?B
    using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_list_all_same(9)[of "transaction_checks T"]
          dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_list_all_same(8)[of "transaction_updates T"]
    by (blast, blast)
qed

lemma dual_transaction_strand:
  assumes "wellformed_transaction T"
  shows "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) =
         dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)@transaction_checks T@
         transaction_updates T@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
using dual_wellformed_transaction_ident_cases'[OF assms] dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_append
unfolding transaction_strand_def by metis

lemma dual_unlabel_transaction_strand:
  assumes "wellformed_transaction T"
  shows "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)) =
         (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)))@(unlabel (transaction_checks T))@
         (unlabel (transaction_updates T))@(unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)))"
using dual_transaction_strand[OF assms] by (simp add: unlabel_def)

lemma dual_transaction_strand_subst:
  assumes "wellformed_transaction T"
  shows "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) =
          (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)@transaction_checks T@
          transaction_updates T@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>"
proof -
  have "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>"
    using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst by metis
  thus ?thesis using dual_transaction_strand[OF assms] by argo
qed

lemma dual_transaction_ik_is_transaction_send:
  assumes "wellformed_transaction T"
  shows "ik\<^sub>s\<^sub>s\<^sub>t (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T))) = trms\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_send T))"
    (is "?A = ?B")
proof -
  { fix t assume "t \<in> ?A"
    then obtain ts where ts:
        "t \<in> set ts" "receive\<langle>ts\<rangle> \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)))"
      by (auto simp add: ik\<^sub>s\<^sub>s\<^sub>t_def)
    hence *: "send\<langle>ts\<rangle> \<in> set (unlabel (transaction_strand T))"
      using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(1) by metis
    have "t \<in> ?B"
      using ts(1) wellformed_transaction_strand_unlabel_memberD(8)[OF assms *, of ts] by force
  } moreover {
    fix t assume "t \<in> ?B"
    then obtain ts where ts:
        "t \<in> set ts" "send\<langle>ts\<rangle> \<in> set (unlabel (transaction_send T))"
      using wellformed_transaction_unlabel_cases(4)[OF assms] by fastforce
    hence "receive\<langle>ts\<rangle> \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)))"
      using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(1) by metis
    hence "receive\<langle>ts\<rangle> \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)))"
      using dual_unlabel_transaction_strand[OF assms] by simp 
    hence "t \<in> ?A" using ts(1) by (auto simp add: ik\<^sub>s\<^sub>s\<^sub>t_def)
  } ultimately show "?A = ?B" by auto
qed

lemma dual_transaction_ik_is_transaction_send':
  fixes \<delta>::"('a,'b,'c,'d) prot_subst"
  assumes "wellformed_transaction T"
  shows "ik\<^sub>s\<^sub>s\<^sub>t (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)))  =
         trms\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_send T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>" (is "?A = ?B")
using dual_transaction_ik_is_transaction_send[OF assms]
      subst_lsst_unlabel[of "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T)" \<delta>]
      ik\<^sub>s\<^sub>s\<^sub>t_subst[of "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T))" \<delta>]
      dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst[of "transaction_strand T" \<delta>]
by auto

lemma db\<^sub>s\<^sub>s\<^sub>t_transaction_prefix_eq:
  assumes T: "wellformed_transaction T"
    and S: "prefix S (transaction_receive T@transaction_checks T)"
  shows "db\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>))"
proof -
  let ?T1 = "transaction_receive T"
  let ?T2 = "transaction_checks T"

  have *: "prefix (unlabel S) (unlabel (?T1@?T2))" using S prefix_unlabel by blast

  have "list_all is_Receive (unlabel ?T1)"
       "list_all is_Check_or_Assignment (unlabel ?T2)"
    using T by (simp_all add: wellformed_transaction_def)
  hence "\<forall>b \<in> set (unlabel ?T1). \<not>is_Insert b \<and> \<not>is_Delete b"
        "\<forall>b \<in> set (unlabel ?T2). \<not>is_Insert b \<and> \<not>is_Delete b"
    by (metis (mono_tags, lifting) Ball_set stateful_strand_step.distinct_disc(16,18),
        metis (mono_tags, lifting) Ball_set stateful_strand_step.distinct_disc(24,26,33,35,37,39))
  hence "\<forall>b \<in> set (unlabel (?T1@?T2)). \<not>is_Insert b \<and> \<not>is_Delete b"
    by (auto simp add: unlabel_def)
  hence "\<forall>b \<in> set (unlabel S). \<not>is_Insert b \<and> \<not>is_Delete b"
    using * unfolding prefix_def by fastforce
  hence "\<forall>b \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>). \<not>is_Insert b \<and> \<not>is_Delete b"
  proof (induction S)
    case (Cons a S)
    then obtain l b where "a = (l,b)" by (metis surj_pair)
    thus ?case
      using Cons unfolding dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def unlabel_def subst_apply_stateful_strand_def
      by (cases b) auto
  qed simp
  hence **: "\<forall>b \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>))). \<not>is_Insert b \<and> \<not>is_Delete b"
    by (metis dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_unlabel)

  show ?thesis 
    using db\<^sub>s\<^sub>s\<^sub>t_no_upd_append[OF **] unlabel_append
    unfolding db\<^sub>s\<^sub>s\<^sub>t_def by metis
qed

lemma db\<^sub>l\<^sub>s\<^sub>s\<^sub>t_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_set_ex:
   assumes "d \<in> set (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<I> D)"
    "\<forall>t u. insert\<langle>t,u\<rangle> \<in> set (unlabel A) \<longrightarrow> (\<exists>s. u = Fun (Set s) [])"
    "\<forall>t u. delete\<langle>t,u\<rangle> \<in> set (unlabel A) \<longrightarrow> (\<exists>s. u = Fun (Set s) [])"
    "\<forall>d \<in> set D. \<exists>s. snd d = Fun (Set s) []"
  shows "\<exists>s. snd d = Fun (Set s) []"
  using assms
proof (induction A arbitrary: D)
  case (Cons a A)
  obtain l b where a: "a = (l,b)" by (metis surj_pair)

  have 1: "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) = receive\<langle>ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle>#unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
    when "b = send\<langle>ts\<rangle>" for ts
    by (simp add: a that subst_lsst_unlabel_cons)

  have 2: "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) = send\<langle>ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle>#unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
    when "b = receive\<langle>ts\<rangle>" for ts
    by (simp add: a that subst_lsst_unlabel_cons)

  have 3: "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) = (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)#unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
    when "\<nexists>ts. b = send\<langle>ts\<rangle> \<or> b = receive\<langle>ts\<rangle>"
    using a that dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_Cons subst_lsst_unlabel_cons[of l b]
    by (cases b) auto

  show ?case using 1 2 3 a Cons by (cases b) fastforce+
qed simp

lemma is_Fun_SetE[elim]:
  assumes t: "is_Fun_Set t"
  obtains s where "t = Fun (Set s) []"
proof (cases t)
  case (Fun f T)
  then obtain s where "f = Set s" using t unfolding is_Fun_Set_def by (cases f) moura+
  moreover have "T = []" using Fun t unfolding is_Fun_Set_def by (cases T) auto
  ultimately show ?thesis using Fun that by fast
qed (use t is_Fun_Set_def in fast)

lemma Fun_Set_InSet_iff:
  "(u = \<langle>a: Var x \<in> Fun (Set s) []\<rangle>) \<longleftrightarrow>
   (is_InSet u \<and> is_Var (the_elem_term u) \<and> is_Fun_Set (the_set_term u) \<and>
    the_Set (the_Fun (the_set_term u)) = s \<and> the_Var (the_elem_term u) = x \<and> the_check u = a)"
  (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B" unfolding is_Fun_Set_def by auto

  assume B: ?B
  thus ?A
  proof (cases u)
    case (InSet b t t')
    hence "b = a" "t = Var x" "t' = Fun (Set s) []"
      using B by (simp, fastforce, fastforce)
    thus ?thesis using InSet by fast
  qed auto
qed

lemma Fun_Set_NotInSet_iff:
  "(u = \<langle>Var x not in Fun (Set s) []\<rangle>) \<longleftrightarrow>
   (is_NegChecks u \<and> bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p u = [] \<and> the_eqs u = [] \<and> length (the_ins u) = 1 \<and>
    is_Var (fst (hd (the_ins u))) \<and> is_Fun_Set (snd (hd (the_ins u)))) \<and>
    the_Set (the_Fun (snd (hd (the_ins u)))) = s \<and> the_Var (fst (hd (the_ins u))) = x"
  (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B" unfolding is_Fun_Set_def by auto

  assume B: ?B
  show ?A
  proof (cases u)
    case (NegChecks X F F')
    hence "X = []" "F = []"
      using B by auto
    moreover have "fst (hd (the_ins u)) = Var x" "snd (hd (the_ins u)) = Fun (Set s) []"
      using B is_Fun_SetE[of "snd (hd (the_ins u))"]
      by (force, fastforce)
    hence "F' = [(Var x, Fun (Set s) [])]"
      using NegChecks B by (cases "the_ins u") auto
    ultimately show ?thesis using NegChecks by fast
  qed (use B in auto)
qed

lemma is_Fun_Set_exi: "is_Fun_Set x \<longleftrightarrow> (\<exists>s. x = Fun (Set s) [])"
by (metis prot_fun.collapse(2) term.collapse(2) prot_fun.disc(11) term.disc(2)
          term.sel(2,4) is_Fun_Set_def un_Fun1_def)

lemma is_Fun_Set_subst:
  assumes "is_Fun_Set S'"
  shows "is_Fun_Set (S' \<cdot> \<sigma>)"
using assms by (fastforce simp add: is_Fun_Set_def)

lemma is_Update_in_transaction_updates:
  assumes tu: "is_Update t"
  assumes t: "t \<in> set (unlabel (transaction_strand TT))"
  assumes vt: "wellformed_transaction TT"
  shows "t \<in> set (unlabel (transaction_updates TT))"
using t tu vt unfolding transaction_strand_def wellformed_transaction_def list_all_iff
by (auto simp add: unlabel_append)

lemma transaction_proj_member:
  assumes "T \<in> set P"
  shows "transaction_proj n T \<in> set (map (transaction_proj n) P)"
using assms by simp

lemma transaction_strand_proj:
  "transaction_strand (transaction_proj n T) = proj n (transaction_strand T)"
proof -
  obtain A B C D E F where "T = Transaction A B C D E F" by (cases T) simp
  thus ?thesis
    using transaction_proj.simps[of n A B C D E F]
    unfolding transaction_strand_def proj_def Let_def by auto
qed

lemma transaction_proj_decl_eq:
  "transaction_decl (transaction_proj n T) = transaction_decl T"
proof -
  obtain A B C D E F where "T = Transaction A B C D E F" by (cases T) simp
  thus ?thesis
    using transaction_proj.simps[of n A B C D E F]
    unfolding proj_def Let_def by auto
qed

lemma transaction_proj_fresh_eq:
  "transaction_fresh (transaction_proj n T) = transaction_fresh T"
proof -
  obtain A B C D E F where "T = Transaction A B C D E F" by (cases T) simp
  thus ?thesis
    using transaction_proj.simps[of n A B C D E F]
    unfolding proj_def Let_def by auto
qed

lemma transaction_proj_trms_subset:
  "trms_transaction (transaction_proj n T) \<subseteq> trms_transaction T"
proof -
  obtain A B C D E F where "T = Transaction A B C D E F" by (cases T) simp
  thus ?thesis
    using transaction_proj.simps[of n A B C D E F] trms\<^sub>s\<^sub>s\<^sub>t_proj_subset(1)[of n]
    unfolding transaction_fresh_def Let_def transaction_strand_def by auto
qed

lemma transaction_proj_vars_subset:
  "vars_transaction (transaction_proj n T) \<subseteq> vars_transaction T"
proof -
  obtain A B C D E F where "T = Transaction A B C D E F" by (cases T) simp
  thus ?thesis
    using transaction_proj.simps[of n A B C D E F]
          sst_vars_proj_subset(3)[of n "transaction_strand T"]
    unfolding transaction_fresh_def Let_def transaction_strand_def by simp
qed

lemma transaction_proj_labels:
  fixes T::"('a,'b,'c,'d) prot_transaction"
  shows "list_all (\<lambda>a. has_LabelN l a \<or> has_LabelS a) (transaction_strand (transaction_proj l T))"
proof -
  define h where "h \<equiv> \<lambda>a::('a,'b,'c,'d) prot_strand_step. has_LabelN l a \<or> has_LabelS a"
  let ?f = "filter h"
  let ?g = "list_all h"

  obtain T1 T2 T3 T4 T5 T6 where T: "T = Transaction T1 T2 T3 T4 T5 T6" by (cases T) simp

  note 0 = transaction_proj.simps[unfolded Let_def, of l T1 T2 T3 T4 T5 T6]

  show ?thesis using T 0 unfolding list_all_iff proj_def by auto
qed

lemma transaction_proj_ident_iff:
  fixes T::"('a,'b,'c,'d) prot_transaction"
  shows "list_all (\<lambda>a. has_LabelN l a \<or> has_LabelS a) (transaction_strand T) \<longleftrightarrow>
         transaction_proj l T = T"
    (is "?A \<longleftrightarrow> ?B")
proof
  obtain T1 T2 T3 T4 T5 T6 where T: "T = Transaction T1 T2 T3 T4 T5 T6" by (cases T) simp
  hence "transaction_strand T = T3@T4@T5@T6" unfolding transaction_strand_def by simp
  thus "?A \<Longrightarrow> ?B"
    using T transaction_proj.simps[unfolded Let_def, of l T1 T2 T3 T4 T5 T6]
    unfolding list_all_iff proj_def by auto

  show "?B \<Longrightarrow> ?A" using transaction_proj_labels[of l T] by presburger
qed

lemma transaction_proj_idem:
  fixes T::"('a,'b,'c,'d) prot_transaction"
  shows "transaction_proj l (transaction_proj l T) = transaction_proj l T"
by (meson transaction_proj_ident_iff transaction_proj_labels)

lemma transaction_proj_ball_subst:
  assumes
    "set Ps = (\<lambda>n. map (transaction_proj n) P) ` set L"
    "\<forall>p \<in> set Ps. Q p"
  shows "\<forall>l \<in> set L. Q (map (transaction_proj l) P)"
using assms by auto

lemma transaction_star_proj_has_star_labels:
  "list_all has_LabelS (transaction_strand (transaction_star_proj T))"
proof -
  let ?f = "filter has_LabelS"

  obtain T1 T2 T3 T4 T5 T6 where T: "T = Transaction T1 T2 T3 T4 T5 T6" by (cases T) simp
  hence T': "transaction_strand (transaction_star_proj T) = ?f T3@?f T4@?f T5@?f T6"
    using transaction_star_proj.simps[unfolded Let_def, of T1 T2 T3 T4 T5 T6]
    unfolding transaction_strand_def by auto

  show ?thesis using Ball_set unfolding T' by fastforce
qed

lemma transaction_star_proj_ident_iff:
  "list_all has_LabelS (transaction_strand T) \<longleftrightarrow> transaction_star_proj T = T" (is "?A \<longleftrightarrow> ?B")
proof
  obtain T1 T2 T3 T4 T5 T6 where T: "T = Transaction T1 T2 T3 T4 T5 T6" by (cases T) simp
  hence T': "transaction_strand T = T3@T4@T5@T6" unfolding transaction_strand_def by simp

  show "?A \<Longrightarrow> ?B" using T T' unfolding list_all_iff by auto
  show "?B \<Longrightarrow> ?A" using transaction_star_proj_has_star_labels[of T] by auto
qed

lemma transaction_star_proj_negates_transaction_proj:
  "transaction_star_proj (transaction_proj l T) = transaction_star_proj T" (is "?A l T")
  "k \<noteq> l \<Longrightarrow> transaction_proj k (transaction_proj l T) = transaction_star_proj T" (is "?B \<Longrightarrow> ?B'")
proof -
  show "?A l T" for l T
  proof -
    obtain T1 T2 T3 T4 T5 T6 where T: "T = Transaction T1 T2 T3 T4 T5 T6" by (cases T) simp
    thus ?thesis
      by (metis dbproj_def transaction_proj.simps transaction_star_proj.simps proj_dbproj(2))
  qed
  thus "?B \<Longrightarrow> ?B'"
    by (metis (no_types) has_LabelS_proj_iff_not_has_LabelN proj_elims_label
        transaction_star_proj_ident_iff transaction_strand_proj)
qed

lemma transaction_updates_send_ex_iff:
  fixes T::"('a,'b,'c,'d) prot_transaction"
  assumes "list_all is_Receive (unlabel (transaction_receive T))"
          "list_all is_Check_or_Assignment (unlabel (transaction_checks T))"
          "list_all is_Update (unlabel (transaction_updates T))"
          "list_all is_Send (unlabel (transaction_send T))"
  shows "transaction_updates T \<noteq> [] \<or> transaction_send T \<noteq> [] \<longleftrightarrow>
         list_ex (\<lambda>a. is_Send (snd a) \<or> is_Update (snd a)) (transaction_strand T)"
proof -
  define f where "f \<equiv> \<lambda>a::('a,'b,'c,'d) prot_strand_step. is_Send (snd a) \<or> is_Update (snd a)"

  have 0: "list_all (\<lambda>a. \<not>(f a)) (transaction_receive T)"
          "list_all (\<lambda>a. \<not>(f a)) (transaction_checks T)"
          "list_all (\<lambda>a. (f a)) (transaction_updates T)"
          "list_all (\<lambda>a. (f a)) (transaction_send T)"
    using assms unfolding list_all_iff unlabel_def f_def by auto

  have 1:
      "list_ex f (transaction_strand T) \<longleftrightarrow>
       list_ex f (transaction_updates T) \<or> list_ex f (transaction_send T)"
    using 0 unfolding list_all_iff list_ex_iff transaction_strand_def by auto

  have 2: "A \<noteq> [] \<longleftrightarrow> list_ex f A" when "list_all f A" for A
    using that by (induct A) auto

  thus ?thesis
    using 1 2[OF 0(3)] 2[OF 0(4)] unfolding list_all_iff list_ex_iff f_def[symmetric] by meson
qed

end
