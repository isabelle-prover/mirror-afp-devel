(*  Title:       Category theory using Isar and Locales
    Author:      Greg O'Keefe, June, July, August 2003

Functors: Define functors and prove a trivial example.
*)

header {* Functors *}

theory Functors
imports Cat
begin

subsection {* Definitions *}

record ('o1,'a1,'o2,'a2) functor =
  om :: "'o1 \<Rightarrow> 'o2"
  am :: "'a1 \<Rightarrow> 'a2"

abbreviation
  om_syn  ("_ \<^sub>\<o>" [81]) where
  "F\<^sub>\<o> \<equiv> om F"

abbreviation
  am_syn  ("_ \<^sub>\<a>" [81]) where
  "F\<^sub>\<a> \<equiv> am F"

locale two_cats = AA: category AA + BB: category BB
    for AA (structure) and BB (structure) + 
  constrains AA :: "('o1,'a1,'m1)category_scheme"
  constrains BB :: "('o2,'a2,'m2)category_scheme"
  fixes preserves_dom  ::  "('o1,'a1,'o2,'a2)functor \<Rightarrow> bool"
  and  preserves_cod  ::  "('o1,'a1,'o2,'a2)functor \<Rightarrow> bool"
  and  preserves_id  ::  "('o1,'a1,'o2,'a2)functor \<Rightarrow> bool"
  and  preserves_comp  ::  "('o1,'a1,'o2,'a2)functor \<Rightarrow> bool"
  defines "preserves_dom G \<equiv> 
  \<forall>f\<in>Ar\<^sub>1. G\<^sub>\<o> (Dom\<^sub>1 f) = Dom\<^sub>2 (G\<^sub>\<a> f)"
  and "preserves_cod G \<equiv> 
  \<forall>f\<in>Ar\<^sub>1. G\<^sub>\<o> (Cod\<^sub>1 f) = Cod\<^sub>2 (G\<^sub>\<a> f)"
  and "preserves_id G \<equiv> 
  \<forall>A\<in>Ob\<^sub>1. G\<^sub>\<a> (Id\<^sub>1 A) = Id\<^sub>2 (G\<^sub>\<o> A)"
  and "preserves_comp G \<equiv> 
  \<forall>f\<in>Ar\<^sub>1. \<forall>g\<in>Ar\<^sub>1. Cod\<^sub>1 f = Dom\<^sub>1 g \<longrightarrow> G\<^sub>\<a> (g \<bullet>\<^sub>1 f) = (G\<^sub>\<a> g) \<bullet>\<^sub>2 (G\<^sub>\<a> f)"

locale functor = two_cats +
  fixes F (structure)
  assumes F_preserves_arrows: "F\<^sub>\<a> : Ar\<^sub>1 \<rightarrow> Ar\<^sub>2"
  and F_preserves_objects: "F\<^sub>\<o> : Ob\<^sub>1 \<rightarrow> Ob\<^sub>2"
  and F_preserves_dom: "preserves_dom F"
  and F_preserves_cod: "preserves_cod F"
  and F_preserves_id: "preserves_id F"
  and F_preserves_comp: "preserves_comp F"
begin

lemmas F_axioms = F_preserves_arrows F_preserves_objects F_preserves_dom 
  F_preserves_cod F_preserves_id F_preserves_comp

lemmas func_pred_defs = preserves_dom_def preserves_cod_def preserves_id_def preserves_comp_def

end

text {* This gives us nicer notation for asserting that things are functors. *}

abbreviation
  Functor  ("Functor _ : _ \<longrightarrow> _" [81]) where
  "Functor F : AA \<longrightarrow> BB \<equiv> functor AA BB F"


subsection {* Simple Lemmas *}

text {* For example: *}

lemma (in functor) "Functor F : AA \<longrightarrow> BB" ..


lemma functors_preserve_arrows [intro]:
  assumes "Functor F : AA \<longrightarrow> BB"
    and "f \<in> ar AA"
  shows "F\<^sub>\<a> f \<in> ar BB"
proof-
  from `Functor F : AA \<longrightarrow> BB`
  have "F\<^sub>\<a> : ar AA \<rightarrow> ar BB"
    by (simp add: functor_def functor_axioms_def)
  from this and `f \<in> ar AA`
  show ?thesis by (rule funcset_mem)
qed


lemma (in functor) functors_preserve_homsets:
  assumes 1: "A \<in> Ob\<^sub>1"
  and 2: "B \<in> Ob\<^sub>1"
  and 3: "f \<in> Hom\<^sub>1 A B"
  shows "F\<^sub>\<a> f \<in> Hom\<^sub>2 (F\<^sub>\<o> A) (F\<^sub>\<o> B)"
proof-
  from 3 
  have 4: "f \<in> Ar" 
    by (simp add: hom_def)
  with F_preserves_arrows 
  have 5: "F\<^sub>\<a> f \<in> Ar\<^sub>2" 
    by (rule funcset_mem)
  from 4 and F_preserves_dom 
  have "Dom\<^sub>2 (F\<^sub>\<a> f) = F\<^sub>\<o> (Dom\<^sub>1 f)"
    by (simp add: preserves_dom_def)
  also from 3 have "\<dots> = F\<^sub>\<o> A"
    by (simp add: hom_def)
  finally have 6: "Dom\<^sub>2 (F\<^sub>\<a> f) = F\<^sub>\<o> A" .
  from 4 and F_preserves_cod 
  have "Cod\<^sub>2 (F\<^sub>\<a> f) = F\<^sub>\<o> (Cod\<^sub>1 f)"
    by (simp add: preserves_cod_def)
  also from 3 have "\<dots> = F\<^sub>\<o> B"
    by (simp add: hom_def)
  finally have 7: "Cod\<^sub>2 (F\<^sub>\<a> f) = F\<^sub>\<o> B" .
  from 5 and 6 and 7
  show ?thesis
    by (simp add: hom_def)
qed
    

lemma functors_preserve_objects [intro]:
  assumes "Functor F : AA \<longrightarrow> BB"
    and "A \<in> ob AA"
  shows "F\<^sub>\<o> A \<in> ob BB"
proof-
  from `Functor F : AA \<longrightarrow> BB`
  have "F\<^sub>\<o> : ob AA \<rightarrow> ob BB"
    by (simp add: functor_def functor_axioms_def)
  from this and `A \<in> ob AA`
  show ?thesis by (rule funcset_mem)
qed


subsection {* Identity Functor *}

definition
  id_func :: "('o,'a,'m) category_scheme \<Rightarrow> ('o,'a,'o,'a) functor" where
  "id_func CC = \<lparr>om=(\<lambda>A\<in>ob CC. A), am=(\<lambda>f\<in>ar CC. f)\<rparr>"

locale one_cat = two_cats +
  assumes endo: "BB = AA"

lemma (in one_cat) id_func_preserves_arrows:
  shows "(id_func AA)\<^sub>\<a> : Ar \<rightarrow> Ar"
  by (unfold id_func_def, rule funcsetI, simp)


lemma (in one_cat) id_func_preserves_objects:
  shows "(id_func AA)\<^sub>\<o> : Ob \<rightarrow> Ob"
  by (unfold id_func_def, rule funcsetI, simp)


lemma (in one_cat) id_func_preserves_dom:
  shows  "preserves_dom (id_func AA)"
unfolding preserves_dom_def endo
proof
  fix f
  assume f: "f \<in> Ar"
  hence lhs: "(id_func AA)\<^sub>\<o> (Dom f) = Dom f"
    by (simp add: id_func_def) auto
  have "(id_func AA)\<^sub>\<a> f = f"
    using f by (simp add: id_func_def)
  hence rhs: "Dom (id_func AA)\<^sub>\<a> f = Dom f"
    by simp
  from lhs and rhs show "(id_func AA)\<^sub>\<o> (Dom f) = Dom (id_func AA)\<^sub>\<a> f"
    by simp
qed

lemma (in one_cat) id_func_preserves_cod:
  "preserves_cod (id_func AA)"
apply (unfold preserves_cod_def, simp only: endo)
proof
  fix f
  assume f: "f \<in> Ar"
  hence lhs: "(id_func AA)\<^sub>\<o> (Cod f) = Cod f"
    by (simp add: id_func_def) auto
  have "(id_func AA)\<^sub>\<a> f = f"
    using f by (simp add: id_func_def)
  hence rhs: "Cod (id_func AA)\<^sub>\<a> f = Cod f"
    by simp
  from lhs and rhs show "(id_func AA)\<^sub>\<o> (Cod f) = Cod (id_func AA)\<^sub>\<a> f"
    by simp
qed


lemma (in one_cat) id_func_preserves_id:
  "preserves_id (id_func AA)"
unfolding preserves_id_def endo
proof
  fix A
  assume A: "A \<in> Ob"
  hence lhs: "(id_func AA)\<^sub>\<a> (Id A) = Id A"
    by (simp add: id_func_def) auto
  have "(id_func AA)\<^sub>\<o> A = A"
    using A by (simp add: id_func_def)
  hence rhs: "Id ((id_func AA)\<^sub>\<o> A) = Id A"
    by simp
  from lhs and rhs show "(id_func AA)\<^sub>\<a> (Id A) = Id ((id_func AA)\<^sub>\<o> A)"
    by simp
qed


lemma (in one_cat) id_func_preserves_comp:
  "preserves_comp (id_func AA)"
unfolding preserves_comp_def endo
proof (intro ballI impI)
  fix f and g
  assume f: "f \<in> Ar" and g: "g \<in> Ar" and "Cod f = Dom g"
  then have "g \<bullet> f \<in> Ar" ..
  hence lhs: "(id_func AA)\<^sub>\<a> (g \<bullet> f) = g \<bullet> f"
    by (simp add: id_func_def)
  have id_f: "(id_func AA)\<^sub>\<a> f = f"
    using f by (simp add: id_func_def)
  have id_g: "(id_func AA)\<^sub>\<a> g = g"
    using g by (simp add: id_func_def)
  hence rhs: "(id_func AA)\<^sub>\<a> g \<bullet> (id_func AA)\<^sub>\<a> f = g \<bullet> f"
    by (simp add: id_f id_g)
  from lhs and rhs 
  show "(id_func AA)\<^sub>\<a> (g \<bullet> f) = (id_func AA)\<^sub>\<a> g \<bullet> (id_func AA)\<^sub>\<a> f"
    by simp
qed

theorem (in one_cat) id_func_functor:
  "Functor (id_func AA) : AA \<longrightarrow> AA"
proof-
  from id_func_preserves_arrows
    and id_func_preserves_objects
    and id_func_preserves_dom
    and id_func_preserves_cod
    and id_func_preserves_id
    and id_func_preserves_comp
  show ?thesis
    by unfold_locales (simp_all add: endo preserves_dom_def
      preserves_cod_def preserves_id_def preserves_comp_def)
qed

end
