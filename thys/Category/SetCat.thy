(*  Title:       Category theory using Isar and Locales
    ID:          $Id: SetCat.thy,v 1.5 2005-10-20 18:43:32 nipkow Exp $
    Author:      Greg O'Keefe, June, July, August 2003
*)

theory SetCat
imports Cat
begin

section {* {{\sf Set}} is a Category *}
subsection{* Definitions *}
record 'c set_arrow =
  set_dom :: "'c set"
  set_func :: "'c \<Rightarrow> 'c"
  set_cod :: "'c set"

constdefs
  set_arrow :: "['c set, 'c set_arrow] \<Rightarrow> bool"
  "set_arrow U f \<equiv> set_dom f \<subseteq> U & set_cod f \<subseteq> U 
  & (set_func f): (set_dom f) \<rightarrow> (set_cod f) 
  & set_func f \<in> extensional (set_dom f)"
  set_id :: "['c set, 'c set] \<Rightarrow> 'c set_arrow"
  "set_id U \<equiv> \<lambda>s\<in>Pow U. \<lparr>set_dom=s, set_func=\<lambda>x\<in>s. x, set_cod=s\<rparr>"
  set_comp :: "['c set_arrow, 'c set_arrow] \<Rightarrow> 'c set_arrow" (infix "\<odot>" 70)
  "set_comp g f \<equiv> 
  \<lparr>
    set_dom = set_dom f, 
    set_func = compose (set_dom f) (set_func g) (set_func f), 
    set_cod = set_cod g
  \<rparr>"
  set_cat :: "'c set \<Rightarrow> ('c set, 'c set_arrow) category"
  "set_cat U \<equiv>
  \<lparr> 
    ob = Pow U,
    ar = {f. set_arrow U f},
    dom = set_dom,
    cod = set_cod,
    id = set_id U, 
    comp = set_comp
  \<rparr>"

subsection {* Simple Rules and Lemmas *}
lemma set_objectI [intro]: "A \<subseteq> U \<Longrightarrow> A \<in> ob (set_cat U)"
  by (simp add: set_cat_def)

lemma set_objectE [intro]: "A \<in> ob (set_cat U) \<Longrightarrow> A \<subseteq> U"
  by (simp add: set_cat_def)

lemma set_homI [intro]:
  assumes "A \<subseteq> U"
  and "B \<subseteq> U"
  and "f : A\<rightarrow>B"
  and "f \<in> extensional A"
  shows "\<lparr>set_dom=A, set_func=f, set_cod=B\<rparr> \<in> hom (set_cat U) A B"
  by (simp add: set_cat_def hom_def set_arrow_def) (intro conjI)

lemma set_dom [simp]: "dom (set_cat U) f = set_dom f"
  by (simp add: set_cat_def)

lemma set_cod [simp]: "cod (set_cat U) f = set_cod f"
  by (simp add: set_cat_def)

lemma set_id [simp]: "id (set_cat U) A = set_id U A"
  by (simp add: set_cat_def)

lemma set_comp [simp]: "comp (set_cat U) g f = g \<odot> f"
  by (simp add: set_cat_def)
  

lemma set_dom_cod_object_subset [intro]:
  notes set_defs [simp] = set_cat_def set_arrow_def 
  assumes "f \<in> ar (set_cat U)"
  shows "dom (set_cat U) f \<in> ob (set_cat U)"
  and "cod (set_cat U) f \<in> ob (set_cat U)"
  and "set_cod f \<subseteq> U"
  and "set_dom f \<subseteq> U"
proof-
  have "dom (set_cat U) f = set_dom f" by (simp!)
  also show "\<dots> \<subseteq> U" by (simp!)
  finally show "dom (set_cat U) f \<in> ob (set_cat U)" ..
  have "cod (set_cat U) f = set_cod f" by (simp!)
  also show "\<dots> \<subseteq> U" by (simp!)
  finally show "cod (set_cat U) f \<in> ob (set_cat U)" ..
qed


text {* In this context, $f \in hom A B$ is quite a strong claim. *}

lemma set_homE [intro]:
  assumes "f \<in> hom (set_cat U) A B"
  shows "A \<subseteq> U"
  and "B \<subseteq> U"
  and "set_dom f = A"
  and "set_func f : A \<rightarrow> B"
  and "set_cod f = B"
proof-
  have 1: "f \<in> ar (set_cat U)" 
    by (simp! add: hom_def set_cat_def)
  show 2: "set_dom f = A"
    by (simp! add: set_cat_def hom_def set_arrow_def)
  from 1 have "set_dom f \<subseteq> U" ..
  thus "A \<subseteq> U" by (simp add: 2)
  show 3: "set_cod f = B"
    by (simp! add: set_cat_def hom_def set_arrow_def)
  from 1 have "set_cod f \<subseteq> U" ..
  thus "B \<subseteq> U" by (simp add: 3)
  have "set_func f \<in> (set_dom f) \<rightarrow> (set_cod f)"
    by (simp! add: set_cat_def hom_def set_arrow_def) auto
  thus "set_func f \<in> A \<rightarrow> B"
    by (simp add: 2 3)
qed


subsection {* Set is a Category *}
lemma set_id_left:
  assumes "f \<in> ar (set_cat U)"
  shows "set_id U (set_cod f) \<odot> f = f"
proof-
  have "set_cod f \<subseteq> U" ..
  hence 1: "set_id U (set_cod f) \<odot> f = 
    \<lparr>
    set_dom=set_dom f, 
    set_func=compose (set_dom f) (\<lambda>x\<in>set_cod f. x) (set_func f),
    set_cod=set_cod f
    \<rparr>"
    by (simp! add: set_comp_def set_id_def)
  have 2: "compose (set_dom f)  (\<lambda>x\<in>set_cod f. x) (set_func f) = set_func f"
  proof (rule extensionalityI)
    show "compose (set_dom f) (\<lambda>x\<in>set_cod f. x) (set_func f) \<in> extensional (set_dom f)"
      by (rule compose_extensional)
    show "set_func f \<in> extensional (set_dom f)"
      by (simp! add: set_cat_def set_arrow_def)
    fix x
    assume x_in_dom: "x \<in> set_dom f"
    have f_into_cod: "set_func f : (set_dom f) \<rightarrow> (set_cod f)" 
      by (simp! add: set_cat_def set_arrow_def)
    from f_into_cod and x_in_dom
    have f_x_in_cod: "set_func f x \<in> set_cod f"
      by (rule funcset_mem)
    show "compose (set_dom f) (\<lambda>x\<in>set_cod f. x) (set_func f) x = set_func f x"
      by (simp add: x_in_dom f_x_in_cod compose_def)
  qed
  from 1 have "set_id U (set_cod f) \<odot> f = 
    \<lparr>
    set_dom=set_dom f, 
    set_func=set_func f,
    set_cod=set_cod f
    \<rparr>"
    by (simp only: 2)
  also have "\<dots> = f"
    by simp
  finally show ?thesis .
qed

lemma set_id_right:
  assumes "f \<in> ar (set_cat U)"
  shows "f \<odot> (set_id U (set_dom f)) = f"
proof-
  have "set_dom f \<subseteq> U" ..
  hence 1: "f \<odot> (set_id U (set_dom f)) = 
    \<lparr>
    set_dom=set_dom f, 
    set_func=compose (set_dom f) (set_func f) (\<lambda>x\<in>set_dom f. x),
    set_cod=set_cod f
    \<rparr>"
    by (simp! add: set_comp_def set_id_def)
  have 2: "compose (set_dom f) (set_func f) (\<lambda>x\<in>set_dom f. x) = set_func f"
  proof (rule extensionalityI)
    show "compose (set_dom f) (set_func f) (\<lambda>x\<in>set_dom f. x) \<in> extensional (set_dom f)"
      by (rule compose_extensional)
    show "set_func f \<in> extensional (set_dom f)"
      by (simp! add: set_cat_def set_arrow_def)
    fix x
    assume x_in_dom: "x \<in> set_dom f"
    thus "compose (set_dom f) (set_func f) (\<lambda>x\<in>set_dom f. x) x = set_func f x"
      by (simp add: compose_def)
  qed
  from 1 have "f \<odot> (set_id U (set_dom f)) = 
    \<lparr>
    set_dom=set_dom f, 
    set_func=set_func f,
    set_cod=set_cod f
    \<rparr>"
    by (simp only: 2)
  also have "\<dots> = f"
    by simp
  finally show ?thesis .
qed

lemma set_id_hom:
  assumes "A \<in> ob (set_cat U)"
  shows "id (set_cat U) A \<in> hom (set_cat U) A A"
proof-
  have 1: "A \<subseteq> U" ..
  hence "id (set_cat U) A = \<lparr>set_dom=A, set_func=\<lambda>x\<in>A. x, set_cod=A\<rparr>"
    by (simp add: set_cat_def set_id_def)
  also have "\<dots> \<in> hom (set_cat U) A A"
  proof (rule set_homI)
    show "(\<lambda>x\<in>A. x) \<in> A \<rightarrow> A"
      by (rule funcsetI, auto)
    show "(\<lambda>x\<in>A. x) \<in> extensional A"
      by (rule restrict_extensional)
  qed (rule 1, rule 1)
  finally show ?thesis .
qed


lemma set_comp_types:
"comp (set_cat U) \<in> hom (set_cat U) B C \<rightarrow> hom (set_cat U) A B \<rightarrow> hom (set_cat U) A C"
proof (rule funcsetI)
  fix g
  assume g_BC: "g \<in> hom (set_cat U) B C"
  hence comp_cod: "set_cod g = C" ..
  show "comp (set_cat U) g \<in> hom (set_cat U) A B \<rightarrow> hom (set_cat U) A C"
  proof (rule funcsetI)
    fix f
    assume f_AB: "f \<in> hom (set_cat U) A B"
    hence comp_dom: "set_dom f = A" ..
    show "comp (set_cat U) g f \<in> hom (set_cat U) A C"
    proof-
      have "comp (set_cat U) g f = 
	\<lparr>
	set_dom = A, 
	set_func = compose (set_dom f) (set_func g) (set_func f),
	set_cod = C
	\<rparr>"
	by (simp add: set_cat_def set_comp_def comp_cod comp_dom)
      also have "\<dots> \<in> hom (set_cat U) A C"
      proof (rule set_homI)
	show "A \<subseteq> U" ..
	show "C \<subseteq> U" ..
	have fs_f: "set_func f: A \<rightarrow> B" ..
	have fs_g: "set_func g: B \<rightarrow> C" ..
	from fs_g and fs_f
	show " compose (set_dom f) (set_func g) (set_func f) : A \<rightarrow> C"
	  by (simp only: comp_dom) (rule funcset_compose)
	show "compose (set_dom f) (set_func g) (set_func f) \<in> extensional A"
	  by (simp only: comp_dom) (rule compose_extensional)
      qed
      finally show ?thesis .
    qed
  qed
qed

text {* We reason explicitly about the function component of the
composite arrow, leaving the rest to the simplifier. *}
	  
lemma set_comp_associative:
  fixes f and g and h
  assumes f_arrow: "f \<in> ar (set_cat U)" 
  and  g_arrow: "g \<in> ar (set_cat U)" 
  and  h_arrow: "h \<in> ar (set_cat U)" 
  and "cod (set_cat U) h = dom (set_cat U) g" 
  and "cod (set_cat U) g = dom (set_cat U) f"
  shows "comp (set_cat U) f (comp (set_cat U) g h) =
  comp (set_cat U) (comp (set_cat U) f g) h"
proof (simp add: set_cat_def set_comp_def)
  show "compose (set_dom h) (set_func f) (compose (set_dom h) (set_func g) (set_func h)) =
    compose (set_dom h) (compose (set_dom g) (set_func f) (set_func g)) (set_func h)"
  proof (rule compose_assoc)
    have 1: "set_cod h = set_dom g" by (simp!)
    have 2: "set_cod g = set_dom f" by (simp!)
    from h_arrow show "set_func h \<in> set_dom h \<rightarrow> set_dom g" 
      by (simp add: set_cat_def set_arrow_def 1)  
    from g_arrow show "set_func g \<in> set_dom g \<rightarrow> set_dom f"
      by (simp add: set_cat_def set_arrow_def 2)  
    from f_arrow show "set_func f \<in> set_dom f \<rightarrow> set_cod f"
      by (simp add: set_cat_def set_arrow_def)  
  qed
qed


theorem set_cat_cat:  "category (set_cat U)"
proof (intro category.intro)
  fix f
  assume "f \<in> ar (set_cat U)"
  show "dom (set_cat U) f \<in> ob (set_cat U)" ..
  show "cod (set_cat U) f \<in> ob (set_cat U)" ..
  show "comp (set_cat U) (id (set_cat U) (cod (set_cat U) f)) f = f"
    by (simp!) (rule set_id_left)
  show "comp (set_cat U) f (id (set_cat U) (dom (set_cat U) f)) = f"
    by (simp!) (rule set_id_right)
next
  fix A
  assume "A \<in> ob (set_cat U)"
  show "id (set_cat U) A \<in> hom (set_cat U) A A"
    by (rule set_id_hom)
next
  fix A and B and C
  show "comp (set_cat U) \<in> hom (set_cat U) B C \<rightarrow> hom (set_cat U) A B \<rightarrow> hom (set_cat U) A C"
    by (rule set_comp_types)
next
  fix f and g and h
  assume "f \<in> ar (set_cat U)" 
    and  "g \<in> ar (set_cat U)" 
    and  "h \<in> ar (set_cat U)" 
    and "cod (set_cat U) h = dom (set_cat U) g" 
    and "cod (set_cat U) g = dom (set_cat U) f"
  show "comp (set_cat U) f (comp (set_cat U) g h) =
    comp (set_cat U) (comp (set_cat U) f g) h"
    by (rule set_comp_associative)
qed

end
