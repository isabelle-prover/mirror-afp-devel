(*  Title:       Category theory using Isar and Locales
    ID:          $Id: HomFunctors.thy,v 1.6 2005-10-20 18:43:32 nipkow Exp $
    Author:      Greg O'Keefe, June, July, August 2003
*)

(* Define homfunctors, prove that they are functors *)
theory HomFunctors
imports SetCat Functors
begin


locale into_set = two_cats +
  assumes "AA = (AA::('o,'a,'m)category_scheme)"
  fixes U and Set 
  defines "U \<equiv> (UNIV::'a set)"
  defines "Set \<equiv> set_cat U"
  assumes BB_Set: "BB = Set"
  fixes homf ("Hom'(_,'_')")
  defines "homf A \<equiv> \<lparr>
  om = (\<lambda>B\<in>Ob. Hom A B),
  am = (\<lambda>f\<in>Ar. \<lparr>set_dom=Hom A (Dom f),set_func=(\<lambda>g\<in>Hom A (Dom f). f \<bullet> g),set_cod=Hom A (Cod f)\<rparr>)
  \<rparr>"


lemma (in into_set) homf_preserves_arrows:
 "Hom(A,_)\<^sub>\<a> : Ar \<rightarrow> ar Set"
proof (rule funcsetI)
  fix f
  assume "f \<in> Ar"
  thus "Hom(A,_)\<^sub>\<a> f \<in> ar Set"
  proof (simp add: homf_def Set_def set_cat_def set_arrow_def U_def)
    have 1: "(op \<bullet>) : Hom (Dom f) (Cod f) \<rightarrow> Hom A (Dom f) \<rightarrow> Hom A (Cod f)" ..
    have 2: "f \<in> Hom (Dom f) (Cod f)" by (simp add: hom_def)
    from 1 and 2 have 3: "(op \<bullet>) f : Hom A (Dom f) \<rightarrow> Hom A (Cod f)" 
      by (rule funcset_mem)
    show "(\<lambda>g\<in>Hom A (Dom f). f \<bullet> g) : Hom A (Dom f) \<rightarrow> Hom A (Cod f)"
    proof (rule funcsetI)
      fix g'
      assume "g' \<in> Hom A (Dom f)"
      from 3 and this show "(\<lambda>g\<in>Hom A (Dom f). f \<bullet> g) g' \<in> Hom A (Cod f)"
	by simp (rule funcset_mem)
    qed
  qed
qed


lemma (in into_set) homf_preserves_objects:
 "Hom(A,_)\<^sub>\<o> : Ob \<rightarrow> ob Set"
proof (rule funcsetI)
  fix B
  assume "B \<in> Ob"
  have "Hom(A,_)\<^sub>\<o> B = Hom A B"
    by (simp! add: homf_def)
  also have "\<dots> \<in> ob Set"
    by (simp! add: Set_def set_cat_def)
  finally show "Hom(A,_)\<^sub>\<o> B \<in> ob Set" .
qed


lemma (in into_set) homf_preserves_dom:
  assumes "f \<in> Ar"
  shows "Hom(A,_)\<^sub>\<o> (Dom f) = dom Set (Hom(A,_)\<^sub>\<a> f)"
proof-
  have "Dom f \<in> Ob" ..
  hence 1: "Hom(A,_)\<^sub>\<o> (Dom f) = Hom A (Dom f)"
    by (simp! add: homf_def)
  have 2: "dom Set (Hom(A,_)\<^sub>\<a> f) = Hom A (Dom f)"
    by (simp! add: homf_def)
  from 1 and 2 show ?thesis by simp
qed

lemma (in into_set) homf_preserves_cod:
  assumes "f \<in> Ar"
  shows "Hom(A,_)\<^sub>\<o> (Cod f) = cod Set (Hom(A,_)\<^sub>\<a> f)"
proof-
  have "Cod f \<in> Ob" ..
  hence 1: "Hom(A,_)\<^sub>\<o> (Cod f) = Hom A (Cod f)"
    by (simp! add: homf_def)
  have 2: "cod Set (Hom(A,_)\<^sub>\<a> f) = Hom A (Cod f)"
    by (simp! add: homf_def)
  from 1 and 2 show ?thesis by simp
qed


lemma (in into_set) homf_preserves_id:
  assumes "B \<in> Ob"
  shows "Hom(A,_)\<^sub>\<a> (Id B) = id Set (Hom(A,_)\<^sub>\<o> B)"
proof-
  have 1: "Id B \<in> Ar" ..
  have 2: "Dom (Id B) = B"
    by (rule category.id_dom_cod)
  have 3: "Cod (Id B) = B"
    by (rule category.id_dom_cod)
  have 4: "(\<lambda>g\<in>Hom A B. (Id B) \<bullet> g) = (\<lambda>g\<in>Hom A B. g)"
    by (rule ext, simp add: hom_def, auto)
  have "Hom(A,_)\<^sub>\<a> (Id B) = \<lparr>
    set_dom=Hom A B, 
    set_func=(\<lambda>g\<in>Hom A B. g),
    set_cod=Hom A B\<rparr>"
    by (simp add: homf_def 1 2 3 4)
  also have "\<dots>= id Set (Hom(A,_)\<^sub>\<o> B)"
    by (simp! add: Set_def U_def set_cat_def set_id_def homf_def)
  finally show ?thesis .
qed
  

lemma (in into_set) homf_preserves_comp:
  assumes f_arrow: "f \<in> Ar" 
  and g_arrow: "g \<in> Ar"
  and "Cod f = Dom g"
  shows "Hom(A,_)\<^sub>\<a> (g \<bullet> f) = (Hom(A,_)\<^sub>\<a> g) \<odot> (Hom(A,_)\<^sub>\<a> f)"
proof-
  have 1: "g \<bullet> f \<in> Ar" ..
  have 2: "Dom (g \<bullet> f) = Dom f" ..
  have 3: "Cod (g \<bullet> f) = Cod g" ..
  have lhs:"Hom(A,_)\<^sub>\<a> (g \<bullet> f) = \<lparr>
    set_dom=Hom A (Dom f), 
    set_func=(\<lambda>h\<in>Hom A (Dom f). (g \<bullet> f) \<bullet> h),
    set_cod=Hom A (Cod g)\<rparr>"
    by (simp add: homf_def 1 2 3)
  have 4: "set_dom ((Hom(A,_)\<^sub>\<a> g) \<odot> (Hom(A,_)\<^sub>\<a> f)) = Hom A (Dom f)"
    by (simp add: set_comp_def homf_def f_arrow)
  have 5: "set_cod ((Hom(A,_)\<^sub>\<a> g) \<odot> (Hom(A,_)\<^sub>\<a> f)) = Hom A (Cod g)"
    by (simp add: set_comp_def homf_def  g_arrow)
  have "set_func ((Hom(A,_)\<^sub>\<a> g) \<odot> (Hom(A,_)\<^sub>\<a> f))
    = compose (Hom A (Dom f)) (\<lambda>y\<in>Hom A (Dom g). g \<bullet> y) (\<lambda>x\<in>Hom A (Dom f). f \<bullet> x)"
    by (simp add: set_comp_def homf_def f_arrow g_arrow)
  also have "\<dots> = (\<lambda>h\<in>Hom A (Dom f). (g \<bullet> f) \<bullet> h)"
  proof (
      rule extensionalityI, 
      rule compose_extensional,
      rule restrict_extensional,
      simp)
    fix h
    assume 10: "h \<in> Hom A (Dom f)"
    hence 11: "f \<bullet> h \<in> Hom A (Dom g)"
    proof-
      from 10 have "h \<in> Ar" by (simp add: hom_def)
      have 100: "(op \<bullet>) : Hom (Dom f) (Dom g) \<rightarrow> Hom A (Dom f) \<rightarrow> Hom A (Dom g)"
	by (rule category.comp_types)
      have "f \<in> Hom (Dom f) (Cod f)" by (simp add: hom_def)
      hence 101: "f \<in> Hom (Dom f) (Dom g)" by (simp!)
      from 100 and 101
      have "(op \<bullet>) f : Hom A (Dom f) \<rightarrow> Hom A (Dom g)"
	by (rule funcset_mem)
      from this and 10 
      show "f \<bullet> h \<in> Hom A (Dom g)"
	by (rule funcset_mem)
    qed
    hence "Cod (f \<bullet> h) = Dom g" 
      and "Dom (f \<bullet> h) = A"
      and "f \<bullet> h \<in> Ar"
      by (simp_all add: hom_def)
    thus "compose (Hom A (Dom f)) (\<lambda>y\<in>Hom A (Dom g). g \<bullet> y) (\<lambda>x\<in>Hom A (Dom f). f \<bullet> x) h = (g \<bullet> f) \<bullet> h"
      by (simp! add: compose_def 10 11 hom_def)
  qed
  finally have 6: "set_func ((Hom(A,_)\<^sub>\<a> g) \<odot> (Hom(A,_)\<^sub>\<a> f))
    = (\<lambda>h\<in>Hom A (Dom f). (g \<bullet> f) \<bullet> h)" .
  from 4 and 5 and 6
  have rhs: "(Hom(A,_)\<^sub>\<a> g) \<odot> (Hom(A,_)\<^sub>\<a> f) = \<lparr>
    set_dom=Hom A (Dom f), 
    set_func=(\<lambda>h\<in>Hom A (Dom f). (g \<bullet> f) \<bullet> h),
    set_cod=Hom A (Cod g)\<rparr>"
    by simp
  show ?thesis
    by (simp add: lhs rhs)
qed


theorem (in into_set) homf_into_set:
  "Functor Hom(A,_) : AA \<longrightarrow> Set"
proof (intro functor.intro functor_axioms.intro two_cats_axioms.intro)
  show "Hom(A,_)\<^sub>\<a> : Ar \<rightarrow> ar Set"
    by (rule homf_preserves_arrows)
  show "Hom(A,_)\<^sub>\<o> : Ob \<rightarrow> ob Set"
    by (rule homf_preserves_objects)
  show "\<forall>f\<in>Ar. Hom(A,_) \<^sub>\<o> (Dom f) = dom Set (Hom(A,_) \<^sub>\<a> f)"
    by (intro ballI) (rule homf_preserves_dom)
  show "\<forall>f\<in>Ar. Hom(A,_) \<^sub>\<o> (Cod f) = cod Set (Hom(A,_) \<^sub>\<a> f)"
    by (intro ballI) (rule homf_preserves_cod)
  show "\<forall>B\<in>Ob. Hom(A,_) \<^sub>\<a> (Id B) = id Set (Hom(A,_) \<^sub>\<o> B)"
    by (intro ballI) (rule homf_preserves_id)
  show "\<forall>f\<in>Ar. \<forall>g\<in>Ar. 
    Cod f = Dom g \<longrightarrow>
    Hom(A,_)\<^sub>\<a> (g \<bullet> f) = comp Set (Hom(A,_)\<^sub>\<a> g) (Hom(A,_)\<^sub>\<a> f)"
    by (intro ballI impI, simp add: Set_def set_cat_def) (rule homf_preserves_comp)
  show "category Set" 
    by (unfold Set_def, rule set_cat_cat)
qed (simp_all)

end