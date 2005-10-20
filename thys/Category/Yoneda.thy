(*  Title:       Category theory using Isar and Locales
    ID:          $Id: Yoneda.thy,v 1.5 2005-10-20 18:43:32 nipkow Exp $
    Author:      Greg O'Keefe, June, July, August 2003
*)

theory Yoneda
imports  HomFunctors NatTrans
begin

section{* Yonedas Lemma *}
subsection{* The Sandwich Natural Transformation *}

locale Yoneda = functor + into_set +
  assumes "AA = (AA::('o,'a,'m)category_scheme)"
  fixes sandwich :: "['o,'a,'o] \<Rightarrow> 'a set_arrow"  ("\<sigma>'(_,_')")
  defines "sandwich A a \<equiv> (\<lambda>B\<in>Ob. \<lparr>
  set_dom=Hom A B, 
  set_func=(\<lambda>f\<in>Hom A B. set_func (F\<^sub>\<a> f) a),
  set_cod=F\<^sub>\<o> B
  \<rparr>)"
  fixes unsandwich :: "['o,'o \<Rightarrow> 'a set_arrow] \<Rightarrow> 'a" ("\<sigma>\<^sup>\<leftarrow>'(_,_')")
  defines "unsandwich A u \<equiv> set_func (u A) (Id A)"

lemma (in Yoneda) F_into_set: 
  "Functor F : AA \<longrightarrow> Set"
proof-
  from F_axioms have "Functor F : AA \<longrightarrow> BB" 
    by (intro functor.intro functor_axioms.intro two_cats_axioms.intro, 
      simp_all add: func_pred_defs)
  thus ?thesis
    by (simp only: BB_Set)
qed


lemma (in Yoneda) F_comp_func:
  assumes 1: "A \<in> Ob" and 2: "B \<in> Ob" and 3: "C \<in> Ob"
  and 4: "g \<in> Hom A B" and 5: "f \<in> Hom B C"
  shows "set_func (F\<^sub>\<a> (f \<bullet> g)) = compose (F\<^sub>\<o> A) (set_func (F\<^sub>\<a> f)) (set_func (F\<^sub>\<a> g))"
proof-
  from 4 and 5 
  have 7: "Cod g = Dom f" 
    and 8: "g \<in> Ar" 
    and 9: "f \<in> Ar"
    and 10: "Dom g = A"
    by (simp_all add: hom_def)
  from F_preserves_dom and 8 and 10
  have 11: "set_dom (F\<^sub>\<a> g) = F\<^sub>\<o> A"
    by (simp add: preserves_dom_def BB_Set Set_def) auto
  from F_preserves_comp and 7 and 8 and 9
  have "F\<^sub>\<a> (f \<bullet> g) = (F\<^sub>\<a> f) \<bullet>\<^sub>2 (F\<^sub>\<a> g)"
    by (simp add: preserves_comp_def)
  hence "set_func (F\<^sub>\<a> (f \<bullet> g))  = set_func ((F\<^sub>\<a> f) \<odot> (F\<^sub>\<a> g))"
    by (simp add: BB_Set Set_def)
  also have "\<dots> = compose (F\<^sub>\<o> A) (set_func (F\<^sub>\<a> f)) (set_func (F\<^sub>\<a> g))"
    by (simp add: set_comp_def 11)
  finally show ?thesis .
qed

lemma (in Yoneda) sandwich_funcset:
  assumes "A \<in> Ob"
  and "a \<in> F\<^sub>\<o> A"
  shows  "\<sigma>(A,a) : Ob \<rightarrow> ar Set"
proof (rule funcsetI)
  fix B
  assume "B \<in> Ob"
  thus "\<sigma>(A,a) B \<in> ar Set"
  proof (simp add: Set_def sandwich_def set_cat_def)
    show "set_arrow U \<lparr>
      set_dom = Hom A B, 
      set_func = \<lambda>f\<in>Hom A B. set_func (F \<^sub>\<a> f) a, 
      set_cod = F \<^sub>\<o> B\<rparr>"
    proof (simp add: set_arrow_def, intro conjI)
      show "Hom A B \<subseteq> U" and "F\<^sub>\<o> B \<subseteq> U"
	by (simp_all add: U_def)
      show "(\<lambda>f\<in>Hom A B. set_func (F\<^sub>\<a> f) a) \<in> Hom A B \<rightarrow> F\<^sub>\<o> B"
      proof (rule funcsetI, simp)
	fix f
	assume "f \<in> Hom A B"
	have "F\<^sub>\<a> f \<in> Hom\<^sub>2 (F\<^sub>\<o> A) (F\<^sub>\<o> B)"
	  by (rule functors_preserve_homsets)
	hence "F\<^sub>\<a> f \<in> ar Set" 
	  and "set_dom (F\<^sub>\<a> f) = (F\<^sub>\<o> A)"
	  and "set_cod (F\<^sub>\<a> f) = (F\<^sub>\<o> B)"
	  by (simp_all add: hom_def BB_Set Set_def)
	hence "set_func (F\<^sub>\<a> f) : (F\<^sub>\<o> A) \<rightarrow> (F\<^sub>\<o> B)"
	  by (simp add: Set_def set_cat_def set_arrow_def)
	thus "set_func (F\<^sub>\<a> f) a \<in> F\<^sub>\<o> B"
	  by (rule funcset_mem)
      qed
    qed
  qed
qed


lemma (in Yoneda) sandwich_type:
  assumes "A \<in> Ob" and 2:"B \<in> Ob"
  and "a \<in> F\<^sub>\<o> A"
  shows "\<sigma>(A,a) B \<in> hom Set (Hom A B) (F\<^sub>\<o> B)"
proof-
  from sandwich_funcset 
  have "\<sigma>(A,a) B \<in> ar Set"
    by (rule funcset_mem)
  thus ?thesis
    by (simp add: sandwich_def hom_def Set_def 2)
qed


lemma (in Yoneda) sandwich_commutes:
  assumes AOb:"A \<in> Ob" and BOb:"B \<in> Ob" and COb:"C \<in> Ob"
  and aFa: "a \<in> F\<^sub>\<o> A"
  and fBC:"f \<in> Hom B C"
  shows "(F \<^sub>\<a> f) \<odot> (\<sigma>(A,a) B) = (\<sigma>(A,a) C) \<odot> (Hom(A,_) \<^sub>\<a> f)"
proof-
  have "f \<in> Hom B C" .
  hence 1:"f \<in> Ar" and 2:"Dom f = B" and 3:"Cod f = C"
    by (simp_all add: hom_def)
  from BOb
  have "set_dom ((F \<^sub>\<a> f) \<odot> (\<sigma>(A,a) B)) = Hom A B"
    by (simp add: set_comp_def sandwich_def)
  also have "\<dots> = set_dom ((\<sigma>(A,a) C) \<odot> (Hom(A,_) \<^sub>\<a> f))"
    by (simp add: set_comp_def homf_def 1 2)
  finally have set_dom_eq: 
    "set_dom ((F \<^sub>\<a> f) \<odot> (\<sigma>(A,a) B)) 
    = set_dom ((\<sigma>(A,a) C) \<odot> (Hom(A,_) \<^sub>\<a> f))" .
  have "(F\<^sub>\<a> f) \<in> Hom\<^sub>2 (F\<^sub>\<o> B) (F\<^sub>\<o> C)" 
    by (rule functors_preserve_homsets)
  hence "set_cod ((F \<^sub>\<a> f) \<odot> (\<sigma>(A,a) B)) = F\<^sub>\<o> C"
    by (simp add: set_comp_def BB_Set Set_def set_cat_def hom_def)
  also from COb
  have "\<dots> = set_cod ((\<sigma>(A,a) C) \<odot> (Hom(A,_) \<^sub>\<a> f))"
    by (simp add: set_comp_def sandwich_def)
  finally have set_cod_eq:
    "set_cod ((F \<^sub>\<a> f) \<odot> (\<sigma>(A,a) B)) 
    = set_cod ((\<sigma>(A,a) C) \<odot> (Hom(A,_) \<^sub>\<a> f))" .
  from AOb and BOb and COb and fBC and aFa
  have set_func_lhs: 
    "set_func ((F \<^sub>\<a> f) \<odot> (\<sigma>(A,a) B)) = 
    (\<lambda>g\<in>Hom A B. set_func (F \<^sub>\<a> (f \<bullet> g)) a)"
    apply (simp add:  set_comp_def sandwich_def compose_def)
    apply (rule extensionalityI, rule restrict_extensional, rule restrict_extensional)
    by (simp add: F_comp_func compose_def)
  have "(op \<bullet>) : Hom B C \<rightarrow> Hom A B \<rightarrow> Hom A C" ..  
  from this and fBC 
  have opfType: "(op \<bullet>) f : Hom A B \<rightarrow> Hom A C"
    by (rule funcset_mem)
  from 1 and 2
  have "set_func ((\<sigma>(A,a) C) \<odot> (Hom(A,_) \<^sub>\<a> f)) =
    (\<lambda>g\<in>Hom A B. set_func (\<sigma>(A,a) C) (f \<bullet> g))"
    apply (simp add: set_comp_def homf_def)
    apply (simp add: compose_def)
    apply (rule extensionalityI, rule restrict_extensional, rule restrict_extensional)
    by auto
  also from COb and opfType 
  have " \<dots> = (\<lambda>g\<in>Hom A B. set_func (F \<^sub>\<a> (f \<bullet> g)) a)"
    apply (simp add: sandwich_def)
    apply (rule extensionalityI, rule restrict_extensional, rule restrict_extensional)
    by (simp add: funcset_mem)
  finally have set_func_rhs:
    "set_func ((\<sigma>(A,a) C) \<odot> (Hom(A,_) \<^sub>\<a> f)) =
    (\<lambda>g\<in>Hom A B. set_func (F \<^sub>\<a> (f \<bullet> g)) a)" .
  from set_func_lhs and set_func_rhs have
    "set_func ((F \<^sub>\<a> f) \<odot> (\<sigma>(A,a) B))
    = set_func ((\<sigma>(A,a) C) \<odot> (Hom(A,_) \<^sub>\<a> f))"
    by simp
  with set_dom_eq and set_cod_eq show ?thesis
    by simp
qed


lemma (in Yoneda) sandwich_natural:
  assumes "A \<in> Ob"
  and "a \<in> F\<^sub>\<o> A"
  shows  "\<sigma>(A,a) : Hom(A,_) \<Rightarrow> F in Func(AA,Set)"
proof (intro natural_transformation.intro natural_transformation_axioms.intro)
  show "category AA" .
  show "category Set" 
    by (simp only: Set_def)(rule set_cat_cat)
  show "Functor Hom(A,_) : AA \<longrightarrow> Set"
    by (rule homf_into_set)
  show "Functor F : AA \<longrightarrow> Set"
    by (rule F_into_set)
  show "\<forall>B\<in>Ob. \<sigma>(A,a) B \<in> hom Set (Hom(A,_)\<^sub>\<o> B) (F\<^sub>\<o> B)"
    by (intro ballI, simp add: homf_def) (rule sandwich_type)
  show "\<sigma>(A,a) : Ob \<rightarrow> ar Set"
    by (rule sandwich_funcset)
  show "\<sigma>(A,a) \<in> extensional (Ob)"
    by (unfold sandwich_def, rule restrict_extensional)
  show "\<forall>B\<in>Ob. \<forall>C\<in>Ob. \<forall>f\<in>Hom B C.
    comp Set (F \<^sub>\<a> f) (\<sigma>(A,a) B) = comp Set (\<sigma>(A,a) C) (Hom(A,_) \<^sub>\<a> f)"
    by (intro ballI, simp add: Set_def) (rule sandwich_commutes)
qed (intro two_cats_axioms.intro, simp_all)

subsection{* Sandwich Components are Bijective *}

lemma (in Yoneda) unsandwich_left_inverse:
  assumes 1: "A \<in> Ob"
  and 2: "a \<in> F\<^sub>\<o> A"
  shows "\<sigma>\<^sup>\<leftarrow>(A,\<sigma>(A,a)) = a"
proof-
  have "Id A \<in> Hom A A" ..
  with 1 
  have 3: "\<sigma>\<^sup>\<leftarrow>(A,\<sigma>(A,a)) = set_func (F\<^sub>\<a> (Id A)) a"
    by (simp add: sandwich_def homf_def unsandwich_def)
  from F_preserves_id and 1
  have 4: "F\<^sub>\<a> (Id A) = id Set (F\<^sub>\<o> A)"
    by (simp add: preserves_id_def BB_Set)
  from F_preserves_objects and 1 
  have "F\<^sub>\<o> A \<in> Ob\<^sub>2" 
    by (rule funcset_mem)
  hence "F\<^sub>\<o> A \<subseteq> U"
    by (simp add: BB_Set Set_def set_cat_def)
  with 2
  have 5: "set_func (id Set (F\<^sub>\<o> A)) a = a"
    by (simp add: Set_def  set_id_def)
  show ?thesis
    by (simp add: 3 4 5)
qed


lemma (in Yoneda) unsandwich_right_inverse:
  assumes 1: "A \<in> Ob"
  and 2: "u : Hom(A,_) \<Rightarrow> F in Func(AA,Set)"
  shows "\<sigma>(A,\<sigma>\<^sup>\<leftarrow>(A,u)) = u"
proof (rule extensionalityI)
  show "\<sigma>(A,\<sigma>\<^sup>\<leftarrow>(A,u)) \<in> extensional (Ob)"
    by (unfold sandwich_def, rule restrict_extensional)
  from 2 show "u \<in>  extensional (Ob)"
    by (simp add: natural_transformation_def natural_transformation_axioms_def)
  fix B
  assume 3: "B \<in> Ob"
  with 1
  have one: "\<sigma>(A,\<sigma>\<^sup>\<leftarrow>(A,u)) B = \<lparr>
    set_dom = Hom A B,
    set_func = (\<lambda>f\<in>Hom A B. (set_func (F\<^sub>\<a> f)) (set_func (u A) (Id A))),
    set_cod = F\<^sub>\<o> B \<rparr>"
    by (simp add: sandwich_def unsandwich_def)
  from 1 have "Hom(A,_)\<^sub>\<o> A = Hom A A"
    by (simp add: homf_def)
  with 1 and 2 have "(u A) \<in> hom Set (Hom A A) (F\<^sub>\<o> A)"
    by (simp add: natural_transformation_def natural_transformation_axioms_def,
      auto)
  hence "set_dom (u A) = Hom A A"
    by (simp add: hom_def Set_def)
  with 1 have applicable: "Id A \<in> set_dom (u A)"
    by (simp)(rule)
  have two: "(\<lambda>f\<in>Hom A B. (set_func (F\<^sub>\<a> f)) (set_func (u A) (Id A))) 
    = (\<lambda>f\<in>Hom A B. (set_func ((F\<^sub>\<a> f) \<odot> (u A)) (Id A)))" 
    by (rule extensionalityI,
      rule restrict_extensional, rule restrict_extensional,
      simp add: set_comp_def compose_def applicable)
  from 2
  have "(\<forall>X\<in>Ob. \<forall>Y\<in>Ob. \<forall>f\<in>Hom X Y. (F\<^sub>\<a> f) \<bullet>\<^sub>2 (u X) = (u Y) \<bullet>\<^sub>2 (Hom(A,_)\<^sub>\<a> f))"
    by (simp add: natural_transformation_def natural_transformation_axioms_def BB_Set)
  with 1 and 3 
  have three: "(\<lambda>f\<in>Hom A B. (set_func ((F\<^sub>\<a> f) \<odot> (u A)) (Id A))) 
    = (\<lambda>f\<in>Hom A B. (set_func ((u B) \<odot> (Hom(A,_))\<^sub>\<a> f)) (Id A))"
    apply (simp add: BB_Set Set_def)
    apply (rule extensionalityI)
    apply (rule restrict_extensional, rule restrict_extensional)
    by simp
  have "\<forall>f \<in> Hom A B. set_dom (Hom(A,_)\<^sub>\<a> f) = Hom A A"
    by (intro ballI, simp add: homf_def hom_def)
  have roolz: "\<And>f. f \<in> Hom A B \<Longrightarrow> set_dom (Hom(A,_)\<^sub>\<a> f) = Hom A A"
    by (simp add: homf_def hom_def)
  have rooly: "Id A \<in> Hom A A" ..
  have roolx: "\<And>f. f \<in> Hom A B \<Longrightarrow> f \<in> Ar"
    by (simp add: hom_def)
  have roolw: "\<And>f. f \<in> Hom A B \<Longrightarrow> Id A \<in> Hom A (Dom f)"
  proof-
    fix f
    assume "f \<in> Hom A B"
    hence "Dom f = A" by (simp add: hom_def)
    thus "Id A \<in> Hom A (Dom f)"
      by simp rule
  qed
  have annoying: "\<And>f. f \<in> Hom A B \<Longrightarrow> Id A = Id (Dom f)"
    by (simp add: hom_def)
  have "(\<lambda>f\<in>Hom A B. (set_func ((u B) \<odot> (Hom(A,_))\<^sub>\<a> f)) (Id A))
    = (\<lambda>f\<in>Hom A B. (compose (Hom A A) (set_func (u B)) (set_func (Hom(A,_)\<^sub>\<a> f))) (Id A))"
    apply (rule extensionalityI)
    apply (rule restrict_extensional, rule restrict_extensional)
    by (simp add: compose_def set_comp_def roolz rooly)
  also have "\<dots> = (\<lambda>f\<in>Hom A B. (set_func (u B) f))"
    apply (rule extensionalityI)
    apply (rule restrict_extensional, rule restrict_extensional)
    apply (simp add: compose_def homf_def rooly roolx roolw)
    apply (simp only: annoying)
    apply (simp add: roolx id_right)
    done
  finally have four: 
    "(\<lambda>f\<in>Hom A B. (set_func ((u B) \<odot> (Hom(A,_))\<^sub>\<a> f)) (Id A))
    = (\<lambda>f\<in>Hom A B. (set_func (u B) f))" .
  from 2 and  3 
  have uBhom: "u B \<in> hom Set (Hom(A,_)\<^sub>\<o> B) (F\<^sub>\<o> B)"
    by (simp add: natural_transformation_def natural_transformation_axioms_def)
  with 3 
  have five: "set_dom (u B) = Hom A B"
    by (simp add: hom_def homf_def Set_def set_cat_def)
  from uBhom
  have six: "set_cod (u B) = F\<^sub>\<o> B" 
    by (simp add: hom_def homf_def Set_def set_cat_def)
  have seven: "restrict (set_func (u B)) (Hom A B) = set_func (u B)"
    apply (rule extensionalityI)
    apply (rule restrict_extensional)
  proof-
    from uBhom have "u B \<in> ar Set"
      by (simp add: hom_def)
    hence almost: "set_func (u B) \<in> extensional (set_dom (u B))"
      by (simp add: Set_def set_cat_def set_arrow_def)
    from almost and five
    show "set_func (u B) \<in> extensional (Hom A B)" 
      by simp
    fix f
    assume "f \<in> Hom A B"
    thus "restrict (set_func (u B)) (Hom A B) f = set_func (u B) f"
      by simp
  qed
  from one and two and three and four and five and six and seven
  show "\<sigma>(A,\<sigma>\<^sup>\<leftarrow>(A,u)) B = u B" 
    by simp
qed


text {* In order to state the lemma, we must rectify a curious
omission from the Isabelle/HOL library. They define the idea of
injectivity on a given set, but surjectivity is only defined relative
to the entire universe of the target type. *}

constdefs
  surj_on :: "['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool"   
  "surj_on f A B \<equiv> \<forall>y\<in>B. \<exists>x\<in>A. f(x)=y"
  bij_on :: "['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool" 
  "bij_on f A B \<equiv> inj_on f A & surj_on f A B"
  equinumerous :: "['a set, 'b set] \<Rightarrow> bool" (infix "\<cong>" 40)
  "equinumerous A B \<equiv> \<exists>f. bij_on f A B"

theorem (in Yoneda) Yoneda:
  assumes 1: "A \<in> Ob"
  shows "F\<^sub>\<o> A \<cong> {u. u : Hom(A,_) \<Rightarrow> F in Func(AA,Set)}"
apply (unfold equinumerous_def bij_on_def surj_on_def inj_on_def)
apply (intro exI conjI bexI ballI impI)
proof-
  -- "Sandwich is injective"
  fix x and y
  assume 2: "x \<in> F\<^sub>\<o> A" and 3: "y \<in> F\<^sub>\<o> A"
  and 4: "\<sigma>(A,x) = \<sigma>(A,y)"
  hence "\<sigma>\<^sup>\<leftarrow>(A,\<sigma>(A,x)) = \<sigma>\<^sup>\<leftarrow>(A,\<sigma>(A,y))"
    by simp
  with unsandwich_left_inverse
  show "x = y"
    by (simp add: 1 2 3)
next
  -- "Sandwich covers F A"
  fix u
  assume "u \<in> {y. y : Hom(A,_) \<Rightarrow> F in Func (AA,Set)}"
  hence 2: "u : Hom(A,_) \<Rightarrow> F in Func (AA,Set)"
    by simp
  with 1 show "\<sigma>(A,\<sigma>\<^sup>\<leftarrow>(A,u)) = u"
    by (rule unsandwich_right_inverse)
  -- "Sandwich is into F A" (* there is really similar reasoning elsewhere*)
  from 1 and 2 
  have "u A \<in> hom Set (Hom A A) (F\<^sub>\<o> A)"
    by (simp add: natural_transformation_def natural_transformation_axioms_def homf_def)
  hence "u A \<in> ar Set" and "dom Set (u A) = Hom A A" and "cod Set (u A) = F\<^sub>\<o> A"
    by (simp_all add: hom_def)
  hence uAfuncset: "set_func (u A) : (Hom A A) \<rightarrow> (F\<^sub>\<o> A)"
    by (simp add: Set_def set_cat_def set_arrow_def)
  have "Id A \<in> Hom A A" ..
  with uAfuncset 
  show "\<sigma>\<^sup>\<leftarrow>(A,u) \<in> F\<^sub>\<o> A"
    by (simp add: unsandwich_def, rule funcset_mem)
qed

end