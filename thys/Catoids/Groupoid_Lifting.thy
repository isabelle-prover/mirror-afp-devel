(*
Title: Lifting groupoids to distributive Dedekind quantales
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Lifting groupoids to powerset Dedekind quantales and powerset relation algebras\<close>

theory Groupoid_Lifting
  imports Groupoid Quantales_Converse.Quantale_Converse Catoid_Lifting Relation_Algebra.Relation_Algebra

begin

instantiation set :: (groupoid) dedekind_quantale
begin

definition invol_set :: "'a set \<Rightarrow> 'a set" where
  "invol = Inv"

instance
  apply intro_classes
     apply (simp add: invol_set_def)
    apply (simp add: Inv_contrav invol_set_def times_set_def)
   apply (simp add: Groupoid_Lifting.invol_set_def image_Union)
  by (simp add: groupoid_class.modular_law invol_set_def times_set_def)

end

instantiation set :: (groupoid) boolean_dedekind_quantale

begin

instance..

end

instantiation set :: (groupoid) relation_algebra

begin

definition composition_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
   "composition_set x y = x \<star> y"

definition  converse_set :: "'a set \<Rightarrow> 'a set" where
  "converse = Inv"

definition unit_set :: "'a set" where
   "unit_set = sfix"

instance
  apply intro_classes
        apply (simp add: composition_set_def conv_assoc)
       apply (smt (verit) composition_set_def stfix_set stopp.conv_uns unit_set_def)
      apply (simp add: composition_set_def stopp.conv_distl_small)
     apply (simp add: converse_set_def)
    apply (simp add: converse_set_def st_mgpd.Inv_un)
   apply (simp add: Inv_contrav composition_set_def converse_set_def)
  by (simp add: composition_set_def converse_set_def groupoid_class.residuation)

end

end


























