(*
Title: Lifting catoids to modal powerset quantales
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Lifting catoids to modal powerset quantales\<close>

theory Catoid_Lifting
  imports Catoid Quantales_Converse.Modal_Quantale

begin

instantiation set :: (catoid) monoid_mult

begin

definition one_set :: "'a set" where
  "1 = sfix"

definition times_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "X * Y = X \<star> Y"

instance
  apply intro_classes
  unfolding times_set_def one_set_def
    apply (simp add: conv_assoc)
  using stopp.conv_unt apply blast
  by (metis stfix_set stopp.conv_uns)

end

instantiation set :: (catoid) semiring_one_zero

begin

definition zero_set :: "'a set" where
  "zero_set = {}"

definition plus_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "X + Y = X \<union> Y"

instance
  apply intro_classes
  unfolding times_set_def one_set_def zero_set_def plus_set_def conv_exp
          apply safe
             apply blast
            apply blast
           apply blast
          apply blast
         apply (metis Dst empty_iff singletonD stopp.st_compat stopp.t_absorb)
        apply (metis (mono_tags) insertI1 mem_Collect_eq stopp.t_absorb stopp.tt_idem)
  using Dst singletonD apply fastforce
      apply (metis (mono_tags) insertI1 mem_Collect_eq stopp.s_absorb stopp.ts_compat)
     apply blast
    apply blast
  apply blast
  by blast

end

instantiation set :: (catoid) dioid

begin

instance
  by intro_classes (auto simp: plus_set_def)

end

instantiation set :: (local_catoid) domain_semiring

begin

definition domain_op_set :: "'a set \<Rightarrow> 'a set" where
  "dom X = Src X"

instance
  apply intro_classes
      apply (simp add: Catoid_Lifting.domain_op_set_def times_set_def)
     apply (simp add: domain_op_set_def times_set_def)
    apply (metis (full_types) domain_op_set_def less_eq_def one_set_def stopp.Tgt_subid)
   apply (simp add: Catoid_Lifting.domain_op_set_def zero_set_def)
  by (simp add: Catoid_Lifting.domain_op_set_def image_Un plus_set_def)

end

instantiation set :: (local_catoid) range_semiring

begin

definition range_op_set :: "'a set \<Rightarrow> 'a set" where
  "cod X = Tgt X"

instance
  apply intro_classes
      apply (simp add: Catoid_Lifting.range_op_set_def times_set_def)
     apply (simp add: range_op_set_def times_set_def)
    apply (metis (mono_tags, lifting) Catoid_Lifting.range_op_set_def boolean_algebra.disj_one_right image_Un one_set_def plus_set_def stfix_set stopp.sfix_im)
   apply (simp add: range_op_set_def zero_set_def)
  by (simp add: image_Un plus_set_def range_op_set_def)

end

instantiation set :: (local_catoid) dr_modal_semiring

begin

instance
  by intro_classes (auto simp add: domain_op_set_def range_op_set_def)

end


instantiation set :: (catoid) quantale

begin

instance
  by (intro_classes, auto simp: times_set_def conv_exp)

end

instantiation set :: (local_catoid) domain_quantale

begin

instance
  by intro_classes (simp_all, auto simp add: domain_op_set_def image_Un)

end

instantiation set :: (local_catoid) codomain_quantale

begin

instance
  by intro_classes (simp_all, auto simp add: range_op_set_def image_Un)

end

instantiation set :: (local_catoid) dc_modal_quantale

begin

instance
  by intro_classes simp_all

end

end


























