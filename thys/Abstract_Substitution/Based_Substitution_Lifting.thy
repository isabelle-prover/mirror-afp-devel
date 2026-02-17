theory Based_Substitution_Lifting \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 
  imports 
    Based_Substitution
    Substitution_Lifting
begin

section \<open>Lifting of based substitutions\<close>

locale based_substitution_lifting =
  substitution_lifting +
  base: base_substitution where 
  subst = base_subst and vars = base_vars and is_ground = base_is_ground +
  sub: based_substitution where
  subst = sub_subst and vars = sub_vars and is_ground = sub_is_ground
begin

sublocale based_substitution where subst = subst and vars = vars and is_ground = is_ground
proof unfold_locales
  fix expr \<rho>

  show "vars (expr \<cdot> \<rho>) = \<Union> (base_vars ` (\<lambda>x. x \<cdot>v \<rho>) ` vars expr)"
    using sub.vars_subst
    unfolding subst_def vars_def
    by simp
next
  fix expr \<gamma> 
  assume "is_ground (expr \<cdot> \<gamma>)" 

  then show "\<forall>x\<in>vars expr. base_is_ground (x \<cdot>v \<gamma>)"
    unfolding is_ground_def vars_def
    using sub.variable_grounding
    by auto
qed simp

end

subsection \<open>Lifting of properties\<close>

locale variables_in_base_imgu_lifting =
  based_substitution_lifting +
  sub: variables_in_base_imgu where
  vars = sub_vars and subst = sub_subst and is_ground = sub_is_ground
begin

sublocale variables_in_base_imgu where subst = subst and vars = vars and is_ground = is_ground
proof unfold_locales
  fix expr \<mu> XX
  assume imgu: "base.is_imgu \<mu> XX" "finite XX" "\<forall>X \<in> XX. finite X"

  show "vars (expr \<cdot> \<mu>) \<subseteq> vars expr \<union> \<Union> (base_vars ` \<Union> XX)"
    using sub.variables_in_base_imgu[OF imgu]
    unfolding vars_def subst_def to_set_map
    by auto
qed

end

locale based_subst_update_lifting =
  based_substitution_lifting +
  subst_update_lifting +
  sub: based_subst_update where
  vars = sub_vars and subst = sub_subst and is_ground = sub_is_ground
begin

sublocale based_subst_update where subst = subst and vars = vars and is_ground = is_ground
proof unfold_locales
  fix update expr \<gamma> x
  assume "base_is_ground update" "is_ground (expr \<cdot> \<gamma>)" "x \<in> vars expr"
  
  then show "is_ground (expr \<cdot> \<gamma>\<lbrakk>x := update\<rbrakk>)"
    using sub.ground_subst_update_in_vars
    unfolding is_ground_def subst_def
    by auto
qed

end

locale vars_grounded_iff_is_grounding_lifting = 
  based_substitution_lifting +
  sub: vars_grounded_iff_is_grounding where
  vars = sub_vars and subst = sub_subst and is_ground = sub_is_ground
begin

sublocale vars_grounded_iff_is_grounding where
  subst = subst and vars = vars and is_ground = is_ground
  using sub.is_grounding_if_vars_grounded
  by unfold_locales (simp add: vars_def is_ground_def subst_def)

end

end
