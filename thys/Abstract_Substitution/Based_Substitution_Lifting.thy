theory Based_Substitution_Lifting \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 
  imports 
    Based_Substitution
    Substitution_Lifting
begin

section \<open>Lifting of based substitutions\<close>

locale based_substitution_lifting =
  substitution_lifting +
  base: base_substitution where subst = base_subst and vars = base_vars +
  sub: based_substitution where subst = sub_subst and vars = sub_vars
begin

sublocale based_substitution where subst = subst and vars = vars
proof unfold_locales
  fix expr \<rho>

  show "vars (expr \<cdot> \<rho>) = \<Union> (base_vars ` (\<lambda>x. x \<cdot>v \<rho>) ` vars expr)"
    using sub.vars_subst
    unfolding subst_def vars_def
    by simp
qed simp

end

subsection \<open>Lifting of properties\<close>

locale variables_in_base_imgu_lifting =
  based_substitution_lifting +
  sub: variables_in_base_imgu where vars = sub_vars and subst = sub_subst
begin

sublocale variables_in_base_imgu where subst = subst and vars = vars
proof unfold_locales
  fix expr \<mu> XX
  assume imgu: "base.is_imgu \<mu> XX" "finite XX" "\<forall>X \<in> XX. finite X"

  show "vars (expr \<cdot> \<mu>) \<subseteq> vars expr \<union> \<Union> (base_vars ` \<Union> XX)"
    using sub.variables_in_base_imgu[OF imgu]
    unfolding vars_def subst_def to_set_map
    by auto
qed

end

end
