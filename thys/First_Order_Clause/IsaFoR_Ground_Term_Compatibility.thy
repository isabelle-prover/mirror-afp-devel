theory IsaFoR_Ground_Term_Compatibility
  imports
    IsaFoR_Nonground_Context
    Abstract_Substitution.Noop_Substitution
begin

interpretation ground: nonground_term where
  comp_subst = noop_comp_subst and id_subst = noop_id_subst and term_vars = noop_vars and
  subst_update = noop_subst_update and apply_subst = noop_apply_subst and
  term_subst = noop_subst and term_to_ground = id and term_from_ground = id and
  term_is_ground = noop_is_ground
  by unfold_locales (use unit.is_right_invertible_def in simp_all)

interpretation ground: nonground_term_with_context where
  comp_subst = noop_comp_subst and id_subst = noop_id_subst and term_vars = noop_vars and
  subst_update = noop_subst_update and apply_subst = noop_apply_subst and
  term_subst = noop_subst and term_to_ground = id and term_from_ground = id and
  apply_context = apply_ground_context and hole = \<box> and  compose_context = "(\<circ>\<^sub>c)" and
  map_context = map_args_actxt and context_to_set = set2_actxt and ground_hole = \<box> and 
  compose_ground_context = "(\<circ>\<^sub>c)" and to_ground_context_map = map_args_actxt and
  from_ground_context_map = map_args_actxt and ground_context_map = map_args_actxt and
  ground_context_to_set = set2_actxt and apply_ground_context = apply_ground_context and
  occurences = "\<lambda>_ _. 0" and term_is_ground = noop_is_ground
proof unfold_locales

  interpret grounding_lifting where
    comp_subst = noop_comp_subst and id_subst = noop_id_subst and sub_vars = noop_vars and
    apply_subst = noop_apply_subst and to_set = set2_actxt and sub_is_ground = noop_is_ground and
    sub_to_ground = id and sub_from_ground = id and sub_subst = noop_subst and
    map = map_args_actxt and to_ground_map  = map_args_actxt and from_ground_map = map_args_actxt and
    ground_map  = map_args_actxt and to_set_ground = set2_actxt
    by unfold_locales (auto simp: noop_vars_def)

  fix c c' and t :: "'f gterm" and f :: "'f gterm \<Rightarrow> 'f gterm" and \<sigma> and x :: 'v

  show "ground.from_ground c\<langle>t\<rangle>\<^sub>G = (to_ground c)\<langle>ground.from_ground t\<rangle>\<^sub>G"
    by (simp add: to_ground_def)

  show "ground.from_ground c\<langle>t\<rangle>\<^sub>G = (from_ground c)\<langle>ground.from_ground t\<rangle>\<^sub>G"
    by (simp add: from_ground_def)

  show "ground.is_ground c\<langle>t\<rangle>\<^sub>G \<longleftrightarrow> is_ground c  \<and> ground.is_ground t"
    by (simp add: is_ground_def noop_is_ground_def)

  show "map_args_actxt f (c \<circ>\<^sub>c c') = map_args_actxt f c \<circ>\<^sub>c map_args_actxt f c'"
    by (induction c) simp_all

  show "from_ground (c \<circ>\<^sub>c c') = from_ground c \<circ>\<^sub>c from_ground c'"
    by (simp add: from_ground_def)

  show "ground.vars c\<langle>t\<rangle>\<^sub>G = vars c \<union> ground.vars t"
    by (simp add: vars_def noop_vars_def)

  show "noop_subst c\<langle>t\<rangle>\<^sub>G \<sigma> = (subst c \<sigma>)\<langle>noop_subst t \<sigma>\<rangle>\<^sub>G"
    by (simp add: subst_def noop_subst_def)

  show "x \<in> ground.vars t \<Longrightarrow> \<exists>c. t = c\<langle>ground.Var x\<rangle>\<^sub>G"
    by (simp add: noop_vars_def)

  show "\<And>\<gamma> c\<^sub>G t\<^sub>G. noop_subst t \<gamma> = c\<^sub>G\<langle>t\<^sub>G\<rangle>\<^sub>G  \<Longrightarrow>
         (\<exists>c t'. t = c\<langle>t'\<rangle>\<^sub>G \<and> noop_subst t' \<gamma> = t\<^sub>G \<and> local.subst c \<gamma> = c\<^sub>G) \<or> 
         (\<exists>c c\<^sub>G' x. t = c\<langle>ground.Var x\<rangle>\<^sub>G \<and> c\<^sub>G = local.subst c \<gamma> \<circ>\<^sub>c c\<^sub>G')"
    by (simp add: subst_def noop_subst_def)

  show "\<lbrakk>\<exists>t. \<not> ground.is_ground t; ground.is_ground t\<rbrakk> \<Longrightarrow> 0 = Suc 0"
    by (simp add: noop_vars_def)

  show "x \<in> ground.vars t \<longleftrightarrow> (0::nat) < 0"
    by (simp add: noop_vars_def)
qed simp_all

end
