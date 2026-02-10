theory IsaFoR_Ground_Superposition_Compatibility
imports
  Ground_Superposition_Compatibility
  First_Order_Clause.IsaFoR_Ground_Term_Compatibility
  First_Order_Clause.IsaFoR_Ground_Critical_Pairs
  First_Order_Clause.IsaFoR_KBO
begin

(* TODO: Move *)
abbreviation trivial_tiebreakers ::
  "'t\<^sub>G clause \<Rightarrow> 't clause \<Rightarrow> 't clause \<Rightarrow> bool" where
  "trivial_tiebreakers \<equiv> \<bottom>"

abbreviation trivial_select :: "'a clause \<Rightarrow> 'a clause" where
  "trivial_select _ \<equiv> {#}"

abbreviation ground_less_kbo :: "('f :: weighted) gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" where
  "ground_less_kbo t t' \<equiv> less_kbo (term.from_ground t :: ('f, unit) term) (term.from_ground t')"

interpretation grounded_kbo: context_compatible_nonground_order where 
  less\<^sub>t = "ground_less_kbo :: 'f :: weighted gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" and
  comp_subst = noop_comp_subst and id_subst = noop_id_subst and term_subst = noop_subst and
  term_vars = noop_vars and subst_updates = noop_subst_updates and
  apply_subst = noop_apply_subst and subst_update = noop_subst_update and
  compose_context = "(\<circ>\<^sub>c)" and term_from_ground = id and term_to_ground = id and
  map_context = map_args_actxt and to_ground_context_map = map_args_actxt and
  from_ground_context_map = map_args_actxt and context_to_set = set2_actxt and hole = \<box> and
  apply_context = apply_ground_context and 
  occurences = "\<lambda>_ _. 0" and ground_hole = \<box> and apply_ground_context = apply_ground_context and
  compose_ground_context = "(\<circ>\<^sub>c)" and ground_context_map = map_args_actxt and
  ground_context_to_set = set2_actxt and term_is_ground = noop_is_ground
proof unfold_locales

  show "transp ground_less_kbo"
    using transp_def
    by fastforce
next

  show "asymp ground_less_kbo"
    by fastforce
next

  show "wfp_on (range ground.from_ground) ground_less_kbo"
    using wfp_on_image 
    by auto
next

  show "totalp_on (range ground.from_ground) ground_less_kbo"
    by (meson KBO.term.order.less\<^sub>r_def KBO.term.order.restriction.totalp subset_UNIV
        totalp_on_mono_strong)
next
  fix t and c :: "'f ground_context"

  assume "c \<noteq> \<box>"

  then show "ground_less_kbo t c\<langle>t\<rangle>\<^sub>G"
    using KBO.term.order.less\<^sub>r_def KBO.term.restriction.subterm_property
    by blast
qed simp_all

interpretation grounded_clause: nonground_clause where
  comp_subst = noop_comp_subst and id_subst = noop_id_subst and subst_update = noop_subst_update and
  subst_updates = noop_subst_updates and apply_subst = noop_apply_subst and
  term_subst = noop_subst and term_vars = noop_vars and term_to_ground = id and
  term_from_ground = id and term_is_ground = noop_is_ground
  by unfold_locales

interpretation ground_superposition_compatibility: ground_superposition_compatibility where
  apply_context = apply_ground_context and compose_context = "(\<circ>\<^sub>c)" and hole = \<box> and
  map_context = map_args_actxt and context_to_set = set2_actxt and select = trivial_select and 
  tiebreakers = trivial_tiebreakers and
  less\<^sub>t = "ground_less_kbo :: 'f :: weighted gterm \<Rightarrow> 'f gterm \<Rightarrow> bool"
  by unfold_locales auto

end
