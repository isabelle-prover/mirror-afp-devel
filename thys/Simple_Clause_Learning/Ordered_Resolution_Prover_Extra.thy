theory Ordered_Resolution_Prover_Extra
  imports
    "Ordered_Resolution_Prover.Abstract_Substitution"
begin

section \<open>Abstract Substitution Extra\<close>

lemma (in substitution_ops) subst_atm_of_eqI:
  "L \<cdot>l \<sigma>\<^sub>L = K \<cdot>l \<sigma>\<^sub>K \<Longrightarrow> atm_of L \<cdot>a \<sigma>\<^sub>L = atm_of K \<cdot>a \<sigma>\<^sub>K"
  by (cases L; cases K) (simp_all add: subst_lit_def)

lemma (in substitution_ops) subst_atm_of_eq_compI:
  "L \<cdot>l \<sigma> = - (L' \<cdot>l \<sigma>) \<Longrightarrow> atm_of L \<cdot>a \<sigma> = atm_of L' \<cdot>a \<sigma>"
  by (cases L; cases L') (simp_all add: uminus_literal_def subst_lit_def)

lemma (in substitution_ops) set_mset_subst_cls_conv: "set_mset (C \<cdot> \<sigma>) = (\<lambda>L. L \<cdot>l \<sigma>) ` set_mset C"
  by (simp add: subst_cls_def)

lemma (in substitution_ops) is_ground_cls_add_mset[simp]:
  "is_ground_cls (add_mset L C) \<longleftrightarrow> is_ground_lit L \<and> is_ground_cls C"
  by (auto simp: is_ground_cls_def)

lemma (in substitution_ops) grounding_of_clss_empty[simp]: "grounding_of_clss {} = {}"
  by (simp add: grounding_of_clss_def)

lemma (in substitution_ops) grounding_of_clss_singleton[simp]: "grounding_of_clss {C} = grounding_of_cls C"
  by (simp add: grounding_of_clss_def)

lemma (in substitution_ops) grounding_of_clss_insert:
  "grounding_of_clss (insert C N) = grounding_of_cls C \<union> grounding_of_clss N"
  by (simp add: grounding_of_clss_def)

lemma (in substitution_ops) grounding_of_clss_union:
  "grounding_of_clss (A \<union> B) = grounding_of_clss A \<union> grounding_of_clss B"
  by (simp add: grounding_of_clss_def)

lemma (in substitution) grounding_of_subst_cls_renaming_ident[simp]:
  assumes "is_renaming \<rho>"
  shows "grounding_of_cls (C \<cdot> \<rho>) = grounding_of_cls C"
  by (metis (no_types, lifting) assms subset_antisym subst_cls_comp_subst
      subst_cls_eq_grounding_of_cls_subset_eq subst_cls_id_subst is_renaming_def)

lemma (in substitution) grounding_of_subst_cls_subset: "grounding_of_cls (C \<cdot> \<mu>) \<subseteq> grounding_of_cls C"
proof (rule subsetI)
  fix D
  assume "D \<in> grounding_of_cls (C \<cdot> \<mu>)"
  then obtain \<gamma> where D_def: "D = C \<cdot> \<mu> \<cdot> \<gamma>" and gr_\<gamma>: "is_ground_subst \<gamma>"
    unfolding grounding_of_cls_def mem_Collect_eq by auto

  show "D \<in> grounding_of_cls C"
    unfolding grounding_of_cls_def mem_Collect_eq D_def
    using is_ground_comp_subst[OF gr_\<gamma>, of \<mu>]
    by force
qed

lemma (in substitution) grounding_of_subst_clss_subset: "grounding_of_clss (CC \<cdot>cs \<mu>) \<subseteq> grounding_of_clss CC"
  using grounding_of_subst_cls_subset
  by (auto simp: grounding_of_clss_def subst_clss_def)


lemma (in substitution) grounding_of_subst_clss_renaming_ident[simp]:
  assumes "is_renaming \<rho>"
  shows "grounding_of_clss (CC \<cdot>cs \<rho>) = grounding_of_clss CC"
  by (metis assms dual_order.eq_iff grounding_of_subst_clss_subset
      is_renaming_inv_renaming_cancel_clss)

lemma (in substitution) is_ground_cls_if_in_grounding_of_cls: "C' \<in> grounding_of_cls C \<Longrightarrow> is_ground_cls C'"
  using grounding_ground grounding_of_clss_singleton by blast

lemma (in substitution) image_grounding_of_cls_grounding_of_cls:
  "grounding_of_cls ` grounding_of_cls C = (\<lambda>x. {x}) ` grounding_of_cls C"
proof (rule image_cong)
  show "\<And>x. x \<in> grounding_of_cls C \<Longrightarrow> grounding_of_cls x = {x}"
    using grounding_of_cls_ground is_ground_cls_if_in_grounding_of_cls by blast
qed simp

lemma (in substitution) grounding_of_clss_grounding_of_clss[simp]:
  "grounding_of_clss (grounding_of_clss N) = grounding_of_clss N"
  unfolding grounding_of_clss_def UN_UN_flatten
  unfolding image_grounding_of_cls_grounding_of_cls
  by simp

lemma (in substitution) is_ground_clss_grounding_of_clss[simp]: "is_ground_clss (grounding_of_clss N)"
  using grounding_of_clss_def union_grounding_of_cls_ground by metis

lemma (in substitution) generalizes_lit_refl[simp]: "generalizes_lit L L"
  unfolding generalizes_lit_def by (rule exI[of _ id_subst]) simp

lemma (in substitution) generalizes_lit_trans:
  "generalizes_lit L1 L2 \<Longrightarrow> generalizes_lit L2 L3 \<Longrightarrow> generalizes_lit L1 L3"
  unfolding generalizes_lit_def using subst_lit_comp_subst by blast


end