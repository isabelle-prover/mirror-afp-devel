theory DenotationalEquivalences
imports "Denotational-PropsUpd" "Denotational-Props"
begin

lemma disjoint_join_is_update:
  assumes "fdom \<rho>1 = d1"
  assumes "fdom \<rho>2 = d2"
  assumes "d1 \<inter> d2 = {}"
  shows "\<rho>1\<^bsub>[d1 \<union> d2]\<^esub> \<squnion> \<rho>2\<^bsub>[d1 \<union> d2]\<^esub> = \<rho>1 f++ \<rho>2"
proof-
  have disjoint: "fdom \<rho>1 \<inter> fdom \<rho>2 = {}" using assms by auto

  have compat[simp]: "compatible (\<rho>1\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub>) (\<rho>2\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub>)"
  proof (rule compatible_fmapI)
    show "fdom (\<rho>1\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub>) = fdom (\<rho>2\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub>)"
      by simp
    fix x
    assume "x \<in> fdom (\<rho>1\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub>)"
    hence "(x \<in> fdom \<rho>1 \<and> x \<notin> fdom \<rho>2) \<or> (x \<in> fdom \<rho>2 \<and> x \<notin> fdom \<rho>1)" using disjoint by auto
    thus "compatible (\<rho>1\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub> f! x) (\<rho>2\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub> f! x)"
      by auto
  qed
  
  have "\<rho>1 f++ \<rho>2 = \<rho>1\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub> \<squnion> \<rho>2\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub>"
  proof
    show "fdom (\<rho>1 f++ \<rho>2) = fdom (\<rho>1\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub> \<squnion> \<rho>2\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub>)"
      by simp
  next
    fix x
    assume "x \<in> fdom (\<rho>1 f++ \<rho>2)"
    hence "(x \<in> fdom \<rho>1 \<and> x \<notin> fdom \<rho>2) \<or> (x \<in> fdom \<rho>2 \<and> x \<notin> fdom \<rho>1)" using disjoint by auto
    thus "\<rho>1 f++ \<rho>2 f! x = \<rho>1\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub> \<squnion> \<rho>2\<^bsub>[fdom \<rho>1 \<union> fdom \<rho>2]\<^esub> f! x"
      by auto
  qed
  thus ?thesis using assms by simp
qed
   
theorem heap_update_join:
  assumes disjoint: "fdom \<rho> \<inter> heapVars \<Gamma> = {}"
  assumes exp_eq: "\<And> e \<rho>. e \<in> snd ` set \<Gamma> \<Longrightarrow> DenotationalUpd.ESem e \<rho> = Denotational.ESem e \<rho>"
  shows "DenotationalUpd.HSem \<Gamma> \<rho> = Denotational.HSem \<Gamma> \<rho>"
proof-
  have cond: "HSem_cond'' \<Gamma> \<rho>"
    by (rule disjoint_is_HSem_cond[OF disjoint])

  have heapToEnv_eq: "\<And> \<rho>. heapToEnv \<Gamma> (\<lambda>e. DenotationalUpd.ESem e \<rho>) = heapToEnv \<Gamma> (\<lambda>e. Denotational.ESem e \<rho>)"
    by (rule heapToEnv_cong[OF refl exp_eq])

  show ?thesis
    unfolding "Denotational-PropsUpd.HSem_def'" "Denotational.HSem_def'"[OF cond]
    apply (simp add: bottom_of_fjc to_bot_fmap_def)
    apply (rule fix_on_cong[OF fix_on_cond_HSem])
    apply simp
    apply (drule sym)
    apply simp
    apply (subst heapToEnv_eq)
    apply (rule disjoint_join_is_update[OF refl _ disjoint, symmetric])
    apply simp
    done
qed

theorem HSem_join_update:
  "DenotationalUpd.ESem e \<rho> = Denotational.ESem e \<rho>" and "\<And> e. e \<in> snd ` set (asToHeap as) \<Longrightarrow> DenotationalUpd.ESem e \<rho> = Denotational.ESem e \<rho>"
proof(nominal_induct e and  avoiding: \<rho>  rule:exp_assn.strong_induct)
case (Let as e \<rho>)
  have "fdom \<rho> \<inter> heapVars (asToHeap as) = {}"
    by (metis Let(1) disjoint_iff_not_equal sharp_star_Env)
  hence "DenotationalUpd.HSem (asToHeap as) \<rho> = Denotational.HSem (asToHeap as) \<rho>"
    by (rule heap_update_join[OF _ Let(2)])
  thus ?case using Let(1,3) by simp
qed auto
end
