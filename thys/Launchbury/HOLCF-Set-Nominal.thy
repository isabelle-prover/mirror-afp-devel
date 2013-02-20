theory "HOLCF-Set-Nominal"
imports "HOLCF-Set" "HOLCF-Join" "Nominal-HOLCF"
begin

subsubsection {* Equivariance of @{theory "HOLCF-Set"} and @{theory "HOLCF-Join"} definitions *}

lemma subcpo_eqvt[eqvt]:
  fixes S :: "('a::cont_pt) set"
  assumes "subcpo S"
  shows "subcpo (\<pi> \<bullet> S)"
proof(rule subcpoI)
  fix Y :: "nat \<Rightarrow> 'a"
  assume "chain Y"
    hence "chain (-\<pi> \<bullet> Y)" by (rule chain_eqvt)
  moreover
  assume "\<And> i. Y i \<in> \<pi> \<bullet> S"
  hence "\<And> i. - \<pi> \<bullet> Y i \<in> S" by (metis (full_types) mem_permute_iff permute_minus_cancel(1))
  hence "\<And> i. (- \<pi> \<bullet> Y) i \<in> S" by (metis eqvt_apply permute_pure)
  ultimately
  have "(\<Squnion> i. (- \<pi> \<bullet> Y) i) \<in> S" by (metis subcpo.cpo[OF assms])
  hence "\<pi> \<bullet> (\<Squnion> i. (- \<pi> \<bullet> Y) i) \<in> \<pi> \<bullet> S"  by (metis mem_permute_iff)
  thus "(\<Squnion> i. Y i) \<in> \<pi> \<bullet> S"
    apply -
    apply (subst (asm) cont2contlubE[OF perm_cont `chain (-\<pi> \<bullet> Y)`])
    by (metis image_image permute_minus_cancel(1) permute_set_eq_image range_eqvt)
qed

lemma subpcpo_bot_eqvt[eqvt]:
  fixes S :: "('a::cont_pt) set"
  assumes "subpcpo_bot S b"
  shows "subpcpo_bot (\<pi> \<bullet> S) (\<pi> \<bullet> b)"
  apply (rule subpcpo_botI)
  apply (metis subcpo.cpo[OF subcpo_eqvt[OF subpcpo_is_subcpo[OF subpcpo_bot_is_subpcpo[OF assms]]]])
  apply (metis bottom_of_subpcpo_bot_there[OF assms] mem_permute_iff)
  apply (metis (full_types) bottom_of_subpcpo_bot_minimal[OF assms] eqvt_bound mem_permute_iff perm_cont_simp)
  done

lemma subpcpo_eqvt[eqvt]:
  fixes S :: "('a::cont_pt) set"
  assumes "subpcpo S"
  shows "subpcpo (\<pi> \<bullet> S)"
  by (rule subpcpo_bot_is_subpcpo[OF subpcpo_bot_eqvt[OF subpcpo_is_subpcpo_bot[OF assms]]])

lemma bottom_of_eqvt:
  assumes "subpcpo S"
  shows "\<pi> \<bullet> (bottom_of (S ::('a::cont_pt) set)) = bottom_of (\<pi> \<bullet> S)"
  by (rule bottom_of_subpcpo_bot[symmetric, OF subpcpo_bot_eqvt[OF  subpcpo_is_subpcpo_bot[OF assms]]])

lemma closed_on_eqvt:
  "closed_on S F \<Longrightarrow> closed_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)"
  apply (rule closed_onI)
  apply (simp add: permute_set_def)
  by (metis closed_onE eqvt_apply)

lemma cont_eqvt[eqvt]:
  "cont (F::'a::cont_pt \<Rightarrow> 'b::cont_pt) \<Longrightarrow> cont (\<pi> \<bullet> F)"
  apply (rule contI)
  apply (drule_tac Y = "unpermute \<pi> Y" in contE)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply (drule perm_is_lub_eqvt[of _ _ "\<pi>"])
  apply (subst (asm) eqvt_apply[of _ F])
  apply (subst (asm) lub_eqvt)
  apply (rule cpo)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply perm_simp
  apply assumption
  done

lemma chain_on_eqvt:
  "chain_on (S::'a::cont_pt set) Y \<Longrightarrow> chain_on (\<pi> \<bullet> S) (\<pi> \<bullet> Y)"
  apply (rule chain_onI)
  apply (drule_tac i = i in chain_onE)
  apply (metis perm_cont_simp permute_fun_app_eq permute_pure)
  apply (drule_tac i = i in chain_on_is_on)
  by (metis (full_types) mem_permute_iff permute_fun_app_eq permute_pure)

lemma cont_on_eqvt:
  "cont_on S (F::'a::cont_pt \<Rightarrow> 'b::cont_pt) \<Longrightarrow> cont_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)"
  apply (rule cont_onI)
  apply (drule_tac Y = "unpermute \<pi> Y" in cont_onE)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply (metis chain_on_eqvt permute_minus_cancel(2))
  apply (drule perm_is_lub_eqvt[of _ _ "\<pi>"])
  apply (subst (asm) eqvt_apply[of _ F])
  apply (subst (asm) lub_eqvt)
  apply (rule cpo)
  apply (drule chain_on_is_chain)
  apply (auto intro: chain_eqvt simp add: unpermute_def)[1]
  apply perm_simp
  apply assumption
  done


lemma fix_on_cond_eqvt:
  assumes "fix_on_cond S (b::'a::cont_pt) F"
  shows "fix_on_cond (\<pi> \<bullet> S) (\<pi> \<bullet> b) (\<pi> \<bullet> F)"
proof
  from assms
  have pcpo1: "subpcpo S" and closed: "closed_on S F" and cont: "cont_on S F" and [simp]:"b = bottom_of S"
    by (metis fix_on_cond.cases)+

  show "subpcpo (\<pi> \<bullet> S)" by (rule subpcpo_eqvt[OF pcpo1])
  show "bottom_of (\<pi> \<bullet> S) = \<pi> \<bullet> b" by (simp add: bottom_of_eqvt[OF pcpo1, symmetric])
  show "closed_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)" by (rule closed_on_eqvt[OF closed])
  show "cont_on (\<pi> \<bullet> S) (\<pi> \<bullet> F)" by (rule cont_on_eqvt[OF cont])
qed

lemma fix_on_eqvt:
  assumes "fix_on_cond S (b::'a::cont_pt) F"
  shows "\<pi> \<bullet> (fix_on' b F) = fix_on' (\<pi> \<bullet> b) (\<pi> \<bullet> F)"
proof-
  have permuted: "fix_on_cond (\<pi> \<bullet> S) (\<pi> \<bullet> b :: 'a ::cont_pt) (\<pi> \<bullet> F)"
    by (rule fix_on_cond_eqvt[OF assms])
  show ?thesis
    apply (rule parallel_fix_on_ind[OF assms permuted _ refl])
    apply (rule adm_is_adm_on)
    apply (rule adm_eq[OF cont_compose[OF perm_cont cont_fst] cont_snd])
    by auto
qed

lemma to_bot_eqvt[eqvt,simp]: "\<pi> \<bullet> to_bot (\<rho>::'a::{subpcpo_partition,cont_pt}) = to_bot (\<pi> \<bullet> \<rho>)"
proof(rule below_antisym)
  show "to_bot (\<pi> \<bullet> \<rho>) \<sqsubseteq> \<pi> \<bullet> to_bot \<rho>"
    by (metis perm_cont_simp to_bot_minimal unrelated)
  show "\<pi> \<bullet> to_bot \<rho> \<sqsubseteq> to_bot (\<pi> \<bullet> \<rho>)"
    by (metis eqvt_bound perm_cont_simp to_bot_minimal unrelated)
qed

lemma compatible_eqvt[eqvt]:
  "compatible (x::'a::cont_pt) y \<Longrightarrow> compatible (\<pi> \<bullet> x) (\<pi> \<bullet> y)"
  unfolding compatible_def
  by (metis empty_eqvt insert_eqvt perm_is_lub_simp)

lemma join_eqvt[simp,eqvt]:
  "\<pi> \<bullet> ((x::'a::{cont_pt}) \<squnion> y) = (\<pi> \<bullet> x) \<squnion> (\<pi> \<bullet> y)"
proof (cases "\<exists> z. {x, y} <<| z")
case False
  hence "\<not> (\<exists> z. {\<pi> \<bullet> x, \<pi> \<bullet> y} <<| z)" by (metis perm_is_lub_simp empty_eqvt insert_eqvt eqvt_bound)
  thus ?thesis using False unfolding cpo_class.join_def by auto
next
case True
  hence "\<exists> z. {\<pi> \<bullet> x, \<pi> \<bullet> y} <<| z" by (metis perm_is_lub_simp empty_eqvt insert_eqvt)
  thus ?thesis using True unfolding cpo_class.join_def by (auto simp add: empty_eqvt insert_eqvt)
qed
end

