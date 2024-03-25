(*
Title: Cubical Omega-Zero-Categories with Connections
Authors: Tanguy Massacrier, Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section\<open>Cubical $(\omega,0)$-Categories with Connections\<close>

theory CubicalOmegaZeroCategoriesConnections
  imports CubicalCategoriesConnections

begin

text \<open>All categories considered in this component are single-set categories.\<close>

text \<open>First we define shell-invertibility.\<close>

abbreviation (in cubical_omega_category_connections) "ri_inv i x y \<equiv> (DD i x y \<and> DD i y x \<and> x \<otimes>\<^bsub>i\<^esub> y = \<partial> i ff x \<and> y \<otimes>\<^bsub>i\<^esub> x = \<partial> i tt x)"

abbreviation (in cubical_omega_category_connections) "ri_inv_shell k i x \<equiv> (\<forall>j \<alpha>. j + 1 \<le> k \<and> j \<noteq> i \<longrightarrow> (\<exists>y. ri_inv i (\<partial> j \<alpha> x) y))"

text \<open>Next we define the class of cubical $(\omega,0)$-categories with connections.\<close>

class cubical_omega_zero_category_connections = cubical_omega_category_connections +
  assumes ri_inv: "k \<ge> 1 \<Longrightarrow> i \<le> k - 1 \<Longrightarrow> dim_bound k x \<Longrightarrow> ri_inv_shell k i x \<Longrightarrow> \<exists>y. ri_inv i x y"

begin

text \<open>Finally, to show our axiomatisation at work we prove Proposition 2.4.7 from our companion paper, namely that every
cell in an $(\omega,0)$-category is ri-invertible for each natural number i. This requires some background theory engineering.\<close>

lemma ri_inv_fix:
  assumes "fFx i x"
  shows "\<exists>y. ri_inv i x y"
  by (metis assms icat.st_local local.face_compat_var local.icat.sscatml.l0_absorb)

lemma ri_inv2:
  assumes "k \<ge> 1"
  assumes "dim_bound k x"
  and "ri_inv_shell k i x"
  shows "\<exists>y. ri_inv i x y"
  proof (cases "i \<le> k - 1")
  case True
  thus ?thesis
    using assms local.ri_inv by simp
next
  case False
  hence "fFx i x"
    using assms(2) by fastforce
  thus ?thesis
    using ri_inv_fix by simp
qed

lemma ri_inv3: 
  assumes "dim_bound k x"
  and "ri_inv_shell k i x"
  shows "\<exists>y. ri_inv i x y"
proof (cases "k = 0")
  case True
  thus ?thesis
    using assms(1) less_eq_nat.simps(1) ri_inv_fix by simp
next
  case False
  hence "k \<ge> 1"
    by simp
  thus ?thesis
    using assms ri_inv2 by simp
qed

lemma ri_unique: "(\<exists>y. ri_inv i x y) = (\<exists>!y. ri_inv i x y)"
  by (metis local.icat.pcomp_assoc local.icat.sscatml.assoc_defined local.icat.sscatml.l0_absorb local.icat.sts_msg.st_local local.pcomp_uface)

lemma ri_unique_var: "ri_inv i x y \<Longrightarrow> ri_inv i x z \<Longrightarrow> y = z"
  using ri_unique by fastforce

definition "ri i x = (THE y. ri_inv i x y)"

lemma ri_inv_ri: "ri_inv i x y \<Longrightarrow> (y = ri i x)"
proof-
  assume a: "ri_inv i x y"
  hence "\<exists>!y. ri_inv i x y"
    using ri_unique by blast
  thus "y = ri i x"
    unfolding ri_def 
    by (smt (verit, ccfv_threshold) a the_equality)
qed

lemma ri_def_prop:
  assumes "dim_bound k x"
  and "ri_inv_shell k i x"
shows "DD i x (ri i x) \<and> DD i (ri i x) x \<and> x \<otimes>\<^bsub>i\<^esub> (ri i x) = \<partial> i ff x \<and> (ri i x) \<otimes>\<^bsub>i\<^esub> x = \<partial> i tt x"
proof-
  have "\<exists>y. ri_inv i x y"
    using assms ri_inv3 by blast
  hence "\<exists>!y. DD i x y \<and> DD i y x \<and> x \<otimes>\<^bsub>i\<^esub> y = \<partial> i ff x \<and> y \<otimes>\<^bsub>i\<^esub> x = \<partial> i tt x"
    by (simp add: ri_unique)
  hence "DD i x (ri i x) \<and> DD i (ri i x) x \<and> x \<otimes>\<^bsub>i\<^esub> (ri i x) = \<partial> i ff x \<and> (ri i x) \<otimes>\<^bsub>i\<^esub> x = \<partial> i tt x"
    unfolding ri_def by (smt (verit, del_insts) theI')
  thus ?thesis
    by simp
qed

lemma ri_right:
  assumes "dim_bound k x"
  and "ri_inv_shell k i x"
  shows "x \<otimes>\<^bsub>i\<^esub> ri i x = \<partial> i ff x"
  using assms ri_def_prop by simp

lemma ri_right_set:
  assumes "dim_bound k x"
  and "ri_inv_shell k i x"
  shows "x \<odot>\<^bsub>i\<^esub> ri i x = {\<partial> i ff x}"
  using assms local.icat.pcomp_def_var3 ri_def_prop by blast

lemma ri_left:
  assumes "dim_bound k x"
  and "ri_inv_shell k i x"
  shows "ri i x \<otimes>\<^bsub>i\<^esub> x = \<partial> i tt x"
  using assms ri_def_prop by simp

lemma ri_left_set:
  assumes "dim_bound k x"
  and "ri_inv_shell k i x"
  shows "ri i x \<odot>\<^bsub>i\<^esub> x = {\<partial> i tt x}"
  using assms local.icat.pcomp_def_var3 ri_def_prop by blast

lemma dim_face: "dim_bound k x \<Longrightarrow> dim_bound k (\<partial> i \<alpha> x)"
  by (metis local.double_fix_prop local.face_comm_var)

lemma dim_ri_inv:
  assumes "dim_bound k x"
  and "ri_inv i x y"
  shows "dim_bound k y"
proof-
  {fix l \<alpha>
  assume ha: "l \<ge> k"
  have h1: "DD i x (\<partial> l \<alpha> y)"
    by (smt (verit, ccfv_threshold) assms ha icat.st_local icid.s_absorb_var3 local.pcomp_face_func_DD)
  have h2: "DD i (\<partial> l \<alpha> y) x"
    by (metis (full_types) assms ha icid.ts_compat local.iDst local.locality local.pcomp_face_func_DD)
  have "\<partial> l \<alpha> (x \<otimes>\<^bsub>i\<^esub> y) = \<partial> l \<alpha> x \<otimes>\<^bsub>i\<^esub> \<partial> l \<alpha> y"
    by (metis ha assms(1) assms(2) local.fFx_prop local.face_func local.icat.sscatml.r0_absorb local.pcomp_uface)
  hence h3: "\<partial> l \<alpha> (x \<otimes>\<^bsub>i\<^esub> y) = x \<otimes>\<^bsub>i\<^esub> \<partial> l \<alpha> y"
    by (metis assms(1) ha local.face_compat_var)
  have "\<partial> l \<alpha> (y \<otimes>\<^bsub>i\<^esub> x) = \<partial> l \<alpha> y \<otimes>\<^bsub>i\<^esub> \<partial> l \<alpha> x"
    by (metis ha assms(1) assms(2) local.fFx_prop local.face_func local.icat.sscatml.r0_absorb local.pcomp_uface)
  hence "\<partial> l \<alpha> (y \<otimes>\<^bsub>i\<^esub> x) = \<partial> l \<alpha> y \<otimes>\<^bsub>i\<^esub> x"
    by (metis assms(1) ha local.face_compat_var)
  hence "ri_inv i x (\<partial> l \<alpha> y)"
    by (smt (z3) assms(1) assms(2) h1 h2 h3 ha icid.ts_compat local.face_comm_var)
  hence "\<partial> l \<alpha> y = y"
    using ri_unique_var assms(2) by blast}
  thus ?thesis
    by simp
qed

lemma every_dim_k_ri_inv:
  assumes "dim_bound k x"
  shows "\<forall>i. \<exists>y. ri_inv i x y" using \<open>dim_bound k x\<close>
proof (induct k arbitrary: x)
  case 0
  thus ?case 
    using ri_inv_fix by simp
next
  case (Suc k)
  {fix i
    have "\<exists>y. ri_inv i x y"
    proof (cases "Suc k \<le> i")
      case True 
      thus ?thesis
        using Suc.prems ri_inv_fix by simp
    next
      case False
      {fix j \<alpha>
        assume h: "j \<le> k \<and> j \<noteq> i"
        hence a: "dim_bound k (\<Sigma> j (k - j) (\<partial> j \<alpha> x))"
          by (smt (z3) Suc.prems antisym_conv2 le_add_diff_inverse local.face_comm_var local.face_compat_var local.symcomp_face2 local.symcomp_type_var nle_le not_less_eq_eq)
        have "\<exists>y. ri_inv i (\<partial> j \<alpha> x) y"
        proof (cases "j < i")
          case True
          obtain y where b: "ri_inv (i - 1) (\<Sigma> j (k - j) (\<partial> j \<alpha> x)) y"
            using Suc.hyps a by force
          have c: "dim_bound k y"
            apply (rule dim_ri_inv[where x = "\<Sigma> j (k - j) (\<partial> j \<alpha> x)"])
            using a b by simp_all 
          hence d: "DD i (\<partial> j \<alpha> x) (\<Theta> j (k - j) y)"
            by (smt (verit) False True a b h icid.ts_compat le_add_diff_inverse local.iDst local.icid.stopp.ts_compat local.inv_symcomp_face1 local.inv_symcomp_symcomp local.locality nle_le not_less_eq_eq)
          hence e: "DD i (\<Theta> j (k - j) y) (\<partial> j \<alpha> x)"
            by (smt (verit) False True b c dual_order.refl h icid.ts_compat le_add_diff_inverse local.iDst local.icid.stopp.ts_compat local.inv_symcomp_face1 local.inv_symcomp_symcomp local.locality local.symcomp_type_var not_less_eq_eq)
          have f: "\<partial> j \<alpha> x \<otimes>\<^bsub>i\<^esub> \<Theta> j (k - j) y = \<Theta> j (k - j) (\<Sigma> j (k - j) (\<partial> j \<alpha> x) \<otimes>\<^bsub>(i - 1)\<^esub> y)"
            apply (subst inv_symcomp_comp4)
            using True local.symcomp_type_var1 c False One_nat_def b local.face_compat_var local.inv_symcomp_symcomp a by auto
          have "\<Theta> j (k - j) y \<otimes>\<^bsub>i\<^esub> \<partial> j \<alpha> x = \<Theta> j (k - j) (y \<otimes>\<^bsub>(i - 1)\<^esub> \<Sigma> j (k - j) (\<partial> j \<alpha> x))"
            apply (subst inv_symcomp_comp4)
            using True local.symcomp_type_var1 b c False local.face_compat_var local.inv_symcomp_symcomp a by simp_all
          thus ?thesis
            by (metis False True b c d dual_order.refl e f h le_add_diff_inverse local.icid.stopp.Dst local.inv_symcomp_face1 not_less_eq_eq)
        next
          case False
          obtain y where b: "ri_inv i (\<Sigma> j (k - j) (\<partial> j \<alpha> x)) y"
            using Suc.hyps a by presburger
          have c: "dim_bound k y"
            apply (rule dim_ri_inv[where x = "\<Sigma> j (k - j) (\<partial> j \<alpha> x)"])
            using a b by simp_all
          hence d: "DD i (\<partial> j \<alpha> x) (\<Theta> j (k - j) y)"
            by (smt (verit) False a b dual_order.refl h icid.ts_compat le_add_diff_inverse linorder_neqE_nat local.iDst local.icid.stopp.ts_compat local.inv_symcomp_face2 local.inv_symcomp_symcomp local.locality)
          hence e: "DD i (\<Theta> j (k - j) y) (\<partial> j \<alpha> x)"
            by (smt (z3) False add.commute b c dual_order.refl h le_add_diff_inverse2 linorder_neqE_nat local.face_comm_var local.face_compat_var local.iDst local.inv_symcomp_face2 local.inv_symcomp_symcomp local.locality local.symcomp_face2)
          have f: "\<partial> j \<alpha> x \<otimes>\<^bsub>i\<^esub> \<Theta> j (k - j) y = \<Theta> j (k - j) (\<Sigma> j (k - j) (\<partial> j \<alpha> x) \<otimes>\<^bsub>i\<^esub> y)"
            apply (subst inv_symcomp_comp2)
            using False h nat_neq_iff local.symcomp_type_var1 b c a local.face_compat_var local.inv_symcomp_symcomp by simp_all
          have "\<Theta> j (k - j) y \<otimes>\<^bsub>i\<^esub> \<partial> j \<alpha> x = \<Theta> j (k - j) (y \<otimes>\<^bsub>i\<^esub> \<Sigma> j (k - j) (\<partial> j \<alpha> x))"
            apply (subst inv_symcomp_comp2)
            using False h a b c local.inv_symcomp_symcomp by simp_all
          thus ?thesis
            by (metis False antisym_conv3 b d e f h local.face_compat_var local.inv_symcomp_face2 local.inv_symcomp_symcomp local.symcomp_type_var1)
        qed}
      thus ?thesis
        apply (intro ri_inv[where k = "k + 1"])
        using False Suc.prems by simp_all
    qed}
  thus ?case
    by simp
qed

text \<open>We can now show that every cell is ri-invertible in every direction i.\<close>

lemma every_ri_inv: "\<exists>y. ri_inv i x y"
  using every_dim_k_ri_inv local.fin_fix by blast

end

end