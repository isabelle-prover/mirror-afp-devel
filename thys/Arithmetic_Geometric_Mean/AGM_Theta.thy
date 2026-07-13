(*
  File:     AGM_Theta.thy
  Author:   Manuel Eberl, University of Innsbruck
*)
section \<open>Relating the complete elliptic integral to the Jacobi theta functions\<close>
theory AGM_Theta
  imports "Theta_Functions.Theta_Nullwert" Arithmetic_Geometric_Mean_Integral
begin

text \<open>
  The Jacobi theta nullwert functions have the property that 
  $(\vartheta_3(q)^2, \vartheta_4(q)^2)$ is transformed by a single step of the AGM iteration
  into $(\vartheta_3(q^2)^2, \vartheta_4(q^2)^2)$. Clearly, for $n\to\infty$, this converges
  to $(\vartheta_3(0)^2,\vartheta_4(0)^2) = (1,1)$.
\<close>
lemma agm_seq_jacobi_theta_00_01_square_real:
  fixes q :: real
  assumes "q \<in> {-1<..<1}"
  shows   "agm_seq (\<theta>\<^sub>3 q ^ 2) (\<theta>\<^sub>4 q ^ 2) n = (\<theta>\<^sub>3 (q ^ (2 ^ n)) ^ 2, \<theta>\<^sub>4 (q ^ (2 ^ n)) ^ 2)"
  using assms
proof (induction n arbitrary: q)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have "agm_seq ((\<theta>\<^sub>3 q)\<^sup>2) ((\<theta>\<^sub>4 q)\<^sup>2) (Suc n) =
          agm_seq (amean ((\<theta>\<^sub>3 q)\<^sup>2) ((\<theta>\<^sub>4 q)\<^sup>2)) (gmean ((\<theta>\<^sub>3 q)\<^sup>2) ((\<theta>\<^sub>4 q)\<^sup>2)) n"
    by (simp add: agm_seq_rec)
  also have "amean ((\<theta>\<^sub>3 q)\<^sup>2) ((\<theta>\<^sub>4 q)\<^sup>2) = (\<theta>\<^sub>3 (q\<^sup>2))\<^sup>2"
    unfolding amean_eq_midpoint using jacobi_theta_nw_00_plus_01_square_real[of q]
    by (simp add: midpoint_def)
  also have "gmean ((\<theta>\<^sub>3 q)\<^sup>2) ((\<theta>\<^sub>4 q)\<^sup>2) = \<theta>\<^sub>3 q * \<theta>\<^sub>4 q"
    using jacobi_theta_nw_00_nonneg[of q] jacobi_theta_nw_01_nonneg[of q] Suc.prems
    by (simp add: gmean_real_def flip: power_mult_distrib)
  also have "\<dots> = (\<theta>\<^sub>4 (q\<^sup>2))\<^sup>2"
    by (rule jacobi_theta_nw_00_times_01_real)
  also have "agm_seq ((\<theta>\<^sub>3 (q\<^sup>2))\<^sup>2) ((\<theta>\<^sub>4 (q\<^sup>2))\<^sup>2) n = ((\<theta>\<^sub>3 (q ^ 2 ^ Suc n))\<^sup>2, (\<theta>\<^sub>4 (q ^ 2 ^ Suc n))\<^sup>2)"
  proof (subst Suc.IH) 
    have "\<bar>q ^ 2\<bar> < 1"
      unfolding power_abs by (subst power_less_one_iff) (use Suc.prems in auto)
    thus "q ^ 2 \<in> {-1<..<1}"
      unfolding greaterThanLessThan_iff by linarith
  qed (simp_all add: power_mult)
  finally show ?case .
qed

lemma agm_jacobi_theta_00_01_square_real:
  fixes q :: real
  assumes "q \<in> {-1<..<1}"
  shows   "agm (\<theta>\<^sub>3 q ^ 2) (\<theta>\<^sub>4 q ^ 2) = 1"
proof -
  have "(fst \<circ> agm_seq (\<theta>\<^sub>3 q ^ 2) (\<theta>\<^sub>4 q ^ 2)) \<longlonglongrightarrow> agm (\<theta>\<^sub>3 q ^ 2) (\<theta>\<^sub>4 q ^ 2)"
    by (rule tendsto_agm1_real) auto
  also have "(fst \<circ> agm_seq (\<theta>\<^sub>3 q ^ 2) (\<theta>\<^sub>4 q ^ 2)) = (\<lambda>n. \<theta>\<^sub>3 (q ^ (2 ^ n)) ^ 2)"
    using assms by (simp add: agm_seq_jacobi_theta_00_01_square_real o_def)
  finally have "(\<lambda>n. \<theta>\<^sub>3 (q ^ (2 ^ n)) ^ 2) \<longlonglongrightarrow> agm (\<theta>\<^sub>3 q ^ 2) (\<theta>\<^sub>4 q ^ 2)" .
  moreover have "(\<lambda>n. \<theta>\<^sub>3 (q ^ (2 ^ n)) ^ 2) \<longlonglongrightarrow> \<theta>\<^sub>3 0 ^ 2"
    by (intro tendsto_intros tendsto_power_zero filterlim_subseq[of "\<lambda>n. 2 ^ n"]
              strict_monoI power_strict_increasing)
       (use assms in auto)
  hence "(\<lambda>n. \<theta>\<^sub>3 (q ^ (2 ^ n)) ^ 2) \<longlonglongrightarrow> 1"
    by simp
  ultimately show ?thesis
    using LIMSEQ_unique by blast
qed

text \<open>
  By recasting the above in terms of the complete elliptic integral $k$, we get the following
  identity that relates $K$ to the Jacobi theta functions.

  We only show the identity for real $q$ with $0\leq q < 1$. The version for the complex $z$-plane 
  is a bit more intricate: there the identity fails to hold at any point within a disc of radius
  $\frac{1}{2}$ around any point of the form $\frac{1}{2} + \mathbb{Z}$. This is due to the branch
  cut of $K$.
\<close>
theorem elliptic_K_jacobi_theta_real:
  fixes q :: real
  assumes q: "q \<in> {0..<1}"
  shows   "elliptic_K (\<theta>\<^sub>2 q ^ 4 / \<theta>\<^sub>3 q ^ 4) = pi / 2 * \<theta>\<^sub>3 q ^ 2"
proof -
  have *: "\<theta>\<^sub>4 q ^ 4 = \<theta>\<^sub>3 q ^ 4 - \<theta>\<^sub>2 q ^ 4"
    using jacobi_theta_nw_pow4_real[of q] q by simp
  have "1 = agm ((\<theta>\<^sub>3 q)\<^sup>2) ((\<theta>\<^sub>4 q)\<^sup>2)"
    by (subst agm_jacobi_theta_00_01_square_real) (use q in auto)
  also have "\<dots> = pi * (\<theta>\<^sub>3 q)\<^sup>2 / (2 * elliptic_K ((\<theta>\<^sub>3 q ^ 4 - \<theta>\<^sub>4 q ^ 4) / \<theta>\<^sub>3 q ^ 4))"
    by (subst agm_conv_elliptic_K_real) 
       (use q in \<open>auto simp: jacobi_theta_00_nw_nonzero_real jacobi_theta_01_nw_nonzero_real\<close>)
  also have "\<dots> = pi * \<theta>\<^sub>3 q ^ 2 / (2 * elliptic_K (\<theta>\<^sub>2 q ^ 4 / \<theta>\<^sub>3 q ^ 4))"
    by (subst *) auto
  finally show ?thesis
    by (auto simp: divide_simps mult_ac split: if_splits)
qed

end