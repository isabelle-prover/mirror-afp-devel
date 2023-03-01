(* Author: Maximilian Schäffeler *)
section \<open>Bounded Linear Functions\<close>
theory Blinfun_Util
  imports 
    "HOL-Analysis.Bounded_Linear_Function" 
    Bounded_Functions
begin

subsection \<open>Composition\<close>

lemma blinfun_compose_id[simp]:
  "id_blinfun o\<^sub>L f = f"
  "f o\<^sub>L id_blinfun = f"
  by (auto intro!: blinfun_eqI)

lemma blinfun_compose_assoc: "F o\<^sub>L G o\<^sub>L H = F o\<^sub>L (G o\<^sub>L H)"
  using blinfun_apply_inject by fastforce

lemma blinfun_compose_diff_right: "f o\<^sub>L (g - h) = (f o\<^sub>L g) - (f o\<^sub>L h)"
  by (auto intro!: blinfun_eqI simp: blinfun.bilinear_simps)

subsection \<open>Power\<close>

overloading
  blinfunpow \<equiv> "compow :: nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>\<^sub>L 'a) \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'a)"
begin

primrec blinfunpow :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>\<^sub>L 'a) \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'a)"
  where
    "blinfunpow 0 f = id_blinfun"
  | "blinfunpow (Suc n) f = f o\<^sub>L blinfunpow n f"

end

lemma bounded_pow_blinfun[intro]: 
  assumes "bounded (range (F::nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'a))"
  shows "bounded (range (\<lambda>t. (F t)^^(Suc n)))"
  using assms proof -
  assume "bounded (range F)"
  then obtain b where bh: "\<And>x. norm (F x) \<le> b"
    by (auto simp: bounded_iff)
  hence "norm ((F x)^^(Suc n)) \<le> b^(Suc n)" for x
    using bh
    by (induction n) (auto intro!: order.trans[OF norm_blinfun_compose] simp: mult_mono')
  thus ?thesis
    by (auto intro!: boundedI)
qed

lemma blincomp_scaleR_right: "(a *\<^sub>R (F :: 'a :: real_normed_vector \<Rightarrow>\<^sub>L 'a)) ^^ t = a^t *\<^sub>R F^^t"
  by (induction t) (auto intro: blinfun_eqI simp: blinfun.scaleR_left blinfun.scaleR_right)
lemma summable_inv_Q:
  fixes Q :: "'a :: banach \<Rightarrow>\<^sub>L 'a"
  assumes onorm_le: "norm (id_blinfun - Q) < 1"
  shows "summable (\<lambda>n. (id_blinfun - Q)^^n)"
  using onorm_le norm_blinfun_compose 
  by (force intro!: summable_ratio_test)

lemma blinfunpow_assoc: "(F::'a::real_normed_vector \<Rightarrow>\<^sub>L 'a) ^^ (Suc n) =(F ^^n) o\<^sub>L F"
  by (induction n) (auto simp: blinfun_compose_assoc[symmetric]) 

lemma norm_blinfunpow_le: "norm ((f :: 'b :: real_normed_vector \<Rightarrow>\<^sub>L 'b) ^^ n) \<le> norm f ^ n"
  by (induction n) (auto simp: norm_blinfun_id_le intro!: order.trans[OF norm_blinfun_compose] mult_left_mono)

lemma blinfunpow_nonneg: 
  assumes "\<And>v. 0 \<le> v \<Longrightarrow> 0 \<le> blinfun_apply (f :: ('b :: {ord, real_normed_vector} \<Rightarrow>\<^sub>L 'b)) v"
  shows "0 \<le> v \<Longrightarrow> 0 \<le> (f^^n) v"
  by(induction n) (auto simp: assms)

lemma blinfunpow_mono: 
  assumes "\<And>u v. u \<le> v \<Longrightarrow> (f :: 'b :: {ord, real_normed_vector} \<Rightarrow>\<^sub>L 'b) u \<le> f v"
  shows "u \<le> v \<Longrightarrow> (f^^n) u \<le> (f^^n) v"
  by (induction n) (auto simp: assms)  

lemma banach_blinfun:
  fixes C :: "'b :: {real_normed_vector, complete_space} \<Rightarrow>\<^sub>L 'b"
  assumes "norm C < 1"
  shows "\<exists>!v. C v = v" "\<And>v. (\<lambda>n. (C ^^ n) v) \<longlonglongrightarrow> (THE v. C v = v)"
  using assms
proof -
  obtain v where "C v = v" "\<forall>v'. C v' = v' \<longrightarrow> v' = v"
    using assms banach_fix_type[of "norm C" "blinfun_apply C"]
    by (metis blinfun.zero_right less_irrefl mult.left_neutral mult_less_le_imp_less 
        norm_blinfun norm_conv_dist norm_ge_zero zero_less_dist_iff)
  obtain l where "(\<forall>v u. norm (C (v - u)) \<le> l * dist v u)" "0 \<le> l" "l < 1"
    by (metis assms dist_norm norm_blinfun norm_imp_pos_and_ge)
  hence 1: "dist (C v) (C u) \<le> l * dist v u" for v u
    by (simp add: blinfun.diff_right dist_norm)
  have 2: "dist ((C ^^ n) v0) v \<le> l ^ n * dist v0 v" for n v0
    using \<open>0 \<le> l\<close> 
    by (induction n) (auto simp: mult.assoc 
        intro!: mult_mono' order.trans[OF 1[of _ v , unfolded \<open>C v = v\<close>]])
  have "(\<lambda>n. l ^ n) \<longlonglongrightarrow> 0"
    by (simp add: LIMSEQ_realpow_zero \<open>0 \<le> l\<close> \<open>l < 1\<close>)
  hence k: "\<And>v0. (\<lambda>n. l ^ n * dist v0 v) \<longlonglongrightarrow> 0"
    by (auto simp add: tendsto_mult_left_zero)
  have "(\<lambda>n. dist ((C ^^ n) v0) v) \<longlonglongrightarrow> 0" for v0
    using k 2 order_trans abs_ge_self
    by (subst Limits.tendsto_0_le[where ?K = 1, where ?f = "(\<lambda>n. l ^ n * dist v0 v)"])
      (fastforce intro: eventuallyI)+
  hence "\<And>v0. (\<lambda>n. (C ^^ n) v0) \<longlonglongrightarrow> v"
    using tendsto_dist_iff
    by blast
  thus "(\<lambda>n. (C ^^ n) v0) \<longlonglongrightarrow> (THE v. C v = v)" for v0
    using theI'[of "\<lambda>x. C x = x"] \<open>C v = v\<close> \<open>\<forall>v'. C v' = v' \<longrightarrow> v' = v\<close> 
    by blast
next
  show "norm C < 1 \<Longrightarrow> \<exists>!v. blinfun_apply C v = v"
    by (auto intro!: banach_fix_type[OF _ assms] 
        simp: dist_norm norm_blinfun blinfun.diff_right[symmetric])
qed

subsection \<open>Geometric Sum\<close>

lemma inv_one_sub_Q:
  fixes Q :: "'a :: banach \<Rightarrow>\<^sub>L 'a"
  assumes onorm_le: "norm (id_blinfun - Q) < 1"
  shows "(Q o\<^sub>L (\<Sum>i. (id_blinfun - Q)^^i)) = id_blinfun" 
    and "(\<Sum>i. (id_blinfun - Q)^^i) o\<^sub>L Q = id_blinfun"
proof -
  obtain b where bh: "b < 1"  "norm (id_blinfun - Q) < b"
    using onorm_le dense 
    by blast
  have "0 < b" 
    using le_less_trans[OF norm_ge_zero bh(2)] .
  have norm_le_aux: "norm ((id_blinfun - Q)^^Suc n) \<le> b^(Suc n)" for n
  proof (induction n)
    case 0
    thus ?case 
      using bh 
      by simp
  next
    case (Suc n)
    thus ?case
    proof -
      have "norm ((id_blinfun - Q) ^^ Suc (Suc n)) \<le> norm (id_blinfun - Q) * norm((id_blinfun - Q) ^^ Suc n)"
        using norm_blinfun_compose 
        by auto
      thus ?thesis
        using Suc.IH \<open>0 < b\<close> bh order.trans
        by (fastforce simp: mult_mono')
    qed 
  qed
  have "(Q o\<^sub>L (\<Sum>i\<le>n. (id_blinfun - Q)^^i)) = (id_blinfun - (id_blinfun - Q)^^(Suc n))" for n
    by (induction n)  (auto simp: bounded_bilinear.diff_left bounded_bilinear.add_right 
        bounded_bilinear_blinfun_compose)
  hence "\<And>n. norm (id_blinfun - (Q o\<^sub>L (\<Sum>i\<le>n. (id_blinfun - Q)^^i))) \<le> b^Suc n"
    using norm_le_aux 
    by auto
  hence l2: "(\<lambda>n. (id_blinfun - (Q o\<^sub>L (\<Sum>i\<le>n. (id_blinfun - Q)^^i)))) \<longlonglongrightarrow> 0"
    using \<open>0 < b\<close> bh 
    by (subst Lim_transform_bound[where g="\<lambda>n. b^Suc n"]) (auto intro!: tendsto_eq_intros)
  have "summable (\<lambda>n. (id_blinfun - Q)^^n)"
    using onorm_le norm_blinfun_compose 
    by (force intro!: summable_ratio_test)
  hence "(\<lambda>n. \<Sum>i\<le>n.  (id_blinfun - Q)^^i) \<longlonglongrightarrow> (\<Sum>i. (id_blinfun - Q)^^i)"
    using summable_LIMSEQ' 
    by blast
  hence "(\<lambda>n. Q o\<^sub>L (\<Sum>i\<le>n. (id_blinfun - Q)^^i)) \<longlonglongrightarrow> (Q o\<^sub>L (\<Sum>i. (id_blinfun - Q)^^i))"
    using bounded_bilinear_blinfun_compose 
    by (subst Limits.bounded_bilinear.tendsto[where prod = "(o\<^sub>L)"]) auto   
  hence "(\<lambda>n. id_blinfun - (Q o\<^sub>L (\<Sum>i\<le>n. (id_blinfun - Q)^^i))) \<longlonglongrightarrow> 
    id_blinfun - (Q o\<^sub>L (\<Sum>i. (id_blinfun - Q)^^i))"
    by (subst Limits.tendsto_diff) auto
  thus "(Q o\<^sub>L (\<Sum>i. (id_blinfun - Q)^^i)) = id_blinfun"
    using LIMSEQ_unique l2 by fastforce

  have "((\<Sum>i\<le>n. (id_blinfun - Q)^^i) o\<^sub>L Q) = (id_blinfun - (id_blinfun - Q)^^(Suc n))" for n
  proof (induction n)
    case (Suc n)
    have "sum ((^^) (id_blinfun - Q)) {..Suc n} o\<^sub>L Q = 
        (sum ((^^) (id_blinfun - Q)) {..n} o\<^sub>L Q) + ((id_blinfun - Q) ^^Suc n o\<^sub>L Q)"
      by (simp add: bounded_bilinear.add_left bounded_bilinear_blinfun_compose)
    also have "\<dots> = id_blinfun - (((id_blinfun - Q)^^(Suc n) o\<^sub>L id_blinfun) - 
        ((id_blinfun - Q) ^^Suc n o\<^sub>L Q))"
      using Suc.IH 
      by auto
    also have "\<dots> = id_blinfun - (((id_blinfun - Q)^^(Suc n) o\<^sub>L (id_blinfun - Q)))"
      by (auto intro!: blinfun_eqI simp: blinfun.diff_right blinfun.diff_left blinfun.minus_left)
    also have "\<dots> = id_blinfun - (((id_blinfun - Q)^^(Suc (Suc n))))"
      using blinfunpow_assoc
      by metis
    finally show ?case
      by auto
  qed simp
  hence "\<And>n. norm (id_blinfun - ((\<Sum>i\<le>n. (id_blinfun - Q)^^i) o\<^sub>L Q)) \<le> b^Suc n"
    using norm_le_aux by auto
  hence l2: "(\<lambda>n. id_blinfun - ((\<Sum>i\<le>n. (id_blinfun - Q)^^i) o\<^sub>L Q)) \<longlonglongrightarrow> 0"
    using \<open>0 < b\<close> bh 
    by (subst Lim_transform_bound[where g="\<lambda>n. b^Suc n"]) (auto intro!: tendsto_eq_intros)
  have "summable (\<lambda>n. (id_blinfun - Q)^^n)"
    using local.onorm_le norm_blinfun_compose 
    by (force intro!: summable_ratio_test)
  hence "(\<lambda>n. \<Sum>i\<le>n.  (id_blinfun - Q)^^i) \<longlonglongrightarrow> (\<Sum>i. (id_blinfun - Q)^^i)"
    using summable_LIMSEQ' by blast
  hence "(\<lambda>n. (\<Sum>i\<le>n. (id_blinfun - Q)^^i) o\<^sub>L Q) \<longlonglongrightarrow> ((\<Sum>i. (id_blinfun - Q)^^i) o\<^sub>L Q)"
    using bounded_bilinear_blinfun_compose 
    by (subst Limits.bounded_bilinear.tendsto[where prod = "(o\<^sub>L)"]) auto   
  hence "(\<lambda>n. id_blinfun - ((\<Sum>i\<le>n. (id_blinfun - Q)^^i) o\<^sub>L Q)) \<longlonglongrightarrow> 
    id_blinfun - ((\<Sum>i. (id_blinfun - Q)^^i) o\<^sub>L Q)"
    by (subst Limits.tendsto_diff) auto
  thus "((\<Sum>i. (id_blinfun - Q)^^i) o\<^sub>L Q) = id_blinfun"
    using LIMSEQ_unique l2 by fastforce
qed

lemma inv_norm_le:
  fixes Q :: "'a :: banach \<Rightarrow>\<^sub>L 'a"
  assumes "norm Q  < 1"
  shows "(id_blinfun-Q) o\<^sub>L (\<Sum>i. Q^^i) = id_blinfun"
    "(\<Sum>i. Q^^i) o\<^sub>L (id_blinfun-Q) = id_blinfun"
  using inv_one_sub_Q[of "id_blinfun - Q"] assms
  by auto

lemma inv_norm_le':
  fixes Q :: "'a :: banach \<Rightarrow>\<^sub>L 'a"
  assumes "norm Q  < 1"
  shows "(id_blinfun-Q) ((\<Sum>i. Q^^i) x) = x"
    "(\<Sum>i. Q^^i) ((id_blinfun-Q) x) = x"
  using inv_norm_le assms  
  by (auto simp del: blinfun_apply_blinfun_compose 
      simp: inv_norm_le blinfun_apply_blinfun_compose[symmetric])

subsection \<open>Inverses\<close>

definition "is_inverse\<^sub>L X Y \<longleftrightarrow> X o\<^sub>L Y = id_blinfun \<and> Y o\<^sub>L X = id_blinfun"

abbreviation "invertible\<^sub>L X \<equiv> \<exists>X'. is_inverse\<^sub>L X X'"

lemma is_inverse\<^sub>L_I[intro]:
  assumes "X o\<^sub>L Y = id_blinfun" "Y o\<^sub>L X = id_blinfun"
  shows "is_inverse\<^sub>L X Y"
  using assms
  unfolding is_inverse\<^sub>L_def
  by auto

lemma is_inverse\<^sub>L_D[dest]:
  assumes "is_inverse\<^sub>L X Y"
  shows "X o\<^sub>L Y = id_blinfun" "Y o\<^sub>L X = id_blinfun"
  using assms
  unfolding is_inverse\<^sub>L_def
  by auto

lemma invertible\<^sub>L_D[dest]:
  assumes "invertible\<^sub>L f"
  obtains g where "f o\<^sub>L g = id_blinfun" "g o\<^sub>L f = id_blinfun"
  using assms
  by auto

lemma invertible\<^sub>L_I[intro]:
  assumes "f o\<^sub>L g = id_blinfun" "g o\<^sub>L f = id_blinfun"
  shows "invertible\<^sub>L f"
  using assms
  by auto

lemma is_inverse\<^sub>L_comm: "is_inverse\<^sub>L X Y \<longleftrightarrow> is_inverse\<^sub>L Y X"
  by auto

lemma is_inverse\<^sub>L_unique: "is_inverse\<^sub>L f g \<Longrightarrow> is_inverse\<^sub>L f h \<Longrightarrow> g = h"
  unfolding is_inverse\<^sub>L_def
  using blinfun_compose_assoc  blinfun_compose_id(1)
  by metis

lemma is_inverse\<^sub>L_ex1: "is_inverse\<^sub>L f g \<Longrightarrow> \<exists>!h. is_inverse\<^sub>L f h"
  using is_inverse\<^sub>L_unique
  by auto

lemma is_inverse\<^sub>L_ex1': "\<exists>x. is_inverse\<^sub>L f x \<Longrightarrow> \<exists>!x. is_inverse\<^sub>L f x"
  using is_inverse\<^sub>L_ex1
  by auto

definition "inv\<^sub>L f = (THE g. is_inverse\<^sub>L f g)"

lemma inv\<^sub>L_eq:
  assumes "is_inverse\<^sub>L f g" 
  shows "inv\<^sub>L f = g"
  unfolding inv\<^sub>L_def
  using assms is_inverse\<^sub>L_ex1
  by (auto intro!: the_equality)

lemma inv\<^sub>L_I:
  assumes "f o\<^sub>L g = id_blinfun" "g o\<^sub>L f = id_blinfun" 
  shows "g = inv\<^sub>L f"
  using assms inv\<^sub>L_eq
  unfolding is_inverse\<^sub>L_def
  by auto

lemma inv_app1 [simp]: "invertible\<^sub>L X \<Longrightarrow> (inv\<^sub>L X) o\<^sub>L X = id_blinfun"
  using is_inverse\<^sub>L_ex1' inv\<^sub>L_eq 
  by blast

lemma inv_app2[simp]: "invertible\<^sub>L X \<Longrightarrow> X o\<^sub>L (inv\<^sub>L X)  = id_blinfun"
  using is_inverse\<^sub>L_ex1' inv\<^sub>L_eq 
  by blast

lemma inv_app1'[simp]: "invertible\<^sub>L X \<Longrightarrow> inv\<^sub>L X (X v) = v"
  using inv_app1 blinfun_apply_blinfun_compose id_blinfun.rep_eq
  by metis

lemma inv_app2'[simp]: "invertible\<^sub>L X \<Longrightarrow> X (inv\<^sub>L X v) = v"
  using inv_app2 blinfun_apply_blinfun_compose id_blinfun.rep_eq
  by metis

lemma inv\<^sub>L_inv\<^sub>L[simp]: "invertible\<^sub>L X \<Longrightarrow> inv\<^sub>L (inv\<^sub>L X) = X"
  by (metis inv\<^sub>L_eq is_inverse\<^sub>L_comm)

lemma inv\<^sub>L_cancel_iff:
  assumes "invertible\<^sub>L f"
  shows "f x = y \<longleftrightarrow> x = inv\<^sub>L f y"
  by (auto simp add: assms)

lemma invertible\<^sub>L_inf_sum:
  assumes "norm (X :: 'b :: banach \<Rightarrow>\<^sub>L 'b) < 1"
  shows "invertible\<^sub>L (id_blinfun - X)"
  using Blinfun_Util.inv_norm_le[OF assms] assms
  by blast

lemma inv\<^sub>L_inf_sum:
  fixes X :: "'b :: banach \<Rightarrow>\<^sub>L _"
  assumes "norm X < 1"
  shows "inv\<^sub>L (id_blinfun - X) = (\<Sum>i. X ^^ i)"
  using Blinfun_Util.inv_norm_le[OF assms] assms
  by (auto simp: inv\<^sub>L_I[symmetric])

lemma is_inverse\<^sub>L_compose:
  assumes "invertible\<^sub>L f" "invertible\<^sub>L g" 
  shows "is_inverse\<^sub>L (f o\<^sub>L g) (inv\<^sub>L g o\<^sub>L inv\<^sub>L f)"
  by (auto intro!: blinfun_eqI is_inverse\<^sub>L_I[of _ "inv\<^sub>L g o\<^sub>L inv\<^sub>L f"]
      simp: inv_app2'[OF assms(1)] inv_app2'[OF assms(2)] inv_app1'[OF assms(1)] inv_app1'[OF assms(2)])

lemma invertible\<^sub>L_compose: "invertible\<^sub>L f \<Longrightarrow> invertible\<^sub>L g \<Longrightarrow> invertible\<^sub>L (f o\<^sub>L g)"
  using is_inverse\<^sub>L_compose 
  by blast

lemma inv\<^sub>L_compose: 
  assumes "invertible\<^sub>L f" "invertible\<^sub>L g" 
  shows"inv\<^sub>L (f o\<^sub>L g) = (inv\<^sub>L g) o\<^sub>L (inv\<^sub>L f)"
  using assms inv\<^sub>L_eq is_inverse\<^sub>L_compose
  by blast

lemma inv\<^sub>L_id_blinfun[simp]: "inv\<^sub>L id_blinfun = id_blinfun"
  by (metis blinfun_compose_id(2) inv\<^sub>L_I)


subsection \<open>Norm\<close>
lemma bounded_range_subset: 
  "bounded (range f :: real set) \<Longrightarrow> bounded (f ` X')"
  by (auto simp: bounded_iff)

lemma bounded_const: "bounded ((\<lambda>_. x) ` X)"
  by (meson finite_imp_bounded finite.emptyI finite_insert finite_subset image_subset_iff insert_iff)

lift_definition bfun_pos :: "('d \<Rightarrow>\<^sub>b real) \<Rightarrow> ('d \<Rightarrow>\<^sub>b real)" is "\<lambda>f i. if f i < 0 then -f i else f i"
  using bounded_const bounded_range_subset by (auto simp: bfun_def)

lemma bfun_pos_zero[simp]: "bfun_pos f = 0 \<longleftrightarrow> f = 0"
  by (auto intro!: bfun_eqI simp: bfun_pos.rep_eq split: if_splits)

lift_definition bfun_nonneg :: "('d \<Rightarrow>\<^sub>b real) \<Rightarrow> ('d \<Rightarrow>\<^sub>b real)" is "\<lambda>f i. if f i \<le> 0 then 0 else f i"
  using bounded_const bounded_range_subset by (auto simp: bfun_def)

lemma bfun_nonneg_split: "bfun_nonneg x - bfun_nonneg (- x) = x"
  by (auto simp: bfun_nonneg.rep_eq)

lemma blinfun_split: "blinfun_apply f x = f (bfun_nonneg x) - f (bfun_nonneg (- x))"
  using bfun_nonneg_split
  by (metis blinfun.diff_right)

lemma bfun_nonneg_pos: "bfun_nonneg x + bfun_nonneg (-x) = bfun_pos x"
  by (auto simp: bfun_nonneg.rep_eq bfun_pos.rep_eq)

lemma bfun_nonneg: "0 \<le> bfun_nonneg f"
  by (auto simp: bfun_nonneg.rep_eq)

lemma bfun_pos_eq_nonneg: "bfun_pos n = bfun_nonneg n + bfun_nonneg (-n)"
  by (auto simp: bfun_pos.rep_eq bfun_nonneg.rep_eq)

lemma blinfun_mono_norm_pos:
  fixes f :: "('c \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('d \<Rightarrow>\<^sub>b real)"
  assumes "\<And>v :: 'c \<Rightarrow>\<^sub>b real. v \<ge> 0 \<Longrightarrow> f v \<ge> 0"
  shows "norm (f n) \<le> norm (f (bfun_pos n))"
proof -
  have *: "\<bar>f n i\<bar> \<le> \<bar>f (bfun_pos n) i\<bar>" for i
    by (auto simp: blinfun_split[of f n] bfun_nonneg_pos[symmetric] blinfun.add_right abs_real_def)
      (metis add_nonneg_nonneg assms bfun_nonneg leD less_eq_bfun_def zero_bfun.rep_eq)+
  thus "norm (f n) \<le> norm ((f (bfun_pos n)))"
    unfolding norm_bfun_def' using *
    by (auto intro!: cSUP_mono bounded_imp_bdd_above abs_le_norm_bfun boundedI[of _ "norm ((f (bfun_pos n)))"])
qed

lemma norm_bfun_pos[simp]: "norm (bfun_pos f) = norm f"
proof -
  have "norm (bfun_pos f) = (\<Squnion>i. \<bar>bfun_pos f i\<bar>)"
    by (auto simp add: norm_bfun_def')
  also have "\<dots> = (\<Squnion>i. \<bar>f i\<bar>)"
    by (rule SUP_cong[OF refl]) (auto simp: bfun_pos.rep_eq)
  finally show ?thesis by (auto simp add: norm_bfun_def')
qed

lemma norm_blinfun_mono_eq_nonneg:
  fixes f :: "('c \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('d \<Rightarrow>\<^sub>b real)"
  assumes "\<And>v :: 'c \<Rightarrow>\<^sub>b real. v \<ge> 0 \<Longrightarrow> f v \<ge> 0"
  shows "norm f = (\<Squnion>v \<in> {v. v \<ge> 0}. norm (f v) / norm v)"
  unfolding norm_blinfun.rep_eq onorm_def
proof (rule antisym, rule cSUP_mono)
  have *: "norm (blinfun_apply f v) / norm v \<le> norm f" for v
    using norm_blinfun[of f]
    by (cases "v = 0") (auto simp: pos_divide_le_eq)
  thus "bdd_above ((\<lambda>v. norm (f v) / norm v) ` {v. 0 \<le> v})"
    by (auto intro!: bounded_imp_bdd_above boundedI)
  show "\<exists>m\<in>{v. 0 \<le> v}. norm (f n) / norm n \<le> norm (f m) / norm m" for n
    using blinfun_mono_norm_pos[OF assms]
    by (cases "norm (bfun_pos n) = 0")
      (auto intro!: frac_le exI[of _ "bfun_pos n"] simp: less_eq_bfun_def bfun_pos.rep_eq)
  show "(\<Squnion>v\<in>{v. 0 \<le> v}. norm (f v) / norm v) \<le> (\<Squnion>x. norm (f x) / norm x)"
    using *
    by (auto intro!: cSUP_mono bounded_imp_bdd_above boundedI)
qed auto

lemma norm_blinfun_normalized_le: "norm (blinfun_apply f v) / norm v \<le> norm f"
  by (simp add: blinfun.bounded_linear_right le_onorm norm_blinfun.rep_eq)

lemma norm_blinfun_mono_eq_nonneg':
  fixes f :: "('c \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('d \<Rightarrow>\<^sub>b real)"
  assumes "\<And>v :: 'c \<Rightarrow>\<^sub>b real. 0 \<le> v \<Longrightarrow> 0 \<le> f v"
  shows "norm f = (\<Squnion>x \<in> {x. norm x = 1 \<and> x \<ge> 0}. norm (f x))"
proof (subst norm_blinfun_mono_eq_nonneg[OF assms])
  show "(\<Squnion>v\<in>{v. 0 \<le> v}. norm (f v) / norm v) =
    (\<Squnion>x\<in>{x. norm x = 1 \<and> 0 \<le> x}. norm (f x))"
  proof (rule antisym, rule cSUP_mono)
    show "{v::'c \<Rightarrow>\<^sub>b real. 0 \<le> v} \<noteq> {}" by auto
    show "bdd_above ((\<lambda>x. norm (f x)) ` {x. norm x = 1 \<and> 0 \<le> x})"
      by (fastforce intro: order.trans[OF norm_blinfun[of f]] bounded_imp_bdd_above boundedI)
    show "\<exists>m\<in>{x. norm x = 1 \<and> 0 \<le> x}. norm (f n) / norm n \<le> norm (f m)" if "n \<in> {v. 0 \<le> v}" for n
    proof (cases "norm (bfun_pos n) = 0")
      case True
      then show ?thesis by (auto intro!: exI[of _ 1])
    next
      case False
      then show ?thesis
        using that
        by (auto simp: scaleR_nonneg_nonneg blinfun.scaleR_right intro!: exI[of _ "(1/norm n) *\<^sub>R n"])
    qed
    show "(\<Squnion>x\<in>{x. norm x = 1 \<and> 0 \<le> x}. norm (f x)) \<le> (\<Squnion>v\<in>{v. 0 \<le> v}. norm (f v) / norm v)"
    proof (rule cSUP_mono)
      show "{x::'c \<Rightarrow>\<^sub>b real. norm x = 1 \<and> 0 \<le> x} \<noteq> {}"
        by (auto intro!: exI[of _ 1])
    qed (fastforce intro!: norm_blinfun_normalized_le bounded_imp_bdd_above boundedI)+
  qed
qed auto

lemma norm_blinfun_mono_le_norm_one:
  fixes f :: "('c \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('d \<Rightarrow>\<^sub>b real)"
  assumes "\<And>v :: 'c \<Rightarrow>\<^sub>b real. v \<ge> 0 \<Longrightarrow> f v \<ge> 0"
  assumes "norm x = 1" "0 \<le> x"
  shows "norm (f x) \<le> norm (f 1)" 
proof -
  have **: "0 \<le> 1 - x"
    using assms
    by (auto simp: less_eq_bfun_def intro: order.trans[OF le_norm_bfun])
  show ?thesis
    unfolding norm_bfun_def'
  proof (intro cSUP_mono)
    show"bdd_above (range (\<lambda>x. norm (apply_bfun (blinfun_apply f 1) x)))"
      using order.trans abs_le_norm_bfun norm_blinfun
      by (fastforce intro!: bounded_imp_bdd_above boundedI)
    show "\<exists>m\<in>UNIV. norm (f x n) \<le> norm (f 1 m)" for n
      using assms(1) assms(3) assms(1)[of "1 - x"] **
      unfolding less_eq_bfun_def zero_bfun.rep_eq abs_real_def
      by (auto simp: blinfun.diff_right linorder_class.not_le[symmetric])
  qed auto
qed

lemma norm_blinfun_mono_eq_one:
  fixes f :: "('c \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('d \<Rightarrow>\<^sub>b real)"
  assumes "\<And>v :: 'c \<Rightarrow>\<^sub>b real. v \<ge> 0 \<Longrightarrow> f v \<ge> 0"
  shows "norm f = norm (f 1)"
proof -
  have "(\<Squnion>x\<in>{x. norm x = 1 \<and> 0 \<le> x}. norm (f x)) = norm (f 1)"
  proof (rule antisym, rule cSUP_least)
    show "{x::'c \<Rightarrow>\<^sub>b real. norm x = 1 \<and> 0 \<le> x} \<noteq> {}"
      by (auto intro!: exI[of _ 1])
  next
    show "\<And>x. x \<in> {x. norm x = 1 \<and> 0 \<le> x} \<Longrightarrow> norm (f x) \<le> norm (f 1)"
      by (simp add: assms norm_blinfun_mono_le_norm_one)
  next
    show "norm (f 1) \<le> (\<Squnion>x\<in>{x. norm x = 1 \<and> 0 \<le> x}. norm (f x))"
      by (rule cSUP_upper) (fastforce intro!: bdd_aboveI2 order.trans[OF norm_blinfun])+
  qed
  thus ?thesis
    using norm_blinfun_mono_eq_nonneg'[OF assms] 
    by auto
qed

subsection \<open>Miscellaneous\<close>

lemma bounded_linear_apply_bfun: "bounded_linear (\<lambda>x. apply_bfun x i)"
  using norm_le_norm_bfun
  by (fastforce intro: bounded_linear_intro[of _ 1])

lemma lim_blinfun_apply: "convergent X \<Longrightarrow> (\<lambda>n. blinfun_apply (X n) u) \<longlonglongrightarrow> lim X u"  
  using blinfun.bounded_bilinear_axioms
  by (auto simp: convergent_LIMSEQ_iff intro: Limits.bounded_bilinear.tendsto)

lemma bounded_apply_blinfun: 
  assumes "bounded ((F :: 'c \<Rightarrow> 'd::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector) ` S)"
  shows "bounded ((\<lambda>b. blinfun_apply (F b) x) ` S)"
proof -
  obtain b where "\<forall>x\<in>S. norm (F x) \<le> b"
    by (meson \<open>bounded (F ` S)\<close> bounded_pos image_eqI)
  thus "bounded ((\<lambda>b. (F b) x) ` S)"
    by (auto simp: mult_right_mono mult.commute[of _ b] 
        intro!: boundedI[of _ "norm x * b"] dual_order.trans[OF _ norm_blinfun])
qed

lemma tendsto_blinfun_apply: "(\<lambda>n. X n) \<longlonglongrightarrow> L  \<Longrightarrow> (\<lambda>n. blinfun_apply (X n) u) \<longlonglongrightarrow> L u"  
  using blinfun.bounded_bilinear_axioms
  by (auto simp: convergent_LIMSEQ_iff intro: Limits.bounded_bilinear.tendsto)


definition "nonneg_blinfun (Q :: _::{ordered_real_normed_vector} \<Rightarrow>\<^sub>L _::{ordered_ab_group_add, ordered_real_normed_vector}) \<equiv> (\<forall>v\<ge>0. blinfun_apply Q v \<ge> 0)"

definition "blinfun_le Q R = nonneg_blinfun (R - Q)"


lemma nonneg_blinfun_nonneg[dest]: "nonneg_blinfun Q \<Longrightarrow> 0 \<le> v \<Longrightarrow> 0 \<le> Q v"
  unfolding nonneg_blinfun_def
  by auto

lemma nonneg_blinfun_mono[dest]: "nonneg_blinfun Q \<Longrightarrow> u \<le> v \<Longrightarrow> Q u \<le> Q v"
  using nonneg_blinfun_nonneg[of Q "v - u", unfolded blinfun.diff_right]
  by auto

lemma nonneg_id_blinfun: "nonneg_blinfun id_blinfun"
  by (auto simp: nonneg_blinfun_def)




lemma blinfun_nonneg_eq:
  assumes "\<forall>v \<ge> 0. blinfun_apply (f::('c \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('c \<Rightarrow>\<^sub>b real)) v = blinfun_apply g v"
  shows "f = g"
proof (rule blinfun_eqI)
  fix v :: "'c \<Rightarrow>\<^sub>b real"
  define v1 where "v1 = Bfun (\<lambda>x. max (v x) 0)"
  define v2 where "v2 = Bfun (\<lambda>x. - min (v x) 0)"
  have in_bfun[simp]: "(\<lambda>x. max (v x) 0) \<in> bfun" "(\<lambda>x. - min (v x) 0) \<in> bfun"
    by (auto simp: le_norm_bfun minus_min_eq_max abs_le_norm_bfun abs_le_D2 intro!: boundedI[of _ "norm v"])
  have eq_v: "v = v1 - v2"
    unfolding v1_def v2_def
    by (auto simp: Bfun_inverse)
  have nonneg: "0 \<le> v1" "0 \<le> v2"
    unfolding less_eq_bfun_def
    by (auto simp: v1_def v2_def Bfun_inverse)
  show " blinfun_apply f v = blinfun_apply g v"
    unfolding eq_v
    using nonneg assms
    by (auto simp: blinfun.diff_right)
qed

lemma bfun_zero_le_one: "0 \<le> (1 :: 'c \<Rightarrow>\<^sub>b real)"
  by (simp add: less_eq_bfunI)

lemma norm_nonneg_blinfun_one:
  assumes "nonneg_blinfun (X :: ('c \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('c \<Rightarrow>\<^sub>b real))"
  shows "norm X = norm (blinfun_apply X 1)"
  using assms unfolding nonneg_blinfun_def
  by (auto simp: norm_blinfun_mono_eq_one)


lemma blinfun_apply_mono: "nonneg_blinfun X \<Longrightarrow> 0 \<le> v \<Longrightarrow> blinfun_le X Y \<Longrightarrow> X v \<le> Y v"
  by (simp add: blinfun.diff_left blinfun_le_def nonneg_blinfun_def)

lemma nonneg_blinfun_scaleR[intro]:  "nonneg_blinfun B \<Longrightarrow> 0 \<le> c \<Longrightarrow> nonneg_blinfun (c *\<^sub>R B)"
  by (simp add: nonneg_blinfun_def scaleR_blinfun.rep_eq scaleR_nonneg_nonneg)

lemma nonneg_blinfun_compose[intro]: "nonneg_blinfun B \<Longrightarrow> nonneg_blinfun C \<Longrightarrow> nonneg_blinfun (C o\<^sub>L B)"
  by (simp add: nonneg_blinfun_def)


lemma matrix_le_norm_mono:
  assumes "nonneg_blinfun (C :: ('c \<Rightarrow>\<^sub>b real) \<Rightarrow>\<^sub>L ('c \<Rightarrow>\<^sub>b real))"
    and "nonneg_blinfun (D - C)"
  shows "norm C \<le> norm D"
proof -
  have "nonneg_blinfun D"
    using assms
    by (metis add_nonneg_nonneg diff_add_cancel nonneg_blinfun_def plus_blinfun.rep_eq)
  have zero_le: "0 \<le> C 1" "0 \<le> D 1"
    using assms zero_le_one  \<open>nonneg_blinfun D\<close>
    by (auto simp add: less_eq_bfunI nonneg_blinfun_nonneg)
  hence "C 1 \<le> D 1"
    using assms(2) unfolding nonneg_blinfun_def blinfun.diff_left
    by (simp add: less_eq_bfun_def)
  thus ?thesis
    using assms \<open>nonneg_blinfun D\<close> zero_le le_norm_bfun
    by (fastforce simp: norm_nonneg_blinfun_one norm_bfun_def' less_eq_bfun_def intro!: bdd_above.I2 cSUP_mono)
qed


lemma bounded_subset: "Y \<subseteq> X \<Longrightarrow> bounded (f ` X) \<Longrightarrow> bounded (f ` Y)"
  by (auto simp: bounded_def)

lemma bounded_subset_range: "bounded (range f) \<Longrightarrow> bounded (f ` Y)"
  using bounded_subset subset_UNIV by metis


lift_definition bfun_if :: "('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow>\<^sub>b 'c::metric_space) \<Rightarrow> ('b \<Rightarrow>\<^sub>b 'c) \<Rightarrow> ('b \<Rightarrow>\<^sub>b 'c)" is "\<lambda>b u v s. if b s then u s else v s"
  using bounded_subset_range
  by (auto simp: bfun_def)

lemma bfun_if_add: "bfun_if b (w + z) (u + v) = bfun_if b w u + bfun_if b z v"
  by (auto simp: bfun_if.rep_eq)

lemma bfun_if_zero_add: "bfun_if b 0 (u + v) = bfun_if b 0 u + bfun_if b 0 v"
  by (auto simp: bfun_if.rep_eq)

lemma bfun_if_zero_le: "0 \<le> v \<Longrightarrow> bfun_if b 0 v \<le> v"
  by (metis (no_types, lifting) bfun_if.rep_eq le_less less_eq_bfun_def)


lemma bfun_if_eq: "(\<And>i. P i \<Longrightarrow> apply_bfun v i = apply_bfun u i) \<Longrightarrow> (\<And>i. \<not>P i \<Longrightarrow> v i = apply_bfun w i) \<Longrightarrow> bfun_if P u w = v"
  by (auto simp: bfun_if.rep_eq)
  
lemma bfun_if_scaleR: "c *\<^sub>R bfun_if b v1 v2 = bfun_if b (c *\<^sub>R v1) (c *\<^sub>R v2)"
  by (auto simp: bfun_if.rep_eq)



lemma summable_blinfun_apply:
  assumes "summable (f :: nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'a)" 
  shows "summable (\<lambda>n. f n v)"
  using assms tendsto_blinfun_apply
  unfolding summable_def sums_def blinfun.sum_left[symmetric]
  by auto


lemma blinfun_apply_suminf: 
  assumes "summable (f :: nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'a)" 
  shows "(\<Sum>k. blinfun_apply (f k) v) = (\<Sum>k. f k) v"
  using bounded_linear.suminf[OF blinfun.bounded_linear_left assms] 
  by auto
end