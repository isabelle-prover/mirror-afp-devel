(*  Title:   Riesz_Representation.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section  \<open>The Riesz Representation Theorem\<close>
theory Riesz_Representation
  imports "Regular_Measure"
          "Urysohn_Locally_Compact_Hausdorff"
begin

subsection \<open> Lemmas for Complex-Valued Continuous Maps \<close>
(* TODO: Move *)
lemma continuous_map_Re'[simp,continuous_intros]: "continuous_map euclidean euclideanreal Re"
  and continuous_map_Im'[simp,continuous_intros]: "continuous_map euclidean euclideanreal Im"
  and continuous_map_complex_of_real'[simp,continuous_intros]: "continuous_map euclideanreal euclidean complex_of_real"
  by(auto simp: continuous_on tendsto_Re tendsto_Im)

corollary
  assumes "continuous_map X euclidean f"
  shows continuous_map_Re[simp,continuous_intros]: "continuous_map X euclideanreal (\<lambda>x. Re (f x))"
    and continuous_map_Im[simp,continuous_intros]: "continuous_map X euclideanreal (\<lambda>x. Im (f x))"
   by(auto intro!: continuous_map_compose[OF assms,simplified comp_def] continuous_map_Re' continuous_map_Im')

lemma continuous_map_of_real_iff[simp]:
  "continuous_map X euclidean (\<lambda>x. of_real (f x) ::  _ :: real_normed_div_algebra) \<longleftrightarrow> continuous_map X euclideanreal f"
  by(auto simp: continuous_map_atin tendsto_of_real_iff)

lemma continuous_map_complex_mult [continuous_intros]:
  fixes f :: "'a \<Rightarrow> complex"
  shows "\<lbrakk>continuous_map X euclidean f; continuous_map X euclidean g\<rbrakk> \<Longrightarrow> continuous_map X euclidean (\<lambda>x. f x * g x)"
  by (simp add: continuous_map_atin tendsto_mult)

lemma continuous_map_complex_mult_left:
  fixes f :: "'a \<Rightarrow> complex"
  shows "continuous_map X euclidean f \<Longrightarrow> continuous_map X euclidean (\<lambda>x. c * f x)"
  by(simp add: continuous_map_atin tendsto_mult)

lemma complex_continuous_map_iff:
  "continuous_map X euclidean f \<longleftrightarrow> continuous_map X euclideanreal (\<lambda>x. Re (f x)) \<and> continuous_map X euclideanreal (\<lambda>x. Im (f x))"
proof safe
  assume "continuous_map X euclideanreal (\<lambda>x. Re (f x))" "continuous_map X euclideanreal (\<lambda>x. Im (f x))"
  then have "continuous_map X euclidean (\<lambda>x. Re (f x) + \<i> * Im (f x))"
    by(auto intro!: continuous_map_add continuous_map_complex_mult_left continuous_map_compose[of X euclideanreal,simplified comp_def])
  thus "continuous_map X euclidean f"
    using complex_eq by auto
qed(use continuous_map_compose[OF _ continuous_map_Re',simplified comp_def] continuous_map_compose[OF _ continuous_map_Im',simplified comp_def] in auto)

lemma complex_integrable_iff: "complex_integrable M f \<longleftrightarrow> integrable M (\<lambda>x. Re (f x)) \<and> integrable M (\<lambda>x. Im (f x))"
proof safe
  assume h[measurable]:"integrable M (\<lambda>x. Re (f x))" "integrable M (\<lambda>x. Im (f x))"
  show "complex_integrable M f"
    unfolding integrable_iff_bounded
  proof safe
    show f[measurable]:"f \<in> borel_measurable M"
      using borel_measurable_complex_iff h by blast
    have "(\<integral>\<^sup>+ x. ennreal (cmod (f x)) \<partial>M) \<le> (\<integral>\<^sup>+ x. ennreal (\<bar>Re (f x)\<bar> + \<bar>Im (f x)\<bar>) \<partial>M)"
      by(intro nn_integral_mono ennreal_leI) (use cmod_le in auto)
    also have "... = (\<integral>\<^sup>+ x. ennreal \<bar>Re (f x)\<bar> \<partial>M) + (\<integral>\<^sup>+ x. ennreal \<bar>Im (f x)\<bar> \<partial>M)"
      by(auto intro!: nn_integral_add)
    also have "... < \<infinity>"
      using h by(auto simp: integrable_iff_bounded)
    finally show "(\<integral>\<^sup>+ x. ennreal (cmod (f x)) \<partial>M) < \<infinity>" .
  qed
qed(auto dest: integrable_Re integrable_Im)

subsection \<open> Compact Supports \<close>
definition has_compact_support_on :: "('a \<Rightarrow> 'b :: monoid_add) \<Rightarrow> 'a topology \<Rightarrow> bool"
   (infix "has'_compact'_support'_on" 60) where
   "f has_compact_support_on X \<longleftrightarrow> compactin X (X closure_of support_on (topspace X) f)"

lemma has_compact_support_on_iff:
  "f has_compact_support_on X \<longleftrightarrow> compactin X (X closure_of {x\<in>topspace X. f x \<noteq> 0})"
  by(simp add: has_compact_support_on_def support_on_def)

lemma has_compact_support_on_zero[simp]: "(\<lambda>x. 0) has_compact_support_on X"
  by(simp add: has_compact_support_on_iff)

lemma has_compact_support_on_compact_space[simp]: "compact_space X \<Longrightarrow> f has_compact_support_on X"
  by(auto simp: has_compact_support_on_def closedin_compact_space)

lemma has_compact_support_on_add[simp,intro!]:
  assumes "f has_compact_support_on X" "g has_compact_support_on X"
  shows "(\<lambda>x. f x + g x) has_compact_support_on X"
proof -
  have "support_on (topspace X) (\<lambda>x. f x + g x)
        \<subseteq> support_on (topspace X) f \<union> support_on (topspace X) g"
    by(auto simp: in_support_on)
  moreover have "compactin X (X closure_of ...)"
    using assms by(simp add: has_compact_support_on_def compactin_Un)
  ultimately show ?thesis
    unfolding has_compact_support_on_def by (meson closed_compactin closedin_closure_of closure_of_mono)
qed

lemma has_compact_support_on_sum:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> f i has_compact_support_on X"
  shows "(\<lambda>x. (\<Sum>i\<in>I. f i x)) has_compact_support_on X"
proof -
  have "support_on (topspace X) (\<lambda>x. (\<Sum>i\<in>I. f i x)) \<subseteq> (\<Union>i\<in>I. support_on (topspace X) (f i))"
    by(simp add: subset_eq) (meson in_support_on sum.neutral)
  moreover have "compactin X (X closure_of ...)"
    using assms by(auto simp: has_compact_support_on_def closure_of_Union intro!: compactin_Union)
  ultimately show ?thesis
    unfolding has_compact_support_on_def by (meson closed_compactin closedin_closure_of closure_of_mono)
qed

lemma has_compact_support_on_mult_left:
  fixes g :: "_ \<Rightarrow> _ :: mult_zero"
  assumes "g has_compact_support_on X"
  shows "(\<lambda>x. f x * g x) has_compact_support_on X"
proof -
  have "support_on (topspace X) (\<lambda>x. f x * g x) \<subseteq> support_on (topspace X) g"
    by(auto simp add: in_support_on)
  thus ?thesis
    using assms unfolding has_compact_support_on_def
    by (meson closed_compactin closedin_closure_of closure_of_mono)
qed

lemma has_compact_support_on_mult_right:
  fixes f :: "_ \<Rightarrow> _ :: mult_zero"
  assumes "f has_compact_support_on X"
  shows "(\<lambda>x. f x * g x) has_compact_support_on X"
proof -
  have "support_on (topspace X) (\<lambda>x. f x * g x) \<subseteq> support_on (topspace X) f"
    by(auto simp add: in_support_on)
  thus ?thesis
    using assms unfolding has_compact_support_on_def
    by (meson closed_compactin closedin_closure_of closure_of_mono)
qed

lemma has_compact_support_on_uminus_iff[simp]:
  fixes f :: "_ \<Rightarrow> _ :: group_add"
  shows "(\<lambda>x. - f x) has_compact_support_on X \<longleftrightarrow> f has_compact_support_on X"
  by(auto simp: has_compact_support_on_def support_on_def)

lemma has_compact_support_on_diff[simp,intro!]:
  fixes f :: "_ \<Rightarrow> _ :: group_add"
  shows "f has_compact_support_on X \<Longrightarrow> g has_compact_support_on X
         \<Longrightarrow> (\<lambda>x. f x - g x) has_compact_support_on X"
  unfolding diff_conv_add_uminus by(intro has_compact_support_on_add) auto

lemma has_compact_support_on_max[simp,intro!]:
  assumes "f has_compact_support_on X" "g has_compact_support_on X"
  shows "(\<lambda>x. max (f x) (g x)) has_compact_support_on X"
proof -
  have "support_on (topspace X) (\<lambda>x. max (f x) (g x))
        \<subseteq> support_on (topspace X)  f \<union> support_on (topspace X) g"
    by (simp add: in_support_on max_def_raw unfold_simps(2))
  moreover have "compactin X (X closure_of ...)"
    using assms by(simp add: has_compact_support_on_def compactin_Un)
  ultimately show ?thesis
    unfolding has_compact_support_on_def by (meson closed_compactin closedin_closure_of closure_of_mono)
qed

lemma has_compact_support_on_ext_iff[iff]:
  "(\<lambda>x\<in>topspace X. f x) has_compact_support_on X \<longleftrightarrow> f has_compact_support_on X"
  by(auto intro!: arg_cong2[where f=compactin] arg_cong2[where f="(closure_of)"]
            simp: has_compact_support_on_def in_support_on)

lemma has_compact_support_on_of_real_iff[iff]:
  "(\<lambda>x. of_real (f x)) has_compact_support_on X = f has_compact_support_on X"
  by(auto simp: has_compact_support_on_iff)

lemma has_compact_support_on_complex_iff:
  "f has_compact_support_on X \<longleftrightarrow>
   (\<lambda>x. Re (f x)) has_compact_support_on X \<and> (\<lambda>x. Im (f x)) has_compact_support_on X"
proof safe
  assume h:"(\<lambda>x. Re (f x)) has_compact_support_on X" "(\<lambda>x. Im (f x)) has_compact_support_on X"
  have "support_on (topspace X) f \<subseteq> support_on (topspace X) (\<lambda>x. Re (f x)) \<union> support_on (topspace X) (\<lambda>x. Im (f x))"
    using complex.expand by(auto simp: in_support_on)
  hence "X closure_of support_on (topspace X) f
         \<subseteq> X closure_of support_on (topspace X) (\<lambda>x. Re (f x)) \<union> X closure_of support_on (topspace X) (\<lambda>x. Im (f x))"
    by (metis (no_types, lifting) closure_of_Un sup.absorb_iff2)
  thus "f has_compact_support_on X"
    using h unfolding has_compact_support_on_def
    by (meson closed_compactin closedin_closure_of compactin_Un)
next
  assume h:"f has_compact_support_on X"
  have "support_on (topspace X) (\<lambda>x. Re (f x)) \<subseteq> support_on (topspace X) f"
       "support_on (topspace X) (\<lambda>x. Im (f x)) \<subseteq> support_on (topspace X) f"
    by(auto simp: in_support_on)
  thus "(\<lambda>x. Re (f x)) has_compact_support_on X" "(\<lambda>x. Im (f x)) has_compact_support_on X"
    using h by(auto simp: closed_compactin closure_of_mono  has_compact_support_on_def)
qed

lemma [simp]:
  assumes "f has_compact_support_on X"
  shows has_compact_support_on_Re:"(\<lambda>x. Re (f x)) has_compact_support_on X"
    and has_compact_support_on_Im:"(\<lambda>x. Im (f x)) has_compact_support_on X"
  using assms by(auto simp: has_compact_support_on_complex_iff)

subsection \<open> Positive Linear Functionsls \<close>
definition positive_linear_functional_on_CX :: "'a topology \<Rightarrow> (('a \<Rightarrow> 'b :: {ring, order, topological_space}) \<Rightarrow> 'b) \<Rightarrow> bool"
  where "positive_linear_functional_on_CX X \<phi> \<equiv>
  (\<forall>f. continuous_map X euclidean f \<longrightarrow> f has_compact_support_on X
        \<longrightarrow> (\<forall>x\<in>topspace X. f x \<ge> 0) \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) \<ge> 0) \<and>
  (\<forall>f a. continuous_map X euclidean f \<longrightarrow> f has_compact_support_on X
         \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. a * f x) = a * \<phi> (\<lambda>x\<in>topspace X. f x)) \<and>
  (\<forall>f g. continuous_map X euclidean f \<longrightarrow> f has_compact_support_on X
         \<longrightarrow> continuous_map X euclidean g \<longrightarrow> g has_compact_support_on X
         \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x + g x) = \<phi> (\<lambda>x\<in>topspace X. f x) + \<phi> (\<lambda>x\<in>topspace X. g x))"

lemma
  assumes "positive_linear_functional_on_CX X \<phi>"
  shows pos_lin_functional_on_CX_pos:
    "\<And>f. continuous_map X euclidean f \<Longrightarrow> f has_compact_support_on X
        \<Longrightarrow> (\<And>x. x\<in>topspace X \<Longrightarrow> f x \<ge> 0) \<Longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) \<ge> 0"
    and pos_lin_functional_on_CX_lin:
    "\<And>f a. continuous_map X euclidean f \<Longrightarrow> f has_compact_support_on X
            \<Longrightarrow> \<phi> (\<lambda>x\<in>topspace X. a * f x) = a * \<phi> (\<lambda>x\<in>topspace X. f x)"
    "\<And>f g. continuous_map X euclidean f \<Longrightarrow> f has_compact_support_on X
           \<Longrightarrow> continuous_map X euclidean g \<Longrightarrow> g has_compact_support_on X
           \<Longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x + g x) = \<phi> (\<lambda>x\<in>topspace X. f x) + \<phi> (\<lambda>x\<in>topspace X. g x)"
  using assms by(auto simp: positive_linear_functional_on_CX_def)

lemma pos_lin_functional_on_CX_pos_complex:
  assumes "positive_linear_functional_on_CX X \<phi>"
  shows "continuous_map X euclidean f \<Longrightarrow> f has_compact_support_on X
        \<Longrightarrow> (\<And>x. x\<in>topspace X \<Longrightarrow> Re (f x) \<ge> 0) \<Longrightarrow> (\<And>x. x \<in> topspace X \<Longrightarrow> f x \<in> \<real>)
        \<Longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) \<ge> 0"
  by(intro pos_lin_functional_on_CX_pos[OF assms]) (simp_all add: complex_is_Real_iff less_eq_complex_def)

lemma positive_linear_functional_on_CX_compact:
  assumes "compact_space X"
  shows "positive_linear_functional_on_CX X \<phi> \<longleftrightarrow> 
  (\<forall>f. continuous_map X euclidean f \<longrightarrow> (\<forall>x\<in>topspace X. f x \<ge> 0) \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) \<ge> 0) \<and>
  (\<forall>f a. continuous_map X euclidean f \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. a * f x) = a * \<phi> (\<lambda>x\<in>topspace X. f x)) \<and>
  (\<forall>f g. continuous_map X euclidean f \<longrightarrow> continuous_map X euclidean g
         \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x + g x) = \<phi> (\<lambda>x\<in>topspace X. f x) + \<phi> (\<lambda>x\<in>topspace X. g x))"
  by(auto simp: positive_linear_functional_on_CX_def assms)

lemma
  assumes "positive_linear_functional_on_CX X \<phi>" "compact_space X"
  shows pos_lin_functional_on_CX_compact_pos:
    "\<And>f. continuous_map X euclidean f
        \<Longrightarrow> (\<And>x. x\<in>topspace X \<Longrightarrow> f x \<ge> 0) \<Longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) \<ge> 0"
    and pos_lin_functional_on_CX_compact_lin:
    "\<And>f a. continuous_map X euclidean f
            \<Longrightarrow> \<phi> (\<lambda>x\<in>topspace X. a * f x) = a * \<phi> (\<lambda>x\<in>topspace X. f x)"
    "\<And>f g. continuous_map X euclidean f \<Longrightarrow> continuous_map X euclidean g
           \<Longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x + g x) = \<phi> (\<lambda>x\<in>topspace X. f x) + \<phi> (\<lambda>x\<in>topspace X. g x)"
  using assms(1) by(auto simp: positive_linear_functional_on_CX_compact assms(2))

lemma pos_lin_functional_on_CX_diff:
  fixes f :: "_ \<Rightarrow> _ :: {real_normed_vector, ring_1}"
  assumes "positive_linear_functional_on_CX X \<phi>"
    and cont:"continuous_map X euclidean f" "continuous_map X euclidean g"
    and csupp: "f has_compact_support_on X" "g has_compact_support_on X"
  shows "\<phi> (\<lambda>x\<in>topspace X. f x - g x) = \<phi> (\<lambda>x\<in>topspace X. f x) - \<phi> (\<lambda>x\<in>topspace X. g x)"
  using pos_lin_functional_on_CX_lin(2)[OF assms(1),of f "\<lambda>x. - g x"] cont csupp
    pos_lin_functional_on_CX_lin(1)[OF assms(1) cont(2) csupp(2),of "- 1"] by simp

lemma pos_lin_functional_on_CX_compact_diff:
  fixes f :: "_ \<Rightarrow> _ :: {real_normed_vector, ring_1}"
  assumes "positive_linear_functional_on_CX X \<phi>" "compact_space X"
    and "continuous_map X euclidean f" "continuous_map X euclidean g"
  shows "\<phi> (\<lambda>x\<in>topspace X. f x - g x) = \<phi> (\<lambda>x\<in>topspace X. f x) - \<phi> (\<lambda>x\<in>topspace X. g x)"
  using assms(2) by(auto intro!: pos_lin_functional_on_CX_diff assms)

lemma pos_lin_functional_on_CX_mono:
  fixes f :: "_ \<Rightarrow> _ :: {real_normed_vector, ring_1, ordered_ab_group_add}"
  assumes "positive_linear_functional_on_CX X \<phi>"
    and mono:"\<And>x. x \<in> topspace X \<Longrightarrow> f x \<le> g x"
    and cont:"continuous_map X euclidean f" "continuous_map X euclidean g"
    and csupp: "f has_compact_support_on X" "g has_compact_support_on X"
  shows "\<phi> (\<lambda>x\<in>topspace X. f x) \<le> \<phi> (\<lambda>x\<in>topspace X. g x)"
proof -
  have "\<phi> (\<lambda>x\<in>topspace X. f x) \<le> \<phi> (\<lambda>x\<in>topspace X. f x) + \<phi> (\<lambda>x\<in>topspace X. g x - f x)"
    by(auto intro!: pos_lin_functional_on_CX_pos[OF assms(1)] assms continuous_map_diff)
  also have "... = \<phi> (\<lambda>x\<in>topspace X. f x + (g x - f x))"
    by(intro pos_lin_functional_on_CX_lin(2)[symmetric]) (auto intro!: assms continuous_map_diff)
  also have "... = \<phi> (\<lambda>x\<in>topspace X. g x)"
    by simp
  finally show ?thesis .
qed

lemma pos_lin_functional_on_CX_compact_mono:
  fixes f :: "_ \<Rightarrow> _ :: {real_normed_vector, ring_1, ordered_ab_group_add}"
  assumes "positive_linear_functional_on_CX X \<phi>" "compact_space X"
    and "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<le> g x"
    and "continuous_map X euclidean f" "continuous_map X euclidean g"
  shows "\<phi> (\<lambda>x\<in>topspace X. f x) \<le> \<phi> (\<lambda>x\<in>topspace X. g x)"
  using assms(2) by(auto intro!: assms pos_lin_functional_on_CX_mono)

lemma pos_lin_functional_on_CX_zero:
  assumes "positive_linear_functional_on_CX X \<phi>"
  shows "\<phi> (\<lambda>x\<in>topspace X. 0) = 0"
proof -
  have "\<phi> (\<lambda>x\<in>topspace X. 0) = \<phi> (\<lambda>x\<in>topspace X. 0 * 0)"
    by simp
  also have "... = 0 * \<phi> (\<lambda>x\<in>topspace X. 0)"
    by(intro pos_lin_functional_on_CX_lin) (auto simp: assms)
  finally show ?thesis
    by simp
qed

lemma pos_lin_functional_on_CX_uminus:
  fixes f :: "_ \<Rightarrow> _ :: {real_normed_vector, ring_1}"
  assumes "positive_linear_functional_on_CX X \<phi>"
    and "continuous_map X euclidean f"
    and csupp: "f has_compact_support_on X"
  shows "\<phi> (\<lambda>x\<in>topspace X. - f x) = - \<phi> (\<lambda>x\<in>topspace X. f x)"
  using pos_lin_functional_on_CX_diff[of X \<phi> "\<lambda>x. 0" f]
  by(auto simp: assms pos_lin_functional_on_CX_zero)

lemma pos_lin_functional_on_CX_compact_uminus:
  fixes f :: "_ \<Rightarrow> _ :: {real_normed_vector, ring_1}"
  assumes "positive_linear_functional_on_CX X \<phi>" "compact_space X"
    and "continuous_map X euclidean f"
  shows "\<phi> (\<lambda>x\<in>topspace X. - f x) = - \<phi> (\<lambda>x\<in>topspace X. f x)"
  using pos_lin_functional_on_CX_diff[of X \<phi> "\<lambda>x. 0" f]
  by(auto simp: assms pos_lin_functional_on_CX_zero)

lemma pos_lin_functional_on_CX_sum:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow>  _ :: {real_normed_vector}"
  assumes "positive_linear_functional_on_CX X \<phi>"
    and "finite I" "\<And>i. i \<in> I \<Longrightarrow> continuous_map X euclidean (f i)"
    and "\<And>i. i \<in> I \<Longrightarrow> f i has_compact_support_on X"
  shows "\<phi> (\<lambda>x\<in>topspace X. (\<Sum>i\<in>I. f i x)) = (\<Sum>i\<in>I. \<phi> (\<lambda>x\<in>topspace X. f i x))"
  using assms(2,3,4)
proof induction
  case empty
  show ?case
    using pos_lin_functional_on_CX_zero[OF assms(1)] by(simp add: restrict_def)
next
  case ih:(insert a F)
  show ?case (is "?lhs = ?rhs")
  proof -
    have "?lhs = \<phi> (\<lambda>x\<in>topspace X. f a x + (\<Sum>i\<in>F. f i x))"
      by(simp add: sum.insert_if[OF ih(1)] ih(2) restrict_def)
    also have "... = \<phi> (\<lambda>x\<in>topspace X. f a x) + \<phi> (\<lambda>x\<in>topspace X. (\<Sum>i\<in>F. f i x))"
      by (auto intro!: pos_lin_functional_on_CX_lin[OF assms(1)]
                       has_compact_support_on_sum ih continuous_map_sum)
    also have "... = ?rhs"
      by(simp add: ih) (simp add: restrict_def)
    finally show ?thesis .
  qed
qed

lemma pos_lin_functional_on_CX_pos_is_real:
  fixes f :: "_ \<Rightarrow> complex"
  assumes "positive_linear_functional_on_CX X \<phi>"
    and "continuous_map X euclidean f" "f has_compact_support_on X"
    and "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<in> \<real>"
  shows "\<phi> (\<lambda>x\<in>topspace X. f x) \<in> \<real>"
proof -
  have "\<phi> (\<lambda>x\<in>topspace X. f x) = \<phi> (\<lambda>x\<in>topspace X. complex_of_real (Re (f x)))"
    by (metis (no_types, lifting) assms(4) of_real_Re restrict_ext)
  also have "... = \<phi> (\<lambda>x\<in>topspace X. complex_of_real (max 0 (Re (f x))) - complex_of_real (max 0 (- Re (f x))))"
    by (metis (no_types, opaque_lifting) diff_0 diff_0_right equation_minus_iff max.absorb_iff2 max.order_iff neg_0_le_iff_le nle_le of_real_diff)
  also have "... = \<phi> (\<lambda>x\<in>topspace X. complex_of_real (max 0 (Re (f x)))) - \<phi> (\<lambda>x\<in>topspace X. complex_of_real (max 0 (- Re (f x))))"
    using assms by(auto intro!: pos_lin_functional_on_CX_diff continuous_map_real_max)
  also have "... \<in> \<real>"
    using assms by(intro Reals_diff)
      (auto intro!: nonnegative_complex_is_real pos_lin_functional_on_CX_pos[OF assms(1)] continuous_map_real_max
              simp: less_eq_complex_def)
  finally show ?thesis .
qed

lemma
  fixes \<phi> X
  defines "\<phi>' \<equiv> (\<lambda>f. Re (\<phi> (\<lambda>x\<in>topspace X. complex_of_real (f x))))"
  assumes plf:"positive_linear_functional_on_CX X \<phi>"
  shows pos_lin_functional_on_CX_complex_decompose:
    "\<And>f. continuous_map X euclidean f \<Longrightarrow> f has_compact_support_on X
      \<Longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x)
          = complex_of_real (\<phi>' (\<lambda>x\<in>topspace X. Re (f x))) + \<i> * complex_of_real (\<phi>' (\<lambda>x\<in>topspace X. Im (f x)))"
    and pos_lin_functional_on_CX_complex_decompose_plf:
    "positive_linear_functional_on_CX X \<phi>'"
proof -
  fix f :: "_ \<Rightarrow> complex"
  assume f:"continuous_map X euclidean f" "f has_compact_support_on X"
  show "\<phi> (\<lambda>x\<in>topspace X. f x)
          = complex_of_real (\<phi>' (\<lambda>x\<in>topspace X. Re (f x))) + \<i> * complex_of_real (\<phi>' (\<lambda>x\<in>topspace X. Im (f x)))"
    (is "?lhs = ?rhs")
  proof -
    have "\<phi> (\<lambda>x\<in>topspace X. f x) = \<phi> (\<lambda>x\<in>topspace X. Re (f x) + \<i> * Im (f x))"
      using complex_eq by presburger
    also have "... = \<phi> (\<lambda>x\<in>topspace X. complex_of_real (Re (f x))) + \<phi> (\<lambda>x\<in>topspace X. \<i> * complex_of_real (Im (f x)))"
      using f by(auto intro!: pos_lin_functional_on_CX_lin[OF plf] has_compact_support_on_mult_left continuous_map_complex_mult_left)
    also have "... = \<phi> (\<lambda>x\<in>topspace X. complex_of_real (Re (f x))) + \<i> * \<phi> (\<lambda>x\<in>topspace X. complex_of_real (Im (f x)))"
      using f by(auto intro!: pos_lin_functional_on_CX_lin[OF plf])
    also have "... = complex_of_real (\<phi>' (\<lambda>x\<in>topspace X. (Re (f x)))) + \<i> * complex_of_real (\<phi>' (\<lambda>x\<in>topspace X. Im (f x)))"
    proof -
      have [simp]: "complex_of_real (\<phi>' (\<lambda>x\<in>topspace X. Re (f x))) = \<phi> (\<lambda>x\<in>topspace X. complex_of_real (Re (f x)))"
        (is "?l = ?r")
      proof -
        have "?l = complex_of_real (Re (\<phi> (\<lambda>x\<in>topspace X. complex_of_real (Re (f x)))))"
          by (metis (mono_tags, lifting) \<phi>'_def restrict_apply' restrict_ext)
        also have "... = ?r"
          by(intro of_real_Re pos_lin_functional_on_CX_pos_is_real[OF plf]) (use f in auto)
        finally show ?thesis .
      qed
      have [simp]: "complex_of_real (\<phi>' (\<lambda>x\<in>topspace X. Im (f x))) = \<phi> (\<lambda>x\<in>topspace X. complex_of_real (Im (f x)))"
        (is "?l = ?r")
      proof -
        have "?l = complex_of_real (Re (\<phi> (\<lambda>x\<in>topspace X. complex_of_real (Im (f x)))))"
          by (metis (mono_tags, lifting) \<phi>'_def restrict_apply' restrict_ext)
        also have "... = ?r"
          by(intro of_real_Re pos_lin_functional_on_CX_pos_is_real[OF plf]) (use f in auto)
        finally show ?thesis .
      qed
      show ?thesis by simp
    qed
    finally show ?thesis .
  qed
next
  show "positive_linear_functional_on_CX X \<phi>'"
    unfolding positive_linear_functional_on_CX_def
  proof safe
    fix f
    assume f:"continuous_map X euclideanreal f" "f has_compact_support_on X" "\<forall>x\<in>topspace X. 0 \<le> f x"
    show "\<phi>' (\<lambda>x\<in>topspace X. f x) \<ge> 0"
    proof -
      have "0 \<le> \<phi> (\<lambda>x\<in>topspace X. complex_of_real (f x))"
        using f by(intro pos_lin_functional_on_CX_pos[OF plf]) (simp_all add: less_eq_complex_def)
      hence "0 \<le> Re (\<phi> (\<lambda>x\<in>topspace X. complex_of_real (f x)))"
        by (simp add: less_eq_complex_def)
      also have "... = \<phi>' (\<lambda>x\<in>topspace X. f x)"
        by (metis (mono_tags, lifting) \<phi>'_def restrict_apply' restrict_ext)
      finally show ?thesis .
    qed
  next
    fix a f
    assume f:"continuous_map X euclideanreal f" "f has_compact_support_on X"
    show "\<phi>' (\<lambda>x\<in>topspace X. a * f x) = a * \<phi>' (\<lambda>x\<in>topspace X. f x)"
    proof -
      have *:"\<phi> (\<lambda>x\<in>topspace X. complex_of_real a * complex_of_real (f x)) = complex_of_real a * \<phi> (\<lambda>x\<in>topspace X. complex_of_real (f x))"
        using f by(auto intro!: pos_lin_functional_on_CX_lin[OF plf])
      have "\<phi>' (\<lambda>x\<in>topspace X. a * f x) = Re (\<phi> (\<lambda>x\<in>topspace X. complex_of_real a * complex_of_real (f x)))"
        by (metis (mono_tags, lifting) \<phi>'_def of_real_mult restrict_apply' restrict_ext)
      also have "... =  a * (Re (\<phi> (\<lambda>x\<in>topspace X. complex_of_real (f x))))"
        unfolding * by simp
      also have "... =  a * \<phi>' (\<lambda>x\<in>topspace X. f x)"
        by (metis (mono_tags, lifting) \<phi>'_def restrict_apply' restrict_ext)
      finally show ?thesis .
    qed
  next
    fix f g
    assume fg:"continuous_map X euclideanreal f" "f has_compact_support_on X"
              "continuous_map X euclideanreal g" "g has_compact_support_on X"
    show "\<phi>' (\<lambda>x\<in>topspace X. f x + g x) = \<phi>' (\<lambda>x\<in>topspace X. f x) + \<phi>' (\<lambda>x\<in>topspace X. g x)"
    proof -
      have *: "\<phi> (\<lambda>x\<in>topspace X. complex_of_real (f x) + complex_of_real (g x)) = \<phi> (\<lambda>x\<in>topspace X. complex_of_real (f x)) + \<phi> (\<lambda>x\<in>topspace X. complex_of_real (g x))"
        using fg by(auto intro!: pos_lin_functional_on_CX_lin[OF plf])
      have "\<phi>' (\<lambda>x\<in>topspace X. f x + g x) = Re (\<phi> (\<lambda>x\<in>topspace X. complex_of_real (f x + g x)))"
        by (metis (mono_tags, lifting) \<phi>'_def restrict_apply' restrict_ext)
      also have "... = Re (\<phi> (\<lambda>x\<in>topspace X. complex_of_real (f x)) + \<phi> (\<lambda>x\<in>topspace X. complex_of_real (g x)))"
        unfolding of_real_add * by simp
      also have "... = Re (\<phi> (\<lambda>x\<in>topspace X. complex_of_real (f x))) + Re (\<phi> (\<lambda>x\<in>topspace X. complex_of_real (g x)))"
        by simp
      also have "... = \<phi>' (\<lambda>x\<in>topspace X. f x) + \<phi>' (\<lambda>x\<in>topspace X. g x)"
        by (metis (mono_tags, lifting) \<phi>'_def restrict_apply' restrict_ext)
      finally show ?thesis .
    qed
  qed
qed

subsection \<open> Lemmas for Uniqueness \<close>
lemma rep_measures_real_unique:
  assumes "locally_compact_space X" "Hausdorff_space X"
  assumes N: "subalgebra N (borel_of X)"
    "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> f has_compact_support_on X \<Longrightarrow> integrable N f"
        "\<And>A. A\<in>sets N \<Longrightarrow> emeasure N A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N C)"
        "\<And>A. openin X A \<Longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K)"
        "\<And>A. A\<in>sets N \<Longrightarrow> emeasure N A < \<infinity> \<Longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K)"
        "\<And>K. compactin X K \<Longrightarrow> N K < \<infinity>"
      assumes M: "subalgebra M (borel_of X)"
        "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> f has_compact_support_on X \<Longrightarrow> integrable M f"
        "\<And>A. A\<in>sets M \<Longrightarrow> emeasure M A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure M C)"
        "\<And>A. openin X A \<Longrightarrow> emeasure M A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure M K)"
        "\<And>A. A\<in>sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow> emeasure M A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure M K)"
        "\<And>K. compactin X K \<Longrightarrow> M K < \<infinity>"
    and sets_eq: "sets N = sets M"
    and integ_eq: "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> f has_compact_support_on X \<Longrightarrow> (\<integral>x. f x \<partial>N) = (\<integral>x. f x \<partial>M)"
  shows "N = M"
proof(intro measure_eqI sets_eq)
  have space_N: "space N = topspace X" and space_M: "space M = topspace X"
    using N(1) M(1) by(auto simp: subalgebra_def space_borel_of)
  have "N K = M K" if K:"compactin X K" for K
  proof -
    have kc: "kc_space X"
      using Hausdorff_imp_kc_space assms(2) by blast
    have K_sets[measurable]: "K \<in> sets N" "K \<in> sets M"
      using N(1) M(1) compactin_imp_closedin_gen[OF kc K]
      by(auto simp: borel_of_closed subalgebra_def)
    show ?thesis
    proof(rule antisym[OF ennreal_le_epsilon ennreal_le_epsilon])
      fix e :: real
      assume e: "e > 0"
      show "emeasure N K \<le> emeasure M K + ennreal e"
      proof -
        have "emeasure M K \<ge>  \<Sqinter> (emeasure M ` {C. openin X C \<and> K \<subseteq> C})"
          by(simp add: M(3)[OF K_sets(2)])
        from Inf_le_iff[THEN iffD1,OF this,rule_format,of "emeasure M K + e"]
        obtain U where U:"openin X U" "K \<subseteq> U" "emeasure M U < emeasure M K + ennreal e"
          using K M(6) e by fastforce
        then have [measurable]: "U \<in> sets M"
          using M(1) by(auto simp: subalgebra_def borel_of_open)
        then obtain f where f:"continuous_map X (top_of_set {0..1::real}) f"
          "f ` (topspace X - U) \<subseteq> {0}" "f ` K \<subseteq> {1}"
          "disjnt (X closure_of {x \<in> topspace X. f x \<noteq> 0}) (topspace X - U)"
          "compactin X (X closure_of {x \<in> topspace X. f x \<noteq> 0})"
          using Urysohn_locally_compact_Hausdorff_closed_compact_support[OF assms(1) disjI1[OF assms(2)],of 0 1 "topspace X - U" K] U K
          by(simp add: closedin_def disjnt_iff) blast
        have f_int: "integrable N f" "integrable M f"
          using f by(auto intro!: N M simp: continuous_map_in_subtopology has_compact_support_on_iff)
        have f_01: "x \<in> topspace X \<Longrightarrow> 0 \<le> f x" "x \<in> topspace X \<Longrightarrow> f x \<le> 1" for x
          using continuous_map_image_subset_topspace[OF f(1)] by auto
        have "emeasure N K = (\<integral>\<^sup>+x. indicator K x \<partial>N)"
          by simp
        also have "... \<le> (\<integral>\<^sup>+x. f x \<partial>N)"
          using f(3) by(intro nn_integral_mono) (auto simp: indicator_def)
        also have "... = ennreal (\<integral>x. f x \<partial>N)"
          by(rule nn_integral_eq_integral) (use f_int continuous_map_image_subset_topspace[OF f(1)] f_01 space_N in auto)
        also have "... = ennreal (\<integral>x. f x \<partial>M)"
          using f by(auto intro!: ennreal_cong integ_eq simp: continuous_map_in_subtopology has_compact_support_on_iff)
        also have "... = (\<integral>\<^sup>+x. f x \<partial>M)"
          by(rule nn_integral_eq_integral[symmetric])
            (use f_int continuous_map_image_subset_topspace[OF f(1)] f_01 space_M in auto)
        also have "... \<le> (\<integral>\<^sup>+x. indicator U x \<partial>M)"
          using f(2) f_01 by(intro nn_integral_mono) (auto simp: indicator_def space_M)
        also have "... = emeasure M U"
          by simp
        also have "... < emeasure M K + ennreal e"
          by fact
        finally show ?thesis
          by simp
      qed
    next
      fix e :: real
      assume e: "e > 0"
      show "emeasure M K \<le> emeasure N K + ennreal e"
      proof -
        have "emeasure N K \<ge>  \<Sqinter> (emeasure N ` {C. openin X C \<and> K \<subseteq> C})"
          by(simp add: N(3)[OF K_sets(1)])
        from Inf_le_iff[THEN iffD1,OF this,rule_format,of "emeasure N K + e"]
        obtain U where U:"openin X U" "K \<subseteq> U" "emeasure N U < emeasure N K + ennreal e"
          using K N(6) e by fastforce
        then have [measurable]: "U \<in> sets N"
          using N(1) by(auto simp: subalgebra_def borel_of_open)
        then obtain f where f:"continuous_map X (top_of_set {0..1::real}) f"
          "f ` (topspace X - U) \<subseteq> {0}" "f ` K \<subseteq> {1}"
          "disjnt (X closure_of {x \<in> topspace X. f x \<noteq> 0}) (topspace X - U)"
          "compactin X (X closure_of {x \<in> topspace X. f x \<noteq> 0})"
          using Urysohn_locally_compact_Hausdorff_closed_compact_support[OF assms(1) disjI1[OF assms(2)],of 0 1 "topspace X - U" K] U K
          by(simp add: closedin_def disjnt_iff) blast
        have f_int: "integrable N f" "integrable M f"
          using f by(auto intro!: N M simp: continuous_map_in_subtopology has_compact_support_on_iff)
        have f_01: "x \<in> topspace X \<Longrightarrow> 0 \<le> f x" "x \<in> topspace X \<Longrightarrow> f x \<le> 1" for x
          using continuous_map_image_subset_topspace[OF f(1)] by auto
        have "emeasure M K = (\<integral>\<^sup>+x. indicator K x \<partial>M)"
          by simp
        also have "... \<le> (\<integral>\<^sup>+x. f x \<partial>M)"
          using f(3) by(intro nn_integral_mono) (auto simp: indicator_def)
        also have "... = ennreal (\<integral>x. f x \<partial>M)"
          by(rule nn_integral_eq_integral) (use f_int continuous_map_image_subset_topspace[OF f(1)] f_01 space_M in auto)
        also have "... = ennreal (\<integral>x. f x \<partial>N)"
          using f by(auto intro!: ennreal_cong integ_eq[symmetric] simp: continuous_map_in_subtopology has_compact_support_on_iff)
        also have "... = (\<integral>\<^sup>+x. f x \<partial>N)"
          by(rule nn_integral_eq_integral[symmetric])
            (use f_int continuous_map_image_subset_topspace[OF f(1)] f_01 space_N in auto)
        also have "... \<le> (\<integral>\<^sup>+x. indicator U x \<partial>N)"
          using f(2) f_01 by(intro nn_integral_mono) (auto simp: indicator_def space_N)
        also have "... = emeasure N U"
          by simp
        also have "... < emeasure N K + ennreal e"
          by fact
        finally show ?thesis
          by simp
      qed
    qed
  qed
  hence "\<And>A. openin X A \<Longrightarrow> emeasure N A = emeasure M A"
    by(auto simp: N(4) M(4))
  thus "\<And>A. A \<in> sets N \<Longrightarrow> emeasure N A = emeasure M A"
    using N(3) M(3) by(auto simp: sets_eq)
qed

lemma rep_measures_complex_unique:
  fixes X :: "'a topology"
  assumes "locally_compact_space X" "Hausdorff_space X"
  assumes N: "subalgebra N (borel_of X)"
    "\<And>f. continuous_map X euclidean f \<Longrightarrow> f has_compact_support_on X \<Longrightarrow> complex_integrable N f"
        "\<And>A. A\<in>sets N \<Longrightarrow> emeasure N A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N C)"
        "\<And>A. openin X A \<Longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K)"
        "\<And>A. A\<in>sets N \<Longrightarrow> emeasure N A < \<infinity> \<Longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K)"
        "\<And>K. compactin X K \<Longrightarrow> N K < \<infinity>"
      assumes M: "subalgebra M (borel_of X)"
        "\<And>f. continuous_map X euclidean f \<Longrightarrow> f has_compact_support_on X \<Longrightarrow> complex_integrable M f"
        "\<And>A. A\<in>sets M \<Longrightarrow> emeasure M A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure M C)"
        "\<And>A. openin X A \<Longrightarrow> emeasure M A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure M K)"
        "\<And>A. A\<in>sets M \<Longrightarrow> emeasure M A < \<infinity> \<Longrightarrow> emeasure M A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure M K)"
        "\<And>K. compactin X K \<Longrightarrow> M K < \<infinity>"
    and sets_eq: "sets N = sets M"
    and integ_eq: "\<And>f::'a \<Rightarrow> complex. continuous_map X euclidean f \<Longrightarrow> f has_compact_support_on X
                   \<Longrightarrow> (\<integral>x. f x \<partial>N) = (\<integral>x. f x \<partial>M)"
  shows "N = M"
proof(rule rep_measures_real_unique[OF assms(1,2)])
  fix f
  assume f:"continuous_map X euclideanreal f" "f has_compact_support_on X"
  show "(\<integral>x. f x \<partial>N) = (\<integral>x. f x \<partial>M)"
  proof -
    have "(\<integral>x. f x \<partial>N) = Re (\<integral>x. (complex_of_real (f x)) \<partial>N)"
      by simp
    also have "... = Re (\<integral>x. (complex_of_real (f x)) \<partial>M)"
    proof -
      have 1:"(\<integral>x. (complex_of_real (f x)) \<partial>N) = (\<integral>x. (complex_of_real (f x)) \<partial>M)"
        by(rule integ_eq) (auto intro!: f)
      show ?thesis
        unfolding 1 by simp
    qed
    finally show ?thesis
      by simp
  qed
next
  fix f
  assume "continuous_map X euclideanreal f" "f has_compact_support_on X"
  hence "complex_integrable N (\<lambda>x. complex_of_real (f x))" "complex_integrable M (\<lambda>x. complex_of_real (f x))"
    by (auto intro!: M N)
  thus "integrable N f" "integrable M f"
    using complex_of_real_integrable_eq by auto
qed fact+

lemma finite_tight_measure_eq:
  assumes "locally_compact_space X" "metrizable_space X" "tight_on X N" "tight_on X M"
    and integ_eq: "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> f \<in> topspace X \<rightarrow> {0..1} \<Longrightarrow> (\<integral>x. f x \<partial>N) = (\<integral>x. f x \<partial>M)"
  shows "N = M"
proof(rule measure_eqI)
  interpret N: finite_measure N
    using assms(3) tight_on_def by blast
  interpret M: finite_measure M
    using assms(4) tight_on_def by blast
  have integ_N: "\<And>A. A \<in> sets N \<Longrightarrow> integrable N (indicat_real A)"
   and integ_M: "\<And>A. A \<in> sets M \<Longrightarrow> integrable M (indicat_real A)"
    by (auto simp add: N.emeasure_eq_measure M.emeasure_eq_measure)
  have sets_N: "sets N = borel_of X" and space_N: "space N = topspace X"
   and sets_M: "sets M = borel_of X" and space_M: "space M = topspace X"
    using assms(3,4) sets_eq_imp_space_eq[of _ "borel_of X"]
    by(auto simp: tight_on_def space_borel_of)
  fix A
  assume [measurable]:"A \<in> sets N"
  then have [measurable]: "A \<in> sets M"
    using sets_M sets_N by blast
  have "measure M A = \<Squnion> (Sigma_Algebra.measure M ` {K. compactin X K \<and> K \<subseteq> A})"
    by(auto intro!: inner_regular''[OF assms(2,4)])
  also have "... = \<Squnion> (Sigma_Algebra.measure N ` {K. compactin X K \<and> K \<subseteq> A})"
  proof -
    have "measure M K = measure N K" if K:"compactin X K" "K \<subseteq> A" for K
    proof -
      have [measurable]: "K \<in> sets M" "K \<in> sets N"
        by(auto simp: sets_M sets_N intro!: borel_of_closed compactin_imp_closedin K metrizable_imp_Hausdorff_space assms)
      show ?thesis
      proof(rule antisym[OF field_le_epsilon field_le_epsilon])
        fix e :: real
        assume e:"e > 0"
        have "\<forall>y>measure N K. \<exists>a\<in>measure N ` {C. openin X C \<and> K \<subseteq> C}. a < y"
          by(intro cInf_le_iff[THEN iffD1] eq_refl[OF N.outer_regularD[OF N.outer_regular'[OF assms(2) sets_N[symmetric]],symmetric]])
            (auto intro!: bdd_belowI[where m=0] compactin_subset_topspace[OF K(1)])
        from this[rule_format,of "measure N K + e"] obtain U where U: "openin X U" "K \<subseteq> U" "measure N U < measure N K + e"
          using e by auto
        then have [measurable]: "U \<in> sets M" "U \<in> sets N"
          by(auto simp: sets_N sets_M intro!: borel_of_open)
        obtain f where f:"continuous_map X (top_of_set {0..1::real}) f"
          "f ` (topspace X - U) \<subseteq> {0}" "f ` K \<subseteq> {1}"
          "disjnt (X closure_of {x \<in> topspace X. f x \<noteq> 0}) (topspace X - U)"
          "compactin X (X closure_of {x \<in> topspace X. f x \<noteq> 0})"
          using Urysohn_locally_compact_Hausdorff_closed_compact_support[OF assms(1) disjI1[OF metrizable_imp_Hausdorff_space[OF assms(2)]],of 0 1 "topspace X - U" K] U K
          by(simp add: closedin_def disjnt_iff) blast
        hence f': "continuous_map X euclideanreal f"
          "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<ge> 0" "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<le> 1"
          by (auto simp add: continuous_map_in_subtopology)
        have [measurable]: "f \<in> borel_measurable M" "f \<in> borel_measurable N"
          using continuous_map_measurable[OF f'(1)]
          by(auto simp: borel_of_euclidean sets_N sets_M cong: measurable_cong_sets)
        from f'(2,3) have f_int[simp]: "integrable M f" "integrable N f"
          by(auto intro!: M.integrable_const_bound[where B=1] N.integrable_const_bound[where B=1] simp: space_N space_M)
        have "measure M K = (\<integral>x. indicator K x \<partial>M)"
          by simp
        also have "... \<le> (\<integral>x. f x \<partial>M)"
          using f(3) f'(2) by(intro integral_mono integ_M) (auto simp: space_M indicator_def)
        also have "... = (\<integral>x. f x \<partial>N)"
          by(auto intro!: integ_eq[symmetric] f')
        also have "... \<le> (\<integral>x. indicator U x \<partial>N)"
          using f(2) f'(3) by(intro integral_mono integ_N) (auto simp: space_N indicator_def)
        also have "... \<le> measure N K + e"
          using U(3) by fastforce
        finally show "measure M K \<le> measure N K + e" .
      next
        fix e :: real
        assume e:"e > 0"
        have "\<forall>y>measure M K. \<exists>a\<in>measure M ` {C. openin X C \<and> K \<subseteq> C}. a < y"
          by(intro cInf_le_iff[THEN iffD1] eq_refl[OF M.outer_regularD[OF M.outer_regular'[OF assms(2) sets_M[symmetric]],symmetric]])
            (auto intro!: bdd_belowI[where m=0] compactin_subset_topspace[OF K(1)])
        from this[rule_format,of "measure M K + e"] obtain U where U: "openin X U" "K \<subseteq> U" "measure M U < measure M K + e"
          using e by auto
        then have [measurable]: "U \<in> sets M" "U \<in> sets N"
          by(auto simp: sets_N sets_M intro!: borel_of_open)
        obtain f where f:"continuous_map X (top_of_set {0..1::real}) f"
          "f ` (topspace X - U) \<subseteq> {0}" "f ` K \<subseteq> {1}"
          "disjnt (X closure_of {x \<in> topspace X. f x \<noteq> 0}) (topspace X - U)"
          "compactin X (X closure_of {x \<in> topspace X. f x \<noteq> 0})"
          using Urysohn_locally_compact_Hausdorff_closed_compact_support[OF assms(1) disjI1[OF metrizable_imp_Hausdorff_space[OF assms(2)]],of 0 1 "topspace X - U" K] U K
          by(simp add: closedin_def disjnt_iff) blast
        hence f': "continuous_map X euclideanreal f"
          "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<ge> 0" "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<le> 1"
          by (auto simp add: continuous_map_in_subtopology)
        have [measurable]: "f \<in> borel_measurable M" "f \<in> borel_measurable N"
          using continuous_map_measurable[OF f'(1)]
          by(auto simp: borel_of_euclidean sets_N sets_M cong: measurable_cong_sets)
        from f'(2,3) have f_int[simp]: "integrable M f" "integrable N f"
          by(auto intro!: M.integrable_const_bound[where B=1] N.integrable_const_bound[where B=1] simp: space_N space_M)
        have "measure N K = (\<integral>x. indicator K x \<partial>N)"
          by simp
        also have "... \<le> (\<integral>x. f x \<partial>N)"
          using f(3) f'(2) by(intro integral_mono integ_N) (auto simp: space_N indicator_def)
        also have "... = (\<integral>x. f x \<partial>M)"
          by(auto intro!: integ_eq f')
        also have "... \<le> (\<integral>x. indicator U x \<partial>M)"
          using f(2) f'(3) by(intro integral_mono integ_M) (auto simp: space_M indicator_def)
        also have "... \<le> measure M K + e"
          using U(3) by fastforce
        finally show "measure N K \<le> measure M K + e" .
      qed
    qed
    thus ?thesis
      by simp
  qed
  also have "... = measure N A"
    by(auto intro!: inner_regular''[symmetric,OF assms(2,3)])
  finally show "emeasure N A = emeasure M A"
    using M.emeasure_eq_measure N.emeasure_eq_measure by presburger
qed(insert assms(3,4), auto simp: tight_on_def)

subsection \<open> Riesez Representation Theorem for Real Numbers \<close>
theorem Riesz_representation_real_complete:
  fixes X :: "'a topology" and \<phi> :: "('a \<Rightarrow> real) \<Rightarrow> real"
  assumes lh:"locally_compact_space X" "Hausdorff_space X"
    and plf:"positive_linear_functional_on_CX X \<phi>"
  shows "\<exists>M. \<exists>!N. sets N = M \<and> subalgebra N (borel_of X)
         \<and> (\<forall>A\<in>sets N. emeasure N A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N C))
         \<and> (\<forall>A. openin X A \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))
         \<and> (\<forall>A\<in>sets N. emeasure N A < \<infinity>
                       \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))
         \<and> (\<forall>K. compactin X K \<longrightarrow> emeasure N K < \<infinity>)
         \<and> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow> f has_compact_support_on X \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))
         \<and> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow> f has_compact_support_on X \<longrightarrow> integrable N f)
         \<and> complete_measure N"
proof -
  let ?iscont = "\<lambda>f. continuous_map X euclideanreal f"
  let ?csupp = "\<lambda>f. f has_compact_support_on X"
  let ?fA = "\<lambda>A f. ?iscont f \<and> ?csupp f \<and> X closure_of {x\<in>topspace X. f x \<noteq> 0} \<subseteq> A
                    \<and> f \<in> topspace X \<rightarrow> {0..1} \<and> f \<in> topspace X - A \<rightarrow> {0}"
  let ?fK = "\<lambda>K f. ?iscont f \<and> ?csupp f \<and> f \<in> topspace X \<rightarrow> {0..1} \<and> f \<in> K \<rightarrow> {1}"

  have ext_sup[simp]:
    "\<And>P Q. {x\<in>topspace X. (if x \<in> topspace X then P x else Q x) \<noteq> 0} = {x\<in>topspace X. P x \<noteq> 0}"
    by fastforce
  have times_unfold[simp]: "\<And>P Q. {x\<in>topspace X. P x \<and> Q x} = {x\<in>topspace X. P x} \<inter> {x\<in>topspace X. Q x}"
    by fastforce
  note pos    = pos_lin_functional_on_CX_pos[OF plf]
  note linear = pos_lin_functional_on_CX_lin[OF plf]
  note \<phi>diff  = pos_lin_functional_on_CX_diff[OF plf]
  note \<phi>mono  = pos_lin_functional_on_CX_mono[OF plf]
  note \<phi>_0    = pos_lin_functional_on_CX_zero[OF plf]

  text \<open> Lemma 2.13~\cite{Rudin}.\<close>
  have fApartition: "\<exists>hi. (\<forall>i\<le>n. (?fA (Vi i) (hi i))) \<and>
                          (\<forall>x\<in>K. (\<Sum>i\<le>n. hi i x) = 1) \<and> (\<forall>x\<in>topspace X. 0 \<le> (\<Sum>i\<le>n. hi i x)) \<and>
                          (\<forall>x\<in>topspace X. (\<Sum>i\<le>n. hi i x) \<le> 1)"
    if K:"compactin X K" "\<And>i::nat. i \<le> n \<Longrightarrow> openin X (Vi i)" "K \<subseteq> (\<Union>i\<le>n. Vi i)" for K Vi n
  proof -
    {
      fix x
      assume x:"x \<in> K"
      have "\<exists>i\<le>n. x \<in> Vi i \<and> (\<exists>U V. openin X U \<and> (compactin X V) \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> Vi i)"
      proof -
        obtain i where i: "i \<le> n" "x \<in> Vi i"
          using K x by blast
        thus ?thesis
          using locally_compact_space_neighbourhood_base[of X] neighbourhood_base_of[of "\<lambda>U. compactin X U" X] lh K
          by(fastforce intro!: exI[where x=i])
      qed
    }

    hence "\<exists>ix Ux Vx. \<forall>x\<in>K. ix x \<le> n \<and> x \<in> Vi (ix x) \<and> openin X (Ux x) \<and>
                      compactin X (Vx x) \<and> x \<in> Ux x \<and> Ux x \<subseteq> Vx x \<and> Vx x \<subseteq> Vi (ix x)"
      by metis
    then obtain ix Ux Vx where xinK: "\<And>x. x \<in> K \<Longrightarrow> ix x \<le> n" "\<And>x. x \<in> K \<Longrightarrow> x \<in> Vi (ix x)"
            "\<And>x. x \<in> K \<Longrightarrow> openin X (Ux x)" "\<And>x. x \<in> K \<Longrightarrow> compactin X (Vx x)" "\<And>x. x \<in> K \<Longrightarrow> x \<in> Ux x"
            "\<And>x. x \<in> K \<Longrightarrow> Ux x \<subseteq> Vx x" "\<And>x. x \<in> K \<Longrightarrow> Vx x \<subseteq> Vi (ix x)"
      by blast
    hence "K \<subseteq> (\<Union>x\<in>K. Ux x)"
      by fastforce
    from compactinD[OF K(1) _ this] xinK(3) obtain K' where K': "finite K'" "K' \<subseteq> K" "K \<subseteq> (\<Union>x\<in>K'. Ux x)"
      by (metis (no_types, lifting) finite_subset_image imageE)

    define Hi where "Hi \<equiv> (\<lambda>i. \<Union> (Vx ` {x. x \<in> K' \<and> ix x = i}))"
    have Hi_Vi: "\<And>i. i \<le> n \<Longrightarrow> Hi i \<subseteq> Vi i"
      using xinK K' by(fastforce simp: Hi_def)
    have K_unHi: "K \<subseteq> (\<Union>i\<le>n. Hi i)"
    proof
      fix x
      assume "x \<in> K"
      then obtain y where y:"y \<in> K'" "x \<in> Ux y"
        using K' by auto
      then have "x \<in> Vx y" "ix y \<le> n"
        using K' xinK[of y] by auto
      with y show "x \<in> (\<Union>i\<le>n. Hi i)" 
        by(fastforce simp: Hi_def)
    qed
    have compactin_Hi: "\<And>i. i \<le> n \<Longrightarrow> compactin X (Hi i)"
      using xinK K' by(auto intro!: compactin_Union simp: Hi_def)
    {
      fix i
      assume "i \<in> {..n}"
      then have i: "i \<le> n" by auto
      have "closedin X (topspace X - Vi i)" "disjnt (topspace X - Vi i) (Hi i)"
        using Hi_Vi[OF i] K(2)[OF i] by (auto simp: disjnt_def)
      from Urysohn_locally_compact_Hausdorff_closed_compact_support[of _ 0 1,OF lh(1) disjI1[OF lh(2)] _ this(1) compactin_Hi[OF i] this(2)]
      have "\<exists>hi. continuous_map X (top_of_set {0..1::real}) hi \<and> hi ` (topspace X - Vi i) \<subseteq> {0} \<and>
                 hi ` Hi i \<subseteq> {1} \<and> disjnt (X closure_of {x\<in>topspace X. hi x \<noteq> 0}) (topspace X - Vi i) \<and>
                 ?csupp hi"
        unfolding has_compact_support_on_iff  by fastforce
      hence "\<exists>hi. ?iscont hi \<and> hi ` topspace X \<subseteq> {0..1} \<and> hi ` (topspace X - Vi i) \<subseteq> {0} \<and>
                  hi ` Hi i \<subseteq> {1} \<and> disjnt (X closure_of {x\<in>topspace X. hi x \<noteq> 0}) (topspace X - Vi i) \<and>
                  ?csupp hi"
        by (simp add: continuous_map_in_subtopology disjnt_def has_compact_support_on_def)
    }
    hence "\<exists>hi. \<forall>i\<in>{..n}. ?iscont (hi i) \<and> hi i ` topspace X \<subseteq> {0..1} \<and>
                hi i ` (topspace X - Vi i) \<subseteq> {0} \<and> hi i ` Hi i \<subseteq> {1} \<and>
                disjnt (X closure_of {x\<in>topspace X. hi i x \<noteq> 0}) (topspace X - Vi i) \<and>  ?csupp (hi i)"
      by(intro bchoice) auto
    hence "\<exists>hi. \<forall>i\<le>n. ?iscont (hi i) \<and> hi i ` topspace X \<subseteq> {0..1} \<and> hi i ` (topspace X - Vi i) \<subseteq> {0} \<and>
              hi i ` Hi i \<subseteq> {1} \<and> disjnt (X closure_of {x\<in>topspace X. hi i x \<noteq> 0}) (topspace X - Vi i) \<and> ?csupp (hi i)"
      by (meson atMost_iff)    
    then obtain gi where gi: "\<And>i. i \<le> n \<Longrightarrow> ?iscont (gi i)"
      "\<And>i. i \<le> n \<Longrightarrow> gi i ` topspace X \<subseteq> {0..1}" "\<And>i. i \<le> n \<Longrightarrow> gi i ` (topspace X - Vi i) \<subseteq> {0}"
      "\<And>i. i \<le> n \<Longrightarrow> gi i ` Hi i \<subseteq> {1}"
      "\<And>i. i \<le> n \<Longrightarrow> disjnt (X closure_of {x\<in>topspace X. gi i x \<noteq> 0}) (topspace X - Vi i)"
      "\<And>i. i \<le> n \<Longrightarrow> ?csupp (gi i)"
      by fast
    define hi where "hi \<equiv> (\<lambda>n. \<lambda>x\<in>topspace X. (\<Prod>i<n. (1 - gi i x)) * gi n x)"
    show ?thesis
    proof(safe intro!: exI[where x=hi])
      fix i
      assume i: "i \<le> n"
      then show "?iscont (hi i)"
        using gi(1) by(auto simp: hi_def intro!: continuous_map_real_mult continuous_map_prod continuous_map_diff)
      show "?csupp (hi i)"
      proof -
        have "{x \<in> topspace X. hi i x \<noteq> 0} = {x\<in>topspace X. gi i x \<noteq> 0} \<inter> (\<Inter>j<i. {x\<in>topspace X. gi j x \<noteq> 1})"
          using gi by(auto simp: hi_def)
        also have "... \<subseteq> {x\<in>topspace X. gi i x \<noteq> 0}"
          by blast
        finally show ?thesis
          using gi(6)[OF i] closure_of_mono closed_compactin
          by(fastforce simp: has_compact_support_on_iff)
      qed
    next
      fix i x
      assume i: "i \<le> n" and x: "x \<in> topspace X"
      {
        assume "x \<notin> Vi i"
        with i x gi(3)[of i] show "hi i x = 0"
          by(auto simp: hi_def)
      }
      show "hi i x \<in> {0..1}"
        using i x gi(2) by(auto simp: hi_def image_subset_iff intro!: mult_nonneg_nonneg mult_le_one prod_le_1 prod_nonneg)
    next
      fix x
      have 1:"(\<Sum>i\<le>n. hi i x) = 1 - (\<Prod>i\<le>n. (1 - gi i x))" if x:"x \<in> topspace X"
      proof -
        have "(\<Sum>i\<le>n. hi i x) = (\<Sum>j\<le>n. (\<Prod>i<j. (1 - gi i x)) * gi j x)"
          using x by (simp add: hi_def)
        also have "... = 1 - (\<Prod>i\<le>n. (1 - gi i x))"
        proof -
          have [simp]: "(\<Prod>i<m. 1 - gi i x) * (1 - gi m x) = (\<Prod>i\<le>m. 1 - gi i x)" for m
            by (metis lessThan_Suc_atMost prod.lessThan_Suc)
          show ?thesis
            by(induction n, simp_all) (simp add: right_diff_distrib)
        qed
        finally show ?thesis .
      qed
      {
        assume x:"x \<in> K"
        then obtain i where i: "i \<le> n" "x \<in> Hi i"
          using K_unHi by auto
        have "x \<in> topspace X"
          using K(1) x compactin_subset_topspace by auto
        hence "(\<Sum>i\<le>n. hi i x) = 1 - (\<Prod>i\<le>n. (1 - gi i x))"
          by(simp add: 1)
        also have "... = 1"
          using i gi(4)[OF i(1)] by(auto intro!: prod_zero bexI[where x=i])
        finally show "(\<Sum>i\<le>n. hi i x) = 1" .
      }
      assume x: "x \<in> topspace X"
      then show "0 \<le> (\<Sum>i\<le>n. hi i x)" "(\<Sum>i\<le>n. hi i x) \<le> 1"
        using gi(2) by(auto simp: 1 image_subset_iff intro!: prod_nonneg prod_le_1)
    next
      fix i x
      assume h:"i \<le> n" "x \<in> X closure_of {x \<in> topspace X. hi i x \<noteq> 0}"
      have "{x \<in> topspace X. hi i x \<noteq> 0} = {x\<in>topspace X. gi i x \<noteq> 0} \<inter> (\<Inter>j<i. {x\<in>topspace X. gi j x \<noteq> 1})"
        using gi by(auto simp: hi_def)
      also have "... \<subseteq> {x\<in>topspace X. gi i x \<noteq> 0}"
        by blast
      finally have "X closure_of {x \<in> topspace X. hi i x \<noteq> 0} \<subseteq> X closure_of {x\<in>topspace X. gi i x \<noteq> 0}"
        by(rule closure_of_mono)
      thus "x \<in> Vi i"
        using gi(5)[OF h(1)] h(2) closure_of_subset_topspace by(fastforce simp: disjnt_def)
    qed
  qed
  note [simp, intro!] = continuous_map_add continuous_map_diff continuous_map_real_mult
  define \<mu>' where "\<mu>' \<equiv> (\<lambda>A. \<Squnion> (ennreal ` \<phi> ` {(\<lambda>x\<in>topspace X. f x) |f. ?fA A f}))"
  define \<mu> where "\<mu> \<equiv> (\<lambda>A. \<Sqinter> (\<mu>' ` {V. A \<subseteq> V \<and> openin X V}))"

  define Mf where "Mf \<equiv> {E. E \<subseteq> topspace X \<and> \<mu> E < \<top> \<and> \<mu> E = (\<Squnion> (\<mu> ` {K. K \<subseteq> E \<and> compactin X K}))}"
  define M where "M \<equiv> {E. E \<subseteq> topspace X \<and> (\<forall>K. compactin X K \<longrightarrow> E \<inter> K \<in> Mf)}"

  have \<mu>'_mono: "\<And>A B. A \<subseteq> B \<Longrightarrow> \<mu>' A \<le> \<mu>' B"
    unfolding \<mu>'_def by(fastforce intro!: SUP_subset_mono imageI)
  have \<mu>_open: "\<mu> A = \<mu>' A" if "openin X A" for A
    unfolding \<mu>_def by (metis (mono_tags, lifting) INF_eqI \<mu>'_mono dual_order.refl mem_Collect_eq that)
  have \<mu>_mono: "\<And>A B. A \<subseteq> B \<Longrightarrow> \<mu> A \<le> \<mu> B"
    unfolding \<mu>_def by(auto intro!: INF_superset_mono)
  have \<mu>_fin_subset: "\<mu> A < \<infinity> \<Longrightarrow> A \<subseteq> topspace X" for A
    by (metis (mono_tags, lifting) INF_less_iff \<mu>_def mem_Collect_eq openin_subset order.trans)

  have \<mu>'_empty: "\<mu>' {} = 0" and \<mu>_empty: "\<mu> {} = 0"
  proof -
    have 1:"{(\<lambda>x\<in>topspace X. f x) |f. ?fA {} f} = {\<lambda>x\<in>topspace X. 0}"
      by(fastforce intro!: exI[where x="\<lambda>x\<in>topspace X. 0"])
    thus "\<mu>' {} = 0" "\<mu> {} = 0"
      by(auto simp: \<mu>'_def \<phi>_0 \<mu>_open)
  qed
  have empty_in_Mf: "{} \<in> Mf"
    by(auto simp: Mf_def \<mu>_empty)

  have step1: "\<mu> (\<Union> (range Ei)) \<le> (\<Sum>i. \<mu> (Ei i))" for Ei
  proof -
    have 1: "\<mu>' (V \<union> U) \<le> \<mu>' V + \<mu>' U" if VU: "openin X V" "openin X U" for V U
    proof -
      have "\<mu>' (V \<union> U) = \<Squnion> (ennreal ` \<phi> ` {(\<lambda>x\<in>topspace X. f x) |f. ?fA (V \<union> U) f})"
        by(simp add: \<mu>'_def)
      also have "... \<le> \<mu>' V + \<mu>' U"
        unfolding Sup_le_iff
      proof safe
        fix g
        assume g: "?iscont g" "?csupp g" "g \<in> topspace X \<rightarrow> {0..1}" "g \<in> topspace X - (V \<union> U) \<rightarrow> {0}"
                  "X closure_of {x \<in> topspace X. g x \<noteq> 0} \<subseteq> V \<union> U"
        have "\<exists>hi. (\<forall>i\<le>Suc 0. ?iscont (hi i) \<and> ?csupp (hi i) \<and>
                    X closure_of {x \<in> topspace X. hi i x \<noteq> 0} \<subseteq> (case i of 0 \<Rightarrow> V | Suc _ \<Rightarrow> U) \<and>
                    hi i \<in> topspace X \<rightarrow> {0..1} \<and>
                    hi i \<in> topspace X - (case i of 0 \<Rightarrow> V | Suc _ \<Rightarrow> U) \<rightarrow> {0}) \<and>
                    (\<forall>x\<in>X closure_of {x\<in>topspace X. g x \<noteq> 0}. (\<Sum>i\<le>Suc 0. hi i x) = 1) \<and>
                    (\<forall>x\<in>topspace X. 0 \<le> (\<Sum>i\<le>Suc 0. hi i x)) \<and> (\<forall>x\<in>topspace X. (\<Sum>i\<le>Suc 0. hi i x) \<le> 1)"
        proof(safe intro!: fApartition[of _ "Suc 0" "\<lambda>i. case i of 0 \<Rightarrow> V | _ \<Rightarrow> U"])
          have 1:"(\<Union>i\<le>Suc 0. case i of 0 \<Rightarrow> V | Suc _ \<Rightarrow> U) = U \<union> V"
            by(fastforce simp: le_Suc_eq)
          show "\<And>x. x \<in> X closure_of {x \<in> topspace X. g x \<noteq> 0} \<Longrightarrow> x \<in> (\<Union>i\<le>Suc 0. case i of 0 \<Rightarrow> V | Suc _ \<Rightarrow> U)"
            unfolding 1 using g by blast
        next
          show "compactin X (X closure_of {x \<in> topspace X. g x \<noteq> 0})"
            using g by(simp add: has_compact_support_on_iff)
        qed(use g VU le_Suc_eq in auto)
        then obtain hi where
          "(\<forall>i\<le>Suc 0. ?iscont (hi i) \<and> ?csupp (hi i) \<and>
            X closure_of {x \<in> topspace X. hi i x \<noteq> 0} \<subseteq> (case i of 0 \<Rightarrow> V | Suc _ \<Rightarrow> U) \<and>
            hi i \<in> topspace X \<rightarrow> {0..1} \<and> hi i \<in> topspace X - (case i of 0 \<Rightarrow> V | Suc _ \<Rightarrow> U) \<rightarrow> {0}) \<and>
            (\<forall>x\<in>X closure_of {x\<in>topspace X. g x \<noteq> 0}. (\<Sum>i\<le>Suc 0. hi i x) = 1) \<and>
            (\<forall>x\<in>topspace X. 0 \<le> (\<Sum>i\<le>Suc 0. hi i x)) \<and> (\<forall>x\<in>topspace X. (\<Sum>i\<le>Suc 0. hi i x) \<le> 1)"
          by blast
        hence h0: "?iscont (hi 0)" "?csupp (hi 0)" "X closure_of {x \<in> topspace X. hi 0 x \<noteq> 0} \<subseteq> V"
          "hi 0 \<in> topspace X \<rightarrow> {0..1}" "hi 0 \<in> topspace X - V \<rightarrow> {0}"
          and h1: "?iscont (hi (Suc 0))" "?csupp (hi (Suc 0))" "X closure_of {x \<in> topspace X. hi (Suc 0) x \<noteq> 0} \<subseteq> U"
          "hi (Suc 0) \<in> topspace X \<rightarrow> {0..1}" "hi (Suc 0) \<in> topspace X - U \<rightarrow> {0}"
          and h01_sum: "\<And>x. x \<in> X closure_of {x\<in>topspace X. g x \<noteq> 0} \<Longrightarrow> (\<Sum>i\<le>Suc 0. hi i x) = 1"
          unfolding le_Suc_eq le_0_eq by auto
        have "ennreal (\<phi> (\<lambda>x\<in>topspace X. g x)) = ennreal (\<phi> (\<lambda>x\<in>topspace X. g x * (hi 0 x + hi (Suc 0) x)))"
        proof -
          have [simp]: "(\<lambda>x\<in>topspace X. g x) = (\<lambda>x\<in>topspace X. g x * (hi 0 x + hi (Suc 0) x))"
          proof
            fix x
            consider "g x \<noteq> 0" "x \<in> topspace X" | "g x = 0" | "x \<notin> topspace X"
              by fastforce
            then show "restrict g (topspace X) x = (\<lambda>x\<in>topspace X. g x * (hi 0 x + hi (Suc 0) x)) x"
            proof cases
              case 1
              then have "x \<in> X closure_of {x\<in>topspace X. g x \<noteq> 0}"
                using in_closure_of by fastforce
              from h01_sum[OF this] show ?thesis
                by simp
            qed simp_all
          qed
          show ?thesis
            by simp
        qed
        also have "... = ennreal (\<phi> (\<lambda>x\<in>topspace X. g x * hi 0 x + g x * hi (Suc 0) x))"
          by (simp add: ring_class.ring_distribs(1))
        also have "... = ennreal (\<phi> (\<lambda>x\<in>topspace X. g x * hi 0 x) + \<phi> (\<lambda>x\<in>topspace X. g x * hi (Suc 0) x))"
          by(intro ennreal_cong linear(2) has_compact_support_on_mult_left continuous_map_real_mult g h0 h1)
        also have "... = ennreal (\<phi> (\<lambda>x\<in>topspace X. g x * hi 0 x)) + ennreal (\<phi> (\<lambda>x\<in>topspace X. g x * hi (Suc 0) x))"
          using g(3) h0(4) h1(4)
          by(auto intro!: ennreal_plus pos g h0 h1 has_compact_support_on_mult_left mult_nonneg_nonneg)
        also have "... \<le> \<mu>' V + \<mu>' U"
          unfolding \<mu>'_def
        proof(safe intro!: add_mono Sup_upper imageI)
          show "\<exists>f. (\<lambda>x\<in>topspace X. g x * hi 0 x) = restrict f (topspace X) \<and> ?iscont f \<and> ?csupp f \<and>
              X closure_of {x \<in> topspace X. f x \<noteq> 0} \<subseteq> V \<and> f \<in> topspace X \<rightarrow> {0..1} \<and> f \<in> topspace X - V \<rightarrow> {0}"
            using Pi_mem[OF g(3)] Pi_mem[OF h0(4)] in_mono[OF closure_of_mono[OF inf_sup_ord(2)[of "{x \<in> topspace X. g x \<noteq> 0}"]]] h0(3,5)
            by(auto intro!: exI[where x="\<lambda>x\<in>topspace X.  g x * hi 0 x"] g(1,2) h0(1,2) has_compact_support_on_mult_left mult_le_one mult_nonneg_nonneg)
          show "\<exists>f. (\<lambda>x\<in>topspace X. g x * hi (Suc 0) x) = restrict f (topspace X) \<and> ?iscont f \<and>
             ?csupp f \<and> X closure_of {x \<in> topspace X. f x \<noteq> 0} \<subseteq> U \<and> f \<in> topspace X \<rightarrow> {0..1} \<and> f \<in> topspace X - U \<rightarrow> {0}"
            using Pi_mem[OF g(3)] Pi_mem[OF h1(4)] in_mono[OF closure_of_mono[OF inf_sup_ord(2)[of "{x \<in> topspace X. g x \<noteq> 0}"]]] h1(3,5)
            by(auto intro!: exI[where x="\<lambda>x\<in>topspace X.  g x * hi 1 x"] g(1,2) h1(1,2) has_compact_support_on_mult_left mult_le_one mult_nonneg_nonneg)
        qed
        finally show "ennreal (\<phi> (restrict g (topspace X))) \<le> \<mu>' V + \<mu>' U" .
      qed
      finally show "\<mu>' (V \<union> U) \<le> \<mu>' V + \<mu>' U" .
    qed

    consider "\<exists>i. \<mu> (Ei i) = \<infinity>" | "\<And>i. \<mu> (Ei i) < \<infinity>"
      using top.not_eq_extremum by auto
    then show ?thesis
    proof cases
      case 1
      then show ?thesis
        by (metis \<mu>_mono ennreal_suminf_lessD infinity_ennreal_def linorder_not_le subset_UNIV top.not_eq_extremum)
    next
      case fin:2
      show ?thesis
      proof(rule ennreal_le_epsilon)
        fix e :: real
        assume e: "0 < e"
        have "\<exists>Vi. Ei i \<subseteq> Vi \<and> openin X Vi \<and> \<mu>' Vi \<le> \<mu> (Ei i) + ennreal ((1 / 2)^Suc i) * ennreal e" for i
        proof -
          have 1:"\<mu> (Ei i) < \<mu> (Ei i) + ennreal ((1 / 2) ^ Suc i) * ennreal e"
            using e fin less_le by fastforce
          have "0 < ennreal ((1 / 2)^Suc i) * ennreal e"
            using e by (simp add: ennreal_zero_less_mult_iff)
          have "(\<Sqinter> (\<mu>' ` {V. Ei i \<subseteq> V \<and> openin X V})) \<le> \<mu> (Ei i)"
            by(auto simp: \<mu>_def)
          from Inf_le_iff[THEN iffD1,OF this,rule_format,OF 1]
          show ?thesis
            by auto
        qed
        then obtain Vi where Vi: "\<And>i. Vi i \<supseteq> Ei i" "\<And>i. openin X (Vi i)"
          "\<And>i. \<mu> (Vi i) \<le> \<mu> (Ei i) + ennreal ((1 / 2)^Suc i) * ennreal e"
          by (metis \<mu>_open)
        hence "\<mu> (\<Union> (range Ei)) \<le> \<mu> (\<Union> (range Vi))"
          by(auto intro!: \<mu>_mono)
        also have "... = \<mu>' (\<Union> (range Vi))"
          using Vi by(auto intro!: \<mu>_open)
        also have "... = (\<Squnion> (ennreal ` \<phi> ` {(\<lambda>x\<in>topspace X. f x) |f. ?fA (\<Union> (range Vi)) f}))"
          by(simp add: \<mu>'_def)
        also have "... \<le> (\<Sum>i. \<mu> (Ei i)) + ennreal e"
          unfolding Sup_le_iff
        proof safe
          fix f
          assume f: "?iscont f" "?csupp f" "X closure_of {x \<in> topspace X. f x \<noteq> 0} \<subseteq> \<Union> (range Vi)" "f \<in> topspace X \<rightarrow> {0..1}" "f \<in> topspace X - \<Union> (range Vi) \<rightarrow> {0}"
          have "\<exists>n. f \<in> topspace X - (\<Union>i\<le>n. Vi i) \<rightarrow> {0} \<and> X closure_of {x \<in> topspace X. f x \<noteq> 0} \<subseteq> (\<Union>i\<le>n. Vi i)"
          proof -
            obtain K where K:"finite K" "K \<subseteq> range Vi" "X closure_of {x \<in> topspace X. f x \<noteq> 0} \<subseteq> \<Union> K"
              using compactinD[OF f(2)[simplified has_compact_support_on_iff]] Vi(2) f(3)
              by (metis (mono_tags, lifting) imageE)
            hence "\<exists>n. K \<subseteq> Vi ` {..n}"
              by (metis (no_types, lifting) finite_nat_iff_bounded_le finite_subset_image image_mono)
            then obtain n where n: "X closure_of {x \<in> topspace X. f x \<noteq> 0} \<subseteq> (\<Union>i\<le>n. Vi i)"
              using K(3) by fastforce
            show ?thesis
              using in_closure_of n subsetD by(fastforce intro!: exI[where x=n])
          qed
          then obtain n where n:"f \<in> topspace X - (\<Union>i\<le>n. Vi i) \<rightarrow> {0}" "X closure_of {x \<in> topspace X. f x \<noteq> 0} \<subseteq> (\<Union>i\<le>n. Vi i)"
            by blast
          have "ennreal (\<phi> (restrict f (topspace X))) \<le> \<mu>' (\<Union>i\<le>n. Vi i)"
            using f(4) f n by(auto intro!: imageI exI[where x=f] Sup_upper simp: \<mu>'_def)
          also have "... \<le> (\<Sum>i\<le>n. \<mu>' (Vi i))"
          proof(induction n)
            case ih:(Suc n')
            have [simp]:"\<mu>' (\<Union> (Vi ` {..Suc n'})) = \<mu>' (\<Union> (Vi ` {..n'}) \<union> Vi (Suc n'))"
              by(rule arg_cong[of _ _ \<mu>']) (fastforce simp: le_Suc_eq)
            also have "... \<le> \<mu>' (\<Union> (Vi ` {..n'})) + \<mu>' (Vi (Suc n'))"
              using Vi(2) by(auto intro!: 1)
            also have "... \<le> (\<Sum>i\<le>Suc n'. \<mu>' (Vi i))"
              using ih by fastforce
            finally show ?case .
          qed simp
          also have "... = (\<Sum>i\<le>n. \<mu> (Vi i))"
            using Vi(2) by(simp add: \<mu>_open)
          also have "... \<le> (\<Sum>i. \<mu> (Vi i))"
            by (auto intro!: incseq_SucI incseq_le[OF _ summable_LIMSEQ'])
          also have "... \<le> (\<Sum>i. \<mu> (Ei i) + ennreal ((1 / 2)^Suc i) * ennreal e)"
            by(intro suminf_le Vi(3)) auto
          also have "... = (\<Sum>i. \<mu> (Ei i)) + (\<Sum>i. ennreal ((1 / 2)^Suc i) * ennreal e)"
            by(rule suminf_add[symmetric]) auto
          also have "... = (\<Sum>i. \<mu> (Ei i)) + (\<Sum>i. ennreal ((1 / 2)^Suc i)) * ennreal e"
            by simp
          also have "... = (\<Sum>i. \<mu> (Ei i)) + ennreal 1 * ennreal e"
          proof -
            have "(\<Sum>i. ennreal ((1 / 2)^Suc i)) =  ennreal 1"
              by(rule suminf_ennreal_eq) (use power_half_series in auto)
            thus ?thesis
              by presburger
          qed
          also have "... = (\<Sum>i. \<mu> (Ei i)) + ennreal e"
            by simp
          finally show "ennreal (\<phi> (restrict f (topspace X))) \<le> (\<Sum>i. \<mu> (Ei i)) + ennreal e" .
        qed
        finally show "\<mu> (\<Union> (range Ei)) \<le> (\<Sum>i. \<mu> (Ei i)) + ennreal e" .
      qed
    qed
  qed
  have step1': "\<mu> (E1 \<union> E2) \<le> \<mu> E1 + \<mu> E2" for E1 E2
  proof -
    define En where "En \<equiv> (\<lambda>n::nat. if n = 0 then E1 else if n = 1 then E2 else {})"
    have 1: "(\<Union> (range En)) = (E1 \<union> E2)"
      by(auto simp: En_def)
    have 2: "(\<Sum>i. \<mu> (En i)) = \<mu> E1 + \<mu> E2"
      using suminf_offset[of "\<lambda>i. \<mu> (En i)",of "Suc (Suc 0)"]
      by(auto simp: En_def \<mu>_empty)
    show ?thesis
      using step1[of En] by(simp add: 1 2)
  qed
  have step2: "K \<in> Mf" "\<mu> K = (\<Sqinter> (ennreal ` \<phi> ` {(\<lambda>x\<in>topspace X. f x) | f. ?fK K f}))" if K: "compactin X K" for K
  proof -
    have le1: "\<mu> K \<le> ennreal (\<phi> (\<lambda>x\<in>topspace X. f x))" if f:"?iscont f" "?csupp f" "f \<in> topspace X \<rightarrow> {0..1}" "f \<in> K \<rightarrow> {1}" for f
    proof -
      have f: "continuous_map X (top_of_set {0..1::real}) f" "f ` K \<subseteq> {1}" "?csupp f"
        using f by (auto simp: continuous_map_in_subtopology)
      hence f_cont: "?iscont f" "f \<in> topspace X \<rightarrow> {0..1}"
        by (auto simp add: continuous_map_in_subtopology)        
      have 1:"\<mu> K \<le> ennreal (1 / ((real n + 1) / (real n + 2)) * \<phi> (\<lambda>x\<in>topspace X. f x))" for n
      proof -
        let ?a = "(real n + 1) / (real n + 2)"
        define V where "V \<equiv> {x\<in>topspace X. ?a < f x}"
        have openinV:"openin X V"
          using f(1)by (auto simp: V_def continuous_map_upper_lower_semicontinuous_lt_gen)
        have KV: "K \<subseteq> V"
          using f(2) compactin_subset_topspace[OF K] by(auto simp: V_def)
        hence "\<mu> K \<le> \<mu> V"
          by(rule \<mu>_mono)
        also have "... = \<mu>' V"
          by(simp add: \<mu>_open openinV)
        also have "... = (\<Squnion> (ennreal ` \<phi> ` {(\<lambda>x\<in>topspace X. f x) |f. ?fA V f}))"
          by(simp add: \<mu>'_def)
        also have "... \<le> (1 / ?a) * \<phi> (\<lambda>x\<in>topspace X. f x)"
          unfolding Sup_le_iff
        proof (safe intro!: ennreal_leI)
          fix g
          assume g: "?iscont g" "?csupp g" "X closure_of {x\<in>topspace X. g x \<noteq> 0} \<subseteq> V"
            "g \<in> topspace X \<rightarrow> {0..1}" "g \<in> topspace X - V \<rightarrow> {0}"
          show "\<phi> (restrict g (topspace X)) \<le> 1 / ?a * \<phi> (restrict f (topspace X))" (is "?l \<le> ?r")
          proof -
            have "?l \<le> \<phi> (\<lambda>x\<in>topspace X. 1 / ?a * f x)"
            proof(rule \<phi>mono)
              fix x
              assume x: "x \<in> topspace X"
              consider "g x \<noteq> 0" | "g x = 0"
                by fastforce
              then show "g x \<le> 1 / ((real n + 1) / (real n + 2)) * f x"
              proof cases
                case 1
                then have "x \<in> V"
                  using g(5) x by auto
                hence "?a < f x"
                  by(auto simp: V_def x)
                hence "1 < 1 / ?a * f x"
                  by (simp add: divide_less_eq mult.commute)
                thus ?thesis
                  by(intro order.strict_implies_order[OF order.strict_trans1[of "g x" 1 "1 / ?a * f x"]]) (use g(4) x in auto)
              qed(use Pi_mem[OF f_cont(2)] x in auto)
            qed(intro g f_cont f has_compact_support_on_mult_left continuous_map_real_mult continuous_map_canonical_const)+
            also have "... = ?r"
              by(intro linear f f_cont)
            finally show ?thesis .
          qed
        qed
        finally show ?thesis .
      qed
      have 2:"(\<lambda>n. ennreal (1 / ((real n + 1) / (real n + 2)) * \<phi> (restrict f (topspace X))))
               \<longlonglongrightarrow> ennreal (\<phi> (restrict f (topspace X)))"
      proof(intro tendsto_ennrealI tendsto_mult_right[where l="1::real",simplified])
        have 1: "(\<lambda>n. 1 / ((real n + 1) / (real n + 2))) = (\<lambda>n. real (Suc (Suc n)) / real (Suc n))"
          by (simp add: add.commute)
        show "(\<lambda>n. 1 / ((real n + 1) / (real n + 2))) \<longlonglongrightarrow> 1"
          unfolding 1 by(rule LIMSEQ_Suc[OF LIMSEQ_Suc_n_over_n])
      qed
      show "\<mu> K \<le> ennreal (\<phi> (\<lambda>x\<in>topspace X. f x))"
        by(rule Lim_bounded2[where N=0,OF 2]) (use 1 in auto)
    qed
    have muK_fin:"\<mu> K < \<top>"
    proof -
      obtain f where f: "continuous_map X (top_of_set {0..1::real}) f" "f ` K \<subseteq> {1}" "?csupp f"
        using Urysohn_locally_compact_Hausdorff_closed_compact_support[OF lh(1) disjI1[OF lh(2)]
            zero_le_one closedin_empty K] by(auto simp: has_compact_support_on_iff)
      hence "?iscont f" "?csupp f" "f \<in> topspace X \<rightarrow> {0..1}" "f \<in> K \<rightarrow> {1}"
        by(auto simp: continuous_map_in_subtopology)
      from le1[OF this]
      show ?thesis
        using dual_order.strict_trans2 ennreal_less_top by blast
    qed
    moreover have " \<mu> K = (\<Squnion> (\<mu> ` {K'. K' \<subseteq> K \<and> compactin X K'}))"
      by (metis (no_types, lifting) SUP_eqI \<mu>_mono mem_Collect_eq subset_refl K)
    ultimately show "K \<in> Mf"
      using compactin_subset_topspace[OF K] by(simp add: Mf_def)

    show "\<mu> K = (\<Sqinter> (ennreal ` \<phi> ` {(\<lambda>x\<in>topspace X. f x) |f. ?fK K f}))"
    proof(safe intro!: antisym le_Inf_iff[THEN iffD2] Inf_le_iff[THEN iffD2])
      fix g
      assume "?iscont g" "?csupp g" "g \<in> topspace X \<rightarrow> {0..1}" "g \<in> K \<rightarrow> {1}"
      from le1[OF this(1-4)]
      show "\<mu> K \<le> ennreal (\<phi> (\<lambda>x\<in>topspace X. g x))"
        by force
    next
      fix y
      assume "\<mu> K < y"
      then obtain V where V: "openin X V" "K \<subseteq> V" "\<mu>' V < y"
        by (metis (mono_tags, lifting) INF_less_iff \<mu>_def mem_Collect_eq)
      hence "closedin X (topspace X - V)" "disjnt (topspace X - V) K"
        by (auto simp: disjnt_def)
      from Urysohn_locally_compact_Hausdorff_closed_compact_support[OF lh(1) disjI1[OF lh(2)] zero_le_one this(1) K this(2)]
      obtain f where f':"continuous_map X (subtopology euclidean {0..1}) f" "f ` (topspace X - V) \<subseteq> {0::real}"
        "f ` K \<subseteq> {1}" "disjnt (X closure_of {x\<in>topspace X. f x \<noteq> 0}) (topspace X - V)"
        "compactin X (X closure_of {x\<in>topspace X. f x \<noteq> 0})"
        by blast
      hence f:"?iscont f" "?csupp f" "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<ge> 0"
        "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<le> 1" "\<And>x. x \<in> K \<Longrightarrow> f x = 1"
        by(auto simp: has_compact_support_on_iff continuous_map_in_subtopology)
      have "ennreal (\<phi> (restrict f (topspace X))) < y"
      proof(rule order.strict_trans1)
        show "ennreal (\<phi> (restrict f (topspace X))) \<le> \<mu>' V"
          unfolding \<mu>'_def using f' f in_closure_of
          by (fastforce intro!: Sup_upper imageI exI[where x="\<lambda>x\<in>topspace X. f x"] simp: disjnt_iff)
      qed fact
      thus "\<exists>a\<in>ennreal ` \<phi> ` {(\<lambda>x\<in>topspace X. f x)|f. ?fK K f}. a < y"
        using f compactin_subset_topspace[OF K] by(auto intro!: exI[where x="\<lambda>x\<in>topspace X. f x"])
    qed
  qed
  have \<mu>_K: "\<mu> K \<le> ennreal (\<phi> (\<lambda>x\<in>topspace X. f x))" if K: "compactin X K" and f:"?fK K f" for K f
    using le_Inf_iff[THEN iffD1,OF eq_refl[OF step2(2)[OF K]]] f by blast
  have step3: "\<mu> A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. \<mu> K)" "\<mu> A < \<infinity> \<Longrightarrow> A \<in> Mf" if A:"openin X A" for A
  proof -
    show "\<mu> A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. \<mu> K)"
    proof(safe intro!: antisym le_Sup_iff[THEN iffD2] Sup_le_iff[THEN iffD2])
      fix y
      assume y: "y < \<mu> A"
      from less_SUP_iff[THEN iffD1,OF less_INF_D[OF y[simplified \<mu>_def],simplified \<mu>'_def],of A]
      obtain f where f: "?iscont f" "?csupp f" "X closure_of {x \<in> topspace X. f x \<noteq> 0} \<subseteq> A"
        "f \<in> topspace X \<rightarrow> {0..1}" "f \<in> topspace X - A \<rightarrow> {0}" "y < ennreal (\<phi> (\<lambda>x\<in>topspace X. f x))"
        using A by blast
      show "\<exists>a\<in>\<mu> ` {K. compactin X K \<and> K \<subseteq> A}. y < a"
      proof(rule bexI[where x="\<mu> (X closure_of {x \<in> topspace X. f x \<noteq> 0})"])
        show "y < \<mu> (X closure_of {a \<in> topspace X. f a \<noteq> 0})"
        proof(rule order.strict_trans2)
          show "ennreal (\<phi> (\<lambda>x\<in>topspace X. f x)) \<le> \<mu> (X closure_of {a \<in> topspace X. f a \<noteq> 0})"
            using f in_closure_of in_mono
            by(fastforce intro!: Sup_upper imageI exI[where x=f] simp: \<mu>_def le_Inf_iff \<mu>'_def)
        qed fact
      qed(use f(2,3) has_compact_support_on_iff in auto)
    qed(auto intro!: \<mu>_mono)
    thus "\<mu> A < \<infinity> \<Longrightarrow> A \<in> Mf"
      unfolding Mf_def using openin_subset[OF A] by simp metis
  qed
  have step4: "\<mu> (\<Union>n. En n) = (\<Sum>n. \<mu> (En n))" "\<mu> (\<Union>n. En n) < \<infinity> \<Longrightarrow> (\<Union>n. En n) \<in> Mf"
    if En: "\<And>n. En n \<in> Mf" "disjoint_family En" for En
  proof -
    have compacts: "\<mu> (K1 \<union> K2) = \<mu> K1 + \<mu> K2" if K: "compactin X K1" "compactin X K2" "disjnt K1 K2" for K1 K2
    proof(rule antisym)
      show "\<mu> (K1 \<union> K2) \<le> \<mu> K1 + \<mu> K2"
        by(rule step1')
    next
      show "\<mu> K1 + \<mu> K2 \<le> \<mu> (K1 \<union> K2)"
      proof(rule ennreal_le_epsilon)
        fix e :: real
        assume e: "0 < e" "\<mu> (K1 \<union> K2) < \<top>"
        from Urysohn_locally_compact_Hausdorff_closed_compact_support[OF lh(1) disjI1[OF lh(2)]
            zero_le_one compactin_imp_closedin[OF lh(2) K(1)] K(2,3)]
        obtain f where f: "continuous_map X (top_of_set {0..1::real}) f" "f ` K1 \<subseteq> {0}" "f ` K2 \<subseteq> {1}"
          "disjnt (X closure_of {x \<in> topspace X. f x \<noteq> 0}) K1" "compactin X (X closure_of {x \<in> topspace X. f x \<noteq> 0})"
          by blast
        hence f': "?iscont f" "?csupp f" "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<ge> 0" "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<le> 1"
          by(auto simp: has_compact_support_on_iff continuous_map_in_subtopology)
        from Inf_le_iff[THEN iffD1,OF eq_refl[OF step2(2)[symmetric,OF  compactin_Un[OF K(1,2)]]],rule_format,of "\<mu> (K1 \<union> K2) + ennreal e"]
        obtain g where g: "?iscont g" "?csupp g" "g \<in> topspace X \<rightarrow> {0..1}" "g \<in> K1 \<union> K2 \<rightarrow> {1}"
          "ennreal (\<phi> (\<lambda>x\<in>topspace X. g x)) < \<mu> (K1 \<union> K2) + ennreal e"
          using e by fastforce
        have "\<mu> K1 + \<mu> K2 \<le> ennreal (\<phi> (\<lambda>x\<in>topspace X. (1 - f x) * g x)) + ennreal (\<phi> (\<lambda>x\<in>topspace X. f x * g x))"
        proof(rule add_mono)
          show "\<mu> K1 \<le> ennreal (\<phi> (\<lambda>x\<in>topspace X. (1 - f x) * g x))"
            using f' Pi_mem[OF g(3)] g(1,2,4,5) f(2) compactin_subset_topspace[OF K(1)]
            by(auto intro!: \<mu>_K has_compact_support_on_mult_left mult_nonneg_nonneg mult_le_one K(1) mult_eq_1[THEN iffD2])
          show "\<mu> K2 \<le> ennreal (\<phi> (\<lambda>x\<in>topspace X. f x * g x))"
            using g f Pi_mem[OF g(3)] f' compactin_subset_topspace[OF K(2)]
            by(auto intro!: \<mu>_K[OF K(2)] has_compact_support_on_mult_left mult_nonneg_nonneg mult_le_one mult_eq_1[THEN iffD2])
        qed
        also have "... = ennreal (\<phi> (\<lambda>x\<in>topspace X. (1 - f x)*g x) + \<phi> (\<lambda>x\<in>topspace X. f x * g x))"
          using f' g by(auto intro!: ennreal_plus[symmetric] pos has_compact_support_on_mult_left mult_nonneg_nonneg)
        also have "... = ennreal (\<phi> (\<lambda>x\<in>topspace X. (1 - f x) * g x + f x * g x))"
          by(auto intro!: ennreal_cong linear[symmetric] has_compact_support_on_mult_left f' g)
        also have "... = ennreal (\<phi> (\<lambda>x\<in>topspace X. g x))"
          by (simp add: Groups.mult_ac(2) right_diff_distrib)
        also have "... < \<mu> (K1 \<union> K2) + ennreal e"
          by fact
        finally show "\<mu> K1 + \<mu> K2 \<le> \<mu> (K1 \<union> K2) + ennreal e"
          by order
      qed
    qed
    have Hn:"\<exists>Hn. \<forall>n. compactin X (Hn n) \<and> (Hn n) \<subseteq> En n \<and> \<mu> (En n) < \<mu> (Hn n) + ennreal ((1 / 2)^Suc n) * ennreal e'"
      if e': "e' > 0" for e'
    proof(safe intro!: choice)
      show "\<exists>Hn. compactin X Hn \<and> Hn \<subseteq> En n \<and> \<mu> (En n) < \<mu> Hn + ennreal ((1 / 2)^Suc n) * ennreal e'" for n
      proof(cases "\<mu> (En n) <  ennreal ((1 / 2)^Suc n) * ennreal e'")
        case True
        then show ?thesis
          using e' by(auto intro!: exI[where x="{}"] simp: \<mu>_empty ennreal_zero_less_mult_iff)
      next
        case False
        then have le: "\<mu> (En n) \<ge> ennreal ((1 / 2) ^ Suc n) * ennreal e'"
          by order
        hence pos:"0 < \<mu> (En n)"
          using e' zero_less_power by fastforce
        have fin: "\<mu> (En n) < \<top>"
          using En Mf_def by blast
        hence 1:"\<mu> (En n) - ennreal ((1 / 2)^Suc n) * ennreal e' < \<mu> (En n)"
          using pos by(auto intro!: ennreal_between simp: ennreal_zero_less_mult_iff e')
        have "\<mu> (En n) = \<Squnion> (\<mu> ` {K. K \<subseteq> (En n) \<and> compactin X K})"
          using En by(auto simp: Mf_def)
        from le_Sup_iff[THEN iffD1,OF eq_refl[OF this],rule_format,OF 1]
        obtain Hn where Hn: "Hn \<subseteq> En n" "compactin X Hn" "\<mu> (En n) - ennreal ((1 / 2)^Suc n) * ennreal e' < \<mu> Hn"
          by blast
        hence "\<mu> (En n) < \<mu> Hn + ennreal ((1 / 2)^Suc n) * ennreal e'"
          by (metis diff_diff_ennreal' diff_gt_0_iff_gt_ennreal fin le order_less_le)
        with Hn(1,2) show ?thesis
          by blast
      qed
    qed
    show 1:"\<mu> (\<Union>n. En n) = (\<Sum>n. \<mu> (En n))"
    proof(rule antisym)
      show "(\<Sum>n. \<mu> (En n)) \<le> \<mu> (\<Union> (range En))"
      proof(rule ennreal_le_epsilon)
        fix e :: real
        assume fin: "\<mu> (\<Union> (range En)) < \<top>" and e:"0 < e"
        from Hn[OF e] obtain Hn where Hn: "\<And>n. compactin X (Hn n)" "\<And>n. Hn n \<subseteq> En n"
          "\<And>n. \<mu> (En n) < \<mu> (Hn n) + ennreal ((1 / 2) ^ Suc n) * ennreal e"
          by blast
        have "(\<Sum>n\<le>N. \<mu> (En n)) \<le> \<mu> (\<Union> (range En)) + ennreal e" for N
        proof -
          have "(\<Sum>n\<le>N. \<mu> (En n)) \<le> (\<Sum>n\<le>N. \<mu> (Hn n) + ennreal ((1 / 2) ^ Suc n) * ennreal e)"
            by(rule sum_mono) (use Hn(3) order_less_le in auto)
          also have "... = (\<Sum>n\<le>N. \<mu> (Hn n)) + (\<Sum>n\<le>N. ennreal ((1 / 2) ^ Suc n) * ennreal e)"
            by(rule sum.distrib)
          also have "... = \<mu> (\<Union>n\<le>N. Hn n) + (\<Sum>n\<le>N. ennreal ((1 / 2) ^ Suc n) * ennreal e)"
          proof -
            have "(\<Sum>n\<le>N. \<mu> (Hn n)) = \<mu> (\<Union>n\<le>N. Hn n)"
            proof(induction N)
              case ih:(Suc N')
              show ?case (is "?l = ?r")
              proof -
                have "?l = \<mu> (\<Union> (Hn ` {..N'})) + \<mu> (Hn (Suc N'))"
                  by(simp add: ih)
                also have "... = \<mu> ((\<Union> (Hn ` {..N'})) \<union> Hn (Suc N'))"
                proof(rule compacts[symmetric])
                  show "disjnt (\<Union> (Hn ` {..N'})) (Hn (Suc N'))"
                    using En(2) Hn(2) unfolding disjoint_family_on_def disjnt_iff
                    by (metis Int_iff Suc_n_not_le_n UNIV_I UN_iff atMost_iff empty_iff in_mono)
                qed(auto intro!: compactin_Union Hn)
                also have "... = ?r"
                  by (simp add: Un_commute atMost_Suc)
                finally show ?thesis .
              qed
            qed simp
            thus ?thesis
              by simp
          qed
          also have "... \<le> \<mu> (\<Union> (range En)) + (\<Sum>n\<le>N. ennreal ((1 / 2) ^ Suc n) * ennreal e)"
            using Hn(2) by(auto intro!: \<mu>_mono)
          also have "... \<le> \<mu> (\<Union> (range En)) + ennreal e"
          proof -
            have "(\<Sum>n\<le>N. ennreal ((1 / 2) ^ Suc n) * ennreal e) = ennreal (\<Sum>n\<le>N. ((1 / 2) ^ Suc n)) * ennreal e"
              unfolding sum_distrib_right[symmetric] by simp
            also have "... = ennreal e * ennreal (\<Sum>n\<le>N. ((1 / 2) ^ Suc n))"
              using mult.commute by blast
            also have "... \<le> ennreal e * ennreal (\<Sum>n. ((1 / 2) ^ Suc n))"
              using e by(auto intro!: ennreal_mult_le_mult_iff[THEN iffD2] ennreal_leI sum_le_suminf)
            also have "... = ennreal e"
              using power_half_series sums_unique by fastforce
            finally show ?thesis
              by fastforce
          qed
          finally show ?thesis .
        qed
        thus "(\<Sum>n. \<mu> (En n)) \<le> \<mu> (\<Union> (range En)) + ennreal e"
          by(auto intro!: LIMSEQ_le_const2[OF summable_LIMSEQ'] exI[where x=0])
      qed
    qed fact
    show "\<Union> (range En) \<in> Mf" if "\<mu> (\<Union> (range En)) < \<infinity>"
    proof -
      have "\<mu> (\<Union> (range En)) = (\<Squnion> (\<mu> ` {K. K \<subseteq> (\<Union> (range En)) \<and> compactin X K}))"
      proof(rule antisym)
        show "\<mu> (\<Union> (range En)) \<le> \<Squnion> (\<mu> ` {K. K \<subseteq> \<Union> (range En) \<and> compactin X K})"
          unfolding le_Sup_iff
        proof safe
          fix y
          assume "y < \<mu> (\<Union> (range En))"
          from order_tendstoD(1)[OF summable_LIMSEQ' this[simplified 1]]
          obtain N where N: "y < (\<Sum>n\<le>N. \<mu> (En n))"
            by fastforce
          obtain e where e: "e > 0" "y < (\<Sum>n\<le>N. \<mu> (En n)) - ennreal e"
            by (metis N ennreal_le_epsilon ennreal_less_top less_diff_eq_ennreal linorder_not_le)
          from Hn[OF e(1)] obtain Hn where Hn: "\<And>n. compactin X (Hn n)" "\<And>n. Hn n \<subseteq> En n"
            "\<And>n. \<mu> (En n) < \<mu> (Hn n) + ennreal ((1 / 2) ^ Suc n) * ennreal e"
            by blast
          have "y < (\<Sum>n\<le>N. \<mu> (En n)) - ennreal e"
            by fact
          also have "... \<le> (\<Sum>n\<le>N. \<mu> (Hn n) + ennreal ((1 / 2) ^ Suc n) * ennreal e) - ennreal e"
            by(intro ennreal_minus_mono sum_mono) (use Hn(3) order_less_le in auto)
          also have "... = (\<Sum>n\<le>N. \<mu> (Hn n)) + (\<Sum>n\<le>N. ennreal ((1 / 2) ^ Suc n) * ennreal e) - ennreal e"
            by (simp add: sum.distrib)
          also have "... = \<mu> (\<Union>n\<le>N. Hn n) + (\<Sum>n\<le>N. ennreal ((1 / 2) ^ Suc n) * ennreal e) - ennreal e"
          proof -
            have "(\<Sum>n\<le>N. \<mu> (Hn n)) = \<mu> (\<Union>n\<le>N. Hn n)"
            proof(induction N)
              case ih:(Suc N')
              show ?case (is "?l = ?r")
              proof -
                have "?l = \<mu> (\<Union> (Hn ` {..N'})) + \<mu> (Hn (Suc N'))"
                  by(simp add: ih)
                also have "... = \<mu> ((\<Union> (Hn ` {..N'})) \<union> Hn (Suc N'))"
                proof(rule compacts[symmetric])
                  show "disjnt (\<Union> (Hn ` {..N'})) (Hn (Suc N'))"
                    using En(2) Hn(2) unfolding disjoint_family_on_def disjnt_iff
                    by (metis Int_iff Suc_n_not_le_n UNIV_I UN_iff atMost_iff empty_iff in_mono)
                qed(auto intro!: compactin_Union Hn)
                also have "... = ?r"
                  by (simp add: Un_commute atMost_Suc)
                finally show ?thesis .
              qed
            qed simp
            thus ?thesis
              by simp
          qed
          also have "... \<le> \<mu> (\<Union>n\<le>N. Hn n) + (\<Sum>n. ennreal ((1 / 2) ^ Suc n) * ennreal e) - ennreal e"
            by(intro ennreal_minus_mono add_mono sum_le_suminf) (use e in auto)
          also have "... = \<mu> (\<Union>n\<le>N. Hn n) + (\<Sum>n. ennreal ((1 / 2) ^ Suc n)) * ennreal e - ennreal e"
            using ennreal_suminf_multc by presburger
          also have "... = \<mu> (\<Union>n\<le>N. Hn n) + ennreal e - ennreal e"
          proof -
            have "(\<Sum>n. ennreal ((1 / 2) ^ Suc n)) = ennreal 1"
              by(rule suminf_ennreal_eq) (use power_half_series in auto)
            thus ?thesis
              by fastforce
          qed
          also have "... = \<mu> (\<Union>n\<le>N. Hn n)"
            by simp
          finally show "Bex (\<mu> ` {K. K \<subseteq> \<Union> (range En) \<and> compactin X K}) ((<) y)"
            using Hn by(auto intro!: exI[where x="\<Union>n\<le>N. Hn n"] compactin_Union)
        qed
      qed(auto intro!: Sup_le_iff[THEN iffD2] \<mu>_mono)
      moreover have "(\<Union> (range En)) \<subseteq> topspace X"
        using En by(auto simp: Mf_def)
      ultimately show ?thesis
        using that by(auto simp: Mf_def)
    qed
  qed
  have step4': "\<mu> (E1 \<union> E2) = \<mu> E1 + \<mu> E2" "\<mu>(E1 \<union> E2) < \<infinity> \<Longrightarrow> E1 \<union> E2 \<in> Mf"
    if E: "E1 \<in> Mf"  "E2 \<in> Mf" "disjnt E1 E2" for E1 E2
  proof -
    define En where "En \<equiv> (\<lambda>n::nat. if n = 0 then E1 else if n = 1 then E2 else {})"
    have 1: "(\<Union> (range En)) = (E1 \<union> E2)"
      by(auto simp: En_def)
    have 2: "(\<Sum>i. \<mu> (En i)) = \<mu> E1 + \<mu> E2"
      using suminf_offset[of "\<lambda>i. \<mu> (En i)",of "Suc (Suc 0)"]
      by(auto simp: En_def \<mu>_empty)
    have 3:"disjoint_family En"
      using E(3) by(auto simp: disjoint_family_on_def disjnt_def En_def)
    have 4: "\<And>n. En n \<in> Mf"
      using E(1,2) by(auto simp: En_def empty_in_Mf)
    show "\<mu> (E1 \<union> E2) = \<mu> E1 + \<mu> E2" "\<mu>(E1 \<union> E2) < \<infinity> \<Longrightarrow> E1 \<union> E2 \<in> Mf"
      using step4[of En] E(1) by(simp_all add: 1 2 3 4)
  qed

  have step5: "\<exists>V K. openin X V \<and> compactin X K \<and> K \<subseteq> E \<and> E \<subseteq> V \<and> \<mu> (V - K) < ennreal e"
    if E: "E \<in> Mf" and e: "e > 0" for E e
  proof-
    have 1:"\<mu> E < \<mu> E + ennreal (e / 2)"
      using E e by(simp add: Mf_def) (metis \<mu>_mono linorder_not_le)
    hence 2: "\<mu> E + ennreal (e / 2) < \<mu> E + ennreal (e / 2) + ennreal (e / 2)"
      by simp
    from Inf_le_iff[THEN iffD1,OF eq_refl,rule_format,OF _ 1]
    obtain V where V: "openin X V" "E \<subseteq> V" "\<mu> V < \<mu> E + ennreal (e / 2)"
      using \<mu>_def \<mu>_open by force
    have "\<mu> E + ennreal (e / 2) + ennreal (e / 2) \<le> (\<Squnion>K\<in>{K. K \<subseteq> E \<and> compactin X K}. \<mu> K + ennreal e)"    
      by(subst ennreal_SUP_add_left,insert E e) (auto simp: ennreal_plus_if Mf_def)
    from le_Sup_iff[THEN iffD1,OF this,rule_format,OF 2]
    obtain K where K: "compactin X K" "K \<subseteq> E" "\<mu> E  + ennreal (e / 2) < \<mu> K + ennreal e"
      by blast
    have "\<mu> (V - K) < \<infinity>"
      by (metis Diff_subset V(3) \<mu>_mono dual_order.strict_trans1 infinity_ennreal_def order_le_less_trans top_greatest)
    hence "\<mu> K + \<mu> (V - K) = \<mu> (K \<union> (V - K))"
      by(intro step4'(1)[symmetric,OF step2(1)[OF K(1)] step3(2)] openin_diff V(1) compactin_imp_closedin K(1) lh(2))
        (auto simp: disjnt_iff)
    also have "... = \<mu> V"
      by (metis Diff_partition K(2) V(2) order_trans)
    also have "... < \<mu> K + ennreal e"
      by(auto intro!: order.strict_trans[OF V(3)] K)
    finally have "\<mu> (V - K) < ennreal e"
      by(simp add: ennreal_add_left_cancel_less)
    thus ?thesis
      using V K by blast
  qed
  have step6: "\<And>A B. A \<in> Mf \<Longrightarrow> B \<in> Mf \<Longrightarrow> A - B \<in> Mf" "\<And>A B. A \<in> Mf \<Longrightarrow> B \<in> Mf \<Longrightarrow> A \<union> B \<in> Mf"
    "\<And>A B. A \<in> Mf \<Longrightarrow> B \<in> Mf \<Longrightarrow> A \<inter> B \<in> Mf"
  proof -
    {
      fix A B
      assume AB: "A \<in> Mf" "B \<in> Mf"
      have dif1: "\<mu> (A - B) < \<infinity>"
        by (metis (no_types, lifting) AB(1) Diff_subset Mf_def \<mu>_mono infinity_ennreal_def mem_Collect_eq order_le_less_trans)
      have "\<mu> (A - B) = (\<Squnion> (\<mu> ` {K. K \<subseteq> (A - B) \<and> compactin X K}))"
      proof(rule antisym)
        show "\<mu> (A - B) \<le> \<Squnion> (\<mu> ` {K. K \<subseteq> A - B \<and> compactin X K})"
          unfolding le_Sup_iff
        proof safe
          fix y
          assume y:"y < \<mu> (A - B)"
          then obtain e where e: "e > 0" "ennreal e = \<mu> (A - B) - y"
            by (metis dif1 diff_gt_0_iff_gt_ennreal diff_le_self_ennreal ennreal_cases ennreal_less_zero_iff neq_top_trans order_less_le)
          from step5[OF AB(1) half_gt_zero[OF e(1)]] step5[OF AB(2) half_gt_zero[OF e(1)]]
          obtain V1 V2 K1 K2 where VK:
            "openin X V1" "compactin X K1" "K1 \<subseteq> A" "A \<subseteq> V1" "\<mu> (V1 - K1) < ennreal (e / 2)"
            "openin X V2" "compactin X K2" "K2 \<subseteq> B" "B \<subseteq> V2" "\<mu> (V2 - K2) < ennreal (e / 2)"
            by auto
          have K1V2:"compactin X (K1 - V2)"
            by(auto intro!: closed_compactin[OF VK(2)] compactin_imp_closedin[OF lh(2) VK(2)] VK(6))
          have "\<mu> (A - B) \<le> \<mu> ((K1 - V2) \<union> (V1 - K1) \<union> (V2 - K2))"
            using VK by(auto intro!: \<mu>_mono)
          also have "... \<le> \<mu> ((K1 - V2) \<union>  (V1 - K1)) + \<mu> (V2 - K2)"
            by fact
          also have "... \<le> \<mu> (K1 - V2) + \<mu> (V1 - K1) + \<mu> (V2 - K2)"
            by(auto intro!: step1')
          also have "... < \<mu> (K1 - V2) + \<mu> (V1 - K1) + ennreal (e / 2)"
            unfolding add.assoc ennreal_add_left_cancel_less ennreal_add_left_cancel_less
            using step2(1)[OF K1V2] VK(5,10) Mf_def by fastforce
          also have "... \<le> \<mu> (K1 - V2) + ennreal (e / 2) + ennreal (e / 2)"
            using order.strict_implies_order[OF VK(5)] by(auto simp: add_mono)
          also have "... = \<mu> (K1 - V2) + ennreal e"
            using e(1) ennreal_plus_if by auto
          finally have 1:"\<mu> (A - B) < \<mu> (K1 - V2) + ennreal e" .
          show "\<exists>a\<in>(\<mu> ` {K. K \<subseteq> A - B \<and> compactin X K}). (y < a)"
          proof(safe intro!: bexI[where x="\<mu> (K1 - V2)"] imageI)
            have "y  < \<mu> (K1 - V2) + ennreal e - ennreal e"
              by (metis 1 add_diff_self_ennreal e(2) ennreal_less_top less_diff_eq_ennreal order_less_imp_le y)
            also have "... = \<mu> (K1 - V2)"
              by simp
            finally show "y < \<mu> (K1 - V2)" .
          qed(use K1V2 VK in auto)
        qed
      qed(auto intro!: \<mu>_mono simp: Sup_le_iff)
      with dif1 show "A - B \<in> Mf"
        using Mf_def \<mu>_fin_subset by auto
    }
    note diff=this
    fix A B
    assume AB: "A \<in> Mf" "B \<in> Mf"
    show un: "A \<union> B \<in> Mf"
    proof -
      have "A \<union> B = (A - B) \<union> B"
        by fastforce
      also have "... \<in> Mf"
      proof(rule step4'(2))
        have "\<mu> (A - B \<union> B) = \<mu> (A - B) + \<mu> B"
          by(rule step4'(1)) (auto simp: diff AB disjnt_iff)
        also have "... < \<infinity>"
          using Mf_def diff[OF AB] AB(2) by fastforce
        finally show "\<mu> (A - B \<union> B) < \<infinity>" .
      qed(auto simp: diff AB disjnt_iff)
      finally show ?thesis .
    qed
    show int: "A \<inter> B \<in> Mf"
    proof -
      have "A \<inter> B = A - (A - B)"
        by blast
      also have "... \<in> Mf"
        by(auto intro!: diff AB)
      finally show ?thesis .
    qed
  qed
  have step6': "(\<Union>i\<in>I. Ai i) \<in> Mf" if "finite I" "(\<And>i. i \<in> I \<Longrightarrow> Ai i \<in> Mf)" for Ai and I :: "nat set"
  proof -
    have "(\<forall>i\<in>I. Ai i \<in> Mf) \<longrightarrow> (\<Union>i\<in>I. Ai i) \<in> Mf"
      by(rule finite_induct[OF that(1)]) (auto intro!: step6(2) empty_in_Mf)
    with that show ?thesis
      by blast
  qed
  have step7: "sigma_algebra (topspace X) M" "sets (borel_of X) \<subseteq> M"
  proof -
    show sa:"sigma_algebra (topspace X) M"
      unfolding sigma_algebra_iff2
    proof(intro conjI ballI allI impI)
      show "{} \<in> M"
        using empty_in_Mf by(auto simp: M_def)
    next
      show M_subspace:"M \<subseteq> Pow (topspace X)"
        by(auto simp: M_def)
      {
        fix s
        assume s:"s \<in> M"
        show "topspace X - s \<in> M"
          unfolding M_def
        proof(intro conjI CollectI allI impI)
          fix K
          assume K: "compactin X K"
          have "(topspace X - s) \<inter> K = K - (s \<inter> K)"
            using M_subspace s compactin_subset_topspace[OF K] by fast
          also have "... \<in> Mf"
            by(intro step6(1) step2(1)[OF K]) (use s K M_def in blast)
          finally show "(topspace X - s) \<inter> K \<in> Mf" .
        qed blast
      }
      {
        fix An :: "nat \<Rightarrow> _"
        assume An: "range An \<subseteq> M"
        show "(\<Union> (range An)) \<in> M"
          unfolding M_def
        proof(intro CollectI conjI allI impI)
          fix K
          assume K: "compactin X K"
          have "\<exists>Bn. \<forall>n. Bn n = (An n \<inter> K) - (\<Union>i<n. Bn i)"
            by(rule dependent_wellorder_choice) auto
          then obtain Bn where Bn: "\<And>n. Bn n = (An n \<inter> K) - (\<Union>i<n. Bn i)"
            by blast
          have Bn_disj:"disjoint_family Bn"
            unfolding disjoint_family_on_def
          proof safe
            fix m n x
            assume h:"m \<noteq> n" "x \<in> Bn m" "x \<in> Bn n"
            then consider "m < n" | "n < m"
              by linarith
            then show "x \<in> {}"
            proof cases
              case 1
              with h(3) have "x \<notin> Bn m"
                by(auto simp: Bn[of n])
              with h(2) show ?thesis by blast
            next
              case 2
              with h(2) have "x \<notin> Bn n"
                by(auto simp: Bn[of m])
              with h(3) show ?thesis by blast
            qed
          qed
          have un:"(\<Union> (range An) \<inter> K) = (\<Union>n. Bn n)"
          proof -
            have 1:"An n \<inter> K \<subseteq> (\<Union>i\<le>n. Bn i)" for n
            proof safe
              fix x
              assume x:"x \<in> An n" "x \<in> K"
              define m where "m = (LEAST m. x \<in> An m)"
              have m1:"\<And>l. l < m \<Longrightarrow> x \<in> An m \<Longrightarrow> x \<notin> An l"
                using m_def not_less_Least by blast
              hence x_nBn:"l < m \<Longrightarrow> x \<notin> Bn l" for l
                by (metis Bn Diff_Diff_Int Diff_iff m_def not_less_Least)
              have m2: "x \<in> An m"
                by (metis LeastI_ex x(1) m_def)
              have m3: "m \<le> n"
                using m1 m2 not_le_imp_less x(1) by blast
              have "x \<in> Bn m"
                unfolding Bn[of m]
                using x_nBn m2 x(2) by fast
              thus "x \<in> \<Union> (Bn ` {..n})"
                using m3 by blast
            qed
            have 2:"(\<Union>n. An n \<inter> K) = (\<Union>n. Bn n)"
            proof(rule antisym)
              show "(\<Union>n. An n \<inter> K) \<subseteq> \<Union> (range Bn)"
              proof safe
                fix n x
                assume "x \<in> An n" "x \<in> K"
                then have "x \<in> (\<Union>i\<le>n. Bn i)"
                  using 1 by fast
                thus "x \<in> \<Union> (range Bn)"
                  by fast
              qed
            next
              show " \<Union> (range Bn) \<subseteq> (\<Union>n. An n \<inter> K)"
              proof(rule SUP_mono)
                show "\<exists>m\<in>UNIV. Bn i \<subseteq> An m \<inter> K" for i
                  by(auto intro!: bexI[where x=i] simp: Bn[of i])
              qed
            qed
            thus ?thesis
              by simp
          qed
          also have "... \<in> Mf"
          proof(safe intro!: step4(2) Bn_disj)
            fix n
            show "Bn n \<in> Mf"
            proof(rule less_induct)
              fix n
              show " (\<And>m. m < n \<Longrightarrow> Bn m \<in> Mf) \<Longrightarrow> Bn n \<in> Mf"
                using An K by(auto intro!: step6' step6(1) simp :Bn[of n] M_def)
            qed
          next
            have "\<mu> (\<Union> (range Bn)) \<le> \<mu> K"
              unfolding un[symmetric] by(auto intro!: \<mu>_mono)
            also have "... < \<infinity>"
              using step2(1)[OF K] by(auto simp: Mf_def)
            finally show "\<mu> (\<Union> (range Bn)) < \<infinity>" .
          qed
          finally show "\<Union> (range An) \<inter> K \<in> Mf " .
        qed(use An M_def in auto)
      }
    qed
    show "sets (borel_of X) \<subseteq> M"
      unfolding sets_borel_of_closed
    proof(safe intro!: sigma_algebra.sigma_sets_subset[OF sa])
      fix T
      assume "closedin X T"
      then show "T \<in> M"
        by (simp add: Int_commute M_def closedin_subset compact_Int_closedin step2(1))
    qed
  qed
  have step8: "A \<in> Mf \<longleftrightarrow> A \<in> M \<and> \<mu> A < \<infinity>" for A
  proof safe
    assume A: "A \<in> Mf"
    then have "A \<subseteq> topspace X"
      by(auto simp: Mf_def)
    thus "A \<in> M"
      by(auto simp: M_def intro!:step6(3)[OF A step2(1)])
    show "\<mu> A < \<infinity>"
      using A by(auto simp: Mf_def)
  next
    assume A: "A \<in> M" "\<mu> A < \<infinity>"
    hence "A \<subseteq> topspace X"
      using M_def by blast
    moreover have "\<mu> A = (\<Squnion> (\<mu> ` {K. K \<subseteq> A \<and> compactin X K}))"
    proof(rule antisym)
      show "\<mu> A \<le> \<Squnion> (\<mu> ` {K. K \<subseteq> A \<and> compactin X K})"
        unfolding le_Sup_iff
      proof safe
        fix y
        assume y:"y < \<mu> A"
        then obtain e where e: "e > 0" "ennreal e = \<mu> A - y"
          by (metis A(2) diff_gt_0_iff_gt_ennreal diff_le_self_ennreal ennreal_cases ennreal_less_zero_iff neq_top_trans order_less_le)
        obtain U where U: "openin X U" "A \<subseteq> U" "\<mu> U < \<infinity>"
          using Inf_less_iff[THEN iffD1,OF A(2)[simplified \<mu>_def]] \<mu>_open by force
        from step5[OF step3(2)[OF U(1,3)] half_gt_zero[OF e(1)]]
        obtain V K where VK:
            "openin X V" "compactin X K" "K \<subseteq> U" "U \<subseteq> V" "\<mu> (V - K) < ennreal (e / 2)"
          by blast
        have AK: "A \<inter> K \<in> Mf"
          using step2(1) VK(2) A by(auto simp: M_def)
        hence e': "\<mu> (A \<inter> K) < \<mu> (A \<inter> K) + ennreal (e / 2)"
          by (metis Diff_Diff_Int Diff_subset Int_commute U(3) VK(3) VK(5) \<mu>_mono add.commute diff_gt_0_iff_gt_ennreal ennreal_add_diff_cancel infinity_ennreal_def order_le_less_trans top.not_eq_extremum zero_le)
        have "\<mu> (A \<inter> K) + ennreal (e / 2) = (\<Squnion>K\<in>{L. L \<subseteq> (A \<inter> K) \<and> compactin X L}. \<mu> K + ennreal (e / 2))"
          by(subst ennreal_SUP_add_left) (use AK Mf_def in auto)
        from le_Sup_iff[THEN iffD1,OF this[THEN eq_refl],rule_format,OF e']
        obtain H where H: "compactin X H" "H \<subseteq> A \<inter> K" "\<mu> (A \<inter> K) < \<mu> H + ennreal (e / 2)"
          by blast
        show "\<exists>a\<in>\<mu> ` {K. K \<subseteq> A \<and> compactin X K}. y < a"
        proof(safe intro!: bexI[where x="\<mu> H"] imageI H(1))
          have "\<mu> A \<le> \<mu> ((A \<inter> K) \<union> (V - K))"
            using VK U by(auto intro!: \<mu>_mono)
          also have "... \<le> \<mu> (A \<inter> K) + \<mu> (V - K)"
            by(auto intro!: step1'(1))
          also have "... < \<mu> H + ennreal (e / 2) + ennreal (e / 2)"
            using H(3) VK(5) add_strict_mono by blast
          also have "... = \<mu> H + ennreal e"
            using e(1) ennreal_plus_if by fastforce
          finally have 1: "\<mu> A < \<mu> H + ennreal e" .
          have "y = \<mu> A - ennreal e"
            using A(2) diff_diff_ennreal e(2) y by fastforce
          also have "... < \<mu> H + ennreal e - ennreal e"
            using 1
            by (metis diff_le_self_ennreal e(2) ennreal_add_diff_cancel_right ennreal_less_top minus_less_iff_ennreal top_neq_ennreal)
          also have "... = \<mu> H"
            by simp
          finally show "y < \<mu> H" .
        qed(use H in auto)
      qed
    qed(auto simp: Sup_le_iff intro!: \<mu>_mono)
    ultimately show "A \<in> Mf"
      using A(2) Mf_def by auto
  qed
  define N where "N \<equiv> measure_of (topspace X) M \<mu>"
  have step9: "measure_space (topspace X) M \<mu>"
    unfolding measure_space_def
  proof safe
    show "countably_additive M \<mu>"
      unfolding countably_additive_def
      by (metis Sup_upper UNIV_I \<mu>_mono image_eqI image_subset_iff infinity_ennreal_def linorder_not_less neq_top_trans step1 step4(1) step8)
  qed(auto simp: step7 positive_def \<mu>_empty)
  have space_N: "space N = topspace X" and sets_N: "sets N = M" and emeasure_N: "A \<in> sets N \<Longrightarrow> emeasure N A = \<mu> A" for A
  proof -
    show "space N = topspace X"
      by (simp add: N_def space_measure_of_conv)
    show 1:"sets N = M"
      by (simp add: N_def sigma_algebra.sets_measure_of_eq step7(1))
    have "\<And>x. x \<in> M \<Longrightarrow> x \<subseteq> topspace X"
      by(auto simp: M_def)
    thus "A \<in> sets N \<Longrightarrow> emeasure N A = \<mu> A"
      unfolding N_def using step9 by(auto intro!: emeasure_measure_of simp: measure_space_def 1[simplified N_def])
  qed
  have g1:"subalgebra N (borel_of X)" (is ?g1)
   and g2:"(\<forall>A\<in>sets N. emeasure N A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N C))" (is ?g2)
   and g3:"(\<forall>A. openin X A \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))" (is ?g3)
   and g4:"(\<forall>A\<in>sets N. emeasure N A < \<infinity> \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))" (is ?g4)
   and g5:"(\<forall>K. compactin X K \<longrightarrow> emeasure N K < \<infinity>)" (is ?g5)
   and g6:"complete_measure N" (is ?g6)
  proof -
    have 1: "\<And>P. (\<And>C. P C \<Longrightarrow> C \<in> sets N) \<Longrightarrow> emeasure N ` {C. P C} = \<mu> ` {C. P C}"
      using emeasure_N by auto
    show ?g1
      by(auto simp: subalgebra_def sets_N space_N space_borel_of step7)
    show ?g2
    proof -
      have "emeasure N ` {C. openin X C \<and> A \<subseteq> C} = \<mu> ` {C. openin X C \<and> A \<subseteq> C}" for A
        using step7(2) by(auto intro!: 1 simp: sets_N dest: borel_of_open)
      hence "emeasure N ` {C. openin X C \<and> A \<subseteq> C} = \<mu>' ` {C. openin X C \<and> A \<subseteq> C}" for A
        using \<mu>_open by auto
      thus ?thesis
        by(simp add: emeasure_N sets_N \<mu>_def) (metis (no_types, lifting) Collect_cong)
    qed
    show ?g3
      by (metis (no_types, lifting) 1 borel_of_open emeasure_N sets_N step2(1) step3(1) step7(2) step8 subsetD)
    show ?g4
    proof safe
      fix A
      assume A[measurable]: "A \<in> sets N" "emeasure N A < \<infinity>"
      then have Mf:"A \<in> Mf"
        by (simp add: emeasure_N sets_N step8)
      have "emeasure N A = \<mu> A"
        by (simp add: emeasure_N)
      also have "... = \<Squnion> (\<mu> ` {K. compactin X K \<and> K \<subseteq> A})"
        using Mf unfolding Mf_def by simp metis
      also have "... = \<Squnion> (emeasure N ` {K. compactin X K \<and> K \<subseteq> A})"
        using emeasure_N sets_N step2(1) step8 by auto
      finally show "emeasure N A = \<Squnion> (emeasure N ` {K. compactin X K \<and> K \<subseteq> A})" .
    qed
    show ?g5
      using emeasure_N sets_N step2(1) step8 by auto
    show ?g6
    proof
      fix A B
      assume AB:"B \<subseteq> A" "A \<in> null_sets N"
      then have "\<mu> A = 0"
        by (metis emeasure_N null_setsD1 null_setsD2)
      hence 1:"\<mu> B = 0"
        using \<mu>_mono[OF AB(1)] by fastforce
      have "B \<in> Mf"
      proof -
        have "B \<subseteq> topspace X"
          by (metis AB gfp.leq_trans null_setsD2 sets.sets_into_space space_N)
        moreover have "\<mu> B = \<Squnion> (\<mu> ` {K. K \<subseteq> B \<and> compactin X K})"
        proof(rule antisym)
          show "\<Squnion> (\<mu> ` {K. K \<subseteq> B \<and> compactin X K}) \<le> \<mu> B"
            by(auto simp: Sup_le_iff \<mu>_mono)
        qed(simp add: 1)
        moreover have "\<mu> B < \<top>"
          by(simp add: 1)
        ultimately show ?thesis
          unfolding Mf_def by blast
      qed
      thus "B \<in> sets N"
        by(simp add: step8 sets_N)
    qed
  qed        
      
  have g7: "(\<forall>f. ?iscont f \<longrightarrow> ?csupp f \<longrightarrow> integrable N f)"
    unfolding integrable_iff_bounded
  proof safe
    fix f
    assume f:"?iscont f" "?csupp f"
    then show [measurable]:"f \<in> borel_measurable N"
      by(auto intro!: measurable_from_subalg[OF g1]
          simp: lower_semicontinuous_map_measurable upper_lower_semicontinuous_map_iff_continuous_map)
    let ?K = "X closure_of {x\<in>topspace X. f x \<noteq> 0}"
    have K[measurable]: "compactin X ?K" "?K \<in> sets N"
      using f(2) g1 sets_N step2(1) step8 by(auto simp: has_compact_support_on_iff subalgebra_def)
    have "bounded (f ` ?K)"
      using image_compactin[of X ?K euclideanreal f] f
      by(auto simp: has_compact_support_on_iff intro!: compact_imp_bounded)
    then obtain B where B:"\<And>x. x \<in> ?K \<Longrightarrow> \<bar>f x\<bar> \<le> B"
      by (meson bounded_real imageI)
    show "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>N) < \<infinity>"
    proof -
      have "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>N) \<le> (\<integral>\<^sup>+ x. ennreal (indicator ?K x *\<bar>f x\<bar>) \<partial>N)"
        using in_closure_of by(fastforce intro!: nn_integral_mono simp: indicator_def space_N)
      also have "... \<le> (\<integral>\<^sup>+ x. ennreal (B * indicator ?K x) \<partial>N)"
        using B by(auto intro!: nn_integral_mono ennreal_leI simp: indicator_def)
      also have "... = (\<integral>\<^sup>+ x. ennreal B * indicator ?K x \<partial>N)"
        by(auto intro!: nn_integral_cong simp: indicator_def)
      also have "... = ennreal B * (\<integral>\<^sup>+ x. indicator ?K x \<partial>N)"
        by(simp add: nn_integral_cmult)
      also have "... = ennreal B * emeasure N ?K"
        by simp
      finally show ?thesis
        using g5 K(1) ennreal_mult_less_top linorder_not_le top.not_eq_extremum by fastforce
    qed
  qed
  have g8: "\<forall>f. ?iscont f \<longrightarrow> ?csupp f \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N)"
  proof safe
    have 1: "\<phi> (\<lambda>x\<in>topspace X. f x) \<le> (\<integral>x. f x \<partial>N)" if f:"?iscont f" "?csupp f" for f
    proof -
      let ?K = "X closure_of {x\<in>topspace X. f x \<noteq> 0}"
      have K[measurable]: "compactin X ?K" "?K \<in> sets N"
        using f(2) g1  sets_N step2(1) step8 by(auto simp: has_compact_support_on_iff subalgebra_def)
      have f_meas[measurable]: "f \<in> borel_measurable N"
        using f by(auto intro!: measurable_from_subalg[OF g1]
            simp: lower_semicontinuous_map_measurable upper_lower_semicontinuous_map_iff_continuous_map)
      have "bounded (f ` ?K)"
        using image_compactin[of X ?K euclideanreal f] f
        by(auto simp: has_compact_support_on_iff intro!: compact_imp_bounded)
      then obtain B' where B':"\<And>x. x \<in> ?K \<Longrightarrow> \<bar>f x\<bar> \<le> B'"
        by (meson bounded_real imageI)
      define B where "B \<equiv> max 1 B'"
      have B_pos: "B > 0" and B: "\<And>x. x \<in> ?K \<Longrightarrow> \<bar>f x\<bar> \<le> B"
        using B' by(auto simp add: B_def intro!: max.coboundedI2)
      have 1:"\<phi> (\<lambda>x\<in>topspace X. f x) \<le> (\<integral>x. f x \<partial>N) +  1 / (Suc n) * (2 * measure N ?K + (1 / Suc n) + 2 * B + 1)" for n
      proof -
        have "\<exists>yn. \<forall>m::nat. yn m = (if m = 0 then - B - 1 else  1 / 2 * 1 / Suc n + yn (m - 1))"
          by(rule dependent_wellorder_choice) auto
        then obtain yn' where yn':"\<And>m::nat. yn' m = (if m = 0 then - B - 1 else  1 / 2 * 1 / Suc n + yn' (m - 1))"
          by blast
        hence yn'_0: "yn' 0 = - B - 1" and yn'_Suc: "\<And>m. yn' (Suc m) = 1 / 2 * 1 / Suc n + yn' m"
          by simp_all
        have yn'_accum: "yn' m = m * (1 / 2 * 1 / Suc n) + yn' 0" for m
          by(induction m) (auto simp: yn'_Suc add_divide_distrib)

        define L :: nat where "L = (LEAST k. B \<le> yn' k)"
        define yn where "yn \<equiv> (\<lambda>n. if n = L then B else yn' n)"
        have L_least: "\<And>i. i < L \<Longrightarrow> yn' i < B"
          by (metis L_def linorder_not_less not_less_Least)
        have yn_L: "yn L = B"
          by(auto simp: yn_def)
        have yn'_L: "yn' L \<ge> B"
          unfolding L_def
        proof(rule LeastI_ex)
          show "\<exists>x. B \<le> yn' x"
          proof(safe intro!: exI[where x="nat (ceiling ((2 * B + 2) / ((1/2) * 1 / real (Suc n))))"])
            have "B \<le> 2 * B + 2 + (- B - 1)"
              using B_pos by fastforce
            also have "... = (2 * B + 2) / ((1/2) * 1 / real (Suc n)) * (1 / 2 * 1 / Suc n) + yn' 0"
              by(auto simp: yn'_0)
            also have "... \<le> real (nat (ceiling ((2 * B + 2) / ((1/2) * 1 / real (Suc n))))) * (1 / 2 * 1 / Suc n) + yn' 0"
              by(intro add_mono real_nat_ceiling_ge mult_right_mono) auto
            also have "... = yn' (nat (ceiling ((2 * B + 2) / ((1/2) * 1 / real (Suc n)))))"
              by (metis yn'_accum)
            finally show " B \<le> yn' (nat \<lceil>(2 * B + 2) / (1 / 2 * 1 / real (Suc n))\<rceil>)" .
          qed
        qed
        have L_pos: "0 < L"
        proof(rule ccontr)
          assume "\<not> 0 < L"
          then have [simp]:"L = 0"
            by blast
          show False
            using yn'_L yn'_0 B_pos by auto
        qed
        have yn_0: "yn 0 = - B - 1"
          using L_pos by(auto simp: yn_def yn'_0)
        have strict_mono_yn:"strict_mono yn"
        proof(rule strict_monoI_Suc)
          fix m
          consider "m = L" | "Suc m = L" | "m < L" "Suc m < L" | "L < m" "L < Suc m"
            by linarith
          then show "yn m < yn (Suc m)"
          proof cases
            case 1
            then have "yn m = B"
              by(simp add: yn_L)
            also have "... \<le> yn' m"
              using yn'_L by(simp add: 1)
            also have "... < yn' (Suc m)"
              by (simp add: yn'_Suc)
            also have "... = yn (Suc m)"
              using 1 by(auto simp: yn_def)
            finally show ?thesis .
          next
            case 2
            then have "yn m = yn' m"
              using yn_def by force
            also have "... < B"
              using L_least[of m] 2 by blast
            also have "... = yn (Suc m)"
              by(simp add: 2 yn_L)
            finally show ?thesis .
          qed(auto simp: yn_def yn'_Suc)
        qed
        have yn_le_L: "\<And>i. i \<le> L \<Longrightarrow> yn i \<le> B"
          using L_least less_eq_real_def yn_def by auto
        have yn_ge_L: "\<And>i. L < i \<Longrightarrow> B < yn i"
          using strict_mono_yn[THEN strict_monoD] yn_L by blast
        have yn_ge: "\<And>i. - B - 1 \<le> yn i"
          using monoD[OF strict_mono_mono[OF strict_mono_yn],of 0] yn_0 by auto
        have yn_Suc_le: "yn (Suc i) < 1 / real (Suc n) + yn i" for i
        proof -
          consider "i = L" | "Suc i = L" | "i < L" "Suc i < L" | "L < i" "L < Suc i"
            by linarith
          then show ?thesis
          proof cases
            case 1
            then have "yn (Suc i) = yn' (Suc L)"
              by(simp add: yn_def)
            also have "... = 1 / 2 * 1 / Suc n + yn' L"
              by(simp add: yn'_Suc)
            also have "... = (1 / 2) * (1 / Suc n) + (1 / 2) * (1 / Suc n) + yn' (L - 1)"
              using L_pos yn' by fastforce
            also have "... = 1 / Suc n + yn' (L - 1)"
              unfolding semiring_normalization_rules(1) by simp
            also have "... < 1 / Suc n + B"
              by (simp add: L_least L_pos less_eq_real_def)
            finally show ?thesis
              by(simp add: 1 yn_L)
          next
            case 2
            then have "yn (Suc i) = B"
              by(simp add: yn_L)
            also have "... \<le> yn' L"
              using yn'_L .
            also have "... = 1 / 2 * 1 / Suc n + yn' (L - 1)"
              using yn' L_pos by simp
            also have "... = 1 / 2 * 1 / Suc n + yn i"
              using 2 yn_def by force
            also have "... < 1 / Suc n + yn i"
              by (simp add: pos_less_divide_eq)
            finally show ?thesis .
          qed(auto simp: yn_def yn'_Suc pos_less_divide_eq)
        qed

        have f_bound: "f x \<in> {yn 0<..yn L}" if x:"x \<in> ?K" for x
          using B[OF x] yn_L yn_0 by auto
        define En where "En \<equiv> (\<lambda>m. {x\<in>topspace X. yn m < f x \<and> f x \<le> yn (Suc m)} \<inter> ?K)"
        have En_sets[measurable]: "En m \<in> sets N" for m
        proof -
          have "{x\<in>topspace X. yn m < f x \<and> f x \<le> yn (Suc m)} = f -` {yn m<..yn (Suc m)} \<inter> space N"
            by(auto simp: space_N)
          also have "... \<in> sets N"
            by simp
          finally show ?thesis
            by(simp add: En_def)
        qed
        have En_disjnt: "disjoint_family En"
          unfolding disjoint_family_on_def
        proof safe
          fix m n x
          assume "m \<noteq> n" and x: "x \<in> En n" "x \<in> En m"
          then consider "m < n" | "n < m"
            by linarith
          thus "x \<in> {}"
          proof cases
            case 1
            hence 1:"Suc m \<le> n"
              by simp
            from x have "f x \<le> yn (Suc m)" "yn n < f x"
              by(auto simp: En_def)
            with 1 show ?thesis
              using monoD[OF strict_mono_mono[OF strict_mono_yn] 1] by linarith
          next
            case 2
            hence 1:"Suc n \<le> m"
              by simp
            from x have "f x \<le> yn (Suc n)" "yn m < f x"
              by(auto simp: En_def)
            with 1 show ?thesis
              using monoD[OF strict_mono_mono[OF strict_mono_yn] 1] by linarith
          qed
        qed
        have K_eq_un_En: "?K = (\<Union>i\<le>L. En i)"
        proof safe
          fix x
          assume x:"x \<in> ?K"
          have "\<exists>m\<in>{..L}. yn m < f x \<and> x \<in> topspace X \<and> f x \<le> yn (Suc m)"
          proof(rule ccontr)
            assume "\<not> (\<exists>m\<in>{..L}. yn m < f x \<and> x \<in> topspace X \<and> f x \<le> yn (Suc m))"
            then have 1:"\<And>m. m \<le> L \<Longrightarrow> yn (Suc m) < f x \<or> f x \<le> yn m"
              using compactin_subset_topspace[OF K(1)] x by force
            then have "m \<le> L \<Longrightarrow> yn (Suc m) < f x" for m
              by(induction m) (use B x yn_0 in fastforce)+
            hence "yn (Suc L) < f x"
              by force
            with yn_ge_L[of "Suc L"] f_bound x B show False
              by fastforce
          qed
          thus "x \<in> (\<Union>i\<le>L. En i)"
            using x by(auto simp: En_def)
        qed(auto simp: En_def)
        have emeasure_En_fin: "emeasure N (En i) < \<infinity>" for i
        proof -
          have "emeasure N (En i) \<le> \<mu> ?K"
            unfolding emeasure_N[OF En_sets[of i]] by(auto intro!: \<mu>_mono simp: En_def)
          also have "... < \<infinity>"
            using step2(1)[OF K(1)] step8 by blast
          finally show ?thesis .
        qed
        have "\<exists>Vi. openin X Vi \<and> En i \<subseteq> Vi \<and> measure N Vi < measure N (En i) + (1 / Suc n) / Suc L \<and>
                   (\<forall>x\<in>Vi. f x < (1 / real (Suc n) + yn i)) \<and> emeasure N Vi < \<infinity>" for i
        proof -
          have 1:"emeasure N (En i) < emeasure N (En i) + ennreal (1 / real (Suc n) / real (Suc L))"
            unfolding ennreal_add_left_cancel_less[where b=0,simplified add_0_right]
            using emeasure_En_fin by (simp add: order_less_le)
          from Inf_le_iff[THEN iffD1,OF eq_refl[OF g2[rule_format,OF En_sets[of i],symmetric]],rule_format,OF this]
          obtain Vi where Vi:"openin X Vi" "Vi \<supseteq> En i"
            "emeasure N Vi < emeasure N (En i) + ennreal (1 / real (Suc n) / real (Suc L))"
            by blast
          hence "ennreal (measure N Vi) = emeasure N Vi"
            unfolding measure_def using ennreal_enn2real_if by fastforce
          also have "... < ennreal (measure N (En i)) + ennreal (1 / real (Suc n) / real (Suc L))"
            using ennreal_enn2real_if emeasure_En_fin Vi by (metis emeasure_eq_ennreal_measure top.extremum_strict)
          also have "... = ennreal (measure N (En i) + 1 / real (Suc n) / real (Suc L))"
            by simp
          finally have 1:"measure N Vi < measure N (En i) + 1 / real (Suc n) / real (Suc L)"
            by(auto intro!: ennreal_less_iff[THEN iffD1])
          define Vi' where "Vi' = Vi \<inter> {x\<in>topspace X. yn i < f x \<and> f x < 1 / real (Suc n) + yn i}"
          have "En i \<subseteq> Vi'"
          proof -
            have "En i = En i \<inter> {x\<in>topspace X. yn i < f x \<and> f x < 1 / real (Suc n) + yn i}"
              unfolding En_def using order.strict_trans1[OF _ yn_Suc_le] by fast
            also have "... \<subseteq> Vi'"
              using Vi(2) by(auto simp: Vi'_def)
            finally show ?thesis .
          qed
          moreover have "openin X Vi'"
          proof -
            have "{x \<in> topspace X. yn i<f x \<and> f x< 1/real (Suc n) + yn i} = (f -` {yn i<..<1/real (Suc n) + yn i} \<inter> topspace X)"
              by fastforce
            also have "openin X ..."
              using continuous_map_open[OF f(1)] by simp
            finally show ?thesis
              using Vi(1) by(auto simp: Vi'_def)
          qed
          moreover have "measure N Vi' <  measure N (En i) + (1 / real (Suc n) / real (Suc L))" (is "?l < ?r")
          proof -
            have "?l \<le> measure N Vi"
              unfolding measure_def
            proof(safe intro!: enn2real_mono emeasure_mono)
              show "Vi \<in> sets N"
                using Vi(1) borel_of_open sets_N step7(2) by blast
              show "emeasure N Vi < \<top>"
                by (metis \<open>ennreal (Sigma_Algebra.measure N Vi) = emeasure N Vi\<close> ennreal_less_top)
            qed(auto simp: Vi'_def)
            with 1 show ?thesis
              by fastforce
          qed
          moreover have "\<And>x. x \<in> Vi' \<Longrightarrow> f x < (1 / real (Suc n) + yn i)"
            by(auto simp: Vi'_def)
          moreover have "emeasure N Vi' < \<infinity>"
            by (metis (no_types, lifting) Diff_Diff_Int Diff_subset Vi'_def Vi(1) \<open>ennreal (measure N Vi) = emeasure N Vi\<close> borel_of_open
                      emeasure_mono ennreal_less_top infinity_ennreal_def linorder_not_less sets_N step7(2) subsetD top.not_eq_extremum)
          ultimately show ?thesis
            by blast
        qed
        then obtain Vi where
          Vi: "\<And>i. openin X (Vi i)" "\<And>i. En i \<subseteq> Vi i"
          "\<And>i. measure N (Vi i) < measure N (En i) + (1 / Suc n) / Suc L"
          "\<And>i x. x \<in> Vi i \<Longrightarrow> f x < (1 / real (Suc n) + yn i)"
          "\<And>i. emeasure N (Vi i) < \<infinity>"
          by metis
        have "?K \<subseteq> (\<Union>i\<le>L. Vi i)"
          using K_eq_un_En Vi(2) by blast
        from fApartition[OF K(1) Vi(1) this]
        obtain hi where hi: "\<And>i. i \<le> L \<Longrightarrow> ?iscont (hi i)" "\<And>i. i \<le> L \<Longrightarrow> ?csupp (hi i)"
          "\<And>i. i \<le> L \<Longrightarrow> X closure_of {x \<in> topspace X.  hi i x \<noteq> 0} \<subseteq> Vi i"
         "\<And>i. i \<le> L \<Longrightarrow> hi i \<in> topspace X \<rightarrow> {0..1}" "\<And>i. i \<le> L \<Longrightarrow> hi i \<in> topspace X - Vi i \<rightarrow> {0}"
         "\<And>x. x \<in> ?K \<Longrightarrow> (\<Sum>i\<le>L. hi i x) = 1" "\<And>x. x \<in> topspace X \<Longrightarrow> 0 \<le> (\<Sum>i\<le>L. hi i x)"
         "\<And>x. x \<in> topspace X \<Longrightarrow> (\<Sum>i\<le>L. hi i x) \<le> 1"
          by blast
        have f_sum_hif: "(\<Sum>i\<le>L. f x * hi i x) = f x" if x:"x \<in> topspace X" for x
        proof(cases "f x = 0")
          case False
          then have "x \<in> ?K"
            using in_closure_of x by fast
          with hi(6)[OF this] show ?thesis
            by(simp add: sum_distrib_left[symmetric])
        qed simp
        have sum_muEi:"(\<Sum>i\<le>L. measure N (En i)) = measure N ?K"
        proof -
          have "(\<Sum>i\<le>L. measure N (En i)) = measure N (\<Union>i\<le>L. En i)"
            using emeasure_En_fin En_disjnt
            by(fastforce intro!: measure_UNION'[symmetric] fmeasurableI pairwiseI simp: disjnt_iff disjoint_family_on_def)
          also have "... = measure N ?K"
            by(simp add: K_eq_un_En)
          finally show ?thesis .
        qed
        have measure_K_le: "measure N ?K \<le> (\<Sum>i\<le>L. \<phi> (\<lambda>x\<in>topspace X. hi i x))"
        proof -
          have "ennreal (measure N ?K) = \<mu> ?K"
            by (metis (mono_tags, lifting) K(1) K(2) Sigma_Algebra.measure_def emeasure_N ennreal_enn2real g5 infinity_ennreal_def)
          also  have "\<mu> ?K \<le> ennreal (\<phi> (\<lambda>x\<in>topspace X. \<Sum>i\<le>L. hi i x))"
            by(auto intro!: le_Inf_iff[THEN iffD1,OF eq_refl[OF step2(2)[OF K(1)]],rule_format]
                imageI exI[where x="\<lambda>x. \<Sum>i\<le>L. hi i x"] has_compact_support_on_sum hi continuous_map_sum)
          also have "... =  ennreal (\<Sum>i\<le>L. \<phi> (\<lambda>x\<in>topspace X. hi i x))"
            by(auto intro!: pos_lin_functional_on_CX_sum assms ennreal_cong hi)
          finally show ?thesis
            using Pi_mem[OF hi(4)] by(auto intro!: ennreal_le_iff[of _ "measure N ?K",THEN iffD1] sum_nonneg pos hi)
        qed
        have "\<phi> (restrict f (topspace X)) = \<phi> (\<lambda>x\<in>topspace X. \<Sum>i\<le>L. f x * hi i x)"
          using f_sum_hif restrict_ext by force
        also have "... = (\<Sum>i\<le>L. \<phi> (\<lambda>x\<in>topspace X. f x * hi i x))"
          using f hi by(auto intro!: pos_lin_functional_on_CX_sum assms has_compact_support_on_mult_right)
        also have "... \<le> (\<Sum>i\<le>L. \<phi> (\<lambda>x\<in>topspace X. (1 / (Suc n) + yn i) * hi i x))"
        proof(safe intro!: sum_mono \<phi>mono)
          fix i x
          assume i:"i \<le> L" "x \<in> topspace X"
          show "f x * hi i x \<le> (1 / (Suc n) + yn i) * hi i x"
          proof(cases "x \<in> Vi i")
            case True
            hence "f x < 1 / (Suc n) + yn i"
              by fact
            thus ?thesis
              using Pi_mem[OF hi(4)[OF i(1)] i(2)] by(intro mult_right_mono) auto
          next
            case False
            then show ?thesis
              using Pi_mem[OF hi(5)[OF i(1)]] i(2) by force
          qed
        qed(auto intro!: f hi has_compact_support_on_mult_left)
        also have "... = (\<Sum>i\<le>L. (1 / (Suc n) + yn i) * \<phi> (\<lambda>x\<in>topspace X. hi i x))"
          by(intro Finite_Cartesian_Product.sum_cong_aux linear hi) auto
        also have "... = (\<Sum>i\<le>L. (1 / (Suc n) + yn i + (B + 1)) * \<phi> (\<lambda>x\<in>topspace X. hi i x))
                          - (\<Sum>i\<le>L. (B + 1) * \<phi> (\<lambda>x\<in>topspace X. hi i x))"
          by(simp add: sum_subtractf[symmetric] distrib_right)
        also have "... = (\<Sum>i\<le>L. (1 / (Suc n) + yn i + (B + 1)) * \<phi> (\<lambda>x\<in>topspace X. hi i x))
                          - (B + 1) * (\<Sum>i\<le>L. \<phi> (\<lambda>x\<in>topspace X. hi i x))"
          by (simp add: sum_distrib_left)
        also have "... \<le> (\<Sum>i\<le>L. (1 / (Suc n) + yn i + (B + 1)) * (measure N (En i) + (1 / Suc n / Suc L)))
                          - (B + 1) * measure N ?K"
        proof(safe intro!: diff_mono[OF sum_mono[OF mult_left_mono]])
          fix i
          assume i: "i \<le> L"
          show "\<phi> (restrict (hi i) (topspace X)) \<le> measure N (En i) + 1 / (Suc n) / (Suc L)" (is "?l \<le> ?r")
          proof -
            have "?l \<le> measure N (Vi i)"
            proof -
              have "ennreal (\<phi> (restrict (hi i) (topspace X))) \<le> \<mu>' (Vi i)"
                using hi(1,2,3,4,5)[OF i] by(auto intro!: SUP_upper imageI exI[where x="hi i"] simp: \<mu>'_def)
              also have "... = emeasure N (Vi i)"
                by (metis Vi(1) \<mu>_open borel_of_open emeasure_N sets_N step7(2) subsetD)
              also have "... = ennreal (measure N (Vi i))"
                using Vi(5)[of i] by(auto simp: measure_def intro!: ennreal_enn2real[symmetric])
              finally show "\<phi> (restrict (hi i) (topspace X)) \<le> measure N (Vi i)"
                using ennreal_le_iff measure_nonneg by blast
            qed
            with Vi(3)[of i] show ?thesis
              by linarith
          qed
          show "0 \<le> 1 / real (Suc n) + yn i + (B + 1)"
            using yn_ge[of i] by(simp add: add.assoc)
        qed(use B_pos measure_K_le in fastforce)
        also have "... = (\<Sum>i\<le>L. (yn i - 1 / (Suc n)) * measure N (En i)) + 2 * (\<Sum>i\<le>L. ((1 / Suc n)) * measure N (En i))
                          + (\<Sum>i\<le>L. (B + 1) * measure N (En i))
                          + (\<Sum>i\<le>L. (1 / (Suc n) + yn i + (B + 1)) * (1 / Suc n / Suc L)) - (B + 1) * measure N ?K"
          by(simp add: distrib_left distrib_right sum.distrib sum_subtractf left_diff_distrib)
        also have "... = (\<Sum>i\<le>L. (yn i - 1 / (Suc n)) * measure N (En i)) + 1 / Suc n * 2* measure N ?K
                          + (\<Sum>i\<le>L. (1 / (Suc n) + yn i + (B + 1)) * (1 / Suc n / Suc L))"
          by(simp add: sum_distrib_left[symmetric] sum_muEi del: times_divide_eq_left)
        also have "... \<le> (\<Sum>i\<le>L. (yn i - 1 / (Suc n)) * measure N (En i)) + 1 / Suc n * 2* measure N ?K
                          + (\<Sum>i\<le>L. (1 / (Suc n) + B + (B + 1)) * (1 / Suc n / Suc L))"
        proof -
          have "(\<Sum>i\<le>L. (1 / (Suc n) + yn i + (B + 1)) * (1 / Suc n / Suc L))
                 \<le> (\<Sum>i\<le>L. (1 / (Suc n) + B + (B + 1)) * (1 / Suc n / Suc L))"
          proof(safe intro!: sum_mono mult_right_mono)
            fix i
            assume i: "i \<le> L"
            show "1 / (Suc n) + yn i + (B + 1) \<le> 1 / (Suc n) + B + (B + 1)"
              using yn_le_L[OF i] by fastforce
          qed auto
          thus ?thesis
            by argo
        qed
        also have "... = (\<Sum>i\<le>L. (yn i - 1 / (Suc n)) * measure N (En i)) + 1 / Suc n * 2* measure N ?K
                          + (1 / (Suc n) + B + (B + 1)) * (1 / Suc n)"
          by simp
        also have "... = (\<Sum>i\<le>L. (yn i - 1 / (Suc n)) * measure N (En i))
                          + 1 / Suc n * (2 * measure N ?K + (1 / Suc n) + 2 * B + 1)"
          by argo
        also have "... \<le> (\<integral>x. f x \<partial>N) + 1 / (Suc n) * (2 * measure N ?K + (1 / Suc n) + 2 * B + 1)"
        proof -
          have "(\<Sum>i\<le>L. (yn i - 1 / (Suc n)) * measure N (En i)) \<le> (\<integral>x. f x \<partial>N)" (is "?l \<le> ?r")
          proof -
            have "?l = (\<Sum>i\<le>L. (\<integral>x. (yn i - 1 / (Suc n)) * indicator (En i) x \<partial>N))"
              by simp
            also have "... = (\<integral>x. (\<Sum>i\<le>L. (yn i - 1 / (Suc n)) * indicator (En i) x) \<partial>N)"
              by(rule Bochner_Integration.integral_sum[symmetric]) (use emeasure_En_fin in simp)
            also have "... \<le> ?r"
            proof(rule integral_mono)
              fix x
              assume x: "x \<in> space N"
              consider "\<And>i. i \<le> L \<Longrightarrow> x \<notin> En i" | "\<exists>i\<le>L. x \<in> En i"
                by blast
              then show " (\<Sum>i\<le>L. (yn i - 1 / real (Suc n)) * indicat_real (En i) x) \<le> f x"
              proof cases
                case 1
                then have "x \<notin> ?K"
                  by(simp add: K_eq_un_En)
                hence "f x = 0"
                  using x in_closure_of by(fastforce simp: space_N)
                with 1 show ?thesis
                  by force
              next
                case 2
                then obtain i where i: "i \<le> L" "x \<in> En i"
                  by blast
                with En_disjnt have "\<And>j. j \<noteq> i \<Longrightarrow> x \<notin> En j"
                  by(auto simp: disjoint_family_on_def)
                hence "(\<Sum>i\<le>L. (yn i - 1 / real (Suc n)) * indicat_real (En i) x)
                        = (\<Sum>j\<le>L. if j = i then (yn i - 1 / real (Suc n)) else 0)"
                  by(intro Finite_Cartesian_Product.sum_cong_aux) (use i in auto)
                also have "... = yn i - 1 / real (Suc n)"
                  using i by auto
                also have "... \<le> f x"
                  using i(2) by(auto simp: En_def diff_less_eq order_less_le_trans intro!: order.strict_implies_order)
                finally show ?thesis . 
              qed
            next
              show "integrable N (\<lambda>x. \<Sum>i\<le>L. (yn i - 1 / real (Suc n)) * indicat_real (En i) x)"
                using emeasure_En_fin by fastforce
            qed(use g7 f in auto)
            finally show ?thesis .
          qed
          thus ?thesis
            by fastforce
        qed
        finally show ?thesis .
      qed
      show ?thesis
      proof(rule Lim_bounded2)
        show "(\<lambda>n. (\<integral>x. f x \<partial>N) + 1 / real (Suc n) * (2 * measure N ?K + 1 / real (Suc n) + 2 * B + 1)) \<longlonglongrightarrow> (\<integral>x. f x \<partial>N)"
          apply(rule tendsto_add[where b=0,simplified])
           apply simp
          apply(rule tendsto_mult[where a = "0::real", simplified,where b="2 * measure N ?K + 2 * B + 1"])
           apply(intro LIMSEQ_Suc[OF lim_inverse_n'] tendsto_add[OF tendsto_const,of _ 0,simplified] tendsto_add[OF _ tendsto_const])+
          done
      qed(use 1 in auto)
    qed
    fix f
    assume f: "?iscont f" "?csupp f"
    show "\<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N)"
    proof(rule antisym)
      have "- \<phi> (\<lambda>x\<in>topspace X. f x) = \<phi> (\<lambda>x\<in>topspace X. - f x)"
        using f by(auto intro!: \<phi>diff[of "\<lambda>x. 0" f,simplified \<phi>_0,simplified,symmetric])
      also have "... \<le> (\<integral>x. - f x \<partial>N)"
        by(intro 1) (auto simp: f)
      also have "... = - (\<integral>x. f x \<partial>N)"
        by simp
      finally show "\<phi> (\<lambda>x\<in>topspace X. f x) \<ge> (\<integral>x. f x \<partial>N)"
        by linarith
    qed(intro f 1)
  qed
  show ?thesis
    apply(intro exI[where x=M] ex1I[where a=N] rep_measures_real_unique[OF lh(1,2),of _ N])
    using sets_N g1 g2 g3 g4 g5 g6 g7 g8 by auto
qed

subsection \<open> Riesz Representation Theorem for Complex Numbers\<close>
theorem Riesz_representation_complex_complete:
  fixes X :: "'a topology" and \<phi> :: "('a \<Rightarrow> complex) \<Rightarrow> complex"
  assumes lh:"locally_compact_space X" "Hausdorff_space X"
    and plf:"positive_linear_functional_on_CX X \<phi>"
    shows "\<exists>M. \<exists>!N. sets N = M \<and> subalgebra N (borel_of X)
         \<and> (\<forall>A\<in>sets N. emeasure N A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N C))
         \<and> (\<forall>A. openin X A \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))
         \<and> (\<forall>A\<in>sets N. emeasure N A < \<infinity> \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))
         \<and> (\<forall>K. compactin X K \<longrightarrow> emeasure N K < \<infinity>)
         \<and> (\<forall>f. continuous_map X euclidean f \<longrightarrow> f has_compact_support_on X \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))
         \<and> (\<forall>f. continuous_map X euclidean f \<longrightarrow> f has_compact_support_on X \<longrightarrow> complex_integrable N f)
         \<and> complete_measure N"
proof -
  let ?\<phi>' = "\<lambda>f. Re (\<phi> (\<lambda>x\<in>topspace X. complex_of_real (f x)))"
  from  Riesz_representation_real_complete[OF lh pos_lin_functional_on_CX_complex_decompose_plf[OF plf]]
  obtain M N where MN:
   "sets N = M" "subalgebra N (borel_of X)" "(\<forall>A\<in>sets N. emeasure N A = \<Sqinter> (emeasure N ` {C. openin X C \<and> A \<subseteq> C}))"
    "(\<forall>A. openin X A \<longrightarrow> emeasure N A = \<Squnion> (emeasure N ` {K. compactin X K \<and> K \<subseteq> A}))"
     "(\<forall>A\<in>sets N. emeasure N A < \<infinity> \<longrightarrow> emeasure N A = \<Squnion> (emeasure N ` {K. compactin X K \<and> K \<subseteq> A}))"
    "(\<forall>K. compactin X K \<longrightarrow> emeasure N K < \<infinity>)"
    "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> f has_compact_support_on X \<Longrightarrow> ?\<phi>' (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N)"
    "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> f has_compact_support_on X \<Longrightarrow> integrable N f" "complete_measure N"
    by fastforce
  have MN1: "complex_integrable N f" if f:"continuous_map X euclidean f" "f has_compact_support_on X" for f
    using f unfolding complex_integrable_iff
    by(auto intro!: MN(8))
  have MN2: "\<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N)"
    if f:"continuous_map X euclidean f" "f has_compact_support_on X" for f
  proof -
    have "\<phi> (\<lambda>x\<in>topspace X. f x)
          = complex_of_real (?\<phi>' (\<lambda>x\<in>topspace X. Re (f x))) + \<i> * complex_of_real (?\<phi>' (\<lambda>x\<in>topspace X. Im (f x)))"
      using f by(intro pos_lin_functional_on_CX_complex_decompose[OF plf])
    also have "... = complex_of_real (\<integral>x. Re (f x) \<partial>N) + \<i> * complex_of_real (\<integral>x. Im (f x) \<partial>N)"
    proof -
      have *:"?\<phi>' (\<lambda>x\<in>topspace X. Re (f x)) = (\<integral>x. Re (f x) \<partial>N)"
        using f by(intro MN(7)) auto
      have **:"?\<phi>' (\<lambda>x\<in>topspace X. Im (f x)) = (\<integral>x. Im (f x) \<partial>N)"
        using f by(intro MN(7)) auto
      show ?thesis
       unfolding * ** ..
    qed
    also have "... = complex_of_real (Re (\<integral>x. f x \<partial>N)) + \<i> * complex_of_real (Im (\<integral>x. f x \<partial>N))"
      by(simp add: integral_Im[OF MN1[OF that]] integral_Re[OF MN1[OF that]])
    also have "... = (\<integral>x. f x \<partial>N)"
      using complex_eq by auto
    finally show ?thesis .
  qed
  show ?thesis
    apply(intro exI[where x=M] ex1I[where a=N] rep_measures_complex_unique[OF lh])
    using MN(1-6,9) MN1 MN2
    by auto
qed

subsection \<open> Other Forms of the Theorem \<close>
text \<open> In the case when the representation measure is on $X$.\<close>
theorem Riesz_representation_real:
  assumes lh:"locally_compact_space X" "Hausdorff_space X"
    and "positive_linear_functional_on_CX X \<phi>"
    shows "\<exists>!N. sets N = sets (borel_of X)
         \<and> (\<forall>A\<in>sets N. emeasure N A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N C))
         \<and> (\<forall>A. openin X A \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))
         \<and> (\<forall>A\<in>sets N. emeasure N A < \<infinity> \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))
         \<and> (\<forall>K. compactin X K \<longrightarrow> emeasure N K < \<infinity>)
         \<and> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow> f has_compact_support_on X \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))
         \<and> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow> f has_compact_support_on X \<longrightarrow> integrable N f)"
proof -
  from Riesz_representation_real_complete[OF assms] obtain M N where MN:
   "sets N = M" "subalgebra N (borel_of X)" "(\<forall>A\<in>sets N. emeasure N A = \<Sqinter> (emeasure N ` {C. openin X C \<and> A \<subseteq> C}))"
    "(\<forall>A. openin X A \<longrightarrow> emeasure N A = \<Squnion> (emeasure N ` {K. compactin X K \<and> K \<subseteq> A}))"
    "(\<forall>A\<in>sets N. emeasure N A < \<infinity> \<longrightarrow> emeasure N A = \<Squnion> (emeasure N ` {K. compactin X K \<and> K \<subseteq> A}))"
    "(\<forall>K. compactin X K \<longrightarrow> emeasure N K < \<infinity>)"
    "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> f has_compact_support_on X \<Longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N)"
    "\<And>f. continuous_map X euclideanreal f \<Longrightarrow> f has_compact_support_on X \<Longrightarrow> integrable N f" "complete_measure N"
    by fastforce

  define N' where "N' \<equiv> restr_to_subalg N (borel_of X)"
  have g1: "sets N' = sets (borel_of X)" (is ?g1)
   and g2: "\<forall>A\<in>sets N'. emeasure N' A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N' C)" (is ?g2)
   and g3: "\<forall>A. openin X A \<longrightarrow> emeasure N' A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N' K)" (is ?g3)
   and g4: "\<forall>A\<in>sets N'. emeasure N' A < \<infinity> \<longrightarrow> emeasure N' A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N' K)" (is ?g4)
   and g5: "\<forall>K. compactin X K \<longrightarrow> emeasure N' K < \<infinity>" (is ?g5)
   and g6: "\<forall>f. continuous_map X euclideanreal f \<longrightarrow> f has_compact_support_on X \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N')" (is ?g6)
   and g7: "\<forall>f. continuous_map X euclideanreal f \<longrightarrow> f has_compact_support_on X \<longrightarrow> integrable N' f" (is ?g7)
  proof -
    have sets_N': "sets N' = borel_of X"
      using sets_restr_to_subalg[OF MN(2)] by(auto simp: N'_def)
    have emeasure_N': "\<And>A. A \<in> sets N' \<Longrightarrow> emeasure N' A = emeasure N A"
      by (simp add: MN(2) N'_def emeasure_restr_to_subalg sets_restr_to_subalg)
    have setsN'[measurable]: "\<And>A. openin X A \<Longrightarrow> A \<in> sets N'" "\<And>A. compactin X A \<Longrightarrow> A \<in> sets N'"
      by(auto simp: sets_N' dest: borel_of_open borel_of_closed[OF compactin_imp_closedin[OF lh(2)]])
    have sets_N'_sets_N[simp]: "\<And>A. A \<in> sets N' \<Longrightarrow> A \<in> sets N"
      using MN(2) sets_N' subalgebra_def by blast
    show ?g1
      by (simp add: MN(2) N'_def sets_restr_to_subalg)
    show ?g2
      using MN(3) by(auto simp: emeasure_N')
    show ?g3
      using MN(4) by(auto simp: emeasure_N')
    show ?g4
      using MN(5) by(auto simp: emeasure_N')
    show ?g5
      using MN(6) by(auto simp: emeasure_N')
    show ?g6 ?g7
    proof safe
      fix f
      assume f:"continuous_map X euclideanreal f" "f has_compact_support_on X"
      then have [measurable]: "f \<in> borel_measurable (borel_of X)"
        by (simp add: continuous_lower_semicontinuous lower_semicontinuous_map_measurable)
      from MN(7,8) f show "\<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N')" "integrable N' f"
        by(auto simp: N'_def integral_subalgebra2[OF MN(2)] intro!: integrable_in_subalg[OF MN(2)])
    qed
  qed
  have g8: "\<And>L. sets L = sets (borel_of X) \<Longrightarrow> subalgebra L (borel_of X)"
    by (metis sets_eq_imp_space_eq subalgebra_def subset_refl)

  show ?thesis
    apply(intro ex1I[where a=N'] rep_measures_real_unique[OF lh])
    using g1 g2 g3 g4 g5 g6 g7 g8 by auto
qed

theorem Riesz_representation_complex:
  fixes X :: "'a topology" and \<phi> :: "('a \<Rightarrow> complex) \<Rightarrow> complex"
  assumes lh:"locally_compact_space X" "Hausdorff_space X"
    and "positive_linear_functional_on_CX X \<phi>"
    shows "\<exists>!N. sets N = sets (borel_of X)
         \<and> (\<forall>A\<in>sets N. emeasure N A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N C))
         \<and> (\<forall>A. openin X A \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))
         \<and> (\<forall>A\<in>sets N. emeasure N A < \<infinity> \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))
         \<and> (\<forall>K. compactin X K \<longrightarrow> emeasure N K < \<infinity>)
         \<and> (\<forall>f. continuous_map X euclidean f \<longrightarrow> f has_compact_support_on X \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))
         \<and> (\<forall>f. continuous_map X euclidean f \<longrightarrow> f has_compact_support_on X \<longrightarrow> complex_integrable N f)"
proof -
  from Riesz_representation_complex_complete[OF assms] obtain M N where MN:
   "sets N = M" "subalgebra N (borel_of X)" "(\<forall>A\<in>sets N. emeasure N A = \<Sqinter> (emeasure N ` {C. openin X C \<and> A \<subseteq> C}))"
    "(\<forall>A. openin X A \<longrightarrow> emeasure N A = \<Squnion> (emeasure N ` {K. compactin X K \<and> K \<subseteq> A}))"
    "(\<forall>A\<in>sets N. emeasure N A < \<infinity> \<longrightarrow> emeasure N A = \<Squnion> (emeasure N ` {K. compactin X K \<and> K \<subseteq> A}))"
    "(\<forall>K. compactin X K \<longrightarrow> emeasure N K < \<infinity>)"
    "\<And>f. continuous_map X euclidean f \<Longrightarrow> f has_compact_support_on X \<Longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N)"
    "\<And>f. continuous_map X euclidean f \<Longrightarrow> f has_compact_support_on X \<Longrightarrow> complex_integrable N f" "complete_measure N"
    by fastforce

  define N' where "N' \<equiv> restr_to_subalg N (borel_of X)"
  have g1: "sets N' = sets (borel_of X)" (is ?g1)
   and g2: "\<forall>A\<in>sets N'. emeasure N' A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N' C)" (is ?g2)
   and g3: "\<forall>A. openin X A \<longrightarrow> emeasure N' A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N' K)" (is ?g3)
   and g4: "\<forall>A\<in>sets N'. emeasure N' A < \<infinity> \<longrightarrow> emeasure N' A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N' K)" (is ?g4)
   and g5: "\<forall>K. compactin X K \<longrightarrow> emeasure N' K < \<infinity>" (is ?g5)
   and g6: "\<forall>f. continuous_map X euclidean f \<longrightarrow> f has_compact_support_on X \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N')" (is ?g6)
   and g7: "\<forall>f. continuous_map X euclidean f \<longrightarrow> f has_compact_support_on X \<longrightarrow> complex_integrable N' f" (is ?g7)
  proof -
    have sets_N': "sets N' = borel_of X"
      using sets_restr_to_subalg[OF MN(2)] by(auto simp: N'_def)
    have emeasure_N': "\<And>A. A \<in> sets N' \<Longrightarrow> emeasure N' A = emeasure N A"
      by (simp add: MN(2) N'_def emeasure_restr_to_subalg sets_restr_to_subalg)
    have setsN'[measurable]: "\<And>A. openin X A \<Longrightarrow> A \<in> sets N'" "\<And>A. compactin X A \<Longrightarrow> A \<in> sets N'"
      by(auto simp: sets_N' dest: borel_of_open borel_of_closed[OF compactin_imp_closedin[OF lh(2)]])
    have sets_N'_sets_N[simp]: "\<And>A. A \<in> sets N' \<Longrightarrow> A \<in> sets N"
      using MN(2) sets_N' subalgebra_def by blast
    show ?g1
      by (simp add: MN(2) N'_def sets_restr_to_subalg)
    show ?g2
      using MN(3) by(auto simp: emeasure_N')
    show ?g3
      using MN(4) by(auto simp: emeasure_N')
    show ?g4
      using MN(5) by(auto simp: emeasure_N')
    show ?g5
      using MN(6) by(auto simp: emeasure_N')
    show ?g6 ?g7
    proof safe
      fix f :: "_ \<Rightarrow> complex"
      assume f:"continuous_map X euclidean f" "f has_compact_support_on X"
      then have [measurable]: "f \<in> borel_measurable (borel_of X)"
        by (metis borel_of_euclidean continuous_map_measurable)
      show "\<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N')" "integrable N' f"
        using MN(7,8) f by(auto simp: N'_def integral_subalgebra2[OF MN(2)] intro!: integrable_in_subalg[OF MN(2)])
    qed
  qed
  have g8: "\<And>L. sets L = sets (borel_of X) \<Longrightarrow> subalgebra L (borel_of X)"
    by (metis sets_eq_imp_space_eq subalgebra_def subset_refl)

  show ?thesis
    apply(intro ex1I[where a=N'] rep_measures_complex_unique[OF lh])
    using g1 g2 g3 g4 g5 g6 g7 g8 by auto
qed

subsubsection \<open> Theorem for Compact Hausdorff Spaces \<close>
theorem Riesz_representation_real_compact_Hausdorff:
  fixes X :: "'a topology" and \<phi> :: "('a \<Rightarrow> real) \<Rightarrow> real"
  assumes lh:"compact_space X" "Hausdorff_space X"
    and "positive_linear_functional_on_CX X \<phi>"
    shows "\<exists>!N. sets N = sets (borel_of X) \<and> finite_measure N
         \<and> (\<forall>A\<in>sets N. emeasure N A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N C))
         \<and> (\<forall>A. openin X A \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))
         \<and> (\<forall>A\<in>sets N. emeasure N A < \<infinity> \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))
         \<and> (\<forall>K. compactin X K \<longrightarrow> emeasure N K < \<infinity>)
         \<and> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))
         \<and> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow> integrable N f)"
proof -
  have [simp]: "compactin X (X closure_of A)" for A
    by (simp add: closedin_compact_space lh(1))
  from Riesz_representation_real[OF compact_imp_locally_compact_space[OF lh(1)] assms(2,3)] obtain N where N:
  "sets N = sets (borel_of X)"
  "(\<forall>A\<in>sets N. emeasure N A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N C))"
  "(\<forall>A. openin X A \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))"
  "(\<forall>A\<in>sets N. emeasure N A < \<infinity> \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))"
  "(\<forall>K. compactin X K \<longrightarrow> emeasure N K < \<infinity>)"
  "(\<forall>f. continuous_map X euclideanreal f \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
  "(\<forall>f. continuous_map X euclideanreal f \<longrightarrow> integrable N f)"
    by(fastforce simp: assms(1))
  have space_N:"space N = topspace X"
    by (simp add: N(1) sets_eq_imp_space_eq space_borel_of)
  have fin:"finite_measure N"
    using N(5)[rule_format,of "topspace X"] lh(1)
    by(auto intro!: finite_measureI simp: space_N compact_space_def)
  have 1:"\<And>L. sets L = sets (borel_of X) \<Longrightarrow> subalgebra L (borel_of X)"
    by (metis sets_eq_imp_space_eq subalgebra_def subset_refl)
  show ?thesis
    by(intro ex1I[where a=N] rep_measures_real_unique[OF compact_imp_locally_compact_space[OF lh(1)] lh(2)])
      (use N fin 1 in auto)
qed

theorem Riesz_representation_complex_compact_Hausdorff:
  fixes X :: "'a topology" and \<phi> :: "('a \<Rightarrow> complex) \<Rightarrow> complex"
  assumes lh:"compact_space X" "Hausdorff_space X"
    and "positive_linear_functional_on_CX X \<phi>"
    shows "\<exists>!N. sets N = sets (borel_of X) \<and> finite_measure N
         \<and> (\<forall>A\<in>sets N. emeasure N A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N C))
         \<and> (\<forall>A. openin X A \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))
         \<and> (\<forall>A\<in>sets N. emeasure N A < \<infinity> \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))
         \<and> (\<forall>K. compactin X K \<longrightarrow> emeasure N K < \<infinity>)
         \<and> (\<forall>f. continuous_map X euclidean f \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))
         \<and> (\<forall>f. continuous_map X euclidean f \<longrightarrow> complex_integrable N f)"
proof -
  have [simp]: "compactin X (X closure_of A)" for A
    by (simp add: closedin_compact_space lh(1))
  from Riesz_representation_complex[OF compact_imp_locally_compact_space[OF lh(1)] assms(2,3)] obtain N where N:
  "sets N = sets (borel_of X)"
  "(\<forall>A\<in>sets N. emeasure N A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N C))"
  "(\<forall>A. openin X A \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))"
  "(\<forall>A\<in>sets N. emeasure N A < \<infinity> \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))"
  "(\<forall>K. compactin X K \<longrightarrow> emeasure N K < \<infinity>)"
  "(\<forall>f. continuous_map X euclidean f \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
  "(\<forall>f. continuous_map X euclidean f \<longrightarrow> complex_integrable N f)"
    by (fastforce simp: lh(1))
  have space_N:"space N = topspace X"
    by (simp add: N(1) sets_eq_imp_space_eq space_borel_of)
  have fin:"finite_measure N"
    using N(5)[rule_format,of "topspace X"] lh(1)
    by(auto intro!: finite_measureI simp: space_N compact_space_def)
  have 1:"\<And>L. sets L = sets (borel_of X) \<Longrightarrow> subalgebra L (borel_of X)"
    by (metis sets_eq_imp_space_eq subalgebra_def subset_refl)
  show ?thesis
    by(intro ex1I[where a=N] rep_measures_complex_unique[OF compact_imp_locally_compact_space[OF lh(1)] lh(2)])
      (use N fin 1 in auto)
qed

subsubsection \<open> Theorem for Compact Metrizable Spaces\<close>
theorem Riesz_representation_real_compact_metrizable:
  fixes X :: "'a topology" and \<phi> :: "('a \<Rightarrow> real) \<Rightarrow> real"
  assumes lh:"compact_space X" "metrizable_space X"
    and plf:"positive_linear_functional_on_CX X \<phi>"
    shows "\<exists>!N. sets N = sets (borel_of X) \<and> finite_measure N
           \<and> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
proof -
  have hd: "Hausdorff_space X"
    by (simp add: lh(2) metrizable_imp_Hausdorff_space)

  from Riesz_representation_real_compact_Hausdorff[OF lh(1) hd plf] obtain N where N:
  "sets N = sets (borel_of X)" "finite_measure N"
  "(\<forall>A\<in>sets N. emeasure N A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N C))"
  "(\<forall>A. openin X A \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))"
  "(\<forall>A\<in>sets N. emeasure N A < \<infinity> \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))"
  "(\<forall>K. compactin X K \<longrightarrow> emeasure N K < \<infinity>)"
  "(\<forall>f. continuous_map X euclideanreal f \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
  "(\<forall>f. continuous_map X euclideanreal f \<longrightarrow> integrable N f)"
    by fastforce
  then have tight_on_N:"tight_on X N"
    using finite_measure.tight_on_compact_space lh(1) lh(2) by metis

  show ?thesis
  proof(safe intro!: ex1I[where a=N])
    fix M
    assume M:"sets M = sets (borel_of X)" "finite_measure M" "(\<forall>f. continuous_map X euclideanreal f \<longrightarrow> \<phi> (restrict f (topspace X)) = integral\<^sup>L M f)"
    then have "tight_on X M"
      using finite_measure.tight_on_compact_space lh(1) lh(2) by blast
    thus "M = N"
      using N(7) M(3) by(auto intro!: finite_tight_measure_eq[OF compact_imp_locally_compact_space[OF lh(1)] lh(2)] tight_on_N)
  qed(use N in auto)
qed

theorem Riesz_representation_real_compact_metrizable_le1:
  fixes X :: "'a topology" and \<phi> :: "('a \<Rightarrow> real) \<Rightarrow> real"
  assumes lh:"compact_space X" "metrizable_space X"
    and plf:"positive_linear_functional_on_CX X \<phi>"
    shows "\<exists>!N. sets N = sets (borel_of X) \<and> finite_measure N
           \<and> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow> f \<in> topspace X \<rightarrow> {0..1} \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
proof -
  have hd: "Hausdorff_space X"
    by (simp add: lh(2) metrizable_imp_Hausdorff_space)

  from Riesz_representation_real_compact_Hausdorff[OF lh(1) hd plf] obtain N where N:
  "sets N = sets (borel_of X)" "finite_measure N"
  "(\<forall>A\<in>sets N. emeasure N A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N C))"
  "(\<forall>A. openin X A \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))"
  "(\<forall>A\<in>sets N. emeasure N A < \<infinity> \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))"
  "(\<forall>K. compactin X K \<longrightarrow> emeasure N K < \<infinity>)"
  "(\<forall>f. continuous_map X euclideanreal f \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
  "(\<forall>f. continuous_map X euclideanreal f \<longrightarrow> integrable N f)"
    by fastforce
  then have tight_on_N:"tight_on X N"
    using finite_measure.tight_on_compact_space lh(1) lh(2) by metis

  show ?thesis
  proof(safe intro!: ex1I[where a=N])
    fix M
    assume M:"sets M = sets (borel_of X)" "finite_measure M" "(\<forall>f. continuous_map X euclideanreal f \<longrightarrow> f \<in> topspace X \<rightarrow> {0..1} \<longrightarrow> \<phi> (restrict f (topspace X)) = integral\<^sup>L M f)"
    then have "tight_on X M"
      using finite_measure.tight_on_compact_space lh(1) lh(2) by blast
    thus "M = N"
      using N(7) M(3) by(auto intro!: finite_tight_measure_eq[OF compact_imp_locally_compact_space[OF lh(1)] lh(2)] tight_on_N)
  qed(use N in auto)
qed

theorem Riesz_representation_complex_compact_metrizable:
  fixes X :: "'a topology" and \<phi> :: "('a \<Rightarrow> complex) \<Rightarrow> complex"
  assumes lh:"compact_space X" "metrizable_space X"
    and plf:"positive_linear_functional_on_CX X \<phi>"
    shows "\<exists>!N. sets N = sets (borel_of X) \<and> finite_measure N
           \<and> (\<forall>f. continuous_map X euclidean f \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
proof-
  have hd: "Hausdorff_space X"
    by (simp add: lh(2) metrizable_imp_Hausdorff_space)

  from Riesz_representation_complex_compact_Hausdorff[OF lh(1) hd plf] obtain N where N:
  "sets N = sets (borel_of X)" "finite_measure N"
  "(\<forall>A\<in>sets N. emeasure N A = (\<Sqinter>C\<in>{C. openin X C \<and> A \<subseteq> C}. emeasure N C))"
  "(\<forall>A. openin X A \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))"
  "(\<forall>A\<in>sets N. emeasure N A < \<infinity> \<longrightarrow> emeasure N A = (\<Squnion>K\<in>{K. compactin X K \<and> K \<subseteq> A}. emeasure N K))"
  "(\<forall>K. compactin X K \<longrightarrow> emeasure N K < \<infinity>)"
  "(\<forall>f. continuous_map X euclidean f \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
  "(\<forall>f. continuous_map X euclidean f \<longrightarrow> complex_integrable N f)"
    by fastforce
  then have tight_on_N:"tight_on X N"
    using finite_measure.tight_on_compact_space lh(1) lh(2) by metis

  show ?thesis
  proof(safe intro!: ex1I[where a=N])
    fix M
    assume M:"sets M = sets (borel_of X)" "finite_measure M" "(\<forall>f. continuous_map X euclidean f \<longrightarrow> \<phi> (restrict f (topspace X)) = (\<integral>x. f x \<partial>M))"
    then have tight_on_M:"tight_on X M"
      using finite_measure.tight_on_compact_space lh(1) lh(2) by blast
    have "(\<integral>x. f x \<partial>N) = (\<integral>x. f x \<partial>M)" if f:"continuous_map X euclideanreal f" for f
    proof -
      have "(\<integral>x. f x \<partial>N) = Re (\<integral>x. complex_of_real (f x) \<partial>N)"
        by simp
      also have "... = Re (\<phi> (\<lambda>x\<in>topspace X. complex_of_real (f x)))"
        by(intro arg_cong[where f=Re] N(7)[rule_format,symmetric]) (simp add: f)
      also have "... = Re (\<integral>x. complex_of_real (f x) \<partial>M)"
        by(intro arg_cong[where f=Re] M(3)[rule_format]) (simp add: f)
      also have "... = (\<integral>x. f x \<partial>M)"
        by simp
      finally show ?thesis .
    qed
    thus "M = N"
      by(auto intro!: finite_tight_measure_eq[OF compact_imp_locally_compact_space[OF lh(1)] lh(2)] tight_on_N tight_on_M)
  qed(use N in auto)
qed

theorem Riesz_representation_real_compact_metrizable_subprob:
  fixes X :: "'a topology" and \<phi> :: "('a \<Rightarrow> real) \<Rightarrow> real"
  assumes lh:"compact_space X" "metrizable_space X"
    and plf:"positive_linear_functional_on_CX X \<phi>"
      and le1: "\<phi> (\<lambda>x\<in>topspace X. 1) \<le> 1" and ne: "X \<noteq> trivial_topology"
    shows "\<exists>!N. sets N = sets (borel_of X) \<and> subprob_space N
           \<and> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
proof -
  from Riesz_representation_real_compact_metrizable[OF assms(1-3)]
  obtain N where N: "sets N = sets (borel_of X)" "finite_measure N" "(\<forall>f. continuous_map X euclideanreal f \<longrightarrow>  \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
    "\<And>M. sets M = sets (borel_of X) \<Longrightarrow> finite_measure M \<Longrightarrow> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow>  \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>M)) \<Longrightarrow> M = N"
    by fastforce
  then interpret finite_measure N
    by blast
  have subN:"subprob_space N"
  proof
    have "measure N (space N) = (\<integral>x. 1 \<partial>N)"
      by simp
    also have "... = \<phi> (\<lambda>x\<in>topspace X. 1)"
      by(intro N(3)[rule_format,symmetric]) simp
    also have "... \<le> 1"
      by fact
    finally show "emeasure N (space N) \<le> 1"
      by (simp add: emeasure_eq_measure)
  next
    show "space N \<noteq> {}"
      using sets_eq_imp_space_eq[OF N(1)] ne by(auto simp: space_borel_of)
  qed
  show ?thesis
    using N(4)[OF _ subprob_space.axioms(1)] subN N(1,3) by(auto intro!: ex1I[where a=N])
qed

theorem Riesz_representation_real_compact_metrizable_subprob_le1:
  fixes X :: "'a topology" and \<phi> :: "('a \<Rightarrow> real) \<Rightarrow> real"
  assumes lh:"compact_space X" "metrizable_space X"
    and plf:"positive_linear_functional_on_CX X \<phi>"
      and le1: "\<phi> (\<lambda>x\<in>topspace X. 1) \<le> 1" and ne: "X \<noteq> trivial_topology"
    shows "\<exists>!N. sets N = sets (borel_of X) \<and> subprob_space N
           \<and> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow> f \<in> topspace X \<rightarrow> {0..1} \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
proof -
  from Riesz_representation_real_compact_metrizable_le1[OF lh plf]
  obtain N where N: "sets N = sets (borel_of X)" "finite_measure N" "(\<forall>f. continuous_map X euclideanreal f \<longrightarrow> f \<in> topspace X \<rightarrow> {0..1} \<longrightarrow>  \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
    "\<And>M. sets M = sets (borel_of X) \<Longrightarrow> finite_measure M \<Longrightarrow> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow>  f \<in> topspace X \<rightarrow> {0..1} \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>M)) \<Longrightarrow> M = N"
    by fastforce
  then interpret finite_measure N
    by blast
  have subN:"subprob_space N"
  proof
    have "measure N (space N) = (\<integral>x. 1 \<partial>N)"
      by simp
    also have "... = \<phi> (\<lambda>x\<in>topspace X. 1)"
      by(intro N(3)[rule_format,symmetric]) simp_all
    also have "... \<le> 1"
      by fact
    finally show "emeasure N (space N) \<le> 1"
      by (simp add: emeasure_eq_measure)
  next
    show "space N \<noteq> {}"
      using sets_eq_imp_space_eq[OF N(1)] ne by(auto simp: space_borel_of)
  qed
  show ?thesis
    using N(4)[OF _ subprob_space.axioms(1)] subN N(1,3) by(auto intro!: ex1I[where a=N])
qed

theorem Riesz_representation_real_compact_metrizable_prob:
  fixes X :: "'a topology" and \<phi> :: "('a \<Rightarrow> real) \<Rightarrow> real"
  assumes lh:"compact_space X" "metrizable_space X"
    and plf:"positive_linear_functional_on_CX X \<phi>"
      and "\<phi> (\<lambda>x\<in>topspace X. 1) = 1"
    shows "\<exists>!N. sets N = sets (borel_of X) \<and> prob_space N
           \<and> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
proof -
  from Riesz_representation_real_compact_metrizable[OF lh plf]
  obtain N where N: "sets N = sets (borel_of X)" "finite_measure N" "(\<forall>f. continuous_map X euclideanreal f \<longrightarrow>  \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
    "\<And>M. sets M = sets (borel_of X) \<Longrightarrow> finite_measure M \<Longrightarrow> (\<forall>f. continuous_map X euclideanreal f \<longrightarrow>  \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>M)) \<Longrightarrow> M = N"
    by fastforce
  then interpret finite_measure N
    by blast
  have probN:"prob_space N"
  proof
    have "measure N (space N) = (\<integral>x. 1 \<partial>N)"
      by simp
    also have "... = \<phi> (\<lambda>x\<in>topspace X. 1)"
      by(intro N(3)[rule_format,symmetric]) simp
    also have "... = 1"
      by fact
    finally show "emeasure N (space N) = 1"
      by (simp add: emeasure_eq_measure)
  qed
  show ?thesis
    using N(4)[OF _ prob_space.finite_measure] probN N(1,3) by(auto intro!: ex1I[where a=N])
qed

theorem Riesz_representation_complex_compact_metrizable_subprob:
  fixes X :: "'a topology" and \<phi> :: "('a \<Rightarrow> complex) \<Rightarrow> complex"
  assumes lh:"compact_space X" "metrizable_space X"
    and plf:"positive_linear_functional_on_CX X \<phi>"
      and le1: "Re (\<phi> (\<lambda>x\<in>topspace X. 1)) \<le> 1" and ne: "X \<noteq> trivial_topology"
    shows "\<exists>!N. sets N = sets (borel_of X) \<and> subprob_space N
           \<and> (\<forall>f. continuous_map X euclidean f \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
proof -
  from Riesz_representation_complex_compact_metrizable[OF lh plf]
  obtain N where N: "sets N = sets (borel_of X)" "finite_measure N" "(\<forall>f. continuous_map X euclidean f \<longrightarrow>  \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
    "\<And>M. sets M = sets (borel_of X) \<Longrightarrow> finite_measure M \<Longrightarrow> (\<forall>f. continuous_map X euclidean f \<longrightarrow>  \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>M)) \<Longrightarrow> M = N"
    by fastforce
  then interpret finite_measure N
    by blast
  have subN:"subprob_space N"
  proof
    have "measure N (space N) = (\<integral>x. 1 \<partial>N)"
      by simp
    also have "... = Re (\<integral>x. 1 \<partial>N)"
      by simp
    also have "... = Re (\<phi> (\<lambda>x\<in>topspace X. 1))"
      by(intro arg_cong[where f=Re] N(3)[rule_format,symmetric]) simp
    also have "... \<le> 1"
      by fact
    finally show "emeasure N (space N) \<le> 1"
      by (simp add: emeasure_eq_measure)
  next
    show "space N \<noteq> {}"
      using sets_eq_imp_space_eq[OF N(1)] ne by(auto simp: space_borel_of)
  qed
  show ?thesis
    using N(4)[OF _ subprob_space.axioms(1)] subN N(1,3) by(auto intro!: ex1I[where a=N])
qed

theorem Riesz_representation_complex_compact_metrizable_prob:
  fixes X :: "'a topology" and \<phi> :: "('a \<Rightarrow> complex) \<Rightarrow> complex"
  assumes lh:"compact_space X" "metrizable_space X"
    and plf:"positive_linear_functional_on_CX X \<phi>"
      and "Re (\<phi> (\<lambda>x\<in>topspace X. 1)) = 1"
    shows "\<exists>!N. sets N = sets (borel_of X) \<and> prob_space N
           \<and> (\<forall>f. continuous_map X euclidean f \<longrightarrow> \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
proof -
  from Riesz_representation_complex_compact_metrizable[OF lh plf]
  obtain N where N: "sets N = sets (borel_of X)" "finite_measure N" "(\<forall>f. continuous_map X euclidean f \<longrightarrow>  \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>N))"
    "\<And>M. sets M = sets (borel_of X) \<Longrightarrow> finite_measure M \<Longrightarrow> (\<forall>f. continuous_map X euclidean f \<longrightarrow>  \<phi> (\<lambda>x\<in>topspace X. f x) = (\<integral>x. f x \<partial>M)) \<Longrightarrow> M = N"
    by fastforce
  then interpret finite_measure N
    by blast
  have probN:"prob_space N"
  proof
    have "measure N (space N) = (\<integral>x. 1 \<partial>N)"
      by simp
    also have "... = Re (\<integral>x. 1 \<partial>N)"
      by simp
    also have "... = Re (\<phi> (\<lambda>x\<in>topspace X. 1))"
      by(intro arg_cong[where f=Re] N(3)[rule_format,symmetric]) simp
    also have "... = 1"
      by fact
    finally show "emeasure N (space N) = 1"
      by (simp add: emeasure_eq_measure)
  qed
  show ?thesis
    using N(4)[OF _ prob_space.finite_measure] probN N(1,3) by(auto intro!: ex1I[where a=N])
qed

end