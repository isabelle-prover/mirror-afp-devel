section \<open>Möbius transforms and the modular group\<close>
theory Modular_Group
imports
  "HOL-Complex_Analysis.Complex_Analysis" 
  "HOL-Number_Theory.Number_Theory"
begin

subsection \<open>Basic properties of Möbius transforms\<close>

lemma moebius_uminus [simp]: "moebius (-a) (-b) (-c) (-d) = moebius a b c d"
  by (simp add: fun_eq_iff moebius_def divide_simps) (simp add: algebra_simps add_eq_0_iff2)

lemma moebius_uminus': "moebius (-a) b c d = moebius a (-b) (-c) (-d)"
  by (simp add: fun_eq_iff moebius_def divide_simps) (simp add: algebra_simps add_eq_0_iff2)

lemma moebius_diff_eq:
  fixes a b c d :: "'a :: field"
  defines "f \<equiv> moebius a b c d"
  assumes *: "c = 0 \<or> z \<noteq> -d / c \<and> w \<noteq> -d / c"
  shows   "f w - f z = (a * d - b * c) / ((c * w + d) * (c * z + d)) * (w - z)"
  using * by (auto simp: moebius_def divide_simps f_def add_eq_0_iff)
             (auto simp: algebra_simps)


lemma continuous_on_moebius [continuous_intros]:
  fixes a b c d :: "'a :: real_normed_field"
  assumes "c \<noteq> 0 \<or> d \<noteq> 0" "c = 0 \<or> -d / c \<notin> A"
  shows   "continuous_on A (moebius a b c d)"
  unfolding moebius_def
  by (intro continuous_intros) (use assms in \<open>auto simp: add_eq_0_iff\<close>)

lemma continuous_on_moebius' [continuous_intros]:
  fixes a b c d :: "'a :: real_normed_field"
  assumes "continuous_on A f" "c \<noteq> 0 \<or> d \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> c = 0 \<or> f z \<noteq> -d / c"
  shows   "continuous_on A (\<lambda>x. moebius a b c d (f x))"
proof -
  have "continuous_on A (moebius a b c d \<circ> f)" using assms
    by (intro continuous_on_compose assms continuous_on_moebius) force+
  thus ?thesis
    by (simp add: o_def)
qed

lemma holomorphic_on_moebius [holomorphic_intros]:
  assumes "c \<noteq> 0 \<or> d \<noteq> 0" "c = 0 \<or> -d / c \<notin> A"
  shows   "(moebius a b c d) holomorphic_on A"
  unfolding moebius_def
  by (intro holomorphic_intros) (use assms in \<open>auto simp: add_eq_0_iff\<close>)

lemma holomorphic_on_moebius' [holomorphic_intros]:
  assumes "f holomorphic_on A" "c \<noteq> 0 \<or> d \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> c = 0 \<or> f z \<noteq> -d / c"
  shows   "(\<lambda>x. moebius a b c d (f x)) holomorphic_on A"
proof -
  have "(moebius a b c d \<circ> f) holomorphic_on A" using assms
    by (intro holomorphic_on_compose assms holomorphic_on_moebius) force+
  thus ?thesis
    by (simp add: o_def)
qed

lemma analytic_on_moebius [analytic_intros]:
  assumes "c \<noteq> 0 \<or> d \<noteq> 0" "c = 0 \<or> -d / c \<notin> A"
  shows   "(moebius a b c d) analytic_on A"
  unfolding moebius_def
  by (intro analytic_intros) (use assms in \<open>auto simp: add_eq_0_iff\<close>)

lemma analytic_on_moebius' [analytic_intros]:
  assumes "f analytic_on A" "c \<noteq> 0 \<or> d \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> c = 0 \<or> f z \<noteq> -d / c"
  shows   "(\<lambda>x. moebius a b c d (f x)) analytic_on A"
proof -
  have "(moebius a b c d \<circ> f) analytic_on A" using assms
    by (intro analytic_on_compose assms analytic_on_moebius) force+
  thus ?thesis
    by (simp add: o_def)
qed

lemma moebius_has_field_derivative:
  assumes "c = 0 \<or> x \<noteq> -d / c" "c \<noteq> 0 \<or> d \<noteq> 0"
  shows   "(moebius a b c d has_field_derivative (a * d - b * c) / (c * x + d) ^ 2) (at x within A)"
  unfolding moebius_def
  apply (rule derivative_eq_intros refl)+
  using assms
   apply (auto simp: divide_simps add_eq_0_iff power2_eq_square split: if_splits)
  apply (auto simp: algebra_simps)?
  done



subsection \<open>Unimodular M\"obius transforms\<close>

text \<open>
  A unimodular M\"obius transform has integer coefficients and determinant \<open>\<plusminus>1\<close>.
\<close>
locale unimodular_moebius_transform =
  fixes a b c d :: int
  assumes unimodular: "a * d - b * c = 1"
begin

definition \<phi> :: "complex \<Rightarrow> complex" where 
  "\<phi> = moebius (of_int a) (of_int b) (of_int c) (of_int d)"

lemma cnj_\<phi>: "\<phi> (cnj z) = cnj (\<phi> z)"
  by (simp add: moebius_def \<phi>_def)

lemma Im_transform:
  "Im (\<phi> z) = Im z / norm (of_int c * z + of_int d) ^ 2"
proof -
  have "Im (\<phi> z) = Im z * of_int (a * d - b * c) /
                   ((real_of_int c * Re z + real_of_int d)\<^sup>2 + (real_of_int c * Im z)\<^sup>2)"
    by (simp add: \<phi>_def moebius_def Im_divide algebra_simps)
  also have "a * d - b * c = 1"
    using unimodular by simp
  also have "((real_of_int c * Re z + real_of_int d)\<^sup>2 + (real_of_int c * Im z)\<^sup>2) =
             norm (of_int c * z + of_int d) ^ 2"
    unfolding cmod_power2 by (simp add: power2_eq_square algebra_simps)
  finally show ?thesis
    by simp
qed

lemma Im_transform_pos_aux:
  assumes "Im z \<noteq> 0"
  shows   "of_int c * z + of_int d \<noteq> 0"
proof (cases "c = 0")
  case False
  hence "Im (of_int c * z + of_int d) \<noteq> 0"
    using assms by auto
  moreover have "Im 0 = 0"
    by simp
  ultimately show ?thesis
    by metis
next
  case True
  thus ?thesis using unimodular
    by auto
qed

lemma Im_transform_pos: "Im z > 0 \<Longrightarrow> Im (\<phi> z) > 0"
  using Im_transform_pos_aux[of z] by (auto simp: Im_transform)

lemma Im_transform_neg: "Im z < 0 \<Longrightarrow> Im (\<phi> z) < 0"
  using Im_transform_pos[of "cnj z"] by (simp add: cnj_\<phi>)

lemma Im_transform_zero_iff [simp]: "Im (\<phi> z) = 0 \<longleftrightarrow> Im z = 0"
  using Im_transform_pos_aux[of z] by (auto simp: Im_transform)

lemma Im_transform_pos_iff [simp]: "Im (\<phi> z) > 0 \<longleftrightarrow> Im z > 0"
  using Im_transform_pos[of z] Im_transform_neg[of z] Im_transform_zero_iff[of z]
  by (cases "Im z" "0 :: real" rule: linorder_cases) (auto simp del: Im_transform_zero_iff)

lemma Im_transform_neg_iff [simp]: "Im (\<phi> z) < 0 \<longleftrightarrow> Im z < 0"
  using Im_transform_pos_iff[of "cnj z"] by (simp add: cnj_\<phi>)

lemma Im_transform_nonneg_iff [simp]: "Im (\<phi> z) \<ge> 0 \<longleftrightarrow> Im z \<ge> 0"
  using Im_transform_neg_iff[of z] by linarith

lemma Im_transform_nonpos_iff [simp]: "Im (\<phi> z) \<le> 0 \<longleftrightarrow> Im z \<le> 0"
  using Im_transform_pos_iff[of z] by linarith  

lemma transform_in_reals_iff [simp]: "\<phi> z \<in> \<real> \<longleftrightarrow> z \<in> \<real>"
  using Im_transform_zero_iff[of z] by (auto simp: complex_is_Real_iff)

end


lemma Im_one_over_neg_iff [simp]: "Im (1 / z) < 0 \<longleftrightarrow> Im z > 0"
proof -
  interpret unimodular_moebius_transform 0 1 "-1" 0
    by standard auto
  show ?thesis
    using Im_transform_pos_iff[of z] by (simp add: \<phi>_def moebius_def)
qed


locale inverse_unimodular_moebius_transform = unimodular_moebius_transform
begin

sublocale inv: unimodular_moebius_transform d "-b" "-c" a
  by unfold_locales (use unimodular in Groebner_Basis.algebra)

lemma inv_\<phi>:
  assumes "of_int c * z + of_int d \<noteq> 0"
  shows   "inv.\<phi> (\<phi> z) = z"
  using unimodular assms
  unfolding inv.\<phi>_def \<phi>_def of_int_minus
  by (subst moebius_inverse) (auto simp flip: of_int_mult)

lemma inv_\<phi>':
  assumes "of_int c * z - of_int a \<noteq> 0"
  shows   "\<phi> (inv.\<phi> z) = z"
  using unimodular assms
  unfolding inv.\<phi>_def \<phi>_def of_int_minus
  by (subst moebius_inverse') (auto simp flip: of_int_mult)

end


subsection \<open>The modular group\<close>

subsubsection \<open>Definition\<close>

text \<open>
  We define the modular group as a quotient of all integer tuples $(a,b,c,d)$ with $ad-bc = 1$
  over a relation that identifies $(a,b,c,d)$ with $(-a,-b,-c,-d)$.
\<close>
definition modgrp_rel :: "int \<times> int \<times> int \<times> int \<Rightarrow> int \<times> int \<times> int \<times> int \<Rightarrow> bool" where
  "modgrp_rel =
     (\<lambda>(a,b,c,d) (a',b',c',d'). a * d - b * c = 1 \<and>
                                ((a,b,c,d) = (a',b',c',d') \<or> (a,b,c,d) = (-a',-b',-c',-d')))"

lemma modgrp_rel_same_iff: "modgrp_rel x x \<longleftrightarrow> (case x of (a,b,c,d) \<Rightarrow> a * d - b * c = 1)"
  by (auto simp: modgrp_rel_def)

lemma part_equivp_modgrp_rel: "part_equivp modgrp_rel"
  unfolding part_equivp_def
proof safe
  show "\<exists>x. modgrp_rel x x"
    by (rule exI[of _ "(1,0,0,1)"]) (auto simp: modgrp_rel_def)
qed (auto simp: modgrp_rel_def case_prod_unfold fun_eq_iff)
       

quotient_type modgrp = "int \<times> int \<times> int \<times> int" / partial: modgrp_rel
  by (fact part_equivp_modgrp_rel)

instantiation modgrp :: one
begin

lift_definition one_modgrp :: modgrp is "(1, 0, 0, 1)"
  by (auto simp: modgrp_rel_def)

instance ..
end


instantiation modgrp :: times
begin

lift_definition times_modgrp :: "modgrp \<Rightarrow> modgrp \<Rightarrow> modgrp"
  is "\<lambda>(a,b,c,d) (a',b',c',d'). (a * a' + b * c', a * b' + b * d', c * a' + d * c', c * b' + d * d')"
  unfolding modgrp_rel_def case_prod_unfold prod_eq_iff fst_conv snd_conv
  by (elim conjE disjE; intro conjI) (auto simp: algebra_simps)

instance ..
end


instantiation modgrp :: inverse
begin

lift_definition inverse_modgrp :: "modgrp \<Rightarrow> modgrp"
  is "\<lambda>(a, b, c, d). (d, -b, -c, a)"
  by (auto simp: modgrp_rel_def algebra_simps)

definition divide_modgrp :: "modgrp \<Rightarrow> modgrp \<Rightarrow> modgrp" where
  "divide_modgrp x y = x * inverse y"

instance ..

end


interpretation modgrp: Groups.group "(*) :: modgrp \<Rightarrow> _" 1 inverse
proof
  show "a * b * c = a * (b * c :: modgrp)" for a b c
    by (transfer; unfold modgrp_rel_def case_prod_unfold prod_eq_iff fst_conv snd_conv;
        intro conjI; elim conjE disjE)
       (auto simp: algebra_simps)
next
  show "1 * a = a" for a :: modgrp
    by transfer (auto simp: modgrp_rel_def)
next
  show "inverse a * a = 1" for a :: modgrp
    by (transfer; unfold modgrp_rel_def case_prod_unfold prod_eq_iff fst_conv snd_conv;
        intro conjI; elim conjE disjE)
       (auto simp: algebra_simps)
qed    


instance modgrp :: monoid_mult
  by standard (simp_all add: modgrp.assoc)

lemma inverse_power_modgrp: "inverse (x ^ n :: modgrp) = inverse x ^ n"
  by (induction n) (simp_all add: algebra_simps modgrp.inverse_distrib_swap power_commuting_commutes)



subsubsection \<open>Basic operations\<close>

text \<open>Application to a field\<close>
lift_definition apply_modgrp :: "modgrp \<Rightarrow> 'a :: field \<Rightarrow> 'a" is
  "\<lambda>(a,b,c,d). moebius (of_int a) (of_int b) (of_int c) (of_int d)"
  by (auto simp: modgrp_rel_def)

text \<open>The shift operation $z \mapsto z + n$\<close>
lift_definition shift_modgrp :: "int \<Rightarrow> modgrp" is "\<lambda>n. (1, n, 0, 1)"
  by transfer (auto simp: modgrp_rel_def)

text \<open>The shift operation $z \mapsto z + 1$\<close>
lift_definition T_modgrp :: modgrp is "(1, 1, 0, 1)"
  by transfer (auto simp: modgrp_rel_def)

text \<open>The operation $z \mapsto -\frac{1}{z}$\<close>
lift_definition S_modgrp :: modgrp is "(0, -1, 1, 0)"
  by transfer (auto simp: modgrp_rel_def)

text \<open>Whether or not the transformation has a pole in the complex plane\<close>
lift_definition is_singular_modgrp :: "modgrp \<Rightarrow> bool" is "\<lambda>(a,b,c,d). c \<noteq> 0"
  by transfer (auto simp: modgrp_rel_def)

text \<open>The position of the transformation's pole in the complex plane (if it has one)\<close>
lift_definition pole_modgrp :: "modgrp \<Rightarrow> 'a :: field" is "\<lambda>(a,b,c,d). -of_int d / of_int c"
  by transfer (auto simp: modgrp_rel_def)

lemma pole_modgrp_in_Reals: "pole_modgrp f \<in> (\<real> :: 'a :: real_field set)"
  by transfer (auto intro!: Reals_divide)

lemma Im_pole_modgrp [simp]: "Im (pole_modgrp f) = 0"
  by transfer auto

text \<open>
  The complex number to which complex infinity is mapped by the transformation.
  This is undefined if the transformation maps complex infinity to itself.
\<close>
lift_definition pole_image_modgrp :: "modgrp \<Rightarrow> 'a :: field" is "\<lambda>(a,b,c,d). of_int a / of_int c"
  by transfer (auto simp: modgrp_rel_def)

lemma Im_pole_image_modgrp [simp]: "Im (pole_image_modgrp f) = 0"
  by transfer auto

text \<open>
  The normalised coefficients of the transformation. The convention that is chosen is that
  \<open>c\<close> is always non-negative, and if \<open>c\<close> is zero then \<open>d\<close> is positive.
\<close>
lift_definition modgrp_a :: "modgrp \<Rightarrow> int" is "\<lambda>(a,b,c,d). if c < 0 \<or> c = 0 \<and> d < 0 then -a else a"
  by transfer (auto simp: modgrp_rel_def)

lift_definition modgrp_b :: "modgrp \<Rightarrow> int" is "\<lambda>(a,b,c,d). if c < 0 \<or> c = 0 \<and> d < 0 then -b else b"
  by transfer (auto simp: modgrp_rel_def)

lift_definition modgrp_c :: "modgrp \<Rightarrow> int" is "\<lambda>(a,b,c,d). \<bar>c\<bar>"
  by transfer (auto simp: modgrp_rel_def)

lift_definition modgrp_d :: "modgrp \<Rightarrow> int" is "\<lambda>(a,b,c,d). if c < 0 \<or> c = 0 \<and> d < 0 then -d else d"
  by transfer (auto simp: modgrp_rel_def)

lemma modgrp_abcd_S [simp]:
  "modgrp_a S_modgrp = 0" "modgrp_b S_modgrp = -1" "modgrp_c S_modgrp = 1" "modgrp_d S_modgrp = 0"
  by (transfer; simp)+

lemma modgrp_abcd_T [simp]:
  "modgrp_a T_modgrp = 1" "modgrp_b T_modgrp = 1" "modgrp_c T_modgrp = 0" "modgrp_d T_modgrp = 1"
  by (transfer; simp)+

lemma modgrp_abcd_shift [simp]:
  "modgrp_a (shift_modgrp n) = 1" "modgrp_b (shift_modgrp n) = n"
  "modgrp_c (shift_modgrp n) = 0" "modgrp_d (shift_modgrp n) = 1"
  by (transfer; simp)+

lemma modgrp_c_shift_left [simp]:
  "modgrp_c (shift_modgrp n * f) = modgrp_c f"
  by transfer auto

lemma modgrp_d_shift_left [simp]:
  "modgrp_d (shift_modgrp n * f) = modgrp_d f"
  by transfer auto

lemma modgrp_abcd_det: "modgrp_a x * modgrp_d x - modgrp_b x * modgrp_c x = 1"
  by transfer (auto simp: modgrp_rel_def)

lemma modgrp_c_nonneg: "modgrp_c x \<ge> 0"
  by transfer auto

lemma modgrp_a_nz_or_b_nz: "modgrp_a x \<noteq> 0 \<or> modgrp_b x \<noteq> 0"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma modgrp_c_nz_or_d_nz: "modgrp_c x \<noteq> 0 \<or> modgrp_d x \<noteq> 0"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma modgrp_cd_signs: "modgrp_c x > 0 \<or> modgrp_c x = 0 \<and> modgrp_d x > 0"
  by transfer (auto simp: modgrp_rel_def zmult_eq_1_iff)

lemma apply_modgrp_altdef:
  "(apply_modgrp x :: 'a :: field \<Rightarrow> _) =
   moebius (of_int (modgrp_a x)) (of_int (modgrp_b x)) (of_int (modgrp_c x)) (of_int (modgrp_d x))"
proof (transfer, goal_cases)
  case (1 x)
  thus ?case
    by (auto simp: case_prod_unfold moebius_uminus')
qed

text \<open>
  Converting a quadruple of numbers into an element of the modular group.
\<close>
lift_definition modgrp :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> modgrp" is
  "\<lambda>a b c d. if a * d - b * c = 1 then (a, b, c, d) else (1, 0, 0, 1)"
  by transfer (auto simp: modgrp_rel_def)

lemma modgrp_wrong: "a * d - b * c \<noteq> 1 \<Longrightarrow> modgrp a b c d = 1"
  by transfer (auto simp: modgrp_rel_def algebra_simps)

lemma modgrp_cong:
  assumes "modgrp_rel (a,b,c,d) (a',b',c',d')"
  shows   "modgrp a b c d = modgrp a' b' c' d'"
  using assms by transfer (auto simp add: modgrp_rel_def)

lemma modgrp_abcd [simp]: "modgrp (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x) = x"
  apply transfer
  apply (auto split: if_splits)
        apply (auto simp: modgrp_rel_def)
  done

lemma
  assumes "a * d - b * c = 1"
  shows   modgrp_c_modgrp: "modgrp_c (modgrp a b c d) = \<bar>c\<bar>"
    and   modgrp_a_modgrp: "modgrp_a (modgrp a b c d) = (if c < 0 \<or> c = 0 \<and> d < 0 then -a else a)"
    and   modgrp_b_modgrp: "modgrp_b (modgrp a b c d) = (if c < 0 \<or> c = 0 \<and> d < 0 then -b else b)"
    and   modgrp_d_modgrp: "modgrp_d (modgrp a b c d) = (if c < 0 \<or> c = 0 \<and> d < 0 then -d else d)"
  using assms by (transfer; simp add: modgrp_rel_def)+


subsubsection \<open>Basic properties\<close>

lemma continuous_on_apply_modgrp [continuous_intros]:
  fixes g :: "'a :: topological_space \<Rightarrow> 'b :: real_normed_field"
  assumes "continuous_on A g" "\<And>z. z \<in> A \<Longrightarrow> \<not>is_singular_modgrp f \<or> g z \<noteq> pole_modgrp f"
  shows   "continuous_on A (\<lambda>z. apply_modgrp f (g z))"
  using assms
  by transfer (auto intro!: continuous_intros simp: modgrp_rel_def)

lemma holomorphic_on_apply_modgrp [holomorphic_intros]:
  assumes "g holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> \<not>is_singular_modgrp f \<or> g z \<noteq> pole_modgrp f"
  shows   "(\<lambda>z. apply_modgrp f (g z)) holomorphic_on A"
  using assms
  by transfer (auto intro!: holomorphic_intros simp: modgrp_rel_def)

lemma analytic_on_apply_modgrp [analytic_intros]:
  assumes "g analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> \<not>is_singular_modgrp f \<or> g z \<noteq> pole_modgrp f"
  shows   "(\<lambda>z. apply_modgrp f (g z)) analytic_on A"
  using assms
  by transfer (auto intro!: analytic_intros simp: modgrp_rel_def)

lemma isCont_apply_modgrp [continuous_intros]:
  fixes z :: "'a :: real_normed_field"
  assumes "\<not>is_singular_modgrp f \<or> z \<noteq> pole_modgrp f"
  shows   "isCont (apply_modgrp f) z"
proof -
  define S where "S = (if is_singular_modgrp f then -{pole_modgrp f} else (UNIV :: 'a set))"
  have "continuous_on S (apply_modgrp f)"
    unfolding S_def by (intro continuous_intros) auto
  moreover have "open S" "z \<in> S"
    using assms by (auto simp: S_def)
  ultimately show ?thesis
    using continuous_on_eq_continuous_at by blast
qed

lemmas tendsto_apply_modgrp [tendsto_intros] = isCont_tendsto_compose[OF isCont_apply_modgrp]

lift_definition diff_scale_factor_modgrp :: "modgrp \<Rightarrow> 'a :: field \<Rightarrow> 'a \<Rightarrow> 'a" is
  "\<lambda>(a,b,c,d) w z. (of_int c * w + of_int d) * (of_int c * z + of_int d)"
  by (auto simp: modgrp_rel_def algebra_simps)

lemma diff_scale_factor_modgrp_commutes:
  "diff_scale_factor_modgrp f w z = diff_scale_factor_modgrp f z w"
  by transfer (simp add: case_prod_unfold)

lemma diff_scale_factor_modgrp_zero_iff:
  fixes w z :: "'a :: field_char_0"
  shows "diff_scale_factor_modgrp f w z = 0 \<longleftrightarrow> is_singular_modgrp f \<and> pole_modgrp f \<in> {w, z}"
  by transfer
     (auto simp: case_prod_unfold modgrp_rel_def divide_simps add_eq_0_iff mult.commute 
                    minus_equation_iff[of "of_int x" for x])

lemma apply_modgrp_diff_eq:
  fixes g :: modgrp
  defines "f \<equiv> apply_modgrp g"
  assumes *: "\<not>is_singular_modgrp g \<or> pole_modgrp g \<notin> {w, z}"
  shows   "f w - f z = (w - z) / diff_scale_factor_modgrp g w z"
  unfolding f_def using *
  by transfer
     (auto simp: modgrp_rel_def moebius_diff_eq zmult_eq_1_iff
           simp flip: of_int_diff of_int_mult split: if_splits)

lemma norm_modgrp_dividend_ge:
  fixes z :: complex
  shows   "norm (of_int c * z + of_int d) \<ge> \<bar>c * Im z\<bar>"
proof -
  define x y where "x = Re z" and "y = Im z"
  have z_eq: "z = Complex x y"
    by (simp add: x_def y_def)
  have "(real_of_int c * y) ^ 2 \<le> (real_of_int c * x + real_of_int d) ^ 2 + (real_of_int c * y) ^ 2"
    by simp
  also have "\<dots> = norm (of_int c * z + of_int d) ^ 2"
    by (simp add: cmod_power2 x_def y_def)
  finally show "norm (of_int c * z + of_int d) \<ge> \<bar>c * y\<bar>"
    by (metis abs_le_square_iff abs_norm_cancel)
qed

lemma diff_scale_factor_modgrp_altdef:
  fixes g :: modgrp
  defines "c \<equiv> modgrp_c g" and "d \<equiv> modgrp_d g"
  shows "diff_scale_factor_modgrp g w z = (of_int c * w + of_int d) * (of_int c * z + of_int d)"
  unfolding c_def d_def by transfer (auto simp: algebra_simps)

lemma norm_diff_scale_factor_modgrp_ge_complex:
  fixes w z :: complex
  assumes "w \<noteq> z"
  shows   "norm (diff_scale_factor_modgrp g w z) \<ge> of_int (modgrp_c g) ^ 2 * \<bar>Im w * Im z\<bar>"
proof -
  have "norm (diff_scale_factor_modgrp g w z) \<ge>
        \<bar>of_int (modgrp_c g) * Im w\<bar> * \<bar>of_int (modgrp_c g) * Im z\<bar>"
    unfolding diff_scale_factor_modgrp_altdef norm_mult
    by (intro mult_mono norm_modgrp_dividend_ge) auto
  thus ?thesis
    by (simp add: algebra_simps abs_mult power2_eq_square)
qed

lemma apply_shift_modgrp [simp]: "apply_modgrp (shift_modgrp n) z = z + of_int n"
  by transfer (auto simp: moebius_def)

lemma apply_modgrp_T [simp]: "apply_modgrp T_modgrp z = z + 1"
  by transfer (auto simp: moebius_def)

lemma apply_modgrp_S [simp]: "apply_modgrp S_modgrp z = -1 / z"
  by transfer (auto simp: moebius_def)

lemma apply_modgrp_1 [simp]: "apply_modgrp 1 z = z"
  by transfer (auto simp: moebius_def)

lemma apply_modgrp_mult_aux:
  fixes z :: "'a :: field_char_0"
  assumes ns: "c' = 0 \<or> z \<noteq> -d' / c'"
  assumes det: "a * d - b * c = 1" "a' * d' - b' * c' = 1"
  shows   "moebius a b c d (moebius a' b' c' d' z) =
           moebius (a * a' + b * c') (a * b' + b * d')
                   (c * a' + d * c') (c * b' + d * d') z"
proof -
  have det': "c \<noteq> 0 \<or> d \<noteq> 0" "c' \<noteq> 0 \<or> d' \<noteq> 0"
    using det by auto
  from assms have nz: "c' * z + d' \<noteq> 0"
    by (auto simp add: divide_simps add_eq_0_iff split: if_splits)
  show ?thesis using det nz
    by (simp add: moebius_def divide_simps) (auto simp: algebra_simps)
qed

lemma apply_modgrp_mult:
  fixes z :: "'a :: field_char_0"
  assumes "\<not>is_singular_modgrp y \<or> z \<noteq> pole_modgrp y"
  shows   "apply_modgrp (x * y) z = apply_modgrp x (apply_modgrp y z)"
  using assms
proof (transfer, goal_cases)
  case (1 y z x)
  obtain a b c d where [simp]: "x = (a, b, c, d)"
    using prod_cases4 by blast
  obtain a' b' c' d' where [simp]: "y = (a', b', c', d')"
    using prod_cases4 by blast
  show ?case
    using apply_modgrp_mult_aux[of "of_int c'" z "of_int d'" "of_int a" "of_int d"
                                   "of_int b" "of_int c" "of_int a'" "of_int b'"] 1
    by (simp flip: of_int_mult of_int_add of_int_diff of_int_minus add: modgrp_rel_def)
qed

lemma is_singular_modgrp_altdef: "is_singular_modgrp x \<longleftrightarrow> modgrp_c x \<noteq> 0"
  by transfer (auto split: if_splits)

lemma not_is_singular_modgrpD:
  assumes "\<not>is_singular_modgrp x"
  shows   "x = shift_modgrp (sgn (modgrp_a x) * modgrp_b x)"
  using assms
proof (transfer, goal_cases)
  case (1 x)
  obtain a b c d where [simp]: "x = (a, b, c, d)"
    using prod_cases4 by blast
  from 1 have [simp]: "c = 0"
    by auto
  from 1 have "a = 1 \<and> d = 1 \<or> a = -1 \<and> d = -1"
    by (auto simp: modgrp_rel_def zmult_eq_1_iff)
  thus ?case
    by (auto simp: modgrp_rel_def)
qed

lemma is_singular_modgrp_inverse [simp]: "is_singular_modgrp (inverse x) \<longleftrightarrow> is_singular_modgrp x"
  by transfer auto

lemma is_singular_modgrp_S_left_iff [simp]: "is_singular_modgrp (S_modgrp * f) \<longleftrightarrow> modgrp_a f \<noteq> 0"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma is_singular_modgrp_S_right_iff [simp]: "is_singular_modgrp (f * S_modgrp) \<longleftrightarrow> modgrp_d f \<noteq> 0"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma is_singular_modgrp_T_left_iff [simp]:
  "is_singular_modgrp (T_modgrp * f) \<longleftrightarrow> is_singular_modgrp f"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma is_singular_modgrp_T_right_iff [simp]:
  "is_singular_modgrp (f * T_modgrp) \<longleftrightarrow> is_singular_modgrp f"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma is_singular_modgrp_shift_left_iff [simp]:
  "is_singular_modgrp (shift_modgrp n * f) \<longleftrightarrow> is_singular_modgrp f"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma is_singular_modgrp_shift_right_iff [simp]:
  "is_singular_modgrp (f * shift_modgrp n) \<longleftrightarrow> is_singular_modgrp f"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma pole_modgrp_inverse [simp]: "pole_modgrp (inverse x) = pole_image_modgrp x"
  by transfer auto

lemma pole_image_modgrp_inverse [simp]: "pole_image_modgrp (inverse x) = pole_modgrp x"
  by transfer auto

lemma pole_image_modgrp_in_Reals: "pole_image_modgrp x \<in> (\<real> :: 'a :: {real_field, field} set)"
  by transfer (auto intro!: Reals_divide)

lemma apply_modgrp_inverse_eqI:
  fixes x y :: "'a :: field_char_0"
  assumes "\<not>is_singular_modgrp f \<or> y \<noteq> pole_modgrp f" "apply_modgrp f y = x"
  shows   "apply_modgrp (inverse f) x = y"
proof -
  have "apply_modgrp (inverse f) x = apply_modgrp (inverse f * f) y"
    using assms by (subst apply_modgrp_mult) auto
  also have "\<dots> = y"
    by simp
  finally show ?thesis .
qed

lemma apply_modgrp_eq_iff [simp]:
  fixes x y :: "'a :: field_char_0"
  assumes "\<not>is_singular_modgrp f \<or> x \<noteq> pole_modgrp f \<and> y \<noteq> pole_modgrp f"
  shows   "apply_modgrp f x = apply_modgrp f y \<longleftrightarrow> x = y"
  using assms by (metis apply_modgrp_inverse_eqI)

lemma is_singular_modgrp_times_aux:
  assumes det: "a * d - b * c = 1" "a' * d' - b' * (c' :: int) = 1"
  shows   "(c * a' + d * c' \<noteq> 0) \<longleftrightarrow> ((c = 0 \<longrightarrow> c' \<noteq> 0) \<and> (c = 0 \<or> c' = 0 \<or> -d * c' \<noteq> a' * c))"
  using assms by Groebner_Basis.algebra

lemma is_singular_modgrp_times_iff:
   "is_singular_modgrp (x * y) \<longleftrightarrow>
      (is_singular_modgrp x \<or> is_singular_modgrp y) \<and>
      (\<not>is_singular_modgrp x \<or> \<not>is_singular_modgrp y \<or> pole_modgrp x \<noteq> (pole_image_modgrp y :: real))"
proof (transfer, goal_cases)
  case (1 x y)
  obtain a b c d where [simp]: "x = (a, b, c, d)"
    using prod_cases4 by blast
  obtain a' b' c' d' where [simp]: "y = (a', b', c', d')"
    using prod_cases4 by blast
  show ?case
    using is_singular_modgrp_times_aux[of a d b c a' d' b' c'] 1
    by (auto simp: modgrp_rel_def field_simps simp flip: of_int_mult of_int_add of_int_minus of_int_diff)
qed

lemma shift_modgrp_1: "shift_modgrp 1 = T_modgrp"
  by transfer (auto simp: modgrp_rel_def)

lemma shift_modgrp_eq_iff: "shift_modgrp n = shift_modgrp m \<longleftrightarrow> n = m"
  by transfer (auto simp: modgrp_rel_def)

lemma shift_modgrp_neq_S [simp]: "shift_modgrp n \<noteq> S_modgrp"
  by transfer (auto simp: modgrp_rel_def)

lemma S_neq_shift_modgrp [simp]: "S_modgrp \<noteq> shift_modgrp n"
  by transfer (auto simp: modgrp_rel_def)

lemma shift_modgrp_eq_T_iff [simp]: "shift_modgrp n = T_modgrp \<longleftrightarrow> n = 1"
  by transfer (auto simp: modgrp_rel_def)

lemma T_eq_shift_modgrp_iff [simp]: "T_modgrp = shift_modgrp n \<longleftrightarrow> n = 1"
  by transfer (auto simp: modgrp_rel_def)

lemma shift_modgrp_0 [simp]: "shift_modgrp 0 = 1"
  by transfer (auto simp: modgrp_rel_def)

lemma shift_modgrp_add: "shift_modgrp (m + n) = shift_modgrp m * shift_modgrp n"
  by transfer (auto simp: modgrp_rel_def)

lemma shift_modgrp_minus: "shift_modgrp (-m) = inverse (shift_modgrp m)"
proof -
  have "1 = shift_modgrp (m + (-m))"
    by simp
  also have "shift_modgrp (m + (-m)) = shift_modgrp m * shift_modgrp (-m)"
    by (subst shift_modgrp_add) auto
  finally show ?thesis
    by (simp add: modgrp.inverse_unique)
qed

lemma shift_modgrp_power: "shift_modgrp n ^ m = shift_modgrp (n * m)"
  by (induction m) (auto simp: algebra_simps shift_modgrp_add)

lemma shift_modgrp_power_int: "shift_modgrp n powi m = shift_modgrp (n * m)"
  by (cases "m \<ge> 0")
     (auto simp: power_int_def shift_modgrp_power simp flip: shift_modgrp_minus)

lemma shift_shift_modgrp: "shift_modgrp n * (shift_modgrp m * x) = shift_modgrp (n + m) * x"
  by (simp add: mult.assoc shift_modgrp_add)


lemma shift_modgrp_conv_T_power: "shift_modgrp n = T_modgrp powi n"
  by (simp flip: shift_modgrp_1 add: shift_modgrp_power_int)

lemma modgrp_S_S [simp]: "S_modgrp * S_modgrp = 1"
  by transfer (auto simp: modgrp_rel_def)

lemma inverse_S_modgrp [simp]: "inverse S_modgrp = S_modgrp"
  using modgrp_S_S modgrp.inverse_unique by metis

lemma modgrp_S_S_' [simp]: "S_modgrp * (S_modgrp * x) = x"
  by (subst mult.assoc [symmetric], subst modgrp_S_S) simp

lemma modgrp_S_power: "S_modgrp ^ n = (if even n then 1 else S_modgrp)"
  by (induction n) auto

lemma modgrp_S_S_power_int: "S_modgrp powi n = (if even n then 1 else S_modgrp)"
  by (auto simp: power_int_def modgrp_S_power even_nat_iff)


lemma not_is_singular_1_modgrp [simp]: "\<not>is_singular_modgrp 1"
  by transfer auto

lemma not_is_singular_T_modgrp [simp]: "\<not>is_singular_modgrp T_modgrp"
  by transfer auto

lemma not_is_singular_shift_modgrp [simp]: "\<not>is_singular_modgrp (shift_modgrp n)"
  by transfer auto

lemma is_singular_S_modgrp [simp]: "is_singular_modgrp S_modgrp"
  by transfer auto

lemma pole_modgrp_S [simp]: "pole_modgrp S_modgrp = 0"
  by transfer auto

lemma pole_modgrp_1 [simp]: "pole_modgrp 1 = 0"
  by transfer auto

lemma pole_modgrp_T [simp]: "pole_modgrp T_modgrp = 0"
  by transfer auto

lemma pole_modgrp_shift [simp]: "pole_modgrp (shift_modgrp n) = 0"
  by transfer auto

lemma pole_image_modgrp_1 [simp]: "pole_image_modgrp 1 = 0"
  by transfer auto

lemma pole_image_modgrp_T [simp]: "pole_image_modgrp T_modgrp = 0"
  by transfer auto

lemma pole_image_modgrp_shift [simp]: "pole_image_modgrp (shift_modgrp n) = 0"
  by transfer auto

lemma pole_image_modgrp_S [simp]: "pole_image_modgrp S_modgrp = 0"
  by transfer auto

lemma minus_minus_power2_eq: "(-x - y :: 'a :: ring_1) ^ 2 = (x + y) ^ 2"
  by (simp add: algebra_simps power2_eq_square)

lift_definition deriv_modgrp :: "modgrp \<Rightarrow> 'a :: field \<Rightarrow> 'a" is
  "\<lambda>(a,b,c,d) x. inverse ((of_int c * x + of_int d) ^ 2)"
  by (auto simp: modgrp_rel_def minus_minus_power2_eq)

lemma deriv_modgrp_nonzero:
  assumes "\<not>is_singular_modgrp f \<or> (x :: 'a :: field_char_0) \<noteq> pole_modgrp f"
  shows   "deriv_modgrp f x \<noteq> 0"
  using assms
  by transfer (auto simp: modgrp_rel_def add_eq_0_iff split: if_splits)

lemma deriv_modgrp_altdef:
  "deriv_modgrp f z = inverse (of_int (modgrp_c f) * z + of_int (modgrp_d f)) ^ 2"
  by transfer (auto simp: minus_minus_power2_eq power_inverse)

lemma apply_modgrp_has_field_derivative [derivative_intros]:
  assumes "\<not>is_singular_modgrp f \<or> x \<noteq> pole_modgrp f"
  shows   "(apply_modgrp f has_field_derivative deriv_modgrp f x) (at x within A)"
  using assms
proof (transfer, goal_cases)
  case (1 f x A)
  obtain a b c d where [simp]: "f = (a, b, c, d)"
    using prod_cases4 .
  have "(moebius (of_int a) (of_int b) (of_int c) (of_int d) has_field_derivative
           (of_int (a * d - b * c) / ((of_int c * x + of_int d)\<^sup>2)))
           (at x within A)"
    unfolding of_int_mult of_int_diff
    by (rule moebius_has_field_derivative) (use 1 in \<open>auto simp: modgrp_rel_def\<close>)
  also have "a * d - b * c = 1"
    using 1 by (simp add: modgrp_rel_def)
  finally show ?case
    by (simp add: field_simps)
qed

lemma apply_modgrp_has_field_derivative' [derivative_intros]:
  assumes "(g has_field_derivative g') (at x within A)"
  assumes "\<not>is_singular_modgrp f \<or> g x \<noteq> pole_modgrp f"
  shows   "((\<lambda>x. apply_modgrp f (g x)) has_field_derivative deriv_modgrp f (g x) * g')
              (at x within A)"
proof -
  have "((apply_modgrp f \<circ> g) has_field_derivative deriv_modgrp f (g x) * g') (at x within A)"
    by (intro DERIV_chain assms derivative_intros)
  thus ?thesis
    by (simp add: o_def)
qed


lemma modgrp_a_1 [simp]: "modgrp_a 1 = 1"
  and modgrp_b_1 [simp]: "modgrp_b 1 = 0"
  and modgrp_c_1 [simp]: "modgrp_c 1 = 0"
  and modgrp_d_1 [simp]: "modgrp_d 1 = 1"
  by (transfer; simp; fail)+

lemma modgrp_c_0: 
  assumes "a * d = 1"
  shows   "modgrp a b 0 d = shift_modgrp (if a > 0 then b else -b)"
  using assms by transfer (auto simp: modgrp_rel_def zmult_eq_1_iff)

lemma not_singular_modgrpD:
  assumes "\<not>is_singular_modgrp f"
  shows   "f = shift_modgrp (modgrp_b f)"
  using assms by transfer (auto simp: modgrp_rel_def zmult_eq_1_iff)

lemma S_conv_modgrp: "S_modgrp = modgrp 0 (-1) 1 0"
  and T_conv_modgrp: "T_modgrp = modgrp 1 1 0 1"
  and shift_conv_modgrp: "shift_modgrp n = modgrp 1 n 0 1"
  and one_conv_modgrp: "1 = modgrp 1 0 0 1"
  by (transfer; simp add: modgrp_rel_def)+

lemma modgrp_rel_reflI: "(case x of (a,b,c,d) \<Rightarrow> a * d - b * c = 1) \<Longrightarrow> x = y \<Longrightarrow> modgrp_rel x y"
  by (simp add: modgrp_rel_def case_prod_unfold)

lemma modgrp_times:
  assumes "a * d - b * c = 1"
  assumes "a' * d' - b' * c' = 1"
  shows "modgrp a b c d * modgrp a' b' c' d' =
         modgrp (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d')"
  using assms by transfer (auto simp: modgrp_rel_def algebra_simps)

lemma modgrp_inverse:
  assumes "a * d - b * c = 1"
  shows   "inverse (modgrp a b c d) = modgrp d (-b) (-c) a"
  by (intro modgrp.inverse_unique, subst modgrp_times)
     (use assms in \<open>auto simp: algebra_simps one_conv_modgrp\<close>)

lemma modgrp_a_mult_shift [simp]: "modgrp_a (f * shift_modgrp m) = modgrp_a f"
  by transfer auto

lemma modgrp_b_mult_shift [simp]: "modgrp_b (f * shift_modgrp m) = modgrp_a f * m + modgrp_b f"
  by transfer auto

lemma modgrp_c_mult_shift [simp]: "modgrp_c (f * shift_modgrp m) = modgrp_c f"
  by transfer auto

lemma modgrp_d_mult_shift [simp]: "modgrp_d (f * shift_modgrp m) = modgrp_c f * m + modgrp_d f"
  by transfer auto

lemma coprime_modgrp_c_d: "coprime (modgrp_c f) (modgrp_d f)"
proof -
  define a b c d where "a = modgrp_a f" "b = modgrp_b f" "c = modgrp_c f" "d = modgrp_d f"
  have "[a * 0 - b * c = a * d - b * c] (mod d)"
    by (intro cong_diff cong_refl cong_mult) (auto simp: Cong.cong_def)
  also have "a * d - b * c = 1"
    unfolding a_b_c_d_def modgrp_abcd_det[of f] by simp
  finally have "[c * (-b) = 1] (mod d)"
    by (simp add: mult_ac)
  thus "coprime c d"
    by (subst coprime_iff_invertible_int) (auto intro!: exI[of _ "-b"])
qed

context unimodular_moebius_transform
begin

lift_definition as_modgrp :: modgrp is "(a, b, c, d)"
  using unimodular by (auto simp: modgrp_rel_def)

lemma as_modgrp_altdef: "as_modgrp = modgrp a b c d"
  using unimodular by transfer (auto simp: modgrp_rel_def)

lemma \<phi>_as_modgrp: "\<phi> = apply_modgrp as_modgrp"
  unfolding \<phi>_def by transfer simp

end

interpretation modgrp: unimodular_moebius_transform "modgrp_a x" "modgrp_b x" "modgrp_c x" "modgrp_d x"
  rewrites "modgrp.as_modgrp = x" and "modgrp.\<phi> = apply_modgrp x"
proof -
  show *: "unimodular_moebius_transform (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x)"
    by unfold_locales (rule modgrp_abcd_det)
  show "unimodular_moebius_transform.as_modgrp (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x) = x"
    by (subst unimodular_moebius_transform.as_modgrp_altdef[OF *]) auto
  show "unimodular_moebius_transform.\<phi> (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x) = apply_modgrp x"
    by (subst unimodular_moebius_transform.\<phi>_def[OF *], subst apply_modgrp_altdef) auto
qed


subsection \<open>Code generation\<close>

code_datatype modgrp

lemma one_modgrp_code [code]:   "1 = modgrp 1 0 0 1"
  and S_modgrp_code [code]:     "S_modgrp = modgrp 0 (-1) 1 0"
  and T_modgrp_code [code]:     "T_modgrp = modgrp 1 1 0 1"
  and shift_modgrp_code [code]: "shift_modgrp n = modgrp 1 n 0 1"
  by (simp_all add: one_conv_modgrp S_conv_modgrp T_conv_modgrp shift_conv_modgrp)

lemma inverse_modgrp_code [code]: "inverse (modgrp a b c d) = modgrp d (-b) (-c) a"
  by (cases "a * d - b * c = 1")
     (auto simp: modgrp_inverse modgrp_wrong algebra_simps)

lemma times_modgrp_code [code]:
  "modgrp a b c d * modgrp a' b' c' d' = (
     if a * d - b * c \<noteq> 1 then modgrp a' b' c' d'
     else if a' * d' - b' * c' \<noteq> 1 then modgrp a b c d
     else  modgrp (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d'))"
  by (simp add: modgrp_times modgrp_wrong)

lemma modgrp_a_code [code]:
  "modgrp_a (modgrp a b c d) = (if a * d - b * c = 1 then if c < 0 \<or> c = 0 \<and> d < 0 then -a else a else 1)"
  by transfer auto

lemma modgrp_b_code [code]:
  "modgrp_b (modgrp a b c d) = (if a * d - b * c = 1 then if c < 0 \<or> c = 0 \<and> d < 0 then -b else b else 0)"
  by transfer (auto simp: modgrp_rel_def)

lemma modgrp_c_code [code]:
  "modgrp_c (modgrp a b c d) = (if a * d - b * c = 1 then \<bar>c\<bar> else 0)"
  by transfer (auto simp: modgrp_rel_def)

lemma modgrp_d_code [code]:
  "modgrp_d (modgrp a b c d) = (if a * d - b * c = 1 then if c < 0 \<or> c = 0 \<and> d < 0 then -d else d else 1)"
  by transfer auto

lemma apply_modgrp_code [code]:
  "apply_modgrp (modgrp a b c d) z =
     (if a * d - b * c \<noteq> 1 then z else (of_int a * z + of_int b) / (of_int c * z + of_int d))"
  by transfer (auto simp: moebius_def)

lemma is_singular_modgrp_code [code]:
  "is_singular_modgrp (modgrp a b c d) \<longleftrightarrow> a * d - b * c = 1 \<and> c \<noteq> 0"
  by transfer auto

lemma pole_modgrp_code [code]:
  "pole_modgrp (modgrp a b c d) = (if a * d - b * c = 1 then -of_int d / of_int c else 0)"
  by transfer auto

lemma pole_image_modgrp_code [code]:
  "pole_image_modgrp (modgrp a b c d) =
    (if a * d - b * c = 1 \<and> c \<noteq> 0 then of_int a / of_int c else 0)"
  by transfer auto


text \<open>
  The following will be needed later to define the slash operator.
  
\<close>
definition modgrp_factor :: "modgrp \<Rightarrow> complex \<Rightarrow> complex" where
  "modgrp_factor g z = of_int (modgrp_c g) * z + of_int (modgrp_d g)"

lemma modgrp_factor_1 [simp]: "modgrp_factor 1 z = 1"
  by (auto simp: modgrp_factor_def)

lemma modgrp_factor_shift [simp]: "modgrp_factor (shift_modgrp n) z = 1"
  by (simp add: modgrp_factor_def)

lemma modgrp_factor_T [simp]: "modgrp_factor T_modgrp z = 1"
  by (simp add: modgrp_factor_def)

lemma modgrp_factor_S [simp]: "modgrp_factor S_modgrp z = z"
  by (simp add: modgrp_factor_def)

lemma modgrp_factor_shift_right [simp]:
  "modgrp_factor (f * shift_modgrp n) z = modgrp_factor f (z + of_int n)"
  unfolding modgrp_factor_def
  by transfer (auto simp: algebra_simps)

lemma modgrp_factor_shift_left [simp]:
  "modgrp_factor (shift_modgrp n * f) z = modgrp_factor f z"
  by (simp add: modgrp_factor_def)

lemma modgrp_factor_T_right [simp]:
  "modgrp_factor (f * T_modgrp) z = modgrp_factor f (z + 1)"
  unfolding shift_modgrp_1 [symmetric] by (subst modgrp_factor_shift_right) auto

lemma modgrp_factor_T_left [simp]:
  "modgrp_factor (T_modgrp * f) z = modgrp_factor f z"
  unfolding shift_modgrp_1 [symmetric] by (subst modgrp_factor_shift_left) auto

lemma has_field_derivative_modgrp_factor [derivative_intros]:
  assumes "(f has_field_derivative f') (at x)"
  shows   "((\<lambda>x. modgrp_factor g (f x)) has_field_derivative (of_int (modgrp_c g) * f')) (at x)"
  unfolding modgrp_factor_def by (auto intro!: derivative_eq_intros assms)

lemma modgrp_factor_analytic [analytic_intros]: "modgrp_factor g analytic_on A"
  unfolding modgrp_factor_def by (auto simp: modgrp_factor_def intro!: analytic_intros)

lemma modgrp_factor_meromorphic [meromorphic_intros]: "modgrp_factor h meromorphic_on A"
  unfolding modgrp_factor_def by (auto intro!: meromorphic_intros)

lemma modgrp_factor_nonzero [simp]:
  assumes "Im z \<noteq> 0"
  shows   "modgrp_factor g z \<noteq> 0"
proof -
  define c d where "c = modgrp_c g" and "d = modgrp_d g"
  have "c \<noteq> 0 \<or> d \<noteq> 0"
    unfolding c_def d_def using modgrp_c_nz_or_d_nz by blast
  have "of_int c * z + of_int d \<noteq> 0"
    using assms \<open>c \<noteq> 0 \<or> d \<noteq> 0\<close> by (auto simp: complex_eq_iff)
  thus ?thesis
    by (simp add: modgrp_factor_def c_def d_def)
qed

lemma tendsto_modgrp_factor [tendsto_intros]:
  "(f \<longlongrightarrow> c) F \<Longrightarrow> ((\<lambda>x. modgrp_factor g (f x)) \<longlongrightarrow> modgrp_factor g c) F"
  unfolding modgrp_factor_def by (auto intro!: tendsto_intros)

lemma minus_diff_power_even:
  assumes "even k"
  shows   "(-a - b) ^ k = (a + b :: 'a :: ring_1) ^ k"
proof -
  have "(-a - b) ^ k = (-(a + b)) ^ k"
    by simp
  also have "\<dots> = (a + b) ^ k"
    using assms by (rule power_minus_even)
  finally show ?thesis .
qed

lemma minus_diff_power_int_even: 
  assumes "even k"
  shows   "(-a - b) powi k = (a + b :: 'a :: field) powi k"
proof -
  have "(-a - b) powi k = (-(a + b)) powi k"
    by simp
  also have "\<dots> = (a + b) powi k"
    by (rule power_int_minus_left_even) fact
  finally show ?thesis .
qed


subsection \<open>The slash operator\<close>

text \<open>
  The typical definition in the literature is that, for a function
  $f : \mathbb{H}\to\mathbb{C}$ and an element $\gamma$ of the modular group,
  the slash operator of weight $k$ is defined as $(f|_k\gamma)(z) = (cz+d)^{-k} f(\gamma z)$.

  This has notational advantages, but for formalisation, we think the following is a bit
  easier for now. Note that in practice, $k$ will always be even, and we do in fact need it to
  be even here because otherwise the concept would not be well-defined since $(c,d)$ is only
  determined up to a factor $\pm 1$.
\<close>
lift_definition modgrp_slash :: "modgrp \<Rightarrow> int \<Rightarrow> complex \<Rightarrow> complex" is
  "(\<lambda>(a,b,c,d) k z. if even k then (of_int c * z + of_int d) powi k else 0)"
  by standard (auto simp: fun_eq_iff modgrp_rel_def minus_diff_power_int_even)

lemma modgrp_slash_altdef:
  "modgrp_slash f k z = (if even k then modgrp_factor f z powi k else 0)"
  unfolding modgrp_factor_def by transfer (force simp: modgrp_rel_def minus_diff_power_int_even)

lemma modgrp_slash_1 [simp]: "even k \<Longrightarrow> modgrp_slash 1 k z = 1"
  by transfer auto

lemma modgrp_slash_shift [simp]: "even k \<Longrightarrow> modgrp_slash (shift_modgrp n) k z = 1"
  by transfer auto

lemma modgrp_slash_T [simp]: "even k \<Longrightarrow> modgrp_slash T_modgrp k z = 1"
  by transfer auto

lemma modgrp_slash_S [simp]: "even k \<Longrightarrow> modgrp_slash S_modgrp k z = z powi k"
  by transfer auto

lemma modgrp_slash_mult:
  assumes "z \<notin> \<real>"
  shows   "modgrp_slash (f * g) k z = modgrp_slash f k (apply_modgrp g z) * modgrp_slash g k z"
proof (use assms in transfer, safe, goal_cases)
  case (1 z a b c d a' b' c' d' k)
  hence "complex_of_int d' + z * complex_of_int c' \<noteq> 0"
    using 1 by (auto simp: modgrp_rel_def complex_eq_iff complex_is_Real_iff)
  thus ?case
    by (auto simp: moebius_def field_simps power_int_divide_distrib)
qed

lemma modgrp_slash_meromorphic [meromorphic_intros]: "modgrp_slash f k meromorphic_on A"
  unfolding modgrp_slash_altdef by (cases "even k") (auto intro!: meromorphic_intros)


subsection \<open>Representation as product of powers of generators\<close>

definition modgrp_from_gens :: "int option list \<Rightarrow> modgrp" where
  "modgrp_from_gens xs = prod_list (map (\<lambda>x. case x of None \<Rightarrow> S_modgrp | Some n \<Rightarrow> shift_modgrp n) xs)"

lemma modgrp_from_gens_Nil [simp]:
        "modgrp_from_gens [] = 1"
  and modgrp_from_gens_append [simp]:
        "modgrp_from_gens (xs @ ys) = modgrp_from_gens xs * modgrp_from_gens ys"
  and modgrp_from_gens_Cons1 [simp]:
        "modgrp_from_gens (None # xs) = S_modgrp * modgrp_from_gens xs"
  and modgrp_from_gens_Cons2 [simp]:
        "modgrp_from_gens (Some n # xs) = shift_modgrp n * modgrp_from_gens xs"
  and modgrp_from_gens_Cons:
        "modgrp_from_gens (x # xs) =
            (case x of None \<Rightarrow> S_modgrp | Some n \<Rightarrow> shift_modgrp n) * modgrp_from_gens xs"
  by (simp_all add: modgrp_from_gens_def)

definition invert_modgrp_gens :: "int option list \<Rightarrow> int option list"
  where "invert_modgrp_gens = rev \<circ> map (map_option uminus)"

lemma invert_modgrp_gens_Nil [simp]:
        "invert_modgrp_gens [] = []"
  and invert_modgrp_gens_append [simp]:
        "invert_modgrp_gens (xs @ ys) = invert_modgrp_gens ys @ invert_modgrp_gens xs"
  and invert_modgrp_gens_Cons1 [simp]:
        "invert_modgrp_gens (None # xs) = invert_modgrp_gens xs @ [None]"
  and invert_modgrp_gens_Cons2 [simp]:
        "invert_modgrp_gens (Some n # xs) = invert_modgrp_gens xs @ [Some (-n)]"
  and invert_modgrp_gens_Cons:
        "invert_modgrp_gens (x # xs) = invert_modgrp_gens xs @ [map_option uminus x]"
  by (simp_all add: invert_modgrp_gens_def)

lemma modgrp_from_gens_invert [simp]:
  "modgrp_from_gens (invert_modgrp_gens xs) = inverse (modgrp_from_gens xs)"
  by (induction xs)
     (auto simp: invert_modgrp_gens_Cons map_option_case algebra_simps 
                 modgrp.inverse_distrib_swap shift_modgrp_minus split: option.splits)

function modgrp_genseq :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int option list" where
  "modgrp_genseq a b c d =
     (if c = 0 then let b' = (if a > 0 then b else -b) in [Some b']
      else modgrp_genseq (-a * (d div c) + b) (-a) (d mod c) (-c) @ [None, Some (d div c)])"
  by auto
termination
  by (relation "Wellfounded.measure (nat \<circ> abs \<circ> (\<lambda>(_,_,c,_) \<Rightarrow> c))") (auto simp: abs_mod_less)

lemmas [simp del] = modgrp_genseq.simps

lemma modgrp_genseq_c_0: "modgrp_genseq a b 0 d = (let b' = (if a > 0 then b else -b) in [Some b'])"
  and modgrp_genseq_c_nz:
        "c \<noteq> 0 \<Longrightarrow> modgrp_genseq a b c d =
           (let q = d div c in modgrp_genseq (-a * q + b) (-a) (d mod c) (-c) @ [None, Some q])"
  by (subst modgrp_genseq.simps; simp add: Let_def)+  

lemma modgrp_genseq_code [code]:
  "modgrp_genseq a b c d =
     (if c = 0 then [Some (if a > 0 then b else -b)]
      else (let q = d div c in modgrp_genseq (-a * q + b) (-a) (d mod c) (-c) @ [None, Some q]))"
  by (subst modgrp_genseq.simps) (auto simp: Let_def)

lemma modgrp_genseq_correct:
  assumes "a * d - b * c = 1"
  shows   "modgrp_from_gens (modgrp_genseq a b c d) = modgrp a b c d"
  using assms
proof (induction a b c d rule: modgrp_genseq.induct)
  case (1 a b c d)
  write S_modgrp ("S")
  write shift_modgrp ("T")

  show ?case
  proof (cases "c = 0")
    case [simp]: True
    thus ?thesis using 1
      by (auto simp: modgrp_genseq_c_0 modgrp_c_0)
  next
    case False
    define q r where "q = d div c" and "r = d mod c"
    have "q * c + r = d"
      by (simp add: q_def r_def)
    with \<open>a * d - b * c = 1\<close> have det': "a * r - (b - a * q) * c = 1"
      by Groebner_Basis.algebra

    have "modgrp_from_gens (modgrp_genseq a b c d) = modgrp (-a * q + b) (-a) r (-c) * (S * T q)"
      using False "1.IH" det' by (simp add: modgrp_genseq_c_nz Let_def q_def r_def)
    also have "S * T q = modgrp 0 (- 1) 1 q"
      unfolding S_conv_modgrp shift_conv_modgrp by (subst modgrp_times) simp_all
    also have "modgrp (-a * q + b) (-a) r (-c) * \<dots> = modgrp (- a) (- b) (- c) (-r - c * q)"
      using det' by (subst modgrp_times) simp_all
    also have "\<dots> = modgrp a b c (q * c + r)"
      using det' by (intro modgrp_cong) (auto simp: algebra_simps modgrp_rel_def)
    also have "q * c + r = d"
      by (simp add: q_def r_def)
    finally show ?thesis .
  qed
qed

lemma filterlim_apply_modgrp_at:
  assumes "\<not>is_singular_modgrp g \<or> z \<noteq> pole_modgrp g"
  shows   "filterlim (apply_modgrp g) (at (apply_modgrp g z)) (at (z :: 'a :: real_normed_field))"
proof -
  have "\<forall>\<^sub>F x in at z. x \<in> (if is_singular_modgrp g then -{pole_modgrp g} else UNIV) - {z}"
    by (intro eventually_at_in_open) (use assms in auto)
  hence "\<forall>\<^sub>F x in at z. apply_modgrp g x \<noteq> apply_modgrp g z"
    by eventually_elim (use assms in \<open>auto split: if_splits\<close>)
  thus ?thesis
    using assms by (auto simp: filterlim_at intro!: tendsto_eq_intros)
qed

lemma apply_modgrp_neq_pole_image [simp]:
  "is_singular_modgrp g \<Longrightarrow> z \<noteq> pole_modgrp g \<Longrightarrow>
     apply_modgrp g (z :: 'a :: field_char_0) \<noteq> pole_image_modgrp g"
  by transfer (auto simp: field_simps add_eq_0_iff moebius_def modgrp_rel_def
                    simp flip: of_int_add of_int_mult of_int_diff)

lemma image_apply_modgrp_conv_vimage:
  fixes A :: "'a :: field_char_0 set"
  assumes "\<not>is_singular_modgrp f \<or> pole_modgrp f \<notin> A"
  defines "S \<equiv> (if is_singular_modgrp f then -{pole_image_modgrp f :: 'a} else UNIV)"
  shows   "apply_modgrp f ` A = apply_modgrp (inverse f) -` A \<inter> S"
proof (intro equalityI subsetI)
  fix z assume z: "z \<in> (apply_modgrp (inverse f) -` A) \<inter> S"
  thus "z \<in> apply_modgrp f ` A" using assms
    by (auto elim!: rev_image_eqI simp flip: apply_modgrp_mult simp: S_def split: if_splits)
next
  fix z assume z: "z \<in> apply_modgrp f ` A"
  then obtain x where x: "x \<in> A" "z = apply_modgrp f x"
    by auto
  have "apply_modgrp (inverse f) (apply_modgrp f x) \<in> A"
    using x assms by (subst apply_modgrp_mult [symmetric]) auto
  moreover have "apply_modgrp f x \<noteq> pole_image_modgrp f" if "is_singular_modgrp f"
    using x assms that by (intro apply_modgrp_neq_pole_image) auto
  ultimately show "z \<in> (apply_modgrp (inverse f) -` A) \<inter> S"
    using x by (auto simp: S_def)
qed

lemma apply_modgrp_open_map:
  fixes A :: "'a :: real_normed_field set"
  assumes "open A" "\<not>is_singular_modgrp f \<or> pole_modgrp f \<notin> A"
  shows   "open (apply_modgrp f ` A)"
proof -
  define S :: "'a set" where "S = (if is_singular_modgrp f then -{pole_image_modgrp f} else UNIV)"
  have "open S"
    by (auto simp: S_def)
  have "apply_modgrp f ` A = apply_modgrp (inverse f) -` A \<inter> S"
    using image_apply_modgrp_conv_vimage[of f A] assms by (auto simp: S_def)
  also have "apply_modgrp (inverse f) -` A \<inter> S = S \<inter> apply_modgrp (inverse f) -` A"
    by (simp only: Int_commute)
  also have "open \<dots>"
    using assms by (intro continuous_open_preimage continuous_intros assms \<open>open S\<close>)
                   (auto simp: S_def)
  finally show ?thesis .
qed

lemma filtermap_at_apply_modgrp:
  fixes z :: "'a :: real_normed_field"
  assumes "\<not>is_singular_modgrp g \<or> z \<noteq> pole_modgrp g"
  shows   "filtermap (apply_modgrp g) (at z) = at (apply_modgrp g z)"
proof (rule filtermap_fun_inverse)
  show "filterlim (apply_modgrp g) (at (apply_modgrp g z)) (at z)"
    using assms by (intro filterlim_apply_modgrp_at) auto
next
  have "filterlim (apply_modgrp (inverse g)) (at (apply_modgrp (inverse g) (apply_modgrp g z)))
           (at (apply_modgrp g z))"
    using assms by (intro filterlim_apply_modgrp_at) auto
  also have "apply_modgrp (inverse g) (apply_modgrp g z) = z"
    using assms by (simp flip: apply_modgrp_mult)
  finally show "filterlim (apply_modgrp (inverse g)) (at z) (at (apply_modgrp g z))" .
next
  have "eventually (\<lambda>x. x \<in> (if is_singular_modgrp g then -{pole_image_modgrp g} else UNIV))
           (at (apply_modgrp g z))"
    by (intro eventually_at_in_open') (use assms in auto)
  thus "\<forall>\<^sub>F x in at (apply_modgrp g z). apply_modgrp g (apply_modgrp (inverse g) x) = x"
    by eventually_elim (auto simp flip: apply_modgrp_mult split: if_splits)
qed

lemma zorder_moebius_zero:
  assumes "a \<noteq> 0" "a * d - b * c \<noteq> 0"
  shows   "zorder (moebius a b c d) (-b / a) = 1"
proof (rule zorder_eqI)
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  define A where "A = (if c = 0 then UNIV else -{-d/c})"
  show "open A"
    by (auto simp: A_def)
  show "-b/a \<in> A"
    using assms by (auto simp: A_def field_simps)
  show "(\<lambda>x. a / (c * x + d)) holomorphic_on A"
  proof (intro holomorphic_intros)
    fix x assume "x \<in> A"
    thus "c * x + d \<noteq> 0"
      unfolding A_def using assms
      by (auto simp: A_def field_simps add_eq_0_iff split: if_splits)
  qed
  show "a / (c * (-b / a) + d) \<noteq> 0"
    using assms by (auto simp: field_simps)
  show "moebius a b c d w = a / (c * w + d) * (w - - b / a) powi 1"
    if "w \<in> (if c = 0 then UNIV else - {- d / c})" "w \<noteq> - b / a" for w
    using that assms by (auto simp: divide_simps moebius_def split: if_splits)
qed

lemma zorder_moebius_pole:
  assumes "c \<noteq> 0" "a * d - b * c \<noteq> 0"
  shows   "zorder (moebius a b c d) (-d / c) = -1"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  have "zorder (moebius a b c d) (-d / c) =
          zorder (\<lambda>x. (a * x + b) / c / (x - (-d / c)) ^ 1) (-d / c)"
  proof (rule zorder_cong)
    have "eventually (\<lambda>z. z \<noteq> -d/c) (at (-d/c))"
      by (simp add: eventually_neq_at_within)
    thus "\<forall>\<^sub>F z in at (- d / c). moebius a b c d z = (a * z + b) / c / (z - - d / c) ^ 1"
      by eventually_elim (use assms in \<open>auto simp: moebius_def divide_simps mult_ac\<close>)
  qed auto
  also have "zorder (\<lambda>x. (a * x + b) / c / (x - (-d / c)) ^ 1) (-d / c) = -int 1"
  proof (rule zorder_nonzero_div_power)
    show "(\<lambda>w. (a * w + b) / c) holomorphic_on UNIV"
      using assms by (intro holomorphic_intros)
    show "(a * (-d / c) + b) / c \<noteq> 0"
      using assms by (auto simp: field_simps)
  qed auto
  finally show ?thesis by simp
qed

lemma zorder_moebius:
  assumes "c = 0 \<or> z \<noteq> -d / c" "a * d - b * c \<noteq> 0"
  shows   "zorder (\<lambda>x. moebius a b c d x - moebius a b c d z) z = 1"
proof (rule zorder_eqI)
  define S where "S = (if c = 0 then UNIV else -{-d/c})"
  define g where "g = (\<lambda>w. (a * d - b * c) / ((c * w + d) * (c * z + d)))"
  show "open S" "z \<in> S"
    using assms by (auto simp: S_def)
  show "g holomorphic_on S"
    unfolding g_def using assms
    by (intro holomorphic_intros no_zero_divisors)
       (auto simp: S_def field_simps add_eq_0_iff split: if_splits)
  show "(a * d - b * c) / ((c * z + d) * (c * z + d)) \<noteq> 0"
    using assms by (auto simp: add_eq_0_iff split: if_splits)
  show "moebius a b c d w - moebius a b c d z =
         (a * d - b * c) / ((c * w + d) * (c * z + d)) * (w - z) powi 1" if "w \<in> S" for w
    by (subst moebius_diff_eq) (use that assms in \<open>auto simp: S_def split: if_splits\<close>)
qed

lemma zorder_apply_modgrp:
  assumes "\<not>is_singular_modgrp g \<or> z \<noteq> pole_modgrp g"
  shows   "zorder (\<lambda>x. apply_modgrp g x - apply_modgrp g z) z = 1"
  using assms
proof (transfer, goal_cases)
  case (1 f z)
  obtain a b c d where [simp]: "f = (a, b, c, d)"
    using prod_cases4 .
  show ?case using 1 zorder_moebius[of c z d a b]
    by (auto simp: modgrp_rel_def simp flip: of_int_mult)
qed

lemma zorder_fls_modgrp_pole:
  assumes "is_singular_modgrp f"
  shows   "zorder (apply_modgrp f) (pole_modgrp f) = -1"
  using assms
proof (transfer, goal_cases)
  case (1 f)
  obtain a b c d where [simp]: "f = (a, b, c, d)"
    using prod_cases4 .
  show ?case using 1 zorder_moebius_pole[of c a d b]
    by (auto simp: modgrp_rel_def simp flip: of_int_mult)
qed


subsection \<open>Induction rules in terms of generators\<close>

text \<open>Theorem 2.1\<close>
lemma modgrp_induct_S_shift [case_names id S shift]:
  assumes "P 1"
          "\<And>x. P x \<Longrightarrow> P (S_modgrp * x)"
          "\<And>x n. P x \<Longrightarrow> P (shift_modgrp n * x)"
  shows   "P x"
proof -
  define xs where "xs = modgrp_genseq (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x)"
  have "P (modgrp_from_gens xs)"
    by (induction xs) (auto intro: assms simp: modgrp_from_gens_Cons split: option.splits)
  thus ?thesis using modgrp_abcd_det[of x]
    by (simp add: xs_def modgrp_genseq_correct)
qed

lemma modgrp_induct [case_names id S T inv_T]:
  assumes "P 1"
          "\<And>x. P x \<Longrightarrow> P (S_modgrp * x)"
          "\<And>x. P x \<Longrightarrow> P (T_modgrp * x)"
          "\<And>x. P x \<Longrightarrow> P (inverse T_modgrp * x)"
  shows   "P x"
proof -
  define xs where "xs = modgrp_genseq (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x)"
  have *: "P (T_modgrp ^ n * x)" if "P x" for n x
    by (induction n) (auto simp: mult.assoc shift_modgrp_1 intro: assms that)
  have **: "P (inverse T_modgrp ^ n * x)" if "P x" for n x
    by (induction n) (auto simp: shift_modgrp_add mult.assoc shift_modgrp_1 intro: assms that) 
  have ***: "P (shift_modgrp n * x)" if "P x" for n x
    using *[of x "nat n"] **[of x "nat (-n)"] that
    by (auto simp: shift_modgrp_conv_T_power power_int_def)
  have "P (modgrp_from_gens xs)"
    by (induction xs) (auto intro: assms *** simp: modgrp_from_gens_Cons split: option.splits)
  thus ?thesis using modgrp_abcd_det[of x]
    by (simp add: xs_def modgrp_genseq_correct)
qed

lemma modgrp_induct_S_shift' [case_names id S shift]:
  assumes "P 1"
          "\<And>x. P x \<Longrightarrow> P (x * S_modgrp)"
          "\<And>x n. P x \<Longrightarrow> P (x * shift_modgrp n)"
  shows   "P x"
proof -
  define xs where "xs = modgrp_genseq (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x)"
  have "P (modgrp_from_gens xs)"
    by (induction xs rule: rev_induct) (auto intro: assms simp: modgrp_from_gens_Cons split: option.splits)
  thus ?thesis using modgrp_abcd_det[of x]
    by (simp add: xs_def modgrp_genseq_correct)
qed

lemma modgrp_induct' [case_names id S T inv_T]:
  assumes "P 1"
          "\<And>x. P x \<Longrightarrow> P (x * S_modgrp)"
          "\<And>x. P x \<Longrightarrow> P (x * T_modgrp)"
          "\<And>x. P x \<Longrightarrow> P (x * inverse T_modgrp)"
  shows   "P x"
proof -
  define xs where "xs = modgrp_genseq (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x)"
  have *: "P (x * T_modgrp ^ n)" if "P x" for n x
    using assms(3)[of "x * T_modgrp ^ n" for n]
    by (induction n)  (auto intro: that simp: algebra_simps power_commuting_commutes)
  have **: "P (x * inverse T_modgrp ^ n)" if "P x" for n x
    using assms(4)[of "x * inverse T_modgrp ^ n" for n]
    by (induction n) (auto intro: that simp: algebra_simps power_commuting_commutes) 
  have ***: "P (x * shift_modgrp n)" if "P x" for n x
    using *[of x "nat n"] **[of x "nat (-n)"] that
    by (auto simp: shift_modgrp_conv_T_power power_int_def)
  have "P (modgrp_from_gens xs)"
    by (induction xs rule: rev_induct)
       (auto intro: assms *** simp: modgrp_from_gens_Cons split: option.splits)
  thus ?thesis using modgrp_abcd_det[of x]
    by (simp add: xs_def modgrp_genseq_correct)
qed

lemma moebius_uminus1: "moebius (-a) b c d = moebius a (-b) (-c) (-d)"
  by (auto simp add: moebius_def fun_eq_iff divide_simps) (auto simp: algebra_simps add_eq_0_iff)

lemma moebius_shift:
  "moebius a b c d (z + of_int n) = moebius a (a * of_int n + b) c (c * of_int n + d) z"
  by (simp add: moebius_def algebra_simps)

lemma moebius_eq_shift: "moebius 1 (of_int n) 0 1 z = z + of_int n"
  by (simp add: moebius_def)

lemma moebius_S:
  assumes "a * d - b * c \<noteq> 0" "z \<noteq> 0"
  shows   "moebius a b c d (-(1 / z)) = moebius b (- a) d (- c) (z :: 'a :: field)"
  using assms by (auto simp: divide_simps moebius_def)

lemma moebius_eq_S: "moebius 0 1 (-1) 0 z = -1 / z"
  by (simp add: moebius_def)

definition apply_modgrp' :: "modgrp \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a :: ring_1"
  where "apply_modgrp' f =
           (\<lambda>(x,y). (of_int (modgrp_a f) * x + of_int (modgrp_b f) * y, 
                     of_int (modgrp_c f) * x + of_int (modgrp_d f) * y))"

lemma apply_modgrp'_z_one:
  assumes "z \<notin> \<real>"
  shows   "apply_modgrp' f (z, 1) = (modgrp_factor f z * apply_modgrp f z, modgrp_factor f z)"
proof -
  from assms have "complex_of_int (modgrp_c f) * z + complex_of_int (modgrp_d f) \<noteq> 0"
    by (simp add: complex_is_Real_iff modgrp.Im_transform_pos_aux)
  thus ?thesis
    by (simp add: apply_modgrp'_def modgrp_factor_def apply_modgrp_altdef moebius_def)
qed


subsection \<open>Subgroups\<close>

locale modgrp_subgroup =
  fixes G :: "modgrp set"
  assumes one_in_G [simp, intro]: "1 \<in> G"
  assumes times_in_G [simp, intro]: "x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> x * y \<in> G"
  assumes inverse_in_G [simp, intro]: "x \<in> G \<Longrightarrow> inverse x \<in> G"
begin

lemma divide_in_G [intro]: "f \<in> G \<Longrightarrow> g \<in> G \<Longrightarrow> f / g \<in> G"
  unfolding divide_modgrp_def by (intro times_in_G inverse_in_G)

lemma power_in_G [intro]: "f \<in> G \<Longrightarrow> f ^ n \<in> G"
  by (induction n) auto

lemma power_int_in_G [intro]: "f \<in> G \<Longrightarrow> f powi n \<in> G"
  by (auto simp: power_int_def)

lemma prod_list_in_G [intro]: "(\<And>x. x \<in> set xs \<Longrightarrow> x \<in> G) \<Longrightarrow> prod_list xs \<in> G"
  by (induction xs) auto

lemma inverse_in_G_iff [simp]: "inverse f \<in> G \<longleftrightarrow> f \<in> G"
  by (metis inverse_in_G modgrp.inverse_inverse)

definition rel :: "complex \<Rightarrow> complex \<Rightarrow> bool" where
  "rel x y \<longleftrightarrow> Im x > 0 \<and> Im y > 0 \<and> (\<exists>f\<in>G. apply_modgrp f x = y)"

definition orbit :: "complex \<Rightarrow> complex set" where
  "orbit x = {y. rel x y}"

lemma Im_nonpos_imp_not_rel: "Im x \<le> 0 \<or> Im y \<le> 0 \<Longrightarrow> \<not>rel x y"
  by (auto simp: rel_def)

lemma orbit_empty: "Im x \<le> 0 \<Longrightarrow> orbit x = {}"
  by (auto simp: orbit_def Im_nonpos_imp_not_rel)

lemma rel_imp_Im_pos [dest]:
  assumes "rel x y"
  shows   "Im x > 0" "Im y > 0"
  using assms by (auto simp: rel_def)

lemma rel_refl [simp]: "rel x x \<longleftrightarrow> Im x > 0"
  by (auto simp: rel_def intro!: bexI[of _ 1])

lemma rel_sym:
  assumes "rel x y"
  shows   "rel y x"
proof -
  from assms obtain f where f: "f \<in> G" "Im x > 0" "Im y > 0" "apply_modgrp f x = y"
    by (auto simp: rel_def intro!: bexI[of _ 1])
  from this have "apply_modgrp (inverse f) y = x"
    using pole_modgrp_in_Reals[of f, where ?'a = complex]
    by (intro apply_modgrp_inverse_eqI) (auto simp: complex_is_Real_iff)
  moreover have "inverse f \<in> G"
    using f by auto
  ultimately show ?thesis
    using f by (auto simp: rel_def)
qed

lemma rel_commutes: "rel x y = rel y x"
  using rel_sym by blast

lemma rel_trans [trans]:
  assumes "rel x y" "rel y z"
  shows   "rel x z"
proof -
  from assms obtain f where f: "f \<in> G" "Im x > 0" "Im y > 0" "apply_modgrp f x = y"
    by (auto simp: rel_def intro!: bexI[of _ 1])
  from assms obtain g where g: "Im z > 0" "g \<in> G" "apply_modgrp g y = z"
    by (auto simp: rel_def intro!: bexI[of _ 1])
  have "apply_modgrp (g * f) x = z"
    using f g pole_modgrp_in_Reals[of f, where ?'a = complex]
    by (subst apply_modgrp_mult) (auto simp: complex_is_Real_iff)
  with f g show ?thesis
    unfolding rel_def by blast
qed

lemma relI1 [intro]: "rel x y \<Longrightarrow> f \<in> G \<Longrightarrow> Im x > 0 \<Longrightarrow> rel x (apply_modgrp f y)"
  using modgrp.Im_transform_pos_iff rel_def rel_trans by blast

lemma relI2 [intro]: "rel x y \<Longrightarrow> f \<in> G \<Longrightarrow> Im x > 0 \<Longrightarrow> rel (apply_modgrp f x) y"
  by (meson relI1 rel_commutes rel_def)

lemma rel_apply_modgrp_left_iff [simp]:
  assumes "f \<in> G"
  shows   "rel (apply_modgrp f x) y \<longleftrightarrow> Im x > 0 \<and> rel x y"
proof safe
  assume "rel (apply_modgrp f x) y"
  thus "rel x y"
    by (meson assms modgrp.Im_transform_pos_iff rel_def rel_trans)
next
  assume "rel x y" "Im x > 0"
  thus "rel (apply_modgrp f x) y"
    by (meson assms relI2 rel_trans)
qed auto

lemma rel_apply_modgrp_right_iff [simp]:
  assumes "f \<in> G"
  shows   "rel y (apply_modgrp f x) \<longleftrightarrow> Im x > 0 \<and> rel y x"
  using assms by (metis rel_apply_modgrp_left_iff rel_sym)

lemma orbit_refl_iff: "x \<in> orbit x \<longleftrightarrow> Im x > 0"
  by (auto simp: orbit_def)

lemma orbit_refl: "Im x > 0 \<Longrightarrow> x \<in> orbit x"
  by (auto simp: orbit_def)

lemma orbit_cong: "rel x y \<Longrightarrow> orbit x = orbit y"
  using rel_trans rel_commutes unfolding orbit_def by blast

lemma orbit_empty_iff [simp]: "orbit x = {} \<longleftrightarrow> Im x \<le> 0" "{} = orbit x \<longleftrightarrow> Im x \<le> 0"
  using orbit_refl orbit_empty by force+

lemmas [simp] = orbit_refl_iff

lemma orbit_eq_iff: "orbit x = orbit y \<longleftrightarrow> Im x \<le> 0 \<and> Im y \<le> 0 \<or> rel x y"
proof (cases "Im y \<le> 0 \<or> Im x \<le> 0")
  case True
  thus ?thesis
    by (auto simp: orbit_empty)
next
  case False
  have "(\<forall>z. rel x z \<longleftrightarrow> rel y z) \<longleftrightarrow> rel x y"
    by (meson False not_le rel_commutes rel_refl rel_trans)
  thus ?thesis
    using False unfolding orbit_def by blast
qed 

lemma orbit_apply_modgrp [simp]: "f \<in> G \<Longrightarrow> orbit (apply_modgrp f z) = orbit z"
  by (subst orbit_eq_iff) auto  

lemma apply_modgrp_in_orbit_iff [simp]: "f \<in> G \<Longrightarrow> apply_modgrp f z \<in> orbit y \<longleftrightarrow> z \<in> orbit y"
  by (auto simp: orbit_def rel_commutes)

lemma orbit_imp_Im_pos: "x \<in> orbit y \<Longrightarrow> Im x > 0"
  by (auto simp: orbit_def)

end

interpretation modular_group: modgrp_subgroup UNIV
  by unfold_locales auto

notation modular_group.rel (infixl "\<sim>\<^sub>\<Gamma>" 49)

lemma (in modgrp_subgroup) rel_imp_rel: "rel x y \<Longrightarrow> x \<sim>\<^sub>\<Gamma> y"
  unfolding rel_def modular_group.rel_def by auto

lemma modular_group_rel_plus_int_iff_right1 [simp]:
  assumes "z \<in> \<int>"
  shows   "x \<sim>\<^sub>\<Gamma> y + z \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
proof -
  from assms obtain n where n: "z = of_int n"
    by (elim Ints_cases)
  have "x \<sim>\<^sub>\<Gamma> apply_modgrp (shift_modgrp n) y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
    by (subst modular_group.rel_apply_modgrp_right_iff) auto
  thus ?thesis
    by (simp add: n)
qed

lemma
  assumes "z \<in> \<int>"
  shows   modular_group_rel_plus_int_iff_right2 [simp]: "x \<sim>\<^sub>\<Gamma> z + y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
    and   modular_group_rel_plus_int_iff_left1 [simp]:  "z + x \<sim>\<^sub>\<Gamma> y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
    and   modular_group_rel_plus_int_iff_left2 [simp]:  "x + z \<sim>\<^sub>\<Gamma> y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
  using modular_group_rel_plus_int_iff_right1[OF assms] modular_group.rel_commutes add.commute
  by metis+

lemma modular_group_rel_S_iff_right [simp]: "x \<sim>\<^sub>\<Gamma> -(1/y) \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
proof -
  have "x \<sim>\<^sub>\<Gamma> apply_modgrp S_modgrp y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
    by (subst modular_group.rel_apply_modgrp_right_iff) auto
  thus ?thesis
    by simp
qed

lemma modular_group_rel_S_iff_left [simp]: "-(1/x) \<sim>\<^sub>\<Gamma> y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
  using modular_group_rel_S_iff_right[of y x] by (metis modular_group.rel_commutes)


subsubsection \<open>Subgroups containing shifts\<close>

definition modgrp_subgroup_period :: "modgrp set \<Rightarrow> nat" where
  "modgrp_subgroup_period G = nat (Gcd {n. shift_modgrp n \<in> G})"

lemma of_nat_modgrp_subgroup_period:
  "of_nat (modgrp_subgroup_period G) = Gcd {n. shift_modgrp n \<in> G}"
  unfolding modgrp_subgroup_period_def by simp

lemma ideal_int_conv_Gcd:
  fixes A :: "int set"
  assumes "0 \<in> A"
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x + y \<in> A"
  assumes "\<And>x y. x \<in> A \<Longrightarrow> x * y \<in> A"
  shows   "A = {n. Gcd A dvd n}"
proof
  show "A \<subseteq> {n. Gcd A dvd n}"
    by auto
next
  have "Gcd A \<in> A"
  proof (cases "A = {0}")
    case False
    define x :: int where "x = int (LEAST x. int x \<in> A \<and> x > 0)"
    have ex: "\<exists>x. int x \<in> A \<and> x > 0"
    proof -
      from False obtain x where "x \<in> A - {0}"
        using assms(1) by auto
      with assms(3)[of x "-1"] show ?thesis
        by (intro exI[of _ "if x > 0 then nat x else nat (-x)"]) auto
    qed
    have x: "x \<in> A \<and> x > 0"
      unfolding x_def using LeastI_ex[OF ex] by auto
    have x': "x \<le> y" if y: "y \<in> A" "y > 0" for y
      using y unfolding x_def
      by (metis of_nat_le_iff wellorder_Least_lemma(2) zero_less_imp_eq_int)
    have "x dvd Gcd A"
    proof (rule Gcd_greatest)
      fix y assume y: "y \<in> A"
      have "y = (y div x) * x + (y mod x)"
        by simp
      have "y + x * (-1) * (y div x) \<in> A"
        by (intro assms) (use x y in auto)
      also have "y + x * (-1) * (y div x) = y mod x"
        by (simp add: algebra_simps)
      finally have "y mod x \<in> A" .
      moreover have "y mod x \<ge> 0" "y mod x < x"
        using x by simp_all
      ultimately have "y mod x = 0"
        using x'[of "y mod x"] by (cases "y mod x = 0") auto
      thus "x dvd y"
        by presburger
    qed
    thus "Gcd A \<in> A"
      using assms(3) x by (auto elim!: dvdE)
  qed auto
  thus "{n. Gcd A dvd n} \<subseteq> A"
    by (auto elim!: dvdE intro!: assms)
qed


locale modgrp_subgroup_periodic = modgrp_subgroup +
  assumes periodic': "\<exists>n>0. shift_modgrp n \<in> G"
begin

lemma modgrp_subgroup_period_pos: "modgrp_subgroup_period G > 0"
proof -
  have "Gcd {n. shift_modgrp n \<in> G} \<noteq> 0"
    using periodic' by (auto intro!: Nat.gr0I simp: Gcd_0_iff)
  moreover have "Gcd {n. shift_modgrp n \<in> G} \<ge> 0"
    by simp
  ultimately show ?thesis
    unfolding modgrp_subgroup_period_def by linarith
qed

lemma shift_modgrp_in_G_iff: "shift_modgrp n \<in> G \<longleftrightarrow> int (modgrp_subgroup_period G) dvd n"
proof -
  let ?A = "{n. shift_modgrp n \<in> G}"
  have "?A = {n. int (modgrp_subgroup_period G) dvd n}"
    unfolding of_nat_modgrp_subgroup_period
    by (rule ideal_int_conv_Gcd) (auto simp: shift_modgrp_add simp flip: shift_modgrp_power_int)
  thus ?thesis
    by auto
qed

lemma shift_modgrp_in_G_period [intro, simp]:
  "shift_modgrp (int (modgrp_subgroup_period G)) \<in> G"
  by (subst shift_modgrp_in_G_iff) auto

lemma shift_modgrp_in_G [intro]:
  "int (modgrp_subgroup_period G) dvd n \<Longrightarrow> shift_modgrp n \<in> G"
  by (subst shift_modgrp_in_G_iff) auto

end

interpretation modular_group: modgrp_subgroup_periodic UNIV
  rewrites "modgrp_subgroup_period UNIV = Suc 0"
  by unfold_locales (auto intro: exI[of _ 1] simp: modgrp_subgroup_period_def)

lemma modgrp_subgroup_period_UNIV [simp]: "modgrp_subgroup_period UNIV = Suc 0"
  by (simp add: modgrp_subgroup_period_def)


subsubsection \<open>Congruence subgroups\<close>

lift_definition modgrps_cong :: "int \<Rightarrow> modgrp set" is
  "\<lambda>q. {(a,b,c,d) :: (int \<times> int \<times> int \<times> int) | a b c d. a * d - b * c = 1 \<and> q dvd c}"
  by (auto simp: rel_set_def modgrp_rel_def)

lemma modgrps_cong_altdef: "modgrps_cong q = {f. q dvd modgrp_c f}"
  by transfer' (auto simp: modgrp_rel_def)

lemma modgrp_in_modgrps_cong_iff:
  assumes "a * d - b * c = 1"
  shows   "modgrp a b c d \<in> modgrps_cong q \<longleftrightarrow> q dvd c"
  using assms by (auto simp: modgrps_cong_altdef modgrp_c_code)

lemma modgrp_in_modgrps_cong:
  assumes "q dvd c" "a * d - b * c = 1"
  shows   "modgrp a b c d \<in> modgrps_cong q"
  using assms by (auto simp: modgrps_cong_altdef modgrp_c_code)

lemma shift_in_modgrps_cong [simp]: "shift_modgrp n \<in> modgrps_cong q"
  by (auto simp: modgrps_cong_altdef)

lemma S_in_modgrps_cong_iff [simp]: "S_modgrp \<in> modgrps_cong q \<longleftrightarrow> is_unit q"
  by (auto simp: modgrps_cong_altdef)

locale hecke_cong_subgroup =
  fixes q :: int
  assumes q_pos: "q > 0"
begin

definition subgrp ("\<Gamma>''") where "subgrp = modgrps_cong q"

lemma shift_in_subgrp [simp]: "shift_modgrp n \<in> subgrp"
  by (auto simp: subgrp_def)

lemma S_in_subgrp_iff [simp]: "S_modgrp \<in> subgrp \<longleftrightarrow> q = 1"
  using q_pos by (auto simp: subgrp_def)

sublocale modgrp_subgroup \<Gamma>'
proof
  show "inverse x \<in> \<Gamma>'" if "x \<in> \<Gamma>'" for x
  proof -
    from that have "q dvd modgrp_c x"
      by (simp add: modgrps_cong_altdef subgrp_def)
    hence "q dvd modgrp_c (inverse x)"
      by transfer auto
    thus "inverse x \<in> \<Gamma>'"
      by (simp add: modgrps_cong_altdef subgrp_def)
  qed
next
  show "x * y \<in> \<Gamma>'" if "x \<in> \<Gamma>'" "y \<in> \<Gamma>'" for x y
  proof -
    from that have "q dvd modgrp_c x" "q dvd modgrp_c y"
      by (auto simp: modgrps_cong_altdef subgrp_def)
    hence "q dvd modgrp_c (x * y)"
      by transfer auto
    thus ?thesis
      by (auto simp: modgrps_cong_altdef subgrp_def)
  qed
qed (auto simp: subgrp_def modgrps_cong_altdef)

end


locale hecke_prime_subgroup =
  fixes p :: int
  assumes p_prime: "prime p"
begin

lemma p_pos: "p > 0"
  using p_prime by (simp add: prime_gt_0_int)

lemma p_not_1 [simp]: "p \<noteq> 1"
  using p_prime by auto

sublocale hecke_cong_subgroup p
  by standard (rule p_pos)

notation subgrp ("\<Gamma>''")

definition S_shift_modgrp where "S_shift_modgrp n = S_modgrp * shift_modgrp n"

(* Theorem 4.1 *)
lemma modgrp_decompose:
  assumes "f \<notin> \<Gamma>'"
  obtains g k where "g \<in> \<Gamma>'" "k \<in> {0..<p}" "f = g * S_modgrp * shift_modgrp k"
proof -
  define a b c d where "a = modgrp_a f" "b = modgrp_b f" "c = modgrp_c f" "d = modgrp_d f"
  have det: "a * d - b * c = 1"
    unfolding a_b_c_d_def using modgrp_abcd_det[of f] by simp
  have "\<not>p dvd c"
    unfolding a_b_c_d_def using assms by (auto simp: subgrp_def modgrps_cong_altdef)
  hence "coprime p c"
    using p_prime by (intro prime_imp_coprime) auto
  define k where "k = (modular_inverse p c * d) mod p"
  have "[k * c = (modular_inverse p c * d) mod p * c] (mod p)"
    by (simp add: k_def)
  also have "[(modular_inverse p c * d) mod p * c = modular_inverse p c * d * c] (mod p)"
    by (intro cong_mult cong_mod_leftI cong_refl)
  also have "modular_inverse p c * d * c = modular_inverse p c * c * d"
    by (simp add: mult_ac)
  also have "[\<dots> = 1 * d] (mod p)" using \<open>coprime p c\<close>
    by (intro cong_mult cong_refl cong_modular_inverse2) (auto simp: coprime_commute)
  finally have "[k * c = d] (mod p)"
    by simp
  hence dvd: "p dvd k * c - d"
    by (simp add: cong_iff_dvd_diff)

  have det': "(k * a - b) * c - a * (k * c - d) = 1"
    using det by (simp add: algebra_simps)
  define g where "g = modgrp (k * a - b) a (k * c - d) c"

  show ?thesis
  proof (rule that)
    show "g \<in> \<Gamma>'"
      unfolding subgrp_def g_def using det' dvd
      by (intro modgrp_in_modgrps_cong) auto
  next
    show "k \<in> {0..<p}"
      unfolding k_def using p_pos by simp
  next
    have "g * S_modgrp * shift_modgrp k = modgrp a b c d" using det
      by (auto simp: g_def S_modgrp_code shift_modgrp_code times_modgrp_code algebra_simps)
    also have "\<dots> = f"
      by (simp add: a_b_c_d_def)
    finally show "f = g * S_modgrp * shift_modgrp k" ..
  qed
qed

lemma modgrp_decompose':
  obtains g h 
    where "g \<in> \<Gamma>'" "h = 1 \<or> (\<exists>k\<in>{0..<p}. h = S_shift_modgrp k)" "f = g * h"
proof (cases "f \<in> \<Gamma>'")
  case True
  thus ?thesis
    using that[of f 1] by auto
next
  case False
  thus ?thesis
    using modgrp_decompose[of f] that modgrp.assoc unfolding S_shift_modgrp_def
    by metis
qed

end

end
