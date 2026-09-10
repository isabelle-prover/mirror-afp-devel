(*  Title:      Simson_Complex_Geometry.thy
    Author:     Arthur Freitas Ramos, 2026
    Maintainer: Arthur Freitas Ramos

Shared ordinary-complex geometry used by the Simson and Miquel developments.

The published Complex_Geometry entry supplies the foundational notions of
complex-plane geometry.  This theory records the additional circle, line, and
ordinary-complex cross-ratio interface needed by both developments, so that
the two AFP entries do not carry duplicate definitions and proofs.
*)

theory Simson_Complex_Geometry
  imports Complex_Geometry.Elementary_Complex_Geometry
begin

lemma Im_zero_self_cnj:
  assumes "Im W = 0" shows "W = cnj W"
  using assms by (simp add: complex_eq_iff)

lemma im_zero_cross:
  fixes A B :: complex
  assumes h: "Im (cnj A * B) = 0"
  shows "cnj A * B = A * cnj B"
proof -
  have "cnj A * B = cnj (cnj A * B)" by (rule Im_zero_self_cnj[OF h])
  also have "... = A * cnj B" by (simp add: complex_cnj_mult)
  finally show ?thesis .
qed

lemma collinear_iff_cross:
  "collinear a b c \<longleftrightarrow> Im (cnj (b - a) * (c - a)) = 0"
proof (cases "a = b")
  case True
  then show ?thesis by (simp add: collinear_def)
next
  case False
  have hab: "b - a \<noteq> 0" using False by simp
  have ratio_real:
    "is_real ((c - a) / (b - a)) \<longleftrightarrow>
      (c - a) * cnj (b - a) = (b - a) * cnj (c - a)"
    using is_real_div[of "b - a" "c - a"] hab by simp
  have cross_real:
    "is_real (cnj (b - a) * (c - a)) \<longleftrightarrow>
      cnj (b - a) * (c - a) = (b - a) * cnj (c - a)"
  proof
    assume h: "is_real (cnj (b - a) * (c - a))"
    then show "cnj (b - a) * (c - a) = (b - a) * cnj (c - a)"
      by (rule im_zero_cross)
  next
    assume h: "cnj (b - a) * (c - a) = (b - a) * cnj (c - a)"
    have "cnj (cnj (b - a) * (c - a)) = cnj (b - a) * (c - a)"
      using h by (simp add: complex_cnj_mult)
    then show "is_real (cnj (b - a) * (c - a))"
      by (metis Reals_cnj_iff complex_is_Real_iff)
  qed
  show ?thesis
    unfolding collinear_def
    using False ratio_real cross_real by (simp add: mult.commute)
qed

section \<open>Circles, lines, and the ordinary complex cross ratio\<close>

text \<open>A point \<^term>\<open>z\<close> lies on the circle of centre \<^term>\<open>c\<close> and radius
  \<^term>\<open>R\<close> when its distance to the centre equals \<^term>\<open>R\<close>.\<close>

definition oncircle :: "complex \<Rightarrow> real \<Rightarrow> complex \<Rightarrow> bool"
  where "oncircle c R z \<longleftrightarrow> cmod (z - c) = R"

text \<open>A point \<^term>\<open>z\<close> lies on the line through \<^term>\<open>a\<close> and \<^term>\<open>b\<close> when it
  is an affine combination of them with a real parameter.\<close>

definition on_line :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> bool"
  where "on_line a b z \<longleftrightarrow> (\<exists>t::real. z = a + of_real t * (b - a))"

text \<open>Four points are concyclic when they share a common circle of positive
  radius; three points are concyclic when they share such a circle.\<close>

definition concyclic :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> bool"
  where "concyclic a b c d \<longleftrightarrow>
    (\<exists>ctr R. 0 < R \<and> oncircle ctr R a \<and> oncircle ctr R b \<and> oncircle ctr R c \<and> oncircle ctr R d)"

definition concyclic3 :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> bool"
  where "concyclic3 a b c \<longleftrightarrow>
    (\<exists>ctr R. 0 < R \<and> oncircle ctr R a \<and> oncircle ctr R b \<and> oncircle ctr R c)"

text \<open>The ordinary cross ratio of four complex numbers.\<close>

definition complex_cross_ratio :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex"
  where "complex_cross_ratio w x y z = (w - y) * (x - z) / ((w - z) * (x - y))"

section \<open>Elementary facts about circles\<close>

lemma oncircle_norm_sq:
  assumes "oncircle c R z"
  shows "(z - c) * cnj (z - c) = complex_of_real (R\<^sup>2)"
proof -
  have "(z - c) * cnj (z - c) = complex_of_real ((cmod (z - c))\<^sup>2)"
    by (metis complex_norm_square)
  then show ?thesis using assms by (simp add: oncircle_def)
qed

lemma oncircle_ne_centre:
  assumes "oncircle c R z" and "0 < R"
  shows "z \<noteq> c"
proof
  assume "z = c"
  then have "cmod (z - c) = 0" by simp
  with assms show False by (simp add: oncircle_def)
qed

lemma cnj_diff_on_circle:
  assumes "oncircle c R z" and "0 < R"
  shows "cnj (z - c) = complex_of_real (R\<^sup>2) / (z - c)"
proof -
  have "z - c \<noteq> 0" using oncircle_ne_centre[OF assms] by simp
  moreover have "(z - c) * cnj (z - c) = complex_of_real (R\<^sup>2)"
    using oncircle_norm_sq[OF assms(1)] .
  ultimately show ?thesis
    by (metis nonzero_mult_div_cancel_left)
qed

section \<open>The cross-ratio criterion\<close>

text \<open>The algebraic heart of the criterion: replacing each of four points by
  the reciprocal expression that describes a point on a circle leaves the
  cross ratio unchanged.\<close>

lemma complex_cross_ratio_reciprocal_aux:
  fixes A B C D k :: complex
  assumes "A \<noteq> 0" and "B \<noteq> 0" and "C \<noteq> 0" and "D \<noteq> 0"
    and "A \<noteq> D" and "B \<noteq> C" and "k \<noteq> 0"
  shows "(k/A - k/C) * (k/B - k/D) / ((k/A - k/D) * (k/B - k/C))
         = (A - C) * (B - D) / ((A - D) * (B - C))"
  using assms by (simp add: divide_simps) algebra

text \<open>If four points lie on a common circle of positive radius (and the two
  relevant differences are nonzero), then their cross ratio is real.\<close>

lemma concyclic_complex_cross_ratio_real:
  assumes a: "oncircle ctr R a" and b: "oncircle ctr R b"
    and c: "oncircle ctr R c" and d: "oncircle ctr R d"
    and pos: "0 < R" and ad: "a \<noteq> d" and bc: "b \<noteq> c"
  shows "complex_cross_ratio a b c d \<in> \<real>"
proof -
  define A where "A = a - ctr"
  define B where "B = b - ctr"
  define C where "C = c - ctr"
  define D where "D = d - ctr"
  define k where "k = complex_of_real (R\<^sup>2)"
  have kne: "k \<noteq> 0" using pos by (simp add: k_def)
  have Ane: "A \<noteq> 0" using oncircle_ne_centre[OF a pos] by (simp add: A_def)
  have Bne: "B \<noteq> 0" using oncircle_ne_centre[OF b pos] by (simp add: B_def)
  have Cne: "C \<noteq> 0" using oncircle_ne_centre[OF c pos] by (simp add: C_def)
  have Dne: "D \<noteq> 0" using oncircle_ne_centre[OF d pos] by (simp add: D_def)
  have ADne: "A \<noteq> D" using ad by (simp add: A_def D_def)
  have BCne: "B \<noteq> C" using bc by (simp add: B_def C_def)
  \<comment> \<open>conjugates of the four points on the circle\<close>
  have cA: "cnj (a - ctr) = k / A"
    using cnj_diff_on_circle[OF a pos] by (simp add: A_def k_def)
  have cB: "cnj (b - ctr) = k / B"
    using cnj_diff_on_circle[OF b pos] by (simp add: B_def k_def)
  have cC: "cnj (c - ctr) = k / C"
    using cnj_diff_on_circle[OF c pos] by (simp add: C_def k_def)
  have cD: "cnj (d - ctr) = k / D"
    using cnj_diff_on_circle[OF d pos] by (simp add: D_def k_def)
  \<comment> \<open>conjugates of the six differences appearing in the cross ratio\<close>
  have e_ac: "cnj (a - c) = k/A - k/C"
    using cA cC by (metis complex_cnj_diff diff_add_cancel diff_diff_eq2)
  have e_bd: "cnj (b - d) = k/B - k/D"
    using cB cD by (metis complex_cnj_diff diff_add_cancel diff_diff_eq2)
  have e_ad: "cnj (a - d) = k/A - k/D"
    using cA cD by (metis complex_cnj_diff diff_add_cancel diff_diff_eq2)
  have e_bc: "cnj (b - c) = k/B - k/C"
    using cB cC by (metis complex_cnj_diff diff_add_cancel diff_diff_eq2)
  have "cnj (complex_cross_ratio a b c d)
        = cnj (a - c) * cnj (b - d) / (cnj (a - d) * cnj (b - c))"
    by (simp only: complex_cross_ratio_def complex_cnj_divide complex_cnj_mult)
  also have "\<dots> = (k/A - k/C) * (k/B - k/D) / ((k/A - k/D) * (k/B - k/C))"
    by (simp only: e_ac e_bd e_ad e_bc)
  also have "\<dots> = (A - C) * (B - D) / ((A - D) * (B - C))"
    using complex_cross_ratio_reciprocal_aux[OF Ane Bne Cne Dne ADne BCne kne] .
  also have "\<dots> = complex_cross_ratio a b c d"
    by (simp add: complex_cross_ratio_def A_def B_def C_def D_def)
  finally have "cnj (complex_cross_ratio a b c d) = complex_cross_ratio a b c d" .
  thus ?thesis by (simp add: Reals_cnj_iff)
qed

text \<open>If three points lie on a circle and the cross ratio of a fourth point
  with them is real, the fourth point lies on the same circle.\<close>

lemma complex_cross_ratio_real_on_circle:
  assumes hc: "oncircle ctr R c" and hp: "oncircle ctr R p" and hq: "oncircle ctr R q"
    and pos: "0 < R"
    and cp: "c \<noteq> p" and cq: "c \<noteq> q" and pq: "p \<noteq> q" and mq: "m \<noteq> q"
    and crreal: "complex_cross_ratio m c p q \<in> \<real>"
  shows "oncircle ctr R m"
proof -
  define k where "k = complex_of_real (R\<^sup>2)"
  define G where "G = c - ctr"
  define P where "P = p - ctr"
  define K where "K = q - ctr"
  define M where "M = m - ctr"
  define cM where "cM = cnj (m - ctr)"
  have kne: "k \<noteq> 0" using pos by (simp add: k_def)
  have Gne: "G \<noteq> 0" using oncircle_ne_centre[OF hc pos] by (simp add: G_def)
  have Pne: "P \<noteq> 0" using oncircle_ne_centre[OF hp pos] by (simp add: P_def)
  have Kne: "K \<noteq> 0" using oncircle_ne_centre[OF hq pos] by (simp add: K_def)
  have GK: "G \<noteq> K" using cq by (simp add: G_def K_def)
  have GP: "G \<noteq> P" using cp by (simp add: G_def P_def)
  have KP: "K \<noteq> P" using pq by (simp add: K_def P_def)
  have MK: "M \<noteq> K" using mq by (simp add: M_def K_def)
  \<comment> \<open>conjugates of the three circle points\<close>
  have cG: "cnj (c - ctr) = k / G"
    using cnj_diff_on_circle[OF hc pos] by (simp add: G_def k_def)
  have cP: "cnj (p - ctr) = k / P"
    using cnj_diff_on_circle[OF hp pos] by (simp add: P_def k_def)
  have cK: "cnj (q - ctr) = k / K"
    using cnj_diff_on_circle[OF hq pos] by (simp add: K_def k_def)
  \<comment> \<open>conjugates of the four differences of the cross ratio\<close>
  have e_mp: "cnj (m - p) = cM - k / P"
    using cP unfolding cM_def by (metis complex_cnj_diff diff_add_cancel diff_diff_eq2)
  have e_mq: "cnj (m - q) = cM - k / K"
    using cK unfolding cM_def by (metis complex_cnj_diff diff_add_cancel diff_diff_eq2)
  have e_cq: "cnj (c - q) = k / G - k / K"
    using cG cK by (metis complex_cnj_diff diff_add_cancel diff_diff_eq2)
  have e_cp: "cnj (c - p) = k / G - k / P"
    using cG cP by (metis complex_cnj_diff diff_add_cancel diff_diff_eq2)
  \<comment> \<open>denominators are nonzero\<close>
  have KcMk: "K * cM - k \<noteq> 0"
  proof -
    have "cnj (m - q) = (K * cM - k) / K"
      using e_mq Kne by (simp add: field_simps)
    moreover have "cnj (m - q) \<noteq> 0" using mq by simp
    ultimately show ?thesis using Kne by auto
  qed
  \<comment> \<open>simplify the conjugate cross ratio\<close>
  have cnjcr: "cnj (complex_cross_ratio m c p q)
      = (P * cM - k) * (G - K) / ((K * cM - k) * (G - P))"
  proof -
    have "cnj (complex_cross_ratio m c p q)
        = cnj (m - p) * cnj (c - q) / (cnj (m - q) * cnj (c - p))"
      by (simp only: complex_cross_ratio_def complex_cnj_divide complex_cnj_mult)
    also have "\<dots> = (cM - k/P) * (k/G - k/K) / ((cM - k/K) * (k/G - k/P))"
      by (simp only: e_mp e_mq e_cq e_cp)
    also have "\<dots> = (P * cM - k) * (G - K) / ((K * cM - k) * (G - P))"
      using Gne Pne Kne kne by (simp add: divide_simps) algebra
    finally show ?thesis .
  qed
  \<comment> \<open>the cross ratio itself in the shifted coordinates\<close>
  have cr: "complex_cross_ratio m c p q = (M - P) * (G - K) / ((M - K) * (G - P))"
    by (simp add: complex_cross_ratio_def M_def P_def K_def G_def)
  \<comment> \<open>reality of the cross ratio\<close>
  from crreal have "cnj (complex_cross_ratio m c p q) = complex_cross_ratio m c p q"
    by (simp add: Reals_cnj_iff)
  with cnjcr cr
  have eq1: "(P * cM - k) * (G - K) / ((K * cM - k) * (G - P))
           = (M - P) * (G - K) / ((M - K) * (G - P))"
    by simp
  \<comment> \<open>cancel the common nonzero factors and cross-multiply\<close>
  have heq: "(P * cM - k) * (M - K) = (M - P) * (K * cM - k)"
  proof -
    have Y: "(K * cM - k) * (G - P) \<noteq> 0" using KcMk GP by simp
    have V: "(M - K) * (G - P) \<noteq> 0" using MK GP by simp
    have "(P * cM - k) * (G - K) * ((M - K) * (G - P))
        = (M - P) * (G - K) * ((K * cM - k) * (G - P))"
      using eq1 Y V by (simp add: frac_eq_eq)
    then have "((P * cM - k) * (M - K)) * ((G - K) * (G - P))
        = ((M - P) * (K * cM - k)) * ((G - K) * (G - P))"
      by (simp add: mult_ac)
    moreover have "(G - K) * (G - P) \<noteq> 0" using GK GP by simp
    ultimately show ?thesis by simp
  qed
  have "(K - P) * (M * cM - k) = 0"
    using heq by (simp add: algebra_simps)
  then have "M * cM = k"
    using KP by (metis mult_eq_0_iff right_minus_eq)
  \<comment> \<open>translate back to a distance statement\<close>
  have "M * cM = complex_of_real ((cmod M)\<^sup>2)"
    unfolding cM_def M_def by (metis complex_norm_square)
  with \<open>M * cM = k\<close> have "complex_of_real ((cmod M)\<^sup>2) = complex_of_real (R\<^sup>2)"
    by (simp add: k_def)
  then have "(cmod M)\<^sup>2 = R\<^sup>2" by (metis of_real_eq_iff)
  then have "cmod M = R" using pos by (simp add: power2_eq_imp_eq)
  thus ?thesis by (simp add: oncircle_def M_def)
qed

section \<open>Collinearity gives real ratios\<close>

lemma on_line_ratio_real:
  assumes "on_line a b z" and "b \<noteq> z"
  shows "(a - z) / (b - z) \<in> \<real>"
proof -
  from assms(1) obtain t where z: "z = a + of_real t * (b - a)"
    by (auto simp: on_line_def)
  have az: "a - z = of_real (- t) * (b - a)"
    using z by (simp add: algebra_simps of_real_minus)
  have bz: "b - z = of_real (1 - t) * (b - a)"
    using z by (simp add: algebra_simps of_real_diff)
  have bane: "b - a \<noteq> 0"
  proof
    assume "b - a = 0"
    with bz have "b - z = 0" by simp
    with assms(2) show False by simp
  qed
  have tne: "1 - t \<noteq> 0"
  proof
    assume "1 - t = 0"
    with bz have "b - z = 0" by simp
    with assms(2) show False by simp
  qed
  have "(a - z) / (b - z) = of_real (- t) / of_real (1 - t)"
    using az bz bane by simp
  also have "\<dots> = of_real (- t / (1 - t))"
    by (simp add: of_real_divide)
  finally show ?thesis by simp
qed

end
