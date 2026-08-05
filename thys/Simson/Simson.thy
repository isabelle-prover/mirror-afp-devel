(*  Title:      Simson.thy
    Author:     Arthur Freitas Ramos, 2026
    Maintainer: Arthur Freitas Ramos

The Wallace-Simson Line Theorem.

Let ABC be a nondegenerate triangle and let M be a point on its circumcircle.
Drop the perpendiculars from M to the three side lines BC, CA, AB, with feet
P, Q, R respectively.  Then P, Q, R are collinear; the line through them is the
Simson line (also called the Wallace line, after William Wallace's 1798
publication).  The converse also holds: if the three feet are collinear, then M
lies on the circumcircle of ABC.

We work with complex coordinates.  A circle is the set of points at a fixed
positive distance from a centre; three points are collinear when the imaginary
part of cnj (b - a) * (c - a) vanishes.  The foot of the perpendicular from m to
the line through a and b has the closed form

    foot a b m = (a + m)/2 + (b - a) * cnj (m - a) / (2 * cnj (b - a)).

Placing A, B, C, M on a common circle turns each pairwise difference of feet
into a clean product, and the theorem reduces to two algebraic identities with
the complex conjugate: for the forward direction the ratio of two foot
differences is a cross ratio of concyclic points (hence real), and for the
converse the collinearity of the feet forces the norm identity that puts M on
the circle.

Reference: the theorem was published by William Wallace in 1798 and is commonly
named after Robert Simson.
*)

theory Simson
  imports Simson_Complex_Geometry
begin

section \<open>Perpendicularity and feet of perpendiculars\<close>

text \<open>A point \<^term>\<open>z\<close> lies on the circle of centre \<^term>\<open>c\<close> and radius
  \<^term>\<open>R\<close> when its distance to the centre equals \<^term>\<open>R\<close>.\<close>

text \<open>Two displacement vectors are perpendicular when the real part of
  \<^term>\<open>cnj u * v\<close> (their Euclidean inner product) vanishes.\<close>

definition complex_perpendicular :: "complex \<Rightarrow> complex \<Rightarrow> bool"
  where "complex_perpendicular u v \<longleftrightarrow> Re (cnj u * v) = 0"

text \<open>The foot of the perpendicular from \<^term>\<open>m\<close> to the line through
  \<^term>\<open>a\<close> and \<^term>\<open>b\<close>, in closed complex form.\<close>

definition foot :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex"
  where "foot a b m = (a + m)/2 + (b - a) * cnj (m - a) / (2 * cnj (b - a))"


section \<open>Collinearity as a real ratio\<close>

text \<open>Three distinct-enough points are collinear exactly when the ratio of the
  two displacement vectors is real.\<close>

lemma collinear_iff_real_ratio:
  assumes "a \<noteq> c" shows "collinear a b c = ((b - a)/(c - a) \<in> \<real>)"
proof -
  have hc: "c - a \<noteq> 0" using assms by simp
  have E: "((b - a)/(c - a) \<in> \<real>) = (cnj (b - a) * (c - a) = (b - a) * cnj (c - a))"
    using hc by (auto simp add: Reals_cnj_iff complex_cnj_divide field_simps)
  have "collinear a b c = (Im (cnj (b - a) * (c - a)) = 0)"
    by (simp add: collinear_iff_cross)
  also have "... = (cnj (b - a) * (c - a) = (b - a) * cnj (c - a))"
  proof
    assume "Im (cnj (b - a) * (c - a)) = 0"
    thus "cnj (b - a) * (c - a) = (b - a) * cnj (c - a)" by (rule im_zero_cross)
  next
    assume "cnj (b - a) * (c - a) = (b - a) * cnj (c - a)"
    hence "cnj (b - a) * (c - a) = cnj (cnj (b - a) * (c - a))" by (simp add: complex_cnj_mult)
    thus "Im (cnj (b - a) * (c - a)) = 0" by (metis Reals_cnj_iff complex_is_Real_iff)
  qed
  finally show ?thesis using E by simp
qed

text \<open>Degenerate instances of collinearity, and its cyclic symmetry.\<close>

lemma collinear_refl: "collinear a b b"
  by (simp add: collinear_iff_cross algebra_simps)

lemma collinear_aba: "collinear a b a"
  by (simp add: collinear_iff_cross algebra_simps)

lemma collinear_aac: "collinear a a c"
  by (simp add: collinear_iff_cross algebra_simps)

lemma collinear_cycle:
  assumes "collinear a b c" shows "collinear b c a"
  using assms by (simp add: collinear_iff_cross algebra_simps)

text \<open>A non-collinear triple has three distinct vertices.\<close>

lemma ncol_distinct:
  assumes "\<not> collinear a b c" shows "a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c"
  using assms by (metis collinear_aac collinear_aba collinear_refl)


section \<open>Points on a circle\<close>

text \<open>On a circle, the squared distance to the centre is the constant
  \<^term>\<open>R\<^sup>2\<close>.\<close>

text \<open>The converse: the norm identity characterises membership of a circle of
  positive radius.\<close>

lemma oncircle_of_norm_sq:
  fixes z ctr :: complex and R :: real
  assumes h: "(z - ctr) * cnj (z - ctr) = complex_of_real (R^2)" and pos: "0 < R"
  shows "oncircle ctr R z"
proof -
  have "complex_of_real ((cmod (z - ctr))^2) = (z - ctr) * cnj (z - ctr)"
    by (rule complex_norm_square)
  also have "... = complex_of_real (R^2)" by (rule h)
  finally have "complex_of_real ((cmod (z - ctr))^2) = complex_of_real (R^2)" .
  hence "(cmod (z - ctr))^2 = R^2" by (simp only: of_real_eq_iff)
  hence "cmod (z - ctr) = R" using pos by (simp add: power2_eq_iff_nonneg)
  thus ?thesis by (simp add: oncircle_def)
qed

section \<open>The foot of a perpendicular\<close>

text \<open>Two elementary conjugate identities.\<close>

lemma of_real_Re_eq: "complex_of_real (Re z) = (z + cnj z)/2"
  by (simp add: complex_add_cnj)

lemma Re_sub_cnj_half_zero: "Re ((z - cnj z)/2) = 0"
  by (simp add: complex_diff_cnj)

text \<open>The parameter of the foot along the line, before any circle assumption.\<close>

lemma foot_ratio_gen:
  fixes a b m p q :: complex
  assumes "q \<noteq> 0" and "b - a \<noteq> 0"
  shows "((a + m)/2 + (b - a)*p/(2*q) - a)/(b - a) = ((m - a)/(b - a) + p/q)/2"
  using assms by (simp add: field_simps)

text \<open>A point lies on a line exactly when the displacement ratio is real.\<close>

lemma on_line_iff:
  assumes "a \<noteq> b" shows "on_line a b z = ((z - a)/(b - a) \<in> \<real>)"
proof -
  have hba: "b - a \<noteq> 0" using assms by simp
  show ?thesis
  proof
    assume "on_line a b z"
    then obtain t::real where "z = a + of_real t * (b - a)" unfolding on_line_def by blast
    hence "z - a = of_real t * (b - a)" by simp
    hence "(z - a)/(b - a) = of_real t" using hba by (simp add: field_simps)
    thus "(z - a)/(b - a) \<in> \<real>" by simp
  next
    assume "(z - a)/(b - a) \<in> \<real>"
    then obtain t::real where "(z - a)/(b - a) = of_real t" using Reals_cases by blast
    hence "z - a = of_real t * (b - a)" using hba by (simp add: field_simps)
    hence "z = a + of_real t * (b - a)" by (simp add: algebra_simps)
    thus "on_line a b z" unfolding on_line_def by blast
  qed
qed

text \<open>The foot lies on its line.\<close>

lemma foot_on_line:
  assumes "a \<noteq> b" shows "on_line a b (foot a b m)"
proof -
  have hba: "b - a \<noteq> 0" using assms by simp
  have hcba: "cnj (b - a) \<noteq> 0" using assms by simp
  have "(foot a b m - a)/(b - a) = ((m - a)/(b - a) + cnj (m - a)/cnj (b - a))/2"
    unfolding foot_def by (rule foot_ratio_gen[OF hcba hba])
  also have "... = ((m - a)/(b - a) + cnj ((m - a)/(b - a)))/2"
    by (simp add: complex_cnj_divide)
  also have "... = complex_of_real (Re ((m - a)/(b - a)))"
    by (simp add: of_real_Re_eq)
  finally have "(foot a b m - a)/(b - a) \<in> \<real>" by simp
  thus ?thesis using on_line_iff[OF assms] by simp
qed

text \<open>The segment from \<^term>\<open>m\<close> to its foot is perpendicular to the line.\<close>

lemma foot_perp:
  assumes "a \<noteq> b" shows "complex_perpendicular (b - a) (foot a b m - m)"
proof -
  have hba: "cnj (b - a) \<noteq> 0" using assms by simp
  have eq: "cnj (b - a) * (foot a b m - m) = ((b - a)*cnj (m - a) - cnj ((b - a)*cnj (m - a)))/2"
    unfolding foot_def using hba by (simp add: complex_cnj_mult field_simps)
  have "Re (cnj (b - a) * (foot a b m - m)) = 0"
    unfolding eq by (rule Re_sub_cnj_half_zero)
  thus ?thesis unfolding complex_perpendicular_def .
qed

text \<open>The preceding two properties uniquely characterise the perpendicular
  foot on every nondegenerate line.\<close>

lemma foot_unique:
  assumes ab: "a \<noteq> b"
    and zline: "on_line a b z"
    and zperp: "complex_perpendicular (b - a) (z - m)"
  shows "z = foot a b m"
proof -
  obtain t :: real where z: "z = a + of_real t * (b - a)"
    using zline unfolding on_line_def by blast
  have fline: "on_line a b (foot a b m)"
    by (rule foot_on_line[OF ab])
  then obtain s :: real where f: "foot a b m = a + of_real s * (b - a)"
    unfolding on_line_def by blast
  have fperp: "complex_perpendicular (b - a) (foot a b m - m)"
    by (rule foot_perp[OF ab])
  have hzero: "Re (cnj (b - a) * (z - foot a b m)) = 0"
    using zperp fperp unfolding complex_perpendicular_def
    by (simp add: algebra_simps)
  have hts:
      "(t - s) *
        (Re (b - a) * Re (b - a) + Im (b - a) * Im (b - a)) = 0"
    using hzero unfolding z f
    by (simp add: complex_mult_cnj algebra_simps)
  have hnorm:
      "Re (b - a) * Re (b - a) + Im (b - a) * Im (b - a) \<noteq> 0"
    using ab
    by (auto simp: sum_squares_eq_zero_iff power2_eq_square complex_eq_iff)
  have "t - s = 0"
    using hts hnorm by (auto simp: mult_eq_0_iff)
  hence "t = s" by simp
  thus ?thesis unfolding z f by simp
qed


section \<open>Feet of the three perpendiculars from a point on the circle\<close>

text \<open>Rewriting the foot when \<^term>\<open>a\<close> and \<^term>\<open>b\<close> lie on the circle: a pure
  field identity supporting the geometric rewrite that follows.\<close>

lemma foot_general_gen:
  fixes A B mu k :: complex
  assumes "A \<noteq> 0" and "B \<noteq> 0" and "A \<noteq> B" and "k \<noteq> 0"
  shows "(B - A)*(mu - k/A)/(2*(k/B - k/A)) = B*(k - mu*A)/(2*k)"
  using assms by (simp add: field_simps)

text \<open>Closed form for the foot when both line endpoints lie on the circle of
  centre \<^term>\<open>ctr\<close> and radius \<^term>\<open>r\<close>.\<close>

lemma foot_general:
  fixes a b m ctr :: complex and r :: real
  assumes ha: "oncircle ctr r a" and hb: "oncircle ctr r b" and pos: "0 < r" and dab: "a \<noteq> b"
  shows "foot a b m = ctr + (a - ctr + (m - ctr))/2 + (b - ctr)*(complex_of_real (r^2) - cnj (m - ctr)*(a - ctr))/(2*complex_of_real (r^2))"
proof -
  have Ane: "a - ctr \<noteq> 0" using oncircle_ne_centre[OF ha pos] by simp
  have Bne: "b - ctr \<noteq> 0" using oncircle_ne_centre[OF hb pos] by simp
  have AB: "a - ctr \<noteq> b - ctr" using dab by simp
  have R2ne: "complex_of_real (r^2) \<noteq> 0" using pos by simp
  have cnjA: "cnj (a - ctr) = complex_of_real (r^2)/(a - ctr)" using cnj_diff_on_circle[OF ha pos] .
  have cnjB: "cnj (b - ctr) = complex_of_real (r^2)/(b - ctr)" using cnj_diff_on_circle[OF hb pos] .
  have e1: "cnj (m - a) = cnj (m - ctr) - complex_of_real (r^2)/(a - ctr)"
  proof -
    have "cnj (m - a) = cnj (m - ctr) - cnj (a - ctr)" by (simp add: complex_cnj_diff)
    also have "... = cnj (m - ctr) - complex_of_real (r^2)/(a - ctr)" by (subst cnjA) (rule refl)
    finally show ?thesis .
  qed
  have e2: "cnj (b - a) = complex_of_real (r^2)/(b - ctr) - complex_of_real (r^2)/(a - ctr)"
  proof -
    have "cnj (b - a) = cnj (b - ctr) - cnj (a - ctr)" by (simp add: complex_cnj_diff)
    also have "... = complex_of_real (r^2)/(b - ctr) - complex_of_real (r^2)/(a - ctr)" by (simp only: cnjA cnjB)
    finally show ?thesis .
  qed
  have e3: "b - a = (b - ctr) - (a - ctr)" by simp
  have g:
    "((b - ctr) - (a - ctr)) *
       (cnj (m - ctr) - complex_of_real (r^2) / (a - ctr)) /
       (2 * (complex_of_real (r^2) / (b - ctr) -
         complex_of_real (r^2) / (a - ctr)))
     = (b - ctr) *
         (complex_of_real (r^2) - cnj (m - ctr) * (a - ctr)) /
         (2 * complex_of_real (r^2))"
    by (rule foot_general_gen[OF Ane Bne AB R2ne])
  have num: "(b - a)*cnj (m - a) = ((b - ctr) - (a - ctr))*(cnj (m - ctr) - complex_of_real (r^2)/(a - ctr))"
    by (simp only: e3 e1)
  have den: "2*cnj (b - a) = 2*(complex_of_real (r^2)/(b - ctr) - complex_of_real (r^2)/(a - ctr))"
    by (simp only: e2)
  have key: "(b - a)*cnj (m - a)/(2*cnj (b - a)) = (b - ctr)*(complex_of_real (r^2) - cnj (m - ctr)*(a - ctr))/(2*complex_of_real (r^2))"
  proof -
    have
      "(b - a) * cnj (m - a) / (2 * cnj (b - a))
       = ((b - ctr) - (a - ctr)) *
           (cnj (m - ctr) - complex_of_real (r^2) / (a - ctr)) /
           (2 * (complex_of_real (r^2) / (b - ctr) -
             complex_of_real (r^2) / (a - ctr)))"
      by (simp only: num den)
    also have "... = (b - ctr)*(complex_of_real (r^2) - cnj (m - ctr)*(a - ctr))/(2*complex_of_real (r^2))"
      by (rule g)
    finally show ?thesis .
  qed
  have "foot a b m = (a + m)/2 + (b - a)*cnj (m - a)/(2*cnj (b - a))"
    unfolding foot_def by simp
  also have "... = (a + m)/2 + (b - ctr)*(complex_of_real (r^2) - cnj (m - ctr)*(a - ctr))/(2*complex_of_real (r^2))"
    using key by simp
  also have "... = ctr + (a - ctr + (m - ctr))/2 + (b - ctr)*(complex_of_real (r^2) - cnj (m - ctr)*(a - ctr))/(2*complex_of_real (r^2))"
    by (simp add: field_simps)
  finally show ?thesis .
qed

text \<open>The difference of the feet on \<^term>\<open>BC\<close> and \<^term>\<open>AB\<close>.\<close>

lemma foot_diff_PR:
  fixes a b c m ctr :: complex and r :: real
  assumes ha: "oncircle ctr r a" and hb: "oncircle ctr r b" and hc: "oncircle ctr r c"
    and pos: "0 < r" and dab: "a \<noteq> b" and dbc: "b \<noteq> c"
  shows "foot b c m - foot a b m = (c - a)*(complex_of_real (r^2) - cnj (m - ctr)*(b - ctr))/(2*complex_of_real (r^2))"
proof -
  have R2ne: "complex_of_real (r^2) \<noteq> 0" using pos by simp
  have fbc: "foot b c m = ctr + (b - ctr + (m - ctr))/2 + (c - ctr)*(complex_of_real (r^2) - cnj (m - ctr)*(b - ctr))/(2*complex_of_real (r^2))"
    by (rule foot_general[OF hb hc pos dbc])
  have fab: "foot a b m = ctr + (a - ctr + (m - ctr))/2 + (b - ctr)*(complex_of_real (r^2) - cnj (m - ctr)*(a - ctr))/(2*complex_of_real (r^2))"
    by (rule foot_general[OF ha hb pos dab])
  show ?thesis unfolding fbc fab using R2ne by (simp add: field_simps)
qed

text \<open>The difference of the feet on \<^term>\<open>CA\<close> and \<^term>\<open>AB\<close>.\<close>

lemma foot_diff_QR:
  fixes a b c m ctr :: complex and r :: real
  assumes ha: "oncircle ctr r a" and hb: "oncircle ctr r b" and hc: "oncircle ctr r c"
    and pos: "0 < r" and dab: "a \<noteq> b" and dca: "c \<noteq> a"
  shows "foot c a m - foot a b m = (c - b)*(complex_of_real (r^2) - cnj (m - ctr)*(a - ctr))/(2*complex_of_real (r^2))"
proof -
  have R2ne: "complex_of_real (r^2) \<noteq> 0" using pos by simp
  have fca: "foot c a m = ctr + (c - ctr + (m - ctr))/2 + (a - ctr)*(complex_of_real (r^2) - cnj (m - ctr)*(c - ctr))/(2*complex_of_real (r^2))"
    by (rule foot_general[OF hc ha pos dca])
  have fab: "foot a b m = ctr + (a - ctr + (m - ctr))/2 + (b - ctr)*(complex_of_real (r^2) - cnj (m - ctr)*(a - ctr))/(2*complex_of_real (r^2))"
    by (rule foot_general[OF ha hb pos dab])
  show ?thesis unfolding fca fab using R2ne by (simp add: field_simps)
qed

text \<open>On the circle, \<^term>\<open>complex_of_real (r^2) - cnj (m - ctr)*(z - ctr)\<close>
  factors through \<^term>\<open>m - z\<close>.\<close>

lemma circle_factor:
  assumes hm: "oncircle ctr r m" and pos: "0 < r"
  shows "complex_of_real (r^2) - cnj (m - ctr)*(z - ctr) = complex_of_real (r^2)*(m - z)/(m - ctr)"
proof -
  have Mne: "m - ctr \<noteq> 0" using oncircle_ne_centre[OF hm pos] by simp
  have cnjM: "cnj (m - ctr) = complex_of_real (r^2)/(m - ctr)" using cnj_diff_on_circle[OF hm pos] .
  have "complex_of_real (r^2) - cnj (m - ctr)*(z - ctr) = complex_of_real (r^2) - complex_of_real (r^2)/(m - ctr)*(z - ctr)"
    by (subst cnjM) (rule refl)
  also have "... = complex_of_real (r^2)*(m - z)/(m - ctr)" using Mne by (simp add: field_simps)
  finally show ?thesis .
qed

text \<open>When \<^term>\<open>m\<close> too lies on the circle, the two foot differences take a
  particularly clean form.\<close>

lemma foot_diff_PR_circ:
  assumes ha: "oncircle ctr r a" and hb: "oncircle ctr r b" and hc: "oncircle ctr r c"
    and hm: "oncircle ctr r m" and pos: "0 < r" and dab: "a \<noteq> b" and dbc: "b \<noteq> c"
  shows "foot b c m - foot a b m = (c - a)*(m - b)/(2*(m - ctr))"
proof -
  have R2ne: "complex_of_real (r^2) \<noteq> 0" using pos by simp
  have Mne: "m - ctr \<noteq> 0" using oncircle_ne_centre[OF hm pos] by simp
  have "foot b c m - foot a b m = (c - a)*(complex_of_real (r^2) - cnj (m - ctr)*(b - ctr))/(2*complex_of_real (r^2))"
    by (rule foot_diff_PR[OF ha hb hc pos dab dbc])
  also have "... = (c - a)*(complex_of_real (r^2)*(m - b)/(m - ctr))/(2*complex_of_real (r^2))"
    by (subst circle_factor[OF hm pos]) (rule refl)
  also have "... = (c - a)*(m - b)/(2*(m - ctr))" using R2ne Mne by (simp add: field_simps)
  finally show ?thesis .
qed

lemma foot_diff_QR_circ:
  assumes ha: "oncircle ctr r a" and hb: "oncircle ctr r b" and hc: "oncircle ctr r c"
    and hm: "oncircle ctr r m" and pos: "0 < r" and dab: "a \<noteq> b" and dca: "c \<noteq> a"
  shows "foot c a m - foot a b m = (c - b)*(m - a)/(2*(m - ctr))"
proof -
  have R2ne: "complex_of_real (r^2) \<noteq> 0" using pos by simp
  have Mne: "m - ctr \<noteq> 0" using oncircle_ne_centre[OF hm pos] by simp
  have "foot c a m - foot a b m = (c - b)*(complex_of_real (r^2) - cnj (m - ctr)*(a - ctr))/(2*complex_of_real (r^2))"
    by (rule foot_diff_QR[OF ha hb hc pos dab dca])
  also have "... = (c - b)*(complex_of_real (r^2)*(m - a)/(m - ctr))/(2*complex_of_real (r^2))"
    by (subst circle_factor[OF hm pos]) (rule refl)
  also have "... = (c - b)*(m - a)/(2*(m - ctr))" using R2ne Mne by (simp add: field_simps)
  finally show ?thesis .
qed


section \<open>The Wallace-Simson line\<close>

text \<open>Forward direction: if \<^term>\<open>m\<close> lies on the circumcircle of the
  nondegenerate triangle \<^term>\<open>a\<close>, \<^term>\<open>b\<close>, \<^term>\<open>c\<close>, then the three feet of
  the perpendiculars from \<^term>\<open>m\<close> to the side lines are collinear.  The key
  step is that the ratio of two foot differences equals a cross ratio of four
  concyclic points, hence is real.\<close>

theorem simson_line:
  fixes a b c m ctr :: complex and r :: real
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle ctr r a" and hb: "oncircle ctr r b" and hc: "oncircle ctr r c"
    and hm: "oncircle ctr r m" and pos: "0 < r"
  shows "collinear (foot b c m) (foot c a m) (foot a b m)"
proof -
  have dist: "a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c" using ncol_distinct[OF hncol] .
  have dab: "a \<noteq> b" and dac: "a \<noteq> c" and dbc: "b \<noteq> c" using dist by auto
  have dca: "c \<noteq> a" using dac by simp
  have Mne: "m - ctr \<noteq> 0" using oncircle_ne_centre[OF hm pos] by simp
  have hPR: "foot b c m - foot a b m = (c - a)*(m - b)/(2*(m - ctr))"
    by (rule foot_diff_PR_circ[OF ha hb hc hm pos dab dbc])
  have hQR: "foot c a m - foot a b m = (c - b)*(m - a)/(2*(m - ctr))"
    by (rule foot_diff_QR_circ[OF ha hb hc hm pos dab dca])
  show ?thesis
  proof (cases "m = a")
    case True
    have "foot c a m - foot a b m = 0" using hQR True by simp
    hence "foot c a m = foot a b m" by simp
    thus ?thesis by (simp add: collinear_refl)
  next
    case False
    hence dma: "m \<noteq> a" by simp
    have dcb: "c \<noteq> b" using dbc by simp
    have Bne: "(c - b)*(m - a) \<noteq> 0" using dcb dma by simp
    have D2ne: "2*(m - ctr) \<noteq> 0" using Mne by simp
    have RQ: "foot a b m \<noteq> foot c a m"
    proof
      assume "foot a b m = foot c a m"
      hence "(c - b)*(m - a)/(2*(m - ctr)) = 0" using hQR by simp
      thus False using Bne Mne by simp
    qed
    have ratio: "(foot b c m - foot a b m)/(foot c a m - foot a b m) = complex_cross_ratio c m a b"
    proof -
      have "(foot b c m - foot a b m)/(foot c a m - foot a b m) = ((c - a)*(m - b)/(2*(m - ctr)))/((c - b)*(m - a)/(2*(m - ctr)))"
        using hPR hQR by simp
      also have "... = (c - a)*(m - b)/((c - b)*(m - a))"
        using D2ne by simp
      also have "... = complex_cross_ratio c m a b"
        by (simp add: complex_cross_ratio_def)
      finally show ?thesis .
    qed
    have cr_real: "complex_cross_ratio c m a b \<in> \<real>"
      by (rule concyclic_complex_cross_ratio_real[OF hc hm ha hb pos dcb dma])
    have "(foot b c m - foot a b m)/(foot c a m - foot a b m) \<in> \<real>"
      using ratio cr_real by simp
    hence "collinear (foot a b m) (foot b c m) (foot c a m)"
      using collinear_iff_real_ratio[OF RQ] by simp
    thus ?thesis by (rule collinear_cycle)
  qed
qed


section \<open>The converse\<close>

text \<open>A field identity that clears the three circle denominators from the
  collinearity relation of the feet.  It is stated over an arbitrary field so
  that the algebraic simplification can be discharged uniformly.\<close>

lemma converse_key_gen:
  fixes A B C ca cb cc R D cm :: "'a::field"
  assumes A0: "A \<noteq> 0" and B0: "B \<noteq> 0" and C0: "C \<noteq> 0"
    and hA: "A * ca = R" and hB: "B * cb = R" and hC: "C * cc = R"
  shows
    "A * B * C *
       ((cc - ca) * (R - D * cb) * (C - B) * (R - cm * A) -
        (C - A) * (R - cm * B) * (cc - cb) * (R - D * ca))
     = R^2 * (A - B) * (A - C) * (B - C) * (R - cm * D)"
proof -
  have ca: "ca = R / A" using hA A0 by (simp add: field_simps)
  have cb: "cb = R / B" using hB B0 by (simp add: field_simps)
  have cc: "cc = R / C" using hC C0 by (simp add: field_simps)
  show ?thesis unfolding ca cb cc using A0 B0 C0 by (simp add: field_simps) (simp add: algebra_simps power2_eq_square)
qed

text \<open>Specialised to the circle, with the conjugate substitutions folded back
  into differences of the original points.\<close>

lemma converse_key_complex:
  fixes a b c m ctr :: complex and r :: real
  assumes Ane: "a - ctr \<noteq> 0" and Bne: "b - ctr \<noteq> 0" and Cne: "c - ctr \<noteq> 0"
    and hA: "(a - ctr)*cnj (a - ctr) = complex_of_real (r^2)"
    and hB: "(b - ctr)*cnj (b - ctr) = complex_of_real (r^2)"
    and hC: "(c - ctr)*cnj (c - ctr) = complex_of_real (r^2)"
  shows
    "(a - ctr) * (b - ctr) * (c - ctr) *
       (cnj (c - a) *
          (complex_of_real (r^2) - (m - ctr) * cnj (b - ctr)) *
          (c - b) *
          (complex_of_real (r^2) - cnj (m - ctr) * (a - ctr)) -
        (c - a) *
          (complex_of_real (r^2) - cnj (m - ctr) * (b - ctr)) *
          cnj (c - b) *
          (complex_of_real (r^2) - (m - ctr) * cnj (a - ctr)))
     = (complex_of_real (r^2))^2 * (a - b) * (a - c) * (b - c) *
         (complex_of_real (r^2) - cnj (m - ctr) * (m - ctr))"
proof -
  have key:
    "(a - ctr) * (b - ctr) * (c - ctr) *
       ((cnj (c - ctr) - cnj (a - ctr)) *
          (complex_of_real (r^2) - (m - ctr) * cnj (b - ctr)) *
          ((c - ctr) - (b - ctr)) *
          (complex_of_real (r^2) - cnj (m - ctr) * (a - ctr)) -
        ((c - ctr) - (a - ctr)) *
          (complex_of_real (r^2) - cnj (m - ctr) * (b - ctr)) *
          (cnj (c - ctr) - cnj (b - ctr)) *
          (complex_of_real (r^2) - (m - ctr) * cnj (a - ctr)))
     = (complex_of_real (r^2))^2 *
         ((a - ctr) - (b - ctr)) *
         ((a - ctr) - (c - ctr)) *
         ((b - ctr) - (c - ctr)) *
         (complex_of_real (r^2) - cnj (m - ctr) * (m - ctr))"
    by (rule converse_key_gen[OF Ane Bne Cne hA hB hC])
  have g1: "cnj(c-ctr)-cnj(a-ctr) = cnj(c-a)" by (simp add: complex_cnj_diff)
  have g4: "cnj(c-ctr)-cnj(b-ctr) = cnj(c-b)" by (simp add: complex_cnj_diff)
  have g2: "(c-ctr)-(b-ctr) = c-b" by simp
  have g3: "(c-ctr)-(a-ctr) = c-a" by simp
  have g5: "(a-ctr)-(b-ctr) = a-b" by simp
  have g6: "(a-ctr)-(c-ctr) = a-c" by simp
  have g7: "(b-ctr)-(c-ctr) = b-c" by simp
  show ?thesis using key by (simp only: g1 g4 g2 g3 g5 g6 g7)
qed

text \<open>Converse direction: if the three feet of the perpendiculars from
  \<^term>\<open>m\<close> to the side lines of the nondegenerate triangle are collinear, then
  \<^term>\<open>m\<close> lies on the circumcircle.\<close>

theorem simson_line_converse:
  fixes a b c m ctr :: complex and r :: real
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle ctr r a" and hb: "oncircle ctr r b" and hc: "oncircle ctr r c"
    and pos: "0 < r"
    and hcol: "collinear (foot b c m) (foot c a m) (foot a b m)"
  shows "oncircle ctr r m"
proof -
  have dist: "a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c" using ncol_distinct[OF hncol] .
  have dab: "a \<noteq> b" and dac: "a \<noteq> c" and dbc: "b \<noteq> c" using dist by auto
  have dca: "c \<noteq> a" using dac by simp
  have Ane: "a - ctr \<noteq> 0" using oncircle_ne_centre[OF ha pos] by simp
  have Bne: "b - ctr \<noteq> 0" using oncircle_ne_centre[OF hb pos] by simp
  have Cne: "c - ctr \<noteq> 0" using oncircle_ne_centre[OF hc pos] by simp
  have R2ne: "complex_of_real (r^2) \<noteq> 0" using pos by simp
  have hA: "(a - ctr)*cnj (a - ctr) = complex_of_real (r^2)" using oncircle_norm_sq[OF ha] .
  have hB: "(b - ctr)*cnj (b - ctr) = complex_of_real (r^2)" using oncircle_norm_sq[OF hb] .
  have hC: "(c - ctr)*cnj (c - ctr) = complex_of_real (r^2)" using oncircle_norm_sq[OF hc] .
  have hPR: "foot b c m - foot a b m = (c - a)*(complex_of_real (r^2) - cnj (m - ctr)*(b - ctr))/(2*complex_of_real (r^2))"
    by (rule foot_diff_PR[OF ha hb hc pos dab dbc])
  have hQR: "foot c a m - foot a b m = (c - b)*(complex_of_real (r^2) - cnj (m - ctr)*(a - ctr))/(2*complex_of_real (r^2))"
    by (rule foot_diff_QR[OF ha hb hc pos dab dca])
  have col2: "collinear (foot a b m) (foot b c m) (foot c a m)"
    using collinear_cycle[OF collinear_cycle[OF hcol]] .
  have Imraw: "Im (cnj (foot b c m - foot a b m) * (foot c a m - foot a b m)) = 0"
    using col2 by (simp add: collinear_iff_cross)
  have cross: "cnj (foot b c m - foot a b m) * (foot c a m - foot a b m) = (foot b c m - foot a b m) * cnj (foot c a m - foot a b m)"
    by (rule im_zero_cross[OF Imraw])
  have inner0:
    "cnj (c - a) *
       (complex_of_real (r^2) - (m - ctr) * cnj (b - ctr)) *
       (c - b) *
       (complex_of_real (r^2) - cnj (m - ctr) * (a - ctr)) -
     (c - a) *
       (complex_of_real (r^2) - cnj (m - ctr) * (b - ctr)) *
       cnj (c - b) *
       (complex_of_real (r^2) - (m - ctr) * cnj (a - ctr))
     = 0"
    using cross[unfolded hPR hQR] R2ne by (simp add: complex_cnj_divide complex_cnj_mult complex_cnj_diff field_simps)
  have keyeq:
    "(a - ctr) * (b - ctr) * (c - ctr) *
       (cnj (c - a) *
          (complex_of_real (r^2) - (m - ctr) * cnj (b - ctr)) *
          (c - b) *
          (complex_of_real (r^2) - cnj (m - ctr) * (a - ctr)) -
        (c - a) *
          (complex_of_real (r^2) - cnj (m - ctr) * (b - ctr)) *
          cnj (c - b) *
          (complex_of_real (r^2) - (m - ctr) * cnj (a - ctr)))
     = (complex_of_real (r^2))^2 * (a - b) * (a - c) * (b - c) *
         (complex_of_real (r^2) - cnj (m - ctr) * (m - ctr))"
    by (rule converse_key_complex[OF Ane Bne Cne hA hB hC])
  have RHS0: "(complex_of_real (r^2))^2*(a - b)*(a - c)*(b - c)*(complex_of_real (r^2) - cnj (m - ctr)*(m - ctr)) = 0"
    using keyeq inner0 by simp
  have abcne: "(a - b)*(a - c)*(b - c) \<noteq> 0" using dab dac dbc by simp
  have zero: "complex_of_real (r^2) - cnj (m - ctr)*(m - ctr) = 0"
    using RHS0 R2ne abcne by simp
  have "(m - ctr)*cnj (m - ctr) = complex_of_real (r^2)"
    using zero by (simp add: mult.commute)
  thus "oncircle ctr r m" by (rule oncircle_of_norm_sq[OF _ pos])
qed

text \<open>The two directions combine into the usual characterisation of the
  circumcircle by collinearity of the three perpendicular feet.\<close>

theorem simson_line_iff:
  fixes a b c m ctr :: complex and r :: real
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle ctr r a" and hb: "oncircle ctr r b" and hc: "oncircle ctr r c"
    and pos: "0 < r"
  shows
    "oncircle ctr r m \<longleftrightarrow>
      collinear (foot b c m) (foot c a m) (foot a b m)"
proof
  assume hm: "oncircle ctr r m"
  show "collinear (foot b c m) (foot c a m) (foot a b m)"
    by (rule simson_line[OF hncol ha hb hc hm pos])
next
  assume hcol: "collinear (foot b c m) (foot c a m) (foot a b m)"
  show "oncircle ctr r m"
    by (rule simson_line_converse[OF hncol ha hb hc pos hcol])
qed

end
