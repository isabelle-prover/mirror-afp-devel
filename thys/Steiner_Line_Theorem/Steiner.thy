(*  Title:      Steiner.thy
    Author:     Arthur Freitas Ramos, David Barros Hulak,
                Ruy Jose Guerra Barretto de Queiroz, 2026
    Maintainer: Arthur Freitas Ramos

The Steiner line theorem.

For a point on the circumcircle of a nondegenerate triangle, the reflections
of the point in the three sidelines are collinear.  The resulting line passes
through the orthocenter of the triangle.
*)

theory Steiner
  imports "Simson.Simson"
begin

section \<open>Reflections and the orthocenter\<close>

text \<open>The reflection of a point in a sideline is twice its perpendicular
  foot, minus the original point.\<close>

definition steiner_reflect :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex"
  where "steiner_reflect a b m = 2 * foot a b m - m"

text \<open>In circumcentre coordinates the orthocenter is the sum of the three
  vertex vectors.\<close>

definition orthocenter ::
    "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex"
  where "orthocenter a b c ctr = a + b + c - 2 * ctr"

text \<open>The coordinate formula gives the altitude-perpendicularity identities
  directly from the equal circumradius equations.  Thus this algebraic lemma
  does not need the non-collinearity or positive-radius assumptions; those
  hypotheses are imposed by the triangle theorems below.\<close>

lemma orthocenter_is_orthocenter:
  fixes a b c ctr :: complex and r :: real
  assumes ha: "oncircle ctr r a" and hb: "oncircle ctr r b"
    and hc: "oncircle ctr r c"
  shows "complex_perpendicular (c - b)
      (orthocenter a b c ctr - a) \<and>
    complex_perpendicular (a - c)
      (orthocenter a b c ctr - b) \<and>
    complex_perpendicular (b - a)
      (orthocenter a b c ctr - c)"
proof -
  have hA: "(a - ctr) * cnj (a - ctr) = complex_of_real (r^2)"
    using oncircle_norm_sq[OF ha] .
  have hB: "(b - ctr) * cnj (b - ctr) = complex_of_real (r^2)"
    using oncircle_norm_sq[OF hb] .
  have hC: "(c - ctr) * cnj (c - ctr) = complex_of_real (r^2)"
    using oncircle_norm_sq[OF hc] .
  have alt_a:
      "complex_perpendicular (c - b)
        (orthocenter a b c ctr - a)"
  proof -
    have hnorm:
        "(c - ctr) * cnj (c - ctr) =
          (b - ctr) * cnj (b - ctr)"
      using hB hC by simp
    have eq:
        "cnj (c - b) * (orthocenter a b c ctr - a) =
          (cnj (c - ctr) * (b - ctr) -
            cnj (cnj (c - ctr) * (b - ctr))) +
          ((c - ctr) * cnj (c - ctr) -
            (b - ctr) * cnj (b - ctr))"
      by (simp add: orthocenter_def complex_cnj_diff complex_cnj_mult
          algebra_simps)
    have hcnj:
        "cnj ((cnj (c - ctr) * (b - ctr) -
            cnj (cnj (c - ctr) * (b - ctr))) +
          ((c - ctr) * cnj (c - ctr) -
            (b - ctr) * cnj (b - ctr))) =
          -((cnj (c - ctr) * (b - ctr) -
            cnj (cnj (c - ctr) * (b - ctr))) +
          ((c - ctr) * cnj (c - ctr) -
            (b - ctr) * cnj (b - ctr)))"
      using hnorm
      by (simp add: complex_cnj_diff complex_cnj_mult algebra_simps)
    have hzero:
        "Re ((cnj (c - ctr) * (b - ctr) -
            cnj (cnj (c - ctr) * (b - ctr))) +
          ((c - ctr) * cnj (c - ctr) -
            (b - ctr) * cnj (b - ctr))) = 0"
      using hcnj by (metis eq_minus_cnj_iff_imag)
    show ?thesis
      unfolding complex_perpendicular_def
      using eq hzero
      by (simp only: eq hzero)
  qed
  have alt_b:
      "complex_perpendicular (a - c)
        (orthocenter a b c ctr - b)"
  proof -
    have hnorm:
        "(a - ctr) * cnj (a - ctr) =
          (c - ctr) * cnj (c - ctr)"
      using hA hC by simp
    have eq:
        "cnj (a - c) * (orthocenter a b c ctr - b) =
          (cnj (a - ctr) * (c - ctr) -
            cnj (cnj (a - ctr) * (c - ctr))) +
          ((a - ctr) * cnj (a - ctr) -
            (c - ctr) * cnj (c - ctr))"
      by (simp add: orthocenter_def complex_cnj_diff complex_cnj_mult
          algebra_simps)
    have hcnj:
        "cnj ((cnj (a - ctr) * (c - ctr) -
            cnj (cnj (a - ctr) * (c - ctr))) +
          ((a - ctr) * cnj (a - ctr) -
            (c - ctr) * cnj (c - ctr))) =
          -((cnj (a - ctr) * (c - ctr) -
            cnj (cnj (a - ctr) * (c - ctr))) +
          ((a - ctr) * cnj (a - ctr) -
            (c - ctr) * cnj (c - ctr)))"
      using hnorm
      by (simp add: complex_cnj_diff complex_cnj_mult algebra_simps)
    have hzero:
        "Re ((cnj (a - ctr) * (c - ctr) -
            cnj (cnj (a - ctr) * (c - ctr))) +
          ((a - ctr) * cnj (a - ctr) -
            (c - ctr) * cnj (c - ctr))) = 0"
      using hcnj by (metis eq_minus_cnj_iff_imag)
    show ?thesis
      unfolding complex_perpendicular_def
      using eq hzero
      by (simp only: eq hzero)
  qed
  have alt_c:
      "complex_perpendicular (b - a)
        (orthocenter a b c ctr - c)"
  proof -
    have hnorm:
        "(b - ctr) * cnj (b - ctr) =
          (a - ctr) * cnj (a - ctr)"
      using hB hA by simp
    have eq:
        "cnj (b - a) * (orthocenter a b c ctr - c) =
          (cnj (b - ctr) * (a - ctr) -
            cnj (cnj (b - ctr) * (a - ctr))) +
          ((b - ctr) * cnj (b - ctr) -
            (a - ctr) * cnj (a - ctr))"
      by (simp add: orthocenter_def complex_cnj_diff complex_cnj_mult
          algebra_simps)
    have hcnj:
        "cnj ((cnj (b - ctr) * (a - ctr) -
            cnj (cnj (b - ctr) * (a - ctr))) +
          ((b - ctr) * cnj (b - ctr) -
            (a - ctr) * cnj (a - ctr))) =
          -((cnj (b - ctr) * (a - ctr) -
            cnj (cnj (b - ctr) * (a - ctr))) +
          ((b - ctr) * cnj (b - ctr) -
            (a - ctr) * cnj (a - ctr)))"
      using hnorm
      by (simp add: complex_cnj_diff complex_cnj_mult algebra_simps)
    have hzero:
        "Re ((cnj (b - ctr) * (a - ctr) -
            cnj (cnj (b - ctr) * (a - ctr))) +
          ((b - ctr) * cnj (b - ctr) -
            (a - ctr) * cnj (a - ctr))) = 0"
      using hcnj by (metis eq_minus_cnj_iff_imag)
    show ?thesis
      unfolding complex_perpendicular_def
      using eq hzero
      by (simp only: eq hzero)
  qed
  show ?thesis using alt_a alt_b alt_c by blast
qed

lemma steiner_reflect_unfold:
  assumes "a \<noteq> b"
  shows "steiner_reflect a b m = a + (b - a) * cnj (m - a) / cnj (b - a)"
  using assms by (simp add: steiner_reflect_def foot_def field_simps)

lemma collinear_homothety:
  assumes "collinear p q r"
  shows "collinear (2 * p - m) (2 * q - m) (2 * r - m)"
  using assms by (simp add: collinear_iff_cross algebra_simps)

lemma im_zero_of_cnj_eq:
  assumes "cnj z = z"
  shows "Im z = 0"
  using assms by (metis Reals_cnj_iff complex_is_Real_iff)

section \<open>The circle formula for a reflected point\<close>

text \<open>This is the only field calculation needed to place the reflected point
  in circumcentre coordinates.\<close>

lemma steiner_reflect_ratio_gen:
  fixes B C M k :: complex
  assumes B0: "B \<noteq> 0" and C0: "C \<noteq> 0" and M0: "M \<noteq> 0"
    and BC: "B \<noteq> C" and k0: "k \<noteq> 0"
  shows "(C - B) * (k / M - k / B) / (k / C - k / B)
      = C * (M - B) / M"
  using assms by (simp add: divide_simps) algebra

lemma steiner_reflect_formula:
  fixes b c m ctr :: complex and r :: real
  assumes hb: "oncircle ctr r b" and hc: "oncircle ctr r c"
    and hm: "oncircle ctr r m" and pos: "0 < r" and bc: "b \<noteq> c"
  shows "steiner_reflect b c m =
      ctr + (b - ctr) + (c - ctr) -
        (b - ctr) * (c - ctr) / (m - ctr)"
proof -
  define B where "B = b - ctr"
  define C where "C = c - ctr"
  define M where "M = m - ctr"
  define k where "k = complex_of_real (r^2)"
  have B0: "B \<noteq> 0"
    using oncircle_ne_centre[OF hb pos] by (simp add: B_def)
  have C0: "C \<noteq> 0"
    using oncircle_ne_centre[OF hc pos] by (simp add: C_def)
  have M0: "M \<noteq> 0"
    using oncircle_ne_centre[OF hm pos] by (simp add: M_def)
  have BC: "B \<noteq> C" using bc by (simp add: B_def C_def)
  have k0: "k \<noteq> 0" using pos by (simp add: k_def)
  have cc: "cnj (c - ctr) = k / C"
    using cnj_diff_on_circle[OF hc pos] by (simp add: C_def k_def)
  have bb: "cnj (b - ctr) = k / B"
    using cnj_diff_on_circle[OF hb pos] by (simp add: B_def k_def)
  have mm: "cnj (m - ctr) = k / M"
    using cnj_diff_on_circle[OF hm pos] by (simp add: M_def k_def)
  have diff: "c - b = C - B" by (simp add: B_def C_def)
  have cb: "cnj (c - b) = k / C - k / B"
  proof -
    have "cnj (c - b) = cnj (c - ctr) - cnj (b - ctr)"
      by (simp only: complex_cnj_diff; algebra)
    also have "... = k / C - k / B" by (simp only: cc bb)
    finally show ?thesis .
  qed
  have cb_shift: "cnj (C - B) = k / C - k / B"
    using cb diff by (simp only: diff)
  have mb: "cnj (m - b) = k / M - k / B"
  proof -
    have "cnj (m - b) = cnj (m - ctr) - cnj (b - ctr)"
      by (simp only: complex_cnj_diff; algebra)
    also have "... = k / M - k / B" by (simp only: mm bb)
    finally show ?thesis .
  qed
  have ratio:
      "(c - b) * cnj (m - b) / cnj (c - b) = C * (M - B) / M"
  proof -
    have gen:
        "(C - B) * (k / M - k / B) / (k / C - k / B)
            = C * (M - B) / M"
      by (rule steiner_reflect_ratio_gen[OF B0 C0 M0 BC k0])
    have step:
        "(c - b) * cnj (m - b) / cnj (c - b) =
          (C - B) * (k / M - k / B) / (k / C - k / B)"
      by (simp only: cb cb_shift mb diff)
    show ?thesis
      using step gen by (simp only: step gen)
  qed
  have hu: "steiner_reflect b c m = b + (c - b) * cnj (m - b) / cnj (c - b)"
    by (rule steiner_reflect_unfold[OF bc])
  have hsteiner:
      "steiner_reflect b c m = b + C * (M - B) / M"
    using hu ratio by (simp add: hu ratio)
  have frac: "C * (M - B) / M = C - B * C / M"
    using M0 by (simp add: field_simps M0 algebra_simps)
  have hcalc: "b + C * (M - B) / M = ctr + B + C - B * C / M"
    using frac by (simp add: B_def algebra_simps)
  show ?thesis
    using hsteiner hcalc by (simp add: B_def C_def M_def)
qed

section \<open>The orthocenter incidence calculation\<close>

lemma steiner_orthocenter_cross_gen:
  fixes A B C M k :: complex
  assumes A0: "A \<noteq> 0" and B0: "B \<noteq> 0" and C0: "C \<noteq> 0"
    and M0: "M \<noteq> 0"
    and hA: "A * cnj A = k" and hB: "B * cnj B = k"
    and hC: "C * cnj C = k" and hM: "M * cnj M = k"
  shows "cnj (C + A - C * A / M - (A + B + C)) *
      (B + C - B * C / M - (A + B + C)) =
    (C + A - C * A / M - (A + B + C)) *
      cnj (B + C - B * C / M - (A + B + C))"
proof -
  have cA: "cnj A = k / A" using hA A0 by (simp add: field_simps)
  have cB: "cnj B = k / B" using hB B0 by (simp add: field_simps)
  have cC: "cnj C = k / C" using hC C0 by (simp add: field_simps)
  have cM: "cnj M = k / M" using hM M0 by (simp add: field_simps)
  show ?thesis
    using A0 B0 C0 M0
    by (simp add: cA cB cC cM complex_cnj_diff complex_cnj_mult
        complex_cnj_divide divide_simps field_simps)
qed

lemma steiner_orthocenter_collinear:
  fixes a b c m ctr :: complex and r :: real
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle ctr r a" and hb: "oncircle ctr r b"
    and hc: "oncircle ctr r c" and hm: "oncircle ctr r m"
    and pos: "0 < r"
  shows "collinear (orthocenter a b c ctr)
      (steiner_reflect b c m) (steiner_reflect c a m)"
proof -
  have dist: "a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c"
    using ncol_distinct[OF hncol] .
  have ab: "a \<noteq> b" and ac: "a \<noteq> c" and bc: "b \<noteq> c"
    using dist by auto
  have ca: "c \<noteq> a" using ac by simp
  define A where "A = a - ctr"
  define B where "B = b - ctr"
  define C where "C = c - ctr"
  define M where "M = m - ctr"
  define k where "k = complex_of_real (r^2)"
  have A0: "A \<noteq> 0"
    using oncircle_ne_centre[OF ha pos] by (simp add: A_def)
  have B0: "B \<noteq> 0"
    using oncircle_ne_centre[OF hb pos] by (simp add: B_def)
  have C0: "C \<noteq> 0"
    using oncircle_ne_centre[OF hc pos] by (simp add: C_def)
  have M0: "M \<noteq> 0"
    using oncircle_ne_centre[OF hm pos] by (simp add: M_def)
  have hA: "A * cnj A = k"
    using oncircle_norm_sq[OF ha] by (simp add: A_def k_def)
  have hB: "B * cnj B = k"
    using oncircle_norm_sq[OF hb] by (simp add: B_def k_def)
  have hC: "C * cnj C = k"
    using oncircle_norm_sq[OF hc] by (simp add: C_def k_def)
  have hM: "M * cnj M = k"
    using oncircle_norm_sq[OF hm] by (simp add: M_def k_def)
  have ra: "steiner_reflect b c m =
      ctr + B + C - B * C / M"
    using steiner_reflect_formula[OF hb hc hm pos bc]
    by (simp add: B_def C_def M_def)
  have rb: "steiner_reflect c a m =
      ctr + C + A - C * A / M"
    using steiner_reflect_formula[OF hc ha hm pos ca]
    by (simp add: A_def C_def M_def)
  have cross:
      "cnj ((C + A - C * A / M) - (A + B + C)) *
          ((B + C - B * C / M) - (A + B + C)) =
        ((C + A - C * A / M) - (A + B + C)) *
          cnj ((B + C - B * C / M) - (A + B + C))"
    by (rule steiner_orthocenter_cross_gen[OF A0 B0 C0 M0 hA hB hC hM])
  have cross':
      "cnj (steiner_reflect c a m - orthocenter a b c ctr) *
          (steiner_reflect b c m - orthocenter a b c ctr) =
        (steiner_reflect c a m - orthocenter a b c ctr) *
          cnj (steiner_reflect b c m - orthocenter a b c ctr)"
    using cross
    by (simp add: ra rb orthocenter_def A_def B_def C_def M_def algebra_simps)
  show ?thesis
  proof -
    have self:
        "cnj (cnj (steiner_reflect c a m - orthocenter a b c ctr) *
            (steiner_reflect b c m - orthocenter a b c ctr)) =
          cnj (steiner_reflect c a m - orthocenter a b c ctr) *
            (steiner_reflect b c m - orthocenter a b c ctr)"
      using cross' by (simp add: complex_cnj_mult)
    have self':
        "cnj (cnj (steiner_reflect b c m - orthocenter a b c ctr) *
            (steiner_reflect c a m - orthocenter a b c ctr)) =
          cnj (steiner_reflect b c m - orthocenter a b c ctr) *
            (steiner_reflect c a m - orthocenter a b c ctr)"
      using self by (simp add: complex_cnj_mult algebra_simps)
    have hIm:
        "Im (cnj (steiner_reflect b c m - orthocenter a b c ctr) *
          (steiner_reflect c a m - orthocenter a b c ctr)) = 0"
      using self' by (rule im_zero_of_cnj_eq)
    show ?thesis using hIm by (simp only: collinear_iff_cross)
  qed
qed

section \<open>Steiner's line theorem\<close>

text \<open>The reflections in the three sidelines are collinear.\<close>

theorem steiner_line:
  fixes a b c m ctr :: complex and r :: real
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle ctr r a" and hb: "oncircle ctr r b"
    and hc: "oncircle ctr r c" and hm: "oncircle ctr r m"
    and pos: "0 < r"
  shows "collinear (steiner_reflect b c m)
      (steiner_reflect c a m) (steiner_reflect a b m)"
proof -
  have hsim: "collinear (foot b c m) (foot c a m) (foot a b m)"
    by (rule simson_line[OF hncol ha hb hc hm pos])
  have hhom:
      "collinear (2 * foot b c m - m) (2 * foot c a m - m)
        (2 * foot a b m - m)"
    by (rule collinear_homothety[OF hsim])
  thus ?thesis by (simp add: steiner_reflect_def)
qed

text \<open>The Steiner line passes through the orthocenter.\<close>

theorem steiner_line_through_orthocenter:
  fixes a b c m ctr :: complex and r :: real
  assumes hncol: "\<not> collinear a b c"
    and ha: "oncircle ctr r a" and hb: "oncircle ctr r b"
    and hc: "oncircle ctr r c" and hm: "oncircle ctr r m"
    and pos: "0 < r"
  shows "collinear (orthocenter a b c ctr)
      (steiner_reflect b c m) (steiner_reflect c a m) \<and>
    collinear (orthocenter a b c ctr)
      (steiner_reflect c a m) (steiner_reflect a b m) \<and>
    collinear (orthocenter a b c ctr)
      (steiner_reflect a b m) (steiner_reflect b c m)"
proof -
  have hncol_bca: "\<not> collinear b c a"
    using hncol by (metis collinear_cycle)
  have hncol_cab: "\<not> collinear c a b"
    using hncol by (metis collinear_cycle)
  have hbc_ca:
      "collinear (orthocenter a b c ctr)
        (steiner_reflect b c m) (steiner_reflect c a m)"
    by (rule steiner_orthocenter_collinear[OF hncol ha hb hc hm pos])
  have hca_ab':
      "collinear (orthocenter b c a ctr)
        (steiner_reflect c a m) (steiner_reflect a b m)"
    by (rule steiner_orthocenter_collinear[OF hncol_bca hb hc ha hm pos])
  have hca_ab:
      "collinear (orthocenter a b c ctr)
        (steiner_reflect c a m) (steiner_reflect a b m)"
    using hca_ab'
    by (simp add: orthocenter_def add.commute add.left_commute add.assoc)
  have hab_bc':
      "collinear (orthocenter c a b ctr)
        (steiner_reflect a b m) (steiner_reflect b c m)"
    by (rule steiner_orthocenter_collinear[OF hncol_cab hc ha hb hm pos])
  have hab_bc:
      "collinear (orthocenter a b c ctr)
        (steiner_reflect a b m) (steiner_reflect b c m)"
    using hab_bc'
    by (simp add: orthocenter_def add.commute add.left_commute add.assoc)
  show ?thesis using hbc_ca hca_ab hab_bc by blast
qed

end
