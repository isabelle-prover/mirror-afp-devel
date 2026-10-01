(*  Title:      Miquel.thy
    Author:     Arthur Freitas Ramos, 2026
    Maintainer: Arthur Freitas Ramos

Miquel's Pivot Theorem.

Let ABC be a triangle in the Euclidean plane, and let P, Q, R be points
lying on the side lines BC, CA, AB respectively.  Then the circumcircles of
the three triangles AQR, BRP, CPQ pass through a common point M, the Miquel
point of the configuration.

We work with complex coordinates.  A circle is a set of points at a fixed
positive distance from a centre, and collinearity of three points is
expressed by an affine real parameter.  The core of the proof is the
classical criterion that four (pairwise suitably distinct) complex numbers
lie on a common circle if and only if their cross ratio is real.  From this
criterion Miquel's theorem reduces to an algebraic identity: the product of
the three relevant cross ratios equals a product of three real ratios coming
from the collinearity of P, Q, R on the side lines.

Reference: A. Miquel, "Memoire de Geometrie", Journal de mathematiques pures
et appliquees, 1838.
*)

theory Miquel
  imports "Simson.Simson_Complex_Geometry"
begin
section \<open>Existence of the circumscribed circle\<close>

text \<open>Any three non-collinear points lie on a common circle of positive radius.
  We exhibit the circumcentre in closed form.  Writing \<^term>\<open>u = b - a\<close> and
  \<^term>\<open>v = c - a\<close>, the centre is \<^term>\<open>a + w\<close> with
  \<^term>\<open>w = u * v * cnj (u - v) / D\<close> and \<^term>\<open>D = cnj u * v - u * cnj v\<close>.
  Non-collinearity is exactly \<^term>\<open>D \<noteq> 0\<close>, and a short conjugation
  computation shows the centre is equidistant from the three points.\<close>

lemma circumcircle_exists:
  assumes ncol: "\<not> collinear a b c"
  shows "concyclic3 a b c"
proof -
  define u where "u = b - a"
  define v where "v = c - a"
  define D where "D = cnj u * v - u * cnj v"
  have imz: "Im (cnj u * v) \<noteq> 0" using ncol by (simp add: collinear_iff_cross u_def v_def)
  have Dval: "D = complex_of_real (2 * Im (cnj u * v)) * \<i>"
    unfolding D_def by (metis complex_cnj_cnj complex_cnj_mult complex_diff_cnj)
  define s where "s = Im (cnj u * v)"
  have Dvals: "D = complex_of_real (2 * s) * \<i>" unfolding s_def by (rule Dval)
  have imzs: "s \<noteq> 0" unfolding s_def by (rule imz)
  have Dne: "D \<noteq> 0" using imzs by (simp add: Dvals)
  have cnjD: "cnj D = - D" unfolding D_def
    by (metis complex_cnj_cnj complex_cnj_diff complex_cnj_mult minus_diff_eq)
  define w where "w = u * v * cnj (u - v) / D"
  have cnjw: "cnj w = cnj u * cnj v * (v - u) / D"
  proof -
    have "cnj w = cnj u * cnj v * (u - v) / cnj D"
      unfolding w_def by (simp add: complex_cnj_mult complex_cnj_divide complex_cnj_diff)
    also have "\<dots> = cnj u * cnj v * (u - v) / (- D)" by (simp add: cnjD)
    also have "\<dots> = cnj u * cnj v * (v - u) / D"
    proof -
      have "cnj u * cnj v * (u - v) / (- D) = - (cnj u * cnj v * (u - v) / D)" by simp
      also have "\<dots> = - (cnj u * cnj v * (u - v)) / D" by simp
      also have "\<dots> = cnj u * cnj v * (v - u) / D" by (simp add: right_diff_distrib)
      finally show ?thesis .
    qed
    finally show ?thesis .
  qed
  have wD: "w * D = u * v * cnj (u - v)" unfolding w_def using Dne by simp
  have cnjwD: "cnj w * D = cnj u * cnj v * (v - u)" unfolding cnjw using Dne by simp
  have e1: "w * cnj u + cnj w * u = u * cnj u"
  proof -
    have "(w * cnj u + cnj w * u) * D = (w * D) * cnj u + (cnj w * D) * u"
      by (simp add: algebra_simps)
    also have "\<dots> = u * v * cnj (u - v) * cnj u + cnj u * cnj v * (v - u) * u"
      by (simp add: wD cnjwD)
    also have "\<dots> = u * cnj u * D" unfolding D_def complex_cnj_diff by algebra
    finally have "(w * cnj u + cnj w * u) * D = u * cnj u * D" .
    thus ?thesis using Dne by (metis mult_right_cancel)
  qed
  have e2: "w * cnj v + cnj w * v = v * cnj v"
  proof -
    have "(w * cnj v + cnj w * v) * D = (w * D) * cnj v + (cnj w * D) * v"
      by (simp add: algebra_simps)
    also have "\<dots> = u * v * cnj (u - v) * cnj v + cnj u * cnj v * (v - u) * v"
      by (simp add: wD cnjwD)
    also have "\<dots> = v * cnj v * D" unfolding D_def complex_cnj_diff by algebra
    finally have "(w * cnj v + cnj w * v) * D = v * cnj v * D" .
    thus ?thesis using Dne by (metis mult_right_cancel)
  qed
  have d1: "(u - w) * cnj (u - w) = w * cnj w"
  proof -
    have "(u - w) * cnj (u - w) = (u - w) * (cnj u - cnj w)" by (simp add: complex_cnj_diff)
    also have "\<dots> = u * cnj u - (w * cnj u + cnj w * u) + w * cnj w"
      by (simp add: algebra_simps)
    also have "\<dots> = w * cnj w" using e1 by simp
    finally show ?thesis .
  qed
  have d2: "(v - w) * cnj (v - w) = w * cnj w"
  proof -
    have "(v - w) * cnj (v - w) = (v - w) * (cnj v - cnj w)" by (simp add: complex_cnj_diff)
    also have "\<dots> = v * cnj v - (w * cnj v + cnj w * v) + w * cnj w"
      by (simp add: algebra_simps)
    also have "\<dots> = w * cnj w" using e2 by simp
    finally show ?thesis .
  qed
  have R1: "cmod (u - w) = cmod w"
  proof -
    have "complex_of_real ((cmod (u - w))\<^sup>2) = complex_of_real ((cmod w)\<^sup>2)"
    proof -
      have "complex_of_real ((cmod (u - w))\<^sup>2) = (u - w) * cnj (u - w)"
        by (rule complex_norm_square)
      also have "\<dots> = w * cnj w" by (rule d1)
      also have "\<dots> = complex_of_real ((cmod w)\<^sup>2)" by (rule complex_norm_square[symmetric])
      finally show ?thesis .
    qed
    hence "(cmod (u - w))\<^sup>2 = (cmod w)\<^sup>2" by (metis of_real_eq_iff)
    thus ?thesis by (metis norm_ge_zero power2_eq_imp_eq)
  qed
  have R2: "cmod (v - w) = cmod w"
  proof -
    have "complex_of_real ((cmod (v - w))\<^sup>2) = complex_of_real ((cmod w)\<^sup>2)"
    proof -
      have "complex_of_real ((cmod (v - w))\<^sup>2) = (v - w) * cnj (v - w)"
        by (rule complex_norm_square)
      also have "\<dots> = w * cnj w" by (rule d2)
      also have "\<dots> = complex_of_real ((cmod w)\<^sup>2)" by (rule complex_norm_square[symmetric])
      finally show ?thesis .
    qed
    hence "(cmod (v - w))\<^sup>2 = (cmod w)\<^sup>2" by (metis of_real_eq_iff)
    thus ?thesis by (metis norm_ge_zero power2_eq_imp_eq)
  qed
  have ab: "a \<noteq> b"
  proof
    assume "a = b"
    hence "collinear a b c" by (simp add: collinear_iff_cross)
    with ncol show False by simp
  qed
  have ac: "a \<noteq> c"
  proof
    assume "a = c"
    hence "collinear a b c" by (simp add: collinear_iff_cross)
    with ncol show False by simp
  qed
  have bc: "b \<noteq> c"
  proof
    assume bc': "b = c"
    have "Im (cnj (b - a) * (c - a)) = 0"
      using bc' by (metis complex_In_mult_cnj_zero mult.commute)
    hence "collinear a b c" by (simp add: collinear_iff_cross)
    with ncol show False by simp
  qed
  have u0: "u \<noteq> 0" using ab by (simp add: u_def)
  have v0: "v \<noteq> 0" using ac by (simp add: v_def)
  have uv: "u \<noteq> v" using bc by (simp add: u_def v_def)
  have w0: "w \<noteq> 0"
  proof
    assume "w = 0"
    hence "u * v * cnj (u - v) = 0" using wD by simp
    thus False using u0 v0 uv by (simp add: complex_cnj_zero)
  qed
  have onA: "oncircle (a + w) (cmod w) a" by (simp add: oncircle_def)
  have onB: "oncircle (a + w) (cmod w) b"
  proof -
    have "cmod (b - (a + w)) = cmod (u - w)" by (simp add: u_def algebra_simps)
    also have "\<dots> = cmod w" by (rule R1)
    finally show ?thesis by (simp add: oncircle_def)
  qed
  have onC: "oncircle (a + w) (cmod w) c"
  proof -
    have "cmod (c - (a + w)) = cmod (v - w)" by (simp add: v_def algebra_simps)
    also have "\<dots> = cmod w" by (rule R2)
    finally show ?thesis by (simp add: oncircle_def)
  qed
  have Rpos: "0 < cmod w" using w0 by simp
  show "concyclic3 a b c"
    unfolding concyclic3_def
    using onA onB onC Rpos by blast
qed

text \<open>Antisymmetry of the planar cross product under a change of base point.\<close>

lemma cross_base_change:
  fixes a b c :: complex
  shows "Im (cnj (b - c) * (a - c)) = - Im (cnj (b - a) * (c - a))"
  by (simp add: algebra_simps)

text \<open>If the triangle \<^term>\<open>a\<close>\<^term>\<open>b\<close>\<^term>\<open>c\<close> is nondegenerate and
  \<^term>\<open>p\<close>, \<^term>\<open>q\<close> lie on the side lines \<^term>\<open>b\<close>\<^term>\<open>c\<close> and
  \<^term>\<open>c\<close>\<^term>\<open>a\<close> without coinciding with \<^term>\<open>c\<close>, then \<^term>\<open>c\<close>,
  \<^term>\<open>p\<close>, \<^term>\<open>q\<close> are themselves non-collinear.  Hence their
  circumscribed circle exists.\<close>

lemma cpq_ncol:
  assumes ncol: "\<not> collinear a b c"
    and lp: "on_line b c p"
    and lq: "on_line c a q"
    and pc: "p \<noteq> c"
    and qc: "q \<noteq> c"
  shows "\<not> collinear c p q"
proof -
  from lp obtain t where t: "p = b + of_real t * (c - b)" using on_line_def by auto
  from lq obtain s where s: "q = c + of_real s * (a - c)" using on_line_def by auto
  have pmc: "p - c = of_real (1 - t) * (b - c)"
    by (simp add: t of_real_diff algebra_simps)
  have qmc: "q - c = of_real s * (a - c)"
    by (simp add: s)
  have imkey: "Im (cnj (p - c) * (q - c)) = (1 - t) * s * Im (cnj (b - c) * (a - c))"
    by (simp add: pmc qmc algebra_simps)
  have t1: "1 - t \<noteq> 0"
  proof
    assume "1 - t = 0"
    hence "p - c = 0" by (simp add: pmc)
    thus False using pc by simp
  qed
  have s0: "s \<noteq> 0"
  proof
    assume "s = 0"
    hence "q - c = 0" by (simp add: qmc)
    thus False using qc by simp
  qed
  have imbc: "Im (cnj (b - c) * (a - c)) \<noteq> 0"
  proof -
    have ne: "Im (cnj (b - a) * (c - a)) \<noteq> 0" using ncol by (simp add: collinear_iff_cross)
    have "Im (cnj (b - c) * (a - c)) = - Im (cnj (b - a) * (c - a))" by (rule cross_base_change)
    with ne show ?thesis by simp
  qed
  have prod0: "(1 - t) * s * Im (cnj (b - c) * (a - c)) \<noteq> 0"
    using t1 s0 imbc by simp
  from prod0 imkey have "Im (cnj (p - c) * (q - c)) \<noteq> 0" by simp
  thus "\<not> collinear c p q" by (simp add: collinear_iff_cross)
qed


section \<open>Miquel's pivot theorem\<close>

text \<open>The three cross ratios attached to the Miquel configuration multiply to
  a product of three ratios coming from the side lines.\<close>

lemma miquel_complex_cross_ratio_product:
  assumes dmr: "m \<noteq> r" and daq: "a \<noteq> q" and dmp: "m \<noteq> p"
    and dbr: "b \<noteq> r" and dmq: "m \<noteq> q" and dcp: "c \<noteq> p"
  shows "complex_cross_ratio m a q r * complex_cross_ratio m b r p * complex_cross_ratio m c p q
       = (a - r) * (b - p) * (c - q) / ((a - q) * (b - r) * (c - p))"
proof -
  have n1: "m - r \<noteq> 0" using dmr by simp
  have n3: "m - p \<noteq> 0" using dmp by simp
  have n5: "m - q \<noteq> 0" using dmq by simp
  have "complex_cross_ratio m a q r * complex_cross_ratio m b r p * complex_cross_ratio m c p q
      = (((m-q)*(a-r)) * ((m-r)*(b-p)) * ((m-p)*(c-q)))
        / (((m-r)*(a-q)) * ((m-p)*(b-r)) * ((m-q)*(c-p)))"
    unfolding complex_cross_ratio_def by (simp add: mult.commute mult.left_commute)
  also have "\<dots> = (((m-p)*(m-q)*(m-r)) * ((a-r)*(b-p)*(c-q)))
        / (((m-p)*(m-q)*(m-r)) * ((a-q)*(b-r)*(c-p)))"
    by (simp add: mult.commute mult.left_commute)
  also have "\<dots> = (a - r) * (b - p) * (c - q) / ((a - q) * (b - r) * (c - p))"
    using n1 n3 n5 by simp
  finally show ?thesis .
qed

text \<open>The main theorem.  With the side-line conditions on \<^term>\<open>p\<close>,
  \<^term>\<open>q\<close>, \<^term>\<open>r\<close>, and general-position distinctness, any point
  \<^term>\<open>m\<close> lying on the circumcircles of \<^term>\<open>a\<close>\<^term>\<open>q\<close>\<^term>\<open>r\<close> and
  \<^term>\<open>b\<close>\<^term>\<open>r\<close>\<^term>\<open>p\<close> also lies on the circumcircle of
  \<^term>\<open>c\<close>\<^term>\<open>p\<close>\<^term>\<open>q\<close>.  Thus the three circumcircles are concurrent
  at the Miquel point \<^term>\<open>m\<close>.\<close>

theorem miquel_pivot:
  assumes lr: "on_line a b r" and lp: "on_line b c p" and lq: "on_line c a q"
    and h1: "concyclic a q r m" and h2: "concyclic b r p m"
    and ncol: "\<not> collinear a b c"
    and dmp: "m \<noteq> p" and dmq: "m \<noteq> q" and dmr: "m \<noteq> r"
    and daq: "a \<noteq> q" and dar: "a \<noteq> r" and dbr: "b \<noteq> r" and dbp: "b \<noteq> p"
    and dcp: "c \<noteq> p" and dcq: "c \<noteq> q"
  shows "concyclic c p q m"
proof -
  \<comment> \<open>unpack the three circles\<close>
  from h1 obtain o1 R1 where c1: "0 < R1"
      "oncircle o1 R1 a" "oncircle o1 R1 q" "oncircle o1 R1 r" "oncircle o1 R1 m"
    by (auto simp: concyclic_def)
  from h2 obtain o2 R2 where c2: "0 < R2"
      "oncircle o2 R2 b" "oncircle o2 R2 r" "oncircle o2 R2 p" "oncircle o2 R2 m"
    by (auto simp: concyclic_def)
  \<comment> \<open>the third circle exists because the triangle is nondegenerate\<close>
  have ncolcpq: "\<not> collinear c p q"
    using cpq_ncol[OF ncol lp lq] dcp dcq by auto
  have dpq: "p \<noteq> q"
  proof
    assume "p = q"
    hence "Im (cnj (p - c) * (q - c)) = 0"
      by (metis complex_In_mult_cnj_zero mult.commute)
    hence "collinear c p q" by (simp add: collinear_iff_cross)
    with ncolcpq show False by simp
  qed
  from circumcircle_exists[OF ncolcpq] obtain o3 R3 where c3: "0 < R3"
      "oncircle o3 R3 c" "oncircle o3 R3 p" "oncircle o3 R3 q"
    by (auto simp: concyclic3_def)
  \<comment> \<open>the two known circles make two cross ratios real\<close>
  have cr1: "complex_cross_ratio m a q r \<in> \<real>"
    using concyclic_complex_cross_ratio_real[OF c1(5) c1(2) c1(3) c1(4) c1(1)] dmr daq by simp
  have cr2: "complex_cross_ratio m b r p \<in> \<real>"
    using concyclic_complex_cross_ratio_real[OF c2(5) c2(2) c2(3) c2(4) c2(1)] dmp dbr by simp
  \<comment> \<open>the product of all three cross ratios is a product of real side ratios\<close>
  have side1: "(a - r) / (b - r) \<in> \<real>"
    using on_line_ratio_real[OF lr] dbr by simp
  have side2: "(b - p) / (c - p) \<in> \<real>"
    using on_line_ratio_real[OF lp] dcp by simp
  have side3: "(c - q) / (a - q) \<in> \<real>"
    using on_line_ratio_real[OF lq] daq by simp
  have Phi: "(a - r) * (b - p) * (c - q) / ((a - q) * (b - r) * (c - p)) \<in> \<real>"
  proof -
    have "(a - r) * (b - p) * (c - q) / ((a - q) * (b - r) * (c - p))
        = ((a - r) / (b - r)) * ((b - p) / (c - p)) * ((c - q) / (a - q))"
      using daq dbr dcp by (simp add: field_simps)
    also have "\<dots> \<in> \<real>"
      using side1 side2 side3 by (intro Reals_mult)
    finally show ?thesis .
  qed
  \<comment> \<open>hence the third cross ratio is real\<close>
  have prod: "complex_cross_ratio m a q r * complex_cross_ratio m b r p * complex_cross_ratio m c p q
            = (a - r) * (b - p) * (c - q) / ((a - q) * (b - r) * (c - p))"
    using miquel_complex_cross_ratio_product[OF dmr daq dmp dbr dmq dcp] .
  have cr1ne: "complex_cross_ratio m a q r \<noteq> 0"
    unfolding complex_cross_ratio_def using dmq dar by (simp add: dmr daq)
  have cr2ne: "complex_cross_ratio m b r p \<noteq> 0"
    unfolding complex_cross_ratio_def using dmr dbp by (simp add: dmp dbr)
  have cr3real: "complex_cross_ratio m c p q \<in> \<real>"
  proof -
    have "complex_cross_ratio m c p q
        = ((a - r) * (b - p) * (c - q) / ((a - q) * (b - r) * (c - p)))
          / (complex_cross_ratio m a q r * complex_cross_ratio m b r p)"
    proof -
      have ne: "complex_cross_ratio m a q r * complex_cross_ratio m b r p \<noteq> 0"
        using cr1ne cr2ne by simp
      have "complex_cross_ratio m c p q
          = (complex_cross_ratio m a q r * complex_cross_ratio m b r p * complex_cross_ratio m c p q)
            / (complex_cross_ratio m a q r * complex_cross_ratio m b r p)"
        using ne by simp
      then show ?thesis using prod by simp
    qed
    also have "\<dots> \<in> \<real>"
      using Phi Reals_mult[OF cr1 cr2] by (rule Reals_divide)
    finally show ?thesis .
  qed
  \<comment> \<open>the converse criterion places \<^term>\<open>m\<close> on the third circle\<close>
  have "oncircle o3 R3 m"
    using complex_cross_ratio_real_on_circle[OF c3(2) c3(3) c3(4) c3(1) dcp dcq dpq dmq cr3real] .
  with c3 show ?thesis
    by (auto simp: concyclic_def)
qed


section \<open>Concurrency of the three circumcircles\<close>

text \<open>We now prove Miquel's theorem in its classical concurrency form: for a
  nondegenerate triangle the three circumcircles have a common point.  The
  circumcircles of \<open>a\<close>\<open>q\<close>\<open>r\<close> and \<open>b\<close>\<open>r\<close>\<open>p\<close> both pass through
  \<open>r\<close>.  When they are not tangent there, they meet again in a second point,
  the \<^emph>\<open>Miquel point\<close>, which is the reflection of \<open>r\<close> in the line
  joining the two centres.  Reflection in a line is an isometry fixing every
  point of that line, so this second point automatically lies on both circles;
  the pivot theorem then places it on the third.\<close>

definition reflect_line :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex"
  where "reflect_line o1 o2 z = o1 + (o2 - o1) * cnj (z - o1) / cnj (o2 - o1)"

text \<open>Reflection in the line through \<open>o1\<close> and \<open>o2\<close> preserves the distance
  to \<open>o1\<close>.\<close>

lemma reflect_line_dist1:
  assumes oo: "o1 \<noteq> o2"
  shows "cmod (reflect_line o1 o2 z - o1) = cmod (z - o1)"
proof -
  have "cmod (reflect_line o1 o2 z - o1)
      = cmod ((o2 - o1) * cnj (z - o1) / cnj (o2 - o1))"
    by (simp add: reflect_line_def)
  also have "\<dots> = cmod (o2 - o1) * cmod (z - o1) / cmod (o2 - o1)"
    by (simp add: norm_mult norm_divide complex_mod_cnj del: complex_cnj_diff)
  also have "\<dots> = cmod (z - o1)"
  proof -
    have "cmod (o2 - o1) \<noteq> 0" using oo by (metis norm_eq_zero right_minus_eq)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

text \<open>Reflection in the line through \<open>o1\<close> and \<open>o2\<close> also preserves the
  distance to \<open>o2\<close>.\<close>

lemma reflect_line_dist2:
  assumes oo: "o1 \<noteq> o2"
  shows "cmod (reflect_line o1 o2 z - o2) = cmod (z - o2)"
proof -
  have g0: "cnj (o2 - o1) \<noteq> 0"
    using oo by (metis complex_cnj_zero_iff right_minus_eq)
  have cnjrel: "cnj (z - o1) = cnj (z - o2) + cnj (o2 - o1)"
  proof -
    have "cnj (z - o1) = cnj ((z - o2) + (o2 - o1))" by simp
    also have "\<dots> = cnj (z - o2) + cnj (o2 - o1)" by (simp add: complex_cnj_add)
    finally show ?thesis .
  qed
  have eqform: "reflect_line o1 o2 z - o2 = (o2 - o1) * cnj (z - o2) / cnj (o2 - o1)"
  proof -
    have "(reflect_line o1 o2 z - o2) * cnj (o2 - o1)
        = (o1 - o2) * cnj (o2 - o1) + (o2 - o1) * cnj (z - o1)"
      using g0 by (simp add: reflect_line_def field_simps)
    also have "\<dots> = (o1 - o2) * cnj (o2 - o1)
                    + (o2 - o1) * (cnj (z - o2) + cnj (o2 - o1))"
      by (simp add: cnjrel)
    also have "\<dots> = (o2 - o1) * cnj (z - o2)" by (simp add: algebra_simps)
    finally have "(reflect_line o1 o2 z - o2) * cnj (o2 - o1) = (o2 - o1) * cnj (z - o2)" .
    thus ?thesis using g0 by (simp add: field_simps)
  qed
  have "cmod (reflect_line o1 o2 z - o2)
      = cmod ((o2 - o1) * cnj (z - o2) / cnj (o2 - o1))"
    by (simp add: eqform)
  also have "\<dots> = cmod (o2 - o1) * cmod (z - o2) / cmod (o2 - o1)"
    by (simp add: norm_mult norm_divide complex_mod_cnj del: complex_cnj_diff)
  also have "\<dots> = cmod (z - o2)"
  proof -
    have "cmod (o2 - o1) \<noteq> 0" using oo by (metis norm_eq_zero right_minus_eq)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

text \<open>If \<open>r\<close> does not lie on the line through the two centres, i.e.\ the two
  circles are not tangent at \<open>r\<close>, then the reflected point is genuinely
  distinct from \<open>r\<close>.\<close>

lemma reflect_line_neq:
  assumes ncl: "\<not> collinear o1 o2 r"
  shows "reflect_line o1 o2 r \<noteq> r"
proof
  assume eq: "reflect_line o1 o2 r = r"
  have oo: "o1 \<noteq> o2"
  proof
    assume "o1 = o2"
    hence "collinear o1 o2 r" by (simp add: collinear_iff_cross)
    with ncl show False by simp
  qed
  have g0: "cnj (o2 - o1) \<noteq> 0"
    using oo by (metis complex_cnj_zero_iff right_minus_eq)
  have "(reflect_line o1 o2 r - r) * cnj (o2 - o1)
      = (o2 - o1) * cnj (r - o1) - (r - o1) * cnj (o2 - o1)"
    using g0 by (simp add: reflect_line_def field_simps)
  moreover have "reflect_line o1 o2 r - r = 0" using eq by simp
  ultimately have z0: "(o2 - o1) * cnj (r - o1) - (r - o1) * cnj (o2 - o1) = 0"
    by simp
  from z0 have zeq: "(o2 - o1) * cnj (r - o1) = (r - o1) * cnj (o2 - o1)" by simp
  have "cnj (cnj (o2 - o1) * (r - o1)) = (o2 - o1) * cnj (r - o1)"
    by (simp add: complex_cnj_mult)
  also have "\<dots> = (r - o1) * cnj (o2 - o1)" by (rule zeq)
  also have "\<dots> = cnj (o2 - o1) * (r - o1)" by (simp add: mult.commute)
  finally have "cnj (cnj (o2 - o1) * (r - o1)) = cnj (o2 - o1) * (r - o1)" .
  hence "Im (cnj (o2 - o1) * (r - o1)) = 0" by (metis cnj.sel(2) neg_equal_zero)
  hence "collinear o1 o2 r" by (simp add: collinear_iff_cross)
  with ncl show False by simp
qed

text \<open>The classical Miquel theorem.  Let \<open>a\<close>\<open>b\<close>\<open>c\<close> be a nondegenerate
  triangle with \<open>r\<close>, \<open>p\<close>, \<open>q\<close> on the side lines \<open>a\<close>\<open>b\<close>, \<open>b\<close>\<open>c\<close>,
  \<open>c\<close>\<open>a\<close>.  Given the circumcircles of \<open>a\<close>\<open>q\<close>\<open>r\<close> and \<open>b\<close>\<open>r\<close>\<open>p\<close>,
  not tangent at \<open>r\<close>, their second common point --- the reflection of \<open>r\<close>
  in the centre line --- lies on all three circumcircles, including that of
  \<open>c\<close>\<open>p\<close>\<open>q\<close>.  No common point is assumed: it is constructed.\<close>

theorem miquel_concurrent:
  assumes lr: "on_line a b r" and lp: "on_line b c p" and lq: "on_line c a q"
    and ncol: "\<not> collinear a b c"
    and ca: "oncircle o1 R1 a" and cq: "oncircle o1 R1 q"
    and car: "oncircle o1 R1 r" and R1pos: "0 < R1"
    and cbb: "oncircle o2 R2 b" and cbr: "oncircle o2 R2 r"
    and cpp: "oncircle o2 R2 p" and R2pos: "0 < R2"
    and nonline: "\<not> collinear o1 o2 r"
    and daq: "a \<noteq> q" and dar: "a \<noteq> r" and dbr: "b \<noteq> r" and dbp: "b \<noteq> p"
    and dcp: "c \<noteq> p" and dcq: "c \<noteq> q"
  shows "concyclic a q r (reflect_line o1 o2 r)
       \<and> concyclic b r p (reflect_line o1 o2 r)
       \<and> concyclic c p q (reflect_line o1 o2 r)"
proof -
  define m where "m = reflect_line o1 o2 r"
  have oo: "o1 \<noteq> o2"
  proof
    assume "o1 = o2"
    hence "collinear o1 o2 r" by (simp add: collinear_iff_cross)
    with nonline show False by simp
  qed
  \<comment> \<open>the constructed point lies on the first two circles\<close>
  have m1: "oncircle o1 R1 m"
  proof -
    have "cmod (m - o1) = cmod (r - o1)"
      unfolding m_def by (rule reflect_line_dist1[OF oo])
    also have "\<dots> = R1" using car by (simp add: oncircle_def)
    finally show ?thesis by (simp add: oncircle_def)
  qed
  have m2: "oncircle o2 R2 m"
  proof -
    have "cmod (m - o2) = cmod (r - o2)"
      unfolding m_def by (rule reflect_line_dist2[OF oo])
    also have "\<dots> = R2" using cbr by (simp add: oncircle_def)
    finally show ?thesis by (simp add: oncircle_def)
  qed
  have h1: "concyclic a q r m"
    unfolding concyclic_def using R1pos ca cq car m1 by blast
  have h2: "concyclic b r p m"
    unfolding concyclic_def using R2pos cbb cbr cpp m2 by blast
  have mr: "m \<noteq> r" unfolding m_def by (rule reflect_line_neq[OF nonline])
  \<comment> \<open>the third circle exists because the triangle is nondegenerate\<close>
  have ncolcpq: "\<not> collinear c p q"
    using cpq_ncol[OF ncol lp lq] dcp dcq by auto
  have c3: "concyclic3 c p q" using circumcircle_exists[OF ncolcpq] .
  \<comment> \<open>the constructed point lies on the third circle\<close>
  have h3: "concyclic c p q m"
  proof (cases "m = p")
    case True
    from c3 obtain ctr R where "0 < R"
        "oncircle ctr R c" "oncircle ctr R p" "oncircle ctr R q"
      by (auto simp: concyclic3_def)
    thus ?thesis using True unfolding concyclic_def by blast
  next
    case notp: False
    show ?thesis
    proof (cases "m = q")
      case True
      from c3 obtain ctr R where "0 < R"
          "oncircle ctr R c" "oncircle ctr R p" "oncircle ctr R q"
        by (auto simp: concyclic3_def)
      thus ?thesis using True unfolding concyclic_def by blast
    next
      case notq: False
      show ?thesis
        using miquel_pivot[OF lr lp lq h1 h2 ncol notp notq mr
                              daq dar dbr dbp dcp dcq] .
    qed
  qed
  show ?thesis using h1 h2 h3 by (simp add: m_def)
qed

text \<open>The existence form: the three circumcircles have a common point.\<close>

corollary miquel_point_exists:
  assumes lr: "on_line a b r" and lp: "on_line b c p" and lq: "on_line c a q"
    and ncol: "\<not> collinear a b c"
    and ca: "oncircle o1 R1 a" and cq: "oncircle o1 R1 q"
    and car: "oncircle o1 R1 r" and R1pos: "0 < R1"
    and cbb: "oncircle o2 R2 b" and cbr: "oncircle o2 R2 r"
    and cpp: "oncircle o2 R2 p" and R2pos: "0 < R2"
    and nonline: "\<not> collinear o1 o2 r"
    and daq: "a \<noteq> q" and dar: "a \<noteq> r" and dbr: "b \<noteq> r" and dbp: "b \<noteq> p"
    and dcp: "c \<noteq> p" and dcq: "c \<noteq> q"
  shows "\<exists>m. concyclic a q r m \<and> concyclic b r p m \<and> concyclic c p q m"
  using miquel_concurrent[OF lr lp lq ncol ca cq car R1pos cbb cbr cpp R2pos
      nonline daq dar dbr dbp dcp dcq]
  by blast

end
