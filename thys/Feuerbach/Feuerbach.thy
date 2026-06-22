theory Feuerbach
  imports "HOL-Analysis.Analysis"
begin

section \<open>Algebraic condition for two circles to be tangent to each other\<close>

lemma inner_real2: "(x::real^2) \<bullet> y = x$1 * y$1 + x$2 * y$2"
  by (simp add: inner_vec_def UNIV_2)

lemma norm_real2_sq: "(norm (x::real^2))^2 = (x$1)^2 + (x$2)^2"
  by (simp add: power2_norm_eq_inner inner_real2 power2_eq_square[of "x$1"] power2_eq_square[of "x$2"])

lemma dist_real2_sq: "(dist (a::real^2) b)^2 = (a$1 - b$1)^2 + (a$2 - b$2)^2"
  by (simp add: dist_norm norm_real2_sq)

lemma collinear_3_2d:
  "collinear {(a::real^2), b, c} \<longleftrightarrow>
   (b$1 - a$1) * (c$2 - a$2) = (c$1 - a$1) * (b$2 - a$2)"
proof -
  have "collinear {a, b, c} = (a = b \<or> c = b \<or> (\<exists>k. c - b = k *\<^sub>R (a - b)))"
    by (simp add: collinear_3 collinear_lemma)
  also have "\<dots> = ((b$1 - a$1) * (c$2 - a$2) = (c$1 - a$1) * (b$2 - a$2))"
    (is "?L = ?R")
  proof
    assume ?L
    then consider "a = b" | "c = b" | k where "c - b = k *\<^sub>R (a - b)"
      by auto
    then show ?R
    proof cases
      case (3 k) 
      then have "\<And>i. (c - b)$i = (k *\<^sub>R (a - b))$i" by (simp add: vec_eq_iff)
      from this [of 1] this [of 2]
      show ?thesis
        by (simp add: vec_eq_iff) algebra
    qed auto
  next
    assume ?R
    then have det: "(a$1 - b$1) * (c$2 - b$2) = (c$1 - b$1) * (a$2 - b$2)"
      by (simp add: algebra_simps)
    show ?L
    proof (cases "a = b")
      case True then show ?thesis by simp
    next
      case False
      then obtain i :: 2 where i_ne: "(a - b) $ i \<noteq> 0"
        by (auto simp: vec_eq_iff)
      define k where "k = (c - b) $ i / (a - b) $ i"
      have "c - b = k *\<^sub>R (a - b)"
      proof (rule vec_eq_iff[THEN iffD2], rule allI)
        fix j :: 2
        have "(c$j - b$j) * (a$i - b$i) = (c$i - b$i) * (a$j - b$j)"
          using exhaust_2 [of i] using exhaust_2 [of j] det 
          by (auto simp: algebra_simps)
        then show "(c - b) $ j = (k *\<^sub>R (a - b)) $ j"
          using i_ne by (simp add: eq_divide_imp k_def)
      qed
      then show ?thesis by auto
    qed
  qed
  finally show ?thesis .
qed

section \<open>Geometric invariance lemmas\<close>

lemma collinear_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
  shows "collinear (f ` S) = collinear S"
  by (simp add: assms collinear_aff_dim)

lemma collinear_orthogonal_transformation:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "orthogonal_transformation f"
  shows "collinear {f a, f b, f c} = collinear {a, b, c}"
  using assms collinear_linear_image orthogonal_transformation_inj
    orthogonal_transformation_linear by force

lemma rotation_to_x_axis:
  fixes v :: "real^2"
  assumes "v \<noteq> 0"
  obtains R :: "real^2 \<Rightarrow> real^2" where "orthogonal_transformation R" "(R v)$1 = norm v" "(R v)$2 = 0"
proof -
  define p where "p = v$1"
  define q where "q = v$2"
  define r where "r = norm v"
  have r_pos: "r > 0" using assms by (simp add: r_def)
  have r_ne: "r \<noteq> 0" using r_pos by simp
  have r_sq: "r\<^sup>2 = p\<^sup>2 + q\<^sup>2"
    unfolding r_def p_def q_def by (simp add: norm_real2_sq)
  define R :: "real^2 \<Rightarrow> real^2" where
    "R x = (\<chi> i. if i = 1 then (p * x$1 + q * x$2) / r else (-q * x$1 + p * x$2) / r)" for x
  have R1: "\<And>x. (R x)$1 = (p * x$1 + q * x$2) / r"
    unfolding R_def by simp
  have R2: "\<And>x. (R x)$2 = (-q * x$1 + p * x$2) / r"
    unfolding R_def by simp
  have lin: "linear R"
  proof (rule linearI)
    fix x y :: "real^2"
    show "R (x + y) = R x + R y"
      by (simp add: vec_eq_iff R1 R2 forall_2 add_divide_distrib diff_divide_distrib algebra_simps)
  next
    fix c :: real and x :: "real^2"
    show "R (c *\<^sub>R x) = c *\<^sub>R R x"
      by (simp add: vec_eq_iff R1 R2 forall_2 algebra_simps)
  qed
  have inner_pres: "R x \<bullet> R y = x \<bullet> y" for x y :: "real^2"
    using r_sq r_ne by (simp add: inner_real2 R1 R2 field_simps) algebra
  have orth: "orthogonal_transformation R"
    unfolding orthogonal_transformation_def using lin inner_pres by auto
  have rv1: "(R v)$1 = norm v"
    by (metis R1 nonzero_mult_div_cancel_left p_def power2_eq_square q_def r_def r_ne r_sq)
  have rv2: "(R v)$2 = 0"
    by (simp add: R2 p_def q_def)
  from orth rv1 rv2 show ?thesis by (rule that[where R=R])
qed

lemma collinear_translate:
  fixes x :: "'a::euclidean_space"
  shows "collinear {x, y, z} = collinear {x - a, y - a, z - a}"
  by (simp add: between_norm collinear_between_cases)

lemma int_case_lemma:
  fixes c1 c2 :: "(real,2) vec"
  assumes "0 \<le> r1" "r1 < r2" and d: "dist c1 c2 = \<bar>r1 - r2\<bar>" and int: "dist c1 c2 = \<bar>r1 - r2\<bar>"
  shows "c1 = c2 \<and> r1 = r2 \<or> (\<exists>!x. dist c1 x = r1 \<and> dist c2 x = r2)"
proof -
  have r_diff: "r2 - r1 > 0" using assms by linarith
  have abs_eq: "dist c1 c2 = r2 - r1"
    using int assms by simp
  define x where "x = c1 + (r1 / (r2 - r1)) *\<^sub>R (c1 - c2)"
  have dist_c1c2: "norm (c1 - c2) = r2 - r1"
    using abs_eq by (simp add: dist_norm)
  have dist1: "dist c1 x = r1"
    using assms r_diff
    by (simp add: dist_norm x_def divide_simps norm_minus_commute)
  have dist2: "dist c2 x = r2"
  proof -
    have "c2 - x = (1 + r1 / (r2 - r1)) *\<^sub>R (c2 - c1)"
      by (simp add: x_def scaleR_add_left scaleR_diff_right)
    also have "1 + r1 / (r2 - r1) = r2 / (r2 - r1)"
      using r_diff by (simp add: field_simps)
    finally show ?thesis
      using assms r_diff
      by (simp add: dist_norm divide_simps norm_minus_commute)
  qed
  have unique: "y = x" if "dist c1 y = r1" "dist c2 y = r2" for y
  proof -
    have nor: "norm (c1 - y) = r1" "norm (c2 - y) = r2" 
      using that by (auto simp add: dist_norm)
    have "dist c2 y = dist c2 c1 + dist c1 y"
      using that abs_eq by (simp add: dist_commute)
    then have "norm (c2 - c1) *\<^sub>R (c1 - y) = norm (c1 - y) *\<^sub>R (c2 - c1)"
      by (simp add: dist_triangle_eq)
    then have eq_y: "(r2 - r1) *\<^sub>R y = r2 *\<^sub>R c1 - r1 *\<^sub>R c2"
      using dist_c1c2 nor by (simp add: norm_minus_commute algebra_simps)
    have eq_x: "(r2 - r1) *\<^sub>R x = r2 *\<^sub>R c1 - r1 *\<^sub>R c2"
      using r_diff
      by (simp add: x_def scaleR_add_right scaleR_diff_left scaleR_diff_right)
    show "y = x" using eq_y eq_x r_diff
      by (metis scaleR_cancel_left less_irrefl)
  qed
  show ?thesis
    using dist1 dist2 unique by blast
qed

theorem circles_tangent:
  fixes r1 r2 :: real and c1 c2 :: "real^2"
  assumes "0 \<le> r1" "0 \<le> r2"
    and "dist c1 c2 = r1 + r2 \<or> dist c1 c2 = \<bar>r1 - r2\<bar>"
  shows "c1 = c2 \<and> r1 = r2 \<or> (\<exists>!x::real^2. dist c1 x = r1 \<and> dist c2 x = r2)"
  using assms
proof -
  consider (ext) "dist c1 c2 = r1 + r2" | (int) "dist c1 c2 = \<bar>r1 - r2\<bar>"
    using assms(3) by blast
  then show ?thesis
  proof cases
    case ext
    show ?thesis
    proof (cases "r1 + r2 = 0")
      case True then show ?thesis
        using assms(1,2) local.ext by auto
    next
      case False
      then have r_pos: "r1 + r2 > 0" using assms(1,2) by linarith
      define x where "x = c1 + (r1 / (r1 + r2)) *\<^sub>R (c2 - c1)"
      have x_sub_c1: "x - c1 = (r1 / (r1 + r2)) *\<^sub>R (c2 - c1)"
        by (simp add: x_def)
      have x_sub_c2: "x - c2 = - (r2 / (r1 + r2)) *\<^sub>R (c2 - c1)"
      proof -
        have "x - c2 = (r1 / (r1 + r2) - 1) *\<^sub>R (c2 - c1)"
          by (simp add: x_def scaleR_diff_left)
        also have "r1 / (r1 + r2) - 1 = - (r2 / (r1 + r2))"
          using r_pos by (simp add: field_simps)
        finally show ?thesis by simp
      qed
      have dist_c1c2: "norm (c2 - c1) = r1 + r2"
        using ext by (simp add: dist_norm norm_minus_commute)
      have dist1: "dist c1 x = r1"
        using dist_c1c2 assms(1) r_pos
        by (simp add: dist_norm x_def divide_simps)
      have dist2: "dist c2 x = r2"
      proof -
        have "c2 - x = (r2 / (r1 + r2)) *\<^sub>R (c2 - c1)"
          using x_sub_c2 by (metis minus_diff_eq neg_equal_iff_equal scaleR_minus_left)
        then have "norm (c2 - x) = r2 / (r1 + r2) * norm (c2 - c1)"
          using assms(2) r_pos by (simp add: divide_simps)
        then show ?thesis
          using dist_c1c2 r_pos by (simp add: dist_norm)
      qed
      have unique: "y = x" if "dist c1 y = r1" "dist c2 y = r2" for y
      proof -
        have norm_c1y: "norm (c1 - y) = r1" using that(1) by (simp add: dist_norm)
        have norm_yc2: "norm (y - c2) = r2"
          using that(2) by (simp add: dist_norm norm_minus_commute)
        have "dist c1 c2 = dist c1 y + dist y c2"
          using that ext by (simp add: dist_commute)
        then have "norm (c1 - y) *\<^sub>R (y - c2) = norm (y - c2) *\<^sub>R (c1 - y)"
          by (simp add: dist_triangle_eq)
        then have "(r1 + r2) *\<^sub>R y = r2 *\<^sub>R c1 + r1 *\<^sub>R c2"
          using norm_c1y norm_yc2 by (simp add: algebra_simps)
        moreover have "(r1 + r2) *\<^sub>R x = r2 *\<^sub>R c1 + r1 *\<^sub>R c2"
          using r_pos
          by (simp add: x_def scaleR_add_left scaleR_add_right scaleR_diff_right)
        ultimately show "y = x"
          using r_pos by (metis scaleR_cancel_left less_irrefl)
      qed
      show ?thesis
        using dist1 dist2 unique by blast
    qed
  next
    case int
    show ?thesis
    proof (cases "r1 = r2")
      case True
      with int show ?thesis by auto
    next
      case False
      show ?thesis
      proof (cases "r1 \<le> r2")
        case True
        then show ?thesis
          using int_case_lemma False \<open>0 \<le> r1\<close> int less_eq_real_def by blast
      next
        case False
        then have "c1 = c2 \<and> r2 = r1 \<or> (\<exists>!x. dist c2 x = r2 \<and> dist c1 x = r1)"
          using int_case_lemma[of r2 r1 c2 c1] \<open>0 \<le> r2\<close> int by (simp add: dist_commute)
        then show ?thesis
          by blast
      qed
    qed
  qed
qed

section \<open>Feuerbach's theorem\<close>

text \<open>
  Given a non-degenerate triangle $abc$, let the circle passing through
  the midpoints of its sides (the ``9 point circle'') have center @{term ncenter}
  and radius @{term nradius}. Now suppose the circle with center @{term icenter} and
  radius @{term iradius} is tangent to three sides (either internally or
  externally to one side and two produced sides), meaning that it's either
  the inscribed circle or one of the three escribed circles. Then the two
  circles are tangent to each other, i.e.\ either they are identical or they
  touch at exactly one point.
\<close>

locale Feuerbach =
  fixes a b c :: "real^2"
    and mbc mac mab :: "real^2"
    and pbc pac pab :: "real^2"
    and ncenter icenter :: "real^2"
    and nradius iradius :: real
  assumes mab_def: "mab = midpoint a b" 
      and mbc_def: "mbc = midpoint b c" 
      and mac_def: "mac = midpoint c a"
  assumes nr1: "dist ncenter mbc = nradius"
      and nr2: "dist ncenter mac = nradius"
      and nr3: "dist ncenter mab = nradius"
      and ir1: "dist icenter pbc = iradius"
      and ir2: "dist icenter pac = iradius"
      and ir3: "dist icenter pab = iradius"
      and col_ab: "collinear {a, b, pab}" and orth_ab: "orthogonal (a - b) (icenter - pab)"
      and col_bc: "collinear {b, c, pbc}" and orth_bc: "orthogonal (b - c) (icenter - pbc)"
      and col_ac: "collinear {a, c, pac}" and orth_ac: "orthogonal (a - c) (icenter - pac)"

begin

lemma special:
  assumes bx: "b$2 = 0" and bne: "b$1 \<noteq> 0" and cne: "c$2 \<noteq> 0" and [simp]: "a=0"
  shows "ncenter = icenter \<and> nradius = iradius \<or>
         (\<exists>!x::real^2. dist ncenter x = nradius \<and> dist icenter x = iradius)"
proof -
  \<comment> \<open>First establish non-negativity of radii\<close>
  obtain "0 \<le> nradius" "0 \<le> iradius" using nr1 ir1 zero_le_dist by metis
      \<comment> \<open>Non-collinearity: since a=0, b on x-axis (@{term \<open>b$2=0\<close>}, @{term \<open>b$1\<noteq>0\<close>}), and @{term \<open>c$2\<noteq>0\<close>}\<close>
  have ncol: "\<not> collinear {0, b, c}"
    by (simp add: assms collinear_3_2d)
      \<comment> \<open>Introduce coordinate names\<close>
  define bx where "bx = b$1"
  define cx where "cx = c$1"
  define cy where "cy = c$2"
    \<comment> \<open>Expand midpoint coordinates\<close>
  have mab_eq: "mab = (1/2) *\<^sub>R b" and mbc_eq: "mbc = (1/2) *\<^sub>R (b + c)" and mac_eq: "mac = (1/2) *\<^sub>R c"
    by (auto simp add: midpoint_def mab_def mbc_def mac_def)
  have mab1: "mab$1 = bx / 2" and mab2: "mab$2 = 0"
    using mab_eq bx by (simp_all add: bx_def)
  have mbc1: "mbc$1 = (bx + cx) / 2" and mbc2: "mbc$2 = cy / 2"
    using mbc_eq bx by (simp_all add: bx_def cx_def cy_def add_divide_distrib)
  have mac1: "mac$1 = cx / 2" and mac2: "mac$2 = cy / 2"
    using mac_eq by (simp_all add: cx_def cy_def)
      \<comment> \<open>Extract collinearity conditions\<close>
  have pab2: "pab$2 = 0"
    using bne bx col_ab collinear_3_2d by force
  have col_bc_eq: "(c$1 - b$1) * (pbc$2 - b$2) = (pbc$1 - b$1) * (c$2 - b$2)"
    using col_bc collinear_3_2d[of b c pbc] by simp
  have pbc_col: "(cx - bx) * pbc$2 = (pbc$1 - bx) * cy"
    using col_bc_eq bx by (simp add: bx_def cx_def cy_def)
  have col_ac_eq: "c$1 * pac$2 = pac$1 * c$2"
    using col_ac collinear_3_2d[of 0 c pac] by simp
  have pac_col: "cx * pac$2 = pac$1 * cy"
    using col_ac_eq by (simp add: cx_def cy_def)
      \<comment> \<open>Extract orthogonality conditions\<close>
  have orth_ab_eq: "icenter$1 = pab$1"
    using orth_ab by (simp add: orthogonal_def inner_real2 bx bne)
  have orth_bc_eq: "(bx - cx) * (icenter$1 - pbc$1) - cy * (icenter$2 - pbc$2) = 0"
    using orth_bc by (simp add: orthogonal_def inner_real2 cx_def cy_def bx bx_def)
  have orth_ac_eq: "cx * (icenter$1 - pac$1) + cy * (icenter$2 - pac$2) = 0"
    using orth_ac by (simp add: orthogonal_def inner_real2 cx_def cy_def)
      \<comment> \<open>Approach: use theorem @{text circles_tangent}. We need to show the distance condition.\<close>
      \<comment> \<open>We work entirely in coordinates with $a=0$, $b=(bx,0)$, $c=(cx,cy)$.\<close>
      \<comment> \<open>All geometric conditions become polynomial equations.\<close>
      \<comment> \<open>Strategy: solve for ncenter, nradius, icenter, iradius from constraints,\<close>
      \<comment> \<open>then verify the tangency condition.\<close>

  \<comment> \<open>Solve for ncenter from equidistance to midpoints\<close>
  \<comment> \<open>n1 = @{term \<open>ncenter$1\<close>}, n2 = @{term \<open>ncenter$2\<close>}\<close>
  have n1_val: "ncenter$1 = (bx + 2*cx) / 4"
    using dist_real2_sq[of ncenter mbc] mbc1 mbc2 
    using dist_real2_sq[of ncenter mac] mac1 mac2 bne
    unfolding nr1 nr2 bx_def by algebra

  have n2_val: "ncenter$2 * cy = (cy^2 + bx*cx - cx^2) / 4"
    using dist_real2_sq[of ncenter mbc] mbc1 mbc2
    using dist_real2_sq[of ncenter mab] mab1 mab2
    by (simp add: nr1 nr3 n1_val power2_eq_square field_simps)

  have nradius_sq: "nradius^2 = (ncenter$1 - bx/2)^2 + ncenter$2^2"
    using dist_real2_sq mab1 mab2 nr3 by force

  \<comment> \<open>Extract incircle foot point and center coordinates\<close>
  \<comment> \<open>From @{term \<open>pab$2 = 0\<close>} and @{term \<open>icenter$1 = pab$1\<close>}, we get @{term \<open>iradius = \<bar>icenter$2\<bar>\<close>}\<close>
  have irad_sq: "iradius^2 = (icenter$2)^2"
    using dist_real2_sq ir3 orth_ab_eq pab2 by fastforce

  \<comment> \<open>Derive incircle squared-distance to each side\<close>
  \<comment> \<open>Key idea: pbc is foot of perpendicular from icenter to line bc.\<close>
  \<comment> \<open>From orthogonality (bx-cx)*u = cy*v where u=@{term \<open>icenter$1\<close>}-@{term \<open>pbc$1\<close>}, v=@{term \<open>icenter$2\<close>}-@{term \<open>pbc$2\<close>}.\<close>
  \<comment> \<open>From collinearity, cy*(@{term \<open>icenter$1\<close>}-bx) - (cx-bx)*@{term \<open>icenter$2\<close>} = cy*u - (cx-bx)*v.\<close>
  \<comment> \<open>Then (u²+v²)*D = (cy*u-(cx-bx)*v)² because (cx-bx)*u+cy*v=0 (Lagrange identity).\<close>

  have irad_sq_bc: "iradius^2 * ((cx-bx)^2 + cy^2) = (cy*(icenter$1-bx) - (cx-bx)*icenter$2)^2"
  proof -
    define u where "u = icenter$1 - pbc$1"
    define v where "v = icenter$2 - pbc$2"
    have uv_orth: "(cx - bx) * u + cy * v = 0"
      using orth_bc_eq by (simp add: u_def v_def algebra_simps)
    have irad_uv: "iradius^2 = u^2 + v^2"
      using dist_real2_sq ir1 u_def v_def by blast
    have "cy * (icenter$1 - bx) - (cx - bx) * icenter$2 = cy * u - (cx - bx) * v"
      by (simp add: mult.commute pbc_col right_diff_distrib' u_def v_def)
    then show ?thesis using irad_uv uv_orth by algebra
  qed

  have irad_sq_ac: "iradius^2 * (cx^2 + cy^2) = (cy*icenter$1 - cx*icenter$2)^2"
  proof -
    define u where "u = icenter$1 - pac$1"
    define v where "v = icenter$2 - pac$2"
    have uv_orth: "cx * u + cy * v = 0"
      using orth_ac_eq by (simp add: u_def v_def)
    have irad_uv: "iradius^2 = u^2 + v^2"
      using dist_real2_sq ir2 u_def v_def by blast
    have "cy * icenter$1 - cx * icenter$2 = cy * u - cx * v"
      by (simp add: pac_col right_diff_distrib' u_def v_def)
    then show ?thesis using irad_uv uv_orth by algebra
  qed

  have tangent_cond: "dist ncenter icenter = nradius + iradius \<or> dist ncenter icenter = \<bar>nradius - iradius\<bar>"
  proof -
    \<comment> \<open>Introduce short names for coordinates\<close>
    define i1 where "i1 = icenter$1"
    define i2 where "i2 = icenter$2"
    define n1 where "n1 = ncenter$1"
    define n2 where "n2 = ncenter$2"
    \<comment> \<open>Restate all equations in terms of i1, i2, n1, n2, bx, cx, cy\<close>
    from n1_val have n1_eq: "n1 = (bx + 2*cx) / 4" by (simp add: n1_def)
    from n2_val have n2_eq: "n2 * cy = (cy^2 + bx*cx - cx^2) / 4" by (simp add: n2_def)
    from nradius_sq have nr_sq: "nradius^2 = (n1 - bx/2)^2 + n2^2" by (simp add: n1_def n2_def)
    from irad_sq have ir_sq: "iradius^2 = i2^2" by (simp add: i2_def)
    from irad_sq_bc irad_sq have ir_bc: "i2^2 * ((cx-bx)^2 + cy^2) = (cy*(i1-bx) - (cx-bx)*i2)^2"
      by (simp add: i1_def i2_def)
    from irad_sq_ac irad_sq have ir_ac: "i2^2 * (cx^2 + cy^2) = (cy*i1 - cx*i2)^2"
      by (simp add: i1_def i2_def)
    have key_linear: "cy * (2*i1 - bx) = 2 * (i1 + cx - bx) * i2"
      using ir_ac ir_bc bne cne
      by (simp add: bx_def cy_def field_simps) algebra
    have dist_sq: "(dist ncenter icenter)^2 = (n1 - i1)^2 + (n2 - i2)^2"
      using dist_real2_sq[of ncenter icenter] by (simp add: n1_def n2_def i1_def i2_def)
    have cy_ne: "cy \<noteq> 0" using cne by (simp add: cy_def)
    have bx_ne: "bx \<noteq> 0" using bne by (simp add: bx_def)
    have nrad_nn: "0 \<le> nradius" using nr1 zero_le_dist by metis
    have irad_nn: "0 \<le> iradius" using ir1 zero_le_dist by metis
    have dist_nn: "0 \<le> dist ncenter icenter" by simp
    have key_sq: "((dist ncenter icenter)\<^sup>2 - nradius\<^sup>2 - iradius\<^sup>2)\<^sup>2 = 4 * nradius\<^sup>2 * iradius\<^sup>2"
    proof -
      \<comment> \<open>Substitute all definitions to get a purely algebraic statement\<close>
      have lhs: "(dist ncenter icenter)\<^sup>2 - nradius\<^sup>2 - iradius\<^sup>2 = 
                  i1\<^sup>2 - (bx+2*cx)*i1/2 - 2*n2*i2 + bx*cx/2"
        using dist_sq nr_sq ir_sq by (simp add: n1_eq field_simps power2_eq_square)
      have rhs_eq: "4 * nradius\<^sup>2 * iradius\<^sup>2 = ((2*cx-bx)\<^sup>2/4 + 4*n2\<^sup>2)*i2\<^sup>2"
          using nr_sq ir_sq key_linear by (simp add: n1_eq field_simps) algebra
      have "4 * cy\<^sup>2 * (i1\<^sup>2 - (bx+2*cx)*i1/2 - 2*n2*i2 + bx*cx/2)\<^sup>2 = 
            4 * cy\<^sup>2 * ((2*cx-bx)\<^sup>2/4 + 4*n2\<^sup>2)*i2\<^sup>2"
          using ir_ac n2_eq key_linear by (simp add: field_simps) algebra
      then show ?thesis using lhs rhs_eq cy_ne by simp
    qed
    then have prod_zero: "((dist ncenter icenter)\<^sup>2 - (nradius + iradius)\<^sup>2) * ((dist ncenter icenter)\<^sup>2 - (nradius - iradius)\<^sup>2) = 0"
      by (simp add: power2_eq_square algebra_simps)
    then show ?thesis
      by (smt (verit) irad_nn mult_eq_0_iff nrad_nn real_abs_dist real_sqrt_abs)
  qed
  show ?thesis 
    using circles_tangent[OF \<open>0 \<le> nradius\<close> \<open>0 \<le> iradius\<close>] tangent_cond by blast
qed

theorem main:
  assumes "\<not> collinear {a, b, c}"
  shows "ncenter = icenter \<and> nradius = iradius \<or>
         (\<exists>!x::real^2. dist ncenter x = nradius \<and> dist icenter x = iradius)"
proof -
  \<comment> \<open>Step 1: Translate so that a becomes the origin\<close>
  define a' where "a' = (0::real^2)"
  define b' where "b' = b - a"
  define c' where "c' = c - a"
  define mab' where "mab' = mab - a"
  define mbc' where "mbc' = mbc - a"
  define mac' where "mac' = mac - a"
  define pab' where "pab' = pab - a"
  define pbc' where "pbc' = pbc - a"
  define pac' where "pac' = pac - a"
  define ncenter' where "ncenter' = ncenter - a"
  define icenter' where "icenter' = icenter - a"
  \<comment> \<open>Translation preserves all geometric properties\<close>
  have ncol': "\<not> collinear {a', b', c'}"
    using assms(1) collinear_translate[of a b c a] by (simp add: a'_def b'_def c'_def)
  have mid_ab': "midpoint a' b' = mab'"
    by (simp add: a'_def add_diff_eq b'_def diff_add_eq mab'_def mab_def midpoint_eq_iff)
  have mid_bc': "midpoint b' c' = mbc'"
    by (simp add: add_diff_eq b'_def c'_def diff_add_eq mbc'_def mbc_def midpoint_eq_iff)
  have mid_ca': "midpoint c' a' = mac'"
    by (simp add: add_diff_eq a'_def c'_def diff_add_eq mac'_def mac_def midpoint_eq_iff)
  \<comment> \<open>Now a' = 0, so we have the origin case\<close>
  \<comment> \<open>Step 2: Rotate so that b' lands on the x-axis\<close>
  have b'_ne: "b' \<noteq> 0"
    using a'_def ncol' by force
  obtain R :: "real^2 \<Rightarrow> real^2" where
    R_orth: "orthogonal_transformation R" and R_b1: "R b' $1 = norm b'" and R_b2: "R b' $2 = 0"
    using rotation_to_x_axis[OF b'_ne] by blast
  have R_lin: "linear R" 
    using R_orth orthogonal_transformation_linear by blast
  have R_inner: "\<And>v w. R v \<bullet> R w = v \<bullet> w"
    using R_orth by (simp add: orthogonal_transformation_def)
  have R_norm: "\<And>v. norm (R v) = norm v"
    using R_orth orthogonal_transformation by blast
  have R_dist: "\<And>x y. dist (R x) (R y) = dist x y"
    by (meson R_orth orthogonal_transformation_isometry)
  have R_0: "R 0 = 0" using R_lin by (simp add: linear_0)
  have R_midpoint: "\<And>x y. R (midpoint x y) = midpoint (R x) (R y)"
    using R_lin by (simp add: midpoint_def linear_add linear_cmul)
  have R_orth_pres: "\<And>u v. orthogonal (R u) (R v) = orthogonal u v"
    by (simp add: orthogonal_def R_inner)
  \<comment> \<open>Rotated (R b') is on the x-axis with positive first component\<close>
  have b''_x: "R b' $ 2 = 0" using R_b2 by simp
  have b''_ne: "R b' $ 1 \<noteq> 0"
    by (simp add: R_b1 b'_ne)
  \<comment> \<open>(R c') has nonzero y-component (from non-collinearity)\<close>
  have c''_y: "R c' $ 2 \<noteq> 0"
  proof
    assume c2_0: "R c' $ 2 = 0"
    \<comment> \<open>If @{term \<open>R c' $ 2 = 0\<close>} then 0, (R b'), (R c') are all on x-axis, hence collinear\<close>
    have "collinear {(0::real^2), (R b'), (R c')}"
      by (simp add: R_b2 c2_0 collinear_3_2d)
    \<comment> \<open>But collinear is preserved under orthogonal transformation\<close>
    then have "collinear {R 0, R b', R c'}"
      by (simp add: R_0)
    then have "collinear {0, b', c'}"
      using collinear_orthogonal_transformation[OF R_orth, of 0 b' c'] by (simp add: R_0)
    then have "collinear {a', b', c'}" by (simp add: a'_def)
    then show False using ncol' by contradiction
  qed
  \<comment> \<open>Transfer all properties to rotated coordinates and apply the special case theorem\<close>
  interpret F0: Feuerbach 0 "R b'" "R c'" "R mbc'" "R mac'" "R mab'" "R pbc'" "R pac'" "R pab'" "R ncenter'" "R icenter'"
  proof
    show "R mab' = midpoint 0 (R b')"
      using R_0 R_midpoint a'_def mid_ab' by force
    show "R mbc' = midpoint (R b') (R c')"
      using R_midpoint mid_bc' by force
    show "R mac' = midpoint (R c') 0"
      using R_0 R_midpoint a'_def mid_ca' by force
    obtain "dist ncenter' mbc' = nradius" "dist ncenter' mac' = nradius" "dist ncenter' mab' = nradius"
      by (metis diff_add_cancel dist_add_cancel2 mab'_def mac'_def mbc'_def ncenter'_def nr1 nr2 nr3)
    then show "dist (R ncenter') (R mbc') = nradius" "dist (R ncenter') (R mac') = nradius" "dist (R ncenter') (R mab') = nradius"
      using R_dist by auto
    obtain "dist icenter' pbc' = iradius" "dist icenter' pac' = iradius" "dist icenter' pab' = iradius"
      by (metis (no_types, opaque_lifting) add.commute diff_add_cancel dist_add_cancel icenter'_def ir1
          ir2 ir3 pab'_def pac'_def pbc'_def)
    then show "dist (R icenter') (R pbc') = iradius" "dist (R icenter') (R pac') = iradius" "dist (R icenter') (R pab') = iradius"
      using R_dist by auto
    have "collinear {a', b', pab'}"
      by (metis a'_def b'_def col_ab collinear_translate diff_self pab'_def)
    then show "collinear {0, (R b'), R pab'}"
      using collinear_orthogonal_transformation[OF R_orth, of 0 b' pab']
      by (simp add: a'_def R_0)
    have "orthogonal (a' - b') (icenter' - pab')"
      by (simp add: a'_def b'_def icenter'_def orth_ab pab'_def)
    then show "orthogonal (0 - (R b')) ((R icenter') - R pab')"
      by (simp add: a'_def R_inner inner_diff_right orthogonal_def)
    have "collinear {b', c', pbc'}"
      using b'_def c'_def col_bc collinear_translate pbc'_def by blast
    then show "collinear {(R b'), (R c'), R pbc'}"
      using collinear_orthogonal_transformation[OF R_orth, of b' c' pbc'] by simp
    have "orthogonal (b' - c') (icenter' - pbc')"
      by (simp add: b'_def c'_def icenter'_def orth_bc pbc'_def)
    then show "orthogonal ((R b') - (R c')) ((R icenter') - R pbc')"
      by (simp add: R_inner inner_diff_left inner_diff_right orthogonal_def)
    have "collinear {a', c', pac'}"
      by (metis a'_def c'_def col_ac collinear_translate diff_self pac'_def)
    then show "collinear {0, (R c'), R pac'}"
      using collinear_orthogonal_transformation[OF R_orth, of 0 c' pac']
      by (simp add: a'_def R_0)
    have "orthogonal (a' - c') (icenter' - pac')"
      by (simp add: a'_def c'_def icenter'_def orth_ac pac'_def)
    then show "orthogonal (0 - (R c')) ((R icenter') - R pac')"
      by (simp add: a'_def R_inner inner_diff_right orthogonal_def)
  qed
  have special: "(R ncenter') = (R icenter') \<and> nradius = iradius \<or>
    (\<exists>!x. dist (R ncenter') x = nradius \<and> dist (R icenter') x = iradius)"
    using F0.special by (simp add: b''_ne b''_x c''_y)
  \<comment> \<open>Step 4: Transfer conclusion back to original coordinates\<close>
  show ?thesis
  proof (cases "R ncenter' = R icenter' \<and> nradius = iradius")
    case True
    then show ?thesis
      by (metis R_dist diff_add_cancel dist_eq_0_iff icenter'_def ncenter'_def) 
  next
    case False
    with special obtain x where
      x_uniq: "dist (R ncenter') x = nradius \<and> dist (R icenter') x = iradius"
      "\<And>y. dist (R ncenter') y = nradius \<and> dist (R icenter') y = iradius \<Longrightarrow> y = x"
      by blast
    \<comment> \<open>Map x back through inverse transformations\<close>
    have inj_R: "inj R" 
      using R_orth orthogonal_transformation_inj by blast
    then obtain Rinv where Rinv_lr: "\<And>v. Rinv (R v) = v" and Rinv_rl: "\<And>v. R (Rinv v) = v"
      by (metis linear_injective_imp_surjective surjE injD R_lin)
    define x' where "x' = Rinv x + a"
    have Rx': "R (x' - a) = x" by (simp add: x'_def Rinv_lr Rinv_rl)
    obtain "dist ncenter x' = nradius" "dist icenter x' = iradius"
      using x_uniq unfolding icenter'_def ncenter'_def
      by (metis R_dist Rinv_rl diff_add_cancel dist_add_cancel2 x'_def)
    moreover have "y = x'" if "dist ncenter y = nradius" "dist icenter y = iradius" for y
    proof -
      have "dist (R ncenter') (R (y - a)) = nradius" "dist (R icenter') (R (y - a)) = iradius"
        using that R_dist by (auto simp add: ncenter'_def icenter'_def dist_norm)
      then show "y = x'"
        using Rinv_lr x'_def x_uniq(2) by force
    qed
    ultimately show ?thesis by blast
  qed
qed

end


section \<open>Nine-point circle\<close>

text \<open>
  As a little bonus, verify that the circle passing through the
  midpoints of the sides is indeed a 9-point circle, i.e.\ it passes
  through the feet of the altitudes and the midpoints of the lines joining
  the vertices to the orthocenter (where the altitudes intersect).
\<close>

\<comment> \<open>Pure scalar version: all vector operations expanded to components\<close>
lemma nine_point_circle_1_scalar:
  fixes bv cx cy n1 n2 f1 f2 g1 g2 h1 h2 nr :: real
  assumes cy_ne: "cy \<noteq> 0" and bv_ne: "bv \<noteq> 0"
    \<comment> \<open>Nine-point center equidistant to midpoints of sides\<close>
    \<comment> \<open>midpoint(0,b) = (bv/2, 0), midpoint(b,c) = ((bv+cx)/2, cy/2), midpoint(c,0) = (cx/2, cy/2)\<close>
    and nr1: "(n1 - (bv+cx)/2)^2 + (n2 - cy/2)^2 = nr^2"
    and nr2: "(n1 - cx/2)^2 + (n2 - cy/2)^2 = nr^2"
    and nr3: "(n1 - bv/2)^2 + n2^2 = nr^2"
    \<comment> \<open>fab = (f1, f2): foot of altitude from c to ab (the x-axis)\<close>
    \<comment> \<open>collinear {0, (bv,0), (f1,f2)}: bv * f2 = f1 * 0, so f2 = 0\<close>
    and fab_col: "bv * f2 = 0"
    \<comment> \<open>orthogonal (0-(bv,0)) ((cx,cy)-(f1,f2)): -bv*(cx-f1) + 0*(cy-f2) = 0\<close>
    and fab_orth: "bv * (cx - f1) = 0"
    \<comment> \<open>fbc = (g1, g2): foot of altitude from 0 to bc\<close>
    \<comment> \<open>collinear {(bv,0), (cx,cy), (g1,g2)}: (cx-bv)*(g2-0) = (g1-bv)*(cy-0)\<close>
    and fbc_col: "(cx - bv) * g2 = (g1 - bv) * cy"
    \<comment> \<open>orthogonal ((bv,0)-(cx,cy)) ((0,0)-(g1,g2)): (bv-cx)*(-g1) + (-cy)*(-g2) = 0\<close>
    and fbc_orth: "(bv - cx) * g1 = cy * g2"
    \<comment> \<open>fac = (h1, h2): foot of altitude from b to ca\<close>
    \<comment> \<open>collinear {(cx,cy), 0, (h1,h2)}: (-cx)*(h2-cy) = (h1-cx)*(-cy)\<close>
    and fac_col: "cx * h2 = h1 * cy"
    \<comment> \<open>orthogonal ((cx,cy)-0) ((bv,0)-(h1,h2)): cx*(bv-h1) + cy*(0-h2) = 0\<close>
    and fac_orth: "cx * (bv - h1) = cy * h2"
  shows "(n1 - f1)^2 + (n2 - f2)^2 = nr^2 \<and> (n1 - g1)^2 + (n2 - g2)^2 = nr^2 \<and> (n1 - h1)^2 + (n2 - h2)^2 = nr^2"
  using assms by algebra

theorem nine_point_circle_1:
  fixes a b c :: "real^2"
    and mbc mac mab :: "real^2"
    and fbc fac fab :: "real^2"
    and ncenter :: "real^2"
    and nradius :: real
  assumes "\<not> collinear {a, b, c}"
    and "midpoint a b = mab"
    and "midpoint b c = mbc"
    and "midpoint c a = mac"
    and "dist ncenter mbc = nradius"
    and "dist ncenter mac = nradius"
    and "dist ncenter mab = nradius"
    and "collinear {a, b, fab}" "orthogonal (a - b) (c - fab)"
    and "collinear {b, c, fbc}" "orthogonal (b - c) (a - fbc)"
    and "collinear {c, a, fac}" "orthogonal (c - a) (b - fac)"
  shows "dist ncenter fab = nradius \<and> dist ncenter fbc = nradius \<and> dist ncenter fac = nradius"
proof -
  have nr_pos: "0 \<le> nradius" using assms zero_le_dist by metis
  define a1 a2 b1 b2 c1 c2 n1 n2 f1 f2 g1 g2 h1 h2
    where "a1 = a$1" and "a2 = a$2"
      and "b1 = b$1" and "b2 = b$2"
      and "c1 = c$1" and "c2 = c$2"
      and "n1 = ncenter$1" and "n2 = ncenter$2"
      and "f1 = fab$1" and "f2 = fab$2"
      and "g1 = fbc$1" and "g2 = fbc$2"
      and "h1 = fac$1" and "h2 = fac$2"
  note defs = a1_def a2_def b1_def b2_def c1_def c2_def
              n1_def n2_def f1_def f2_def g1_def g2_def h1_def h2_def
  have ncol: "(b1 - a1) * (c2 - a2) \<noteq> (c1 - a1) * (b2 - a2)"
    using assms(1) collinear_3_2d by (auto simp: defs)
  have dist1: "(n1 - (b1+c1)/2)^2 + (n2 - (b2+c2)/2)^2 = nradius^2"
    using assms(3,5)[symmetric] by (simp add: midpoint_def dist_real2_sq defs)
  have dist2: "(n1 - (c1+a1)/2)^2 + (n2 - (c2+a2)/2)^2 = nradius^2"
    using assms(4,6)[symmetric] by (simp add: midpoint_def dist_real2_sq defs)
  have dist3: "(n1 - (a1+b1)/2)^2 + (n2 - (a2+b2)/2)^2 = nradius^2"
    using assms(2,7)[symmetric] by (simp add: midpoint_def dist_real2_sq defs)
  have col: "(b1 - a1) * (f2 - a2) = (f1 - a1) * (b2 - a2)"
            "(c1 - b1) * (g2 - b2) = (g1 - b1) * (c2 - b2)"
            "(a1 - c1) * (h2 - c2) = (h1 - c1) * (a2 - c2)"
    using assms collinear_3_2d by (auto simp: defs)+
  have orth: "(a1 - b1) * (c1 - f1) + (a2 - b2) * (c2 - f2) = 0"
             "(b1 - c1) * (a1 - g1) + (b2 - c2) * (a2 - g2) = 0"
             "(c1 - a1) * (b1 - h1) + (c2 - a2) * (b2 - h2) = 0"
    using assms
    by (simp_all add: orthogonal_def inner_real2 defs)
  have "(n1 - f1)^2 + (n2 - f2)^2 = nradius^2 \<and>
        (n1 - g1)^2 + (n2 - g2)^2 = nradius^2 \<and>
        (n1 - h1)^2 + (n2 - h2)^2 = nradius^2"
    using dist1 dist2 dist3 col orth ncol
    by algebra
  then show ?thesis
    using nr_pos  
    by (simp add: dist_real2_sq f1_def f2_def g1_def g2_def h1_def h2_def n1_def n2_def power2_eq_imp_eq)
qed


theorem nine_point_circle_2:
  fixes a b c :: "real^2"
    and mbc mac mab :: "real^2"
    and fbc fac fab :: "real^2"
    and ncenter oc :: "real^2"
    and nradius :: real
  assumes "\<not> collinear {a, b, c}"
    and "midpoint a b = mab"
    and "midpoint b c = mbc"
    and "midpoint c a = mac"
    and "dist ncenter mbc = nradius"
    and "dist ncenter mac = nradius"
    and "dist ncenter mab = nradius"
    and "collinear {a, b, fab}" "orthogonal (a - b) (c - fab)"
    and "collinear {b, c, fbc}" "orthogonal (b - c) (a - fbc)"
    and "collinear {c, a, fac}" "orthogonal (c - a) (b - fac)"
    and "collinear {oc, a, fbc}" "collinear {oc, b, fac}" "collinear {oc, c, fab}"
  shows "dist ncenter (midpoint oc a) = nradius \<and>
         dist ncenter (midpoint oc b) = nradius \<and>
         dist ncenter (midpoint oc c) = nradius"
proof -
  have nr_pos: "0 \<le> nradius" using assms(5) zero_le_dist by metis
  define a1 a2 b1 b2 c1 c2 n1 n2 f1 f2 g1 g2 h1 h2 o1 o2
    where "a1 = a$1" and "a2 = a$2"
      and "b1 = b$1" and "b2 = b$2"
      and "c1 = c$1" and "c2 = c$2"
      and "n1 = ncenter$1" and "n2 = ncenter$2"
      and "f1 = fab$1" and "f2 = fab$2"
      and "g1 = fbc$1" and "g2 = fbc$2"
      and "h1 = fac$1" and "h2 = fac$2"
      and "o1 = oc$1" and "o2 = oc$2"
  note defs = a1_def a2_def b1_def b2_def c1_def c2_def
              n1_def n2_def f1_def f2_def g1_def g2_def h1_def h2_def o1_def o2_def
  have ncol: "(b1 - a1) * (c2 - a2) \<noteq> (c1 - a1) * (b2 - a2)"
    using assms(1) collinear_3_2d by (auto simp: defs)
  have dist1: "(n1 - (b1+c1)/2)^2 + (n2 - (b2+c2)/2)^2 = nradius^2"
    using assms(3,5)[symmetric] by (simp add: midpoint_def dist_real2_sq defs)
  have dist2: "(n1 - (c1+a1)/2)^2 + (n2 - (c2+a2)/2)^2 = nradius^2"
    using assms(4,6)[symmetric] by (simp add: midpoint_def dist_real2_sq defs)
  have dist3: "(n1 - (a1+b1)/2)^2 + (n2 - (a2+b2)/2)^2 = nradius^2"
    using assms(2,7)[symmetric] by (simp add: midpoint_def dist_real2_sq defs)
  have col: "(b1 - a1) * (f2 - a2) = (f1 - a1) * (b2 - a2)"
            "(c1 - b1) * (g2 - b2) = (g1 - b1) * (c2 - b2)"
            "(a1 - c1) * (h2 - c2) = (h1 - c1) * (a2 - c2)"
    using assms collinear_3_2d by (auto simp: defs)+
  have orth: "(a1 - b1) * (c1 - f1) + (a2 - b2) * (c2 - f2) = 0"
             "(b1 - c1) * (a1 - g1) + (b2 - c2) * (a2 - g2) = 0"
             "(c1 - a1) * (b1 - h1) + (c2 - a2) * (b2 - h2) = 0"
    using assms by (simp_all add: orthogonal_def inner_real2 defs)
  have oc_col: "(a1 - o1) * (g2 - o2) = (g1 - o1) * (a2 - o2)"
               "(b1 - o1) * (h2 - o2) = (h1 - o1) * (b2 - o2)"
               "(c1 - o1) * (f2 - o2) = (f1 - o1) * (c2 - o2)"
    using assms collinear_3_2d by (auto simp: defs)+
  \<comment> \<open>Derive direct orthogonality conditions for the orthocenter,
      eliminating the altitude-foot variables from the final algebra calls.\<close>
  have oc_orth: "(b1 - c1) * (o1 - a1) + (b2 - c2) * (o2 - a2) = 0"
                "(c1 - a1) * (o1 - b1) + (c2 - a2) * (o2 - b2) = 0"
                "(a1 - b1) * (o1 - c1) + (a2 - b2) * (o2 - c2) = 0"
    using oc_col col orth ncol by algebra+
  have "(n1 - (o1+a1)/2)^2 + (n2 - (o2+a2)/2)^2 = nradius^2"
    using dist1 dist2 dist3 oc_orth ncol by algebra
  moreover have "(n1 - (o1+b1)/2)^2 + (n2 - (o2+b2)/2)^2 = nradius^2"
    using dist1 dist2 dist3 oc_orth ncol by algebra
  moreover have "(n1 - (o1+c1)/2)^2 + (n2 - (o2+c2)/2)^2 = nradius^2"
    using dist1 dist2 dist3 oc_orth ncol by algebra
  ultimately show ?thesis
    using nr_pos by (simp add: dist_real2_sq defs midpoint_def power2_eq_imp_eq)
qed

end
