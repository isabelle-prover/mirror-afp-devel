(*  Author: Mathias Schack Rabing <mathiasrabing@outlook.com> *)

theory Ceva
imports
  Triangle.Triangle
begin

definition\<^marker>\<open>tag important\<close> Triangle_area :: "'a::real_inner \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real"
  where "Triangle_area x y z = abs(sin (angle x y z)) * dist x y * dist y z"

lemma Triangle_area_per1 : "Triangle_area a b c = Triangle_area b c a"
proof -
  have H : "abs(sin (angle a b c)) * dist b c = abs(sin (angle b a c)) * dist a c"
    using sine_law_triangle
    by (metis (mono_tags, opaque_lifting) abs_mult real_abs_dist)
  show ?thesis                                                      
    apply(simp add: Triangle_area_def)
    using H
    by (metis abs_of_nonneg angle_commute dist_commute sin_angle_nonneg sine_law_triangle)
qed

lemma Triangle_area_per2 : "Triangle_area a b c = Triangle_area b a c"
proof -
  have H : "abs(sin (angle a b c)) * dist b c = abs(sin (angle b a c)) * dist a c"
    using sine_law_triangle
    by (metis (mono_tags, opaque_lifting) abs_mult real_abs_dist)
  show ?thesis
    using H
    by (simp add: Triangle_area_def dist_commute[of a b])
qed

lemma collinear_angle: 
  fixes a b c :: "'a::euclidean_space"
  shows "collinear {a, b, c} \<Longrightarrow> a \<noteq> b \<Longrightarrow> b \<noteq> c \<Longrightarrow> angle a b c \<in> {0, pi}"
proof (cases "a = c")
  case True
  assume Col : "collinear {a, b, c}"
  assume H1 : "a \<noteq> b"
  assume H2 : "b \<noteq> c"
  assume H3 : "a = c"
  show ?thesis
    using H1 H3 angle_refl_mid
    by auto
next
  case False
  assume Col : "collinear {a, b, c}"
  assume H1 : "a \<noteq> b"
  assume H2 : "b \<noteq> c"
  assume H3 : "a \<noteq> c"
  consider (bet1) "between (b, c) a" | (bet2) "between (c, a) b" | (bet3) "between (a, b) c"
    using Col collinear_between_cases
    by auto
  then show ?thesis
  proof cases
    case bet1
    assume B1: "between (b, c) a"
    have H: "angle c a b = pi"
      apply(rule strictly_between_implies_angle_eq_pi)
      using B1 H3 H1
      by (auto simp: between_commute)
    show ?thesis
      by (smt (verit) H angle_nonneg angle_sum_triangle insert_iff)
  next
    case bet2
    assume B1: "between (c, a) b"
    show ?thesis
      by (metis H1 H2 bet2 between_commute sin_angle_zero_iff sin_pi strictly_between_implies_angle_eq_pi)
  next
    case bet3
    assume B1: "between (a, b) c"
    have H: "angle b c a = pi"
      apply(rule strictly_between_implies_angle_eq_pi)
      using B1 H3 H2 H1
      by (auto simp: between_commute)
    show ?thesis
      by (smt (verit) H angle_nonneg angle_sum_triangle insert_iff)
    qed
qed

lemma Triangle_area_0 : 
  fixes c :: "'a::euclidean_space"
  shows "Triangle_area a b c = 0 \<longleftrightarrow> collinear {a,b,c}"
proof -
  show ?thesis
    apply(simp add: Triangle_area_def)
    using collinear_angle
    by (metis (no_types, lifting) Angles.angle_collinear collinear_2 insertCI insert_absorb sin_angle_zero_iff)
qed


lemma Angle_longer_side : 
  fixes a :: "'a :: euclidean_space"
  assumes Col : "between (b,d) c"
  assumes NeqBC : "b \<noteq> c"
  shows "angle a b c = angle a b d"
proof (cases "a = b \<or> b = d \<or> c = d")
  case True
  then show ?thesis
    using Col
    by auto
next
  case False
  assume H : "\<not> (a = b \<or> b = d \<or> c = d)"
  have NeqAB : "a \<noteq> b"
    using H
    by auto
  have NeqBD : "b \<noteq> d"
    using H
    by auto
  have NeqCD : "c \<noteq> d"
    using H
    by auto
  have Goal1 : "norm (d - b) *\<^sub>R (c - b) = norm (c - b) *\<^sub>R (d - b)"
    apply(rule vangle_eq_0D)
    using Col
    by (metis Groups.add_ac(2) NeqBC NeqCD add_le_same_cancel1 angle_def angle_nonneg angle_sum_triangle eq_add_iff order.eq_iff strictly_between_implies_angle_eq_pi)
  have Goal2 : "(a - b) \<bullet> (c - b) * norm (d - b) \<noteq>
    (a - b) \<bullet> (d - b) * norm (c - b) \<Longrightarrow> a = b"
    apply(simp only: mult.commute[where b="norm (d - b)"])
    apply(simp only: mult.commute[where b="norm (c - b)"])
    apply(simp only: real_inner_class.inner_scaleR_right[THEN sym])
    using Goal1
    by auto
  have Goal : "(a - b) \<bullet> (c - b) * (norm (a - b) * norm (d - b)) =
     (a - b) \<bullet> (d - b) * (norm (a - b) * norm (c - b))"
    using Goal2
    by auto
  show ?thesis
    apply(simp add: angle_def)
    using NeqAB NeqBD NeqCD NeqBC
    apply(simp only: vangle_def)
    using Goal
    by (smt (verit, best) eq_iff_diff_eq_0 frac_eq_eq no_zero_divisors norm_eq_zero)
qed

lemma Triangle_area_comb :
  fixes c :: "'a::euclidean_space"
  assumes Col : "between (b,c) m"
  shows "Triangle_area a b m + Triangle_area a c m = Triangle_area a b c"
proof (cases "b = m \<or> c = m")
  case True
  then
  have Eq : "b = m \<or> c = m"
    by auto
  have Tri0 : "Triangle_area a m m = 0"
    by (auto simp: Triangle_area_0)
  show ?thesis
    using Eq Tri0
    using Triangle_area_per1 Triangle_area_per2
    by (metis add.right_neutral add_0)
next
  case False
  then 
  have Neq : "\<not>(b = m \<or> c = m)"
    by auto
  have NeqBM : "b \<noteq> m"
    using Neq
    by auto
  have NeqCM : "c \<noteq> m"
    using Neq
    by auto
  have Angle1 : "angle a b m = angle a b c"
    using Col Angle_longer_side NeqBM NeqCM
    by auto
  have Angle2 : "angle a c m = angle a c b"
    using Col Angle_longer_side NeqBM NeqCM between_commute
    by metis
  have "\<bar>sin (angle a b m)\<bar> * dist a b * dist b m +
        \<bar>sin (angle a c m)\<bar> * dist a c * dist c m =
        \<bar>sin (angle a b c)\<bar> * dist a b * dist b m +
        \<bar>sin (angle a c b)\<bar> * dist a c * dist c m"
    using Angle1 Angle2
    by simp
  also have "\<bar>sin (angle a b c)\<bar> * dist a b * dist b m +
        \<bar>sin (angle a c b)\<bar> * dist a c * dist c m =
        \<bar>sin (angle a b c)\<bar> * dist a b * dist b m +
        \<bar>sin (angle a b c)\<bar> * dist a b * dist c m"
    using sine_law_triangle
    by (smt (verit) congruent_triangle_sss(17) dist_commute sin_angle_nonneg)
  also have 
       "\<bar>sin (angle a b c)\<bar> * dist a b * dist b m +
        \<bar>sin (angle a b c)\<bar> * dist a b * dist c m =
        \<bar>sin (angle a b c)\<bar> * dist a b * (dist b m + dist c m)"
    by (metis inner_add(2) inner_real_def)
  also have "\<bar>sin (angle a b c)\<bar> * dist a b * (dist b m + dist c m) =
        \<bar>sin (angle a b c)\<bar> * dist a b * dist b c"
    by (metis assms between dist_commute)
  finally have Goal : "\<bar>sin (angle a b m)\<bar> * dist a b * dist b m +
        \<bar>sin (angle a c m)\<bar> * dist a c * dist c m =
        \<bar>sin (angle a b c)\<bar> * dist a b * dist b c"
    by simp
  show ?thesis
    apply(simp add: Triangle_area_def)
    using Goal
    by blast
qed

lemma Triangle_area_cal :
  fixes a :: "'a::euclidean_space"
  assumes Col : "collinear {a,m,b}"
  shows "\<exists> k. dist a m * k = Triangle_area a c m \<and> dist b m * k = Triangle_area b c m"
proof (cases "b = m \<or> a = m")
  case True
  then 
  have Eq :"(a \<noteq> m \<and> b = m) \<or> (a = m \<and> b \<noteq> m) \<or> (a = m \<and> b = m)"
    by auto
  show ?thesis
    using Eq
    by(auto simp: Triangle_area_0 collinear_3_eq_affine_dependent exI[where x="Triangle_area a c m / dist a m"]
                     exI[where x="Triangle_area b c m / dist b m"])
next
  case False
  then
  have H : "\<not> (b = m \<or> a = m)"
    by simp
  have NeqBM : "b \<noteq> m" and NeqMA : "m \<noteq> a"
    using H
    by auto
  have H1: "dist a m * \<bar>sin (angle a m c)\<bar> * dist c m =
    \<bar>sin (angle a c m)\<bar> * dist a c * dist c m"
    using sine_law_triangle
    by (smt (verit) angle_commute dist_commute mult.commute sin_angle_nonneg)
  have "dist b m * \<bar>sin (angle a m c)\<bar> * dist c m =
    dist b m * \<bar>sin (pi - angle a m c)\<bar> * dist c m"
    by auto
  also have "dist b m * \<bar>sin (pi - angle a m c)\<bar> * dist c m =
    dist b m * \<bar>sin (angle b m c)\<bar> * dist c m"
    using angle_inverse[THEN sym] Col NeqBM NeqMA
    by (smt (verit, ccfv_SIG) Angle_longer_side angle_commute between_commute collinear_between_cases sin_pi_minus)
  also have "dist b m * \<bar>sin (angle b m c)\<bar> * dist c m =
    \<bar>sin (angle b c m)\<bar> * dist b c * dist c m"
    using sine_law_triangle
    by (metis abs_of_nonneg angle_commute dist_commute mult.commute sin_angle_nonneg)
  finally have H2: "dist b m * \<bar>sin (angle a m c)\<bar> * dist c m =
    \<bar>sin (angle b c m)\<bar> * dist b c * dist c m"
    by simp
  show ?thesis
    apply(simp add: Triangle_area_def)
    apply(rule exI[where x="\<bar>sin (angle a m c)\<bar> * dist c m"])
    using H1 H2
    by auto
qed

lemma Triangle_area_comb_alt :
  fixes a :: "'a::euclidean_space"
  assumes Col1 : "collinear {a,m,b}"
  assumes Col2 : "collinear {c,k,m}"
  shows Goal : "\<exists> h. dist a m * h = Triangle_area a c k \<and> dist b m * h = Triangle_area b c k"
proof -
  obtain "H" where TriB : "dist a m * H = Triangle_area a c m \<and> dist b m * H = Triangle_area b c m"
    using Col1 Triangle_area_cal by blast
  obtain "h" where TriS : "dist a m * h = Triangle_area a k m \<and> dist b m * h = Triangle_area b k m"
    using Col1 Triangle_area_cal by blast
  consider (bet1) "between (k, m) c" | (bet2) "between (m, c) k" | (bet3) "between (c, k) m"
    using Col2 collinear_between_cases
    by auto
  then show ?thesis
  proof cases
    case bet1
    have AreaAC : "dist a m * H = Triangle_area a c m" and AreaBC : "dist b m * H = Triangle_area b c m"
      using TriB
      by auto
    have AreaAM : "dist a m * h = Triangle_area a k m" and AreaBM : "dist b m * h = Triangle_area b k m"
      using TriS
      by auto
    assume Bet : "between (k, m) c"
    have "dist a m * (h - H) = dist a m * h - dist a m * H"
      by (simp add: right_diff_distrib)
    also have "dist a m * h - dist a m * H = Triangle_area a k m - Triangle_area a c m"
      using AreaAC AreaAM
      by auto
    also have "Triangle_area a k m - Triangle_area a c m  = Triangle_area a c k"
      using Bet Triangle_area_comb
      by (metis Triangle_area_per1 Triangle_area_per2 diff_eq_eq)
    finally have Goal1 : "dist a m * (h - H) = Triangle_area a c k"
      by simp
    have "dist b m * (h - H) = dist b m * h - dist b m * H"
      by (simp add: right_diff_distrib)
    also have "dist b m * h - dist b m * H = Triangle_area b k m - Triangle_area b c m"
      using AreaBC AreaBM
      by auto
    also have "Triangle_area b k m - Triangle_area b c m  = Triangle_area b c k"
      using Bet Triangle_area_comb
      by (metis Triangle_area_per1 Triangle_area_per2 diff_eq_eq)
    finally have Goal2 : "dist b m * (h - H) = Triangle_area b c k"
      by simp
    show ?thesis
      using Goal1 Goal2 by blast
  next
    case bet2
    have AreaAC : "dist a m * H = Triangle_area a c m" and AreaBC : "dist b m * H = Triangle_area b c m"
      using TriB
      by auto
    have AreaAM : "dist a m * h = Triangle_area a k m" and AreaBM : "dist b m * h = Triangle_area b k m"
      using TriS
      by auto
    assume Bet : "between (m, c) k"
    have "dist a m * (H - h) = dist a m * H - dist a m * h"
      by (simp add: right_diff_distrib)
    also have "dist a m * H - dist a m * h = Triangle_area a c m - Triangle_area a k m"
      using AreaAC AreaAM
      by auto
    also have "Triangle_area a c m - Triangle_area a k m  = Triangle_area a c k"
      using Bet Triangle_area_comb
      by (smt (verit) between_triv1)
    finally have Goal1 : "dist a m * (H - h) = Triangle_area a c k"
      by simp
    have "dist b m * (H - h) = dist b m * H - dist b m * h"
      by (simp add: right_diff_distrib)
    also have "dist b m * H - dist b m * h = Triangle_area b c m - Triangle_area b k m"
      using AreaBC AreaBM
      by auto
    also have "Triangle_area b c m - Triangle_area b k m  = Triangle_area b c k"
      using Bet Triangle_area_comb
      by (smt (verit) between_triv1)
    finally have Goal2 : "dist b m * (H - h) = Triangle_area b c k"
      by simp
    show ?thesis
      using Goal1 Goal2 by blast
  next
    case bet3
    have AreaAC : "dist a m * H = Triangle_area a c m" and AreaBC : "dist b m * H = Triangle_area b c m"
      using TriB
      by auto
    have AreaAM : "dist a m * h = Triangle_area a k m" and AreaBM : "dist b m * h = Triangle_area b k m"
      using TriS
      by auto
    assume Bet : "between (c, k) m"
    have "dist a m * (H + h) = Triangle_area a c k"
      by (simp add: AreaAC TriS Triangle_area_comb bet3 distrib_left)
    moreover have "dist b m * (H + h) = Triangle_area b c k"
      by (simp add: AreaBC TriS Triangle_area_comb bet3 distrib_left)
    ultimately show ?thesis
      by blast
    qed
qed

lemma Cevas : 
  fixes a :: "'a::euclidean_space"
  assumes MidCol : "collinear {a,k,d} \<and> collinear {b,k,e} \<and> collinear {c,k,f}"
  assumes TriCol : "collinear {a,f,b} \<and> collinear {a,e,c} \<and> collinear {b,d,c}"
  assumes Triangle : "\<not> collinear {a,b,c}"
  shows "dist a f * dist b d * dist c e = dist f b * dist d c * dist e a"
proof -
  obtain "n1" where Tri1: "dist a f * n1 = Triangle_area a c k \<and> dist b f * n1 = Triangle_area b c k"
    by (meson MidCol TriCol Triangle_area_comb_alt)
  obtain "n2" where Tri2 : "dist a e * n2 = Triangle_area a b k \<and> dist c e * n2 = Triangle_area c b k"
    by (meson MidCol TriCol Triangle_area_comb_alt)
  obtain "n3" where Tri3 : "dist b d * n3 = Triangle_area b a k \<and> dist c d * n3 = Triangle_area c a k"
    by (meson MidCol TriCol Triangle_area_comb_alt)
  have Tri1'1 : "dist a f * n1 = Triangle_area a c k" and Tri1'2 : "dist b f * n1 = Triangle_area b c k"
    using assms
    by (auto simp: Tri1)
  have Tri2'1 : "dist c e * n2 = Triangle_area c b k" and Tri2'2 : "dist a e * n2 = Triangle_area a b k"
    using assms
    by (auto simp: Tri2)
  have Tri3'1 : "dist c d * n3 = Triangle_area c a k" and Tri3'2 : "dist b d * n3 = Triangle_area b a k"
    using assms
    by (auto simp: Tri3)
  have "dist a f * n1 * dist b d * n3 * dist c e * n2 = 
       Triangle_area a c k * Triangle_area b a k * Triangle_area c b k"
    using Tri1'1 Tri2'1 Tri3'2
    by simp
  also have "Triangle_area a c k * Triangle_area b a k * Triangle_area c b k = 
       Triangle_area c a k * Triangle_area a b k * Triangle_area b c k"
    using Triangle_area_per2
    by metis
  also have "Triangle_area c a k * Triangle_area a b k * Triangle_area b c k =
       dist b f * n1 * dist c d * n3 * dist a e * n2"
    using Tri1'2 Tri2'2 Tri3'1
    by simp
  also have "dist b f * n1 * dist c d * n3 * dist a e * n2 =
       dist f b * n1 * dist d c * n3 * dist e a * n2"
    using dist_commute
    by metis
  finally have Goal: "dist a f * n1 * dist b d * n3 * dist c e * n2 = 
       dist f b * n1 * dist d c * n3 * dist e a * n2"
    by simp
  then consider (n2) "n2 = 0" | (n1) "n1 = 0" | (n3) "n3 = 0" | 
                (dist) "dist a f * (dist b d * dist c e) = dist f b * (dist d c * dist e a)"
     by auto
  then show ?thesis
  proof cases
    case n2
    then show ?thesis
    proof -
      assume n0 : "n2 = 0"
      have H1 : "Triangle_area c b k = 0"
        using Tri2'1 n0
        by auto
      have H1' : "collinear {c,b,k}"
        using H1 Triangle_area_0
        by auto
      have H1 : "Triangle_area a b k = 0"
        using Tri2'2 n0
        by auto
      have H2' : "collinear {a,b,k}"
        using H1 Triangle_area_0
        by auto
      have H : "b = k"
        using H1' H2' collinear_3_trans Triangle collinear_3_trans
        by (metis Triangle_area_0 Triangle_area_per1)
      have H1 : "b = f"
        using H Triangle collinear_3_trans MidCol TriCol
        by (metis doubleton_eq_iff)
      have H2 : "b = d"
        using H H1 Triangle collinear_3_trans MidCol TriCol
        by blast
      show ?thesis
        using H H1 H2
        by simp
    qed
  next
    case n1
    then show ?thesis
    proof -
      assume n0 : "n1 = 0"
      have H1 : "Triangle_area a c k = 0"
        using Tri1'1 n0
        by auto
      have H1' : "collinear {a,c,k}"
        using H1 Triangle_area_0
        by auto
      have H1 : "Triangle_area b c k = 0"
        using Tri1'2 n0
        by auto
      have H2' : "collinear {b,c,k}"
        using H1 Triangle_area_0
        by auto
      have H : "c = k"
        using H1' H2' collinear_3_trans Triangle collinear_3_trans
        by (smt (verit) insert_commute)
      have H1 : "c = d"
        using H H1' H2' Triangle
        by (metis Tri3'1 Tri3'2 Triangle_area_0 Triangle_area_per2 dist_eq_0_iff mult_eq_0_iff)
      have H2 : "c = e"
        using H H1 H1' H2' Triangle
        by (metis Tri2'1 Tri2'2 Triangle_area_0 Triangle_area_per2 dist_eq_0_iff mult_eq_0_iff)
      show ?thesis
        using H H1 H2
        by simp
    qed
  next
    case n3
    then show ?thesis
    proof -
      assume n0 : "n3 = 0"
      have H1 : "Triangle_area c a k = 0"
        using Tri3'1 n0
        by auto
      have H1' : "collinear {c,a,k}"
        using H1 Triangle_area_0
        by auto
      have H1 : "Triangle_area b a k = 0"
        using Tri3'2 n0
        by auto
      have H2' : "collinear {b,a,k}"
        using H1 Triangle_area_0
        by auto
      have H : "a = k"
        using H1' H2' collinear_3_trans Triangle
        by (metis (full_types) insert_commute)
      have H1 : "a = f"
        using H H1' H2' Triangle
        by (metis Tri1'1 Tri1'2 Triangle_area_0 Triangle_area_per1 dist_eq_0_iff mult_eq_0_iff)
      have H2 : "a = e"
        using H H1 H1' H2' collinear_3_trans Triangle
        by (metis MidCol TriCol collinear_3_eq_affine_dependent)
      show ?thesis
        using H H1 H2
        by simp
        qed
  next
    case dist
    then show ?thesis
      by auto
    qed
qed


end