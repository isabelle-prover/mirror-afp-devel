(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Intersecting Chord Theorem\<close>

theory Chord_Segments
imports
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
  "../Triangle/Triangle"
begin

subsection \<open>Preliminaries\<close>

subsubsection \<open>Addition to Fields\<close>

lemma divide_eq_minus_1_iff:
  fixes a b :: "'a :: field"
  shows "(a / b = - 1) \<longleftrightarrow> b \<noteq> 0 \<and> a = - b"
using divide_eq_1_iff by fastforce

subsubsection \<open>Addition to Power\<close>

lemma power2_eq_iff_nonneg:
  fixes x y :: "'a :: linordered_semidom"
  assumes "0 \<le> x" "0 \<le> y"
  shows "(x ^ 2 = y ^ 2) \<longleftrightarrow> x = y"
using assms power2_eq_imp_eq by blast

subsubsection \<open>Addition to Transcendental\<close>

lemma arccos_minus_abs:
  assumes "\<bar>x\<bar> \<le> 1"
  shows "arccos (- x) = pi - arccos x"
using assms by (simp add: arccos_minus)

subsubsection \<open>Additions to Convex Euclidean Space\<close>

lemma between_commute:
  "between (A, B) X \<longleftrightarrow> between (B, A) X"
by (simp add: between_mem_segment closed_segment_commute)

lemma between_same:
  assumes "between (a, a) x"
  shows "x = a"
using assms unfolding between_mem_segment by simp

lemma betweenI:
  assumes "0 \<le> u" "u \<le> 1" "x = (1 - u) *\<^sub>R a + u *\<^sub>R b"
  shows "between (a, b) x"
using assms unfolding between_def closed_segment_def by auto

lemma betweenE:
  assumes "between (a, b) x"
  obtains u where "0 \<le> u" "u \<le> 1" "x = (1 - u) *\<^sub>R a + u *\<^sub>R b"
using assms unfolding between_def closed_segment_def by auto

lemma betweenI':
  assumes "0 \<le> u" "u \<le> 1" "x = u *\<^sub>R a + (1 - u) *\<^sub>R b"
  shows "between (a, b) x"
proof -
  from assms have "between (b, a) x" by (auto intro: betweenI)
  from this show "between (a, b) x" by (simp add: between_commute)
qed

lemma betweenE':
  assumes "between (a, b) x"
  obtains u where "0 \<le> u" "u \<le> 1" "x = u *\<^sub>R a + (1 - u) *\<^sub>R b"
proof -
  from assms have "between (b, a) x" by (simp add: between_commute)
  from this obtain u where "0 \<le> u" "u \<le> 1" "x = u *\<^sub>R a + (1 - u) *\<^sub>R b"
    by (auto elim: betweenE)
  from this that show thesis by blast
qed

lemma between_implies_scaled_diff:
  assumes "between (S, T) X" "between (S, T) Y" "S \<noteq> Y"
  obtains c where "(X - Y) = c *\<^sub>R (S - Y)"
proof -
  from \<open>between (S, T) X\<close> obtain u\<^sub>X where X: "X = u\<^sub>X *\<^sub>R S + (1 - u\<^sub>X) *\<^sub>R T"
    by (auto elim: betweenE')
  from \<open>between (S, T) Y\<close> obtain u\<^sub>Y where Y: "Y = u\<^sub>Y *\<^sub>R S + (1 - u\<^sub>Y) *\<^sub>R T"
    by (auto elim: betweenE')
  have "X - Y = (u\<^sub>X - u\<^sub>Y) *\<^sub>R (S - T)"
  proof -
    from X Y have "X - Y =  u\<^sub>X *\<^sub>R S - u\<^sub>Y *\<^sub>R S + ((1 - u\<^sub>X) *\<^sub>R T - (1 - u\<^sub>Y) *\<^sub>R T)" by simp
    also have "\<dots> = (u\<^sub>X - u\<^sub>Y) *\<^sub>R S - (u\<^sub>X - u\<^sub>Y) *\<^sub>R T" by (simp add: scaleR_left.diff)
    finally show ?thesis by (simp add: real_vector.scale_right_diff_distrib)
  qed
  moreover from Y have "S - Y = (1 - u\<^sub>Y) *\<^sub>R (S - T)"
    by (simp add: real_vector.scale_left_diff_distrib real_vector.scale_right_diff_distrib)
  moreover note \<open>S \<noteq> Y\<close>
  ultimately have "(X - Y) = ((u\<^sub>X - u\<^sub>Y) / (1 - u\<^sub>Y)) *\<^sub>R (S - Y)" by auto
  from this that show thesis by blast
qed

lemma between_swap:
  fixes A B X Y :: "'a::euclidean_space"
  assumes "between (A, B) X"
  assumes "between (A, B) Y"
  shows "between (X, B) Y \<longleftrightarrow> between (A, Y) X"
using assms by (auto simp add: between)

lemma betweenE_if_dist_leq:
  fixes A B X :: "'a::euclidean_space"
  assumes "between (A, B) X"
  assumes "dist A X \<le> dist B X"
  obtains u where "1 / 2 \<le> u" "u \<le> 1" and "X = u *\<^sub>R A + (1 - u) *\<^sub>R B"
proof (cases "A = B")
  assume "A \<noteq> B"
  from \<open>between (A, B) X\<close> obtain u where u: "u \<ge> 0" "u \<le> 1" and X: "X = u *\<^sub>R A + (1 - u) *\<^sub>R B"
    by (auto elim: betweenE')
  from X have "X = B + u *\<^sub>R (A - B)" and "X = A + (u - 1) *\<^sub>R (A - B)"
    by (simp add: scaleR_diff_left real_vector.scale_right_diff_distrib)+
  from \<open>X = B + u *\<^sub>R (A - B)\<close> have dist_B: "dist B X = norm (u *\<^sub>R (A - B))"
    by (auto simp add: dist_norm)
  from \<open>X = A + (u - 1) *\<^sub>R (A - B)\<close> have dist_A: "dist A X = norm ((u - 1) *\<^sub>R (A - B))"
    by (auto simp add: dist_norm)
  from \<open>A \<noteq> B\<close> have "norm (A - B) > 0" by auto
  from this \<open>dist A X \<le> dist B X\<close> have "u \<ge> 1 / 2"
    using dist_A dist_B by simp
  from this \<open>u \<le> 1\<close> X that show thesis by blast
next
  assume "A = B"
  def u \<equiv> "1::real"
  from \<open>between (A, B) X\<close> \<open>A = B\<close> have "1 / 2 \<le> u" "u \<le> 1" "X = u *\<^sub>R A + (1 - u) *\<^sub>R B"
    unfolding u_def by (auto simp add: between_same)
  from this that show thesis by blast
qed

lemma dist_geq_iff_midpoint_in_between:
  fixes A B X :: "'a::euclidean_space"
  assumes "between (A, B) X"
  shows "dist A X \<le> dist B X \<longleftrightarrow> between (X, B) (midpoint A B)"
proof
  assume "dist A X \<le> dist B X"
  from \<open>between (A, B) X\<close> this obtain u
    where u: "1 / 2 \<le> u" "u \<le> 1" and X: "X = u *\<^sub>R A + (1 - u) *\<^sub>R B"
    using betweenE_if_dist_leq by blast
  have M: "midpoint A B = (1 / 2) *\<^sub>R A + (1 / 2) *\<^sub>R B"
    unfolding midpoint_def by (simp add: scaleR_add_right)
  from \<open>1 / 2 \<le> u\<close> have 1: "midpoint A B = (1 / (2 * u)) *\<^sub>R X + (1 - (1 / (2 * u))) *\<^sub>R B"
  proof -
    have "(2 - u * 2) / (2 * u) = 1 / u - u / u"
      using u(1) by (simp add: diff_divide_distrib)
    also have "\<dots> = 1 / u - 1" using u(1) by auto
    finally have "(2 - u * 2) / (2 * u) = 1 / u - 1" .
    from \<open>1 / 2 \<le> u\<close> this show ?thesis
      using X M by (simp add: scaleR_add_right scaleR_add_left[symmetric])
  qed
  moreover from u have 2: "(1 / (2 * u)) \<ge> 0" "(1 / (2 * u)) \<le> 1" by auto
  ultimately show "between (X, B) (midpoint A B)"
    using betweenI' by blast
next
  assume "between (X, B) (midpoint A B)"
  from this have "between (A, midpoint A B) X"
    using \<open>between (A, B) X\<close> between_midpoint(1) between_swap by blast
  from this have "dist A X \<le> dist A (midpoint A B)"
    using between zero_le_dist by force
  also have "dist A (midpoint A B) \<le> dist B (midpoint A B)"
    by (simp add: dist_midpoint)
  also from \<open>between (X, B) (midpoint A B)\<close> have "dist B (midpoint A B) \<le> dist B X"
    using between zero_le_dist by (metis add.commute dist_commute le_add_same_cancel1)
  finally show "dist A X \<le> dist B X" .
qed

subsubsection \<open>Additions to Angles\<close>

lemma vangle_scales:
  assumes "0 < c"
  shows "vangle (c *\<^sub>R v\<^sub>1) v\<^sub>2 = vangle v\<^sub>1 v\<^sub>2"
using assms unfolding vangle_def by auto

lemma vangle_inverse:
  "vangle (- v\<^sub>1) v\<^sub>2 = pi - vangle v\<^sub>1 v\<^sub>2"
proof -
  have "\<bar>v\<^sub>1 \<bullet> v\<^sub>2 / (norm v\<^sub>1 * norm v\<^sub>2)\<bar> \<le> 1"
  proof cases
    assume "v\<^sub>1 \<noteq> 0 \<and> v\<^sub>2 \<noteq> 0"
    from this show ?thesis by (simp add: Cauchy_Schwarz_ineq2)
  next
    assume "\<not> (v\<^sub>1 \<noteq> 0 \<and> v\<^sub>2 \<noteq> 0)"
    from this show ?thesis by auto
  qed
  from this show ?thesis
    unfolding vangle_def by (simp add: arccos_minus_abs)
qed

lemma orthogonal_iff_angle:
  shows "orthogonal (A - B) (C - B) \<longleftrightarrow> angle A B C = pi / 2"
unfolding angle_def by (auto simp only: orthogonal_iff_vangle)

lemma angle_inverse:
  assumes "between (A, C) B"
  assumes "A \<noteq> B" "B \<noteq> C"
  shows "angle A B D = pi - angle C B D"
proof -
  from \<open>between (A, C) B\<close> obtain u where u: "u \<ge> 0" "u \<le> 1"
    and X: "B = u *\<^sub>R A + (1 - u) *\<^sub>R C" by (auto elim: betweenE')
  from \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> X have "u \<noteq> 0" "u \<noteq> 1" by auto
  have "0 < ((1 - u) / u)"
    using \<open>u \<noteq> 0\<close> \<open>u \<noteq> 1\<close> \<open>u \<ge> 0\<close> \<open>u \<le> 1\<close> by simp
  from X have "A - B = - (1 - u) *\<^sub>R (C - A)"
    by (simp add: real_vector.scale_right_diff_distrib real_vector.scale_left_diff_distrib)
  moreover from X have "C - B = u *\<^sub>R (C - A)"
    by (simp add: scaleR_diff_left real_vector.scale_right_diff_distrib)
  ultimately have "A - B = - (((1 - u) / u) *\<^sub>R (C - B))"
    using \<open>u \<noteq> 0\<close> by simp (metis minus_diff_eq real_vector.scale_minus_left)
  from this have "vangle (A - B) (D - B) = pi - vangle (C - B) (D - B)"
    using \<open>0 < (1 - u) / u\<close> by (simp add: vangle_inverse vangle_scales)
  from this show ?thesis
    unfolding angle_def by simp
qed

lemma strictly_between_implies_angle_eq_pi:
  assumes "between (A, C) B"
  assumes "A \<noteq> B" "B \<noteq> C"
  shows "angle A B C = pi"
proof -
  from \<open>between (A, C) B\<close> obtain u where u: "u \<ge> 0" "u \<le> 1"
    and X: "B = u *\<^sub>R A + (1 - u) *\<^sub>R C" by (auto elim: betweenE')
  from \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> X have "u \<noteq> 0" "u \<noteq> 1" by auto
  from \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> \<open>between (A, C) B\<close> have "A \<noteq> C"
    using between_same by blast
  from X have "A - B = - (1 - u) *\<^sub>R (C - A)"
    by (simp add: real_vector.scale_right_diff_distrib real_vector.scale_left_diff_distrib)
  moreover from this have "dist A B = norm ((1 - u) *\<^sub>R (C - A))"
    using \<open>u \<ge> 0\<close> \<open>u \<le> 1\<close> by (simp add: dist_norm)
  moreover from X have "C - B = u *\<^sub>R (C - A)"
    by (simp add: scaleR_diff_left real_vector.scale_right_diff_distrib)
  moreover from this have "dist C B = norm (u *\<^sub>R (C - A))"
    by (simp add: dist_norm)
  ultimately have "(A - B) \<bullet> (C - B) / (dist A B * dist C B) = u * (u - 1) / (\<bar>1 - u\<bar> * \<bar>u\<bar>)"
    using \<open>A \<noteq> C\<close> by (simp add: dot_square_norm power2_eq_square)
  also have "\<dots> = - 1"
    using \<open>u \<noteq> 0\<close> \<open>u \<noteq> 1\<close> \<open>u \<ge> 0\<close> \<open>u \<le> 1\<close> by (simp add: divide_eq_minus_1_iff)
  finally show ?thesis
    unfolding angle_altdef by simp
qed

subsubsection \<open>Additions to Triangles\<close>

lemma pythagoras:
  fixes A B C :: "'a :: euclidean_space"
  assumes "orthogonal (A - C) (B - C)"
  shows "(dist B C) ^ 2 + (dist C A) ^ 2 = (dist A B) ^ 2"
proof -
  from assms have "cos (angle A C B) = 0"
    by (metis orthogonal_iff_angle cos_pi_half)
  from this show ?thesis
    by (simp add: cosine_law_triangle[of A B C] dist_commute)
qed

lemma isosceles_triangle_orthogonal_on_midpoint:
  fixes A B C :: "'a::euclidean_space"
  assumes "dist C A = dist C B"
  shows "orthogonal (C - midpoint A B) (A - midpoint A B)"
proof (cases "A = B")
  assume "A \<noteq> B"
  let ?M = "midpoint A B"
  have "angle A ?M C = pi - angle B ?M C"
    using \<open>A \<noteq> B\<close> angle_inverse between_midpoint(1) midpoint_eq_endpoint by metis
  moreover have "angle A ?M C = angle C ?M B"
  proof -
    have congruence: "congruent_triangle C A ?M C B ?M"
    proof (rule congruent_triangleI_sss)
      show "dist C A = dist C B" using assms .
      show "dist A ?M = dist B ?M" by (simp add: dist_midpoint)
      show "dist C (midpoint A B) = dist C (midpoint A B)" ..
    qed
    from this show ?thesis by (simp add: congruent_triangle.angles(6))
  qed
  ultimately have "angle A ?M C = pi / 2" by (simp add: angle_commute)
  from this show ?thesis
    by (simp add: orthogonal_iff_angle orthogonal_commute)
next
  assume "A = B"
  from this show ?thesis
    by (simp add: midpoint_refl orthogonal_clauses(1))
qed

subsection \<open>Properties of Chord Segments\<close>

lemma chord_property:
  fixes S C :: "'a :: euclidean_space"
  assumes "dist C S = dist C T"
  assumes "between (S, T) X"
  shows "dist S X * dist X T = (dist C S) ^ 2 - (dist C X) ^ 2"
proof -
  def M \<equiv> "midpoint S T"
  have "between (S, T) M"
    unfolding M_def by (simp add: between_midpoint(1))
  have "dist T M = dist S M"
    unfolding M_def by (simp add: dist_midpoint)

  have distances: "max (dist S X) (dist X T) = (dist S M) + (dist X M) \<and>
    min (dist S X) (dist X T) = (dist S M) - (dist X M)"
  proof cases
    assume "dist S X \<le> dist X T"
    from this have "between (X, T) M"
      using \<open>between (S, T) X\<close> M_def
      by (simp add: dist_geq_iff_midpoint_in_between dist_commute)
    from this have "between (S, M) X"
      using \<open>between (S, T) X\<close> \<open>between (S, T) M\<close> between_swap by blast
    from \<open>between (X, T) M\<close> have "dist X T = dist X M + dist M T"
      using between by auto
    moreover from \<open>between (S, M) X\<close> have "dist S X = dist S M - dist M X"
      using between dist_commute by force
    ultimately show ?thesis
      using \<open>dist S X \<le> dist X T\<close> \<open>dist T M = dist S M\<close>
      by (simp add: add.commute dist_commute max_def min_def)
  next
    assume "\<not> (dist S X \<le> dist X T)"
    from this have "dist T X \<le> dist S X" by (simp add: dist_commute)
    from this have "between (S, X) M"
      using \<open>between (S, T) X\<close> M_def
      by (simp add: dist_geq_iff_midpoint_in_between midpoint_sym between_commute)
    from this have "between (T, M) X"
      using \<open>between (S, T) X\<close> \<open>between (S, T) M\<close> between_swap between_commute by blast
    from \<open>between (S, X) M\<close> have "dist S X = dist S M + dist M X"
      using between by auto
    moreover from \<open>between (T, M) X\<close> have "dist T X = dist T M - dist M X"
      using between dist_commute by force
    ultimately show ?thesis
      using \<open>\<not> dist S X \<le> dist X T\<close> \<open>dist T M = dist S M\<close>
      by (metis dist_commute max_def min_def)
  qed

  have "orthogonal (C - M) (S - M)"
    using \<open>dist C S = dist C T\<close> M_def
    by (auto simp add: isosceles_triangle_orthogonal_on_midpoint)
  have "orthogonal (C - M) (X - M)"
  proof -
    have "between (S, T) M"
      using M_def between_midpoint(1) by blast
    obtain c where "(X - M) = c *\<^sub>R (S - M)"
    proof (cases "S = M")
      assume "S \<noteq> M"
      from \<open>between (S, T) X\<close> \<open>between (S, T) M\<close> this obtain c where "(X - M) = c *\<^sub>R (S - M)"
        using between_implies_scaled_diff by blast
      from this that show thesis by blast
    next
      assume "S = M"
      from this \<open>between (S, T) X\<close> have "X = M"
        unfolding M_def by (metis between_same midpoint_eq_endpoint(1))
      from \<open>X = M\<close> \<open>S = M\<close> have "(X - M) = 0 *\<^sub>R (S - M)" by simp
      from this that show thesis by blast
    qed
    from this \<open>orthogonal (C - M) (S - M)\<close> show ?thesis
      by (auto intro: orthogonal_clauses(2))
  qed
  from \<open>orthogonal (C - M) (S - M)\<close> \<open>orthogonal (C - M) (X - M)\<close> have
    "(dist S M) ^ 2 + (dist M C) ^ 2 = (dist C S) ^ 2"
    "(dist X M) ^ 2 + (dist M C) ^ 2 = (dist C X) ^ 2"
    by (auto simp only: pythagoras)
  from this have geometric_observation:
    "(dist S M) ^ 2 = (dist C S) ^ 2 - (dist M C) ^ 2"
    "(dist X M) ^ 2 = (dist C X) ^ 2 - (dist M C) ^ 2"
    by auto

  have "dist S X * dist X T = max (dist S X) (dist X T) * min (dist S X) (dist X T)"
    by (auto split: split_max)
  also have "\<dots> = ((dist S M) + (dist X M)) * ((dist S M) - (dist X M))"
    using distances by simp
  also have "\<dots> = (dist S M) ^ 2 - (dist X M) ^ 2"
    by (simp add: field_simps power2_eq_square)
  also have "\<dots> = ((dist C S) ^ 2 - (dist M C) ^ 2) - ((dist C X) ^ 2 - (dist M C) ^ 2)"
    using geometric_observation by simp
  also have "\<dots> = (dist C S) ^ 2 - (dist C X) ^ 2" by simp
  finally show ?thesis .
qed

theorem product_of_chord_segments:
  fixes S\<^sub>1 T\<^sub>1 S\<^sub>2 T\<^sub>2 X C :: "'a :: euclidean_space"
  assumes "between (S\<^sub>1, T\<^sub>1) X" "between (S\<^sub>2, T\<^sub>2) X"
  assumes "dist C S\<^sub>1 = r" "dist C T\<^sub>1 = r"
  assumes "dist C S\<^sub>2 = r" "dist C T\<^sub>2 = r"
  shows "dist S\<^sub>1 X * dist X T\<^sub>1 = dist S\<^sub>2 X * dist X T\<^sub>2"
proof -
  from \<open>dist C S\<^sub>1 = r\<close> \<open>dist C T\<^sub>1 = r\<close> \<open>between (S\<^sub>1, T\<^sub>1) X\<close>
  have "dist S\<^sub>1 X * dist X T\<^sub>1 = r ^ 2 - (dist C X) ^ 2"
    by (subst chord_property) auto
  also from \<open>dist C S\<^sub>2 = r\<close> \<open>dist C T\<^sub>2 = r\<close> \<open>between (S\<^sub>2, T\<^sub>2) X\<close>
  have "\<dots> = dist S\<^sub>2 X * dist X T\<^sub>2"
    by (subst chord_property) auto
  finally show ?thesis .
qed

end