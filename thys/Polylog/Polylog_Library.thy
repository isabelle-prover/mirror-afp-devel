(*
  File:     Polylog/Polylog_Library.thy
  Authors:  Manuel Eberl (University of Innsbruck)
*)
section \<open>Auxiliary material\<close>
theory Polylog_Library
imports
  "HOL-Complex_Analysis.Complex_Analysis"
  "Linear_Recurrences.Eulerian_Polynomials"
begin

subsection \<open>Miscellaneous\<close>

(* TODO: Move? *)

lemma linear_of_real [intro]: "linear of_real"
  by standard (auto simp: scaleR_conv_of_real)

lemma fps_conv_radius_fps_of_poly [simp]:
  fixes p :: "'a :: {banach, real_normed_div_algebra} poly"
  shows "fps_conv_radius (fps_of_poly p) = \<infinity>"
proof -
  have "conv_radius (poly.coeff p) = conv_radius (\<lambda>_. 0 :: 'a)"
    using MOST_coeff_eq_0 unfolding cofinite_eq_sequentially by (rule conv_radius_cong')
  also have "\<dots> = \<infinity>"
    by simp
  finally show ?thesis
    by (simp add: fps_conv_radius_def)
qed

lemma eval_fps_power: 
  fixes F :: "'a :: {banach, real_normed_div_algebra, comm_ring_1} fps"
  assumes z: "norm z < fps_conv_radius F"
  shows      "eval_fps (F ^ n) z = eval_fps F z ^ n"
proof (induction n)
  case 0
  thus ?case
    by (auto simp: eval_fps_mult)
next
  case (Suc n)
  have "eval_fps (F ^ Suc n) z = eval_fps (F * F ^ n) z"
    by simp
  also from z have "\<dots> = eval_fps F z * eval_fps (F ^ n) z"
    by (subst eval_fps_mult) (auto intro!: less_le_trans[OF _ fps_conv_radius_power])
  finally show ?case
    using Suc.IH by simp
qed   

lemma eval_fps_of_poly [simp]: "eval_fps (fps_of_poly p) z = poly p z"
proof -
  have "(\<lambda>n. poly.coeff p n * z ^ n) sums poly p z"
    unfolding poly_altdef by (rule sums_finite) (auto simp: coeff_eq_0)
  moreover have "(\<lambda>n. poly.coeff p n * z ^ n) sums eval_fps (fps_of_poly p) z"
    using sums_eval_fps[of z "fps_of_poly p"] by simp
  ultimately show ?thesis
    using sums_unique2 by blast
qed

lemma poly_holomorphic_on [holomorphic_intros]:
  assumes [holomorphic_intros]: "f holomorphic_on A"
  shows   "(\<lambda>z. poly p (f z)) holomorphic_on A"
  unfolding poly_altdef by (intro holomorphic_intros)

lemma simply_connected_eq_global_primitive:
  assumes "simply_connected S" "open S" "f holomorphic_on S"
  obtains h where "\<And>z. z \<in> S \<Longrightarrow> (h has_field_derivative f z) (at z)"
  using simply_connected_eq_global_primitive[of S] assms that by blast

lemma
  assumes "x \<in> closed_segment y z"
  shows in_closed_segment_imp_Re_in_closed_segment: "Re x \<in> closed_segment (Re y) (Re z)" (is ?th1)
    and in_closed_segment_imp_Im_in_closed_segment: "Im x \<in> closed_segment (Im y) (Im z)" (is ?th2)
proof -
  from assms obtain t where t: "t \<in> {0..1}" "x = linepath y z t"
    by (metis imageE linepath_image_01)
  have "Re x = linepath (Re y) (Re z) t" "Im x = linepath (Im y) (Im z) t"
    by (simp_all add: t Re_linepath' Im_linepath')
  with t(1) show ?th1 ?th2
    using linepath_in_path[of t "Re y" "Re z"] linepath_in_path[of t "Im y" "Im z"] by simp_all
qed

lemma linepath_in_open_segment: "t \<in> {0<..<1} \<Longrightarrow> x \<noteq> y \<Longrightarrow> linepath x y t \<in> open_segment x y"
  unfolding greaterThanLessThan_iff by (metis in_segment(2) linepath_def)

lemma in_open_segment_imp_Re_in_open_segment:
  assumes "x \<in> open_segment y z" "Re y \<noteq> Re z"
  shows   "Re x \<in> open_segment (Re y) (Re z)"
proof -
  from assms obtain t where t: "t \<in> {0<..<1}" "x = linepath y z t"
    by (metis greaterThanLessThan_iff in_segment(2) linepath_def)
  have "Re x = linepath (Re y) (Re z) t"
    by (simp_all add: t Re_linepath')
  with t(1) show ?thesis
    using linepath_in_open_segment[of t "Re y" "Re z"] assms by auto
qed

lemma in_open_segment_imp_Im_in_open_segment:
  assumes "x \<in> open_segment y z" "Im y \<noteq> Im z"
  shows   "Im x \<in> open_segment (Im y) (Im z)"
proof -
  from assms obtain t where t: "t \<in> {0<..<1}" "x = linepath y z t"
    by (metis greaterThanLessThan_iff in_segment(2) linepath_def)
  have "Im x = linepath (Im y) (Im z) t"
    by (simp_all add: t Im_linepath')
  with t(1) show ?thesis
    using linepath_in_open_segment[of t "Im y" "Im z"] assms by auto
qed

(* TODO: Move to Eulerian_Poly *)
lemma poly_eulerian_poly_0 [simp]: "poly (eulerian_poly n) 0 = 1"
  by (induction n) (auto simp: eulerian_poly.simps(2) Let_def)

(* TODO: Move to Eulerian_Poly *)
lemma eulerian_poly_at_1 [simp]: "poly (eulerian_poly n) 1 = fact n"
  by (induction n) (auto simp: eulerian_poly.simps(2) Let_def algebra_simps)


subsection \<open>The slotted complex plane\<close>

(* TODO: Move? *)

lemma closed_slot_left: "closed (complex_of_real ` {..c})"
  by (intro closed_injective_linear_image) (auto simp: inj_def)

lemma closed_slot_right: "closed (complex_of_real ` {c..})"
  by (intro closed_injective_linear_image) (auto simp: inj_def)

lemma complex_slot_left_eq: "complex_of_real ` {..c} = {z. Re z \<le> c \<and> Im z = 0}"
  by (auto simp: image_iff complex_eq_iff)

lemma complex_slot_right_eq: "complex_of_real ` {c..} = {z. Re z \<ge> c \<and> Im z = 0}"
  by (auto simp: image_iff complex_eq_iff)

lemma complex_double_slot_eq:
  "complex_of_real ` ({..c1} \<union> {c2..}) = {z. Im z = 0 \<and> (Re z \<le> c1 \<or> Re z \<ge> c2)}"
  by (auto simp: image_iff complex_eq_iff)

lemma starlike_slotted_complex_plane_left_aux:
  assumes z: "z \<in> -(complex_of_real ` {..c})" and c: "c < c'"
  shows   "closed_segment (complex_of_real c') z \<subseteq> -(complex_of_real ` {..c})"
proof -
  show "closed_segment c' z \<subseteq> -of_real ` {..c}"
  proof (cases "Im z = 0")
    case True
    thus ?thesis using z c
      by (auto simp: closed_segment_same_Im closed_segment_eq_real_ivl complex_slot_left_eq)
  next
    case False
    show ?thesis
    proof
      fix x assume x: "x \<in> closed_segment (of_real c') z"
      consider "x = of_real c'" | "x = z" | "x \<in> open_segment (of_real c') z"
        unfolding open_segment_def using x by blast
      thus "x \<in> -complex_of_real ` {..c}"
      proof cases
        assume "x \<in> open_segment (of_real c') z"
        hence "Im x \<in> open_segment (Im (complex_of_real c')) (Im z)"
          by (intro in_open_segment_imp_Im_in_open_segment) (use False in auto)
        hence "Im x \<noteq> 0"
          by (auto simp: open_segment_eq_real_ivl split: if_splits)
        thus ?thesis
          by (auto simp: complex_slot_right_eq)
      qed (use z c in \<open>auto simp: complex_slot_left_eq\<close>)
    qed
  qed
qed

lemma starlike_slotted_complex_plane_left: "starlike (-(complex_of_real ` {..c}))"
  unfolding starlike_def
proof (rule bexI[of _ "of_real c + 1"]; (intro ballI)?)
  show "complex_of_real c + 1 \<in> -complex_of_real ` {..c}"
    by (auto simp: complex_eq_iff)
  show "closed_segment (complex_of_real c + 1) z \<subseteq> - complex_of_real ` {..c}"
    if "z \<in> - complex_of_real ` {..c}" for z
    using starlike_slotted_complex_plane_left_aux[OF that, of "c + 1"] by simp
qed


lemma starlike_slotted_complex_plane_right_aux:
  assumes z: "z \<in> -(complex_of_real ` {c..})" and c: "c > c'"
  shows   "closed_segment (complex_of_real c') z \<subseteq> -(complex_of_real ` {c..})"
proof -
  show "closed_segment c' z \<subseteq> -of_real ` {c..}"
  proof (cases "Im z = 0")
    case True
    thus ?thesis using z c
      by (auto simp: closed_segment_same_Im closed_segment_eq_real_ivl complex_slot_right_eq)
  next
    case False
    show ?thesis
    proof
      fix x assume x: "x \<in> closed_segment (of_real c') z"
      consider "x = of_real c'" | "x = z" | "x \<in> open_segment (of_real c') z"
        unfolding open_segment_def using x by blast
      thus "x \<in> -complex_of_real ` {c..}"
      proof cases
        assume "x \<in> open_segment (of_real c') z"
        hence "Im x \<in> open_segment (Im (complex_of_real c')) (Im z)"
          by (intro in_open_segment_imp_Im_in_open_segment) (use False in auto)
        hence "Im x \<noteq> 0"
          by (auto simp: open_segment_eq_real_ivl split: if_splits)
        thus ?thesis
          by (auto simp: complex_slot_right_eq)
      qed (use z c in \<open>auto simp: complex_slot_right_eq\<close>)
    qed
  qed
qed

lemma starlike_slotted_complex_plane_right: "starlike (-(complex_of_real ` {c..}))"
  unfolding starlike_def
proof (rule bexI[of _ "of_real c - 1"]; (intro ballI)?)
  show "complex_of_real c - 1 \<in> -complex_of_real ` {c..}"
    by (auto simp: complex_eq_iff)
  show "closed_segment (complex_of_real c - 1) z \<subseteq> - complex_of_real ` {c..}"
    if "z \<in> - complex_of_real ` {c..}" for z
    using starlike_slotted_complex_plane_right_aux[OF that, of "c - 1"] by simp
qed


lemma starlike_doubly_slotted_complex_plane_aux:
  assumes z: "z \<in> -(complex_of_real ` ({..c1} \<union> {c2..}))" and c: "c1 < c" "c < c2"
  shows   "closed_segment (complex_of_real c) z \<subseteq> -(complex_of_real ` ({..c1} \<union> {c2..}))"
proof -
  show "closed_segment c z \<subseteq> -of_real ` ({..c1} \<union> {c2..})"
  proof (cases "Im z = 0")
    case True
    thus ?thesis using z c
      by (auto simp: closed_segment_same_Im closed_segment_eq_real_ivl complex_double_slot_eq)
  next
    case False
    show ?thesis
    proof
      fix x assume x: "x \<in> closed_segment (of_real c) z"
      consider "x = of_real c" | "x = z" | "x \<in> open_segment (of_real c) z"
        unfolding open_segment_def using x by blast
      thus "x \<in> -complex_of_real ` ({..c1} \<union> {c2..})"
      proof cases
        assume "x \<in> open_segment (of_real c) z"
        hence "Im x \<in> open_segment (Im (complex_of_real c)) (Im z)"
          by (intro in_open_segment_imp_Im_in_open_segment) (use False in auto)
        hence "Im x \<noteq> 0"
          by (auto simp: open_segment_eq_real_ivl split: if_splits)
        thus ?thesis
          by (auto simp: complex_slot_right_eq)
      qed (use z c in \<open>auto simp: complex_slot_right_eq\<close>)
    qed
  qed
qed

lemma starlike_doubly_slotted_complex_plane:
  assumes "c1 < c2"
  shows   "starlike (-(complex_of_real ` ({..c1} \<union> {c2..})))"
proof -
  from assms obtain c where c: "c1 < c" "c < c2"
    using dense by blast
  show ?thesis
    unfolding starlike_def
  proof (rule bexI[of _ "of_real c"]; (intro ballI)?)
    show "complex_of_real c \<in> -complex_of_real ` ({..c1} \<union> {c2..})"
      using c by (auto simp: complex_eq_iff)
    show "closed_segment (complex_of_real c) z \<subseteq> - complex_of_real ` ({..c1} \<union> {c2..})"
      if "z \<in> - complex_of_real ` ({..c1} \<union> {c2..})" for z
      using starlike_doubly_slotted_complex_plane_aux[OF that, of c] c by simp
  qed
qed

lemma simply_connected_slotted_complex_plane_left:
  "simply_connected (-(complex_of_real ` {..c}))"
  by (intro starlike_imp_simply_connected starlike_slotted_complex_plane_left)

lemma simply_connected_slotted_complex_plane_right:
  "simply_connected (-(complex_of_real ` {c..}))"
  by (intro starlike_imp_simply_connected starlike_slotted_complex_plane_right)

lemma simply_connected_doubly_slotted_complex_plane:
  "c1 < c2 \<Longrightarrow> simply_connected (-(complex_of_real ` ({..c1} \<union> {c2..})))"
  by (intro starlike_imp_simply_connected starlike_doubly_slotted_complex_plane)

end