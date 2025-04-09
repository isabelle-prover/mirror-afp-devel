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
