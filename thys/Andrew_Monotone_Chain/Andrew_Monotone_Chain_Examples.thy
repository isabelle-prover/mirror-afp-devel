(*  Title:      Andrew_Monotone_Chain_Examples.thy
    Author:     Arthur Freitas Ramos
    Author:     David Barros Hulak
    Author:     Ruy J. G. B. de Queiroz
*)

section \<open>Examples\<close>

theory Andrew_Monotone_Chain_Examples
  imports
    Andrew_Monotone_Chain
    "HOL-Analysis.Convex_Euclidean_Space"
begin

text \<open>
  The first examples use integer coordinates to exercise the polymorphic
  executable code path: the scan, sorting, and orientation tests work over any
  ordered integral domain.  The geometric convex-hull specification is then
  instantiated in the following subsection over real coordinates, where
  Isabelle's convexity library provides the ambient vector-space structure.
\<close>

abbreviation square_points :: "(int \<times> int) list"
where
  "square_points \<equiv>
    [(0, 0), (1, 0), (1, 1), (0, 1), (0, 0), (1, 1)]"

lemma square_hull:
  "andrew_hull square_points = [(0, 0), (1, 0), (1, 1), (0, 1)]"
  by eval

lemma square_lower_hull:
  "lower_hull square_points = [(0, 0), (1, 0), (1, 1)]"
  by eval

lemma square_upper_hull:
  "upper_hull square_points = [(1, 1), (0, 1), (0, 0)]"
  by eval

abbreviation collinear_points :: "(int \<times> int) list"
where
  "collinear_points \<equiv> [(2, 0), (0, 0), (1, 0), (3, 0), (1, 0)]"

lemma collinear_hull:
  "andrew_hull collinear_points = [(0, 0), (3, 0)]"
  by eval

abbreviation diamond_points :: "(int \<times> int) list"
where
  "diamond_points \<equiv>
    [(0, 0), (1, 1), (2, 0), (1, -1), (1, 0), (0, 0), (2, 0)]"

lemma diamond_hull:
  "andrew_hull diamond_points = [(0, 0), (1, -1), (2, 0), (1, 1)]"
  by eval

lemma diamond_hull_subset:
  "set (andrew_hull diamond_points) \<subseteq> set diamond_points"
  by (rule andrew_hull_subset)

lemma diamond_hull_turns_lower:
  "chain_turns (lower_hull diamond_points)"
  by (rule lower_hull_turns)

lemma diamond_hull_turns_upper:
  "chain_turns (upper_hull diamond_points)"
  by (rule upper_hull_turns)

subsection \<open>Convex-hull Examples over the Reals\<close>

definition square_real :: "(real \<times> real) list"
where
  "square_real =
    [(0, 0), (1, 0), (1, 1), (0, 1), (0, 0), (1, 1)]"

definition square_real_vertices :: "(real \<times> real) list"
where
  "square_real_vertices = [(0, 0), (1, 0), (1, 1), (0, 1)]"

lemma square_real_hull:
  "andrew_hull square_real = square_real_vertices"
  by eval

lemma square_real_correct:
  "convex_hull_correct square_real (andrew_hull square_real)"
  by (rule andrew_hull_correctness(4))

lemma square_real_irredundant:
  "convex_hull_irredundant (andrew_hull square_real)"
  by (rule andrew_hull_correctness(5))

lemma square_real_convex_hull:
  "convex hull set (andrew_hull square_real) = convex hull set square_real"
  by (rule andrew_hull_correctness(3))

definition collinear_real :: "(real \<times> real) list"
where
  "collinear_real = [(2, 0), (0, 0), (1, 0), (3, 0), (1, 0)]"

definition collinear_real_vertices :: "(real \<times> real) list"
where
  "collinear_real_vertices = [(0, 0), (3, 0)]"

lemma collinear_real_hull:
  "andrew_hull collinear_real = collinear_real_vertices"
  by eval

lemma one_zero_in_collinear_real_hull:
  "(1::real, 0) \<in> convex hull set collinear_real_vertices"
proof -
  let ?a = "(0::real, 0::real)"
  let ?b = "(3::real, 0::real)"
  have "(1::real, 0::real) \<in> closed_segment ?a ?b"
    by (simp add: in_segment scaleR_prod_def, rule exI[where x = "1 / 3"], simp)
  also have "\<dots> = convex hull {?a, ?b}"
    by (simp add: segment_convex_hull)
  also have "\<dots> = convex hull set collinear_real_vertices"
    by (simp add: collinear_real_vertices_def)
  finally show ?thesis .
qed

lemma two_zero_in_collinear_real_hull:
  "(2::real, 0) \<in> convex hull set collinear_real_vertices"
proof -
  let ?a = "(0::real, 0::real)"
  let ?b = "(3::real, 0::real)"
  have "(2::real, 0::real) \<in> closed_segment ?a ?b"
    by (simp add: in_segment scaleR_prod_def, rule exI[where x = "2 / 3"], simp)
  also have "\<dots> = convex hull {?a, ?b}"
    by (simp add: segment_convex_hull)
  also have "\<dots> = convex hull set collinear_real_vertices"
    by (simp add: collinear_real_vertices_def)
  finally show ?thesis .
qed

lemma collinear_real_correct:
  "convex_hull_correct collinear_real (andrew_hull collinear_real)"
  by (rule andrew_hull_correctness(4))

lemma collinear_real_irredundant:
  "convex_hull_irredundant (andrew_hull collinear_real)"
  by (rule andrew_hull_correctness(5))

lemma collinear_real_convex_hull:
  "convex hull set (andrew_hull collinear_real) = convex hull set collinear_real"
  by (rule andrew_hull_correctness(3))

definition diamond_real :: "(real \<times> real) list"
where
  "diamond_real =
    [(0, 0), (1, 1), (2, 0), (1, -1), (1, 0), (0, 0), (2, 0)]"

definition diamond_real_vertices :: "(real \<times> real) list"
where
  "diamond_real_vertices = [(0, 0), (1, -1), (2, 0), (1, 1)]"

lemma diamond_real_hull:
  "andrew_hull diamond_real = diamond_real_vertices"
  by eval

lemma diamond_center_in_computed_hull:
  "(1::real, 0) \<in> convex hull set diamond_real_vertices"
proof -
  let ?a = "(0::real, 0::real)"
  let ?c = "(2::real, 0::real)"
  have "(1::real, 0::real) \<in> closed_segment ?a ?c"
    by (simp add: in_segment scaleR_prod_def, rule exI[where x = "1 / 2"], simp)
  also have "\<dots> = convex hull {?a, ?c}"
    by (simp add: segment_convex_hull)
  also have "\<dots> \<subseteq> convex hull set diamond_real_vertices"
    by (rule hull_mono) (auto simp: diamond_real_vertices_def)
  finally show ?thesis .
qed

lemma diamond_real_correct:
  "convex_hull_correct diamond_real (andrew_hull diamond_real)"
  by (rule andrew_hull_correctness(4))

lemma diamond_real_irredundant:
  "convex_hull_irredundant (andrew_hull diamond_real)"
  by (rule andrew_hull_correctness(5))

lemma diamond_real_convex_hull:
  "convex hull set (andrew_hull diamond_real) = convex hull set diamond_real"
  by (rule andrew_hull_correctness(3))

value "andrew_hull square_points"
value "andrew_hull collinear_points"
value "andrew_hull diamond_points"

end
