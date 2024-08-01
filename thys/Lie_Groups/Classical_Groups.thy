(*  Title:       Classical_Groups
    Author:      Richard Schmoetten <richard.schmoetten@ed.ac.uk>, 2024
    Maintainer:  Richard Schmoetten <richard.schmoetten@ed.ac.uk>
*)

theory Classical_Groups

imports
Lie_Group
Linear_Algebra_More

begin

section \<open>Matrix Groups\<close>

subsection \<open>Entry Type\<close>

text \<open>
  What would be a good type for the entries of our matrices? Ideally, I would be able to talk about
  matrices over reals $\mathbb{R}$, the complex numbers $\mathbb{C}$, and the quaternionic
  skew-field $\mathbb{H}$. This is hard: only algebras and inner product spaces over $\mathbb{R}$
  are well-supported in Isabelle's Main.

  For now, for simplicity, I will work with real matrices only. Alternatively, one could try to
  characterise the type class containing $\mathbb{R}$, $\mathbb{C}$, and $\mathbb{H}$ only.
  Below is a first attempt to maintain at least some generality. I give some trivial type
  instantiations, as a basic check.

  However, locales are the way to go, in my opinion.
\<close>

class real_normed_eucl = real_normed_field + euclidean_space

(* basic properties *)
instance real_normed_eucl \<subseteq> euclidean_space by standard
instance real_normed_eucl \<subseteq> real_normed_field by standard
instance real_normed_eucl \<subseteq> topological_space by standard

(* more basic properties, related to general definitions of GL and other groups *)
instance real_normed_eucl \<subseteq> comm_ring by standard
instance real_normed_eucl \<subseteq> comm_ring_1 by standard
instance real_normed_eucl \<subseteq> real_algebra_1 by standard

(* properties of vectors over the base type *)
instance vec :: (real_normed_eucl, finite) topological_space by standard
instance vec :: (real_normed_eucl, finite) euclidean_space by standard

(* concrete instantiations *)
instance real :: real_normed_eucl by standard
instance complex :: real_normed_eucl by standard

  

subsection \<open>Mat(n, F)\<close>

text\<open>
  The set of all \<open>'n\<close>-vectors over a \<open>topological_space\<close> is a \<open>topological_space\<close>: this is proved in
  \<open>Finite_Cartesian_Product\<close>. Similar for vectors over a \<open>euclidean_space\<close>. Therefore, a vector of
  vectors over a topological space (i.e. a matrix) is also a topological space.
  We can thus define the identity as a chart; this is not superbly useful, but serves as a template
  for charts for the multiplicative matrix groups later on.
\<close>
lift_definition chart_mat::"(('a::real_normed_eucl,'n::finite)square_matrix, ('a,'n)square_matrix)chart"
  is "(UNIV, UNIV, \<lambda>m. m, \<lambda>m. m)"
  by (auto simp: homeomorphism_def)


subsection \<open>GL(n, F)\<close>

text \<open>
  We define polymorphic abbreviations for the carrier set of the general linear group as a
  matrix group over a commutative ring. This group can be considered as the automorphism group
  on arbitrary modules of non-commutative rings too, but one loses the isomorphism with matrices,
  and I'm mostly interested in much more specific general linear groups anyway (namely, over real
  and complex numbers). Using commutative rings (with 1) also means that determinants play nicely.
\<close>
abbreviation in_GL::"('a::comm_ring_1,'n::finite)square_matrix \<Rightarrow> bool"
  where "in_GL \<equiv> invertible"
abbreviation GL where "GL \<equiv> Collect in_GL"

text \<open>
  As an example for making the polymorphic \<open>GL\<close> concrete, we specify the general linear group
  in four real/complex dimensions.\<close>
abbreviation GL\<^sub>R\<^sub>4::"(real,4)square_matrix set" where "GL\<^sub>R\<^sub>4 \<equiv> GL"
abbreviation GL\<^sub>C\<^sub>4::"(complex,4)square_matrix set" where "GL\<^sub>C\<^sub>4 \<equiv> GL"

text \<open>
  PROBLEM: the inner product on the LHS is real, not complex,
  which is why the commented line (involving complex multiplication) cannot work
  (it only passes type checking because \<open>complex_of_real\<close> is a coercion).
\<close>
lemma
  assumes "x\<in>GL\<^sub>C\<^sub>4"
  (*shows "(row i x) \<bullet> (row i x) = (\<Sum>j\<in>UNIV. (row i x)$j * (row i x)$j)"*)
  shows "((row i x \<bullet> row i x)::real) = (\<Sum>j\<in>UNIV. (row i x)$j \<bullet> (row i x)$j)"
  by (simp add: inner_vec_def)

text \<open>
  We now define the chart that makes GL(n,F) a Lie group. Since a chart is a homeomorphism,
  we first need to show that GL is an open set. Notice this GL is already restricted to
  have much more powerful entries, since we require topology (continuity) now.
\<close>
lemma GL_preimage_det: "det -` (UNIV - {0::'a::real_normed_eucl}) = GL"
proof (safe)
  fix x::"('a::real_normed_eucl, 'n::finite) square_matrix"
  assume "in_GL x"
  then show "x \<in> det -` (UNIV - {0})"
      using invertible_det_nz by auto
next
  fix x::"('a::real_normed_eucl, 'n::finite) square_matrix"
  assume "det x \<noteq> 0"
  then show "in_GL x"
    by (simp add: invertible_det_nz)
qed

lemma open_GL: "open (GL::('a::real_normed_eucl,'n::finite)square_matrix set)"
  using open_vimage continuous_on_det GL_preimage_det
  by (metis open_UNIV open_delete)

lift_definition chart_GL::"(('a::real_normed_eucl,'n::finite)square_matrix, ('a,'n)square_matrix)chart"
  is "(GL, GL, \<lambda>m. m, \<lambda>m. m)"
  by (auto simp: homeomorphism_def open_GL)
lift_definition real_chart_GL::"((real,'n::finite)square_matrix, (real,'n)square_matrix)chart"
  is "(GL, GL, \<lambda>m. m, \<lambda>m. m)"
  by (auto simp: homeomorphism_def open_GL)

lemma transfer_GL [simp]:
  shows "domain chart_GL = GL"
    and "codomain chart_GL = GL"
    and "apply_chart chart_GL = (\<lambda>x. x)"
    and "inv_chart chart_GL = (\<lambda>x. x)"
  by (transfer, simp)+

abbreviation charts_GL where "charts_GL \<equiv> {chart_GL}"
abbreviation real_charts_GL where "real_charts_GL \<equiv> {real_chart_GL}"


interpretation manifold_GL: c_manifold "charts_GL" k
  using smooth_compat_refl by (unfold_locales, simp)

(* try removing the type annotation below *)
abbreviation prod_chart_GL :: "(('a::real_normed_eucl, 'b::finite)square_matrix \<times> ('a, 'b)square_matrix, ('a, 'b)square_matrix \<times> ('a, 'b)square_matrix) chart"
  where "prod_chart_GL \<equiv> c_manifold_prod.prod_chart chart_GL chart_GL"
abbreviation prod_charts_GL :: "(('a::real_normed_eucl, 'b::finite)square_matrix \<times> ('a, 'b)square_matrix, ('a, 'b)square_matrix \<times> ('a, 'b)square_matrix) chart set"
  where "prod_charts_GL \<equiv> c_manifold_prod.prod_charts charts_GL charts_GL"

interpretation prod_manifold_GL: c_manifold_prod k (*"charts_GL" "charts_GL"*)
    "charts_GL::(('a::real_normed_eucl,'n::finite)square_matrix, ('a,'n)square_matrix)chart set"
    "charts_GL::(('a::real_normed_eucl,'n::finite)square_matrix, ('a,'n)square_matrix)chart set"
  unfolding c_manifold_prod_def apply (simp add: manifold_GL.c_manifold_axioms) done

abbreviation "prod_GL_carrier \<equiv> manifold.carrier prod_manifold_GL.prod_charts"
abbreviation "prod_GL_atlas \<equiv> c_manifold.atlas prod_manifold_GL.prod_charts \<infinity>"

lemma transfer_prod_GL [simp]:
  shows "domain prod_chart_GL = GL\<times>GL"
    and "codomain prod_chart_GL =  GL\<times>GL"
    and "apply_chart prod_chart_GL = (\<lambda>x. x)"
    and "inv_chart prod_chart_GL = (\<lambda>x. x)"
  using c_manifold_prod.domain_prod_chart c_manifold_prod.codomain_prod_chart
    c_manifold_prod.apply_prod_chart c_manifold_prod.inv_chart_prod_chart transfer_GL
  by auto

lemma manifold_GL_carrier [simp]: "manifold_GL.carrier = GL"
  by (simp add: manifold_GL.carrier_def)

lemma prod_manifold_GL_carrier [simp]: "prod_GL_carrier = GL\<times>GL"
  using prod_manifold_GL.prod_carrier by auto

text \<open>
  The following lemma basically just does unfolding and type checking.
  Possibly useful once general results for \<open>charts_GL\<close> need to be specified down to \<open>real_charts_GL\<close>.
\<close>
lemma real_GL_is_a_GL:
  shows "real_chart_GL = chart_GL"
    and "real_charts_GL = charts_GL"
    and "manifold.carrier (c_manifold_prod.prod_charts real_charts_GL real_charts_GL) = prod_GL_carrier"
  unfolding chart_GL_def real_chart_GL_def by simp+


lemma mult_closed_on_GL:
  fixes f_mult :: "('a,'b)square_matrix \<times> ('a,'b)square_matrix
      \<Rightarrow> ('a::comm_ring_1, 'b::finite) square_matrix"
  defines f_mult: "f_mult \<equiv> (\<lambda>(x, y). x ** y)"
  shows "f_mult ` (GL\<times>GL) \<subseteq> GL"
proof
  fix x
  assume "x \<in> f_mult ` (GL \<times> GL)"
  then obtain y z::"('a,'b)square_matrix" where "x = y**z" "invertible y" "invertible z"
    using f_mult by auto
  then show "x\<in>GL"
    by (simp add: invertible_mult)
qed

lemma GL_group_mult_right_div:
  shows "group_on_with (domain chart_GL) (**) (mat 1) (\<lambda>m\<^sub>1 m\<^sub>2. m\<^sub>1 ** matrix_inv m\<^sub>2) matrix_inv"
  apply unfold_locales
  apply (simp_all add: matrix_mul_assoc invertible_mult invertible_mat_1 invertible_matrix_inv)
  by (simp add: matrix_inv_def invertible_right_inverse matrix_left_right_inverse verit_sko_ex_indirect)


lemma smooth_on_proj: "smooth_on prod_GL_carrier fst" "smooth_on prod_GL_carrier snd"
  using smooth_on_fst [OF smooth_on_id manifold.open_carrier] apply blast
  using smooth_on_snd [OF smooth_on_id manifold.open_carrier] by blast


lemma mult_smooth_on_real_GL:
  fixes f_mult :: "(real,'n)square_matrix \<times> (real,'n)square_matrix \<Rightarrow> (real,'n::finite)square_matrix"
  defines f_mult: "f_mult \<equiv> (\<lambda>(x, y). x ** y)"
  shows "smooth_on (GL\<times>GL) f_mult"
proof (unfold f_mult, simp add: case_prod_beta', intro smooth_on_matrix_mult)
  \<comment> \<open>Isabelle doesn't seem to infer types for \<^term>\<open>GL\<close> and \<^term>\<open>prod_GL_carrier\<close> below,
    even though they should be clear from being accepted in ``show'' statements
    (i.e. they should be inferred from having to match the types in the lemma's goal).\<close>
  let ?GL = "GL::(real,'n)square_matrix set"
  show "smooth_on (?GL \<times> ?GL) fst"
    using smooth_on_proj(1) by simp
  show "smooth_on (?GL \<times> ?GL) snd"
    using smooth_on_proj(2) by simp
  show "open (?GL \<times> ?GL)"
    using manifold.open_carrier[of prod_charts_GL] prod_manifold_GL_carrier by simp
qed


lemma mult_smooth_on_GL_expanded:
  assumes "x \<in> prod_GL_carrier"
  shows "x \<in> domain prod_chart_GL"
    and "(\<lambda>(x, y). x ** y) ` domain prod_chart_GL \<subseteq> domain chart_GL"
    and "smooth_on (codomain prod_chart_GL) (apply_chart chart_GL \<circ> (\<lambda>(x, y). x ** y) \<circ> inv_chart prod_chart_GL)"
  using assms apply fastforce
  apply (simp add: mult_closed_on_GL)
  apply (simp add: fun.map_ident)
  using mult_smooth_on_real_GL \<comment> \<open>only for real entries\<close>
oops


lemma mult_smooth_on_real_GL_expanded:
  fixes f_mult :: "(real,'n)square_matrix \<times> (real,'n)square_matrix \<Rightarrow> (real,'n::finite)square_matrix"
    and x :: "(real,'n)square_matrix\<times>(real,'n)square_matrix"
  defines f_mult: "f_mult \<equiv> (\<lambda>(x, y). x ** y)"
  assumes "x \<in> prod_GL_carrier"
  shows "x \<in> domain prod_chart_GL"
    and "f_mult ` domain prod_chart_GL \<subseteq> domain chart_GL"
    and "smooth_on (codomain prod_chart_GL) (apply_chart chart_GL \<circ> f_mult \<circ> inv_chart prod_chart_GL)"
proof -
  show "x \<in> domain prod_chart_GL"
    using assms by fastforce
  show "f_mult ` domain prod_chart_GL \<subseteq> domain chart_GL"
    by (simp add: f_mult mult_closed_on_GL)
  show "smooth_on (codomain prod_chart_GL) (apply_chart chart_GL \<circ> f_mult \<circ> inv_chart prod_chart_GL)"
    apply (simp add: fun.map_ident)
    by (simp add: f_mult mult_smooth_on_real_GL)
qed


theorem real_GL_Lie_group: "lie_group real_charts_GL (**) (mat 1) (\<lambda>m\<^sub>1 m\<^sub>2. m\<^sub>1 ** (matrix_inv m\<^sub>2)) matrix_inv"
proof (intro group_manifold_imp_lie_group2)
  let ?div = "\<lambda>m\<^sub>1 m\<^sub>2. m\<^sub>1 ** matrix_inv m\<^sub>2"
  let ?prod = "c_manifold_prod.prod_charts real_charts_GL real_charts_GL"
  show "c_manifold real_charts_GL \<infinity>"
    by (simp add: manifold_GL.c_manifold_axioms real_GL_is_a_GL(2))
  show "group_on_with (\<Union> (domain ` real_charts_GL)) (**) (mat 1) ?div matrix_inv"
    using GL_group_mult_right_div real_GL_is_a_GL(2)
    by (metis (mono_tags, lifting) manifold.carrier_def manifold_GL_carrier transfer_GL(1))
  show "diff_axioms \<infinity> ?prod real_charts_GL (\<lambda>(a, b). a ** b)"
  proof (unfold_diff_axioms; unfold real_GL_is_a_GL(1,2) prod_manifold_GL_carrier)
    fix x :: "((real, 'b) vec, 'b) vec \<times> ((real, 'b) vec, 'b) vec"
    assume x_in: "x \<in> GL \<times> GL"
    show "x \<in> domain prod_chart_GL"
      using x_in by simp
    show "real_chart_GL \<in> manifold_GL.atlas \<infinity>"
      by (simp add: manifold_GL.in_charts_in_atlas real_GL_is_a_GL(1))
    show "prod_chart_GL \<in> prod_GL_atlas"
      by (simp add: prod_manifold_GL.prod_chart_in_atlas)
    show mult_maps_domain: "(\<lambda>(x, y). x ** y) ` domain prod_chart_GL \<subseteq> domain real_chart_GL"
      using x_in mult_smooth_on_real_GL_expanded(2)
      by (simp add: mult_closed_on_GL real_GL_is_a_GL(1))
    show "smooth_on (codomain prod_chart_GL) (
        apply_chart real_chart_GL \<circ> (\<lambda>(x, y). x ** y) \<circ> inv_chart prod_chart_GL)"
      using mult_smooth_on_real_GL_expanded(3) x_in real_GL_is_a_GL(1)
      by (metis prod_manifold_GL_carrier smooth_on_open_subsetsI transfer_prod_GL(2))
  qed
  show "diff_axioms \<infinity> real_charts_GL real_charts_GL matrix_inv"
  proof (unfold_diff_axioms; unfold real_GL_is_a_GL(1,2) manifold_GL_carrier)
    fix x :: "((real, 'b) vec, 'b) vec"
    assume x_in: "x \<in> GL"
\<comment> \<open>Cheeky: "cast up" the real matrix x to be in the domain of \<open>chart_GL\<close>,
  rather than \<open>real_chart_GL\<close>. This makes proofs easier for sledgehammer wherever they involve
  lemmas about GL in general.\<close>
    show "x \<in> domain real_chart_GL"
      using x_in by (simp add: real_GL_is_a_GL(1))
    show "chart_GL \<in> manifold_GL.atlas \<infinity>"
      by (simp add: manifold_GL.in_charts_in_atlas)
    show "real_chart_GL \<in> manifold_GL.atlas \<infinity>"
      by (simp add: manifold_GL.in_charts_in_atlas real_GL_is_a_GL(1))
    show mult_maps_domain: "matrix_inv ` domain real_chart_GL \<subseteq> domain chart_GL"
      by (simp add: image_subset_iff invertible_matrix_inv real_GL_is_a_GL(1))
    have 1: "(\<lambda>x. x) \<circ> matrix_inv \<circ> (\<lambda>x. x) = matrix_inv"
      by auto
    show "smooth_on (codomain real_chart_GL) (apply_chart chart_GL \<circ> matrix_inv \<circ> inv_chart real_chart_GL)"
      using smooth_on_matrix_inv[OF _ open_GL] by (simp add: real_GL_is_a_GL(1) 1)
  qed
qed


corollary real_GL_Lie_grp: "lie_grp real_charts_GL (**) (mat 1)"
  using lie_group_imp_lie_grp[OF real_GL_Lie_group] .

end