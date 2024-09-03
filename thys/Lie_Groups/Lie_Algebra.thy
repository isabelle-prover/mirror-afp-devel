(*  Title:       Lie_Algebra
    Author:      Richard Schmoetten <richard.schmoetten@ed.ac.uk>, 2024
    Maintainer:  Richard Schmoetten <richard.schmoetten@ed.ac.uk>
*)

section \<open>The Lie algebra of a Lie Group\<close>
theory Lie_Algebra
  imports
    Lie_Group
    Manifold_Lie_Bracket
    Smooth_Manifolds.Cotangent_Space
begin


sublocale lie_group \<subseteq> smooth_manifold by unfold_locales

locale lie_algebra_morphism = 
  src: lie_algebra S1 scale1 bracket1 +
  dest: lie_algebra S2 scale2 bracket2 +
  linear_on S1 S2 scale1 scale2 f
  for S1 S2
    and scale1::"'a::field \<Rightarrow> 'b \<Rightarrow> 'b::ab_group_add" and scale2::"'a::field \<Rightarrow> 'c \<Rightarrow> 'c::ab_group_add"
    and bracket1 and bracket2
    and f +
  assumes bracket_hom: "\<And>X Y. X \<in> S1 \<Longrightarrow> Y \<in> S1 \<Longrightarrow> f (bracket1 X Y) = bracket2 (f X) (f Y)"


text \<open>Multiple isomorphic Lie algebras can be referred to as ``the'' Lie algebra $\mathfrak g$
    of a given Lie group $G$. One Lie algebra is already guaranteed to exist for any Lie group
    by virtue of @{thm smooth_manifold.lie_algebra_of_smooth_vector_fields}. We give an isomorphism
    between the subalgebra of \emph{left-invariant} (smooth) vector fields and the tangent space
    at identity, and take the latter to be ``the'' Lie algebra $\mathfrak g$.\<close>

context lie_group begin

text \<open>Some notation, for simplicity: the Lie group (or here, its carrier) is $G$, and the tangent
  space at the identity (the Lie algebra) is $\mathfrak g$.\<close>
notation carrier (\<open>G\<close>)
definition tangent_space_at_identity (\<open>\<gg>\<close>)
  where "tangent_space_at_identity = tangent_space tms_one"

subsection \<open>(Left-)invariant vector fields\<close>
text \<open>A vector field $X$ is invariant under some $k$-smooth map $F$ if the vector assigned to a
    point $F(p)$ by $X$ is the same as the vector assigned by (the push-forward under) $F$ to the
    vector $X(p)$. Essentially, $F$ and $X$ ``commute''.\<close>

definition (in c_manifold) vector_field_invariant_under :: "'a vector_field \<Rightarrow> ('a\<Rightarrow>'a) \<Rightarrow> bool"
    (infix \<open>invariant'_under\<close> 80)
  where "X invariant_under F \<equiv> \<forall>p\<in>carrier. \<forall>f\<in>diff_fun_space.
                                X (F p) f = (diff.push_forward k charts charts F) (X p) f"

\<comment> \<open>TODO this could be in an instance of \<^locale>\<open>diff\<close> going from a manifold to itself,
    rather than \<^locale>\<open>diffeomorphism\<close>, i.e. an endomorphism rather than an automorphism.\<close>
definition (in c_automorphism) invariant :: "'a vector_field \<Rightarrow> bool"
  where "invariant X \<equiv> \<forall>p\<in>carrier. \<forall>g\<in>src.diff_fun_space. X (f p) g = push_forward (X p) g"

lemma (in c_automorphism) invariant_simp: "src.vector_field_invariant_under X f  = invariant X"
  unfolding src.vector_field_invariant_under_def invariant_def by simp

lemma (in c_manifold) vector_field_invariant_underD: "X (F p) f = X p (restrict0 carrier (f \<circ> F))"
  if "X invariant_under F" "diff k charts charts F" "p\<in>carrier" "f\<in>diff_fun_space"
  using that by (auto simp: vector_field_invariant_under_def diff.push_forward_def)

lemma (in c_manifold) vector_field_invariant_underI: "X invariant_under F"
  if "diff k charts charts F" "\<And>p f. p\<in>carrier \<Longrightarrow> f\<in>diff_fun_space \<Longrightarrow> X (F p) f = X p (restrict0 carrier (f \<circ> F))"
  by (simp add: vector_field_invariant_under_def diff.push_forward_def that)

\<comment> \<open>Repeat notation from @{thm c_manifold.vector_field_invariant_under_def}.\<close>
notation vector_field_invariant_under (infix \<open>invariant'_under\<close> 80)
abbreviation "L_invariant X \<equiv> \<forall>p\<in>carrier. X invariant_under (\<L> p)"

lemma L_invariantD [dest]: "X (tms p q) f = X q (restrict0 G (f \<circ> (\<L> p)))"
  if "L_invariant X" "p\<in>G" "q\<in>G" "f\<in>diff_fun_space"
  using vector_field_invariant_underD diff_tms(1) that by auto

lemma L_invariantI [intro]: "L_invariant X"
  if "\<And>p q f. p\<in>carrier \<Longrightarrow> q\<in>carrier \<Longrightarrow> f\<in>diff_fun_space \<Longrightarrow> X (tms p q) f = X q (restrict0 carrier (f \<circ> (\<L> p)))"
  using that vector_field_invariant_underI diff_tms(1) by auto

lemma lie_bracket_left_invariant:
  assumes "L_invariant X" "smooth_vector_field X"
    and "L_invariant Y"  "smooth_vector_field Y"
  shows "L_invariant [X;Y]" "smooth_vector_field [X;Y]"
proof
  fix p assume p: "p\<in>G"
  show "vector_field_invariant_under [X;Y] (\<L> p)"
  proof (intro vector_field_invariant_underI)
    fix q f
    assume q: "q\<in>G" and f: "f\<in>diff_fun_space"
    have 1: "restrict0 G ((Z \<hungarumlaut> f) \<circ> \<L> p) = Z \<hungarumlaut> (restrict0 G (f \<circ> \<L> p))"
      if Z: "L_invariant Z" "extensional0 carrier Z" for Z
    proof
      fix t show "restrict0 G ((Z \<hungarumlaut> f) \<circ> tms p) t = Z t (restrict0 G (f \<circ> tms p))"
        apply (cases "t\<in>G")
        subgoal
          using f p Z vector_field_invariant_underD[OF _ _ q smooth_vf_diff_fun_space]
          by (auto)
        using Z by (simp add: extensional0_outside)
    qed
    show "[X;Y] (tms p q) f = [X;Y] q (restrict0 G (f \<circ> tms p))"
      unfolding lie_bracket_def
      using assms diff_tms(1) assms
      by (auto simp: 1 p f vector_field_invariant_underD[OF _ _ q smooth_vf_diff_fun_space] smooth_vector_fieldE(2))
  qed (simp add: p diff_tms(1))
qed (simp_all add: assms(2,4) lie_bracket_closed)


text \<open>In fact, left-invariant smooth vector fields form a Lie subalgebra.\<close>
lemma subspace_of_left_invariant_svf:
  fixes \<XX>\<^sub>\<L> defines "\<XX>\<^sub>\<L> \<equiv> {X \<in> SVF. L_invariant X}"
  shows "subspace \<XX>\<^sub>\<L>"
proof (unfold subspace_def, safe)
  interpret SVF: lie_algebra SVF scaleR lie_bracket_of_smooth_vector_fields
    using lie_algebra_of_smooth_vector_fields by simp

  have "L_invariant 0"
    apply (intro ballI vector_field_invariant_underI) by (simp_all add: diff_tms(1))
  thus "0 \<in> \<XX>\<^sub>\<L>" unfolding assms(1) using SVF.m1.mem_zero by blast

  fix c and x
  assume x: "x \<in> \<XX>\<^sub>\<L>"
  then have "L_invariant (c *\<^sub>R x)"
    apply (intro ballI vector_field_invariant_underI) using assms by (auto simp add: diff_tms(1))
  thus "c *\<^sub>R x \<in> \<XX>\<^sub>\<L>" unfolding assms(1) using SVF.m1.mem_scale x assms by blast

  fix y
  assume y: "y \<in> \<XX>\<^sub>\<L>"
  then have "L_invariant (x + y)"
    apply (intro ballI vector_field_invariant_underI) using assms vector_field_invariant_underD x by (auto simp: diff_tms(1))
  thus "x + y \<in> \<XX>\<^sub>\<L>" unfolding assms(1) using SVF.m1.mem_add assms x y by blast
qed


lemma lie_algebra_of_left_invariant_svf:
  fixes \<XX>\<^sub>\<L> defines "\<XX>\<^sub>\<L> \<equiv> {X. smooth_vector_field X \<and> L_invariant X}"
  shows "lie_algebra \<XX>\<^sub>\<L> (*\<^sub>R) (\<lambda>X Y. [X;Y])"
proof -
  interpret SVF: lie_algebra SVF scaleR lie_bracket_of_smooth_vector_fields
    using lie_algebra_of_smooth_vector_fields by simp
  show ?thesis
    using assms subspace_of_left_invariant_svf by (auto intro: SVF.lie_subalgebra
        simp: SVF.m1.implicit_subspace_with subspace_with lie_bracket_left_invariant SVF_def)
qed

end

end