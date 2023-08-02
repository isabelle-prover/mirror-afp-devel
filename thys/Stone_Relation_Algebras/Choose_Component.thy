(* Title:      An Operation to Select Components
   Author:     Nicolas Robinson-O'Brien, Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>An Operation to Select Components\<close>

text \<open>
In this theory we axiomatise an operation to select components of a graph.
This is joint work with Nicolas Robinson-O'Brien.
\<close>

theory Choose_Component

imports
  Relation_Algebras

begin

context stone_relation_algebra
begin

text \<open>
A \<open>vector_classes\<close> corresponds to one or more equivalence classes and a \<open>unique_vector_class\<close> corresponds to a single equivalence class.
\<close>

definition vector_classes        :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where "vector_classes x v \<equiv> regular x \<and> regular v \<and> equivalence x \<and> vector v \<and> x * v \<le> v \<and> v \<noteq> bot"
definition unique_vector_class   :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where "unique_vector_class x v \<equiv> vector_classes x v \<and> v * v\<^sup>T \<le> x"

end

text \<open>
We introduce the operation \<open>choose_component\<close>.
\begin{itemize}
  \item Axiom \<open>component_in_v\<close> expresses that the result of \<open>choose_component\<close> is contained in the set of vertices, $v$, we are selecting from, ignoring the weights.
  \item Axiom \<open>component_is_vector\<close> states that the result of \<open>choose_component\<close> is a vector.
  \item Axiom \<open>component_is_regular\<close> states that the result of \<open>choose_component\<close> is regular.
  \item Axiom \<open>component_is_connected\<close> states that any two vertices from the result of \<open>choose_component\<close> are connected in $e$.
  \item Axiom \<open>component_single\<close> states that the result of \<open>choose_component\<close> is closed under being connected in $e$.
  \item Finally, axiom \<open>component_not_bot_when_v_bot_bot\<close> expresses that the operation \<open>choose_component\<close> returns a non-empty component if the input satisfies the given criteria.
\end{itemize}
\<close>

class choose_component =
  fixes choose_component :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

class choose_component_algebra = choose_component + stone_relation_algebra +
  assumes component_is_vector:              "vector (choose_component e v)"
  assumes component_is_regular:             "regular (choose_component e v)"
  assumes component_in_v:                   "choose_component e v \<le> --v"
  assumes component_is_connected:           "choose_component e v * (choose_component e v)\<^sup>T \<le> e"
  assumes component_single:                 "e * choose_component e v \<le> choose_component e v"
  assumes component_not_bot_when_v_bot_bot: "vector_classes e v \<longrightarrow> choose_component e v \<noteq> bot"
begin

lemma component_single_eq:
  assumes "equivalence x"
  shows "choose_component x v = x * choose_component x v"
proof -
  have "choose_component x v \<le> x * choose_component x v"
    by (meson component_is_connected ex231c mult_isotone order_lesseq_imp)
  thus ?thesis
    by (simp add: component_single order.antisym)
qed

end

class choose_component_algebra_tarski = choose_component_algebra + stone_relation_algebra_tarski
begin

definition "choose_component_point x \<equiv> choose_component 1 (--x)"

lemma choose_component_point_point:
  assumes "vector x"
      and "x \<noteq> bot"
    shows "point (choose_component_point x)"
proof (intro conjI)
  show 1: "vector (choose_component_point x)"
    by (simp add: choose_component_point_def component_is_vector)
  show "injective (choose_component_point x)"
    by (simp add: choose_component_point_def component_is_connected)
  have "vector_classes 1 (--x)"
    by (metis assms comp_inf.semiring.mult_zero_left coreflexive_symmetric inf.eq_refl mult_1_left pp_one regular_closed_p selection_closed_id vector_classes_def vector_complement_closed)
  hence "choose_component_point x \<noteq> bot"
    by (simp add: choose_component_point_def component_not_bot_when_v_bot_bot)
  thus "surjective (choose_component_point x)"
    using 1 choose_component_point_def component_is_regular tarski vector_mult_closed by fastforce
qed

lemma choose_component_point_decreasing:
  "choose_component_point x \<le> --x"
  by (metis choose_component_point_def component_in_v regular_closed_p)

end

end

