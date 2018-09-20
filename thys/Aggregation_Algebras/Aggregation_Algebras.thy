(* Title:      Algebras for Aggregation and Minimisation
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section {* Algebras for Aggregation and Minimisation *}

text {*
This theory gives algebras with operations for aggregation and minimisation.
In the weighted-graph model of matrices over (extended) numbers, the operations have the following meaning.
The binary operation $+$ adds the weights of corresponding edges of two graphs.
Addition does not have to be the standard addition on numbers, but can be any aggregation satisfying certain basic properties as demonstrated by various models of the algebras in another theory.
The unary operation @{text sum} adds the weights of all edges of a graph.
The result is a single aggregated weight using the same aggregation as $+$ but applied internally to the edges of a single graph.
The unary operation @{text minarc} finds an edge with a minimal weight in a graph.
It yields the position of such an edge as a regular element of a Stone relation algebra.

We give axioms for these operations which are sufficient to prove the correctness of Prim's and Kruskal's minimum spanning tree algorithms.
The operations have been proposed and axiomatised first in \cite{Guttmann2016c} with simplified axioms given in \cite{Guttmann2018a}.
The present version adds two axioms to prove total correctness of the spanning tree algorithms as discussed in \cite{Guttmann2018b}.
*}

theory Aggregation_Algebras

imports Stone_Kleene_Relation_Algebras.Kleene_Relation_Algebras

begin

context sup
begin

no_notation
  sup (infixl "+" 65)

end

context plus
begin

notation
  plus (infixl "+" 65)

end

text {*
We first introduce s-algebras as a class with the operations $+$ and @{text sum}.
Axiom @{text sum_plus_right_isotone} states that for non-empty graphs, the operation $+$ is $\leq$-isotone in its second argument on the image of the aggregation operation @{text sum}.
Axiom @{text sum_bot} expresses that the empty graph contributes no weight.
Axiom @{text sum_plus} generalises the inclusion-exclusion principle to sets of weights.
Axiom @{text sum_conv} specifies that reversing edge directions does not change the aggregated weight.
In instances of @{text s_algebra}, aggregated weights can be partially ordered.
*}

class sum =
  fixes sum :: "'a \<Rightarrow> 'a"

class s_algebra = stone_relation_algebra + plus + sum +
  assumes sum_plus_right_isotone: "x \<noteq> bot \<and> sum x \<le> sum y \<longrightarrow> sum z + sum x \<le> sum z + sum y"
  assumes sum_bot: "sum x + sum bot = sum x"
  assumes sum_plus: "sum x + sum y = sum (x \<squnion> y) + sum (x \<sqinter> y)"
  assumes sum_conv: "sum (x\<^sup>T) = sum x"
begin

lemma sum_disjoint:
  assumes "x \<sqinter> y = bot"
    shows "sum ((x \<squnion> y) \<sqinter> z) = sum (x \<sqinter> z) + sum (y \<sqinter> z)"
  by (subst sum_plus) (metis assms inf.sup_monoid.add_assoc inf.sup_monoid.add_commute inf_bot_left inf_sup_distrib2 sum_bot)

lemma sum_disjoint_3:
  assumes "w \<sqinter> x = bot"
      and "w \<sqinter> y = bot"
      and "x \<sqinter> y = bot"
    shows "sum ((w \<squnion> x \<squnion> y) \<sqinter> z) = sum (w \<sqinter> z) + sum (x \<sqinter> z) + sum (y \<sqinter> z)"
  by (metis assms inf_sup_distrib2 sup_idem sum_disjoint)

lemma sum_symmetric:
  assumes "y = y\<^sup>T"
    shows "sum (x\<^sup>T \<sqinter> y) = sum (x \<sqinter> y)"
  by (metis assms sum_conv conv_dist_inf)

lemma sum_commute:
  "sum x + sum y = sum y + sum x"
  by (metis inf_commute sum_plus sup_commute)

end

text {*
We next introduce the operation @{text minarc}.
Axiom @{text minarc_below} expresses that the result of @{text minarc} is contained in the graph ignoring the weights.
Axiom @{text minarc_arc} states that the result of @{text minarc} is a single unweighted edge if the graph is not empty.
Axiom @{text minarc_min} specifies that any edge in the graph weighs at least as much as the edge at the position indicated by the result of @{text minarc}, where weights of edges between different nodes are compared by applying the operation @{text sum} to single-edge graphs.
Axiom @{text sum_linear} requires that aggregated weights are linearly ordered, which is necessary for both Prim's and Kruskal's minimum spanning tree algorithms.
Axiom @{text finite_regular} ensures that there are only finitely many unweighted graphs, and therefore only finitely many edges and nodes in a graph; again this is necessary for the minimum spanning tree algorithms we consider.
*}

class minarc =
  fixes minarc :: "'a \<Rightarrow> 'a"

class m_algebra = s_algebra + minarc +
  assumes minarc_below: "minarc x \<le> --x"
  assumes minarc_arc: "x \<noteq> bot \<longrightarrow> arc (minarc x)"
  assumes minarc_min: "arc y \<and> y \<sqinter> x \<noteq> bot \<longrightarrow> sum (minarc x \<sqinter> x) \<le> sum (y \<sqinter> x)"
  assumes sum_linear: "sum x \<le> sum y \<or> sum y \<le> sum x"
  assumes finite_regular: "finite { x . regular x }"
begin

text {*
Axioms @{text minarc_below} and @{text minarc_arc} suffice to derive the Tarski rule in Stone relation algebras.
*}

subclass stone_relation_algebra_tarski
proof unfold_locales
  fix x
  let ?a = "minarc x"
  assume 1: "regular x"
  assume "x \<noteq> bot"
  hence "arc ?a"
    by (simp add: minarc_arc)
  hence "top = top * ?a * top"
    by (simp add: comp_associative)
  also have "... \<le> top * --x * top"
    by (simp add: minarc_below mult_isotone)
  finally show "top * x * top = top"
    using 1 antisym by simp
qed

lemma minarc_bot:
  "minarc bot = bot"
  by (metis bot_unique minarc_below regular_closed_bot)

lemma minarc_bot_iff:
  "minarc x = bot \<longleftrightarrow> x = bot"
  using covector_bot_closed inf_bot_right minarc_arc vector_bot_closed minarc_bot by fastforce

lemma minarc_meet_bot:
  assumes "minarc x \<sqinter> x = bot"
    shows "minarc x = bot"
proof -
  have "minarc x \<le> -x"
    using assms pseudo_complement by auto
  thus ?thesis
    by (metis minarc_below inf_absorb1 inf_import_p inf_p)
qed

lemma minarc_meet_bot_minarc_iff:
  "minarc x \<sqinter> x = bot \<longleftrightarrow> minarc x = bot"
  using comp_inf.semiring.mult_not_zero minarc_meet_bot by blast

lemma minarc_meet_bot_iff:
  "minarc x \<sqinter> x = bot \<longleftrightarrow> x = bot"
  using inf_bot_right minarc_bot_iff minarc_meet_bot by blast

lemma minarc_regular:
  "regular (minarc x)"
proof (cases "x = bot")
  assume "x = bot"
  thus ?thesis
    by (simp add: minarc_bot)
next
  assume "x \<noteq> bot"
  thus ?thesis
    by (simp add: arc_regular minarc_arc)
qed

lemma minarc_selection:
  "selection (minarc x \<sqinter> y) y"
  using inf_assoc minarc_regular selection_closed_id by auto

lemma minarc_below_regular:
  "regular x \<Longrightarrow> minarc x \<le> x"
  by (metis minarc_below)

(*
lemma sum_bot: "sum bot = bot" nitpick [expect=genuine] oops
lemma plus_bot: "x + bot = x" nitpick [expect=genuine] oops
lemma "sum x = bot \<longrightarrow> x = bot" nitpick [expect=genuine] oops
*)

end

class m_kleene_algebra = m_algebra + stone_kleene_relation_algebra

end

