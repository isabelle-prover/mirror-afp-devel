(*  Title:       Paradoxical_Decomposition.thy
    Author:      Arthur F. Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026

    The abstract notion of a paradoxical decomposition of a set under a
    group action. This is the bridge between the algebraic content
    (the free group F_2 has a paradoxical decomposition) and the
    geometric content (the unit ball in R^3 has one as well).
*)

theory Paradoxical_Decomposition
  imports BT_Prelim
begin

section \<open>Group actions on a set\<close>

text \<open>
  An action of a (carrier) group @{term G} on a set @{term X} is a function
  @{term "act :: 'g \<Rightarrow> 'a \<Rightarrow> 'a"} respecting the unit and multiplication
  on @{term X}. We do not fix the group structure here; rather, we record
  the algebraic laws that an action must satisfy. Concrete instances will
  be given in later theories (the action of \<open>F\<^sub>2\<close> on itself by
  left translation; the action of \<open>SO(3)\<close> on \<open>S\<^sup>2\<close>).
\<close>

locale group_action =
  fixes carrier :: "'g set"
    and unit  :: "'g"
    and mult  :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"  (infixl \<open>\<cdot>\<close> 70)
    and act   :: "'g \<Rightarrow> 'a \<Rightarrow> 'a"
    and ground :: "'a set"
  assumes unit_carrier [simp]: "unit \<in> carrier"
    and mult_closed [intro]: "\<lbrakk>g \<in> carrier; h \<in> carrier\<rbrakk> \<Longrightarrow> g \<cdot> h \<in> carrier"
    and act_closed [intro]: "\<lbrakk>g \<in> carrier; x \<in> ground\<rbrakk> \<Longrightarrow> act g x \<in> ground"
    and act_unit [simp]: "x \<in> ground \<Longrightarrow> act unit x = x"
    and act_mult: "\<lbrakk>g \<in> carrier; h \<in> carrier; x \<in> ground\<rbrakk>
       \<Longrightarrow> act (g \<cdot> h) x = act g (act h x)"

context group_action
begin

definition orbit :: "'a \<Rightarrow> 'a set" where
  "orbit x = {y. \<exists>g \<in> carrier. y = act g x}"

definition image_set :: "'g \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "image_set g A = act g ` A"

lemma image_set_unit:
  assumes "A \<subseteq> ground"
  shows "image_set unit A = A"
    using assms unfolding image_set_def by force

lemma orbit_self:
  assumes "x \<in> ground"
  shows "x \<in> orbit x"
  using assms by (simp add: orbit_def) (metis act_unit unit_carrier)

end


section \<open>Paradoxical decomposition\<close>

text \<open>
  A subset @{term X} of the underlying set of a group action is
  \<^emph>\<open>paradoxical\<close> when it admits two finite collections of
  pairwise disjoint pieces, all contained in @{term X}, such that each
  collection can be translated (by group elements) so that the resulting
  \<^emph>\<open>disjoint\<close> union is the whole of @{term X}.

  This is the standard Banach-Tarski definition. We will instantiate it
  twice: once for \<open>F\<^sub>2\<close> acting on itself, and once for the
  rotation group acting on \<open>S\<^sup>2\<close> (and ultimately the ball).
\<close>

context group_action
begin

definition paradoxical :: "'a set \<Rightarrow> bool" where
  "paradoxical X \<longleftrightarrow>
    (\<exists>P Q :: 'a set list. \<exists>gP gQ :: 'g list.
       length P = length gP \<and> length Q = length gQ \<and>
       set gP \<subseteq> carrier \<and> set gQ \<subseteq> carrier \<and>
       pairwise_disjoint (P @ Q) \<and>
       pairwise_disjoint (map2 image_set gP P) \<and>
       pairwise_disjoint (map2 image_set gQ Q) \<and>
       (\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i) \<subseteq> X \<and>
       X = (\<Union>i<length P. image_set (gP ! i) (P ! i)) \<and>
       X = (\<Union>i<length Q. image_set (gQ ! i) (Q ! i)))"

text \<open>
  A specialised constructor for the most common case: each of @{term P}
  and @{term Q} has exactly two pieces. This matches the \<open>F\<^sub>2\<close>
  decomposition (split into the \<open>a\<close> / \<open>a\<^sup>-\<^sup>1\<close> classes and
  the \<open>b\<close> / \<open>b\<^sup>-\<^sup>1\<close> classes).
\<close>

lemma paradoxical_two_two:
  assumes "p1 \<in> carrier" "p2 \<in> carrier" "q1 \<in> carrier" "q2 \<in> carrier"
    and disj_P12: "P1 \<inter> P2 = {}"
    and disj_Q12: "Q1 \<inter> Q2 = {}"
    and disj_PQ:  "(P1 \<union> P2) \<inter> (Q1 \<union> Q2) = {}"
    and sub: "P1 \<union> P2 \<union> Q1 \<union> Q2 \<subseteq> X"
    and disj_imgP: "image_set p1 P1 \<inter> image_set p2 P2 = {}"
    and disj_imgQ: "image_set q1 Q1 \<inter> image_set q2 Q2 = {}"
    and cover_P: "X = image_set p1 P1 \<union> image_set p2 P2"
    and cover_Q: "X = image_set q1 Q1 \<union> image_set q2 Q2"
  shows "paradoxical X"
proof -
  let ?P = "[P1, P2]" and ?Q = "[Q1, Q2]"
  let ?gP = "[p1, p2]" and ?gQ = "[q1, q2]"
  have lens: "length ?P = length ?gP" "length ?Q = length ?gQ" by simp_all
  have closed: "set ?gP \<subseteq> carrier" "set ?gQ \<subseteq> carrier"
    using assms(1-4) by auto
  have disj_all: "pairwise_disjoint (?P @ ?Q)"
    using disj_P12 disj_Q12 disj_PQ
    by (auto simp: pairwise_disjoint_def nth_Cons' nth_append Int_commute Int_Un_distrib)
  have map2_P: "map2 image_set ?gP ?P = [image_set p1 P1, image_set p2 P2]" by simp
  have map2_Q: "map2 image_set ?gQ ?Q = [image_set q1 Q1, image_set q2 Q2]" by simp
  have disj_map_P: "pairwise_disjoint (map2 image_set ?gP ?P)"
    using disj_imgP unfolding map2_P
    by (auto simp: pairwise_disjoint_def nth_Cons' Int_commute)
  have disj_map_Q: "pairwise_disjoint (map2 image_set ?gQ ?Q)"
    using disj_imgQ unfolding map2_Q
    by (auto simp: pairwise_disjoint_def nth_Cons' Int_commute)
  have sub_un: "(\<Union>i<length ?P. ?P ! i) \<union> (\<Union>i<length ?Q. ?Q ! i) \<subseteq> X"
    using sub by (auto simp: lessThan_Suc)
  have cov_P': "X = (\<Union>i<length ?P. image_set (?gP ! i) (?P ! i))"
    using cover_P by (auto simp: lessThan_Suc)
  have cov_Q': "X = (\<Union>i<length ?Q. image_set (?gQ ! i) (?Q ! i))"
    using cover_Q by (auto simp: lessThan_Suc)
  show ?thesis
    unfolding paradoxical_def
    using lens closed disj_all disj_map_P disj_map_Q sub_un cov_P' cov_Q'
    by blast
qed

text \<open>
  With the finite-list convention used above, the empty set is
  paradoxical: take both families of pieces to be empty.  The two
  translated indexed unions are then both the empty union, hence both
  equal to \<open>{}\<close>.  This degenerate case is harmless in the later
  non-empty geometric applications, but recording it keeps the abstract
  definition honest about empty indexed unions.
\<close>

lemma paradoxical_empty: "paradoxical {}"
  unfolding paradoxical_def
  by (intro exI[where x="[]"])
     (auto simp: pairwise_disjoint_def image_set_def)

end


section \<open>Equidecomposability\<close>

text \<open>
  Two subsets @{term X} and @{term Y} are \<^emph>\<open>equidecomposable\<close>
  under a group action when they admit congruent partitions: the
  \<open>i\<close>-th piece of @{term X} maps onto the \<open>i\<close>-th piece of
  @{term Y} via some group element.
\<close>

context group_action
begin

definition equidecomposable :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "equidecomposable X Y \<longleftrightarrow>
    (\<exists>P Q :: 'a set list. \<exists>gs :: 'g list.
        length P = length Q \<and> length P = length gs \<and>
        set gs \<subseteq> carrier \<and>
        pairwise_disjoint P \<and> pairwise_disjoint Q \<and>
        X = (\<Union>i<length P. P ! i) \<and>
        Y = (\<Union>i<length Q. Q ! i) \<and>
        (\<forall>i < length P. Q ! i = image_set (gs ! i) (P ! i)))"

text \<open>
  The main development uses this relation only as background notation:
  the sphere and ball arguments below work directly with explicit finite
  lists of pieces and transformations, so the needed partition data is
  visible at each transfer step.
\<close>

end

end
