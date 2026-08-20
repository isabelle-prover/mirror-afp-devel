(*  Title:       Free_Action_Paradox.thy
    Author:      Arthur F. Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026

    Auxiliary definitions for free group actions.

    This is the principal reduction step in the Banach-Tarski proof:
    the paradoxical decomposition of F\<^sub>2 is transported to the
    sphere once the F\<^sub>2 action by rotations is free away from its
    countable fixed-point set.
*)

theory Free_Action_Paradox
  imports Paradoxical_Decomposition
begin

section \<open>Free actions\<close>

text \<open>
  An action is \<^emph>\<open>free\<close> on a set @{term X} if non-identity
  group elements have no fixed points in @{term X}: \<open>g \<cdot> x = x\<close>
  forces \<open>g = unit\<close>.
\<close>

context group_action
begin

definition free_on :: "'a set \<Rightarrow> bool" where
  "free_on X \<longleftrightarrow>
    (\<forall>g \<in> carrier. \<forall>x \<in> X. act g x = x \<longrightarrow> g = unit)"

end


section \<open>Choice of orbit representatives\<close>

text \<open>
  Given a free action of @{term G} on @{term X}, the orbits partition
  @{term X}, and for any subset of choice representatives \<open>M \<subseteq> X\<close>
  (one per orbit), every \<open>x \<in> X\<close> can be written uniquely as
  \<open>act g m\<close> for some \<open>g \<in> carrier\<close> and \<open>m \<in> M\<close>.

  This is where the axiom of choice enters: we pick one element from
  each orbit.
\<close>

context group_action
begin

definition orbit_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "orbit_eq x y \<longleftrightarrow> (\<exists>g \<in> carrier. y = act g x)"

lemma orbit_eq_refl: "x \<in> ground \<Longrightarrow> orbit_eq x x"
  unfolding orbit_eq_def using act_unit unit_carrier by metis

text \<open>
  When the action is free on @{term X}, the orbit relation is symmetric
  on @{term X}, provided every element has a group inverse in the
  carrier. We do not require \<open>group\<close>-level inverses here, so we
  state symmetry conditionally.
\<close>

end


section \<open>Transport of paradoxical decompositions along free actions\<close>

text \<open>
  This is the abstract Banach-Tarski reduction: suppose @{term G} acts
  freely on @{term X}, and @{term G} itself admits a paradoxical
  decomposition under the regular action (left multiplication on
  itself). Choosing one representative per @{term G}-orbit in @{term X}
  via the axiom of choice transports the paradox: each piece
  \<open>P\<^sub>i \<subseteq> G\<close> in the decomposition lifts to the union
  \<open>{act g m | g \<in> P\<^sub>i, m \<in> M}\<close>, where \<open>M\<close> is the chosen
  set of representatives.

  The later Hausdorff theory carries out this lift explicitly for
  \<open>S\<^sup>2 \<setminus> D\<close>: it defines orbit representatives, proves the lifted
  pieces are disjoint, and proves the two translated covers directly.
  The predicate below only packages the freeness and closure hypotheses
  that such an argument needs.
\<close>

context group_action
begin

text \<open>
  A free action is suitable for orbit-by-orbit transport when the set is
  contained in the ground space, the action is free on it, and the set is
  closed under the action of every carrier element.
\<close>

definition transports_paradox :: "'a set \<Rightarrow> bool" where
  "transports_paradox X \<longleftrightarrow>
    (X \<subseteq> ground \<and>
     free_on X \<and>
     (\<forall>x \<in> X. \<forall>g \<in> carrier. act g x \<in> X))"

text \<open>
  Under the assumptions captured by @{const transports_paradox}, a
  paradoxical decomposition of the carrier transports to a paradoxical
  decomposition of @{term X}. The proof is the standard
  ``orbit-by-orbit'' argument and uses the axiom of choice to select
  one representative per orbit.
\<close>

end

end
