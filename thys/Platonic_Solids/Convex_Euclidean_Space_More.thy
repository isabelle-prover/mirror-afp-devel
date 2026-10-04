section\<open>Convexity\<close>

theory Convex_Euclidean_Space_More
  imports "HOL-Analysis.Starlike"
begin

lemma connected_Int_rel_frontier:
  assumes "connected S"
      and "S \<subseteq> affine hull T"
      and "S \<inter> T \<noteq> {}"
      and "S - T \<noteq> {}"
    shows "S \<inter> rel_frontier T \<noteq> {}"
proof
  assume *: "S \<inter> rel_frontier T = {}"
  let ?E1 = "S \<inter> rel_interior T"
  let ?E2 = "S - closure T"
  have "openin (top_of_set S) ?E1"
    by (meson assms(2) openin_Int openin_rel_interior
        openin_subtopology_Int_subset openin_subtopology_self)
  moreover have "openin (top_of_set S) ?E2"
    by (meson closed_closedin closed_closure closedin_self
        closedin_subtopology_refl openin_subtopology_diff_closed)
  moreover have "S \<subseteq> ?E1 \<union> ?E2"
    using "*" rel_frontier_def by fastforce
  moreover have "?E1 \<inter> ?E2 = {}"
    using rel_interior_subset_closure by fastforce
  moreover have "?E1 \<noteq> {}"
    using assms(3) calculation(3) closure_subset by fastforce
  moreover have "?E2 \<noteq> {}"
    using assms(4) calculation(3) rel_interior_subset by fastforce
  ultimately show "False"
    using connected_openin[of S] assms(1) by blast
qed

end
