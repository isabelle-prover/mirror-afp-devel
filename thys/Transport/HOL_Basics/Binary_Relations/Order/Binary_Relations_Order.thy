\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Binary_Relations_Order
  imports
    Binary_Relations_Order_Base
    Binary_Relations_Reflexive
    Binary_Relations_Symmetric
    Binary_Relations_Transitive
begin

paragraph \<open>Summary\<close>
text \<open>Basic results about the order on binary relations.\<close>

lemma in_dom_if_rel_if_rel_comp_le:
  assumes "(R \<circ>\<circ> S) \<le> (S \<circ>\<circ> R)"
  and "R x y" "S y z"
  shows "in_dom S x"
  using assms by (blast intro: in_dom_if_in_dom_rel_comp)

lemma in_codom_if_rel_if_rel_comp_le:
  assumes "(R \<circ>\<circ> S) \<le> (S \<circ>\<circ> R)"
  and "R x y" "S y z"
  shows "in_codom R z"
  using assms by (blast intro: in_codom_if_in_codom_rel_comp)

lemma rel_comp_le_rel_inv_if_rel_comp_le_if_symmetric:
  assumes symms: "symmetric R1" "symmetric R2"
  and le: "(R1 \<circ>\<circ> R2) \<le> R3"
  shows "(R2 \<circ>\<circ> R1) \<le> R3\<inverse>"
proof -
  from le have "(R1 \<circ>\<circ> R2)\<inverse> \<le> R3\<inverse>" by blast
  with symms show ?thesis by simp
qed

lemma rel_inv_le_rel_comp_if_le_rel_comp_if_symmetric:
  assumes symms: "symmetric R1" "symmetric R2"
  and le: "R3 \<le> (R1 \<circ>\<circ> R2)"
  shows "R3\<inverse> \<le> (R2 \<circ>\<circ> R1)"
proof -
  from le have "R3\<inverse> \<le> (R1 \<circ>\<circ> R2)\<inverse>" by blast
  with symms show ?thesis by simp
qed

corollary rel_comp_le_rel_comp_if_rel_comp_le_rel_comp_if_symmetric:
  assumes "symmetric R1" "symmetric R2" "symmetric R3" "symmetric R4"
  and "(R1 \<circ>\<circ> R2) \<le> (R3 \<circ>\<circ> R4)"
  shows "(R2 \<circ>\<circ> R1) \<le> (R4 \<circ>\<circ> R3)"
proof -
  from assms have "(R2 \<circ>\<circ> R1) \<le> (R3 \<circ>\<circ> R4)\<inverse>"
    by (intro rel_comp_le_rel_inv_if_rel_comp_le_if_symmetric)
  with assms show ?thesis by simp
qed

corollary rel_comp_le_rel_comp_iff_if_symmetric:
  assumes "symmetric R1" "symmetric R2" "symmetric R3" "symmetric R4"
  shows "(R1 \<circ>\<circ> R2) \<le> (R3 \<circ>\<circ> R4) \<longleftrightarrow> (R2 \<circ>\<circ> R1) \<le> (R4 \<circ>\<circ> R3)"
  using assms
  by (blast intro: rel_comp_le_rel_comp_if_rel_comp_le_rel_comp_if_symmetric)

corollary eq_if_le_rel_if_symmetric:
  assumes "symmetric R" "symmetric S"
  and "(R \<circ>\<circ> S) \<le> (S \<circ>\<circ> R)"
  shows "(R \<circ>\<circ> S) = (S \<circ>\<circ> R)"
  using assms rel_comp_le_rel_comp_iff_if_symmetric[of R S]
  by (intro antisym) auto

lemma rel_comp_le_rel_comp_if_le_rel_if_reflexive_on_in_codom_if_transitive:
  assumes trans: "transitive S"
  and refl_on: "reflexive_on (in_codom S) R"
  and le_rel: "R \<le> S"
  shows "R \<circ>\<circ> S \<le> S \<circ>\<circ> R"
proof (rule le_relI)
  fix x1 x2 assume"(R \<circ>\<circ> S) x1 x2"
  then obtain x3 where "R x1 x3" "S x3 x2" by blast
  then have "S x1 x3" using le_rel by blast
  with \<open>S x3 x2\<close> have "S x1 x2" using trans by blast
  with refl_on have "R x2 x2" by blast
  then show "(S \<circ>\<circ> R) x1 x2" using \<open>S x1 x2\<close> by blast
qed


end