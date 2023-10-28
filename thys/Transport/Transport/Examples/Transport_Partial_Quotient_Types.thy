\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transport for Partial Quotient Types\<close>
theory Transport_Partial_Quotient_Types
  imports
    HOL.Lifting
    Transport
begin

paragraph \<open>Summary\<close>
text \<open>Every partial quotient type @{term Quotient}, as used by the Lifting
package, is transportable.\<close>

context transport
begin

interpretation t : transport L "(=)" l r .

lemma Quotient_T_eq_Galois:
  assumes "Quotient (\<le>\<^bsub>L\<^esub>) l r T"
  shows "T = t.Galois"
proof (intro ext iffI)
  fix x y assume "T x y"
  with assms have "x \<le>\<^bsub>L\<^esub> x" "l x = y" using Quotient_cr_rel by auto
  with assms have "r (l x) \<le>\<^bsub>L\<^esub> x" "r (l x) \<le>\<^bsub>L\<^esub> r y"
    using Quotient_rep_abs Quotient_rep_reflp by auto
  with assms have "x \<le>\<^bsub>L\<^esub> r y" using Quotient_part_equivp
    by (blast elim: part_equivpE dest: transpD sympD)
  then show "t.Galois x y" by blast
next
  fix x y assume "t.Galois x y"
  with assms show "T x y" using Quotient_cr_rel Quotient_refl1 Quotient_symp
    by (fastforce intro: Quotient_rel_abs2[symmetric] dest: sympD)
qed

lemma Quotient_if_preorder_equivalence:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (=)) l r"
  shows "Quotient (\<le>\<^bsub>L\<^esub>) l r t.Galois"
proof (rule QuotientI)
  from assms show g2: "l (r y) = y" for y by fastforce
  from assms show "r y \<le>\<^bsub>L\<^esub> r y" for y by blast
  show g1: "x \<le>\<^bsub>L\<^esub> x' \<longleftrightarrow> x \<le>\<^bsub>L\<^esub> x \<and> x' \<le>\<^bsub>L\<^esub> x' \<and> l x = l x'"
    (is "?lhs \<longleftrightarrow> ?rhs") for x x'
  proof (rule iffI)
    assume ?rhs
    with assms have "\<eta> x \<le>\<^bsub>L\<^esub> \<eta> x'" by fastforce
    moreover from \<open>?rhs\<close> assms have "x \<le>\<^bsub>L\<^esub> \<eta> x" "\<eta> x' \<le>\<^bsub>L\<^esub> x'"
      by (blast elim: t.preorder_equivalence_order_equivalenceE)+
    moreover from assms have "transitive (\<le>\<^bsub>L\<^esub>)" by blast
    ultimately show "x \<le>\<^bsub>L\<^esub> x'" by blast
  next
    assume ?lhs
    with assms show ?rhs by blast
  qed
  from assms show "t.Galois = (\<lambda>x y. x \<le>\<^bsub>L\<^esub> x \<and> l x = y)"
    by (intro ext iffI)
    (metis g1 g2 t.left_GaloisE,
      auto intro!: t.left_Galois_left_if_left_rel_if_inflationary_on_in_fieldI
      elim!: t.preorder_equivalence_order_equivalenceE)
qed

lemma partial_equivalence_rel_equivalence_if_Quotient:
  assumes "Quotient (\<le>\<^bsub>L\<^esub>) l r T"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (=)) l r"
proof (rule t.partial_equivalence_rel_equivalence_if_order_equivalenceI)
  from Quotient_part_equivp[OF assms] show "partial_equivalence_rel (\<le>\<^bsub>L\<^esub>)"
    by (blast elim: part_equivpE dest: transpD sympD)
  have "x \<equiv>\<^bsub>L\<^esub> r (l x)" if "in_field (\<le>\<^bsub>L\<^esub>) x" for x
  proof -
    from assms \<open>in_field (\<le>\<^bsub>L\<^esub>) x\<close> have "x \<le>\<^bsub>L\<^esub> x"
      using Quotient_refl1 Quotient_refl2 by fastforce
    with assms Quotient_rep_abs Quotient_symp show ?thesis
      by (fastforce dest: sympD)
  qed
  with assms show "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (=)) l r"
    using Quotient_abs_rep Quotient_rel_abs Quotient_rep_reflp
      Quotient_abs_rep[symmetric]
    by (intro t.order_equivalenceI dep_mono_wrt_relI rel_equivalence_onI
      inflationary_onI deflationary_onI)
    auto
qed auto

corollary Quotient_iff_partial_equivalence_rel_equivalence:
  "Quotient (\<le>\<^bsub>L\<^esub>) l r t.Galois \<longleftrightarrow> ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (=)) l r"
  using Quotient_if_preorder_equivalence partial_equivalence_rel_equivalence_if_Quotient
  by blast

corollary Quotient_T_eq_ge_Galois_right:
  assumes "Quotient (\<le>\<^bsub>L\<^esub>) l r T"
  shows "T = t.ge_Galois_right"
  using assms
  by (subst t.ge_Galois_right_eq_left_Galois_if_symmetric_if_in_codom_eq_in_dom_if_galois_prop)
  (blast dest: partial_equivalence_rel_equivalence_if_Quotient
  intro: in_codom_eq_in_dom_if_reflexive_on_in_field Quotient_T_eq_Galois)+

end


end