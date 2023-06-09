section \<open>Preliminaries\<close>

subsection \<open>Connecting Predicate-Based and Set-Based Relations\<close>

theory Well_Order_Connection
  imports 
    Main 
    Complete_Non_Orders.Well_Relations
begin

lemma refl_on_relation_of: "refl_on A (relation_of r A) \<longleftrightarrow> reflexive A r"
  by (auto simp: refl_on_def reflexive_def relation_of_def)

lemma trans_relation_of: "trans (relation_of r A) \<longleftrightarrow> transitive A r"
  by (auto simp: trans_def relation_of_def transitive_def)

lemma preorder_on_relation_of: "preorder_on A (relation_of r A) \<longleftrightarrow> quasi_ordered_set A r"
  by (simp add: preorder_on_def refl_on_relation_of trans_relation_of quasi_ordered_set_def)

lemma antisym_relation_of: "antisym (relation_of r A) \<longleftrightarrow> antisymmetric A r"
  by (auto simp: antisym_def relation_of_def antisymmetric_def)

lemma partial_order_on_relation_of:
  "partial_order_on A (relation_of r A) \<longleftrightarrow> partially_ordered_set A r"
  by (auto simp: partial_order_on_def preorder_on_relation_of antisym_relation_of
      quasi_ordered_set_def partially_ordered_set_def)

lemma total_on_relation_of: "total_on A (relation_of r A) \<longleftrightarrow> semiconnex A r"
  by (auto simp: total_on_def relation_of_def semiconnex_def)

lemma linear_order_on_relation_of:
  shows "linear_order_on A (relation_of r A) \<longleftrightarrow> total_ordered_set A r"
  by (auto simp: linear_order_on_def partial_order_on_relation_of total_on_relation_of
      total_ordered_set_def total_quasi_ordered_set_def partially_ordered_set_def
      connex_iff_semiconnex_reflexive)

lemma relation_of_sub_Id: "(relation_of r A - Id) = relation_of (\<lambda>x y. r x y \<and> x \<noteq> y) A"
  by (auto simp: relation_of_def)

lemma (in antisymmetric) asympartp_iff_weak_neq:
  shows "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> asympartp (\<sqsubseteq>) x y \<longleftrightarrow> x \<sqsubseteq> y \<and> x \<noteq> y"
  by (auto intro!: asympartpI antisym)

lemma wf_relation_of: "wf (relation_of r A) = well_founded A r"
  apply (simp add: wf_eq_minimal relation_of_def well_founded_iff_ex_extremal Ball_def)
  by (metis (no_types, opaque_lifting) equals0I insert_Diff insert_not_empty  subsetI  subset_iff)

lemma well_order_on_relation_of:
  shows "well_order_on A (relation_of r A) \<longleftrightarrow> well_ordered_set A r"
  by (auto simp: well_order_on_def linear_order_on_relation_of relation_of_sub_Id
      wf_relation_of well_ordered_iff_well_founded_total_ordered
      antisymmetric.asympartp_iff_weak_neq total_ordered_set_def
      cong: well_founded_cong)

lemma (in connex) Field_relation_of: "Field (relation_of (\<sqsubseteq>) A) = A"
  by (auto simp: Field_def relation_of_def)

lemma (in well_ordered_set) Well_order_relation_of:
  shows "Well_order (relation_of (\<sqsubseteq>) A)"
  by (auto simp: Field_relation_of well_order_on_relation_of well_ordered_set_axioms)

lemma in_relation_of: "(x,y) \<in> relation_of r A \<longleftrightarrow> x \<in> A \<and> y \<in> A \<and> r x y"
  by (simp add: relation_of_def)

lemma relation_of_triv: "relation_of (\<lambda>x y. (x,y) \<in> r) UNIV = r"
  by (auto simp: relation_of_def)

lemma Restr_eq_relation_of: "Restr R A = relation_of (\<lambda>x y. (x,y) \<in> R) A"
  by (auto simp: relation_of_def)

theorem ex_well_order: "\<exists>r. well_ordered_set A r"
proof-
  from well_order_on obtain R where R: "well_order_on A R" by auto
  then have "well_order_on A (Restr R A)"
    by (simp add: well_order_on_Field[OF R] Restr_Field)
  then show ?thesis by (auto simp: Restr_eq_relation_of well_order_on_relation_of)
qed


end