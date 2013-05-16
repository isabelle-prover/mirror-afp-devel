(*FIXME: depends on Well_Order_Extension.thy, which is currently awaiting
integration into the Isabelle distribituion.*)
theory Wpo_Extension
imports
  Well_Partial_Orders
  Well_Order_Extension
begin

lemma wfp_on_imp_wf:
  assumes "wfp_on P A"
  shows "wf {(x, y). x \<in> A \<and> y \<in> A \<and> P x y}"
  using wfp_on_imp_inductive_on [OF assms]
  unfolding wf_def inductive_on_def
  by (simp) (metis)

lemma wf_imp_wfp_on:
  assumes "wf {(x, y). x \<in> A \<and> y \<in> A \<and> P x y}"
  shows "wfp_on P A"
  using assms
  unfolding wf_iff_no_infinite_down_chain wfp_on_def
  by auto

lemma wfp_on_wf_conv:
  "wfp_on P A \<longleftrightarrow> wf {(x, y). x \<in> A \<and> y \<in> A \<and> P x y}"
  by (blast dest: wf_imp_wfp_on wfp_on_imp_wf)

lemma well_order_extension:
  assumes "wfp_on P A"
  shows "\<exists>W. (\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> W x y) \<and> po_on W A \<and> wfp_on W A \<and> total_on W A"
proof -
  let ?r = "{(x, y). x \<in> A \<and> y \<in> A \<and> P x y}"
  from wfp_on_imp_wf [OF assms]
    have "wf ?r" and "Field ?r \<subseteq> A" by (auto simp: Field_def)
  with well_order_on_extension [of ?r A] obtain r
    where "?r \<subseteq> r" and "well_order_on A r" by blast
  then have wf_R: "wf (r - Id)" and refl_R: "refl_on A r"
    and antisym_R: "antisym r" and total_R: "Relation.total_on A r"
    and trans_R: "trans r"
    by (auto simp: well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def)
  def Q \<equiv> "\<lambda>x y. (x, y) \<in> r - Id"
  have *: "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q x y"
    using `?r \<subseteq> r` and wfp_on_imp_irreflp_on [OF assms]
    by (auto simp: Q_def irreflp_on_def)
  have "wfp_on Q UNIV"
    by (rule inductive_on_imp_wfp_on, insert wf_R, simp only: inductive_on_def wf_def Q_def)
       (metis UNIV_I)
  with wfp_on_subset have "wfp_on Q A" by (metis (full_types) subset_UNIV)
  have antisym_Q: "antisymp_on Q\<^sup>=\<^sup>= UNIV"
    using antisym_R by (auto simp: antisym_def antisymp_on_def Q_def)
  have "total_on Q\<^sup>=\<^sup>= A"
    using total_R by (auto simp: Relation.total_on_def total_on_def Q_def)
  then have "total_on Q A" by (auto simp: total_on_def)
  have "irreflp_on Q A" by (metis `wfp_on Q A` wfp_on_imp_irreflp_on)
  have "transp_on Q\<^sup>=\<^sup>= UNIV"
    using trans_R by (simp only: trans_def transp_on_def Q_def) blast
  with transp_on_subset have "transp_on Q\<^sup>=\<^sup>= A" by (metis (full_types) subset_UNIV)
  then have "transp_on Q A"
    unfolding transp_on_def
    by (auto) (metis (full_types) UNIV_I antisym_Q antisymp_on_def antisymp_on_reflclp)
  with `irreflp_on Q A`
    have "po_on Q A" by (auto simp: po_on_def)
  with `total_on Q A` and `wfp_on Q A`
    show ?thesis using * by blast
qed

text {*Every well-founded and total partial order is a well-partial-order.*}
lemma po_on_imp_wpo_on:
  assumes "po_on P A" and "wfp_on P A" and "total_on P A"
  shows "wpo_on P A"
proof
  show "irreflp_on P A" by (rule po_on_imp_irreflp_on [OF `po_on P A`])
  show "transp_on P A" by (rule po_on_imp_transp_on [OF `po_on P A`])
  show "almost_full_on (P\<^sup>=\<^sup>=) A"
  proof (rule ccontr)
    assume "~ ?thesis"
    then obtain f where *: "\<And>i::nat. f i \<in> A" and
      "\<And>i j. i < j \<Longrightarrow> \<not> P\<^sup>=\<^sup>= (f i) (f j)"
      unfolding almost_full_on_def good_def by blast
    with `total_on P A` have "\<And>i j. i < j \<Longrightarrow> P (f j) (f i)"
      unfolding total_on_def by blast
    then have "\<forall>i. P (f (Suc i)) (f i)" by auto
    with `wfp_on P A` and * show False unfolding wfp_on_def by blast
  qed
qed

text {*Every well-founded relation can be extended to a well-partial-order.*}
lemma wpo_on_extension:
  assumes "wfp_on P A"
  shows "\<exists>W. (\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> W x y) \<and> wpo_on W A"
  using well_order_extension [OF assms] and po_on_imp_wpo_on
  by blast

end

