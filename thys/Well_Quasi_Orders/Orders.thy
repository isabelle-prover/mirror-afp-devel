theory Orders
imports
  "Well_Quasi_Orders"
  "Well_Partial_Orders"
begin

text {*If the strict part of a quasi-order @{term Q} is a
well-partial-order, then @{term Q} is a well-quasi-order.*}
lemma wpo_on_strict_imp_wqo_on:
  fixes P Q
  defines "P \<equiv> strict Q"
  assumes "wpo_on P A" and "qo_on Q A"
  shows "wqo_on Q A"
proof
  from `qo_on Q A` show "transp_on Q A"
    unfolding qo_on_def by blast
  from `qo_on Q A` have "reflp_on Q A"
    unfolding qo_on_def by blast
  moreover have "almost_full_on P\<^sup>=\<^sup>= A"
    by (rule `wpo_on P A` [THEN wpo_on_imp_almost_full_on])
  ultimately show "almost_full_on Q A"
    unfolding P_def reflp_on_def almost_full_on_def good_def
    by (auto) (metis)
qed

lemma qo_on_imp_po_on_strict:
  "qo_on P A \<Longrightarrow> po_on (strict P) A"
  unfolding qo_on_def po_on_def
  by (auto) (metis (no_types) transp_on_imp_transp_on_strict)

lemma po_on_imp_qo_on_reflclp:
  "po_on P A \<Longrightarrow> qo_on P\<^sup>=\<^sup>= A"
  unfolding qo_on_def po_on_def
  by (metis reflp_on_reflclp transp_on_imp_transp_on_reflclp)

text {*For antisymmetric @{term P}, @{term P} is a quasi-order iff
it is reflexive and its strict part is a partial order.*}
lemma qo_on_po_on_conv:
  assumes "antisymp_on P A"
  shows "qo_on P A \<longleftrightarrow> reflp_on P A \<and> po_on (strict P) A"
  (is "?lhs = ?rhs")
proof
  assume "?lhs"
  then have "reflp_on P A" by (rule qo_on_imp_reflp_on)
  with `?lhs` show "?rhs"
    by (blast dest: qo_on_imp_po_on_strict)
next
  assume "?rhs"
  then have "po_on (strict P) A"
    and refl: "\<And>x. \<lbrakk>x \<in> A\<rbrakk> \<Longrightarrow> P x x"
    unfolding reflp_on_def by blast+
  then have "qo_on (strict P)\<^sup>=\<^sup>= A" by (blast dest: po_on_imp_qo_on_reflclp)
  moreover from assms
    have "\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> (strict P)\<^sup>=\<^sup>= x y = P x y"
    by (auto intro: refl simp: antisymp_on_def)
  ultimately show "?lhs"
    unfolding qo_on_def reflp_on_def transp_on_def
    by blast
qed

lemma wqo_on_imp_wpo_on:
  fixes P Q
  defines "P \<equiv> strict Q"
  assumes "wqo_on Q A" and "antisymp_on Q A"
  shows "wpo_on P A"
proof
  have refl: "\<And>x. x \<in> A \<Longrightarrow> Q x x"
    using `wqo_on Q A` [THEN wqo_on_imp_reflp_on]
    unfolding reflp_on_def by blast
  show "irreflp_on P A" by (simp add: P_def)
  show "transp_on P A"
    using `wqo_on Q A` [THEN wqo_on_imp_transp_on, THEN transp_on_imp_transp_on_strict]
    unfolding P_def .
  from `wqo_on Q A` have af: "almost_full_on Q A"
    by (rule wqo_on_imp_almost_full_on)
  from assms
    have eq: "\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> Q x y = (strict Q)\<^sup>=\<^sup>= x y"
    by (auto intro: refl simp: antisymp_on_def)
  show "almost_full_on P\<^sup>=\<^sup>= A"
  proof
    fix f
    assume *: "\<forall>i::nat. f i \<in> A"
    from af [unfolded almost_full_on_def, THEN spec, THEN mp, OF this]
      show "good P\<^sup>=\<^sup>= f"
      using * and eq
      unfolding P_def good_def
      by blast
  qed
qed

lemma wpo_on_strict_wqo_on_conv:
  assumes "qo_on P A" and "antisymp_on P A"
  shows "wpo_on (strict P) A = wqo_on P A"
  using wpo_on_strict_imp_wqo_on [OF _ assms(1)]
    and wqo_on_imp_wpo_on [OF _ assms(2)]
    by blast

end

