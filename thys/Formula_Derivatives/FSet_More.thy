theory FSet_More
imports  "~~/src/HOL/Library/FSet"
begin

lemma Suc_pred_image[simp]: "0 \<notin> P \<Longrightarrow> (\<lambda>x. Suc (x - Suc 0)) ` P = P"
    unfolding image_def by safe (metis Suc_pred neq0_conv)+

context includes fset.lifting begin

lift_definition fMax :: "('a :: linorder) fset \<Rightarrow> 'a" is Max .
lift_definition fMin :: "('a :: linorder) fset \<Rightarrow> 'a" is Min .

lemma fMax_in[simp]: "A \<noteq> {||} \<Longrightarrow> fMax A |\<in>| A"
  by transfer (rule Max_in)

lemma fMin_in[simp]: "A \<noteq> {||} \<Longrightarrow> fMin A |\<in>| A"
  by transfer (rule Min_in)

lemma fMax_ge[simp]: "x |\<in>| A \<Longrightarrow> x \<le> fMax A"
  by transfer (rule Max_ge)

lemma fMin_le[simp]: "x |\<in>| A \<Longrightarrow> fMin A \<le> x"
  by transfer (rule Min_le)

lemma fMax_eqI: "(\<And>y. y |\<in>| A \<Longrightarrow> y \<le> x) \<Longrightarrow> x |\<in>| A \<Longrightarrow> fMax A = x"
  by transfer (rule Max_eqI)

lemma fMin_eqI: "(\<And>y. y |\<in>| A \<Longrightarrow> x \<le> y) \<Longrightarrow> x |\<in>| A \<Longrightarrow> fMin A = x"
  by transfer (rule Min_eqI)

lemma fMax_singleton[simp]: "fMax {|x|} = x"
  by transfer (rule Max_singleton)

lemma fMin_singleton[simp]: "fMin {|x|} = x"
  by transfer (rule Min_singleton)

lemma fMax_finsert[simp]: "fMax (finsert x A) = (if A = {||} then x else max x (fMax A))"
  by transfer simp

lemma fMin_finsert[simp]: "fMin (finsert x A) = (if A = {||} then x else min x (fMin A))"
  by transfer simp

lemmas Suc_pred_fimage[simp] = Suc_pred_image[Transfer.transferred]

lemma mono_fMax_commute: "mono f \<Longrightarrow> A \<noteq> {||} \<Longrightarrow> f (fMax A) = fMax (f |`| A)"
  by transfer (rule mono_Max_commute)

end

context linorder
begin

context includes fset.lifting begin

lemma fset_linorder_max_induct[case_names fempty finsert]:
  assumes "P {||}"
  and     "\<And>x S. \<lbrakk>\<forall>y. y |\<in>| S \<longrightarrow> y < x; P S\<rbrakk> \<Longrightarrow> P (finsert x S)"
  shows "P S"
proof -
  (* FIXME transfer and right_total vs. bi_total *)
  note Domainp_forall_transfer[transfer_rule]
  show ?thesis
  using assms by (transfer fixing: less) (auto intro: finite_linorder_max_induct)
qed

lemma finsert_eq_iff:
  assumes "a |\<notin>| A" and "b |\<notin>| B"
  shows "(finsert a A = finsert b B) =
    (if a = b then A = B else \<exists>C. A = finsert b C \<and> b |\<notin>| C \<and> B = finsert a C \<and> a |\<notin>| C)"
  using assms by transfer (force simp: insert_eq_iff)

end

end

lemma ffilter_eq_fempty_iff:
  "ffilter P X = {||} \<longleftrightarrow> (\<forall>x. x |\<in>| X \<longrightarrow> \<not> P x)"
  "{||} = ffilter P X \<longleftrightarrow> (\<forall>x. x |\<in>| X \<longrightarrow> \<not> P x)"
  by auto

lemma max_ffilter_below[simp]: "\<lbrakk>x |\<in>| P; x < n\<rbrakk> \<Longrightarrow>
  max n (Suc (fMax (ffilter (\<lambda>i. i < n) P))) = n"
  by (metis max.absorb1 Suc_leI fMax_in fempty_iff ffmember_filter)

lemma fMax_boundedD:
  "\<lbrakk>fMax P < n; x |\<in>| P\<rbrakk> \<Longrightarrow> x < n"
  "\<lbrakk>fMax P \<le> n; n |\<notin>| P; x |\<in>| P\<rbrakk> \<Longrightarrow> x < n"
  by (metis fMax_ge le_less_trans, metis fMax_ge leD neqE order.strict_trans2)

lemma fMax_ffilter_less: "x |\<in>| P \<Longrightarrow> x < n \<Longrightarrow> fMax (ffilter (\<lambda>i. i < n) P) < n"
  by (metis fMax_in ffilter_eq_fempty_iff(2) ffmember_filter)

end
