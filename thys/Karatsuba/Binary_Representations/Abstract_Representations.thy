section "Representations"

subsection "Abstract Representations"

theory Abstract_Representations
  imports Main
begin

text "Idea: some type @{text 'a} is represented non-uniquely by some type @{text 'b}.
The function @{term f} produces a unique representant."

locale abstract_representation =
  fixes from_type :: "'a \<Rightarrow> 'b"
  fixes to_type :: "'b \<Rightarrow> 'a"
  fixes f :: "'b \<Rightarrow> 'b"
  assumes to_from: "to_type \<circ> from_type = id"
  assumes from_to: "from_type \<circ> to_type = f"
begin

lemma to_from_elem[simp]: "to_type (from_type x) = x"
  using to_from by (metis comp_apply id_apply)
lemma from_to_elem: "from_type (to_type x) = f x"
  using from_to by (metis comp_apply)

lemma f_idem: "f \<circ> f = f"
proof -
  have "f \<circ> f = from_type \<circ> to_type \<circ> from_type \<circ> to_type"
    using from_to by fastforce
  also have "... = from_type \<circ> to_type"
    using to_from by (simp add: rewriteR_comp_comp)
  finally show ?thesis using from_to by simp
qed

corollary f_idem_elem[simp]: "f (f x) = f x"
  using f_idem by (metis comp_apply)

lemma f_from: "f \<circ> from_type = from_type"
proof -
  have "f \<circ> from_type = from_type \<circ> to_type \<circ> from_type"
    using from_to by simp
  also have "... = from_type"
    using to_from by (simp add: rewriteR_comp_comp)
  finally show ?thesis .
qed

corollary f_from_elem[simp]: "f (from_type x) = from_type x"
  using f_from by (metis comp_apply)

lemma to_f: "to_type \<circ> f = to_type"
proof -
  have "to_type \<circ> f = to_type \<circ> from_type \<circ> to_type"
    using from_to by fastforce
  also have "... = to_type" using to_from by simp
  finally show ?thesis .
qed

corollary to_f_elem[simp]: "to_type (f x) = to_type x"
  using to_f by (metis comp_apply)

lemma f_fixed_point_iff: "f x = x \<longleftrightarrow> (\<exists>y. x = from_type y)"
proof
  assume "f x = x"
  then show "\<exists>y. x = from_type y" using from_to_elem by metis
next
  assume "\<exists>y. x = from_type y"
  then obtain y where "x = from_type y" by blast
  then show "f x = x" by simp
qed

lemma f_fixed_point_iff': "f x = x \<longleftrightarrow> x = from_type (to_type x)"
  using from_to by auto

lemma range_f_range_from: "range f = range from_type"
proof (standard; standard)
  fix x
  assume "x \<in> range f"
  then obtain x' where "x = f x'" by blast
  then have "f x = x" by simp
  then show "x \<in> range from_type" using f_fixed_point_iff by blast
next
  fix x
  assume "x \<in> range from_type"
  then obtain y where "x = from_type y" by blast
  then have "f x = x" using f_fixed_point_iff by simp
  then show "x \<in> range f" by (metis rangeI)
qed

lemma to_eq_iff_f_eq: "to_type x = to_type y \<longleftrightarrow> f x = f y"
proof
  show "to_type x = to_type y \<Longrightarrow> f x = f y" using from_to_elem[symmetric] by simp
next
  show "f x = f y \<Longrightarrow> to_type x = to_type y" using to_f_elem by metis
qed

lemma from_inj: "inj from_type"
  using to_from by (metis inj_on_id inj_on_imageI2)

end

lemma from_to_f_criterion:
  assumes "to_type \<circ> from_type = id"
  assumes "f \<circ> from_type = from_type"
  assumes "\<And>x y. to_type x = to_type y \<Longrightarrow> f x = f y"
  shows "from_type \<circ> to_type = f"
proof
  fix x
  have "to_type (from_type (to_type x)) = to_type x"
    using assms(1) by (metis comp_apply id_apply)
  hence "f (from_type (to_type x)) = f x"
    using assms(3) by metis
  hence "from_type (to_type x) = f x"
    using assms(2) by (metis comp_apply)
  thus "(from_type \<circ> to_type) x = f x"
    by (metis comp_apply)
qed

end