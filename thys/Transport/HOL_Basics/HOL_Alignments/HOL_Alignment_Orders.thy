\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Alignment With Order Definitions from HOL\<close>
theory HOL_Alignment_Orders
  imports
    "HOL-Library.Preorder"
    HOL_Alignment_Binary_Relations
    HOL_Syntax_Bundles_Orders
    Orders
begin

named_theorems HOL_order_alignment

paragraph \<open>Functions\<close>

definition "rel R x y \<equiv> (x, y) \<in> R"
lemma rel_of_eq [simp]: "rel = (\<lambda>R x y. (x, y) \<in> R)" unfolding rel_def by simp
lemma rel_of_iff [iff]: "rel R x y \<longleftrightarrow> (x, y) \<in> R" by simp

subparagraph \<open>Bi-Related\<close>

overloading
  bi_related_set \<equiv> "bi_related :: 'a rel \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
begin
  definition "bi_related_set (S :: 'a rel) \<equiv> bi_related (rel S) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"
end

lemma bi_related_set_eq_bi_related_pred [simp]:
  "((\<equiv>\<^bsub>S :: 'a rel\<^esub>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool) = (\<equiv>\<^bsub>rel S\<^esub>)"
  unfolding bi_related_set_def by simp

lemma bi_related_set_eq_bi_related_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  shows "(\<equiv>\<^bsub>S :: 'a rel\<^esub>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool \<equiv> (\<equiv>\<^bsub>R\<^esub>)"
  using assms by simp

lemma bi_related_set_iff_bi_related_pred [iff]: "(x :: 'a) \<equiv>\<^bsub>(S :: 'a rel)\<^esub> (y :: 'a) \<longleftrightarrow> x \<equiv>\<^bsub>rel S\<^esub> y"
  by simp

lemma (in preorder_equiv) equiv_eq_bi_related [HOL_order_alignment]:
  "equiv = bi_related (\<le>)"
  by (intro ext) (auto intro: equiv_antisym dest: equivD1 equivD2)


subparagraph \<open>Inflationary\<close>

overloading
  inflationary_on_set \<equiv> "inflationary_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
begin
  definition "inflationary_on_set (S :: 'a set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv>
    inflationary_on (mem_of S)"
end

lemma inflationary_on_set_eq_inflationary_on_pred [simp]:
  "(inflationary_on (S :: 'a set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool) =
    inflationary_on (mem_of S)"
  unfolding inflationary_on_set_def by simp

lemma inflationary_on_set_eq_inflationary_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "inflationary_on (S :: 'a set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv> inflationary_on P"
  using assms by simp

lemma inflationary_on_set_iff_inflationary_on_pred [iff]:
  "inflationary_on (S :: 'a set) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (f :: 'a \<Rightarrow> 'b) \<longleftrightarrow>
    inflationary_on (mem_of S) R f"
  by simp


subparagraph \<open>Deflationary\<close>

overloading
  deflationary_on_set \<equiv> "deflationary_on :: 'a set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
begin
  definition "deflationary_on_set (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv>
    deflationary_on (mem_of S)"
end

lemma deflationary_on_set_eq_deflationary_on_pred [simp]:
  "(deflationary_on (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool) = deflationary_on (mem_of S)"
  unfolding deflationary_on_set_def by simp

lemma deflationary_on_set_eq_deflationary_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "deflationary_on (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv> deflationary_on P"
  using assms by simp

lemma deflationary_on_set_iff_deflationary_on_pred [iff]:
  "deflationary_on (S :: 'a set) (R :: 'b \<Rightarrow> 'a \<Rightarrow> bool) (f :: 'a \<Rightarrow> 'b) \<longleftrightarrow> deflationary_on (mem_of S) R f"
  by simp


subparagraph \<open>Idempotent\<close>

overloading
  idempotent_on_set \<equiv> "idempotent_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "idempotent_on_set (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool \<equiv>
    idempotent_on (mem_of S)"
end

lemma idempotent_on_set_eq_idempotent_on_pred [simp]:
  "(idempotent_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool) = idempotent_on (mem_of S)"
  unfolding idempotent_on_set_def by simp

lemma idempotent_on_set_iff_idempotent_on_pred [iff]:
  "idempotent_on (S :: 'a set) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (f :: 'a \<Rightarrow> 'a) \<longleftrightarrow> idempotent_on (mem_of S) R f"
  by simp


paragraph \<open>Properties\<close>
subparagraph \<open>Equivalence Relations\<close>

lemma equiv_eq_equivalence_rel [HOL_order_alignment]: "equivp = equivalence_rel"
  by (intro ext) (fastforce intro: equivpI
    simp: HOL_bin_rel_alignment equivalence_rel_eq_equivalence_rel_on
    elim: equivpE)


subparagraph \<open>Partial Equivalence Relations\<close>

lemma part_equiv_eq_partial_equivalence_rel_if_rel [HOL_order_alignment]:
  assumes "R x y"
  shows "part_equivp R = partial_equivalence_rel R"
  using assms by (fastforce intro!: part_equivpI simp: HOL_bin_rel_alignment
    partial_equivalence_rel_eq_partial_equivalence_rel_on
    elim!: part_equivpE)


subparagraph \<open>Partial Orders\<close>

lemma (in order) partial_order [HOL_order_alignment]: "partial_order (\<le>)"
  using order_refl order_trans order_antisym by blast


subparagraph \<open>Preorders\<close>

lemma (in partial_preordering) preorder [HOL_order_alignment]: "preorder (\<^bold>\<le>)"
  using refl trans by blast

lemma partial_preordering_eq [HOL_order_alignment]:
  "partial_preordering = Preorders.preorder"
  by (intro ext) (auto intro: partial_preordering.intro
    dest: partial_preordering.trans partial_preordering.refl reflexiveD)

subparagraph \<open>Linear Orders\<close>

lemma (in linorder) linear_order: "linear_order (\<le>)"
  using linear partial_order by blast

subparagraph \<open>Strict Parital Orders\<close>

lemma (in preordering) linear_order: "strict_partial_order (\<^bold><)"
  using strict_iff_not trans by blast

subparagraph \<open>Strict Linear Orders\<close>

lemma (in linorder) strict_linear_order: "strict_linear_order (<)"
  using preordering.linear_order local.order.linear_order
  by (intro strict_linear_orderI) auto

subparagraph \<open>Well-Orders\<close>

lemma (in wellorder) wellorder: "wellorder (<)"
  by (metis wellorderI local.strict_linear_order local.wfp_on_less wfp_eq_wellfounded)

end