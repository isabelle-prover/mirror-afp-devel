\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Alignment With Definitions from HOL\<close>
theory HOL_Alignment_Orders
  imports
    "HOL-Library.Preorder"
    HOL_Alignment_Binary_Relations
    HOL_Syntax_Bundles_Orders
    Orders
begin

named_theorems HOL_order_alignment

paragraph \<open>Functions\<close>
subparagraph \<open>Bi-Related\<close>

lemma (in preorder_equiv) equiv_eq_bi_related [HOL_order_alignment]:
  "equiv = bi_related (\<le>)"
  by (intro ext) (auto intro: equiv_antisym dest: equivD1 equivD2)


subparagraph \<open>Inflationary\<close>

overloading
  inflationary_on_set \<equiv> "inflationary_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "inflationary_on_set (S :: 'a set) :: ('a \<Rightarrow> _) \<Rightarrow> _ \<equiv>
    inflationary_on (mem_of S)"
end

lemma inflationary_on_set_eq_inflationary_on_pred [simp]:
  "(inflationary_on (S :: 'a set) :: ('a \<Rightarrow> _) \<Rightarrow> _) = inflationary_on (mem_of S)"
  unfolding inflationary_on_set_def by simp

lemma inflationary_on_set_iff_inflationary_on_pred [iff]:
  "inflationary_on (S :: 'a set) (R :: 'a \<Rightarrow> _) f \<longleftrightarrow> inflationary_on (mem_of S) R f"
  by simp

text \<open>Terms like @{term deflationary_on}, @{term rel_equivalence_on},
and @{term idempotent_on} are automatically overloaded. One can get similar
correspondence lemmas by unfolding the corresponding definitional theorems,
e.g. @{thm deflationary_on_eq_inflationary_on_rel_inv}.\<close>


paragraph \<open>Properties\<close>
subparagraph \<open>Equivalence Relations\<close>

lemma equiv_eq_equivalence_rel [HOL_order_alignment]: "equivp = equivalence_rel"
  by (intro ext) (fastforce intro!: equivpI
    simp: HOL_bin_rel_alignment reflexive_eq_reflexive_on elim!: equivpE)


subparagraph \<open>Partial Equivalence Relations\<close>

lemma part_equiv_eq_partial_equivalence_rel_if_rel [HOL_order_alignment]:
  assumes "R x y"
  shows "part_equivp R = partial_equivalence_rel R"
  using assms by (fastforce intro!: part_equivpI
    simp: HOL_bin_rel_alignment elim!: part_equivpE)


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


end