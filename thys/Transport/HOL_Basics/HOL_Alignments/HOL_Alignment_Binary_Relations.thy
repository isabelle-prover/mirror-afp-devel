\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Alignment With Definitions from HOL.Main\<close>
theory HOL_Alignment_Binary_Relations
  imports
    Main
    HOL_Mem_Of
    HOL_Syntax_Bundles_Relations
    LBinary_Relations
begin

unbundle no_HOL_relation_syntax

named_theorems HOL_bin_rel_alignment

paragraph \<open>Properties\<close>
subparagraph \<open>Antisymmetric\<close>

overloading
  antisymmetric_on_set \<equiv> "antisymmetric_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "antisymmetric_on_set (S :: 'a set) :: ('a \<Rightarrow> _) \<Rightarrow> _ \<equiv>
    antisymmetric_on (mem_of S)"
end

lemma antisymmetric_on_set_eq_antisymmetric_on_pred [simp]:
  "(antisymmetric_on (S :: 'a set) :: ('a \<Rightarrow> _) \<Rightarrow> bool) =
    antisymmetric_on (mem_of S)"
  unfolding antisymmetric_on_set_def by simp

lemma antisymmetric_on_set_iff_antisymmetric_on_pred [iff]:
  "antisymmetric_on (S :: 'a set) (R :: 'a \<Rightarrow> _) \<longleftrightarrow> antisymmetric_on (mem_of S) R"
  by simp

lemma antisymp_eq_antisymmetric [HOL_bin_rel_alignment]:
  "antisymp = antisymmetric"
  by (intro ext) (auto intro: antisympI dest: antisymmetricD antisympD)


subparagraph \<open>Injective\<close>

overloading
  rel_injective_on_set \<equiv> "rel_injective_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  rel_injective_at_set \<equiv> "rel_injective_at :: 'a set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_injective_on_set (S :: 'a set) :: ('a \<Rightarrow> _) \<Rightarrow> _ \<equiv>
    rel_injective_on (mem_of S)"
  definition "rel_injective_at_set (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> _) \<Rightarrow> _ \<equiv>
    rel_injective_at (mem_of S)"
end

lemma rel_injective_on_set_eq_rel_injective_on_pred [simp]:
  "(rel_injective_on (S :: 'a set) :: ('a \<Rightarrow> _) \<Rightarrow> bool) =
    rel_injective_on (mem_of S)"
  unfolding rel_injective_on_set_def by simp

lemma rel_injective_on_set_iff_rel_injective_on_pred [iff]:
  "rel_injective_on (S :: 'a set) (R :: 'a \<Rightarrow> _) \<longleftrightarrow> rel_injective_on (mem_of S) R"
  by simp

lemma rel_injective_at_set_eq_rel_injective_at_pred [simp]:
  "(rel_injective_at (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) =
    rel_injective_at (mem_of S)"
  unfolding rel_injective_at_set_def by simp

lemma rel_injective_at_set_iff_rel_injective_at_pred [iff]:
  "rel_injective_at (S :: 'a set) (R :: 'b \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> rel_injective_at (mem_of S) R"
  by simp

lemma left_unique_eq_rel_injective [HOL_bin_rel_alignment]:
  "left_unique = rel_injective"
  by (intro ext) (blast intro: left_uniqueI dest: rel_injectiveD left_uniqueD)

subparagraph \<open>Irreflexive\<close>

overloading
  irreflexive_on_set \<equiv> "irreflexive_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "irreflexive_on_set (S :: 'a set) :: ('a \<Rightarrow> _) \<Rightarrow> _ \<equiv>
    irreflexive_on (mem_of S)"
end

lemma irreflexive_on_set_eq_irreflexive_on_pred [simp]:
  "(irreflexive_on (S :: 'a set) :: ('a \<Rightarrow> _) \<Rightarrow> bool) =
    irreflexive_on (mem_of S)"
  unfolding irreflexive_on_set_def by simp

lemma irreflexive_on_set_iff_irreflexive_on_pred [iff]:
  "irreflexive_on (S :: 'a set) (R :: 'a \<Rightarrow> _) \<longleftrightarrow>
    irreflexive_on (mem_of S) R"
  by simp

lemma irreflp_on_eq_irreflexive_on [HOL_bin_rel_alignment]:
  "irreflp_on = irreflexive_on"
  by (intro ext) (blast intro: irreflp_onI dest: irreflp_onD)

lemma irreflp_eq_irreflexive [HOL_bin_rel_alignment]: "irreflp = irreflexive"
  by (intro ext) (blast intro: irreflpI dest: irreflexiveD irreflpD)

subparagraph \<open>Left-Total\<close>

overloading
  left_total_on_set \<equiv> "left_total_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "left_total_on_set (S :: 'a set) :: ('a \<Rightarrow> _) \<Rightarrow> _ \<equiv>
    left_total_on (mem_of S)"
end

lemma left_total_on_set_eq_left_total_on_pred [simp]:
  "(left_total_on (S :: 'a set) :: ('a \<Rightarrow> _) \<Rightarrow> bool) =
    left_total_on (mem_of S)"
  unfolding left_total_on_set_def by simp

lemma left_total_on_set_iff_left_total_on_pred [iff]:
  "left_total_on (S :: 'a set) (R :: 'a \<Rightarrow> _) \<longleftrightarrow> left_total_on (mem_of S) R"
  by simp

lemma Transfer_left_total_eq_left_total [HOL_bin_rel_alignment]:
  "Transfer.left_total = Binary_Relations_Left_Total.left_total"
  by (intro ext) (fast intro: Transfer.left_totalI
    elim: Transfer.left_totalE Binary_Relations_Left_Total.left_totalE)


subparagraph \<open>Reflexive\<close>

overloading
  reflexive_on_set \<equiv> "reflexive_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "reflexive_on_set (S :: 'a set) :: ('a \<Rightarrow> _) \<Rightarrow> _ \<equiv>
    reflexive_on (mem_of S)"
end

lemma reflexive_on_set_eq_reflexive_on_pred [simp]:
  "(reflexive_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) =
    reflexive_on (mem_of S)"
  unfolding reflexive_on_set_def by simp

lemma reflexive_on_set_iff_reflexive_on_pred [iff]:
  "reflexive_on (S :: 'a set) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow>
    reflexive_on (mem_of S) R"
  by simp

lemma reflp_on_eq_reflexive_on [HOL_bin_rel_alignment]:
  "reflp_on = reflexive_on"
  by (intro ext) (blast intro: reflp_onI dest: reflp_onD)

lemma reflp_eq_reflexive [HOL_bin_rel_alignment]: "reflp = reflexive"
  by (intro ext) (blast intro: reflpI dest: reflexiveD reflpD)


subparagraph \<open>Right-Unique\<close>

overloading
  right_unique_on_set \<equiv> "right_unique_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  right_unique_at_set \<equiv> "right_unique_at :: 'a set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "right_unique_on_set (S :: 'a set) :: ('a \<Rightarrow> _) \<Rightarrow> _ \<equiv>
    right_unique_on (mem_of S)"
  definition "right_unique_at_set (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> _) \<Rightarrow> _ \<equiv>
    right_unique_at (mem_of S)"
end

lemma right_unique_on_set_eq_right_unique_on_pred [simp]:
  "(right_unique_on (S :: 'a set) :: ('a \<Rightarrow> _) \<Rightarrow> bool) =
    right_unique_on (mem_of S)"
  unfolding right_unique_on_set_def by simp

lemma right_unique_on_set_iff_right_unique_on_pred [iff]:
  "right_unique_on (S :: 'a set) (R :: 'a \<Rightarrow> _) \<longleftrightarrow> right_unique_on (mem_of S) R"
  by simp

lemma right_unique_at_set_eq_right_unique_at_pred [simp]:
  "(right_unique_at (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) =
    right_unique_at (mem_of S)"
  unfolding right_unique_at_set_def by simp

lemma right_unique_at_set_iff_right_unique_at_pred [iff]:
  "right_unique_at (S :: 'a set) (R :: 'b \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> right_unique_at (mem_of S) R"
  by simp

lemma Transfer_right_unique_eq_right_unique [HOL_bin_rel_alignment]:
  "Transfer.right_unique = Binary_Relations_Right_Unique.right_unique"
  by (intro ext) (blast intro: Transfer.right_uniqueI
    dest: Transfer.right_uniqueD Binary_Relations_Right_Unique.right_uniqueD)


subparagraph \<open>Surjective\<close>

overloading
  rel_surjective_at_set \<equiv> "rel_surjective_at :: 'a set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_surjective_at_set (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> _) \<Rightarrow> _ \<equiv>
    rel_surjective_at (mem_of S)"
end

lemma rel_surjective_at_set_eq_rel_surjective_at_pred [simp]:
  "(rel_surjective_at (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> _) \<Rightarrow> bool) =
    rel_surjective_at (mem_of S)"
  unfolding rel_surjective_at_set_def by simp

lemma rel_surjective_at_set_iff_rel_surjective_at_pred [iff]:
  "rel_surjective_at (S :: 'a set) (R :: 'b \<Rightarrow> 'a \<Rightarrow> _) \<longleftrightarrow> rel_surjective_at (mem_of S) R"
  by simp

lemma Transfer_right_total_eq_rel_surjective [HOL_bin_rel_alignment]:
  "Transfer.right_total = rel_surjective"
  by (intro ext) (fast intro: Transfer.right_totalI rel_surjectiveI
    elim: Transfer.right_totalE rel_surjectiveE)


subparagraph \<open>Symmetric\<close>

overloading
  symmetric_on_set \<equiv> "symmetric_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "symmetric_on_set (S :: 'a set) :: ('a \<Rightarrow> _) \<Rightarrow> _ \<equiv>
    symmetric_on (mem_of S)"
end

lemma symmetric_on_set_eq_symmetric_on_pred [simp]:
  "(symmetric_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) =
    symmetric_on (mem_of S)"
  unfolding symmetric_on_set_def by simp

lemma symmetric_on_set_iff_symmetric_on_pred [iff]:
  "symmetric_on (S :: 'a set) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow>
    symmetric_on (mem_of S) R"
  by simp

lemma symp_eq_symmetric [HOL_bin_rel_alignment]: "symp = symmetric"
  by (intro ext) (blast intro: sympI dest: symmetricD sympD)


subparagraph \<open>Transitive\<close>

overloading
  transitive_on_set \<equiv> "transitive_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "transitive_on_set (S :: 'a set) :: ('a \<Rightarrow> _) \<Rightarrow> _ \<equiv>
    transitive_on (mem_of S)"
end

lemma transitive_on_set_eq_transitive_on_pred [simp]:
  "(transitive_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) =
    transitive_on (mem_of S)"
  unfolding transitive_on_set_def by simp

lemma transitive_on_set_iff_transitive_on_pred [iff]:
  "transitive_on (S :: 'a set) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow>
    transitive_on (mem_of S) R"
  by simp

lemma transp_eq_transitive [HOL_bin_rel_alignment]: "transp = transitive"
  by (intro ext) (blast intro: transpI dest: transpD)


paragraph \<open>Functions\<close>

lemma relcompp_eq_rel_comp [HOL_bin_rel_alignment]: "relcompp = rel_comp"
  by (intro ext) auto

lemma conversep_eq_rel_inv [HOL_bin_rel_alignment]: "conversep = rel_inv"
  by (intro ext) auto

lemma Domainp_eq_in_dom [HOL_bin_rel_alignment]: "Domainp = in_dom"
  by (intro ext) auto

lemma Rangep_eq_in_codom [HOL_bin_rel_alignment]: "Rangep = in_codom"
   by (intro ext) auto

overloading
  restrict_left_set \<equiv> "restrict_left :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a set) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
begin
  definition "restrict_left_set (R :: 'a \<Rightarrow> _) (S :: 'a set) \<equiv> R\<restriction>\<^bsub>mem_of S\<^esub>"
end

lemma restrict_left_set_eq_restrict_left_pred [simp]:
  "(R\<restriction>\<^bsub>S :: 'a set\<^esub> :: 'a \<Rightarrow> _) = R\<restriction>\<^bsub>mem_of S\<^esub>"
  unfolding restrict_left_set_def by simp

lemma restrict_left_set_iff_restrict_left_pred [iff]:
  "(R\<restriction>\<^bsub>S :: 'a set\<^esub> :: 'a \<Rightarrow> _) x y \<longleftrightarrow> R\<restriction>\<^bsub>mem_of S\<^esub> x y"
  by simp



paragraph \<open>Restricted Equality\<close>

lemma eq_onp_eq_eq_restrict [HOL_bin_rel_alignment]: "eq_onp = eq_restrict"
  unfolding eq_onp_def by (intro ext) auto

overloading
  eq_restrict_set \<equiv> "eq_restrict :: 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
begin
  definition "eq_restrict_set (S :: 'a set) \<equiv> ((=\<^bsub>mem_of S\<^esub>) :: 'a \<Rightarrow> _)"
end

lemma eq_restrict_set_eq_eq_restrict_pred [simp]:
  "((=\<^bsub>S :: 'a set\<^esub>) :: 'a \<Rightarrow> _) = (=\<^bsub>mem_of S\<^esub>)"
  unfolding eq_restrict_set_def by simp

lemma eq_restrict_set_iff_eq_restrict_pred [iff]:
  "(x :: 'a) =\<^bsub>(S :: 'a set)\<^esub> y \<longleftrightarrow> x =\<^bsub>mem_of S\<^esub> y"
  by simp


end
