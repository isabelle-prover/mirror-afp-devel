\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Alignment With Binary Relation Definitions from HOL.Main\<close>
theory HOL_Alignment_Binary_Relations
  imports
    Main
    HOL_Mem_Of
    LBinary_Relations
begin

unbundle no relcomp_syntax and no converse_syntax

named_theorems HOL_bin_rel_alignment

paragraph \<open>Properties\<close>
subparagraph \<open>Antisymmetric\<close>

overloading
  antisymmetric_on_set \<equiv> "antisymmetric_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "antisymmetric_on_set (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _ \<equiv>
    antisymmetric_on (mem_of S)"
end

lemma antisymmetric_on_set_eq_antisymmetric_on_pred [simp]:
  "(antisymmetric_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = antisymmetric_on (mem_of S)"
  unfolding antisymmetric_on_set_def by simp

lemma antisymmetric_on_set_eq_antisymmetric_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "antisymmetric_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> antisymmetric_on P"
  using assms by simp

lemma antisymmetric_on_set_iff_antisymmetric_on_pred [iff]:
  "antisymmetric_on (S :: 'a set) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> antisymmetric_on (mem_of S) R"
  by simp

lemma antisymp_on_eq_antisymmetric_on [HOL_bin_rel_alignment]:
  "antisymp_on = antisymmetric_on"
  by (intro ext) (auto intro: antisymp_onI dest: antisymmetric_onD antisymp_onD)

lemma antisymp_eq_antisymmetric [HOL_bin_rel_alignment]:
  "antisymp = antisymmetric"
  by (intro ext) (auto intro: antisympI dest: antisymmetricD antisympD)

subparagraph \<open>Asymmetric\<close>

overloading
  asymmetric_on_set \<equiv> "asymmetric_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "asymmetric_on_set (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _ \<equiv> asymmetric_on (mem_of S)"
end

lemma asymmetric_on_set_eq_asymmetric_on_pred [simp]:
  "(asymmetric_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = asymmetric_on (mem_of S)"
  unfolding asymmetric_on_set_def by simp

lemma asymmetric_on_set_eq_asymmetric_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "asymmetric_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> asymmetric_on P"
  using assms by simp

lemma asymmetric_on_set_iff_asymmetric_on_pred [iff]:
  "asymmetric_on (S :: 'a set) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> asymmetric_on (mem_of S) R"
  by simp

lemma asymp_on_eq_asymmetric_on [HOL_bin_rel_alignment]: "asymp_on = asymmetric_on"
  by (intro ext) (auto dest: asymp_onD)

lemma asymp_eq_asymmetric [HOL_bin_rel_alignment]: "asymp = asymmetric"
  by (intro ext) (auto dest: asympD)

subparagraph \<open>Injective\<close>

overloading
  rel_injective_on_set \<equiv> "rel_injective_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  rel_injective_at_set \<equiv> "rel_injective_at :: 'a set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_injective_on_set (S :: 'a set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> _ \<equiv>
    rel_injective_on (mem_of S)"
  definition "rel_injective_at_set (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _ \<equiv>
    rel_injective_at (mem_of S)"
end

lemma rel_injective_on_set_eq_rel_injective_on_pred [simp]:
  "(rel_injective_on (S :: 'a set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) =
    rel_injective_on (mem_of S)"
  unfolding rel_injective_on_set_def by simp

lemma rel_injective_on_set_eq_rel_injective_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "rel_injective_on (S :: 'a set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv> rel_injective_on P"
  using assms by simp

lemma rel_injective_on_set_iff_rel_injective_on_pred [iff]:
  "rel_injective_on (S :: 'a set) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow> rel_injective_on (mem_of S) R"
  by simp

lemma rel_injective_at_set_eq_rel_injective_at_pred [simp]:
  "(rel_injective_at (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) =
    rel_injective_at (mem_of S)"
  unfolding rel_injective_at_set_def by simp

lemma rel_injective_at_set_eq_rel_injective_at_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "rel_injective_at (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> rel_injective_at P"
  using assms by simp

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
  definition "irreflexive_on_set (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    irreflexive_on (mem_of S)"
end

lemma irreflexive_on_set_eq_irreflexive_on_pred [simp]:
  "(irreflexive_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) =
    irreflexive_on (mem_of S)"
  unfolding irreflexive_on_set_def by simp

lemma irreflexive_on_set_eq_irreflexive_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "irreflexive_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> irreflexive_on P"
  using assms by simp

lemma irreflexive_on_set_iff_irreflexive_on_pred [iff]:
  "irreflexive_on (S :: 'a set) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> irreflexive_on (mem_of S) R"
  by simp

lemma irreflp_on_eq_irreflexive_on [HOL_bin_rel_alignment]: "irreflp_on = irreflexive_on"
  by (intro ext) (blast intro: irreflp_onI dest: irreflp_onD)

lemma irreflp_eq_irreflexive [HOL_bin_rel_alignment]: "irreflp = irreflexive"
  by (intro ext) (blast intro: irreflpI dest: irreflexiveD irreflpD)

subparagraph \<open>Left-Total\<close>

overloading
  left_total_on_set \<equiv> "left_total_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "left_total_on_set (S :: 'a set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> _ \<equiv>
    left_total_on (mem_of S)"
end

lemma left_total_on_set_eq_left_total_on_pred [simp]:
  "(left_total_on (S :: 'a set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) =
    left_total_on (mem_of S)"
  unfolding left_total_on_set_def by simp

lemma left_total_on_set_eq_left_total_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "left_total_on (S :: 'a set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv> left_total_on P"
  using assms by simp

lemma left_total_on_set_iff_left_total_on_pred [iff]:
  "left_total_on (S :: 'a set) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow> left_total_on (mem_of S) R"
  by simp

lemma Transfer_left_total_eq_left_total [HOL_bin_rel_alignment]:
  "Transfer.left_total = Binary_Relations_Left_Total.left_total"
  by (intro ext) (fast intro: Transfer.left_totalI
    elim: Transfer.left_totalE Binary_Relations_Left_Total.left_totalE)


subparagraph \<open>Reflexive\<close>

overloading
  reflexive_on_set \<equiv> "reflexive_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "reflexive_on_set (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _ \<equiv>
    reflexive_on (mem_of S)"
end

lemma reflexive_on_set_eq_reflexive_on_pred [simp]:
  "(reflexive_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = reflexive_on (mem_of S)"
  unfolding reflexive_on_set_def by simp

lemma reflexive_on_set_eq_reflexive_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "reflexive_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> reflexive_on P"
  using assms by simp

lemma reflexive_on_set_iff_reflexive_on_pred [iff]:
  "reflexive_on (S :: 'a set) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> reflexive_on (mem_of S) R"
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
  definition "right_unique_on_set (S :: 'a set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> _ \<equiv>
    right_unique_on (mem_of S)"
  definition "right_unique_at_set (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _ \<equiv>
    right_unique_at (mem_of S)"
end

lemma right_unique_on_set_eq_right_unique_on_pred [simp]:
  "(right_unique_on (S :: 'a set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) = right_unique_on (mem_of S)"
  unfolding right_unique_on_set_def by simp

lemma right_unique_on_set_eq_right_unique_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "right_unique_on (S :: 'a set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv> right_unique_on P"
  using assms by simp

lemma right_unique_on_set_iff_right_unique_on_pred [iff]:
  "right_unique_on (S :: 'a set) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow> right_unique_on (mem_of S) R"
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
  definition "rel_surjective_at_set (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _ \<equiv>
    rel_surjective_at (mem_of S)"
end

lemma rel_surjective_at_set_eq_rel_surjective_at_pred [simp]:
  "(rel_surjective_at (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = rel_surjective_at (mem_of S)"
  unfolding rel_surjective_at_set_def by simp

lemma rel_surjective_at_set_eq_rel_surjective_at_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "rel_surjective_at (S :: 'a set) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> rel_surjective_at P"
  using assms by simp

lemma rel_surjective_at_set_iff_rel_surjective_at_pred [iff]:
  "rel_surjective_at (S :: 'a set) (R :: 'b \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> rel_surjective_at (mem_of S) R"
  by simp

lemma Transfer_right_total_eq_rel_surjective [HOL_bin_rel_alignment]:
  "Transfer.right_total = rel_surjective"
  by (intro ext) (fast intro: Transfer.right_totalI rel_surjectiveI
    elim: Transfer.right_totalE rel_surjectiveE)


subparagraph \<open>Symmetric\<close>

overloading
  symmetric_on_set \<equiv> "symmetric_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "symmetric_on_set (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _ \<equiv>
    symmetric_on (mem_of S)"
end

lemma symmetric_on_set_eq_symmetric_on_pred [simp]:
  "(symmetric_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = symmetric_on (mem_of S)"
  unfolding symmetric_on_set_def by simp

lemma symmetric_on_set_eq_symmetric_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "symmetric_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> symmetric_on P"
  using assms by simp

lemma symmetric_on_set_iff_symmetric_on_pred [iff]:
  "symmetric_on (S :: 'a set) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> symmetric_on (mem_of S) R"
  by simp

lemma symp_on_eq_symmetric_on [HOL_bin_rel_alignment]: "symp_on = symmetric_on"
  by (intro ext) (blast intro: symp_onI dest: symmetric_onD symp_onD)

lemma symp_eq_symmetric [HOL_bin_rel_alignment]: "symp = symmetric"
  by (intro ext) (blast intro: sympI dest: symmetricD sympD)


subparagraph \<open>Transitive\<close>

overloading
  transitive_on_set \<equiv> "transitive_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "transitive_on_set (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _ \<equiv>
    transitive_on (mem_of S)"
end

lemma transitive_on_set_eq_transitive_on_pred [simp]:
  "(transitive_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = transitive_on (mem_of S)"
  unfolding transitive_on_set_def by simp

lemma transitive_on_set_eq_transitive_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "transitive_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> transitive_on P"
  using assms by simp

lemma transitive_on_set_iff_transitive_on_pred [iff]:
  "transitive_on (S :: 'a set) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> transitive_on (mem_of S) R"
  by simp

lemma transp_on_eq_transitive_on [HOL_bin_rel_alignment]: "transp_on = transitive_on"
  by (intro ext) (blast intro: transp_onI dest: transp_onD transitive_onD)

lemma transp_eq_transitive [HOL_bin_rel_alignment]: "transp = transitive"
  by (intro ext) (blast intro: transpI dest: transpD)

subparagraph \<open>Well-Founded\<close>

overloading
  wellfounded_on_set \<equiv> "wellfounded_on :: 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "wellfounded_on_set (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _ \<equiv> wellfounded_on (mem_of S)"
end

lemma wellfounded_on_set_eq_wellfounded_on_pred [simp]:
  "(wellfounded_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = wellfounded_on (mem_of S)"
  unfolding wellfounded_on_set_def by simp

lemma wellfounded_on_set_eq_wellfounded_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "wellfounded_on (S :: 'a set) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> wellfounded_on P"
  using assms by simp

lemma wellfounded_on_set_iff_wellfounded_on_pred [iff]:
  "wellfounded_on (S :: 'a set) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> wellfounded_on (mem_of S) R"
  by simp

lemma wfp_on_eq_wellfounded_on [HOL_bin_rel_alignment]: "wfp_on = wellfounded_on"
proof (urule (rr) ext iffI wellfounded_onI)
  fix A R Q x assume "wfp_on A R" and hyps: "mem_of A x" "Q x"
  then show "\<exists>m : mem_of A. Q m \<and> (\<forall>y : mem_of A. R y m \<longrightarrow> \<not> Q y)"
  by (induction rule: wfp_on_induct) (use hyps in auto)
next
  fix A :: "'a set" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" assume wf: "wellfounded_on A R"
  {
    fix P x assume hyps: "x \<in> A" "\<forall>x \<in> A. (\<forall>y \<in> A. R y x \<longrightarrow> P y) \<longrightarrow> P x"
    with wf have "P x"
    unfolding wellfounded_on_set_iff_wellfounded_on_pred
    by (induction rule: wellfounded_on_induct) (use hyps in blast)+
  }
  then show "wfp_on A R" unfolding wfp_on_def by blast
qed

lemma wfp_eq_wellfounded [HOL_bin_rel_alignment]: "wfp = wellfounded"
  by (urule fun_cong[OF wfp_on_eq_wellfounded_on])

subparagraph \<open>Bi-Total\<close>

lemma bi_total_on_set_eq_bi_total_on_pred [simp]:
  "(bi_total_on (S :: 'a set) (T :: 'b set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) =
    bi_total_on (mem_of S) (mem_of T)"
  by auto

lemma bi_total_on_set_eq_bi_total_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  and "Q \<equiv> mem_of T"
  shows "bi_total_on (S :: 'a set) (T :: 'b set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv> bi_total_on P Q"
  using assms by simp

lemma bi_total_on_set_iff_bi_total_on_pred [iff]:
  "bi_total_on (S :: 'a set) (T :: 'b set) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow>
    bi_total_on (mem_of S) (mem_of T) R"
  by simp

lemma Transfer_bi_total_eq_bi_total [HOL_bin_rel_alignment]:
  "Transfer.bi_total = Binary_Relations_Bi_Total.bi_total"
  unfolding bi_total_alt_def by (auto simp add: HOL_bin_rel_alignment)

subparagraph \<open>Bi-Unique\<close>

lemma bi_unique_on_set_eq_bi_unique_on_pred [simp]:
  "(bi_unique_on (S :: 'a set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) = bi_unique_on (mem_of S)"
  by auto

lemma bi_unique_on_set_eq_bi_unique_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "bi_unique_on (S :: 'a set) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv> bi_unique_on P"
  using assms by simp

lemma bi_unique_on_set_iff_bi_unique_on_pred [iff]:
  "bi_unique_on (S :: 'a set) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow> bi_unique_on (mem_of S) R"
  by simp

lemma Transfer_bi_unique_eq_bi_unique [HOL_bin_rel_alignment]:
  "Transfer.bi_unique = Binary_Relations_Bi_Unique.bi_unique"
  unfolding bi_unique_alt_def by (auto simp add: HOL_bin_rel_alignment)


paragraph \<open>Functions\<close>

lemma Domainp_eq_in_dom [HOL_bin_rel_alignment]: "Domainp = in_dom"
  by (intro ext) auto

lemma Rangep_eq_in_codom [HOL_bin_rel_alignment]: "Rangep = in_codom"
   by (intro ext) auto

lemma relcompp_eq_rel_comp [HOL_bin_rel_alignment]: "relcompp = rel_comp"
  by (intro ext) auto

lemma conversep_eq_rel_inv [HOL_bin_rel_alignment]: "conversep = rel_inv"
  by (intro ext) auto

lemma eq_onp_eq_eq_restrict [HOL_bin_rel_alignment]: "eq_onp = rel_restrict_left (=)"
  unfolding eq_onp_def by (intro ext) auto

definition "rel_restrict_left_set (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (S :: 'a set) \<equiv> R\<restriction>\<^bsub>mem_of S\<^esub>"
adhoc_overloading rel_restrict_left rel_restrict_left_set

definition "rel_restrict_right_set (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (S :: 'b set) \<equiv> R\<upharpoonleft>\<^bsub>mem_of S\<^esub>"
adhoc_overloading rel_restrict_right rel_restrict_right_set

definition "rel_restrict_set (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (S :: 'a set) \<equiv> R\<up>\<^bsub>mem_of S\<^esub>"
adhoc_overloading rel_restrict rel_restrict_set

lemma rel_restrict_left_set_eq_restrict_left_pred [simp]:
  "R\<restriction>\<^bsub>S\<^esub> = R\<restriction>\<^bsub>mem_of S\<^esub>"
  unfolding rel_restrict_left_set_def by simp

lemma rel_restrict_left_set_eq_restrict_left_pred_uhint [uhint]:
  assumes "R \<equiv> R'"
  and "P \<equiv> mem_of S"
  shows "R\<restriction>\<^bsub>S\<^esub> \<equiv> R'\<restriction>\<^bsub>P\<^esub>"
  using assms by simp

lemma rel_restrict_left_set_iff_restrict_left_pred [iff]: "R\<restriction>\<^bsub>S\<^esub> x y \<longleftrightarrow> R\<restriction>\<^bsub>mem_of S\<^esub> x y"
  by simp

lemma rel_restrict_right_set_eq_restrict_right_pred [simp]:
  "R\<upharpoonleft>\<^bsub>S\<^esub> = R\<upharpoonleft>\<^bsub>mem_of S\<^esub>"
  unfolding rel_restrict_right_set_def by simp

lemma rel_restrict_right_set_eq_restrict_right_pred_uhint [uhint]:
  assumes "R \<equiv> R'"
  and "P \<equiv> mem_of S"
  shows "R\<upharpoonleft>\<^bsub>S\<^esub> \<equiv> R'\<upharpoonleft>\<^bsub>P\<^esub>"
  using assms by simp

lemma rel_restrict_right_set_iff_restrict_right_pred [iff]: "R\<upharpoonleft>\<^bsub>S\<^esub> x y \<longleftrightarrow> R\<upharpoonleft>\<^bsub>mem_of S\<^esub> x y"
  by simp

lemma rel_restrict_set_eq_restrict_pred [simp]:
  "R\<up>\<^bsub>S\<^esub> = R\<up>\<^bsub>mem_of S\<^esub>"
  unfolding rel_restrict_set_def by simp

lemma rel_restrict_set_eq_restrict_pred_uhint [uhint]:
  assumes "R \<equiv> R'"
  and "P \<equiv> mem_of S"
  shows "R\<up>\<^bsub>S\<^esub> \<equiv> R'\<up>\<^bsub>P\<^esub>"
  using assms by simp

lemma rel_restrict_set_iff_restrict_pred [iff]: "R\<up>\<^bsub>S\<^esub> x y \<longleftrightarrow> R\<up>\<^bsub>mem_of S\<^esub> x y"
  by simp

end
