theory Missing_Multiset
imports Main "~~/src/HOL/Library/Multiset" "~~/src/HOL/Library/Disjoint_Sets"
begin

lemma image_mset_If:
  "image_mset (\<lambda>x. if P x then f x else g x) A = 
     image_mset f (filter_mset P A) + image_mset g (filter_mset (\<lambda>x. \<not>P x) A)"
  by (induction A) (auto simp: add_ac)

lemma mset_set_Union: 
  "finite A \<Longrightarrow> finite B \<Longrightarrow> A \<inter> B = {} \<Longrightarrow> mset_set (A \<union> B) = mset_set A + mset_set B"
  by (induction A rule: finite_induct) (auto simp: add_ac)

lemma filter_mset_mset_set [simp]:
  "finite A \<Longrightarrow> filter_mset P (mset_set A) = mset_set {x\<in>A. P x}"
proof (induction A rule: finite_induct)
  case (insert x A)
  from insert.hyps have "filter_mset P (mset_set (insert x A)) = 
      filter_mset P (mset_set A) + mset_set (if P x then {x} else {})"
    by (simp add: add_ac)
  also have "filter_mset P (mset_set A) = mset_set {x\<in>A. P x}"
    by (rule insert.IH)
  also from insert.hyps 
    have "\<dots> + mset_set (if P x then {x} else {}) =
            mset_set ({x \<in> A. P x} \<union> (if P x then {x} else {}))" (is "_ = mset_set ?A")
     by (intro mset_set_Union [symmetric]) simp_all
  also from insert.hyps have "?A = {y\<in>insert x A. P y}" by auto
  finally show ?case .
qed simp_all

lemma image_mset_Diff: 
  assumes "B \<subseteq># A"
  shows   "image_mset f (A - B) = image_mset f A - image_mset f B"
proof -
  have "image_mset f (A - B + B) = image_mset f (A - B) + image_mset f B"
    by simp
  also from assms have "A - B + B = A"
    by (simp add: subset_mset.diff_add) 
  finally show ?thesis by simp
qed

lemma mset_set_Diff:
  assumes "finite A" "B \<subseteq> A"
  shows  "mset_set (A - B) = mset_set A - mset_set B"
proof -
  from assms have "mset_set ((A - B) \<union> B) = mset_set (A - B) + mset_set B"
    by (intro mset_set_Union) (auto dest: finite_subset)
  also from assms have "A - B \<union> B = A" by blast
  finally show ?thesis by simp
qed

lemma bij_betw_UNION_disjoint:
  assumes disj: "disjoint_family_on A' I"
  assumes bij: "\<And>i. i \<in> I \<Longrightarrow> bij_betw f (A i) (A' i)"
  shows   "bij_betw f (\<Union>i\<in>I. A i) (\<Union>i\<in>I. A' i)"
unfolding bij_betw_def
proof
  from bij show eq: "f ` UNION I A = UNION I A'"
    by (auto simp: bij_betw_def image_UN)
  show "inj_on f (UNION I A)"
  proof (rule inj_onI, clarify)
    fix i j x y assume A: "i \<in> I" "j \<in> I" "x \<in> A i" "y \<in> A j" and B: "f x = f y"
    from A bij[of i] bij[of j] have "f x \<in> A' i" "f y \<in> A' j"
      by (auto simp: bij_betw_def)
    with B have "A' i \<inter> A' j \<noteq> {}" by auto
    with disj A have "i = j" unfolding disjoint_family_on_def by blast
    with A B bij[of i] show "x = y" by (auto simp: bij_betw_def dest: inj_onD)
  qed
qed

lemma mset_set_empty_iff: "mset_set A = {#} \<longleftrightarrow> A = {} \<or> infinite A"
  using finite_set_mset_mset_set by fastforce
  
lemma size_mset_set [simp]: "size (mset_set A) = card A"
  by (simp only: size_eq_msetsum card_eq_setsum setsum_unfold_msetsum)  

lemma count_image_mset: 
  "count (image_mset f A) x = (\<Sum>y\<in>f -` {x} \<inter> set_mset A. count A y)"
  by (induction A)
     (auto simp: setsum.distrib setsum.delta' intro!: setsum.mono_neutral_left)

end