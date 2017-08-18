(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section {* Set Partitions *}

theory Set_Partition
imports
  "HOL-Library.FuncSet"
  Card_Partitions.Card_Partitions
begin

subsection {* Useful Additions to Main Theories *}

lemma set_eqI':
  assumes "\<And>x. x \<in> A \<Longrightarrow> x \<in> B"
  assumes "\<And>x. x \<in> B \<Longrightarrow> x \<in> A"
  shows "A = B"
using assms by auto

lemma comp_image:
  "(op ` f \<circ> op ` g) = op ` (f o g)"
by rule auto

subsection {* Introduction and Elimination Rules *}

text {* The definition of @{const partition_on} is in @{theory Disjoint_Sets}. *}

(* TODO: move the following theorems to Disjoint_Sets *)

lemma partition_onI:
  assumes "\<And>p. p \<in> P \<Longrightarrow> p \<noteq> {}"
  assumes "\<Union>P = A"
  assumes "\<And>p p'. p \<in> P \<Longrightarrow> p' \<in> P \<Longrightarrow> p \<noteq> p' \<Longrightarrow> p \<inter> p' = {}"
  shows "partition_on A P"
using assms unfolding partition_on_def disjoint_def by blast

lemma partition_onE:
  assumes "partition_on A P"
  obtains "\<And>p. p \<in> P \<Longrightarrow> p \<noteq> {}"
     "\<Union>P = A"
     "\<And>p p'. p \<in> P \<Longrightarrow> p' \<in> P \<Longrightarrow> p \<noteq> p' \<Longrightarrow> p \<inter> p' = {}"
using assms unfolding partition_on_def disjoint_def by blast

subsection {* Basic Facts on Set Partitions *}

lemma partition_on_notemptyI:
  assumes "partition_on A P"
  assumes "A \<noteq> {}"
  shows "P \<noteq> {}"
using assms by (auto elim: partition_onE)

lemma partition_on_disjoint:
  assumes "partition_on A P"
  assumes "partition_on B Q"
  assumes "A \<inter> B = {}"
  shows "P \<inter> Q = {}"
using assms by (fastforce elim: partition_onE)

lemma partition_on_eq_implies_eq_carrier:
  assumes "partition_on A Q"
  assumes "partition_on B Q"
  shows "A = B"
using assms by (fastforce elim: partition_onE)

text \<open>An alternative formulation of @{thm partition_on_insert}\<close>
lemma partition_on_insert':
  assumes "partition_on (A - X) P"
  assumes "X \<subseteq> A" "X \<noteq> {}"
  shows "partition_on A (insert X P)"
proof -
  have "disjnt (A - X) X" by (simp add: disjnt_iff)
  from assms(1) this assms(3) have "partition_on ((A - X) \<union> X) (insert X P)"
    by (rule partition_on_insert)
  from this \<open>X \<subseteq> A\<close> show ?thesis
    by (metis Diff_partition sup_commute)
qed

subsection {* The Unique Part Containing an Element in a Set Partition *}

lemma partition_on_partition_on_unique:
  assumes "partition_on A P"
  assumes "x \<in> A"
  shows "\<exists>!X. x \<in> X \<and> X \<in> P"
proof -
  from \<open>partition_on A P\<close> have "\<Union>P = A"
    by (auto elim: partition_onE)
  from this \<open>x \<in> A\<close> obtain X where X: "x \<in> X \<and> X \<in> P" by blast
  {
    fix Y
    assume "x \<in> Y \<and> Y \<in> P"
    from this have "X = Y"
      using X \<open>partition_on A P\<close> by (meson partition_onE disjoint_iff_not_equal)
  }
  from this X show ?thesis by auto
qed

lemma partition_on_the_part_mem:
  assumes "partition_on A P"
  assumes "x \<in> A"
  shows "(THE X. x \<in> X \<and> X \<in> P) \<in> P"
proof -
  from \<open>x \<in> A\<close> have "\<exists>!X. x \<in> X \<and> X \<in> P"
    using \<open>partition_on A P\<close> by (simp add: partition_on_partition_on_unique)
  from this show "(THE X. x \<in> X \<and> X \<in> P) \<in> P"
    by (metis (no_types, lifting) theI)
qed

lemma partition_on_in_the_unique_part:
  assumes "partition_on A P"
  assumes "x \<in> A"
  shows "x \<in> (THE X. x \<in> X \<and> X \<in> P)"
proof -
  from assms have "\<exists>!X. x \<in> X \<and> X \<in> P"
    by (simp add: partition_on_partition_on_unique)
  from this show ?thesis
    by (metis (mono_tags, lifting) theI')
qed

lemma partition_on_the_part_eq:
  assumes "partition_on A P"
  assumes "x \<in> X" "X \<in> P"
  shows "(THE X. x \<in> X \<and> X \<in> P) = X"
proof -
  from \<open>x \<in> X\<close> \<open>X \<in> P\<close> have "x \<in> A"
    using \<open>partition_on A P\<close> by (auto elim: partition_onE)
  from this have "\<exists>!X. x \<in> X \<and> X \<in> P"
    using \<open>partition_on A P\<close> by (simp add: partition_on_partition_on_unique)
  from \<open>x \<in> X\<close> \<open>X \<in> P\<close> this show "(THE X. x \<in> X \<and> X \<in> P) = X"
    by (auto intro!: the1_equality)
qed

lemma partition_on_all_in_part_eq_part:
  assumes "partition_on A P"
  assumes "X' \<in> P"
  shows "{x \<in> A. (THE X. x \<in> X \<and> X \<in> P) = X'} = X'"
proof
  show "{x \<in> A. (THE X. x \<in> X \<and> X \<in> P) = X'} \<subseteq> X'"
    using assms(1) partition_on_in_the_unique_part by force
next
  show "X' \<subseteq> {x \<in> A. (THE X. x \<in> X \<and> X \<in> P) = X'}"
  proof
    fix x
    assume "x \<in> X'"
    from \<open>x \<in> X'\<close> \<open>X' \<in> P\<close> have "x \<in> A"
      using \<open>partition_on A P\<close> by (auto elim: partition_onE)
    moreover from \<open>x \<in> X'\<close> \<open>X' \<in> P\<close> have "(THE X. x \<in> X \<and> X \<in> P) = X'"
      using \<open>partition_on A P\<close> partition_on_the_part_eq by fastforce
    ultimately show "x \<in> {x \<in> A. (THE X. x \<in> X \<and> X \<in> P) = X'}" by auto
  qed
qed

subsection {* Cardinality of Parts in a Set Partition *}

lemma partition_on_le_set_elements:
  assumes "finite A"
  assumes "partition_on A P"
  shows "card P \<le> card A"
using assms
proof (induct A arbitrary: P)
  case empty
  from this show "card P \<le> card {}" by (simp add: partition_on_empty)
next
  case (insert a A)
  show ?case
  proof (cases "{a} \<in> P")
    case True
    have prop_partition_on: "\<forall>p\<in>P. p \<noteq> {}" "\<Union>P = insert a A"
      "\<forall>p\<in>P. \<forall>p'\<in>P. p \<noteq> p' \<longrightarrow> p \<inter> p' = {}"
      using \<open>partition_on (insert a A) P\<close> by (fastforce elim: partition_onE)+
    from this(2, 3) \<open>a \<notin> A\<close> \<open>{a} \<in> P\<close> have A_eq: "A = \<Union>(P - {{a}})"
      by auto (metis Int_iff UnionI empty_iff insert_iff)
    from prop_partition_on A_eq have partition_on: "partition_on A (P - {{a}})"
      by (intro partition_onI) auto
    from insert.hyps(3) this have "card (P - {{a}}) \<le> card A" by simp
    from this insert(1, 2, 4) \<open>{a} \<in> P\<close> show ?thesis
      using finite_elements[OF \<open>finite A\<close> partition_on] by simp
  next
    case False
    from \<open>partition_on (insert a A) P\<close> obtain p where p_def: "p \<in> P" "a \<in> p"
      by (blast elim: partition_onE)
    from \<open>partition_on (insert a A) P\<close> p_def have a_notmem: "\<forall>p'\<in> P - {p}. a \<notin> p'"
      by (blast elim: partition_onE)
    from \<open>partition_on (insert a A) P\<close> p_def have "p - {a} \<notin> P"
      unfolding partition_on_def disjoint_def
      by (metis Diff_insert_absorb Diff_subset inf.orderE mk_disjoint_insert)
    let ?P' = "insert (p - {a}) (P - {p})"
    have "partition_on A ?P'"
    proof (rule partition_onI)
      from \<open>partition_on (insert a A) P\<close> have "\<forall>p\<in>P. p \<noteq> {}" by (auto elim: partition_onE)
      from this p_def \<open>{a} \<notin> P\<close> show "\<And>p'. p'\<in>insert (p - {a}) (P - {p}) \<Longrightarrow> p' \<noteq> {}"
        by (simp; metis (no_types) Diff_eq_empty_iff subset_singletonD)
    next
      from \<open>partition_on (insert a A) P\<close> have "\<Union>P = insert a A" by (auto elim: partition_onE)
      from p_def this \<open>a \<notin> A\<close> a_notmem show "\<Union>insert (p - {a}) (P - {p}) = A" by auto
    next
      show "\<And>pa pa'. pa\<in>insert (p - {a}) (P - {p}) \<Longrightarrow> pa'\<in>insert (p - {a}) (P - {p}) \<Longrightarrow> pa \<noteq> pa' \<Longrightarrow> pa \<inter> pa' = {}"
        using \<open>partition_on (insert a A) P\<close> p_def a_notmem
        unfolding partition_on_def disjoint_def
        by (metis disjoint_iff_not_equal insert_Diff insert_iff)
    qed
    have "finite P" using \<open>finite A\<close> \<open>partition_on A ?P'\<close> finite_elements by fastforce
    have "card P = Suc (card (P - {p}))"
      using p_def \<open>finite P\<close> card.remove by fastforce
    also have "\<dots> = card ?P'" using \<open>p - {a} \<notin> P\<close> \<open>finite P\<close> by simp
    also have "\<dots> \<le> card A" using \<open>partition_on A ?P'\<close> insert.hyps(3) by simp
    also have "\<dots> \<le> card (insert a A)" by (simp add: card_insert_le \<open>finite A\<close> )
    finally show ?thesis .
  qed
qed

subsection {* Operations on Set Partitions *}

lemma partition_on_union:
  assumes "A \<inter> B = {}"
  assumes "partition_on A P"
  assumes "partition_on B Q"
  shows "partition_on (A \<union> B) (P \<union> Q)"
proof (rule partition_onI)
  fix X
  assume "X \<in> P \<union> Q"
  from this \<open>partition_on A P\<close> \<open>partition_on B Q\<close> show "X \<noteq> {}"
    by (auto elim: partition_onE)
next
  show "\<Union>(P \<union> Q) = A \<union> B"
    using \<open>partition_on A P\<close> \<open>partition_on B Q\<close> by (auto elim: partition_onE)
next
  fix X Y
  assume "X \<in> P \<union> Q" "Y \<in> P \<union> Q" "X \<noteq> Y"
  from this assms show "X \<inter> Y = {}"
    by (elim UnE partition_onE) auto
qed

lemma partition_on_split1:
  assumes "partition_on A (P \<union> Q)"
  shows "partition_on (\<Union>P) P"
proof (rule partition_onI)
  fix p
  assume "p \<in> P"
  from this assms show "p \<noteq> {}"
    using Un_iff partition_onE by auto
next
  show "\<Union>P = \<Union>P" ..
next
  fix p p'
  assume a: "p \<in> P" "p' \<in> P" "p \<noteq> p'"
  from this assms show "p \<inter> p' = {}"
    using partition_onE subsetCE sup_ge1 by blast
qed

lemma partition_on_split2:
  assumes "partition_on A (P \<union> Q)"
  shows "partition_on (\<Union>Q) Q"
using assms partition_on_split1 sup_commute by metis

lemma partition_on_intersect_on_elements:
  assumes "partition_on (A \<union> C) P"
  assumes "\<forall>X \<in> P. \<exists>x. x \<in> X \<inter> C"
  shows "partition_on C ((\<lambda>X. X \<inter> C) ` P)"
proof (rule partition_onI)
  fix p
  assume "p \<in> (\<lambda>X. X \<inter> C) ` P"
  from this assms show "p \<noteq> {}" by auto
next
  have "\<Union>P = A \<union> C"
    using assms by (auto elim: partition_onE)
  from this show "\<Union>((\<lambda>X. X \<inter> C) ` P) = C" by auto
next
  fix p p'
  assume "p \<in> (\<lambda>X. X \<inter> C) ` P" "p' \<in> (\<lambda>X. X \<inter> C) ` P" "p \<noteq> p'"
  from this assms(1) show "p \<inter> p' = {}"
    by (blast elim: partition_onE)
qed

lemma partition_on_insert_elements:
  assumes "A \<inter> B = {}"
  assumes "partition_on B P"
  assumes "f \<in> A \<rightarrow>\<^sub>E P"
  shows "partition_on (A \<union> B) ((\<lambda>X. X \<union> {x \<in> A. f x = X}) ` P)" (is "partition_on _ ?P")
proof (rule partition_onI)
  fix X
  assume "X \<in> ?P"
  from this \<open>partition_on B P\<close> show "X \<noteq> {}"
    by (auto elim: partition_onE)
next
  show "\<Union>?P = A \<union> B"
    using \<open>partition_on B P\<close> \<open>f \<in> A \<rightarrow>\<^sub>E P\<close> by (auto elim: partition_onE)
next
  fix X Y
  assume "X \<in> ?P" "Y \<in> ?P" "X \<noteq> Y"
  from \<open>X \<in> ?P\<close> obtain X' where X': "X = X' \<union> {x \<in> A. f x = X'}" "X' \<in> P" by auto
  from \<open>Y \<in> ?P\<close> obtain Y' where Y': "Y = Y' \<union> {x \<in> A. f x = Y'}" "Y' \<in> P" by auto
  from \<open>X \<noteq> Y\<close> X' Y' have "X' \<noteq> Y'" by auto
  from this X' Y' have "X' \<inter> Y' = {}"
    using \<open>partition_on B P\<close> by (auto elim!: partition_onE)
  from X' Y' have "X' \<subseteq> B" "Y' \<subseteq> B"
    using \<open>partition_on B P\<close> by (auto elim!: partition_onE)
  from this \<open>X' \<inter> Y' = {}\<close> X' Y' \<open>X' \<noteq> Y'\<close> show "X \<inter> Y = {}"
    using \<open>A \<inter> B = {}\<close> by auto
qed

lemma partition_on_map:
  assumes "inj_on f A"
  assumes "partition_on A P"
  shows "partition_on (f ` A) (op ` f ` P)"
proof -
  {
    fix X Y
    assume "X \<in> P" "Y \<in> P" "f ` X \<noteq> f ` Y"
    moreover from assms have "\<forall>p\<in>P. \<forall>p'\<in>P. p \<noteq> p' \<longrightarrow> p \<inter> p' = {}" and "inj_on f (\<Union>P)"
      by (auto elim!: partition_onE)
    ultimately have "f ` X \<inter> f ` Y = {}"
      unfolding inj_on_def by auto (metis IntI empty_iff rev_image_eqI)+
  }
  from assms this show "partition_on (f ` A) (op ` f ` P)"
    by (auto intro!: partition_onI elim!: partition_onE)
qed

lemma set_of_partition_on_map:
  assumes "inj_on f A"
  shows "op ` (op ` f) ` {P. partition_on A P} = {P. partition_on (f ` A) P}"
proof (rule set_eqI')
  fix x
  assume "x \<in> op ` (op ` f) ` {P. partition_on A P}"
  from this \<open>inj_on f A\<close> show "x \<in> {P. partition_on (f ` A) P}"
    by (auto intro: partition_on_map)
next
  fix P
  assume "P \<in> {P. partition_on (f ` A) P}"
  from this have "partition_on (f ` A) P" by auto
  from this have mem: "\<And>X x. X \<in> P \<Longrightarrow> x \<in> X \<Longrightarrow> x \<in> f ` A"
    by (auto elim!: partition_onE)
  have "op ` (f \<circ> the_inv_into A f) ` P = op ` f ` op ` (the_inv_into A f) ` P"
    by (simp add: image_comp comp_image)
  moreover have "P = op ` (f \<circ> the_inv_into A f) ` P"
  proof (rule set_eqI')
    fix X
    assume X: "X \<in> P"
    moreover from X mem have in_range: "\<forall>x\<in>X. x \<in> f ` A" by auto
    moreover have "X = (f \<circ> the_inv_into A f) ` X"
    proof (rule set_eqI')
      fix x
      assume "x \<in> X"
      show "x \<in> (f \<circ> the_inv_into A f) ` X"
      proof (rule image_eqI)
        from in_range \<open>x \<in> X\<close> assms show "x = (f \<circ> the_inv_into A f) x"
          by (auto simp add: f_the_inv_into_f[of f])
        from \<open>x \<in> X\<close> show "x \<in> X" by assumption
      qed
    next
      fix x
      assume "x \<in> (f \<circ> the_inv_into A f) ` X"
      from this obtain x' where x': "x' \<in> X \<and> x = f (the_inv_into A f x')" by auto
      from in_range x' have f: "f (the_inv_into A f x') \<in> X"
        by (subst f_the_inv_into_f[of f]) (auto intro: \<open>inj_on f A\<close>)
      from x' \<open>X \<in> P\<close> f show "x \<in> X" by auto
    qed
    ultimately show "X \<in> op ` (f \<circ> the_inv_into A f) ` P" by auto
  next
    fix X
    assume "X \<in> op ` (f \<circ> the_inv_into A f) ` P"
    moreover
    {
      fix Y
      assume "Y \<in> P"
      from this \<open>inj_on f A\<close> mem have "\<forall>x\<in>Y. f (the_inv_into A f x) = x"
        by (auto simp add: f_the_inv_into_f)
      from this have "(f \<circ> the_inv_into A f) ` Y = Y" by force
    }
    ultimately show "X \<in> P" by auto
  qed
  ultimately have P: "P = op ` f ` op ` (the_inv_into A f) ` P" by simp
  have A_eq: "A = the_inv_into A f ` f ` A" by (simp add: assms)
  from \<open>inj_on f A\<close> have "inj_on (the_inv_into A f) (f ` A)"
    using \<open>partition_on (f ` A) P\<close> by (simp add: inj_on_the_inv_into)
  from this have  "op ` (the_inv_into A f) ` P \<in> {P. partition_on A P}"
    using \<open>partition_on (f ` A) P\<close> by (subst A_eq, auto intro!: partition_on_map)
  from P this show "P \<in> op ` (op ` f) ` {P. partition_on A P}" by (rule image_eqI)
qed

end
