(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section {* Set Partitions *}

theory Set_Partition
imports
  "~~/src/HOL/Library/FuncSet"
  "../Card_Partitions/Card_Partitions"
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

text {* The definition of partitions is in the Card\_Partitions theory. *}

lemma partitionsI:
  assumes "\<And>p. p \<in> P \<Longrightarrow> p \<noteq> {}"
  assumes "\<Union>P = A"
  assumes "\<And>p p'. p \<in> P \<Longrightarrow> p' \<in> P \<Longrightarrow> p \<noteq> p' \<Longrightarrow> p \<inter> p' = {}"
  shows "partitions P A"
using assms unfolding partitions_def by blast

lemma partitionsE:
  assumes "partitions P A"
  obtains "\<And>p. p \<in> P \<Longrightarrow> p \<noteq> {}"
     "\<Union>P = A"
     "\<And>p p'. p \<in> P \<Longrightarrow> p' \<in> P \<Longrightarrow> p \<noteq> p' \<Longrightarrow> p \<inter> p' = {}"
using assms unfolding partitions_def by blast

subsection {* Basic Facts on Set Partitions *}

lemma partitions_notemptyI:
  assumes "partitions P A"
  assumes "A \<noteq> {}"
  shows "P \<noteq> {}"
using assms by (auto elim: partitionsE)

lemma partitions_disjoint:
  assumes "partitions P A"
  assumes "partitions Q B"
  assumes "A \<inter> B = {}"
  shows "P \<inter> Q = {}"
using assms by (fastforce elim: partitionsE)

lemma partitions_eq_implies_eq_carrier:
  assumes "partitions Q A"
  assumes "partitions Q B"
  shows "A = B"
using assms by (fastforce elim: partitionsE)

subsection {* The Unique Part Containing an Element in a Set Partition *}

lemma partitions_partitions_unique:
  assumes "partitions P A"
  assumes "x \<in> A"
  shows "\<exists>!X. x \<in> X \<and> X \<in> P"
proof -
  from \<open>partitions P A\<close> have "\<Union>P = A"
    by (auto elim: partitionsE)
  from this \<open>x \<in> A\<close> obtain X where X: "x \<in> X \<and> X \<in> P" by blast
  {
    fix Y
    assume "x \<in> Y \<and> Y \<in> P"
    from this have "X = Y"
      using X \<open>partitions P A\<close> by (meson partitionsE disjoint_iff_not_equal)
  }
  from this X show ?thesis by auto
qed

lemma partitions_the_part_mem:
  assumes "partitions P A"
  assumes "x \<in> A"
  shows "(THE X. x \<in> X \<and> X \<in> P) \<in> P"
proof -
  from \<open>x \<in> A\<close> have "\<exists>!X. x \<in> X \<and> X \<in> P"
    using \<open>partitions P A\<close> by (simp add: partitions_partitions_unique)
  from this show "(THE X. x \<in> X \<and> X \<in> P) \<in> P"
    by (metis (no_types, lifting) theI)
qed

lemma partitions_the_part_eq:
  assumes "partitions P A"
  assumes "x \<in> X" "X \<in> P"
  shows "(THE X. x \<in> X \<and> X \<in> P) = X"
proof -
  from \<open>x \<in> X\<close> \<open>X \<in> P\<close> have "x \<in> A"
    using \<open>partitions P A\<close> by (auto elim: partitionsE)
  from this have "\<exists>!X. x \<in> X \<and> X \<in> P"
    using \<open>partitions P A\<close> by (simp add: partitions_partitions_unique)
  from \<open>x \<in> X\<close> \<open>X \<in> P\<close> this show "(THE X. x \<in> X \<and> X \<in> P) = X"
    by (auto intro!: the1_equality)
qed

subsection {* Cardinality of Parts in a Set Partition *}

lemma partitions_le_set_elements:
  assumes "finite A"
  assumes "partitions P A"
  shows "card P \<le> card A"
using assms
proof (induct A arbitrary: P)
  case empty
  from this show "card P \<le> card {}" by (simp add: partitions_empty)
next
  case (insert a A)
  show ?case
  proof (cases "{a} \<in> P")
    case True
    have prop_partitions: "\<forall>p\<in>P. p \<noteq> {}" "\<Union>P = insert a A"
      "\<forall>p\<in>P. \<forall>p'\<in>P. p \<noteq> p' \<longrightarrow> p \<inter> p' = {}"
      using \<open>partitions P (insert a A)\<close> by (fastforce elim: partitionsE)+
    from this(2, 3) \<open>a \<notin> A\<close> \<open>{a} \<in> P\<close> have A_eq: "A = \<Union>(P - {{a}})"
      by auto (metis Int_iff UnionI empty_iff insert_iff)
    from prop_partitions A_eq have partitions: "partitions (P - {{a}}) A"
      by (intro partitionsI) auto
    from insert.hyps(3) this have "card (P - {{a}}) \<le> card A" by simp
    from this insert(1, 2, 4) \<open>{a} \<in> P\<close> show ?thesis
      using finite_elements[OF \<open>finite A\<close> partitions] by simp
  next
    case False
    from \<open>partitions P (insert a A)\<close> obtain p where p_def: "p \<in> P" "a \<in> p"
      by (blast elim: partitionsE)
    from \<open>partitions P (insert a A)\<close> p_def have a_notmem: "\<forall>p'\<in> P - {p}. a \<notin> p'"
      by (blast elim: partitionsE)
    from \<open>partitions P (insert a A)\<close> p_def have "p - {a} \<notin> P"
      unfolding partitions_def
      by (metis Diff_insert_absorb Diff_subset inf.orderE mk_disjoint_insert)
    let ?P' = "insert (p - {a}) (P - {p})"
    have "partitions ?P' A"
    proof (rule partitionsI)
      from \<open>partitions P (insert a A)\<close> have "\<forall>p\<in>P. p \<noteq> {}" by (auto elim: partitionsE)
      from this p_def \<open>{a} \<notin> P\<close> show "\<And>p'. p'\<in>insert (p - {a}) (P - {p}) \<Longrightarrow> p' \<noteq> {}"
        by (simp; metis (no_types) Diff_eq_empty_iff subset_singletonD)
    next
      from \<open>partitions P (insert a A)\<close> have "\<Union>P = insert a A" by (auto elim: partitionsE)
      from p_def this \<open>a \<notin> A\<close> a_notmem show "\<Union>insert (p - {a}) (P - {p}) = A" by auto
    next
      show "\<And>pa pa'. pa\<in>insert (p - {a}) (P - {p}) \<Longrightarrow> pa'\<in>insert (p - {a}) (P - {p}) \<Longrightarrow> pa \<noteq> pa' \<Longrightarrow> pa \<inter> pa' = {}"
        using \<open>partitions P (insert a A)\<close> p_def a_notmem
        unfolding partitions_def by (metis disjoint_iff_not_equal insert_Diff insert_iff)
    qed
    have "finite P" using \<open>finite A\<close> \<open>partitions ?P' A\<close> finite_elements by fastforce
    have "card P = Suc (card (P - {p}))"
      using p_def \<open>finite P\<close> card.remove by fastforce
    also have "\<dots> = card ?P'" using \<open>p - {a} \<notin> P\<close> \<open>finite P\<close> by simp
    also have "\<dots> \<le> card A" using \<open>partitions ?P' A\<close> insert.hyps(3) by simp
    also have "\<dots> \<le> card (insert a A)" by (simp add: card_insert_le \<open>finite A\<close> )
    finally show ?thesis .
  qed
qed

subsection {* Operations on Set Partitions *}

lemma partitions_union:
  assumes "A \<inter> B = {}"
  assumes "partitions P A"
  assumes "partitions Q B"
  shows "partitions (P \<union> Q) (A \<union> B)"
proof (rule partitionsI)
  fix X
  assume "X \<in> P \<union> Q"
  from this \<open>partitions P A\<close> \<open>partitions Q B\<close> show "X \<noteq> {}"
    by (auto elim: partitionsE)
next
  show "\<Union>(P \<union> Q) = A \<union> B"
    using \<open>partitions P A\<close> \<open>partitions Q B\<close> by (auto elim: partitionsE)
next
  fix X Y
  assume "X \<in> P \<union> Q" "Y \<in> P \<union> Q" "X \<noteq> Y"
  from this assms show "X \<inter> Y = {}"
    by (elim UnE partitionsE) auto
qed

lemma partitions_split1:
  assumes "partitions (P \<union> Q) A"
  shows "partitions P (\<Union>P)"
proof (rule partitionsI)
  fix p
  assume "p \<in> P"
  from this assms show "p \<noteq> {}"
    using Un_iff partitionsE by auto
next
  show "\<Union>P = \<Union>P" ..
next
  fix p p'
  assume a: "p \<in> P" "p' \<in> P" "p \<noteq> p'"
  from this assms show "p \<inter> p' = {}"
    using partitionsE subsetCE sup_ge1 by blast
qed

lemma partitions_split2:
  assumes "partitions (P \<union> Q) A"
  shows "partitions Q (\<Union>Q)"
using assms partitions_split1 sup_commute by metis

lemma partitions_intersect_on_elements:
  assumes "partitions P (A \<union> C)"
  assumes "\<forall>X \<in> P. \<exists>x. x \<in> X \<inter> C"
  shows "partitions ((\<lambda>X. X \<inter> C) ` P) C"
proof (rule partitionsI)
  fix p
  assume "p \<in> (\<lambda>X. X \<inter> C) ` P"
  from this assms show "p \<noteq> {}" by auto
next
  have "\<Union>P = A \<union> C"
    using assms by (auto elim: partitionsE)
  from this show "\<Union>((\<lambda>X. X \<inter> C) ` P) = C" by auto
next
  fix p p'
  assume "p \<in> (\<lambda>X. X \<inter> C) ` P" "p' \<in> (\<lambda>X. X \<inter> C) ` P" "p \<noteq> p'"
  from this assms(1) show "p \<inter> p' = {}"
    by (blast elim: partitionsE)
qed

lemma partitions_insert_elements:
  assumes "A \<inter> B = {}"
  assumes "partitions P B"
  assumes "f \<in> A \<rightarrow>\<^sub>E P"
  shows "partitions ((\<lambda>X. X \<union> {x \<in> A. f x = X}) ` P) (A \<union> B)" (is "partitions ?P _")
proof (rule partitionsI)
  fix X
  assume "X \<in> ?P"
  from this \<open>partitions P B\<close> show "X \<noteq> {}"
    by (auto elim: partitionsE)
next
  show "\<Union>?P = A \<union> B"
    using \<open>partitions P B\<close> \<open>f \<in> A \<rightarrow>\<^sub>E P\<close> by (auto elim: partitionsE)
next
  fix X Y
  assume "X \<in> ?P" "Y \<in> ?P" "X \<noteq> Y"
  from \<open>X \<in> ?P\<close> obtain X' where X': "X = X' \<union> {x \<in> A. f x = X'}" "X' \<in> P" by auto
  from \<open>Y \<in> ?P\<close> obtain Y' where Y': "Y = Y' \<union> {x \<in> A. f x = Y'}" "Y' \<in> P" by auto
  from \<open>X \<noteq> Y\<close> X' Y' have "X' \<noteq> Y'" by auto
  from this X' Y' have "X' \<inter> Y' = {}"
    using \<open>partitions P B\<close> by (auto elim!: partitionsE)
  from X' Y' have "X' \<subseteq> B" "Y' \<subseteq> B"
    using \<open>partitions P B\<close> by (auto elim!: partitionsE)
  from this \<open>X' \<inter> Y' = {}\<close> X' Y' \<open>X' \<noteq> Y'\<close> show "X \<inter> Y = {}"
    using \<open>A \<inter> B = {}\<close> by auto
qed

lemma partitions_map:
  assumes "inj_on f A"
  assumes "partitions P A"
  shows "partitions (op ` f ` P) (f ` A)"
proof -
  {
    fix X Y
    assume "X \<in> P" "Y \<in> P" "f ` X \<noteq> f ` Y"
    moreover from assms have "\<forall>p\<in>P. \<forall>p'\<in>P. p \<noteq> p' \<longrightarrow> p \<inter> p' = {}" and "inj_on f (\<Union>P)"
      by (auto elim!: partitionsE)
    ultimately have "f ` X \<inter> f ` Y = {}"
      unfolding inj_on_def by auto (metis IntI empty_iff rev_image_eqI)+
  }
  from assms this show "partitions (op ` f ` P) (f ` A)"
    by (auto intro!: partitionsI elim!: partitionsE)
qed

lemma set_of_partitions_map:
  assumes "inj_on f A"
  shows "op ` (op ` f) ` {P. partitions P A} = {P. partitions P (f ` A)}"
proof (rule set_eqI')
  fix x
  assume "x \<in> op ` (op ` f) ` {P. partitions P A}"
  from this \<open>inj_on f A\<close> show "x \<in> {P. partitions P (f ` A)}"
    by (auto intro: partitions_map)
next
  fix P
  assume "P \<in> {P. partitions P (f ` A)}"
  from this have "partitions P (f ` A)" by auto
  from this have mem: "\<And>X x. X \<in> P \<Longrightarrow> x \<in> X \<Longrightarrow> x \<in> f ` A"
    by (auto elim!: partitionsE)
  have "op ` (f \<circ> the_inv_into A f) ` P = op ` f ` op ` (the_inv_into A f) ` P"
    by (simp add: image_comp comp_image)
  moreover have "P = op ` (f \<circ> the_inv_into A f) ` P"
  proof (rule set_eqI')
    fix X
    assume "X \<in> P"
    moreover from this mem have in_range: "\<forall>x\<in>X. x \<in> f ` A" by auto
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
    using \<open>partitions P (f ` A)\<close> by (simp add: inj_on_the_inv_into)
  from this have  "op ` (the_inv_into A f) ` P \<in> {P. partitions P A}"
    using \<open>partitions P (f ` A)\<close> by (subst A_eq, auto intro!: partitions_map)
  from P this show "P \<in> op ` (op ` f) ` {P. partitions P A}" by (rule image_eqI)
qed

end
