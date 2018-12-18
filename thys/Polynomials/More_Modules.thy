(* Author: Alexander Maletzky *)

theory More_Modules
  imports HOL.Modules
begin

text \<open>More facts about modules.\<close>

section \<open>Modules over Commutative Rings\<close>

context module
begin

lemma scale_minus_both [simp]: "(- a) *s (- x) = a *s x"
  by simp

subsection \<open>Submodules Spanned by Sets of Module-Elements\<close>

lemma span_insertI:
  assumes "p \<in> span B"
  shows "p \<in> span (insert r B)"
proof -
  have "B \<subseteq> insert r B" by blast
  hence "span B \<subseteq> span (insert r B)" by (rule span_mono)
  with assms show ?thesis ..
qed

lemma span_insertD:
  assumes "p \<in> span (insert r B)" and "r \<in> span B"
  shows "p \<in> span B"
  using assms(1)
proof (induct p rule: span_induct_alt)
  case base
  show "0 \<in> span B" by (fact span_zero)
next
  case step: (step q b a)
  from step(1) have "b = r \<or> b \<in> B" by simp
  thus "q *s b + a \<in> span B"
  proof
    assume eq: "b = r"
    from step(2) assms(2) show ?thesis unfolding eq by (intro span_add span_scale)
  next
    assume "b \<in> B"
    hence "b \<in> span B" using span_superset ..
    with step(2) show ?thesis by (intro span_add span_scale)
  qed
qed

lemma span_insert_idI:
  assumes "r \<in> span B"
  shows "span (insert r B) = span B"
proof (intro subset_antisym subsetI)
  fix p
  assume "p \<in> span (insert r B)"
  from this assms show "p \<in> span B" by (rule span_insertD)
next
  fix p
  assume "p \<in> span B"
  thus "p \<in> span (insert r B)" by (rule span_insertI)
qed

lemma span_insert_zero: "span (insert 0 B) = span B"
  using span_zero by (rule span_insert_idI)

lemma span_Diff_zero: "span (B - {0}) = span B"
  by (metis span_insert_zero insert_Diff_single)

lemma span_insert_subset:
  assumes "span A \<subseteq> span B" and "r \<in> span B"
  shows "span (insert r A) \<subseteq> span B"
proof
  fix p
  assume "p \<in> span (insert r A)"
  thus "p \<in> span B"
  proof (induct p rule: span_induct_alt)
    case base
    show ?case by (fact span_zero)
  next
    case step: (step q b a)
    show ?case
    proof (intro span_add span_scale)
      from \<open>b \<in> insert r A\<close> show "b \<in> span B"
      proof
        assume "b = r"
        thus "b \<in> span B" using assms(2) by simp
      next
        assume "b \<in> A"
        hence "b \<in> span A" using span_superset ..
        thus "b \<in> span B" using assms(1) ..
      qed
    qed fact
  qed
qed

lemma replace_span:
  assumes "q \<in> span B"
  shows "span (insert q (B - {p})) \<subseteq> span B"
  by (rule span_insert_subset, rule span_mono, fact Diff_subset, fact)

lemma sum_in_spanI: "(\<Sum>b\<in>B. q b *s b) \<in> span B"
  by (auto simp: intro: span_sum span_scale dest: span_base)

lemma spanE:
  assumes "p \<in> span B"
  obtains A q where "finite A" and "A \<subseteq> B" and "p = (\<Sum>b\<in>A. (q b) *s b)"
  using assms by (auto simp: span_explicit)

lemma span_finite_subset:
  assumes "p \<in> span B"
  obtains A where "finite A" and "A \<subseteq> B" and "p \<in> span A"
proof -
  from assms obtain A q where "finite A" and "A \<subseteq> B" and p: "p = (\<Sum>a\<in>A. q a *s a)"
    by (rule spanE)
  note this(1, 2)
  moreover have "p \<in> span A" unfolding p by (rule sum_in_spanI)
  ultimately show ?thesis ..
qed

lemma span_finiteE:
  assumes "finite B" and "p \<in> span B"
  obtains q where "p = (\<Sum>b\<in>B. (q b) *s b)"
  using assms by (auto simp: span_finite)

lemma span_subset_spanI:
  assumes "A \<subseteq> span B"
  shows "span A \<subseteq> span B"
  using assms subspace_span by (rule span_minimal)

lemma span_insert_cong:
  assumes "span A = span B"
  shows "span (insert p A) = span (insert p B)" (is "?l = ?r")
proof
  have 1: "span (insert p C1) \<subseteq> span (insert p C2)" if "span C1 = span C2" for C1 C2
  proof (rule span_subset_spanI)
    show "insert p C1 \<subseteq> span (insert p C2)"
    proof (rule insert_subsetI)
      show "p \<in> span (insert p C2)" by (rule span_base) simp
    next
      have "C1 \<subseteq> span C1" by (rule span_superset)
      also from that have "\<dots> = span C2" .
      also have "\<dots> \<subseteq> span (insert p C2)" by (rule span_mono) blast
      finally show "C1 \<subseteq> span (insert p C2)" .
    qed
  qed
  from assms show "?l \<subseteq> ?r" by (rule 1)
  from assms[symmetric] show "?r \<subseteq> ?l" by (rule 1)
qed

lemma span_induct' [consumes 1, case_names base step]:
  assumes "p \<in> span B" and "P 0"
    and "\<And>a q p. a \<in> span B \<Longrightarrow> P a \<Longrightarrow> p \<in> B \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> P (a + q *s p)"
  shows "P p"
  using assms(1, 1)
proof (induct p rule: span_induct_alt)
  case base
  from assms(2) show ?case .
next
  case (step q b a)
  from step.hyps(1) have "b \<in> span B" by (rule span_base)
  hence "q *s b \<in> span B" by (rule span_scale)
  with step.prems have "a \<in> span B" by (simp only: span_add_eq)
  hence "P a" by (rule step.hyps)
  show ?case
  proof (cases "q = 0")
    case True
    from \<open>P a\<close> show ?thesis by (simp add: True)
  next
    case False
    with \<open>a \<in> span B\<close> \<open>P a\<close> step.hyps(1) have "P (a + q *s b)" by (rule assms(3))
    thus ?thesis by (simp only: add.commute)
  qed
qed

lemma span_INT_subset: "span (\<Inter>a\<in>A. f a) \<subseteq> (\<Inter>a\<in>A. span (f a))" (is "?l \<subseteq> ?r")
proof
  fix p
  assume "p \<in> ?l"
  show "p \<in> ?r"
  proof
    fix a
    assume "a \<in> A"
    from \<open>p \<in> ?l\<close> show "p \<in> span (f a)"
    proof (induct p rule: span_induct')
      case base
      show ?case by (fact span_zero)
    next
      case (step p q b)
      from step(3) \<open>a \<in> A\<close> have "b \<in> f a" ..
      hence "b \<in> span (f a)" by (rule span_base)
      with step(2) show ?case by (intro span_add span_scale)
    qed
  qed
qed

lemma span_INT: "span (\<Inter>a\<in>A. span (f a)) = (\<Inter>a\<in>A. span (f a))" (is "?l = ?r")
proof
  have "?l \<subseteq> (\<Inter>a\<in>A. span (span (f a)))" by (rule span_INT_subset)
  also have "... = ?r" by (simp add: span_span)
  finally show "?l \<subseteq> ?r" .
qed (fact span_superset)

lemma span_Int_subset: "span (A \<inter> B) \<subseteq> span A \<inter> span B"
proof -
  have "span (A \<inter> B) = span (\<Inter>x\<in>{A, B}. x)" by simp
  also have "\<dots> \<subseteq> (\<Inter>x\<in>{A, B}. span x)" by (fact span_INT_subset)
  also have "\<dots> = span A \<inter> span B" by simp
  finally show ?thesis .
qed

lemma span_Int: "span (span A \<inter> span B) = span A \<inter> span B"
proof -
  have "span (span A \<inter> span B) = span (\<Inter>x\<in>{A, B}. span x)" by simp
  also have "\<dots> = (\<Inter>x\<in>{A, B}. span x)" by (fact span_INT)
  also have "\<dots> = span A \<inter> span B" by simp
  finally show ?thesis .
qed

lemma span_image_scale_eq_image_scale: "span ((*s) q ` F) = (*s) q ` span F" (is "?A = ?B")
proof (intro subset_antisym subsetI)
  fix p
  assume "p \<in> ?A"
  thus "p \<in> ?B"
  proof (induct p rule: span_induct')
    case base
    from span_zero show ?case by (rule rev_image_eqI) simp
  next
    case (step p r a)
    from step.hyps(2) obtain p' where "p' \<in> span F" and p: "p = q *s p'" ..
    from step.hyps(3) obtain a' where "a' \<in> F" and a: "a = q *s a'" ..
    from this(1) have "a' \<in> span F" by (rule span_base)
    hence "r *s a' \<in> span F" by (rule span_scale)
    with \<open>p' \<in> span F\<close> have "p' + r *s a' \<in> span F" by (rule span_add)
    hence "q *s (p' + r *s a') \<in> ?B" by (rule imageI)
    also have "q *s (p' + r *s a') = p + r *s a" by (simp add: a p algebra_simps)
    finally show ?case .
  qed
next
  fix p
  assume "p \<in> ?B"
  then obtain p' where "p' \<in> span F" and "p = q *s p'" ..
  from this(1) show "p \<in> ?A" unfolding \<open>p = q *s p'\<close>
  proof (induct p' rule: span_induct')
    case base
    show ?case by (simp add: span_zero)
  next
    case (step p r a)
    from step.hyps(3) have "q *s a \<in> (*s) q ` F" by (rule imageI)
    hence "q *s a \<in> ?A" by (rule span_base)
    hence "r *s (q *s a) \<in> ?A" by (rule span_scale)
    with step.hyps(2) have "q *s p + r *s (q *s a) \<in> ?A" by (rule span_add)
    also have "q *s p + r *s (q *s a) = q *s (p + r *s a)" by (simp add: algebra_simps)
    finally show ?case .
  qed
qed

end (* module *)

section \<open>Ideals over Commutative Rings\<close>

lemma module_times: "module (*)"
  by (standard, simp_all add: algebra_simps)

interpretation ideal: module times
  by (fact module_times)

declare ideal.scale_scale[simp del]

abbreviation "ideal \<equiv> ideal.span"

lemma ideal_eq_UNIV_iff_contains_one: "ideal B = UNIV \<longleftrightarrow> 1 \<in> ideal B"
proof
  assume *: "1 \<in> ideal B"
  show "ideal B = UNIV"
  proof
    show "UNIV \<subseteq> ideal B"
    proof
      fix x
      from * have "x * 1 \<in> ideal B" by (rule ideal.span_scale)
      thus "x \<in> ideal B" by simp
    qed
  qed simp
qed simp

end (* theory *)
