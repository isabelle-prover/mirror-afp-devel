(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Proving Falling Factorial of a Sum with Combinatorics\<close>

theory Falling_Factorial_Sum_Combinatorics
imports
  "Discrete_Summation.Factorials"
  "Injectivity_Solver3"
begin

subsection \<open>Preliminaries\<close>

subsubsection \<open>Addition to List Theory\<close>

lemma finite_lists_distinct_length_eq [intro]:
  assumes "finite A"
  shows "finite {xs. length xs = n \<and> distinct xs \<and> set xs \<subseteq> A}" (is "finite ?S")
proof -
  have "finite {xs. set xs \<subseteq> A \<and> length xs = n}"
    using \<open>finite A\<close> by (rule finite_lists_length_eq)
  moreover have "?S \<subseteq> {xs. set xs \<subseteq> A \<and> length xs = n}" by auto
  ultimately show ?thesis using finite_subset by auto
qed

subsubsection \<open>Addition to Factorials Theory\<close>

(* TODO: what's the right class here? *)
lemma prod_ffact:
  fixes m :: "'a :: {ord, ring_1, comm_monoid_mult, comm_semiring_1_cancel}"
  shows "(\<Prod>i = 0..<n. m - of_nat i) = ffact n m"
proof -
  have "inj_on (\<lambda>j. j - 1) {1..n}" by (simp add: inj_on_diff_nat)
  moreover have "{0..<n} = (\<lambda>j. j - 1) ` {1..n}"
  proof -
    have "i \<in> (\<lambda>j. j - 1) ` {1..n}" if "i \<in> {0..<n}" for i
      using that by (auto intro: image_eqI[where x="i + 1"])
    from this show ?thesis by auto
  qed
  moreover have "m - of_nat (i - 1) = m + 1 - of_nat n + of_nat (n - i)" if "i \<in> {1..n}" for i
    using that by (simp add: of_nat_diff)
  ultimately have "(\<Prod>i = 0..<n. m - of_nat i) = (\<Prod>i = 1..n. m + 1 - of_nat n + of_nat (n - i))"
    by (rule prod.reindex_cong)
  from this show ?thesis
    unfolding ffact_def by (simp only: pochhammer_prod_rev)
qed

lemma prod_ffact_nat:
  fixes m :: nat
  shows "(\<Prod>i = 0..<n. m - i) = ffact n m"
proof cases
  assume "n \<le> m"
  have "inj_on (\<lambda>j. j - 1) {1..n}" by (simp add: inj_on_diff_nat)
  moreover have "{0..<n} = (\<lambda>j. j - 1) ` {1..n}"
  proof -
    have "i \<in> (\<lambda>j. j - 1) ` {1..n}" if "i \<in> {0..<n}" for i
      using that by (auto intro: image_eqI[where x="i + 1"])
    from this show ?thesis by auto
  qed
  ultimately have "(\<Prod>i = 0..<n. m - i) = (\<Prod>i = 1..n. (m + 1) - i)"
    by (auto intro: prod.reindex_cong[where l="\<lambda>i. i - 1"])
  from this \<open>n \<le> m\<close> show ?thesis
    unfolding ffact_def by (simp add: pochhammer_prod_rev)
next
  assume "\<not> n \<le> m"
  from this show ?thesis by (auto simp add: ffact_nat_triv)
qed

(* TODO: what's the right class here? *)
lemma prod_rev_ffact:
  fixes m :: "'a :: {ord, ring_1, comm_monoid_mult, comm_semiring_1_cancel}"
  shows "(\<Prod>i = 1..n. m - of_nat n + of_nat i) = ffact n m"
proof -
  have "inj_on (\<lambda>i. i + 1) {0..<n}" by simp
  moreover have "{1..n} = (\<lambda>i. i + 1) ` {0..<n}" by auto
  moreover have "m - of_nat n + of_nat (i + 1) = m + 1 - of_nat n + of_nat i" for i by simp
  ultimately have "(\<Prod>i = 1..n. m - of_nat n + of_nat i) = (\<Prod>i = 0..<n. m + 1 - of_nat n + of_nat i)"
    by (rule prod.reindex_cong[where l="\<lambda>i. i + 1"])
  from this show ?thesis
    unfolding ffact_def by (simp only: pochhammer_prod)
qed

lemma prod_rev_ffact_nat:
  fixes m :: nat
  assumes "n \<le> m"
  shows "(\<Prod>i = 1..n. m - n + i) = ffact n m"
proof -
  have "inj_on (\<lambda>i. i + 1) {0..<n}" by simp
  moreover have "{1..n} = (\<lambda>i. i + 1) ` {0..<n}" by auto
  moreover have "m - n + (i + 1) = m + 1 - n + i" for i
    using  \<open>n \<le> m\<close> by auto
  ultimately have "(\<Prod>i = 1..n. m - n + i) = (\<Prod>i = 0..<n. m + 1 - n + i)"
    by (rule prod.reindex_cong)
 from this show ?thesis
   unfolding ffact_def by (simp only: pochhammer_prod of_nat_id)
qed

lemma prod_rev_ffact_nat':
  fixes m :: nat
  assumes "n \<le> m"
  shows "\<Prod>{m - n + 1..m} = ffact n m"
proof -
  have "inj_on (\<lambda>i. m - n + i) {1::nat..n}" by (auto intro: inj_onI)
  moreover have "{m - n + 1..m} = (\<lambda>i. m - n + i) ` {1::nat..n}"
  proof -
    have "i \<in> (\<lambda>i. m + i - n) ` {Suc 0..n}" if "i \<in> {m - n + 1..m}" for i
      using that \<open>n \<le> m\<close> by (auto intro!: image_eqI[where x="i - (m - n)"])
    with \<open>n \<le> m\<close> show ?thesis by auto
  qed
  moreover have "m - n + i = m - n + i" for i ..
  ultimately have "\<Prod>{m - n + (1::nat)..m} = (\<Prod>i = 1..n. m - n + i)"
    by (rule prod.reindex_cong)
  from this show ?thesis
    using \<open>n \<le> m\<close> by (simp only: prod_rev_ffact_nat)
qed

lemma card_lists_distinct_length_eq:
  assumes "finite A"
  shows "card {xs. length xs = n \<and> distinct xs \<and> set xs \<subseteq> A} = ffact n (card A)"
proof cases
  assume "n \<le> card A"
  have "card {xs. length xs = n \<and> distinct xs \<and> set xs \<subseteq> A} = \<Prod>{card A - n + 1..card A}"
    using \<open>finite A\<close> \<open>n \<le> card A\<close> by (rule card_lists_distinct_length_eq)
  also have "\<dots> = ffact n (card A)"
    using \<open>n \<le> card A\<close> by (simp add: prod_rev_ffact_nat'[symmetric])
  finally show ?thesis .
next
  assume "\<not> n \<le> card A"
  from this \<open>finite A\<close> have "\<forall>xs. length xs = n \<and> distinct xs \<and> set xs \<subseteq> A \<longrightarrow> False"
    by (metis card_mono distinct_card)
  from this have eq_empty: "{xs. length xs = n \<and> distinct xs \<and> set xs \<subseteq> A} = {}"
    using \<open>finite A\<close> by auto
  from \<open>\<not> n \<le> card A\<close> show ?thesis
    by (simp add: ffact_nat_triv eq_empty)
qed

subsection \<open>Interleavings of Two Lists\<close>

inductive interleavings :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "interleavings [] ys ys"
| "interleavings xs [] xs"
| "interleavings xs ys zs \<Longrightarrow> interleavings (x#xs) ys (x#zs)"
| "interleavings xs ys zs \<Longrightarrow> interleavings xs (y#ys) (y#zs)"

lemma interleaving_Nil_implies_eq1:
  assumes "interleavings xs ys zs"
  assumes "xs = []"
  shows "ys = zs"
using assms by (induct rule: interleavings.induct) auto

lemma interleaving_Nil_iff1:
  "interleavings [] ys zs \<longleftrightarrow> (ys = zs)"
using interleaving_Nil_implies_eq1
by (auto simp add: interleavings.intros(1))

lemma interleaving_Nil_implies_eq2:
  assumes "interleavings xs ys zs"
  assumes "ys = []"
  shows "xs = zs"
using assms by (induct rule: interleavings.induct) auto

lemma interleaving_Nil_iff2:
  "interleavings xs [] zs \<longleftrightarrow> (xs = zs)"
using interleaving_Nil_implies_eq2
by (auto simp add: interleavings.intros(2))

lemma interleavings_Cons:
  "{zs. interleavings (x#xs) (y#ys) zs} =
    {x#zs|zs. interleavings xs (y#ys) zs} \<union> {y#zs|zs. interleavings (x#xs) ys zs}"
  (is "?S = ?expr")
proof
  show "?S \<subseteq> ?expr"
    by (auto elim: interleavings.cases)
next
  show "?expr \<subseteq> ?S"
    by (auto intro: interleavings.intros)
qed

lemma interleavings_filter:
  assumes "X \<inter> Y = {}" "set zs \<subseteq> X \<union> Y"
  shows "interleavings [z\<leftarrow>zs . z \<in> X] [z\<leftarrow>zs . z \<in> Y] zs"
using assms by (induct zs) (auto intro: interleavings.intros)

lemma interleavings_filter_eq1:
  assumes "interleavings xs ys zs"
  assumes "(\<forall>x\<in>set xs. P x) \<and> (\<forall>y\<in>set ys. \<not> P y)"
  shows "filter P zs = xs"
using assms by (induct rule: interleavings.induct) auto

lemma interleavings_filter_eq2:
  assumes "interleavings xs ys zs"
  assumes "(\<forall>x\<in>set xs. \<not> P x) \<and> (\<forall>y\<in>set ys. P y)"
  shows "filter P zs = ys"
using assms by (induct rule: interleavings.induct) auto

lemma interleavings_length:
  assumes "interleavings xs ys zs"
  shows "length xs + length ys = length zs"
using assms by (induct xs ys zs rule: interleavings.induct) auto

lemma interleavings_set:
  assumes "interleavings xs ys zs"
  shows "set xs \<union> set ys = set zs"
using assms by (induct xs ys zs rule: interleavings.induct) auto

lemma interleavings_distinct:
  assumes "interleavings xs ys zs"
  shows "distinct xs \<and> distinct ys \<and> set xs \<inter> set ys = {} \<longleftrightarrow> distinct zs"
using assms interleavings_set by (induct xs ys zs rule: interleavings.induct) fastforce+

lemma two_mutual_lists_induction:
  assumes "\<And>ys. P [] ys"
  assumes "\<And>xs. P xs []"
  assumes "\<And>x xs y ys. P xs (y#ys) \<Longrightarrow> P (x#xs) ys \<Longrightarrow> P (x#xs) (y#ys)"
  shows "P xs ys"
using assms by (induction_schema) (pat_completeness, lexicographic_order)

lemma finite_interleavings:
  "finite {zs. interleavings xs ys zs}"
proof (induct xs ys rule: two_mutual_lists_induction)
  case (1 ys)
  show ?case by (simp add: interleaving_Nil_iff1)
next
  case (2 xs)
  then show ?case by (simp add: interleaving_Nil_iff2)
next
  case (3 x xs y ys)
  then show ?case by (simp add: interleavings_Cons)
qed

lemma card_interleavings:
  assumes "set xs \<inter> set ys = {}"
  shows "card {zs. interleavings xs ys zs} = (length xs + length ys choose (length xs))"
using assms
proof (induct xs ys rule: two_mutual_lists_induction)
  case (1 ys)
  have "card {zs. interleavings [] ys zs} = card {ys}"
    by (simp add: interleaving_Nil_iff1)
  also have "\<dots> = (length [] + length ys choose (length []))" by simp
  finally show ?case .
next
  case (2 xs)
  have "card {zs. interleavings xs [] zs} = card {xs}"
    by (simp add: interleaving_Nil_iff2)
  also have "\<dots> = (length xs + length [] choose (length xs))" by simp
  finally show ?case .
next
  case (3 x xs y ys)
  have "card {zs. interleavings (x # xs) (y # ys) zs} =
    card ({x#zs|zs. interleavings xs (y#ys) zs} \<union> {y#zs|zs. interleavings (x#xs) ys zs})"
    by (simp add: interleavings_Cons)
  also have "\<dots> = card {x#zs|zs. interleavings xs (y#ys) zs} + card {y#zs|zs. interleavings (x#xs) ys zs}"
  proof -
    have "finite {x # zs |zs. interleavings xs (y # ys) zs}"
      by (simp add: finite_interleavings)
    moreover have "finite {y # zs |zs. interleavings (x # xs) ys zs}"
      by (simp add: finite_interleavings)
    moreover have "{x # zs |zs. interleavings xs (y # ys) zs} \<inter> {y # zs |zs. interleavings (x # xs) ys zs} = {}"
      using \<open>set (x # xs) \<inter> set (y # ys) = {}\<close> by auto
    ultimately show ?thesis by (simp add: card_Un_disjoint)
  qed
  also have "\<dots> = card ((\<lambda>zs. x # zs) ` {zs. interleavings xs (y # ys) zs}) +
    card ((\<lambda>zs. y # zs) ` {zs. interleavings (x#xs) ys zs})"
    by (simp add: setcompr_eq_image)
  also have "\<dots> = card {zs. interleavings xs (y # ys) zs} + card {zs. interleavings (x#xs) ys zs}"
    by (simp add: card_image)
  also have "\<dots> = (length xs + length (y # ys) choose length xs) + (length (x # xs) + length ys choose length (x # xs))"
    using 3 by simp
  also have "\<dots> = length (x # xs) + length (y # ys) choose length (x # xs)" by simp
  finally show ?case .
qed

subsection \<open>Cardinality of Distinct Fixed-Length Lists from a Union of Two Sets\<close>

lemma lists_distinct_union_by_interleavings:
  assumes "X \<inter> Y = {}"
  shows "{zs. length zs = n \<and> distinct zs \<and> set zs \<subseteq> X \<union> Y} = do {
    k \<leftarrow> {0..n};
    xs \<leftarrow> {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> X};
    ys \<leftarrow> {ys. length ys = n - k \<and> distinct ys \<and> set ys \<subseteq> Y};
    {zs. interleavings xs ys zs}
  }" (is "?S = ?expr")
proof
  show "?S \<subseteq> ?expr"
  proof
    fix zs
    assume "zs \<in> ?S"
    from this have "length zs = n" and "distinct zs" and "set zs \<subseteq> X \<union> Y" by auto
    define xs where "xs = filter (\<lambda>z. z \<in> X) zs"
    define ys where "ys = filter (\<lambda>z. z \<in> Y) zs"
    have eq: "[z\<leftarrow>zs . z \<in> Y] = [z\<leftarrow>zs . z \<notin> X]"
      using \<open>set zs \<subseteq> X \<union> Y\<close> \<open>X \<inter> Y = {}\<close>
      by (auto intro: filter_cong)
    have "length xs \<le> n \<and> distinct xs \<and> set xs \<subseteq> X"
      using \<open>length zs = n\<close> \<open>distinct zs\<close> unfolding xs_def by auto
    moreover have "length ys = n - length xs"
      using \<open>set zs \<subseteq> X \<union> Y\<close> \<open>length zs = n\<close>
      unfolding xs_def ys_def eq
      by (metis diff_add_inverse sum_length_filter_compl)
    moreover have "distinct ys \<and> set ys \<subseteq> Y"
      using \<open>distinct zs\<close> unfolding ys_def by auto
    moreover have "interleavings xs ys zs"
      using xs_def ys_def \<open>X \<inter> Y = {}\<close> \<open>set zs \<subseteq> X \<union> Y\<close>
      by (simp add: interleavings_filter)
    ultimately show "zs \<in> ?expr" by force
  qed
next
  show "?expr \<subseteq> ?S"
  proof
    fix zs
    assume "zs \<in> ?expr"
    from this obtain xs ys where "length xs \<le> n" "distinct xs" "set xs \<subseteq> X"
      and "length ys = n - length xs" "distinct ys" "set ys \<subseteq> Y" "interleavings xs ys zs" by auto
    have "length zs = n"
      using \<open>length xs \<le> n\<close> \<open>length ys = n - length xs\<close> \<open>interleavings xs ys zs\<close>
      using interleavings_length by force
    moreover have "distinct zs"
      using \<open>distinct xs\<close> \<open>distinct ys\<close> \<open>interleavings xs ys zs\<close> \<open>set xs \<subseteq> X\<close> \<open>set ys \<subseteq> Y\<close>
      using \<open>X \<inter> Y = {}\<close> interleavings_distinct by fastforce
    moreover have "set zs \<subseteq> X \<union> Y"
      using \<open>interleavings xs ys zs\<close> \<open>set xs \<subseteq> X\<close> \<open>set ys \<subseteq> Y\<close> interleavings_set by blast
    ultimately show "zs \<in> ?S" by blast
  qed
qed

lemma interleavings_inject:
  assumes "(set xs \<union> set xs') \<inter> (set ys \<union> set ys') = {}"
  assumes "interleavings xs ys zs" "interleavings xs' ys' zs'"
  assumes "zs = zs'"
  shows "xs = xs'" and "ys = ys'"
proof -
  have "xs = filter (\<lambda>z. z \<in> set xs \<union> set xs') zs"
    using \<open>(set xs \<union> set xs') \<inter> (set ys \<union> set ys') = {}\<close> \<open>interleavings xs ys zs\<close>
    by (auto intro: interleavings_filter_eq1[symmetric])
  also have "\<dots> = filter (\<lambda>z. z \<in> set xs \<union> set xs') zs'"
    using \<open>zs = zs'\<close> by simp
  also have "\<dots> = xs'"
    using \<open>(set xs \<union> set xs') \<inter> (set ys \<union> set ys') = {}\<close> \<open>interleavings xs' ys' zs'\<close>
    by (auto intro: interleavings_filter_eq1)
  finally show "xs = xs'" by simp
  have "ys = filter (\<lambda>z. z \<in> set ys \<union> set ys') zs"
    using \<open>(set xs \<union> set xs') \<inter> (set ys \<union> set ys') = {}\<close> \<open>interleavings xs ys zs\<close>
    by (auto intro: interleavings_filter_eq2[symmetric])
  also have "\<dots> = filter (\<lambda>z. z \<in> set ys \<union> set ys') zs'"
    using \<open>zs = zs'\<close> by simp
  also have "\<dots> = ys'"
    using \<open>(set xs \<union> set xs') \<inter> (set ys \<union> set ys') = {}\<close> \<open>interleavings xs' ys' zs'\<close>
    by (auto intro: interleavings_filter_eq2)
  finally show "ys = ys'" .
qed

lemma injectivity:
  assumes "X \<inter> Y = {}"
  assumes "k \<in> {0..n} \<and> k' \<in> {0..n}"
  assumes "(length xs = k \<and> distinct xs \<and> set xs \<subseteq> X) \<and> (length xs' = k' \<and> distinct xs' \<and> set xs' \<subseteq> X)"
  assumes "(length ys = n - k \<and> distinct ys \<and> set ys \<subseteq> Y) \<and> (length ys' = n - k' \<and> distinct ys' \<and> set ys' \<subseteq> Y)"
  assumes "interleavings xs ys zs \<and> interleavings xs' ys' zs'"
  assumes "zs = zs'"
  shows "k = k'" and "xs = xs'" and "ys = ys'"
proof -
  from assms(1,3,4) have "(set xs \<union> set xs') \<inter> (set ys \<union> set ys') = {}" by blast
  from this assms(5) \<open>zs = zs'\<close> show "xs = xs'" and "ys = ys'"
    using interleavings_inject by fastforce+
  from this assms(3) show "k = k'" by auto
qed

lemma card_lists_distinct_length_eq_union:
  assumes "finite X" "finite Y" "X \<inter> Y = {}"
  shows "card {zs. length zs = n \<and> distinct zs \<and> set zs \<subseteq> X \<union> Y} =
    (\<Sum>k=0..n. (n choose k) * ffact k (card X) * ffact (n - k) (card Y))"
  (is "card ?S = _")
proof -
  let ?expr = "do {
    k \<leftarrow> {0..n};
    xs \<leftarrow> {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> X};
    ys \<leftarrow> {ys. length ys = n - k \<and> distinct ys \<and> set ys \<subseteq> Y};
    {zs. interleavings xs ys zs}
  }"
  from \<open>X \<inter> Y = {}\<close> have "card ?S = card ?expr"
    by (simp add: lists_distinct_union_by_interleavings)
  let "?S \<bind> ?comp" = "?expr"
  {
    fix k
    assume "k \<in> ?S"
    let "?expr" = "?comp k"
    let "?S \<bind> ?comp" = "?expr"
    from \<open>finite X\<close> have "finite ?S" by auto
    moreover {
      fix xs
      assume xs: "xs \<in> ?S"
      let ?expr = "?comp xs"
      let "?S \<bind> ?comp" = ?expr
      from \<open>finite Y\<close> have "finite ?S" by auto
      moreover {
        fix ys
        assume ys: "ys \<in> ?S"
        let ?expr = "?comp ys"
        term ?expr
        have "finite ?expr"
          by (simp add: finite_interleavings)
        moreover have "card ?expr = (n choose k)"
          using xs ys \<open>X \<inter> Y = {}\<close> \<open>k \<in> _\<close>
          by (subst card_interleavings) auto
        ultimately have "finite ?expr \<and> card ?expr = (n choose k)" ..
      }
      moreover have "disjoint_family_on ?comp ?S"
        using \<open>k \<in> {0..n}\<close> \<open>xs \<in> {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> X}\<close>
        by (injectivity_solver rule: injectivity(3)[OF \<open>X \<inter> Y = {}\<close>])
      moreover have "card ?S = ffact (n - k) (card Y)"
        using \<open>finite Y\<close> by (simp add: card_lists_distinct_length_eq)
      ultimately have "card ?expr = (n choose k) * ffact (n - k) (card Y)"
        by (subst card_bind_constant) auto
      moreover have "finite ?expr"
        using \<open>finite ?S\<close> by (auto intro!: finite_bind finite_interleavings)
      ultimately have "finite ?expr \<and> card ?expr = (n choose k) * ffact (n - k) (card Y)"
        by blast
    }
    moreover have "disjoint_family_on ?comp ?S"
      using \<open>k \<in> {0..n}\<close>
      by (injectivity_solver rule: injectivity(2)[OF \<open>X \<inter> Y = {}\<close>])
    moreover have "card ?S = ffact k (card X)"
      using \<open>finite X\<close> by (simp add: card_lists_distinct_length_eq)
    ultimately have "card ?expr = (n choose k) * ffact k (card X) * ffact (n - k) (card Y)"
      by (subst card_bind_constant) auto
    moreover have "finite ?expr"
      using \<open>finite ?S\<close> \<open>finite Y\<close> by (auto intro!: finite_bind finite_interleavings)
    ultimately have "finite ?expr \<and> card ?expr = (n choose k) * ffact k (card X) * ffact (n - k) (card Y)"
      by blast
  }
  moreover have "disjoint_family_on ?comp ?S"
    by (injectivity_solver rule: injectivity(1)[OF \<open>X \<inter> Y = {}\<close>])
  ultimately have "card ?expr = (\<Sum>k=0..n. (n choose k) * ffact k (card X) * ffact (n - k) (card Y))"
    by (auto simp add: card_bind)
  from \<open>card _ = card ?expr\<close> this show ?thesis by simp
qed

lemma
  "ffact n (x + y) = (\<Sum>k=0..n. (n choose k) * ffact k x * ffact (n - k) y)"
proof -
  define X where "X = {..<x}"
  define Y where "Y = {x..<x+y}"
  have "finite X" and "card X = x" unfolding X_def by auto
  have "finite Y" and "card Y = y" unfolding Y_def by auto
  have "X \<inter> Y = {}" unfolding X_def Y_def by auto
  have "ffact n (x + y) = ffact n (card X + card Y)"
    using \<open>card X = x\<close> \<open>card Y = y\<close> by simp
  also have "\<dots> = ffact n (card (X \<union> Y))"
    using \<open>X \<inter> Y = {}\<close> \<open>finite X\<close> \<open>finite Y\<close> by (simp add: card_Un_disjoint)
  also have "\<dots> = card {xs. length xs = n \<and> distinct xs \<and> set xs \<subseteq> X \<union> Y}"
   using \<open>finite X\<close> \<open>finite Y\<close> by (simp add: card_lists_distinct_length_eq)
  also have "\<dots> = (\<Sum>k=0..n. (n choose k) * ffact k (card X) * ffact (n - k) (card Y))"
    using \<open>X \<inter> Y = {}\<close> \<open>finite X\<close> \<open>finite Y\<close> by (simp add: card_lists_distinct_length_eq_union)
  also have "\<dots> = (\<Sum>k=0..n. (n choose k) * ffact k x * ffact (n - k) y)"
    using \<open>card X = x\<close> \<open>card Y = y\<close> by simp
  finally show ?thesis .
qed

end