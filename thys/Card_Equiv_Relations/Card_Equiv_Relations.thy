(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section {* Cardinality of Equivalence Relations *}

theory Card_Equiv_Relations
imports
  "../Card_Partitions/Card_Partitions"
  "../Bell_Numbers_Spivey/Bell_Numbers"
  More_Set_Partition
begin

subsection {* Bijection between Equivalence Relations and Set Partitions *}

definition partition_of :: "('a \<times> 'a) set \<Rightarrow> 'a set set"
where
  "partition_of R = (UNIV // R) - {{}}"

definition equiv_relation_of :: "'a set set \<Rightarrow> ('a \<times> 'a) set"
where
  "equiv_relation_of P = {(x, y). \<exists>X\<in>P. x \<in> X \<and> y \<in> X}"

subsubsection {* Dedicated Facts for Bijection Proof *}

lemma equiv_equiv_relation_of:
  assumes "partition_on A P"
  shows "equiv A (equiv_relation_of P)"
proof (rule equivI)
  show "refl_on A (equiv_relation_of P)"
  proof (rule refl_onI)
    show "equiv_relation_of P \<subseteq> A \<times> A"
      unfolding equiv_relation_of_def
      using \<open>partition_on A P\<close> by (auto elim: partition_onE)
  next
    fix x
    assume "x \<in> A"
    from this show "(x, x) \<in> equiv_relation_of P"
      unfolding equiv_relation_of_def
      using \<open>partition_on A P\<close> by (auto elim!: partition_onE)
  qed
next
  show "sym (equiv_relation_of P)"
    unfolding equiv_relation_of_def by (auto intro: symI)
next
  show "trans (equiv_relation_of P)"
  proof (rule transI)
    fix x y z
    assume "(x, y) \<in> equiv_relation_of P" "(y, z) \<in> equiv_relation_of P"
    from this obtain X\<^sub>1 X\<^sub>2 where "X\<^sub>1 \<in> P" "X\<^sub>2 \<in> P"
      and "x \<in> X\<^sub>1" "y \<in> X\<^sub>1" and "y \<in> X\<^sub>2" "z \<in> X\<^sub>2"
      unfolding equiv_relation_of_def by auto
    from this have "X\<^sub>1 = X\<^sub>2"
      using \<open>partition_on A P\<close> partition_onE disjoint_iff_not_equal by blast
    from this show "(x, z) \<in> equiv_relation_of P"
      using \<open>x \<in> X\<^sub>1\<close> \<open>z \<in> X\<^sub>2\<close> \<open>X\<^sub>2 \<in> P\<close>
      unfolding equiv_relation_of_def by auto
  qed
qed

lemma partition_of_eq:
  assumes "equiv A R"
  shows "partition_of R = A // R"
proof
  show "partition_of R \<subseteq> A // R"
  proof
    fix X
    assume "X \<in> partition_of R"
    from this obtain x where "X = R `` {x}" and "X \<noteq> {}"
      unfolding partition_of_def by (auto elim!: quotientE)
    from this have "x \<in> A"
      using \<open>equiv A R\<close> equiv_class_eq_iff by fastforce
    from this \<open>X = R `` {x}\<close> show "X \<in> A // R"
      by (auto intro!: quotientI)
  qed
next
  show "A // R \<subseteq> partition_of R"
  proof
    fix X
    assume "X \<in> A // R"
    from this have "X \<noteq> {}"
      using \<open>equiv A R\<close> in_quotient_imp_non_empty by auto
    moreover from \<open>X \<in> A // R\<close> have "X \<in> UNIV // R"
      by (metis UNIV_I assms proj_Eps proj_preserves)
    ultimately show "X \<in> partition_of R"
      unfolding partition_of_def by simp
  qed
qed

lemma partition_on_partition_of:
  assumes "equiv A R"
  shows "partition_on A (partition_of R)"
proof (rule partition_onI)
  fix X
  assume "X \<in> partition_of R"
  from this show "X \<noteq> {}"
    unfolding partition_of_def by simp
next
  show "\<Union>partition_of R = A"
  proof
    show "\<Union>partition_of R \<subseteq> A"
      unfolding partition_of_def
      using \<open>equiv A R\<close>
      by (auto elim!: quotientE simp add: equiv_class_eq_iff)
  next
    show "A \<subseteq> \<Union>partition_of R"
    proof
      fix x
      assume "x \<in> A"
      from this have "x \<in> R `` {x}"
        using \<open>equiv A R\<close> by (meson equiv_class_self)
      moreover have "R `` {x} \<in> partition_of R"
        unfolding partition_of_eq[OF \<open>equiv A R\<close>]
        using \<open>x \<in> A\<close> by (auto intro!: quotientI)
      ultimately show "x \<in> \<Union>partition_of R" by auto
    qed
  qed
next
  fix X X'
  assume "X \<in> partition_of R" "X' \<in> partition_of R" "X \<noteq> X'"
  from this show "X \<inter> X' = {}"
    using partition_of_eq \<open>equiv A R\<close> quotient_disj by blast
qed

lemma equiv_relation_of_partition_of:
  assumes "equiv A R"
  shows "equiv_relation_of (partition_of R) = R"
proof
  show "equiv_relation_of (partition_of R) \<subseteq> R"
  proof
    fix xy
    assume "xy \<in> equiv_relation_of (partition_of R)"
    from this obtain x y and X where "xy = (x, y)"
      and "X \<in> partition_of R" and "x \<in> X" "y \<in> X"
      unfolding equiv_relation_of_def by auto
    from \<open>X \<in> partition_of R\<close> obtain z where "X = R `` {z}"
      unfolding partition_of_def by (auto elim: quotientE)
    show "xy \<in> R"
      using \<open>xy = (x, y)\<close> \<open>X = R `` {z}\<close> \<open>x \<in> X\<close> \<open>y \<in> X\<close> \<open>equiv A R\<close>
      by (simp add: equiv_class_eq_iff)
  qed
next
  show "R \<subseteq> equiv_relation_of (partition_of R)"
  proof
    fix xy
    assume "xy \<in> R"
    obtain x y where "xy = (x, y)" by fastforce
    from \<open>xy \<in> R\<close> have "(x, y) \<in> R"
      using \<open>xy = (x, y)\<close> by simp
    have "R `` {x} \<in> partition_of R"
      using \<open>equiv A R\<close> \<open>(x, y) \<in> R\<close>
      by (simp add: equiv_class_eq_iff partition_of_eq quotientI)
    moreover have "x \<in> R `` {x}"
      using \<open>(x, y) \<in> R\<close> \<open>equiv A R\<close>
      by (meson equiv_class_eq_iff equiv_class_self)
    moreover have "y \<in> R `` {x}"
      using \<open>(x, y) \<in> R\<close> \<open>equiv A R\<close> by simp
    ultimately have "(x, y) \<in> equiv_relation_of (partition_of R)"
      unfolding equiv_relation_of_def by auto
    from this show "xy \<in> equiv_relation_of (partition_of R)"
      using \<open>xy = (x, y)\<close> by simp
  qed
qed

lemma partition_of_equiv_relation_of:
  assumes "partition_on A P"
  shows "partition_of (equiv_relation_of P) = P"
proof
  show "partition_of (equiv_relation_of P) \<subseteq> P"
  proof
    fix X
    assume X: "X \<in> partition_of (equiv_relation_of P)"
    from this have "X \<noteq> {}"
      unfolding partition_of_def by auto
    from X obtain x where "X = equiv_relation_of P `` {x}"
      unfolding partition_of_def by (auto elim: quotientE)
    from this have X_eq: "X = {y. \<exists>X\<in>P. x \<in> X \<and> y \<in> X}"
      unfolding equiv_relation_of_def by auto
    from X_eq \<open>X \<noteq> {}\<close> \<open>partition_on A P\<close> have "x \<in> A"
      using partition_on_no_partition_outside_carrier by force
    from X_eq \<open>partition_on A P\<close> \<open>x \<in> A\<close> show "X \<in> P"
      using the_unique_part_alternative_def partition_on_the_part_mem by force
  qed
next
  show "P \<subseteq> partition_of (equiv_relation_of P)"
  proof
    fix X
    assume "X \<in> P"
    from \<open>X \<in> P\<close> have "X \<noteq> {}"
      using \<open>partition_on A P\<close> partition_onE by auto
    from this obtain x where "x \<in> X" by auto
    have "X = {(x, y). \<exists>X\<in>P. x \<in> X \<and> y \<in> X} `` {x}"
      using \<open>partition_on A P\<close> \<open>x \<in> X\<close> \<open>X \<in> P\<close> partition_on_part_characteristic by fastforce
    from \<open>X \<noteq> {}\<close> this show "X \<in> partition_of (equiv_relation_of P)"
      unfolding partition_of_def equiv_relation_of_def
      by (auto intro!: quotientI simp only:)
  qed
qed

lemma equiv_relation_of_eq:
  assumes "partition_on A P"
  shows "(A // equiv_relation_of P) = P"
using assms partition_of_eq partition_of_equiv_relation_of
  equiv_equiv_relation_of by force

subsubsection {* Bijection Proof *}

lemma bij_betw_partition_of:
  "bij_betw partition_of {R. equiv A R} {P. partition_on A P}"
proof (rule bij_betw_byWitness[where f'="equiv_relation_of"])
 show "\<forall>R\<in>{R. equiv A R}. equiv_relation_of (partition_of R) = R"
   by (simp add: equiv_relation_of_partition_of)
 show "\<forall>P\<in>{P. partition_on A P}. partition_of (equiv_relation_of P) = P"
   by (simp add: partition_of_equiv_relation_of)
 show "partition_of ` {R. equiv A R} \<subseteq> {P. partition_on A P}"
   using partition_on_partition_of by auto
 show "equiv_relation_of ` {P. partition_on A P} \<subseteq> {R. equiv A R}"
   using equiv_equiv_relation_of by auto
qed

lemma bij_betw_partition_of_equiv_with_k_classes:
  "bij_betw partition_of {R. equiv A R \<and> card (A // R) = k} {P. partition_on A P \<and> card P = k}"
proof (rule bij_betw_byWitness[where f'="equiv_relation_of"])
 show "\<forall>R\<in>{R. equiv A R \<and> card (A // R) = k}. equiv_relation_of (partition_of R) = R"
   by (auto simp add: equiv_relation_of_partition_of)
 show "\<forall>P\<in>{P. partition_on A P \<and> card P = k}. partition_of (equiv_relation_of P) = P"
   by (auto simp add: partition_of_equiv_relation_of)
 show "partition_of ` {R. equiv A R \<and> card (A // R) = k} \<subseteq> {P. partition_on A P \<and> card P = k}"
   using partition_on_partition_of by (auto simp add: partition_of_eq)
 show "equiv_relation_of ` {P. partition_on A P \<and> card P = k} \<subseteq> {R. equiv A R \<and> card (A // R) = k}"
   using equiv_equiv_relation_of by (auto simp add: equiv_relation_of_eq)
qed

subsection {* Finiteness of Equivalence Relations *}

lemma finite_equiv:
  assumes "finite A"
  shows "finite {R. equiv A R}"
proof -
  have "bij_betw partition_of {R. equiv A R} {P. partition_on A P}"
    by (rule bij_betw_partition_of)
  from this show "finite {R. equiv A R}"
    using \<open>finite A\<close> finitely_many_partition_on by (simp add: bij_betw_finite)
qed

subsection {* Cardinality of Equivalence Relations *}

theorem card_equiv_rel_eq_card_partitions:
  "card {R. equiv A R} = card {P. partition_on A P}"
proof -
  have "bij_betw partition_of {R. equiv A R} {P. partition_on A P}"
    by (rule bij_betw_partition_of)
  from this show "card {R. equiv A R} = card {P. partition_on A P}"
    by (rule bij_betw_same_card)
qed

corollary card_equiv_rel_eq_Bell:
  assumes "finite A"
  shows "card {R. equiv A R} = Bell (card A)"
using assms Bell_altdef card_equiv_rel_eq_card_partitions by force

corollary card_equiv_rel_eq_sum_Stirling:
  assumes "finite A"
  shows "card {R. equiv A R} = setsum (Stirling (card A)) {..card A}"
using assms card_equiv_rel_eq_Bell Bell_Stirling_eq by simp

theorem card_equiv_k_classes_eq_card_partitions_k_parts:
  "card {R. equiv A R \<and> card (A // R) = k} = card {P. partition_on A P \<and> card P = k}"
proof -
  have "bij_betw partition_of {R. equiv A R \<and> card (A // R) = k} {P. partition_on A P \<and> card P = k}"
    by (rule bij_betw_partition_of_equiv_with_k_classes)
  from this show "card {R. equiv A R \<and> card (A // R) = k} = card {P. partition_on A P \<and> card P = k}"
    by (rule bij_betw_same_card)
qed

corollary
  assumes "finite A"
  shows "card {R. equiv A R \<and> card (A // R) = k} = Stirling (card A) k"
using card_equiv_k_classes_eq_card_partitions_k_parts
  card_partition_on[OF \<open>finite A\<close>] by metis

end
