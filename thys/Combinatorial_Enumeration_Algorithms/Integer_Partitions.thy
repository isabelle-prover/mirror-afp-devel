section "Integer Paritions"

theory Integer_Partitions
  imports
    "HOL-Library.Multiset"
    Common_Lemmas
    Card_Number_Partitions.Card_Number_Partitions
begin

subsection"Definition"

definition integer_partitions :: "nat \<Rightarrow> nat multiset set" where
  "integer_partitions i = {A. sum_mset A = i \<and> 0 \<notin># A}"
text \<open>Cardinality: \<open>Partition i\<close> (from \<open>Card_Number_Partitions.Card_Number_Partitions\<close> \cite{AFPnumpat})\<close>
text "Example: \<open>integer_partitions 4 = {{4}, {3,1}, {2,2} {2,1,1}, {1,1,1,1}}\<close>"

subsection"Algorithm"

fun integer_partitions_enum_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat list list" where
  "integer_partitions_enum_aux 0 m = [[]]"
| "integer_partitions_enum_aux n m =
  [h#r . h \<leftarrow> [1..< Suc (min n m)], r \<leftarrow> integer_partitions_enum_aux (n-h) h]"

fun integer_partitions_enum :: "nat \<Rightarrow> nat list list" where
 "integer_partitions_enum n = integer_partitions_enum_aux n n"

subsection"Verification"

subsubsection"Correctness"

lemma integer_partitions_empty: "[] \<in> set (integer_partitions_enum_aux n m) \<Longrightarrow> n = 0"
  by(induct n) auto

lemma integer_partitions_enum_aux_first:
  "x # xs \<in> set (integer_partitions_enum_aux n m)
    \<Longrightarrow> xs \<in> set (integer_partitions_enum_aux (n-x) x)"
  by(induct n) auto

lemma integer_partitions_enum_aux_max_n:
  "x#xs \<in> set (integer_partitions_enum_aux n m) \<Longrightarrow> x \<le> n"
  by (induct n) auto

lemma integer_partitions_enum_aux_max_head:
  "x#xs \<in> set (integer_partitions_enum_aux n m) \<Longrightarrow> x \<le> m"
  by (induct n) auto

(*not used, but nice to have nonetheless*)
lemma integer_partitions_enum_aux_max:
  "xs \<in> set (integer_partitions_enum_aux n m) \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<le> m"
proof(induct xs arbitrary: n m x)
  case Nil
  then show ?case using integer_partitions_enum_aux_max_head by simp
next
  case (Cons y xs)
  then show ?case 
    using integer_partitions_enum_aux_max_head integer_partitions_enum_aux_first  
    by fastforce                                         
qed

lemma integer_partitions_enum_aux_sum:
  "xs \<in> set (integer_partitions_enum_aux n m) \<Longrightarrow> sum_list xs = n"
proof(induct xs arbitrary: n m)
  case Nil
  then show ?case using integer_partitions_empty by simp
next
  case (Cons x xs)
  then have "\<lbrakk>xs \<in> set (integer_partitions_enum_aux (n-x) x)\<rbrakk> \<Longrightarrow> sum_list xs = (n-x)"
    by simp
  moreover have "xs \<in> set (integer_partitions_enum_aux (n-x) x)"
    using Cons integer_partitions_enum_aux_first by simp
  moreover have "x \<le> n"
    using Cons integer_partitions_enum_aux_max_n by simp
  ultimately show ?case
    by simp
qed

lemma integer_partitions_enum_aux_not_null_aux:
  "x#xs \<in> set (integer_partitions_enum_aux n m) \<Longrightarrow> x \<noteq> 0"
  by (induct n) auto

lemma integer_partitions_enum_aux_not_null:
  "xs \<in> set (integer_partitions_enum_aux n m) \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<noteq> 0"
proof(induct xs arbitrary: x n m)
  case Nil
  then show ?case by simp
next
  case (Cons y xs)
  show ?case proof(cases "y = x")
    case True
    then show ?thesis
      using Cons integer_partitions_enum_aux_not_null_aux by simp 
  next
    case False
    then show ?thesis
       using Cons integer_partitions_enum_aux_not_null_aux integer_partitions_enum_aux_first
       by fastforce
  qed
qed

lemma integer_partitions_enum_aux_head_minus:
     "h \<le> m \<Longrightarrow> h > 0 \<Longrightarrow> n \<ge> h \<Longrightarrow>
  ys \<in> set (integer_partitions_enum_aux (n-h) h)\<Longrightarrow> h#ys \<in> set (integer_partitions_enum_aux n m)"
proof(induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have 1: "1 \<le> m" by simp

  have 2: "(\<exists>x. (x = min (Suc n) m \<or> Suc 0 \<le> x \<and> x < Suc n \<and> x < m) \<and> h # ys
      \<in> (#) x ` set (integer_partitions_enum_aux (Suc n - x) x))"
    unfolding image_def using Suc by auto

  from 1 2 have "Suc 0 \<le> m \<and>(\<exists>x. (x = min (Suc n) m \<or> Suc 0 \<le> x \<and> x < Suc n \<and> x < m)
         \<and> h # ys \<in> (#) x ` set (integer_partitions_enum_aux (Suc n - x) x))"
    by simp
    
  then show ?case by auto
qed

lemma integer_partitions_enum_aux_head_plus:
  "h \<le> m \<Longrightarrow> h > 0 \<Longrightarrow> ys \<in> set (integer_partitions_enum_aux n h)
    \<Longrightarrow> h#ys \<in> set (integer_partitions_enum_aux (h + n) m)"
  using integer_partitions_enum_aux_head_minus by simp 

lemma integer_partitions_enum_correct_aux1:
  assumes "0 \<notin># A "
  and "\<forall>x \<in># A. x \<le> m"
shows" \<exists>xs\<in>set (integer_partitions_enum_aux (\<Sum>\<^sub># A) m). A = mset xs"
using assms proof(induct A arbitrary: m rule: multiset_induct_max)
  case empty
  then show ?case by simp
next
  case (add h A)
  have hc1: "h \<le> m"
    using add by simp

  have hc2: "h > 0"
    using add by simp

  obtain ys where o1: "ys \<in> set (integer_partitions_enum_aux (\<Sum>\<^sub># A) h)" and o2: " A = mset ys"
    using add by force

  have "h#ys \<in> set (integer_partitions_enum_aux (h + \<Sum>\<^sub># A) m)"
    using integer_partitions_enum_aux_head_plus hc1 o1 hc2 by blast 

  then show ?case
    using o2 by force
qed

theorem integer_partitions_enum_correct:
  "set (map mset (integer_partitions_enum n)) = integer_partitions n"
proof(standard)
  have "\<lbrakk>xs \<in> set (integer_partitions_enum_aux n n)\<rbrakk> \<Longrightarrow> \<Sum>\<^sub># (mset xs) = n" for xs
    by (simp add: integer_partitions_enum_aux_sum sum_mset_sum_list)
  moreover have "xs \<in> set (integer_partitions_enum_aux n n) \<Longrightarrow> 0 \<notin># mset xs" for xs
    using integer_partitions_enum_aux_not_null by auto
  ultimately show "set (map mset (integer_partitions_enum n)) \<subseteq> integer_partitions n"
    unfolding integer_partitions_def by auto
next
  have "0 \<notin># A \<Longrightarrow> A \<in> mset ` set (integer_partitions_enum_aux (\<Sum>\<^sub># A) (\<Sum>\<^sub># A))" for A
    unfolding image_def
    using integer_partitions_enum_correct_aux1 by (simp add: sum_mset.remove)
  then show "integer_partitions n \<subseteq> set (map mset (integer_partitions_enum n))"
    unfolding integer_partitions_def by auto
qed

subsubsection"Distinctness"

lemma integer_partitions_enum_aux_distinct:
  "distinct (integer_partitions_enum_aux n m)"
proof(induct n m rule:integer_partitions_enum_aux.induct)
  case (1 m)
  then show ?case by simp
next
  case (2 n m)
  have "distinct [h#r . h \<leftarrow> [1..< Suc (min (Suc n) m)], r \<leftarrow> integer_partitions_enum_aux ((Suc n)-h) h]"
    apply(subst Cons_distinct_concat_map_function)
    using 2 by auto
  then show ?case by simp
qed

theorem integer_partitions_enum_distinct:
  "distinct (integer_partitions_enum n)"
  using integer_partitions_enum_aux_distinct by simp

subsubsection"Cardinality"

lemma partitions_bij_betw_count:
  "bij_betw count {N. count N partitions n} {p. p partitions n}"
  by (rule bij_betw_byWitness[where f'="Abs_multiset"]) (auto simp: partitions_imp_finite_elements)

lemma card_partitions_count_partitions:
  "card {p. p partitions n} = card {N. count N partitions n}"
  using bij_betw_same_card partitions_bij_betw_count by metis

text"this sadly is not proven in \<open>Card_Number_Partitions.Card_Number_Partitions\<close>"
lemma card_partitions_number_partition:
  "card {p. p partitions n} = card {N. number_partition n N}"
  using card_partitions_count_partitions count_partitions_iff by simp

lemma integer_partitions_number_partition_eq:
  "integer_partitions n = {N. number_partition n N}"
  using integer_partitions_def number_partition_def by auto

lemma integer_partitions_cardinality_aux:
  "card (integer_partitions n) = (\<Sum>k\<le>n. Partition n k)"
  using card_partitions_number_partition integer_partitions_number_partition_eq card_partitions
  by simp

theorem integer_partitions_cardinality:
  "card (integer_partitions n) = Partition (2*n) n"
  using integer_partitions_cardinality_aux Partition_sum_Partition_diff add_implies_diff le_add1 mult_2
  by simp  

end
