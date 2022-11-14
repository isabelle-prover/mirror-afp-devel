section "Integer Compositions"

theory Integer_Compositions
  imports
    Common_Lemmas
begin

subsection"Definition"

definition integer_compositions :: "nat \<Rightarrow> nat list set" where
  "integer_compositions i = {xs. sum_list xs = i \<and> 0 \<notin> set xs}"
text "Integer compositions are \<open>integer_partitions\<close> where the order matters."
text "Cardinality: \<open>sum from n = 1 to i (binomial (i-1) (n-1)) = 2^(i-1)\<close>"
text "Example: \<open>integer_compositions 3 = {[3], [2,1], [1,2], [1,1,1]}\<close>"

subsection"Algorithm"

fun integer_composition_enum :: "nat \<Rightarrow> nat list list" where
  "integer_composition_enum 0 = [[]]"
| "integer_composition_enum (Suc n) =
    [Suc m #xs. m \<leftarrow> [0..< Suc n], xs \<leftarrow> integer_composition_enum (n-m)]"

subsection"Verification"

subsubsection"Correctness"

lemma integer_composition_enum_tail_elem:
  "x#xs \<in> set (integer_composition_enum n) \<Longrightarrow> xs \<in> set (integer_composition_enum (n - x))"
  by(induct n) auto

lemma integer_composition_enum_not_null_aux:
  "x#xs \<in> set (integer_composition_enum n) \<Longrightarrow> x \<noteq> 0"
  by(induct n) auto

lemma integer_composition_enum_not_null: "xs \<in> set (integer_composition_enum n) \<Longrightarrow> 0 \<notin> set xs"
proof(induct xs arbitrary: n)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  then show ?case 
    using integer_composition_enum_not_null_aux integer_composition_enum_tail_elem
    by fastforce
qed

lemma integer_composition_enum_empty: "[] \<in> set (integer_composition_enum n) \<Longrightarrow> n = 0"
  by(induct n) auto

lemma integer_composition_enum_sum: "xs \<in> set (integer_composition_enum n) \<Longrightarrow> sum_list xs = n"
proof(induct n arbitrary: xs rule: integer_composition_enum.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  show ?case proof(cases xs)
    case Nil
    then show ?thesis using 2 by auto
  next
    case (Cons y ys)
    have p1: "sum_list ys = Suc x - y" using 2 Cons
      by auto

    have "Suc x \<ge> y"
      using 2 Cons by auto
    then have p2: "sum_list ys = Suc x - y \<Longrightarrow> y + sum_list ys = Suc x"
      by simp

    show ?thesis
      using p1 p2 Cons by simp
  qed
qed

lemma integer_composition_enum_head_set:
  assumes"x \<noteq> 0" and "x \<le> n"
  shows" xs \<in> set (integer_composition_enum (n-x)) \<Longrightarrow> x#xs \<in> set (integer_composition_enum n)"
using assms proof(induct n arbitrary: x xs)
  case 0
  then show ?case
    by simp
next
  case c1: (Suc n)
  from c1.prems have 1:
    "\<forall>y\<in>{0..<n}. x = Suc y \<longrightarrow> xs \<notin> set (integer_composition_enum (n - y)) \<Longrightarrow> x = Suc n"
    by(induct x) simp_all

  then have 2: "\<forall>y\<in>{0..<n}. x = Suc y \<longrightarrow> xs \<notin> set (integer_composition_enum (n - y)) \<Longrightarrow> xs = []"
    using c1.prems(1) by simp
  show ?case using 1 2 by auto
qed

lemma integer_composition_enum_correct_aux:
  "0 \<notin> set xs \<Longrightarrow> xs \<in> set (integer_composition_enum (sum_list xs))"
  by(induct xs) (auto simp: integer_composition_enum_head_set) 

theorem integer_composition_enum_correct: 
  "set (integer_composition_enum n) = integer_compositions n"
proof standard
  show "set (integer_composition_enum n) \<subseteq> integer_compositions n"
    unfolding integer_compositions_def
    using integer_composition_enum_not_null integer_composition_enum_sum by auto
next
  show "integer_compositions n \<subseteq> set (integer_composition_enum n)"
    unfolding integer_compositions_def
    using integer_composition_enum_correct_aux by auto
qed

subsubsection"Distinctness"

theorem integer_composition_enum_distinct:
  "distinct (integer_composition_enum n)"
proof(induct n rule: integer_composition_enum.induct)
  case 1
  then show ?case by auto
next
  case (2 n)

  have h1: "x \<in> set [0..<Suc n] \<Longrightarrow> distinct (integer_composition_enum (n - x))" for x
    using "2" by simp
    
  have h2: "distinct [0..<n]"
    by simp

  have "distinct [Suc m #xs. m \<leftarrow> [0..< n], xs \<leftarrow> integer_composition_enum (n-m)]"
    using h1 h2 Cons_Suc_distinct_concat_map_function by simp
  then show ?case by auto 
qed

subsubsection"Cardinality"

lemma sum_list_two_pow_aux:
  "(\<Sum>x\<leftarrow>[0..< n]. (2::nat) ^ (n - x)) + 2 ^ (0 - 1) + 2 ^ 0 = 2 ^ (Suc n)"
proof(induct n)
  case 0
  then show ?case by simp
next
  case c1: (Suc n)

  have "x \<le> n \<Longrightarrow> 2 ^ (Suc n - x) = 2 * 2^ (n - x)" for x
    by (simp add: Suc_diff_le)
  also have "x \<in> set [0..<Suc n] \<Longrightarrow> x \<le> n" for x
    by auto
  ultimately have "(\<Sum>x\<leftarrow>[0..<Suc n]. 2 ^ (Suc n - x)) = (\<Sum>x\<leftarrow>[0..<Suc n]. 2* 2 ^ (n - x))"
     by (metis (mono_tags, lifting) map_eq_conv)
  
  also have "... = (\<Sum>x\<leftarrow>[0..< n]. 2* 2 ^ (n - x)) + 2* 2 ^ (0)"
    using sum_list_extract_last by simp
  
  also have "(\<Sum>x\<leftarrow>[0..< n]. (2::nat)* (2::nat) ^ (n - x)) = 2*(\<Sum>x\<leftarrow>[0..< n]. 2 ^ (n - x))"
    using sum_list_const_mult by fast

  ultimately have "(\<Sum>x\<leftarrow>[0..<Suc n]. (2::nat) ^ (Suc n - x))
      = 2*(\<Sum>x\<leftarrow>[0..< n]. 2 ^ (n - x)) + 2* 2 ^ (0)"
    by metis

  then show ?case using c1
    by simp 
qed

lemma sum_list_two_pow:
  "Suc (\<Sum>x\<leftarrow>[0..<n]. 2 ^ (n - Suc x)) = 2 ^ n"
  using sum_list_two_pow_aux sum_list_extract_last by(cases n) auto

lemma integer_composition_enum_length:
  "length (integer_composition_enum n) = 2^(n-1)"
proof(induct n rule: integer_composition_enum.induct)
  case 1
  then show ?case by simp
next
  case (2 n)
  then have "length [Suc m #xs. m \<leftarrow> [0..< n], xs \<leftarrow> integer_composition_enum (n-m)]
        = (\<Sum>x\<leftarrow>[0..<n]. 2 ^ (n - x - 1))"
    using length_concat_map_function_sum_list [of
        "[0..< n]"
        "\<lambda> x. integer_composition_enum (n - x)"
        "\<lambda> x. 2 ^ (n - x - 1)"
        "\<lambda> m xs. Suc m #xs"]
    by auto

  then show ?case
    using sum_list_two_pow
    by simp
qed

theorem integer_compositions_card:
  "card (integer_compositions n) = 2^(n-1)"
  using integer_composition_enum_correct integer_composition_enum_length
    integer_composition_enum_distinct distinct_card by metis

end
