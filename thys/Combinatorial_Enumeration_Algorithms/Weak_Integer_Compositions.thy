section "Weak Integer Compositions"

theory Weak_Integer_Compositions
  imports
    "HOL-Combinatorics.Multiset_Permutations"
    Common_Lemmas
begin

subsection"Definition"

definition weak_integer_compositions :: "nat \<Rightarrow> nat \<Rightarrow> nat list set" where
  "weak_integer_compositions i l = {xs. length xs = l \<and> sum_list xs = i}"
text "Weak integer compositions are similar to integer compositions, with the trade-off that 0 is
  allowed but the composition must have a fixed length."
text "Cardinality: \<open>binomial (i + n - 1) i\<close>"
text "Example: \<open>weak_integer_compositions 2 2 = {[2,0], [1,1], [0,2]}\<close>"

subsection"Algorithm"

fun weak_integer_composition_enum :: "nat \<Rightarrow> nat \<Rightarrow> nat list list" where
  "weak_integer_composition_enum i 0 = (if i = 0 then [[]] else [])"
| "weak_integer_composition_enum i (Suc 0) = [[i]]"
| "weak_integer_composition_enum i l =
  [h#r . h \<leftarrow> [0..< Suc i], r \<leftarrow> weak_integer_composition_enum (i-h) (l-1)]"

subsection"Verification"

subsubsection"Correctness"

lemma weak_integer_composition_enum_length:
  "xs \<in> set (weak_integer_composition_enum i l) \<Longrightarrow> length xs = l"
proof(induct l arbitrary: xs i)
  case 0
  then show ?case by simp
next
  case (Suc l)
  then show ?case by(cases l) auto 
qed

lemma weak_integer_composition_enum_sum_list:
  "xs \<in> set (weak_integer_composition_enum i l) \<Longrightarrow> sum_list xs = i"
proof(induct l arbitrary: xs i)
  case 0
  then show ?case by simp
next
  case (Suc l)
  then show ?case by(cases l) auto 
qed
  
lemma weak_integer_composition_enum_head:
  assumes "xs \<in> set (weak_integer_composition_enum (sum_list xs) (length xs))"
  shows "x # xs \<in> set (weak_integer_composition_enum (x + sum_list xs) (Suc (length xs)))"
proof(cases "length xs")
  case 0
  then show ?thesis by simp
next
  case (Suc y)

  (*maybe this should be proven elsewhere*)
  have 1: "\<lbrakk>n \<in> set xs; 0 < n\<rbrakk> \<Longrightarrow> 0 < sum_list xs" for n
    using sum_list_eq_0_iff by fast


  have 2: "xs \<notin> set (weak_integer_composition_enum 0 (Suc y)) \<Longrightarrow> 0 < sum_list xs"
    using Suc assms not_gr0 by fastforce

  have "x # xs \<notin> (#) (x + sum_list xs) ` set (weak_integer_composition_enum 0 (Suc y))
    \<Longrightarrow> \<exists>xa\<in>{0..<x + sum_list xs}. x # xs \<in> (#) xa ` set (weak_integer_composition_enum (x + sum_list xs - xa) (Suc y))"
   unfolding image_def using Suc assms 1 2 by auto
    
  from Suc this show ?thesis
    by auto
qed

lemma weak_integer_composition_enum_correct_aux:
  "xs \<in> set (weak_integer_composition_enum (sum_list xs) (length xs))"
  by (induct xs) (auto simp: weak_integer_composition_enum_head)

theorem weak_integer_composition_enum_correct:
  "set (weak_integer_composition_enum i l) = weak_integer_compositions i l"
proof standard
  show "set (weak_integer_composition_enum i l) \<subseteq> weak_integer_compositions i l"
    unfolding weak_integer_compositions_def
    using weak_integer_composition_enum_length weak_integer_composition_enum_sum_list
    by auto
next
  show "weak_integer_compositions i l \<subseteq> set (weak_integer_composition_enum i l)"
    unfolding weak_integer_compositions_def
    using weak_integer_composition_enum_correct_aux by auto
qed

subsubsection"Distinctness"

theorem weak_integer_composition_enum_distinct: "distinct (weak_integer_composition_enum i l)"
proof(induct rule: weak_integer_composition_enum.induct)
  case (1 i)
  then show ?case
    by simp
next
  case (2 i)
  then show ?case 
    by simp
next
  case (3 i l)
  have "distinct [h#r . h \<leftarrow> [0..< Suc i], r \<leftarrow> weak_integer_composition_enum (i-h) (Suc l)]"
    apply(subst Cons_distinct_concat_map_function)
    using 3 by auto
  then show ?case by simp
qed


subsubsection"Cardinality"

text \<open>The following is a generalization of the binomial coefficient to multisets. Sometimes it
is called multiset coefficient. Here we call it "multichoose" \cite{stanleyenumerative}.\<close>

definition multichoose:: "nat \<Rightarrow> nat \<Rightarrow> nat" (infixl "multichoose" 65) where
  "n multichoose k = (n + k -1) choose k"

lemma weak_integer_composition_enum_zero: "length (weak_integer_composition_enum 0 (Suc n)) = 1"
  by(induct n) auto

lemma a_choose_equivalence: "Suc (\<Sum>x\<leftarrow>[0..<k]. n + (k - x) choose (k - x)) = Suc (n + k) choose k"
proof -
  have "m \<ge> k \<Longrightarrow> (\<Sum>x\<leftarrow>[0..< Suc k]. m - x choose (k - x)) = Suc m choose k" for m
    using sum_choose_diagonal leq_sum_to_sum_list by metis
  then have 1: "Suc (\<Sum>x\<leftarrow>[0..<k]. (n + k) - x choose (k - x)) = Suc (n + k) choose k"
    by simp

  have "Suc (\<Sum>x\<leftarrow>[0..<k]. (n + k) - x choose (k - x)) = Suc (\<Sum>x\<leftarrow>[0..<k]. n + (k - x) choose (k - x))"
    by (metis (no_types, opaque_lifting) Nat.diff_add_assoc2 add.commute binomial_n_0 diff_is_0_eq' nle_le)
  
  then show ?thesis using 1 by simp 
qed

lemma composition_enum_length: "length (weak_integer_composition_enum i n) = n multichoose i"
  unfolding multichoose_def
proof(induct i n rule: weak_integer_composition_enum.induct)
  case (1 i)
  then show ?case by simp
next
  case (2 i)
  then show ?case by simp
next
  case (3 i n)

  then have "x \<in> set [0..< i] \<Longrightarrow>
    length (weak_integer_composition_enum (i - x) (Suc n)) = n + (i - x) choose (i - x)" for x
    by simp

  then have ev: "length [h#r . h \<leftarrow> [0..< i], r \<leftarrow> weak_integer_composition_enum (i-h) (Suc n)] =
     (\<Sum>x\<leftarrow>[0..< i]. n + (i - x) choose (i - x))"
    using length_concat_map_function_sum_list [of
      "[0..< i]"
      "\<lambda>x. (weak_integer_composition_enum (i-x) (Suc n))"
      "\<lambda>x. n + (i-x) choose (i-x)"
      "\<lambda>h r. h#r"
      ] by simp

  have "Suc (\<Sum>x\<leftarrow>[0..<i]. n + (i - x) choose (i - x)) = Suc (n + i) choose i"
    using a_choose_equivalence by simp

  then show ?case using weak_integer_composition_enum_zero ev by auto
qed

theorem weak_integer_compositions_cardinality: "card (weak_integer_compositions n k) = k multichoose n"
  using weak_integer_composition_enum_correct weak_integer_composition_enum_distinct composition_enum_length
  distinct_card by metis

end
