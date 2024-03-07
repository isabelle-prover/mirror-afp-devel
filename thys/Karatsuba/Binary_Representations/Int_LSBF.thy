theory Int_LSBF
  imports Nat_LSBF "HOL-Algebra.IntRing" 
begin

section "Representing @{type int} in LSBF"

subsection "Type definition"

datatype sign = Positive | Negative
type_synonym int_lsbf = "sign \<times> nat_lsbf"

subsection "Conversions"

fun from_int :: "int \<Rightarrow> int_lsbf" where
"from_int x = (if x \<ge> 0 then (Positive, from_nat (nat x)) else (Negative, from_nat (nat (-x))))"
fun to_int :: "int_lsbf \<Rightarrow> int" where
"to_int (Positive, xs) = int (to_nat xs)"
| "to_int (Negative, xs) = - int (to_nat xs)"

lemma to_int_from_int[simp]: "to_int (from_int x) = x"
  by (cases "x \<ge> 0") simp_all

fun truncate_int :: "int_lsbf \<Rightarrow> int_lsbf" where
"truncate_int (Positive, xs) = (Positive, truncate xs)"
| "truncate_int (Negative, xs) = (let ys = truncate xs in if ys = [] then (Positive, []) else (Negative, ys))"

lemma to_int_truncate[simp]: "to_int (truncate_int xs) = to_int xs"
  by (induction xs rule: truncate_int.induct) (simp_all add: Let_def to_nat_zero_iff)

lemma truncate_from_int[simp]: "truncate_int (from_int x) = from_int x"
  apply (cases "x \<ge> 0")
  subgoal by simp
  subgoal unfolding Let_def
  proof -
    assume "\<not> x \<ge> 0"
    then have "to_nat (from_nat (nat (- x))) > 0" by simp
    then have "truncate (from_nat (nat (- x))) \<noteq> []" using to_nat_zero_iff nless_le by blast
    then show ?thesis by simp
  qed
  done

lemma pos_and_neg_imp_zero:
  assumes "to_int (Positive, x) = to_int (Negative, y)"
  shows "to_nat x = 0 \<and> to_nat y = 0"
proof -
  have "to_int (Positive, x) \<ge> 0" "to_int (Negative, y) \<le> 0" by simp_all
  with assms have "to_int (Positive, x) = 0" "to_int (Negative, y) = 0" by simp_all
  thus ?thesis by simp_all
qed

lemma to_int_eq_imp_truncate_int_eq: "to_int (a, x) = to_int (b, y) \<Longrightarrow> truncate_int (a, x) = truncate_int (b, y)"
  apply (cases a; cases b)
  subgoal by (simp add: to_nat_eq_imp_truncate_eq[of x y])
  subgoal
    using pos_and_neg_imp_zero[of x y] to_nat_zero_iff
    by fastforce
  subgoal using to_nat_zero_iff by (simp add: Let_def)
  subgoal by (simp add: to_nat_eq_imp_truncate_eq[of x y])
  done

lemma from_int_to_int: "from_int \<circ> to_int = truncate_int"
proof -
  have "(\<And>x y. to_int x = to_int y \<Longrightarrow> truncate_int x = truncate_int y)"
    using to_int_eq_imp_truncate_int_eq by auto
  thus ?thesis
    using from_to_f_criterion[of to_int from_int truncate_int]
    using truncate_from_int to_int_from_int
    using comp_apply
    by fastforce
qed

interpretation int_lsbf: abstract_representation from_int to_int truncate_int
proof
  show "to_int \<circ> from_int = id"
    using to_int_from_int comp_apply by fastforce
next
  show "from_int \<circ> to_int = truncate_int"
    using from_int_to_int comp_apply by fastforce
qed

subsection "Addition"

fun add_int :: "int_lsbf \<Rightarrow> int_lsbf \<Rightarrow> int_lsbf" where
"add_int (Negative, xs) (Negative, ys) = (Negative, add_nat xs ys)"
| "add_int (Positive, xs) (Positive, ys) = (Positive, add_nat xs ys)"
| "add_int (Positive, xs) (Negative, ys) = (if compare_nat xs ys then (Negative, subtract_nat ys xs) else (Positive, subtract_nat xs ys))"
| "add_int (Negative, xs) (Positive, ys) = (if compare_nat xs ys then (Positive, subtract_nat ys xs) else (Negative, subtract_nat xs ys))"

lemma add_int_correct: "to_int (add_int x y) = to_int x + to_int y"
  apply (induction x y rule: add_int.induct)
  subgoal by (simp add: add_nat_correct)
  subgoal by (simp add: add_nat_correct)
  apply (auto simp only: add_int.simps compare_nat_correct subtract_nat_correct to_int.simps split: if_splits)
  done

fun nat_mul_to_int_mul :: "(nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf) \<Rightarrow> int_lsbf \<Rightarrow> int_lsbf \<Rightarrow> int_lsbf"  where
"nat_mul_to_int_mul f (x, xs) (y, ys) = ((if x = y then Positive else Negative), f xs ys)"

lemma nat_mul_to_int_mul_correct:
  assumes "\<And>x y. to_nat (f x y) = to_nat x * to_nat y"
  shows "\<And>x y xs ys. to_int (nat_mul_to_int_mul f (x, xs) (y, ys)) = to_int (x, xs) * to_int (y, ys)"
  subgoal for x y xs ys
    by (cases x; cases y) (simp_all add: assms)
  done
    
subsection "Grid Multiplication"

fun grid_mul_int where "grid_mul_int x y = nat_mul_to_int_mul grid_mul_nat x y"

corollary grid_mul_int_correct: "to_int (grid_mul_int x y) = to_int x * to_int y"
  using nat_mul_to_int_mul_correct[OF grid_mul_nat_correct]
  by (metis grid_mul_int.elims surj_pair)

end