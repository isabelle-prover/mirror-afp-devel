section "Code Generation"

theory Karatsuba_Code_Nat
  imports Main "HOL-Library.Code_Binary_Nat" Karatsuba
begin

text "In this theory, the Karatsuba Multiplication implemented in @{text Karatsuba} is used for code
generation. This is not really practical (except beginning at ~3000 decimal digits), but merely a
nice gimmick."

fun from_numeral :: "num \<Rightarrow> nat_lsbf" where
  "from_numeral num.One = [True]"
| "from_numeral (num.Bit0 x) = False # from_numeral x"
| "from_numeral (num.Bit1 x) = True # from_numeral x"

lemma from_numeral_nonempty: "from_numeral x \<noteq> []"
  by (induction x rule: from_numeral.induct; simp)

lemma from_numeral_truncated: "truncated (from_numeral x)"
  unfolding truncated_iff
  by (induction x rule: from_numeral.induct; simp add: from_numeral_nonempty)

lemma to_nat_from_numeral_neq_zero: "to_nat (from_numeral x) \<noteq> 0"
  using to_nat_zero_iff from_numeral_truncated from_numeral_nonempty by simp

fun to_numeral_of_truncated :: "nat_lsbf \<Rightarrow> num" where
"to_numeral_of_truncated [] = num.One"
| "to_numeral_of_truncated [True] = num.One"
| "to_numeral_of_truncated (True # xs) = num.Bit1 (to_numeral_of_truncated xs)"
| "to_numeral_of_truncated (False # xs) = num.Bit0 (to_numeral_of_truncated xs)"

lemma to_numeral_of_truncated_from_numeral:
 "to_numeral_of_truncated (from_numeral x) = x"
  apply (induction x)
  subgoal by simp
  subgoal by simp
  subgoal for x by (cases "from_numeral x"; simp)
  done

lemma nat_of_num_to_numeral_of_truncated:
  assumes "truncated xs"
  assumes "xs \<noteq> []"
  shows "nat_of_num (to_numeral_of_truncated xs) = to_nat xs"
  using assms proof (induction xs rule: to_numeral_of_truncated.induct)
  case 1
  then show ?case by blast
next
  case 2
  then show ?case by simp
next
  case (3 v va)
  note truncated_Cons_imp_truncated_tl[OF "3.prems"(1)]
  from "3.IH"[OF this] show ?case by simp
next
  case (4 xs)
  from "4.prems"(1) have "xs \<noteq> []"
    apply (intro ccontr[of "xs \<noteq> []"])
    by (simp add: truncated_iff)
  note truncated_Cons_imp_truncated_tl[OF "4.prems"(1)]
  from "4.IH"[OF this \<open>xs \<noteq> []\<close>] show ?case by simp
qed

definition to_numeral :: "nat_lsbf \<Rightarrow> num" where
  "to_numeral xs = (let xs' = Nat_LSBF.truncate xs in to_numeral_of_truncated xs')"

lemma to_numeral_from_numeral: "to_numeral (from_numeral x) = x"
  unfolding to_numeral_def Let_def
  using from_numeral_truncated  to_numeral_of_truncated_from_numeral
  by simp

lemma nat_of_num_to_numeral:
  assumes "to_nat xs \<noteq> 0"
  shows "nat_of_num (to_numeral xs) = to_nat xs"
  unfolding to_numeral_def Let_def
  using assms nat_of_num_to_numeral_of_truncated[of "truncate xs", OF truncate_truncate]
  unfolding nat_lsbf.to_f_elem
  using to_nat_zero_iff
  by simp

lemma l0:
  assumes "truncated xs"
  shows "to_numeral_of_truncated xs = num_of_nat (to_nat xs)"
  using assms
  by (metis nat_of_num_inverse nat_of_num_to_numeral_of_truncated num_of_nat.simps(1) to_nat.simps(1) to_numeral_of_truncated.simps(1))
  
lemma l1: "to_numeral xs = num_of_nat (to_nat xs)"
  unfolding to_numeral_def Let_def
  using l0[of "truncate xs"] truncate_truncate[of xs] nat_lsbf.to_f_elem
  by simp

lemma l2: "to_nat (from_numeral x) = nat_of_num x"
  by (metis nat_of_num_to_numeral to_nat_from_numeral_neq_zero to_numeral_from_numeral)

lemma[code]: 
  "(x::num) * y = to_numeral (karatsuba_mul_nat (from_numeral x) (from_numeral y))"
  unfolding l1 karatsuba_mul_nat_correct l2 times_num_def by (rule refl)

end