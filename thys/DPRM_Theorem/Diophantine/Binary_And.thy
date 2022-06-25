subsection \<open>Binary and is Diophantine\<close>

theory Binary_And
  imports Binary_Masking Binary_Orthogonal
begin

lemma lm0244: "(a && b) \<preceq> a"
proof (induct a b rule: bitAND_nat.induct)
  case (1 uu)
  then show ?case by simp
next
  case (2 v n)
  then show ?case
    apply (auto simp add: mult.commute)
    by (smt One_nat_def add_cancel_left_right even_succ_div_two masks.elims(3) mod_Suc_le_divisor
          mod_by_Suc_0 mod_mod_trivial mod_mult_self4 mult_numeral_1_right mult_zero_right
          nonzero_mult_div_cancel_left not_mod2_eq_Suc_0_eq_0 numeral_2_eq_2 numeral_One
          odd_two_times_div_two_succ zero_neq_numeral)
qed

lemma lm0245: "(a && b) \<preceq> b"
  by (subst bitAND_commutes) (simp add: lm0244)

lemma bitAND_lt_left: "m && n \<le> m"
  using lm0244 masks_leq by auto
lemma bitAND_lt_right: "m && n \<le> n"
  using lm0245 masks_leq by auto

lemmas bitAND_lt = bitAND_lt_right bitAND_lt_left

lemma auxm3_lm0246:
  shows "bin_carry a b k = bin_carry a b k mod 2"
  using bin_carry_bounded by auto

lemma auxm2_lm0246:
  assumes "(\<forall>r< n.(nth_bit a r + nth_bit b r \<le> 1))" 
  shows "(nth_bit (a+b) n) = (nth_bit a n + nth_bit b n) mod 2"
  using assms no_carry by auto

lemma auxm1_lm0246: "a \<preceq> (a+b) \<Longrightarrow> (\<forall>n. nth_bit a n + nth_bit b n \<le> 1)" (is "?P \<Longrightarrow> ?Q")
proof-
{
  assume asm: "\<not>?Q"
  then obtain n where n1:"\<not>(nth_bit a n + nth_bit b n \<le> 1)"
    and n2:"\<forall>r < n. (nth_bit a r + nth_bit b r \<le> 1)"
    using obtain_smallest by (auto dest: obtain_smallest)
  hence ab1: "nth_bit a n =1  \<and>  nth_bit b n = 1" using nth_bit_def by auto
  hence "nth_bit (a+b) n = 0" using n2 auxm2_lm0246 by auto
  hence "\<not>?P" using masks_leq_equiv ab1 by auto (metis One_nat_def not_one_le_zero)
} then show "?P \<Longrightarrow> ?Q" by auto
qed

lemma aux0_lm0246:"a \<preceq> (a+b) \<longrightarrow>(a+b)\<exclamdown> n = a \<exclamdown> n + b \<exclamdown> n"
proof-
  show ?thesis using auxm1_lm0246 auxm2_lm0246 less_Suc_eq_le numeral_2_eq_2 by auto
qed

lemma aux1_lm0246:"a\<preceq>b \<longrightarrow> (\<forall>n. nth_bit (b-a) n = nth_bit b n - nth_bit a n)"
  using aux0_lm0246 masks_leq by auto (metis add_diff_cancel_left' le_add_diff_inverse)

lemma lm0246:"(a - (a && b)) \<bottom> (b - (a && b))"
  apply (subst ortho_mult_equiv)
  apply (rule allI) subgoal for k
  proof(cases "nth_bit a k = 0")
    case True
    have "nth_bit (a- (a && b)) k = 0" by (auto simp add: lm0244 aux1_lm0246 "True")
    then show ?thesis by simp
  next
    case False
    then show ?thesis proof(cases "nth_bit b k = 0")
      case True
      have "nth_bit (b- (a && b)) k = 0" by (auto simp add: lm0245 aux1_lm0246 "True")
      then show ?thesis by simp
    next
      case False2: False
      have "nth_bit a k = 1" using False nth_bit_def by auto
      moreover have "nth_bit b k = 1" using False2 nth_bit_def by auto
      ultimately have "nth_bit (b- (a && b)) k = 0"
        by (auto simp add: lm0245 aux1_lm0246 bitAND_digit_mult)
      then show ?thesis by simp
    qed
  qed
done

lemma aux0_lm0247:"(nth_bit a k) * (nth_bit b k) \<le> 1"
  using eq_iff nth_bit_def by fastforce

lemma lm0247_masking_equiv:
  fixes a b c :: nat
  shows "(c = a && b) \<longleftrightarrow> (c \<preceq> a \<and> c \<preceq> b \<and> (a - c) \<bottom> (b - c))" (is "?P \<longleftrightarrow> ?Q")
proof (rule)
  assume ?P
  thus ?Q
    apply (auto simp add: lm0244 lm0245)
    using lm0246 orthogonal.simps by blast
next
  assume Q: ?Q
  have "(\<forall>k. nth_bit c k \<le> nth_bit a k \<and> nth_bit c k \<le> nth_bit b k)"
    using Q masks_leq_equiv by auto
  moreover have "(\<forall>k x. nth_bit x k \<le> 1)"
    by (auto simp add: nth_bit_def)
  ultimately have f0:"(\<forall>k. nth_bit c k \<le> ((nth_bit a k) * (nth_bit b k)))"
    by (metis mult.right_neutral mult_0_right not_mod_2_eq_0_eq_1 nth_bit_def)
  show "?Q \<Longrightarrow> ?P"
  proof (rule ccontr)
    assume contr:"c \<noteq> a && b"
    have k_exists:"(\<exists>k. (nth_bit c k) < ((nth_bit a k) * (nth_bit b k)))"
      using bitAND_mult_equiv by (meson f0 contr le_less)
    then obtain k
      where "(nth_bit c k) < ((nth_bit a k) * (nth_bit b k))" ..
    hence abc_kth:"((nth_bit c k) = 0) \<and> ((nth_bit a k) = 1) \<and> ((nth_bit b k) = 1)"
      using aux0_lm0247 less_le_trans
      by (metis One_nat_def Suc_leI nth_bit_bounded less_le less_one one_le_mult_iff)
    hence "(nth_bit (a - c) k) = 1 \<and> (nth_bit (b - c) k) = 1"
      by (auto simp add: abc_kth aux1_lm0246 Q)
    hence "\<not> ((a - c) \<bottom> (b - c))"
      by (metis mult.left_neutral not_mod_2_eq_0_eq_1 ortho_mult_equiv)
    then show False
      using Q by blast
  qed
qed

definition binary_and ("[_ = _ && _]" 1000)
  where "[A = B && C] \<equiv> (TERNARY (\<lambda>a b c. a = b && c) A B C)"

lemma binary_and_dioph[dioph]:
  fixes A B C :: polynomial
  defines "DR \<equiv> [A = B && C]"
  shows "is_dioph_rel DR"
proof -
  define DS where "DS \<equiv> (A [\<preceq>] B) [\<and>] (A [\<preceq>] C) [\<and>] (B [-] A) [\<bottom>] (C [-] A)"

  have "eval DS a = eval DR a" for a
    unfolding DS_def DR_def binary_and_def defs
    by (simp add: lm0247_masking_equiv)

  moreover have "is_dioph_rel DS"
    unfolding DS_def by (auto simp: dioph)

  ultimately show ?thesis
    by (auto simp: is_dioph_rel_def)
qed

declare binary_and_def[defs]


definition binary_and_attempt :: "polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial" ("_ &? _") where
  "A &? B \<equiv> Const 0"

end