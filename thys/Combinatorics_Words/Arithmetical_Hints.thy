(*  Title:      CoW/Arithmetical_Hints.thy
    Author:     Štěpán Holub, Charles University
    Author:     Martin Raška, Charles University
    Author:     Štěpán Starosta, CTU in Prague

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/
*)

theory Arithmetical_Hints
  imports Main
begin

section "Arithmetical hints"

text\<open>In this section we give some specific auxiliary lemmas on natural numbers.\<close>

lemma zero_diff_eq: "i \<le> j \<Longrightarrow> (0::nat) = j - i  \<Longrightarrow> j = i"
  by simp

lemma zero_less_diff': "i < j \<Longrightarrow> j - i \<noteq> (0::nat)"
   by simp

lemma nat_prod_le: "m \<noteq> (0 :: nat) \<Longrightarrow> m*n \<le> k \<Longrightarrow> n \<le> k"
  using le_trans[of n "m*n" k] by auto

lemma get_div: "(p :: nat) < a \<Longrightarrow> m = (m * a + p) div a"
  by simp

lemma get_mod: "(p :: nat) < a \<Longrightarrow> p = (m * a + p) mod a"
  by simp

lemma plus_one_between:  "(a :: nat) < b \<Longrightarrow> \<not> b < a + 1"
  by auto

lemma quotient_smaller: "k \<noteq> (0 :: nat) \<Longrightarrow>  b \<le> k * b"
  by simp

lemma mult_cancel_le: "b \<noteq> 0 \<Longrightarrow> a*b \<le> c*b \<Longrightarrow> a \<le> (c::nat)"
  by simp

lemma add_lessD2: "k + m < (n::nat) \<Longrightarrow> m < n"
unfolding add.commute[of k] using add_lessD1.

lemma mod_offset:  assumes "M \<noteq> (0 :: nat)"
  obtains k where "n mod M = (l + k) mod M"
proof-
  have "(l + (M - l mod M)) mod M = 0"
    using mod_add_left_eq[of l M "(M - l mod M)", unfolded le_add_diff_inverse[OF mod_le_divisor[OF assms[unfolded neq0_conv]], of l] mod_self, symmetric].
  from mod_add_left_eq[of "(l + (M - l mod M))" M n, symmetric, unfolded this add.commute[of 0] add.comm_neutral]
  have "((l + (M - l mod M)) + n) mod M = n mod M".
  from that[OF this[unfolded add.assoc, symmetric]]
  show thesis.
qed

lemma assumes "q \<noteq> (0::nat)" shows "p \<le> p + q - gcd p q"
  using gcd_le2_nat[OF \<open>q \<noteq> 0\<close>, of p]
  by linarith

lemma less_mult_one: assumes "(m-1)*k < k" obtains "m = 0" | "m = (1::nat)"
  using assms by fastforce

lemmas gcd_le2_pos = gcd_le2_nat[folded zero_order(4)] and
       gcd_le1_pos = gcd_le1_nat[folded zero_order(4)]

lemma ge1_pos_conv: "1 \<le> k \<longleftrightarrow> 0 < (k::nat)"
  by linarith

lemma per_lemma_len_le: assumes le: "p + q - gcd p q \<le> (n :: nat)" and "0 < q" shows "p \<le> n"
  using le unfolding add_diff_assoc[OF gcd_le2_pos[OF \<open>0 < q\<close>], symmetric] by (rule add_leD1)

lemma Suc_less_iff_Suc_le: "Suc n < k \<longleftrightarrow> Suc n \<le> k - 1"
   by auto

lemma nat_induct_pair: "P 0 0 \<Longrightarrow> (\<And> m n. P m n \<Longrightarrow> P m (Suc n)) \<Longrightarrow> (\<And> m n. P m n \<Longrightarrow> P (Suc m) n) \<Longrightarrow> P m n"
  by (induction m arbitrary: n) (metis nat_induct, simp)

lemma One_less_Two_le_iff: "1 < k \<longleftrightarrow> 2 \<le> (k :: nat)"
  by fastforce

lemma at_least2_Suc: assumes "2 \<le> k"
  obtains k' where "k = Suc(Suc k')"
  using Suc3_eq_add_3  less_eqE[OF assms] by auto

lemma at_least3_Suc: assumes "3 \<le> k"
  obtains k' where "k = Suc(Suc(Suc k'))"
  using Suc3_eq_add_3  less_eqE[OF assms] by auto

lemmas not0_SucE[elim] = not0_implies_Suc[THEN exE]

lemma le1_SucE: assumes "1 \<le> n"
  obtains k where "n = Suc k" using Suc_le_D[OF assms[unfolded One_nat_def]] by blast

lemma Suc_minus:  "k \<noteq> 0 \<Longrightarrow> Suc (k - 1) = k"
   by simp

lemma Suc_minus': "1 \<le> k \<Longrightarrow> Suc(k - 1) = k"
  by simp

lemmas Suc_minus_pos = Suc_diff_1

lemma Suc_minus2: "2 \<le> k \<Longrightarrow> Suc (Suc(k - 2)) = k"
  by auto

lemma Suc_leE: assumes "Suc k \<le> n" obtains m where "n = Suc m" and "k \<le> m"
using Suc_le_D assms by blast

lemma two_three_add_le_mult: "2 \<le> (l::nat) \<Longrightarrow> 3 \<le> k \<Longrightarrow> k + l + 1 \<le> k*l"
  unfolding numeral_nat
  by (elim Suc_leE)  simp

lemma almost_equal_equal: assumes "(a:: nat) \<noteq> 0" and "b \<noteq> 0" and eq: "k*(a+b) + a = m*(a+b) + b"
  shows "k = m" and "a = b"
proof-
  show "k = m"
  proof (rule linorder_cases[of k m])
    assume "k < m"
    from add_le_mono1[OF mult_le_mono1[OF Suc_leI[OF this]]]
    have "(Suc k)*(a + b) + b \<le> m*(a+b) + b".
    hence False
      using  \<open>b \<noteq> 0\<close> unfolding mult_Suc eq[symmetric] by force
    thus ?thesis by blast
  next
    assume "m < k"
    from add_le_mono1[OF mult_le_mono1[OF Suc_leI[OF this]]]
    have "(Suc m)*(a + b) + a \<le> k*(a+b) + a".
    hence False
      using  \<open>a \<noteq> 0\<close> unfolding mult_Suc eq by force
    thus ?thesis by blast
  qed (simp)
  thus "a = b"
    using eq by auto
qed

lemma crossproduct_le: assumes "(a::nat) \<le> b" and "c \<le> d"
  shows "a*d + b*c \<le> a*c + b*d"
proof-
  have "b * c \<le> b * d  + a * c"
    using assms by (simp add: trans_le_add1)
  note mult_le_mono[OF assms]
  have "a * (d - c) \<le> b * (d - c)"
    using mult_le_mono1[OF \<open>a \<le> b\<close>].
  hence "a * d - a * c \<le> b * d - b * c"
    using diff_mult_distrib2 by metis
  hence "a * d \<le> b * d - b * c + a * c"
    using le_diff_conv by blast
  hence "a * d \<le> (b * d  + a * c) - b * c"
    by (simp add: \<open>c \<le> d\<close>)
  hence "a * d + b * c \<le> (b * d  + a * c) - b * c + b * c"
    by simp
  thus ?thesis
    using \<open>b * c \<le> b * d  + a * c\<close> by force
qed

lemma (in linorder) le_less_cases: "(a \<le> b \<Longrightarrow> P) \<Longrightarrow> (b < a \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis local.not_less)

end
