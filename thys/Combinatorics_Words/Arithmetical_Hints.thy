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

lemma per_lemma_len_le: assumes le: "p + q - gcd p q \<le> (n :: nat)" and "q \<noteq> 0" shows "p \<le> n"
  using le unfolding add_diff_assoc[OF gcd_le2_nat[OF \<open>q \<noteq> 0\<close>], symmetric] by (rule add_leD1)

lemma predE: assumes "k \<noteq> 0" obtains pred where "k = Suc pred"
  using assms not0_implies_Suc by auto

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

lemma two_three_add_le_mult: assumes "2 \<le> (l::nat)" and  "3 \<le> k" shows "l + k + 1 \<le> l*k" 
proof-
  obtain l' where l: "l = Suc (Suc l')"
     using  \<open>2 \<le> l\<close> at_least2_Suc[OF \<open>2 \<le> l\<close>] by blast
  obtain k' where k: "k = Suc (Suc (Suc k'))"
    using  \<open>3 \<le> k\<close> at_least3_Suc[OF \<open>3 \<le> k\<close>] by blast
  show "l + k + 1 \<le> l*k"
    unfolding l k
  by (induct l' k' rule: nat_induct_pair, simp, simp add: add.commute[of "Suc (Suc l')"] mult.commute[of "Suc (Suc l')"], simp_all)
qed

lemmas not0_SucE = not0_implies_Suc[THEN exE] 

lemma le1_SucE: assumes "1 \<le> n"
  obtains k where "n = Suc k" using Suc_le_D[OF assms[unfolded One_nat_def]] by blast   

lemma Suc_minus:  "k \<noteq> 0 \<Longrightarrow> Suc (k - 1) = k"
   by simp 

lemma Suc_minus': "1 \<le> k \<Longrightarrow> Suc(k - 1) = k"
  by simp

lemmas Suc_minus'' = Suc_diff_1

lemma Suc_minus2: "2 \<le> k \<Longrightarrow> Suc (Suc(k - 2)) = k"
  by auto

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


end