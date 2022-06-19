subsection \<open>Binary orthogonality is Diophantine\<close>

theory Binary_Orthogonal
  imports Binomial_Coefficient "Digit_Expansions.Binary_Operations" "Lucas_Theorem.Lucas_Theorem"
begin

lemma equiv_with_lucas: "nth_digit = Lucas_Theorem.nth_digit_general"
  unfolding nth_digit_def Lucas_Theorem.nth_digit_general_def by simp

lemma lm0241_ortho_binom_equiv:"(a \<bottom> b) \<longleftrightarrow> odd ((a + b) choose b)" (is "?P \<longleftrightarrow> ?Q")
proof
  assume "?P"
  hence dig0:"(\<forall>i. (nth_bit a i) * (nth_bit b i) = 0)"
    using ortho_mult_equiv
    by auto
  hence "(\<forall>i. (nth_bit a i) * (nth_bit b i) \<noteq> 1)"
    by presburger
  hence dcons:"(\<forall>i. \<not>(((nth_bit a i) = 1) \<and> ((nth_bit b i) = 1)))"
    by auto
  hence "(\<forall>i. (bin_carry a b i) = 0)" using no_carry_mult_equiv dig0
    by blast
  hence dsum:"(\<forall>i. (nth_bit (a + b) i) = (nth_bit a i) + (nth_bit b i))"
    by (metis One_nat_def add.commute add_cancel_right_left add_self_mod_2
        dig0 mult_is_0 not_mod2_eq_Suc_0_eq_0 nth_bit_def one_mod_two_eq_one
        sum_digit_formula)

  have bdd_ab_exists:"(\<exists>p. (a + b) < 2^(Suc p))"
    using aux1_lm0241_pow2_up_bound by auto
  then obtain p where bdd_ab:"(a + b) < 2^(Suc p)" by blast
  moreover from bdd_ab have "b < 2^(Suc p)" by auto

  ultimately have "((a + b) choose b) mod 2 =
        (\<Prod>i\<le>p. ((nth_digit (a + b) i 2) choose (nth_digit b i 2))) mod 2"
    using lucas_theorem[of "a+b" 2 p b] bdd_ab two_is_prime_nat
    by (simp add: equiv_with_lucas)

  then have a_choose_b_digit_prod: "((a + b) choose b) mod 2 =
        (\<Prod>i\<le>p. ((nth_bit (a + b) i) choose (nth_bit b i))) mod 2"
    using nth_digit_base2_equiv
    by (auto cong: prod.cong)

  have "(\<forall>i. ((nth_bit (a + b) i) choose (nth_bit b i) = 1))"
    using aux2_lm0241_single_digit_binom[where ?a="nth_bit (a + b) i"
                                               and ?b="nth_bit b i"]
    by (metis add.commute add.right_neutral binomial_n_0 binomial_n_n dig0 dsum
        mult_is_0)
  hence f0:"1 = (\<Prod>i<p. (nth_bit (a + b) i) choose (nth_bit b i))"
    by simp
  hence f1:"... = ... mod 2" by simp
  hence f2:"... = ((a + b) choose b) mod 2"
    using a_choose_b_digit_prod by (simp add: \<open>\<forall>i. (a + b) \<exclamdown> i choose b \<exclamdown> i = 1\<close>)
  then show "?Q" using f0 by fastforce
next
  assume "?Q"
  hence a_choose_b_odd:"((a + b) choose b) mod 2 = 1"
    using odd_iff_mod_2_eq_one by blast

  have bdd_ab_exists:"(\<exists>p. (a + b) < 2^(Suc p))"
    using aux1_lm0241_pow2_up_bound by auto
  then obtain p where bdd_ab:"(a + b) < 2^(Suc p)" by blast
  moreover from bdd_ab have bdd_b: "b < 2^(Suc p)" by auto

  ultimately have "((a + b) choose b) mod 2 =
        (\<Prod>i\<le>p. ((nth_digit (a + b) i 2) choose (nth_digit b i 2))) mod 2"
    using lucas_theorem[of "a+b" 2 p b] bdd_ab two_is_prime_nat
    by (simp add: equiv_with_lucas)

  then have a_choose_b_digit_prod: "((a + b) choose b) mod 2 =
        (\<Prod>i\<le>p. ((nth_bit (a + b) i) choose (nth_bit b i))) mod 2"
    using nth_digit_base2_equiv nth_digit_def
    by (auto cong: prod.cong)
  hence all_prod_one_mod2:"... = 1" using a_choose_b_odd by linarith

  have choose_bdd:"(\<forall>i. 1 \<ge> (nth_bit (a + b) i) choose (nth_bit b i))"
    using nth_bit_bounded
    by (metis One_nat_def binomial_n_0 choose_one not_mod2_eq_Suc_0_eq_0
        nth_bit_def order_refl)
  hence "1 \<ge> (\<Prod>i\<le>p. ((nth_bit (a + b) i) choose (nth_bit b i)))"
    using all_prod_one_mod2 by (meson prod_le_1 zero_le)
  hence "(\<Prod>i\<le>p. ((nth_bit (a + b) i) choose (nth_bit b i))) mod 2 =
             (\<Prod>i\<le>p. ((nth_bit (a + b) i) choose (nth_bit b i)))"
    using all_prod_one_mod2 by linarith
  hence "... = 1"
    using all_prod_one_mod2 by linarith
  hence sub_pq_one:"\<forall>i\<le>p. (nth_bit (a + b) i) choose (nth_bit b i) = 1"
    using
      aux4_lm0241_prod_one[where ?n="p" and ?f="(\<lambda>i. (nth_bit (a + b) i) choose (nth_bit b i))"]
      choose_bdd by blast

  have "\<forall>r > p. (a + b) < 2^r" using bdd_ab
    by(metis One_nat_def Suc_lessI lessI less_imp_add_positive numeral_2_eq_2
       power_strict_increasing_iff trans_less_add1)
  hence "\<forall>r > p. r \<ge> p \<longrightarrow> (a + b) < 2^r" by auto
  hence ab_digit_bdd:"\<forall>r > p. r \<ge> p \<longrightarrow> nth_bit (a + b) r = 0"
    using nth_bit_def by simp

  have "\<forall>k > p. b < 2 ^ k" using bdd_b
    by(metis One_nat_def Suc_lessI lessI less_imp_add_positive numeral_2_eq_2
       power_strict_increasing_iff trans_less_add1)
  hence b_digit_bdd:"\<forall>k > p. k \<ge> p \<longrightarrow> nth_bit b k = 0"
    using nth_bit_def
    by (simp add: \<open>\<forall>k>p. b < 2 ^ k\<close>)

  from b_digit_bdd ab_digit_bdd aux3_lm0241_binom_bounds
  have "\<forall>i. i \<ge> p \<longrightarrow> (nth_bit (a + b) i) choose (nth_bit b i) = 1"
    by (simp add: le_less sub_pq_one)

  hence "\<forall>i. ((nth_bit (a + b) i) choose (nth_bit b i)) = 1"
    using sub_pq_one not_less by (metis linear)
  hence "\<forall>i. \<not>(nth_bit a i = 1 \<and> nth_bit b i = 1)" using aux5_lm0241 by blast
  hence "\<forall>i. ((nth_bit a i = 0 \<and> nth_bit b i = 1) \<or>
                  (nth_bit a i = 1 \<and> nth_bit b i = 0) \<or>
                  (nth_bit a i = 0 \<and> nth_bit b i = 0))"
    by (auto simp add:nth_bit_def nth_digit_bounded; metis nat.simps(3))
  hence "\<forall>i. (nth_bit a i) * (nth_bit b i) = 0" using mult_is_0 by blast
  then show "?P" using ortho_mult_equiv by blast
qed

definition orthogonal (infix "[\<bottom>]" 50)
  where "P [\<bottom>] Q \<equiv> (BINARY (\<lambda>a b. a \<bottom> b) P Q)"

lemma orthogonal_dioph[dioph]:
  fixes P Q
  defines "DR \<equiv> (P [\<bottom>] Q)"
  shows "is_dioph_rel DR"
proof -
  define P' Q' where pushed_def: "P' \<equiv> push_param P 1" "Q' \<equiv> push_param Q 1"

  define DS where "DS \<equiv> [\<exists>] [Param 0 = (P' [+] Q') choose Q'] [\<and>] ODD (Param 0)"

  have "eval DS a = eval DR a" for a
    unfolding DS_def DR_def orthogonal_def pushed_def defs
    using push_push1 lm0241_ortho_binom_equiv by (simp add: push0)

  moreover have "is_dioph_rel DS"
    unfolding DS_def by (simp add: dioph)

  ultimately show ?thesis
    by (auto simp: is_dioph_rel_def)
qed

declare orthogonal_def[defs]

end