theory Carries
  imports Bits_Digits
begin

section \<open>Carries in base-b expansions\<close>

text \<open>Some auxiliary lemmas\<close>
lemma rev_induct[consumes 1, case_names base step]:
  fixes i k :: nat
  assumes le: "i \<le> k"
    and base: "P k"
    and step: "\<And>i. i \<le> k \<Longrightarrow> P i \<Longrightarrow> P (i - 1)"
  shows "P i"
proof -
  have "\<And>i::nat. n = k-i \<Longrightarrow> i \<le> k \<Longrightarrow> P i" for n
  proof (induct n)
    case 0
    then have "i = k" by arith
    with base show "P i" by simp
  next
    case (Suc n)
    then have "n = (k - (i + 1))" by arith
    moreover have k: "i + 1 \<le> k" using Suc.prems by arith
    ultimately have "P (i + 1)" by (rule Suc.hyps)
    from step[OF k this] show ?case by simp
  qed
  with le show ?thesis by fast
qed

subsection \<open>Definition of carry received at position k\<close>
text \<open>When adding two numbers m and n, the carry is \emph{introduced}
      at position 1 but is \emph{received} at position 2. The function below
      accounts for the latter case. 

\begin{center} \begin{verbatim}
        k: 6 5 4 3 2 1 0
        c:         1
   - - - - - - - - - - - -
        m:   1 0 1 0 1 0
        n:           1 1
    ----------------------
    m + n: 0 1 0 1 1 0 0
\end{verbatim} \end{center} \<close>

definition bin_carry :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bin_carry a b k = (a mod 2^k + b mod 2^k) div 2^k"

text \<open>Carry in the subtraction of two natural numbers\<close>

definition bin_narry :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bin_narry a b k = (if b mod 2^k > a mod 2^k then 1 else 0)"

text \<open>Equivalent definition\<close>
definition bin_narry2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bin_narry2 a b k = ((2^k + a mod 2^k - b mod 2^k) div 2^k + 1) mod 2"

lemma bin_narry_equiv: "bin_narry a b c = bin_narry2 a b c"
  apply (auto simp add: bin_narry_def bin_narry2_def)
  subgoal by (smt add.commute div_less dvd_0_right even_Suc le_add_diff_inverse2 less_add_eq_less 
        mod_greater_zero_iff_not_dvd neq0_conv not_mod2_eq_Suc_0_eq_0 order_le_less zero_less_diff 
        zero_less_numeral zero_less_power)
  subgoal by (simp add: le_div_geq less_imp_diff_less)
  done

subsection \<open>Properties of carries\<close>

lemma div_sub:
  fixes a b c :: nat
  shows "(a - b) div c = (if(a mod c < b mod c) then a div c - b div c - 1 else  a div c - b div c)"
proof-
  consider (alb) "a<b" | (ageb) "a\<ge>b" by linarith
  then show ?thesis
  proof cases
    case alb
    then show ?thesis using div_le_mono by auto
  next
    case ageb
    obtain a1 a2 where a1_def: "a1 = a div c" and a2_def: "a2 = a mod c" and a_def: "a=a1*c+a2" 
      using mod_div_decomp by blast
    obtain b1 b2 where b1_def: "b1 = b div c" and b2_def: "b2 = b mod c" and b_def: "b=b1*c+b2" 
      using mod_div_decomp by blast
    have a1geb1: "a1\<ge>b1" using ageb a1_def b1_def using div_le_mono by blast
    show ?thesis
    proof(cases "c=0")
      assume "c=0"
      then show ?thesis by simp
    next
      assume cneq0: "c \<noteq> 0"
      then show ?thesis
      proof(cases "a2 < b2")
        assume a2lb2: "a2 < b2"
        then show ?thesis 
        proof(cases "a1=b1")
          case True
          then show ?thesis using ageb a2lb2 a_def b_def by force 
        next
          assume "\<not>(a1=b1)"
          hence a1gb1: "a1>b1" using a1geb1 by auto
          have boundc: "a2+c-b2<c" using a2lb2 cneq0 by linarith
          have "a-b = (a1 - b1) * c + a2 - b2"
            using a_def b_def a1geb1 nat_diff_add_eq1[of b1 a1 c a2 b2] by auto
          also have "... = (a1 - b1-1+1) * c + a2 - b2"
            using a1gb1 Suc_diff_Suc[of b1 a1] by auto
          also have "... = (a1 - b1 - 1) * c + (a2 + c - b2)" 
            using div_eq_0_iff[of b2 c] mod_div_trivial[of b c] b2_def by force
          finally have "(a-b) div c = a1 - b1 - 1 + (a2 + c - b2) div c"
            using a_def b_def cneq0 by auto
          then show ?thesis 
            using boundc div_less by (simp add: a1_def a2_def b1_def b2_def)
        qed
      next
        assume a2geb2: "\<not> a2 < b2"
        then have "(a - b) div c = ((a1 - b1) * c + (a2 - b2)) div c" 
          using a1geb1 a_def b_def nat_diff_add_eq1 by auto
        then show ?thesis using a2geb2 div_add1_eq[of "(a1-b1)*c" "a2-b2" c]
          by(auto simp add: b2_def a2_def a1_def b1_def less_imp_diff_less)
      qed
    qed
  qed
qed

lemma dif_digit_formula:"a \<ge> b \<longrightarrow> (a - b)\<exclamdown>k = (a\<exclamdown>k + b\<exclamdown>k + bin_narry a b k) mod 2"
proof -
  {
    presume asm: "a\<ge>b" "a mod 2 ^ k < b mod 2 ^ k"
    then have "Suc((a - b) div 2 ^ k) = a div 2 ^ k - b div 2 ^ k"
      by (smt Nat.add_diff_assoc One_nat_def Suc_pred add.commute diff_is_0_eq div_add_self1 
          div_le_mono div_sub mod_add_self1 nat_le_linear neq0_conv plus_1_eq_Suc power_not_zero 
          zero_neq_numeral) 
    then have "(a - b) div 2 ^ k mod 2 = Suc (a div 2 ^ k mod 2 + b div 2 ^ k mod 2) mod 2"
      by (smt diff_is_0_eq even_Suc even_diff_nat even_iff_mod_2_eq_zero le_less mod_add_eq 
          nat.simps(3) not_mod_2_eq_1_eq_0)
  }
  moreover
  {
    presume asm2: "\<not> a mod 2 ^ k < b mod 2 ^ k" "b \<le> a"
    then have "(a - b) div 2 ^ k mod 2 = (a div 2 ^ k mod 2 + b div 2 ^ k mod 2) mod 2"
      using div_sub[of b "2^k" a] div_le_mono even_add even_iff_mod_2_eq_zero 
        le_add_diff_inverse2[of "b div 2 ^ k" "a div 2 ^ k"] mod_mod_trivial[of _ 2] 
        not_less[of "a mod 2 ^ k" "b mod 2 ^ k"] not_mod_2_eq_1_eq_0 div_sub by smt

  }

  ultimately show ?thesis
    by (auto simp add: bin_narry_def nth_bit_def) 
qed


lemma dif_narry_formula: 
  "a\<ge>b \<longrightarrow> bin_narry a b (k + 1) = (if (a\<exclamdown>k < b\<exclamdown>k + bin_narry a b k) then 1 else 0)"
proof -
  {
    presume a1: "a mod (2 * 2 ^ k) < b mod (2 * 2 ^ k)"
    presume a2: "\<not> a div 2 ^ k mod 2 < Suc (b div 2 ^ k mod 2)"
    have f3: "2 ^ k \<noteq> (0::nat)"
      by simp
    have f4: "a div 2 ^ k mod 2 = 1"
      using a2 by (meson le_less_trans mod2_eq_if mod_greater_zero_iff_not_dvd not_less 
          zero_less_Suc)
    then have "b mod (2 * 2 ^ k) = b mod 2 ^ k"
      using a2 by (metis (no_types) One_nat_def le_simps(3) mod_less_divisor mod_mult2_eq 
          mult.left_neutral neq0_conv not_less semiring_normalization_rules(7))
    then have "False"
      using f4 f3 a1 by (metis One_nat_def add.commute div_add_self1 div_le_mono less_imp_le 
          mod_div_trivial mod_mult2_eq mult.left_neutral not_less plus_1_eq_Suc 
          semiring_normalization_rules(7) zero_less_Suc)
  }
  moreover
  {
    presume a1: "\<not> a mod 2 ^ k < b mod 2 ^ k"
    presume a2: "a mod (2 * 2 ^ k) < b mod (2 * 2 ^ k)"
    presume a3: "\<not> a div 2 ^ k mod 2 < b div 2 ^ k mod 2"
    presume a4: "b \<le> a"
    have f6: "a mod 2 ^ Suc k < b mod 2 ^ Suc k"
    using a2 by simp
    obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where f7: "b + nn a b = a" using a4 le_add_diff_inverse by auto
    have "(a div 2 ^ k - b div 2 ^ k) div 2 = a div 2 ^ k div 2 - b div 2 ^ k div 2"
    using a3 div_sub by presburger
      then have f8: "(a - b) div 2 ^ Suc k = a div 2 ^ Suc k - b div 2 ^ Suc k"
        using a1 by (metis (no_types) div_mult2_eq div_sub power_Suc power_commutes)
      have f9: "\<forall>n na. Suc (na div n) = (n + na) div n \<or> 0 = n"
        by (metis (no_types) add_Suc_right add_cancel_left_right div_add_self1 lessI 
            less_Suc_eq_0_disj less_one zero_neq_one)
      then have "\<forall>n na nb. (na + nb - n) div na = Suc (nb div na) - n div na - 1 \<or>
         \<not> (na + nb) mod na < n mod na \<or> 0 = na" by (metis (no_types) div_sub)
      then have f10: "\<forall>n na nb. \<not> (nb::nat) mod na < n mod na \<or> nb div na - n div na 
          = (na + nb - n) div na \<or> 0 = na"
        by (metis (no_types) diff_Suc_Suc diff_commute diff_diff_left mod_add_self1 plus_1_eq_Suc)
      have "\<forall>n. Suc n \<noteq> n" by linarith
    then have "(0::nat) = 2 ^ Suc k"
      using f10 f9 f8 f7 f6 a4 by (metis add_diff_cancel_left' add_diff_assoc)
    then have "False"
      by simp
  }

  ultimately show ?thesis
    apply (auto simp add: nth_bit_def not_less bin_narry_def)
    subgoal by (smt add_0_left add_less_cancel_left Divides.divmod_digit_0(2) le_less_trans mod_less_divisor
        mod_mult2_eq mult_zero_right nat_neq_iff not_less not_mod2_eq_Suc_0_eq_0 
        semiring_normalization_rules(7) zero_less_numeral zero_less_power)
    subgoal by (smt One_nat_def add.left_neutral Divides.divmod_digit_0(1) le_less_trans less_imp_le
          mod_less_divisor mod_mult2_eq mod_mult_self1_is_0 mult_zero_right not_less
          not_mod2_eq_Suc_0_eq_0 not_one_le_zero semiring_normalization_rules(7) zero_less_numeral 
          zero_less_power)
    done
qed
 
lemma sum_digit_formula:"(a + b)\<exclamdown>k =(a\<exclamdown>k + b\<exclamdown>k + bin_carry a b k) mod 2"
  by (simp add: bin_carry_def nth_bit_def) (metis div_add1_eq mod_add_eq)

lemma sum_carry_formula:"bin_carry a b (k + 1) =(a\<exclamdown>k + b\<exclamdown>k + bin_carry a b k) div 2"
  by (simp add: bin_carry_def nth_bit_def)
     (smt div_mult2_eq div_mult_self4 mod_mult2_eq power_not_zero semiring_normalization_rules(20)
          semiring_normalization_rules(34) semiring_normalization_rules(7) zero_neq_numeral)

lemma bin_carry_bounded:
  shows "bin_carry a b k = bin_carry a b k mod 2"
proof-
  have "a mod 2 ^ k <  2 ^k" by simp
  moreover have "b mod 2 ^ k < 2 ^ k" by simp
  ultimately have "(a mod 2 ^ k + b mod 2 ^ k) <  2 ^(Suc k)" by (simp add: mult_2 add_strict_mono)
  then have "(a mod 2 ^ k + b mod 2 ^ k) div 2^k  \<le> 1" using less_mult_imp_div_less by force
  then have "bin_carry a b k \<le> 1" using div_le_mono bin_carry_def by fastforce
  then show ?thesis by auto
qed

lemma carry_bounded: "bin_carry a b k \<le> 1"
  using bin_carry_bounded not_mod_2_eq_1_eq_0[of "bin_carry a b k"] by auto

lemma no_carry:
  "(\<forall>r< n.((nth_bit a r) + (nth_bit b r) \<le> 1)) \<Longrightarrow>
          (nth_bit (a + b) n) = (nth_bit a n + nth_bit b n) mod 2"
  (is "?P \<Longrightarrow> ?Q n")
proof (rule ccontr)
  assume p: "?P"
  assume nq: "\<not>?Q n"
  then obtain k where k1:"\<not>?Q k" and k2:"\<forall>r<k. ?Q r" by (auto dest: obtain_smallest)

  have c1: "1 = bin_carry a b k"
    using k1 sum_digit_formula bin_carry_bounded
    by auto (metis add.commute not_mod2_eq_Suc_0_eq_0 plus_nat.add_0)

  have "bin_carry a b (k-1) = 0" using sum_digit_formula
    by (metis bin_carry_bounded bin_carry_def diff_is_0_eq' diff_less div_by_1 even_add
              even_iff_mod_2_eq_zero k2 less_numeral_extra(1) mod_by_1 neq0_conv nth_bit_bounded
              power_0)

  moreover have "a \<exclamdown> (k-1) + b \<exclamdown> (k-1) < 1"
    by (smt add.right_neutral c1 calculation diff_le_self k2 leI le_add_diff_inverse2 le_less_trans
            mod_by_1 mod_if nat_less_le nq one_div_two_eq_zero one_neq_zero p sum_carry_formula)

  ultimately have "0 = bin_carry a b k" using k2 sum_carry_formula
    by auto (metis Suc_eq_plus1_left add_diff_inverse_nat less_imp_diff_less mod_0 mod_Suc
              mod_add_self1 mod_div_trivial mod_less n_not_Suc_n plus_nat.add_0)

  then show False using c1 by auto
qed

lemma no_carry_mult_equiv:"(\<forall>k. nth_bit a k * nth_bit b k = 0) \<longleftrightarrow> (\<forall>k. bin_carry a b k = 0)"
  (is "?P \<longleftrightarrow> ?Q")
proof
  assume P: ?P 
  {
    fix k
    from P have "bin_carry a b k = 0"
    proof (induction k)
      case 0
      then show ?case using bin_carry_def by (simp)
    next
      case (Suc k)
      then show ?case using sum_carry_formula P
        by (metis One_nat_def Suc_eq_plus1 add.right_neutral div_less lessI
        mult_is_0 not_mod_2_eq_0_eq_1 nth_bit_def numeral_2_eq_2 zero_less_Suc)
    qed
  }
  then show ?Q by auto
next
  assume Q: ?Q
  {
    fix k
    from Q have "a \<exclamdown> k * b \<exclamdown> k = 0"
    proof (induction k)
      case 0
      then show ?case using bin_carry_def nth_bit_def
        by simp (metis add_self_div_2 not_mod2_eq_Suc_0_eq_0 power_one_right)
    next
      case (Suc k)
      then show ?case
        using nth_bit_def  sum_carry_formula
        by simp (metis One_nat_def add.right_neutral add_self_div_2 not_mod_2_eq_1_eq_0 power_Suc)+
    qed
  }
  then show ?P by auto 
qed


(* NEW LEMMAS FROM DIGIT COMPARISON *)

lemma carry_digit_impl: "bin_carry a b k \<noteq> 0 \<Longrightarrow> \<exists>r<k. a \<exclamdown> r + b \<exclamdown> r = 2"
proof(rule ccontr)
  assume "\<not> (\<exists>r<k. a \<exclamdown> r + b \<exclamdown> r = 2)"
  hence bound: "\<forall>r<k. a \<exclamdown> r + b \<exclamdown> r \<le> 1" using nth_bit_def by auto
  assume bk:"bin_carry a b k \<noteq> 0"
  hence base: "bin_carry a b k = 1" using carry_bounded le_less[of "bin_carry a b k" 1] by auto
  have step: "i \<le> k \<Longrightarrow> bin_carry a b i = 1 \<Longrightarrow> bin_carry a b (i - 1) = 1" for i
    proof(rule ccontr)
      assume ik: "i \<le> k"
      assume carry: "bin_carry a b i = 1"
      assume "bin_carry a b (i- 1) \<noteq> 1"
      hence "bin_carry a b (i - 1) = 0" using bin_carry_bounded not_mod_2_eq_1_eq_0[of "bin_carry a b (i - 1)"] by auto
      then show False using ik carry bound sum_carry_formula[of a b "i-1"] 
        apply simp
        by (metis Suc_eq_plus1 Suc_pred add_lessD1 bot_nat_0.not_eq_extremum carry diff_is_0_eq' div_le_mono le_eq_less_or_eq less_add_one one_div_two_eq_zero)
    qed 
  have "\<forall>i\<le>k. bin_carry a b i = 1" using rev_induct[where ?P="\<lambda>c.(bin_carry a b c = 1)"] step base by blast
  moreover have "bin_carry a b 0 = 0" using bin_carry_def by simp
  ultimately show False by auto
qed


end