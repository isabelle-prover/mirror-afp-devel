section \<open>Digit functions\<close>

theory Bits_Digits
  imports Main
begin

text \<open>We define the n-th bit of a number in base 2 representation \<close>
definition nth_bit :: "nat \<Rightarrow> nat \<Rightarrow> nat" (infix "\<exclamdown>" 100) where
  "nth_bit num k = (num div (2 ^ k)) mod 2"

text \<open>as well as the n-th digit of a number in an arbitrary base \<close>
definition nth_digit :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nth_digit num k base = (num div (base ^ k)) mod base"

text \<open>In base 2, the two definitions coincide. \<close>
lemma nth_digit_base2_equiv:"nth_bit a k = nth_digit a k (2::nat)"
  by (auto simp add:nth_bit_def nth_digit_def)

lemma general_digit_base:
  assumes "t1 > t2" and "b>1"
  shows "nth_digit (a * b^t1) t2 b = 0" 
proof -
  have 1: "b^t1 div b^t2 = b^(t1-t2)" using assms apply auto
    by (metis Suc_lessD less_imp_le less_numeral_extra(3) power_diff)
  have "b^t2 dvd b^t1" using `t1 > t2`
    by (simp add: le_imp_power_dvd)
  hence "(a * b^t1) div b^t2 = a * b^(t1-t2)" using div_mult_swap[of "b^t2" "b^t1" "a"] 1 by auto
  thus ?thesis using nth_digit_def assms by auto
qed

lemma nth_bit_bounded: "nth_bit a k \<le> 1"
  by (auto simp add: nth_bit_def)

lemma nth_digit_bounded: "b>1 \<Longrightarrow> nth_digit a k b \<le> b-1"
  apply (auto simp add: nth_digit_def)
  using less_Suc_eq_le by fastforce

lemma obtain_smallest: "P (n::nat) \<Longrightarrow> \<exists>k\<le>n. P k \<and> (\<forall>a<k.\<not>(P a))"
  by (metis ex_least_nat_le not_less_zero zero_le)

subsection \<open>Simple properties and equivalences\<close>

text \<open>Reduce the @{term nth_digit} function to @{term nth_bit} if the base is a power of 2\<close>

lemma digit_gen_pow2_reduct:
  \<open>(nth_digit a t (2 ^ c)) \<exclamdown> k = a \<exclamdown> (c * t + k)\<close> if \<open>k < c\<close>
proof -
  have moddiv: "(x mod 2 ^ c) \<exclamdown> k = x \<exclamdown> k" for x
  proof-
    define n where \<open>n = c - k\<close>
    with \<open>k < c\<close> have c_nk: \<open>c = n + k\<close>
      by simp
    obtain a b where x_def: "x = a * 2 ^ c + b" and "b < 2 ^ c" 
      by (meson mod_div_decomp mod_less_divisor zero_less_numeral zero_less_power)
    then have bk: "(x mod 2 ^ c) \<exclamdown> k = b \<exclamdown> k" by simp
    from \<open>b < 2 ^ c\<close> have \<open>x div 2 ^ k = a * 2 ^ (c - k) + b div 2 ^ k\<close>
      by (simp add: x_def c_nk power_add flip: mult.commute [of \<open>2 ^ k\<close>] mult.left_commute [of \<open>2 ^ k\<close>])
    then have "x \<exclamdown> k = (a*2^(c-k) + b div 2^k) mod 2" by (simp add: nth_bit_def)
    then have "x \<exclamdown> k = b \<exclamdown> k" using nth_bit_def \<open>k < c\<close> by (simp add: mod2_eq_if)
    then show ?thesis using nth_bit_def bk by linarith
  qed
  have "a div ((2 ^ c) ^ t * 2 ^ k) = a div (2 ^ c) ^ t div 2 ^ k" using div_mult2_eq by blast
  moreover have "a div (2 ^ c) ^ t mod 2 ^ c div 2 ^ k mod 2 = a div (2 ^ c) ^ t div 2 ^ k mod 2"
    using moddiv nth_bit_def by auto 
  ultimately show "(nth_digit a t (2^c)) \<exclamdown> k = a \<exclamdown> (c*t+k)"
    using nth_digit_def nth_bit_def by (auto simp: power_add power_mult)
qed

text \<open>Show equivalence of numbers by equivalence of all their bits (digits)\<close>

lemma aux_even_pow2_factor: "a > 0 \<Longrightarrow> \<exists>k b. ((a::nat) = (2^k) * b \<and> odd b)"
proof(induction  a rule: full_nat_induct)
  case (1 n)
  then show ?case
  proof (cases "odd n")
    case True
    then show ?thesis by (metis nat_power_eq_Suc_0_iff power_Suc power_Suc0_right power_commutes)
  next
    case False
    have "(\<exists>t. n = 2 * t)" using False by auto
    then obtain t where n_def:"n = 2 * t" ..
    then have "t < n" using "1.prems" by linarith
    then have ih:"\<exists>r s. t = 2^r * s \<and> odd s" using 1 n_def by simp
    then have "\<exists>r s. n = 2^(Suc r) * s" using n_def by auto
    then show ?thesis by (metis ih n_def power_commutes semiring_normalization_rules(18)
                          semiring_normalization_rules(28))
  qed
qed

lemma aux0_digit_wise_equiv:"a > 0 \<Longrightarrow> (\<exists>k. nth_bit a k = 1)"
proof -
  assume a_geq_0: "a > 0"
  consider (odd) "a mod 2 = 1" | (even) "a mod 2 = 0" by force
  then show ?thesis
  proof(cases)
    case odd
    then show ?thesis by (metis div_by_1 nth_bit_def power_0)
  next
    case even
    then have bk_def:"\<exists>k b. (a = (2^k) * b \<and> odd b)"
      using aux_even_pow2_factor a_geq_0 by simp
    then obtain b k where bk_cond:"(a = (2^k) * b \<and> odd b)" by blast
    then have "b = a div (2^k)" by simp
    then have digi_b:"nth_bit b 0 = 1" using bk_def
      using bk_cond nth_bit_def odd_iff_mod_2_eq_one by fastforce
    then have "nth_bit a k = (nth_bit b 0)" using nth_bit_def bk_cond by force
    then have "nth_bit a k = 1" using digi_b by simp
    then show ?thesis by blast
  qed
qed

lemma aux1_digit_wise_equiv:"(\<forall>k.(nth_bit a k = 0)) \<longleftrightarrow> a = 0" (is "?P \<longleftrightarrow> ?Q")
proof
  assume "?Q"
  then show "?P" by (simp add: nth_bit_def)
next
  {
    assume a_neq_0:"\<not>?Q"
    then have "a > 0" by blast
    then have "\<not>?P" using aux0_digit_wise_equiv by (metis zero_neq_one)
  }
  thus "?P \<Longrightarrow> ?Q" by blast
qed

lemma aux2_digit_wise_equiv: "(\<forall>r<k. nth_bit a r = 0) \<longrightarrow> (a mod 2^k = 0)"
proof(induct k)
  case 0
  then show ?case
    by (auto simp add: nth_bit_def)
next
  case (Suc k)
  then show ?case
    by (auto simp add: nth_bit_def)
       (metis dvd_imp_mod_0 dvd_mult_div_cancel dvd_refl even_iff_mod_2_eq_zero
        lessI minus_mod_eq_div_mult minus_mod_eq_mult_div mult_dvd_mono)
qed

lemma digit_wise_equiv: "(a = b) \<longleftrightarrow> (\<forall>k. nth_bit a k = nth_bit b k)" (is "?P \<longleftrightarrow> ?Q")
proof
  assume "?P"
  then show "?Q" by simp
next
  {
    assume notP: "\<not>?P"
    have "\<not>(\<forall>k. nth_bit a k = nth_bit b k)" if ab: "a<b" for a b
    proof-
      define c::nat where "c = b - a"
      have b: "a+c=b" by (auto simp add: c_def "ab" less_imp_le)
      have  "\<exists>k.(nth_bit c k = 1)" using nth_bit_def aux1_digit_wise_equiv
        by (metis c_def not_less0 not_mod_2_eq_1_eq_0 that zero_less_diff)
      then obtain k where k1:"nth_bit c k = 1" and k2:"\<forall>r < k. (nth_bit c r \<noteq> 1)"
        by (auto dest: obtain_smallest)
      then have cr0: "\<forall>r < k. (nth_bit c r = 0)" by (simp add: nth_bit_def)
      from aux2_digit_wise_equiv cr0 have "c mod 2^k = 0" by auto
      then have "a div 2 ^ k mod 2 \<noteq> b div 2 ^ k mod 2"
        by auto (metis b div_plus_div_distrib_dvd_right even_add k1 nth_bit_def odd_iff_mod_2_eq_one)
      then show ?thesis by (auto simp add: nth_bit_def)
    qed
    from this [of a b] this [of b a] notP have "\<forall>k. nth_bit a k = nth_bit b k \<Longrightarrow> a = b"
      using linorder_neqE_nat by auto
  }
  then show "?Q ==> ?P" by auto
qed

text \<open>Represent natural numbers in their binary expansion\<close>

lemma aux3_digit_sum_repr:
  assumes "b < 2^r"
  shows "(a*2^r + b) \<exclamdown> r = (a*2^r) \<exclamdown> r"
  by (auto simp add: nth_bit_def assms)

lemma aux2_digit_sum_repr:
  assumes "n < 2^c" "r < c"
  shows "(a*2^c+n) \<exclamdown> r = n \<exclamdown> r"
proof -
  have [simp]: \<open>a*(2::nat) ^ c div 2 ^ r = a*2 ^ (c - r)\<close>
    using assms(2)
    by (auto simp: less_iff_Suc_add
          monoid_mult_class.power_add ac_simps)
  show ?thesis
    using assms
    by (auto simp add: nth_bit_def
            div_plus_div_distrib_dvd_left
            le_imp_power_dvd
          simp flip: mod_add_left_eq)
qed

lemma aux1_digit_sum_repr:
assumes "n < 2^c" "r<c"
shows "(\<Sum>k<c.((n \<exclamdown> k)*2^k)) \<exclamdown> r = n \<exclamdown> r"
proof-
  define a where "a \<equiv> (\<Sum>k=0..<Suc(r).((n \<exclamdown> k)*2^k))"
  define d where "d \<equiv> (\<Sum>k=Suc(r)..<c.((n \<exclamdown> k)*2^k))"
  define e where "e \<equiv> (\<Sum>k=Suc r..<c.((n \<exclamdown> k)*2^(k-Suc(r))))"
  define b where "b \<equiv> (\<Sum>k=0..<r.((n \<exclamdown> k)*2^k))"
  have ad: "(\<Sum>k=0..<c.((n \<exclamdown> k)*2^k)) = a + d"
    using a_def d_def assms
    by (metis (no_types, lifting) Suc_leI a_def assms(2) d_def sum.atLeastLessThan_concat zero_le)
  have "d = (\<Sum>k=Suc(r)..<c.(2^(Suc r) * (n \<exclamdown> k *  2^(k - Suc r))))"
    using d_def apply (simp)
    apply (rule sum.cong; auto simp: algebra_simps)
    by (metis add_Suc le_add_diff_inverse numerals(2) power_Suc power_add)
  hence d2r: "d = 2^Suc(r)*e" using d_def e_def
     sum_distrib_left[of "2^(Suc r)" "\<lambda>k. (n \<exclamdown> k) *  2^(k - Suc r)" "{Suc r..<c}"] by auto
  have "(\<Sum>k<c.((n \<exclamdown> k)*2^k)) = a +2^Suc(r)*e" by (simp add: d2r ad lessThan_atLeast0)
  moreover have "(\<Sum>k=0..<Suc(r).((n \<exclamdown> k)*2^k)) < 2 ^ Suc(r)" using assms
  proof(induct r)
    case 0
    then show ?case
    proof -
      have "n \<exclamdown> 0 < Suc 1" 
        by (metis (no_types) atLeastLessThan_empty atLeastLessThan_iff lessI linorder_not_less 
                  nth_bit_bounded)
      then show ?thesis
        by simp
    qed
    next
      case (Suc r)
      have r2: "n \<exclamdown> Suc(r) *  2 ^ Suc(r) \<le>  2 ^ Suc(r)" using nth_bit_bounded by simp
      have "(\<Sum>k=0..<Suc(r).((n \<exclamdown> k)*2^k)) < 2 ^ Suc(r)" 
        using Suc.hyps using Suc.prems(2) Suc_lessD assms(1) by blast
      then show ?case using "r2" 
        by (smt Suc_leI Suc_le_lessD add_Suc add_le_mono mult_2 power_Suc sum.atLeast0_lessThan_Suc)
    qed
    then have "a < 2 ^Suc(r)" using a_def by blast
  ultimately have ar:"(a+d) \<exclamdown> r = a \<exclamdown> r" using d2r
    by (metis (no_types, lifting) aux2_digit_sum_repr lessI semiring_normalization_rules(24) 
              semiring_normalization_rules(7))
    (* Second part of proof *)
  have ab: "a =(n \<exclamdown> r)*2^r + b" using a_def b_def d_def by simp
  have "(\<Sum>k=0..<r.((n \<exclamdown> k)*2^k)) <2^r"
  proof(induct r)
    case 0
      then show ?case by auto
    next
      case (Suc r)
      have r2: "n \<exclamdown> r *  2 ^ r \<le>  2 ^ r" using nth_bit_bounded by simp
      have "(\<Sum>k = 0..<r. n \<exclamdown> k * 2 ^ k) < 2^r" using Suc.hyps by auto
      then show ?case apply simp using "r2" by linarith
  qed
  then have b: "b < 2^r" using b_def by blast
  then have "a \<exclamdown> r = ((n \<exclamdown> r)*2^r) \<exclamdown> r" using ab aux3_digit_sum_repr by simp
  then have "a \<exclamdown> r = (n \<exclamdown> r)" using nth_bit_def by simp
  then show ?thesis using ar a_def by (simp add: ad lessThan_atLeast0)
qed

lemma digit_sum_repr:
  assumes "n < 2^c"
  shows "n = (\<Sum>k < c.((n \<exclamdown> k) * 2^k))"
proof -
  have "\<forall>k. (c\<le>k \<longrightarrow> n<2^k)" using assms less_le_trans by fastforce
  then have nik: "\<forall>k.( k\<ge> c \<longrightarrow> (n \<exclamdown> k = 0))"  by (auto simp add: nth_bit_def)
  have "(\<Sum>r<c.((n \<exclamdown> r)*(2::nat)^r))<(2::nat)^c"
  proof (induct c)
    case 0
    then show ?case by simp
  next
    case (Suc c)
    then show ?case
      using nth_bit_bounded
            add_mono_thms_linordered_field[of "(n \<exclamdown> c)* 2 ^ c" " 2 ^ c" "(\<Sum>r<c. n \<exclamdown> r * 2 ^ r)" "2^c"]
      by simp
  qed
  then have "\<forall>k. k\<ge> c \<longrightarrow> (\<Sum>r<c.((n \<exclamdown> r)*2^r)) \<exclamdown> k = 0"
    using less_le_trans by (auto simp add: nth_bit_def) fastforce
  then have "\<forall>r\<ge>c.(n \<exclamdown> r  = (\<Sum>k<c.((n \<exclamdown> k)*2^k)) \<exclamdown> r)" by (simp add: nik)
  moreover have "\<forall>r<c.(n \<exclamdown> r  = (\<Sum>k<c.((n \<exclamdown> k)*2^k)) \<exclamdown> r)" using aux1_digit_sum_repr assms by simp
  ultimately have "\<forall>r.(\<Sum>k<c.((nth_bit n k)*2^k)) \<exclamdown> r = n \<exclamdown> r " by (metis not_less)
  then show ?thesis using digit_wise_equiv by presburger
qed

lemma digit_sum_repr_variant:
  "n =(\<Sum>k<n.((nth_bit n k)*2^k))"
  using less_exp digit_sum_repr by auto

lemma digit_sum_index_variant:
  "r>n \<longrightarrow> ((\<Sum>k< n.((n \<exclamdown> k)*2^k)) = (\<Sum>k< r.(n \<exclamdown> k)*2^k))"
proof-
  have "\<forall>r.(2^r > r)" using less_exp by simp
  then have pow2: "\<forall>r.(r>n \<longrightarrow> 2^r>n)" using less_trans by blast
  then have "\<forall>r.(r > n \<longrightarrow> (n \<exclamdown> r = 0))" by (auto simp add: nth_bit_def)
  then have "\<forall>r. r > n \<longrightarrow> (n \<exclamdown> r)*2^r = 0" by auto
  then show ?thesis using digit_sum_repr digit_sum_repr_variant pow2 by auto
qed

text \<open>Digits are preserved under shifts\<close>

lemma digit_shift_preserves_digits:
  assumes "b>1" 
  shows "nth_digit (b * y) (Suc t) b = nth_digit y t b" 
  using nth_digit_def assms by auto

lemma digit_shift_inserts_zero_least_siginificant_digit:
  assumes "t>0" and "b>1"
  shows "nth_digit (1 + b * y) t b = nth_digit (b * y) t b" 
  using nth_digit_def assms apply auto
proof -
  assume "0 < t"
  assume "Suc 0 < b"
  hence "Suc (b * y) mod b = 1"
    by (simp add: Suc_times_mod_eq)
  hence "b * y div b = Suc (b * y) div b"
    using \<open>b>1\<close> by (metis (no_types) One_nat_def diff_Suc_Suc gr_implies_not0 minus_mod_eq_div_mult 
                 mod_mult_self1_is_0 nonzero_mult_div_cancel_right)
  then show "Suc (b * y) div b ^ t mod b = b * y div b ^ t mod b"
    using \<open>t>0\<close> by (metis Suc_pred div_mult2_eq power_Suc)
qed

text \<open>Represent natural numbers in their base-b digitwise expansion\<close>

lemma aux3_digit_gen_sum_repr:
  assumes "d < b^r" and "b > 1"
  shows "nth_digit (a*b^r + d) r b = nth_digit (a*b^r) r b"
  using \<open>b>1\<close> by (auto simp: nth_digit_def assms)

lemma aux2_digit_gen_sum_repr:
  assumes "n < b^c" "r < c"
  shows "nth_digit (a*b^c+n) r b = nth_digit n r b"
proof -
  have [simp]: \<open>a*b ^ c div b ^ r = a*b ^ (c - r)\<close>
    using assms(2)
    by (auto simp: less_iff_Suc_add
          monoid_mult_class.power_add ac_simps)
  show ?thesis
    using assms
    by (auto simp add: nth_digit_def
            div_plus_div_distrib_dvd_left
            le_imp_power_dvd
          simp flip: mod_add_left_eq) 
qed

lemma aux1_digit_gen_sum_repr:
assumes "n < b^c" "r<c" and "b>1"
shows "nth_digit (\<Sum>k<c.((nth_digit n k b)*b^k)) r b = nth_digit n r b"
proof-
  define a where "a \<equiv> (\<Sum>k=0..<Suc(r).((nth_digit n k b)*b^k))"
  define d where "d \<equiv> (\<Sum>k=Suc(r)..<c.((nth_digit n k b)*b^k))"
  define e where "e \<equiv> (\<Sum>k=Suc r..<c.((nth_digit n k b)*b^(k-Suc(r))))"
  define f where "f \<equiv> (\<Sum>k=0..<r.((nth_digit n k b)*b^k))"
  have ad: "(\<Sum>k=0..<c.((nth_digit n k b)*b^k)) = a + d"
    using a_def d_def assms
    by (metis (no_types, lifting) Suc_leI a_def assms(2) d_def sum.atLeastLessThan_concat zero_le)
  have "d = (\<Sum>k=Suc(r)..<c.(b^(Suc r) * (nth_digit n k b * b^(k - Suc r))))" 
    using d_def apply (auto) apply (rule sum.cong; auto simp: algebra_simps)
    by (metis add_Suc le_add_diff_inverse power_Suc power_add)
  hence d2r: "d = b^Suc(r)*e" using d_def e_def sum_distrib_left[of "b^(Suc r)" 
                          "\<lambda>k. (nth_digit n k b) *  b^(k - Suc r)" "{Suc r..<c}"] by auto
  have "(\<Sum>k<c.((nth_digit n k b)*b^k)) = a +b^Suc(r)*e" 
    by (simp add: d2r ad lessThan_atLeast0)
  moreover have "(\<Sum>k=0..<Suc(r).((nth_digit n k b)*b^k)) < b ^ Suc(r)" using assms
  proof(induct r)
    case 0
    then show ?case
    proof -
      have "nth_digit n 0 b < b" 
        using nth_digit_bounded[of "b" "n" "0"] \<open>b>1\<close> by auto
      then show ?thesis
        by simp
    qed
    next
      case (Suc r)
      have r2: "(nth_digit n (Suc r) b) * b ^ Suc(r) \<le> (b-1) * b ^ Suc(r)" 
        using nth_digit_bounded[of "b" "n" "Suc r"] \<open>b>1\<close> by auto
      moreover have "(\<Sum>k=0..<Suc(r).((nth_digit n k b)*b^k)) < b ^ Suc(r)" 
        using Suc.hyps using Suc.prems(2) Suc_lessD assms(1) \<open>b>1\<close> by blast
      ultimately have "(nth_digit n (Suc r) b) * b ^ Suc(r) 
                     + (\<Sum>k=0..<Suc(r).((nth_digit n k b)*b^k)) < b ^ Suc (Suc r)" 
        using assms(3) mult_eq_if by auto 
      then show ?case by auto
    qed
    hence "a < b^Suc(r)" using a_def by blast
  ultimately have ar:"nth_digit (a+d) r b = nth_digit a r b" using d2r
    by (metis (no_types, lifting) aux2_digit_gen_sum_repr lessI semiring_normalization_rules(24) 
              semiring_normalization_rules(7))
    (* Second part of proof *)
  have ab: "a =(nth_digit n r b)*b^r + f" using a_def f_def d_def by simp
  have "(\<Sum>k=0..<r.((nth_digit n k b)*b^k)) < b^r"
  proof(induct r)
    case 0
      then show ?case by auto
    next
      case (Suc r)
      have r2: "nth_digit n r b * b ^ r \<le> (b-1) * b ^ r" 
        using nth_digit_bounded[of "b"] \<open>b>1\<close> by auto
      have "(\<Sum>k = 0..<r. nth_digit n k b * b ^ k) < b^r" using Suc.hyps by auto
      then show ?case using "r2" assms(3) mult_eq_if by auto
  qed
  hence f: "f < b^r" using f_def by blast
  hence "nth_digit a r b = (nth_digit (nth_digit n r b * b^r) r b)" 
    using ab aux3_digit_gen_sum_repr \<open>b>1\<close> by simp
  hence "nth_digit a r b = nth_digit n r b" 
    using nth_digit_def \<open>b>1\<close> by simp
  then show ?thesis using ar a_def by (simp add: ad lessThan_atLeast0)
qed

lemma aux_gen_b_factor: "a > 0 \<Longrightarrow> b>1 \<Longrightarrow> \<exists>k c. ((a::nat) = (b^k) * c \<and> \<not>(c mod b = 0))"
proof(induction  a rule: full_nat_induct)
  case (1 n)
  show ?case 
  proof(cases "n mod b = 0")
    case True
    then obtain t where n_def: "n = b * t" by blast
    hence "t < n"
      using 1 by auto 
    with 1 have ih:"\<exists>r s. t = b^r * s \<and> \<not>(s mod b = 0)"
      by (metis Suc_leI gr0I mult_0_right n_def) 
    hence "\<exists>r s. n = b^(Suc r) * s" using n_def by auto
    then show ?thesis by (metis ih mult.commute mult.left_commute n_def power_Suc)
  next
    case False
    then show ?thesis by (metis mult.commute power_0 power_Suc power_Suc0_right)
  qed
qed

lemma aux0_digit_wise_gen_equiv:
  assumes "b>1" and a_geq_0: "a > 0"
  shows "(\<exists>k. nth_digit a k b \<noteq> 0)"
proof(cases "a mod b = 0")
  case True
  hence "\<exists>k c. a = (b^k) * c \<and> \<not>(c mod b = 0)"
    using aux_gen_b_factor a_geq_0 assms by simp
  then obtain c k where ck_cond:"a = (b^k) * c \<and> \<not>(c mod b = 0)" by blast
  hence c_cond:"c = a div (b^k)" using a_geq_0 by auto
  hence digi_b:"nth_digit c 0 b \<noteq> 0"
    using ck_cond nth_digit_def by force
  hence "nth_digit a k b = nth_digit c 0 b" 
    using nth_digit_def c_cond by simp
  hence "nth_digit a k b \<noteq> 0" using digi_b by simp
  then show ?thesis by blast next
  case False
  then show ?thesis
    by (metis div_by_1 nth_digit_def power.simps(1))
qed

lemma aux1_digit_wise_gen_equiv:
  assumes "b>1"
  shows "(\<forall>k.(nth_digit a k b = 0)) \<longleftrightarrow> a = 0" (is "?P \<longleftrightarrow> ?Q")
proof
  assume "?Q"
  then show "?P" by (simp add: nth_digit_def)
next
  {
    assume a_neq_0:"\<not>?Q"
    hence "a > 0" by blast
    hence "\<not>?P" using aux0_digit_wise_gen_equiv \<open>b>1\<close> by auto
  } from this show "?P \<Longrightarrow> ?Q" by blast
qed

lemma aux2_digit_wise_gen_equiv: "(\<forall>r<k. nth_digit a r b = 0) \<longrightarrow> (a mod b^k = 0)"
proof(induct k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then show ?case apply(auto simp add: nth_digit_def)
    using dvd_imp_mod_0 dvd_mult_div_cancel dvd_refl
        lessI minus_mod_eq_div_mult minus_mod_eq_mult_div mult_dvd_mono
    by (metis mod_0_imp_dvd)
qed

text \<open>Two numbers are the same if and only if their digits are the same\<close>

lemma digit_wise_gen_equiv: 
  assumes "b>1"
  shows "(x = y) \<longleftrightarrow> (\<forall>k. nth_digit x k b = nth_digit y k b)" (is "?P \<longleftrightarrow> ?Q")
proof
  assume "?P"
  then show "?Q" by simp
next{
    assume notP: "\<not>?P"
    have"\<not>(\<forall>k. nth_digit x k b = nth_digit y k b)" if xy: "x<y" for x y
    proof-
      define c::nat where "c = y - x"
      have y: "x+c=y" by (auto simp add: c_def "xy" less_imp_le)
      have  "\<exists>k.(nth_digit c k b \<noteq> 0)" 
        using nth_digit_def \<open>b>1\<close> aux0_digit_wise_gen_equiv 
        by (metis c_def that zero_less_diff)
      then obtain k where k1:"nth_digit c k b \<noteq> 0" 
                      and k2:"\<forall>r < k. (nth_digit c r b = 0)"
        apply(auto dest: obtain_smallest) done
      hence cr0: "\<forall>r < k. (nth_digit c r b = 0)" by (simp add: nth_digit_def)
      from aux2_digit_wise_gen_equiv cr0 have "c mod b^k = 0" by auto
      hence "x div b ^ k mod b \<noteq> y div b ^ k mod b"
        using y k1 \<open>b>1\<close> aux1_digit_wise_gen_equiv[of "b" "c"] nth_digit_def apply auto
                proof - (* this ISAR proof was found by sledgehammer  *)
                        fix ka :: nat
                        assume a1: "b ^ k dvd c"
                        assume a2: "x div b ^ k mod b = (x + c) div b ^ k mod b"
                        assume a3: "y = x + c"
                        assume a4: "\<And>num k base. nth_digit num k base 
                                    = num div base ^ k mod base"
                have f5: "\<forall>n na. (na::nat) + n - na = n"
                  by simp
                  have f6: "x div b ^ k + c div b ^ k = y div b ^ k"
                    using a3 a1 by (simp add: add.commute div_plus_div_distrib_dvd_left)
                  have f7: "\<forall>n. (x div b ^ k + n) mod b = (y div b ^ k + n) mod b"
                    using a3 a2 by (metis add.commute mod_add_right_eq)
                  have "\<forall>n na nb. ((nb::nat) mod na + n - (nb + n) mod na) mod na = 0"
                    by (metis (no_types) add.commute minus_mod_eq_mult_div mod_add_right_eq 
                        mod_mult_self1_is_0)
                  then show "c div b ^ ka mod b = 0"
                    using f7 f6 f5 a4 by (metis (no_types) k1)
                qed
      then show ?thesis by (auto simp add: nth_digit_def)
    qed
    from this [of x y] this [of y x] notP 
      have "\<forall>k. nth_digit x k b = nth_digit y k b \<Longrightarrow> x = y" apply(auto)
      using linorder_neqE_nat by blast}then show "?Q ==> ?P" by auto
qed

text \<open>A number is equal to the sum of its digits multiplied by powers of two\<close>

lemma digit_gen_sum_repr:
  assumes "n < b^c" and "b>1"
  shows "n = (\<Sum>k < c.((nth_digit n k b) * b^k))"
proof -
  have 1: "(c\<le>k \<longrightarrow> n<b^k)" for k using assms less_le_trans by fastforce
  hence nik: "c\<le>k \<longrightarrow> (nth_digit n k b = 0)" for k 
    by (auto simp add: nth_digit_def)
  have "(\<Sum>r<c.((nth_digit n r b)*b^r))<b^c" apply(induct c, auto)
    subgoal for c
    proof -
      assume IH: "(\<Sum>r<c. nth_digit n r b * b ^ r) < b ^ c"
      have bound: "(nth_digit n c b) * b ^ c \<le> (b-1) * b^c" 
        using nth_digit_bounded \<open>b>1\<close> by auto
      thus ?thesis using assms IH
        by (metis (no_types, lifting) bound add_mono_thms_linordered_field(1) 
            add_mono_thms_linordered_field(5) le_less mult_eq_if not_one_le_zero)
    qed
    done
  hence "k\<ge>c \<longrightarrow> nth_digit (\<Sum>r<c.((nth_digit n r b)*b^r)) k b = 0" for k
    apply(auto simp add: nth_digit_def) using less_le_trans assms(2) by fastforce 
  hence "\<forall>r\<ge>c.(nth_digit n r b 
    = nth_digit (\<Sum>k<c.((nth_digit n k b)*b^k)) r b)" by (simp add: nik)
  moreover have "\<forall>r<c.(nth_digit n r b 
               = nth_digit (\<Sum>k<c.((nth_digit n k b) * b^k)) r b)" 
    using aux1_digit_gen_sum_repr assms by simp
  ultimately have "\<forall>r. nth_digit (\<Sum>k<c.((nth_digit n k b)*b^k)) r b 
                    = nth_digit n r b" by (metis not_less)
  then show ?thesis 
    using digit_wise_gen_equiv[of "b" "(\<Sum>k<c. nth_digit n k b * b ^ k)" "n"] \<open>b>1\<close> by auto 
qed

lemma digit_gen_sum_repr_variant:
  assumes "b>1"
  shows "n = (\<Sum>k<n.((nth_digit n k b)*b^k))"
proof-
  have "n < b^n" using \<open>b>1\<close> apply (induct n, auto) by (simp add: less_trans_Suc) 
  then show ?thesis using digit_gen_sum_repr \<open>b>1\<close> by auto
qed

lemma digit_gen_sum_index_variant:
  assumes "b>1" shows "r>n \<Longrightarrow> 
  (\<Sum>k< n.((nth_digit n k b )*b^k)) = (\<Sum>k< r.(nth_digit n k b)*b^k)"
proof -
  assume "r>n"
  have "b^r > r" for r using \<open>b>1\<close>  by (induction r, auto simp add: less_trans_Suc)
  hence powb: "\<forall>r.(r>n \<longrightarrow> b^r>n)" using less_trans by auto
  hence "r > n \<longrightarrow> (nth_digit n r b = 0)" for r 
    by (auto simp add: nth_digit_def)
  hence "r > n \<longrightarrow> (nth_digit n r b) * b^r = 0" for r by auto
  then show ?thesis using digit_gen_sum_repr digit_gen_sum_repr_variant powb \<open>n < r\<close> assms by auto
qed

text \<open>@{text nth_digit} extracts coefficients from a base-b digitwise expansion\<close>

lemma nth_digit_gen_power_series:
  fixes c b k q
  defines "b \<equiv> 2^(Suc c)"
  assumes bound: "\<forall>k. (f k) < b" (* < 2^c makes proof easier, but is too strong for const f *)
  shows "nth_digit (\<Sum>k=0..q. (f k) * b^k) t b = (if t\<le>q then (f t) else 0)"
proof (induction q arbitrary: t)
  case 0
  have "b>1" using b_def
    using one_less_numeral_iff power_gt1 semiring_norm(76) by blast
  have "f 0 < b" using bound by auto
  hence "t>0 \<longrightarrow> f 0 < b^t" using \<open>b>1\<close>
    using bound less_imp_le_nat less_le_trans by (metis self_le_power)
  thus ?case using nth_digit_def bound by auto 
next
  case (Suc q)
  thus ?case 
  proof (cases "t \<le> Suc q")
    case True
    have f_le_bound: "f k \<le> b-1" for k using bound apply auto 
      by (metis Suc_pred b_def less_Suc_eq_le numeral_2_eq_2 zero_less_Suc zero_less_power)
    have series_bound: "(\<Sum>k = 0..q. f k * b ^ k) < b^(Suc q)"
      apply (induct q)
        subgoal using bound by (simp add: less_imp_le_nat) 
        subgoal for q
          proof -
            assume asm: "(\<Sum>k = 0..q. f k * b ^ k) < b ^ Suc q"
            have "(\<Sum>k = 0..q. f k * b ^ k) + f (Suc q) * (b * b ^ q) 
                \<le> (\<Sum>k = 0..q. f k * b ^ k) + (b-1) * (b * b ^ q)" using f_le_bound by auto  
            also have "... < b^(Suc q) + (b-1) * (b * b ^ q)" using asm by auto
            also have "... \<le> b * b * b^q" apply auto
              by (metis One_nat_def Suc_neq_Zero b_def eq_imp_le mult.assoc mult_eq_if numerals(2) 
                  power_not_zero)
            finally show ?thesis using asm by auto
          qed 
        done
    hence "nth_digit ((\<Sum>k = 0..q. f k * b ^ k) + f (Suc q) * (b * b ^ q)) t b = f t" 
      using Suc nth_digit_def apply (cases "t = Suc q", auto)
        subgoal using  Suc_n_not_le_n add.commute add.left_neutral b_def bound div_mult_self1 
              less_imp_le_nat less_mult_imp_div_less mod_less not_one_le_zero one_less_numeral_iff 
              one_less_power power_Suc semiring_norm(76) zero_less_Suc by auto
        subgoal 
          proof -
            assume "t \<noteq> Suc q"
            hence "t < Suc q" using True by auto
            hence "nth_digit (f (Suc q) * b ^ Suc q + (\<Sum>k = 0..q. f k * b ^ k)) t b 
                = nth_digit (\<Sum>k = 0..q. f k * b ^ k) t b"
              using aux2_digit_gen_sum_repr[of "\<Sum>k = 0..q. f k * b ^ k" "b" "Suc q" "t" 
                    "f (Suc q)"] series_bound by auto
            hence "((\<Sum>k = 0..q. f k * b ^ k) + f (Suc q) * (b * b ^ q)) div b ^ t mod b
                  = (\<Sum>k = 0..q. f k * b ^ k) div b ^ t mod b" 
              using nth_digit_def by (auto simp:add.commute)
            thus ?thesis using Suc[of "t"] nth_digit_def True \<open>t \<noteq> Suc q\<close> by auto
          qed
        done
    thus ?thesis using True by auto
  next
    case False (* t > Suc q *)
    hence "t \<ge> Suc (Suc q)" by auto
    have f_le_bound: "f k \<le> b-1" for k using bound apply auto 
      by (metis Suc_pred b_def less_Suc_eq_le numeral_2_eq_2 zero_less_Suc zero_less_power)
    have bound: "(\<Sum>k = 0..q. f k * b ^ k) < b^(Suc q)" for q
      apply (induct q)
        subgoal using bound by (simp add: less_imp_le_nat) 
        subgoal for q
          proof -
            assume asm: "(\<Sum>k = 0..q. f k * b ^ k) < b ^ Suc q"
            have "(\<Sum>k = 0..q. f k * b ^ k) + f (Suc q) * (b * b ^ q) 
                \<le> (\<Sum>k = 0..q. f k * b ^ k) + (b-1) * (b * b ^ q)" using f_le_bound by auto  
            also have "... < b^(Suc q) + (b-1) * (b * b ^ q)" using asm by auto
            also have "... \<le> b * b * b^q" apply auto
              by (metis One_nat_def Suc_neq_Zero b_def eq_imp_le mult.assoc mult_eq_if numerals(2) 
                  power_not_zero)
            finally show ?thesis using asm by auto
          qed 
        done
    have "(\<Sum>k = 0..q. f k * b ^ k) + f (Suc q) * (b * b ^ q) < (b ^ Suc (Suc q))" 
      using bound[of "Suc q"] by auto 
    also have "... \<le> b^t" using \<open>t \<ge> Suc (Suc q)\<close> 
      apply auto by (metis b_def nat_power_less_imp_less not_le numeral_2_eq_2 power_Suc 
                     zero_less_Suc zero_less_power)
    finally show ?thesis using \<open>t \<ge> Suc (Suc q)\<close> bound[of "Suc q"] nth_digit_def by auto
  qed
qed

text \<open>Equivalence condition for the @{text nth_digit} function \<^cite>\<open>"h10lecturenotes"\<close>
      (see equation 2.29)\<close>

lemma digit_gen_equiv:
  assumes "b>1"
  shows "d = nth_digit a k b \<longleftrightarrow> (\<exists>x.\<exists>y.(a = x * b^(k+1) + d*b^k +y \<and> d < b \<and> y < b^k))"
  (is "?P \<longleftrightarrow> ?Q")
proof
  assume p: ?P
  then show ?Q
  proof(cases "k<a")
    case True

    (* 3rd condition *)
    have "(\<Sum>i<k.((nth_digit a i b)*b^i)) < b^k"
    proof(induct k)
      case 0
      then show ?case by auto
    next
      case (Suc k)
      have "(\<Sum>i<Suc k. nth_digit a i b * b ^ i) = (nth_digit a k b) * b^k  
            + (\<Sum>i<k.((nth_digit a i b)*b^i))" by simp
      moreover have " (nth_digit a k b) * b^k \<le> (b-1) * b^ k"
        using assms mult_le_mono nth_digit_bounded by auto
      moreover have "(\<Sum>i<k.((nth_digit a i b)*b^i)) < b ^ (Suc k)" 
        using Suc.hyps assms order.strict_trans2 by fastforce
      ultimately show ?case using assms using Suc.hyps mult_eq_if by auto
    qed
    moreover define y where "y = (\<Sum>i<k.((nth_digit a i b)*b^i))"
    ultimately have 3: "y < b^k"  by blast

    (* 2nd condition*)
     have 2: "d < b" using nth_digit_bounded[of b a k] p assms by linarith

    (* 1st condition *)
    define x where "x =  (\<Sum>i=Suc k..<a. ((nth_digit a i b)*b^(i-Suc k)))"
    have "a = (\<Sum>i<a.((nth_digit a i b)*b^i))" using assms digit_gen_sum_repr_variant by blast
    hence s:"a = y + d * b^k  
            + (\<Sum>i=Suc k..<a.((nth_digit a i b)*b^i))" using True y_def p
      by (metis (no_types, lifting) Suc_leI atLeast0LessThan gr_implies_not0 
          linorder_not_less sum.atLeastLessThan_concat sum.lessThan_Suc)
    have "(\<Sum>n = Suc k..<a. nth_digit a n b * b ^ (n - Suc k) * b ^ Suc k) 
          =  (\<Sum>i = Suc k..<a. nth_digit a i b * b ^ i)"
      apply (rule sum.cong; auto simp: algebra_simps)
      by (metis Suc_le_lessD Zero_not_Suc add_diff_cancel_left' diff_Suc_1 diff_Suc_Suc 
          less_imp_Suc_add power_add power_eq_if)
    hence "x * b^(k+1) = (\<Sum>i=Suc k..<a.((nth_digit a i b)*b^i))" 
      using x_def sum_distrib_right[of "\<lambda>i. (nth_digit a i b) *  b^(i - Suc k)"] by simp
    hence "a = x * b^(k+1) + d*b^k +y" using s by auto
    thus ?thesis using 2 3 by blast
  next
    case False
    then have "a < b^k" using assms power_gt_expt[of b k] by auto
    moreover have "d = 0" by (simp add: calculation nth_digit_def p)
    ultimately show ?thesis
      using assms by force   
  qed
next
  assume ?Q
  then obtain x y where conds: "a = x * b^(k+1) + d*b^k +y \<and> d < b \<and> y < b^k" by auto
  hence "nth_digit a k b = nth_digit(x * b^(k+1) + d*b^k) k b"
    using aux3_digit_gen_sum_repr[of y b "k" "x*b + d"] assms by (auto simp: algebra_simps)
  hence "nth_digit a k b = nth_digit(d*b^k) k b" 
    using aux2_digit_gen_sum_repr[of "d*b^k" "b" "k+1" k x] conds by auto
  then show ?P using conds nth_digit_def by simp
qed


end
