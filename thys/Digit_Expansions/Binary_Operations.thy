theory Binary_Operations
  imports Bits_Digits Carries
begin

section \<open>Digit-wise Operations\<close>

subsection \<open>Binary AND\<close>

fun bitAND_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" (infix "&&" 64) where
  "0 && _ = 0" |
  "m && n = 2 * ((m div 2) && (n div 2)) + (m mod 2) * (n mod 2)"

lemma bitAND_zero[simp]: "n = 0 \<Longrightarrow> m && n = 0"
  by (induct m n rule:bitAND_nat.induct, auto)

lemma bitAND_1: "a && 1 = (a mod 2)"
  by (induction a; auto)

lemma bitAND_rec: "m && n = 2 * ((m div 2) && (n div 2)) + (m mod 2) * (n mod 2)"
  by (cases m; simp_all)

lemma bitAND_commutes:"m && n = n && m"
  by (induct m n rule: bitAND_nat.induct, simp) (metis bitAND_rec mult.commute)

lemma nth_digit_0: "x \<le> 1 \<Longrightarrow> nth_bit x 0 = x" by (simp add: nth_bit_def)

lemma bitAND_zeroone: "a \<le> 1 \<Longrightarrow> b \<le> 1 \<Longrightarrow> a && b \<le> 1"
  using nth_bit_def nth_digit_0 nat_le_linear bitAND_nat.elims
  by (metis (no_types, lifting) One_nat_def add.left_neutral bitAND_zero div_less le_zero_eq lessI
             mult.right_neutral mult_0_right not_mod2_eq_Suc_0_eq_0 numeral_2_eq_2)

lemma aux1_bitAND_digit_mult:
  fixes a b c :: nat
  shows "k > 0 \<and> a mod 2 = 0 \<and> b \<le> 1 \<Longrightarrow> (a + b) div 2^k = a div 2^k"
  by (induction k, auto)
     (metis One_nat_def add_cancel_left_right div_mult2_eq even_succ_div_two le_0_eq le_Suc_eq)

lemma bitAND_digit_mult:"(nth_bit (a && b) k) = (nth_bit a k) * (nth_bit b k)"
proof(induction k arbitrary: a b)
  case 0
  show ?case
    using nth_bit_def
    by auto (metis (no_types, opaque_lifting) Groups.add_ac(2) bitAND_rec mod_mod_trivial
              mod_mult_self2 mult_numeral_1_right mult_zero_right not_mod_2_eq_1_eq_0 numeral_One)
next
  case (Suc k)
  have "nth_bit (a && b) (Suc k)
        = (2 * (a div 2 && b div 2) + a mod 2 * (b mod 2)) div 2 ^(Suc k) mod 2"
    using bitAND_rec by (metis nth_bit_def)

  moreover have "(a mod 2) * (b mod 2) < (2 ^ Suc(k))"
    by (metis One_nat_def lessI mult_numeral_1_right mult_zero_right not_mod_2_eq_1_eq_0
              numeral_2_eq_2 numeral_One power_gt1 zero_less_numeral zero_less_power)

  ultimately have "nth_bit (a && b) (Suc k) = (2 * (a div 2 && b div 2)) div 2 ^(Suc k) mod 2"
    using aux1_bitAND_digit_mult
    by (metis le_numeral_extra(1) le_numeral_extra(4) mod_mult_self1_is_0 mult_numeral_1_right
              mult_zero_right not_mod_2_eq_1_eq_0 numeral_One zero_less_Suc)

  then have "nth_bit (a && b) (Suc k) = (nth_bit (a div 2 && b div 2) k)"
    by (auto simp add: nth_bit_def)

  then have "nth_bit (a && b) (Suc k) = (nth_bit (a div 2) k) * (nth_bit (b div 2) k)"
    using Suc
    by presburger

  then show ?case
    by (metis div_mult2_eq nth_bit_def power_Suc)
qed

lemma bitAND_single_bit_mult_equiv: "a \<le> 1 \<Longrightarrow> b \<le> 1 \<Longrightarrow> a * b = a && b"
  using bitAND_digit_mult[of a b 0] bitAND_zeroone by (auto simp: nth_digit_0)

lemma bitAND_mult_equiv:
  "(\<forall>k. (nth_bit c k) = (nth_bit a k) * (nth_bit b k)) \<longleftrightarrow> c = a && b" (is "?P \<longleftrightarrow> ?Q")
proof
  assume "?Q"
  then show "?P" using bitAND_digit_mult by simp
next
  assume "?P"
  then show "?Q" using bitAND_digit_mult digit_wise_equiv by presburger
qed

lemma bitAND_linear:
  fixes k::nat
  shows "(b < 2^k) \<and> (d < 2^k) \<Longrightarrow> (a * 2^k + b) && (c * 2^k + d) = (a && c) * 2^k + (b && d)"
proof(induction k arbitrary: a b c d)
  case 0
  then show ?case by simp
next
  case (Suc k)
  define m where "m = a * 2^(Suc k) + b"
  define n where "n = c * 2^(Suc k) + d"

  have "m && n = 2 * (bitAND_nat (m div 2) (n div 2)) + (m mod 2) * (n mod 2)"
    using bitAND_rec
    by blast

  moreover have "d mod 2 = n mod 2 \<and> b mod 2 = m mod 2"
    by (metis m_def n_def add.commute mod_mult_self2 power_Suc semiring_normalization_rules(19))

  ultimately have f0:"m && n
                      = 2 * ((a * 2^k + (b div 2)) && (c * 2^k + (d div 2))) + (b mod 2)*(d mod 2)"
    by (metis add.commute div_mult_self2 m_def n_def power_Suc semiring_normalization_rules(19)
              zero_neq_numeral)

  have "b div 2 < (2 ^ k) \<and> d div 2 < (2 ^ k)"
    using Suc.prems
    by auto

  then have f1:"m && n
                = ((a && c) * 2^(Suc k)) + 2 * ((b div 2) && (d div 2)) + (b mod 2) * (d mod 2)"
    using f0 Suc.IH
    by simp

  have "b && d = 2 * ((b div 2) && (d div 2)) + (b mod 2) * (d mod 2)"
    using bitAND_rec
    by blast

  then show ?case
    using f1
    by (auto simp add: m_def n_def)
qed

subsection \<open>Binary orthogonality\<close>
text \<open>cf. \<^cite>\<open>h10lecturenotes\<close> section 2.6.1 on "Binary orthogonality"\<close>
text \<open>The following definition differs slightly from the one in the paper. However, we later prove the 
     equivalence of the two definitions.\<close>

fun orthogonal :: "nat => nat => bool" (infix "\<bottom>" 49) where
  "(orthogonal a b) = (a && b = 0)"

lemma ortho_mult_equiv: "a \<bottom> b \<longleftrightarrow> (\<forall>k. (nth_bit a k) * (nth_bit b k) = 0)" (is "?P \<longleftrightarrow> ?Q")
proof
  assume "?P"
  then show "?Q" using bitAND_digit_mult nth_bit_def by (metis div_0 mod_0 orthogonal.simps)
next
  assume "?Q"
  then show "?P" using bitAND_mult_equiv nth_bit_def by (metis div_0 mod_0 orthogonal.simps)
qed

lemma aux1_1_digit_lt_linear:
  assumes "b < 2^r" "k \<ge> r"
  shows  "bin_carry (a*2^r) b k = 0"
proof-
  have "b < 2^r \<longrightarrow>(a*2^r) \<bottom> b"
  proof(induct a  b rule: bitAND_nat.induct)
    case (1 uu)
    then show ?case by simp
  next
    case (2 v n)
    show ?case apply auto using bitAND_linear[of n r 0 0 "Suc(v)"] bitAND_commutes by auto
  qed
  then show ?thesis using ortho_mult_equiv no_carry_mult_equiv assms(1) by auto
qed

lemma aux1_digit_lt_linear:
  assumes "b < 2^r" and "k \<ge> r"
  shows "(a*2^r + b) \<exclamdown> k = (a*2^r) \<exclamdown> k"
proof-
  have "b div 2 ^ k = 0" using assms by (simp add: order.strict_trans2)
  moreover have "(a * 2 ^ r mod 2 ^ k +  b mod 2 ^ k) div 2 ^ k = 0" using assms
  proof-
    have "bin_carry (a*2^r) b k = 0" using assms aux1_1_digit_lt_linear by auto
    then show ?thesis using assms by (auto simp add: bin_carry_def)
  qed
  ultimately show ?thesis
    by (auto simp add: nth_bit_def div_add1_eq[of "a*2^r" "b" "2^k"])
qed

lemma aux_digit_shift: "(a * 2^t) \<exclamdown> (l+t) = a \<exclamdown> l"
  using nth_bit_def
  by (induct l; auto)
     (smt div_mult2_eq mult.commute nonzero_mult_div_cancel_right power_add power_not_zero zero_neq_numeral)

lemma aux_digit_lt_linear:
  assumes b: "b < (2::nat)^t"
  assumes d: "d < (2::nat)^t"
  shows "(a * 2^t + b) \<exclamdown> k \<le> (c * 2^t + d) \<exclamdown> k \<longleftrightarrow> ((a * 2^t) \<exclamdown> k \<le> (c * 2^t) \<exclamdown> k \<and> b \<exclamdown> k \<le> d \<exclamdown> k)"
proof (cases "k < t")
  case True
  from True have "(a * 2^t + b) \<exclamdown> k = b \<exclamdown> k"
    using aux2_digit_sum_repr assms(1) by auto
  moreover from True have "(c * 2^t + d) \<exclamdown> k = d \<exclamdown> k"
    using aux2_digit_sum_repr assms(2) by auto
  moreover from True have "(a * 2^t) \<exclamdown> k = 0"
    using aux2_digit_sum_repr[of "0"] nth_bit_def by auto
  ultimately show ?thesis
    using aux2_digit_sum_repr assms by auto
next
  case False
  from False have "(a * 2^t + b) \<exclamdown> k = (a * 2^t) \<exclamdown> k"
    using aux1_digit_lt_linear assms(1) by auto
  moreover from False have "(c * 2^t + d) \<exclamdown> k = (c * 2^t) \<exclamdown> k" using aux1_digit_lt_linear assms(2) by auto
  moreover from False have "b \<exclamdown> k = 0"
    using aux1_digit_lt_linear[of _ _ _ "0"] nth_bit_def assms(1) by auto
  ultimately show ?thesis by auto
qed

lemma aux2_digit_lt_linear:
  fixes a b c d t l :: nat
  shows "\<exists>k. (a * 2^t) \<exclamdown> k \<le> (c * 2^t) \<exclamdown> k \<longrightarrow> a \<exclamdown> l \<le> c \<exclamdown> l"
proof -
  define k where "k = l + t"
  have "(a * 2^t) \<exclamdown> k = a \<exclamdown> l" using nth_bit_def k_def
    using aux_digit_shift by auto
  moreover have "(c * 2^t) \<exclamdown> k = c \<exclamdown> l" using nth_bit_def k_def
    using aux_digit_shift by auto
  ultimately show ?thesis by metis
qed

lemma aux3_digit_lt_linear:
  fixes a b c d t k :: nat
  shows "\<exists>l. a \<exclamdown> l \<le> c \<exclamdown> l \<longrightarrow> (a * 2^t) \<exclamdown> k \<le> (c * 2^t) \<exclamdown> k"
proof (cases "k < t")
  case True
  hence "(a * 2^t) \<exclamdown> k = 0"
    using aux2_digit_sum_repr[of "0"] nth_bit_def by auto
  then show ?thesis by auto
next
  case False
  define l where "l = k - t"
  hence k: "k = l + t" using False by auto
  have "(a * 2^t) \<exclamdown> k = a \<exclamdown> l" using nth_bit_def l_def
    using aux_digit_shift k by auto
  moreover have "(c * 2^t) \<exclamdown> k = c \<exclamdown> l" using nth_bit_def l_def
    using aux_digit_shift k by auto
  ultimately show ?thesis by auto
qed

lemma digit_lt_linear:
  fixes a b c d t :: nat
  assumes b: "b < (2::nat)^t"
  assumes d: "d < (2::nat)^t"
  shows "(\<forall>k. (a * 2^t + b) \<exclamdown> k \<le> (c * 2^t + d) \<exclamdown> k) \<longleftrightarrow> (\<forall>l. a \<exclamdown> l \<le> c \<exclamdown> l \<and> b \<exclamdown> l \<le> d \<exclamdown> l)"
proof -
  have shift: "(\<forall>k. (a * 2^t) \<exclamdown> k \<le> (c * 2^t) \<exclamdown> k) \<longleftrightarrow> (\<forall>l. a \<exclamdown> l \<le> c \<exclamdown> l)" (is "?P \<longleftrightarrow> ?Q")
  proof
    assume P: ?P
    show ?Q using P aux2_digit_lt_linear by auto
  next
    assume Q: ?Q
    show ?P using Q aux3_digit_lt_linear by auto
  qed

  have main: "(\<forall>k. (a * 2^t + b) \<exclamdown> k \<le> (c * 2^t + d) \<exclamdown> k \<longleftrightarrow> ((a * 2^t) \<exclamdown> k \<le> (c * 2^t) \<exclamdown> k \<and> b \<exclamdown> k \<le> d \<exclamdown> k))"
    using aux_digit_lt_linear b d by auto

  from main shift show ?thesis by auto
qed

text \<open>Sufficient bitwise (digitwise) condition for the non-strict standard order of natural numbers\<close>

lemma digitwise_leq: 
  assumes "b>1"
  shows "\<forall>t. nth_digit x t b \<le> nth_digit y t b \<Longrightarrow> x \<le> y"
proof -
  assume asm: "\<forall>t. nth_digit x t b \<le> nth_digit y t b"
  define r where "r \<equiv>(if x>y then x else y)"
  have "x = (\<Sum>k<x. (nth_digit x k b) * b ^ k)" 
    using digit_gen_sum_repr_variant \<open>b>1\<close> by auto
  hence x: "x = (\<Sum>k=0..<r. (nth_digit x k b) * b ^ k)" 
    using atLeast0LessThan r_def digit_gen_sum_index_variant \<open>b>1\<close> 
    by (metis (full_types) linorder_neqE_nat)
  have "y = (\<Sum>k<y. (nth_digit y k b) * b ^ k)" 
    using digit_gen_sum_repr_variant \<open>b>1\<close> by auto
  hence y: "y = (\<Sum>k=0..<r. (nth_digit y k b) * b ^ k)"
    using atLeast0LessThan r_def digit_gen_sum_index_variant \<open>b>1\<close> by auto
  show ?thesis using asm x y 
    sum_mono[of "{0..<r}" "\<lambda>k. nth_digit x k b * b^k" "\<lambda>k. nth_digit y k b * b^k"] 
    by auto
qed

subsection \<open>Binary masking\<close>

text \<open>Preliminary result on the standard non-strict of natural numbers\<close>

lemma bitwise_leq: "(\<forall>k. a \<exclamdown> k \<le>  b \<exclamdown> k) \<longrightarrow> a \<le> b"
  using digitwise_leq[of 2] by (simp add: nth_digit_base2_equiv)

text \<open>cf. \<^cite>\<open>h10lecturenotes\<close> section 2.6.2 on "Binary Masking"\<close>
text \<open>Again, the equivalence to the definition there will be proved in a later lemma.\<close>

fun masks :: "nat => nat => bool" (infix "\<preceq>" 49) where
  "masks 0 _ = True" |
  "masks a b = ((a div 2 \<preceq> b div 2) \<and> (a mod 2 \<le> b mod 2))"

lemma masks_substr: "a \<preceq> b \<Longrightarrow> (a div (2^k) \<preceq> b div (2^k))"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  moreover
  {
    fix ka :: nat
    assume a1: "a div 2 ^ ka \<preceq> b div 2 ^ ka"

    have f2: "\<forall>n na nb. (nb::nat) div na div n = nb div n div na"
      by (metis (no_types) div_mult2_eq semiring_normalization_rules(7))

    then have f3: "\<forall>n na nb nc.
                    (nc div nb = 0 \<or> nc div 2 div nb \<preceq> na div 2 div n) \<or> \<not> nc div nb \<preceq> na div n"
      by (metis (no_types) masks.elims(2))

    {
      assume "\<exists>n. a div n div 2 ^ ka \<noteq> 0" then have "a div 2 ^ ka \<noteq> 0" using f2 by (metis div_0)
      then have "a div 2 div 2 ^ ka \<preceq> b div 2 div 2 ^ ka" using f3 a1 by meson
    }
    then have "a div (2 * 2 ^ ka) \<preceq> b div (2 * 2 ^ ka)"
      by (metis (no_types) div_mult2_eq masks.simps(1))
  }
  ultimately show ?case by simp
qed

lemma masks_digit_leq:"(a \<preceq> b) \<Longrightarrow> (nth_bit a k) \<le> (nth_bit b k)"
proof (induction k arbitrary: a b)
  case 0
  then show ?case
    by (metis add_cancel_left_right bitAND_nat.elims div_by_1 le0 masks.simps(2) power_0
              mod_mult_self1_is_0 mod_mult_self4 nth_bit_def)
next
  case (Suc k)
  then show ?case
    by (simp add: nth_bit_def)
       (metis div_mult2_eq masks_substr nth_bit_def pow.simps(1) power_numeral)
qed

lemma masks_leq_equiv:"(a \<preceq> b) \<longleftrightarrow> (\<forall>k. (nth_bit a k) \<le> (nth_bit b k))" (is "?P \<longleftrightarrow> ?Q")
proof
  assume "?P"
  then show "?Q" using masks_digit_leq by auto
next
  assume "?Q"
  then show "?P" using nth_bit_def
  proof (induct a b rule: masks.induct)
    case (1 uu)
    then show ?case by simp
  next
    case (2 v b)
    then show ?case by simp (metis drop_bit_Suc drop_bit_eq_div div_by_1 power.simps(1))
  qed
qed

lemma masks_leq:"a \<preceq> b \<longrightarrow> a \<le> b"
  using masks_leq_equiv bitwise_leq by simp

lemma mask_linear:
  fixes a b c d t :: nat
  assumes b: "b < (2::nat)^t"
  assumes d: "d < (2::nat)^t"
  shows "((a * 2^t + b \<preceq> c * 2^t + d) \<longleftrightarrow> (a \<preceq> c \<and> b \<preceq> d))" (is "?P \<longleftrightarrow> ?Q")
proof -
  have "?P \<longleftrightarrow> (\<forall>k. (a * 2^t + b) \<exclamdown> k \<le> (c * 2^t + d) \<exclamdown> k)" using masks_leq_equiv by auto
  also have "... \<longleftrightarrow> (\<forall>k. a \<exclamdown> k \<le> c \<exclamdown> k \<and> b \<exclamdown> k \<le> d \<exclamdown> k)" using b d digit_lt_linear by auto
  also have "... \<longleftrightarrow> a \<preceq> c \<and> b \<preceq> d" using masks_leq_equiv by auto
  finally show ?thesis by auto
qed

lemma aux1_lm0241_pow2_up_bound:"(\<exists>(p::nat). (a::nat) < 2^(Suc p))"
  by (induction a) (use less_exp in fastforce)+

lemma aux2_lm0241_single_digit_binom:
  assumes "1 \<ge> (a::nat)"
  assumes "1 \<ge> (b::nat)"
  shows "\<not>(a = 1 \<and> b = 1) \<longleftrightarrow> ((a + b) choose b) = 1" (is "?P \<longleftrightarrow> ?Q")
  using assms(1) assms(2)
  by (metis Suc_eq_plus1 add.commute add_cancel_right_left add_eq_if
              binomial_n_0 choose_one le_add2 le_antisym zero_neq_one)

lemma aux3_lm0241_binom_bounds:
  assumes "1 \<ge> (m::nat)"
  assumes "1 \<ge> (n::nat)"
  shows "1 \<ge> m choose n"
  using assms(1) assms(2) le_Suc_eq by auto

lemma aux4_lm0241_prod_one:
  fixes f::"(nat \<Rightarrow> nat)"
  assumes "(\<forall>x. (1 \<ge> f x))"
  shows "(\<Prod>k \<le> n. (f k)) = 1 \<longrightarrow> (\<forall>k. k \<le> n \<longrightarrow> f k = 1)" (is "?P \<longrightarrow> ?Q")
proof(rule ccontr)
  assume assm:"\<not>(?P \<longrightarrow> ?Q)"
  hence f_zero:"\<exists>r. r \<le> n \<and> f r \<noteq> 1" by simp
  then obtain r where "f r \<noteq> 1"  and "r \<le> n" by blast
  hence "f r = 0" using assms le_antisym not_less by blast
  hence contr:"(\<Prod>k \<le> n. f k) = 0" using \<open>r \<le> n\<close> by auto
  then show False using assm contr by simp
qed

lemma aux5_lm0241:
  "(\<forall>i. (nth_bit (a + b) i) choose (nth_bit b i) = 1) \<longrightarrow>
   \<not>(nth_bit a i = 1 \<and> nth_bit b i = 1)"
   (is "?P \<longrightarrow> ?Q i")
proof(rule ccontr)
  assume assm:"\<not>(?P \<longrightarrow> ?Q i)"
  hence "(\<exists>i. \<not>?Q i)" by blast
  then obtain i where contr:"\<not>?Q i" and i_minimal:"(\<forall>j < i. ?Q j)" 
    using obtain_smallest[of \<open>\<lambda>i. \<not>?Q i\<close>] by auto
  hence "\<forall>j. j < i \<longrightarrow> nth_bit a j * nth_bit b j = 0" by (simp add: nth_bit_def)
  hence "\<forall>j. j < i \<longrightarrow> ((nth_bit a j = 0 \<and> nth_bit b j = 1) \<or>
                            (nth_bit a j = 1 \<and> nth_bit b j = 0) \<or>
                            (nth_bit a j = 0 \<and> nth_bit b j = 0))"
      by (auto simp add: nth_bit_def)
  hence "\<forall>j. j < i \<longrightarrow> nth_bit a j + nth_bit b j \<le> 1" by auto
  hence "bin_carry a b i = 0"
    using no_carry by (metis contr add_self_mod_2 assm choose_one one_neq_zero)
  hence f0:"nth_bit (a + b) i = (nth_bit a i + nth_bit b i) mod 2"
    by(auto simp add:sum_digit_formula)
  have "... = 0" using contr by auto
  hence "(nth_bit (a + b) i) choose (nth_bit b i) = 0" using f0 contr by auto
  then show False using assm by fastforce
qed

end
