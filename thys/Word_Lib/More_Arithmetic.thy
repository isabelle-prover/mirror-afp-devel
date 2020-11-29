
section \<open>Arithmetic lemmas\<close>

theory More_Arithmetic
  imports Main "HOL-Library.Type_Length"
begin

declare iszero_0 [intro]

declare min.absorb1 [simp] min.absorb2 [simp]

lemma n_less_equal_power_2 [simp]:
  "n < 2 ^ n"
  by (induction n) simp_all

lemma min_pm [simp]: "min a b + (a - b) = a"
  for a b :: nat
  by arith

lemma min_pm1 [simp]: "a - b + min a b = a"
  for a b :: nat
  by arith

lemma rev_min_pm [simp]: "min b a + (a - b) = a"
  for a b :: nat
  by arith

lemma rev_min_pm1 [simp]: "a - b + min b a = a"
  for a b :: nat
  by arith

lemma min_minus [simp]: "min m (m - k) = m - k"
  for m k :: nat
  by arith

lemma min_minus' [simp]: "min (m - k) m = m - k"
  for m k :: nat
  by arith

lemma nat_min_simps:
  "(a::nat) \<le> b \<Longrightarrow> min b a = a"
  "a \<le> b \<Longrightarrow> min a b = a"
  by simp_all

lemma iszero_minus:
  \<open>iszero (- z) \<longleftrightarrow> iszero z\<close>
  by (simp add: iszero_def)

lemma diff_le_eq': "a - b \<le> c \<longleftrightarrow> a \<le> b + c"
  for a b c :: int
  by arith

lemma zless2: "0 < (2 :: int)"
  by (fact zero_less_numeral)

lemma zless2p: "0 < (2 ^ n :: int)"
  by arith

lemma zle2p: "0 \<le> (2 ^ n :: int)"
  by arith

lemma ex_eq_or: "(\<exists>m. n = Suc m \<and> (m = k \<or> P m)) \<longleftrightarrow> n = Suc k \<or> (\<exists>m. n = Suc m \<and> P m)"
  by auto

lemma power_minus_simp: "0 < n \<Longrightarrow> a ^ n = a * a ^ (n - 1)"
  by (auto dest: gr0_implies_Suc)

lemma n2s_ths:
  \<open>2 + n = Suc (Suc n)\<close>
  \<open>n + 2 = Suc (Suc n)\<close>
  by (fact add_2_eq_Suc add_2_eq_Suc')+

lemma s2n_ths:
  \<open>Suc (Suc n) = 2 + n\<close>
  \<open>Suc (Suc n) = n + 2\<close>
  by simp_all

lemma gt_or_eq_0: "0 < y \<or> 0 = y"
  for y :: nat
  by arith

lemmas nat_simps = diff_add_inverse2 diff_add_inverse

lemmas nat_iffs = le_add1 le_add2

lemma sum_imp_diff: "j = k + i \<Longrightarrow> j - i = k"
  for k :: nat
  by simp

lemma le_diff_eq': "a \<le> c - b \<longleftrightarrow> b + a \<le> c"
  for a b c :: int
  by arith

lemma less_diff_eq': "a < c - b \<longleftrightarrow> b + a < c"
  for a b c :: int
  by arith

lemma diff_less_eq': "a - b < c \<longleftrightarrow> a < b + c"
  for a b c :: int
  by arith

lemma axxbyy: "a + m + m = b + n + n \<Longrightarrow> a = 0 \<or> a = 1 \<Longrightarrow> b = 0 \<or> b = 1 \<Longrightarrow> a = b \<and> m = n"
  for a b m n :: int
  by arith

lemmas zadd_diff_inverse =
  trans [OF diff_add_cancel [symmetric] add.commute]

lemmas add_diff_cancel2 =
  add.commute [THEN diff_eq_eq [THEN iffD2]]

lemmas mcl = mult_cancel_left [THEN iffD1, THEN make_pos_rule]

lemma pl_pl_rels: "a + b = c + d \<Longrightarrow> a \<ge> c \<and> b \<le> d \<or> a \<le> c \<and> b \<ge> d"
  for a b c d :: nat
  by arith

lemmas pl_pl_rels' = add.commute [THEN [2] trans, THEN pl_pl_rels]

lemma minus_eq: "m - k = m \<longleftrightarrow> k = 0 \<or> m = 0"
  for k m :: nat
  by arith

lemma pl_pl_mm: "a + b = c + d \<Longrightarrow> a - c = d - b"
  for a b c d :: nat
  by arith

lemmas pl_pl_mm' = add.commute [THEN [2] trans, THEN pl_pl_mm]

lemma less_le_mult': "w * c < b * c \<Longrightarrow> 0 \<le> c \<Longrightarrow> (w + 1) * c \<le> b * c"
  for b c w :: int
  apply (rule mult_right_mono)
   apply (rule zless_imp_add1_zle)
   apply (erule (1) mult_right_less_imp_less)
  apply assumption
  done

lemma less_le_mult: "w * c < b * c \<Longrightarrow> 0 \<le> c \<Longrightarrow> w * c + c \<le> b * c"
  for b c w :: int
  using less_le_mult' [of w c b] by (simp add: algebra_simps)

lemmas less_le_mult_minus = iffD2 [OF le_diff_eq less_le_mult,
  simplified left_diff_distrib]

lemma gen_minus: "0 < n \<Longrightarrow> f n = f (Suc (n - 1))"
  by auto

lemma mpl_lem: "j \<le> i \<Longrightarrow> k < j \<Longrightarrow> i - j + k < i"
  for i j k :: nat
  by arith

lemmas dme = div_mult_mod_eq
lemmas dtle = div_times_less_eq_dividend
lemmas th2 = order_trans [OF order_refl [THEN [2] mult_le_mono] div_times_less_eq_dividend]

lemma td_gal: "0 < c \<Longrightarrow> a \<ge> b * c \<longleftrightarrow> a div c \<ge> b"
  for a b c :: nat
  apply safe
   apply (erule (1) xtrans(4) [OF div_le_mono div_mult_self_is_m])
  apply (erule th2)
  done

lemmas td_gal_lt = td_gal [simplified not_less [symmetric], simplified]

lemmas sdl = div_nat_eqI

lemma given_quot: "f > 0 \<Longrightarrow> (f * l + (f - 1)) div f = l"
  for f l :: nat
  by (rule div_nat_eqI) (simp_all)

lemma given_quot_alt: "f > 0 \<Longrightarrow> (l * f + f - Suc 0) div f = l"
  for f l :: nat
  apply (frule given_quot)
  apply (rule trans)
   prefer 2
   apply (erule asm_rl)
  apply (rule_tac f="\<lambda>n. n div f" in arg_cong)
  apply (simp add : ac_simps)
  done

lemma nat_less_power_trans:
  fixes n :: nat
  assumes nv: "n < 2 ^ (m - k)"
  and     kv: "k \<le> m"
  shows "2 ^ k * n < 2 ^ m"
proof (rule order_less_le_trans)
  show "2 ^ k * n < 2 ^ k * 2 ^ (m - k)"
    by (rule mult_less_mono2 [OF nv zero_less_power]) simp

  show "(2::nat) ^ k * 2 ^ (m - k) \<le> 2 ^ m" using nv kv
    by (subst power_add [symmetric]) simp
qed

lemma nat_le_power_trans:
  fixes n :: nat
  shows "\<lbrakk>n \<le> 2 ^ (m - k); k \<le> m\<rbrakk> \<Longrightarrow> 2 ^ k * n \<le> 2 ^ m"
  by (metis le_add_diff_inverse mult_le_mono2 semiring_normalization_rules(26))

lemma x_power_minus_1:
  fixes x :: "'a :: {ab_group_add, power, numeral, one}"
  shows "x + (2::'a) ^ n - (1::'a) = x + (2 ^ n - 1)" by simp

lemma nat_diff_add:
  fixes i :: nat
  shows "\<lbrakk> i + j = k \<rbrakk> \<Longrightarrow> i = k - j"
  by arith

lemma pow_2_gt: "n \<ge> 2 \<Longrightarrow> (2::int) < 2 ^ n"
  by (induct n) auto

lemma sum_to_zero:
  "(a :: 'a :: ring) + b = 0 \<Longrightarrow> a = (- b)"
  by (drule arg_cong[where f="\<lambda> x. x - a"], simp)

lemma arith_is_1:
  "\<lbrakk> x \<le> Suc 0; x > 0 \<rbrakk> \<Longrightarrow> x = 1"
  by arith

lemma suc_le_pow_2:
  "1 < (n::nat) \<Longrightarrow> Suc n < 2 ^ n"
  by (induct n; clarsimp)
     (case_tac "n = 1"; clarsimp)

lemma nat_le_Suc_less_imp:
  "x < y \<Longrightarrow> x \<le> y - Suc 0"
  by arith

lemma power_sub_int:
  "\<lbrakk> m \<le> n; 0 < b \<rbrakk> \<Longrightarrow> b ^ n div b ^ m = (b ^ (n - m) :: int)"
  apply (subgoal_tac "\<exists>n'. n = m + n'")
   apply (clarsimp simp: power_add)
  apply (rule exI[where x="n - m"])
  apply simp
  done

lemma nat_Suc_less_le_imp:
  "(k::nat) < Suc n \<Longrightarrow> k \<le> n"
  by auto

lemma nat_add_less_by_max:
  "\<lbrakk> (x::nat) \<le> xmax ; y < k - xmax \<rbrakk> \<Longrightarrow> x + y < k"
  by simp

lemma nat_le_Suc_less:
  "0 < y \<Longrightarrow> (x \<le> y - Suc 0) = (x < y)"
  by arith

lemma nat_power_minus_less:
  "a < 2 ^ (x - n) \<Longrightarrow> (a :: nat) < 2 ^ x"
  by (erule order_less_le_trans) simp

lemma less_le_mult_nat':
  "w * c < b * c ==> 0 \<le> c ==> Suc w * c \<le> b * (c::nat)"
  apply (rule mult_right_mono)
   apply (rule Suc_leI)
   apply (erule (1) mult_right_less_imp_less)
  apply assumption
  done

lemma less_le_mult_nat:
  \<open>0 < c \<and> w < b \<Longrightarrow> c + w * c \<le> b * c\<close> for b c w :: nat
  using less_le_mult_nat' [of w c b] by simp

lemma diff_diff_less:
  "(i < m - (m - (n :: nat))) = (i < m \<and> i < n)"
  by auto

lemma nat_add_offset_less:
  fixes x :: nat
  assumes yv: "y < 2 ^ n"
  and     xv: "x < 2 ^ m"
  and     mn: "sz = m + n"
  shows   "x * 2 ^ n + y < 2 ^ sz"
proof (subst mn)
  from yv obtain qy where "y + qy = 2 ^ n" and "0 < qy"
    by (auto dest: less_imp_add_positive)

  have "x * 2 ^ n + y < x * 2 ^ n + 2 ^ n" by simp fact+
  also have "\<dots> = (x + 1) * 2 ^ n" by simp
  also have "\<dots> \<le> 2 ^ (m + n)" using xv
    by (subst power_add) (rule mult_le_mono1, simp)
  finally show "x * 2 ^ n + y < 2 ^ (m + n)" .
qed

lemma p_assoc_help:
  fixes p :: "'a::{ring,power,numeral,one}"
  shows "p + 2^sz - 1 = p + (2^sz - 1)"
  by simp

lemma nat_power_less_diff:
  assumes lt: "(2::nat) ^ n * q < 2 ^ m"
  shows "q < 2 ^ (m - n)"
  using lt
proof (induct n arbitrary: m)
  case 0
  then show ?case by simp
next
  case (Suc n)

  have ih: "\<And>m. 2 ^ n * q < 2 ^ m \<Longrightarrow> q < 2 ^ (m - n)"
    and prem: "2 ^ Suc n * q < 2 ^ m" by fact+

  show ?case
  proof (cases m)
    case 0
    then show ?thesis using Suc by simp
  next
    case (Suc m')
    then show ?thesis using prem
      by (simp add: ac_simps ih)
  qed
qed

lemma pow_mono_leq_imp_lt:
  "x \<le> y \<Longrightarrow> x < 2 ^ y"
  by (simp add: le_less_trans)

lemma small_powers_of_2:
  "x \<ge> 3 \<Longrightarrow> x < 2 ^ (x - 1)"
  by (induct x; simp add: suc_le_pow_2)

lemma power_2_mult_step_le:
  "\<lbrakk>n' \<le> n; 2 ^ n' * k' < 2 ^ n * k\<rbrakk> \<Longrightarrow> 2 ^ n' * (k' + 1) \<le> 2 ^ n * (k::nat)"
  apply (cases "n'=n", simp)
   apply (metis Suc_leI le_refl mult_Suc_right mult_le_mono semiring_normalization_rules(7))
  apply (drule (1) le_neq_trans)
  apply clarsimp
  apply (subgoal_tac "\<exists>m. n = n' + m")
   prefer 2
   apply (simp add: le_Suc_ex)
  apply (clarsimp simp: power_add)
  by (metis Suc_leI mult.assoc mult_Suc_right nat_mult_le_cancel_disj)

lemma nat_less_power_trans2:
  fixes n :: nat
  shows "\<lbrakk>n < 2 ^ (m - k); k \<le> m\<rbrakk> \<Longrightarrow> n * 2 ^ k  < 2 ^ m"
  by (subst mult.commute, erule (1) nat_less_power_trans)

lemma nat_move_sub_le: "(a::nat) + b \<le> c \<Longrightarrow> a \<le> c - b"
  by arith

lemma plus_minus_one_rewrite:
  "v + (- 1 :: ('a :: {ring, one, uminus})) \<equiv> v - 1"
  by (simp add: field_simps)

lemma Suc_0_lt_2p_len_of: "Suc 0 < 2 ^ LENGTH('a :: len)"
  by (metis One_nat_def len_gt_0 lessI numeral_2_eq_2 one_less_power)

end
