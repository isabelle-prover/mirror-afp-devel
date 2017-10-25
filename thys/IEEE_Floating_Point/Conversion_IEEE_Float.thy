(* Author: Fabian Hellauer
           Fabian Immler
*)
theory Conversion_IEEE_Float
  imports
    "HOL-Library.Float"
    IEEE
    "HOL-Library.Code_Target_Numeral"
begin

section \<open>IEEE.float to Float.float\<close>

definition to_man_exp where
  "to_man_exp x F =
    (case F of (s, e, f) \<Rightarrow>
    (
    if is_zero x F
    then (0, 0)
    else if is_denormal x F
    then
      let sh = Suc (fracwidth x - nat (bitlen f))
      in (((-1::int)^s * int f * 2 ^ sh), ((1 :: int) - bias x - fracwidth x - sh))
    else
      (((-1::int)^s * (2 ^ fracwidth x + int f)), (int e - bias x - fracwidth x))))"

lemma to_man_exp_correct:
  "(case to_man_exp x F of (i, j) \<Rightarrow> i * 2 powr j) = valof x F"
proof (cases F)
  case (fields s e f)
  define sh where "sh = Suc (fracwidth x - nat (bitlen f))"
  have *: "(- 1) ^ s * real f * 2 ^ sh * 2 powr (1 - real (bias x) - real (fracwidth x) - real sh) =
    (- 1) ^ s * real f * 2 powr (1 - real (bias x) - real (fracwidth x))"
    by (auto simp: powr_realpow[symmetric] powr_add[symmetric] algebra_simps)
  show ?thesis
    unfolding fields to_man_exp_def Let_def split_beta' fst_conv snd_conv sh_def[symmetric]
    by (auto simp: * divide_simps powr_realpow powr_diff is_denormal_def is_zero_def powr_minus)
qed

lemma to_man_exp_bitlen:
  "bitlen (abs (fst (to_man_exp x f))) = (if is_zero x f then 0 else Suc (fracwidth x))"
  if "is_valid x f"
  using that
  by (auto simp: to_man_exp_def bitlen_eq_zero_iff  abs_mult
      is_valid_def is_denormal_def is_zero_def bitlen_twopow_add_eq
      less_power_nat_iff_bitlen of_nat_diff bitlen_nonneg
      simp del: power_Suc
      split: prod.splits )

definition Float_of_IEEE_rep where
  "Float_of_IEEE_rep x f = (case to_man_exp x f of (i, j) \<Rightarrow> Float.Float i j)"

lemma Float_of_IEEE_rep: "Float_of_IEEE_rep x f = valof x f"
  by (auto simp: Float_of_IEEE_rep_def to_man_exp_correct[symmetric] split: prod.splits)


section \<open>Float.float to IEEE.float\<close>

definition normal_rep_of_man_exp_b :: "format \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> representation"
  where
    "normal_rep_of_man_exp_b x b m e =
  (if m > 0 then 0 else 1,
    nat (e + int (bias x) + b),
    nat (\<bar>m\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x))"

lemma normal_rep_of_man_exp_b_correct:
  fixes b :: nat
  assumes f_not_zero: "m \<noteq> 0"
  assumes exponent_b: "0 < e + int (bias x) + b"
    and mantissa_b: "0 \<le> \<bar>m\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x"
    and b_ok: "fracwidth x \<ge> b"
  shows "valof x (normal_rep_of_man_exp_b x b m e) = m * 2 powr e"
  using assms
proof  (cases "m > 0")
  case True
  have if_false: "\<not>nat (e + int (bias x) + b) = 0"
    using exponent_b by linarith
  have a: "?thesis \<longleftrightarrow>
    2 ^ nat (e + int (bias x) + int b) *
    (1 + real (nat (\<bar>m\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x)) / 2 ^ fracwidth x) /
    2 ^ bias x
    =
    real_of_int m *
    2 powr real_of_int e"
    using if_false normal_rep_of_man_exp_b_def valof.simps powr_realpow
    by (auto simp add: True)
  have m_greater: "m > 0"
    by (metis Float.compute_is_float_pos Float_mantissa_exponent True)
  then have "\<bar>m\<bar> = m"
    by simp
  then have s2: "real (nat (\<bar>m\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x))
    = \<bar>m\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x"
    using mantissa_b by auto
  have s3: "\<bar>real_of_int m\<bar> = real_of_int m"
    using \<open>0 < m\<close> by linarith
  have s4: "(real_of_int e + (real (fracwidth x) + real (bias x)))
    = real_of_int (e + bias x + fracwidth x)"
    by simp
  have s5: "real (nat (e + int (bias x) + int b)) + real (fracwidth x - b)
    = real_of_int (e + int (bias x) + int (fracwidth x))"
    using if_false b_ok by linarith
  show ?thesis
    unfolding a
    by (simp add: s2 s3 divide_simps powr_realpow[symmetric] powr_add[symmetric])
        (simp add: s4 s5)
next
  case False
  have if_false: "nat (e + int (bias x) + int b) \<noteq> 0"
    using exponent_b by linarith
  have a: "?thesis \<longleftrightarrow>
    - (2 ^ nat (e + int (bias x) + int b) *
    (1 + real (nat (\<bar>m\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x)) / 2 ^ fracwidth x) /
    2 ^ bias x)
    =
    real_of_int m *
    2 powr real_of_int e"
    using if_false normal_rep_of_man_exp_b_def mantissa_exponent valof.simps powr_realpow
    by (simp add: False)
  have m_smaller: "m < 0"
    by (metis False Float.compute_is_float_pos Float.compute_is_float_zero Float_mantissa_exponent
        f_not_zero linorder_neqE_linordered_idom)
  then have "\<bar>m\<bar> = - m"
    by simp
  then have s2: "real (nat (\<bar>m\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x))
    = \<bar>m\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x"
    using mantissa_b by auto
  have s3: "\<bar>real_of_int m\<bar> = - real_of_int m"
    using \<open>0 > m\<close> by linarith
  have s4: "(real_of_int e + (real (fracwidth x) + real (bias x)))
    = real_of_int (e + bias x + fracwidth x)"
    by simp
  have s5: "real (nat (e + int (bias x) + int b)) + real (fracwidth x - b)
    = real_of_int (e + int (bias x) + int (fracwidth x))"
    using if_false b_ok by linarith
  show ?thesis
    unfolding a
    by (simp add: s2 s3 divide_simps powr_realpow[symmetric] powr_add[symmetric])
      (simp add: s4 s5)
qed

lemma floorlog_pos_iff: "floorlog b x > 0 \<longleftrightarrow> x > 0 \<and> b > 1"
  by (auto simp: floorlog_def)

lemma bitlen_pos_iff: "bitlen x > 0 \<longleftrightarrow> x > 0"
  by (auto simp: bitlen_def floorlog_pos_iff)

definition normal_rep_of_man_exp :: "format \<Rightarrow> int \<Rightarrow> int \<Rightarrow> representation" where
  "normal_rep_of_man_exp x m e = normal_rep_of_man_exp_b x (nat (bitlen \<bar>m\<bar> - 1)) m e"

lemma normal_rep_of_man_exp_correct:
  assumes "m \<noteq> 0"
  assumes mantissa: "bitlen \<bar>m\<bar> \<le> fracwidth x"
  assumes exponent: "- int (bias x) - bitlen \<bar>m\<bar> + 1 < e"
    "e < 2^(expwidth x) - int (bias x) - fracwidth x"
  shows "valof x (normal_rep_of_man_exp x m e) = m * 2 powr e" (is ?th1)
    and "is_valid x (normal_rep_of_man_exp x m e)" (is ?th2)
    and "is_normal x (normal_rep_of_man_exp x m e)" (is ?th3)
proof -
  from assms(1) have mnz[simp]: "m \<noteq> 0"
    by (auto simp: is_float_zero_def mantissa_exponent)
  let ?bl = "bitlen \<bar>m\<bar>"
  let ?d = "(fracwidth x - nat (?bl - 1))"
  have bl_pos: "?bl > 0"
    by (auto simp: bitlen_pos_iff)
  have "\<bar>m\<bar> * 2 ^ ?d - 2 ^ fracwidth x \<ge>
    2 ^ (nat (?bl - 1)) * 2 ^ ?d - 2 ^ fracwidth x"
    using bitlen_bounds[of "\<bar>m\<bar>"] bl_pos
    by (auto simp: bitlen_def floorlog_def)
  also have "2 ^ (nat (?bl - 1)) * 2 ^ ?d - 2 ^ fracwidth x
    = (2::int) ^ (nat (?bl - 1) + ?d) - 2 ^ fracwidth x"
    unfolding power_add[symmetric]
    by auto
  also have "(nat (?bl - 1) + ?d) = fracwidth x"
    using assms by simp
  finally have mantissa_ok: "0 \<le> \<bar>m\<bar> * 2 ^ ?d - 2 ^ fracwidth x"
    by simp
  have "\<bar>m\<bar> * (2::real) ^ ?d <
      2 ^ nat (?bl) * (2::real) ^ ?d"
    using abs_real_le_2_powr_bitlen bitlen_nonneg powr_int
    by auto
  also have "\<dots> = 2 ^ (nat (?bl) + fracwidth x - nat (?bl - 1))"
    unfolding power_add[symmetric]
    using mantissa
    by simp
  also
  have "?bl > 0" by fact
  then have "nat (?bl) + fracwidth x - nat (?bl - 1) = fracwidth x + 1"
    using assms
    by (simp)
  finally
  have "\<bar>m\<bar> * (2::real) ^ ?d < 2 ^ (fracwidth x + 1)"
    by simp
  then have "real_of_int (\<bar>m\<bar> * 2 ^ ?d) <
    real_of_int (2 ^ (fracwidth x + 1) - 1) + 1"
    by simp
  then have "\<bar>m\<bar> * 2 ^ ?d < 2 ^ (fracwidth x + 1)"
    unfolding int_le_real_less[symmetric]
    by simp
  then have "\<bar>m\<bar> * 2 ^ ?d < 2 ^ (fracwidth x + 1)"
    by simp
  then have "\<bar>m\<bar> * 2 ^ ?d - 2 ^ fracwidth x < 2 ^ fracwidth x"
    by (simp)
  with mantissa_ok
  have l: "nat (\<bar>m\<bar> * 2 ^ ?d - 2 ^ fracwidth x) < 2 ^ fracwidth x"
    by (simp add: nat_less_iff)

  have emax: "nat (e + int (bias x) + (bitlen \<bar>m\<bar> - 1)) < emax x"
    using exponent mantissa
    by (auto simp: emax_def nat_less_iff of_nat_diff)
  show ?th1
    unfolding normal_rep_of_man_exp_def
    using assms mantissa_ok mantissa
    by (intro normal_rep_of_man_exp_b_correct) auto
  show ?th2
    unfolding normal_rep_of_man_exp_def
    using assms l
    by (auto simp: normal_rep_of_man_exp_b_def nat_less_iff is_valid_def)
  show ?th3
    using bl_pos exponent emax
    by (auto simp: normal_rep_of_man_exp_def normal_rep_of_man_exp_b_def is_normal_def bl_pos emax_def)
qed

lemma general_valof_topfloat:
  assumes ew_ok: "expwidth x \<ge> 2"
  shows "valof x (topfloat x) = largest x"
proof -
  let ?fw = "2 ^ fracwidth x"
  from ew_ok have "((2::nat) ^ expwidth x - 1 - 1) \<ge> 1"
    by simp (metis Suc_1 Suc_leI linorder_neqE_nat nat.simps(1) not_le not_numeral_le_zero
        numerals(2) power.simps(1) power_inject_exp power_one_right zero_less_diff zero_less_power)
  moreover have "real (?fw - Suc 0) = real (?fw) - 1"
    by (simp add: of_nat_diff)
  moreover have "(?fw - (1::real)) / ?fw = 1 - 1 / ?fw"
  proof -
    have f1: "\<forall>r ra rb. (r::real) / rb + ra / rb + - 1 * ((ra + r) / rb) = 0"
      by (simp add: add_divide_distrib)
    have "- (1::real) + ?fw + 1 = ?fw"
      by auto
    then have f2: "(1::real) / ?fw + (- 1 + ?fw) / ?fw + - 1 * (?fw / ?fw) = 0"
      using f1 by metis
    have f3: "((?fw - (1::real)) / ?fw \<noteq> 1 - 1 / ?fw) = ((1::real) / ?fw + (- 1 + ?fw) / ?fw \<noteq> 1)"
      by fastforce
    have "(1::real) / ?fw + (- 1 + ?fw) / ?fw = 1"
      using f2 by simp
    then show "(?fw - (1::real)) / ?fw = 1 - 1 / ?fw"
      using f3 by meson
  qed
  ultimately show ?thesis
    unfolding emax_def topfloat_def largest_def
    by auto
qed

definition subnormal_rep_of_man_exp :: "format \<Rightarrow> int \<Rightarrow> int \<Rightarrow> representation"
  where
    "subnormal_rep_of_man_exp x m e =
  (if m \<ge> 0 then 0 else 1,
    0,
    nat (\<bar>m\<bar> * 2 ^ nat (e + bias x + fracwidth x - 1)))"

lemma subnormal_rep_of_man_exp_correct:
  assumes "m \<noteq> 0"
  assumes mantissa: "bitlen \<bar>m\<bar> \<le> 1 - e - int (bias x)"
  assumes exponent: "fracwidth x - int (bias x) < e"
  shows "valof x (subnormal_rep_of_man_exp x m e) = m * 2 powr e" (is ?th1)
    and "is_valid x (subnormal_rep_of_man_exp x m e)" (is ?th2)
    and "is_denormal x (subnormal_rep_of_man_exp x m e)" (is ?th3)
proof -
  have mnz: "m \<noteq> 0" using assms(1) by (auto simp: is_float_zero_def mantissa_exponent)
  then have "bitlen (\<bar>m\<bar> * 2 ^ nat (e + int (bias x) + int (fracwidth x) - 1)) =
    bitlen \<bar>m\<bar> + e + int (bias x) + int (fracwidth x) - 1"
    using exponent
    by simp
  also have "\<dots> \<le> fracwidth x"
    using mantissa
    by simp
  finally have "bitlen (\<bar>m\<bar> * 2 ^ nat (e + int (bias x) + int (fracwidth x) - 1)) \<le> fracwidth x"
    .
  from this
  have 1: "nat (\<bar>m\<bar> * 2 ^ nat (e + int (bias x) + int (fracwidth x) - 1))
    < 2 ^ fracwidth x"
    by (auto simp: bitlen_le_iff_power)

  have 2: "\<bar>m\<bar> * 2 ^ nat (e + int (bias x) + int (fracwidth x) - 1) > 0"
    using mnz
    by (auto simp: intro!: mult_pos_pos)

  have req: "real (nat (e + int (bias x) + int (fracwidth x) - 1)) =
        real_of_int (e) + real (bias x) + real (fracwidth x) - 1"
    using exponent by auto
  have not_le: "2 powr real_of_int (e) \<le> 0 \<longleftrightarrow> False"
    by (simp add: antisym_conv)
  show ?th2
    using 1
    by (auto simp: subnormal_rep_of_man_exp_def is_valid_def)
  show ?th3
    using 2
    by (auto simp: subnormal_rep_of_man_exp_def is_denormal_def)
  show ?th1
    by (auto simp: subnormal_rep_of_man_exp_def powr_realpow[symmetric] powr_add diff_add_eq req
        powr_diff is_float_nonneg_def zero_le_mult_iff not_le
        mantissa_exponent)
qed

definition "valid_man_exp x m e \<longleftrightarrow>
  bitlen (abs m) \<le> int (fracwidth x) \<and> int (fracwidth x) - int (bias x) < e \<and>
  e < 2 ^ expwidth x - int (bias x) - int (fracwidth x)"

definition float_rep_of_man_exp :: "format \<Rightarrow> int \<Rightarrow> int \<Rightarrow> representation" where
  "float_rep_of_man_exp x m e = (
    if valid_man_exp x m e
    then
      if m = 0 then (0,0,0)
      else if bitlen (abs m) + e \<le> 1 - int (bias x)
      then subnormal_rep_of_man_exp x m e
      else normal_rep_of_man_exp x m e
    else plus_infinity x)"

lemma is_valid_0[simp]: "is_valid x (0, 0, 0)"
  by (auto simp: is_valid_def)

lemma is_zero_0[simp]: "is_zero x (0, 0, 0)"
  by (auto simp: is_finite_def is_denormal_def is_normal_def is_zero_def)

lemma is_valid_plus_infinity[simp]: "is_valid x (plus_infinity x)"
  by (auto simp: is_valid_def plus_infinity_def emax_def)

theorem float_rep_of_man_exp_is_valid[simp]:
  "is_valid x (float_rep_of_man_exp x m e)"
  by (auto simp: float_rep_of_man_exp_def valid_man_exp_def
      intro!: subnormal_rep_of_man_exp_correct normal_rep_of_man_exp_correct)

theorem float_rep_of_man_exp:
  "valof x (float_rep_of_man_exp x m e) = m * 2 powr e"
  "is_finite x (float_rep_of_man_exp x m e)"
  if "valid_man_exp x m e"
  using that
  by (auto simp: float_rep_of_man_exp_def is_float_zero_def is_finite_def valid_man_exp_def
      intro!: subnormal_rep_of_man_exp_correct normal_rep_of_man_exp_correct is_valid_0)

lemma zero_eq_plus_infinity_iff: "(0, 0, 0) = plus_infinity x \<longleftrightarrow> expwidth x = 0"
  by (auto simp: plus_infinity_def emax_def le_Suc_eq)

lemma not_normal_plus_infinity[simp]: "is_normal x (plus_infinity x) \<longleftrightarrow> False"
  by (auto simp: is_normal_def plus_infinity_def)

lemma not_denormal_plus_infinity[simp]: "is_denormal x (plus_infinity x) \<longleftrightarrow> False"
  by (auto simp: is_denormal_def plus_infinity_def)

lemma is_zero_plus_infinity[simp]: "is_zero x (plus_infinity x) \<longleftrightarrow> expwidth x = 0"
  by (auto simp: is_zero_def plus_infinity_def emax_def le_Suc_eq)

lemma is_infinity_plus_infinity[simp]: "is_infinity x (plus_infinity x)"
  by (auto simp: is_infinity_def plus_infinity_def)

theorem float_rep_of_man_exp_invalid:
  "float_rep_of_man_exp x m e = plus_infinity x \<longleftrightarrow> \<not>valid_man_exp x m e"
  if "0 < expwidth x"
  using that float_rep_of_man_exp[of x m e]
  by (auto simp: float_rep_of_man_exp_def is_finite_def valid_man_exp_def
      intro!: subnormal_rep_of_man_exp_correct normal_rep_of_man_exp_correct)


section \<open>Lifting to Type @{type float}\<close>

subsection \<open>Interface to target language\<close>

definition to_man_exp_float :: "IEEE.float \<Rightarrow> integer \<times> integer"
  where "to_man_exp_float x =
  (case to_man_exp float_format (Rep_float x) of (i, j) \<Rightarrow> (integer_of_int i, integer_of_int j))"

definition from_man_exp_float :: "integer \<Rightarrow> integer \<Rightarrow> IEEE.float"
  where "from_man_exp_float x y =
    Abs_float (float_rep_of_man_exp float_format (int_of_integer x) (int_of_integer y))"

subsection \<open>Conversions\<close>

definition "Float_of_IEEE x = (case to_man_exp_float x of (m, e) \<Rightarrow> Float.Float (int_of_integer m) (int_of_integer e))"

theorem Float_of_IEEE: "real_of_float (Float_of_IEEE x) = Val x"
  unfolding Float_of_IEEE_def
  using to_man_exp_correct[of float_format "Rep_float x"]
  by (auto simp: Float_of_IEEE_def Float_of_IEEE_rep Val_def to_man_exp_float_def
      split!: prod.splits)

definition "IEEE_of_Float x = Abs_float (float_rep_of_man_exp float_format (mantissa x) (Float.exponent x))"

lemma compute_IEEE_of_Float[code]:
  "IEEE_of_Float x = from_man_exp_float (integer_of_int (mantissa x)) (integer_of_int (Float.exponent x))"
  by (auto simp: IEEE_of_Float_def from_man_exp_float_def Float_mantissa_exponent)

lemma Finite_Abs_float_iff:
  "Finite (Abs_float x) \<longleftrightarrow> is_finite float_format x" if "is_valid float_format x"
  using that
  by (auto simp: Finite_def Isnormal_def Abs_float_inverse is_finite_def
      Isdenormal_def Iszero_def)

lemma Infinity_Plus_infinity:
  "Infinity Plus_infinity"
  using is_valid_plus_infinity[of float_format]
  by (auto simp: Infinity_def Plus_infinity_def is_infinity_plus_infinity Abs_float_inverse)

theorem IEEE_of_Float_valid: "Val (IEEE_of_Float x) = real_of_float x"
  and IEEE_of_Float_Finite_valid: "Finite (IEEE_of_Float x)"
  if "valid_man_exp float_format (mantissa x) (Float.exponent x)"
  using float_rep_of_man_exp[of float_format "mantissa x" "Float.exponent x", OF that]
  by (auto simp: Val_def IEEE_of_Float_def float_format_def bias_def Abs_float_inverse
    mantissa_exponent Finite_Abs_float_iff)

lemma pos_expwidth[simp]: "0 < expwidth float_format"
  by (auto simp: float_format_def)

theorem IEEE_of_Float_invalid:
  "IEEE_of_Float x = Plus_infinity \<longleftrightarrow> \<not>valid_man_exp float_format (mantissa x) (Float.exponent x)"
  by (simp add: Plus_infinity_def IEEE_of_Float_def float_rep_of_man_exp_invalid
      Abs_float_inverse Abs_float_inject)

end