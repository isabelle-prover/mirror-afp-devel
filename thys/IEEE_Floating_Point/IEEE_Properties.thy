(* Author: Lei Yu, University of Cambridge *)

section \<open>Proofs of Properties about Floating Point Arithmetic\<close>

theory IEEE_Properties
imports IEEE
begin

lemmas float_defs =
  Finite_def Infinity_def Iszero_def Isnan_def Val_def Sign_def
  Isnormal_def Isdenormal_def Fraction_def Exponent_def float_format_def
  Plus_zero_def Minus_zero_def


subsection \<open>Theorems derived from definitions\<close>

lemma sign: "\<And>a. sign a = fst a"
  by auto

lemma exponent: "\<And>a. exponent a = fst (snd a)"
  by auto

lemma fraction: "\<And>a. fraction a = snd (snd a)"
  by auto

lemma is_valid:
  "is_valid x a \<longleftrightarrow>
    sign a < 2 \<and> exponent a < 2^(expwidth x) \<and> fraction a < 2^(fracwidth x)"
  by (auto simp: is_valid_def emax_def)

lemma is_valid_defloat: "is_valid float_format (Rep_float a)"
  by (cases a) (simp add: Abs_float_inverse)

lemma float_cases: "Isnan a \<or> Infinity a \<or> Isnormal a \<or> Isdenormal a \<or> Iszero a"
  by (cases a)
    (auto simp: Abs_float_inverse emax_def is_nan_def float_defs
      is_infinity_def is_normal_def is_denormal_def is_zero_def is_valid_def)

lemma float_cases_finite: "Isnan a \<or> Infinity a \<or> Finite a"
  by (cases a)
    (auto simp: Abs_float_inverse emax_def is_nan_def float_defs
      is_infinity_def is_normal_def is_denormal_def is_zero_def is_valid_def)

lemma float_zero1: "Iszero Plus_zero"
  by (auto simp: float_defs Abs_float_inverse is_zero_def is_valid_def)

lemma float_zero2: "Iszero Minus_zero"
  by (auto simp: float_defs Abs_float_inverse is_zero_def is_valid_def)

lemma is_valid_special:
  "is_valid x (minus_infinity x)"
  "is_valid x (plus_infinity x)"
  "is_valid x (topfloat x)"
  "is_valid x (bottomfloat x)"
  "is_valid x (plus_zero x)"
  "is_valid x (minus_zero x)"
  by (auto simp: emax_def is_valid_def minus_infinity_def
    plus_infinity_def topfloat_def bottomfloat_def)

lemma sign_0_1: "is_valid x a \<Longrightarrow> sign a < 2"
  by (auto simp: is_valid_def)

text \<open>The types of floating-point numbers are mutually distinct.\<close>
lemma float_distinct:
  "\<not> (Isnan a \<and> Infinity a)"
  "\<not> (Isnan a \<and> Isnormal a)"
  "\<not> (Isnan a \<and> Isdenormal a)"
  "\<not> (Isnan a \<and> Iszero a)"
  "\<not> (Infinity a \<and> Isnormal a)"
  "\<not> (Infinity a \<and> Isdenormal a)"
  "\<not> (Infinity a \<and> Iszero a)"
  "\<not> (Isnormal a \<and> Isdenormal a)"
  "\<not> (Isdenormal a \<and> Iszero a)"
  by (auto simp: emax_def float_defs is_nan_def is_infinity_def
    is_normal_def is_denormal_def is_zero_def)

lemma float_distinct_finite: "\<not> (Isnan a \<and> Finite a)" "\<not>(Infinity a \<and> Finite a)"
  by (auto simp: emax_def float_defs is_nan_def
    is_infinity_def is_normal_def is_denormal_def is_zero_def)

lemma finite_infinity: "Finite a \<Longrightarrow> \<not> Infinity a"
  by (auto simp: emax_def float_defs is_infinity_def is_normal_def is_denormal_def is_zero_def)

lemma finite_nan: "Finite a \<Longrightarrow> \<not> Isnan a"
  by (auto simp: emax_def float_defs is_nan_def is_infinity_def
    is_normal_def is_denormal_def is_zero_def)

text \<open>For every real number, the floating-point numbers closest to it always exist.\<close>
lemma is_closest_exists:
  fixes v :: "representation \<Rightarrow> real"
    and s :: "representation set"
  assumes finite: "finite s"
    and non_empty: "s \<noteq> {}"
  shows "\<exists>a. is_closest v s x a"
  using finite non_empty
proof (induct s rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert z s)
  show ?case
  proof (cases "s = {}")
    case True
    then have "is_closest v (insert z s) x z"
      by (auto simp: is_closest_def)
    then show ?thesis by metis
  next
    case False
    then obtain a where a: "is_closest v s x a"
      using insert by metis
    then show ?thesis
    proof (cases "\<bar>v a - x\<bar>" "\<bar>v z - x\<bar>" rule: le_cases)
      case le
      then show ?thesis
        by (metis insert_iff a is_closest_def)
    next
      case ge
      have "\<forall>b. b \<in> s \<longrightarrow> \<bar>v a - x\<bar> \<le> \<bar>v b - x\<bar>"
        by (metis a is_closest_def)
      then have "\<forall>b. b \<in> insert z s \<longrightarrow> \<bar>v z - x\<bar> \<le> \<bar>v b - x\<bar>"
        by (metis eq_iff ge insert_iff order.trans)
      then show ?thesis using is_closest_def a
        by (metis insertI1)
    qed
  qed
qed

lemma closest_is_everything:
  fixes v :: "representation \<Rightarrow> real"
    and s :: "representation set"
  assumes finite: "finite s"
    and non_empty: "s \<noteq> {}"
  shows "is_closest v s x (closest v p s x) \<and>
    ((\<exists>b. is_closest v s x b \<and> p b) \<longrightarrow> p (closest v p s x))"
  unfolding closest_def
  by (rule someI_ex) (metis assms is_closest_exists [of s v x])

lemma closest_in_set:
  fixes v :: "representation \<Rightarrow> real"
  assumes "finite s" and "s \<noteq> {}"
  shows "closest v p s x \<in> s"
  by (metis assms closest_is_everything is_closest_def)

lemma closest_is_closest:
  fixes v :: "representation \<Rightarrow> real"
  assumes "finite s" and "s \<noteq> {}"
  shows "is_closest v s x (closest v p s x)"
  by (metis closest_is_everything assms)

lemma float_first_cross:
  "{a::representation. fst a < m \<and> fst (snd a) < n \<and> snd (snd a) < p} =
    image (\<lambda>((x::nat), (y, z)). (x, y, z)) ({x. x < m} \<times> {y. y < n} \<times> {z. z < p})"
  by auto

lemma finite_r3: "finite {a::representation. fst a < m \<and> fst (snd a) < n \<and> snd (snd a) < p}"
  by (auto simp: float_first_cross)

lemma is_valid_finite: "finite {a. is_valid x a}"
  by (auto simp: finite_r3 sign exponent fraction is_valid_def)

lemma is_finite_subset: "{a::representation. is_finite x a} \<subseteq> {a. is_valid x a} "
  by (auto simp: is_finite_def)

lemma match_float_finite:
  assumes "{a::representation. is_finite x a} \<subseteq> {a. is_valid x a}"
  shows "finite {a. is_finite x a}"
  by (metis assms finite_subset is_valid_finite)

lemma is_finite_finite: "finite {a::representation. is_finite x a}"
  by (metis is_finite_subset match_float_finite)

lemma is_valid_nonempty: "{a::representation. is_valid x a} \<noteq> {}"
  by (metis Collect_empty_eq is_valid_special(2))

lemma is_finite_nonempty: "{a::representation. is_finite x a} \<noteq> {}"
proof -
  have "(0, 0, 0) \<in> {a. is_finite x a}"
    by (auto simp: is_zero_def is_valid_def is_finite_def)
  then show ?thesis by (metis empty_iff)
qed

lemma is_finite_closest:
  fixes v :: "representation \<Rightarrow> real"
  shows "is_finite f (closest v p {a. is_finite f a} x)"
  by (metis closest_in_set is_finite_finite is_finite_nonempty mem_Collect_eq)

lemma is_valid_closest:
  fixes v :: "representation \<Rightarrow> real"
  shows "is_valid f (closest v p {a. is_finite f a} x)"
  by (metis is_finite_closest is_finite_def)

lemma is_valid_round: "is_valid f (round f To_nearest x)"
proof -
  have "is_valid f (minus_infinity f)"
    and "is_valid f (plus_infinity f)"
    and "is_valid f (closest (valof f) (\<lambda>a. even (fraction a)) {a. is_finite f a} x)"
    using is_valid_special is_valid_closest by auto
  then have "is_valid f (round f To_nearest x)" by auto
  then show ?thesis by auto
qed

lemma zerosign_valid:
  assumes "is_valid x a"
  shows "is_valid x (zerosign x s a)"
  using is_valid_special by (metis assms zerosign_def)

lemma defloat_float_zerosign_round:
  "Rep_float(Abs_float (zerosign float_format s (round float_format To_nearest x))) =
    zerosign float_format s (round float_format To_nearest x)"
  by (metis is_valid_round mem_Collect_eq zerosign_valid Abs_float_inverse)


subsection \<open>Properties about ordering and bounding\<close>

text \<open>Lifting of non-exceptional comparisons.\<close>
lemma float_lt [simp]:
  assumes "Finite a" "Finite b"
  shows "a < b \<longleftrightarrow> Val a < Val b"
proof
  assume "Val a < Val b"
  moreover have "\<not> Isnan a" and "\<not> Isnan b" and "\<not> Infinity a" and "\<not> Infinity b"
    using assms by (auto simp: finite_nan finite_infinity)
  ultimately have "fcompare float_format (Rep_float a) (Rep_float b) = Lt"
    by (auto simp add: Infinity_def Isnan_def Val_def fcompare_def)
  then show "a < b" by (auto simp: less_float_def)
next
  assume "a < b"
  then have lt: "fcompare float_format (Rep_float a) (Rep_float b) = Lt"
    by (simp add: less_float_def)
  have "\<not> Isnan a" and "\<not> Isnan b" and "\<not> Infinity a" and "\<not> Infinity b"
    using assms by (auto simp: finite_nan finite_infinity)
  then show "Val a < Val b"
    using lt assms
    by (simp add: fcompare_def Isnan_def Infinity_def Val_def split: if_split_asm)
qed

lemma float_eq [simp]:
  assumes "Finite a" "Finite b"
  shows "a \<doteq> b \<longleftrightarrow> Val a = Val b"
proof
  assume *: "Val a = Val b"
  have "\<not> Isnan a" and "\<not> Isnan b" and "\<not> Infinity a" and "\<not> Infinity b"
    using assms float_distinct_finite by auto
  with * have "fcompare float_format (Rep_float a) (Rep_float b) = Eq"
    by (auto simp add: Infinity_def Isnan_def Val_def fcompare_def)
  then show "a \<doteq> b" by (auto simp: float_eq_def)
next
  assume "a \<doteq> b"
  then have eq: "fcompare float_format (Rep_float a) (Rep_float b) = Eq"
    by (simp add: float_eq_def)
  have "\<not> Isnan a" and "\<not> Isnan b" and "\<not> Infinity a" and "\<not> Infinity b"
    using assms float_distinct_finite by auto
  then show "Val a = Val b"
    using eq assms
    by (simp add: fcompare_def Isnan_def Infinity_def Val_def split: if_split_asm)
qed

lemma float_le [simp]:
  assumes "Finite a" "Finite b"
  shows "a \<le> b \<longleftrightarrow> Val a \<le> Val b"
proof -
  have "a \<le> b \<longleftrightarrow>  a < b \<or> a \<doteq> b"
    by (auto simp add: less_eq_float_def less_float_def float_eq_def)
  then show ?thesis
    by (auto simp add: assms)
qed

text \<open>Reflexivity of equality for non-NaNs.\<close>
lemma float_eq_refl [simp]: "a \<doteq> a \<longleftrightarrow> \<not> Isnan a"
  by (auto simp add: Infinity_def Isnan_def Val_def fcompare_def float_eq_def)

text \<open>Properties about Ordering.\<close>
lemma float_lt_trans: "Finite a \<Longrightarrow> Finite b \<Longrightarrow> Finite c \<Longrightarrow> a < b \<Longrightarrow> b < c \<Longrightarrow> a < c"
  by (auto simp: le_trans)

lemma float_le_less_trans: "Finite a \<Longrightarrow> Finite b \<Longrightarrow> Finite c \<Longrightarrow> a \<le> b \<Longrightarrow> b < c \<Longrightarrow> a < c"
  by (auto simp: le_trans)

lemma float_le_trans: "Finite a \<Longrightarrow> Finite b \<Longrightarrow> Finite c \<Longrightarrow> a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
  by (auto simp: le_trans)

lemma float_le_neg: "Finite a \<Longrightarrow> Finite b \<Longrightarrow> \<not> a < b \<longleftrightarrow> b \<le> a"
  by auto


text \<open>Properties about bounding.\<close>

lemma float_le_infinity [simp]: "\<not> Isnan a \<Longrightarrow> a \<le> Plus_infinity"
  by (auto simp: Isnan_def fcompare_def is_nan_def is_infinity_def plus_infinity_def
      Plus_infinity_def less_eq_float_def Abs_float_inverse emax_def is_valid_def)

lemma [simp]: "Plus_zero \<le> Abs_float (topfloat float_format)"
  by (auto simp: fcompare_def is_nan_def less_eq_float_def topfloat_def float_format_def
      Abs_float_inverse emax_def is_infinity_def is_zero_def is_valid_def Plus_zero_def)

lemma valof_topfloat: "valof float_format (topfloat float_format) = largest float_format"
  by (simp add: emax_def float_format_def topfloat_def largest_def)

lemma float_frac_le: "Finite a \<Longrightarrow> Fraction a \<le> 2^52 - 1"
  by (cases a) (auto simp: Abs_float_inverse float_defs is_valid_def)

lemma float_exp_le: "Finite a \<Longrightarrow> Exponent a \<le> 2046"
  by (cases a) (auto simp: emax_def float_defs is_normal_def is_denormal_def is_zero_def)

lemma float_sign_le: "(-1::real)^(Sign a) = 1 \<or> (-1::real)^(Sign a) = -1"
  by (metis neg_one_even_power neg_one_odd_power)

lemma exp_less: "a \<le> b \<Longrightarrow> (2::real)^a \<le> 2^b" for a b :: nat
  by auto

lemma div_less: "a \<le> b \<and> c > 0 \<Longrightarrow> a/c \<le> b/c" for a b c :: "'a::linordered_field"
  by (metis divide_le_cancel less_asym)

lemma finite_topfloat: "Finite Topfloat"
  by (auto simp: float_defs Topfloat_def topfloat_def Abs_float_inverse
      emax_def is_normal_def is_valid_def)

lemma valof_eq:
  "\<And>r. valof fmt r =
    (if exponent r = 0
     then (-1)^sign r * (2 / (2^bias fmt)) * real (fraction r)/2^(fracwidth fmt)
     else (-1)^sign r * ((2^exponent r) / (2^bias fmt)) * (1 + real (fraction r)/2^fracwidth fmt))"
  by auto

lemma float_le_topfloat:
  assumes "Finite a"
  shows "a \<le> Topfloat"
proof -
  have vt: "valof float_format (topfloat float_format) =
      ((2^2046) / (2^bias float_format)) * (1 + (2^52 - 1)/2^fracwidth float_format)"
    by (auto simp: emax_def float_format_def topfloat_def)
  have frale: "Fraction a \<le> 2^52 - 1"
    by (rule float_frac_le [OF assms])
  moreover from assms have exple: "Exponent a \<le> 2046"
    by (rule float_exp_le)
  ultimately have "Fraction a/2^(fracwidth float_format) \<le> (2^52 - 1)/2^(fracwidth float_format)"
    by (auto simp: float_format_def)
  then have "(2 / (2^bias float_format)) * (Fraction a/2^(fracwidth float_format)) \<le>
      (2 / (2^bias float_format)) * ((2^52 - 1)/2^(fracwidth float_format))"
    by (auto simp: float_format_def bias_def)
  then have ineq: "0 < 1 + Fraction a/2^fracwidth float_format"
       "(1 + Fraction a/2^fracwidth float_format) \<le> 1 + (2^52 - 1)/2^fracwidth float_format"
    by (auto simp: float_format_def bias_def)
  then have "0 < (2::real)^Exponent a / (2^bias float_format)"
    by (metis zero_less_divide_iff zero_less_numeral zero_less_power)
  then have gt0: "0 < (2^Exponent a / 2^bias float_format) * (1 + Fraction a/2^fracwidth float_format)"
    using ineq by (metis zero_less_mult_iff)
  moreover
  have "(2::real)^Exponent a / (2^bias float_format) \<le> (2^2046) / (2^bias float_format)"
    by (metis exple exp_less div_less zero_less_numeral zero_less_power)
  ultimately
  have "(2^Exponent a / 2^bias float_format) * (1 + Fraction a/2^fracwidth float_format) \<le>
      valof float_format (topfloat float_format)"
    by (metis vt ineq div_0 pos_divide_less_eq mult_mono' less_eq_real_def)
  then
  have "1 * (2^Exponent a / 2^bias float_format) * (1 + Fraction a / 2^fracwidth float_format) \<le>
      valof float_format (topfloat float_format)"
    and "-1* (2^Exponent a / 2^bias float_format) * (1 + Fraction a / 2^fracwidth float_format) \<le>
      valof float_format (topfloat float_format)"
    using gt0 by auto
  then have nzexp: \<comment> \<open>nonzero exponent case\<close>
    "(-1)^(Sign a) * (2^Exponent a / 2^bias float_format) *
      (1 + Fraction a/2^fracwidth float_format) \<le> valof float_format (topfloat float_format)"
    by (metis float_sign_le)
  have "-1* (2 / (2^bias float_format)) * (Fraction a/2^(fracwidth float_format)) \<le>
      valof float_format (topfloat float_format)"
    and "1 * (2 / (2^bias float_format)) * (Fraction a/2^(fracwidth float_format)) \<le>
      valof float_format (topfloat float_format)"
    using frale vt by (auto simp: float_format_def bias_def)
  then have  \<comment> \<open>zero exponent case\<close>
    "(-1)^(Sign a)*(2 / (2^bias float_format)) * (Fraction a/2^(fracwidth float_format)) \<le>
      valof float_format (topfloat float_format)"
    by (metis float_sign_le)
  then have "Val a \<le> Val Topfloat"
    using nzexp
    by (cases a) (auto simp: float_defs Abs_float_inverse Topfloat_def is_valid_special)
  then show ?thesis
    by (metis assms finite_topfloat float_le)
qed

lemma topfloat_eq_largest: "Val Topfloat = largest float_format"
proof -
  have "Val Topfloat = valof float_format (topfloat float_format)"
    by (simp add: Abs_float_inverse Topfloat_def is_valid_special Val_def)
  also have "\<dots> = largest float_format"
    by (simp add: emax_def largest_def float_format_def topfloat_def)
  finally show ?thesis .
qed

lemma float_val_le_largest:
  assumes "Finite a"
  shows "Val a \<le> largest float_format"
  by (metis assms finite_topfloat float_le float_le_topfloat topfloat_eq_largest)

lemma float_val_lt_threshold:
  assumes "Finite a"
  shows "Val a < threshold float_format"
proof -
  have "Val a \<le> largest float_format"
    by (rule float_val_le_largest [OF assms])
  also have "\<dots> < threshold float_format"
    by (auto simp: float_format_def largest_def threshold_def bias_def)
  finally show ?thesis .
qed


subsection \<open>Algebraic properties about basic arithmetic\<close>

text \<open>Commutativity of addition.\<close>
lemma
  assumes "Finite a" "Finite b"
  shows float_plus_comm_eq: "a + b = b + a"
    and float_plus_comm: "Finite (a + b) \<Longrightarrow> (a + b) \<doteq> (b + a)"
proof -
  have "\<not> Isnan a" and "\<not> Isnan b" and "\<not> Infinity a" and "\<not> Infinity b"
    using assms by (auto simp: finite_nan finite_infinity)
  then show "a + b = b + a"
    by (simp add: float_defs fadd_def plus_float_def add.commute)
  then show "Finite (a + b) \<Longrightarrow> (a + b) \<doteq> (b + a)"
    by (metis float_eq)
qed

text \<open>Showing \<open>-(- a) = a\<close>.\<close>
lemma sign_double_neg [simp]:
  assumes "is_valid x a"
  shows "1 - (1 - sign a) = sign a"
proof -
  from assms have "sign a < 2"
    by (auto simp: is_valid_def)
  then show "(1 - (1 - sign a)) = sign a"
    by auto
qed

lemma float_double_neg_eq [simp]:
  assumes "\<not> Isnan a"
  shows "float_neg (float_neg a) = a"
proof -
  have isv: "is_valid float_format ((1 - (Sign a), Exponent a, Fraction a))"
    by (cases a) (auto simp: float_defs Abs_float_inverse is_valid_def)
  have "float_neg (float_neg a) =
      Abs_float (fneg float_format To_nearest
        (Rep_float (Abs_float (1 - (Sign a), Exponent a, Fraction a))))"
    by (simp add: float_defs float_neg_def fneg_def)
  also have "\<dots> = Abs_float (fneg float_format To_nearest (1 - (Sign a), Exponent a, Fraction a))"
    using isv by (simp add: Abs_float_inverse)
  also have "\<dots> = Abs_float (1 - (1 - (Sign a)), Exponent a, Fraction a)"
    by (auto simp: fneg_def)
  also have "\<dots> = Abs_float ((Sign a), Exponent a, Fraction a)"
    by (metis Sign_def is_valid_defloat sign_double_neg)
  finally show "float_neg (float_neg a) = a"
    by (simp add: float_defs) (metis Rep_float_inverse exponent.elims fraction.simps sign.simps)
qed

lemma float_double_neg [simp]: "\<not> Isnan a \<Longrightarrow> float_neg (float_neg a) \<doteq> a"
  by auto

text \<open>The floating-point number a falls into the same category as the negation of \<open>a\<close>.\<close>
lemma neg_zero: "is_zero x a \<longleftrightarrow> is_zero x (fneg x m a)"
  by (auto simp: fneg_def is_zero_def)

lemma float_neg_zero [simp]: "Iszero (float_neg a) = Iszero a"
proof -
  have isv: "is_valid float_format ((1 - (Sign a), Exponent a, Fraction a))"
    by (cases a) (auto simp: float_defs Abs_float_inverse is_valid_def)
  have "Iszero (float_neg a) = Iszero (Abs_float (fneg float_format To_nearest (Rep_float a)))"
    by (auto simp: Iszero_def float_neg_def)
  also have "\<dots> = is_zero float_format (fneg float_format To_nearest (Rep_float a))"
    using isv by (auto simp: float_defs Abs_float_inverse fneg_def)
  also have "\<dots> = Iszero a" by (metis Iszero_def neg_zero)
  finally show ?thesis
    by metis
qed

lemma neg_infinity [simp]: "is_infinity x (fneg x m a) = is_infinity x a"
  by (auto simp: fneg_def is_infinity_def)

lemma neg_normal [simp]: "is_normal x (fneg x m a) = is_normal x a"
  by (auto simp: fneg_def is_normal_def)

lemma float_neg_normal [simp]: "Isnormal (float_neg a) = Isnormal a"
proof -
  have "is_valid float_format (1 - (Sign a), Exponent a, Fraction a)"
    by (cases a) (auto simp: float_defs Abs_float_inverse is_valid_def)
  then have "Isnormal (float_neg a) =
      is_normal float_format (fneg float_format To_nearest (Rep_float a))"
    by (auto simp: Abs_float_inverse float_defs fneg_def float_neg_def)
  also have "\<dots> = Isnormal a"
    by (metis Isnormal_def neg_normal)
  finally show ?thesis .
qed

lemma neg_denormal [simp]: "is_denormal x (fneg x m a) \<longleftrightarrow> is_denormal x a"
  by (auto simp: fneg_def is_denormal_def)

lemma float_neg_denormal [simp]: "Isdenormal (float_neg a) \<longleftrightarrow> Isdenormal a"
proof -
  have "is_valid float_format (1 - (Sign a), Exponent a, Fraction a)"
    by (cases a) (auto simp: float_defs Abs_float_inverse is_valid_def)
  then have "Isdenormal (Abs_float (fneg float_format To_nearest (Rep_float a))) =
      is_denormal float_format (fneg float_format To_nearest (Rep_float a))"
    by (auto simp: float_defs Abs_float_inverse fneg_def)
  also have "\<dots> = Isdenormal a"
    by (metis Isdenormal_def neg_denormal)
  finally show ?thesis
    by (simp add: float_neg_def)
qed

lemma neg_valid: "is_valid x a \<Longrightarrow> is_valid x (fneg x m a)"
  by (auto simp: fneg_def is_valid_def)

lemma neg_finite: "is_finite x a \<Longrightarrow> is_finite x (fneg x m a) "
  by (metis is_finite_def neg_denormal neg_normal neg_valid neg_zero)

lemma float_neg_finite: "Finite a \<Longrightarrow> Finite (float_neg a)"
  by (metis Finite_def float_neg_denormal float_neg_normal float_neg_zero)

text \<open>The sign of a and the sign of a's negation is different.\<close>
lemma float_neg_sign: "(Sign a) \<noteq> (Sign (float_neg a))"
proof -
  have "Sign a < 2"
    by (metis Sign_def is_valid_defloat sign_0_1)
  moreover have "Sign a = 0 \<Longrightarrow> Sign (float_neg a) = 1"
    by (cases a) (auto simp: Sign_def fneg_def float_neg_def Abs_float_inverse is_valid_def)
  moreover have "Sign a = 1 \<Longrightarrow> Sign (float_neg a) = 0"
    by (cases a) (auto simp: Sign_def fneg_def float_neg_def Abs_float_inverse is_valid_def)
  ultimately show ?thesis
    by (metis One_nat_def less_2_cases zero_neq_one)
qed

lemma float_neg_sign1: "Sign a = Sign (float_neg b) \<longleftrightarrow> Sign a \<noteq> Sign b"
  by (metis Sign_def float_neg_sign is_valid_defloat less_2_cases sign_0_1)

lemma neg_val:
  assumes "is_finite float_format a"
  shows "valof float_format (fneg float_format m a) = - valof float_format a" (is "?L = ?R")
proof -
  have A: "?L =
    valof float_format
      (sign (fneg float_format m a),
        exponent (fneg float_format m a), fraction (fneg float_format m a))"
    by (metis exponent.simps fneg_def fraction.simps sign.simps)
  also have "\<dots> = valof float_format (1 - sign a, exponent a, fraction a)"
    by (metis calculation fneg_def)
  finally have Leq: "?L = valof float_format (1 - sign a, exponent a, fraction a)" .
  have C: "sign a = 0 \<longleftrightarrow> 1 - (sign a) = 1"
    by auto
  have D: "sign a = 1 \<longleftrightarrow> 1 - (sign a) = 0"
    using sign_0_1 assms by (auto simp: is_valid_def is_finite_def)
  then have "valof float_format (0, exponent a, fraction a) =
      - valof float_format (1, exponent a, fraction a)"
    by auto
  then show "?thesis"
    using A C D Leq
    by (metis diff_0_right exponent.simps fraction.cases fraction.simps
      less_one minus_diff_eq neq0_conv sign.simps zero_less_diff)
qed

lemma float_neg_val:
  assumes "Finite b"
  shows "Val (float_neg b) = - (Val b)"
proof -
  have "Val (float_neg b) =
      valof float_format (Sign (float_neg b), Exponent (float_neg b), Fraction (float_neg b))"
    unfolding float_defs
    by (metis prod.exhaust exponent.simps fraction.simps sign.simps)
  also have "\<dots> = valof float_format (1 - (Sign b), Exponent b, Fraction b)"
    using float_neg_def fneg_def Abs_float_inverse
    by (cases b) (auto simp: float_defs is_valid_def)
  finally have Vb: "Val (float_neg b) =
    valof float_format (1 - (Sign b), Exponent b, Fraction b)" .
  have C: "Val b = valof float_format (Sign b, Exponent b, Fraction b)"
    unfolding float_defs
    by (metis exponent.simps fraction.simps prod.exhaust sign.simps)
  then show ?thesis
    using assms Vb C
    unfolding Val_def Exponent_def Finite_def Fraction_def Isdenormal_def
      Isnormal_def Iszero_def Sign_def
    by (metis fneg_def is_finite_def is_valid_defloat neg_val)
qed

text \<open>Showing \<open>a + (- b) = a - b\<close>.\<close>
lemma float_neg_add:
  "Finite a \<Longrightarrow> Finite b \<Longrightarrow> Finite (a - b) \<Longrightarrow> Val a + Val (float_neg b) = Val a - Val b"
  by (simp add: float_neg_val)

lemma float_plus_minus:
  assumes "Finite a" "Finite b" "Finite (a - b)"
  shows "(a + float_neg b) \<doteq> (a - b)"
proof -
  have nab: "\<not> Isnan a" "\<not> Isnan (float_neg b)" "\<not> Infinity a" "\<not> Infinity (float_neg  b)"
    using assms by (auto simp: finite_nan finite_infinity float_neg_finite)
  have "a - b =
    Abs_float
      (zerosign float_format
        (if Iszero a \<and> Iszero b \<and> Sign a \<noteq> Sign b then (Sign a) else 0)
        (round float_format To_nearest (Val a - Val b)))"
    using assms finite_infinity finite_nan
    by (simp add: fsub_def minus_float_def float_defs [symmetric])
  also have "\<dots> =
    Abs_float
      (zerosign float_format
        (if Iszero a \<and> Iszero (float_neg b) \<and> Sign a = Sign (float_neg b) then Sign a else 0)
        (round float_format To_nearest (Val a + Val (float_neg b))))"
    using assms by (simp add: float_neg_sign1 float_neg_add)
  also have "\<dots> = a + float_neg b"
    using nab by (auto simp: float_defs fadd_def plus_float_def)
  finally show ?thesis
    using assms by (metis float_eq)
qed

lemma bottomfloat_eq_m_largest: "Val Bottomfloat = - largest float_format"
proof -
  have "Val Bottomfloat = valof float_format (bottomfloat float_format)"
    by (simp add: Abs_float_inverse Bottomfloat_def is_valid_special Val_def)
  also have "\<dots> = - largest float_format"
    by (simp add: emax_def largest_def float_format_def bottomfloat_def)
  finally show ?thesis .
qed

lemma Bottomfloat_m_Topfloat: "Val Bottomfloat = - Val Topfloat"
  by (metis bottomfloat_eq_m_largest topfloat_eq_largest)

lemma float_val_ge_bottomfloat: "Finite a \<Longrightarrow> Val a \<ge> Val Bottomfloat"
  by (metis Bottomfloat_m_Topfloat float_neg_finite float_neg_val float_val_le_largest
      minus_minus neg_le_iff_le topfloat_eq_largest)

lemma finite_Bottomfloat: "Finite Bottomfloat"
  by (auto simp: float_defs Bottomfloat_def bottomfloat_def Abs_float_inverse
      emax_def is_normal_def is_valid_def)

lemma float_ge_bottomfloat: "Finite a \<Longrightarrow> a \<ge> Bottomfloat"
  by (metis finite_Bottomfloat float_le float_val_ge_bottomfloat)

lemma sign_Rep_Topfloat [simp]: "sign (Rep_float Topfloat) = 0"
  using is_valid_special
  by (auto simp add: Abs_float_inverse Topfloat_def topfloat_def)

lemma exponent_Rep_Topfloat [simp]:
  "exponent (Rep_float Topfloat) = emax float_format - Suc 0"
  using is_valid_special
  by (auto simp add: Abs_float_inverse Topfloat_def topfloat_def)

lemma fraction_Rep_Topfloat [simp]:
  "fraction (Rep_float Topfloat) = 2 ^ fracwidth float_format - Suc 0"
  using is_valid_special
  by (auto simp add: Abs_float_inverse Topfloat_def topfloat_def)

lemma Bottomfloat_fneg_Topfloat: "Bottomfloat = float_neg Topfloat"
  using is_valid_special
  by (auto simp add: Abs_float_inject float_neg_def fneg_def Bottomfloat_def bottomfloat_def)

lemma float_val_ge_largest:
  assumes "Finite a"
  shows "Val a \<ge> - largest float_format"
proof -
  have "Val Bottomfloat = valof float_format (bottomfloat float_format)"
    using Bottomfloat_def Abs_float_inverse is_valid_special
    by (metis (full_types) Val_def mem_Collect_eq)
  also have "\<dots> = - largest float_format"
    by (auto simp: emax_def bias_def bottomfloat_def float_format_def largest_def)
  finally have "Val Bottomfloat = -largest float_format" .
  then show ?thesis
    using float_val_ge_bottomfloat by (metis assms)
qed

lemma float_val_gt_threshold:
  assumes "Finite a"
  shows "Val a > - threshold float_format"
proof -
  have largest: "Val a \<ge> -largest float_format"
    using float_val_ge_bottomfloat assms by (metis float_val_ge_largest)
  then have "-largest float_format > - threshold float_format"
    by (auto simp: bias_def threshold_def float_format_def largest_def)
  then show ?thesis
    by (metis largest less_le_trans)
qed

text \<open>Showing \<open>abs (- a) = abs a\<close>.\<close>
lemma float_abs [simp]: "\<not> Isnan a \<Longrightarrow> float_abs (float_neg a) = float_abs a"
  by (cases a) (auto simp: float_abs_def float_neg_def fneg_def Abs_float_inverse is_valid_def)

lemma neg_zerosign: "fneg x m (zerosign x s a) = zerosign x (1 - s) (fneg x m a)"
  by (auto simp: fneg_def zerosign_def is_zero_def is_valid_def)

lemma finite_valid: "is_finite x a \<Longrightarrow> is_valid x a"
  by (cases a) (metis is_finite_def)


subsection \<open>Properties about Rounding Errors\<close>

definition error :: "real \<Rightarrow> real"
  where "error x = Val (Abs_float (round float_format To_nearest x)) - x"

lemma bound_at_worst_lemma:
  assumes threshold: "\<bar>x\<bar> < threshold float_format"
  assumes finite: "is_finite float_format a"
  shows "\<bar>valof float_format (round float_format To_nearest x) - x\<bar> \<le> \<bar>valof float_format a - x\<bar>"
proof -
  have "round float_format To_nearest x =
      closest (valof float_format)  (\<lambda>a. even (fraction a)) {a. is_finite float_format a} x"
    using threshold by (metis abs_less_iff le_minus_iff not_less round.simps(1))
  then have "is_closest (valof float_format) {a. is_finite float_format a} x
      (round float_format To_nearest x)"
    using closest_is_closest by (metis is_finite_finite is_finite_nonempty)
  then show ?thesis
    using finite is_closest_def by (metis mem_Collect_eq)
qed

lemma defloat_float_round:
  "Rep_float (Abs_float (round float_format To_nearest x)) =
    round (float_format) To_nearest x"
  by (metis mem_Collect_eq Abs_float_inverse is_valid_round)

lemma error_at_worst_lemma:
  assumes "\<bar>x\<bar> < threshold float_format" and "Finite a"
  shows "\<bar>error x\<bar> \<le> \<bar>Val a - x\<bar> "
proof -
  have "Finite a = is_finite float_format (Rep_float a)"
    using is_valid_defloat
    by (metis Finite_def Isdenormal_def Isnormal_def Iszero_def is_finite_def)
  then have "\<bar>Val(Abs_float(round float_format To_nearest x)) - x\<bar> \<le> \<bar>Val a - x\<bar>"
    using bound_at_worst_lemma assms
    by (metis Val_def defloat_float_round)
  then show ?thesis
    by (metis error_def)
qed

lemma error_is_zero [simp]:
  assumes "Finite a"
  shows "error (Val a) = 0"
proof -
  have "\<bar>Val a\<bar> < threshold float_format"
    by (metis abs_less_iff minus_less_iff float_val_gt_threshold float_val_lt_threshold assms)
  then show ?thesis
    by (metis abs_le_zero_iff abs_zero diff_self error_at_worst_lemma assms)
qed

lemma valof_scale_up:
  assumes "e \<noteq> 0"
  shows "valof float_format (s::nat, e + k, f) = 2^k * valof float_format (s, e, f)"
  using assms
  by auto (metis add.commute power_add)

lemma is_finite_zerosign:
  assumes "is_finite float_format a"
  shows "is_finite float_format (zerosign float_format s a)"
  using assms
  by (metis (full_types) exponent.simps fraction.simps is_finite_def is_zero_def
    minus_zero_def plus_zero_def zerosign_def zerosign_valid)

lemma defloat_float_zerosign_round_finite:
  assumes threshold: "\<bar>x\<bar> < threshold float_format"
  shows "is_finite float_format (zerosign float_format s (round float_format To_nearest x))"
proof -
  have "round float_format To_nearest x =
      (closest (valof float_format) (\<lambda>a. even (fraction a)) {a. is_finite float_format a} x)"
    using threshold by (metis (full_types) abs_less_iff leD le_minus_iff round.simps(1))
  then have "is_finite float_format (round float_format To_nearest x) "
    by (metis is_finite_closest)
  then show ?thesis
    using is_finite_zerosign by auto
qed

lemma signzero_zero:
  "is_zero float_format a \<Longrightarrow> valof float_format (zerosign float_format s a) = 0"
  by (auto simp add: zerosign_def)

lemma val_zero: "is_zero float_format a \<Longrightarrow> valof float_format a = 0"
  by (cases a) (auto simp add: is_zero_def)

lemma float_add:
  assumes "Finite a"
    and "Finite b"
    and threshold: "\<bar>Val a + Val b\<bar> < threshold float_format"
  shows finite_float_add: "Finite (a + b)"
    and error_float_add:  "Val (a + b) = Val a + Val b + error (Val a + Val b)"
proof -
  have "\<not> Isnan a" and "\<not> Isnan b" and "\<not> Infinity a" and "\<not> Infinity b"
    using assms float_distinct_finite by auto
  then have ab: "(a + b) =
    Abs_float (zerosign float_format
      (if Iszero a \<and> Iszero b \<and> Sign a = Sign b then (Sign a) else 0)
      (round float_format To_nearest (Val a + Val b)))"
    using assms by (auto simp add: float_defs fadd_def plus_float_def)
  then have "is_finite float_format (Rep_float (a + b))"
    by (metis threshold defloat_float_zerosign_round defloat_float_zerosign_round_finite)
  then show "Finite (a + b)"
    by (metis Finite_def Isdenormal_def Isnormal_def Iszero_def is_finite_def)
  have val_ab: "Val (a + b) =
    valof float_format (zerosign float_format
      (if Iszero a \<and> Iszero b \<and> Sign a = Sign b then (Sign a) else 0)
      (round float_format To_nearest (Val a + Val b)))"
    using defloat_float_zerosign_round
    by (auto simp: ab Infinity_def Isnan_def Val_def)
  show "Val (a + b) = Val a + Val b + error (Val a + Val b)"
  proof (cases "is_zero float_format (round float_format To_nearest (Val a + Val b))")
    case True
    have "Val a + Val b + error (Val a + Val b) =
        valof float_format (round float_format To_nearest (Val a + Val b))"
      unfolding error_def Val_def
      by (metis add_diff_cancel_left add_0_right defloat_float_round diff_add_cancel)
    then show ?thesis
      by (metis True signzero_zero val_zero val_ab)
  next
    case False
    then show ?thesis
      by (metis ab add.commute eq_diff_eq' error_def zerosign_def)
  qed
qed

lemma float_sub:
  assumes "Finite a"
    and "Finite b"
    and threshold: "\<bar>Val a - Val b\<bar> < threshold float_format"
  shows finite_float_sub: "Finite (a - b)"
    and error_float_sub: "Val (a - b) = Val a - Val b + error (Val a - Val b)"
proof -
  have "\<not> Isnan a" and "\<not> Isnan b" and "\<not> Infinity a" and "\<not> Infinity b"
    using assms by (auto simp: finite_nan finite_infinity)
  then have ab: "a - b =
    Abs_float (zerosign float_format
      (if Iszero a \<and> Iszero b \<and> Sign a \<noteq> Sign b then Sign a else 0)
      (round float_format To_nearest (Val a - Val b)))"
    using assms by (auto simp add: float_defs fsub_def minus_float_def)
  then have "is_finite float_format (Rep_float (a - b))"
   by (metis threshold defloat_float_zerosign_round_finite defloat_float_zerosign_round)
  then show "Finite (a - b)"
    by (metis Finite_def Isdenormal_def Isnormal_def Iszero_def is_finite_def)
  have val_ab: "Val (a - b) =
    valof float_format (zerosign float_format
      (if Iszero a \<and> Iszero b \<and> Sign a \<noteq> Sign b then Sign a else 0)
      (round float_format To_nearest (Val a - Val b)))"
    using defloat_float_zerosign_round
    by (auto simp: ab Infinity_def Isnan_def Val_def)
  show "Val (a - b) = Val a - Val b + error (Val a - Val b)"
  proof (cases "is_zero float_format (round float_format To_nearest (Val a - Val b))")
    case True
    have "Val a - Val b + error (Val a - Val b) =
        valof float_format (round float_format To_nearest (Val a - Val b))"
      unfolding error_def Val_def
      by (metis add_diff_cancel_left add_0_right defloat_float_round diff_add_cancel)
    then show ?thesis
      by (metis True signzero_zero val_zero val_ab)
  next
    case False
    then show ?thesis
      by (metis ab add.commute eq_diff_eq' error_def zerosign_def)
  qed
qed

lemma float_mul:
  assumes "Finite a"
    and "Finite b"
    and threshold: "\<bar>Val a * Val b\<bar> < threshold float_format"
  shows finite_float_mul: "Finite (a * b)"
    and error_float_mul: "Val (a * b) = Val a * Val b + error (Val a * Val b)"
proof -
  have non: "\<not> Isnan a" "\<not> Isnan b" "\<not> Infinity a" "\<not> Infinity b"
    using assms float_distinct_finite by auto
  then have ab: "a * b =
    Abs_float (zerosign float_format (of_bool (Sign a \<noteq> Sign b))
      (round float_format To_nearest (Val a * Val b)))"
    using assms by (auto simp: float_defs fmul_def times_float_def)
  then have "is_finite float_format (Rep_float (a * b))"
    by (metis threshold defloat_float_zerosign_round_finite defloat_float_zerosign_round)
  then show "Finite (a * b)"
    by (metis Finite_def Isdenormal_def Isnormal_def Iszero_def is_finite_def)
  have val_ab: "Val (a * b) =
      valof float_format (zerosign float_format (of_bool (Sign a \<noteq> Sign b))
        (round float_format To_nearest (Val a * Val b)))"
    using defloat_float_zerosign_round
    by (auto simp: ab float_defs of_bool_def)
  show "Val (a * b) = Val a * Val b + error (Val a * Val b)"
  proof (cases "is_zero float_format (round float_format To_nearest (Val a * Val b))")
    case True
    have "Val a * Val b + error (Val a * Val b) =
        valof float_format (round float_format To_nearest (Val a * Val b))"
      unfolding error_def Val_def
      by (metis add_diff_cancel_left add_0_right defloat_float_round diff_add_cancel)
    then show ?thesis
      by (metis True signzero_zero val_zero val_ab)
  next
    case False then show ?thesis
      by (metis ab add.commute eq_diff_eq' error_def zerosign_def)
  qed
qed

lemma float_div:
  assumes "Finite a"
    and "Finite b"
    and not_zero: "\<not> Iszero b"
    and threshold: "\<bar>Val a / Val b\<bar> < threshold float_format"
  shows finite_float_div: "Finite (a / b)"
    and error_float_div: "Val (a / b) = Val a / Val b + error (Val a / Val b)"
proof -
  have ab: "a / b =
    Abs_float (zerosign float_format (of_bool (Sign a \<noteq> Sign b))
      (round float_format To_nearest (Val a / Val b)))"
     using assms
     by (simp add: divide_float_def fdiv_def finite_infinity finite_nan not_zero float_defs [symmetric])
  then have "is_finite float_format (Rep_float(a / b))"
    by (metis threshold defloat_float_zerosign_round_finite defloat_float_zerosign_round)
  then show "Finite (a / b)"
    by (metis Finite_def Isdenormal_def Isnormal_def Iszero_def is_finite_def)
  have val_ab: "Val (a / b) =
      valof float_format (zerosign float_format (of_bool (Sign a \<noteq> Sign b))
        (round float_format To_nearest (Val a / Val b)))"
    using defloat_float_zerosign_round
    by (auto simp: ab float_defs of_bool_def)
  show "Val (a / b) = Val a / Val b + error (Val a / Val b)"
  proof (cases "is_zero float_format (round float_format To_nearest (Val a / Val b))")
    case True
    have "Val a / Val b + error (Val a / Val b) =
        valof float_format (round float_format To_nearest (Val a / Val b))"
      unfolding error_def Val_def
      by (metis add_diff_cancel_left add_0_right defloat_float_round diff_add_cancel)
    then show ?thesis
      by (metis True signzero_zero val_zero val_ab)
  next
    case False then show ?thesis
      by (metis ab add.commute eq_diff_eq' error_def zerosign_def)
  qed
qed

end
