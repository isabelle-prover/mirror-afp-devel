(* Formalization of IEEE-754 Standard for binary floating-point arithmetic *)
(* Author: Lei Yu, University of Cambridge *)

section \<open>Specification of the IEEE standard\<close>

theory IEEE
imports Complex_Main
begin

type_synonym format = "nat \<times> nat"
type_synonym representation = "nat \<times> nat \<times> nat"


subsection \<open>Derived parameters for floating point formats\<close>

fun expwidth :: "format \<Rightarrow> nat"
  where "expwidth (ew, fw) = ew"

fun fracwidth :: "format \<Rightarrow> nat"
  where "fracwidth (ew, fw) = fw"

definition wordlength :: "format \<Rightarrow> nat"
  where "wordlength x = expwidth x + fracwidth x + 1"

definition emax :: "format \<Rightarrow> nat"
  where "emax x =  2^(expwidth x) - 1"

definition bias :: "format \<Rightarrow> nat"
  where "bias x = 2^(expwidth x - 1) - 1"


subsection \<open>Predicates for the four IEEE formats\<close>

definition is_single :: "format \<Rightarrow> bool"
  where "is_single x \<longleftrightarrow> expwidth x = 8 \<and> wordlength x = 32"

definition is_double :: "format \<Rightarrow> bool"
  where "is_double x \<longleftrightarrow> expwidth x = 11 \<and> wordlength x = 64"

definition is_single_extended :: "format \<Rightarrow> bool"
  where "is_single_extended x \<longleftrightarrow> expwidth x \<ge> 11 \<and> wordlength x \<ge> 43"

definition is_double_extended :: "format \<Rightarrow> bool"
  where "is_double_extended x \<longleftrightarrow> expwidth x \<ge> 15 \<and> wordlength x \<ge> 79"


subsection \<open>Extractors for fields\<close>

fun sign :: "representation \<Rightarrow> nat"
  where "sign (s, e, f) = s"

fun exponent :: "representation \<Rightarrow> nat"
  where "exponent (s, e, f) = e"

fun fraction :: "representation \<Rightarrow> nat"
  where "fraction (s, e, f) = f"


subsection \<open>Partition of numbers into disjoint classes\<close>

definition is_nan :: "format \<Rightarrow> representation \<Rightarrow> bool"
  where "is_nan x a \<longleftrightarrow> exponent a = emax x \<and> fraction a \<noteq> 0"

definition is_infinity :: "format \<Rightarrow> representation \<Rightarrow> bool"
  where "is_infinity x a \<longleftrightarrow> exponent a = emax x \<and> fraction a = 0"

definition is_normal :: "format \<Rightarrow> representation \<Rightarrow> bool"
  where "is_normal x a \<longleftrightarrow> 0 < exponent a \<and> exponent a < emax x"

definition is_denormal :: "format \<Rightarrow> representation \<Rightarrow> bool"
  where "is_denormal x a \<longleftrightarrow> exponent a = 0 \<and> fraction a \<noteq> 0"

definition is_zero :: "format \<Rightarrow> representation \<Rightarrow> bool"
  where "is_zero x a \<longleftrightarrow> exponent a = 0 \<and> fraction a = 0"

definition is_valid :: "format \<Rightarrow> representation \<Rightarrow> bool"
  where "is_valid x a \<longleftrightarrow> sign a < 2 \<and> exponent a < 2^(expwidth x) \<and> fraction a < 2^(fracwidth x)"

definition is_finite :: "format \<Rightarrow> representation \<Rightarrow> bool"
  where "is_finite x a \<longleftrightarrow> is_valid x a \<and> (is_normal x a \<or> is_denormal x a \<or> is_zero x a)"


subsection \<open>Special values\<close>

definition plus_infinity :: "format \<Rightarrow> representation"
  where "plus_infinity x = (0, emax x, 0)"

definition minus_infinity :: "format \<Rightarrow> representation"
  where "minus_infinity x = (1, emax x, 0)"

definition plus_zero :: "format \<Rightarrow> representation"
  where [simp]: "plus_zero x = (0, 0, 0)"

definition minus_zero :: "format \<Rightarrow> representation"
  where [simp]: "minus_zero x = (1, 0, 0)"

definition topfloat :: "format \<Rightarrow> representation"
  where "topfloat x = (0, (emax x - 1), 2^(fracwidth x) - 1)"

definition bottomfloat :: "format \<Rightarrow> representation"
  where "bottomfloat x = (1, (emax x - 1), 2^(fracwidth x) - 1)"


subsection \<open>Negation operation on floating point values\<close>

definition minus :: "format \<Rightarrow> representation \<Rightarrow> representation"
  where [simp]: "minus x a = (1 - sign a, exponent a, fraction a)"


subsection \<open>Concrete encodings\<close>

fun encoding :: "format \<Rightarrow> representation \<Rightarrow> nat"
  where "encoding x (s, e, f) = s * power 2 (wordlength x - 1) + e * power 2 (fracwidth x) + f"


subsection \<open>Real number valuations\<close>

fun valof :: "format \<Rightarrow> representation \<Rightarrow> real"
where
  "valof x (s, e, f) =
    (if e = 0
     then (-1::real)^s * (2 / (2^bias x)) * (real f/2^(fracwidth x))
     else (-1::real)^s * ((2^e) / (2^bias x)) * (1 + real f/2^fracwidth x))"

text \<open>The largest value that can be represented in floating point format.\<close>
definition largest :: "format \<Rightarrow> real"
  where "largest x = (2^(emax x - 1) / 2^bias x) * (2 - 1/(2^fracwidth x))"

text \<open>Threshold, used for checking overflow.\<close>
definition threshold :: "format \<Rightarrow> real"
  where "threshold x = (2^(emax x - 1) / 2^bias x) * (2 - 1/(2^(Suc(fracwidth x))))"

text \<open>Unit of least precision.\<close>
definition ulp :: "format \<Rightarrow> representation \<Rightarrow> real"
  where "ulp x a = valof x (0, exponent a, 1) - valof x (0, exponent a, 0)"

text \<open>Enumerated type for rounding modes.\<close>
datatype roundmode = To_nearest | float_To_zero | To_pinfinity | To_ninfinity

text \<open>Characterization of best approximation from a set of abstract values.\<close>
definition "is_closest v s x a \<longleftrightarrow> a \<in> s \<and> (\<forall>b. b \<in> s \<longrightarrow> \<bar>v a - x\<bar> \<le> \<bar>v b - x\<bar>)"

text \<open>Best approximation with a deciding preference for multiple possibilities.\<close>
definition "closest v p s x =
  (SOME a. is_closest v s x a \<and> ((\<exists>b. is_closest v s x b \<and> p b) \<longrightarrow> p a))"


subsection \<open>Rounding\<close>

fun round :: "format \<Rightarrow> roundmode \<Rightarrow> real \<Rightarrow> representation"
where
  "round x To_nearest y =
   (if y \<le> - threshold x then minus_infinity x
    else if y \<ge> threshold x then plus_infinity x
    else closest (valof x) (\<lambda>a. even (fraction a)) {a. is_finite x a} y)"
| "round x float_To_zero y =
   (if y < - largest x then bottomfloat x
    else if y > largest x then topfloat x
    else closest (valof x) (\<lambda>a. True) {a. is_finite x a \<and> \<bar>valof x a\<bar> \<le> \<bar>y\<bar>} y)"
| "round x To_pinfinity y =
   (if y < - largest x then bottomfloat x
    else if y > largest x then plus_infinity x
    else closest (valof x) (\<lambda>a. True) {a. is_finite x a \<and> valof x a \<ge> y} y)"
| "round x To_ninfinity y =
   (if y < - largest x then minus_infinity x
    else if y > largest x then topfloat x
    else closest (valof x) (\<lambda>a. True) {a. is_finite x a \<and> valof x a \<le> y} y)"

text \<open>Rounding to integer values in floating point format.\<close>

definition is_integral :: "format \<Rightarrow> representation \<Rightarrow> bool"
  where "is_integral x a \<longleftrightarrow> is_finite x a \<and> (\<exists>n::nat. \<bar>valof x a\<bar> = real n)"

fun intround :: "format \<Rightarrow> roundmode \<Rightarrow> real \<Rightarrow> representation"
where
  "intround x To_nearest y =
    (if y \<le> - threshold x then minus_infinity x
     else if y \<ge> threshold x then plus_infinity x
     else closest (valof x) (\<lambda>a. (\<exists>n::nat. even n \<and> \<bar>valof x a\<bar> = real n)) {a. is_integral x a} y)"
|"intround x float_To_zero y =
    (if y < - largest x then bottomfloat x
     else if y > largest x then topfloat x
     else closest (valof x) (\<lambda>x. True) {a. is_integral x a \<and> \<bar>valof x a\<bar> \<le> \<bar>y\<bar>} y)"
|"intround x To_pinfinity y =
    (if y < - largest x then bottomfloat x
     else if y > largest x then plus_infinity x
     else closest (valof x) (\<lambda>x. True) {a. is_integral x a \<and> valof x a \<ge> y} y)"
|"intround x To_ninfinity y =
    (if y < - largest x then minus_infinity x
     else if y > largest x then topfloat x
     else closest (valof x) (\<lambda>x. True) {a. is_integral x a \<and> valof x a \<ge> y} y)"

text \<open>Non-standard of NaN.\<close>
definition some_nan :: "format \<Rightarrow> representation"
  where "some_nan x = (SOME a. is_nan x a)"

text \<open>Coercion for signs of zero results.\<close>
definition zerosign :: "format \<Rightarrow> nat \<Rightarrow> representation \<Rightarrow> representation"
  where "zerosign x s a =
    (if is_zero x a then (if s = 0 then plus_zero x else minus_zero x) else a)"

text \<open>Remainder operation.\<close>
definition rem :: "real \<Rightarrow> real \<Rightarrow> real"
  where "rem x y =
    (let n = closest id (\<lambda>x. \<exists>n::nat. even n \<and> \<bar>x\<bar> = real n) {x. \<exists>n :: nat. \<bar>x\<bar> = real n} (x / y)
     in x - n * y)"

definition frem :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> representation"
  where "frem x m a b =
    (if is_nan x a \<or> is_nan x b \<or> is_infinity x a \<or> is_zero x b then some_nan x
     else zerosign x (sign a) (round x m (rem (valof x a) (valof x b))))"


subsection \<open>Definitions of the arithmetic operations\<close>

definition fintrnd :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation"
  where "fintrnd x m a =
    (if is_nan x a then (some_nan x)
     else if is_infinity x a then a
     else zerosign x (sign a) (intround x m (valof x a)))"

definition fadd :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> representation"
  where "fadd x m a b =
    (if is_nan x a \<or> is_nan x b \<or> (is_infinity x a \<and> is_infinity x b \<and> sign a \<noteq> sign b)
     then some_nan x
     else if (is_infinity x a) then a
     else if (is_infinity x b) then b
     else
      zerosign x
        (if is_zero x a \<and> is_zero x b \<and> sign a = sign b then sign a
         else if m = To_ninfinity then 1 else 0)
        (round x m (valof x a + valof x b)))"

definition fsub :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> representation"
  where "fsub x m a b =
    (if is_nan x a \<or> is_nan x b \<or> (is_infinity x a \<and> is_infinity x b \<and> sign a = sign b)
     then some_nan x
     else if is_infinity x a then a
     else if is_infinity x b then minus x b
     else
      zerosign x
        (if is_zero x a \<and> is_zero x b \<and> sign a \<noteq> sign b then sign a
         else if m = To_ninfinity then 1 else 0)
        (round x m (valof x a - valof x b)))"

definition fmul :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> representation"
  where "fmul x m a b =
    (if is_nan x a \<or> is_nan x b \<or> (is_zero x a \<and> is_infinity x b) \<or> (is_infinity x a \<and> is_zero x b)
     then some_nan x
     else if is_infinity x a \<or> is_infinity x b
     then (if sign a = sign b then plus_infinity x else minus_infinity x)
     else zerosign x (if sign a = sign b then 0 else 1 ) (round x m (valof x a * valof x b)))"

definition fdiv :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> representation"
  where "fdiv x m a b =
    (if is_nan x a \<or> is_nan x b \<or> (is_zero x a \<and> is_zero x b) \<or> (is_infinity x a \<and> is_infinity x b)
     then some_nan x
     else if is_infinity x a \<or> is_zero x b
     then (if sign a = sign b then plus_infinity x else minus_infinity x)
     else if is_infinity x b
     then (if sign a = sign b then plus_zero x else minus_zero x)
     else zerosign x (if sign a = sign b then 0 else 1) (round x m (valof x a / valof x b)))"

definition fsqrt :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation"
  where "fsqrt x m a =
    (if is_nan x a then some_nan x
     else if is_zero x a \<or> is_infinity x a \<and> sign a = 0 then a
     else if sign a = 1 then some_nan x
     else zerosign x (sign a) (round x m (sqrt (valof x a))))"

text \<open>Negation.\<close>
definition fneg :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation"
  where "fneg x m a = (1 - sign a, exponent a, fraction a)"


subsection \<open>Comparison operations\<close>

datatype ccode = Gt | Lt | Eq | Und

definition fcompare :: "format \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> ccode"
  where "fcompare x a b =
    (if is_nan x a \<or> is_nan x b then Und
     else if is_infinity x a \<and> sign a = 1
     then (if is_infinity x b \<and> sign b = 1 then Eq else Lt)
     else if is_infinity x a \<and> sign a = 0
     then (if is_infinity x b \<and> sign b = 0 then Eq else Gt)
     else if is_infinity x b \<and> sign b = 1 then Gt
     else if is_infinity x b \<and> sign b = 0 then Lt
     else if valof x a < valof x b then Lt
     else if valof x a = valof x b then Eq
     else Gt)"

definition flt :: "format \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> bool"
  where [simp]: "flt x a b \<longleftrightarrow> fcompare x a b = Lt"

definition fle :: "format \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> bool"
  where [simp]: "fle x a b \<longleftrightarrow> fcompare x a b = Lt \<or> fcompare x a b = Eq"

definition fgt :: "format \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> bool"
  where [simp]: "fgt x a b \<longleftrightarrow> fcompare x a b = Gt"

definition fge :: "format \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> bool"
  where [simp]: "fge x a b \<longleftrightarrow> fcompare x a b = Gt \<or> fcompare x a b = Eq"

definition feq :: "format \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> bool"
  where [simp]: "feq x a b \<longleftrightarrow> fcompare x a b = Eq"


section \<open>Specify float to be double  precision and round to even\<close>

definition float_format :: format
  where "float_format = (11, 52)"

text \<open>The float type.\<close>
typedef float = "{a. is_valid float_format a}"
proof
  show "(0, 0, 0) \<in> ?float" by (simp add: is_valid_def)
qed

definition Val :: "float \<Rightarrow> real"
  where "Val a = valof (float_format) (Rep_float a)"

definition Float :: "real \<Rightarrow> float"
  where "Float x = Abs_float (round float_format To_nearest x)"

definition Sign :: "float \<Rightarrow> nat"
  where "Sign a = sign (Rep_float a)"

definition Exponent :: "float \<Rightarrow> nat"
  where "Exponent a = exponent (Rep_float a)"

definition Fraction :: "float \<Rightarrow> nat"
  where "Fraction a = fraction (Rep_float a)"

definition Ulp :: "float \<Rightarrow> real"
  where "Ulp a = ulp float_format (Rep_float a)"

text \<open>Lifting of the discriminator functions.\<close>
definition Isnan :: "float \<Rightarrow> bool"
  where "Isnan a = is_nan float_format (Rep_float a)"

definition Infinity :: "float \<Rightarrow> bool"
  where "Infinity a \<longleftrightarrow> is_infinity float_format (Rep_float a)"

definition Isnormal :: "float \<Rightarrow> bool"
  where "Isnormal a \<longleftrightarrow> is_normal float_format (Rep_float a)"

definition Isdenormal :: "float \<Rightarrow> bool"
  where "Isdenormal a \<longleftrightarrow> is_denormal float_format (Rep_float a)"

definition Iszero :: "float \<Rightarrow> bool"
  where "Iszero a \<longleftrightarrow> is_zero float_format (Rep_float a)"

definition Finite :: "float \<Rightarrow> bool"
  where "Finite a \<longleftrightarrow> Isnormal a \<or> Isdenormal a \<or> Iszero a"

definition Isintegral :: "float \<Rightarrow> bool"
  where "Isintegral a \<longleftrightarrow> is_integral float_format (Rep_float a)"


text \<open>Basic operations on floats.\<close>

definition Topfloat :: "float"
  where "Topfloat = Abs_float (topfloat float_format)"

definition Bottomfloat :: "float"
  where "Bottomfloat = Abs_float (bottomfloat float_format)"

definition Plus_zero :: "float"
  where "Plus_zero = Abs_float (plus_zero float_format)"

definition Minus_zero :: "float"
  where "Minus_zero = Abs_float (minus_zero float_format)"

definition Minus_infinity :: "float"
  where "Minus_infinity = Abs_float (minus_infinity float_format)"

definition Plus_infinity :: "float"
  where "Plus_infinity = Abs_float (plus_infinity float_format)"

instantiation float :: plus
begin

definition plus_float :: "float \<Rightarrow> float \<Rightarrow> float"
  where "a + b = Abs_float (fadd float_format To_nearest (Rep_float a) (Rep_float b))"

instance ..

end

instantiation float :: minus
begin

definition minus_float :: "float \<Rightarrow> float \<Rightarrow> float"
  where "a - b = Abs_float (fsub float_format To_nearest (Rep_float a) (Rep_float b))"

instance ..

end

instantiation float :: times
begin

definition times_float :: "float \<Rightarrow> float \<Rightarrow> float"
  where "a * b = Abs_float (fmul float_format To_nearest (Rep_float a) (Rep_float b))"

instance ..

end

instantiation float :: inverse
begin

definition divide_float :: "float \<Rightarrow> float \<Rightarrow> float"
  where "a div b = Abs_float (fdiv float_format To_nearest (Rep_float a) (Rep_float b))"

definition inverse_float :: "float \<Rightarrow> float"
  where "inverse_float a = Float (1 / Val a)"

instance ..

end

definition float_rem :: "float \<Rightarrow> float \<Rightarrow> float"
  where "float_rem a b = Abs_float (frem float_format To_nearest (Rep_float a) (Rep_float b))"

definition float_sqrt :: "float \<Rightarrow> float"
  where "float_sqrt a = Abs_float (fsqrt float_format To_nearest (Rep_float a))"

definition ROUNDFLOAT :: "float \<Rightarrow> float"
  where "ROUNDFLOAT a = Abs_float (fintrnd float_format To_nearest (Rep_float a))"


instantiation float :: ord
begin

definition less_float :: "float \<Rightarrow> float \<Rightarrow> bool"
  where "a < b \<longleftrightarrow> flt float_format (Rep_float a) (Rep_float b)"

definition less_eq_float :: "float \<Rightarrow> float \<Rightarrow> bool"
  where "a \<le> b \<longleftrightarrow> fle float_format (Rep_float a) (Rep_float b)"

instance ..

end


definition float_gt :: "float \<Rightarrow> float \<Rightarrow> bool"
  where "float_gt a b = fgt float_format (Rep_float a) (Rep_float b)"

definition float_ge :: "float \<Rightarrow> float \<Rightarrow> bool"
  where "float_ge a b = fge float_format (Rep_float a) (Rep_float b)"

definition float_eq :: "float \<Rightarrow> float \<Rightarrow> bool"  (infixl "\<doteq>" 70)
  where "float_eq a b = feq float_format (Rep_float a) (Rep_float b)"

definition float_neg :: "float \<Rightarrow> float"
  where "float_neg a = Abs_float (fneg float_format To_nearest (Rep_float a))"

definition float_abs :: "float \<Rightarrow> float"
  where "float_abs a = (if sign (Rep_float a) = 0 then a else float_neg a)"

text \<open>The \<open>1 + \<epsilon>\<close> property.\<close>
definition normalizes :: "real \<Rightarrow> bool"
  where "normalizes x =
    (1/ (2::real)^(bias float_format - 1) \<le> \<bar>x\<bar> \<and> \<bar>x\<bar> < threshold float_format)"

end
