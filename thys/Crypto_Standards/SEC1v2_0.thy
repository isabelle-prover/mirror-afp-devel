theory SEC1v2_0
  imports "Words"
          "EC_Common"

begin

text \<open> https://www.secg.org/sec1-v2.pdf

SEC 1 v2.0 is the current standard from the Standards for Efficient Cryptography Group (SECG)
for elliptic curve cryptography (ECC).  The text of the standard is available at the above link.

In this theory, we translate the functions defined in SEC 1 v2.0 to HOL.  We adhere as closely to
the written standard as possible, including function and variable names.  It should be clear to
anyone, regardless of their experience with HOL, that this translation exactly matches the 
standard.  Variances from the written standard are (over-)explained in comments.

Note: We only consider curves of the form \<open>y\<^sup>2 \<equiv> x\<^sup>3 + ax + b (mod p)\<close> over a finite prime field
\<open>F\<^sub>p\<close>, 2 < p, where \<open>4a\<^sup>3 + 27b\<^sup>2 \<noteq> 0 (mod p)\<close>.  The standard also considers curves over finite 
fields of characteristic 2. 

The residues_prime_gt2 locale fixes a prime p, where 2 < p, and the corresponding residue ring
labeled R. That is, \<open>R = \<int>\<^sub>p\<close>, the integers modulo p.  Note that SEC 1 sometimes uses the letter
R to represent points on an elliptic curve.  Because R is used for the residue ring here, we
will need to choose another letter when SEC 1 uses R.  Otherwise we strive to keep the same
variable names as the standard.\<close>

context residues_prime_gt2
begin

section \<open>2. Mathematical Foundations\<close>

text \<open>The majority of this chapter of the standard is, as the title suggests, background 
information about finite fields and elliptic curves.  HOL/Isabelle has well-built theories
of finite fields and elliptic curves.  We don't need to translate any of that now.  We use what
HOL already has.  There are a few things in Section 2.3 Data Types and Conversions which need
translation.  See below.\<close>

subsection \<open>2.1-2.2 Finite Fields and Elliptic Curves\<close>

text \<open>The language used in the HOL formalization of finite fields might be opaque to 
non-mathematicians.  We use this section only to point out things to the reader who might
appreciate some reminders on the language used for finite fields and elliptic curves.

First we state a few simple things about the prime p that will be useful in some proof below.
For example, that p is odd and that the number of octets (8-bit bytes) needed to represent p is
greater than 0.  The third lemma here is useful when thinking about the functions that convert
between points in the elliptic curve and a string of octets.\<close>

lemma p_mod2: "p mod 2 = 1"
  using gt2 p_prime prime_odd_nat by presburger 

lemma octet_len_p: "0 < octet_length p"
  by (metis gt2 nat_to_words_nil_iff_zero2 neq0_conv not_less_iff_gr_or_eq zero_less_numeral)

lemma octet_len_p':
  assumes "l = octet_length p"
  shows   "1 \<noteq> l + 1 \<and> 1 \<noteq> 2*l + 1 \<and> l + 1 \<noteq> 2*l + 1"
  using assms octet_len_p by linarith


text \<open>The term "carrier" might be unknown to the non-math reader.  For the finite field with p 
elements, where p is prime, the carrier is integers mod p, or simply the interval [0, p-1].\<close>
lemma inCarrier: "(a \<in> carrier R) = (0 \<le> a \<and> a < p)"
  by (metis int_ops(1) mod_pos_pos_trivial not_one_less_zero of_int_closed of_nat_le_0_iff 
            pos_mod_conj r_one res_mult_eq res_of_integer_eq residues_axioms residues_def 
            verit_comp_simplify1(3))

text \<open>The carrier R is a ring of integers.  But also, it's only the integers in [0,p-1].
Isabelle/HOL is a typed language, so we might need to convert an integer (int) in the carrier to a
natural number (nat).  This is not a problem, since all elements of the carrier are non-negative.
So we can convert to a nat and back to an int and we are back to where we started.\<close>
lemma inCarrierNatInt: 
  assumes "a \<in> carrier R"
  shows   "int (nat a) = a"
  by (metis assms local.minus_minus m_gt_one nat_eq_iff2 nat_int of_nat_1 of_nat_less_iff 
            pos_mod_conj res_neg_eq zless_nat_conj)

text \<open>The term nonsingular is defined in Elliptic_Locale.thy and is done for a generic type
of curve.  Then Elliptic_Test.thy builds on Elliptic_Locale.thy builds on that theory
but specifically for curves over the integers.  So just to make it more clear for the case
of integers, the definition of nonsingular here is exactly the familiar notion for elliptic
curves as found in SEC 1, page 16.\<close>
lemma nonsingularEq:
  assumes "nonsingular a b"
  shows   "(4*a^3 + 27*b^2) mod p \<noteq> 0" 
  by (metis nonsingular_def add_cong assms mult_cong res_of_integer_eq res_pow_eq zero_cong)

lemma nonsingularEq_nat:
  fixes a b :: nat
  assumes "nonsingular (int a) (int b)"
  shows   "(4*a^3 + 27*b^2) mod p \<noteq> 0"
proof - 
  have "(4*(int a)^3 + 27*(int b)^2) mod p \<noteq> 0" using assms nonsingularEq by meson
  then show ?thesis
    by (metis (mono_tags, opaque_lifting) cring_class.of_nat_add cring_class.of_nat_mult of_nat_mod
              of_nat_numeral of_nat_power semiring_1_class.of_nat_0)
qed

text \<open>As we did for "nonsingular", we see that the definition "on_curve" is exactly the 
usual definition for curves over the integers, for example on page 6 of SEC 1.\<close>
lemma onCurveEq:
  assumes "on_curve a b P"  "P = Point x y"
  shows   "y^2 mod p = (x^3 + a*x + b) mod p"
proof - 
  have "y [^] (2::nat) = x [^] (3::nat) \<oplus> a \<otimes> x \<oplus> b" using assms(1,2) on_curve_def by simp
  then show ?thesis
    by (metis add.commute mod_add_right_eq res_add_eq res_mult_eq res_pow_eq) 
qed

lemma onCurveEq2: 
  assumes "on_curve a b (Point x y)" 
  shows   "(x \<in> carrier R) \<and> (y \<in> carrier R) \<and> (y^2 mod p = (x^3 + a*x + b) mod p)"
proof - 
  have 1: "y^2 mod p = (x^3 + a*x + b) mod p" using assms onCurveEq by blast
  have 2: "x \<in> carrier R \<and> y \<in> carrier R"     using assms on_curve_def by auto
  show ?thesis                                using 1 2 on_curve_def by fast
qed

lemma onCurveEq3: 
  assumes "(x \<in> carrier R) \<and> (y \<in> carrier R) \<and> (y^2 mod p = (x^3 + a*x + b) mod p)" 
  shows   "on_curve a b (Point x y)"
  by (smt (z3) assms on_curve_def mod_add_right_eq point.case(2) res_add_eq res_mult_eq res_pow_eq)

lemma onCurveEq4: 
  "on_curve a b (Point x y) = 
    ((x \<in> carrier R) \<and> (y \<in> carrier R) \<and> (y^2 mod p = (x^3 + a*x + b) mod p))" 
  using onCurveEq2 onCurveEq3 by blast


text \<open>The number of points on an elliptic curve over a finite field is finite.\<close>
lemma CurveFinite: "finite {P. on_curve a b P}" 
proof - 
  let ?S = "{P. on_curve a b P}"
  have 1: "Infinity \<in> ?S"           using on_curve_def by force
  let ?S' = "{P. P \<noteq> Infinity \<and> on_curve a b P}"
  have 2: "?S = {Infinity} \<union> ?S'"   using 1 by fast
  have 3: "?S' = {P. \<exists>x y. (P = Point x y) \<and> (x \<in> carrier R) \<and> (y \<in> carrier R) \<and> 
                           (y^2 mod p = (x^3 + a*x + b) mod p)}"
    by (metis (no_types, lifting) onCurveEq2 onCurveEq3 point.distinct(2) point.exhaust) 
  have 4: "?S' \<subseteq> {P. \<exists>x y. (P = Point x y) \<and> (x \<in> carrier R) \<and> (y \<in> carrier R)}"
    using 3 by auto
  have 5: "finite {P. \<exists>x y. (P = Point x y) \<and> (x \<in> carrier R) \<and> (y \<in> carrier R)}"
    by (simp add: finite_image_set2)
  have 6: "finite ?S'"    using 4 5 finite_subset by blast
  show ?thesis            using 2 6 by force
qed

text \<open>The points on a non-singular elliptic curve form a group.  So if the number of points is 
a prime n, every point on the curve has order n.\<close>
lemma CurveOrderPrime:
  assumes "a \<in> carrier R"  "b \<in> carrier R"  "nonsingular a b" 
          "C = {P. on_curve a b P}"  "prime n"  "card C = n" "Q \<in> C"
  shows   "point_mult a n Q = Infinity" 
proof - 
  have 1: "ell_prime_field p (nat a) (nat b)" 
    using assms(1,2,3) ell_prime_field_def R_def ell_prime_field_axioms_def inCarrierNatInt 
          nonsingularEq_nat residues_prime_gt2_axioms by algebra
  interpret EPF: ell_prime_field p R "(nat a)" "(nat b)" 
    using 1 apply blast using R_def by presburger
  have 2: "C = carrier EPF.curve" using assms(1,2,4) EPF.curve_def inCarrierNatInt by simp
  have 3: "Q [^]\<^bsub>EPF.curve\<^esub>n = \<one>\<^bsub>EPF.curve\<^esub>" 
    using 2 assms(5,6,7) EPF.curve.power_order_eq_one EPF.finite_curve by presburger
  show ?thesis 
  by (metis 2 3 EPF.in_carrier_curve EPF.multEqPowInCurve EPF.one_curve assms(1,7) inCarrierNatInt)
qed

text \<open>"opp" is defined in Elliptic_Locale.  This is the "opposite" of a point on the curve,
meaning you just negate the y coordinate (modulo p).\<close>
lemma oppEq: "opp (Point x y) = Point x ((-y) mod p)" 
  using opp_Point res_neg_eq by presburger

lemma oppEq':
  fixes   x y :: int 
  assumes "0 < y"  "y < p"
  shows   "opp (Point x y) = Point x (p-y)" 
proof - 
  let ?y = "(-y) mod p"
  have "?y = p - y" using assms(1,2) zmod_zminus1_eq_if by auto 
  then show ?thesis using oppEq by presburger
qed


subsection \<open>2.3 Data Types and Conversions\<close>

text \<open>We have translated routines for converting natural numbers from/to words of a given 
number of bits for many crypto standards.  This can be found in Words.thy.  We have abbreviations
for converting natural numbers to/from octet string, and to/from bit strings.  For ease of 
reference, we will discuss in comments the existing conversion methods for each mentioned in 
section 2.3 of SEC 1.  

New in this standard is converting between elliptic curve points and octet strings.  We define
those primitives below.\<close>

subsubsection \<open>2.3.1 Bit-String-to-Octet-String Conversion\<close>

text\<open>"Bit strings should be converted to octet strings as described in this section. Informally 
the idea is to pad the bit string with 0's on the left to make its length a multiple of 8, then 
chop the result up into octets."

This conversion in Words.thy is named bits_to_octets_len.  Note that there is another routine
called bits_to_octets.  This second routine will convert to octets but will "wash away" any
"extra" 0 bits on the left so that the leftmost byte of the output is not zero.  Whereas, the
output of bits_to_octets_len will always be \<lceil>l/8\<rceil>, where l is the length of the input bit string,
given that the input bit string is valid.  A bit string is valid when each value in the list is
either 0 or 1.  Note bit strings are represented as lists, as are octet strings, so
            bits_to_octets_len [0,0,0,0,0,0,0,0,0,0,0,1,0,0,1] = [0,9]
            bits_to_octets     [0,0,0,0,0,0,0,0,0,0,0,1,0,0,1] = [9]

Bottom line: when this standard calls for conversion from a bit string to an octet string,
we use bits_to_octets_len.
\<close>

subsubsection \<open>2.3.2 Octet-String-to-Bit-String Conversion\<close>

text \<open>Similar to above, to convert from a valid octet string to a bit string, we use
octets_to_bits_len in Words.thy.  Again, there is a second routine called octets_to_bits that will
"wash away" any high 0s.  So
            octets_to_bits_len [0,9] = [0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1]
            octets_to_bits     [0,9] = [1,0,0,1]
The output of octets_to_bits_len will always be 8x as long as the input, when the input is a valid
string of octets.  Octets are valid when each octet is in the list is a value in [0, 255].  The 
output of octets_to_bits will always start with 1.

Bottom line: when the standard calls for conversion from an octet string to a bit string, we 
use octets_to_bits_len.
\<close>

subsubsection \<open>2.3.3 Elliptic-Curve-Point-to-Octet-String Conversion\<close>

text \<open>We have not dealt with storing elliptic curve points as octet strings in other standards.
Thus this is a new data conversion primitive.  

Note that the standard writes ceiling(log2 p / 8).  This is the same as the octet_length when
p is an odd prime.  (See Words/octetLenLog2Prime.)  So we write octet_length instead.

Also the standard says: Assign the value 0x02 to the single octet Y if (y mod 2) = 0, or the 
value 0x03 if (y mod 2) = 1.  Here we write that as Y = [2 + (y mod 2)].  Remember that 
octets are modeled in Isabelle as a list of natural numbers.  So Y will be [2] if y is even
and will be [3] when y is odd.  We hope that this is clear to the reader that it exactly matches
the standard as written.\<close>

definition point_to_octets_nocomp :: "nat \<Rightarrow> nat \<Rightarrow> octets" where
  "point_to_octets_nocomp x y = 
  ( let l = octet_length p;
        X = nat_to_octets_len x l;
        Y = nat_to_octets_len y l
    in
        4 # X @ Y
  )" 

definition point_to_octets_comp :: "nat \<Rightarrow> nat \<Rightarrow> octets" where
  "point_to_octets_comp x y =
  (let l = octet_length p;
       X = nat_to_octets_len x l;
       Y = [2 + (y mod 2)]
   in 
       Y @ X
  )" 

definition point_to_octets :: "int point \<Rightarrow> bool \<Rightarrow> octets" where
  "point_to_octets P Compress = 
  ( case P of
    Infinity  \<Rightarrow> [0]
  | Point x y \<Rightarrow> 
    ( if Compress then (point_to_octets_comp   (nat x) (nat y))
                  else (point_to_octets_nocomp (nat x) (nat y))
    )
  )" 

text \<open>Now a few lemmas about converting a point to octets.  The first set of lemmas shows that 
we know the length of the output when the input is a point on the curve.  For points not on the
curve, we have a bound on the length of the resulting octets.\<close>

lemma point_to_octets_len_Inf: "length (point_to_octets Infinity C) = 1"
  using point_to_octets_def by simp

lemma point_to_octets_nocomp_len_bnd: 
  assumes "l = octet_length p" 
  shows   "2*l + 1 \<le> length (point_to_octets_nocomp x y)"  
proof - 
  let ?X = "nat_to_octets_len x l" 
  have 1: "l \<le> length ?X"  using assms(1) nat_to_words_len_len by auto 
  let ?Y = "nat_to_octets_len y l" 
  have 2: "l \<le> length ?Y"  using assms(1) nat_to_words_len_len by auto 
  have 3: "point_to_octets_nocomp x y = 4 # ?X @ ?Y" 
                           using point_to_octets_nocomp_def assms(1) by meson
  then show ?thesis        using 1 2 by simp
qed

lemma point_to_octets_nocomp_len:
  assumes "x < p"  "y < p"  "l = octet_length p" 
  shows   "length (point_to_octets_nocomp x y) = 2*l + 1"  
proof - 
  let ?X = "nat_to_octets_len x l" 
  have 1: "length ?X = l"  using assms(1,3) nat_to_word_len_mono' zero_less_numeral by blast 
  let ?Y = "nat_to_octets_len y l" 
  have 2: "length ?Y = l"  using assms(2,3) nat_to_word_len_mono' zero_less_numeral by blast 
  have 3: "point_to_octets_nocomp x y = 4 # ?X @ ?Y" 
                           using point_to_octets_nocomp_def assms(3) by meson
  show ?thesis             using 1 2 3 by auto
qed

lemma point_to_octets_len_F_bnd:
  assumes "P = Point x y"  "l = octet_length p" 
  shows   "2*l + 1 \<le> length (point_to_octets P False)"  
  using assms point_to_octets_nocomp_len_bnd point_to_octets_def by auto

lemma point_to_octets_len_F':
  assumes "P = Point (x::int) (y::int)"  "x < p"  "y < p"  "l = octet_length p" 
  shows   "length (point_to_octets P False) = 2*l + 1"  
proof - 
  have x2: "(nat x) < p"    using assms(2) m_gt_one by linarith 
  have y2: "(nat y) < p"    using assms(3) m_gt_one by linarith 
  have "length (point_to_octets P False) = length (point_to_octets_nocomp (nat x) (nat y))" 
                            using assms(1) point_to_octets_def by simp
  then show ?thesis         using assms(4) point_to_octets_nocomp_len x2 y2 by presburger 
qed

lemma point_to_octets_len_F:
  assumes "on_curve a b P"  "l = octet_length p"  "P \<noteq> Infinity" 
  shows   "length (point_to_octets P False) = 2*l + 1"
proof - 
  obtain x and y where 1: "P = Point x y"   using assms(3) by (meson point.exhaust)
  have x1: "x < p" using 1 assms(1) on_curve_def inCarrier by auto
  have y1: "y < p" using 1 assms(1) on_curve_def inCarrier by auto
  show ?thesis     using 1 x1 y1 assms(2) point_to_octets_len_F' by blast
qed

lemma point_to_octets_comp_len_bnd: 
  assumes "l = octet_length p" 
  shows   "l + 1 \<le> length (point_to_octets_comp x y)"  
proof - 
  let ?X = "nat_to_octets_len x l" 
  have 1: "l \<le> length ?X"  using assms(1) nat_to_words_len_len by auto 
  let ?Y = "[2 + (y mod 2)]"
  have 2: "length ?Y = 1"  by simp 
  have 3: "point_to_octets_comp x y = ?Y @ ?X" 
                           using point_to_octets_comp_def assms(1) by meson
  then show ?thesis        using 1 2 by simp
qed

lemma point_to_octets_comp_len:
  assumes "x < p"  "l = octet_length p" 
  shows   "length (point_to_octets_comp x y) = l + 1"  
proof - 
  let ?X = "nat_to_octets_len x l" 
  have 1: "length ?X = l"  using assms(1,2) nat_to_word_len_mono' zero_less_numeral by blast 
  then show ?thesis 
    by (metis 1 assms(2) point_to_octets_comp_def One_nat_def length_append list.size(3,4) 
              Suc_eq_plus1 plus_1_eq_Suc) 
qed

lemma point_to_octets_len_T_bnd:
  assumes "P = Point x y"  "l = octet_length p" 
  shows   "l + 1 \<le> length (point_to_octets P True)"  
  using assms point_to_octets_comp_len_bnd point_to_octets_def by auto

lemma point_to_octets_len_T':
  assumes "P = Point (x::int) (y::int)"  "x < p"  "l = octet_length p" 
  shows   "length (point_to_octets P True) = l + 1"
proof -
  have 1: "(nat x) < p" using assms(2) m_gt_one by linarith 
  have    "length (point_to_octets P True) = length (point_to_octets_comp (nat x) (nat y))" 
                        using assms(1) point_to_octets_def by simp
  then show ?thesis     using assms(3) point_to_octets_comp_len 1 by presburger 
qed

lemma point_to_octets_len_T:
  assumes "on_curve a b P"  "l = octet_length p"  "P \<noteq> Infinity" 
  shows   "length (point_to_octets P True) = l + 1"
proof - 
  obtain x and y where 1: "P = Point x y" using assms(3) by (meson point.exhaust)
  have x1: "x < p" using 1    assms(1) on_curve_def inCarrier by auto
  show ?thesis     using 1 x1 assms(2) point_to_octets_len_T' by blast
qed

lemma point_to_octets_len1:
  assumes "length (point_to_octets P C) = 1"  
  shows   "P = Infinity"
  apply (cases P)
  apply simp
  by (metis (full_types) add_diff_cancel_right' assms diff_is_0_eq' mult_is_0 neq0_conv octet_len_p
            point_to_octets_len_F_bnd point_to_octets_len_T_bnd zero_neq_numeral)

lemma point_to_octets_len_oncurve:
  assumes "on_curve a b P" "l = octet_length p" "L = length (point_to_octets P C)"
  shows   "L = 1 \<or> L = l+1 \<or> L = 2*l+1" 
  apply (cases P)
  using point_to_octets_len_Inf assms(3)   apply presburger
  apply (cases C)
  using point_to_octets_len_T assms(1,2,3) apply simp
  using point_to_octets_len_F assms(1,2,3)    by simp


text \<open>Next set of lemmas:  We know the output of point_to_octets is always a valid string of 
octets, no matter what is input.  Recall that an octet is valid if its value is < 256 = 2^8.\<close>

lemma point_to_octets_comp_valid: "octets_valid (point_to_octets_comp x y)"
proof - 
  have "2 + (y mod 2) < 256" by linarith
  then show ?thesis 
    using point_to_octets_comp_def nat_to_words_len_valid words_valid_cons words_valid_concat 
    by force
qed

lemma point_to_octets_nocomp_valid: "octets_valid (point_to_octets_nocomp x y)"
proof - 
  have "(4::nat) < 256" by fastforce
  then show ?thesis
    by (metis point_to_octets_nocomp_def nat_to_words_len_valid words_valid_cons 
              words_valid_concat Twoto8)
qed

lemma point_to_octets_valid: "octets_valid (point_to_octets P C)"
  apply (cases P)
  apply (simp add: point_to_octets_def words_valid_cons words_valid_nil)
  apply (cases C)
  apply (simp add: point_to_octets_comp_valid   point_to_octets_def) 
  by    (simp add: point_to_octets_nocomp_valid point_to_octets_def) 

text \<open>Next up: converting a point to octets without compression is injective.  A similar
lemma when compression is used is a bit more complicated and is shown below.\<close>

lemma point_to_octets_nocomp_inj:
  assumes "point_to_octets_nocomp x y = point_to_octets_nocomp x' y'" 
          "x < p"  "x' < p"  
  shows   "x = x' \<and> y = y'"
proof - 
  let ?l  = "octet_length p"
  let ?M  = "point_to_octets_nocomp x  y"
  let ?M' = "point_to_octets_nocomp x' y'"
  let ?X  = "nat_to_octets_len x  ?l" 
  let ?X' = "nat_to_octets_len x' ?l" 
  let ?Y  = "nat_to_octets_len y  ?l" 
  let ?Y' = "nat_to_octets_len y' ?l" 
  have l: "length ?X  = ?l \<and> length ?X' = ?l" 
    by (meson assms(2,3) le_trans less_or_eq_imp_le nat_lowbnd_word_len2 nat_to_words_len_upbnd
              not_le zero_less_numeral)
  have m1: "?M  = 4 # ?X  @ ?Y"         using point_to_octets_nocomp_def by meson
  have m2: "?M' = 4 # ?X' @ ?Y'"        using point_to_octets_nocomp_def by meson
  have x1: "?X  = take ?l (drop 1 ?M)"  using m1 l by simp
  have x2: "?X' = take ?l (drop 1 ?M')" using m2 l by simp
  have x3: "?X = ?X'"                   using x1 x2 assms(1) by argo
  have x4: "x = x'"                     using nat_to_words_len_inj x3 by auto
  have y1: "?Y  = drop (1+?l) ?M"       using m1 l by simp
  have y2: "?Y' = drop (1+?l) ?M'"      using m2 l by simp
  have y3: "?Y = ?Y'"                   using y1 y2 assms(1) by argo
  have y4: "y = y'"                     using nat_to_words_len_inj y3 by auto
  show ?thesis                          using x4 y4 by fast
qed

lemma point_to_octets_nocomp_inj':
  assumes "point_to_octets_nocomp x y = point_to_octets_nocomp x' y'" 
          "x < p"  "y < p" 
  shows   "x = x' \<and> y = y'"
proof - 
  let ?l  = "octet_length p"
  let ?M  = "point_to_octets_nocomp x  y"
  let ?M' = "point_to_octets_nocomp x' y'"
  let ?X  = "nat_to_octets_len x  ?l" 
  let ?X' = "nat_to_octets_len x' ?l" 
  let ?Y  = "nat_to_octets_len y  ?l" 
  let ?Y' = "nat_to_octets_len y' ?l" 
  have l1: "length ?X  = ?l \<and> length ?Y = ?l" 
    by (meson assms(2,3) le_trans less_or_eq_imp_le nat_lowbnd_word_len2 nat_to_words_len_upbnd 
              not_le zero_less_numeral)
  have l2: "?l \<le> length ?X' \<and> ?l \<le> length ?Y'" using nat_to_words_len_len by auto 
  have m1: "?M  = 4 # ?X  @ ?Y"                 using point_to_octets_nocomp_def by meson
  have m2: "?M' = 4 # ?X' @ ?Y'"                using point_to_octets_nocomp_def by meson
  have l3: "length ?M  = 1 + length ?X  + length ?Y"          using m1 by force
  have l4: "length ?M' = 1 + length ?X' + length ?Y'"         using m2 by force
  have l5: "length ?X  + length ?Y = length ?X' + length ?Y'" using assms(1) l3 l4 by simp
  have l6: "length ?X'  = ?l \<and> length ?Y' = ?l"               using l5 l2 l1 by simp
  have x1: "?X  = take ?l (drop 1 ?M)"          using m1 l1 by simp
  have x2: "?X' = take ?l (drop 1 ?M')"         using m2 l6 by simp
  have x3: "?X = ?X'"                           using x1 x2 assms(1) by argo
  have x4: "x = x'"                             using nat_to_words_len_inj x3 by auto
  have y1: "?Y  = drop (1+?l) ?M"               using m1 l1 by simp
  have y2: "?Y' = drop (1+?l) ?M'"              using m2 l6 by simp
  have y3: "?Y = ?Y'"                           using y1 y2 assms(1) by argo
  have y4: "y = y'"                             using nat_to_words_len_inj y3 by auto
  show ?thesis                                  using x4 y4 by fast
qed


text \<open>Now a few lemmas about converting the "opposite" of a point to octets using compression.\<close>

definition FlipY :: "nat \<Rightarrow> nat" where
  "FlipY Y = (if Y = 2 then 3 else 2)" 

definition FlipYhd :: "octets \<Rightarrow> octets" where
  "FlipYhd M = (FlipY (hd M)) # (tl M)"

lemma point_to_octets_comp_opp:
  assumes "M = point_to_octets_comp x y"  "M' = point_to_octets_comp x (p-y)"
          "y < p"  "0 < y" 
  shows   "M = FlipYhd M' \<and> M' = FlipYhd M" 
proof -
  let ?l = "octet_length p"
  let ?X = "nat_to_octets_len x ?l"
  let ?Y = "2 + (y mod 2)"
  let ?y = "(p-y)" 
  let ?Y' = "2 + (?y mod 2)" 
  have 1: "M = ?Y # ?X \<and> M' = ?Y' # ?X"         using assms(1,2) point_to_octets_comp_def by force
  have 2: "(y mod 2 = 0) = (?y mod 2 = 1)"
    by (metis p_mod2 assms(3) dvd_imp_mod_0 le_add_diff_inverse less_imp_le_nat odd_add 
              odd_iff_mod_2_eq_one) 
  have 3: "(?Y = 2) = (?Y' = 3)"                using 2 by auto
  have 4: "(?Y = FlipY ?Y') \<and> (?Y' = FlipY ?Y)" using FlipY_def 3 by fastforce
  show ?thesis                                  using FlipYhd_def 4 1 by force
qed

lemma point_to_octets_comp_opp':
  assumes "P = Point x y"  "0 < y"  "y < p" 
          "M = point_to_octets P True"  "M' = point_to_octets (opp P) True"
  shows   "M = FlipYhd M' \<and> M' = FlipYhd M" 
  by (simp add: assms point_to_octets_comp_opp oppEq' point_to_octets_def nat_minus_as_int) 

subsubsection \<open>2.3.4 Octet-String-to-Elliptic-Curve-Point Conversion\<close>

text \<open>This conversion function needs to know the elliptic curve coefficients a and b to
check if the recovered point is really on the curve.  We also check that the high octet is 4.
And we insist that the octet string is valid (meaning every octet is a value < 256) and the 
number of octets must be 2*l+ 1, where l is the length of the modulus p in octets.\<close>
definition octets_to_point_nocomp_validInput :: "int \<Rightarrow> int \<Rightarrow> octets \<Rightarrow> bool" where
"octets_to_point_nocomp_validInput a b M = 
  ( let W  = hd M;
        M' = drop 1 M;
        l  = octet_length p;
        X  = take l M';
        x  = int (octets_to_nat X);
        Y  = drop l M';
        y  = int (octets_to_nat Y);
        P  = Point x y
    in
      (octets_valid M) \<and> (W = 4) \<and> (on_curve a b P) \<and> (length M = 2*l + 1)
  )"

definition octets_to_point_nocomp :: "int \<Rightarrow> int \<Rightarrow> octets \<Rightarrow> int point option" where
  "octets_to_point_nocomp a b M = 
  ( let W  = hd M;
        M' = drop 1 M;
        l  = octet_length p;
        X  = take l M';
        x  = int (octets_to_nat X);
        Y  = drop l M';
        y  = int (octets_to_nat Y);
        P  = Point x y
    in
      if (octets_to_point_nocomp_validInput a b M) then Some P else None
  )" 


text \<open>Recovering a point when compression was used is not as straight forward.  We need to 
find a square root mod p, which, depending on p, is not always simple to do.  If p mod 4 = 3, then
it is easy to write down the square root of a quadratic residue, but the SEC 1 standard does not
require that p meet that restriction.  In this definition, we check if \<alpha> is a quadratic residue
and let HOL return one of its square roots, \<beta>. 

There is an issue that is not discussed in the standard.  In the case when \<alpha> = 0,
there is only one square root < p, namely 0.  If \<alpha> = 0 and y = 1, the standard says to set
y' = p.  This will solve the elliptic curve equation but p is not a field element modulo p.
To handle this, we add a check that is not described in the standard.  If \<alpha> = 0, we insist that
y must be 0 (correspondingly Y must be 2).

Note that we define a variable T below that does not appear in the standard explicitly.  T is 
for "test" and it just tests that the high octet is either 2 or 3.  (See step 2.3 in 
section 2.3.4 in the standard.)\<close>
definition octets_to_point_comp_validInput :: "int \<Rightarrow> int \<Rightarrow> octets \<Rightarrow> bool" where
"octets_to_point_comp_validInput a b M = 
  ( let Y  = hd M;
        T  = (Y = 2) \<or> (Y = 3);
        l  = octet_length p;
        X  = drop 1 M;
        x  = int (octets_to_nat X);
        \<alpha>  = (x^3 + a*x + b) mod p
    in
      (octets_valid M) \<and> (x < p) \<and> T \<and> (\<alpha> = 0 \<longrightarrow> Y = 2) \<and> (QuadRes' p \<alpha>) \<and> (length M = l + 1)
  )" 

definition octets_to_point_comp :: "int \<Rightarrow> int \<Rightarrow> octets \<Rightarrow> int point option" where
  "octets_to_point_comp a b M = 
  ( let Y  = hd M;
        y  = Y - 2;
        X  = drop 1 M;
        x  = int (octets_to_nat X);
        \<alpha>  = (x^3 + a*x + b) mod p;
        \<beta>  = some_root_nat p \<alpha>;
        y' = int (if \<beta> mod 2 = y then \<beta> else (p-\<beta>));
        P  = Point x y'
    in
      if (octets_to_point_comp_validInput a b M) then Some P else None
  )"

definition octets_to_point_validInput :: "int \<Rightarrow> int \<Rightarrow> octets \<Rightarrow> bool" where
  "octets_to_point_validInput a b M \<equiv> (M = [0]) \<or> 
    (octets_to_point_comp_validInput a b M) \<or> (octets_to_point_nocomp_validInput a b M)"

definition octets_to_point :: "int \<Rightarrow> int \<Rightarrow> octets \<Rightarrow> int point option" where
  "octets_to_point a b M = 
  ( let lp = octet_length p;
        lM = length M 
    in
        if  M = [0]      then Some Infinity else (
        if lM =   lp + 1 then octets_to_point_comp   a b M else (
        if lM = 2*lp + 1 then octets_to_point_nocomp a b M
        else None
      )
    )
  )" 

text \<open>octets_to_point produces the point at infinity in only one way.\<close>

lemma octets2PointNoCompNotInf:
  assumes "octets_to_point_nocomp a b M = Some P" 
  shows   "P \<noteq> Infinity"
  by (smt (z3) assms octets_to_point_nocomp_def option.distinct(1) option.inject point.distinct(1))

lemma octets2PointCompNotInf:
  assumes "octets_to_point_comp a b M = Some P" 
  shows   "P \<noteq> Infinity"
  by (smt (z3) assms octets_to_point_comp_def option.distinct(1) option.inject point.distinct(1))

lemma octets2PointInf1: "octets_to_point a b [0] = Some Infinity"
  using octets_to_point_def by presburger

lemma octets2PointInf2:
  assumes "octets_to_point a b M = Some Infinity"
  shows   "M = [0]"
  by (smt (z3) assms octets_to_point_def octets2PointNoCompNotInf octets2PointCompNotInf 
               option.distinct(1)) 

lemma octets2PointInf: "(octets_to_point a b M = Some Infinity) = (M = [0])"
  using octets2PointInf1 octets2PointInf2 by blast

text \<open>octets_to_point produces a point on the curve or None.\<close>

lemma octets2PointNoCompOnCurve:
  assumes "octets_to_point_nocomp a b M = Some P" 
  shows   "on_curve a b P"
  by (smt (z3) assms octets_to_point_nocomp_def octets_to_point_nocomp_validInput_def 
               option.distinct(1) option.inject)

lemma octets2PointCompOnCurve:
  assumes "octets_to_point_comp a b M = Some P"  
  shows   "on_curve a b P"
proof - 
  let ?Y  = "hd M"
  let ?T  = "(?Y = 2) \<or> (?Y = 3)"
  let ?y  = "?Y - 2"
  let ?X  = "drop 1 M"
  let ?x  = "int (octets_to_nat ?X)"
  let ?\<alpha>  = "(?x^3 + a*?x + b) mod p"
  let ?\<beta>  = "some_root_nat p ?\<alpha>"
  let ?y' = "int (if ?\<beta> mod 2 = ?y then ?\<beta> else (p-?\<beta>))"
  have 1: "P = Point ?x ?y'" 
    by (smt (z3) assms(1) octets_to_point_comp_def option.distinct(1) option.inject)
  have 2: "octets_to_point_comp_validInput a b M" 
    by (smt (verit, best) assms(1) octets_to_point_comp_def option.simps(3)) 
  have 3: "QuadRes' p ?\<alpha>"      using 2 octets_to_point_comp_validInput_def by meson
  have a1: "?\<alpha> = 0 \<longrightarrow> ?y = 0" 
    by (metis 2 octets_to_point_comp_validInput_def diff_self_eq_0) 
  have a2: "?\<alpha> \<noteq> 0 \<longrightarrow> 0 < ?\<beta>"
    by (metis (mono_tags, opaque_lifting) 3 QuadRes'HasNatRoot bits_mod_0 mod_mod_trivial 
              bot_nat_0.not_eq_extremum cong_def int_ops(1) power_zero_numeral) 
  have x1: "0 \<le> ?x"            using of_nat_0_le_iff by blast
  have x2: "?x < p"            using 2 octets_to_point_comp_validInput_def by meson
  have x3: "?x \<in> carrier R"    using x1 x2 inCarrier by blast 
  have y1: "0 \<le> ?y'"           using of_nat_0_le_iff by blast
  have y2: "?y' < p"
    by (smt (verit, ccfv_threshold) 3 a1 a2 QuadRes'HasNatRoot dvd_imp_mod_0 even_diff_nat gr0I
            int_ops(6) of_nat_0_less_iff zero_less_diff)
  have y3: "?y' \<in> carrier R"   using y1 y2 inCarrier by blast 
  have y4: "?y'^2 mod p = (?x^3 + a*?x + b) mod p"
    by (smt (z3) 3 QuadRes'HasNatRoot QuadRes'HasTwoNatRoots cong_def mod_mod_trivial of_nat_power)
  show ?thesis                 using 1 y4 x3 y3 onCurveEq3 by presburger
qed

lemma octets2PointOnCurve:
  assumes "octets_to_point a b M = Some P" 
  shows   "on_curve a b P"
  by (smt (verit) assms octets2PointCompOnCurve octets2PointNoCompOnCurve octets_to_point_def 
          on_curve_infinity option.inject option.simps(3))


text \<open>Now we have some lemmas about converting a point to octets then back to a point.  First
when compression is not used.\<close>

lemma  
  assumes "on_curve a b P"  "P = Point x y"  "M = point_to_octets_nocomp (nat x) (nat y)"
  shows   point2OctetsNoComp_validInput: "octets_to_point_nocomp_validInput a b M"
  and     point2Octets2PointNoComp:      "octets_to_point_nocomp a b M = Some P"
proof -
  let ?l = "octet_length p"
  let ?X = "nat_to_octets_len (nat x) ?l"
  let ?Y = "nat_to_octets_len (nat y) ?l"
  have x1: "nat x < p"        using assms(1,2) on_curve_def inCarrier by fastforce
  have x2: "length ?X = ?l"   using nat_to_word_len_mono' x1 zero_less_numeral by blast
  have y1: "nat y < p"        using assms(1,2) on_curve_def inCarrier by fastforce
  have y2: "length ?Y = ?l"   using nat_to_word_len_mono' y1 zero_less_numeral by blast
  have m1: "M = 4 # ?X @ ?Y"  using assms(3) point_to_octets_nocomp_def by meson
  have m2: "octets_valid M"   using assms(3) point_to_octets_nocomp_valid by blast 
  let ?M' = "drop  1 M"
  let ?X' = "take ?l ?M'"
  let ?Y' = "drop ?l ?M'"
  have x3: "?X = ?X'"         using m1 x2 by fastforce
  have y3: "?Y = ?Y'"         using m1 x2 by fastforce
  let ?x = "int (octets_to_nat ?X')"
  let ?y = "int (octets_to_nat ?Y')"
  have x4: "?x = int (nat x)" by (metis x3 nat_to_words_len_to_nat zero_less_numeral) 
  have x5: "?x = x"           using assms(1,2) on_curve_def inCarrierNatInt x4 by auto
  have y4: "?y = int (nat y)" by (metis y3 nat_to_words_len_to_nat zero_less_numeral) 
  have y5: "?y = y"           using assms(1,2) on_curve_def inCarrierNatInt y4 by auto
  show     "octets_to_point_nocomp_validInput a b M"
    using m2 m1 octets_to_point_nocomp_validInput_def assms(1,2) x2 x5 y2 y5 by auto
  then show "octets_to_point_nocomp a b M = Some P"
    using assms(2) octets_to_point_nocomp_def x5 y5 by presburger
qed

text \<open>Continuing lemmas about converting a point to octets then back to a point: Now for
when compression is used.\<close>

lemma 
  assumes "on_curve a b P"  "P = Point x y"  "M = point_to_octets_comp (nat x) (nat y)"
  shows   point2OctetsValidInputComp: "octets_to_point_comp_validInput a b M"
  and     point2Octets2PointComp:     "octets_to_point_comp a b M = Some P"
proof -
  let ?l  = "octet_length p"
  let ?X  = "nat_to_octets_len (nat x) ?l"
  let ?Y  = "[2 + ((nat y) mod 2)]" 
  have m1: "M = ?Y @ ?X"             using assms(3) point_to_octets_comp_def by presburger
  let ?Y' = "hd M" 
  have y1: "?Y' = 2 + (nat y) mod 2" using m1 by fastforce
  let ?T  = "?Y' = 2 \<or> ?Y' = 3"
  have T1: "?T"                      using y1 by force
  let ?X' = "drop 1 M"
  have x1: "?X' = ?X"                using m1 by auto
  let ?x  = "int (octets_to_nat ?X')"
  have x2: "?x = int (nat x)"        by (metis x1 nat_to_words_len_to_nat zero_less_numeral)
  have x3: "?x = x"                  using assms(1,2) on_curve_def inCarrierNatInt x2 by auto
  have x4: "?x < p"                  using x3 assms(1,2) inCarrier on_curve_def by auto 
  let ?\<alpha>  = "((?x^3 + a*?x + b) mod p)" 
  have y2: "y^2 mod p = ?\<alpha>"          using assms(1,2) onCurveEq x3 by presburger 
  have y3: "0 \<le> y \<and> y < p"           using assms(1,2) inCarrier onCurveEq2 by blast 
  have a1: "QuadRes' p ?\<alpha>" 
    by (metis y2 QuadRes'_def QuadResImplQuadRes'2 QuadRes_def cong_def mod_mod_trivial p_prime)   
  have y4: "?\<alpha> = 0 \<longrightarrow> y^2 mod p = 0" using y2 by argo
  have y5: "?\<alpha> = 0 \<longrightarrow> y = 0"         by (meson y4 y3 ZeroSqrtMod p_prime prime_nat_int_transfer) 
  have y6: "?\<alpha> = 0 \<longrightarrow> ?Y' = 2"       using y1 y5 by fastforce
  have l1: "length ?X = ?l"           using nat_to_word_len_mono' x3 x4 by force 
  have l2: "length  M = ?l + 1"       using l1 m1 by auto
  show A1: "octets_to_point_comp_validInput a b M" 
    by (metis assms(3) x4 T1 y6 a1 l2 octets_to_point_comp_validInput_def 
              point_to_octets_comp_valid)
  let ?y  = "?Y' - 2"
  have y7: "?y = (nat y) mod 2"      using y1 by force
  let ?\<beta>  = "some_root_nat p ?\<alpha>"
  have b1: "?\<beta> < p"                  using QuadRes'HasNatRoot a1 by blast 
  let ?y' = "int (if ?\<beta> mod 2 = ?y then ?\<beta> else (p-?\<beta>))"
  let ?P  = "Point ?x ?y'"
  have A2: "octets_to_point_comp a b M = Some ?P"  by (smt (verit) A1 octets_to_point_comp_def) 
  show "octets_to_point_comp a b M = Some P"       proof (cases "?\<alpha> = 0")
    case T0: True
    have T1: "y = 0"   by (metis ZeroSqrtMod y4 y3 p_prime T0 prime_nat_int_transfer) 
    show ?thesis       using A2 T0 T1 ZeroSqrtMod' assms(2) p_prime x3 y7 by force
  next
    case False
    then have "0 < ?\<alpha>" by (smt (verit, best) m_gt_one pos_mod_conj)
    then have "(nat y) = ?\<beta> \<or> (nat y) = p - ?\<beta>"
      by (metis Euclidean_Rings.pos_mod_bound QuadResHasExactlyTwoRoots2 a1 gt2 int_ops(1)
                nat_int not_less of_nat_le_0_iff p_prime y2 y3) 
    then show ?thesis 
      by (smt (verit) A2 assms(2) b1 diff_is_0_eq' even_diff_nat int_nat_eq less_imp_le_nat 
              less_numeral_extra(3) odd_add odd_iff_mod_2_eq_one p_mod2 x3 y7 y3 zero_less_diff)  
  qed
qed

text \<open>Now it's easy to show that for points on the curve, point_to_octets_comp is injective.\<close>
lemma point_to_octets_comp_inj:
  assumes "point_to_octets_comp x y = point_to_octets_comp x' y'" 
          "on_curve a b (Point (int x) (int y))"  "on_curve a b (Point (int x') (int y'))"
  shows   "x = x' \<and> y = y'"
  by (metis assms(1,2,3) nat_int option.inject point.inject point2Octets2PointComp)

lemma point_to_octets_comp_inj':
  assumes "point_to_octets_comp (nat x) (nat y) = point_to_octets_comp (nat x') (nat y')" 
          "on_curve a b (Point x y)"  "on_curve a b (Point x' y')"
  shows   "x = x' \<and> y = y'"
  by (metis assms(1,2,3) option.inject point.inject point2Octets2PointComp)

text \<open>In the Public Key Recovery Operation, you have "forgotten" y.  So you just try to recover
the whole point by guessing that y is even.  So we have a few lemmas here that will be 
useful for that recovery operation.\<close>
lemma point2Octets2PointComp_forgot_Y2:
  assumes "on_curve a b P"  "P = Point x y"  "y mod 2 = 0"
          "l = octet_length p"  "X = nat_to_octets_len (nat x) l"  "M = 2 # X" 
  shows   "octets_to_point_comp a b M = Some P"
proof -
  have "M = point_to_octets_comp (nat x) (nat y)" 
    by (metis assms(3,4,5,6) point_to_octets_comp_def add.right_neutral append_Cons append_Nil
              dvd_imp_mod_0 even_mod_2_iff even_of_nat int_nat_eq odd_add) 
  then show ?thesis using assms(1,2) point2Octets2PointComp by blast 
qed

lemma point2Octets2PointComp_forgot_Y2':
  assumes "on_curve a b P"  "P = Point x y"  "y mod 2 = 1"
          "l = octet_length p"  "X = nat_to_octets_len (nat x) l"  "M = 2 # X" 
  shows   "octets_to_point_comp a b M = Some (opp P)"
proof -
  have 0: "y \<noteq> 0"       using assms(3) by force
  have 1: "0 < y"       using 0 assms(1,2) on_curve_def inCarrier by force 
  have 2: "y < p"       using   assms(1,2) on_curve_def inCarrier by force 
  let ?y = "p - y"
  let ?P = "Point x ?y"
  have 3: "?P = opp P"  using oppEq'[OF 1 2] assms(2) by presburger
  have 4: "(nat ?y) mod 2 = 0"
    by (metis assms(3) cancel_comm_monoid_add_class.diff_cancel even_of_nat int_nat_eq mod_0 
              mod_diff_right_eq not_mod_2_eq_1_eq_0 odd_iff_mod_2_eq_one p_mod2) 
  have 5: "M = point_to_octets_comp (nat x) (nat ?y)" 
                        using 4 assms(4,5,6) point_to_octets_comp_def by fastforce
  show ?thesis          using 3 5 assms(1,2) point2Octets2PointComp opp_closed by auto
qed

lemma point2Octets2PointComp_PoppP:
  assumes "on_curve a b P"  "P = Point x y"  "l = octet_length p"  
          "X = nat_to_octets_len (nat x) l"  "M = 2 # X" 
  shows   "octets_to_point_comp a b M = Some P \<or> octets_to_point_comp a b M = Some (opp P)"
  apply (cases "y mod 2 = 0")
  using assms(1,2,3,4,5) point2Octets2PointComp_forgot_Y2  apply presburger
  using assms(1,2,3,4,5) point2Octets2PointComp_forgot_Y2'    by presburger

lemma point2Octets2PointComp_PoppP':
  assumes "on_curve a b P"  "P = Point x y"  "l = octet_length p"  
          "X = nat_to_octets_len (nat x) l"  "M = 2 # X" 
  shows   "octets_to_point a b M = Some P \<or> octets_to_point a b M = Some (opp P)"
proof - 
  have      "x < p"             using assms(1,2) inCarrier onCurveEq2 by blast 
  then have "nat x < p"         using m_gt_one by linarith 
  then have "length X = l"      using assms(3,4) nat_to_word_len_mono' zero_less_numeral by blast  
  then have "octets_to_point a b M = octets_to_point_comp a b M"
                                by (simp add: octets_to_point_def assms(3,5)) 
  then show ?thesis             using assms point2Octets2PointComp_PoppP by algebra
qed

text \<open>Putting together what we have proved above, if P is on the curve, then converting P to
octets and then back to a point, whether or not compression is used, will get back the 
original P.\<close>
lemma point2Octets2Point:
  assumes "on_curve a b P" "M = point_to_octets P C"
  shows   "octets_to_point a b M = Some P"
proof (cases P)
  case Infinity
  then show ?thesis by (simp add: assms(2) octets_to_point_def point_to_octets_def)
next
  case P: (Point x y)
  then show ?thesis proof (cases C)
    case T0: True
    let ?lp = "octet_length p"
    have T1: "length M = ?lp + 1" using P assms(1,2) T0 point_to_octets_len_T by fastforce 
    have T2: "octets_to_point a b M = octets_to_point_comp a b M" 
      by (smt (verit, best) octet_len_p' T1 octets_to_point_def One_nat_def Suc_eq_plus1 
              list.size(3,4))
    show ?thesis using T2 P T0 assms(1,2) point2Octets2PointComp point_to_octets_def by auto 
  next
    case F0: False
    let ?lp = "octet_length p"
    have l: "0 < ?lp"
      by (metis gr_implies_not_zero gt2 nat_to_words_nil_iff_zero2 neq0_conv zero_less_numeral) 
    have F1: "length M = 2*?lp + 1" using P assms(1,2) F0 point_to_octets_len_F by fastforce 
    have F2: "octets_to_point a b M = octets_to_point_nocomp a b M" 
      by (smt (verit, best) F1 octet_len_p' octets_to_point_def One_nat_def Suc_eq_plus1 
              list.size(3,4)) 
    then show ?thesis using F2 P F0 assms(1,2) point2Octets2PointNoComp point_to_octets_def by simp
  qed
qed

text \<open>Now we think about the other direction.  We start with octets.  If the octets are a valid
input for when compression is or is not used, then if we convert the octets to a point and then
back again, we will get back the original octets.\<close>

lemma octets2PointNoCompValidInIFF1:
  "(octets_to_point_nocomp a b M \<noteq> None) = (octets_to_point_nocomp_validInput a b M)" 
  by (smt (z3) not_None_eq octets_to_point_nocomp_def)

lemma octets2PointNoCompalidInIFF2:
  "(\<exists>P. octets_to_point_nocomp a b M = Some P) = (octets_to_point_nocomp_validInput a b M)"
  using octets2PointNoCompValidInIFF1 by force 

lemma octets2Point2OctetsNoComp:
  assumes "octets_to_point_nocomp a b M = Some P"
  shows   "point_to_octets P False = M"
proof - 
  let ?W  = "hd M"
  let ?M' = "drop 1 M"
  let ?l  = "octet_length p"
  let ?X  = "take ?l ?M'"
  let ?x  = "int (octets_to_nat ?X)"
  let ?Y  = "drop ?l ?M'"
  let ?y  = "int (octets_to_nat ?Y)"
  let ?P  = "Point ?x ?y"
  have V: "octets_to_point_nocomp_validInput a b M"
    using assms octets2PointNoCompValidInIFF1 by blast 
  have P1: "?P = P"              by (smt (z3) assms(1) V octets_to_point_nocomp_def option.inject) 
  have M1: "length M = 2*?l + 1" using V octets_to_point_nocomp_validInput_def by meson
  have M2: "octets_valid M"      using V octets_to_point_nocomp_validInput_def by meson
  have W1: "?W = 4"              using V octets_to_point_nocomp_validInput_def by meson
  have X1: "length ?X = ?l"      using M1 by force
  have X2: "octets_valid ?X"     using M2 words_valid_take words_valid_drop by blast
  have Y1: "length ?Y = ?l"      using M1 by force
  have Y2: "octets_valid ?Y"     using M2 words_valid_drop by blast
  have M3: "M = ?W # ?X @ ?Y"
    by (metis M1 One_nat_def append_take_drop_id drop_0 drop_Suc_Cons hd_Cons_tl leD le_add2 
              list.size(3) zero_less_one) 
  have O1: "point_to_octets P False = point_to_octets_nocomp (nat ?x) (nat ?y)"
                                       using P1 point_to_octets_def by force
  have x1: "nat ?x = octets_to_nat ?X" by (meson nat_int) 
  have y1: "nat ?y = octets_to_nat ?Y" by (meson nat_int) 
  let ?X' = "nat_to_octets_len (nat ?x) ?l"
  have X3: "?X' = ?X"                  by (metis X1 X2 x1 words_to_nat_to_words_len2) 
  let ?Y' = "nat_to_octets_len (nat ?y) ?l"
  have Y3: "?Y' = ?Y"                  by (metis Y1 Y2 y1 words_to_nat_to_words_len2) 
  show ?thesis using M3 O1 X3 Y3 W1 point_to_octets_nocomp_def by algebra
qed

lemma octets2PointCompValidInIFF1:
  "(octets_to_point_comp a b M \<noteq> None) = (octets_to_point_comp_validInput a b M)" 
  by (smt (z3) not_None_eq octets_to_point_comp_def)

lemma octets2PointCompValidInIFF2:
  "(\<exists>P. octets_to_point_comp a b M = Some P) = (octets_to_point_comp_validInput a b M)"
  using octets2PointCompValidInIFF1 by force 

lemma octets2Point2OctetsComp:
  assumes "octets_to_point_comp a b M = Some P"
  shows   "point_to_octets P True = M"
proof - 
  let ?Y  = "hd M"
  let ?T  = "(?Y = 2) \<or> (?Y = 3)"
  let ?y  = "?Y - 2"
  let ?l  = "octet_length p"
  let ?X  = "drop 1 M"
  let ?x  = "int (octets_to_nat ?X)"
  let ?\<alpha>  = "(?x^3 + a*?x + b) mod p"
  let ?\<beta>  = "some_root_nat p ?\<alpha>"
  let ?y' = "int (if ?\<beta> mod 2 = ?y then ?\<beta> else (p-?\<beta>))"
  let ?P  = "Point ?x ?y'"
  have V: "octets_to_point_comp_validInput a b M"
    using assms octets2PointCompValidInIFF1 by blast 
  have P1: "?P = P" 
    by (smt (z3) assms(1) V octets_to_point_comp_def option.inject) 
  let ?X' = "nat_to_octets_len (nat ?x) ?l"
  let ?Y' = "[2 + ((nat ?y') mod 2)]" 
  let ?M  = "?Y' @ ?X'"
  have O1: "point_to_octets P True = ?M" 
    using P1 point_to_octets_def point_to_octets_comp_def by force
  have x1: "?X = ?X'"
    by (metis V add_diff_cancel_right' length_drop nat_int octets_to_point_comp_validInput_def
              words_to_nat_to_words_len2 words_valid_drop)
  have a1: "QuadRes' p ?\<alpha>"     by (meson V octets_to_point_comp_validInput_def) 
  have M1: "length M = ?l + 1" by (meson V octets_to_point_comp_validInput_def)
  have y1: "?y = 0 \<or> ?y = 1"
    by (metis V add_diff_cancel_right' diff_self_eq_0 numeral_2_eq_2 numeral_3_eq_3
              octets_to_point_comp_validInput_def plus_1_eq_Suc) 
  have y3: "(nat ?y') mod 2 = ?y"
    by (smt (verit, ccfv_threshold) QuadRes'HasNatRoot a1 even_add even_diff_nat 
            less_imp_of_nat_less mod2_eq_if nat_int p_mod2 y1)
  have y4: "[?Y] = ?Y'"
    by (metis V add.commute add.left_neutral add_diff_cancel_right' numeral_2_eq_2 numeral_3_eq_3
              octets_to_point_comp_validInput_def plus_1_eq_Suc y3)  
  have M2: "?M = M" 
    by (metis (mono_tags, opaque_lifting) x1 y4 M1 One_nat_def Suc_eq_plus1 append_Cons append_Nil
              drop0 drop_Suc list.exhaust_sel list.size(3) nat.simps(3))
  show ?thesis using O1 M2 by argo
qed

lemma octets2PointValidInIFF1:
  "(octets_to_point a b M \<noteq> None) = (octets_to_point_validInput a b M)"
  by (smt (verit, best) R_def octets2Point2OctetsNoComp octets2PointCompValidInIFF1 
          octets2PointNoCompOnCurve octets_to_point_comp_validInput_def octets_to_point_def 
          octets_to_point_nocomp_def octets_to_point_validInput_def option.simps(3) 
          point2Octets2Point residues_prime_gt2_axioms)

lemma octets2PointValidInIFF2:
  "(\<exists>P. octets_to_point a b M = Some P) = (octets_to_point_validInput a b M)"
  using octets2PointValidInIFF1 by auto

lemma octets2Point2Octets:
  assumes "octets_to_point a b M = Some P"  "lM = length M"  "lp = octet_length p"
          "C = (if lM = lp + 1 then True else False)" 
  shows   "point_to_octets P C = M"
proof - 
  have 1: "(M = [0]) \<or> (lM = lp + 1) \<or> (lM = 2*lp + 1)" 
    by (smt (z3) assms(1,2,3) octets_to_point_def option.simps(3)) 
  have 2: "M = [0] \<longrightarrow> point_to_octets P C = M"
    using assms(1) octets_to_point_def point_to_octets_def by force
  have 3: "lM = lp + 1 \<longrightarrow> point_to_octets P C = M"
    using 2   assms(1,2,3,4) octets_to_point_def octets2Point2OctetsComp   by force
  have 4: "lM = 2*lp + 1 \<longrightarrow> point_to_octets P C = M"
    using 2 3 assms(1,2,3,4) octets_to_point_def octets2Point2OctetsNoComp by force
  show ?thesis using 1 2 3 4 by fast
qed

subsubsection \<open>2.3.5 Field-Element-to-Octet-String Conversion\<close>

text \<open>In this translation of SEC 1, we only consider prime fields.  So a "field element" is 
simply a natural number in the range [0, p-1].  So converting field elements to or from octets
is the same as converting between nats and octets.

The only detail to keep in mind is that the resulting octet string should have the same number
of octets as the prime p.  So if x is a field element (natural number in [0,p-1]), then
we convert x to an octet string M with:
           M = nat_to_octets_len x (octet_length p)
\<close>

subsubsection \<open>2.3.6 Octet-String-to-Field-Element Conversion\<close>

text \<open>Again, we only consider prime fields in this translation.  So a field element is a natural
number in the range [0,p-1].  We can convert any octet string to a nat using octets_to_nat, 
defined in Words.thy.  If the resulting nat is p or greater, it should be rejected.  Note that
you might need to check if the input octets were valid using octets_valid, which checks that 
each octet is a value no greater than 255.\<close>

subsubsection \<open>2.3.7 Integer-to-Octet-String Conversion\<close>

text \<open>Again, there are two conversion primitives for converting a non-negative integer, a.k.a. a
natural number, to an octet string.  nat_to_octets will convert a nat to an octet string so that
the high octet is non-zero.  nat_to_octets_len will produce an octet string that has at least
a minimum number of octets.  In either case, if you translate back to a natural number, you will
get back the original value.  For example:
            nat_to_octets     256   =       [1,0]
            nat_to_octets_len 256 5 = [0,0,0,1,0]
            nat_to_octets_len 256 1 =       [1,0]
and 
            octets_to_nat [1,0]       = 256
            octets_to_nat [0,0,0,1,0] = 256
\<close>

subsubsection \<open>2.3.8 Octet-String-to-Integer Conversion\<close>

text \<open>As described above, the routine to convert an octet string to a natural number is
octets_to_nat.  Of note, octets_valid ensures that a string of octets is valid, meaning each
octet has the value 255 or less.  So octets_valid [0,1,255,3] = True and 
octets_valid [0,1,256,3] = False.\<close>

subsubsection \<open>2.3.9 Field-Element-to-Integer Conversion\<close>

text \<open>Again, we only consider prime fields in this translation of SEC 1.  So a field element is
simply an integer in [0,p-1].  So there is no conversion required.\<close>



section \<open>3. Cryptographic Components\<close>

subsection \<open>3.1 Elliptic Curve Domain Parameters\<close>

text \<open>3.1.1.2.1 Elliptic Curve Domain Parameters over \<open>F\<^sub>p\<close> Validation Primitive

SEC 1 only allows a security level t of 80, 112, 128, 192, or 256.  Then "twice the security
level" will actually be 2*t except for t = 80 and 256, where it's merely close to 2*t.\<close>
definition twiceSecurityLevel :: "nat \<Rightarrow> nat" where
  "twiceSecurityLevel t = 
  ( if (t =  80) then 192 else
  ( if (t = 256) then 521 else 2*t ) )" 


text \<open>The standard writes \<lceil>log 2 p\<rceil>.  Note that because p is odd (thus not a power of 2), 
\<lceil>log 2 p\<rceil> = bit_length p.  See Words.bitLenLog2Prime.  Also, the standard explains that the number
of points on the elliptic curve is n*h.  (h is called the "cofactor".)  It doesn't make a lot of
sense to consider an elliptic curve that has zero points on it.  So we must have 0 < h.  (We
know that 0 < n because the standard insists that n is prime.)  So while not explicitly written
in the standard, we include the requirement that 0 < h.\<close>
definition ECdomainParametersValid :: 
  "nat \<Rightarrow> nat \<Rightarrow> int point \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "ECdomainParametersValid a b G n h t \<equiv>
   ( (t \<in> {80, 112, 128, 192, 256})      \<and> (\<lceil>log 2 p\<rceil> = twiceSecurityLevel t) \<and> 
     (a \<in> carrier R)   \<and> (b \<in> carrier R) \<and> (nonsingular a b) \<and> 
     (n*h \<noteq> p)         \<and> (prime n)       \<and>  card {P. on_curve a b P} = n*h \<and>
     (on_curve a b G)  \<and> (G \<noteq> Infinity)  \<and> (point_mult a n G = Infinity) \<and>
     (h \<le> 2^(t div 8)) \<and> (h = \<lfloor>((sqrt p + 1)^2) div n\<rfloor>) \<and> 0 < h \<and>
     (\<forall>B\<in>{1..99}. (p^B mod n \<noteq> 1))
   )"

text \<open>The security level t is not always explicitly listed in elliptic curve parameters.\<close>
definition ECdomainParametersValid' :: "nat \<Rightarrow> nat \<Rightarrow> int point \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "ECdomainParametersValid' a b G n h \<equiv> (\<exists>t. ECdomainParametersValid a b G n h t)"

lemma ECparamsValidImplies': 
  "ECdomainParametersValid a b G n h t \<Longrightarrow> ECdomainParametersValid' a b G n h"
  using ECdomainParametersValid'_def by blast

definition twiceSecurityLevelInv :: "nat \<Rightarrow> nat" where
  "twiceSecurityLevelInv twoT = 
  ( if (twoT = 192) then  80 else
  ( if (twoT = 521) then 256 else (twoT div 2) ) )" 

lemma twiceSecurityLevelInv: 
  assumes "t \<in> {80, 112, 128, 192, 256}" 
  shows   "twiceSecurityLevelInv (twiceSecurityLevel t) = t"
  using assms twiceSecurityLevelInv_def twiceSecurityLevel_def by fastforce 

text \<open>Even when not explicitly stated, the security level can be recovered from the bit length
of the prime modulus p.\<close>
lemma ECparamsValid'Implies: 
  assumes "ECdomainParametersValid' a b G n h"  "t = twiceSecurityLevelInv (nat \<lceil>log 2 p\<rceil>)"
  shows   "ECdomainParametersValid  a b G n h t"
proof - 
  obtain t' where t1: "ECdomainParametersValid  a b G n h t'"
    using ECdomainParametersValid'_def assms(1) by presburger
  have t2: "t' \<in> {80, 112, 128, 192, 256}"
    using ECdomainParametersValid_def t1 by presburger
  have t3: "\<lceil>log 2 p\<rceil> = twiceSecurityLevel t'" 
    using ECdomainParametersValid_def t1 by presburger 
  have t4: "t' = twiceSecurityLevelInv (nat \<lceil>log 2 p\<rceil>)"
    using nat_int t2 t3 twiceSecurityLevelInv by presburger 
  show ?thesis using assms(2) t1 t4 by argo
qed

lemma ECparamsValid'Implies2: 
  assumes "ECdomainParametersValid' a b G n h"  "t = twiceSecurityLevelInv (bit_length p)"
  shows   "ECdomainParametersValid  a b G n h t"
  by (metis ECparamsValid'Implies assms(1,2) bitLenLog2Prime gt2 nat_int p_prime)

lemma ECparamsValid_min_p:
  assumes "ECdomainParametersValid a b G n h t"
  shows   "2^191 \<le> p"
proof - 
  have 1: "t \<in> {80, 112, 128, 192, 256}" using assms ECdomainParametersValid_def by algebra
  have 2: "bit_length p = twiceSecurityLevel t"
    by (metis assms bitLenLog2Prime gt2 nat_int p_prime ECdomainParametersValid_def) 
  have 3: "192 \<le> twiceSecurityLevel t"   using 1 twiceSecurityLevel_def by fastforce
  have 4: "192 \<le> bit_length p"           using 2 3 by fastforce
  show ?thesis 
    by (meson 4 less_bit_len less_le_trans numeral_less_iff semiring_norm(68,79,81)) 
qed

text \<open>The following lemma is convenient below when showing that valid EC domain parameters
meet the definition of "Elliptic Prime Field" defined in EC_Common.\<close>
lemma paramsValidEllPrimeField:
  assumes "ECdomainParametersValid a b G n h t"
  shows   "a \<in> carrier R \<and> b \<in> carrier R \<and> (4*a^3 + 27*b^2) mod p \<noteq> 0"
  using ECdomainParametersValid_def assms nonsingularEq_nat by presburger

lemma paramsValidEllPrimeField':
  assumes "ECdomainParametersValid a b G n h t"
  shows   "ell_prime_field p a b"
  using assms ell_prime_field.intro ell_prime_field_axioms_def 
        residues_prime_gt2.paramsValidEllPrimeField residues_prime_gt2_axioms by blast


text \<open>The following lemmas are useful for the Public Key Recovery Operation below.\<close>
lemma p_div_n:
  assumes "ECdomainParametersValid a b G n h t"
  shows   "p div n \<le> h"
proof - 
  let ?h = "((sqrt p + 1)^2) / n"
  have h1: "h = nat (floor ?h)" using assms(1) ECdomainParametersValid_def by fastforce
  have h2: "?h < h + 1"         using h1 by linarith
  have f1: "(sqrt p + 1)^2 = p + 1 + 2*(sqrt p)" by (simp add: comm_semiring_1_class.power2_sum)
  have h3: "?h = (p + 2*(sqrt p) + 1) / n"       using f1 by force
  have h4: "?h = (real p / real n) + ((2*(sqrt p) + 1)/n)"
    by (simp add: add_divide_distrib h3) 
  have h5: "(real p / real n) \<le> ?h"              using h4 by auto
  have h6: "(real p / real n) < h + 1"           using h5 h2 by linarith
  have a1: "real (p div n) \<le> (real p / real n)"  using real_of_nat_div4 by blast 
  have a2: "p div n < h + 1"                     using h6 a1 by auto
  show ?thesis                                   using a2 by simp
qed

lemma less_p_div_n:
  assumes "ECdomainParametersValid a b G n h t"  "x < p" 
  shows   "x div n \<le> h"
  by (meson assms p_div_n div_le_mono le_trans less_imp_le_nat) 

lemma less_p_div_n':
  assumes "ECdomainParametersValid a b G n h t"  "(int x) \<in> carrier R" 
  shows   "x div n \<le> h"
  by (meson assms(1,2) inCarrier less_p_div_n of_nat_less_iff) 

text \<open>Next up we show that h < n.  The number of points on the elliptic curve is n*h.  For 
recommended curves, the cofactor h is typically small, like h < 10.  The prime n is very large,
around the size of p.  So in some sense, it's not surprising that h < n.  The only issue here is
to show that given the definition of valid parameters.\<close>
lemma h_less_n:
  assumes "ECdomainParametersValid a b G n h t"
  shows   "h < n" 
proof - 
  let ?t2 = "twiceSecurityLevel t" 
  have t: "t \<in> {80, 112, 128, 192, 256}" using assms ECdomainParametersValid_def by algebra
  have t2: "2*t \<le> ?t2"                   using t twiceSecurityLevel_def by force 
  have h:  "h \<le> 2^(t div 8)"             using assms ECdomainParametersValid_def by algebra
  have h1: "real h \<le> real 2^(t div 8)"   using h by simp
  have h2: "0 < real (h + 1)"            by auto
  have h3: "real (h+1) \<le> real (2^(t div 8) + 1)" using h by fastforce
  have p1: "\<lceil>log 2 p\<rceil> = ?t2"             using assms ECdomainParametersValid_def by algebra
  have p2: "bit_length p = ?t2"          by (metis p1 bitLenLog2Prime gt2 of_nat_eq_iff p_prime) 
  have p3: "2^(?t2-1) \<le> p"              using bit_len_exact3 gt2 p2 by force 
  have p4: "2^(2*t-1) \<le> p" by (meson p3 t2 diff_le_mono le_trans one_le_numeral power_increasing) 
  have n1: "p div n \<le> h"                using assms p_div_n by fast
  have n2: "\<lfloor>(real p / real n)\<rfloor> \<le> h"     by (simp add: n1 floor_divide_of_nat_eq) 
  have n3: "(real p / real n) < h + 1"   using n2 by linarith
  have n4: "prime n"                     using assms ECdomainParametersValid_def by algebra
  have n5: "0 < n"                       by (simp add: n4 prime_gt_0_nat) 
  have n6: "0 < real n"                  using n5 by fastforce
  have n7: "real p < real n * (h+1)"     using n3 n6 by (simp add: mult.commute pos_divide_less_eq)
  have n:  "real p / real (h+1) < real n" using n7 h2 pos_divide_less_eq by blast 
  have a1: "real 2^(2*t-1) / real (h+1) < real n"   
    by (metis n p4 h2 less_le_trans not_less of_nat_power_less_of_nat_cancel_iff pos_divide_less_eq)
  have a2: "real 2^(2*t-1) / real (2^(t div 8)+1) \<le> real 2^(2*t-1) / real (h+1)" 
    using h3 by (simp add: frac_le) 
  have a3: "real 2^(2*t-1) / real (2^(t div 8)+1) < real n"           using a1 a2 by argo
  have a4: "real 2^(t div 8) < real 2^(2*t-1) / real (2^(t div 8)+1)" using t by fastforce
  have     "real h < real n"                                          using a3 a4 h1 by argo
  then show ?thesis by simp
qed

text \<open>It is sometimes helpful to know that n is an odd prime.  In the following proof, we see if
n = 2, then h = 1 and p = 2.  We already know that p cannot be that small, so we are done.  But
also, if n = 2, the n*h = p, which also contradicts the definition of valid elliptic curve
parameters.\<close>
lemma n_not_2: 
  assumes "ECdomainParametersValid a b G n h t"
  shows   "2 < n"
proof - 
  have n0: "prime n"         using assms ECdomainParametersValid_def by algebra
  have h0: "0 < h"           using assms ECdomainParametersValid_def by algebra
  have p0: "2^191 \<le> p"       using assms ECparamsValid_min_p by fast
  have n2: "n = 2 \<longrightarrow> p \<le> 2" proof assume A: "n = 2"
    have A1: "h = 1"                       using A h0 h_less_n assms by fastforce 
    have A2: "1 = \<lfloor>((sqrt p + 1)^2) div 2\<rfloor>" using A A1 assms ECdomainParametersValid_def by simp
    have A3: "((sqrt p + 1)^2) div 2 \<le> 2"  using A2 by linarith
    have A4: "((sqrt p + 1)^2) \<le> 4"        using A3 by simp
    show     "p \<le> 2"                       using A4 real_le_rsqrt by force 
  qed
  have "n \<noteq> 2"     using p0 n2 by fastforce
  then show ?thesis using n0 le_neq_implies_less prime_ge_2_nat by presburger 
qed

lemma n_odd:
  assumes "ECdomainParametersValid a b G n h t"
  shows   "odd n"
  by (metis assms n_not_2 ECdomainParametersValid_def prime_odd_nat) 

text \<open>In fact, n must be a great deal larger than 2.\<close>
lemma ECparamsValid_min_n:
  assumes "ECdomainParametersValid a b G n h t"
  shows   "2^95 < n"
proof -
  have n1: "p div n \<le> h"              using assms p_div_n by fast
  have n2: "\<lfloor>(real p / real n)\<rfloor> \<le> h"   by (simp add: n1 floor_divide_of_nat_eq) 
  have n3: "(real p / real n) < h + 1" using n2 by linarith
  have n4: "prime n"                   using assms ECdomainParametersValid_def by algebra
  have n5: "0 < n"                     by (simp add: n4 prime_gt_0_nat) 
  have n6: "0 < real n"                using n5 by fastforce
  have n7: "real p < real n * (h+1)"   using n3 n6 by (simp add: mult.commute pos_divide_less_eq)
  have n8: "p < n *(h+1)"         by (metis n7 of_nat_less_imp_less semiring_1_class.of_nat_mult)
  have h1: "h+1 \<le> n"              using assms h_less_n by fastforce
  have a1: "p < n^2"              
    by (metis n8 h1 less_le_trans nat_1_add_1 nat_mult_le_cancel_disj power_add power_one_right)
  have a2: "2^191 < n^2"             using a1 assms ECparamsValid_min_p by fastforce
  have a3: "((2::nat)^95)^2 = 2^190" by auto
  have a4: "((2::nat)^95)^2 < n^2"   using a2 a3 by force
  show ?thesis                       using a4 power_less_imp_less_base by blast  
qed

end (*residues_prime_gt2 context*)

text \<open>Now we know what valid elliptic curve parameters are.  So we fix a set of parameters and
define the cryptographic primitives below using those valid parameters.\<close>

locale SEC1 = residues_prime_gt2 +
  fixes a b n h t   :: nat
  and   G           :: "int point"
assumes ECparamsValid: "ECdomainParametersValid a b G n h t"

begin

text \<open>Elliptic_Locale defines elliptic curve operations.  In this locale, we have fixed a set of
elliptic curve parameters.  We use the coefficients a and b to make convenient abbreviations
for definitions found in Elliptic_Locale as well as a data conversion primitive defined above.\<close>
abbreviation on_curve' :: "int point \<Rightarrow> bool" where
  "on_curve' Q \<equiv> on_curve a b Q"

abbreviation point_mult' :: "nat \<Rightarrow> int point \<Rightarrow> int point" where
  "point_mult' x Q \<equiv> point_mult a x Q"

abbreviation add' :: "int point \<Rightarrow> int point \<Rightarrow> int point" where
  "add' P Q \<equiv> add a P Q" 

abbreviation octets_to_point' :: "octets \<Rightarrow> int point option" where
  "octets_to_point' M \<equiv> octets_to_point a b M" 

text \<open>We show that the valid elliptic curve parameters meet the assumptions of the ell_prime_field
locale in EC_Common.  We then write some properties in terms of "curve" which is defined in 
ell_prime_field.  Of note: the definitions in Elliptic_Locale use additive notation for the 
elliptic curve group.  For example, \<open>add' P Q\<close>, or "P + Q".  In contrast, ell_prime_field uses
multiplicative notation, so that the same operation is denoted \<open>P\<otimes>\<^bsub>EPF.curve\<^esub>Q\<close>. \<close>

sublocale EPF: ell_prime_field p R a b
  using ECparamsValid paramsValidEllPrimeField' apply blast
  by (simp add: R_def) 

lemma order_EPF_curve: "order EPF.curve = n*h"
  using order_def ECparamsValid ECdomainParametersValid_def EPF.curve_def
  by (metis partial_object.select_convs(1)) 

lemma order_EPF_curve_h1: 
  assumes "h = 1"
  shows   "order EPF.curve = n"
  using assms order_EPF_curve by simp

lemma order_EPF_curve_h1': 
  assumes "h = 1"
  shows   "prime (order EPF.curve)"
  using assms order_EPF_curve_h1 ECparamsValid ECdomainParametersValid_def by blast

text \<open>When h=1, then all points on the curve can be written as some power of the generator G.  
(And any point on the curve can be picked as the generator, for that matter.  It's just a cyclic
group.)\<close>
lemma EC_h1_cyclic:
  assumes "h = 1" 
  shows   "carrier EPF.curve = {Q. (\<exists>d<n. Q = point_mult' d G)}" 
proof - 
  have H: "on_curve' G \<and> G \<noteq> Infinity \<and> point_mult' n G = Infinity\<and> prime (n::nat)"
    using ECparamsValid ECdomainParametersValid_def by blast 
  let ?S1 = "carrier EPF.curve"
  let ?S2 = "{Q. (\<exists>d<n. Q = point_mult' d G)}"
  have 1: "card ?S1 = n"  by (metis assms(1) order_EPF_curve_h1 order_def) 
  have 2: "card ?S2 = n"  using EPF.curve_cycle_n2[of G n] H by fast
  have 3: "\<forall>d. on_curve' (point_mult' d G)" by (simp add: H point_mult_closed)
  have 4: "?S2 \<subseteq> ?S1"     using 3 EPF.curve_def by force
  show ?thesis            using 1 2 4 EPF.finite_curve card_subset_eq by blast 
qed

lemma EC_h1_cyclic':
  assumes "h = 1"  "on_curve' P" 
  shows   "\<exists>d<n. P = point_mult' d G" 
  using assms EC_h1_cyclic EPF.curve_def by auto

text \<open>Next up, we write down some facts about the generator G, and its multiples P = d*G (or
powers when written with multiplicative notation, P = G^d).\<close>
lemma GonEPFcurve: "G \<in> carrier EPF.curve"
  using ECdomainParametersValid_def ECparamsValid EPF.in_carrier_curve by presburger

lemma dGonEPFcurve:
  assumes "P = point_mult' d G"
  shows   "P \<in> carrier EPF.curve" 
  using GonEPFcurve EPF.multEqPowInCurve EPF.curve.nat_pow_closed EPF.in_carrier_curve assms 
  by force

lemma Gnot1onEPFcurve: "G \<noteq> \<one>\<^bsub>EPF.curve\<^esub>"
  using ECdomainParametersValid_def ECparamsValid EPF.one_curve by presburger

lemma nGeq1onEPFcurve: "G [^]\<^bsub>EPF.curve\<^esub> n = \<one>\<^bsub>EPF.curve\<^esub>"
proof - 
  have "point_mult' n G = Infinity" 
    using ECdomainParametersValid_def ECparamsValid by presburger 
  then show ?thesis 
    using GonEPFcurve EPF.in_carrier_curve EPF.one_curve EPF.multEqPowInCurve by auto 
qed

lemma invG: "inv\<^bsub>EPF.curve\<^esub> G = G [^]\<^bsub>EPF.curve\<^esub> (n-1)"
proof -
  have "prime n"             using ECparamsValid ECdomainParametersValid_def by blast
  then have "1 < n"          using prime_gt_1_nat by simp
  then have "1 + (n-1) = n"  by auto
  then have "G \<otimes>\<^bsub>EPF.curve\<^esub> (G [^]\<^bsub>EPF.curve\<^esub> (n-1)) = \<one>\<^bsub>EPF.curve\<^esub>"
    by (metis nGeq1onEPFcurve EPF.curve.nat_pow_Suc2 GonEPFcurve plus_1_eq_Suc)
  then show ?thesis
    using EPF.curve.comm_inv_char EPF.curve.nat_pow_closed GonEPFcurve by presburger 
qed

lemma ordGisn: 
  assumes "x < n"  "0 < x"
  shows "point_mult' x G \<noteq> Infinity"
  using ECdomainParametersValid_def ECparamsValid assms(1,2) EPF.order_n by presburger

lemma ordGisn': 
  assumes "x < n"  "0 < x"
  shows "G [^]\<^bsub>EPF.curve\<^esub> x \<noteq> \<one>\<^bsub>EPF.curve\<^esub>"
  using assms ordGisn EPF.one_curve EPF.multEqPowInCurve GonEPFcurve EPF.in_carrier_curve 
  by algebra

lemma curve_ord_G: "EPF.curve.ord G = n"
  using ECdomainParametersValid_def ECparamsValid EPF.curve_ord_n5 by presburger

lemma multGmodn: "point_mult' x G = point_mult' (x mod n) G"
  by (metis ECdomainParametersValid_def ECparamsValid EPF.multQmodn)

lemma multGmodn': "G[^]\<^bsub>EPF.curve\<^esub>x = G[^]\<^bsub>EPF.curve\<^esub>(x mod n)"
  using multGmodn EPF.in_carrier_curve GonEPFcurve EPF.multEqPowInCurve by fastforce 

lemma multdGmodn:
  assumes "P = point_mult' d G"
  shows   "point_mult' x P = point_mult' (x mod n) P"
  by (metis ECdomainParametersValid_def ECparamsValid EPF.in_carrier_curve EPF.multQmodn
            EPF.order_n_cycle assms dGonEPFcurve)

lemma multdGmodn':
  assumes "P = point_mult' d G"
  shows   "P[^]\<^bsub>EPF.curve\<^esub>x = P[^]\<^bsub>EPF.curve\<^esub>(x mod n)"
  using assms multdGmodn EPF.in_carrier_curve dGonEPFcurve EPF.multEqPowInCurve by fastforce

lemma multGmodn'int: "G[^]\<^bsub>EPF.curve\<^esub>(x::int) = G[^]\<^bsub>EPF.curve\<^esub>(x mod n)"
  by (metis EPF.in_carrier_curve EPF.one_curve GonEPFcurve EPF.multEqPowInCurve EPF.multQmodn'int
            nGeq1onEPFcurve prime_gt_1_nat ECparamsValid ECdomainParametersValid_def)

lemma multdGmodn'int: 
  assumes "P = point_mult' d G"
  shows   "P[^]\<^bsub>EPF.curve\<^esub>(x::int) = P[^]\<^bsub>EPF.curve\<^esub>(x mod n)"
  by (metis assms ECparamsValid EPF.in_carrier_curve EPF.multQmodn'int EPF.order_n_cycle
            dGonEPFcurve prime_gt_1_nat ECdomainParametersValid_def)


text \<open>Computations done on the components of elliptic curve points are done modulo p.  The order
of the curve, however, is n, a prime different from p.  So, for example, the scalar multiplication
(n+a)G = aG, because the generator G has order n.  So when computations are done on scalars
intended for a scalar multiplication of a point on the curve, those should be reduced modulo n.
In particular, we will need to compute inverses of scalars modulo n.\<close>

definition "Rn = residue_ring (int n)"

sublocale N: residues_prime n Rn
  using ECdomainParametersValid_def ECparamsValid residues_prime_def apply presburger
  using Rn_def by presburger 

abbreviation inv_mod_n :: "nat \<Rightarrow> nat" where
  "inv_mod_n x \<equiv> inv_mod n x"

lemma inv_mod_n_inv:
  assumes "x \<in> carrier Rn" "x \<noteq> 0" 
  shows   "inv\<^bsub>Rn\<^esub> x = inv_mod_n x"
  using N.inv_mod_p_inv_in_ring assms(1,2) by presburger

lemma inv_mod_n_inv':
  assumes "0 < x" "x < n"  
  shows   "inv\<^bsub>Rn\<^esub> x = inv_mod_n x"
  using assms inv_mod_n_inv by (simp add: N.res_carrier_eq) 


subsection \<open>3.2 Elliptic Curve Key Pairs\<close>

text \<open>3.2.1 Elliptic Curve Key Pair Generation Primitive

This section doesn't exactly define a validation primitive.  But from the Key Pair Generation
Primitive, we can write down what it means to be a valid EC key pair.  d is the private key
and Q is the public key.  We can also write down separately what it means for d to be a valid
private key.  Also note that the key generation method in 3.2.1 says to randomly select d.  As
we said above, we do not model random selection here, so we include d as an input.\<close>

definition ECkeyGen :: "nat \<Rightarrow> int point" where
  "ECkeyGen d = point_mult' d G"

definition ECkeyPairValid :: "nat \<Rightarrow> int point \<Rightarrow> bool" where
  "ECkeyPairValid d Q \<equiv> (0 < d) \<and> (d < n) \<and> (point_mult' d G = Q)"

definition ECprivateKeyValid :: "nat \<Rightarrow> bool" where
  "ECprivateKeyValid d \<equiv> (0 < d) \<and> (d < n)"

lemma ECkeyPairImpliesKeyGen:
  assumes "ECkeyPairValid d Q"
  shows   "Q = ECkeyGen d"
  using ECkeyGen_def ECkeyPairValid_def assms by presburger

lemma ECkeyPairEqKeyGen: "(ECkeyPairValid d Q) = ((Q = ECkeyGen d) \<and> ECprivateKeyValid d)"
  using ECkeyGen_def ECkeyPairValid_def ECprivateKeyValid_def by auto

lemma ECkeyPairImpliesPrivateKeyValid:
  assumes "ECkeyPairValid d Q"
  shows   "ECprivateKeyValid d"
  using assms ECkeyPairValid_def ECprivateKeyValid_def by auto

lemma ECkeyPairNotInf:
  assumes "ECkeyPairValid d Q"
  shows   "Q \<noteq> Infinity"
  by (metis assms ECkeyPairValid_def ordGisn)

lemma ECkeyPairOnCurve:
  assumes "ECkeyPairValid d Q"
  shows   "on_curve' Q"
  by (metis ECdomainParametersValid_def ECkeyPairValid_def ECparamsValid assms point_mult_closed)

lemma ECkeyPairOrd_n:
  assumes "ECkeyPairValid d Q"
  shows   "point_mult' n Q = Infinity"
  by (metis ECkeyPairValid_def assms mod_self multdGmodn point_mult.simps(1))

lemma ECkeyPair_dInRn':
  assumes "ECprivateKeyValid d"
  shows   "d \<in> carrier Rn"
  using ECprivateKeyValid_def N.res_carrier_eq assms by force

lemma ECkeyPair_dInRn:
  assumes "ECkeyPairValid d Q"
  shows   "d \<in> carrier Rn"
  using ECkeyPairValid_def N.res_carrier_eq assms by force

lemma ECkeyPair_invRn':
  assumes "ECprivateKeyValid d"
  shows   "inv\<^bsub>Rn\<^esub>d \<in> carrier Rn \<and> d\<otimes>\<^bsub>Rn\<^esub>inv\<^bsub>Rn\<^esub>d = \<one>\<^bsub>Rn\<^esub>"
  using ECprivateKeyValid_def N.inv_closed N.res_carrier_eq N.zero_cong assms by force

lemma ECkeyPair_invRn:
  assumes "ECkeyPairValid d Q"
  shows   "inv\<^bsub>Rn\<^esub>d \<in> carrier Rn \<and> d\<otimes>\<^bsub>Rn\<^esub>inv\<^bsub>Rn\<^esub>d = \<one>\<^bsub>Rn\<^esub>"
  using ECkeyPairValid_def N.inv_closed N.res_carrier_eq N.zero_cong assms by force

lemma ECkeyPair_inv_d':
  assumes "ECprivateKeyValid d"
  shows   "inv_mod_n d = inv\<^bsub>Rn\<^esub>d"
  using ECprivateKeyValid_def N.res_carrier_eq assms inv_mod_n_inv by force

lemma ECkeyPair_inv_d:
  assumes "ECkeyPairValid d Q"
  shows   "inv_mod_n d = inv\<^bsub>Rn\<^esub>d"
  using ECkeyPairValid_def N.res_carrier_eq assms inv_mod_n_inv by force

lemma ECkeyPair_curveMult:
  assumes "ECkeyPairValid d Q"
  shows   "G[^]\<^bsub>EPF.curve\<^esub>d = Q"
  using ECkeyPairValid_def EPF.in_carrier_curve GonEPFcurve assms EPF.multEqPowInCurve by auto 

lemma ECkeyGen_mod_n: "ECkeyGen d = ECkeyGen (d mod n)"
  using ECkeyGen_def multGmodn by presburger 

lemma ECkeyGen_valid_mod_n: "(d mod n \<noteq> 0) = ECprivateKeyValid (d mod n)"
  by (simp add: ECprivateKeyValid_def N.p_prime prime_gt_0_nat)

lemma ECkeyGen_int:
  fixes d :: int
  shows "G[^]\<^bsub>EPF.curve\<^esub>d = ECkeyGen (nat (d mod int n))"
  using EPF.ell_prime_field_axioms GonEPFcurve N.p_prime SEC1.ECkeyGen_def SEC1_axioms 
        ell_prime_field.in_carrier_curve ell_prime_field.multEqPowInCurve multGmodn'int 
        prime_gt_0_nat by force

text \<open>3.2.2.1 Elliptic Curve Public Key Validation Primitive\<close>

definition ECpublicKeyValid :: "int point \<Rightarrow> bool" where
  "ECpublicKeyValid Q \<equiv> (Q \<noteq> Infinity) \<and> (on_curve' Q) \<and> (point_mult' n Q = Infinity)"

text \<open>3.2.3.1 Elliptic Curve Public Key Partial Validation Primitive\<close>

definition ECpublicKeyPartialValid :: "int point \<Rightarrow> bool" where
  "ECpublicKeyPartialValid Q \<equiv> (Q \<noteq> Infinity) \<and> (on_curve' Q)"

lemma validImpliesPartialValid: "ECpublicKeyValid Q \<Longrightarrow> ECpublicKeyPartialValid Q"
  using ECpublicKeyPartialValid_def ECpublicKeyValid_def by blast

text \<open>In general, if we have a partially valid public key, it is not necessarily (fully) valid.
However, when h = 1, then this is true.\<close>
lemma partValidImpliesValidIFheq1:
  assumes "h = 1"  "ECpublicKeyPartialValid Q"
  shows   "ECpublicKeyValid Q"
proof - 
  have 1: "Q \<noteq> Infinity" using assms(2) ECpublicKeyPartialValid_def by fast
  have 2: "on_curve' Q"  using assms(2) ECpublicKeyPartialValid_def by fast
  have 3: "card {P. on_curve a b P} = n" 
    using ECparamsValid ECdomainParametersValid_def assms(1) by simp
  have 4: "point_mult' n Q = Infinity" 
    using 2 3 CurveOrderPrime EPF.AB_in_carrier EPF.nonsingular_in_bf N.p_prime by blast 
  show ?thesis  using 1 2 4 ECpublicKeyValid_def by presburger
qed

lemma partValidImpliesValidIFheq1':
  assumes "h = 1"  "Q \<noteq> Infinity"  "on_curve' Q"
  shows   "point_mult' n Q = Infinity"
  using partValidImpliesValidIFheq1 assms ECpublicKeyPartialValid_def ECpublicKeyValid_def
  by blast

lemma keyPairValidImpliespublicKeyValid:
  assumes "ECkeyPairValid d Q"
  shows   "ECpublicKeyValid Q"
  using ECkeyPairNotInf ECkeyPairOnCurve ECkeyPairOrd_n ECpublicKeyValid_def assms by blast 

lemma ECpublicKeyValid_curve:
  assumes "ECpublicKeyValid Q"
  shows   "Q \<noteq> \<one>\<^bsub>EPF.curve\<^esub> \<and> Q \<in> carrier EPF.curve \<and> Q[^]\<^bsub>EPF.curve\<^esub> n = \<one>\<^bsub>EPF.curve\<^esub>"
  using assms ECpublicKeyValid_def EPF.in_carrier_curve EPF.one_curve EPF.multEqPowInCurve by auto

lemma ECpublicKeyPartValid_curve:
  assumes "ECpublicKeyPartialValid Q"
  shows   "Q \<noteq> \<one>\<^bsub>EPF.curve\<^esub> \<and> Q \<in> carrier EPF.curve"
  using assms ECpublicKeyPartialValid_def EPF.in_carrier_curve EPF.one_curve by auto 

lemma ECkeyGenValid:
  assumes "ECprivateKeyValid d"
  shows   "ECpublicKeyValid (ECkeyGen d)"
  using ECkeyGen_def ECkeyPairValid_def ECprivateKeyValid_def assms 
        keyPairValidImpliespublicKeyValid by auto

lemma ECKeyGenValidPair:
  assumes "ECprivateKeyValid d"
  shows   "ECkeyPairValid d (ECkeyGen d)"
  using assms ECprivateKeyValid_def ECkeyGen_def ECkeyPairValid_def by simp


subsection \<open>3.3 Elliptic Curve Diffie-Hellman Primitives\<close>

text \<open>3.3.1 Elliptic Curve Diffie-Hellman Primitive\<close>

definition ECDHprim :: "nat \<Rightarrow> int point \<Rightarrow> int option" where
  "ECDHprim d\<^sub>U Q\<^sub>V = 
   ( let P = point_mult' d\<^sub>U Q\<^sub>V in
     ( case P of
         Infinity    \<Rightarrow> None
       | Point x\<^sub>P y\<^sub>P \<Rightarrow> Some x\<^sub>P )
   )"

lemma ECDHinCarrier: 
  assumes "ECDHprim d Q = Some z"  "on_curve' Q"
  shows   "z \<in> carrier R" 
proof - 
  let ?P = "point_mult' d Q" 
  have 1: "?P \<noteq> Infinity" using assms(1) ECDHprim_def by fastforce
  obtain x and y where 2: "?P = Point x y"  by (meson 1 point.exhaust) 
  have 3: "z = x"         using 1 2 assms(1) ECDHprim_def by auto
  have 4: "on_curve' ?P"  using assms(2) point_mult_closed by auto 
  show ?thesis            using 2 3 4 on_curve_def by auto
qed

lemma ECDH_validKeys:
  assumes "ECprivateKeyValid d"  "ECpublicKeyValid Q"
  shows   "\<exists>z. ECDHprim d Q = Some z"
proof - 
  have 1: "0 < d \<and> d < n" 
    using assms(1) ECprivateKeyValid_def by simp
  have 2: "on_curve' Q \<and> Q \<noteq> Infinity \<and> point_mult' n Q = Infinity" 
    using assms(2) ECpublicKeyValid_def  by blast
  let ?P = "point_mult' d Q" 
  have 3: "?P \<noteq> Infinity"                  using 1 2 EPF.order_n by blast 
  obtain x and y where 4: "?P = Point x y" using 3 point.exhaust by blast
  have 5: "ECDHprim d Q = Some x"          using 4 ECDHprim_def by force
  show ?thesis                             using 5 by fast
qed

lemma ECDH_curveMult:
  assumes "on_curve' Q"
  shows   "ECDHprim d Q =  ( let P = Q [^]\<^bsub>EPF.curve\<^esub> d in
                           ( case P of Infinity \<Rightarrow> None | Point x\<^sub>P y\<^sub>P \<Rightarrow> Some x\<^sub>P ))"
  using assms ECDHprim_def EPF.multEqPowInCurve by presburger 

text \<open>The important thing about Diffie-Hellman is that two entities can compute the same value
using only their own (private) key and the other's public information.  This lemma shows that.\<close>
lemma ECDH_2ValidKeyPairs:
  assumes "ECkeyPairValid d1 P1"  "ECkeyPairValid d2 P2"
  shows   "ECDHprim d1 P2 = ECDHprim d2 P1"
  by (metis (no_types, lifting) assms(1,2) ECDHprim_def ECkeyPairValid_def EPF.AB_in_carrier(1,2)
             EPF.in_carrier_curve EPF.nonsingular_in_bf GonEPFcurve mult.commute point_mult_mult)

text \<open>3.3.2 Elliptic Curve Cofactor Diffie-Hellman Primitive\<close>

definition ECcofDHprim :: "nat \<Rightarrow> int point \<Rightarrow> int option" where
  "ECcofDHprim d\<^sub>U Q\<^sub>V = 
   ( let P = point_mult' (h*d\<^sub>U) Q\<^sub>V in
     ( case P of
         Infinity    \<Rightarrow> None
       | Point x\<^sub>P y\<^sub>P \<Rightarrow> Some x\<^sub>P )
   )"

lemma ECcofDHinCarrier: 
  assumes "ECcofDHprim d Q = Some z" "on_curve' Q"
  shows   "z \<in> carrier R" 
proof - 
  let ?P = "point_mult' (h*d) Q" 
  have 1: "?P \<noteq> Infinity"                   using assms(1) ECcofDHprim_def by fastforce
  obtain x and y where 2: "?P = Point x y"  by (meson 1 point.exhaust) 
  have 3: "z = x"                           using 1 2 assms(1) ECcofDHprim_def by auto
  have 4: "on_curve' ?P"                    using assms(2) point_mult_closed by auto 
  show ?thesis                              using 2 3 4 on_curve_def by auto
qed

lemma ECcofDH_validKeys:
  assumes "ECprivateKeyValid d"  "ECpublicKeyValid Q"
  shows   "\<exists>z. ECcofDHprim d Q = Some z"
proof - 
  have 1: "0 < d \<and> d < n" 
    using assms(1) ECprivateKeyValid_def by simp
  have 2: "on_curve' Q \<and> Q \<noteq> Infinity \<and> point_mult' n Q = Infinity" 
    using assms(2) ECpublicKeyValid_def by blast
  have 3: "h < n"          using h_less_n ECparamsValid by auto
  have 4: "0 < h"          using ECdomainParametersValid_def ECparamsValid by presburger
  have 5: "\<not> n dvd d"      using 1   by fastforce
  have 6: "\<not> n dvd h"      using 3 4 by fastforce
  have 7: "\<not> n dvd (h*d)"  by (simp add: 5 6 N.p_coprime_left coprime_dvd_mult_left_iff)  
  let ?m = "(h*d) mod n"
  have 8: "0 < ?m"         using 7 mod_greater_zero_iff_not_dvd by blast 
  have 9: "?m < n"         using 3 by fastforce 
  let ?P = "point_mult' (h*d) Q" 
  have 10: "?P = point_mult' ?m Q" using EPF.multQmodn assms(2) ECpublicKeyValid_def by blast
  have 11: "?P \<noteq> Infinity"                  using 8 9 2 10 EPF.order_n by auto
  obtain x and y where 12: "?P = Point x y" using 11 point.exhaust by blast
  have "ECcofDHprim d Q = Some x"           using 12 ECcofDHprim_def by force
  then show ?thesis by fast
qed

lemma ECcoDH_curveMult:
  assumes "on_curve' Q"
  shows   "ECcofDHprim d Q =  ( let P = Q [^]\<^bsub>EPF.curve\<^esub> (h*d) in
                              ( case P of Infinity \<Rightarrow> None | Point x\<^sub>P y\<^sub>P \<Rightarrow> Some x\<^sub>P ))"
  using assms ECcofDHprim_def EPF.multEqPowInCurve by presburger 

text \<open>The important thing about Diffie-Hellman is that two entities can compute the same value 
using only their own (private) key and the other's public information.  This lemma shows that.\<close>
lemma ECcofDH_2ValidKeyPairs:
  assumes "ECkeyPairValid k1 P1" "ECkeyPairValid k2 P2"
  shows   "ECcofDHprim k1 P2 = ECcofDHprim k2 P1"
proof - 
  have 1: "P1 = point_mult' k1 G" using assms(1) by (simp add: ECkeyPairValid_def)
  have 2: "P2 = point_mult' k2 G" using assms(2) by (simp add: ECkeyPairValid_def)
  have 3: "point_mult' (h*k2) P1 = point_mult' (k1*(h*k2)) G"
    using 1 EPF.AB_in_carrier(1,2) EPF.in_carrier_curve EPF.nonsingular_in_bf GonEPFcurve 
          point_mult_mult by presburger  
  have 4: "point_mult' (h*k1) P2 = point_mult' (k2*(h*k1)) G"  
    using 2 EPF.AB_in_carrier(1,2) EPF.in_carrier_curve EPF.nonsingular_in_bf GonEPFcurve 
          point_mult_mult by presburger  
  show ?thesis by (metis 3 4 mult.commute mult.left_commute ECcofDHprim_def)
qed

text \<open>3.3.* Choose either "normal" or cofactor Diffie-Hellman.

In some of the schemes below, the entities U and V must agree to use either "normal" or
cofactor Diffie-Hellman.  This primitive is convenient to use in those definitions.\<close>

definition ECDHprimChoose :: "bool \<Rightarrow> nat \<Rightarrow> int point \<Rightarrow> int option" where
  "ECDHprimChoose useCoDH d\<^sub>U Q\<^sub>V = 
     (if useCoDH then (ECcofDHprim d\<^sub>U Q\<^sub>V) else (ECDHprim d\<^sub>U Q\<^sub>V) )"

lemma ECDHchooseinCarrier: 
  assumes "ECDHprimChoose useCo d Q = Some z"  "on_curve' Q"
  shows   "z \<in> carrier R" 
  using ECDHprimChoose_def ECDHinCarrier ECcofDHinCarrier assms by presburger

lemma ECDHchoose_validKeys:
  assumes "ECprivateKeyValid d"  "ECpublicKeyValid Q"
  shows   "\<exists>z. ECDHprimChoose useCo d Q = Some z"
  using ECDHprimChoose_def ECDH_validKeys ECcofDH_validKeys assms by presburger

text \<open>The important thing is that two entities can compute the same value using only their
own (private) key together with the other's public information.\<close>
lemma ECDHch_2ValidKeyPairs:
  assumes "ECkeyPairValid k1 P1"  "ECkeyPairValid k2 P2"
  shows   "ECDHprimChoose useCoDH k1 P2 = ECDHprimChoose useCoDH k2 P1"
  by (simp add: ECDHprimChoose_def ECDH_2ValidKeyPairs ECcofDH_2ValidKeyPairs assms(1,2))


subsection \<open>3.4 Elliptic Curve MQV Primitive

Compared to the Diffie-Hellman primitive, the MQV primitive is involved.  So we break the
definition into smaller chunks.  MQVcomputeQbar corresponds to steps 2 and 4 in the standard.
MQVcompute_s is step 3.  MQVcomputeP is step 5.\<close>

definition MQVcomputeQbar :: "int point \<Rightarrow> nat option" where
  "MQVcomputeQbar Q = 
  (case Q of
     Infinity  \<Rightarrow> None
   | Point x y \<Rightarrow> (
     let z    = (2::nat)^(nat (\<lceil>(log 2 n)/2\<rceil>));
         xBar = nat (x mod z)
     in Some (xBar + z)
  ))"

definition MQVcompute_s :: "nat \<Rightarrow> nat option \<Rightarrow> nat \<Rightarrow> nat option" where
  "MQVcompute_s d2U Q2Ubar d1U = 
  ( case Q2Ubar of
     None         \<Rightarrow> None
   | Some Q2Ubar' \<Rightarrow> Some ((d2U + Q2Ubar'*d1U) mod n))" 

definition MQVcomputeP :: 
  "nat option \<Rightarrow> int point \<Rightarrow> nat option \<Rightarrow> int point \<Rightarrow> int point option" where
  "MQVcomputeP s Q2V Q2Vbar Q1V =
  ( case s of
     None    \<Rightarrow> None
   | Some s' \<Rightarrow>
     (case Q2Vbar of
       None         \<Rightarrow> None
     | Some Q2Vbar' \<Rightarrow> Some ( point_mult' (h*s') (add' Q2V (point_mult' Q2Vbar' Q1V)) )
     )
  )"

definition ECMQVprim_validInput :: 
  "nat \<Rightarrow> int point \<Rightarrow> nat \<Rightarrow> int point \<Rightarrow> int point \<Rightarrow> int point \<Rightarrow> bool" where
  "ECMQVprim_validInput d1U Q1U d2U Q2U Q1V Q2V \<equiv> 
     (ECkeyPairValid d1U Q1U)      \<and> (ECkeyPairValid d2U Q2U) \<and> 
     (ECpublicKeyPartialValid Q1V) \<and> (ECpublicKeyPartialValid Q2V)"

text \<open>The standard has (d1U, Q1U) as one of the inputs, but the curve point Q1U does not appear
in the computation.  We write this function to be consistent with the text of the standard.\<close>
definition ECMQVprim :: 
  "nat \<Rightarrow> int point \<Rightarrow> nat \<Rightarrow> int point \<Rightarrow> int point \<Rightarrow> int point \<Rightarrow> int option" where
  "ECMQVprim d1U Q1U d2U Q2U Q1V Q2V = 
  ( let Q2Ubar = MQVcomputeQbar Q2U;
        s      = MQVcompute_s d2U Q2Ubar d1U;
        Q2Vbar = MQVcomputeQbar Q2V;
        P      = MQVcomputeP s Q2V Q2Vbar Q1V
    in 
    (case P of
       None             \<Rightarrow> None
     | Some Infinity    \<Rightarrow> None
     | Some (Point x y) \<Rightarrow> Some x
    )
  )"

lemma MQVcomputeQbar_notInf:
  assumes "Q \<noteq> Infinity"
  shows   "\<exists>Qbar. MQVcomputeQbar Q = Some Qbar"
  by (metis (no_types, lifting) MQVcomputeQbar_def assms point.case(2) point.exhaust)

lemma MQVcomputeQbar_validPair:
  assumes "ECkeyPairValid d2U Q2U"
  shows   "\<exists>Q2Ubar. MQVcomputeQbar Q2U = Some Q2Ubar"
  using ECkeyPairNotInf MQVcomputeQbar_notInf assms by blast

lemma MQVcomputeQbar_validPub:
  assumes "ECpublicKeyPartialValid Q2V"
  shows   "\<exists>Q2Vbar. MQVcomputeQbar Q2V = Some Q2Vbar"
  using ECpublicKeyPartialValid_def MQVcomputeQbar_notInf assms by presburger

lemma MQVcompute_s_validIn:
  assumes "ECkeyPairValid d2U Q2U"  "Q2Ubar = MQVcomputeQbar Q2U"
  shows   "\<exists>s. MQVcompute_s d2U Q2Ubar d1U = Some s"
  using MQVcomputeQbar_validPair MQVcompute_s_def assms(1,2) by fastforce

lemma MQVcomputeP_validIn:
  assumes "ECkeyPairValid d2U Q2U"  "ECpublicKeyPartialValid Q2V"  "Q2Ubar = MQVcomputeQbar Q2U"
          "s = MQVcompute_s d2U Q2Ubar d1U"  "Q2Vbar = MQVcomputeQbar Q2V" 
  shows   "\<exists>P. MQVcomputeP s Q2V Q2Vbar Q1V = Some P"
  using MQVcomputeP_def MQVcomputeQbar_validPair MQVcomputeQbar_validPub MQVcompute_s_def assms 
  by fastforce

text \<open>The important thing is that both U and V can compute the same value using only their
own key pairs and the other's public keys.  This lemma shows that is true.\<close>
lemma MQV_reverseUV:
  assumes "ECkeyPairValid d1U Q1U"  "ECkeyPairValid d2U Q2U"
          "ECkeyPairValid d1V Q1V"  "ECkeyPairValid d2V Q2V"
  shows   "ECMQVprim d1U Q1U d2U Q2U Q1V Q2V = ECMQVprim d1V Q1V d2V Q2V Q1U Q2U"
proof - 
  have U11: "Q1U = point_mult' d1U G" using assms(1) by (simp add: ECkeyPairValid_def)
  have U21: "Q2U = point_mult' d2U G" using assms(2) by (simp add: ECkeyPairValid_def)
  have V11: "Q1V = point_mult' d1V G" using assms(3) by (simp add: ECkeyPairValid_def)
  have V21: "Q2V = point_mult' d2V G" using assms(4) by (simp add: ECkeyPairValid_def)
  obtain Q2Ubar where Q2Ubar: "MQVcomputeQbar Q2U = Some Q2Ubar"
    using MQVcomputeQbar_validPair assms(2) by presburger 
  obtain Q2Vbar where Q2Vbar: "MQVcomputeQbar Q2V = Some Q2Vbar"
    using MQVcomputeQbar_validPair assms(4) by presburger 
  obtain sU where sU: "MQVcompute_s d2U (Some Q2Ubar) d1U = Some sU"
    by (simp add: MQVcompute_s_def) 
  have sU1: "sU = (d2U + Q2Ubar*d1U) mod n" using sU MQVcompute_s_def by simp
  obtain sV where sV: "MQVcompute_s d2V (Some Q2Vbar) d1V = Some sV"
    by (simp add: MQVcompute_s_def) 
  have sV1: "sV = (d2V + Q2Vbar*d1V) mod n" using sV MQVcompute_s_def by simp
  obtain PU where PU: "MQVcomputeP (Some sU) Q2V (Some Q2Vbar) Q1V = Some PU"
    by (simp add: MQVcomputeP_def)
  have U1: "PU = point_mult' (h*sU) (add' Q2V (point_mult' Q2Vbar Q1V))"
    using MQVcomputeP_def PU by auto
  have U2: "PU = point_mult' (h*sU) 
                             (add' (point_mult' d2V G) (point_mult' Q2Vbar (point_mult' d1V G)))"
    using U1 V11 V21 by fast
  have U3: "PU = point_mult' (h*sU) (point_mult' (d2V + Q2Vbar*d1V) G)" 
    by (metis U2 point_mult_add EPF.AB_in_carrier(1,2) EPF.in_carrier_curve EPF.nonsingular_in_bf
              GonEPFcurve V11 mult.commute point_mult_mult) 
  have U4: "PU = point_mult' (h*sU*(d2V + Q2Vbar*d1V)) G" 
    by (metis U3 point_mult_mult EPF.AB_in_carrier(1,2) EPF.in_carrier_curve EPF.nonsingular_in_bf
              GonEPFcurve mult.commute)
  let ?xU = "(h*sU*(d2V + Q2Vbar*d1V)) mod n"
  have U5: "PU = point_mult' ?xU G"   using U4 multGmodn by blast 
  obtain PV where PV: "MQVcomputeP (Some sV) Q2U (Some Q2Ubar) Q1U = Some PV"
    by (simp add: MQVcomputeP_def)
  have V1: "PV = point_mult' (h*sV) (add' Q2U (point_mult' Q2Ubar Q1U))"
    using MQVcomputeP_def PV by auto
  have V2: "PV = point_mult' (h*sV) 
                             (add' (point_mult' d2U G) (point_mult' Q2Ubar (point_mult' d1U G)))"
    using V1 U11 U21 by fast
  have V3: "PV = point_mult' (h*sV) (point_mult' (d2U + Q2Ubar*d1U) G)" 
    by (metis V2 point_mult_add EPF.AB_in_carrier(1,2) EPF.in_carrier_curve EPF.nonsingular_in_bf
              GonEPFcurve U11 mult.commute point_mult_mult)
  have V4: "PV = point_mult' (h*sV*(d2U + Q2Ubar*d1U)) G" 
    by (metis V3 point_mult_mult EPF.AB_in_carrier(1,2) EPF.in_carrier_curve EPF.nonsingular_in_bf
              GonEPFcurve mult.commute)
  let ?xV = "(h*sV*(d2U + Q2Ubar*d1U)) mod n"
  have V5: "PV = point_mult' ?xV G"   using V4 multGmodn by blast 
  have x1: "?xU = ?xV" by (metis sU1 sV1 mult.commute mod_mult_right_eq mult.assoc) 
  have x2: "PU = PV"   using x1 U5 V5 by argo
  show ?thesis         using x2 PU PV Q2Ubar Q2Vbar sU sV ECMQVprim_def by presburger 
qed


end (* of SEC1 locale *)

subsection \<open>3.5 Hash Functions\<close>

text \<open>Section 3.5 of SEC 1 covers the HASH functions that are supported by this standard.  The
supported hash functions are SHA-1, 224, 256, 384, and 512, all defined in FIPS 180, currently
in version 4.  We have translated that standard to HOL in FIPS180_4.thy.

In this theory, we don't define any hash function.  We only need to know the type of a hash
function.  For that, we use the type synonym below.  The key fact we will use for a hash function
is that for any input, the length of the output has hLen octets, for some fixed hLen.  For
example, SHA-256 always outputs hLen = 32 octets (256 bits).

There are limits on the length of a message that should be given to a SHA function, however as
we show in FIPS180_4.thy, you can still compute a hash output for any length of input message
and that output will have the correct length.  If Hash is hash_type, we can insist

\<open>\<forall>x. octets_valid (Hash x)\<close> and \<open>\<forall>x. length (Hash x) = hLen\<close>.  \<close>

type_synonym hash_type = "octets \<Rightarrow> octets"


subsection \<open>3.6 Key Derivation Functions\<close>

text \<open>This sections lists the key derivation functions (KDFs) that are supported by this standard.
Those are ANSI-X9.63-KDF, IKEv2-KDF, TLS-KDF, NIST-800-56-Concatenation-KDF.  The specification
states "The NIST-800-56-Catenation-KDF should be used, except for backwards compatability with
implementations already using one of the three other key derivation functions."

Again, we don't define any key derivation functions here.  We need only a type for key derivation
functions.  The example in 3.6.1 shows that the input is an octet string Z and a non-negative
integer keydatalen.  It has an optional input called SharedInfo which is also octets.  If the
optional SharedInfo is not used, that input will be the empty list [].  It produces an octet 
string of length keydatalen.

So we have the type of a key derivation function.  We also introduce the type of a function
which indicates if the input is valid for the key derivation function.  So if KDF is kdf_type
and KDF_ValidIn is kdf_validin_type, then we can insist that 
     \<open>\<forall>Z l I. KDF_ValidIn Z l I \<longrightarrow> length (KDF Z l I) = l \<and> octets_valid (KDF Z l I)\<close>\<close>

type_synonym kdf_type         = "octets \<Rightarrow> nat \<Rightarrow> octets \<Rightarrow> octets"
type_synonym kdf_validin_type = "octets \<Rightarrow> nat \<Rightarrow> octets \<Rightarrow> bool"

subsection \<open>3.7 MAC Schemes\<close>

text \<open>This section lists the MAC Schemes that are supported by this standard.  There are many,
based on HMAC (using various SHAs) and CMAC (using AES of various sizes).  A MAC scheme will
be used by ECIES in Section 5.1 below.

Again we need only to define a type for MAC functions.  The example given in 3.7 says that
the entities need to agree on a MAC scheme plus mackeylen and maclen.  Then they establish
a shared secret key K, an octet string of length mackeylen.  Then the tagging function takes
an input an octet string M and outputs an octet string D of length maclen.  Since mackeylen = 
length K, we don't need to list it separately as an input. And maclen is the length of the output
of MAC, so it's not an input as much as a feature of the MAC scheme.  So our type synonym for a 
generic MAC function, using the variable names in the standard, follows MAC(K, M) = D.  

We also give a mac_validin_type.  So if MAC is mac_type, and MAC_VI is mac_validin_type, We could
insist that 
     \<open>\<forall>K M. MAC_VI K M \<longrightarrow> length K         = mackeylen\<close> and  
     \<open>\<forall>K M. MAC_VI K M \<longrightarrow> length (MAC K M) = maclen\<close>    and
     \<open>\<forall>K M. MAC_VI K M \<longrightarrow> octets_valid (MAC K M)\<close>.  \<close>

type_synonym mac_type         = "octets \<Rightarrow> octets \<Rightarrow> octets"
type_synonym mac_validin_type = "octets \<Rightarrow> octets \<Rightarrow> bool"


subsection \<open>3.8 Symmetric Encryption Schemes\<close>

text \<open>This standard supports 3-key TDES, XOR, and AES as symmetric encryption schemes.

And encryption scheme, labelled ENC later in this standard, takes a shared private key K and a
message M and produces a ciphertext C.  All of these are octet strings.  The type of the
decryption is the same: it takes K and C and produces M.

If ENC is enc_type, ENC_VI is enc_validin_type, DEC is dec_type, and DEC_VI is dec_valid_in_type,
we might insist
  \<open>ENC_VI K M \<longrightarrow> DEC_VI K (ENC K M) \<and> DEC K (ENC K M) = M\<close> and
  \<open>DEC_VI K C \<longrightarrow> ENC_VI K (DEC K C) \<and> ENC K (DEC K C) = C\<close> 
\<close>

type_synonym enc_type         = "octets \<Rightarrow> octets \<Rightarrow> octets" 
type_synonym enc_validin_type = "octets \<Rightarrow> octets \<Rightarrow> bool" 

type_synonym dec_type         = "octets \<Rightarrow> octets \<Rightarrow> octets"
type_synonym dec_validin_type = "octets \<Rightarrow> octets \<Rightarrow> bool"

subsection \<open>3.9 Key Wrap Schemes\<close>

text \<open>This subsection specifies that either the NIST AES key wrap algorithm or the CMS TDES key
wrap algorithm
• must be used as the key wrap scheme in the Wrapped Key Transport Scheme, and
• should be used more generally when wrapping an existing symmetric key with another sym-
metric key.

A key wrap scheme takes as input a key-encryption key K, an octet string of length wrapkeylen, 
and an octet string C which is the key that needs wrapping.  It produces an octet string W, 
which is the wrapped key.

If WRAP is wrap_type, WRAP_VI is wrap_validin_type, UNWRAP is unwrap_type, and UNWRAP_VI is 
unwrap_validin_type, we might insist
  \<open>WRAP_VI K C   \<longrightarrow> UNWRAP_VI K (WRAP K C) \<and> UNWRAP K (WRAP K C) = C\<close> and
  \<open>UNWRAP_VI K W \<longrightarrow> WRAP_VI K (UNWRAP K W) \<and> WRAP K (UNWRAP K W) = W\<close> 
\<close>

type_synonym wrap_type         = "octets \<Rightarrow> octets \<Rightarrow> octets"
type_synonym wrap_validin_type = "octets \<Rightarrow> octets \<Rightarrow> bool"

type_synonym unwrap_type         = "octets \<Rightarrow> octets \<Rightarrow> octets"
type_synonym unwrap_validin_type = "octets \<Rightarrow> octets \<Rightarrow> bool"

subsection \<open>3.10 Random Number Generation\<close>

text \<open>Cryptographic keys must be generated in a way that prevents an adversary from guessing the
private key. Keys should be generated with the help of a random number generator.
Random number generators must comply with ANS X9.82 [X9.82] or corresponding NIST publi-
cation [800-90].

We don't model random number generation in this theory.  When the standard says "pick a random
number", we simply include that random value as an input to the function.\<close>

subsection \<open>3.11 Security Levels and Protection Lifetimes\<close>

text \<open>"Data protected with cryptography today may continue to need protection in the future.
Advances in cryptanalysis can be predicted, at least approximately. Based on current
approximations, this document requires that data that needs protection beyond the year 2010 must
be protected with 112-bit security or higher.  Data that needs protection beyond the year 2030 must
be protected with 128-bit security or higher.  Data that needs protection beyond the year 2040
should be protected with 192-bit security or higher. Data that needs protection beyond 2080 should
be protected with 256-bit security or higher."\<close>



section \<open>4 Signature Schemes\<close>

type_synonym sig_type  = "nat \<times> nat" 

subsection \<open>4.1 Elliptic Curve Digital Signature Algorithm\<close>

text \<open>In the setup (Section 4.1.1) for the Elliptic Curve Digital Signature Algorithm (ECDSA),
the "entities" U and V need to agree on a few things.

They have to pick a hash algorithm.  Above we discuss that the only approved hash algorithms are
found in FIPS 180, The Secure Hash Standard.  This hash is used only in the computation of the
message digest e.

They must also agree on an elliptic curve.  Also (Section 4.1.2) Entity U should  generate a key
pair \<open>(d\<^sub>U, Q\<^sub>U)\<close>.  Entity V should obtain \<open>Q\<^sub>U\<close>.\<close>

subsubsection \<open>4.1.3 Signing Operation\<close>

text \<open>Note in the standard, they convert the binary string Ebar to an octet string E and then
convert E to an integer e.  We do not need to compute E.  We can go straight from a bit string
to a nat.  You can see this in Words.bits_to_octets_to_nat, which shows that converting to a
nat from the bits is the same as going to octets then to a nat.  As an aside, this "e" is a
"message digest".

As noted above for p, because n is odd (n is an odd prime), and thus not a power of 2,
\<open>\<lceil>log 2 n\<rceil> = bit_length n\<close>.  I feel that using \<open>bit_length n\<close> is more understandable, and
for Isabelle to compute these values for given test vectors I must use \<open>bit_length n\<close>.\<close>

context SEC1
begin

definition ECDSA_compute_e :: "hash_type \<Rightarrow> octets \<Rightarrow> nat" where
  "ECDSA_compute_e Hash M = (
    let H    = Hash M;
        Hbar = octets_to_bits_len H;
        x    = bit_length n;
        Ebar = take x Hbar
    in bits_to_nat Ebar
  )"

lemma ECDSA_e_bnd:
  assumes "e = ECDSA_compute_e Hash M"  "octets_valid (Hash M)" 
  shows   "e < 2^(bit_length n)"
proof - 
  let ?H    = "Hash M"
  let ?Hbar = "octets_to_bits_len ?H"
  let ?x    = "bit_length n"
  let ?Ebar = "take ?x ?Hbar" 
  have 1: "e = bits_to_nat ?Ebar" using assms(1) ECDSA_compute_e_def by presburger
  have 2: "length ?Ebar \<le> ?x"     by fastforce
  have 3: "bits_valid ?Hbar"      using assms(2) octets_valid_to_bits_len_valid by fast
  have 4: "bits_valid ?Ebar"      using 3 words_valid_take by fast
  have 5: "e < 2^(length ?Ebar)" 
    by (metis 1 4 words_to_nat_len_bnd words_valid_def less_numeral_extra(1) power_one_right) 
  show ?thesis by (meson 2 5 le_trans linorder_not_less one_le_numeral power_increasing)  
qed

lemma ECDSA_e_bitlen:
  assumes "e = ECDSA_compute_e Hash M"  "octets_valid (Hash M)" 
  shows   "bit_length e \<le> bit_length n"
  using assms less_bit_len2 ECDSA_e_bnd by blast

lemma ECDSA_e_bitlen':
  assumes "e = ECDSA_compute_e Hash M"  "octets_valid (Hash M)" 
  shows   "bit_length e \<le> nat \<lceil>log 2 n\<rceil>"
  by (metis N.p_prime ECparamsValid n_not_2 ECDSA_e_bitlen bitLenLog2Prime assms nat_int)

text \<open>It could be that the hash function output has the same number of bits as the order n.
For example, the NIST curve P-256 has a 256-bit n.  Then if the hash used is SHA-256, the hash
output always has 256 bits.  In this case, the computation of e is simplified.\<close>
lemma ECDSA_e_hlen_eq:
  assumes "e = ECDSA_compute_e Hash M"  "octets_valid (Hash M)"  "length (Hash M) = hlen"
          "bit_length n = 8*hlen"
  shows   "e = octets_to_nat (Hash M)"
  by (metis ECDSA_compute_e_def assms octets_to_bits_len_len octets_to_bits_len_to_nat 
            order.refl take_all)

lemma ECDSA_e_hlen_eq':
  assumes "e = ECDSA_compute_e Hash M"  "octets_valid (Hash M)"  "length (Hash M) = hlen"
          "nat \<lceil>log 2 n\<rceil> = 8*hlen" 
  shows   "e = octets_to_nat (Hash M)"
  by (metis ECparamsValid n_not_2 N.p_prime bitLenLog2Prime nat_int assms ECDSA_e_hlen_eq) 

text \<open>Note that in the standard, the ephemeral key pair is denoted (k, R).  However the letter
R is used in this theory to refer to the ring of integers modulo the prime p.  We need to use
a different letter, so we use P instead of R.

Also, the procedure for singing a message is to first compute the message digest e and then sign
that digest.  For ease of application, we clearly delineate these two steps.\<close>
definition ECDSA_Sign_e :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int point \<Rightarrow> sig_type option" where
  "ECDSA_Sign_e d\<^sub>U e k P = 
  ( case P of 
      Infinity    \<Rightarrow> None
    | Point x\<^sub>P y\<^sub>P \<Rightarrow> 
      ( let r    = nat (x\<^sub>P mod n);
            kinv = inv_mod_n k;
            s    = (kinv*(e + r*d\<^sub>U)) mod n
       in
        if r = 0 then None else (
        if s = 0 then None else Some (r,s)
        )
      )
  )"

abbreviation ECDSA_Sign :: "hash_type \<Rightarrow> nat \<Rightarrow> octets \<Rightarrow> nat \<Rightarrow> int point \<Rightarrow> sig_type option" where
  "ECDSA_Sign Hash d\<^sub>U M k P \<equiv> ECDSA_Sign_e d\<^sub>U (ECDSA_compute_e Hash M) k P"

text \<open>The standard says to pick a key pair (k,P) for signing.  But as P is a function of k, we can
abbreviate these definitions.\<close>

abbreviation ECDSA_Sign_e' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> sig_type option" where
  "ECDSA_Sign_e' d\<^sub>U e k \<equiv> ECDSA_Sign_e d\<^sub>U e k (ECkeyGen k)"

abbreviation ECDSA_Sign' :: "hash_type \<Rightarrow> nat \<Rightarrow> octets \<Rightarrow> nat \<Rightarrow> sig_type option" where
  "ECDSA_Sign' Hash d\<^sub>U M k \<equiv> ECDSA_Sign Hash d\<^sub>U M k (ECkeyGen k)"

text \<open>Now a few facts about the signing operation.  Some of these are helpful in the public
key recovery operation which is defined in 4.1.6\<close>
lemma ECDSA_Sign_e_Inf:
  assumes "P = Infinity"
  shows   "ECDSA_Sign_e d\<^sub>U e k P = None"
  by (simp add: ECDSA_Sign_e_def assms)

lemma ECDSA_Sign_Inf:
  assumes "P = Infinity"
  shows   "ECDSA_Sign Hash d\<^sub>U M k P = None"
  using assms ECDSA_Sign_e_Inf ECDSA_Sign_e_def by simp

lemma ECDSA_Sign_e_Some:
  assumes "ECDSA_Sign_e d\<^sub>U e k P = Some S"
  shows   "P \<noteq> Infinity"
  using ECDSA_Sign_e_Inf assms by force

lemma ECDSA_Sign_Some:
  assumes "ECDSA_Sign Hash d\<^sub>U M k P = Some S"
  shows   "P \<noteq> Infinity"
  using ECDSA_Sign_e_Some assms ECDSA_Sign_e_def by simp

lemma ECDSA_Sign_e_SomeOut:
  assumes "ECDSA_Sign_e d\<^sub>U e k P = Some S"  "P = Point x y"  "r = nat (x mod n)"
          "kinv = inv_mod_n k"  "s = (kinv*(e + r*d\<^sub>U)) mod n"
  shows   "S = (r, s)"
  by (smt (z3) assms ECDSA_Sign_e_def option.distinct(1) option.inject point.simps(5)) 

lemma ECDSA_Sign_SomeOut:
  assumes "ECDSA_Sign Hash d\<^sub>U M k P = Some S"  "P = Point x y"  "r = nat (x mod n)"
          "kinv = inv_mod_n k"  "s = (kinv*(e + r*d\<^sub>U)) mod n"  "e = ECDSA_compute_e Hash M"
  shows   "S = (r, s)"
  using ECDSA_Sign_e_SomeOut assms ECDSA_Sign_e_def by algebra

lemma ECDSA_Sign_e_inRn:
  assumes "ECDSA_Sign_e d\<^sub>U e k P = Some S"  "r = fst S"  "s = snd S"
  shows   "0 < r \<and> r < n \<and> r \<in> carrier Rn \<and> 0 < s \<and> s < n \<and> s \<in> carrier Rn"
proof - 
  obtain x y where P: "P = Point x y" by (metis assms(1) ECDSA_Sign_e_Some point.exhaust) 
  let ?r    = "nat (x mod n)"
  let ?kinv = "inv_mod_n k"
  let ?s    = "(?kinv*(e + ?r*d\<^sub>U)) mod n"
  have r1: "0 < ?r"          using assms(1) ECDSA_Sign_e_def P gr_zeroI by fastforce 
  have r2: "?r < n"          using nat_less_iff prime_gt_1_nat r1 by fastforce  
  have r3: "?r \<in> carrier Rn" using r2 by fastforce 
  have s1: "0 < ?s"          using assms(1) ECDSA_Sign_e_def P gr_zeroI r1 by fastforce
  have s2: "?s < n"          using nat_less_iff prime_gt_1_nat by fastforce
  have s3: "?s \<in> carrier Rn" by (metis N.mod_in_carrier of_nat_mod)
  have S1: "S = (?r, ?s)"    using ECDSA_Sign_e_SomeOut P assms(1) by blast 
  show ?thesis               using S1 r1 r2 r3 s1 s2 s3 assms(2,3) by force
qed

lemma ECDSA_Sign_inRn:
  assumes "ECDSA_Sign Hash d\<^sub>U M k P = Some S"  "r = fst S"  "s = snd S" 
  shows   "0 < r \<and> r < n \<and> r \<in> carrier Rn \<and> 0 < s \<and> s < n \<and> s \<in> carrier Rn"
  using ECDSA_Sign_e_inRn assms ECDSA_Sign_e_def by algebra

lemma ECDSA_Sign_e_invRn:
  assumes "ECDSA_Sign_e d\<^sub>U e k P = Some S"  "r = fst S"  "s = snd S"
  shows   "inv_mod_n r = inv\<^bsub>Rn\<^esub>r \<and> r\<otimes>\<^bsub>Rn\<^esub>inv\<^bsub>Rn\<^esub>r = \<one>\<^bsub>Rn\<^esub> \<and> inv\<^bsub>Rn\<^esub>r \<in> carrier Rn \<and>
           inv_mod_n s = inv\<^bsub>Rn\<^esub>s \<and> s\<otimes>\<^bsub>Rn\<^esub>inv\<^bsub>Rn\<^esub>s = \<one>\<^bsub>Rn\<^esub> \<and> inv\<^bsub>Rn\<^esub>s \<in> carrier Rn"
  using ECDSA_Sign_e_inRn ECkeyPair_invRn' ECkeyPair_inv_d' ECprivateKeyValid_def assms 
  by presburger

lemma ECDSA_Sign_invRn:
  assumes "ECDSA_Sign Hash d\<^sub>U M k P = Some S"  "r = fst S"  "s = snd S" 
  shows   "inv_mod_n r = inv\<^bsub>Rn\<^esub>r \<and> r\<otimes>\<^bsub>Rn\<^esub>inv\<^bsub>Rn\<^esub>r = \<one>\<^bsub>Rn\<^esub> \<and> inv\<^bsub>Rn\<^esub>r \<in> carrier Rn \<and>
           inv_mod_n s = inv\<^bsub>Rn\<^esub>s \<and> s\<otimes>\<^bsub>Rn\<^esub>inv\<^bsub>Rn\<^esub>s = \<one>\<^bsub>Rn\<^esub> \<and> inv\<^bsub>Rn\<^esub>s \<in> carrier Rn"
  using ECDSA_Sign_e_invRn assms ECDSA_Sign_e_def by algebra

lemma ECDSA_Sign_e_SomeOut_Curve:
  assumes "ECDSA_Sign_e d\<^sub>U e k P = Some S"  "P = Point x y"  "r = nat (x mod n)"
          "kinv = inv\<^bsub>Rn\<^esub> k" "c = (e + r*d\<^sub>U) mod n"  "s = kinv \<otimes>\<^bsub>Rn\<^esub> c"  "ECkeyPairValid k P"
  shows   "S = (r, s)"
  by (smt (verit) assms ECDSA_Sign_e_SomeOut ECDSA_Sign_e_invRn ECkeyPair_inv_d split_beta
          N.res_mult_eq fst_eqD mod_mult_right_eq of_nat_mod semiring_1_class.of_nat_mult snd_eqD)

lemma ECDSA_Sign_e_SomeOut_Curve':
  assumes "ECDSA_Sign_e' d\<^sub>U e k = Some S"  "P = Point x y"  "r = nat (x mod n)"
          "kinv = inv\<^bsub>Rn\<^esub> k"  "c = (e + r*d\<^sub>U) mod n"  "s = kinv \<otimes>\<^bsub>Rn\<^esub> c"  "ECkeyGen k = P" 
          "ECprivateKeyValid k"
  shows   "S = (r, s)"
  using assms ECkeyPairEqKeyGen ECDSA_Sign_e_SomeOut_Curve by blast

lemma ECDSA_Sign_SomeOut_Curve:
  assumes "ECDSA_Sign Hash d\<^sub>U M k P = Some S"  "P = Point x y"  "r = nat (x mod n)"
          "kinv = inv\<^bsub>Rn\<^esub> k"  "c = (e + r*d\<^sub>U) mod n"  "s = kinv \<otimes>\<^bsub>Rn\<^esub> c"  "ECkeyPairValid k P"
          "e = ECDSA_compute_e Hash M"
  shows   "S = (r, s)"
  using ECDSA_Sign_e_SomeOut_Curve assms ECDSA_Sign_e_def by algebra

lemma ECDSA_Sign_SomeOut_Curve':
  assumes "ECDSA_Sign Hash d\<^sub>U M k P = Some S"  "P = Point x y"  "r = nat (x mod n)"
          "kinv = inv\<^bsub>Rn\<^esub> k"  "c = (e + r*d\<^sub>U) mod n"  "s = kinv \<otimes>\<^bsub>Rn\<^esub> c"  "ECkeyGen k = P" 
          "e = ECDSA_compute_e Hash M"  "ECprivateKeyValid k" 
  shows   "S = (r, s)"
  using assms ECkeyPairEqKeyGen ECDSA_Sign_SomeOut_Curve by presburger

lemma ECDSA_Sign_e_SomeOut_r:
  assumes "ECDSA_Sign_e d\<^sub>U e k P = Some S"  "P = Point x y"  "r = fst S"
  shows   "r = nat (x mod n)"
  using assms ECDSA_Sign_e_SomeOut by fastforce

lemma ECDSA_Sign_SomeOut_r:
  assumes "ECDSA_Sign Hash d\<^sub>U M k P = Some S"  "P = Point x y"  "r = fst S"
  shows   "r = nat (x mod n)"
  using ECDSA_Sign_e_SomeOut_r assms ECDSA_Sign_e_def by blast

lemma ECDSA_Sign_e_SomeOut_s:
  assumes "ECDSA_Sign_e d\<^sub>U e k P = Some S"  "P = Point x y"  "s = snd S"  "r = nat (x mod n)" 
          "kinv = inv_mod_n k" 
  shows   "s = (kinv*(e + r*d\<^sub>U)) mod n"
  using assms ECDSA_Sign_e_SomeOut by fastforce

lemma ECDSA_Sign_SomeOut_s:
  assumes "ECDSA_Sign Hash d\<^sub>U M k P = Some S"  "P = Point x y"  "s = snd S"  "r = nat (x mod n)" 
          "kinv = inv_mod_n k"  "e = ECDSA_compute_e Hash M"
  shows   "s = (kinv*(e + r*d\<^sub>U)) mod n"
  using ECDSA_Sign_e_SomeOut_s assms ECDSA_Sign_e_def by blast

lemma ECDSA_Sign_e_SomeOut_curve_s:
  fixes   x :: int
  assumes "ECDSA_Sign_e d\<^sub>U e k P = Some S"  "P = Point x y"  "s = snd S"  "r = nat (x mod n)" 
          "kinv = inv\<^bsub>Rn\<^esub> k"  "c = (e + r*d\<^sub>U) mod n"  "ECkeyPairValid k P"
  shows   "s = kinv \<otimes>\<^bsub>Rn\<^esub> c"
  by (smt (verit) assms ECDSA_Sign_e_SomeOut_s ECkeyPair_inv_d N.mult_cong N.res_mult_eq 
          mod_mod_trivial of_nat_mod semiring_1_class.of_nat_mult)

lemma ECDSA_Sign_e_SomeOut_curve_s':
  fixes   x :: int
  assumes "ECDSA_Sign_e d\<^sub>U e k P = Some S"  "P = Point x y"  "s = snd S"  "r = nat (x mod n)" 
          "kinv = inv\<^bsub>Rn\<^esub> k"  "c = (e + r*d\<^sub>U) mod n"  "ECkeyGen k = P"  "ECprivateKeyValid k"
  shows   "s = kinv \<otimes>\<^bsub>Rn\<^esub> c"
  using assms ECkeyPairEqKeyGen ECDSA_Sign_e_SomeOut_curve_s by algebra

lemma ECDSA_Sign_SomeOut_curve_s:
  fixes   x :: int
  assumes "ECDSA_Sign Hash d\<^sub>U M k P = Some S"  "P = Point x y"  "s = snd S"  "r = nat (x mod n)" 
          "kinv = inv\<^bsub>Rn\<^esub> k"  "c = (e + r*d\<^sub>U) mod n"  "ECkeyPairValid k P" 
          "e = ECDSA_compute_e Hash M"
  shows   "s = kinv \<otimes>\<^bsub>Rn\<^esub> c"
  using ECDSA_Sign_e_SomeOut_curve_s assms ECDSA_Sign_e_def by algebra

lemma ECDSA_Sign_SomeOut_curve_s':
  fixes   x :: int
  assumes "ECDSA_Sign Hash d\<^sub>U M k P = Some S"  "P = Point x y"  "s = snd S"  "r = nat (x mod n)"
          "kinv = inv\<^bsub>Rn\<^esub> k"  "c = (e + r*d\<^sub>U) mod n"  "ECkeyGen k = P"  "ECprivateKeyValid k"
          "e = ECDSA_compute_e Hash M"
  shows   "s = kinv \<otimes>\<^bsub>Rn\<^esub> c"
  using assms ECkeyPairEqKeyGen ECDSA_Sign_SomeOut_curve_s by algebra

text \<open>Now a few facts about signing with (k mod n) as the private ephemeral key versus k.\<close>

lemma ECDSA_Sign_e_kmodn: "ECDSA_Sign_e d\<^sub>U e k P = ECDSA_Sign_e d\<^sub>U e (k mod n) P"
  using inv_mod_mod ECDSA_Sign_e_def by presburger

lemma ECDSA_Sign_kmodn: "ECDSA_Sign Hash d\<^sub>U M k P = ECDSA_Sign Hash d\<^sub>U M (k mod n) P"
  using ECDSA_Sign_e_kmodn ECDSA_Sign_e_def by fast

lemma ECDSA_Sign_e'_kmodn: "ECDSA_Sign_e' d\<^sub>U e k = ECDSA_Sign_e' d\<^sub>U e (k mod n)"
  using ECDSA_Sign_e_kmodn ECkeyGen_mod_n by presburger

lemma ECDSA_Sign'_kmodn: "ECDSA_Sign' Hash d\<^sub>U M k = ECDSA_Sign' Hash d\<^sub>U M (k mod n)"
  using ECDSA_Sign_e'_kmodn ECDSA_Sign_e_def by fast


subsubsection \<open>4.1.4 Verifying Operation\<close>

text \<open>Again, the standard uses the letter R to represent a curve point.  Here R is used to
denote the ring of integers mod p.  So use a different letter (P) to avoid confusion.

As above, the way to verify that a signature S matches a message M is to first compute the message
digest e and verify that S matches e.  So we again delineate the two steps of calculating the
digest and verifying S against e.

Recall that \<open>(d\<^sub>U,Q\<^sub>U)\<close> is the (long-term) key pair for the signer U.\<close>
definition ECDSA_Verify_e :: "int point \<Rightarrow> nat \<Rightarrow> sig_type \<Rightarrow> bool" where
  "ECDSA_Verify_e Q\<^sub>U e S =
  ( let r    = fst S; 
        s    = snd S; 
        sinv = inv_mod_n s;
        u1   = (e*sinv) mod n;
        u2   = (r*sinv) mod n;
        P    = add' (point_mult' u1 G) (point_mult' u2 Q\<^sub>U)
    in
       (case P of 
          Infinity  \<Rightarrow> False
        | Point x y \<Rightarrow> (
             (0 < r) \<and> (r < n) \<and> (0 < s) \<and> (s < n) \<and> (nat (x mod n) = r) )
       )
  )" 

abbreviation ECDSA_Verify :: "hash_type \<Rightarrow> int point \<Rightarrow> octets \<Rightarrow> sig_type \<Rightarrow> bool" where
  "ECDSA_Verify Hash Q\<^sub>U M S \<equiv> ECDSA_Verify_e Q\<^sub>U (ECDSA_compute_e Hash M) S"

text \<open>If M is signed with a valid ephemeral key pair (k, P), then the resulting signature S will
pass the verification routine for M.\<close>
lemma ECDSA_Sign_e_Verify:
  assumes "ECDSA_Sign_e   d\<^sub>U e k P = Some S"  "ECkeyPairValid k P"  "ECkeyPairValid d\<^sub>U Q\<^sub>U" 
  shows   "ECDSA_Verify_e Q\<^sub>U e S"
proof - 
  obtain x y where P: "P = Point x y" by (metis assms(1) ECDSA_Sign_e_Some point.exhaust) 
  let ?r    = "nat (x mod n)"
  let ?kinv = "inv_mod_n k"
  let ?s    = "(?kinv*(e + ?r*d\<^sub>U)) mod n"
  have S1: "S = (?r, ?s)"            using ECDSA_Sign_e_SomeOut P assms(1) by blast 
  have S2: "fst S = ?r \<and> snd S = ?s" using S1 by force
  have r1: "0 < ?r"                  by (metis assms(1) S2 ECDSA_Sign_e_inRn)
  have r2: "?r < n"                  by (metis assms(1) S2 ECDSA_Sign_e_inRn)  
  have s1: "0 < ?s"                  by (metis assms(1) S2 ECDSA_Sign_e_inRn)
  have s2: "?s < n"                  by (metis assms(1) S2 ECDSA_Sign_e_inRn)
  let ?x = "(e + ?r*d\<^sub>U) mod n" 
  have x0: "?s = ?kinv \<otimes>\<^bsub>Rn\<^esub> ?x"  
    by (metis ECDSA_Sign_e_SomeOut_curve_s ECkeyPair_inv_d P S2 assms(1,2))
  have x1: "0 < ?x"           by (metis s1 mod_mod_trivial mod_mult_right_eq mult_0_right not_gr0)
  have x2: "?x \<in> carrier Rn"  by (metis N.mod_in_carrier of_nat_mod)
  have k1: "k \<in> carrier Rn"   using assms(2) ECkeyPair_dInRn by fast
  have k2: "k \<noteq> 0"            using ECkeyPairValid_def assms(2) by blast
  have k3: "?kinv = inv\<^bsub>Rn\<^esub>k" using ECkeyPair_inv_d assms(2) by auto
  have k4: "inv\<^bsub>Rn\<^esub>?kinv = k" using N.nonzero_inverse_inverse_eq N.zero_cong k1 k2 k3 by force 
  let ?sinv = "inv_mod_n ?s" 
  have s3: "?sinv = inv\<^bsub>Rn\<^esub>?s" by (metis s2 s1 inv_mod_n_inv') 
  have s4: "?sinv = inv\<^bsub>Rn\<^esub>?kinv \<otimes>\<^bsub>Rn\<^esub> inv\<^bsub>Rn\<^esub>?x"
    using N.m_comm N.nonzero_imp_inverse_nonzero N.nonzero_inverse_mult_distrib N.zero_cong 
          k1 k2 k3 s3 x0 x1 x2 by auto 
  have s5: "?sinv = k \<otimes>\<^bsub>Rn\<^esub> inv\<^bsub>Rn\<^esub>?x" using s4 k4 by presburger
  let ?u1   = " (e*?sinv) mod n"
  let ?u2   = "(?r*?sinv) mod n"
  let ?P    = "add' (point_mult' ?u1 G) (point_mult' ?u2 Q\<^sub>U)"
  have kP2: "G [^]\<^bsub>EPF.curve\<^esub>k = P"    using assms(2) ECkeyPair_curveMult by fast
  have P1: "?P = G [^]\<^bsub>EPF.curve\<^esub>?u1 \<otimes>\<^bsub>EPF.curve\<^esub> Q\<^sub>U [^]\<^bsub>EPF.curve\<^esub>?u2"
    using ECkeyPairOnCurve EPF.add_curve EPF.in_carrier_curve GonEPFcurve assms(3) 
          EPF.multEqPowInCurve by presburger 
  have P2: "Q\<^sub>U [^]\<^bsub>EPF.curve\<^esub>?u2 = G [^]\<^bsub>EPF.curve\<^esub>(d\<^sub>U*?u2)"
    using ECkeyPair_curveMult EPF.curve.nat_pow_pow GonEPFcurve assms(3) by blast
  have P3: "?P = G [^]\<^bsub>EPF.curve\<^esub>(?u1 + d\<^sub>U*?u2)" 
    using P1 P2 EPF.curve.nat_pow_mult GonEPFcurve by presburger 
  have k5: "(?u1 + d\<^sub>U*?u2) mod n = ?x*?sinv mod n"
    by (smt (z3) add_mult_distrib mod_add_cong mod_add_left_eq mod_mult_right_eq mult.assoc 
            mult.commute) 
  have k6: "?x*?sinv mod n = ?x\<otimes>\<^bsub>Rn\<^esub>?sinv" by (simp add: N.res_mult_eq of_nat_mod)
  have k7: "?x\<otimes>\<^bsub>Rn\<^esub>?sinv = ?x \<otimes>\<^bsub>Rn\<^esub> k \<otimes>\<^bsub>Rn\<^esub> inv\<^bsub>Rn\<^esub>?x" 
    by (metis N.inv_closed N.m_assoc N.zero_cong gr_implies_not0 k1 of_nat_eq_0_iff x1 x2 k6 s5)
  have k8: "?x \<otimes>\<^bsub>Rn\<^esub> k \<otimes>\<^bsub>Rn\<^esub> inv\<^bsub>Rn\<^esub>?x = k"
    by (metis N.inv_closed N.m_lcomm N.r_inv N.r_one N.zero_cong k1 k7 less_not_refl2 
              of_nat_eq_0_iff s5 x1 x2) 
  have k9: "(?u1 + d\<^sub>U*?u2) mod n = k"   by (metis k5 k6 k7 k8 nat_int) 
  have P4: "?P = P"                     by (metis P3 k9 kP2 multGmodn') 
  show ?thesis                          using P4 S2 P r1 r2 s1 s2 ECDSA_Verify_e_def by auto
qed

lemma ECDSA_Sign_e_Verify':
  assumes "ECDSA_Sign_e'  d\<^sub>U e k = Some S"  "ECprivateKeyValid k"  "ECkeyPairValid d\<^sub>U Q\<^sub>U" 
  shows   "ECDSA_Verify_e Q\<^sub>U e S"
  using assms ECDSA_Sign_e_Verify ECkeyPairEqKeyGen by blast

lemma ECDSA_Sign_Verify:
  assumes "ECDSA_Sign   Hash d\<^sub>U M k P = Some S"  "ECkeyPairValid k P"  "ECkeyPairValid d\<^sub>U Q\<^sub>U" 
  shows   "ECDSA_Verify Hash Q\<^sub>U M S"
  using ECDSA_Sign_e_def ECDSA_Sign_e_Verify ECDSA_Verify_e_def assms by fast

lemma ECDSA_Sign_Verify':
  assumes "ECDSA_Sign'  Hash d\<^sub>U M k = Some S"  "ECprivateKeyValid k"  "ECkeyPairValid d\<^sub>U Q\<^sub>U" 
  shows   "ECDSA_Verify Hash Q\<^sub>U M S"
  using assms ECDSA_Sign_Verify ECkeyPairEqKeyGen by blast


subsubsection \<open>4.1.5 Alternative Verifying Operation\<close>

text \<open>If the verifier knows U's private key \<open>d\<^sub>U\<close>, they can use this alternate form of the
verification routine.  In short, if the verifier knows \<open>d\<^sub>U\<close>, they can compute the (private)
ephemeral signing k labeled k above.  Note that this alternate verifying operation needs only one
elliptic curve operation, as opposed to the two needed above.\<close>
definition ECDSA_Verify_e_Alt :: "nat \<Rightarrow> nat \<Rightarrow> sig_type \<Rightarrow> bool" where
  "ECDSA_Verify_e_Alt d\<^sub>U e S =
  ( let r    = fst S; 
        s    = snd S; 
        sinv = inv_mod_n s;
        u1   = nat ((e*sinv) mod n);
        u2   = nat ((r*sinv) mod n);
        P    = point_mult' (u1 + u2*d\<^sub>U) G
    in
       (case P of 
          Infinity  \<Rightarrow> False
        | Point x y \<Rightarrow> (
             (0 < r) \<and> (r < n) \<and> (0 < s) \<and> (s < n) \<and> (nat (x mod n) = r) )
       )
  )" 

definition ECDSA_Verify_Alt :: "hash_type \<Rightarrow> nat \<Rightarrow> octets \<Rightarrow> sig_type \<Rightarrow> bool" where
  "ECDSA_Verify_Alt Hash d\<^sub>U M S = ECDSA_Verify_e_Alt d\<^sub>U (ECDSA_compute_e Hash M) S"

lemma ECDSA_Verify_e_eq: 
  assumes "ECkeyPairValid d\<^sub>U Q\<^sub>U"
  shows   "ECDSA_Verify_e_Alt d\<^sub>U e S = ECDSA_Verify_e Q\<^sub>U e S"
  by (smt (z3) ECDSA_Verify_e_Alt_def ECDSA_Verify_e_def ECkeyPairOnCurve ECkeyPairValid_def 
          EPF.add_curve EPF.curve.nat_pow_mult EPF.curve.nat_pow_pow EPF.in_carrier_curve 
          GonEPFcurve assms(1) mult.commute EPF.multEqPowInCurve nat_int)

lemma ECDSA_Verify_eq: 
  assumes "ECkeyPairValid d\<^sub>U Q\<^sub>U"
  shows   "ECDSA_Verify_Alt Hash d\<^sub>U M S = ECDSA_Verify Hash Q\<^sub>U M S"
  using ECDSA_Verify_Alt_def ECDSA_Verify_e_eq assms by presburger

text \<open>If you can recover the ephemeral signing key (because you know the long-term secret key)
from a paired message (digest) and verified signature, then if you sign that message with that
recovered signing key, you will get back that signature.  This is the inverse of the lemma above
which says that if you sign a message and get S, then S will be verified as a correct signature
for the message.\<close>
definition ECDSA_Verify_Alt_recover_k :: "nat \<Rightarrow> nat \<Rightarrow> sig_type \<Rightarrow> nat" where
  "ECDSA_Verify_Alt_recover_k d\<^sub>U e S = 
  ( let r    = fst S; 
        s    = snd S; 
        sinv = inv_mod_n s;
        u1   = nat ((e*sinv) mod n);
        u2   = nat ((r*sinv) mod n) 
    in (u1 + u2*d\<^sub>U) mod n
  )" 

lemma recovered_k_less_n: "ECDSA_Verify_Alt_recover_k d\<^sub>U e S < n"
  by (metis ECDSA_Verify_Alt_recover_k_def N.p_prime mod_less_divisor prime_gt_0_nat)

lemma ECDSA_Verify_e_Sign:
  assumes "ECDSA_Verify_e Q\<^sub>U e S"  "P = point_mult' k G"  "ECkeyPairValid d\<^sub>U Q\<^sub>U" 
          "k = ECDSA_Verify_Alt_recover_k d\<^sub>U e S"
  shows   "ECDSA_Sign_e d\<^sub>U e k P = Some S" 
proof - 
  have 1: "ECDSA_Verify_e_Alt d\<^sub>U e S" using assms(1,3) ECDSA_Verify_e_eq by fast
  let ?r    = "fst S"
  let ?s    = "snd S"
  let ?sinv = "inv_mod_n ?s"
  let ?u1   = "nat (( e*?sinv) mod n)"
  let ?u2   = "nat ((?r*?sinv) mod n)"
  let ?P    = "point_mult' (?u1 + ?u2*d\<^sub>U) G"
  have P1: "?P = point_mult' ((?u1 + ?u2*d\<^sub>U) mod n) G"   using multGmodn by presburger
  have P2: "?P = point_mult' k G"           by (metis P1 assms(4) ECDSA_Verify_Alt_recover_k_def)
  have P3: "?P = P"                         using assms(2) ECkeyPairValid_def P2 by algebra
  have P4: "?P \<noteq> Infinity"                  using 1 ECDSA_Verify_e_Alt_def by fastforce
  obtain x and y where P5: "?P = Point x y" using P4 point.exhaust by blast
  have 2: "(0 < ?r) \<and> (?r < n) \<and> (0 < ?s) \<and> (?s < n) \<and> (nat (x mod n) = ?r)" 
    by (smt (verit) 1 ECDSA_Verify_e_Alt_def P5 point.case(2)) 
  have s1: "?sinv = inv\<^bsub>Rn\<^esub>?s"              using 2 inv_mod_n_inv' by fastforce
  have s2: "inv\<^bsub>Rn\<^esub>?sinv = ?s" 
    by (simp add: 2 s1 ECkeyPair_dInRn' ECprivateKeyValid_def N.nonzero_inverse_inverse_eq
                  N.zero_cong)
  have k1: "0 < k"  by (metis P2 P4 assms(2) gr0I point_mult.simps(1))
  have k2: "k < n"  using assms(4) recovered_k_less_n by simp
  let ?c = "(e + ?r*d\<^sub>U) mod n" 
  have k3: "k = ?c*?sinv mod n"
    by (metis (no_types, lifting) ECDSA_Verify_Alt_recover_k_def assms(4) distrib_right 
        mod_add_left_eq mod_add_right_eq mod_mult_left_eq mult.assoc mult.commute nat_int) 
  have c1: "0 < ?c \<and> ?c < n" 
    by (metis bot_nat_0.not_eq_extremum k1 k2 k3 less_nat_zero_code mod_0 mod_less_divisor mult_0)
  let ?kinv = "inv_mod_n k"
  have k4: "?kinv = inv\<^bsub>Rn\<^esub> k"       using k1 k2 inv_mod_n_inv' by fastforce 
  have k5: "k = ?c \<otimes>\<^bsub>Rn\<^esub> inv\<^bsub>Rn\<^esub>?s"  by (simp add: N.res_mult_eq k3 of_nat_mod s1)
  have k6: "inv\<^bsub>Rn\<^esub> k = (inv\<^bsub>Rn\<^esub>?c) \<otimes>\<^bsub>Rn\<^esub> ?s" 
    by (metis 2 k5 s1 s2 c1 ECkeyGen_valid_mod_n ECkeyPair_dInRn' ECkeyPair_invRn' N.m_comm
        N.nonzero_imp_inverse_nonzero N.nonzero_inverse_mult_distrib N.zero_cong
        bot_nat_0.not_eq_extremum mod_if of_nat_eq_0_iff)
  let ?s' = "(?kinv*(e + ?r*d\<^sub>U)) mod n"
  have s3: "?s' = (inv\<^bsub>Rn\<^esub> k) \<otimes>\<^bsub>Rn\<^esub> ?c"
    by (simp add: N.res_mult_eq k4 mod_mult_right_eq of_nat_mod)
  have s4: "?s' = ((inv\<^bsub>Rn\<^esub>?c) \<otimes>\<^bsub>Rn\<^esub> ?c) \<otimes>\<^bsub>Rn\<^esub> ?s" 
    by (metis (no_types, lifting) 2 k4 k6 s3 ECkeyPair_invRn' ECprivateKeyValid_def
              ECkeyPair_dInRn' N.cring_simprules(11) N.res_mult_eq c1 mult.commute)
  have s5: "?s = ?s'" 
    by (metis 2 s4 ECkeyGen_valid_mod_n ECkeyPair_dInRn' ECkeyPair_invRn' EPF.nat_int_eq
              N.m_closed N.m_comm N.r_one c1 mod_if nat_neq_iff) 
  have A1: "ECDSA_Sign_e d\<^sub>U e k P = 
     ( let r = nat (x mod n); kinv = inv_mod_n k; s = (kinv*(e + r*d\<^sub>U)) mod n in
        if r = 0 then None else (if s = 0 then None else Some (r,s)))"
    using ECDSA_Sign_e_def P3 P4 P5 by force
  have A2: "ECDSA_Sign_e d\<^sub>U e k P = (if ?r = 0 then None else 
           (if ?s = 0 then None else Some (?r,?s)))" 
    by (smt (verit) 2 A1 s5) 
  show ?thesis using A2 2 by auto
qed

lemma ECDSA_Verify_Sign:
  assumes "ECDSA_Verify Hash Q\<^sub>U M S"  "P = point_mult' k G"  "ECkeyPairValid d\<^sub>U Q\<^sub>U" 
          "k = ECDSA_Verify_Alt_recover_k d\<^sub>U (ECDSA_compute_e Hash M) S"
  shows   "ECDSA_Sign Hash d\<^sub>U M k P = Some S" 
  by (metis ECDSA_Verify_e_Sign assms)

text \<open>One last variation on this theme.  Suppose that the cofactor h = 1.  Then you know that
every point on the curve is a power of the generator G.  So if you know that \<open>Q\<^sub>U\<close> is a partially
valid public key, then we know that there is a corresponding private key \<open>d\<^sub>U\<close>.  If you could find
that private key (which, in practice, you can't), then you can use it to recover the ephemeral
signing key.\<close>
lemma ECDSA_Verify_Sign_h1:
  assumes "ECpublicKeyPartialValid Q\<^sub>U"  "ECDSA_Verify_e Q\<^sub>U e S"  "h = 1"
  shows   "\<exists>d\<^sub>U. (Q\<^sub>U = point_mult' d\<^sub>U G \<and> 
                ECDSA_Sign_e' d\<^sub>U e (ECDSA_Verify_Alt_recover_k d\<^sub>U e S) = Some S)"
proof - 
  have 1: "on_curve' Q\<^sub>U"               using assms(1) ECpublicKeyPartialValid_def  by blast
  obtain d\<^sub>U where 2: "d\<^sub>U<n \<and> Q\<^sub>U = point_mult' d\<^sub>U G" using assms(3) 1 EC_h1_cyclic'  by blast 
  have 3: "Q\<^sub>U \<noteq> Infinity"              using assms(1) ECpublicKeyPartialValid_def by blast
  have 4: "0 < d\<^sub>U"                     by (metis 2 3 not_gr0 point_mult.simps(1)) 
  have 5: "ECkeyPairValid d\<^sub>U Q\<^sub>U"       using 2 4 ECkeyPairValid_def by blast
  have 6: "ECDSA_Sign_e' d\<^sub>U e (ECDSA_Verify_Alt_recover_k d\<^sub>U e S) = Some S"
    using 5 ECDSA_Verify_e_Sign ECkeyGen_def assms(2) by blast 
  show ?thesis  using 2 6 by fast
qed


subsubsection \<open>4.1.6 Public Key Recovery Operation\<close>

text \<open>The idea is that if you have a signature, you can generate a small list of putative values
for the public key.  Then if you have an oracle, you can test each of these putative values.  This
is a convenient option in bandwidth-constrained environments.  What might this oracle be?  For
example, if you have a second message (M2) and the signature for that message (S2), then you can
check that (ECDSA_Verify Hash Q M2 S2) returns True when the putative public key Q is used.

We don't have access to the oracle needed in step 1.6.2 of the public key recovery operation.
So here we simply call it the ValidationOracle, which takes a point and returns True or False.

Note that the public key recovery operation loops over j.  In HOL/Isabelle, we translate the loop
as a recursive function ECDSA_PublicKeyRecovery_rec.  The "meat" of each iteration is contained
in the function ECDSA_PublicKeyRecovery_1. ECDSA_PublicKeyRecovery first computes e (because it is
the same in every loop iteration) and kicks off the loop by calling ECDSA_PublicKeyRecovery_rec.

Lastly, we note again that the standard writes \<lceil>(log 2 p)/8\<rceil>.  We know because p is odd
(and thus not a power of two) that octet_length p = \<lceil>(log 2 p)/8\<rceil>.  The proof of this may be found
in Words.thy/octetLenLog2Prime.\<close>

definition ECDSA_PublicKeyRecovery_1 :: 
  "(int point \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> sig_type \<Rightarrow> nat \<Rightarrow> int point option" where 
  "ECDSA_PublicKeyRecovery_1 ValidationOracle e Sig j = 
  ( let r    = fst Sig;
        s    = snd Sig;
        x    = r + j*n;
        mlen = octet_length p;
        X    = nat_to_octets_len x mlen;
        P    = octets_to_point' (2 # X)
    in
     ( case P of
         None    \<Rightarrow> None
       | Some R' \<Rightarrow> 
       ( let nR   = point_mult' n R';
             rInv = inv_mod_n r; 
             eG   = opp (point_mult' e G);
             sR1  = point_mult' s R';
             sR2  = point_mult' s (opp R');
             Q1   = point_mult' rInv (add' sR1 eG);
             Q2   = point_mult' rInv (add' sR2 eG)
         in
             if (nR = Infinity) then
               ( if (ValidationOracle Q1) then (Some Q1) else
                 if (ValidationOracle Q2) then (Some Q2) else None
               ) 
             else None
       )
     )
  )"

text \<open>It is a little more convenient to have a loop counter that decreases until it reaches 0.
So the loop index i here satisfies j = h + 1 - i, where j is the loop counter from step 1 in
the standard. i starts at h+1, which corresponds to j = 0.  When i = 1, j = h, so when i = 0,
there are no more iterations to perform.  If the signature is valid, the public key should be
recovered so that i = 0 is never reached.\<close>
fun ECDSA_PublicKeyRecovery_rec :: 
  "(int point \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> sig_type \<Rightarrow> nat \<Rightarrow> int point option" where
   "ECDSA_PublicKeyRecovery_rec ValidationOracle e Sig 0 = None"
 | "ECDSA_PublicKeyRecovery_rec ValidationOracle e Sig i = 
   ( let P = ECDSA_PublicKeyRecovery_1 ValidationOracle e Sig (h+1-i) in
   ( if   (P = None)
     then (ECDSA_PublicKeyRecovery_rec ValidationOracle e Sig (i-1))
     else P ) )"

definition ECDSA_PublicKeyRecovery_e :: 
  "(int point \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> sig_type \<Rightarrow> int point option" where
  "ECDSA_PublicKeyRecovery_e   ValidationOracle e S = 
   ECDSA_PublicKeyRecovery_rec ValidationOracle e S (h+1)"

definition ECDSA_PublicKeyRecovery :: 
  "hash_type \<Rightarrow> (int point \<Rightarrow> bool) \<Rightarrow> octets \<Rightarrow> sig_type \<Rightarrow> int point option" where
  "ECDSA_PublicKeyRecovery Hash ValidationOracle M S = 
   ECDSA_PublicKeyRecovery_e ValidationOracle (ECDSA_compute_e Hash M) S"

text \<open>Knowing nothing about the hash function or the oracle, at the very least we know that
if the key recovery operation returns a point, then that point is on the elliptic curve.\<close>
lemma ECDSA_PublicKeyRecovery_1_onCurve:
  assumes "ECDSA_PublicKeyRecovery_1 ValidationOracle e Sig j = Some Q"
  shows   "on_curve' Q" 
proof - 
  let ?r    = "fst Sig"
  let ?s    = "snd Sig"
  let ?x    = "?r + j*n"
  let ?mlen = "octet_length p"
  let ?X    = "nat_to_octets_len ?x ?mlen"
  let ?P    = "octets_to_point' (2 # ?X)"
  have 1: "?P \<noteq> None"
    by (metis (no_types, lifting) ECDSA_PublicKeyRecovery_1_def assms option.case(1) 
               option.distinct(1)) 
  obtain R' where 2: "?P = Some R'" using 1 by blast
  have 3: "on_curve' R'"            using 2 octets2PointOnCurve by fast
  let ?rInv = "inv_mod_n ?r" 
  let ?eG   = "opp (point_mult' e G)" 
  let ?sR1  = "point_mult' ?s R'"
  let ?sR2  = "point_mult' ?s (opp R')"
  let ?Q1   = "point_mult' ?rInv (add' ?sR1 ?eG)" 
  let ?Q2   = "point_mult' ?rInv (add' ?sR2 ?eG)"
  have 4: "Q = ?Q1 \<or> Q = ?Q2"  
    by (smt (verit, best) 2 assms ECDSA_PublicKeyRecovery_1_def not_None_eq not_Some_eq 
            option.distinct(1) option.inject option.simps(5)) 
  have 5: "on_curve' ?eG \<and> on_curve' ?sR1 \<and> on_curve' ?sR2" 
    using 3 ECparamsValid ECdomainParametersValid_def opp_closed point_mult_closed by simp
  have 6: "on_curve' ?Q1 \<and> on_curve' ?Q2" 
    using 5 point_mult_closed add_closed by auto
  show ?thesis using 4 6 by fast
qed

lemma ECDSA_PublicKeyRecovery_rec_onCurve:
  assumes "ECDSA_PublicKeyRecovery_rec ValidationOracle e Sig i = Some Q"
  shows   "on_curve' Q" 
  using assms apply (induct i)
  apply simp
  using ECDSA_PublicKeyRecovery_1_onCurve ECDSA_PublicKeyRecovery_rec.simps(2) diff_Suc_1 
  by (smt (verit, best)) 

text \<open>The public key recovery operation is guaranteed to return the correct public key \<open>Q\<^sub>U\<close>,
given a correct validation oracle.  In the next several lemmas, we work toward proving this.

In the ECDSA locale, U has signed a message with its key pair.  So the correct oracle will only
return "true" when the putative public key matches U's public key.\<close>
definition UOracle :: "int point \<Rightarrow> int point \<Rightarrow> bool" where
  "UOracle Q\<^sub>U possibleQ = (Q\<^sub>U = possibleQ)" 

lemma OracleCorrect_1:
  assumes "ECDSA_PublicKeyRecovery_1 (UOracle Q\<^sub>U) e Sig j = Some P"
  shows   "P = Q\<^sub>U"
proof - 
  let ?r    = "fst Sig"
  let ?s    = "snd Sig"
  let ?x    = "?r + j*n"
  let ?mlen = "octet_length p"
  let ?X    = "nat_to_octets_len ?x ?mlen"
  let ?P    = "octets_to_point' (2 # ?X)"
  have 1: "?P \<noteq> None" 
    by (metis (no_types, lifting) ECDSA_PublicKeyRecovery_1_def assms option.case(1) 
               option.distinct(1)) 
  obtain R' where 2: "?P = Some R'" using 1 by blast
  show ?thesis
    by (smt (verit) 2 ECDSA_PublicKeyRecovery_1_def UOracle_def assms option.distinct(1) 
            option.inject option.simps(5)) 
qed

lemma OracleCorrect_rec:
  assumes "ECDSA_PublicKeyRecovery_rec (UOracle Q\<^sub>U) e Sig i = Some P"
  shows   "P = Q\<^sub>U"
  using assms apply (induct i)
  apply simp
  by (smt (verit, del_insts) ECDSA_PublicKeyRecovery_rec.simps(2) OracleCorrect_1 diff_Suc_1)

lemma KeyRecoveryWorks_1: 
  assumes "ECDSA_Sign_e d\<^sub>U e k P = Some S"  "ECkeyPairValid k P"  "P = Point x y" 
          "j = (nat x) div n"  "ECkeyPairValid d\<^sub>U Q\<^sub>U"
  shows   "ECDSA_PublicKeyRecovery_1 (UOracle Q\<^sub>U) e S j = Some Q\<^sub>U" 
proof - 
  have x0: "0 \<le> x \<and> x < p \<and> x \<in> carrier R"
    using ECkeyPairOnCurve assms(2,3) inCarrier onCurveEq2 by blast 
  have j0: "0 \<le> x div n"        using x0 div_int_pos_iff of_nat_0_le_iff by blast 
  have j1: "j = nat (x div n)"  using assms(4) nat_div_distrib nat_int x0 by presburger 
  let ?r = "fst S"
  let ?s = "snd S" 
  have r1: "?r = nat (x mod n)" by (metis ECDSA_Sign_e_SomeOut_r assms(1,3)) 
  have r2: "?r \<in> carrier Rn"    using ECDSA_Sign_e_inRn assms(1) by blast 
  have r3: "0 < ?r"             using ECDSA_Sign_e_inRn assms(1) by blast 
  let ?x = "?r + j*n" 
  let ?kinv = "inv\<^bsub>Rn\<^esub> k"
  have k0: "0 < k"              using assms(2) ECkeyPairValid_def by simp
  have k1: "k \<in> carrier Rn"     using assms(2) ECkeyPair_dInRn by blast 
  have k2: "?kinv \<in> carrier Rn"
    by (metis k1 k0 N.inv_closed N.zero_cong bot_nat_0.not_eq_extremum 
              dual_order.refl of_nat_le_0_iff)
  have k3: "k \<otimes>\<^bsub>Rn\<^esub> ?kinv = \<one>\<^bsub>Rn\<^esub>"   using ECkeyPairValid_def N.zero_cong assms(2) k1 by force 
  let ?c = "(e + ?r*d\<^sub>U) mod n"
  have c1: "?c \<in> carrier Rn"         by (simp add: of_nat_mod)
  have s1: "?s = ?kinv \<otimes>\<^bsub>Rn\<^esub> ?c"     using ECDSA_Sign_e_SomeOut_curve_s assms(1,2,3,5) r1 by blast
  have x1: "?x = x"                  using j0 j1 r1 r3 by auto 
  let ?l = "octet_length p"
  let ?X = "nat_to_octets_len ?x ?l"
  let ?P = "octets_to_point' (2 # ?X)"
  have P1: "on_curve' P"                  using assms(2) ECkeyPairOnCurve by blast
  have P2: "?P = Some P \<or> ?P = Some (opp P)" 
    by (metis P1 assms(3) x1 point2Octets2PointComp_PoppP' nat_int) 
  have P3: "point_mult' n P = Infinity"   using assms(2) by (simp add: ECkeyPairOrd_n) 
  have P4: "P \<in> carrier EPF.curve"        by (simp add: EPF.in_carrier_curve P1) 
  have P5: "opp P = inv\<^bsub>EPF.curve\<^esub> P"     using EPF.inv_curve P4 by presburger
  have P6: "point_mult' n (opp P) = Infinity" 
    by (metis EPF.curve.inv_one EPF.curve.nat_pow_inv EPF.one_curve P1 P3 P4 P5 
              EPF.multEqPowInCurve opp_closed) 
  have P7: "point_mult' k G = P" using assms(2) ECkeyPairValid_def by blast 
  have P8: "G[^]\<^bsub>EPF.curve\<^esub>k = P" 
    using P7 EPF.in_carrier_curve GonEPFcurve EPF.multEqPowInCurve by force  
  obtain R' where R1: "?P = Some R'"                              using P2 by blast
  have R2: "R' = P \<or> R' = opp P"                                  using P2 R1 by auto
  have R3: "(R' = opp P) = (opp R' = P)"                          using P1 R2 opp_opp by auto
  let ?nR   = "point_mult' n R'"
  have nR1: "?nR = point_mult' n P \<or> ?nR = point_mult' n (opp P)" using R2 by fast
  have nR2: "?nR = Infinity"                                      using nR1 P3 P6 by argo
  let ?rInv = "inv_mod_n ?r" 
  have rInv: "?rInv = inv\<^bsub>Rn\<^esub> ?r"
    using ECDSA_Sign_e_inRn assms(1) bot_nat_0.not_eq_extremum inv_mod_n_inv by presburger
  have rInv2: "?r \<otimes>\<^bsub>Rn\<^esub> ?rInv = \<one>\<^bsub>Rn\<^esub>" by (simp add: N.zero_cong r2 r3 rInv)
  let ?eG   = "opp (point_mult' e G)"
  have eG1: "?eG = G[^]\<^bsub>EPF.curve\<^esub>(-(int e))"
    using EPF.curve.int_pow_neg_int EPF.in_carrier_curve EPF.inv_curve GonEPFcurve dGonEPFcurve 
          EPF.multEqPowInCurve by auto 
  have eG2: "?eG = G[^]\<^bsub>EPF.curve\<^esub>(-(int e) mod n)" using eG1 multGmodn'int by presburger
  let ?em = "(-(int e) mod n)"
  have em1: "?em = \<ominus>\<^bsub>Rn\<^esub>e"                          using N.res_neg_eq by presburger
  let ?sR1  = "point_mult' ?s R'"
  let ?sR2  = "point_mult' ?s (opp R')"
  have sR1: "{?sR1, ?sR2} = {point_mult' ?s P, point_mult' ?s (opp P)}"
    using R2 R3 by fastforce 
  have sR2: "{?sR1, ?sR2} = {P[^]\<^bsub>EPF.curve\<^esub>?s, P[^]\<^bsub>EPF.curve\<^esub>(-?s)}"
    by (metis sR1 P1 P4 P5 EPF.curve.int_pow_neg_int EPF.curve.nat_pow_inv opp_closed
              EPF.multEqPowInCurve) 
  have sR3: "(R' = opp P) \<Longrightarrow> (?sR1 = P[^]\<^bsub>EPF.curve\<^esub>(-?s) \<and> ?sR2 = P[^]\<^bsub>EPF.curve\<^esub>?s)"
    by (metis P1 doubleton_eq_iff EPF.multEqPowInCurve sR2 opp_opp)
  let ?Q1   = "point_mult' ?rInv (add' ?sR1 ?eG)"
  let ?Q2   = "point_mult' ?rInv (add' ?sR2 ?eG)"
  let ?Q = "((P[^]\<^bsub>EPF.curve\<^esub>?s) \<otimes>\<^bsub>EPF.curve\<^esub> (G [^]\<^bsub>EPF.curve\<^esub>?em))[^]\<^bsub>EPF.curve\<^esub>?rInv"
  have Q1: "(R' = P) \<Longrightarrow> ?Q1 = ?Q"
    using P4 eG2 EPF.add_curve GonEPFcurve EPF.curve.int_pow_closed EPF.curve.m_closed 
          EPF.curve.nat_pow_closed EPF.in_carrier_curve EPF.multEqPowInCurve by auto
  have Q2: "(R' = opp P) \<Longrightarrow> ?Q2 = ?Q"
    using P4 sR3 eG2 GonEPFcurve EPF.add_curve EPF.curve.int_pow_closed EPF.curve.m_closed 
          EPF.curve.nat_pow_closed EPF.in_carrier_curve EPF.multEqPowInCurve by auto
  have Q3: "P[^]\<^bsub>EPF.curve\<^esub>?s = G[^]\<^bsub>EPF.curve\<^esub>(k*?s)" 
    using P8 EPF.curve.nat_pow_pow GonEPFcurve by blast 
  have Q4: "(G[^]\<^bsub>EPF.curve\<^esub>(k*?s) \<otimes>\<^bsub>EPF.curve\<^esub> (G [^]\<^bsub>EPF.curve\<^esub>?em)) = 
             G[^]\<^bsub>EPF.curve\<^esub>(k*?s+?em)"
    by (metis EPF.curve.is_group GonEPFcurve group.int_pow_mult int_pow_int) 
  have Q5: "?Q = G[^]\<^bsub>EPF.curve\<^esub>((k*?s+?em)*?rInv)" 
    by (metis Q3 Q4 EPF.curve.int_pow_pow GonEPFcurve int_pow_int)
  have Q6: "?Q = G[^]\<^bsub>EPF.curve\<^esub>((k*?s+?em)*?rInv mod n)" 
    using Q5 multGmodn'int by algebra
  have ex1: "(k*?s+?em)*?rInv mod n = (k\<otimes>\<^bsub>Rn\<^esub>?s \<oplus>\<^bsub>Rn\<^esub> ?em)\<otimes>\<^bsub>Rn\<^esub>?rInv"
    by (simp add: N.res_add_eq N.res_mult_eq mod_add_left_eq mod_mult_right_eq mult.commute) 
  have ex2: "(k*?s+?em)*?rInv mod n = (k\<otimes>\<^bsub>Rn\<^esub>(?kinv \<otimes>\<^bsub>Rn\<^esub> ?c) \<ominus>\<^bsub>Rn\<^esub>e)\<otimes>\<^bsub>Rn\<^esub>(inv\<^bsub>Rn\<^esub> ?r)"
    using ex1 s1 em1 rInv by algebra
  have ex3: "k\<otimes>\<^bsub>Rn\<^esub>(?kinv \<otimes>\<^bsub>Rn\<^esub> ?c)  = k\<otimes>\<^bsub>Rn\<^esub>?kinv \<otimes>\<^bsub>Rn\<^esub> ?c"
    using m_assoc k1 k2 c1 by algebra
  have ex4: "k\<otimes>\<^bsub>Rn\<^esub>(?kinv \<otimes>\<^bsub>Rn\<^esub> ?c)  = ?c" 
    using ex3 k3 N.l_one c1 by presburger 
  have ex5: "?c \<ominus>\<^bsub>Rn\<^esub>e = e \<oplus>\<^bsub>Rn\<^esub> (?r\<otimes>\<^bsub>Rn\<^esub>d\<^sub>U) \<ominus>\<^bsub>Rn\<^esub>e"
    by (simp add: N.res_add_eq N.res_mult_eq mod_add_right_eq of_nat_mod) 
  have ex6: "?c \<ominus>\<^bsub>Rn\<^esub>e = ?r\<otimes>\<^bsub>Rn\<^esub>d\<^sub>U" 
    using ex5 by (simp add: N.res_add_eq N.res_diff_eq N.res_mult_eq mod_diff_left_eq)
  have ex7: "(k*?s+?em)*?rInv mod n = ?r\<otimes>\<^bsub>Rn\<^esub>d\<^sub>U\<otimes>\<^bsub>Rn\<^esub>?rInv"
    using ex2 ex4 ex6 rInv by argo
  have ex8: "(k*?s+?em)*?rInv mod n = d\<^sub>U mod n" 
    by (metis (mono_tags, opaque_lifting) ex7 rInv2 N.res_mult_eq N.res_one_eq mod_mult_right_eq
               mult.left_commute mult.right_neutral of_nat_mod semiring_1_class.of_nat_mult)
  have ex9: "(k*?s+?em)*?rInv mod n = d\<^sub>U"     using ex8 assms(5) ECkeyPairValid_def by force
  have Q7:  "?Q = G[^]\<^bsub>EPF.curve\<^esub>d\<^sub>U"          by (metis Q6 ex9 int_pow_int) 
  have Q8:  "?Q = Q\<^sub>U"                         using Q7 ECkeyPair_curveMult assms(5) by presburger 
  have A1:  "(R' = P)     \<Longrightarrow> ?Q1 = Q\<^sub>U"       using Q8 Q1 by argo
  have A11: "(R' = P)     \<Longrightarrow> UOracle Q\<^sub>U ?Q1" using A1 UOracle_def by blast
  have A12: "(R' = P)     \<Longrightarrow> ECDSA_PublicKeyRecovery_1 (UOracle Q\<^sub>U) e S j = Some Q\<^sub>U"
    using A11 ECDSA_PublicKeyRecovery_1_def P2 nR2 A1 R1 by auto 
  have A2:  "(R' = opp P) \<Longrightarrow> ?Q2 = Q\<^sub>U"       using Q8 Q2 by argo
  have A21: "(R' = opp P) \<Longrightarrow> UOracle Q\<^sub>U ?Q2" using A2 UOracle_def by blast
  have A22: "(R' = opp P) \<Longrightarrow> ECDSA_PublicKeyRecovery_1 (UOracle Q\<^sub>U) e S j = Some Q\<^sub>U"
    by (smt (verit) nR2 A21 R1 UOracle_def ECDSA_PublicKeyRecovery_1_def option.simps(5)) 
  show ?thesis using A12 A22 R2 by fast
qed

lemma KeyRecoveryWorks_1': 
  assumes "ECDSA_Sign Hash d\<^sub>U M k P = Some S"  "ECkeyPairValid k P"  "P = Point x y"  
          "j = (nat x) div n"  "ECkeyPairValid d\<^sub>U Q\<^sub>U"  "e = ECDSA_compute_e Hash M"
  shows   "ECDSA_PublicKeyRecovery_1 (UOracle Q\<^sub>U) e S j = Some Q\<^sub>U" 
  using KeyRecoveryWorks_1 assms ECDSA_Sign_e_def by algebra

lemma KeyRecoveryWorks_rec_h1: 
  assumes "ECDSA_Sign_e d\<^sub>U e k P = Some S"  "ECkeyPairValid k P"  "P = Point x y" 
          "j = (nat x) div n"  "ECkeyPairValid d\<^sub>U Q\<^sub>U"
  shows   "ECDSA_PublicKeyRecovery_rec (UOracle Q\<^sub>U) e S (h+1-j) = Some Q\<^sub>U" 
proof -
  have 1: "x \<in> carrier R"
    using assms(2,3) ECkeyPairOnCurve onCurveEq2 by blast 
  have 2: "j \<le> h" 
    by (metis 1 assms(4) less_p_div_n' ECparamsValid inCarrierNatInt)
  have 3: "h+1-(h+1-j) = j" 
    using 2 by fastforce 
  have 4: "ECDSA_PublicKeyRecovery_1 (UOracle Q\<^sub>U) e S j = Some Q\<^sub>U"
    using KeyRecoveryWorks_1 assms(1,2,3,4,5) by blast
  show ?thesis 
    by (smt (verit, ccfv_SIG) 2 3 4 ECDSA_PublicKeyRecovery_rec.simps(2) Suc_diff_le 
             Suc_eq_plus1 option.distinct(1)) 
qed

lemma KeyRecoveryWorks_rec_h1': 
  assumes "ECDSA_Sign Hash d\<^sub>U M k P = Some S"  "ECkeyPairValid k P"  "P = Point x y" 
          "j = (nat x) div n"  "ECkeyPairValid d\<^sub>U Q\<^sub>U"  "e = ECDSA_compute_e Hash M"
  shows   "ECDSA_PublicKeyRecovery_rec (UOracle Q\<^sub>U) e S (h+1-j) = Some Q\<^sub>U" 
  using KeyRecoveryWorks_rec_h1 assms ECDSA_Sign_e_def by algebra

lemma KeyRecoveryWorks_rec_h2: 
  assumes "ECDSA_Sign_e d\<^sub>U e k P = Some S"  "ECkeyPairValid k P"  "P = Point x y"  
          "j = (nat x) div n"  "h+1-j \<le> L"  "ECkeyPairValid d\<^sub>U Q\<^sub>U"
  shows   "ECDSA_PublicKeyRecovery_rec (UOracle Q\<^sub>U) e S L = Some Q\<^sub>U" 
  using assms proof (induct L)
  case 0
  then show ?case by (metis KeyRecoveryWorks_rec_h1 bot_nat_0.extremum_uniqueI) 
next
  case (Suc L)
  then show ?case proof (cases "ECDSA_PublicKeyRecovery_1 (UOracle Q\<^sub>U) e S (h+1-(Suc L)) = None")
    case True
    then have "ECDSA_PublicKeyRecovery_rec (UOracle Q\<^sub>U) e S (Suc L) = 
               ECDSA_PublicKeyRecovery_rec (UOracle Q\<^sub>U) e S L" 
      using ECDSA_PublicKeyRecovery_rec.simps(2) diff_Suc_1 by presburger 
    then show ?thesis
      by (metis KeyRecoveryWorks_rec_h1 Suc.hyps Suc.prems(1,5,6) assms(2,3,4)
                le_eq_less_or_eq less_Suc_eq_le)
  next
    case F0: False
    have F1: "ECDSA_PublicKeyRecovery_rec (UOracle Q\<^sub>U) e S (Suc L) = 
                ECDSA_PublicKeyRecovery_1 (UOracle Q\<^sub>U) e S (h+1-(Suc L))"
      using ECDSA_PublicKeyRecovery_rec.simps(2) F0 by presburger
    have F2: "ECDSA_PublicKeyRecovery_1 (UOracle Q\<^sub>U) e S (h+1-(Suc L)) = Some Q\<^sub>U" 
      using F0 OracleCorrect_1 by blast
    then show ?thesis using F1 F2 by presburger
  qed
qed

lemma KeyRecoveryWorks_rec_h2': 
  assumes "ECDSA_Sign Hash d\<^sub>U M k P = Some S"  "ECkeyPairValid k P"  "P = Point x y" 
          "j = (nat x) div n"  "h+1-j \<le> L"  "ECkeyPairValid d\<^sub>U Q\<^sub>U"  "e = ECDSA_compute_e Hash M"
  shows   "ECDSA_PublicKeyRecovery_rec (UOracle Q\<^sub>U) e S L = Some Q\<^sub>U" 
  using KeyRecoveryWorks_rec_h2 assms ECDSA_Sign_e_def by algebra

lemma KeyRecoveryWorks_rec: 
  assumes "ECDSA_Sign_e d\<^sub>U e k P = Some S"  "ECkeyPairValid k P"  "ECkeyPairValid d\<^sub>U Q\<^sub>U"
  shows   "ECDSA_PublicKeyRecovery_rec (UOracle Q\<^sub>U) e S (h+1) = Some Q\<^sub>U"
  by (metis assms(1,2,3) ECDSA_Sign_e_Some KeyRecoveryWorks_rec_h2 diff_le_self point.exhaust) 

lemma KeyRecoveryWorks_rec': 
  assumes "ECDSA_Sign Hash d\<^sub>U M k P = Some S"  "ECkeyPairValid k P"  "ECkeyPairValid d\<^sub>U Q\<^sub>U"
          "e = ECDSA_compute_e Hash M" 
  shows   "ECDSA_PublicKeyRecovery_rec (UOracle Q\<^sub>U) e S (h+1) = Some Q\<^sub>U"
  using KeyRecoveryWorks_rec assms ECDSA_Sign_e_def by algebra

text \<open>Here finally is the lemma that we have been working toward.  The entity U has signed the
message M with the ephemeral key pair (k,P).  Given a correct oracle for \<open>Q\<^sub>U\<close>, the key recovery
operation will recover \<open>Q\<^sub>U\<close> given the message M and the signature S.  Again, what could the 
oracle be?  Typically, the person trying to recover \<open>Q\<^sub>U\<close> will have at least 2 messages signed by
U.  They can run the key recovery operation with one (message, signature) pair and use a second
(message, key) pair to to check any putative \<open>Q\<^sub>U\<close> that the key recovery operation presents.\<close>
lemma KeyRecoveryWorks:
  assumes "ECDSA_Sign_e d\<^sub>U e k P = Some S"  "ECkeyPairValid k P"  "ECkeyPairValid d\<^sub>U Q\<^sub>U"
  shows   "ECDSA_PublicKeyRecovery_e (UOracle Q\<^sub>U) e S = Some Q\<^sub>U"
  using ECDSA_PublicKeyRecovery_e_def KeyRecoveryWorks_rec assms(1,2,3) by presburger 

lemma KeyRecoveryWorks':
  assumes "ECDSA_Sign Hash d\<^sub>U M k P = Some S"  "ECkeyPairValid k P"  "ECkeyPairValid d\<^sub>U Q\<^sub>U"
  shows   "ECDSA_PublicKeyRecovery Hash (UOracle Q\<^sub>U) M S = Some Q\<^sub>U"
  using ECDSA_PublicKeyRecovery_def ECDSA_Sign_e_def KeyRecoveryWorks assms by presburger


subsubsection \<open>4.1.7 Self-Signing Operation\<close>

text \<open>The statement of the self-signing operation in the standard is vague in two ways and 
overly complex in another.

First, it takes as input "information", labeled I.  The format of this "information" is not 
specified.  It is  only said that I "should include the identity of the signer", without indicating
what "identity" means.  

Second, step 4 in the standard says "Form a message M containing both I and (r,s)."  It does not
indicate how such a message should be formed.  Isabelle is a typed language so we need to specify
the type of I.  We specify the type of I as 'a, which is the generic term for "some type".  And we
assume the existence of a "form a message" function that takes "information" type and a signature
type and produces octets.

Note that the standard lists as input the curve parameters and the "information" I.  But also 
needed as input are an ephemeral key, which we label (k, P), and a random integer s in the range
[1,n-1].  As noted above, we cannot use (k, R) to represent the ephemeral key because R is already
used in this theory to refer to the integer ring R of integers modulo p.

Finally, let's examine step 5 in the standard.  It says to "Use the Public Key Recovery Operation"
to recover a public key Q.  In that operation, we know only (x mod n), where x is the first 
coordinate of the ephemeral key point P.  So we must loop over all possible x and try to 
reconstruct P.  In the self-signing operation, we know the ephemeral key is (k,P).  No need to
loop to recover P.  Then we get the public key is Q = r^(-1)*(s*P - e*G).  Because (k,P) is a 
valid key pair, we know that P = k*G, so Q = r^(-1)(s*k - e)*G.  But we already know this if
we look at step 6 in the standard which tells us that the private key is d = r^(-1)(s*k - e).
If (d,Q) is to be a valid key pair, we must have Q = d*G.  In summary, there is no need to 
actually use the public key recovery operation.  We can simply defined d as shown in step 6
and set Q = d*G.

Special note for computing d: As mentioned above, Isabelle/HOL is a typed language.  We need
to make sure that the difference computed for d is done on integers, in case that s*k < e.\<close>

text \<open>These are the conditions in the standard for the user of the self-signing operation.  They
must pick a valid ephemeral key (k,P) and a value s in [1, n-1].\<close>
definition ECDSA_SelfSign_validIn' :: "nat \<Rightarrow> int point \<Rightarrow> nat \<Rightarrow> bool" where
  "ECDSA_SelfSign_validIn' k P s = (ECkeyPairValid k P \<and> 0 < s \<and> s < n)"

text \<open>These are the conditions that guarantee that the self-signing operation will produce
some output.\<close>
definition ECDSA_SelfSign_validIn :: 
  "hash_type \<Rightarrow> ('a \<Rightarrow> sig_type \<Rightarrow> octets) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> int point \<Rightarrow> nat \<Rightarrow> bool" 
  where
  "ECDSA_SelfSign_validIn Hash FormMessage I k P s = 
   ( case P of
       Infinity  \<Rightarrow> False
     | Point x y \<Rightarrow> 
      ( let r    = nat (x mod n);
            M    = FormMessage I (r,s);
            e    = ECDSA_compute_e Hash M;
            rInv = inv_mod_n r;
            d    = nat ((rInv*(s*(int k) - (int e)) ) mod n)
        in
           0 < r \<and> 0 < d 
      )
   )"

definition ECDSA_SelfSign :: 
  "hash_type \<Rightarrow> ('a \<Rightarrow> sig_type \<Rightarrow> octets) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> int point \<Rightarrow> nat 
   \<Rightarrow> (nat \<times> int point \<times> octets) option" 
  where
  "ECDSA_SelfSign Hash FormMessage I k P s = 
   ( case P of
       Infinity  \<Rightarrow> None
     | Point x y \<Rightarrow> 
      ( let r    = nat (x mod n);
            M    = FormMessage I (r,s);
            e    = ECDSA_compute_e Hash M;
            rInv = inv_mod_n r;
            d    = nat ((rInv*(s*(int k) - (int e)) ) mod n);
            Q    = point_mult' d G
        in
          ( if (r=0) then None else
          ( if (d=0) then None else Some (d, Q, M) ))
      )
   )"

lemma ECDSA_SelfSign_ValidIn:
  assumes "ECDSA_SelfSign_validIn Hash FormMessage I k P s"
  shows   "\<exists>d Q M. ECDSA_SelfSign Hash FormMessage I k P s = Some (d, Q, M)"
proof -
  have 1: "P \<noteq> Infinity" using assms ECDSA_SelfSign_validIn_def by force
  obtain x and y where 2: "P = Point x y" by (meson 1 point.exhaust) 
  let ?r    = "nat (x mod n)"
  let ?M    = "FormMessage I (?r,s)"
  let ?e    = "ECDSA_compute_e Hash ?M"
  let ?rInv = "inv_mod_n ?r"
  let ?d    = "nat ((?rInv*(s*(int k) - (int ?e)) ) mod n)"
  have 3: "0 < ?r" by (smt (verit) assms 1 2 ECDSA_SelfSign_validIn_def point.simps(5)) 
  have 4: "0 < ?d" by (smt (verit) assms 1 2 ECDSA_SelfSign_validIn_def point.simps(5))
  have 5: "?r \<noteq> 0" using 3 by fast
  have 6: "?d \<noteq> 0" using 4 by fast
  show ?thesis     using 1 2 5 6 ECDSA_SelfSign_def option.discI point.simps(5) by (smt (z3))
qed

lemma ECDSA_SelfSign_PnotInf:
  assumes "ECDSA_SelfSign Hash FormMessage I k P s = Some (d, Q, M)" 
  shows   "P \<noteq> Infinity"
  by (metis (no_types, lifting) assms(1) ECDSA_SelfSign_def option.discI point.simps(4)) 

lemma ECDSA_SelfSign_Some:
  fixes x :: int
  assumes "ECDSA_SelfSign Hash FormMessage I k P s = Some (d, Q, M)" 
          "P = Point x y"  "r = nat (x mod n)"  "M' = FormMessage I (r,s)"
          "e = ECDSA_compute_e Hash M'"  "rInv = inv_mod_n r"
          "d' = nat ((rInv*(s*(int k) - (int e)) ) mod n)"  "Q' = point_mult' d' G"
  shows   "d = d' \<and> Q = Q' \<and> M = M' \<and> r \<noteq>0 \<and> d \<noteq> 0"
  by (smt (verit, del_insts) assms ECDSA_SelfSign_def option.simps(1,3) point.case(2) 
          prod.sel(1,2)) 

lemma ECDSA_SelfSign_SomeValid:
  assumes "ECDSA_SelfSign Hash FormMessage I k P s = Some (d, Q, M)" 
  shows   "ECDSA_SelfSign_validIn Hash FormMessage I k P s"
proof - 
  have 1: "P \<noteq> Infinity"                             by (metis ECDSA_SelfSign_PnotInf assms) 
  obtain x and y where 2: "P = Point x y"             by (meson 1 point.exhaust) 
  let ?r    = "nat (x mod n)"
  let ?M    = "FormMessage I (?r,s)"
  let ?e    = "ECDSA_compute_e Hash ?M"
  let ?rInv = "inv_mod_n ?r"
  let ?d    = "nat ((?rInv*(s*(int k) - (int ?e)) ) mod n)"
  let ?Q    = "point_mult' ?d G"
  have 3: "d = ?d \<and> Q = ?Q \<and> M = ?M \<and> ?r \<noteq>0 \<and> d \<noteq> 0"  by (metis 2 ECDSA_SelfSign_Some assms) 
  have 4: "0 < ?r \<and> 0 < ?d"                             using 3 by force
  show ?thesis   using 1 2 4 ECDSA_SelfSign_validIn_def by fastforce
qed

text \<open>The output (d,Q) of the self-signing operation is a valid key pair.\<close>
lemma ECDSA_SelfSign_ValidKeyPair:
  assumes "ECDSA_SelfSign Hash FormMessage I k P s = Some (d, Q, M)" 
  shows   "ECkeyPairValid d Q" 
proof - 
  have 1: "P \<noteq> Infinity"                             by (metis ECDSA_SelfSign_PnotInf assms) 
  obtain x and y where 2: "P = Point x y"             by (meson 1 point.exhaust) 
  let ?r    = "nat (x mod n)"
  let ?M    = "FormMessage I (?r,s)"
  let ?e    = "ECDSA_compute_e Hash ?M"
  let ?rInv = "inv_mod_n ?r"
  let ?d    = "nat ((?rInv*(s*(int k) - (int ?e)) ) mod n)"
  let ?Q    = "point_mult' ?d G"
  have 3: "d = ?d \<and> Q = ?Q \<and> M = ?M \<and> ?r \<noteq>0 \<and> d \<noteq> 0" 
    by (metis 2 ECDSA_SelfSign_Some assms) 
  have 4: "d < n"
    by (metis 3 Euclidean_Rings.pos_mod_bound N.residues_prime_axioms nat_int prime_gt_1_nat
              residues_prime.p_prime zless_nat_conj) 
  show ?thesis using 3 4 ECkeyPairValid_def by blast
qed

text \<open>Here is the main result about the self-signing operation.  Namely, if you follow the
self-signing operation and get (d, Q, M), then the message M is formed from the information I and
(r,s) and when M is signed using (d,Q) as the signer's key pair (together with the ephemeral key
(k,P), then the resulting signature is (r,s).\<close>
lemma ECDSA_SelfSign_SignWorks:
  assumes "ECDSA_SelfSign Hash FormMessage I k P s = Some (d, Q, M)" 
          "P = Point x y"  "r = nat (x mod n)"  "ECkeyPairValid k P"  "s<n"  "0<s"
  shows   "M = FormMessage I (r,s) \<and> ECDSA_Sign Hash d M k P = Some (r,s)"
proof - 
  let ?M    = "FormMessage I (r,s)"
  let ?e    = "ECDSA_compute_e Hash M"
  let ?rInv = "inv_mod_n r"
  let ?d    = "nat ((?rInv*(s*(int k) - (int ?e)) ) mod n)"
  let ?Q    = "point_mult' d G"
  have 1:  "d = ?d \<and> Q = ?Q \<and> M = ?M \<and> r \<noteq>0 \<and> d \<noteq> 0" by (metis ECDSA_SelfSign_Some assms(1,2,3)) 
  have r1: "r \<in> carrier Rn"      by (metis 1 N.mod_in_carrier assms(3) nat_eq_iff2) 
  have r2: "?rInv = inv\<^bsub>Rn\<^esub> r"   using 1 r1 inv_mod_n_inv by presburger
  have d1: "?d = inv\<^bsub>Rn\<^esub>r \<otimes>\<^bsub>Rn\<^esub> (s \<otimes>\<^bsub>Rn\<^esub> k \<ominus>\<^bsub>Rn\<^esub> ?e)"
    by (metis 1 r2 N.res_diff_eq N.res_mult_eq int_nat_eq int_ops(1) mod_diff_left_eq 
              mod_mult_right_eq nat_int)
  let ?kinv = "inv_mod_n k"
  have k1: "0 < k \<and> k < n"       using assms(4) ECkeyPairValid_def by blast
  have k2: "?kinv = inv\<^bsub>Rn\<^esub> k"   using inv_mod_n_inv' k1 by presburger  
  have k3: "k \<in> carrier Rn"      using k1 ECkeyPair_dInRn' ECprivateKeyValid_def by blast 
  let ?s    = "(?kinv*(?e + r*?d)) mod n"
  have s1: "?s = inv\<^bsub>Rn\<^esub> k \<otimes>\<^bsub>Rn\<^esub> (?e \<oplus>\<^bsub>Rn\<^esub> r \<otimes>\<^bsub>Rn\<^esub> ?d)"
    by (simp add: k2 N.res_add_eq N.res_mult_eq mod_add_right_eq mod_mult_right_eq of_nat_mod)
  have d2: "r \<otimes>\<^bsub>Rn\<^esub> ?d = s \<otimes>\<^bsub>Rn\<^esub> k \<ominus>\<^bsub>Rn\<^esub> ?e" 
    by (metis 1 r1 d1 EPF.nat_int_eq N.inv_closed N.l_one N.m_assoc N.mod_in_carrier N.r_inv
              N.res_diff_eq N.zero_cong int_ops(1)) 
  have s2: "(?e \<oplus>\<^bsub>Rn\<^esub> r \<otimes>\<^bsub>Rn\<^esub> ?d) = s \<otimes>\<^bsub>Rn\<^esub> k" 
    using d2 by (simp add: N.res_add_eq N.res_diff_eq N.res_mult_eq mod_add_right_eq) 
  have s3: "?s = inv\<^bsub>Rn\<^esub> k \<otimes>\<^bsub>Rn\<^esub> (s \<otimes>\<^bsub>Rn\<^esub> k)" using s1 s2 by argo
  have s4: "?s = inv\<^bsub>Rn\<^esub> k \<otimes>\<^bsub>Rn\<^esub> k \<otimes>\<^bsub>Rn\<^esub> s"   using s3
    by (simp add: N.res_mult_eq mod_mult_right_eq mult.commute mult.left_commute) 
  have s5: "?s = s"   
    by (metis s4 k3 assms(4,5,6) ECkeyPair_dInRn' ECkeyPair_invRn ECprivateKeyValid_def 
              N.l_one N.m_comm nat_int) 
  show ?thesis
    by (smt (verit) 1 s5 ECDSA_Sign_e_def assms(2,3,6) bot_nat_0.not_eq_extremum point.simps(5))  
qed

text \<open>This is a restatement of the lemma above where we use "ECDSA_SelfSign_validIn k P s", 
which again means that (k,P) is a valid key pair and s is in [1,n-1].\<close>
lemma ECDSA_SelfSign_SignWorks':
  assumes "ECDSA_SelfSign Hash FormMessage I k P s = Some (d, Q, M)" 
          "P = Point x y"  "r = nat (x mod n)"  "ECDSA_SelfSign_validIn' k P s"
  shows   "M = FormMessage I (r,s) \<and> ECDSA_Sign Hash d M k P = Some (r,s)"
  using ECDSA_SelfSign_SignWorks assms ECDSA_SelfSign_validIn'_def by fastforce


end (* SEC1 locale *)


section \<open>5 Encryption and Key Transport Schemes\<close>

text \<open>"This section specifies the public-key encryption and key transport schemes based on 
ECC supported in this document.

Public-key encryption schemes are designed to be used by two entities - a sender U and a recipient
V - when U wants to send a message M to V confidentially, and V wants to recover M.

Key transport schemes are a special class of public-key encryption schemes where the message M
is restricted to be a cryptographic key, usually a symmetric key. Except for this restriction, most
of the discussion below about public-key encryption schemes also applies to key transport schemes.
Here, public-key encryption schemes are described in terms of an encryption operation, a decryption
operation, and associated setup and key deployment procedures. Entities U and V should use the
scheme as follows when they want to communicate. First U and V should use the setup procedure
to establish which options to use the scheme with, then V should use the key deployment procedure
to select a key pair and U should obtain V's public key - U will use V's public key to control
the encryption procedure, and V will use its key pair to control the decryption operation. Then
each time U wants to send a message M to V, U should apply the encryption operation to M under
V's public key to compute an encryption or ciphertext C of M , and convey C to V . Finally when
V receives C, entity V should apply the decryption operation to C under its key pair to recover
the message M.

Loosely speaking, public-key encryption schemes are designed so that it is hard for an adversary
who does not possess V 's secret key to recover messages from their ciphertexts. Thereby, 
public-key encryption schemes provide data confidentiality."\<close>

subsection \<open>5.1 Elliptic Curve Integrated Encryption Scheme\<close>

locale ECIES = SEC1 +
  fixes KDF                 :: kdf_type
    and KDF_VI              :: kdf_validin_type
    and MAC                 :: mac_type
    and MAC_VI              :: mac_validin_type
    and mackeylen maclen    :: nat
    and ENC                 :: enc_type
    and ENC_VI              :: enc_validin_type
    and DEC                 :: dec_type
    and DEC_VI              :: dec_validin_type
    and enckeylen           :: nat
    and useCoDH useCompress :: bool
    and d\<^sub>V                  :: nat
    and Q\<^sub>V                  :: "int point" 
assumes VkeyPairValid : "ECkeyPairValid d\<^sub>V Q\<^sub>V" 
    and ENC_valid     : "\<forall>K M. ENC_VI K M \<longrightarrow> DEC K (ENC K M) = M"
begin

subsubsection \<open>5.1.3 Encryption Operation\<close>

text\<open>Note for Step 6: This definition doesn't cover the case when ENC = XOR and backward 
compatibility mode is not selected.\<close>
definition ECIES_Encryption :: 
  "octets \<Rightarrow> octets \<Rightarrow> octets \<Rightarrow> nat \<Rightarrow> int point \<Rightarrow> (octets \<times> octets \<times> octets) option" where
  "ECIES_Encryption M SharedInfo1 SharedInfo2 k P = 
  ( case (ECDHprimChoose useCoDH k Q\<^sub>V) of 
      None   \<Rightarrow> None
    | Some z \<Rightarrow> 
      ( let Pbar = point_to_octets P useCompress;
            mlen = octet_length p;
            Z    = nat_to_octets_len (nat z) mlen;
            K    = KDF Z (enckeylen + mackeylen) SharedInfo1;
            EK   = take enckeylen K;
            MK   = drop enckeylen K;
            EM   = ENC EK M;
            D    = MAC MK (EM @ SharedInfo2)
           in
               Some (Pbar, EM, D)
      )
  )"

definition ECIES_Encryption_validIn :: 
  "octets \<Rightarrow> octets \<Rightarrow> octets \<Rightarrow> nat \<Rightarrow> int point \<Rightarrow> bool" where
  "ECIES_Encryption_validIn M SharedInfo1 SharedInfo2 k P = 
  ( case (ECDHprimChoose useCoDH k Q\<^sub>V) of 
      None   \<Rightarrow> False
    | Some z \<Rightarrow> 
      ( let mlen = octet_length p;
            Z    = nat_to_octets_len (nat z) mlen;
            K    = KDF Z (enckeylen + mackeylen) SharedInfo1;
            EK   = take enckeylen K;
            MK   = drop enckeylen K;
            EM   = ENC EK M
            in
              (ECkeyPairValid k P) \<and>  (ENC_VI EK M) \<and> 
              (KDF_VI Z (enckeylen + mackeylen) SharedInfo1) \<and> (MAC_VI MK (EM @ SharedInfo2))
      ) 
  )" 

lemma ECIES_Encryption_validIn_someOut:
  assumes "ECIES_Encryption_validIn M SharedInfo1 SharedInfo2 k P"
  shows   "ECIES_Encryption M SharedInfo1 SharedInfo2 k P \<noteq> None" 
  by (smt (z3) assms ECIES_Encryption_validIn_def ECIES_Encryption_def case_optionE option.discI 
          option.simps(5)) 

lemma ECIES_Encryption_validIn_someZ:
  assumes "ECIES_Encryption_validIn M SharedInfo1 SharedInfo2 k P"
  shows   "\<exists>z. ECDHprimChoose useCoDH k Q\<^sub>V = Some z"
  using assms ECIES_Encryption_validIn_def case_optionE by blast 

lemma ECIES_Encryption_someZout:
  assumes "ECDHprimChoose useCoDH k Q\<^sub>V = Some z"
  shows   "\<exists>Pbar EM D. ECIES_Encryption M SharedInfo1 SharedInfo2 k P = Some (Pbar, EM, D)"
  by (metis (no_types, lifting) assms ECIES_Encryption_def option.simps(5))

lemma ECIES_Encryption_SomeOutEq:
  assumes "ECDHprimChoose useCoDH k Q\<^sub>V = Some z" 
          "Pbar = point_to_octets P useCompress"
          "mlen = octet_length p" 
          "Z = nat_to_octets_len (nat z) mlen" 
          "K = KDF Z (enckeylen + mackeylen) SharedInfo1"
          "EK = take enckeylen K" 
          "MK = drop enckeylen K" 
          "EM = ENC EK M"
          "D = MAC MK (EM @ SharedInfo2)"
   shows  "ECIES_Encryption M SharedInfo1 SharedInfo2 k P = Some (Pbar, EM, D)"
  by (metis (mono_tags, lifting) assms ECIES_Encryption_def option.simps(5)) 

subsubsection \<open>5.1.4 Decryption Operation\<close>

definition ECIES_Decryption ::
  "(octets \<times> octets \<times> octets) \<Rightarrow> octets \<Rightarrow> octets \<Rightarrow> octets option" where
  "ECIES_Decryption C SharedInfo1 SharedInfo2 = 
  ( let Pbar = fst C;
        EM   = fst (snd C);
        D    = snd (snd C)
    in
        ( case (octets_to_point' Pbar) of
          None    \<Rightarrow> None
        | Some P  \<Rightarrow>
          ( let T = (if useCoDH then (ECpublicKeyPartialValid P) 
                                else (ECpublicKeyValid        P) )
            in
              ( case (ECDHprimChoose useCoDH d\<^sub>V P) of
                  None    \<Rightarrow> None
                | Some z  \<Rightarrow> 
                  ( let mlen = octet_length p;
                        Z    = nat_to_octets_len (nat z) mlen;
                        K    = KDF Z (enckeylen + mackeylen) SharedInfo1;
                        EK   = take enckeylen K;
                        MK   = drop enckeylen K;
                        D'   = MAC MK (EM @ SharedInfo2);
                        M    = DEC EK EM
                    in
                        if (T \<and> D = D') then (Some M) else None
                  )
              )
          )
        )
  )"

text \<open>This is the main thing we would like to know.  If you encrypt a message with 
ECIES_Encryption, then you can get back that message with ECIES_Decryption.\<close>
lemma ECIES_Decryption_validIn:
  assumes "ECIES_Encryption_validIn M SharedInfo1 SharedInfo2 k P"
          "ECIES_Encryption M SharedInfo1 SharedInfo2 k P = Some (Pbar, EM, D)"
  shows   "ECIES_Decryption (Pbar, EM, D) SharedInfo1 SharedInfo2 = Some M"
proof -
  obtain z where z1: "ECDHprimChoose useCoDH k Q\<^sub>V = Some z"
    using ECIES_Encryption_validIn_someZ assms(1) by blast
  let ?mlen = "octet_length p" 
  let ?Z    = "nat_to_octets_len (nat z) ?mlen" 
  let ?K    = "KDF ?Z (enckeylen + mackeylen) SharedInfo1"
  let ?EK   = "take enckeylen ?K" 
  let ?MK   = "drop enckeylen ?K" 
  have P1: "Pbar = point_to_octets P useCompress" 
    by (metis (mono_tags, lifting) assms(2) z1 ECIES_Encryption_SomeOutEq  
              option.simps(1) prod.sel(1)) 
  have P2: "ECkeyPairValid k P" 
    by (metis (no_types, lifting) assms(1) z1 ECIES_Encryption_validIn_def option.simps(5)) 
  have P3: "on_curve' P"                    using P2 ECkeyPairOnCurve by blast
  have P4: "octets_to_point' Pbar = Some P" using P1 P3 point2Octets2Point by fast
  have P5: "ECpublicKeyValid P \<and> ECpublicKeyPartialValid P"
    using P2 keyPairValidImpliespublicKeyValid validImpliesPartialValid by blast 
  let ?T = "(if useCoDH then (ECpublicKeyPartialValid P) else (ECpublicKeyValid P) )"
  have T1: "?T"           using P5 by presburger
  have M1: "EM = ENC ?EK M" 
    using assms(2) z1 ECIES_Encryption_SomeOutEq option.simps(1) prod.sel(1) by simp
  let ?M = "DEC ?EK EM"
  have M2: "ENC_VI ?EK M" using assms(1) ECIES_Encryption_validIn_def
    by (smt (verit, best) assms(1) ECIES_Encryption_validIn_def z1 option.simps(5)) 
  have M3: "?M = M"       using M1 M2 ENC_valid by blast
  have D1: "D = MAC ?MK (EM @ SharedInfo2)" 
    using assms(2) z1 ECIES_Encryption_SomeOutEq option.simps(1) prod.sel(1) by force
  have z2: "ECDHprimChoose useCoDH k Q\<^sub>V = ECDHprimChoose useCoDH d\<^sub>V P"
    using P2 VkeyPairValid ECDHch_2ValidKeyPairs by blast 
  show ?thesis            using z1 z2 P4 T1 M3 D1 ECIES_Decryption_def by force
qed

subsection \<open>5.2 Wrapped Key Transport Scheme\<close>

text \<open>"The wrapped key transport scheme uses a combination of a key wrap scheme and a key
agreement scheme."  This section of the standard discusses how a wrapped key transport scheme may
work without making any specific definitions.\<close>

end (* of ECIES locale *)

section \<open>6 Key Agreement Schemes\<close>

text \<open>"Key agreement schemes are designed to be used by two entities --- an entity U and an entity
V --- when U and V want to establish shared keying data that they can later use to control the
operation of a symmetric cryptographic scheme. ... Note that this document does not address how
specific keys should be derived from keying data established using a key agreement scheme. This
detail is left to be determined on an application by application basis." \<close>

subsection \<open>6.1 Elliptic Curve Diffie-Hellman Scheme\<close>

locale ECDH = SEC1 +
  fixes KDF     :: kdf_type
    and KDF_VI  :: kdf_validin_type
    and useCoDH :: bool
    and d\<^sub>V d\<^sub>U    :: nat
    and Q\<^sub>V Q\<^sub>U    :: "int point" 
assumes VkeyPairValid : "ECkeyPairValid d\<^sub>V Q\<^sub>V" 
    and UkeyPairValid : "ECkeyPairValid d\<^sub>U Q\<^sub>U" 
begin

subsubsection \<open>6.1.3 Key Agreement Operation\<close>

definition ECDH_KeyAgreement :: "nat \<Rightarrow> octets \<Rightarrow> octets option" where
  "ECDH_KeyAgreement keydatalen SharedInfo = 
   ( let z = ECDHprimChoose useCoDH d\<^sub>U Q\<^sub>V
     in 
        case z of
          None    \<Rightarrow> None
        | Some z' \<Rightarrow> 
          ( let mlen = octet_length p;
                Z    = nat_to_octets_len (nat z') mlen
          in
              Some (KDF Z keydatalen SharedInfo)
          )
   )" 

text \<open>Remember ECDHchoose_validKeys: Because these are both valid key pairs, we know that
\<open>\<exists>z. ECDHprimChoose useCo d Q = Some z\<close>.\<close>
definition ECDH_KeyAgreement_validIn :: "nat \<Rightarrow> octets \<Rightarrow> bool" where
  "ECDH_KeyAgreement_validIn keydatalen SharedInfo \<equiv> 
     \<exists>z. (ECDHprimChoose useCoDH d\<^sub>U Q\<^sub>V = Some z) \<and> 
         (KDF_VI (nat_to_octets_len (nat z) (octet_length p)) keydatalen SharedInfo)" 

text \<open>This lemma shows that entity V can get the same key that U produced.  U produces the key 
with U's private key and V's public key.  V produces the same key with V's private key and 
U's public key.\<close>
lemma ECDH_KeyAgreement_eq:
  "ECDH_KeyAgreement keydatalen SharedInfo = 
   ( let z = ECDHprimChoose useCoDH d\<^sub>V Q\<^sub>U
     in 
        case z of
          None    \<Rightarrow> None
        | Some z' \<Rightarrow> 
          ( let mlen = octet_length p;
                Z    = nat_to_octets_len (nat z') mlen
          in
              Some (KDF Z keydatalen SharedInfo)
          )
   )" 
  by (metis ECDH_KeyAgreement_def ECDHch_2ValidKeyPairs UkeyPairValid VkeyPairValid option.simps(5)
            ECDHchoose_validKeys ECkeyPairImpliesPrivateKeyValid keyPairValidImpliespublicKeyValid)

end (* of ECDH locale *)

subsection \<open>6.2 Elliptic Curve MQV Scheme\<close>

locale ECMQV = SEC1 +
  fixes KDF             :: kdf_type
    and d1U d2U d1V d2V :: nat
    and Q1U Q2U Q1V Q2V :: "int point"
assumes VkeyPairValid : "ECkeyPairValid d1V Q1V" "ECkeyPairValid d2V Q2V" 
    and UkeyPairValid : "ECkeyPairValid d1U Q1U" "ECkeyPairValid d2U Q2U" 
begin

subsubsection \<open>6.2.3 Key Agreement Operation\<close>

definition ECMQV_KeyAgreement :: "nat \<Rightarrow> octets \<Rightarrow> octets option" where
  "ECMQV_KeyAgreement keydatalen SharedInfo = 
  ( let z = ECMQVprim d1U Q1U d2U Q2U Q1V Q2V
    in
        case z of
          None    \<Rightarrow> None
        | Some z' \<Rightarrow> 
          ( let mlen = octet_length p;
                Z    = nat_to_octets_len (nat z') mlen
          in
              Some (KDF Z keydatalen SharedInfo)
          )
  )"


text \<open>As with the Diffie-Hellman Key Agreement operation, the important thing to note with the
ECMQV Key Agreement operation is that both U and V can compute the same key using their own keys
together with the public keys of the other party.  This follows from MQV_reverseUV above.\<close>

lemma ECMQV_KeyAgreement_eq:
  "ECMQV_KeyAgreement keydatalen SharedInfo = 
  ( let z = ECMQVprim d1V Q1V d2V Q2V Q1U Q2U
    in
        case z of
          None    \<Rightarrow> None
        | Some z' \<Rightarrow> 
          ( let mlen = octet_length p;
                Z    = nat_to_octets_len (nat z') mlen
          in
              Some (KDF Z keydatalen SharedInfo)
          )
  )"
  by (metis ECMQV_KeyAgreement_def MQV_reverseUV UkeyPairValid VkeyPairValid)

end (* of ECMQV locale *)


end