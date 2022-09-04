(*  Title:      Code_Target_Integer_Bit.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Bit operations for target language integers\<close>

theory Code_Target_Integer_Bit
  imports
    "HOL-Library.Word"
    "Code_Int_Integer_Conversion"
    "Word_Lib.Most_significant_bit"
    "Word_Lib.Least_significant_bit"
    "Word_Lib.Generic_set_bit"
    "Word_Lib.Bit_Comprehension"
begin

text \<open>TODO: separate\<close>

lemmas [transfer_rule] =
  identity_quotient
  fun_quotient
  Quotient_integer[folded integer.pcr_cr_eq]

lemma undefined_transfer:
  assumes "Quotient R Abs Rep T"
  shows "T (Rep undefined) undefined"
using assms unfolding Quotient_alt_def by blast

bundle undefined_transfer = undefined_transfer[transfer_rule]


section \<open>More lemmas about @{typ integer}s\<close>

context
  includes integer.lifting
begin

lemma integer_of_nat_less_0_conv [simp]: "\<not> integer_of_nat n < 0"
  by transfer simp

lemma int_of_integer_pow: "int_of_integer (x ^ n) = int_of_integer x ^ n"
  by transfer rule

lemma sub1_lt_0_iff [simp]: "Code_Numeral.sub n num.One < 0 \<longleftrightarrow> False"
  by transfer (simp add: sub_negative)

lemma nat_of_integer_numeral [simp]: "nat_of_integer (numeral n) = numeral n"
  by transfer simp

lemma nat_of_integer_sub1_conv_pred_numeral [simp]:
  "nat_of_integer (Code_Numeral.sub n num.One) = pred_numeral n"
  by transfer (simp only: pred_numeral_def int_nat_eq numeral_One int_minus flip: int_int_eq, simp)

lemma nat_of_integer_1 [simp]: "nat_of_integer 1 = 1"
  by transfer simp

lemma dup_1 [simp]: "Code_Numeral.dup 1 = 2"
  by transfer simp

lift_definition bin_rest_integer :: "integer \<Rightarrow> integer" is \<open>\<lambda>k . k div 2\<close> .

lift_definition bin_last_integer :: "integer \<Rightarrow> bool" is odd .

lift_definition Bit_integer :: "integer \<Rightarrow> bool \<Rightarrow> integer" is \<open>\<lambda>k b. of_bool b + 2 * k\<close> .

end


section \<open>Target language implementations\<close>

text \<open>
  Unfortunately, this is not straightforward,
  because these API functions have different signatures and preconditions on the parameters:

  \begin{description}
  \item[Standard ML] Shifts in IntInf are given as word, but not IntInf.
  \item[Haskell] In the Data.Bits.Bits type class, shifts and bit indices are given as Int rather than Integer.
  \end{description}

  Additional constants take only parameters of type @{typ integer} rather than @{typ nat}
  and check the preconditions as far as possible (e.g., being non-negative) in a portable way.
  Manual implementations inside code\_printing perform the remaining range checks and convert
  these @{typ integer}s into the right type.

  For normalisation by evaluation, we derive custom code equations, because NBE
  does not know these code\_printing serialisations and would otherwise loop.
\<close>

code_printing code_module Integer_Bit \<rightharpoonup> (SML)
\<open>structure Integer_Bit : sig
  val test_bit : IntInf.int -> IntInf.int -> bool
  val set_bit : IntInf.int -> IntInf.int -> bool -> IntInf.int
  val shiftl : IntInf.int -> IntInf.int -> IntInf.int
  val shiftr : IntInf.int -> IntInf.int -> IntInf.int
end = struct

val maxWord = IntInf.pow (2, Word.wordSize);

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

fun set_bit x n b =
  if n < maxWord then
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n)))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))))
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

fun shiftl x n =
  if n < maxWord then IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

end; (*struct Integer_Bit*)\<close>
code_reserved SML Integer_Bit

code_printing code_module Integer_Bit \<rightharpoonup> (OCaml)
\<open>module Integer_Bit : sig
  val test_bit : Z.t -> Z.t -> bool
  val shiftl : Z.t -> Z.t -> Z.t
  val shiftr : Z.t -> Z.t -> Z.t
end = struct

(* We do not need an explicit range checks here,
   because Big_int.int_of_big_int raises Failure
   if the argument does not fit into an int. *)
let test_bit x n =  Z.testbit x (Z.to_int n);;

let shiftl x n = Z.shift_left x (Z.to_int n);;

let shiftr x n = Z.shift_right x (Z.to_int n);;

end;; (*struct Integer_Bit*)\<close>
code_reserved OCaml Integer_Bit

code_printing code_module Data_Bits \<rightharpoonup> (Haskell)
\<open>
module Data_Bits where {

import qualified Data.Bits;

{-
  The ...Bounded functions assume that the Integer argument for the shift
  or bit index fits into an Int, is non-negative and (for types of fixed bit width)
  less than bitSize
-}

infixl 7 .&.;
infixl 6 `xor`;
infixl 5 .|.;

(.&.) :: Data.Bits.Bits a => a -> a -> a;
(.&.) = (Data.Bits..&.);

xor :: Data.Bits.Bits a => a -> a -> a;
xor = Data.Bits.xor;

(.|.) :: Data.Bits.Bits a => a -> a -> a;
(.|.) = (Data.Bits..|.);

complement :: Data.Bits.Bits a => a -> a;
complement = Data.Bits.complement;

testBitUnbounded :: Data.Bits.Bits a => a -> Integer -> Bool;
testBitUnbounded x b
  | b <= toInteger (Prelude.maxBound :: Int) = Data.Bits.testBit x (fromInteger b)
  | otherwise = error ("Bit index too large: " ++ show b)
;

testBitBounded :: Data.Bits.Bits a => a -> Integer -> Bool;
testBitBounded x b = Data.Bits.testBit x (fromInteger b);

setBitUnbounded :: Data.Bits.Bits a => a -> Integer -> Bool -> a;
setBitUnbounded x n b
  | n <= toInteger (Prelude.maxBound :: Int) =
    if b then Data.Bits.setBit x (fromInteger n) else Data.Bits.clearBit x (fromInteger n)
  | otherwise = error ("Bit index too large: " ++ show n)
;

setBitBounded :: Data.Bits.Bits a => a -> Integer -> Bool -> a;
setBitBounded x n True = Data.Bits.setBit x (fromInteger n);
setBitBounded x n False = Data.Bits.clearBit x (fromInteger n);

shiftlUnbounded :: Data.Bits.Bits a => a -> Integer -> a;
shiftlUnbounded x n
  | n <= toInteger (Prelude.maxBound :: Int) = Data.Bits.shiftL x (fromInteger n)
  | otherwise = error ("Shift operand too large: " ++ show n)
;

shiftlBounded :: Data.Bits.Bits a => a -> Integer -> a;
shiftlBounded x n = Data.Bits.shiftL x (fromInteger n);

shiftrUnbounded :: Data.Bits.Bits a => a -> Integer -> a;
shiftrUnbounded x n
  | n <= toInteger (Prelude.maxBound :: Int) = Data.Bits.shiftR x (fromInteger n)
  | otherwise = error ("Shift operand too large: " ++ show n)
;

shiftrBounded :: (Ord a, Data.Bits.Bits a) => a -> Integer -> a;
shiftrBounded x n = Data.Bits.shiftR x (fromInteger n);

}\<close>

  and \<comment> \<open>@{theory HOL.Quickcheck_Narrowing} maps @{typ integer} to
            Haskell's Prelude.Int type instead of Integer. For compatibility
            with the Haskell target, we nevertheless provide bounded and
            unbounded functions.\<close>
  (Haskell_Quickcheck)
\<open>
module Data_Bits where {

import qualified Data.Bits;

{-
  The functions assume that the Int argument for the shift or bit index is
  non-negative and (for types of fixed bit width) less than bitSize
-}

infixl 7 .&.;
infixl 6 `xor`;
infixl 5 .|.;

(.&.) :: Data.Bits.Bits a => a -> a -> a;
(.&.) = (Data.Bits..&.);

xor :: Data.Bits.Bits a => a -> a -> a;
xor = Data.Bits.xor;

(.|.) :: Data.Bits.Bits a => a -> a -> a;
(.|.) = (Data.Bits..|.);

complement :: Data.Bits.Bits a => a -> a;
complement = Data.Bits.complement;

testBitUnbounded :: Data.Bits.Bits a => a -> Prelude.Int -> Bool;
testBitUnbounded = Data.Bits.testBit;

testBitBounded :: Data.Bits.Bits a => a -> Prelude.Int -> Bool;
testBitBounded = Data.Bits.testBit;

setBitUnbounded :: Data.Bits.Bits a => a -> Prelude.Int -> Bool -> a;
setBitUnbounded x n True = Data.Bits.setBit x n;
setBitUnbounded x n False = Data.Bits.clearBit x n;

setBitBounded :: Data.Bits.Bits a => a -> Prelude.Int -> Bool -> a;
setBitBounded x n True = Data.Bits.setBit x n;
setBitBounded x n False = Data.Bits.clearBit x n;

shiftlUnbounded :: Data.Bits.Bits a => a -> Prelude.Int -> a;
shiftlUnbounded = Data.Bits.shiftL;

shiftlBounded :: Data.Bits.Bits a => a -> Prelude.Int -> a;
shiftlBounded = Data.Bits.shiftL;

shiftrUnbounded :: Data.Bits.Bits a => a -> Prelude.Int -> a;
shiftrUnbounded = Data.Bits.shiftR;

shiftrBounded :: (Ord a, Data.Bits.Bits a) => a -> Prelude.Int -> a;
shiftrBounded = Data.Bits.shiftR;

}\<close>
code_reserved Haskell Data_Bits

code_printing code_module Integer_Bit \<rightharpoonup> (Scala)
\<open>object Integer_Bit {

def testBit(x: BigInt, n: BigInt) : Boolean =
  if (n.isValidInt)
    x.testBit(n.toInt)
  else
    sys.error("Bit index too large: " + n.toString)

def setBit(x: BigInt, n: BigInt, b: Boolean) : BigInt =
  if (n.isValidInt)
    if (b)
      x.setBit(n.toInt)
    else
      x.clearBit(n.toInt)
  else
    sys.error("Bit index too large: " + n.toString)

def shiftl(x: BigInt, n: BigInt) : BigInt =
  if (n.isValidInt)
    x << n.toInt
  else
    sys.error("Shift index too large: " + n.toString)

def shiftr(x: BigInt, n: BigInt) : BigInt =
  if (n.isValidInt)
    x << n.toInt
  else
    sys.error("Shift index too large: " + n.toString)

} /* object Integer_Bit */\<close>

code_printing
  constant "Bit_Operations.and :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup>
  (SML) "IntInf.andb ((_),/ (_))" and
  (OCaml) "Z.logand" and
  (Haskell) "((Data'_Bits..&.) :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "((Data'_Bits..&.) :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (Scala) infixl 3 "&"
| constant "Bit_Operations.or :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup>
  (SML) "IntInf.orb ((_),/ (_))" and
  (OCaml) "Z.logor" and
  (Haskell) "((Data'_Bits..|.) :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "((Data'_Bits..|.) :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (Scala) infixl 1 "|"
| constant "Bit_Operations.xor :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup>
  (SML) "IntInf.xorb ((_),/ (_))" and
  (OCaml) "Z.logxor" and
  (Haskell) "(Data'_Bits.xor :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.xor :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (Scala) infixl 2 "^"
| constant "Bit_Operations.not :: integer \<Rightarrow> integer" \<rightharpoonup>
  (SML) "IntInf.notb" and
  (OCaml) "Z.lognot" and
  (Haskell) "(Data'_Bits.complement :: Integer -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.complement :: Prelude.Int -> Prelude.Int)" and
  (Scala) "_.unary'_~"

code_printing constant bin_rest_integer \<rightharpoonup>
  (SML) "IntInf.div ((_), 2)" and
  (OCaml) "Z.shift'_right/ _/ 1" and
  (Haskell) "(Data'_Bits.shiftrUnbounded _ 1 :: Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.shiftrUnbounded _ 1 :: Prelude.Int)" and
  (Scala) "_ >> 1"

context
  includes integer.lifting bit_operations_syntax
begin

lemma bitNOT_integer_code [code]:
  fixes i :: integer shows
  "NOT i = - i - 1"
  by transfer (simp add: not_int_def)

lemma bin_rest_integer_code [code nbe]:
  "bin_rest_integer i = i div 2"
  by transfer rule

lemma bin_last_integer_code [code]:
  "bin_last_integer i \<longleftrightarrow> i AND 1 \<noteq> 0"
  by transfer (simp add: and_one_eq odd_iff_mod_2_eq_one)

lemma bin_last_integer_nbe [code nbe]:
  "bin_last_integer i \<longleftrightarrow> i mod 2 \<noteq> 0"
  by transfer (simp add: odd_iff_mod_2_eq_one)

lemma bitval_bin_last_integer [code_unfold]:
  "of_bool (bin_last_integer i) = i AND 1"
  by transfer (simp add: and_one_eq mod_2_eq_odd)

end

definition integer_test_bit :: "integer \<Rightarrow> integer \<Rightarrow> bool"
  where "integer_test_bit x n = (if n < 0 then undefined x n else bit x (nat_of_integer n))"

declare [[code drop: \<open>bit :: integer \<Rightarrow> nat \<Rightarrow> bool\<close>]]

lemma bit_integer_code [code]:
  "bit x n \<longleftrightarrow> integer_test_bit x (integer_of_nat n)"
  by (simp add: integer_test_bit_def)

lemma integer_test_bit_code [code]:
  "integer_test_bit x (Code_Numeral.Neg n) = undefined x (Code_Numeral.Neg n)"
  "integer_test_bit 0 0 = False"
  "integer_test_bit 0 (Code_Numeral.Pos n) = False"
  "integer_test_bit (Code_Numeral.Pos num.One)      0 = True"
  "integer_test_bit (Code_Numeral.Pos (num.Bit0 n)) 0 = False"
  "integer_test_bit (Code_Numeral.Pos (num.Bit1 n)) 0 = True"
  "integer_test_bit (Code_Numeral.Pos num.One)      (Code_Numeral.Pos n') = False"
  "integer_test_bit (Code_Numeral.Pos (num.Bit0 n)) (Code_Numeral.Pos n') =
   integer_test_bit (Code_Numeral.Pos n) (Code_Numeral.sub n' num.One)"
  "integer_test_bit (Code_Numeral.Pos (num.Bit1 n)) (Code_Numeral.Pos n') =
   integer_test_bit (Code_Numeral.Pos n) (Code_Numeral.sub n' num.One)"
  "integer_test_bit (Code_Numeral.Neg num.One)      0 = True"
  "integer_test_bit (Code_Numeral.Neg (num.Bit0 n)) 0 = False"
  "integer_test_bit (Code_Numeral.Neg (num.Bit1 n)) 0 = True"
  "integer_test_bit (Code_Numeral.Neg num.One)      (Code_Numeral.Pos n') = True"
  "integer_test_bit (Code_Numeral.Neg (num.Bit0 n)) (Code_Numeral.Pos n') =
   integer_test_bit (Code_Numeral.Neg n) (Code_Numeral.sub n' num.One)"
  "integer_test_bit (Code_Numeral.Neg (num.Bit1 n)) (Code_Numeral.Pos n') =
   integer_test_bit (Code_Numeral.Neg (n + num.One)) (Code_Numeral.sub n' num.One)"
  by (simp_all add: integer_test_bit_def bit_integer_def bit_0 flip: bit_not_int_iff')

code_printing constant integer_test_bit \<rightharpoonup>
  (SML) "Integer'_Bit.test'_bit" and
  (OCaml) "Integer'_Bit.test'_bit" and
  (Haskell) "(Data'_Bits.testBitUnbounded :: Integer -> Integer -> Bool)" and
  (Haskell_Quickcheck) "(Data'_Bits.testBitUnbounded :: Prelude.Int -> Prelude.Int -> Bool)" and
  (Scala) "Integer'_Bit.testBit"

context
  includes integer.lifting bit_operations_syntax
begin

lemma lsb_integer_code [code]:
  fixes x :: integer shows
  "lsb x = bit x 0"
by transfer(simp add: lsb_int_def)

definition integer_set_bit :: "integer \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> integer"
where [code del]: "integer_set_bit x n b = (if n < 0 then undefined x n b else set_bit x (nat_of_integer n) b)"

lemma set_bit_integer_code [code]:
  "set_bit x i b = integer_set_bit x (integer_of_nat i) b"
by(simp add: integer_set_bit_def)

lemma set_bit_integer_conv_masks:
  fixes x :: integer shows
  "set_bit x i b = (if b then x OR (push_bit i 1) else x AND NOT (push_bit i 1))"
  by (transfer; rule bit_eqI) (simp add: bit_simps)

end

code_printing constant integer_set_bit \<rightharpoonup>
  (SML) "Integer'_Bit.set'_bit" and
  (Haskell) "(Data'_Bits.setBitUnbounded :: Integer -> Integer -> Bool -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.setBitUnbounded :: Prelude.Int -> Prelude.Int -> Bool -> Prelude.Int)" and
  (Scala) "Integer'_Bit.setBit"

text \<open>
  OCaml.Big\_int does not have a method for changing an individual bit, so we emulate that with masks.
  We prefer an Isabelle implementation, because this then takes care of the signs for AND and OR.
\<close>

context
  includes bit_operations_syntax
begin

lemma integer_set_bit_code [code]:
  "integer_set_bit x n b =
  (if n < 0 then undefined x n b else
   if b then x OR (push_bit (nat_of_integer n) 1)
   else x AND NOT (push_bit (nat_of_integer n) 1))"
  by (auto simp add: integer_set_bit_def not_less set_bit_eq set_bit_def unset_bit_def)

end

definition integer_shiftl :: "integer \<Rightarrow> integer \<Rightarrow> integer"
where [code del]: "integer_shiftl x n = (if n < 0 then undefined x n else push_bit (nat_of_integer n) x)"

declare [[code drop: \<open>push_bit :: nat \<Rightarrow> integer \<Rightarrow> integer\<close>]]

lemma shiftl_integer_code [code]:
  fixes x :: integer shows
  "push_bit n x = integer_shiftl x (integer_of_nat n)"
by(auto simp add: integer_shiftl_def)

context
includes integer.lifting
begin

lemma shiftl_integer_conv_mult_pow2:
  fixes x :: integer shows
  "push_bit n x = x * 2 ^ n"
  by (fact push_bit_eq_mult)

lemma integer_shiftl_code [code]:
  "integer_shiftl x (Code_Numeral.Neg n) = undefined x (Code_Numeral.Neg n)"
  "integer_shiftl x 0 = x"
  "integer_shiftl x (Code_Numeral.Pos n) = integer_shiftl (Code_Numeral.dup x) (Code_Numeral.sub n num.One)"
  "integer_shiftl 0 (Code_Numeral.Pos n) = 0"
     apply (simp_all add: integer_shiftl_def numeral_eq_Suc)
  apply transfer
  apply (simp add: ac_simps)
  done

end

code_printing constant integer_shiftl \<rightharpoonup>
  (SML) "Integer'_Bit.shiftl" and
  (OCaml) "Integer'_Bit.shiftl" and
  (Haskell) "(Data'_Bits.shiftlUnbounded :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.shiftlUnbounded :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (Scala) "Integer'_Bit.shiftl"

definition integer_shiftr :: "integer \<Rightarrow> integer \<Rightarrow> integer"
where [code del]: "integer_shiftr x n = (if n < 0 then undefined x n else drop_bit (nat_of_integer n) x)"

declare [[code drop: \<open>drop_bit :: nat \<Rightarrow> integer \<Rightarrow> integer\<close>]]

lemma shiftr_integer_conv_div_pow2:
  includes integer.lifting fixes x :: integer shows
  "drop_bit n x = x div 2 ^ n"
  by (fact drop_bit_eq_div)

lemma shiftr_integer_code [code]:
  fixes x :: integer shows
  "drop_bit n x = integer_shiftr x (integer_of_nat n)"
by(auto simp add: integer_shiftr_def)

code_printing constant integer_shiftr \<rightharpoonup>
  (SML) "Integer'_Bit.shiftr" and
  (OCaml) "Integer'_Bit.shiftr" and
  (Haskell) "(Data'_Bits.shiftrUnbounded :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.shiftrUnbounded :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (Scala) "Integer'_Bit.shiftr"

lemma integer_shiftr_code [code]:
  includes integer.lifting
  shows
  "integer_shiftr x (Code_Numeral.Neg n) = undefined x (Code_Numeral.Neg n)"
  "integer_shiftr x 0 = x"
  "integer_shiftr 0 (Code_Numeral.Pos n) = 0"
  "integer_shiftr (Code_Numeral.Pos num.One) (Code_Numeral.Pos n) = 0"
  "integer_shiftr (Code_Numeral.Pos (num.Bit0 n')) (Code_Numeral.Pos n) =
   integer_shiftr (Code_Numeral.Pos n') (Code_Numeral.sub n num.One)"
  "integer_shiftr (Code_Numeral.Pos (num.Bit1 n')) (Code_Numeral.Pos n) =
   integer_shiftr (Code_Numeral.Pos n') (Code_Numeral.sub n num.One)"
  "integer_shiftr (Code_Numeral.Neg num.One) (Code_Numeral.Pos n) = -1"
  "integer_shiftr (Code_Numeral.Neg (num.Bit0 n')) (Code_Numeral.Pos n) =
   integer_shiftr (Code_Numeral.Neg n') (Code_Numeral.sub n num.One)"
  "integer_shiftr (Code_Numeral.Neg (num.Bit1 n')) (Code_Numeral.Pos n) =
   integer_shiftr (Code_Numeral.Neg (Num.inc n')) (Code_Numeral.sub n num.One)"
          apply (simp_all add: integer_shiftr_def numeral_eq_Suc drop_bit_Suc)
    apply transfer apply simp
   apply transfer apply simp
  apply transfer apply (simp add: add_One)
  done

context
includes integer.lifting
begin

lemma Bit_integer_code [code]:
  "Bit_integer i False = push_bit 1 i"
  "Bit_integer i True = push_bit 1 i + 1"
  by (transfer; simp)+

lemma msb_integer_code [code]:
  "msb (x :: integer) \<longleftrightarrow> x < 0"
  by transfer (simp add: msb_int_def)

end

context
  includes integer.lifting bit_operations_syntax
begin

lemma bitAND_integer_unfold [code]:
  "x AND y =
   (if x = 0 then 0
    else if x = - 1 then y
    else Bit_integer (bin_rest_integer x AND bin_rest_integer y) (bin_last_integer x \<and> bin_last_integer y))"
  by transfer
    (auto simp add: algebra_simps
      and_int_rec [of _ \<open>_ * 2\<close>] and_int_rec [of \<open>_ * 2\<close>] and_int_rec [of \<open>1 + _ * 2\<close>]
      elim!: evenE oddE)

lemma bitOR_integer_unfold [code]:
  "x OR y =
   (if x = 0 then y
    else if x = - 1 then - 1
    else Bit_integer (bin_rest_integer x OR bin_rest_integer y) (bin_last_integer x \<or> bin_last_integer y))"
  by transfer
    (auto simp add: algebra_simps
      or_int_rec [of _ \<open>_ * 2\<close>] or_int_rec [of _ \<open>1 + _ * 2\<close>] or_int_rec [of \<open>1 + _ * 2\<close>]
      elim!: evenE oddE)

lemma bitXOR_integer_unfold [code]:
  "x XOR y =
   (if x = 0 then y
    else if x = - 1 then NOT y
    else Bit_integer (bin_rest_integer x XOR bin_rest_integer y)
      (\<not> bin_last_integer x \<longleftrightarrow> bin_last_integer y))"
  by transfer
    (auto simp add: algebra_simps
      xor_int_rec [of _ \<open>_ * 2\<close>] xor_int_rec [of \<open>_ * 2\<close>] xor_int_rec [of \<open>1 + _ * 2\<close>]
      elim!: evenE oddE)

end


section \<open>Test code generator setup\<close>

context
  includes bit_operations_syntax
begin

definition bit_integer_test :: "bool" where
  "bit_integer_test =
  (([ -1 AND 3, 1 AND -3, 3 AND 5, -3 AND (- 5)
    , -3 OR 1, 1 OR -3, 3 OR 5, -3 OR (- 5)
    , NOT 1, NOT (- 3)
    , -1 XOR 3, 1 XOR (- 3), 3 XOR 5, -5 XOR (- 3)
    , set_bit 5 4 True, set_bit (- 5) 2 True, set_bit 5 0 False, set_bit (- 5) 1 False
    , push_bit 2 1, push_bit 3 (- 1)
    , drop_bit 3 100, drop_bit 3 (- 100)] :: integer list)
  = [ 3, 1, 1, -7
    , -3, -3, 7, -1
    , -2, 2
    , -4, -4, 6, 6
    , 21, -1, 4, -7
    , 4, -8
    , 12, -13] \<and>
    [ bit (5 :: integer) 4, bit (5 :: integer) 2, bit (-5 :: integer) 4, bit (-5 :: integer) 2
    , lsb (5 :: integer), lsb (4 :: integer), lsb (-1 :: integer), lsb (-2 :: integer),
      msb (5 :: integer), msb (0 :: integer), msb (-1 :: integer), msb (-2 :: integer)]
  = [ False, True, True, False,
      True, False, True, False,
      False, False, True, True])"

export_code bit_integer_test checking SML Haskell? Haskell_Quickcheck? OCaml? Scala

notepad begin
have bit_integer_test by eval
have bit_integer_test by normalization
have bit_integer_test by code_simp
end
ML_val \<open>val true = @{code bit_integer_test}\<close>

lemma "x AND y = x OR (y :: integer)"
quickcheck[random, expect=counterexample]
quickcheck[exhaustive, expect=counterexample]
oops

lemma "(x :: integer) AND x = x OR x"
quickcheck[narrowing, expect=no_counterexample]
oops

lemma "(f :: integer \<Rightarrow> unit) = g"
quickcheck[narrowing, size=3, expect=no_counterexample]
by(simp add: fun_eq_iff)

end

hide_const bit_integer_test
hide_fact bit_integer_test_def

end
