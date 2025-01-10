(*  Title:      Code_Target_Integer_Bit.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Bit operations for target language integers\<close>

theory Code_Target_Integer_Bit
  imports
    "HOL-Library.Word"
    "Code_Target_Word"
    "Code_Int_Integer_Conversion"
    "Word_Lib.Most_significant_bit"
    "Word_Lib.Generic_set_bit"
    "Word_Lib.Bit_Comprehension"
begin

section \<open>More lemmas about @{typ integer}s\<close>

context
  includes integer.lifting
begin

lemma not_integer_of_nat_less_0 [simp]:
  \<open>\<not> integer_of_nat n < 0\<close>
  by transfer simp

lemma sub_integer_negative:
  \<open>\<not> Code_Numeral.sub n num.One < 0\<close>
  by transfer (simp add: sub_negative)

lemma integer_dup_eq [simp]:
  \<open>Code_Numeral.dup = times (2 :: integer)\<close>
  by transfer simp

lemma nat_of_integer_sub_1_conv_pred_numeral [simp]:
  \<open>nat_of_integer (Code_Numeral.sub n num.One) = pred_numeral n\<close>
proof (transfer fixing: n)
  have \<open>nat (numeral n - Numeral1) = nat (numeral n) - nat Numeral1\<close>
    by (subst nat_diff_distrib) simp_all
  then show \<open>nat (numeral n - Numeral1) = pred_numeral n\<close>
    by simp
qed

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

context
  includes integer.lifting and bit_operations_syntax
begin

private lemma [simp]:
  \<open>- 1 div 2 = (- 1 :: integer)\<close>
  by (rule bit_eqI) (simp add: bit_simps flip: bit_Suc)

lemma and_integer_code [code]:
  \<open>x AND y =
   (if x = 0 then 0
    else if x = - 1 then y
    else (x mod 2) * (y mod 2) + push_bit 1 (drop_bit 1 x AND drop_bit 1 y))\<close>
  for x y :: integer
proof -
  from and_rec [of x y]
  have \<open>x AND y = (x mod 2) * (y mod 2) + push_bit 1 (drop_bit 1 x AND drop_bit 1 y)\<close>
    by (simp del: push_bit_and add: odd_iff_mod_2_eq_one drop_bit_Suc)
  then show ?thesis
    by auto
qed

lemma or_integer_code [code]:
  \<open>x OR y =
   (if x = 0 then y
    else if x = - 1 then - 1
    else max (x mod 2) (y mod 2) + push_bit 1 (drop_bit 1 x OR drop_bit 1 y))\<close>
  for x y :: integer
proof -
  from or_rec [of x y]
  have \<open>x OR y = max (x mod 2) (y mod 2) + push_bit 1 (drop_bit 1 x OR drop_bit 1 y)\<close>
    by (simp del: push_bit_or add: odd_iff_mod_2_eq_one drop_bit_Suc)
  then show ?thesis
    by auto
qed

lemma xor_integer_code [code]:
  \<open>x XOR y =
   (if x = 0 then y
    else if x = - 1 then NOT y
    else \<bar>x mod 2 - y mod 2\<bar> + push_bit 1 (drop_bit 1 x XOR drop_bit 1 y))\<close>
  for x y :: integer
proof -
  from xor_rec [of x y]
  have \<open>x XOR y = \<bar>x mod 2 - y mod 2\<bar> + push_bit 1 (drop_bit 1 x XOR drop_bit 1 y)\<close>
    by (simp del: push_bit_xor add: odd_iff_mod_2_eq_one drop_bit_Suc) auto
  then show ?thesis
    by auto
qed

end

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
code_reserved (SML) Integer_Bit

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
code_reserved (OCaml) Integer_Bit

code_printing code_module Integer_Bit \<rightharpoonup> (Scala)
\<open>object Integer_Bit {

def testBit(x: BigInt, n: BigInt) : Boolean =
  n.isValidInt match {
    case true => x.testBit(n.toInt)
    case false => sys.error("Bit index too large: " + n.toString)
  }

def setBit(x: BigInt, n: BigInt, b: Boolean) : BigInt =
  n.isValidInt match {
    case true if b => x.setBit(n.toInt)
    case true => x.clearBit(n.toInt)
    case false => sys.error("Bit index too large: " + n.toString)
  }

def shiftl(x: BigInt, n: BigInt) : BigInt =
  n.isValidInt match {
    case true => x << n.toInt
    case false => sys.error("Shift index too large: " + n.toString)
  }

def shiftr(x: BigInt, n: BigInt) : BigInt =
  n.isValidInt match {
    case true => x << n.toInt
    case false => sys.error("Shift index too large: " + n.toString)
  }

} /* object Integer_Bit */\<close>

definition integer_test_bit :: \<open>integer \<Rightarrow> integer \<Rightarrow> bool\<close>
  where \<open>integer_test_bit x n = (if n < 0 then undefined x n else bit x (nat_of_integer n))\<close>

lemma integer_test_bit_code [code]:
  \<open>integer_test_bit x (Code_Numeral.Neg n) \<longleftrightarrow> undefined x (Code_Numeral.Neg n)\<close>
  \<open>integer_test_bit 0 0 \<longleftrightarrow> False\<close>
  \<open>integer_test_bit 0 (Code_Numeral.Pos n) \<longleftrightarrow> False\<close>
  \<open>integer_test_bit (Code_Numeral.Pos num.One)      0 \<longleftrightarrow> True\<close>
  \<open>integer_test_bit (Code_Numeral.Pos (num.Bit0 n)) 0 \<longleftrightarrow> False\<close>
  \<open>integer_test_bit (Code_Numeral.Pos (num.Bit1 n)) 0 \<longleftrightarrow> True\<close>
  \<open>integer_test_bit (Code_Numeral.Pos num.One)      (Code_Numeral.Pos n') \<longleftrightarrow> False\<close>
  \<open>integer_test_bit (Code_Numeral.Pos (num.Bit0 n)) (Code_Numeral.Pos n') \<longleftrightarrow>
   integer_test_bit (Code_Numeral.Pos n) (Code_Numeral.sub n' num.One)\<close>
  \<open>integer_test_bit (Code_Numeral.Pos (num.Bit1 n)) (Code_Numeral.Pos n') \<longleftrightarrow>
   integer_test_bit (Code_Numeral.Pos n) (Code_Numeral.sub n' num.One)\<close>
  \<open>integer_test_bit (Code_Numeral.Neg num.One)      0 \<longleftrightarrow> True\<close>
  \<open>integer_test_bit (Code_Numeral.Neg (num.Bit0 n)) 0 \<longleftrightarrow> False\<close>
  \<open>integer_test_bit (Code_Numeral.Neg (num.Bit1 n)) 0 \<longleftrightarrow> True\<close>
  \<open>integer_test_bit (Code_Numeral.Neg num.One)      (Code_Numeral.Pos n') \<longleftrightarrow> True\<close>
  \<open>integer_test_bit (Code_Numeral.Neg (num.Bit0 n)) (Code_Numeral.Pos n') \<longleftrightarrow>
   integer_test_bit (Code_Numeral.Neg n) (Code_Numeral.sub n' num.One)\<close>
  \<open>integer_test_bit (Code_Numeral.Neg (num.Bit1 n)) (Code_Numeral.Pos n') \<longleftrightarrow>
   integer_test_bit (Code_Numeral.Neg (n + num.One)) (Code_Numeral.sub n' num.One)\<close>
  by (simp_all add: integer_test_bit_def bit_integer_def sub_integer_negative flip: bit_not_int_iff')

code_printing constant integer_test_bit \<rightharpoonup>
  (SML) "Integer'_Bit.test'_bit" and
  (OCaml) "Integer'_Bit.test'_bit" and
  (Haskell) "(Data'_Bits.testBitUnbounded :: Integer -> Integer -> Bool)" and
  (Haskell_Quickcheck) "(Data'_Bits.testBitUnbounded :: Prelude.Int -> Prelude.Int -> Bool)" and
  (Scala) "Integer'_Bit.testBit"

lemma bit_integer_code [code]:
  "bit x n \<longleftrightarrow> integer_test_bit x (integer_of_nat n)"
  by (simp add: integer_test_bit_def)

definition integer_set_bit :: \<open>integer \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> integer\<close>
  where \<open>integer_set_bit x n b = (if n < 0 then undefined x n b else set_bit x (nat_of_integer n) b)\<close>

text \<open>
  OCaml.Big\_int does not have a method for changing an individual bit, so we emulate that with masks.
  We prefer an Isabelle implementation, because this then takes care of the signs for AND and OR.
\<close>

context
  includes bit_operations_syntax
begin

lemma integer_set_bit_code [code]:
  \<open>integer_set_bit x n b =
  (if n < 0 then undefined x n b else
   if b then x OR (push_bit (nat_of_integer n) 1)
   else x AND NOT (push_bit (nat_of_integer n) 1))\<close>
  by (simp add: integer_set_bit_def set_bit_eq set_bit_def unset_bit_def)

end

code_printing constant integer_set_bit \<rightharpoonup>
  (SML) "Integer'_Bit.set'_bit" and
  (Haskell) "(Data'_Bits.genericSetBitUnbounded :: Integer -> Integer -> Bool -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.genericSetBitUnbounded :: Prelude.Int -> Prelude.Int -> Bool -> Prelude.Int)" and
  (Scala) "Integer'_Bit.setBit"

lemma set_bit_integer_code [code]:
  \<open>set_bit x i b = integer_set_bit x (integer_of_nat i) b\<close>
  by (simp add: integer_set_bit_def)

definition integer_shiftl :: \<open>integer \<Rightarrow> integer \<Rightarrow> integer\<close>
  where \<open>integer_shiftl x n = (if n < 0 then undefined x n else push_bit (nat_of_integer n) x)\<close>

lemma integer_shiftl_code [code]:
  \<open>integer_shiftl x (Code_Numeral.Neg n) = undefined x (Code_Numeral.Neg n)\<close>
  \<open>integer_shiftl x 0 = x\<close>
  \<open>integer_shiftl x (Code_Numeral.Pos n) = integer_shiftl (Code_Numeral.dup x) (Code_Numeral.sub n num.One)\<close>
  \<open>integer_shiftl 0 (Code_Numeral.Pos n) = 0\<close>
  by (simp_all add: integer_shiftl_def numeral_eq_Suc sub_integer_negative ac_simps)

code_printing constant integer_shiftl \<rightharpoonup>
  (SML) "Integer'_Bit.shiftl" and
  (OCaml) "Integer'_Bit.shiftl" and
  (Haskell) "(Data'_Bits.shiftlUnbounded :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.shiftlUnbounded :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (Scala) "Integer'_Bit.shiftl"

lemma shiftl_integer_code [code]:
  \<open>push_bit n x = integer_shiftl x (integer_of_nat n)\<close> for x :: integer
  by (simp add: integer_shiftl_def)

definition integer_shiftr :: \<open>integer \<Rightarrow> integer \<Rightarrow> integer\<close>
  where \<open>integer_shiftr x n = (if n < 0 then undefined x n else drop_bit (nat_of_integer n) x)\<close>


context
  includes integer.lifting
begin

private lemma [simp]:
  \<open>drop_bit (pred_numeral n) (- 1) = (- 1 :: integer)\<close>
  by (transfer fixing: n) simp

private lemma [simp]:
  \<open>- numeral (num.Bit0 m) div (2 :: integer) = - numeral m\<close>
  by (transfer fixing: m) simp

private lemma [simp]:
  \<open>- numeral (num.Bit1 m) div (2 :: integer) = - numeral (Num.inc m)\<close>
  by (transfer fixing: m) (simp add: add_One)

lemma integer_shiftr_code [code]:
  \<open>integer_shiftr x (Code_Numeral.Neg n) = undefined x (Code_Numeral.Neg n)\<close>
  \<open>integer_shiftr x 0 = x\<close>
  \<open>integer_shiftr 0 (Code_Numeral.Pos n) = 0\<close>
  \<open>integer_shiftr (Code_Numeral.Pos num.One) (Code_Numeral.Pos n) = 0\<close>
  \<open>integer_shiftr (Code_Numeral.Pos (num.Bit0 n')) (Code_Numeral.Pos n) =
   integer_shiftr (Code_Numeral.Pos n') (Code_Numeral.sub n num.One)\<close>
  \<open>integer_shiftr (Code_Numeral.Pos (num.Bit1 n')) (Code_Numeral.Pos n) =
   integer_shiftr (Code_Numeral.Pos n') (Code_Numeral.sub n num.One)\<close>
  \<open>integer_shiftr (Code_Numeral.Neg num.One) (Code_Numeral.Pos n) = -1\<close>
  \<open>integer_shiftr (Code_Numeral.Neg (num.Bit0 n')) (Code_Numeral.Pos n) =
   integer_shiftr (Code_Numeral.Neg n') (Code_Numeral.sub n num.One)\<close>
  \<open>integer_shiftr (Code_Numeral.Neg (num.Bit1 n')) (Code_Numeral.Pos n) =
   integer_shiftr (Code_Numeral.Neg (Num.inc n')) (Code_Numeral.sub n num.One)\<close>
  by (simp_all add: integer_shiftr_def numeral_eq_Suc drop_bit_Suc sub_integer_negative)

end

code_printing constant integer_shiftr \<rightharpoonup>
  (SML) "Integer'_Bit.shiftr" and
  (OCaml) "Integer'_Bit.shiftr" and
  (Haskell) "(Data'_Bits.shiftrUnbounded :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.shiftrUnbounded :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (Scala) "Integer'_Bit.shiftr"

lemma shiftr_integer_code [code]:
  \<open>drop_bit n x = integer_shiftr x (integer_of_nat n)\<close> for x :: integer
  by (simp add: integer_shiftr_def)

end
