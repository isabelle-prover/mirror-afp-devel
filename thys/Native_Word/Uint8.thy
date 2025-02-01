(*  Title:      Uint8.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Unsigned words of 8 bits\<close>

theory Uint8
  imports
    "HOL-Library.Code_Target_Bit_Shifts"
    Uint_Common
    Code_Target_Word
    Code_Int_Integer_Conversion
begin

text \<open>
  Restriction for OCaml code generation:
  OCaml does not provide an int8 type, so no special code generation 
  for this type is set up. If the theory \<^text>\<open>Code_Target_Int_Bit\<close>
  is imported, the type \<open>uint8\<close> is emulated via \<^typ>\<open>8 word\<close>.
\<close>

section \<open>Type definition and primitive operations\<close>

typedef uint8 = \<open>UNIV :: 8 word set\<close> ..

global_interpretation uint8: word_type_copy Abs_uint8 Rep_uint8
  using type_definition_uint8 by (rule word_type_copy.intro)

setup_lifting type_definition_uint8

declare uint8.of_word_of [code abstype]

declare Quotient_uint8 [transfer_rule]

instantiation uint8 :: \<open>{comm_ring_1, semiring_modulo, equal, linorder}\<close>
begin

lift_definition zero_uint8 :: uint8 is 0 .
lift_definition one_uint8 :: uint8 is 1 .
lift_definition plus_uint8 :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is \<open>(+)\<close> .
lift_definition uminus_uint8 :: \<open>uint8 \<Rightarrow> uint8\<close> is uminus .
lift_definition minus_uint8 :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is \<open>(-)\<close> .
lift_definition times_uint8 :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is \<open>(*)\<close> .
lift_definition divide_uint8 :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is \<open>(div)\<close> .
lift_definition modulo_uint8 :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is \<open>(mod)\<close> .
lift_definition equal_uint8 :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> bool\<close> is \<open>HOL.equal\<close> .
lift_definition less_eq_uint8 :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> bool\<close> is \<open>(\<le>)\<close> .
lift_definition less_uint8 :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> bool\<close> is \<open>(<)\<close> .

global_interpretation uint8: word_type_copy_ring Abs_uint8 Rep_uint8
  by standard (fact zero_uint8.rep_eq one_uint8.rep_eq
    plus_uint8.rep_eq uminus_uint8.rep_eq minus_uint8.rep_eq
    times_uint8.rep_eq divide_uint8.rep_eq modulo_uint8.rep_eq
    equal_uint8.rep_eq less_eq_uint8.rep_eq less_uint8.rep_eq)+

instance proof -
  show \<open>OFCLASS(uint8, comm_ring_1_class)\<close>
    by (rule uint8.of_class_comm_ring_1)
  show \<open>OFCLASS(uint8, semiring_modulo_class)\<close>
    by (fact uint8.of_class_semiring_modulo)
  show \<open>OFCLASS(uint8, equal_class)\<close>
    by (fact uint8.of_class_equal)
  show \<open>OFCLASS(uint8, linorder_class)\<close>
    by (fact uint8.of_class_linorder)
qed

end

instantiation uint8 :: ring_bit_operations
begin

lift_definition bit_uint8 :: \<open>uint8 \<Rightarrow> nat \<Rightarrow> bool\<close> is bit .
lift_definition not_uint8 :: \<open>uint8 \<Rightarrow> uint8\<close> is \<open>Bit_Operations.not\<close> .
lift_definition and_uint8 :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is \<open>Bit_Operations.and\<close> .
lift_definition or_uint8 :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is \<open>Bit_Operations.or\<close> .
lift_definition xor_uint8 :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is \<open>Bit_Operations.xor\<close> .
lift_definition mask_uint8 :: \<open>nat \<Rightarrow> uint8\<close> is mask .
lift_definition push_bit_uint8 :: \<open>nat \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is push_bit .
lift_definition drop_bit_uint8 :: \<open>nat \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is drop_bit .
lift_definition signed_drop_bit_uint8 :: \<open>nat \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is signed_drop_bit .
lift_definition take_bit_uint8 :: \<open>nat \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is take_bit .
lift_definition set_bit_uint8 :: \<open>nat \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is Bit_Operations.set_bit .
lift_definition unset_bit_uint8 :: \<open>nat \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is unset_bit .
lift_definition flip_bit_uint8 :: \<open>nat \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is flip_bit .

global_interpretation uint8: word_type_copy_bits Abs_uint8 Rep_uint8 signed_drop_bit_uint8
  by standard (fact bit_uint8.rep_eq not_uint8.rep_eq and_uint8.rep_eq or_uint8.rep_eq xor_uint8.rep_eq
    mask_uint8.rep_eq push_bit_uint8.rep_eq drop_bit_uint8.rep_eq signed_drop_bit_uint8.rep_eq take_bit_uint8.rep_eq
    set_bit_uint8.rep_eq unset_bit_uint8.rep_eq flip_bit_uint8.rep_eq)+

instance
  by (fact uint8.of_class_ring_bit_operations)

end

lift_definition uint8_of_nat :: \<open>nat \<Rightarrow> uint8\<close>
  is word_of_nat .

lift_definition nat_of_uint8 :: \<open>uint8 \<Rightarrow> nat\<close>
  is unat .

lift_definition uint8_of_int :: \<open>int \<Rightarrow> uint8\<close>
  is word_of_int .

lift_definition int_of_uint8 :: \<open>uint8 \<Rightarrow> int\<close>
  is uint .

context
  includes integer.lifting
begin

lift_definition Uint8 :: \<open>integer \<Rightarrow> uint8\<close>
  is word_of_int .

lift_definition integer_of_uint8 :: \<open>uint8 \<Rightarrow> integer\<close>
  is uint .

end

global_interpretation uint8: word_type_copy_more Abs_uint8 Rep_uint8 signed_drop_bit_uint8
  uint8_of_nat nat_of_uint8 uint8_of_int int_of_uint8 Uint8 integer_of_uint8
  apply standard
       apply (simp_all add: uint8_of_nat.rep_eq nat_of_uint8.rep_eq
         uint8_of_int.rep_eq int_of_uint8.rep_eq
         Uint8.rep_eq integer_of_uint8.rep_eq integer_eq_iff)
  done

instantiation uint8 :: "{size, msb, bit_comprehension}"
begin

lift_definition size_uint8 :: \<open>uint8 \<Rightarrow> nat\<close> is size .

lift_definition msb_uint8 :: \<open>uint8 \<Rightarrow> bool\<close> is msb .

lift_definition set_bits_uint8 :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> uint8\<close> is set_bits .
lift_definition set_bits_aux_uint8 :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> uint8 \<Rightarrow> uint8\<close> is set_bits_aux .

global_interpretation uint8: word_type_copy_misc Abs_uint8 Rep_uint8 signed_drop_bit_uint8
  uint8_of_nat nat_of_uint8 uint8_of_int int_of_uint8 Uint8 integer_of_uint8 8 set_bits_aux_uint8
  by (standard; transfer) simp_all

instance using uint8.of_class_bit_comprehension
  by simp_all standard

end

section \<open>Code setup\<close>

code_printing code_module Uint8 \<rightharpoonup> (SML)
\<open>(* Test that words can handle numbers between 0 and 3 *)
val _ = if 3 <= Word.wordSize then () else raise (Fail ("wordSize less than 3"));

structure Uint8 : sig
  val shiftl : Word8.word -> IntInf.int -> Word8.word
  val shiftr : Word8.word -> IntInf.int -> Word8.word
  val shiftr_signed : Word8.word -> IntInf.int -> Word8.word
  val test_bit : Word8.word -> IntInf.int -> bool
end = struct

fun shiftl x n =
  Word8.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word8.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word8.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word8.andb (x, Word8.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word8.fromInt 0

end; (* struct Uint8 *)\<close>
code_reserved (SML) Uint8

code_printing code_module Uint8 \<rightharpoonup> (Haskell)
 \<open>module Uint8(Int8, Word8) where

  import Data.Int(Int8)
  import Data.Word(Word8)\<close>
code_reserved (Haskell) Uint8

text \<open>
  Scala provides only signed 8bit numbers, so we use these and 
  implement sign-sensitive operations like comparisons manually.
\<close>

code_printing code_module Uint8 \<rightharpoonup> (Scala)
\<open>object Uint8 {

def less(x: Byte, y: Byte) : Boolean =
  x < 0 match {
    case true => y < 0 && x < y
    case false => y < 0 || x < y
  }

def less_eq(x: Byte, y: Byte) : Boolean =
  x < 0 match {
    case true => y < 0 && x <= y
    case false => y < 0 || x <= y
  }

def shiftl(x: Byte, n: BigInt) : Byte = (x << n.intValue).toByte

def shiftr(x: Byte, n: BigInt) : Byte = ((x & 255) >>> n.intValue).toByte

def shiftr_signed(x: Byte, n: BigInt) : Byte = (x >> n.intValue).toByte

def test_bit(x: Byte, n: BigInt) : Boolean =
  (x & (1 << n.intValue)) != 0

} /* object Uint8 */\<close>
code_reserved (Scala) Uint8

text \<open>
  Avoid @{term Abs_uint8} in generated code, use @{term Rep_uint8'} instead. 
  The symbolic implementations for code\_simp use @{term Rep_uint8}.

  The new destructor @{term Rep_uint8'} is executable.
  As the simplifier is given the [code abstract] equations literally, 
  we cannot implement @{term Rep_uint8} directly, because that makes code\_simp loop.

  If code generation raises Match, some equation probably contains @{term Rep_uint8} 
  ([code abstract] equations for @{typ uint8} may use @{term Rep_uint8} because
  these instances will be folded away.)

  To convert @{typ "8 word"} values into @{typ uint8}, use @{term "Abs_uint8'"}.
\<close>

definition Rep_uint8' where [simp]: "Rep_uint8' = Rep_uint8"

lemma Rep_uint8'_transfer [transfer_rule]:
  "rel_fun cr_uint8 (=) (\<lambda>x. x) Rep_uint8'"
unfolding Rep_uint8'_def by(rule uint8.rep_transfer)

lemma Rep_uint8'_code [code]: "Rep_uint8' x = (BITS n. bit x n)"
  by transfer (simp add: set_bits_bit_eq)

lift_definition Abs_uint8' :: "8 word \<Rightarrow> uint8" is "\<lambda>x :: 8 word. x" .

lemma Abs_uint8'_code [code]: "Abs_uint8' x = Uint8 (integer_of_int (uint x))"
including integer.lifting by transfer simp

declare [[code drop: "term_of_class.term_of :: uint8 \<Rightarrow> _"]]

lemma term_of_uint8_code [code]:
  defines "TR \<equiv> typerep.Typerep" and "bit0 \<equiv> STR ''Numeral_Type.bit0''" shows
  "term_of_class.term_of x = 
   Code_Evaluation.App (Code_Evaluation.Const (STR ''Uint8.uint8.Abs_uint8'') (TR (STR ''fun'') [TR (STR ''Word.word'') [TR bit0 [TR bit0 [TR bit0 [TR (STR ''Numeral_Type.num1'') []]]]], TR (STR ''Uint8.uint8'') []]))
       (term_of_class.term_of (Rep_uint8' x))"
by(simp add: term_of_anything)

lemma Uin8_code [code]: "Rep_uint8 (Uint8 i) = word_of_int (int_of_integer_symbolic i)"
unfolding Uint8_def int_of_integer_symbolic_def by(simp add: Abs_uint8_inverse)

code_printing type_constructor uint8 \<rightharpoonup>
  (SML) "Word8.word" and
  (Haskell) "Uint8.Word8" and
  (Scala) "Byte"
| constant Uint8 \<rightharpoonup> 
  (SML) "Word8.fromLargeInt (IntInf.toLarge _)" and
  (Haskell) "(Prelude.fromInteger _ :: Uint8.Word8)" and
  (Haskell_Quickcheck) "(Prelude.fromInteger (Prelude.toInteger _) :: Uint8.Word8)" and
  (Scala) "_.byteValue"
| constant "0 :: uint8" \<rightharpoonup>
  (SML) "(Word8.fromInt 0)" and
  (Haskell) "(0 :: Uint8.Word8)" and
  (Scala) "0.toByte"
| constant "1 :: uint8" \<rightharpoonup>
  (SML) "(Word8.fromInt 1)" and
  (Haskell) "(1 :: Uint8.Word8)" and
  (Scala) "1.toByte"
| constant "plus :: uint8 \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word8.+ ((_), (_))" and
  (Haskell) infixl 6 "+" and
  (Scala) "(_ +/ _).toByte"
| constant "uminus :: uint8 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word8.~" and
  (Haskell) "negate" and
  (Scala) "(- _).toByte"
| constant "minus :: uint8 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word8.- ((_), (_))" and
  (Haskell) infixl 6 "-" and
  (Scala) "(_ -/ _).toByte"
| constant "times :: uint8 \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word8.* ((_), (_))" and
  (Haskell) infixl 7 "*" and
  (Scala) "(_ */ _).toByte"
| constant "HOL.equal :: uint8 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML) "!((_ : Word8.word) = _)" and
  (Haskell) infix 4 "==" and
  (Scala) infixl 5 "=="
| class_instance uint8 :: equal \<rightharpoonup> (Haskell) -
| constant "less_eq :: uint8 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Word8.<= ((_), (_))" and
  (Haskell) infix 4 "<=" and
  (Scala) "Uint8.less'_eq"
| constant "less :: uint8 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Word8.< ((_), (_))" and
  (Haskell) infix 4 "<" and
  (Scala) "Uint8.less"
| constant "Bit_Operations.not :: uint8 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word8.notb" and
  (Haskell) "Data'_Bits.complement" and
  (Scala) "_.unary'_~.toByte"
| constant "Bit_Operations.and :: uint8 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word8.andb ((_),/ (_))" and
  (Haskell) infixl 7 "Data_Bits..&." and
  (Scala) "(_ & _).toByte"
| constant "Bit_Operations.or :: uint8 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word8.orb ((_),/ (_))" and
  (Haskell) infixl 5 "Data_Bits..|." and
  (Scala) "(_ | _).toByte"
| constant "Bit_Operations.xor :: uint8 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word8.xorb ((_),/ (_))" and
  (Haskell) "Data'_Bits.xor" and
  (Scala) "(_ ^ _).toByte"

definition uint8_divmod :: "uint8 \<Rightarrow> uint8 \<Rightarrow> uint8 \<times> uint8" where
  "uint8_divmod x y = 
  (if y = 0 then (undefined ((div) :: uint8 \<Rightarrow> _) x (0 :: uint8), undefined ((mod) :: uint8 \<Rightarrow> _) x (0 :: uint8)) 
  else (x div y, x mod y))"

definition uint8_div :: "uint8 \<Rightarrow> uint8 \<Rightarrow> uint8" 
where "uint8_div x y = fst (uint8_divmod x y)"

definition uint8_mod :: "uint8 \<Rightarrow> uint8 \<Rightarrow> uint8" 
where "uint8_mod x y = snd (uint8_divmod x y)"

lemma div_uint8_code [code]: "x div y = (if y = 0 then 0 else uint8_div x y)"
  including undefined_transfer unfolding uint8_divmod_def uint8_div_def
by transfer (simp add: word_div_def)

lemma mod_uint8_code [code]: "x mod y = (if y = 0 then x else uint8_mod x y)"
including undefined_transfer unfolding uint8_mod_def uint8_divmod_def
by transfer (simp add: word_mod_def)

definition uint8_sdiv :: "uint8 \<Rightarrow> uint8 \<Rightarrow> uint8"
where
  "uint8_sdiv x y =
   (if y = 0 then undefined ((div) :: uint8 \<Rightarrow> _) x (0 :: uint8)
    else Abs_uint8 (Rep_uint8 x sdiv Rep_uint8 y))"

definition div0_uint8 :: "uint8 \<Rightarrow> uint8"
where [code del]: "div0_uint8 x = undefined ((div) :: uint8 \<Rightarrow> _) x (0 :: uint8)"
declare [[code abort: div0_uint8]]

definition mod0_uint8 :: "uint8 \<Rightarrow> uint8"
where [code del]: "mod0_uint8 x = undefined ((mod) :: uint8 \<Rightarrow> _) x (0 :: uint8)"
declare [[code abort: mod0_uint8]]

lemma uint8_divmod_code [code]:
  "uint8_divmod x y =
  (if 0x80 \<le> y then if x < y then (0, x) else (1, x - y)
   else if y = 0 then (div0_uint8 x, mod0_uint8 x)
   else let q = push_bit 1 (uint8_sdiv (drop_bit 1 x) y);
            r = x - q * y
        in if r \<ge> y then (q + 1, r - y) else (q, r))"
  including undefined_transfer unfolding uint8_divmod_def uint8_sdiv_def div0_uint8_def mod0_uint8_def
    less_eq_uint8.rep_eq
  apply transfer
  apply (simp add: divmod_via_sdivmod push_bit_eq_mult)
  done

lemma uint8_sdiv_code [code]:
  "Rep_uint8 (uint8_sdiv x y) =
   (if y = 0 then Rep_uint8 (undefined ((div) :: uint8 \<Rightarrow> _) x (0 :: uint8))
    else Rep_uint8 x sdiv Rep_uint8 y)"
unfolding uint8_sdiv_def by(simp add: Abs_uint8_inverse)

text \<open>
  Note that we only need a translation for signed division, but not for the remainder
  because @{thm uint8_divmod_code} computes both with division only.
\<close>

code_printing
  constant uint8_div \<rightharpoonup>
  (SML) "Word8.div ((_), (_))" and
  (Haskell) "Prelude.div"
| constant uint8_mod \<rightharpoonup>
  (SML) "Word8.mod ((_), (_))" and
  (Haskell) "Prelude.mod"
| constant uint8_divmod \<rightharpoonup>
  (Haskell) "divmod"
| constant uint8_sdiv \<rightharpoonup>
  (Scala) "(_ '/ _).toByte"

global_interpretation uint8: word_type_copy_target_language Abs_uint8 Rep_uint8 signed_drop_bit_uint8
  uint8_of_nat nat_of_uint8 uint8_of_int int_of_uint8 Uint8 integer_of_uint8 8 set_bits_aux_uint8 8 7
  defines uint8_test_bit = uint8.test_bit
    and uint8_shiftl = uint8.shiftl
    and uint8_shiftr = uint8.shiftr
    and uint8_sshiftr = uint8.sshiftr
  by standard simp_all

code_printing constant uint8_test_bit \<rightharpoonup>
  (SML) "Uint8.test'_bit" and
  (Haskell) "Data'_Bits.testBitBounded" and
  (Scala) "Uint8.test'_bit" and
  (Eval) "(fn w => fn i => if i < 0 orelse i >= 8 then raise (Fail \"argument to uint8'_test'_bit out of bounds\") else Uint8.test'_bit w i)"

code_printing constant uint8_shiftl \<rightharpoonup>
  (SML) "Uint8.shiftl" and
  (Haskell) "Data'_Bits.shiftlBounded" and
  (Scala) "Uint8.shiftl" and
  (Eval) "(fn w => fn i => if i < 0 orelse i >= 8 then raise (Fail \"argument to uint8'_shiftl out of bounds\") else Uint8.shiftl w i)"

code_printing constant uint8_shiftr \<rightharpoonup>
  (SML) "Uint8.shiftr" and
  (Haskell) "Data'_Bits.shiftrBounded" and
  (Scala) "Uint8.shiftr" and
  (Eval) "(fn w => fn i => if i < 0 orelse i >= 8 then raise (Fail \"argument to uint8'_shiftr out of bounds\") else Uint8.shiftr w i)"

code_printing constant uint8_sshiftr \<rightharpoonup>
  (SML) "Uint8.shiftr'_signed" and
  (Haskell) 
    "(Prelude.fromInteger (Prelude.toInteger (Data'_Bits.shiftrBounded (Prelude.fromInteger (Prelude.toInteger _) :: Uint8.Int8) _)) :: Uint8.Word8)" and
  (Scala) "Uint8.shiftr'_signed" and
  (Eval) "(fn w => fn i => if i < 0 orelse i >= 8 then raise (Fail \"argument to uint8'_sshiftr out of bounds\") else Uint8.shiftr'_signed w i)"

context
  includes bit_operations_syntax
begin

lemma uint8_msb_test_bit: "msb x \<longleftrightarrow> bit (x :: uint8) 7"
  by transfer (simp add: msb_word_iff_bit)

lemma msb_uint16_code [code]: "msb x \<longleftrightarrow> uint8_test_bit x 7"
  by (simp add: uint8.test_bit_def uint8_msb_test_bit)

lemma uint8_of_int_code [code]:
  "uint8_of_int i = Uint8 (integer_of_int i)"
  including integer.lifting by transfer simp

lemma int_of_uint8_code [code]:
  "int_of_uint8 x = int_of_integer (integer_of_uint8 x)"
  by (simp add: int_of_uint8.rep_eq integer_of_uint8_def)

lemma uint8_of_nat_code [code]:
  "uint8_of_nat = uint8_of_int \<circ> int"
  by transfer (simp add: fun_eq_iff)

lemma nat_of_uint8_code [code]:
  "nat_of_uint8 x = nat_of_integer (integer_of_uint8 x)"
  unfolding integer_of_uint8_def including integer.lifting by transfer simp

definition integer_of_uint8_signed :: "uint8 \<Rightarrow> integer"
where
  "integer_of_uint8_signed n = (if bit n 7 then undefined integer_of_uint8 n else integer_of_uint8 n)"

lemma integer_of_uint8_signed_code [code]:
  "integer_of_uint8_signed n =
  (if bit n 7 then undefined integer_of_uint8 n else integer_of_int (uint (Rep_uint8' n)))"
  by (simp add: integer_of_uint8_signed_def integer_of_uint8_def)

lemma integer_of_uint8_code [code]:
  "integer_of_uint8 n =
  (if bit n 7 then integer_of_uint8_signed (n AND 0x7F) OR 0x80 else integer_of_uint8_signed n)"
proof -
  have \<open>integer_of_uint8_signed (n AND 0x7F) OR 0x80 = Bit_Operations.set_bit 7 (integer_of_uint8_signed (take_bit 7 n))\<close>
    by (simp add: take_bit_eq_mask set_bit_eq_or push_bit_eq_mult mask_eq_exp_minus_1)
  moreover have \<open>integer_of_uint8 n = Bit_Operations.set_bit 7 (integer_of_uint8 (take_bit 7 n))\<close> if \<open>bit n 7\<close>
  proof (rule bit_eqI)
    fix m
    from that show \<open>bit (integer_of_uint8 n) m = bit (Bit_Operations.set_bit 7 (integer_of_uint8 (take_bit 7 n))) m\<close> for m
      including integer.lifting by transfer (auto simp add: bit_simps dest: bit_imp_le_length)
  qed
  ultimately show ?thesis
    by simp (simp add: integer_of_uint8_signed_def bit_simps)
qed

end

code_printing
  constant "integer_of_uint8" \<rightharpoonup>
  (SML) "IntInf.fromLarge (Word8.toLargeInt _)" and
  (Haskell) "Prelude.toInteger"
| constant "integer_of_uint8_signed" \<rightharpoonup>
  (Scala) "BigInt"

section \<open>Quickcheck setup\<close>

definition uint8_of_natural :: "natural \<Rightarrow> uint8"
where "uint8_of_natural x \<equiv> Uint8 (integer_of_natural x)"

instantiation uint8 :: "{random, exhaustive, full_exhaustive}" begin
definition "random_uint8 \<equiv> qc_random_cnv uint8_of_natural"
definition "exhaustive_uint8 \<equiv> qc_exhaustive_cnv uint8_of_natural"
definition "full_exhaustive_uint8 \<equiv> qc_full_exhaustive_cnv uint8_of_natural"
instance ..
end

instantiation uint8 :: narrowing begin

interpretation quickcheck_narrowing_samples
  "\<lambda>i. let x = Uint8 i in (x, 0xFF - x)" "0"
  "Typerep.Typerep (STR ''Uint8.uint8'') []" .

definition "narrowing_uint8 d = qc_narrowing_drawn_from (narrowing_samples d) d"
declare [[code drop: "partial_term_of :: uint8 itself \<Rightarrow> _"]]
lemmas partial_term_of_uint8 [code] = partial_term_of_code

instance ..
end

end
