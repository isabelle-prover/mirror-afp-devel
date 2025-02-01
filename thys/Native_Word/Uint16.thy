(*  Title:      Uint16.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Unsigned words of 16 bits\<close>

theory Uint16
  imports
    "HOL-Library.Code_Target_Bit_Shifts"
    Uint_Common
    Code_Target_Word
    Code_Int_Integer_Conversion
begin

text \<open>
  Restriction for ML code generation:
  This theory assumes that the ML system provides a Word16
  implementation (mlton does, but PolyML 5.5 does not).
  Therefore, the code setup lives in the target \<open>SML_word\<close>
  rather than \<open>SML\<close>.  This ensures that code generation still
  works as long as \<open>uint16\<close> is not involved.
  For the target \<open>SML\<close> itself, no special code generation 
  for this type is set up. Nevertheless, it should work by emulation via \<^typ>\<open>16 word\<close>
  if the theory \<^text>\<open>Code_Target_Int_Bit\<close> is imported.

  Restriction for OCaml code generation:
  OCaml does not provide an int16 type, so no special code generation 
  for this type is set up.
\<close>

section \<open>Type definition and primitive operations\<close>

typedef uint16 = \<open>UNIV :: 16 word set\<close> ..

global_interpretation uint16: word_type_copy Abs_uint16 Rep_uint16
  using type_definition_uint16 by (rule word_type_copy.intro)

setup_lifting type_definition_uint16

declare uint16.of_word_of [code abstype]

declare Quotient_uint16 [transfer_rule]

instantiation uint16 :: \<open>{comm_ring_1, semiring_modulo, equal, linorder}\<close>
begin

lift_definition zero_uint16 :: uint16 is 0 .
lift_definition one_uint16 :: uint16 is 1 .
lift_definition plus_uint16 :: \<open>uint16 \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is \<open>(+)\<close> .
lift_definition uminus_uint16 :: \<open>uint16 \<Rightarrow> uint16\<close> is uminus .
lift_definition minus_uint16 :: \<open>uint16 \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is \<open>(-)\<close> .
lift_definition times_uint16 :: \<open>uint16 \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is \<open>(*)\<close> .
lift_definition divide_uint16 :: \<open>uint16 \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is \<open>(div)\<close> .
lift_definition modulo_uint16 :: \<open>uint16 \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is \<open>(mod)\<close> .
lift_definition equal_uint16 :: \<open>uint16 \<Rightarrow> uint16 \<Rightarrow> bool\<close> is \<open>HOL.equal\<close> .
lift_definition less_eq_uint16 :: \<open>uint16 \<Rightarrow> uint16 \<Rightarrow> bool\<close> is \<open>(\<le>)\<close> .
lift_definition less_uint16 :: \<open>uint16 \<Rightarrow> uint16 \<Rightarrow> bool\<close> is \<open>(<)\<close> .

global_interpretation uint16: word_type_copy_ring Abs_uint16 Rep_uint16
  by standard (fact zero_uint16.rep_eq one_uint16.rep_eq
    plus_uint16.rep_eq uminus_uint16.rep_eq minus_uint16.rep_eq
    times_uint16.rep_eq divide_uint16.rep_eq modulo_uint16.rep_eq
    equal_uint16.rep_eq less_eq_uint16.rep_eq less_uint16.rep_eq)+

instance proof -
  show \<open>OFCLASS(uint16, comm_ring_1_class)\<close>
    by (rule uint16.of_class_comm_ring_1)
  show \<open>OFCLASS(uint16, semiring_modulo_class)\<close>
    by (fact uint16.of_class_semiring_modulo)
  show \<open>OFCLASS(uint16, equal_class)\<close>
    by (fact uint16.of_class_equal)
  show \<open>OFCLASS(uint16, linorder_class)\<close>
    by (fact uint16.of_class_linorder)
qed

end

instantiation uint16 :: ring_bit_operations
begin

lift_definition bit_uint16 :: \<open>uint16 \<Rightarrow> nat \<Rightarrow> bool\<close> is bit .
lift_definition not_uint16 :: \<open>uint16 \<Rightarrow> uint16\<close> is \<open>Bit_Operations.not\<close> .
lift_definition and_uint16 :: \<open>uint16 \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is \<open>Bit_Operations.and\<close> .
lift_definition or_uint16 :: \<open>uint16 \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is \<open>Bit_Operations.or\<close> .
lift_definition xor_uint16 :: \<open>uint16 \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is \<open>Bit_Operations.xor\<close> .
lift_definition mask_uint16 :: \<open>nat \<Rightarrow> uint16\<close> is mask .
lift_definition push_bit_uint16 :: \<open>nat \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is push_bit .
lift_definition drop_bit_uint16 :: \<open>nat \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is drop_bit .
lift_definition signed_drop_bit_uint16 :: \<open>nat \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is signed_drop_bit .
lift_definition take_bit_uint16 :: \<open>nat \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is take_bit .
lift_definition set_bit_uint16 :: \<open>nat \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is Bit_Operations.set_bit .
lift_definition unset_bit_uint16 :: \<open>nat \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is unset_bit .
lift_definition flip_bit_uint16 :: \<open>nat \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is flip_bit .

global_interpretation uint16: word_type_copy_bits Abs_uint16 Rep_uint16 signed_drop_bit_uint16
  by standard (fact bit_uint16.rep_eq not_uint16.rep_eq and_uint16.rep_eq or_uint16.rep_eq xor_uint16.rep_eq
    mask_uint16.rep_eq push_bit_uint16.rep_eq drop_bit_uint16.rep_eq signed_drop_bit_uint16.rep_eq take_bit_uint16.rep_eq
    set_bit_uint16.rep_eq unset_bit_uint16.rep_eq flip_bit_uint16.rep_eq)+

instance
  by (fact uint16.of_class_ring_bit_operations)

end

lift_definition uint16_of_nat :: \<open>nat \<Rightarrow> uint16\<close>
  is word_of_nat .

lift_definition nat_of_uint16 :: \<open>uint16 \<Rightarrow> nat\<close>
  is unat .

lift_definition uint16_of_int :: \<open>int \<Rightarrow> uint16\<close>
  is word_of_int .

lift_definition int_of_uint16 :: \<open>uint16 \<Rightarrow> int\<close>
  is uint .

context
  includes integer.lifting
begin

lift_definition Uint16 :: \<open>integer \<Rightarrow> uint16\<close>
  is word_of_int .

lift_definition integer_of_uint16 :: \<open>uint16 \<Rightarrow> integer\<close>
  is uint .

end

global_interpretation uint16: word_type_copy_more Abs_uint16 Rep_uint16 signed_drop_bit_uint16
  uint16_of_nat nat_of_uint16 uint16_of_int int_of_uint16 Uint16 integer_of_uint16
  apply standard
       apply (simp_all add: uint16_of_nat.rep_eq nat_of_uint16.rep_eq
         uint16_of_int.rep_eq int_of_uint16.rep_eq
         Uint16.rep_eq integer_of_uint16.rep_eq integer_eq_iff)
  done

instantiation uint16 :: "{size, msb, bit_comprehension}"
begin

lift_definition size_uint16 :: \<open>uint16 \<Rightarrow> nat\<close> is size .

lift_definition msb_uint16 :: \<open>uint16 \<Rightarrow> bool\<close> is msb .

lift_definition set_bits_uint16 :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> uint16\<close> is set_bits .
lift_definition set_bits_aux_uint16 :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> uint16 \<Rightarrow> uint16\<close> is set_bits_aux .

global_interpretation uint16: word_type_copy_misc Abs_uint16 Rep_uint16 signed_drop_bit_uint16
  uint16_of_nat nat_of_uint16 uint16_of_int int_of_uint16 Uint16 integer_of_uint16 16 set_bits_aux_uint16
  by (standard; transfer) simp_all

instance using uint16.of_class_bit_comprehension
  by simp_all standard

end

section \<open>Code setup\<close>

code_printing code_module Uint16 \<rightharpoonup> (SML_word)
\<open>(* Test that words can handle numbers between 0 and 15 *)
val _ = if 4 <= Word.wordSize then () else raise (Fail ("wordSize less than 4"));

structure Uint16 : sig
  val shiftl : Word16.word -> IntInf.int -> Word16.word
  val shiftr : Word16.word -> IntInf.int -> Word16.word
  val shiftr_signed : Word16.word -> IntInf.int -> Word16.word
  val test_bit : Word16.word -> IntInf.int -> bool
end = struct

fun shiftl x n =
  Word16.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word16.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word16.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word16.andb (x, Word16.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word16.fromInt 0

end; (* struct Uint16 *)\<close>
code_reserved (SML_word) Uint16

code_printing code_module Uint16 \<rightharpoonup> (Haskell)
 \<open>module Uint16(Int16, Word16) where

  import Data.Int(Int16)
  import Data.Word(Word16)\<close>
code_reserved (Haskell) Uint16

text \<open>Scala provides unsigned 16-bit numbers as Char.\<close>

code_printing code_module Uint16 \<rightharpoonup> (Scala)
\<open>object Uint16 {

def shiftl(x: scala.Char, n: BigInt) : scala.Char = (x << n.intValue).toChar

def shiftr(x: scala.Char, n: BigInt) : scala.Char = (x >>> n.intValue).toChar

def shiftr_signed(x: scala.Char, n: BigInt) : scala.Char = (x.toShort >> n.intValue).toChar

def test_bit(x: scala.Char, n: BigInt) : Boolean = (x & (1.toChar << n.intValue)) != 0

} /* object Uint16 */\<close>
code_reserved (Scala) Uint16

text \<open>
  Avoid @{term Abs_uint16} in generated code, use @{term Rep_uint16'} instead. 
  The symbolic implementations for code\_simp use @{term Rep_uint16}.

  The new destructor @{term Rep_uint16'} is executable.
  As the simplifier is given the [code abstract] equations literally, 
  we cannot implement @{term Rep_uint16} directly, because that makes code\_simp loop.

  If code generation raises Match, some equation probably contains @{term Rep_uint16} 
  ([code abstract] equations for @{typ uint16} may use @{term Rep_uint16} because
  these instances will be folded away.)

  To convert @{typ "16 word"} values into @{typ uint16}, use @{term "Abs_uint16'"}.
\<close>

definition Rep_uint16' where [simp]: "Rep_uint16' = Rep_uint16"

lemma Rep_uint16'_transfer [transfer_rule]:
  "rel_fun cr_uint16 (=) (\<lambda>x. x) Rep_uint16'"
unfolding Rep_uint16'_def by(rule uint16.rep_transfer)

lemma Rep_uint16'_code [code]: "Rep_uint16' x = (BITS n. bit x n)"
  by transfer (simp add: set_bits_bit_eq)

lift_definition Abs_uint16' :: "16 word \<Rightarrow> uint16" is "\<lambda>x :: 16 word. x" .

lemma Abs_uint16'_code [code]:
  "Abs_uint16' x = Uint16 (integer_of_int (uint x))"
including integer.lifting by transfer simp

declare [[code drop: "term_of_class.term_of :: uint16 \<Rightarrow> _"]]

lemma term_of_uint16_code [code]:
  defines "TR \<equiv> typerep.Typerep" and "bit0 \<equiv> STR ''Numeral_Type.bit0''" shows
  "term_of_class.term_of x = 
   Code_Evaluation.App (Code_Evaluation.Const (STR ''Uint16.uint16.Abs_uint16'') (TR (STR ''fun'') [TR (STR ''Word.word'') [TR bit0 [TR bit0 [TR bit0 [TR bit0 [TR (STR ''Numeral_Type.num1'') []]]]]], TR (STR ''Uint16.uint16'') []]))
       (term_of_class.term_of (Rep_uint16' x))"
by(simp add: term_of_anything)

lemma Uint16_code [code]: "Rep_uint16 (Uint16 i) = word_of_int (int_of_integer_symbolic i)"
unfolding Uint16_def int_of_integer_symbolic_def by(simp add: Abs_uint16_inverse)

code_printing
  type_constructor uint16 \<rightharpoonup>
  (SML_word) "Word16.word" and
  (Haskell) "Uint16.Word16" and
  (Scala) "scala.Char"
| constant Uint16 \<rightharpoonup>
  (SML_word) "Word16.fromLargeInt (IntInf.toLarge _)" and
  (Haskell) "(Prelude.fromInteger _ :: Uint16.Word16)" and
  (Haskell_Quickcheck) "(Prelude.fromInteger (Prelude.toInteger _) :: Uint16.Word16)" and
  (Scala) "_.charValue"
| constant "0 :: uint16" \<rightharpoonup>
  (SML_word) "(Word16.fromInt 0)" and
  (Haskell) "(0 :: Uint16.Word16)" and
  (Scala) "0"
| constant "1 :: uint16" \<rightharpoonup>
  (SML_word) "(Word16.fromInt 1)" and
  (Haskell) "(1 :: Uint16.Word16)" and
  (Scala) "1"
| constant "plus :: uint16 \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.+ ((_), (_))" and
  (Haskell) infixl 6 "+" and
  (Scala) "(_ +/ _).toChar"
| constant "uminus :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.~" and
  (Haskell) "negate" and
  (Scala) "(- _).toChar"
| constant "minus :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.- ((_), (_))" and
  (Haskell) infixl 6 "-" and
  (Scala) "(_ -/ _).toChar"
| constant "times :: uint16 \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.* ((_), (_))" and
  (Haskell) infixl 7 "*" and
  (Scala) "(_ */ _).toChar"
| constant "HOL.equal :: uint16 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML_word) "!((_ : Word16.word) = _)" and
  (Haskell) infix 4 "==" and
  (Scala) infixl 5 "=="
| class_instance uint16 :: equal \<rightharpoonup> (Haskell) -
| constant "less_eq :: uint16 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML_word) "Word16.<= ((_), (_))" and
  (Haskell) infix 4 "<=" and
  (Scala) infixl 4 "<="
| constant "less :: uint16 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML_word) "Word16.< ((_), (_))" and
  (Haskell) infix 4 "<" and
  (Scala) infixl 4 "<"
| constant "Bit_Operations.not :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.notb" and
  (Haskell) "Data'_Bits.complement" and
  (Scala) "_.unary'_~.toChar"
| constant "Bit_Operations.and :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.andb ((_),/ (_))" and
  (Haskell) infixl 7 "Data_Bits..&." and
  (Scala) "(_ & _).toChar"
| constant "Bit_Operations.or :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.orb ((_),/ (_))" and
  (Haskell) infixl 5 "Data_Bits..|." and
  (Scala) "(_ | _).toChar"
| constant "Bit_Operations.xor :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.xorb ((_),/ (_))" and
  (Haskell) "Data'_Bits.xor" and
  (Scala) "(_ ^ _).toChar"

definition uint16_div :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" 
where "uint16_div x y = (if y = 0 then undefined ((div) :: uint16 \<Rightarrow> _) x (0 :: uint16) else x div y)"

definition uint16_mod :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" 
where "uint16_mod x y = (if y = 0 then undefined ((mod) :: uint16 \<Rightarrow> _) x (0 :: uint16) else x mod y)"

context includes undefined_transfer begin

lemma div_uint16_code [code]: "x div y = (if y = 0 then 0 else uint16_div x y)"
unfolding uint16_div_def by transfer (simp add: word_div_def)

lemma mod_uint16_code [code]: "x mod y = (if y = 0 then x else uint16_mod x y)"
unfolding uint16_mod_def by transfer (simp add: word_mod_def)

lemma uint16_div_code [code]:
  "Rep_uint16 (uint16_div x y) =
  (if y = 0 then Rep_uint16 (undefined ((div) :: uint16 \<Rightarrow> _) x (0 :: uint16)) else Rep_uint16 x div Rep_uint16 y)"
unfolding uint16_div_def by transfer simp

lemma uint16_mod_code [code]:
  "Rep_uint16 (uint16_mod x y) =
  (if y = 0 then Rep_uint16 (undefined ((mod) :: uint16 \<Rightarrow> _) x (0 :: uint16)) else Rep_uint16 x mod Rep_uint16 y)"
unfolding uint16_mod_def by transfer simp

end

code_printing constant uint16_div \<rightharpoonup>
  (SML_word) "Word16.div ((_), (_))" and
  (Haskell) "Prelude.div" and
  (Scala) "(_ '/ _).toChar"
| constant uint16_mod \<rightharpoonup>
  (SML_word) "Word16.mod ((_), (_))" and
  (Haskell) "Prelude.mod" and
  (Scala) "(_ % _).toChar"

global_interpretation uint16: word_type_copy_target_language Abs_uint16 Rep_uint16 signed_drop_bit_uint16
  uint16_of_nat nat_of_uint16 uint16_of_int int_of_uint16 Uint16 integer_of_uint16 16 set_bits_aux_uint16 16 15
  defines uint16_test_bit = uint16.test_bit
    and uint16_shiftl = uint16.shiftl
    and uint16_shiftr = uint16.shiftr
    and uint16_sshiftr = uint16.sshiftr
  by standard simp_all

code_printing constant uint16_test_bit \<rightharpoonup>
  (SML_word) "Uint16.test'_bit" and
  (Haskell) "Data'_Bits.testBitBounded" and
  (Scala) "Uint16.test'_bit"

code_printing constant uint16_shiftl \<rightharpoonup>
  (SML_word) "Uint16.shiftl" and
  (Haskell) "Data'_Bits.shiftlBounded" and
  (Scala) "Uint16.shiftl"

code_printing constant uint16_shiftr \<rightharpoonup>
  (SML_word) "Uint16.shiftr" and
  (Haskell) "Data'_Bits.shiftrBounded" and
  (Scala) "Uint16.shiftr"

code_printing constant uint16_sshiftr \<rightharpoonup>
  (SML_word) "Uint16.shiftr'_signed" and
  (Haskell) 
    "(Prelude.fromInteger (Prelude.toInteger (Data'_Bits.shiftrBounded (Prelude.fromInteger (Prelude.toInteger _) :: Uint16.Int16) _)) :: Uint16.Word16)" and
  (Scala) "Uint16.shiftr'_signed"

lemma uint16_msb_test_bit: "msb x \<longleftrightarrow> bit (x :: uint16) 15"
  by transfer (simp add: msb_word_iff_bit)

lemma msb_uint16_code [code]: "msb x \<longleftrightarrow> uint16_test_bit x 15"
  by (simp add: uint16.test_bit_def uint16_msb_test_bit)

lemma uint16_of_int_code [code]: "uint16_of_int i = Uint16 (integer_of_int i)"
including integer.lifting by transfer simp

lemma int_of_uint16_code [code]:
  "int_of_uint16 x = int_of_integer (integer_of_uint16 x)"
  by (simp add: int_of_uint16.rep_eq integer_of_uint16_def)

lemma uint16_of_nat_code [code]:
  "uint16_of_nat = uint16_of_int \<circ> int"
  by transfer (simp add: fun_eq_iff)

lemma nat_of_uint16_code [code]:
  "nat_of_uint16 x = nat_of_integer (integer_of_uint16 x)"
  unfolding integer_of_uint16_def including integer.lifting by transfer simp

lemma integer_of_uint16_code [code]:
  "integer_of_uint16 n = integer_of_int (uint (Rep_uint16' n))"
unfolding integer_of_uint16_def by transfer auto

code_printing
  constant "integer_of_uint16" \<rightharpoonup>
  (SML_word) "Word16.toInt _ : IntInf.int" and
  (Haskell) "Prelude.toInteger" and
  (Scala) "BigInt"

section \<open>Quickcheck setup\<close>

definition uint16_of_natural :: "natural \<Rightarrow> uint16"
where "uint16_of_natural x \<equiv> Uint16 (integer_of_natural x)"

instantiation uint16 :: "{random, exhaustive, full_exhaustive}" begin
definition "random_uint16 \<equiv> qc_random_cnv uint16_of_natural"
definition "exhaustive_uint16 \<equiv> qc_exhaustive_cnv uint16_of_natural"
definition "full_exhaustive_uint16 \<equiv> qc_full_exhaustive_cnv uint16_of_natural"
instance ..
end

instantiation uint16 :: narrowing begin

interpretation quickcheck_narrowing_samples
  "\<lambda>i. let x = Uint16 i in (x, 0xFFFF - x)" "0"
  "Typerep.Typerep (STR ''Uint16.uint16'') []" .

definition "narrowing_uint16 d = qc_narrowing_drawn_from (narrowing_samples d) d"
declare [[code drop: "partial_term_of :: uint16 itself \<Rightarrow> _"]]
lemmas partial_term_of_uint16 [code] = partial_term_of_code

instance ..
end

end
