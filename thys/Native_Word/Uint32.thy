(*  Title:      Uint32.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Unsigned words of 32 bits\<close>

theory Uint32
  imports
    "HOL-Library.Code_Target_Bit_Shifts"
    Uint_Common
    Code_Target_Word
    Code_Int_Integer_Conversion
begin

section \<open>Type definition and primitive operations\<close>

typedef uint32 = \<open>UNIV :: 32 word set\<close> ..

global_interpretation uint32: word_type_copy Abs_uint32 Rep_uint32
  using type_definition_uint32 by (rule word_type_copy.intro)

setup_lifting type_definition_uint32

declare uint32.of_word_of [code abstype]

declare Quotient_uint32 [transfer_rule]

instantiation uint32 :: \<open>{comm_ring_1, semiring_modulo, equal, linorder}\<close>
begin

lift_definition zero_uint32 :: uint32 is 0 .
lift_definition one_uint32 :: uint32 is 1 .
lift_definition plus_uint32 :: \<open>uint32 \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is \<open>(+)\<close> .
lift_definition uminus_uint32 :: \<open>uint32 \<Rightarrow> uint32\<close> is uminus .
lift_definition minus_uint32 :: \<open>uint32 \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is \<open>(-)\<close> .
lift_definition times_uint32 :: \<open>uint32 \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is \<open>(*)\<close> .
lift_definition divide_uint32 :: \<open>uint32 \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is \<open>(div)\<close> .
lift_definition modulo_uint32 :: \<open>uint32 \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is \<open>(mod)\<close> .
lift_definition equal_uint32 :: \<open>uint32 \<Rightarrow> uint32 \<Rightarrow> bool\<close> is \<open>HOL.equal\<close> .
lift_definition less_eq_uint32 :: \<open>uint32 \<Rightarrow> uint32 \<Rightarrow> bool\<close> is \<open>(\<le>)\<close> .
lift_definition less_uint32 :: \<open>uint32 \<Rightarrow> uint32 \<Rightarrow> bool\<close> is \<open>(<)\<close> .

global_interpretation uint32: word_type_copy_ring Abs_uint32 Rep_uint32
  by standard (fact zero_uint32.rep_eq one_uint32.rep_eq
    plus_uint32.rep_eq uminus_uint32.rep_eq minus_uint32.rep_eq
    times_uint32.rep_eq divide_uint32.rep_eq modulo_uint32.rep_eq
    equal_uint32.rep_eq less_eq_uint32.rep_eq less_uint32.rep_eq)+

instance proof -
  show \<open>OFCLASS(uint32, comm_ring_1_class)\<close>
    by (rule uint32.of_class_comm_ring_1)
  show \<open>OFCLASS(uint32, semiring_modulo_class)\<close>
    by (fact uint32.of_class_semiring_modulo)
  show \<open>OFCLASS(uint32, equal_class)\<close>
    by (fact uint32.of_class_equal)
  show \<open>OFCLASS(uint32, linorder_class)\<close>
    by (fact uint32.of_class_linorder)
qed

end

instantiation uint32 :: ring_bit_operations
begin

lift_definition bit_uint32 :: \<open>uint32 \<Rightarrow> nat \<Rightarrow> bool\<close> is bit .
lift_definition not_uint32 :: \<open>uint32 \<Rightarrow> uint32\<close> is \<open>Bit_Operations.not\<close> .
lift_definition and_uint32 :: \<open>uint32 \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is \<open>Bit_Operations.and\<close> .
lift_definition or_uint32 :: \<open>uint32 \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is \<open>Bit_Operations.or\<close> .
lift_definition xor_uint32 :: \<open>uint32 \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is \<open>Bit_Operations.xor\<close> .
lift_definition mask_uint32 :: \<open>nat \<Rightarrow> uint32\<close> is mask .
lift_definition push_bit_uint32 :: \<open>nat \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is push_bit .
lift_definition drop_bit_uint32 :: \<open>nat \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is drop_bit .
lift_definition signed_drop_bit_uint32 :: \<open>nat \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is signed_drop_bit .
lift_definition take_bit_uint32 :: \<open>nat \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is take_bit .
lift_definition set_bit_uint32 :: \<open>nat \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is Bit_Operations.set_bit .
lift_definition unset_bit_uint32 :: \<open>nat \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is unset_bit .
lift_definition flip_bit_uint32 :: \<open>nat \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is flip_bit .

global_interpretation uint32: word_type_copy_bits Abs_uint32 Rep_uint32 signed_drop_bit_uint32
  by standard (fact bit_uint32.rep_eq not_uint32.rep_eq and_uint32.rep_eq or_uint32.rep_eq xor_uint32.rep_eq
    mask_uint32.rep_eq push_bit_uint32.rep_eq drop_bit_uint32.rep_eq signed_drop_bit_uint32.rep_eq take_bit_uint32.rep_eq
    set_bit_uint32.rep_eq unset_bit_uint32.rep_eq flip_bit_uint32.rep_eq)+

instance
  by (fact uint32.of_class_ring_bit_operations)

end

lift_definition uint32_of_nat :: \<open>nat \<Rightarrow> uint32\<close>
  is word_of_nat .

lift_definition nat_of_uint32 :: \<open>uint32 \<Rightarrow> nat\<close>
  is unat .

lift_definition uint32_of_int :: \<open>int \<Rightarrow> uint32\<close>
  is word_of_int .

lift_definition int_of_uint32 :: \<open>uint32 \<Rightarrow> int\<close>
  is uint .

context
  includes integer.lifting
begin

lift_definition Uint32 :: \<open>integer \<Rightarrow> uint32\<close>
  is word_of_int .

lift_definition integer_of_uint32 :: \<open>uint32 \<Rightarrow> integer\<close>
  is uint .

end

global_interpretation uint32: word_type_copy_more Abs_uint32 Rep_uint32 signed_drop_bit_uint32
  uint32_of_nat nat_of_uint32 uint32_of_int int_of_uint32 Uint32 integer_of_uint32
  apply standard
       apply (simp_all add: uint32_of_nat.rep_eq nat_of_uint32.rep_eq
         uint32_of_int.rep_eq int_of_uint32.rep_eq
         Uint32.rep_eq integer_of_uint32.rep_eq integer_eq_iff)
  done

instantiation uint32 :: "{size, msb, bit_comprehension}"
begin

lift_definition size_uint32 :: \<open>uint32 \<Rightarrow> nat\<close> is size .

lift_definition msb_uint32 :: \<open>uint32 \<Rightarrow> bool\<close> is msb .

lift_definition set_bits_uint32 :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> uint32\<close> is set_bits .
lift_definition set_bits_aux_uint32 :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> uint32 \<Rightarrow> uint32\<close> is set_bits_aux .

global_interpretation uint32: word_type_copy_misc Abs_uint32 Rep_uint32 signed_drop_bit_uint32
  uint32_of_nat nat_of_uint32 uint32_of_int int_of_uint32 Uint32 integer_of_uint32 32 set_bits_aux_uint32
  by (standard; transfer) simp_all

instance using uint32.of_class_bit_comprehension
  by simp_all standard

end

section \<open>Code setup\<close>

code_printing code_module Uint32 \<rightharpoonup> (SML)
\<open>(* Test that words can handle numbers between 0 and 31 *)
val _ = if 5 <= Word.wordSize then () else raise (Fail ("wordSize less than 5"));

structure Uint32 : sig
  val shiftl : Word32.word -> IntInf.int -> Word32.word
  val shiftr : Word32.word -> IntInf.int -> Word32.word
  val shiftr_signed : Word32.word -> IntInf.int -> Word32.word
  val test_bit : Word32.word -> IntInf.int -> bool
end = struct

fun shiftl x n =
  Word32.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word32.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word32.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word32.andb (x, Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word32.fromInt 0

end; (* struct Uint32 *)\<close>
code_reserved (SML) Uint32

code_printing code_module Uint32 \<rightharpoonup> (Haskell)
 \<open>module Uint32(Int32, Word32) where

  import Data.Int(Int32)
  import Data.Word(Word32)\<close>
code_reserved (Haskell) Uint32

text \<open>
  OCaml and Scala provide only signed 32bit numbers, so we use these and 
  implement sign-sensitive operations like comparisons manually.
\<close>
code_printing code_module "Uint32" \<rightharpoonup> (OCaml)
\<open>module Uint32 : sig
  val less : int32 -> int32 -> bool
  val less_eq : int32 -> int32 -> bool
  val shiftl : int32 -> Z.t -> int32
  val shiftr : int32 -> Z.t -> int32
  val shiftr_signed : int32 -> Z.t -> int32
  val test_bit : int32 -> Z.t -> bool
end = struct

(* negative numbers have their highest bit set, 
   so they are greater than positive ones *)
let less x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y < 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y < 0;;

let less_eq x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y <= 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y <= 0;;

let shiftl x n = Int32.shift_left x (Z.to_int n);;

let shiftr x n = Int32.shift_right_logical x (Z.to_int n);;

let shiftr_signed x n = Int32.shift_right x (Z.to_int n);;

let test_bit x n =
  Int32.compare 
    (Int32.logand x (Int32.shift_left Int32.one (Z.to_int n)))
    Int32.zero
  <> 0;;

end;; (*struct Uint32*)\<close>
code_reserved (OCaml) Uint32

code_printing code_module Uint32 \<rightharpoonup> (Scala)
\<open>object Uint32 {

def less(x: Int, y: Int) : Boolean =
  x < 0 match {
    case true => y < 0 && x < y
    case false => y < 0 || x < y
  }

def less_eq(x: Int, y: Int) : Boolean =
  x < 0 match {
    case true => y < 0 && x <= y
    case false => y < 0 || x <= y
  }

def shiftl(x: Int, n: BigInt) : Int = x << n.intValue

def shiftr(x: Int, n: BigInt) : Int = x >>> n.intValue

def shiftr_signed(x: Int, n: BigInt) : Int = x >> n.intValue

def test_bit(x: Int, n: BigInt) : Boolean =
  (x & (1 << n.intValue)) != 0

} /* object Uint32 */\<close>
code_reserved (Scala) Uint32

text \<open>
  OCaml's conversion from Big\_int to int32 demands that the value fits int a signed 32-bit integer.
  The following justifies the implementation.
\<close>

context
  includes bit_operations_syntax
begin

definition Uint32_signed :: "integer \<Rightarrow> uint32" 
where "Uint32_signed i = (if i < -(0x80000000) \<or> i \<ge> 0x80000000 then undefined Uint32 i else Uint32 i)"

lemma Uint32_code [code]:
  "Uint32 i = 
  (let i' = i AND 0xFFFFFFFF
   in if bit i' 31 then Uint32_signed (i' - 0x100000000) else Uint32_signed i')"
  including undefined_transfer and integer.lifting unfolding Uint32_signed_def
  apply transfer
  apply (subst word_of_int_via_signed)
     apply (auto simp add: push_bit_of_1 mask_eq_exp_minus_1 word_of_int_via_signed cong del: if_cong)
  done

lemma Uint32_signed_code [code]:
  "Rep_uint32 (Uint32_signed i) = 
  (if i < -(0x80000000) \<or> i \<ge> 0x80000000 then Rep_uint32 (undefined Uint32 i) else word_of_int (int_of_integer_symbolic i))"
unfolding Uint32_signed_def Uint32_def int_of_integer_symbolic_def 
by(simp add: Abs_uint32_inverse)

end

text \<open>
  Avoid @{term Abs_uint32} in generated code, use @{term Rep_uint32'} instead. 
  The symbolic implementations for code\_simp use @{term Rep_uint32}.

  The new destructor @{term Rep_uint32'} is executable.
  As the simplifier is given the [code abstract] equations literally, 
  we cannot implement @{term Rep_uint32} directly, because that makes code\_simp loop.

  If code generation raises Match, some equation probably contains @{term Rep_uint32} 
  ([code abstract] equations for @{typ uint32} may use @{term Rep_uint32} because
  these instances will be folded away.)

  To convert @{typ "32 word"} values into @{typ uint32}, use @{term "Abs_uint32'"}.
\<close>

definition Rep_uint32' where [simp]: "Rep_uint32' = Rep_uint32"

lemma Rep_uint32'_transfer [transfer_rule]:
  "rel_fun cr_uint32 (=) (\<lambda>x. x) Rep_uint32'"
unfolding Rep_uint32'_def by(rule uint32.rep_transfer)

lemma Rep_uint32'_code [code]: "Rep_uint32' x = (BITS n. bit x n)"
  by transfer (simp add: set_bits_bit_eq) 

lift_definition Abs_uint32' :: "32 word \<Rightarrow> uint32" is "\<lambda>x :: 32 word. x" .

lemma Abs_uint32'_code [code]:
  "Abs_uint32' x = Uint32 (integer_of_int (uint x))"
including integer.lifting by transfer simp

declare [[code drop: "term_of_class.term_of :: uint32 \<Rightarrow> _"]]

lemma term_of_uint32_code [code]:
  defines "TR \<equiv> typerep.Typerep" and "bit0 \<equiv> STR ''Numeral_Type.bit0''" 
  shows
  "term_of_class.term_of x = 
   Code_Evaluation.App (Code_Evaluation.Const (STR ''Uint32.uint32.Abs_uint32'') (TR (STR ''fun'') [TR (STR ''Word.word'') [TR bit0 [TR bit0 [TR bit0 [TR bit0 [TR bit0 [TR (STR ''Numeral_Type.num1'') []]]]]]], TR (STR ''Uint32.uint32'') []]))
       (term_of_class.term_of (Rep_uint32' x))"
by(simp add: term_of_anything)

code_printing
  type_constructor uint32 \<rightharpoonup>
  (SML) "Word32.word" and
  (Haskell) "Uint32.Word32" and
  (OCaml) "int32" and
  (Scala) "Int" and
  (Eval) "Word32.word"
| constant Uint32 \<rightharpoonup>
  (SML) "Word32.fromLargeInt (IntInf.toLarge _)" and
  (Haskell) "(Prelude.fromInteger _ :: Uint32.Word32)" and
  (Haskell_Quickcheck) "(Prelude.fromInteger (Prelude.toInteger _) :: Uint32.Word32)" and
  (Scala) "_.intValue"
| constant Uint32_signed \<rightharpoonup>
  (OCaml) "Z.to'_int32"
| constant "0 :: uint32" \<rightharpoonup>
  (SML) "(Word32.fromInt 0)" and
  (Haskell) "(0 :: Uint32.Word32)" and
  (OCaml) "Int32.zero" and
  (Scala) "0"
| constant "1 :: uint32" \<rightharpoonup>
  (SML) "(Word32.fromInt 1)" and
  (Haskell) "(1 :: Uint32.Word32)" and
  (OCaml) "Int32.one" and
  (Scala) "1"
| constant "plus :: uint32 \<Rightarrow> _ " \<rightharpoonup>
  (SML) "Word32.+ ((_), (_))" and
  (Haskell) infixl 6 "+" and
  (OCaml) "Int32.add" and
  (Scala) infixl 7 "+"
| constant "uminus :: uint32 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word32.~" and
  (Haskell) "negate" and
  (OCaml) "Int32.neg" and
  (Scala) "!(- _)"
| constant "minus :: uint32 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word32.- ((_), (_))" and
  (Haskell) infixl 6 "-" and
  (OCaml) "Int32.sub" and
  (Scala) infixl 7 "-"
| constant "times :: uint32 \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word32.* ((_), (_))" and
  (Haskell) infixl 7 "*" and
  (OCaml) "Int32.mul" and
  (Scala) infixl 8 "*"
| constant "HOL.equal :: uint32 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML) "!((_ : Word32.word) = _)" and
  (Haskell) infix 4 "==" and
  (OCaml) "(Int32.compare _ _ = 0)" and
  (Scala) infixl 5 "=="
| class_instance uint32 :: equal \<rightharpoonup>
  (Haskell) -
| constant "less_eq :: uint32 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Word32.<= ((_), (_))" and
  (Haskell) infix 4 "<=" and
  (OCaml) "Uint32.less'_eq" and
  (Scala) "Uint32.less'_eq"
| constant "less :: uint32 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Word32.< ((_), (_))" and
  (Haskell) infix 4 "<" and
  (OCaml) "Uint32.less" and
  (Scala) "Uint32.less"
| constant "Bit_Operations.not :: uint32 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word32.notb" and
  (Haskell) "Data'_Bits.complement" and
  (OCaml) "Int32.lognot" and
  (Scala) "_.unary'_~"
| constant "Bit_Operations.and :: uint32 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word32.andb ((_),/ (_))" and
  (Haskell) infixl 7 "Data_Bits..&." and
  (OCaml) "Int32.logand" and
  (Scala) infixl 3 "&"
| constant "Bit_Operations.or :: uint32 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word32.orb ((_),/ (_))" and
  (Haskell) infixl 5 "Data_Bits..|." and
  (OCaml) "Int32.logor" and
  (Scala) infixl 1 "|"
| constant "Bit_Operations.xor :: uint32 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word32.xorb ((_),/ (_))" and
  (Haskell) "Data'_Bits.xor" and
  (OCaml) "Int32.logxor" and
  (Scala) infixl 2 "^"

definition uint32_divmod :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32 \<times> uint32" where
  "uint32_divmod x y = 
  (if y = 0 then (undefined ((div) :: uint32 \<Rightarrow> _) x (0 :: uint32), undefined ((mod) :: uint32 \<Rightarrow> _) x (0 :: uint32)) 
  else (x div y, x mod y))"

definition uint32_div :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" 
where "uint32_div x y = fst (uint32_divmod x y)"

definition uint32_mod :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" 
where "uint32_mod x y = snd (uint32_divmod x y)"

lemma div_uint32_code [code]: "x div y = (if y = 0 then 0 else uint32_div x y)"
including undefined_transfer unfolding uint32_divmod_def uint32_div_def
by transfer (simp add: word_div_def)

lemma mod_uint32_code [code]: "x mod y = (if y = 0 then x else uint32_mod x y)"
including undefined_transfer unfolding uint32_mod_def uint32_divmod_def
by transfer (simp add: word_mod_def)

definition uint32_sdiv :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32"
where [code del]:
  "uint32_sdiv x y =
   (if y = 0 then undefined ((div) :: uint32 \<Rightarrow> _) x (0 :: uint32)
    else Abs_uint32 (Rep_uint32 x sdiv Rep_uint32 y))"

definition div0_uint32 :: "uint32 \<Rightarrow> uint32"
where [code del]: "div0_uint32 x = undefined ((div) :: uint32 \<Rightarrow> _) x (0 :: uint32)"
declare [[code abort: div0_uint32]]

definition mod0_uint32 :: "uint32 \<Rightarrow> uint32"
where [code del]: "mod0_uint32 x = undefined ((mod) :: uint32 \<Rightarrow> _) x (0 :: uint32)"
declare [[code abort: mod0_uint32]]

lemma uint32_divmod_code [code]:
  "uint32_divmod x y =
  (if 0x80000000 \<le> y then if x < y then (0, x) else (1, x - y)
   else if y = 0 then (div0_uint32 x, mod0_uint32 x)
   else let q = push_bit 1 (uint32_sdiv (drop_bit 1 x) y);
            r = x - q * y
        in if r \<ge> y then (q + 1, r - y) else (q, r))"
  including undefined_transfer unfolding uint32_divmod_def uint32_sdiv_def div0_uint32_def mod0_uint32_def
    less_eq_uint32.rep_eq
  apply transfer
  apply (simp add: divmod_via_sdivmod push_bit_eq_mult)
  done

lemma uint32_sdiv_code [code]:
  "Rep_uint32 (uint32_sdiv x y) =
   (if y = 0 then Rep_uint32 (undefined ((div) :: uint32 \<Rightarrow> _) x (0 :: uint32))
    else Rep_uint32 x sdiv Rep_uint32 y)"
unfolding uint32_sdiv_def by(simp add: Abs_uint32_inverse)

text \<open>
  Note that we only need a translation for signed division, but not for the remainder
  because @{thm uint32_divmod_code} computes both with division only.
\<close>

code_printing
  constant uint32_div \<rightharpoonup>
  (SML) "Word32.div ((_), (_))" and
  (Haskell) "Prelude.div"
| constant uint32_mod \<rightharpoonup>
  (SML) "Word32.mod ((_), (_))" and
  (Haskell) "Prelude.mod"
| constant uint32_divmod \<rightharpoonup>
  (Haskell) "divmod"
| constant uint32_sdiv \<rightharpoonup>
  (OCaml) "Int32.div" and
  (Scala) "_ '/ _"

global_interpretation uint32: word_type_copy_target_language Abs_uint32 Rep_uint32 signed_drop_bit_uint32
  uint32_of_nat nat_of_uint32 uint32_of_int int_of_uint32 Uint32 integer_of_uint32 32 set_bits_aux_uint32 32 31
  defines uint32_test_bit = uint32.test_bit
    and uint32_shiftl = uint32.shiftl
    and uint32_shiftr = uint32.shiftr
    and uint32_sshiftr = uint32.sshiftr
  by standard simp_all

code_printing constant uint32_test_bit \<rightharpoonup>
  (SML) "Uint32.test'_bit" and
  (Haskell) "Data'_Bits.testBitBounded" and
  (OCaml) "Uint32.test'_bit" and
  (Scala) "Uint32.test'_bit" and
  (Eval) "(fn w => fn n => if n < 0 orelse 32 <= n then raise (Fail \"argument to uint32'_test'_bit out of bounds\") else Uint32.test'_bit w n)"

code_printing constant uint32_shiftl \<rightharpoonup>
  (SML) "Uint32.shiftl" and
  (Haskell) "Data'_Bits.shiftlBounded" and
  (OCaml) "Uint32.shiftl" and
  (Scala) "Uint32.shiftl" and
  (Eval) "(fn w => fn i => if i < 0 orelse i >= 32 then raise Fail \"argument to uint32'_shiftl out of bounds\" else Uint32.shiftl w i)"

code_printing constant uint32_shiftr \<rightharpoonup>
  (SML) "Uint32.shiftr" and
  (Haskell) "Data'_Bits.shiftrBounded" and
  (OCaml) "Uint32.shiftr" and
  (Scala) "Uint32.shiftr" and
  (Eval) "(fn w => fn i => if i < 0 orelse i >= 32 then raise Fail \"argument to uint32'_shiftr out of bounds\" else Uint32.shiftr w i)"

code_printing constant uint32_sshiftr \<rightharpoonup>
  (SML) "Uint32.shiftr'_signed" and
  (Haskell) 
    "(Prelude.fromInteger (Prelude.toInteger (Data'_Bits.shiftrBounded (Prelude.fromInteger (Prelude.toInteger _) :: Uint32.Int32) _)) :: Uint32.Word32)" and
  (OCaml) "Uint32.shiftr'_signed" and
  (Scala) "Uint32.shiftr'_signed" and
  (Eval) "(fn w => fn i => if i < 0 orelse i >= 32 then raise Fail \"argument to uint32'_shiftr'_signed out of bounds\" else Uint32.shiftr'_signed w i)"

context
  includes bit_operations_syntax
begin

lemma uint32_msb_test_bit: "msb x \<longleftrightarrow> bit (x :: uint32) 31"
  by transfer (simp add: msb_word_iff_bit)

lemma msb_uint32_code [code]: "msb x \<longleftrightarrow> uint32_test_bit x 31"
  by (simp add: uint32.test_bit_def uint32_msb_test_bit)

lemma uint32_of_int_code [code]:
  "uint32_of_int i = Uint32 (integer_of_int i)"
  including integer.lifting by transfer simp

lemma int_of_uint32_code [code]:
  "int_of_uint32 x = int_of_integer (integer_of_uint32 x)"
  including integer.lifting by transfer simp

lemma uint32_of_nat_code [code]:
  "uint32_of_nat = uint32_of_int \<circ> int"
  by transfer (simp add: fun_eq_iff)

lemma nat_of_uint32_code [code]:
  "nat_of_uint32 x = nat_of_integer (integer_of_uint32 x)"
  unfolding integer_of_uint32_def including integer.lifting by transfer simp

definition integer_of_uint32_signed :: "uint32 \<Rightarrow> integer"
where
  "integer_of_uint32_signed n = (if bit n 31 then undefined integer_of_uint32 n else integer_of_uint32 n)"

lemma integer_of_uint32_signed_code [code]:
  "integer_of_uint32_signed n =
  (if bit n 31 then undefined integer_of_uint32 n else integer_of_int (uint (Rep_uint32' n)))"
  by (simp add: integer_of_uint32_signed_def integer_of_uint32_def)

lemma integer_of_uint32_code [code]:
  "integer_of_uint32 n =
  (if bit n 31 then integer_of_uint32_signed (n AND 0x7FFFFFFF) OR 0x80000000 else integer_of_uint32_signed n)"
proof -
  have \<open>integer_of_uint32_signed (n AND 0x7FFFFFFF) OR 0x80000000 = Bit_Operations.set_bit 31 (integer_of_uint32_signed (take_bit 31 n))\<close>
    by (simp add: take_bit_eq_mask set_bit_eq_or push_bit_eq_mult mask_eq_exp_minus_1)
  moreover have \<open>integer_of_uint32 n = Bit_Operations.set_bit 31 (integer_of_uint32 (take_bit 31 n))\<close> if \<open>bit n 31\<close>
  proof (rule bit_eqI)
    fix m
    from that show \<open>bit (integer_of_uint32 n) m = bit (Bit_Operations.set_bit 31 (integer_of_uint32 (take_bit 31 n))) m\<close> for m
      including integer.lifting by transfer (auto simp add: bit_simps dest: bit_imp_le_length)
  qed
  ultimately show ?thesis
    by simp (simp add: integer_of_uint32_signed_def bit_simps)
qed

end

code_printing
  constant "integer_of_uint32" \<rightharpoonup>
  (SML) "IntInf.fromLarge (Word32.toLargeInt _) : IntInf.int" and
  (Haskell) "Prelude.toInteger"
| constant "integer_of_uint32_signed" \<rightharpoonup>
  (OCaml) "Z.of'_int32" and
  (Scala) "BigInt"

section \<open>Quickcheck setup\<close>

definition uint32_of_natural :: "natural \<Rightarrow> uint32"
where "uint32_of_natural x \<equiv> Uint32 (integer_of_natural x)"

instantiation uint32 :: "{random, exhaustive, full_exhaustive}" begin
definition "random_uint32 \<equiv> qc_random_cnv uint32_of_natural"
definition "exhaustive_uint32 \<equiv> qc_exhaustive_cnv uint32_of_natural"
definition "full_exhaustive_uint32 \<equiv> qc_full_exhaustive_cnv uint32_of_natural"
instance ..
end

instantiation uint32 :: narrowing begin

interpretation quickcheck_narrowing_samples
  "\<lambda>i. let x = Uint32 i in (x, 0xFFFFFFFF - x)" "0"
  "Typerep.Typerep (STR ''Uint32.uint32'') []" .

definition "narrowing_uint32 d = qc_narrowing_drawn_from (narrowing_samples d) d"
declare [[code drop: "partial_term_of :: uint32 itself \<Rightarrow> _"]]
lemmas partial_term_of_uint32 [code] = partial_term_of_code

instance ..
end

end
