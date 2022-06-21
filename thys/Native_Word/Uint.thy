(*  Title:      Uint.thy
    Author:     Peter Lammich, TU Munich
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Unsigned words of default size\<close>

theory Uint imports
  Word_Type_Copies
  Code_Target_Integer_Bit
begin

text \<open>
  This theory provides access to words in the target languages of the code generator
  whose bit width is the default of the target language. To that end, the type \<open>uint\<close>
  models words of width \<open>dflt_size\<close>, but \<open>dflt_size\<close> is known only to be positive.

  Usage restrictions:
  Default-size words (type \<open>uint\<close>) cannot be used for evaluation, because 
  the results depend on the particular choice of word size in the target language
  and implementation. Symbolic evaluation has not yet been set up for \<open>uint\<close>.
\<close>

text \<open>The default size type\<close>
typedecl dflt_size

instantiation dflt_size :: typerep begin
definition "typerep_class.typerep \<equiv>  \<lambda>_ :: dflt_size itself. Typerep.Typerep (STR ''Uint.dflt_size'') []"
instance ..
end

consts dflt_size_aux :: "nat"
specification (dflt_size_aux) dflt_size_aux_g0: "dflt_size_aux > 0"
  by auto
hide_fact dflt_size_aux_def

instantiation dflt_size :: len begin
definition "len_of_dflt_size (_ :: dflt_size itself) \<equiv> dflt_size_aux"
instance by(intro_classes)(simp add: len_of_dflt_size_def dflt_size_aux_g0)
end

abbreviation "dflt_size \<equiv> len_of (TYPE (dflt_size))"

context includes integer.lifting begin
lift_definition dflt_size_integer :: integer is "int dflt_size" .
declare dflt_size_integer_def[code del]
  \<comment> \<open>The code generator will substitute a machine-dependent value for this constant\<close>

lemma dflt_size_by_int[code]: "dflt_size = nat_of_integer dflt_size_integer"
by transfer simp

lemma dflt_size[simp]: 
  "dflt_size > 0"
  "dflt_size \<ge> Suc 0"
  "\<not> dflt_size < Suc 0"
  using len_gt_0[where 'a=dflt_size]
  by (simp_all del: len_gt_0)
end

section \<open>Type definition and primitive operations\<close>

typedef uint = \<open>UNIV :: dflt_size word set\<close> ..

global_interpretation uint: word_type_copy Abs_uint Rep_uint
  using type_definition_uint by (rule word_type_copy.intro)

setup_lifting type_definition_uint

declare uint.of_word_of [code abstype]

declare Quotient_uint [transfer_rule]

instantiation uint :: \<open>{comm_ring_1, semiring_modulo, equal, linorder}\<close>
begin

lift_definition zero_uint :: uint is 0 .
lift_definition one_uint :: uint is 1 .
lift_definition plus_uint :: \<open>uint \<Rightarrow> uint \<Rightarrow> uint\<close> is \<open>(+)\<close> .
lift_definition uminus_uint :: \<open>uint \<Rightarrow> uint\<close> is uminus .
lift_definition minus_uint :: \<open>uint \<Rightarrow> uint \<Rightarrow> uint\<close> is \<open>(-)\<close> .
lift_definition times_uint :: \<open>uint \<Rightarrow> uint \<Rightarrow> uint\<close> is \<open>(*)\<close> .
lift_definition divide_uint :: \<open>uint \<Rightarrow> uint \<Rightarrow> uint\<close> is \<open>(div)\<close> .
lift_definition modulo_uint :: \<open>uint \<Rightarrow> uint \<Rightarrow> uint\<close> is \<open>(mod)\<close> .
lift_definition equal_uint :: \<open>uint \<Rightarrow> uint \<Rightarrow> bool\<close> is \<open>HOL.equal\<close> .
lift_definition less_eq_uint :: \<open>uint \<Rightarrow> uint \<Rightarrow> bool\<close> is \<open>(\<le>)\<close> .
lift_definition less_uint :: \<open>uint \<Rightarrow> uint \<Rightarrow> bool\<close> is \<open>(<)\<close> .

global_interpretation uint: word_type_copy_ring Abs_uint Rep_uint
  by standard (fact zero_uint.rep_eq one_uint.rep_eq
    plus_uint.rep_eq uminus_uint.rep_eq minus_uint.rep_eq
    times_uint.rep_eq divide_uint.rep_eq modulo_uint.rep_eq
    equal_uint.rep_eq less_eq_uint.rep_eq less_uint.rep_eq)+

instance proof -
  show \<open>OFCLASS(uint, comm_ring_1_class)\<close>
    by (rule uint.of_class_comm_ring_1)
  show \<open>OFCLASS(uint, semiring_modulo_class)\<close>
    by (fact uint.of_class_semiring_modulo)
  show \<open>OFCLASS(uint, equal_class)\<close>
    by (fact uint.of_class_equal)
  show \<open>OFCLASS(uint, linorder_class)\<close>
    by (fact uint.of_class_linorder)
qed

end

instantiation uint :: ring_bit_operations
begin

lift_definition bit_uint :: \<open>uint \<Rightarrow> nat \<Rightarrow> bool\<close> is bit .
lift_definition not_uint :: \<open>uint \<Rightarrow> uint\<close> is \<open>Bit_Operations.not\<close> .
lift_definition and_uint :: \<open>uint \<Rightarrow> uint \<Rightarrow> uint\<close> is \<open>Bit_Operations.and\<close> .
lift_definition or_uint :: \<open>uint \<Rightarrow> uint \<Rightarrow> uint\<close> is \<open>Bit_Operations.or\<close> .
lift_definition xor_uint :: \<open>uint \<Rightarrow> uint \<Rightarrow> uint\<close> is \<open>Bit_Operations.xor\<close> .
lift_definition mask_uint :: \<open>nat \<Rightarrow> uint\<close> is mask .
lift_definition push_bit_uint :: \<open>nat \<Rightarrow> uint \<Rightarrow> uint\<close> is push_bit .
lift_definition drop_bit_uint :: \<open>nat \<Rightarrow> uint \<Rightarrow> uint\<close> is drop_bit .
lift_definition signed_drop_bit_uint :: \<open>nat \<Rightarrow> uint \<Rightarrow> uint\<close> is signed_drop_bit .
lift_definition take_bit_uint :: \<open>nat \<Rightarrow> uint \<Rightarrow> uint\<close> is take_bit .
lift_definition set_bit_uint :: \<open>nat \<Rightarrow> uint \<Rightarrow> uint\<close> is Bit_Operations.set_bit .
lift_definition unset_bit_uint :: \<open>nat \<Rightarrow> uint \<Rightarrow> uint\<close> is unset_bit .
lift_definition flip_bit_uint :: \<open>nat \<Rightarrow> uint \<Rightarrow> uint\<close> is flip_bit .

global_interpretation uint: word_type_copy_bits Abs_uint Rep_uint signed_drop_bit_uint
  by standard (fact bit_uint.rep_eq not_uint.rep_eq and_uint.rep_eq or_uint.rep_eq xor_uint.rep_eq
    mask_uint.rep_eq push_bit_uint.rep_eq drop_bit_uint.rep_eq signed_drop_bit_uint.rep_eq take_bit_uint.rep_eq
    set_bit_uint.rep_eq unset_bit_uint.rep_eq flip_bit_uint.rep_eq)+

instance
  by (fact uint.of_class_ring_bit_operations)

end

lift_definition uint_of_nat :: \<open>nat \<Rightarrow> uint\<close>
  is word_of_nat .

lift_definition nat_of_uint :: \<open>uint \<Rightarrow> nat\<close>
  is unat .

lift_definition uint_of_int :: \<open>int \<Rightarrow> uint\<close>
  is word_of_int .

lift_definition int_of_uint :: \<open>uint \<Rightarrow> int\<close>
  is uint .

context
  includes integer.lifting
begin

lift_definition Uint :: \<open>integer \<Rightarrow> uint\<close>
  is word_of_int .

lift_definition integer_of_uint :: \<open>uint \<Rightarrow> integer\<close>
  is uint .

end

global_interpretation uint: word_type_copy_more Abs_uint Rep_uint signed_drop_bit_uint
  uint_of_nat nat_of_uint uint_of_int int_of_uint Uint integer_of_uint
  apply standard
       apply (simp_all add: uint_of_nat.rep_eq nat_of_uint.rep_eq
         uint_of_int.rep_eq int_of_uint.rep_eq
         Uint.rep_eq integer_of_uint.rep_eq integer_eq_iff)
  done

instantiation uint :: "{size, msb, lsb, set_bit, bit_comprehension}"
begin

lift_definition size_uint :: \<open>uint \<Rightarrow> nat\<close> is size .

lift_definition msb_uint :: \<open>uint \<Rightarrow> bool\<close> is msb .
lift_definition lsb_uint :: \<open>uint \<Rightarrow> bool\<close> is lsb .

text \<open>Workaround: avoid name space clash by spelling out \<^text>\<open>lift_definition\<close> explicitly.\<close>

definition set_bit_uint :: \<open>uint \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> uint\<close>
  where set_bit_uint_eq: \<open>set_bit_uint a n b = (if b then Bit_Operations.set_bit else unset_bit) n a\<close>

context
  includes lifting_syntax
begin

lemma set_bit_uint_transfer [transfer_rule]:
  \<open>(cr_uint ===> (=) ===> (\<longleftrightarrow>) ===> cr_uint) Generic_set_bit.set_bit Generic_set_bit.set_bit\<close>
  by (simp only: set_bit_eq [abs_def] set_bit_uint_eq [abs_def]) transfer_prover

end

lift_definition set_bits_uint :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> uint\<close> is set_bits .
lift_definition set_bits_aux_uint :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> uint \<Rightarrow> uint\<close> is set_bits_aux .

global_interpretation uint: word_type_copy_misc Abs_uint Rep_uint signed_drop_bit_uint
  uint_of_nat nat_of_uint uint_of_int int_of_uint Uint integer_of_uint dflt_size set_bits_aux_uint
  by (standard; transfer) simp_all

instance using uint.of_class_bit_comprehension
  uint.of_class_set_bit uint.of_class_lsb
  by simp_all standard

end

section \<open>Code setup\<close>

code_printing code_module Uint \<rightharpoonup> (SML)
\<open>
structure Uint : sig
  val set_bit : Word.word -> IntInf.int -> bool -> Word.word
  val shiftl : Word.word -> IntInf.int -> Word.word
  val shiftr : Word.word -> IntInf.int -> Word.word
  val shiftr_signed : Word.word -> IntInf.int -> Word.word
  val test_bit : Word.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word.orb (x, mask)
     else Word.andb (x, Word.notb mask)
  end

fun shiftl x n =
  Word.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word.andb (x, Word.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word.fromInt 0

end; (* struct Uint *)\<close>
code_reserved SML Uint

code_printing code_module Uint \<rightharpoonup> (Haskell)
 \<open>module Uint(Int, Word, dflt_size) where

  import qualified Prelude
  import Data.Int(Int)
  import Data.Word(Word)
  import qualified Data.Bits

  dflt_size :: Prelude.Integer
  dflt_size = Prelude.toInteger (bitSize_aux (0::Word)) where
    bitSize_aux :: (Data.Bits.Bits a, Prelude.Bounded a) => a -> Int
    bitSize_aux = Data.Bits.bitSize\<close>
  and (Haskell_Quickcheck)
 \<open>module Uint(Int, Word, dflt_size) where

  import qualified Prelude
  import Data.Int(Int)
  import Data.Word(Word)
  import qualified Data.Bits

  dflt_size :: Prelude.Int
  dflt_size = bitSize_aux (0::Word) where
    bitSize_aux :: (Data.Bits.Bits a, Prelude.Bounded a) => a -> Int
    bitSize_aux = Data.Bits.bitSize
\<close>
code_reserved Haskell Uint dflt_size

text \<open>
  OCaml and Scala provide only signed bit numbers, so we use these and 
  implement sign-sensitive operations like comparisons manually.
\<close>

code_printing code_module "Uint" \<rightharpoonup> (OCaml)
\<open>module Uint : sig
  type t = int
  val dflt_size : Z.t
  val less : t -> t -> bool
  val less_eq : t -> t -> bool
  val set_bit : t -> Z.t -> bool -> t
  val shiftl : t -> Z.t -> t
  val shiftr : t -> Z.t -> t
  val shiftr_signed : t -> Z.t -> t
  val test_bit : t -> Z.t -> bool
  val int_mask : int
  val int32_mask : int32
  val int64_mask : int64
end = struct

type t = int

let dflt_size = Z.of_int Sys.int_size;;

(* negative numbers have their highest bit set, 
   so they are greater than positive ones *)
let less x y =
  if x<0 then
    y<0 && x<y
  else y < 0 || x < y;;

let less_eq x y =
  if x < 0 then
    y < 0 &&  x <= y
  else y < 0 || x <= y;;

let set_bit x n b =
  let mask = 1 lsl (Z.to_int n)
  in if b then x lor mask
     else x land (lnot mask);;

let shiftl x n = x lsl (Z.to_int n);;

let shiftr x n = x lsr (Z.to_int n);;

let shiftr_signed x n = x asr (Z.to_int n);;

let test_bit x n = x land (1 lsl (Z.to_int n)) <> 0;;

let int_mask =
  if Sys.int_size < 32 then lnot 0 else 0xFFFFFFFF;;

let int32_mask = 
  if Sys.int_size < 32 then Int32.pred (Int32.shift_left Int32.one Sys.int_size)
  else Int32.of_string "0xFFFFFFFF";;

let int64_mask = 
  if Sys.int_size < 64 then Int64.pred (Int64.shift_left Int64.one Sys.int_size)
  else Int64.of_string "0xFFFFFFFFFFFFFFFF";;

end;; (*struct Uint*)\<close>
code_reserved OCaml Uint

code_printing code_module Uint \<rightharpoonup> (Scala)
\<open>object Uint {
def dflt_size : BigInt = BigInt(32)

def less(x: Int, y: Int) : Boolean =
  if (x < 0) y < 0 && x < y
  else y < 0 || x < y

def less_eq(x: Int, y: Int) : Boolean =
  if (x < 0) y < 0 && x <= y
  else y < 0 || x <= y

def set_bit(x: Int, n: BigInt, b: Boolean) : Int =
  if (b)
    x | (1 << n.intValue)
  else
    x & (1 << n.intValue).unary_~

def shiftl(x: Int, n: BigInt) : Int = x << n.intValue

def shiftr(x: Int, n: BigInt) : Int = x >>> n.intValue

def shiftr_signed(x: Int, n: BigInt) : Int = x >> n.intValue

def test_bit(x: Int, n: BigInt) : Boolean =
  (x & (1 << n.intValue)) != 0

} /* object Uint */\<close>
code_reserved Scala Uint


text \<open>
  OCaml's conversion from Big\_int to int demands that the value fits into a signed integer.
  The following justifies the implementation.
\<close>

context
  includes integer.lifting bit_operations_syntax
begin

definition wivs_mask :: int where "wivs_mask = 2^ dflt_size - 1"
lift_definition wivs_mask_integer :: integer is wivs_mask .
lemma [code]: "wivs_mask_integer = 2 ^ dflt_size - 1"
  by transfer (simp add: wivs_mask_def)

definition wivs_shift :: int where "wivs_shift = 2 ^ dflt_size"
lift_definition wivs_shift_integer :: integer is wivs_shift .
lemma [code]: "wivs_shift_integer = 2 ^ dflt_size"
  by transfer (simp add: wivs_shift_def)

definition wivs_index :: nat where "wivs_index == dflt_size - 1"
lift_definition wivs_index_integer :: integer is "int wivs_index".
lemma wivs_index_integer_code[code]: "wivs_index_integer = dflt_size_integer - 1"
  by transfer (simp add: wivs_index_def of_nat_diff)

definition wivs_overflow :: int where "wivs_overflow == 2^ (dflt_size - 1)"
lift_definition wivs_overflow_integer :: integer is wivs_overflow .
lemma [code]: "wivs_overflow_integer = 2 ^ (dflt_size - 1)"
  by transfer (simp add: wivs_overflow_def)

definition wivs_least :: int where "wivs_least == - wivs_overflow"
lift_definition wivs_least_integer :: integer is wivs_least .
lemma [code]: "wivs_least_integer = - (2 ^ (dflt_size - 1))"
  by transfer (simp add: wivs_overflow_def wivs_least_def)

definition Uint_signed :: "integer \<Rightarrow> uint" where
  "Uint_signed i = (if i < wivs_least_integer \<or> wivs_overflow_integer \<le> i then undefined Uint i else Uint i)"

lemma Uint_code [code]:
  "Uint i = 
  (let i' = i AND wivs_mask_integer in 
   if bit i' wivs_index then Uint_signed (i' - wivs_shift_integer) else Uint_signed i')"
  including undefined_transfer 
  unfolding Uint_signed_def
  apply transfer
  apply (subst word_of_int_via_signed)
       apply (auto simp add: push_bit_of_1 mask_eq_exp_minus_1 word_of_int_via_signed
         wivs_mask_def wivs_index_def wivs_overflow_def wivs_least_def wivs_shift_def)
  done

lemma Uint_signed_code [code]:
  "Rep_uint (Uint_signed i) = 
  (if i < wivs_least_integer \<or> i \<ge> wivs_overflow_integer then Rep_uint (undefined Uint i) else word_of_int (int_of_integer_symbolic i))"
  unfolding Uint_signed_def Uint_def int_of_integer_symbolic_def by(simp add: Abs_uint_inverse)
end

text \<open>
  Avoid @{term Abs_uint} in generated code, use @{term Rep_uint'} instead. 
  The symbolic implementations for code\_simp use @{term Rep_uint}.

  The new destructor @{term Rep_uint'} is executable.
  As the simplifier is given the [code abstract] equations literally, 
  we cannot implement @{term Rep_uint} directly, because that makes code\_simp loop.

  If code generation raises Match, some equation probably contains @{term Rep_uint} 
  ([code abstract] equations for @{typ uint} may use @{term Rep_uint} because
  these instances will be folded away.)
\<close>

definition Rep_uint' where [simp]: "Rep_uint' = Rep_uint"

lemma Rep_uint'_code [code]: "Rep_uint' x = (BITS n. bit x n)"
  unfolding Rep_uint'_def by transfer (simp add: set_bits_bit_eq)

lift_definition Abs_uint' :: "dflt_size word \<Rightarrow> uint" is "\<lambda>x :: dflt_size word. x" .

lemma Abs_uint'_code [code]:
  "Abs_uint' x = Uint (integer_of_int (uint x))"
including integer.lifting by transfer simp

declare [[code drop: "term_of_class.term_of :: uint \<Rightarrow> _"]]

lemma term_of_uint_code [code]:
  defines "TR \<equiv> typerep.Typerep" and "bit0 \<equiv> STR ''Numeral_Type.bit0''" 
  shows
  "term_of_class.term_of x = 
   Code_Evaluation.App (Code_Evaluation.Const (STR ''Uint.uint.Abs_uint'') (TR (STR ''fun'') [TR (STR ''Word.word'')  [TR (STR ''Uint.dflt_size'') []], TR (STR ''Uint.uint'') []]))
       (term_of_class.term_of (Rep_uint' x))"
  by(simp add: term_of_anything)

text \<open>Important:
  We must prevent the reflection oracle (eval-tac) to 
  use our machine-dependent type.
\<close>

code_printing
  type_constructor uint \<rightharpoonup>
  (SML) "Word.word" and
  (Haskell) "Uint.Word" and
  (OCaml) "Uint.t" and
  (Scala) "Int" and
  (Eval) "*** \"Error: Machine dependent type\" ***" and
  (Quickcheck) "Word.word" 
| constant dflt_size_integer \<rightharpoonup>
  (SML) "(IntInf.fromLarge (Int.toLarge Word.wordSize))" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.wordSize" and
  (Haskell) "Uint.dflt'_size" and
  (OCaml) "Uint.dflt'_size" and
  (Scala) "Uint.dflt'_size"
| constant Uint \<rightharpoonup>
  (SML) "Word.fromLargeInt (IntInf.toLarge _)" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.fromInt" and
  (Haskell) "(Prelude.fromInteger _ :: Uint.Word)" and
  (Haskell_Quickcheck) "(Prelude.fromInteger (Prelude.toInteger _) :: Uint.Word)" and
  (Scala) "_.intValue"
| constant Uint_signed \<rightharpoonup>
  (OCaml) "Z.to'_int"
| constant "0 :: uint" \<rightharpoonup>
  (SML) "(Word.fromInt 0)" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "(Word.fromInt 0)" and
  (Haskell) "(0 :: Uint.Word)" and
  (OCaml) "0" and
  (Scala) "0"
| constant "1 :: uint" \<rightharpoonup>
  (SML) "(Word.fromInt 1)" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "(Word.fromInt 1)" and
  (Haskell) "(1 :: Uint.Word)" and
  (OCaml) "1" and
  (Scala) "1"
| constant "plus :: uint \<Rightarrow> _ " \<rightharpoonup>
  (SML) "Word.+ ((_), (_))" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.+ ((_), (_))" and
  (Haskell) infixl 6 "+" and
  (OCaml) "Pervasives.(+)" and
  (Scala) infixl 7 "+"
| constant "uminus :: uint \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word.~" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.~" and
  (Haskell) "negate" and
  (OCaml) "Pervasives.(~-)" and
  (Scala) "!(- _)"
| constant "minus :: uint \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word.- ((_), (_))" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.- ((_), (_))" and
  (Haskell) infixl 6 "-" and
  (OCaml) "Pervasives.(-)" and
  (Scala) infixl 7 "-"
| constant "times :: uint \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word.* ((_), (_))" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.* ((_), (_))" and
  (Haskell) infixl 7 "*" and
  (OCaml) "Pervasives.( * )" and
  (Scala) infixl 8 "*"
| constant "HOL.equal :: uint \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML) "!((_ : Word.word) = _)" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "!((_ : Word.word) = _)" and
  (Haskell) infix 4 "==" and
  (OCaml) "(Pervasives.(=):Uint.t -> Uint.t -> bool)" and
  (Scala) infixl 5 "=="
| class_instance uint :: equal \<rightharpoonup>
  (Haskell) -
| constant "less_eq :: uint \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Word.<= ((_), (_))" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.<= ((_), (_))" and
  (Haskell) infix 4 "<=" and
  (OCaml) "Uint.less'_eq" and
  (Scala) "Uint.less'_eq"
| constant "less :: uint \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Word.< ((_), (_))" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.< ((_), (_))" and
  (Haskell) infix 4 "<" and
  (OCaml) "Uint.less" and
  (Scala) "Uint.less"
| constant "Bit_Operations.not :: uint \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word.notb" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.notb" and
  (Haskell) "Data'_Bits.complement" and
  (OCaml) "Pervasives.lnot" and
  (Scala) "_.unary'_~"
| constant "Bit_Operations.and :: uint \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word.andb ((_),/ (_))" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.andb ((_),/ (_))" and
  (Haskell) infixl 7 "Data_Bits..&." and
  (OCaml) "Pervasives.(land)" and
  (Scala) infixl 3 "&"
| constant "Bit_Operations.or :: uint \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word.orb ((_),/ (_))" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.orb ((_),/ (_))" and
  (Haskell) infixl 5 "Data_Bits..|." and
  (OCaml) "Pervasives.(lor)" and
  (Scala) infixl 1 "|"
| constant "Bit_Operations.xor :: uint \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word.xorb ((_),/ (_))" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.xorb ((_),/ (_))" and
  (Haskell) "Data'_Bits.xor" and
  (OCaml) "Pervasives.(lxor)" and
  (Scala) infixl 2 "^"

definition uint_divmod :: "uint \<Rightarrow> uint \<Rightarrow> uint \<times> uint" where
  "uint_divmod x y = 
  (if y = 0 then (undefined ((div) :: uint \<Rightarrow> _) x (0 :: uint), undefined ((mod) :: uint \<Rightarrow> _) x (0 :: uint)) 
  else (x div y, x mod y))"

definition uint_div :: "uint \<Rightarrow> uint \<Rightarrow> uint" 
where "uint_div x y = fst (uint_divmod x y)"

definition uint_mod :: "uint \<Rightarrow> uint \<Rightarrow> uint" 
where "uint_mod x y = snd (uint_divmod x y)"

lemma div_uint_code [code]: "x div y = (if y = 0 then 0 else uint_div x y)"
including undefined_transfer unfolding uint_divmod_def uint_div_def
by transfer(simp add: word_div_def)

lemma mod_uint_code [code]: "x mod y = (if y = 0 then x else uint_mod x y)"
including undefined_transfer unfolding uint_mod_def uint_divmod_def
by transfer(simp add: word_mod_def)

definition uint_sdiv :: "uint \<Rightarrow> uint \<Rightarrow> uint"
where [code del]:
  "uint_sdiv x y =
   (if y = 0 then undefined ((div) :: uint \<Rightarrow> _) x (0 :: uint)
    else Abs_uint (Rep_uint x sdiv Rep_uint y))"

definition div0_uint :: "uint \<Rightarrow> uint"
where [code del]: "div0_uint x = undefined ((div) :: uint \<Rightarrow> _) x (0 :: uint)"
declare [[code abort: div0_uint]]

definition mod0_uint :: "uint \<Rightarrow> uint"
where [code del]: "mod0_uint x = undefined ((mod) :: uint \<Rightarrow> _) x (0 :: uint)"
declare [[code abort: mod0_uint]]

definition wivs_overflow_uint :: uint 
  where "wivs_overflow_uint \<equiv> push_bit (dflt_size - 1) 1"

lemma Rep_uint_wivs_overflow_uint_eq:
  \<open>Rep_uint wivs_overflow_uint = 2 ^ (dflt_size - Suc 0)\<close>
  by (simp add: wivs_overflow_uint_def one_uint.rep_eq push_bit_uint.rep_eq uint.word_of_power push_bit_eq_mult)

lemma wivs_overflow_uint_greater_eq_0:
  \<open>wivs_overflow_uint > 0\<close>
  apply (simp add: less_uint.rep_eq zero_uint.rep_eq Rep_uint_wivs_overflow_uint_eq)
  apply transfer
  apply (simp add: take_bit_push_bit push_bit_eq_mult)
  done

lemma uint_divmod_code [code]:
  "uint_divmod x y =
  (if wivs_overflow_uint \<le> y then if x < y then (0, x) else (1, x - y)
   else if y = 0 then (div0_uint x, mod0_uint x)
   else let q = push_bit 1 (uint_sdiv (drop_bit 1 x) y);
            r = x - q * y
        in if r \<ge> y then (q + 1, r - y) else (q, r))"
proof (cases \<open>y = 0\<close>)
  case True
  moreover have \<open>x \<ge> 0\<close>
    by transfer simp
  moreover note wivs_overflow_uint_greater_eq_0
  ultimately show ?thesis
    by (auto simp add: uint_divmod_def div0_uint_def mod0_uint_def not_less)
next
  case False
  then show ?thesis
    including undefined_transfer 
    unfolding uint_divmod_def uint_sdiv_def div0_uint_def mod0_uint_def
      wivs_overflow_uint_def
    apply transfer
    apply (simp add: divmod_via_sdivmod push_bit_of_1)
    done
qed

lemma uint_sdiv_code [code]:
  "Rep_uint (uint_sdiv x y) =
   (if y = 0 then Rep_uint (undefined ((div) :: uint \<Rightarrow> _) x (0 :: uint))
    else Rep_uint x sdiv Rep_uint y)"
unfolding uint_sdiv_def by(simp add: Abs_uint_inverse)

text \<open>
  Note that we only need a translation for signed division, but not for the remainder
  because @{thm uint_divmod_code} computes both with division only.
\<close>

code_printing
  constant uint_div \<rightharpoonup>
  (SML) "Word.div ((_), (_))" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.div ((_), (_))" and
  (Haskell) "Prelude.div"
| constant uint_mod \<rightharpoonup>
  (SML) "Word.mod ((_), (_))" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.mod ((_), (_))" and
  (Haskell) "Prelude.mod"
| constant uint_divmod \<rightharpoonup>
  (Haskell) "divmod"
| constant uint_sdiv \<rightharpoonup>
  (OCaml) "Pervasives.('/)" and
  (Scala) "_ '/ _"

definition uint_test_bit :: "uint \<Rightarrow> integer \<Rightarrow> bool"
where [code del]:
  "uint_test_bit x n =
  (if n < 0 \<or> dflt_size_integer \<le> n then undefined (bit :: uint \<Rightarrow> _) x n
   else bit x (nat_of_integer n))"

lemma test_bit_uint_code [code]:
  "bit x n \<longleftrightarrow> n < dflt_size \<and> uint_test_bit x (integer_of_nat n)"
  including undefined_transfer integer.lifting unfolding uint_test_bit_def
  by (transfer, simp, transfer, simp)

lemma uint_test_bit_code [code]:
  "uint_test_bit w n =
  (if n < 0 \<or> dflt_size_integer \<le> n then undefined (bit :: uint \<Rightarrow> _) w n else bit (Rep_uint w) (nat_of_integer n))"
  unfolding uint_test_bit_def by(simp add: bit_uint.rep_eq)

code_printing constant uint_test_bit \<rightharpoonup>
  (SML) "Uint.test'_bit" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Uint.test'_bit" and
  (Haskell) "Data'_Bits.testBitBounded" and
  (OCaml) "Uint.test'_bit" and
  (Scala) "Uint.test'_bit"

definition uint_set_bit :: "uint \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint"
where [code del]:
  "uint_set_bit x n b =
  (if n < 0 \<or> dflt_size_integer \<le> n then undefined (set_bit :: uint \<Rightarrow> _) x n b
   else set_bit x (nat_of_integer n) b)"

lemma set_bit_uint_code [code]:
  "set_bit x n b = (if n < dflt_size then uint_set_bit x (integer_of_nat n) b else x)"
  including undefined_transfer integer.lifting unfolding uint_set_bit_def
  by (transfer) (auto cong: conj_cong simp add: not_less set_bit_beyond word_size)

lemma uint_set_bit_code [code]:
  "Rep_uint (uint_set_bit w n b) = 
  (if n < 0 \<or> dflt_size_integer \<le> n then Rep_uint (undefined (set_bit :: uint \<Rightarrow> _) w n b)
   else set_bit (Rep_uint w) (nat_of_integer n) b)"
including undefined_transfer integer.lifting unfolding uint_set_bit_def by transfer simp

code_printing constant uint_set_bit \<rightharpoonup>
  (SML) "Uint.set'_bit" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Uint.set'_bit" and
  (Haskell) "Data'_Bits.setBitBounded" and
  (OCaml) "Uint.set'_bit" and
  (Scala) "Uint.set'_bit"

definition uint_shiftl :: "uint \<Rightarrow> integer \<Rightarrow> uint"
where [code del]:
  "uint_shiftl x n = (if n < 0 \<or> dflt_size_integer \<le> n then undefined (push_bit :: nat \<Rightarrow> uint \<Rightarrow> _) x n else push_bit (nat_of_integer n) x)"

lemma shiftl_uint_code [code]: "push_bit n x = (if n < dflt_size then uint_shiftl x (integer_of_nat n) else 0)"
  including undefined_transfer integer.lifting unfolding uint_shiftl_def
  by (transfer fixing: n) simp

lemma uint_shiftl_code [code]:
  "Rep_uint (uint_shiftl w n) =
  (if n < 0 \<or> dflt_size_integer \<le> n then Rep_uint (undefined (push_bit :: nat \<Rightarrow> uint \<Rightarrow> _) w n) else push_bit (nat_of_integer n) (Rep_uint w))"
  including undefined_transfer integer.lifting unfolding uint_shiftl_def by transfer simp

code_printing constant uint_shiftl \<rightharpoonup>
  (SML) "Uint.shiftl" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Uint.shiftl" and
  (Haskell) "Data'_Bits.shiftlBounded" and
  (OCaml) "Uint.shiftl" and
  (Scala) "Uint.shiftl"

definition uint_shiftr :: "uint \<Rightarrow> integer \<Rightarrow> uint"
where [code del]:
  "uint_shiftr x n = (if n < 0 \<or> dflt_size_integer \<le> n then undefined (drop_bit :: nat \<Rightarrow> uint \<Rightarrow> _) x n else drop_bit (nat_of_integer n) x)"

lemma shiftr_uint_code [code]: "drop_bit n x = (if n < dflt_size then uint_shiftr x (integer_of_nat n) else 0)"
  including undefined_transfer integer.lifting unfolding uint_shiftr_def
  by (transfer fixing: n) simp

lemma uint_shiftr_code [code]:
  "Rep_uint (uint_shiftr w n) =
  (if n < 0 \<or> dflt_size_integer \<le> n then Rep_uint (undefined (drop_bit :: nat \<Rightarrow> uint \<Rightarrow> _) w n) else drop_bit (nat_of_integer n) (Rep_uint w))"
  including undefined_transfer integer.lifting unfolding uint_shiftr_def by transfer simp

code_printing constant uint_shiftr \<rightharpoonup>
  (SML) "Uint.shiftr" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Uint.shiftr" and
  (Haskell) "Data'_Bits.shiftrBounded" and
  (OCaml) "Uint.shiftr" and
  (Scala) "Uint.shiftr"

definition uint_sshiftr :: "uint \<Rightarrow> integer \<Rightarrow> uint"
where [code del]:
  "uint_sshiftr x n =
  (if n < 0 \<or> dflt_size_integer \<le> n then undefined signed_drop_bit_uint n x else signed_drop_bit_uint (nat_of_integer n) x)"

lemma sshiftr_uint_code [code]:
  "signed_drop_bit_uint n x = 
  (if n < dflt_size then uint_sshiftr x (integer_of_nat n) else 
    if bit x wivs_index then -1 else 0)"
including undefined_transfer integer.lifting unfolding uint_sshiftr_def
by transfer(simp add: not_less signed_drop_bit_beyond word_size wivs_index_def)

lemma uint_sshiftr_code [code]:
  "Rep_uint (uint_sshiftr w n) =
  (if n < 0 \<or> dflt_size_integer \<le> n then Rep_uint (undefined signed_drop_bit_uint n w) else signed_drop_bit (nat_of_integer n) (Rep_uint w))"
including undefined_transfer integer.lifting unfolding uint_sshiftr_def by transfer simp

code_printing constant uint_sshiftr \<rightharpoonup>
  (SML) "Uint.shiftr'_signed" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Uint.shiftr'_signed" and
  (Haskell) 
    "(Prelude.fromInteger (Prelude.toInteger (Data'_Bits.shiftrBounded (Prelude.fromInteger (Prelude.toInteger _) :: Uint.Int) _)) :: Uint.Word)" and
  (OCaml) "Uint.shiftr'_signed" and
  (Scala) "Uint.shiftr'_signed"

lemma uint_msb_test_bit: "msb x \<longleftrightarrow> bit (x :: uint) wivs_index"
  by transfer (simp add: msb_word_iff_bit wivs_index_def)

lemma msb_uint_code [code]: "msb x \<longleftrightarrow> uint_test_bit x wivs_index_integer"
  apply(simp add: uint_test_bit_def uint_msb_test_bit 
  wivs_index_integer_code dflt_size_integer_def wivs_index_def)
  by (metis (full_types) One_nat_def dflt_size(2) less_iff_diff_less_0 
    nat_of_integer_of_nat of_nat_1 of_nat_diff of_nat_less_0_iff wivs_index_def)

lemma uint_of_int_code [code]: "uint_of_int i = (BITS n. bit i n)"
  by transfer (simp add: word_of_int_conv_set_bits)


section \<open>Quickcheck setup\<close>

definition uint_of_natural :: "natural \<Rightarrow> uint"
where "uint_of_natural x \<equiv> Uint (integer_of_natural x)"

instantiation uint :: "{random, exhaustive, full_exhaustive}" begin
definition "random_uint \<equiv> qc_random_cnv uint_of_natural"
definition "exhaustive_uint \<equiv> qc_exhaustive_cnv uint_of_natural"
definition "full_exhaustive_uint \<equiv> qc_full_exhaustive_cnv uint_of_natural"
instance ..
end

instantiation uint :: narrowing begin

interpretation quickcheck_narrowing_samples
  "\<lambda>i. (Uint i, Uint (- i))" "0"
  "Typerep.Typerep (STR ''Uint.uint'') []" .

definition "narrowing_uint d = qc_narrowing_drawn_from (narrowing_samples d) d"
declare [[code drop: "partial_term_of :: uint itself \<Rightarrow> _"]]
lemmas partial_term_of_uint [code] = partial_term_of_code

instance ..
end

end
