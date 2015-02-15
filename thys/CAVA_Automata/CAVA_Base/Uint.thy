section {* Unsigned words of default size *}

(* Based on Lochbihler's Uint32.thy *)

theory Uint imports
  "../../Native_Word/Word_Misc"
  "../../Native_Word/Bits_Integer"
begin

text {* The default size type *}
typedecl dflt_size
consts dflt_size_aux :: "nat"
specification (dflt_size_aux) dflt_size_aux_g0: "dflt_size_aux > 0"
  by auto

instantiation dflt_size :: len begin
  definition "len_of_dflt_size (a::dflt_size itself) \<equiv> dflt_size_aux"
  instance 
    apply default 
    unfolding len_of_dflt_size_def
    by (rule dflt_size_aux_g0)
end

abbreviation "dflt_size \<equiv> len_of (TYPE (dflt_size))"

lift_definition dflt_size_integer :: integer is "int dflt_size" .
declare dflt_size_integer_def[code del]
  -- "The code generator will substitute a machine-dependent value for this constant"

lemma dflt_size_by_int[code]: "dflt_size = nat_of_integer dflt_size_integer"
  unfolding dflt_size_integer_def by simp

lemma dflt_size[simp]: 
  "dflt_size > 0"
  "dflt_size \<ge> Suc 0"
  "\<not>dflt_size < Suc 0"
  using len_gt_0[where 'a=dflt_size]
  by (simp_all del: len_gt_0)
  
declare Quotient_prod[transfer_rule]

section {* Type definition and primitive operations *}

typedef uint = "UNIV :: dflt_size word set" .. 

setup_lifting type_definition_uint

text {* Use an abstract type for code generation to disable pattern matching on @{term Abs_uint}. *}
declare Rep_uint_inverse[code abstype]

declare Quotient_uint[transfer_rule]

instantiation uint :: "{neg_numeral, Divides.div, comm_monoid_mult, comm_ring}" begin
lift_definition zero_uint :: uint is "0 :: dflt_size word" .
lift_definition one_uint :: uint is "1" .
lift_definition plus_uint :: "uint \<Rightarrow> uint \<Rightarrow> uint" is "op + :: dflt_size word \<Rightarrow> _" .
lift_definition minus_uint :: "uint \<Rightarrow> uint \<Rightarrow> uint" is "op -" .
lift_definition uminus_uint :: "uint \<Rightarrow> uint" is uminus .
lift_definition times_uint :: "uint \<Rightarrow> uint \<Rightarrow> uint" is "op *" .
lift_definition div_uint :: "uint \<Rightarrow> uint \<Rightarrow> uint" is "op div" .
lift_definition mod_uint :: "uint \<Rightarrow> uint \<Rightarrow> uint" is "op mod" .
instance by default (transfer, simp add: algebra_simps)+
end

instantiation uint :: linorder begin
lift_definition less_uint :: "uint \<Rightarrow> uint \<Rightarrow> bool" is "op <" .
lift_definition less_eq_uint :: "uint \<Rightarrow> uint \<Rightarrow> bool" is "op \<le>" .
instance by(default)(transfer, simp add: less_le_not_le linear)+
end

lemmas [code] = less_uint.rep_eq less_eq_uint.rep_eq

instantiation uint :: bitss begin
lift_definition bitNOT_uint :: "uint \<Rightarrow> uint" is bitNOT .
lift_definition bitAND_uint :: "uint \<Rightarrow> uint \<Rightarrow> uint" is bitAND .
lift_definition bitOR_uint :: "uint \<Rightarrow> uint \<Rightarrow> uint" is bitOR .
lift_definition bitXOR_uint :: "uint \<Rightarrow> uint \<Rightarrow> uint" is bitXOR .
lift_definition test_bit_uint :: "uint \<Rightarrow> nat \<Rightarrow> bool" is test_bit .
lift_definition set_bit_uint :: "uint \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> uint" is set_bit .
lift_definition set_bits_uint :: "(nat \<Rightarrow> bool) \<Rightarrow> uint" is "set_bits" .
lift_definition lsb_uint :: "uint \<Rightarrow> bool" is lsb .
lift_definition shiftl_uint :: "uint \<Rightarrow> nat \<Rightarrow> uint" is shiftl .
lift_definition shiftr_uint :: "uint \<Rightarrow> nat \<Rightarrow> uint" is shiftr .
lift_definition msb_uint :: "uint \<Rightarrow> bool" is msb .
instance ..
end

lemmas [code] = test_bit_uint.rep_eq lsb_uint.rep_eq msb_uint.rep_eq

instantiation uint :: equal begin
lift_definition equal_uint :: "uint \<Rightarrow> uint \<Rightarrow> bool" is "equal_class.equal" .
instance by default(transfer, simp add: equal_eq)
end

lemmas [code] = equal_uint.rep_eq

instantiation uint :: size begin
lift_definition size_uint :: "uint \<Rightarrow> nat" is "size" .
instance ..
end

lemmas [code] = size_uint.rep_eq

lift_definition sshiftr_uint :: "uint \<Rightarrow> nat \<Rightarrow> uint" (infixl ">>>" 55) is sshiftr .

lift_definition uint_of_int :: "int \<Rightarrow> uint" is "word_of_int" .

lemma bitval_integer_transfer [transfer_rule]:
  "(fun_rel op = pcr_integer) bitval bitval"
by(auto simp add: bitval_def integer.pcr_cr_eq cr_integer_def split: bit.split)

text {* Use pretty numerals from integer for pretty printing *}

lift_definition Uint :: "integer \<Rightarrow> uint" is "word_of_integer" .

context begin interpretation lifting_syntax .

lemma [transfer_rule]: "(op = ===> cr_uint ===> op =) (\<lambda>n m. cr_uint m n) op ="
by(auto 4 3 simp add: cr_uint_def Rep_uint_inject)

lemma Uint_transfer_word_of_int [transfer_rule]: "(pcr_integer ===> cr_uint) word_of_int Uint"
by(rule fun_relI)(simp add: cr_uint_def integer.pcr_cr_eq cr_integer_def Uint.rep_eq word_of_integer.rep_eq)

end

lemma Rep_uint_numeral [simp]: "Rep_uint (numeral n) = numeral n"
by(induction n)(simp_all add: one_uint_def Abs_uint_inverse numeral.simps plus_uint_def)

lemma numeral_uint_transfer [transfer_rule]:
  "(fun_rel op = cr_uint) numeral numeral"
by(auto simp add: cr_uint_def)

lemma numeral_uint [code_unfold]: "numeral n = Uint (numeral n)"
by transfer simp

lemma Rep_uint_neg_numeral [simp]: "Rep_uint (neg_numeral n) = neg_numeral n"
by(simp only: neg_numeral_def uminus_uint_def)(simp add: Abs_uint_inverse)

lemma uint_neg_numeral_transfer [transfer_rule]:
  "(fun_rel op = cr_uint) neg_numeral neg_numeral"
by(auto simp add: cr_uint_def)

lemma neg_numeral_uint [code_unfold]: "neg_numeral n = Uint (neg_numeral n)"
by transfer(simp add: cr_uint_def)

lemma Abs_uint_numeral [code_post]: "Abs_uint (numeral n) = numeral n"
by(induction n)(simp_all add: one_uint_def numeral.simps plus_uint_def Abs_uint_inverse)

lemma Abs_uint_0 [code_post]: "Abs_uint 0 = 0"
by(simp add: zero_uint_def)

lemma Abs_uint_1 [code_post]: "Abs_uint 1 = 1"
by(simp add: one_uint_def)

section {* Code setup *}

code_printing code_module Uint \<rightharpoonup> (SML)
{*
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

end; (* struct Uint *)*}
code_reserved SML Uint

code_printing code_module Uint \<rightharpoonup> (Haskell)
{*
import qualified Data.Word;
import qualified Data.Int;
import qualified Data.Bits;

type Int = Data.Int.Int;

type Word = Data.Word.Word;

dflt_size :: Integer;
dflt_size = Prelude.toInteger (bitSize_aux (0::Word))
  where {
    bitSize_aux :: (Data.Bits.Bits a, Bounded a) => a -> Uint.Int;
    bitSize_aux = Data.Bits.bitSize
  };

*}
code_reserved Haskell Uint dflt_size

text {*
  OCaml and Scala provide only signed bit numbers, so we use these and 
  implement sign-sensitive operations like comparisons manually.
*}

code_printing code_module "Uint" \<rightharpoonup> (OCaml)
{*module Uint : sig
  type t = int
  val dflt_size : Big_int.big_int
  val less : t -> t -> bool
  val less_eq : t -> t -> bool
  val set_bit : t -> Big_int.big_int -> bool -> t
  val shiftl : t -> Big_int.big_int -> t
  val shiftr : t -> Big_int.big_int -> t
  val shiftr_signed : t -> Big_int.big_int -> t
  val test_bit : t -> Big_int.big_int -> bool
end = struct

type t = int

let dflt_size = Big_int.big_int_of_int (
  let rec f n = if n=0 then 0 else f (n / 2) + 1 in f min_int);;

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
  let mask = 1 lsl (Big_int.int_of_big_int n)
  in if b then x lor mask
     else x land (lnot mask);;

let shiftl x n = x lsl (Big_int.int_of_big_int n);;

let shiftr x n = x lsr (Big_int.int_of_big_int n);;

let shiftr_signed x n = x asr (Big_int.int_of_big_int n);;

let test_bit x n = x land (1 lsl (Big_int.int_of_big_int n)) <> 0;;

end;; (*struct Uint*)*}
code_reserved OCaml Uint

code_printing code_module Uint \<rightharpoonup> (Scala)
{*object Uint {
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

} /* object Uint */*}
code_reserved Scala Uint


text {*
  OCaml's conversion from Big\_int to int demands that the value fits int a signed -bit integer.
  The following justifies the implementation.
*}

definition wivs_mask :: int where "wivs_mask == (2^(dflt_size) - 1)"
lift_definition wivs_mask_integer :: integer is wivs_mask .
lemma [code]: "wivs_mask_integer = (2^dflt_size) - 1"
  by transfer (simp add: wivs_mask_def)

definition wivs_shift :: int where "wivs_shift == (2^(dflt_size))"
lift_definition wivs_shift_integer :: integer is wivs_shift .
lemma [code]: "wivs_shift_integer = (2^dflt_size)"
  by transfer (simp add: wivs_shift_def)

definition wivs_index :: nat where "wivs_index == dflt_size - 1"
lift_definition wivs_index_integer :: integer is "int wivs_index".
lemma wivs_index_integer_code[code]: "wivs_index_integer = dflt_size_integer - 1"
  apply transfer apply (simp add: wivs_index_def)
  by (metis One_nat_def add_diff_cancel2 dflt_size(1) diff_Suc_1 
    less_nat_zero_code nat.exhaust of_nat_Suc)

definition wivs_overflow :: int where "wivs_overflow == (2^(dflt_size - 1))"
lift_definition wivs_overflow_integer :: integer is wivs_overflow .
lemma [code]: "wivs_overflow_integer = (2^(dflt_size - 1))"
  by transfer (simp add: wivs_overflow_def)

definition wivs_least :: int where "wivs_least == - wivs_overflow"
lift_definition wivs_least_integer :: integer is wivs_least .
lemma [code]: "wivs_least_integer = - (2^(dflt_size - 1))"
  by transfer (simp add: wivs_overflow_def wivs_least_def)

definition Uint_signed :: "integer \<Rightarrow> uint" 
where "Uint_signed i = (if i < wivs_least_integer 
  \<or> wivs_overflow_integer \<le> i then undefined Uint i else Uint i)"

lemma Uint_code [code]:
  "Uint i = 
  (let i' = i AND wivs_mask_integer
   in 
     if i' !! wivs_index then 
       Uint_signed (i' - wivs_shift_integer) 
     else Uint_signed i')"
  including undefined_transfer 
  unfolding Uint_signed_def
  apply transfer
  apply (rule word_of_int_via_signed)
  by (auto simp: wivs_mask_def wivs_shift_def wivs_index_def wivs_overflow_def 
    wivs_least_def bin_mask_conv_pow2 shiftl_int_def)

lemma Uint_signed_code [code abstract]:
  "Rep_uint (Uint_signed i) = 
  (if i < wivs_least_integer \<or> i \<ge> wivs_overflow_integer then Rep_uint (undefined Uint i) else word_of_int (int_of_integer_symbolic i))"
  unfolding Uint_signed_def Uint_def int_of_integer_symbolic_def word_of_integer_def
  by(simp add: Abs_uint_inverse)

text {* 
  Avoid @{term Abs_uint} in generated code, use @{term Rep_uint'} instead. 
  The symbolic implementations for code\_simp use @{term Rep_uint}.

  The new destructor @{term Rep_uint'} is executable.
  As the simplifier is given the [code abstract] equations literally, 
  we cannot implement @{term Rep_uint} directly, because that makes code\_simp loop.

  If code generation raises Match, some equation probably contains @{term Rep_uint} 
  ([code abstract] equations for @{typ uint} may use @{term Rep_uint} because
  these instances will be folded away.)
*}

definition Rep_uint' where [simp]: "Rep_uint' = Rep_uint"

lemma Rep_uint'_code [code]: "Rep_uint' x = (BITS n. x !! n)"
unfolding Rep_uint'_def by transfer simp

lemma [code, code del]: "term_of_class.term_of = (term_of_class.term_of :: uint \<Rightarrow> _)" ..

instantiation dflt_size :: typerep
begin

definition "typerep_class.typerep \<equiv> 
  \<lambda>_ :: dflt_size itself. Typerep.Typerep (STR ''Uint.dflt_size'') []"
  instance ..

end

lemma term_of_uint_code [code]:
  defines "TR \<equiv> typerep.Typerep" and "bit0 \<equiv> STR ''Numeral_Type.bit0''" 
  shows
  "term_of_class.term_of x = 
   Code_Evaluation.App (Code_Evaluation.Const (STR ''Uint.Abs_uint'') (TR (STR ''fun'') [TR (STR ''Word.word'')  [TR (STR ''Uint.dflt_size'') []], TR (STR ''Uint.uint'') []]))
       (term_of_class.term_of (Rep_uint' x))"
  by(simp add: term_of_anything)

text {* Important:
  We must prevent the reflection oracle (eval-tac) to 
  use our machine-dependent type.
 *}

code_printing
  type_constructor uint \<rightharpoonup>
  (SML) "Word.word" and
  (Haskell) "Uint.Word" and
  (OCaml) "Uint.t" and
  (Scala) "Int" and
  (Eval) "*** \"Error: Machine dependent type\" ***" and
  (Quickcheck) "Word.word" 
| constant dflt_size_integer \<rightharpoonup>
  (SML) "Word.wordSize" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.wordSize" and
  (Haskell) "Uint.dflt'_size" and
  (OCaml) "Uint.dflt'_size" and
  (Scala) "Uint.dflt'_size"
| constant Uint \<rightharpoonup>
  (SML) "Word.fromInt" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.fromInt" and
  (Haskell) "(Prelude.fromInteger _ :: Uint.Word)" and
  (Scala) "_.intValue"
| constant Uint_signed \<rightharpoonup>
  (OCaml) "Big'_int.int'_of'_big'_int"
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
| constant "bitNOT :: uint \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word.notb" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.notb" and
  (Haskell) "Data'_Bits.complement" and
  (OCaml) "Pervasives.lnot" and
  (Scala) "_.unary'_~"
| constant "bitAND :: uint \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word.andb ((_),/ (_))" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.andb ((_),/ (_))" and
  (Haskell) infixl 7 "Data_Bits..&." and
  (OCaml) "Pervasives.(land)" and
  (Scala) infixl 3 "&"
| constant "bitOR :: uint \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word.orb ((_),/ (_))" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.orb ((_),/ (_))" and
  (Haskell) infixl 5 "Data_Bits..|." and
  (OCaml) "Pervasives.(lor)" and
  (Scala) infixl 1 "|"
| constant "bitXOR :: uint \<Rightarrow> _" \<rightharpoonup>
  (SML) "Word.xorb ((_),/ (_))" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Word.xorb ((_),/ (_))" and
  (Haskell) "Data'_Bits.xor" and
  (OCaml) "Pervasives.(lxor)" and
  (Scala) infixl 2 "^"

definition uint_divmod :: "uint \<Rightarrow> uint \<Rightarrow> uint \<times> uint" where
  "uint_divmod x y = 
  (if y = 0 then (undefined (op div :: uint \<Rightarrow> _) x (0 :: uint), undefined (op mod :: uint \<Rightarrow> _) x (0 :: uint)) 
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
   (if y = 0 then undefined (op div :: uint \<Rightarrow> _) x (0 :: uint)
    else Abs_uint (Rep_uint x sdiv Rep_uint y))"

definition div0_uint :: "uint \<Rightarrow> uint"
where [code del]: "div0_uint x = undefined (op div :: uint \<Rightarrow> _) x (0 :: uint)"
code_abort div0_uint

definition mod0_uint :: "uint \<Rightarrow> uint"
where [code del]: "mod0_uint x = undefined (op mod :: uint \<Rightarrow> _) x (0 :: uint)"
code_abort mod0_uint

thm divmod_via_sdivmod

definition wivs_overflow_uint :: uint 
  where "wivs_overflow_uint \<equiv> 1 << (dflt_size - 1)"

(* TODO: Move to Word *)
lemma dflt_size_word_pow_ne_zero[simp]:
  "(2\<Colon>('a::len) word) ^ (len_of TYPE('a) - Suc (0\<Colon>nat)) \<noteq> 0"
proof -
  have "len_of (TYPE('a)\<Colon>'a itself) - Numeral1 \<noteq> len_of (TYPE('a)\<Colon>'a itself)"
    by (metis Suc_pred len_gt_0 n_not_Suc_n numeral_1_eq_Suc_0)
  thus "2 ^ (len_of (TYPE('a)\<Colon>'a itself) - Suc 0) \<noteq> (0\<Colon>'a word)"
    by (metis diff_less_Suc nat_neq_iff not_less_eq numeral_1_eq_Suc_0 
      power_eq_0_iff unat_0 unat_p2 zero_neq_numeral)
qed

(*lemma dflt_size_word_pow_ne_zero[simp]:
  "(2\<Colon>dflt_size word) ^ (len_of TYPE(dflt_size) - Suc (0\<Colon>nat)) \<noteq> (0\<Colon>dflt_size word)"
  by (metis Suc_pred len_of_dflt_size_def less_not_refl nat_zero_less_power_iff
    not_less_eq unat_0 unat_p2 word_len_aux zero_less_numeral)

proof -
  show "2 ^ (len_of (TYPE(dflt_size)\<Colon>dflt_size itself) - Suc 0) \<noteq> (0\<Colon>dflt_size word)"
    by (metis Suc_pred len_of_dflt_size_def less_not_refl nat_zero_less_power_iff
      not_less_eq unat_0 unat_p2 word_len_aux zero_less_numeral)
qed*)

lemma uint_divmod_code [code]:
  "uint_divmod x y =
  (if wivs_overflow_uint \<le> y then if x < y then (0, x) else (1, x - y)
   else if y = 0 then (div0_uint x, mod0_uint x)
   else let q = (uint_sdiv (x >> 1) y) << 1;
            r = x - q * y
        in if r \<ge> y then (q + 1, r - y) else (q, r))"
  including undefined_transfer 
  unfolding uint_divmod_def uint_sdiv_def div0_uint_def mod0_uint_def
    wivs_overflow_uint_def
  by transfer (simp add: divmod_via_sdivmod)

lemma uint_sdiv_code [code abstract]:
  "Rep_uint (uint_sdiv x y) =
   (if y = 0 then Rep_uint (undefined (op div :: uint \<Rightarrow> _) x (0 :: uint))
    else Rep_uint x sdiv Rep_uint y)"
unfolding uint_sdiv_def by(simp add: Abs_uint_inverse)

text {* 
  Note that we only need a translation for signed division, but not for the remainder
  because @{thm uint_divmod_code} computes both with division only.
*}

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
  (if n < 0 \<or> dflt_size_integer \<le> n then undefined (test_bit :: uint \<Rightarrow> _) x n
   else x !! (nat_of_integer n))"

term test_bit

lemma test_bit_uint_code [code]:
  "test_bit x n \<longleftrightarrow> n < dflt_size \<and> uint_test_bit x (integer_of_nat n)"
  including undefined_transfer unfolding uint_test_bit_def
  by transfer 
    (auto cong: conj_cong dest: test_bit_size simp add: word_size)

lemma uint_test_bit_code [code]:
  "uint_test_bit w n =
  (if n < 0 \<or> dflt_size_integer \<le> n then undefined (test_bit :: uint \<Rightarrow> _) w n else Rep_uint w !! nat_of_integer n)"
unfolding uint_test_bit_def
by(simp add: test_bit_uint.rep_eq)

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
  including undefined_transfer unfolding uint_set_bit_def
  by (transfer) (auto cong: conj_cong simp add: not_less set_bit_beyond word_size)

lemma uint_set_bit_code [code abstract]:
  "Rep_uint (uint_set_bit w n b) = 
  (if n < 0 \<or> dflt_size_integer \<le> n then Rep_uint (undefined (set_bit :: uint \<Rightarrow> _) w n b)
   else set_bit (Rep_uint w) (nat_of_integer n) b)"
including undefined_transfer unfolding uint_set_bit_def by transfer simp

code_printing constant uint_set_bit \<rightharpoonup>
  (SML) "Uint.set'_bit" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Uint.set'_bit" and
  (Haskell) "Data'_Bits.setBitBounded" and
  (OCaml) "Uint.set'_bit" and
  (Scala) "Uint.set'_bit"

lift_definition uint_set_bits :: "(nat \<Rightarrow> bool) \<Rightarrow> uint \<Rightarrow> nat \<Rightarrow> uint" is set_bits_aux .

lemma uint_set_bits_code [code]:
  "uint_set_bits f w n =
  (if n = 0 then w 
   else let n' = n - 1 in uint_set_bits f ((w << 1) OR (if f n' then 1 else 0)) n')"
by(transfer fixing: n)(cases n, simp_all)

lemma set_bits_uint [code]:
  "(BITS n. f n) = uint_set_bits f 0 dflt_size"
  by transfer (simp add: set_bits_conv_set_bits_aux)

lemma lsb_code [code]: fixes x :: uint shows "lsb x = x !! 0"
by transfer(simp add: word_lsb_def word_test_bit_def)

definition uint_shiftl :: "uint \<Rightarrow> integer \<Rightarrow> uint"
where [code del]:
  "uint_shiftl x n = (if n < 0 \<or> dflt_size_integer \<le> n then undefined (shiftl :: uint \<Rightarrow> _) x n else x << (nat_of_integer n))"

lemma shiftl_uint_code [code]: "x << n = (if n < dflt_size then uint_shiftl x (integer_of_nat n) else 0)"
including undefined_transfer unfolding uint_shiftl_def
by transfer(simp add: not_less shiftl_zero_size word_size)

lemma uint_shiftl_code [code abstract]:
  "Rep_uint (uint_shiftl w n) =
  (if n < 0 \<or> dflt_size_integer \<le> n then Rep_uint (undefined (shiftl :: uint \<Rightarrow> _) w n) else Rep_uint w << (nat_of_integer n))"
including undefined_transfer unfolding uint_shiftl_def by transfer simp

code_printing constant uint_shiftl \<rightharpoonup>
  (SML) "Uint.shiftl" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Uint.shiftl" and
  (Haskell) "Data'_Bits.shiftlBounded" and
  (OCaml) "Uint.shiftl" and
  (Scala) "Uint.shiftl"

definition uint_shiftr :: "uint \<Rightarrow> integer \<Rightarrow> uint"
where [code del]:
  "uint_shiftr x n = (if n < 0 \<or> dflt_size_integer \<le> n then undefined (shiftr :: uint \<Rightarrow> _) x n else x >> (nat_of_integer n))"

lemma shiftr_uint_code [code]: "x >> n = (if n < dflt_size then uint_shiftr x (integer_of_nat n) else 0)"
including undefined_transfer unfolding uint_shiftr_def
by transfer(simp add: not_less shiftr_zero_size word_size)

lemma uint_shiftr_code [code abstract]:
  "Rep_uint (uint_shiftr w n) =
  (if n < 0 \<or> dflt_size_integer \<le> n then Rep_uint (undefined (shiftr :: uint \<Rightarrow> _) w n) else Rep_uint w >> nat_of_integer n)"
including undefined_transfer unfolding uint_shiftr_def by transfer simp

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
  (if n < 0 \<or> dflt_size_integer \<le> n then undefined sshiftr_uint x n else sshiftr_uint x (nat_of_integer n))"

lemma sshiftr_beyond: fixes x :: "'a :: len word" shows
  "size x \<le> n \<Longrightarrow> x >>> n = (if x !! (size x - 1) then -1 else 0)"
by(rule word_eqI)(simp add: nth_sshiftr word_size)

lemma sshiftr_uint_code [code]:
  "x >>> n = 
  (if n < dflt_size then uint_sshiftr x (integer_of_nat n) else 
    if x !! wivs_index then -1 else 0)"
including undefined_transfer unfolding uint_sshiftr_def
by transfer(simp add: not_less sshiftr_beyond word_size wivs_index_def)

lemma uint_sshiftr_code [code abstract]:
  "Rep_uint (uint_sshiftr w n) =
  (if n < 0 \<or> dflt_size_integer \<le> n then Rep_uint (undefined sshiftr_uint w n) else Rep_uint w >>> (nat_of_integer n))"
including undefined_transfer unfolding uint_sshiftr_def by transfer simp

code_printing constant uint_sshiftr \<rightharpoonup>
  (SML) "Uint.shiftr'_signed" and
  (Eval) "(raise (Fail \"Machine dependent code\"))" and
  (Quickcheck) "Uint.shiftr'_signed" and
  (Haskell) 
    "(Prelude.fromInteger (Prelude.toInteger (Data'_Bits.shiftrBounded (Prelude.fromInteger (Prelude.toInteger _) :: Uint.Int) _)) :: Uint.Word)" and
  (OCaml) "Uint.shiftr'_signed" and
  (Scala) "Uint.shiftr'_signed"

lemma uint_msb_test_bit: "msb x \<longleftrightarrow> (x :: uint) !! wivs_index"
by transfer(simp add: msb_nth wivs_index_def)

lemma msb_uint_code [code]: "msb x \<longleftrightarrow> uint_test_bit x wivs_index_integer"
  apply(simp add: uint_test_bit_def uint_msb_test_bit 
  wivs_index_integer_code dflt_size_integer_def wivs_index_def)
  by (metis (full_types) One_nat_def dflt_size(2) less_iff_diff_less_0 
    nat_of_integer_of_nat of_nat_1 of_nat_diff of_nat_less_0_iff wivs_index_def)

lemma uint_of_int_code [code]: "uint_of_int i = (BITS n. i !! n)"
by transfer(simp add: word_of_int_conv_set_bits test_bit_int_def[abs_def])

section "Quickcheck Setup"

definition "uint_of_natural x \<equiv> Uint (integer_of_natural x)"

(* TODO: Move to Word_Misc, and also setup other uintXX types *)
notation scomp (infixl "\<circ>\<rightarrow>" 60)

definition qc_random_cnv :: 
  "(natural \<Rightarrow> 'a::term_of) \<Rightarrow> natural \<Rightarrow> Random.seed
    \<Rightarrow> ('a \<times> (unit \<Rightarrow> Code_Evaluation.term)) \<times> Random.seed"
  where "qc_random_cnv a_of_natural i = Random.range (i + 1) \<circ>\<rightarrow> (\<lambda>k. Pair (
       let n = a_of_natural k
       in (n, \<lambda>_. Code_Evaluation.term_of n)))"

no_notation scomp (infixl "\<circ>\<rightarrow>" 60)


definition qc_exhaustive_cnv :: "(natural \<Rightarrow> 'a) \<Rightarrow> _"
  where "qc_exhaustive_cnv a_of_natural f d 
  = Quickcheck_Exhaustive.exhaustive (%x. f (a_of_natural x)) d"

definition qc_full_exhaustive_cnv ::
  "(natural \<Rightarrow> ('a::term_of)) \<Rightarrow> ('a \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option)
  \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option" where
  "qc_full_exhaustive_cnv a_of_natural f d = Quickcheck_Exhaustive.full_exhaustive 
  (%(x, xt). f (a_of_natural x, %_. Code_Evaluation.term_of (a_of_natural x))) d"


instantiation uint :: "{random, exhaustive, full_exhaustive}"
begin
  definition "random_uint \<equiv> qc_random_cnv uint_of_natural"
  definition "exhaustive_uint \<equiv> qc_exhaustive_cnv uint_of_natural"
  definition "full_exhaustive_uint \<equiv> qc_full_exhaustive_cnv uint_of_natural"
  instance ..
end

(* TODO/FIXME: Instantiation for narrowing not possible, as required stuff is 
    well-hidden with hide_{const,typ,\<dots>}. *)


section {* Tests *}

value wivs_overflow


lemma uint_word_of_uminus_conv: 
  "[|x>0; x < 2^dflt_size|] ==> uint ((word_of_int (- x))::dflt_size word) = (2 ^ dflt_size - x)"
  apply (simp add: int_word_uint)
  thm zmod_zminus1_eq_if
  by (metis min.strict_iff_order power_eq_0_iff 
    semiring_numeral_div_class.mod_less zmod_zminus1_eq_if)

lemma uint_word_of_negnum_conv: 
  "[|numeral x>(0::int); (numeral x :: int) < 2^dflt_size|] 
  ==> uint ((word_of_int (neg_numeral x))::dflt_size word) = (2 ^ dflt_size - numeral x)"
  by (metis neg_numeral_def uint_word_of_uminus_conv)
  
lemma mod_neg_pos_int: "a<(0::int) \<Longrightarrow> -a < m \<Longrightarrow> a mod m = m + a"
proof -
  assume a1: "a < 0"
  assume "- a < m"
  hence "\<forall>x\<^sub>0. - a + x\<^sub>0 \<le> m + x\<^sub>0"
    by (metis add_le_cancel_right inf.strict_iff_order)
  hence "- a mod - m = - a + - m"
    using a1 by (metis add_0_iff is_num_normalize(10) mod_pos_neg_trivial neg_0_less_iff_less)
  hence "- a mod - m = - (m + a)"
    by auto
  thus "a mod m = m + a"
    by simp
qed

lemma mod_neg_pos_int_numeral:
  assumes "numeral x>(0::int)" 
  assumes "numeral x < m"  
  shows "(neg_numeral x::int) mod m = m - numeral x"
  using mod_neg_pos_int[of "neg_numeral x" m] assms
  by simp

lemma shift_beyond[simp]: 
  "(w::dflt_size word) << dflt_size = 0"
  "(w::dflt_size word) >> dflt_size = 0"
  by (simp_all add: shiftl_zero_size shiftr_zero_size word_size)

definition "uint_test1 \<equiv> let 
  test_list1 = (let
      HS = uint_of_int ((2^(dflt_size - 1)))
    in
      ([ HS+HS+1, -1, -HS - HS + 5, HS + (HS - 1), 0x12
      , 0x5A AND 0x36
      , 0x5A OR 0x36
      , 0x5A XOR 0x36
      , NOT 0x5A
      , 5 + 6, -5 + 6, -6 + 5, -5 + -6, HS + (HS - 1) + 1
      , 5 - 3, 3 - 5
      , 5 * 3, -5 * 3, -5 * -4, 0x12345678 * 0x87654321]
    @ (if dflt_size > 4 then
      [ 5 div 3, -5 div 3, -5 div -3, 5 div -3
      , 5 mod 3, -5 mod 3, -5 mod -3, 5 mod -3
      , set_bit 5 4 True, set_bit -5 2 True, set_bit 5 0 False, set_bit -5 1 False
      , set_bit 5 dflt_size True, set_bit 5 dflt_size False, set_bit -5 dflt_size True, set_bit -5 dflt_size False
      , 1 << 2, -1 << 3, 1 << dflt_size, 1 << 0
      , 31 >> 3, -1 >> 3, 31 >> dflt_size, -1 >> dflt_size
      , 15 >>> 2, -1 >>> 3, 15 >>> dflt_size, -1 >>> dflt_size]
    else []) :: uint list));
  
  test_list2 = (let 
      S=wivs_shift 
    in 
      ([ 1, -1, -S + 5, S - 1, 0x12
      , 0x5A AND 0x36
      , 0x5A OR 0x36
      , 0x5A XOR 0x36
      , NOT 0x5A
      , 5 + 6, -5 + 6, -6 + 5, -5 + -6, 0
      , 5 - 3, 3 - 5
      , 5 * 3, -5 * 3, -5 * -4, 0x12345678 * 0x87654321]
    @ (if dflt_size > 4 then
      [ 5 div 3, (S - 5) div 3, (S - 5) div (S - 3), 5 div (S - 3)
      , 5 mod 3, (S - 5) mod 3, (S - 5) mod (S - 3), 5 mod (S - 3)
      , set_bit 5 4 True, -1, set_bit 5 0 False, -7
      , 5, 5, -5, -5
      , 4, -8, 0, 1
      , 3, (S >> 3) - 1, 0, 0
      , 3, (S>>1) + (S >> 1) - 1, 0, -1] 
    else []) :: int list));


  test_list_c1 = (let
      HS = uint_of_int ((2^(dflt_size - 1)))
    in
  [  (0x5 :: uint) = 0x5, (0x5 :: uint) = 0x6
   , (0x5 :: uint) < 0x5, (0x5 :: uint) < 0x6, (-5 :: uint) < 6, (6 :: uint) < -5
   , (0x5 :: uint) \<le> 0x5, (0x5 :: uint) \<le> 0x4, (-5 :: uint) \<le> 6, (6 :: uint) \<le> -5 
   , (HS - 1) < HS, (HS + HS - 1) < 0, HS < HS - 1
   , (HS - 1) !! 0, (HS - 1 :: uint) !! (dflt_size - 1), (HS :: uint) !! (dflt_size - 1), (HS :: uint) !! dflt_size
   ]);

  test_list_c2 =
   [ True, False
   , False, dflt_size\<ge>2, dflt_size=3, dflt_size\<noteq>3
   , True, False, dflt_size=3, dflt_size\<noteq>3
   , True, False, False
   , dflt_size\<noteq>1, False, True, False
   ]
in
  test_list1 = map uint_of_int test_list2
\<and> test_list_c1 = test_list_c2

"
(*
lemma "uint_test1"
proof -
  note [simp del] = word_of_int_numeral word_of_int_1 word_of_int_neg_numeral
  note [simp] = word_of_int_minus word_of_int_numeral[symmetric] word_of_int_2p_len 
    word_neg_numeral_alt
  note [simp] = wi_hom_mult wi_hom_neg wi_hom_add wi_hom_sub one_word_def bwsimps

  have [simp]: "(2::int) * 2^(dflt_size - Suc 0) = (2^(dflt_size))"
    by (cases dflt_size) simp_all

  have [simp]: "(-2::int) * 2^(dflt_size - Suc 0) = - (2^(dflt_size))"
    by (cases dflt_size) simp_all

  have [simp]: "!!a. word_of_int (2^dflt_size + a) = ((word_of_int a)::dflt_size word)"
    apply (simp only: wi_hom_syms)
    apply simp
    done

  have [simp]: "!!a. word_of_int (2^dflt_size - a) = ((word_of_int (-a))::dflt_size word)"
    apply (simp only: wi_hom_syms)
    apply simp
    done

  {
    fix P
    assume A: "dflt_size > 4"
    assume that: "\<And>n. dflt_size = Suc (Suc (Suc (Suc (Suc n)))) \<Longrightarrow> P"
    have P
      apply (rule that[where n="dflt_size - 5"])
      using A
      apply (simp add: eval_nat_numeral)
      done
  } note ds_cases = this
    
  have aux1[simp]: "\<And>x::int. \<lbrakk>4 < dflt_size; x<32\<rbrakk> \<Longrightarrow> x < 2 ^ dflt_size"
    apply (erule ds_cases, simp_all) []
    (*apply (smt zless2p)*)
  proof -
    fix x :: int and n :: nat
    assume "x < 32"
    also have "\<dots> \<le> 32 * 2^n" by simp
    finally show "x < 32 * 2 ^ n" .
  qed

  have [simp]: "\<And>x. \<lbrakk>4 < dflt_size; numeral x<(32::int)\<rbrakk> 
    \<Longrightarrow> (numeral x mod 2 ^ dflt_size) = (numeral x::int)"
    by (metis aux1 semiring_numeral_div_class.mod_less zero_le_numeral)

  have aux2: "\<And>n. (28\<Colon>int) \<le> (28\<Colon>int) * (2\<Colon>int) ^ n"
    by simp

  have aux3: "\<And>(a::int) b n. \<lbrakk>a<b; b>0\<rbrakk> \<Longrightarrow> a < b * 2^n"
  proof -
    fix a::int and b n
    assume "a<b"
    also assume "b>0" hence "b \<le> b * 2^n" by auto
    finally show "a<b*2^n" .
  qed

  have [simp]: "\<And>n. (-1\<Colon>int) div ((32\<Colon>int) * (2\<Colon>int) ^ n) = (-1\<Colon>int)"
    using div_eq_minus1 by simp

  {
    fix a b c :: int and n 
    assume "a < b + c" "c>0"
    hence "a < b + c * 2^n"
      by (metis aux3 diff_less_eq')
  } note aux3 = aux3 this

  {
    fix a b c :: int and n 
    assume A: "a \<le> b + c" and B: "c>0"
    note A
    also
    from B have "c \<le> c * 2^n" by auto
    hence "b + c \<le> b + c * 2^n" by auto
    finally have "a \<le> b + c * 2^n" .
  } note aux3 = aux3 this

  have aux4: "((-5::int) mod 2 ^ dflt_size < 6 mod 2 ^ dflt_size) \<longleftrightarrow> dflt_size=3"
  proof -
    have [simp]: "\<And>n. (0::int) \<le> -5 + 16 * 2 ^ n"
    proof -
      fix n::nat
      have "(0::int) \<le> -5 + 16" by simp
      also have "(16::int) \<le> 16 * 2^n" by simp
      finally show "(0::int) \<le> -5 + 16 * 2 ^ n" by simp
    qed
    (*by (smt one_le_power)*)

    have [simp]: "\<And>n. \<not>((16::int) * 2 ^ n < 11)"
    proof -
      fix n
      have "(11::int) < 16" by simp
      also have "\<dots> \<le> 16*2^n" by simp
      finally show "\<not>((16::int) * 2 ^ n < 11)" by auto
    qed
    (* by (smt one_le_power)*)

    have [simp]: "\<And>x (y :: int) n. x < y \<Longrightarrow> x < y * 2^n"
    proof -
      fix x y :: int and n
      assume "x<y"
      also have "(1::int) \<le> 2^n" by auto
      hence "y \<le> y * 2^n" proof -
        {
          assume "y>0"
          hence ?thesis

        }

        sledgehammer [isar_proofs]
      
      thm mult_le_mono2

      hence "y \<le> y * 2^n" apply simp using zless2p[of n] apply simp by simp

      apply simp

    show ?thesis
      apply auto
      apply (cases dflt_size, auto)
      apply (case_tac nat, auto)
      apply (case_tac nata, auto)
      apply (case_tac nat, auto)
      apply (subst (asm) (2) mod_pos_pos_trivial, auto) []
      using zless2p apply simp
      apply (smt zless2p)
      apply (auto simp: mod_int_def divmod_int_def)
      apply (simp add: negDivAlg_eqn)
      done
  qed

  have aux5: "((-5::int) mod 2 ^ dflt_size > 6 mod 2 ^ dflt_size) \<longleftrightarrow> dflt_size\<noteq>3"
  proof -
    have [simp]: "\<And>n. (0::int) \<le> -5 + 16 * 2 ^ n"
      by (smt one_le_power)

    have [simp]: "\<And>n. 11 < ((16::int) * 2 ^ n)"
      by (smt one_le_power)

    show ?thesis
      apply auto
      apply (cases dflt_size, auto)
      apply (case_tac nat, auto)
      apply (case_tac nata, auto)
      apply (case_tac nat, auto)
      apply (subst mod_pos_pos_trivial, auto) []
      apply (smt zless2p)
      apply (auto simp: mod_int_def divmod_int_def)
      apply (simp add: negDivAlg_eqn)
      done
  qed

  have aux6: "((-5::int) mod 2 ^ dflt_size \<le> 6 mod 2 ^ dflt_size) \<longleftrightarrow> dflt_size=3"
  proof -
    have [simp]: "\<And>n. (0::int) \<le> -5 + 16 * 2 ^ n"
      by (smt one_le_power)

    have [simp]: "\<And>n. \<not> (((16::int) * 2 ^ n) \<le> 11)"
      by (smt one_le_power)

    show ?thesis
      apply auto
      apply (cases dflt_size, auto)
      apply (case_tac nat, auto)
      apply (case_tac nata, auto)
      apply (case_tac nat, auto)
      apply (subst (asm) (2) mod_pos_pos_trivial, auto) []
      apply (smt zless2p)
      apply (auto simp: mod_int_def divmod_int_def)
      apply (simp add: negDivAlg_eqn)
      done
  qed

  have aux7: "((-5::int) mod 2 ^ dflt_size \<ge> 6 mod 2 ^ dflt_size) \<longleftrightarrow> dflt_size\<noteq>3"
  proof -
    have [simp]: "\<And>n. (0::int) \<le> -5 + 16 * 2 ^ n"
      by (smt one_le_power)

    have [simp]: "\<And>n. (((16::int) * 2 ^ n) \<ge> 11)"
      by (smt one_le_power)

    show ?thesis
      apply auto
      apply (cases dflt_size, auto)
      apply (case_tac nat, auto)
      apply (case_tac nata, auto)
      apply (case_tac nat, auto)
      apply (subst mod_pos_pos_trivial, auto) []
      apply (smt zless2p)
      apply (auto simp: mod_int_def divmod_int_def)
      apply (simp add: negDivAlg_eqn)
      done
  qed

  have [simp]: "\<And>n. (-1\<Colon>int) < (2\<Colon>int) ^ n"
    by (smt zle2p)

  have [simp]: "\<And>n. (2 * 2 ^ n - 1) mod 2 = (1::int)"
    by (metis Word_Miscellaneous.z1pmod2 brdmods'(6) diff_add_cancel mod_2_not_eq_zero_eq_one_int)

  have [simp]: "\<And>n. (2 * 2 ^ n - 1) div 2 = 2^n - (1::int)"
    by (simp)

  { fix n
    have "\<not> bin_nth (2 ^ n - 1) n"
      by (induction n) (auto simp: bin_rest_def)
  } note [simp]=this
    
  show ?thesis
    unfolding uint_test1_def
    apply (simp add: wivs_shift_def Let_def split del: split_if)
    apply transfer
    apply (intro conjI)
    apply simp_all
    apply (cases "4 < dflt_size", simp_all)
    apply (intro conjI)

    apply (fastforce simp add: word_div_def int_word_uint mod_neg_pos_int_numeral set_bit_word_of_int
      word_mod_def
      | fastforce simp add: set_bit_beyond word_size shiftl_def shiftr_def shiftr1_def int_word_uint
    ) +

    apply (erule ds_cases, simp_all)
    apply (simp only: neg_numeral_def word_of_int_minus[symmetric])
    apply simp
    apply (rule word_uint_eqI)
    apply (simp add: int_word_uint shiftr_div_2n)
    apply (subst mod_pos_pos_trivial, simp_all add: aux3) []
    apply (subst mod_pos_pos_trivial, simp_all add: shiftr_int_def aux3) []

    apply (rule word_sint.Rep_eqD)
    apply (simp add: int_word_sint sshiftr_div_2n)
    apply (erule ds_cases, simp_all)
    apply (subst mod_pos_pos_trivial, simp_all add: aux3)
    apply (subst mod_pos_pos_trivial, simp_all add: aux3)

    apply (rule word_sint.Rep_eqD)
    apply (simp add: int_word_sint sshiftr_div_2n shiftr_int_def)
    apply (erule ds_cases, simp_all)
    apply (subst mod_pos_pos_trivial, simp_all add: aux3)
    apply (subst mod_pos_geq, simp_all add: aux3 add.commute)
    apply (subst mod_pos_pos_trivial, simp_all add: aux3)

    apply (rule word_sint.Rep_eqD)
    apply (simp add: int_word_sint sshiftr_div_2n)
    apply (erule ds_cases, simp_all)
    apply (subst mod_pos_pos_trivial, simp_all add: aux3)
    apply (smt zdiv_eq_0_iff zless2p)

    apply (rule word_sint.Rep_eqD)
    apply (simp add: int_word_sint sshiftr_div_2n)
    apply (erule ds_cases, simp_all)
    apply (subst mod_pos_pos_trivial, simp_all add: aux3)
    apply (subst mod_pos_pos_trivial, simp_all add: aux3)

    apply transfer
    apply (cases dflt_size, simp_all) []

    apply (simp add: word_less_alt int_word_uint)
    apply (cases dflt_size, simp_all) []
    apply (case_tac nat, simp_all) []
    apply (case_tac nata, simp_all) []
    apply (subst mod_pos_pos_trivial, simp_all add: aux3)
    apply (subst mod_pos_pos_trivial, simp_all add: aux3)

    apply (simp add: word_less_alt int_word_uint aux4)

    apply (simp add: word_less_alt int_word_uint aux5)

    apply (simp add: word_le_def int_word_uint)
    apply (cases dflt_size, simp_all) []
    apply (case_tac nat, simp_all) []
    apply (case_tac nata, simp_all) []
    apply (case_tac natb, simp_all) []
    apply (subst mod_pos_pos_trivial, simp_all add: aux3)
    apply (subst mod_pos_pos_trivial, simp_all add: aux3)

    apply (simp add: word_le_def int_word_uint aux6)
    apply (simp add: word_le_def int_word_uint aux7)

    apply (simp add: word_less_alt int_word_uint)
    apply (cases dflt_size, simp_all) []
    apply (subst mod_pos_pos_trivial, simp_all add: aux3)

    apply (simp add: word_less_alt int_word_uint)
    apply (cases dflt_size, simp_all) []
    apply (subst mod_pos_pos_trivial, simp_all add: aux3)

    apply (simp add: bin_last_def)
    apply (cases dflt_size, simp_all) []
    apply (case_tac nat, simp_all) []

    apply (cases dflt_size, simp_all) []
    apply (metis nth_2p_bin)
    done
qed
*)
(*
export_code uint_test1 in Haskell file "/tmp/test_hs"
export_code uint_test1 in OCaml file "/tmp/test.ocaml"
export_code uint_test1 in Scala file "/tmp/test.scala"
export_code uint_test1 in SML file "/tmp/test.sml"
*)


text {* Testing Quickcheck *}
lemma "x = (5::uint)"
  quickcheck[random]
  quickcheck[exhaustive]
  oops

lemma "uint_test1"
  quickcheck[random]
  quickcheck[exhaustive]
  oops

text {* Testing Generated Code *}
export_code uint_test1 checking SML Haskell? OCaml? Scala

text {* Cleaning up *}
hide_const uint_test1
hide_fact uint_test1_def
no_notation sshiftr_uint (infixl ">>>" 55)

(*
code_thms "op + :: uint \<Rightarrow> _"

lemma [code nbe]: "uint (Rep_uint (Uint a)) + uint (Rep_uint (Uint b)) 
  AND bin_mask (nat_of_integer dflt_size_integer)
  = uint (Rep_uint (Uint (a+b)))"
  apply transfer
  apply simp
  by (metis arths(2) word_of_int_code)

notepad begin

have "x = ((3::uint) << 2)"
  apply normalization
  

;
uint (Rep_uint (Uint (3\<Colon>integer))) +
    uint (Rep_uint (Uint (4\<Colon>integer)))

*)

end
