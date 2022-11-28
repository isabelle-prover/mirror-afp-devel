theory Preliminary_Library
  imports Main "HOL-Library.Word" "Word_Lib.Word_Lib_Sumo" "HOL-Library.Countable"
begin

section \<open>Preliminary Theories\<close>
text \<open>In this subsection, we provide the type and value system used by the CHERI-C Memory Model.
      We also provide proofs for the conversion between large words (i.e. bits) and a list of bytes.
      For primitive bytes that are not $U8_\tau$ or $S8_\tau$, we need to be able to convert between
      their normal representation and list of bytes so that storing values work as intended. 
      The high-level detail is given in the paper~\cite{park_2022}.\<close>
subsection \<open>Types and Values\<close>
text \<open>We first formalise the capability type. We first define \textit{memory capabilities} as a record,
      then we define \textit{tagged capabilities} by extending the record. We state the class 
      comp\_countable for future work, but countable is sufficient for the block\_id type.
      For the permissions, we present only those used by the memory model.\<close>
class comp_countable = countable + zero + ord

record ('a :: comp_countable) mem_capability =
  block_id :: "'a" (* block_id *)
  offset :: int (* offset/address *)
  base :: nat (* metadata *)
  len :: nat
  perm_load :: bool
  perm_cap_load :: bool
  perm_store :: bool
  perm_cap_store :: bool
  perm_cap_store_local :: bool
  perm_global :: bool

record ('a :: comp_countable) capability = "'a mem_capability" + 
  tag :: bool (* tag *)

text \<open>cctype corresponds to $\tau$ in the paper~\cite{park_2022}, where $\tau$ is the type system.\<close>
datatype cctype = 
  Uint8
  | Sint8
  | Uint16
  | Sint16
  | Uint32
  | Sint32
  | Uint64
  | Sint64
  | Cap

text \<open>$'a\ ccval$ corresponds to $\mathcal{V}_\mathcal{C}$ in the paper~\cite{park_2022}. $'a$ in 
      this instance must be countable. \<close>
datatype 'a ccval = 
  Uint8_v      "8 word"
  | Sint8_v    "8 sword"
  | Uint16_v   "16 word"
  | Sint16_v   "16 sword"
  | Uint32_v   "32 word"
  | Sint32_v   "32 sword"
  | Uint64_v   "64 word"
  | Sint64_v   "64 sword"
  | Cap_v      "'a capability"
  | Cap_v_frag "'a capability" "nat"
  | Undef

text \<open>memval\_type infers the type of a value. \<close>
fun memval_type :: "'a ccval \<Rightarrow> cctype"
  where
  "memval_type v = (case v of 
     Uint8_v  _ \<Rightarrow> Uint8
   | Sint8_v  _ \<Rightarrow> Sint8
   | Uint16_v _ \<Rightarrow> Uint16
   | Sint16_v _ \<Rightarrow> Sint16
   | Uint32_v _ \<Rightarrow> Uint32
   | Sint32_v _ \<Rightarrow> Sint32
   | Uint64_v _ \<Rightarrow> Uint64
   | Sint64_v _ \<Rightarrow> Sint64
   | Cap_v    _ \<Rightarrow> Cap
   | Cap_v_frag _ _ \<Rightarrow> Uint8)"


subsection \<open>Primitive Value Conversion and Cast Proof\<close>
text \<open>In this subsection, we provide proofs for the conversion between words and list of words.
      We also provide proofs that casting primitive values is correct. These will be used by the
      \texttt{load} and \texttt{store} operations in the memory model.\<close>
abbreviation encode_u8 :: "nat \<Rightarrow> 8 word"
  where
  "encode_u8 x \<equiv> word_of_nat x"

abbreviation decode_u8 :: "8 word \<Rightarrow> nat"
  where
  "decode_u8 b \<equiv> unat b"

abbreviation encode_u8_list :: "8 word \<Rightarrow> 8 word list"
  where
  "encode_u8_list w \<equiv> [w]"

abbreviation decode_u8_list :: "8 word list \<Rightarrow> 8 word"
  where
  "decode_u8_list ls \<equiv> hd ls"

lemma encode_decode_u8_list:
  "ls = [b] \<Longrightarrow> ls = encode_u8_list (decode_u8_list ls)"
  by simp

lemma decode_encode_u8_list:
  "w = decode_u8_list (encode_u8_list w)"
  by simp

lemma encode_decode_u8:
  "w = encode_u8 (decode_u8 w)"
  by simp

lemma decode_encode_u8:
  assumes "i \<le> 2 ^ LENGTH(8) - 1"
  shows "i = decode_u8 (encode_u8 i)"
  by (metis assms le_unat_uoi unat_minus_one_word)
  
abbreviation u64_split :: "64 word \<Rightarrow> 32 word list"
  where
  "u64_split x \<equiv> (word_rsplit :: 64 word \<Rightarrow> 32 word list) x"

abbreviation u32_split :: "32 word \<Rightarrow> 16 word list"
  where
  "u32_split x \<equiv> (word_rsplit :: 32 word \<Rightarrow> 16 word list) x"

abbreviation u16_split :: "16 word \<Rightarrow> 8 word list"
  where
  "u16_split x \<equiv> (word_rsplit :: 16 word \<Rightarrow> 8 word list) x"

abbreviation cat_u16 :: "8 word list \<Rightarrow> 16 word"
  where
  "cat_u16 x \<equiv> (word_rcat :: 8 word list \<Rightarrow> 16 word) x"

abbreviation encode_u16 :: "nat \<Rightarrow> 8 word list"
  where 
  "encode_u16 x \<equiv> u16_split (word_of_nat x)"

abbreviation decode_u16 :: "8 word list \<Rightarrow> nat"
  where
  "decode_u16 x \<equiv> unat (cat_u16 x)"

lemma flatten_u16_length:
  "length (u16_split vs) = 2"
  by (simp add: length_word_rsplit_even_size wsst_TYs(3))

lemma rsplit_rcat_eq:
  assumes "LENGTH(('b::len)) mod LENGTH(('a::len)) = 0"
    and "length w = LENGTH('b) div LENGTH('a)"
  shows "(word_rsplit :: 'b word \<Rightarrow> 'a word list) ((word_rcat :: 'a word list \<Rightarrow> 'b word) w) = w"
  by (simp add: assms mod_0_imp_dvd size_word.rep_eq word_rsplit_rcat_size)

lemma rsplit_rcat_u16_eq:
  assumes "w = [a1, a2]"
  shows "(word_rsplit :: 16 word \<Rightarrow> 8 word list) ((word_rcat :: 8 word list \<Rightarrow> 16 word) w) = w"
proof -
  have l1: "length w * 8 = 16"
    using assms by clarsimp
  moreover have l2: "size ((word_rcat :: 8 word list \<Rightarrow> 16 word) w) = 16"
    using assms
    by (simp add: size_word.rep_eq)
  from l1 l2 have "length w * 8 = size ((word_rcat :: 8 word list \<Rightarrow> 16 word) w)"
    by argo
  thus ?thesis
    by (metis l1 l2 len8 word_rsplit_rcat_size)
qed
    

lemma encode_decode_u16:
  assumes "w = [a, b]"
  shows "w = encode_u16 (decode_u16 w)"
  by (simp add: assms rsplit_rcat_eq)

lemma cat_flatten_u16_eq:
  "cat_u16 (u16_split w) = w" 
  by (simp add: word_rcat_rsplit)

lemma decode_encode_u16:
  assumes "i \<le> 2 ^ LENGTH(16) - 1"
  shows "i = decode_u16 (encode_u16 i)" 
  by (metis assms cat_flatten_u16_eq le_unat_uoi unat_minus_one_word)

abbreviation flatten_u32 :: "32 word \<Rightarrow> 8 word list"
  where
  "flatten_u32 x \<equiv> (word_rsplit :: 32 word \<Rightarrow> 8 word list) x"

abbreviation cat_u32 :: "8 word list \<Rightarrow> 32 word"
  where
  "cat_u32 x \<equiv> (word_rcat :: 8 word list \<Rightarrow> 32 word) x"

abbreviation encode_u32 :: "nat \<Rightarrow> 8 word list"
  where
  "encode_u32 x \<equiv> flatten_u32 (word_of_nat x)"

abbreviation decode_u32 :: "8 word list \<Rightarrow> nat"
  where
  "decode_u32 i \<equiv> unat (cat_u32 i)"

lemma flatten_u32_length:
  "length (flatten_u32 vs) = 4"
  by (simp add: length_word_rsplit_even_size wsst_TYs(3))

lemma rsplit_rcat_u32_eq:
  assumes "w = [a1, a2, b1, b2]"
  shows "(word_rsplit :: 32 word \<Rightarrow> 8 word list) ((word_rcat :: 8 word list \<Rightarrow> 32 word) w) = w" 
  using rsplit_rcat_eq assms
  by force

lemma encode_decode_u32:
  assumes "w = [a1, a2, b1, b2]"
  shows "w = encode_u32 (decode_u32 w)" 
  using assms 
  by (simp add: rsplit_rcat_u32_eq)

lemma cat_flatten_u32_eq:
  "cat_u32 (flatten_u32 w) = w" 
  by (simp add: word_rcat_rsplit)

lemma decode_encode_u32:
  assumes "i \<le> 2 ^ LENGTH(32) - 1"
  shows "i = decode_u32 (encode_u32 i)" 
  by (metis assms le_unat_uoi unat_minus_one_word word_rcat_rsplit)

abbreviation flatten_u64 :: "64 word \<Rightarrow> 8 word list"
  where
  "flatten_u64 x \<equiv> (word_rsplit :: 64 word \<Rightarrow> 8 word list) x"

abbreviation cat_u64 :: "8 word list \<Rightarrow> 64 word"
  where
  "cat_u64 x \<equiv> word_rcat x"

abbreviation encode_u64 :: "nat \<Rightarrow> 8 word list"
  where
  "encode_u64 x \<equiv> flatten_u64 (word_of_nat x)"

abbreviation decode_u64 :: "8 word list \<Rightarrow> nat"
  where
  "decode_u64 x \<equiv> unat (cat_u64 x)"

lemma flatten_u64_length:
  "length (flatten_u64 vs) = 8"
  by (simp add: length_word_rsplit_even_size wsst_TYs(3))

lemma encode_decode_u64:
  assumes "w = [a1, a2, b1, b2, c1, c2, d1, d2]"
  shows "w = encode_u64 (decode_u64 w)"
  using assms 
  by (simp add: rsplit_rcat_eq)

lemma cat_flatten_u64_eq:
  "cat_u64 (flatten_u64 w) = w" 
  by (simp add: word_rcat_rsplit)

lemma decode_encode_u64:
  assumes "i \<le> 2 ^ LENGTH(64) - 1"
  shows "i = decode_u64 (encode_u64 i)" 
  by (metis assms le_unat_uoi unat_minus_one_word word_rcat_rsplit)

abbreviation encode_s8 :: "int \<Rightarrow> 8 sword"
  where
  "encode_s8 x \<equiv> word_of_int x"

abbreviation decode_s8 :: "8 sword \<Rightarrow> int"
  where
  "decode_s8 b \<equiv> sint b"

abbreviation encode_s8_list :: "8 sword \<Rightarrow> 8 word list"
  where
  "encode_s8_list w \<equiv> [SCAST(8 signed \<rightarrow> 8) w]"

abbreviation decode_s8_list :: "8 word list \<Rightarrow> 8 sword"
  where
  "decode_s8_list ls \<equiv> UCAST(8 \<rightarrow> 8 signed) (hd ls)"

lemma encode_decode_s8_list:
  "ls = [b] \<Longrightarrow> ls = encode_s8_list (decode_s8_list ls)"
  by simp

lemma decode_encode_s8_list:
  "w = decode_s8_list (encode_s8_list w)"
  by simp

lemma encode_decode_s8:
  "w = encode_s8 (decode_s8 w)"
  by simp

lemma decode_encode_s8:
  assumes "- (2 ^ (LENGTH(8) - 1)) \<le> i"
    and "i < 2 ^ (LENGTH(8) - 1)"
  shows "i = decode_s8 (encode_s8 i)" 
  by (metis assms More_Word.sint_of_int_eq len_signed)
  
abbreviation s64_split :: "64 sword \<Rightarrow> 32 word list"
  where
  "s64_split x \<equiv> (word_rsplit :: 64 sword \<Rightarrow> 32 word list) x"

abbreviation s32_split :: "32 sword \<Rightarrow> 16 word list"
  where
  "s32_split x \<equiv> (word_rsplit :: 32 sword \<Rightarrow> 16 word list) x"

abbreviation s16_split :: "16 sword \<Rightarrow> 8 word list"
  where
  "s16_split x \<equiv> (word_rsplit :: 16 sword \<Rightarrow> 8 word list) x"

abbreviation cat_s16 :: "8 word list \<Rightarrow> 16 sword"
  where
  "cat_s16 x \<equiv> (word_rcat :: 8 word list \<Rightarrow> 16 sword) x"

abbreviation encode_s16 :: "int \<Rightarrow> 8 word list"
  where 
  "encode_s16 x \<equiv> s16_split (word_of_int x)"

abbreviation decode_s16 :: "8 word list \<Rightarrow> int"
  where
  "decode_s16 x \<equiv> sint (cat_s16 x)"

lemma flatten_s16_length:
  "length (s16_split vs) = 2"
  by (simp add: length_word_rsplit_even_size wsst_TYs(3))

lemma rsplit_rcat_s16_eq:
  assumes "w = [a1, a2]"
  shows "(word_rsplit :: 16 sword \<Rightarrow> 8 word list) ((word_rcat :: 8 word list \<Rightarrow> 16 sword) w) = w"
proof -
  have l1: "length w * 8 = 16"
    using assms by clarsimp
  moreover have l2: "size ((word_rcat :: 8 word list \<Rightarrow> 16 sword) w) = 16"
    using assms
    by (simp add: size_word.rep_eq)
  from l1 l2 have "length w * 8 = size ((word_rcat :: 8 word list \<Rightarrow> 16 sword) w)"
    by argo
  thus ?thesis
    by (simp add: word_rsplit_rcat_size)
qed
    

lemma encode_decode_s16:
  assumes "w = [a, b]"
  shows "w = encode_s16 (decode_s16 w)"
  by (simp add: assms rsplit_rcat_eq)

lemma cat_flatten_s16_eq:
  "cat_s16 (s16_split w) = w" 
  by (simp add: word_rcat_rsplit)

lemma decode_encode_s16:
  assumes "- (2 ^ (LENGTH(16) - 1)) \<le> i"
    and "i < 2 ^ (LENGTH(16) - 1)"
  shows "i = decode_s16 (encode_s16 i)" 
  by (metis assms cat_flatten_s16_eq len_signed sint_of_int_eq)

abbreviation flatten_s32 :: "32 sword \<Rightarrow> 8 word list"
  where
  "flatten_s32 x \<equiv> (word_rsplit :: 32 sword \<Rightarrow> 8 word list) x"

abbreviation cat_s32 :: "8 word list \<Rightarrow> 32 sword"
  where
  "cat_s32 x \<equiv> (word_rcat :: 8 word list \<Rightarrow> 32 sword) x"

abbreviation encode_s32 :: "int \<Rightarrow> 8 word list"
  where
  "encode_s32 x \<equiv> flatten_s32 (word_of_int x)"

abbreviation decode_s32 :: "8 word list \<Rightarrow> int"
  where
  "decode_s32 i \<equiv> sint (cat_s32 i)"

lemma flatten_s32_length:
  "length (flatten_s32 vs) = 4"
  by (simp add: length_word_rsplit_even_size wsst_TYs(3))

lemma rsplit_rcat_s32_eq:
  assumes "w = [a1, a2, b1, b2]"
  shows "(word_rsplit :: 32 sword \<Rightarrow> 8 word list) ((word_rcat :: 8 word list \<Rightarrow> 32 sword) w) = w" 
  using rsplit_rcat_eq assms
  by force

lemma encode_decode_s32:
  assumes "w = [a1, a2, b1, b2]"
  shows "w = encode_s32 (decode_s32 w)" 
  using assms 
  by (simp add: rsplit_rcat_s32_eq)

lemma decode_encode_s32:
  assumes "- (2 ^ (LENGTH(32) - 1)) \<le> i"
    and "i < 2 ^ (LENGTH(32) - 1)"
  shows "i = decode_s32 (encode_s32 i)" 
  by (metis assms len_signed sint_of_int_eq word_rcat_rsplit)
  
abbreviation flatten_s64 :: "64 sword \<Rightarrow> 8 word list"
  where
  "flatten_s64 x \<equiv> (word_rsplit :: 64 sword \<Rightarrow> 8 word list) x"

lemma flatten_s64_length:
  "length (flatten_s64 vs) = 8"
  by (simp add: length_word_rsplit_even_size wsst_TYs(3))

abbreviation cat_s64 :: "8 word list \<Rightarrow> 64 sword"
  where
  "cat_s64 x \<equiv> word_rcat x"

abbreviation encode_s64 :: "int \<Rightarrow> 8 word list"
  where
  "encode_s64 x \<equiv> flatten_s64 (word_of_int x)"

abbreviation decode_s64 :: "8 word list \<Rightarrow> int"
  where
  "decode_s64 x \<equiv> sint (cat_s64 x)"

lemma encode_decode_s64:
  assumes "w = [a1, a2, b1, b2, c1, c2, d1, d2]"
  shows "w = encode_s64 (decode_s64 w)"
  using assms 
  by (simp add: rsplit_rcat_eq)

lemma decode_encode_s64:
  assumes "- (2 ^ (LENGTH(64) - 1)) \<le> i"
    and "i < 2 ^ (LENGTH(64) - 1)"
  shows "i = decode_s64 (encode_s64 i)" 
  by (metis assms len_signed sint_of_int_eq word_rcat_rsplit)

definition word_of_integer :: "integer \<Rightarrow> 'a::len word"
  where
  "word_of_integer x \<equiv> word_of_int (int_of_integer x)"

definition sword_of_integer :: "integer \<Rightarrow> 'a::len sword"
  where
  "sword_of_integer x \<equiv> word_of_int (int_of_integer x)"

definition integer_of_word :: "'a::len word \<Rightarrow> integer"
  where
  "integer_of_word x \<equiv> integer_of_int (uint x)"

definition integer_of_sword :: "'a::len sword \<Rightarrow> integer"
  where
  "integer_of_sword x \<equiv> integer_of_int (sint x)"

lemma word_integer_eq:
  "word_of_integer (integer_of_word w) = w"
  unfolding word_of_integer_def integer_of_word_def
  by (metis int_of_integer_of_int integer_of_int_eq_of_int word_uint.Rep_inverse')

lemma sword_integer_eq:
  "sword_of_integer (integer_of_sword w) = w"
  unfolding sword_of_integer_def integer_of_sword_def
  by (metis int_of_integer_of_int integer_of_int_eq_of_int word_sint.Rep_inverse')

lemma integer_word_bounded_eq:
  assumes "0 \<le> i"
  assumes "i \<le> 2 ^ LENGTH('a::len) - 1"
  shows "integer_of_word ((word_of_integer :: integer \<Rightarrow> 'a word) i) = i"
  unfolding integer_of_word_def word_of_integer_def
  using assms 
  by (metis integer_less_eq_iff integer_of_int_eq_of_int minus_integer.rep_eq of_int_0_le_iff of_int_eq_1_iff of_int_eq_numeral_power_cancel_iff of_int_integer_of word_of_int_inverse zle_diff1_eq)

lemma integer_sword_bounded_eq:
  assumes "- (2 ^ (LENGTH('a::len) - 1)) \<le> i"
    and "i < 2 ^ (LENGTH('a) - 1)"
  shows "integer_of_sword ((sword_of_integer :: integer \<Rightarrow> 'a sword) i) = i"
  unfolding integer_of_sword_def sword_of_integer_def
  using signed_take_bit_int_eq_self assms 
  by (smt (verit) diff_numeral_special(11) int_of_integer_numeral integer_less_eq_iff integer_of_int_eq_of_int len_signed minus_integer.rep_eq numeral_power_eq_of_int_cancel_iff of_int_integer_of of_int_power_less_of_int_cancel_iff one_integer.rep_eq sint_of_int_eq uminus_integer.rep_eq)

definition word8_of_integer :: "integer \<Rightarrow> 8 word"
  where
  "word8_of_integer \<equiv> word_of_integer"

definition word16_of_integer :: "integer \<Rightarrow> 16 word"
  where
  "word16_of_integer \<equiv> word_of_integer"

definition word32_of_integer :: "integer \<Rightarrow> 32 word"
  where
  "word32_of_integer \<equiv> word_of_integer"

definition word64_of_integer :: "integer \<Rightarrow> 64 word"
  where
  "word64_of_integer \<equiv> word_of_integer"

definition integer_of_word8 :: "8 word \<Rightarrow> integer"
  where
  "integer_of_word8 \<equiv> integer_of_word"
                                
definition integer_of_word16 :: "16 word \<Rightarrow> integer"
  where
  "integer_of_word16 \<equiv> integer_of_word"

definition integer_of_word32 :: "32 word \<Rightarrow> integer"
  where
  "integer_of_word32 \<equiv> integer_of_word"

definition integer_of_word64 :: "64 word \<Rightarrow> integer"
  where
  "integer_of_word64 \<equiv> integer_of_word"

lemma word8_integer_eq:
  "word8_of_integer (integer_of_word8 w) = w" 
  unfolding word8_of_integer_def integer_of_word8_def
  using word_integer_eq 
  by blast

lemma word16_integer_eq:
  "word16_of_integer (integer_of_word16 w) = w" 
  unfolding word16_of_integer_def integer_of_word16_def
  using word_integer_eq 
  by blast

lemma word32_integer_eq:
  "word32_of_integer (integer_of_word32 w) = w" 
  unfolding word32_of_integer_def integer_of_word32_def
  using word_integer_eq 
  by blast

lemma word64_integer_eq:
  "word64_of_integer (integer_of_word64 w) = w"
  unfolding word64_of_integer_def integer_of_word64_def
  using word_integer_eq
  by blast

lemma integer_word8_bounded_eq:
   assumes "0 \<le> i"
    and "i \<le> 2 ^ LENGTH(8) - 1"
  shows "integer_of_word8 (word8_of_integer i) = i"
  unfolding word8_of_integer_def integer_of_word8_def
  using integer_word_bounded_eq assms
  by blast

lemma integer_word16_bounded_eq:
   assumes "0 \<le> i"
    and "i \<le> 2 ^ LENGTH(16) - 1"
  shows "integer_of_word16 (word16_of_integer i) = i"
  unfolding word16_of_integer_def integer_of_word16_def
  using integer_word_bounded_eq assms
  by blast

lemma integer_word32_bounded_eq:
   assumes "0 \<le> i"
    and "i \<le> 2 ^ LENGTH(32) - 1"
  shows "integer_of_word32 (word32_of_integer i) = i"
  unfolding word32_of_integer_def integer_of_word32_def
  using integer_word_bounded_eq assms
  by blast

lemma integer_word64_bounded_eq:
   assumes "0 \<le> i"
    and "i \<le> 2 ^ LENGTH(64) - 1"
  shows "integer_of_word64 (word64_of_integer i) = i"
  unfolding word64_of_integer_def integer_of_word64_def
  using integer_word_bounded_eq assms
  by blast

definition sword8_of_integer :: "integer \<Rightarrow> 8 sword"
  where
  "sword8_of_integer \<equiv> sword_of_integer"

definition sword16_of_integer :: "integer \<Rightarrow> 16 sword"
  where
  "sword16_of_integer \<equiv> sword_of_integer"

definition sword32_of_integer :: "integer \<Rightarrow> 32 sword"
  where
  "sword32_of_integer \<equiv> sword_of_integer"

definition sword64_of_integer :: "integer \<Rightarrow> 64 sword"
  where
  "sword64_of_integer \<equiv> sword_of_integer"

definition integer_of_sword8 :: "8 sword \<Rightarrow> integer"
  where
  "integer_of_sword8 \<equiv> integer_of_sword"

definition integer_of_sword16 :: "16 sword \<Rightarrow> integer"
  where
  "integer_of_sword16 \<equiv> integer_of_sword"

definition integer_of_sword32 :: "32 sword \<Rightarrow> integer"
  where
  "integer_of_sword32 \<equiv> integer_of_sword"

definition integer_of_sword64 :: "64 sword \<Rightarrow> integer"
  where
  "integer_of_sword64 \<equiv> integer_of_sword"

lemma sword8_integer_eq:
  "sword8_of_integer (integer_of_sword8 w) = w" 
  unfolding sword8_of_integer_def integer_of_sword8_def
  using sword_integer_eq 
  by blast

lemma sword16_integer_eq:
  "sword16_of_integer (integer_of_sword16 w) = w" 
  unfolding sword16_of_integer_def integer_of_sword16_def
  using sword_integer_eq 
  by blast

lemma sword32_integer_eq:
  "sword32_of_integer (integer_of_sword32 w) = w" 
  unfolding sword32_of_integer_def integer_of_sword32_def
  using sword_integer_eq 
  by blast

lemma sword64_integer_eq:
  "sword64_of_integer (integer_of_sword64 w) = w"
  unfolding sword64_of_integer_def integer_of_sword64_def
  using sword_integer_eq
  by blast

lemma integer_sword8_bounded_eq:
   assumes "- (2 ^ (LENGTH(8) - 1)) \<le> i"
    and "i < 2 ^ (LENGTH(8) - 1)"
  shows "integer_of_sword8 (sword8_of_integer i) = i"
  unfolding sword8_of_integer_def integer_of_sword8_def
  using integer_sword_bounded_eq assms 
  by metis 

lemma integer_sword16_bounded_eq:
   assumes "- (2 ^ (LENGTH(16) - 1)) \<le> i"
    and "i < 2 ^ (LENGTH(16) - 1)"
  shows "integer_of_sword16 (sword16_of_integer i) = i"
  unfolding sword16_of_integer_def integer_of_sword16_def
  using integer_sword_bounded_eq assms
  by metis

lemma integer_sword32_bounded_eq:
   assumes "- (2 ^ (LENGTH(32) - 1)) \<le> i"
    and "i < 2 ^ (LENGTH(32) - 1)"
  shows "integer_of_sword32 (sword32_of_integer i) = i"
  unfolding sword32_of_integer_def integer_of_sword32_def
  using integer_sword_bounded_eq assms 
  by metis

lemma integer_sword64_bounded_eq:
   assumes "- (2 ^ (LENGTH(64) - 1)) \<le> i"
    and "i < 2 ^ (LENGTH(64) - 1)"
  shows "integer_of_sword64 (sword64_of_integer i) = i"
  unfolding sword64_of_integer_def integer_of_sword64_def
  using integer_sword_bounded_eq assms
  by metis

lemmas flatten_types_length = flatten_u16_length flatten_s16_length flatten_u32_length flatten_s32_length flatten_u64_length flatten_s64_length

text \<open>cast\_val is an executable code that ensures easy casting of values. This value cast function
      is used within the Gillian 
      framework~\cite{old_gillian_2020, gillian_2021, maksimovic_2021, fragoso_2020}.\<close>
definition cast_val ::  "String.literal \<Rightarrow> integer \<Rightarrow> integer"
  where
  "cast_val s i \<equiv>
     if s = STR ''uint8'' then integer_of_word8 (word8_of_integer i) 
     else if s = STR ''int8'' then integer_of_sword8 (sword8_of_integer i)
     else if s = STR ''uint16'' then integer_of_word16 (word16_of_integer i)
     else if s = STR ''int16'' then integer_of_sword16 (sword16_of_integer i)
     else if s = STR ''uint32'' then integer_of_word32 (word32_of_integer i)
     else if s = STR ''int32'' then integer_of_sword32 (sword32_of_integer i)
     else if s = STR ''uint64'' then integer_of_word64 (word64_of_integer i)
     else if s = STR ''int64'' then integer_of_sword64 (sword64_of_integer i)
     else i"

end
