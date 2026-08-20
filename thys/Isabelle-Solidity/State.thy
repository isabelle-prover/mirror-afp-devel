theory State
imports Stores "HOL-Library.Word"
begin

section \<open>Value types\<close>

type_synonym bytes = string
type_synonym id = String.literal

datatype ('a::address) valtype =
  Bool (bool: bool)
| Uint (uint: "256 word")
| Address (ad: 'a)
| Bytes (bytes: bytes) \<comment>\<open>bytes1, ..., bytes32\<close>

instantiation valtype :: (address) vtype
begin

fun to_nat_valtype::"'a valtype \<Rightarrow> nat option" where
  "to_nat_valtype (Uint x) = Some (unat x)"
| "to_nat_valtype _ = None"

instance ..

end

section \<open>Common functions\<close>

fun lift_bool_unary::"(bool \<Rightarrow> bool) \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "lift_bool_unary op (Bool b) = Some (Bool (op b))"
| "lift_bool_unary _ _ = None"

definition vtnot where
  "vtnot = lift_bool_unary Not"

fun lift_bool_binary::"(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "lift_bool_binary op (Bool l) (Bool r) = Some (Bool (op l r))"
| "lift_bool_binary _ _ _ = None"

definition vtand where
  "vtand = lift_bool_binary (\<and>)"

definition vtor where
  "vtor = lift_bool_binary (\<or>)"

fun vtequals where
  "vtequals (Uint l) (Uint r) = Some (Bool (l = r))"
| "vtequals (Address l) (Address r) = Some (Bool (l = r))"
| "vtequals (Bool l) (Bool r) = Some (Bool (l = r))"
| "vtequals (Bytes l) (Bytes r) = Some (Bool (l = r))"
| "vtequals _ _ = None"

fun lift_int_comp::"(256 word \<Rightarrow> 256 word \<Rightarrow> bool) \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "lift_int_comp op (Uint l) (Uint r) = Some (Bool (op l r))"
| "lift_int_comp _ _ _ = None"

definition vtless where
  "vtless = lift_int_comp (<)"

fun lift_int_binary::"(256 word \<Rightarrow> 256 word \<Rightarrow> 256 word) \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "lift_int_binary op (Uint l) (Uint r) = Some (Uint (op l r))"
| "lift_int_binary _ _ _ = None"

definition vtplus where
  "vtplus = lift_int_binary (+)"

fun vtplus_safe::"('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtplus_safe (Uint l) (Uint r) = (if unat l + unat r < 2^256 then Some (Uint (l + r)) else None)"
| "vtplus_safe _ _ = None"

declare vtplus_safe.simps[simp del]

definition vtminus where
  "vtminus = lift_int_binary (-)"

fun vtminus_safe::"('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtminus_safe (Uint l) (Uint r) = (if r \<le> l then Some (Uint (l - r)) else None)"
| "vtminus_safe _ _ = None"

declare vtminus_safe.simps[simp del]

definition vtmult where
  "vtmult = lift_int_binary (*)"

fun vtmult_safe::"('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtmult_safe (Uint l) (Uint r) = (if unat l * unat r < 2^256 then Some (Uint (l * r)) else None)"
| "vtmult_safe _ _ = None"

declare vtmult_safe.simps[simp del]

definition vtmod where
  "vtmod = lift_int_binary (mod)"

section \<open>Operations on bytes\<close>

(* indexing bytes_n returns bytes_1 *)
fun vtbytes_index :: "('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtbytes_index (Bytes xs) (Uint i) = (if unat i < length xs then Some (Bytes [xs ! unat i]) else None)"
| "vtbytes_index _ _ = None"

definition zipWith :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
  "zipWith op xs ys = map (\<lambda> (x, y). op x y) (zip xs ys)"

fun lift_bytes_binary::"(char \<Rightarrow> char \<Rightarrow> char) \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "lift_bytes_binary op (Bytes l) (Bytes r) = (if length l = length r then Some (Bytes (zipWith op l r)) else None)"
| "lift_bytes_binary _ _ _ = None"

fun lift_bytes_unary::"(char \<Rightarrow> char) \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "lift_bytes_unary op (Bytes l) = Some (Bytes (map op l))"
| "lift_bytes_unary _ _ = None"

definition word8_to_char :: "8 word \<Rightarrow> char" where
  "word8_to_char w = char_of (unat w)"

definition char_to_word8 :: "char \<Rightarrow> 8 word" where
  "char_to_word8 c = of_nat (of_char c)"

definition op_word8_to_char :: "(8 word \<Rightarrow> 8 word \<Rightarrow> 8 word) \<Rightarrow> (char \<Rightarrow> char \<Rightarrow> char)" where
  "op_word8_to_char op x y = word8_to_char (op (char_to_word8 x) (char_to_word8 y))"

context
  includes bit_operations_syntax
begin

definition vtbytes_and where
  "vtbytes_and = lift_bytes_binary (op_word8_to_char (AND))"

definition vtbytes_or where
  "vtbytes_or = lift_bytes_binary (op_word8_to_char (OR))"

definition vtbytes_xor where
  "vtbytes_xor = lift_bytes_binary (op_word8_to_char (XOR))"

definition vtbytes_not where
  "vtbytes_not = lift_bytes_unary (\<lambda> x. word8_to_char ((NOT) (char_to_word8 x)))"

end

fun resize_list :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "resize_list m pad xs =
     (if length xs < m
      then xs @ replicate (m - length xs) pad
      else take m xs)"

fun vtbytes_cast :: "nat \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtbytes_cast m (Bytes xs) = Some (Bytes (resize_list m (CHR 0x00) xs))"
| "vtbytes_cast m _ = None"

section \<open>State\<close>

subsection \<open>Definition\<close>

type_synonym 'v stack = "(id, 'v kdata) fmap"
type_synonym 'a balances = "'a \<Rightarrow> nat"
type_synonym ('a, 'v) storage = "'a \<Rightarrow> id \<Rightarrow> 'v storage_data"
type_synonym 'v calldata = "(id, 'v call_data) fmap"

record ('a::address) state =
  Memory:: "('a::address valtype) memory"
  Calldata:: "('a::address valtype) calldata"
  Storage:: "('a::address, 'a::address valtype) storage"
  Stack:: "('a::address valtype) stack"
  Balances::"('a::address) balances"

subsection \<open>Update Function\<close>

datatype ex = Err

definition balances_update:: "('a::address) \<Rightarrow> nat \<Rightarrow> ('a::address) state \<Rightarrow> ('a::address) state" where
  "balances_update i n s = s\<lparr>Balances := (Balances s)(i := n)\<rparr>"

definition calldata_update:: "id \<Rightarrow> ('a::address valtype) call_data \<Rightarrow> ('a::address) state \<Rightarrow> ('a::address) state" where
  "calldata_update i d = Calldata_update (fmupd i d)"

definition stack_update:: "id \<Rightarrow> ('a::address valtype) kdata \<Rightarrow> ('a::address) state \<Rightarrow> ('a::address) state" where
  "stack_update i d = Stack_update (fmupd i d)"

definition memory_update:: "location \<Rightarrow> ('a::address valtype) mdata \<Rightarrow> ('a::address) state \<Rightarrow> ('a::address) state" where
  "memory_update i d s = s\<lparr>Memory := (Memory s)[i := d]\<rparr>"

lemma balances_update_id[simp]: "balances_update x (Balances s x) s = s"
  unfolding balances_update_def by simp

end