(*  Title:      Native_Word_Test.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Test cases\<close>

theory Native_Word_Test
imports
  Uint64 Uint32 Uint16 Uint8 Uint Native_Cast_Uint
  "HOL-Library.Code_Test"
begin

export_code
  nat_of_uint8 uint8_of_nat
  nat_of_uint16 uint16_of_nat
  nat_of_uint32 uint32_of_nat
  nat_of_uint64 uint64_of_nat
  nat_of_uint uint_of_nat
  in SML

section \<open>Tests for \\<open>^typ\<close>\<open>integer\<close>\<close>

context
  includes bit_operations_syntax
begin

definition bit_integer_test :: bool
  where \<open>bit_integer_test =
  (([ -1 AND 3, 1 AND -3, 3 AND 5, -3 AND (- 5)
    , -3 OR 1, 1 OR -3, 3 OR 5, -3 OR (- 5)
    , NOT 1, NOT (- 3)
    , -1 XOR 3, 1 XOR (- 3), 3 XOR 5, -5 XOR (- 3)
    , Bit_Operations.set_bit 4 5, Bit_Operations.set_bit 2 (- 5)
    , Bit_Operations.unset_bit 0 5, Bit_Operations.unset_bit 1 (- 5)
    , Bit_Operations.flip_bit 4 5, Bit_Operations.flip_bit 1 (- 5)
    , push_bit 2 1, push_bit 3 (- 1)
    , drop_bit 3 100, drop_bit 3 (- 100)
    , take_bit 4 100, take_bit 4 (- 100)] :: integer list)
  = [ 3, 1, 1, -7
    , -3, -3, 7, -1
    , -2, 2
    , -4, -4, 6, 6
    , 21, -1, 4, -7, 21, -7
    , 4, -8
    , 12, -13
    , 4, 12] \<and>
    [ bit (5 :: integer) 4, bit (5 :: integer) 2, bit (-5 :: integer) 4, bit (-5 :: integer) 2
    , bit (5 :: integer) 0, bit (4 :: integer) 0, bit (-1 :: integer) 0, bit (-2 :: integer) 0,
      msb (5 :: integer), msb (0 :: integer), msb (-1 :: integer), msb (-2 :: integer)]
  = [ False, True, True, False,
      True, False, True, False,
      False, False, True, True])\<close>

export_code bit_integer_test
  checking SML Haskell? Haskell_Quickcheck? OCaml? Scala

notepad
begin
  have bit_integer_test by eval
  have bit_integer_test by normalization
  have bit_integer_test by code_simp
end

ML_val \<open>val true = @{code bit_integer_test}\<close>

lemma \<open>x AND y = x OR (y :: integer)\<close>
quickcheck [random, expect=counterexample]
quickcheck [exhaustive, expect=counterexample]
oops

lemma \<open>(x :: integer) AND x = x OR x\<close>
quickcheck [narrowing, expect=no_counterexample]
by transfer simp

lemma \<open>(f :: integer \<Rightarrow> unit) = g\<close>
quickcheck[narrowing, size=3, expect=no_counterexample]
by (simp add: fun_eq_iff)

end


section \<open>Tests for \<^typ>\<open>uint8\<close>\<close>

context
  includes bit_operations_syntax
begin

definition test_uint8 :: bool
  where \<open>test_uint8 \<longleftrightarrow>
  (([ 0x101, -1, -255, 0xFF, 0x12
    , 0x5A AND 0x36
    , 0x5A OR 0x36
    , 0x5A XOR 0x36
    , NOT 0x5A
    , 5 + 6, -5 + 6, -6 + 5, -5 + -6, 0xFF + 1
    , 5 - 3, 3 - 5
    , 5 * 3, -5 * 3, -5 * -4, 0x12 * 0x87
    , 5 div 3, -5 div 3, -5 div -3, 5 div -3
    , 5 mod 3, -5 mod 3, -5 mod -3, 5 mod -3
    , Bit_Operations.set_bit 4 5, Bit_Operations.set_bit 2 (- 5)
    , Bit_Operations.set_bit 32 5, Bit_Operations.set_bit 32 (- 5)
    , Bit_Operations.unset_bit 0 5, Bit_Operations.unset_bit 1 (- 5)
    , Bit_Operations.unset_bit 32 5, Bit_Operations.unset_bit 32 (- 5)
    , Bit_Operations.flip_bit 4 5, Bit_Operations.flip_bit 1 (- 5)
    , Bit_Operations.flip_bit 32 5, Bit_Operations.flip_bit 32 (- 5)
    , push_bit 2 1, push_bit 3 (- 1), push_bit 8 1, push_bit 0 1
    , drop_bit 3 100, drop_bit 3 (- 100), drop_bit 8 100, drop_bit 8 (- 100)
    , signed_drop_bit_uint8 3 100, signed_drop_bit_uint8 3 (- 100)
    , signed_drop_bit_uint8 8 100, signed_drop_bit_uint8 8 (- 100)
    , take_bit 4 100, take_bit 4 (- 100)] :: uint8 list)
   =
    [ 1, 255, 1, 255, 18
    , 18
    , 126
    , 108
    , 165
    , 11, 1, 255, 245, 0
    , 2, 254
    , 15, 241, 20, 126
    , 1, 83, 0, 0
    , 2, 2, 251, 5
    , 21, 255, 5, 251, 4, 249, 5, 251, 21, 249, 5, 251
    , 4, 248, 0, 1
    , 12, 19, 0, 0
    , 12, 243, 0, 255
    , 4, 12]) \<and>
  ([ (0x5 :: uint8) = 0x5, (0x5 :: uint8) = 0x6
   , (0x5 :: uint8) < 0x5, (0x5 :: uint8) < 0x6, (-5 :: uint8) < 6, (6 :: uint8) < -5
   , (0x5 :: uint8) \<le> 0x5, (0x5 :: uint8) \<le> 0x4, (-5 :: uint8) \<le> 6, (6 :: uint8) \<le> -5
   , (0x7F :: uint8) < 0x80, (0xFF :: uint8) < 0, (0x80 :: uint8) < 0x7F
   , bit (0x7F :: uint8) 0, bit (0x7F :: uint8) 7, bit (0x80 :: uint8) 7, bit (0x80 :: uint8) 8
   ]
  =
   [ True, False
   , False, True, False, True
   , True, False, False, True
   , True, False, False
   , True, False, True, False
   ]) \<and>
  ([integer_of_uint8 0, integer_of_uint8 0x7F, integer_of_uint8 0x80, integer_of_uint8 0xAA]
  =
   [0, 0x7F, 0x80, 0xAA])\<close>

export_code test_uint8
  checking SML Haskell? Scala

notepad
begin
  have test_uint8 by eval
  have test_uint8 by code_simp
  have test_uint8 by normalization
end

ML_val \<open>val true = @{code test_uint8}\<close>

definition test_uint8' :: uint8
  where \<open>test_uint8' = drop_bit 2 (push_bit 3 (0 + 10 - 14 * 3 div 6 mod 3))\<close>

ML \<open>val 0wx12 = @{code test_uint8'}\<close>

lemma \<open>x AND y = x OR (y :: uint8)\<close>
quickcheck [random, expect=counterexample]
quickcheck [exhaustive, expect=counterexample]
oops

lemma \<open>(x :: uint8) AND x = x OR x\<close>
quickcheck [narrowing, expect=no_counterexample]
by transfer simp

lemma \<open>(f :: uint8 \<Rightarrow> unit) = g\<close>
quickcheck [narrowing, size=3, expect=no_counterexample]
by (simp add: fun_eq_iff)


section \<open>Tests for \<^typ>\<open>uint16\<close>\<close>

context
  includes bit_operations_syntax
begin

definition test_uint16 :: bool
  where \<open>test_uint16 \<longleftrightarrow>
  (([ 0x10001, -1, -65535, 0xFFFF, 0x1234
    , 0x5A AND 0x36
    , 0x5A OR 0x36
    , 0x5A XOR 0x36
    , NOT 0x5A
    , 5 + 6, -5 + 6, -6 + 5, -5 + -6, 0xFFFF + 1
    , 5 - 3, 3 - 5
    , 5 * 3, -5 * 3, -5 * -4, 0x1234 * 0x8765
    , 5 div 3, -5 div 3, -5 div -3, 5 div -3
    , 5 mod 3, -5 mod 3, -5 mod -3, 5 mod -3
    , Bit_Operations.set_bit 4 5, Bit_Operations.set_bit 2 (- 5)
    , Bit_Operations.set_bit 32 5, Bit_Operations.set_bit 32 (- 5)
    , Bit_Operations.unset_bit 0 5, Bit_Operations.unset_bit 1 (- 5)
    , Bit_Operations.unset_bit 32 5, Bit_Operations.unset_bit 32 (- 5)
    , Bit_Operations.flip_bit 4 5, Bit_Operations.flip_bit 1 (- 5)
    , Bit_Operations.flip_bit 32 5, Bit_Operations.flip_bit 32 (- 5)
    , push_bit 2 1, push_bit 3 (- 1), push_bit 16 1, push_bit 0 1
    , drop_bit 3 100, drop_bit 3 (- 100), drop_bit 16 100, drop_bit 16 (- 100)
    , signed_drop_bit_uint16 3 100, signed_drop_bit_uint16 3 (- 100)
    , signed_drop_bit_uint16 16 100, signed_drop_bit_uint16 16 (- 100)
    , take_bit 4 100, take_bit 4 (- 100)] :: uint16 list)
   =
    [ 1, 65535, 1, 65535, 4660
    , 18
    , 126
    , 108
    , 65445
    , 11, 1, 65535, 65525, 0
    , 2, 65534
    , 15, 65521, 20, 39556
    , 1, 21843, 0, 0
    , 2, 2, 65531, 5
    , 21, 65535, 5, 65531, 4, 65529, 5, 65531, 21, 65529, 5, 65531
    , 4, 65528, 0, 1
    , 12, 8179, 0, 0
    , 12, 65523, 0, 65535
    , 4, 12]) \<and>
  ([ (0x5 :: uint16) = 0x5, (0x5 :: uint16) = 0x6
   , (0x5 :: uint16) < 0x5, (0x5 :: uint16) < 0x6, (-5 :: uint16) < 6, (6 :: uint16) < -5
   , (0x5 :: uint16) \<le> 0x5, (0x5 :: uint16) \<le> 0x4, (-5 :: uint16) \<le> 6, (6 :: uint16) \<le> -5
   , (0x7FFF :: uint16) < 0x8000, (0xFFFF :: uint16) < 0, (0x8000 :: uint16) < 0x7FFF
   , bit (0x7FFF :: uint16) 0, bit (0x7FFF :: uint16) 15, bit (0x8000 :: uint16) 15, bit (0x8000 :: uint16) 16
   ]
  =
   [ True, False
   , False, True, False, True
   , True, False, False, True
   , True, False, False
   , True, False, True, False
   ]) \<and>
  ([integer_of_uint16 0, integer_of_uint16 0x7FFF, integer_of_uint16 0x8000, integer_of_uint16 0xAAAA]
  =
   [0, 0x7FFF, 0x8000, 0xAAAA])\<close>

export_code test_uint16 checking Haskell? Scala
export_code test_uint16 checking SML_word

notepad begin
  have test_uint16 by code_simp
  have test_uint16 by normalization
end

lemma \<open>(x :: uint16) AND x = x OR x\<close>
quickcheck [narrowing, expect=no_counterexample]
by transfer simp

lemma \<open>(f :: uint16 \<Rightarrow> unit) = g\<close>
quickcheck [narrowing, size=3, expect=no_counterexample]
by (simp add: fun_eq_iff)

end


section \<open>Tests for \<^typ>\<open>uint32\<close>\<close>

context
  includes bit_operations_syntax
begin

definition test_uint32 :: bool
  where \<open>test_uint32 \<longleftrightarrow>
  (([ 0x100000001, -1, -4294967291, 0xFFFFFFFF, 0x12345678
    , 0x5A AND 0x36
    , 0x5A OR 0x36
    , 0x5A XOR 0x36
    , NOT 0x5A
    , 5 + 6, -5 + 6, -6 + 5, -5 + (- 6), 0xFFFFFFFFF + 1
    , 5 - 3, 3 - 5
    , 5 * 3, -5 * 3, -5 * -4, 0x12345678 * 0x87654321
    , 5 div 3, -5 div 3, -5 div -3, 5 div -3
    , 5 mod 3, -5 mod 3, -5 mod -3, 5 mod -3
    , Bit_Operations.set_bit 4 5, Bit_Operations.set_bit 2 (- 5)
    , Bit_Operations.set_bit 32 5, Bit_Operations.set_bit 32 (- 5)
    , Bit_Operations.unset_bit 0 5, Bit_Operations.unset_bit 1 (- 5)
    , Bit_Operations.unset_bit 32 5, Bit_Operations.unset_bit 32 (- 5)
    , Bit_Operations.flip_bit 4 5, Bit_Operations.flip_bit 1 (- 5)
    , Bit_Operations.flip_bit 32 5, Bit_Operations.flip_bit 32 (- 5)
    , push_bit 2 1, push_bit 3 (- 1), push_bit 32 1, push_bit 0 1
    , drop_bit 3 100, drop_bit 3 (- 100), drop_bit 32 100, drop_bit 32 (- 100)
    , signed_drop_bit_uint32 3 100, signed_drop_bit_uint32 3 (- 100)
    , signed_drop_bit_uint32 32 100, signed_drop_bit_uint32 32 (- 100)
    , take_bit 4 100, take_bit 4 (- 100)] :: uint32 list)
   =
    [ 1, 4294967295, 5, 4294967295, 305419896
    , 18
    , 126
    , 108
    , 4294967205
    , 11, 1, 4294967295, 4294967285, 0
    , 2, 4294967294
    , 15, 4294967281, 20, 1891143032
    , 1, 1431655763, 0, 0
    , 2, 2, 4294967291, 5
    , 21, 4294967295, 5, 4294967291, 4, 4294967289, 5, 4294967291, 21, 4294967289, 5, 4294967291
    , 4, 4294967288, 0, 1
    , 12, 536870899, 0, 0
    , 12, 4294967283, 0, 4294967295
    , 4, 12]) \<and>
  ([ (0x5 :: uint32) = 0x5, (0x5 :: uint32) = 0x6
   , (0x5 :: uint32) < 0x5, (0x5 :: uint32) < 0x6, (-5 :: uint32) < 6, (6 :: uint32) < -5
   , (0x5 :: uint32) \<le> 0x5, (0x5 :: uint32) \<le> 0x4, (-5 :: uint32) \<le> 6, (6 :: uint32) \<le> -5
   , (0x7FFFFFFF :: uint32) < 0x80000000, (0xFFFFFFFF :: uint32) < 0, (0x80000000 :: uint32) < 0x7FFFFFFF
   , bit (0x7FFFFFFF :: uint32) 0, bit (0x7FFFFFFF :: uint32) 31, bit (0x80000000 :: uint32) 31, bit (0x80000000 :: uint32) 32
   ]
  =
   [ True, False
   , False, True, False, True
   , True, False, False, True
   , True, False, False
   , True, False, True, False
   ]) \<and>
  ([integer_of_uint32 0, integer_of_uint32 0x7FFFFFFF, integer_of_uint32 0x80000000, integer_of_uint32 0xAAAAAAAA]
  =
   [0, 0x7FFFFFFF, 0x80000000, 0xAAAAAAAA])\<close>

export_code test_uint32 checking SML Haskell? OCaml? Scala

notepad begin
  have test_uint32 by eval
  have test_uint32 by code_simp
  have test_uint32 by normalization
end

ML_val \<open>val true = @{code test_uint32}\<close>

definition test_uint32' :: uint32
  where \<open>test_uint32' = drop_bit 2 (push_bit 3 (0 + 10 - 14 * 3 div 6 mod 3))\<close>

ML \<open>val 0wx12 = @{code test_uint32'}\<close>

lemma "x AND y = x OR (y :: uint32)"
quickcheck [random, expect=counterexample]
quickcheck [exhaustive, expect=counterexample]
oops

lemma "(x :: uint32) AND x = x OR x"
quickcheck [narrowing, expect=no_counterexample]
by transfer simp

lemma "(f :: uint32 \<Rightarrow> unit) = g"
quickcheck [narrowing, size=3, expect=no_counterexample]
by (simp add: fun_eq_iff)

end


section \<open>Tests for \<^typ>\<open>uint64\<close> \<close>

context
  includes bit_operations_syntax
begin

definition test_uint64 :: bool
  where \<open>test_uint64 \<longleftrightarrow>
  (([ 0x10000000000000001, -1, -9223372036854775808, 0xFFFFFFFFFFFFFFFF, 0x1234567890ABCDEF
    , 0x5A AND 0x36
    , 0x5A OR 0x36
    , 0x5A XOR 0x36
    , NOT 0x5A
    , 5 + 6, -5 + 6, -6 + 5, -5 + (- 6), 0xFFFFFFFFFFFFFFFFFF + 1
    , 5 - 3, 3 - 5
    , 5 * 3, -5 * 3, -5 * -4, 0x1234567890ABCDEF * 0xFEDCBA0987654321
    , 5 div 3, -5 div 3, -5 div -3, 5 div -3
    , 5 mod 3, -5 mod 3, -5 mod -3, 5 mod -3
    , Bit_Operations.set_bit 4 5, Bit_Operations.set_bit 2 (- 5)
    , Bit_Operations.set_bit 32 5, Bit_Operations.set_bit 32 (- 5)
    , Bit_Operations.unset_bit 0 5, Bit_Operations.unset_bit 1 (- 5)
    , Bit_Operations.unset_bit 32 5, Bit_Operations.unset_bit 32 (- 5)
    , Bit_Operations.flip_bit 4 5, Bit_Operations.flip_bit 1 (- 5)
    , Bit_Operations.flip_bit 32 5, Bit_Operations.flip_bit 32 (- 5)
    , push_bit 2 1, push_bit 3 (- 1), push_bit 64 1, push_bit 0 1
    , drop_bit 3 100, drop_bit 3 (- 100), drop_bit 64 100, drop_bit 64 (- 100)
    , signed_drop_bit_uint64 3 100, signed_drop_bit_uint64 3 (- 100)
    , signed_drop_bit_uint64 64 100, signed_drop_bit_uint64 64 (- 100)
    , take_bit 4 100, take_bit 4 (- 100)] :: uint64 list)
   =
    [ 1, 18446744073709551615, 9223372036854775808, 18446744073709551615, 1311768467294899695
    , 18
    , 126
    , 108
    , 18446744073709551525
    , 11, 1, 18446744073709551615, 18446744073709551605, 0
    , 2, 18446744073709551614
    , 15, 18446744073709551601, 20, 14000077364136384719
    , 1, 6148914691236517203, 0, 0
    , 2, 2, 18446744073709551611, 5 
    , 21, 18446744073709551615, 4294967301, 18446744073709551611, 4, 18446744073709551609, 5, 18446744069414584315, 21, 18446744073709551609, 4294967301, 18446744069414584315
    , 4, 18446744073709551608, 0, 1
    , 12, 2305843009213693939, 0, 0
    , 12, 18446744073709551603, 0, 18446744073709551615
    , 4, 12]) \<and>
  ([ (0x5 :: uint64) = 0x5, (0x5 :: uint64) = 0x6
   , (0x5 :: uint64) < 0x5, (0x5 :: uint64) < 0x6, (-5 :: uint64) < 6, (6 :: uint64) < -5
   , (0x5 :: uint64) \<le> 0x5, (0x5 :: uint64) \<le> 0x4, (-5 :: uint64) \<le> 6, (6 :: uint64) \<le> -5 
   , (0x7FFFFFFFFFFFFFFF :: uint64) < 0x8000000000000000, (0xFFFFFFFFFFFFFFFF :: uint64) < 0, (0x8000000000000000 :: uint64) < 0x7FFFFFFFFFFFFFFF
   , bit (0x7FFFFFFFFFFFFFFF :: uint64) 0, bit (0x7FFFFFFFFFFFFFFF :: uint64) 63, bit (0x8000000000000000 :: uint64) 63, bit (0x8000000000000000 :: uint64) 64
   ]
  =
   [ True, False
   , False, True, False, True
   , True, False, False, True
   , True, False, False
   , True, False, True, False
   ]) \<and>
  ([integer_of_uint64 0, integer_of_uint64 0x7FFFFFFFFFFFFFFF, integer_of_uint64 0x8000000000000000, integer_of_uint64 0xAAAAAAAAAAAAAAAA]
  =
   [0, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xAAAAAAAAAAAAAAAA])\<close>

value [nbe] \<open>[0x10000000000000001, -1, -9223372036854775808, 0xFFFFFFFFFFFFFFFF, 0x1234567890ABCDEF
    , 0x5A AND 0x36
    , 0x5A OR 0x36
    , 0x5A XOR 0x36
    , NOT 0x5A
    , 5 + 6, -5 + 6, -6 + 5, -5 + (- 6), 0xFFFFFFFFFFFFFFFFFF + 1
    , 5 - 3, 3 - 5
    , 5 * 3, -5 * 3, -5 * -4, 0x1234567890ABCDEF * 0xFEDCBA0987654321
    , 5 div 3, -5 div 3, -5 div -3, 5 div -3
    , 5 mod 3, -5 mod 3, -5 mod -3, 5 mod -3
    , push_bit 2 1, push_bit 3 (- 1), push_bit 64 1, push_bit 0 1
    , drop_bit 3 100, drop_bit 3 (- 100), drop_bit 64 100, drop_bit 64 (- 100)
    , signed_drop_bit_uint64 3 100, signed_drop_bit_uint64 3 (- 100)
    , signed_drop_bit_uint64 64 100, signed_drop_bit_uint64 64 (- 100)
    , take_bit 4 100, take_bit 4 (- 100)] :: uint64 list\<close>

export_code test_uint64 checking SML Haskell? OCaml? Scala

notepad begin
  have test_uint64 by eval
  have test_uint64 by code_simp
  have test_uint64 by normalization
end

ML_val \<open>val true = @{code test_uint64}\<close>

definition test_uint64' :: uint64
  where \<open>test_uint64' = drop_bit 2 (push_bit 3 (0 + 10 - 14 * 3 div 6 mod 3))\<close>

ML \<open>val 0wx12 = @{code test_uint64'}\<close>

end


section \<open>Tests for \<^typ>\<open>uint\<close>\<close>

context
  includes bit_operations_syntax
begin

definition test_uint :: bool
  where \<open>test_uint = (let
  test_list1 = (let
      HS = uint_of_int (2 ^ (dflt_size - 1))
    in
      ([ HS + HS + 1, -1, -HS - HS + 5, HS + (HS - 1), 0x12
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
      , Bit_Operations.set_bit dflt_size 5, Bit_Operations.set_bit dflt_size (- 5)
      , Bit_Operations.unset_bit dflt_size 5, Bit_Operations.unset_bit dflt_size (- 5)
      , Bit_Operations.flip_bit 0 5, Bit_Operations.flip_bit 0 (- 5)
      , push_bit 2 1, push_bit 3 (- 1), push_bit dflt_size 1, push_bit 0 1
      , drop_bit 3 31, drop_bit 3 (- 1), drop_bit dflt_size 31, drop_bit dflt_size (- 1)
      , signed_drop_bit_uint 2 15, signed_drop_bit_uint 3 (- 1)
      , signed_drop_bit_uint dflt_size 15, signed_drop_bit_uint dflt_size (- 1)
      , take_bit 4 100, take_bit 4 (- 100)]
    else []) :: uint list));

  test_list2 = (let
      S = wivs_shift
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
      , 5, -5, 5, -5, 4, -6
      , 4, -8, 0, 1
      , 3, drop_bit 3 S - 1, 0, 0
      , 3, drop_bit 1 S + drop_bit 1 S - 1, 0, -1
      , 4, 12]
    else []) :: int list));

  test_list_c1 = (let
      HS = uint_of_int ((2^(dflt_size - 1)))
    in
  [  (0x5 :: uint) = 0x5, (0x5 :: uint) = 0x6
   , (0x5 :: uint) < 0x5, (0x5 :: uint) < 0x6, (-5 :: uint) < 6, (6 :: uint) < -5
   , (0x5 :: uint) \<le> 0x5, (0x5 :: uint) \<le> 0x4, (-5 :: uint) \<le> 6, (6 :: uint) \<le> -5
   , (HS - 1) < HS, (HS + HS - 1) < 0, HS < HS - 1
   , bit (HS - 1) 0, bit (HS - 1 :: uint) (dflt_size - 1), bit (HS :: uint) (dflt_size - 1), bit (HS :: uint) dflt_size
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
\<and> test_list_c1 = test_list_c2)\<close>

export_code test_uint checking SML Haskell? OCaml? Scala

lemma test_uint
quickcheck[exhaustive, expect=no_counterexample]
oops \<comment> \<open>FIXME: prove correctness of test by reflective means (not yet supported)\<close>

lemma \<open>x AND y = x OR (y :: uint)\<close>
quickcheck [random, expect=counterexample]
quickcheck [exhaustive, expect=counterexample]
oops

lemma \<open>(x :: uint) AND x = x OR x\<close>
quickcheck [narrowing, expect=no_counterexample]
by transfer simp

lemma \<open>(f :: uint \<Rightarrow> unit) = g\<close>
quickcheck [narrowing, size=3, expect=no_counterexample]
by (simp add: fun_eq_iff)


section \<open>Tests for casts\<close>

definition test_casts :: bool
  where \<open>test_casts \<longleftrightarrow>
  map uint8_of_uint32 [10, 0, 0xFE, 0xFFFFFFFF] = [10, 0, 0xFE, 0xFF] \<and>
  map uint8_of_uint64 [10, 0, 0xFE, 0xFFFFFFFFFFFFFFFF] = [10, 0, 0xFE, 0xFF] \<and>
  map uint32_of_uint8 [10, 0, 0xFF] = [10, 0, 0xFF] \<and>
  map uint64_of_uint8 [10, 0, 0xFF] = [10, 0, 0xFF]\<close>

definition test_casts' :: bool
  where \<open>test_casts' \<longleftrightarrow>
  map uint8_of_uint16 [10, 0, 0xFE, 0xFFFF] = [10, 0, 0xFE, 0xFF] \<and>
  map uint16_of_uint8 [10, 0, 0xFF] = [10, 0, 0xFF] \<and>
  map uint16_of_uint32 [10, 0, 0xFFFE, 0xFFFFFFFF] = [10, 0, 0xFFFE, 0xFFFF] \<and>
  map uint16_of_uint64 [10, 0, 0xFFFE, 0xFFFFFFFFFFFFFFFF] = [10, 0, 0xFFFE, 0xFFFF] \<and>
  map uint32_of_uint16 [10, 0, 0xFFFF] = [10, 0, 0xFFFF] \<and>
  map uint64_of_uint16 [10, 0, 0xFFFF] = [10, 0, 0xFFFF]\<close>

definition test_casts'' :: bool
  where \<open>test_casts'' \<longleftrightarrow>
  map uint32_of_uint64 [10, 0, 0xFFFFFFFE, 0xFFFFFFFFFFFFFFFF] = [10, 0, 0xFFFFFFFE, 0xFFFFFFFF] \<and>
  map uint64_of_uint32 [10, 0, 0xFFFFFFFF] = [10, 0, 0xFFFFFFFF]\<close>

export_code test_casts test_casts'' checking SML Haskell? Scala
export_code test_casts'' checking OCaml?
export_code test_casts' checking Haskell? Scala

notepad begin
  have test_casts by eval
  have test_casts by normalization
  have test_casts by code_simp
  have test_casts' by normalization
  have test_casts' by code_simp
  have test_casts'' by eval
  have test_casts'' by normalization
  have test_casts'' by code_simp
end

ML \<open>
  val true = @{code test_casts}
  val true = @{code test_casts''}
\<close>

definition test_casts_uint :: bool
  where \<open>test_casts_uint \<longleftrightarrow>
  map uint_of_uint32 ([0, 10] @ (if dflt_size < 32 then [push_bit (dflt_size - 1) 1, 0xFFFFFFFF] else [0xFFFFFFFF])) = 
  [0, 10] @ (if dflt_size < 32 then [push_bit (dflt_size - 1) 1, (push_bit dflt_size 1) - 1] else [0xFFFFFFFF]) \<and>
  map uint32_of_uint [0, 10, if dflt_size < 32 then push_bit (dflt_size - 1) 1 else 0xFFFFFFFF] =
  [0, 10, if dflt_size < 32 then push_bit (dflt_size - 1) 1 else 0xFFFFFFFF] \<and>
  map uint_of_uint64 [0, 10, push_bit (dflt_size - 1) 1, 0xFFFFFFFFFFFFFFFF] =
  [0, 10, push_bit (dflt_size - 1) 1, (push_bit dflt_size 1) - 1] \<and>
  map uint64_of_uint [0, 10, push_bit (dflt_size - 1) 1] =
  [0, 10, push_bit (dflt_size - 1) 1]\<close>

definition test_casts_uint' :: bool
  where \<open>test_casts_uint' \<longleftrightarrow>
  map uint_of_uint16 [0, 10, 0xFFFF] = [0, 10, 0xFFFF] \<and>
  map uint16_of_uint [0, 10, 0xFFFF] = [0, 10, 0xFFFF]\<close>

definition test_casts_uint'' :: bool
  where \<open>test_casts_uint'' \<longleftrightarrow>
  map uint_of_uint8 [0, 10, 0xFF] = [0, 10, 0xFF] \<and>
  map uint8_of_uint [0, 10, 0xFF] = [0, 10, 0xFF]\<close>

export_code test_casts_uint test_casts_uint'' checking SML Haskell?
export_code test_casts_uint checking OCaml?
export_code test_casts_uint' checking Haskell? Scala

end

end

end
