(*  Title:      Native_Word_Test_GHC.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_GHC
imports
  Native_Word_Test
begin

section \<open>Test with GHC\<close>

declare [[code_test_ghc = "-XTypeSynonymInstances"]]

test_code
  test_uint64 "test_uint64' = 0x12"
  test_uint32 "test_uint32' = 0x12"
  test_uint16
  test_uint8 "test_uint8' = 0x12"
  test_uint
  test_casts test_casts' test_casts''
  test_casts_uint test_casts_uint' test_casts_uint''
in GHC


subsection \<open>Test quickcheck narrowing\<close>

context
  includes bit_operations_syntax
begin

lemma \<open>(x :: uint64) AND y = x OR y\<close>
quickcheck [narrowing, expect=counterexample]
oops

lemma \<open>(f :: uint64 \<Rightarrow> bool) = g\<close>
quickcheck [narrowing, size=3, expect=counterexample]
oops

lemma \<open>(x :: uint32) AND y = x OR y\<close>
quickcheck [narrowing, expect=counterexample]
oops

lemma \<open>(f :: uint32 \<Rightarrow> bool) = g\<close>
quickcheck [narrowing, size=3, expect=counterexample]
oops

lemma \<open>(x :: uint16) AND y = x OR y\<close>
quickcheck [narrowing, expect=counterexample]
oops

lemma \<open>(f :: uint16 \<Rightarrow> bool) = g\<close>
quickcheck [narrowing, size=3, expect=counterexample]
oops

lemma \<open>(x :: uint8) AND y = x OR y\<close>
quickcheck [narrowing, expect=counterexample]
oops

lemma \<open>(f :: uint8 \<Rightarrow> bool) = g\<close>
quickcheck [narrowing, size=3, expect=counterexample]
oops

lemma \<open>(x :: uint) AND y = x OR y\<close>
quickcheck [narrowing, expect=counterexample]
oops

lemma \<open>(f :: uint \<Rightarrow> bool) = g\<close>
quickcheck [narrowing, size=3, expect=counterexample]
oops

end

end
