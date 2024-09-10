(*  Title:      Native_Word_Test_MLton.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_MLton
imports
  Native_Word_Test
begin

section \<open>Test with MLton\<close>

test_code
  test_uint64 \<open>test_uint64' = 0x12\<close>
  test_uint32 \<open>test_uint32' = 0x12\<close>
  test_uint8 \<open>test_uint8' = 0x12\<close>
  test_uint
  test_casts
  test_casts''
  test_casts_uint
  test_casts_uint''
in MLton

text \<open>MLton provides \texttt{Word16} and \texttt{Word64} structures. To test them in the
  SML\_word target, we have to associate a driver with the combination.\<close>

setup \<open>Code_Test.add_driver ("MLton_word", (Code_Test.evaluate_in_mlton, "SML_word"))\<close>

test_code
  test_uint64 \<open>test_uint64' = 0x12\<close>
  test_uint32 \<open>test_uint32' = 0x12\<close>
  test_uint16
  test_uint8 \<open>test_uint8' = 0x12\<close>
  test_uint
  test_casts
  test_casts'
  test_casts''
  test_casts_uint
  test_casts_uint'
  test_casts_uint''
in MLton_word

end
