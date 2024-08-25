(*  Title:      Native_Word_Test_Emu.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_Emu
  imports
  Native_Word_Test
  Code_Target_Int_Bit
begin

section \<open>Test cases for emulation of native words\<close>

subsection \<open>Tests for \<^typ>\<open>uint8\<close>\<close>

text \<open>
  Test that \<^typ>\<open>uint8\<close> is emulated for OCaml via \<^typ>\<open>8 word\<close>
  if \<^theory>\<open>Native_Word.Code_Target_Int_Bit\<close> is imported.
\<close>

definition test_uint8_emulation :: bool
  where \<open>test_uint8_emulation \<longleftrightarrow> (0xFFF - 0x10 = (0xEF :: uint8))\<close>

export_code test_uint8_emulation checking OCaml?
  \<comment> \<open>test the other target languages as well\<close> SML Haskell? Scala


subsection \<open>Tests for \<^typ>\<open>uint16\<close>\<close>

text \<open>
  Test that \<^typ>\<open>uint16\<close> is emulated for PolyML and OCaml via \<^typ>\<open>16 word\<close>
  if \<^theory>\<open>Native_Word.Code_Target_Int_Bit\<close> is imported.
\<close>

definition test_uint16_emulation :: bool
  where \<open>test_uint16_emulation \<longleftrightarrow> (0xFFFFF - 0x1000 = (0xEFFF :: uint16))\<close>

export_code test_uint16_emulation checking SML OCaml?
  \<comment> \<open>test the other target languages as well\<close> Haskell? Scala

notepad begin
  have test_uint16 by eval
  have test_uint16_emulation by eval
  have test_uint16_emulation by normalization
  have test_uint16_emulation by code_simp
end

ML_val \<open>
  val true = @{code test_uint16};
  val true = @{code test_uint16_emulation};
\<close>

lemma \<open>x AND y = x OR (y :: uint16)\<close>
quickcheck [random, expect=counterexample]
quickcheck [exhaustive, expect=counterexample]
oops

end
