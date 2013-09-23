(*  Title:      Uint16_Test.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Uint16_Test imports
  Uint16
  Code_Target_Bits_Int
begin

text {*
  Test that @{typ uint16} is emulated for PolyML and OCaml via @{typ "16 word"} 
  if @{theory Code_Target_Bits_Int} is imported.
*}

definition test_uint16_emulation :: bool where
  "test_uint16_emulation \<longleftrightarrow> (0xFFFFF - 0x1000 = (0xEFFF :: uint16))"

export_code test_uint16_emulation checking SML OCaml?
  -- {* test the other target languages as well *} Haskell? Scala

notepad begin
have test_uint16_emulation by eval
have test_uint16_emulation by normalization
have test_uint16_emulation by code_simp
end

hide_const test_uint16_emulation
hide_fact test_uint16_emulation_def

end