(*  Title:      Native_Word_Test_SMLNJ2.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_SMLNJ2
  imports Native_Word_Test_Emu
  options [condition = "$ISABELLE_SMLNJ"]
begin

test_code
  test_uint16 test_uint16_emulation
  test_casts'
  test_casts_uint'
in SMLNJ

end
