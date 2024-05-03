theory nested_break_cont
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "nested_break_cont.c"

autocorres "nested_break_cont.c"

end