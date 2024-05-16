theory loop_test2
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "loop_test2.c"

autocorres "loop_test2.c"

end