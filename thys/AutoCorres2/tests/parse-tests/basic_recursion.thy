theory basic_recursion
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "basic_recursion.c"

autocorres "basic_recursion.c"

end