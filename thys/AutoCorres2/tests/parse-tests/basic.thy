theory basic
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "basic.c"

autocorres "basic.c"

end