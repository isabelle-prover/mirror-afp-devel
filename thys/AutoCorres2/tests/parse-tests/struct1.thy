theory struct1
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "struct1.c"

autocorres "struct1.c"


end