theory struct_init
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "struct_init.c"

autocorres "struct_init.c"

end