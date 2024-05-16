theory voidptrptr
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "voidptrptr.c"

autocorres "voidptrptr.c"

end