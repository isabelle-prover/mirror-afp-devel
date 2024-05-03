theory heap_infer
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "heap_infer.c"

autocorres "heap_infer.c"

end