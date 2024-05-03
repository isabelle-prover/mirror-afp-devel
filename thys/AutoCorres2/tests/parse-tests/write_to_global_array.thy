theory write_to_global_array
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "write_to_global_array.c"

autocorres "write_to_global_array.c"

end