theory read_global_array
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "read_global_array.c"

autocorres "read_global_array.c"

end