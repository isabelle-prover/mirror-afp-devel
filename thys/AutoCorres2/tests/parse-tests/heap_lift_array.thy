theory heap_lift_array
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "heap_lift_array.c"

autocorres "heap_lift_array.c"

end