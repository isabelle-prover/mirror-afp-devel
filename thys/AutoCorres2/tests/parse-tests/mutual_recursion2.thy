theory mutual_recursion2
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "mutual_recursion2.c"

autocorres "mutual_recursion2.c"

end