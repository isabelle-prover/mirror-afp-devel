theory while_loop_no_vars
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "while_loop_no_vars.c"

autocorres "while_loop_no_vars.c"

end