theory word_abs_exn
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "word_abs_exn.c"

autocorres "word_abs_exn.c"

end