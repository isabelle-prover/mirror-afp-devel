theory big_bit_ops
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "big_bit_ops.c"

autocorres [no_body = fr] "big_bit_ops.c"

end