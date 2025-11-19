theory unliftable_call
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "unliftable_call.c"

autocorres [no_heap_abs = call_f rec_typ rec_untyp] "unliftable_call.c"

thm ts_def

end