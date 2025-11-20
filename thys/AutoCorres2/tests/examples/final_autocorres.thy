(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory final_autocorres
  imports "AutoCorres2_Main.AutoCorres_Main"
begin
install_C_file "final_autocorres.c"

declare [[ML_print_depth=1000]]
init-autocorres [skip_word_abs]"final_autocorres.c"
autocorres [ scope = add] "final_autocorres.c"
autocorres [ scope = minus] "final_autocorres.c"
autocorres [ scope = call_add_minus] "final_autocorres.c"

text \<open>When not yet all functions are processed the definition of function pointer 
environments are not generated.

To generate those definitions ands propagate them to the functions use the @{command "final-autocorres"} 

This might be useful for development or debugging to avoid @{command autocorres} running on all functions and
still having everything around.
\<close>

final-autocorres "final_autocorres.c"



thm ts_def
thm final_defs
thm \<P>_defs
context final_autocorres_global_addresses
begin
thm ts_corres
end

text \<open>Process the rest.\<close>
autocorres "final_autocorres.c"

text \<open>Note the warning that @{command autocorres} is already finalised. 
@{thm final_defs} and @{thm \<P>_defs} are not updated.

So calling @{command autocorres} after @{command "final-autocorres"} is unexpected. Also note that
when @{command autocorres} detects that all functions are processed it automatically calls
@{command "final-autocorres"}.
\<close>
thm ts_def
thm final_defs
thm \<P>_defs

end
