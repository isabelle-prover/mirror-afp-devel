(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory final_autocorres
  imports "AutoCorres2_Main.AutoCorres_Main"
begin
install_C_file "final_autocorres.c"

autocorres [scope = add] "final_autocorres.c"

text \<open>When not yet all functions are processed  the wrap up locales
 \<open>final_autocorres_all_impl\<close> and \<open>final_autocorres_all_corres\<close> are not generated.

To generate these locale you can use the @{command "final-autocorres"} which simply wraps up all
functions that are processed up to now in those locales.

This might be useful for development or debugging to avoid @{command autocorres} running on all functions and
still having the locales around.
\<close>

final-autocorres "final_autocorres.c"



context final_autocorres_all_impl
begin
thm ts_def
end

context final_autocorres_all_corres
begin
thm ts_corres
end

text \<open>Process the rest.\<close>
autocorres "final_autocorres.c"

text \<open>Note the warning that @{command autocorres} is already finalised. 
Locales @{locale final_autocorres_all_impl} and @{locale final_autocorres_all_corres} do not change, 
as they were already defined before. 
\<close>

context final_autocorres_all_impl
begin
thm ts_def
end

context final_autocorres_all_corres
begin
thm ts_corres
end


end
