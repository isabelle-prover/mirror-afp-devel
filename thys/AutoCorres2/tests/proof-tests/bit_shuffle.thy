(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory bit_shuffle imports
  "AutoCorres2_Main.AutoCorres_Main"
begin


install_C_file "bit_shuffle.c"

autocorres "bit_shuffle.c"

context bit_shuffle_all_corres
begin

thm bit_shuffle'_def
thm "bit_shuffle'_ac_corres"
end

end