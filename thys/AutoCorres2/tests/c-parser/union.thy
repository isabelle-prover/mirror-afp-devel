(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory union
imports "AutoCorres2.CTranslation"
begin

declare  [[c_parser_feedback_level=0, ML_print_depth=1000, legacy_anonymous_names = false]]
include_C_file "union.h" for union.c

install_C_file "union.c" 

thm init'globals_body_def

thm global_const_defs
thm global_const_selectors
thm global_const_array_selectors
thm global_const_non_array_selectors

thm globs1_initial_value_def

thm globs1_def
thm globu2_def
thm globs2_def
ML_val \<open>RecursiveRecordPackage.get_info @{theory}\<close>

thm foo_body_def
thm bar_body_def
thm car_body_def
thm access1_body_def
thm access2_body_def
thm access3_body_def
thm access4_body_def

thm update1_body_def
thm update2_body_def
thm heap_update1_body_def
thm heap_update3_body_def
thm heap_update2_body_def
thm size_align_simps
thm size_simps

end
