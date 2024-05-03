(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver443
  imports "AutoCorres2.CTranslation"
begin


  declare [[allow_underscore_idents=true]]
  (* 3014 lines, with  78 globals:  works ;
     3498 lines, with  96 globals:  works ;
     3719 lines, with 108 globals:  fails
     3719 lines, (down to _camkes_call_tls_var_to_465_2),
      with following functions removed:
         get__camkes_call_tls_var_to_465
         get_echo_int_4_l_to
                                    fails
  *)

declare [[ML_print_depth=10000]]
  install_C_file "jiraver443.c"

  context jiraver443_simpl
begin
    thm echo_char_unmarshal_inputs_body_def
    thm get__camkes_ret_tls_var_from_244_body_def
    (* observe the UnspecifiedSyntax issue in seL4_Send, if you so desire *)
    thm seL4_Send_body_def
  end

end
