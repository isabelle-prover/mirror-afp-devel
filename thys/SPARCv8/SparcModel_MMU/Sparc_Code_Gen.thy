(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory sparc_code_gen

imports Main sparc_execution sparc_init_state

begin

export_code init_state0 reset_mode_mod reset_mode_val
state_undef
seq_exec_leon3 in OCaml
module_name Sparc_seq file sparc_seq

end
