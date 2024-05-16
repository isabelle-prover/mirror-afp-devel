(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver1241
imports "AutoCorres2.CTranslation"
begin

install_C_file "jiraver1241.c"

ML \<open>
val mungedb =
    CalculateState.get_csenv @{theory} "jiraver1241.c"
    |> the
    |> ProgramAnalysis.get_mungedb
    |> ProgramAnalysis.render_mungedb;

assert
  (mungedb = [
    (* Functions are global variables with guaranteed-unique names,
       so no aliasing is required. *)
    "C variable 'a' declared globally -> Isabelle state field 'a'",
    "C variable 'b' declared globally -> Isabelle state field 'b'",
    "C variable 'c' declared globally -> Isabelle state field 'c'",
    "C variable 'local' declared in function 'a' -> Isabelle state field 'local'",
    "C variable 'local' declared in function 'b' -> Isabelle state field 'local'",
    "C variable 'local' declared in function 'c' -> Isabelle state field 'local'"
  ])

  "Incorrect mungeDB output";
\<close>

end