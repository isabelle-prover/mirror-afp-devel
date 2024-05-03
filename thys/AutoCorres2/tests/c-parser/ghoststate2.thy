(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ghoststate2
imports "AutoCorres2.CTranslation"
begin

(*
ML {*
IsarInstall.install_C_file ((((NONE, NONE), NONE), "ghoststate2.c"),
  SOME [(IsarInstall.GhostState, "nat")]) @{theory}
  handle TYPE(msg, tys, tms) =>
    (Pretty.writeln
      (Pretty.block (Pretty.commas (map (Syntax.pretty_term @{context}) tms)));
     @{theory})
*}
*)

install_C_file "ghoststate2.c" [ghostty="nat"]

context ghoststate2_simpl
begin

thm f_body_def
thm f_modifies

end (* context *)

end (* theory *)
