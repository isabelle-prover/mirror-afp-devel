(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ghoststate1
imports "AutoCorres2.CTranslation"
begin

install_C_file "ghoststate1.c" [ghostty="nat \<Rightarrow> nat"]

(* demonstrates existence of ghost'state global variable of appropriate type *)
term "\<acute>ghost'state :== (\<lambda>x. x + (1::nat))"

end
