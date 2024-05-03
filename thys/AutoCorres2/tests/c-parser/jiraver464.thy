(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver464
  imports "AutoCorres2.CTranslation"
begin

(* declare [[calculate_modifies_proofs=false]] *)

install_C_file "jiraver464.c"

print_locale f_spec
context clz_spec
begin
thm clz_spec
end

context f_spec
begin
  thm f_spec
end

context halt_spec
begin
thm halt_spec
end

context jiraver464_simpl
begin
  thm f_body_def
  thm f_modifies
  

thm clz_body_def
thm clz_modifies

thm clz_body_def
thm halt_body_def

end

end
