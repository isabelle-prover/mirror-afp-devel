(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory modifies_assumptions
imports "AutoCorres2.CTranslation"
begin

install_C_file "modifies_assumptions.c"

context modifies_assumptions_simpl
begin

thm f_body_def


thm f_modifies (* proved by working with the Spec body *)

(* rest are generated *)
thm g_modifies
thm h_modifies
thm j_modifies
thm k_modifies

lemma "\<Gamma> modifies_assumptions.f = Some f_body"
apply (simp add: f_impl)
done

end

end
