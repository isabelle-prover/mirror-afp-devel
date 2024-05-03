(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory dc_20081211
imports "AutoCorres2.CTranslation"
begin

install_C_file "dc_20081211.c"

declare [[show_types]]

context setHardwareASID_modifies
begin

thm setHardwareASID_modifies

end


context dc_20081211_simpl 
begin

thm setCurrentPD_impl
thm setCurrentPD_modifies
thm setCurrentPD_body_def

thm setHardwareASID_impl
thm setHardwareASID_modifies
thm setHardwareASID_body_def

thm invalidateTLB_impl
thm invalidateTLB_modifies
thm invalidateTLB_body_def

thm invalidateHWASID_impl
thm invalidateHWASID_modifies
thm invalidateHWASID_body_def

thm invalidateMVA_impl
thm invalidateMVA_modifies
thm invalidateMVA_body_def

thm lockTLBEntry_impl
thm lockTLBEntry_modifies
thm lockTLBEntry_body_def

thm test_impl
thm test_modifies
thm test_body_def


lemma test_modifies:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} Call
  dc_20081211.test {t. t may_only_modify_globals s in [x]}"
  (* fails: apply(vcg spec=modifies)
     perhaps because there already is a test_modifies already in
     scope *)
  oops

end

end
