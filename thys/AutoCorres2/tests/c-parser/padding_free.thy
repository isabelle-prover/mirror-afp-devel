(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory padding_free
imports "AutoCorres2.CTranslation"
begin

install_C_file "padding_free.c"

text \<open>Ensure that these types are padding-free (\<^typ>\<open>'a::packed_type\<close>):\<close>
thm packed_type_access_ti[where 'a=p_t_C]
thm packed_type_access_ti[where 'a=q_t_C]
thm packed_type_access_ti[where 'a=r_t_C]

end
