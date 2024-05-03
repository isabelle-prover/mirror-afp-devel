(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory codetests
imports "AutoCorres2.CTranslation"
begin

local_setup \<open>
  TermsTypes.prim_mk_defn "foo" @{term "33::nat"} [] #> snd
\<close>

term "foo"
thm "foo_def"


ML \<open>
  Context.>> (Context.map_theory (
    RecursiveRecordPackage.define_record_type [
      {record_name = "myrecord",
       fields = [{fldname = "fld1", fldty = @{typ "nat"}},
                 {fldname = "myset", fldty = @{typ "nat \<Rightarrow> bool"}}]}
    ]))
\<close>

thm myrecord_accupd_same

end
