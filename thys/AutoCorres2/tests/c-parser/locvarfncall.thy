(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory locvarfncall
imports "AutoCorres2.CTranslation"
begin

install_C_file "locvarfncall.c"

context locvarfncall_simpl
begin

thm something_body_def
thm something_else_body_def
thm another_body_def
end

 
lemma (in something_impl) foo: "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL something() \<lbrace> \<acute>ret' = 112 \<rbrace>"
apply vcg
apply simp

done

lemma (in something_else_impl) "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL something_else(4)
           \<lbrace> \<acute>ret' = 50 \<rbrace>"
apply vcg
apply simp
done

text \<open>Note that there is no explicit distinctness for the local variables 
of different procedures. Quite the opposite, parameters and local variables are 
encoded positionally for each procedure.
However, the calling conventions encoded in SIMPL procedure calls maintain the expected
'stack semantics' and don't get into the way even when procedures are inlined.
\<close>


lemma (in another_impl) 
  shows "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL another(4)
           \<lbrace> \<acute>ret' = 51 \<rbrace>"
apply vcg
apply simp
done

end

