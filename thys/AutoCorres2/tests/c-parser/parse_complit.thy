(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_complit
imports "AutoCorres2.CTranslation"
begin

install_C_file "parse_complit.c"

context parse_complit_simpl
begin
thm simple1_body_def
thm simple2_body_def
thm simple3_body_def
thm simple4_body_def
thm simple5_body_def
thm f_body_def
thm g_body_def
thm h_body_def
thm function_body_def
thm function2_body_def
thm function3_body_def
thm sjw_body_def
thm enum_test_body_def
thm main_body_def
end

context main_impl 
begin
term "s \<cdot> aa :: 32 signed word[11]"  (* should have an 11-wide array of ints as its range *)
end

lemma (in function2_impl) f2_test:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL function2() \<lbrace> \<acute>ret' = 3 \<rbrace>"
apply vcg
apply simp
done

lemma (in enum_test_impl) foo:
  "\<forall>x. \<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL enum_test(x) \<lbrace> \<acute>ret' = -1 \<rbrace>"
apply vcg
apply (simp add: val2_def)
done

end
