(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory fncall
imports "AutoCorres2.CTranslation"
begin

declare sep_conj_ac [simp add]

primrec
  fac :: "nat \<Rightarrow> nat"
where
  "fac 0 = 1"
| "fac (Suc n) = (Suc n) * fac n"


install_C_file "fncall.c"

context fncall_simpl
begin


thm has_bogus_spec_impl
thm f_impl
thm g_impl
thm h_impl
thm i_impl
thm calls_bogus_impl
thm f_body_def
thm g_body_def
thm fact_body_def


thm has_bogus_spec_modifies
thm g_modifies
thm f_modifies
thm fact_modifies

term "f_body"
term "fact_body"

end

print_locale fncall_global_addresses

print_locale g_modifies
thm g_modifies_def

print_locale f_spec
thm f_spec_def

lemma (in g_impl)
  shows "\<Gamma> \<turnstile> \<lbrace> \<acute>t_hrs = t \<rbrace> \<acute>ret' :== PROC g() \<lbrace> \<acute>t_hrs = t \<rbrace>"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg, simp)
done


lemma (in f_impl) f_impl_result:
  "\<Gamma> fncall.f = Some f_body"
  apply (rule f_impl)
  done

lemma (in g_impl) g_spec:
  shows
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== PROC g() \<lbrace> \<acute>ret' = 257 \<rbrace>"
  apply vcg
  apply simp
  done

lemma (in f_impl) foo:
  shows
   "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== PROC f(n) \<lbrace> \<acute>ret' = 1 \<rbrace>"
apply vcg
apply (simp )
done

lemma (in f_spec) foo :
shows
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL f(\<acute>n) \<lbrace> \<acute>ret' = 1 \<rbrace>"

apply vcg
done

lemma (in fact_impl) bar:
shows "\<Gamma> \<turnstile> \<lbrace> 1\<le> \<acute>n & \<acute>n \<le> 12 \<rbrace> \<acute>ret' :== CALL fact(\<acute>n) \<lbrace> \<acute>ret' = of_nat (fac (unat \<acute>n)) \<rbrace>"
apply vcg
    apply unat_arith
    apply simp
   apply simp
oops


context h_impl 
begin
interpretation h_modif: h_modifies
  apply (unfold_locales)
  apply (vcg)
  apply (simp add: meq_def)
  done

lemmas h_modifies' = h_modif.h_modifies

end

(* FIXME: I guess the issue is that A is implicitly the empty set and
this does not match with the catch rule! 
Maybe we can decouple the spec=modifies and the "real" modifies solver...
We could check if the post-conditions are canonical and only then go into
solver mode...
 *)


lemma (in i_impl) baz:
notes h_modifies = h_modifies'
shows "\<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> \<lbrace> \<acute>t_hrs = t \<rbrace> \<acute>ret' :== PROC i() \<lbrace> \<acute>t_hrs = t \<rbrace>"

  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies)
  apply simp
done

locale ih = i_impl + i_modifies + h_modifies
lemma (in ih) qux:
shows "\<Gamma> \<turnstile> \<lbrace>\<acute>t_hrs = t\<rbrace> \<acute>ret' :== CALL i() \<lbrace> t = \<acute>t_hrs \<rbrace>"
  apply vcg
  apply simp
oops

locale ff = f_spec + f_modifies
(* this lemma is bogus, because f does actually modify the globals *)
lemma (in ff) bogus1:
shows "\<Gamma> \<turnstile> \<lbrace> \<acute>t_hrs = t \<rbrace> \<acute>ret' :== CALL f(\<acute>n) \<lbrace> t = \<acute>t_hrs \<rbrace>"
apply vcg
apply simp
done

lemma (in has_bogus_spec_spec) bogus2:
shows "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL has_bogus_spec() \<lbrace> \<acute>ret' = 4 \<rbrace>"
apply vcg
done

lemma (in has_bogus_spec_impl) toldyou:
shows "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL has_bogus_spec() \<lbrace> \<acute>ret' = 3 \<rbrace>"
  apply vcg
  apply simp
done

locale calls_bogus_impl_bogus_spec = has_bogus_spec_spec + calls_bogus_impl

lemma (in calls_bogus_impl_bogus_spec) bogus3:
shows "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL calls_bogus() \<lbrace> \<acute>ret' = 4 \<rbrace>"
  apply vcg
  apply simp
done

end
