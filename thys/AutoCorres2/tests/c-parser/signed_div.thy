(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory signed_div
imports "AutoCorres2.CTranslation"
begin

install_C_file "signed_div.c"

lemma exec_lvar_nondet_init_simp: "(\<Gamma>\<turnstile> \<langle>lvar_nondet_init upd, Normal s\<rangle> \<Rightarrow> t) = (\<exists>v. t = Normal (upd (\<lambda>_. v) s))"
  apply (simp add: lvar_nondet_init_def)
  apply (subst exec.simps)
  apply auto
  done

lemma ex_extend:"((\<exists>v. s = f v) \<and> P s) = (\<exists>v. s = f v \<and> P (f v))"
by auto




lemma (in f_impl) f_result:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL f(5, -1) \<lbrace> \<acute>ret' = -5 \<rbrace>"
  apply vcg
  apply (clarsimp simp: sdiv_word_def sdiv_int_def)
  done

lemma (in f_impl) f_overflow:
  shows "\<lbrakk> s \<cdot>\<^sub>\<L> a = of_int (- (2^31)); s \<cdot>\<^sub>\<L> b = -1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<langle> Call signed_div.f ,Normal s\<rangle> \<Rightarrow> Fault SignedArithmetic"
  apply (rule exec.Call [where \<Gamma>=\<Gamma>, OF f_impl, simplified f_body_def creturn_def])
  apply (rule exec.CatchMiss)
  apply (subst exec.simps, clarsimp simp del: word_neq_0_conv simp: sdiv_word_def sdiv_int_def)
  apply (rule_tac x = "Fault SignedArithmetic" in exI)
  apply (subst exec.simps, clarsimp simp del: word_neq_0_conv simp: sdiv_word_def sdiv_int_def)
  apply (subst exec_lvar_nondet_init_simp)
  apply (subst (1) ex_extend)
  apply (subst exec.simps, clarsimp simp del: word_neq_0_conv simp: sdiv_word_def sdiv_int_def)
  apply (subst exec.simps, clarsimp simp del: word_neq_0_conv simp: sdiv_word_def sdiv_int_def)
  apply simp 
  done

lemma (in g_impl) g_result:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL g(-5, 10) \<lbrace> \<acute>ret' = -5 \<rbrace>"
  apply vcg
  apply (clarsimp simp: smod_word_def smod_int_def sdiv_int_def)
  done

lemma (in h_impl) h_result:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL h(5, -1) \<lbrace> \<acute>ret' = 0 \<rbrace>"
  apply vcg
  apply (simp add: word_div_def uint_word_ariths)
  done

lemma (in f_impl) i_result:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret' :== CALL f(5, -1) \<lbrace> \<acute>ret' = -5 \<rbrace>"
  apply vcg
  apply (clarsimp simp: sdiv_word_def sdiv_int_def)
  done

end
