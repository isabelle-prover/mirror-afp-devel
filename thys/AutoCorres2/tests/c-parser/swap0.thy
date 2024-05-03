(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory swap0
imports "AutoCorres2.CTranslation"
begin

declare hrs_simps [simp add]
declare sep_conj_ac [simp add]

thm sep_conj_ac
install_C_file "swap0.c" [memsafe]

context swap_impl
begin
interpretation swap_spec
  apply (unfold_locales)
apply (hoare_rule HoarePartial.ProcNoRec1)
apply(unfold sep_app_def)
apply vcg
  apply(fold lift_def)
apply(sep_point_tac)
    apply(simp add: sep_map'_ptr_safe sep_map'_ptr_aligned sep_map'_NULL sep_map'_lift sep_map'_g)
  apply (subst sep_conj_ac)
apply(rule sep_heap_update_global)
apply(sep_select_tac "p \<mapsto> _")
apply(rule sep_heap_update_global)
  apply (subst (asm) sep_conj_ac)
  apply (subst  sep_conj_ac)
apply(erule sep_conj_impl)
 apply simp+
  done


declare hrs_simps [simp del]

lemma mem_safe_swap:
  "mem_safe (PROC swap(\<acute>p,\<acute>q)) \<Gamma>"
apply(insert swap_impl)
apply(unfold swap_body_def)
apply(subst mem_safe_restrict)
apply(rule intra_mem_safe)
 apply(simp_all add: restrict_map_def ccatchreturn_def split: if_split_asm)
  apply(auto simp: whileAnno_def intra_sc)
done

declare hrs_simps [simp add]


lemma sep_frame_swap:
  "\<lbrakk> \<forall>\<sigma>. \<Gamma> \<turnstile> \<lbrace>\<sigma>. (P (f \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace> PROC swap(\<acute>p,\<acute>q) \<lbrace> (Q (g \<sigma> \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>;
      htd_ind f; htd_ind g; \<forall>s. htd_ind (g s) \<rbrakk> \<Longrightarrow>
      \<forall>\<sigma>. \<Gamma> \<turnstile> \<lbrace>\<sigma>. (P (f \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>
          PROC swap(\<acute>p,\<acute>q)
          \<lbrace> (Q (g \<sigma> \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<sigma>))\<^bsup>sep\<^esup> \<rbrace>"
apply(simp only: sep_app_def)
apply(rule sep_frame)
    apply(auto intro!: mem_safe_swap)
done

lemma expand_swap_pre:
  "(p_' s \<mapsto> x \<and>\<^sup>* q_' s \<mapsto> y) =
    (\<lambda>(v,w). v \<mapsto> x \<and>\<^sup>* w \<mapsto> y) (p_' s,q_' s)"
  by simp

lemma expand_swap_post:
  "(p_' s \<mapsto> x \<and>\<^sup>* q_' s \<mapsto> y) =
    (\<lambda>(v,w) s. v \<mapsto> x \<and>\<^sup>* w \<mapsto> y) (p_' s,q_' s) (\<lambda>s. s)"
  by simp

lemma swap_spec:
  "\<forall>\<sigma> s x y R f. \<Gamma> \<turnstile>
    \<lbrace>\<sigma>. (\<acute>p \<mapsto> x \<and>\<^sup>* \<acute>q \<mapsto> y \<and>\<^sup>* R (f \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>
    PROC swap(\<acute>p,\<acute>q)
    \<lbrace>(\<^bsup>\<sigma>\<^esup>p \<mapsto> y \<and>\<^sup>* \<^bsup>\<sigma>\<^esup>q \<mapsto> x \<and>\<^sup>* R (f \<sigma>))\<^bsup>sep\<^esup> \<rbrace>"
apply clarify
apply(subst sep_conj_assoc [symmetric])+
apply(subst expand_swap_pre)
apply(subst (2) expand_swap_post)
apply(insert swap_spec)
apply(rule_tac x=\<sigma> in spec)
apply(rule sep_frame_swap)
   apply(unfold sep_app_def)
   apply clarsimp
  apply(simp add: htd_ind_def)+
done
end

context test_impl
begin
interpretation test_spec
  apply unfold_locales
  apply(hoare_rule HoarePartial.ProcNoRec1)
  apply(unfold sep_app_def)
  apply vcg
  apply(fold lift_def)
  apply(unfold sep_map_any_old)
  apply sep_exists_tac
  apply clarsimp
  apply sep_point_tac
  apply(unfold sep_app_def)
  subgoal for x y h d phantom_machine_state locals global_exn_var v
    apply(simp add: sep_map'_ptr_safe sep_map'_ptr_aligned sep_map'_NULL sep_map'_lift sep_map'_g)
    apply(rule_tac x=x in exI)
    apply(rule_tac x=y in exI)
    apply(rule_tac x="(\<lambda>z. locals \<cdot> c \<mapsto> (x + y))" in exI)
    apply(rule_tac x="\<lambda>s. undefined" in exI)
    apply rule
     apply(sep_select_tac "locals \<cdot> c \<mapsto> _")
     apply(rule sep_heap_update_global)
     apply (subst sep_conj_ac (1))
     apply (subst sep_conj_ac (2))
     apply(erule sep_conj_impl, simp)+
     apply simp
    apply clarsimp

    apply(rule_tac x="x + y" in exI)
    apply(rule_tac x=y in exI)
    apply(rule_tac x="(\<lambda>z. locals \<cdot> b \<mapsto> x)" in exI)
    apply fastforce
    done
  done
thm test_spec
end




end
