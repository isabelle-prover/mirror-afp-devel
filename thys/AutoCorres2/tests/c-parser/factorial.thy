(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory factorial
imports "AutoCorres2.CTranslation" "MachineWords"
begin

declare hrs_simps [simp add]
declare sep_conj_ac [simp add]

consts free_pool :: "nat \<Rightarrow> heap_assert"

primrec
  fac :: "nat \<Rightarrow> machine_word"
where
  "fac 0 = 1"
| "fac (Suc n) = of_nat (Suc n) * fac n"

lemma fac_unfold:
  "unat n \<noteq> 0 \<Longrightarrow> fac (unat n) = n * fac (unat (n - 1))"
  apply(case_tac "unat n")
   apply simp
  apply(subst unat_minus_one)
   apply(simp only: unat_simps)
   apply(clarify)
   apply simp
  apply clarsimp
  apply(simp only: unat_simps)
  apply(subst mod_less)
   apply (fold len_of_addr_card)
   apply unat_arith
  apply (clarsimp simp: distrib_right split: unat_splits)
  done

primrec
  fac_list :: "nat \<Rightarrow> machine_word list"
where
  "fac_list 0 = [1]"
| "fac_list (Suc n) = fac (Suc n) # fac_list n"

lemma fac_list_length [simp]:
  "length (fac_list n) = n + 1"
  by (induct n) auto

lemma fac_list_unfold:
  "unat n \<noteq> 0 \<Longrightarrow> fac_list (unat n) = fac (unat n) # fac_list (unat (n - 1))"
  apply(case_tac "unat n")
   apply clarsimp
  apply(subst unat_minus_one)
   apply force
   apply clarsimp
  done

primrec
  sep_list :: "machine_word list \<Rightarrow> machine_word ptr \<Rightarrow> heap_assert"
where
  "sep_list [] p = (\<lambda>s. p=NULL \<and> \<box> s)"
| "sep_list (x#xs) p = (\<lambda>s. \<exists>j. ((p \<mapsto> x) \<and>\<^sup>* (p +\<^sub>p 1) \<mapsto> j \<and>\<^sup>*
      sep_list xs (Ptr j)) s)"

lemma sep_list_NULL [simp]:
  "sep_list xs NULL = (\<lambda>s. xs = [] \<and> \<box> s)"
  by (case_tac xs) auto

definition
  sep_fac_list :: "machine_word \<Rightarrow> machine_word ptr \<Rightarrow> heap_assert"
where
  "sep_fac_list n p \<equiv> sep_list (fac_list (unat n)) p"

lemma sep_fac_list_unfold:
  "((\<lambda>s. unat n \<noteq> 0 \<and> (\<exists>q. (p \<mapsto> fac (unat n) \<and>\<^sup>* (p +\<^sub>p 1) \<mapsto> q \<and>\<^sup>*
      sep_fac_list (n - 1) (Ptr q)) s)) \<and>\<^sup>* R) s \<Longrightarrow>
      (sep_fac_list n p \<and>\<^sup>* R) s"
  apply (erule sep_globalise)
  apply (simp add: sep_fac_list_def fac_list_unfold)
  done

lemma sep_fac_list_points:
  "sep_points (sep_fac_list n p) s \<Longrightarrow> (p \<hookrightarrow> fac (unat n)) s"
  apply(unfold sep_points_def)
  apply(subst sep_map'_unfold)
  apply(erule sep_conj_impl)
   apply(unfold sep_fac_list_def)
   apply(case_tac "unat n")
    apply simp
    apply(unfold sep_map'_old)
    apply(erule (1) sep_conj_impl)
    apply simp
   apply clarsimp
   apply(subst (asm) sep_conj_assoc [symmetric])+
   apply(erule sep_conj_impl)
    apply simp+
  done

declare [[c_parser_feedback_level = 2]]

install_C_file "factorial.c" [memsafe]


context factorial_global_addresses
 
begin
context  includes factorial_variables
begin
term factorial_body
thm factorial_body_def
end
end
locale mem_safe_alloc = alloc_impl + alloc_spec +
  assumes mem_safe_alloc: "mem_safe (\<acute>ret' :== PROC alloc()) \<Gamma>"

context mem_safe_alloc
begin
thm mem_safe_alloc
end
lemma (in mem_safe_alloc) sep_frame_alloc:
  "\<lbrakk> \<forall>\<sigma>. \<Gamma> \<turnstile> \<lbrace>\<sigma>. (P (f \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace> \<acute>ret' :== PROC alloc() \<lbrace> (Q (g \<sigma> \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>;
      htd_ind f; htd_ind g; \<forall>s. htd_ind (g s) \<rbrakk> \<Longrightarrow>
      \<forall>\<sigma>. \<Gamma> \<turnstile> \<lbrace>\<sigma>. (P (f \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>
              \<acute>ret' :== PROC alloc()
              \<lbrace> (Q (g \<sigma> \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<sigma>))\<^bsup>sep\<^esup> \<rbrace>"
  unfolding sep_app_def
  by (rule sep_frame, auto intro!: mem_safe_alloc)

lemma (in mem_safe_alloc) alloc_spec':
  shows "\<forall>\<sigma> k R f. \<Gamma> \<turnstile>
    \<lbrace>\<sigma>. ((\<lambda>x. free_pool k) ((\<lambda>x. undefined) \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (f \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>
    \<acute>ret' :== PROC alloc()
    \<lbrace> ((\<lambda>p s. if k > 0 then (\<turnstile>\<^sub>s p \<and>\<^sup>* \<turnstile>\<^sub>s (p +\<^sub>p 1) \<and>\<^sup>*
        free_pool (k - 1)) s else (free_pool k) s \<and> p = NULL) \<acute>ret'
        \<and>\<^sup>* R (f \<sigma>))\<^bsup>sep\<^esup> \<rbrace>"
  apply clarify
  apply(insert alloc_spec)
  apply(rule_tac x=\<sigma> in spec)
  apply(rule sep_frame_alloc)
     apply(clarsimp simp: sep_app_def split: if_split_asm)
    apply simp+
  done

locale mem_safe_free = free_impl + free_spec +
  assumes mem_safe_free: "mem_safe (PROC free(\<acute>p)) \<Gamma>"

lemma (in mem_safe_free) sep_frame_free:
  "\<lbrakk> \<forall>\<sigma>. \<Gamma> \<turnstile> \<lbrace>\<sigma>. (P (f \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace> PROC free(\<acute>p) \<lbrace> (Q (g \<sigma> \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>;
      htd_ind f; htd_ind g; \<forall>s. htd_ind (g s) \<rbrakk> \<Longrightarrow>
      \<forall>\<sigma>. \<Gamma> \<turnstile> \<lbrace>\<sigma>. (P (f \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>
              PROC free(\<acute>p)
              \<lbrace> (Q (g \<sigma> \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<sigma>))\<^bsup>sep\<^esup> \<rbrace>"
  apply(simp only: sep_app_def)
  apply(rule sep_frame, auto intro!: mem_safe_free)
  done


lemma (in mem_safe_free) free_spec':
  shows "\<forall>\<sigma> k R f. \<Gamma> \<turnstile>
    \<lbrace>\<sigma>. ((\<lambda>p. sep_cut' (ptr_val p) (2 * size_of TYPE(machine_word)) \<and>\<^sup>* free_pool k) \<acute>p  \<and>\<^sup>* R (f \<acute>(\<lambda>x. x)))\<^bsup>sep\<^esup> \<rbrace>
    PROC free(\<acute>p)
    \<lbrace> ((\<lambda>x. free_pool (k + 1)) ((\<lambda>x. ()) \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (f \<sigma>))\<^bsup>sep\<^esup> \<rbrace>"
  apply clarify
  apply(insert free_spec)
  apply(rule_tac x=\<sigma> in spec)
  apply(rule sep_frame_free)
     apply(clarsimp simp: sep_app_def split: if_split_asm)
    apply simp+
  done



lemma double_word_sep_cut':
  "(p \<mapsto> x \<and>\<^sup>* (p +\<^sub>p 1) \<mapsto> y) s \<Longrightarrow> sep_cut' (ptr_val (p::machine_word ptr)) (2*word_size) s"
  supply word_size_def [simp]
apply(clarsimp simp: sep_conj_def sep_cut'_def dest!: sep_map_dom)
apply(subgoal_tac "{ptr_val p..+word_size} \<subseteq> {ptr_val p..+(2*word_size)}")
 apply(subgoal_tac "{ptr_val p+(of_nat word_size)..+word_size} \<subseteq> {ptr_val p..+(2*word_size)}")
  apply rule
   apply (fastforce simp: ptr_add_def)
  apply clarsimp
  apply(drule intvlD)
  apply (clarsimp simp add:)
    apply(case_tac "k < word_size")
  apply (simp add: word_size_def)
   apply(erule intvlI)
  apply(erule notE)
  apply(clarsimp simp: intvl_def)
  apply(rule_tac x="k - word_size" in exI)
  apply rule
   apply(simp only: unat_simps)
   apply(subst mod_less)
    apply(simp add: addr_card)
   apply (simp add: ptr_add_def addr_card)
  apply simp
 apply(clarsimp simp: intvl_def)
 apply(rule_tac x="word_size+k" in exI)
 apply simp
apply(rule intvl_start_le)
apply simp
done

context factorial_impl
begin
  thm factorial_body_def
end
locale specs =  mem_safe_alloc + mem_safe_free + factorial_impl
begin
declare [[ML_print_depth = 10000]]

interpretation factorial_spec: factorial_spec
  apply (unfold_locales)
  apply(hoare_rule HoarePartial.ProcRec1)
  apply (hoare_rule anno = "factorial_invs_body k" in HoarePartial.annotateI)
   prefer 2
   apply (simp add: whileAnno_def factorial_invs_body_def)
  apply(subst factorial_invs_body_def)
  apply(unfold sep_app_def) 
  apply (vcg exspec=alloc_spec' exspec=free_spec' )
    apply (fold lift_def)
    apply(clarsimp simp: sep_app_def)
    apply (rename_tac actuals1 global_exn_var ret' p' ) 
    apply (rule conjI)
     apply clarsimp
     apply(rule_tac x=k in exI)
     apply(rule_tac x="\<lambda>p. \<box>" in exI)
     apply(rule_tac x="\<lambda>s. undefined" in exI)
     apply clarsimp
     apply (rule conjI)
      apply (clarsimp )
     apply clarsimp
     apply (rename_tac a b actuals2)
     apply(subgoal_tac "(\<turnstile>\<^sub>s (actuals2 \<cdot> alloc.ret') \<and>\<^sup>* sep_true) (lift_state (a,b))")
      prefer 2
      apply(drule sep_conj_sep_true_right)
      apply simp
     apply(subgoal_tac "(\<turnstile>\<^sub>s ((actuals2 \<cdot> alloc.ret') +\<^sub>p 1) \<and>\<^sup>* sep_true) (lift_state (a,b))")
      prefer 2
      apply (subst (asm) (1)  sep_conj_com)
      apply (subst (asm) sep_conj_assoc [])
      apply (subst (asm) (2)  sep_conj_com)
      apply (subst (asm) sep_conj_assoc [symmetric])
      apply (subst (asm) (1)  sep_conj_com)
      apply (subst (asm) sep_conj_assoc [])
      apply(drule  sep_conj_sep_true_left)
      apply simp
      apply (subst (asm) (3)  sep_conj_com)
      apply(subst (asm) sep_conj_assoc [symmetric])+
      apply(drule_tac Q="free_pool (k - Suc 0)" in sep_conj_sep_true_right)
      apply simp
     apply(simp add: tagd_ptr_safe tagd_g c_guard_ptr_aligned c_guard_NULL)
     apply(simp add: sep_fac_list_def)
     apply (subst (1)  sep_conj_com)
     apply (subst  sep_conj_assoc [])
    apply (subst (2)  sep_conj_com)
     apply(sep_select_tac "(_ +\<^sub>p _) \<mapsto> _")
     apply(rule sep_heap_update_global')
     apply simp
     apply (subst (1)  sep_conj_com)
     apply (subst  sep_conj_assoc [])
     apply(rule sep_heap_update_global')
     apply simp
    apply clarsimp
    apply(rule_tac x=k in exI)
    apply clarsimp
    apply(rule_tac x="k - Suc (unat ((actuals1 \<cdot> n) - 1))" in exI)
    apply clarsimp
    apply(rule_tac x="\<lambda>(n,p). sep_fac_list (n - 1) p" in exI)
    apply(rule_tac x="\<lambda>s. (s \<cdot>\<^sub>\<L> n, s \<cdot>\<^sub>\<L> q)" in exI)
    apply (rule conjI, clarsimp)
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply(simp add: sep_fac_list_def)
     apply(rule_tac x="fac_list (unat ((actuals1 \<cdot> n) - 1))" in exI)
     apply clarsimp
    apply clarsimp
    apply (rename_tac actuals2 ab bb actuals3)
    apply(subgoal_tac "(\<turnstile>\<^sub>s (actuals3 \<cdot> alloc.ret') \<and>\<^sup>* sep_true) (lift_state (ab,bb))")
     prefer 2
     apply(erule (1) sep_conj_impl)
     apply simp
    apply(subgoal_tac "(\<turnstile>\<^sub>s ((actuals3 \<cdot> alloc.ret') +\<^sub>p 1) \<and>\<^sup>* sep_true) (lift_state (ab,bb))")
     prefer 2
     apply(subgoal_tac "(\<turnstile>\<^sub>s (actuals3 \<cdot> alloc.ret') \<and>\<^sup>*
                         \<turnstile>\<^sub>s ((actuals3 \<cdot> alloc.ret') +\<^sub>p 1) \<and>\<^sup>*
                         sep_fac_list ((actuals1 \<cdot> n) - 1) (actuals2 \<cdot> ret') \<and>\<^sup>*
                         free_pool (k - Suc (unat (actuals1 \<cdot> n)))) =
                         (\<turnstile>\<^sub>s ((actuals3 \<cdot> alloc.ret') +\<^sub>p 1) \<and>\<^sup>* (\<turnstile>\<^sub>s (actuals3 \<cdot> alloc.ret') \<and>\<^sup>*
                         sep_fac_list ((actuals1 \<cdot> n) - 1) (actuals2 \<cdot> ret') \<and>\<^sup>*
                         free_pool (k - Suc (unat (actuals1 \<cdot> n)))))")
      prefer 2
      apply simp
     apply (subst (asm) sep_conj_assoc [symmetric])
     apply (subst (asm) (2)  sep_conj_com)
     apply (subst (asm) sep_conj_assoc [])
     apply(erule (1) sep_conj_impl)
     apply simp
    apply(sep_point_tac sep_fac_list_points)
    apply(simp add: tagd_ptr_safe tagd_g sep_map'_g c_guard_ptr_aligned c_guard_NULL sep_map'_lift)
    apply(rule sep_fac_list_unfold)
    apply clarsimp    
    apply (rule conjI, unat_arith)
    apply sep_exists_tac
    apply(rule_tac x="ptr_val (actuals2 \<cdot> ret')" in exI)
    apply clarsimp
    apply(subst fac_unfold)
     apply unat_arith
    apply clarsimp
    apply(sep_select_tac "(_ +\<^sub>p _) \<mapsto> _")
    apply(rule sep_heap_update_global')
    apply(sep_select_tac "_ \<mapsto> _")
      apply(rule sep_heap_update_global')
      apply(erule (1) sep_conj_impl)+
      apply clarsimp
   apply clarsimp
   apply(case_tac xs)
    apply simp
   apply clarsimp
   apply sep_exists_tac
   apply clarsimp
   apply sep_point_tac
   apply(simp add: sep_map'_g c_guard_ptr_aligned c_guard_NULL sep_map'_lift)
   apply(rule_tac x="k - Suc (length list)" in exI)
   apply(rule_tac x="\<lambda>p. sep_list list (Ptr j)" in exI)
   apply(rule_tac x="\<lambda>x. ()" in exI)
   apply(clarsimp simp: sep_app_def)
   apply (rename_tac actuals1 aa list j) 
   apply (rule conjI)
    apply(subgoal_tac "((actuals1 \<cdot> q) \<mapsto> aa \<and>\<^sup>* sep_list list (Ptr j) \<and>\<^sup>*
                         ((actuals1 \<cdot> q) +\<^sub>p 1) \<mapsto> j \<and>\<^sup>* free_pool (k - Suc (length list))) =
                       (sep_list list (Ptr j) \<and>\<^sup>* ((actuals1 \<cdot> q) \<mapsto> aa \<and>\<^sup>*
                         ((actuals1 \<cdot> q) +\<^sub>p 1) \<mapsto> j \<and>\<^sup>* free_pool (k - Suc (length list))))")
     apply(erule (1) sep_conj_impl)
     apply simp
     apply (subst (asm) (1) sep_conj_com)
     apply (subst (asm) sep_conj_assoc [])
     apply (subst (asm) (2) sep_conj_com)
     apply(erule sep_conj_impl)
      apply simp
     apply(erule double_word_sep_cut'[ simplified word_size_def,simplified])
    apply simp
   apply clarsimp
   apply(subgoal_tac "Suc (k - Suc (length list)) = k - length list")
    apply force
   apply arith
  apply clarsimp
  done
end








lemma proc_deps_intra_deps: 
  assumes proc_deps: "p \<in> proc_deps X \<Gamma>"
  assumes X: "X = Call x"
  assumes bdy: "\<Gamma> x = Some bdy"
  shows "p = x \<or> p \<in> ({y. (\<exists>z \<in> intra_deps bdy.  y \<in> proc_deps (Call z) \<Gamma>)})"
  using proc_deps X bdy 
  apply (induct arbitrary: x)
   apply simp
  apply (auto  split: option.splits)
  using proc_deps.simps by fastforce+

lemma proc_deps_intra_deps_trans: 
  assumes p_z: "p \<in> proc_deps Z \<Gamma>"
  assumes Z: "Z = Call z"
  assumes z_bdy:  "z \<in> intra_deps bdy"
  shows "p \<in> proc_deps bdy \<Gamma>"
  using p_z Z z_bdy 
proof (induct arbitrary: z)
  case (1 y)
  from 1 have y_z: "y \<in> intra_deps (Call z)" by simp
  hence "y=z" by simp
  with 1 have "y \<in> intra_deps bdy"
    by simp
  from proc_deps.intros(1)[OF this]
  show ?case .
next
  case 2
  then show ?case
    by (auto intro: proc_deps.intros)
qed

lemma proc_deps_trans: 
  assumes p_z: "p \<in> proc_deps Z \<Gamma>"
  assumes Z: "Z = Call z"
  assumes z_bdy:  "z \<in> proc_deps bdy \<Gamma>"
  shows "p \<in> proc_deps bdy \<Gamma>"
  using p_z Z z_bdy 
  by (induct arbitrary: z bdy) (auto intro: proc_deps.intros)


lemma callees_proc_deps:
  assumes bdy: "\<Gamma> x = Some bdy" 
  assumes p: "p \<in> ({y. (\<exists>z \<in> intra_deps bdy.  y \<in> proc_deps (Call z) \<Gamma>)})" 
  shows  "p \<in> proc_deps (Call x) \<Gamma>"
proof (cases "p=x")
  case True thus ?thesis by (auto intro: proc_deps.intros)
next
  case False
  note neq_p_x = False
    from p obtain z where z: "z \<in> intra_deps bdy" and p_z: "p \<in> proc_deps (Call z) \<Gamma>" 
      by auto
  show ?thesis
  proof -
    have z_x: "z \<in> proc_deps (Call x) \<Gamma>"
      apply (rule proc_deps.intros(2) [where \<Gamma>=\<Gamma>, OF _ bdy z]) 
      apply simp
      done
    from proc_deps_trans [OF p_z refl z_x]
    show ?thesis .
  qed
qed

lemma proc_deps_body_characteristic:
assumes bdy: "\<Gamma> x = Some bdy" 
shows "proc_deps (Call x) \<Gamma> = insert x {y. (\<exists>z \<in> intra_deps bdy. y \<in> proc_deps (Call z) \<Gamma>)}"
  using callees_proc_deps [OF bdy]
  proc_deps_intra_deps [OF _ refl bdy]
  by auto


lemma (in specs) mem_safe_factorial:
  assumes free_leaf: "proc_deps (Call factorial.free) \<Gamma> = {}"
  assumes alloc_leaf: "proc_deps (Call factorial.alloc) \<Gamma> = {}"
  assumes free_bdy: "\<Gamma> factorial.free = Some free_bdy"
  assumes alloc_bdy: "\<Gamma> factorial.alloc = Some alloc_bdy"
  assumes intra_safe_free: "intra_safe free_bdy"
  assumes intra_safe_alloc: "intra_safe alloc_bdy"
  shows "mem_safe (\<acute>ret' :== PROC factorial(\<acute>n)) \<Gamma>"
proof -
  note hrs_simps [simp del]
  have intra_deps: "intra_deps (factorial_body)  =  {factorial.free, factorial.alloc, factorial.factorial}"
    by (auto simp add: factorial_body_def lvar_nondet_init_def call_exn_def block_exn_def creturn_def 
   ccatchreturn_def whileAnno_def)
  with proc_deps_body_characteristic [OF factorial_impl] free_leaf alloc_leaf
  have proc_deps_fac: "proc_deps (Call factorial.factorial) \<Gamma> = {factorial.free, factorial.alloc, factorial.factorial}"
    by simp
  have mem_safe_p: "All (mem_safe (Spec {(s, t). \<exists>v. t = s\<langle>p :=\<^sub>\<L> \<lambda>_. v\<rangle>}))"
    apply (auto simp add: mem_safe_def)
    apply (case_tac t)
       apply (auto elim!: exec_Normal_elim_cases)   
    apply (auto simp add: restrict_safe_def restrict_safe_OK_def)
    apply (rule exec.Spec)
    apply clarsimp 
    apply (rule_tac x="v" in exI)
    apply (case_tac s)
    apply (auto simp add:  restrict_htd_def)
    done


  have mem_safe_q: "All (mem_safe (Spec {(s, t). \<exists>v. t = s\<langle>q :=\<^sub>\<L> \<lambda>_. v\<rangle>}))"
    apply (auto simp add: mem_safe_def)
    apply (case_tac t)
       apply (auto elim!: exec_Normal_elim_cases)   
    apply (auto simp add: restrict_safe_def restrict_safe_OK_def)
    apply (rule exec.Spec)
    apply clarsimp 
    apply (rule_tac x="v" in exI)
    apply (case_tac s)
    apply (auto simp add:  restrict_htd_def)
    done

  have mem_safe_ret: "All (mem_safe (Spec {(s, t). \<exists>v. t = s\<langle>ret' :=\<^sub>\<L> \<lambda>_. v\<rangle>}))"
    apply (auto simp add: mem_safe_def)
    apply (case_tac t)
       apply (auto elim!: exec_Normal_elim_cases)   
    apply (auto simp add: restrict_safe_def restrict_safe_OK_def)
    apply (rule exec.Spec)
    apply clarsimp 
    apply (rule_tac x="v" in exI)
    apply (case_tac s)
    apply (auto simp add:  restrict_htd_def)
    done

  from mem_safe_p mem_safe_q mem_safe_ret have intra_safe_factorial: "intra_safe factorial_body"
    apply (simp add: factorial_body_def lvar_nondet_init_def 
     call_exn_def block_exn_def creturn_def 
     ccatchreturn_def whileAnno_def intra_sc) 
    done
  show ?thesis
    apply(subst mem_safe_restrict)
    apply(rule intra_mem_safe)
     apply (simp only: proc_deps_fac)
     apply (auto simp add: intra_safe_factorial restrict_map_def 
       free_bdy alloc_bdy intra_safe_free intra_safe_alloc factorial_impl
       split: if_split_asm)
    done
qed

end
