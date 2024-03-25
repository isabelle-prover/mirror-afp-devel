(*******************************************************************************

  Project: Sumcheck Protocol

  Authors: Azucena Garvia Bosshard <zucegb@gmail.com>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
           Jonathan Bootle, IBM Research Europe <jbt@zurich.ibm.com>

*******************************************************************************)

section \<open>Instantiation for Multivariate Polynomials\<close>

theory Polynomial_Instantiation
  imports 
    "Polynomials.More_MPoly_Type"
begin

text \<open>
\textbf{NOTE:} if considered to be useful enough, the definitions and lemmas in this theory could 
be moved to the theory @{theory "Polynomials.More_MPoly_Type"}.
\<close>

text \<open>Define instantiation of mpoly's. The conditions @{term "(\<noteq>) 1"} and @{term "(\<noteq>) 0"} in 
the sets being multiplied or added over are needed to prove the correspondence with evaluation: 
a full instance corresponds to an evaluation (see lemma below).\<close>

subsection \<open>Instantiation of monomials\<close>

type_synonym ('a, 'b) subst = "'a \<rightharpoonup> 'b"

lift_definition 
  inst_monom_coeff :: \<open>(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> (nat, 'a) subst \<Rightarrow> 'a::comm_semiring_1\<close> 
  is \<open>\<lambda>m \<sigma>. (\<Prod>v | v \<in> dom \<sigma> \<and> the (\<sigma> v) ^ m v \<noteq> 1. the (\<sigma> v) ^ m v)\<close> .

lift_definition 
  inst_monom_resid :: \<open>(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> (nat, 'a) subst \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat)\<close>  
  is \<open>(\<lambda>m \<sigma> v. m v when v \<notin> dom \<sigma>)\<close>
  by (metis (mono_tags, lifting) finite_subset mem_Collect_eq subsetI zero_when) 

lemmas inst_monom_defs = inst_monom_coeff_def inst_monom_resid_def

lemma lookup_inst_monom_resid:
  shows \<open>lookup (inst_monom_resid m \<sigma>) v = (if v \<in> dom \<sigma> then 0 else lookup m v)\<close>
  by transfer simp


subsection \<open>Instantiation of polynomials\<close>

definition 
  inst_fun :: \<open>((nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a) \<Rightarrow> (nat, 'a) subst \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a::comm_semiring_1\<close> where
  \<open>inst_fun p \<sigma> = (\<lambda>m. (\<Sum>m' | inst_monom_resid m' \<sigma> = m \<and> p m' * inst_monom_coeff m' \<sigma> \<noteq> 0.
                               p m' * inst_monom_coeff m' \<sigma>))\<close>

lemma finite_inst_fun_keys: 
  assumes \<open>finite {m. p m \<noteq> 0}\<close>
  shows \<open>finite {m. (\<Sum>m' | inst_monom_resid m' \<sigma> = m \<and> p m' \<noteq> 0 \<and> inst_monom_coeff m' \<sigma> \<noteq> 0.
                               p m' * inst_monom_coeff m' \<sigma>) \<noteq> 0}\<close>
proof -
  from \<open>finite {m. p m \<noteq> 0}\<close>
  have \<open>finite ((\<lambda>m'. inst_monom_resid m' \<sigma>)`{x. p x \<noteq> 0})\<close> by auto
  moreover 
  have \<open>{m. (\<Sum>m' | inst_monom_resid m' \<sigma> = m \<and> p m' \<noteq> 0 \<and> inst_monom_coeff m' \<sigma> \<noteq> 0. 
                         p m' * inst_monom_coeff m' \<sigma>) \<noteq> 0}
            \<subseteq> (\<lambda>m'. inst_monom_resid m' \<sigma>)`{m. p m \<noteq> 0}\<close>
    by (auto elim: sum.not_neutral_contains_not_neutral)
  ultimately show ?thesis
    by (auto elim: finite_subset)
qed

lemma finite_inst_fun_keys_ext:
  assumes \<open>finite {m. p m \<noteq> 0}\<close>
  shows  "finite {a. (\<Sum>m' | inst_monom_resid m' \<sigma> = a \<and> p m' \<noteq> 0 \<and> inst_monom_coeff m' \<sigma> \<noteq> 0.
        p m' * inst_monom_coeff m' \<sigma> * (\<Prod>aa. the (\<rho> aa) ^ lookup (inst_monom_resid m' \<sigma>) aa)) \<noteq> 0}"
proof -
  from \<open>finite {m. p m \<noteq> 0}\<close>
  have \<open>finite ((\<lambda>m'. inst_monom_resid m' \<sigma>)`{x. p x \<noteq> 0})\<close> by auto
  moreover 
  have \<open>{m. (\<Sum>m' | inst_monom_resid m' \<sigma> = m \<and> p m' \<noteq> 0 \<and> inst_monom_coeff m' \<sigma> \<noteq> 0. 
                         p m' * inst_monom_coeff m' \<sigma> * 
                         (\<Prod>aa. the (\<rho> aa) ^ lookup (inst_monom_resid m' \<sigma>) aa)) \<noteq> 0}
            \<subseteq> (\<lambda>m'. inst_monom_resid m' \<sigma>)`{m. p m \<noteq> 0}\<close>
    by (auto elim: sum.not_neutral_contains_not_neutral)
  ultimately show ?thesis
    by (auto elim: finite_subset)
qed

lift_definition 
  inst_aux :: \<open>((nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> (nat, 'a) subst \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::semidom\<close> 
  is inst_fun 
  by (auto simp add: inst_fun_def intro: finite_inst_fun_keys)

lift_definition inst :: \<open>'a mpoly \<Rightarrow> (nat, 'a::semidom) subst \<Rightarrow> 'a mpoly\<close> 
  is inst_aux .

lemmas inst_defs = inst_def inst_aux_def inst_fun_def


subsection \<open>Full instantiation corresponds to evaluation\<close>

lemma dom_Some: \<open>dom (Some o f) = UNIV\<close>
  by (simp add: dom_def)

lemma inst_full_eq_insertion:      
  fixes p :: \<open>('a::semidom) mpoly\<close> and \<sigma> :: \<open>nat \<Rightarrow> 'a\<close> 
  shows \<open>inst p (Some o \<sigma>) = Const (insertion \<sigma> p)\<close>
proof transfer
  fix p :: \<open>(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a\<close> and \<sigma> :: \<open>nat \<Rightarrow> 'a\<close> 
  show \<open>inst_aux p (Some o \<sigma>) = Const\<^sub>0 (insertion_aux \<sigma> p)\<close>
    unfolding poly_mapping_eq_iff
    apply (simp add: Const\<^sub>0_def inst_aux.rep_eq inst_fun_def inst_monom_defs
                     Poly_Mapping.single.rep_eq insertion_aux.rep_eq insertion_fun_def)
    apply (rule ext)
    subgoal for m
      by (cases "m = 0") 
         (simp_all add: Sum_any.expand_set Prod_any.expand_set dom_Some)
    done
qed


end