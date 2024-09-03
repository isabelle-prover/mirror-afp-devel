theory AnswerIndexedFamilies
imports Main
begin

chapter \<open>Answer-Indexed Families\<close>

typedecl 'a state
consts L :: \<open>'a state => 'a set\<close>
datatype answer = T | F
type_synonym 'a AiF = \<open>answer \<Rightarrow> 'a set\<close>

fun and_AiF :: \<open>'a AiF \<Rightarrow> 'a AiF \<Rightarrow> 'a AiF\<close> (infixl \<open>\<and>\<sqdot>\<close> 60) where
  \<open>(a \<and>\<sqdot> b) T = a T \<inter> b T\<close>
| \<open>(a \<and>\<sqdot> b) F = a F \<union> b F\<close>

fun or_AiF :: \<open>'a AiF \<Rightarrow> 'a AiF \<Rightarrow> 'a AiF\<close> (infixl \<open>\<or>\<sqdot>\<close> 59) where
  \<open>(a \<or>\<sqdot> b) T = a T \<union> b T\<close>
| \<open>(a \<or>\<sqdot> b) F = a F \<inter> b F\<close>

fun not_AiF :: \<open>'a AiF \<Rightarrow> 'a AiF\<close> (\<open>\<not>\<sqdot> _\<close>) where
  \<open>(\<not>\<sqdot> a) T = a F\<close>
| \<open>(\<not>\<sqdot> a) F = a T\<close>

fun univ_AiF :: \<open>'a AiF\<close> (\<open>T\<bullet>\<close>) where
  \<open>T\<bullet> T = UNIV\<close>
| \<open>T\<bullet> F = {}\<close>

fun satisfying_AiF :: \<open>'a \<Rightarrow> 'a state AiF\<close> (\<open>sat\<bullet>\<close>) where
  \<open>sat\<bullet> x T = {state. x \<in> L state}\<close>
| \<open>sat\<bullet> x F = {state. x \<notin> L state}\<close>

section \<open>Example: Propositional logic\<close>

datatype (atoms_plogic: 'a) plogic =
    True_plogic                               (\<open>true\<^sub>p\<close>)
  | Prop_plogic \<open>'a\<close>                            (\<open>prop\<^sub>p'(_')\<close>)
  | Not_plogic \<open>'a plogic\<close>                    (\<open>not\<^sub>p _\<close> [85] 85)
  | Or_plogic  \<open>'a plogic\<close> \<open>'a plogic\<close>        (\<open>_ or\<^sub>p _\<close> [82,82] 81)
  | And_plogic \<open>'a plogic\<close> \<open>'a plogic\<close>        (\<open>_ and\<^sub>p _\<close> [82,82] 81)

fun plogic_semantics :: \<open>'a plogic \<Rightarrow> 'a state AiF\<close> (\<open>\<lbrakk>_\<rbrakk>\<^sub>p\<close>) where
  \<open>\<lbrakk> true\<^sub>p    \<rbrakk>\<^sub>p = T\<bullet>\<close>
| \<open>\<lbrakk> not\<^sub>p \<phi>   \<rbrakk>\<^sub>p = \<not>\<sqdot> \<lbrakk>\<phi>\<rbrakk>\<^sub>p\<close>
| \<open>\<lbrakk> prop\<^sub>p(a) \<rbrakk>\<^sub>p = sat\<bullet> a\<close>
| \<open>\<lbrakk> \<phi> or\<^sub>p \<psi>  \<rbrakk>\<^sub>p = \<lbrakk>\<phi>\<rbrakk>\<^sub>p \<or>\<sqdot> \<lbrakk>\<psi>\<rbrakk>\<^sub>p\<close>
| \<open>\<lbrakk> \<phi> and\<^sub>p \<psi> \<rbrakk>\<^sub>p = \<lbrakk>\<phi>\<rbrakk>\<^sub>p \<and>\<sqdot> \<lbrakk>\<psi>\<rbrakk>\<^sub>p\<close>

definition false_p (\<open>false\<^sub>p\<close>) where
false_p_def [simp]: \<open>false\<^sub>p = not\<^sub>p true\<^sub>p\<close>

definition implies_p :: \<open>'a plogic \<Rightarrow> 'a plogic \<Rightarrow> 'a plogic\<close> (\<open>_ implies\<^sub>p _\<close> [81,81] 80)  where
implies_p_def[simp]: \<open>\<phi> implies\<^sub>p \<psi> = (not\<^sub>p \<phi> or\<^sub>p \<psi>)\<close>

subsection \<open>Propositional logic lemmas\<close>

lemma AiF_cases:  
  assumes \<open>A T = B T\<close> and \<open>A F = B F\<close>
  shows \<open>A = B\<close>
proof (rule ext)
  fix x show \<open>A x = B x\<close> by (cases \<open>x\<close>; simp add: assms) 
qed

lemma or_and_negation: \<open>\<lbrakk> \<phi> or\<^sub>p \<psi> \<rbrakk>\<^sub>p = \<lbrakk> not\<^sub>p ((not\<^sub>p \<phi>) and\<^sub>p (not\<^sub>p \<psi>)) \<rbrakk>\<^sub>p\<close>
  by (rule AiF_cases; simp)

lemma and_or_negation: \<open>\<lbrakk> \<phi> and\<^sub>p \<psi>\<rbrakk>\<^sub>p = \<lbrakk> not\<^sub>p ((not\<^sub>p \<phi>) or\<^sub>p (not\<^sub>p \<psi>)) \<rbrakk>\<^sub>p\<close>
  by (rule AiF_cases; simp)

lemma de_morgan_1: \<open>\<lbrakk> not\<^sub>p (\<phi> and\<^sub>p \<psi>) \<rbrakk>\<^sub>p = \<lbrakk> (not\<^sub>p \<phi>) or\<^sub>p (not\<^sub>p \<psi>) \<rbrakk>\<^sub>p\<close>
  by (rule AiF_cases; simp)

lemma de_morgan_2: \<open>\<lbrakk> not\<^sub>p (\<phi> or\<^sub>p \<psi>)  \<rbrakk>\<^sub>p = \<lbrakk> (not\<^sub>p \<phi>) and\<^sub>p (not\<^sub>p \<psi>) \<rbrakk>\<^sub>p\<close>
  by (rule AiF_cases; simp)

subsection \<open>Propositional logic equivalence\<close>

fun plogic_semantics' :: \<open>'a state \<Rightarrow> 'a plogic \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>p\<close> 60) where
  \<open>\<Gamma> \<Turnstile>\<^sub>p true\<^sub>p = True\<close>
| \<open>\<Gamma> \<Turnstile>\<^sub>p not\<^sub>p \<phi> = (\<not> \<Gamma> \<Turnstile>\<^sub>p \<phi>)\<close>
| \<open>\<Gamma> \<Turnstile>\<^sub>p prop\<^sub>p(a) = (a \<in> L \<Gamma>)\<close>
| \<open>\<Gamma> \<Turnstile>\<^sub>p \<phi> or\<^sub>p \<psi> = (\<Gamma> \<Turnstile>\<^sub>p \<phi> \<or> \<Gamma> \<Turnstile>\<^sub>p \<psi>)\<close>
| \<open>\<Gamma> \<Turnstile>\<^sub>p \<phi> and\<^sub>p \<psi> = (\<Gamma> \<Turnstile>\<^sub>p \<phi> \<and> \<Gamma> \<Turnstile>\<^sub>p \<psi>)\<close>

lemma plogic_equivalence:
  shows \<open>(  \<Gamma>  \<Turnstile>\<^sub>p \<phi> \<longleftrightarrow> \<Gamma> \<in> \<lbrakk>\<phi>\<rbrakk>\<^sub>p T)\<close>
  and   \<open>(\<not> \<Gamma>  \<Turnstile>\<^sub>p \<phi> \<longleftrightarrow> \<Gamma> \<in> \<lbrakk>\<phi>\<rbrakk>\<^sub>p F)\<close>
proof (induct \<open>\<phi>\<close>)
qed (auto)

end