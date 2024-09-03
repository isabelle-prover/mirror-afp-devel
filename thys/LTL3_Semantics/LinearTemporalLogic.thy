theory LinearTemporalLogic
imports Traces AnswerIndexedFamilies Main
begin

chapter \<open>Linear-time Temporal Logic\<close>

datatype (atoms_ltl: 'a) ltl =
      True_ltl                             (\<open>true\<^sub>l\<close>)
    | Not_ltl \<open>'a ltl\<close>                     (\<open>not\<^sub>l _\<close> [85] 85)
    | Prop_ltl \<open>'a\<close>                          (\<open>prop\<^sub>l'(_')\<close>)
    | Or_ltl \<open>'a ltl\<close> \<open>'a ltl\<close>             (\<open>_ or\<^sub>l _\<close> [82,82] 81)
    | And_ltl \<open>'a ltl\<close> \<open>'a ltl\<close>            (\<open>_ and\<^sub>l _  \<close> [82,82] 81)
    | Next_ltl \<open>'a ltl\<close>                    (\<open>X\<^sub>l _\<close> [88] 87)
    | Until_ltl \<open>'a ltl\<close> \<open>'a ltl\<close>          (\<open>_ U\<^sub>l  _\<close> [84,84] 83)

fun lsatisfying_AiF :: \<open>'a \<Rightarrow> 'a state infinite_trace AiF\<close> (\<open>lsat\<bullet>\<close>) where
\<open>lsat\<bullet> x T = {t. x \<in> L (t 0)}\<close> |
\<open>lsat\<bullet> x F = {t. x \<notin> L (t 0)}\<close>

fun x_operator :: \<open>'a infinite_trace AiF \<Rightarrow> 'a infinite_trace AiF\<close> (\<open>X\<sqdot>\<close>) where
\<open>X\<sqdot> t T = {x | x. itdrop 1 x \<in> (t T)}\<close>|
\<open>X\<sqdot> t F = {x | x. itdrop 1 x \<in> (t F)}\<close>

fun u_operator :: \<open>'a infinite_trace AiF \<Rightarrow> 'a infinite_trace AiF \<Rightarrow> 'a infinite_trace AiF\<close> (infix \<open>U\<sqdot>\<close> 61) where
\<open>(a U\<sqdot> b) T = {x | x. \<exists>k. (\<forall>i<k. itdrop i x \<in> (a T)) \<and> itdrop k x \<in> (b T)}\<close>|
\<open>(a U\<sqdot> b) F = {x | x. \<forall>k. (\<exists>i<k. itdrop i x \<in> (a F)) \<or> itdrop k x \<in> (b F)}\<close>

fun ltl_semantics :: \<open>'a ltl \<Rightarrow> 'a state infinite_trace AiF\<close> (\<open>\<lbrakk>_\<rbrakk>\<^sub>l\<close>) where
\<open>\<lbrakk> true\<^sub>l    \<rbrakk>\<^sub>l = T\<bullet>\<close>|
\<open>\<lbrakk> not\<^sub>l \<phi>   \<rbrakk>\<^sub>l = \<not>\<sqdot> \<lbrakk> \<phi> \<rbrakk>\<^sub>l\<close>|
\<open>\<lbrakk> prop\<^sub>l(a) \<rbrakk>\<^sub>l = lsat\<bullet> a\<close>|
\<open>\<lbrakk> \<phi> or\<^sub>l \<psi>  \<rbrakk>\<^sub>l = \<lbrakk> \<phi> \<rbrakk>\<^sub>l \<or>\<sqdot> \<lbrakk> \<psi> \<rbrakk>\<^sub>l\<close>|
\<open>\<lbrakk> \<phi> and\<^sub>l \<psi> \<rbrakk>\<^sub>l = \<lbrakk> \<phi> \<rbrakk>\<^sub>l \<and>\<sqdot> \<lbrakk> \<psi> \<rbrakk>\<^sub>l\<close>|
\<open>\<lbrakk> X\<^sub>l \<phi>     \<rbrakk>\<^sub>l = X\<sqdot> \<lbrakk> \<phi> \<rbrakk>\<^sub>l\<close>|
\<open>\<lbrakk> \<phi> U\<^sub>l \<psi>   \<rbrakk>\<^sub>l = \<lbrakk> \<phi> \<rbrakk>\<^sub>l U\<sqdot> \<lbrakk> \<psi> \<rbrakk>\<^sub>l\<close>

lemma excluded_middle_ltl' : 
  shows \<open>(\<Gamma> \<notin> \<lbrakk>\<phi>\<rbrakk>\<^sub>l T) \<longleftrightarrow> (\<Gamma> \<in> \<lbrakk>\<phi>\<rbrakk>\<^sub>l F)\<close>
  and   \<open>(\<Gamma> \<notin> \<lbrakk>\<phi>\<rbrakk>\<^sub>l F) \<longleftrightarrow> (\<Gamma> \<in> \<lbrakk>\<phi>\<rbrakk>\<^sub>l T)\<close>
proof (induct \<open>\<phi>\<close> arbitrary: \<open>\<Gamma>\<close>)
qed auto

lemma excluded_middle_ltl: \<open>\<Gamma> \<in> \<lbrakk>\<phi>\<rbrakk>\<^sub>l T \<or> \<Gamma> \<in> \<lbrakk>\<phi>\<rbrakk>\<^sub>l F\<close>
  using excluded_middle_ltl' by blast

definition false_ltl (\<open>false\<^sub>l\<close>) where
  false_ltl_def[simp]: \<open>false\<^sub>l = not\<^sub>l true\<^sub>l\<close>

definition implies_ltl :: \<open>'a ltl \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl\<close> (infix \<open>implies\<^sub>l\<close> 80)  where
  implies_ltl_def[simp]: \<open>\<phi> implies\<^sub>l \<psi> = (not\<^sub>l \<phi> or\<^sub>l \<psi>)\<close>

definition final_ltl :: \<open>'a ltl \<Rightarrow> 'a ltl\<close> (\<open>F\<^sub>l _\<close>) where
  final_ltl_def[simp]: \<open>(F\<^sub>l \<phi>) = (true\<^sub>l U\<^sub>l \<phi>)\<close>

definition global_ltl :: \<open>'a ltl \<Rightarrow> 'a ltl\<close> (\<open>G\<^sub>l _\<close>) where
  global_ltl_def[simp]: \<open>(G\<^sub>l \<phi>) = (not\<^sub>l F\<^sub>l (not\<^sub>l \<phi>))\<close>

section \<open>Linear temporal logic equivalence\<close>

fun ltl_semantics' :: \<open>'a state infinite_trace \<Rightarrow> 'a ltl \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>l\<close> 60) where
  \<open>\<Gamma> \<Turnstile>\<^sub>l true\<^sub>l    = True\<close>
| \<open>\<Gamma> \<Turnstile>\<^sub>l not\<^sub>l \<phi>   = (\<not> \<Gamma> \<Turnstile>\<^sub>l \<phi>)\<close>
| \<open>\<Gamma> \<Turnstile>\<^sub>l prop\<^sub>l(a) = (a \<in> L (\<Gamma> 0))\<close>
| \<open>\<Gamma> \<Turnstile>\<^sub>l \<phi> or\<^sub>l \<psi>  = (\<Gamma> \<Turnstile>\<^sub>l \<phi> \<or> \<Gamma> \<Turnstile>\<^sub>l \<psi>)\<close>
| \<open>\<Gamma> \<Turnstile>\<^sub>l \<phi> and\<^sub>l \<psi> = (\<Gamma> \<Turnstile>\<^sub>l \<phi> \<and> \<Gamma> \<Turnstile>\<^sub>l \<psi>)\<close>
| \<open>\<Gamma> \<Turnstile>\<^sub>l (X\<^sub>l \<phi>)   = itdrop 1 \<Gamma> \<Turnstile>\<^sub>l \<phi>\<close>
| \<open>\<Gamma> \<Turnstile>\<^sub>l (\<phi> U\<^sub>l \<psi>) = (\<exists>k. (\<forall>i<k. itdrop i \<Gamma> \<Turnstile>\<^sub>l \<phi>) \<and> itdrop k \<Gamma> \<Turnstile>\<^sub>l \<psi>)\<close>


section \<open>Linear temporal logic lemmas\<close>
lemma \<open>\<lbrakk> F\<^sub>l (F\<^sub>l \<phi>) \<rbrakk>\<^sub>l = \<lbrakk> F\<^sub>l \<phi> \<rbrakk>\<^sub>l\<close>
proof (rule AiF_cases)
  show \<open>\<lbrakk>F\<^sub>l F\<^sub>l \<phi>\<rbrakk>\<^sub>l T = \<lbrakk>F\<^sub>l \<phi>\<rbrakk>\<^sub>l T\<close>
    apply (clarsimp intro!: set_eqI, rule)
     apply auto[1]
    by (clarsimp, metis add_0)
next
  show \<open>\<lbrakk>F\<^sub>l F\<^sub>l \<phi>\<rbrakk>\<^sub>l F = \<lbrakk>F\<^sub>l \<phi>\<rbrakk>\<^sub>l F\<close>
    apply (clarsimp intro!: set_eqI, rule)
     apply (clarsimp, metis add_0)
    by simp
qed

lemma ltl_equivalence: 
  shows \<open>   \<Gamma> \<Turnstile>\<^sub>l \<phi>  = (\<Gamma> \<in> \<lbrakk> \<phi> \<rbrakk>\<^sub>l T)\<close>
  and   \<open>(\<not> \<Gamma> \<Turnstile>\<^sub>l \<phi>) = (\<Gamma> \<in> \<lbrakk> \<phi> \<rbrakk>\<^sub>l F)\<close>
proof(induct \<open>\<phi>\<close> arbitrary: \<open>\<Gamma>\<close>)
qed auto

end