section \<open>Semantics\<close>

theory Semantics imports Syntax begin

subsection \<open>Definition\<close>

type_synonym 'a var_denot = \<open>nat \<Rightarrow> 'a\<close>
type_synonym 'a fun_denot = \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a\<close>
type_synonym 'a pre_denot = \<open>nat \<Rightarrow> 'a list \<Rightarrow> bool\<close>

primrec semantics_tm :: \<open>'a var_denot \<Rightarrow> 'a fun_denot \<Rightarrow> tm \<Rightarrow> 'a\<close> (\<open>\<lparr>_, _\<rparr>\<close>) where
  \<open>\<lparr>E, F\<rparr> (\<^bold>#n) = E n\<close>
| \<open>\<lparr>E, F\<rparr> (\<^bold>\<dagger>f ts) = F f (map \<lparr>E, F\<rparr> ts)\<close>

primrec semantics_fm :: \<open>'a var_denot \<Rightarrow> 'a fun_denot \<Rightarrow> 'a pre_denot \<Rightarrow> fm \<Rightarrow> bool\<close>
  (\<open>\<lbrakk>_, _, _\<rbrakk>\<close>) where
  \<open>\<lbrakk>_, _, _\<rbrakk> \<^bold>\<bottom> = False\<close>
| \<open>\<lbrakk>E, F, G\<rbrakk> (\<^bold>\<ddagger>P ts) = G P (map \<lparr>E, F\<rparr> ts)\<close>
| \<open>\<lbrakk>E, F, G\<rbrakk> (p \<^bold>\<longrightarrow> q) = (\<lbrakk>E, F, G\<rbrakk> p \<longrightarrow> \<lbrakk>E, F, G\<rbrakk> q)\<close>
| \<open>\<lbrakk>E, F, G\<rbrakk> (\<^bold>\<forall>p) = (\<forall>x. \<lbrakk>x \<Zsemi> E, F, G\<rbrakk> p)\<close>

fun sc :: \<open>('a var_denot \<times> 'a fun_denot \<times> 'a pre_denot) \<Rightarrow> sequent \<Rightarrow> bool\<close> where
  \<open>sc (E, F, G) (A, B) = ((\<forall>p [\<in>] A. \<lbrakk>E, F, G\<rbrakk> p) \<longrightarrow> (\<exists>q [\<in>] B. \<lbrakk>E, F, G\<rbrakk> q))\<close>

subsection \<open>Substitution\<close>

lemma add_env_semantics [simp]: \<open>\<lparr>E, F\<rparr> ((t \<Zsemi> s) n) = (\<lparr>E, F\<rparr> t \<Zsemi> \<lambda>m. \<lparr>E, F\<rparr> (s m)) n\<close>
  by (induct n) simp_all

lemma lift_lemma [simp]: \<open>\<lparr>x \<Zsemi> E, F\<rparr> (lift_tm t) = \<lparr>E, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma sub_tm_semantics [simp]: \<open>\<lparr>E, F\<rparr> (sub_tm s t) = \<lparr>\<lambda>n. \<lparr>E, F\<rparr> (s n), F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma sub_fm_semantics [simp]: \<open>\<lbrakk>E, F, G\<rbrakk> (sub_fm s p) = \<lbrakk>\<lambda>n. \<lparr>E, F\<rparr> (s n), F, G\<rbrakk> p\<close>
  by (induct p arbitrary: E s) (auto cong: map_cong)

subsection \<open>Variables\<close>

lemma upd_vars_tm [simp]: \<open>n [\<notin>] vars_tm t \<Longrightarrow> \<lparr>E(n := x), F\<rparr> t = \<lparr>E, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma add_upd_commute [simp]: \<open>(y \<Zsemi> E(n := x)) m = ((y \<Zsemi> E)(Suc n := x)) m\<close>
  by (induct m) simp_all

lemma upd_vars_fm [simp]: \<open>max_list (vars_fm p) < n \<Longrightarrow> \<lbrakk>E(n := x), F, G\<rbrakk> p = \<lbrakk>E, F, G\<rbrakk> p\<close>
proof (induct p arbitrary: E n)
  case (Pre P ts)
  moreover have \<open>max_list (concat (map vars_tm ts)) < n\<close>
    using Pre.prems max_list_concat by simp
  then have \<open>n [\<notin>] concat (map vars_tm ts)\<close>
    using max_list_in by blast
  then have \<open>\<forall>t [\<in>] ts. n [\<notin>] vars_tm t\<close>
    by simp
  ultimately show ?case
    using upd_vars_tm by (metis list.map_cong semantics_fm.simps(2))
next
  case (Uni p)
  have \<open>?case = ((\<forall>y. \<lbrakk>\<lambda>m. (y \<Zsemi> E(n := x)) m, F, G\<rbrakk> p) = (\<forall>y. \<lbrakk>y \<Zsemi> E, F, G\<rbrakk> p))\<close>
    by (simp add: fun_upd_def)
  then show ?case
    using Uni by simp
qed (auto simp: max_list_append cong: map_cong)

end
