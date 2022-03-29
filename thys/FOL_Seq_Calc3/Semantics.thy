section \<open>Semantics\<close>

theory Semantics imports Syntax begin

subsection \<open>Shift\<close>

definition shift :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a\<close>
  (\<open>_\<langle>_:_\<rangle>\<close> [90, 0, 0] 91) where
  \<open>E\<langle>n:x\<rangle> = (\<lambda>m. if m < n then E m else if m = n then x else E (m-1))\<close>

lemma shift_eq [simp]: \<open>n = m \<Longrightarrow> (E\<langle>n:x\<rangle>) m = x\<close>
  by (simp add: shift_def)

lemma shift_gt [simp]: \<open>m < n \<Longrightarrow> (E\<langle>n:x\<rangle>) m = E m\<close>
  by (simp add: shift_def)

lemma shift_lt [simp]: \<open>n < m \<Longrightarrow> (E\<langle>n:x\<rangle>) m = E (m-1)\<close>
  by (simp add: shift_def)

lemma shift_commute [simp]: \<open>E\<langle>n:y\<rangle>\<langle>0:x\<rangle> = E\<langle>0:x\<rangle>\<langle>n+1:y\<rangle>\<close>
proof
  fix m
  show \<open>(E\<langle>n:y\<rangle>\<langle>0:x\<rangle>) m = (E\<langle>0:x\<rangle>\<langle>n+1:y\<rangle>) m\<close>
    unfolding shift_def by (cases m) simp_all
qed

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
| \<open>\<lbrakk>E, F, G\<rbrakk> (\<^bold>\<forall>p) = (\<forall>x. \<lbrakk>E\<langle>0:x\<rangle>, F, G\<rbrakk> p)\<close>

fun sc :: \<open>('a var_denot \<times> 'a fun_denot \<times> 'a pre_denot) \<Rightarrow> sequent \<Rightarrow> bool\<close> where
  \<open>sc (E, F, G) (A, B) = ((\<forall>p [\<in>] A. \<lbrakk>E, F, G\<rbrakk> p) \<longrightarrow> (\<exists>q [\<in>] B. \<lbrakk>E, F, G\<rbrakk> q))\<close>

subsection \<open>Instantiation\<close>

lemma lift_lemma [simp]: \<open>\<lparr>E\<langle>0:x\<rangle>, F\<rparr> (\<^bold>\<up>t) = \<lparr>E, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma inst_tm_semantics [simp]: \<open>\<lparr>E, F\<rparr> (t\<llangle>s/m\<rrangle>) = \<lparr>E\<langle>m:\<lparr>E, F\<rparr> s\<rangle>, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma inst_fm_semantics [simp]: \<open>\<lbrakk>E, F, G\<rbrakk> (p\<langle>t/m\<rangle>) = \<lbrakk>E\<langle>m:\<lparr>E, F\<rparr> t\<rangle>, F, G\<rbrakk> p\<close>
  by (induct p arbitrary: E m t) (auto cong: map_cong)

subsection \<open>Variables\<close>

lemma upd_vars_tm [simp]: \<open>n [\<notin>] vars_tm t \<Longrightarrow> \<lparr>E(n := x), F\<rparr> t = \<lparr>E, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma shift_upd_commute: \<open>m \<le> n \<Longrightarrow> (E(n := x)\<langle>m:y\<rangle>) = ((E\<langle>m:y\<rangle>)(Suc n := x))\<close>
  unfolding shift_def by fastforce

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
  have \<open>?case = ((\<forall>y. \<lbrakk>E(n := x)\<langle>0:y\<rangle>, F, G\<rbrakk> p) = (\<forall>y. \<lbrakk>E\<langle>0:y\<rangle>, F, G\<rbrakk> p))\<close>
    by (simp add: fun_upd_def)
  also have \<open>\<dots> = ((\<forall>y. \<lbrakk>(E\<langle>0:y\<rangle>)(n + 1 := x), F, G\<rbrakk> p) = (\<forall>y. \<lbrakk>E\<langle>0:y\<rangle>, F, G\<rbrakk> p))\<close>
    by (simp add: shift_upd_commute)
  finally show ?case
    using Uni by fastforce
qed (auto simp: max_list_append cong: map_cong)

end
