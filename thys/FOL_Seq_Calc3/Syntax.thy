section \<open>Syntax\<close>

theory Syntax imports List_Syntax begin

subsection \<open>Terms and Formulas\<close>

datatype tm
  = Var nat (\<open>\<^bold>#\<close>)
  | Fun nat \<open>tm list\<close> (\<open>\<^bold>\<dagger>\<close>)

datatype fm
  = Falsity (\<open>\<^bold>\<bottom>\<close>)
  | Pre nat \<open>tm list\<close> (\<open>\<^bold>\<ddagger>\<close>)
  | Imp fm fm (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | Uni fm (\<open>\<^bold>\<forall>\<close>)

type_synonym sequent = \<open>fm list \<times> fm list\<close>

subsubsection \<open>Instantiation\<close>

primrec lift_tm :: \<open>tm \<Rightarrow> tm\<close> (\<open>\<^bold>\<up>\<close>) where
  \<open>\<^bold>\<up>(\<^bold>#n) = \<^bold>#(n+1)\<close>
| \<open>\<^bold>\<up>(\<^bold>\<dagger>f ts) = \<^bold>\<dagger>f (map \<^bold>\<up> ts)\<close>

primrec inst_tm :: \<open>tm \<Rightarrow> tm \<Rightarrow> nat \<Rightarrow> tm\<close> (\<open>_'\<llangle>_'/_'\<rrangle>\<close> [90, 0, 0] 91) where
  \<open>(\<^bold>#n)\<llangle>s/m\<rrangle> = (if n < m then \<^bold>#n else if n = m then s else \<^bold>#(n-1))\<close>
| \<open>(\<^bold>\<dagger>f ts)\<llangle>s/m\<rrangle> = \<^bold>\<dagger>f (map (\<lambda>t. t\<llangle>s/m\<rrangle>) ts)\<close>

primrec inst_fm :: \<open>fm \<Rightarrow> tm \<Rightarrow> nat \<Rightarrow> fm\<close> (\<open>_'\<langle>_'/_'\<rangle>\<close> [90, 0, 0] 91) where
  \<open>\<^bold>\<bottom>\<langle>_/_\<rangle> = \<^bold>\<bottom>\<close>
| \<open>(\<^bold>\<ddagger>P ts)\<langle>s/m\<rangle> = \<^bold>\<ddagger>P (map (\<lambda>t. t\<llangle>s/m\<rrangle>) ts)\<close>
| \<open>(p \<^bold>\<longrightarrow> q)\<langle>s/m\<rangle> = (p\<langle>s/m\<rangle> \<^bold>\<longrightarrow> q\<langle>s/m\<rangle>)\<close>
| \<open>(\<^bold>\<forall>p)\<langle>s/m\<rangle> = \<^bold>\<forall>(p\<langle>\<^bold>\<up>s/m+1\<rangle>)\<close>

subsubsection \<open>Variables\<close>

primrec vars_tm :: \<open>tm \<Rightarrow> nat list\<close> where
  \<open>vars_tm (\<^bold>#n) = [n]\<close>
| \<open>vars_tm (\<^bold>\<dagger>_ ts) = concat (map vars_tm ts)\<close>

primrec vars_fm :: \<open>fm \<Rightarrow> nat list\<close> where
  \<open>vars_fm \<^bold>\<bottom> = []\<close>
| \<open>vars_fm (\<^bold>\<ddagger>_ ts) = concat (map vars_tm ts)\<close>
| \<open>vars_fm (p \<^bold>\<longrightarrow> q) = vars_fm p @ vars_fm q\<close>
| \<open>vars_fm (\<^bold>\<forall>p) = vars_fm p\<close>

primrec max_list :: \<open>nat list \<Rightarrow> nat\<close> where
  \<open>max_list [] = 0\<close>
| \<open>max_list (x # xs) = max x (max_list xs)\<close>

definition max_var_fm :: \<open>fm \<Rightarrow> nat\<close> where
  \<open>max_var_fm p = max_list (vars_fm p)\<close>

lemma max_list_append: \<open>max_list (xs @ ys) = max (max_list xs) (max_list ys)\<close>
  by (induct xs) auto

lemma max_list_concat: \<open>xs [\<in>] xss \<Longrightarrow> max_list xs \<le> max_list (concat xss)\<close>
  by (induct xss) (auto simp: max_list_append)

lemma max_list_in: \<open>max_list xs < n \<Longrightarrow> n [\<notin>] xs\<close>
  by (induct xs) auto

definition vars_fms :: \<open>fm list \<Rightarrow> nat list\<close> where
  \<open>vars_fms A \<equiv> concat (map vars_fm A)\<close>

lemma vars_fms_member: \<open>p [\<in>] A \<Longrightarrow> vars_fm p [\<subseteq>] vars_fms A\<close>
  unfolding vars_fms_def by (induct A) auto

lemma max_list_mono: \<open>A [\<subseteq>] B \<Longrightarrow> max_list A \<le> max_list B\<close>
  by (induct A) (simp, metis linorder_not_le list.set_intros(1) max.absorb2 max.absorb3
      max_list.simps(2) max_list_in set_subset_Cons subset_code(1))

lemma max_list_vars_fms:
  assumes \<open>max_list (vars_fms A) \<le> n\<close> \<open>p [\<in>] A\<close>
  shows \<open>max_list (vars_fm p) \<le> n\<close>
  using assms max_list_mono vars_fms_member by (meson dual_order.trans)

definition fresh :: \<open>fm list \<Rightarrow> nat\<close> where
  \<open>fresh A \<equiv> Suc (max_list (vars_fms A))\<close>

subsection \<open>Rules\<close>

datatype rule
  = Idle
  | Axiom nat \<open>tm list\<close>
  | FlsL
  | FlsR
  | ImpL fm fm
  | ImpR fm fm
  | UniL tm fm
  | UniR fm

end
