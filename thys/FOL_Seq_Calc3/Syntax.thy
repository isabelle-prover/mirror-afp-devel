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

subsubsection \<open>Substitution\<close>

primrec add_env :: \<open>'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a\<close> (infix \<open>\<Zsemi>\<close> 0) where
  \<open>(t \<Zsemi> s) 0 = t\<close>
| \<open>(t \<Zsemi> s) (Suc n) = s n\<close>

primrec lift_tm :: \<open>tm \<Rightarrow> tm\<close> where
  \<open>lift_tm (\<^bold>#n) = \<^bold>#(n+1)\<close>
| \<open>lift_tm (\<^bold>\<dagger>f ts) = \<^bold>\<dagger>f (map lift_tm ts)\<close>

primrec sub_tm :: \<open>(nat \<Rightarrow> tm) \<Rightarrow> tm \<Rightarrow> tm\<close> where
  \<open>sub_tm s (\<^bold>#n) = s n\<close>
| \<open>sub_tm s (\<^bold>\<dagger>f ts) = \<^bold>\<dagger>f (map (sub_tm s) ts)\<close>

primrec sub_fm :: \<open>(nat \<Rightarrow> tm) \<Rightarrow> fm \<Rightarrow> fm\<close> where
  \<open>sub_fm _ \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>sub_fm s (\<^bold>\<ddagger>P ts) = \<^bold>\<ddagger>P (map (sub_tm s) ts)\<close>
| \<open>sub_fm s (p \<^bold>\<longrightarrow> q) = sub_fm s p \<^bold>\<longrightarrow> sub_fm s q\<close>
| \<open>sub_fm s (\<^bold>\<forall>p) = \<^bold>\<forall>(sub_fm (\<^bold>#0 \<Zsemi> \<lambda>n. lift_tm (s n)) p)\<close>

abbreviation inst_single :: \<open>tm \<Rightarrow> fm \<Rightarrow> fm\<close> (\<open>\<langle>_\<rangle>\<close>) where
  \<open>\<langle>t\<rangle> \<equiv> sub_fm (t \<Zsemi> \<^bold>#)\<close>

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

datatype rule =
  Idle | Axiom nat \<open>tm list\<close> | FlsL | FlsR | ImpL fm fm | ImpR fm fm | UniL tm fm | UniR fm

end
