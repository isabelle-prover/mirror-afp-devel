(*
  File:      FOL_Axiomatic_Variant.thy
  Author:    Asta Halkjær From

  This work is a formalization of the soundness and completeness of an axiomatic system
  for first-order logic. The proof system is based on System Q1 by Smullyan
  and the completeness proof follows his textbook "First-Order Logic" (Springer-Verlag 1968).
  The completeness proof is in the Henkin style where a consistent set
  is extended to a maximal consistent set using Lindenbaum's construction
  and Henkin witnesses are added during the construction to ensure saturation as well.
  The resulting set is a Hintikka set which, by the model existence theorem, is satisfiable
  in the Herbrand universe.

  This variant uses free variables as Henkin witnesses. This gives completeness for syntax
  with only finitely many available constants.
*)

theory FOL_Axiomatic_Variant imports "HOL-Library.Countable" begin

section \<open>Syntax\<close>

datatype 'f tm
  = Var nat (\<open>\<^bold>#\<close>)
  | Fun 'f \<open>'f tm list\<close> (\<open>\<^bold>\<dagger>\<close>)

datatype ('f, 'p) fm
  = Falsity (\<open>\<^bold>\<bottom>\<close>)
  | Pre 'p \<open>'f tm list\<close> (\<open>\<^bold>\<ddagger>\<close>)
  | Imp \<open>('f, 'p) fm\<close> \<open>('f, 'p) fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | Uni \<open>('f, 'p) fm\<close> (\<open>\<^bold>\<forall>\<close>)

abbreviation Neg (\<open>\<^bold>\<not> _\<close> [70] 70) where \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

term \<open>\<^bold>\<forall>(\<^bold>\<bottom> \<^bold>\<longrightarrow> \<^bold>\<ddagger>''P'' [\<^bold>\<dagger>''f'' [\<^bold>#0]])\<close>

section \<open>Semantics\<close>

definition shift :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a\<close>
  (\<open>_\<langle>_:_\<rangle>\<close> [90, 0, 0] 91) where
  \<open>E\<langle>n:x\<rangle> = (\<lambda>m. if m < n then E m else if m = n then x else E (m-1))\<close>

primrec semantics_tm (\<open>\<lparr>_, _\<rparr>\<close>) where
  \<open>\<lparr>E, F\<rparr> (\<^bold>#n) = E n\<close>
| \<open>\<lparr>E, F\<rparr> (\<^bold>\<dagger>f ts) = F f (map \<lparr>E, F\<rparr> ts)\<close>

primrec semantics_fm (\<open>\<lbrakk>_, _, _\<rbrakk>\<close>) where
  \<open>\<lbrakk>_, _, _\<rbrakk> \<^bold>\<bottom> = False\<close>
| \<open>\<lbrakk>E, F, G\<rbrakk> (\<^bold>\<ddagger>P ts) = G P (map \<lparr>E, F\<rparr> ts)\<close>
| \<open>\<lbrakk>E, F, G\<rbrakk> (p \<^bold>\<longrightarrow> q) = (\<lbrakk>E, F, G\<rbrakk> p \<longrightarrow> \<lbrakk>E, F, G\<rbrakk> q)\<close>
| \<open>\<lbrakk>E, F, G\<rbrakk> (\<^bold>\<forall>p) = (\<forall>x. \<lbrakk>E\<langle>0:x\<rangle>, F, G\<rbrakk> p)\<close>

proposition \<open>\<lbrakk>E, F, G\<rbrakk> (\<^bold>\<forall>(\<^bold>\<ddagger>P [\<^bold># 0]) \<^bold>\<longrightarrow> \<^bold>\<ddagger>P [\<^bold>\<dagger> a []])\<close>
  by (simp add: shift_def)

section \<open>Operations\<close>

subsection \<open>Shift\<close>

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

subsection \<open>Variables\<close>

primrec vars_tm where
  \<open>vars_tm (\<^bold>#n) = [n]\<close>
| \<open>vars_tm (\<^bold>\<dagger>_ ts) = concat (map vars_tm ts)\<close>

primrec vars_fm where
  \<open>vars_fm \<^bold>\<bottom> = []\<close>
| \<open>vars_fm (\<^bold>\<ddagger>_ ts) = concat (map vars_tm ts)\<close>
| \<open>vars_fm (p \<^bold>\<longrightarrow> q) = vars_fm p @ vars_fm q\<close>
| \<open>vars_fm (\<^bold>\<forall>p) = vars_fm p\<close>

abbreviation \<open>vars S \<equiv> \<Union>p \<in> S. set (vars_fm p)\<close>

primrec max_list :: \<open>nat list \<Rightarrow> nat\<close> where
  \<open>max_list [] = 0\<close>
| \<open>max_list (x # xs) = max x (max_list xs)\<close>

lemma max_list_append: \<open>max_list (xs @ ys) = max (max_list xs) (max_list ys)\<close>
  by (induct xs) auto

lemma upd_vars_tm [simp]: \<open>n \<notin> set (vars_tm t) \<Longrightarrow> \<lparr>E(n := x), F\<rparr> t = \<lparr>E, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma shift_upd_commute: \<open>m \<le> n \<Longrightarrow> (E(n := x)\<langle>m:y\<rangle>) = ((E\<langle>m:y\<rangle>)(n + 1 := x))\<close>
  unfolding shift_def by fastforce

lemma max_list_concat: \<open>xs \<in> set xss \<Longrightarrow> max_list xs \<le> max_list (concat xss)\<close>
  by (induct xss) (auto simp: max_list_append)

lemma max_list_in: \<open>max_list xs < n \<Longrightarrow> n \<notin> set xs\<close>
  by (induct xs) auto

lemma upd_vars_fm [simp]: \<open>max_list (vars_fm p) < n \<Longrightarrow> \<lbrakk>E(n := x), F, G\<rbrakk> p = \<lbrakk>E, F, G\<rbrakk> p\<close>
proof (induct p arbitrary: E n)
  case (Pre P ts)
  moreover have \<open>max_list (concat (map vars_tm ts)) < n\<close>
    using Pre.prems max_list_concat by simp
  then have \<open>n \<notin> set (concat (map vars_tm ts))\<close>
    using max_list_in by blast
  then have \<open>\<forall>t \<in> set ts. n \<notin> set (vars_tm t)\<close>
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

abbreviation \<open>max_var p \<equiv> max_list (vars_fm p)\<close>

subsection \<open>Instantiation\<close>

primrec lift_tm (\<open>\<^bold>\<up>\<close>) where
  \<open>\<^bold>\<up>(\<^bold>#n) = \<^bold>#(n+1)\<close>
| \<open>\<^bold>\<up>(\<^bold>\<dagger>f ts) = \<^bold>\<dagger>f (map \<^bold>\<up> ts)\<close>

primrec inst_tm (\<open>_'\<llangle>_'/_'\<rrangle>\<close> [90, 0, 0] 91) where
  \<open>(\<^bold>#n)\<llangle>s/m\<rrangle> = (if n < m then \<^bold>#n else if n = m then s else \<^bold>#(n-1))\<close>
| \<open>(\<^bold>\<dagger>f ts)\<llangle>s/m\<rrangle> = \<^bold>\<dagger>f (map (\<lambda>t. t\<llangle>s/m\<rrangle>) ts)\<close>

primrec inst_fm (\<open>_'\<langle>_'/_'\<rangle>\<close> [90, 0, 0] 91) where
  \<open>\<^bold>\<bottom>\<langle>_/_\<rangle> = \<^bold>\<bottom>\<close>
| \<open>(\<^bold>\<ddagger>P ts)\<langle>s/m\<rangle> = \<^bold>\<ddagger>P (map (\<lambda>t. t\<llangle>s/m\<rrangle>) ts)\<close>
| \<open>(p \<^bold>\<longrightarrow> q)\<langle>s/m\<rangle> = (p\<langle>s/m\<rangle> \<^bold>\<longrightarrow> q\<langle>s/m\<rangle>)\<close>
| \<open>(\<^bold>\<forall>p)\<langle>s/m\<rangle> = \<^bold>\<forall>(p\<langle>\<^bold>\<up>s/m+1\<rangle>)\<close>

lemma lift_lemma [simp]: \<open>\<lparr>E\<langle>0:x\<rangle>, F\<rparr> (\<^bold>\<up>t) = \<lparr>E, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma inst_tm_semantics [simp]: \<open>\<lparr>E, F\<rparr> (t\<llangle>s/m\<rrangle>) = \<lparr>E\<langle>m:\<lparr>E, F\<rparr> s\<rangle>, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma inst_fm_semantics [simp]: \<open>\<lbrakk>E, F, G\<rbrakk> (p\<langle>t/m\<rangle>) = \<lbrakk>E\<langle>m:\<lparr>E, F\<rparr> t\<rangle>, F, G\<rbrakk> p\<close>
  by (induct p arbitrary: E m t) (auto cong: map_cong)

subsection \<open>Size\<close>

text \<open>The built-in \<open>size\<close> is not invariant under substitution.\<close>

primrec size_fm where
  \<open>size_fm \<^bold>\<bottom> = 1\<close>
| \<open>size_fm (\<^bold>\<ddagger>_ _) = 1\<close>
| \<open>size_fm (p \<^bold>\<longrightarrow> q) = 1 + size_fm p + size_fm q\<close>
| \<open>size_fm (\<^bold>\<forall>p) = 1 + size_fm p\<close>

lemma size_inst_fm [simp]:
  \<open>size_fm (p\<langle>t/m\<rangle>) = size_fm p\<close>
  by (induct p arbitrary: m t) auto

section \<open>Propositional Semantics\<close>

primrec boolean where
  \<open>boolean _ _ \<^bold>\<bottom> = False\<close>
| \<open>boolean G _ (\<^bold>\<ddagger>P ts) = G P ts\<close>
| \<open>boolean G A (p \<^bold>\<longrightarrow> q) = (boolean G A p \<longrightarrow> boolean G A q)\<close>
| \<open>boolean _ A (\<^bold>\<forall>p) = A (\<^bold>\<forall>p)\<close>

abbreviation \<open>tautology p \<equiv> \<forall>G A. boolean G A p\<close>

proposition \<open>tautology (\<^bold>\<forall>(\<^bold>\<ddagger>P [\<^bold>#0]) \<^bold>\<longrightarrow> \<^bold>\<forall>(\<^bold>\<ddagger>P [\<^bold>#0]))\<close>
  by simp

lemma boolean_semantics: \<open>boolean (\<lambda>a. G a \<circ> map \<lparr>E, F\<rparr>) \<lbrakk>E, F, G\<rbrakk> = \<lbrakk>E, F, G\<rbrakk>\<close>
proof
  fix p
  show \<open>boolean (\<lambda>a. G a \<circ> map \<lparr>E, F\<rparr>) \<lbrakk>E, F, G\<rbrakk> p = \<lbrakk>E, F, G\<rbrakk> p\<close>
    by (induct p) simp_all
qed

lemma tautology: \<open>tautology p \<Longrightarrow> \<lbrakk>E, F, G\<rbrakk> p\<close>
  using boolean_semantics by metis

proposition \<open>\<exists>p. (\<forall>E F G. \<lbrakk>E, F, G\<rbrakk> p) \<and> \<not> tautology p\<close>
  by (metis boolean.simps(4) fm.simps(36) semantics_fm.simps(1,3,4))

section \<open>Calculus\<close>

text \<open>Adapted from System Q1 by Smullyan in First-Order Logic (1968)\<close>

inductive Axiomatic (\<open>\<turnstile> _\<close> [50] 50) where
  TA: \<open>tautology p \<Longrightarrow> \<turnstile> p\<close>
| IA: \<open>\<turnstile> \<^bold>\<forall>p \<^bold>\<longrightarrow> p\<langle>t/0\<rangle>\<close>
| MP: \<open>\<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> \<turnstile> p \<Longrightarrow> \<turnstile> q\<close>
| GR: \<open>\<turnstile> q \<^bold>\<longrightarrow> p\<langle>\<^bold>#n/0\<rangle> \<Longrightarrow> max_var p < n \<Longrightarrow> max_var q < n \<Longrightarrow> \<turnstile> q \<^bold>\<longrightarrow> \<^bold>\<forall>p\<close>

lemmas
  TA[simp]
  MP[trans, dest]
  GR[intro]

text \<open>We simulate assumptions on the lhs of \<open>\<turnstile>\<close> with a chain of implications on the rhs.\<close>

primrec imply (infixr \<open>\<^bold>\<leadsto>\<close> 56) where
  \<open>([] \<^bold>\<leadsto> q) = q\<close>
| \<open>(p # ps \<^bold>\<leadsto> q) = (p \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q)\<close>

abbreviation Axiomatic_assms (\<open>_ \<turnstile> _\<close> [50, 50] 50) where
  \<open>ps \<turnstile> q \<equiv> \<turnstile> ps \<^bold>\<leadsto> q\<close>

section \<open>Soundness\<close>

theorem soundness: \<open>\<turnstile> p \<Longrightarrow> \<lbrakk>E, F, G\<rbrakk> p\<close>
proof (induct p arbitrary: E F rule: Axiomatic.induct)
  case (GR q p n)
  then have \<open>\<lbrakk>E(n := x), F, G\<rbrakk> (q \<^bold>\<longrightarrow> p\<langle>\<^bold>#n/0\<rangle>)\<close> for x
    by blast
  then have \<open>\<lbrakk>E(n := x), F, G\<rbrakk> q \<longrightarrow> \<lbrakk>E(n := x), F, G\<rbrakk> (p\<langle>\<^bold>#n/0\<rangle>)\<close> for x
    by simp
  then have \<open>\<lbrakk>E, F, G\<rbrakk> q \<longrightarrow> \<lbrakk>E(n := x), F, G\<rbrakk> (p\<langle>\<^bold>#n/0\<rangle>)\<close> for x
    using GR.hyps(3-4) by simp
  then have \<open>\<lbrakk>E, F, G\<rbrakk> q \<longrightarrow> (\<forall>x. \<lbrakk>E(n := x), F, G\<rbrakk> (p\<langle>\<^bold>#n/0\<rangle>))\<close>
    by blast
  then have \<open>\<lbrakk>E, F, G\<rbrakk> q \<longrightarrow> (\<forall>x. \<lbrakk>E(n := x)\<langle>0:x\<rangle>, F, G\<rbrakk> p)\<close>
    by simp
  then have \<open>\<lbrakk>E, F, G\<rbrakk> q \<longrightarrow> (\<forall>x. \<lbrakk>(E\<langle>0:x\<rangle>)(n + 1 := x), F, G\<rbrakk> p)\<close>
    using shift_upd_commute by (metis zero_le)
  moreover have \<open>max_list (vars_fm p) < n\<close>
    using GR.hyps(3) by (simp add: max_list_append)
  ultimately have \<open>\<lbrakk>E, F, G\<rbrakk> q \<longrightarrow> (\<forall>x. \<lbrakk>E\<langle>0:x\<rangle>, F, G\<rbrakk> p)\<close>
    using upd_vars_fm by simp
  then show ?case
    by simp
qed (auto simp: tautology)

corollary \<open>\<not> (\<turnstile> \<^bold>\<bottom>)\<close>
  using soundness by fastforce

section \<open>Derived Rules\<close>

lemma AS: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  by auto

lemma AK: \<open>\<turnstile> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q\<close>
  by auto

lemma Neg: \<open>\<turnstile> \<^bold>\<not> \<^bold>\<not> p \<^bold>\<longrightarrow> p\<close>
  by auto

lemma contraposition:
  \<open>\<turnstile> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<not> p\<close>
  \<open>\<turnstile> (\<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<not> p) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q\<close>
  by (auto intro: TA)

lemma GR': \<open>\<turnstile> \<^bold>\<not> p\<langle>\<^bold>#n/0\<rangle> \<^bold>\<longrightarrow> q \<Longrightarrow> max_var p < n \<Longrightarrow> max_var q < n \<Longrightarrow> \<turnstile> \<^bold>\<not> \<^bold>\<forall>p \<^bold>\<longrightarrow> q\<close>
proof -
  assume *: \<open>\<turnstile> \<^bold>\<not> p\<langle>\<^bold>#n/0\<rangle> \<^bold>\<longrightarrow> q\<close> and n: \<open>max_var p < n\<close> \<open>max_var q < n\<close>
  have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> p\<langle>\<^bold>#n/0\<rangle>\<close>
    using * contraposition(1) by fast
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> p\<langle>\<^bold>#n/0\<rangle>\<close>
    by (meson AK AS MP Neg)
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<forall>p\<close>
    using n by auto
  then have \<open>\<turnstile> \<^bold>\<not> \<^bold>\<forall>p \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> q\<close>
    using contraposition(1) by fast
  then show ?thesis
    by (meson AK AS MP Neg)
qed

lemma Imp3: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> ((s \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> (s \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> s \<^bold>\<longrightarrow> r)\<close>
  by auto

lemma imply_ImpE: \<open>\<turnstile> ps \<^bold>\<leadsto> p \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q\<close>
  by (induct ps) (auto intro: Imp3 MP)

lemma MP' [trans, dest]: \<open>ps \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> ps \<turnstile> p \<Longrightarrow> ps \<turnstile> q\<close>
  using imply_ImpE by fast

lemma imply_Cons [intro]: \<open>ps \<turnstile> q \<Longrightarrow> p # ps \<turnstile> q\<close>
  by (auto intro: MP AK)

lemma imply_head [intro]: \<open>p # ps \<turnstile> p\<close>
proof (induct ps)
  case (Cons q ps)
  then show ?case
    by (metis AK MP' imply.simps(1-2))
qed auto

lemma imply_lift_Imp [simp]:
  assumes \<open>\<turnstile> p \<^bold>\<longrightarrow> q\<close>
  shows \<open>\<turnstile> p \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q\<close>
  using assms MP MP' imply_head by (metis imply.simps(2))

lemma add_imply [simp]: \<open>\<turnstile> q \<Longrightarrow> ps \<turnstile> q\<close>
  using MP imply_head by (auto simp del: TA)

lemma imply_mem [simp]: \<open>p \<in> set ps \<Longrightarrow> ps \<turnstile> p\<close>
proof (induct ps)
  case (Cons q ps)
  then show ?case
    by (metis imply_Cons imply_head set_ConsD)
qed simp

lemma deduct1: \<open>ps \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> p # ps \<turnstile> q\<close>
  by (meson MP' imply_Cons imply_head)

lemma imply_append [iff]: \<open>(ps @ qs \<^bold>\<leadsto> r) = (ps \<^bold>\<leadsto> qs \<^bold>\<leadsto> r)\<close>
  by (induct ps) simp_all

lemma imply_swap_append: \<open>ps @ qs \<turnstile> r \<Longrightarrow> qs @ ps \<turnstile> r\<close>
proof (induct qs arbitrary: ps)
  case (Cons q qs)
  then show ?case
    by (metis deduct1 imply.simps(2) imply_append)
qed simp

lemma deduct2: \<open>p # ps \<turnstile> q \<Longrightarrow> ps \<turnstile> p \<^bold>\<longrightarrow> q\<close>
  by (metis imply.simps(1-2) imply_append imply_swap_append)

lemmas deduct [iff] = deduct1 deduct2

lemma cut [trans, dest]: \<open>p # ps \<turnstile> r \<Longrightarrow> q # ps \<turnstile> p \<Longrightarrow> q # ps \<turnstile> r\<close>
  by (meson MP' deduct(2) imply_Cons)

lemma Boole: \<open>(\<^bold>\<not> p) # ps \<turnstile> \<^bold>\<bottom> \<Longrightarrow> ps \<turnstile> p\<close>
  by (meson MP' Neg add_imply deduct(2))

lemma imply_weaken: \<open>ps \<turnstile> q \<Longrightarrow> set ps \<subseteq> set ps' \<Longrightarrow> ps' \<turnstile> q\<close>
proof (induct ps arbitrary: q)
  case (Cons p ps)
  then show ?case
    by (metis MP' deduct(2) imply_mem insert_subset list.simps(15))
qed simp

section \<open>Consistent\<close>

definition \<open>consistent S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>

lemma UN_finite_bound:
  assumes \<open>finite A\<close> and \<open>A \<subseteq> (\<Union>n. f n)\<close>
  shows \<open>\<exists>m :: nat. A \<subseteq> (\<Union>n \<le> m. f n)\<close>
  using assms
proof (induct rule: finite_induct)
  case (insert x A)
  then obtain m where \<open>A \<subseteq> (\<Union>n \<le> m. f n)\<close>
    by fast
  then have \<open>A \<subseteq> (\<Union>n \<le> (m + k). f n)\<close> for k
    by fastforce
  moreover obtain m' where \<open>x \<in> f m'\<close>
    using insert(4) by blast
  ultimately have \<open>{x} \<union> A \<subseteq> (\<Union>n \<le> m + m'. f n)\<close>
    by auto
  then show ?case
    by blast
qed simp

lemma split_list:
  assumes \<open>x \<in> set A\<close>
  shows \<open>set (x # removeAll x A) = set A \<and> x \<notin> set (removeAll x A)\<close>
  using assms by auto

lemma imply_vars_fm: \<open>vars_fm (ps \<^bold>\<leadsto> q) = concat (map vars_fm ps) @ vars_fm q\<close>
  by (induct ps) auto

lemma inconsistent_fm:
  assumes \<open>consistent S\<close> and \<open>\<not> consistent ({p} \<union> S)\<close>
  obtains S' where \<open>set S' \<subseteq> S\<close> and \<open>p # S' \<turnstile> \<^bold>\<bottom>\<close>
proof -
  obtain S' where S': \<open>set S' \<subseteq> {p} \<union> S\<close> \<open>p \<in> set S'\<close> \<open>S' \<turnstile> \<^bold>\<bottom>\<close>
    using assms unfolding consistent_def by blast
  then obtain S'' where S'': \<open>set (p # S'') = set S'\<close> \<open>p \<notin> set S''\<close>
    using split_list by metis
  then have \<open>p # S'' \<turnstile> \<^bold>\<bottom>\<close>
    using \<open>S' \<turnstile> \<^bold>\<bottom>\<close> imply_weaken by blast
  then show ?thesis
    using that S'' S'(1)
    by (metis Diff_insert_absorb Diff_subset_conv list.simps(15))
qed

definition max_set :: \<open>nat set \<Rightarrow> nat\<close> where
  \<open>max_set X \<equiv> if X = {} then 0 else Max X\<close>

lemma max_list_in_Cons: \<open>xs \<noteq> [] \<Longrightarrow> max_list xs \<in> set xs\<close>
proof (induct xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  then show ?case
    by (metis linorder_not_less list.set_intros(1-2) max.absorb2 max.absorb3
        max_list.simps(1-2) max_nat.right_neutral)
qed

lemma max_list_max: \<open>\<forall>x \<in> set xs. x \<le> max_list xs\<close>
  by (induct xs) auto

lemma max_list_in_set: \<open>finite S \<Longrightarrow> set xs \<subseteq> S \<Longrightarrow> max_list xs \<le> max_set S\<close>
  unfolding max_set_def using max_list_in_Cons
  by (metis (mono_tags, lifting) Max_ge bot.extremum_uniqueI bot_nat_0.extremum max_list.simps(1)
      set_empty subsetD)

lemma consistent_add_witness:
  assumes \<open>consistent S\<close> and \<open>(\<^bold>\<not> \<^bold>\<forall>p) \<in> S\<close>
    and \<open>finite (vars S)\<close> and \<open>max_set (vars S) < n\<close>
  shows \<open>consistent ({\<^bold>\<not> p\<langle>\<^bold>#n/0\<rangle>} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {\<^bold>\<not> p\<langle>\<^bold>#n/0\<rangle>} \<union> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>set S' \<subseteq> S\<close> and \<open>(\<^bold>\<not> p\<langle>\<^bold>#n/0\<rangle>) # S' \<turnstile> \<^bold>\<bottom>\<close>
    using assms inconsistent_fm unfolding consistent_def by metis
  then have \<open>\<turnstile> \<^bold>\<not> p\<langle>\<^bold>#n/0\<rangle> \<^bold>\<longrightarrow> S' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    by simp
  moreover have \<open>max_list (vars_fm p) < n\<close>
    using assms(2-4) max_list_in_set by fastforce
  moreover have \<open>\<forall>p \<in> set S'. max_list (vars_fm p) < n\<close>
    using \<open>set S' \<subseteq> S\<close> assms(3-4) max_list_in_set
    by (meson Union_upper image_eqI order_le_less_trans subsetD)
  then have \<open>max_list (concat (map vars_fm S')) < n\<close>
    using assms(4) by (induct S') (auto simp: max_list_append)
  then have \<open>max_list (vars_fm (S' \<^bold>\<leadsto> \<^bold>\<bottom>)) < n\<close>
    unfolding imply_vars_fm max_list_append by simp
  ultimately have \<open>\<turnstile> \<^bold>\<not> \<^bold>\<forall>p \<^bold>\<longrightarrow> S' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    using GR' unfolding max_list_append by auto
  then have \<open>(\<^bold>\<not> \<^bold>\<forall>p) # S' \<turnstile> \<^bold>\<bottom>\<close>
    by simp
  moreover have \<open>set ((\<^bold>\<not> \<^bold>\<forall>p) # S') \<subseteq> S\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

lemma consistent_add_instance:
  assumes \<open>consistent S\<close> and \<open>\<^bold>\<forall>p \<in> S\<close>
  shows \<open>consistent ({p\<langle>t/0\<rangle>} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {p\<langle>t/0\<rangle>} \<union> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>set S' \<subseteq> S\<close> and \<open>p\<langle>t/0\<rangle> # S' \<turnstile> \<^bold>\<bottom>\<close>
    using assms inconsistent_fm unfolding consistent_def by blast
  moreover have \<open>\<turnstile> \<^bold>\<forall>p \<^bold>\<longrightarrow> p\<langle>t/0\<rangle>\<close>
    using IA by blast
  ultimately have \<open>\<^bold>\<forall>p # S' \<turnstile> \<^bold>\<bottom>\<close>
    by (meson add_imply cut deduct(1))
  moreover have \<open>set ((\<^bold>\<forall>p) # S') \<subseteq> S\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

section \<open>Extension\<close>

fun witness where
  \<open>witness used (\<^bold>\<not> \<^bold>\<forall>p) = {\<^bold>\<not> p\<langle>\<^bold>#(SOME n. max_set used < n)/0\<rangle>}\<close>
| \<open>witness _ _ = {}\<close>

primrec extend where
  \<open>extend S f 0 = S\<close>
| \<open>extend S f (Suc n) =
   (let Sn = extend S f n in
     if consistent ({f n} \<union> Sn)
     then witness (vars ({f n} \<union> Sn)) (f n) \<union> {f n} \<union> Sn
     else Sn)\<close>

definition \<open>Extend S f \<equiv> \<Union>n. extend S f n\<close>

lemma Extend_subset: \<open>S \<subseteq> Extend S f\<close>
  unfolding Extend_def by (metis Union_upper extend.simps(1) range_eqI)

lemma extend_bound: \<open>(\<Union>n \<le> m. extend S f n) = extend S f m\<close>
  by (induct m) (simp_all add: atMost_Suc Let_def)

lemma finite_vars_witness [simp]: \<open>finite (vars (witness used p))\<close>
  by (induct used p rule: witness.induct) simp_all

lemma finite_vars_extend [simp]: \<open>finite (vars S) \<Longrightarrow> finite (vars (extend S f n))\<close>
  by (induct n) (simp_all add: Let_def)

lemma max_list_mono: \<open>set xs \<subseteq> set ys \<Longrightarrow> max_list xs \<le> max_list ys\<close>
  using max_list_max max_list_in_Cons
  by (metis less_nat_zero_code linorder_not_le max_list.simps(1) subset_code(1))

lemma consistent_witness:
  fixes p :: \<open>('f, 'p) fm\<close>
  assumes \<open>consistent S\<close> and \<open>p \<in> S\<close> and \<open>vars S \<subseteq> used\<close> and \<open>finite used\<close>
  shows \<open>consistent (witness used p \<union> S)\<close>
  using assms
proof (induct used p rule: witness.induct)
  case (1 used p)
  moreover have \<open>\<exists>n. max_set used < n\<close>
    by blast
  ultimately obtain n where n: \<open>witness used (\<^bold>\<not> \<^bold>\<forall>p) = {\<^bold>\<not> p\<langle>\<^bold>#n/0\<rangle>}\<close> and \<open>max_set used < n\<close>
    by (metis someI_ex witness.simps(1))
  then have \<open>max_set (vars S) < n\<close>
    using 1(3-4) max_list_mono order_le_less_trans
    by (metis (no_types, lifting) Max.subset_imp bot.extremum_uniqueI less_nat_zero_code linorder_neqE_nat max_set_def)
  moreover have \<open>finite (vars S)\<close>
    using 1(3-4) infinite_super by blast
  ultimately show ?case
    using 1 n(1) consistent_add_witness by metis
qed (auto simp: assms)

lemma consistent_extend:
  fixes f :: \<open>nat \<Rightarrow> ('f, 'p) fm\<close>
  assumes \<open>consistent S\<close> \<open>finite (vars S)\<close>
  shows \<open>consistent (extend S f n)\<close>
  using assms
proof (induct n)
  case (Suc n)
  then show ?case
    using consistent_witness[where S=\<open>{f n} \<union> _\<close>] by (auto simp: Let_def)
qed simp

lemma consistent_Extend:
  fixes f :: \<open>nat \<Rightarrow> ('f, 'p) fm\<close>
  assumes \<open>consistent S\<close> \<open>finite (vars S)\<close>
  shows \<open>consistent (Extend S f)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> Extend S f \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>S' \<turnstile> \<^bold>\<bottom>\<close> and \<open>set S' \<subseteq> Extend S f\<close>
    unfolding consistent_def by blast
  then obtain m where \<open>set S' \<subseteq> (\<Union>n \<le> m. extend S f n)\<close>
    unfolding Extend_def using UN_finite_bound by (metis List.finite_set)
  then have \<open>set S' \<subseteq> extend S f m\<close>
    using extend_bound by blast
  moreover have \<open>consistent (extend S f m)\<close>
    using assms consistent_extend by blast
  ultimately show False
    unfolding consistent_def using \<open>S' \<turnstile> \<^bold>\<bottom>\<close> by blast
qed

section \<open>Maximal\<close>

definition \<open>maximal S \<equiv> \<forall>p. p \<notin> S \<longrightarrow> \<not> consistent ({p} \<union> S)\<close>

lemma maximal_exactly_one:
  assumes \<open>consistent S\<close> and \<open>maximal S\<close>
  shows \<open>p \<in> S \<longleftrightarrow> (\<^bold>\<not> p) \<notin> S\<close>
proof
  assume \<open>p \<in> S\<close>
  show \<open>(\<^bold>\<not> p) \<notin> S\<close>
  proof
    assume \<open>(\<^bold>\<not> p) \<in> S\<close>
    then have \<open>set [p, \<^bold>\<not> p] \<subseteq> S\<close>
      using \<open>p \<in> S\<close> by simp
    moreover have \<open>[p, \<^bold>\<not> p] \<turnstile> \<^bold>\<bottom>\<close>
      by blast
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  assume \<open>(\<^bold>\<not> p) \<notin> S\<close>
  then have \<open>\<not> consistent ({\<^bold>\<not> p} \<union> S)\<close>
    using \<open>maximal S\<close> unfolding maximal_def by blast
  then obtain S' where \<open>set S' \<subseteq> S\<close> \<open>(\<^bold>\<not> p) # S' \<turnstile> \<^bold>\<bottom>\<close>
    using \<open>consistent S\<close> inconsistent_fm by blast
  then have \<open>S' \<turnstile> p\<close>
    using Boole by blast
  have \<open>consistent ({p} \<union> S)\<close>
    unfolding consistent_def
  proof
    assume \<open>\<exists>S'. set S' \<subseteq> {p} \<union> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
    then obtain S'' where \<open>set S'' \<subseteq> S\<close> and \<open>p # S'' \<turnstile> \<^bold>\<bottom>\<close>
      using assms inconsistent_fm unfolding consistent_def by blast
    then have \<open>S' @ S'' \<turnstile> \<^bold>\<bottom>\<close>
      using \<open>S' \<turnstile> p\<close> by (metis MP' add_imply imply.simps(2) imply_append)
    moreover have \<open>set (S' @ S'') \<subseteq> S\<close>
      using \<open>set S' \<subseteq> S\<close> \<open>set S'' \<subseteq> S\<close> by simp
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
  then show \<open>p \<in> S\<close>
    using \<open>maximal S\<close> unfolding maximal_def by blast
qed

lemma maximal_Extend:
  assumes \<open>surj f\<close>
  shows \<open>maximal (Extend S f)\<close>
proof (rule ccontr)
  assume \<open>\<not> maximal (Extend S f)\<close>
  then obtain p where
    \<open>p \<notin> Extend S f\<close> and \<open>consistent ({p} \<union> Extend S f)\<close>
    unfolding maximal_def using assms consistent_Extend by blast
  obtain k where k: \<open>f k = p\<close>
    using \<open>surj f\<close> unfolding surj_def by metis
  then have \<open>p \<notin> extend S f (Suc k)\<close>
    using \<open>p \<notin> Extend S f\<close> unfolding Extend_def by blast
  then have \<open>\<not> consistent ({p} \<union> extend S f k)\<close>
    using k by (auto simp: Let_def)
  moreover have \<open>{p} \<union> extend S f k \<subseteq> {p} \<union> Extend S f\<close>
    unfolding Extend_def by blast
  ultimately have \<open>\<not> consistent ({p} \<union> Extend S f)\<close>
    unfolding consistent_def by auto
  then show False
    using \<open>consistent ({p} \<union> Extend S f)\<close> by blast
qed

section \<open>Saturation\<close>

definition \<open>saturated S \<equiv> \<forall>p. (\<^bold>\<not> \<^bold>\<forall>p) \<in> S \<longrightarrow> (\<exists>n. (\<^bold>\<not> p\<langle>\<^bold>#n/0\<rangle>) \<in> S)\<close>

lemma saturated_Extend:
  assumes \<open>consistent (Extend S f)\<close> and \<open>surj f\<close>
  shows \<open>saturated (Extend S f)\<close>
proof (rule ccontr)
  assume \<open>\<not> saturated (Extend S f)\<close>
  then obtain p where p: \<open>(\<^bold>\<not> \<^bold>\<forall>p) \<in> Extend S f\<close> \<open>\<nexists>n. (\<^bold>\<not> p\<langle>\<^bold>#n/0\<rangle>) \<in> Extend S f\<close>
    unfolding saturated_def by blast
  obtain k where k: \<open>f k = (\<^bold>\<not> \<^bold>\<forall>p)\<close>
    using \<open>surj f\<close> unfolding surj_def by metis

  have \<open>extend S f k \<subseteq> Extend S f\<close>
    unfolding Extend_def by auto
  then have \<open>consistent ({\<^bold>\<not> \<^bold>\<forall>p} \<union> extend S f k)\<close>
    using assms(1) p(1) unfolding consistent_def by blast
  then have \<open>\<exists>n. extend S f (Suc k) = {\<^bold>\<not> p\<langle>\<^bold>#n/0\<rangle>} \<union> {\<^bold>\<not> \<^bold>\<forall>p} \<union> extend S f k\<close>
    using k by (auto simp: Let_def)
  moreover have \<open>extend S f (Suc k) \<subseteq> Extend S f\<close>
    unfolding Extend_def by blast
  ultimately show False
    using p(2) by auto
qed

section \<open>Hintikka\<close>

locale Hintikka =
  fixes H :: \<open>('f, 'p) fm set\<close>
  assumes
    NoFalsity: \<open>\<^bold>\<bottom> \<notin> H\<close> and
    ImpP: \<open>(p \<^bold>\<longrightarrow> q) \<in> H \<Longrightarrow> p \<notin> H \<or> q \<in> H\<close> and
    ImpN: \<open>(p \<^bold>\<longrightarrow> q) \<notin> H \<Longrightarrow> p \<in> H \<and> q \<notin> H\<close> and
    UniP: \<open>\<^bold>\<forall>p \<in> H \<Longrightarrow> \<forall>t. p\<langle>t/0\<rangle> \<in> H\<close> and
    UniN: \<open>\<^bold>\<forall>p \<notin> H \<Longrightarrow> \<exists>n. p\<langle>\<^bold>#n/0\<rangle> \<notin> H\<close>

subsection \<open>Model Existence\<close>

abbreviation hmodel (\<open>\<lbrakk>_\<rbrakk>\<close>) where \<open>\<lbrakk>H\<rbrakk> \<equiv> \<lbrakk>\<^bold>#, \<^bold>\<dagger>, \<lambda>P ts. Pre P ts \<in> H\<rbrakk>\<close>

lemma semantics_tm_id [simp]:
  \<open>\<lparr>\<^bold>#, \<^bold>\<dagger>\<rparr> t = t\<close>
  by (induct t) (auto cong: map_cong)

lemma semantics_tm_id_map [simp]: \<open>map \<lparr>\<^bold>#, \<^bold>\<dagger>\<rparr> ts = ts\<close>
  by (auto cong: map_cong)

theorem Hintikka_model:
  assumes \<open>Hintikka H\<close>
  shows \<open>p \<in> H \<longleftrightarrow> \<lbrakk>H\<rbrakk> p\<close>
proof (induct p rule: wf_induct[where r=\<open>measure size_fm\<close>])
  case 1
  then show ?case ..
next
  case (2 x)
  show \<open>x \<in> H \<longleftrightarrow> \<lbrakk>H\<rbrakk> x\<close>
  proof (cases x; safe)
    case Falsity
    assume \<open>\<^bold>\<bottom> \<in> H\<close>
    then have False
      using assms Hintikka.NoFalsity by fast
    then show \<open>\<lbrakk>H\<rbrakk> \<^bold>\<bottom>\<close> ..
  next
    case Falsity
    assume \<open>\<lbrakk>H\<rbrakk> \<^bold>\<bottom>\<close>
    then have False
      by simp
    then show \<open>\<^bold>\<bottom> \<in> H\<close> ..
  next
    case (Pre P ts)
    assume \<open>\<^bold>\<ddagger>P ts \<in> H\<close>
    then show \<open>\<lbrakk>H\<rbrakk> (\<^bold>\<ddagger>P ts)\<close>
      by simp
  next
    case (Pre P ts)
    assume \<open>\<lbrakk>H\<rbrakk> (\<^bold>\<ddagger>P ts)\<close>
    then show \<open>\<^bold>\<ddagger>P ts \<in> H\<close>
      by simp
  next
    case (Imp p q)
    assume \<open>(p \<^bold>\<longrightarrow> q) \<in> H\<close>
    then have \<open>p \<notin> H \<or> q \<in> H\<close>
      using assms Hintikka.ImpP by blast
    then have \<open>\<not> \<lbrakk>H\<rbrakk> p \<or> \<lbrakk>H\<rbrakk> q\<close>
      using 2 Imp by simp
    then show \<open>\<lbrakk>H\<rbrakk> (p \<^bold>\<longrightarrow> q)\<close>
      by simp
  next
    case (Imp p q)
    assume \<open>\<lbrakk>H\<rbrakk> (p \<^bold>\<longrightarrow> q)\<close>
    then have \<open>\<not> \<lbrakk>H\<rbrakk> p \<or> \<lbrakk>H\<rbrakk> q\<close>
      by simp
    then have \<open>p \<notin> H \<or> q \<in> H\<close>
      using 2 Imp by simp
    then show \<open>(p \<^bold>\<longrightarrow> q) \<in> H\<close>
      using assms Hintikka.ImpN by blast
  next
    case (Uni p)
    assume \<open>\<^bold>\<forall>p \<in> H\<close>
    then have \<open>\<forall>t. p\<langle>t/0\<rangle> \<in> H\<close>
      using assms Hintikka.UniP by metis
    then have \<open>\<forall>t. \<lbrakk>H\<rbrakk> (p\<langle>t/0\<rangle>)\<close>
      using 2 Uni by simp
    then show \<open>\<lbrakk>H\<rbrakk> (\<^bold>\<forall>p)\<close>
      by simp
  next
    case (Uni p)
    assume \<open>\<lbrakk>H\<rbrakk> (\<^bold>\<forall>p)\<close>
    then have \<open>\<forall>t. \<lbrakk>H\<rbrakk> (p\<langle>t/0\<rangle>)\<close>
      by simp
    then have \<open>\<forall>t. p\<langle>t/0\<rangle> \<in> H\<close>
      using 2 Uni by simp
    then show \<open>\<^bold>\<forall>p \<in> H\<close>
      using assms Hintikka.UniN by blast
  qed
qed

subsection \<open>Maximal Consistent Sets are Hintikka Sets\<close>

lemma inconsistent_head:
  assumes \<open>consistent S\<close> and \<open>maximal S\<close> and \<open>p \<notin> S\<close>
  obtains S' where \<open>set S' \<subseteq> S\<close> and \<open>p # S' \<turnstile> \<^bold>\<bottom>\<close>
  using assms inconsistent_fm unfolding consistent_def maximal_def by metis

lemma inconsistent_parts [simp]:
  assumes \<open>ps \<turnstile> \<^bold>\<bottom>\<close> and \<open>set ps \<subseteq> S\<close>
  shows \<open>\<not> consistent S\<close>
  using assms unfolding consistent_def by blast

lemma Hintikka_Extend:
  fixes H :: \<open>('f, 'p) fm set\<close>
  assumes \<open>consistent H\<close> and \<open>maximal H\<close> and \<open>saturated H\<close>
  shows \<open>Hintikka H\<close>
proof
  show \<open>\<^bold>\<bottom> \<notin> H\<close>
  proof
    assume \<open>\<^bold>\<bottom> \<in> H\<close>
    moreover have \<open>[\<^bold>\<bottom>] \<turnstile> \<^bold>\<bottom>\<close>
      by blast
    ultimately have \<open>\<not> consistent H\<close>
      using inconsistent_parts[where ps=\<open>[\<^bold>\<bottom>]\<close>] by simp
    then show False
      using \<open>consistent H\<close> ..
  qed
next
  fix p q
  assume *: \<open>(p \<^bold>\<longrightarrow> q) \<in> H\<close>
  show \<open>p \<notin> H \<or> q \<in> H\<close>
  proof safe
    assume \<open>q \<notin> H\<close>
    then obtain Hq' where Hq': \<open>q # Hq' \<turnstile> \<^bold>\<bottom>\<close> \<open>set Hq' \<subseteq> H\<close>
      using assms inconsistent_head by metis

    assume \<open>p \<in> H\<close>
    then have \<open>(\<^bold>\<not> p) \<notin> H\<close>
      using assms maximal_exactly_one by blast
    then obtain Hp' where Hp': \<open>(\<^bold>\<not> p) # Hp' \<turnstile> \<^bold>\<bottom>\<close> \<open>set Hp' \<subseteq> H\<close>
      using assms inconsistent_head by metis

    let ?H' = \<open>Hp' @ Hq'\<close>
    have H': \<open>set ?H' = set Hp' \<union> set Hq'\<close>
      by simp
    then have \<open>set Hp' \<subseteq> set ?H'\<close> and \<open>set Hq' \<subseteq> set ?H'\<close>
      by blast+
    then have \<open>(\<^bold>\<not> p) # ?H' \<turnstile> \<^bold>\<bottom>\<close> and \<open>q # ?H' \<turnstile> \<^bold>\<bottom>\<close>
      using Hp'(1) Hq'(1) deduct imply_weaken by metis+
    then have \<open>(p \<^bold>\<longrightarrow> q) # ?H' \<turnstile> \<^bold>\<bottom>\<close>
      using Boole imply_Cons imply_head MP' cut by metis
    moreover have \<open>set ((p \<^bold>\<longrightarrow> q) # ?H') \<subseteq> H\<close>
      using \<open>q \<notin> H\<close> *(1) H' Hp'(2) Hq'(2) by auto
    ultimately show False
      using assms unfolding consistent_def by blast
  qed
next
  fix p q
  assume *: \<open>(p \<^bold>\<longrightarrow> q) \<notin> H\<close>
  show \<open>p \<in> H \<and> q \<notin> H\<close>
  proof (safe, rule ccontr)
    assume \<open>p \<notin> H\<close>
    then obtain H' where S': \<open>p # H' \<turnstile> \<^bold>\<bottom>\<close> \<open>set H' \<subseteq> H\<close>
      using assms inconsistent_head by metis
    moreover have \<open>(\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) # H' \<turnstile> p\<close>
      by auto
    ultimately have \<open>(\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) # H' \<turnstile> \<^bold>\<bottom>\<close>
      by blast
    moreover have \<open>set ((\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) # H') \<subseteq> H\<close>
      using *(1) S'(2) assms maximal_exactly_one by auto
    ultimately show False
      using assms unfolding consistent_def by blast
  next
    assume \<open>q \<in> H\<close>
    then have \<open>(\<^bold>\<not> q) \<notin> H\<close>
      using assms maximal_exactly_one by blast
    then obtain H' where H': \<open>(\<^bold>\<not> q) # H' \<turnstile> \<^bold>\<bottom>\<close> \<open>set H' \<subseteq> H\<close>
      using assms inconsistent_head by metis
    moreover have \<open>(\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) # H' \<turnstile> \<^bold>\<not> q\<close>
      by auto
    ultimately have \<open>(\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) # H' \<turnstile> \<^bold>\<bottom>\<close>
      by blast
    moreover have \<open>set ((\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) # H') \<subseteq> H\<close>
      using *(1) H'(2) assms maximal_exactly_one by auto
    ultimately show False
      using assms unfolding consistent_def by blast
  qed
next
  fix p
  assume \<open>\<^bold>\<forall>p \<in> H\<close>
  then show \<open>\<forall>t. p\<langle>t/0\<rangle> \<in> H\<close>
    using assms consistent_add_instance unfolding maximal_def by blast
next
  fix p
  assume \<open>\<^bold>\<forall>p \<notin> H\<close>
  then show \<open>\<exists>n. p\<langle>\<^bold>#n/0\<rangle> \<notin> H\<close>
    using assms maximal_exactly_one unfolding saturated_def by fast
qed

section \<open>Countable Formulas\<close>

instance tm :: (countable) countable
  by countable_datatype

instance fm :: (countable, countable) countable
  by countable_datatype

section \<open>Completeness\<close>

theorem strong_completeness:
  fixes p :: \<open>('f :: countable, 'p :: countable) fm\<close>
  assumes \<open>\<forall>(E :: _ \<Rightarrow> 'f tm) F G. Ball X \<lbrakk>E, F, G\<rbrakk> \<longrightarrow> \<lbrakk>E, F, G\<rbrakk> p\<close>
    and \<open>finite (vars X)\<close>
  shows \<open>\<exists>ps. set ps \<subseteq> X \<and> ps \<turnstile> p\<close>
proof (rule ccontr)
  assume \<open>\<nexists>ps. set ps \<subseteq> X \<and> ps \<turnstile> p\<close>
  then have *: \<open>\<nexists>ps. set ps \<subseteq> X \<and> (\<^bold>\<not> p) # ps \<turnstile> \<^bold>\<bottom>\<close>
    using Boole by blast

  let ?S = \<open>{\<^bold>\<not> p} \<union> X\<close>
  let ?H = \<open>Extend ?S from_nat\<close>

  have \<open>consistent ?S\<close>
    using * by (metis consistent_def imply_Cons inconsistent_fm)
  moreover have \<open>finite (vars ?S)\<close>
    using assms by simp
  ultimately have \<open>consistent ?H\<close> and \<open>maximal ?H\<close>
    using assms consistent_Extend maximal_Extend surj_from_nat by blast+
  moreover from this have \<open>saturated ?H\<close>
    using saturated_Extend by fastforce
  ultimately have \<open>Hintikka ?H\<close>
    using assms Hintikka_Extend by blast

  have \<open>\<lbrakk>?H\<rbrakk> p\<close> if \<open>p \<in> ?S\<close> for p
    using that Extend_subset Hintikka_model \<open>Hintikka ?H\<close> by blast
  then have \<open>\<lbrakk>?H\<rbrakk> (\<^bold>\<not> p)\<close> and \<open>\<forall>q \<in> X. \<lbrakk>?H\<rbrakk> q\<close>
    by fastforce+
  moreover from this have \<open>\<lbrakk>?H\<rbrakk> p\<close>
    using assms(1) by blast
  ultimately show False
    by simp
qed

theorem completeness:
  fixes p :: \<open>('f :: countable, 'p :: countable) fm\<close>
  assumes \<open>\<forall>(E :: _ \<Rightarrow> 'f tm) F G. \<lbrakk>E, F, G\<rbrakk> p\<close>
  shows \<open>\<turnstile> p\<close>
  using assms strong_completeness[where X=\<open>{}\<close>] by simp

corollary
  fixes p :: \<open>(unit, unit) fm\<close>
  assumes \<open>\<forall>(E :: nat \<Rightarrow> unit tm) F G. \<lbrakk>E, F, G\<rbrakk> p\<close>
  shows \<open>\<turnstile> p\<close>
  using completeness assms .

section \<open>Main Result\<close>

abbreviation valid :: \<open>(nat, nat) fm \<Rightarrow> bool\<close> where
  \<open>valid p \<equiv> \<forall>(E :: nat \<Rightarrow> nat tm) F G. \<lbrakk>E, F, G\<rbrakk> p\<close>

theorem main: \<open>valid p \<longleftrightarrow> (\<turnstile> p)\<close>
  using completeness soundness by blast

end
