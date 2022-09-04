(*
  File:      FOL_Axiomatic.thy
  Author:    Asta Halkjær From

  This work is a formalization of the soundness and completeness of an axiomatic system
  for first-order logic. The proof system is based on System Q1 by Smullyan
  and the completeness proof follows his textbook "First-Order Logic" (Springer-Verlag 1968).
  The completeness proof is in the Henkin style where a consistent set
  is extended to a maximal consistent set using Lindenbaum's construction
  and Henkin witnesses are added during the construction to ensure saturation as well.
  The resulting set is a Hintikka set which, by the model existence theorem, is satisfiable
  in the Herbrand universe.
*)

theory FOL_Axiomatic imports "HOL-Library.Countable" begin

section \<open>Syntax\<close>

datatype (params_tm: 'f) tm
  = Var nat (\<open>\<^bold>#\<close>)
  | Fun 'f \<open>'f tm list\<close> (\<open>\<^bold>\<dagger>\<close>)

abbreviation Const (\<open>\<^bold>\<star>\<close>) where \<open>\<^bold>\<star>a \<equiv> \<^bold>\<dagger>a []\<close>

datatype (params_fm: 'f, 'p) fm
  = Falsity (\<open>\<^bold>\<bottom>\<close>)
  | Pre 'p \<open>'f tm list\<close> (\<open>\<^bold>\<ddagger>\<close>)
  | Imp \<open>('f, 'p) fm\<close> \<open>('f, 'p) fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | Uni \<open>('f, 'p) fm\<close> (\<open>\<^bold>\<forall>\<close>)

abbreviation Neg (\<open>\<^bold>\<not> _\<close> [70] 70) where \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

term \<open>\<^bold>\<forall>(\<^bold>\<bottom> \<^bold>\<longrightarrow> \<^bold>\<ddagger>''P'' [\<^bold>\<dagger>''f'' [\<^bold>#0]])\<close>

section \<open>Semantics\<close>

definition shift (\<open>_\<langle>_:_\<rangle>\<close>) where
  \<open>E\<langle>n:x\<rangle> m \<equiv> if m < n then E m else if m = n then x else E (m-1)\<close>

primrec semantics_tm (\<open>\<lparr>_, _\<rparr>\<close>) where
  \<open>\<lparr>E, F\<rparr> (\<^bold>#n) = E n\<close>
| \<open>\<lparr>E, F\<rparr> (\<^bold>\<dagger>f ts) = F f (map \<lparr>E, F\<rparr> ts)\<close>

primrec semantics_fm (\<open>\<lbrakk>_, _, _\<rbrakk>\<close>) where
  \<open>\<lbrakk>_, _, _\<rbrakk> \<^bold>\<bottom> = False\<close>
| \<open>\<lbrakk>E, F, G\<rbrakk> (\<^bold>\<ddagger>P ts) = G P (map \<lparr>E, F\<rparr> ts)\<close>
| \<open>\<lbrakk>E, F, G\<rbrakk> (p \<^bold>\<longrightarrow> q) = (\<lbrakk>E, F, G\<rbrakk> p \<longrightarrow> \<lbrakk>E, F, G\<rbrakk> q)\<close>
| \<open>\<lbrakk>E, F, G\<rbrakk> (\<^bold>\<forall>p) = (\<forall>x. \<lbrakk>E\<langle>0:x\<rangle>, F, G\<rbrakk> p)\<close>

proposition \<open>\<lbrakk>E, F, G\<rbrakk> (\<^bold>\<forall>(\<^bold>\<ddagger>P [\<^bold># 0]) \<^bold>\<longrightarrow> \<^bold>\<ddagger>P [\<^bold>\<star>a])\<close>
  by (simp add: shift_def)

section \<open>Operations\<close>

subsection \<open>Shift\<close>

context fixes n m :: nat begin

lemma shift_eq [simp]: \<open>n = m \<Longrightarrow> E\<langle>n:x\<rangle> m = x\<close>
  by (simp add: shift_def)

lemma shift_gt [simp]: \<open>m < n \<Longrightarrow> E\<langle>n:x\<rangle> m = E m\<close>
  by (simp add: shift_def)

lemma shift_lt [simp]: \<open>n < m \<Longrightarrow> E\<langle>n:x\<rangle> m = E (m-1)\<close>
  by (simp add: shift_def)

lemma shift_commute [simp]: \<open>(E\<langle>n:y\<rangle>\<langle>0:x\<rangle>) = (E\<langle>0:x\<rangle>\<langle>n+1:y\<rangle>)\<close>
proof
  fix m
  show \<open>(E\<langle>n:y\<rangle>\<langle>0:x\<rangle>) m = (E\<langle>0:x\<rangle>\<langle>n+1:y\<rangle>) m\<close>
    unfolding shift_def by (cases m) simp_all
qed

end

subsection \<open>Parameters\<close>

abbreviation \<open>params S \<equiv> \<Union>p \<in> S. params_fm p\<close>

lemma upd_params_tm [simp]: \<open>f \<notin> params_tm t \<Longrightarrow> \<lparr>E, F(f := x)\<rparr> t = \<lparr>E, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma upd_params_fm [simp]: \<open>f \<notin> params_fm p \<Longrightarrow> \<lbrakk>E, F(f := x), G\<rbrakk> p = \<lbrakk>E, F, G\<rbrakk> p\<close>
  by (induct p arbitrary: E) (auto cong: map_cong)

lemma finite_params_tm [simp]: \<open>finite (params_tm t)\<close>
  by (induct t) simp_all

lemma finite_params_fm [simp]: \<open>finite (params_fm p)\<close>
  by (induct p) simp_all

subsection \<open>Instantiation\<close>

primrec lift_tm (\<open>\<^bold>\<up>\<close>) where
  \<open>\<^bold>\<up>(\<^bold>#n) = \<^bold>#(n+1)\<close>
| \<open>\<^bold>\<up>(\<^bold>\<dagger>f ts) = \<^bold>\<dagger>f (map \<^bold>\<up> ts)\<close>

primrec inst_tm (\<open>\<llangle>_'/_\<rrangle>\<close>) where
  \<open>\<llangle>s/m\<rrangle>(\<^bold>#n) = (if n < m then \<^bold>#n else if n = m then s else \<^bold>#(n-1))\<close>
| \<open>\<llangle>s/m\<rrangle>(\<^bold>\<dagger>f ts) = \<^bold>\<dagger>f (map \<llangle>s/m\<rrangle> ts)\<close>

primrec inst_fm (\<open>\<langle>_'/_\<rangle>\<close>) where
  \<open>\<langle>_/_\<rangle>\<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>\<langle>s/m\<rangle>(\<^bold>\<ddagger>P ts) = \<^bold>\<ddagger>P (map \<llangle>s/m\<rrangle> ts)\<close>
| \<open>\<langle>s/m\<rangle>(p \<^bold>\<longrightarrow> q) = \<langle>s/m\<rangle>p \<^bold>\<longrightarrow> \<langle>s/m\<rangle>q\<close>
| \<open>\<langle>s/m\<rangle>(\<^bold>\<forall>p) = \<^bold>\<forall>(\<langle>\<^bold>\<up>s/m+1\<rangle>p)\<close>

lemma lift_lemma [simp]: \<open>\<lparr>E\<langle>0:x\<rangle>, F\<rparr> (\<^bold>\<up>t) = \<lparr>E, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma inst_tm_semantics [simp]: \<open>\<lparr>E, F\<rparr> (\<llangle>s/m\<rrangle>t) = \<lparr>E\<langle>m:\<lparr>E, F\<rparr> s\<rangle>, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma inst_fm_semantics [simp]: \<open>\<lbrakk>E, F, G\<rbrakk> (\<langle>t/m\<rangle>p) = \<lbrakk>E\<langle>m:\<lparr>E, F\<rparr> t\<rangle>, F, G\<rbrakk> p\<close>
  by (induct p arbitrary: E m t) (auto cong: map_cong)

subsection \<open>Size\<close>

text \<open>The built-in \<open>size\<close> is not invariant under substitution.\<close>

primrec size_fm where
  \<open>size_fm \<^bold>\<bottom> = 1\<close>
| \<open>size_fm (\<^bold>\<ddagger>_ _) = 1\<close>
| \<open>size_fm (p \<^bold>\<longrightarrow> q) = 1 + size_fm p + size_fm q\<close>
| \<open>size_fm (\<^bold>\<forall>p) = 1 + size_fm p\<close>

lemma size_inst_fm [simp]: \<open>size_fm (\<langle>t/m\<rangle>p) = size_fm p\<close>
  by (induct p arbitrary: m t) simp_all

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

lemma tautology[simp]: \<open>tautology p \<Longrightarrow> \<lbrakk>E, F, G\<rbrakk> p\<close>
  using boolean_semantics by metis

proposition \<open>\<exists>p. (\<forall>E F G. \<lbrakk>E, F, G\<rbrakk> p) \<and> \<not> tautology p\<close>
  by (metis boolean.simps(4) fm.simps(36) semantics_fm.simps(1,3,4))

section \<open>Calculus\<close>

text \<open>Adapted from System Q1 by Smullyan in First-Order Logic (1968).\<close>

inductive Axiomatic (\<open>\<turnstile> _\<close> [50] 50) where
  TA: \<open>tautology p \<Longrightarrow> \<turnstile> p\<close>
| IA: \<open>\<turnstile> \<^bold>\<forall>p \<^bold>\<longrightarrow> \<langle>t/0\<rangle>p\<close>
| MP: \<open>\<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> \<turnstile> p \<Longrightarrow> \<turnstile> q\<close>
| GR: \<open>\<turnstile> q \<^bold>\<longrightarrow> \<langle>\<^bold>\<star>a/0\<rangle>p \<Longrightarrow> a \<notin> params {p, q} \<Longrightarrow> \<turnstile> q \<^bold>\<longrightarrow> \<^bold>\<forall>p\<close>

text \<open>We simulate assumptions on the lhs of \<open>\<turnstile>\<close> with a chain of implications on the rhs.\<close>

primrec imply (infixr \<open>\<^bold>\<leadsto>\<close> 56) where
  \<open>([] \<^bold>\<leadsto> q) = q\<close>
| \<open>(p # ps \<^bold>\<leadsto> q) = (p \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q)\<close>

abbreviation Axiomatic_assms (\<open>_ \<turnstile> _\<close> [50, 50] 50) where
  \<open>ps \<turnstile> q \<equiv> \<turnstile> ps \<^bold>\<leadsto> q\<close>

section \<open>Soundness\<close>

theorem soundness: \<open>\<turnstile> p \<Longrightarrow> \<lbrakk>E, F, G\<rbrakk> p\<close>
proof (induct p arbitrary: F rule: Axiomatic.induct)
  case (GR q a p)
  moreover from this have \<open>\<lbrakk>E, F(a := x), G\<rbrakk> (q \<^bold>\<longrightarrow> \<langle>\<^bold>\<star>a/0\<rangle>p)\<close> for x
    by blast
  ultimately show ?case
    by fastforce
qed auto

corollary \<open>\<not> (\<turnstile> \<^bold>\<bottom>)\<close>
  using soundness by fastforce

section \<open>Derived Rules\<close>

lemma Imp1: \<open>\<turnstile> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q\<close>
  and Imp2: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  and Neg: \<open>\<turnstile> \<^bold>\<not> \<^bold>\<not> p \<^bold>\<longrightarrow> p\<close>
  by (auto intro: TA)

text \<open>The tautology axiom TA is not used directly beyond this point.\<close>

lemma Tran': \<open>\<turnstile> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  by (meson Imp1 Imp2 MP)

lemma Swap: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  by (meson Imp1 Imp2 Tran' MP)

lemma Tran: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  by (meson Swap Tran' MP)

text \<open>Note that contraposition in the other direction is an instance of the lemma Tran.\<close>

lemma contraposition: \<open>\<turnstile> (\<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<not> p) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q\<close>
  by (meson Neg Swap Tran MP)

lemma GR': \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p \<^bold>\<longrightarrow> q \<Longrightarrow> a \<notin> params {p, q} \<Longrightarrow> \<turnstile> \<^bold>\<not> (\<^bold>\<forall>p) \<^bold>\<longrightarrow> q\<close>
proof -
  assume *: \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p \<^bold>\<longrightarrow> q\<close> and a: \<open>a \<notin> params {p, q}\<close>
  have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p\<close>
    using * Tran MP by metis
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<langle>\<^bold>\<star>a/0\<rangle>p\<close>
    using Neg Tran MP by metis
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<forall>p\<close>
    using a by (auto intro: GR)
  then have \<open>\<turnstile> \<^bold>\<not> (\<^bold>\<forall>p) \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> q\<close>
    using Tran MP by metis
  then show ?thesis
    using Neg Tran MP by metis
qed

lemma imply_ImpE: \<open>\<turnstile> ps \<^bold>\<leadsto> p \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q\<close>
proof (induct ps)
  case Nil
  then show ?case
    by (metis Imp1 Swap MP imply.simps(1))
next
  case (Cons r ps)
  have \<open>\<turnstile> (r \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> p) \<^bold>\<longrightarrow> r \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q\<close>
    by (meson Cons.hyps Imp1 Imp2 MP)
  then have \<open>\<turnstile> (r \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> p) \<^bold>\<longrightarrow> (r \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q)) \<^bold>\<longrightarrow> r \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q\<close>
    by (meson Imp1 Imp2 MP)
  then show ?case
    by simp
qed

lemma MP': \<open>ps \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> ps \<turnstile> p \<Longrightarrow> ps \<turnstile> q\<close>
  using imply_ImpE MP by metis

lemma imply_Cons [intro]: \<open>ps \<turnstile> q \<Longrightarrow> p # ps \<turnstile> q\<close>
  by (auto intro: MP Imp1)

lemma imply_head [intro]: \<open>p # ps \<turnstile> p\<close>
  by (induct ps) (metis Imp1 Imp2 MP imply.simps, metis Imp1 Imp2 MP imply.simps(2))

lemma add_imply [simp]: \<open>\<turnstile> q \<Longrightarrow> ps \<turnstile> q\<close>
  using imply_head by (metis MP imply.simps(2))

lemma imply_mem [simp]: \<open>p \<in> set ps \<Longrightarrow> ps \<turnstile> p\<close>
  using imply_head imply_Cons by (induct ps) fastforce+

lemma deduct1: \<open>ps \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> p # ps \<turnstile> q\<close>
  by (meson MP' imply_Cons imply_head)

lemma imply_append [iff]: \<open>(ps @ qs \<^bold>\<leadsto> r) = (ps \<^bold>\<leadsto> qs \<^bold>\<leadsto> r)\<close>
  by (induct ps) simp_all

lemma imply_swap_append: \<open>ps @ qs \<turnstile> r \<Longrightarrow> qs @ ps \<turnstile> r\<close>
proof (induct qs arbitrary: ps)
  case Cons
  then show ?case
    by (metis deduct1 imply.simps(2) imply_append)
qed simp

lemma deduct2: \<open>p # ps \<turnstile> q \<Longrightarrow> ps \<turnstile> p \<^bold>\<longrightarrow> q\<close>
  by (metis imply.simps imply_append imply_swap_append)

lemmas deduct [iff] = deduct1 deduct2

lemma cut: \<open>p # ps \<turnstile> r \<Longrightarrow> q # ps \<turnstile> p \<Longrightarrow> q # ps \<turnstile> r\<close>
  by (meson MP' deduct(2) imply_Cons)

lemma Boole: \<open>(\<^bold>\<not> p) # ps \<turnstile> \<^bold>\<bottom> \<Longrightarrow> ps \<turnstile> p\<close>
  by (meson MP' Neg add_imply deduct(2))

lemma imply_weaken: \<open>ps \<turnstile> q \<Longrightarrow> set ps \<subseteq> set ps' \<Longrightarrow> ps' \<turnstile> q\<close>
  by (induct ps arbitrary: q) (simp, metis MP' deduct(2) imply_mem insert_subset list.simps(15))

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

lemma imply_params_fm: \<open>params_fm (ps \<^bold>\<leadsto> q) = params_fm q \<union> (\<Union>p \<in> set ps. params_fm p)\<close>
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
    using that S'' S'(1) Diff_insert_absorb Diff_subset_conv list.simps(15) by metis
qed

lemma consistent_add_witness:
  assumes \<open>consistent S\<close> and \<open>\<^bold>\<not> (\<^bold>\<forall>p) \<in> S\<close> and \<open>a \<notin> params S\<close>
  shows \<open>consistent ({\<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {\<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p} \<union> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>set S' \<subseteq> S\<close> and \<open>(\<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p) # S' \<turnstile> \<^bold>\<bottom>\<close>
    using assms inconsistent_fm unfolding consistent_def by metis
  then have \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p \<^bold>\<longrightarrow> S' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    by simp
  moreover have \<open>a \<notin> params_fm p\<close>
    using assms(2-3) by auto
  moreover have \<open>\<forall>p \<in> set S'. a \<notin> params_fm p\<close>
    using \<open>set S' \<subseteq> S\<close> assms(3) by auto
  then have \<open>a \<notin> params_fm (S' \<^bold>\<leadsto> \<^bold>\<bottom>)\<close>
    by (simp add: imply_params_fm)
  ultimately have \<open>\<turnstile> \<^bold>\<not> (\<^bold>\<forall>p) \<^bold>\<longrightarrow> S' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    using GR' by fast
  then have \<open>\<^bold>\<not> (\<^bold>\<forall>p) # S' \<turnstile> \<^bold>\<bottom>\<close>
    by simp
  moreover have \<open>set ((\<^bold>\<not> (\<^bold>\<forall>p)) # S') \<subseteq> S\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

lemma consistent_add_instance:
  assumes \<open>consistent S\<close> and \<open>\<^bold>\<forall>p \<in> S\<close>
  shows \<open>consistent ({\<langle>t/0\<rangle>p} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {\<langle>t/0\<rangle>p} \<union> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>set S' \<subseteq> S\<close> and \<open>\<langle>t/0\<rangle>p # S' \<turnstile> \<^bold>\<bottom>\<close>
    using assms inconsistent_fm unfolding consistent_def by blast
  moreover have \<open>\<turnstile> \<^bold>\<forall>p \<^bold>\<longrightarrow> \<langle>t/0\<rangle>p\<close>
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
  \<open>witness used (\<^bold>\<not> (\<^bold>\<forall>p)) = {\<^bold>\<not> \<langle>\<^bold>\<star>(SOME a. a \<notin> used)/0\<rangle>p}\<close>
| \<open>witness _ _ = {}\<close>

primrec extend where
  \<open>extend S f 0 = S\<close>
| \<open>extend S f (Suc n) =
   (let Sn = extend S f n in
     if consistent ({f n} \<union> Sn)
     then witness (params ({f n} \<union> Sn)) (f n) \<union> {f n} \<union> Sn
     else Sn)\<close>

definition \<open>Extend S f \<equiv> \<Union>n. extend S f n\<close>

lemma extend_subset: \<open>S \<subseteq> extend S f n\<close>
  by (induct n) (fastforce simp: Let_def)+

lemma Extend_subset: \<open>S \<subseteq> Extend S f\<close>
  unfolding Extend_def by (metis Union_upper extend.simps(1) range_eqI)

lemma extend_bound: \<open>(\<Union>n \<le> m. extend S f n) = extend S f m\<close>
  by (induct m) (simp_all add: atMost_Suc Let_def)

lemma finite_params_witness [simp]: \<open>finite (params (witness used p))\<close>
  by (induct used p rule: witness.induct) simp_all

lemma finite_params_extend [simp]: \<open>finite (params (extend S f n) - params S)\<close>
  by (induct n) (simp_all add: Let_def Un_Diff)

lemma Set_Diff_Un: \<open>X - (Y \<union> Z) = X - Y - Z\<close>
  by blast

lemma infinite_params_extend:
  assumes \<open>infinite (UNIV - params S)\<close>
  shows \<open>infinite (UNIV - params (extend S f n))\<close>
proof -
  have \<open>finite (params (extend S f n) - params S)\<close>
    by simp
  then obtain extra where \<open>finite extra\<close> \<open>params (extend S f n) = extra \<union> params S\<close>
    using extend_subset by fast
  then have \<open>?thesis = infinite (UNIV - (extra \<union> params S))\<close>
    by simp
  also have \<open>\<dots> = infinite (UNIV - extra - params S)\<close>
    by (simp add: Set_Diff_Un)
  also have \<open>\<dots> = infinite (UNIV - params S)\<close>
    using \<open>finite extra\<close> by (metis Set_Diff_Un Un_commute finite_Diff2)
  finally show ?thesis
    using assms ..
qed

lemma consistent_witness:
  assumes \<open>consistent S\<close> and \<open>p \<in> S\<close> and \<open>params S \<subseteq> used\<close>
    and \<open>infinite (UNIV - used)\<close>
  shows \<open>consistent (witness used p \<union> S)\<close>
  using assms
proof (induct used p rule: witness.induct)
  case (1 used p)
  moreover have \<open>\<exists>a. a \<notin> used\<close>
    using 1(4) by (meson Diff_iff finite_params_fm finite_subset subset_iff)
  ultimately obtain a where a: \<open>witness used (\<^bold>\<not> (\<^bold>\<forall>p)) = {\<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p}\<close> and \<open>a \<notin> used\<close>
    by (metis someI_ex witness.simps(1))
  then have \<open>a \<notin> params S\<close>
    using 1(3) by fast
  then show ?case
    using 1(1-2) a(1) consistent_add_witness by metis
qed (auto simp: assms)

lemma consistent_extend:
  assumes \<open>consistent S\<close> and \<open>infinite (UNIV - params S)\<close>
  shows \<open>consistent (extend S f n)\<close>
proof (induct n)
  case (Suc n)
  have \<open>infinite (UNIV - params (extend S f n))\<close>
    using assms(2) infinite_params_extend by fast
  with finite_params_fm have \<open>infinite (UNIV - (params_fm (f n) \<union> params (extend S f n)))\<close>
    by (metis Set_Diff_Un Un_commute finite_Diff2)
  with Suc consistent_witness[where S=\<open>{f n} \<union> extend S f n\<close>] show ?case
    by (simp add: Let_def)
qed (use assms(1) in simp)

lemma consistent_Extend:
  assumes \<open>consistent S\<close> and \<open>infinite (UNIV - params S)\<close>
  shows \<open>consistent (Extend S f)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> Extend S f \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>S' \<turnstile> \<^bold>\<bottom>\<close> and \<open>set S' \<subseteq> Extend S f\<close>
    unfolding consistent_def by blast
  then obtain m where \<open>set S' \<subseteq> (\<Union>n \<le> m. extend S f n)\<close>
    unfolding Extend_def using UN_finite_bound by (metis finite_set)
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
  unfolding maximal_def
proof safe
  fix p
  assume \<open>p \<notin> Extend S f\<close> and \<open>consistent ({p} \<union> Extend S f)\<close>
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

definition \<open>saturated S \<equiv> \<forall>p. \<^bold>\<not> (\<^bold>\<forall>p) \<in> S \<longrightarrow> (\<exists>a. (\<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p) \<in> S)\<close>

lemma saturated_Extend:
  assumes \<open>consistent (Extend S f)\<close> and \<open>surj f\<close>
  shows \<open>saturated (Extend S f)\<close>
  unfolding saturated_def
proof safe
  fix p
  assume *: \<open>\<^bold>\<not> (\<^bold>\<forall>p) \<in> Extend S f\<close>
  obtain k where k: \<open>f k = \<^bold>\<not> (\<^bold>\<forall>p)\<close>
    using \<open>surj f\<close> unfolding surj_def by metis
  have \<open>extend S f k \<subseteq> Extend S f\<close>
    unfolding Extend_def by auto
  then have \<open>consistent ({\<^bold>\<not> (\<^bold>\<forall>p)} \<union> extend S f k)\<close>
    using assms(1) * unfolding consistent_def by blast
  then have \<open>\<exists>a. extend S f (Suc k) = {\<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p} \<union> {\<^bold>\<not> (\<^bold>\<forall>p)} \<union> extend S f k\<close>
    using k by (auto simp: Let_def)
  moreover have \<open>extend S f (Suc k) \<subseteq> Extend S f\<close>
    unfolding Extend_def by blast
  ultimately show \<open>\<exists>a. \<^bold>\<not> \<langle>\<^bold>\<star> a/0\<rangle>p \<in> Extend S f\<close>
    by blast
qed

section \<open>Hintikka\<close>

locale Hintikka =
  fixes H :: \<open>('f, 'p) fm set\<close>
  assumes
    FlsH: \<open>\<^bold>\<bottom> \<notin> H\<close> and
    ImpH: \<open>(p \<^bold>\<longrightarrow> q) \<in> H \<longleftrightarrow> (p \<in> H \<longrightarrow> q \<in> H)\<close> and
    UniH: \<open>(\<^bold>\<forall>p \<in> H) \<longleftrightarrow> (\<forall>t. \<langle>t/0\<rangle>p \<in> H)\<close>

subsection \<open>Model Existence\<close>

abbreviation hmodel (\<open>\<lbrakk>_\<rbrakk>\<close>) where \<open>\<lbrakk>H\<rbrakk> \<equiv> \<lbrakk>\<^bold>#, \<^bold>\<dagger>, \<lambda>P ts. \<^bold>\<ddagger>P ts \<in> H\<rbrakk>\<close>

lemma semantics_tm_id [simp]: \<open>\<lparr>\<^bold>#, \<^bold>\<dagger>\<rparr> t = t\<close>
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
  then show ?case
    using assms unfolding Hintikka_def by (cases x) auto
qed

subsection \<open>Maximal Consistent Sets are Hintikka Sets\<close>

lemma deriv_iff_MCS:
  assumes \<open>consistent S\<close> and \<open>maximal S\<close>
  shows \<open>(\<exists>ps. set ps \<subseteq> S \<and> ps \<turnstile> p) \<longleftrightarrow> p \<in> S\<close>
proof
  from assms maximal_exactly_one[OF assms(1)] show \<open>\<exists>ps. set ps \<subseteq> S \<and> ps \<turnstile> p \<Longrightarrow> p \<in> S\<close>
    unfolding consistent_def using MP add_imply deduct1 imply.simps(1) imply_ImpE
    by (metis insert_absorb insert_mono list.simps(15))
next
  show \<open>p \<in> S \<Longrightarrow> \<exists>ps. set ps \<subseteq> S \<and> ps \<turnstile> p\<close>
    using imply_head by (metis empty_subsetI insert_absorb insert_mono list.set(1) list.simps(15))
qed

lemma Hintikka_Extend:
  assumes \<open>consistent H\<close> and \<open>maximal H\<close> and \<open>saturated H\<close>
  shows \<open>Hintikka H\<close>
proof
  show \<open>\<^bold>\<bottom> \<notin> H\<close>
    using assms deriv_iff_MCS unfolding consistent_def by fast
next
  fix p q
  show \<open>(p \<^bold>\<longrightarrow> q) \<in> H \<longleftrightarrow> (p \<in> H \<longrightarrow> q \<in> H)\<close>
    using deriv_iff_MCS[OF assms(1-2)] maximal_exactly_one[OF assms(1-2)]
    by (metis Imp1 contraposition add_imply deduct1 insert_subset list.simps(15))
next
  fix p
  show \<open>(\<^bold>\<forall>p \<in> H) \<longleftrightarrow> (\<forall>t. \<langle>t/0\<rangle>p \<in> H)\<close>
    using assms consistent_add_instance maximal_exactly_one
    unfolding maximal_def saturated_def by metis
qed

section \<open>Countable Formulas\<close>

instance tm :: (countable) countable
  by countable_datatype

instance fm :: (countable, countable) countable
  by countable_datatype

section \<open>Completeness\<close>

lemma infinite_Diff_fin_Un: \<open>infinite (X - Y) \<Longrightarrow> finite Z \<Longrightarrow> infinite (X - (Z \<union> Y))\<close>
  by (simp add: Set_Diff_Un Un_commute)

theorem strong_completeness:
  fixes p :: \<open>('f :: countable, 'p :: countable) fm\<close>
  assumes \<open>\<forall>(E :: _ \<Rightarrow> 'f tm) F G. (\<forall>q \<in> X. \<lbrakk>E, F, G\<rbrakk> q) \<longrightarrow> \<lbrakk>E, F, G\<rbrakk> p\<close>
    and \<open>infinite (UNIV - params X)\<close>
  shows \<open>\<exists>ps. set ps \<subseteq> X \<and> ps \<turnstile> p\<close>
proof (rule ccontr)
  assume \<open>\<nexists>ps. set ps \<subseteq> X \<and> ps \<turnstile> p\<close>
  then have *: \<open>\<nexists>ps. set ps \<subseteq> X \<and> ((\<^bold>\<not> p) # ps \<turnstile> \<^bold>\<bottom>)\<close>
    using Boole by blast

  let ?S = \<open>{\<^bold>\<not> p} \<union> X\<close>
  let ?H = \<open>Extend ?S from_nat\<close>

  from inconsistent_fm have \<open>consistent ?S\<close>
    unfolding consistent_def using * imply_Cons by metis
  moreover have \<open>infinite (UNIV - params ?S)\<close>
    using assms(2) finite_params_fm by (simp add: infinite_Diff_fin_Un)
  ultimately have \<open>consistent ?H\<close> and \<open>maximal ?H\<close>
    using consistent_Extend maximal_Extend surj_from_nat by blast+
  moreover from this have \<open>saturated ?H\<close>
    using saturated_Extend by fastforce
  ultimately have \<open>Hintikka ?H\<close>
    using assms(2) Hintikka_Extend by blast

  have \<open>\<lbrakk>?H\<rbrakk> p\<close> if \<open>p \<in> ?S\<close> for p
    using that Extend_subset Hintikka_model \<open>Hintikka ?H\<close> by blast
  then have \<open>\<lbrakk>?H\<rbrakk> (\<^bold>\<not> p)\<close> and \<open>\<forall>q \<in> X. \<lbrakk>?H\<rbrakk> q\<close>
    by blast+
  moreover from this have \<open>\<lbrakk>?H\<rbrakk> p\<close>
    using assms(1) by blast
  ultimately show False
    by simp
qed

theorem completeness:
  fixes p :: \<open>(nat, nat) fm\<close>
  assumes \<open>\<forall>(E :: nat \<Rightarrow> nat tm) F G. \<lbrakk>E, F, G\<rbrakk> p\<close>
  shows \<open>\<turnstile> p\<close>
  using assms strong_completeness[where X=\<open>{}\<close>] by auto

section \<open>Main Result\<close>

abbreviation valid :: \<open>(nat, nat) fm \<Rightarrow> bool\<close> where
  \<open>valid p \<equiv> \<forall>(E :: nat \<Rightarrow> nat tm) F G. \<lbrakk>E, F, G\<rbrakk> p\<close>

theorem main: \<open>valid p \<longleftrightarrow> (\<turnstile> p)\<close>
  using completeness soundness by blast

end
