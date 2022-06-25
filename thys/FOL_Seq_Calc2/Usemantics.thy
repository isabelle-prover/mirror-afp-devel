section \<open>Bounded semantics\<close>

theory Usemantics imports SeCaV begin

text \<open>In this theory, we define an alternative semantics for SeCaV formulas where the quantifiers
  are bounded to terms in a specific set.
  This is needed to construct a countermodel from a Hintikka set.\<close>

text \<open>This function defines the semantics, which are bounded by the set \<open>u\<close>.\<close>
primrec usemantics where
  \<open>usemantics u e f g (Pre i l) = g i (semantics_list e f l)\<close>
| \<open>usemantics u e f g (Imp p q) = (usemantics u e f g p \<longrightarrow> usemantics u e f g q)\<close>
| \<open>usemantics u e f g (Dis p q) = (usemantics u e f g p \<or> usemantics u e f g q)\<close>
| \<open>usemantics u e f g (Con p q) = (usemantics u e f g p \<and> usemantics u e f g q)\<close>
| \<open>usemantics u e f g (Exi p) = (\<exists>x \<in> u. usemantics u (SeCaV.shift e 0 x) f g p)\<close>
| \<open>usemantics u e f g (Uni p) = (\<forall>x \<in> u. usemantics u (SeCaV.shift e 0 x) f g p)\<close>
| \<open>usemantics u e f g (Neg p) = (\<not> usemantics u e f g p)\<close>

text \<open>An environment is well-formed if the variables are actually in the quantifier set \<open>u\<close>.\<close>
definition is_env :: \<open>'a set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool\<close> where
  \<open>is_env u e \<equiv> \<forall>n. e n \<in> u\<close>

text \<open>A function interpretation is well-formed if it is closed in the quantifier set \<open>u\<close>.\<close>
definition is_fdenot :: \<open>'a set \<Rightarrow> (nat \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> bool\<close> where
  \<open>is_fdenot u f \<equiv> \<forall>i l. list_all (\<lambda>x. x \<in> u) l \<longrightarrow> f i l \<in> u\<close>

text \<open>If we choose to quantify over the universal set, we obtain the usual semantics\<close>
lemma usemantics_UNIV: \<open>usemantics UNIV e f g p \<longleftrightarrow> semantics e f g p\<close>
  by (induct p arbitrary: e) auto

text \<open>If a function name \<open>n\<close> is not in a formula, it does not matter whether it is in
  the function interpretation or not.\<close>
lemma uupd_lemma [iff]: \<open>n \<notin> params p \<Longrightarrow> usemantics u e (f(n := x)) g p \<longleftrightarrow> usemantics u e f g p\<close>
  by (induct p arbitrary: e) simp_all

text \<open>The semantics of substituting variable i by term t in formula a are well-defined\<close>
lemma usubst_lemma [iff]:
  \<open>usemantics u e f g (subst a t i) \<longleftrightarrow> usemantics u (SeCaV.shift e i (semantics_term e f t)) f g a\<close>
  by (induct a arbitrary: e i t) simp_all

subsubsection \<open>Soundness of SeCaV with regards to the bounded semantics\<close>
text \<open>We would like to prove that the SeCaV proof system is sound under the bounded semantics.\<close>

text \<open>If the environment and the function interpretation are well-formed, the semantics of terms
  are in the quantifier set \<open>u\<close>.\<close>
lemma usemantics_term [simp]:
  assumes \<open>is_env u e\<close> \<open>is_fdenot u f\<close>
  shows \<open>semantics_term e f t \<in> u\<close> \<open>list_all (\<lambda>x. x \<in> u) (semantics_list e f ts)\<close>
  using assms by (induct t and ts rule: semantics_term.induct semantics_list.induct)
    (simp_all add: is_env_def is_fdenot_def)

text \<open>If a function interpretation is well-formed, replacing the value by one in the quantifier set
  results in a well-formed function interpretation.\<close>
lemma is_fdenot_shift [simp]: \<open>is_fdenot u f \<Longrightarrow> x \<in> u \<Longrightarrow> is_fdenot u (f(i := \<lambda>_. x))\<close>
  unfolding is_fdenot_def SeCaV.shift_def by simp

text \<open>If a sequent is provable in the SeCaV proof system and the environment
  and function interpretation are well-formed, the sequent is valid under the bounded semantics.\<close>
theorem sound_usemantics:
  assumes \<open>\<tturnstile> z\<close> and \<open>is_env u e\<close> and \<open>is_fdenot u f\<close>
  shows \<open>\<exists>p \<in> set z. usemantics u e f g p\<close>
  using assms
proof (induct arbitrary: f rule: sequent_calculus.induct)
  case (10 i p z)
  then show ?case
  proof (cases \<open>\<forall>x \<in> u. usemantics u e (f(i := \<lambda>_. x)) g (sub 0 (Fun i []) p)\<close>)
    case False
    moreover have \<open>\<forall>x \<in> u. \<exists>p \<in> set (sub 0 (Fun i []) p # z). usemantics u e (f(i := \<lambda>_. x)) g p\<close>
      using 10 is_fdenot_shift by metis
    ultimately have \<open>\<exists>x \<in> u. \<exists>p \<in> set z. usemantics u e (f(i := \<lambda>_. x)) g p\<close>
      by fastforce
    moreover have \<open>list_all (\<lambda>p. i \<notin> params p) z\<close>
      using 10 by simp
    ultimately show ?thesis
      using 10 Ball_set insert_iff list.set(2) uupd_lemma by metis
  qed simp
next
  case (11 i p z)
  then show ?case
  proof (cases \<open>\<forall>x \<in> u. usemantics u e (f(i := \<lambda>_. x)) g (Neg (sub 0 (Fun i []) p))\<close>)
    case False
    moreover have
      \<open>\<forall>x \<in> u. \<exists>p \<in> set (Neg (sub 0 (Fun i []) p) # z). usemantics u e (f(i := \<lambda>_. x)) g p\<close>
      using 11 is_fdenot_shift by metis
    ultimately have \<open>\<exists>x \<in> u. \<exists>p \<in> set z. usemantics u e (f(i := \<lambda>_. x)) g p\<close>
      by fastforce
    moreover have \<open>list_all (\<lambda>p. i \<notin> params p) z\<close>
      using 11 by simp
    ultimately show ?thesis
      using 11 Ball_set insert_iff list.set(2) uupd_lemma by metis
  qed simp
qed fastforce+

end
