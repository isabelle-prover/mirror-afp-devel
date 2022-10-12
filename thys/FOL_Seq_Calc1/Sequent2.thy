theory Sequent2 imports Sequent begin

section \<open>Completeness Revisited\<close>

lemma \<open>\<exists>p. q = compl p\<close>
  by (metis compl.simps(1))

definition compl' where
  \<open>compl' = (\<lambda>q. (SOME p. q = compl p))\<close>

lemma comp'_sem:
  \<open>eval e f g (compl' p) \<longleftrightarrow> \<not> eval e f g p\<close>
  by (smt compl'_def compl.simps(1) compl eval.simps(7) someI_ex)

lemma comp'_sem_list: \<open>list_ex (\<lambda>p. \<not> eval e f g p) (map compl' ps) \<longleftrightarrow> list_ex (eval e f g) ps\<close>
  by (induct ps) (use comp'_sem in auto)

theorem SC_completeness':
  fixes ps :: \<open>(nat, nat) form list\<close>
  assumes \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. list_ex (eval e f g) (p # ps)\<close>
  shows \<open>\<turnstile> p # ps\<close>
proof -
  define ps' where \<open>ps' = map compl' ps\<close>
  then have \<open>ps = map compl ps'\<close>
    by (induct ps arbitrary: ps') (simp, smt compl'_def compl.simps(1) list.simps(9) someI_ex)
  from assms have \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. (list_ex (eval e f g) ps) \<or> eval e f g p\<close>
    by auto
  then have \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. (list_ex (\<lambda>p. \<not> eval e f g p) ps') \<or> eval e f g p\<close>
    unfolding ps'_def using comp'_sem_list by blast
  then have \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. list_all (eval e f g) ps' \<longrightarrow> eval e f g p\<close>
    by (metis Ball_set Bex_set)
  then have \<open>\<turnstile> p # map compl ps'\<close>
    using SC_completeness by blast
  then show ?thesis
    using \<open>ps = map compl ps'\<close> by auto
qed

corollary
  fixes ps :: \<open>(nat, nat) form list\<close>
  assumes \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. list_ex (eval e f g) ps\<close>
  shows \<open>\<turnstile> ps\<close>
  using assms SC_completeness' by (cases ps) auto

end
