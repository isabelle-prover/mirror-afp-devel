(*
  File:      Stalnaker_Logic.thy
  Author:    Laura Gamboa Guzman

  This work is a formalization of Stalnaker's epistemic logic
  and its soundness and completeness theorems, as well as the 
  equivalence between the axiomatization of S4 available in the Epistemic 
  Logic theory and the topological one.
  It builds on the Epistemic_Logic theory by A.H. From.
*)

theory Stalnaker_Logic
  imports "Epistemic_Logic.Epistemic_Logic"

begin


section \<open>Utility\<close>

subsection \<open>Some properties of Normal Modal Logics\<close>

lemma duality_taut: \<open>tautology (((K i p) \<^bold>\<longrightarrow> K i (\<^bold>\<not>q))\<^bold>\<longrightarrow> ((L i q) \<^bold>\<longrightarrow> (\<^bold>\<not> K i p)))\<close>
  by force

lemma K_imp_trans: 
  assumes \<open>A \<turnstile> (p \<^bold>\<longrightarrow> q)\<close>  \<open>A \<turnstile> (q \<^bold>\<longrightarrow> r)\<close>
  shows  \<open>A \<turnstile> (p \<^bold>\<longrightarrow> r)\<close>
proof - 
  have \<open>tautology  ((p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> ( (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow>  (p \<^bold>\<longrightarrow> r)))\<close>
    by fastforce
  then show ?thesis
    by (meson A1 R1 assms(1) assms(2))
qed

lemma K_imp_trans': 
  assumes \<open>A \<turnstile> (q \<^bold>\<longrightarrow> r)\<close>
  shows  \<open>A \<turnstile> ((p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> r))\<close>
proof - 
  have \<open>tautology  ((q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> ((p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> r)))\<close>
    by fastforce
  then show ?thesis 
    using A1 R1 assms by blast
qed

lemma K_imply_multi:
  assumes \<open>A \<turnstile> (a \<^bold>\<longrightarrow> b)\<close> and \<open>A \<turnstile> (a \<^bold>\<longrightarrow> c)\<close>
  shows \<open>A \<turnstile> (a \<^bold>\<longrightarrow> (b\<^bold>\<and>c))\<close>
proof -
  have \<open>tautology ((a\<^bold>\<longrightarrow>b)\<^bold>\<longrightarrow>(a\<^bold>\<longrightarrow>c)\<^bold>\<longrightarrow>(a\<^bold>\<longrightarrow>(b\<^bold>\<and>c)))\<close>
    by force
  then have \<open>A \<turnstile> ((a\<^bold>\<longrightarrow>b)\<^bold>\<longrightarrow>(a\<^bold>\<longrightarrow>c)\<^bold>\<longrightarrow>(a\<^bold>\<longrightarrow>(b\<^bold>\<and>c)))\<close>
    using A1 by blast
  then have \<open>A \<turnstile> ((a\<^bold>\<longrightarrow>c)\<^bold>\<longrightarrow>(a\<^bold>\<longrightarrow>(b\<^bold>\<and>c)))\<close>
    using assms(1) R1 by blast
  then show ?thesis 
    using assms(2) R1 by blast
qed

lemma K_multi_imply:
  assumes \<open>A \<turnstile> (a \<^bold>\<longrightarrow> b \<^bold>\<longrightarrow> c)\<close>
  shows \<open>A \<turnstile> ((a\<^bold>\<and>b) \<^bold>\<longrightarrow> c)\<close>
proof - 
  have \<open>tautology ((a \<^bold>\<longrightarrow> b \<^bold>\<longrightarrow> c) \<^bold>\<longrightarrow> ((a\<^bold>\<and>b) \<^bold>\<longrightarrow> c))\<close>
    by force
  then have \<open>A \<turnstile> ((a \<^bold>\<longrightarrow> b \<^bold>\<longrightarrow> c) \<^bold>\<longrightarrow> ((a\<^bold>\<and>b) \<^bold>\<longrightarrow> c))\<close>
    using A1 by blast
  then show ?thesis
    using assms R1 by blast 
qed

lemma K_thm: \<open>A \<turnstile> ((K i p) \<^bold>\<and> (L i q) \<^bold>\<longrightarrow> L i (p \<^bold>\<and> q))\<close>
proof -
  have \<open>tautology (p \<^bold>\<longrightarrow> (\<^bold>\<not>(p \<^bold>\<and> q)) \<^bold>\<longrightarrow> \<^bold>\<not> q)\<close>
    by force
  then have \<open>A \<turnstile> (p \<^bold>\<longrightarrow> (\<^bold>\<not>(p \<^bold>\<and> q)) \<^bold>\<longrightarrow> \<^bold>\<not> q)\<close>
    by (simp add: A1)
  then have \<open>A \<turnstile> ((K i p) \<^bold>\<longrightarrow> K i ((\<^bold>\<not>(p \<^bold>\<and> q)) \<^bold>\<longrightarrow> \<^bold>\<not> q))\<close> 
        and \<open>A \<turnstile> (K i ((\<^bold>\<not>(p \<^bold>\<and> q)) \<^bold>\<longrightarrow> \<^bold>\<not> q) \<^bold>\<longrightarrow> K i (\<^bold>\<not>(p \<^bold>\<and> q)) \<^bold>\<longrightarrow> K i (\<^bold>\<not> q))\<close>
     apply (simp add: K_map)
    by (meson K_A2')
  then have \<open>A \<turnstile> ((K i p) \<^bold>\<longrightarrow> K i (\<^bold>\<not>(p \<^bold>\<and> q)) \<^bold>\<longrightarrow> K i (\<^bold>\<not> q))\<close> 
    using K_imp_trans by blast
  then have \<open>A \<turnstile> ((K i p) \<^bold>\<longrightarrow> L i (q) \<^bold>\<longrightarrow> L i (p \<^bold>\<and> q))\<close> 
    by (metis AK.simps K_imp_trans duality_taut)
  then show ?thesis
    by (simp add: K_multi_imply)
qed

primrec conjunct :: \<open>'i fm list \<Rightarrow> 'i fm\<close> where
  \<open>conjunct [] = \<^bold>\<top>\<close>
| \<open>conjunct (p#ps) = (p \<^bold>\<and> conjunct ps)\<close>

lemma imply_conjunct: \<open>tautology ((imply G p) \<^bold>\<longrightarrow> ((conjunct G) \<^bold>\<longrightarrow> p))\<close>
  apply(induction G) 
  apply simp
  by force

lemma conjunct_imply: \<open>tautology (((conjunct G) \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow>(imply G p))\<close>
  by (induct G) simp_all

lemma K_imply_conjunct:
  assumes \<open>A \<turnstile> imply G p\<close>
  shows \<open>A \<turnstile> ((conjunct G) \<^bold>\<longrightarrow> p)\<close>
  using A1 R1 assms imply_conjunct by blast

lemma K_conjunct_imply:
  assumes \<open>A \<turnstile> ((conjunct G) \<^bold>\<longrightarrow> p)\<close>
  shows \<open>A \<turnstile> imply G p\<close>
  using A1 R1 assms conjunct_imply by blast

lemma K_conj_imply_factor: 
  fixes A :: \<open>('i fm \<Rightarrow> bool)\<close>  
  shows \<open>A \<turnstile> ((((K i p) \<^bold>\<and> (K i q)) \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow>((K i (p \<^bold>\<and> q)) \<^bold>\<longrightarrow> r))\<close>
proof -
  have *: \<open>A \<turnstile> ((K i (p \<^bold>\<and> q)) \<^bold>\<longrightarrow> ((K i p) \<^bold>\<and> (K i q)))\<close>
  proof (rule ccontr) 
    assume \<open>\<not> A \<turnstile> ((K i (p \<^bold>\<and> q)) \<^bold>\<longrightarrow> ((K i p) \<^bold>\<and> (K i q)))\<close>
    then have \<open>consistent A {\<^bold>\<not>((K i (p \<^bold>\<and> q)) \<^bold>\<longrightarrow> ((K i p) \<^bold>\<and> (K i q)))}\<close>
      by (metis imply.simps(1) inconsistent_imply insert_is_Un list.set(1))
    let ?V = \<open>Extend A {\<^bold>\<not>((K i (p \<^bold>\<and> q)) \<^bold>\<longrightarrow> ((K i p) \<^bold>\<and> (K i q)))}\<close> 
    let ?M = \<open>\<lparr>\<W> = mcss A, \<K> = reach A, \<pi> = pi\<rparr>\<close> 
    have \<open>?V \<in> \<W> ?M \<and> ?M, ?V \<Turnstile> \<^bold>\<not>((K i (p \<^bold>\<and> q)) \<^bold>\<longrightarrow> ((K i p) \<^bold>\<and> (K i q)))\<close>
      using canonical_model \<open>consistent A {\<^bold>\<not> (K i (p \<^bold>\<and> q) \<^bold>\<longrightarrow> K i p \<^bold>\<and> K i q)}\<close> 
            insert_iff mem_Collect_eq by fastforce
    then have o: \<open>?M, ?V \<Turnstile> ((K i (p \<^bold>\<and> q)) \<^bold>\<and> \<^bold>\<not>((K i p) \<^bold>\<and> (K i q)))\<close>
      by auto
    then have \<open>?M, ?V \<Turnstile> (K i (p \<^bold>\<and> q))\<close> \<open>(?M, ?V \<Turnstile> \<^bold>\<not>(K i p)) \<or> (?M, ?V \<Turnstile> \<^bold>\<not>(K i q))\<close>
      by auto
    then have \<open>\<forall> U \<in> \<W> ?M \<inter> \<K> ?M i ?V. ?M, U \<Turnstile>(p \<^bold>\<and> q)\<close>
              \<open>\<exists> U \<in> \<W> ?M \<inter> \<K> ?M i ?V. ?M, U \<Turnstile> ((\<^bold>\<not>p) \<^bold>\<or> (\<^bold>\<not>q))\<close>
      using o by auto
    then show False 
      by simp
  qed
  then have \<open>A \<turnstile> (((K i (p \<^bold>\<and> q)) \<^bold>\<longrightarrow> ((K i p) \<^bold>\<and> (K i q))) \<^bold>\<longrightarrow>
                   ((((K i p) \<^bold>\<and> (K i q)) \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> ((K i (p \<^bold>\<and> q)) \<^bold>\<longrightarrow> r)))\<close>
    by (simp add: A1)
  then show ?thesis 
    using "*" R1 by blast
qed

lemma K_conjunction_in: \<open>A \<turnstile> (K i (p \<^bold>\<and> q) \<^bold>\<longrightarrow> ((K i p) \<^bold>\<and> K i q))\<close>
proof -
  have o1: \<open>A \<turnstile> ((p\<^bold>\<and>q) \<^bold>\<longrightarrow> p)\<close> and o2: \<open>A \<turnstile> ((p\<^bold>\<and>q) \<^bold>\<longrightarrow> q)\<close>
    apply(simp add: A1)
    by (simp add: A1)
  then have c1: \<open>A \<turnstile> (K i (p \<^bold>\<and> q) \<^bold>\<longrightarrow> K i q)\<close> and c2: \<open>A \<turnstile> (K i (p \<^bold>\<and> q) \<^bold>\<longrightarrow> K i p)\<close> 
    apply (simp add: K_map o2)
    by (simp add: K_map o1)
  then show ?thesis
    by (simp add: K_imply_multi)
qed

lemma K_conjunction_in_mult:  \<open>A \<turnstile> ((K i (conjunct G)) \<^bold>\<longrightarrow> conjunct (map (K i) G))\<close>
proof (induct G)
  case Nil
  then show ?case
    by (simp add: A1)
  case (Cons a G)
  then have \<open>A \<turnstile> ((K i (conjunct (a#G))) \<^bold>\<longrightarrow> (K i (a \<^bold>\<and> conjunct G)))\<close>
        and  \<open>A \<turnstile> ((K i (a \<^bold>\<and> conjunct G)) \<^bold>\<longrightarrow> ((K i a) \<^bold>\<and> K i (conjunct G)))\<close>
    apply (simp add: A1)
    by (metis K_conjunction_in)
  then have o1: \<open>A \<turnstile> ((K i (conjunct (a#G))) \<^bold>\<longrightarrow> ((K i a) \<^bold>\<and> K i (conjunct G)))\<close>
    using K_imp_trans by blast
  then have \<open>A \<turnstile> (((K i a) \<^bold>\<and> K i (conjunct G)) \<^bold>\<longrightarrow> K i a)\<close> 
        and o2: \<open>A \<turnstile> (((K i a) \<^bold>\<and> K i (conjunct G)) \<^bold>\<longrightarrow> conjunct (map (K i) G))\<close>
    apply (simp add: A1)
    by (metis Cons.hyps K_imply_Cons K_multi_imply imply.simps(1) imply.simps(2))
  then have \<open>A \<turnstile> (((K i a) \<^bold>\<and> K i (conjunct G)) \<^bold>\<longrightarrow> (K i a) \<^bold>\<and> conjunct (map (K i) G))\<close>
    using K_imply_multi by blast
  then show ?case 
    using K_imp_trans o1 by auto
qed

lemma K_conjunction_out: \<open>A \<turnstile> ((K i p) \<^bold>\<and> (K i q) \<^bold>\<longrightarrow> K i (p \<^bold>\<and> q))\<close>
proof -
  have \<open>A \<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p\<^bold>\<and>q)\<close>
    by (simp add: A1)
  then have \<open>A \<turnstile> K i (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p\<^bold>\<and>q)\<close>
    by (simp add: R2)
  then have \<open>A \<turnstile> ((K i p) \<^bold>\<longrightarrow> K i (q \<^bold>\<longrightarrow> p\<^bold>\<and>q))\<close>
    by (simp add: K_map \<open>A \<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p \<^bold>\<and> q)\<close>)
  then have \<open>A \<turnstile> ((K i p) \<^bold>\<longrightarrow> (K i q) \<^bold>\<longrightarrow> K i (p\<^bold>\<and>q))\<close>
    by (meson K_A2' K_imp_trans)
  then show ?thesis
    using K_multi_imply by blast
qed

lemma K_conjunction_out_mult: \<open>A \<turnstile> (conjunct (map (K i) G) \<^bold>\<longrightarrow> (K i (conjunct G)))\<close>
proof (induct G)
  case Nil
  then show ?case
    by (metis A1 K_imply_conjunct Nil_is_map_conv R2 conjunct.simps(1) eval.simps(5) imply.simps(1))
  case (Cons a G)
  then have \<open>A \<turnstile> ((conjunct (map (K i) (a#G))) \<^bold>\<longrightarrow> ((K i a) \<^bold>\<and> conjunct (map (K i) G)))\<close>
    by (simp add: A1)
  then have *: \<open>A \<turnstile> (((K i a) \<^bold>\<and> conjunct (map (K i) G))\<^bold>\<longrightarrow> (K i a) \<^bold>\<and> K i (conjunct G))\<close>
    by (metis Cons.hyps K_imply_Cons K_imply_head K_imply_multi K_multi_imply imply.simps(1) imply.simps(2))
  then have \<open>A \<turnstile> (((K i a) \<^bold>\<and> K i (conjunct G))\<^bold>\<longrightarrow> K i (conjunct (a#G)))\<close>
    by (simp add: K_conjunction_out)
  then show ?case
    using "*" K_imp_trans by auto
qed

subsection \<open>More on mcs's properties\<close>

lemma mcs_conjunction: 
  assumes \<open>consistent A V\<close> and \<open>maximal A V\<close> 
  shows \<open>p \<in> V \<and> q \<in> V \<longrightarrow> (p \<^bold>\<and> q) \<in> V\<close>
proof - 
  have \<open>tautology (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> (p\<^bold>\<and>q))\<close>
    by force  
  then have \<open>(p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> (p\<^bold>\<and>q)) \<in> V\<close>
    using A1 assms(1) assms(2) deriv_in_maximal by blast
  then have \<open>p \<in> V \<longrightarrow> (q \<^bold>\<longrightarrow> (p\<^bold>\<and>q)) \<in> V\<close>
    by (meson assms(1) assms(2) consequent_in_maximal)
  then show ?thesis
    using assms(1) assms(2) consequent_in_maximal by blast
qed

lemma mcs_conjunction_mult: 
 assumes \<open>consistent A V\<close> and \<open>maximal A V\<close> 
  shows \<open>(set (S :: ('i fm list)) \<subseteq> V \<and> finite (set S)) \<longrightarrow> (conjunct S) \<in> V\<close>
proof(induct S)
  case Nil
  then show ?case
    by (metis K_Boole assms(1) assms(2) conjunct.simps(1) consistent_def inconsistent_subset maximal_def)
  case (Cons a S)
  then have \<open>set S \<subseteq> set (a#S)\<close>
    by (meson set_subset_Cons)
  then have c1: \<open> set (a # S) \<subseteq> V \<and> finite (set (a # S)) \<longrightarrow> conjunct (S) \<in> V \<and> a \<in> V\<close>
    using Cons by fastforce
  then have \<open> conjunct (S) \<in> V \<and> a \<in> V \<longrightarrow> (conjunct (a#S)) \<in> V \<close>
    using assms(1) assms(2) mcs_conjunction by auto
  then show ?case
    using c1 by fastforce
qed

lemma reach_dualK: 
  assumes \<open>consistent A V\<close> \<open>maximal A V\<close>
    and \<open>consistent A W\<close> \<open>maximal A W\<close> \<open>W \<in> reach A i V\<close>
  shows \<open>\<forall>p. p \<in> W \<longrightarrow> (L i p) \<in> V\<close>
proof (rule ccontr)
  assume \<open>\<not> (\<forall>p. p \<in> W \<longrightarrow> (L i p) \<in> V)\<close>
  then obtain p' where *: \<open>p' \<in> W \<and> (L i p') \<notin> V\<close>
    by presburger
  then have \<open>(\<^bold>\<not> L i p') \<in> V\<close>
    using assms(1) assms(2) assms(3) assms(4) assms(5) exactly_one_in_maximal by blast
  then have \<open>K i (\<^bold>\<not> p') \<in> V\<close>
    using assms(1) assms(2) exactly_one_in_maximal by blast
  then have \<open>(\<^bold>\<not> p') \<in> W\<close>
    using assms(5) by blast
  then show False
    by (meson "*" assms(3) assms(4) exactly_one_in_maximal)
qed 

lemma dual_reach: 
  assumes \<open>consistent A V\<close> \<open>maximal A V\<close> 
  shows \<open>(L i p) \<in> V \<longrightarrow> (\<exists> W. W \<in> reach A i V \<and> p \<in> W)\<close>
proof -
  have \<open>(\<nexists>W. W \<in> {W. known V i \<subseteq> W} \<and> p \<in> W) \<longrightarrow> (\<forall>W. W \<in> {W. known V i \<subseteq> W} \<longrightarrow> (\<^bold>\<not>p) \<in> W)\<close>
    by blast
  then have \<open>(\<forall>W. W \<in> {W. known V i \<subseteq> W} \<longrightarrow> (\<^bold>\<not>p) \<in> W) \<longrightarrow> (\<forall> W. W \<in> reach A i V \<longrightarrow> (\<^bold>\<not>p) \<in> W)\<close>
    by fastforce
  then have \<open>(\<forall> W. W \<in> reach A i V \<longrightarrow> (\<^bold>\<not>p) \<in> W) \<longrightarrow> ((K i (\<^bold>\<not>p)) \<in> V)\<close>
    by blast
  then have \<open>((K i (\<^bold>\<not>p)) \<in> V) \<longrightarrow> (\<not>((L i p) \<in> V))\<close>
    using assms(1) assms(2) exactly_one_in_maximal by blast
  then have \<open>(\<nexists>W. W \<in> {W. known V i \<subseteq> W} \<and> p \<in> W) \<longrightarrow> \<not>((L i p) \<in> V)\<close> 
    by blast
  then show ?thesis
    by blast
qed


section  \<open>Ax.2\<close>

definition weakly_directed :: \<open>('i, 's) kripke \<Rightarrow> bool\<close> where
  \<open>weakly_directed M \<equiv> \<forall>i. \<forall>s \<in> \<W> M. \<forall>t \<in> \<W> M. \<forall>r \<in> \<W> M.
     (r \<in> \<K> M i s \<and> t \<in> \<K> M i s)\<longrightarrow>(\<exists> u \<in> \<W> M. (u \<in> \<K> M i r \<and> u \<in> \<K> M i t))\<close>

inductive Ax_2 :: \<open>'i fm \<Rightarrow> bool\<close> where 
  \<open>Ax_2 (\<^bold>\<not> K i (\<^bold>\<not> K i p) \<^bold>\<longrightarrow> K i (\<^bold>\<not> K i (\<^bold>\<not> p)))\<close> 

subsection \<open>Soundness\<close>

theorem weakly_directed:
  assumes \<open>weakly_directed M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>M, w \<Turnstile> (L i (K i p) \<^bold>\<longrightarrow> K i (L i p))\<close>
proof 
  assume \<open>M, w \<Turnstile> (L i (K i p))\<close>
  then have \<open>\<exists>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> K i p\<close> 
    by simp
  then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. \<exists>u \<in> \<W> M \<inter> \<K> M i v. M, u \<Turnstile> p\<close>
    using \<open>weakly_directed M\<close> \<open>w \<in> \<W> M\<close> unfolding weakly_directed_def
    by (metis IntE IntI semantics.simps(6)) 
  then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> L i p\<close>
    by simp
  then show \<open>M, w \<Turnstile> K i (L i p)\<close>
    by simp
qed

lemma soundness_Ax_2: \<open>Ax_2 p \<Longrightarrow> weakly_directed M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  by (induct p rule: Ax_2.induct) (meson weakly_directed)

subsection \<open>Imply completeness\<close>

lemma Ax_2_weakly_directed:
  fixes A :: \<open>'i fm \<Rightarrow> bool\<close>
  assumes \<open>\<forall>p. Ax_2 p \<longrightarrow> A p\<close> \<open>consistent A V\<close> \<open>maximal A V\<close>
    and \<open>consistent A W\<close> \<open>maximal A W\<close> \<open>consistent A U\<close> \<open>maximal A U\<close>
    and \<open>W \<in> reach A i V\<close> \<open>U \<in> reach A i V\<close>
  shows \<open>\<exists>X. (consistent A X) \<and> (maximal A X) \<and> X \<in> (reach A i W) \<inter> (reach A i U)\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  let ?S = \<open>(known W i) \<union> (known U i)\<close>
  have \<open>\<not> consistent A ?S\<close> 
    by (smt (verit, best) Int_Collect \<open>\<nexists>X. consistent A X \<and> maximal A X \<and> X \<in> {Wa. known W i \<subseteq> Wa} \<inter> {W. known U i \<subseteq> W}\<close> maximal_extension mem_Collect_eq sup.bounded_iff)
  then obtain S' where *: \<open>A \<turnstile> imply S' \<^bold>\<bottom>\<close> \<open>set S' \<subseteq> ?S\<close> \<open>finite (set S')\<close>
    unfolding consistent_def by blast 
  let ?U = \<open>filter (\<lambda>p. p \<in> (known U i)) S'\<close>
  let ?W = \<open>filter (\<lambda>p. p \<in> (known W i)) S'\<close>
  let ?p = \<open>conjunct ?U\<close> and ?q = \<open>conjunct ?W\<close>
  have \<open>(set ?U) \<union> (set ?W) = (set S')\<close>
    using * by auto
  then have \<open>A \<turnstile> imply ?U (imply ?W \<^bold>\<bottom>)\<close>
    using K_imply_weaken imply_append  
    by (metis (mono_tags, lifting) "*"(1) set_append subset_refl) 
  then have \<open>A \<turnstile> (?p \<^bold>\<longrightarrow> (imply ?W \<^bold>\<bottom>))\<close>
    using K_imply_conjunct by blast
  then have \<open>tautology ((imply ?W \<^bold>\<bottom>) \<^bold>\<longrightarrow> (?q \<^bold>\<longrightarrow> \<^bold>\<bottom>))\<close>
    using imply_conjunct by blast
  then have \<open>A \<turnstile> ((imply ?W \<^bold>\<bottom>) \<^bold>\<longrightarrow> (?q \<^bold>\<longrightarrow> \<^bold>\<bottom>))\<close>
    using A1 by blast
  then have \<open>A \<turnstile> (?p \<^bold>\<longrightarrow> (?q \<^bold>\<longrightarrow> \<^bold>\<bottom>))\<close>
    using K_imp_trans \<open>A \<turnstile> (conjunct (filter (\<lambda>p. p \<in> known U i) S') \<^bold>\<longrightarrow> imply (filter (\<lambda>p. p \<in> known W i) S') \<^bold>\<bottom>)\<close>
    by blast 
  then have o1: \<open>A \<turnstile> ((?p \<^bold>\<and> ?q) \<^bold>\<longrightarrow> \<^bold>\<bottom>)\<close>
    by (meson K_multi_imply)
  moreover have \<open>set ?U \<subseteq> (known U i)\<close> and \<open>set ?W \<subseteq> (known W i)\<close> 
                and \<open>\<forall> p. p \<in> set ?U \<longrightarrow> (K i p) \<in> U\<close> and \<open>\<forall> p. p \<in> set ?W \<longrightarrow> (K i p) \<in> W\<close> 
    by auto
  then have \<open>set (map (K i) ?U) \<subseteq> U\<close> and c1: \<open>set (map (K i) ?W) \<subseteq> W\<close>
     apply (metis (mono_tags, lifting) imageE set_map subsetI) 
    by auto
  then have c2: \<open>conjunct (map (K i) ?U) \<in> U\<close> and c2': \<open>conjunct (map (K i) ?W) \<in> W\<close>
    using assms(6) assms(7) mcs_conjunction_mult apply blast
    using assms(4) assms(5) c1 mcs_conjunction_mult by blast
  then have \<open>((conjunct (map (K i) ?U)) \<^bold>\<longrightarrow> (K i ?p)) \<in> U\<close> 
        and c3: \<open>((conjunct (map (K i) ?W)) \<^bold>\<longrightarrow> (K i ?q)) \<in> W\<close> 
    apply (meson K_conjunction_out_mult assms(6) assms(7) deriv_in_maximal)
    by (meson K_conjunction_out_mult assms(4) assms(5) deriv_in_maximal)
  then have c4: \<open>(K i ?p) \<in> U\<close> and c4': \<open>(K i ?q) \<in> W\<close>
    using assms(6) assms(7) c2 consequent_in_maximal apply blast
    using assms(4) assms(5) c2' c3 consequent_in_maximal by blast
  then have \<open>(L i (K i ?p)) \<in> V\<close> and c5: \<open>(L i (K i ?q)) \<in> V\<close> 
    using assms(2) assms(3) assms(6) assms(7) assms(9) exactly_one_in_maximal apply blast
    using assms(2) assms(3) assms(4) assms(5) assms(8) c4' exactly_one_in_maximal by blast
  then have \<open>(K i (L i ?p)) \<in> V\<close>
    by (meson Ax_2.intros assms(1) assms(2) assms(3) ax_in_maximal consequent_in_maximal)
  then have \<open>((K i (L i ?p)) \<^bold>\<and> (L i (K i ?q))) \<in> V\<close>
    using assms(2) assms(3) c5 mcs_conjunction by blast
  then have \<open>(L i ((L i ?p) \<^bold>\<and> K i ?q)) \<in> V\<close>
    by (meson K_thm assms(2) assms(3) consequent_in_maximal deriv_in_maximal)
  then have \<open>(L i ((K i ?q) \<^bold>\<and> L i ?p)) \<in> V\<close>
    by (smt (z3) \<open>K i (L i (conjunct (filter (\<lambda>p. p \<in> known U i) S'))) \<in> V\<close> assms(2) assms(3) assms(4) assms(5) assms(8) c4' exactly_one_in_maximal mcs_conjunction mem_Collect_eq subset_iff)
  then obtain Z' where z1:\<open>(consistent A Z') \<and> (maximal A Z')\<close> and z2:\<open>Z' \<in> (reach A i V)\<close> 
                  and z3: \<open>((K i ?q) \<^bold>\<and> L i ?p) \<in> Z'\<close>
    using \<open>K i (L i (conjunct (filter (\<lambda>p. p \<in> known U i) S'))) \<in> V\<close> assms(4) assms(5) assms(8) c4' mcs_conjunction by blast
  then have z4: \<open>(L i (?q \<^bold>\<and> ?p)) \<in> Z'\<close>
    by (metis K_thm consequent_in_maximal deriv_in_maximal)
  then have o2:\<open>(L i (L i (?q \<^bold>\<and> ?p))) \<in> V\<close>
    using assms(2) assms(3) mcs_properties(2) z1 z2 by blast
  then have \<open>A \<turnstile> K i (K i (((?p \<^bold>\<and> ?q) \<^bold>\<longrightarrow> \<^bold>\<bottom>)))\<close> 
    by (metis R2 o1)
  then have o3:\<open>K i (K i (((?p \<^bold>\<and> ?q) \<^bold>\<longrightarrow> \<^bold>\<bottom>))) \<in> V\<close>
    using assms(2) assms(3) deriv_in_maximal by blast
  then obtain X1 where x1:\<open>(consistent A X1) \<and> (maximal A X1)\<close> and x2:\<open>X1 \<in> (reach A i V)\<close> 
                  and x3: \<open>(L i (?q \<^bold>\<and> ?p)) \<in> X1\<close>
    using z1 z2 z4 by blast
  then have x4:\<open>(K i (((?p \<^bold>\<and> ?q) \<^bold>\<longrightarrow> \<^bold>\<bottom>))) \<in> X1\<close>
    using o3 by blast
  then have t:\<open>\<forall>x. \<forall>y. tautology (((x\<^bold>\<and>y)\<^bold>\<longrightarrow>\<^bold>\<bottom>)\<^bold>\<longrightarrow>\<^bold>\<not>(y\<^bold>\<and>x))\<close>
    by (metis eval.simps(4) eval.simps(5))
  then have \<open>(((?p\<^bold>\<and>?q)\<^bold>\<longrightarrow>\<^bold>\<bottom>)\<^bold>\<longrightarrow>\<^bold>\<not>(?q\<^bold>\<and>?p)) \<in> X1\<close>
    using A1 deriv_in_maximal x1 by blast
  then have \<open>K i (((?p\<^bold>\<and>?q)\<^bold>\<longrightarrow>\<^bold>\<bottom>)\<^bold>\<longrightarrow>\<^bold>\<not>(?q\<^bold>\<and>?p)) \<in> X1\<close>
    by (meson A1 R2 deriv_in_maximal t x1)
  then have \<open>(K i ((?p\<^bold>\<and>?q)\<^bold>\<longrightarrow>\<^bold>\<bottom>)\<^bold>\<longrightarrow> K i (\<^bold>\<not>(?q\<^bold>\<and>?p))) \<in> X1\<close>
    by (meson K_A2' consequent_in_maximal deriv_in_maximal x1)
  then have \<open>(K i ((?p\<^bold>\<and>?q)\<^bold>\<longrightarrow>\<^bold>\<bottom>)\<^bold>\<longrightarrow> (\<^bold>\<not> L i(?q\<^bold>\<and>?p))) \<in> X1\<close>
    using consequent_in_maximal exactly_one_in_maximal x1 x3 x4 by blast
  then have \<open>(\<^bold>\<not> L i(?q\<^bold>\<and>?p)) \<in> X1 \<and> (L i(?q\<^bold>\<and>?p)) \<in> X1\<close>
    using consequent_in_maximal x1 x4 x3 by blast
  then show False
    using exactly_one_in_maximal x1 by blast
qed

lemma mcs\<^sub>_\<^sub>2_weakly_directed:
  fixes A :: \<open>'i fm \<Rightarrow> bool\<close>
  assumes \<open>\<forall>p. Ax_2 p \<longrightarrow> A p\<close>
  shows \<open>weakly_directed \<lparr>\<W> = mcss A, \<K> = reach A, \<pi> = pi\<rparr>\<close>
  unfolding weakly_directed_def
proof (intro allI ballI, auto)
  fix i V U W
  assume \<open>consistent A V\<close> \<open>maximal A V\<close> \<open>consistent A U\<close> \<open>maximal A U\<close> \<open>consistent A W\<close> 
      \<open>maximal A W\<close> \<open>known V i \<subseteq> U\<close> \<open>known V i \<subseteq> W\<close>
  then have \<open>\<exists>X. (consistent A X) \<and> (maximal A X) \<and> X \<in> (reach A i W) \<inter> (reach A i U)\<close>
    using Ax_2_weakly_directed [where A=A and V=V and W=W and U=U] assms IntD2 
      by simp
  then have \<open>\<exists>X. (consistent A X) \<and> (maximal A X) \<and> X \<in> (reach A i W) \<and> X \<in> (reach A i U)\<close>
    by simp
  then show \<open>\<exists>X. (consistent A X) \<and> (maximal A X) \<and> known W i \<subseteq> X \<and> known U i \<subseteq> X\<close>
    by auto
qed

lemma imply_completeness_K_2:
  assumes valid: \<open>\<forall>(M :: ('i, 'i fm set) kripke). \<forall>w \<in> \<W> M.
    weakly_directed M \<longrightarrow> (\<forall>q \<in> G. M, w \<Turnstile> q) \<longrightarrow> M, w \<Turnstile> p\<close>
  shows \<open>\<exists>qs. set qs \<subseteq> G \<and> (Ax_2 \<turnstile> imply qs p)\<close>
proof (rule ccontr)
assume \<open>\<nexists>qs. set qs \<subseteq> G \<and> Ax_2 \<turnstile> imply qs p\<close>
  then have *: \<open>\<forall>qs. set qs \<subseteq> G \<longrightarrow> \<not> Ax_2 \<turnstile> imply ((\<^bold>\<not> p) # qs) \<^bold>\<bottom>\<close>
    using K_Boole by blast

  let ?S = \<open>{\<^bold>\<not> p} \<union> G\<close>
  let ?V = \<open>Extend Ax_2 ?S\<close>
  let ?M = \<open>\<lparr>\<W> = mcss Ax_2, \<K> = reach Ax_2, \<pi> = pi\<rparr>\<close>

  have \<open>consistent Ax_2 ?S\<close>
    using * by (metis K_imply_Cons consistent_def inconsistent_subset)
  then have \<open>?M, ?V \<Turnstile> (\<^bold>\<not> p)\<close> \<open>\<forall>q \<in> G. ?M, ?V \<Turnstile> q\<close> \<open>consistent Ax_2 ?V\<close> \<open>maximal Ax_2 ?V\<close>
    using canonical_model unfolding list_all_def by fastforce+
  moreover have \<open>weakly_directed ?M\<close>
    using mcs\<^sub>_\<^sub>2_weakly_directed [where A=Ax_2] by fast
  ultimately have \<open>?M, ?V \<Turnstile> p\<close>
    using valid by auto
  then show False
    using \<open>?M, ?V \<Turnstile> (\<^bold>\<not> p)\<close> by simp
qed


section \<open>System S4.2\<close>

abbreviation SystemS4_2 :: \<open>'i fm \<Rightarrow> bool\<close> ("\<turnstile>\<^sub>S\<^sub>4\<^sub>2 _" [50] 50) where
  \<open>\<turnstile>\<^sub>S\<^sub>4\<^sub>2 p \<equiv> AxT \<oplus> Ax4 \<oplus> Ax_2 \<turnstile> p\<close>

abbreviation AxS4_2 :: \<open>'i fm \<Rightarrow> bool\<close> where
  \<open>AxS4_2 \<equiv> AxT \<oplus> Ax4 \<oplus> Ax_2\<close>

subsection \<open>Soundness\<close>

abbreviation w_directed_preorder :: \<open>('i, 'w) kripke \<Rightarrow> bool\<close> where
  \<open>w_directed_preorder M \<equiv> reflexive M \<and> transitive M \<and> weakly_directed M\<close>

lemma soundness_AxS4_2: \<open>AxS4_2 p \<Longrightarrow> w_directed_preorder M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  using soundness_AxT soundness_Ax4 soundness_Ax_2 by metis

lemma soundness\<^sub>S\<^sub>4\<^sub>2: \<open>\<turnstile>\<^sub>S\<^sub>4\<^sub>2 p \<Longrightarrow> w_directed_preorder M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  using soundness soundness_AxS4_2 .

subsection \<open>Completeness\<close>

lemma imply_completeness_S4_2:
  assumes valid: \<open>\<forall>(M :: ('i, 'i fm set) kripke). \<forall>w \<in> \<W> M.
    w_directed_preorder M \<longrightarrow> (\<forall>q \<in> G. M, w \<Turnstile> q) \<longrightarrow> M, w \<Turnstile> p\<close>
  shows \<open>\<exists>qs. set qs \<subseteq> G \<and> (AxS4_2 \<turnstile> imply qs p)\<close>
proof (rule ccontr)
  assume \<open>\<nexists>qs. set qs \<subseteq> G \<and> AxS4_2 \<turnstile> imply qs p\<close>
  then have *: \<open>\<forall>qs. set qs \<subseteq> G \<longrightarrow> \<not> AxS4_2 \<turnstile> imply ((\<^bold>\<not> p) # qs) \<^bold>\<bottom>\<close>
    using K_Boole by blast

  let ?S = \<open>{\<^bold>\<not> p} \<union> G\<close>
  let ?V = \<open>Extend AxS4_2 ?S\<close>
  let ?M = \<open>\<lparr>\<W> = mcss AxS4_2, \<K> = reach AxS4_2, \<pi> = pi\<rparr>\<close>

  have \<open>consistent AxS4_2 ?S\<close>
    using * by (metis (no_types, lifting) K_imply_Cons consistent_def inconsistent_subset)
  then have
    \<open>?M, ?V \<Turnstile> (\<^bold>\<not> p)\<close> \<open>\<forall>q \<in> G. ?M, ?V \<Turnstile> q\<close>
    \<open>consistent AxS4_2 ?V\<close> \<open>maximal AxS4_2 ?V\<close>
    using canonical_model unfolding list_all_def by fastforce+
  moreover have \<open>w_directed_preorder ?M\<close>
    using reflexive\<^sub>T[of AxS4_2] mcs\<^sub>_\<^sub>2_weakly_directed[of AxS4_2] transitive\<^sub>K\<^sub>4[of AxS4_2] by auto
  ultimately have \<open>?M, ?V \<Turnstile> p\<close>
    using valid by auto
  then show False
    using \<open>?M, ?V \<Turnstile> (\<^bold>\<not> p)\<close> by simp
qed

lemma completeness\<^sub>S\<^sub>4\<^sub>2:
  assumes \<open>\<forall>(M :: ('i, 'i fm set) kripke). \<forall>w \<in> \<W> M. w_directed_preorder M \<longrightarrow> M, w \<Turnstile> p\<close>
  shows \<open>\<turnstile>\<^sub>S\<^sub>4\<^sub>2 p\<close>
  using assms imply_completeness_S4_2[where G=\<open>{}\<close>] by auto

abbreviation \<open>valid\<^sub>S\<^sub>4\<^sub>2 p \<equiv> \<forall>(M :: (nat, nat fm set) kripke). \<forall>w \<in> \<W> M. w_directed_preorder M \<longrightarrow> M, w \<Turnstile> p\<close>

theorem main\<^sub>S\<^sub>4\<^sub>2: \<open>valid\<^sub>S\<^sub>4\<^sub>2 p \<longleftrightarrow> \<turnstile>\<^sub>S\<^sub>4\<^sub>2 p\<close>
  using soundness\<^sub>S\<^sub>4\<^sub>2 completeness\<^sub>S\<^sub>4\<^sub>2 by fast

corollary
  assumes \<open>w_directed_preorder M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>valid\<^sub>S\<^sub>4\<^sub>2 p \<longrightarrow> M, w \<Turnstile> p\<close>
  using assms soundness\<^sub>S\<^sub>4\<^sub>2 completeness\<^sub>S\<^sub>4\<^sub>2 by fast


section \<open>Topological S4 axioms\<close>

abbreviation DoubleImp (infixr "\<^bold>\<longleftrightarrow>" 25) where
  \<open>(p\<^bold>\<longleftrightarrow>q) \<equiv> ((p \<^bold>\<longrightarrow> q) \<^bold>\<and> (q \<^bold>\<longrightarrow> p))\<close>

inductive System_topoS4 :: \<open>'i fm \<Rightarrow> bool\<close> ("\<turnstile>\<^sub>T\<^sub>o\<^sub>p _" [50] 50) where
  A1': \<open>tautology p \<Longrightarrow> \<turnstile>\<^sub>T\<^sub>o\<^sub>p p\<close>
| AR: \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p ((K i (p \<^bold>\<and> q)) \<^bold>\<longleftrightarrow> ((K i p) \<^bold>\<and> K i q))\<close>
| AT': \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p (K i p \<^bold>\<longrightarrow> p)\<close>
| A4': \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p (K i p \<^bold>\<longrightarrow> K i (K i p))\<close>
| AN: \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p K i \<^bold>\<top>\<close>
| R1': \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p p \<Longrightarrow> \<turnstile>\<^sub>T\<^sub>o\<^sub>p (p \<^bold>\<longrightarrow> q) \<Longrightarrow> \<turnstile>\<^sub>T\<^sub>o\<^sub>p q\<close>
| RM: \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p (p \<^bold>\<longrightarrow> q) \<Longrightarrow> \<turnstile>\<^sub>T\<^sub>o\<^sub>p ((K i p) \<^bold>\<longrightarrow> K i q)\<close>

lemma topoS4_trans: \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p ((p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r)\<close>
  by (simp add: A1')

lemma topoS4_conjElim: \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p (p \<^bold>\<and> q \<^bold>\<longrightarrow> q)\<close>
  by (simp add: A1')

lemma topoS4_AxK: \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p (K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i q)\<close>
proof -
  have \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p ((p \<^bold>\<and> (p \<^bold>\<longrightarrow> q)) \<^bold>\<longrightarrow> q)\<close>
    using A1' by force
  then have *: \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p (K i (p \<^bold>\<and> (p \<^bold>\<longrightarrow> q)) \<^bold>\<longrightarrow> K i q)\<close>
    using RM by fastforce
  then have \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p (K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i (p \<^bold>\<and> (p \<^bold>\<longrightarrow> q)))\<close>
    using AR topoS4_conjElim System_topoS4.simps by fast
  then show ?thesis
    by (meson "*" System_topoS4.R1' topoS4_trans)
qed

lemma topoS4_NecR:
  assumes \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p p\<close>
  shows\<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p K i p\<close>
proof -
  have \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p (\<^bold>\<top> \<^bold>\<longrightarrow> p)\<close>
    using assms by (metis System_topoS4.A1' System_topoS4.R1' conjunct.simps(1) imply.simps(1) imply_conjunct)
  then have \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p (K i \<^bold>\<top> \<^bold>\<longrightarrow> K i p)\<close>
    using RM by force
  then show ?thesis
    by (meson AN System_topoS4.R1')
qed

lemma empty_S4: "{} \<turnstile>\<^sub>S\<^sub>4 p \<longleftrightarrow> AxT \<oplus> Ax4 \<turnstile> p"
  by simp

lemma S4_topoS4: \<open>{} \<turnstile>\<^sub>S\<^sub>4 p \<Longrightarrow> \<turnstile>\<^sub>T\<^sub>o\<^sub>p p\<close>
  unfolding empty_S4
proof (induct p rule: AK.induct)
  case (A2 i p q)
  then show ?case using topoS4_AxK .
next 
  case (Ax p)
    then show ?case 
      using AT' A4' by (metis AxT.cases Ax4.cases)
next
  case (R2 p)
  then show ?case 
    by (simp add: topoS4_NecR)
qed (meson System_topoS4.intros)+

lemma topoS4_S4:
  fixes p :: \<open>'i fm\<close>
  shows \<open>\<turnstile>\<^sub>T\<^sub>o\<^sub>p p \<Longrightarrow> {} \<turnstile>\<^sub>S\<^sub>4 p\<close>
  unfolding empty_S4
proof (induct p rule: System_topoS4.induct)
  case (AT' i p)
  then show ?case
    by (simp add: Ax AxT.intros)
next
  case (A4' i p)
  then show ?case
    by (simp add: Ax Ax4.intros)
next
  case (AR i p q)
    then show ?case
      by (meson K_conj_imply_factor K_conjunction_in K_conjunction_out K_imp_trans' K_imply_multi R1)
next
  case (AN i) 
  then have *: \<open>AxT \<oplus> Ax4 \<turnstile> \<^bold>\<top>\<close>
    by (simp add: A1)
  then show ?case 
    by (simp add: * R2)
next
  case (RM p q i)
  then have \<open>AxT \<oplus> Ax4 \<turnstile> K i (p \<^bold>\<longrightarrow> q)\<close>
    by (simp add: R2)
  then show ?case
    by (simp add: K_map RM.hyps(2))
qed (meson AK.intros)+

theorem main\<^sub>S\<^sub>4': \<open>{} \<TTurnstile>\<^sub>S\<^sub>4 p \<longleftrightarrow> (\<turnstile>\<^sub>T\<^sub>o\<^sub>p p)\<close>
  using main\<^sub>S\<^sub>4[of "{}"] S4_topoS4 topoS4_S4 by fast

end
