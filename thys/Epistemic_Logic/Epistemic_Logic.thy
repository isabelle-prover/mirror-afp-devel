(*
  File:      Epistemic_Logic.thy
  Author:    Asta Halkjær From

  This work is a formalization of epistemic logic with countably many agents.
  It includes proofs of soundness and completeness for the axiom system K.
  The completeness proof is based on the textbook "Reasoning About Knowledge"
  by Fagin, Halpern, Moses and Vardi (MIT Press 1995).
*)

theory Epistemic_Logic imports "HOL-Library.Countable" begin

section \<open>Syntax\<close>

type_synonym id = string

datatype 'i fm
  = FF ("\<^bold>\<bottom>")
  | Pro id
  | Dis \<open>'i fm\<close> \<open>'i fm\<close> (infixr "\<^bold>\<or>" 30)
  | Con \<open>'i fm\<close> \<open>'i fm\<close> (infixr "\<^bold>\<and>" 35)
  | Imp \<open>'i fm\<close> \<open>'i fm\<close> (infixr "\<^bold>\<longrightarrow>" 25)
  | K 'i \<open>'i fm\<close>

abbreviation TT ("\<^bold>\<top>") where
  \<open>TT \<equiv> \<^bold>\<bottom> \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

abbreviation Neg ("\<^bold>\<not> _" [40] 40) where
  \<open>Neg p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

section \<open>Semantics\<close>

datatype ('i, 's) kripke = Kripke (\<pi>: \<open>'s \<Rightarrow> id \<Rightarrow> bool\<close>) (\<K>: \<open>'i \<Rightarrow> 's \<Rightarrow> 's set\<close>)

primrec semantics :: \<open>('i, 's) kripke \<Rightarrow> 's \<Rightarrow> 'i fm \<Rightarrow> bool\<close>
  ("_, _ \<Turnstile> _" [50,50] 50) where
  \<open>(_, _ \<Turnstile> \<^bold>\<bottom>) = False\<close>
| \<open>(M, s \<Turnstile> Pro i) = \<pi> M s i\<close>
| \<open>(M, s \<Turnstile> (p \<^bold>\<or> q)) = ((M, s \<Turnstile> p) \<or> (M, s \<Turnstile> q))\<close>
| \<open>(M, s \<Turnstile> (p \<^bold>\<and> q)) = ((M, s \<Turnstile> p) \<and> (M, s \<Turnstile> q))\<close>
| \<open>(M, s \<Turnstile> (p \<^bold>\<longrightarrow> q)) = ((M, s \<Turnstile> p) \<longrightarrow> (M, s \<Turnstile> q))\<close>
| \<open>(M, s \<Turnstile> K i p) = (\<forall>t \<in> \<K> M i s. M, t \<Turnstile> p)\<close>

section \<open>S5 Axioms\<close>

abbreviation reflexive :: \<open>('i, 's) kripke \<Rightarrow> bool\<close> where
  \<open>reflexive M \<equiv> \<forall>i s. s \<in> \<K> M i s\<close>

abbreviation symmetric :: \<open>('i, 's) kripke \<Rightarrow> bool\<close> where
  \<open>symmetric M \<equiv> \<forall>i s t. t \<in> \<K> M i s \<longleftrightarrow> s \<in> \<K> M i t\<close>

abbreviation transitive :: \<open>('i, 's) kripke \<Rightarrow> bool\<close> where
  \<open>transitive M \<equiv> \<forall>i s t u. t \<in> \<K> M i s \<and> u \<in> \<K> M i t \<longrightarrow> u \<in> \<K> M i s\<close>

lemma Imp_intro [intro]: \<open>(M, s \<Turnstile> p \<Longrightarrow> M, s \<Turnstile> q) \<Longrightarrow> M, s \<Turnstile> Imp p q\<close>
  by simp

theorem distribution: \<open>M, s \<Turnstile> (K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i q)\<close>
proof
  assume \<open>M, s \<Turnstile> (K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q))\<close>
  then have \<open>M, s \<Turnstile> K i p\<close> \<open>M, s \<Turnstile> K i (p \<^bold>\<longrightarrow> q)\<close>
    by simp_all
  then have \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> p\<close> \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
    by simp_all
  then have \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> q\<close>
    by simp
  then show \<open>M, s \<Turnstile> K i q\<close>
    by simp
qed

theorem generalization:
  assumes valid: \<open>\<forall>(M :: ('i, 's) kripke) s. M, s \<Turnstile> p\<close>
  shows \<open>(M :: ('i, 's) kripke), s \<Turnstile> K i p\<close>
proof -
  have \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> p\<close>
    using valid by blast
  then show \<open>M, s \<Turnstile> K i p\<close>
    by simp
qed

theorem truth:
  assumes \<open>reflexive M\<close>
  shows \<open>M, s \<Turnstile> (K i p \<^bold>\<longrightarrow> p)\<close>
proof
  assume \<open>M, s \<Turnstile> K i p\<close>
  then have \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> p\<close>
    by simp
  moreover have \<open>s \<in> \<K> M i s\<close>
    using \<open>reflexive M\<close> by blast
  ultimately show \<open>M, s \<Turnstile> p\<close>
    by blast
qed

theorem pos_introspection:
  assumes \<open>transitive M\<close>
  shows \<open>M, s \<Turnstile> (K i p \<^bold>\<longrightarrow> K i (K i p))\<close>
proof
  assume \<open>M,s \<Turnstile> K i p\<close>
  then have \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> p\<close>
    by simp
  then have \<open>\<forall>t \<in> \<K> M i s. \<forall>u \<in> \<K> M i t. M, u \<Turnstile> p\<close>
    using \<open>transitive M\<close> by blast
  then have \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> K i p\<close>
    by simp
  then show \<open>M, s \<Turnstile> K i (K i p)\<close>
    by simp
qed

theorem neg_introspection:
  assumes \<open>symmetric M\<close> \<open>transitive M\<close>
  shows \<open>M, s \<Turnstile> (\<^bold>\<not> K i p \<^bold>\<longrightarrow> K i (\<^bold>\<not> K i p))\<close>
proof
  assume \<open>M,s \<Turnstile> \<^bold>\<not> (K i p)\<close>
  then obtain u where \<open>u \<in> \<K> M i s\<close> \<open>\<not> (M, u \<Turnstile> p)\<close>
    by auto
  moreover have \<open>\<forall>t \<in> \<K> M i s. u \<in> \<K> M i t\<close>
    using \<open>u \<in> \<K> M i s\<close> \<open>symmetric M\<close> \<open>transitive M\<close> by blast
  ultimately have \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> \<^bold>\<not> K i p\<close>
    by auto
  then show \<open>M, s \<Turnstile> K i (\<^bold>\<not> K i p)\<close>
    by simp
qed

section \<open>Axiom System K\<close>

primrec eval :: \<open>(id \<Rightarrow> bool) \<Rightarrow> ('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm \<Rightarrow> bool\<close> where
  \<open>eval _ _ \<^bold>\<bottom> = False\<close>
| \<open>eval g _ (Pro i) = g i\<close>
| \<open>eval g h (p \<^bold>\<or> q) = (eval g h p \<or> eval g h q)\<close>
| \<open>eval g h (p \<^bold>\<and> q) = (eval g h p \<and> eval g h q)\<close>
| \<open>eval g h (p \<^bold>\<longrightarrow> q) = (eval g h p \<longrightarrow> eval g h q)\<close>
| \<open>eval _ h (K i p) = h (K i p)\<close>

abbreviation \<open>tautology p \<equiv> \<forall>g h. eval g h p\<close>

inductive SystemK :: \<open>'i fm \<Rightarrow> bool\<close> ("\<turnstile> _" [50] 50) where
  A1: \<open>tautology p \<Longrightarrow> \<turnstile> p\<close>
| A2: \<open>\<turnstile> (K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i q)\<close>
| R1: \<open>\<turnstile> p \<Longrightarrow> \<turnstile> (p \<^bold>\<longrightarrow> q) \<Longrightarrow> \<turnstile> q\<close>
| R2: \<open>\<turnstile> p \<Longrightarrow> \<turnstile> K i p\<close>

section \<open>Soundness\<close>

lemma eval_semantics: \<open>eval (pi s) (\<lambda>q. Kripke pi r, s \<Turnstile> q) p = (Kripke pi r, s \<Turnstile> p)\<close>
  by (induct p) simp_all

lemma tautology:
  assumes \<open>tautology p\<close>
  shows \<open>M, s \<Turnstile> p\<close>
proof -
  from assms have \<open>eval (g s) (\<lambda>q. Kripke g r, s \<Turnstile> q) p\<close> for g r
    by simp
  then have \<open>Kripke g r, s \<Turnstile> p\<close> for g r
    using eval_semantics by metis
  then show \<open>M, s \<Turnstile> p\<close>
    by (metis kripke.collapse)
qed

theorem soundness: \<open>\<turnstile> p \<Longrightarrow> M, s \<Turnstile> p\<close>
  by (induct p arbitrary: s rule: SystemK.induct) (simp_all add: tautology)

section \<open>Derived rules\<close>

primrec imply :: \<open>'i fm list \<Rightarrow> 'i fm \<Rightarrow> 'i fm\<close> where
  \<open>imply [] q = q\<close>
| \<open>imply (p # ps) q = (p \<^bold>\<longrightarrow> imply ps q)\<close>

lemma K_imply_head: \<open>\<turnstile> imply (p # ps) p\<close>
proof -
  have \<open>tautology (imply (p # ps) p)\<close>
    by (induct ps) simp_all
  then show ?thesis
    using A1 by blast
qed

lemma K_imply_Cons:
  assumes \<open>\<turnstile> imply ps q\<close>
  shows \<open>\<turnstile> imply (p # ps) q\<close>
proof -
  have \<open>\<turnstile> (imply ps q \<^bold>\<longrightarrow> imply (p # ps) q)\<close>
    by (simp add: A1)
  with R1 assms show ?thesis .
qed

lemma K_right_mp:
  assumes \<open>\<turnstile> imply ps p\<close> \<open>\<turnstile> imply ps (p \<^bold>\<longrightarrow> q)\<close>
  shows \<open>\<turnstile> imply ps q\<close>
proof -
  have \<open>tautology (imply ps p \<^bold>\<longrightarrow> imply ps (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> imply ps q)\<close>
    by (induct ps) simp_all
  with A1 have \<open>\<turnstile> (imply ps p \<^bold>\<longrightarrow> imply ps (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> imply ps q)\<close> .
  then show ?thesis
    using assms R1 by blast
qed

lemma tautology_imply_superset:
  assumes \<open>set ps \<subseteq> set qs\<close>
  shows \<open>tautology (imply ps r \<^bold>\<longrightarrow> imply qs r)\<close>
proof (rule ccontr)
  assume \<open>\<not> tautology (imply ps r \<^bold>\<longrightarrow> imply qs r)\<close>
  then obtain g h where \<open>\<not> eval g h (imply ps r \<^bold>\<longrightarrow> imply qs r)\<close>
    by blast
  then have \<open>eval g h (imply ps r)\<close> \<open>\<not> eval g h (imply qs r)\<close>
    by simp_all
  then consider (np) \<open>\<exists>p \<in> set ps. \<not> eval g h p\<close> | (r) \<open>\<forall>p \<in> set ps. eval g h p\<close> \<open>eval g h r\<close>
    by (induct ps) auto
  then show False
  proof cases
    case np
    then have \<open>\<exists>p \<in> set qs. \<not> eval g h p\<close>
      using \<open>set ps \<subseteq> set qs\<close> by blast
    then have \<open>eval g h (imply qs r)\<close>
      by (induct qs) simp_all
    then show ?thesis
      using \<open>\<not> eval g h (imply qs r)\<close> by blast
  next
    case r
    then have \<open>eval g h (imply qs r)\<close>
      by (induct qs) simp_all
    then show ?thesis
      using \<open>\<not> eval g h (imply qs r)\<close> by blast
  qed
qed

lemma K_imply_weaken:
  assumes \<open>\<turnstile> imply ps q\<close> \<open>set ps \<subseteq> set ps'\<close>
  shows \<open>\<turnstile> imply ps' q\<close>
proof -
  have \<open>tautology (imply ps q \<^bold>\<longrightarrow> imply ps' q)\<close>
    using \<open>set ps \<subseteq> set ps'\<close> tautology_imply_superset by blast
  then have \<open>\<turnstile> (imply ps q \<^bold>\<longrightarrow> imply ps' q)\<close>
    using A1 by blast
  then show ?thesis
    using \<open>\<turnstile> imply ps q\<close> R1 by blast
qed

lemma imply_append: \<open>imply (ps @ ps') q = imply ps (imply ps' q)\<close>
  by (induct ps) simp_all

lemma K_ImpI:
  assumes \<open>\<turnstile> imply (p # G) q\<close>
  shows \<open>\<turnstile> imply G (p \<^bold>\<longrightarrow> q)\<close>
proof -
  have \<open>set (p # G) \<subseteq> set (G @ [p])\<close>
    by simp
  then have \<open>\<turnstile> imply (G @ [p]) q\<close>
    using assms K_imply_weaken by blast
  then have \<open>\<turnstile> imply G (imply [p] q)\<close>
    using imply_append by metis
  then show ?thesis
    by simp
qed

lemma K_Boole:
  assumes \<open>\<turnstile> imply ((\<^bold>\<not> p) # G) \<^bold>\<bottom>\<close>
  shows \<open>\<turnstile> imply G p\<close>
proof -
  have \<open>\<turnstile> imply G (\<^bold>\<not> \<^bold>\<not> p)\<close>
    using assms K_ImpI by blast
  moreover have \<open>tautology (imply G (\<^bold>\<not> \<^bold>\<not> p) \<^bold>\<longrightarrow> imply G p)\<close>
    by (induct G) simp_all
  then have \<open>\<turnstile> (imply G (\<^bold>\<not> \<^bold>\<not> p) \<^bold>\<longrightarrow> imply G p)\<close>
    using A1 by blast
  ultimately show ?thesis
    using R1 by blast
qed

lemma K_DisE:
  assumes \<open>\<turnstile> imply (A # G) C\<close> \<open>\<turnstile> imply (B # G) C\<close> \<open>\<turnstile> imply G (A \<^bold>\<or> B)\<close>
  shows \<open>\<turnstile> imply G C\<close>
proof -
  have \<open>tautology (imply (A # G) C \<^bold>\<longrightarrow> imply (B # G) C \<^bold>\<longrightarrow> imply G (A \<^bold>\<or> B) \<^bold>\<longrightarrow> imply G C)\<close>
    by (induct G) auto
  then have \<open>\<turnstile> (imply (A # G) C \<^bold>\<longrightarrow> imply (B # G) C \<^bold>\<longrightarrow> imply G (A \<^bold>\<or> B) \<^bold>\<longrightarrow> imply G C)\<close>
    using A1 by blast
  then show ?thesis
    using assms R1 by blast
qed

lemma K_mp: \<open>\<turnstile> imply (p # (p \<^bold>\<longrightarrow> q) # V) q\<close>
  by (meson K_imply_head K_imply_weaken K_right_mp set_subset_Cons)

lemma K_swap:
  assumes \<open>\<turnstile> imply (p # q # G) r\<close>
  shows \<open>\<turnstile> imply (q # p # G) r\<close>
  using assms K_ImpI by (metis imply.simps(1-2))

lemma K_DisL:
  assumes \<open>\<turnstile> imply (p # ps) q\<close> \<open>\<turnstile> imply (p' # ps) q\<close>
  shows \<open>\<turnstile> imply ((p \<^bold>\<or> p') # ps) q\<close>
proof -
  have \<open>\<turnstile> imply (p # (p \<^bold>\<or> p') # ps) q\<close> \<open>\<turnstile> imply (p' # (p \<^bold>\<or> p') # ps) q\<close>
    using assms K_swap K_imply_Cons by blast+
  moreover have \<open>\<turnstile> imply ((p \<^bold>\<or> p') # ps) (p \<^bold>\<or> p')\<close>
    using K_imply_head by blast
  ultimately show ?thesis
    using K_DisE by blast
qed

lemma K_distrib_K_imp:
  assumes \<open>\<turnstile> K i (imply G q)\<close>
  shows \<open>\<turnstile> imply (map (K i) G) (K i q)\<close>
proof -
  have \<open>\<turnstile> (K i (imply G q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q))\<close>
  proof (induct G)
    case Nil
    then show ?case
      by (simp add: A1)
  next
    case (Cons a G)
    have \<open>\<turnstile> (K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> K i (imply G q))\<close>
      by (simp add: A2)
    moreover have
      \<open>\<turnstile> ((K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> K i (imply G q)) \<^bold>\<longrightarrow>
        (K i (imply G q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)) \<^bold>\<longrightarrow>
        (K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)))\<close>
      by (simp add: A1)
    ultimately have \<open>\<turnstile> (K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q))\<close>
      using Cons R1 by blast
    moreover have
      \<open>\<turnstile> ((K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)) \<^bold>\<longrightarrow>
        (K i (imply (a # G) q) \<^bold>\<longrightarrow> K i a \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)))\<close>
      by (simp add: A1)
    ultimately have \<open>\<turnstile> (K i (imply (a # G) q) \<^bold>\<longrightarrow> K i a \<^bold>\<longrightarrow> imply (map (K i) G) (K i q))\<close>
      using R1 by blast
    then show ?case
      by simp
  qed
  then show ?thesis
    using assms R1 by blast
qed

section \<open>Completeness\<close>

subsection \<open>Consistent sets\<close>

definition consistent :: \<open>'i fm set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> \<turnstile> imply S' \<^bold>\<bottom>\<close>

lemma inconsistent_subset:
  assumes \<open>consistent V\<close> \<open>\<not> consistent ({p} \<union> V)\<close>
  obtains S where \<open>set S \<subseteq> V\<close> \<open>\<turnstile> imply (p # S) \<^bold>\<bottom>\<close>
proof -
  obtain V' where V': \<open>set V' \<subseteq> ({p} \<union> V)\<close> \<open>p \<in> set V'\<close> \<open>\<turnstile> imply V' \<^bold>\<bottom>\<close>
    using assms unfolding consistent_def by blast
  then have *: \<open>\<turnstile> imply (p # V') \<^bold>\<bottom>\<close>
    using K_imply_Cons by blast

  let ?S = \<open>removeAll p V'\<close>
  have \<open>set (p # V') \<subseteq> set (p # ?S)\<close>
    by auto
  then have \<open>\<turnstile> imply (p # ?S) \<^bold>\<bottom>\<close>
    using * K_imply_weaken by blast
  moreover have \<open>set ?S \<subseteq> V\<close>
    using V'(1) by (metis Diff_subset_conv set_removeAll)
  ultimately show ?thesis
    using that by blast
qed

lemma consistent_consequent:
  assumes \<open>consistent V\<close> \<open>p \<in> V\<close> \<open>\<turnstile> (p \<^bold>\<longrightarrow> q)\<close>
  shows \<open>consistent ({q} \<union> V)\<close>
proof -
  have \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> \<turnstile> imply (p # V') \<^bold>\<bottom>\<close>
    using \<open>consistent V\<close> \<open>p \<in> V\<close> unfolding consistent_def
    by (metis insert_subset list.simps(15))
  then have \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> \<turnstile> imply (q # V') \<^bold>\<bottom>\<close>
    using \<open>\<turnstile> (p \<^bold>\<longrightarrow> q)\<close> K_imply_head K_right_mp by (metis imply.simps(1-2))
  then show ?thesis
    using \<open>consistent V\<close> inconsistent_subset by metis
qed

lemma consistent_consequent':
  assumes \<open>consistent V\<close> \<open>p \<in> V\<close> \<open>tautology (p \<^bold>\<longrightarrow> q)\<close>
  shows \<open>consistent ({q} \<union> V)\<close>
  using assms consistent_consequent A1 by blast

lemma consistent_disjuncts:
  assumes \<open>consistent V\<close> \<open>(p \<^bold>\<or> q) \<in> V\<close>
  shows \<open>consistent ({p} \<union> V) \<or> consistent ({q} \<union> V)\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then have \<open>\<not> consistent ({p} \<union> V)\<close> \<open>\<not> consistent ({q} \<union> V)\<close>
    by blast+

  then obtain S' T' where
    S': \<open>set S' \<subseteq> V\<close> \<open>\<turnstile> imply (p # S') \<^bold>\<bottom>\<close> and
    T': \<open>set T' \<subseteq> V\<close> \<open>\<turnstile> imply (q # T') \<^bold>\<bottom>\<close>
    using \<open>consistent V\<close> inconsistent_subset by metis

  from S' have p: \<open>\<turnstile> imply (p # S' @ T') \<^bold>\<bottom>\<close>
    by (metis K_imply_weaken Un_upper1 append_Cons set_append)
  moreover from T' have q: \<open>\<turnstile> imply (q # S' @ T') \<^bold>\<bottom>\<close>
    by (metis K_imply_head K_right_mp R1 imply.simps(2) imply_append)
  ultimately have \<open>\<turnstile> imply ((p \<^bold>\<or> q) # S' @ T') \<^bold>\<bottom>\<close>
    using K_DisL by blast
  then have \<open>\<turnstile> imply (S' @ T') \<^bold>\<bottom>\<close>
    using S'(1) T'(1) p q \<open>consistent V\<close> \<open>(p \<^bold>\<or> q) \<in> V\<close> unfolding consistent_def
    by (metis Un_subset_iff insert_subset list.simps(15) set_append)
  moreover have \<open>set (S' @ T') \<subseteq> V\<close>
    by (simp add: S'(1) T'(1))
  ultimately show False
    using \<open>consistent V\<close> unfolding consistent_def by blast
qed

lemma exists_finite_inconsistent:
  assumes \<open>\<not> consistent ({\<^bold>\<not> p} \<union> V)\<close>
  obtains W where \<open>{\<^bold>\<not> p} \<union> W \<subseteq> {\<^bold>\<not> p} \<union> V\<close> \<open>(\<^bold>\<not> p) \<notin> W\<close> \<open>finite W\<close> \<open>\<not> consistent ({\<^bold>\<not> p} \<union> W)\<close>
proof -
  obtain W' where W': \<open>set W' \<subseteq> {\<^bold>\<not> p} \<union> V\<close> \<open>\<turnstile> imply W' \<^bold>\<bottom>\<close>
    using assms unfolding consistent_def by blast
  let ?S = \<open>removeAll (\<^bold>\<not> p) W'\<close>
  have \<open>\<not> consistent ({\<^bold>\<not> p} \<union> set ?S)\<close>
    unfolding consistent_def using W'(2) by auto
  moreover have \<open>finite (set ?S)\<close>
    by blast
  moreover have \<open>{\<^bold>\<not> p} \<union> set ?S \<subseteq> {\<^bold>\<not> p} \<union> V\<close>
    using W'(1) by auto
  moreover have \<open>(\<^bold>\<not> p) \<notin> set ?S\<close>
    by simp
  ultimately show ?thesis
    by (meson that)
qed

lemma inconsistent_imply:
  assumes \<open>\<not> consistent ({\<^bold>\<not> p} \<union> set W)\<close>
  shows \<open>\<turnstile> imply W p\<close>
  using assms K_Boole K_imply_weaken unfolding consistent_def
  by (metis insert_is_Un list.simps(15))

subsection \<open>Maximal consistent sets\<close>

definition maximal :: \<open>'i fm set \<Rightarrow> bool\<close> where
  \<open>maximal S \<equiv> \<forall>p. p \<notin> S \<longrightarrow> \<not> consistent ({p} \<union> S)\<close>

theorem K_deriv_in_maximal:
  assumes \<open>consistent V\<close> \<open>maximal V\<close> \<open>\<turnstile> p\<close>
  shows \<open>p \<in> V\<close>
  using assms R1 inconsistent_subset unfolding consistent_def maximal_def
  by (metis imply.simps(2))

theorem exactly_one_in_maximal:
  assumes \<open>consistent V\<close> \<open>maximal V\<close>
  shows \<open>p \<in> V \<longleftrightarrow> (\<^bold>\<not> p) \<notin> V\<close>
proof
  assume \<open>p \<in> V\<close>
  then show \<open>(\<^bold>\<not> p) \<notin> V\<close>
    using assms K_mp unfolding consistent_def maximal_def
    by (metis empty_subsetI insert_subset list.set(1) list.simps(15))
next
  assume \<open>(\<^bold>\<not> p) \<notin> V\<close>
  have \<open>\<turnstile> (p \<^bold>\<or> \<^bold>\<not> p)\<close>
    by (simp add: A1)
  then have \<open>(p \<^bold>\<or> \<^bold>\<not> p) \<in> V\<close>
    using assms K_deriv_in_maximal by blast
  then have \<open>consistent ({p} \<union> V) \<or> consistent ({\<^bold>\<not> p} \<union> V)\<close>
    using assms consistent_disjuncts by blast
  then show \<open>p \<in> V\<close>
    using \<open>maximal V\<close> \<open>(\<^bold>\<not> p) \<notin> V\<close> unfolding maximal_def by blast
qed

theorem consequent_in_maximal:
  assumes \<open>consistent V\<close> \<open>maximal V\<close> \<open>p \<in> V\<close> \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close>
  shows \<open>q \<in> V\<close>
proof -
  have \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> \<turnstile> imply (p # (p \<^bold>\<longrightarrow> q) # V') \<^bold>\<bottom>\<close>
    using \<open>consistent V\<close> \<open>p \<in> V\<close> \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close> unfolding consistent_def
    by (metis insert_subset list.simps(15))
  then have \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> \<turnstile> imply (q # V') \<^bold>\<bottom>\<close>
    by (meson K_mp K_ImpI K_imply_weaken K_right_mp set_subset_Cons)
  then have \<open>consistent ({q} \<union> V)\<close>
    using \<open>consistent V\<close> inconsistent_subset by metis
  then show ?thesis
    using \<open>maximal V\<close> unfolding maximal_def by fast
qed

subsection \<open>Lindenbaum extension\<close>

instantiation fm :: (countable) countable begin
instance by countable_datatype
end

primrec extend :: \<open>'i fm set \<Rightarrow> (nat \<Rightarrow> 'i fm) \<Rightarrow> nat \<Rightarrow> 'i fm set\<close> where
  \<open>extend S f 0 = S\<close> |
  \<open>extend S f (Suc n) =
    (if consistent ({f n} \<union> extend S f n)
     then {f n} \<union> extend S f n
     else extend S f n)\<close>

definition Extend :: \<open>'i fm set \<Rightarrow> (nat \<Rightarrow> 'i fm) \<Rightarrow> 'i fm set\<close> where
  \<open>Extend S f \<equiv> \<Union>n. extend S f n\<close>

lemma Extend_subset: \<open>S \<subseteq> Extend S f\<close>
  unfolding Extend_def using Union_upper extend.simps(1) range_eqI
  by metis

lemma extend_bound: \<open>(\<Union>n \<le> m. extend S f n) = extend S f m\<close>
  by (induct m) (simp_all add: atMost_Suc)

lemma consistent_extend: \<open>consistent S \<Longrightarrow> consistent (extend S f n)\<close>
  by (induct n) simp_all

lemma UN_finite_bound:
  assumes \<open>finite A\<close> \<open>A \<subseteq> (\<Union>n. f n)\<close>
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

lemma consistent_Extend:
  assumes \<open>consistent S\<close>
  shows \<open>consistent (Extend S f)\<close>
  unfolding Extend_def
proof (rule ccontr)
  assume \<open>\<not> consistent (\<Union>n. extend S f n)\<close>
  then obtain S' where \<open>\<turnstile> imply S' \<^bold>\<bottom>\<close> \<open>set S' \<subseteq> (\<Union>n. extend S f n)\<close>
    unfolding consistent_def by blast
  then obtain m where \<open>set S' \<subseteq> (\<Union>n \<le> m. extend S f n)\<close>
    using UN_finite_bound by (metis List.finite_set)
  then have \<open>set S' \<subseteq> extend S f m\<close>
    using extend_bound by blast
  moreover have \<open>consistent (extend S f m)\<close>
    using assms consistent_extend by blast
  ultimately show False
    unfolding consistent_def using \<open>\<turnstile> imply S' \<^bold>\<bottom>\<close> by blast
qed

lemma Extend_maximal:
  assumes \<open>surj f\<close>
  shows \<open>maximal (Extend S f)\<close>
proof (rule ccontr)
  assume \<open>\<not> maximal (Extend S f)\<close>
  then obtain p where \<open>p \<notin> Extend S f\<close> \<open>consistent ({p} \<union> Extend S f)\<close>
    unfolding maximal_def using assms consistent_Extend by blast
  obtain k where n: \<open>f k = p\<close>
    using \<open>surj f\<close> unfolding surj_def by metis
  then have \<open>p \<notin> extend S f (Suc k)\<close>
    using \<open>p \<notin> Extend S f\<close> unfolding Extend_def by blast
  then have \<open>\<not> consistent ({p} \<union> extend S f k)\<close>
    using n by fastforce
  moreover have \<open>{p} \<union> extend S f k \<subseteq> {p} \<union> Extend S f\<close>
    unfolding Extend_def by blast
  ultimately have \<open>\<not> consistent ({p} \<union> Extend S f)\<close>
    unfolding consistent_def by fastforce
  then show False
    using \<open>consistent ({p} \<union> Extend S f)\<close> by blast
qed

lemma maximal_extension:
  fixes V :: \<open>('i :: countable) fm set\<close>
  assumes \<open>consistent V\<close>
  obtains W where \<open>V \<subseteq> W\<close> \<open>consistent W\<close> \<open>maximal W\<close>
proof -
  let ?W = \<open>Extend V from_nat\<close>

  have \<open>V \<subseteq> ?W\<close>
    using Extend_subset by blast
  moreover have \<open>consistent ?W\<close>
    using assms consistent_Extend by blast
  moreover have \<open>maximal ?W\<close>
    using assms Extend_maximal surj_from_nat by blast
  ultimately show ?thesis
    using that by blast
qed

subsection \<open>Model existence\<close>

type_synonym 'i s_max = \<open>'i fm set\<close>

abbreviation pi :: \<open>'i s_max \<Rightarrow> id \<Rightarrow> bool\<close> where
  \<open>pi s i \<equiv> Pro i \<in> s\<close>

abbreviation partition :: \<open>'i fm set \<Rightarrow> 'i \<Rightarrow> 'i fm set\<close> where
  \<open>partition V i \<equiv> {p. K i p \<in> V}\<close>

abbreviation reach :: \<open>'i \<Rightarrow> 'i s_max \<Rightarrow> 'i s_max set\<close> where
  \<open>reach i V \<equiv> {W. partition V i \<subseteq> W \<and> consistent W \<and> maximal W}\<close>

theorem model_existence:
  fixes p :: \<open>('i :: countable) fm\<close>
  assumes \<open>consistent V\<close> \<open>maximal V\<close>
  shows \<open>(p \<in> V \<longleftrightarrow> Kripke pi reach, V \<Turnstile> p) \<and> ((\<^bold>\<not> p) \<in> V \<longleftrightarrow> Kripke pi reach, V \<Turnstile> \<^bold>\<not> p)\<close>
  using assms
proof (induct p arbitrary: V)
  case FF
  then show ?case
  proof (intro conjI impI iffI)
    assume \<open>\<^bold>\<bottom> \<in> V\<close>
    then have False
      using \<open>consistent V\<close> K_imply_head unfolding consistent_def
      by (metis bot.extremum insert_subset list.set(1) list.simps(15))
    then show \<open>Kripke pi reach, V \<Turnstile> \<^bold>\<bottom>\<close> ..
  next
    assume \<open>Kripke pi reach, V \<Turnstile> \<^bold>\<not> \<^bold>\<bottom>\<close>
    then show \<open>(\<^bold>\<not> \<^bold>\<bottom>) \<in> V\<close>
      using \<open>consistent V\<close> \<open>maximal V\<close> unfolding maximal_def
      by (meson K_Boole inconsistent_subset consistent_def)
  qed simp_all
next
  case (Pro i)
  then show ?case
  proof (intro conjI impI iffI)
    assume \<open>(\<^bold>\<not> Pro i) \<in> V\<close>
    then show \<open>Kripke pi reach, V \<Turnstile> \<^bold>\<not> Pro i\<close>
      using \<open>consistent V\<close> \<open>maximal V\<close> exactly_one_in_maximal by auto
  next
    assume \<open>Kripke pi reach, V \<Turnstile> \<^bold>\<not> Pro i\<close>
    then show \<open>(\<^bold>\<not> Pro i) \<in> V\<close>
      using \<open>consistent V\<close> \<open>maximal V\<close> exactly_one_in_maximal by auto
  qed (simp_all add: \<open>maximal V\<close> maximal_def)
next
  case (Dis p q)
  have \<open>(p \<^bold>\<or> q) \<in> V \<longrightarrow> Kripke pi reach, V \<Turnstile> (p \<^bold>\<or> q)\<close>
  proof
    assume \<open>(p \<^bold>\<or> q) \<in> V\<close>
    then have \<open>consistent ({p} \<union> V) \<or> consistent ({q} \<union> V)\<close>
      using \<open>consistent V\<close> consistent_disjuncts by blast
    then have \<open>p \<in> V \<or> q \<in> V\<close>
      using \<open>maximal V\<close> unfolding maximal_def by fast
    then show \<open>Kripke pi reach, V \<Turnstile> (p \<^bold>\<or> q)\<close>
      using Dis by simp
  qed
  moreover have \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) \<in> V \<longrightarrow> Kripke pi reach, V \<Turnstile> \<^bold>\<not> (p \<^bold>\<or> q)\<close>
  proof
    assume \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) \<in> V\<close>
    then have \<open>consistent ({\<^bold>\<not> q} \<union> V)\<close> \<open>consistent ({\<^bold>\<not> p} \<union> V)\<close>
      using \<open>consistent V\<close> consistent_consequent' by fastforce+
    then have \<open>(\<^bold>\<not> p) \<in> V\<close> \<open>(\<^bold>\<not> q) \<in> V\<close>
      using \<open>maximal V\<close> unfolding maximal_def by fast+
    then show \<open>Kripke pi reach, V \<Turnstile> \<^bold>\<not> (p \<^bold>\<or> q)\<close>
      using Dis by simp
  qed
  ultimately show ?case
    using exactly_one_in_maximal Dis by auto
next
  case (Con p q)
  have \<open>(p \<^bold>\<and> q) \<in> V \<longrightarrow> Kripke pi reach, V \<Turnstile> (p \<^bold>\<and> q)\<close>
  proof
    assume \<open>(p \<^bold>\<and> q) \<in> V\<close>
    then have \<open>consistent ({p} \<union> V)\<close> \<open>consistent ({q} \<union> V)\<close>
      using \<open>consistent V\<close> consistent_consequent' by fastforce+
    then have \<open>p \<in> V\<close> \<open>q \<in> V\<close>
      using \<open>maximal V\<close> unfolding maximal_def by fast+
    then show \<open>Kripke pi reach, V \<Turnstile> (p \<^bold>\<and> q)\<close>
      using Con by simp
  qed
  moreover have \<open>(\<^bold>\<not> (p \<^bold>\<and> q)) \<in> V \<longrightarrow> Kripke pi reach, V \<Turnstile> \<^bold>\<not> (p \<^bold>\<and> q)\<close>
  proof
    assume \<open>(\<^bold>\<not> (p \<^bold>\<and> q)) \<in> V\<close>
    then have \<open>consistent ({\<^bold>\<not> p \<^bold>\<or> \<^bold>\<not> q} \<union> V)\<close>
      using \<open>consistent V\<close> consistent_consequent' by fastforce
    then have \<open>consistent ({\<^bold>\<not> p} \<union> V) \<or> consistent ({\<^bold>\<not> q} \<union> V)\<close>
      using \<open>consistent V\<close> \<open>maximal V\<close> consistent_disjuncts unfolding maximal_def by blast
    then have \<open>(\<^bold>\<not> p) \<in> V \<or> (\<^bold>\<not> q) \<in> V\<close>
      using \<open>maximal V\<close> unfolding maximal_def by fast
    then show \<open>Kripke pi reach, V \<Turnstile> \<^bold>\<not> (p \<^bold>\<and> q)\<close>
      using Con by simp
  qed
  ultimately show ?case
    using exactly_one_in_maximal Con by auto
next
  case (Imp p q)
  have \<open>(p \<^bold>\<longrightarrow> q) \<in> V \<longrightarrow> Kripke pi reach, V \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
  proof
    assume \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close>
    then have \<open>consistent ({\<^bold>\<not> p \<^bold>\<or> q} \<union> V)\<close>
      using \<open>consistent V\<close> consistent_consequent' by fastforce
    then have \<open>consistent ({\<^bold>\<not> p} \<union> V) \<or> consistent ({q} \<union> V)\<close>
      using \<open>consistent V\<close> \<open>maximal V\<close> consistent_disjuncts unfolding maximal_def by blast
    then have \<open>(\<^bold>\<not> p) \<in> V \<or> q \<in> V\<close>
      using \<open>maximal V\<close> unfolding maximal_def by fast
    then show \<open>Kripke pi reach, V \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
      using Imp by simp
  qed
  moreover have \<open>(\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) \<in> V \<longrightarrow> Kripke pi reach, V \<Turnstile> \<^bold>\<not> (p \<^bold>\<longrightarrow> q)\<close>
  proof
    assume \<open>(\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) \<in> V\<close>
    then have \<open>consistent ({p} \<union> V)\<close> \<open>consistent ({\<^bold>\<not> q} \<union> V)\<close>
      using \<open>consistent V\<close> consistent_consequent' by fastforce+
    then have \<open>p \<in> V\<close> \<open>(\<^bold>\<not> q) \<in> V\<close>
      using \<open>maximal V\<close> unfolding maximal_def by fast+
    then show \<open>Kripke pi reach, V \<Turnstile> \<^bold>\<not> (p \<^bold>\<longrightarrow> q)\<close>
      using Imp by simp
  qed
  ultimately show ?case
    using exactly_one_in_maximal Imp \<open>consistent V\<close> by auto
next
  case (K i p)
  then have \<open>K i p \<in> V \<longrightarrow> Kripke pi reach, V \<Turnstile> K i p\<close>
    by auto
  moreover have \<open>(Kripke pi reach, V \<Turnstile> K i p) \<longrightarrow> K i p \<in> V\<close>
  proof (intro allI impI)
    assume \<open>Kripke pi reach, V \<Turnstile> K i p\<close>

    have \<open>\<not> consistent ({\<^bold>\<not> p} \<union> partition V i)\<close>
    proof
      assume \<open>consistent ({\<^bold>\<not> p} \<union> partition V i)\<close>
      then obtain W where W: \<open>{\<^bold>\<not> p} \<union> partition V i \<subseteq> W\<close> \<open>consistent W\<close> \<open>maximal W\<close>
        using \<open>consistent V\<close> maximal_extension by blast
      then have \<open>Kripke pi reach, W \<Turnstile> \<^bold>\<not> p\<close>
        using K \<open>consistent V\<close> by blast
      moreover have \<open>W \<in> reach i V\<close>
        using W by simp
      ultimately have \<open>Kripke pi reach, V \<Turnstile> \<^bold>\<not> K i p\<close>
        by auto
      then show False
        using \<open>Kripke pi reach, V \<Turnstile> K i p\<close> by auto
    qed

    then obtain W where W:
      \<open>{\<^bold>\<not> p} \<union> W \<subseteq> {\<^bold>\<not> p} \<union> partition V i\<close> \<open>(\<^bold>\<not> p) \<notin> W\<close> \<open>finite W\<close> \<open>\<not> consistent ({\<^bold>\<not> p} \<union> W)\<close>
      using exists_finite_inconsistent by metis

    obtain L where L: \<open>set L = W\<close>
      using \<open>finite W\<close> finite_list by blast

    then have \<open>\<turnstile> imply L p\<close>
      using W(4) inconsistent_imply by blast
    then have \<open>\<turnstile> K i (imply L p)\<close>
      using R2 by fast
    then have \<open>\<turnstile> imply (map (K i) L) (K i p)\<close>
      using K_distrib_K_imp by fast
    then have \<open>imply (map (K i) L) (K i p) \<in> V\<close>
      using K_deriv_in_maximal K.prems(1, 2) by blast
    then show \<open>K i p \<in> V\<close>
      using L W(1-2)
    proof (induct L arbitrary: W)
      case (Cons a L)
      then have \<open>K i a \<in> V\<close>
        by auto
      then have \<open>imply (map (K i) L) (K i p) \<in> V\<close>
        using Cons(2) \<open>consistent V\<close> \<open>maximal V\<close> consequent_in_maximal by auto
      then show ?case
        using Cons by auto
    qed simp
  qed
  moreover have \<open>(Kripke pi reach, V \<Turnstile> \<^bold>\<not> K i p) \<longrightarrow> (\<^bold>\<not> K i p) \<in> V\<close>
    using \<open>consistent V\<close> \<open>maximal V\<close> exactly_one_in_maximal calculation(1) by auto
  moreover have \<open>(\<^bold>\<not> K i p) \<in> V \<longrightarrow> Kripke pi reach, V \<Turnstile> \<^bold>\<not> K i p\<close>
    using \<open>consistent V\<close> \<open>maximal V\<close> calculation(2) exactly_one_in_maximal by auto
  ultimately show ?case
    by blast
qed

subsection \<open>Completeness\<close>

lemma imply_completeness:
  assumes valid: \<open>\<forall>(M :: ('i, ('i :: countable) fm set) kripke) s.
    list_all (\<lambda>q. M, s \<Turnstile> q) G \<longrightarrow> M, s \<Turnstile> p\<close>
  shows \<open>\<turnstile> imply G p\<close>
proof (rule K_Boole, rule ccontr)
  assume \<open>\<not> \<turnstile> imply ((\<^bold>\<not> p) # G) \<^bold>\<bottom>\<close>

  let ?S = \<open>set ((\<^bold>\<not> p) # G)\<close>
  let ?V = \<open>Extend ?S from_nat\<close>
  let ?M = \<open>Kripke pi reach\<close>

  have \<open>consistent ?S\<close>
    unfolding consistent_def using \<open>\<not> \<turnstile> imply ((\<^bold>\<not> p) # G) \<^bold>\<bottom>\<close> K_imply_weaken by blast
  then have \<open>consistent ?V\<close>
    using consistent_Extend by blast

  have \<open>maximal ?V\<close>
    using Extend_maximal surj_from_nat by blast

  { fix x
    assume \<open>x \<in> ?S\<close>
    then have \<open>x \<in> ?V\<close>
      using Extend_subset by blast
    then have \<open>?M, ?V \<Turnstile> x\<close>
      using model_existence \<open>consistent ?V\<close> \<open>maximal ?V\<close> by blast }
  then have \<open>?M, ?V \<Turnstile> (\<^bold>\<not> p)\<close> \<open>list_all (\<lambda>p. ?M, ?V \<Turnstile> p) G\<close>
    unfolding list_all_def by fastforce+
  then have \<open>?M, ?V \<Turnstile> p\<close>
    using valid by blast
  then show False
    using \<open>?M, ?V \<Turnstile> (\<^bold>\<not> p)\<close> by simp
qed

theorem completeness:
  assumes \<open>\<forall>(M :: ('i :: countable, 'i fm set) kripke) s. M, s \<Turnstile> p\<close>
  shows \<open>\<turnstile> p\<close>
  using assms imply_completeness[where G=\<open>[]\<close>] by auto

section \<open>Main Result\<close> \<comment> \<open>System K is sound and complete\<close>

abbreviation \<open>valid p \<equiv> \<forall>(M :: (nat, nat s_max) kripke) s. M, s \<Turnstile> p\<close>

theorem main: \<open>valid p \<longleftrightarrow> \<turnstile> p\<close>
proof
  assume \<open>valid p\<close>
  with completeness show \<open>\<turnstile> p\<close>
    by blast
next
  assume \<open>\<turnstile> p\<close>
  with soundness show \<open>valid p\<close>
    by (intro allI)
qed

corollary \<open>valid p \<longrightarrow> M, s \<Turnstile> p\<close>
proof
  assume \<open>valid p\<close>
  then have \<open>\<turnstile> p\<close>
    unfolding main .
  with soundness show \<open>M, s \<Turnstile> p\<close> .
qed

section \<open>Acknowledgements\<close>

text \<open>
The formalization is inspired by work by Berghofer, which also formalizes Henkin-style completeness.

  \<^item> Stefan Berghofer:
  First-Order Logic According to Fitting.
  \<^url>\<open>https://www.isa-afp.org/entries/FOL-Fitting.shtml\<close>
\<close>

end
