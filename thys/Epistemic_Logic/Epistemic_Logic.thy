(*
  File:      Epistemic_Logic.thy
  Author:    Asta Halkjær From

  This work is a formalization of epistemic logic with countably many agents.
  It includes proofs of soundness and completeness for the axiom system K.
  The completeness proof is based on the textbook "Reasoning About Knowledge"
  by Fagin, Halpern, Moses and Vardi (MIT Press 1995).
  The extensions of system K (T, KB, K4, S4, S5) and their completeness proofs
  are based on the textbook "Modal Logic" by Blackburn, de Rijke and Venema
  (Cambridge University Press 2001).
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

abbreviation \<open>L i p \<equiv> \<^bold>\<not> K i (\<^bold>\<not> p)\<close>

section \<open>Semantics\<close>

datatype ('i, 'w) kripke =
  Kripke (\<W>: \<open>'w set\<close>) (\<pi>: \<open>'w \<Rightarrow> id \<Rightarrow> bool\<close>) (\<K>: \<open>'i \<Rightarrow> 'w \<Rightarrow> 'w set\<close>)

primrec semantics :: \<open>('i, 'w) kripke \<Rightarrow> 'w \<Rightarrow> 'i fm \<Rightarrow> bool\<close>
  ("_, _ \<Turnstile> _" [50, 50] 50) where
  \<open>(M, w \<Turnstile> \<^bold>\<bottom>) = False\<close>
| \<open>(M, w \<Turnstile> Pro x) = \<pi> M w x\<close>
| \<open>(M, w \<Turnstile> (p \<^bold>\<or> q)) = ((M, w \<Turnstile> p) \<or> (M, w \<Turnstile> q))\<close>
| \<open>(M, w \<Turnstile> (p \<^bold>\<and> q)) = ((M, w \<Turnstile> p) \<and> (M, w \<Turnstile> q))\<close>
| \<open>(M, w \<Turnstile> (p \<^bold>\<longrightarrow> q)) = ((M, w \<Turnstile> p) \<longrightarrow> (M, w \<Turnstile> q))\<close>
| \<open>(M, w \<Turnstile> K i p) = (\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> p)\<close>

section \<open>S5 Axioms\<close>

definition reflexive :: \<open>('i, 'w) kripke \<Rightarrow> bool\<close> where
  \<open>reflexive M \<equiv> \<forall>i. \<forall>w \<in> \<W> M. w \<in> \<K> M i w\<close>

definition symmetric :: \<open>('i, 'w) kripke \<Rightarrow> bool\<close> where
  \<open>symmetric M \<equiv> \<forall>i. \<forall>v \<in> \<W> M. \<forall>w \<in> \<W> M. v \<in> \<K> M i w \<longleftrightarrow> w \<in> \<K> M i v\<close>

definition transitive :: \<open>('i, 'w) kripke \<Rightarrow> bool\<close> where
  \<open>transitive M \<equiv> \<forall>i. \<forall>u \<in> \<W> M. \<forall>v \<in> \<W> M. \<forall>w \<in> \<W> M.
    w \<in> \<K> M i v \<and> u \<in> \<K> M i w \<longrightarrow> u \<in> \<K> M i v\<close>

abbreviation refltrans :: \<open>('i, 'w) kripke \<Rightarrow> bool\<close> where
  \<open>refltrans M \<equiv> reflexive M \<and> transitive M\<close>

abbreviation equivalence :: \<open>('i, 'w) kripke \<Rightarrow> bool\<close> where
  \<open>equivalence M \<equiv> reflexive M \<and> symmetric M \<and> transitive M\<close>

lemma Imp_intro [intro]: \<open>(M, w \<Turnstile> p \<Longrightarrow> M, w \<Turnstile> q) \<Longrightarrow> M, w \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
  by simp

theorem distribution: \<open>M, w \<Turnstile> (K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i q)\<close>
proof
  assume \<open>M, w \<Turnstile> (K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q))\<close>
  then have \<open>M, w \<Turnstile> K i p\<close> \<open>M, w \<Turnstile> K i (p \<^bold>\<longrightarrow> q)\<close>
    by simp_all
  then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> p\<close> \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
    by simp_all
  then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> q\<close>
    by simp
  then show \<open>M, w \<Turnstile> K i q\<close>
    by simp
qed

theorem generalization:
  assumes valid: \<open>\<forall>(M :: ('i, 'w) kripke) w. M, w \<Turnstile> p\<close>
  shows \<open>(M :: ('i, 'w) kripke), w \<Turnstile> K i p\<close>
proof -
  have \<open>\<forall>w' \<in> \<K> M i w. M, w' \<Turnstile> p\<close>
    using valid by blast
  then show \<open>M, w \<Turnstile> K i p\<close>
    by simp
qed

theorem truth:
  assumes \<open>reflexive M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>M, w \<Turnstile> (K i p \<^bold>\<longrightarrow> p)\<close>
proof
  assume \<open>M, w \<Turnstile> K i p\<close>
  then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> p\<close>
    by simp
  moreover have \<open>w \<in> \<K> M i w\<close>
    using \<open>reflexive M\<close> \<open>w \<in> \<W> M\<close> unfolding reflexive_def by blast
  ultimately show \<open>M, w \<Turnstile> p\<close>
    using \<open>w \<in> \<W> M\<close> by simp
qed

theorem pos_introspection:
  assumes \<open>transitive M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>M, w \<Turnstile> (K i p \<^bold>\<longrightarrow> K i (K i p))\<close>
proof
  assume \<open>M, w \<Turnstile> K i p\<close>
  then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> p\<close>
    by simp
  then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. \<forall>u \<in> \<W> M \<inter> \<K> M i v. M, u \<Turnstile> p\<close>
    using \<open>transitive M\<close> \<open>w \<in> \<W> M\<close> unfolding transitive_def by blast
  then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> K i p\<close>
    by simp
  then show \<open>M, w \<Turnstile> K i (K i p)\<close>
    by simp
qed

theorem neg_introspection:
  assumes \<open>symmetric M\<close> \<open>transitive M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>M, w \<Turnstile> (\<^bold>\<not> K i p \<^bold>\<longrightarrow> K i (\<^bold>\<not> K i p))\<close>
proof
  assume \<open>M, w \<Turnstile> \<^bold>\<not> (K i p)\<close>
  then obtain u where \<open>u \<in> \<K> M i w\<close> \<open>\<not> (M, u \<Turnstile> p)\<close> \<open>u \<in> \<W> M\<close>
    by auto
  moreover have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. u \<in> \<W> M \<inter> \<K> M i v\<close>
    using \<open>u \<in> \<K> M i w\<close> \<open>symmetric M\<close> \<open>transitive M\<close> \<open>u \<in> \<W> M\<close> \<open>w \<in> \<W> M\<close>
    unfolding symmetric_def transitive_def by blast
  ultimately have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> \<^bold>\<not> K i p\<close>
    by auto
  then show \<open>M, w \<Turnstile> K i (\<^bold>\<not> K i p)\<close>
    by simp
qed

section \<open>Normal Modal Logic\<close>

primrec eval :: \<open>(id \<Rightarrow> bool) \<Rightarrow> ('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm \<Rightarrow> bool\<close> where
  \<open>eval _ _ \<^bold>\<bottom> = False\<close>
| \<open>eval g _ (Pro x) = g x\<close>
| \<open>eval g h (p \<^bold>\<or> q) = (eval g h p \<or> eval g h q)\<close>
| \<open>eval g h (p \<^bold>\<and> q) = (eval g h p \<and> eval g h q)\<close>
| \<open>eval g h (p \<^bold>\<longrightarrow> q) = (eval g h p \<longrightarrow> eval g h q)\<close>
| \<open>eval _ h (K i p) = h (K i p)\<close>

abbreviation \<open>tautology p \<equiv> \<forall>g h. eval g h p\<close>

inductive AK :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm \<Rightarrow> bool\<close> ("_ \<turnstile> _" [50, 50] 50)
  for A :: \<open>'i fm \<Rightarrow> bool\<close> where
    A1: \<open>tautology p \<Longrightarrow> A \<turnstile> p\<close>
  | A2: \<open>A \<turnstile> (K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i q)\<close>
  | Ax: \<open>A p \<Longrightarrow> A \<turnstile> p\<close>
  | R1: \<open>A \<turnstile> p \<Longrightarrow> A \<turnstile> (p \<^bold>\<longrightarrow> q) \<Longrightarrow> A \<turnstile> q\<close>
  | R2: \<open>A \<turnstile> p \<Longrightarrow> A \<turnstile> K i p\<close>

section \<open>Soundness\<close>

lemma eval_semantics: \<open>eval (pi w) (\<lambda>q. Kripke W pi r, w \<Turnstile> q) p = (Kripke W pi r, w \<Turnstile> p)\<close>
  by (induct p) simp_all

lemma tautology:
  assumes \<open>tautology p\<close>
  shows \<open>M, w \<Turnstile> p\<close>
proof -
  from assms have \<open>eval (g w) (\<lambda>q. Kripke W g r, w \<Turnstile> q) p\<close> for W g r
    by simp
  then have \<open>Kripke W g r, w \<Turnstile> p\<close> for W g r
    using eval_semantics by fast
  then show \<open>M, w \<Turnstile> p\<close>
    by (metis kripke.collapse)
qed

theorem soundness:
  fixes M :: \<open>('i, 'w) kripke\<close>
  assumes \<open>\<And>(M :: ('i, 'w) kripke) w p. A p \<Longrightarrow> P M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  shows \<open>A \<turnstile> p \<Longrightarrow> P M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  by (induct p arbitrary: w rule: AK.induct) (auto simp: assms tautology)

section \<open>Derived rules\<close>

lemma K_A2': \<open>A \<turnstile> (K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i p \<^bold>\<longrightarrow> K i q)\<close>
proof -
  have \<open>A \<turnstile> (K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i q)\<close>
    using A2 by fast
  moreover have \<open>A \<turnstile> ((P \<^bold>\<and> Q \<^bold>\<longrightarrow> R) \<^bold>\<longrightarrow> (Q \<^bold>\<longrightarrow> P \<^bold>\<longrightarrow> R))\<close> for P Q R
    by (simp add: A1)
  ultimately show ?thesis
    using R1 by fast
qed

lemma K_map:
  assumes \<open>A \<turnstile> (p \<^bold>\<longrightarrow> q)\<close>
  shows \<open>A \<turnstile> (K i p \<^bold>\<longrightarrow> K i q)\<close>
proof -
  note \<open>A \<turnstile> (p \<^bold>\<longrightarrow> q)\<close>
  then have \<open>A \<turnstile> K i (p \<^bold>\<longrightarrow> q)\<close>
    using R2 by fast
  moreover have \<open>A \<turnstile> (K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i p \<^bold>\<longrightarrow> K i q)\<close>
    using K_A2' by fast
  ultimately show ?thesis
    using R1 by fast
qed

lemma K_LK: \<open>A \<turnstile> (L i (\<^bold>\<not> p) \<^bold>\<longrightarrow> \<^bold>\<not> K i p)\<close>
proof -
  have \<open>A \<turnstile> (p \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> p)\<close>
    by (simp add: A1)
  moreover have \<open>A \<turnstile> ((P \<^bold>\<longrightarrow> Q) \<^bold>\<longrightarrow> (\<^bold>\<not> Q \<^bold>\<longrightarrow> \<^bold>\<not> P))\<close> for P Q
    using A1 by force
  ultimately show ?thesis
    using K_map R1 by fast
qed

primrec imply :: \<open>'i fm list \<Rightarrow> 'i fm \<Rightarrow> 'i fm\<close> where
  \<open>imply [] q = q\<close>
| \<open>imply (p # ps) q = (p \<^bold>\<longrightarrow> imply ps q)\<close>

lemma K_imply_head: \<open>A \<turnstile> imply (p # ps) p\<close>
proof -
  have \<open>tautology (imply (p # ps) p)\<close>
    by (induct ps) simp_all
  then show ?thesis
    using A1 by blast
qed

lemma K_imply_Cons:
  assumes \<open>A \<turnstile> imply ps q\<close>
  shows \<open>A \<turnstile> imply (p # ps) q\<close>
proof -
  have \<open>A \<turnstile> (imply ps q \<^bold>\<longrightarrow> imply (p # ps) q)\<close>
    by (simp add: A1)
  with R1 assms show ?thesis .
qed

lemma K_right_mp:
  assumes \<open>A \<turnstile> imply ps p\<close> \<open>A \<turnstile> imply ps (p \<^bold>\<longrightarrow> q)\<close>
  shows \<open>A \<turnstile> imply ps q\<close>
proof -
  have \<open>tautology (imply ps p \<^bold>\<longrightarrow> imply ps (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> imply ps q)\<close>
    by (induct ps) simp_all
  with A1 have \<open>A \<turnstile> (imply ps p \<^bold>\<longrightarrow> imply ps (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> imply ps q)\<close> .
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
  assumes \<open>A \<turnstile> imply ps q\<close> \<open>set ps \<subseteq> set ps'\<close>
  shows \<open>A \<turnstile> imply ps' q\<close>
proof -
  have \<open>tautology (imply ps q \<^bold>\<longrightarrow> imply ps' q)\<close>
    using \<open>set ps \<subseteq> set ps'\<close> tautology_imply_superset by blast
  then have \<open>A \<turnstile> (imply ps q \<^bold>\<longrightarrow> imply ps' q)\<close>
    using A1 by blast
  then show ?thesis
    using \<open>A \<turnstile> imply ps q\<close> R1 by blast
qed

lemma imply_append: \<open>imply (ps @ ps') q = imply ps (imply ps' q)\<close>
  by (induct ps) simp_all

lemma K_ImpI:
  assumes \<open>A \<turnstile> imply (p # G) q\<close>
  shows \<open>A \<turnstile> imply G (p \<^bold>\<longrightarrow> q)\<close>
proof -
  have \<open>set (p # G) \<subseteq> set (G @ [p])\<close>
    by simp
  then have \<open>A \<turnstile> imply (G @ [p]) q\<close>
    using assms K_imply_weaken by blast
  then have \<open>A \<turnstile> imply G (imply [p] q)\<close>
    using imply_append by metis
  then show ?thesis
    by simp
qed

lemma K_Boole:
  assumes \<open>A \<turnstile> imply ((\<^bold>\<not> p) # G) \<^bold>\<bottom>\<close>
  shows \<open>A \<turnstile> imply G p\<close>
proof -
  have \<open>A \<turnstile> imply G (\<^bold>\<not> \<^bold>\<not> p)\<close>
    using assms K_ImpI by blast
  moreover have \<open>tautology (imply G (\<^bold>\<not> \<^bold>\<not> p) \<^bold>\<longrightarrow> imply G p)\<close>
    by (induct G) simp_all
  then have \<open>A \<turnstile> (imply G (\<^bold>\<not> \<^bold>\<not> p) \<^bold>\<longrightarrow> imply G p)\<close>
    using A1 by blast
  ultimately show ?thesis
    using R1 by blast
qed

lemma K_DisE:
  assumes \<open>A \<turnstile> imply (p # G) r\<close> \<open>A \<turnstile> imply (q # G) r\<close> \<open>A \<turnstile> imply G (p \<^bold>\<or> q)\<close>
  shows \<open>A \<turnstile> imply G r\<close>
proof -
  have \<open>tautology (imply (p # G) r \<^bold>\<longrightarrow> imply (q # G) r \<^bold>\<longrightarrow> imply G (p \<^bold>\<or> q) \<^bold>\<longrightarrow> imply G r)\<close>
    by (induct G) auto
  then have \<open>A \<turnstile> (imply (p # G) r \<^bold>\<longrightarrow> imply (q # G) r \<^bold>\<longrightarrow> imply G (p \<^bold>\<or> q) \<^bold>\<longrightarrow> imply G r)\<close>
    using A1 by blast
  then show ?thesis
    using assms R1 by blast
qed

lemma K_mp: \<open>A \<turnstile> imply (p # (p \<^bold>\<longrightarrow> q) # G) q\<close>
  by (meson K_imply_head K_imply_weaken K_right_mp set_subset_Cons)

lemma K_swap:
  assumes \<open>A \<turnstile> imply (p # q # G) r\<close>
  shows \<open>A \<turnstile> imply (q # p # G) r\<close>
  using assms K_ImpI by (metis imply.simps(1-2))

lemma K_DisL:
  assumes \<open>A \<turnstile> imply (p # ps) q\<close> \<open>A \<turnstile> imply (p' # ps) q\<close>
  shows \<open>A \<turnstile> imply ((p \<^bold>\<or> p') # ps) q\<close>
proof -
  have \<open>A \<turnstile> imply (p # (p \<^bold>\<or> p') # ps) q\<close> \<open>A \<turnstile> imply (p' # (p \<^bold>\<or> p') # ps) q\<close>
    using assms K_swap K_imply_Cons by blast+
  moreover have \<open>A \<turnstile> imply ((p \<^bold>\<or> p') # ps) (p \<^bold>\<or> p')\<close>
    using K_imply_head by blast
  ultimately show ?thesis
    using K_DisE by blast
qed

lemma K_distrib_K_imp:
  assumes \<open>A \<turnstile> K i (imply G q)\<close>
  shows \<open>A \<turnstile> imply (map (K i) G) (K i q)\<close>
proof -
  have \<open>A \<turnstile> (K i (imply G q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q))\<close>
  proof (induct G)
    case Nil
    then show ?case
      by (simp add: A1)
  next
    case (Cons a G)
    have \<open>A \<turnstile> (K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> K i (imply G q))\<close>
      by (simp add: A2)
    moreover have
      \<open>A \<turnstile> ((K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> K i (imply G q)) \<^bold>\<longrightarrow>
        (K i (imply G q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)) \<^bold>\<longrightarrow>
        (K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)))\<close>
      by (simp add: A1)
    ultimately have \<open>A \<turnstile> (K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q))\<close>
      using Cons R1 by blast
    moreover have
      \<open>A \<turnstile> ((K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)) \<^bold>\<longrightarrow>
        (K i (imply (a # G) q) \<^bold>\<longrightarrow> K i a \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)))\<close>
      by (simp add: A1)
    ultimately have \<open>A \<turnstile> (K i (imply (a # G) q) \<^bold>\<longrightarrow> K i a \<^bold>\<longrightarrow> imply (map (K i) G) (K i q))\<close>
      using R1 by blast
    then show ?case
      by simp
  qed
  then show ?thesis
    using assms R1 by blast
qed

section \<open>Completeness\<close>

subsection \<open>Consistent sets\<close>

definition consistent :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm set \<Rightarrow> bool\<close> where
  \<open>consistent A S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> A \<turnstile> imply S' \<^bold>\<bottom>\<close>

lemma inconsistent_subset:
  assumes \<open>consistent A V\<close> \<open>\<not> consistent A ({p} \<union> V)\<close>
  obtains V' where \<open>set V' \<subseteq> V\<close> \<open>A \<turnstile> imply (p # V') \<^bold>\<bottom>\<close>
proof -
  obtain V' where V': \<open>set V' \<subseteq> ({p} \<union> V)\<close> \<open>p \<in> set V'\<close> \<open>A \<turnstile> imply V' \<^bold>\<bottom>\<close>
    using assms unfolding consistent_def by blast
  then have *: \<open>A \<turnstile> imply (p # V') \<^bold>\<bottom>\<close>
    using K_imply_Cons by blast

  let ?S = \<open>removeAll p V'\<close>
  have \<open>set (p # V') \<subseteq> set (p # ?S)\<close>
    by auto
  then have \<open>A \<turnstile> imply (p # ?S) \<^bold>\<bottom>\<close>
    using * K_imply_weaken by blast
  moreover have \<open>set ?S \<subseteq> V\<close>
    using V'(1) by (metis Diff_subset_conv set_removeAll)
  ultimately show ?thesis
    using that by blast
qed

lemma consistent_deriv:
  assumes \<open>consistent A V\<close> \<open>A \<turnstile> p\<close>
  shows \<open>consistent A ({p} \<union> V)\<close>
  using assms by (metis R1 consistent_def imply.simps(2) inconsistent_subset)

lemma consistent_consequent:
  assumes \<open>consistent A V\<close> \<open>p \<in> V\<close> \<open>A \<turnstile> (p \<^bold>\<longrightarrow> q)\<close>
  shows \<open>consistent A ({q} \<union> V)\<close>
proof -
  have \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> A \<turnstile> imply (p # V') \<^bold>\<bottom>\<close>
    using \<open>consistent A V\<close> \<open>p \<in> V\<close> unfolding consistent_def
    by (metis insert_subset list.simps(15))
  then have \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> A \<turnstile> imply (q # V') \<^bold>\<bottom>\<close>
    using \<open>A \<turnstile> (p \<^bold>\<longrightarrow> q)\<close> K_imply_head K_right_mp by (metis imply.simps(1-2))
  then show ?thesis
    using \<open>consistent A V\<close> inconsistent_subset by metis
qed

lemma consistent_consequent':
  assumes \<open>consistent A V\<close> \<open>p \<in> V\<close> \<open>tautology (p \<^bold>\<longrightarrow> q)\<close>
  shows \<open>consistent A ({q} \<union> V)\<close>
  using assms consistent_consequent A1 by blast

lemma consistent_disjuncts:
  assumes \<open>consistent A V\<close> \<open>(p \<^bold>\<or> q) \<in> V\<close>
  shows \<open>consistent A ({p} \<union> V) \<or> consistent A ({q} \<union> V)\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then have \<open>\<not> consistent A ({p} \<union> V)\<close> \<open>\<not> consistent A ({q} \<union> V)\<close>
    by blast+

  then obtain S' T' where
    S': \<open>set S' \<subseteq> V\<close> \<open>A \<turnstile> imply (p # S') \<^bold>\<bottom>\<close> and
    T': \<open>set T' \<subseteq> V\<close> \<open>A \<turnstile> imply (q # T') \<^bold>\<bottom>\<close>
    using \<open>consistent A V\<close> inconsistent_subset by metis

  from S' have p: \<open>A \<turnstile> imply (p # S' @ T') \<^bold>\<bottom>\<close>
    by (metis K_imply_weaken Un_upper1 append_Cons set_append)
  moreover from T' have q: \<open>A \<turnstile> imply (q # S' @ T') \<^bold>\<bottom>\<close>
    by (metis K_imply_head K_right_mp R1 imply.simps(2) imply_append)
  ultimately have \<open>A \<turnstile> imply ((p \<^bold>\<or> q) # S' @ T') \<^bold>\<bottom>\<close>
    using K_DisL by blast
  then have \<open>A \<turnstile> imply (S' @ T') \<^bold>\<bottom>\<close>
    using S'(1) T'(1) p q \<open>consistent A V\<close> \<open>(p \<^bold>\<or> q) \<in> V\<close> unfolding consistent_def
    by (metis Un_subset_iff insert_subset list.simps(15) set_append)
  moreover have \<open>set (S' @ T') \<subseteq> V\<close>
    by (simp add: S'(1) T'(1))
  ultimately show False
    using \<open>consistent A V\<close> unfolding consistent_def by blast
qed

lemma exists_finite_inconsistent:
  assumes \<open>\<not> consistent A ({\<^bold>\<not> p} \<union> V)\<close>
  obtains W where \<open>{\<^bold>\<not> p} \<union> W \<subseteq> {\<^bold>\<not> p} \<union> V\<close> \<open>(\<^bold>\<not> p) \<notin> W\<close> \<open>finite W\<close> \<open>\<not> consistent A ({\<^bold>\<not> p} \<union> W)\<close>
proof -
  obtain W' where W': \<open>set W' \<subseteq> {\<^bold>\<not> p} \<union> V\<close> \<open>A \<turnstile> imply W' \<^bold>\<bottom>\<close>
    using assms unfolding consistent_def by blast
  let ?S = \<open>removeAll (\<^bold>\<not> p) W'\<close>
  have \<open>\<not> consistent A ({\<^bold>\<not> p} \<union> set ?S)\<close>
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
  assumes \<open>\<not> consistent A ({\<^bold>\<not> p} \<union> set G)\<close>
  shows \<open>A \<turnstile> imply G p\<close>
  using assms K_Boole K_imply_weaken unfolding consistent_def
  by (metis insert_is_Un list.simps(15))

subsection \<open>Maximal consistent sets\<close>

definition maximal :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm set \<Rightarrow> bool\<close> where
  \<open>maximal A S \<equiv> \<forall>p. p \<notin> S \<longrightarrow> \<not> consistent A ({p} \<union> S)\<close>

theorem deriv_in_maximal:
  assumes \<open>consistent A V\<close> \<open>maximal A V\<close> \<open>A \<turnstile> p\<close>
  shows \<open>p \<in> V\<close>
  using assms R1 inconsistent_subset unfolding consistent_def maximal_def
  by (metis imply.simps(2))

theorem exactly_one_in_maximal:
  assumes \<open>consistent A V\<close> \<open>maximal A V\<close>
  shows \<open>p \<in> V \<longleftrightarrow> (\<^bold>\<not> p) \<notin> V\<close>
proof
  assume \<open>p \<in> V\<close>
  then show \<open>(\<^bold>\<not> p) \<notin> V\<close>
    using assms K_mp unfolding consistent_def maximal_def
    by (metis empty_subsetI insert_subset list.set(1) list.simps(15))
next
  assume \<open>(\<^bold>\<not> p) \<notin> V\<close>
  have \<open>A \<turnstile> (p \<^bold>\<or> \<^bold>\<not> p)\<close>
    by (simp add: A1)
  then have \<open>(p \<^bold>\<or> \<^bold>\<not> p) \<in> V\<close>
    using assms deriv_in_maximal by blast
  then have \<open>consistent A ({p} \<union> V) \<or> consistent A ({\<^bold>\<not> p} \<union> V)\<close>
    using assms consistent_disjuncts by blast
  then show \<open>p \<in> V\<close>
    using \<open>maximal A V\<close> \<open>(\<^bold>\<not> p) \<notin> V\<close> unfolding maximal_def by blast
qed

theorem consequent_in_maximal:
  assumes \<open>consistent A V\<close> \<open>maximal A V\<close> \<open>p \<in> V\<close> \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close>
  shows \<open>q \<in> V\<close>
proof -
  have \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> A \<turnstile> imply (p # (p \<^bold>\<longrightarrow> q) # V') \<^bold>\<bottom>\<close>
    using \<open>consistent A V\<close> \<open>p \<in> V\<close> \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close> unfolding consistent_def
    by (metis insert_subset list.simps(15))
  then have \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> A \<turnstile> imply (q # V') \<^bold>\<bottom>\<close>
    by (meson K_mp K_ImpI K_imply_weaken K_right_mp set_subset_Cons)
  then have \<open>consistent A ({q} \<union> V)\<close>
    using \<open>consistent A V\<close> inconsistent_subset by metis
  then show ?thesis
    using \<open>maximal A V\<close> unfolding maximal_def by fast
qed

theorem ax_in_maximal:
  assumes \<open>consistent A V\<close> \<open>maximal A V\<close> \<open>A p\<close>
  shows \<open>p \<in> V\<close>
  using assms deriv_in_maximal Ax by blast

theorem mcs_properties:
  assumes \<open>consistent A V\<close> and \<open>maximal A V\<close>
  shows \<open>A \<turnstile> p \<Longrightarrow> p \<in> V\<close>
    and \<open>p \<in> V \<longleftrightarrow> (\<^bold>\<not> p) \<notin> V\<close>
    and \<open>p \<in> V \<Longrightarrow> (p \<^bold>\<longrightarrow> q) \<in> V \<Longrightarrow> q \<in> V\<close>
  using assms deriv_in_maximal exactly_one_in_maximal consequent_in_maximal by blast+

subsection \<open>Lindenbaum extension\<close>

instantiation fm :: (countable) countable begin
instance by countable_datatype
end

primrec extend :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm set \<Rightarrow> (nat \<Rightarrow> 'i fm) \<Rightarrow> nat \<Rightarrow> 'i fm set\<close> where
  \<open>extend A S f 0 = S\<close> |
  \<open>extend A S f (Suc n) =
    (if consistent A ({f n} \<union> extend A S f n)
     then {f n} \<union> extend A S f n
     else extend A S f n)\<close>

definition Extend :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm set \<Rightarrow> (nat \<Rightarrow> 'i fm) \<Rightarrow> 'i fm set\<close> where
  \<open>Extend A S f \<equiv> \<Union>n. extend A S f n\<close>

lemma Extend_subset: \<open>S \<subseteq> Extend A S f\<close>
  unfolding Extend_def using Union_upper extend.simps(1) range_eqI
  by metis

lemma extend_bound: \<open>(\<Union>n \<le> m. extend A S f n) = extend A S f m\<close>
  by (induct m) (simp_all add: atMost_Suc)

lemma consistent_extend: \<open>consistent A S \<Longrightarrow> consistent A (extend A S f n)\<close>
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
  assumes \<open>consistent A S\<close>
  shows \<open>consistent A (Extend A S f)\<close>
  unfolding Extend_def
proof (rule ccontr)
  assume \<open>\<not> consistent A (\<Union>n. extend A S f n)\<close>
  then obtain S' where \<open>A \<turnstile> imply S' \<^bold>\<bottom>\<close> \<open>set S' \<subseteq> (\<Union>n. extend A S f n)\<close>
    unfolding consistent_def by blast
  then obtain m where \<open>set S' \<subseteq> (\<Union>n \<le> m. extend A S f n)\<close>
    using UN_finite_bound by (metis List.finite_set)
  then have \<open>set S' \<subseteq> extend A S f m\<close>
    using extend_bound by blast
  moreover have \<open>consistent A (extend A S f m)\<close>
    using assms consistent_extend by blast
  ultimately show False
    unfolding consistent_def using \<open>A \<turnstile> imply S' \<^bold>\<bottom>\<close> by blast
qed

lemma maximal_Extend:
  assumes \<open>surj f\<close>
  shows \<open>maximal A (Extend A S f)\<close>
proof (rule ccontr)
  assume \<open>\<not> maximal A (Extend A S f)\<close>
  then obtain p where \<open>p \<notin> Extend A S f\<close> \<open>consistent A ({p} \<union> Extend A S f)\<close>
    unfolding maximal_def using assms consistent_Extend by blast
  obtain k where n: \<open>f k = p\<close>
    using \<open>surj f\<close> unfolding surj_def by metis
  then have \<open>p \<notin> extend A S f (Suc k)\<close>
    using \<open>p \<notin> Extend A S f\<close> unfolding Extend_def by blast
  then have \<open>\<not> consistent A ({p} \<union> extend A S f k)\<close>
    using n by fastforce
  moreover have \<open>{p} \<union> extend A S f k \<subseteq> {p} \<union> Extend A S f\<close>
    unfolding Extend_def by blast
  ultimately have \<open>\<not> consistent A ({p} \<union> Extend A S f)\<close>
    unfolding consistent_def by fastforce
  then show False
    using \<open>consistent A ({p} \<union> Extend A S f)\<close> by blast
qed

lemma maximal_extension:
  fixes V :: \<open>('i :: countable) fm set\<close>
  assumes \<open>consistent A V\<close>
  obtains W where \<open>V \<subseteq> W\<close> \<open>consistent A W\<close> \<open>maximal A W\<close>
proof -
  let ?W = \<open>Extend A V from_nat\<close>
  have \<open>V \<subseteq> ?W\<close>
    using Extend_subset by blast
  moreover have \<open>consistent A ?W\<close>
    using assms consistent_Extend by blast
  moreover have \<open>maximal A ?W\<close>
    using assms maximal_Extend surj_from_nat by blast
  ultimately show ?thesis
    using that by blast
qed

subsection \<open>Canonical model\<close>

abbreviation pi :: \<open>'i fm set \<Rightarrow> id \<Rightarrow> bool\<close> where
  \<open>pi V x \<equiv> Pro x \<in> V\<close>

abbreviation known :: \<open>'i fm set \<Rightarrow> 'i \<Rightarrow> 'i fm set\<close> where
  \<open>known V i \<equiv> {p. K i p \<in> V}\<close>

abbreviation reach :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i \<Rightarrow> 'i fm set \<Rightarrow> 'i fm set set\<close> where
  \<open>reach A i V \<equiv> {W. known V i \<subseteq> W}\<close>

abbreviation mcss :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm set set\<close> where
  \<open>mcss A \<equiv> {W. consistent A W \<and> maximal A W}\<close>

abbreviation canonical :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> ('i, 'i fm set) kripke\<close> where
  \<open>canonical A \<equiv> Kripke (mcss A) pi (reach A)\<close>

lemma truth_lemma:
  fixes A and p :: \<open>('i :: countable) fm\<close>
  defines \<open>M \<equiv> canonical A\<close>
  assumes \<open>consistent A V\<close> and \<open>maximal A V\<close>
  shows \<open>(p \<in> V \<longleftrightarrow> M, V \<Turnstile> p) \<and> ((\<^bold>\<not> p) \<in> V \<longleftrightarrow> M, V \<Turnstile> \<^bold>\<not> p)\<close>
  using assms unfolding M_def
proof (induct p arbitrary: V)
  case FF
  then show ?case
  proof (intro conjI impI iffI)
    assume \<open>\<^bold>\<bottom> \<in> V\<close>
    then have False
      using \<open>consistent A V\<close> K_imply_head unfolding consistent_def
      by (metis bot.extremum insert_subset list.set(1) list.simps(15))
    then show \<open>canonical A, V \<Turnstile> \<^bold>\<bottom>\<close> ..
  next
    assume \<open>canonical A, V \<Turnstile> \<^bold>\<not> \<^bold>\<bottom>\<close>
    then show \<open>(\<^bold>\<not> \<^bold>\<bottom>) \<in> V\<close>
      using \<open>consistent A V\<close> \<open>maximal A V\<close> unfolding maximal_def
      by (meson K_Boole inconsistent_subset consistent_def)
  qed simp_all
next
  case (Pro x)
  then show ?case
  proof (intro conjI impI iffI)
    assume \<open>(\<^bold>\<not> Pro x) \<in> V\<close>
    then show \<open>canonical A, V \<Turnstile> \<^bold>\<not> Pro x\<close>
      using \<open>consistent A V\<close> \<open>maximal A V\<close> exactly_one_in_maximal by auto
  next
    assume \<open>canonical A, V \<Turnstile> \<^bold>\<not> Pro x\<close>
    then show \<open>(\<^bold>\<not> Pro x) \<in> V\<close>
      using \<open>consistent A V\<close> \<open>maximal A V\<close> exactly_one_in_maximal by auto
  qed (simp_all add: \<open>maximal A V\<close> maximal_def)
next
  case (Dis p q)
  have \<open>(p \<^bold>\<or> q) \<in> V \<longrightarrow> canonical A, V \<Turnstile> (p \<^bold>\<or> q)\<close>
  proof
    assume \<open>(p \<^bold>\<or> q) \<in> V\<close>
    then have \<open>consistent A ({p} \<union> V) \<or> consistent A ({q} \<union> V)\<close>
      using \<open>consistent A V\<close> consistent_disjuncts by blast
    then have \<open>p \<in> V \<or> q \<in> V\<close>
      using \<open>maximal A V\<close> unfolding maximal_def by fast
    then show \<open>canonical A, V \<Turnstile> (p \<^bold>\<or> q)\<close>
      using Dis by simp
  qed
  moreover have \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) \<in> V \<longrightarrow> canonical A, V \<Turnstile> \<^bold>\<not> (p \<^bold>\<or> q)\<close>
  proof
    assume \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) \<in> V\<close>
    then have \<open>consistent A ({\<^bold>\<not> q} \<union> V)\<close> \<open>consistent A ({\<^bold>\<not> p} \<union> V)\<close>
      using \<open>consistent A V\<close> consistent_consequent' by fastforce+
    then have \<open>(\<^bold>\<not> p) \<in> V\<close> \<open>(\<^bold>\<not> q) \<in> V\<close>
      using \<open>maximal A V\<close> unfolding maximal_def by fast+
    then show \<open>canonical A, V \<Turnstile> \<^bold>\<not> (p \<^bold>\<or> q)\<close>
      using Dis by simp
  qed
  ultimately show ?case
    using exactly_one_in_maximal Dis by auto
next
  case (Con p q)
  have \<open>(p \<^bold>\<and> q) \<in> V \<longrightarrow> canonical A, V \<Turnstile> (p \<^bold>\<and> q)\<close>
  proof
    assume \<open>(p \<^bold>\<and> q) \<in> V\<close>
    then have \<open>consistent A ({p} \<union> V)\<close> \<open>consistent A ({q} \<union> V)\<close>
      using \<open>consistent A V\<close> consistent_consequent' by fastforce+
    then have \<open>p \<in> V\<close> \<open>q \<in> V\<close>
      using \<open>maximal A V\<close> unfolding maximal_def by fast+
    then show \<open>canonical A, V \<Turnstile> (p \<^bold>\<and> q)\<close>
      using Con by simp
  qed
  moreover have \<open>(\<^bold>\<not> (p \<^bold>\<and> q)) \<in> V \<longrightarrow> canonical A, V \<Turnstile> \<^bold>\<not> (p \<^bold>\<and> q)\<close>
  proof
    assume \<open>(\<^bold>\<not> (p \<^bold>\<and> q)) \<in> V\<close>
    then have \<open>consistent A ({\<^bold>\<not> p \<^bold>\<or> \<^bold>\<not> q} \<union> V)\<close>
      using \<open>consistent A V\<close> consistent_consequent' by fastforce
    then have \<open>consistent A ({\<^bold>\<not> p} \<union> V) \<or> consistent A ({\<^bold>\<not> q} \<union> V)\<close>
      using \<open>consistent A V\<close> \<open>maximal A V\<close> consistent_disjuncts unfolding maximal_def by blast
    then have \<open>(\<^bold>\<not> p) \<in> V \<or> (\<^bold>\<not> q) \<in> V\<close>
      using \<open>maximal A V\<close> unfolding maximal_def by fast
    then show \<open>canonical A, V \<Turnstile> \<^bold>\<not> (p \<^bold>\<and> q)\<close>
      using Con by simp
  qed
  ultimately show ?case
    using exactly_one_in_maximal Con by auto
next
  case (Imp p q)
  have \<open>(p \<^bold>\<longrightarrow> q) \<in> V \<longrightarrow> canonical A, V \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
  proof
    assume \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close>
    then have \<open>consistent A ({\<^bold>\<not> p \<^bold>\<or> q} \<union> V)\<close>
      using \<open>consistent A V\<close> consistent_consequent' by fastforce
    then have \<open>consistent A ({\<^bold>\<not> p} \<union> V) \<or> consistent A ({q} \<union> V)\<close>
      using \<open>consistent A V\<close> \<open>maximal A V\<close> consistent_disjuncts unfolding maximal_def by blast
    then have \<open>(\<^bold>\<not> p) \<in> V \<or> q \<in> V\<close>
      using \<open>maximal A V\<close> unfolding maximal_def by fast
    then show \<open>canonical A, V \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
      using Imp by simp
  qed
  moreover have \<open>(\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) \<in> V \<longrightarrow> canonical A, V \<Turnstile> \<^bold>\<not> (p \<^bold>\<longrightarrow> q)\<close>
  proof
    assume \<open>(\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) \<in> V\<close>
    then have \<open>consistent A ({p} \<union> V)\<close> \<open>consistent A ({\<^bold>\<not> q} \<union> V)\<close>
      using \<open>consistent A V\<close> consistent_consequent' by fastforce+
    then have \<open>p \<in> V\<close> \<open>(\<^bold>\<not> q) \<in> V\<close>
      using \<open>maximal A V\<close> unfolding maximal_def by fast+
    then show \<open>canonical A, V \<Turnstile> \<^bold>\<not> (p \<^bold>\<longrightarrow> q)\<close>
      using Imp by simp
  qed
  ultimately show ?case
    using exactly_one_in_maximal Imp \<open>consistent A V\<close> by auto
next
  case (K i p)
  then have \<open>K i p \<in> V \<longrightarrow> canonical A, V \<Turnstile> K i p\<close>
    by auto
  moreover have \<open>(canonical A, V \<Turnstile> K i p) \<longrightarrow> K i p \<in> V\<close>
  proof (intro allI impI)
    assume \<open>canonical A, V \<Turnstile> K i p\<close>

    have \<open>\<not> consistent A ({\<^bold>\<not> p} \<union> known V i)\<close>
    proof
      assume \<open>consistent A ({\<^bold>\<not> p} \<union> known V i)\<close>
      then obtain W where W: \<open>{\<^bold>\<not> p} \<union> known V i \<subseteq> W\<close> \<open>consistent A W\<close> \<open>maximal A W\<close>
        using \<open>consistent A V\<close> maximal_extension by blast
      then have \<open>canonical A, W \<Turnstile> \<^bold>\<not> p\<close>
        using K \<open>consistent A V\<close> by blast
      moreover have \<open>W \<in> reach A i V\<close> \<open>W \<in> mcss A\<close>
        using W by simp_all
      ultimately have \<open>canonical A, V \<Turnstile> \<^bold>\<not> K i p\<close>
        by auto
      then show False
        using \<open>canonical A, V \<Turnstile> K i p\<close> by auto
    qed

    then obtain W where W:
      \<open>{\<^bold>\<not> p} \<union> W \<subseteq> {\<^bold>\<not> p} \<union> known V i\<close> \<open>(\<^bold>\<not> p) \<notin> W\<close> \<open>finite W\<close> \<open>\<not> consistent A ({\<^bold>\<not> p} \<union> W)\<close>
      using exists_finite_inconsistent by metis

    obtain L where L: \<open>set L = W\<close>
      using \<open>finite W\<close> finite_list by blast

    then have \<open>A \<turnstile> imply L p\<close>
      using W(4) inconsistent_imply by blast
    then have \<open>A \<turnstile> K i (imply L p)\<close>
      using R2 by fast
    then have \<open>A \<turnstile> imply (map (K i) L) (K i p)\<close>
      using K_distrib_K_imp by fast
    then have \<open>imply (map (K i) L) (K i p) \<in> V\<close>
      using deriv_in_maximal K.prems(1, 2) by blast
    then show \<open>K i p \<in> V\<close>
      using L W(1-2)
    proof (induct L arbitrary: W)
      case (Cons a L)
      then have \<open>K i a \<in> V\<close>
        by auto
      then have \<open>imply (map (K i) L) (K i p) \<in> V\<close>
        using Cons(2) \<open>consistent A V\<close> \<open>maximal A V\<close> consequent_in_maximal by auto
      then show ?case
        using Cons by auto
    qed simp
  qed
  moreover have \<open>(canonical A, V \<Turnstile> \<^bold>\<not> K i p) \<longrightarrow> (\<^bold>\<not> K i p) \<in> V\<close>
    using \<open>consistent A V\<close> \<open>maximal A V\<close> exactly_one_in_maximal calculation(1)
    by (metis (no_types, lifting) semantics.simps(1, 5))
  moreover have \<open>(\<^bold>\<not> K i p) \<in> V \<longrightarrow> canonical A, V \<Turnstile> \<^bold>\<not> K i p\<close>
    using \<open>consistent A V\<close> \<open>maximal A V\<close> calculation(2) exactly_one_in_maximal by auto
  ultimately show ?case
    by blast
qed

lemma canonical_model:
  assumes \<open>consistent A S\<close> and \<open>p \<in> S\<close>
  defines \<open>V \<equiv> Extend A S from_nat\<close> and \<open>M \<equiv> canonical A\<close>
  shows \<open>M, V \<Turnstile> p\<close> and \<open>consistent A V\<close> and \<open>maximal A V\<close>
proof -
  have \<open>consistent A V\<close>
    using \<open>consistent A S\<close> unfolding V_def using consistent_Extend by blast
  have \<open>maximal A V\<close>
    unfolding V_def using maximal_Extend surj_from_nat by blast

  { fix x
    assume \<open>x \<in> S\<close>
    then have \<open>x \<in> V\<close>
      unfolding V_def using Extend_subset by blast
    then have \<open>M, V \<Turnstile> x\<close>
      unfolding M_def using truth_lemma \<open>consistent A V\<close> \<open>maximal A V\<close> by blast }
  then show \<open>M, V \<Turnstile> p\<close>
    using \<open>p \<in> S\<close> by blast+
  show \<open>consistent A V\<close> \<open>maximal A V\<close>
    by fact+
qed

subsection \<open>Completeness\<close>

lemma imply_completeness:
  fixes P :: \<open>(('i :: countable, 'i fm set) kripke) \<Rightarrow> bool\<close>
  assumes \<open>\<forall>M. \<forall>w \<in> \<W> M. P M \<longrightarrow> (\<forall>q \<in> G. M, w \<Turnstile> q) \<longrightarrow> M, w \<Turnstile> p\<close>
    and \<open>P (canonical A)\<close>
  shows \<open>\<exists>qs. set qs \<subseteq> G \<and> (A \<turnstile> imply qs p)\<close>
proof (rule ccontr)
  assume \<open>\<nexists>qs. set qs \<subseteq> G \<and> A \<turnstile> imply qs p\<close>
  then have *: \<open>\<forall>qs. set qs \<subseteq> G \<longrightarrow> \<not> A \<turnstile> imply ((\<^bold>\<not> p) # qs) \<^bold>\<bottom>\<close>
    using K_Boole by blast

  let ?S = \<open>{\<^bold>\<not> p} \<union> G\<close>
  let ?V = \<open>Extend A ?S from_nat\<close>
  let ?M = \<open>canonical A\<close>

  have \<open>consistent A ?S\<close>
    using * by (metis K_imply_Cons consistent_def inconsistent_subset)
  then have \<open>?M, ?V \<Turnstile> (\<^bold>\<not> p)\<close> \<open>\<forall>q \<in> G. ?M, ?V \<Turnstile> q\<close>
    using canonical_model by fastforce+
  moreover have \<open>?V \<in> mcss A\<close>
    using \<open>consistent A ?S\<close> consistent_Extend maximal_Extend surj_from_nat by blast
  ultimately have \<open>?M, ?V \<Turnstile> p\<close>
    using assms by simp
  then show False
    using \<open>?M, ?V \<Turnstile> (\<^bold>\<not> p)\<close> by simp
qed

abbreviation valid :: \<open>(('i :: countable, 'i fm set) kripke \<Rightarrow> bool) \<Rightarrow> 'i fm \<Rightarrow> bool\<close> where
  \<open>valid P p \<equiv> \<forall>M. \<forall>w \<in> \<W> M. P M \<longrightarrow> M, w \<Turnstile> p\<close>

theorem completeness:
  assumes \<open>valid P p\<close> and \<open>P (canonical A)\<close>
  shows \<open>A \<turnstile> p\<close>
  using assms imply_completeness[where G=\<open>{}\<close>] by simp

corollary completeness\<^sub>K:
  assumes \<open>valid (\<lambda>_. True) p\<close>
  shows \<open>A \<turnstile> p\<close>
  using assms completeness[where P=\<open>\<lambda>_. True\<close>] by blast

section \<open>System K\<close>

abbreviation SystemK :: \<open>'i fm \<Rightarrow> bool\<close> ("\<turnstile>\<^sub>K _" [50] 50) where
  \<open>\<turnstile>\<^sub>K p \<equiv> (\<lambda>_. False) \<turnstile> p\<close>

lemma soundness\<^sub>K: \<open>\<turnstile>\<^sub>K p \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  using soundness by metis

abbreviation \<open>valid\<^sub>K \<equiv> valid (\<lambda>_. True)\<close>

corollary
  assumes \<open>valid\<^sub>K p\<close>
  shows \<open>\<turnstile>\<^sub>K p\<close>
  using completeness\<^sub>K assms .

theorem main\<^sub>K: \<open>valid\<^sub>K p \<longleftrightarrow> \<turnstile>\<^sub>K p\<close>
proof
  assume \<open>valid\<^sub>K p\<close>
  with completeness show \<open>\<turnstile>\<^sub>K p\<close>
    by blast
next
  assume \<open>\<turnstile>\<^sub>K p\<close>
  with soundness\<^sub>K show \<open>valid\<^sub>K p\<close>
    by fast
qed

corollary
  assumes \<open>valid\<^sub>K p\<close> and \<open>w \<in> \<W> M\<close>
  shows \<open>M, w \<Turnstile> p\<close>
proof -
  have \<open>\<turnstile>\<^sub>K p\<close>
    using assms(1) unfolding main\<^sub>K .
  with soundness\<^sub>K assms(2) show \<open>M, w \<Turnstile> p\<close> by fast
qed

section \<open>System T\<close>

text \<open>Also known as System M\<close>

inductive AxT :: \<open>'i fm \<Rightarrow> bool\<close> where
  \<open>AxT (K i p \<^bold>\<longrightarrow> p)\<close>

abbreviation SystemT :: \<open>'i fm \<Rightarrow> bool\<close> ("\<turnstile>\<^sub>T _" [50] 50) where
  \<open>\<turnstile>\<^sub>T p \<equiv> AxT \<turnstile> p\<close>

lemma soundness_AxT: \<open>AxT p \<Longrightarrow> reflexive M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  by (induct p rule: AxT.induct) (meson truth)

lemma soundness\<^sub>T: \<open>\<turnstile>\<^sub>T p \<Longrightarrow> reflexive M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  using soundness soundness_AxT .

lemma AxT_reflexive:
  assumes \<open>AxT \<le> A\<close> and \<open>consistent A V\<close> and \<open>maximal A V\<close>
  shows \<open>V \<in> reach A i V\<close>
proof -
  have \<open>(K i p \<^bold>\<longrightarrow> p) \<in> V\<close> for p
    using assms ax_in_maximal AxT.intros by fast
  then have \<open>p \<in> V\<close> if \<open>K i p \<in> V\<close> for p
    using that assms consequent_in_maximal by blast
  then show ?thesis
    using assms by blast
qed

lemma mcs\<^sub>T_reflexive:
  assumes \<open>AxT \<le> A\<close>
  shows \<open>reflexive (canonical A)\<close>
  unfolding reflexive_def
proof safe
  fix i V
  assume \<open>V \<in> \<W> (canonical A)\<close>
  then have \<open>consistent A V\<close> \<open>maximal A V\<close>
    by simp_all
  with AxT_reflexive assms have \<open>V \<in> reach A i V\<close> .
  then show \<open>V \<in> \<K> (canonical A) i V\<close>
    by simp
qed

abbreviation \<open>valid\<^sub>T \<equiv> valid reflexive\<close>

lemma completeness\<^sub>T:
  assumes \<open>valid\<^sub>T p\<close>
  shows \<open>\<turnstile>\<^sub>T p\<close>
  using assms completeness mcs\<^sub>T_reflexive by blast

theorem main\<^sub>T: \<open>valid\<^sub>T p \<longleftrightarrow> \<turnstile>\<^sub>T p\<close>
  using soundness\<^sub>T completeness\<^sub>T by fast

corollary
  assumes \<open>reflexive M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>valid\<^sub>T p \<longrightarrow> M, w \<Turnstile> p\<close>
  using assms soundness\<^sub>T completeness\<^sub>T by fast

section \<open>System KB\<close>

inductive AxB :: \<open>'i fm \<Rightarrow> bool\<close> where
  \<open>AxB (p \<^bold>\<longrightarrow> K i (L i p))\<close>

abbreviation SystemKB :: \<open>'i fm \<Rightarrow> bool\<close> ("\<turnstile>\<^sub>K\<^sub>B _" [50] 50) where
  \<open>\<turnstile>\<^sub>K\<^sub>B p \<equiv> AxB \<turnstile> p\<close>

lemma soundness_AxB: \<open>AxB p \<Longrightarrow> symmetric M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  unfolding symmetric_def by (induct p rule: AxB.induct) auto

lemma soundness\<^sub>K\<^sub>B: \<open>\<turnstile>\<^sub>K\<^sub>B p \<Longrightarrow> symmetric M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  using soundness soundness_AxB .

lemma AxB_symmetric':
  assumes \<open>AxB \<le> A\<close> \<open>consistent A V\<close> \<open>maximal A V\<close> \<open>consistent A W\<close> \<open>maximal A W\<close>
    and \<open>W \<in> reach A i V\<close>
  shows \<open>V \<in> reach A i W\<close>
proof -
  have \<open>\<forall>p. K i p \<in> W \<longrightarrow> p \<in> V\<close>
  proof (intro allI impI, rule ccontr)
    fix p
    assume \<open>K i p \<in> W\<close> \<open>p \<notin> V\<close>
    then have \<open>(\<^bold>\<not> p) \<in> V\<close>
      using assms(2-3) exactly_one_in_maximal by fast
    then have \<open>K i (L i (\<^bold>\<not> p)) \<in> V\<close>
      using assms(1-3) ax_in_maximal AxB.intros consequent_in_maximal by fast
    then have \<open>L i (\<^bold>\<not> p) \<in> W\<close>
      using \<open>W \<in> reach A i V\<close> by fast
    then have \<open>(\<^bold>\<not> K i p) \<in> W\<close>
      using assms(4-5) by (meson K_LK consistent_consequent maximal_def)
    then show False
      using \<open>K i p \<in> W\<close> assms(4-5) exactly_one_in_maximal by fast
  qed
  then have \<open>known W i \<subseteq> V\<close>
    by blast
  then show ?thesis
    using assms(2-3) by simp
qed

lemma mcs\<^sub>K\<^sub>B_symmetric:
  assumes \<open>AxB \<le> A\<close>
  shows \<open>symmetric (canonical A)\<close>
  unfolding symmetric_def
proof (intro allI ballI)
  fix i V W
  assume \<open>V \<in> \<W> (canonical A)\<close> \<open>W \<in> \<W> (canonical A)\<close>
  then have \<open>consistent A V\<close> \<open>maximal A V\<close> \<open>consistent A W\<close> \<open>maximal A W\<close>
    by simp_all
  with AxB_symmetric' assms have \<open>W \<in> reach A i V \<longleftrightarrow> V \<in> reach A i W\<close>
    by metis
  then show
    \<open>(W \<in> \<K> (canonical A) i V) = (V \<in> \<K> (canonical A) i W)\<close>
    by simp
qed

abbreviation \<open>valid\<^sub>K\<^sub>B \<equiv> valid symmetric\<close>

lemma completeness\<^sub>K\<^sub>B:
  assumes \<open>valid\<^sub>K\<^sub>B p\<close>
  shows \<open>\<turnstile>\<^sub>K\<^sub>B p\<close>
  using assms completeness mcs\<^sub>K\<^sub>B_symmetric by blast

theorem main\<^sub>K\<^sub>B: \<open>valid\<^sub>K\<^sub>B p \<longleftrightarrow> \<turnstile>\<^sub>K\<^sub>B p\<close>
  using soundness\<^sub>K\<^sub>B completeness\<^sub>K\<^sub>B by fast

corollary
  assumes \<open>symmetric M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>valid\<^sub>K\<^sub>B p \<longrightarrow> M, w \<Turnstile> p\<close>
  using assms soundness\<^sub>K\<^sub>B completeness\<^sub>K\<^sub>B by fast

section \<open>System K4\<close>

inductive Ax4 :: \<open>'i fm \<Rightarrow> bool\<close> where
  \<open>Ax4 (K i p \<^bold>\<longrightarrow> K i (K i p))\<close>

abbreviation SystemK4 :: \<open>'i fm \<Rightarrow> bool\<close> ("\<turnstile>\<^sub>K\<^sub>4 _" [50] 50) where
  \<open>\<turnstile>\<^sub>K\<^sub>4 p \<equiv> Ax4 \<turnstile> p\<close>

lemma soundness_Ax4: \<open>Ax4 p \<Longrightarrow> transitive M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  by (induct p rule: Ax4.induct) (meson pos_introspection)

lemma soundness\<^sub>K\<^sub>4: \<open>\<turnstile>\<^sub>K\<^sub>4 p \<Longrightarrow> transitive M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  using soundness soundness_Ax4 .

lemma Ax4_transitive:
  assumes \<open>Ax4 \<le> A\<close> \<open>consistent A V\<close> \<open>maximal A V\<close>
    and \<open>W \<in> reach A i V\<close> \<open>U \<in> reach A i W\<close>
  shows \<open>U \<in> reach A i V\<close>
proof -
  have \<open>(K i p \<^bold>\<longrightarrow> K i (K i p)) \<in> V\<close> for p
    using assms(1-3) ax_in_maximal Ax4.intros by fast
  then have \<open>K i (K i p) \<in> V\<close> if \<open>K i p \<in> V\<close> for p
    using that assms(2-3) consequent_in_maximal by blast
  then show ?thesis
    using assms(4-5) by blast
qed

lemma mcs\<^sub>K\<^sub>4_transitive:
  assumes \<open>Ax4 \<le> A\<close>
  shows \<open>transitive (canonical A)\<close>
  unfolding transitive_def
proof safe
  fix i U V W
  assume \<open>V \<in> \<W> (canonical A)\<close>
  then have \<open>consistent A V\<close> \<open>maximal A V\<close>
    by simp_all
  moreover assume
    \<open>W \<in> \<K> (canonical A) i V\<close>
    \<open>U \<in> \<K> (canonical A) i W\<close>
  ultimately have \<open>U \<in> reach A i V\<close>
    using Ax4_transitive assms by simp
  then show \<open>U \<in> \<K> (canonical A) i V\<close>
    by simp
qed

abbreviation \<open>valid\<^sub>K\<^sub>4 \<equiv> valid transitive\<close>

lemma completeness\<^sub>K\<^sub>4:
  assumes \<open>valid\<^sub>K\<^sub>4 p\<close>
  shows \<open>\<turnstile>\<^sub>K\<^sub>4 p\<close>
  using assms completeness mcs\<^sub>K\<^sub>4_transitive by blast

theorem main\<^sub>K\<^sub>4: \<open>valid\<^sub>K\<^sub>4 p \<longleftrightarrow> \<turnstile>\<^sub>K\<^sub>4 p\<close>
  using soundness\<^sub>K\<^sub>4 completeness\<^sub>K\<^sub>4 by fast

corollary
  assumes \<open>transitive M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>valid\<^sub>K\<^sub>4 p \<longrightarrow> M, w \<Turnstile> p\<close>
  using assms soundness\<^sub>K\<^sub>4 completeness\<^sub>K\<^sub>4 by fast

section \<open>System S4\<close>

abbreviation Or :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool\<close> (infixl \<open>\<oplus>\<close> 65) where
  \<open>A \<oplus> A' \<equiv> \<lambda>x. A x \<or> A' x\<close>

abbreviation SystemS4 :: \<open>'i fm \<Rightarrow> bool\<close> ("\<turnstile>\<^sub>S\<^sub>4 _" [50] 50) where
  \<open>\<turnstile>\<^sub>S\<^sub>4 p \<equiv> AxT \<oplus> Ax4 \<turnstile> p\<close>

lemma soundness_AxT4: \<open>(AxT \<oplus> Ax4) p \<Longrightarrow> reflexive M \<and> transitive M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  using soundness_AxT soundness_Ax4 by fast

lemma soundness\<^sub>S\<^sub>4: \<open>\<turnstile>\<^sub>S\<^sub>4 p \<Longrightarrow> reflexive M \<and> transitive M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  using soundness soundness_AxT4 .

abbreviation \<open>valid\<^sub>S\<^sub>4 \<equiv> valid refltrans\<close>

lemma completeness\<^sub>S\<^sub>4:
  assumes \<open>valid\<^sub>S\<^sub>4 p\<close>
  shows \<open>\<turnstile>\<^sub>S\<^sub>4 p\<close>
  using assms completeness[where P=refltrans] mcs\<^sub>T_reflexive[where A=\<open>AxT \<oplus> Ax4\<close>]
    mcs\<^sub>K\<^sub>4_transitive[where A=\<open>AxT \<oplus> Ax4\<close>]
  by blast

theorem main\<^sub>S\<^sub>4: \<open>valid\<^sub>S\<^sub>4 p \<longleftrightarrow> \<turnstile>\<^sub>S\<^sub>4 p\<close>
  using soundness\<^sub>S\<^sub>4 completeness\<^sub>S\<^sub>4 by fast

corollary
  assumes \<open>reflexive M\<close> \<open>transitive M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>valid\<^sub>S\<^sub>4 p \<longrightarrow> M, w \<Turnstile> p\<close>
  using assms soundness\<^sub>S\<^sub>4 completeness\<^sub>S\<^sub>4 by fast

section \<open>System S5\<close>

abbreviation SystemS5 :: \<open>'i fm \<Rightarrow> bool\<close> ("\<turnstile>\<^sub>S\<^sub>5 _" [50] 50) where
  \<open>\<turnstile>\<^sub>S\<^sub>5 p \<equiv> AxT \<oplus> AxB \<oplus> Ax4 \<turnstile> p\<close>

abbreviation AxTB4 :: \<open>'i fm \<Rightarrow> bool\<close> where
  \<open>AxTB4 \<equiv> AxT \<oplus> AxB \<oplus> Ax4\<close>

lemma soundness_AxTB4: \<open>AxTB4 p \<Longrightarrow> equivalence M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  using soundness_AxT soundness_AxB soundness_Ax4 by fast

lemma soundness\<^sub>S\<^sub>5: \<open>\<turnstile>\<^sub>S\<^sub>5 p \<Longrightarrow> equivalence M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  using soundness soundness_AxTB4 .

abbreviation \<open>valid\<^sub>S\<^sub>5 \<equiv> valid equivalence\<close>

lemma completeness\<^sub>S\<^sub>5:
  assumes \<open>valid\<^sub>S\<^sub>5 p\<close>
  shows \<open>\<turnstile>\<^sub>S\<^sub>5 p\<close>
  using assms completeness[where P=equivalence]
    mcs\<^sub>T_reflexive[where A=AxTB4] mcs\<^sub>K\<^sub>B_symmetric[where A=AxTB4] mcs\<^sub>K\<^sub>4_transitive[where A=AxTB4]
  by blast

theorem main\<^sub>S\<^sub>5: \<open>valid\<^sub>S\<^sub>5 p \<longleftrightarrow> \<turnstile>\<^sub>S\<^sub>5 p\<close>
  using soundness\<^sub>S\<^sub>5 completeness\<^sub>S\<^sub>5 by fast

corollary
  assumes \<open>equivalence M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>valid\<^sub>S\<^sub>5 p \<longrightarrow> M, w \<Turnstile> p\<close>
  using assms soundness\<^sub>S\<^sub>5 completeness\<^sub>S\<^sub>5 by fast

subsection \<open>Traditional formulation\<close>

inductive SystemS5' :: \<open>'i fm \<Rightarrow> bool\<close> ("\<turnstile>\<^sub>S\<^sub>5'' _" [50] 50) where
  A1': \<open>tautology p \<Longrightarrow> \<turnstile>\<^sub>S\<^sub>5' p\<close>
| A2': \<open>\<turnstile>\<^sub>S\<^sub>5' (K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i p \<^bold>\<longrightarrow> K i q)\<close>
| AT': \<open>\<turnstile>\<^sub>S\<^sub>5' (K i p \<^bold>\<longrightarrow> p)\<close>
| A5': \<open>\<turnstile>\<^sub>S\<^sub>5' (\<^bold>\<not> K i p \<^bold>\<longrightarrow> K i (\<^bold>\<not> K i p))\<close>
| R1': \<open>\<turnstile>\<^sub>S\<^sub>5' p \<Longrightarrow> \<turnstile>\<^sub>S\<^sub>5' (p \<^bold>\<longrightarrow> q) \<Longrightarrow> \<turnstile>\<^sub>S\<^sub>5' q\<close>
| R2': \<open>\<turnstile>\<^sub>S\<^sub>5' p \<Longrightarrow> \<turnstile>\<^sub>S\<^sub>5' K i p\<close>

lemma S5'_trans: \<open>\<turnstile>\<^sub>S\<^sub>5' ((p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r)\<close>
  by (simp add: A1')

lemma S5'_L: \<open>\<turnstile>\<^sub>S\<^sub>5' (p \<^bold>\<longrightarrow> L i p)\<close>
proof -
  have \<open>\<turnstile>\<^sub>S\<^sub>5' (K i (\<^bold>\<not> p) \<^bold>\<longrightarrow> \<^bold>\<not> p)\<close>
    using AT' by fast
  moreover have \<open>\<turnstile>\<^sub>S\<^sub>5' ((P \<^bold>\<longrightarrow> \<^bold>\<not> Q) \<^bold>\<longrightarrow> Q \<^bold>\<longrightarrow> \<^bold>\<not> P)\<close> for P Q :: \<open>'i fm\<close>
    using A1' by force
  ultimately show ?thesis
    using R1' by blast
qed

lemma S5'_B: \<open>\<turnstile>\<^sub>S\<^sub>5' (p \<^bold>\<longrightarrow> K i (L i p))\<close>
  using A5' S5'_L R1' S5'_trans by metis

lemma S5'_KL: \<open>\<turnstile>\<^sub>S\<^sub>5' (K i p \<^bold>\<longrightarrow> L i p)\<close>
  by (meson AT' R1' S5'_L S5'_trans)

lemma S5'_map_K:
  assumes \<open>\<turnstile>\<^sub>S\<^sub>5' (p \<^bold>\<longrightarrow> q)\<close>
  shows \<open>\<turnstile>\<^sub>S\<^sub>5' (K i p \<^bold>\<longrightarrow> K i q)\<close>
proof -
  note \<open>\<turnstile>\<^sub>S\<^sub>5' (p \<^bold>\<longrightarrow> q)\<close>
  then have \<open>\<turnstile>\<^sub>S\<^sub>5' K i (p \<^bold>\<longrightarrow> q)\<close>
    using R2' by fast
  moreover have \<open>\<turnstile>\<^sub>S\<^sub>5' (K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i p \<^bold>\<longrightarrow> K i q)\<close>
    using A2' by fast
  ultimately show ?thesis
    using R1' by fast
qed

lemma S5'_map_L:
  assumes \<open>\<turnstile>\<^sub>S\<^sub>5' (p \<^bold>\<longrightarrow> q)\<close>
  shows \<open>\<turnstile>\<^sub>S\<^sub>5' (L i p \<^bold>\<longrightarrow> L i q)\<close>
  using assms by (metis R1' S5'_map_K S5'_trans)

lemma S5'_L_dual: \<open>\<turnstile>\<^sub>S\<^sub>5' (\<^bold>\<not> L i (\<^bold>\<not> p) \<^bold>\<longrightarrow> K i p)\<close>
proof -
  have \<open>\<turnstile>\<^sub>S\<^sub>5' (K i p \<^bold>\<longrightarrow> K i p)\<close> \<open>\<turnstile>\<^sub>S\<^sub>5' (\<^bold>\<not> \<^bold>\<not> p \<^bold>\<longrightarrow> p)\<close>
    by (simp_all add: A1')
  then have \<open>\<turnstile>\<^sub>S\<^sub>5' (K i (\<^bold>\<not> \<^bold>\<not> p) \<^bold>\<longrightarrow> K i p)\<close>
    by (simp add: S5'_map_K)
  moreover have \<open>\<turnstile>\<^sub>S\<^sub>5' ((P \<^bold>\<longrightarrow> Q) \<^bold>\<longrightarrow> (\<^bold>\<not> \<^bold>\<not> P \<^bold>\<longrightarrow> Q))\<close> for P Q :: \<open>'i fm\<close>
    by (simp add: A1')
  ultimately show \<open>\<turnstile>\<^sub>S\<^sub>5' (\<^bold>\<not> \<^bold>\<not> K i (\<^bold>\<not> \<^bold>\<not> p) \<^bold>\<longrightarrow> K i p)\<close>
    using R1' by blast
qed

lemma S5'_4: \<open>\<turnstile>\<^sub>S\<^sub>5' (K i p \<^bold>\<longrightarrow> K i (K i p))\<close>
proof -
  have \<open>\<turnstile>\<^sub>S\<^sub>5' (L i (\<^bold>\<not> p) \<^bold>\<longrightarrow> K i (L i (\<^bold>\<not> p)))\<close>
    using A5' by fast
  moreover have \<open>\<turnstile>\<^sub>S\<^sub>5' ((P \<^bold>\<longrightarrow> Q) \<^bold>\<longrightarrow> \<^bold>\<not> Q \<^bold>\<longrightarrow> \<^bold>\<not> P)\<close> for P Q :: \<open>'i fm\<close>
    using A1' by force
  ultimately have \<open>\<turnstile>\<^sub>S\<^sub>5' (\<^bold>\<not> K i (L i (\<^bold>\<not> p)) \<^bold>\<longrightarrow> \<^bold>\<not> L i (\<^bold>\<not> p))\<close>
    using R1' by fast
  then have \<open>\<turnstile>\<^sub>S\<^sub>5' (L i (K i (\<^bold>\<not> \<^bold>\<not> p)) \<^bold>\<longrightarrow> \<^bold>\<not> L i (\<^bold>\<not> p))\<close>
    by blast
  moreover have \<open>\<turnstile>\<^sub>S\<^sub>5' (p \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> p)\<close>
    by (simp add: A1')
  ultimately have \<open>\<turnstile>\<^sub>S\<^sub>5' (L i (K i p) \<^bold>\<longrightarrow> \<^bold>\<not> L i (\<^bold>\<not> p))\<close>
    by (metis (no_types, opaque_lifting) R1' S5'_map_K S5'_trans)
  then have \<open>\<turnstile>\<^sub>S\<^sub>5' (L i (K i p) \<^bold>\<longrightarrow> K i p)\<close>
    by (meson S5'_L_dual R1' S5'_trans)
  then show ?thesis
    by (metis A2' R1' R2' S5'_B S5'_trans)
qed

lemma S5_S5': \<open>\<turnstile>\<^sub>S\<^sub>5 p \<Longrightarrow> \<turnstile>\<^sub>S\<^sub>5' p\<close>
proof (induct p rule: AK.induct)
  case (A2 i p q)
  have \<open>\<turnstile>\<^sub>S\<^sub>5' (K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i p \<^bold>\<longrightarrow> K i q)\<close>
    using A2' .
  moreover have \<open>\<turnstile>\<^sub>S\<^sub>5' ((P \<^bold>\<longrightarrow> Q \<^bold>\<longrightarrow> R) \<^bold>\<longrightarrow> (Q \<^bold>\<and> P \<^bold>\<longrightarrow> R))\<close> for P Q R :: \<open>'i fm\<close>
    by (simp add: A1')
  ultimately show ?case
    using R1' by blast
next
  case (Ax p)
  then show ?case
    using AT' S5'_B S5'_4
    by (metis Ax4.cases AxB.cases AxT.cases)
qed (meson SystemS5'.intros)+

lemma S5'_S5:
  fixes p :: \<open>('i :: countable) fm\<close>
  shows \<open>\<turnstile>\<^sub>S\<^sub>5' p \<Longrightarrow> \<turnstile>\<^sub>S\<^sub>5 p\<close>
proof (induct p rule: SystemS5'.induct)
  case (AT' i p)
  then show ?case
    by (simp add: Ax AxT.intros)
next
  case (A5' i p)
  then show ?case
    using completeness\<^sub>S\<^sub>5 neg_introspection by fast
qed (meson AK.intros K_A2')+

theorem main\<^sub>S\<^sub>5': \<open>valid\<^sub>S\<^sub>5 p \<longleftrightarrow> \<turnstile>\<^sub>S\<^sub>5' p\<close>
  using main\<^sub>S\<^sub>5 S5_S5' S5'_S5 by blast

section \<open>Acknowledgements\<close>

text \<open>
The formalization is inspired by Berghofer's formalization of Henkin-style completeness.

  \<^item> Stefan Berghofer:
  First-Order Logic According to Fitting.
  \<^url>\<open>https://www.isa-afp.org/entries/FOL-Fitting.shtml\<close>
\<close>

end
