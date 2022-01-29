(*
  File:      PAL.thy
  Author:    Asta Halkjær From

  This work is a formalization of public announcement logic with countably many agents.
  It includes proofs of soundness and completeness for a variant of the axiom system
    PA + DIST! + NEC!.
  The completeness proof builds on the Epistemic Logic theory.
*)

theory PAL imports "Epistemic_Logic.Epistemic_Logic" begin

section \<open>Syntax\<close>

datatype 'i pfm
  = FF (\<open>\<^bold>\<bottom>\<^sub>!\<close>)
  | Pro' id (\<open>Pro\<^sub>!\<close>)
  | Dis \<open>'i pfm\<close> \<open>'i pfm\<close> (infixr \<open>\<^bold>\<or>\<^sub>!\<close> 30)
  | Con \<open>'i pfm\<close> \<open>'i pfm\<close> (infixr \<open>\<^bold>\<and>\<^sub>!\<close> 35)
  | Imp \<open>'i pfm\<close> \<open>'i pfm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<^sub>!\<close> 25)
  | K' 'i \<open>'i pfm\<close> (\<open>K\<^sub>!\<close>)
  | Ann \<open>'i pfm\<close> \<open>'i pfm\<close> (\<open>[_]\<^sub>! _\<close> [50, 50] 50)

abbreviation PIff :: \<open>'i pfm \<Rightarrow> 'i pfm \<Rightarrow> 'i pfm\<close> (infixr \<open>\<^bold>\<longleftrightarrow>\<^sub>!\<close> 25) where
  \<open>p \<^bold>\<longleftrightarrow>\<^sub>! q \<equiv> (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<and>\<^sub>! (q \<^bold>\<longrightarrow>\<^sub>! p)\<close>

abbreviation PNeg (\<open>\<^bold>\<not>\<^sub>! _\<close> [40] 40) where
  \<open>\<^bold>\<not>\<^sub>! p \<equiv> p \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!\<close>

abbreviation PL (\<open>L\<^sub>!\<close>) where
  \<open>L\<^sub>! i p \<equiv> (\<^bold>\<not>\<^sub>! (K\<^sub>! i (\<^bold>\<not>\<^sub>! p)))\<close>

section \<open>Semantics\<close>

fun
  psemantics :: \<open>('i, 'w) kripke \<Rightarrow> 'w \<Rightarrow> 'i pfm \<Rightarrow> bool\<close> (\<open>_, _ \<Turnstile>\<^sub>! _\<close> [50, 50] 50) and
  restrict :: \<open>('i, 'w) kripke \<Rightarrow> 'i pfm \<Rightarrow> ('i, 'w) kripke\<close> where
  \<open>(M, w \<Turnstile>\<^sub>! \<^bold>\<bottom>\<^sub>!) = False\<close>
| \<open>(M, w \<Turnstile>\<^sub>! Pro\<^sub>! x) = \<pi> M w x\<close>
| \<open>(M, w \<Turnstile>\<^sub>! (p \<^bold>\<or>\<^sub>! q)) = ((M, w \<Turnstile>\<^sub>! p) \<or> (M, w \<Turnstile>\<^sub>! q))\<close>
| \<open>(M, w \<Turnstile>\<^sub>! (p \<^bold>\<and>\<^sub>! q)) = ((M, w \<Turnstile>\<^sub>! p) \<and> (M, w \<Turnstile>\<^sub>! q))\<close>
| \<open>(M, w \<Turnstile>\<^sub>! (p \<^bold>\<longrightarrow>\<^sub>! q)) = ((M, w \<Turnstile>\<^sub>! p) \<longrightarrow> (M, w \<Turnstile>\<^sub>! q))\<close>
| \<open>(M, w \<Turnstile>\<^sub>! K\<^sub>! i p) = (\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile>\<^sub>! p)\<close>
| \<open>(M, w \<Turnstile>\<^sub>! [r]\<^sub>! p) = ((M, w \<Turnstile>\<^sub>! r) \<longrightarrow> (restrict M r, w \<Turnstile>\<^sub>! p))\<close>
| \<open>restrict M p = Kripke {w. w \<in> \<W> M \<and> M, w \<Turnstile>\<^sub>! p} (\<pi> M) (\<K> M)\<close>

primrec static :: \<open>'i pfm \<Rightarrow> bool\<close> where
  \<open>static \<^bold>\<bottom>\<^sub>! = True\<close>
| \<open>static (Pro\<^sub>! _) = True\<close>
| \<open>static (p \<^bold>\<or>\<^sub>! q) = (static p \<and> static q)\<close>
| \<open>static (p \<^bold>\<and>\<^sub>! q) = (static p \<and> static q)\<close>
| \<open>static (p \<^bold>\<longrightarrow>\<^sub>! q) = (static p \<and> static q)\<close>
| \<open>static (K\<^sub>! i p) = static p\<close>
| \<open>static ([r]\<^sub>! p) = False\<close>

primrec lower :: \<open>'i pfm \<Rightarrow> 'i fm\<close> where
  \<open>lower \<^bold>\<bottom>\<^sub>! = \<^bold>\<bottom>\<close>
| \<open>lower (Pro\<^sub>! x) = Pro x\<close>
| \<open>lower (p \<^bold>\<or>\<^sub>! q) = (lower p \<^bold>\<or> lower q)\<close>
| \<open>lower (p \<^bold>\<and>\<^sub>! q) = (lower p \<^bold>\<and> lower q)\<close>
| \<open>lower (p \<^bold>\<longrightarrow>\<^sub>! q) = (lower p \<^bold>\<longrightarrow> lower q)\<close>
| \<open>lower (K\<^sub>! i p) = K i (lower p)\<close>
| \<open>lower ([r]\<^sub>! p) = undefined\<close>

primrec lift :: \<open>'i fm \<Rightarrow> 'i pfm\<close> where
  \<open>lift \<^bold>\<bottom> = \<^bold>\<bottom>\<^sub>!\<close>
| \<open>lift (Pro x) = Pro\<^sub>! x\<close>
| \<open>lift (p \<^bold>\<or> q) = (lift p \<^bold>\<or>\<^sub>! lift q)\<close>
| \<open>lift (p \<^bold>\<and> q) = (lift p \<^bold>\<and>\<^sub>! lift q)\<close>
| \<open>lift (p \<^bold>\<longrightarrow> q) = (lift p \<^bold>\<longrightarrow>\<^sub>! lift q)\<close>
| \<open>lift (K i p) = K\<^sub>! i (lift p)\<close>

lemma lower_semantics:
  assumes \<open>static p\<close>
  shows \<open>(M, w \<Turnstile> lower p) \<longleftrightarrow> (M, w \<Turnstile>\<^sub>! p)\<close>
  using assms by (induct p arbitrary: w) simp_all

lemma lift_semantics: \<open>(M, w \<Turnstile> p) \<longleftrightarrow> (M, w \<Turnstile>\<^sub>! lift p)\<close>
  by (induct p arbitrary: w) simp_all

lemma lower_lift: \<open>lower (lift p) = p\<close>
  by (induct p) simp_all

lemma lift_lower: \<open>static p \<Longrightarrow> lift (lower p) = p\<close>
  by (induct p) simp_all

section \<open>Soundness of Reduction\<close>

primrec reduce' :: \<open>'i pfm \<Rightarrow> 'i pfm \<Rightarrow> 'i pfm\<close> where
  \<open>reduce' r \<^bold>\<bottom>\<^sub>! = (r \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!)\<close>
| \<open>reduce' r (Pro\<^sub>! x) = (r \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x)\<close>
| \<open>reduce' r (p \<^bold>\<or>\<^sub>! q) = (reduce' r p \<^bold>\<or>\<^sub>! reduce' r q)\<close>
| \<open>reduce' r (p \<^bold>\<and>\<^sub>! q) = (reduce' r p \<^bold>\<and>\<^sub>! reduce' r q)\<close>
| \<open>reduce' r (p \<^bold>\<longrightarrow>\<^sub>! q) = (reduce' r p \<^bold>\<longrightarrow>\<^sub>! reduce' r q)\<close>
| \<open>reduce' r (K\<^sub>! i p) = (r \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i (reduce' r p))\<close>
| \<open>reduce' r ([p]\<^sub>! q) = undefined\<close>

primrec reduce :: \<open>'i pfm \<Rightarrow> 'i pfm\<close> where
  \<open>reduce \<^bold>\<bottom>\<^sub>! = \<^bold>\<bottom>\<^sub>!\<close>
| \<open>reduce (Pro\<^sub>! x) = Pro\<^sub>! x\<close>
| \<open>reduce (p \<^bold>\<or>\<^sub>! q) = (reduce p \<^bold>\<or>\<^sub>! reduce q)\<close>
| \<open>reduce (p \<^bold>\<and>\<^sub>! q) = (reduce p \<^bold>\<and>\<^sub>! reduce q)\<close>
| \<open>reduce (p \<^bold>\<longrightarrow>\<^sub>! q) = (reduce p \<^bold>\<longrightarrow>\<^sub>! reduce q)\<close>
| \<open>reduce (K\<^sub>! i p) = K\<^sub>! i (reduce p)\<close>
| \<open>reduce ([r]\<^sub>! p) = reduce' (reduce r) (reduce p)\<close>

lemma static_reduce': \<open>static p \<Longrightarrow> static r \<Longrightarrow> static (reduce' r p)\<close>
  by (induct p) simp_all

lemma static_reduce: \<open>static (reduce p)\<close>
  by (induct p) (simp_all add: static_reduce')

lemma reduce'_semantics:
  assumes \<open>static q\<close>
  shows \<open>((M, w \<Turnstile>\<^sub>! [p]\<^sub>! (q))) = (M, w \<Turnstile>\<^sub>! reduce' p q)\<close>
  using assms by (induct q arbitrary: w) auto

lemma reduce_semantics: \<open>(M, w \<Turnstile>\<^sub>! p) = (M, w \<Turnstile>\<^sub>! reduce p)\<close>
proof (induct p arbitrary: M w)
  case (Ann p q)
  then show ?case
    using reduce'_semantics static_reduce by fastforce
qed simp_all

section \<open>Proof System\<close>

primrec peval :: \<open>(id \<Rightarrow> bool) \<Rightarrow> ('i pfm \<Rightarrow> bool) \<Rightarrow> 'i pfm \<Rightarrow> bool\<close> where
  \<open>peval _ _ \<^bold>\<bottom>\<^sub>! = False\<close>
| \<open>peval g _ (Pro\<^sub>! x) = g x\<close>
| \<open>peval g h (p \<^bold>\<or>\<^sub>! q) = (peval g h p \<or> peval g h q)\<close>
| \<open>peval g h (p \<^bold>\<and>\<^sub>! q) = (peval g h p \<and> peval g h q)\<close>
| \<open>peval g h (p \<^bold>\<longrightarrow>\<^sub>! q) = (peval g h p \<longrightarrow> peval g h q)\<close>
| \<open>peval _ h (K\<^sub>! i p) = h (K\<^sub>! i p)\<close>
| \<open>peval _ h ([r]\<^sub>! p) = h ([r]\<^sub>! p)\<close>

abbreviation \<open>ptautology p \<equiv> \<forall>g h. peval g h p\<close>

inductive PAK :: \<open>('i pfm \<Rightarrow> bool) \<Rightarrow> 'i pfm \<Rightarrow> bool\<close> (\<open>_ \<turnstile>\<^sub>! _\<close> [20, 20] 20)
  for A :: \<open>'i pfm \<Rightarrow> bool\<close> where
    PA1: \<open>ptautology p \<Longrightarrow> A \<turnstile>\<^sub>! p\<close>
  | PA2: \<open>A \<turnstile>\<^sub>! K\<^sub>! i p \<^bold>\<and>\<^sub>! K\<^sub>! i (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i q\<close>
  | PAx: \<open>A p \<Longrightarrow> A \<turnstile>\<^sub>! p\<close>
  | PR1: \<open>A \<turnstile>\<^sub>! p \<Longrightarrow> A \<turnstile>\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! q \<Longrightarrow> A \<turnstile>\<^sub>! q\<close>
  | PR2: \<open>A \<turnstile>\<^sub>! p \<Longrightarrow> A \<turnstile>\<^sub>! K\<^sub>! i p\<close>
  | PFF: \<open>A \<turnstile>\<^sub>! [r]\<^sub>! \<^bold>\<bottom>\<^sub>! \<^bold>\<longleftrightarrow>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!)\<close>
  | PPro: \<open>A \<turnstile>\<^sub>! [r]\<^sub>! Pro\<^sub>! x \<^bold>\<longleftrightarrow>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x)\<close>
  | PDis: \<open>A \<turnstile>\<^sub>! [r]\<^sub>! (p \<^bold>\<or>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! [r]\<^sub>! p \<^bold>\<or>\<^sub>! [r]\<^sub>! q\<close>
  | PCon: \<open>A \<turnstile>\<^sub>! [r]\<^sub>! (p \<^bold>\<and>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! [r]\<^sub>! p \<^bold>\<and>\<^sub>! [r]\<^sub>! q\<close>
  | PImp: \<open>A \<turnstile>\<^sub>! ([r]\<^sub>! (p \<^bold>\<longrightarrow>\<^sub>! q)) \<^bold>\<longleftrightarrow>\<^sub>! ([r]\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! [r]\<^sub>! q)\<close>
  | PK: \<open>A \<turnstile>\<^sub>! ([r]\<^sub>! K\<^sub>! i p) \<^bold>\<longleftrightarrow>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i ([r]\<^sub>! p))\<close>
  | PAnn: \<open>A \<turnstile>\<^sub>! p \<Longrightarrow> A \<turnstile>\<^sub>! [r]\<^sub>! p\<close>

lemma eval_peval: \<open>eval h (g o lift) p = peval h g (lift p)\<close>
  by (induct p) simp_all

lemma tautology_ptautology: \<open>tautology p \<Longrightarrow> ptautology (lift p)\<close>
  using eval_peval by blast

theorem AK_PAK: \<open>A o lift \<turnstile> p \<Longrightarrow> A \<turnstile>\<^sub>! lift p\<close>
  by (induct p rule: AK.induct) (auto intro: PAK.intros(1-5) simp: tautology_ptautology)

abbreviation validP :: \<open>(('i :: countable, 'i fm set) kripke \<Rightarrow> bool) \<Rightarrow> 'i pfm \<Rightarrow> bool\<close> (\<open>valid\<^sub>!\<close>)
  where \<open>valid\<^sub>! P p \<equiv> \<forall>M. \<forall>w \<in> \<W> M. P M \<longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>

theorem static_completeness:
  assumes \<open>static p\<close> and \<open>valid\<^sub>! P p\<close>
    and \<open>valid P (lower p) \<Longrightarrow> A o lift \<turnstile> lower p\<close>
  shows \<open>A \<turnstile>\<^sub>! p\<close>
proof -
  have \<open>valid P (lower p)\<close>
    using assms by (simp add: lower_semantics)
  then have \<open>A o lift \<turnstile> lower p\<close>
    using assms(3) by fast
  then have \<open>A \<turnstile>\<^sub>! lift (lower p)\<close>
    using AK_PAK by fast
  then show ?thesis
    using assms(1) lift_lower by metis
qed

corollary
  assumes \<open>static p\<close> \<open>valid\<^sub>! (\<lambda>_. True) p\<close>
  shows \<open>A \<turnstile>\<^sub>! p\<close>
  using assms static_completeness[where P=\<open>\<lambda>_. True\<close>] completeness\<^sub>K by metis

section \<open>Soundness\<close>

lemma peval_semantics: \<open>peval (val w) (\<lambda>q. Kripke W val r, w \<Turnstile>\<^sub>! q) p = (Kripke W val r, w \<Turnstile>\<^sub>! p)\<close>
  by (induct p) simp_all

lemma ptautology:
  assumes \<open>ptautology p\<close>
  shows \<open>M, w \<Turnstile>\<^sub>! p\<close>
proof -
  from assms have \<open>peval (g w) (\<lambda>q. Kripke W g r, w \<Turnstile>\<^sub>! q) p\<close> for W g r
    by simp
  then have \<open>Kripke W g r, w \<Turnstile>\<^sub>! p\<close> for W g r
    using peval_semantics by fast
  then show \<open>M, w \<Turnstile>\<^sub>! p\<close>
    by (metis kripke.collapse)
qed

theorem soundness:
  assumes
    \<open>\<And>M p w. A p \<Longrightarrow> P M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
    \<open>\<And>M p. P M \<Longrightarrow> P (restrict M p)\<close>
  shows \<open>A \<turnstile>\<^sub>! p \<Longrightarrow> P M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
proof (induct p arbitrary: M w rule: PAK.induct)
  case (PAnn p r)
  moreover have \<open>P (restrict M r)\<close>
    using PAnn(3) assms(2) by simp
  ultimately show ?case
    by simp
qed (simp_all add: assms ptautology)

corollary \<open>(\<lambda>_. False) \<turnstile>\<^sub>! p \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using soundness[where P=\<open>\<lambda>_. True\<close>] by metis

section \<open>Completeness\<close>

lemma ConE:
  assumes \<open>A \<turnstile>\<^sub>! p \<^bold>\<and>\<^sub>! q\<close>
  shows \<open>A \<turnstile>\<^sub>! p\<close> \<open>A \<turnstile>\<^sub>! q\<close>
  using assms by (metis PA1 PR1 peval.simps(4-5))+

lemma Iff_Dis:
  assumes \<open>A \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! p'\<close> \<open>A \<turnstile>\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! q'\<close>
  shows \<open>A \<turnstile>\<^sub>! ((p \<^bold>\<or>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<or>\<^sub>! q'))\<close>
proof -
  have \<open>A \<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! p') \<^bold>\<longrightarrow>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! q') \<^bold>\<longrightarrow>\<^sub>! ((p \<^bold>\<or>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<or>\<^sub>! q'))\<close>
    by (simp add: PA1)
  then show ?thesis
    using assms PR1 by blast
qed

lemma Iff_Con:
  assumes \<open>A \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! p'\<close> \<open>A \<turnstile>\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! q'\<close>
  shows \<open>A \<turnstile>\<^sub>! (p \<^bold>\<and>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<and>\<^sub>! q')\<close>
proof -
  have \<open>A \<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! p') \<^bold>\<longrightarrow>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! q') \<^bold>\<longrightarrow>\<^sub>! ((p \<^bold>\<and>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<and>\<^sub>! q'))\<close>
    by (simp add: PA1)
  then show ?thesis
    using assms PR1 by blast
qed

lemma Iff_Imp:
  assumes \<open>A \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! p'\<close> \<open>A \<turnstile>\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! q'\<close>
  shows \<open>A \<turnstile>\<^sub>! ((p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<longrightarrow>\<^sub>! q'))\<close>
proof -
  have \<open>A \<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! p') \<^bold>\<longrightarrow>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! q') \<^bold>\<longrightarrow>\<^sub>! ((p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<longrightarrow>\<^sub>! q'))\<close>
    by (simp add: PA1)
  then show ?thesis
    using assms PR1 by blast
qed

lemma Iff_sym: \<open>(A \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! q) = (A \<turnstile>\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! p)\<close>
proof -
  have \<open>A \<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! p)\<close>
    by (simp add: PA1)
  then show ?thesis
    using PR1 ConE by blast
qed

lemma Iff_Iff:
  assumes \<open>A \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! p'\<close> \<open>A \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! q\<close>
  shows \<open>A \<turnstile>\<^sub>! p' \<^bold>\<longleftrightarrow>\<^sub>! q\<close>
proof -
  have \<open>ptautology ((p \<^bold>\<longleftrightarrow>\<^sub>! p') \<^bold>\<longrightarrow>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! (p' \<^bold>\<longleftrightarrow>\<^sub>! q))\<close>
    by (metis peval.simps(4-5))
  with PA1 have \<open>A \<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! p') \<^bold>\<longrightarrow>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! (p' \<^bold>\<longleftrightarrow>\<^sub>! q)\<close> .
  then show ?thesis
    using assms PR1 by blast
qed

lemma K'_A2': \<open>A \<turnstile>\<^sub>! K\<^sub>! i (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i q\<close>
proof -
  have \<open>A \<turnstile>\<^sub>! K\<^sub>! i p \<^bold>\<and>\<^sub>! K\<^sub>! i (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i q\<close>
    using PA2 by fast
  moreover have \<open>A \<turnstile>\<^sub>! (P \<^bold>\<and>\<^sub>! Q \<^bold>\<longrightarrow>\<^sub>! R) \<^bold>\<longrightarrow>\<^sub>! (Q \<^bold>\<longrightarrow>\<^sub>! P \<^bold>\<longrightarrow>\<^sub>! R)\<close> for P Q R
    by (simp add: PA1)
  ultimately show ?thesis
    using PR1 by fast
qed

lemma K'_map:
  assumes \<open>A \<turnstile>\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! q\<close>
  shows \<open>A \<turnstile>\<^sub>! K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i q\<close>
proof -
  note \<open>A \<turnstile>\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! q\<close>
  then have \<open>A \<turnstile>\<^sub>! K\<^sub>! i (p \<^bold>\<longrightarrow>\<^sub>! q)\<close>
    using PR2 by fast
  moreover have \<open>A \<turnstile>\<^sub>! K\<^sub>! i (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i q\<close>
    using K'_A2' by fast
  ultimately show ?thesis
    using PR1 by fast
qed

lemma ConI:
  assumes \<open>A \<turnstile>\<^sub>! p\<close> \<open>A \<turnstile>\<^sub>! q\<close>
  shows \<open>A \<turnstile>\<^sub>! p \<^bold>\<and>\<^sub>! q\<close>
proof -
  have \<open>A \<turnstile>\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! q \<^bold>\<longrightarrow>\<^sub>! p \<^bold>\<and>\<^sub>! q\<close>
    by (simp add: PA1)
  then show ?thesis
    using assms PR1 by blast
qed

lemma Iff_wk:
  assumes \<open>A \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! q\<close>
  shows \<open>A \<turnstile>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! p) \<^bold>\<longleftrightarrow>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! q)\<close>
proof -
  have \<open>A \<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! ((r \<^bold>\<longrightarrow>\<^sub>! p) \<^bold>\<longleftrightarrow>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! q))\<close>
    by (simp add: PA1)
  then show ?thesis
    using assms PR1 by blast
qed

lemma Iff_reduce':
  assumes \<open>static p\<close>
  shows \<open>A \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! reduce' r p\<close>
  using assms
proof (induct p rule: pfm.induct)
  case FF
  then show ?case
    by (simp add: PFF)
next
  case (Pro' x)
  then show ?case
    by (simp add: PPro)
next
  case (Dis p q)
  then have \<open>A \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<or>\<^sub>! [r]\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! reduce' r (p \<^bold>\<or>\<^sub>! q)\<close>
    using Iff_Dis by fastforce
  moreover have \<open>A \<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<or>\<^sub>! [r]\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! ([r]\<^sub>! (p \<^bold>\<or>\<^sub>! q))\<close>
    using PDis Iff_sym by fastforce
  ultimately show ?case
    using PA1 PR1 Iff_Iff by blast
next
  case (Con p q)
  then have \<open>A \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<and>\<^sub>! [r]\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! reduce' r (p \<^bold>\<and>\<^sub>! q)\<close>
    using Iff_Con by fastforce
  moreover have \<open>A \<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<and>\<^sub>! [r]\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! ([r]\<^sub>! (p \<^bold>\<and>\<^sub>! q))\<close>
    using PCon Iff_sym by fastforce
  ultimately show ?case
    using PA1 PR1 Iff_Iff by blast
next
  case (Imp p q)
  then have \<open>A \<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! [r]\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! reduce' r (p \<^bold>\<longrightarrow>\<^sub>! q)\<close>
    using Iff_Imp by fastforce
  moreover have \<open>A \<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! [r]\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! ([r]\<^sub>! (p \<^bold>\<longrightarrow>\<^sub>! q))\<close>
    using PImp Iff_sym by fastforce
  ultimately show ?case
    using PA1 PR1 Iff_Iff by blast
next
  case (K' i p)
  then have \<open>A \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! reduce' r p\<close>
    by simp
  then have \<open>A \<turnstile>\<^sub>! K\<^sub>! i ([r]\<^sub>! p) \<^bold>\<longleftrightarrow>\<^sub>! K\<^sub>! i (reduce' r p)\<close>
    using K'_map ConE ConI by metis
  moreover have \<open>A \<turnstile>\<^sub>! [r]\<^sub>! K\<^sub>! i p \<^bold>\<longleftrightarrow>\<^sub>! r \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i ([r]\<^sub>! p)\<close>
    using PK .
  ultimately have \<open>A \<turnstile>\<^sub>! [r]\<^sub>! K\<^sub>! i p \<^bold>\<longleftrightarrow>\<^sub>! r \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i (reduce' r p)\<close>
    by (meson Iff_Iff Iff_sym Iff_wk)
  then show ?case
    by simp
next
  case (Ann r p)
  then show ?case
    by simp
qed

lemma Iff_Ann1:
  assumes r: \<open>A \<turnstile>\<^sub>! r \<^bold>\<longleftrightarrow>\<^sub>! r'\<close> and \<open>static p\<close>
  shows \<open>A \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! [r']\<^sub>! p\<close>
  using assms(2-)
proof (induct p)
  case FF
  have \<open>A \<turnstile>\<^sub>! (r \<^bold>\<longleftrightarrow>\<^sub>! r') \<^bold>\<longrightarrow>\<^sub>! ((r \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!) \<^bold>\<longleftrightarrow>\<^sub>! (r' \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!))\<close>
    by (auto intro: PA1)
  then have \<open>A \<turnstile>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!) \<^bold>\<longleftrightarrow>\<^sub>! (r' \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!)\<close>
    using r PR1 by blast
  then show ?case
    by (meson PFF Iff_Iff Iff_sym)
next
  case (Pro' x)
  have \<open>A \<turnstile>\<^sub>! (r \<^bold>\<longleftrightarrow>\<^sub>! r') \<^bold>\<longrightarrow>\<^sub>! ((r \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x) \<^bold>\<longleftrightarrow>\<^sub>! (r' \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x))\<close>
    by (auto intro: PA1)
  then have \<open>A \<turnstile>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x) \<^bold>\<longleftrightarrow>\<^sub>! (r' \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x)\<close>
    using r PR1 by blast
  then show ?case
    by (meson PPro Iff_Iff Iff_sym)
next
  case (Dis p q)
  then have \<open>A \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<or>\<^sub>! [r]\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! [r']\<^sub>! p \<^bold>\<or>\<^sub>! [r']\<^sub>! q\<close>
    by (simp add: Iff_Dis)
  then show ?case
    by (meson PDis Iff_Iff Iff_sym)
next
  case (Con p q)
  then have \<open>A \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<and>\<^sub>! [r]\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! [r']\<^sub>! p \<^bold>\<and>\<^sub>! [r']\<^sub>! q\<close>
    by (simp add: Iff_Con)
  then show ?case
    by (meson PCon Iff_Iff Iff_sym)
next
  case (Imp p q)
  then have \<open>A \<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! [r]\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! ([r']\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! [r']\<^sub>! q)\<close>
    by (simp add: Iff_Imp)
  then show ?case
    by (meson PImp Iff_Iff Iff_sym)
next
  case (K' i p)
  then have \<open>A \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! [r']\<^sub>! p\<close>
    by simp
  then have \<open>A \<turnstile>\<^sub>! K\<^sub>! i ([r]\<^sub>! p) \<^bold>\<longleftrightarrow>\<^sub>! K\<^sub>! i ([r']\<^sub>! p)\<close>
    using K'_map ConE ConI by metis
  then show ?case
    by (meson Iff_Iff Iff_Imp Iff_sym PK r)
next
  case (Ann s p)
  then show ?case
    by simp
qed

lemma Iff_Ann2:
  assumes \<open>A \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! p'\<close>
  shows \<open>A \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! [r]\<^sub>! p'\<close>
  using assms PAnn ConE ConI PImp PR1 by metis

lemma Iff_reduce: \<open>A \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! reduce p\<close>
proof (induct p)
  case (Dis p q)
  then show ?case
    by (simp add: Iff_Dis)
next
  case (Con p q)
  then show ?case
    by (simp add: Iff_Con)
next
  case (Imp p q)
  then show ?case
    by (simp add: Iff_Imp)
next
  case (K' i p)
  have
    \<open>A \<turnstile>\<^sub>! K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i (reduce p)\<close>
    \<open>A \<turnstile>\<^sub>! K\<^sub>! i (reduce p) \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i p\<close>
    using K' K'_map ConE by fast+
  then have \<open>A \<turnstile>\<^sub>! K\<^sub>! i p \<^bold>\<longleftrightarrow>\<^sub>! K\<^sub>! i (reduce p)\<close>
    using ConI by blast
  then show ?case
    by simp
next
  case (Ann r p)
  have \<open>A \<turnstile>\<^sub>! [reduce r]\<^sub>! reduce p \<^bold>\<longleftrightarrow>\<^sub>! reduce' (reduce r) (reduce p)\<close>
    using Iff_reduce' static_reduce by blast
  moreover have \<open>A \<turnstile>\<^sub>! [r]\<^sub>! reduce p \<^bold>\<longleftrightarrow>\<^sub>! [reduce r]\<^sub>! reduce p\<close>
    using Ann(1) Iff_Ann1 static_reduce by blast
  ultimately have \<open>A \<turnstile>\<^sub>! [r]\<^sub>! reduce p \<^bold>\<longleftrightarrow>\<^sub>! reduce' (reduce r) (reduce p)\<close>
    using Iff_Iff Iff_sym by blast
  moreover have \<open>A \<turnstile>\<^sub>! [r]\<^sub>! reduce p \<^bold>\<longleftrightarrow>\<^sub>! [r]\<^sub>! p\<close>
    by (meson Ann(2) static_reduce Iff_Ann2 Iff_sym)
  ultimately have \<open>A \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! reduce' (reduce r) (reduce p)\<close>
    using Iff_Iff by blast
  then show ?case
    by simp
qed (simp_all add: PA1)

theorem completeness\<^sub>P:
  assumes \<open>valid\<^sub>! P p\<close> and \<open>valid P (lower (reduce p)) \<Longrightarrow> A o lift \<turnstile> lower (reduce p)\<close>
  shows \<open>A \<turnstile>\<^sub>! p\<close>
proof -
  have \<open>valid\<^sub>! P (reduce p)\<close>
    using assms(1) reduce_semantics by fast
  moreover have \<open>static (reduce p)\<close>
    using static_reduce by fast
  ultimately have \<open>A \<turnstile>\<^sub>! reduce p\<close>
    using static_completeness assms(2) by blast
  moreover have \<open>A \<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! reduce p)\<close>
    using Iff_reduce by blast
  ultimately show ?thesis
    using ConE(2) PR1 by blast
qed

corollary completeness\<^sub>P\<^sub>K:
  assumes \<open>valid\<^sub>! (\<lambda>_. True) p\<close>
  shows \<open>A \<turnstile>\<^sub>! p\<close>
  using assms completeness\<^sub>P[where P=\<open>\<lambda>_. True\<close>] completeness\<^sub>K by metis

section \<open>System PAL + K\<close>

abbreviation SystemPK :: \<open>'i pfm \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>!\<^sub>K _\<close> [20] 20) where
  \<open>\<turnstile>\<^sub>!\<^sub>K p \<equiv> (\<lambda>_. False) \<turnstile>\<^sub>! p\<close>

lemma soundness\<^sub>P\<^sub>K: \<open>\<turnstile>\<^sub>!\<^sub>K p \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using soundness[where P=\<open>\<lambda>_. True\<close>] by metis

abbreviation validPK (\<open>valid\<^sub>!\<^sub>K\<close>) where
  \<open>valid\<^sub>!\<^sub>K \<equiv> valid\<^sub>! (\<lambda>_. True)\<close>

corollary
  assumes \<open>valid\<^sub>!\<^sub>K p\<close>
  shows \<open>\<turnstile>\<^sub>!\<^sub>K p\<close>
  using completeness\<^sub>P\<^sub>K assms .

theorem main\<^sub>P\<^sub>K: \<open>valid\<^sub>!\<^sub>K p = (\<turnstile>\<^sub>!\<^sub>K p)\<close>
  using soundness\<^sub>P\<^sub>K completeness\<^sub>P\<^sub>K by fast

corollary
  assumes \<open>valid\<^sub>!\<^sub>K p\<close> and \<open>w \<in> \<W> M\<close>
  shows \<open>M, w \<Turnstile>\<^sub>! p\<close>
  using assms soundness\<^sub>P\<^sub>K completeness\<^sub>P\<^sub>K by metis

section \<open>System PAL + T\<close>

text \<open>Also known as System PAL + M\<close>

inductive AxPT :: \<open>'i pfm \<Rightarrow> bool\<close> where
  \<open>AxPT (K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! p)\<close>

abbreviation SystemPT :: \<open>'i pfm \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>!\<^sub>T _\<close> [20] 20) where
  \<open>\<turnstile>\<^sub>!\<^sub>T p \<equiv> AxPT \<turnstile>\<^sub>! p\<close>

lemma soundness_AxPT: \<open>AxPT p \<Longrightarrow> reflexive M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  unfolding reflexive_def by (induct p rule: AxPT.induct) simp

lemma reflexive_restrict: \<open>reflexive M \<Longrightarrow> reflexive (restrict M p)\<close>
  unfolding reflexive_def by simp

lemma soundness\<^sub>P\<^sub>T: \<open>\<turnstile>\<^sub>!\<^sub>T p \<Longrightarrow> reflexive M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using soundness[where A=AxPT and P=reflexive] soundness_AxPT reflexive_restrict by fastforce

lemma AxT_AxPT: \<open>AxT = AxPT o lift\<close>
  unfolding comp_apply using lower_lift
  by (metis AxPT.simps AxT.simps lift.simps(5-6) lower.simps(5-6))

abbreviation validPT (\<open>valid\<^sub>!\<^sub>T\<close>) where
  \<open>valid\<^sub>!\<^sub>T \<equiv> valid\<^sub>! reflexive\<close>

lemma completeness\<^sub>P\<^sub>T:
  assumes \<open>valid\<^sub>!\<^sub>T p\<close>
  shows \<open>\<turnstile>\<^sub>!\<^sub>T p\<close>
  using assms completeness\<^sub>P[where p=p] completeness\<^sub>T AxT_AxPT by metis

theorem main\<^sub>P\<^sub>T: \<open>valid\<^sub>!\<^sub>T p \<longleftrightarrow> (\<turnstile>\<^sub>!\<^sub>T p)\<close>
  using soundness\<^sub>P\<^sub>T completeness\<^sub>P\<^sub>T by fast

corollary
  assumes \<open>reflexive M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>valid\<^sub>!\<^sub>T p \<longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using assms soundness\<^sub>P\<^sub>T completeness\<^sub>P\<^sub>T by fast

section \<open>System PKB\<close>

inductive AxPB :: \<open>'i pfm \<Rightarrow> bool\<close> where
  \<open>AxPB (p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i (L\<^sub>! i p))\<close>

abbreviation SystemPKB :: \<open>'i pfm \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>!\<^sub>K\<^sub>B _\<close> [20] 20) where
  \<open>\<turnstile>\<^sub>!\<^sub>K\<^sub>B p \<equiv> AxPB \<turnstile>\<^sub>! p\<close>

lemma soundness_AxPB: \<open>AxPB p \<Longrightarrow> symmetric M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  unfolding symmetric_def by (induct p rule: AxPB.induct) auto

lemma symmetric_restrict: \<open>symmetric M \<Longrightarrow> symmetric (restrict M p)\<close>
  unfolding symmetric_def by simp

lemma soundness\<^sub>P\<^sub>K\<^sub>B: \<open>\<turnstile>\<^sub>!\<^sub>K\<^sub>B p \<Longrightarrow> symmetric M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using soundness[where A=AxPB and P=symmetric] soundness_AxPB symmetric_restrict by fastforce

lemma AxB_AxPB: \<open>AxB = AxPB o lift\<close>
proof
  fix p :: \<open>'i fm\<close>
  show \<open>AxB p = (AxPB \<circ> lift) p\<close>
    unfolding comp_apply using lower_lift
    by (smt (verit, best) AxB.simps AxPB.simps lift.simps(1, 5-6) lower.simps(5-6))
qed

abbreviation validPKB (\<open>valid\<^sub>!\<^sub>K\<^sub>B\<close>) where
  \<open>valid\<^sub>!\<^sub>K\<^sub>B \<equiv> valid\<^sub>! symmetric\<close>

lemma completeness\<^sub>P\<^sub>K\<^sub>B:
  assumes \<open>valid\<^sub>!\<^sub>K\<^sub>B p\<close>
  shows \<open>\<turnstile>\<^sub>!\<^sub>K\<^sub>B p\<close>
  using assms completeness\<^sub>P[where p=p] completeness\<^sub>K\<^sub>B AxB_AxPB by metis

theorem main\<^sub>P\<^sub>K\<^sub>B: \<open>valid\<^sub>!\<^sub>K\<^sub>B p \<longleftrightarrow> (\<turnstile>\<^sub>!\<^sub>K\<^sub>B p)\<close>
  using soundness\<^sub>P\<^sub>K\<^sub>B completeness\<^sub>P\<^sub>K\<^sub>B by fast

corollary
  assumes \<open>symmetric M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>valid\<^sub>!\<^sub>K\<^sub>B p \<longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using assms soundness\<^sub>P\<^sub>K\<^sub>B completeness\<^sub>P\<^sub>K\<^sub>B by fast

section \<open>System PK4\<close>

inductive AxP4 :: \<open>'i pfm \<Rightarrow> bool\<close> where
  \<open>AxP4 (K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i (K\<^sub>! i p))\<close>

abbreviation SystemPK4 :: \<open>'i pfm \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>!\<^sub>K\<^sub>4 _\<close> [20] 20) where
  \<open>\<turnstile>\<^sub>!\<^sub>K\<^sub>4 p \<equiv> AxP4 \<turnstile>\<^sub>! p\<close>

lemma pos_introspection:
  assumes \<open>transitive M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>M, w \<Turnstile>\<^sub>! (K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i (K\<^sub>! i p))\<close>
proof -
  { assume \<open>M, w \<Turnstile>\<^sub>! K\<^sub>! i p\<close>
    then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile>\<^sub>! p\<close>
      by simp
    then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. \<forall>u \<in> \<W> M \<inter> \<K> M i v. M, u \<Turnstile>\<^sub>! p\<close>
      using \<open>transitive M\<close> \<open>w \<in> \<W> M\<close> unfolding transitive_def by blast
    then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile>\<^sub>! K\<^sub>! i p\<close>
      by simp
    then have \<open>M, w \<Turnstile>\<^sub>! K\<^sub>! i (K\<^sub>! i p)\<close>
      by simp }
  then show ?thesis
    by fastforce
qed

lemma soundness_AxP4: \<open>AxP4 p \<Longrightarrow> transitive M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  by (induct p rule: AxP4.induct) (metis pos_introspection)

lemma transitive_restrict: \<open>transitive M \<Longrightarrow> transitive (restrict M p)\<close>
  unfolding transitive_def
  by (metis (no_types, lifting) kripke.exhaust_sel kripke.inject mem_Collect_eq restrict.elims)

lemma soundness\<^sub>P\<^sub>K\<^sub>4: \<open>\<turnstile>\<^sub>!\<^sub>K\<^sub>4 p \<Longrightarrow> transitive M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using soundness[where A=AxP4 and P=transitive] soundness_AxP4 transitive_restrict by fastforce

lemma Ax4_AxP4: \<open>Ax4 = AxP4 o lift\<close>
proof
  fix p :: \<open>'i fm\<close>
  show \<open>Ax4 p = (AxP4 \<circ> lift) p\<close>
    unfolding comp_apply using lower_lift
    by (smt (verit, best) Ax4.simps AxP4.simps lift.simps(1, 5-6) lower.simps(5-6))
qed

abbreviation validPK4 (\<open>valid\<^sub>!\<^sub>K\<^sub>4\<close>) where
  \<open>valid\<^sub>!\<^sub>K\<^sub>4 \<equiv> valid\<^sub>! transitive\<close>

lemma completeness\<^sub>P\<^sub>K\<^sub>4:
  assumes \<open>valid\<^sub>!\<^sub>K\<^sub>4 p\<close>
  shows \<open>\<turnstile>\<^sub>!\<^sub>K\<^sub>4 p\<close>
  using assms completeness\<^sub>P[where p=p] completeness\<^sub>K\<^sub>4 Ax4_AxP4 by metis

theorem main\<^sub>P\<^sub>K\<^sub>4: \<open>valid\<^sub>!\<^sub>K\<^sub>4 p \<longleftrightarrow> (\<turnstile>\<^sub>!\<^sub>K\<^sub>4 p)\<close>
  using soundness\<^sub>P\<^sub>K\<^sub>4 completeness\<^sub>P\<^sub>K\<^sub>4 by fast

corollary
  assumes \<open>transitive M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>valid\<^sub>!\<^sub>K\<^sub>4 p \<longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using assms soundness\<^sub>P\<^sub>K\<^sub>4 completeness\<^sub>P\<^sub>K\<^sub>4 by fast

section \<open>System PS4\<close>

abbreviation SystemPS4 :: \<open>'i pfm \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>!\<^sub>S\<^sub>4 _\<close> [20] 20) where
  \<open>\<turnstile>\<^sub>!\<^sub>S\<^sub>4 p \<equiv> AxPT \<oplus> AxP4 \<turnstile>\<^sub>! p\<close>

lemma soundness_AxPT4: \<open>(AxPT \<oplus> AxP4) p \<Longrightarrow> refltrans M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using soundness_AxPT soundness_AxP4 by fast

lemma refltrans_restrict: \<open>refltrans M \<Longrightarrow> refltrans (restrict M p)\<close>
  using reflexive_restrict transitive_restrict by blast

lemma soundness\<^sub>P\<^sub>S\<^sub>4: \<open>\<turnstile>\<^sub>!\<^sub>S\<^sub>4 p \<Longrightarrow> reflexive M \<and> transitive M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using soundness[where A=\<open>AxPT \<oplus> AxP4\<close> and P=refltrans] soundness_AxPT4 refltrans_restrict
  by fastforce

lemma AxT4_AxPT4: \<open>(AxT \<oplus> Ax4) = (AxPT \<oplus> AxP4) o lift\<close>
  using AxT_AxPT Ax4_AxP4 unfolding comp_apply by metis

abbreviation validPS4 (\<open>valid\<^sub>!\<^sub>S\<^sub>4\<close>) where
  \<open>valid\<^sub>!\<^sub>S\<^sub>4 \<equiv> valid\<^sub>! refltrans\<close>

lemma completeness\<^sub>P\<^sub>S\<^sub>4:
  assumes \<open>valid\<^sub>!\<^sub>S\<^sub>4 p\<close>
  shows \<open>\<turnstile>\<^sub>!\<^sub>S\<^sub>4 p\<close>
  using assms completeness\<^sub>P[where P=refltrans and p=p] completeness\<^sub>S\<^sub>4 AxT4_AxPT4
  by (metis (mono_tags, lifting))

theorem main\<^sub>P\<^sub>S\<^sub>4: \<open>valid\<^sub>!\<^sub>S\<^sub>4 p \<longleftrightarrow> (\<turnstile>\<^sub>!\<^sub>S\<^sub>4 p)\<close>
  using soundness\<^sub>P\<^sub>S\<^sub>4 completeness\<^sub>P\<^sub>S\<^sub>4 by fast

corollary
  assumes \<open>reflexive M\<close> \<open>transitive M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>valid\<^sub>!\<^sub>S\<^sub>4 p \<longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using assms soundness\<^sub>P\<^sub>S\<^sub>4 completeness\<^sub>P\<^sub>S\<^sub>4 by fast

section \<open>System PS5\<close>

abbreviation SystemPS5 :: \<open>'i pfm \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>!\<^sub>S\<^sub>5 _\<close> [20] 20) where
  \<open>\<turnstile>\<^sub>!\<^sub>S\<^sub>5 p \<equiv> AxPT \<oplus> AxPB \<oplus> AxP4 \<turnstile>\<^sub>! p\<close>

abbreviation AxPTB4 :: \<open>'i pfm \<Rightarrow> bool\<close> where
  \<open>AxPTB4 \<equiv> AxPT \<oplus> AxPB \<oplus> AxP4\<close>

lemma soundness_AxPTB4: \<open>AxPTB4 p \<Longrightarrow> equivalence M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using soundness_AxPT soundness_AxPB soundness_AxP4 by fast

lemma equivalence_restrict: \<open>equivalence M \<Longrightarrow> equivalence (restrict M p)\<close>
  using reflexive_restrict symmetric_restrict transitive_restrict by blast

lemma soundness\<^sub>P\<^sub>S\<^sub>5: \<open>\<turnstile>\<^sub>!\<^sub>S\<^sub>5 p \<Longrightarrow> equivalence M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using soundness[where A=AxPTB4 and P=equivalence and M=M and w=w]
    soundness_AxPTB4 equivalence_restrict by fast

lemma AxTB4_AxPTB4: \<open>AxTB4 = AxPTB4 o lift\<close>
  using AxT_AxPT AxB_AxPB Ax4_AxP4 unfolding comp_apply by metis

abbreviation validPS5 (\<open>valid\<^sub>!\<^sub>S\<^sub>5\<close>) where
  \<open>valid\<^sub>!\<^sub>S\<^sub>5 \<equiv> valid\<^sub>! equivalence\<close>

lemma completeness\<^sub>P\<^sub>S\<^sub>5:
  assumes \<open>valid\<^sub>!\<^sub>S\<^sub>5 p\<close>
  shows \<open>\<turnstile>\<^sub>!\<^sub>S\<^sub>5 p\<close>
  using assms completeness\<^sub>P[where P=equivalence and p=p] completeness\<^sub>S\<^sub>5 AxTB4_AxPTB4
  by (metis (mono_tags, lifting))

theorem main\<^sub>P\<^sub>S\<^sub>5: \<open>valid\<^sub>!\<^sub>S\<^sub>5 p \<longleftrightarrow> (\<turnstile>\<^sub>!\<^sub>S\<^sub>5 p)\<close>
  using soundness\<^sub>P\<^sub>S\<^sub>5 completeness\<^sub>P\<^sub>S\<^sub>5 by fast

corollary
  assumes \<open>reflexive M\<close> \<open>symmetric M\<close> \<open>transitive M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>valid\<^sub>!\<^sub>S\<^sub>5 p \<longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using assms soundness\<^sub>P\<^sub>S\<^sub>5 completeness\<^sub>P\<^sub>S\<^sub>5 by fast

end
