(*
  File:      PAL.thy
  Author:    Asta Halkjær From

  This work is a formalization of public announcement logic.
  It includes proofs of soundness and completeness for variants of the axiom system
    PA + DIST! + NEC!.
  The completeness proofs build on the Epistemic Logic theory.
*)

theory PAL imports "Epistemic_Logic.Epistemic_Logic" begin

section \<open>Syntax\<close>

datatype 'i pfm
  = FF (\<open>\<^bold>\<bottom>\<^sub>!\<close>)
  | Pro' id (\<open>Pro\<^sub>!\<close>)
  | Dis \<open>'i pfm\<close> \<open>'i pfm\<close> (infixr \<open>\<^bold>\<or>\<^sub>!\<close> 60)
  | Con \<open>'i pfm\<close> \<open>'i pfm\<close> (infixr \<open>\<^bold>\<and>\<^sub>!\<close> 65)
  | Imp \<open>'i pfm\<close> \<open>'i pfm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<^sub>!\<close> 55)
  | K' 'i \<open>'i pfm\<close> (\<open>K\<^sub>!\<close>)
  | Ann \<open>'i pfm\<close> \<open>'i pfm\<close> (\<open>[_]\<^sub>! _\<close> [80, 80] 80)

abbreviation PIff :: \<open>'i pfm \<Rightarrow> 'i pfm \<Rightarrow> 'i pfm\<close> (infixr \<open>\<^bold>\<longleftrightarrow>\<^sub>!\<close> 55) where
  \<open>p \<^bold>\<longleftrightarrow>\<^sub>! q \<equiv> (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<and>\<^sub>! (q \<^bold>\<longrightarrow>\<^sub>! p)\<close>

abbreviation PNeg (\<open>\<^bold>\<not>\<^sub>! _\<close> [70] 70) where
  \<open>\<^bold>\<not>\<^sub>! p \<equiv> p \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!\<close>

abbreviation PL (\<open>L\<^sub>!\<close>) where
  \<open>L\<^sub>! i p \<equiv> (\<^bold>\<not>\<^sub>! (K\<^sub>! i (\<^bold>\<not>\<^sub>! p)))\<close>

primrec anns :: \<open>'i pfm \<Rightarrow> 'i pfm set\<close> where
  \<open>anns \<^bold>\<bottom>\<^sub>! = {}\<close>
| \<open>anns (Pro\<^sub>! _) = {}\<close>
| \<open>anns (p \<^bold>\<or>\<^sub>! q) = (anns p \<union> anns q)\<close>
| \<open>anns (p \<^bold>\<and>\<^sub>! q) = (anns p \<union> anns q)\<close>
| \<open>anns (p \<^bold>\<longrightarrow>\<^sub>! q) = (anns p \<union> anns q)\<close>
| \<open>anns (K\<^sub>! i p) = anns p\<close>
| \<open>anns ([r]\<^sub>! p) = {r} \<union> anns r \<union> anns p\<close>

section \<open>Semantics\<close>

fun
  psemantics :: \<open>('i, 'w) kripke \<Rightarrow> 'w \<Rightarrow> 'i pfm \<Rightarrow> bool\<close> (\<open>_, _ \<Turnstile>\<^sub>! _\<close> [50, 50, 50] 50) and
  restrict :: \<open>('i, 'w) kripke \<Rightarrow> 'i pfm \<Rightarrow> ('i, 'w) kripke\<close> (\<open>_[_!]\<close> [50, 50] 50) where
  \<open>M, w \<Turnstile>\<^sub>! \<^bold>\<bottom>\<^sub>! \<longleftrightarrow> False\<close>
| \<open>M, w \<Turnstile>\<^sub>! Pro\<^sub>! x \<longleftrightarrow> \<pi> M w x\<close>
| \<open>M, w \<Turnstile>\<^sub>! p \<^bold>\<or>\<^sub>! q \<longleftrightarrow> M, w \<Turnstile>\<^sub>! p \<or> M, w \<Turnstile>\<^sub>! q\<close>
| \<open>M, w \<Turnstile>\<^sub>! p \<^bold>\<and>\<^sub>! q \<longleftrightarrow> M, w \<Turnstile>\<^sub>! p \<and> M, w \<Turnstile>\<^sub>! q\<close>
| \<open>M, w \<Turnstile>\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! q \<longleftrightarrow> M, w \<Turnstile>\<^sub>! p \<longrightarrow> M, w \<Turnstile>\<^sub>! q\<close>
| \<open>M, w \<Turnstile>\<^sub>! K\<^sub>! i p \<longleftrightarrow> (\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile>\<^sub>! p)\<close>
| \<open>M, w \<Turnstile>\<^sub>! [r]\<^sub>! p \<longleftrightarrow> M, w \<Turnstile>\<^sub>! r \<longrightarrow> M[r!], w \<Turnstile>\<^sub>! p\<close>
| \<open>M[r!] = M \<lparr>\<W> := {w. w \<in> \<W> M \<and> M, w \<Turnstile>\<^sub>! r}\<rparr>\<close>

abbreviation validPStar :: \<open>(('i, 'w) kripke \<Rightarrow> bool) \<Rightarrow> 'i pfm set \<Rightarrow> 'i pfm \<Rightarrow> bool\<close>
  (\<open>_; _ \<TTurnstile>\<^sub>!\<star> _\<close> [50, 50, 50] 50) where
  \<open>P; G \<TTurnstile>\<^sub>!\<star> p \<equiv> \<forall>M. P M \<longrightarrow> (\<forall>w \<in> \<W> M. (\<forall>q \<in> G. M, w \<Turnstile>\<^sub>! q) \<longrightarrow> M, w \<Turnstile>\<^sub>! p)\<close>

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
  shows \<open>(M, w \<Turnstile>\<^sub>! [p]\<^sub>! q) = (M, w \<Turnstile>\<^sub>! reduce' p q)\<close>
  using assms by (induct q arbitrary: w) auto

lemma reduce_semantics: \<open>M, w \<Turnstile>\<^sub>! p \<longleftrightarrow> M, w \<Turnstile>\<^sub>! reduce p\<close>
proof (induct p arbitrary: M w)
  case (Ann p q)
  then show ?case
    using reduce'_semantics static_reduce by fastforce
qed simp_all

section \<open>Chains of Implications\<close>

primrec implyP :: \<open>'i pfm list \<Rightarrow> 'i pfm \<Rightarrow> 'i pfm\<close> (infixr \<open>\<^bold>\<leadsto>\<^sub>!\<close> 56) where
  \<open>([] \<^bold>\<leadsto>\<^sub>! q) = q\<close>
| \<open>(p # ps \<^bold>\<leadsto>\<^sub>! q) = (p \<^bold>\<longrightarrow>\<^sub>! ps \<^bold>\<leadsto>\<^sub>! q)\<close>

lemma lift_implyP: \<open>lift (ps \<^bold>\<leadsto> q) = (map lift ps \<^bold>\<leadsto>\<^sub>! lift q)\<close>
  by (induct ps) auto

lemma reduce_implyP: \<open>reduce (ps \<^bold>\<leadsto>\<^sub>! q) = (map reduce ps \<^bold>\<leadsto>\<^sub>! reduce q)\<close>
  by (induct ps) auto

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

inductive PAK :: \<open>('i pfm \<Rightarrow> bool) \<Rightarrow> ('i pfm \<Rightarrow> bool) \<Rightarrow> 'i pfm \<Rightarrow> bool\<close>
  (\<open>_; _ \<turnstile>\<^sub>! _\<close> [50, 50, 50] 50)
  for A B :: \<open>'i pfm \<Rightarrow> bool\<close> where
    PA1: \<open>ptautology p \<Longrightarrow> A; B \<turnstile>\<^sub>! p\<close>
  | PA2: \<open>A; B \<turnstile>\<^sub>! K\<^sub>! i p \<^bold>\<and>\<^sub>! K\<^sub>! i (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i q\<close>
  | PAx: \<open>A p \<Longrightarrow> A; B \<turnstile>\<^sub>! p\<close>
  | PR1: \<open>A; B \<turnstile>\<^sub>! p \<Longrightarrow> A; B \<turnstile>\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! q \<Longrightarrow> A; B \<turnstile>\<^sub>! q\<close>
  | PR2: \<open>A; B \<turnstile>\<^sub>! p \<Longrightarrow> A; B \<turnstile>\<^sub>! K\<^sub>! i p\<close>
  | PAnn: \<open>A; B \<turnstile>\<^sub>! p \<Longrightarrow> B r \<Longrightarrow> A; B \<turnstile>\<^sub>! [r]\<^sub>! p\<close>
  | PFF: \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! \<^bold>\<bottom>\<^sub>! \<^bold>\<longleftrightarrow>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!)\<close>
  | PPro: \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! Pro\<^sub>! x \<^bold>\<longleftrightarrow>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x)\<close>
  | PDis: \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! (p \<^bold>\<or>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! [r]\<^sub>! p \<^bold>\<or>\<^sub>! [r]\<^sub>! q\<close>
  | PCon: \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! (p \<^bold>\<and>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! [r]\<^sub>! p \<^bold>\<and>\<^sub>! [r]\<^sub>! q\<close>
  | PImp: \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! ([r]\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! [r]\<^sub>! q)\<close>
  | PK: \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! K\<^sub>! i p \<^bold>\<longleftrightarrow>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i ([r]\<^sub>! p))\<close>

abbreviation PAK_assms (\<open>_; _; _ \<turnstile>\<^sub>! _\<close> [50, 50, 50, 50] 50) where
  \<open>A; B; G \<turnstile>\<^sub>! p \<equiv> \<exists>qs. set qs \<subseteq> G \<and> (A; B \<turnstile>\<^sub>! qs \<^bold>\<leadsto>\<^sub>! p)\<close>

lemma eval_peval: \<open>eval h (g o lift) p = peval h g (lift p)\<close>
  by (induct p) simp_all

lemma tautology_ptautology: \<open>tautology p \<Longrightarrow> ptautology (lift p)\<close>
  using eval_peval by blast

theorem AK_PAK: \<open>A o lift \<turnstile> p \<Longrightarrow> A; B \<turnstile>\<^sub>! lift p\<close>
  by (induct p rule: AK.induct) (auto intro: PAK.intros(1-5) simp: tautology_ptautology)

abbreviation validP
  :: \<open>(('i, 'i fm set) kripke \<Rightarrow> bool) \<Rightarrow> 'i pfm set \<Rightarrow> 'i pfm \<Rightarrow> bool\<close>
  (\<open>_; _ \<TTurnstile>\<^sub>! _\<close> [50, 50, 50] 50)
  where \<open>P; G \<TTurnstile>\<^sub>! p \<equiv> P; G \<TTurnstile>\<^sub>!\<star> p\<close>

lemma set_map_inv:
  assumes \<open>set xs \<subseteq> f ` X\<close>
  shows \<open>\<exists>ys. set ys \<subseteq> X \<and> map f ys = xs\<close>
  using assms
proof (induct xs)
  case (Cons x xs)
  then obtain ys where \<open>set ys \<subseteq> X\<close> \<open>map f ys = xs\<close>
    by auto
  moreover obtain y where \<open>y \<in> X\<close> \<open>f y = x\<close>
    using Cons.prems by auto
  ultimately have \<open>set (y # ys) \<subseteq> X\<close> \<open>map f (y # ys) = x # xs\<close>
    by simp_all
  then show ?case
    by meson
qed simp

lemma strong_static_completeness':
  assumes \<open>static p\<close> and \<open>\<forall>q \<in> G. static q\<close> and \<open>P; G \<TTurnstile>\<^sub>! p\<close>
    and \<open>P; lower ` G \<TTurnstile>\<star> lower p \<Longrightarrow> A o lift; lower ` G \<turnstile> lower p\<close>
  shows \<open>A; B; G \<turnstile>\<^sub>! p\<close>
proof -
  have \<open>P; lower ` G \<TTurnstile>\<star> lower p\<close>
    using assms by (simp add: lower_semantics)
  then have \<open>A o lift; lower ` G \<turnstile> lower p\<close>
    using assms(4) by blast
  then obtain qs where \<open>set qs \<subseteq> G\<close> and \<open>A o lift \<turnstile> map lower qs \<^bold>\<leadsto> lower p\<close>
    using set_map_inv by blast
  then have \<open>A; B \<turnstile>\<^sub>! lift (map lower qs \<^bold>\<leadsto> lower p)\<close>
    using AK_PAK by fast
  then have \<open>A; B \<turnstile>\<^sub>! map lift (map lower qs) \<^bold>\<leadsto>\<^sub>! lift (lower p)\<close>
    using lift_implyP by metis
  then have \<open>A; B \<turnstile>\<^sub>! map (lift o lower) qs \<^bold>\<leadsto>\<^sub>! lift (lower p)\<close>
    by simp
  then show ?thesis
    using assms(1-2) \<open>set qs \<subseteq> G\<close> lift_lower
    by (metis (mono_tags, lifting) comp_apply map_idI subset_eq)
qed

theorem strong_static_completeness:
  assumes \<open>static p\<close> and \<open>\<forall>q \<in> G. static q\<close> and \<open>P; G \<TTurnstile>\<^sub>! p\<close>
    and \<open>\<And>G p. P; G \<TTurnstile> p \<Longrightarrow> A o lift; G \<turnstile> p\<close>
  shows \<open>A; B; G \<turnstile>\<^sub>! p\<close>
  using strong_static_completeness' assms .

corollary static_completeness':
  assumes \<open>static p\<close> and \<open>P; {} \<TTurnstile>\<^sub>!\<star> p\<close>
    and \<open>P; {} \<TTurnstile> lower p \<Longrightarrow> A o lift \<turnstile> lower p\<close>
  shows \<open>A; B \<turnstile>\<^sub>! p\<close>
  using assms strong_static_completeness'[where G=\<open>{}\<close> and p=p] by simp

corollary static_completeness:
  assumes \<open>static p\<close> and \<open>P; {} \<TTurnstile>\<^sub>!\<star> p\<close> and \<open>\<And>p. P; {} \<TTurnstile> p \<Longrightarrow> A o lift \<turnstile> p\<close>
  shows \<open>A; B \<turnstile>\<^sub>! p\<close>
  using static_completeness' assms .

corollary
  assumes \<open>static p\<close> \<open>(\<lambda>_. True); {} \<TTurnstile>\<^sub>! p\<close>
  shows \<open>A; B \<turnstile>\<^sub>! p\<close>
  using assms static_completeness[where P=\<open>\<lambda>_. True\<close> and p=p] completeness\<^sub>A by blast

section \<open>Soundness\<close>

lemma peval_semantics:
  \<open>peval (val w) (\<lambda>q. \<lparr>\<W> = W, \<K> = r, \<pi> = val\<rparr>, w \<Turnstile>\<^sub>! q) p = (\<lparr>\<W> = W, \<K> = r, \<pi> = val\<rparr>, w \<Turnstile>\<^sub>! p)\<close>
  by (induct p) simp_all

lemma ptautology:
  assumes \<open>ptautology p\<close>
  shows \<open>M, w \<Turnstile>\<^sub>! p\<close>
proof -
  from assms have \<open>peval (g w) (\<lambda>q. \<lparr>\<W> = W, \<K> = r, \<pi> = g\<rparr>, w \<Turnstile>\<^sub>! q) p\<close> for W g r
    by simp
  then have \<open>\<lparr>\<W> = W, \<K> = r, \<pi> = g\<rparr>, w \<Turnstile>\<^sub>! p\<close> for W g r
    using peval_semantics by fast
  then show \<open>M, w \<Turnstile>\<^sub>! p\<close>
    by (metis kripke.cases)
qed

theorem soundness\<^sub>P:
  assumes
    \<open>\<And>M p w. A p \<Longrightarrow> P M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
    \<open>\<And>M r. P M \<Longrightarrow> B r \<Longrightarrow> P (M[r!])\<close>
  shows \<open>A; B \<turnstile>\<^sub>! p \<Longrightarrow> P M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
proof (induct p arbitrary: M w rule: PAK.induct)
  case (PAnn p r)
  then show ?case
    using assms by simp
qed (simp_all add: assms ptautology)

corollary \<open>(\<lambda>_. False); B \<turnstile>\<^sub>! p \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using soundness\<^sub>P[where P=\<open>\<lambda>_. True\<close>] by metis

section \<open>Strong Soundness\<close>

lemma ptautology_imply_superset:
  assumes \<open>set ps \<subseteq> set qs\<close>
  shows \<open>ptautology (ps \<^bold>\<leadsto>\<^sub>! r \<^bold>\<longrightarrow>\<^sub>! qs \<^bold>\<leadsto>\<^sub>! r)\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain g h where \<open>\<not> peval g h (ps \<^bold>\<leadsto>\<^sub>! r \<^bold>\<longrightarrow>\<^sub>! qs \<^bold>\<leadsto>\<^sub>! r)\<close>
    by blast
  then have \<open>peval g h (ps \<^bold>\<leadsto>\<^sub>! r)\<close> \<open>\<not> peval g h (qs \<^bold>\<leadsto>\<^sub>! r)\<close>
    by simp_all
  then consider (np) \<open>\<exists>p \<in> set ps. \<not> peval g h p\<close> | (r) \<open>\<forall>p \<in> set ps. peval g h p\<close> \<open>peval g h r\<close>
    by (induct ps) auto
  then show False
  proof cases
    case np
    then have \<open>\<exists>p \<in> set qs. \<not> peval g h p\<close>
      using \<open>set ps \<subseteq> set qs\<close> by blast
    then have \<open>peval g h (qs \<^bold>\<leadsto>\<^sub>! r)\<close>
      by (induct qs) simp_all
    then show ?thesis
      using \<open>\<not> peval g h (qs \<^bold>\<leadsto>\<^sub>! r)\<close> by blast
  next
    case r
    then have \<open>peval g h (qs \<^bold>\<leadsto>\<^sub>! r)\<close>
      by (induct qs) simp_all
    then show ?thesis
      using \<open>\<not> peval g h (qs \<^bold>\<leadsto>\<^sub>! r)\<close> by blast
  qed
qed

lemma PK_imply_weaken:
  assumes \<open>A; B \<turnstile>\<^sub>! ps \<^bold>\<leadsto>\<^sub>! q\<close> \<open>set ps \<subseteq> set ps'\<close>
  shows \<open>A; B \<turnstile>\<^sub>! ps' \<^bold>\<leadsto>\<^sub>! q\<close>
proof -
  have \<open>ptautology (ps \<^bold>\<leadsto>\<^sub>! q \<^bold>\<longrightarrow>\<^sub>! ps' \<^bold>\<leadsto>\<^sub>! q)\<close>
    using \<open>set ps \<subseteq> set ps'\<close> ptautology_imply_superset by blast
  then have \<open>A; B \<turnstile>\<^sub>! ps \<^bold>\<leadsto>\<^sub>! q \<^bold>\<longrightarrow>\<^sub>! ps' \<^bold>\<leadsto>\<^sub>! q\<close>
    using PA1 by blast
  then show ?thesis
    using \<open>A; B \<turnstile>\<^sub>! ps \<^bold>\<leadsto>\<^sub>! q\<close> PR1 by blast
qed

lemma implyP_append: \<open>(ps @ ps' \<^bold>\<leadsto>\<^sub>! q) = (ps \<^bold>\<leadsto>\<^sub>! ps' \<^bold>\<leadsto>\<^sub>! q)\<close>
  by (induct ps) simp_all

lemma PK_ImpI:
  assumes \<open>A; B \<turnstile>\<^sub>! p # G \<^bold>\<leadsto>\<^sub>! q\<close>
  shows \<open>A; B \<turnstile>\<^sub>! G \<^bold>\<leadsto>\<^sub>! (p \<^bold>\<longrightarrow>\<^sub>! q)\<close>
proof -
  have \<open>set (p # G) \<subseteq> set (G @ [p])\<close>
    by simp
  then have \<open>A; B \<turnstile>\<^sub>! G @ [p] \<^bold>\<leadsto>\<^sub>! q\<close>
    using assms PK_imply_weaken by blast
  then have \<open>A; B \<turnstile>\<^sub>! G \<^bold>\<leadsto>\<^sub>! [p] \<^bold>\<leadsto>\<^sub>! q\<close>
    using implyP_append by metis
  then show ?thesis
    by simp
qed

corollary soundness_imply\<^sub>P:
  assumes
    \<open>\<And>M p w. A p \<Longrightarrow> P M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
    \<open>\<And>M r. P M \<Longrightarrow> B r \<Longrightarrow> P (M[r!])\<close>
  shows \<open>A; B \<turnstile>\<^sub>! qs \<^bold>\<leadsto>\<^sub>! p \<Longrightarrow> P M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> \<forall>q \<in> set qs. M, w \<Turnstile>\<^sub>! q \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
proof (induct qs arbitrary: p)
  case Nil
  then show ?case
    using soundness\<^sub>P[of A P B p M w] assms by simp
next
  case (Cons q qs)
  then show ?case
    using PK_ImpI by fastforce
qed

theorem strong_soundness\<^sub>P:
  assumes
    \<open>\<And>M w p. A p \<Longrightarrow> P M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
    \<open>\<And>M r. P M \<Longrightarrow> B r \<Longrightarrow> P (M[r!])\<close>
  shows \<open>A; B; G \<turnstile>\<^sub>! p \<Longrightarrow> P; G \<TTurnstile>\<^sub>!\<star> p\<close>
proof safe
  fix qs w and M :: \<open>('a, 'b) kripke\<close>
  assume \<open>A; B \<turnstile>\<^sub>! qs \<^bold>\<leadsto>\<^sub>! p\<close>
  moreover assume \<open>set qs \<subseteq> G\<close> \<open>\<forall>q \<in> G. M, w \<Turnstile>\<^sub>! q\<close>
  then have \<open>\<forall>q \<in> set qs. M, w \<Turnstile>\<^sub>! q\<close>
    using \<open>set qs \<subseteq> G\<close> by blast
  moreover assume \<open>P M\<close> \<open>w \<in> \<W> M\<close>
  ultimately show \<open>M, w \<Turnstile>\<^sub>! p\<close>
    using soundness_imply\<^sub>P[of A P B qs p] assms by blast
qed

section \<open>Completeness\<close>

lemma ConE:
  assumes \<open>A; B \<turnstile>\<^sub>! p \<^bold>\<and>\<^sub>! q\<close>
  shows \<open>A; B \<turnstile>\<^sub>! p\<close> \<open>A; B \<turnstile>\<^sub>! q\<close>
  using assms by (metis PA1 PR1 peval.simps(4-5))+

lemma Iff_Dis:
  assumes \<open>A; B \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! p'\<close> \<open>A; B \<turnstile>\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! q'\<close>
  shows \<open>A; B \<turnstile>\<^sub>! ((p \<^bold>\<or>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<or>\<^sub>! q'))\<close>
proof -
  have \<open>A; B \<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! p') \<^bold>\<longrightarrow>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! q') \<^bold>\<longrightarrow>\<^sub>! ((p \<^bold>\<or>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<or>\<^sub>! q'))\<close>
    by (simp add: PA1)
  then show ?thesis
    using assms PR1 by blast
qed

lemma Iff_Con:
  assumes \<open>A; B \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! p'\<close> \<open>A; B \<turnstile>\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! q'\<close>
  shows \<open>A; B \<turnstile>\<^sub>! (p \<^bold>\<and>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<and>\<^sub>! q')\<close>
proof -
  have \<open>A; B \<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! p') \<^bold>\<longrightarrow>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! q') \<^bold>\<longrightarrow>\<^sub>! ((p \<^bold>\<and>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<and>\<^sub>! q'))\<close>
    by (simp add: PA1)
  then show ?thesis
    using assms PR1 by blast
qed

lemma Iff_Imp:
  assumes \<open>A; B \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! p'\<close> \<open>A; B \<turnstile>\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! q'\<close>
  shows \<open>A; B \<turnstile>\<^sub>! ((p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<longrightarrow>\<^sub>! q'))\<close>
proof -
  have \<open>A; B \<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! p') \<^bold>\<longrightarrow>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! q') \<^bold>\<longrightarrow>\<^sub>! ((p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (p' \<^bold>\<longrightarrow>\<^sub>! q'))\<close>
    by (simp add: PA1)
  then show ?thesis
    using assms PR1 by blast
qed

lemma Iff_sym: \<open>(A; B \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! q) = (A; B \<turnstile>\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! p)\<close>
proof -
  have \<open>A; B \<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! (q \<^bold>\<longleftrightarrow>\<^sub>! p)\<close>
    by (simp add: PA1)
  then show ?thesis
    using PR1 ConE by blast
qed

lemma Iff_Iff:
  assumes \<open>A; B \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! p'\<close> \<open>A; B \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! q\<close>
  shows \<open>A; B \<turnstile>\<^sub>! p' \<^bold>\<longleftrightarrow>\<^sub>! q\<close>
proof -
  have \<open>ptautology ((p \<^bold>\<longleftrightarrow>\<^sub>! p') \<^bold>\<longrightarrow>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! (p' \<^bold>\<longleftrightarrow>\<^sub>! q))\<close>
    by (metis peval.simps(4-5))
  with PA1 have \<open>A; B \<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! p') \<^bold>\<longrightarrow>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! (p' \<^bold>\<longleftrightarrow>\<^sub>! q)\<close> .
  then show ?thesis
    using assms PR1 by blast
qed

lemma K'_A2': \<open>A; B \<turnstile>\<^sub>! K\<^sub>! i (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i q\<close>
proof -
  have \<open>A; B \<turnstile>\<^sub>! K\<^sub>! i p \<^bold>\<and>\<^sub>! K\<^sub>! i (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i q\<close>
    using PA2 by fast
  moreover have \<open>A; B \<turnstile>\<^sub>! (P \<^bold>\<and>\<^sub>! Q \<^bold>\<longrightarrow>\<^sub>! R) \<^bold>\<longrightarrow>\<^sub>! (Q \<^bold>\<longrightarrow>\<^sub>! P \<^bold>\<longrightarrow>\<^sub>! R)\<close> for P Q R
    by (simp add: PA1)
  ultimately show ?thesis
    using PR1 by fast
qed

lemma K'_map:
  assumes \<open>A; B \<turnstile>\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! q\<close>
  shows \<open>A; B \<turnstile>\<^sub>! K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i q\<close>
proof -
  note \<open>A; B \<turnstile>\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! q\<close>
  then have \<open>A; B \<turnstile>\<^sub>! K\<^sub>! i (p \<^bold>\<longrightarrow>\<^sub>! q)\<close>
    using PR2 by fast
  moreover have \<open>A; B \<turnstile>\<^sub>! K\<^sub>! i (p \<^bold>\<longrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i q\<close>
    using K'_A2' by fast
  ultimately show ?thesis
    using PR1 by fast
qed

lemma ConI:
  assumes \<open>A; B \<turnstile>\<^sub>! p\<close> \<open>A; B \<turnstile>\<^sub>! q\<close>
  shows \<open>A; B \<turnstile>\<^sub>! p \<^bold>\<and>\<^sub>! q\<close>
proof -
  have \<open>A; B \<turnstile>\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! q \<^bold>\<longrightarrow>\<^sub>! p \<^bold>\<and>\<^sub>! q\<close>
    by (simp add: PA1)
  then show ?thesis
    using assms PR1 by blast
qed

lemma Iff_wk:
  assumes \<open>A; B \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! q\<close>
  shows \<open>A; B \<turnstile>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! p) \<^bold>\<longleftrightarrow>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! q)\<close>
proof -
  have \<open>A; B \<turnstile>\<^sub>! (p \<^bold>\<longleftrightarrow>\<^sub>! q) \<^bold>\<longrightarrow>\<^sub>! ((r \<^bold>\<longrightarrow>\<^sub>! p) \<^bold>\<longleftrightarrow>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! q))\<close>
    by (simp add: PA1)
  then show ?thesis
    using assms PR1 by blast
qed

lemma Iff_reduce':
  assumes \<open>static p\<close>
  shows \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! reduce' r p\<close>
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
  then have \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<or>\<^sub>! [r]\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! reduce' r (p \<^bold>\<or>\<^sub>! q)\<close>
    using Iff_Dis by fastforce
  moreover have \<open>A; B \<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<or>\<^sub>! [r]\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! ([r]\<^sub>! (p \<^bold>\<or>\<^sub>! q))\<close>
    using PDis Iff_sym by fastforce
  ultimately show ?case
    using PA1 PR1 Iff_Iff by blast
next
  case (Con p q)
  then have \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<and>\<^sub>! [r]\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! reduce' r (p \<^bold>\<and>\<^sub>! q)\<close>
    using Iff_Con by fastforce
  moreover have \<open>A; B \<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<and>\<^sub>! [r]\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! ([r]\<^sub>! (p \<^bold>\<and>\<^sub>! q))\<close>
    using PCon Iff_sym by fastforce
  ultimately show ?case
    using PA1 PR1 Iff_Iff by blast
next
  case (Imp p q)
  then have \<open>A; B \<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! [r]\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! reduce' r (p \<^bold>\<longrightarrow>\<^sub>! q)\<close>
    using Iff_Imp by fastforce
  moreover have \<open>A; B \<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! [r]\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! ([r]\<^sub>! (p \<^bold>\<longrightarrow>\<^sub>! q))\<close>
    using PImp Iff_sym by fastforce
  ultimately show ?case
    using PA1 PR1 Iff_Iff by blast
next
  case (K' i p)
  then have \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! reduce' r p\<close>
    by simp
  then have \<open>A; B \<turnstile>\<^sub>! K\<^sub>! i ([r]\<^sub>! p) \<^bold>\<longleftrightarrow>\<^sub>! K\<^sub>! i (reduce' r p)\<close>
    using K'_map ConE ConI by metis
  moreover have \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! K\<^sub>! i p \<^bold>\<longleftrightarrow>\<^sub>! r \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i ([r]\<^sub>! p)\<close>
    using PK .
  ultimately have \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! K\<^sub>! i p \<^bold>\<longleftrightarrow>\<^sub>! r \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i (reduce' r p)\<close>
    by (meson Iff_Iff Iff_sym Iff_wk)
  then show ?case
    by simp
next
  case (Ann r p)
  then show ?case
    by simp
qed

lemma Iff_Ann1:
  assumes r: \<open>A; B \<turnstile>\<^sub>! r \<^bold>\<longleftrightarrow>\<^sub>! r'\<close> and \<open>static p\<close>
  shows \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! [r']\<^sub>! p\<close>
  using assms(2-)
proof (induct p)
  case FF
  have \<open>A; B \<turnstile>\<^sub>! (r \<^bold>\<longleftrightarrow>\<^sub>! r') \<^bold>\<longrightarrow>\<^sub>! ((r \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!) \<^bold>\<longleftrightarrow>\<^sub>! (r' \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!))\<close>
    by (auto intro: PA1)
  then have \<open>A; B \<turnstile>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!) \<^bold>\<longleftrightarrow>\<^sub>! (r' \<^bold>\<longrightarrow>\<^sub>! \<^bold>\<bottom>\<^sub>!)\<close>
    using r PR1 by blast
  then show ?case
    by (meson PFF Iff_Iff Iff_sym)
next
  case (Pro' x)
  have \<open>A; B \<turnstile>\<^sub>! (r \<^bold>\<longleftrightarrow>\<^sub>! r') \<^bold>\<longrightarrow>\<^sub>! ((r \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x) \<^bold>\<longleftrightarrow>\<^sub>! (r' \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x))\<close>
    by (auto intro: PA1)
  then have \<open>A; B \<turnstile>\<^sub>! (r \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x) \<^bold>\<longleftrightarrow>\<^sub>! (r' \<^bold>\<longrightarrow>\<^sub>! Pro\<^sub>! x)\<close>
    using r PR1 by blast
  then show ?case
    by (meson PPro Iff_Iff Iff_sym)
next
  case (Dis p q)
  then have \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<or>\<^sub>! [r]\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! [r']\<^sub>! p \<^bold>\<or>\<^sub>! [r']\<^sub>! q\<close>
    by (simp add: Iff_Dis)
  then show ?case
    by (meson PDis Iff_Iff Iff_sym)
next
  case (Con p q)
  then have \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<and>\<^sub>! [r]\<^sub>! q \<^bold>\<longleftrightarrow>\<^sub>! [r']\<^sub>! p \<^bold>\<and>\<^sub>! [r']\<^sub>! q\<close>
    by (simp add: Iff_Con)
  then show ?case
    by (meson PCon Iff_Iff Iff_sym)
next
  case (Imp p q)
  then have \<open>A; B \<turnstile>\<^sub>! ([r]\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! [r]\<^sub>! q) \<^bold>\<longleftrightarrow>\<^sub>! ([r']\<^sub>! p \<^bold>\<longrightarrow>\<^sub>! [r']\<^sub>! q)\<close>
    by (simp add: Iff_Imp)
  then show ?case
    by (meson PImp Iff_Iff Iff_sym)
next
  case (K' i p)
  then have \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! [r']\<^sub>! p\<close>
    by simp
  then have \<open>A; B \<turnstile>\<^sub>! K\<^sub>! i ([r]\<^sub>! p) \<^bold>\<longleftrightarrow>\<^sub>! K\<^sub>! i ([r']\<^sub>! p)\<close>
    using K'_map ConE ConI by metis
  then show ?case
    by (meson Iff_Iff Iff_Imp Iff_sym PK r)
next
  case (Ann s p)
  then show ?case
    by simp
qed

lemma Iff_Ann2:
  assumes \<open>A; B \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! p'\<close> and \<open>B r\<close>
  shows \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! [r]\<^sub>! p'\<close>
  using assms PAnn ConE ConI PImp PR1 by metis

lemma Iff_reduce:
  assumes \<open>\<forall>r \<in> anns p. B r\<close>
  shows \<open>A; B \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! reduce p\<close>
  using assms
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
  then have
    \<open>A; B \<turnstile>\<^sub>! K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i (reduce p)\<close>
    \<open>A; B \<turnstile>\<^sub>! K\<^sub>! i (reduce p) \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i p\<close>
    using K'_map ConE by fastforce+
  then have \<open>A; B \<turnstile>\<^sub>! K\<^sub>! i p \<^bold>\<longleftrightarrow>\<^sub>! K\<^sub>! i (reduce p)\<close>
    using ConI by blast
  then show ?case
    by simp
next
  case (Ann r p)
  then have \<open>B r\<close>
    by simp
  have \<open>A; B \<turnstile>\<^sub>! [reduce r]\<^sub>! reduce p \<^bold>\<longleftrightarrow>\<^sub>! reduce' (reduce r) (reduce p)\<close>
    using Iff_reduce' static_reduce by blast
  moreover have \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! reduce p \<^bold>\<longleftrightarrow>\<^sub>! [reduce r]\<^sub>! reduce p\<close>
    using Ann Iff_Ann1 static_reduce by fastforce
  ultimately have \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! reduce p \<^bold>\<longleftrightarrow>\<^sub>! reduce' (reduce r) (reduce p)\<close>
    using Iff_Iff Iff_sym by blast
  moreover have \<open>\<forall>r \<in> anns p. B r\<close>
    using Ann.prems by simp
  then have \<open>A; B \<turnstile>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! reduce p\<close>
    using Ann.hyps(2) by blast
  then have \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! reduce p \<^bold>\<longleftrightarrow>\<^sub>! [r]\<^sub>! p\<close>
    using \<open>B r\<close> Iff_Ann2 Iff_sym by blast
  ultimately have \<open>A; B \<turnstile>\<^sub>! [r]\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! reduce' (reduce r) (reduce p)\<close>
    using Iff_Iff by blast
  then show ?case
    by simp
qed (simp_all add: PA1)

lemma anns_implyP [simp]:
  \<open>anns (ps \<^bold>\<leadsto>\<^sub>! q) =  anns q \<union> (\<Union>p \<in> set ps. anns p)\<close>
  by (induct ps) auto

lemma strong_completeness\<^sub>P':
  assumes \<open>P; G \<TTurnstile>\<^sub>! p\<close>
    and \<open>\<forall>r \<in> anns p. B r\<close> \<open>\<forall>q \<in> G. \<forall>r \<in> anns q. B r\<close>
    and \<open>P; lower ` reduce ` G \<TTurnstile>\<star> lower (reduce p) \<Longrightarrow>
      A o lift; lower ` reduce ` G \<turnstile> lower (reduce p)\<close>
  shows \<open>A; B; G \<turnstile>\<^sub>! p\<close>
proof -
  have \<open>P; reduce ` G \<TTurnstile>\<^sub>!\<star> reduce p\<close>
    using assms(1) reduce_semantics by fast
  moreover have \<open>static (reduce p)\<close> \<open>\<forall>q \<in> reduce ` G. static q\<close>
    using static_reduce by fast+
  ultimately have \<open>A; B; reduce ` G \<turnstile>\<^sub>! reduce p\<close>
    using assms(4) strong_static_completeness'[where G=\<open>reduce ` G\<close> and p=\<open>reduce p\<close>]
    by presburger
  then have \<open>\<exists>qs. set qs \<subseteq> G \<and> (A; B \<turnstile>\<^sub>! map reduce qs \<^bold>\<leadsto>\<^sub>! reduce p)\<close>
    using set_map_inv by fast
  then obtain qs where qs: \<open>set qs \<subseteq> G\<close> and \<open>A; B \<turnstile>\<^sub>! map reduce qs \<^bold>\<leadsto>\<^sub>! reduce p\<close>
    by blast
  then have \<open>A; B \<turnstile>\<^sub>! reduce (qs \<^bold>\<leadsto>\<^sub>! p)\<close>
    using reduce_implyP by metis
  moreover have \<open>\<forall>r \<in> anns (qs \<^bold>\<leadsto>\<^sub>! p). B r\<close>
    using assms(2-3) qs by auto
  then have \<open>A; B \<turnstile>\<^sub>! qs \<^bold>\<leadsto>\<^sub>! p \<^bold>\<longleftrightarrow>\<^sub>! reduce (qs \<^bold>\<leadsto>\<^sub>! p)\<close>
    using Iff_reduce by blast
  ultimately have \<open>A; B \<turnstile>\<^sub>! qs \<^bold>\<leadsto>\<^sub>! p\<close>
    using ConE(2) PR1 by blast
  then show ?thesis
    using qs by blast
qed

theorem strong_completeness\<^sub>P:
  assumes \<open>P; G \<TTurnstile>\<^sub>! p\<close>
    and \<open>\<forall>r \<in> anns p. B r\<close> \<open>\<forall>q \<in> G. \<forall>r \<in> anns q. B r\<close>
    and \<open>\<And>G p. P; G \<TTurnstile>\<star> p \<Longrightarrow> A o lift; G \<turnstile> p\<close>
  shows \<open>A; B; G \<turnstile>\<^sub>! p\<close>
  using strong_completeness\<^sub>P' assms .

theorem main\<^sub>P:
  assumes \<open>\<And>M w p. A p \<Longrightarrow> P M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
    and \<open>\<And>M r. P M \<Longrightarrow> B r \<Longrightarrow> P (M[r!])\<close>
    and \<open>\<forall>r \<in> anns p. B r\<close> \<open>\<forall>q \<in> G. \<forall>r \<in> anns q. B r\<close>
    and \<open>\<And>G p. P; G \<TTurnstile>\<star> p \<Longrightarrow> A o lift; G \<turnstile> p\<close>
  shows \<open>P; G \<TTurnstile>\<^sub>! p \<longleftrightarrow> A; B; G \<turnstile>\<^sub>! p\<close>
  using strong_soundness\<^sub>P[of A P B G p] strong_completeness\<^sub>P[of P G p B A] assms by blast

corollary strong_completeness\<^sub>P\<^sub>B:
  assumes \<open>P; G \<TTurnstile>\<^sub>! p\<close>
    and \<open>\<And>G p. P; G \<TTurnstile>\<star> p \<Longrightarrow> A o lift; G \<turnstile> p\<close>
  shows \<open>A; (\<lambda>_. True); G \<turnstile>\<^sub>! p\<close>
  using strong_completeness\<^sub>P[where B=\<open>\<lambda>_. True\<close>] assms by blast

corollary completeness\<^sub>P':
  assumes \<open>P; {} \<TTurnstile>\<^sub>! p\<close>
    and \<open>\<forall>r \<in> anns p. B r\<close>
    and \<open>\<And>p. P; {} \<TTurnstile> lower p \<Longrightarrow> A o lift \<turnstile> lower p\<close>
  shows \<open>A; B \<turnstile>\<^sub>! p\<close>
  using assms strong_completeness\<^sub>P'[where P=P and G=\<open>{}\<close>] by simp

corollary completeness\<^sub>P:
  assumes \<open>P; {} \<TTurnstile>\<^sub>! p\<close>
    and \<open>\<forall>r \<in> anns p. B r\<close>
    and \<open>\<And>p. P; {} \<TTurnstile> p \<Longrightarrow> A o lift \<turnstile> p\<close>
  shows \<open>A; B \<turnstile>\<^sub>! p\<close>
  using completeness\<^sub>P' assms .

corollary completeness\<^sub>P\<^sub>A:
  assumes \<open>(\<lambda>_. True); {} \<TTurnstile>\<^sub>! p\<close>
  shows \<open>A; (\<lambda>_. True) \<turnstile>\<^sub>! p\<close>
  using assms completeness\<^sub>P[of \<open>\<lambda>_. True\<close> p \<open>\<lambda>_. True\<close>] completeness\<^sub>A by blast

section \<open>System PAL + K\<close>

abbreviation SystemPK (\<open>_ \<turnstile>\<^sub>!\<^sub>K _\<close> [50, 50] 50) where
  \<open>G \<turnstile>\<^sub>!\<^sub>K p \<equiv> (\<lambda>_. False); (\<lambda>_. True); G \<turnstile>\<^sub>! p\<close>

lemma strong_soundness\<^sub>P\<^sub>K: \<open>G \<turnstile>\<^sub>!\<^sub>K p \<Longrightarrow> (\<lambda>_. True); G \<TTurnstile>\<^sub>!\<star> p\<close>
  using strong_soundness\<^sub>P[of \<open>\<lambda>_. False\<close> \<open>\<lambda>_. True\<close>] by fast

abbreviation validPK (\<open>_ \<TTurnstile>\<^sub>!\<^sub>K _\<close> [50, 50] 50) where
  \<open>G \<TTurnstile>\<^sub>!\<^sub>K p \<equiv> (\<lambda>_. True); G \<TTurnstile>\<^sub>! p\<close>

lemma strong_completeness\<^sub>P\<^sub>K:
  assumes \<open>G \<TTurnstile>\<^sub>!\<^sub>K p\<close>
  shows \<open>G \<turnstile>\<^sub>!\<^sub>K p\<close>
  using strong_completeness\<^sub>P\<^sub>B assms strong_completeness\<^sub>K unfolding comp_apply .

theorem main\<^sub>P\<^sub>K: \<open>G \<TTurnstile>\<^sub>!\<^sub>K p \<longleftrightarrow> G \<turnstile>\<^sub>!\<^sub>K p\<close>
  using strong_soundness\<^sub>P\<^sub>K[of G p] strong_completeness\<^sub>P\<^sub>K[of G p] by fast

corollary \<open>G \<TTurnstile>\<^sub>!\<^sub>K p \<Longrightarrow> (\<lambda>_. True); G \<TTurnstile>\<^sub>!\<star> p\<close>
  using strong_soundness\<^sub>P\<^sub>K[of G p] strong_completeness\<^sub>P\<^sub>K[of G p] by fast

section \<open>System PAL + T\<close>

text \<open>Also known as System PAL + M\<close>

inductive AxPT :: \<open>'i pfm \<Rightarrow> bool\<close> where
  \<open>AxPT (K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! p)\<close>

abbreviation SystemPT (\<open>_ \<turnstile>\<^sub>!\<^sub>T _\<close> [50, 50] 50) where
  \<open>G \<turnstile>\<^sub>!\<^sub>T p \<equiv> AxPT; (\<lambda>_. True); G \<turnstile>\<^sub>! p\<close>

lemma soundness_AxPT: \<open>AxPT p \<Longrightarrow> reflexive M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  unfolding reflexive_def by (induct p rule: AxPT.induct) simp

lemma reflexive_restrict: \<open>reflexive M \<Longrightarrow> reflexive (M[r!])\<close>
  unfolding reflexive_def by simp

lemma strong_soundness\<^sub>P\<^sub>T: \<open>G \<turnstile>\<^sub>!\<^sub>T p \<Longrightarrow> reflexive; G \<TTurnstile>\<^sub>!\<star> p\<close>
  using strong_soundness\<^sub>P[of AxPT reflexive \<open>\<lambda>_. True\<close> G p]
    soundness_AxPT reflexive_restrict by fast

lemma AxT_AxPT: \<open>AxT = AxPT o lift\<close>
  unfolding comp_apply using lower_lift
  by (metis AxPT.simps AxT.simps lift.simps(5-6) lower.simps(5-6))

abbreviation validPT (\<open>_ \<TTurnstile>\<^sub>!\<^sub>T _\<close> [50, 50] 50) where
  \<open>G \<TTurnstile>\<^sub>!\<^sub>T p \<equiv> reflexive; G \<TTurnstile>\<^sub>! p\<close>

lemma strong_completeness\<^sub>P\<^sub>T:
  assumes \<open>G \<TTurnstile>\<^sub>!\<^sub>T p\<close>
  shows \<open>G \<turnstile>\<^sub>!\<^sub>T p\<close>
  using strong_completeness\<^sub>P\<^sub>B assms strong_completeness\<^sub>T unfolding AxT_AxPT .

theorem main\<^sub>P\<^sub>T: \<open>G \<TTurnstile>\<^sub>!\<^sub>T p \<longleftrightarrow> G \<turnstile>\<^sub>!\<^sub>T p\<close>
  using strong_soundness\<^sub>P\<^sub>T[of G p] strong_completeness\<^sub>P\<^sub>T[of G p] by fast

corollary \<open>G \<TTurnstile>\<^sub>!\<^sub>T p \<Longrightarrow> reflexive; G \<TTurnstile>\<^sub>!\<star> p\<close>
  using strong_soundness\<^sub>P\<^sub>T[of G p] strong_completeness\<^sub>P\<^sub>T[of G p] by fast

section \<open>System PAL + KB\<close>

inductive AxPB :: \<open>'i pfm \<Rightarrow> bool\<close> where
  \<open>AxPB (p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i (L\<^sub>! i p))\<close>

abbreviation SystemPKB (\<open>_ \<turnstile>\<^sub>!\<^sub>K\<^sub>B _\<close> [50, 50] 50) where
  \<open>G \<turnstile>\<^sub>!\<^sub>K\<^sub>B p \<equiv> AxPB; (\<lambda>_. True); G \<turnstile>\<^sub>! p\<close>

lemma soundness_AxPB: \<open>AxPB p \<Longrightarrow> symmetric M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  unfolding symmetric_def by (induct p rule: AxPB.induct) auto

lemma symmetric_restrict: \<open>symmetric M \<Longrightarrow> symmetric (M[r!])\<close>
  unfolding symmetric_def by simp

lemma strong_soundness\<^sub>P\<^sub>K\<^sub>B: \<open>G \<turnstile>\<^sub>!\<^sub>K\<^sub>B p \<Longrightarrow> symmetric; G \<TTurnstile>\<^sub>!\<star> p\<close>
  using strong_soundness\<^sub>P[of AxPB symmetric \<open>\<lambda>_. True\<close> G p]
    soundness_AxPB symmetric_restrict by fast

lemma AxB_AxPB: \<open>AxB = AxPB o lift\<close>
proof
  fix p :: \<open>'i fm\<close>
  show \<open>AxB p = (AxPB \<circ> lift) p\<close>
    unfolding comp_apply using lower_lift
    by (smt (verit, best) AxB.simps AxPB.simps lift.simps(1, 5-6) lower.simps(5-6))
qed

abbreviation validPKB (\<open>_ \<TTurnstile>\<^sub>!\<^sub>K\<^sub>B _\<close> [50, 50] 50) where
  \<open>G \<TTurnstile>\<^sub>!\<^sub>K\<^sub>B p \<equiv> symmetric; G \<TTurnstile>\<^sub>! p\<close>

lemma strong_completeness\<^sub>P\<^sub>K\<^sub>B:
  assumes \<open>G \<TTurnstile>\<^sub>!\<^sub>K\<^sub>B p\<close>
  shows \<open>G \<turnstile>\<^sub>!\<^sub>K\<^sub>B p\<close>
  using strong_completeness\<^sub>P\<^sub>B assms strong_completeness\<^sub>K\<^sub>B unfolding AxB_AxPB .

theorem main\<^sub>P\<^sub>K\<^sub>B: \<open>G \<TTurnstile>\<^sub>!\<^sub>K\<^sub>B p \<longleftrightarrow> G \<turnstile>\<^sub>!\<^sub>K\<^sub>B p\<close>
  using strong_soundness\<^sub>P\<^sub>K\<^sub>B[of G p] strong_completeness\<^sub>P\<^sub>K\<^sub>B[of G p] by fast

corollary \<open>G \<TTurnstile>\<^sub>!\<^sub>K\<^sub>B p \<Longrightarrow> symmetric; G \<TTurnstile>\<^sub>!\<star> p\<close>
  using strong_soundness\<^sub>P\<^sub>K\<^sub>B[of G p] strong_completeness\<^sub>P\<^sub>K\<^sub>B[of G p] by fast

section \<open>System PAL + K4\<close>

inductive AxP4 :: \<open>'i pfm \<Rightarrow> bool\<close> where
  \<open>AxP4 (K\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i (K\<^sub>! i p))\<close>

abbreviation SystemPK4 (\<open>_ \<turnstile>\<^sub>!\<^sub>K\<^sub>4 _\<close> [50, 50] 50) where
  \<open>G \<turnstile>\<^sub>!\<^sub>K\<^sub>4 p \<equiv> AxP4; (\<lambda>_. True); G \<turnstile>\<^sub>! p\<close>

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

lemma transitive_restrict: \<open>transitive M \<Longrightarrow> transitive (M[r!])\<close>
  unfolding transitive_def by (cases M) (metis (no_types, lifting) frame.select_convs(1-2)
      frame.update_convs(1) mem_Collect_eq restrict.simps)

lemma strong_soundness\<^sub>P\<^sub>K\<^sub>4: \<open>G \<turnstile>\<^sub>!\<^sub>K\<^sub>4 p \<Longrightarrow> transitive; G \<TTurnstile>\<^sub>!\<star> p\<close>
  using strong_soundness\<^sub>P[of AxP4 transitive \<open>\<lambda>_. True\<close> G p]
    soundness_AxP4 transitive_restrict by fast

lemma Ax4_AxP4: \<open>Ax4 = AxP4 o lift\<close>
proof
  fix p :: \<open>'i fm\<close>
  show \<open>Ax4 p = (AxP4 \<circ> lift) p\<close>
    unfolding comp_apply using lower_lift
    by (smt (verit, best) Ax4.simps AxP4.simps lift.simps(1, 5-6) lower.simps(5-6))
qed

abbreviation validPK4 (\<open>_ \<TTurnstile>\<^sub>!\<^sub>K\<^sub>4 _\<close> [50, 50] 50) where
  \<open>G \<TTurnstile>\<^sub>!\<^sub>K\<^sub>4 p \<equiv> transitive; G \<TTurnstile>\<^sub>! p\<close>

lemma strong_completeness\<^sub>P\<^sub>K\<^sub>4:
  assumes \<open>G \<TTurnstile>\<^sub>!\<^sub>K\<^sub>4 p\<close>
  shows \<open>G \<turnstile>\<^sub>!\<^sub>K\<^sub>4 p\<close>
  using strong_completeness\<^sub>P\<^sub>B assms strong_completeness\<^sub>K\<^sub>4 unfolding Ax4_AxP4 .

theorem main\<^sub>P\<^sub>K\<^sub>4: \<open>G \<TTurnstile>\<^sub>!\<^sub>K\<^sub>4 p \<longleftrightarrow> G \<turnstile>\<^sub>!\<^sub>K\<^sub>4 p\<close>
  using strong_soundness\<^sub>P\<^sub>K\<^sub>4[of G p] strong_completeness\<^sub>P\<^sub>K\<^sub>4[of G p] by fast

corollary \<open>G \<TTurnstile>\<^sub>!\<^sub>K\<^sub>4 p \<Longrightarrow> transitive; G \<TTurnstile>\<^sub>!\<star> p\<close>
  using strong_soundness\<^sub>P\<^sub>K\<^sub>4[of G p] strong_completeness\<^sub>P\<^sub>K\<^sub>4[of G p] by fast

section \<open>System PAL + K5\<close>

inductive AxP5 :: \<open>'i pfm \<Rightarrow> bool\<close> where
  \<open>AxP5 (L\<^sub>! i p \<^bold>\<longrightarrow>\<^sub>! K\<^sub>! i (L\<^sub>! i p))\<close>

abbreviation SystemPK5 (\<open>_ \<turnstile>\<^sub>!\<^sub>K\<^sub>5 _\<close> [50, 50] 50) where
  \<open>G \<turnstile>\<^sub>!\<^sub>K\<^sub>5 p \<equiv> AxP5; (\<lambda>_. True); G \<turnstile>\<^sub>! p\<close>

lemma soundness_AxP5: \<open>AxP5 p \<Longrightarrow> Euclidean M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  by (induct p rule: AxP5.induct) (unfold Euclidean_def psemantics.simps, blast)

lemma Euclidean_restrict: \<open>Euclidean M \<Longrightarrow> Euclidean (M[r!])\<close>
  unfolding Euclidean_def by auto

lemma strong_soundness\<^sub>P\<^sub>K\<^sub>5: \<open>G \<turnstile>\<^sub>!\<^sub>K\<^sub>5 p \<Longrightarrow> Euclidean; G \<TTurnstile>\<^sub>!\<star> p\<close>
  using strong_soundness\<^sub>P[of AxP5 Euclidean \<open>\<lambda>_. True\<close> G p]
    soundness_AxP5 Euclidean_restrict by fast

lemma Ax5_AxP5: \<open>Ax5 = AxP5 o lift\<close>
proof
  fix p :: \<open>'i fm\<close>
  show \<open>Ax5 p = (AxP5 \<circ> lift) p\<close>
    unfolding comp_apply using lower_lift
    by (smt (verit, best) Ax5.simps AxP5.simps lift.simps(1, 5-6) lower.simps(5-6))
qed

abbreviation validPK5 (\<open>_ \<TTurnstile>\<^sub>!\<^sub>K\<^sub>5 _\<close> [50, 50] 50) where
  \<open>G \<TTurnstile>\<^sub>!\<^sub>K\<^sub>5 p \<equiv> Euclidean; G \<TTurnstile>\<^sub>! p\<close>

lemma strong_completeness\<^sub>P\<^sub>K\<^sub>5:
  assumes \<open>G \<TTurnstile>\<^sub>!\<^sub>K\<^sub>5 p\<close>
  shows \<open>G \<turnstile>\<^sub>!\<^sub>K\<^sub>5 p\<close>
  using strong_completeness\<^sub>P\<^sub>B assms strong_completeness\<^sub>K\<^sub>5 unfolding Ax5_AxP5 .

theorem main\<^sub>P\<^sub>K\<^sub>5: \<open>G \<TTurnstile>\<^sub>!\<^sub>K\<^sub>5 p \<longleftrightarrow> G \<turnstile>\<^sub>!\<^sub>K\<^sub>5 p\<close>
  using strong_soundness\<^sub>P\<^sub>K\<^sub>5[of G p] strong_completeness\<^sub>P\<^sub>K\<^sub>5[of G p] by fast

corollary \<open>G \<TTurnstile>\<^sub>!\<^sub>K\<^sub>5 p \<Longrightarrow> Euclidean; G \<TTurnstile>\<^sub>!\<star> p\<close>
  using strong_soundness\<^sub>P\<^sub>K\<^sub>5[of G p] strong_completeness\<^sub>P\<^sub>K\<^sub>5[of G p] by fast

section \<open>System PAL + S4\<close>

abbreviation SystemPS4 (\<open>_ \<turnstile>\<^sub>!\<^sub>S\<^sub>4 _\<close> [50, 50] 50) where
  \<open>G \<turnstile>\<^sub>!\<^sub>S\<^sub>4 p \<equiv> AxPT \<oplus> AxP4; (\<lambda>_. True); G \<turnstile>\<^sub>! p\<close>

lemma soundness_AxPT4: \<open>(AxPT \<oplus> AxP4) p \<Longrightarrow> refltrans M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using soundness_AxPT soundness_AxP4 by fast

lemma refltrans_restrict: \<open>refltrans M \<Longrightarrow> refltrans (M[r!])\<close>
  using reflexive_restrict transitive_restrict by blast

lemma strong_soundness\<^sub>P\<^sub>S\<^sub>4: \<open>G \<turnstile>\<^sub>!\<^sub>S\<^sub>4 p \<Longrightarrow> refltrans; G \<TTurnstile>\<^sub>!\<star> p\<close>
  using strong_soundness\<^sub>P[of \<open>AxPT \<oplus> AxP4\<close> refltrans \<open>\<lambda>_. True\<close> G p]
    soundness_AxPT4 refltrans_restrict by fast

lemma AxT4_AxPT4: \<open>(AxT \<oplus> Ax4) = (AxPT \<oplus> AxP4) o lift\<close>
  using AxT_AxPT Ax4_AxP4 unfolding comp_apply by metis

abbreviation validPS4 (\<open>_ \<TTurnstile>\<^sub>!\<^sub>S\<^sub>4 _\<close> [50, 50] 50) where
  \<open>G \<TTurnstile>\<^sub>!\<^sub>S\<^sub>4 p \<equiv> refltrans; G \<TTurnstile>\<^sub>! p\<close>

theorem strong_completeness\<^sub>P\<^sub>S\<^sub>4:
  assumes \<open>G \<TTurnstile>\<^sub>!\<^sub>S\<^sub>4 p\<close>
  shows \<open>G \<turnstile>\<^sub>!\<^sub>S\<^sub>4 p\<close>
  using strong_completeness\<^sub>P\<^sub>B assms strong_completeness\<^sub>S\<^sub>4 unfolding AxT4_AxPT4 .

theorem main\<^sub>P\<^sub>S\<^sub>4: \<open>G \<TTurnstile>\<^sub>!\<^sub>S\<^sub>4 p \<longleftrightarrow> G \<turnstile>\<^sub>!\<^sub>S\<^sub>4 p\<close>
  using strong_soundness\<^sub>P\<^sub>S\<^sub>4[of G p] strong_completeness\<^sub>P\<^sub>S\<^sub>4[of G p] by fast

corollary \<open>G \<TTurnstile>\<^sub>!\<^sub>S\<^sub>4 p \<Longrightarrow> refltrans; G \<TTurnstile>\<^sub>!\<star> p\<close>
  using strong_soundness\<^sub>P\<^sub>S\<^sub>4[of G p] strong_completeness\<^sub>P\<^sub>S\<^sub>4[of G p] by fast

section \<open>System PAL + S5\<close>

abbreviation SystemPS5 (\<open>_ \<turnstile>\<^sub>!\<^sub>S\<^sub>5 _\<close> [50, 50] 50) where
  \<open>G \<turnstile>\<^sub>!\<^sub>S\<^sub>5 p \<equiv> AxPT \<oplus> AxPB \<oplus> AxP4; (\<lambda>_. True); G \<turnstile>\<^sub>! p\<close>

abbreviation AxPTB4 :: \<open>'i pfm \<Rightarrow> bool\<close> where
  \<open>AxPTB4 \<equiv> AxPT \<oplus> AxPB \<oplus> AxP4\<close>

lemma soundness_AxPTB4: \<open>AxPTB4 p \<Longrightarrow> equivalence M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using soundness_AxPT soundness_AxPB soundness_AxP4 by fast

lemma equivalence_restrict: \<open>equivalence M \<Longrightarrow> equivalence (M[r!])\<close>
  using reflexive_restrict symmetric_restrict transitive_restrict by blast

lemma strong_soundness\<^sub>P\<^sub>S\<^sub>5: \<open>G \<turnstile>\<^sub>!\<^sub>S\<^sub>5 p \<Longrightarrow> equivalence; G \<TTurnstile>\<^sub>!\<star> p\<close>
  using strong_soundness\<^sub>P[of AxPTB4 equivalence \<open>\<lambda>_. True\<close> G p]
    soundness_AxPTB4 equivalence_restrict by fast

lemma AxTB4_AxPTB4: \<open>AxTB4 = AxPTB4 o lift\<close>
  using AxT_AxPT AxB_AxPB Ax4_AxP4 unfolding comp_apply by metis

abbreviation validPS5 (\<open>_ \<TTurnstile>\<^sub>!\<^sub>S\<^sub>5 _\<close> [50, 50] 50) where
  \<open>G \<TTurnstile>\<^sub>!\<^sub>S\<^sub>5 p \<equiv> equivalence; G \<TTurnstile>\<^sub>! p\<close>

theorem strong_completeness\<^sub>P\<^sub>S\<^sub>5:
  assumes \<open>G \<TTurnstile>\<^sub>!\<^sub>S\<^sub>5 p\<close>
  shows \<open>G \<turnstile>\<^sub>!\<^sub>S\<^sub>5 p\<close>
  using strong_completeness\<^sub>P\<^sub>B assms strong_completeness\<^sub>S\<^sub>5 unfolding AxTB4_AxPTB4 .

theorem main\<^sub>P\<^sub>S\<^sub>5: \<open>G \<TTurnstile>\<^sub>!\<^sub>S\<^sub>5 p \<longleftrightarrow> G \<turnstile>\<^sub>!\<^sub>S\<^sub>5 p\<close>
  using strong_soundness\<^sub>P\<^sub>S\<^sub>5[of G p] strong_completeness\<^sub>P\<^sub>S\<^sub>5[of G p] by fast

corollary \<open>G \<TTurnstile>\<^sub>!\<^sub>S\<^sub>5 p \<Longrightarrow> equivalence; G \<TTurnstile>\<^sub>!\<star> p\<close>
  using strong_soundness\<^sub>P\<^sub>S\<^sub>5[of G p] strong_completeness\<^sub>P\<^sub>S\<^sub>5[of G p] by fast

section \<open>System PAL + S5'\<close>

abbreviation SystemPS5' (\<open>_ \<turnstile>\<^sub>!\<^sub>S\<^sub>5'' _\<close> [50, 50] 50) where
  \<open>G \<turnstile>\<^sub>!\<^sub>S\<^sub>5' p \<equiv> AxPT \<oplus> AxP5; (\<lambda>_. True); G \<turnstile>\<^sub>! p\<close>

abbreviation AxPT5 :: \<open>'i pfm \<Rightarrow> bool\<close> where
  \<open>AxPT5 \<equiv> AxPT \<oplus> AxP5\<close>

lemma soundness_AxPT5: \<open>AxPT5 p \<Longrightarrow> equivalence M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile>\<^sub>! p\<close>
  using soundness_AxPT soundness_AxPT soundness_AxP5 symm_trans_Euclid by fast

lemma strong_soundness\<^sub>P\<^sub>S\<^sub>5': \<open>G \<turnstile>\<^sub>!\<^sub>S\<^sub>5' p \<Longrightarrow> equivalence; G \<TTurnstile>\<^sub>!\<star> p\<close>
  using strong_soundness\<^sub>P[of AxPT5 equivalence \<open>\<lambda>_. True\<close> G p]
    soundness_AxPT5 equivalence_restrict by fast

lemma AxT5_AxPT5: \<open>AxT5 = AxPT5 o lift\<close>
  using AxT_AxPT Ax5_AxP5 unfolding comp_apply by metis

theorem strong_completeness\<^sub>P\<^sub>S\<^sub>5':
  assumes \<open>G \<TTurnstile>\<^sub>!\<^sub>S\<^sub>5 p\<close>
  shows \<open>G \<turnstile>\<^sub>!\<^sub>S\<^sub>5' p\<close>
  using strong_completeness\<^sub>P\<^sub>B assms strong_completeness\<^sub>S\<^sub>5' unfolding AxT5_AxPT5 .

theorem main\<^sub>P\<^sub>S\<^sub>5': \<open>G \<TTurnstile>\<^sub>!\<^sub>S\<^sub>5 p \<longleftrightarrow> G \<turnstile>\<^sub>!\<^sub>S\<^sub>5' p\<close>
  using strong_soundness\<^sub>P\<^sub>S\<^sub>5'[of G p] strong_completeness\<^sub>P\<^sub>S\<^sub>5'[of G p] by fast

end
