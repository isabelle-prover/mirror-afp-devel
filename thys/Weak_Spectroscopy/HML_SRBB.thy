(* License: LGPL *)

section \<open>Hennessy--Milner Logic for Stability-Respecting Branching Bisimilarity\<close>

theory HML_SRBB
  imports LTS_Semantics
begin

text \<open>
  This section describes a variant of Hennessy--Milner logic that characterizes stability-respecting branching bisimilarity (SRBB).
\<close>

text \<open>The following mutually-recursive datatype family describes a grammar of \<open>HML_SRBB\<close> formulas.\<close>

datatype
  ('act, 'i) hml_srbb =
    TT |
    Internal \<open>('act, 'i) hml_srbb_inner\<close> |
    ImmConj \<open>'i set\<close> \<open>'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct\<close>
and
  ('act, 'i) hml_srbb_inner =
    Obs 'act \<open>('act, 'i) hml_srbb\<close> |
    Conj \<open>'i set\<close> \<open>'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct\<close> |
    StableConj \<open>'i set\<close> \<open>'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct\<close> |
    BranchConj 'act \<open>('act, 'i) hml_srbb\<close>
               \<open>'i set\<close> \<open>'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct\<close>
and
  ('act, 'i) hml_srbb_conjunct =
    Pos \<open>('act, 'i) hml_srbb_inner\<close> |
    Neg \<open>('act, 'i) hml_srbb_inner\<close>

text \<open>
  The constructors correspond to more conventional notation of HML as follows:

  \<^item> \<^type>\<open>hml_srbb\<close> (members usually referred to as \<open>\<phi>\<close>):
    \<^item> \<^term>\<open>TT\<close> encodes \<open>\<top>\<close>
    \<^item> \<^term>\<open>(Internal \<chi>)\<close> encodes \<open>\<langle>\<epsilon>\<rangle>\<chi>\<close>
    \<^item> \<^term>\<open>(ImmConj I \<psi>s)\<close> encodes $\bigwedge\nolimits_{i \in \mathrm{\texttt{I}}} {\psi s}(i)$
  \<^item> \<^type>\<open>hml_srbb_inner\<close> (usually \<open>\<chi>\<close>):
    \<^item> \<^term>\<open>(Obs \<alpha> \<phi>)\<close> encodes \<open>(\<alpha>)\<phi>\<close>
    \<^item> \<^term>\<open>(Conj I \<psi>s)\<close> encodes $\bigwedge\nolimits_{i \in \mathrm{\texttt{I}}} {\psi s}(i)$
    \<^item> \<^term>\<open>(StableConj I \<psi>s)\<close> encodes $\neg\langle\tau\rangle\top \land \bigwedge\nolimits_{i \in \mathrm{\texttt{I}}} {\psi s}(i)$
    \<^item> \<^term>\<open>(BranchConj \<alpha> \<phi> I \<psi>s)\<close> encodes $(\alpha)\varphi \land \bigwedge\nolimits_{i \in \mathrm{\texttt{I}}} {\psi s}(i)$
  \<^item> \<^type>\<open>hml_srbb_conjunct\<close> (usually \<open>\<psi>\<close>):
    \<^item> \<^term>\<open>(Pos \<chi>)\<close> encodes \<open>\<langle>\<epsilon>\<rangle>\<chi>\<close>
    \<^item> \<^term>\<open>(Neg \<chi>)\<close> encodes \<open>\<not>\<langle>\<epsilon>\<rangle>\<chi>\<close>
\<close>

subsection \<open>Semantics of HML$_\text{SRBB}$ Formulas\<close>

text \<open>
  This section describes how semantic meaning is assigned to HML$_\text{SRBB}$ formulas in the context of a LTS.
  We define what it means for a process \<open>p\<close> to satisfy an HML$_\text{SRBB}$ formula \<open>\<phi>\<close>, written as \<open>p \<Turnstile>SRBB \<phi>\<close>.
\<close>

context lts_tau
begin

primrec
      hml_srbb_models :: \<open>'s \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool\<close> (infixl \<open>\<Turnstile>SRBB\<close> 60)
  and hml_srbb_inner_models :: \<open>'s \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool\<close>
  and hml_srbb_conjunct_models :: \<open>'s \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool\<close> where
  \<open>hml_srbb_models state TT =
    True\<close> |
  \<open>hml_srbb_models state (Internal \<chi>) =
    (\<exists>p'. state \<Zsurj> p' \<and> (hml_srbb_inner_models p' \<chi>))\<close> |
  \<open>hml_srbb_models state (ImmConj I \<psi>s) =
    (\<forall>i\<in>I. hml_srbb_conjunct_models state (\<psi>s i))\<close> |

  \<open>hml_srbb_inner_models state (Obs a \<phi>) =
    ((\<exists>p'. state \<mapsto> a p' \<and> hml_srbb_models p' \<phi>) \<or> a = \<tau> \<and> hml_srbb_models state \<phi>)\<close> |
  \<open>hml_srbb_inner_models state (Conj I \<psi>s) =
    (\<forall>i\<in>I. hml_srbb_conjunct_models state (\<psi>s i))\<close> |
  \<open>hml_srbb_inner_models state (StableConj I \<psi>s) =
    ((\<nexists>p'. state \<mapsto> \<tau> p') \<and> (\<forall>i\<in>I. hml_srbb_conjunct_models state (\<psi>s i)))\<close> |
  \<open>hml_srbb_inner_models state (BranchConj a \<phi> I \<psi>s) =
    (((\<exists>p'. state \<mapsto> a p' \<and> hml_srbb_models p' \<phi>) \<or> a = \<tau> \<and> hml_srbb_models state \<phi>)
    \<and> (\<forall>i\<in>I. hml_srbb_conjunct_models state (\<psi>s i)))\<close> |

  \<open>hml_srbb_conjunct_models state (Pos \<chi>) =
    (\<exists>p'. state \<Zsurj> p' \<and> hml_srbb_inner_models p' \<chi>)\<close> |
  \<open>hml_srbb_conjunct_models state (Neg \<chi>) =
    (\<nexists>p'. state \<Zsurj> p' \<and> hml_srbb_inner_models p' \<chi>)\<close>

sublocale lts_semantics \<open>step\<close> \<open>hml_srbb_models\<close> .
sublocale hml_srbb_inner: lts_semantics where models = hml_srbb_inner_models .
sublocale hml_srbb_conj: lts_semantics where models = hml_srbb_conjunct_models .

subsection \<open>Distinguishing Formulas\<close>

lemma verum_never_distinguishes:
  \<open>\<not> distinguishes TT p q\<close>
  by simp

text \<open>
  If $\bigwedge\nolimits_{i \in I} {\psi s}(i)$ distinguishes \<open>p\<close> from \<open>q\<close>, then there must be at least one conjunct in this conjunction that distinguishes \<open>p\<close> from \<open>q\<close>.
\<close>
lemma srbb_dist_imm_conjunction_implies_dist_conjunct:
  assumes \<open>distinguishes (ImmConj I \<psi>s) p q\<close>
  shows \<open>\<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
  using assms by auto

lemma srbb_dist_conjunction_implies_dist_conjunct:
  assumes \<open>hml_srbb_inner.distinguishes (Conj I \<psi>s) p q\<close>
  shows \<open>\<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
  using assms by auto

lemma srbb_dist_branch_conjunction_implies_dist_conjunct_or_branch:
  assumes
    \<open>hml_srbb_inner.distinguishes (BranchConj \<alpha> \<phi> I \<psi>s) p q\<close>
  shows
    \<open>(\<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q)
       \<or> hml_srbb_inner.distinguishes (Obs \<alpha> \<phi>) p q\<close>
  using assms by force

lemma srbb_dist_conjunct_implies_dist_imm_conjunction:
  assumes
    \<open>i\<in>I\<close>
    \<open>hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
    \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<psi>s i)\<close>
  shows
    \<open>distinguishes (ImmConj I \<psi>s) p q\<close>
  using assms by auto

lemma srbb_dist_conjunct_implies_dist_conjunction:
  assumes
    \<open>i\<in>I\<close>
    \<open>hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
    \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<psi>s i)\<close>
  shows
    \<open>hml_srbb_inner.distinguishes (Conj I \<psi>s) p q\<close>
  using assms by auto

lemma srbb_dist_conjunct_or_branch_implies_dist_branch_conjunction:
  assumes
    \<open>\<forall>i \<in> I. hml_srbb_conjunct_models p (\<psi>s i)\<close>
    \<open>hml_srbb_inner_models p (Obs \<alpha> \<phi>)\<close>
    \<open>(i\<in>I \<and> hml_srbb_conj.distinguishes (\<psi>s i) p q)
         \<or> (hml_srbb_inner.distinguishes (Obs \<alpha> \<phi>) p q)\<close>
  shows
    \<open>hml_srbb_inner.distinguishes (BranchConj \<alpha> \<phi> I \<psi>s) p q\<close>
  using assms by force

subsection \<open>HML$_\text{SRBB}$ Implication and Equivalence\<close>

abbreviation hml_srbb_impl
  :: \<open>('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool\<close>  (infixr \<open>\<Rrightarrow>\<close> 70)
where
  \<open>hml_srbb_impl \<equiv> entails\<close>

abbreviation
  hml_srbb_impl_inner
  :: \<open>('a, 's) hml_srbb_inner \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool\<close>
  (infix \<open>\<chi>\<Rrightarrow>\<close> 70)
where
  \<open>(\<chi>\<Rrightarrow>) \<equiv> hml_srbb_inner.entails\<close>

abbreviation
  hml_srbb_impl_conjunct
  :: \<open>('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool\<close>
  (infix \<open>\<psi>\<Rrightarrow>\<close> 70)
where
  \<open>(\<psi>\<Rrightarrow>) \<equiv> hml_srbb_conj.entails\<close>

abbreviation
  hml_srbb_eq
  :: \<open>('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool\<close>
  (infix \<open>\<Lleftarrow>srbb\<Rrightarrow>\<close> 70)
where
  \<open>(\<Lleftarrow>srbb\<Rrightarrow>) \<equiv> logical_eq\<close>

abbreviation
  hml_srbb_eq_inner
  :: \<open>('a, 's) hml_srbb_inner \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool\<close>
  (infix \<open>\<Lleftarrow>\<chi>\<Rrightarrow>\<close> 70)
where
  \<open>(\<Lleftarrow>\<chi>\<Rrightarrow>) \<equiv> hml_srbb_inner.logical_eq\<close>

abbreviation
  hml_srbb_eq_conjunct
  :: \<open>('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool\<close>
  (infix \<open>\<Lleftarrow>\<psi>\<Rrightarrow>\<close> 70)
  where
  \<open>(\<Lleftarrow>\<psi>\<Rrightarrow>) \<equiv> hml_srbb_conj.logical_eq\<close>

subsection \<open>Substitution and Congruence\<close>

lemma srbb_internal_subst:
  assumes
    \<open>\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r\<close>
    \<open>\<phi> \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>l)\<close>
  shows
    \<open>\<phi> \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>r)\<close>
  using assms by force

lemma internal_srbb_cong:
  assumes \<open>\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r\<close>
  shows \<open>(Internal \<chi>l) \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>r)\<close>
  using assms by auto


lemma immconj_cong:
  assumes
    \<open>\<psi>sl ` I = \<psi>sr ` I\<close>
    \<open>\<psi>sl s \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>sr s\<close>
  shows
    \<open>ImmConj (I \<union> {s}) \<psi>sl \<Lleftarrow>srbb\<Rrightarrow> ImmConj (I \<union> {s}) \<psi>sr\<close>
  using assms
  by (auto) (metis (mono_tags, lifting) image_iff)+

lemma obs_srbb_cong:
  assumes \<open>\<phi>l \<Lleftarrow>srbb\<Rrightarrow> \<phi>r\<close>
  shows \<open>(Obs \<alpha> \<phi>l) \<Lleftarrow>\<chi>\<Rrightarrow> (Obs \<alpha> \<phi>r)\<close>
  using assms by auto

subsection \<open>Trivial and Equivalent Formulas\<close>

lemma empty_conj_trivial[simp]:
  \<open>state \<Turnstile>SRBB ImmConj {} \<psi>s\<close>
  \<open>hml_srbb_inner_models state (Conj {} \<psi>s)\<close>
  \<open>hml_srbb_inner_models state (Obs \<tau> TT)\<close>
  by simp+

lemma empty_branch_conj_tau:
  \<open>hml_srbb_inner_models state (BranchConj \<tau> TT {} \<psi>s)\<close>
  by auto

lemma stable_conj_parts:
  assumes
    \<open>hml_srbb_inner_models p (StableConj I \<Psi>)\<close>
    \<open>i \<in> I\<close>
  shows
    \<open>hml_srbb_conjunct_models p (\<Psi> i)\<close>
  using assms by auto

lemma branching_conj_parts:
  assumes
    \<open>hml_srbb_inner_models p (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
    \<open>i \<in> I\<close>
  shows
    \<open>hml_srbb_conjunct_models p (\<Psi> i)\<close>
  using assms by auto

lemma branching_conj_obs:
  assumes \<open>hml_srbb_inner_models p (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
  shows \<open>hml_srbb_inner_models p (Obs \<alpha> \<phi>)\<close>
  using assms by auto

lemma srbb_obs_\<tau>_is_\<chi>TT: \<open>Obs \<tau> TT \<Lleftarrow>\<chi>\<Rrightarrow> Conj {} \<psi>s\<close>
  by simp

lemma srbb_obs_is_empty_branch_conj: \<open>Obs \<alpha> \<phi> \<Lleftarrow>\<chi>\<Rrightarrow> BranchConj \<alpha> \<phi> {} \<psi>s\<close>
  by auto

lemma srbb_TT_is_\<chi>TT: \<open>TT \<Lleftarrow>srbb\<Rrightarrow> Internal (Conj {} \<psi>s)\<close>
  using lts_tau.refl by force

lemma srbb_TT_is_empty_conj: \<open>TT \<Lleftarrow>srbb\<Rrightarrow> ImmConj {} \<psi>s\<close>
  by simp

text \<open>Positive conjuncts in stable conjunctions can be replaced by negative ones.\<close>
lemma srbb_stable_Neg_normalizable:
  assumes
    \<open>i \<in> I\<close> \<open>\<Psi> i = Pos \<chi>\<close>
    \<open>\<Psi>' = \<Psi>(i:= Neg (StableConj {left} (\<lambda>_. Neg \<chi>)))\<close>
  shows
    \<open>Internal (StableConj I \<Psi>) \<Lleftarrow>srbb\<Rrightarrow> Internal (StableConj I \<Psi>')\<close>
proof (rule logical_eqI)
  fix p
  assume \<open>p \<Turnstile>SRBB Internal (StableConj I \<Psi>)\<close>
  then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' (StableConj I \<Psi>)\<close> by auto
  hence \<open>stable_state p'\<close> by auto
  from p'_spec have \<open>\<exists>p''. p' \<Zsurj> p'' \<and> hml_srbb_inner_models p'' \<chi>\<close>
    using assms(1,2) by auto
  with \<open>stable_state p'\<close> have \<open>hml_srbb_inner_models p' \<chi>\<close>
    using stable_state_stable by blast
  hence \<open>hml_srbb_conjunct_models p' (Neg (StableConj {left} (\<lambda>_. Neg \<chi>)))\<close>
    using \<open>stable_state p'\<close> stable_state_stable by (auto, blast)
  hence \<open>hml_srbb_inner_models p' (StableConj I \<Psi>')\<close>
    unfolding assms(3) using p'_spec by auto
  thus \<open>p \<Turnstile>SRBB hml_srbb.Internal (StableConj I \<Psi>')\<close>
    using \<open>p \<Zsurj> p'\<close> by auto
next
  fix p
  assume \<open>p \<Turnstile>SRBB Internal (StableConj I \<Psi>')\<close>
  then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' (StableConj I \<Psi>')\<close> by auto
  hence \<open>stable_state p'\<close> by auto
  from p'_spec(2) have other_conjuncts: \<open>\<forall>j\<in>I. i \<noteq> j \<longrightarrow> hml_srbb_conjunct_models p' (\<Psi> j)\<close>
    using assms stable_conj_parts fun_upd_apply by metis
  from p'_spec(2) have \<open>hml_srbb_conjunct_models p' (\<Psi>' i)\<close>
    using assms(1) stable_conj_parts by blast
  hence \<open>hml_srbb_conjunct_models p' (Neg (StableConj {left} (\<lambda>_. Neg \<chi>)))\<close>
    unfolding assms(3) by auto
  with \<open>stable_state p'\<close> have \<open>hml_srbb_inner_models p' \<chi>\<close>
    using stable_state_stable by (auto, metis silent_reachable.simps)
  then have \<open>hml_srbb_conjunct_models p' (Pos \<chi>)\<close>
    using lts_tau.refl by fastforce
  hence \<open>hml_srbb_inner_models p' (StableConj I \<Psi>)\<close>
    using p'_spec assms other_conjuncts by auto
  thus \<open>p \<Turnstile>SRBB hml_srbb.Internal (StableConj I \<Psi>)\<close>
    using p'_spec(1) by auto
qed

text \<open>All positive conjuncts in stable conjunctions can be replaced by negative ones at once.\<close>
lemma srbb_stable_Neg_normalizable_set:
  assumes
    \<open>\<Psi>' = (\<lambda>i. case (\<Psi> i) of
      Pos \<chi> \<Rightarrow> Neg (StableConj {left} (\<lambda>_. Neg \<chi>)) |
      Neg \<chi> \<Rightarrow> Neg \<chi>)\<close>
  shows
    \<open>Internal (StableConj I \<Psi>) \<Lleftarrow>srbb\<Rrightarrow> Internal (StableConj I \<Psi>')\<close>
proof (rule logical_eqI)
  fix p
  assume \<open>p \<Turnstile>SRBB Internal (StableConj I \<Psi>)\<close>
  then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' (StableConj I \<Psi>)\<close> by auto
  hence \<open>stable_state p'\<close> by auto
  from p'_spec have
    \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow> (\<exists>p''. p' \<Zsurj> p'' \<and> hml_srbb_inner_models p'' \<chi>)\<close>
    by fastforce
  with \<open>stable_state p'\<close> have \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow> hml_srbb_inner_models p' \<chi>\<close>
    using stable_state_stable by blast
  hence pos_rewrite: \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow>
      hml_srbb_conjunct_models p' (Neg (StableConj {left} (\<lambda>_. Neg \<chi>)))\<close>
    using \<open>stable_state p'\<close> stable_state_stable by (auto, blast)
  hence \<open>hml_srbb_inner_models p' (StableConj I \<Psi>')\<close>
    unfolding assms using p'_spec
    by (auto, metis (no_types, lifting) hml_srbb_conjunct.exhaust hml_srbb_conjunct.simps(5,6)
        pos_rewrite)
  thus \<open>p \<Turnstile>SRBB Internal (StableConj I \<Psi>')\<close>
    using \<open>p \<Zsurj> p'\<close> by auto
next
  fix p
  assume \<open>p \<Turnstile>SRBB Internal (StableConj I \<Psi>')\<close>
  then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' (StableConj I \<Psi>')\<close> by auto
  hence \<open>stable_state p'\<close> by auto
  from p'_spec(2) have other_conjuncts:
      \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Neg \<chi> \<longrightarrow> hml_srbb_conjunct_models p' (\<Psi> i)\<close>
    using assms stable_conj_parts by (metis hml_srbb_conjunct.simps(6))
  from p'_spec(2) have \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow> hml_srbb_conjunct_models p' (\<Psi>' i)\<close>
    using assms(1) stable_conj_parts by blast
  hence \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow>
      hml_srbb_conjunct_models p' (Neg (StableConj {left} (\<lambda>_. Neg \<chi>)))\<close>
    unfolding assms by auto
  with \<open>stable_state p'\<close> have \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow> hml_srbb_inner_models p' \<chi>\<close>
    using stable_state_stable by (auto, metis silent_reachable.simps)
  then have pos_conjuncts:
      \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow>hml_srbb_conjunct_models p' (Pos \<chi>)\<close>
    using hml_srbb_conjunct_models.simps(1) silent_reachable.simps by blast
  hence \<open>hml_srbb_inner_models p' (StableConj I \<Psi>)\<close>
    using p'_spec assms other_conjuncts
    by (auto, metis other_conjuncts pos_conjuncts hml_srbb_conjunct.exhaust)
  thus \<open>p \<Turnstile>SRBB Internal (StableConj I \<Psi>)\<close>
    using p'_spec(1) by auto
qed

definition conjunctify_distinctions ::
  \<open>('s \<Rightarrow> ('a, 's) hml_srbb) \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> ('a, 's) hml_srbb_conjunct)\<close> where
  \<open>conjunctify_distinctions \<Phi> p \<equiv> \<lambda>q.
    case (\<Phi> q) of
      TT \<Rightarrow> undefined
    | Internal \<chi> \<Rightarrow> Pos \<chi>
    | ImmConj I \<Psi> \<Rightarrow> \<Psi> (SOME i. i\<in>I \<and> hml_srbb_conj.distinguishes (\<Psi> i) p q)\<close>

lemma distinction_conjunctification:
  assumes
    \<open>\<forall>q\<in>I. distinguishes (\<Phi> q) p q\<close>
  shows
    \<open>\<forall>q\<in>I. hml_srbb_conj.distinguishes ((conjunctify_distinctions \<Phi> p) q) p q\<close>
  unfolding conjunctify_distinctions_def
proof
  fix q
  assume q_I: \<open>q\<in>I\<close>
  show \<open>hml_srbb_conj.distinguishes
          (case \<Phi> q of hml_srbb.Internal x \<Rightarrow> hml_srbb_conjunct.Pos x
           | ImmConj I \<Psi> \<Rightarrow> \<Psi> (SOME i. i \<in> I \<and> hml_srbb_conj.distinguishes (\<Psi> i) p q))
          p q\<close>
  proof (cases \<open>\<Phi> q\<close>)
    case TT
    then show ?thesis using assms q_I by fastforce
  next
    case (Internal \<chi>)
    then show ?thesis using assms q_I by auto
  next
    case (ImmConj J \<Psi>)
    then have \<open>\<exists>i \<in> J. hml_srbb_conj.distinguishes (\<Psi> i) p q\<close>
      using assms q_I by auto
    then show ?thesis
      by (metis (mono_tags, lifting) ImmConj hml_srbb.simps(11) someI)
  qed
qed

lemma distinction_combination:
  fixes p q
  defines
    \<open>Q\<alpha> \<equiv> {q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. distinguishes \<phi> p q')}\<close>
  assumes
    \<open>p \<mapsto>a \<alpha> p'\<close>
    \<open>\<forall>q'\<in> Q\<alpha>.
      \<forall>q''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> (distinguishes (\<Phi> q'') p' q'')\<close>
  shows
    \<open>\<forall>q'\<in>Q\<alpha>.
      hml_srbb_inner.distinguishes (Obs \<alpha> (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''}
                                                   (conjunctify_distinctions \<Phi> p'))) p q'\<close>
proof -
  have \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q''\<in>{q''. q' \<mapsto>a \<alpha> q''}.
      hml_srbb_conj.distinguishes ((conjunctify_distinctions \<Phi> p') q'') p' q''\<close>
  proof clarify
    fix q' q''
    assume \<open>q' \<in> Q\<alpha>\<close> \<open>q' \<mapsto>a \<alpha> q''\<close>
    thus \<open>hml_srbb_conj.distinguishes (conjunctify_distinctions \<Phi> p' q'') p' q''\<close>
      using distinction_conjunctification assms(3)
      by (metis mem_Collect_eq)
  qed
  hence \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q''\<in>{q''. \<exists>q1'\<in>Q\<alpha>. q1' \<mapsto>a \<alpha> q''}.
      hml_srbb_conj.distinguishes ((conjunctify_distinctions \<Phi> p') q'') p' q''\<close> by blast
  hence \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q''. q' \<mapsto>a \<alpha> q''
    \<longrightarrow> distinguishes (ImmConj {q''. \<exists>q1'\<in>Q\<alpha>. q1' \<mapsto>a \<alpha> q''}
                               (conjunctify_distinctions \<Phi> p')) p' q''\<close> by auto
  thus \<open>\<forall>q'\<in>Q\<alpha>.
      hml_srbb_inner.distinguishes (Obs \<alpha> (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''}
                                                   (conjunctify_distinctions \<Phi> p'))) p q'\<close>
    by (auto) (metis assms(2))+
qed

definition conjunctify_distinctions_dual ::
  \<open>('s \<Rightarrow> ('a, 's) hml_srbb) \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> ('a, 's) hml_srbb_conjunct)\<close> where
  \<open>conjunctify_distinctions_dual \<Phi> p \<equiv> \<lambda>q.
    case (\<Phi> q) of
      TT \<Rightarrow> undefined
    | Internal \<chi> \<Rightarrow> Neg \<chi>
    | ImmConj I \<Psi> \<Rightarrow>
      (case \<Psi> (SOME i. i\<in>I \<and> hml_srbb_conj.distinguishes (\<Psi> i) q p) of
        Pos \<chi> \<Rightarrow> Neg \<chi> | Neg \<chi> \<Rightarrow> Pos \<chi>)\<close>

lemma dual_conjunct:
  assumes
    \<open>hml_srbb_conj.distinguishes \<psi> p q\<close>
  shows
    \<open>hml_srbb_conj.distinguishes (case \<psi> of
               hml_srbb_conjunct.Pos \<chi> \<Rightarrow> hml_srbb_conjunct.Neg \<chi>
               | hml_srbb_conjunct.Neg \<chi> \<Rightarrow> hml_srbb_conjunct.Pos \<chi>) q p\<close>
  using assms
  by (cases \<psi>, auto)

lemma distinction_conjunctification_dual:
  assumes
    \<open>\<forall>q\<in>I. distinguishes (\<Phi> q) q p\<close>
  shows
    \<open>\<forall>q\<in>I. hml_srbb_conj.distinguishes (conjunctify_distinctions_dual \<Phi> p q) p q\<close>
  unfolding conjunctify_distinctions_dual_def
proof
  fix q
  assume q_I: \<open>q\<in>I\<close>
  show \<open>hml_srbb_conj.distinguishes
          (case \<Phi> q of hml_srbb.Internal x \<Rightarrow> hml_srbb_conjunct.Neg x
           | ImmConj I \<Psi> \<Rightarrow>
               ( case \<Psi> (SOME i. i \<in> I \<and> hml_srbb_conj.distinguishes (\<Psi> i) q p) of
                  hml_srbb_conjunct.Pos x \<Rightarrow> hml_srbb_conjunct.Neg x
               | hml_srbb_conjunct.Neg x \<Rightarrow> hml_srbb_conjunct.Pos x))
          p q\<close>
  proof (cases \<open>\<Phi> q\<close>)
    case TT
    then show ?thesis using assms q_I by fastforce
  next
    case (Internal \<chi>)
    then show ?thesis using assms q_I by auto
  next
    case (ImmConj J \<Psi>)
    then have \<open>\<exists>i \<in> J. hml_srbb_conj.distinguishes (\<Psi> i) q p\<close>
      using assms q_I by auto
    hence \<open>hml_srbb_conj.distinguishes (case \<Psi>
      (SOME i. i \<in> J \<and> hml_srbb_conj.distinguishes (\<Psi> i) q p) of
               hml_srbb_conjunct.Pos x \<Rightarrow> hml_srbb_conjunct.Neg x
               | hml_srbb_conjunct.Neg x \<Rightarrow> hml_srbb_conjunct.Pos x) p q\<close>
      by (metis (no_types, lifting) dual_conjunct someI_ex)
    then show ?thesis unfolding ImmConj by auto
  qed
qed

lemma distinction_conjunctification_two_way:
  fixes \<Phi> p I
  defines
    \<open>conjfy q \<equiv>
      (if distinguishes (\<Phi> q) p q
      then conjunctify_distinctions \<Phi>
      else conjunctify_distinctions_dual \<Phi>) p q\<close>
  assumes
    \<open>\<forall>q\<in>I. distinguishes (\<Phi> q) p q \<or> distinguishes (\<Phi> q) q p\<close>
  shows
    \<open>\<forall>q\<in>I. hml_srbb_conj.distinguishes (conjfy q) p q\<close>
proof safe
  fix q
  assume \<open>q \<in> I\<close>
  then consider \<open>distinguishes (\<Phi> q) p q\<close>
    | \<open>distinguishes (\<Phi> q) q p\<close> using assms by blast
  thus \<open>hml_srbb_conj.distinguishes (conjfy q) p q\<close>
  proof cases
    case 1
    then show ?thesis using distinction_conjunctification conjfy_def
      by (smt (verit) singleton_iff)
  next
    case 2
    then show ?thesis using distinction_conjunctification_dual singleton_iff
      unfolding distinguishes_def conjfy_def
      by (smt (verit, ccfv_threshold))
  qed
qed

end \<comment> \<open>of \<open>lts_tau\<close>\<close>

end
