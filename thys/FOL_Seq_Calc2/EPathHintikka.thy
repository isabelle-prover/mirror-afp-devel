section \<open>Escape path formulas are Hintikka\<close>

theory EPathHintikka imports Hintikka ProverLemmas begin

text \<open>In this theory, we show that the formulas in the sequents on a saturated escape path in a
  proof tree form a Hintikka set.
  This is a crucial part of our completeness proof.\<close>

subsection \<open>Definitions\<close>
text \<open>In this section we define a few concepts that make the following proofs easier to read.\<close>

text \<open>\<open>pseq\<close> is the sequent in a node.\<close>
definition pseq :: \<open>state \<times> rule \<Rightarrow> sequent\<close> where
  \<open>pseq z = snd (fst z)\<close>

text \<open>\<open>ptms\<close> is the list of terms in a node.\<close>
definition ptms :: \<open>state \<times> rule \<Rightarrow> tm list\<close> where
  \<open>ptms z = fst (fst z)\<close>

subsection \<open>Facts about streams\<close>

text \<open>Escape paths are infinite, so if you drop the first \<open>n\<close> nodes, you are still on the path.\<close>
lemma epath_sdrop: \<open>epath steps \<Longrightarrow> epath (sdrop n steps)\<close>
  by (induct n) (auto elim: epath.cases)

text \<open>Dropping the first \<open>n\<close> elements of a stream can only reduce the set of elements in the stream.\<close>
lemma sset_sdrop: \<open>sset (sdrop n s) \<subseteq> sset s\<close>
proof (induct n arbitrary: s)
  case (Suc n)
  then show ?case
    by (metis in_mono sdrop_simps(2) stl_sset subsetI)
qed simp

subsection  \<open>Transformation of states on an escape path\<close>
text \<open>We need to prove some lemmas about how the states of an escape path are connected.\<close>

text \<open>Since escape paths are well-formed, the eff relation holds between the nodes on the path.\<close>
lemma epath_eff:
  assumes \<open>epath steps\<close> \<open>eff (snd (shd steps)) (fst (shd steps)) ss\<close>
  shows \<open>fst (shd (stl steps)) |\<in>| ss\<close>
  using assms by (metis (mono_tags, lifting) epath.simps eff_def)

text \<open>The list of terms in a state contains the terms of the current sequent and the terms from the
  previous state.\<close>
lemma effect_tms:
  assumes \<open>(B, z') |\<in>| effect r (A, z)\<close>
  shows \<open>B = remdups (A @ subterms z @ subterms z')\<close>
  using assms by (smt (verit, best) effect.simps fempty_iff fimageE prod.simps(1))

text \<open>The two previous lemmas can be combined into a single lemma.\<close>
lemma epath_effect:
  assumes \<open>epath steps\<close> \<open>shd steps = ((A, z), r)\<close>
  shows \<open>\<exists>B z' r'. (B, z') |\<in>| effect r (A, z) \<and> shd (stl steps) = ((B, z'), r') \<and>
          (B = remdups (A @ subterms z @ subterms z'))\<close>
  using assms epath_eff effect_tms
  by (metis (mono_tags, lifting) eff_def fst_conv prod.collapse snd_conv)

text \<open>The list of terms in the next state on an escape path contains the terms in the current state
  plus the terms from the next state.\<close>
lemma epath_stl_ptms:
  assumes \<open>epath steps\<close>
  shows \<open>ptms (shd (stl steps)) = remdups (ptms (shd steps) @
    subterms (pseq (shd steps)) @ subterms (pseq (shd (stl steps))))\<close>
  using assms epath_effect
  by (metis (mono_tags) eff_def effect_tms epath_eff pseq_def ptms_def surjective_pairing)

text \<open>The list of terms never decreases on an escape path.\<close>
lemma epath_sdrop_ptms:
  assumes \<open>epath steps\<close>
  shows \<open>set (ptms (shd steps)) \<subseteq> set (ptms (shd (sdrop n steps)))\<close>
  using assms
proof (induct n)
  case (Suc n)
  then have \<open>epath (sdrop n steps)\<close>
    using epath_sdrop by blast
  then show ?case
    using Suc epath_stl_ptms by fastforce
qed simp

subsection \<open>Preservation of formulas on escape paths\<close>

text \<open>If a property will eventually hold on a path, there is some index from which it begins to
  hold, and before which it does not hold.\<close>
lemma ev_prefix_sdrop:
  assumes \<open>ev (holds P) xs\<close>
  shows \<open>\<exists>n. list_all (not P) (stake n xs) \<and> holds P (sdrop n xs)\<close>
  using assms
proof (induct xs)
  case (base xs)
  then show ?case
    by (metis list.pred_inject(1) sdrop.simps(1) stake.simps(1))
next
  case (step xs)
  then show ?case
    by (metis holds.elims(1) list.pred_inject(2) list_all_simps(2) sdrop.simps(1-2) stake.simps(1-2))
qed

text \<open>More specifically, the path will consists of a prefix and a suffix for which the property
  does not hold and does hold, respectively.\<close>
lemma ev_prefix:
  assumes \<open>ev (holds P) xs\<close>
  shows \<open>\<exists>pre suf. list_all (not P) pre \<and> holds P suf \<and> xs = pre @- suf\<close>
  using assms ev_prefix_sdrop by (metis stake_sdrop)

text \<open>All rules are always enabled, so they are also always enabled at specific steps.\<close>
lemma always_enabledAtStep: \<open>enabledAtStep r xs\<close>
  by (simp add: RuleSystem_Defs.enabled_def eff_def)

text \<open>If a formula is in the sequent in the first state of an escape path and none of the rule
  applications in some prefix of the path affect that formula, the formula will still be in the
  sequent after that prefix.\<close>
lemma epath_preserves_unaffected:
  assumes \<open>p \<in> set (pseq (shd steps))\<close> and \<open>epath steps\<close> and \<open>steps = pre @- suf\<close> and
    \<open>list_all (not (\<lambda>step. affects (snd step) p)) pre\<close>
  shows \<open>p \<in> set (pseq (shd suf))\<close>
  using assms
proof (induct pre arbitrary: steps)
  case Nil
  then show ?case
    by simp
next
  case (Cons q pre)
  from this(3) show ?case
  proof cases
    case (epath sl)
    from this(2-4) show ?thesis
      using Cons(1-2, 4-5) effect_preserves_unaffected unfolding eff_def pseq_def list_all_def
      by (metis (no_types, lifting) list.sel(1) list.set_intros(1-2) prod.exhaust_sel
          shift.simps(2) shift_simps(1) stream.sel(2))
  qed
qed

subsection \<open>Formulas on an escape path form a Hintikka set\<close>

text \<open>This definition captures the set of formulas on an entire path\<close>
definition \<open>tree_fms steps \<equiv> \<Union>ss \<in> sset steps. set (pseq ss)\<close>

text \<open>The sequent at the head of a path is in the set of formulas on that path\<close>
lemma pseq_in_tree_fms: \<open>\<lbrakk>x \<in> sset steps; p \<in> set (pseq x)\<rbrakk> \<Longrightarrow> p \<in> tree_fms steps\<close>
  using pseq_def tree_fms_def by blast

text \<open>If a formula is in the set of formulas on a path, there is some index on the path where that
  formula can be found in the sequent.\<close>
lemma tree_fms_in_pseq: \<open>p \<in> tree_fms steps \<Longrightarrow> \<exists>n. p \<in> set (pseq (steps !! n))\<close>
  unfolding pseq_def tree_fms_def using sset_range[of steps] by simp

text \<open>If a path is saturated, so is any suffix of that path (since saturation is defined in terms of
  the always operator).\<close>
lemma Saturated_sdrop: \<open>Saturated steps \<Longrightarrow> Saturated (sdrop n steps)\<close>
  by (simp add: RuleSystem_Defs.Saturated_def alw_iff_sdrop saturated_def)

text \<open>This is an abbreviation that determines whether a given rule is applied in a given state.\<close>
abbreviation \<open>is_rule r step \<equiv> snd step = r\<close>

text \<open>If a path is saturated, it is always possible to find a state in which a given rule is applied.\<close>
lemma Saturated_ev_rule:
  assumes \<open>Saturated steps\<close>
  shows \<open>ev (holds (is_rule r)) (sdrop n steps)\<close>
proof -
  have \<open>Saturated (sdrop n steps)\<close>
    using \<open>Saturated steps\<close> Saturated_sdrop by fast
  moreover have \<open>r \<in> Prover.R\<close>
    by (metis rules_repeat snth_sset)
  ultimately have \<open>saturated r (sdrop n steps)\<close>
    unfolding Saturated_def by fast
  then show ?thesis
    unfolding saturated_def using always_enabledAtStep holds.elims(3) by blast
qed

text \<open>On an escape path, the sequent is never an axiom (since that would end the branch, and escape
  paths are infinitely long).\<close>
lemma epath_never_branchDone:
  assumes \<open>epath steps\<close>
  shows \<open>alw (holds (not (branchDone o pseq))) steps\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then have \<open>ev (holds (branchDone o pseq)) steps\<close>
    by (simp add: alw_iff_sdrop ev_iff_sdrop)
  then obtain n where n: \<open>holds (branchDone o pseq) (sdrop n steps)\<close>
    using sdrop_wait by blast
  let ?suf = \<open>sdrop n steps\<close>
  have \<open>\<forall>r A. effect r (A, pseq (shd ?suf)) = {||}\<close>
    unfolding effect_def using n by simp
  moreover have \<open>epath ?suf\<close>
    using \<open>epath steps\<close> epath_sdrop by blast
  then have \<open>\<forall>r A. \<exists>z' r'. z' |\<in>| effect r (A, pseq (shd ?suf)) \<and> shd (stl ?suf) = (z', r')\<close>
    using epath_effect by (metis calculation prod.exhaust_sel pseq_def)
  ultimately show False
    by blast
qed

text \<open>Finally we arrive at the main result of this theory:
  The set of formulas on a saturated escape path form a Hintikka set.

  The proof basically says that, given a formula, we can find some index into the path where a rule
  is applied to decompose that formula into the parts needed for the Hintikka set.
  The lemmas above are used to guarantee that the formula does not disappear (and that the branch
  does not end) before the rule is applied, and that the correct formulas are generated by the
  effect function when the rule is finally applied.
  For Beta rules, only one of the constituent formulas need to be on the path, since the path runs
  along only one of the two branches.
  For Gamma and Delta rules, the construction of the list of terms in each state guarantees that
  the formulas are instantiated with terms in the Hintikka set.\<close>
lemma escape_path_Hintikka:
  assumes \<open>epath steps\<close> and \<open>Saturated steps\<close>
  shows \<open>Hintikka (tree_fms steps)\<close>
    (is \<open>Hintikka ?H\<close>)
proof
  fix n ts
  assume pre: \<open>Pre n ts \<in> ?H\<close>
  then obtain m where m: \<open>Pre n ts \<in> set (pseq (shd (sdrop m steps)))\<close>
    using tree_fms_in_pseq by auto

  show \<open>Neg (Pre n ts) \<notin> ?H\<close>
  proof
    assume \<open>Neg (Pre n ts) \<in> ?H\<close>
    then obtain k where k: \<open>Neg (Pre n ts) \<in> set (pseq (shd (sdrop k steps)))\<close>
      using tree_fms_in_pseq by auto

    let ?pre = \<open>stake (m + k) steps\<close>
    let ?suf = \<open>sdrop (m + k) steps\<close>

    have
      1: \<open>\<not> affects r (Pre n ts)\<close> and
      2: \<open>\<not> affects r (Neg (Pre n ts))\<close> for r
      unfolding affects_def by (cases r, simp_all)+

    have \<open>list_all (not (\<lambda>step. affects (snd step) (Pre n ts))) ?pre\<close>
      unfolding list_all_def using 1 by (induct ?pre) simp_all
    then have p: \<open>Pre n ts \<in> set (pseq (shd ?suf))\<close>
      using \<open>epath steps\<close> epath_preserves_unaffected m epath_sdrop
      by (metis (no_types, lifting) list.pred_mono_strong list_all_append
          sdrop_add stake_add stake_sdrop)

    have \<open>list_all (not (\<lambda>step. affects (snd step) (Neg (Pre n ts)))) ?pre\<close>
      unfolding list_all_def using 2 by (induct ?pre) simp_all
    then have np: \<open>Neg (Pre n ts) \<in> set (pseq (shd ?suf))\<close>
      using \<open>epath steps\<close> epath_preserves_unaffected k epath_sdrop
      by (smt (verit, best) add.commute list.pred_mono_strong list_all_append sdrop_add
          stake_add stake_sdrop)

    have \<open>holds (branchDone o pseq) ?suf\<close>
      using p np branchDone_contradiction by auto
    moreover have \<open>\<not> holds (branchDone o pseq) ?suf\<close>
      using \<open>epath steps\<close> epath_never_branchDone by (simp add: alw_iff_sdrop)
    ultimately show False
      by blast
  qed
next
  fix p q
  assume \<open>Dis p q \<in> ?H\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = AlphaDis
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B z' r' where
    z': \<open>(B, z') |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, z'), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  ultimately have \<open>p \<in> set z'\<close> \<open>q \<in> set z'\<close>
    using parts_in_effect unfolding parts_def by fastforce+

  then show \<open>p \<in> ?H \<and> q \<in> ?H\<close>
    using z'(2) ori pseq_in_tree_fms
    by (metis (no_types, opaque_lifting) Un_iff fst_conv pseq_def shd_sset snd_conv sset_sdrop
        sset_shift stl_sset subset_eq)
next
  fix p q
  assume \<open>Imp p q \<in> tree_fms steps\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = AlphaImp
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B z' r' where
    z': \<open>(B, z') |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, z'), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  ultimately have \<open>Neg p \<in> set z'\<close> \<open>q \<in> set z'\<close>
    using parts_in_effect unfolding parts_def by fastforce+

  then show \<open>Neg p \<in> ?H \<and> q \<in> ?H\<close>
    using z'(2) ori pseq_in_tree_fms
    by (metis (no_types, opaque_lifting) Un_iff fst_conv pseq_def shd_sset snd_conv sset_sdrop
        sset_shift stl_sset subset_eq)
next
  fix p q
  assume \<open>Neg (Con p q) \<in> ?H\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = AlphaCon
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B z' r' where
    z': \<open>(B, z') |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, z'), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  ultimately have \<open>Neg p \<in> set z'\<close> \<open>Neg q \<in> set z'\<close>
    using parts_in_effect unfolding parts_def by fastforce+

  then show \<open>Neg p \<in> ?H \<and> Neg q \<in> ?H\<close>
    using z'(2) ori pseq_in_tree_fms
    by (metis (no_types, opaque_lifting) Un_iff fst_conv pseq_def shd_sset snd_conv sset_sdrop
        sset_shift stl_sset subset_eq)
next
  fix p q
  assume \<open>Con p q \<in> ?H\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = BetaCon
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B z' r' where
    z': \<open>(B, z') |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, z'), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  ultimately consider \<open>p \<in> set z'\<close> | \<open>q \<in> set z'\<close>
    using parts_in_effect unfolding parts_def by fastforce

  then show \<open>p \<in> ?H \<or> q \<in> ?H\<close>
    using z'(2) ori pseq_in_tree_fms
    by (metis (no_types, opaque_lifting) Un_iff fst_conv pseq_def shd_sset snd_conv sset_sdrop
        sset_shift stl_sset subset_eq)
next
  fix p q
  assume \<open>Neg (Imp p q) \<in> ?H\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = BetaImp
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B z' r' where
    z': \<open>(B, z') |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, z'), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  ultimately consider \<open>p \<in> set z'\<close> | \<open>Neg q \<in> set z'\<close>
    using parts_in_effect unfolding parts_def by fastforce

  then show \<open>p \<in> ?H \<or> Neg q \<in> ?H\<close>
    using z'(2) ori pseq_in_tree_fms
    by (metis (no_types, opaque_lifting) Un_iff fst_conv pseq_def shd_sset snd_conv sset_sdrop
        sset_shift stl_sset subset_eq)
next
  fix p q
  assume \<open>Neg (Dis p q) \<in> ?H\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = BetaDis
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B z' r' where
    z': \<open>(B, z') |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, z'), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  ultimately consider \<open>Neg p \<in> set z'\<close> | \<open>Neg q \<in> set z'\<close>
    using parts_in_effect unfolding parts_def by fastforce

  then show \<open>Neg p \<in> ?H \<or> Neg q \<in> ?H\<close>
    using z'(2) ori pseq_in_tree_fms
    by (metis (no_types, opaque_lifting) Un_iff fst_conv pseq_def shd_sset snd_conv sset_sdrop
        sset_shift stl_sset subset_eq)
next
  fix p
  assume \<open>Exi p \<in> ?H\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto

  let ?r = GammaExi

  show \<open>\<forall>t \<in> terms ?H. sub 0 t p \<in> ?H\<close>
  proof
    fix t
    assume t: \<open>t \<in> terms ?H\<close>
    show \<open>sub 0 t p \<in> ?H\<close>
    proof -
      have \<open>\<exists>m. t \<in> set (subterms (pseq (shd (sdrop m steps))))\<close>
      proof (cases \<open>(\<Union>f \<in> ?H. set (subtermFm f)) = {}\<close>)
        case True
        moreover have \<open>\<forall>p \<in> set (pseq (shd steps)). p \<in> ?H\<close>
          unfolding tree_fms_def by (metis pseq_in_tree_fms shd_sset tree_fms_def)
        ultimately have \<open>\<forall>p \<in> set (pseq (shd steps)). subtermFm p = []\<close>
          by simp
        then have \<open>concat (map subtermFm (pseq (shd steps))) = []\<close>
          by (induct \<open>pseq (shd steps)\<close>) simp_all
        then have \<open>subterms (pseq (shd steps)) = [Fun 0 []]\<close>
          unfolding subterms_def by (metis list.simps(4) remdups_eq_nil_iff)
        then show ?thesis
          using True t unfolding terms_def
          by (metis empty_iff insert_iff list.set_intros(1) sdrop.simps(1))
      next
        case False
        then obtain pt where pt: \<open>t \<in> set (subtermFm pt)\<close> \<open>pt \<in> ?H\<close>
          using t unfolding terms_def by (metis (no_types, lifting) UN_E)
        then obtain m where m: \<open>pt \<in> set (pseq (shd (sdrop m steps)))\<close>
          using tree_fms_in_pseq by auto
        then show ?thesis
          using pt(1) set_subterms by fastforce
      qed
      then obtain m where \<open>t \<in> set (subterms (pseq (shd (sdrop m steps))))\<close>
        by blast
      then have \<open>t \<in> set (ptms (shd (stl (sdrop m steps))))\<close>
        using epath_stl_ptms epath_sdrop \<open>epath steps\<close>
        by (metis (no_types, opaque_lifting) Un_iff set_append set_remdups)
      moreover have \<open>epath (stl (sdrop m steps))\<close>
        using epath_sdrop \<open>epath steps\<close> by (meson epath.cases)
      ultimately have \<open>\<forall>k \<ge> m. t \<in> set (ptms (shd (stl (sdrop k steps))))\<close>
        using epath_sdrop_ptms by (metis (no_types, lifting) le_Suc_ex sdrop_add sdrop_stl subsetD)
      then have above: \<open>\<forall>k > m. t \<in> set (ptms (shd (sdrop k steps)))\<close>
        by (metis Nat.lessE less_irrefl_nat less_trans_Suc linorder_not_less sdrop_simps(2))

      let ?pre = \<open>stake (n + m + 1) steps\<close>
      let ?suf = \<open>sdrop (n + m + 1) steps\<close>

      have *: \<open>\<not> affects r ?f\<close> for r
        unfolding affects_def by (cases r, simp_all)+

      have \<open>ev (holds (is_rule ?r)) ?suf\<close>
        using \<open>Saturated steps\<close> Saturated_ev_rule by blast
      then obtain pre suf k where
        pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
        suf: \<open>holds (is_rule ?r) suf\<close> and
        ori: \<open>pre = stake k ?suf\<close> \<open>suf = sdrop k ?suf\<close>
        using ev_prefix_sdrop by blast

      have k: \<open>\<exists>k > m. suf = sdrop k steps\<close>
        using ori by (meson le_add2 less_add_one order_le_less_trans sdrop_add trans_less_add1)

      have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) ?pre\<close>
        unfolding list_all_def using * by (induct ?pre) simp_all
      then have \<open>?f \<in> set (pseq (shd ?suf))\<close>
        using \<open>epath steps\<close> epath_preserves_unaffected n epath_sdrop
        by (metis (no_types, lifting) list.pred_mono_strong list_all_append
            sdrop_add stake_add stake_sdrop)
      then have \<open>?f \<in> set (pseq (shd suf))\<close>
        using \<open>epath steps\<close> epath_preserves_unaffected n epath_sdrop * ori
        by (metis (no_types, lifting) list.pred_mono_strong pre stake_sdrop)
      moreover have \<open>epath suf\<close>
        using \<open>epath steps\<close> epath_sdrop ori by blast
      then obtain B z' r' where
        z': \<open>(B, z') |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close>
        \<open>shd (stl suf) = ((B, z'), r')\<close>
        using suf epath_effect unfolding pseq_def ptms_def
        by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)

      moreover have \<open>t \<in> set (ptms (shd suf))\<close>
        using above k by (meson le_add2 less_add_one order_le_less_trans)
      ultimately have \<open>sub 0 t p \<in> set z'\<close>
        using parts_in_effect[where A=\<open>ptms (shd suf)\<close>] unfolding parts_def by fastforce
      then show ?thesis
        using k pseq_in_tree_fms z'(2)
        by (metis Pair_inject in_mono prod.collapse pseq_def shd_sset sset_sdrop stl_sset)
    qed
  qed
next
  fix p
  assume \<open>Neg (Uni p) \<in> ?H\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto

  let ?r = GammaUni

  show \<open>\<forall>t \<in> terms ?H. Neg (sub 0 t p) \<in> ?H\<close>
  proof
    fix t
    assume t: \<open>t \<in> terms ?H\<close>
    show \<open>Neg (sub 0 t p) \<in> ?H\<close>
    proof -
      have \<open>\<exists>m. t \<in> set (subterms (pseq (shd (sdrop m steps))))\<close>
      proof (cases \<open>(\<Union>f \<in> ?H. set (subtermFm f)) = {}\<close>)
        case True
        moreover have \<open>\<forall>p \<in> set (pseq (shd steps)). p \<in> ?H\<close>
          unfolding tree_fms_def by (metis pseq_in_tree_fms shd_sset tree_fms_def)
        ultimately have \<open>\<forall>p \<in> set (pseq (shd steps)). subtermFm p = []\<close>
          by simp
        then have \<open>concat (map subtermFm (pseq (shd steps))) = []\<close>
          by (induct \<open>pseq (shd steps)\<close>) simp_all
        then have \<open>subterms (pseq (shd steps)) = [Fun 0 []]\<close>
          unfolding subterms_def by (metis list.simps(4) remdups_eq_nil_iff)
        then show ?thesis
          using True t unfolding terms_def
          by (metis empty_iff insert_iff list.set_intros(1) sdrop.simps(1))
      next
        case False
        then obtain pt where pt: \<open>t \<in> set (subtermFm pt)\<close> \<open>pt \<in> ?H\<close>
          using t unfolding terms_def by (metis (no_types, lifting) UN_E)
        then obtain m where m: \<open>pt \<in> set (pseq (shd (sdrop m steps)))\<close>
          using tree_fms_in_pseq by auto
        then show ?thesis
          using pt(1) set_subterms by fastforce
      qed
      then obtain m where \<open>t \<in> set (subterms (pseq (shd (sdrop m steps))))\<close>
        by blast
      then have \<open>t \<in> set (ptms (shd (stl (sdrop m steps))))\<close>
        using epath_stl_ptms epath_sdrop \<open>epath steps\<close>
        by (metis (no_types, lifting) Un_iff set_append set_remdups)
      moreover have \<open>epath (stl (sdrop m steps))\<close>
        using epath_sdrop \<open>epath steps\<close> by (meson epath.cases)
      ultimately have \<open>\<forall>k \<ge> m. t \<in> set (ptms (shd (stl (sdrop k steps))))\<close>
        using epath_sdrop_ptms by (metis (no_types, lifting) le_Suc_ex sdrop_add sdrop_stl subsetD)
      then have above: \<open>\<forall>k > m. t \<in> set (ptms (shd (sdrop k steps)))\<close>
        by (metis Nat.lessE less_irrefl_nat less_trans_Suc linorder_not_less sdrop_simps(2))

      let ?pre = \<open>stake (n + m + 1) steps\<close>
      let ?suf = \<open>sdrop (n + m + 1) steps\<close>

      have *: \<open>\<not> affects r ?f\<close> for r
        unfolding affects_def by (cases r, simp_all)+

      have \<open>ev (holds (is_rule ?r)) ?suf\<close>
        using \<open>Saturated steps\<close> Saturated_ev_rule by blast
      then obtain pre suf k where
        pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
        suf: \<open>holds (is_rule ?r) suf\<close> and
        ori: \<open>pre = stake k ?suf\<close> \<open>suf = sdrop k ?suf\<close>
        using ev_prefix_sdrop by blast

      have k: \<open>\<exists>k > m. suf = sdrop k steps\<close>
        using ori by (meson le_add2 less_add_one order_le_less_trans sdrop_add trans_less_add1)

      have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) ?pre\<close>
        unfolding list_all_def using * by (induct ?pre) simp_all
      then have \<open>?f \<in> set (pseq (shd ?suf))\<close>
        using \<open>epath steps\<close> epath_preserves_unaffected n epath_sdrop
        by (metis (no_types, lifting) list.pred_mono_strong list_all_append
            sdrop_add stake_add stake_sdrop)
      then have \<open>?f \<in> set (pseq (shd suf))\<close>
        using \<open>epath steps\<close> epath_preserves_unaffected n epath_sdrop * ori
        by (metis (no_types, lifting) list.pred_mono_strong pre stake_sdrop)
      moreover have \<open>epath suf\<close>
        using \<open>epath steps\<close> epath_sdrop ori by blast
      then obtain B z' r' where
        z': \<open>(B, z') |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close>
        \<open>shd (stl suf) = ((B, z'), r')\<close>
        using suf epath_effect unfolding pseq_def ptms_def
        by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)

      moreover have \<open>t \<in> set (ptms (shd suf))\<close>
        using above k by (meson le_add2 less_add_one order_le_less_trans)
      ultimately have \<open>Neg (sub 0 t p) \<in> set z'\<close>
        using parts_in_effect[where A=\<open>ptms (shd suf)\<close>] unfolding parts_def by fastforce
      then show ?thesis
        using k pseq_in_tree_fms z'(2)
        by (metis Pair_inject in_mono prod.collapse pseq_def shd_sset sset_sdrop stl_sset)
    qed
  qed
next
  fix p
  assume \<open>Uni p \<in> tree_fms steps\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = DeltaUni
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B z' r' where
    z': \<open>(B, z') |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, z'), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  ultimately obtain C where
    C: \<open>set (ptms (shd suf)) \<subseteq> set C\<close> \<open>sub 0 (Fun (generateNew C) []) p \<in> set z'\<close>
    using parts_in_effect[where B=B and z'=\<open>z'\<close> and z=\<open>pseq (shd suf)\<close> and r=\<open>?r\<close> and p=\<open>Uni p\<close>]
    unfolding parts_def by auto
  then have *: \<open>sub 0 (Fun (generateNew C) []) p \<in> ?H\<close>
    using z'(2) ori pseq_in_tree_fms
    by (metis (no_types, lifting) Pair_inject Un_iff in_mono prod.collapse pseq_def shd_sset
        sset_sdrop sset_shift stl_sset)
  let ?t = \<open>Fun (generateNew C) []\<close>
  show \<open>\<exists>t \<in> terms ?H. sub 0 t p \<in> ?H\<close>
  proof (cases \<open>?t \<in> set (subtermFm (sub 0 ?t p))\<close>)
    case True
    then have \<open>?t \<in> terms ?H\<close>
      unfolding terms_def using * by (metis UN_I empty_iff)
    then show ?thesis
      using * by blast
  next
    case False
    then have \<open>sub 0 t p = sub 0 ?t p\<close> for t
      using sub_const_transfer by metis
    moreover have \<open>terms ?H \<noteq> {}\<close>
      unfolding terms_def by simp
    then have \<open>\<exists>t. t \<in> terms ?H\<close>
      by blast
    ultimately show ?thesis
      using * by metis
  qed
next
  fix p
  assume \<open>Neg (Exi p) \<in> tree_fms steps\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = DeltaExi
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B z' r' where
    z': \<open>(B, z') |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, z'), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  ultimately obtain C where
    C: \<open>set (ptms (shd suf)) \<subseteq> set C\<close> \<open>Neg (sub 0 (Fun (generateNew C) []) p) \<in> set z'\<close>
    using parts_in_effect[where B=B and z'=z' and z=\<open>pseq (shd suf)\<close> and r=\<open>?r\<close> and p=\<open>Neg (Exi p)\<close>]
    unfolding parts_def by auto
  then have *: \<open>Neg (sub 0 (Fun (generateNew C) []) p) \<in> ?H\<close>
    using z'(2) ori pseq_in_tree_fms
    by (metis (no_types, lifting) Pair_inject Un_iff in_mono prod.collapse pseq_def shd_sset
        sset_sdrop sset_shift stl_sset)
  let ?t = \<open>Fun (generateNew C) []\<close>
  show \<open>\<exists>t \<in> terms ?H. Neg (sub 0 t p) \<in> ?H\<close>
  proof (cases \<open>?t \<in> set (subtermFm (Neg (sub 0 ?t p)))\<close>)
    case True
    then have \<open>?t \<in> terms ?H\<close>
      unfolding terms_def using * by (metis UN_I empty_iff)
    then show ?thesis
      using * by blast
  next
    case False
    then have \<open>Neg (sub 0 t p) = Neg (sub 0 ?t p)\<close> for t
      using sub_const_transfer by (metis subtermFm.simps(7))
    moreover have \<open>terms ?H \<noteq> {}\<close>
      unfolding terms_def by simp
    then have \<open>\<exists>t. t \<in> terms ?H\<close>
      by blast
    ultimately show ?thesis
      using * by metis
  qed
next
  fix p
  assume \<open>Neg (Neg p) \<in> tree_fms steps\<close> (is \<open>?f \<in> ?H\<close>)
  then obtain n where n: \<open>?f \<in> set (pseq (shd (sdrop n steps)))\<close>
    using tree_fms_in_pseq by auto
  let ?steps = \<open>sdrop n steps\<close>
  let ?r = NegNeg
  have \<open>ev (holds (is_rule ?r)) ?steps\<close>
    using \<open>Saturated steps\<close> Saturated_ev_rule by blast
  then obtain pre suf where
    pre: \<open>list_all (not (is_rule ?r)) pre\<close> and
    suf: \<open>holds (is_rule ?r) suf\<close> and
    ori: \<open>?steps = pre @- suf\<close>
    using ev_prefix by blast

  have \<open>affects r ?f \<longleftrightarrow> r = ?r\<close> for r
    unfolding affects_def by (cases r) simp_all
  then have \<open>list_all (not (\<lambda>step. affects (snd step) ?f)) pre\<close>
    using pre by simp
  moreover have \<open>epath (pre @- suf)\<close>
    using \<open>epath steps\<close> epath_sdrop ori by metis
  ultimately have \<open>?f \<in> set (pseq (shd suf))\<close>
    using epath_preserves_unaffected n ori by metis

  moreover have \<open>epath suf\<close>
    using \<open>epath (pre @- suf)\<close> epath_sdrop by (metis alwD alw_iff_sdrop alw_shift)
  then obtain B z' r' where
    z': \<open>(B, z') |\<in>| effect ?r (ptms (shd suf), pseq (shd suf))\<close> \<open>shd (stl suf) = ((B, z'), r')\<close>
    using suf epath_effect unfolding pseq_def ptms_def
    by (metis (mono_tags, lifting) holds.elims(2) prod.collapse)
  ultimately have \<open>p \<in> set z'\<close>
    using parts_in_effect unfolding parts_def by fastforce

  then show \<open>p \<in> ?H\<close>
    using z'(2) ori pseq_in_tree_fms
    by (metis (no_types, lifting) Pair_inject Un_iff in_mono prod.collapse pseq_def shd_sset
        sset_sdrop sset_shift stl_sset)
qed

end
