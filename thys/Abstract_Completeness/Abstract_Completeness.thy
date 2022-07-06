(*<*)
(* An abstract completeness theorem *)
theory Abstract_Completeness
imports
  Collections.Locale_Code
  "HOL-Library.Countable_Set"
  "HOL-Library.FSet"
  "HOL-Library.Code_Target_Nat"
  "HOL-Library.Linear_Temporal_Logic_on_Streams"
begin
(*>*)

section\<open>General Tree Concepts\<close>

codatatype 'a tree = Node (root: 'a) (cont: \<open>'a tree fset\<close>)

inductive tfinite where
  tfinite: \<open>(\<And> t'. t' |\<in>| cont t \<Longrightarrow> tfinite t') \<Longrightarrow> tfinite t\<close>


(*<*)(* Infinite paths in trees. *)(*>*)
coinductive ipath where
  ipath: \<open>\<lbrakk>root t = shd steps; t' |\<in>| cont t; ipath t' (stl steps)\<rbrakk> \<Longrightarrow> ipath t steps\<close>

(*<*)(* Finite trees have no infinite paths. *)
lemma ftree_no_ipath: \<open>tfinite t \<Longrightarrow> \<not> ipath t steps\<close>
  by (induct t arbitrary: steps rule: tfinite.induct) (auto elim: ipath.cases)
(*>*)

primcorec konig where
  \<open>shd (konig t) = root t\<close>
| \<open>stl (konig t) = konig (SOME t'. t' |\<in>| cont t \<and> \<not> tfinite t')\<close>

lemma Konig: \<open>\<not> tfinite t \<Longrightarrow> ipath t (konig t)\<close>
  by (coinduction arbitrary: t) (metis (lifting) tfinite.simps konig.simps someI_ex)


section\<open>Rule Systems\<close>

(*<*)(* A step consists of a pair (s,r) such that the rule r is taken in state s. *)(*>*)
type_synonym ('state, 'rule) step = \<open>'state \<times> 'rule\<close>

(*<*)(* A derivation tree is a tree of steps: *)(*>*)
type_synonym ('state, 'rule) dtree = \<open>('state, 'rule) step tree\<close>

locale RuleSystem_Defs =
fixes eff :: \<open>'rule \<Rightarrow> 'state \<Rightarrow> 'state fset \<Rightarrow> bool\<close>
(* The countable set of rules is initially provided as a stream: *)
and rules :: \<open>'rule stream\<close>
begin

abbreviation \<open>R \<equiv> sset rules\<close>

lemma countable_R: \<open>countable R\<close> by (metis countableI_type countable_image sset_range)
lemma NE_R: \<open>R \<noteq> {}\<close> by (metis UNIV_witness all_not_in_conv empty_is_image sset_range)

definition \<open>enabled r s \<equiv> \<exists> sl. eff r s sl\<close>
definition \<open>pickEff r s \<equiv> if enabled r s then (SOME sl. eff r s sl) else the None\<close>

lemma pickEff: \<open>enabled r s \<Longrightarrow> eff r s (pickEff r s)\<close>
  by (metis enabled_def pickEff_def tfl_some)

abbreviation \<open>effStep step \<equiv> eff (snd step) (fst step)\<close>
abbreviation \<open>enabledAtStep r step \<equiv> enabled r (fst step)\<close>
abbreviation \<open>takenAtStep r step \<equiv> snd step = r\<close>

text \<open>Saturation is a very strong notion of fairness:
  If a rule is enabled at some point, it will eventually be taken.\<close>
definition \<open>saturated r \<equiv> alw (holds (enabledAtStep r) impl ev (holds (takenAtStep r)))\<close>
definition \<open>Saturated steps \<equiv> \<forall> r \<in> R. saturated r steps\<close>

(*<*)(* Well-formed derivation trees *)(*>*)
coinductive wf where
  wf: \<open>\<lbrakk>snd (root t) \<in> R; effStep (root t) (fimage (fst o root) (cont t));
    \<And>t'. t' |\<in>| cont t \<Longrightarrow> wf t'\<rbrakk> \<Longrightarrow> wf t\<close>


(*<*)(* Escape paths *)(*>*)
coinductive epath where
  epath: \<open>\<lbrakk>snd (shd steps) \<in> R; fst (shd (stl steps)) |\<in>| sl; effStep (shd steps) sl;
    epath (stl steps)\<rbrakk> \<Longrightarrow> epath steps\<close>

lemma wf_ipath_epath:
  assumes \<open>wf t\<close> \<open>ipath t steps\<close>
  shows \<open>epath steps\<close>
proof -
  have *: \<open>\<And>t st. ipath t st \<Longrightarrow> root t = shd st\<close> by (auto elim: ipath.cases)
  show ?thesis using assms
  proof (coinduction arbitrary: t steps)
    case epath
    then show ?case by (cases rule: wf.cases[case_product ipath.cases]) (metis * o_apply fimageI)
  qed
qed

definition \<open>fair rs \<equiv> sset rs \<subseteq> R \<and> (\<forall> r \<in> R. alw (ev (holds ((=) r))) rs)\<close>

lemma fair_stl: \<open>fair rs \<Longrightarrow> fair (stl rs)\<close>
  unfolding fair_def by (metis alw.simps subsetD stl_sset subsetI)

lemma sdrop_fair: \<open>fair rs \<Longrightarrow> fair (sdrop m rs)\<close>
  using alw_sdrop unfolding fair_def by (metis alw.coinduct alw_nxt fair_def fair_stl)


section\<open>A Fair Enumeration of the Rules\<close>

(*<*)(* The fair enumeration of rules *)(*>*)
definition \<open>fenum \<equiv> flat (smap (\<lambda>n. stake n rules) (fromN 1))\<close>

lemma sset_fenum: \<open>sset fenum = R\<close>
  unfolding fenum_def by (subst sset_flat)
   (auto simp: stream.set_map in_set_conv_nth sset_range[of rules],
     metis atLeast_Suc_greaterThan greaterThan_0 lessI range_eqI stake_nth)

lemma fair_fenum: \<open>fair fenum\<close>
proof -
  { fix r assume \<open>r \<in> R\<close>
    then obtain m where r: \<open>r = rules !! m\<close> unfolding sset_range by blast
    { fix n :: nat and rs let ?fenum = \<open>\<lambda>n. flat (smap (\<lambda>n. stake n rules) (fromN n))\<close>
      assume \<open>n > 0\<close>
      hence \<open>alw (ev (holds ((=) r))) (rs @- ?fenum n)\<close>
      proof (coinduction arbitrary: n rs)
        case alw
        show ?case
        proof (rule exI[of _ \<open>rs @- ?fenum n\<close>], safe)
          show \<open>\<exists>n' rs'. stl (rs @- ?fenum n) = rs' @- ?fenum n' \<and> n' > 0\<close>
          proof(cases rs)
            case Nil thus ?thesis unfolding alw by (intro exI) auto
          qed (auto simp: alw intro: exI[of _ n])
        next
          show \<open>ev (holds ((=) r)) (rs @- flat (smap (\<lambda>n. stake n rules) (fromN n)))\<close>
            using alw r unfolding ev_holds_sset
            by (cases \<open>m < n\<close>) (force simp: stream.set_map in_set_conv_nth)+
        qed
     qed
    }
  }
  thus \<open>fair fenum\<close> unfolding fair_def sset_fenum
    by (metis fenum_def alw_shift le_less zero_less_one)
qed

definition \<open>trim rs s = sdrop_while (\<lambda>r. Not (enabled r s)) rs\<close>


(*<*)(* The fair tree associated to a stream of rules and a state *)(*>*)
primcorec mkTree where
  \<open>root (mkTree rs s) = (s, (shd (trim rs s)))\<close>
| \<open>cont (mkTree rs s) = fimage (mkTree (stl (trim rs s))) (pickEff (shd (trim rs s)) s)\<close>

(*<*)(* More efficient code equation for mkTree *)(*>*)
lemma mkTree_unfold[code]:
  \<open>mkTree rs s = (case trim rs s of SCons r s' \<Rightarrow> Node (s, r) (fimage (mkTree s') (pickEff r s)))\<close>
  by (subst mkTree.ctr) (simp split: stream.splits)

end

locale RuleSystem = RuleSystem_Defs eff rules
for eff :: \<open>'rule \<Rightarrow> 'state \<Rightarrow> 'state fset \<Rightarrow> bool\<close> and rules :: \<open>'rule stream\<close> +
fixes S :: \<open>'state set\<close>
assumes eff_S: \<open>\<And> s r sl s'. \<lbrakk>s \<in> S; r \<in> R; eff r s sl; s' |\<in>| sl\<rbrakk> \<Longrightarrow> s' \<in> S\<close>
and enabled_R: \<open>\<And> s. s \<in> S \<Longrightarrow> \<exists> r \<in> R. \<exists> sl. eff r s sl\<close>
begin

(*<*)(* The minimum waiting time in a stream for the enabled rules in a given state: *)(*>*)
definition \<open>minWait rs s \<equiv> LEAST n. enabled (shd (sdrop n rs)) s\<close>

lemma trim_alt:
  assumes s: \<open>s \<in> S\<close> and rs: \<open>fair rs\<close>
  shows \<open>trim rs s = sdrop (minWait rs s) rs\<close>
proof (unfold trim_def minWait_def sdrop_simps, rule sdrop_while_sdrop_LEAST[unfolded o_def])
  from enabled_R[OF s] obtain r sl where r: \<open>r \<in> R\<close> and sl: \<open>eff r s sl\<close> by blast
  from bspec[OF conjunct2[OF rs[unfolded fair_def]] r] obtain m where \<open>r = rs !! m\<close>
    by atomize_elim (erule alw.cases, auto simp only: ev_holds_sset sset_range)
  with r sl show \<open>\<exists>n. enabled (rs !! n) s\<close> unfolding enabled_def by auto
qed

lemma minWait_ex:
  assumes s: \<open>s \<in> S\<close> and rs: \<open>fair rs\<close>
  shows \<open>\<exists> n. enabled (shd (sdrop n rs)) s\<close>
proof -
  obtain r where r: \<open>r \<in> R\<close> and e: \<open>enabled r s\<close> using enabled_R s unfolding enabled_def by blast
  then obtain n where \<open>shd (sdrop n rs) = r\<close> using sdrop_fair[OF rs]
    by (metis (full_types) alw_nxt holds.simps sdrop.simps(1) fair_def sdrop_wait)
  thus ?thesis using r e by auto
qed

lemma assumes \<open>s \<in> S\<close> and \<open>fair rs\<close>
  shows trim_in_R: \<open>shd (trim rs s) \<in> R\<close>
  and trim_enabled: \<open>enabled (shd (trim rs s)) s\<close>
  and trim_fair: \<open>fair (trim rs s)\<close>
  unfolding trim_alt[OF assms] minWait_def
  using LeastI_ex[OF minWait_ex[OF assms]] sdrop_fair[OF assms(2)]
    conjunct1[OF assms(2)[unfolded fair_def]] by simp_all (metis subsetD snth_sset)

lemma minWait_least: \<open>\<lbrakk>enabled (shd (sdrop n rs)) s\<rbrakk> \<Longrightarrow> minWait rs s \<le> n\<close>
  unfolding minWait_def by (intro Least_le conjI)

lemma in_cont_mkTree:
  assumes s: \<open>s \<in> S\<close> and rs: \<open>fair rs\<close> and t': \<open>t' |\<in>| cont (mkTree rs s)\<close>
  shows \<open>\<exists> sl' s'. s' \<in> S \<and> eff (shd (trim rs s)) s sl' \<and>
                 s' |\<in>| sl' \<and> t' = mkTree (stl (trim rs s)) s'\<close>
proof -
  define sl' where \<open>sl' = pickEff (shd (trim rs s)) s\<close>
  obtain s' where s': \<open>s' |\<in>| sl'\<close> and \<open>t' = mkTree (stl (trim rs s)) s'\<close>
    using t' unfolding sl'_def by auto
  moreover have 1: \<open>enabled (shd (trim rs s)) s\<close> using trim_enabled[OF s rs] .
  moreover with trim_in_R pickEff eff_S s rs s'[unfolded sl'_def] have \<open>s' \<in> S\<close> by blast
  ultimately show ?thesis unfolding sl'_def using pickEff by blast
qed

lemma ipath_mkTree_sdrop:
  assumes s: \<open>s \<in> S\<close> and rs: \<open>fair rs\<close> and i: \<open>ipath (mkTree rs s) steps\<close>
  shows \<open>\<exists> n s'. s' \<in> S \<and> ipath (mkTree (sdrop n rs) s') (sdrop m steps)\<close>
using s rs i proof (induct m arbitrary: steps rs)
  case (Suc m)
  then obtain n s' where s': \<open>s' \<in> S\<close>
    and ip: \<open>ipath (mkTree (sdrop n rs) s') (sdrop m steps)\<close> (is \<open>ipath ?t _\<close>) by blast
  from ip obtain t' where r: \<open>root ?t = shd (sdrop m steps)\<close> and t': \<open>t' |\<in>| cont ?t\<close>
    and i: \<open>ipath t' (sdrop (Suc m) steps)\<close> by (cases, simp)
  from in_cont_mkTree[OF s' sdrop_fair[OF Suc.prems(2)] t'] obtain sl'' s'' where
    e: \<open>eff (shd (trim (sdrop n rs) s')) s' sl''\<close> and
    s'': \<open>s'' |\<in>| sl''\<close> and t'_def: \<open>t' = mkTree (stl (trim (sdrop n rs) s')) s''\<close> by blast
  have \<open>shd (trim (sdrop n rs) s') \<in> R\<close> by (metis sdrop_fair Suc.prems(2) trim_in_R s')
  thus ?case using i s'' e s' unfolding sdrop_stl t'_def sdrop_add add.commute[of n]
    trim_alt[OF s' sdrop_fair[OF Suc.prems(2)]]
    by (intro exI[of _ \<open>minWait (sdrop n rs) s' + Suc n\<close>] exI[of _ s'']) (simp add: eff_S)
qed (auto intro!: exI[of _ 0] exI[of _ s])

lemma wf_mkTree:
  assumes s: \<open>s \<in> S\<close> and \<open>fair rs\<close>
  shows \<open>wf (mkTree rs s)\<close>
using assms proof (coinduction arbitrary: rs s)
  case (wf rs s) let ?t = \<open>mkTree rs s\<close>
  have \<open>snd (root ?t) \<in> R\<close> using trim_in_R[OF wf] by simp
  moreover have \<open>fst \<circ> root \<circ> mkTree (stl (trim rs s)) = id\<close> by auto
  hence \<open>effStep (root ?t) (fimage (fst \<circ> root) (cont ?t))\<close>
    using trim_enabled[OF wf] by (simp add: pickEff)
  ultimately show ?case using fair_stl[OF trim_fair[OF wf]] in_cont_mkTree[OF wf]
    by (auto intro!: exI[of _ \<open>stl (trim rs s)\<close>])
qed


(*<*)(* The position of a rule in a rule stream *)(*>*)
definition \<open>pos rs r \<equiv> LEAST n. shd (sdrop n rs) = r\<close>

lemma pos: \<open>\<lbrakk>fair rs; r \<in> R\<rbrakk> \<Longrightarrow> shd (sdrop (pos rs r) rs) = r\<close>
  unfolding pos_def
  by (rule LeastI_ex) (metis (full_types) alw.cases fair_def holds.simps sdrop_wait)

lemma pos_least: \<open>shd (sdrop n rs) = r \<Longrightarrow> pos rs r \<le> n\<close>
  unfolding pos_def by (metis (full_types) Least_le)

lemma minWait_le_pos: \<open>\<lbrakk>fair rs; r \<in> R; enabled r s\<rbrakk> \<Longrightarrow> minWait rs s \<le> pos rs r\<close>
  by (auto simp del: sdrop_simps intro: minWait_least simp: pos)

lemma stake_pos_minWait:
  assumes rs: \<open>fair rs\<close> and m: \<open>minWait rs s < pos rs r\<close> and r: \<open>r \<in> R\<close> and s: \<open>s \<in> S\<close>
  shows \<open>pos (stl (trim rs s)) r = pos rs r - Suc (minWait rs s)\<close>
proof -
  have \<open>pos rs r - Suc (minWait rs s) + minWait rs s = pos rs r - Suc 0\<close> using m by auto
  moreover have \<open>shd (stl (sdrop (pos rs r - Suc 0) rs)) = shd (sdrop (pos rs r) rs)\<close>
    by (metis Suc_pred gr_implies_not0 m neq0_conv sdrop.simps(2) sdrop_stl)
  ultimately have \<open>pos (stl (trim rs s)) r \<le> pos rs r - Suc (minWait rs s)\<close>
    using pos[OF rs r] by (auto simp: add.commute trim_alt[OF s rs] intro: pos_least)
  moreover
  have \<open>pos rs r \<le> pos (stl (trim rs s)) r + Suc (minWait rs s)\<close>
    using pos[OF sdrop_fair[OF fair_stl[OF rs]] r, of \<open>minWait rs s\<close>]
    by (auto simp: trim_alt[OF s rs] add.commute intro: pos_least)
  hence \<open>pos rs r - Suc (minWait rs s) \<le> pos (stl (trim rs s)) r\<close> by linarith
  ultimately show ?thesis by simp
qed

lemma ipath_mkTree_ev:
  assumes s: \<open>s \<in> S\<close> and rs: \<open>fair rs\<close>
  and i: \<open>ipath (mkTree rs s) steps\<close> and r: \<open>r \<in> R\<close>
  and alw: \<open>alw (holds (enabledAtStep r)) steps\<close>
  shows \<open>ev (holds (takenAtStep r)) steps\<close>
using s rs i alw proof (induction \<open>pos rs r\<close> arbitrary: rs s steps rule: less_induct)
  case (less rs s steps) note s = \<open>s \<in> S\<close> and trim_def' = trim_alt[OF s \<open>fair rs\<close>]
  let ?t = \<open>mkTree rs s\<close>
  from less(4,3) s in_cont_mkTree obtain t' :: \<open>('state, 'rule) step tree\<close> and s' where
    rt: \<open>root ?t = shd steps\<close> and i: \<open>ipath (mkTree (stl (trim rs s)) s') (stl steps)\<close> and
    s': \<open>s' \<in> S\<close> by cases fast
  show ?case
  proof(cases \<open>pos rs r = minWait rs s\<close>)
    case True
    with pos[OF less.prems(2) r] rt[symmetric] show ?thesis by (auto simp: trim_def' ev.base)
  next
    case False
    have e: \<open>enabled r s\<close> using less.prems(4) rt  by (subst (asm) alw_nxt, cases steps) auto
    with False r less.prems(2) have 2: \<open>minWait rs s < pos rs r\<close> using minWait_le_pos by force
    let ?m1 = \<open>pos rs r - Suc (minWait rs s)\<close>
    have \<open>Suc ?m1 \<le> pos rs r\<close> using 2 by auto
    moreover have \<open>?m1 = pos (stl (trim rs s)) r\<close> using e \<open>fair rs\<close> 2 r s
      by (auto intro: stake_pos_minWait[symmetric])
    moreover have \<open>fair (stl (trim rs s))\<close> \<open>alw (holds (enabledAtStep r)) (stl steps)\<close>
      using less.prems by (metis fair_stl trim_fair, metis alw.simps)
    ultimately show \<open>?thesis\<close> by (auto intro: ev.step[OF less.hyps[OF _ s' _ i]])
  qed
qed

section\<open>Persistent rules\<close>

definition
  \<open>per r \<equiv>
    \<forall>s r1 sl' s'. s \<in> S \<and> enabled r s \<and> r1 \<in> R - {r} \<and> eff r1 s sl' \<and> s' |\<in>| sl' \<longrightarrow> enabled r s'\<close>

lemma per_alw:
  assumes p: \<open>per r\<close> and e: \<open>epath steps \<and> fst (shd steps) \<in> S\<close>
  shows \<open>alw (holds (enabledAtStep r) impl
    (holds (takenAtStep r) or nxt (holds (enabledAtStep r)))) steps\<close>
using e proof coinduct
  case (alw steps)
  moreover
  { let ?s = \<open>fst (shd steps)\<close>  let ?r1 = \<open>snd (shd steps)\<close>
    let ?s' = \<open>fst (shd (stl steps))\<close>
    assume \<open>?s \<in> S\<close> and \<open>enabled r ?s\<close> and \<open>?r1 \<noteq> r\<close>
    moreover have \<open>?r1 \<in> R\<close> using alw by (auto elim: epath.cases)
    moreover obtain sl' where \<open>eff ?r1 ?s sl' \<and> ?s' |\<in>| sl'\<close> using alw by (auto elim: epath.cases)
    ultimately have \<open>enabled r ?s'\<close> using p unfolding per_def by blast
  }
  ultimately show ?case by (auto intro: eff_S elim: epath.cases)
qed

end \<comment> \<open>context RuleSystem\<close>


(*<*) (* Rule-persistent rule system *) (*>*)
locale PersistentRuleSystem = RuleSystem eff rules S
for eff :: \<open>'rule \<Rightarrow> 'state \<Rightarrow> 'state fset \<Rightarrow> bool\<close> and rules :: \<open>'rule stream\<close> and S +
assumes per: \<open>\<And> r. r \<in> R \<Longrightarrow> per r\<close>
begin

lemma ipath_mkTree_saturated:
  assumes s: \<open>s \<in> S\<close> and rs: \<open>fair rs\<close>
  and i: \<open>ipath (mkTree rs s) steps\<close> and r: \<open>r \<in> R\<close>
  shows \<open>saturated r steps\<close>
unfolding saturated_def using s rs i proof (coinduction arbitrary: rs s steps)
  case (alw rs s steps)
  show ?case
  proof (intro exI[of _ steps], safe)
    assume \<open>holds (enabledAtStep r) steps\<close>
    hence \<open>alw (holds (enabledAtStep r)) steps \<or> ev (holds (takenAtStep r)) steps\<close>
      by (rule variance[OF _ per_alw[OF per[OF r]]])
        (metis wf_ipath_epath wf_mkTree alw mkTree.simps(1) ipath.simps fst_conv)
    thus \<open>ev (holds (takenAtStep r)) steps\<close> by (metis ipath_mkTree_ev[OF alw r])
  next
    from alw show \<open>\<exists>rs' s' steps'.
      stl steps = steps' \<and> s' \<in> S \<and> fair rs' \<and> ipath (mkTree rs' s') steps'\<close>
      using ipath_mkTree_sdrop[where m=1, simplified] trim_in_R sdrop_fair by fast
  qed
qed

theorem ipath_mkTree_Saturated:
  assumes \<open>s \<in> S\<close> and \<open>fair rs\<close> and \<open>ipath (mkTree rs s) steps\<close>
  shows \<open>Saturated steps\<close>
  unfolding Saturated_def using ipath_mkTree_saturated[OF assms] by blast

theorem epath_completeness_Saturated:
  assumes \<open>s \<in> S\<close>
  shows
  \<open>(\<exists> t. fst (root t) = s \<and> wf t \<and> tfinite t) \<or>
   (\<exists> steps. fst (shd steps) = s \<and> epath steps \<and> Saturated steps)\<close> (is \<open>?A \<or> ?B\<close>)
proof -
  { assume \<open>\<not> ?A\<close>
    with assms have \<open>\<not> tfinite (mkTree fenum s)\<close> using wf_mkTree fair_fenum by auto
    then obtain steps where \<open>ipath (mkTree fenum s) steps\<close> using Konig by blast
    with assms have \<open>fst (shd steps) = s \<and> epath steps \<and> Saturated steps\<close>
      by (metis wf_ipath_epath ipath.simps ipath_mkTree_Saturated
        wf_mkTree fair_fenum mkTree.simps(1) fst_conv)
    hence ?B by blast
  }
  thus ?thesis by blast
qed


end \<comment> \<open>context PersistentRuleSystem\<close>



section\<open>Code generation\<close>

(* Here we assume a deterministic effect eff': *)

locale RuleSystem_Code =
fixes eff' :: \<open>'rule \<Rightarrow> 'state \<Rightarrow> 'state fset option\<close>
and rules :: \<open>'rule stream\<close> \<comment> \<open>countably many rules\<close>
begin

definition \<open>eff r s sl \<equiv> eff' r s = Some sl\<close>

end (* context RuleSystem_Code *)

definition [code del]: \<open>effG eff' r s sl \<equiv> RuleSystem_Code.eff eff' r s sl\<close>

sublocale RuleSystem_Code < RuleSystem_Defs
  where eff = \<open>effG eff'\<close> and rules = rules .

context RuleSystem_Code
begin

lemma enabled_eff': \<open>enabled r s \<longleftrightarrow> eff' r s \<noteq> None\<close>
unfolding enabled_def effG_def eff_def by auto

lemma pickEff_the[code]: \<open>pickEff r s = the (eff' r s)\<close>
unfolding pickEff_def enabled_def effG_def eff_def by auto

lemmas [code_unfold] = trim_def enabled_eff' pickEff_the

(*<*)
end (* context RuleSystem_Code *)
(*>*)

setup Locale_Code.open_block
interpretation i: RuleSystem_Code eff' rules for eff' and rules .
declare [[lc_delete \<open>RuleSystem_Defs.mkTree (effG ?eff')\<close>]]
declare [[lc_delete RuleSystem_Defs.trim]]
declare [[lc_delete RuleSystem_Defs.enabled]]
declare [[lc_delete RuleSystem_Defs.pickEff]]
declare [[lc_add \<open>RuleSystem_Defs.mkTree (effG ?eff')\<close> i.mkTree_unfold]]
setup Locale_Code.close_block

code_printing
  constant the \<rightharpoonup> (Haskell) "fromJust"
| constant Option.is_none \<rightharpoonup> (Haskell) "isNothing"

export_code mkTree_effG_uu in Haskell module_name Tree (*file \<open>.\<close>*)

(*<*)
end
(*>*)
