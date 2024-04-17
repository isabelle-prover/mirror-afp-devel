(*<*)
theory Local_State
imports
  Programs
begin

lemmas trace_steps'_map =
  trace.steps'.map(1)[where af=id and sf="Pair (fst (trace.final' (ls, s) xs))" and s="snd (trace.final' (ls, s) xs)", simplified]
  trace.steps'.map(1)[where af=id and sf="Pair x"]
    for ls s xs x

lemma trace_steps'_snd_le_const:
  assumes "trace.steps' (ls, s) xs \<subseteq> {(a, (ls', s'), (ls'', s'))}"
  shows "(\<lambda>x. snd (snd x)) ` set xs \<subseteq> {s}"
using subset_singletonD[OF assms] by (force simp: trace.steps'.step_conv image_subset_iff)

lemma trace_natural'_took_step_shared_changes:
  assumes "trace.steps' (ls, s) xs \<subseteq> {(a, (ls'', s''), (ls''', s'''))}"
  assumes "trace.final' (ls, s) xs = (ls', s')"
  assumes "s \<noteq> s'"
  shows "trace.natural' s (map (map_prod id snd) xs) = [(a, s')]"
using subset_singletonD[OF assms(1)] assms(2-)
by (auto simp: trace.steps'.step_conv trace.natural'.append trace.natural'.eq_Nil_conv
               image_subset_iff append_eq_Cons_conv)

lemma trace_natural'_took_step_shared_same:
  assumes "trace.steps' (ls, s) xs \<subseteq> {(a, (ls'', s'), (ls''', s'))}"
  assumes "alss \<in> set xs"
  shows "snd (snd alss) = s"
using subset_singletonD[OF assms(1)] assms(2)
by (fastforce simp: trace.steps'.step_conv image_subset_iff)

(*>*)
section\<open> Structural local state\label{sec:local_state} \<close>

subsection\<open> \<^emph>\<open>spec.local\<close>\label{sec:local_state-spec_local} \<close>

text\<open>

We develop a few combinators for structural local state. The goal is to encapsulate a local state
of type \<^typ>\<open>'ls\<close> in a process \<^typ>\<open>('a agent, 'ls \<times> 's, 'v) spec\<close>. Applying \<^term>\<open>spec.smap snd\<close>
yields a process of type \<^typ>\<open>('a agent, 's, 'v) spec\<close>. We also constrain environment steps
to not affect \<^typ>\<open>'ls\<close>, yielding a plausible data refinement rule
(see \S\ref{sec:local_state-data_refinement}).

\<close>

\<comment>\<open> Lift a predicate on the shared state \<close>
abbreviation (input) localize1 :: "('b \<Rightarrow> 's \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'ls \<times> 's \<Rightarrow> 'a" where
  "localize1 f b s \<equiv> f b (snd s)"

setup \<open>Sign.mandatory_path "spec"\<close>

setup \<open>Sign.mandatory_path "local"\<close>

definition qrm :: "('a agent, 'ls \<times> 's) steps" where \<comment>\<open> cf \<^const>\<open>ag.assm\<close> \<close>
  "qrm = range proc \<times> UNIV \<union> {env} \<times> (Id \<times>\<^sub>R UNIV)"

abbreviation (input) "interference \<equiv> spec.rel spec.local.qrm"

setup \<open>Sign.parent_path\<close>

definition local :: "('a agent, 'ls \<times> 's, 'v) spec \<Rightarrow> ('a agent, 's, 'v) spec" where
  "local P = spec.smap snd (spec.local.interference \<sqinter> P)"

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma local_le_conv:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.local P
         \<longleftrightarrow> (\<exists>\<sigma>'. \<lblot>\<sigma>'\<rblot> \<le> P
                 \<and> trace.steps \<sigma>' \<subseteq> spec.local.qrm
                 \<and> \<lblot>\<sigma>\<rblot> \<le> \<lblot>trace.map id snd id \<sigma>'\<rblot>)"
by (simp add: spec.local_def spec.singleton.le_conv ac_simps)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "idle"\<close>

lemma local_le[spec.idle_le]: \<comment>\<open> Converse does not hold \<close>
  assumes "spec.idle \<le> P"
  shows "spec.idle \<le> spec.local P"
by (simp add: spec.local_def assms spec.idle_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "local"\<close>

setup \<open>Sign.mandatory_path "qrm"\<close>

lemma refl:
  shows "refl (spec.local.qrm `` {a})"
by (simp add: spec.local.qrm_def refl_onI)

lemma member:
  shows "(proc a, s, s') \<in> spec.local.qrm"
    and "(env, s, s') \<in> spec.local.qrm \<longleftrightarrow> fst s = fst s'"
by (auto simp: spec.local.qrm_def)

lemma inter:
  shows "UNIV \<times> Id \<inter> spec.local.qrm = UNIV \<times> Id"
    and "spec.local.qrm \<inter> UNIV \<times> Id = UNIV \<times> Id"
    and "spec.local.qrm \<inter> {self} \<times> Id = {self} \<times> Id"
    and "spec.local.qrm \<inter> {env} \<times> UNIV = {env} \<times> (Id \<times>\<^sub>R UNIV)"
    and "spec.local.qrm \<inter> {env} \<times> (UNIV \<times>\<^sub>R Id) = {env} \<times> Id"
    and "spec.local.qrm \<inter> A \<times> (Id \<times>\<^sub>R r) = A \<times> (Id \<times>\<^sub>R r)"
by (auto simp: spec.local.qrm_def)

lemmas simps[simp] =
  spec.local.qrm.refl
  spec.local.qrm.member
  spec.local.qrm.inter

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "interference"\<close>

lemma smap_snd:
  shows "spec.smap snd spec.local.interference = \<top>"
by (subst spec.map.rel)
   (auto simp: spec.local.qrm_def spec.rel.UNIV
               image_Un map_prod_image_Times map_prod_image_relprod map_prod_surj
    simp flip: Sigma_Un_distrib1)

setup \<open>Sign.parent_path\<close>

lemma inf_interference:
  shows "spec.local P = spec.local (P \<sqinter> spec.local.interference)"
by (simp add: spec.local_def ac_simps)

lemma bot:
  shows "spec.local \<bottom> = \<bottom>"
by (simp add: spec.local_def spec.map.bot)

lemma top:
  shows "spec.local \<top> = \<top>"
by (simp add: spec.local_def spec.local.interference.smap_snd)

lemma monotone:
  shows "mono spec.local"
proof(rule monotoneI)
  show "spec.local P \<le> spec.local P'" if "P \<le> P'" for P P' :: "('a agent, 's \<times> 'ls, 'v) spec"
    unfolding spec.local_def by (strengthen ord_to_strengthen(1)[OF \<open>P \<le> P'\<close>]) simp
qed

lemmas strengthen[strg] = st_monotone[OF spec.local.monotone]
lemmas mono = monotoneD[OF spec.local.monotone]
lemmas mono2mono[cont_intro, partial_function_mono]
  = monotone2monotone[OF spec.local.monotone, simplified, of orda P for orda P]

lemma Sup:
  shows "spec.local (\<Squnion>X) = (\<Squnion>x\<in>X. spec.local x)"
by (simp add: spec.local_def inf_Sup spec.map.Sup image_image)

lemmas sup = spec.local.Sup[where X="{X, Y}" for X Y, simplified]

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) P"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. spec.local (P x))"
by (simp add: spec.local_def assms)

lemma idle:
  shows "spec.local spec.idle = spec.idle"
by (simp add: spec.local_def inf.absorb2[OF spec.idle.rel_le] spec.map.idle)

lemma action:
  fixes F :: "('v \<times> 'a agent \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  shows "spec.local (spec.action F)
       = spec.action (map_prod id (map_prod id (map_prod snd snd)) `
                                  (F \<inter> UNIV \<times> spec.local.qrm))"
by (simp add: spec.local_def spec.action.inf_rel spec.map.surj_sf_action)

lemma return:
  shows "spec.local (spec.return v) = spec.return v"
by (simp add: spec.return_def spec.local.action
              Times_Int_Times map_prod_image_Times map_prod_snd_snd_image_Id)

lemma bind_le: \<comment>\<open> Converse does not hold \<close>
  shows "spec.local (f \<bind> g) \<le> spec.local f \<bind> (\<lambda>v. spec.local (g v))"
by (simp add: spec.local_def spec.bind.inf_rel spec.map.bind_le)

lemma interference:
  shows "spec.local (spec.rel ({env} \<times> UNIV)) = spec.rel ({env} \<times> UNIV)"
by (simp add: spec.local_def spec.map.rel map_prod_image_Times map_prod_image_relprod
        flip: spec.rel.inf)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "map"\<close>

lemma local_le:
  shows "spec.map id sf vf (spec.local P) \<le> spec.local (spec.map id (map_prod id sf) vf P)"
by (fastforce intro: spec.map.mono inf.mono spec.rel.mono
               simp: spec.local_def spec.map.comp spec.map.inf_rel spec.local.qrm_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "vmap"\<close>

lemma local:
  shows "spec.vmap vf (spec.local P) = spec.local (spec.vmap vf P)"
by (simp add: spec.local_def spec.map.comp spec.map.inf_rel spec.rel.reflcl(1)[where A=UNIV])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "invmap"\<close>

lemma smap_snd:
  fixes P :: "('a, 'ls \<times> 't, 'w) spec"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  shows "spec.invmap id sf vf (spec.smap snd P)
       = spec.smap snd (spec.invmap id (map_prod id sf) vf P)" (is "?lhs = ?rhs")
proof(rule spec.singleton.antisym)
  have smap_snd_aux:
    "\<exists>zs. trace.natural' (ls, sf s) xs = trace.natural' (ls, sf s) (map (map_prod id (map_prod id sf)) zs)
        \<and> trace.natural' s (map (map_prod id snd) zs) = trace.natural' s ys" (is "\<exists>zs. ?P ls s ys zs")
    if "trace.natural' (sf s) (map (map_prod id sf) ys) = trace.natural' (sf s) (map (map_prod id snd) xs)"
   for ls and s :: "'s" and sf :: "'s \<Rightarrow> 't" and xs :: "('a \<times> 'ls \<times> 't) list" and ys :: "('a \<times> 's) list"
    using that
  proof(induct xs arbitrary: ls s ys)
    case (Nil ls s ys) then show ?case
      by (fastforce intro: exI[where x="map (map_prod id (Pair ls)) ys"]
                     simp: comp_def trace.natural'.eq_Nil_conv)
  next
    case (Cons x xs ls s ys) show ?case
    proof(cases "snd (snd x) = sf s")
      case True with Cons.prems show ?thesis
        by (cases x) (fastforce dest: Cons.hyps[where ls="fst (snd x)"]
                               intro: exI[where x="(fst x, fst (snd x), s) # zs" for zs]
                           simp flip: id_def)
    next
      case False
      with Cons.prems obtain a s\<^sub>x us s' zs
        where "x = (a, s\<^sub>x, sf s')"
        and "sf s' \<noteq> sf s"
        and "snd ` map_prod id sf ` set us \<subseteq> {sf s}"
        and "ys = us @ (a, s') # zs"
        and "trace.natural' (sf s') (map (map_prod id sf) zs) = trace.natural' (sf s') (map (map_prod id snd) xs)"
        by (cases x) (clarsimp simp: trace.natural'.eq_Cons_conv map_eq_append_conv simp flip: id_def)
      with False show ?thesis
        by (fastforce simp: comp_def trace.natural'.append image_subset_iff trace.natural'.eq_Nil_conv
                     intro: exI[where x="map (map_prod id (Pair ls)) us @ (a, (s\<^sub>x, s')) # zs" for zs]
                      dest: Cons.hyps[where ls="fst (snd x)"])
    qed
  qed
  fix \<sigma>
  assume "\<lblot>\<sigma>\<rblot> \<le> ?lhs"
  then obtain ls xs v i
    where *: "\<lblot>(ls, sf (trace.init \<sigma>)), xs, v\<rblot> \<le> P"
      and **: "trace.natural' (sf (trace.init \<sigma>)) (map (map_prod id sf) (trace.rest \<sigma>))
             = trace.natural' (sf (trace.init \<sigma>)) (map (map_prod id snd) (take i xs))"
      and ***: "if i \<le> length xs then trace.term \<sigma> = None else map_option vf (trace.term \<sigma>) = v"
    apply (clarsimp simp: spec.singleton.le_conv spec.singleton_le_conv)
    apply (erule trace.less_eq_takeE)
    apply (erule trace.take.naturalE)
    apply (clarsimp simp: trace.take.map trace.natural_def trace.split_all not_le
                   split: if_split_asm)
    apply (metis order.strict_iff_not take_all)
    done
  from smap_snd_aux[OF **] obtain zs
    where "trace.natural' (ls, sf (trace.init \<sigma>)) (take i xs)
         = trace.natural' (ls, sf (trace.init \<sigma>)) (map (map_prod id (map_prod id sf)) zs)"
      and "trace.natural' (trace.init \<sigma>) (map (map_prod id snd) zs)
         = trace.natural' (trace.init \<sigma>) (trace.rest \<sigma>)"
    by blast
  with * *** show "\<lblot>\<sigma>\<rblot> \<le> ?rhs"
    apply -
    unfolding spec.singleton.le_conv
    apply (rule exI[where x="trace.T (ls, trace.init \<sigma>) zs (if i \<le> length xs then None else trace.term \<sigma>)"])
    apply (clarsimp simp: spec.singleton_le_conv trace.natural_def trace.less_eq_None
                   split: if_splits
                   elim!: order.trans[rotated])
    apply (metis append_take_drop_id prefixI trace.natural'.append)
    done
next
  show "\<lblot>\<sigma>\<rblot> \<le> ?lhs" if "\<lblot>\<sigma>\<rblot> \<le> ?rhs" for \<sigma>
    using that
    by (fastforce dest: spec.singleton.map_le[where af=id and sf=sf and vf=vf]
                  simp: spec.singleton.le_conv)
qed

lemma local:
  fixes P :: "('a agent, 'ls \<times> 't, 'v) spec"
  fixes sf :: "'s \<Rightarrow> 't"
  shows "spec.invmap id sf vf (spec.local P) = spec.local (spec.invmap id (map_prod id sf) vf P)"
by (auto simp: spec.local_def spec.local.qrm_def ac_simps
               spec.invmap.smap_snd spec.invmap.inf spec.invmap.rel
  intro!: arg_cong[where f="\<lambda>r. spec.smap snd (spec.invmap id (map_prod id sf) vf P \<sqinter> spec.rel r)"])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term"\<close>

setup \<open>Sign.mandatory_path "none"\<close>

lemma local:
  shows "spec.term.none (spec.local P) = spec.local (spec.term.none P)"
by (simp add: spec.local_def spec.term.none.inf spec.term.none.inf_none_rel spec.term.none.map)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "all"\<close>

lemma local:
  shows "spec.term.all (spec.local P) = spec.local (spec.term.all P)"
by (simp add: spec.local_def spec.term.all.map spec.term.all.rel spec.term.all.inf)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "closed"\<close>

lemma local:
  assumes "P \<in> spec.term.closed _"
  shows "spec.local P \<in> spec.term.closed _"
by (rule spec.term.closed_clI)
   (simp add: spec.term.all.local spec.term.all.monomorphic
        flip: spec.term.closed_conv[OF assms, simplified])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Local state transformations\label{sec:local_state-transformations} \<close>

text\<open>

We want to reorder, introduce and eliminate actions that affect local state while preserving
observable behaviour under \<^const>\<open>spec.local\<close>.

The closure that arises from \<^const>\<open>spec.local\<close>, i.e.:

\<close>

lemma
  defines "cl \<equiv> spec.map_invmap.cl _ _ _ id snd id"
  assumes "spec.local.interference \<sqinter> P
        \<le> cl (spec.local.interference \<sqinter> Q)"
  shows "spec.local P \<le> spec.local Q"
unfolding spec.local_def
by (strengthen ord_to_strengthen(1)[OF assms(2)])
   (simp add: spec.map_invmap.galois cl_def spec.map_invmap.cl_def)

text\<open>

expresses all transformations, but does not decompose over \<^const>\<open>spec.bind\<close>; in other
words we do not have \<open>cl f \<bind> (\<lambda>v. cl (g v)) \<le> cl (f \<bind> g)\<close> as the
local states that \<open>cl f\<close> terminates with may not satisfy \<open>g\<close>. (Observe that we do not expect the
converse to hold as then all local states would need to be preserved.)

We therefore define a closure that preserves the observable state and
the initial and optionally final (if terminating) local states via a projection:

\<close>

setup \<open>Sign.mandatory_path "seq_ctxt"\<close>

definition prj :: "bool \<Rightarrow> ('a, 'ls \<times> 's, 'v) trace.t \<Rightarrow> ('a, 's, 'v) trace.t \<times> 'ls \<times> 'ls option" where
  "prj T \<sigma> = (\<natural>(trace.map id snd id \<sigma>),
                fst (trace.init \<sigma>),
                if T then map_option \<langle>fst (trace.final \<sigma>)\<rangle> (trace.term \<sigma>) else None)"

setup \<open>Sign.mandatory_path "prj"\<close>

lemma natural:
  shows "seq_ctxt.prj T (\<natural>\<sigma>) = seq_ctxt.prj T \<sigma>"
by (simp add: seq_ctxt.prj_def trace.natural.map_natural)

lemma idle:
  shows "seq_ctxt.prj T (trace.T s [] None) = (trace.T (snd s) [] None, fst s, None)"
by (simp add: seq_ctxt.prj_def trace.natural.simps)

lemmas simps[simp] =
  seq_ctxt.prj.natural

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

interpretation seq_ctxt: galois.image_vimage "seq_ctxt.prj T" for T .

setup \<open>Sign.mandatory_path "seq_ctxt.equivalent"\<close>

lemma partial_sel_equivE:
  assumes "seq_ctxt.equivalent T \<sigma>\<^sub>1 \<sigma>\<^sub>2"
  obtains "trace.init \<sigma>\<^sub>1 = trace.init \<sigma>\<^sub>2"
      and "trace.term \<sigma>\<^sub>1 = trace.term \<sigma>\<^sub>2"
      and "\<lbrakk>T; \<exists>v. trace.term \<sigma>\<^sub>1 = Some v\<rbrakk> \<Longrightarrow> trace.final \<sigma>\<^sub>1 = trace.final \<sigma>\<^sub>2"
using assms
by (cases \<sigma>\<^sub>1)
   (force intro: prod_eqI
           simp: seq_ctxt.prj_def trace.natural.trace_conv
      simp flip: trace.final'.map[where af=id and sf=snd]
           cong: trace.final'.natural'_cong)

lemma downwards_existsE:
  assumes "\<sigma>\<^sub>1' \<le> \<sigma>\<^sub>1"
  assumes "seq_ctxt.equivalent T \<sigma>\<^sub>1 \<sigma>\<^sub>2"
  obtains \<sigma>\<^sub>2'
    where "\<sigma>\<^sub>2' \<le> \<sigma>\<^sub>2"
      and "seq_ctxt.equivalent T \<sigma>\<^sub>1' \<sigma>\<^sub>2'"
using assms
apply atomize_elim
apply (clarsimp simp: seq_ctxt.prj_def)
apply (rule trace.natural.less_eqE[OF trace.map.mono sym], assumption, assumption)
apply (clarsimp split: if_split_asm)
 apply (cases "trace.term \<sigma>\<^sub>1'")
  apply (fastforce simp: trace.natural_def elim: trace.less_eqE trace.map.less_eqR)+
done

lemma downwards_existsE2:
  assumes "\<sigma>\<^sub>1' \<le> \<sigma>\<^sub>1"
  assumes "seq_ctxt.equivalent T \<sigma>\<^sub>1' \<sigma>\<^sub>2'"
  obtains \<sigma>\<^sub>2
    where "\<sigma>\<^sub>2' \<le> \<sigma>\<^sub>2"
      and "seq_ctxt.equivalent T \<sigma>\<^sub>1 \<sigma>\<^sub>2"
proof(atomize_elim, use \<open>\<sigma>\<^sub>1' \<le> \<sigma>\<^sub>1\<close> in \<open>induct rule: trace.less_eqE\<close>)
  case prefix
  from prefix(3) obtain zs
    where *: "\<sigma>\<^sub>1 = trace.T (trace.init \<sigma>\<^sub>1) (trace.rest \<sigma>\<^sub>1' @ zs) (trace.term \<sigma>\<^sub>1)"
    by (cases \<sigma>\<^sub>1) (auto elim: prefixE)
  show ?case
  proof(cases "trace.term \<sigma>\<^sub>1")
    case None with assms(2) prefix(1,2) * show ?thesis
      by (cases \<sigma>\<^sub>1, cases \<sigma>\<^sub>2')
         (fastforce intro!: exI[where x="trace.T (trace.init \<sigma>\<^sub>1) (trace.rest \<sigma>\<^sub>2' @ zs) (trace.term \<sigma>\<^sub>1)"]
                      simp: seq_ctxt.prj_def trace.natural_def
                            trace.natural'.append trace.less_eq_same_append_conv
                      cong: trace.final'.natural'_cong)
  next
    case (Some v)
    from assms(2) prefix(2)
    have "snd (trace.final \<sigma>\<^sub>1') = trace.final (trace.map id snd id \<sigma>\<^sub>2')"
      by (cases \<sigma>\<^sub>1', cases \<sigma>\<^sub>2')
         (clarsimp simp: seq_ctxt.prj_def trace.natural_def trace.final'.map
                  dest!: arg_cong[where f="\<lambda>xs. trace.final' (snd (trace.init \<sigma>\<^sub>1)) xs"])
    with Some assms(2) prefix(1,2) * show ?thesis
      apply (cases \<sigma>\<^sub>1)
      apply (cases \<sigma>\<^sub>2')
      apply (rule exI[where x="trace.T (trace.init \<sigma>\<^sub>1) (trace.rest \<sigma>\<^sub>2' @ (undefined, trace.final \<sigma>\<^sub>1') # zs) (trace.term \<sigma>\<^sub>1)"])
      apply (clarsimp simp: seq_ctxt.prj_def trace.natural_def trace.natural'.append trace.less_eq_same_append_conv)
      apply (clarsimp cong: trace.final'.natural'_cong)
      done
  qed
next
  case (maximal v) with assms(2) show ?case
    by blast
qed

lemma map_sf_eq_id:
  assumes "seq_ctxt.equivalent True \<sigma>\<^sub>1 \<sigma>\<^sub>2"
  shows "seq_ctxt.equivalent True (trace.map af id vf \<sigma>\<^sub>1) (trace.map af id vf \<sigma>\<^sub>2)"
using assms
by (auto simp: seq_ctxt.prj_def comp_def trace.final'.map[where sf=id, simplified] trace.natural_def
    simp flip: trace.natural'.map_inj_on_sf
         dest: arg_cong[where f="map (map_prod af id)"])

lemma mono:
  assumes "T \<Longrightarrow> T'"
  assumes "seq_ctxt.equivalent T' \<sigma>\<^sub>1 \<sigma>\<^sub>2"
  shows "seq_ctxt.equivalent T \<sigma>\<^sub>1 \<sigma>\<^sub>2"
using assms by (clarsimp simp: seq_ctxt.prj_def)

lemma append:
  assumes "seq_ctxt.equivalent True (trace.T s xs (Some v)) (trace.T s' xs' v')"
  assumes "seq_ctxt.equivalent T (trace.T (trace.final' s xs) ys w) (trace.T t' ys' w')"
  shows "seq_ctxt.equivalent T (trace.T s (xs @ ys) w) (trace.T s' (xs' @ ys') w')"
using assms
by (clarsimp simp: seq_ctxt.prj_def trace.natural_def trace.natural'.append
        simp flip: trace.final'.map[where af=id and sf=snd]
             cong: trace.final'.natural'_cong if_cong)
  (simp; metis trace.final'.map[where af=id and sf=fst])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

setup \<open>Sign.mandatory_path "seq_ctxt"\<close>

definition cl :: "bool \<Rightarrow> ('a, 'ls \<times> 's, 'v) spec \<Rightarrow> ('a, 'ls \<times> 's, 'v) spec" where
  "cl T P = \<Squnion>(spec.singleton ` {\<sigma>\<^sub>1. \<exists>\<sigma>\<^sub>2. \<lblot>\<sigma>\<^sub>2\<rblot> \<le> P \<and> seq_ctxt.equivalent T \<sigma>\<^sub>1 \<sigma>\<^sub>2})"

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "singleton.seq_ctxt"\<close>

lemma cl_le_conv[spec.singleton.le_conv]:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.seq_ctxt.cl T P \<longleftrightarrow> (\<exists>\<sigma>'. \<lblot>\<sigma>'\<rblot> \<le> P \<and> seq_ctxt.equivalent T \<sigma> \<sigma>')" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (clarsimp simp: spec.seq_ctxt.cl_def spec.singleton_le_conv)
       (force elim: seq_ctxt.equivalent.downwards_existsE[where T=T]
              dest: order.trans[OF spec.singleton.mono])
  show "?rhs \<Longrightarrow> ?lhs"
    unfolding spec.seq_ctxt.cl_def spec.singleton_le_conv by blast
qed

setup \<open>Sign.parent_path\<close>

interpretation seq_ctxt: closure_complete_distrib_lattice_distributive_class "spec.seq_ctxt.cl T" for F
proof standard
  show "P \<le> spec.seq_ctxt.cl T Q \<longleftrightarrow> spec.seq_ctxt.cl T P \<le> spec.seq_ctxt.cl T Q" (is "?lhs \<longleftrightarrow> ?rhs")
    for P Q :: "('a, 'ls \<times> 's, 'v) spec"
  proof(rule iffI)
    show "?lhs \<Longrightarrow> ?rhs"
      by (rule spec.singleton_le_extI)
         (force simp: spec.singleton.seq_ctxt.cl_le_conv dest: order.trans[rotated])
    show "?rhs \<Longrightarrow> ?lhs"
      by (metis spec.singleton.seq_ctxt.cl_le_conv spec.singleton_le_ext_conv)
  qed
  show "spec.seq_ctxt.cl T (\<Squnion> X) \<le> \<Squnion> (spec.seq_ctxt.cl T ` X) \<squnion> spec.seq_ctxt.cl T \<bottom>"
    for X :: "('a, 'ls \<times> 's, 'v) spec set"
    by (auto simp: spec.seq_ctxt.cl_def)
qed

setup \<open>Sign.mandatory_path "idle.seq_ctxt"\<close>

lemma cl_le_conv[spec.idle_le]:
  shows "spec.idle \<le> spec.seq_ctxt.cl T P \<longleftrightarrow> spec.idle \<le> P" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI[OF _ order.trans[OF _ spec.seq_ctxt.expansive]])
  show "?lhs \<Longrightarrow> ?rhs"
    by (clarsimp simp: spec.idle_def spec.singleton.le_conv)
       (metis "trace.take.0" seq_ctxt.equivalent.partial_sel_equivE spec.singleton.takeI trace.t.sel(1))
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "seq_ctxt.cl"\<close>

lemma bot[simp]:
  shows "spec.seq_ctxt.cl T \<bottom> = \<bottom>"
by (simp add: spec.seq_ctxt.cl_def spec.singleton.not_bot)

lemma mono:
  assumes "T' \<Longrightarrow> T"
  assumes "P \<le> P'"
  shows "spec.seq_ctxt.cl T P \<le> spec.seq_ctxt.cl T' P'"
unfolding spec.seq_ctxt.cl_def
by (strengthen ord_to_strengthen(1)[OF \<open>P \<le> P'\<close>])
   (blast intro: seq_ctxt.equivalent.mono[OF assms(1)])

lemma strengthen[strg]:
  assumes "st_ord (\<not> F) T T'"
  assumes "st_ord F P P'"
  shows "st_ord F (spec.seq_ctxt.cl T P) (spec.seq_ctxt.cl T' P')"
using assms by (cases F; simp add: spec.seq_ctxt.cl.mono le_bool_def)

lemma Sup:
  shows "spec.seq_ctxt.cl T (\<Squnion>X) = \<Squnion>(spec.seq_ctxt.cl T ` X)"
by (simp add: spec.seq_ctxt.cl_Sup)

lemmas sup = spec.seq_ctxt.cl.Sup[where X="{P, Q}" for P Q, simplified]

lemma singleton:
  shows "spec.seq_ctxt.cl T \<lblot>\<sigma>\<rblot> = \<Squnion>(spec.singleton ` {\<sigma>'. seq_ctxt.equivalent T \<sigma> \<sigma>'})" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (clarsimp simp: spec.seq_ctxt.cl_def spec.singleton_le_conv)
       (metis seq_ctxt.equivalent.downwards_existsE2 seq_ctxt.prj.natural trace.natural.mono)
  show "?rhs \<le> ?lhs"
    by (fastforce simp: spec.seq_ctxt.cl_def)
qed

lemma idle: \<comment>\<open> not \<open>simp\<close> friendly \<close>
  shows "spec.seq_ctxt.cl T (spec.idle :: ('a, 'ls \<times> 's, 'v) spec)
       = spec.term.none (spec.rel (UNIV \<times> (UNIV \<times>\<^sub>R Id)) :: ('a, 'ls \<times> 's, 'w) spec)" (is "?lhs = ?rhs")
proof(rule spec.singleton.antisym)
  have *: "s = s'"
    if "snd ` set xs \<subseteq> {(ls\<^sub>0, s\<^sub>0)}"
   and "trace.natural' s\<^sub>0 (map (map_prod id snd) ys) = trace.natural' s\<^sub>0 (map (map_prod id snd) xs)"
   and "(a, (ls, s), ls', s') \<in> trace.steps' (ls\<^sub>0, s\<^sub>0) ys"
   for xs ys :: "('a \<times> ('ls \<times> 's)) list" and ls\<^sub>0 s\<^sub>0 a ls s ls' and s'
    using that
  proof(induct ys rule: rev_induct)
    case snoc from snoc.prems show ?case
      by (auto simp: trace.natural'.append trace.steps'.append split_pairs
                     trace.final'.map[where s="(ls\<^sub>0, s\<^sub>0)" and sf=snd, simplified]
                     trace.natural'.map_natural'[where sf=snd and s="(ls\<^sub>0, s\<^sub>0)", simplified]
          simp flip: id_def trace.natural'.eq_Nil_conv
              split: if_split_asm
               dest: arg_cong[where f="\<lambda>xs. trace.natural' s\<^sub>0 (map (map_prod id snd) xs)"]
              intro: snoc.hyps[OF snoc.prems(1)])
  qed simp
  show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
    using that
    by (cases \<sigma>)
       (clarsimp simp: spec.singleton.le_conv * trace.split_all seq_ctxt.prj_def trace.natural_def)
  have *: "s' = snd s"
    if "trace.steps' s xs \<subseteq> UNIV \<times> (UNIV \<times>\<^sub>R Id)"
   and "(a, (ls', s')) \<in> set xs"
   for a s ls' s' and xs :: "('a \<times> ('ls \<times> 's)) list"
    using that by (induct xs arbitrary: s) (auto simp: trace.steps'.Cons_eq_if split: if_splits)
  show "\<lblot>\<sigma>\<rblot> \<le> ?lhs" if "\<lblot>\<sigma>\<rblot> \<le> ?rhs" for \<sigma>
    using that
    by (cases "trace.init \<sigma>")
       (fastforce simp: spec.singleton.le_conv seq_ctxt.prj_def trace.natural_def map_prod.comp
                  dest: *
                 intro: exI[where x="trace.map id (map_prod \<langle>fst (trace.init \<sigma>)\<rangle> id) id \<sigma>"])
qed

lemma invmap_le:
  shows "spec.seq_ctxt.cl True (spec.invmap af id vf P) \<le> spec.invmap af id vf (spec.seq_ctxt.cl True P)"
by (rule spec.singleton_le_extI)
   (auto simp: spec.singleton.le_conv dest: seq_ctxt.equivalent.map_sf_eq_id)

lemma map_le:
  shows "spec.map af id vf (spec.seq_ctxt.cl True P) \<le> spec.seq_ctxt.cl True (spec.map af id vf P)"
by (rule spec.singleton_le_extI)
   (clarsimp simp: spec.singleton.le_conv
            dest!: seq_ctxt.equivalent.map_sf_eq_id[where af=af and vf=vf];
    meson order.refl order.trans spec.singleton.seq_ctxt.cl_le_conv)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term.none.seq_ctxt"\<close>

lemma cl:
  shows "spec.term.none (spec.seq_ctxt.cl T P) = spec.seq_ctxt.cl T (spec.term.none P)"
by (rule spec.singleton.antisym)
   (auto simp: spec.singleton.le_conv seq_ctxt.prj_def trace.split_Ex trace.natural_def)

lemma cl_True_False:
  shows "spec.seq_ctxt.cl True (spec.term.none f) = spec.seq_ctxt.cl False (spec.term.none f)"
by (rule spec.singleton.antisym)
   (auto simp: spec.singleton.le_conv seq_ctxt.prj_def trace.split_Ex trace.natural_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term.all.seq_ctxt"\<close>

lemma cl_le:
  shows "spec.seq_ctxt.cl T (spec.term.all P) \<le> spec.term.all (spec.seq_ctxt.cl T P)"
by (metis spec.seq_ctxt.mono_cl spec.term.galois spec.term.lower_upper_contractive spec.term.none.seq_ctxt.cl)

lemma cl_False:
  shows "spec.seq_ctxt.cl False (spec.term.all P) = spec.term.all (spec.seq_ctxt.cl False P)"
by (rule spec.singleton.antisym)
   (auto simp: spec.singleton.le_conv seq_ctxt.prj_def trace.split_Ex trace.natural_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "bind.seq_ctxt"\<close>

lemma cl_le:
  shows "spec.seq_ctxt.cl True f \<bind> (\<lambda>v. spec.seq_ctxt.cl T (g v)) \<le> spec.seq_ctxt.cl T (f \<bind> g)"
proof(induct rule: spec.bind_le)
  case incomplete show ?case
    by (simp add: spec.seq_ctxt.cl.mono spec.term.none.seq_ctxt.cl)
next
  case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v)
  then obtain \<sigma>\<^sub>f' \<sigma>\<^sub>g'
    where *: "\<lblot>\<sigma>\<^sub>f'\<rblot> \<le> f" "seq_ctxt.equivalent True \<sigma>\<^sub>f \<sigma>\<^sub>f'"
             "\<lblot>\<sigma>\<^sub>g'\<rblot> \<le> g v" "seq_ctxt.equivalent T \<sigma>\<^sub>g \<sigma>\<^sub>g'"
    by (clarsimp simp: spec.singleton.seq_ctxt.cl_le_conv)
  let ?\<sigma> = "trace.T (trace.init \<sigma>\<^sub>f') (trace.rest \<sigma>\<^sub>f' @ trace.rest \<sigma>\<^sub>g') (trace.term \<sigma>\<^sub>g')"
  from continue(2,3) *
  have "\<lblot>?\<sigma>\<rblot> \<le> f \<bind> g"
   by (cases \<sigma>\<^sub>f', cases \<sigma>\<^sub>g')
      (fastforce intro: spec.bind.continueI[where v=v]  elim: seq_ctxt.equivalent.partial_sel_equivE)
  moreover
  from continue(2,3) *(2,4)
  have "seq_ctxt.equivalent T (trace.T (trace.init \<sigma>\<^sub>f) (trace.rest \<sigma>\<^sub>f @ trace.rest \<sigma>\<^sub>g) (trace.term \<sigma>\<^sub>g)) ?\<sigma>"
    by (cases \<sigma>\<^sub>f, cases \<sigma>\<^sub>g, cases \<sigma>\<^sub>f', cases \<sigma>\<^sub>g') (auto intro: seq_ctxt.equivalent.append)
  ultimately show ?case
    by (auto simp: spec.singleton.seq_ctxt.cl_le_conv)
qed

lemma clL_le:
  shows "spec.seq_ctxt.cl True f \<bind> g \<le> spec.seq_ctxt.cl T (f \<bind> g)"
by (strengthen ord_to_strengthen(2)[OF spec.bind.seq_ctxt.cl_le])
   (rule spec.bind.mono[OF order.refl spec.seq_ctxt.expansive])

lemma clR_le:
  shows "f \<bind> (\<lambda>v. spec.seq_ctxt.cl T (g v)) \<le> spec.seq_ctxt.cl T (f \<bind> g)"
by (strengthen ord_to_strengthen(2)[OF spec.bind.seq_ctxt.cl_le])
   (rule spec.bind.mono[OF spec.seq_ctxt.expansive order.refl])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "seq_ctxt"\<close>

lemma cl_local_le: \<comment>\<open> the RHS is the closure that arises from \<^const>\<open>spec.local\<close>, ignoring the constraint \<close>
  shows "spec.seq_ctxt.cl T P \<le> spec.map_invmap.cl _ _ _ id snd id P"
by (fastforce simp: spec.map_invmap.cl_def spec.seq_ctxt.cl_def seq_ctxt.prj_def spec.map.Sup
                    spec.map.singleton spec.singleton.map_le_conv spec.singleton_le_conv
         simp flip: spec.map_invmap.galois)

lemma cl_local:
  shows "spec.local (spec.seq_ctxt.cl T (spec.local.interference \<sqinter> P))
       = spec.local P" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (simp add: spec.local_def spec.map_invmap.galois le_infI2 spec.seq_ctxt.cl_local_le
            flip: spec.map_invmap.cl_def)
  show "?rhs \<le> ?lhs"
    unfolding spec.local_def by (strengthen ord_to_strengthen(2)[OF spec.seq_ctxt.expansive]) simp
qed

lemma cl_imp_local_le:
  assumes "spec.local.interference \<sqinter> P
        \<le> spec.seq_ctxt.cl False (spec.local.interference \<sqinter> Q)"
  shows "spec.local P \<le> spec.local Q"
by (subst (1 2) spec.seq_ctxt.cl_local[where T=False, symmetric])
   (use assms spec.seq_ctxt.cl[where T=False] in \<open>auto intro: spec.local.mono\<close>)

lemma cl_inf_pre:
  shows "spec.pre P \<sqinter> spec.seq_ctxt.cl T c = spec.seq_ctxt.cl T (spec.pre P \<sqinter> c)"
by (fastforce simp: spec.singleton.le_conv
             intro: spec.singleton.antisym
              elim: seq_ctxt.equivalent.partial_sel_equivE)

lemma cl_pre_le_conv:
  shows "spec.seq_ctxt.cl T c \<le> spec.pre P \<longleftrightarrow> c \<le> spec.pre P" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  from spec.seq_ctxt.cl_inf_pre[where P=P and c=c, symmetric]
  show "?lhs \<Longrightarrow> ?rhs"
    by (auto intro: order.trans[OF spec.seq_ctxt.expansive])
  from spec.seq_ctxt.cl_inf_pre[where P=P and c=c, symmetric]
  show "?rhs \<Longrightarrow> ?lhs"
    by (simp add: inf.absorb_iff2)
qed

lemma cl_inf_post:
  shows "spec.post Q \<sqinter> spec.seq_ctxt.cl True c = spec.seq_ctxt.cl True (spec.post Q \<sqinter> c)"
by (fastforce simp: spec.singleton.le_conv
             intro: spec.singleton.antisym
              elim: seq_ctxt.equivalent.partial_sel_equivE
             split: option.split)

lemma cl_post_le_conv:
  shows "spec.seq_ctxt.cl True c \<le> spec.post Q \<longleftrightarrow> c \<le> spec.post Q" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  from spec.seq_ctxt.cl_inf_post[where Q=Q and c=c, symmetric]
  show "?lhs \<Longrightarrow> ?rhs"
    by (auto intro: order.trans[OF spec.seq_ctxt.expansive])
  from spec.seq_ctxt.cl_inf_post[where Q=Q and c=c, symmetric]
  show "?rhs \<Longrightarrow> ?lhs"
    by (simp add: inf.absorb_iff2)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsubsection\<open> Permuting local actions\label{sec:local_state-permuting} \<close>

text\<open>

We can reorder operations on the local state as these are not observable.

Firstly: an initial action \<open>F\<close> that does not change the observable state can be swapped with an
arbitrary action \<open>G\<close>.

\<close>

setup \<open>Sign.mandatory_path "spec.seq_ctxt"\<close>

lemma cl_action_permuteL_le:
  fixes F  :: "('v \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes G  :: "'v \<Rightarrow> ('w \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes G' :: "('v' \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes F' :: "'v' \<Rightarrow> ('w \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
    \<comment>\<open> \<open>F\<close> does not change \<open>'s\<close>, can be partial \<close>
  assumes F: "\<And>v a s s'. \<lbrakk>P s; (v, a, s, s') \<in> F\<rbrakk> \<Longrightarrow> snd s' = snd s"
    \<comment>\<open> The final state and return value are independent of the order of actions.
        \<open>F'\<close> does not change \<open>'s\<close>, cannot be partial \<close>
  assumes FGG'F': "\<And>v w a a' s s' t. \<lbrakk>P s; (v, a', s, t) \<in> F; (w, a, t, s') \<in> G v\<rbrakk>
                   \<Longrightarrow> \<exists>v' a'' a''' s'' t'. (v', a'', s, t') \<in> G' \<and> (w, a''', t', s'') \<in> F' v'
                          \<and> snd s' = snd t' \<and> (snd s \<noteq> snd t' \<longrightarrow> a'' = a) \<and> (T \<longrightarrow> fst s'' = fst s') \<and> snd s'' = snd t'"
  shows "(spec.action F \<bind> (\<lambda>v. spec.action (G v))) \<sqinter> spec.pre P
      \<le> spec.seq_ctxt.cl T (spec.action G' \<bind> (\<lambda>v. spec.action (F' v)))" (is "_ \<le> ?rhs")
unfolding spec.bind.inf_pre
proof(rule order.trans[OF spec.bind.mono[OF spec.pre.inf_action_le(2) order.refl]],
      induct rule: spec.bind_le)
  case incomplete
  from F have "spec.term.none (spec.action (F \<inter> UNIV \<times> UNIV \<times> Pre P)) \<le> spec.seq_ctxt.cl T spec.idle"
    by (fastforce intro: spec.term.none.mono[OF spec.action.rel_le]
                   simp: spec.seq_ctxt.cl.idle[where 'w='v])
  also have "... \<le> ?rhs"
    by (simp add: spec.idle_le spec.seq_ctxt.cl.mono)
  finally show ?case .
next
  case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v) then show ?case
    apply -
    apply (erule (1) spec.singleton.action_Some_leE)
    apply (erule (1) spec.singleton.action_not_idle_leE)
    apply clarsimp
    apply (frule (1) F)
    apply (frule (2) FGG'F')
    apply (clarsimp simp: spec.singleton.seq_ctxt.cl_le_conv)
    apply (intro exI conjI)
     apply (rule spec.bind.continueI)
      apply (rule spec.action.stepI, assumption, blast)
     apply (rule spec.action.stepI[where w="trace.term \<sigma>\<^sub>g"], simp, force)
    apply (clarsimp simp: seq_ctxt.prj_def trace.stuttering.equiv.append_conv
                      trace.stuttering.equiv.simps(3)[where xs="[x]" and ys="[]" for x, simplified])
    apply (rule exI[where x="[]"])
    apply (simp add: image_image trace.natural'.eq_Nil_conv
                     trace_steps'_snd_le_const trace_natural'_took_step_shared_changes)
    apply (intro conjI impI)
    apply (simp add: trace_steps'_snd_le_const)
    done
qed

text\<open>

Secondly: an initial action \<open>G\<close> that does change the observable state can be swapped with an
arbitrary action action \<open>F\<close> that does not observably change the state.

\<close>

lemma cl_action_permuteR_le:
  fixes G  :: "('v \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes F  :: "'v \<Rightarrow> ('w \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes F' :: "('v' \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes G' :: "'v' \<Rightarrow> ('w \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
    \<comment>\<open> \<open>F\<close> does not stall if \<open>G\<close> makes an observable state change \<close>
  assumes G: "\<And>v a s s'. \<lbrakk>P s; (v, a, s, s') \<in> G; snd s' \<noteq> snd s\<rbrakk>
              \<Longrightarrow> \<exists>v' w a'' t s''. (v', a'', s, t) \<in> F' \<and> (w, a, t, s'') \<in> G' v' \<and> snd t = snd s \<and> snd s'' = snd s'"
    \<comment>\<open> The final state and return value are independent of the order of actions \<close>
  assumes GFF'G': "\<And>v w a a' s s' t. \<lbrakk>P s; (v, a, s, t) \<in> G; (w, a', t, s') \<in> F v\<rbrakk>
                   \<Longrightarrow> snd s' = snd t \<and> (\<exists>v' a'' a''' s'' t'. (v', a'', s, t') \<in> F' \<and> (w, a''', t', s'') \<in> G' v'
                                                       \<and> snd t' = snd s \<and> (T \<longrightarrow> fst s'' = fst s') \<and> snd s'' = snd s' \<and> (snd s'' \<noteq> snd t' \<longrightarrow> a''' = a))"
  shows "(spec.action G \<bind> (\<lambda>v. spec.action (F v))) \<sqinter> spec.pre P
      \<le> spec.seq_ctxt.cl T (spec.action F' \<bind> (\<lambda>v. spec.action (G' v)))"
unfolding spec.bind.inf_pre
proof(rule order.trans[OF spec.bind.mono[OF spec.pre.inf_action_le(2) order.refl]],
      induct rule: spec.bind_le)
  case incomplete show ?case
    unfolding spec.term.galois
  proof(induct rule: spec.action_le)
    case idle show ?case
      by (simp add: spec.idle_le)
  next
    case (step v a s s') then show ?case
    proof(cases "snd s' = snd s")
      case True with step show ?thesis
        by (clarsimp simp: spec.singleton.le_conv intro!: exI[where x=None] exI[where x="trace.T s [] None"])
           (simp add: seq_ctxt.prj_def trace.natural.simps order.trans[OF spec.idle.minimal_le] spec.idle_le)
    next
      case False with step show ?thesis
        by (fastforce simp: spec.singleton.le_conv seq_ctxt.prj_def trace.natural.simps
                      dest: G
                     intro: spec.bind.continueI
                      elim: spec.action.stepI)
    qed
  qed
next
  case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v) then show ?case
    apply -
    apply (erule (1) spec.singleton.action_Some_leE)
    apply (erule (1) spec.singleton.action_not_idle_leE)
    apply clarsimp
    apply (drule (2) GFF'G')
    apply (clarsimp simp: spec.singleton.seq_ctxt.cl_le_conv)
    apply (intro exI conjI)
     apply (rule spec.bind.continueI)
      apply (rule spec.action.stepI, assumption, blast)
     apply (rule spec.action.stepI[where w="trace.term \<sigma>\<^sub>g"], simp, force)
    apply (clarsimp simp: seq_ctxt.prj_def trace.stuttering.equiv.append_conv
                          trace.stuttering.equiv.simps(1)[where xs="[x]" for x, simplified])
    apply (rule exI)
    apply (rule exI[where x="[]"])
    apply (intro conjI)
      apply simp
     apply (fastforce simp: trace.natural'.eq_Nil_conv
                      dest: trace_natural'_took_step_shared_changes trace_natural'_took_step_shared_same)
    apply (auto simp: trace.natural'.eq_Nil_conv
            simp flip: trace.final'.map[where af=id and sf=snd]
                dest!: arg_cong[where f=snd] trace_natural'_took_step_shared_same)
    done
qed

lemma cl_action_bind_action_pre_post:
  fixes F' :: "('v \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes G' :: "'v \<Rightarrow> ('w \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes Q :: "'w \<Rightarrow> ('ls \<times> 's) pred"
  assumes "\<And>v w a a' s s' s''. \<lbrakk>P s; (v, a, s, s') \<in> F; (w, a', s', s'') \<in> G v\<rbrakk> \<Longrightarrow> Q w s''"
  shows "spec.pre P \<sqinter> spec.seq_ctxt.cl True (spec.action F \<bind> (\<lambda>v. spec.action (G v))) \<le> spec.post Q"
unfolding spec.seq_ctxt.cl_inf_pre spec.seq_ctxt.cl_post_le_conv spec.bind.inf_pre
proof(induct rule: spec.bind_le)
  case incomplete show ?case
    by (simp add: spec.term.none.post_le)
next
  case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v) with assms show ?case
    by (cases \<sigma>\<^sub>f)
       (fastforce simp: spec.singleton.le_conv spec.singleton.action_le_conv trace.steps'.step_conv
                 split: option.split_asm)
qed

lemma cl_rev_kleene_star_action_permute_le:
  fixes F G :: "(unit \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
    \<comment>\<open> \<open>F\<close> does not stall if \<open>G\<close> changes the observable state \<close>
  assumes G: "\<And>a s s'. \<lbrakk>((), a, s, s') \<in> G; snd s' \<noteq> snd s\<rbrakk>
            \<Longrightarrow> \<exists>w a'' t s''. ((), a'', s, t) \<in> F \<and> ((), a, t, s'') \<in> G \<and> snd t = snd s \<and> snd s'' = snd s'"
    \<comment>\<open> The final state is independent of order of actions, \<open>F\<close> does not change \<open>'s\<close>, can be partial \<close>
  assumes GFFG: "\<And>a a' s s' t. \<lbrakk>((), a, s, t) \<in> G; ((), a', t, s') \<in> F\<rbrakk>
                       \<Longrightarrow> snd s' = snd t \<and> (\<exists>a'' a''' t'. ((), a'', s, t') \<in> F \<and> ((), a''', t', s') \<in> G
                                                       \<and> snd t' = snd s \<and> (snd s' \<noteq> snd t' \<longrightarrow> a''' = a))"
  shows "spec.kleene.rev_star (spec.action G) \<bind> (\<lambda>_::unit. spec.action F)
      \<le> spec.seq_ctxt.cl True (spec.action F \<then> spec.kleene.rev_star (spec.action G))" (is "?lhs spec.kleene.rev_star \<le> ?rhs")
proof(induct rule: spec.kleene.rev_star.fixp_induct[where P="\<lambda>R. ?lhs R \<le> ?rhs", case_names adm bot step])
  case (step S)
  from assms have "S (spec.action G) \<then> spec.action G \<then> spec.action F
     \<le> S (spec.action G) \<bind> (\<lambda>x. spec.seq_ctxt.cl True (spec.action F \<bind> (\<lambda>v. spec.action G)))"
    by (simp add: spec.bind.bind)
       (strengthen ord_to_strengthen(1)[OF spec.seq_ctxt.cl_action_permuteR_le[where P="\<top>" and T=True, simplified]]; force)
  also have "\<dots> \<le> ?rhs"
    apply (strengthen ord_to_strengthen(1)[OF spec.bind.seq_ctxt.clR_le])
    apply (subst spec.bind.bind[symmetric])
    apply (strengthen ord_to_strengthen(1)[OF step])
    apply (strengthen ord_to_strengthen(1)[OF spec.bind.seq_ctxt.clL_le[where T=True]])
    apply (strengthen ord_to_strengthen(2)[OF spec.kleene.fold_rev_starR])
    apply (simp add: spec.bind.bind)
    done
  moreover have "spec.return () \<then> spec.action F \<le> ?rhs"
    apply (simp add: spec.bind.returnL spec.idle_le)
    apply (rule order.trans[OF _ spec.seq_ctxt.expansive])
    apply (rule order.trans[OF _ spec.bind.mono[OF order.refl spec.kleene.epsilon_rev_star_le]])
    apply simp
    done
  ultimately show ?case
    by (simp add: spec.bind.supL)
qed simp_all

lemma cl_local_action_interference_permute_le: \<comment>\<open> local actions permute with interference \<close>
  fixes F :: "(unit \<times> 'a agent \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes r :: "'s rel"
    \<comment>\<open> \<open>F\<close> does not block \<close>
  assumes "\<And>s ls. \<exists>v a ls'. (v, a, (ls, s), (ls', s)) \<in> F"
    \<comment>\<open> \<open>F\<close> is insensitive to and does not modify the shared state \<close>
  assumes "\<And>v a s s' s'' ls ls'. (v, a, (ls, s), (ls', s')) \<in> F
                  \<Longrightarrow> s' = s \<and> (v, a, (ls, s''), (ls', s'')) \<in> F"
  shows "spec.rel (A \<times> (Id \<times>\<^sub>R r)) \<bind> (\<lambda>_::unit. spec.action F)
      \<le> spec.seq_ctxt.cl True (spec.action F \<then> spec.rel (A \<times> (Id \<times>\<^sub>R r)))"
by (simp add: spec.rel.monomorphic_conv spec.kleene.star_rev_star spec.rel.act_def)
   (rule spec.seq_ctxt.cl_rev_kleene_star_action_permute_le; use assms in fastforce)

lemma cl_action_mumble_trailing_le:
  assumes "\<And>v a s s'. \<lbrakk>P s; (v, a, s, s') \<in> F\<rbrakk>
                  \<Longrightarrow> \<exists>a' ls'. (v, a', s, (ls', snd s')) \<in> F'
                             \<and> (snd s' \<noteq> snd s \<longrightarrow> a' = a) \<and> (T \<longrightarrow> ls' = fst s')"
  shows "spec.action F \<sqinter> spec.pre P \<le> spec.seq_ctxt.cl T (spec.action F')"
proof(rule order.trans[OF spec.pre.inf_action_le(2)], induct rule: spec.action_le)
  case idle show ?case
    by (simp add: spec.idle_le)
next
  case (step v a s s')
  then obtain a' ls' where "(v, a', s, (ls', snd s')) \<in> F'" and "snd s' \<noteq> snd s \<longrightarrow> a' = a" and "T \<longrightarrow> ls' = fst s'"
    by (blast dest: assms)
  then show ?case
    unfolding spec.singleton.le_conv
    by (fastforce intro: exI[where x="trace.T s [(a', (ls', snd s'))] (Some v)"] spec.action.stepI
                   simp: seq_ctxt.prj_def trace.natural.simps(2)[where xs="[]"])
qed

lemma cl_action_mumbleL_le:
  assumes "\<And>w a s s'. \<lbrakk>P s; (w, a, s, s') \<in> G\<rbrakk>
               \<Longrightarrow> \<exists>v a' a'' t s''. (v, a', s, t) \<in> F' \<and> (w, a'', t, s'') \<in> G' v
                              \<and> snd t = snd s \<and> (T \<longrightarrow> fst s'' = fst s')
                              \<and> snd s'' = snd s' \<and> (snd s'' \<noteq> snd t \<longrightarrow> a'' = a)"
  shows "spec.action G \<sqinter> spec.pre P \<le> spec.seq_ctxt.cl T (spec.action F' \<bind> (\<lambda>v. spec.action (G' v)))"
using assms by (fastforce intro!: spec.seq_ctxt.cl_action_permuteR_le[where F="\<lambda>v. ({v} \<times> UNIV \<times> Id)", simplified spec.return_def[symmetric], simplified])

lemma cl_action_mumbleR_le:
  assumes "\<And>v a s s'. \<lbrakk>P s; (v, a, s, s') \<in> G\<rbrakk>
               \<Longrightarrow> \<exists>w a' a'' t. (w, a', s, t) \<in> G' \<and> (v, a'', t, s') \<in> F' w
                              \<and> snd t = snd s' \<and> (snd t \<noteq> snd s \<longrightarrow> a' = a)"
  shows "spec.action G \<sqinter> spec.pre P \<le> spec.seq_ctxt.cl T (spec.action G' \<bind> (\<lambda>v. spec.action (F' v)))"
using assms by (fastforce intro!: spec.seq_ctxt.cl_action_permuteL_le[where F="({()} \<times> UNIV \<times> Id)", simplified, simplified spec.idle_le spec.bind.returnL spec.return_def[symmetric]])

lemma cl_action_mumble_expandL_le:
  assumes "\<And>v a s s'. \<lbrakk>P s; (v, a, s, s') \<in> F\<rbrakk> \<Longrightarrow> snd s' = snd s"
  assumes "\<And>v w a a' s s' s''. \<lbrakk>P s; (v, a, s, s') \<in> F; (w, a', s', s'') \<in> G v\<rbrakk>
                 \<Longrightarrow> \<exists>s'''. (w, a', s, s''') \<in> G' \<and> snd s''' = snd s'' \<and> (T \<longrightarrow> fst s''' = fst s'')"
  shows "(spec.action F \<bind> (\<lambda>v. spec.action (G v))) \<sqinter> spec.pre P \<le> spec.seq_ctxt.cl T (spec.action G')"
using assms by (fastforce intro!: spec.seq_ctxt.cl_action_permuteL_le[where F'="\<lambda>v. ({v} \<times> UNIV \<times> Id)", simplified spec.return_def[symmetric], simplified])

lemma cl_action_mumble_expandR_le:
  assumes "\<And>v a s s'. \<lbrakk>P s; (v, a, s, s') \<in> G; snd s' \<noteq> snd s\<rbrakk> \<Longrightarrow> \<exists>v' s''. (v', a, s, s'') \<in> G' \<and> snd s'' = snd s'"
  assumes "\<And>v w a a' s s' t. \<lbrakk>P s; (v, a, s, t) \<in> G; (w, a', t, s') \<in> F v\<rbrakk>
                 \<Longrightarrow> snd s' = snd t \<and> (\<exists>a'' s''. (w, a'', s, s'') \<in> G' \<and> snd s'' = snd s' \<and> (T \<longrightarrow> fst s'' = fst s') \<and> (snd s'' \<noteq> snd s \<longrightarrow> a'' = a))"
  shows "(spec.action G \<bind> (\<lambda>v. spec.action (F v))) \<sqinter> spec.pre P \<le> spec.seq_ctxt.cl T (spec.action G')"
using assms by (fastforce intro!: spec.seq_ctxt.cl_action_permuteR_le[where F'="({()} \<times> UNIV \<times> Id)", simplified, simplified spec.idle_le spec.bind.returnL spec.return_def[symmetric]])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec.local"\<close>

lemma init_write_interference_permute_le:
  fixes P :: "('a agent, 'ls \<times> 's, 'v) spec"
  shows "spec.local (spec.rel ({env} \<times> UNIV) \<bind> (\<lambda>_::unit. spec.write (proc a) (map_prod \<langle>ls\<rangle> id) \<then> P))
      \<le> spec.local (spec.write (proc a) (map_prod \<langle>ls\<rangle> id) \<then> (spec.rel ({env} \<times> UNIV) \<bind> (\<lambda>_::unit. P)))"
apply (rule spec.seq_ctxt.cl_imp_local_le)
apply (simp add: ac_simps spec.bind.inf_rel spec.action.inf_rel
           flip: spec.rel.inf spec.bind.bind)
apply (rule order.trans[OF _ spec.bind.seq_ctxt.cl_le])
apply (rule spec.bind.mono[OF _ spec.seq_ctxt.expansive])
apply (rule spec.seq_ctxt.cl_local_action_interference_permute_le)
apply auto
done

lemma init_write_interference2_permute_le:
  fixes P :: "('a agent, 'ls \<times> 's, 'v) spec"
  shows "spec.local (spec.rel (A \<times> (Id \<times>\<^sub>R r)) \<bind> (\<lambda>_::unit. spec.write (proc a) (map_prod \<langle>ls\<rangle> id) \<then> P))
      \<le> spec.local (spec.write (proc a) (map_prod \<langle>ls\<rangle> id) \<then> (spec.rel (A \<times> (Id \<times>\<^sub>R r)) \<bind> (\<lambda>_::unit. P)))"
apply (rule spec.seq_ctxt.cl_imp_local_le)
apply (simp add: ac_simps spec.bind.inf_rel spec.action.inf_rel
           flip: spec.rel.inf spec.bind.bind)
apply (rule order.trans[OF _ spec.bind.seq_ctxt.cl_le])
apply (rule spec.bind.mono[OF _ spec.seq_ctxt.expansive])
apply (rule spec.seq_ctxt.cl_local_action_interference_permute_le)
apply auto
done

lemma trailing_local_act:
  fixes F :: "'v \<Rightarrow> ('w \<times> 'a agent \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  shows "spec.local (P \<bind> (\<lambda>v. spec.action (F v)))
       = spec.local (P \<bind> (\<lambda>v. spec.action {(w, a, (ls, s), (ls, s')) |w a ls s ls' s'. (w, a, (ls, s), (ls', s')) \<in> F v \<and> (a = env \<longrightarrow> ls' = ls)}))" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    apply (rule spec.seq_ctxt.cl_imp_local_le)
    apply (simp add: spec.bind.inf_rel spec.action.inf_rel)
    apply (rule order.trans[OF _ spec.bind.seq_ctxt.clR_le])
    apply (rule spec.bind.mono[OF order.refl])
    apply (rule spec.seq_ctxt.cl_action_mumble_trailing_le[where P=\<top>, simplified])
    apply (force simp: spec.local.qrm_def)
    done
  show "?rhs \<le> ?lhs"
    apply (rule spec.seq_ctxt.cl_imp_local_le)
    apply (simp add: spec.bind.inf_rel spec.action.inf_rel)
    apply (rule order.trans[OF _ spec.bind.seq_ctxt.clR_le])
    apply (rule spec.bind.mono[OF order.refl])
    apply (rule spec.seq_ctxt.cl_action_mumble_trailing_le[where P=\<top>, simplified])
    apply (force simp: spec.local.qrm_def)
    done
qed

setup \<open>Sign.parent_path\<close>


subsection\<open> \<^emph>\<open>spec.localize\<close>\label{sec:local_state-spec_localize} \<close>

text\<open>

We can transform a process into one with the same observable behavior that ignores a local state.
For compositionality we allow the \<open>env\<close> steps to change the local state but not the \<open>self\<close> steps.

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

definition localize :: "'ls rel \<Rightarrow> ('a agent, 's, 'v) spec \<Rightarrow> ('a agent, 'ls \<times> 's, 'v) spec" where
  "localize r P = spec.rel ({env} \<times> (r \<times>\<^sub>R UNIV) \<union> range proc \<times> (Id \<times>\<^sub>R UNIV)) \<sqinter> spec.sinvmap snd P"

setup \<open>Sign.mandatory_path "idle"\<close>

lemma localize_le:
  assumes "spec.idle \<le> P"
  shows "spec.idle \<le> spec.localize r P"
by (simp add: spec.localize_def spec.idle.rel_le spec.idle.invmap_le[OF assms] spec.idle.term.all_le_conv)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term"\<close>

setup \<open>Sign.mandatory_path "none"\<close>

lemma localize:
  shows "spec.term.none (spec.localize r P) = spec.localize r (spec.term.none P)"
by (simp add: spec.localize_def spec.term.none.inf spec.term.none.inf_none_rel)
   (simp add: spec.term.none.invmap)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "all"\<close>

lemma localize:
  shows "spec.term.all (spec.localize r P) = spec.localize r (spec.term.all P)"
by (simp add: spec.localize_def spec.term.all.rel spec.term.all.inf spec.term.all.invmap)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "closed"\<close>

lemma localize:
  assumes "P \<in> spec.term.closed _"
  shows "spec.localize r P \<in> spec.term.closed _"
by (rule spec.term.closed_clI)
   (simp add: spec.term.all.localize spec.term.all.monomorphic
        flip: spec.term.closed_conv[OF assms, simplified])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "localize"\<close>

lemma singleton:
  fixes \<sigma> :: "('a agent, 's, 'v) trace.t"
  shows "spec.localize Id \<lblot>\<sigma>\<rblot> = (\<Squnion>ls::'ls. \<lblot>trace.map id (Pair ls) id \<sigma>\<rblot>)" (is "?lhs = ?rhs")
proof(rule antisym)
  have *: "map (map_prod id (map_prod \<langle>ls\<rangle> id)) xs = xs"
    if "trace.steps' (ls, s) xs \<subseteq> UNIV \<times> (Id \<times>\<^sub>R UNIV)"
   for ls s and xs :: "('a agent \<times> ('ls \<times> 's)) list"
    using that by (induct xs arbitrary: s) (auto simp: trace.steps'.Cons_eq_if split: if_split_asm)
  have "\<exists>x. \<lblot>\<sigma>''\<rblot> \<le> \<lblot>trace.map id (Pair x) id \<sigma>\<rblot>"
    if "\<lblot>trace.map id snd id \<sigma>'\<rblot> \<le> \<lblot>\<sigma>\<rblot>"
   and "\<sigma>'' \<le> \<sigma>'"
   and "trace.steps' (trace.init \<sigma>'') (trace.rest \<sigma>'') \<subseteq> UNIV \<times> (Id \<times>\<^sub>R UNIV)"
   for \<sigma>' \<sigma>'' :: "('a agent, 'ls \<times> 's, 'v) trace.t"
    using that
    by - (cases \<sigma>'',
          drule spec.singleton.map_le[where  af=id and sf="Pair (fst (trace.init \<sigma>''))" and vf=id],
          fastforce dest: * trace.map.mono[where af=id and sf="\<lambda>x. (fst (trace.init \<sigma>''), snd x)" and vf=id] spec.singleton.mono
                   intro: exI[where x="fst (trace.init \<sigma>'')"]
                    simp: map_prod_def split_def
               simp flip: id_def)
  then show "?lhs \<le> ?rhs"
    by (simp add: spec.localize_def spec.invmap.singleton inf_Sup spec.singleton.inf_rel
            flip: Times_Un_distrib1)
  show "?rhs \<le> ?lhs"
    by (auto simp: spec.localize_def spec.invmap.singleton spec.singleton.le_conv trace_steps'_map
            intro: exI[where x="trace.map id (Pair a) id \<sigma>" for a])
qed

lemma bot:
  shows "spec.localize r \<bottom> = \<bottom>"
by (simp add: spec.localize_def spec.invmap.bot)

lemma top:
  shows "spec.localize r \<top> = spec.rel ({env} \<times> (r \<times>\<^sub>R UNIV) \<union> range proc \<times> (Id \<times>\<^sub>R UNIV))"
by (simp add: spec.localize_def spec.invmap.top)

lemma Sup:
  shows "spec.localize r (\<Squnion>X) = (\<Squnion>x\<in>X. spec.localize r x)"
by (simp add: spec.localize_def spec.invmap.Sup inf_Sup image_image)

lemmas sup = spec.localize.Sup[where X="{X, Y}" for X Y, simplified]

lemma mono:
  assumes "r \<subseteq> r'"
  assumes "P \<le> P'"
  shows "spec.localize r P \<le> spec.localize r' P'"
unfolding spec.localize_def
apply (strengthen ord_to_strengthen(1)[OF \<open>r \<subseteq> r'\<close>])
apply (strengthen ord_to_strengthen(1)[OF \<open>P \<le> P'\<close>])
apply simp
done

lemma strengthen[strg]:
  assumes "st_ord F r r'"
  assumes "st_ord F P P'"
  shows "st_ord F (spec.localize r P) (spec.localize r P')"
using assms by (cases F; simp add: spec.localize.mono)

lemma mono2mono[cont_intro, partial_function_mono]:
  assumes "monotone orda (\<le>) r"
  assumes "monotone orda (\<le>) P"
  shows "monotone orda (\<le>) (\<lambda>x. spec.localize (r x) (P x))"
using assms by (simp add: monotone_def spec.localize.mono)

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) P"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. spec.localize r (P x))"
using assms by (simp add: spec.localize_def)

lemma bind:
  shows "spec.localize r (f \<bind> g) = spec.localize r f \<bind> (\<lambda>v. spec.localize r (g v))"
by (simp add: spec.localize_def spec.invmap.bind spec.bind.inf_rel)

lemma action:
  fixes F :: "('v \<times> 'a agent \<times> 's \<times> 's) set"
  shows "spec.localize r (spec.action F)
       = spec.rel ({env} \<times> (r \<times>\<^sub>R Id))
        \<bind> (\<lambda>_::unit. spec.action ((map_prod id (map_prod id (map_prod snd snd)) -` F)
                                    \<inter> UNIV \<times> ({env} \<times> (r \<times>\<^sub>R UNIV) \<union> range proc \<times> (Id \<times>\<^sub>R UNIV) \<union> UNIV \<times> Id))
        \<bind> (\<lambda>v. spec.rel ({env} \<times> (r \<times>\<^sub>R Id)) \<bind> (\<lambda>_::unit. spec.return v)))"
by (simp add: spec.localize_def spec.invmap.action spec.bind.inf_rel spec.action.inf_rel_reflcl spec.return.inf_rel
              map_prod_snd_snd_vimage inf_sup_distrib Times_Int_Times relprod_inter
              spec.rel.reflcl
        flip: spec.rel.inf)

lemma return:
  shows "(spec.localize r (spec.return v) :: ('a agent, 'ls \<times> 's, 'v) spec)
       = spec.rel ({env} \<times> (r \<times>\<^sub>R Id)) \<bind> (\<lambda>_::unit. spec.return v)"
apply (simp add: spec.return_def spec.localize.action)
apply (simp add: ac_simps map_prod_vimage_Times inf_sup_distrib1 Times_Int_Times
                 map_prod_snd_snd_vimage relprod_inter relprod_inter_Id spec.idle_le
           flip: spec.return_def)
apply (simp add: sup.absorb1 Sigma_mono
           flip: sup.assoc Times_Un_distrib2)
apply (subst spec.action.return_const[where W="{()}"], simp, simp)
apply (simp add: spec.bind.bind spec.bind.return
           flip: spec.rel.act_def[where r="{env} \<times> (r \<times>\<^sub>R Id)", simplified ac_simps])
apply (simp add: spec.rel.wind_bind
           flip: spec.rel.unfoldL spec.bind.bind)
done

lemma rel:
  shows "spec.localize r (spec.rel s)
       = spec.rel (({env} \<times> (r \<times>\<^sub>R UNIV) \<union> range proc \<times> (Id \<times>\<^sub>R UNIV))
                    \<inter> map_prod id (map_prod snd snd) -` (s \<union> UNIV \<times> Id))"
by (simp add: spec.localize_def spec.invmap.rel flip: spec.rel.inf)

lemma rel_le:
  shows "spec.localize Id P \<le> spec.rel (UNIV \<times> (Id \<times>\<^sub>R UNIV))"
unfolding spec.localize_def by (blast intro: le_infI1 spec.rel.mono)

lemma parallel:
  shows "spec.localize UNIV (P \<parallel> Q) = spec.localize UNIV P \<parallel> spec.localize UNIV Q"
by (simp add: spec.localize_def spec.invmap.parallel spec.parallel.inf_rel)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "action"\<close>

lemma localize_le:
  assumes "Id \<subseteq> r"
  shows "spec.action (map_prod id (map_prod id (map_prod snd snd)) -` F \<inter> UNIV \<times> UNIV \<times> (Id \<times>\<^sub>R UNIV))
      \<le> spec.localize r (spec.action F)"
unfolding spec.localize.action
by (strengthen ord_to_strengthen[OF spec.return.rel_le])
   (use assms in \<open>force intro!: spec.action.mono
                          simp: spec.bind.return spec.bind.returnL spec.idle_le\<close>)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "interference.closed"\<close>

lemma localize:
  assumes "P \<in> spec.interference.closed ({env} \<times> UNIV)"
  shows "spec.localize UNIV P \<in> spec.interference.closed ({env} \<times> UNIV)"
by (force simp: spec.localize_def
         intro: spec.interference.closed.rel subsetD[OF spec.interference.closed.antimono, rotated]
                spec.interference.closed.invmap[where sf=snd and vf=id, OF assms])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "local"\<close>

lemma localize:
  assumes "Id \<subseteq> r"
  shows "spec.local (spec.localize r P) = P" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (simp add: ac_simps spec.local_def spec.local.qrm_def spec.localize_def spec.map_invmap.galois)
  from assms show "?rhs \<le> ?lhs"
    by (simp add: spec.local_def spec.local.qrm_def spec.localize_def ac_simps)
       (simp add: spec.map.rel spec.rel.UNIV relprod_inter inf.absorb1
                  inf_sup_distrib Times_Int_Times map_prod_image_Times map_prod_image_relprod
            flip: Sigma_Un_distrib1 spec.map.inf_distr spec.rel.inf)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

setup \<open>Sign.mandatory_path "bind"\<close>

lemma smap_sndL:
  assumes "UNIV \<times> (Id \<times>\<^sub>R UNIV) \<subseteq> r"
  shows "spec.smap snd f \<bind> g = spec.smap snd (f \<bind> (\<lambda>v. spec.rel r \<sqinter> spec.sinvmap snd (g v)))" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
  proof(induct rule: spec.bind_le)
    case incomplete show ?case by (simp add: spec.map.mono spec.term.none.map)
  next
    case (continue \<sigma>\<^sub>f' \<sigma>\<^sub>g v)
    from \<open>\<lblot>\<sigma>\<^sub>f'\<rblot> \<le> spec.smap snd f\<close>
    obtain \<sigma>\<^sub>f
      where *: "\<lblot>\<sigma>\<^sub>f\<rblot> \<le> f" "\<lblot>\<sigma>\<^sub>f'\<rblot> \<le> \<lblot>trace.map id snd id \<sigma>\<^sub>f\<rblot>"
      by (clarsimp simp: spec.singleton.le_conv)
    let ?\<sigma> = "trace.T (trace.init \<sigma>\<^sub>f)
                      (trace.rest \<sigma>\<^sub>f @ map (map_prod id (Pair (fst (trace.final \<sigma>\<^sub>f)))) (trace.rest \<sigma>\<^sub>g))
                      (trace.term \<sigma>\<^sub>g)"
    from continue(3) \<open>\<lblot>\<sigma>\<^sub>f'\<rblot> \<le> \<lblot>trace.map id snd id \<sigma>\<^sub>f\<rblot>\<close>
    have "trace.final \<sigma>\<^sub>f' = snd (trace.final \<sigma>\<^sub>f)"
      by (cases \<sigma>\<^sub>f')
         (clarsimp simp flip: trace.final'.map[where af=id and sf=snd]
                        cong: trace.final'.natural'_cong)
    with assms continue(2,3,4) *
    have "\<lblot>?\<sigma>\<rblot> \<le> f \<bind> (\<lambda>v. spec.rel r \<sqinter> spec.sinvmap snd (g v))"
      by (cases \<sigma>\<^sub>f; cases \<sigma>\<^sub>g)
         (force intro!: spec.bind.continueI[where v=v]
                 simp: spec.singleton.le_conv spec.singleton_le_conv trace_steps'_map
                       trace.natural_def comp_def)
    moreover
    from continue(3) \<open>\<lblot>\<sigma>\<^sub>f'\<rblot> \<le> \<lblot>trace.map id snd id \<sigma>\<^sub>f\<rblot>\<close>
    have "\<lblot>trace.init \<sigma>\<^sub>f', trace.rest \<sigma>\<^sub>f' @ trace.rest \<sigma>\<^sub>g, trace.term \<sigma>\<^sub>g\<rblot> \<le> \<lblot>trace.map id snd id ?\<sigma>\<rblot>"
      by (clarsimp simp: comp_def spec.singleton_le_conv trace.natural_def trace.natural'.append
                   cong: trace.final'.natural'_cong)
    ultimately show ?case
      by (force simp: spec.singleton.le_conv)
  qed
  show "?rhs \<le> ?lhs"
    by (simp add: spec.bind.mono
                  spec.invmap.bind spec.map_invmap.galois spec.map_invmap.upper_lower_expansive)
qed

lemma smap_sndR:
  assumes "UNIV \<times> (Id \<times>\<^sub>R UNIV) \<subseteq> r"
  shows "f \<bind> (\<lambda>v. spec.smap snd (g v)) = spec.smap snd (spec.rel r \<sqinter> spec.sinvmap snd f \<bind> g)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
  proof(induct rule: spec.bind_le)
    case incomplete show ?case
    proof(rule spec.singleton_le_extI)
      show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> spec.term.none f" for \<sigma>
        using assms that
        by (cases \<sigma>)
           (force simp: comp_def spec.singleton.le_conv trace_steps'_map
                intro!: exI[where x="trace.T (undefined, trace.init \<sigma>)
                                             (map (map_prod id (Pair undefined))
                                             (trace.rest \<sigma>)) None"]
                        spec.bind.incompleteI)
    qed
  next
    case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g' v)
    from \<open>\<lblot>\<sigma>\<^sub>g'\<rblot> \<le> spec.smap snd (g v)\<close>
    obtain \<sigma>\<^sub>g
      where "\<lblot>\<sigma>\<^sub>g\<rblot> \<le> g v" and "\<lblot>\<sigma>\<^sub>g'\<rblot> \<le> \<lblot>trace.map id snd id \<sigma>\<^sub>g\<rblot>"
      by (clarsimp simp: spec.singleton.le_conv)
    let ?\<sigma> = "trace.T (fst (trace.init \<sigma>\<^sub>g), trace.init \<sigma>\<^sub>f)
                      (map (map_prod id (Pair (fst (trace.init \<sigma>\<^sub>g)))) (trace.rest \<sigma>\<^sub>f) @ trace.rest \<sigma>\<^sub>g)
                      (trace.term \<sigma>\<^sub>g)"
    from continue(2) \<open>\<lblot>\<sigma>\<^sub>g'\<rblot> \<le> \<lblot>trace.map id snd id \<sigma>\<^sub>g\<rblot>\<close>
    have "snd (trace.init \<sigma>\<^sub>g) = trace.final \<sigma>\<^sub>f"
      by (metis spec.singleton_le_conv trace.less_eqE trace.natural.sel(1) trace.t.map_sel(1))
    with assms continue(1,3) \<open>\<lblot>\<sigma>\<^sub>g\<rblot> \<le> g v\<close>
    have "\<lblot>?\<sigma>\<rblot> \<le> spec.rel r \<sqinter> spec.sinvmap snd f \<bind> g"
      by (cases \<sigma>\<^sub>f, cases \<sigma>\<^sub>g)
         (rule spec.bind.continueI[where v=v];
          force simp: spec.singleton.le_conv comp_def trace_steps'_map trace.final'.map)
    moreover
    from continue(2) \<open>\<lblot>\<sigma>\<^sub>g'\<rblot> \<le> \<lblot>trace.map id snd id \<sigma>\<^sub>g\<rblot>\<close>
    have "\<lblot>trace.init \<sigma>\<^sub>f, trace.rest \<sigma>\<^sub>f @ trace.rest \<sigma>\<^sub>g', trace.term \<sigma>\<^sub>g'\<rblot> \<le> \<lblot>trace.map id snd id ?\<sigma>\<rblot>"
      by (cases \<sigma>\<^sub>f)
         (clarsimp simp: comp_def spec.singleton_le_conv trace.natural_def trace.natural'.append;
          metis order_le_less same_prefix_prefix trace.less_eqE trace.less_eq_None(2) trace.t.sel(1) trace.t.sel(2) trace.t.sel(3))
    ultimately show ?case
      by (force simp: spec.singleton.le_conv)
  qed
  show "?rhs \<le> ?lhs"
    by (simp add: spec.bind.mono
                  spec.invmap.bind spec.map_invmap.galois spec.map_invmap.upper_lower_expansive)
qed

lemma localL:
  shows "spec.local f \<bind> g = spec.local (f \<bind> (\<lambda>v. spec.localize Id (g v)))"
unfolding spec.local_def spec.localize_def spec.local.qrm_def
by (subst spec.bind.smap_sndL[where r="{env} \<times> (Id \<times>\<^sub>R UNIV) \<union> range proc \<times> (Id \<times>\<^sub>R UNIV)"];
    fastforce simp: ac_simps spec.bind.inf_rel inf_sup_distrib1 Times_Int_Times
         simp flip: spec.rel.inf)

lemma localR:
  shows "f \<bind> (\<lambda>v. spec.local (g v)) = spec.local (spec.localize Id f \<bind> g)"
unfolding spec.local_def spec.localize_def spec.local.qrm_def
by (subst spec.bind.smap_sndR[where r="{env} \<times> (Id \<times>\<^sub>R UNIV) \<union> range proc \<times> (Id \<times>\<^sub>R UNIV)"];
    fastforce simp: ac_simps spec.bind.inf_rel inf_sup_distrib1 Times_Int_Times
         simp flip: spec.rel.inf)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "local"\<close>

setup \<open>Sign.mandatory_path "cam"\<close>

lemma cl_le:
  shows "spec.local (spec.cam.cl ({env} \<times> (s \<times>\<^sub>R r)) P) \<le> spec.cam.cl ({env} \<times> r) (spec.local P)"
unfolding spec.cam.cl_def spec.local.sup spec.term.all.local spec.term.none.local[symmetric]
by (fastforce intro: le_supI2 spec.term.none.mono spec.bind.mono spec.rel.mono
          simp flip: spec.map_invmap.galois spec.rel.inf
               simp: spec.local_def spec.map_invmap.galois spec.bind.inf_rel spec.invmap.bind spec.invmap.rel)

lemma cl:
  assumes "Id \<subseteq> r\<^sub>l"
  shows "spec.local (spec.cam.cl ({env} \<times> (r\<^sub>l \<times>\<^sub>R r)) P)
       = spec.cam.cl ({env} \<times> r) (spec.local P)" (is "?lhs = ?rhs")
proof(rule antisym[OF spec.local.cam.cl_le])
  have "spec.local (spec.term.all P) \<then> spec.rel ({env} \<times> r)
     \<le> spec.local (spec.term.all P \<then> spec.rel ({env} \<times> (r\<^sub>l \<times>\<^sub>R r)))"
  proof(induct rule: spec.bind_le)
    case incomplete show ?case
      by (simp add: spec.term.none.local spec.local.mono order.trans[OF _ spec.term.none.bindL_le])
  next
    case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v)
    from \<open>trace.term \<sigma>\<^sub>f = Some v\<close> \<open>\<lblot>\<sigma>\<^sub>f\<rblot> \<le> spec.local (spec.term.all P)\<close>
    obtain s xs w
      where P: "\<lblot>s, xs, w\<rblot> \<le> P"
               "trace.steps' s xs \<subseteq> spec.local.qrm"
               "\<lblot>\<sigma>\<^sub>f\<rblot> \<le> \<lblot>snd s, map (map_prod id snd) xs, trace.term \<sigma>\<^sub>f\<rblot>"
      by (clarsimp simp: spec.singleton.local_le_conv spec.singleton.le_conv spec.singleton_le_conv
                         trace.split_all trace.natural_def)
    let ?\<sigma> = "trace.T s
                      (xs @ map (map_prod id (Pair (fst (trace.final' s xs)))) (trace.rest \<sigma>\<^sub>g))
                      (trace.term \<sigma>\<^sub>g)"
    from assms continue(2,3,4) P(1,3)
    have "\<lblot>?\<sigma>\<rblot> \<le> spec.term.all P \<bind> (\<lambda>_::'g. spec.rel ({env} \<times> (r\<^sub>l \<times>\<^sub>R r)))"
      by (cases \<sigma>\<^sub>f)
         (fastforce intro: spec.bind.continueI
                     simp: spec.singleton.le_conv trace.steps'.map(1)[where af=id and sf="Pair (fst (trace.final' s xs))" and s="snd (trace.final' s xs)", simplified]
                simp flip: trace.final'.map[where af=id and sf=snd]
                     cong: trace.final'.natural'_cong)
    moreover
    from continue(2,3,4) P(2,3)
    have "trace.steps' (trace.init ?\<sigma>) (trace.rest ?\<sigma>) \<subseteq> spec.local.qrm"
      by (fastforce simp: spec.singleton.le_conv spec.singleton_le_conv trace.natural_def trace.natural'.append
                          trace.steps'.append trace.steps'.map(1)[where af=id and sf="Pair (fst (trace.final' s xs))" and s="snd (trace.final' s xs)", simplified]
               simp flip: trace.final'.map[where af=id and sf=snd]
                    cong: trace.final'.natural'_cong)
    moreover
    from \<open>trace.term \<sigma>\<^sub>f = Some v\<close> \<open>\<lblot>\<sigma>\<^sub>f\<rblot> \<le> \<lblot>snd s, map (map_prod id snd) xs, trace.term \<sigma>\<^sub>f\<rblot>\<close>
    have "\<lblot>trace.init \<sigma>\<^sub>f, trace.rest \<sigma>\<^sub>f @ trace.rest \<sigma>\<^sub>g, trace.term \<sigma>\<^sub>g\<rblot> \<le> \<lblot>trace.map id snd id ?\<sigma>\<rblot>"
      by (cases \<sigma>\<^sub>f)
         (simp add: spec.singleton_le_conv trace.natural'.append trace.natural_def comp_def
              cong: trace.final'.natural'_cong)
    ultimately show ?case
      by (force simp: spec.singleton.local_le_conv spec.singleton.le_conv)
  qed
  then show "?rhs \<le> ?lhs"
    by (auto simp: spec.cam.cl_def spec.local.sup spec.term.all.local
        simp flip: spec.term.none.local
            intro: le_supI2 spec.term.none.mono)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "cam.closed"\<close>

lemma local:
  assumes "Id \<subseteq> s"
  assumes "P \<in> spec.cam.closed ({env} \<times> (s \<times>\<^sub>R r))"
  shows "spec.local P \<in> spec.cam.closed ({env} \<times> r)"
by (metis spec.cam.closed spec.cam.closed_conv[OF assms(2)] spec.local.cam.cl[OF assms(1)])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "interference"\<close>

lemma cl_le:
  shows "spec.local (spec.interference.cl ({env} \<times> (s \<times>\<^sub>R r)) P)
      \<le> spec.interference.cl ({env} \<times> r) (spec.local P)"
by (force intro: spec.interference.cl.mono
           simp: spec.local_def spec.map_invmap.upper_lower_expansive spec.map_invmap.galois
                 spec.invmap.interference.cl spec.interference.cl.inf_rel)

lemma cl:
  assumes "Id \<subseteq> s"
  shows "spec.local (spec.interference.cl ({env} \<times> (s \<times>\<^sub>R r)) P)
       = spec.interference.cl ({env} \<times> r) (spec.local P)"
apply (rule antisym[OF spec.local.interference.cl_le])
apply (simp add: spec.interference.cl_def spec.bind.bind spec.bind.localL spec.bind.localR
                 spec.invmap.bind spec.invmap.return spec.invmap.rel
           flip: spec.local.cam.cl[OF order.refl])
apply (simp add: spec.localize.bind spec.localize.rel spec.localize.return)
apply (simp add: spec.rel.wind_bind_trailing flip: spec.bind.bind)
apply (simp add: ac_simps inf_sup_distrib1 map_prod_vimage_Times Times_Int_Times
                 map_prod_snd_snd_vimage relprod_inter spec.rel.reflcl spec.rel.Id UNIV_unit)
apply (intro spec.local.mono spec.bind.mono spec.rel.mono spec.cam.cl.mono)
using assms apply force+
done

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "interference.closed"\<close>

lemma local:
  assumes "P \<in> spec.interference.closed ({env} \<times> (Id \<times>\<^sub>R r))"
  shows "spec.local P \<in> spec.interference.closed ({env} \<times> r)"
by (rule spec.interference.closed_clI)
   (simp flip: spec.interference.closed_conv[OF assms] spec.local.interference.cl[OF order.refl])

lemma local_UNIV:
  assumes "P \<in> spec.interference.closed ({env} \<times> UNIV)"
  shows "spec.local P \<in> spec.interference.closed ({env} \<times> UNIV)"
proof -
  have *: "{env} \<times> (Id \<times>\<^sub>R UNIV) \<subseteq> {env} \<times> UNIV" by blast
  show ?thesis
    by (rule spec.interference.closed_clI)
       (simp flip: spec.interference.closed_conv[OF subsetD[OF spec.interference.closed.antimono[OF *] assms]]
                   spec.local.interference.cl[OF order.refl])
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> \<^emph>\<open>spec.local\_init\<close>\label{sec:local_state-spec_local_init} \<close>

setup \<open>Sign.mandatory_path "spec"\<close>

definition local_init :: "'a \<Rightarrow> 'ls \<Rightarrow> ('a agent, 'ls \<times> 's, 'v) spec \<Rightarrow> ('a agent, 's, 'v) spec" where
  "local_init a ls P = spec.local (spec.write (proc a) (map_prod \<langle>ls\<rangle> id) \<then> P)"

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma local_init_le_conv:
  shows "\<lblot>\<sigma>\<rblot> \<le> spec.local_init a ls P
         \<longleftrightarrow> \<lblot>\<sigma>\<rblot> \<le> spec.idle \<or> (\<exists>\<sigma>'. \<lblot>\<sigma>'\<rblot> \<le> P
                                  \<and> trace.steps \<sigma>' \<subseteq> spec.local.qrm
                                  \<and> \<lblot>\<sigma>\<rblot> \<le> \<lblot>trace.map id snd id \<sigma>'\<rblot>
                                  \<and> fst (trace.init \<sigma>') = ls)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume ?lhs
  then obtain \<sigma>'
        where "\<lblot>\<sigma>'\<rblot> \<le> spec.write (proc a) (map_prod \<langle>ls\<rangle> id) \<then> P"
          and "trace.steps' (trace.init \<sigma>') (trace.rest \<sigma>') \<subseteq> spec.local.qrm"
          and "\<lblot>\<sigma>\<rblot> \<le> \<lblot>trace.map id snd id \<sigma>'\<rblot>"
    by (clarsimp simp: spec.local_init_def spec.singleton.local_le_conv)
  then show ?rhs
  proof(induct rule: spec.singleton.bind_le)
    case incomplete then show ?case
      by (cases \<sigma>')
         (rule disjI1;
          fastforce simp: spec.singleton.le_conv spec.singleton.action_le_conv trace.steps'.step_conv
          elim!: order.trans)
  next
    case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v\<^sub>f) then show ?case
      by (cases \<sigma>\<^sub>g)
         (rule disjI2; erule (1) spec.singleton.action_Some_leE;
          force simp: exI[where x=\<sigma>\<^sub>g] spec.singleton.le_conv image_image
                      trace.steps'.append trace_steps'_snd_le_const)
  qed
next
  show "?rhs \<Longrightarrow> ?lhs"
    by (fastforce simp: spec.local_init_def spec.idle_le trace.split_all spec.singleton.local_le_conv
                intro!: spec.bind.continueI[where xs="[]", simplified] spec.action.stutterI
                 elim!: order.trans)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "idle"\<close>

lemma local_init_le[spec.idle_le]:
  shows "spec.idle \<le> spec.local_init a ls P"
by (simp add: spec.local_init_def spec.idle_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "local_init"\<close>

lemma Sup:
  shows "spec.local_init a ls (\<Squnion>X) = (\<Squnion>x\<in>X. spec.local_init a ls x) \<squnion> spec.idle"
apply (simp add: spec.local_init_def spec.local.Sup spec.local.sup image_image
                 spec.bind.SUPR(1)[where X=X and g=pred_K, simplified]
                 spec.bind.botR spec.local.action
           flip: bot_fun_def spec.term.none.local)
apply (subst spec.return.cong, force, force)
apply (simp add: spec.term.none.return spec.term.none.Sup spec.term.none.sup spec.term.none.idle
                 sup.absorb2)
done

lemma Sup_not_empty:
  assumes "X \<noteq> {}"
  shows "spec.local_init a ls (\<Squnion>X) = (\<Squnion>x\<in>X. spec.local_init a ls x)"
by (subst spec.local_init.Sup) (meson assms spec.local_init.Sup sup.absorb1 SUPI spec.idle_le ex_in_conv)

lemmas sup = spec.local_init.Sup_not_empty[where X="{X, Y}" for X Y, simplified]

lemma bot:
  shows "spec.local_init a ls \<bottom> = spec.idle"
using spec.local_init.Sup[where X="{}"] by simp

lemma top:
  shows "spec.local_init a ls \<top> = (\<top> :: ('a agent, 's, 'v) spec)"
proof -
  have "\<lblot>\<sigma>\<rblot> \<le> spec.local_init a ls \<top>" for \<sigma> :: "('a agent, 's, 'v) trace.t"
    by (fastforce simp: spec.local_init_def spec.local.qrm_def spec.singleton.local_le_conv trace.steps'.map comp_def
                 intro: exI[where x="trace.T (ls, trace.init \<sigma>) (map (map_prod id (Pair ls)) (trace.rest \<sigma>)) (trace.term \<sigma>)"]
                        spec.bind.continueI[where xs="[]", simplified] spec.action.stutterI)
  then show ?thesis
    by (fastforce intro: top_le spec.singleton_le_extI simp: spec.local_init_def)
qed

lemma monotone:
  shows "mono (spec.local_init a ls :: ('a agent, 'ls \<times> 's, 'v) spec \<Rightarrow> _)"
proof(rule monotoneI)
  show "spec.local_init a ls P \<le> spec.local_init a ls P'" if "P \<le> P'" for P P' :: "('a agent, 'ls \<times> 's, 'v) spec"
    unfolding spec.local_init_def by (strengthen ord_to_strengthen(1)[OF \<open>P \<le> P'\<close>]) simp
qed

lemmas strengthen[strg] = st_monotone[OF spec.local_init.monotone]
lemmas mono = monotoneD[OF spec.local_init.monotone]

lemma mono2mono[cont_intro, partial_function_mono]:
  assumes "monotone orda (\<le>) P"
  shows "monotone orda (\<le>) (\<lambda>x. spec.local_init a ls (P x))"
by (simp add: monotone2monotone[OF spec.local_init.monotone assms])

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) P"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. spec.local_init a ls (P x))"
by (simp add: spec.local_init_def assms)

lemma action:
  fixes F  :: "('v \<times> 'a agent \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  shows "spec.local_init a ls (spec.action F)
       = spec.action {(v, a, s, s') |v a ls' s s'. (v, a, (ls, s), (ls', s')) \<in> F \<and> (a = env \<longrightarrow> ls' = ls)}" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    apply (subst (3) spec.local.localize[where r=UNIV, symmetric], simp)
    apply (simp add: spec.local_init_def)
    apply (rule spec.seq_ctxt.cl_imp_local_le)
    apply (simp add: spec.localize.action spec.bind.inf_rel spec.action.inf_rel spec.return.inf_rel)
    apply (strengthen ord_to_strengthen(2)[OF spec.return.rel_le])
    apply (fastforce intro: spec.seq_ctxt.cl_action_mumble_expandL_le[where P=\<top>, simplified]
                      simp: spec.local.qrm_def spec.bind.returnL spec.idle_le)
    done
  show "?rhs \<le> ?lhs"
    apply (subst (1) spec.local.localize[where r=UNIV, symmetric], simp)
    apply (simp add: spec.local_init_def)
    apply (rule spec.seq_ctxt.cl_imp_local_le)
    apply (simp add: spec.localize.action spec.bind.inf_rel spec.action.inf_rel spec.return.inf_rel
                     spec.rel.Id spec.bind.returnL spec.idle_le UNIV_unit
               flip: spec.rel.inf)
    apply (fastforce intro: spec.seq_ctxt.cl_action_mumbleL_le[where P=\<top>, simplified]
                      simp: spec.local.qrm_def)
    done
qed

lemma return:
  shows "spec.local_init a ls (spec.return v) = spec.return v"
by (auto simp: spec.local_init.action spec.return_def intro: arg_cong[where f=spec.action])

lemma localize_le:
  assumes "spec.idle \<le> P"
  shows "spec.local_init a ls (spec.localize r P) \<le> P"
unfolding spec.local_init_def spec.localize_def
apply (rule order.trans[OF spec.local.bind_le])
apply (simp add: spec.local.action)
apply (subst spec.return.cong, force, force)
apply (simp add: assms spec.bind.SupL spec.bind.supL
                 spec.bind.returnL spec.idle.local_le spec.idle.invmap_le spec.idle.rel_le)
apply (simp add: le_infI2 spec.local_def spec.map_invmap.galois)
done

lemma localize:
  assumes "spec.idle \<le> P"
  assumes "Id \<subseteq> r"
  shows "spec.local_init a ls (spec.localize r P) = P" (is "?lhs = ?rhs")
proof(rule antisym[OF spec.local_init.localize_le[OF assms(1)] spec.singleton_le_extI])
  show "\<lblot>\<sigma>\<rblot> \<le> ?lhs" if "\<lblot>\<sigma>\<rblot> \<le> ?rhs" for \<sigma>
    using that
    by (cases \<sigma>)
       (fastforce simp: spec.local_init_def spec.localize_def spec.local.qrm_def comp_def
                        spec.singleton.le_conv spec.singleton.local_le_conv trace_steps'_map
                 intro: exI[where x="trace.map id (Pair ls) id \<sigma>"] subsetD[OF \<open>Id \<subseteq> r\<close>]
                        spec.bind.continueI[where xs="[]", simplified] spec.action.stutterI)
qed

lemma inf_interference:
  shows "spec.local_init a ls P = spec.local_init a ls (P \<sqinter> spec.local.interference)"
unfolding spec.local_init_def
by (subst spec.local.inf_interference)
   (auto simp: ac_simps spec.bind.inf_rel spec.action.inf_rel
        intro: arg_cong[where f="\<lambda>x. spec.local (spec.action x \<bind> (\<lambda>x. P \<sqinter> spec.local.interference))"])

lemma eq_local:
  assumes "spec.idle \<le> P"
  shows "(\<Squnion>ls. spec.local_init a ls P) = spec.local P"
proof -
  have "spec.local (spec.action {((), proc a, (ls, s), ls', s) |ls' ls s. True} \<then> P)
      = spec.local P" (is "?lhs = ?rhs")
proof(rule antisym)
  have "?rhs = spec.return () \<then> ?rhs"
    by (simp add: spec.bind.returnL assms spec.idle.local_le)
  also have "\<dots> = spec.smap snd (spec.sinvmap snd (spec.return ()) \<then> spec.rel spec.local.qrm \<sqinter> P)"
    by (simp add: spec.local_def spec.bind.smap_sndR[where r=UNIV, simplified spec.rel.UNIV])
  also have "?lhs \<le> \<dots>"
    by (force intro: spec.map.mono spec.bind.mono le_infI2 spec.action.rel_le
               simp: spec.local_def spec.invmap.return spec.bind.bind spec.bind.return spec.bind.inf_rel)
  finally show "?lhs \<le> ?rhs" .
  show "?rhs \<le> ?lhs"
    by (force simp: assms
             intro: spec.local.mono order.trans[OF spec.bind.returnL_le[where g="\<langle>P\<rangle>" and v="()"]]
                    spec.return.action_le spec.bind.mono)
  qed
  then show ?thesis
    by (simp add: spec.local_init_def UNION_eq
            flip: spec.local.Sup[where X="(\<lambda>ls. spec.write (proc a) (map_prod \<langle>ls\<rangle> id) \<then> P) ` UNIV", simplified, simplified image_image]
                  spec.bind.SUPL spec.action.SUP_not_empty)
qed

lemma ag_le:
  shows "spec.local_init a ls (\<lbrace>P\<rbrace>, Id \<times>\<^sub>R A \<turnstile> UNIV \<times>\<^sub>R G, \<lbrace>\<lambda>v s. Q v (snd s)\<rbrace>)
      \<le> \<lbrace>\<lambda>s. P (ls, s)\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
apply (subst ag.reflcl_a)
apply (simp add: spec.local_init_def spec.local_def spec.local.qrm_def
                 spec.map_invmap.galois spec.invmap.ag map_prod_snd_snd_vimage)
apply (subst inf.commute)
apply (subst heyting[symmetric])
apply (subst sup.commute, subst ag.assm_heyting)
apply (force intro: ag.spec.bind[rotated] ag.spec.action[where Q="\<lambda>_. FST ((=) ls) \<^bold>\<and> P"] ag.mono)
done

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "bind"\<close>

lemma local_initL:
  shows "spec.local_init a ls f \<bind> g = spec.local_init a ls (f \<bind> (\<lambda>v. spec.localize Id (g v)))"
by (simp add: spec.local_init_def spec.bind.localL spec.bind.bind)

lemma local_initR:
  shows "f \<bind> (\<lambda>v. spec.local_init a ls (g v)) = spec.local_init a ls (spec.localize Id f \<bind> g)"
oops

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "sinvmap"\<close>

lemma local_init:
  fixes P :: "('a agent, 'ls \<times> 't, 'v) spec"
  fixes sf :: "'s \<Rightarrow> 't"
  shows "spec.sinvmap sf (spec.local_init a ls P)
       = spec.local_init a ls (spec.rel (UNIV \<times> (Id \<times>\<^sub>R map_prod sf sf -` Id))
                                 \<bind> (\<lambda>_::unit. spec.sinvmap (map_prod id sf) P))" (is "?lhs = ?rhs")
proof(rule antisym)
  let ?r = "UNIV \<times> (Id \<times>\<^sub>R map_prod sf sf -` Id)"
  have "?lhs = spec.local (spec.rel ?r \<bind>
                 (\<lambda>_::unit. spec.action ({((), proc a, (ls', s), ls, s') |ls' s s'. sf s = sf s'}) \<bind>
                   (\<lambda>_::unit. spec.rel ?r \<bind> (\<lambda>_::unit. spec.sinvmap (map_prod id sf) P))))"
    by (simp add: spec.local_init_def spec.invmap.local spec.invmap.bind spec.invmap.action
                  spec.bind.bind map_prod_conv map_prod_map_prod_vimage_Id)
  also have "\<dots> \<le> spec.local (spec.rel ?r \<bind>
                    (\<lambda>_::unit. spec.write (proc a) (map_prod \<langle>ls\<rangle> id) \<bind>
                      (\<lambda>_::unit. spec.rel.act ?r \<bind>
                        (\<lambda>_::unit. spec.rel ?r \<bind> (\<lambda>_::unit. spec.sinvmap (map_prod id sf) P)))))"
    apply (rule spec.seq_ctxt.cl_imp_local_le)
    apply (simp add: ac_simps spec.bind.inf_rel spec.action.inf_rel spec.rel.act_def flip: spec.rel.inf)
    apply (subst (4) spec.bind.bind[symmetric])
    apply ( (rule spec.seq_ctxt.cl_action_mumbleL_le[where P="\<top>", simplified]; force)
          | rule order.trans[OF spec.bind.mono spec.bind.seq_ctxt.cl_le] spec.seq_ctxt.expansive )+
    done
  also have "\<dots> = spec.local (spec.rel ?r \<bind>
                    (\<lambda>_::unit. spec.write (proc a) (map_prod \<langle>ls\<rangle> id) \<bind>
                      (\<lambda>_::unit. spec.rel ?r \<bind> (\<lambda>_::unit. spec.sinvmap (map_prod id sf) P))))"
    by (simp add: spec.rel.wind_bind flip: spec.bind.bind spec.rel.unfoldL)
  also have "\<dots> \<le> spec.local (spec.write (proc a) (map_prod \<langle>ls\<rangle> id) \<bind>
                    (\<lambda>_::unit. spec.rel ?r \<bind>
                      (\<lambda>_::unit. spec.rel ?r \<bind> (\<lambda>_::unit. spec.sinvmap (map_prod id sf) P))))"
    by (rule spec.local.init_write_interference2_permute_le)
  also have "\<dots> = spec.local (spec.write (proc a) (map_prod \<langle>ls\<rangle> id) \<bind>
                    (\<lambda>_::unit. spec.rel ?r \<bind> (\<lambda>_::unit. spec.sinvmap (map_prod id sf) P)))"
    by (simp add: spec.rel.wind_bind flip: spec.bind.bind)
  also have "\<dots> = ?rhs"
    by (simp add: spec.local_init_def)
  finally show "?lhs \<le> ?rhs" .
  show "?rhs \<le> ?lhs"
    by (fastforce simp: spec.local_init_def spec.invmap.local spec.invmap.bind spec.invmap.action
                        map_prod_conv spec.bind.bind map_prod_map_prod_vimage_Id
                 intro: spec.local.mono order.trans[OF _ spec.bind.relL_le] spec.bind.mono spec.action.mono)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "vmap"\<close>

lemma local_init:
  shows "spec.vmap vf (spec.local_init a ls P) = spec.local_init a ls (spec.vmap vf P)"
by (simp add: spec.local_init_def spec.vmap.local spec.map.bind_inj_sf spec.map.id)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "vinvmap"\<close>

lemma local_init:
  shows "spec.vinvmap vf (spec.local_init a ls P) = spec.local_init a ls (spec.vinvmap vf P)"
by (simp add: spec.local_init_def spec.invmap.local spec.invmap.bind spec.invmap.action spec.rel.Id UNIV_unit
              spec.bind.returnL spec.idle_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term.none"\<close>

lemma local_init:
  shows "spec.term.none (spec.local_init a ls P) = spec.local_init a ls (spec.term.none P)"
by (simp add: spec.local_init_def spec.term.none.local spec.term.none.bind)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term.all"\<close>

lemma local_init:
  shows "spec.term.all (spec.local_init a ls P)
       = spec.local_init a ls (spec.term.all P) \<squnion> \<Squnion>range spec.return"
apply (simp add: spec.local_init_def spec.term.all.local spec.term.all.bind spec.term.all.action
                 spec.local.Sup spec.local.sup spec.local.action spec.local.return image_image ac_simps)
apply (subst (2) spec.return.cong, force, force intro!: exI[where x="proc a"])
apply (rule antisym; clarsimp simp: le_supI1 le_supI2 SUP_upper SUP_upper2 spec.idle_le)
done

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "interference.closed"\<close>

lemma local_init:
  assumes "P \<in> spec.interference.closed ({env} \<times> (Id \<times>\<^sub>R r))"
  shows "spec.local_init a ls P \<in> spec.interference.closed ({env} \<times> r)"
by (rule spec.interference.closed_clI)
   (simp add: spec.local_init_def spec.bind.bind spec.interference.cl.action
              spec.interference.cl.bindR[OF assms] spec.interference.closed.bind_relL[OF assms]
              order.trans[OF spec.local.init_write_interference2_permute_le[simplified]]
        flip: spec.local.interference.cl[where s=Id])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Hoist to \<^emph>\<open>('s, 'v) prog\<close>\label{sec:local_state-prog} \<close>

setup \<open>Sign.mandatory_path "prog"\<close>

lift_definition local :: "('ls \<times> 's, 'v) prog \<Rightarrow> ('s, 'v) prog" is spec.local
by (blast intro: spec.interference.closed.local subsetD[OF spec.interference.closed.antimono, rotated])

definition local_init :: "'ls \<Rightarrow> ('ls \<times> 's, 'v) prog \<Rightarrow> ('s, 'v) prog" where
  "local_init ls P = prog.local (prog.write (map_prod \<langle>ls\<rangle> id) \<then> P)"
  \<comment>\<open> equivalent to lifting \<^const>\<open>spec.local_init\<close>; see \<open>prog.p2s.local_init\<close> \<close>

lift_definition localize :: "('s, 'v) prog \<Rightarrow> ('ls \<times> 's, 'v) prog" is "spec.localize UNIV"
by (rule spec.interference.closed.localize)

setup \<open>Sign.mandatory_path "p2s"\<close>

lemmas local[prog.p2s.simps] = prog.local.rep_eq

lemma local_init[prog.p2s.simps]:
  shows "prog.p2s (prog.local_init ls P) = spec.local_init () ls (prog.p2s P)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (simp add: prog.local_init_def spec.local_init_def
                  prog.p2s.simps prog.p2s.action prog.p2s.interference_wind_bind
                  map_prod_image_Collect spec.interference.cl.action spec.bind.bind
                  order.trans[OF spec.local.init_write_interference_permute_le[simplified]])
  show "?rhs \<le> ?lhs"
    by (simp add: prog.local_init_def spec.local_init_def prog.p2s.simps prog.p2s.action
                  map_prod_image_Collect
                  spec.local.mono[OF spec.bind.mono[OF spec.interference.expansive order.refl]])
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "local"\<close>

lemma Sup:
  shows "prog.local (\<Squnion>X) = (\<Squnion>x\<in>X. prog.local x)"
by transfer
   (simp add: spec.local.Sup spec.local.sup spec.interference.cl.bot spec.local.interference
        flip: spec.term.none.local)

lemmas sup = prog.local.Sup[where X="{X, Y}" for X Y, simplified]

lemma bot:
  shows "prog.local \<bottom> = \<bottom>"
using prog.local.Sup[where X="{}"] by simp

lemma top:
  shows "prog.local \<top> = \<top>"
by transfer (simp add: spec.local.top)

lemma monotone:
  shows "mono prog.local"
by (rule monotoneI) (transfer; erule monotoneD[OF spec.local.monotone])

lemmas strengthen[strg] = st_monotone[OF prog.local.monotone]
lemmas mono = monotoneD[OF prog.local.monotone]
lemmas mono2mono[cont_intro, partial_function_mono]
  = monotone2monotone[OF prog.local.monotone, simplified, of orda P for orda P]

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) P"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. prog.local (P x))"
proof(rule mcontI)
  from assms show "monotone orda (\<le>) (\<lambda>x. prog.local (P x))"
    by (blast intro: mcont_mono prog.local.mono2mono)
  from assms show "cont luba orda Sup (\<le>) (\<lambda>x. prog.local (P x))"
    by (fastforce intro: contI dest: mcont_cont contD simp: prog.local.Sup image_image)
qed

lemma bind_botR:
  shows "prog.local (P \<bind> \<bottom>) = prog.local P \<bind> \<bottom>"
by (simp add: prog.p2s.simps spec.interference.cl.bot bot_fun_def
              spec.interference.closed.bind_relR spec.interference.closed.local_UNIV
        flip: spec.bind.botR prog.p2s_inject)
   (simp add: spec.bind.localL spec.localize.bot)

lemma action:
  shows "prog.local (prog.action F) = prog.action (map_prod id (map_prod snd snd) ` F)"
by transfer
   (force simp: spec.local.interference.cl[OF subset_UNIV, where r=UNIV, simplified] spec.local.action
         intro: arg_cong[where f="\<lambda>F. spec.interference.cl ({env} \<times> UNIV) (spec.action F)"])

lemma return:
  shows "prog.local (prog.return v) = prog.return v"
by (simp add: prog.return_def prog.local.action map_prod_image_Times map_prod_snd_snd_image_Id)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "local_init"\<close>

lemma transfer[transfer_rule]:
  shows "rel_fun (=) (rel_fun cr_prog cr_prog) (spec.local_init ()) prog.local_init"
by (simp add: cr_prog_def prog.p2s.local_init rel_fun_def)

lemma Sup:
  shows "prog.local_init ls (\<Squnion>X) = (\<Squnion>x\<in>X. prog.local_init ls x)"
by (simp add: prog.local_init_def prog.bind.SupR prog.local.Sup prog.local.sup image_image
                 prog.local.bind_botR prog.local.action)
   (subst prog.return.cong; force simp: prog.bind.returnL)

lemmas sup = prog.local_init.Sup[where X="{X, Y}" for X Y, simplified]

lemma bot[simp]:
  shows "prog.local_init ls \<bottom> = \<bottom>"
using prog.local_init.Sup[where ls=ls and X="{}"] by simp

lemma top:
  shows "prog.local_init ls \<top> = \<top>"
by (simp add: prog.p2s.simps spec.local_init.top flip: prog.p2s_inject)

lemma monotone:
  shows "mono (prog.local_init ls)"
unfolding prog.local_init_def by simp

lemmas strengthen[strg] = st_monotone[OF prog.local_init.monotone]
lemmas mono = monotoneD[OF prog.local_init.monotone]

lemma mono2mono[cont_intro, partial_function_mono]:
  assumes "monotone orda (\<le>) P"
  shows "monotone orda (\<le>) (\<lambda>x. prog.local_init ls (P x))"
by (simp add: monotone2monotone[OF prog.local_init.monotone assms])

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) P"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. prog.local_init ls (P x))"
proof(rule mcontI)
  from assms show "monotone orda (\<le>) (\<lambda>x. prog.local_init ls (P x))"
    by (blast intro: mcont_mono prog.local_init.mono2mono)
  from assms show "cont luba orda Sup (\<le>) (\<lambda>x. prog.local_init ls (P x))"
    by (fastforce intro: contI dest: mcont_cont contD simp: prog.local_init.Sup image_image)
qed

lemma bind_botR:
  shows "prog.local_init ls (P \<bind> \<bottom>) = prog.local_init ls P \<bind> \<bottom>"
by (simp add: prog.local_init_def prog.local.bind_botR flip: prog.bind.bind)

lemma return:
  shows "prog.local_init ls (prog.return v) = prog.return v" (is "?lhs = ?rhs")
proof -
  have "prog.p2s ?rhs = spec.local_init () ls (spec.localize UNIV (spec.rel ({env} \<times> UNIV)
                                            \<bind> (\<lambda>_::unit. spec.return v)))"
    by (simp add: prog.p2s.simps prog.p2s.return spec.interference.cl.return
                  spec.local_init.localize spec.idle_le)
  also have "\<dots> = spec.local_init () ls (spec.rel ({env} \<times> UNIV) \<bind> (\<lambda>_::unit. spec.return v))"
    by (simp add: spec.localize.bind spec.localize.rel spec.localize.return
                  spec.bind.inf_rel spec.return.inf_rel
                  map_prod_vimage_Times map_prod_snd_snd_vimage
                  ac_simps Int_Un_distrib Int_Un_distrib2 Times_Int_Times relprod_inter spec.rel.reflcl
                  spec.rel.wind_bind_trailing times_subset_iff Id_le_relprod_conv
      flip: spec.rel.inf spec.bind.bind)
  also have "\<dots> = prog.p2s ?lhs"
    by (simp add: prog.p2s.simps prog.p2s.return spec.interference.cl.return)
  finally show ?thesis
    by (simp add: p2s_inject)
qed

lemma eq_local:
  shows "(\<Squnion>ls. prog.local_init ls P) = prog.local P"
by transfer
   (simp add: spec.local_init.eq_local spec.idle_le sup.absorb1 spec.interference.least
              spec.interference.closed.local_UNIV)

setup \<open>Sign.parent_path\<close>

lemma localize_alt_def:
  shows "prog.localize P = prog.rel (Id \<times>\<^sub>R UNIV) \<sqinter> prog.sinvmap snd P"
by transfer (simp add: spec.localize_def ac_simps)

setup \<open>Sign.mandatory_path "localize"\<close>

lemma Sup:
  shows "prog.localize (\<Squnion>X) = (\<Squnion>x\<in>X. prog.localize x)"
by (simp add: prog.localize_alt_def prog.invmap.Sup inf_Sup inf_sup_distrib image_image prog.bind.inf_rel
              inv_image_alt_def map_prod_snd_snd_vimage relprod_inter
              prog.rel.Id prog.rel.empty prog.bind.returnL prog.invmap.bot UNIV_unit
        flip: prog.rel.inf)

lemmas sup = prog.localize.Sup[where X="{X, Y}" for X Y, simplified]

lemma bot:
  shows "prog.localize \<bottom> = \<bottom>"
using prog.localize.Sup[where X="{}"] by simp

lemma top:
  shows "prog.localize \<top> = prog.rel (Id \<times>\<^sub>R UNIV)"
by transfer (simp add: spec.localize.top ac_simps)

lemma monotone:
  shows "mono prog.localize"
by (rule monotoneI) (transfer; simp add: spec.interference.cl.mono spec.localize.mono)

lemmas strengthen[strg] = st_monotone[OF prog.localize.monotone]
lemmas mono = monotoneD[OF prog.localize.monotone]
lemmas mono2mono[cont_intro, partial_function_mono]
  = monotone2monotone[OF prog.localize.monotone, simplified, of orda P for orda P]

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) P"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. prog.localize (P x))"
proof(rule mcontI)
  from assms show "monotone orda (\<le>) (\<lambda>x. prog.localize (P x))"
    by (blast intro: mcont_mono prog.localize.mono2mono)
  from assms show "cont luba orda Sup (\<le>) (\<lambda>x. prog.localize (P x))"
    by (fastforce intro: contI dest: mcont_cont contD simp: prog.localize.Sup image_image)
qed

lemmas p2s[prog.p2s.simps] = prog.localize.rep_eq

lemma bind:
  shows "prog.localize (f \<bind> g) = prog.localize f \<bind> (\<lambda>v. prog.localize (g v))"
by transfer
   (simp add: spec.localize.bind spec.interference.least spec.interference.closed.bind spec.bind.mono)

lemma parallel:
  shows "prog.localize (P \<parallel> Q) = prog.localize P \<parallel> prog.localize Q"
by transfer (simp add: spec.localize.parallel)

lemma rel:
  fixes r :: "'s rel"
  shows "prog.localize (prog.rel r) = prog.rel (Id \<times>\<^sub>R r)"
by (subst (2) prog.rel.reflcl[symmetric])
   (transfer; auto simp: spec.localize.rel intro: arg_cong[where f=spec.rel])

lemma action:
  shows "prog.localize (prog.action F)
       = prog.action (map_prod id (map_prod snd snd) -` F \<inter> UNIV \<times> (Id \<times>\<^sub>R UNIV))"
by (simp add: prog.localize_alt_def prog.invmap.action prog.bind.inf_rel prog.action.inf_rel
              map_prod_snd_snd_vimage relprod_inter prog.rel.Id UNIV_unit refl_relprod_conv
              prog.bind.return prog.return.rel_le
              inf.absorb2
        flip: prog.rel.inf)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "local"\<close>

lemma localize:
  fixes P :: "('s, 'v) prog"
  shows "prog.local (prog.localize P :: ('ls \<times> 's, 'v) prog) = P"
by transfer
   (simp add: spec.local.interference.cl[where r=UNIV and s=UNIV, simplified] spec.local.localize
        flip: spec.interference.closed_conv)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Refinement rules \label{sec:local_state-refinement} \<close>

setup \<open>Sign.mandatory_path "spec"\<close>

text\<open>

We use \<open>localizeA\<close> to hoist assumes similarly to \<^const>\<open>spec.localize\<close>.

\<close>

definition localizeA :: "(sequential, 's, 'v) spec \<Rightarrow> (sequential, 'ls \<times> 's, 'v) spec" where
  "localizeA P = spec.local.interference \<sqinter> spec.sinvmap snd P"

setup \<open>Sign.mandatory_path "localizeA"\<close>

lemma bot:
  shows "spec.localizeA \<bottom> = \<bottom>"
by (simp add: spec.localizeA_def spec.invmap.bot)

lemma top:
  shows "spec.localizeA \<top> = spec.local.interference"
by (simp add: spec.localizeA_def spec.invmap.top)

lemma ag_assm:
  shows "spec.localizeA (ag.assm A) = ag.assm (Id \<times>\<^sub>R A)"
apply (simp add: spec.localizeA_def spec.invmap.rel spec.local.qrm_def flip: spec.rel.inf)
apply (subst (1 2) spec.rel.reflcl[where A=UNIV, symmetric])
apply (auto intro: arg_cong[where f=spec.rel])
done

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "refinement"\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

lemma localI: \<comment>\<open> Introduce local state \<close>
  fixes A :: "(sequential, 's, 'v) spec"
  fixes c :: "(sequential, 'ls \<times> 's, 'v) spec"
  fixes c' :: "(sequential, 's, 'v) spec"
  fixes P :: "'s pred"
  fixes Q :: "'v \<Rightarrow> 's pred"
  assumes "c \<le> \<lbrace>\<lambda>s. P (snd s)\<rbrace>, spec.localizeA A \<tturnstile> spec.sinvmap snd c', \<lbrace>\<lambda>v s. Q v (snd s)\<rbrace>"
  shows "spec.local c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> c', \<lbrace>Q\<rbrace>"
apply (simp only: spec.local_def spec.map_invmap.galois spec.invmap.refinement id_apply)
apply (subst inf.commute)
apply (subst heyting[symmetric])
apply (strengthen ord_to_strengthen[OF assms])
apply (strengthen ord_to_strengthen[OF refinement.heyting_le])
apply (simp add: refinement.mono[OF order.refl _ _ order.refl] heyting spec.localizeA_def)
done

setup \<open>Sign.mandatory_path "seq_ctxt"\<close>

lemma local_seq_ctxt_cl:
  fixes A :: "(sequential, 's, 'v) spec"
  fixes P :: "'s pred"
  fixes Q :: "'v \<Rightarrow> 's pred"
  fixes c :: "(sequential, 'ls \<times> 's, 'v) spec"
  fixes c' :: "(sequential, 'ls \<times> 's, 'v) spec"
  assumes "spec.local.interference \<sqinter> c
        \<le> \<lbrace>\<lambda>s. P (snd s)\<rbrace>, spec.localizeA A \<tturnstile> spec.seq_ctxt.cl False (spec.local.interference \<sqinter> c'), \<lbrace>\<lambda>v s. Q v (snd s)\<rbrace>"
  shows "spec.local c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> spec.local c', \<lbrace>Q\<rbrace>"
apply (simp only: spec.local_def spec.map_invmap.galois spec.invmap.refinement id_apply)
apply (subst inf.left_idem[symmetric]) \<comment>\<open> non-linear use of env constraint \<close>
apply (strengthen ord_to_strengthen(1)[OF assms])
apply (subst inf.commute)
apply (subst heyting[symmetric])
apply (strengthen ord_to_strengthen(2)[OF refinement.heyting_le])
apply (subst inf.commute, fold spec.localizeA_def)
apply (rule refinement.mono[OF order.refl order.refl _ order.refl])
apply (strengthen ord_to_strengthen(1)[OF spec.seq_ctxt.cl_local_le])
apply (simp add: heyting flip: spec.map_invmap.cl_def)
done

lemma cl_bind:
  fixes f :: "('a agent, 'ls \<times> 's, 'v) spec"
  fixes g :: "'v \<Rightarrow> ('a agent, 'ls \<times> 's, 'w) spec"
  assumes g: "\<And>v. g v \<le> \<lbrace>Q' v\<rbrace>, refinement.spec.bind.res (spec.pre P \<sqinter> spec.term.all A \<sqinter> spec.seq_ctxt.cl True f') A v \<tturnstile> spec.seq_ctxt.cl T (g' v), \<lbrace>Q\<rbrace>"
  assumes f: "f \<le> \<lbrace>P\<rbrace>, spec.term.all A \<tturnstile> spec.seq_ctxt.cl True f', \<lbrace>Q'\<rbrace>"
  shows "f \<bind> g \<le> \<lbrace>P\<rbrace>, A \<tturnstile> spec.seq_ctxt.cl T (f' \<bind> g'), \<lbrace>Q\<rbrace>"
by (strengthen ord_to_strengthen[OF spec.bind.seq_ctxt.cl_le]) (rule refinement.spec.bind[OF assms])

lemma cl_action_permuteL:
  fixes F  :: "('v \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes G  :: "'v \<Rightarrow> ('w \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes G' :: "('v' \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes F' :: "'v' \<Rightarrow> ('w \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes Q :: "'w \<Rightarrow> ('ls \<times> 's) pred"
  assumes F: "\<And>v a s s'. \<lbrakk>P s; (v, a, s, s') \<in> F\<rbrakk> \<Longrightarrow> snd s' = snd s"
  assumes FGG'F': "\<And>v w a a' s s' t. \<lbrakk>P s; (v, a', s, t) \<in> F; (w, a, t, s') \<in> G v\<rbrakk>
                   \<Longrightarrow> \<exists>v' a'' a''' t'. (v', a'', s, t') \<in> G' \<and> (w, a''', t', s') \<in> F' v'
                          \<and> snd s' = snd t' \<and> (snd s \<noteq> snd t' \<longrightarrow> a'' = a)"
  assumes Q: "\<And>v w a a' s s' s''. \<lbrakk>P s; (v, a, s, s') \<in> G'; (w, a', s', s'') \<in> F' v\<rbrakk> \<Longrightarrow> Q w s''"
  shows "spec.action F \<bind> (\<lambda>v. spec.action (G v)) \<le> \<lbrace>P\<rbrace>, A \<tturnstile> spec.seq_ctxt.cl T (spec.action G' \<bind> (\<lambda>v. spec.action (F' v))), \<lbrace>Q\<rbrace>"
apply (strengthen ord_to_strengthen[OF top_greatest[where a=T]])
apply (rule order.trans[OF spec.seq_ctxt.cl_action_permuteL_le[where T=True and F'=F' and G'=G', simplified heyting[symmetric]]])
  apply (erule (1) F)
 apply (drule (2) FGG'F', blast)
apply (simp only: refinement_def spec.pre.next_imp_eq_heyting spec.idle_le inf.bounded_iff)
apply (rule order.trans[OF _ heyting.mono[OF order.refl spec.next_imp.mono[OF top_greatest order.refl]]])
apply (simp add: heyting heyting.detachment spec.seq_ctxt.cl_action_bind_action_pre_post[OF Q])
done

lemma cl_action_permuteR:
  fixes G  :: "('v \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes F  :: "'v \<Rightarrow> ('w \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes F' :: "('v' \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  fixes G' :: "'v' \<Rightarrow> ('w \<times> 'a \<times> ('ls \<times> 's) \<times> ('ls \<times> 's)) set"
  assumes G: "\<And>v a s s'. \<lbrakk>P s; (v, a, s, s') \<in> G; snd s' \<noteq> snd s\<rbrakk>
              \<Longrightarrow> \<exists>v' w a'' t s''. (v', a'', s, t) \<in> F' \<and> (w, a, t, s'') \<in> G' v' \<and> snd t = snd s \<and> snd s'' = snd s'"
  assumes GFF'G': "\<And>v w a a' s s' t. \<lbrakk>P s; (v, a, s, t) \<in> G; (w, a', t, s') \<in> F v\<rbrakk>
                   \<Longrightarrow> snd s' = snd t \<and> (\<exists>v' a'' a''' t'. (v', a'', s, t') \<in> F' \<and> (w, a''', t', s') \<in> G' v'
                                                        \<and> snd t' = snd s \<and> (snd s' \<noteq> snd t' \<longrightarrow> a''' = a))"
  assumes Q: "\<And>v w a a' s s' s''. \<lbrakk>P s; (v, a, s, s') \<in> F'; (w, a', s', s'') \<in> G' v\<rbrakk> \<Longrightarrow> Q w s''"
  shows "spec.action G \<bind> (\<lambda>v. spec.action (F v)) \<le> \<lbrace>P\<rbrace>, A \<tturnstile> spec.seq_ctxt.cl T (spec.action F' \<bind> (\<lambda>v. spec.action (G' v))), \<lbrace>Q\<rbrace>"
apply (strengthen ord_to_strengthen[OF top_greatest[where a=T]])
apply (rule order.trans[OF spec.seq_ctxt.cl_action_permuteR_le[where T=True, simplified heyting[symmetric]]])
  apply (erule (2) G)
 apply (drule (2) GFF'G', blast)
apply (simp only: refinement_def spec.pre.next_imp_eq_heyting spec.idle_le inf.bounded_iff)
apply (rule order.trans[OF _ heyting.mono[OF order.refl spec.next_imp.mono[OF top_greatest order.refl]]])
apply (simp add: heyting heyting.detachment spec.seq_ctxt.cl_action_bind_action_pre_post[OF Q])
done

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "prog"\<close>

lemma localI: \<comment>\<open> Introduce local state \<close>
  fixes A :: "(sequential, 's, 'v) spec"
  fixes c :: "('ls \<times> 's, 'v) prog"
  fixes c' :: "(sequential, 's, 'v) spec"
  fixes P :: "'s pred"
  fixes Q :: "'v \<Rightarrow> 's pred"
  assumes "prog.p2s c \<le> \<lbrace>\<lambda>s. P (snd s)\<rbrace>, spec.localizeA A \<tturnstile> spec.sinvmap snd c', \<lbrace>\<lambda>v s. Q v (snd s)\<rbrace>"
  shows "prog.p2s (prog.local c) \<le> \<lbrace>P\<rbrace>, A \<tturnstile> c', \<lbrace>Q\<rbrace>"
using assms by transfer (erule refinement.spec.localI)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsubsection\<open> Data refinement \label{sec:local_state-data_refinement} \<close>

text\<open>

In this setting a (concrete) specification \<open>c\<close> is a \<^emph>\<open>data refinement\<close> of (abstract) specification
\<open>c'\<close> if:
 \<^item> the observable state changes coincide
 \<^item> concrete local states are mapped to abstract local states by \<open>sf\<close> which then coincide

Observations:
 \<^item> pre/post are in terms of the concrete local states
  \<^item> \<open>sf\<close> can be used to lift these to the abstract local states
 \<^item> we do not require \<open>c\<close> or \<open>c'\<close> to disallow the environment from changing the local state
 \<^item> essentially a Skolemization of Lamport's existentials \<^citep>\<open>\<open>\S8\<close> in "Lamport:1994"\<close>

References:
 \<^item> \<^citet>\<open>\<open>Chapter~14 ``Refinement Methods due to Abadi and Lamport and to Lynch''\<close> in "deRoeverEngelhardt:1998"\<close>
  \<^item> in general \<open>c\<close> will need to be augmented with auxiliary variables

\<close>

setup \<open>Sign.mandatory_path "refinement"\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

lemma data:
  fixes A :: "(sequential, 's, 'v) spec"
  fixes c :: "(sequential, 'cls \<times> 's, 'v) spec"
  fixes c' :: "(sequential, 'als \<times> 's, 'v) spec"
  fixes sf :: "'cls \<Rightarrow> 'als"
  assumes "c \<le> \<lbrace>\<lambda>s. P (snd s)\<rbrace>, spec.localizeA A \<tturnstile> spec.sinvmap (map_prod sf id) c', \<lbrace>\<lambda>v s. Q v (snd s)\<rbrace>"
  shows "spec.local c \<le> \<lbrace>P\<rbrace>, A \<tturnstile> spec.local c', \<lbrace>Q\<rbrace>"
proof -
  have *: "spec.smap snd (spec.local.interference \<sqinter> spec.sinvmap (map_prod sf id) c')
        \<le> spec.smap snd (spec.local.interference \<sqinter> c')" (is "?lhs \<le> ?rhs")
  proof(rule spec.singleton_le_extI)
    show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
      using that
      by (clarsimp simp: spec.singleton.le_conv)
         (fastforce simp: trace.steps'.map spec.local.qrm_def
               simp flip: id_def
                  intro!: exI[where x="trace.map id (map_prod sf id) id \<sigma>'" for \<sigma>'])
  qed
  show ?thesis
    apply (simp only: spec.local_def spec.map_invmap.galois spec.invmap.refinement id_apply)
    apply (subst inf.left_idem[symmetric]) \<comment>\<open> non-linear use of env constraint \<close>
    apply (strengthen ord_to_strengthen(1)[OF assms])
    apply (strengthen ord_to_strengthen(1)[OF refinement.inf_le])
    apply (subst inf.commute)
    apply (subst heyting[symmetric])
    apply (strengthen ord_to_strengthen(2)[OF refinement.heyting_le])
    apply (subst inf.commute, fold spec.localizeA_def)
    apply (rule refinement.mono[OF order.refl _ _ order.refl])
     apply (simp add: spec.localizeA_def; fail)
    apply (simp add: heyting inf.absorb1 * flip: spec.map_invmap.galois)
    done
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "prog"\<close>

lemma data:
  fixes A :: "(sequential, 's, 'v) spec"
  fixes c :: "('cls \<times> 's, 'v) prog"
  fixes c' :: "('als \<times> 's, 'v) prog"
  fixes sf :: "'cls \<Rightarrow> 'als"
  assumes "prog.p2s c \<le> \<lbrace>\<lambda>s. P (snd s)\<rbrace>, spec.localizeA A \<tturnstile> spec.sinvmap (map_prod sf id) (prog.p2s c'), \<lbrace>\<lambda>v s. Q v (snd s)\<rbrace>"
  shows "prog.p2s (prog.local c) \<le> \<lbrace>P\<rbrace>, A \<tturnstile> prog.p2s (prog.local c'), \<lbrace>Q\<rbrace>"
using assms by transfer (erule refinement.spec.data)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Assume/guarantee \label{sec:local_state-ag} \<close>

setup \<open>Sign.mandatory_path "ag"\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

lemma local:
  fixes A G :: "'s rel"
  fixes P :: "'s pred"
  fixes Q :: "'v \<Rightarrow> 's pred"
  fixes c :: "(sequential, 'ls \<times> 's, 'v) spec"
  assumes "c \<le> \<lbrace>\<lambda>s. P (snd s)\<rbrace>, Id \<times>\<^sub>R A \<turnstile> UNIV \<times>\<^sub>R G, \<lbrace>\<lambda>v s. Q v (snd s)\<rbrace>"
  shows "spec.local c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
unfolding spec.local_def
apply (subst spec.map_invmap.galois)
apply (strengthen ord_to_strengthen(1)[OF assms])
apply (subst (1) ag.reflcl_ag)
apply (simp only: spec.invmap.ag inv_image_alt_def map_prod_snd_snd_vimage)
apply (subst inf.commute)
apply (subst heyting[symmetric])
apply (subst spec.local.qrm_def)
apply (subst sequential.range_proc_self)
apply (subst Un_commute, subst ag.assm_heyting)
apply (auto intro: ag.mono)
done

lemma localize_lift:
  fixes A G :: "'s rel"
  fixes P :: "'s \<Rightarrow> bool"
  fixes Q :: "'v \<Rightarrow> 's \<Rightarrow> bool"
  fixes c :: "(sequential, 's, 'v) spec"
  notes inf.bounded_iff[simp del]
  assumes c: "c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "spec.localize UNIV c \<le> \<lbrace>\<lambda>s. P (snd s)\<rbrace>, UNIV \<times>\<^sub>R A \<turnstile> Id \<times>\<^sub>R G, \<lbrace>\<lambda>v s::'ls \<times> 's. Q v (snd s)\<rbrace>"
proof(rule ag.name_pre_state)
  fix s :: "'ls \<times> 's" assume "P (snd s)"
  show "spec.localize UNIV c \<le> \<lbrace>(=) s\<rbrace>, UNIV \<times>\<^sub>R A \<turnstile> Id \<times>\<^sub>R G, \<lbrace>\<lambda>v s. Q v (snd s)\<rbrace>"
apply (strengthen ord_to_strengthen[OF c])
apply (simp add: spec.localize_def spec.invmap.ag inv_image_snd)
apply (simp add: ac_simps ag_def heyting)

\<comment>\<open> discharge pre \<close>
apply (subst (2) inf.commute)
apply (subst (2) inf.commute)
apply (subst inf.assoc)
apply (subst inf.assoc[symmetric])
apply (subst heyting.curry_conv)
apply (subst heyting.discharge)
 apply (simp add: \<open>P (snd s)\<close> predicate1I spec.pre.mono; fail)
apply (simp add: ac_simps)

\<comment>\<open> discarge assume \<close>
apply (subst inf.assoc[symmetric])
apply (subst inf.assoc[symmetric])
apply (subst heyting.discharge)
 apply (force intro: le_infI2 spec.rel.mono)
apply (simp add: ac_simps)

\<comment>\<open> establish post \<close>
apply (subst inf.bounded_iff, rule conjI)
 apply (simp add: le_infI2; fail)

\<comment>\<open> establish guarantee \<close>
apply (force simp: inf.bounded_iff
        simp flip: inf.assoc spec.rel.inf
            intro: le_infI2 spec.rel.mono_reflcl)
done
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "prog"\<close>

lemma local:
  fixes A G :: "'s rel"
  fixes P :: "'s pred"
  fixes Q :: "'v \<Rightarrow> 's pred"
  fixes c :: "('ls \<times> 's, 'v) prog"
  assumes "prog.p2s c \<le> \<lbrace>\<lambda>s. P (snd s)\<rbrace>, Id \<times>\<^sub>R A \<turnstile> UNIV \<times>\<^sub>R G, \<lbrace>\<lambda>v s. Q v (snd s)\<rbrace>"
  shows "prog.p2s (prog.local c) \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
using assms by transfer (rule ag.spec.local)

lemma localize_lift:
  fixes A G :: "'s rel"
  fixes P :: "'s \<Rightarrow> bool"
  fixes Q :: "'v \<Rightarrow> 's \<Rightarrow> bool"
  fixes c :: "('s, 'v) prog"
  assumes "prog.p2s c \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  shows "prog.p2s (prog.localize c) \<le> \<lbrace>\<lambda>s. P (snd s)\<rbrace>, UNIV \<times>\<^sub>R A \<turnstile> Id \<times>\<^sub>R G, \<lbrace>\<lambda>v s. Q v (snd s)\<rbrace>"
using assms by transfer (rule ag.spec.localize_lift)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Specification inhabitation\label{sec:local_state-inhabitation} \<close>

setup \<open>Sign.mandatory_path "inhabits.spec"\<close>

lemma localize:
  assumes "P -s, xs\<rightarrow> P'"
  assumes "Id \<subseteq> r"
  shows "spec.localize r P -(ls, s), map (map_prod id (Pair ls)) xs\<rightarrow> spec.localize r P'"
by (auto intro!: inhabits.inf inhabits.spec.rel.rel
           simp: spec.localize_def assms(1) trace_steps'_map subsetD[OF assms(2)] inhabits.spec.invmap comp_def)

lemma local:
  assumes "P -(ls, s), xs\<rightarrow> spec.return v"
  assumes "trace.steps' (ls, s) xs \<subseteq> spec.local.qrm"
  shows "spec.local P -s, map (map_prod id snd) xs\<rightarrow> spec.return v"
unfolding spec.local_def
by (rule inhabits.spec.map[where af=id and sf=snd and vf=id and s="(ls, s)", simplified])
   (rule inhabits.inf[OF inhabits.spec.rel.rel_term[OF assms(2), where v=v] assms(1), simplified])

lemma local_init:
  assumes "P -(ls, s), xs\<rightarrow> P'"
  assumes "trace.steps' (ls, s) xs \<subseteq> spec.local.qrm"
  shows "spec.local_init a ls P -s, map (map_prod id snd) xs\<rightarrow> spec.local_init a (fst (trace.final' (ls, s) xs)) P'"
proof -
  have "\<lblot>s, map (map_prod id snd) xs, Some ()\<rblot> \<then> spec.local_init a (fst (trace.final' (ls, s) xs)) P'
     \<le> spec.local_init a ls (\<lblot>(ls, s), xs, Some ()\<rblot> \<bind> (\<lambda>_. P'))"
  proof(induct rule: spec.bind_le)
    case incomplete from assms(2) show ?case
      by (fastforce simp: spec.term.none.singleton spec.singleton.local_init_le_conv
                   intro: spec.bind.incompleteI)
  next
    case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v)
    consider (idle) "\<lblot>\<sigma>\<^sub>g\<rblot> \<le> spec.idle"
          | (steps) \<sigma>' where "\<lblot>\<sigma>'\<rblot> \<le> P'"
                         and "trace.steps' (trace.init \<sigma>') (trace.rest \<sigma>') \<subseteq> spec.local.qrm"
                         and  "\<lblot>\<sigma>\<^sub>g\<rblot> \<le> \<lblot>trace.map id snd id \<sigma>'\<rblot>"
                         and "fst (trace.init \<sigma>') = fst (trace.final' (ls, s) xs)"
      using disjE[OF iffD1[OF spec.singleton.local_init_le_conv continue(4)]] by metis
    then show ?case
    proof cases
      case idle with \<open>\<natural>\<sigma>\<^sub>g \<noteq> trace.T (trace.init \<sigma>\<^sub>g) [] None\<close> show ?thesis
        by (simp add: spec.singleton.le_conv spec.singleton.local_init_le_conv
                      trace.natural_def trace.natural'.eq_Nil_conv)
    next
      case (steps \<sigma>')
      let ?\<sigma>' = "trace.T (ls, s) (xs @ trace.rest \<sigma>') (trace.term \<sigma>')"
      from continue(1,2,3) steps(3)
      have *: "snd (trace.final' (ls, s) xs) = snd (trace.init \<sigma>')"
        by (cases \<sigma>'; cases \<sigma>\<^sub>f)
           (clarsimp; metis snd_conv spec.singleton_le_conv trace.natural.sel(1)
                            trace.final'.map trace.final'.natural' trace.less_eqE  trace.t.sel(1))
      with steps(4) have *: "trace.final' (ls, s) xs = trace.init \<sigma>'"
        by (simp add: prod.expand)
      from steps(1) *
      have "\<lblot>?\<sigma>'\<rblot> \<le> \<lblot>(ls, s), xs, Some ()\<rblot> \<then> P'"
        by (simp add: spec.bind.continueI[OF order.refl])
      moreover
      from assms(2) steps(2) *
      have "trace.steps ?\<sigma>' \<subseteq> spec.local.qrm"
        by (simp add: trace.steps'.append)
      moreover
      from continue(1-3) steps *
      have "\<lblot>trace.init \<sigma>\<^sub>f, trace.rest \<sigma>\<^sub>f @ trace.rest \<sigma>\<^sub>g, trace.term \<sigma>\<^sub>g\<rblot> \<le> \<lblot>trace.map id snd id ?\<sigma>'\<rblot>"
        by (auto simp: trace.less_eq_None spec.singleton_le_conv trace.natural_def trace.natural'.append
                 cong: trace.final'.natural'_cong
                 elim: trace.less_eqE)
      ultimately show ?thesis
        by (simp add: spec.singleton.local_init_le_conv exI[where x="?\<sigma>'"])
    qed
  qed
  then show ?thesis
    unfolding inhabits_def
    by (rule order.trans[OF _ spec.local_init.mono[OF assms(1)[unfolded inhabits_def]]])
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "prog.inhabits"\<close>

lemma localize:
  assumes "prog.p2s P -s, xs\<rightarrow> prog.p2s P'"
  shows "prog.p2s (prog.localize P) -(ls, s), map (map_prod id (Pair ls)) xs\<rightarrow> prog.p2s (prog.localize P')"
using assms by transfer (rule inhabits.spec.localize; blast)

lemma local:
  assumes "prog.p2s P -(ls, s), xs\<rightarrow> spec.return v"
  assumes "trace.steps' (ls, s) xs \<subseteq> spec.local.qrm"
  shows "prog.p2s (prog.local P) -s, map (map_prod id snd) xs\<rightarrow> spec.return v"
using assms by transfer (rule inhabits.spec.local)

lemma local_init:
  assumes "prog.p2s P -(ls, s), xs\<rightarrow> prog.p2s P'"
  assumes "trace.steps' (ls, s) xs \<subseteq> spec.local.qrm"
  shows "prog.p2s (prog.local_init ls P) -s, map (map_prod id snd) xs\<rightarrow> prog.p2s (prog.local_init (fst (trace.final' (ls, s) xs)) P')"
using assms by transfer (rule inhabits.spec.local_init)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
