(*<*)
theory Safety_Closure
imports
  ConcurrentHOL.TLS
begin

(*>*)
section\<open> Observations about safety closure\label{sec:safety_closure} \<close>

text\<open>

We demonstrate that \<open>Sup\<close> does not distribute in \<^typ>\<open>('a, 's, 'v) tls\<close> as it does in
\<^typ>\<open>('a, 's, 'v) spec\<close>: specifically a \<open>Sup\<close> of a set of safety properties in the former need not
be a safety property, whereas in the latter it is (see \S\ref{sec:safety_logic-logic}).

\<close>

corec bnats :: "nat \<Rightarrow> ('a \<times> nat, 'v) tllist" where
  "bnats i = TCons (undefined, i) (bnats (Suc i))"

definition bnat :: "('a, nat, 'v) behavior.t" where
  "bnat = behavior.B 0 (bnats 1)"

definition tnats :: "nat \<Rightarrow> nat \<Rightarrow> ('a \<times> nat) list" where
  "tnats i j = map (Pair undefined) (upt i j)"

definition tnat :: "nat \<Rightarrow> ('a, nat, 'v) trace.t" where
  "tnat i = trace.T 0 (tnats (Suc 0) (Suc i)) None"

lemma tnat_simps[simp]:
  shows "tnats i i = []"
    and "trace.init (tnat i) = 0"
    and "trace.rest (tnat i) = tnats 1 (Suc i)"
    and "length (tnats i j) = j - i"
by (simp_all add: tnats_def tnat_def)

lemma take_tnats:
  shows "take i (tnats j k) = tnats j (min (i + j) k)"
by (simp add: tnats_def take_map add.commute split: split_min)

lemma take_tnat:
  shows "trace.take i (tnat j) = tnat (min i j)"
by (simp add: trace.take_def take_tnats tnat_def)

lemma mono_tnat:
  shows "mono tnat"
by (rule monoI) (auto simp: trace.less_eq_take_def take_tnat split: split_min)

lemma final'_tnats:
  shows "trace.final' i (tnats j k) = (if j < k then k - 1 else i)"
by (simp add: tnats_def trace.final'_def comp_def)

lemma sset_tnat:
  shows "trace.sset (tnat i) = {j. j \<le> i}"
by (force simp: tnat_def tnats_def trace.sset.simps)

lemma natural'_tnats:
  shows "trace.natural' i (tnats (Suc i) (Suc j)) = tnats (Suc i) (Suc j)"
proof -
  have "trace.natural' i (map (Pair undefined) (upt (Suc i) (Suc j)))
      = map (Pair undefined) (upt (Suc i) (Suc j))" for j
    by (induct j arbitrary: i) (simp_all add: trace.natural'.append)
  from this show ?thesis unfolding tnats_def .
qed

lemma natural_tnat:
  shows "\<natural>(tnat i) = tnat i"
by (simp add: tnat_def trace.natural_def natural'_tnats del: upt_Suc)

lemma ttake_bnats:
  shows "ttake i (bnats j) = (tnats j (i + j), None)"
by (induct i arbitrary: j) (subst bnats.code; simp add: tnats_def upt_rec)+

lemma take_bnat_tnat:
  shows "behavior.take i bnat = tnat i"
by (simp add: bnat_def tnat_def behavior.take_def ttake_bnats)

unbundle tls.extra_syntax

definition bnat_approx :: "(unit, nat, unit) spec set" where
  "bnat_approx = {\<lblot>behavior.take i bnat\<rblot> |i. True}"

lemma bnat_approx_alt_def:
  shows "bnat_approx = {\<lblot>tnat i\<rblot> |i. True}"
by (simp add: bnat_approx_def take_bnat_tnat)

lemma not_tls_from_spec_Sup_distrib: \<comment>\<open> \<^const>\<open>tls.from_spec\<close> is not \<open>Sup\<close>-distributive \<close>
  shows "\<not>tls.from_spec (\<Squnion>bnat_approx) \<le> \<Squnion>(tls.from_spec ` bnat_approx)" (is "\<not>?lhs \<le> ?rhs")
proof -
  have "\<lblot>bnat\<rblot>\<^sub>T \<le> ?lhs"
  proof -
    have *: "\<exists>j. behavior.take i \<omega> \<in> raw.spec.cl {behavior.take j bnat}" if "bnat \<simeq>\<^sub>T \<omega>"
      for i and \<omega> :: "('a, nat, 'b) behavior.t"
      by (rule behavior.stuttering.equiv.takeE[OF sym[OF that], where i=i])
         (force simp: raw.spec.cl_def simp flip: trace.stuttering.cl.downwards.cl)
    note spec.singleton.transfer[transfer_rule]
    show ?thesis
      unfolding bnat_approx_def
      by transfer
         (force dest: * simp: TLS.raw.singleton_def raw.from_spec_def Safety_Logic.raw.singleton_def
                   simp flip: ex_simps elim!: behavior.stuttering.clE)
  qed
  moreover
  have "\<not>(\<forall>j. tnat j \<le> tnat i)" for i
    by (auto intro!: exI[where x="Suc i"] dest!: monoD[OF trace.sset.mono] simp: sset_tnat)
  then have "\<not>\<lblot>bnat\<rblot>\<^sub>T \<le> ?rhs"
    by (fastforce simp: bnat_approx_def tls.singleton.le_conv spec.singleton_le_conv take_bnat_tnat natural_tnat)
  ultimately show ?thesis
    by (blast dest: order.trans)
qed

definition bnat' :: "(unit, nat, unit) tls set" where
  "bnat' = tls.from_spec ` bnat_approx"

lemma not_tls_safety_cl_Sup_distrib: \<comment>\<open> \<^const>\<open>tls.safety.cl\<close> is not \<open>Sup\<close>-distributive \<close>
  shows "\<not>tls.safety.cl (\<Squnion>bnat') \<le> \<Squnion>(tls.safety.cl ` bnat')"
proof -
  have "(\<Squnion>x\<in>bnat_approx. tls.to_spec (tls.from_spec x)) = \<Squnion>bnat_approx" (is "?lhs = ?rhs")
  proof(rule antisym)
    show "?lhs \<le> ?rhs"
      by (simp add: Sup_upper2 tls.safety.lower_upper_contractive)
  have "\<exists>\<omega> ia ib. (\<forall>i. \<natural> (behavior.take i \<omega>) \<le> tnat ib) \<and> tnat i = behavior.take ia \<omega>"
   for i
    by (rule exI[where x="behavior.B 0 (tshift2 (tnats (Suc 0) (Suc i), None) (trepeat (undefined, i)))"])
       (force simp: behavior.take.tshift ttake_trepeat trace.take.continue take_tnat
                    trace.natural.continue trace.natural'.replicate natural_tnat not_le final'_tnats
         simp flip: tnat_def
             split: split_min
             intro: monoD[OF mono_tnat])
  then show "?rhs \<le> ?lhs"
    by (clarsimp simp: bnat_approx_alt_def spec.singleton.le_conv tls.singleton.le_conv
                       spec.singleton_le_conv natural_tnat
            simp flip: ex_simps;
        fast)
  qed
  then show ?thesis
    by (simp add: bnat'_def tls.safety.cl_def tls.safety.upper_lower_upper tls.to_spec.Sup
                  not_tls_from_spec_Sup_distrib image_image)
qed

definition cl_bnat' :: "(unit, nat, unit) tls set" where
  "cl_bnat' = tls.safety.cl ` bnat'"

lemma not_tls_safety_closed_Sup:
  shows "cl_bnat' \<subseteq> tls.safety.closed"
    and "\<Squnion>cl_bnat' \<notin> tls.safety.closed"
unfolding cl_bnat'_def
using not_tls_safety_cl_Sup_distrib
by (blast intro: tls.safety.expansive complete_lattice_class.Sup_mono
           dest: tls.safety.least[rotated, where x="\<Squnion>bnat'"])+

paragraph\<open> Negation does not preserve \<^const>\<open>tls.safety.closed\<close> \<close>

notepad
begin

have "tls.always (tls.state_prop id) \<in> tls.safety.closed"
by (simp add: tls.safety.closed.always tls.safety.closed.state_prop)

have "-tls.always (tls.state_prop id) \<notin> tls.safety.closed"
proof -
  let ?P = "behavior.B True (trepeat (undefined, True)) :: ('a, bool, 'c) behavior.t"
  have "\<exists>\<omega>'. behavior.take i ?P = behavior.take i \<omega>'
           \<and> (\<exists>j \<omega>''. behavior.dropn j \<omega>' = Some \<omega>'' \<and> \<not> behavior.init \<omega>'')"
   for i
    by (auto simp: behavior.dropn.continue behavior.take.continue behavior.take.trepeat
                   trace.take.replicate case_tllist_trepeat
                   exI[where x="behavior.take i ?P @-\<^sub>B trepeat (undefined, False)"]
                   exI[where x="Suc i"])
  then have "\<lblot>?P\<rblot>\<^sub>T \<le> tls.safety.cl (-tls.always (tls.state_prop id))"
    by (clarsimp simp: tls.singleton.le_conv; fast)
  moreover
  have "behavior.init \<omega>'"
    if "behavior.dropn i (behavior.B True (trepeat (undefined, True))) = Some \<omega>'"
  for i and \<omega>' :: "('a, bool, 'c) behavior.t"
    using that
    by (cases i) (auto simp: behavior.dropn_alt_def tdropn_trepeat case_tllist_trepeat)
  then have "\<not>\<lblot>?P\<rblot>\<^sub>T \<le> -tls.always (tls.state_prop id)"
    by (auto simp: tls.singleton.le_conv)
  ultimately show ?thesis
    using tls.safety.le_closedE by blast
qed

end

subsection\<open> Liveness\label{sec:safety_closure-liveness} \<close>

text\<open>

Famously arbitrary properties on infinite sequences can be decomposed into \<^emph>\<open>safety\<close> and \<^emph>\<open>liveness\<close>
properties. The latter have been identified with the topologically dense sets.

References:
 \<^item> \<^citet>\<open>"AlpernSchneider:1985" and "Schneider:1987"\<close>: topological account
 \<^item> \<^citet>\<open>"Kindler:1994"\<close>: overview
 \<^item> \<^citet>\<open>\<open>\S8.5.3\<close> in "Lynch:1996"\<close>
 \<^item> \<^citet>\<open>"ManoliosTrefler:2003"\<close>: lattice-theoretic account
 \<^item> \<^citet>\<open>"Maier:2004"\<close>: an intuitionistic semantics for LTL (including next/X/\<open>\<circle>\<close>) over finite and infinite sequences

\<close>

setup \<open>Sign.mandatory_path "raw.safety"\<close>

lemma dense_alt_def: \<comment>\<open> \<^citet>\<open>\<open>\S8.5.3 Liveness Property\<close> in "Lynch:1996"\<close> \<close>
  shows "(raw.safety.dense :: ('a, 's, 'v) behavior.t set set)
       = {P. \<forall>\<sigma>. \<exists>xsv. \<sigma> @-\<^sub>B xsv \<in> P}" (is "?lhs = ?rhs")
proof(rule antisym)
  have "\<exists>xsv. \<sigma> @-\<^sub>B xsv \<in> P" if "raw.safety.cl P = UNIV" for P and \<sigma> :: "('a, 's, 'v) trace.t"
    using that
    by (auto simp: behavior.take.continue
        simp flip: trace.take.Ex_all
            elim!: raw.safety.cl_altE[where i="Suc (length  (trace.rest \<sigma>))"]
            dest!: subsetD[where c="\<sigma> @-\<^sub>B TNil undefined", OF Set.equalityD2])
       (metis behavior.continue.take_drop_id behavior.continue.tshift2)
  then show "?lhs \<subseteq> ?rhs"
    by (clarsimp simp: raw.safety.dense_def)
next
  have "\<omega> \<in> raw.safety.cl P" if "\<forall>\<sigma>. \<exists>xsv. \<sigma> @-\<^sub>B xsv \<in> P" for P and \<omega> :: "('a, 's, 'v) behavior.t"
  proof(rule raw.safety.cl_altI)
    fix i
    from spec[OF that, where x="behavior.take i \<omega>"]
    obtain xsv where "behavior.take i \<omega> @-\<^sub>B xsv \<in> P" ..
    moreover
    have "behavior.take i \<omega> = behavior.take i (behavior.take i \<omega> @-\<^sub>B xsv)"
      by (clarsimp simp: behavior.take.continue behavior.take.all_continue
                         trace.take.behavior.take length_ttake not_le
                  split: enat.split split_min)
    ultimately show "\<exists>\<omega>'\<in>P. behavior.take i \<omega> = behavior.take i \<omega>'" ..
  qed
  then show "?rhs \<subseteq> ?lhs"
    by (auto simp: raw.safety.dense_def)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "tls"\<close>

definition live :: "('a, 's, 'v) tls set" where
  "live = tls.safety.dense"

setup \<open>Sign.mandatory_path "live"\<close>

lemma not_bot:
  shows "\<bottom> \<notin> tls.live"
by (simp add: tls.live_def tls.safety.dense_def tls.bot_not_top)

lemma top:
  shows "\<top> \<in> tls.live"
by (simp add: tls.live_def tls.safety.dense_top)

lemma live_le:
  assumes "P \<in> tls.live"
  assumes "P \<le> Q"
  shows "Q \<in> tls.live"
using assms by (simp add: tls.live_def tls.safety.dense_le)

lemma inf_safety_eq_top: \<comment>\<open> \<^citet>\<open>\<open>Theorem~8.8\<close> in "Lynch:1996"\<close> \<close>
  shows "tls.live \<sqinter> tls.safety.closed = {\<top>}"
unfolding tls.live_def by (rule tls.safety.dense_inf_closed)

lemma terminating:
  shows "tls.eventually tls.terminated \<in> tls.live"
by (simp add: tls.live_def tls.safety.dense_def tls.safety.cl.eventually[OF tls.terminated.not_bot])

text\<open>

However this definition of liveness does not endorse traditional \<^emph>\<open>response\<close> properties.

\<close>

\<comment>\<open> direct counterexample \<close>
corec alternating :: "bool \<Rightarrow> ('a \<times> bool, 'b) tllist" where
  "alternating b = TCons (undefined, b) (alternating (\<not>b))"

abbreviation (input) "A b \<equiv> behavior.B b (tls.live.alternating (\<not>b))"

lemma dropn_alternating:
  shows "behavior.dropn i (tls.live.A b) = Some (tls.live.A (if even i then b else \<not>b))"
proof(induct i arbitrary: b)
  case (Suc i) show ?case
    by (subst tls.live.alternating.code) (simp add: behavior.dropn.Suc  Suc[of "\<not>b", simplified])
qed simp

notepad
begin

let ?P = "tls.leads_to (tls.state_prop id) (tls.state_prop Not) :: ('a, bool, unit) tls"
let ?\<omega> = "\<lblot>behavior.B True (TNil ())\<rblot>\<^sub>T :: ('a, bool, unit) tls"

have "\<not>?\<omega> \<le> ?P"
  by (auto simp: tls.singleton.le_conv split: nat.split)
then have "\<not>?\<omega> \<le> tls.safety.cl ?P"
  by (simp add: tls.safety.cl.terminated_iff tls.singleton.terminated_le_conv behavior.sset.simps)
then have "?P \<notin> tls.live"
  by (auto simp: tls.live_def tls.safety.dense_def
           dest: order.trans[where a="?\<omega>", OF top_greatest eq_refl[OF sym]])

\<comment>\<open> non-triviality \<close>
let ?\<omega>' = "\<lblot>tls.live.A True\<rblot>\<^sub>T :: ('a, bool, unit) tls"
have "?\<omega>' \<le> ?P"
  by (clarsimp simp: tls.singleton.le_conv tls.live.dropn_alternating[where b=True, simplified]) presburger

\<comment>\<open> intuition: there's some safety in these response properties \<close>
let ?Q = "tls.always (tls.terminated \<^bold>\<longrightarrow>\<^sub>B tls.state_prop Not) :: ('a, bool, unit) tls"
have "?Q \<in> tls.safety.closed"
  by (simp add: tls.safety.closed.always tls.safety.closed.boolean_implication
                tls.safety.closed.not_terminated tls.safety.closed.state_prop)
moreover have "\<not>?\<omega> \<le> ?Q"
  by (auto simp: tls.singleton.le_conv behavior.sset.simps split: nat.split)
then have "?Q \<noteq> \<top>"
  by (auto dest: order.trans[where a="?\<omega>", OF top_greatest eq_refl[OF sym]])
ultimately have "?Q \<notin> tls.live"
  using tls.live.inf_safety_eq_top by auto
moreover
  have "tls.terminated \<sqinter> (tls.state_prop id \<^bold>\<longrightarrow>\<^sub>B tls.eventually (tls.state_prop Not)) \<le> tls.state_prop Not"
    by (simp add: boolean_implication.conv_sup inf_sup_distrib tls.state_prop.simps tls.terminated.inf_eventually)
  then have "?P \<le> ?Q"
    by - (rule tls.always.mono;
          simp add: tls.terminated.inf_always flip: boolean_implication.shunt2)
ultimately have "?P \<notin> tls.live"
  by (blast dest: tls.live.live_le)

end

setup \<open>Sign.parent_path\<close>

paragraph\<open> The famous decomposition \<close>

definition Safe :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" where
  "Safe P = tls.safety.cl P"

definition Live :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" where
  "Live P = P \<squnion> -tls.safety.cl P"

lemma decomp:
  shows "P = tls.Safe P \<sqinter> tls.Live P"
by (simp add: tls.Safe_def tls.Live_def boolean_algebra.conj_disj_distrib inf.absorb2 tls.safety.expansive)

setup \<open>Sign.mandatory_path "safety.closed"\<close>

lemma Safe:
  shows "tls.Safe P \<in> tls.safety.closed"
by (simp add: tls.Safe_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "live"\<close>

lemma Live:
  shows "tls.Live P \<in> tls.live"
by (simp add: tls.live_def tls.safety.dense_def tls.Live_def sup_shunt tls.safety.cl.sup tls.safety.expansive)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
