(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory KBPsAuto
imports
  Extra
  KBPs
begin
(*>*)

section\<open>Automata Synthesis\<close>

text\<open>

\label{sec:kbps-automata-synthesis}

Our attention now shifts to showing how we can synthesise standard
automata that \emph{implement} a JKBP under certain conditions. We
proceed by defining \emph{incremental views} following
\<^cite>\<open>"Ron:1996"\<close>, which provide the interface between the system and
these automata. The algorithm itself is presented in
\S\ref{sec:kbps-alg}.

\<close>

subsection\<open>Incremental views\<close>

text\<open>

\label{sec:kbps-environments}

Intuitively an agent instantaneously observes the system state, and so
must maintain her view of the system \emph{incrementally}: her new
view must be a function of her current view and some new
observation. We allow this observation to be an arbitrary projection
@{term "envObs a"} of the system state for each agent @{term "a"}:

\<close>

locale Environment =
  PreEnvironment jkbp envInit envAction envTrans envVal
    for jkbp :: "('a, 'p, 'aAct) JKBP"
    and envInit :: "'s list"
    and envAction :: "'s \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's"
    and envVal :: "'s \<Rightarrow> 'p \<Rightarrow> bool"
+ fixes envObs :: "'a \<Rightarrow> 's \<Rightarrow> 'obs"

text\<open>

An incremental view therefore consists of two functions with these
types:

\<close>

type_synonym ('a, 'obs, 'tv) InitialIncrJointView = "'a \<Rightarrow> 'obs \<Rightarrow> 'tv"
type_synonym ('a, 'obs,  'tv) IncrJointView = "'a \<Rightarrow> 'obs \<Rightarrow> 'tv \<Rightarrow> 'tv"

text\<open>

These functions are required to commute with their corresponding
trace-based joint view in the obvious way:

\<close>

locale IncrEnvironment =
  Environment jkbp envInit envAction envTrans envVal envObs
+ PreEnvironmentJView jkbp envInit envAction envTrans envVal jview
    for jkbp :: "('a, 'p, 'aAct) JKBP"
    and envInit :: "'s list"
    and envAction :: "'s \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's"
    and envVal :: "'s \<Rightarrow> 'p \<Rightarrow> bool"
    and jview :: "('a, 's, 'tv) JointView"
    and envObs :: "'a \<Rightarrow> 's \<Rightarrow> 'obs"
+ fixes jviewInit :: "('a, 'obs, 'tv) InitialIncrJointView"
  fixes jviewIncr :: "('a, 'obs, 'tv) IncrJointView"
  assumes jviewInit: "\<forall>a s. jviewInit a (envObs a s) = jview a (tInit s)"
  assumes jviewIncr: "\<forall>a t s. jview a (t \<leadsto> s)
                             = jviewIncr a (envObs a s) (jview a t)"

text\<open>

Armed with these definitions, the following sections show that there
are automata that implement a JKBP in a given environment.

\<close>

subsection\<open>Automata\<close>

text\<open>

Our implementations of JKBPs take the form of deterministic Moore
automata, where transitions are labelled by observation and states
with the action to be performed. We will use the term \emph{protocols}
interchangeably with automata, following the KBP literature, and adopt
\emph{joint protocols} for the assignment of one such to each agent:

\<close>

record ('obs, 'aAct, 'ps) Protocol =
  pInit :: "'obs \<Rightarrow> 'ps"
  pTrans :: "'obs \<Rightarrow> 'ps \<Rightarrow> 'ps"
  pAct :: "'ps \<Rightarrow> 'aAct list"

type_synonym ('a, 'obs, 'aAct, 'ps) JointProtocol
    = "'a \<Rightarrow> ('obs, 'aAct, 'ps) Protocol"

context IncrEnvironment
begin

text\<open>

To ease composition with the system we adopt the function @{term
"pInit"} which maps the initial observation to an initial automaton
state.

\<^citet>\<open>"Ron:1996"\<close> shows that even non-deterministic JKBPs can be
implemented with deterministic transition functions; intuitively all
relevant uncertainty the agent has about the system must be encoded
into each automaton state, so there is no benefit to doing this
non-deterministically. In contrast we model the non-deterministic
choice of action by making @{term "pAct"} a relation.

Running a protocol on a trace is entirely standard, as is running a
joint protocol, and determining their actions:

\<close>

fun runJP :: "('a, 'obs, 'aAct, 'ps) JointProtocol
           \<Rightarrow> 's Trace \<Rightarrow> 'a \<Rightarrow> 'ps"
where
  "runJP jp (tInit s) a = pInit (jp a) (envObs a s)"
| "runJP jp (t \<leadsto> s) a = pTrans (jp a) (envObs a s) (runJP jp t a)"

abbreviation actJP :: "('a, 'obs, 'aAct, 'ps) JointProtocol
                    \<Rightarrow> 's Trace \<Rightarrow> 'a \<Rightarrow> 'aAct list" where
  "actJP jp \<equiv> \<lambda>t a. pAct (jp a) (runJP jp t a)"

text \<open>

Similarly to \S\ref{sec:kbps-canonical-kripke} we will reason about
the set of traces generated by a joint protocol in a fixed
environment:

\<close>

inductive_set
  jpTraces :: "('a, 'obs, 'aAct, 'ps) JointProtocol \<Rightarrow> 's Trace set"
    for jp :: "('a, 'obs, 'aAct, 'ps) JointProtocol"
where
  "s \<in> set envInit \<Longrightarrow> tInit s \<in> jpTraces jp"
| "\<lbrakk> t \<in> jpTraces jp; eact \<in> set (envAction (tLast t));
     \<And>a. aact a \<in> set (actJP jp t a); s = envTrans eact aact (tLast t) \<rbrakk>
     \<Longrightarrow> t \<leadsto> s \<in> jpTraces jp"
(*<*)

declare jpTraces.intros[intro]

lemma jpTraces_init_inv[dest]:
  "tInit s \<in> jpTraces jp \<Longrightarrow> s \<in> set envInit"
  by (cases rule: jpTraces.cases) auto

lemma jpTraces_step_inv[dest]:
  "t \<leadsto> s \<in> jpTraces jp
    \<Longrightarrow> t \<in> jpTraces jp
     \<and> (\<exists>eact \<in> set (envAction (tLast t)).
        (\<exists>aact. (\<forall>a. aact a \<in> set (actJP jp t a))
          \<and> s = envTrans eact aact (tLast t)))"
  by (cases rule: jpTraces.cases) auto

lemma jpTraces_init_length_inv:
  "t \<in> jpTraces jp \<Longrightarrow> (tLength t = 0) \<longleftrightarrow> (\<exists>s. s \<in> set envInit \<and> t = tInit s)"
  by (induct t) (auto elim: jpTraces.cases)

lemma jpTraces_step_length_inv_aux:
  "t \<in> { t \<in> jpTraces jp . tLength t = Suc n }
    \<Longrightarrow> \<exists>t' s. t = t' \<leadsto> s
            \<and> t' \<in> jpTraces jp
            \<and> tLength t' = n
            \<and> (\<exists>eact \<in> set (envAction (tLast t')).
               (\<exists>aact. (\<forall>a. aact a \<in> set (actJP jp t' a))
                 \<and> s = envTrans eact aact (tLast t')))"
  by (induct t arbitrary: n) auto

lemma jpTraces_step_length_inv:
  "{ t \<in> jpTraces jp . tLength t = Suc n }
 = { t \<leadsto> s |eact aact t s. t \<in> { t \<in> jpTraces jp . tLength t = n }
              \<and> eact \<in> set (envAction (tLast t))
              \<and> (\<forall>a. aact a \<in> set (actJP jp t a))
              \<and> s = envTrans eact aact (tLast t) }"
  apply (rule set_eqI)
  apply rule
   apply (drule jpTraces_step_length_inv_aux)
   apply auto
  done
(*>*)

end (* context IncrEnvironment *)

subsection\<open>The Implementation Relation\<close>

text\<open>

\label{sec:kbps-implementation}

With this machinery in hand, we now relate automata with JKBPs. We say
a joint protocol @{term "jp"} \emph{implements} a JKBP when they
perform the same actions on the canonical of traces. Note that the
behaviour of @{term "jp"} on other traces is arbitrary.

\<close>

context IncrEnvironment
begin

definition
  implements :: "('a, 'obs, 'aAct, 'ps) JointProtocol \<Rightarrow> bool"
where
  "implements jp \<equiv> (\<forall>t \<in> jkbpC. set \<circ> actJP jp t = set \<circ> jAction MC t)"

text\<open>

Clearly there are environments where the canonical trace set @{term
"jkbpC"} can be generated by actions that differ from those prescribed
by the JKBP. We can show that the \emph{implements} relation is a
stronger requirement than the mere trace-inclusion required by the
\emph{represents} relation of \S\ref{sec:kbps-canonical-kripke}.

\<close>
(*<*)

lemma implementsI[intro]:
  "(\<And>t. t \<in> jkbpC \<Longrightarrow> set \<circ> actJP jp t = set \<circ> jAction MC t)
  \<Longrightarrow> implements jp"
  unfolding implements_def by simp

lemma implementsE[elim]:
  assumes impl: "implements jp"
      and tC: "t \<in> jkbpC"
     shows "set \<circ> actJP jp t = set \<circ> jAction MC t"
  using assms unfolding implements_def by simp

lemma implements_actJP_jAction:
   assumes impl: "implements jp"
       and tCn: "t \<in> jkbpCn n"
  shows "set (actJP jp t a) = set (jAction (MCn n) t a)" (is "?lhs = ?rhs")
proof -
  from tCn have tC: "t \<in> jkbpC" by blast
  hence "?lhs = (set \<circ> jAction MC t) a"
    using implementsE[OF impl, symmetric] by auto
  also have "... = set (jAction (MCn n) t a)"
    by (simp add: jkbpC_jkbpCn_jAction_eq[OF tCn])
  finally show ?thesis .
qed

(*>*)
lemma implements_represents:
  assumes impl: "implements jp"
  shows "represents (jpTraces jp)"
(*<*)
proof -
  { fix n
    have "{ t \<in> jpTraces jp . tLength t = n }
        = { t \<in> jkbpC . tLength t = n }"
    proof(induct n)
      case 0 thus ?case
        by (auto dest: jpTraces_init_length_inv iff: jkbpC_traces_of_length)
    next
      case (Suc n)
      hence indhyp: "{t \<in> jpTraces jp . tLength t = n} = jkbpCn n"
        by (simp add: jkbpC_traces_of_length)

      have "{t \<in> jpTraces jp. tLength t = Suc n}
          = {t \<leadsto> s |eact aact t s. t \<in> jkbpCn n
                      \<and> eact \<in> set (envAction (tLast t))
                      \<and> (\<forall>a. aact a \<in> set (actJP jp t a))
                      \<and> s = envTrans eact aact (tLast t) }"
        using indhyp by (simp add: jpTraces_step_length_inv)
      also have "... = jkbpCn (Suc n)"
        apply (auto iff: Let_def)
        apply (auto iff: implements_actJP_jAction[OF impl, symmetric])
        done
      finally show ?case by (auto iff: jkbpC_traces_of_length)
    qed }
  hence R: "jpTraces jp = jkbpC" by auto
  from R jkbpC_represents
  show "represents (jpTraces jp)" by simp
qed

lemma implements_ind_jkbpC:
  assumes acts: "\<And>a n t.
                  \<lbrakk> {t \<in> jpTraces jp. tLength t = n} = jkbpCn n; t \<in> jkbpCn n \<rbrakk>
                  \<Longrightarrow> actJP jp t a = jAction MC t a"
  shows "implements jp"
proof -
  let ?T = "jpTraces jp"

  from acts have acts':
      "\<And>n t. \<lbrakk> {t \<in> jpTraces jp. tLength t = n} = jkbpCn n; t \<in> jkbpCn n \<rbrakk>
          \<Longrightarrow> actJP jp t = jAction (MCn n) t"
    by (simp only: jkbpC_jkbpCn_jAction_eq)

  from acts have acts':
      "\<And>n t. \<lbrakk> {t \<in> jpTraces jp. tLength t = n} = jkbpCn n; t \<in> jkbpCn n \<rbrakk>
          \<Longrightarrow> actJP jp t = jAction (MCn n) t"
    apply -
    apply (rule ext)
    apply simp
    using jkbpC_jkbpCn_jAction_eq
    apply simp
    done

  { fix n
    have "{ t \<in> ?T . tLength t = n } = { t \<in> jkbpC . tLength t = n }"
    proof(induct n)
      case 0 thus ?case
        by (auto dest: jpTraces_init_length_inv iff: jkbpC_traces_of_length)
    next
      case (Suc n)
      hence indhyp: "{t \<in> ?T. tLength t = n} = jkbpCn n"
        by (simp add: jkbpC_traces_of_length)

      have "{t \<in> jpTraces jp. tLength t = Suc n}
          = {t \<leadsto> s |eact aact t s. t \<in> jkbpCn n
                      \<and> eact \<in> set (envAction (tLast t))
                      \<and> (\<forall>a. aact a \<in> set (actJP jp t a))
                      \<and> s = envTrans eact aact (tLast t) }"
        using indhyp by (simp add: jpTraces_step_length_inv)
      also have "... = jkbpCn (Suc n)"
        apply (auto iff: Let_def)
         apply (drule acts'[OF indhyp, symmetric])
         apply auto[1]
        apply (drule acts'[OF indhyp, symmetric])
        apply auto[1]
        done
      finally show ?case
        apply (auto iff: jkbpC_traces_of_length)
        done
    qed
    hence "\<forall>t\<in>jkbpCn n. actJP jp t = jAction (MCn n) t"
      apply clarsimp
      apply (rule acts')
       apply (auto iff: jkbpC_traces_of_length)
      done
    hence "\<forall>t\<in>jkbpCn n. actJP jp t = jAction MC t"
      apply clarsimp
      by ( rule sync_jview_jAction_eq[where n="n"]
         , auto iff: jkbpC_traces_of_length)
  }
  thus ?thesis
    unfolding implements_def jkbpC_def
    apply clarsimp
    done
qed

(*>*)
text\<open>

The proof is by a straightfoward induction over the lengths of traces
generated by the joint protocol.

Our final piece of technical machinery allows us to refine automata
definitions: we say that two joint protocols are \emph{behaviourally
equivalent} if the actions they propose coincide for each canonical
trace. The implementation relation is preserved by this relation.

\<close>

definition
  behaviourally_equiv :: "('a, 'obs, 'aAct, 'ps) JointProtocol
                        \<Rightarrow> ('a, 'obs, 'aAct, 'ps') JointProtocol
                        \<Rightarrow> bool"
where
  "behaviourally_equiv jp jp' \<equiv> \<forall>t \<in> jkbpC. set \<circ> actJP jp t = set \<circ> actJP jp' t"

(*<*)
lemma behaviourally_equivI[intro]:
  "(\<And>t. t \<in> jkbpC \<Longrightarrow> set \<circ> actJP jp t = set \<circ> actJP jp' t)
    \<Longrightarrow> behaviourally_equiv jp jp'"
  unfolding behaviourally_equiv_def by simp
(*>*)

lemma behaviourally_equiv_implements:
  assumes "behaviourally_equiv jp jp'"
  shows "implements jp \<longleftrightarrow> implements jp'"
(*<*)
  using assms unfolding behaviourally_equiv_def implements_def by simp
(*>*)
text\<open>\<close>

end (* context IncrEnvironment *)

(* **************************************** *)

subsection\<open>Automata using Equivalence Classes\<close>

text\<open>

We now show that there is an implementation of every JKBP with respect
to every incremental synchronous view. Intuitively the states of the
automaton for agent @{term "a"} represent the equivalence classes of
traces that @{term "a"} considers possible, and the transitions update
these sets according to her KBP.

\<close>

context IncrEnvironment
begin

definition
  mkAutoEC :: "('a, 'obs, 'aAct, 's Trace set) JointProtocol"
where
  "mkAutoEC \<equiv> \<lambda>a.
     \<lparr> pInit = \<lambda>obs. { t \<in> jkbpC . jviewInit a obs = jview a t },
       pTrans = \<lambda>obs ps. { t |t t'. t \<in> jkbpC \<and> t' \<in> ps
                                 \<and> jview a t = jviewIncr a obs (jview a t') },
       pAct = \<lambda>ps. jAction MC (SOME t. t \<in> ps) a \<rparr>"

text\<open>

The function \<open>SOME\<close> is Hilbert's indefinite description
operator @{term "\<epsilon>"}, used here to choose an arbitrary trace from the
protocol state.

That this automaton maintains the correct equivalence class on a trace
@{term "t"} follows from an easy induction over @{term "t"}.

\<close>

lemma mkAutoEC_ec:
  assumes "t \<in> jkbpC"
  shows "runJP mkAutoEC t a = { t' \<in> jkbpC . jview a t' = jview a t }"
(*<*)
  using assms
  apply (induct t)
   apply (auto simp add: mkAutoEC_def jviewInit)[1]
  apply simp
  apply (subst mkAutoEC_def)
  apply (auto iff: Let_def jviewIncr)
  done
(*>*)

text\<open>

We can show that the construction yields an implementation by
appealing to the previous lemma and showing that the @{term "pAct"}
functions coincide.

\<close>

lemma mkAutoEC_implements: "implements mkAutoEC"
(*<*)
  apply (rule implements_ind_jkbpC)
  apply (subst mkAutoEC_def)
  apply simp
  apply (subgoal_tac "t \<in> jkbpC")
   using mkAutoEC_ec
   apply simp
   apply (rule S5n_jAction_eq)
    apply simp_all
    apply (rule_tac a=t in someI2)
     apply simp_all
    unfolding mkM_def
    apply auto
   done
(*>*)

text\<open>

This definition leans on the canonical trace set jkbpC, and is indeed
effective: we can enumerate all canonical traces and are sure to find
one that has the view we expect. Then it is sufficient to consider
other traces of the same length due to synchrony.  We would need to do
this computation dynamically, as the automaton will (in general) have
an infinite state space.

\<close>

end (* context IncrEnvironment *)

(* **************************************** *)

subsection\<open>Simulations\<close>

text\<open>
\label{sec:kbps-theory-automata-env-sims}

Our goal now is to reduce the space required by the automaton
constructed by @{term "mkAutoEC"} by \emph{simulating} the equivalence
classes (\S\ref{sec:kripke-theory-simulations}).

The following locale captures the framework of \<^citet>\<open>"Ron:1996"\<close>:

\<close>

locale SimIncrEnvironment =
  IncrEnvironment jkbp envInit envAction envTrans envVal jview envObs
                  jviewInit jviewIncr
    for jkbp :: "('a, 'p, 'aAct) JKBP"

    and envInit :: "'s list"
    and envAction :: "'s \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's"
    and envVal :: "'s \<Rightarrow> 'p \<Rightarrow> bool"
    and jview :: "('a, 's, 'tv) JointView"
    and envObs :: "'a \<Rightarrow> 's \<Rightarrow> 'obs"
    and jviewInit :: "('a, 'obs, 'tv) InitialIncrJointView"
    and jviewIncr :: "('a, 'obs, 'tv) IncrJointView"
+ fixes simf :: "'s Trace \<Rightarrow> 'ss"
  fixes simRels :: "'a \<Rightarrow> 'ss Relation"
  fixes simVal :: "'ss \<Rightarrow> 'p \<Rightarrow> bool"
  assumes simf: "sim MC (mkKripke (simf ` jkbpC) simRels simVal) simf"

context SimIncrEnvironment
begin

text\<open>

Note that the back tick \<open>`\<close> is Isabelle/HOL's relational image
operator. In context it says that @{term "simf"} must be a simulation
from @{term "jkbpC"} to its image under @{term "simf"}.

Firstly we lift our familiar canonical trace sets and Kripke
structures through the simulation.

\<close>

abbreviation jkbpCSn :: "nat \<Rightarrow> 'ss set"(*<*)(\<open>jkbpCS\<^bsub>_\<^esub>\<close>)(*>*) where
  "jkbpCS\<^bsub>n\<^esub> \<equiv> simf ` jkbpC\<^bsub>n\<^esub>"

abbreviation jkbpCS :: "'ss set" where
  "jkbpCS \<equiv> simf ` jkbpC"

abbreviation MCSn :: "nat \<Rightarrow> ('a, 'p, 'ss) KripkeStructure"(*<*)(\<open>MCS\<^bsub>_\<^esub>\<close>)(*>*) where
  "MCS\<^bsub>n\<^esub> \<equiv> mkKripke jkbpCS\<^bsub>n\<^esub> simRels simVal"

abbreviation MCS :: "('a, 'p, 'ss) KripkeStructure" where
  "MCS \<equiv> mkKripke jkbpCS simRels simVal"
(*<*)
lemma jkbpCSn_jkbpCS_subset:
  "jkbpCSn n \<subseteq> jkbpCS"
  by (rule image_mono[OF jkbpCn_jkbpC_subset])

(*>*)
text\<open>

We will be often be concerned with the equivalence class of traces
generated by agent @{term "a"}'s view:

\<close>

abbreviation sim_equiv_class :: "'a \<Rightarrow> 's Trace \<Rightarrow> 'ss set" where
  "sim_equiv_class a t \<equiv> simf ` { t' \<in> jkbpC . jview a t' = jview a t }"

abbreviation jkbpSEC :: "'ss set set" where
  "jkbpSEC \<equiv> \<Union>a. sim_equiv_class a ` jkbpC"

text\<open>

With some effort we can show that the temporal slice of the simulated
structure is adequate for determining the actions of the JKBP. The
proof is tedious and routine, exploiting the sub-model property
(\S\ref{sec:generated_models}).

\<close>
(*<*)

lemma sim_submodel_aux:
  assumes s: "s \<in> worlds (MCSn n)"
  shows "gen_model MCS s = gen_model (MCSn n) s"
proof(rule gen_model_subset[where T="jkbpCSn n"])
  from s show "s \<in> worlds MCS"
    by (simp add: subsetD[OF jkbpCSn_jkbpCS_subset])
  from s show "s \<in> worlds (MCSn n)" by assumption
next
  fix a
  show "relations MCS a \<inter> jkbpCSn n \<times> jkbpCSn n
      = relations (MCSn n) a \<inter> jkbpCSn n \<times> jkbpCSn n"
    by (simp add: Int_ac Int_absorb1
                  relation_mono[OF jkbpCSn_jkbpCS_subset jkbpCSn_jkbpCS_subset])
next
  from s
  show "(\<Union>a. relations (MCSn n) a)\<^sup>* `` {s} \<subseteq> jkbpCSn n"
    apply (clarsimp simp del: mkKripke_simps)
    apply (erule kripke_rels_trc_worlds)
    apply auto
    done
next
  from s obtain t
    where st: "s = simf t"
      and tCn: "t \<in> jkbpCn n"
    by fastforce
  from tCn have tC: "t \<in> jkbpC" by blast
  { fix t'
    assume tt': "(t, t') \<in> (\<Union>a. relations MC a)\<^sup>*"
    from tC tt' have t'C: "t' \<in> jkbpC"
      by - (erule kripke_rels_trc_worlds, simp_all)
    from tCn tt' have t'Len: "tLength t' = n"
      by (auto dest: sync_tLength_eq_trc[where as=UNIV])
    from t'C t'Len have "t' \<in> jkbpCn n"
      by - (erule jkbpC_tLength_inv) }
  hence "(\<Union>a. relations MC a)\<^sup>* `` {t} \<subseteq> jkbpCn n"
    by clarsimp
  hence "simf ` ((\<Union>a. relations MC a)\<^sup>* `` {t}) \<subseteq> jkbpCSn n"
    by (rule image_mono)
  with st tC
  show "(\<Union>a. relations MCS a)\<^sup>* `` {s} \<subseteq> jkbpCSn n"
    using sim_trc_commute[OF _ simf, where t=t]
    by simp
qed simp_all
(*>*)

lemma jkbpC_jkbpCSn_jAction_eq:
  assumes tCn: "t \<in> jkbpCn n"
  shows "jAction MC t = jAction (MCSn n) (simf t)"
(*<*) (is "?lhs = ?rhs")
proof -
  have "?lhs = jAction MCS (simf t)"
    by (simp add: simulation_jAction_eq simf jkbpCn_jkbpC_inc[OF tCn])
  also have "... = ?rhs"
    using tCn
    by - ( rule gen_model_jAction_eq[OF sim_submodel_aux, where w="simf t"]
         , auto intro: gen_model_world_refl )
  finally show ?thesis .
qed
(*>*)

end (* context SimIncrEnvironment *)

text\<open>

It can be shown that a suitable simulation into a finite structure is
adequate to establish the existence of finite-state implementations
\<^citep>\<open>\<open>Theorem~2\<close> in "Ron:1996"\<close>: essentially we apply the simulation to
the states of @{term "mkAutoEC"}. However this result does not make it
clear how the transition function can be incrementally
constructed. One approach is to maintain @{term "jkbpC"} while
extending the automaton, which is quite space inefficient.

Intuitively we would like to compute the possible @{term
"sim_equiv_class"} successors of a given @{term "sim_equiv_class"}
without reference to @{term "jkbpC"}, and this should be possible as
the reachable simulated worlds must contain enough information to
differentiate themselves from every other simulated world (reachable
or not) that represents a trace that is observationally distinct to
their own.

This leads us to asking for some extra functionality of our
simulation, which we do in the following section.

\<close>

subsection\<open>Automata using simulations\<close>

text_raw\<open>
\label{sec:kbps-automata-synthesis-alg}

\begin{figure}[hp]
\begin{isabellebody}%
\<close>
locale AlgSimIncrEnvironment =
  SimIncrEnvironment jkbp envInit envAction envTrans envVal
                     jview envObs jviewInit jviewIncr simf simRels simVal
    for jkbp :: "('a, 'p, 'aAct) JKBP"
    and envInit :: "'s list"
    and envAction :: "'s \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's"
    and envVal :: "'s \<Rightarrow> 'p \<Rightarrow> bool"

    and jview :: "('a, 's, 'tv) JointView"
    and envObs :: "'a \<Rightarrow> 's \<Rightarrow> 'obs"
    and jviewInit :: "('a, 'obs, 'tv) InitialIncrJointView"
    and jviewIncr :: "('a, 'obs, 'tv) IncrJointView"

    and simf :: "'s Trace \<Rightarrow> 'ss"
    and simRels :: "'a \<Rightarrow> 'ss Relation"
    and simVal :: "'ss \<Rightarrow> 'p \<Rightarrow> bool"

+ fixes simAbs :: "'rep \<Rightarrow> 'ss set"

    and simObs :: "'a \<Rightarrow> 'rep \<Rightarrow> 'obs"
    and simInit :: "'a \<Rightarrow> 'obs \<Rightarrow> 'rep"
    and simTrans :: "'a \<Rightarrow> 'rep \<Rightarrow> 'rep list"
    and simAction :: "'a \<Rightarrow> 'rep \<Rightarrow> 'aAct list"

  assumes simInit:
            "\<forall>a iobs. iobs \<in> envObs a ` set envInit
                   \<longrightarrow> simAbs (simInit a iobs)
                     = simf ` { t' \<in> jkbpC. jview a t' = jviewInit a iobs }"
      and simObs:
            "\<forall>a ec t. t \<in> jkbpC \<and> simAbs ec = sim_equiv_class a t
                   \<longrightarrow> simObs a ec = envObs a (tLast t)"
      and simAction:
            "\<forall>a ec t. t \<in> jkbpC \<and> simAbs ec = sim_equiv_class a t
                   \<longrightarrow> set (simAction a ec) = set (jAction MC t a)"
      and simTrans:
            "\<forall>a ec t. t \<in> jkbpC \<and> simAbs ec = sim_equiv_class a t
                   \<longrightarrow> simAbs ` set (simTrans a ec)
                     = { sim_equiv_class a (t' \<leadsto> s)
                         |t' s. t' \<leadsto> s \<in> jkbpC \<and> jview a t' = jview a t }"
text_raw\<open>
\end{isabellebody}%
\begin{isamarkuptext}%
\caption{The \<open>SimEnvironment\<close> locale extends the @{term
"Environment"} locale with simulation and algorithmic operations. The
backtick \<open>`\<close> is Isabelle/HOL's image-of-a-set-under-a-function
operator.}
\label{fig:kbps-theory-auto-SimEnvironment}
\end{isamarkuptext}%
\end{figure}
\<close>

text\<open>

The locale in Figure~\ref{fig:kbps-theory-auto-SimEnvironment} captures
our extra requirements of a simulation.

Firstly we relate the concrete representation @{typ "'rep"} of
equivalence classes under simulation to differ from the abstract
representation @{typ "'ss set"} using the abstraction function @{term
"simAbs"} \<^citep>\<open>"EdR:cup98"\<close>; there is no one-size-fits-all concrete
representation, as we will see.

Secondly we ask for a function @{term "simInit a iobs"} that
faithfully generates a representation of the equivalence class of
simulated initial states that are possible for agent @{term "a"} given
the valid initial observation @{term "iobs"}.

Thirdly the @{term "simObs"} function allows us to partition the
results of @{term "simTrans"} according to the recurrent observation
that agent @{term "a"} makes of the equivalence class.

Fourthly, the function @{term "simAction"} computes a list of actions
enabled by the JKBP on a state that concretely represents a canonical
equivalence class.

Finally we expect to compute the list of represented @{term
"sim_equiv_class"} successors of a given @{term "sim_equiv_class"}
using @{term "simTrans"}.

Note that these definitions are stated relative to the environment and
the JKBP, allowing us to treat specialised cases such as broadcast
(\S\ref{sec:kbps-theory-spr-deterministic-protocols} and
\S\ref{sec:kbps-theory-spr-non-deterministic-protocols}).

With these functions in hand, we can define our desired automaton:

\<close>

definition (in AlgSimIncrEnvironment)
  mkAutoSim :: "('a, 'obs, 'aAct, 'rep) JointProtocol"
where
  "mkAutoSim \<equiv> \<lambda>a.
     \<lparr> pInit = simInit a,
       pTrans = \<lambda>obs ec. (SOME ec'. ec' \<in> set (simTrans a ec)
                                  \<and> simObs a ec' = obs),
       pAct = simAction a \<rparr>"
(*<*)

context AlgSimIncrEnvironment
begin

lemma jAction_simAbs_cong:
  assumes tC: "t \<in> jkbpC"
      and ec: "simAbs ec = sim_equiv_class a t"
      and ec': "simAbs ec = simAbs ec'"
  shows "set (simAction a ec) = set (simAction a ec')"
  using assms simAction[rule_format, where a=a and t=t] tC by simp

lemma simTrans_simAbs_cong:
  assumes tC: "t \<in> jkbpC"
      and ec: "simAbs ec = sim_equiv_class a t"
      and ec': "simAbs ec = simAbs ec'"
  shows "simAbs ` set (simTrans a ec) = simAbs ` set (simTrans a ec')"
  using assms simTrans[rule_format, where a=a and t=t] tC by simp

lemma mkAutoSim_simps[simp]:
  "pInit (mkAutoSim a) = simInit a"
  "pTrans (mkAutoSim a) = (\<lambda>obs ec. (SOME ec'. ec' \<in> set (simTrans a ec) \<and> simObs a ec' = obs))"
  "pAct (mkAutoSim a) = simAction a"
  unfolding mkAutoSim_def by simp_all

end (* context AlgSimIncrEnvironment *)

(*>*)
text\<open>

The automaton faithfully constructs the simulated equivalence class of
the given trace:

\<close>

lemma (in AlgSimIncrEnvironment) mkAutoSim_ec:
  assumes tC: "t \<in> jkbpC"
  shows "simAbs (runJP mkAutoSim t a) = sim_equiv_class a t"
(*<*)
using tC
proof(induct t)
  case (tInit s) thus ?case
    by (simp add: jviewInit[rule_format, symmetric] simInit)
next
  case (tStep t s)
  hence tC: "t \<in> jkbpC" by blast

      from tC tStep
      have F: "simAbs ` set (simTrans a (runJP mkAutoSim t a))
             = { sim_equiv_class a (t' \<leadsto> s)
                 |t' s. t' \<leadsto> s \<in> jkbpC \<and> jview a t' = jview a t}"
        using simTrans[rule_format, where a=a and t=t and ec="runJP mkAutoSim t a"]
        apply clarsimp
        done

      from tStep
      have G: "sim_equiv_class a (t \<leadsto> s)
             \<in> { sim_equiv_class a (t' \<leadsto> s)
                |t' s. t' \<leadsto> s \<in> jkbpC \<and> jview a t' = jview a t}"
        by auto

      from F G
      have H: "sim_equiv_class a (t \<leadsto> s) \<in> simAbs ` set (simTrans a (runJP mkAutoSim t a))"
        by simp

      then obtain r
        where R: "r \<in> set (simTrans a (runJP mkAutoSim t a))"
        and S: "simAbs r = sim_equiv_class a (t \<leadsto> s)"
        by auto

  show ?case
  proof(simp, rule someI2)
    from R S tStep tC
    show "r \<in> set (simTrans a (runJP mkAutoSim t a)) \<and> simObs a r = envObs a s"
      using simObs[rule_format, where t="t\<leadsto>s" and a=a]
      apply clarsimp
      done
  next
    fix x assume x: "x \<in> set (simTrans a (runJP mkAutoSim t a)) \<and> simObs a x = envObs a s"

    from x
    have A: "simObs a x = envObs a s" by simp

    from x
    have "simAbs x \<in> simAbs ` set (simTrans a (runJP mkAutoSim t a))" by simp
    with tStep tC
    have "simAbs x \<in> { sim_equiv_class a (t' \<leadsto> s)
                         |t' s. t' \<leadsto> s \<in> jkbpC \<and> jview a t' = jview a t}"
      using simTrans[rule_format, where a=a and t=t] by simp
    then obtain t' s'
      where X: "simAbs x = sim_equiv_class a (t' \<leadsto> s')"
          and Y: "t' \<leadsto> s' \<in> jkbpC"
          and Z: "jview a t' = jview a t"
      by auto

    from A X Y Z
    show "simAbs x = sim_equiv_class a (t \<leadsto> s)"
      using simObs[rule_format, where a=a and t="t'\<leadsto>s'", symmetric]
      by (simp add: jviewIncr)
  qed
qed

(*>*)
text\<open>

This follows from a simple induction on @{term "t"}.

The following is a version of the Theorem 2 of \<^citet>\<open>"Ron:1996"\<close>.

\<close>

theorem (in AlgSimIncrEnvironment) mkAutoSim_implements:
  "implements mkAutoSim"
(*<*)
  apply rule
  apply rule
  apply (auto dest: jkbpCn_jkbpC_inc iff: mkAutoSim_ec simAction)
  done
(*>*)

text\<open>

The reader may care to contrast these structures with the
\emph{progression structures} of \<^citet>\<open>"Ron:1997"\<close>, where states
contain entire Kripke structures, and expanding the automaton is
alternated with bisimulation reduction to ensure termination when a
finite-state implementation exists (see \S\ref{sec:kbps-alg-auto-min})
We also use simulations in Appendix~\ref{ch:complexity} to show the
complexity of some related model checking problems.

We now review a simple \emph{depth-first search} (DFS) theory, and an
abstraction of finite maps, before presenting the algorithm for KBP
synthesis.

\FloatBarrier

\<close>

(*<*)
end
(*>*)
