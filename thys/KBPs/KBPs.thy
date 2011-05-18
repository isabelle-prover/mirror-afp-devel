(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory KBPs
imports Main Kripke Traces
begin

record ('a, 'p, 'aAct) GC =
  guard  :: "('a, 'p) Kform"
  action :: "'aAct"

type_synonym ('a, 'p, 'aAct) KBP = "('a, 'p, 'aAct) GC list"

(* The following syntactic restriction implies the desired semantic
property, that we can evaluate a guard at an arbitrary world that is
compatible with a given observation
\cite[p204]{DBLP:journals/dc/FaginHMV97}. *)

fun subjective :: "'a \<Rightarrow> ('a, 'p) Kform \<Rightarrow> bool"
where
  "subjective a (Kprop p)      = False"
| "subjective a (Knot f)       = subjective a f"
| "subjective a (Kand f g)     = (subjective a f \<and> subjective a g)"
| "subjective a (Knows a' f)   = (a = a')"

lemma S5n_subjective_eq:
  assumes S5n: "S5n M"
      and subj: "subjective a \<phi>"
      and ww': "(w, w') \<in> relations M a"
  shows "M, w \<Turnstile> \<phi> \<longleftrightarrow> M, w' \<Turnstile> \<phi>"
  using subj ww'
  by (induct \<phi> rule: subjective.induct) (auto dest: S5n_rels_eq[OF S5n])

(*>*)section {*Semantics of Knowledge-Based Programs*}

text{*

\label{sec:kbps-logic-of-knowledge}
\label{sec:semantics}

We use what is now a standard account of the multi-agent (multi-modal)
propositional logic of knowledge \cite{Chellas:1980,FHMV:1995}. The
language of the guards is propositional, augmented by one knowledge
modality per agent and parameterised by a type @{typ "'p"} of
propositions and @{typ "'a"} of agents:
\[@{term "\<phi>"} ::= @{text "p | \<not>\<phi> | \<phi> \<and> \<phi> | \<^bold>K\<^bsub>a\<^esub>\<^sub> \<phi>"}\]

Formulas are interpreted with respect to a \emph{Kripke structure}, which
consists of a set of worlds of type @{typ "'w"}, an equivalence
relation @{text "\<sim>\<^sub>a"} for each agent @{term "a"} over these worlds,
and a way of evaluating propositions at each world; these are
collected in a record of type @{typ "('a, 'p, 'w)
KripkeStructure"}. We define satisfaction of a formula @{term "\<phi>"} at
a world @{term "w"} in structure @{term "M"} as follows:
\begin{center}
 \begin{tabular}{l@ {~~iff~~}l}
   @{text "M, w \<Turnstile> p"} & @{term "p"} is true at @{term "w"} in @{term "M"}\\
   @{text "M, w \<Turnstile> \<not>\<phi>"} & @{term "M, w \<Turnstile> \<phi>"} is false\\
   @{text "M, w \<Turnstile> \<phi> \<and> \<psi>"} & @{term "M, w \<Turnstile> \<phi>"} \mbox{and} @{term "M, w \<Turnstile> \<psi>"}\\
   @{text "M, w \<Turnstile> \<^bold>K\<^bsub>a\<^esub>\<^sub> \<phi>"} & @{term "M, w' \<Turnstile> \<phi>"} for all worlds @{text "w'"} where @{text "w \<sim>\<^sub>a w'"} in  @{term "M"}
 \end{tabular}
\end{center}
Intuitively @{text "w \<sim>\<^sub>a w'"} if @{term "a"} cannot distinguish
between worlds @{term "w"} and @{term "w'"}; the final clause
expresses the idea that an agent knows @{term "\<psi>"} iff @{term "\<psi>"} is
true at all worlds she considers possible (relative to world @{term
"w"})\footnote{As one would expect there has been extensive debate
over the properties of knowledge; the reader is encouraged to consult
\cite[Chapter~2]{FHMV:1995}. Also their Chapter~7 presents a more
general (but non-algorithmic) account of KBPs at a less harried
pace.}. This semantics supports nested modal operators, so, for
example, ``the sender does not know that the receiver knows the bit
that was sent'' can be expressed.

\label{sec:kbps-theory-kbps-semantics}

We represent a \emph{knowledge-based program} (KBP) of type @{typ
"('a, 'p, 'aAct) KBP"} as a list of records with fields @{term
"guard"} and @{term "action"}, where the guards are knowledge
formulas and the actions elements of the @{typ "'aAct"} type, and
expect there to be one per agent. Lists are used here and elsewhere to
ease the generation of code (see \S\ref{sec:kbps-spr-single-agent-rep}
and \S\ref{sec:perspective}). The function @{term "set"} maps a list
to the set of its elements.

Note that the robot of \S\ref{sec:robot-example} cannot directly
determine its exact position because of the noise in its sensor, which
means that we cannot allow arbitrary formulas as guards. However an
agent $a$ \emph{can} evaluate formulas of the form
$\mathbf{K}_a$@{term "\<psi>"} that depend only on the equivalence class of
worlds $a$ considers possible. That @{term "\<phi>"} is a boolean
combination of such formulas is denoted by @{term "subjective a \<phi>"}.

\label{sec:kbps-theory-environments}
\label{sec:kbps-environments}

We model the agents' interactions using a \emph{finite environment},
following van der Meyden \cite{Ron:1996}, which consist of a finite
type @{typ "'s"} of states, a set @{term "envInit"} of initial states,
a function @{term "envVal"} that evaluates propositions at each state,
and a projection @{term "envObs"} that captures how each agent
instantaneously observes these states. The system evolves using the
transition function @{term "envTrans"}, which incorporates the
environment's non-deterministic choice of action @{term "envAction"}
and those of the agents' KBPs into a global state change. We collect
these into an Isabelle locale:

*}

locale Environment =
  fixes jkbp :: "'a \<Rightarrow> ('a, 'p, 'aAct) KBP"
    and envInit :: "('s :: finite) list"
    and envAction :: "'s \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's"
    and envVal :: "'s \<Rightarrow> 'p \<Rightarrow> bool"
    and envObs :: "'a \<Rightarrow> 's \<Rightarrow> 'obs"
  assumes subj: "\<forall>a gc. gc \<in> set (jkbp a) \<longrightarrow> subjective a (guard gc)"
(*<*)
begin
  (*>*)

text{*

A locale defines a scope where the desired types, variables and
assumptions are fixed and can be freely appealed to. Later we can
instantiate these in various ways (see \S\ref{sec:kbps-alg}) and also
extend the locale (see \S\ref{sec:kripke-simulations}).

In the @{text "Environment"} locale we compute the actions enabled at
world @{term "w"} in an arbitrary Kripke structure @{term "M"} for
each agent using a list comprehension:

*}

definition jAction :: "('a, 'p, 'w) KripkeStructure \<Rightarrow> 'w \<Rightarrow> 'a \<Rightarrow> 'aAct list" where
  "jAction M w a \<equiv> [ action gc. gc \<leftarrow> jkbp a, (M, w \<Turnstile> guard gc) ]"
(*<*)

lemma S5n_jAction_eq:
  assumes S5n: "S5n M"
      and ww': "(w, w') \<in> relations M a"
  shows "jAction M w a = jAction M w' a"
proof -
  { fix gc assume "gc \<in> set (jkbp a)"
    with subj have "subjective a (guard gc)" by auto
    with S5n ww' have "M, w \<Turnstile> guard gc = M, w' \<Turnstile> guard gc"
      by - (rule S5n_subjective_eq, simp_all) }
  thus ?thesis
    unfolding jAction_def
    apply -
    apply (rule arg_cong[where f=concat])
    apply auto
    done
qed

(* Also the JKBP behaves the same on relevant @{term "sub_model"}s for
all agents, and its behaviour is preserved by simulation. *)

lemma sub_model_jAction_eq:
  assumes S: "sub_model M w = sub_model M' w"
      and w': "w' \<in> worlds (sub_model M' w)"
      and M: "kripke M"
      and M': "kripke M'"
  shows "jAction M w' = jAction M' w'"
  apply (rule ext)
  unfolding jAction_def
  by (auto iff: sub_model_eq[OF M M' S w'])

lemma simulation_jAction_eq:
  assumes M: "kripke M"
      and sim: "sim M M' f"
      and w: "w \<in> worlds M"
  shows "jAction M w = jAction M' (f w)"
  apply (rule ext)
  unfolding jAction_def
  using assms by (auto iff: sim_semantic_equivalence)
(*>*)

text{*

\label{sec:kbps-views}

This function composes with @{term "envTrans"} provided we can find a
suitable Kripke structure and world. With the notional mutual
dependency between knowledge and action of \S\ref{sec:introduction} in
mind, this structure should be based on the set of traces generated by
@{term "jkbp"} in this particular environment, i.e., the very thing we
are in the process of defining. As with all fixpoints there may be
zero, one or many solutions; the following construction considers a
broadly-applicable special case for which unique solutions exist.

We represent the possible evolutions of the system as finite sequences
of states, represented by a left-recursive type @{typ "'s Trace"} with
constructors @{term "tInit s"} and @{term "t \<leadsto> s"}, equipped with
@{term "tFirst"}, @{term "tLast"}, @{term "tLength"} and @{term
"tMap"} functions.

Our construction begins by deriving a Kripke structure from an
arbitrary set of traces @{term "T"}. The equivalence relation on these
traces can be defined in a variety of ways \cite{FHMV:1995,Ron:1996};
here we derive the relation from the \emph{synchronous perfect-recall
(SPR) view}, which records all observations made by an agent:

*}

definition spr_jview :: "'a \<Rightarrow> 's Trace \<Rightarrow> 'obs Trace" where
  "spr_jview a \<equiv> tMap (envObs a)"
(*<*)

lemma spr_jview_length_eq:
  "tLength (spr_jview a t) = tLength t"
  unfolding spr_jview_def by simp

lemma spr_jview_tInit_inv[simp]:
  "spr_jview a t = tInit obs \<longleftrightarrow> (\<exists>s. t = tInit s \<and> envObs a s = obs)"
  unfolding spr_jview_def by (cases t, simp_all)

lemma spr_jview_tStep_eq_inv:
  "spr_jview a t' = spr_jview a (t \<leadsto> s) \<Longrightarrow> \<exists>t'' s'. t' = t'' \<leadsto> s'"
  unfolding spr_jview_def by (cases t', simp_all)

lemma spr_jview_prefix_closed[dest]:
  "spr_jview a (t \<leadsto> s) = spr_jview a (t' \<leadsto> s') \<Longrightarrow> spr_jview a t = spr_jview a t'"
  unfolding spr_jview_def by simp

lemma spr_sync:
  assumes "spr_jview a t = spr_jview a t'"
  shows "tLength t = tLength t'"
  using assms spr_jview_length_eq[where a=a, symmetric] by simp

lemma spr_tFirst[dest]:
  assumes v: "spr_jview a t = spr_jview a t'"
  shows "envObs a (tFirst t) = envObs a (tFirst t')"
  using spr_sync[OF v] v
  apply (induct rule: trace_induct2)
  apply (simp_all add: spr_jview_def)
  done

lemma spr_tLast[dest]:
  assumes v: "spr_jview a t = spr_jview a t'"
  shows "envObs a (tLast t) = envObs a (tLast t')"
  using spr_sync[OF v] v
  apply (induct rule: trace_induct2)
  apply (simp_all add: spr_jview_def)
  done

definition mkM :: "'s Trace set \<Rightarrow> ('a, 'p, 's Trace) KripkeStructure" where
  "mkM T \<equiv>
      \<lparr> worlds = T,
        relations = \<lambda>a. { (t, t') . t \<in> T \<and> t' \<in> T \<and> spr_jview a t = spr_jview a t' },
        valuation = envVal \<circ> tLast \<rparr>"

lemma mkM_kripke[intro, simp]: "kripke (mkM T)"
  unfolding mkM_def by (rule kripkeI) fastsimp

lemma mkM_S5n[intro, simp]: "S5n (mkM T)"
  unfolding mkM_def
  by (rule S5nI, rule equivI)
     (bestsimp intro: equivI refl_onI symI transI)+

lemma mkM_simps[simp]:
  "worlds (mkM T) = T"
  "\<lbrakk> (t, t') \<in> relations (mkM T) a \<rbrakk> \<Longrightarrow> spr_jview a t = spr_jview a t'"
  "\<lbrakk> (t, t') \<in> relations (mkM T) a \<rbrakk> \<Longrightarrow> t \<in> T"
  "\<lbrakk> (t, t') \<in> relations (mkM T) a \<rbrakk> \<Longrightarrow> t' \<in> T"
  "valuation (mkM T) = envVal \<circ> tLast"
  unfolding mkM_def by simp_all

lemma mkM_rel_length[simp]:
  assumes tt': "(t, t') \<in> relations (mkM T) a"
  shows "tLength t' = tLength t"
proof -
  from tt' have "spr_jview a t = spr_jview a t'" by simp
  thus ?thesis by (rule spr_sync[symmetric])
qed
(*>*)

text{*

\label{sec:kbps-canonical-kripke}

The Kripke structure @{text "mkM T"} relates all traces that have the
same SPR view, and evaluates propositions at the final state of the
trace, i.e., @{term "envVal \<circ> tLast"}. In general we apply the
adjective ``synchronous'' to relations that ``tell the time'' by
distinguishing all traces of distinct lengths.

Using this structure we construct the sequence of \emph{temporal
slices} that arises from interpreting @{term "jkbp"} with respect to
@{term "T"} by recursion over the time:

*}

fun jkbpTn :: "nat \<Rightarrow> 's Trace set \<Rightarrow> 's Trace set"(*<*)("jkbpT\<^bsub>_\<^esub>")(*>*) where
  "jkbpT\<^bsub>0\<^esub> T      = { tInit s |s. s \<in> set envInit }"
| "jkbpT\<^bsub>Suc n\<^esub> T = { t \<leadsto> envTrans eact aact (tLast t) |t eact aact.
                             t \<in> jkbpT\<^bsub>n\<^esub> T \<and> eact \<in> set (envAction (tLast t))
                          \<and> (\<forall>a. aact a \<in> set (jAction (mkM T) t a)) }"
(*<*)

definition jkbpT :: "'s Trace set \<Rightarrow> 's Trace set" where "jkbpT T \<equiv> \<Union>n. jkbpT\<^bsub>n\<^esub> T"

definition represents :: "'s Trace set \<Rightarrow> bool" where
  "represents T \<equiv> jkbpT T = T"

lemma jkbpTn_length[simp]:
  "t \<in> jkbpTn n T \<Longrightarrow> tLength t = n"
  by (induct n arbitrary: t, auto)

lemma jkbpT_tLength_inv:
  "\<lbrakk> t \<in> jkbpT T; tLength t = n \<rbrakk> \<Longrightarrow> t \<in> jkbpTn n T"
  unfolding jkbpT_def
  by (induct n arbitrary: t, fastsimp+)

lemma jkbpT_traces_of_length:
   "{ t \<in> jkbpT T . tLength t = n } = jkbpTn n T"
  using jkbpT_tLength_inv
  unfolding jkbpT_def by bestsimp

lemma representsI:
  "jkbpT T = T \<Longrightarrow> represents T"
  unfolding represents_def by simp

lemma representsD:
  "represents T \<Longrightarrow> jkbpT T = T"
  unfolding represents_def by simp

lemma sync_tLength_eq_trc:
  assumes "(t, t') \<in> (\<Union>a\<in>as. relations (mkM T) a)\<^sup>*"
  shows "tLength t = tLength t'"
  using assms by (induct rule: rtrancl_induct) auto

lemma sync_sub_model_tLength:
  assumes traces: "{ t \<in> T . tLength t = n } = { t \<in> T' . tLength t = n }"
      and tT: "t \<in> { t \<in> T . tLength t = n }"
  shows "sub_model (mkM T) t = sub_model (mkM T') t"
  apply(rule sub_model_subset[where T="{ t \<in> T . tLength t = n }"])
  apply simp_all

  (* t \<in> T and t \<in> T' *)
  prefer 4
  using tT
  apply simp
  prefer 4
  using tT traces
  apply simp

  apply (unfold mkM_def)[1]
  using tT traces
  apply (auto)[1]

  using tT
  apply (auto dest: sync_tLength_eq_trc[where as=UNIV] kripke_rels_trc_worlds)[1]

  using tT traces
  apply (auto dest: sync_tLength_eq_trc[where as=UNIV] kripke_rels_trc_worlds)[1]

  done

lemma sync_jview_jAction_eq:
  assumes traces: "{ t \<in> T . tLength t = n } = { t \<in> T' . tLength t = n }"
      and tT: "t \<in> { t \<in> T . tLength t = n }"
  shows "jAction (mkM T) t = jAction (mkM T') t"
  apply (rule sub_model_jAction_eq[where w=t])
  apply (rule sync_sub_model_tLength)
  using assms
  apply (auto intro: sub_model_world_refl)
  done

(*>*)text{*

\label{sec:kripke-sub-models}
\label{sec:kbps-canonical-traces}
\label{sec:kbps-representation}

We define @{term "jkbpT T"} to be @{thm (rhs) jkbpT_def}. This gives
us a closure condition on sets of traces @{term "T"}: we say that
@{term "T"} \emph{represents} @{term "jkbp"} if it is equal to @{term
"jkbpT T"}. Exploiting the synchrony of the SPR view, we can
inductively construct traces of length $n + 1$ by interpreting @{term
"jkbp"} with respect to all those of length $n$:

*}

fun jkbpCn :: "nat \<Rightarrow> 's Trace set"(*<*)("jkbpC\<^bsub>_\<^esub>")(*>*) where
  "jkbpC\<^bsub>0\<^esub>      = { tInit s |s. s \<in> set envInit }"
| "jkbpC\<^bsub>Suc n\<^esub> = { t \<leadsto> envTrans eact aact (tLast t) |t eact aact.
                             t \<in> jkbpC\<^bsub>n\<^esub> \<and> eact \<in> set (envAction (tLast t))
                          \<and> (\<forall>a. aact a \<in> set (jAction (mkM jkbpC\<^bsub>n\<^esub>) t a)) }"
(*<*)

abbreviation mkMCn :: "nat \<Rightarrow> ('a, 'p, 's Trace) KripkeStructure" ("mkMC\<^bsub>_\<^esub>") where
  "mkMC\<^bsub>n\<^esub> \<equiv> mkM jkbpC\<^bsub>n\<^esub>"

lemma jkbpCn_step_inv:
  "t \<leadsto> s \<in> jkbpCn (Suc n) \<Longrightarrow> t \<in> jkbpCn n"
  by (induct n arbitrary: t, (fastsimp simp add: Let_def)+)

lemma jkbpCn_length[simp]:
  "t \<in> jkbpCn n \<Longrightarrow> tLength t = n"
  by (induct n arbitrary: t, (fastsimp simp add: Let_def)+)

lemma jkbpCn_init_inv[intro]:
  "tInit s \<in> jkbpCn n \<Longrightarrow> s \<in> set envInit"
   by (frule jkbpCn_length) auto

lemma jkbpCn_tFirst_init_inv[intro]:
 "t \<in> jkbpCn n \<Longrightarrow> tFirst t \<in> set envInit"
  by (induct n arbitrary: t) (auto iff: Let_def)

definition jkbpC :: "'s Trace set" where "jkbpC \<equiv> \<Union>n. jkbpC\<^bsub>n\<^esub>"
abbreviation "mkMC \<equiv> mkM jkbpC"

lemma jkbpCn_jkbpC_subset:
  "jkbpCn n \<subseteq> jkbpC"
  unfolding jkbpC_def by blast

lemma jkbpCn_jkbpC_inc[intro]:
  "t \<in> jkbpCn n \<Longrightarrow> t \<in> jkbpC"
  unfolding jkbpC_def by best

lemma jkbpC_tLength_inv[intro]:
  "\<lbrakk> t \<in> jkbpC; tLength t = n \<rbrakk> \<Longrightarrow> t \<in> jkbpCn n"
  unfolding jkbpC_def
  by (induct n arbitrary: t, (fastsimp simp add: Let_def)+)

lemma jkbpC_traces_of_length:
   "{ t \<in> jkbpC . tLength t = n } = jkbpCn n"
  unfolding jkbpC_def by bestsimp

lemma jkbpC_prefix_closed[dest]:
  "t \<leadsto> s \<in> jkbpC \<Longrightarrow> t \<in> jkbpC"
  apply (drule jkbpC_tLength_inv)
   apply simp
  apply (auto iff: Let_def jkbpC_def)
  done

lemma jkbpC_init[iff]:
  "tInit s \<in> jkbpC \<longleftrightarrow> s \<in> set envInit"
  unfolding jkbpC_def
  apply rule
   apply (fast)
  apply (subgoal_tac "tInit s \<in> jkbpCn 0")
   apply simp
  apply (rule_tac x=0 in exI)
  apply simp_all
  done

lemma jkbpC_jkbpCn_rels:
  "\<lbrakk> (u, v) \<in> relations mkMC a; tLength u = n \<rbrakk>
    \<Longrightarrow> (u, v) \<in> relations (mkMCn n) a"
  unfolding mkM_def
  apply clarsimp
  apply (drule spr_sync)
  apply auto
  done

lemma jkbpC_tFirst_init_inv[intro]:
  "t \<in> jkbpC \<Longrightarrow> tFirst t \<in> set envInit"
  unfolding jkbpC_def by blast

lemma jkbpC_jkbpCn_jAction_eq:
  assumes tCn: "t \<in> jkbpCn n"
  shows "jAction mkMC t = jAction (mkMCn n) t"
  using assms
  by - (rule sync_jview_jAction_eq, auto iff: jkbpC_traces_of_length)

lemma jkbpTn_jkbpCn_represents:
  "jkbpT\<^bsub>n\<^esub> jkbpC = jkbpC\<^bsub>n\<^esub>"
  apply (induct n)
   apply simp
  apply (auto iff: Let_def jkbpC_jkbpCn_jAction_eq)
  apply blast+
  done

(*>*)
text{*

We define @{term "mkMC\<^bsub>n\<^esub>"} to be @{text "mkM jkbpC\<^bsub>n\<^esub>"}, and @{term
"jkbpC"} to be @{text "\<Union>n. jkbpC\<^bsub>n\<^esub>"} with corresponding Kripke
structure @{term "mkMC"}.

We show that @{thm (concl) jkbpC_jkbpCn_jAction_eq} for @{term "t \<in>
jkbpCn n"}, i.e., that the relevant temporal slice suffices for
computing @{term "jAction"}, by appealing to a multi-modal
generalisation of the \emph{generated model property}
\cite[\S3.4]{Chellas:1980}. This asserts that the truth of a formula
at a world $w$ depends only on the worlds reachable from $w$ in zero
or more steps, using any of the agents' accessibility relations at
each step. We then establish that @{thm jkbpTn_jkbpCn_represents} by
induction on @{term "n"}, implying that @{term "jkbpC"} represents
@{term "jkbp"} in the environment of interest. Uniqueness follows by a
similar argument, and so:
\begin{theorem}
  The set @{term "jkbpC"} canonically represents @{term "jkbp"}.
\end{theorem}
This is a specialisation of \cite[Theorem~7.2.4]{FHMV:1995}.

*}
(*<*)

theorem jkbpC_represents: "represents jkbpC"
  using jkbpTn_jkbpCn_represents
  by (simp add: representsI jkbpC_def jkbpT_def)

theorem jkbpC_represents_uniquely:
  assumes repT: "represents T"
  shows "T = jkbpC"
proof -
  { fix n
    have "{ t \<in> T . tLength t = n } = { t \<in> jkbpC . tLength t = n }"
    proof(induct n)
      case 0
      from repT have F: "{t \<in> T. tLength t = 0} = jkbpTn 0 T"
        by - (subst jkbpT_traces_of_length[symmetric], simp add: representsD)
      thus ?case by (auto iff: jkbpC_traces_of_length)
    next
      case (Suc n)
      hence indhyp: "{t \<in> T. tLength t = n} = jkbpCn n"
        by (simp add: jkbpC_traces_of_length)

      from repT have F: "\<And>n. jkbpTn n T = {t \<in> T. tLength t = n}"
        by - (subst jkbpT_traces_of_length[symmetric], simp add: representsD)
      from indhyp F have G: "jkbpTn n T = jkbpCn n"
        by simp
      from repT have H: "\<And>n. {t \<in> T. tLength t = n} = {t \<in> jkbpTn n T. tLength t = n}"
        by (subst representsD[OF repT, symmetric], auto iff: jkbpT_traces_of_length)
      from F indhyp have ACTS:
        "\<And>t. t \<in> jkbpTn n T
          \<Longrightarrow> jAction (mkM T) t = jAction (mkMCn n) t"
        by - (rule sync_jview_jAction_eq[where n="n"], auto)
      show ?case
        apply (auto iff: Let_def ACTS G H jkbpC_traces_of_length)
        apply blast+
        done
    qed }
  thus ?thesis by auto
qed

end (* context *)

end
(*>*)
