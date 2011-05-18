(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory MuddyChildren
imports SPRViewDet
begin
(*>*)

subsection{* The Muddy Children *}

text{*

\label{sec:mc}

The classic muddy children puzzle \cite[\S1.1,
Example~7.2.5]{FHMV:1995} is an example of a multi-agent broadcast
scenario that exemplifies non-obvious reasoning about mutual states of
knowledge. Briefly, there are $N > 2$ children playing together, some
of whom get mud on their foreheads. Each can see the others' foreheads
but not their own. A mother observes the situation and either says
that everyone is clean, or says that someone is dirty. She then asks
``Do any of you know whether you have mud on your own forehead?''
over and over. Assuming the children are perceptive, intelligent,
truthful and they answer simultaneously, what will happen?

Each agent $\mbox{child}_i$ reasons with the following KBP:
\begin{center}
  \begin{tabular}{lll}
    $\mathbf{do}$\\
     & $\gcalt\ \hat{\mathbf{K}}_{\mbox{child}_i} \mbox{muddy}_i$ & $@{text "\<rightarrow>"}$ Say ``I know if my forehead is muddy''\\
     & $\gcalt\ @{text "\<not>"}\hat{\mathbf{K}}_{\mbox{child}_i} \mbox{muddy}_i$ & $@{text "\<rightarrow>"}$ Say nothing\\
    $\mathbf{od}$\\
  \end{tabular}
\end{center}
where $\hat{\mathbf{K}}_a @{text "\<phi>"}$ abbreviates $\mathbf{K}_a
@{text "\<phi>"}\ @{text "\<or>"}\ \mathbf{K}_a @{text "\<not>\<phi>"}$.  As the mother
has complete knowledge of the situation, we integrate her behaviour
into the environment.

In general the determinism of a KBP is a function of the environment,
and may be difficult to establish. In this case and many others,
however, determinism is syntactically manifest as the guards are
logically disjoint, independently of the knowledge subformulas.

The model records a child's initial observation of the mother's
pronouncement and the muddiness of the other children in her initial
private state, and these states are preserved by @{term "envTrans"}.
The recurring common observation is all of the children's public
responses to the mother's questions. Being able to distinguish these
types of observations is crucial to making this a broadcast scenario.

\begin{wrapfigure}{r}{0.5\textwidth}
  \vspace{-20pt}
  \includegraphics[width=0.48\textwidth]{MC}
  \vspace{-10pt}
  \caption{The protocol of $\mbox{child}_0$.}
  \label{fig:mc}
\end{wrapfigure}

Running the algorithm for three children and minimising yields the
automaton in Figure~\ref{fig:mc} for $\mbox{child}_0$. The initial
transitions are labelled with the initial observation, i.e., the
cleanliness ``C'' or muddiness ``M'' of the other two children. The
dashed initial transition covers the case where everyone is clean; in
the others the mother has announced that someone is dirty. Later
transitions simply record the actions performed by each of the agents,
where ``K'' is the first action in the above KBP, and ``N'' the
second. Double-circled states are those in which $\mbox{child}_0$
knows whether she is muddy, and single-circled where she does not.

To the best of our knowledge this is the first time that an
implementation of the muddy children has been automatically
synthesised.

*}
(*<*)

datatype Agent = Child0 | Child1 | Child2
datatype Proposition = Dirty Agent

datatype ChildAct = SayIKnow | SayNothing

lemma Agent_univ: "(UNIV :: Agent set) = {Child0, Child1, Child2}"
  unfolding UNIV_def
  apply auto
  apply (case_tac x)
  apply auto
  done

instance Agent :: finite
  apply intro_classes
  apply (auto iff: Agent_univ)
  done

instantiation Agent :: linorder
begin

fun
  less_Agent
where
  "less_Agent Child0 Child0 = False"
| "less_Agent Child0 _      = True"
| "less_Agent Child1 Child2 = True"
| "less_Agent Child1 _      = False"
| "less_Agent Child2 _      = False"

definition
  less_eq_Agent :: "Agent \<Rightarrow> Agent \<Rightarrow> bool"
where
  "less_eq_Agent x y \<equiv> x = y \<or> x < y"

instance
  apply intro_classes
  unfolding less_eq_Agent_def
  apply (case_tac x, case_tac y, simp_all)
  apply (case_tac y, simp_all)
  apply (case_tac y, simp_all)
  apply (case_tac x, case_tac y, case_tac z, simp_all)
  apply (case_tac x, case_tac z, simp_all)
  apply (case_tac x, case_tac y, simp_all)
  apply (case_tac y, simp_all)
  apply (case_tac x, case_tac y, simp_all)
  apply (case_tac y, simp_all)
  apply (case_tac y, simp_all)
  done
end

lemma Act_univ: "(UNIV :: ChildAct set) = {SayIKnow, SayNothing}"
  unfolding UNIV_def
  apply auto
  apply (case_tac x)
  apply auto
  done

instance ChildAct :: finite
  apply intro_classes
  apply (auto iff: Act_univ)
  done

instantiation ChildAct :: linorder
begin

fun
  less_ChildAct
where
  "less_ChildAct SayIKnow SayNothing = True"
| "less_ChildAct _ _ = False"

definition
  less_eq_ChildAct :: "ChildAct \<Rightarrow> ChildAct \<Rightarrow> bool"
where
  "less_eq_ChildAct x y \<equiv> x = y \<or> x < y"

instance
  apply intro_classes
  unfolding less_eq_ChildAct_def
  apply (case_tac x, case_tac y, simp_all)
  apply (case_tac y, simp_all)
  apply (case_tac y, simp_all)
  apply (case_tac x, case_tac y, simp_all)
  apply (case_tac y, simp_all)
  done
end

type_synonym EnvAct = "unit"
type_synonym EnvState = "(bool \<times> bool \<times> bool) \<times> (ChildAct \<times> ChildAct \<times> ChildAct)"
type_synonym AgentState = "bool \<times> bool \<times> bool"
type_synonym GlobalState = "(Agent, EnvState, AgentState) BEState"

definition "agents \<equiv> fromList [Child0, Child1, Child2]"

fun
  aChildIsDirty :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"
where
  "aChildIsDirty False False False = False"
| "aChildIsDirty _ _ _ = True"

definition
  initPS :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> (Agent \<times> (bool \<times> bool \<times> bool)) odlist"
where
  "initPS c0 c1 c2 \<equiv>
     let acid = aChildIsDirty c0 c1 c2
      in fromList [ (Child0, (acid, c1, c2)), (Child1, (acid, c0, c2)), (Child2, (acid, c0, c1))]"

definition
  envInit :: "GlobalState list"
where
  "envInit \<equiv>
    let bu = [False, True]
     in [ \<lparr> es = ((c0, c1, c2), (SayNothing, SayNothing, SayNothing)), ps = initPS c0 c1 c2 \<rparr> .
             c0 \<leftarrow> bu, c1 \<leftarrow> bu, c2 \<leftarrow> bu ]"

(* The environment is passive, but it still needs to do something in
   each round for the system as a whole to evolve. *)

definition
  envAction :: "GlobalState \<Rightarrow> EnvAct list"
where
  "envAction \<equiv> \<lambda>_. [()]"

(* Transitions involve broadcasting the children's private actions,
leaving their private states unchanged. *)

definition
  envTransES :: "EnvAct \<Rightarrow> (Agent \<Rightarrow> ChildAct) \<Rightarrow> EnvState \<Rightarrow> EnvState"
where
  "envTransES \<equiv> \<lambda>eAct aAct s. (fst s, aAct Child0, aAct Child1, aAct Child2)"

definition
  envTrans :: "EnvAct \<Rightarrow> (Agent \<Rightarrow> ChildAct) \<Rightarrow> GlobalState \<Rightarrow> GlobalState"
where
  "envTrans eact aact s \<equiv> s \<lparr> es := envTransES eact aact (es s) \<rparr>"

(* Common observation: the actions of the agents. *)

definition "envObsC \<equiv> snd"

definition
  envVal :: "GlobalState \<Rightarrow> Proposition \<Rightarrow> bool"
where
  "envVal \<equiv> \<lambda>s p.
     case p of Dirty a \<Rightarrow>
       (case es s of ((c0, c1, c2), _) \<Rightarrow>
         (case a of
            Child0 \<Rightarrow> c0
          | Child1 \<Rightarrow> c1
          | Child2 \<Rightarrow> c2))"

(* FIXME This is a bit grot, this definition is already made for us in the locale. *)

definition "envObs \<equiv> \<lambda>a s. (envObsC (es s), ODList.lookup (ps s) a)"

(* The KBP. Clearly subjective and deterministic. *)

abbreviation
  "Kor \<phi> \<psi> \<equiv> Knot (Kand (Knot \<phi>) (Knot \<psi>))"

definition
  jkbp :: "Agent \<Rightarrow> (Agent, Proposition, ChildAct) KBP"
where
  "jkbp a = [ \<lparr> guard = Kor (\<^bold>K\<^sub>a (Kprop (Dirty a)))
                            (\<^bold>K\<^sub>a (Knot (Kprop (Dirty a)))), action = SayIKnow \<rparr>,
              \<lparr> guard = Kand (Knot (\<^bold>K\<^sub>a (Kprop (Dirty a))))
                             (Knot (\<^bold>K\<^sub>a (Knot (Kprop (Dirty a))))), action = SayNothing \<rparr> ]"

interpretation MC!: Environment jkbp envInit envAction envTrans envVal envObs
  apply unfold_locales
  unfolding jkbp_def
  apply auto
  done

interpretation MC!:
  DetBroadcastEnvironment jkbp envInit envAction envTrans envVal envObs agents envObsC
  apply unfold_locales
  prefer 3
  apply (fold envObs_def envAction_def envTrans_def)
  apply clarify
  apply (erule MC.jkbpDetI)
   apply (simp add: jkbp_def)
   apply (auto simp: jkbp_def)[1]

  unfolding envAction_def envTrans_def envObs_def agents_def
  apply (simp_all add: Agent_univ jkbp_def)

  done

definition
  mcDFS
where
  [code]: "mcDFS \<equiv> SPRDetAutoDFS agents jkbp envInit envAction envTrans envVal envObsC envObs"

definition
  mcAlg
where
  [code]: "mcAlg \<equiv> mkSPRDetAuto agents jkbp envInit envAction envTrans envVal envObsC envObs"

lemma (in DetBroadcastEnvironment)
  "MC.implements mcAlg"
  unfolding mcAlg_def by (rule MC.mkSPRDetAuto_implements)

(*
export_code "mcDFS" "mcAlg" in Haskell file "/tmp/" (string_classes)
*)

end
(*>*)
