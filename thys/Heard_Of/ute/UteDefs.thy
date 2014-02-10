theory UteDefs
imports "../HOModel"
begin

section {* Verification of the \ute{} Consensus Algorithm *}

text {*
  Algorithm \ute{} is presented in~\cite{biely:tolerating}. It is an
  uncoordinated algorithm that tolerates value (a.k.a.\ Byzantine) faults,
  and can be understood as a variant of \emph{UniformVoting}. The parameters
  $T$, $E$, and $\alpha$ appear as thresholds of the algorithm and in the
  communication predicates. Their values can be chosen within certain bounds
  in order to adapt the algorithm to the characteristics of different systems.

  We formalize in Isabelle the correctness proof of the algorithm that
  appears in~\cite{biely:tolerating}, using the framework of theory
  @{text HOModel}.
*}


subsection {* Model of the Algorithm *}

text {*
  We begin by introducing an anonymous type of processes of finite
  cardinality that will instantiate the type variable @{text "'proc"}
  of the generic HO model.
*}

typedecl Proc -- {* the set of processes *}
axiomatization where Proc_finite: "OFCLASS(Proc, finite_class)"
instance Proc :: finite by (rule Proc_finite)

abbreviation
  "N \<equiv> card (UNIV::Proc set)"   -- {* number of processes *}

text {*
  The algorithm proceeds in \emph{phases} of $2$ rounds each (we call
  \emph{steps} the individual rounds that constitute a phase).
  The following utility functions compute the phase and step of a round,
  given the round number.
*}

abbreviation
 "nSteps \<equiv> 2"
definition phase where "phase (r::nat) \<equiv> r div nSteps"
definition step where "step (r::nat) \<equiv> r mod nSteps"

lemma phase_zero [simp]: "phase 0 = 0"
by (simp add: phase_def)

lemma step_zero [simp]: "step 0 = 0"
by (simp add: step_def)

lemma phase_step: "(phase r * nSteps) + step r = r"
  by (auto simp add: phase_def step_def)

text {* The following record models the local state of a process. *}

record 'val pstate =
  x :: 'val                -- {* current value held by process *}
  vote :: "'val option"    -- {* value the process voted for, if any *}
  decide :: "'val option"  -- {* value the process has decided on, if any *}

text {* Possible messages sent during the execution of the algorithm. *}

datatype 'val msg =
   Val "'val"
 | Vote "'val option"

text {*
  The @{text x} field of the initial state is unconstrained, all other
  fields are initialized appropriately.
*}

definition Ute_initState where
  "Ute_initState p st \<equiv>
   (vote st = None) \<and> (decide st = None)"

text {* 
  The following locale introduces the parameters used for the \ute{}
  algorithm and their constraints~\cite{biely:tolerating}.
*}

locale ute_parameters =
  fixes \<alpha>::nat and T::nat and E::nat
  assumes majE: "2*E \<ge> N + 2*\<alpha>"
      and majT: "2*T \<ge> N + 2*\<alpha>"
      and EltN: "E < N"
      and TltN: "T < N"
begin

text {* Simple consequences of the above parameter constraints. *}

lemma alpha_lt_N: "\<alpha> < N"
using EltN majE by auto

lemma alpha_lt_T: "\<alpha> < T"
using majT alpha_lt_N by auto

lemma alpha_lt_E: "\<alpha> < E"
using majE alpha_lt_N by auto

text {*
  We separately define the transition predicates and the send functions
  for each step and later combine them to define the overall next-state relation.
*}

text {*
  In step 0, each process sends its current @{text x}.
  If it receives the value $v$ more than $T$ times, it votes for $v$,
  otherwise it doesn't vote.
*}

definition
  send0 :: "nat \<Rightarrow> Proc \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> 'val msg"
where
  "send0 r p q st \<equiv> Val (x st)"

definition
  next0 :: "nat \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> (Proc \<Rightarrow> 'val msg option) 
                \<Rightarrow> 'val pstate \<Rightarrow> bool" 
where
  "next0 r p st msgs st' \<equiv>
     (\<exists>v. card {q. msgs q = Some (Val v)} > T \<and> st' = st \<lparr> vote := Some v \<rparr>)
   \<or> \<not>(\<exists>v. card {q. msgs q = Some (Val v)} > T) \<and> st' = st \<lparr> vote := None \<rparr>"

text {*
  In step 1, each process sends its current @{text vote}.

  If it receives more than @{text "\<alpha>"} votes for a given value @{text v},
  it sets its @{text x} field to @{text v}, else it sets @{text x} to a
  default value.

  If the process receives more than @{text E} votes for @{text v}, it decides
  @{text v}, otherwise it leaves its decision unchanged.
*}

definition
  send1 :: "nat \<Rightarrow> Proc \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> 'val msg" 
where
  "send1 r p q st \<equiv> Vote (vote st)"

definition
  next1 :: "nat \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> (Proc \<Rightarrow> 'val msg option) 
                \<Rightarrow> 'val pstate \<Rightarrow> bool" 
where
  "next1 r p st msgs st' \<equiv>
    ( (\<exists>v. card {q. msgs q = Some (Vote (Some v))} > \<alpha> \<and> x st' = v)
     \<or> \<not>(\<exists>v. card {q. msgs q = Some (Vote (Some v))} > \<alpha>) 
         \<and> x st' = undefined  )
  \<and> ( (\<exists>v. card {q. msgs q = Some (Vote (Some v))} > E \<and> decide st' = Some v)
     \<or> \<not>(\<exists>v. card {q. msgs q = Some (Vote (Some v))} > E) 
         \<and> decide st' = decide st )
  \<and> vote st' = None"

text {*
  The overall send function and next-state relation are simply obtained as
  the composition of the individual relations defined above.
*}

definition 
  Ute_sendMsg :: "nat \<Rightarrow> Proc \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> 'val msg" 
where
  "Ute_sendMsg (r::nat) \<equiv> if step r = 0 then send0 r else send1 r"

definition 
  Ute_nextState :: "nat \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> (Proc \<Rightarrow> 'val msg option)
                        \<Rightarrow> 'val pstate \<Rightarrow> bool" 
where
  "Ute_nextState r \<equiv> if step r = 0 then next0 r else next1 r"


subsection {* Communication Predicate for \ute{} *}

text {*
  Following~\cite{biely:tolerating}, we now define the communication predicate
  for the \ute{} algorithm to be correct.

  The round-by-round predicate stipulates the following conditions:
  \begin{itemize}
  \item no process may receive more than @{text "\<alpha>"} corrupted messages, and
  \item every process should receive more than @{text "max(T, N + 2*\<alpha> - E - 1)"} 
    correct messages.
  \end{itemize}
  \cite{biely:tolerating} also requires that every process should receive more
  than @{text "\<alpha>"} correct messages, but this is implied, since @{text "T > \<alpha>"}
  (cf. lemma @{text alpha_lt_T}).
*}

definition Ute_commPerRd where
  "Ute_commPerRd HOrs SHOrs \<equiv>
   \<forall>p. card (HOrs p - SHOrs p) \<le> \<alpha>
     \<and> card (SHOrs p \<inter> HOrs p) > N + 2*\<alpha> - E - 1
     \<and> card (SHOrs p \<inter> HOrs p) > T"

text {*
  The global communication predicate requires there exists some phase
  @{text "\<Phi>"} such that:
  \begin{itemize}
  \item all HO and SHO sets of all processes are equal in the second step
    of phase @{text "\<Phi>"}, i.e.\ all processes receive messages from the 
    same set of processes, and none of these messages is corrupted,
  \item every process receives more than @{text T} correct messages in
    the first step of phase @{text "\<Phi>+1"}, and
  \item every process receives more than @{text E} correct messages in the
    second step of phase @{text "\<Phi>+1"}.
  \end{itemize}
  The predicate in the article~\cite{biely:tolerating} requires infinitely
  many such phases, but one is clearly enough.
*}

definition Ute_commGlobal where
  "Ute_commGlobal HOs SHOs \<equiv>
    \<exists>\<Phi>. (let r = Suc (nSteps*\<Phi>)
         in  (\<exists>\<pi>. \<forall>p. \<pi> = HOs r p \<and> \<pi> = SHOs r p)
           \<and> (\<forall>p. card (SHOs (Suc r) p \<inter> HOs (Suc r) p) > T)
           \<and> (\<forall>p. card (SHOs (Suc (Suc r)) p \<inter> HOs (Suc (Suc r)) p) > E))"


subsection {* The \ute{} Heard-Of Machine *}

text {* 
  We now define the coordinated HO machine for the \ute{} algorithm
  by assembling the algorithm definition and its communication-predicate.
*}

definition Ute_SHOMachine where
  "Ute_SHOMachine = \<lparr>
     CinitState =  (\<lambda> p st crd. Ute_initState p st),
     sendMsg =  Ute_sendMsg,
     CnextState = (\<lambda> r p st msgs crd st'. Ute_nextState r p st msgs st'),
     SHOcommPerRd = Ute_commPerRd,
     SHOcommGlobal = Ute_commGlobal 
   \<rparr>"

abbreviation
  "Ute_M \<equiv> (Ute_SHOMachine::(Proc, 'val pstate, 'val msg) SHOMachine)"

end   -- {* locale @{text "ute_parameters"} *}

end   (* theory UteDefs *)
