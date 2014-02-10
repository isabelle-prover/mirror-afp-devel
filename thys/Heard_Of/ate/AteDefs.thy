theory AteDefs
imports "../HOModel"
begin

section {* Verification of the \ate{} Consensus algorithm *}

text {* 
  Algorithm \ate{} is presented in~\cite{biely:tolerating}. Like \ute{},
  it is an uncoordinated algorithm that tolerates value faults, and it
  is parameterized by values $T$, $E$, and $\alpha$ that serve a similar
  function as in \ute{}, allowing the algorithm to be adapted to the
  characteristics of different systems. \ate{} can be understood as a
  variant of \emph{OneThirdRule} tolerating Byzantine faults.

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

text {* The following record models the local state of a process. *}

record 'val pstate =
  x :: "'val"              -- {* current value held by process *}
  decide :: "'val option"  -- {* value the process has decided on, if any *}

text {*
  The @{text x} field of the initial state is unconstrained, but no
  decision has yet been taken.
*}

definition Ate_initState where
  "Ate_initState p st \<equiv> (decide st = None)"

text {* 
  The following locale introduces the parameters used for the \ate{}
  algorithm and their constraints~\cite{biely:tolerating}.
*}

locale ate_parameters =
  fixes \<alpha>::nat and T::nat and E::nat
  assumes TNaE:"T \<ge> 2*(N + 2*\<alpha> - E)"
      and TltN:"T < N"
      and EltN:"E < N"

begin

text {* The following are consequences of the assumptions on the parameters. *}

lemma majE: "2 * (E - \<alpha>) \<ge> N"
using TNaE TltN by auto

lemma Egta: "E > \<alpha>"
using majE EltN by auto

lemma Tge2a: "T \<ge> 2 * \<alpha>"
using TNaE EltN by auto

text {*
  At every round, each process sends its current @{text x}.
  If it received more than @{text T} messages, it selects the smallest value
  and store it in @{text x}. As in algorithm \emph{OneThirdRule}, we
  therefore require values to be linearly ordered.

  If more than @{text E} messages holding the same value are received,
  the process decides that value.
*}

definition mostOftenRcvd where
  "mostOftenRcvd (msgs::Proc \<Rightarrow> 'val option) \<equiv>
   {v. \<forall>w. card {qq. msgs qq = Some w} \<le> card {qq. msgs qq = Some v}}"

definition 
  Ate_sendMsg :: "nat \<Rightarrow> Proc \<Rightarrow> Proc \<Rightarrow> 'val pstate \<Rightarrow> 'val"
where
  "Ate_sendMsg r p q st \<equiv> x st"

definition
  Ate_nextState :: "nat \<Rightarrow> Proc \<Rightarrow> ('val::linorder) pstate \<Rightarrow> (Proc \<Rightarrow> 'val option)
                        \<Rightarrow> 'val pstate \<Rightarrow> bool"
where
  "Ate_nextState r p st msgs st' \<equiv>
     (if card {q. msgs q \<noteq> None} > T
      then x st' = Min (mostOftenRcvd msgs)
      else x st' = x st)
   \<and> (   (\<exists>v. card {q. msgs q = Some v} > E  \<and> decide st' = Some v)
       \<or> \<not> (\<exists>v. card {q. msgs q = Some v} > E) 
         \<and> decide st' = decide st)"


subsection {* Communication Predicate for \ate{} *}

text {*
  Following~\cite{biely:tolerating}, we now define the communication
  predicate for the \ate{} algorithm. The round-by-round predicate
  requires that no process may receive more than @{text "\<alpha>"} corrupted
  messages at any round.
*}
definition Ate_commPerRd where
  "Ate_commPerRd HOrs SHOrs \<equiv>
   \<forall>p. card (HOrs p - SHOrs p) \<le> \<alpha>"

text {*
  The global communication predicate stipulates the three following
  conditions:
  \begin{itemize}
  \item for every process @{text p} there are infinitely many rounds 
    where @{text p} receives more than @{text T} messages,
  \item for every process @{text p} there are infinitely many rounds 
    where @{text p} receives more than @{text E} uncorrupted messages,
  \item and there are infinitely many rounds in which more than
    @{text "E - \<alpha>"} processes receive uncorrupted messages from the
    same set of processes, which contains more than @{text T} processes.
  \end{itemize}
*}
definition
  Ate_commGlobal where
  "Ate_commGlobal HOs SHOs \<equiv>
     (\<forall>r p. \<exists>r' > r. card (HOs r' p) > T)
   \<and> (\<forall>r p.  \<exists>r' > r. card (SHOs r' p \<inter> HOs r' p) > E)
   \<and> (\<forall>r. \<exists>r' > r. \<exists>\<pi>1 \<pi>2.
        card \<pi>1 > E - \<alpha>
      \<and> card \<pi>2 > T
      \<and> (\<forall>p \<in> \<pi>1. HOs r' p = \<pi>2 \<and> SHOs r' p \<inter> HOs r' p = \<pi>2))"

subsection {* The \ate{} Heard-Of Machine *}

text {* 
  We now define the non-coordinated SHO machine for the \ate{} algorithm
  by assembling the algorithm definition and its communication-predicate.
*}

definition Ate_SHOMachine where
  "Ate_SHOMachine = \<lparr> 
    CinitState =  (\<lambda> p st crd. Ate_initState p (st::('val::linorder) pstate)),
    sendMsg =  Ate_sendMsg,
    CnextState = (\<lambda> r p st msgs crd st'. Ate_nextState r p st msgs st'),
    SHOcommPerRd = (Ate_commPerRd:: Proc HO \<Rightarrow> Proc HO \<Rightarrow> bool),
    SHOcommGlobal = Ate_commGlobal
   \<rparr>"

abbreviation
  "Ate_M \<equiv> (Ate_SHOMachine::(Proc, 'val::linorder pstate, 'val) SHOMachine)"

end   -- {* locale @{text "ate_parameters"} *}

end   (* theory AteDefs *)
