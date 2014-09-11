theory UvDefs
imports "../HOModel"
begin

section {* Verification of the \emph{UniformVoting} Consensus Algorithm *}

text {*
  Algorithm \emph{UniformVoting} is presented in~\cite{charron:heardof}.
  It can be considered as a deterministic version of Ben-Or's well-known 
  probabilistic Consensus algorithm~\cite{ben-or:advantage}. We formalize
  in Isabelle the correctness proof given in~\cite{charron:heardof},
  using the framework of theory @{text HOModel}.
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

abbreviation "nSteps \<equiv> 2"

definition phase where "phase (r::nat) \<equiv> r div nSteps"

definition step where "step (r::nat) \<equiv> r mod nSteps"

text {*
  The following record models the local state of a process.
*}

record 'val pstate =
  x :: 'val                -- {* current value held by process *}
  vote :: "'val option"    -- {* value the process voted for, if any *}
  decide :: "'val option"  -- {* value the process has decided on, if any *}

text {*
  Possible messages sent during the execution of the algorithm, and characteristic
  predicates to distinguish types of messages.
*}

datatype 'val msg =
  Val 'val
| ValVote 'val "'val option"
| Null  -- {* dummy message in case nothing needs to be sent *}

definition isValVote where "isValVote m \<equiv> \<exists>z v. m = ValVote z v"

definition isVal where "isVal m \<equiv> \<exists>v. m = Val v"

text {*
  Selector functions to retrieve components of messages. These functions
  have a meaningful result only when the message is of appropriate kind.
*}

fun getvote where
  "getvote (ValVote z v) = v"

fun getval where
  "getval (ValVote z v) = z"
| "getval (Val z) = z"


text {*
  The @{text x} field of the initial state is unconstrained, all other
  fields are initialized appropriately.
*}

definition UV_initState where
  "UV_initState p st \<equiv> (vote st = None) \<and> (decide st = None)"

text {*
  We separately define the transition predicates and the send functions
  for each step and later combine them to define the overall next-state relation.
*}

definition msgRcvd where  -- {* processes from which some message was received *}
  "msgRcvd (msgs:: Proc \<rightharpoonup> 'val msg) = {q . msgs q \<noteq> None}"

definition smallestValRcvd where
  "smallestValRcvd (msgs::Proc \<rightharpoonup> ('val::linorder) msg) \<equiv>
   Min {v. \<exists>q. msgs q = Some (Val v)}"

text {*
  In step 0, each process sends its current @{text x} value.

  It updates its @{text x} field to the smallest value it has received.
  If the process has received the same value @{text v} from all processes
  from which it has heard, it updates its @{text vote} field to @{text v}.
*}

definition send0 where
  "send0 r p q st \<equiv> Val (x st)"

definition next0 where
  "next0 r p st (msgs::Proc \<rightharpoonup> ('val::linorder) msg) st' \<equiv>
       (\<exists>v. (\<forall>q \<in> msgRcvd msgs. msgs q = Some (Val v))
           \<and> st' = st \<lparr> vote := Some v, x := smallestValRcvd msgs \<rparr>)
    \<or> \<not>(\<exists>v. \<forall>q \<in> msgRcvd msgs. msgs q = Some (Val v))
       \<and> st' = st \<lparr> x := smallestValRcvd msgs \<rparr>"

text {*
  In step 1, each process sends its current @{text x} and @{text vote} values.
*}

definition send1 where
  "send1 r p q st \<equiv> ValVote (x st) (vote st)"

definition valVoteRcvd where
  -- {* processes from which values and votes were received *}
  "valVoteRcvd (msgs :: Proc \<rightharpoonup> 'val msg) \<equiv> 
   {q . \<exists>z v. msgs q = Some (ValVote z v)}"

definition smallestValNoVoteRcvd where
  "smallestValNoVoteRcvd (msgs::Proc \<rightharpoonup> ('val::linorder) msg) \<equiv>
   Min {v. \<exists>q. msgs q = Some (ValVote v None)}"

definition someVoteRcvd where
  -- {* set of processes from which some vote was received *}
  "someVoteRcvd (msgs :: Proc \<rightharpoonup> 'val msg) \<equiv>
   { q . q \<in> msgRcvd msgs \<and> isValVote (the (msgs q)) \<and> getvote (the (msgs q)) \<noteq> None }"

definition identicalVoteRcvd where
  "identicalVoteRcvd (msgs :: Proc \<rightharpoonup> 'val msg) v \<equiv>
   \<forall>q \<in> msgRcvd msgs. isValVote (the (msgs q)) \<and> getvote (the (msgs q)) = Some v"

definition x_update where
 "x_update st msgs st' \<equiv>
   (\<exists>q \<in> someVoteRcvd msgs . x st' = the (getvote (the (msgs q))))
 \<or> someVoteRcvd msgs = {} \<and> x st' = smallestValNoVoteRcvd msgs"

definition dec_update where
  "dec_update st msgs st' \<equiv>
    (\<exists>v. identicalVoteRcvd msgs v \<and> decide st' = Some v)
  \<or> \<not>(\<exists>v. identicalVoteRcvd msgs v) \<and> decide st' = decide st"

definition next1 where
  "next1 r p st msgs st' \<equiv>
     x_update st msgs st'
   \<and> dec_update st msgs st'
   \<and> vote st' = None"

text {*
  The overall send function and next-state relation are simply obtained as 
  the composition of the individual relations defined above.
*}

definition UV_sendMsg where
  "UV_sendMsg (r::nat) \<equiv> if step r = 0 then send0 r else send1 r"

definition UV_nextState where
  "UV_nextState r \<equiv> if step r = 0 then next0 r else next1 r"


subsection {* Communication Predicate for \emph{UniformVoting} *}

text {*
  We now define the communication predicate for the \emph{UniformVoting}
  algorithm to be correct.

  The round-by-round predicate requires that for any two processes
  there is always one process heard by both of them. In other words,
  no ``split rounds'' occur during the execution of the algorithm~\cite{charron:heardof}.
  Note that in particular, heard-of sets are never empty.
*}

definition UV_commPerRd where
  "UV_commPerRd HOrs \<equiv> \<forall>p q. \<exists>pq. pq \<in> HOrs p \<inter> HOrs q"

text {*
  The global predicate requires the existence of a (space-)uniform round
  during which the heard-of sets of all processes are equal.
  (Observe that \cite{charron:heardof} requires infinitely many uniform
  rounds, but the correctness proof uses just one such round.)
*}

definition UV_commGlobal where
  "UV_commGlobal HOs \<equiv> \<exists>r. \<forall>p q. HOs r p = HOs r q"


subsection {* The \emph{UniformVoting} Heard-Of Machine *}

text {*
  We now define the HO machine for \emph{Uniform Voting} by assembling the
  algorithm definition and its communication predicate. Notice that the
  coordinator arguments for the initialization and transition functions are
  unused since \emph{UniformVoting} is not a coordinated algorithm.
*}

definition UV_HOMachine where
  "UV_HOMachine = \<lparr> 
    CinitState =  (\<lambda>p st crd. UV_initState p st),
    sendMsg =  UV_sendMsg,
    CnextState = (\<lambda>r p st msgs crd st'. UV_nextState r p st msgs st'),
    HOcommPerRd = UV_commPerRd,
    HOcommGlobal = UV_commGlobal
  \<rparr>"

abbreviation
  "UV_M \<equiv> (UV_HOMachine::(Proc, 'val::linorder pstate, 'val msg) HOMachine)"

end
