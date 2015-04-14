section {* The OneThirdRule Algorithm *}

theory OneThirdRule_Defs
imports "../../Heard_Of/HOModel" "../Consensus_Types"
begin

text {* The contents of this file have been taken almost verbatim from the
  Heard Of Model AFP entry. The only difference is that the types have been
  changed. *}


subsection {* Model of the algorithm *}

text {*
  The state of each process consists of two fields: @{text last_vote} holds
  the current value proposed by the process and @{text decision} the
  value (if any, hence the option type) it has decided.
*}

record 'val pstate =
  last_vote :: "'val"
  decision :: "'val option"

text {*
  The initial value of field @{text last_vote} is unconstrained, but no decision
  has been taken initially.
*}

definition OTR_initState where
  "OTR_initState p st \<equiv> decision st = None"

text {*
  Given a vector @{text msgs} of values (possibly null) received from 
  each process, @{term "HOV msgs v"} denotes the set of processes from
  which value @{text v} was received.
*}

definition HOV :: "(process \<Rightarrow> 'val option) \<Rightarrow> 'val \<Rightarrow> process set" where
  "HOV msgs v \<equiv> { q . msgs q = Some v }"

text {*
  @{term "MFR msgs v"} (``most frequently received'') holds for
  vector @{text msgs} if no value has been received more frequently
  than @{text v}.

  Some such value always exists, since there is only a finite set of
  processes and thus a finite set of possible cardinalities of the
  sets @{term "HOV msgs v"}.
*}

definition MFR :: "(process \<Rightarrow> 'val option) \<Rightarrow> 'val \<Rightarrow> bool" where
  "MFR msgs v \<equiv> \<forall>w. card (HOV msgs w) \<le> card (HOV msgs v)"

lemma MFR_exists: "\<exists>v. MFR msgs v"
proof -
  let ?cards = "{ card (HOV msgs v) | v . True }"
  let ?mfr = "Max ?cards"
  have "\<forall>v. card (HOV msgs v) \<le> N" by (auto intro: card_mono)
  hence "?cards \<subseteq> { 0 .. N }" by auto
  hence fin: "finite ?cards" by (metis atLeast0AtMost finite_atMost finite_subset)
  hence "?mfr \<in> ?cards" by (rule Max_in) auto
  then obtain v where v: "?mfr = card (HOV msgs v)" by auto
  have "MFR msgs v"
  proof (auto simp: MFR_def)
    fix w
    from fin have "card (HOV msgs w) \<le> ?mfr" by (rule Max_ge) auto
    thus "card (HOV msgs w) \<le> card (HOV msgs v)" by (unfold v)
  qed
  thus ?thesis ..
qed

text {*
  Also, if a process has heard from at least one other process,
  the most frequently received values are among the received messages.
*}

lemma MFR_in_msgs:
  assumes HO:"HOs m p \<noteq> {}"
      and v: "MFR (HOrcvdMsgs OTR_M m p (HOs m p) (rho m)) v"
             (is "MFR ?msgs v")
  shows "\<exists>q \<in> HOs m p. v = the (?msgs q)"
proof -
  from HO obtain q where q: "q \<in> HOs m p"
    by auto
  with v have "HOV ?msgs (the (?msgs q)) \<noteq> {}"
    by (auto simp: HOV_def HOrcvdMsgs_def)
  hence HOp: "0 < card (HOV ?msgs (the (?msgs q)))"
    by auto
  also from v have "\<dots> \<le> card (HOV ?msgs v)"
    by (simp add: MFR_def)
  finally have "HOV ?msgs v \<noteq> {}"
    by auto
  thus ?thesis
    by (auto simp: HOV_def HOrcvdMsgs_def)
qed

text {*
  @{term "TwoThirds msgs v"} holds if value @{text v} has been
  received from more than $2/3$ of all processes.
*}

definition TwoThirds where
  "TwoThirds msgs v \<equiv> (2*N) div 3 < card (HOV msgs v)"

text {*
  The next-state relation of algorithm \emph{One-Third Rule} for every process
  is defined as follows:
  if the process has received values from more than $2/3$ of all processes,
  the @{text last_vote} field is set to the smallest among the most frequently received
  values, and the process decides value $v$ if it received $v$ from more than
  $2/3$ of all processes. If @{text p} hasn't heard from more than $2/3$ of
  all processes, the state remains unchanged.
  (Note that @{text Some} is the constructor of the option datatype, whereas
  @{text "\<some>"} is Hilbert's choice operator.)
  We require the type of values to be linearly ordered so that the minimum
  is guaranteed to be well-defined.
*}

definition OTR_nextState where
  "OTR_nextState r p (st::('val::linorder) pstate) msgs st' \<equiv> 
   if (2*N) div 3 < card {q. msgs q \<noteq> None}
   then st' = \<lparr> last_vote = Min {v . MFR msgs v},
          decision = (if (\<exists>v. TwoThirds msgs v)
                    then Some (\<some>v. TwoThirds msgs v)
                    else decision st) \<rparr>
   else st' = st"

text {*
  The message sending function is very simple: at every round, every process
  sends its current proposal (field @{text last_vote} of its local state) to all 
  processes.
*}

definition OTR_sendMsg where
  "OTR_sendMsg r p q st \<equiv> last_vote st"

subsection {* Communication predicate for \emph{One-Third Rule} *}

text {*
  We now define the communication predicate for the \emph{One-Third Rule}
  algorithm to be correct.
  It requires that, infinitely often, there is a round where all processes
  receive messages from the same set @{text "\<Pi>"} of processes where @{text "\<Pi>"}
  contains more than two thirds of all processes.
  The ``per-round'' part of the communication predicate is trivial.
*}

definition OTR_commPerRd where
  "OTR_commPerRd HOrs \<equiv> True"

definition OTR_commGlobal where
  "OTR_commGlobal HOs \<equiv>
    \<forall>r. \<exists>r0 \<Pi>. r0 \<ge> r \<and> (\<forall>p. HOs r0 p = \<Pi>) \<and> card \<Pi> > (2*N) div 3"

subsection {* The \emph{One-Third Rule} Heard-Of machine *}

text {*
  We now define the HO machine for the \emph{One-Third Rule} algorithm
  by assembling the algorithm definition and its communication-predicate.
  Because this is an uncoordinated algorithm, the @{text crd} arguments
  of the initial- and next-state predicates are unused.
*}

definition OTR_HOMachine where
  "OTR_HOMachine =
    \<lparr> CinitState =  (\<lambda> p st crd. OTR_initState p st),
     sendMsg =  OTR_sendMsg,
     CnextState = (\<lambda> r p st msgs crd st'. OTR_nextState r p st msgs st'),
     HOcommPerRd = OTR_commPerRd,
     HOcommGlobal = OTR_commGlobal \<rparr>"

abbreviation "OTR_M \<equiv> OTR_HOMachine::(process, 'val::linorder pstate, 'val) HOMachine"

end
