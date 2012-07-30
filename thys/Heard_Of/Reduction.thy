theory Reduction
imports HOModel "../Stuttering_Equivalence/StutterEquivalence"
begin

section {* Reduction Theorem *}

text {*
  We have defined the semantics of HO algorithms such that rounds are executed
  atomically, by all processes. This definition is surprising for a model of
  asynchronous distributed algorithms since it models a synchronous execution
  of rounds. However, it simplifies representing and reasoning about the algorithms. 
  For example, the communication network does not have to be modeled explicitly,
  since the possible sets of messages received by processes can be computed
  from the global configuration and the collections of HO and SHO sets.

  We will now define a more conventional ``fine-grained'' semantics where
  communication is modeled explicitly and rounds of processes can be arbitrarily
  interleaved (subject to the constraints of the communication predicates).
  We will then establish a \emph{reduction theorem} that shows that for every
  fine-grained run there exists an equivalent round-based (``coarse-grained'')
  run in the sense that the two runs exhibit the same sequences of local states
  of all processes, modulo stuttering. We prove the reduction theorem for the
  most general class of coordinated SHO algorithms. It is easy to see that the
  theorem equally holds for the special cases of uncoordinated or HO algorithms,
  and since we have in fact defined these classes of algorithms from the more
  general ones, we can directly apply the general theorem.

  As a corollary, interesting properties remain valid in the fine-grained semantics
  if they hold in the coarse-grained semantics. It is therefore enough to
  verify such properties in the coarse-grained semantics, which is much easier
  to reason about. The essential restriction is that properties may not depend
  on states of different processes occurring simultaneously. (For example, the
  coarse-grained semantics ensures by definition that all processes execute the
  same round at any instant, which is obviously not true of the fine-grained
  semantics.) We claim that all ``reasonable'' properties of fault-tolerant
  distributed algorithms are preserved by our reduction. For example, the
  Consensus (and Weak Consensus) problems fall into this class.

  The proofs follow Chaouch-Saad et al.~\cite{saad:reduction}, where the
  reduction theorem was proved for uncoordinated HO algorithms.
*}

subsection {* Fine-Grained Semantics *}

text {*
  In the fine-grained semantics, a run of an HO algorithm is represented
  as an $\omega$-sequence of system configurations. Each configuration 
  is represented as a record carrying the following information:
  \begin{itemize}
  \item for every process $p$, the current round that process $p$ is executing,
  \item the local state of every process,
  \item for every process $p$, the set of processes to which $p$ has already
    sent a message for the current round,
  \item for all processes $p$ and $q$, the message (if any) that $p$ has
    received from $q$ for the round that $p$ is currently executing, and
  \item the set of messages in transit, represented as triples of the form
    $(p,r,q,m)$ meaning that process $p$ sent message $m$ to process $q$
    for round $r$, but $q$ has not yet received that message.
  \end{itemize}

  As explained earlier, the coordinators of processes are not recorded in
  the configuration, but algorithms may record them as part of the process states.
*}

record ('pst, 'proc, 'msg) config =
  round :: "'proc \<Rightarrow> nat"
  state :: "'proc \<Rightarrow> 'pst"
  sent  :: "'proc \<Rightarrow> 'proc set"
  rcvd  :: "'proc \<Rightarrow> 'proc \<Rightarrow> 'msg option"
  network :: " ('proc * nat * 'proc * 'msg) set"

type_synonym ('pst ,'proc , 'msg) fgrun = "nat \<Rightarrow> ('pst, 'proc, 'msg) config"

text {*
  In an initial configuration for an algorithm, the local state of every process
  satisfies the algorithm's initial-state predicate, and all other components
  have obvious default values.
*}

definition fg_init_config where
  "fg_init_config A (config::('pst,'proc, 'msg) config) (coord::'proc coord) \<equiv>
     round config = (\<lambda>p. 0)
   \<and> (\<forall>p. CinitState A p (state config p) (coord p))
   \<and> sent config = (\<lambda>p. {})
   \<and> rcvd config = (\<lambda>p q. None)
   \<and> network config = {}"

text {*
  In the fine-grained semantics, we have three types of transitions due to
  \begin{itemize}
  \item some process sending a message,
  \item some process receiving a message, and
  \item some process executing a local transition.
  \end{itemize}

  The following definition models process @{text p} sending a message to
  process @{text q}. The transition is enabled if @{text p} has not yet
  sent any message to @{text q} for the current round. The message to be
  sent is computed according to the algorithm's @{text sendMsg} function. 
  The effect of the transition is to add @{text q} to the @{text sent}
  component of the configuration and the message quadruple to the
  @{text network} component.
*}

definition fg_send_msg where
  "fg_send_msg A p q config config' \<equiv>
     q \<notin> (sent config p)
   \<and> config' = config \<lparr> 
        sent := (sent config)(p := (sent config p) \<union> {q}),
        network := network config \<union>
                   {(p, round config p, q,
                     sendMsg A (round config p) p q (state config p))} \<rparr>"

text {*
  The following definition models the reception of a message by process
  @{text p} from process @{text q}. The action is enabled if @{text q}
  is in the heard-of set @{text HO} of process @{text p} for the current
  round, and if the network contains some message from @{text q} to
  @{text p} for the round that @{text p} is currently executing.
  W.l.o.g., we model message corruption at reception: if @{text q} is not
  in @{text p}'s SHO set (parameter @{text SHO}), then an arbitrary value
  @{text m'} is received instead of @{text m}.
*}

definition fg_rcv_msg where
  "fg_rcv_msg p q HO SHO config config' \<equiv> 
   \<exists>m m'. (q, (round config p), p, m) \<in> network config
     \<and> q \<in> HO
     \<and> config' = config \<lparr>
          rcvd := (rcvd config)(p := (rcvd config p)(q := 
                    if q \<in> SHO then Some m else Some m')),
          network := network config - {(q, (round config p), p, m)} \<rparr>"

text {*
  Finally, we consider local state transition of process @{text p}. 
  A local transition is enabled only after @{text p} has sent all messages
  for its current round and has received all messages that it is supposed
  to receive according to its current HO set (parameter @{text HO}). The
  local state is updated according to the algorithm's @{text CnextState} 
  relation, which may depend on the coordinator @{text crd} of the following
  round. The round of process @{text p} is incremented, and the
  @{text sent} and @{text rcvd} components for process @{text p} are
  reset to initial values for the new round.
*}

definition fg_local where
  "fg_local A p HO crd config config' \<equiv>
     sent config p = UNIV
   \<and> dom (rcvd config p) = HO
   \<and> (\<exists>s. CnextState A (round config p) p (state config p) (rcvd config p) crd s
        \<and> config' = config \<lparr>
             round := (round config)(p := Suc (round config p)),
             state := (state config)(p := s),
             sent := (sent config)(p := {}),
             rcvd := (rcvd config)(p := \<lambda>q. None) \<rparr>)"

text {*
  The next-state relation for process @{text p} is just the disjunction of
  the above three types of transitions.
*}

definition fg_next_config where
  "fg_next_config A p HO SHO crd config config' \<equiv>
     (\<exists>q. fg_send_msg A p q config config')
   \<or> (\<exists>q. fg_rcv_msg p q HO SHO config config')
   \<or> fg_local A p HO crd config config'"

text {*
  Fine-grained runs are infinite sequences of configurations that start
  in an initial configuration and where each step corresponds to some process
  sending a message, receiving a message or performing a local step. We also
  require that every process eventually executes every round -- note that
  this condition is implicit in the definition of coarse-grained runs.
*}

definition fg_run where
  "fg_run A rho HOs SHOs coords \<equiv>
      fg_init_config A (rho 0) (coords 0)
    \<and> (\<forall>i. \<exists>p. fg_next_config A p 
                                    (HOs (round (rho i) p) p)
                                    (SHOs (round (rho i) p) p)
                                    (coords (round (rho (Suc i)) p) p)
                                    (rho i) (rho (Suc i)))
    \<and> (\<forall>p r. \<exists>n. round (rho n) p = r)"

text {*
  The following function computes at which ``time point'' (index in the
  fine-grained computation) process @{text p} starts executing round 
  @{text r}. This function plays an important role in the correspondence
  between the two semantics, and in the subsequent proofs.
*}

definition fg_start_round where
  "fg_start_round rho p r \<equiv> LEAST (n::nat). round (rho n) p = r"


subsection {* Properties of the Fine-Grained Semantics *}

text {*
  In preparation for the proof of the reduction theorem, we establish a
  number of consequences of the above definitions.
*}

text {*
  Process states change only when round numbers change during a
  fine-grained run.
*}
lemma fg_state_change:
  assumes rho: "fg_run A rho HOs SHOs coords"
      and rd: "round (rho (Suc n)) p = round (rho n) p"
  shows "state (rho (Suc n)) p = state (rho n) p"
proof -
  from rho have "\<exists>p'. fg_next_config A p' (HOs (round (rho n) p') p') 
                                          (SHOs (round (rho n) p') p')
                                          (coords (round (rho (Suc n)) p') p') 
                                          (rho n) (rho (Suc n))"
    by (auto simp: fg_run_def)
  with rd show ?thesis
    by (auto simp: fg_next_config_def fg_send_msg_def fg_rcv_msg_def fg_local_def)
qed

text {*
  Round numbers never decrease.
*}
lemma fg_round_numbers_increase:
  assumes rho: "fg_run A rho HOs SHOs coords" and n: "n \<le> m"
  shows "round (rho n) p \<le> round (rho m) p"
proof -
  from n obtain k where k: "m = n+k" by (auto simp: le_iff_add)
  {
    fix i
    have "round (rho n) p \<le> round (rho (n+i)) p" (is "?P i")
    proof (induct i)
      show "?P 0" by simp
    next
      fix j
      assume ih: "?P j"
      from rho have "\<exists>p'. fg_next_config A p' (HOs (round (rho (n+j)) p') p')
                                              (SHOs (round (rho (n+j)) p') p')
                                              (coords (round (rho (Suc (n+j))) p') p')
                                              (rho (n+j)) (rho (Suc (n+j)))"
        by (auto simp: fg_run_def)
      hence "round (rho (n+j)) p \<le> round (rho (n + Suc j)) p"
        by (auto simp: fg_next_config_def fg_send_msg_def fg_rcv_msg_def fg_local_def)
      with ih show "?P (Suc j)" by auto
    qed
  }
  with k show ?thesis by simp
qed

text {*
  Combining the two preceding lemmas, it follows that the local states
  of process @{text p} at two configurations are the same if these 
  configurations have the same round number.
*}
lemma fg_same_round_same_state:
  assumes rho: "fg_run A rho HOs SHOs coords"
      and rd: "round (rho m) p = round (rho n) p"
  shows "state (rho m) p = state (rho n) p"
proof -
  {
    fix k i
    have "round (rho (k+i)) p = round (rho k) p 
          \<Longrightarrow> state (rho (k+i)) p = state (rho k) p"
      (is "?R i \<Longrightarrow> ?S i")
    proof (induct i)
      show "?S 0" by simp
    next
      fix j
      assume ih: "?R j \<Longrightarrow> ?S j" 
         and r: "round (rho (k + Suc j)) p = round (rho k) p"
      from rho have 1: "round (rho k) p \<le> round (rho (k+j)) p"
        by (auto elim: fg_round_numbers_increase)
      from rho have 2: "round (rho (k+j)) p \<le> round (rho (k + Suc j)) p"
        by (auto elim: fg_round_numbers_increase)
      from 1 2 r have 3: "round (rho (k+j)) p = round (rho k) p" by auto
      with r have "round (rho (Suc (k+j))) p = round (rho (k+j)) p" by simp
      with rho have "state (rho (Suc (k+j))) p = state (rho (k+j)) p"
        by (auto elim: fg_state_change)
      with 3 ih show "?S (Suc j)" by simp
    qed
  }
  note aux = this
  show ?thesis
  proof (cases "n \<le> m")
    case True
    then obtain k where "m = n+k" by (auto simp: le_iff_add)
    with rd show ?thesis by (auto simp: aux)
  next
    case False
    hence "m \<le> n" by simp
    then obtain k where "n = m+k" by (auto simp: le_iff_add)
    with rd show ?thesis by (auto simp: aux)
  qed
qed

text {*
  Since every process executes every round, function @{text fg_startRound}
  is well-defined. We also list a few facts about @{text fg_startRound} that
  will be used to show that it is a ``stuttering sampling function'',
  a notion introduced in the theories about stuttering equivalence.
*}
lemma fg_start_round:
  assumes "fg_run A rho HOs SHOs coords"
  shows "round (rho (fg_start_round rho p r)) p = r"
using assms by (auto simp: fg_run_def fg_start_round_def intro: LeastI_ex)

lemma fg_start_round_smallest:
  assumes "round (rho k) p = r"
  shows "fg_start_round rho p r \<le> (k::nat)"
using assms unfolding fg_start_round_def by (rule Least_le)

lemma fg_start_round_later:
  assumes rho: "fg_run A rho HOs SHOs coords"
      and r: "round (rho n) p = r" and r': "r < r'"
  shows "n < fg_start_round rho p r'" (is "_ < ?start")
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence start: "?start \<le> n" by simp
  from rho this have "round (rho ?start) p \<le> round (rho n) p"
    by (rule fg_round_numbers_increase)
  with r have "r' \<le> r" by (simp add: fg_start_round[OF rho])
  with r' show "False" by simp
qed

lemma fg_start_round_0:
  assumes rho: "fg_run A rho HOs SHOs coords"
  shows "fg_start_round rho p 0 = 0"
proof -
  from rho have "round (rho 0) p = 0" by (auto simp: fg_run_def fg_init_config_def)
  hence "fg_start_round rho p 0 \<le> 0" by (rule fg_start_round_smallest)
  thus ?thesis by simp
qed

lemma fg_start_round_strict_mono:
  assumes rho: "fg_run A rho HOs SHOs coords"
  shows "strict_mono (fg_start_round rho p)"
proof
  fix r r'
  assume r: "(r::nat) < r'"
  from rho have "round (rho (fg_start_round rho p r)) p = r" by (rule fg_start_round)
  from rho this r show "fg_start_round rho p r < fg_start_round rho p r'"
    by (rule fg_start_round_later)
qed

text {*
  Process @{text p} is at round @{text r} at all configurations between 
  the start of round @{text r} and the start of round @{text "r+1"}.
  By lemma @{text fg_same_round_same_state}, this implies that the
  local state of process @{text p} is the same at all these configurations.
*}
lemma fg_round_between_start_rounds:
assumes rho: "fg_run A rho HOs SHOs coords"
    and 1: "fg_start_round rho p r \<le> n"
    and 2: "n < fg_start_round rho p (Suc r)"
shows "round (rho n) p = r" (is "?rd = r")
proof (rule antisym)
  from 1 have "round (rho (fg_start_round rho p r)) p \<le> ?rd"
    by (rule fg_round_numbers_increase[OF rho])
  thus "r \<le> ?rd" by (simp add: fg_start_round[OF rho])
next
  show "?rd \<le> r"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "Suc r \<le> ?rd" by simp
    hence "fg_start_round rho p (Suc r) \<le> fg_start_round rho p ?rd"
      by (rule rho[THEN fg_start_round_strict_mono, THEN strict_mono_mono, 
                   THEN monoD])
    also have "... \<le> n" by (auto intro: fg_start_round_smallest)
    also note 2
    finally show "False" by simp
  qed
qed

text {*
  For any process @{text p} and round @{text r} there is some instant @{text n}
  where @{text p} executes a local transition from round @{text r}. In fact,
  @{text "n+1"} marks the start of round @{text "r+1"}.
*}
lemma fg_local_transition_from_round:
assumes rho: "fg_run A rho HOs SHOs coords"
obtains n where "round (rho n) p = r"
            and "fg_start_round rho p (Suc r) = Suc n"
            and "fg_local A p (HOs r p) (coords (Suc r) p) (rho n) (rho (Suc n))"
proof -
  have "fg_start_round rho p (Suc r) \<noteq> 0" (is "?start \<noteq> 0")
  proof
    assume contr: "?start = 0"
    from rho have "round (rho ?start) p = Suc r" by (rule fg_start_round)
    with contr rho show "False" by (auto simp: fg_run_def fg_init_config_def)
  qed
  then obtain n where n: "?start = Suc n" by (auto simp: gr0_conv_Suc)
  with fg_start_round[OF rho, of p "Suc r"]
  have 0: "round (rho (Suc n)) p = Suc r" by simp
  have 1: "round (rho n) p = r"
  proof (rule fg_round_between_start_rounds[OF rho])
    have "fg_start_round rho p r < fg_start_round rho p (Suc r)"
      by (rule fg_start_round_strict_mono[OF rho, THEN strict_monoD]) simp
    with n show "fg_start_round rho p r \<le> n" by simp
  next
    from n show "n < ?start" by simp
  qed
  from rho obtain p' where
    "fg_next_config A p' (HOs (round (rho n) p') p')
                         (SHOs (round (rho n) p') p')
                         (coords (round (rho (Suc n)) p') p')
                         (rho n) (rho (Suc n))"
    (is "fg_next_config _ _ ?HO ?SHO ?crd ?cfg ?cfg'")
    by (force simp: fg_run_def)
  hence "fg_local A p (HOs r p) (coords (Suc r) p) (rho n) (rho (Suc n))"
  proof (auto simp: fg_next_config_def)
    fix q
    assume "fg_send_msg A p' q ?cfg ?cfg'"
      -- "impossible because round changes"
    with 0 1 show ?thesis by (auto simp: fg_send_msg_def)
  next
    fix q
    assume "fg_rcv_msg p' q ?HO ?SHO ?cfg ?cfg'"
      -- "impossible because round changes"
    with 0 1 show ?thesis by (auto simp: fg_rcv_msg_def)
  next
    assume "fg_local A p' ?HO ?crd ?cfg ?cfg'"
    with 0 1 show ?thesis by (cases "p' = p") (auto simp: fg_local_def)
  qed
  with 1 n that show ?thesis by auto
qed

text {*
  We now prove two invariants asserted in \cite{saad:reduction}. The first
  one states that any message @{text m} in transit from process @{text p}
  to process @{text q} for round @{text r} corresponds to the message
  computed by @{text p} for @{text q}, given @{text p}'s state at its
  @{text r}th local transition.
*}

lemma fg_invariant1:
  assumes rho: "fg_run A rho HOs SHOs coords"
      and m: "(p,r,q,m) \<in> network (rho n)" (is "?msg n")
  shows "m = sendMsg A r p q (state (rho (fg_start_round rho p r)) p)"
using m proof (induct n)
  -- {* the base case is trivial because the network is empty *}
  assume "?msg 0" with rho show "?thesis"
    by (auto simp: fg_run_def fg_init_config_def)
next
  fix n
  assume m': "?msg (Suc n)" and ih: "?msg n \<Longrightarrow> ?thesis"
  from rho obtain p' where
    "fg_next_config A p' (HOs (round (rho n) p') p') 
                         (SHOs (round (rho n) p') p')
                         (coords (round (rho (Suc n)) p') p')
                         (rho n) (rho (Suc n))"
    (is "fg_next_config _ _ ?HO ?SHO ?crd ?cfg ?cfg'")
    by (force simp: fg_run_def)
  thus "?thesis"
  proof (auto simp: fg_next_config_def)
    txt {*
      Only @{text fg_send_msg} transitions for process @{text p} are interesting,
      since all other transitions cannot add a message for @{text p}, hence we can
      apply the induction hypothesis.
    *}
    fix q'
    assume send: "fg_send_msg A p' q' ?cfg ?cfg'"
    show ?thesis
    proof (cases "?msg n")
      case True
      with ih show ?thesis .
    next
      case False
      with send m' have 1: "p' = p" "round ?cfg p = r"
                    and 2: "m = sendMsg A r p q (state ?cfg p)"
        by (auto simp: fg_send_msg_def)
      from rho 1 have "state ?cfg p = state (rho (fg_start_round rho p r)) p"
        by (auto simp: fg_start_round fg_same_round_same_state)
      with 1 2 show ?thesis by simp
    qed
  next
    fix q'
    assume "fg_rcv_msg p' q' ?HO ?SHO ?cfg ?cfg'"
    with m' have "?msg n" by (auto simp: fg_rcv_msg_def)
    with ih show ?thesis .
  next
    assume "fg_local A p' ?HO ?crd ?cfg ?cfg'"
    with m' have "?msg n" by (auto simp: fg_local_def)
    with ih show ?thesis .
  qed
qed

text {*
  The second invariant states that if process @{text q} received message
  @{text m} from process @{text p}, then (a) @{text p} is in @{text q}'s
  HO set for that round @{text m}, and (b) if @{text p} is moreover in
  @{text q}'s SHO set, then @{text m} is the message that @{text p} computed
  at the start of that round.
*}

lemma fg_invariant2a:
  assumes rho: "fg_run A rho HOs SHOs coords"
      and m: "rcvd (rho n) q p = Some m" (is "?rcvd n")
  shows "p \<in> HOs (round (rho n) q) q"
  (is "p \<in> HOs (?rd n) q" is "?P n")
using m proof (induct n)
  -- {* The base case is trivial because @{text q} has not received any message initially *}
  assume "?rcvd 0" with rho show "?P 0"
    by (auto simp: fg_run_def fg_init_config_def)
next
  fix n
  assume rcvd: "?rcvd (Suc n)" and ih: "?rcvd n \<Longrightarrow> ?P n"
  -- {* For the inductive step we distinguish the possible transitions *}
  from rho obtain p' where
    "fg_next_config A p' (HOs (round (rho n) p') p') 
                         (SHOs (round (rho n) p') p')
                         (coords (round (rho (Suc n)) p') p')
                         (rho n) (rho (Suc n))"
    (is "fg_next_config _ _ ?HO ?SHO ?crd ?cfg ?cfg'")
    by (force simp: fg_run_def)
  thus "?P (Suc n)"
  proof (auto simp: fg_next_config_def)
    txt {* 
      Except for @{text fg_rcv_msg} steps of process @{text q}, the proof
      is immediately reduced to the induction hypothesis.
    *}
    fix q'
    assume rcvmsg: "fg_rcv_msg p' q' ?HO ?SHO ?cfg ?cfg'"
    hence rd: "?rd (Suc n) = ?rd n" by (auto simp: fg_rcv_msg_def)
    show "?P (Suc n)"
    proof (cases "?rcvd n")
      case True
      with ih rd show ?thesis by simp
    next
      case False
      with rcvd rcvmsg rd show ?thesis by (auto simp: fg_rcv_msg_def)
    qed
  next
    fix q'
    assume "fg_send_msg A p' q' ?cfg ?cfg'"
    with rcvd have "?rcvd n" and "?rd (Suc n) = ?rd n"
      by (auto simp: fg_send_msg_def)
    with ih show "?P (Suc n)" by simp
  next
    assume "fg_local A p' ?HO ?crd ?cfg ?cfg'"
    with rcvd have "?rcvd n" and "?rd (Suc n) = ?rd n"
      -- {* in fact, @{text "p' = q"} is impossible because the @{text rcvd} field of @{text p'} is cleared *}
      by (auto simp: fg_local_def)
    with ih show "?P (Suc n)" by simp
  qed
qed

lemma fg_invariant2b:
  assumes rho: "fg_run A rho HOs SHOs coords"
      and m: "rcvd (rho n) q p = Some m" (is "?rcvd n")
      and sho: "p \<in> SHOs (round (rho n) q) q" (is "p \<in> SHOs (?rd n) q")
  shows "m = sendMsg A (?rd n) p q 
                     (state (rho (fg_start_round rho p (?rd n))) p)"
        (is "?P n")
using m sho proof (induct n)
  -- {* The base case is trivial because @{text q} has not received any message initially *}
  assume "?rcvd 0" with rho show "?P 0"
    by (auto simp: fg_run_def fg_init_config_def)
next
  fix n
  assume rcvd: "?rcvd (Suc n)" and p: "p \<in> SHOs (?rd (Suc n)) q"
     and ih: "?rcvd n \<Longrightarrow> p \<in> SHOs (?rd n) q \<Longrightarrow> ?P n"
  -- {* For the inductive step we again distinguish the possible transitions *}
  from rho obtain p' where
    "fg_next_config A p' (HOs (round (rho n) p') p')
                         (SHOs (round (rho n) p') p')
                         (coords (round (rho (Suc n)) p') p')
                         (rho n) (rho (Suc n))"
    (is "fg_next_config _ _ ?HO ?SHO ?crd ?cfg ?cfg'")
    by (force simp: fg_run_def)
  thus "?P (Suc n)"
  proof (auto simp: fg_next_config_def)
    txt {* 
      Except for @{text fg_rcv_msg} steps of process @{text q}, the proof
      is immediately reduced to the induction hypothesis.
    *}
    fix q'
    assume rcvmsg: "fg_rcv_msg p' q' ?HO ?SHO ?cfg ?cfg'"
    hence rd: "?rd (Suc n) = ?rd n" by (auto simp: fg_rcv_msg_def)
    show "?P (Suc n)"
    proof (cases "?rcvd n")
      case True
      with ih p rd show ?thesis by simp
    next
      case False
      from rcvmsg obtain m' m'' where
        "(q', round ?cfg p', p', m') \<in> network ?cfg"
        "rcvd ?cfg' = (rcvd ?cfg)(p' := (rcvd ?cfg p')(q' := 
                          if q' \<in> ?SHO then Some m' else Some m''))"
        by (auto simp: fg_rcv_msg_def split del: split_if_asm)
      with False rcvd p rd have "(p, ?rd n, q, m) \<in> network ?cfg" by auto
      with rho rd show ?thesis by (auto simp: fg_invariant1)
    qed
  next
    fix q'
    assume "fg_send_msg A p' q' ?cfg ?cfg'"
    with rcvd have "?rcvd n" and "?rd (Suc n) = ?rd n"
      by (auto simp: fg_send_msg_def)
    with p ih show "?P (Suc n)" by simp
  next
    assume "fg_local A p' ?HO ?crd ?cfg ?cfg'"
    with rcvd have "?rcvd n" and "?rd (Suc n) = ?rd n"
      -- {* in fact, @{text "p' = q"} is impossible because the @{text rcvd} field of @{text p'} is cleared *}
      by (auto simp: fg_local_def)
    with p ih show "?P (Suc n)" by simp
  qed
qed

subsection {* From Fine-Grained to Coarse-Grained Runs *}

text {*
  The reduction theorem asserts that for any fine-grained run @{text rho}
  there is a coarse-grained run such that every process sees the same
  sequence of local states in the two runs, modulo stuttering. In other words,
  no process can locally distinguish the two runs.

  Given fine-grained run @{text rho}, the corresponding coarse-grained run @{text sigma} is 
  defined as the sequence of state vectors at the beginning of every round. 
  Notice in particular that the local states @{text "sigma r p"} and 
  @{text "sigma r q"} of two different processes @{text p} and @{text q}
  appear at different instants in the original run @{text rho}. Nevertheless,
  we prove that @{text sigma} is a coarse-grained run of the algorithm for
  the same HO, SHO, and coordinator assignments. By definition (and the
  fact that local states remain equal between @{text fg_start_round}
  instants), the sequences of process states in @{text rho} and
  @{text sigma} are easily seen to be stuttering equivalent, and this
  will be formally stated below.
*}

definition coarse_run where
  "coarse_run rho r p \<equiv> state (rho (fg_start_round rho p r)) p"

theorem reduction:
  assumes rho: "fg_run A rho HOs SHOs coords"
  shows "CSHORun A (coarse_run rho) HOs SHOs coords"
        (is "CSHORun _ ?cr _ _ _")
proof (auto simp: CSHORun_def)
  from rho show "CHOinitConfig A (?cr 0) (coords 0)"
    by (auto simp: fg_run_def fg_init_config_def CHOinitConfig_def 
                   coarse_run_def fg_start_round_0[OF rho])
next
  fix r
  show "CSHOnextConfig A r (?cr r) (HOs r) (SHOs r) (coords (Suc r))
                       (?cr (Suc r))"
  proof (auto simp add: CSHOnextConfig_def)
    fix p
    from rho[THEN fg_local_transition_from_round] obtain n
      where n: "round (rho n) p = r"
        and start: "fg_start_round rho p (Suc r) = Suc n" (is "?start = _")
        and loc: "fg_local A p (HOs r p) (coords (Suc r) p) (rho n) (rho (Suc n))"
                 (is "fg_local _ _ ?HO ?crd ?cfg ?cfg'")
      by blast
    have cfg: "?cr r p = state ?cfg p"
      unfolding coarse_run_def proof (rule fg_same_round_same_state[OF rho])
      from n show "round (rho (fg_start_round rho p r)) p = round ?cfg p"
        by (simp add: fg_start_round[OF rho])
    qed
    from start have cfg': "?cr (Suc r) p = state ?cfg' p"
      by (simp add: coarse_run_def)
    have rcvd: "rcvd ?cfg p \<in> SHOmsgVectors A r p (?cr r) ?HO (SHOs r p)"
    proof (auto simp: SHOmsgVectors_def)
      fix q
      assume "q \<in> ?HO"
      with n loc show "\<exists>m. rcvd ?cfg p q = Some m" by (auto simp: fg_local_def)
    next
      fix q m
      assume "rcvd ?cfg p q = Some m"
      with rho n show "q \<in> ?HO" by (auto simp: fg_invariant2a)
    next
      fix q
      assume sho: "q \<in> SHOs r p" and ho: "q \<in> ?HO"
      from ho n loc obtain m where "rcvd ?cfg p q = Some m"
        by (auto simp: fg_local_def)
      with rho n sho show "rcvd ?cfg p q = Some (sendMsg A r q p (?cr r q))"
        by (auto simp: fg_invariant2b coarse_run_def)
    qed
    with n loc cfg cfg'
    show "\<exists>\<mu> \<in> SHOmsgVectors A r p (?cr r) ?HO (SHOs r p).
             CnextState A r p (?cr r p) \<mu> ?crd (?cr (Suc r) p)"
      by (auto simp: fg_local_def)
  qed
qed


subsection {* Locally Similar Runs and Local Properties *}

text {*
  We say that two sequences of configurations (vectors of process states)
  are \emph{locally similar} if for every process the sequences of its
  process states are stuttering equivalent. Observe that different stuttering
  reduction may be applied for every process, hence the original sequences of
  configurations need not be stuttering equivalent and can indeed differ
  wildly in the combinations of local states that occur.

  A property of a sequence of configurations is called \emph{local} if it
  is insensitive to local similarity.
*}

definition locally_similar where
  "locally_similar (\<sigma>::nat \<Rightarrow> 'proc \<Rightarrow> 'pst)  \<tau> \<equiv> 
   \<forall>p::'proc. (\<lambda>n. \<sigma> n p) \<approx> (\<lambda>n. \<tau> n p)"

definition local_property where
  "local_property P \<equiv>
   \<forall>\<sigma> \<tau>. locally_similar \<sigma> \<tau> \<longrightarrow> P \<sigma> \<longrightarrow> P \<tau>"

text {*
  Local similarity is an equivalence relation.
*}

lemma locally_similar_refl: "locally_similar \<sigma> \<sigma>"
  by (simp add: locally_similar_def stutter_equiv_refl)

lemma locally_similar_sym: "locally_similar \<sigma> \<tau> \<Longrightarrow> locally_similar \<tau> \<sigma>"
  by (simp add: locally_similar_def stutter_equiv_sym)

lemma locally_similar_trans [trans]:
  "locally_similar \<rho> \<sigma> \<Longrightarrow> locally_similar \<sigma> \<tau> \<Longrightarrow> locally_similar \<rho> \<tau>"
  by (force simp add: locally_similar_def elim: stutter_equiv_trans)

lemma local_property_eq:
  "local_property P = (\<forall>\<sigma> \<tau>. locally_similar \<sigma> \<tau> \<longrightarrow> P \<sigma> = P \<tau>)"
  by (auto simp: local_property_def dest: locally_similar_sym)

text {*
  Consider any fine-grained run @{text rho}. The projection of @{text rho}
  to vectors of process states is locally similar to the coarse-grained run
  computed from @{text rho}.
*}

lemma coarse_run_locally_similar:
  assumes rho: "fg_run A rho HOs SHOs coords"
  shows "locally_similar (state \<circ> rho) (coarse_run rho)"
proof (auto simp: locally_similar_def)
  fix p
  show "(\<lambda>n. state (rho n) p) \<approx> (\<lambda>n. coarse_run rho n p)" (is "?fgr \<approx> ?cgr")
  proof (rule stutter_equivI)
    show "stutter_sampler (fg_start_round rho p) ?fgr"
    proof (auto simp: stutter_sampler_def)
      from rho show "fg_start_round rho p 0 = 0"
        by (rule fg_start_round_0)
    next
      show "strict_mono (fg_start_round rho p)"
        by (rule fg_start_round_strict_mono[OF rho])
    next
      fix r n
      assume "fg_start_round rho p r < n" and "n < fg_start_round rho p (Suc r)"
      with rho have "round (rho n) p = round (rho (fg_start_round rho p r)) p"
        by (simp add: fg_start_round fg_round_between_start_rounds)
      with rho show "state (rho n) p = state (rho (fg_start_round rho p r)) p"
        by (rule fg_same_round_same_state)
    qed
  next
    show "stutter_sampler id ?cgr"
      by (rule id_stutter_sampler)
  next
    show "?fgr \<circ> fg_start_round rho p = ?cgr \<circ> id"
      by (auto simp: coarse_run_def)
  qed
qed

text {*
  Therefore, in order to verify a local property @{text P} for a
  fine-grained run over given @{text HO}, @{text SHO}, and @{text coord}
  collections, it is enough to show that @{text P} holds for all
  coarse-grained runs for these same collections.
  Indeed, one may restrict attention to coarse-grained runs whose 
  initial states agree with that of the given fine-grained run.
*}

theorem local_property_reduction:
  assumes rho: "fg_run A rho HOs SHOs coords"
      and P: "local_property P"
      and coarse_correct: 
            "\<And> crho. \<lbrakk> CSHORun A crho HOs SHOs coords; crho 0 = state (rho 0)\<rbrakk>
                      \<Longrightarrow> P crho"
  shows "P (state \<circ> rho)"
proof -
  have "coarse_run rho 0 = state (rho 0)"
    by (rule ext, simp add: coarse_run_def fg_start_round_0[OF rho])
  from rho[THEN reduction] this 
  have "P (coarse_run rho)" by (rule coarse_correct)
  with coarse_run_locally_similar[OF rho] P 
  show ?thesis by (auto simp: local_property_eq)
qed


subsection {* Consensus as a Local Property *}

text {*
  Consensus and Weak Consensus are local properties and can therefore
  be verified just over coarse-grained runs, according to theorem
  @{text local_property_reduction}.
*}

lemma integrity_is_local:
  assumes sim: "locally_similar \<sigma> \<tau>"
      and val: "\<And>n. dec (\<sigma> n p) = Some v \<Longrightarrow> v \<in> range vals"
      and dec: "dec (\<tau> n p) = Some v"
  shows "v \<in> range vals"
proof -
  from sim have "(\<lambda>r. \<sigma> r p) \<approx> (\<lambda>r. \<tau> r p)" by (simp add: locally_similar_def)
  then obtain m where "\<sigma> m p = \<tau> n p" by (rule stutter_equiv_element_left)
  from sym[OF this] dec show ?thesis by (auto elim: val)
qed

lemma validity_is_local:
  assumes sim: "locally_similar \<sigma> \<tau>"
      and val: "\<And>n. dec (\<sigma> n p) = Some w \<Longrightarrow> w = v"
      and dec: "dec (\<tau> n p) = Some w"
  shows "w = v"
proof -
  from sim have "(\<lambda>r. \<sigma> r p) \<approx> (\<lambda>r. \<tau> r p)" by (simp add: locally_similar_def)
  then obtain m where "\<sigma> m p = \<tau> n p" by (rule stutter_equiv_element_left)
  from sym[OF this] dec show ?thesis by (auto elim: val)
qed

lemma agreement_is_local:
  assumes sim: "locally_similar \<sigma> \<tau>"
  and agr: "\<And>m n. \<lbrakk>dec (\<sigma> m p) = Some v; dec (\<sigma> n q) = Some w\<rbrakk> \<Longrightarrow> v=w"
  and v: "dec (\<tau> m p) = Some v" and w: "dec (\<tau> n q) = Some w"
  shows "v = w"
proof -
  from sim have "(\<lambda>r. \<sigma> r p) \<approx> (\<lambda>r. \<tau> r p)" by (simp add: locally_similar_def)
  then obtain m' where m': "\<sigma> m' p = \<tau> m p" by (rule stutter_equiv_element_left)
  from sim have "(\<lambda>r. \<sigma> r q) \<approx> (\<lambda>r. \<tau> r q)" by (simp add: locally_similar_def)
  then obtain n' where n': "\<sigma> n' q = \<tau> n q" by (rule stutter_equiv_element_left)
  from sym[OF m'] sym[OF n'] v w show "v = w" by (auto elim: agr)
qed

lemma termination_is_local:
  assumes sim: "locally_similar \<sigma> \<tau>"
      and trm: "dec (\<sigma> m p) = Some v"
  shows "\<exists>n. dec (\<tau> n p) = Some v"
proof -
  from sim have "(\<lambda>r. \<sigma> r p) \<approx> (\<lambda>r. \<tau> r p)" by (simp add: locally_similar_def)
  then obtain n where "\<sigma> m p = \<tau> n p" by (rule stutter_equiv_element_right)
  with trm show ?thesis by auto
qed

theorem consensus_is_local: "local_property (consensus vals dec)"
proof (auto simp: local_property_def consensus_def)
  fix \<sigma> \<tau> n p v
  assume "locally_similar \<sigma> \<tau>"
  and "\<forall>n p v. dec (\<sigma> n p) = Some v \<longrightarrow> v \<in> range vals"
  and "dec (\<tau> n p) = Some v"
  thus "v \<in> range vals" by (blast intro: integrity_is_local)
next
  fix \<sigma> \<tau> m n p q v w
  assume "locally_similar \<sigma> \<tau>"
  and "\<forall>m n p q v w. dec (\<sigma> m p) = Some v \<and> dec (\<sigma> n q) = Some w \<longrightarrow> v = w"
  and "dec (\<tau> m p) = Some v" and "dec (\<tau> n q) = Some w"
  thus "v = w" by (blast intro: agreement_is_local)
next
  fix \<sigma> \<tau> p
  assume "locally_similar \<sigma> \<tau>"
  and "\<forall>p. \<exists>m v. dec (\<sigma> m p) = Some v"
  thus "\<exists>n w. dec (\<tau> n p) = Some w" by (blast dest: termination_is_local)
qed

theorem weak_consensus_is_local: "local_property (weak_consensus vals dec)"
proof (auto simp: local_property_def weak_consensus_def)
  fix \<sigma> \<tau> n p v w
  assume "locally_similar \<sigma> \<tau>"
  and "\<forall>n p w. dec (\<sigma> n p) = Some w \<longrightarrow> w = v"
  and "dec (\<tau> n p) = Some w"
  thus "w = v" by (blast intro: validity_is_local)
next
  fix \<sigma> \<tau> m n p q v w
  assume "locally_similar \<sigma> \<tau>"
  and "\<forall>m n p q v w. dec (\<sigma> m p) = Some v \<and> dec (\<sigma> n q) = Some w \<longrightarrow> v = w"
  and "dec (\<tau> m p) = Some v" and w: "dec (\<tau> n q) = Some w"
  thus "v = w" by (blast intro: agreement_is_local)
next
  fix \<sigma> \<tau> p
  assume "locally_similar \<sigma> \<tau>"
  and "\<forall>p. \<exists>m v. dec (\<sigma> m p) = Some v"
  thus "\<exists>n w. dec (\<tau> n p) = Some w" by (blast dest: termination_is_local)
qed


end
