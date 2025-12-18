(* Title:      	   Circular-Buffer Queue-Lock
   Author(s):     Robert Colvin, Scott Heiner, Peter Hoefner, Roger Su
   License:       BSD 2-Clause
   Maintainer(s): Roger Su <roger.c.su@proton.me>
                  Peter Hoefner <peter@hoefner-online.de>
*)

section \<open>Circular-Buffer Queue-Lock\<close>

text \<open>This theory imports Annotated Commands to access the rely-guarantee 
library extensions, and also imports the Abstract Queue Lock to access
the definitions of the type-synonym @{text thread_id} and the abbreviation
@{text at_head}.\<close>

theory Lock_Circular_Buffer

imports
  RG_Annotated_Commands
  Lock_Abstract_Queue

begin

type_synonym index = nat

datatype flag_status = Pending | Granted

text \<open>We assume a fixed number of threads, and the size of the
circular array is 1 larger the number of threads.\<close>

consts NumThreads :: nat

abbreviation ArraySize :: "nat" where
  "ArraySize \<equiv> NumThreads + 1"

(*==================================================================*)
text \<open>The state of the Circular Buffer Lock consists of the following fields:
\begin{itemize}

  \item @{text myindex}:
    a function that maps each thread to an array-index
    (where the array is modelled by @{text flag_mapping} below).

  \item @{text flag_mapping}:
    an array of size @{text ArraySize} that stores values of type
    @{type flag_status}.

  \item @{text tail}:
    an index representing the tail of the queue, used when a
    thread enqueues.

  \item @{text aux_head}:
    an auxiliary variable that stores the index used by the thread at
    the head of the queue; the head of the queue spins
    on the flag @{text \<open>flag_mapping aux_head\<close>}.

  \item @{text aux_queue}: the auxiliary queue of threads.

  \item @{text aux_mid_release}: 
    an auxiliary variable that signals if a thread has executed the 
    first instruction of \isa{release}, but not the second.
\end{itemize}\<close>

record cblock_state =
  myindex :: "thread_id \<Rightarrow> index"
  flag_mapping :: "index \<Rightarrow> flag_status"
  tail :: index
  aux_head :: index
  aux_queue :: "thread_id list"
  aux_mid_release :: "thread_id option"

(*------------------------------------------------------------------*)
text \<open>We initialise the array of flags (@{text flag_mapping}) with 
@{text Granted} in the zeroth entry and @{text Pending} in all other 
entries. The indices @{text tail} and @{text aux_head} are initialised
to 0. The queue is initially empty, and no thread is in the middle of
@{text release}. (See the conference article for an example.)\<close>

definition cblock_init :: "cblock_state set" where
  "cblock_init \<equiv> \<lbrace>
    \<acute>flag_mapping = (\<lambda> _. Pending)(0 := Granted) \<and>
    \<acute>tail = 0 \<and>
    \<acute>aux_queue = [] \<and>
    \<acute>aux_head = 0 \<and>
    \<acute>aux_mid_release = None \<rbrace>"

(*------------------------------------------------------------------*)
text \<open>Similar to the Abstract Queue Lock, the @{text acquire} procedure
of the Circular Buffer Lock consists of two conceptual steps, and
corresponds to the pseudocode below.
%
(1) To join the queue, Thread @{term i} stores the global index 
@{term tail} locally as @{term \<open>myindex i\<close>}, and atomically increments
@{term tail} modulo the array size.
%
(2) Thread @{term i} then spins on its flag, which is the entry in the
array at index @{term \<open>myindex i\<close>}. When this flag changes from
@{text Pending} to @{text Granted}, the thread has reached the head of
the queue.
%
@{theory_text[display = true] \<open>
  acquire \<equiv> ((myindex i := tail) \<circ>>
              (tail := (tail + 1) mod ArraySize));
             WHILE flag_mapping (myindex i) = Pending DO SKIP OD\<close>}

When Thread @{term i} releases the lock, it sets its flag to @{text Pending}.
Then it sets the flag of the next thread to @{text Granted}, which corresponds
to the `next' entry in the array, modulo the array size. This is encoded as
the pseudocode below.
%
@{theory_text[display = true] \<open>
  release \<equiv> flag_mapping[myindex i] := Pending ;
             flag_mapping[(myindex i + 1) mod ArraySize] := Granted\<close>}\<close>

(*------------------------------------------------------------------*)
text \<open>\paragraph{Auxiliary Variables.}
The @{text release} procedure consists of the single conceptual step of
exiting the queue, but is implemented here as two separate instructions.
Hence, the auxiliary variable @{term aux_mid_release} indicates when a
thread is between the two lines of @{text release}, and allows us to 
express the assertion there.

The other two auxiliary variables, @{term aux_head} (the \emph{head-index})
and @{term aux_queue}, store information that can in principle be inferred 
from the concrete variables (i.e.\ the non-auxiliary variables).
However, explicitly recording this information as auxiliary variables
greatly simplifies the verification process.

In the code, these auxiliary variables need to be updated atomically
with the relevant instructions. Below is the code of @{text release}
with the auxiliary variables included.
(Auxiliary variables are added to @{text acquire} in a similar way.)

@{theory_text[display = true] \<open>
  release \<equiv> \<langle> flag_mapping[myindex i] := Pending \<circ>>
              aux_mid_release := Some i \<rangle> ;
            \<langle> flag_mapping[(myindex i + 1) mod ArraySize] := Granted \<circ>>
              aux_queue := tl aux_queue \<circ>>
              aux_head := (aux_head + 1) mod ArraySize \<circ>>
              aux_mid_release := None \<rangle>\<close>}\<close>

(*==================================================================*)
text \<open>Recall that we assume a fixed number of threads. This constant
is furthermore assumed positive, which we enforce with the use of the
following locale.\<close>

locale numthreads_positive =
  assumes assm_locale: "0 < NumThreads"
begin

subsection \<open>Invariant\<close>

(*------------------------------------------------------------------*)
text \<open>A notion that helps us state the queue-clause of the invariant.
The list of indices use by the queuing threads is a contiguous list of
integers modulo @{text ArraySize}. Note the possibility of ``wrapping
around'', which is covered by the ``else'' clause in the definition.\<close>

definition used_indices :: "cblock_state \<Rightarrow> index list" where
  "used_indices s \<equiv> (if aux_head s \<le> tail s
     then [aux_head s ..< tail s]
     else [aux_head s ..< ArraySize] @ [0 ..< tail s])"

lemma distinct_used_indices: "distinct (used_indices s)"
  using used_indices_def by fastforce

lemma length_used_indices:
  "length (used_indices s) = (if aux_head s \<le> tail s
     then tail s - aux_head s
     else ArraySize - aux_head s + tail s)"
  using used_indices_def by force

(*------------------------------------------------------------------*)
text \<open>The invariant of the Circular Buffer Lock is stated as separate
parts below.
%
The first definition @{text invar_flag} relates @{term flag_mapping}
with the head-index @{term aux_head}, and consists of two clauses.
%
(1)
At every index that is not the head-index, the flag must be @{text Pending}.
%
(2) As for the head-index itself, there are two possibilities.
When the thread at the head of the queue invoked @{text release}
but has only executed its first instruction, 
@{term aux_mid_release} becomes set to @{term \<open>Some i\<close>};
in this case, the flag at the head-index is set to Pending, 
but the thread remains in the queue. 
In all other cases, @{text \<open>aux_mid_release = None\<close>}, 
and the flag at the head-index is always @{text Granted}.\<close>

definition invar_flag :: "cblock_state set" where
  "invar_flag \<equiv> \<lbrace>
    (\<forall> i \<noteq> \<acute>aux_head. \<acute>flag_mapping i = Pending) \<and>
    (\<acute>flag_mapping \<acute>aux_head = Pending \<longleftrightarrow> \<acute>aux_mid_release \<noteq> None) \<rbrace>"

text \<open>The next clause @{text invar_queue} describes the relationship
between the auxiliary queue and the other variables, including the set 
@{term used_indices}.
The clause involving @{term map} further implies a number of properties, 
such as the distinctness of @{term aux_queue} (which mirrors the invariant 
of the Abstract Queue Lock), and the injectivity of @{term myindex}
(i.e.\ each queuing thread has a unique index).\<close>

definition invar_queue :: "cblock_state set" where
  "invar_queue \<equiv> \<lbrace>
    (\<forall> i. i \<in> set \<acute>aux_queue \<longrightarrow> i < NumThreads) \<and>
    (map \<acute>myindex \<acute>aux_queue = \<acute>used_indices) \<rbrace>"

text \<open>The overall invariant, @{text cblock_invar}, is the conjunction
of @{text invar_flag} and @{text invar_queue} above, with additional
inequalities concerning @{term tail}, @{term aux_head}, and 
@{term NumThreads}.\<close>

definition invar_bounds :: "cblock_state set" where
  "invar_bounds \<equiv> \<lbrace>
        \<acute>tail < ArraySize \<and>
    \<acute>aux_head < ArraySize \<rbrace>"

abbreviation cblock_invar :: "thread_id \<Rightarrow> cblock_state set" where
  "cblock_invar i \<equiv>
    invar_flag \<inter> invar_bounds \<inter> invar_queue \<inter> \<lbrace> i < NumThreads \<rbrace>"

lemmas cblock_invariants =
  invar_flag_def
  invar_bounds_def
  invar_queue_def
  used_indices_def

(*------------------------------------------------------------------*)
subsubsection \<open>Invariant Methods\<close>

text \<open>We set up methods that generate structured proofs with named
subgoals, to help us prove the clauses of the invariant.\<close>

theorem thm_method_invar_flag:
  assumes "\<forall> i \<noteq> aux_head s. flag_mapping s i = Pending"
      and "flag_mapping s (aux_head s) = Pending
           \<longleftrightarrow> aux_mid_release s \<noteq> None"
    shows "s \<in> invar_flag"
  using assms invar_flag_def by force

method method_invar_flag =
  cases rule:thm_method_invar_flag,
  goal_cases non_head_pending head_maybe_granted

theorem thm_method_invar_queue:
  assumes "\<forall> i. i \<in> set (aux_queue s) \<longrightarrow> i < NumThreads"
      and "map (myindex s) (aux_queue s) = (used_indices s)"
    shows "s \<in> invar_queue"
  using assms invar_queue_def by force

method method_invar_queue =
  cases rule:thm_method_invar_queue,
  goal_cases bound_thread_id map_used_indices

theorem thm_method_invar:
  assumes flag:  "s \<in> invar_flag"
      and bound: "s \<in> invar_bounds \<and> i < NumThreads"
      and queue: "s \<in> invar_queue"
    shows "s \<in> cblock_invar i"
  using assms by fastforce

method method_cblock_invar =
  cases rule:thm_method_invar,
  goal_cases flag bound queue

(*------------------------------------------------------------------*)
subsubsection \<open>Invariant Lemmas\<close>

text \<open>The initial state satisfies the invariant.\<close>

lemma cblock_init_invar:
  assumes assm_init:  "s \<in> cblock_init"
      and assm_bound: "i < NumThreads"
    shows "s \<in> cblock_invar i"
proof method_cblock_invar
  case flag
  thus ?case
    using assms
    by (method_invar_flag; force simp: cblock_init_def)
next
  case bound
  thus ?case
    using assms 
    by (force simp: assm_locale cblock_init_def invar_bounds_def)
next
  case queue
  thus ?case
    using assms
    by (method_invar_queue; force simp: cblock_init_def used_indices_def)
qed

text \<open>In a state that satisfies the flag-invariant, a thread is the head
of the queue if its flag is Granted. (If the flag of a thread is Pending,
the thread may still be at the head of the queue. In this case, the thread
must be between the two instructions in @{text release}.)\<close>

lemma only_head_is_granted:
  assumes "s \<in> invar_flag"
      and "flag_mapping s i = Granted"
    shows "i = aux_head s"
  using assms by (force simp: invar_flag_def)

text \<open>Let @{text s} be a state that satisfies the bounds-invariant,
with $n$ queuing threads. If we start from the @{text aux_head} index,
and ``advance'' $n$ steps (with potential wrap-around), then we reach
the global @{text tail} index.\<close>

lemma head_tail_mod:
  "s \<in> invar_bounds \<Longrightarrow>
    tail s = (aux_head s + length (used_indices s)) mod (ArraySize)"
  by (fastforce simp: mod_if used_indices_def invar_bounds_def)

text \<open>If a state satisfies the queue-invariant (namely the clause with
the @{text map} function, then the @{text myindex} function is injective
on the set of queuing threads. In other words, every queuing thread has
a unique index in a state that satisfies the queue-invariant.\<close>

lemma invar_map_inj_on:
  "s \<in> invar_queue \<Longrightarrow> inj_on (myindex s) (set (aux_queue s))"
  using distinct_map
  by (fastforce simp: invar_queue_def distinct_used_indices)

text \<open>In a state that satisfies the queue-invariant, the length of the
queue is equal to the length of the list of used indices.\<close>

lemma used_indices_map_queue:
  "s \<in> invar_queue \<Longrightarrow> used_indices s = map (myindex s) (aux_queue s)" 
  unfolding used_indices_def invar_queue_def used_indices_def
  by clarsimp

lemma length_used_indices_queue:
  "s \<in> invar_queue \<Longrightarrow> length (used_indices s) = length (aux_queue s)"
  by (fastforce simp: used_indices_map_queue)

text \<open>In a state that fully satisfies the invariant, if there is a
thread that is not in the queue, then the length of the queue must
be smaller than the total number of threads.\<close>

lemma queue_bounded:
  assumes "s \<in> cblock_invar i"
      and "i \<notin> set (aux_queue s)"
    shows "length (aux_queue s) < NumThreads"
proof-
  have "length (used_indices s) \<le> NumThreads"
    using assms(1)
    by (fastforce simp: invar_bounds_def length_used_indices )
  hence "card (set (aux_queue s)) \<le> NumThreads"
    using assms(1)
    by (fastforce intro: le_trans intro!:  card_length simp: length_used_indices_queue)
  moreover have "card (set (aux_queue s)) = 0 \<longleftrightarrow> aux_queue s = []"
    by fastforce
  moreover have "finite (set (aux_queue s))"
    using calculation by fastforce
  moreover have "card (set (aux_queue s)) = NumThreads
                 \<longleftrightarrow> (\<forall> j < NumThreads. j \<in> set (aux_queue s))"
  proof-
    { assume "card (set (aux_queue s)) = NumThreads"
      hence "set (aux_queue s) = {j. j < NumThreads}"
        using assms by (force simp add: invar_queue_def card_subset_eq subsetI)
      hence "\<forall> j < NumThreads. j \<in> set (aux_queue s)"
        by blast }
    moreover
    { assume "\<forall> j < NumThreads. j \<in> set (aux_queue s)"
      hence "card (set (aux_queue s)) = NumThreads"
        using assms by fastforce }
    ultimately 
      show ?thesis by blast
  qed

  ultimately have "card (set (aux_queue s)) < NumThreads"
    using assms nat_less_le by blast
  
  thus ?thesis 
    using assms
    by (metis used_indices_map_queue Int_iff distinct_card distinct_map distinct_used_indices)
qed

text \<open>If a state that satisfies the bound- and queue-invariants, and
if the queue is non-empty, then the index held by the head of the
queue must be the same as @{text aux_head}.\<close>

lemma head_and_head_index:
  assumes "s \<in> invar_bounds \<inter> invar_queue"
      and "aux_queue s \<noteq> []"
    shows "myindex s (hd (aux_queue s)) = aux_head s"
proof-
  have "myindex s (hd (aux_queue s)) = hd (used_indices s)"
    using assms
    by (simp add: used_indices_map_queue hd_map)
  also have "... = aux_head s"    
    using assms
    by (fastforce simp: invar_queue_def invar_bounds_def upt_rec used_indices_def)
  ultimately show ?thesis 
    by fastforce
qed

text \<open>In a state that satisfies the full invariant, if no thread is
half-way through \emph{release} and Thread @{text i} is at the head
of the queue, then the flag of Thread @{text i} must be Granted.\<close>

lemma head_is_granted:
  assumes "s \<in> cblock_invar i"
      and "aux_mid_release s = None"
      and "i = hd (aux_queue s)"
      and "aux_queue s \<noteq> []"
    shows "flag_mapping s (myindex s i) = Granted"
proof-
  have "myindex s i = aux_head s"
    using assms by (fastforce intro: head_and_head_index)
  thus ?thesis
    using assms
    by (fastforce intro: flag_status.exhaust simp: invar_flag_def)
qed

text \<open>In a state that satisfies the queue-invariant, the global index
@{text tail} is never held by a thread. Indeed, @{text tail} is meant
to be ``free'' for the next thread that joins the queue. Note that
when a thread is not in the queue, its index @{text i} becomes outdated,
and @{text tail} may cycle back and coincide with @{text i}.\<close>

lemma tail_never_used:
  assumes "s \<in> invar_queue"
    shows "\<forall> j \<in> set (aux_queue s). myindex s j \<noteq> tail s"
proof-
  have "tail s \<notin> set (used_indices s)"
    unfolding used_indices_def by clarsimp
  thus ?thesis
    unfolding invar_queue_def
    by (fastforce simp: assms used_indices_map_queue rev_image_eqI)
qed

text \<open>In a state that satisfies the full invariant, if the @{text tail}
index is right before the @{text aux_head} index, then it must be the
case that every thread is in the queue.\<close>

lemma used_indices_full:
  assumes "s \<in> cblock_invar i"
      and "(tail s + 1) mod ArraySize = aux_head s"
    shows "length (used_indices s) = NumThreads"
  using assms
  apply (clarsimp simp: used_indices_def)
  apply (intro conjI impI)
     apply (metis Suc_eq_plus1 add_diff_cancel_left' diff_zero head_tail_mod le_add_diff_inverse 
                  length_used_indices lessI linorder_not_le mod_Suc plus_1_eq_Suc)
    apply (fastforce simp: Suc_diff_le)
   by (metis mod_Suc_le_divisor)+

text \<open>Conversely, if not every thread is in the queue, then the
@{text tail} index is not right before the @{text aux_head} index.\<close>

lemma space_available:
  assumes assm_invar: "s \<in> cblock_invar i"
      and assm_q: "i \<notin> set (aux_queue s)"
    shows "(tail s + 1) mod ArraySize \<noteq> aux_head s"
  using assms queue_bounded length_used_indices_queue
  by (fastforce simp: used_indices_full)

text \<open>The next lemma relates the \emph{append} operation on the
@{text aux_head} and @{text tail} indices to the \emph{append}
operation on the list of @{text used_indices}. (The second and
the last assumptions are the most crucial ones. The rest are
side-condition checks.)\<close>

lemma used_indices_append:
  assumes "s \<in> cblock_invar i"
      and "aux_head s' = aux_head s"
      and "length (used_indices s) < NumThreads"
      and "(tail s + 1) mod ArraySize \<noteq> aux_head s"
      and "tail s' = (tail s + 1) mod ArraySize"
    shows "used_indices s' = used_indices s @ [tail s]"
proof (cases "aux_head s' \<le> tail s'")
  case True (* tail s' \<ge> aux_head s' *)
  hence ln1: "tail s' = (tail s + 1)"
    using assms apply clarsimp
    by (metis Suc_eq_plus1 bot_nat_0.extremum_unique head_tail_mod mod_Suc mod_mod_trivial)
  thus ?thesis 
    using assms used_indices_def ln1 by fastforce
next
  case False (* tail s' < aux_head s' *)
  hence a: "\<not> aux_head s' \<le> tail s'" .
  thus ?thesis
  proof (cases "tail s' = 0")
    case True
    thus ?thesis
      using assms apply clarsimp
      by (metis (no_types, lifting) Suc_eq_plus1 Suc_lessI Zero_not_Suc append.right_neutral 
                assms(5) invar_bounds_def linorder_not_le mem_Collect_eq mod_less upt_Suc 
                upt_eq_Nil_conv used_indices_def)
  next
    case False
    thus ?thesis
    proof -
      have "tail s < tail s'"
        using assms(1) assms(5) apply clarsimp
        by (metis False Suc_eq_plus1 head_tail_mod lessI mod_Suc mod_mod_trivial)
      thus ?thesis
        by (metis a used_indices_def assms(2,5) Suc_eq_plus1 append.assoc less_Suc_eq_le 
                  mod_less_eq_dividend not_less_eq order_less_le upt_Suc_append zero_less_Suc)
    qed
  qed
qed

(*==================================================================*)
subsection \<open>Contract\<close>

text \<open>The contract of the Circular Buffer Lock is devised along three
observations:
(1) local variables do not change;
(2) global variables may change; and
(3) auxiliary variables change similarly as in the Abstract Queue Lock.

The first two areas are covered by @{text contract_raw}.
The only local variable @{term \<open>myindex i\<close>} does not change.
The global variable @{term tail} may change, but is not included in 
the contract, as changes to @{term tail} are not restricted.
%
However, the other global variable @{term flag_mapping} is allowed to
change only in specific ways. As @{term flag_mapping} stores information 
about the head of the conceptual queue, its allowed changes naturally 
relate to the \emph{head stays the head} property. 
%
Under the Circular Buffer Lock, Thread @{term i} is at the head of the
queue when @{text \<open>flag_mapping (myindex i) = Granted\<close>}.
Meanwhile, note that @{term \<open>myindex i\<close>} can become outdated if 
Thread @{term i} is not in the queue. Hence, we need the premise 
@{text \<open>i \<in> set \<ordmasculine>aux_queue\<close>} before the \emph{head stays the head} 
statement in the final clause of @{text contract_raw}.\<close>

definition contract_raw :: "thread_id \<Rightarrow> cblock_state rel" where
  "contract_raw i \<equiv> \<lbrace>
    (i \<in> set \<ordmasculine>aux_queue
     \<longrightarrow> \<ordmasculine>flag_mapping (\<ordmasculine>myindex i) = Granted
     \<longrightarrow> \<ordfeminine>flag_mapping (\<ordfeminine>myindex i) = Granted) \<and>
    (\<ordmasculine>myindex i = \<ordfeminine>myindex i) \<rbrace>"

text \<open>For the auxiliary variable @{term aux_queue} we require the same 
two clauses as in the contract of the Abstract Queue Lock.
%
As for @{term aux_mid_release}, only the head of the queue can invoke 
@{text release} and hence modify @{term aux_mid_release}. Therefore,
the second clause of @{text contract_aux} has the extra equality in
the consequent.\<close>

definition contract_aux :: "thread_id \<Rightarrow> cblock_state rel" where
  "contract_aux i \<equiv> \<lbrace>
    (i \<in> set \<ordmasculine>aux_queue \<longleftrightarrow> i \<in> set \<ordfeminine>aux_queue) \<and>
    (at_head i \<ordmasculine>aux_queue \<longrightarrow> at_head i \<ordfeminine>aux_queue \<and> \<ordmasculine>aux_mid_release = \<ordfeminine>aux_mid_release) \<rbrace>"

text \<open>The two definitions above combine into the overall contract.\<close>

abbreviation cblock_contract :: "thread_id \<Rightarrow> cblock_state rel" where
  "cblock_contract t \<equiv> contract_raw t \<inter> contract_aux t"

lemmas cblock_contracts[simp] = contract_raw_def contract_aux_def

(*==================================================================*)
subsection \<open>RG Lemmas\<close>

abbreviation acq_line1 :: "thread_id \<Rightarrow> cblock_state \<Rightarrow> cblock_state" where
  "acq_line1 i \<equiv>
    (\<acute>myindex[i] \<leftarrow> \<acute>tail) \<circ>>
    (\<acute>tail \<leftarrow> (\<acute>tail + 1) mod ArraySize) \<circ>>
    (\<acute>aux_queue \<leftarrow> \<acute>aux_queue @ [i])"

lemma acq_1_invar:
  assumes assm_old: "s \<in> cblock_invar i"
      and assm_new: "s' = acq_line1 i s"
      and assm_pre: "i \<notin> set (aux_queue s)"
    shows "s' \<in> cblock_invar i"
proof method_cblock_invar
  case flag
  have "(\<forall> j \<noteq> aux_head s. flag_mapping s j = Pending) \<and>
        (flag_mapping s (aux_head s) = Pending \<longleftrightarrow> aux_mid_release s \<noteq> None)"
    using assm_old by (fastforce simp: invar_flag_def)
  hence "(\<forall> j \<noteq> aux_head s'. flag_mapping s' j = Pending) \<and>
         (flag_mapping s' (aux_head s') = Pending \<longleftrightarrow> aux_mid_release s' \<noteq> None)"
    using assm_new by fastforce
  thus ?case 
    by (fastforce simp: invar_flag_def)
next (*----------------------------------------*)
  case bound
  have "aux_head s' < ArraySize"
    using assm_old assm_new by (fastforce simp: invar_bounds_def)
  moreover have "tail s' < ArraySize"
    using assm_new by fastforce
  ultimately show ?case 
    using assm_old assm_new by (fastforce simp: invar_bounds_def)
next (*----------------------------------------*)
  case queue show ?case
  proof method_invar_queue
    case bound_thread_id
    have "\<forall> j. j \<in> set (aux_queue s) \<longrightarrow> j < NumThreads"
      using assm_old assm_new by (fastforce simp: invar_queue_def)
    moreover have "set (aux_queue s') = set (aux_queue s) \<union> {i}"
      using assm_new by fastforce
    moreover have "i < NumThreads"
      using assm_old assm_new by fastforce
    ultimately show ?case 
      by fastforce
  next
    case map_used_indices
    have "map (myindex s') (aux_queue s') = map (myindex s) (aux_queue s) @ [myindex s' i]"
      using assm_new assm_pre by fastforce
    also have ln1: "... = used_indices s @ [myindex s' i]"
      using assm_old by (fastforce simp: used_indices_def invar_queue_def)
    also have "... = used_indices s @ [tail s]"
      using assm_new by fastforce
    also have "... = used_indices s'"
    proof-
      have ahead: "aux_head s = aux_head s'"
        using assms by fastforce 
      have "length (used_indices s) < NumThreads"
        using assm_pre assm_old 
        by (fastforce simp: length_used_indices_queue queue_bounded)
      moreover have "(tail s + 1) mod ArraySize \<noteq> aux_head s"
        using assm_old assm_pre space_available by fastforce
      moreover have "tail s' = (tail s + 1) mod (ArraySize)"
        using assm_new by simp
      ultimately show ?thesis
        by (metis ahead assm_old used_indices_append)
    qed
    ultimately show ?case by fastforce
  qed
qed

theorem cblock_acq1:
 "rely: cblock_contract i    guar: for_others cblock_contract i
  inv:  cblock_invar i  anno_code:
    { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> }
  BasicAnno (acq_line1 i)
    { \<lbrace> i \<in> set \<acute>aux_queue \<rbrace> }"
  apply method_anno_ultimate
    using acq_1_invar by fastforce+

theorem cblock_acq2:
 "rely: cblock_contract i    guar: for_others cblock_contract i
  inv:  cblock_invar i       code:
    { \<lbrace> i \<in> set \<acute>aux_queue \<rbrace> }
  WHILE \<acute>flag_mapping (\<acute>myindex i) = Pending DO SKIP OD
    { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = None \<rbrace> }"
proof method_spinloop
  case est_post
  thus ?case
  proof-
    { fix s assume assm_s: "s \<in> cblock_invar i \<inter> \<lbrace> i \<in> set \<acute>aux_queue \<rbrace> \<inter>
                            \<lbrace> \<acute>flag_mapping (\<acute>myindex i) \<noteq> Pending \<rbrace>"
      hence ln1:"aux_queue s \<noteq> []"
        by force
      have ln2:"flag_mapping s (aux_head s) \<noteq> Pending"
        using assm_s invar_flag_def by force
      hence ln3:"myindex s i = aux_head s"
        using assm_s invar_flag_def
        by (metis (mono_tags, lifting) IntE mem_Collect_eq)
      have "i = hd (aux_queue s) \<and> s \<in> \<lbrace> \<acute>aux_mid_release = None \<rbrace>"
        apply (intro conjI)
         using ln1 ln3 assm_s 
         apply (metis (lifting) Int_Collect head_and_head_index inf_commute inj_onD invar_bounds_def 
                                invar_flag_def invar_map_inj_on invar_queue_def list.set_sel(1))
        using ln2 ln3  assm_s 
        by (fastforce simp: invar_flag_def flag_status.exhaust)
    }
    thus ?thesis by fastforce
  qed
qed (fastforce+)

(*------------------------------------------------------------------*)
abbreviation rel_line1 :: "thread_id \<Rightarrow> cblock_state \<Rightarrow> cblock_state" where
  "rel_line1 i \<equiv> (\<acute>flag_mapping[\<acute>myindex i] \<leftarrow> Pending) \<circ>>
                  (\<acute>aux_mid_release \<leftarrow> Some i)"

lemma rel_1_same:
  "s' = rel_line1 i s \<Longrightarrow>
    (myindex s = myindex s') \<and>
    (\<forall> j \<noteq> myindex s i. flag_mapping s j = flag_mapping s' j) \<and>
    (tail s = tail s') \<and>
    (aux_head s = aux_head s') \<and>
    (aux_queue s = aux_queue s')"
  by simp

lemma rel_1_invar:
  assumes assm_old: "s \<in> cblock_invar i"
      and assm_new: "s' = rel_line1 i s"
      and assm_pre: "at_head i (aux_queue s) \<and> aux_mid_release s = None"
    shows "s' \<in> cblock_invar i"
proof method_cblock_invar
  case flag show ?case
    apply method_invar_flag
     using  assm_new assm_old assm_pre  
     by (fastforce simp: invar_flag_def head_and_head_index)+
next
  case bound
  thus ?case
    using  assm_old invar_bounds_def assm_new 
    by (metis (no_types, lifting) rel_1_same Int_iff mem_Collect_eq)
next
  case queue show ?case
    apply (method_invar_queue)
    using assm_old assm_new apply (fastforce simp: invar_queue_def)
    by (metis (lifting) assm_old assm_new used_indices_map_queue used_indices_def rel_1_same IntE)
qed

lemma rel_1_est_guar:
  assumes "s \<in> \<lbrace> \<acute>aux_queue \<noteq> [] \<and>
                  hd \<acute>aux_queue = i \<and>
                 \<acute>aux_mid_release = None \<rbrace>
               \<inter> cblock_invar i"
      and "s' = rel_line1 i s"
    shows "(s, s') \<in> for_others cblock_contract i
                 \<inter> pred_to_rel (cblock_invar i)"
proof-
  { fix j assume assm_u_t: "j \<noteq> i"
    have "j \<in> set (aux_queue s)
               \<longrightarrow> flag_mapping s  (myindex s  j) = Granted
               \<longrightarrow> flag_mapping s' (myindex s' j) = Granted"
      using assms assm_u_t 
      by (fastforce intro: simp: head_and_head_index inj_onD dest: invar_map_inj_on)
    moreover have "myindex s j = myindex s' j"
      using assms by (fastforce intro: rel_1_same)
    ultimately have "(s, s') \<in> contract_raw j"
      by fastforce }
  moreover
  { fix j assume "j \<noteq> i"
    hence "hd (aux_queue s) \<noteq> j"
      using assms(1) by simp
    moreover have "j \<in> set (aux_queue s) \<longleftrightarrow> j \<in> set (aux_queue s')"
      using rel_1_same assms(2) by simp
    ultimately have "(s, s') \<in> contract_aux j"
      by fastforce }
  moreover have "(s, s') \<in> pred_to_rel (cblock_invar i)"
    using assms rel_1_invar by fastforce
  ultimately show ?thesis 
    by fastforce
qed

theorem cblock_rel1:
 "rely: cblock_contract i    guar: for_others cblock_contract i
  inv:  cblock_invar i  anno_code:
    { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = None \<rbrace> }
  BasicAnno (rel_line1 i)
    { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = Some i \<rbrace> }"
proof method_anno_ultimate
  case est_guar
  thus ?case
    using rel_1_invar
    by (fastforce dest: invar_map_inj_on simp: inj_on_contraD)
next
  case est_post
  thus ?case
    using rel_1_est_guar by fastforce
qed (fastforce+)

abbreviation rel_line2 :: "thread_id \<Rightarrow> cblock_state \<Rightarrow> cblock_state" where
  "rel_line2 i \<equiv>
    (\<acute>flag_mapping[((\<acute>myindex i + 1) mod ArraySize)] \<leftarrow> Granted) \<circ>>
    (\<acute>aux_queue \<leftarrow> tl \<acute>aux_queue) \<circ>>
    (\<acute>aux_head \<leftarrow> (\<acute>aux_head + 1) mod ArraySize) \<circ>>
    (\<acute>aux_mid_release \<leftarrow> None)"

lemma rel_2_same:
  "s' = rel_line2 i s \<Longrightarrow>
    myindex s = myindex s' \<and>
       tail s = tail s' \<and>
    (\<forall> j \<noteq> (myindex s i + 1) mod ArraySize.
    flag_mapping s j = flag_mapping s' j)"
  by fastforce

lemma rel_2_invar:
  assumes assm_old: "s \<in> cblock_invar i"
      and assm_pre: "at_head i (aux_queue s) \<and> aux_mid_release s = Some i"
      and assm_new: "s' = rel_line2 i s"
    shows "s' \<in> cblock_invar i"
proof method_cblock_invar
  case flag show ?case
  apply (method_invar_flag)
      using assm_new assm_old assm_pre
      by (force simp: head_and_head_index invar_flag_def)+
next
  case bound
  have "tail s' < ArraySize"
    using  assm_new assm_old
    by (fastforce simp: invar_bounds_def)
  moreover have "aux_head s' < ArraySize"
    using assms 
    by fastforce
  moreover have "i < NumThreads"
    using assm_old assm_new by fastforce
  ultimately show ?case
    using invar_bounds_def by blast
next
  case queue show ?case
  proof method_invar_queue
    case bound_thread_id
    show ?case 
      using assm_new assm_old assm_pre 
      by (fastforce simp: invar_queue_def list.set_sel(2))
  next
    case map_used_indices
    have same: "tail s = tail s' \<and>
             myindex s = myindex s'"
      using assm_new by (fastforce intro: rel_2_same)
    have "aux_queue s \<noteq> []"
      using assm_pre by fastforce
    hence d: "aux_head s \<noteq> tail s"
      using assm_old head_and_head_index tail_never_used by force
    have t: "aux_queue s' = tl (aux_queue s)"
      using assm_new by fastforce 
    have m: "map (myindex s) (aux_queue s) = used_indices s"
      using assm_old invar_queue_def by fastforce
    have "used_indices s' = tl (used_indices s)"
    proof-
      { assume a: "aux_head s \<le> tail s"
        hence 1: "aux_head s + 1 < ArraySize"
          using d assm_old invar_bounds_def by force
        hence 2: "aux_head s' = aux_head s + 1"
          using assm_new mod_less by force
        hence 3: "aux_head s' \<le> tail s'"
          using a d 2 same by fastforce
        (*----------------------------------------------------------*)
        have "used_indices s = [aux_head s ..< tail s]"
          using a used_indices_def by simp
        also have "... = aux_head s # [aux_head s + 1 ..< tail s]"
          using a d upt_eq_Cons_conv by fastforce
        also have "... = aux_head s # [aux_head s' ..< tail s]"
          using 2 by fastforce
        also have "... = aux_head s # [aux_head s' ..< tail s']"
          using assm_new rel_2_same by fastforce
        also have "... = aux_head s # used_indices s'"
          using 3 used_indices_def by fastforce
        (*----------------------------------------------------------*)
        ultimately have ?thesis 
          by simp }
      moreover
      { assume a: "aux_head s > tail s \<and> aux_head s = ArraySize - 1"
        have "aux_head s' = (aux_head s + 1) mod ArraySize"
          using assm_new by simp
        also have "... = 0"
          using a Suc_eq_plus1 diff_Suc_1 by presburger
        also have "... \<le> tail s'"
          by simp
        ultimately have b: "used_indices s' = [0 ..< tail s']"
          using used_indices_def by presburger
        (*----------------------------------------------------------*)
        from a have "used_indices s = aux_head s # [0 ..< tail s]"
          using used_indices_def by fastforce
        also have "... = aux_head s # used_indices s'"
          using same b by simp
        ultimately have ?thesis by simp }
      moreover
      { assume a: "tail s < aux_head s \<and> aux_head s \<noteq> ArraySize - 1"
        hence b: "aux_head s < ArraySize - 1"
          using assm_old invar_bounds_def by force
        hence "aux_head s + 1 = (aux_head s + 1) mod ArraySize"
          by simp
        also have "... = aux_head s'"
          using assm_new by simp
        (*----------------------------------------------------------*)
        ultimately have c: "tail s' < aux_head s' \<and> aux_head s + 1 = aux_head s'"
          using a same by simp
        hence d: "used_indices s' = [aux_head s' ..< ArraySize] @ [0 ..< tail s']"
          using used_indices_def by simp
        (*----------------------------------------------------------*)
        from a have "used_indices s = [aux_head s ..< ArraySize] @ [0 ..< tail s]"
          using used_indices_def by simp
        also have "... = aux_head s # [aux_head s' ..< ArraySize] @ [0 ..< tail s]"
          using a b c upt_rec by force
        also have "... = aux_head s # used_indices s'"
          using same d by simp
        (*----------------------------------------------------------*)
        ultimately have ?thesis by simp }
      ultimately show ?thesis by force
    qed
    (*--------------------------------------------------------------*)
    hence "map (myindex s) (aux_queue s') = used_indices s'"
      by (simp add: t m map_tl)
    thus ?case using same by (simp add: invar_queue_def)
  qed
qed

lemma rel_2_est_guar:
  assumes assm_old : "s \<in> cblock_invar i"
      and assm_pre : "at_head i (aux_queue s) \<and> aux_mid_release s = Some i"
      and assm_new : "s' = rel_line2 i s"
    shows "(s, s') \<in> for_others cblock_contract i
                   \<inter> pred_to_rel (cblock_invar i)"
proof-
  { fix j assume u: "j \<noteq> i"
    hence "(s, s') \<in> contract_raw j"
    proof-
      have "myindex s j = myindex s' j"
        using assms rel_2_same by presburger
      moreover
      { assume "j \<in> set (aux_queue s) \<and> flag_mapping s (myindex s j) = Granted"
        hence "flag_mapping s' (myindex s j) = Granted"
          using assms by simp
        hence "flag_mapping s' (myindex s' j) = Granted"
          using assms rel_2_same by (metis (no_types, lifting)) }
      ultimately show ?thesis by simp
    qed
    moreover have "(s, s') \<in> contract_aux j"
    proof-
      have s: "tl (aux_queue s) = aux_queue s' \<and>
               hd (aux_queue s) = i \<and>
               i \<noteq> j"
        using assm_new assm_pre u by simp
      hence "j \<in> set (aux_queue s) \<longleftrightarrow> j \<in> set (aux_queue s')"
        by (metis RG_Tran.nth_tl hd_conv_nth list.sel(2) list.set_sel(2) set_ConsD)
      thus ?thesis using s by simp
    qed
    ultimately have "(s, s') \<in> cblock_contract j"
      by simp }
  moreover have "(s, s') \<in> pred_to_rel (cblock_invar i)"
    using assms rel_2_invar by force
  ultimately show ?thesis by simp
qed

theorem cblock_rel2:
 "rely: cblock_contract i    guar: for_others cblock_contract i
  inv:  cblock_invar i  anno_code:
    { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = Some i \<rbrace> }
  BasicAnno (rel_line2 i)
    { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> }"
proof method_anno_ultimate
  case est_guar
  thus ?case 
    using rel_2_est_guar by fastforce
next
  case est_post
  thus ?case
    using rel_2_invar apply clarsimp
    by (metis (mono_tags, lifting) distinct.simps(2) distinct_map distinct_used_indices 
                                   invar_queue_def list.collapse mem_Collect_eq)
qed (fastforce+)

(*==================================================================*)
subsection \<open>RG Theorems\<close>

theorem cblock_acq:
 "rely: cblock_contract i    guar: for_others cblock_contract i
  inv:  cblock_invar i  anno_code:
    { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> }
  BasicAnno (acq_line1 i) .;
    { \<lbrace> i \<in> set \<acute>aux_queue \<rbrace> }
  NoAnno (WHILE \<acute>flag_mapping (\<acute>myindex i) = Pending DO SKIP OD)
    { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = None \<rbrace> }"
  apply method_anno_ultimate
  using cblock_acq1 cblock_acq2 by fastforce+

theorem cblock_rel:
 "rely: cblock_contract i    guar: for_others cblock_contract i
  inv:  cblock_invar i  anno_code:
    { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = None \<rbrace> }
  BasicAnno (rel_line1 i) .;
    { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = Some i \<rbrace> }
  BasicAnno (rel_line2 i)
    { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> }"
  apply method_anno_ultimate
  using cblock_rel1 cblock_rel2 annquin_simp by blast+

theorem cblock_local:
 "rely: cblock_contract i    guar: for_others cblock_contract i
  inv:  cblock_invar i  anno_code:
    { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> }
  BasicAnno (acq_line1 i) .;
    { \<lbrace> i \<in> set \<acute>aux_queue \<rbrace> }
  NoAnno (WHILE \<acute>flag_mapping (\<acute>myindex i) = Pending DO SKIP OD) .;
    { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = None \<rbrace> }
  BasicAnno (rel_line1 i) .;
    { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = Some i \<rbrace> }
  BasicAnno (rel_line2 i)
    { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> }"
  apply (method_anno_ultimate)  
     using cblock_acq1 annquin_simp apply blast
    using cblock_acq2 annquin_simp apply force
   using cblock_rel1 annquin_simp apply blast
  using cblock_rel2 annquin_simp by blast

text \<open>When Sledgehammer is applied directly to one of the subgoals of the
next theorem @{text cblock_local_loop}, several solvers do find proofs but
do not report back. However, when that subgoal is explicitly copied into a
separate lemma below, sledgehammer does find an SMT proof.\<close>

lemma lma_tmp:
  assumes
  "rely: cblock_contract t \<inter> pred_to_rel (cblock_invar t)
   guar: invar_and_guar (cblock_invar t) (for_others cblock_contract t)
   anno_code:
     {\<lbrace>t \<notin> set \<acute>aux_queue\<rbrace> \<inter> cblock_invar t}
   add_invar (cblock_invar t) (BasicAnno (acq_line1 t) .;
     {\<lbrace>t \<in> set \<acute>aux_queue\<rbrace>}
   NoAnno (WHILE \<acute>flag_mapping (\<acute>myindex t) = Pending DO SKIP  OD) .;
     {\<lbrace>at_head t \<acute>aux_queue \<and> \<acute>aux_mid_release = None\<rbrace>}
   BasicAnno (rel_line1 t) .;
     {\<lbrace>at_head t \<acute>aux_queue \<and> \<acute>aux_mid_release = Some t\<rbrace>}
   BasicAnno (rel_line2 t))
     {\<lbrace>t \<notin> set \<acute>aux_queue\<rbrace> \<inter> cblock_invar t}"
  shows
  "anncom_spec_valid
    (\<lbrace>t \<notin> set \<acute>aux_queue\<rbrace> \<inter> cblock_invar t \<inter> \<lbrace>t \<notin> set \<acute>aux_queue\<rbrace>)
    (cblock_contract t \<inter> pred_to_rel (cblock_invar t))
    (invar_and_guar (cblock_invar t) (for_others cblock_contract t))
    (\<lbrace>t \<notin> set \<acute>aux_queue\<rbrace> \<inter> cblock_invar t)
    (add_invar (cblock_invar t)
     (BasicAnno (acq_line1 t) .;
      {\<lbrace>t \<in> set \<acute>aux_queue\<rbrace>}
      NoAnno (WHILE \<acute>flag_mapping (\<acute>myindex t) = Pending DO SKIP  OD) .;
      {\<lbrace>at_head t \<acute>aux_queue \<and> \<acute>aux_mid_release = None\<rbrace>}
      BasicAnno (rel_line1 t) .;
      {\<lbrace>at_head t \<acute>aux_queue \<and> \<acute>aux_mid_release = Some t\<rbrace>}
      BasicAnno (rel_line2 t)))"
  using assms annquin_simp
  by (smt (verit) Int_absorb inf_assoc inf_commute)

theorem cblock_local_loop:
 "rely: cblock_contract i    guar: for_others cblock_contract i
  inv:  cblock_invar i  anno_code:
    { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> }
  WhileAnno UNIV
      ( \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> )
  ( BasicAnno (acq_line1 i) .;
      { \<lbrace> i \<in> set \<acute>aux_queue \<rbrace> }
    NoAnno (WHILE \<acute>flag_mapping (\<acute>myindex i) = Pending DO SKIP OD) .;
      { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = None \<rbrace> }
    BasicAnno (rel_line1 i) .;
      { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = Some i \<rbrace> }
    BasicAnno (rel_line2 i) )
  { {} }"
proof method_anno_ultimate
  case body
  thus ?case
    by (rule lma_tmp, rule cblock_local)
qed (fastforce+)

text \<open>The overall theorem expressing the correctness of the Circular
Buffer Lock.\<close>

theorem cblock_global:
  "annotated global_init: cblock_init global_rely: Id
    \<parallel> i < NumThreads @

  { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace>, cblock_contract i }
  WhileAnno UNIV
      ( \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> )
  ( BasicAnno (acq_line1 i) .;
      { \<lbrace> i \<in> set \<acute>aux_queue \<rbrace> }
    NoAnno (WHILE \<acute>flag_mapping (\<acute>myindex i) = Pending DO SKIP OD) .;
      { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = None \<rbrace> }
    BasicAnno (rel_line1 i) .;
      { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = Some i \<rbrace> }
    BasicAnno (rel_line2 i) )

  \<sslash> cblock_invar i { for_others cblock_contract i, {} }
  global_guar: UNIV global_post: {}"
  apply (method_anno_ultimate)
       apply (fastforce intro!: cblock_local_loop)
      using cblock_init_def cblock_init_invar apply force
     using cblock_contracts cblock_invariants apply fastforce
  by (fastforce simp: assm_locale)+
end text \<open>End of locale\<close>

end text \<open>End of theory\<close>

