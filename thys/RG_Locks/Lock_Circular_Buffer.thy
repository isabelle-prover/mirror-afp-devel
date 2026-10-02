
(*
Title:         Rely-Guarantee Verification of the Circular Buffer Lock
Author(s):     Robert Colvin, Scott Heiner, Peter Hoefner, Roger Su
Year:          2026
License:       BSD 2-Clause
Maintainer(s): Robert Colvin <r.colvin@uq.edu.au>
               Peter Hoefner <peter@hoefner-online.de>
               Roger Su <roger.c.su@proton.me>
*)

section \<open>Circular Buffer Lock\<close>

text \<open>The specification and proof of the Circular Buffer Lock,
using the new specification of the queue.\<close>

theory Lock_Circular_Buffer

imports
  Concurrent_Queue_Contract
  RG_Annotated_Methods

begin

type_synonym thread_id = nat

type_synonym index = nat

datatype flag_status = Pending | Granted

consts NumThreads :: nat

abbreviation ArraySize :: "nat" where
  "ArraySize \<equiv> NumThreads + 1"

(*==================================================================*)

record cblock_state =
  myindex :: "thread_id \<Rightarrow> index"
  flag_mapping :: "index \<Rightarrow> flag_status"
  tail :: index
  aux_head :: index
  aux_queue :: "thread_id list"
  aux_mid_release :: "thread_id option"

(*------------------------------------------------------------------*)

definition cblock_init :: "cblock_state set" where
  "cblock_init \<equiv> \<lbrace>
    \<acute>flag_mapping = (\<lambda> _. Pending)(0 := Granted) \<and>
    \<acute>tail = 0 \<and>
    \<acute>aux_queue = [] \<and>
    \<acute>aux_head = 0 \<and>
    \<acute>aux_mid_release = None
  \<rbrace>"

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

text \<open>For the rest of this theory, we assume that the constant
@{text NumThreads} is positive.\<close>

locale numthreads_positive =
  assumes assm_locale: "0 < NumThreads"
begin

(*==================================================================*)
subsection \<open>Invariant\<close>

definition invar_flag :: "cblock_state set" where
  "invar_flag \<equiv> \<lbrace> (\<forall> j \<noteq> \<acute>aux_head. \<acute>flag_mapping j = Pending)
    \<and> (\<acute>flag_mapping \<acute>aux_head = Pending \<longleftrightarrow> \<acute>aux_mid_release \<noteq> None) \<rbrace>"

definition invar_bounds :: "cblock_state set" where
  "invar_bounds \<equiv> \<lbrace> \<acute>tail < ArraySize
              \<and> \<acute>aux_head < ArraySize \<rbrace>"

definition invar_queue :: "cblock_state set" where
  "invar_queue \<equiv> \<lbrace> (\<forall> j. j \<in> set \<acute>aux_queue \<longrightarrow> j < NumThreads)
                 \<and> (map \<acute>myindex \<acute>aux_queue = \<acute>used_indices) \<rbrace>"

abbreviation cblock_invar :: "thread_id \<Rightarrow> cblock_state set" where
  "cblock_invar i \<equiv>
    invar_flag \<inter> invar_bounds \<inter> invar_queue \<inter> \<lbrace> i < NumThreads \<rbrace>"

lemmas cblock_invariants =
  invar_flag_def invar_bounds_def invar_queue_def 

(*------------------------------------------------------------------*)
subsubsection \<open>Invariant Methods\<close>

text \<open>We set up methods that generate structured proofs with named
subgoals, to help us prove the clauses of the invariant.\<close>

theorem thm_method_invar_flag:
  assumes "\<forall> j \<noteq> aux_head s. flag_mapping s j = Pending"
      and "flag_mapping s (aux_head s) = Pending
           \<longleftrightarrow> aux_mid_release s \<noteq> None"
    shows "s \<in> invar_flag"
  using assms invar_flag_def by force

method method_invar_flag =
  cases rule:thm_method_invar_flag,
  goal_cases non_head_pending head_maybe_granted

theorem thm_method_invar_queue:
  assumes "\<forall> j. j \<in> set (aux_queue s) \<longrightarrow> j < NumThreads"
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
  using assms by simp

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
  then show ?case
    apply method_invar_flag
    using assm_init cblock_init_def by force+
next
  case bound
  then show ?case
    using assm_init assm_bound assm_locale cblock_init_def invar_bounds_def by force
next
  case queue
  then show ?case
    apply method_invar_queue
    using assm_init cblock_init_def used_indices_def by force+
qed

text \<open>In a state that satisfies the flag-invariant, a thread is the head
of the queue if its flag is Granted. (If the flag of a thread is Pending,
the thread may still be at the head of the queue. In this case, the thread
must be between the two instructions in the \emph{release} function.)\<close>

lemma only_head_is_granted:
  assumes "s \<in> invar_flag"
      and "flag_mapping s i = Granted"
    shows "i = aux_head s"
  using assms invar_flag_def by force

text \<open>Let @{text s} be a state that satisfies the bounds-invariant,
with $n$ queuing threads. If we start from the @{text aux_head} index,
and ``advance'' $n$ steps (with potential wrap-around), then we reach
the global @{text tail} index.\<close>

lemma head_tail_mod:
  assumes "s \<in> invar_bounds"
  shows "tail s = (aux_head s + length (used_indices s)) mod (ArraySize)"
proof (cases "aux_head s \<le> tail s")
  case True thus ?thesis
    using assms by (simp add: used_indices_def invar_bounds_def)
next
  case False
  then show ?thesis
    using assms used_indices_def invar_bounds_def
    by (metis (no_types, lifting) CollectD add.assoc le_eq_less_or_eq length_used_indices mod_add_self1 mod_less ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
qed

text \<open>If a state satisfies the queue-invariant (namely the clause with
the @{text map} function, then the @{text myindex} function is injective
on the set of queuing threads. In other words, every queuing thread has
a unique index in a state that satisfies the queue-invariant.\<close>

lemma invar_map_inj_on:
  assumes "s \<in> invar_queue"
  shows "inj_on (myindex s) (set (aux_queue s))"
  using assms distinct_used_indices invar_queue_def distinct_map
  by force

text \<open>In a state that satisfies the queue-invariant, the length of the
queue is equal to the length of the list of used indices.\<close>

lemma length_used_indices_queue:
  assumes "s \<in> invar_queue"
  shows "length (used_indices s) = length (aux_queue s)"
  by (metis (mono_tags, lifting) assms invar_queue_def length_map CollectD)

text \<open>In a state that fully satisfies the invariant, if there is a
thread that is not in the queue, then the length of the queue must
be smaller than the total number of threads.\<close>

lemma queue_bounded:
  assumes "s \<in> cblock_invar i"
      and "i \<notin> set (aux_queue s)"
    shows "length (aux_queue s) < NumThreads"
proof-
  have "length (used_indices s) \<le> NumThreads"
    using assms(1) invar_bounds_def length_used_indices
    by (smt (verit, del_insts) CollectD IntE add.commute diff_add_inverse le_add_diff_inverse2 le_diff_conv less_Suc_eq_le not_less_eq_eq plus_1_eq_Suc trans_le_add2)
  hence "card (set (aux_queue s)) \<le> NumThreads"
    by (metis IntD1 assms(1) card_length inf_commute le_trans length_used_indices_queue)
  moreover
  have "card (set (aux_queue s)) = 0 \<longleftrightarrow> aux_queue s = []"
    by simp
  moreover
  have "finite (set (aux_queue s))"
    using calculation by simp
  moreover
  have "card (set (aux_queue s)) = NumThreads
       \<longleftrightarrow> (\<forall> j < NumThreads. j \<in> set (aux_queue s))"
  proof-
    { assume "card (set (aux_queue s)) = NumThreads"
      then have "set (aux_queue s) = {j. j < NumThreads}"
        using assms by (simp add: invar_queue_def card_subset_eq subsetI)
      then have "\<forall> i < NumThreads. i \<in> set (aux_queue s)"
        by blast }
    moreover
    { assume "\<forall> i < NumThreads. i \<in> set (aux_queue s)"
      then have "card (set (aux_queue s)) = NumThreads"
        using assms by blast }
    ultimately show ?thesis by blast
  qed
  ultimately
  have "card (set (aux_queue s)) < NumThreads"
    using assms nat_less_le by blast  
  thus ?thesis using assms
    by (metis (mono_tags, lifting) IntE distinct_card distinct_map distinct_used_indices invar_queue_def mem_Collect_eq)
qed

text \<open>If a state that satisfies the bound- and queue-invariants, and
if the queue is non-empty, then the index held by the head of the
queue must be the same as @{text aux_head}.\<close>

lemma head_and_head_index:
  assumes "s \<in> invar_bounds \<inter> invar_queue"
      and "aux_queue s \<noteq> []"
    shows "myindex s (hd (aux_queue s)) = aux_head s"
proof-
  have ln0: "map (myindex s) (aux_queue s) = used_indices s"
    using assms(1) invar_queue_def by force
  hence "myindex s (hd (aux_queue s)) = hd (used_indices s)"
    using assms(2) hd_map by metis
  also have "... = aux_head s"
    apply (cases "aux_head s \<le> tail s")
    using assms(2) ln0 upt_rec used_indices_def
     apply fastforce
    using assms(1) invar_bounds_def upt_rec used_indices_def
    by fastforce
  ultimately show ?thesis by simp
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
    using assms(1) assms(3) assms(4) by (simp add: head_and_head_index)
  then show ?thesis
    using assms(1) assms(2) invar_flag_def flag_status.exhaust
    by (smt (verit, best) CollectD IntD1)
qed

text \<open>In a state that satisfies the queue-invariant, the global index
@{text tail} is never held by a thread. Indeed, @{text tail} is meant
to be ``free'' for the next thread that joins the queue. Note that
when a thread is not in the queue, its index becomes outdated,
and @{text tail} may cycle back and coincide with that index.\<close>

lemma tail_never_used:
  assumes "s \<in> invar_queue"
  shows "\<forall> j \<in> set (aux_queue s). myindex s j \<noteq> tail s"
proof-
  have "tail s \<notin> set (used_indices s)"
    using used_indices_def by simp
  hence "tail s \<notin> set (map (myindex s) (aux_queue s))"
    using assms(1) invar_queue_def
    by (smt (verit) CollectD)
    (* by (metis (mono_tags, lifting) CollectD) *)
    (* This commented-out metis proof, which was not found by Sledgehammer,
       also works here but takes several seconds. *)
  thus ?thesis by (metis imageI image_set)
qed

text \<open>In a state that satisfies the full invariant, if the @{text tail}
index is right before the @{text aux_head} index, then it must be the
case that every thread is in the queue.\<close>

lemma used_indices_full:
  assumes "s \<in> cblock_invar i"
      and "(tail s + 1) mod ArraySize = aux_head s"
    shows "length (used_indices s) = NumThreads"
  using assms apply (simp add: used_indices_def) (* Next line: takes a little while *)
  by (smt (z3) CollectD Nat.le_imp_diff_is_add One_nat_def Suc_eq_plus1 Suc_n_not_le_n Zero_not_Suc add_0 add_Suc add_Suc_right add_cancel_left_left add_right_cancel cblock_state.select_convs(5) cancel_comm_monoid_add_class.diff_cancel canonically_ordered_monoid_add_class.lessE diff_Suc_Suc diff_add_inverse2 diff_zero invar_bounds_def le_Suc_eq less_Suc_eq_le mod_Suc mod_Suc_le_divisor mod_less mod_less_eq_dividend mod_self)

text \<open>Conversely, if not every thread is in the queue, then the
@{text tail} index is not right before the @{text aux_head} index.\<close>

lemma space_available:
  assumes assm_invar: "s \<in> cblock_invar i"
      and assm_q: "i \<notin> set (aux_queue s)"
    shows "(tail s + 1) mod ArraySize \<noteq> aux_head s"
proof 
  assume assm_neg: "(tail s + 1) mod ArraySize = aux_head s"
  thus "False"
  proof-
    have "length (used_indices s) = NumThreads"
      using assm_neg assm_invar used_indices_full by simp
    hence "length (aux_queue s) = NumThreads"
      by (metis (mono_tags, lifting) Int_Collect assm_invar invar_queue_def length_map)
    hence "\<forall> j < NumThreads. j \<in> set (aux_queue s)"
      using assm_invar queue_bounded by fastforce
    thus ?thesis using assm_invar assm_q by blast
  qed
qed

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
  case True
  then have ln1: "tail s' = (tail s + 1)"
    using assms(1) assms(2) assms(4) assms(5)
    by (metis IntD1 One_nat_def Suc_lessI add.right_neutral add_Suc_right add_gr_0 add_less_same_cancel1 head_tail_mod inf_commute less_numeral_extra(1) mod_less mod_less_divisor mod_self not_add_less1 order_le_imp_less_or_eq) 
  have "used_indices s' = [aux_head s' ..< tail s']"
    using True used_indices_def by simp
  also have "... = [aux_head s ..< (tail s + 1)]"
    using ln1 assms(2) by simp
  also have ln2: "... = [aux_head s ..< tail s] @ [tail s]"
    using True assms(2) assms(4) assms(5) ln1 by fastforce
  also have "... = used_indices s @ [tail s]"
    using True ln2 neq_Nil_conv used_indices_def by fastforce
  ultimately show ?thesis by simp
next
  case False (* tail s' < aux_head s' *)
  then have ln1: "used_indices s' = [aux_head s ..< ArraySize] @ [0 ..< tail s']"
    using used_indices_def assms(2) assms(3) by simp
  { assume a: "tail s' = 0"
    then have "tail s + 1 = ArraySize"
      using assms(1) assms(5)
      by (metis (no_types, lifting) IntD1 add.commute head_tail_mod inf_commute mod_Suc mod_mod_trivial plus_1_eq_Suc zero_eq_add_iff_both_eq_0 zero_neq_one)
    then have ?thesis
      using a ln1 assms(3) assms(5) nat_neq_iff used_indices_def by fastforce }
  moreover
  { assume a: "tail s' \<noteq> 0"
    then have 1: "0 < tail s'"
      by linarith
    then have 2: "tail s < tail s'"
      using a assms(1) assms(5)
      by (metis IntE Suc_eq_plus1 add_gr_0 head_tail_mod linorder_neqE_nat mod_less mod_less_divisor mod_self not_less_eq)
    then have 3: "tail s < aux_head s"
      using assms(2) False by linarith
    have "used_indices s' = [aux_head s ..< ArraySize] @ [0 ..< tail s']"
      using ln1 by simp
    also have "... = [aux_head s ..< ArraySize] @ [0 ..< tail s] @ [tail s]"
      using 1 2 assms(5)
      by (metis Suc_eq_plus1 bot_nat_0.extremum dual_order.eq_iff less_eq_Suc_le mod_less_eq_dividend upt_Suc_append)
    also have "... = used_indices s @ [tail s]"
      using 3 used_indices_def by fastforce
    ultimately have ?thesis
      by simp }
  ultimately show ?thesis by blast
qed

(*==================================================================*)
subsection \<open>Rely\<close>

definition cblock_rely_raw :: "thread_id \<Rightarrow> cblock_state rel" where
  "cblock_rely_raw i \<equiv> \<lbrace> (i \<in> set \<ordmasculine>aux_queue
    \<longrightarrow> \<ordmasculine>flag_mapping (\<ordmasculine>myindex i) = Granted
    \<longrightarrow> \<ordfeminine>flag_mapping (\<ordfeminine>myindex i) = Granted)
    \<and> (\<ordmasculine>myindex i = \<ordfeminine>myindex i) \<rbrace>"

definition cblock_rely_aux :: "thread_id \<Rightarrow> cblock_state rel" where
  "cblock_rely_aux i \<equiv> \<lbrace> queue_contract i \<ordmasculine>aux_queue \<ordfeminine>aux_queue
    \<and> (at_head i \<ordmasculine>aux_queue \<longrightarrow>
    at_head i \<ordfeminine>aux_queue \<and> \<ordmasculine>aux_mid_release = \<ordfeminine>aux_mid_release) \<rbrace>"

abbreviation cblock_rely :: "thread_id \<Rightarrow> cblock_state rel" where
  "cblock_rely i \<equiv> cblock_rely_raw i \<inter> cblock_rely_aux i"

lemmas cblock_relies [simp] = cblock_rely_raw_def cblock_rely_aux_def

(*==================================================================*)
subsection \<open>RG Lemmas\<close>

abbreviation acq_line1
  :: "thread_id \<Rightarrow> cblock_state \<Rightarrow> cblock_state" where
  "acq_line1 i \<equiv>
    (\<acute>myindex[i] \<leftarrow> \<acute>tail) \<circ>>
    (\<acute>tail \<leftarrow> (\<acute>tail + 1) mod ArraySize) \<circ>>
    (\<acute>aux_queue \<leftarrow> \<acute>aux_queue @ [i])"

lemma acq_1_invar:
  assumes assm_old: "s \<in> cblock_invar i"
  and assm_new: "s' = acq_line1 i s"
  and assm_pre: "i \<notin> set (aux_queue s)"
  shows "s' \<in> cblock_invar i"
proof-
  have ln_same: "flag_mapping s = flag_mapping s' \<and>
                   aux_head s = aux_head s' \<and>
            aux_mid_release s = aux_mid_release s' \<and>
      (\<forall> j \<noteq> i. myindex s j = myindex s' j)"
  using assm_new by simp
  show ?thesis
  proof method_cblock_invar
    case flag
    have "(\<forall> j \<noteq> aux_head s. flag_mapping s j = Pending) \<and>
          (flag_mapping s (aux_head s) = Pending \<longleftrightarrow> aux_mid_release s \<noteq> None)"
      using assm_old invar_flag_def by force
    hence "(\<forall> j \<noteq> aux_head s'. flag_mapping s' j = Pending) \<and>
           (flag_mapping s' (aux_head s') = Pending \<longleftrightarrow> aux_mid_release s' \<noteq> None)"
      using ln_same by simp
    thus ?case using invar_flag_def by force
  next (*----------------------------------------*)
    case bound
    have "aux_head s' < ArraySize"
      using assm_old ln_same by (simp add: invar_bounds_def)
    moreover have "tail s' < ArraySize"
      using assm_new by simp
    ultimately show ?case using invar_bounds_def assm_old ln_same by force
  next (*----------------------------------------*)
    case queue show ?case
      proof method_invar_queue
        case bound_thread_id
        have "\<forall> j. j \<in> set (aux_queue s) \<longrightarrow> j < NumThreads"
          using assm_old invar_queue_def ln_same by force
        moreover have "set (aux_queue s') = set (aux_queue s) \<union> {i}"
          using assm_new by simp
        moreover have "i < NumThreads"
          using assm_old ln_same by blast
        ultimately show ?case by force
      next
        case map_used_indices
        have "map (myindex s') (aux_queue s') = map (myindex s) (aux_queue s) @ [myindex s' i]"
          using assm_new assm_pre by simp
        also have ln1: "... = used_indices s @ [myindex s' i]"
          using used_indices_def assm_old invar_queue_def by blast
        also have "... = used_indices s @ [tail s]"
          using assm_new by simp
        also have "... = used_indices s'"
          proof-
            have "length (used_indices s) < NumThreads"
              by (metis append1_eq_conv assm_old assm_pre length_map ln1 queue_bounded)
            moreover
            have "(tail s + 1) mod ArraySize \<noteq> aux_head s"
              using assm_old assm_pre space_available by blast
            moreover
            have "tail s' = (tail s + 1) mod (ArraySize)"
              using assm_new by simp
            ultimately show ?thesis
              by (metis assm_old ln_same used_indices_append)
            qed
        ultimately show ?case by simp
    qed
  qed
qed

theorem cblock_acq1:
 "rely: cblock_rely  i  guar: for_others cblock_rely i
   inv: cblock_invar i  code:
  { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> }
  Basic (acq_line1 i)
  { \<lbrace> i \<in> set \<acute>aux_queue \<rbrace> }"
proof method_basic_inv
  case est_inv
  then show ?case using acq_1_invar by blast
next
  case est_guar
  then show ?case using at_head_append by fastforce
qed (fastforce+)

theorem cblock_acq2:
 "rely: cblock_rely  i  guar: for_others cblock_rely i
   inv: cblock_invar i  code:
  { \<lbrace> i \<in> set \<acute>aux_queue \<rbrace> }
  WHILE \<acute>flag_mapping (\<acute>myindex i) = Pending DO SKIP OD
  { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = None \<rbrace> }"
proof method_spinloop
  case est_post
  then show ?case
  proof-
    { fix s assume assm_s: "s \<in> cblock_invar i \<inter> \<lbrace> i \<in> set \<acute>aux_queue \<rbrace> \<inter>
                            \<lbrace> \<acute>flag_mapping (\<acute>myindex i) \<noteq> Pending \<rbrace>"
      then have ln1:"aux_queue s \<noteq> []"
        by force
      have ln2:"flag_mapping s (aux_head s) \<noteq> Pending"
        using assm_s invar_flag_def by force
      then have ln3:"myindex s i = aux_head s"
        using assm_s invar_flag_def
        by (metis (mono_tags, lifting) IntE mem_Collect_eq)
      have "i = hd (aux_queue s) \<and> s \<in> \<lbrace> \<acute>aux_mid_release = None \<rbrace>" (is "?A \<and> ?B")
      proof-
        have "?A"
          using ln1 assm_s invar_queue_def head_and_head_index invar_map_inj_on
          by (metis (no_types, lifting) IntD1 Int_Collect inf_commute inj_onD list.set_sel(1) ln3)
          moreover
          have "s \<in> \<lbrace> \<acute>flag_mapping (\<acute>myindex i) = Granted \<rbrace>"
            using ln2 ln3 flag_status.exhaust by auto
          then have "?B"
            using assm_s invar_flag_def ln2 by fastforce
        ultimately show ?thesis by simp
      qed }
    then show ?thesis by blast
  qed
qed (fastforce+)

(*------------------------------------------------------------------*)
abbreviation rel_line1
  :: "thread_id \<Rightarrow> cblock_state \<Rightarrow> cblock_state" where
  "rel_line1 i \<equiv>
    (\<acute>flag_mapping[\<acute>myindex i] \<leftarrow> Pending) \<circ>>
    (\<acute>aux_mid_release \<leftarrow> Some i)"

lemma rel_1_same:
  assumes "s' = rel_line1 i s"
  shows "(myindex s = myindex s') \<and>
         (\<forall> j \<noteq> myindex s i. flag_mapping s j = flag_mapping s' j) \<and>
         (tail s = tail s') \<and>
         (aux_head s = aux_head s') \<and>
         (aux_queue s = aux_queue s')"
  using assms by simp

lemma rel_1_invar:
  assumes assm_old: "s \<in> cblock_invar i"
      and assm_new: "s' = rel_line1 i s"
      and assm_pre: "at_head i (aux_queue s) \<and> aux_mid_release s = None"
    shows "s' \<in> cblock_invar i"
proof-
  have ln_head: "myindex s i = aux_head s"
    using assm_pre assm_old invar_queue_def head_and_head_index by force
  show ?thesis
  proof method_cblock_invar
    case flag show ?case
    proof method_invar_flag
      case non_head_pending
      have "\<forall> j \<noteq> aux_head s. flag_mapping s j = Pending"
        using assm_old invar_flag_def by force
      then show ?case
        using rel_1_same ln_head assm_new by (metis (no_types, lifting))
    next
      case head_maybe_granted
      then show ?case
        using assm_new ln_head by simp
    qed
  next (*---------------------------------------*)
    case bound
    have "tail s' = tail s \<and> aux_head s' = aux_head s"
      using assm_new rel_1_same by presburger
    then show ?case
      by (smt (z3) Int_iff assm_old invar_bounds_def mem_Collect_eq)
  next (*---------------------------------------*)
    case queue
    show ?case
    proof method_invar_queue
      case bound_thread_id
      then show ?case
        using assm_old assm_new invar_queue_def
        by fastforce
    next
      case map_used_indices
      have "used_indices s = used_indices s'"
        using assm_new rel_1_same used_indices_def by presburger
      moreover have "myindex s = myindex s' \<and> aux_queue s = aux_queue s'"
        using assm_new rel_1_same by blast
      ultimately show ?case
        using assm_old invar_queue_def
        by (metis (mono_tags, lifting) Int_iff mem_Collect_eq)
    qed
  qed
qed

lemma rel_1_est_guar:
  assumes "s \<in> \<lbrace> \<acute>aux_queue \<noteq> [] \<and>
                  hd \<acute>aux_queue = i \<and>
                 \<acute>aux_mid_release = None \<rbrace>
               \<inter> cblock_invar i"
      and "s' = rel_line1 i s"
    shows "(s, s') \<in> for_others cblock_rely i"
      and "s \<in> cblock_invar i \<longrightarrow> s' \<in> cblock_invar i"
proof-
  { fix j assume assm_u_t: "j \<noteq> i"
    { assume assm_u_q: "j \<in> set (aux_queue s)"
      then have "j < NumThreads"
        using assms(1) invar_queue_def by force
      from assm_u_q have "myindex s j \<noteq> myindex s i"
        using assms(1) invar_map_inj_on
        by (metis (mono_tags, lifting) Int_iff assm_u_t inj_onD list.set_sel(1) mem_Collect_eq)
      then have "flag_mapping s (myindex s j) \<noteq> Granted"
        using assms(1) only_head_is_granted head_is_granted
        using head_and_head_index by force }
    then have "j \<in> set (aux_queue s)
               \<longrightarrow> flag_mapping s  (myindex s  j) = Granted
               \<longrightarrow> flag_mapping s' (myindex s' j) = Granted"
      by simp
    moreover have "myindex s j = myindex s' j"
      using rel_1_same assms(2) by simp
    ultimately have "(s, s') \<in> cblock_rely_raw j"
      by simp }
  moreover
  { fix j assume "j \<noteq> i"
    then have "hd (aux_queue s) \<noteq> j"
      using assms(1) by simp
    moreover have "queue_contract j (aux_queue s) (aux_queue s')"
      using assms(2) by simp
    ultimately have "(s, s') \<in> cblock_rely_aux j"
      by force }
  ultimately show "(s, s') \<in> for_others cblock_rely i" by blast
next
  show "s \<in> cblock_invar i \<longrightarrow> s' \<in> cblock_invar i"
    using assms rel_1_invar by force
qed

theorem cblock_rel1:
 "rely: cblock_rely  i  guar: for_others cblock_rely i
   inv: cblock_invar i  code:
  { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = None \<rbrace> }
  Basic (rel_line1 i)
  { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = Some i \<rbrace> }"
proof method_basic_inv
  case est_inv
  then show ?case using rel_1_invar by blast
next
  case est_guar
  then show ?case by (clarsimp, meson inj_on_contraD invar_map_inj_on)
qed (fastforce+)

(*------------------------------------------------------------------*)
abbreviation rel_line2
  :: "thread_id \<Rightarrow> cblock_state \<Rightarrow> cblock_state" where
  "rel_line2 i \<equiv>
    (\<acute>flag_mapping[((\<acute>myindex i + 1) mod ArraySize)] \<leftarrow> Granted) \<circ>>
    (\<acute>aux_queue \<leftarrow> tl \<acute>aux_queue) \<circ>>
    (\<acute>aux_head \<leftarrow> (\<acute>aux_head + 1) mod ArraySize) \<circ>>
    (\<acute>aux_mid_release \<leftarrow> None)"

lemma rel_2_same:
  assumes "s' = rel_line2 i s"
    shows "myindex s = myindex s'"
      and "tail s = tail s'"
      and "(\<forall> j \<noteq> (myindex s i + 1) mod ArraySize.
           flag_mapping s j = flag_mapping s' j)"
  using assms by simp_all

lemma rel_2_invar:
  assumes assm_old : "s \<in> cblock_invar i"
      and assm_pre : "at_head i (aux_queue s) \<and> aux_mid_release s = Some i"
      and assm_new : "s' = rel_line2 i s"
    shows "s' \<in> cblock_invar i"
proof method_cblock_invar
  case flag
  have "myindex s i = aux_head s"
    using assm_old assm_pre head_and_head_index by fastforce
  then have ln0: "aux_head s' = (myindex s i + 1) mod ArraySize"
    using assms by simp
  show ?case
  proof method_invar_flag
    case non_head_pending show ?case
      using ln0 assm_new assm_old assm_pre invar_flag_def by force
  next
    case head_maybe_granted show ?case using assms(1,2,3) ln0 by force
  qed
next (*-----------------------------------------*)
  case bound
  { have "tail s < ArraySize"
      using assm_old invar_bounds_def by fastforce
    then have "tail s' < ArraySize"
      using rel_2_same assm_new by presburger }
  moreover
  { have "aux_head s' = (myindex s i + 1) mod ArraySize"
      using assms head_and_head_index by fastforce
    then have "aux_head s' < ArraySize"
      by simp }
  moreover have "i < NumThreads"
    using rel_2_same assm_old assm_new by force
  ultimately show ?case
    using invar_bounds_def by blast
next (*-----------------------------------------*)
  case queue show ?case
  proof method_invar_queue
    case bound_thread_id
    have "\<forall> j. j \<in> set (aux_queue s) \<longrightarrow> j < NumThreads"
      using assm_old invar_queue_def by force
    then have "\<forall> j. j \<in> set (aux_queue s) \<longrightarrow> j < NumThreads"
      using assm_new rel_2_same by presburger
    moreover
    have "aux_queue s \<noteq> []"
      using assm_pre by fastforce
    then have "set (aux_queue s') \<subseteq> set (aux_queue s)"
      using assm_new assm_pre by (simp add: list.set_sel(2) subsetI)
    ultimately show ?case by blast
  next
    case map_used_indices
    have same: "tail s = tail s' \<and>
             myindex s = myindex s'"
      using assm_new rel_2_same by force

    have "aux_queue s \<noteq> []"
      using assm_pre by fastforce
    then have d: "aux_head s \<noteq> tail s"
      using assm_old head_and_head_index tail_never_used by force
    have t: "aux_queue s' = tl (aux_queue s)"
      using assm_new by simp
    have m: "map (myindex s) (aux_queue s) = used_indices s"
      using assm_old invar_queue_def by force

    have "used_indices s' = tl (used_indices s)"
    proof-
      { assume a: "aux_head s \<le> tail s"
        then have 1: "aux_head s < tail s"
          using d by simp
        then have 2: "aux_head s + 1 < ArraySize"
          using assm_old invar_bounds_def by force
        then have 3: "aux_head s' = aux_head s + 1"
          using assm_new mod_less by force
        then have 4: "aux_head s' \<le> tail s'"
          using 1 2 same by simp
  
        have "used_indices s = [aux_head s ..< tail s]"
          using a used_indices_def by simp
        also have "... = aux_head s # [aux_head s + 1 ..< tail s]"
          using 1 upt_eq_Cons_conv by blast
        also have "... = aux_head s # [aux_head s' ..< tail s]"
          using 3 by simp
        also have "... = aux_head s # [aux_head s' ..< tail s']"
          using assm_new rel_2_same by force
        also have "... = aux_head s # used_indices s'"
          using 4 used_indices_def by simp
  
        ultimately have ?thesis by simp }
  
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
        
        from a have "used_indices s = aux_head s # [0 ..< tail s]"
          using used_indices_def by fastforce
        also have "... = aux_head s # used_indices s'"
          using same b by simp
  
        ultimately have ?thesis by simp }
  
      moreover
      { assume a: "tail s < aux_head s \<and> aux_head s \<noteq> ArraySize - 1"
        then have b: "aux_head s < ArraySize - 1"
          using assm_old invar_bounds_def by force
        then have "aux_head s + 1 = (aux_head s + 1) mod ArraySize"
          by simp
        also have "... = aux_head s'"
          using assm_new by simp
  
        ultimately have c: "tail s' < aux_head s' \<and> aux_head s + 1 = aux_head s'"
          using a same by simp
        then have d: "used_indices s' = [aux_head s' ..< ArraySize] @ [0 ..< tail s']"
          using used_indices_def by simp
  
        from a have "used_indices s = [aux_head s ..< ArraySize] @ [0 ..< tail s]"
          using used_indices_def by simp
        also have "... = aux_head s # [aux_head s' ..< ArraySize] @ [0 ..< tail s]"
          using a b c upt_rec by force
        also have "... = aux_head s # used_indices s'"
          using same d by simp
  
        ultimately have ?thesis by simp }
      ultimately show ?thesis by force
    qed

    then have "map (myindex s) (aux_queue s') = used_indices s'"
      by (simp add: t m map_tl)
    then show ?case using same by (simp add: invar_queue_def)
  qed
qed

lemma rel_2_est_guar:
  assumes assm_old : "s \<in> cblock_invar i"
      and assm_pre : "at_head i (aux_queue s) \<and> aux_mid_release s = Some i"
      and assm_new : "s' = rel_line2 i s"
    shows "(s, s') \<in> for_others cblock_rely i"
proof-
  { fix j assume u: "j \<noteq> i"
    then have "(s, s') \<in> cblock_rely_raw j"
    proof-
      have "myindex s j = myindex s' j"
        using assms rel_2_same by presburger
      moreover
      { assume "j \<in> set (aux_queue s) \<and> flag_mapping s (myindex s j) = Granted"
        then have "flag_mapping s' (myindex s j) = Granted"
          using assms by simp
        then have "flag_mapping s' (myindex s' j) = Granted"
          using assms rel_2_same by (metis (no_types, lifting)) }
      ultimately show ?thesis by simp
    qed
    moreover have "(s, s') \<in> cblock_rely_aux j"
    proof-
      have s: "tl (aux_queue s) = aux_queue s' \<and>
               hd (aux_queue s) = i \<and>
               i \<noteq> j"
        using assm_new assm_pre u by simp
      then have "queue_contract j (aux_queue s) (aux_queue s')"
        by (metis queue_contract_tl)
      then show ?thesis using s by simp
    qed
    ultimately have "(s, s') \<in> cblock_rely j"
      by blast }
  then show ?thesis by blast
qed

theorem cblock_rel2:
 "rely: cblock_rely  i  guar: for_others cblock_rely i
   inv: cblock_invar i  code:
  { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = Some i \<rbrace> }
  Basic (rel_line2 i)
  { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> }"
proof method_basic_inv
  case est_inv
  then show ?case using rel_2_invar by blast
next
  case est_guar
  then show ?case using rel_2_est_guar by blast
next
  case est_post
  then show ?case
    by (clarsimp, metis (mono_tags, lifting) distinct.simps(2) distinct_map distinct_used_indices empty_iff invar_queue_def list.collapse mem_Collect_eq set_empty2)
qed (fastforce+)

(*==================================================================*)
subsection \<open>RG Theorems\<close>

theorem cblock_acq:
 "annquin_valid
  rely: cblock_rely  i  guar: for_others cblock_rely i
   inv: cblock_invar i  annotated_code:
    { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> }
  BasicAnno (acq_line1 i) .;
    { \<lbrace> i \<in> set \<acute>aux_queue \<rbrace> } 
  (SPIN \<acute>flag_mapping (\<acute>myindex i) = Pending )
    { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = None \<rbrace> }" 
  apply (decompose_and_discharge 
         helpers: Suc_le_eq at_head_append acq_1_invar at_head_append
         intros: 
         simps: cblock_invariants map_tl at_head_append)
    apply (meson at_head_append)
    subgoal for s using acq_1_invar by(auto simp add: cblock_invariants used_indices_def)
   using acq_1_invar apply(auto simp add: cblock_invariants)[1]
  using acq_1_invar apply(auto simp add: cblock_invariants)[1]
    apply metis
   apply metis
  by (smt (verit, ccfv_threshold) Suc_eq_plus1 antisym_conv2 distinct_map distinct_used_indices
      hd_append2 hd_upt inj_onD length_pos_if_in_set linorder_not_le list.map_sel(1) list.set_sel(1)
      list.size(3) not_less_eq tail_never_used thm_method_invar_queue upt_eq_Nil_conv used_indices_def)

(*------------------------------------------------------------------*)
theorem cblock_rel:
 "annquin_valid
  rely: cblock_rely  i  guar: for_others cblock_rely i
   inv: cblock_invar i  annotated_code:
    { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = None \<rbrace> }
  BasicAnno (rel_line1 i) .;
    { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = Some i \<rbrace> }
  BasicAnno (rel_line2 i)
    { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> }"
  apply (decompose_and_discharge
    helpers: suffix_tl tl_prefix_before Suc_le_eq at_head_append acq_1_invar
    intros:
    simps: cblock_invariants map_tl)
          using rel_1_invar rel_2_invar apply auto
       apply (metis inj_onD invar_map_inj_on)
      apply (metis queue_contract_def queue_contract_tl)
     apply (metis list.sel(2) list.set_sel(2))
    apply (metis suffix_tl tl_prefix_before)
   apply (metis prefix_order.dual_order.refl tl_suffix_after)
  by (metis (mono_tags, lifting) at_head_tl distinct_map distinct_used_indices
      invar_queue_def mem_Collect_eq)

(*------------------------------------------------------------------*)
abbreviation "cblock_local i \<equiv>
    { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> }
  BasicAnno (acq_line1 i) .;
    { \<lbrace> i \<in> set \<acute>aux_queue \<rbrace> }
  SPIN \<acute>flag_mapping (\<acute>myindex i) = Pending  .;
    { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = None \<rbrace> }
  BasicAnno (rel_line1 i) .;
    { \<lbrace> at_head i \<acute>aux_queue \<and> \<acute>aux_mid_release = Some i \<rbrace> }
  BasicAnno (rel_line2 i) /
    \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> "

(*------------------------------------------------------------------*)
theorem cblock_local:
 "annquin_valid
  rely: cblock_rely  i  guar: for_others cblock_rely i
   inv: cblock_invar i  annotated_code:
    { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> }
  cblock_local i
    { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> }"
  apply (decompose_and_discharge 
    helpers: suffix_tl tl_prefix_before Suc_le_eq at_head_append acq_1_invar
      at_head_append suffix_tl tl_prefix_before Suc_le_eq at_head_append acq_1_invar
    intros: cblock_rel cblock_acq  
    simps: cblock_invariants map_tl at_head_append)
          using rel_1_invar rel_2_invar acq_1_invar apply auto
       apply (metis inj_onD invar_map_inj_on)
      apply (metis queue_contract_tl stable_in_queue)
     apply (metis list.sel(2) list.set_sel(2))
    apply (metis suffix_tl tl_prefix_before)
   apply (metis prefix_order.dual_order.refl tl_suffix_after)
  by (metis (mono_tags, lifting) at_head_tl distinct_map distinct_used_indices invar_queue_def mem_Collect_eq)

(*------------------------------------------------------------------*)
theorem cblock_local_loop:
 "annquin_valid
  rely: cblock_rely  i  guar: for_others cblock_rely i
   inv: cblock_invar i  annotated_code:
  { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace> }
  Forever (cblock_local i)
  { {} }"
  by (decompose_and_discharge intros: cblock_local)

(*----------------------------------------------------------------------------*)
theorem cblock_global:
  "valid_multipar: annotated
  global_init: cblock_init
  global_rely: Id
    \<parallel> i < NumThreads @
    { \<lbrace> i \<notin> set \<acute>aux_queue \<rbrace>, cblock_rely i }
  FOREVER (cblock_local i)
    \<sslash> cblock_invar i { for_others cblock_rely i, {} }
  global_guar: UNIV
  global_post: {}"
  apply (decompose_and_discharge intros: cblock_local_loop)
      apply (auto simp add: cblock_init_def cblock_invariants)
   using used_indices_def apply fastforce
  by (simp add: assm_locale)

end text \<open>End of locale\<close>

end text \<open>End of theory\<close>

