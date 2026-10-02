
(*
Title:         Rely-Guarantee Verification of the Abstract Queue Lock
Author(s):     Robert Colvin, Scott Heiner, Peter Hoefner, Roger Su
Year:          2026
License:       BSD 2-Clause
Maintainer(s): Robert Colvin <r.colvin@uq.edu.au>
               Peter Hoefner <peter@hoefner-online.de>
               Roger Su <roger.c.su@proton.me>
*)

section \<open>Abstract Queue Lock\<close>

text \<open>The specification and proof of the Abstract Queue Lock, using
the new specification of the queue.\<close>

theory Lock_Abstract_Queue

imports
  Concurrent_Queue_Contract
  RG_Annotated_Methods

begin

type_synonym thread_id = nat

record queue_lock = queue :: "thread_id list"

abbreviation qlock_rely :: "thread_id \<Rightarrow> queue_lock rel" where
  "qlock_rely i \<equiv> \<lbrace> queue_contract i \<ordmasculine>queue \<ordfeminine>queue \<rbrace>"

(*------------------------------------------------------------------*)
subsection \<open>No Annotations, Simpler Invariant\<close>

text \<open>This section's RG theorems are based on the original, non-annotated
command-type, and are proved using the structured proof-style.
They use a simpler invariant that requires only the distinctness of the
queue, for a simpler global postcondition.\<close>

lemma qlock_spin':
 "rely: qlock_rely i         guar: for_others qlock_rely i
   inv: \<lbrace> distinct \<acute>queue \<rbrace>  code:
     { \<lbrace> i \<in> set \<acute>queue \<rbrace> }
   WHILE hd \<acute>queue \<noteq> i DO SKIP OD
     { \<lbrace> at_head i \<acute>queue \<rbrace> }"
proof method_spinloop
  case stable_post show ?case
    apply clarsimp
    by (metis (full_types) emptyE list.set(1) suffix_bot.extremum_uniqueI takeWhile_eq_Nil_iff)
qed (fastforce+)

lemma qlock_rel':
 "rely: qlock_rely i         guar: for_others qlock_rely i
   inv: \<lbrace> distinct \<acute>queue \<rbrace>  code: 
     { \<lbrace> at_head i \<acute>queue \<rbrace> }
   \<acute>queue := tl \<acute>queue
     { \<lbrace> i \<notin> set \<acute>queue \<rbrace> }"
proof method_basic_inv
  case stab_pre show ?case using stable_at_head by fastforce
  case est_inv  show ?case using distinct_tl    by fastforce
  case est_post show ?case using at_head_tl     by fastforce
next
  case est_guar show ?case
    apply clarsimp
    by (smt (verit, best) prefix_order.dual_order.refl queue_contract_def queue_contract_tl suffix_tl tl_prefix_before tl_suffix_after)
qed (fastforce+)

theorem qlock_global':
  assumes "0 < n"
  shows "global_init: \<lbrace> \<acute>queue = [] \<rbrace>  global_rely: Id
    \<parallel> i < n @
  { \<lbrace> i \<notin> set \<acute>queue \<rbrace>, qlock_rely i }
    WHILE True DO (
      (\<acute>queue := \<acute>queue @ [i]) ;;
      (WHILE hd \<acute>queue \<noteq> i DO SKIP OD) ;;
      (\<acute>queue := tl \<acute>queue))
    OD
  \<sslash> \<lbrace> distinct \<acute>queue \<rbrace>
  { for_others qlock_rely i, {} }
  global_guar: UNIV  global_post: {}"
proof method_multi_parallel_nobound
  case post show ?case using assms by fast
next
  case body show ?case
  proof (standard, method_loop)
    case (loop_body i) show ?case
    proof (rule Seq[where mid = "\<lbrace> at_head i \<acute>queue \<rbrace> \<inter> \<lbrace> distinct \<acute>queue \<rbrace>"], goal_cases ln1_ln2 ln3)
      case ln1_ln2 show ?case
      proof (rule Seq[where mid = "\<lbrace> i \<in> set \<acute>queue \<rbrace> \<inter> \<lbrace> distinct \<acute>queue \<rbrace>"], goal_cases ln1 ln2)
        case ln1 show ?case by (method_basic, auto)
        case ln2 show ?case using qlock_spin' by fast
      qed
      case ln3 show ?case using qlock_rel' by fast
    qed
  qed auto
qed auto

(*------------------------------------------------------------------*)
subsection \<open>No Annotations, Refined Invariant\<close>

text \<open>This section's RG theorems are still based on the non-annotated
command-type, and are proved using the structured proof-style.
They however use a more refined invariant that additionally stipulates
that all queuing threads have IDs smaller than a constant.
This is required to establish a more specific global postcondition.\<close>

consts N :: nat

abbreviation qlock_invar :: "queue_lock set" where
  "qlock_invar \<equiv> \<lbrace> distinct \<acute>queue \<and> set \<acute>queue \<subseteq> {..< N} \<rbrace>"

lemma qlock_spin:
 "rely: qlock_rely i  guar: for_others qlock_rely i
   inv: qlock_invar   code:
     { \<lbrace> i \<in> set \<acute>queue \<rbrace> }
   WHILE hd \<acute>queue \<noteq> i DO SKIP OD
     { \<lbrace> at_head i \<acute>queue \<rbrace> }"
proof method_spinloop
  case stable_post show ?case
    apply clarsimp
    by (metis (full_types) emptyE list.set(1) suffix_bot.extremum_uniqueI takeWhile_eq_Nil_iff)
qed (fastforce+)

lemma qlock_rel:
 "rely: qlock_rely i  guar: for_others qlock_rely i
   inv: qlock_invar   code:
     { \<lbrace> at_head i \<acute>queue \<rbrace> }
  \<acute>queue := tl \<acute>queue
     { \<lbrace> i \<notin> set \<acute>queue \<rbrace> }"
proof method_basic_inv
  case stab_pre show ?case
    using stable_at_head by fastforce
next
  case est_inv show ?case
    using distinct_tl apply clarsimp
    by (smt (verit, best) Nil_tl distinct_tl dual_order.trans hd_Cons_tl set_subset_Cons)
next
  case est_post show ?case
    using at_head_tl by fastforce
next
  case est_guar show ?case
    apply clarsimp
    by (smt (verit, best) prefix_order.dual_order.refl queue_contract_def queue_contract_tl suffix_tl tl_prefix_before tl_suffix_after)
qed (fastforce+)

theorem qlock_local:
  assumes "i < N" shows
  "rely: qlock_rely i  guar: for_others qlock_rely i
    inv: qlock_invar   code:
      { \<lbrace> i \<notin> set \<acute>queue \<rbrace> }
  \<acute>queue := \<acute>queue @ [i] ;;
   WHILE hd \<acute>queue \<noteq> i DO SKIP OD ;;
  \<acute>queue := tl \<acute>queue
      { \<lbrace> i \<notin> set \<acute>queue \<rbrace> }"
proof (rule Seq[where mid = "\<lbrace> at_head i \<acute>queue \<rbrace> \<inter> qlock_invar"],
       rule Seq[where mid = "\<lbrace> i \<in> set \<acute>queue \<rbrace> \<inter> qlock_invar"],
       goal_cases)
  case 1 show ?case
    apply method_basic
    using assms by auto
next
  case 2 show ?case
    apply method_spinloop
    using stable_at_head by auto
next
  case 3 show ?case
  proof method_basic
    case stable_pre show ?case
      using stable_at_head by auto
  next
    case establish_guar show ?case
    proof (standard, standard)
      fix s assume assm_s: "s \<in> \<lbrace> at_head i \<acute>queue \<rbrace> \<inter> qlock_invar"
      show "(s, s\<lparr>queue := tl (queue s)\<rparr>) \<in> lift_guar qlock_invar (for_others qlock_rely i)"
       (is "(?s, ?s') \<in> ?R")
      proof -
        have "(?s, ?s') \<in> for_others qlock_rely i"
          using assm_s apply clarsimp
          by (metis (mono_tags, lifting) Int_iff prefix_suffix_clause_def queue_contract_def queue_contract_tl)
        moreover have "?s \<in> qlock_invar"
          using assm_s by blast
        moreover have "?s' \<in> qlock_invar"
          using assm_s apply clarsimp
          by (smt (verit, ccfv_SIG) distinct_tl order_trans set_mono_sublist sublist_tl)
        ultimately have "(?s, ?s') \<in> Restr (for_others qlock_rely i) qlock_invar"
          by blast
        then show ?thesis using lift_guar_def by blast
      qed
    qed
  next
    case establish_post
    then show ?case
      using at_head_tl qlock_rel Basic_sat_implies_post_and_guar by fast
  qed (force+)
qed

theorem qlock_local_loop_empty:
  assumes "i < N" shows
  "rely: qlock_rely i  guar: for_others qlock_rely i
    inv: qlock_invar   code:
      { \<lbrace> i \<notin> set \<acute>queue \<rbrace> }
    WHILE True DO (
      (\<acute>queue := \<acute>queue @ [i]) ;;
      (WHILE hd \<acute>queue \<noteq> i DO SKIP OD) ;;
      (\<acute>queue := tl \<acute>queue))
    OD
      { {} }"
proof method_loop
  case loop_body show ?case using assms qlock_local by force
qed (fastforce+)

theorem qlock_local_loop_nonempty:
  assumes "i < N" shows
  "rely: qlock_rely i  guar: for_others qlock_rely i
    inv: qlock_invar   code:
      { \<lbrace> i \<notin> set \<acute>queue \<rbrace> }
    WHILE True DO (
      (\<acute>queue := \<acute>queue @ [i]) ;;
      (WHILE hd \<acute>queue \<noteq> i DO SKIP OD) ;;
      (\<acute>queue := tl \<acute>queue))
    OD
      { \<lbrace> \<acute>queue = [] \<rbrace> }"
proof-
  have "{} \<subseteq> \<lbrace> \<acute>queue = [] \<rbrace>"
    by simp
  then show ?thesis
    using weaken_post assms qlock_local_loop_empty by fastforce
qed

theorem qlock_global:
  assumes "0 < N"
  shows "global_init: \<lbrace> \<acute>queue = [] \<rbrace>  global_rely: Id
    \<parallel> i < N @
  { \<lbrace> i \<notin> set \<acute>queue \<rbrace>, qlock_rely i }
    WHILE True DO (
      (\<acute>queue := \<acute>queue @ [i]) ;;
      (WHILE hd \<acute>queue \<noteq> i DO SKIP OD) ;;
      (\<acute>queue := tl \<acute>queue))
    OD
  \<sslash> qlock_invar
  { for_others qlock_rely i, \<lbrace> \<acute>queue = [] \<rbrace> }
  global_guar: UNIV  global_post: \<lbrace> \<acute>queue = [] \<rbrace>"
proof method_multi_parallel
  case post show ?case using assms by blast
  case body show ?case using qlock_local_loop_nonempty by blast
qed auto

(*------------------------------------------------------------------*)
subsection \<open>Monolithic Theorem with Annotations\<close>

text \<open>The main theorem can also be stated as a monolithic RG sentence
on an annotated command, to be proved in the automated proof-style.
In contrast to the previous section, this serves as an alternative way
to state and prove the main RG theorem. Note that this theorem is based
on the more refined invariant, but the proof here is not dependent on
any lemma or theorem from the previous sections.\<close>

theorem qlock_global_anno:
  assumes "0 < N"
  shows "valid_multipar: annotated
  global_init: \<lbrace> \<acute>queue = [] \<rbrace>  global_rely: Id
    \<parallel> i < N @
  { \<lbrace> i \<notin> set \<acute>queue \<rbrace>, qlock_rely i }

  FOREVER (
    \<acute>queue := \<acute>queue @ [i] ..;
      \<lbrace> i \<in> set \<acute>queue \<rbrace> 
     SPIN hd \<acute>queue \<noteq> i  .;
      {\<lbrace> at_head i \<acute>queue \<rbrace>}
     (\<acute>queue := tl \<acute>queue)-
  )

  \<sslash> qlock_invar
  { for_others qlock_rely i, \<lbrace> i \<notin> set \<acute>queue \<rbrace> }
  global_guar: UNIV  global_post: \<lbrace> \<acute>queue = [] \<rbrace>"
  apply decompose_and_discharge
          apply (smt (verit, best) emptyE empty_set mem_Collect_eq prod.sel(1) prod.sel(2) stable_from_def suffix_bot.extremum_uniqueI takeWhile_eq_Nil_iff)
         using distinct_tl apply blast
        apply (meson dual_order.trans set_mono_sublist sublist_tl)
       apply (metis queue_contract_def queue_contract_tl)
      apply (simp add: tl_prefix_before)
     apply (simp add: tl_suffix_after)
    apply (meson at_head_tl)
   using assms apply blast
  apply auto
  using last_in_set by blast

end
