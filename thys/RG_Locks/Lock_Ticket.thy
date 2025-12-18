(* Title:      	   Ticket Lock
   Author(s):     Robert Colvin, Scott Heiner, Peter Hoefner, Roger Su
   License:       BSD 2-Clause
   Maintainer(s): Roger Su <roger.c.su@proton.me>
                  Peter Hoefner <peter@hoefner-online.de>
*)

(* In the formal proof document, the Ticket Lock section starts with
the content of the helper Function_Supplementary, followed by the
actual definitions and RG theorems here. *)

subsection \<open>Basic Definitions\<close>

theory Lock_Ticket

imports
  RG_Annotated_Commands
  Function_Supplementary

begin

type_synonym thread_id = nat

definition positive_nats :: "nat set" where
  "positive_nats \<equiv> { n. 0 < n }"

text \<open>The state of the Ticket Lock consists of three fields.\<close>

record tktlock_state =
  now_serving :: "nat"
  next_ticket :: "nat"
  myticket :: "thread_id \<Rightarrow> nat"

text \<open>Every thread locally stores a ticket number, and this collection of
local variables is modelled globally by the @{term myticket} function.

When Thread @{term i} joins the queue, it sets @{term \<open>myticket i\<close>} to be
the value @{term \<open>next_ticket\<close>}, and atomically increments @{term next_ticket};
this corresponds to the atomic Fetch-And-Add instruction, which is supported
on most computer systems.
%
Thread @{term i} then waits until the @{term now_serving} value becomes
equal to its own ticket number @{term \<open>myticket i\<close>}.
%
When Thread @{term i} leaves the queue, it increments @{term now_serving}.

These steps correspond to the following code for Acquire and Release.
Note that we use forward function composition to model the Fetch-And-Add
instruction.

@{theory_text[display = true] \<open>
  acquire \<equiv> ((myticket i := next_ticket) \<circ>>
              (next_ticket := next_ticket + 1));
             WHILE now_serving \<noteq> myticket i DO SKIP OD)

  release \<equiv> now_serving := now_serving + 1
\<close>}

Conceptually, Thread @{term i} is in the queue if and only if
@{theory_text \<open>now_serving \<le> myticket i\<close>}
and is at the head if and only if
@{theory_text \<open>now_serving = myticket i\<close>}.\<close>

(*------------------------------------------------------------------*)
text \<open>Now, in the initial state, every thread holds the number 0 as
its ticket, and both @{term now_serving} and @{term next_ticket} are
set to 1.\<close>

abbreviation tktlock_init :: "tktlock_state set" where
  "tktlock_init \<equiv> \<lbrace> \<acute>myticket = (\<lambda>j. 0) \<and>
    \<acute>now_serving = 1 \<and> \<acute>next_ticket = 1 \<rbrace>"

text \<open>We further define a shorthand for describing the set of ticket
in use; i.e.\ those numbers from @{term now_serving} up to, but not 
including @{term next_ticket}. This shorthand will later be used in
the invariant.\<close>

abbreviation tktlock_contending_set :: "tktlock_state \<Rightarrow> thread_id set" where
  "tktlock_contending_set s \<equiv> { j. now_serving s \<le> myticket s j }"

(*------------------------------------------------------------------*)
text \<open>We now formalise the invariant of the Ticket Lock.\<close>

abbreviation tktlock_inv :: "tktlock_state set" where
  "tktlock_inv \<equiv> \<lbrace> \<acute>now_serving \<le> \<acute>next_ticket \<and>
    1 \<le> \<acute>now_serving \<and>
    (\<forall> j. \<acute>myticket j < \<acute>next_ticket) \<and>
    bij_betw \<acute>myticket \<acute>tktlock_contending_set {\<acute>now_serving ..< \<acute>next_ticket} \<and>
    inj_img \<acute>myticket positive_nats \<rbrace>"

text \<open>The first three clauses are basic inequalities.

The penultimate clause stipulates that the function @{term myticket}
of every valid state is bijective between the set of queuing/contending
threads (those threads whose tickets are not smaller than @{term now_serving})
and .

The final clause ensures that the function @{term myticket} is injective
when 0 is excluded from its codomain. In other words, all threads, whose
tickets are non-zero, hold unique tickets.\<close>

(*------------------------------------------------------------------*)
text \<open>As for the contract, the first clause ensures that the local
variable @{term \<open>myticket i\<close>} does not change. Meanwhile, the global
variables @{term next_ticket} and @{term now_serving} must not decrease,
as stipulated by the second and third clauses of the contract.

The last two clauses of the contract correspond to the two clauses of
the contract of the Abstract Queue Lock, where 
@{theory_text \<open>i \<in> set queue\<close>} and @{theory_text \<open>at_head i queue\<close>} 
under the Abstract Queue Lock respectively translate to 
@{theory_text \<open>now_serving \<le> myticket i\<close>} and
@{theory_text \<open>now_serving = myticket i\<close>} under the Ticket Lock.\<close>

abbreviation tktlock_contract :: "thread_id \<Rightarrow> tktlock_state rel" where
  "tktlock_contract i \<equiv> \<lbrace> \<ordmasculine>myticket i = \<ordfeminine>myticket i \<and>
    \<ordmasculine>next_ticket \<le> \<ordfeminine>next_ticket \<and>
    \<ordmasculine>now_serving \<le> \<ordfeminine>now_serving \<and>  
    (\<ordmasculine>now_serving \<le> \<ordmasculine>myticket i \<longleftrightarrow> \<ordfeminine>now_serving \<le> \<ordfeminine>myticket i) \<and>
    (\<ordmasculine>now_serving = \<ordmasculine>myticket i \<longrightarrow> \<ordfeminine>now_serving = \<ordfeminine>myticket i) \<rbrace>"

(*------------------------------------------------------------------*)
text \<open>We further state and prove some helper lemmas that will be used later.\<close>

lemma tktlock_contending_set_rewrite:
  "tktlock_contending_set s \<union> {i} = \<lbrace>\<acute>(\<noteq>) i \<longrightarrow> now_serving s \<le> \<acute>(myticket s)\<rbrace>" 
  by fastforce

lemma tktlock_used_tickets_rewrite:
  assumes "now_serving s \<le> next_ticket s"
    shows "{now_serving s ..< next_ticket s} \<union> {next_ticket s}
         = {now_serving s ..< Suc (next_ticket s)}"
  by (fastforce simp: assms atLeastLessThanSuc)

lemma tktlock_enqueue_bij:
  assumes "myticket s i < now_serving s"
      and "bij_betw (myticket s) (tktlock_contending_set s) {now_serving s ..< next_ticket s}"
    shows "bij_betw ( (myticket s)(i := next_ticket s) )
                    ( tktlock_contending_set s \<union> {i} )
                    ( {now_serving s ..< next_ticket s} \<union> {next_ticket s} )"
  apply (rule bij_extension)
  using assms by fastforce+

lemma tktlock_enqueue_inj:
  assumes "s \<in> tktlock_inv"
  shows "inj_img ((myticket s)(i := next_ticket s)) positive_nats"
  apply(subst inj_img_fun_upd_notin)
  using assms by (fastforce simp: nat_less_le)+

method clarsimp_seq = clarsimp, standard, clarsimp

(*------------------------------------------------------------------*)
subsection \<open>RG Theorems\<close>

text \<open>The RG sentence of the first instruction of Acquire.\<close>

lemma tktlock_acq1:
  "rely: tktlock_contract i  guar: for_others tktlock_contract i
   inv:  tktlock_inv    anno_code:
   { \<lbrace> \<acute>myticket i < \<acute>now_serving \<rbrace> }
     BasicAnno ((\<acute>myticket[i] \<leftarrow> \<acute>next_ticket) \<circ>>
                (\<acute>next_ticket \<leftarrow> \<acute>next_ticket + 1))
   { \<lbrace> \<acute>now_serving \<le> \<acute>myticket i \<rbrace> }"
proof method_anno_ultimate
  case est_guar
  thus ?case
    apply clarsimp_seq
     apply (fastforce simp: less_Suc_eq)
    using tktlock_contending_set_rewrite tktlock_enqueue_bij 
    by (fastforce simp: atLeastLessThanSuc tktlock_enqueue_inj)
next
  case est_post
  thus ?case
    apply clarsimp_seq
     apply (fastforce simp: less_Suc_eq)
    using tktlock_contending_set_rewrite tktlock_enqueue_bij 
    by (fastforce simp: atLeastLessThanSuc tktlock_enqueue_inj) 
qed (fastforce)+

text \<open>A helper lemma for the Release procedure.\<close>

lemma tktlock_rel_helper:
  assumes inv1: "now_serving s = myticket s i"
      and inv2: "myticket s i \<le> next_ticket s"
      and inv3: "Suc 0 \<le> myticket s i"
      and inv4: "\<forall>j. myticket s j < next_ticket s"
      and bij_old: "bij_betw (myticket s)
                             \<lbrace>myticket s i \<le> \<acute>(myticket s)\<rbrace>
                             {myticket s i ..< next_ticket s}"
    shows "bij_betw (myticket s)
                    \<lbrace>Suc (myticket s i) \<le> \<acute>(myticket s)\<rbrace>
                    {Suc (myticket s i) ..< next_ticket s}"
proof -
  have thread_rewrite:
    "\<lbrace> Suc (myticket s i) \<le> \<acute>(myticket s)\<rbrace> = {j. myticket s i \<le> myticket s j} - {i}"
    apply (subst set_remove_one_element[where B="{j. Suc (myticket s i) \<le> myticket s j}"]; clarsimp)
    by(metis CollectI Suc_leI assms(5) bij_betw_def inj_onD order_le_imp_less_or_eq)
  have ticket_rewrite: 
    "{Suc (myticket s i) ..< next_ticket s} = {myticket s i ..< next_ticket s} - {myticket s i}"
    by fastforce
  have "bij_betw (myticket s)
                 ( {j. myticket s i \<le> myticket s j} - {i} )
                 ( {myticket s i ..< next_ticket s} - {myticket s i} )"
    by (rule bij_remove_one; clarsimp simp: bij_old)
  thus ?thesis
    by (clarsimp simp: thread_rewrite ticket_rewrite)
qed

text \<open>The RG sentence for the Release procedure.\<close>

lemma tktlock_rel:
  "rely: tktlock_contract i
   guar: for_others tktlock_contract i
   inv:  tktlock_inv

   code: { \<lbrace> \<acute>now_serving = \<acute>myticket i \<rbrace> }
           \<acute>now_serving := \<acute>now_serving + 1
         { \<lbrace> \<acute>myticket i < \<acute>now_serving \<rbrace> }"
proof method_basic_inv
  case est_inv
  thus ?case
    by (clarsimp, fastforce simp: Suc_le_eq intro!: tktlock_rel_helper)
next
  case est_guar
  thus ?case
    by (clarsimp, fastforce simp: less_eq_Suc_le nat_less_le positive_nats_def inj_img_def)
qed (fastforce)+

text \<open>The RG sentence for a thread that performs Acquire and then Release.\<close>

lemma tktlock_local:
 "rely: tktlock_contract i  guar: for_others tktlock_contract i
  inv: tktlock_inv     anno_code:

   { \<lbrace> \<acute>myticket i < \<acute>now_serving \<rbrace> }
   BasicAnno ((\<acute>myticket[i] \<leftarrow> \<acute>next_ticket) \<circ>>
              (\<acute>next_ticket \<leftarrow> \<acute>next_ticket + 1)) .;
   { \<lbrace> \<acute>now_serving \<le> \<acute>myticket i \<rbrace> }
   NoAnno (WHILE \<acute>now_serving \<noteq> \<acute>myticket i DO SKIP OD) .;
   { \<lbrace> \<acute>now_serving = \<acute>myticket i \<rbrace> }
   NoAnno (\<acute>now_serving := \<acute>now_serving + 1)
   { \<lbrace> \<acute>myticket i < \<acute>now_serving \<rbrace> }"
  apply (method_anno_ultimate, goal_cases)
    using tktlock_acq1 apply fastforce 
   apply (clarsimp, method_spinloop; fastforce)
  using tktlock_rel by fastforce

text \<open>The RG sentence for a thread that repeatedly performs Acquire 
and then Release in an infinite loop.\<close>

lemma tktlock_local_loop:
 "rely: tktlock_contract i  guar: for_others tktlock_contract i
  inv:  tktlock_inv    anno_code:

   { \<lbrace> \<acute>myticket i < \<acute>now_serving \<rbrace> }
   WHILEa True DO
    {stable_guard: \<lbrace> \<acute>myticket i < \<acute>now_serving \<rbrace> }
     BasicAnno ((\<acute>myticket[i] \<leftarrow> \<acute>next_ticket) \<circ>>
                (\<acute>next_ticket \<leftarrow> \<acute>next_ticket + 1)) .;
     { \<lbrace> \<acute>now_serving \<le> \<acute>myticket i \<rbrace> }
     NoAnno (WHILE \<acute>now_serving \<noteq> \<acute>myticket i DO SKIP OD) .;
     { \<lbrace> \<acute>now_serving = \<acute>myticket i \<rbrace> }
     NoAnno (\<acute>now_serving := \<acute>now_serving + 1)
   OD
   { \<lbrace> \<acute>myticket i < \<acute>now_serving \<rbrace> }"
proof method_anno_ultimate
  case body
  thus ?case 
    using tktlock_local by (fastforce simp: Int_commute)
qed (fastforce)+

text \<open>The global RG sentence for a set of threads, each of which 
repeatedly performs Acquire and then Release in an infinite loop.\<close>

theorem tktlock_global:
  assumes "0 < n"
    shows "annotated
  global_init: \<lbrace> \<acute>now_serving = 1 \<and> \<acute>next_ticket = 1 \<and> \<acute>myticket = (\<lambda>j. 0) \<rbrace>
  global_rely: Id
    \<parallel> i < n @

  { \<lbrace> \<acute>myticket i < \<acute>now_serving \<rbrace>, tktlock_contract i }
  WHILEa True DO
    {stable_guard: \<lbrace> \<acute>myticket i < \<acute>now_serving \<rbrace> }
    BasicAnno ((\<acute>myticket[i] \<leftarrow> \<acute>next_ticket) \<circ>>
               (\<acute>next_ticket \<leftarrow> \<acute>next_ticket + 1)) .;
    { \<lbrace> \<acute>now_serving \<le> \<acute>myticket i \<rbrace> }
    NoAnno (WHILE \<acute>now_serving \<noteq> \<acute>myticket i DO SKIP OD) .;
    { \<lbrace> \<acute>now_serving = \<acute>myticket i \<rbrace> }
    NoAnno (\<acute>now_serving := \<acute>now_serving + 1)
  OD

  \<sslash> tktlock_inv { for_others tktlock_contract i, {} }
  global_guar: UNIV
  global_post: {}"
proof method_anno_ultimate
  case (local_sat i)
  thus ?case using tktlock_local_loop by fastforce
next
  case (pre i)
  thus ?case
    using bij_betwI' inj_img_def positive_nats_def by fastforce
next
  case (guar_imp_rely i j)
  thus ?case   
    by auto[1]
qed (fastforce simp: assms)+

end
