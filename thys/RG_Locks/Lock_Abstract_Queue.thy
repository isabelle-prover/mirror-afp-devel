(* Title:      	   Abstract Queue Lock
   Author(s):     Robert Colvin, Scott Heiner, Peter Hoefner, Roger Su
   License:       BSD 2-Clause
   Maintainer(s): Roger Su <roger.c.su@proton.me>
                  Peter Hoefner <peter@hoefner-online.de>
*)

section \<open>Abstract Queue Lock\<close>

theory Lock_Abstract_Queue

imports
  RG_Annotated_Commands

begin

text \<open>We identify each thread by a natural number.\<close>

type_synonym thread_id = nat

text \<open>The state of the Abstract Queue Lock consists of one single
field, which is the list of threads.\<close>

record queue_lock = queue :: "thread_id list"

text \<open>The following abbreviation describes when an object is at the
head of a list. Note that both clauses are needed to characterise the
predicate faithfully, because the term @{term \<open>x = hd xs\<close>} (i.e.\
@{term x} is the head of @{term xs}) does not imply that @{term \<open>x \<in> set xs\<close>}.\<close>

abbreviation at_head :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "at_head x xs \<equiv> xs \<noteq> [] \<and> x = hd xs"

text \<open>The contract of the Abstract Queue Lock consists of two clauses.
The first states that a thread cannot be added to or removed from the
queue by its environment. The second states that the head of the queue
remains at the head after any environment-step.\<close>

abbreviation queue_contract :: "thread_id \<Rightarrow> queue_lock rel" where
  "queue_contract i \<equiv> \<lbrace>
    (i \<in> set \<ordmasculine>queue \<longleftrightarrow> i \<in> set \<ordfeminine>queue) \<and>
    (at_head i \<ordmasculine>queue \<longrightarrow> at_head i \<ordfeminine>queue) \<rbrace>"

text \<open>The RG sentence of the Release procedure is made into a separate
lemma below.\<close>

lemma qlock_rel:
 "rely: queue_contract t     guar: for_others queue_contract t
  inv:  \<lbrace> distinct \<acute>queue \<rbrace>  code:
    { \<lbrace> at_head t \<acute>queue \<rbrace> }
  \<acute>queue := tl \<acute>queue
    { \<lbrace> t \<notin> set \<acute>queue \<rbrace> }"
proof method_basic_inv
  case est_guar
  then show ?case
    apply clarsimp
    by (metis hd_Cons_tl in_set_member member_rec(1))
next
  case est_post
  then show ?case
    apply clarsimp
    by (metis distinct.simps(2) list.collapse)
qed (simp_all add: distinct_tl)

text \<open>The correctness of the Abstract Queue Lock is expressed by the
following RG sentence, which describes a closed system of @{term n} 
threads, each repeatedly calls Acquire and then Release in an infinite
loop. We omit the critical section between Acquire and Release, as it
does not access the lock.

The Acquire procedure consists of two steps: enqueuing and spinning.
The Release procedure consists of only the dequeuing step.

Each thread can only be in the queue at most once, so the invariant
requires the queue to be distinct.

The queue is initially empty; hence the global precondition.
Being a closed system, there is no external actor, so the rely is the
identity relation, and the guarantee is the universal relation.
The system executes continuously, as the outer infinite loop never
terminates; hence, the global postcondition is the empty set.
\<close>

theorem qlock_global:
  assumes "0 < n"
  shows "annotated
  global_init: \<lbrace> \<acute>queue = [] \<rbrace>  global_rely: Id
    \<parallel> i < n @
  { \<lbrace> i \<notin> set \<acute>queue \<rbrace>, queue_contract i }

  WHILEa True DO
    {stable_guard: \<lbrace> i \<notin> set \<acute>queue \<rbrace> }
    NoAnno (\<acute>queue := \<acute>queue @ [i]) .;
    { \<lbrace> i \<in> set \<acute>queue \<rbrace> }
    NoAnno (WHILE hd \<acute>queue \<noteq> i DO SKIP OD) .;
    { \<lbrace> at_head i \<acute>queue \<rbrace>}
    NoAnno (\<acute>queue := tl \<acute>queue)
  OD

  \<sslash> \<lbrace> distinct \<acute>queue \<rbrace> { for_others queue_contract i, {} }
  global_guar: UNIV  global_post: {}"
  apply rg_proof_expand
     apply (method_basic; fastforce)
    apply (method_spinloop; fastforce)
   using qlock_rel apply fastforce
  using assms by fastforce

end
