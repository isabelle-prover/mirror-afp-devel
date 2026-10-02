
(*
Title:         Correctness Property of the Concurrent Queue
Author(s):     Robert Colvin, Scott Heiner, Peter Hoefner, Roger Su
Year:          2026
License:       BSD 2-Clause
Maintainer(s): Robert Colvin <r.colvin@uq.edu.au>
               Peter Hoefner <peter@hoefner-online.de>
               Roger Su <roger.c.su@proton.me>
*)

section \<open>Correctness Property of the Concurrent Queue\<close>

text \<open>This theory studies the concurrent queue's correctness property,
expressed under the \emph{rely-guarantee} paradigm, where each process
is specified not only by a precondition and a postcondition, but also
by a rely-relation and a guarantee-relation. These two relations
specify the expected interaction between each process and its
environment. In many scenarios, the rely- and guarantee-relations
exhibit a certain symmetry, which allows them to be expressed in terms
of a common clause, called the \emph{contract}.

This theory defines the contract of the concurrent queue, in which
every process occurs at most once. Queues of this nature are useful for
modelling queued locks.\<close>

theory Concurrent_Queue_Contract
imports "HOL-Library.Sublist" Helpers_Lists_Option
begin

(*==================================================================*)
subsection \<open>The Prefix-Suffix Clause\<close>

text \<open>This section defines the ``prefix-suffix'' clause, which is a
key component of the queue-contract in the next section.\<close>

text \<open>From the viewpoint of an element in the queue, the only changes
it can observe from the environment are (1) the head leaving the queue,
and (2) new elements joining the queue. This calls for the definition
of the following notions: @{term \<open>prefix_before xs i\<close>} is the list of
all elements that are ``before'' the element @{term i} in the queue
@{term xs}; analogously, @{term \<open>suffix_after xs i\<close>} is the list of
all elements that are ``after'' @{term i} in the queue @{term xs}.\<close>

abbreviation prefix_before :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "prefix_before xs i \<equiv> takeWhile (\<lambda>j. i \<noteq> j) xs"

abbreviation suffix_after :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "suffix_after xs i \<equiv> tl (dropWhile (\<lambda>j. i \<noteq> j) xs)"

text \<open>The key part of the contract is thus the following
\emph{prefix-suffix clause}, which stipulates that \emph{
the new prefix is a suffix of the old prefix, and
the old suffix is a prefix of the new suffix}.\<close>

definition prefix_suffix_clause :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "prefix_suffix_clause i xs ys \<equiv> i \<in> set xs \<inter> set ys \<longrightarrow>
      suffix (prefix_before ys i) (prefix_before xs i)
    \<and> prefix (suffix_after  xs i) (suffix_after  ys i)"

text \<open>Note that the premise @{term \<open>i \<in> set xs \<inter> set ys\<close>} in this
definition is crucial for avoiding the edge-cases where @{term i} is
not in the list, as shown below.\<close>

lemma assumes "a \<noteq> b"
  shows "prefix_before [b] a = [b]"
    and "suffix_after  [b] a = []"
  using assms by auto

lemma suffix_after_intro:
  "\<lbrakk> distinct xs ; xs = ps @ i # ss \<rbrakk> \<Longrightarrow> suffix_after xs i = ss"
  by (simp add: dropWhile_append3 tl_append_if)

lemma prefix_before_intro:
  "\<lbrakk> distinct xs ; xs = ps @ i # ss \<rbrakk> \<Longrightarrow> prefix_before xs i = ps"
  by (simp add: takeWhile_append)

lemma prefix_before_not_containing: "i \<notin> set (prefix_before xs i)"
  by (metis (full_types) set_takeWhileD)

lemma suffix_after_nonempty: "suffix_after xs i \<noteq> [] \<Longrightarrow> i \<in> set xs"
  by (simp add: tl_Nil)

lemma prefix_i_suffix:
  "\<lbrakk> distinct xs ; i \<in> set xs \<rbrakk>
  \<Longrightarrow> xs = (prefix_before xs i) @ i # (suffix_after xs i)"
  by (smt (verit, best) dropWhile_eq_Cons_conv dropWhile_eq_Nil_conv list.collapse)

lemma prefix_before_empty_is_head:
  "i \<in> set xs \<Longrightarrow> (prefix_before xs i = []) \<longleftrightarrow> i = hd xs"
  using takeWhile_eq_Nil_iff by (metis (full_types) empty_iff empty_set)

lemma at_head_prefix_before_empty:
  "at_head i xs \<Longrightarrow> prefix_before xs i = []"
  by (induction xs; simp)

lemma tl_prefix_before:
  "\<not> at_head i xs \<Longrightarrow> prefix_before (tl xs) i = tl(prefix_before xs i)"
  apply (induction xs) apply simp apply simp by blast

lemma tl_suffix_after:
  "\<not> at_head i xs \<Longrightarrow> suffix_after (tl xs) i = suffix_after xs i"
  apply (induction xs) apply simp apply simp by blast

(*==================================================================*)
subsection \<open>The Queue-Contract\<close>

text \<open>Using the prefix-suffix clause, this section defines the contract
of the concurrent queue.\<close>

text \<open>As shown by the following negative lemma, the prefix-suffix
clause alone does not capture the ``self-controlling property'', which
the queue-contract should possess. This property states that an element
can only be added to or removed from the queue by itself, never by the
environment..\<close>

lemma pref_suff_alone_not_enough:
  "\<not> (\<forall> i xs ys. prefix_suffix_clause i xs ys \<longrightarrow> (i \<in> set xs \<longleftrightarrow> i \<in> set ys))"
  by (metis Int_iff list.set_intros(1) prefix_before_not_containing prefix_suffix_clause_def)

text \<open>Consequently, the queue-contract needs to include both the
self-controlling property and the prefix-suffix clause, resulting
in the definition below.\<close>

definition queue_contract :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "queue_contract i xs ys \<equiv> (i \<in> set xs \<longleftrightarrow> i \<in> set ys)
                          \<and> (prefix_suffix_clause i xs ys)"

lemmas [simp] = prefix_suffix_clause_def queue_contract_def

lemma queue_contract_id: "queue_contract i xs xs" by simp

lemma queue_contract_nonempty:
  "i \<in> set xs \<Longrightarrow> \<not> queue_contract i xs [] \<and> \<not> queue_contract i [] xs"
  by auto

lemma queue_contract_not_in:
  "\<lbrakk> distinct xs ; distinct ys ; i \<notin> set xs ; i \<notin> set ys \<rbrakk>
  \<Longrightarrow> queue_contract i xs ys"
  by force

lemma queue_contract_enq:
  "\<lbrakk> distinct xs ; i \<noteq> x \<rbrakk> \<Longrightarrow> queue_contract i xs (xs @ [x])"
  by simp

lemma queue_contract_deq:
  "\<lbrakk> distinct (x # xs) ; i \<in> set xs \<rbrakk> \<Longrightarrow> queue_contract i (x # xs) xs"
  using suffix_Cons by fastforce

lemma stable_in_queue:
  "\<lbrakk> i \<in> set xs ; queue_contract i xs ys \<rbrakk> \<Longrightarrow> i \<in> set ys"
  by simp

lemma stable_at_head:
  assumes "queue_contract i xs ys"
      and "at_head i xs"
    shows "at_head i ys"
proof-
  have "prefix_before xs i = []"
    using assms(2) prefix_before_empty_is_head by fast
  then have "prefix_before ys i = []"
    using assms by force
  then show ?thesis
    using assms prefix_before_empty_is_head by (metis stable_in_queue)
qed

lemma queue_contract_tl:
  "\<not> at_head i xs \<Longrightarrow> queue_contract i xs (tl xs)"
  apply (cases xs)
   apply force
  using suffix_ConsI by force

(*==================================================================*)
subsection \<open>Lemmas on Sublists\<close>

lemma sublist_ij_suffix_hd_j:
  "\<lbrakk> distinct xs ; sublist [i,j] xs \<rbrakk> \<Longrightarrow> j = hd (suffix_after xs i)"
  by (clarsimp simp add: sublist_def dropWhile_append)

lemma sublist_ij_suffix_in_j:
  "\<lbrakk> distinct xs ; sublist [i,j] xs \<rbrakk> \<Longrightarrow> j \<in> set (suffix_after xs i)"
  by (clarsimp simp add: sublist_def dropWhile_append)

lemma sublist_ij_prefix_last:
  "\<lbrakk> distinct xs ; sublist [i,j] xs \<rbrakk> \<Longrightarrow> i = last (prefix_before xs j)"
  by (clarsimp simp add: sublist_def takeWhile_append)

lemma at_head_sublist_prefix:
  "distinct xs \<Longrightarrow> (at_head i xs \<and> sublist [i,j] xs) = prefix [i,j] xs"
  by (metis Cons_prefix_Cons distinct.simps(2) distinct_singleton hd_Cons_tl 
            prefix_imp_sublist sublist_Cons_right sublist_ij_suffix_in_j 
            suffix_after_nonempty)

theorem last_of_prefix_implies_sublist:
  "\<lbrakk> distinct xs ;
     j \<in> set xs ;
     i \<in> set (prefix_before xs j) ;
     i = last (prefix_before xs j) \<rbrakk>
  \<Longrightarrow> sublist [i,j] xs"
  by (metis in_queue_not_hd_pred last_snoc prefix_before_empty_is_head snoc_eq_iff_butlast sublist_ij_prefix_last)

theorem head_of_suffix_implies_sublist:
  "\<lbrakk> distinct xs ;
     i \<in> set xs ;
     at_head j (suffix_after xs i) \<rbrakk>
  \<Longrightarrow> sublist [i,j] xs"
  by (metis empty_iff empty_set list.exhaust_sel prefix_i_suffix sublist_ij_explicit)

(*------------------------------------------------------------------*)
theorem queue_contract_preserves_sublist_pred:
  assumes assm_contract:   "queue_contract j xs ys"
      and assm_distinct:   "distinct xs \<and> distinct ys"
      and assm_sublist: "sublist [i,j] ys"
    shows "sublist [i,j] xs"
proof-
  have ln1: "j \<in> set xs"
    using assm_sublist assm_contract set_mono_sublist by fastforce
  then have "suffix (prefix_before ys j) (prefix_before xs j)"
    using assm_contract by simp
  moreover have "i = last (prefix_before ys j)"
    using assm_distinct assm_sublist sublist_ij_prefix_last by fast
  ultimately have ln4: "i = last (prefix_before xs j)"
    using ln1 suffix_same_last
    by (metis (full_types) assm_contract assm_distinct assm_sublist
        queue_contract_nonempty sublist_ij_j_not_hd takeWhile_eq_Nil_iff)
  then have "i \<in> set (prefix_before xs j)"
    using assm_contract assm_distinct assm_sublist
    by (simp, metis last_in_set ln1 prefix_before_empty_is_head
              sublist_ij_j_not_hd suffix_bot.extremum_unique)
  then show ?thesis
    using last_of_prefix_implies_sublist assm_distinct ln1 ln4 by metis
qed

theorem queue_contract_preserves_sublist_succ:
  assumes assm_contract:   "queue_contract i xs ys"
      and assm_distinct:   "distinct xs \<and> distinct ys"
      and assm_sublist: "sublist [i,j] xs"
    shows "sublist [i,j] ys"
proof-
  have "i \<in> set ys"
    using assm_contract assm_sublist set_mono_sublist by fastforce
  moreover
  have "at_head j (suffix_after xs i)"
    by (metis assm_distinct assm_sublist sublist_ij_suffix_hd_j sublist_ij_suffix_in_j)
  then have "at_head j (suffix_after ys i)"
    using assm_contract 
    by (simp, metis calculation distinct.simps(2) distinct_singleton hd_append2 prefixE
         set_mono_prefix subsetD)
  ultimately show ?thesis by (metis assm_distinct head_of_suffix_implies_sublist)
qed

(*------------------------------------------------------------------*)
theorem sublist_ij_contract_explicit:
  assumes assm_xs: "xs = ps @ i # j # ss"
      and assm_contract: "queue_contract i xs ys"
      and assm_distinct: "distinct xs \<and> distinct ys"
    shows "ys = (prefix_before ys i) @ i # j # (suffix_after ys j)"
proof-
  have "\<exists> zs. suffix_after ys i = j # zs"
  proof-
    have "suffix_after xs i = j # ss"
      by (metis assm_distinct assm_xs suffix_after_intro)
    moreover
    have "xs = (ps @ [i]) @ j # ss"
      using assm_xs by auto
    then have "suffix_after xs j = ss"
      using assm_xs assm_distinct suffix_after_intro by fast
    ultimately have "suffix_after xs i = j # suffix_after xs j"
      by simp
    then have "prefix (j # suffix_after xs j) (suffix_after ys i)"
      using assm_contract assm_contract assm_xs by fastforce
    then show ?thesis by (metis append_Cons prefix_def)
  qed
  then obtain ss' where ss': "suffix_after ys i = j # ss'"
    by blast
  (*--------------------------------------------*)
  have "ys = (prefix_before ys i) @ i # (suffix_after ys i)"
    using assms prefix_i_suffix by fastforce
  also have "... = (prefix_before ys i @ [i]) @ j # ss'"
    using ss' by simp
  also have "... = (prefix_before ys i @ [i]) @ j # (suffix_after ys j)"
    using assm_distinct suffix_after_intro by (metis calculation)
  ultimately show ?thesis by auto
qed

(*==================================================================*)
subsection \<open>Counterexamples\<close>

text \<open>Counterexamples that were not ruled out by the previous versions
of the contract.\<close>

fun index_of :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "index_of [] _ = undefined"
| "index_of (x # xs) i = (if x = i then 0 else index_of xs i + 1)"

definition old_contract_1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "old_contract_1 i xs ys \<equiv> (i \<in> set xs \<longleftrightarrow> i \<in> set ys)
                        \<and> (at_head i xs \<longrightarrow> at_head i ys)"

definition old_contract_2 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "old_contract_2 i xs ys \<equiv> (i \<in> set xs \<longleftrightarrow> i \<in> set ys)
                          \<and> (index_of ys i \<le> index_of xs i)"

lemmas defs [simp] = old_contract_1_def old_contract_2_def

lemma "old_contract_2 i xs ys \<Longrightarrow> old_contract_1 i xs ys"
  by (clarsimp, metis Suc_eq_plus1 bot_nat_0.extremum_uniqueI index_of.elims 
  length_pos_if_in_set list.sel(1) list.size(3) rel_simps(70) zero_less_Suc)

locale queue_examples =
  fixes a b c d :: 'a
  assumes locale_assm: "distinct [a, b, c, d]"
begin

lemma eg1:
  shows "old_contract_1 a [a,b] [a,c,b]"
  and "\<not> queue_contract a [a,b] [a,c,b]"
  using locale_assm by auto

lemma eg2:
  shows "old_contract_1 b [a,b] [a,c,b]"
  and "\<not> queue_contract b [a,b] [a,c,b]"
   apply simp
  using locale_assm set_mono_suffix by fastforce

lemma eg3:
  shows "old_contract_1 a [a,b,c] [a,c,b]"
  and "\<not> queue_contract a [a,b,c] [a,c,b]"
  using locale_assm by auto

lemma eg4:
  shows "old_contract_1 b [a,b,c] [a,c,b]"
  and "\<not> queue_contract b [a,b,c] [a,c,b]"
  using locale_assm by auto

lemma eg5:
  shows "old_contract_2 b [a,b] [c,b]"
  and "\<not> queue_contract b [a,b] [c,b]"
  using locale_assm apply force
  using locale_assm set_mono_suffix by force

lemma eg6:
  shows "old_contract_2 b [a,b,c] [c,b]"
  and "\<not> queue_contract b [a,b,c] [c,b]"
  using locale_assm by auto

end text \<open>End of locale.\<close>

(*------------------------------------------------------------------*)
subsection \<open>The Premise of the Prefix-Suffix Clause\<close>

text \<open>The next counterexample is what necessitated the premise
{@term \<open>i \<in> set xs \<inter> set ys\<close>} in the definition of the prefix-suffix
clause.\<close>

definition wrong_prefix_suffix_clause
  :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "wrong_prefix_suffix_clause i xs ys \<equiv>
      suffix (prefix_before ys i) (prefix_before xs i)
    \<and> prefix (suffix_after  xs i) (suffix_after  ys i)"

abbreviation wrong_contract :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "wrong_contract i xs ys \<equiv> (i \<in> set xs \<longleftrightarrow> i \<in> set ys)
                          \<and> wrong_prefix_suffix_clause i xs ys"

text \<open>If @{term a} belongs to neither queue, then @{term b}'s joining
the queue should be permitted by the contract.
However, if the prefix-suffix clause did not have the premise of
{@term \<open>i \<in> set xs \<inter> set ys\<close>}, then this permitted behaviour would
be erroneously ruled out.

The cause of this problem is the way @{term \<open>prefix_before\<close>} and
@{term \<open>suffix_after\<close>} are defined, and how they handle the case when
the element of interest does not belong to the list.

In the following example, @{term \<open>prefix_before [] a = []\<close>} and
@{term \<open>prefix_before [b] a = [b]\<close>}, and @{term \<open>[b]\<close>} is not a
suffix of @{term \<open>[]\<close>}, hence making @{term \<open>wrong_prefix_suffix_clause
a [] [b]\<close>} False.\<close>

lemma eg_no_premise:
  assumes "a \<noteq> b"
    shows "queue_contract a [] [b]"
      and "\<not> wrong_contract a [] [b]"
  using assms apply simp
  using assms wrong_prefix_suffix_clause_def by force

text \<open>As to the reason why the premise of @{text prefix_suffix_clause}
is an intersection rather than a union---this is immaterial, as the
self-controlling clause of @{text prefix_suffix_clause} enforces the
process @{term i} to belong to both queues.\<close>

end
