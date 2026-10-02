
(*
Title:         Rely-Guarantee Verification of the Ticket Lock
Author(s):     Robert Colvin, Scott Heiner, Peter Hoefner, Roger Su
Year:          2026
License:       BSD 2-Clause
Maintainer(s): Robert Colvin <r.colvin@uq.edu.au>
               Peter Hoefner <peter@hoefner-online.de>
               Roger Su <roger.c.su@proton.me>
*)

section \<open>Ticket Lock\<close>

text \<open>The specification and the proof of the Ticket Lock, based on the
new specification of queues, and uses auxiliary-coupling.\<close>

theory Lock_Ticket

imports
  Concurrent_Queue_Contract
  RG_Annotated_Methods

begin

(*------------------------------------------------------------------*)
text \<open>We begin with some generic helpers that will be used later in
the verification of the Ticket Lock.\<close>

definition inj_img :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> bool" where
  "inj_img f B \<equiv> \<forall> x1 x2. f x1 = f x2 \<and> f x1 \<in> B \<longrightarrow> x1 = x2"

lemma bij_extension:
  assumes "a \<notin> A"
      and "b \<notin> B"
      and "bij_betw f A B"
    shows "bij_betw (fun_upd f a b) (A \<union> {a}) (B \<union> {b})"
  by (metis assms bij_betw_combine bij_betw_cong bij_betw_singleton_iff disjoint_insert(1)
            fun_upd_other fun_upd_same inf_bot_right)

lemma inj_img_fun_upd_notin:
  assumes "inj_img f B"
      and "\<forall> x. f x \<noteq> b"
    shows "inj_img (fun_upd f a b) B"
  using assms unfolding inj_img_def by (metis fun_upd_def)

lemma bij_remove_one:
  assumes "a \<in> A"
      and "bij_betw f A B"
    shows "bij_betw f (A - {a}) (B - {f a})"
  using assms bij_betwE bij_betw_DiffI by fastforce

lemma set_remove_one_element:
  assumes "x \<notin> B"
      and "B \<subseteq> A"
      and "A - {x} \<subseteq> B"
    shows "A - {x} = B"
  using assms by blast

lemma helper_map_inj:
  assumes "map f xs = ys"
      and "f x \<in> set ys"
      and "set ys \<subseteq> B"
      and "inj_img f B"
    shows "x \<in> set xs"
  using assms by (clarsimp, metis image_subset_iff inj_img_def)

(*------------------------------------------------------------------*)
text \<open>Now we define the state of the Ticket Lock, as well as the
invariant and rely.\<close>

type_synonym thread_id = nat

definition positive_nats :: "nat set" where
  "positive_nats \<equiv> { n. 0 < n }"

record tktlock_state =
  now_serving :: nat
  next_ticket :: nat
  myticket :: "thread_id \<Rightarrow> nat"
  aux_queue :: "thread_id list"

definition tktlock_init :: "tktlock_state set" where
  "tktlock_init \<equiv> \<lbrace> \<acute>myticket = (\<lambda>i. 0)
                  \<and> \<acute>now_serving = 1
                  \<and> \<acute>next_ticket = 1
                  \<and> \<acute>aux_queue = [] \<rbrace>"

definition contending_threads :: "tktlock_state \<Rightarrow> thread_id set" where
  "contending_threads s \<equiv> { i. now_serving s \<le> myticket s i }"

definition tktlock_inv_concrete :: "tktlock_state set" where
  "tktlock_inv_concrete \<equiv> \<lbrace> \<acute>now_serving \<le> \<acute>next_ticket 
    \<and> 1 \<le> \<acute>now_serving
    \<and> (\<forall> i. \<acute>myticket i < \<acute>next_ticket) 
    \<and> bij_betw \<acute>myticket \<acute>contending_threads {\<acute>now_serving ..< \<acute>next_ticket}
    \<and> inj_img \<acute>myticket positive_nats \<rbrace>"

definition tktlock_inv_coupling :: "tktlock_state set" where
  "tktlock_inv_coupling \<equiv> \<lbrace> map \<acute>myticket \<acute>aux_queue
                            = [\<acute>now_serving ..< \<acute>next_ticket] \<rbrace>"

definition tktlock_inv :: "tktlock_state set" where
  "tktlock_inv \<equiv> tktlock_inv_concrete \<inter> tktlock_inv_coupling"

definition tktlock_rely :: "thread_id \<Rightarrow> tktlock_state rel" where
  "tktlock_rely i \<equiv> \<lbrace> \<ordmasculine>myticket i = \<ordfeminine>myticket i
    \<and> \<ordmasculine>next_ticket \<le> \<ordfeminine>next_ticket 
    \<and> \<ordmasculine>now_serving \<le> \<ordfeminine>now_serving 
    \<and> (\<ordmasculine>now_serving \<le> \<ordmasculine>myticket i \<longleftrightarrow> \<ordfeminine>now_serving \<le> \<ordfeminine>myticket i)
    \<and> (\<ordmasculine>now_serving = \<ordmasculine>myticket i \<longrightarrow> \<ordfeminine>now_serving = \<ordfeminine>myticket i)
    \<and> queue_contract i \<ordmasculine>aux_queue \<ordfeminine>aux_queue \<rbrace>"

lemmas defs [simp] = positive_nats_def
                     contending_threads_def 
                     tktlock_inv_concrete_def 
                     tktlock_inv_coupling_def 
                     tktlock_inv_def 
                     tktlock_rely_def

(*------------------------------------------------------------------*)
subsection \<open>Helper Lemmas\<close>

lemma coupling_in_queue:
  assumes "s \<in> tktlock_inv"
  shows "i \<in> set (aux_queue s) \<longleftrightarrow> now_serving s \<le> (myticket s) i"
    (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A then show ?B
    using assms apply clarsimp
    by (metis atLeastLessThan_iff atLeastLessThan_upt list.set_map rev_image_eqI)
next
  have "map (myticket s) (aux_queue s) = [now_serving s ..< next_ticket s]"
    using assms by simp
  moreover assume ?B
  then have "myticket s i \<in> set [now_serving s ..< next_ticket s]"
    using assms by simp
  moreover have "set [now_serving s ..< next_ticket s] \<subseteq> positive_nats"
    using assms by force
  moreover have "inj_img (myticket s) positive_nats"
    using assms by simp
  ultimately show ?A using helper_map_inj by metis
qed

lemma coupling_at_head:
  assumes "s \<in> tktlock_inv"
  shows "at_head i (aux_queue s) \<longleftrightarrow> now_serving s = (myticket s) i"
  using assms apply clarsimp
  by (smt (verit) Suc_le_lessD at_head_tl distinct_upt hd_in_set hd_upt inj_img_def list.map_disc_iff list.map_sel(1) list.sel(2) mem_Collect_eq nat_less_le upt_eq_Nil_conv)

lemma tktlock_inv_subgoals:
  assumes "s \<in> \<lbrace> \<acute>now_serving \<le> \<acute>next_ticket \<rbrace>"
      and "s \<in> \<lbrace> 1 \<le> \<acute>now_serving \<rbrace>"
      and "s \<in> \<lbrace> \<forall> i. \<acute>myticket i < \<acute>next_ticket \<rbrace>"
      and "s \<in> \<lbrace> bij_betw \<acute>myticket \<acute>contending_threads {\<acute>now_serving ..< \<acute>next_ticket} \<rbrace>"
      and "s \<in> \<lbrace> inj_img \<acute>myticket positive_nats \<rbrace>"
      and "s \<in> \<lbrace> map \<acute>myticket \<acute>aux_queue = [\<acute>now_serving ..< \<acute>next_ticket] \<rbrace>"
    shows "s \<in> tktlock_inv"
  using assms by force

method method_tktlock_inv = rule tktlock_inv_subgoals,
  goal_cases conc1 conc2 conc3 bij inj coup

(*------------------------------------------------------------------*)
lemma contending_threads_rewrite:
  "contending_threads s \<union> {i} = \<lbrace>\<acute>(\<noteq>) i \<longrightarrow> now_serving s \<le> \<acute>(myticket s)\<rbrace>" 
  by auto

lemma tktlock_used_tickets_rewrite:
  assumes "now_serving s \<le> next_ticket s"
    shows "{now_serving s ..< next_ticket s} \<union> {next_ticket s}
         = {now_serving s ..< Suc (next_ticket s)}"
  by (simp add: assms atLeastLessThanSuc)

lemma tktlock_enqueue_bij:
  assumes "myticket s i < now_serving s"
      and "bij_betw (myticket s) (contending_threads s) {now_serving s ..< next_ticket s}"
    shows "bij_betw ( (myticket s)(i := next_ticket s) )
                    ( contending_threads s \<union> {i} )
                    ( {now_serving s ..< next_ticket s} \<union> {next_ticket s} )"
  apply(rule bij_extension)
    using assms(1) apply auto[1]
   apply simp
  using assms(2) by blast

lemma tktlock_enqueue_inj:
  assumes "s \<in> tktlock_inv_concrete"
    shows "inj_img ((myticket s)(i := next_ticket s)) positive_nats"
proof-
  have "inj_img (myticket s) positive_nats"
    using assms by fastforce
  moreover have "\<forall> j. myticket s j \<noteq> next_ticket s"
    using assms nat_neq_iff by auto
  ultimately show ?thesis
    using inj_img_fun_upd_notin by metis
qed

lemma tktlock_rel_helper_1:
  assumes inv1: "now_serving s = myticket s i"
      and inv2: "myticket s i \<le> next_ticket s"
      and inv3: "Suc 0 \<le> myticket s i"
      and inv4: "\<forall> j. myticket s j < next_ticket s"
      and bij_old: "bij_betw (myticket s) \<lbrace> myticket s i \<le> \<acute>(myticket s) \<rbrace>
                                          { myticket s i ..< next_ticket s }"
    shows "bij_betw (myticket s) \<lbrace> Suc (myticket s i) \<le> \<acute>(myticket s) \<rbrace>
                                 { Suc (myticket s i) ..< next_ticket s }"
proof-
  have "\<lbrace>Suc (myticket s i) \<le> \<acute>(myticket s)\<rbrace> = {j. myticket s i \<le> myticket s j} - {i}"
  proof-
    have "i \<notin> {j. Suc (myticket s i) \<le> myticket s j}"
      by clarsimp
    moreover
    have "{j. Suc (myticket s i) \<le> myticket s j} \<subseteq> {j. myticket s i \<le> myticket s j}"
      by clarsimp
    moreover
    have "{j. myticket s i \<le> myticket s j} - {i} \<subseteq> {j. Suc (myticket s i) \<le> myticket s j}"
      by (clarsimp; metis CollectI Suc_leI assms(5) bij_betw_def inj_onD order_le_imp_less_or_eq)
    ultimately show ?thesis 
      using set_remove_one_element by blast
  qed
  moreover
  have "{Suc (myticket s i) ..< next_ticket s} = {myticket s i ..< next_ticket s} - {myticket s i}"
    by fastforce
  moreover
  have "i \<in> \<lbrace>myticket s i \<le> \<acute>(myticket s)\<rbrace>"
    by clarsimp
  hence "bij_betw (myticket s) ( {j. myticket s i \<le> myticket s j} - {i} )
                              ( {myticket s i ..< next_ticket s} - {myticket s i} )"
    using bij_old by (rule bij_remove_one)
  ultimately show ?thesis by clarsimp
qed

lemma tktlock_rel_helper_2:
  assumes pre1: "now_serving s = myticket s i"
      and pre2: "at_head i (aux_queue s)"
      and inv1: "s \<in> tktlock_inv_concrete"
      and inv2: "s \<in> tktlock_inv_coupling"
    shows "((\<lambda>s. s\<lparr>now_serving := now_serving s + 1\<rparr>) \<circ>> (\<lambda>s. s\<lparr>aux_queue := tl (aux_queue s)\<rparr>)) s
          \<in> tktlock_inv" (is "?s \<in> tktlock_inv")
proof method_tktlock_inv
  case conc1
  then show ?case
    using pre1 inv1 apply clarsimp
    using Suc_leI by fast
next
  case conc2
  then show ?case using inv1 by auto
next
  case conc3
  then show ?case using inv1 by auto
next
  case bij
  then show ?case unfolding contending_threads_def
    using pre1 inv1 tktlock_rel_helper_1 by auto
next
  case inj
  then show ?case using inv1 by auto
next
  case coup
  then show ?case using inv2 by (simp add: map_tl)
qed

(*------------------------------------------------------------------*)
subsection \<open>Theorems without Annotations\<close>

theorem tktlock_acq1:
  "rely: tktlock_rely i  guar: for_others tktlock_rely i
   inv:  tktlock_inv     code:
   { \<lbrace> \<acute>myticket i < \<acute>now_serving \<and> i \<notin> set \<acute>aux_queue \<rbrace> }
     Basic ((\<acute>myticket[i] \<leftarrow> \<acute>next_ticket) \<circ>>
            (\<acute>next_ticket \<leftarrow> \<acute>next_ticket + 1) \<circ>>
            (\<acute>aux_queue \<leftarrow> \<acute>aux_queue @ [i]))
   { \<lbrace> \<acute>now_serving \<le> \<acute>myticket i \<and> i \<in> set \<acute>aux_queue \<rbrace> }"
proof method_basic_inv
  case est_inv
  then show ?case
  proof (standard, standard, method_tktlock_inv)
    case (conc3 s)
    then show ?case
      using est_inv apply clarsimp
      using less_SucI by blast
  next
    case (bij s)
    then show ?case
      using tktlock_enqueue_bij by (simp add: atLeastLessThanSuc insert_Collect)
  next
    case (inj s)
    then show ?case
      using tktlock_enqueue_inj by simp
  next
    case (coup s)
    then show ?case by simp
  qed auto
qed auto

theorem tktlock_acq2:
  "rely: tktlock_rely i  guar: for_others tktlock_rely i
   inv:  tktlock_inv     code:
   { \<lbrace> \<acute>now_serving \<le> \<acute>myticket i \<and> i \<in> set \<acute>aux_queue \<rbrace> }
     WHILE \<acute>now_serving \<noteq> \<acute>myticket i DO SKIP OD
   { \<lbrace> \<acute>now_serving = \<acute>myticket i \<and> at_head i \<acute>aux_queue \<rbrace> }"
proof method_spinloop
  case stable_post
  then show ?case using stable_at_head by (clarsimp, blast)
next
  case est_post
  then show ?case using coupling_at_head by fastforce
qed auto

lemma assertion_decomp:
  "\<lbrakk> s \<in> \<lbrace> \<acute>p1 \<rbrace> ; s \<in> \<lbrace> \<acute>p2 \<rbrace> \<rbrakk> \<Longrightarrow> s \<in> \<lbrace> \<acute>p1 \<and> \<acute>p2 \<rbrace>"
  by fast

theorem tktlock_rel:
  "rely: tktlock_rely i  guar: for_others tktlock_rely i
   inv:  tktlock_inv     code:
    { \<lbrace> \<acute>now_serving = \<acute>myticket i \<and> at_head i \<acute>aux_queue \<rbrace> }
  Basic ((\<acute>now_serving \<leftarrow> \<acute>now_serving + 1) \<circ>>
         (\<acute>aux_queue \<leftarrow> tl \<acute>aux_queue))
    { \<lbrace> \<acute>myticket i < \<acute>now_serving \<and> i \<notin> set \<acute>aux_queue \<rbrace> }"
proof method_basic_inv
  case stab_pre
  then show ?case using stable_at_head by (clarsimp, blast)
next
  case stab_post
  then show ?case by fastforce
next
  case id_guar
  then show ?case by fastforce
next
  case est_inv
  then show ?case using tktlock_rel_helper_2 by fastforce
next
  case est_guar
  then show ?case
    unfolding tktlock_rely_def
  proof (standard, standard, standard, intro assertion_decomp, goal_cases)
    case (4 s j)
    then show ?case
      apply clarsimp
      by (metis CollectI Suc_leD Suc_leI inj_img_def le_neq_implies_less)
  next
    case (5 s j)
    then show ?case
      using coupling_at_head apply clarsimp
      by metis
  next
    case (6 s j)
    then have "\<not> at_head j (aux_queue s)"
      by blast
    then show ?case using queue_contract_tl by force
  qed simp_all
next
  case est_post
  then show ?case
    by (clarsimp, metis at_head_tl distinct_map distinct_upt)
qed

(*------------------------------------------------------------------*)
subsection \<open>Monolithic Theorem with Annotations\<close>

theorem tktlock_global:
  assumes "0 < n"
  shows "valid_multipar: annotated
  global_init: \<lbrace> \<acute>now_serving = 1 \<and> \<acute>next_ticket = 1 \<and> \<acute>myticket = (\<lambda>j. 0)
               \<and> \<acute>aux_queue = [] \<rbrace>
  global_rely: Id
    \<parallel> i < n @
  { \<lbrace> \<acute>myticket i < \<acute>now_serving \<and> i \<notin> set \<acute>aux_queue\<rbrace>, tktlock_rely i }

  FOREVER (
    \<lbrace> \<acute>myticket i < \<acute>now_serving \<and> i \<notin> set \<acute>aux_queue \<rbrace> / 
     \<langle>\<acute>myticket[i] := \<acute>next_ticket ;;
      \<acute>next_ticket := \<acute>next_ticket + 1 ;;
      \<acute>aux_queue := \<acute>aux_queue @ [i] \<rangle> .;
    \<lbrace> \<acute>now_serving \<le> \<acute>myticket i \<and> i \<in> set \<acute>aux_queue \<rbrace> 
     SPIN \<acute>now_serving \<noteq> \<acute>myticket i .;
    {\<lbrace> \<acute>now_serving = \<acute>myticket i \<and> at_head i \<acute>aux_queue \<rbrace>}
     \<langle>\<acute>now_serving := \<acute>now_serving + 1 ;;
      \<acute>aux_queue := tl \<acute>aux_queue \<rangle>a
  )

  \<sslash> tktlock_inv
  { for_others tktlock_rely i, {} }
  global_guar: UNIV global_post: \<lbrace> \<acute>aux_queue = [] \<rbrace>"

  apply (decompose_and_discharge helpers: Suc_le_eq simps: map_tl)
  using less_Suc_eq apply blast
  using atLeastLessThanSuc contending_threads_rewrite tktlock_enqueue_bij
  apply auto[1]
  apply (metis inj_img_fun_upd_notin less_not_refl)
  subgoal for i (* stability *)
    apply (auto simp add: stable_from_def)[1]
    by (metis (full_types) length_pos_if_in_set less_numeral_extra(3) list.size(3)
        suffix_bot.extremum_unique takeWhile_eq_Nil_iff)
  subgoal for i
    apply (simp add: subset_iff; mintro)
    apply auto  
    by (metis (lifting) hd_upt inj_img_def length_pos_if_in_set less_not_refl
        linorder_not_less list.map_sel(1) list.size(3) mem_Collect_eq not_less_eq)
  subgoal for i
    using stable_at_head apply ((simp add: subset_iff stable_from_def)?; mintro) apply auto?
    by (simp add: nat_less_le tktlock_rel_helper_1)
  apply (metis inj_img_def less_eq_Suc_le mem_Collect_eq nat_less_le)
  apply (smt (verit, best) atLeastLessThan_iff atLeastLessThan_upt hd_upt inj_img_def
         le_trans linorder_not_less list.map_disc_iff list.map_sel(1) list.set_sel(1)
         mem_Collect_eq not_less_eq_eq)
  apply (metis queue_contract_def queue_contract_tl)
  apply (metis suffix_tl tl_prefix_before)
  apply (metis prefix_order.dual_order.refl tl_suffix_after)
  apply (metis at_head_tl distinct_map distinct_upt)
  apply (auto simp add: subset_iff)[1]
  using bij_betwI' apply fastforce
  apply (smt (verit, best) atLeastLessThan_iff atLeastLessThan_upt hd_upt inj_img_def
         le_trans linorder_not_less list.map_disc_iff list.map_sel(1) list.set_sel(1)
         mem_Collect_eq not_less_eq_eq)
  apply (simp add: subset_iff;mintro, auto)[1]
  apply (metis (full_types) ComplI singletonD)
  apply (metis (full_types) ComplI singleton_iff)
  using assms by blast

end
