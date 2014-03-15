(*  Title:       Toy.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
    Author:      Peter Höfner
*)

header "Simple toy example"

theory Toy
imports Main AWN_Main Qmsg_Lifting
begin

subsection "Messages used in the protocol"

datatype msg =
    Pkt data ip
  | Newpkt data ip

instantiation msg :: msg
begin
definition newpkt_def [simp]: "newpkt \<equiv> \<lambda>(d,dip). Newpkt d dip"
definition eq_newpkt_def: "eq_newpkt m \<equiv> case m of Newpkt d dip  \<Rightarrow> True | _ \<Rightarrow> False" 

instance by intro_classes (simp add: eq_newpkt_def)
end

definition pkt :: "nat \<times> nat \<Rightarrow> msg"
where "pkt \<equiv> \<lambda>(no, sip). Pkt no sip"

lemma pkt_simp [simp]:
  "pkt(no, sip) = Pkt no sip"
  unfolding pkt_def by simp

lemma not_eq_newpkt_pkt [simp]: "\<not>eq_newpkt (Pkt no sip)"
  unfolding eq_newpkt_def by simp

subsection "Protocol model"

record state =
  ip    :: "nat"
  no    :: "nat"
  nhip  :: "nat"
  (* all locals *)
  msg    :: "msg"
  num    :: "nat"
  sip    :: "nat"

abbreviation toy_init :: "ip \<Rightarrow> state"
where "toy_init i \<equiv> \<lparr>
         ip = i,
         no = 0,
         nhip = i,

         msg    = (SOME x. True),
         num    = (SOME x. True),
         sip    = (SOME x. True)
       \<rparr>"

lemma some_neq_not_eq [simp]: "\<not>((SOME x :: nat. x \<noteq> i) = i)"
  by (subst some_eq_ex) (metis zero_neq_numeral)

definition clear_locals :: "state \<Rightarrow> state"
where "clear_locals \<xi> = \<xi> \<lparr>
    msg    := (SOME x. True),
    num    := (SOME x. True),
    sip    := (SOME x. True)
  \<rparr>"

lemma clear_locals_but_not_globals [simp]:
  "ip (clear_locals \<xi>) = ip \<xi>"
  "no (clear_locals \<xi>) = no \<xi>"
  "nhip (clear_locals \<xi>) = nhip \<xi>"
  unfolding clear_locals_def by auto

definition is_newpkt
where "is_newpkt \<xi> \<equiv> case msg \<xi> of
                       Newpkt data dip \<Rightarrow> { \<xi>\<lparr>num := data\<rparr> }
                     | _ \<Rightarrow> {}"

definition is_pkt
where "is_pkt \<xi> \<equiv> case msg \<xi> of
                    Pkt num' sip' \<Rightarrow> { \<xi>\<lparr> num := num', sip := sip' \<rparr> }
                  | _ \<Rightarrow> {}"

lemmas is_msg_defs =
  is_pkt_def is_newpkt_def

lemma is_msg_inv_ip [simp]:
  "\<xi>' \<in> is_pkt \<xi>    \<Longrightarrow> ip \<xi>' = ip \<xi>"
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> ip \<xi>' = ip \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

lemma is_msg_inv_sip [simp]:
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> sip \<xi>' = sip \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

lemma is_msg_inv_no [simp]:
  "\<xi>' \<in> is_pkt \<xi>    \<Longrightarrow> no \<xi>' = no \<xi>"
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> no \<xi>' = no \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

lemma is_msg_inv_nhip [simp]:
  "\<xi>' \<in> is_pkt \<xi>    \<Longrightarrow> nhip \<xi>' = nhip \<xi>"
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> nhip \<xi>' = nhip \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

lemma is_msg_inv_msg [simp]:
  "\<xi>' \<in> is_pkt \<xi>    \<Longrightarrow> msg \<xi>' = msg \<xi>"
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> msg \<xi>' = msg \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

datatype pseqp =
    PToy

fun nat_of_seqp :: "pseqp \<Rightarrow> nat"
where
  "nat_of_seqp PToy = 1"

instantiation "pseqp" :: ord
begin
definition less_eq_seqp [iff]: "l1 \<le> l2 = (nat_of_seqp l1 \<le> nat_of_seqp l2)"
definition less_seqp [iff]:    "l1 < l2 = (nat_of_seqp l1 < nat_of_seqp l2)"
instance ..
end

abbreviation Toy
where
  "Toy \<equiv> \<lambda>_. \<lbrakk>clear_locals\<rbrakk> call(PToy)"

fun \<Gamma>\<^sub>T\<^sub>O\<^sub>Y :: "(state, msg, pseqp, pseqp label) seqp_env"
where
  "\<Gamma>\<^sub>T\<^sub>O\<^sub>Y PToy = labelled PToy (
     receive(\<lambda>msg' \<xi>. \<xi> \<lparr> msg := msg' \<rparr>).
     \<lbrakk>\<xi>. \<xi> \<lparr>nhip := ip \<xi>\<rparr>\<rbrakk>
     (   \<langle>is_newpkt\<rangle> 
         (
             \<lbrakk>\<xi>. \<xi> \<lparr>no := max (no \<xi>) (num \<xi>)\<rparr>\<rbrakk>
             broadcast(\<lambda>\<xi>. pkt(no \<xi>, ip \<xi>)). Toy()
         )
       \<oplus> \<langle>is_pkt\<rangle>
       (
            \<langle>\<xi>. num \<xi> \<ge> no \<xi>\<rangle>
               \<lbrakk>\<xi>. \<xi> \<lparr>no := num \<xi>\<rparr>\<rbrakk>
               \<lbrakk>\<xi>. \<xi> \<lparr>nhip := sip \<xi>\<rparr>\<rbrakk>
               broadcast(\<lambda>\<xi>. pkt(no \<xi>, ip \<xi>)). Toy()
         \<oplus> \<langle>\<xi>. num \<xi> < no \<xi>\<rangle>
               Toy()
       )
     ))"

declare \<Gamma>\<^sub>T\<^sub>O\<^sub>Y.simps [simp del, code del]
lemmas \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_simps [simp, code] = \<Gamma>\<^sub>T\<^sub>O\<^sub>Y.simps [simplified]

fun \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton
where "\<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton PToy = seqp_skeleton (\<Gamma>\<^sub>T\<^sub>O\<^sub>Y PToy)"

lemma \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton_wf [simp]:
  "wellformed \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton"
  proof (rule, intro allI)
    fix pn pn'
    show "call(pn') \<notin> stermsl (\<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton pn)"
      by (cases pn) simp_all
  qed

declare \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton.simps [simp del, code del]
lemmas \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton_simps [simp, code] = \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton.simps [simplified \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_simps seqp_skeleton.simps]

lemma toy_proc_cases [dest]:
  fixes p pn
  assumes "p \<in> ctermsl (\<Gamma>\<^sub>T\<^sub>O\<^sub>Y pn)"
    shows "p \<in> ctermsl (\<Gamma>\<^sub>T\<^sub>O\<^sub>Y PToy)"
  using assms
  by (cases pn) simp_all

definition \<sigma>\<^sub>T\<^sub>O\<^sub>Y :: "ip \<Rightarrow> (state \<times> (state, msg, pseqp, pseqp label) seqp) set"
where "\<sigma>\<^sub>T\<^sub>O\<^sub>Y i \<equiv> {(toy_init i, \<Gamma>\<^sub>T\<^sub>O\<^sub>Y PToy)}"

abbreviation ptoy
  :: "ip \<Rightarrow> (state \<times> (state, msg, pseqp, pseqp label) seqp, msg seq_action) automaton"
where
  "ptoy i \<equiv> \<lparr> init = \<sigma>\<^sub>T\<^sub>O\<^sub>Y i, trans = seqp_sos \<Gamma>\<^sub>T\<^sub>O\<^sub>Y \<rparr>"

lemma toy_trans: "trans (ptoy i) = seqp_sos \<Gamma>\<^sub>T\<^sub>O\<^sub>Y"
  by simp

lemma toy_control_within [simp]: "control_within \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (init (ptoy i))"
  unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def by (rule control_withinI) (auto simp del: \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_simps)

lemma toy_wf [simp]:
  "wellformed \<Gamma>\<^sub>T\<^sub>O\<^sub>Y"
  proof (rule, intro allI)
    fix pn pn'
    show "call(pn') \<notin> stermsl (\<Gamma>\<^sub>T\<^sub>O\<^sub>Y pn)"
      by (cases pn) simp_all
  qed

lemmas toy_labels_not_empty [simp] = labels_not_empty [OF toy_wf]

lemma toy_ex_label [intro]: "\<exists>l. l\<in>labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p"
  by (metis toy_labels_not_empty all_not_in_conv)

lemma toy_ex_labelE [elim]:
  assumes "\<forall>l\<in>labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p. P l p"
      and "\<exists>p l. P l p \<Longrightarrow> Q"
    shows "Q"
 using assms by (metis toy_ex_label) 

lemma toy_simple_labels [simp]: "simple_labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y"
  proof
    fix pn p
    assume "p\<in>subterms(\<Gamma>\<^sub>T\<^sub>O\<^sub>Y pn)"
    thus "\<exists>!l. labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p = {l}"
    by (cases pn) (simp_all cong: seqp_congs | elim disjE)+
  qed

lemma \<sigma>\<^sub>T\<^sub>O\<^sub>Y_labels [simp]: "(\<xi>, p) \<in> \<sigma>\<^sub>T\<^sub>O\<^sub>Y i \<Longrightarrow>  labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p = {PToy-:0}"
  unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def by simp

text {* By default, we no longer let the simplifier descend into process terms. *}

declare seqp_congs [cong]

(* configure the inv_cterms tactic *)
declare
  \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_simps [cterms_env]
  toy_proc_cases [ctermsl_cases]
  seq_invariant_ctermsI [OF toy_wf toy_control_within toy_simple_labels toy_trans, cterms_intros]
  seq_step_invariant_ctermsI [OF toy_wf toy_control_within toy_simple_labels toy_trans, cterms_intros]

subsection "Define an open version of the protocol"

definition \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y :: "((ip \<Rightarrow> state) \<times> ((state, msg, pseqp, pseqp label) seqp)) set"
where "\<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y \<equiv> {(toy_init, \<Gamma>\<^sub>T\<^sub>O\<^sub>Y PToy)}"

abbreviation optoy
  :: "ip \<Rightarrow> ((ip \<Rightarrow> state) \<times> (state, msg, pseqp, pseqp label) seqp, msg seq_action) automaton"
where
  "optoy i \<equiv> \<lparr> init = \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y, trans = oseqp_sos \<Gamma>\<^sub>T\<^sub>O\<^sub>Y i \<rparr>"

lemma initiali_toy [intro!, simp]: "initiali i (init (optoy i)) (init (ptoy i))"
  unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y_def by rule simp_all

lemma oaodv_control_within [simp]: "control_within \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (init (optoy i))"
  unfolding \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y_def by (rule control_withinI) (auto simp del: \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_simps)

lemma \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y_labels [simp]: "(\<sigma>, p) \<in> \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y \<Longrightarrow>  labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p = {PToy-:0}"
  unfolding \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y_def by simp

lemma otoy_trans: "trans (optoy i) = oseqp_sos \<Gamma>\<^sub>T\<^sub>O\<^sub>Y i"
  by simp

(* configure the inv_cterms tactic *)
declare
  oseq_invariant_ctermsI [OF toy_wf oaodv_control_within toy_simple_labels otoy_trans, cterms_intros]
  oseq_step_invariant_ctermsI [OF toy_wf oaodv_control_within toy_simple_labels otoy_trans, cterms_intros]

subsection "Predicates"

definition msg_sender :: "msg \<Rightarrow> ip"
where "msg_sender m \<equiv> case m of Pkt _ ipc \<Rightarrow> ipc"

lemma msg_sender_simps [simp]:
  "\<And>d dip sip. msg_sender (Pkt d sip) = sip"
  unfolding msg_sender_def by simp_all

abbreviation not_Pkt :: "msg \<Rightarrow> bool"
where "not_Pkt m \<equiv> case m of Pkt _ _ \<Rightarrow> False | _ \<Rightarrow> True"

definition nos_increase :: "state \<Rightarrow> state \<Rightarrow> bool"
where "nos_increase \<xi> \<xi>' \<equiv> (no \<xi> \<le> no \<xi>')"

definition msg_num_ok :: "(ip \<Rightarrow> state) \<Rightarrow> msg \<Rightarrow> bool"
where "msg_num_ok \<sigma> m \<equiv> case m of Pkt num' sip' \<Rightarrow> num' \<le> no (\<sigma> sip') | _ \<Rightarrow> True"

lemma msg_num_okI [intro]:
  assumes "\<And>num' sip'. m = Pkt num' sip' \<Longrightarrow> num' \<le> no (\<sigma> sip')"
    shows "msg_num_ok \<sigma> m"
  using assms unfolding msg_num_ok_def
  by (auto split: msg.split)

lemma msg_num_ok_Pkt [simp]:
  "msg_num_ok \<sigma> (Pkt data src) = (data \<le> no (\<sigma> src))"
  unfolding msg_num_ok_def by simp

lemma msg_num_ok_pkt [simp]:
  "msg_num_ok \<sigma> (pkt(data, src)) = (data \<le> no (\<sigma> src))"
  unfolding msg_num_ok_def by simp

lemma msg_num_ok_Newpkt [simp]:
  "msg_num_ok \<sigma> (Newpkt data dst)"
  unfolding msg_num_ok_def by simp

lemma msg_num_ok_newpkt [simp]:
  "msg_num_ok \<sigma> (newpkt(data, dst))"
  unfolding msg_num_ok_def by simp

subsection "Sequential Invariants"

lemma seq_no_leq_num:
  "ptoy i \<TTurnstile> onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<xi>, l). l\<in>{PToy-:7..PToy-:9} \<longrightarrow> no \<xi> \<le> num \<xi>)"
  by inv_cterms

lemma seq_nos_increases:
  "ptoy i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>((\<xi>, _), _, (\<xi>', _)). nos_increase \<xi> \<xi>')"
  unfolding nos_increase_def
  proof -
    show "ptoy i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>((\<xi>, _), _, (\<xi>', _)). no \<xi> \<le> no \<xi>')"
      by (inv_cterms inv add: onl_invariant_sterms [OF toy_wf seq_no_leq_num])
  qed

lemma seq_nos_increases':
  "ptoy i \<TTurnstile>\<^sub>A (\<lambda>((\<xi>, _), _, (\<xi>', _)). nos_increase \<xi> \<xi>')"
  by (rule step_invariant_weakenE [OF seq_nos_increases]) (auto dest!: onllD)

lemma sender_ip_valid:
  "ptoy i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>((\<xi>, _), a, _). anycast (\<lambda>m. msg_sender m = ip \<xi>) a)"
  by inv_cterms

lemma ip_constant:
  "ptoy i \<TTurnstile> onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<xi>, _). ip \<xi> = i)"
  by inv_cterms (simp add: \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def)

lemma nhip_eq_ip:
  "ptoy i \<TTurnstile> onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<xi>, l). l\<in>{PToy-:2..PToy-:8} \<longrightarrow> nhip \<xi> = ip \<xi>)"
  by inv_cterms

lemma seq_msg_num_ok:
  "ptoy i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>((\<xi>, _), a, _).
                anycast (\<lambda>m. case m of Pkt num' sip' \<Rightarrow> num' = no \<xi> \<and> sip' = i | _ \<Rightarrow> True) a)"
  by (inv_cterms inv add: onl_invariant_sterms [OF toy_wf ip_constant])

lemma nhip_eq_i:
  "ptoy i \<TTurnstile> onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<xi>, l). l\<in>{PToy-:2..PToy-:8} \<longrightarrow> nhip \<xi> = i)"
  proof (rule invariant_arbitraryI, clarify intro!: onlI impI)
    fix \<xi> p l n
    assume "(\<xi>, p) \<in> reachable (ptoy i) TT"
       and "l \<in> labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p"
       and "l \<in> {PToy-:2..PToy-:8}"
    from this(1-3) have "nhip \<xi> = ip \<xi>"
      by - (drule invariantD [OF nhip_eq_ip], auto)
    moreover with `(\<xi>, p) \<in> reachable (ptoy i) TT` and `l \<in> labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p` have "ip \<xi> = i"
      by (auto dest: invariantD [OF ip_constant])
    ultimately show "nhip \<xi> = i"
      by simp
  qed

subsection "Global Invariants"

lemma nos_increaseD [dest]:
  assumes "nos_increase \<xi> \<xi>'"
    shows "no \<xi> \<le> no \<xi>'"
  using assms unfolding nos_increase_def .

lemma nos_increase_simp [simp]:
  "nos_increase \<xi> \<xi>' = (no \<xi> \<le> no \<xi>')"
  using assms unfolding nos_increase_def ..

lemmas oseq_nos_increases =
  open_seq_step_invariant [OF seq_nos_increases initiali_toy otoy_trans toy_trans,
                           simplified seqll_onll_swap]

lemmas oseq_no_leq_num =
  open_seq_invariant [OF seq_no_leq_num initiali_toy otoy_trans toy_trans,
                      simplified seql_onl_swap]

lemma all_nos_increase:
  shows "optoy i \<Turnstile>\<^sub>A (otherwith nos_increase {i} S,
                      other nos_increase {i} \<rightarrow>)
                       onll \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>((\<sigma>, _), a, (\<sigma>', _)). (\<forall>j. nos_increase (\<sigma> j) (\<sigma>' j)))"
  proof -
    have *: "\<And>\<sigma> \<sigma>' a. \<lbrakk> otherwith nos_increase {i} S \<sigma> \<sigma>' a; no (\<sigma> i) \<le> no (\<sigma>' i) \<rbrakk>
                       \<Longrightarrow> \<forall>j. no (\<sigma> j) \<le> no (\<sigma>' j)"
      by (auto dest!: otherwith_syncD)
    show ?thesis
      by (inv_cterms
            inv add: oseq_step_invariant_sterms [OF oseq_nos_increases [THEN oinvariant_step_anyact]
                                                                                   toy_wf otoy_trans]
            simp add: seqllsimp) (auto elim!: *)
  qed

lemma oreceived_msg_inv:
  assumes other: "\<And>\<sigma> \<sigma>' m. \<lbrakk> P \<sigma> m; other Q {i} \<sigma> \<sigma>' \<rbrakk> \<Longrightarrow> P \<sigma>' m"
      and local: "\<And>\<sigma> m. P \<sigma> m \<Longrightarrow> P (\<sigma>(i := \<sigma> i\<lparr>msg := m\<rparr>)) m"
    shows "optoy i \<Turnstile> (otherwith Q {i} (orecvmsg P), other Q {i} \<rightarrow>)
                       onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<sigma>, l). l \<in> {PToy-:1} \<longrightarrow> P \<sigma> (msg (\<sigma> i)))"
  proof (inv_cterms, intro impI)
    fix \<sigma> \<sigma>' l
    assume "l = PToy-:1 \<longrightarrow> P \<sigma> (msg (\<sigma> i))"
       and "l = PToy-:1"
       and "other Q {i} \<sigma> \<sigma>'"
    from this(1-2) have "P \<sigma> (msg (\<sigma> i))" ..
    hence "P \<sigma>' (msg (\<sigma> i))" using `other Q {i} \<sigma> \<sigma>'`
      by (rule other)
    moreover from `other Q {i} \<sigma> \<sigma>'` have "\<sigma>' i = \<sigma> i" ..
    ultimately show "P \<sigma>' (msg (\<sigma>' i))" by simp
  next
    fix \<sigma> \<sigma>' msg
    assume "otherwith Q {i} (orecvmsg P) \<sigma> \<sigma>' (receive msg)"
       and "\<sigma>' i = \<sigma> i\<lparr>msg := msg\<rparr>"
    from this(1) have "P \<sigma> msg"
                 and "\<forall>j. j\<noteq>i \<longrightarrow> Q (\<sigma> j) (\<sigma>' j)" by auto
    from this(1) have "P (\<sigma>(i := \<sigma> i\<lparr>msg := msg\<rparr>)) msg" by (rule local)
    thus "P \<sigma>' msg"
    proof (rule other)
      from `\<sigma>' i = \<sigma> i\<lparr>msg := msg\<rparr>` and `\<forall>j. j\<noteq>i \<longrightarrow> Q (\<sigma> j) (\<sigma>' j)`
        show "other Q {i} (\<sigma>(i := \<sigma> i\<lparr>msg := msg\<rparr>)) \<sigma>'"
          by - (rule otherI, auto)
    qed
  qed

lemma msg_num_ok_other_nos_increase [elim]:
  assumes "msg_num_ok \<sigma> m"
      and "other nos_increase {i} \<sigma> \<sigma>'"
    shows "msg_num_ok \<sigma>' m"
  proof (cases m)
    fix num sip
    assume "m = Pkt num sip"
    with `msg_num_ok \<sigma> m` have "num \<le> no (\<sigma> sip)" by simp
    also from `other nos_increase {i} \<sigma> \<sigma>'` have "no (\<sigma> sip) \<le> no (\<sigma>' sip)"
      by (rule otherE) (metis eq_iff nos_increaseD)
    finally have "num \<le> no (\<sigma>' sip)" .
    with `m = Pkt num sip` show ?thesis
      by simp
  qed simp

lemma msg_num_ok_no_leq_no [simp, elim]:
  assumes "msg_num_ok \<sigma> m"
      and "\<forall>j. no (\<sigma> j) \<le> no (\<sigma>' j)"
    shows "msg_num_ok \<sigma>' m"
  using assms(1) proof (cases m)
    fix num sip
    assume "m = Pkt num sip"
    with `msg_num_ok \<sigma> m` have "num \<le> no (\<sigma> sip)" by simp
    also from `\<forall>j. no (\<sigma> j) \<le> no (\<sigma>' j)` have "no (\<sigma> sip) \<le> no (\<sigma>' sip)"
      by simp
    finally have "num \<le> no (\<sigma>' sip)" .
    with `m = Pkt num sip` show ?thesis
      by simp
  qed (simp add: assms(1))

lemma oreceived_msg_num_ok:
  "optoy i \<Turnstile> (otherwith nos_increase {i} (orecvmsg msg_num_ok),
               other nos_increase {i} \<rightarrow>)
              onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<sigma>, l). l\<in>{PToy-:1..} \<longrightarrow> msg_num_ok \<sigma> (msg (\<sigma> i)))"
  (is "_ \<Turnstile> (?S, ?U \<rightarrow>) _")
  proof (inv_cterms inv add: oseq_step_invariant_sterms [OF all_nos_increase toy_wf otoy_trans],
         intro impI, elim impE)
    fix \<sigma> \<sigma>'
    assume "msg_num_ok \<sigma> (msg (\<sigma> i))"
       and "other nos_increase {i} \<sigma> \<sigma>'"
    moreover from this(2) have "msg (\<sigma>' i) = msg (\<sigma> i)"
      by (clarsimp elim!: otherE)
    ultimately show "msg_num_ok \<sigma>' (msg (\<sigma>' i))"
      by (auto)
  next
    fix p l \<sigma> a q l' \<sigma>' pp p' m
    assume a1: "(\<sigma>', p') \<in> oreachable (optoy i) ?S ?U"
       and a2: "PToy-:1 \<in> labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p'"
       and a3: "\<sigma>' i = \<sigma> i\<lparr>msg := m\<rparr>"
    have inv: "optoy i \<Turnstile> (?S, ?U \<rightarrow>) onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<sigma>, l). l \<in> {PToy-:1} \<longrightarrow> msg_num_ok \<sigma> (msg (\<sigma> i)))"
    proof (rule oreceived_msg_inv)
      fix \<sigma> \<sigma>' m
      assume "msg_num_ok \<sigma> m"
         and "other nos_increase {i} \<sigma> \<sigma>'"
      thus "msg_num_ok \<sigma>' m" ..
    next
      fix \<sigma> m
      assume "msg_num_ok \<sigma> m"
      thus "msg_num_ok (\<sigma>(i := \<sigma> i\<lparr>msg := m\<rparr>)) m"
        by (cases m) auto
    qed
    from a1 a2 a3 show "msg_num_ok \<sigma>' m"
      by (clarsimp dest!: oinvariantD [OF inv] onlD)
  qed simp

lemma is_pkt_handler_num_leq_no:
  shows "optoy i \<Turnstile> (otherwith nos_increase {i} (orecvmsg msg_num_ok),
                      other nos_increase {i} \<rightarrow>)
                    onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<sigma>, l). l\<in>{PToy-:6..PToy-:10} \<longrightarrow> num (\<sigma> i) \<le> no (\<sigma> (sip (\<sigma> i))))"
  proof -
    { fix \<sigma> \<sigma>'
      assume "\<forall>j. no (\<sigma> j) \<le> no (\<sigma>' j)"
         and "num (\<sigma> i) \<le> no (\<sigma> (sip (\<sigma> i)))"
      have "num (\<sigma> i) \<le> no (\<sigma>' (sip (\<sigma> i)))"
      proof -
        note `num (\<sigma> i) \<le> no (\<sigma> (sip (\<sigma> i)))`
        also from `\<forall>j. no (\<sigma> j) \<le> no (\<sigma>' j)` have "no (\<sigma> (sip (\<sigma> i))) \<le> no (\<sigma>' (sip (\<sigma> i)))"
          by auto
        finally show ?thesis .
      qed
    } note solve_step = this
    show ?thesis
    proof (inv_cterms inv add: oseq_step_invariant_sterms [OF all_nos_increase toy_wf otoy_trans]
                               onl_oinvariant_sterms [OF toy_wf oreceived_msg_num_ok]
                        solve: solve_step, intro impI, elim impE)
      fix \<sigma> \<sigma>'
      assume *: "num (\<sigma> i) \<le> no (\<sigma> (sip (\<sigma> i)))"
         and "other nos_increase {i} \<sigma> \<sigma>'"
      from this(2) obtain "\<forall>i\<in>{i}. \<sigma>' i = \<sigma> i"
                      and "\<forall>j. j \<notin> {i} \<longrightarrow> nos_increase (\<sigma> j) (\<sigma>' j)" ..
      show "num (\<sigma>' i) \<le> no (\<sigma>' (sip (\<sigma>' i)))"      
      proof (cases "sip (\<sigma> i) = i")
        assume "sip (\<sigma> i) = i"
        with * `\<forall>i\<in>{i}. \<sigma>' i = \<sigma> i`
        show ?thesis by simp
      next
        assume "sip (\<sigma> i) \<noteq> i"
        with `\<forall>j. j \<notin> {i} \<longrightarrow> nos_increase (\<sigma> j) (\<sigma>' j)`
          have "no (\<sigma> (sip (\<sigma> i))) \<le> no (\<sigma>' (sip (\<sigma> i)))" by simp
        with * `\<forall>i\<in>{i}. \<sigma>' i = \<sigma> i`
        show ?thesis by simp
      qed
    next
      fix p l \<sigma> a q l' \<sigma>' pp p'
      assume "msg_num_ok \<sigma> (msg (\<sigma> i))"
         and "\<forall>j. no (\<sigma> j) \<le> no (\<sigma>' j)"
         and "\<sigma>' i \<in> is_pkt (\<sigma> i)"
      show "num (\<sigma>' i) \<le> no (\<sigma>' (sip (\<sigma>' i)))"
      proof (cases "msg (\<sigma> i)")
        fix num' sip'
        assume "msg (\<sigma> i) = Pkt num' sip'"
        with `\<sigma>' i \<in> is_pkt (\<sigma> i)` obtain "num (\<sigma>' i) = num'"
                                      and "sip (\<sigma>' i) = sip'"
          unfolding is_pkt_def by auto
        with `msg (\<sigma> i) = Pkt num' sip'` and `msg_num_ok \<sigma> (msg (\<sigma> i))`
          have "num (\<sigma>' i) \<le> no (\<sigma> (sip (\<sigma>' i)))"
            by simp
        also from `\<forall>j. no (\<sigma> j) \<le> no (\<sigma>' j)` have "no (\<sigma> (sip (\<sigma>' i))) \<le> no (\<sigma>' (sip (\<sigma>' i)))" ..
        finally show ?thesis .
      next
        fix num' sip'
        assume "msg (\<sigma> i) = Newpkt num' sip'"
        with `\<sigma>' i \<in> is_pkt (\<sigma> i)` have False
          unfolding is_pkt_def by simp
        thus ?thesis ..
      qed
    qed
  qed

lemmas oseq_ip_constant =
  open_seq_invariant [OF ip_constant initiali_toy otoy_trans toy_trans,
                      simplified seql_onl_swap]

lemmas oseq_nhip_eq_i =
  open_seq_invariant [OF nhip_eq_i initiali_toy otoy_trans toy_trans,
                      simplified seql_onl_swap]
  
lemmas oseq_nhip_eq_ip =
  open_seq_invariant [OF nhip_eq_ip initiali_toy otoy_trans toy_trans,
                      simplified seql_onl_swap]

lemma oseq_bigger_than_next:
  shows "optoy i \<Turnstile> (otherwith nos_increase {i} (orecvmsg msg_num_ok),
                      other nos_increase {i} \<rightarrow>) global (\<lambda>\<sigma>. no (\<sigma> i) \<le> no (\<sigma> (nhip (\<sigma> i))))"
    (is "_ \<Turnstile> (?S, ?U \<rightarrow>) ?P")
  proof -
    have nhipinv: "optoy i \<Turnstile> (?S, ?U \<rightarrow>)
                              onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<sigma>, l). l\<in>{PToy-:2..PToy-:8}
                                                    \<longrightarrow> nhip (\<sigma> i) = ip (\<sigma> i))"
      by (rule oinvariant_weakenE [OF oseq_nhip_eq_ip]) (auto simp: seqlsimp)
    have ipinv: "optoy i \<Turnstile> (?S, ?U \<rightarrow>) onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<sigma>, l). ip (\<sigma> i) = i)"
      by (rule oinvariant_weakenE [OF oseq_ip_constant]) (auto simp: seqlsimp)
    { fix \<sigma> \<sigma>' a
      assume "no (\<sigma> i) \<le> no (\<sigma> (nhip (\<sigma> i)))"
         and "\<forall>j. nos_increase (\<sigma> j) (\<sigma>' j)"
      note this(1)
      also from `\<forall>j. nos_increase (\<sigma> j) (\<sigma>' j)` have "no (\<sigma> (nhip (\<sigma> i))) \<le> no (\<sigma>' (nhip (\<sigma> i)))"
        by auto
      finally have "no (\<sigma> i) \<le> no (\<sigma>' (nhip (\<sigma> i)))" ..
    } note * = this
    have "optoy i \<Turnstile> (otherwith nos_increase {i} (orecvmsg msg_num_ok),
                      other nos_increase {i} \<rightarrow>)
                     onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<sigma>, l). no (\<sigma> i) \<le> no (\<sigma> (nhip (\<sigma> i))))"
    proof (inv_cterms
             inv add: onl_oinvariant_sterms [OF toy_wf oseq_no_leq_num [THEN oinvariant_anyact]]
                      oseq_step_invariant_sterms [OF all_nos_increase toy_wf otoy_trans]
                      onl_oinvariant_sterms [OF toy_wf is_pkt_handler_num_leq_no]
                      onl_oinvariant_sterms [OF toy_wf nhipinv]
                      onl_oinvariant_sterms [OF toy_wf ipinv]
             simp add: seqlsimp seqllsimp
             simp del: nos_increase_simp
                solve: *)
      fix \<sigma> p l
      assume "(\<sigma>, p) \<in> \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y"
      thus "no (\<sigma> i) \<le> no (\<sigma> (nhip (\<sigma> i)))"
        by (simp add: \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y_def)
    next
      fix \<sigma> \<sigma>' p l
      assume or: "(\<sigma>, p) \<in> oreachable (optoy i) ?S ?U"
         and "l \<in> labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p"
         and "no (\<sigma> i) \<le> no (\<sigma> (nhip (\<sigma> i)))"
         and "other nos_increase {i} \<sigma> \<sigma>'"
      show "no (\<sigma>' i) \<le> no (\<sigma>' (nhip (\<sigma>' i)))"
      proof (cases "nhip (\<sigma>' i) = i")
        assume "nhip (\<sigma>' i) = i"
        with `no (\<sigma> i) \<le> no (\<sigma> (nhip (\<sigma> i)))` show ?thesis
          by simp
      next
        assume "nhip (\<sigma>' i) \<noteq> i"
        moreover from `other nos_increase {i} \<sigma> \<sigma>'` [THEN other_localD] have "\<sigma>' i = \<sigma> i"
          by simp
        ultimately have "no (\<sigma> (nhip (\<sigma> i))) \<le> no (\<sigma>' (nhip (\<sigma>' i)))"
          using `other nos_increase {i} \<sigma> \<sigma>'` and `\<sigma>' i = \<sigma> i` by (auto)
        with `no (\<sigma> i) \<le> no (\<sigma> (nhip (\<sigma> i)))` and `\<sigma>' i = \<sigma> i` show ?thesis
          by simp
      qed
    next
      fix p l \<sigma> a q l' \<sigma>' pp p'
      assume "no (\<sigma> i) \<le> num (\<sigma> i)"
         and "num (\<sigma> i) \<le> no (\<sigma> (sip (\<sigma> i)))"
         and "\<forall>j. nos_increase (\<sigma> j) (\<sigma>' j)"
      from this(1-2) have "no (\<sigma> i) \<le> no (\<sigma> (sip (\<sigma> i)))"
        by (rule le_trans)
      also from `\<forall>j. nos_increase (\<sigma> j) (\<sigma>' j)`
        have "no (\<sigma> (sip (\<sigma> i))) \<le> no (\<sigma>' (sip (\<sigma> i)))"
          by auto
      finally show "no (\<sigma> i) \<le> no (\<sigma>' (sip (\<sigma> i)))" ..
    qed
    thus ?thesis
      by (rule oinvariant_weakenE)
         (auto simp: onl_def)
  qed

lemma anycast_weakenE [elim]:
  assumes "anycast P a"
      and "\<And>m. P m \<Longrightarrow> Q m"
  shows "anycast Q a"
  using assms unfolding anycast_def
  by (auto split: seq_action.split)

lemma oseq_msg_num_ok:
  "optoy i \<Turnstile>\<^sub>A (act TT, other U {i} \<rightarrow>) globala (\<lambda>(\<sigma>, a, _). anycast (msg_num_ok \<sigma>) a)"
  by (rule ostep_invariant_weakenE [OF open_seq_step_invariant
            [OF seq_msg_num_ok initiali_toy otoy_trans toy_trans, simplified seql_onl_swap]])
     (auto simp: seqllsimp dest!: onllD elim!: anycast_weakenE intro!: msg_num_okI)

subsection "Lifting"

lemma opar_bigger_than_next:
  shows "optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile> (otherwith nos_increase {i} (orecvmsg msg_num_ok),
                      other nos_increase {i} \<rightarrow>) global (\<lambda>\<sigma>. no (\<sigma> i) \<le> no (\<sigma> (nhip (\<sigma> i))))"
  proof (rule lift_into_qmsg [OF oseq_bigger_than_next])
    fix \<sigma> \<sigma>' m
    assume "\<forall>j. nos_increase (\<sigma> j) (\<sigma>' j)"
       and "msg_num_ok \<sigma> m"
    from this(2) show "msg_num_ok \<sigma>' m"
    proof (cases m, simp only: msg_num_ok_Pkt)
      fix num' sip'
      assume "num' \<le> no (\<sigma> sip')"
      also from `\<forall>j. nos_increase (\<sigma> j) (\<sigma>' j)` have "no (\<sigma> sip') \<le> no (\<sigma>' sip')"
        by simp
      finally show "num' \<le> no (\<sigma>' sip')" .
    qed simp
  next
    show "optoy i \<Turnstile>\<^sub>A (otherwith nos_increase {i} (orecvmsg msg_num_ok), other nos_increase {i} \<rightarrow>)
                      globala (\<lambda>(\<sigma>, _, \<sigma>'). nos_increase (\<sigma> i) (\<sigma>' i))"
      by (rule ostep_invariant_weakenE [OF open_seq_step_invariant
                                         [OF seq_nos_increases initiali_toy otoy_trans toy_trans]])
         (auto simp: seqllsimp dest!: onllD)
  qed simp

lemma onode_bigger_than_next:
  "\<langle>i : optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<^sub>i\<rangle>\<^sub>o
     \<Turnstile> (otherwith nos_increase {i} (oarrivemsg msg_num_ok), other nos_increase {i} \<rightarrow>)
        global (\<lambda>\<sigma>. no (\<sigma> i) \<le> no (\<sigma> (nhip (\<sigma> i))))"
  by (rule node_lift [OF opar_bigger_than_next])

lemma node_local_nos_increase:
  "\<langle>i : optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg (\<lambda>_ _. True) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                                     globala (\<lambda>(\<sigma>, _, \<sigma>'). nos_increase (\<sigma> i) (\<sigma>' i))"
  proof (rule node_lift_step_statelessassm)
    have "optoy i \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_ _. True) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                      globala (\<lambda>(\<sigma>, _, \<sigma>'). nos_increase (\<sigma> i) (\<sigma>' i))"
      by (rule ostep_invariant_weakenE [OF oseq_nos_increases])
         (auto simp: seqllsimp dest!: onllD)
    thus "optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_ _. True) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                                globala (\<lambda>(\<sigma>, _, \<sigma>'). nos_increase (\<sigma> i) (\<sigma>' i))"
      by (rule lift_step_into_qmsg_statelessassm) auto
  qed simp

lemma opnet_bigger_than_next:
  "opnet (\<lambda>i. optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg) n
     \<Turnstile> (otherwith nos_increase (net_tree_ips n) (oarrivemsg msg_num_ok),
         other nos_increase (net_tree_ips n) \<rightarrow>)
        global (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips n. no (\<sigma> i) \<le> no (\<sigma> (nhip (\<sigma> i))))"
  proof (rule pnet_lift [OF onode_bigger_than_next])
    fix i R\<^sub>i
    have "\<langle>i : optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg msg_num_ok \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                                            globala (\<lambda>(\<sigma>, a, _). castmsg (msg_num_ok \<sigma>) a)"
    proof (rule node_lift_anycast_statelessassm)
      have "optoy i \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_ _. True) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                        globala (\<lambda>(\<sigma>, a, _). anycast (msg_num_ok \<sigma>) a)"
        by (rule ostep_invariant_weakenE [OF oseq_msg_num_ok]) auto
      hence "optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_ _. True) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                                   globala (\<lambda>(\<sigma>, a, _). anycast (msg_num_ok \<sigma>) a)"
        by (rule lift_step_into_qmsg_statelessassm) auto
      thus "optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg msg_num_ok \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                                  globala (\<lambda>(\<sigma>, a, _). anycast (msg_num_ok \<sigma>) a)"
        by (rule ostep_invariant_weakenE) auto
    qed
    thus "\<langle>i : optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg msg_num_ok \<sigma>, other nos_increase {i} \<rightarrow>)
                                            globala (\<lambda>(\<sigma>, a, _). castmsg (msg_num_ok \<sigma>) a)"
      by (rule ostep_invariant_weakenE) auto
  next
    fix i R\<^sub>i
    show "\<langle>i : optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg msg_num_ok \<sigma>,
                                            other nos_increase {i} \<rightarrow>)
             globala (\<lambda>(\<sigma>, a, \<sigma>'). a \<noteq> \<tau> \<and> (\<forall>i d. a \<noteq> i:deliver(d)) \<longrightarrow> nos_increase (\<sigma> i) (\<sigma>' i))"
      by (rule ostep_invariant_weakenE [OF node_local_nos_increase]) auto
  next
    fix i R
    show "\<langle>i : optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg msg_num_ok \<sigma>,
                                           other nos_increase {i} \<rightarrow>)
             globala (\<lambda>(\<sigma>, a, \<sigma>'). a = \<tau> \<or> (\<exists>d. a = i:deliver(d)) \<longrightarrow> nos_increase (\<sigma> i) (\<sigma>' i))"
      by (rule ostep_invariant_weakenE [OF node_local_nos_increase]) auto
  qed simp_all

lemma ocnet_bigger_than_next:
  "oclosed (opnet (\<lambda>i. optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg) n)
     \<Turnstile> (\<lambda>_ _ _. True, other nos_increase (net_tree_ips n) \<rightarrow>)
        global (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips n. no (\<sigma> i) \<le> no (\<sigma> (nhip (\<sigma> i))))"
  proof (rule inclosed_closed)
    show "opnet (\<lambda>i. optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg) n
            \<Turnstile> (otherwith op = (net_tree_ips n) inoclosed, other nos_increase (net_tree_ips n) \<rightarrow>)
               global (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips n. no (\<sigma> i) \<le> no (\<sigma> (nhip (\<sigma> i))))"
    proof (rule oinvariant_weakenE [OF opnet_bigger_than_next])
      fix s s':: "nat \<Rightarrow> state" and a :: "msg node_action"
      assume "otherwith op = (net_tree_ips n) inoclosed s s' a"
      thus "otherwith nos_increase (net_tree_ips n) (oarrivemsg msg_num_ok) s s' a"
      proof (rule otherwithE, intro otherwithI)
        assume "inoclosed s a"
           and "\<forall>j. j \<notin> net_tree_ips n \<longrightarrow> s j = s' j"
           and "otherwith (op=) (net_tree_ips n) inoclosed s s' a"
        thus "oarrivemsg msg_num_ok s a"
          by (cases a) auto
      qed auto
    qed simp
  qed

subsection "Transfer"

definition
  initmissing :: "(nat \<Rightarrow> state option) \<times> 'a \<Rightarrow> (nat \<Rightarrow> state) \<times> 'a"
where
  "initmissing \<sigma> = (\<lambda>i. case (fst \<sigma>) i of None \<Rightarrow> toy_init i | Some s \<Rightarrow> s, snd \<sigma>)"

lemma not_in_net_ips_fst_init_missing [simp]:
  assumes "i \<notin> net_ips \<sigma>"
    shows "fst (initmissing (netgmap fst \<sigma>)) i = toy_init i"
  using assms unfolding initmissing_def by simp

lemma fst_initmissing_netgmap_pair_fst [simp]:
  "fst (initmissing (netgmap (\<lambda>(p, q). (fst (id p), snd (id p), q)) s))
                                               = fst (initmissing (netgmap fst s))"
  unfolding initmissing_def by auto

interpretation toy_openproc: openproc ptoy optoy id
  where "toy_openproc.initmissing = initmissing"
  proof -
    show "openproc ptoy optoy id"
    proof unfold_locales
      fix i :: ip
      have "{(\<sigma>, \<zeta>). (\<sigma> i, \<zeta>) \<in> \<sigma>\<^sub>T\<^sub>O\<^sub>Y i \<and> (\<forall>j. j \<noteq> i \<longrightarrow> \<sigma> j \<in> fst ` \<sigma>\<^sub>T\<^sub>O\<^sub>Y j)} \<subseteq> \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y"
        unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y_def
        proof (rule equalityD1)
          show "\<And>f p. {(\<sigma>, \<zeta>). (\<sigma> i, \<zeta>) \<in> {(f i, p)} \<and> (\<forall>j. j \<noteq> i
                      \<longrightarrow> \<sigma> j \<in> fst ` {(f j, p)})} = {(f, p)}"
            by (rule set_eqI) auto
        qed
      thus "{ (\<sigma>, \<zeta>) |\<sigma> \<zeta> s. s \<in> init (ptoy i)
                             \<and> (\<sigma> i, \<zeta>) = id s
                             \<and> (\<forall>j. j\<noteq>i \<longrightarrow> \<sigma> j \<in> (fst o id) ` init (ptoy j)) } \<subseteq> init (optoy i)"
        by simp
    next
      show "\<forall>j. init (ptoy j) \<noteq> {}"
        unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def by simp
    next
      fix i s a s' \<sigma> \<sigma>'
      assume "\<sigma> i = fst (id s)"
         and "\<sigma>' i = fst (id s')"
         and "(s, a, s') \<in> trans (ptoy i)"
      then obtain q q' where "s = (\<sigma> i, q)"
                         and "s' = (\<sigma>' i, q')"
                         and "((\<sigma> i, q), a, (\<sigma>' i, q')) \<in> trans (ptoy i)" 
         by (cases s, cases s') auto
      from this(3) have "((\<sigma>, q), a, (\<sigma>', q')) \<in> trans (optoy i)"
        by simp (rule open_seqp_action [OF toy_wf])

      with `s = (\<sigma> i, q)` and `s' = (\<sigma>' i, q')`
        show "((\<sigma>, snd (id s)), a, (\<sigma>', snd (id s'))) \<in> trans (optoy i)"
          by simp
    qed
    then interpret op: openproc ptoy optoy id .
    have [simp]: "\<And>i. (SOME x. x \<in> (fst o id) ` init (ptoy i)) = toy_init i"
      unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def by simp
    hence "\<And>i. openproc.initmissing ptoy id i = initmissing i"
      unfolding op.initmissing_def op.someinit_def initmissing_def
      by (auto split: option.split)
    thus "openproc.initmissing ptoy id = initmissing" ..
  qed

lemma fst_initmissing_netgmap_default_toy_init_netlift:
  "fst (initmissing (netgmap fst s)) = default toy_init (netlift fst s)"
  unfolding initmissing_def default_def
  by (simp add: fst_netgmap_netlift del: One_nat_def)

definition
  netglobal :: "((nat \<Rightarrow> state) \<Rightarrow> bool) \<Rightarrow> ((state \<times> 'b) \<times> 'c) net_state \<Rightarrow> bool"
where
  "netglobal P \<equiv> (\<lambda>s. P (default toy_init (netlift fst s)))"

interpretation toy_openproc_par_qmsg: openproc_parq ptoy optoy id qmsg
  where "toy_openproc_par_qmsg.netglobal = netglobal"
    and "toy_openproc_par_qmsg.initmissing = initmissing"
  proof -
    show "openproc_parq ptoy optoy id qmsg"
      by (unfold_locales) simp
    then interpret opq: openproc_parq ptoy optoy id qmsg .

    have im: "\<And>\<sigma>. openproc.initmissing (\<lambda>i. ptoy i \<langle>\<langle> qmsg) (\<lambda>(p, q). (fst (id p), snd (id p), q)) \<sigma>
                                                                                    = initmissing \<sigma>"
      unfolding opq.initmissing_def opq.someinit_def initmissing_def
      unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_def by (clarsimp cong: option.case_cong)
    thus "openproc.initmissing (\<lambda>i. ptoy i \<langle>\<langle> qmsg) (\<lambda>(p, q). (fst (id p), snd (id p), q)) = initmissing"
      by (rule ext)

    have "\<And>P \<sigma>. openproc.netglobal (\<lambda>i. ptoy i \<langle>\<langle> qmsg) (\<lambda>(p, q). (fst (id p), snd (id p), q)) P \<sigma>
                                                                                = netglobal P \<sigma>"
      unfolding opq.netglobal_def netglobal_def opq.initmissing_def initmissing_def opq.someinit_def
      unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_def
      by (clarsimp cong: option.case_cong
                   simp del: One_nat_def
                   simp add: fst_initmissing_netgmap_default_toy_init_netlift
                                                  [symmetric, unfolded initmissing_def])
    thus "openproc.netglobal (\<lambda>i. ptoy i \<langle>\<langle> qmsg) (\<lambda>(p, q). (fst (id p), snd (id p), q)) = netglobal"
      by auto
  qed

subsection "Final result"

lemma bigger_than_next:
  assumes "wf_net_tree any"
  shows "closed (pnet (\<lambda>i. ptoy i \<langle>\<langle> qmsg) any) \<TTurnstile> netglobal (\<lambda>\<sigma>. \<forall>i. no (\<sigma> i) \<le> no (\<sigma> (nhip (\<sigma> i))))"
        (is "_ \<TTurnstile> netglobal (\<lambda>\<sigma>. \<forall>i. ?inv \<sigma> i)")
  proof -
    from `wf_net_tree any`
      have proto: "closed (pnet (\<lambda>i. ptoy i \<langle>\<langle> qmsg) any)
                      \<TTurnstile> netglobal (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips any. no (\<sigma> i) \<le> no (\<sigma> (nhip (\<sigma> i))))"
        by (rule toy_openproc_par_qmsg.close_opnet [OF _ ocnet_bigger_than_next])
    show ?thesis
    unfolding invariant_def opnet_sos.opnet_tau1
    proof (rule, simp only: toy_openproc_par_qmsg.netglobalsimp
                            fst_initmissing_netgmap_pair_fst, rule allI)
      fix \<sigma> i
      assume sr: "\<sigma> \<in> reachable (closed (pnet (\<lambda>i. ptoy i \<langle>\<langle> qmsg) any)) TT"
      hence "\<forall>i\<in>net_tree_ips any. ?inv (fst (initmissing (netgmap fst \<sigma>))) i"
        by - (drule invariantD [OF proto],
              simp only: toy_openproc_par_qmsg.netglobalsimp
                         fst_initmissing_netgmap_pair_fst)
      thus "?inv (fst (initmissing (netgmap fst \<sigma>))) i"
      proof (cases "i\<in>net_tree_ips any")
        assume "i\<notin>net_tree_ips any"
        from sr have "\<sigma> \<in> reachable (pnet (\<lambda>i. ptoy i \<langle>\<langle> qmsg) any) TT" ..
        hence "net_ips \<sigma> = net_tree_ips any" ..
        with `i\<notin>net_tree_ips any` have "i\<notin>net_ips \<sigma>" by simp
        hence "(fst (initmissing (netgmap fst \<sigma>))) i = toy_init i"
          by simp
        thus ?thesis by simp
      qed metis
    qed
  qed
 
end
