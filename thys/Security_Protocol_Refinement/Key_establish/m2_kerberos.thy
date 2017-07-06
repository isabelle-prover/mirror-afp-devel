(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Key_establish/m2_kerberos.thy (Isabelle/HOL 2016-1)
  ID:      $Id: m2_kerberos.thy 133854 2017-03-20 17:53:50Z csprenge $
  Author:  Ivano Somaini, ETH Zurich <somainii@student.ethz.ch>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Key distribution protocols
  Second refinement: channel-protocol, parallel version of BAN-Kerberos

  Copyright (c) 2009-2016 Ivano Somaini, Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section {* Abstract Kerberos core protocol (L2) *}

theory m2_kerberos imports m1_kerberos "../Refinement/Channels"
begin

text {* 
We model an abstract version of the core Kerberos protocol:
\[
\begin{array}{lll}
  \mathrm{M1.}  & A \rightarrow S: & A, B, Na \\ 
  \mathrm{M2a.} & S \rightarrow A: & \{Kab, Ts, B, Na\}_{Kas} \\
  \mathrm{M2b.} & S \rightarrow B: & \{Kab, Ts, A\}_{Kbs} \\
  \mathrm{M3.}  & A \rightarrow B: & \{A, Ta\}_{Kab} \\
  \mathrm{M4.}  & B \rightarrow A: & \{Ta\}_{Kab} \\
\end{array}
\]
Message 1 is sent over an insecure channel, the other four (cleartext) messages 
over secure channels.
*}

declare domIff [simp, iff del]


(******************************************************************************)
subsection {* State *}
(******************************************************************************)

text {* State and observations *}

record m2_state = "m1_state" +
  chan :: "chmsg set"              -- {* channel messages *}

type_synonym 
  m2_obs = "m1_state" 

definition 
  m2_obs :: "m2_state \<Rightarrow> m2_obs" where
  "m2_obs s \<equiv> \<lparr> 
     runs = runs s,
     leak = leak s,
     clk = clk s, 
     cache = cache s
  \<rparr>"

type_synonym
  m2_pred = "m2_state set"

type_synonym
  m2_trans = "(m2_state \<times> m2_state) set"


(******************************************************************************)
subsection {* Events *}
(******************************************************************************)

text {* Protocol events. *}

definition     -- {* by @{term "A"}, refines @{term "m1a_step1"} *}
  m2_step1 :: "[rid_t, agent, agent, nonce] \<Rightarrow> m2_trans"
where
  "m2_step1 Ra A B Na \<equiv> {(s, s1).
     (* guards: *)
     Ra \<notin> dom (runs s) \<and>                                (* Ra is fresh *)
     Na = Ra$na \<and>                                        (* generate nonce *)

     (* actions: *)
     (* create initiator thread and send message 1 *)
     s1 = s\<lparr>
       runs := (runs s)(Ra \<mapsto> (Init, [A, B], [])),
       chan := insert (Insec A B (Msg [aNon Na])) (chan s)  (* send M1 *)
     \<rparr>
  }"

definition     -- {* by @{term "B"}, refines @{term "m1e_step2"} *}
  m2_step2 :: "[rid_t, agent, agent] \<Rightarrow> m2_trans"
where
  "m2_step2 \<equiv> m1_step2"

definition     -- {* by @{text "Server"}, refines @{term m1e_step3} *}
  m2_step3 :: 
    "[rid_t, agent, agent, key, nonce, time] \<Rightarrow> m2_trans"
where
  "m2_step3 Rs A B Kab Na Ts \<equiv> {(s, s1). 

     (* guards: *)
     Rs \<notin> dom (runs s) \<and>                               (* fresh server run *)
     Kab = sesK (Rs$sk) \<and>                               (* fresh session key *)
     Ts = clk s \<and>                                      (* fresh timestamp *) 

     Insec A B (Msg [aNon Na]) \<in> chan s \<and>              (* recv M1 *)
   
     (* actions: *)
     (* record key and send messages 2 and 3 *)
     s1 = s\<lparr>
       runs := (runs s)(Rs \<mapsto> (Serv, [A, B], [aNon Na, aNum Ts])), 
       chan := {Secure Sv A (Msg [aKey Kab, aAgt B, aNum Ts, aNon Na]),  (* send M2a/b *)
                Secure Sv B (Msg [aKey Kab, aAgt A, aNum Ts])} \<union> chan s
     \<rparr>
  }"

definition     -- {* by @{term "A"}, refines @{term m1e_step4} *}
  m2_step4 :: "[rid_t, agent, agent, nonce, key, time, time] \<Rightarrow> m2_trans"
where
  "m2_step4 Ra A B Na Kab Ts Ta \<equiv> {(s, s1).
     (* guards: *)
     runs s Ra = Some (Init, [A, B], []) \<and>          (* session key not yet recv'd*)
     Na = Ra$na \<and>                                   (* fix nonce *)
     Ta = clk s \<and>                                   (* fresh timestamp *) 
     clk s < Ts + Ls \<and>                              (* ensure key recentness *)

     Secure Sv A (Msg [aKey Kab, aAgt B, aNum Ts, aNon Na]) \<in> chan s \<and>  (* recv M2a *)

     (* actions: *)
     (* record session key *)
     s1 = s\<lparr>
       runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta])),
       chan := insert (dAuth Kab (Msg [aAgt A, aNum Ta])) (chan s)   (* send M3 *)
     \<rparr>
  }"

definition     -- {* by @{term "B"}, refines @{term m1e_step5} *}
  m2_step5 :: "[rid_t, agent, agent, key, time, time] \<Rightarrow> m2_trans"
where
  "m2_step5 Rb A B Kab Ts Ta \<equiv> {(s, s1). 
     (* guards: *)
     runs s Rb = Some (Resp, [A, B], []) \<and>          (* Kab not yet received *)
     Secure Sv B (Msg [aKey Kab, aAgt A, aNum Ts]) \<in> chan s \<and>   (* recv M2b *)
     dAuth Kab (Msg [aAgt A, aNum Ta]) \<in> chan s \<and>            (* recv M3 *)

     (* ensure freshness of session key *)
     clk s < Ts + Ls \<and>

     (* check authenticator's validity and replay; 'replays' with fresh authenticator ok!*)
     clk s < Ta + La \<and> 
     (B, Kab, Ta) \<notin> cache s \<and> 

     (* actions: *)
     (* record session key, send message M4 *)
     s1 = s\<lparr>
       runs := (runs s)(Rb \<mapsto> (Resp, [A, B], [aKey Kab, aNum Ts, aNum Ta])), 
       cache := insert (B, Kab, Ta) (cache s),
       chan := insert (dAuth Kab (Msg [aNum Ta])) (chan s)   (* send M4 *)
     \<rparr>
  }"

definition     -- {* by @{term "A"}, refines @{term m1e_step6} *}
  m2_step6 :: "[rid_t, agent, agent, nonce, key, time, time] \<Rightarrow> m2_trans"
where
  "m2_step6 Ra A B Na Kab Ts Ta \<equiv> {(s, s'). 
     runs s Ra = Some (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta]) \<and>   (* key recv'd before *)
     Na = Ra$na \<and>                                    (* generated nonce *)

     clk s < Ts + Ls \<and>                               (* check session key's recentness *)

     dAuth Kab (Msg [aNum Ta]) \<in> chan s \<and>            (* recv M4 *)
 
     (* actions: *)
     s' = s\<lparr>
       runs := (runs s)(Ra \<mapsto> (Init, [A, B], [aKey Kab, aNum Ts, aNum Ta, END]))
     \<rparr>
  }"


text {* Clock tick event *}

definition     -- {* refines @{term m1_tick} *}
  m2_tick :: "time \<Rightarrow> m2_trans" 
where
  "m2_tick \<equiv> m1_tick"


text {* Purge event: purge cache of expired timestamps *}

definition     -- {* refines @{term "m1_purge"} *}
  m2_purge :: "agent \<Rightarrow> m2_trans" 
where
  "m2_purge \<equiv> m1_purge"


text {* Intruder events. *}

definition     -- {* refines @{term m1_leak} *}
  m2_leak :: "[rid_t, agent, agent, nonce, time] \<Rightarrow> m2_trans" 
where
  "m2_leak Rs A B Na Ts \<equiv> {(s, s1).
    (* guards: *) 
    runs s Rs = Some (Serv, [A, B], [aNon Na, aNum Ts]) \<and> 
    (clk s \<ge> Ts + Ls) \<and>            (* only compromise 'old' session keys *)

    (* actions: *)
    (* record session key as leaked; *)
    (* intruder sends himself an insecure channel message containing the key *)
    s1 = s\<lparr> leak := insert (sesK (Rs$sk), A, B, Na, Ts) (leak s), 
            chan := insert (Insec undefined undefined (Msg [aKey (sesK (Rs$sk))])) (chan s) \<rparr> 
  }"

definition     -- {* refines @{term Id} *} 
  m2_fake :: "m2_trans"
where
  "m2_fake \<equiv> {(s, s1). 

     (* actions: *)
     s1 = s\<lparr>
       (* close under fakeable messages *)
       chan := fake ik0 (dom (runs s)) (chan s) 
     \<rparr>
  }"


(******************************************************************************)
subsection {* Transition system *}
(******************************************************************************)

definition 
  m2_init :: "m2_pred"
where
  "m2_init \<equiv> { \<lparr>
     runs = empty,
     leak = corrKey \<times> {undefined},
     clk = 0,
     cache = {},
     chan = {}
  \<rparr> }"

definition 
  m2_trans :: "m2_trans" where
  "m2_trans \<equiv> (\<Union>A B Ra Rb Rs Na Kab Ts Ta T.
     m2_step1 Ra A B Na \<union>
     m2_step2 Rb A B \<union>
     m2_step3 Rs A B Kab Na Ts \<union>
     m2_step4 Ra A B Na Kab Ts Ta \<union>
     m2_step5 Rb A B Kab Ts Ta \<union>
     m2_step6 Ra A B Na Kab Ts Ta \<union>
     m2_tick T \<union>
     m2_purge A \<union> 
     m2_leak Rs A B Na Ts \<union>
     m2_fake \<union>
     Id
  )"

definition 
  m2 :: "(m2_state, m2_obs) spec" where
  "m2 \<equiv> \<lparr>
    init = m2_init,
    trans = m2_trans,
    obs = m2_obs
  \<rparr>"

lemmas m2_loc_defs = 
  m2_def m2_init_def m2_trans_def m2_obs_def
  m2_step1_def m2_step2_def m2_step3_def m2_step4_def m2_step5_def 
  m2_step6_def m2_tick_def m2_purge_def m2_leak_def m2_fake_def 

lemmas m2_defs = m2_loc_defs m1_defs


(******************************************************************************)
subsection {* Invariants and simulation relation *}
(******************************************************************************)

subsubsection {* inv1: Key definedness *}
(*inv**************************************************************************)

text {* All session keys in channel messages stem from existing runs. *}

definition 
  m2_inv1_keys :: "m2_state set"
where 
  "m2_inv1_keys \<equiv> {s. \<forall>R.
     aKey (sesK (R$sk)) \<in> atoms (chan s) \<or> sesK (R$sk) \<in> Domain (leak s) \<longrightarrow> 
       R \<in> dom (runs s)
  }"

lemmas m2_inv1_keysI = m2_inv1_keys_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv1_keysE [elim] = m2_inv1_keys_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv1_keysD = m2_inv1_keys_def [THEN setc_def_to_dest, rule_format, rotated 1]


text {* Invariance proof. *}

lemma PO_m2_inv1_keys_init [iff]:
  "init m2 \<subseteq> m2_inv1_keys"
by (auto simp add: m2_defs intro!: m2_inv1_keysI)

lemma PO_m2_inv1_keys_trans [iff]:
  "{m2_inv1_keys} trans m2 {> m2_inv1_keys}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv1_keysI)
apply (auto simp add:  dest: m2_inv1_keysD dom_lemmas)
done

lemma PO_m2_inv1_keys [iff]: "reach m2 \<subseteq> m2_inv1_keys"
by (rule inv_rule_basic) (auto)


subsubsection {* inv2: Definedness of used keys *}
(*inv*************************************************************************)

definition 
  m2_inv2_keys_for :: "m2_state set"
where 
  "m2_inv2_keys_for \<equiv> {s. \<forall>R.
     sesK (R$sk) \<in> keys_for (chan s) \<longrightarrow> R \<in> dom (runs s)
  }"

lemmas m2_inv2_keys_forI = m2_inv2_keys_for_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv2_keys_forE [elim] = m2_inv2_keys_for_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv2_keys_forD = m2_inv2_keys_for_def [THEN setc_def_to_dest, rule_format, rotated 1]


text {* Invariance proof. *}

lemma PO_m2_inv2_keys_for_init [iff]:
  "init m2 \<subseteq> m2_inv2_keys_for"
by (auto simp add: m2_defs intro!: m2_inv2_keys_forI)

lemma PO_m2_inv2_keys_for_trans [iff]:
  "{m2_inv2_keys_for \<inter> m2_inv1_keys} trans m2 {> m2_inv2_keys_for}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv2_keys_forI)
apply (auto dest: m2_inv2_keys_forD m2_inv1_keysD dest: dom_lemmas)
-- {* 2 subgoals, from step3 and fake *}
apply (rename_tac R s xb xc xd xi, 
       subgoal_tac "aKey (sesK (R$sk)) \<in> atoms (chan s)", auto)
apply (auto simp add: keys_for_def, erule fake.cases, fastforce+)
done

lemma PO_m2_inv2_keys_for [iff]: "reach m2 \<subseteq> m2_inv2_keys_for"
by (rule inv_rule_incr) (auto del: subsetI)


subsubsection {* inv3a: Session key compromise *}
(*inv**************************************************************************)

text {* A L2 version of a session key comprise invariant. Roughly, it states
that adding a set of keys @{term KK} to the parameter @{text T} of @{term extr} 
does not help the intruder to extract keys other than those in @{term KK} or
extractable without adding @{term KK}. 
*}

definition 
  m2_inv3a_sesK_compr :: "m2_state set"
where 
  "m2_inv3a_sesK_compr \<equiv> {s. \<forall>K KK.
     (* KK \<subseteq> range sesK \<longrightarrow> *)
     aKey K \<in> extr (aKey`KK \<union> ik0) (chan s) \<longleftrightarrow> (K \<in> KK \<or> aKey K \<in> extr ik0 (chan s)) 
  }"

lemmas m2_inv3a_sesK_comprI = m2_inv3a_sesK_compr_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv3a_sesK_comprE [elim] = m2_inv3a_sesK_compr_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv3a_sesK_comprD = m2_inv3a_sesK_compr_def [THEN setc_def_to_dest, rule_format]

text {* Additional lemma to get the keys in front *}
lemmas insert_commute_aKey = insert_commute [where x="aKey K" for K] 

lemmas m2_inv3a_sesK_compr_simps = 
  m2_inv3a_sesK_comprD
  m2_inv3a_sesK_comprD [where KK="insert Kab KK" for Kab KK, simplified]
  m2_inv3a_sesK_comprD [where KK="{Kab}" for Kab, simplified]
  insert_commute_aKey 

lemma PO_m2_inv3a_sesK_compr_init [iff]:
  "init m2 \<subseteq> m2_inv3a_sesK_compr"
by (auto simp add: m2_defs intro!: m2_inv3a_sesK_comprI)

lemma PO_m2_inv3a_sesK_compr_trans [iff]:
  "{m2_inv3a_sesK_compr} trans m2 {> m2_inv3a_sesK_compr}"
by (auto simp add: PO_hoare_defs m2_defs m2_inv3a_sesK_compr_simps intro!: m2_inv3a_sesK_comprI)

lemma PO_m2_inv3a_sesK_compr [iff]: "reach m2 \<subseteq> m2_inv3a_sesK_compr"
by (rule inv_rule_basic) (auto) 


subsubsection {* inv3b: Leakage of old session keys *}
(*inv**************************************************************************)

text {* Only old session keys are leaked to the intruder. *}

definition
  m2_inv3b_leak :: "m2_state set"
where
  "m2_inv3b_leak \<equiv> {s. \<forall>Rs A B Na Ts. 
     (sesK (Rs$sk), A, B, Na, Ts) \<in> leak s \<longrightarrow> clk s \<ge> Ts + Ls
  }"

lemmas m2_inv3b_leakI = m2_inv3b_leak_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv3b_leakE [elim] = m2_inv3b_leak_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv3b_leakD = m2_inv3b_leak_def [THEN setc_def_to_dest, rule_format, rotated 1]


text {* Invariance proof. *}

lemma PO_m2_inv3b_leak_init [iff]:
  "init m2 \<subseteq> m2_inv3b_leak"
by (auto simp add: m2_defs intro!: m2_inv3b_leakI)

lemma PO_m2_inv3b_leak_trans [iff]:
  "{m2_inv3b_leak \<inter> m2_inv1_keys} trans m2 {> m2_inv3b_leak}"
by (fastforce simp add: PO_hoare_defs m2_defs intro!: m2_inv3b_leakI dest: m2_inv3b_leakD)

lemma PO_m2_inv3b_leak [iff]: "reach m2 \<subseteq> m2_inv3b_leak"
by (rule inv_rule_incr) (auto del: subsetI)


subsubsection {* inv3: Lost session keys *}
(*inv**************************************************************************)

text {* inv3: Lost but not leaked session keys generated by the server for at 
least one bad agent. This invariant is needed in the proof of the strengthening 
of the authorization guards in steps 4 and 5 (e.g., 
@{term "Kab \<notin> Domain (leaks s) \<longrightarrow> (Kab, A) \<in> azC (runs s)"} for the initiator's step4). 
*}

definition 
  m2_inv3_extrKey :: "m2_state set"
where
  "m2_inv3_extrKey \<equiv> {s. \<forall>K.
     aKey K \<in> extr ik0 (chan s) \<longrightarrow> 
       (K \<in> corrKey \<and> K \<in> Domain (leak s)) \<or>
       (\<exists>R A' B' Na' Ts'. K = sesK (R$sk) \<and>
          runs s R = Some (Serv, [A', B'], [aNon Na', aNum Ts']) \<and> 
          (A' \<in> bad \<or> B' \<in> bad \<or> (K, A', B', Na', Ts') \<in> leak s))
  }"

lemmas m2_inv3_extrKeyI = m2_inv3_extrKey_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv3_extrKeyE [elim] = m2_inv3_extrKey_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv3_extrKeyD = m2_inv3_extrKey_def [THEN setc_def_to_dest, rule_format, rotated 1]

lemma PO_m2_inv3_extrKey_init [iff]:
  "init m2 \<subseteq> m2_inv3_extrKey"
by (auto simp add: m2_defs intro!: m2_inv3_extrKeyI)

lemma PO_m2_inv3_extrKey_trans [iff]:
  "{m2_inv3_extrKey \<inter> m2_inv3a_sesK_compr} 
      trans m2 
   {> m2_inv3_extrKey}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv3_extrKeyI)
apply (auto simp add: m2_inv3a_sesK_compr_simps dest!: m2_inv3_extrKeyD dest: dom_lemmas) (* SLOW *)
done

lemma PO_m2_inv3_extrKey [iff]: "reach m2 \<subseteq> m2_inv3_extrKey"
by (rule_tac J="m2_inv3a_sesK_compr" in inv_rule_incr) (auto) 


subsubsection {* inv4: Messages M2a/M2b for good agents and server state *}
(*inv**************************************************************************)

text {* inv4: Secure messages to honest agents and server state; one variant 
for each of M2a and M2b. These invariants establish guard strengthening for
server authentication by the initiator and the responder. *}

definition 
  m2_inv4_M2a :: "m2_state set"
where
  "m2_inv4_M2a \<equiv> {s. \<forall>A B Kab Ts Na.
     Secure Sv A (Msg [aKey Kab, aAgt B, aNum Ts, aNon Na]) \<in> chan s \<longrightarrow> A \<in> good \<longrightarrow>
       (\<exists>Rs. Kab = sesK (Rs$sk) \<and>
          runs s Rs = Some (Serv, [A, B], [aNon Na, aNum Ts]))
  }"

definition 
  m2_inv4_M2b :: "m2_state set"
where
  "m2_inv4_M2b \<equiv> {s. \<forall>A B Kab Ts.
     Secure Sv B (Msg [aKey Kab, aAgt A, aNum Ts]) \<in> chan s \<longrightarrow> B \<in> good \<longrightarrow>
        (\<exists>Rs Na. Kab = sesK (Rs$sk) \<and>
           runs s Rs = Some (Serv, [A, B], [aNon Na, aNum Ts]))
  }"

lemmas m2_inv4_M2aI = m2_inv4_M2a_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv4_M2aE [elim] = m2_inv4_M2a_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv4_M2aD = m2_inv4_M2a_def [THEN setc_def_to_dest, rule_format, rotated 1]

lemmas m2_inv4_M2bI = m2_inv4_M2b_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv4_M2bE [elim] = m2_inv4_M2b_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv4_M2bD = m2_inv4_M2b_def [THEN setc_def_to_dest, rule_format, rotated 1]


text {* Invariance proofs. *}

lemma PO_m2_inv4_M2a_init [iff]:
  "init m2 \<subseteq> m2_inv4_M2a"
by (auto simp add: m2_defs intro!: m2_inv4_M2aI)

lemma PO_m2_inv4_M2a_trans [iff]:
  "{m2_inv4_M2a} trans m2 {> m2_inv4_M2a}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv4_M2aI)
apply (auto dest!: m2_inv4_M2aD dest: dom_lemmas) 
-- {* 4 subgoals *}
apply (force dest!: spec)
apply (force dest!: spec)
apply (force dest!: spec)
apply (rule exI, auto)
done

lemma PO_m2_inv4_M2a [iff]: "reach m2 \<subseteq> m2_inv4_M2a"
by (rule inv_rule_basic) (auto)


lemma PO_m2_inv4_M2b_init [iff]:
  "init m2 \<subseteq> m2_inv4_M2b"
by (auto simp add: m2_defs intro!: m2_inv4_M2bI)

lemma PO_m2_inv4_M2b_trans [iff]:
  "{m2_inv4_M2b} trans m2 {> m2_inv4_M2b}"
apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv4_M2bI) 
apply (auto dest!: m2_inv4_M2bD dest: dom_lemmas)  
-- {* 4 subgoals *}
apply (force dest!: spec)
apply (force dest!: spec)
apply (force dest!: spec)
apply (rule exI, auto)
done

lemma PO_m2_inv4_M2b [iff]: "reach m2 \<subseteq> m2_inv4_M2b"
by (rule inv_rule_incr) (auto del: subsetI)


text {* Consequence needed in proof of inv8/step5 and inv9/step4: The 
session key uniquely identifies other fields in M2a and M2b, provided it 
is secret. *}

lemma m2_inv4_M2a_M2b_match:
  "\<lbrakk> Secure Sv A' (Msg [aKey Kab, aAgt B', aNum Ts', aNon N]) \<in> chan s; 
     Secure Sv B (Msg [aKey Kab, aAgt A, aNum Ts]) \<in> chan s; 
     aKey Kab \<notin> extr ik0 (chan s); s \<in> m2_inv4_M2a; s \<in> m2_inv4_M2b \<rbrakk>
  \<Longrightarrow> A = A' \<and> B = B' \<and> Ts = Ts'"
apply (subgoal_tac "A' \<notin> bad \<and> B \<notin> bad", auto)
apply (auto dest!: m2_inv4_M2aD m2_inv4_M2bD)
done


text {* More consequences of invariants. Needed in ref/step4 and ref/step5 
respectively to show the strengthening of the authorization guards. *}

lemma m2_inv34_M2a_authorized:
  assumes "Secure Sv A (Msg [aKey K, aAgt B, aNum T, aNon N]) \<in> chan s" 
          "s \<in> m2_inv4_M2a" "s \<in> m2_inv3_extrKey" 
          "K \<notin> Domain (leak s)"
  shows "(K, A) \<in> azC (runs s)"
proof (cases "A \<in> bad")
  case True 
  hence "aKey K \<in> extr ik0 (chan s)" using assms(1) by auto
  thus ?thesis using assms (3-) by auto
next
  case False 
  thus ?thesis using assms(1-2) by (auto dest: m2_inv4_M2aD) 
qed

lemma m2_inv34_M2b_authorized:
  assumes "Secure Sv B (Msg [aKey K, aAgt A, aNum T]) \<in> chan s" 
          "s \<in> m2_inv4_M2b" "s \<in> m2_inv3_extrKey" 
          "K \<notin> Domain (leak s)" 
  shows "(K, B) \<in> azC (runs s)"
  using assms
proof (cases "B \<in> bad")
  case True 
  from assms(1) \<open>B \<in> bad\<close> have "aKey K \<in> extr ik0 (chan s)" by auto
  thus ?thesis using assms (3-) by auto
next
  case False 
  thus ?thesis using assms (1-2) by (auto dest: m2_inv4_M2bD) 
qed


subsubsection {* inv5 (derived): Key secrecy for server *}
(*invd**************************************************************************)

text {* inv5: Key secrecy from server perspective. This invariant links the 
abstract notion of key secrecy to the intruder key knowledge. *}

definition 
  m2_inv5_ikk_sv :: "m2_state set"
where
  "m2_inv5_ikk_sv \<equiv> {s. \<forall>R A B Na Ts.
     runs s R = Some (Serv, [A, B], [aNon Na, aNum Ts]) \<longrightarrow> A \<in> good \<longrightarrow> B \<in> good \<longrightarrow>
     aKey (sesK (R$sk)) \<in> extr ik0 (chan s) \<longrightarrow>
       (sesK (R$sk), A, B, Na, Ts) \<in> leak s
  }"

lemmas m2_inv5_ikk_svI = m2_inv5_ikk_sv_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv5_ikk_svE [elim] = m2_inv5_ikk_sv_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv5_ikk_svD = m2_inv5_ikk_sv_def [THEN setc_def_to_dest, rule_format, rotated 1]


text {* Invariance proof. This invariant follows from @{text m2_inv3_extrKey}. *}

lemma m2_inv5_ikk_sv_derived: 
  "s \<in> m2_inv3_extrKey \<Longrightarrow> s \<in> m2_inv5_ikk_sv"
by (auto simp add: m2_inv3_extrKey_def m2_inv5_ikk_sv_def)

lemma PO_m2_inv5_ikk_sv [iff]: "reach m2 \<subseteq> m2_inv5_ikk_sv"
proof -
  have "reach m2 \<subseteq> m2_inv3_extrKey" by blast
  also have "... \<subseteq> m2_inv5_ikk_sv" by (blast intro: m2_inv5_ikk_sv_derived)
  finally show ?thesis .
qed

(*
lemma PO_m2_inv5_ikk_sv_init [iff]:
  "init m2 \<subseteq> m2_inv5_ikk_sv"
by (auto simp add: m2_defs intro!: m2_inv5_ikk_svI)

lemma PO_m2_inv5_ikk_sv_trans [iff]:
  "{m2_inv5_ikk_sv \<inter> m2_inv3a_sesK_compr \<inter> m2_inv3_extrKey} 
     trans m2 
   {> m2_inv5_ikk_sv}"
apply (simp add: PO_hoare_defs m2_defs, safe intro!: m2_inv5_ikk_svI)
apply (auto simp add: m2_inv3a_sesK_compr_simps dest: dom_lemmas)
done

lemma PO_m2_inv5_ikk_sv [iff]: "reach m2 \<subseteq> m2_inv5_ikk_sv"
by (rule_tac J="m2_inv3a_sesK_compr \<inter> m2_inv3_extrKey" in inv_rule_incr) (auto)
*)

subsubsection {* inv6 (derived): Key secrecy for initiator *}
(*invd**************************************************************************)

text {* This invariant is derivable (see below). *}

definition 
  m2_inv6_ikk_init :: "m2_state set"
where
  "m2_inv6_ikk_init \<equiv> {s. \<forall>A B Ra K Ts nl.
     runs s Ra = Some (Init, [A, B], aKey K # aNum Ts # nl) \<longrightarrow> A \<in> good \<longrightarrow> B \<in> good \<longrightarrow> 
     aKey K \<in> extr ik0 (chan s) \<longrightarrow>
       (K, A, B, Ra$na, Ts) \<in> leak s
  }"

lemmas m2_inv6_ikk_initI = m2_inv6_ikk_init_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv6_ikk_initE [elim] = m2_inv6_ikk_init_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv6_ikk_initD = m2_inv6_ikk_init_def [THEN setc_def_to_dest, rule_format, rotated 1]


subsubsection {* inv7 (derived): Key secrecy for responder *}
(*invd**************************************************************************)

text {* This invariant is derivable (see below). *}

definition 
  m2_inv7_ikk_resp :: "m2_state set"
where
  "m2_inv7_ikk_resp \<equiv> {s. \<forall>A B Rb K Ts nl.
     runs s Rb = Some (Resp, [A, B], aKey K # aNum Ts # nl) \<longrightarrow> A \<in> good \<longrightarrow> B \<in> good \<longrightarrow> 
     aKey K \<in> extr ik0 (chan s) \<longrightarrow>
       (\<exists>Na. (K, A, B, Na, Ts) \<in> leak s)
  }"

lemmas m2_inv7_ikk_respI = m2_inv7_ikk_resp_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv7_ikk_respE [elim] = m2_inv7_ikk_resp_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv7_ikk_respD = m2_inv7_ikk_resp_def [THEN setc_def_to_dest, rule_format, rotated 1]


subsubsection {* inv8: Relating M4 to the responder state *}
(*inv**************************************************************************)

text {* This invariant relates message M4 from the responder to the responder's 
state. It is required in the refinement of step 6 to prove that the initiator 
agrees with the responder on (A, B, Ta, Kab). *}

definition
  m2_inv8_M4 :: "m2_state set"  
where
  "m2_inv8_M4 \<equiv> {s. \<forall>Kab A B Ts Ta N.
     Secure Sv A (Msg [aKey Kab, aAgt B, aNum Ts, aNon N]) \<in> chan s \<longrightarrow>
     dAuth Kab (Msg [aNum Ta]) \<in> chan s \<longrightarrow>  
     aKey Kab \<notin> extr ik0 (chan s) \<longrightarrow>
        (\<exists>Rb. runs s Rb = Some (Resp, [A, B], [aKey Kab, aNum Ts, aNum Ta]))
  }"

lemmas m2_inv8_M4I = m2_inv8_M4_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv8_M4E [elim] = m2_inv8_M4_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv8_M4D = m2_inv8_M4_def [THEN setc_def_to_dest, rule_format, rotated 1]


text {* Invariance proof. *}

lemma PO_m2_inv8_M4_init [iff]:
  "init m2 \<subseteq> m2_inv8_M4"
by (auto simp add: m2_defs intro!: m2_inv8_M4I)

lemma PO_m2_inv8_M4_trans [iff]:
  "{m2_inv8_M4 \<inter> m2_inv4_M2a \<inter> m2_inv4_M2b \<inter> m2_inv3a_sesK_compr \<inter> m2_inv2_keys_for} 
      trans m2 
   {> m2_inv8_M4}"  
proof -
  {
    fix Rs A B Kab Na Ts
    have 
      "{m2_inv8_M4 \<inter> m2_inv3a_sesK_compr \<inter> m2_inv2_keys_for} 
          m2_step3 Rs A B Kab Na Ts 
       {> m2_inv8_M4}"
      apply (simp add: PO_hoare_defs m2_defs, safe intro!: m2_inv8_M4I)
      apply (auto simp add: m2_inv3a_sesK_compr_simps dest!: m2_inv8_M4D dest: dom_lemmas)
      done
  } moreover { 
    fix Ra A B Na Kab Ts Ta
    have "{m2_inv8_M4} m2_step4 Ra A B Na Kab Ts Ta {> m2_inv8_M4}"
      apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv8_M4I)
      -- {* 1 subgoal *}
      apply (drule m2_inv8_M4D, auto) 
      apply (rename_tac Rb, rule_tac x=Rb in exI, auto)
      done
  } moreover {
    fix Rb A B Kab Ts Ta 
    have "{m2_inv8_M4 \<inter> m2_inv4_M2a \<inter> m2_inv4_M2b} m2_step5 Rb A B Kab Ts Ta {> m2_inv8_M4}" 
      apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv8_M4I)
      -- {* 2 subgoals *}
        apply (drule m2_inv4_M2a_M2b_match, auto)

        apply (auto dest!: m2_inv8_M4D)
        apply (rename_tac Rba, rule_tac x=Rba in exI, auto)
      done
  } moreover {
    fix Ra A B Na Kab Ts Ta
    have "{m2_inv8_M4} m2_step6 Ra A B Na Kab Ts Ta {> m2_inv8_M4}"
      apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv8_M4I)
      apply (auto dest!: m2_inv8_M4D)
      -- {* 1 subgoal *}
      apply (rename_tac Rb, rule_tac x=Rb in exI, auto)
      done
  } moreover {
    have "{m2_inv8_M4} m2_fake {> m2_inv8_M4}"
      apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv8_M4I)
      -- {* 1 subgoal *}
      apply (erule fake.cases, auto dest!: m2_inv8_M4D)
      done
  } 
  ultimately show ?thesis
    apply (auto simp add: m2_def m2_trans_def dest!: spec)    (* use above *)
    apply (simp_all (no_asm) add: PO_hoare_defs m2_defs, safe intro!: m2_inv8_M4I) 
    apply (auto simp add: m2_inv3a_sesK_compr_simps dest!: m2_inv8_M4D dest: dom_lemmas)
    done
qed

lemma PO_m2_inv8_M4 [iff]: "reach m2 \<subseteq> m2_inv8_M4"
by (rule_tac J="m2_inv4_M2a \<inter> m2_inv4_M2b \<inter> m2_inv3a_sesK_compr \<inter> m2_inv2_keys_for" 
    in inv_rule_incr) (auto)


subsubsection {* inv9a: Relating the initiator state to M2a *}
(*inv**************************************************************************)

definition
  m2_inv9a_init_M2a :: "m2_state set"
where
  "m2_inv9a_init_M2a \<equiv> {s. \<forall>A B Ra Kab Ts z.
     runs s Ra = Some (Init, [A, B], aKey Kab # aNum Ts # z) \<longrightarrow>
       Secure Sv A (Msg [aKey Kab, aAgt B, aNum Ts, aNon (Ra$na)]) \<in> chan s
  }"

lemmas m2_inv9a_init_M2aI = m2_inv9a_init_M2a_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv9a_init_M2aE [elim] = m2_inv9a_init_M2a_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv9a_init_M2aD = m2_inv9a_init_M2a_def [THEN setc_def_to_dest, rule_format, rotated 1]


text {* Invariance proof. *}

lemma PO_m2_inv9a_init_M2a_init [iff]:
  "init m2 \<subseteq> m2_inv9a_init_M2a"
by (auto simp add: m2_defs intro!: m2_inv9a_init_M2aI)

lemma PO_m2_inv9a_init_M2a_trans [iff]:
  "{m2_inv9a_init_M2a} trans m2 {> m2_inv9a_init_M2a}"
by (fastforce simp add: PO_hoare_defs m2_defs intro!: m2_inv9a_init_M2aI 
              dest: m2_inv9a_init_M2aD)

lemma PO_m2_inv9a_init_M2a [iff]: "reach m2 \<subseteq> m2_inv9a_init_M2a"
by (rule inv_rule_incr) (auto del: subsetI)


subsubsection {* inv9: Relating M3 to the initiator state *}
(*inv**************************************************************************)

text {* This invariant relates message M3 to the initiator's state. It is 
required in step 5 of the refinement to prove that the initiator agrees with 
the responder on (A, B, Ta, Kab). *}

definition
  m2_inv9_M3 :: "m2_state set"  
where
  "m2_inv9_M3 \<equiv> {s. \<forall>Kab A B Ts Ta.
     Secure Sv B (Msg [aKey Kab, aAgt A, aNum Ts]) \<in> chan s \<longrightarrow>
     dAuth Kab (Msg [aAgt A, aNum Ta]) \<in> chan s \<longrightarrow> 
     aKey Kab \<notin> extr ik0 (chan s) \<longrightarrow> (* A \<notin> bad \<longrightarrow> B \<notin> bad \<longrightarrow> *)
       (\<exists>Ra nl. runs s Ra = Some (Init, [A, B], aKey Kab # aNum Ts # aNum Ta # nl))
  }"

lemmas m2_inv9_M3I = m2_inv9_M3_def [THEN setc_def_to_intro, rule_format]
lemmas m2_inv9_M3E [elim] = m2_inv9_M3_def [THEN setc_def_to_elim, rule_format]
lemmas m2_inv9_M3D = m2_inv9_M3_def [THEN setc_def_to_dest, rule_format, rotated 1]


text {* Invariance proof. *}

lemma PO_m2_inv9_M3_init [iff]:
  "init m2 \<subseteq> m2_inv9_M3"
by (auto simp add: m2_defs intro!: m2_inv9_M3I)

lemma PO_m2_inv9_M3_trans [iff]:
  "{m2_inv9_M3 \<inter> m2_inv4_M2a \<inter> m2_inv4_M2b \<inter> m2_inv3a_sesK_compr \<inter> m2_inv2_keys_for} 
      trans m2 
   {> m2_inv9_M3}"
proof -
{
  fix Rs A B Kab Na Ts
  have 
    "{m2_inv9_M3 \<inter> m2_inv3a_sesK_compr \<inter> m2_inv2_keys_for} 
        m2_step3 Rs A B Kab Na Ts 
     {> m2_inv9_M3}"
    apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv9_M3I)
    apply (auto simp add: m2_inv3a_sesK_compr_simps dest!: m2_inv9_M3D dest: dom_lemmas)
    done
} moreover {
  fix Ra A B Na Kab Ts Ta 
  have "{m2_inv9_M3 \<inter> m2_inv4_M2a \<inter> m2_inv4_M2b} m2_step4 Ra A B Na Kab Ts Ta {> m2_inv9_M3}"
    apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv9_M3I)
    apply (auto dest: m2_inv4_M2a_M2b_match)
    -- {* 1 subgoal *}
    apply (frule m2_inv9_M3D, auto)
    apply (rule_tac x=Raa in exI, auto)
    done
} moreover {
  fix Rb A B Kab Ts Ta
  have "{m2_inv9_M3} m2_step5 Rb A B Kab Ts Ta {> m2_inv9_M3}"
    apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv9_M3I)
    apply (auto dest!: m2_inv9_M3D dest: dom_lemmas)
    -- {* 2 subgoals *}
    apply (auto dest!: spec intro!: exI)    -- {* witness Na in both cases *}
    done
} moreover {
  fix Ra A B Na Kab Ts Ta
  have "{m2_inv9_M3} m2_step6 Ra A B Na Kab Ts Ta {> m2_inv9_M3}"
    apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv9_M3I)
    -- {* 1 subgoals *}
    apply (auto dest!: m2_inv9_M3D dest: dom_lemmas)
    apply (rename_tac Raa nl, case_tac "Raa = Ra", auto)
    done
} moreover {
  have "{m2_inv9_M3} m2_fake {> m2_inv9_M3}"
    apply (auto simp add: PO_hoare_defs m2_defs intro!: m2_inv9_M3I)
    -- {* 1 subgoals *}
    apply (erule fake.cases, auto)+
    done
} ultimately 
  show ?thesis 
    apply (auto simp add: m2_def m2_trans_def dest!: spec)     (* use above *)
    apply (simp_all (no_asm) add: PO_hoare_defs m2_defs, safe intro!: m2_inv9_M3I)
    apply (auto simp add: m2_inv3a_sesK_compr_simps dest!: m2_inv9_M3D dest: dom_lemmas)
    done
qed 

lemma PO_m2_inv9_M3 [iff]: "reach m2 \<subseteq> m2_inv9_M3"
by (rule_tac J="m2_inv4_M2a \<inter> m2_inv4_M2b \<inter> m2_inv3a_sesK_compr \<inter> m2_inv2_keys_for" 
    in inv_rule_incr) (auto)


(******************************************************************************)
subsection {* Refinement *}
(******************************************************************************)

text {* The simulation relation. This is a pure superposition refinement. *}

definition
  R12 :: "(m1_state \<times> m2_state) set" where
  "R12 \<equiv> {(s, t). runs s = runs t \<and> leak s = leak t \<and> clk s = clk t \<and> cache s = cache t}"

text {* The mediator function is the identity. *}

definition 
  med21 :: "m2_obs \<Rightarrow> m1_obs" where
  "med21 = id"


text {* Refinement proof. *}

lemma PO_m2_step1_refines_m1_step1:
  "{R12} 
     (m1_step1 Ra A B Na), (m2_step1 Ra A B Na) 
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)

lemma PO_m2_step2_refines_m1_step2:
  "{R12} 
     (m1_step2 Rb A B), (m2_step2 Rb A B)
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)

lemma PO_m2_step3_refines_m1_step3:
  "{R12} 
     (m1_step3 Rs A B Kab Na Ts), (m2_step3 Rs A B Kab Na Ts)
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)

lemma PO_m2_step4_refines_m1_step4:
  "{R12 \<inter> UNIV \<times> (m2_inv4_M2a \<inter> m2_inv3_extrKey)} 
     (m1_step4 Ra A B Na Kab Ts Ta), (m2_step4 Ra A B Na Kab Ts Ta)  
   {> R12}"
apply (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)
apply (auto dest: m2_inv34_M2a_authorized)
done

lemma PO_m2_step5_refines_m1_step5:
  "{R12 \<inter> UNIV 
        \<times> (m2_inv9_M3 \<inter> m2_inv5_ikk_sv \<inter> m2_inv4_M2b \<inter> m2_inv3_extrKey \<inter> m2_inv3b_leak)} 
     (m1_step5 Rb A B Kab Ts Ta), (m2_step5 Rb A B Kab Ts Ta) 
   {> R12}"
apply (simp add: PO_rhoare_defs R12_def m2_defs, safe, simp_all)
apply (auto dest: m2_inv34_M2b_authorized)
-- {* 1 subgoal *}
apply (frule m2_inv4_M2bD, auto)
apply (auto dest: m2_inv9_M3D m2_inv5_ikk_svD [THEN m2_inv3b_leakD])
done

lemma PO_m2_step6_refines_m1_step6:
  "{R12 \<inter> UNIV 
        \<times> (m2_inv9a_init_M2a \<inter> m2_inv8_M4 \<inter> m2_inv5_ikk_sv \<inter> m2_inv4_M2a \<inter> m2_inv3b_leak)} 
     (m1_step6 Ra A B Na Kab Ts Ta), (m2_step6 Ra A B Na Kab Ts Ta) 
   {> R12}"
apply (auto simp add: PO_rhoare_defs R12_def m2_defs)
-- {* 1 subgoal *}
apply (frule m2_inv9a_init_M2aD [THEN m2_inv4_M2aD], auto)
apply (auto dest: m2_inv9a_init_M2aD [THEN m2_inv8_M4D] m2_inv5_ikk_svD [THEN m2_inv3b_leakD])
done

lemma PO_m2_tick_refines_m1_tick:
  "{R12}
    (m1_tick T), (m2_tick T)
   {> R12}"
by (auto simp add: PO_rhoare_defs R12_def m2_defs) 

lemma PO_m2_purge_refines_m1_purge:
  "{R12}
    (m1_purge A), (m2_purge A)
   {> R12}"
by (auto simp add: PO_rhoare_defs R12_def m2_defs) 

lemma PO_m2_leak_refines_leak:
  "{R12} 
     m1_leak Rs A B Na Ts, m2_leak Rs A B Na Ts
   {> R12}"
by (auto simp add: PO_rhoare_defs R12_def m2_defs dest: dom_lemmas)

lemma PO_m2_fake_refines_skip:
  "{R12} 
     Id, m2_fake
   {> R12}"
by (simp add: PO_rhoare_defs R12_def m2_defs, safe, auto)


text {* All together now... *}

lemmas PO_m2_trans_refines_m1_trans = 
  PO_m2_step1_refines_m1_step1 PO_m2_step2_refines_m1_step2
  PO_m2_step3_refines_m1_step3 PO_m2_step4_refines_m1_step4
  PO_m2_step5_refines_m1_step5 PO_m2_step6_refines_m1_step6 
  PO_m2_tick_refines_m1_tick PO_m2_purge_refines_m1_purge
  PO_m2_leak_refines_leak PO_m2_fake_refines_skip 

lemma PO_m2_refines_init_m1 [iff]:
  "init m2 \<subseteq> R12``(init m1)"
by (auto simp add: R12_def m1_defs m2_loc_defs)


lemma PO_m2_refines_trans_m1 [iff]:
  "{R12 \<inter> 
    UNIV \<times> (m2_inv9_M3 \<inter> m2_inv9a_init_M2a \<inter> m2_inv8_M4 \<inter> 
            m2_inv4_M2b \<inter> m2_inv4_M2a \<inter> m2_inv3_extrKey \<inter> m2_inv3b_leak)} 
     (trans m1), (trans m2) 
   {> R12}"
proof -
  -- {* derive invariant @{text "m2_inv5_ikk_sv"} from @{text "m2_inv3_extrKey"}*}
  let ?pre' = "R12 \<inter> 
    UNIV \<times> (m2_inv9_M3 \<inter> m2_inv9a_init_M2a \<inter> m2_inv8_M4 \<inter> m2_inv5_ikk_sv \<inter>
            m2_inv4_M2b \<inter> m2_inv4_M2a \<inter> m2_inv3_extrKey \<inter> m2_inv3b_leak)"
  show ?thesis (is "{?pre} ?t1, ?t2 {>?post}")
  proof (rule relhoare_conseq_left)
    show "?pre \<subseteq> ?pre'"
      by (auto intro: m2_inv5_ikk_sv_derived)
  next 
    show "{?pre'} ?t1, ?t2 {> ?post}"
      by (auto simp add: m2_def m2_trans_def m1_def m1_trans_def)
         (blast intro!: PO_m2_trans_refines_m1_trans)+
  qed
qed  

lemma PO_obs_consistent_R12 [iff]: 
  "obs_consistent R12 med21 m1 m2"
by (auto simp add: obs_consistent_def R12_def med21_def m2_defs)


text {* Refinement result. *}

lemma m2_refines_m1 [iff]:
  "refines 
     (R12 \<inter> 
      (UNIV \<times> 
       (m2_inv9_M3 \<inter> m2_inv9a_init_M2a \<inter> m2_inv8_M4 \<inter> 
        m2_inv4_M2b \<inter> m2_inv4_M2a \<inter> m2_inv3_extrKey \<inter> m2_inv3b_leak \<inter> 
        m2_inv3a_sesK_compr \<inter> m2_inv2_keys_for \<inter> m2_inv1_keys)))
     med21 m1 m2"
by (rule Refinement_using_invariants) (auto)

lemma m2_implements_m1 [iff]:
  "implements med21 m1 m2"
by (rule refinement_soundness) (auto)


(******************************************************************************)
subsection {* Inherited and derived invariants *}
(******************************************************************************)

text {* Show preservation of invariants @{term "m1_inv2i_serv"} and
@{term "m1_inv2r_serv"} from @{text "m1"}. *}

(*invh*************************************************************************)

lemma PO_m2_sat_m1_inv2i_serv [iff]: "reach m2 \<subseteq> m1_inv2i_serv"
by (rule_tac Pa=m1_inv2i_serv and Qa=m1_inv2i_serv and Q=m1_inv2i_serv 
    in m2_implements_m1 [THEN [5] internal_invariant_translation])
   (auto simp add: m2_loc_defs med21_def intro!: m1_inv2i_servI)

(*invh*************************************************************************)

lemma PO_m2_sat_m1_inv2r_serv [iff]: "reach m2 \<subseteq> m1_inv2r_serv"
by (rule_tac Pa=m1_inv2r_serv and Qa=m1_inv2r_serv and Q=m1_inv2r_serv
    in m2_implements_m1 [THEN [5] internal_invariant_translation])
   (fastforce simp add: m2_loc_defs med21_def intro!: m1_inv2r_servI)+


text {* Now we derive the L2 key secrecy invariants for the initiator and the responder 
(see above for the definitions). *}

lemma PO_m2_inv6_init_ikk [iff]: "reach m2 \<subseteq> m2_inv6_ikk_init"
proof -
  have "reach m2 \<subseteq> m1_inv2i_serv \<inter> m2_inv5_ikk_sv" by simp
  also have "... \<subseteq> m2_inv6_ikk_init" by (blast intro!: m2_inv6_ikk_initI dest: m2_inv5_ikk_svD)
  finally show ?thesis .
qed

lemma PO_m2_inv6_resp_ikk [iff]: "reach m2 \<subseteq> m2_inv7_ikk_resp"
proof -
  have "reach m2 \<subseteq> m1_inv2r_serv \<inter> m2_inv5_ikk_sv" by simp
  also have "... \<subseteq> m2_inv7_ikk_resp" by (blast intro!: m2_inv7_ikk_respI dest: m2_inv5_ikk_svD)
  finally show ?thesis .
qed


end

