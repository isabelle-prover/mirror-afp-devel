(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze, Christoph Sprenger
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)

section\<open>Abstract Model\<close>
theory Parametrized_Dataplane_0
  imports
    "Network_Model"
    "infrastructure/Event_Systems"
begin

text\<open>A packet consists of an authenticated info field (e.g., the timestamp of the control plane level
beacon creating the segment), as well as past and future paths. Furthermore, there is a history 
variable @{term "history"} that accurately records the actual path -- this is only used for the
purpose of expressing the desired security property ("Detectability", see below).\<close>

record ('aahi, 'ainfo) pkt0 =
  AInfo :: 'ainfo
  past  :: "'aahi ahi_scheme list"
  future  :: "'aahi ahi_scheme list"
  history  :: "'aahi ahi_scheme list"

text\<open>In this model, the state consists of channel state and local state, each containing sets of 
packets (which we occasionally also call messages).\<close>
record ('aahi, 'ainfo) dp0_state = 
  chan :: "(as \<times> ifs \<times> as \<times> ifs) \<Rightarrow> ('aahi, 'ainfo) pkt0 set"
  loc :: "as \<Rightarrow> ('aahi, 'ainfo) pkt0 set"

text\<open>We now define the events type; it will be explained below.\<close>
datatype ('aahi, 'ainfo) evt0 = 
    evt_dispatch_int0 as "('aahi, 'ainfo) pkt0" 
  | evt_recv0 as ifs "('aahi, 'ainfo) pkt0" 
  | evt_send0 as ifs "('aahi, 'ainfo) pkt0" 
  | evt_deliver0 as "('aahi, 'ainfo) pkt0"
  | evt_dispatch_ext0 as ifs "('aahi, 'ainfo) pkt0" 
  | evt_observe0 "('aahi, 'ainfo) dp0_state"
  | evt_skip0

context network_model
begin

text\<open>We define shortcuts denoting that from a state s, a packet pkt is added to either a local state
or a channel, yielding state s'. No other part of the state is modified.\<close>
definition dp0_add_loc :: "('aahi, 'ainfo) dp0_state \<Rightarrow> ('aahi, 'ainfo) dp0_state 
                            \<Rightarrow> as \<Rightarrow> ('aahi, 'ainfo) pkt0 \<Rightarrow> bool"
where 
  "dp0_add_loc s s' asid pkt \<equiv> s' = s\<lparr>loc := (loc s)(asid := loc s asid \<union> {pkt})\<rparr>"

text \<open>This is a shortcut to denote adding a message to an inter-AS channel. Note that it requires 
the link to exist.\<close>
definition dp0_add_chan :: "('aahi, 'ainfo) dp0_state \<Rightarrow> ('aahi, 'ainfo) dp0_state
                           \<Rightarrow> as \<Rightarrow> ifs \<Rightarrow> ('aahi, 'ainfo) pkt0 \<Rightarrow> bool" where 
  "dp0_add_chan s s' a1 i1 pkt \<equiv> 
    \<exists>a2 i2 . rev_link a1 i1 = (Some a2, Some i2) \<and>
    s' = s\<lparr>chan := (chan s)((a1, i1, a2, i2) := chan s (a1, i1, a2, i2) \<union> {pkt})\<rparr>"

text\<open>Predicate that returns true if a given packet is contained in a given channel.\<close>
definition dp0_in_chan :: "('aahi, 'ainfo) dp0_state \<Rightarrow> as \<Rightarrow> ifs \<Rightarrow> ('aahi, 'ainfo) pkt0 \<Rightarrow> bool" where 
  "dp0_in_chan s a1 i1 pkt \<equiv> 
    \<exists>a2 i2 . rev_link a1 i1 = (Some a2, Some i2) \<and> pkt \<in> (chan s)(a2, i2, a1, i1)"

lemmas dp0_msgs = dp0_add_loc_def dp0_add_chan_def dp0_in_chan_def

(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

text\<open>A typical sequence of events is the following:
\begin{itemize}
\item An AS creates a new packet using @{term "evt_dispatch_int0"} event and puts the packet into its local
state.
\item The AS forwards the packet to the next AS with the @{term "evt_send0"} event, which 
puts the message into an inter-AS channel. 
\item The next AS takes the packet from the channel and puts it in the local state in 
@{term "evt_recv0"}.
\item The last two steps are repeated as the packet gets forwarded from hop to hop through the network,
until it reaches the final AS.
\item The final AS delivers the packet internally to the intended destination with the event
@{term "evt_deliver0"}.
\end{itemize}\<close>

definition
  dp0_dispatch_int
where
  "dp0_dispatch_int s m ainfo asid pas fut hist s' \<equiv>
    \<comment> \<open>guard: check that the future path is a fragment of an authorized segment. In reality,
        honest agents will always choose a path that is a prefix of an authorized segment, but for
        our models this difference is not significant.\<close>
    m = \<lparr> AInfo = ainfo, past = pas, future = fut, history = hist \<rparr> \<and>
    hist = [] \<and>
    pfragment ainfo fut auth_seg0 \<and>
    \<comment> \<open>action: Update the state to include m\<close>
    dp0_add_loc s s' asid m"

definition
  dp0_recv
where
  "dp0_recv s m asid ainfo hf1 downif pas fut hist s' \<equiv>
    \<comment> \<open>guard: there are at least two hop fields left, which means we can advance the packet by one
               hop.\<close>
    m = \<lparr> AInfo = ainfo, past = pas, future = hf1 # fut, history = hist \<rparr> \<and>
    dp0_in_chan s asid downif m \<and> 
    
    ASID hf1 = asid \<and>

    \<comment> \<open>action: Update state to include message\<close>
    dp0_add_loc s s' asid \<lparr>
                AInfo = ainfo,
                past = pas,
                future = hf1 # fut,
                history = hist
              \<rparr>"

definition
  dp0_send
where
  "dp0_send s m asid ainfo hf1 upif pas fut hist s' \<equiv>
    \<comment> \<open>guard: there are at least two hop fields left, which means we can advance the packet by one
               hop. \<close>
    m = \<lparr> AInfo = ainfo, past = pas, future = hf1#fut, history = hist \<rparr> \<and>
    m \<in> (loc s) asid \<and>
    UpIF hf1 = Some upif \<and>
    ASID hf1 = asid \<and>

    \<comment> \<open>action: Update state to include modified message\<close>
    dp0_add_chan s s' asid upif \<lparr>
                AInfo = ainfo,
                past = hf1 # pas,
                future = fut,
                history = hf1 # hist
              \<rparr>"

text \<open>This event represents the destination receiving the packet. Our properties are not expressed
over what happens when an end hosts receives a packet (but rather what happens with a packet while
it traverses the network).
We only need this event to push the last hop field from the future path into the past path, as the
detectability property is expressed over the past path.\<close>
definition
  dp0_deliver
where
  "dp0_deliver s m asid ainfo hf1 pas fut hist s' \<equiv>
    m = \<lparr> AInfo = ainfo, past = pas, future = hf1#fut, history = hist \<rparr> \<and>
    ASID hf1 = asid \<and>
    m \<in> (loc s) asid \<and>
    fut = [] \<and>

    \<comment> \<open>action: Update state to include modified message\<close>
    dp0_add_loc s s' asid 
              \<lparr>
                AInfo = ainfo,
                past = hf1 # pas,
                future = [],
                history = hf1 # hist
              \<rparr>"

\<comment> \<open>Direct dispatch event. A node with asid sends a packet on its outgoing interface upif.

Note that the attacker is NOT part of the real past path. However,
detectability is still achieved in practice, since hf (the hop field of the next AS) points with
its downif towards the attacker node. \<close>
definition
  dp0_dispatch_ext
where
  "dp0_dispatch_ext s m asid ainfo upif pas fut hist s' \<equiv>
    m = \<lparr> AInfo = ainfo, past = pas, future = fut, history = hist \<rparr> \<and>
    hist = [] \<and>

    pfragment ainfo fut auth_seg0 \<and>

    \<comment> \<open>action: Update state to include attacker message\<close>
    dp0_add_chan s s' asid upif m"

(******************************************************************************)
subsection \<open>Transition system\<close>
(******************************************************************************)

fun dp0_trans where
  "dp0_trans s (evt_dispatch_int0 asid m) s' \<longleftrightarrow> 
    (\<exists>ainfo pas fut hist. dp0_dispatch_int s m ainfo asid pas fut hist s')" |
  "dp0_trans s (evt_recv0 asid downif m) s' \<longleftrightarrow> 
    (\<exists>ainfo hf1 pas fut hist. dp0_recv s m asid ainfo hf1 downif pas fut hist s')" |
  "dp0_trans s (evt_send0 asid upif m) s' \<longleftrightarrow> 
    (\<exists>ainfo hf1 pas fut hist. dp0_send s m asid ainfo hf1 upif pas fut hist s')" |
  "dp0_trans s (evt_deliver0 asid m) s' \<longleftrightarrow> 
    (\<exists>ainfo hf1 pas fut hist. dp0_deliver s m asid ainfo hf1 pas fut hist s')" |
  "dp0_trans s (evt_dispatch_ext0 asid upif m) s' \<longleftrightarrow> 
    (\<exists>ainfo pas fut hist. dp0_dispatch_ext s m asid ainfo upif pas fut hist s')" |
  "dp0_trans s (evt_observe0 s'') s' \<longleftrightarrow> s = s' \<and> s = s''" |
  "dp0_trans s evt_skip0 s' \<longleftrightarrow> s = s'"

definition dp0_init :: "('aahi, 'ainfo) dp0_state" where
  "dp0_init \<equiv> \<lparr>chan = (\<lambda>_. {}), loc = (\<lambda>_. {})\<rparr>"

definition dp0 :: "(('aahi, 'ainfo) evt0, ('aahi, 'ainfo) dp0_state) ES" where
  "dp0 \<equiv> \<lparr>
    init = (=) dp0_init,
    trans = dp0_trans
  \<rparr>"

lemmas dp0_trans_defs = dp0_dispatch_int_def dp0_recv_def dp0_send_def dp0_deliver_def dp0_dispatch_ext_def
lemmas dp0_defs = dp0_def dp0_init_def dp0_trans_defs

text\<open>@{text "soup"} is a predicate that is true for a packet m and a state s, if m is contained
anywhere in the system (either in the local state or channels).\<close>
definition soup where "soup m s \<equiv> \<exists>x. m \<in> (loc s) x \<or> (\<exists>x. m \<in> (chan s) x)" 

declare soup_def [simp]
declare if_split_asm [split]

lemma dp0_add_chan_msgs:
  assumes "dp0_add_chan s s' asid upif m" and "soup n s'" and "n \<noteq> m"
  shows "soup n s"
    using assms by (auto simp add: dp0_add_chan_def)

(******************************************************************************)
subsection \<open>Path authorization property\<close>
(******************************************************************************)

text\<open>Path authorization is defined as:
For all messages in the system: the future path is a fragment of an authorized path. 
We strengthen this property by including the real past path (the recorded history that can not be
faked by the attacker). The concatenation of these path remains invariant during forwarding, makes 
this invariant inductive. Note that the history path is in reverse order.\<close>
definition auth_path :: "('aahi, 'ainfo) pkt0 \<Rightarrow> bool" where
  "auth_path m \<equiv> pfragment (AInfo m) (rev (history m) @ future m) auth_seg0"

definition inv_auth :: "('aahi, 'ainfo) dp0_state \<Rightarrow> bool" where
  "inv_auth s \<equiv> \<forall>m . soup m s \<longrightarrow> auth_path m"

lemma inv_authI: 
  assumes "\<And>m . soup m s \<Longrightarrow> pfragment (AInfo m) (rev (history m) @ future m) auth_seg0"
  shows "inv_auth s"
  apply(auto simp add: inv_auth_def auth_path_def)
  using assms soup_def by blast+

lemma inv_authD: 
  assumes "inv_auth s" "soup m s"
  shows "pfragment (AInfo m) (rev (history m) @ future m) auth_seg0"
  using assms by(auto simp add: inv_auth_def auth_path_def) blast

lemma inv_auth_add_chan[elim!]:
  assumes "dp0_add_chan s s' asid upif m" and "inv_auth s"
      and "pfragment (AInfo m) (rev (history m) @ future m) auth_seg0"
    shows "inv_auth s'"
proof(rule inv_authI)
  fix n
  assume "soup n s'"
  then show "pfragment (AInfo n) (rev (history n) @ future n) auth_seg0"
    using assms by(cases "m=n", auto dest!: dp0_add_chan_msgs dest: inv_authD)
qed

lemma inv_auth_add_loc[elim!]:
  assumes "dp0_add_loc s s' asid m" and "inv_auth s"
      and "pfragment (AInfo m) (rev (history m) @ future m) auth_seg0"
    shows "inv_auth s'"
proof(rule inv_authI)
  fix n
  assume "soup n s'"
  then show "pfragment (AInfo n) (rev (history n) @ future n) auth_seg0"
    using assms apply(cases "m=n", auto 3 4 simp add: dp0_add_loc_def dest: inv_authD)
    by (meson auth_path_def inv_auth_def soup_def)
qed

lemma Inv_inv_auth: "Inv dp0 inv_auth"
proof(rule Invariant_rule)
  fix s0
  show "init dp0 s0 \<Longrightarrow> inv_auth s0"
    by (auto simp add: dp0_def dp0_init_def intro!: inv_authI)
next
  fix s e s'
  show "\<lbrakk>dp0: s\<midarrow>e\<rightarrow> s'; inv_auth s\<rbrakk> \<Longrightarrow> inv_auth s'"
  proof (auto simp add: dp0_def elim!: dp0_trans.elims)
    fix m asid ainfo hf1 downif pas fut hist
    assume "inv_auth s" "dp0_recv s m asid ainfo hf1 downif pas fut hist s'" 
    then show "inv_auth s'"
      by(auto simp add: dp0_defs dp0_add_loc_def pfragment_def intro!: inv_authI dest!: inv_authD)
        (auto simp add: dp0_in_chan_def)
  qed(auto simp add: dp0_defs, auto intro: pfragment_prefix dest!: inv_authD)
qed


abbreviation TR_auth where "TR_auth \<equiv> 
  {\<tau> | \<tau> . \<forall> s . evt_observe0 s \<in> set \<tau> \<longrightarrow> inv_auth s}"

lemma tr0_satisfies_pathauthorization: "dp0 \<Turnstile>\<^sub>E\<^sub>S TR_auth"
  using Inv_inv_auth 
  apply(intro trace_property_rule[where ?I="\<lambda>\<tau> s. \<tau> \<in> TR_auth"])
  apply (auto elim!: InvE simp add: inv_auth_def)
  by(auto simp add: dp0_defs elim!: dp0_trans.elims)blast+

text\<open>Easier to read\<close>
definition inv_authorized :: "('aahi, 'ainfo) dp0_state \<Rightarrow> bool" where
  "inv_authorized s \<equiv> \<forall>m . soup m s \<longrightarrow> 
    (\<exists>timestamp auth_path. (timestamp, auth_path) \<in> auth_seg0 \<and>
      (\<exists>pre post. auth_path = pre @ (rev (history m)) @ post ))"

lemma "inv_auth s \<Longrightarrow> inv_authorized s"
  apply (auto simp add: inv_authorized_def inv_auth_def) 
  by (metis auth_path_def pfragment_def pfragment_prefix)+

(******************************************************************************)
subsection \<open>Detectability property\<close>
(******************************************************************************)

text\<open>The attacker sending a packet to another AS is not part of the real path.
However, the next hop's interface will point to the attacker AS (if the hop field is valid), thus
the attacker remains identifiable.\<close>

text\<open>Detectability, the first property: the past real path is a prefix of the past path\<close>
definition inv_detect :: "('aahi, 'ainfo) dp0_state \<Rightarrow> bool" where
  "inv_detect s \<equiv> \<forall>m . soup m s \<longrightarrow> prefix (history m) (past m)"

lemma inv_detectI: 
  assumes "\<And>m x . soup m s \<Longrightarrow> prefix (history m) (past m)" 
    shows "inv_detect s"
  using assms by(auto simp add: inv_detect_def)

lemma inv_detectD: 
  assumes "inv_detect s"
    shows "\<And>m x .m \<in> (loc s) x \<Longrightarrow> prefix (history m) (past m)" 
      and "\<And>m x .m \<in> (chan s) x \<Longrightarrow> prefix (history m) (past m)"
  using assms by(auto simp add: inv_detect_def) blast

lemma inv_detect_add_chan[elim!]:
  assumes "dp0_add_chan s s' asid upif m" "inv_detect s" "prefix (history m) (past m)"
  shows "inv_detect s'"
proof(rule inv_detectI)
  fix n
  assume "soup n s'"
  then show "prefix (history n) (past n)"
    using assms by(cases "m=n", auto dest!: dp0_add_chan_msgs dest: inv_detectD)
qed

lemma inv_detect_add_loc[elim!]:
  assumes "dp0_add_loc s s' asid m" "inv_detect s" "prefix (history m) (past m)"
  shows "inv_detect s'"
proof(rule inv_detectI)
  fix n
  assume "soup n s'"
  then show "prefix (history n) (past n)"
    using assms by(cases "m=n", auto 3 4 simp add: dp0_add_loc_def dest: inv_detectD)
qed

lemma Inv_inv_detect: "Inv dp0 inv_detect"
proof (rule InvI, erule reach.induct)
  fix s0
  show "init dp0 s0 \<Longrightarrow> inv_detect s0"
    by (auto simp add: dp0_def dp0_init_def intro!: inv_detectI)
  next
  fix s e s'
  show "\<lbrakk>dp0: s\<midarrow>e\<rightarrow> s'; inv_detect s\<rbrakk> \<Longrightarrow> inv_detect s'"
    by(auto simp add: dp0_defs elim!: dp0_trans.elims)
      (fastforce simp add: dp0_in_chan_def dest: inv_detectD)+
qed

abbreviation TR_detect where "TR_detect \<equiv> {\<tau> | \<tau> . \<forall> s . evt_observe0 s \<in> set \<tau>  \<longrightarrow> inv_detect s}"

lemma tr0_satisfies_detectability: "dp0 \<Turnstile>\<^sub>E\<^sub>S TR_detect"
  using Inv_inv_detect  
  by(intro trace_property_rule[where ?I="\<lambda>\<tau> s. \<tau> \<in> TR_detect"])
    (fastforce simp add: dp0_defs dp0_in_chan_def elim!: dp0_trans.elims dest: inv_detectD)+

end
end
