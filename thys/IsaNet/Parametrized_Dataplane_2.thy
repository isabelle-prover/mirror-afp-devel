(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze, Christoph Sprenger
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)

section\<open>Concrete Parametrized Model\<close>
text\<open>This is the refinement of the intermediate dataplane model. 
This model is parametric, and requires instantiation of the hop validation function, 
(and other parameters). We do so in the @{text "Parametrized_Dataplane_3_directed"} and
@{text "Parametrized_Dataplane_3_undirected"} models.
Nevertheless, this model contains the complete refinement proof, albeit the hard case, the refinement
of the attacker event, is assumed to hold. The crux of the refinement proof is thus shown in these 
directed/undirected instance models.
The definitions to be given by the instance are those of the locales @{text "dataplane_2_defs"} 
(which contains the basic definitions needed for the protocol, such as the verification of a hop field, 
called @{text "hf_valid_generic"}), and @{text "dataplane_2_ik_defs"} (containing the definition of 
components of the intruder knowledge).
The proof obligations are those in the locale @{text "dataplane_2"}.\<close>

theory Parametrized_Dataplane_2
  imports
    "Parametrized_Dataplane_1" "Network_Model"
begin

record ('aahi, 'uhi) HF =
  AHI :: "'aahi ahi_scheme"
  UHI :: "'uhi"
  HVF :: msgterm 

record ('aahi, 'uinfo, 'uhi, 'ainfo) pkt2 =
  AInfo :: 'ainfo
  UInfo :: "'uinfo"
  past  :: "('aahi, 'uhi) HF list"
  future  :: "('aahi, 'uhi) HF list"
  history  :: "'aahi ahi_scheme list"

text\<open>We use pkt2 instead of pkt, but otherwise the state remains unmodified in this model.\<close>
record ('aahi, 'uinfo, 'uhi, 'ainfo) dp2_state = 
  chan2 :: "(as \<times> ifs \<times> as \<times> ifs) \<Rightarrow> ('aahi, 'uinfo, 'uhi, 'ainfo) pkt2 set"
  loc2 :: "as \<Rightarrow> ('aahi, 'uinfo, 'uhi, 'ainfo) pkt2 set"

datatype ('aahi, 'uinfo, 'uhi, 'ainfo) evt2 = 
    evt_dispatch_int2 as "('aahi, 'uinfo, 'uhi, 'ainfo) pkt2" 
  | evt_recv2 as ifs "('aahi, 'uinfo, 'uhi, 'ainfo) pkt2" 
  | evt_send2 as ifs "('aahi, 'uinfo, 'uhi, 'ainfo) pkt2" 
  | evt_deliver2 as "('aahi, 'uinfo, 'uhi, 'ainfo) pkt2"
  | evt_dispatch_ext2 as ifs "('aahi, 'uinfo, 'uhi, 'ainfo) pkt2" 
  | evt_observe2 "('aahi, 'uinfo, 'uhi, 'ainfo) dp2_state"
  | evt_skip2

definition soup2 where "soup2 m s \<equiv> \<exists>x. m \<in> (loc2 s) x \<or> (\<exists>x. m \<in> (chan2 s) x)" 

declare soup2_def [simp]

fun fwd_pkt :: "('aahi, 'uinfo, 'uhi, 'ainfo) pkt2 \<Rightarrow> ('aahi, 'uinfo, 'uhi, 'ainfo) pkt2" where
  "fwd_pkt \<lparr> AInfo = ainfo, UInfo = uinfo, past = pas, future = hf1#fut, history = hist \<rparr> 
        = \<lparr> AInfo = ainfo, UInfo = uinfo, past = hf1#pas, future = fut, history = (AHI hf1)#hist \<rparr>"

(******************************************************************************)
subsection \<open>Hop validation check, authorized segments, and path extraction.\<close>
(******************************************************************************)
text\<open>First we define a locale that requires a number of functions. We will later extend this
to a locale @{text "dataplane_2"}, which makes assumptions on how these functions operate. We separate the 
assumptions in order to make use of some auxiliary definitions defined in this locale. \<close>
locale dataplane_2_defs = network_model _ auth_seg0
  for auth_seg0 :: "('ainfo \<times> 'aahi ahi_scheme list) set" +
\<comment> \<open>@{text "hf_valid_generic"} is the check that every hop performs. Besides the hop's own field, 
the check may require access to its neighboring hop fields as well as on @{text "ainfo"}, 
@{text "uinfo"} and the entire sequence of hop fields. 
Note that this check should include checking the validity of the info fields. Depending on the 
directed vs. undirected setting, this check may only have access to specific fields.\<close>
  fixes hf_valid_generic :: "'ainfo \<Rightarrow> 'uinfo
    \<Rightarrow> ('aahi, 'uhi) HF list
    \<Rightarrow> ('aahi, 'uhi) HF option 
    \<Rightarrow> ('aahi, 'uhi) HF
    \<Rightarrow> ('aahi, 'uhi) HF option \<Rightarrow> bool"
\<comment> \<open>@{text "hfs_valid_prefix_generic"} is the longest prefix of a given future path, such that 
@{text "hf_valid_generic"} passes for each hop field on the prefix.\<close>
  and hfs_valid_prefix_generic ::
    "'ainfo \<Rightarrow> 'uinfo
     \<Rightarrow> ('aahi, 'uhi) HF list
     \<Rightarrow> ('aahi, 'uhi) HF option
     \<Rightarrow> ('aahi, 'uhi) HF list
     \<Rightarrow> ('aahi, 'uhi) HF option \<Rightarrow> ('aahi, 'uhi) HF list"
\<comment> \<open>We need @{text "auth_restrict"} to further restrict the set of authorized segments. For instance,
   we need it for the empty segment (ainfo, []) since according to the definition any such
   ainfo will be contained in the intruder knowledge. With @{text "auth_restrict"} we can restrict this.\<close>
  and auth_restrict :: "'ainfo \<Rightarrow> 'uinfo \<Rightarrow> ('aahi, 'uhi) HF list \<Rightarrow> bool"
\<comment> \<open>@{text "extr"} extracts from a given hop validation field (@{text "HVF hf"}) the entire authenticated future path that 
is embedded in the HVF.\<close>
  and extr :: "msgterm \<Rightarrow> 'aahi ahi_scheme list"
\<comment> \<open>@{text "extr_ainfo"} extracts the authenticated info field (ainfo) from a given hop validation field.\<close>
  and extr_ainfo :: "msgterm \<Rightarrow> 'ainfo"
\<comment> \<open>@{text "term_ainfo"} extracts what msgterms the intruder can learn from analyzing a given 
authenticated info field.\<close>
  and term_ainfo :: "'ainfo \<Rightarrow> msgterm"
\<comment> \<open>@{text "terms_hf"} extracts what msgterms the intruder can learn from analyzing a given hop field; for instance,
the hop validation field HVF hf and the segment identifier UHI hf.\<close>
  and terms_hf :: "('aahi, 'uhi) HF \<Rightarrow> msgterm set"
\<comment> \<open>@{text "terms_uinfo"} extracts what msgterms the intruder can learn from analyzing a given uinfo field.\<close>
  and terms_uinfo :: "'uinfo \<Rightarrow> msgterm set"
\<comment> \<open>@{text "upd_uinfo"} takes a uinfo field an a hop field and returns the updated uinfo field.\<close>
  and upd_uinfo :: "'uinfo \<Rightarrow> ('aahi, 'uhi) HF \<Rightarrow> 'uinfo"
\<comment> \<open>As @{text "ik_oracle"} (defined below) gives the attacker direct access to hop validation fields 
that could be used to break the property, we have to either restrict the scope of the property, or 
restrict the attacker such that he cannot use the oracle-obtained hop validation fields in packets 
whose path origin matches the path origin of the oracle query. We choose the latter approach and 
fix a predicate @{text "no_oracle"} that tells us if the oracle has not been queried for a path 
origin (ainfo, uinfo combination). This is a prophecy variable.\<close>
  and no_oracle :: "'ainfo \<Rightarrow> 'uinfo \<Rightarrow> bool"

begin

(******************************************************************************)
subsubsection \<open>Auxiliary definitions and lemmas\<close>
(******************************************************************************)

text\<open>Define uinfo field updates.\<close>
fun upd_uinfo_pkt :: "('aahi, 'uinfo, 'uhi, 'ainfo) pkt2 \<Rightarrow> 'uinfo" where
  "upd_uinfo_pkt \<lparr> AInfo = ainfo, UInfo = uinfo, past = pas, future = hf1#fut, history = hist \<rparr> 
    = upd_uinfo uinfo hf1"
| "upd_uinfo_pkt \<lparr> AInfo = ainfo, UInfo = uinfo, past = pas, future = [], history = hist \<rparr> = uinfo"

definition upd_pkt :: "('aahi, 'uinfo, 'uhi, 'ainfo) pkt2 \<Rightarrow> ('aahi, 'uinfo, 'uhi, 'ainfo) pkt2" where
  "upd_pkt pkt = pkt\<lparr>UInfo := upd_uinfo_pkt pkt\<rparr>"

text \<open>This function maps hop fields of the dp2 format to hop fields of dp0 format.\<close>
definition AHIS :: "('aahi, 'uhi) HF list \<Rightarrow> 'aahi ahi_scheme list" where
  "AHIS hfs \<equiv> map AHI hfs"

declare AHIS_def[simp]

fun extr_from_hd :: "('aahi, 'uhi) HF list \<Rightarrow> 'aahi ahi_scheme list" where
    "extr_from_hd (hf#xs) = extr (HVF hf)"
  | "extr_from_hd _ = []"

fun extr_ainfoHd where
    "extr_ainfoHd (hf#xs) = Some (extr_ainfo (HVF hf))"
  | "extr_ainfoHd _ = None"


lemma prefix_AHIS:
  "prefix x1 x2 \<Longrightarrow> prefix (AHIS x1) (AHIS x2)"
  by (induction x1 arbitrary: x2 rule: list.induct) 
     (auto simp add: prefix_def)

lemma AHIS_set: "hf \<in> set (AHIS l) \<Longrightarrow> \<exists>hfc . hfc \<in> set l \<and> hf = AHI hfc"
  by(induction l) auto

lemma AHIS_set_rev: "\<lparr>AHI = ahi, UHI = uhi, HVF = x\<rparr> \<in> set hfs \<Longrightarrow> ahi \<in> set (AHIS hfs)"
  by(induction hfs, auto)

fun pkt2to1loc :: "('aahi, 'uinfo, 'uhi, 'ainfo) pkt2 \<Rightarrow> ('aahi, 'ainfo) pkt1" where
  "pkt2to1loc \<lparr> AInfo = ainfo, UInfo = uinfo, past = pas, future = fut, history = hist \<rparr> = 
           \<lparr> pkt0.AInfo = ainfo, 
             past = AHIS pas, 
             future = AHIS (hfs_valid_prefix_generic ainfo uinfo pas (head pas) fut None), 
             history = hist\<rparr>"

fun pkt2to1chan :: "('aahi, 'uinfo, 'uhi, 'ainfo) pkt2 \<Rightarrow> ('aahi, 'ainfo) pkt1" where
  "pkt2to1chan \<lparr> AInfo = ainfo, UInfo = uinfo, past = pas, future = fut, history = hist \<rparr> = 
           \<lparr> pkt0.AInfo = ainfo, 
             past = AHIS pas, 
             future = AHIS (hfs_valid_prefix_generic ainfo 
     (upd_uinfo_pkt \<lparr> AInfo = ainfo, UInfo = uinfo, past = pas, future = fut, history = hist \<rparr>) 
     pas (head pas) fut None), 
             history = hist\<rparr>"

abbreviation AHIo :: "('aahi, 'uhi) HF option \<Rightarrow> 'aahi ahi_scheme option" where
  "AHIo \<equiv> map_option AHI"

(******************************************************************************)
subsubsection \<open>Authorized segments\<close>
(******************************************************************************)

text \<open>Main definition of authorized up-segments. Makes sure that:
\begin{itemize}
\item the segment is rooted
\item the segment is terminated
\item the segment has matching interfaces
\item the projection to AS owners is an authorized segment in the abstract model. 
\end{itemize}\<close>
definition auth_seg2 :: "'uinfo \<Rightarrow> ('ainfo \<times> ('aahi, 'uhi) HF list) set" where
  "auth_seg2 uinfo \<equiv> ({(ainfo, l) | ainfo l . hfs_valid_prefix_generic ainfo uinfo [] None l None = l 
                                            \<and> auth_restrict ainfo uinfo l
                                            \<and> no_oracle ainfo uinfo
                                            \<and> (ainfo, AHIS l) \<in> auth_seg0})"

lemma auth_seg20:
  "(x, y) \<in> auth_seg2 uinfo \<Longrightarrow> (x, AHIS y) \<in> auth_seg0" by(auto simp add: auth_seg2_def)

lemma pfragment_auth_seg20:
  "pfragment ainfo l (auth_seg2 uinfo) \<Longrightarrow> pfragment ainfo (AHIS l) auth_seg0" 
  by (auto 3 4 simp add: pfragment_def map_append dest: auth_seg20)

lemma pfragment_auth_seg20':
  "\<lbrakk>pfragment ainfo l (auth_seg2 uinfo); l' = AHIS l\<rbrakk> \<Longrightarrow> pfragment ainfo l' auth_seg0" 
  using pfragment_auth_seg20 by blast

text \<open>This is a shortcut to denote adding a message to a local channel. \<close>
definition
  dp2_add_loc2 :: 
    "('aahi, 'uinfo, 'uhi, 'ainfo, 'more) dp2_state_scheme \<Rightarrow> 
     ('aahi, 'uinfo, 'uhi, 'ainfo, 'more) dp2_state_scheme \<Rightarrow> as \<Rightarrow> ('aahi, 'uinfo, 'uhi, 'ainfo) pkt2 \<Rightarrow> bool"
where 
  "dp2_add_loc2 s s' asid pkt \<equiv> s' = s\<lparr>loc2 := (loc2 s)(asid := loc2 s asid \<union> {pkt})\<rparr>"

text \<open>This is a shortcut to denote adding a message to an inter-AS channel. Note that it requires 
the link to exist.\<close>
definition
  dp2_add_chan2 :: 
    "('aahi, 'uinfo, 'uhi, 'ainfo, 'more) dp2_state_scheme \<Rightarrow> ('aahi, 'uinfo, 'uhi, 'ainfo, 'more) dp2_state_scheme
                       \<Rightarrow> as \<Rightarrow> ifs \<Rightarrow> ('aahi, 'uinfo, 'uhi, 'ainfo) pkt2 \<Rightarrow> bool"
where 
  "dp2_add_chan2 s s' a1 i1 pkt \<equiv> 
    \<exists>a2 i2 . rev_link a1 i1 = (Some a2, Some i2) \<and>
    s' = s\<lparr>chan2 := (chan2 s)((a1, i1, a2, i2) := chan2 s (a1, i1, a2, i2) \<union> {pkt})\<rparr>"

text \<open>This is a shortcut to denote receiving a message from an inter-AS channel. Note that it requires 
the link to exist.\<close>
definition
  dp2_in_chan2 :: "('aahi, 'uinfo, 'uhi, 'ainfo, 'more) dp2_state_scheme \<Rightarrow> as \<Rightarrow> ifs \<Rightarrow> ('aahi, 'uinfo, 'uhi, 'ainfo) pkt2 \<Rightarrow> bool"
where 
  "dp2_in_chan2 s a1 i1 pkt \<equiv> 
    \<exists>a2 i2 . rev_link a1 i1 = (Some a2, Some i2) \<and>
    pkt \<in> (chan2 s)(a2, i2, a1, i1)"

lemmas dp2_msgs = dp2_add_loc2_def dp2_add_chan2_def dp2_in_chan2_def


end
(******************************************************************************)
subsection \<open>Intruder Knowledge definition\<close>
(******************************************************************************)
print_locale dataplane_2_defs
locale dataplane_2_ik_defs = dataplane_2_defs _ _ _ _ hf_valid_generic _ _ _ _ _ _ _ upd_uinfo
  for hf_valid_generic :: "'ainfo \<Rightarrow> 'uinfo
    \<Rightarrow> ('aahi, 'uhi) HF list 
    \<Rightarrow> ('aahi, 'uhi) HF option 
    \<Rightarrow> ('aahi, 'uhi) HF
    \<Rightarrow> ('aahi, 'uhi) HF option \<Rightarrow> bool"
  and upd_uinfo :: "'uinfo \<Rightarrow> ('aahi, 'uhi) HF \<Rightarrow> 'uinfo" +
\<comment> \<open>@{text "ik_add"} is Additional Intruder Knowledge, such as hop authenticators in EPIC L1.\<close>
fixes ik_add :: "msgterm set"
\<comment> \<open>@{text "ik_oracle"} is another type of additional Intruder Knowledge. We use it to model the attacker's
ability to brute-force individual hop validation fields and segment identifiers.\<close>
  and ik_oracle :: "msgterm set"
begin

text\<open>This set should contain all terms that can be learned from analyzing a hop field, in particular
the content of the HVF and UHI fields but not the uinfo field (see below).\<close>
definition ik_hfs :: "msgterm set" where
  "ik_hfs = {t | t hf hfs ainfo uinfo. t \<in> terms_hf hf \<and> hf \<in> set hfs \<and> (ainfo, hfs) \<in> (auth_seg2 uinfo)}"

text\<open>This set should contain all terms that can be learned from analyzing the uinfo field.\<close>
definition ik_uinfo :: "msgterm set" where
  "ik_uinfo = {t | ainfo hfs uinfo t. t \<in> terms_uinfo uinfo \<and> (ainfo, hfs) \<in> (auth_seg2 uinfo)}"

declare ik_hfs_def[simp] ik_uinfo_def[simp] (*undeclared later, useful to prevent unfolding*)

definition ik :: "msgterm set" where
  "ik = ik_hfs
      \<union> {term_ainfo ainfo | ainfo hfs uinfo. (ainfo, hfs) \<in> (auth_seg2 uinfo)}
      \<union> ik_uinfo
      \<union> Key`(macK`bad)
      \<union> ik_add
      \<union> ik_oracle"

definition terms_pkt :: "('aahi, 'uinfo, 'uhi, 'ainfo) pkt2 \<Rightarrow> msgterm set" where 
  "terms_pkt m \<equiv> {t | t hf. t \<in> terms_hf hf \<and> hf \<in> set (past m) \<union> set (future m)}
               \<union> {term_ainfo ainfo | ainfo . ainfo = AInfo m}
               \<union> \<Union>{terms_uinfo uinfo | uinfo . uinfo = UInfo m}"

text \<open>Intruder knowledge. We make a simplifying assumption about the attacker's passive capabilities:
        In contrast to his ability to insert messages (which is restricted to the locality of ASes
        that are compromised, i.e. in the set 'bad', the attacker has global eavesdropping abilities.
        This simplifies modelling and does not make the proofs more difficult, while providing stronger
        guarantees.
        We will later prove that the Dolev-Yao closure of @{term "ik_dyn"} remains constant, i.e., 
        the attacker does not learn anything new by observing messages on the network 
        (see @{text "Inv_inv_ik_dyn"}).\<close>
definition ik_dyn  :: "('aahi, 'uinfo, 'uhi, 'ainfo, 'more) dp2_state_scheme \<Rightarrow> msgterm set" where
  "ik_dyn s \<equiv> ik \<union> (\<Union>{terms_pkt m | m x . m \<in> loc2 s x}) \<union> (\<Union>{terms_pkt m | m x . m \<in> chan2 s x})"

text\<open>Different way of presenting the intruder knowledge\<close>
definition ik_dynamic  :: "('aahi, 'uinfo, 'uhi, 'ainfo, 'more) dp2_state_scheme \<Rightarrow> msgterm set" where
  "ik_dynamic s \<equiv> ik \<union> (\<Union>{terms_pkt m | m . soup2 m s})"

lemma "ik_dynamic s = ik_dyn s" 
  apply(auto simp add: ik_dyn_def ik_dynamic_def) 
  by metis+

lemma ik_dyn_mono: "\<lbrakk>x \<in> ik_dyn s; \<And>m . soup2 m s \<Longrightarrow> soup2 m s'\<rbrakk> \<Longrightarrow> x \<in> ik_dyn s'"
  by (auto simp add: ik_dyn_def) metis+

lemma ik_info[elim]:
  "(ainfo, hfs) \<in> (auth_seg2 uinfo) \<Longrightarrow> term_ainfo ainfo \<in> synth (analz ik)"
  by(auto simp add: ik_def)blast

lemma ik_ik_hfs: "t \<in> ik_hfs \<Longrightarrow> t \<in> ik" by(auto simp add: ik_def)

(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

text\<open>This is an attacker event.\<close>
text\<open>The attacker is allowed to send any message that he can derive from his intruder knowledge,
except for messages whose path origin he has queried the oracle for.\<close>
definition
  dp2_dispatch_int
where
  "dp2_dispatch_int s m ainfo uinfo asid pas fut hist s' \<equiv>
    m = \<lparr> AInfo = ainfo, UInfo = uinfo, past = pas, future = fut, history = hist \<rparr> \<and>
    hist = [] \<and>
    terms_pkt m \<subseteq> synth (analz (ik_dyn s)) \<and>
    no_oracle ainfo uinfo \<and>
    \<comment> \<open>action: Update the state to include m\<close>
    dp2_add_loc2 s s' asid m"

definition
  dp2_recv
where
  "dp2_recv s m asid ainfo uinfo hf1 downif pas fut hist s' \<equiv>
    \<comment> \<open>guard: a packet with valid interfaces and valid validation fields is in the incoming channel.\<close>
    m = \<lparr> AInfo = ainfo, UInfo = uinfo, past = pas, future = hf1#fut, history = hist \<rparr> \<and>
    dp2_in_chan2 s (ASID (AHI hf1)) downif m \<and>
    DownIF (AHI hf1) = Some downif \<and>
    ASID (AHI hf1) = asid \<and>
    hf_valid_generic ainfo (upd_uinfo uinfo hf1) (rev(pas)@hf1#fut) (head pas) hf1 (head fut) \<and>

    \<comment> \<open>action: Update local state to include message\<close>
    dp2_add_loc2 s s' asid (upd_pkt m)"

definition
  dp2_send
where
  "dp2_send s m asid ainfo uinfo hf1 upif pas fut hist s' \<equiv>
    \<comment> \<open>guard: forward the packet on the external channel and advance the path by one hop.\<close>
    m = \<lparr> AInfo = ainfo, UInfo = uinfo, past = pas, future = hf1#fut, history = hist \<rparr> \<and>
    m \<in> (loc2 s) asid \<and>
    UpIF (AHI hf1) = Some upif \<and>
    ASID (AHI hf1) = asid \<and>
    hf_valid_generic ainfo uinfo (rev(pas)@hf1#fut) (head pas) hf1 (head fut) \<and>

    \<comment> \<open>action: Update state to include modified message\<close>
    dp2_add_chan2 s s' asid upif \<lparr>
                AInfo = ainfo,
                UInfo = uinfo,
                past = hf1 # pas,
                future = fut,
                history = AHI hf1 # hist
              \<rparr>"

definition
  dp2_deliver
where
  "dp2_deliver s m asid ainfo uinfo hf1 pas fut hist s' \<equiv>
    m = \<lparr> AInfo = ainfo, UInfo = uinfo, past = pas, future = hf1#fut, history = hist \<rparr> \<and>
    m \<in> (loc2 s) asid \<and>
    ASID (AHI hf1) = asid \<and>
    fut = [] \<and>
    hf_valid_generic ainfo uinfo (rev(pas)@hf1#fut) (head pas) hf1 (head fut) \<and>

    \<comment> \<open>action: Update state to include modified message\<close>
    dp2_add_loc2 s s' asid 
              \<lparr>
                AInfo = ainfo,
                UInfo = uinfo,
                past = hf1 # pas,
                future = [],
                history = (AHI hf1) # hist
              \<rparr>"

text\<open>This is an attacker event.\<close>
text\<open>The attacker is allowed to send any message that he can derive from his intruder knowledge,
except for messages whose path origin he has queried the oracle for.\<close>
definition
  dp2_dispatch_ext
where
  "dp2_dispatch_ext s m asid ainfo uinfo upif pas fut hist s' \<equiv>
    m = \<lparr> AInfo = ainfo, UInfo = uinfo, past = pas, future = fut, history = hist \<rparr> \<and>
    asid \<in> bad \<and>
    hist = [] \<and>
    terms_pkt m \<subseteq> synth (analz (ik_dyn s)) \<and>
    no_oracle ainfo uinfo \<and>

    \<comment> \<open>action\<close>
    dp2_add_chan2 s s' asid upif m"

(******************************************************************************)
subsection \<open>Transition system\<close>
(******************************************************************************)

fun dp2_trans where
  "dp2_trans s (evt_dispatch_int2 asid m) s' \<longleftrightarrow> 
    (\<exists>ainfo uinfo pas fut hist . dp2_dispatch_int s m ainfo uinfo asid pas fut hist s')" |
  "dp2_trans s (evt_recv2 asid downif m) s' \<longleftrightarrow> 
    (\<exists>ainfo uinfo hf1 pas fut hist . dp2_recv s m asid ainfo uinfo hf1 downif pas fut hist s')" |
  "dp2_trans s (evt_send2 asid upif m) s' \<longleftrightarrow> 
    (\<exists>ainfo uinfo hf1 pas fut hist. dp2_send s m asid ainfo uinfo hf1 upif pas fut hist s')" |
  "dp2_trans s (evt_deliver2 asid m) s' \<longleftrightarrow> 
    (\<exists>ainfo uinfo hf1 pas fut hist. dp2_deliver s m asid ainfo uinfo hf1 pas fut hist s')" |
  "dp2_trans s (evt_dispatch_ext2 asid upif m) s' \<longleftrightarrow> 
    (\<exists>ainfo uinfo pas fut hist . dp2_dispatch_ext s m asid ainfo uinfo upif pas fut hist s')" |
  "dp2_trans s (evt_observe2 s'') s' \<longleftrightarrow> s = s' \<and> s = s''" |
  "dp2_trans s evt_skip2 s' \<longleftrightarrow> s = s'"

definition dp2_init :: "('aahi, 'uinfo, 'uhi, 'ainfo) dp2_state" where
  "dp2_init \<equiv> \<lparr>chan2 = (\<lambda>_. {}), loc2 = (\<lambda>_. {})\<rparr>"

definition dp2 :: "(('aahi, 'uinfo, 'uhi, 'ainfo) evt2, ('aahi, 'uinfo, 'uhi, 'ainfo) dp2_state) ES" where
  "dp2 \<equiv> \<lparr>
    init = (=) dp2_init,
    trans = dp2_trans
  \<rparr>"

lemmas dp2_trans_defs = dp2_dispatch_int_def dp2_recv_def dp2_send_def dp2_deliver_def dp2_dispatch_ext_def
lemmas dp2_defs = dp2_def dp2_init_def dp2_trans_defs

end

(******************************************************************************)
subsection \<open>Assumptions of the parametrized model\<close>
(******************************************************************************)
text\<open>We now list the assumptions of this parametrized model. \<close>

print_locale dataplane_2_ik_defs
locale dataplane_2 = dataplane_2_ik_defs _ _ _ _ _ _ _ _ _ _ _ _ hf_valid_generic upd_uinfo _ _
  for hf_valid_generic :: "'ainfo \<Rightarrow> 'uinfo
    \<Rightarrow> ('aahi, 'uhi) HF list 
    \<Rightarrow> ('aahi, 'uhi) HF option 
    \<Rightarrow> ('aahi, 'uhi) HF
    \<Rightarrow> ('aahi, 'uhi) HF option \<Rightarrow> bool"
  and upd_uinfo :: "'uinfo \<Rightarrow> ('aahi, 'uhi) HF \<Rightarrow> 'uinfo" + 
(*
removed
\<And>hf . hf \<in> set hfs \<Longrightarrow> terms_hf hf \<subseteq> synth (analz ik); term_ainfo ainfo \<in> synth (analz ik);*)
assumes ik_seg_is_auth:
  "\<lbrakk>terms_pkt m \<subseteq> synth (analz ik); 
    future m = hfs; AInfo m = ainfo;
    nxt = None; no_oracle ainfo uinfo\<rbrakk>
  \<Longrightarrow> pfragment ainfo
            (ifs_valid_prefix prev'
              (AHIS (hfs_valid_prefix_generic ainfo uinfo pas pre hfs nxt))
             None)
                auth_seg0" (*prev' vs prev?*)
and upd_uinfo_ik: 
  "\<lbrakk>terms_uinfo uinfo \<subseteq> synth (analz ik); terms_hf hf \<subseteq> synth (analz ik)\<rbrakk> 
  \<Longrightarrow> terms_uinfo (upd_uinfo uinfo hf) \<subseteq> synth (analz ik)"
(*"terms_uinfo (UInfo m) \<subseteq> synth (analz ik) \<Longrightarrow> terms_uinfo (upd_uinfo_pkt m) \<subseteq> synth (analz ik)"*)
and upd_uinfo_no_oracle: "no_oracle ainfo uinfo \<Longrightarrow> no_oracle ainfo (upd_uinfo uinfo fld)"

\<comment> \<open>We require that @{text "hfs_valid_prefix_generic"} behaves as expected, i.e., that it implements
the check mentioned above.\<close>
and prefix_hfs_valid_prefix_generic: 
  "prefix (hfs_valid_prefix_generic ainfo uinfo pas pre fut nxt) fut"
and cons_hfs_valid_prefix_generic: 
  "\<lbrakk>hf_valid_generic ainfo uinfo hfs (head pas) hf1 (head fut); hfs = (rev pas)@hf1 #fut;
    m = \<lparr>AInfo = ainfo, UInfo = uinfo, past = pas, future = hf1 # fut, history = hist\<rparr>\<rbrakk>
\<Longrightarrow> hfs_valid_prefix_generic ainfo uinfo pas (head pas) (hf1 # fut) None = 
    hf1 # (hfs_valid_prefix_generic ainfo (upd_uinfo_pkt (fwd_pkt m)) (hf1#pas) (Some hf1) fut None)"
begin

(******************************************************************************)
subsection \<open>Mapping dp2 state to dp1 state\<close>
(******************************************************************************)

definition R21 :: "('aahi, 'uinfo, 'uhi, 'ainfo) dp2_state \<Rightarrow> ('aahi, 'ainfo) dp1_state" where
  "R21 s = \<lparr>chan = \<lambda>x . pkt2to1chan ` ((chan2 s) x), 
            loc = \<lambda>x . pkt2to1loc ` ((loc2 s) x)\<rparr>"

lemma auth_seg2_pfragment: 
  "\<lbrakk>pfragment ainfo (hf # fut) (auth_seg2 uinfo); AHIS (hf # fut) = x # xs\<rbrakk>
    \<Longrightarrow> pfragment ainfo (x # xs) auth_seg0"
  by(auto simp add: map_append auth_seg2_def pfragment_def)

lemma dp2_in_chan2_to_0E[elim]:
  "\<lbrakk>dp2_in_chan2 s1 a1 i1 pkt2; pkt2to1chan pkt2 = pkt0; s0 = R21 s1\<rbrakk> \<Longrightarrow> 
    dp0_in_chan s0 a1 i1 pkt0"
  by(auto simp add: R21_def dp2_in_chan2_def dp0_in_chan_def)

lemma dp2_in_loc2_to_0E[elim]:
  "\<lbrakk>pkt2 \<in> (loc2 s1) asid; pkt2to1loc pkt2 = pkt0; P = pkt2to1loc ` loc2 s1 asid\<rbrakk> \<Longrightarrow> 
    pkt0 \<in> P"
  by blast

lemma dp2_add_loc20E:
 "\<lbrakk>dp2_add_loc2 s1 s1' asid p1; p0 = pkt2to1loc p1; s0 = R21 s1; s0' = R21 s1'\<rbrakk>
    \<Longrightarrow> dp0_add_loc s0 s0' asid p0"
  by(auto simp add: R21_def dp2_add_loc2_def dp0_add_loc_def intro!: ext)

lemma dp2_add_chan20E:
 "\<lbrakk>dp2_add_chan2 s1 s1' a1 i1 p1; p0 = pkt2to1chan p1; s0 = R21 s1; s0' = R21 s1'\<rbrakk>
    \<Longrightarrow> dp0_add_chan s0 s0' a1 i1 p0"
  by(fastforce simp add: R21_def dp2_add_chan2_def dp0_add_chan_def)


(******************************************************************************)
subsection\<open>Invariant: Derivable Intruder Knowledge is constant under @{text "dp2_trans"}\<close>
(******************************************************************************)

text \<open>Derivable Intruder Knowledge stays constant throughout all reachable states\<close>
definition inv_ik_dyn :: "('aahi, 'uinfo, 'uhi, 'ainfo) dp2_state \<Rightarrow> bool" where
 "inv_ik_dyn s \<equiv> ik_dyn s \<subseteq> synth (analz ik)"

lemma inv_ik_dynI: 
  assumes "\<And>t m x . \<lbrakk>t \<in> terms_pkt m; m \<in> loc2 s x\<rbrakk> \<Longrightarrow> t \<in> synth (analz ik)"
  and     "\<And>t m x . \<lbrakk>t \<in> terms_pkt m; m \<in> chan2 s x\<rbrakk> \<Longrightarrow> t \<in> synth (analz ik)"
shows "inv_ik_dyn s"
  using assms by(auto simp add: ik_dyn_def inv_ik_dyn_def)

lemma inv_ik_dynD: 
  assumes "inv_ik_dyn s"
  shows "\<And>t m x . \<lbrakk>m \<in> chan2 s x; t \<in> terms_pkt m\<rbrakk> \<Longrightarrow> t \<in> synth (analz ik)"
        "\<And>t m x . \<lbrakk>m \<in> loc2 s x; t \<in> terms_pkt m\<rbrakk> \<Longrightarrow> t \<in> synth (analz ik)"
  using assms 
  by(auto simp add: ik_dyn_def inv_ik_dyn_def Union_eq dest!: subsetD intro!: exI) (*takes a few sec*)

lemmas inv_ik_dynE = inv_ik_dynD[elim_format]

lemma inv_ik_dyn_add_loc2[elim!]: 
  "\<lbrakk>dp2_add_loc2 s s' asid m; inv_ik_dyn s; terms_pkt m \<subseteq> synth (analz ik)\<rbrakk>
    \<Longrightarrow> inv_ik_dyn s'"
      by(auto simp add: dp2_add_loc2_def intro!: inv_ik_dynI elim: inv_ik_dynE)

lemma inv_ik_dyn_add_chan2[elim!]: 
  "\<lbrakk>dp2_add_chan2 s s' a1 i1 m; inv_ik_dyn s; terms_pkt m \<subseteq> synth (analz ik)\<rbrakk>
    \<Longrightarrow> inv_ik_dyn s'"
    by(auto simp add: dp2_add_chan2_def intro!: inv_ik_dynI elim: inv_ik_dynE)
                  
lemma inv_ik_dyn_ik_dyn_ik[simp]: 
  assumes "inv_ik_dyn s" shows "synth (analz (ik_dyn s)) = synth (analz ik)" 
proof-
  from assms have "ik_dyn s \<subseteq> synth (analz ik)" by(auto simp add: ik_dyn_def inv_ik_dyn_def)
  moreover have "ik \<subseteq> ik_dyn s" by(auto simp add: ik_dyn_def)
  ultimately show ?thesis using analz_idem analz_synth order_class.order.antisym sup.absorb2 
                                synth_analz_mono synth_idem synth_increasing by metis
qed

lemma terms_pkt_upd: 
  "\<lbrakk>x \<in> terms_pkt (upd_pkt p); \<And>x. x \<in> terms_pkt p \<Longrightarrow> x \<in> synth (analz ik)\<rbrakk> \<Longrightarrow> x \<in> synth (analz ik)"
  apply(cases p)   
  subgoal for AInfo UInfo past future history 
    by(cases future) 
      (auto simp add: upd_pkt_def terms_pkt_def elim!: upd_uinfo_ik[THEN subsetD, rotated 2])
  done

lemma Inv_inv_ik_dyn: "reach dp2 s \<Longrightarrow> inv_ik_dyn s"
proof(induction s rule: reach.induct)
  case (reach_init s)
  then show ?case
    by (auto simp add: inv_ik_dyn_def dp2_defs ik_dyn_def)
next
  case (reach_trans s e s')
  then show ?case
(*  proof(auto simp add: dp2_def elim!: dp2_trans.elims)
    apply(simp add: dp2_def) 
    apply(elim dp2_trans.elims exE sym[of s, elim_format] sym[of s', elim_format])
    apply(simp_all)
*)
  proof(simp add: dp2_def, elim dp2_trans.elims exE sym[of s, elim_format] sym[of s', elim_format],
        simp_all)
    fix m ainfo uinfo asid pas fut hist
    assume "inv_ik_dyn s" "dp2_dispatch_int s m ainfo uinfo asid pas fut hist s'"
    then show "inv_ik_dyn s'"
      by(auto simp add: dp2_defs)
  next
    fix m asid ainfo uinfo hf1 downif pas fut hist
    assume "inv_ik_dyn s" "dp2_recv s m asid ainfo uinfo hf1 downif pas fut hist s'"
    then show "inv_ik_dyn s'" 
      by(auto simp add: dp2_defs dp2_in_chan2_def elim: terms_pkt_upd dest: inv_ik_dynD(1))
  next
    fix m asid ainfo uinfo upif pas fut hist
    assume "inv_ik_dyn s" "dp2_dispatch_ext s m asid ainfo uinfo upif pas fut hist s'"
    then show "inv_ik_dyn s'"
      by(auto simp add: dp2_defs)
  qed(auto simp add: dp2_defs terms_pkt_def elim!: inv_ik_dynE)
qed


(******************************************************************************)
subsubsection\<open>Attacker dispatch events also capture honest dispatchers\<close>
(******************************************************************************)

text\<open>This lemma shows that our definition of @{text "dp2_dispatch_int"} also works for honest senders.
All packets than an honest sender would send are authorized. According to the definition of the intruder 
knowledge, they are then also derivable from the intruder knowledge. Hence, an honest sender can
send packets with authorized segments. However, the restriction on @{text "no_oracle"} remains.\<close>

lemma dp2_dispatch_int_also_works_for_honest:
  assumes "pfragment ainfo fut (auth_seg2 uinfo)" "past m = []" "AInfo m = ainfo" "UInfo m = uinfo"
          "future m = fut"
    shows "terms_pkt m \<subseteq> synth (analz (ik_dyn s))"
proof-
  from assms have "terms_pkt m \<subseteq> ik"
    by (cases m)
       (auto 3 4 simp add: terms_pkt_def ik_def)
  then show ?thesis by (auto simp add: ik_dyn_def)
qed


(******************************************************************************)
subsection\<open>Refinement proof\<close>
(******************************************************************************)

fun \<pi>\<^sub>2 :: "('aahi, 'uinfo, 'uhi, 'ainfo) evt2 \<Rightarrow> ('aahi, 'ainfo) evt0" where 
  "\<pi>\<^sub>2 (evt_dispatch_int2 asid m) = evt_dispatch_int0 asid (pkt2to1loc m)"
| "\<pi>\<^sub>2 (evt_recv2 asid downif m) = evt_recv0 asid downif (pkt2to1chan m)"
| "\<pi>\<^sub>2 (evt_send2 asid upif m) = evt_send0 asid upif (pkt2to1loc m)"
| "\<pi>\<^sub>2 (evt_deliver2 asid m) = evt_deliver0 asid (pkt2to1loc m)"
| "\<pi>\<^sub>2 (evt_dispatch_ext2 asid upif m) = evt_dispatch_ext0 asid upif (pkt2to1chan m)"
| "\<pi>\<^sub>2 (evt_observe2 s) = evt_observe0 (R21 s)"
| "\<pi>\<^sub>2 evt_skip2 = evt_skip0"

lemma dp2_refines_dp1: "dp2 \<sqsubseteq>\<^sub>\<pi>\<^sub>2 dp1"
proof(rule simulate_ES_fun_with_invariant[where ?I = inv_ik_dyn, where ?h = R21])
  fix s0
  assume "init dp2 s0"
  then show "init dp1 (R21 s0)"
    by(auto simp add: R21_def dp1_defs dp2_defs) 
next
  fix s e s'
  assume "dp2: s\<midarrow>e\<rightarrow> s'" and "inv_ik_dyn s"
  then show "dp1: R21 s\<midarrow>\<pi>\<^sub>2 e\<rightarrow> R21 s'"
  proof(auto simp add: dp2_def elim!: dp2_trans.elims)
    fix m ainfo uinfo asid hf pas fut hist
    assume "dp2_dispatch_int s m ainfo uinfo asid pas fut hist s'"
    then show "dp1: R21 s\<midarrow>evt_dispatch_int0 asid (pkt2to1loc m)\<rightarrow> R21 s'"
      by(auto simp add: dp1_defs dp2_defs \<open>inv_ik_dyn s\<close> simp del: AHIS_def
              intro!: ik_seg_is_auth elim!: dp2_add_loc20E)
    next
    fix m asid ainfo uinfo hf1 downif pas fut hist
    assume "dp2_recv s m asid ainfo uinfo hf1 downif pas fut hist s'"
    then show "dp1: R21 s\<midarrow>evt_recv0 asid downif (pkt2to1chan m)\<rightarrow> R21 s'"
      apply(auto simp add: TW.takeW_split_tail dp1_defs dp2_defs terms_pkt_def
                 elim!: dp2_in_chan2_to_0E dp2_add_loc20E intro: head.cases[where ?x=fut] 
                 intro!: exI[of _ "AHI hf1"])
      apply(rule exI[of _ "AHIS (hfs_valid_prefix_generic ainfo (upd_uinfo_pkt (fwd_pkt (upd_pkt m))) (hf1#pas) (Some hf1) fut None)"])
      apply auto
      subgoal 
        thm cons_hfs_valid_prefix_generic[where ?uinfo ="upd_uinfo _ _", where ?hist = hist]
        apply(frule cons_hfs_valid_prefix_generic[where ?uinfo ="upd_uinfo _ _", where ?hist = hist]) 
        by (auto simp add: upd_pkt_def) 
      apply(auto simp add: TW.takeW_split_tail dp1_defs dp2_defs terms_pkt_def
                 elim!: dp2_in_chan2_to_0E dp2_add_loc20E intro: head.cases[where ?x=fut])
      apply(frule cons_hfs_valid_prefix_generic[where ?uinfo ="upd_uinfo _ _", where ?hist = hist]) 
      by (auto simp add: upd_pkt_def) 
  next
    fix m asid ainfo uinfo hf1 upif pas fut hist
    assume "dp2_send s m asid ainfo uinfo hf1 upif pas fut hist s'"
    then show "dp1: R21 s\<midarrow>evt_send0 asid upif (pkt2to1loc m)\<rightarrow> R21 s'"
      using cons_hfs_valid_prefix_generic 
      by(auto simp add: dp1_defs dp2_defs TW.takeW_split_tail R21_def elim!: dp2_add_chan20E)
  next
    fix m asid ainfo uinfo hf1 pas fut hist
    assume asm: "dp2_deliver s m asid ainfo uinfo hf1 pas fut hist s'"
    then show "dp1: R21 s\<midarrow>evt_deliver0 asid (pkt2to1loc m)\<rightarrow> R21 s'"
      apply(auto simp add: R21_def TW.takeW.simps TW.takeW_split_tail dp1_defs dp2_defs 
                  elim!: dp2_add_loc20E intro: head.cases[where ?x=fut] intro!: exI[of _ "AHI hf1"])
      using prefix_hfs_valid_prefix_generic cons_hfs_valid_prefix_generic head.simps(1) prefix_Nil
    proof -
      assume a1: "hf_valid_generic ainfo uinfo (rev pas @ [hf1]) (head pas) hf1 None"
      have "hfs_valid_prefix_generic ainfo (upd_uinfo_pkt (fwd_pkt m)) (hf1 # pas) (Some hf1) [] None = []"
        by (meson prefix_Nil prefix_hfs_valid_prefix_generic)
      then show "map AHI (hfs_valid_prefix_generic ainfo uinfo pas (head pas) [hf1] None) = [AHI hf1]"
        using a1 asm by (simp add: cons_hfs_valid_prefix_generic dp2_defs)
    qed blast
  next
    fix m asid ainfo uinfo upif pas fut hist
    assume "dp2_dispatch_ext s m asid ainfo uinfo upif pas fut hist s'"
    then show "dp1: R21 s\<midarrow>evt_dispatch_ext0 asid upif (pkt2to1chan m)\<rightarrow> R21 s'"
      apply(auto simp add: dp1_defs dp2_defs \<open>inv_ik_dyn s\<close> upd_uinfo_no_oracle simp del: AHIS_def
              intro!: ik_seg_is_auth elim!: dp2_add_chan20E)
      apply(cases fut)
      by(auto simp add: upd_uinfo_no_oracle)
  qed(auto simp add: R21_def dp2_defs dp1_defs)
next
  fix s
  show "reach dp2 s \<longrightarrow> inv_ik_dyn s" using Inv_inv_ik_dyn by blast
qed

subsection\<open>Property preservation\<close>

text\<open>The following property is weaker than @{text "TR_auth"} in that it does not include the
future path. However, this is inconsequential, since we only included the future path in order for
the original invariant to be inductive. The actual path authorization property only requires the
history to be authorized.
We remove the future path for clarity, as including it would require us to also restrict it using
the interface- and cryptographic valid-prefix functions.\<close>

definition auth_path2 :: "('aahi, 'uinfo, 'uhi, 'ainfo) pkt2 \<Rightarrow> bool" where
  "auth_path2 m \<equiv> pfragment (AInfo m) (rev (history m)) auth_seg0"

abbreviation TR_auth2_hist :: "('aahi, 'uinfo, 'uhi, 'ainfo) evt2 list set" where "TR_auth2_hist \<equiv> 
  {\<tau> | \<tau> . \<forall>s m . evt_observe2 s \<in> set \<tau> \<and> soup2 m s \<longrightarrow> auth_path2 m}"

lemma evt_observe2_0:
  "evt_observe2 s \<in> set \<tau> \<Longrightarrow> evt_observe0 (R10 (R21 s)) \<in> (\<lambda>x. \<pi>\<^sub>1 (\<pi>\<^sub>2 x)) ` set \<tau>"
  by force

declare soup2_def [simp del]
declare soup_def [simp del]

lemma loc2to0: "\<lbrakk>mc \<in> loc2 sc x; sa = R10 (R21 sc); ma = pkt1to0loc (pkt2to1loc mc)\<rbrakk> \<Longrightarrow> ma \<in> loc sa x"
  using R10_def R21_def by simp

lemma chan2to0: "\<lbrakk>mc \<in> chan2 sc (a1, i1, a2, i2); sa = R10 (R21 sc); ma = pkt1to0chan a1 i1 (pkt2to1chan mc)\<rbrakk> 
  \<Longrightarrow> ma \<in> chan sa (a1, i1, a2, i2)"
  using R10_def R21_def by simp

lemma loc2to0_auth: 
  "\<lbrakk>mc \<in> loc2 sc x; sa = R10 (R21 sc); ma = pkt1to0loc (pkt2to1loc mc); auth_path ma\<rbrakk> \<Longrightarrow> auth_path2 mc"
  apply(auto simp add: R10_def R21_def auth_path_def auth_path2_def elim!: pfragmentE) 
  subgoal for zs1 zs2
    by(cases mc)
      (auto intro!: pfragmentI[of _ zs1 _ "pkt0.future (pkt1to0loc (pkt2to1loc mc)) @ zs2"])
  done

lemma chan2to0_auth: 
  "\<lbrakk>mc \<in> chan2 sc (a1, i1, a2, i2); sa = R10 (R21 sc); ma = pkt1to0chan a1 i1 (pkt2to1chan mc); auth_path ma\<rbrakk> \<Longrightarrow> auth_path2 mc"
  apply(auto simp add: R10_def R21_def auth_path_def auth_path2_def elim!: pfragmentE) 
  subgoal for zs1 zs2
    by(cases mc)
      (auto intro!: pfragmentI[of _ zs1 _ "pkt0.future (pkt1to0chan a1 i1 (pkt2to1chan mc)) @ zs2"])
  done

lemma tr2_satisfies_pathauthorization: "dp2 \<Turnstile>\<^sub>E\<^sub>S TR_auth2_hist"
  apply(rule property_preservation[where \<pi>="\<pi>\<^sub>1 o \<pi>\<^sub>2", where E=dp2, where F=dp0, where P=TR_auth])
  using dp2_refines_dp1 dp1_refines_dp0 sim_ES_trans apply blast
  using tr0_satisfies_pathauthorization apply blast
  apply (auto simp del: soup2_def)
  subgoal for \<tau> s m
    apply(auto elim!: allE[of _ "R10 (R21 s)"]) apply force
    apply(auto simp add: soup2_def)
    subgoal
      apply(frule loc2to0_auth) using loc2to0 
      by(auto simp add: soup_def inv_auth_def elim!: allE)
    subgoal
      apply(frule chan2to0_auth) using chan2to0 
      by(fastforce simp add: soup_def inv_auth_def elim!: allE)+
    done
  done


definition inv_detect2 :: "('aahi, 'uinfo, 'uhi, 'ainfo) dp2_state \<Rightarrow> bool" where
  "inv_detect2 s \<equiv> \<forall>m . soup2 m s \<longrightarrow> prefix (history m) (AHIS (past m))"

abbreviation TR_detect2 where "TR_detect2 \<equiv> {\<tau> | \<tau> . \<forall> s . evt_observe2 s \<in> set \<tau>  \<longrightarrow> inv_detect2 s}"

lemma tr2_satisfies_detectability: "dp2 \<Turnstile>\<^sub>E\<^sub>S TR_detect2"
  apply(rule property_preservation[where \<pi>="\<pi>\<^sub>1 o \<pi>\<^sub>2", where E=dp2, where F=dp0, where P=TR_detect])
  using dp2_refines_dp1 dp1_refines_dp0 sim_ES_trans apply blast
  using tr0_satisfies_detectability apply blast
  apply (auto simp add: inv_detect2_def)
  subgoal for \<tau> s m
  apply(auto simp add: soup2_def inv_detect_def)
    apply(auto elim!: allE[of _ "R10 (R21 s)"]) 
    subgoal using evt_observe2_0 by blast
    subgoal
      apply(auto elim!: allE[of _ "(pkt1to0loc (pkt2to1loc m))"])
      using loc2to0 soup_def apply blast
      apply(cases m) 
      by auto
    subgoal using evt_observe2_0 by blast
    subgoal for a1 i1
      apply(auto elim!: allE[of _ "(pkt1to0chan a1 i1 (pkt2to1chan m))"])
      using chan2to0 soup_def apply blast
      apply(cases m) 
      by auto
    done
  done

end
end
