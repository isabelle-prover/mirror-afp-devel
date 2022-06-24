(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze, Christoph Sprenger
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)

section\<open>Intermediate Model\<close>
theory Parametrized_Dataplane_1
  imports
    "Parametrized_Dataplane_0"
    "infrastructure/Message"
begin

text\<open>This model is almost identical to the previous one. The only changes are (i) that the receive
event performs an interface check and (ii) that we permit the
attacker to send any packet with a future path whose interface-valid prefix is authorized, as 
opposed to requiring that the entire future path is authorized. This means that the attacker can 
combine hop fields of subsequent ASes as long as the combination is either authorized, or the 
interfaces of the two hop fields do not correspond to each other. In the latter case the packet will
not be delivered to (or accepted by) the second AS. 
Because (i) requires the @{text "evt_recv0"} event to check the interface over which packets are received,
in the mapping from this model to the abstract model we can thus cut off all invalid hop fields from
the future path.\<close>

type_synonym ('aahi, 'ainfo) dp1_state = "('aahi, 'ainfo) dp0_state"
type_synonym ('aahi, 'ainfo) pkt1 = "('aahi, 'ainfo) pkt0"
type_synonym ('aahi, 'ainfo) evt1 = "('aahi, 'ainfo) evt0"


context network_model
begin

(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)


definition
  dp1_dispatch_int
where
  "dp1_dispatch_int s m ainfo asid pas fut hist s' \<equiv>
    \<comment> \<open>guard: check that the future path is a fragment of an authorized segment. In reality,
        honest agents will always choose a path that is a prefix of an authorized segment, but for
        our models this difference is not significant.\<close>
    m = \<lparr> AInfo = ainfo, past = pas, future = fut, history = hist \<rparr> \<and>
    hist = [] \<and>
    pfragment ainfo (ifs_valid_prefix None fut None) auth_seg0 \<and>
    \<comment> \<open>action: Update the state to include m\<close>
    dp0_add_loc s s' asid m"

text\<open>We construct an artificial hop field that contains a specified asid and upif. The other fields
are irrelevant, as we only use this artificial hop field as "previous" hop field in the 
@{text "ifs_valid_prefix"} function. This is used in the direct dispatch event: the interface-valid prefix
must be authorized. Since the dispatching AS' own hop field is not part of the future path, but the AS
directly after the it does check for the interface correctness, we need this artificial hop
field.\<close>

abbreviation prev_hf where 
  "prev_hf asid upif \<equiv> 
   (Some \<lparr>UpIF = Some upif, DownIF = None, ASID = asid, \<dots> = undefined\<rparr>)"

definition
  dp1_dispatch_ext
where
  "dp1_dispatch_ext s m asid ainfo upif pas fut hist s' \<equiv>
    m = \<lparr> AInfo = ainfo, past = pas, future = fut, history = hist \<rparr> \<and>
    hist = [] \<and>
    pfragment ainfo (ifs_valid_prefix (prev_hf asid upif) fut None) auth_seg0 \<and>

    \<comment> \<open>action: Update state to include attacker message\<close>
    dp0_add_chan s s' asid upif m"

definition
  dp1_recv
where
  "dp1_recv s m asid ainfo hf1 downif pas fut hist s' \<equiv>
      DownIF hf1 = Some downif 
    \<and> dp0_recv s m asid ainfo hf1 downif pas fut hist s'"


(******************************************************************************)
subsection \<open>Transition system\<close>
(******************************************************************************)

fun dp1_trans where
  "dp1_trans s (evt_dispatch_int0 asid m) s' \<longleftrightarrow> 
    (\<exists>ainfo pas fut hist. dp1_dispatch_int s m ainfo asid pas fut hist s')" |
  "dp1_trans s (evt_dispatch_ext0 asid upif m) s' \<longleftrightarrow> 
    (\<exists>ainfo pas fut hist . dp1_dispatch_ext s m asid ainfo upif pas fut hist s')" |
  "dp1_trans s (evt_recv0 asid downif m) s' \<longleftrightarrow> 
    (\<exists>ainfo hf1 pas fut hist. dp1_recv s m asid ainfo hf1 downif pas fut hist s')" |
  "dp1_trans s e s' \<longleftrightarrow> dp0_trans s e s'"

definition dp1_init :: "('aahi, 'ainfo) dp1_state" where
  "dp1_init \<equiv> \<lparr>chan = (\<lambda>_. {}), loc = (\<lambda>_. {})\<rparr>"

definition dp1 :: "(('aahi, 'ainfo) evt1, ('aahi, 'ainfo) dp1_state) ES" where
  "dp1 \<equiv> \<lparr>
    init = (=) dp1_init,
    trans = dp1_trans
  \<rparr>"

lemmas dp1_trans_defs = dp0_trans_defs dp1_dispatch_ext_def dp1_recv_def
lemmas dp1_defs = dp1_def dp1_dispatch_int_def dp1_init_def dp1_trans_defs

fun pkt1to0chan :: "as \<Rightarrow> ifs \<Rightarrow> ('aahi, 'ainfo) pkt1 \<Rightarrow> ('aahi, 'ainfo) pkt0" where
  "pkt1to0chan asid upif \<lparr> AInfo = ainfo, past = pas, future = fut, history = hist \<rparr> = 
           \<lparr> pkt0.AInfo = ainfo, past = pas, future = ifs_valid_prefix (prev_hf asid upif) fut None, history = hist\<rparr>"

fun pkt1to0loc :: "('aahi, 'ainfo) pkt1 \<Rightarrow> ('aahi, 'ainfo) pkt0" where
  "pkt1to0loc \<lparr> AInfo = ainfo, past = pas, future = fut, history = hist \<rparr> = 
           \<lparr> pkt0.AInfo = ainfo, past = pas, future = ifs_valid_prefix None fut None, history = hist\<rparr>"

definition R10 :: "('aahi, 'ainfo) dp1_state \<Rightarrow> ('aahi, 'ainfo) dp0_state" where
  "R10 s = 
    \<lparr>chan = \<lambda>(a1, i1, a2, i2) . (pkt1to0chan a1 i1) ` ((chan s) (a1, i1, a2, i2)), 
      loc = \<lambda>x . pkt1to0loc ` ((loc s) x)\<rparr>"

fun \<pi>\<^sub>1 :: "('aahi, 'ainfo) evt1 \<Rightarrow> ('aahi, 'ainfo) evt0" where 
  "\<pi>\<^sub>1 (evt_dispatch_int0 asid m) = evt_dispatch_int0 asid (pkt1to0loc m)"
| "\<pi>\<^sub>1 (evt_recv0 asid downif m) = evt_recv0 asid downif (pkt1to0loc m)"
| "\<pi>\<^sub>1 (evt_send0 asid upif m) = evt_send0 asid upif (pkt1to0loc m)"
| "\<pi>\<^sub>1 (evt_deliver0 asid m) = evt_deliver0 asid (pkt1to0loc m)"
| "\<pi>\<^sub>1 (evt_dispatch_ext0 asid upif m) = evt_dispatch_ext0 asid upif (pkt1to0chan asid upif m)"
| "\<pi>\<^sub>1 (evt_observe0 s) = evt_observe0 (R10 s)"
| "\<pi>\<^sub>1 evt_skip0 = evt_skip0"

declare TW.takeW.elims[elim]

lemma dp1_refines_dp0: "dp1 \<sqsubseteq>\<^sub>\<pi>\<^sub>1 dp0"
proof(rule simulate_ES_fun[where ?h = R10])
  fix s0
  assume "init dp1 s0"
  then show "init dp0 (R10 s0)"
    by(auto simp add: dp0_defs dp1_defs R10_def) 
next
  fix s e s'
  assume "dp1: s\<midarrow>e\<rightarrow> s'"
  then show "dp0: R10 s\<midarrow> \<pi>\<^sub>1 e\<rightarrow> R10 s'"
  proof(auto simp add: dp1_def elim!: dp1_trans.elims dp0_trans.elims)
    fix m ainfo asid pas fut hist
    assume "dp1_dispatch_int s m ainfo asid pas fut hist s'" 
    then show "dp0: R10 s\<midarrow>evt_dispatch_int0 asid (pkt1to0loc m)\<rightarrow> R10 s'"
      by(auto 3 4 simp add: dp0_defs dp1_defs dp0_msgs R10_def 
                     intro: TW.takeW_prefix elim: pfragment_prefix' dest: strip_ifs_valid_prefix)
  next
    fix m asid ainfo hf1 downif pas fut hist
    assume "dp1_recv s m asid ainfo hf1 downif pas fut hist s'"
    then show "dp0: R10 s\<midarrow>evt_recv0 asid downif (pkt1to0loc m)\<rightarrow> R10 s'"
      by(auto simp add: dp0_defs dp1_defs dp0_msgs R10_def TW.takeW_split_tail 
              elim!: rev_image_eqI intro!: ext)
  next
    fix m asid ainfo hf1 upif pas fut hist
    assume "dp0_send s m asid ainfo hf1 upif pas fut hist s'" 
    then show "dp0: R10 s\<midarrow>evt_send0 asid upif (pkt1to0loc m)\<rightarrow> R10 s'"
      by(cases "ifs_valid_None_prefix (hf1 # fut)")
        (auto 3 4 simp add: dp0_defs dp1_defs dp0_msgs R10_def TW.takeW_split_tail TW.takeW.simps
                     elim!: rev_image_eqI TW.takeW.elims intro!: TW.takeW_pre_eqI) (*takes a few sec*)
  next
    fix m asid ainfo hf1 pas fut hist
    assume "dp0_deliver s m asid ainfo hf1 pas fut hist s'" 
    then show "dp0: R10 s\<midarrow>evt_deliver0 asid (pkt1to0loc m)\<rightarrow> R10 s'"
      by(auto simp add: dp0_defs dp1_defs dp0_msgs R10_def TW.takeW.simps
                intro!: ext elim!: rev_image_eqI TW.takeW.elims)
  qed(auto 3 4 simp add: dp0_defs dp1_defs dp0_msgs R10_def TW.takeW_split_tail)
qed

(******************************************************************************)
subsection \<open>Auxilliary definitions\<close>
(******************************************************************************)
text\<open>These definitions are not directly needed in the parametrized models, but they are useful for 
instances.\<close>

text\<open>Check if interface option is matched by a msgterm.\<close>
fun ASIF :: "ifs option \<Rightarrow> msgterm \<Rightarrow> bool" where
  "ASIF (Some a) (AS a') = (a=a')"
| "ASIF None \<epsilon> = True"
| "ASIF _ _ = False"

lemma ASIF_None[simp]: "ASIF ifopt \<epsilon> \<longleftrightarrow> ifopt = None" by(cases ifopt, auto)
lemma ASIF_AS[simp]: "ASIF ifopt (AS a) \<longleftrightarrow> ifopt = Some a" by(cases ifopt, auto)

text\<open>Turn a msgterm to an ifs option. Note that this maps both @{text "\<epsilon>"} (the msgterm denoting the lack of 
an interface) and arbitrary other msgterms that are not of the form "AS t" to None. The result may
thus be ambiguous. Use with care.\<close>
fun term2if :: "msgterm \<Rightarrow> ifs option" where
  "term2if (AS a) = Some a"
| "term2if \<epsilon> = None"
| "term2if _ = None" (*ambiguous!*)

lemma ASIF_term2if[intro]: "ASIF i mi \<Longrightarrow> ASIF (term2if mi) mi"
  by(cases mi, auto)

fun if2term :: "ifs option \<Rightarrow> msgterm" where "if2term (Some a) = AS a" | "if2term None = \<epsilon>"

lemma if2term_eq[elim]: "if2term a = if2term b \<Longrightarrow> a = b"
  apply(cases a, cases b, auto)
  using if2term.elims msgterm.distinct(1) 
  by (metis term2if.simps(1))

lemma term2if_if2termm[simp]: "term2if (if2term a) = a" apply(cases a) by auto

fun hf2term :: "ahi \<Rightarrow> msgterm" where
  "hf2term \<lparr>UpIF = upif, DownIF = downif, ASID = asid\<rparr> = L [if2term upif, if2term downif, Num asid]"

fun term2hf :: "msgterm \<Rightarrow> ahi" where
  "term2hf (L [upif, downif, Num asid]) = \<lparr>UpIF = term2if upif, DownIF = term2if downif, ASID = asid\<rparr>"

lemma term2hf_hf2term[simp]: "term2hf (hf2term hf) = hf" apply(cases hf) by auto

lemma ahi_eq:
  "\<lbrakk>ASID ahi' = ASID (ahi::ahi); ASIF (DownIF ahi') downif; ASIF (UpIF ahi') upif; 
    ASIF (DownIF ahi) downif; ASIF (UpIF ahi) upif\<rbrakk> \<Longrightarrow> ahi = ahi'"
  by(cases ahi, cases ahi')
    (auto elim: ASIF.elims ahi.cases)

end
end
