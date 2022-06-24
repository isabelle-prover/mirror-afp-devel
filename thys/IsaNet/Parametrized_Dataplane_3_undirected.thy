(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze, Christoph Sprenger
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)

section\<open>Parametrized dataplane protocol for undirected protocols\<close>
text\<open>This is an instance of the @{text "Parametrized_Dataplane_2"} model, specifically for protocols
that authorize paths in an undirected fashion. We specialize the @{text "hf_valid_generic"} check
to a still parametrized, but more concrete @{text "hf_valid"} check. The rest of the parameters 
remain abstract until a later instantiation with a concrete protocols (see the instances directory).

While both the models for undirected and directed protocols import assumptions from the theory
@{text "Network_Assumptions"}, they differ in strength: the assumptions made by undirected protocols
are strictly weaker, since the entire forwarding path is authorized by each AS, and not only the 
future path from the perspective of each AS. 
In addition, the specific conditions that instances have to verify differs between the undirected
and the directed setting (compare the locales @{text "dataplane_3_undirected"} and 
@{text "dataplane_3_directed"}).

This explains the need to split up the verification of the attacker event into two theories. Despite
the differences that concrete protocols may exhibit, these two theories suffice to show the crux
of the refinement proof. The instances merely have to show a set of static conditions.

Note that we don't use the update function in the undirected setting, since none of the instances
require it.\<close>

theory Parametrized_Dataplane_3_undirected
  imports
    "Parametrized_Dataplane_2" "Network_Assumptions"
begin

type_synonym UINFO = "msgterm"

(******************************************************************************)
subsection \<open>Hop validation check, authorized segments, and path extraction.\<close>
(******************************************************************************)
text\<open>First we define a locale that requires a number of functions. We will later extend this
to a locale @{text "dataplane_3_undirected"}, which makes assumptions on how these functions operate. 
We separate the assumptions in order to make use of some auxiliary definitions defined in this locale.\<close>
locale dataplane_3_undirected_defs = network_assums_undirect _ _ _ auth_seg0
  for auth_seg0 :: "('ainfo \<times> 'aahi ahi_scheme list) set" +
\<comment> \<open>@{text "hf_valid"} is the check that every hop performs on its own and the entire path as well as on
ainfo and uinfo. Note that this includes checking the validity of the info fields.\<close>
  fixes hf_valid :: "'ainfo \<Rightarrow> UINFO
    \<Rightarrow> ('aahi, 'uhi) HF list 
    \<Rightarrow> ('aahi, 'uhi) HF 
    \<Rightarrow> bool"
\<comment> \<open>We need @{text "auth_restrict"} to further restrict the set of authorized segments. For instance,
   we need it for the empty segment (ainfo, []) since according to the definition any such
   ainfo will be contained in the intruder knowledge. With @{text "auth_restrict"} we can restrict this.\<close>
  and auth_restrict :: "'ainfo \<Rightarrow> UINFO \<Rightarrow> ('aahi, 'uhi) HF list \<Rightarrow> bool"
\<comment> \<open>extr extracts from a given hop validation field (HVF hf) the entire authenticated future path that 
is embedded in the HVF.\<close>
  and extr :: "msgterm \<Rightarrow> 'aahi ahi_scheme list"
\<comment> \<open>@{text "extr_ainfo"} extracts the authenticated info field (ainfo) from a given hop validation field.\<close>
  and extr_ainfo :: "msgterm \<Rightarrow> 'ainfo"
\<comment> \<open>@{text "term_ainfo"} extracts what msgterms the intruder can learn from analyzing a given 
authenticated info field. Note that currently we do not have a similar function for the 
unauthenticated info field @{text "uinfo"}. Protocols should thus only use that field with terms
that the intruder can already synthesize (such as Numbers).\<close>
  and term_ainfo :: "'ainfo \<Rightarrow> msgterm"
\<comment> \<open>@{text "terms_hf"} extracts what msgterms the intruder can learn from analyzing a given hop field; for instance,
the hop validation field HVF hf and the segment identifier UHI hf.\<close>
  and terms_hf :: "('aahi, 'uhi) HF \<Rightarrow> msgterm set"
\<comment> \<open>@{text "terms_uinfo"} extracts what msgterms the intruder can learn from analyzing a given uinfo field.\<close>
  and terms_uinfo :: "UINFO \<Rightarrow> msgterm set"
\<comment> \<open>As @{text "ik_oracle"} (defined below) gives the attacker direct access to hop validation fields 
that could be used to break the property, we have to either restrict the scope of the property, or 
restrict the attacker such that he cannot use the oracle-obtained hop validation fields in packets 
whose path origin matches the path origin of the oracle query. We choose the latter approach and 
fix a predicate @{text "no_oracle"} that tells us if the oracle has not been queried for a path 
origin (ainfo, uinfo combination). This is a prophecy variable.\<close>
  and no_oracle :: "'ainfo \<Rightarrow> UINFO \<Rightarrow> bool"

begin

abbreviation upd_uinfo :: "UINFO \<Rightarrow> ('aahi, 'uhi) HF \<Rightarrow> UINFO" where 
  "upd_uinfo u hf \<equiv> u"

abbreviation hf_valid_generic :: "'ainfo \<Rightarrow> msgterm
    \<Rightarrow> ('aahi, 'uhi) HF list
    \<Rightarrow> ('aahi, 'uhi) HF option 
    \<Rightarrow> ('aahi, 'uhi) HF
    \<Rightarrow> ('aahi, 'uhi) HF option \<Rightarrow> bool" where
  "hf_valid_generic ainfo uinfo hfs pre hf nxt \<equiv> hf_valid ainfo uinfo hfs hf"

abbreviation hfs_valid_prefix where 
  "hfs_valid_prefix ainfo uinfo pas fut \<equiv> (takeWhile (\<lambda>hf . hf_valid ainfo uinfo (rev(pas)@fut) hf) fut)"

definition hfs_valid_prefix_generic ::
      "'ainfo \<Rightarrow> msgterm \<Rightarrow> ('aahi, 'uhi) HF list \<Rightarrow> ('aahi, 'uhi) HF option \<Rightarrow> ('aahi, 'uhi) HF list \<Rightarrow> 
      ('aahi, 'uhi) HF option \<Rightarrow> ('aahi, 'uhi) HF list"where
  "hfs_valid_prefix_generic ainfo uinfo pas pre fut nxt \<equiv> 
   hfs_valid_prefix ainfo uinfo pas fut"

declare hfs_valid_prefix_generic_def[simp]

sublocale dataplane_2_defs _ _ _ auth_seg0 hf_valid_generic hfs_valid_prefix_generic 
  auth_restrict extr extr_ainfo term_ainfo terms_hf terms_uinfo upd_uinfo
  apply unfold_locales done

lemma auth_seg2_elem: "\<lbrakk>(ainfo, hfs) \<in> auth_seg2 uinfo; hf \<in> set hfs\<rbrakk> 
  \<Longrightarrow> \<exists>uinfo . hf_valid ainfo uinfo hfs hf \<and> auth_restrict ainfo uinfo hfs \<and> (ainfo, AHIS hfs) \<in> auth_seg0"
  by (auto simp add: auth_seg2_def TW.holds_takeW_is_identity dest!: TW.holds_set_list)

end

print_locale dataplane_3_undirected_defs
locale dataplane_3_undirected_ik_defs = dataplane_3_undirected_defs _ _ _ _ hf_valid auth_restrict 
     extr extr_ainfo term_ainfo terms_hf _ for 
        hf_valid :: "'ainfo \<Rightarrow> UINFO \<Rightarrow> ('aahi, 'uhi) HF list \<Rightarrow> ('aahi, 'uhi) HF \<Rightarrow> bool"
    and auth_restrict :: "'ainfo => UINFO \<Rightarrow> ('aahi, 'uhi) HF list \<Rightarrow> bool"
    and extr :: "msgterm \<Rightarrow> 'aahi ahi_scheme list"
    and extr_ainfo :: "msgterm \<Rightarrow> 'ainfo"
    and term_ainfo :: "'ainfo \<Rightarrow> msgterm"
    and terms_hf :: "('aahi, 'uhi) HF \<Rightarrow> msgterm set"
 +
\<comment> \<open>@{text "ik_add"} is Additional Intruder Knowledge, such as hop authenticators in EPIC L1.\<close>
fixes ik_add :: "msgterm set"
\<comment> \<open>@{text "ik_oracle"} is another type of additional Intruder Knowledge. We use it to model the attacker's
ability to brute-force individual hop validation fields and segment identifiers.\<close>
  and ik_oracle :: "msgterm set"
begin

lemma prefix_hfs_valid_prefix_generic: 
  "prefix (hfs_valid_prefix_generic ainfo uinfo pas pre fut nxt) fut"
  apply(simp add: hfs_valid_prefix_generic_def)
  by (metis prefixI takeWhile_dropWhile_id)

lemma cons_hfs_valid_prefix_generic: 
  "\<lbrakk>hf_valid_generic ainfo uinfo hfs (head pas) hf1 (head fut); hfs = (rev pas)@hf1 #fut\<rbrakk>
\<Longrightarrow> hfs_valid_prefix_generic ainfo uinfo pas (head pas) (hf1 # fut) None = 
    hf1 # (hfs_valid_prefix_generic ainfo uinfo (hf1#pas) (Some hf1) fut None)"
  by(auto simp add: TW.takeW_split_tail)

print_locale dataplane_2_ik_defs
sublocale dataplane_2_ik_defs _ _ _ _ hfs_valid_prefix_generic auth_restrict extr extr_ainfo term_ainfo 
  terms_hf _ no_oracle hf_valid_generic upd_uinfo ik_add ik_oracle
  by unfold_locales
end

(******************************************************************************)
subsection \<open>Conditions of the parametrized model\<close>
(******************************************************************************)
text\<open>We now list the assumptions of this parametrized model. \<close>

print_locale dataplane_3_undirected_ik_defs
locale dataplane_3_undirected = dataplane_3_undirected_ik_defs _ _ _ _ terms_uinfo no_oracle hf_valid auth_restrict extr 
       extr_ainfo term_ainfo terms_hf ik_add ik_oracle
    for hf_valid :: "'ainfo \<Rightarrow> msgterm \<Rightarrow> ('aahi, 'uhi) HF list \<Rightarrow> ('aahi, 'uhi) HF \<Rightarrow> bool"
    and auth_restrict :: "'ainfo => UINFO \<Rightarrow> ('aahi, 'uhi) HF list \<Rightarrow> bool"
    and extr :: "msgterm \<Rightarrow> 'aahi ahi_scheme list"
    and extr_ainfo :: "msgterm \<Rightarrow> 'ainfo"
    and term_ainfo :: "'ainfo \<Rightarrow> msgterm"
    and terms_uinfo :: "UINFO \<Rightarrow> msgterm set"
    and ik_add :: "msgterm set"
    and terms_hf :: "('aahi, 'uhi) HF \<Rightarrow> msgterm set"
    and ik_oracle :: "msgterm set"
    and no_oracle :: "'ainfo \<Rightarrow> UINFO \<Rightarrow> bool" +

\<comment> \<open>A valid validation field that is contained in ik corresponds to an authorized hop field.
   (The notable exceptions being oracle-obtained validation fields.)
   This relates the result of @{text "terms_hf"} to its argument. @{text "terms_hf"} has to produce a msgterm that is either
   unique for each given hop field x, or it is only produced by an 'equivalence class' of hop fields
   such that either all of the hop fields of the class are authorized, or none are.
   While the extr function (constrained by assumptions below) also binds the hop information to the
   validation field, it does so only for AHI and AInfo, but not for UHI.\<close>
    assumes COND_terms_hf:
    "\<lbrakk>hf_valid ainfo uinfo l hf; terms_hf hf \<subseteq> analz ik; no_oracle ainfo uinfo; hf \<in> set l\<rbrakk>
      \<Longrightarrow> \<exists>hfs . hf \<in> set hfs \<and> (\<exists>uinfo' . (ainfo, hfs) \<in> (auth_seg2 uinfo'))"
\<comment> \<open>A valid validation field that can be synthesized from the initial intruder knowledge is already
    contained in the initial intruder knowledge if it belongs to an honest AS. This can be combined
   with the previous assumption.\<close> 
    and COND_honest_hf_analz: 
    "\<lbrakk>ASID (AHI hf) \<notin> bad; hf_valid ainfo uinfo l hf; terms_hf hf \<subseteq> synth (analz ik);
      no_oracle ainfo uinfo; hf \<in> set l\<rbrakk>
      \<Longrightarrow> terms_hf hf \<subseteq> analz ik"
\<comment> \<open>Each valid hop field contains the entire path.\<close> 
    and COND_extr:
    "\<lbrakk>hf_valid ainfo uinfo l hf\<rbrakk> \<Longrightarrow> extr (HVF hf) = AHIS l"
\<comment> \<open>A valid hop field is only valid for one specific uinfo.\<close>
    and COND_hf_valid_uinfo:
    "\<lbrakk>hf_valid ainfo uinfo l hf; hf_valid ainfo' uinfo' l' hf\<rbrakk> 
    \<Longrightarrow> uinfo' = uinfo"
begin

(*we prove this for all ainfo (but at most one of them will fit)*)
(*the case distinctions we make on whether the owner of the first hf is an adversary: this is the AS *AFTER*
the AS that sent the packet (the sender AS we know to be malicious as per the evt_dispatch_ext2 event). *)
text\<open>This is the central lemma that we need to prove to show the refinement between this model and 
dp1. It states: If an attacker can synthesize a segment from his knowledge, and does not use a path
origin that was used to query the oracle, then the valid prefix of the segment is authorized. Thus,
the attacker cannot create any valid but unauthorized segments.\<close>
lemma ik_seg_is_auth:
  assumes "terms_pkt m \<subseteq> synth (analz ik)" and 
          "future m = fut" and "AInfo m = ainfo" and "nxt = None" and "no_oracle ainfo uinfo"
  shows "pfragment ainfo
              (AHIS (hfs_valid_prefix ainfo uinfo pas fut))
                auth_seg0" 
proof-
  let ?hfsvalid = "hfs_valid_prefix ainfo uinfo pas fut"
  let ?AHIS = "AHIS ?hfsvalid"
(*  let ?ifsvalid = "ifs_valid_prefix (Some prev') ?AHIS None"*)
  show ?thesis
proof(cases "\<exists>hfhonest \<in> set ?AHIS . ASID hfhonest \<notin> bad")
  case True
  then obtain hfhonesta where hfhonesta_def: "hfhonesta \<in> set ?AHIS" "ASID hfhonesta \<notin> bad" by auto
  then obtain hfhonestc where hfhonestc_def: 
    "hfhonestc \<in> set ?hfsvalid" "hfhonesta = AHI hfhonestc" "ASID (AHI hfhonestc) \<notin> bad"
    by(auto dest: AHIS_set)
  then have hfhonestc_valid: "hf_valid ainfo uinfo (rev(pas)@fut) hfhonestc" using hfhonesta_def
    by (meson set_takeWhileD)
  have hfhonestc_fut: "hfhonestc \<in> set fut" using hfhonestc_def(1) using set_takeWhileD by fastforce
  from hfhonestc_valid hfhonestc_def have "terms_hf hfhonestc \<subseteq> analz ik"
    apply(elim COND_honest_hf_analz[where l="(rev(pas)@fut)"])
    using assms hfhonesta_def set_takeWhileD
    apply(auto simp add: terms_pkt_def)
    by force+
  then obtain hfshonest uinfo' where hfshonest_def: "hfhonestc \<in> set hfshonest" "(ainfo, hfshonest) \<in> auth_seg2 uinfo'" 
    using hfhonestc_valid
    apply-
    apply(drule COND_terms_hf) using assms apply auto
    using hfhonestc_valid hfhonestc_fut by auto
  then obtain uinfo' where hfhonestc_valid':
    "hf_valid ainfo uinfo' hfshonest hfhonestc" by(auto simp add: auth_seg2_def)
  then have uinfo'_uinfo[simp]:"uinfo' = uinfo" using hfhonestc_valid COND_hf_valid_uinfo by simp
  then have AHIS_hfshonest[simp]: "AHIS hfshonest = AHIS (rev(pas)@fut)" 
    using hfhonestc_valid hfhonestc_valid' by(auto dest!: COND_extr)
  show ?thesis 
    using hfshonest_def[simplified] 
    apply(auto simp add: auth_seg2_def pfragment_def simp del: AHIS_def map_append)
    using takeWhile_dropWhile_id map_append AHIS_def by metis
next
  case False
  then show ?thesis 
    by (auto intro!: pfragment_self ASM_adversary)
qed
qed

lemma upd_uinfo_pkt_id[simp]: "upd_uinfo_pkt pkt = UInfo pkt"
  apply(cases pkt)
  subgoal for _ _ _ hfs
    apply(cases hfs) 
    by auto
  done

print_locale dataplane_2
sublocale dataplane_2  _ _ _ _ hfs_valid_prefix_generic _ _ _ _ _ _ no_oracle _ _ hf_valid_generic upd_uinfo
  apply unfold_locales
  using prefix_hfs_valid_prefix_generic
  by (auto simp add: ik_seg_is_auth strip_ifs_valid_prefix simp del: AHIS_def)

end
end
