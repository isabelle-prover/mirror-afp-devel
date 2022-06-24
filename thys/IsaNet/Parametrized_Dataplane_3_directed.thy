(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze, Christoph Sprenger
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)

section\<open>Parametrized dataplane protocol for directed protocols\<close>
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
of the refinement proof. The instances merely have to show a set of static conditions\<close>

theory Parametrized_Dataplane_3_directed
  imports
    "Parametrized_Dataplane_2" "Network_Assumptions" "infrastructure/Take_While_Update"
begin

(******************************************************************************)
subsection \<open>Hop validation check, authorized segments, and path extraction.\<close>
(******************************************************************************)
text\<open>First we define a locale that requires a number of functions. We will later extend this
to a locale @{text "dataplane_3_directed"}, which makes assumptions on how these functions operate. 
We separate the assumptions in order to make use of some auxiliary definitions defined in this locale. \<close>
locale dataplane_3_directed_defs = network_assums_direct _ _ _ auth_seg0
  for auth_seg0 :: "('ainfo \<times> 'aahi ahi_scheme list) set" +
\<comment> \<open>@{text "hf_valid"} is the check that every hop performs on its own and next hop field as well as on
ainfo and uinfo. Note that this includes checking the validity of the info fields. \<close>
  fixes hf_valid :: "'ainfo \<Rightarrow> 'uinfo
    \<Rightarrow> ('aahi, 'uhi) HF
    \<Rightarrow> ('aahi, 'uhi) HF option \<Rightarrow> bool"
\<comment> \<open>We need @{text "auth_restrict"} to further restrict the set of authorized segments. For instance,
   we need it for the empty segment (ainfo, []) since according to the definition any such
   ainfo will be contained in the intruder knowledge. With @{text "auth_restrict"} we can restrict this.\<close>
  and auth_restrict :: "'ainfo \<Rightarrow> 'uinfo \<Rightarrow> ('aahi, 'uhi) HF list \<Rightarrow> bool"
\<comment> \<open>extr extracts from a given hop validation field (HVF hf) the entire authenticated future path that 
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
\<comment> \<open>@{text "upd_uinfo"} returns the updated uinfo field of a packet.\<close>
  and upd_uinfo :: "'uinfo \<Rightarrow> ('aahi, 'uhi) HF \<Rightarrow> 'uinfo"
\<comment> \<open>As @{text "ik_oracle"} (defined below) gives the attacker direct access to hop validation fields 
that could be used to break the property, we have to either restrict the scope of the property, or 
restrict the attacker such that he cannot use the oracle-obtained hop validation fields in packets 
whose path origin matches the path origin of the oracle query. We choose the latter approach and 
fix a predicate @{text "no_oracle"} that tells us if the oracle has not been queried for a path 
origin (ainfo, uinfo combination). This is a prophecy variable.\<close>
  and no_oracle :: "'ainfo \<Rightarrow> 'uinfo \<Rightarrow> bool"
begin

abbreviation hf_valid_generic :: "'ainfo \<Rightarrow> 'uinfo
    \<Rightarrow> ('aahi, 'uhi) HF list
    \<Rightarrow> ('aahi, 'uhi) HF option 
    \<Rightarrow> ('aahi, 'uhi) HF
    \<Rightarrow> ('aahi, 'uhi) HF option \<Rightarrow> bool" where
  "hf_valid_generic ainfo uinfo pas pre hf nxt \<equiv> hf_valid ainfo uinfo hf nxt"

definition hfs_valid_prefix_generic ::
      "'ainfo \<Rightarrow> 'uinfo \<Rightarrow> ('aahi, 'uhi) HF list \<Rightarrow> ('aahi, 'uhi) HF option \<Rightarrow> ('aahi, 'uhi) HF list \<Rightarrow> 
      ('aahi, 'uhi) HF option \<Rightarrow> ('aahi, 'uhi) HF list"where
  "hfs_valid_prefix_generic ainfo uinfo pas pre fut nxt \<equiv> 
  TWu.takeW (\<lambda> uinfo hf nxt . hf_valid ainfo uinfo hf nxt) upd_uinfo uinfo fut nxt"

declare hfs_valid_prefix_generic_def[simp]


sublocale dataplane_2_defs _ _ _ auth_seg0 hf_valid_generic hfs_valid_prefix_generic 
  auth_restrict extr extr_ainfo term_ainfo terms_hf terms_uinfo upd_uinfo
  apply unfold_locales done

abbreviation hfs_valid where 
  "hfs_valid ainfo uinfo l nxt \<equiv> TWu.holds (hf_valid ainfo) upd_uinfo uinfo l nxt"

abbreviation hfs_valid_prefix where   
  "hfs_valid_prefix ainfo uinfo l nxt \<equiv> TWu.takeW (hf_valid ainfo) upd_uinfo uinfo l nxt"

abbreviation hfs_valid_None where
  "hfs_valid_None ainfo uinfo l \<equiv> hfs_valid ainfo uinfo l None"

abbreviation hfs_valid_None_prefix where
  "hfs_valid_None_prefix ainfo uinfo l \<equiv> hfs_valid_prefix ainfo uinfo l None"

(*same as TWu.upds with P and upd parameters given*)
abbreviation upds_uinfo where
  "upds_uinfo \<equiv> foldl upd_uinfo"

abbreviation upds_uinfo_shifted where
  "upds_uinfo_shifted uinfo l nxt \<equiv> TWu.upd_shifted upd_uinfo uinfo l nxt"

end

print_locale dataplane_3_directed_defs
locale dataplane_3_directed_ik_defs = dataplane_3_directed_defs _ _ _ _ hf_valid auth_restrict 
     extr extr_ainfo term_ainfo terms_hf _ upd_uinfo for 
        hf_valid :: "'ainfo \<Rightarrow> 'uinfo \<Rightarrow> ('aahi, 'uhi) HF \<Rightarrow> ('aahi, 'uhi) HF option \<Rightarrow> bool"
    and auth_restrict :: "'ainfo => 'uinfo \<Rightarrow> ('aahi, 'uhi) HF list \<Rightarrow> bool"
    and extr :: "msgterm \<Rightarrow> 'aahi ahi_scheme list"
    and extr_ainfo :: "msgterm \<Rightarrow> 'ainfo"
    and term_ainfo :: "'ainfo \<Rightarrow> msgterm"
    and terms_hf :: "('aahi, 'uhi) HF \<Rightarrow> msgterm set"
    and upd_uinfo :: "'uinfo \<Rightarrow> ('aahi, 'uhi) HF \<Rightarrow> 'uinfo"
 +
\<comment> \<open>@{text "ik_add"} is Additional Intruder Knowledge, such as hop authenticators in EPIC L1.\<close>
fixes ik_add :: "msgterm set"
\<comment> \<open>@{text "ik_oracle"} is another type of additional Intruder Knowledge. We use it to model the attacker's
ability to brute-force individual hop validation fields and segment identifiers.\<close>
  and ik_oracle :: "msgterm set"
begin

lemma auth_seg2_elem: "\<lbrakk>(ainfo, hfs) \<in> (auth_seg2 uinfo); hf \<in> set hfs\<rbrakk> 
  \<Longrightarrow> \<exists>nxt uinfo'. hf_valid ainfo uinfo' hf nxt \<and> auth_restrict ainfo uinfo hfs \<and> (ainfo, AHIS hfs) \<in> auth_seg0"
  by (auto simp add: auth_seg2_def TWu.holds_takeW_is_identity dest!: TWu.holds_set_list)

lemma prefix_hfs_valid_prefix_generic: 
  "prefix (hfs_valid_prefix_generic ainfo uinfo pas pre fut nxt) fut"
  by(auto intro: TWu.takeW_prefix)

lemma cons_hfs_valid_prefix_generic: 
  "\<lbrakk>hf_valid_generic ainfo uinfo hfs (head pas) hf1 (head fut); hfs = (rev pas)@hf1 #fut;
    m = \<lparr>AInfo = ainfo, UInfo = uinfo, past = pas, future = hf1 # fut, history = hist\<rparr>\<rbrakk>
\<Longrightarrow> hfs_valid_prefix_generic ainfo uinfo pas (head pas) (hf1 # fut) None = 
    hf1 # (hfs_valid_prefix_generic ainfo (upd_uinfo_pkt (fwd_pkt m)) (hf1#pas) (Some hf1) fut None)"
  apply auto
  apply(cases fut)
  apply auto
  by (auto simp add: TWu.takeW.simps)

print_locale dataplane_2_ik_defs
sublocale dataplane_2_ik_defs _ _ _ _ hfs_valid_prefix_generic auth_restrict extr extr_ainfo term_ainfo 
  terms_hf _ no_oracle hf_valid_generic upd_uinfo ik_add ik_oracle
  by unfold_locales
end

(******************************************************************************)
subsection \<open>Conditions of the parametrized model\<close>
(******************************************************************************)
text\<open>We now list the assumptions of this parametrized model. \<close>

print_locale dataplane_3_directed_ik_defs
locale dataplane_3_directed = dataplane_3_directed_ik_defs _ _ _ _ _ no_oracle hf_valid auth_restrict 
  extr extr_ainfo term_ainfo _ upd_uinfo ik_add ik_oracle 
  for hf_valid  :: "'ainfo \<Rightarrow> 'uinfo
    \<Rightarrow> ('aahi, 'uhi) HF
    \<Rightarrow> ('aahi, 'uhi) HF option \<Rightarrow> bool"
    and auth_restrict :: "'ainfo => 'uinfo \<Rightarrow> ('aahi, 'uhi) HF list \<Rightarrow> bool"
    and extr :: "msgterm \<Rightarrow> 'aahi ahi_scheme list"
    and extr_ainfo :: "msgterm \<Rightarrow> 'ainfo"
    and term_ainfo :: "'ainfo \<Rightarrow> msgterm"
    and upd_uinfo :: "'uinfo \<Rightarrow> ('aahi, 'uhi) HF \<Rightarrow> 'uinfo"
    and ik_add :: "msgterm set"
    and ik_oracle :: "msgterm set"
    and no_oracle :: "'ainfo \<Rightarrow> 'uinfo \<Rightarrow> bool" +

\<comment> \<open>A valid validation field that is contained in ik corresponds to an authorized hop field.
   (The notable exceptions being oracle-obtained validation fields.)
   This relates the result of @{text "terms_hf"} to its argument. @{text "terms_hf"} has to produce a msgterm that is either
   unique for each given hop field x, or it is only produced by an 'equivalence class' of hop fields
   such that either all of the hop fields of the class are authorized, or none are.
   While the extr function (constrained by assumptions below) also binds the hop information to the
   validation field, it does so only for AHI and AInfo, but not for UHI.\<close>
    assumes COND_terms_hf:
    "\<lbrakk>hf_valid ainfo uinfo hf nxt; terms_hf hf \<subseteq> analz ik; no_oracle ainfo uinfo\<rbrakk>
      \<Longrightarrow> \<exists>hfs . hf \<in> set hfs \<and> (\<exists>uinfo' . (ainfo, hfs) \<in> (auth_seg2 uinfo'))"
\<comment> \<open>A valid validation field that can be synthesized from the initial intruder knowledge is already
    contained in the initial intruder knowledge if it belongs to an honest AS. This can be combined
   with the previous assumption.\<close> 
    and COND_honest_hf_analz: 
    "\<lbrakk>ASID (AHI hf) \<notin> bad; hf_valid ainfo uinfo hf nxt; terms_hf hf \<subseteq> synth (analz ik);
      no_oracle ainfo uinfo\<rbrakk>
      \<Longrightarrow> terms_hf hf \<subseteq> analz ik"
\<comment> \<open>Extracting the path from the validation field of the first hop field of some path l
    returns an extension of the AHI-level path of the valid prefix of l.\<close> 
    and COND_path_prefix_extr:
    "prefix (AHIS (hfs_valid_prefix ainfo uinfo l nxt))
            (extr_from_hd l)"
\<comment> \<open>Extracting the path from the validation field of the first hop field of a completely valid path l
    returns a prefix of the AHI-level path of l. Together with @{thm "COND_path_prefix_extr"}, this implies
    that extr of a completely valid path l is exactly the same AHI-level path as l (see lemma below).\<close> 
    and COND_extr_prefix_path:
    "\<lbrakk>hfs_valid ainfo uinfo l nxt; auth_restrict ainfo uinfo l; nxt = None\<rbrakk> 
    \<Longrightarrow> prefix (extr_from_hd l) (AHIS l)"
\<comment> \<open>A valid hop field is only valid for one specific uinfo.\<close>
    and COND_hf_valid_uinfo:
    "\<lbrakk>hf_valid ainfo uinfo hf nxt; hf_valid ainfo' uinfo' hf nxt'\<rbrakk> 
    \<Longrightarrow> uinfo' = uinfo"
\<comment> \<open>Updating a uinfo field does not reveal anything novel to the attacker.\<close>
    and COND_upd_uinfo_ik: 
    "\<lbrakk>terms_uinfo uinfo \<subseteq> synth (analz ik); terms_hf hf \<subseteq> synth (analz ik)\<rbrakk> 
    \<Longrightarrow> terms_uinfo (upd_uinfo uinfo hf) \<subseteq> synth (analz ik)"
\<comment> \<open>The determination of whether a packet is an oracle packet is invariant under uinfo field updates.\<close>
    and COND_upd_uinfo_no_oracle: 
    "no_oracle ainfo uinfo \<Longrightarrow> no_oracle ainfo (upd_uinfo uinfo fld)"
\<comment> \<open>The restriction on authorized paths is invariant under uinfo field updates.\<close>
    and COND_auth_restrict_upd: 
    "auth_restrict ainfo uinfo (hf1 # hf2 # xs) \<Longrightarrow> auth_restrict ainfo (upd_uinfo uinfo hf2) (hf2 # xs)"
begin

lemma holds_path_eq_extr:
    "\<lbrakk>hfs_valid ainfo uinfo l nxt; auth_restrict ainfo uinfo l; nxt = None\<rbrakk> \<Longrightarrow> extr_from_hd l = AHIS l"
  using COND_extr_prefix_path COND_path_prefix_extr 
  by (metis TWu.holds_implies_takeW_is_identity prefix_order.eq_iff)

lemma upds_uinfo_no_oracle:
  "no_oracle ainfo uinfo \<Longrightarrow> no_oracle ainfo (upds_uinfo uinfo hfs)"
  by (induction hfs rule: rev_induct, auto intro!: COND_upd_uinfo_no_oracle)

(******************************************************************************)
subsection \<open>Lemmas that are needed for the refinement proof\<close>
(******************************************************************************)

thm COND_upd_uinfo_ik COND_upd_uinfo_ik[THEN subsetD] subsetI
lemma upd_uinfo_ik_elem:
    "\<lbrakk>t \<in> terms_uinfo (upd_uinfo uinfo hf); terms_uinfo uinfo \<subseteq> synth (analz ik); terms_hf hf \<subseteq> synth (analz ik)\<rbrakk> 
    \<Longrightarrow> t \<in> synth (analz ik)"
  oops


lemma honest_hf_analz_subsetI: 
    "\<lbrakk>t \<in> terms_hf hf; ASID (AHI hf) \<notin> bad; hf_valid ainfo uinfo hf nxt; terms_hf hf \<subseteq> synth (analz ik);
      no_oracle ainfo uinfo\<rbrakk>
      \<Longrightarrow> t \<in> analz ik"
  using COND_honest_hf_analz subsetI by blast

lemma extr_from_hd_eq: "(l \<noteq> [] \<and> l' \<noteq> [] \<and> hd l = hd l') \<or> (l = [] \<and> l' = []) \<Longrightarrow> extr_from_hd l = extr_from_hd l'" 
  apply (cases l)
   apply auto
  apply(cases l')
  by auto

lemma path_prefix_extr_l:
    "\<lbrakk>hd l = hd l'; l' \<noteq> []\<rbrakk> \<Longrightarrow> prefix (AHIS (hfs_valid_prefix ainfo uinfo l nxt))
            (extr_from_hd l')"
  using COND_path_prefix_extr extr_from_hd.elims list.sel(1) not_prefix_cases prefix_Cons prefix_Nil
  by metis

lemma path_prefix_extr_l':
    "\<lbrakk>hd l = hd l'; l' \<noteq> []; hf = hd l'\<rbrakk> \<Longrightarrow> prefix (AHIS (hfs_valid_prefix ainfo uinfo l nxt))
            (extr (HVF hf))"
  using COND_path_prefix_extr extr_from_hd.elims list.sel(1) not_prefix_cases prefix_Cons prefix_Nil
  by metis  (*takes a few sec*)

(*The proof of this lemma is VERY similar to that of TWu.holds_intermediate *)
lemma auth_restrict_app:
  assumes "auth_restrict ainfo uinfo p" "p = pre @ hf # post"
  shows "auth_restrict ainfo (upds_uinfo_shifted uinfo pre hf) (hf # post)"
  using assms proof(induction pre arbitrary: p uinfo hf)
  case Nil
  then show ?case using assms by (simp add: TWu.upd_shifted.simps(2))
next
  case induct_asm: (Cons a prev) 
  show ?case
  proof(cases prev)
    case Nil
    then have "auth_restrict ainfo (upd_uinfo uinfo hf) (hf # post)" 
      using induct_asm COND_auth_restrict_upd by simp
    then show ?thesis 
      using induct_asm Nil by (auto simp add: TWu.upd_shifted.simps)
  next
    case cons_asm: (Cons b list)
    then have "auth_restrict ainfo (upd_uinfo uinfo b) (b # list @ hf # post)" 
      using induct_asm(2-3) COND_auth_restrict_upd by auto 
    then show ?thesis
      using induct_asm(1)
      by (simp add: cons_asm TWu.upd_shifted.simps)
  qed
qed

lemma hfs_valid_None_Cons:
  assumes "hfs_valid_None ainfo uinfo p" "p = hf1 # hf2 # post"
  shows "hfs_valid_None ainfo (upd_uinfo uinfo hf2) (hf2 # post)"
  using assms apply auto
  by(auto simp add: TWu.holds.simps(1)) 

lemma pfrag_extr_auth:
assumes "hf \<in> set p" and "(ainfo, p) \<in> (auth_seg2 uinfo)"
shows "pfragment ainfo (extr (HVF hf)) auth_seg0"
proof -
  have p_verified: "hfs_valid_None ainfo uinfo p" "auth_restrict ainfo uinfo p"
      using assms(2) auth_seg2_def TWu.holds_takeW_is_identity by fastforce+
    obtain pre post where p_def: "p = pre @ hf # post" using assms(1) split_list by metis
    then have hf_post_valid:
              "hfs_valid_None ainfo (upds_uinfo_shifted uinfo pre hf) (hf # post)" 
              "auth_restrict ainfo (upds_uinfo_shifted uinfo pre hf) (hf # post)"
    using p_verified by (auto intro: TWu.holds_intermediate auth_restrict_app)
      
  then have "pfragment ainfo (AHIS (hf # post)) auth_seg0"
    using assms(2) p_def by(auto intro!: pfragmentI[of _ "AHIS pre" _ "[]"] simp add: auth_seg2_def)

  then have "pfragment ainfo (extr_from_hd (hf # post)) auth_seg0"
    using holds_path_eq_extr[symmetric] hf_post_valid by metis
  then show ?thesis by simp
qed

lemma X_in_ik_is_auth:
  assumes "terms_hf hf1 \<subseteq> analz ik" and "no_oracle ainfo uinfo"
  shows "pfragment ainfo (AHIS (hfs_valid_prefix ainfo uinfo
                (hf1 # fut)
                nxt))
              auth_seg0"
proof -
  let ?pFu = "hf1 # fut"
  let ?takW = "(hfs_valid_prefix ainfo uinfo ?pFu nxt)"
  have "prefix (AHIS (hfs_valid_prefix ainfo uinfo ?takW (TWu.extract (hf_valid ainfo) upd_uinfo uinfo ?pFu nxt)))
               (extr_from_hd ?takW)"
    by(auto simp add: COND_path_prefix_extr simp del: AHIS_def)
  then have "prefix (AHIS ?takW) (extr_from_hd ?takW)"
    by(simp add: TWu.takeW_takeW_extract)
  moreover from assms have "pfragment ainfo (extr_from_hd ?takW) auth_seg0"
    by (auto simp add: TWu.takeW_split_tail dest!: COND_terms_hf intro: pfrag_extr_auth)
  ultimately show ?thesis
    by(auto intro: pfragment_prefix elim!: prefixE)
qed


subsubsection \<open>Fragment is extendable\<close>
(******************************************************************************)

text \<open>makes sure that: the segment is terminated, i.e. the leaf AS's HF has Eo = None\<close>
fun terminated2 :: "('aahi, 'uhi) HF list \<Rightarrow> bool" where
  "terminated2 (hf#xs) \<longleftrightarrow> DownIF (AHI hf) = None \<or> ASID (AHI hf) \<in> bad"
| "terminated2 [] = True" (* we allow this as a special case*)

lemma terminated20: "terminated (AHIS m) \<Longrightarrow> terminated2 m" by(induction m, auto)

lemma cons_snoc: "\<exists>y ys. x # xs = ys @ [y]"
  by (metis append_butlast_last_id rev.simps(2) rev_is_Nil_conv)

lemma terminated2_suffix:
  "\<lbrakk>terminated2 l; l = zs @ x # xs; DownIF (AHI x) \<noteq> None; ASID (AHI x) \<notin> bad\<rbrakk> \<Longrightarrow> \<exists>y ys. zs = ys @ [y]"
  by(cases "zs") 
    (fastforce intro: cons_snoc)+

lemma attacker_modify_cutoff: "\<lbrakk>(info, zs@hf#ys) \<in> auth_seg0; ASID hf = a;
      ASID hf' = a; UpIF hf' = UpIF hf; a \<in> bad; ys' = hf'#ys\<rbrakk> \<Longrightarrow> (info, ys') \<in> auth_seg0"
  by(auto simp add: ASM_modify dest: ASM_cutoff)

lemma auth_seg2_terms_hf[elim]: 
  "\<lbrakk>x \<in> terms_hf hf; hf \<in> set hfs; (ainfo, hfs) \<in> (auth_seg2 uinfo) \<rbrakk> \<Longrightarrow> x \<in> analz ik"
  by(auto 3 4 simp add: ik_def)





(*lemma that would probably be useful for proving fragment_with_Eo_Some_extendable below?*)
lemma "\<lbrakk>hfs_valid ainfo uinfo hfs nxt; hfs = pref @ [hf]\<rbrakk> \<Longrightarrow> hf_valid ainfo (upds_uinfo uinfo pref) hf nxt"
  apply auto
  thm TWu.holds_append[where ?P="(hf_valid ainfo)", where ?upd=upd_uinfo]
  apply(auto simp add: TWu.holds_append[where ?P="(hf_valid ainfo)", where ?upd=upd_uinfo])
  apply(cases pref) apply auto
   apply (simp add: TWu.holds.simps(2))
  apply (simp add: TWu.holds.simps(2))
(*THIS DOES NOT HOLD! We should not update with the head of hfs, but we should update with hf. 
Off-by-one error in both directions (shifted).*)
  oops

text \<open>This lemma proves that an attacker-derivable segment that starts with an attacker hop field,
and has a next hop field which belongs to an honest AS, when restricted to its valid prefix, is
authorized. Essentially this is the case because the hop field of the honest AS already contains
an interface identifier DownIF that points to the attacker-controlled AS. Thus, there must have been
some attacker-owned hop field on the original authorized path. Given the assumptions we make in the
directed setting, the attacker can make take a suffix of an authorized path, such that his hop field
is first on the path, and he can change his own hop field if his hop field is the first on the path,
thus, that segment is also authorized.\<close>
lemma fragment_with_Eo_Some_extendable:
  assumes "terms_hf hf2 \<subseteq> synth (analz ik)"
  and "ASID (AHI hf1) \<in> bad"
  and "ASID (AHI hf2) \<notin> bad" (* if A2 is bad, we could use directly COND_extension. This is covered below *)
  and "hf_valid ainfo uinfo hf1 (Some hf2)"
  and "no_oracle ainfo uinfo"
  shows
   "pfragment ainfo
      (ifs_valid_prefix pre'
        (AHIS (hfs_valid_prefix ainfo uinfo
          (hf1 # hf2 # fut)
          None))
      None)
     auth_seg0"
proof(cases)
  assume "hf_valid ainfo (upd_uinfo uinfo hf2) hf2 (head fut) 
        \<and> if_valid (Some (AHI hf1)) (AHI hf2) (AHIo (head fut))"
  
  then have hf2true: "hf_valid ainfo (upd_uinfo uinfo hf2) hf2 (head fut)"
                     "if_valid (Some (AHI hf1)) (AHI hf2) (AHIo (head fut))" by blast+
  then have "\<exists> hfs uinfo' . hf2 \<in> set hfs \<and> (ainfo, hfs) \<in> (auth_seg2 uinfo')" 
    using assms by(auto intro!: COND_terms_hf COND_upd_uinfo_no_oracle 
                         elim!: honest_hf_analz_subsetI)
  then obtain hfs uinfo' where hfs_def: 
    "hf2 \<in> set hfs" "(ainfo, hfs) \<in> (auth_seg2 uinfo')" "hfs_valid_None ainfo uinfo' hfs"
    "no_oracle ainfo uinfo'"
    using COND_terms_hf by(auto simp add: auth_seg2_def TWu.holds_takeW_is_identity)
  
  have termianted_hfs: "terminated2 hfs" 
    using hfs_def(2) by (auto simp add: auth_seg2_def ASM_terminated intro: terminated20)

  have "\<exists>pref hf1' ys . hfs = pref@[hf1']@(hf2#ys)"
    using hf2true(2) assms(3) hfs_def(1) terminated2_suffix
    by(fastforce dest: split_list intro: termianted_hfs)
  then obtain pref hf1' ys where hfs_unfold: "hfs = pref@[hf1']@(hf2#ys)" by fastforce 


(*New_SCION: the following is possibly quite hard to get right, because we need to appropriately
update uinfo... and that update actually depends on pref. So we need to apply upd_uinfo not only
once, but |pref| many times for hf1' and |pref|+1 naby times for hf2. 
EDIT: Seem like I got it right :) *)
  have hf2_valid: "hf_valid ainfo (upds_uinfo uinfo' (tl (pref@[hf1', hf2]))) hf2 (head ys)" (*only needed to show uinfo'_eq *)
     and hf1'true: "hf_valid ainfo (upds_uinfo uinfo' (tl (pref@[hf1']))) hf1' (Some hf2)"
    (*apply(cases ys)*)
    using hfs_def(3) hfs_unfold 
    apply(auto simp add: TWu.holds_append[where ?P="(hf_valid ainfo)", where ?upd=upd_uinfo])
    apply (auto simp add: hfs_def hfs_unfold TWu.holds_unfold_prelnil tail_snoc TWu.holds.simps(1) 
                elim!: TWu.holds_unfold_prexnxt' intro: rev_exhaust[where ?xs=pref])
    subgoal
      apply(cases pref) apply auto
       apply (metis TWu.holds.simps(1) TWu.holds.simps(2) head.elims)
      by (metis TWu.holds.simps(1) TWu.holds.simps(2) head.elims)
    subgoal
      apply(cases pref) by (auto simp add: TWu.holds.simps) 
    done

  have uinfo'_eq: "upd_uinfo uinfo hf2 = upds_uinfo uinfo' (tl (pref @ [hf1', hf2]))"
    using hf2_valid hf2true(1) by(auto elim!: COND_hf_valid_uinfo)
  then have uinfo'_eq2: "upd_uinfo uinfo hf2 = upd_uinfo (upds_uinfo uinfo' (tl (pref @ [hf1']))) hf2"
    by(simp add: tl_append2)
(*
  then have uinfo'_eq2: "uinfo = upds_uinfo uinfo' (tl (pref @ [hf1']))"
    apply(simp add: tl_append2)
    using upds_uinfo_eq TWu.upds_snoc[where ?upd=upd_uinfo]
    apply(simp add: TWu.upds_snoc[where ?upd=upd_uinfo])
    using inj_upd_uinfo injD
    by metis
*)
(*
    oops doesn't hold!
*)
  
  have if_valid_hf2hf1': "if_valid (Some (AHI hf1')) (AHI hf2) (head (AHIS ys))"
    apply(cases ys)
    using assms(3) hfs_def(2) ASM_if_valid TW.holds_unfold_prexnxt' TW.holds_unfold_prelnil
    by(fastforce simp add: hfs_unfold auth_seg2_def)+

(*
  have "hf_valid ainfo uinfo hf1' (Some hf2)" using assms(5) hf1'true uinfo'_eq2
    by auto 
*)

  have "pfragment ainfo (AHIS (hfs_valid_prefix ainfo (upds_uinfo uinfo' (tl (pref@[hf1'])))
          (hf1' # hf2 # fut)
          None))
        auth_seg0"
    apply(rule X_in_ik_is_auth)
    using hfs_def(1,2,4) assms(2,5) 
    by(fastforce simp add: hfs_unfold ik_def 
                   intro!: upds_uinfo_no_oracle COND_upd_uinfo_no_oracle)+

  then show ?thesis 
    apply-
    apply(rule strip_ifs_valid_prefix)
    apply(erule pfragment_self_eq_nil)
    apply auto
    apply(auto simp add: TWu.takeW_split_tail[where ?x=hf1'])
    subgoal
      using assms(2-4) hf2true(2) if_valid_hf2hf1' hf1'true 
      by(auto elim!: attacker_modify_cutoff[where ?hf'="AHI hf1"] simp add: TWu.takeW_split_tail uinfo'_eq2)
    subgoal
      using hf1'true by(auto)
    done
next
  assume hf2false: "\<not>(hf_valid ainfo (upd_uinfo uinfo hf2) hf2 (head fut) 
                    \<and> if_valid (Some (AHI hf1)) (AHI hf2) (AHIo (head fut)))"
  show ?thesis 
  proof(cases)
    assume hf1_correct: "hf_valid ainfo uinfo hf1 (Some hf2) 
               \<and> if_valid pre' (AHI hf1) (Some (AHI hf2))"
    show ?thesis 
    proof(cases)
      assume hf2_valid: "hf_valid ainfo (upd_uinfo uinfo hf2) hf2 (head fut)"
      then have "\<not>if_valid (Some (AHI hf1)) (AHI hf2) (AHIo (head fut))" using hf2false by simp
      then show ?thesis
        using hf1_correct hf2_valid apply(auto)
        using assms(2) by(auto simp add: TW.takeW_split_tail TWu.takeW_split_tail intro: ASM_singleton) (*takes a few seconds*)
    next
      assume "\<not>hf_valid ainfo (upd_uinfo uinfo hf2) hf2 (head fut)"
      then show ?thesis apply auto  apply(cases fut)
          using assms(2)
          by(auto simp add: TW.takeW_split_tail[where ?x=hf1] TWu.takeW_split_tail TW.takeW.simps 
                  intro: ASM_singleton intro!: strip_ifs_valid_prefix)
    qed
  next
    assume "\<not> (hf_valid ainfo uinfo hf1 (Some hf2) 
               \<and> if_valid pre' (AHI hf1) (Some (AHI hf2)))"
    then show ?thesis 
      using hf2false apply auto 
      by (auto simp add: TW.takeW.simps TWu.takeW_split_tail[where ?x=hf1] TWu.takeW_split_tail[where ?x=hf2] 
                       ASM_singleton assms(2) strip_ifs_valid_prefix) 
  qed
qed

subsubsection \<open>A1 and A2 collude to make a wormhole\<close>
(******************************************************************************)

text \<open>We lift @{text "extend_pfragment0"} to DP2.\<close>
lemma extend_pfragment2:
  assumes "pfragment ainfo 
(ifs_valid_prefix (Some (AHI hf1))
(AHIS (hfs_valid_prefix ainfo (upd_uinfo uinfo hf2)
                      (hf2 # fut)
                      nxt))
             None)
                    auth_seg0"
  assumes "hf_valid ainfo uinfo hf1 (Some hf2)"
  assumes "ASID (AHI hf1) \<in> bad"
  assumes "ASID (AHI hf2) \<in> bad"
  shows "pfragment ainfo 
(ifs_valid_prefix pre'
(AHIS (hfs_valid_prefix ainfo uinfo
                    (hf1 # hf2 # fut)
                    nxt))
             None)
                  auth_seg0"
  using assms
  apply(auto simp add: TWu.takeW_split_tail[where ?P="hf_valid ainfo"]) 
  apply(auto simp add: TWu.takeW_split_tail[where ?P="if_valid"] TWu.takeW.simps(1)
                      intro: ASM_singleton strip_ifs_valid_prefix intro!: extend_pfragment0)
  by (simp add: TW.takeW_split_tail extend_pfragment0)

declare hfs_valid_prefix_generic_def[simp del]

(*we prove this for all ainfo (but at most one of them will fit)*)
(*the case distinctions we make on whether the owner of the first hf is an adversary: this is the AS *AFTER*
the AS that sent the packet (the sender AS we know to be malicious as per the evt_dispatch_ext2 event). *)
text\<open>This is the central lemma that we need to prove to show the refinement between this model and 
dp1. It states: If an attacker can synthesize a segment from his knowledge, and does not use a path
origin that was used to query the oracle, then the valid prefix of the segment is authorized. Thus,
the attacker cannot create any valid but unauthorized segments.\<close>
lemma ik_seg_is_auth:
  assumes "terms_pkt m \<subseteq> synth (analz ik)" and "future m = hfs" and "AInfo m = ainfo"
    and "nxt = None" and "no_oracle ainfo uinfo"
  shows "pfragment ainfo
            (ifs_valid_prefix prev'
              (AHIS (hfs_valid_prefix ainfo uinfo hfs nxt))
             None)
                auth_seg0"
using assms
proof(induction hfs nxt arbitrary: prev' m rule: TWu.takeW.induct[where ?Pa="hf_valid ainfo", where ?upd="upd_uinfo"])
  case (1 _ _) (* LENGTH: 0 *)
  then show ?case using append_Nil ASM_empty pfragment_def Nil_is_map_conv TWu.takeW.simps(1) AHIS_def
    by (metis TW.takeW.simps(1) hfs_valid_prefix_generic_def)
next
  case (2 pre hf nxt)
  then show ?case 
  proof(cases) (* LENGTH: 1, ADVERSARY *)
    assume "ASID (AHI hf) \<in> bad" (*bad*)
    then show ?thesis apply-
      by(intro strip_ifs_valid_prefix)
        (auto simp add: pfragment_def ASM_singleton TWu.takeW_singleton intro!: exI[of _ "[]"])
  next
    assume "ASID (AHI hf) \<notin> bad" (*not bad*) (* LENGTH: 1, HONEST *)
    then show ?thesis
      apply(intro strip_ifs_valid_prefix) apply(cases m)
      using 2 assms by (auto simp add: terms_pkt_def 
               simp del: AHIS_def intro!: X_in_ik_is_auth dest: COND_honest_hf_analz)
  qed
next
  case (3 info hf nxt) (* LENGTH: 1, SPURIOUS *)
  then show ?case
    by (intro strip_ifs_valid_prefix, simp add: TWu.takeW_singleton)
next
  case (4 info hf1 hf2 xs nxt) (*this is the crux of the proof*)
  then show ?case 
  proof(cases)
    assume hf1bad: "ASID (AHI hf1) \<in> bad" (* LENGTH: N, ADVERSARY *)
    then show ?thesis 
    proof(cases)
      assume hf2bad: "ASID (AHI hf2) \<in> bad" (* LENGTH: N, ADVERSARY & ADVERSARY (wormhole assumption2) *)
      show ?thesis 
        apply(intro extend_pfragment2)
        subgoal
          apply (auto simp add: 4(6)) apply(cases m) 
          apply(rule 4(2)[simplified, where ?m1="fwd_pkt (upd_pkt m)"]) (*induction*)
          using 4(3-7) by (auto simp add: terms_pkt_def upd_pkt_def 
                                   intro: COND_upd_uinfo_no_oracle COND_upd_uinfo_ik[THEN subsetD])
        using 4(1,3-5) \<open>no_oracle ainfo uinfo\<close> by(auto intro: hf1bad hf2bad)
    next
      assume "ASID (AHI hf2) \<notin> bad" (* LENGTH: N, ADVERSARY & HONEST (fragment is extendable) *)
      then show ?thesis
        using 4(1,4-7) hf1bad apply(simp add: hfs_valid_prefix_generic_def) 
        using 4(3)
        by(auto 3 4 intro!: fragment_with_Eo_Some_extendable[simplified] 
                  simp add: terms_pkt_def simp del: hfs_valid_prefix_generic_def AHIS_def)
    qed
  next
    assume "ASID (AHI hf1) \<notin> bad" (* LENGTH: N, HONEST *)
    then show ?thesis
      apply(intro strip_ifs_valid_prefix) 
      using 4(1,3-7) by(auto intro!: X_in_ik_is_auth simp del: AHIS_def simp add: terms_pkt_def
                               dest: COND_honest_hf_analz)
  qed
next
  case 5 (* LENGTH: N, SPURIOUS *)
  then show ?case 
    by(intro strip_ifs_valid_prefix, simp add: TWu.takeW_two_or_more)
qed

lemma ik_seg_is_auth':
  assumes "terms_pkt m \<subseteq> synth (analz ik)"
    and "future m = hfs" and "AInfo m = ainfo" and "nxt = None" and "no_oracle ainfo uinfo"
  shows "pfragment ainfo
            (ifs_valid_prefix prev'
              (AHIS (hfs_valid_prefix_generic ainfo uinfo pas pre hfs nxt))
             None)
                auth_seg0"
  using ik_seg_is_auth hfs_valid_prefix_generic_def assms
  by simp

print_locale dataplane_2
sublocale dataplane_2  _ _ _ _ hfs_valid_prefix_generic _ _ _ _ _ _ no_oracle _ _ hf_valid_generic upd_uinfo
  apply unfold_locales
  using ik_seg_is_auth' COND_upd_uinfo_ik COND_upd_uinfo_no_oracle 
    prefix_hfs_valid_prefix_generic cons_hfs_valid_prefix_generic apply auto
  by (metis list.inject) (*WHY? Some problem with cons_hfs_valid_prefix_generic?*)

end
end
