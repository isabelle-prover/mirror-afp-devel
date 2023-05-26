(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)
section \<open>Anapaya-SCION\<close>
text\<open>This is the "new" SCION protocol, as specified on the website of Anapaya:
\url{https://scion.docs.anapaya.net/en/latest/protocols/scion-header.html} (Accessed 2021-03-02).
It does not use the next hop field in its MAC computation, but instead refers uses a mutable uinfo
field which acts as an XOR-based accumulator for all upstream MACs.

This protocol instance requires the use of the extensions of our formalization that provide mutable 
uinfo field and an XOR abstraction.\<close>
theory "Anapaya_SCION"
  imports
    "../Parametrized_Dataplane_3_directed"
    "../infrastructure/Abstract_XOR"
begin

locale scion_defs = network_assums_direct _ _ _ auth_seg0 
  for auth_seg0 :: "(msgterm \<times> ahi list) set"
begin

sublocale comp_fun_commute xor
  by(auto simp add: comp_fun_commute_def xor_def)

(******************************************************************************)
subsection \<open>Hop validation check and extract functions\<close>
(******************************************************************************)
type_synonym SCION_HF = "(unit, unit) HF"

text\<open>The predicate @{term "hf_valid"} is given to the concrete parametrized model as a parameter.
It ensures the authenticity of the hop authenticator in the hop field. The predicate takes an authenticated
info field (in this model always a numeric value, hence the matching on Num ts), the unauthenticated
info field and the hop field to be validated. The next hop field is not used in this instance.\<close>
fun hf_valid :: "msgterm \<Rightarrow> msgterm fset
    \<Rightarrow> SCION_HF
    \<Rightarrow> SCION_HF option \<Rightarrow> bool" where 
  "hf_valid (Num ts) uinfo \<lparr>AHI = ahi, UHI = _, HVF = x\<rparr> nxt \<longleftrightarrow> 
    (\<exists>upif downif. x = Mac[macKey (ASID ahi)] (L [Num ts, upif, downif, FS uinfo]) \<and>
          ASIF (DownIF ahi) downif \<and> ASIF (UpIF ahi) upif)"
| "hf_valid _ _ _ _ = False"

text\<open>Updating the uinfo field involves XORin the current hop validation field onto it. Note that in all 
authorized segments, the hvf will already have been contained in segid, hence this operation only
removes terms from the fset in the forwarding of honestly created packets.\<close>
definition upd_uinfo :: "msgterm fset \<Rightarrow> SCION_HF \<Rightarrow> msgterm fset" where
  "upd_uinfo segid hf = xor segid {| HVF hf |}"

declare upd_uinfo_def[simp]

(*What can uinfo be?
hfs = [], uinfo = FS {||}
hfs = [x], uinfo = FS {||}
hfs = [y, x], uinfo = FS {| MAC-of-x |}
hfs = [z, y, x], uinfo = FS {| MAC-of-x, MAC-of-y |}
*)

text\<open>The following lemma is needed to show the termination of extr, defined below.\<close>
lemma extr_helper:
"\<lbrakk>x = Mac[macKey asid'a] (L [ts, upif'a, downif'a, FS segid']); 
  fcard segid' = fcard (xor segid {|x|}); x |\<in>| segid\<rbrakk>
       \<Longrightarrow> (case x of Hash \<langle>Key (macK asid), L []\<rangle> \<Rightarrow> 0 | Hash \<langle>Key (macK asid), L [ts]\<rangle> \<Rightarrow> 0 
| Hash \<langle>Key (macK asid), L [ts, upif]\<rangle> \<Rightarrow> 0 | Hash \<langle>Key (macK asid), L [ts, upif, downif]\<rangle> \<Rightarrow> 0
            | Hash \<langle>Key (macK asid), L [ts, upif, downif, FS segid]\<rangle> \<Rightarrow> Suc (fcard segid) 
| Hash \<langle>Key (macK asid), L (ts # upif # downif # FS segid # ac # lista)\<rangle> \<Rightarrow> 0
            | Hash \<langle>Key (macK asid), L (ts # upif # downif # _ # list)\<rangle> \<Rightarrow> 0 
| Hash \<langle>Key (macK asid), _\<rangle> \<Rightarrow> 0 | Hash \<langle>Key _, msgterm2\<rangle> \<Rightarrow> 0 | Hash \<langle>_, msgterm2\<rangle> \<Rightarrow> 0 
| Hash _ \<Rightarrow> 0 | _ \<Rightarrow> 0)
           < Suc (fcard segid)"
  apply auto 
  using fcard_fminus1_less xor_singleton(1) by (metis)

text\<open>We can extract the entire path from the hvf field, which includes the local forwarding 
information as well as, recursively, all upstream hvf fields and their hop information.\<close>
function (sequential) extr :: "msgterm \<Rightarrow> ahi list" where
  "extr (Mac[macKey asid] (L [ts, upif, downif, FS segid]))
 = \<lparr>UpIF = term2if upif, DownIF = term2if downif, ASID = asid\<rparr> # (if (\<exists>nextmac asid' upif' downif' segid'. 
         segid' = xor segid {| nextmac |} \<and> 
         nextmac = Mac[macKey asid'] (L [ts, upif', downif', FS segid'])) 
    then extr (THE nextmac. (\<exists>asid' upif' downif' segid'. 
                             segid' = xor segid {| nextmac |} \<and> 
                             nextmac = Mac[macKey asid'] (L [ts, upif', downif', FS segid'])))
    else [])"
| "extr _ = []"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>x. (case x of Mac[macKey asid] (L [ts, upif, downif, FS segid]) 
                    \<Rightarrow> Suc (fcard segid)
                | _ \<Rightarrow> 0))") 
  apply auto
  apply(rule theI2)
  by(auto elim: FS_update_eq elim!: FS_contains_elem intro!: extr_helper)

text\<open>Extract the authenticated info field from a hop validation field.\<close>
fun extr_ainfo :: "msgterm \<Rightarrow> msgterm" where 
  "extr_ainfo (Mac[macKey asid] (L (Num ts # xs))) = Num ts"
| "extr_ainfo _ = \<epsilon>"

abbreviation term_ainfo :: "msgterm \<Rightarrow> msgterm" where
  "term_ainfo \<equiv> id"

text\<open>The ainfo field must be a Num, since it represents the timestamp (this is only needed for 
authorized segments (ainfo, []), since for all other segments, @{text "hf_valid"} enforces this.

Furthermore, we require that the last hop field on l has a MAC that is computed with the empty uinfo 
field. This restriction cannot be introduced via @{text "hf_valid"}, since it is not a check 
performed by the on-path routers, but rather results from the way that authorized paths are set up
on the control plane. We need this restriction to ensure that the uinfo field of the top node does 
not contain extra terms (e.g. secret keys).\<close>
definition auth_restrict where 
  "auth_restrict ainfo uinfo l \<equiv> 
    (\<exists>ts. ainfo = Num ts) 
    \<and> (case l of [] \<Rightarrow> (uinfo = {||}) | 
    _ \<Rightarrow> hf_valid ainfo {||} (last l) None)"

text\<open>When observing a hop field, an attacker learns the HVF. UHI is empty and the AHI only contains 
public information that are not terms.\<close>
fun terms_hf :: "SCION_HF \<Rightarrow> msgterm set" where 
  "terms_hf hf = {HVF hf}"

text\<open>When analyzing a uinfo field (which is an fset of message terms), the attacker learns all 
elements of the fset.\<close>
abbreviation terms_uinfo :: "msgterm fset \<Rightarrow> msgterm set" where 
  "terms_uinfo \<equiv> fset"

abbreviation no_oracle :: "'ainfo \<Rightarrow> msgterm fset \<Rightarrow> bool" where "no_oracle \<equiv> (\<lambda> _ _. True)"

subsubsection\<open>Properties following from definitions\<close>
text\<open>We now define useful properties of the above definition.\<close>
lemma hf_valid_invert:
  "hf_valid tsn uinfo hf nxt \<longleftrightarrow>
   ((\<exists>ahi ts upif downif asid x.
     hf = \<lparr>AHI = ahi, UHI = (), HVF = x\<rparr> \<and>
     ASID ahi = asid \<and> ASIF (DownIF ahi) downif \<and> ASIF (UpIF ahi) upif \<and>
     x = Mac[macKey asid] (L [tsn, upif, downif, FS uinfo]) \<and>
     tsn = Num ts)
    )"
  by(auto elim!: hf_valid.elims)

lemma info_hvf: 
  assumes "hf_valid ainfo uinfo m z" "hf_valid ainfo' uinfo' m' z'" "HVF m = HVF m'" 
  shows "ainfo' = ainfo" "m' = m"
  using assms by(auto simp add: hf_valid_invert intro: ahi_eq)

(******************************************************************************)
subsection\<open>Definitions and properties of the added intruder knowledge\<close>
(******************************************************************************)
text\<open>Here we define @{text "ik_add"} and @{text "ik_oracle"} as being empty, as these features are
not used in this instance model.\<close>

print_locale dataplane_3_directed_defs 
sublocale dataplane_3_directed_defs _ _ _ auth_seg0 hf_valid auth_restrict extr extr_ainfo term_ainfo 
                 terms_hf terms_uinfo upd_uinfo no_oracle
  by unfold_locales
declare TWu.holds_set_list[dest]
declare TWu.holds_takeW_is_identity[simp]
declare parts_singleton[dest]

abbreviation ik_add :: "msgterm set" where "ik_add \<equiv> {}"

abbreviation ik_oracle :: "msgterm set" where "ik_oracle \<equiv> {}"

(******************************************************************************)
subsection\<open>Properties of the intruder knowledge, including @{term "terms_uinfo"}.\<close>
(******************************************************************************)
text\<open>We now instantiate the parametrized model's definition of the intruder knowledge, using the
definitions of @{term "terms_uinfo"} and  @{text "ik_oracle"} from above. We then prove the properties 
that we need to instantiate the @{text "dataplane_3_directed"} locale.\<close>
print_locale dataplane_3_directed_ik_defs
sublocale
  dataplane_3_directed_ik_defs _ _ _ auth_seg0 terms_uinfo no_oracle hf_valid auth_restrict extr extr_ainfo term_ainfo 
                  terms_hf upd_uinfo ik_add ik_oracle 
  by unfold_locales

text\<open>For this instance model, the neighboring hop field is irrelevant. Hence, if we are interested
in establishing the first hop field's validity given @{text "hfs_valid"}, we do not need to make
a case distinction on the rest of the hop fields (which would normally be required by @{text "TWu"}.\<close>
lemma hfs_valid_first[elim]: "hfs_valid ainfo uinfo (hf # post) nxt \<Longrightarrow> hf_valid ainfo uinfo hf nxt'"
  by(cases post, auto simp add: hf_valid_invert TWu.holds.simps)

text\<open>Properties of HVF of valid hop fields that fulfill the restriction.\<close>
lemma auth_properties: 
  assumes "hf \<in> set hfs" "hfs_valid ainfo uinfo hfs nxt" "auth_restrict ainfo uinfo hfs" 
          "t = HVF hf"
  shows "(\<exists>t' . t = Hash t')
       \<and> (\<exists>uinfo'. auth_restrict ainfo uinfo' hfs
       \<and> (\<exists>nxt. hf_valid ainfo uinfo' hf nxt))"
using assms
proof(induction uinfo hfs nxt arbitrary: hf rule: TWu.holds.induct[where ?upd=upd_uinfo])
  case (1 info x y ys nxt)
  then show ?case
  proof(cases "hf = x")
    case True
    then show ?thesis

      using 1(2-5) by (auto simp add: TWu.holds.simps(1) hf_valid_invert)
  next
    case False
    then have "hf \<in> set (y # ys)" using 1 by auto
    then show ?thesis 
      apply- apply(drule 1)
      subgoal using assms 1(2-5) by (simp add: TWu.holds.simps(1))
      using assms(3) 1(2-5) False 
      by(auto simp add: auth_restrict_def hf_valid_invert)
  qed
qed(auto simp add: auth_restrict_def hf_valid_invert intro!: exI)

lemma ik_hfs_form: "t \<in> parts ik_hfs \<Longrightarrow> \<exists> t' . t = Hash t'"
  by(auto 3 4 simp add: auth_seg2_def dest: auth_properties)

declare ik_hfs_def[simp del]

lemma parts_ik_hfs[simp]: "parts ik_hfs = ik_hfs"
  by (auto intro!: parts_Hash ik_hfs_form)

text\<open>This lemma allows us not only to expand the definition of @{term "ik_hfs"}, but also 
to obtain useful properties, such as a term being a Hash, and it being part of a valid hop field.\<close>
lemma ik_hfs_simp: 
  "t \<in> ik_hfs \<longleftrightarrow> (\<exists>t' . t = Hash t') \<and> (\<exists>hf . t = HVF hf
                    \<and> (\<exists>hfs uinfo. hf \<in> set hfs \<and> (\<exists>ainfo . (ainfo, hfs) \<in> (auth_seg2 uinfo)
                    \<and> (\<exists> nxt uinfo'. hf_valid ainfo uinfo' hf nxt))))" (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  assume asm: "?lhs" 
  then obtain ainfo uinfo hf hfs where 
    dfs: "hf \<in> set hfs" "(ainfo, hfs) \<in> (auth_seg2 uinfo)" "t = HVF hf"
    by(auto simp add: ik_hfs_def)
  then have "hfs_valid_None ainfo uinfo hfs" "(ainfo, AHIS hfs) \<in> auth_seg0"
    by(auto simp add: auth_seg2_def)
  then show "?rhs" using asm dfs by(fast intro: ik_hfs_form)
qed(auto simp add: ik_hfs_def)

text\<open>The following lemma is one of the conditions. We already prove it here, since it is helpful
elsewhere. \<close>
lemma auth_restrict_upd:
      "auth_restrict ainfo uinfo (x#y#hfs) 
   \<Longrightarrow> auth_restrict ainfo (upd_uinfo uinfo y) (y#hfs)"
  by (auto simp add: auth_restrict_def)

text\<open>We now show that @{text "ik_uinfo"} is redundant, since all of its terms are already contained in 
@{text "ik_hfs"}. To this end, we first show that a term contained in the uinfo field of an authorized 
paths is also contained in the HVF of the same path.\<close>
lemma uinfo_contained_in_HVF:
  assumes "t \<in> fset uinfo" "(ainfo, hfs) \<in> (auth_seg2 uinfo)" 
  shows "\<exists>hf. t = HVF hf \<and> hf \<in> set hfs"
proof-
  from assms(2) have hfs_defs: "hfs_valid_None ainfo uinfo hfs" "auth_restrict ainfo uinfo hfs" 
    by(auto simp add: auth_seg2_def)
  obtain nxt::"SCION_HF option" where nxt_None[intro]: "nxt = None" by simp
  then show ?thesis using hfs_defs assms(1)
  proof(induction uinfo hfs nxt rule: TWu.holds.induct[where ?upd=upd_uinfo])
    case (1 info x y ys nxt)
    then have hf_valid_x: "hf_valid ainfo info x (Some y)" by(auto simp only: TWu.holds.simps)
    from 1(2-3,5) show ?case 
    proof(cases "t = HVF y")
      case False
      then have "t \<in> fset (upd_uinfo info y)" using 1(2,5) by (simp add: xor_singleton(1))
      moreover have "hfs_valid_None ainfo (upd_uinfo info y) (y # ys)" 
                    "auth_restrict ainfo (upd_uinfo info y) (y # ys)"
        using 1(3-4) by(auto simp only: TWu.holds.simps elim: auth_restrict_upd)
      ultimately have "\<exists>hf. t = HVF hf \<and> hf \<in> set (y # ys)" using 1(1) "1.prems"(1) by blast
      then show ?thesis by auto
    qed(auto)
  next
    case (2 info x nxt)
    then show ?case 
      apply(auto simp only: TWu.holds.simps auth_restrict_def)
      by (auto simp add: hf_valid_invert)
  next
    case (3 info nxt)
    then show ?case by(auto simp add: auth_restrict_def)
  qed
qed

text\<open>The following lemma allows us to ignore @{text "ik_uinfo"} when we unfold @{text "ik"}.\<close>
lemma ik_uinfo_in_ik_hfs: "t \<in> ik_uinfo \<Longrightarrow> t \<in> ik_hfs"
  by(auto simp add: ik_hfs_def dest!: uinfo_contained_in_HVF)


(******************************************************************************)
subsubsection \<open>Properties of Intruder Knowledge\<close>
(******************************************************************************)
lemma auth_ainfo[dest]: "\<lbrakk>(ainfo, hfs) \<in> (auth_seg2 uinfo)\<rbrakk> \<Longrightarrow> \<exists> ts . ainfo = Num ts"
  by(auto simp add: auth_seg2_def auth_restrict_def)

text\<open>This lemma unfolds the definition of the intruder knowledge but also already applies some 
simplifications, such as ignoring @{text "ik_uinfo"}.\<close>
lemma ik_simpler: 
  "ik = ik_hfs
      \<union> {term_ainfo ainfo | ainfo hfs uinfo. (ainfo, hfs) \<in> (auth_seg2 uinfo)}
      \<union> Key`(macK`bad)"
  by(auto simp add: ik_def simp del: ik_uinfo_def dest: ik_uinfo_in_ik_hfs)

  text \<open>There are no ciphertexts (or signatures) in @{term "parts ik"}. Thus, @{term "analz ik"}
and @{term "parts ik"} are identical.\<close>
lemma analz_parts_ik[simp]: "analz ik = parts ik"
  by(rule no_crypt_analz_is_parts)
    (auto simp add: ik_simpler auth_seg2_def ik_hfs_simp auth_restrict_def)
  
lemma parts_ik[simp]: "parts ik = ik"
  by(auto 3 4 simp add: ik_simpler auth_seg2_def auth_restrict_def)

lemma key_ik_bad: "Key (macK asid) \<in> ik \<Longrightarrow> asid \<in> bad"
  by(auto simp add: ik_simpler)
    (auto 3 4 simp add: auth_seg2_def ik_hfs_simp hf_valid_invert)

lemma MAC_synth_helper:
  assumes "hf_valid ainfo uinfo m z" "HVF m = Mac[Key (macK asid)] j" "HVF m \<in> ik"
  shows "\<exists>hfs. m \<in> set hfs \<and> (\<exists>uinfo'. (ainfo, hfs) \<in> auth_seg2 uinfo')"
proof-
  from assms(2-3) obtain ainfo' uinfo' uinfo'' m' hfs' nxt' where dfs:
    "m' \<in> set hfs'" "(ainfo', hfs') \<in> auth_seg2 uinfo''" "hf_valid ainfo' uinfo' m' nxt'" 
    "HVF m = HVF m'"
    by(auto simp add: ik_simpler ik_hfs_simp)
  then have eqs[simp]: "ainfo' = ainfo" "m' = m" using assms(1) by(auto elim!: info_hvf)
  have "auth_restrict ainfo' uinfo'' hfs'" using dfs by(auto simp add: auth_seg2_def)
  then show ?thesis using dfs assms by auto
qed

text\<open>This definition helps with the limiting the number of cases generated. We don't require it, 
but it is convenient. Given a hop validation field and an asid, return if the hvf has the expected
format.\<close>
definition mac_format :: "msgterm \<Rightarrow> as \<Rightarrow> bool" where 
  "mac_format m asid \<equiv> \<exists> j . m = Mac[macKey asid] j"

text\<open>If a valid hop field is derivable by the attacker, but does not belong to the attacker, then 
the hop field is already contained in the set of authorized segments.\<close>
lemma MAC_synth:
  assumes "hf_valid ainfo uinfo m z" "HVF m \<in> synth ik" "mac_format (HVF m) asid" "asid \<notin> bad"
  shows "\<exists>hfs. m \<in> set hfs \<and> 
        (\<exists>uinfo'. (ainfo, hfs) \<in> auth_seg2 uinfo')"
  using assms
  by(auto simp add: mac_format_def ik_simpler ik_hfs_simp elim!: MAC_synth_helper dest!: key_ik_bad)

(******************************************************************************)
subsection\<open>Lemmas helping with conditions relating to extract\<close>
(******************************************************************************)
text\<open>Resolve the definite descriptor operator THE.\<close>
lemma THE_nextmac:
  assumes "hvf = Mac[macKey askey] (L [Num ts, upif, downif, FS (xor info {|hvf|})])"
    shows "(THE nextmac. \<exists>asid' upif' downif'. 
                nextmac = Mac[macKey asid'] (L [Num ts, upif', downif', FS (xor info {|nextmac|})])) 
          = hvf"
  apply(rule theI2[of _ hvf])
  using assms 
  by(auto elim!: FS_update_eq[of _ _ info "hvf"]) 

lemma hf_valid_uinfo:
  assumes "hf_valid ainfo (upd_uinfo uinfo y) y nxt" "hvfy = HVF y"
  shows "hvfy \<in> fset uinfo"
  apply (cases y) 
  using assms by(auto simp add: hf_valid_invert elim!: FS_contains_elem)

text\<open>A single step of extract. Extract on a single valid hop field is equivalent to that hop field's
hop info field concat extract on the next hop field, where the next hop field has to be valid
with uinfo updated.\<close>
lemma extr_hf_valid:
  assumes "hf_valid ainfo uinfo x nxt" "hf_valid ainfo (upd_uinfo uinfo y) y nxt'"
  shows "extr (HVF x) = AHI x # extr (HVF y)"
proof-
  obtain uinfo' where info'_def: "uinfo' = xor uinfo {|HVF y|}" by simp
  obtain ts ahi upif downif hvfx ahi' upif' downif' hvfy where unfolded_defs:
    "x = \<lparr>AHI = ahi, UHI = (), HVF = hvfx\<rparr>"
    "ASIF (UpIF ahi) upif"
    "ASIF (DownIF ahi) downif"
    "hvfx = Mac[macKey (ASID ahi)] (L [Num ts, upif, downif, FS uinfo])"
    "y = \<lparr>AHI = ahi', UHI = (), HVF = hvfy\<rparr>"
    "ASIF (UpIF ahi') upif'"
    "ASIF (DownIF ahi') downif'"
    "hvfy = Mac[macKey (ASID ahi')] (L [Num ts, upif', downif', FS (uinfo')])"
    using assms apply(auto simp only: hf_valid_invert) by (auto simp add: info'_def)
  have hvfy_in_uinfo: "hvfy \<in> fset uinfo" 
    using assms(2) apply(auto intro!: hf_valid_uinfo) using unfolded_defs by simp
  then obtain fcard_uinfo_minus1 where "fcard uinfo = Suc fcard_uinfo_minus1"
    by (metis fcard_Suc_fminus1)
  then show ?thesis 
    apply(cases y)
    using unfolded_defs(1-7) apply (auto intro!: ahi_eq)
    subgoal for nextmac (*difficult case*)
      apply(auto simp add: THE_nextmac dest!: FS_update_eq[of "nextmac" _
             _ "hvfy" "(\<lambda>x. Mac[macKey (ASID ahi')] (L [Num ts, upif', downif', x]))"])
      using unfolded_defs(8) info'_def by fastforce+
    using hvfy_in_uinfo unfolded_defs(8) info'_def 
    by (fastforce dest!: fcard_Suc_fminus1[simplified] elim!: allE[of _ "HVF y"])
qed

(******************************************************************************)
subsection\<open>Direct proof goals for interpretation of @{text "dataplane_3_directed"}\<close>
(******************************************************************************)
lemma COND_honest_hf_analz:
  assumes "ASID (AHI hf) \<notin> bad" "hf_valid ainfo uinfo hf nxt" "terms_hf hf \<subseteq> synth (analz ik)"
    "no_oracle ainfo uinfo"
    shows "terms_hf hf \<subseteq> analz ik"
proof-
  let ?asid = "ASID (AHI hf)"
  from assms(3) have hf_synth_ik: "HVF hf \<in> synth ik" by auto
  from assms(2) have "mac_format (HVF hf) ?asid"
    by(auto simp add: mac_format_def hf_valid_invert)
  then obtain hfs uinfo' where
    "hf \<in> set hfs" "(ainfo, hfs) \<in> auth_seg2 uinfo'"
    using assms(1,2) hf_synth_ik by(auto dest!: MAC_synth)
  then have "HVF hf \<in> ik"
    using assms(2)
    by(auto simp add: ik_hfs_def intro!: ik_ik_hfs intro!: exI) 
  then show ?thesis by auto
qed

lemma COND_terms_hf:
  assumes "hf_valid ainfo uinfo hf nxt" "terms_hf hf \<subseteq> analz ik"
      "no_oracle ainfo uinfo"
  shows "\<exists>hfs. hf \<in> set hfs \<and> (\<exists>uinfo' . (ainfo, hfs) \<in> (auth_seg2 uinfo'))"
proof-
  obtain hfs ainfo uinfo where hfs_def: "hf \<in> set hfs" "(ainfo, hfs) \<in> auth_seg2 uinfo"
    using assms 
    by(simp only: analz_parts_ik parts_ik)
      (auto 3 4 simp add: hf_valid_invert ik_hfs_simp ik_simpler dest: ahi_eq)
  show ?thesis 
    using hfs_def apply (auto simp add: auth_seg2_def dest!: TWu.holds_set_list)
    using hfs_def assms(1) by (auto simp add: auth_seg2_def dest: info_hvf)
qed

lemmas COND_auth_restrict_upd = auth_restrict_upd

lemma COND_extr_prefix_path:
  "\<lbrakk>hfs_valid ainfo uinfo l nxt; auth_restrict ainfo uinfo l\<rbrakk> \<Longrightarrow> prefix (extr_from_hd l) (AHIS l)"
proof(induction l nxt rule: TWu.holds.induct[where ?upd=upd_uinfo])
  case (1 info x y ys nxt)
  from 1(2-3) have hfs_valid: 
                   "hfs_valid ainfo (upd_uinfo info y) (y # ys) nxt" 
                   "auth_restrict ainfo (upd_uinfo info y) (y # ys)"
    by(auto simp only: TWu.holds.simps intro!: auth_restrict_upd)
  then have prefix_y: "prefix (extr_from_hd (y # ys)) (AHIS (y # ys))" by(rule 1(1))
  have "extr_from_hd (x # y # ys) = AHI x # extr_from_hd (y # ys)" 
    apply(cases ys) 
    using 1(2) by(auto simp only: extr_from_hd.simps TWu.holds.simps intro!: extr_hf_valid)
  then show ?case
    using prefix_y by (auto)
qed(auto simp only: TWu.holds.simps hf_valid_invert,
    auto simp add: fcard_fempty auth_restrict_def intro!: ahi_eq dest!: FS_contr)

lemma COND_path_prefix_extr:
  "prefix (AHIS (hfs_valid_prefix ainfo uinfo l nxt))
          (extr_from_hd l)"
proof(induction l nxt rule: TWu.takeW.induct[where ?Pa="hf_valid ainfo", where ?upd=upd_uinfo])
  case (2 info x xo)
  then show ?case 
    apply(cases "fcard info")
    by(auto 3 4 intro!: ahi_eq simp add: fcard_fempty TWu.takeW_split_tail TWu.takeW.simps(1) hf_valid_invert)
next
  case (4 info x y xs xo)
 from 4(1) show ?case 
  proof (cases "hf_valid ainfo (upd_uinfo info y) y (head xs)")
    case hf_valid_y: True
    obtain info' where info'_def: "info' = xor info {|HVF y|}" by simp
    show ?thesis 
    proof(rule prefix_cons[where ?ys="extr_from_hd (y # xs)", where ?x = "AHI x"])
      show "extr_from_hd (x # y # xs) = AHI x # extr_from_hd (y # xs)"
        using hf_valid_y 4(1)
        by(auto simp del: upd_uinfo_def elim!: extr_hf_valid[rotated])
    next
      have "prefix (map AHI (hfs_valid_prefix ainfo (upd_uinfo info y) (y # xs) xo)) (extr (HVF y))"
        using 4(2) by (auto simp del: upd_uinfo_def)
      then show "prefix (AHIS (hfs_valid_prefix ainfo info (x # y # xs) xo)) (AHI x # extr (HVF y))"
        by (auto simp add: TWu.takeW_split_tail[where ?x = x] TWu.takeW.simps(1) simp del: upd_uinfo_def)
    qed(auto)
  next
    case False
    then show ?thesis 
      by(auto simp add: TWu.takeW_split_tail hf_valid_invert) 
        (auto simp add: fcard_fempty intro!: ahi_eq)
  qed
qed(auto simp add: TWu.takeW_split_tail TWu.takeW.simps(1))

lemma COND_hf_valid_uinfo:
  "\<lbrakk>hf_valid ainfo uinfo hf nxt; hf_valid ainfo' uinfo' hf nxt'\<rbrakk> \<Longrightarrow> uinfo' = uinfo"
  by(auto simp add: hf_valid_invert)

lemma COND_upd_uinfo_ik: 
    "\<lbrakk>terms_uinfo uinfo \<subseteq> synth (analz ik); terms_hf hf \<subseteq> synth (analz ik)\<rbrakk> 
    \<Longrightarrow> terms_uinfo (upd_uinfo uinfo hf) \<subseteq> synth (analz ik)"
  by fastforce

lemma COND_upd_uinfo_no_oracle: 
  "no_oracle ainfo uinfo \<Longrightarrow> no_oracle ainfo (upd_uinfo uinfo fld)"
  by (auto)

(******************************************************************************)
subsection\<open>Instantiation of @{text "dataplane_3_directed"} locale\<close>
(******************************************************************************)
print_locale dataplane_3_directed
sublocale
  dataplane_3_directed _ _ _ auth_seg0 terms_uinfo terms_hf hf_valid auth_restrict extr extr_ainfo term_ainfo 
            upd_uinfo ik_add 
            ik_oracle no_oracle
  apply unfold_locales
  using COND_terms_hf COND_honest_hf_analz COND_extr_prefix_path
  COND_path_prefix_extr COND_hf_valid_uinfo COND_upd_uinfo_ik COND_upd_uinfo_no_oracle 
  COND_auth_restrict_upd by auto


(******************************************************************************)
subsection\<open>Normalization of terms\<close>
(******************************************************************************)
text\<open>We now show that all terms that occur in reachable states are normalized, meaning that they 
do not have directly nested FSets. For instance, a term @{term "FS {| FS {| Num 0 |}, Num 0 |}"} is
not normalized, whereas @{term "FS {| Hash (FS {| Num 0 |}), Num 0 |}"} is normalized.\<close>

lemma normalized_upd:
  "\<lbrakk>normalized (FS (upd_uinfo info y)); normalized (FS {| HVF y |})\<rbrakk> 
  \<Longrightarrow> normalized (FS info)"
  by(auto simp add: xor_singleton)

declare normalized.Lst[intro!] normalized.FSt[intro!] normalized.Hash[intro!] normalized.MPair[intro!]

lemma auth_uinfo_normalized:
  "\<lbrakk>hfs_valid ainfo uinfo hfs nxt; auth_restrict ainfo uinfo hfs\<rbrakk> \<Longrightarrow> normalized (FS uinfo)"
proof(induction hfs nxt arbitrary: rule: TWu.holds.induct[where ?upd=upd_uinfo])
  case (1 info x y ys nxt)
  from 1 have hfs_valid: "hf_valid ainfo info x (Some y)"
                   "hfs_valid ainfo (upd_uinfo info y) (y # ys) nxt" 
                   "auth_restrict ainfo (upd_uinfo info y) (y # ys)"
    by(auto simp only: TWu.holds.simps intro!: auth_restrict_upd)
  then have normalized_upd_y: "normalized (FS (upd_uinfo info y))" by (elim 1(1))
  obtain z where hfy_valid: "hf_valid ainfo (upd_uinfo info y) y z" 
    using hfs_valid(2) by(auto dest: hfs_valid_first)
  obtain info_s where info_s_def[simp]: "xor info {|HVF y|} = info_s" by simp
  from normalized_upd_y show ?case
    apply(auto elim!: normalized_upd simp only:)
    using hfy_valid info_s_def normalized_upd_y 
    by (auto 3 4 simp add: hf_valid_invert elim: ASIF.elims(2))
qed(auto simp only: TWu.holds.simps auth_restrict_def, 
    auto simp add: hf_valid_invert)

lemma auth_normalized_hf: 
  assumes "auth_restrict ainfo uinfo (pre @ hf # post)"
          "hfs_valid ainfo (upds_uinfo_shifted uinfo pre hf) (hf # post) nxt"
          "upds_uinfo_shifted uinfo pre hf = hf_uinfo" 
  shows "normalized (HVF hf)"
  using assms(1-2)
  apply(auto dest!: hfs_valid_first simp add: hf_valid_invert assms(3))
  using assms(2-3) 
  by(auto dest!: auth_uinfo_normalized dest: auth_restrict_app elim: ASIF.elims(2))

lemma auth_normalized:
  "\<lbrakk>hf \<in> set hfs; hfs_valid ainfo uinfo hfs nxt; auth_restrict ainfo uinfo hfs\<rbrakk> 
    \<Longrightarrow> normalized (HVF hf)"
  by(auto dest: TWu.holds_intermediate_ex intro: auth_normalized_hf)

text\<open>All terms derivable by the intruder are normalized. Note that (i) the dynamic intruder knowledge 
@{text "ik_dyn"} contains all terms of messages contained in the state and (ii) the dynamic intruder
knowledge remains constant. Hence this lemma suffices to show that all terms contained in @{text "int"}
and @{text "ext"} channels of reachable states are normalized as well.\<close>
lemma ik_synth_normalized: "t \<in> synth (analz ik) \<Longrightarrow> normalized t"
  by (auto, auto simp add: ik_simpler)
     (auto simp add: ik_hfs_def auth_seg2_def hfs_valid_prefix_generic_def 
              elim!: auth_normalized)


end
end
