(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)

section \<open>SCION Variant\<close>
text\<open>This is a slightly variant version of SCION, in which the successor's hop information is not 
embedded in the MAC of a hop field. This difference shows up in the definition of @{term "hf_valid"}.\<close>
section \<open>SCION\<close>
theory SCION_variant
  imports
    "../Parametrized_Dataplane_3_directed"
    "../infrastructure/Keys"
begin

locale scion_defs = network_assums_direct _ _ _ auth_seg0
  for auth_seg0 :: "(msgterm \<times> ahi list) set"
begin

(******************************************************************************)
subsection \<open>Hop validation check and extract functions\<close>
(******************************************************************************)
type_synonym SCION_HF = "(unit, unit) HF"

text\<open>The predicate @{term "hf_valid"} is given to the concrete parametrized model as a parameter.
It ensures the authenticity of the hop authenticator in the hop field. The predicate takes an authenticated
info field (in this model always a numeric value, hence the matching on Num ts), the hop field to 
be validated and in some cases the next hop field.

We distinguish if there is a next hop field (this yields the two cases below). If there is not, then
the hvf simply consists of a MAC over the authenticated info field and the local
routing information of the hop, using the key of the hop to which the hop field belongs. If on the
other hand, there is a subsequent hop field, then the hvf of that hop field is also included
in the MAC computation.\<close>
fun hf_valid :: "msgterm \<Rightarrow> msgterm
    \<Rightarrow> SCION_HF
    \<Rightarrow> SCION_HF option \<Rightarrow> bool" where 
  "hf_valid (Num ts) uinfo \<lparr>AHI = ahi, UHI = _, HVF = x\<rparr> (Some \<lparr>AHI = ahi2, UHI = _, HVF = x2\<rparr>) \<longleftrightarrow> 
    (\<exists>upif downif. x = Mac[macKey (ASID ahi)] (L [Num ts, upif, downif, x2]) \<and>
          ASIF (DownIF ahi) downif \<and> ASIF (UpIF ahi) upif \<and> uinfo = \<epsilon>)"
| "hf_valid (Num ts) uinfo \<lparr>AHI = ahi, UHI = _, HVF = x\<rparr> None \<longleftrightarrow> 
    (\<exists>upif downif. x = Mac[macKey (ASID ahi)] (L [Num ts, upif, downif]) \<and>
          ASIF (DownIF ahi) downif \<and> ASIF (UpIF ahi) upif \<and> uinfo = \<epsilon>)"
| "hf_valid _ _ _ _ = False"

definition upd_uinfo :: "msgterm \<Rightarrow> SCION_HF \<Rightarrow> msgterm" where
  "upd_uinfo uinfo hf \<equiv> uinfo"

text\<open>We can extract the entire path from the hvf field, which includes the local forwarding of the
current hop, the local forwarding information of the next hop (if existant) and, recursively, all 
upstream hvf fields and their hop information.\<close>
fun extr :: "msgterm \<Rightarrow> ahi list" where
  "extr (Mac[macKey asid] (L [ts, upif, downif, x2]))
 = \<lparr>UpIF = term2if upif, DownIF = term2if downif, ASID = asid\<rparr> # extr x2"
| "extr (Mac[macKey asid] (L [ts, upif, downif]))
 = [\<lparr>UpIF = term2if upif, DownIF = term2if downif, ASID = asid\<rparr>]"
| "extr _ = []"

text\<open>Extract the authenticated info field from a hop validation field.\<close>
fun extr_ainfo :: "msgterm \<Rightarrow> msgterm" where 
  "extr_ainfo (Mac[macKey asid] (L (Num ts # xs))) = Num ts"
| "extr_ainfo _ = \<epsilon>"

abbreviation term_ainfo :: "msgterm \<Rightarrow> msgterm" where
  "term_ainfo \<equiv> id"

text\<open>When observing a hop field, an attacker learns the HVF. UHI is empty and the AHI only contains 
public information that are not terms.\<close>
fun terms_hf :: "SCION_HF \<Rightarrow> msgterm set" where 
  "terms_hf hf = {HVF hf}"

abbreviation terms_uinfo :: "msgterm \<Rightarrow> msgterm set" where 
  "terms_uinfo x \<equiv> {x}"

text\<open>An authenticated info field is always a number (corresponding to a timestamp). The 
     unauthenticated info field is set to the empty term @{term "\<epsilon>"}.\<close>
definition auth_restrict where 
  "auth_restrict ainfo uinfo l \<equiv> (\<exists>ts. ainfo = Num ts) \<and> (uinfo = \<epsilon>)"

abbreviation no_oracle where "no_oracle \<equiv> (\<lambda> _ _. True)"

text\<open>We now define useful properties of the above definition.\<close>
lemma hf_valid_invert:
  "hf_valid tsn uinfo hf mo \<longleftrightarrow>
   ((\<exists>ahi ahi2 ts upif downif asid x x2.
     hf = \<lparr>AHI = ahi, UHI = (), HVF = x\<rparr> \<and>
     ASID ahi = asid \<and> ASIF (DownIF ahi) downif \<and> ASIF (UpIF ahi) upif \<and>
     mo = Some \<lparr>AHI = ahi2, UHI = (), HVF = x2\<rparr> \<and>
     x = Mac[macKey asid] (L [tsn, upif, downif, x2]) \<and>
     tsn = Num ts \<and>
     uinfo = \<epsilon>)
 \<or> (\<exists>ahi ts upif downif asid x.
     hf = \<lparr>AHI = ahi, UHI = (), HVF = x\<rparr> \<and>
     ASID ahi = asid \<and> ASIF (DownIF ahi) downif \<and> ASIF (UpIF ahi) upif \<and>
     mo = None \<and>
     x = Mac[macKey asid] (L [tsn, upif, downif]) \<and>
     tsn = Num ts \<and>
     uinfo = \<epsilon>)
    )"
  by(auto elim!: hf_valid.elims)

lemma hf_valid_auth_restrict[dest]: "hf_valid ainfo uinfo hf z \<Longrightarrow> auth_restrict ainfo uinfo l"
  by(auto simp add: hf_valid_invert auth_restrict_def)

lemma info_hvf: 
  assumes "hf_valid ainfo uinfo m z" "hf_valid ainfo' uinfo' m' z'" "HVF m = HVF m'" 
  shows "ainfo' = ainfo" "m' = m"
  using assms by(auto simp add: hf_valid_invert intro: ahi_eq)

(******************************************************************************)
subsection\<open>Definitions and properties of the added intruder knowledge\<close>
(******************************************************************************)
text\<open>Here we define a @{text "ik_add"} and @{text "ik_oracle"} as being empty, as these features are
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
subsection\<open>Properties of the intruder knowledge, including @{text "ik_add"} and  @{text "ik_oracle"}\<close>
(******************************************************************************)
text\<open>We now instantiate the parametrized model's definition of the intruder knowledge, using the
definitions of @{text "ik_add"} and  @{text "ik_oracle"} from above. We then prove the properties 
that we need to instantiate the @{text "dataplane_3_directed"} locale.\<close>
sublocale
  dataplane_3_directed_ik_defs _ _ _ auth_seg0 terms_uinfo no_oracle hf_valid auth_restrict extr extr_ainfo term_ainfo 
                  terms_hf upd_uinfo ik_add ik_oracle 
  by unfold_locales


lemma auth_ainfo[dest]: "\<lbrakk>(ainfo, hfs) \<in> auth_seg2 uinfo\<rbrakk> \<Longrightarrow> \<exists> ts . ainfo = Num ts"
  by(auto simp add: auth_seg2_def auth_restrict_def)

lemma auth_uinfo[dest]: "\<lbrakk>(ainfo, hfs) \<in> auth_seg2 uinfo\<rbrakk> \<Longrightarrow> uinfo = \<epsilon>"
  by(auto simp add: auth_seg2_def auth_restrict_def)

lemma upds_simp[simp]: "TWu.upds upd_uinfo uinfo hfs = uinfo" 
  by(induction hfs, auto simp add: upd_uinfo_def)

lemma upd_shifted_simp[simp]: "TWu.upd_shifted upd_uinfo uinfo hfs nxt = uinfo"  
  by(induction hfs, auto simp only: TWu.upd_shifted.simps upds_simp)

lemma ik_hfs_form: "t \<in> parts ik_hfs \<Longrightarrow> \<exists> t' . t = Hash t'"
  by(auto 3 4 simp add: auth_seg2_def hf_valid_invert)

declare ik_hfs_def[simp del]

lemma parts_ik_hfs[simp]: "parts ik_hfs = ik_hfs"
  by (auto intro!: parts_Hash ik_hfs_form)

text\<open>This lemma allows us not only to expand the definition of @{term "ik_hfs"}, but also 
to obtain useful properties, such as a term being a Hash, and it being part of a valid hop field.\<close>
lemma ik_hfs_simp: 
  "t \<in> ik_hfs \<longleftrightarrow> (\<exists>t' . t = Hash t') \<and> (\<exists>hf . t = HVF hf
                    \<and> (\<exists>hfs. hf \<in> set hfs \<and> (\<exists>ainfo . (ainfo, hfs) \<in> (auth_seg2 \<epsilon>)
                    \<and> (\<exists> nxt. hf_valid ainfo \<epsilon> hf nxt))))" (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  assume asm: "?lhs" 
  then obtain ainfo uinfo hf hfs where 
    dfs: "hf \<in> set hfs" "(ainfo, hfs) \<in> auth_seg2 uinfo" "t = HVF hf"
    by(auto simp add: ik_hfs_def)
  then have dfs_prop: "hfs_valid_None ainfo \<epsilon> hfs"  "(ainfo, AHIS hfs) \<in> auth_seg0"
    using auth_uinfo by(auto simp add: auth_seg2_def)
  then obtain nxt where hf_val: "hf_valid ainfo \<epsilon> hf nxt" using dfs apply auto 
    by(auto dest: TWu.holds_set_list_no_update simp add: upd_uinfo_def) 
  then show "?rhs" using asm dfs dfs_prop hf_val by(auto intro: ik_hfs_form)
qed(auto simp add: ik_hfs_def)

(******************************************************************************)
subsubsection \<open>Properties of Intruder Knowledge\<close>
(******************************************************************************)
lemma Num_ik[intro]: "Num ts \<in> ik"
  by(auto simp add: ik_def)
    (auto simp add: auth_seg2_def auth_restrict_def TWu.holds.simps 
            intro!: exI[of _ "[]"] exI[of _ "\<epsilon>"] ) (*elim!: allE[of _ "[]"]) *)

text \<open>There are no ciphertexts (or signatures) in @{term "parts ik"}. Thus, @{term "analz ik"}
and @{term "parts ik"} are identical.\<close>
lemma analz_parts_ik[simp]: "analz ik = parts ik"
  by(rule no_crypt_analz_is_parts)
    (auto simp add: ik_def auth_seg2_def ik_hfs_simp auth_restrict_def)


lemma parts_ik[simp]: "parts ik = ik"
  by(fastforce simp add: ik_def auth_seg2_def auth_restrict_def)

lemma key_ik_bad: "Key (macK asid) \<in> ik \<Longrightarrow> asid \<in> bad"
  by(auto simp add: ik_def hf_valid_invert)
    (auto 3 4 simp add: auth_seg2_def ik_hfs_simp hf_valid_invert)

lemma MAC_synth_helper:
  assumes "hf_valid ainfo uinfo m z" "HVF m = Mac[Key (macK asid)] j" "HVF m \<in> ik"
  shows "\<exists>hfs. m \<in> set hfs \<and> (\<exists>uinfo'. (ainfo, hfs) \<in> auth_seg2 uinfo')"
proof-
  from assms(2-3) obtain ainfo' uinfo' m' hfs' nxt' where dfs:
    "m' \<in> set hfs'" "(ainfo', hfs') \<in> auth_seg2 uinfo'" "hf_valid ainfo' uinfo' m' nxt'" 
    "HVF m = HVF m'"
    by(auto simp add: ik_def ik_hfs_simp)                
  then have "ainfo' = ainfo" "m' = m" using assms(1) by(auto elim!: info_hvf)
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
  assumes "hf_valid ainfo uinfo m z" "HVF m \<in> synth ik" "mac_format (HVF m) asid"
    "asid \<notin> bad" "checkInfo ainfo"
  shows "\<exists>hfs . m \<in> set hfs \<and> (\<exists>uinfo'. (ainfo, hfs) \<in> auth_seg2 uinfo')"
  using assms
  apply(auto simp add: mac_format_def elim!: MAC_synth_helper dest!: key_ik_bad)
  by(auto simp add: ik_def ik_hfs_simp)

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
  assumes "hf_valid ainfo uinfo hf z" and "terms_hf hf \<subseteq> analz ik" and "no_oracle ainfo uinfo"
  shows "\<exists>hfs. hf \<in> set hfs \<and> (\<exists>uinfo' . (ainfo, hfs) \<in> auth_seg2 uinfo')"
proof-
  obtain hfs ainfo uinfo where hfs_def: "hf \<in> set hfs" "(ainfo, hfs) \<in> auth_seg2 uinfo"
    using assms
    using assms
    by simp
       (auto 3 4 simp add: hf_valid_invert ik_hfs_simp ik_def dest: ahi_eq)
  show ?thesis 
    using hfs_def apply (auto simp add: auth_seg2_def dest!: TWu.holds_set_list)
    using hfs_def assms(1) by (auto simp add: auth_seg2_def dest: info_hvf)
  qed

lemma COND_extr_prefix_path:
  "\<lbrakk>hfs_valid ainfo uinfo l nxt; nxt = None\<rbrakk> \<Longrightarrow> prefix (extr_from_hd l) (AHIS l)"
  by(induction l nxt rule: TWu.holds.induct[where ?upd=upd_uinfo])
    (auto simp add: TWu.holds_split_tail TWu.holds.simps(1) hf_valid_invert,
     auto split: list.split_asm simp add: hf_valid_invert intro!: ahi_eq elim: ASIF.elims)

lemma COND_path_prefix_extr:
  "prefix (AHIS (hfs_valid_prefix ainfo uinfo l nxt))
          (extr_from_hd l)"
  apply(induction l nxt rule: TWu.takeW.induct[where ?Pa="hf_valid ainfo",where ?upd=upd_uinfo])
  by(auto simp add: TWu.takeW_split_tail TWu.takeW.simps(1))
    (auto 3 4 simp add: hf_valid_invert intro!: ahi_eq elim: ASIF.elims)

lemma COND_hf_valid_uinfo:
  "\<lbrakk>hf_valid ainfo uinfo hf nxt; hf_valid ainfo' uinfo' hf nxt'\<rbrakk> \<Longrightarrow> uinfo' = uinfo"
  by(auto simp add: hf_valid_invert)

lemma COND_upd_uinfo_ik: 
    "\<lbrakk>terms_uinfo uinfo \<subseteq> synth (analz ik); terms_hf hf \<subseteq> synth (analz ik)\<rbrakk> 
    \<Longrightarrow> terms_uinfo (upd_uinfo uinfo hf) \<subseteq> synth (analz ik)"
  by (auto simp add: upd_uinfo_def)

lemma COND_upd_uinfo_no_oracle: "no_oracle ainfo uinfo \<Longrightarrow> no_oracle ainfo (upd_uinfo_pkt m)"
  by simp

lemma COND_auth_restrict_upd:
      "auth_restrict ainfo uinfo (x#y#hfs) 
   \<Longrightarrow> auth_restrict ainfo (upd_uinfo uinfo y) (y#hfs)"
  by (auto simp add: auth_restrict_def upd_uinfo_def)

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

end
end
