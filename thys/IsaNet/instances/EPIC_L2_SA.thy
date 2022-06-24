(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)

section \<open>EPIC Level 2 in the Strong Attacker Model\<close>
theory EPIC_L2_SA
  imports
    "../Parametrized_Dataplane_3_directed"
    "../infrastructure/Keys"
begin

type_synonym EPIC_HF = "(unit, msgterm) HF"
type_synonym UINFO = "nat"

locale epic_l2_defs = network_assums_direct _ _ _ auth_seg0 
  for auth_seg0 :: "(msgterm \<times> ahi list) set" +
  fixes no_oracle :: "msgterm \<Rightarrow> UINFO \<Rightarrow> bool"
begin

(******************************************************************************)
subsection \<open>Hop validation check and extract functions\<close>
(******************************************************************************)

text\<open>We model the host key, i.e., the DRKey shared between an AS and an end host as a pair of AS
identifier and source identifier. Note that this "key" is not necessarily secret.
Because the source identifier is not directly embedded, we extract it from the uinfo field.
The uinfo (i.e., the token) is derived from the source address. We thus assume 
that there is some function that extracts the source identifier from the uinfo field.\<close>
definition source_extract :: "msgterm \<Rightarrow> msgterm" where "source_extract = undefined"

definition K_i :: "as \<Rightarrow> msgterm \<Rightarrow> msgterm" where
  "K_i asid uinfo = \<langle>AS asid, source_extract uinfo\<rangle>"

text\<open>The predicate @{term "hf_valid"} is given to the concrete parametrized model as a parameter.
It ensures the authenticity of the hop authenticator in the hop field. The predicate takes an authenticated
info field (in this model always a numeric value, hence the matching on Num ts), an unauthenticated
info field uinfo, the hop field to be validated and in some cases the next hop field.

We distinguish if there is a next hop field (this yields the two cases below). If there is not, then
the hop authenticator @{text "\<sigma>"} simply consists of a MAC over the authenticated info field and the local
routing information of the hop, using the key of the hop to which the hop field belongs. If on the
other hand, there is a subsequent hop field, then the uhi field of that hop field is also included
in the MAC computation.

The hop authenticator @{text "\<sigma>"} is used to compute both the hop validation field and the uhi field.
The first is computed as a MAC over the path origin (pair of absolute timestamp ts and the relative
timestamp given in uinfo), using the hop authenticator as a key to the MAC. The hop authenticator
is not secret, and any end host can use it to create a valid hvf. The uhi field, according to the 
protocol description, is @{text "\<sigma>"} shortened to a few bytes. We model this as applying the hash on @{text "\<sigma>"}.

The predicate @{term "hf_valid"} checks if the hop authenticator, hvf and uhi field are computed
correctly.\<close>
fun hf_valid :: "msgterm \<Rightarrow> UINFO
    \<Rightarrow> EPIC_HF
    \<Rightarrow> EPIC_HF option \<Rightarrow> bool" where 
  "hf_valid (Num ts) uinfo \<lparr>AHI = ahi, UHI = uhi, HVF = x\<rparr> (Some \<lparr>AHI = ahi2, UHI = uhi2, HVF = x2\<rparr>) \<longleftrightarrow> 
    (\<exists>\<sigma> upif downif. \<sigma> = Mac[macKey (ASID ahi)] (L [Num ts, upif, downif, uhi2]) \<and>
          ASIF (DownIF ahi) downif \<and> ASIF (UpIF ahi) upif \<and> uhi = Hash \<sigma> \<and> 
          x = Mac[K_i (ASID ahi) (Num uinfo)] \<langle>Num ts, Num uinfo, \<sigma>\<rangle>)"
| "hf_valid (Num ts) uinfo \<lparr>AHI = ahi, UHI = uhi, HVF = x\<rparr> None \<longleftrightarrow> 
    (\<exists>\<sigma> upif downif. \<sigma> = Mac[macKey (ASID ahi)] (L [Num ts, upif, downif]) \<and>
          ASIF (DownIF ahi) downif \<and> ASIF (UpIF ahi) upif \<and> uhi = Hash \<sigma> \<and> 
          x = Mac[K_i (ASID ahi) (Num uinfo)] \<langle>Num ts, Num uinfo, \<sigma>\<rangle>)"
| "hf_valid _ _ _ _ = False"

abbreviation upd_uinfo :: "nat \<Rightarrow> EPIC_HF \<Rightarrow> nat" where
  "upd_uinfo uinfo hf \<equiv> uinfo"

text\<open>We can extract the entire path from the uhi field, since it includes the hop authenticator, 
which includes the local forwarding information as well as, recursively, all upstream hop 
authenticators and their hop information.
However, the parametrized model defines the extract function to operate on the hop validation field,
not the uhi field. We therefore define a separate function that extracts the path from a hvf. 
We can do so, as both hvf and uhi contain the hop authenticator.
Internally, that function uses @{term "extrUhi"}.\<close>
fun extrUhi :: "msgterm \<Rightarrow> ahi list" where
  "extrUhi (Hash (Mac[macKey asid] (L [ts, upif, downif, uhi2])))
 = \<lparr>UpIF = term2if upif, DownIF = term2if downif, ASID = asid\<rparr> # extrUhi uhi2"
| "extrUhi (Hash (Mac[macKey asid] (L [ts, upif, downif])))
 = [\<lparr>UpIF = term2if upif, DownIF = term2if downif, ASID = asid\<rparr>]"
| "extrUhi _ = []"

text\<open>This function extracts from a hop validation field (HVF hf) the entire path.\<close>
fun extr :: "msgterm \<Rightarrow> ahi list" where
  "extr (Mac[_] \<langle>_, _, \<sigma>\<rangle>) = extrUhi (Hash \<sigma>)" 
   | "extr _ = []"

text\<open>Extract the authenticated info field from a hop validation field.\<close>
fun extr_ainfo :: "msgterm \<Rightarrow> msgterm" where 
  "extr_ainfo (Mac[_] \<langle>Num ts, _, _\<rangle>) = Num ts"
| "extr_ainfo _ = \<epsilon>"

abbreviation term_ainfo :: "msgterm \<Rightarrow> msgterm" where
  "term_ainfo \<equiv> id"

text\<open>When observing a hop field, an attacker learns the HVF and the UHI. The AHI only contains 
public information that are not terms.\<close>
fun terms_hf :: "EPIC_HF \<Rightarrow> msgterm set" where 
  "terms_hf hf = {HVF hf, UHI hf}"

abbreviation terms_uinfo :: "UINFO \<Rightarrow> msgterm set" where 
  "terms_uinfo x \<equiv> {}"

text\<open>An authenticated info field is always a number (corresponding to a timestamp). The 
     unauthenticated info field is as well a number, representing combination of timestamp offset
     and SRC address.\<close>
definition auth_restrict where 
  "auth_restrict ainfo uinfo l \<equiv> (\<exists>ts. ainfo = Num ts)"

text\<open>We now define useful properties of the above definition.\<close>
lemma hf_valid_invert:
  "hf_valid tsn uinfo hf mo \<longleftrightarrow>
   ((\<exists>ahi ahi2 \<sigma> ts upif downif asid x upif2 downif2 asid2 uhi uhi2 x2.
     hf = \<lparr>AHI = ahi, UHI = uhi, HVF = x\<rparr> \<and>
     ASID ahi = asid \<and> ASIF (DownIF ahi) downif \<and> ASIF (UpIF ahi) upif \<and>
     mo = Some \<lparr>AHI = ahi2, UHI = uhi2, HVF = x2\<rparr> \<and>
     ASID ahi2 = asid2 \<and> ASIF (DownIF ahi2) downif2 \<and> ASIF (UpIF ahi2) upif2 \<and>
     \<sigma> = Mac[macKey asid] (L [tsn, upif, downif, uhi2]) \<and>
     tsn = Num ts \<and>
     uhi = Hash \<sigma> \<and>
     x = Mac[K_i (ASID ahi) (Num uinfo)] \<langle>tsn, Num uinfo, \<sigma>\<rangle>)
 \<or> (\<exists>ahi \<sigma> ts upif downif asid uhi x.
     hf = \<lparr>AHI = ahi, UHI = uhi, HVF = x\<rparr> \<and>
     ASID ahi = asid \<and> ASIF (DownIF ahi) downif \<and> ASIF (UpIF ahi) upif \<and>
     mo = None \<and>
     \<sigma> = Mac[macKey asid] (L [tsn, upif, downif]) \<and>
     tsn = Num ts \<and>
     uhi = Hash \<sigma> \<and>
     x = Mac[K_i (ASID ahi) (Num uinfo)] \<langle>tsn, Num uinfo, \<sigma>\<rangle>)
    )"
  apply(auto elim!: hf_valid.elims) using option.exhaust ASIF.simps by metis+

lemma hf_valid_auth_restrict[dest]: "hf_valid ainfo uinfo hf z \<Longrightarrow> auth_restrict ainfo uinfo l"
  by(auto simp add: hf_valid_invert auth_restrict_def)

lemma auth_restrict_ainfo[dest]: "auth_restrict ainfo uinfo l \<Longrightarrow> \<exists>ts. ainfo = Num ts"
  by(auto simp add: auth_restrict_def)

lemma info_hvf: 
  assumes "hf_valid ainfo uinfo m z" "HVF m = Mac[k_i] \<langle>ainfo', Num uinfo', \<sigma>\<rangle> \<or> hf_valid ainfo' uinfo' m z'" 
  shows "uinfo = uinfo'" "ainfo' = ainfo"
  using assms by(auto simp add: hf_valid_invert)

(******************************************************************************)
subsection\<open>Definitions and properties of the added intruder knowledge\<close>
(******************************************************************************)
text\<open>Here we define two sets which are added to the intruder knowledge: @{text "ik_add"}, which contains hop
authenticators. And @{text "ik_oracle"}, which contains the oracle's output to the strong attacker.\<close>
text\<open>Here we define two sets which are added to the intruder knowledge: @{text "ik_add"}, which contains hop
authenticators. And @{text "ik_oracle"}, which contains the oracle's output to the strong attacker.\<close>
print_locale dataplane_3_directed_defs 
sublocale dataplane_3_directed_defs _ _ _ auth_seg0 hf_valid auth_restrict extr extr_ainfo term_ainfo 
                 terms_hf terms_uinfo upd_uinfo no_oracle
  by unfold_locales

abbreviation is_oracle where "is_oracle ainfo t \<equiv> \<not> no_oracle ainfo t "

declare TWu.holds_set_list[dest]
declare TWu.holds_takeW_is_identity[simp]
declare parts_singleton[dest]

text\<open>This additional Intruder Knowledge allows us to model the attacker's access not only to the 
hop validation fields and segment identifiers of authorized segments (which are already given in 
@{text "ik_hfs"}), but to the underlying hop authenticators that are used to create them.\<close>

definition ik_add :: "msgterm set" where
  "ik_add \<equiv> { \<sigma> | ainfo uinfo l hf \<sigma> k_i.  
                 (ainfo, l) \<in> auth_seg2 uinfo
                  \<and> hf \<in> set l \<and> HVF hf = Mac[k_i] \<langle>ainfo, Num uinfo, \<sigma>\<rangle> }"

lemma ik_addI:
  "\<lbrakk>(ainfo, l) \<in> auth_seg2 uinfo; hf \<in> set l; HVF hf = Mac[k_i] \<langle>ainfo, Num uinfo, \<sigma>\<rangle>\<rbrakk> \<Longrightarrow> \<sigma> \<in> ik_add"
  apply(auto simp add: ik_add_def)
  by blast

lemma ik_add_form: "t \<in> ik_add \<Longrightarrow> \<exists> asid l . t = Mac[macKey asid] l"
(*  using [[unify_trace_failure]]*)
  by(auto simp add: ik_add_def auth_seg2_def dest!: TWu.holds_set_list)
    (auto simp add: hf_valid_invert)

lemma parts_ik_add[simp]: "parts ik_add = ik_add"
  by (auto intro!: parts_Hash dest: ik_add_form)

text\<open>This is the oracle output provided to the adversary. Only those hop validation fields and 
segment identifiers whose path origin (combination of ainfo uinfo) is not contained in 
@{term "no_oracle"} appears here.\<close>
definition ik_oracle :: "msgterm set" where 
  "ik_oracle = {t | t ainfo hf l uinfo . hf \<in> set l \<and> hfs_valid_None ainfo uinfo l \<and> 
                    is_oracle ainfo uinfo \<and> (ainfo, l) \<notin> auth_seg2 uinfo \<and> (t = HVF hf \<or> t = UHI hf) }"

lemma ik_oracle_parts_form:
"t \<in> ik_oracle \<Longrightarrow> 
  (\<exists> asid l ainfo uinfo k_i . t = Mac[k_i] \<langle>ainfo, Num uinfo, Mac[macKey asid] l\<rangle>) \<or>
  (\<exists> asid l . t = Hash (Mac[macKey asid] l))"
  by(auto simp add: ik_oracle_def hf_valid_invert dest!: TWu.holds_set_list)

lemma parts_ik_oracle[simp]: "parts ik_oracle = ik_oracle"
  by (auto intro!: parts_Hash dest: ik_oracle_parts_form)

lemma ik_oracle_simp: "t \<in> ik_oracle \<longleftrightarrow>
      (\<exists>ainfo hf l uinfo. hf \<in> set l \<and> hfs_valid_None ainfo uinfo l \<and> is_oracle ainfo uinfo
                       \<and> (ainfo, l) \<notin> auth_seg2 uinfo \<and> (t = HVF hf \<or> t = UHI hf))"
  by(rule iffI, frule ik_oracle_parts_form)
    (auto simp add: ik_oracle_def hf_valid_invert)

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

lemma ik_hfs_form: "t \<in> parts ik_hfs \<Longrightarrow> \<exists> t' . t = Hash t'"
  by(auto 3 4 simp add: auth_seg2_def hf_valid_invert)

declare ik_hfs_def[simp del]

lemma parts_ik_hfs[simp]: "parts ik_hfs = ik_hfs"
  by (auto intro!: parts_Hash ik_hfs_form)

text\<open>This lemma allows us not only to expand the definition of @{term "ik_hfs"}, but also 
to obtain useful properties, such as a term being a Hash, and it being part of a valid hop field.\<close>
lemma ik_hfs_simp: 
  "t \<in> ik_hfs \<longleftrightarrow> (\<exists>t' . t = Hash t') \<and> (\<exists>hf . (t = HVF hf \<or> t = UHI hf)
                    \<and> (\<exists>hfs. hf \<in> set hfs \<and> (\<exists>ainfo uinfo . (ainfo, hfs) \<in> auth_seg2 uinfo
                    \<and> (\<exists> nxt. hf_valid ainfo uinfo hf nxt))))" (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  assume asm: "?lhs" 
  then obtain ainfo uinfo hf hfs where 
    dfs: "hf \<in> set hfs" "(ainfo, hfs) \<in> auth_seg2 uinfo" "t = HVF hf \<or> t = UHI hf"
    by(auto simp add: ik_hfs_def)
  then have "hfs_valid_None ainfo uinfo hfs"  "(ainfo, AHIS hfs) \<in> auth_seg0"
    by(auto simp add: auth_seg2_def)
  then show "?rhs" using asm dfs 
    by (auto 3 4 simp add: auth_seg2_def intro!: ik_hfs_form exI[of _ hf] exI[of _ hfs] 
                     dest: TWu.holds_set_list_no_update)
qed(auto simp add: ik_hfs_def)

(******************************************************************************)
subsubsection \<open>Properties of Intruder Knowledge\<close>
(******************************************************************************)
lemma auth_ainfo[dest]: "\<lbrakk>(ainfo, hfs) \<in> auth_seg2 uinfo\<rbrakk> \<Longrightarrow> \<exists> ts . ainfo = Num ts"
  by(auto simp add: auth_seg2_def)

text \<open>There are no ciphertexts (or signatures) in @{term "parts ik"}. Thus, @{term "analz ik"}
and @{term "parts ik"} are identical.\<close>
lemma analz_parts_ik[simp]: "analz ik = parts ik"
  apply(rule no_crypt_analz_is_parts)
  by(auto simp add: ik_def auth_seg2_def auth_restrict_def ik_hfs_simp)
    (auto simp add: ik_add_def ik_oracle_def auth_seg2_def hf_valid_invert hfs_valid_prefix_generic_def 
          dest!: TWu.holds_set_list)

lemma parts_ik[simp]: "parts ik = ik"
  by(auto 3 4 simp add: ik_def auth_seg2_def auth_restrict_def dest!: parts_singleton_set)

lemma key_ik_bad: "Key (macK asid) \<in> ik \<Longrightarrow> asid \<in> bad"
  by(auto simp add: ik_def hf_valid_invert ik_oracle_simp)
    (auto 3 4 simp add: auth_seg2_def ik_hfs_simp ik_add_def hf_valid_invert)

(******************************************************************************)
subsubsection\<open>Hop authenticators are agnostic to uinfo field\<close>
(******************************************************************************)

fun K_i_upd :: "msgterm \<Rightarrow> msgterm \<Rightarrow> msgterm" where
  "K_i_upd \<langle>AS asid, _\<rangle> uinfo' = \<langle>AS asid, source_extract uinfo'\<rangle>"
| "K_i_upd _ _ = \<epsilon>"

text\<open>Those hop validation fields contained in @{term "auth_seg2"} or that can be generated from the hop
authenticators in @{text "ik_add"} have the property that they are agnostic about the uinfo field. If a
hop validation field is contained in @{term "auth_seg2"} (resp. derivable from @{text "ik_add"}), 
then a field with a different uinfo is also contained (resp. derivable).
To show this, we first define a function that updates uinfo in a hop validation field.\<close>
fun uinfo_change_hf :: "UINFO \<Rightarrow> EPIC_HF \<Rightarrow> EPIC_HF" where
  "uinfo_change_hf new_uinfo hf = 
    (case HVF hf of Mac[k_i] \<langle>ainfo, Num uinfo, \<sigma>\<rangle> 
  \<Rightarrow> hf\<lparr>HVF := Mac[K_i_upd k_i (Num new_uinfo)] \<langle>ainfo, Num new_uinfo, \<sigma>\<rangle>\<rparr> | _ \<Rightarrow> hf)"

fun uinfo_change :: "UINFO \<Rightarrow> EPIC_HF list \<Rightarrow> EPIC_HF list" where 
  "uinfo_change new_uinfo hfs = map (uinfo_change_hf new_uinfo) hfs"

lemma uinfo_change_valid: 
  "hfs_valid ainfo uinfo l nxt \<Longrightarrow> hfs_valid ainfo new_uinfo (uinfo_change new_uinfo l) nxt"
  apply(induction l nxt rule: TWu.holds.induct[where ?upd=upd_uinfo])
  apply auto
  subgoal for info x y ys nxt
    by(cases "map (uinfo_change_hf new_uinfo) ys") (*takes a few seconds*)
      (cases info, auto 3 4 simp add: K_i_def TWu.holds_split_tail hf_valid_invert)+
  by(auto 3 4 simp add: K_i_def TWu.holds_split_tail hf_valid_invert TWu.holds.simps)

lemma uinfo_change_hf_AHI: "AHI (uinfo_change_hf new_uinfo hf) = AHI hf"
  apply(cases "HVF hf") apply auto
  subgoal for k_i apply(cases k_i) apply auto
    subgoal for as uinfo apply(cases uinfo) apply auto 
      subgoal for x1 x2 apply(cases x2) apply auto
      subgoal for x3 apply(cases x3) by auto
    done
  done
  done
  done

lemma uinfo_change_hf_AHIS[simp]: "AHIS (map (uinfo_change_hf new_uinfo) l) = AHIS l"
  apply(induction l) using uinfo_change_hf_AHI by auto

lemma uinfo_change_auth_seg2:
  assumes "hf_valid ainfo uinfo m z" "\<sigma> = Mac[Key (macK asid)] j"
          "HVF m = Mac[k_i] \<langle>ainfo, uinfo', \<sigma>\<rangle>" "\<sigma> \<in> ik_add" "no_oracle ainfo uinfo"
  shows "\<exists>hfs. m \<in> set hfs \<and> (\<exists>uinfo''. (ainfo, hfs) \<in> auth_seg2 uinfo'')"
proof-
  from assms(4) obtain ainfo_add uinfo_add l_add hf_add k_i_add where
    "(ainfo_add, l_add) \<in> auth_seg2 uinfo_add" "hf_add \<in> set l_add"     
    "HVF hf_add = Mac[k_i_add] \<langle>ainfo_add, Num uinfo_add, \<sigma>\<rangle>"
    by(auto simp add: ik_add_def)
  then have add: "m \<in> set (uinfo_change uinfo l_add)" "(ainfo_add, (uinfo_change uinfo l_add)) \<in> auth_seg2 uinfo"
    using assms(1-3,5) apply(auto simp add: auth_seg2_def simp del: AHIS_def)
       apply(auto simp add: hf_valid_invert intro!: image_eqI dest!: TWu.holds_set_list)[1]
       apply(auto simp add: auth_restrict_def intro!: exI elim: ahi_eq dest: uinfo_change_valid simp del: AHIS_def)
    by(auto simp add: hf_valid_invert K_i_def dest!: TWu.holds_set_list_no_update)
  then have "ainfo_add = ainfo" 
    using assms(1) by(auto simp add: auth_seg2_def dest!: TWu.holds_set_list dest: info_hvf)
  then show ?thesis using add by fastforce
qed

lemma MAC_synth_oracle:
  assumes "hf_valid ainfo uinfo m z" "HVF m \<in> ik_oracle"
  shows "is_oracle ainfo uinfo"
  using assms 
  by(auto simp add: ik_oracle_def assms(1) hf_valid_invert dest!: TWu.holds_set_list_no_update)

lemma ik_oracle_is_oracle:
  "\<lbrakk>Mac[\<sigma>] \<langle>ainfo, Num uinfo\<rangle> \<in> ik_oracle\<rbrakk> \<Longrightarrow> is_oracle ainfo uinfo"
  by (auto simp add: ik_oracle_def dest: info_hvf)
     (auto dest!: TWu.holds_set_list_no_update simp add: hf_valid_invert)

lemma MAC_synth_helper:
"\<lbrakk>hf_valid ainfo uinfo m z; no_oracle ainfo uinfo;
  HVF m = Mac[k_i] \<langle>ainfo, Num uinfo, \<sigma>\<rangle>; \<sigma> = Mac[Key (macK asid)] j; \<sigma> \<in> ik \<or> HVF m \<in> ik\<rbrakk>
       \<Longrightarrow> \<exists>hfs. m \<in> set hfs \<and> (\<exists>uinfo'. (ainfo, hfs) \<in> auth_seg2 uinfo')"
  apply(auto simp add: ik_def ik_hfs_simp 
                 dest: MAC_synth_oracle ik_add_form ik_oracle_parts_form[simplified])
  subgoal by(auto simp add: hf_valid_invert simp add: K_i_def)
  subgoal by(auto simp add: hf_valid_invert simp add: K_i_def)
  subgoal by(auto elim!: uinfo_change_auth_seg2 simp add: K_i_def)
  subgoal apply(auto simp add: hf_valid_invert simp add: K_i_def)
    using ik_oracle_parts_form by blast+
  subgoal apply(auto simp add: hf_valid_invert simp add: K_i_def)
    using ahi_eq by blast+
  subgoal by(auto simp add: hf_valid_invert simp add: K_i_def)
  subgoal apply(auto simp add: hf_valid_invert simp add: K_i_def)
    using ik_add_form by blast+
  done

text\<open>This definition helps with the limiting the number of cases generated. We don't require it, 
but it is convenient. Given a hop validation field and an asid, return if the hvf has the expected
format.\<close>
definition mac_format :: "msgterm \<Rightarrow> as \<Rightarrow> bool" where 
  "mac_format m asid \<equiv> \<exists> j ts uinfo k_i . m = Mac[k_i] \<langle>Num ts, uinfo, Mac[macKey asid] j\<rangle>"

text\<open>If a valid hop field is derivable by the attacker, but does not belong to the attacker, and is
over a path origin that does not belong to an oracle query, then the hop field is already 
contained in the set of authorized segments.\<close>
lemma MAC_synth:
  assumes "hf_valid ainfo uinfo m z" "HVF m \<in> synth ik" "mac_format (HVF m) asid"
    "asid \<notin> bad" "checkInfo ainfo" "no_oracle ainfo uinfo" 
  shows "\<exists>hfs . m \<in> set hfs \<and> (\<exists>uinfo'. (ainfo, hfs) \<in> auth_seg2 uinfo')"
  using assms
  apply(auto simp add: mac_format_def elim!: MAC_synth_helper dest!: key_ik_bad)
  apply(auto simp add: ik_def ik_hfs_simp dest: ik_add_form dest!: ik_oracle_parts_form) (* takes a few seconds *)
  using assms(1) by(auto dest: info_hvf simp add: hf_valid_invert)

(******************************************************************************)
subsection\<open>Direct proof goals for interpretation of @{text "dataplane_3_directed"}\<close>
(******************************************************************************)

lemma COND_honest_hf_analz:
  assumes "ASID (AHI hf) \<notin> bad" "hf_valid ainfo uinfo hf nxt" "terms_hf hf \<subseteq> synth (analz ik)"
    "no_oracle ainfo uinfo"
    shows "terms_hf hf \<subseteq> analz ik"
proof-
  let ?asid = "ASID (AHI hf)"
  from assms(3) have hf_synth_ik: "HVF hf \<in> synth ik" "UHI hf \<in> synth ik" by auto
  from assms(2) have "mac_format (HVF hf) ?asid"
    by(auto simp add: mac_format_def hf_valid_invert)
  then obtain hfs uinfo where "hf \<in> set hfs" "(ainfo, hfs) \<in> auth_seg2 uinfo"
    using assms(1,2,4) hf_synth_ik by(auto dest!: MAC_synth)
  then have "HVF hf \<in> ik" "UHI hf \<in> ik" 
    using assms(2)
    by(auto simp add: ik_hfs_def intro!: ik_ik_hfs intro!: exI) 
  then show ?thesis by auto
qed

lemma COND_terms_hf: 
  assumes "hf_valid ainfo uinfo hf z" and "HVF hf \<in> ik" and "no_oracle ainfo uinfo"
  shows "\<exists>hfs. hf \<in> set hfs \<and> (\<exists>uinfo . (ainfo, hfs) \<in> auth_seg2 uinfo)"
proof-
  obtain hfs ainfo where hfs_def: "hf \<in> set hfs" "(ainfo, hfs) \<in> auth_seg2 uinfo"
    using assms apply(auto 3 4 simp add: K_i_def hf_valid_invert ik_hfs_simp ik_def dest: ahi_eq
                             dest!: ik_oracle_is_oracle ik_add_form)
    using MAC_synth_oracle assms(1) by force+
  then obtain hfs ainfo where hfs_def: "hf \<in> set hfs" "(ainfo, hfs) \<in> auth_seg2 uinfo" by auto
  show ?thesis 
    using hfs_def apply (auto simp add: auth_seg2_def dest!: TWu.holds_set_list)
    using hfs_def assms(1) by (auto simp add: auth_seg2_def dest: info_hvf)
qed

lemma COND_extr_prefix_path:
  "\<lbrakk>hfs_valid ainfo uinfo l nxt; nxt = None\<rbrakk> \<Longrightarrow> prefix (extr_from_hd l) (AHIS l)"
  by(induction l nxt rule: TWu.holds.induct[where ?upd=upd_uinfo])
    (auto simp add: K_i_def TWu.holds_split_tail TWu.holds.simps(1) hf_valid_invert,
     auto split: list.split_asm simp add: hf_valid_invert intro!: ahi_eq elim: ASIF.elims)

lemma COND_path_prefix_extr:
  "prefix (AHIS (hfs_valid_prefix ainfo uinfo l nxt))
          (extr_from_hd l)"
  apply(induction l nxt rule: TWu.takeW.induct[where ?Pa="hf_valid ainfo",where ?upd=upd_uinfo])
  by(auto simp add: TWu.takeW_split_tail TWu.takeW.simps(1))
    (auto 3 4 simp add: hf_valid_invert intro!: ahi_eq elim: ASIF.elims)

lemma COND_hf_valid_uinfo:
  "\<lbrakk>hf_valid ainfo uinfo hf nxt; hf_valid ainfo' uinfo' hf nxt'\<rbrakk> \<Longrightarrow> uinfo' = uinfo"
  by(auto dest: info_hvf)

lemma COND_upd_uinfo_ik: 
    "\<lbrakk>terms_uinfo uinfo \<subseteq> synth (analz ik); terms_hf hf \<subseteq> synth (analz ik)\<rbrakk> 
    \<Longrightarrow> terms_uinfo (upd_uinfo uinfo hf) \<subseteq> synth (analz ik)"
  by (auto)

lemma COND_upd_uinfo_no_oracle: 
  "no_oracle ainfo uinfo \<Longrightarrow> no_oracle ainfo (upd_uinfo uinfo fld)"
  by (auto)

lemma COND_auth_restrict_upd:
      "auth_restrict ainfo uinfo (x#y#hfs) 
   \<Longrightarrow> auth_restrict ainfo (upd_uinfo uinfo y) (y#hfs)"
  by (auto simp add: auth_restrict_def)


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
