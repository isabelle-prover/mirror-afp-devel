(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)

section \<open>ICING\<close>
text\<open>We abstract and simplify from the protocol ICING in several ways. First, we only consider 
Proofs of Consent (PoC), not Proofs of Provenance (PoP). Our framework does not support proving the
path validation properties that PoPs provide, and it also currently does not support XOR, and 
dynamically changing hop fields.
Thus, instead of embedding $A_i \oplus PoP_{0,1}$, we embed $A_i$ directly.
We also remove the payload from the Hash that is included in each packet.

We offer three versions of this protocol:
\begin{itemize}
\item @{text "ICING"}, which contains our best effort at modeling the protocol as accurately as 
possible.
\item @{text "ICING_variant"}, in which we strip down the protocol to what is required to obtain the
security guarantees and remove unnecessary fields.
\item @{text "ICING_variant2"}, in which we furthermore simplify the protocol. The key of the MAC in
this protocol is only the key of the AS, as opposed to a key derived specifically for this hop field.
In order to prove that this scheme is secure, we have to assume that ASes only occur once on an
authorized path, since otherwise the MAC for two different hop fields (by the same AS) would be the
same, and the AS could not distinguish the hop fields based on the MAC.
\end{itemize}\<close>
theory ICING
  imports
    "../Parametrized_Dataplane_3_undirected"
begin

locale icing_defs = network_assums_undirect _ _ _ auth_seg0 
  for auth_seg0 :: "(msgterm \<times> nat ahi_scheme list) set"
begin

(******************************************************************************)
subsection \<open>Hop validation check and extract functions\<close>
(******************************************************************************)
type_synonym ICING_HF = "(nat, unit) HF"

text\<open>The term @{term "sntag"} is a key that is derived from the key of an AS and a specific
hop field. We use it in the computation of @{term "hf_valid"}.
The "tag" field is a opaque numeric value which is used to encode further routing information of a
node.\<close>

fun sntag :: "nat ahi_scheme \<Rightarrow> msgterm" where
  "sntag \<lparr>UpIF = upif, DownIF = downif, ASID = asid, \<dots> = tag\<rparr> 
    = \<langle>macKey asid, if2term upif, if2term downif, Num tag\<rangle>"

lemma sntag_eq: "sntag ahi2 = sntag ahi1 \<Longrightarrow> ahi2 = ahi1"
  by(cases ahi1,cases ahi2) auto

(*redefined these functions in terms of a @{text "nat ahi_scheme"}*)
fun hf2term :: "nat ahi_scheme \<Rightarrow> msgterm" where
  "hf2term \<lparr>UpIF = upif, DownIF = downif, ASID = asid, \<dots> = tag\<rparr> 
  = L [if2term upif, if2term downif, Num asid, Num tag]"

fun term2hf :: "msgterm \<Rightarrow> nat ahi_scheme" where
  "term2hf (L [upif, downif, Num asid, Num tag]) 
  = \<lparr>UpIF = term2if upif, DownIF = term2if downif, ASID = asid, \<dots> = tag\<rparr>"

lemma term2hf_hf2term[simp]: "term2hf (hf2term hf) = hf" apply(cases hf) by auto

text\<open>We make some useful definitions that will be used to define the predicate @{term "hf_valid"}.
Having them as separate definitions is useful to prevent unfolding in proofs that don't require it.\<close>
definition fullpath :: "ICING_HF list \<Rightarrow> msgterm" where
  "fullpath hfs = L (map (hf2term o AHI) hfs)"

definition maccontents where
  "maccontents ahi hfs PoC_i_expire
  = \<langle>Mac[sntag ahi] \<langle>fullpath hfs, Num PoC_i_expire\<rangle>, \<langle>Num 0, Hash (fullpath hfs)\<rangle>\<rangle>"

text\<open>The predicate @{term "hf_valid"} is given to the concrete parametrized model as a parameter.
It ensures the authenticity of the hop authenticator in the hop field. The predicate takes an 
expiration timestamp (in this model always a numeric value, hence the matching on 
@{term "Num PoC_i_expire"}), the entire segment and the hop field to be validated.\<close>
fun hf_valid :: "msgterm \<Rightarrow> msgterm
    \<Rightarrow> ICING_HF list
    \<Rightarrow> ICING_HF 
    \<Rightarrow> bool" where 
  "hf_valid (Num PoC_i_expire) uinfo hfs \<lparr>AHI = ahi, UHI = uhi, HVF = A_i\<rparr> \<longleftrightarrow> 
    uhi = () \<and> uinfo = \<epsilon> \<and> A_i = Hash (maccontents ahi hfs PoC_i_expire)"
| "hf_valid _ _ _ _ = False"

text\<open>We can extract the entire path (past and future) from the hvf field.\<close>
fun extr :: "msgterm \<Rightarrow> nat ahi_scheme list" where
  "extr (Mac[Mac[_] \<langle>L fullpathhfs, Num PoC_i_expire\<rangle>] _)
 = map term2hf fullpathhfs"
| "extr _ = []"

text\<open>Extract the authenticated info field from a hop validation field.\<close>
fun extr_ainfo :: "msgterm \<Rightarrow> msgterm" where 
  "extr_ainfo (Mac[_] (L (Num ts # xs))) = Num ts"
| "extr_ainfo _ = \<epsilon>"

abbreviation term_ainfo :: "msgterm \<Rightarrow> msgterm" where
  "term_ainfo \<equiv> id"

text\<open>An authenticated info field is always a number (corresponding to a timestamp). The 
     unauthenticated info field is set to the empty term @{term "\<epsilon>"}.\<close>
definition auth_restrict where 
  "auth_restrict ainfo uinfo l \<equiv> (\<exists>ts. ainfo = Num ts) \<and> (uinfo = \<epsilon>)"

text\<open>When observing a hop field, an attacker learns the HVF. UHI is empty and the AHI only contains 
public information that are not terms.\<close>
fun terms_hf :: "ICING_HF \<Rightarrow> msgterm set" where 
  "terms_hf hf = {HVF hf}"

abbreviation terms_uinfo :: "msgterm \<Rightarrow> msgterm set" where 
  "terms_uinfo x \<equiv> {x}"

abbreviation no_oracle where "no_oracle \<equiv> (\<lambda> _ _. True)"

text\<open>We now define useful properties of the above definition.\<close>
lemma hf_valid_invert:
  "hf_valid tsn uinfo hfs hf \<longleftrightarrow>
(\<exists> PoC_i_expire ahi A_i . tsn = Num PoC_i_expire \<and> ahi = AHI hf \<and>
UHI hf = () \<and> uinfo = \<epsilon> \<and>
HVF hf = A_i \<and>
A_i = Hash (maccontents ahi hfs PoC_i_expire))"
  apply(cases hf) by(auto elim!: hf_valid.elims)

lemma hf_valid_auth_restrict[dest]: "hf_valid ainfo uinfo hfs hf \<Longrightarrow> auth_restrict ainfo uinfo l"
  by(auto simp add: hf_valid_invert auth_restrict_def)

lemma auth_restrict_ainfo[dest]: "auth_restrict ainfo uinfo l \<Longrightarrow> \<exists>ts. ainfo = Num ts"
  by(auto simp add: auth_restrict_def)
lemma auth_restrict_uinfo[dest]: "auth_restrict ainfo uinfo l \<Longrightarrow> uinfo = \<epsilon>"
  by(auto simp add: auth_restrict_def)

lemma info_hvf: 
  assumes "hf_valid ainfo uinfo hfs m" "hf_valid ainfo' uinfo' hfs' m'" 
          "HVF m = HVF m'" "m \<in> set hfs" "m' \<in> set hfs'"
  shows "ainfo' = ainfo" "m' = m"
  using assms
  apply(auto simp add: hf_valid_invert maccontents_def intro: ahi_eq)
  apply(cases m,cases m')
  by(auto intro: sntag_eq)


(******************************************************************************)
subsection\<open>Definitions and properties of the added intruder knowledge\<close>
(******************************************************************************)
text\<open>Here we define a @{text "ik_add"} and @{text "ik_oracle"} as being empty, as these features are
not used in this instance model.\<close>

print_locale dataplane_3_undirected_defs
sublocale dataplane_3_undirected_defs _ _ _ auth_seg0 hf_valid auth_restrict extr extr_ainfo 
  term_ainfo terms_hf terms_uinfo no_oracle
  by unfold_locales

declare parts_singleton[dest]

definition ik_add :: "msgterm set" where
  "ik_add \<equiv> { PoC | ainfo l uinfo hf PoC pkthash.  
                 (ainfo, l) \<in> auth_seg2 uinfo
                  \<and> hf \<in> set l \<and> HVF hf = Mac[PoC] pkthash }"

lemma ik_addI:
  "\<lbrakk>(ainfo, l) \<in> local.auth_seg2 uinfo; hf \<in> set l; HVF hf = Mac[PoC] pkthash\<rbrakk> \<Longrightarrow> PoC \<in> ik_add"
  by(auto simp add: ik_add_def)

lemma ik_add_form: 
  "t \<in> ik_add \<Longrightarrow> \<exists> asid upif downif tag l . t = Mac[\<langle>macKey asid, if2term upif, if2term downif, Num tag\<rangle>] l"
  apply(auto simp add: ik_add_def auth_seg2_def maccontents_def dest!: TW.holds_set_list)
  apply(auto simp add: hf_valid_invert maccontents_def auth_restrict_def)
    by (meson sntag.elims)

lemma elem_eq: "\<lbrakk>x \<in> xs; x = y; xs = ys\<rbrakk> \<Longrightarrow> y \<in> ys"
  by simp

lemma valid_hf_eq: 
"\<lbrakk>HVF hf = Mac[Mac[sntag (AHI hf)] \<langle>fullpath hfs, ainfo'\<rangle>] \<langle>Num 0, Hash (fullpath hfs)\<rangle>;
 HVF hf' = Mac[Mac[sntag (AHI hf)] \<langle>fullpath hfs, ainfo'\<rangle>] pkthash; 
(ainfo', l) \<in> auth_seg2 uinfo; hf' \<in> set l\<rbrakk>
  \<Longrightarrow> hf = hf'"
  by(auto simp add: auth_seg2_def hf_valid_invert maccontents_def auth_restrict_def dest!: sntag_eq)

lemma parts_ik_add[simp]: "parts ik_add = ik_add"
  by (auto intro!: parts_Hash dest: ik_add_form)

abbreviation ik_oracle :: "msgterm set" where "ik_oracle \<equiv> {}"

lemma uinfo_empty[dest]: "(ainfo, hfs) \<in> auth_seg2 uinfo \<Longrightarrow> uinfo = \<epsilon>"
  by(auto simp add: auth_seg2_def auth_restrict_def)

(******************************************************************************)
subsection\<open>Properties of the intruder knowledge, including @{text "ik_add"} and  @{text "ik_oracle"}\<close>
  (******************************************************************************)
text\<open>We now instantiate the parametrized model's definition of the intruder knowledge, using the
definitions of @{text "ik_add"} and  @{text "ik_oracle"} from above. We then prove the properties 
that we need to instantiate the @{text "dataplane_3_undirected"} locale.\<close>
print_locale dataplane_3_undirected_ik_defs
sublocale
  dataplane_3_undirected_ik_defs _ _ _ auth_seg0 terms_uinfo no_oracle hf_valid auth_restrict extr 
    extr_ainfo term_ainfo terms_hf ik_add ik_oracle
  by unfold_locales

lemma ik_hfs_form: "t \<in> parts ik_hfs \<Longrightarrow> \<exists> t' . t = Hash t'"
  apply auto apply(drule parts_singleton)
  by(auto simp add: auth_seg2_def hf_valid_invert)

declare ik_hfs_def[simp del]

lemma parts_ik_hfs[simp]: "parts ik_hfs = ik_hfs"
  by (auto intro!: parts_Hash ik_hfs_form)

text\<open>This lemma allows us not only to expand the definition of @{term "ik_hfs"}, but also 
to obtain useful properties, such as a term being a Hash, and it being part of a valid hop field.\<close>
lemma ik_hfs_simp: 
  "t \<in> ik_hfs \<longleftrightarrow> (\<exists>t' . t = Hash t') \<and> (\<exists>hf . t = HVF hf
                    \<and> (\<exists>hfs. hf \<in> set hfs \<and> (\<exists>ainfo uinfo. (ainfo, hfs) \<in> auth_seg2 uinfo
                    \<and> hf_valid ainfo uinfo hfs hf)))" (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  assume asm: "?lhs" 
  then obtain ainfo uinfo hf hfs where 
    dfs: "hf \<in> set hfs" "(ainfo, hfs) \<in> auth_seg2 uinfo" "t = HVF hf"
    by(auto simp add: ik_hfs_def)
  then obtain uinfo where "hfs_valid_prefix ainfo uinfo [] hfs = hfs"  "(ainfo, AHIS hfs) \<in> auth_seg0"
    by(auto simp add: auth_seg2_def)
  then show "?rhs" using asm dfs 
    by (auto 3 4 simp add: auth_seg2_def intro!: ik_hfs_form intro!: exI[of _ hf])+
qed(auto simp add: ik_hfs_def)


lemma ik_uinfo_empty[simp]: "ik_uinfo = {\<epsilon>}" 
  by(auto simp add: ik_uinfo_def auth_seg2_def auth_restrict_def intro!: exI[of _ "[]"])
declare ik_uinfo_def[simp del]

(******************************************************************************)
subsubsection \<open>Properties of Intruder Knowledge\<close>
(******************************************************************************)
lemma auth_ainfo[dest]: "\<lbrakk>(ainfo, hfs) \<in> auth_seg2 uinfo\<rbrakk> \<Longrightarrow> \<exists> ts . ainfo = Num ts"
  by(auto simp add: auth_seg2_def auth_restrict_def)

lemma Num_ik[intro]: "Num ts \<in> ik"
  by(auto simp add: ik_def auth_seg2_def auth_restrict_def intro!: exI[of _ "[]"])

text \<open>There are no ciphertexts (or signatures) in @{term "parts ik"}. Thus, @{term "analz ik"}
and @{term "parts ik"} are identical.\<close>
lemma analz_parts_ik[simp]: "analz ik = parts ik"
  apply(rule no_crypt_analz_is_parts)
  by(auto simp add: ik_def auth_seg2_def auth_restrict_def ik_hfs_simp dest: ik_add_form)

lemma parts_ik[simp]: "parts ik = ik"
  by(auto 3 4 simp add: ik_def auth_restrict_def auth_seg2_def dest!: parts_singleton_set)

lemma sntag_synth_bad: "sntag ahi \<in> synth ik \<Longrightarrow> ASID ahi \<in> bad"
  by(cases ahi)
    (auto simp add: ik_def ik_hfs_simp auth_restrict_def auth_seg2_def dest: ik_add_form)

lemma HF_eq:
  "\<lbrakk>AHI hf' = AHI hf; UHI hf' = UHI hf; HVF hf' = HVF hf\<rbrakk> \<Longrightarrow> hf' = (hf::('x, 'y)HF)"
  apply(cases hf', cases hf)
  by(auto elim: HF.cases)


(******************************************************************************)
subsection\<open>Direct proof goals for interpretation of @{text "dataplane_3_undirected"}\<close>
(******************************************************************************)

lemma COND_honest_hf_analz:
  assumes "ASID (AHI hf) \<notin> bad" "hf_valid ainfo uinfo hfs hf" "terms_hf hf \<subseteq> synth (analz ik)"
    "no_oracle ainfo uinfo" "hf \<in> set hfs"
    shows "terms_hf hf \<subseteq> analz ik"
proof-
  from assms(3) have hf_synth_ik: "HVF hf \<in> synth ik" by auto
  then have "\<exists>hfs uinfo. hf \<in> set hfs \<and> (ainfo, hfs) \<in> auth_seg2 uinfo"
    using assms(1,2,4,5) 
    apply(auto simp add: ik_def hf_valid_invert ik_hfs_simp)
    subgoal for PoC_i_expire hf' hfs' PoC_i_expire'
      by(auto intro!: exI[of _ hfs'] elim!: back_subst[where ?a=hf', where ?b=hf] 
              simp add: maccontents_def sntag_eq)
    subgoal by(auto simp add: ik_hfs_simp ik_def hf_valid_invert simp del: ik_uinfo_def)
    subgoal by(auto simp add: ik_hfs_simp ik_def hf_valid_invert maccontents_def 
               intro: sntag_synth_bad dest: ik_add_form)
    subgoal
      apply(auto simp add: ik_hfs_simp ik_def hf_valid_invert maccontents_def auth_restrict_def auth_seg2_def
               intro: sntag_synth_bad dest: ik_add_form simp del: ik_uinfo_def) (*takes ~ 10 sec*)
      subgoal by (simp add: fullpath_def)
      subgoal using fullpath_def ik_add_form by auto
        apply (auto simp add: ik_add_def)
        subgoal for ainfoa l uinfoa hf' pkthash
          apply(frule valid_hf_eq[where ?hf'="hf'"])
          by(auto dest: valid_hf_eq simp add: hf_valid_invert maccontents_def auth_seg2_def auth_restrict_def)
      done
    done
  then have "HVF hf \<in> ik"
    using assms(2)
    by(auto simp add: ik_hfs_def intro!: ik_ik_hfs intro!: exI) 
  then show ?thesis by auto
qed

lemma COND_terms_hf: 
  assumes "hf_valid ainfo uinfo hfs hf" and "HVF hf \<in> ik" and "no_oracle ainfo uinfo" and "hf \<in> set hfs"
  shows "\<exists>hfs. hf \<in> set hfs \<and> (\<exists>uinfo' . (ainfo, hfs) \<in> auth_seg2 uinfo')"
  using assms apply(auto 3 4 simp add: hf_valid_invert ik_hfs_simp ik_def dest: ahi_eq)
  using assms(1) assms(2) apply(auto simp add: maccontents_def) 
  apply(frule sntag_eq)
  apply(auto simp add: ik_def ik_hfs_simp dest: ik_add_form)
  by (metis info_hvf(1) info_hvf(2))

lemma COND_extr:
    "\<lbrakk>hf_valid ainfo uinfo l hf\<rbrakk> \<Longrightarrow> extr (HVF hf) = AHIS l"
  by(auto simp add: hf_valid_invert maccontents_def fullpath_def)

lemma COND_hf_valid_uinfo:
    "\<lbrakk>hf_valid ainfo uinfo l hf; hf_valid ainfo' uinfo' l' hf\<rbrakk> 
    \<Longrightarrow> uinfo' = uinfo"
  by(auto simp add: hf_valid_invert)

(******************************************************************************)
subsection\<open>Instantiation of @{text "dataplane_3_undirected"} locale\<close>
(******************************************************************************)
print_locale dataplane_3_undirected
sublocale
  dataplane_3_undirected _ _ _ auth_seg0 hf_valid auth_restrict extr extr_ainfo term_ainfo terms_uinfo ik_add terms_hf 
            ik_oracle  no_oracle
  apply unfold_locales
  using COND_terms_hf COND_honest_hf_analz COND_extr COND_hf_valid_uinfo by auto

end
end
