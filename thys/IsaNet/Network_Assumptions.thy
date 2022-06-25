(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze, Christoph Sprenger
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)

section\<open>Network Assumptions used for authorized segments.\<close>
theory Network_Assumptions
  imports
    "Network_Model"
begin

locale network_assums_generic = network_model _ auth_seg0 for
   auth_seg0 :: "('ainfo \<times> 'aahi ahi_scheme list) set" +
 assumes
\<comment> \<open>All authorized segments have valid interfaces\<close>
    ASM_if_valid: "(info, l) \<in> auth_seg0 \<Longrightarrow> ifs_valid_None l" and
\<comment> \<open>All authorized segments are rooted, i.e., they start with None\<close>
    ASM_empty [simp, intro!]: "(info, []) \<in> auth_seg0" and
    ASM_rooted: "(info, l) \<in> auth_seg0 \<Longrightarrow> rooted l" and
    ASM_terminated: "(info, l) \<in> auth_seg0 \<Longrightarrow> terminated l"

locale network_assums_undirect = network_assums_generic _ _ +
  assumes
    ASM_adversary: "\<lbrakk>\<And>hf. hf \<in> set hfs \<Longrightarrow> ASID hf \<in> bad\<rbrakk> \<Longrightarrow> (info, hfs) \<in> auth_seg0"

locale network_assums_direct = network_assums_generic _ _ +
  assumes
    ASM_singleton: "\<lbrakk>ASID hf \<in> bad\<rbrakk> \<Longrightarrow> (info, [hf]) \<in> auth_seg0" and
    ASM_extension: "\<lbrakk>(info, hf2#ys) \<in> auth_seg0; ASID hf2 \<in> bad; ASID hf1 \<in> bad\<rbrakk>
                    \<Longrightarrow> (info, hf1#hf2#ys) \<in> auth_seg0" and
    ASM_modify: "\<lbrakk>(info, hf#ys) \<in> auth_seg0; ASID hf = a; ASID hf' = a; UpIF hf' = UpIF hf; a \<in> bad\<rbrakk> 
                  \<Longrightarrow> (info, hf'#ys) \<in> auth_seg0" and
    ASM_cutoff: "\<lbrakk>(info, zs@hf#ys) \<in> auth_seg0; ASID hf = a; a \<in> bad\<rbrakk> \<Longrightarrow> (info, hf#ys) \<in> auth_seg0"
begin

lemma auth_seg0_non_empty [simp, intro!]: "auth_seg0 \<noteq> {}"
  by auto

lemma auth_seg0_non_empty_frag [simp, intro!]: "\<exists> info . pfragment info [] auth_seg0"
  apply(auto simp add: pfragment_def)
  by (metis append_Nil2 ASM_empty)

text \<open>This lemma applies the extendability assumptions on @{text "auth_seg0"} to pfragments of 
@{text "auth_seg0"}.\<close>
lemma extend_pfragment0:
  assumes "pfragment ainfo (hf2#xs) auth_seg0"
  assumes "ASID hf1 \<in> bad"
  assumes "ASID hf2 \<in> bad"
  shows "pfragment ainfo (hf1#hf2#xs) auth_seg0"
  using assms
  by(auto intro!: pfragmentI[of _ "[]" _ _] elim!: pfragmentE intro: ASM_cutoff intro!: ASM_extension)

text\<open>This lemma shows that the above assumptions imply that of the undirected setting\<close>
lemma "\<lbrakk>\<And>hf. hf \<in> set hfs \<Longrightarrow> ASID hf \<in> bad\<rbrakk> \<Longrightarrow> (info, hfs) \<in> auth_seg0"
  apply(induction hfs)
  using ASM_empty apply blast
  subgoal for a hfs
    apply(cases hfs)
    by(auto intro!: ASM_singleton ASM_extension)
  done

end
end
