(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze, Christoph Sprenger
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)

chapter\<open>Abstract, and Concrete Parametrized Models\<close>
text\<open>This is the core of our verification -- the abstract and parametrized models that cover a wide
range of protocols.\<close>
section\<open>Network model\<close>
theory Network_Model
  imports
    "infrastructure/Agents"
    "infrastructure/Tools"
    "infrastructure/Take_While"
begin

text\<open>@{term "as"} is already defined as a type synonym for nat.\<close>
type_synonym ifs = nat

text\<open>The authenticated hop information consists of the interface identifiers UpIF, DownIF and an
identifier of the AS to which the hop information belongs. Furthermore, this record is extensible 
and can include additional authenticated hop information (aahi).\<close>
record ahi = 
  UpIF :: "ifs option"
  DownIF :: "ifs option"
  ASID :: as

type_synonym 'aahi ahis = "'aahi ahi_scheme"

locale network_model = compromised + 
  fixes
   auth_seg0 :: "('ainfo \<times> 'aahi ahi_scheme list) set" 
   and tgtas :: "as \<Rightarrow> ifs \<Rightarrow> as option"
   and tgtif :: "as \<Rightarrow> ifs \<Rightarrow> ifs option"
begin

subsection \<open>Interface check\<close>
(******************************************************************************)

text \<open>Check if the interfaces of two adjacent hop fields match. If both hops are compromised we also
interpret the link as valid.\<close>
fun if_valid :: "'aahi ahis option \<Rightarrow> 'aahi ahis => 'aahi ahis option \<Rightarrow> bool" where
  "if_valid None hf _ \<comment> \<open>this is the case for the leaf AS\<close>
    = True"
| "if_valid (Some hf1) (hf2) _
    = ((\<exists>downif . DownIF hf2 = Some downif \<and> 
        tgtas (ASID hf2) downif = Some (ASID hf1) \<and>
        tgtif (ASID hf2) downif = UpIF hf1)
      \<or> ASID hf1 \<in> bad \<and> ASID hf2 \<in> bad)"

text \<open>makes sure that: the segment is terminated, i.e. the first AS's HF has Eo = None\<close>
fun terminated :: "'aahi ahis list \<Rightarrow> bool" where
  "terminated (hf#xs) \<longleftrightarrow> DownIF hf = None \<or> ASID hf \<in> bad"
| "terminated [] = True" (* we allow this as a special case*)

text \<open>makes sure that: the segment is rooted, i.e. the last HF has UpIF = None\<close>
fun rooted :: "'aahi ahis list \<Rightarrow> bool" where
  "rooted [hf] \<longleftrightarrow> UpIF hf = None \<or> ASID hf \<in> bad"
| "rooted (hf#xs) = rooted xs"
| "rooted [] = True" (* we allow this as a special case*)

abbreviation ifs_valid where 
  "ifs_valid pre l nxt \<equiv> TW.holds if_valid pre l nxt"

abbreviation ifs_valid_prefix where 
  "ifs_valid_prefix pre l nxt \<equiv> TW.takeW if_valid pre l nxt"

abbreviation ifs_valid_None where 
  "ifs_valid_None l \<equiv> ifs_valid None l None"

abbreviation ifs_valid_None_prefix where 
  "ifs_valid_None_prefix l \<equiv> ifs_valid_prefix None l None"

lemma strip_ifs_valid_prefix:
  "pfragment ainfo l auth_seg0 \<Longrightarrow> pfragment ainfo (ifs_valid_prefix pre l nxt) auth_seg0"
  by (auto elim: pfragment_prefix' intro: TW.takeW_prefix)


text\<open>Given the AS and an interface identifier of a channel, obtain the AS and interface at the other
end of the same channel.\<close>
abbreviation rev_link :: "as \<Rightarrow> ifs \<Rightarrow> as option \<times> ifs option" where 
  "rev_link a1 i1 \<equiv> (tgtas a1 i1, tgtif a1 i1)"

end
end
