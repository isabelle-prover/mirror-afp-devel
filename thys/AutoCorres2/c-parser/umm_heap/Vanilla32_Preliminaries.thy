(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* License: BSD, terms see file ./LICENSE *)

theory Vanilla32_Preliminaries
imports CTypes
begin

section "Words and Pointers"

instantiation unit :: c_type
begin
definition [simp]: "typ_name_itself (x::unit itself) = ''unit''"
definition typ_info_unit[simp]:
  "typ_info_t (x::unit itself) \<equiv> 
  TypDesc 0 (TypScalar 1 0
            (\<lparr>field_access = (\<lambda>v bs. [0]), field_update = (\<lambda>bs v. ()), field_sz = 1\<rparr>)) 
          ''unit'' 
           :: unit xtyp_info"
instance by intro_classes (simp add: typ_name_itself_unit_def)
end

lemma typ_name_unit[simp]: 
  "typ_name (typ_info_t (TYPE(unit))) = ''unit''"
  "typ_name (typ_uinfo_t TYPE(unit)) = ''unit''"
  by (simp_all add: typ_uinfo_t_def)

instantiation unit :: mem_type
begin
  definition
    to_bytes_unit :: "unit \<Rightarrow> byte list" where
    "to_bytes_unit a \<equiv> [0]"

  definition
    from_bytes_unit :: "byte list \<Rightarrow> unit" where
    "from_bytes_unit bs \<equiv> ()"

  definition
    size_of_unit :: "unit itself \<Rightarrow> nat" where
    "size_of_unit x \<equiv> 0"

  definition
    align_of_unit :: "unit itself \<Rightarrow> nat" where
    "align_of_unit x \<equiv> 1"

  instance
    apply intro_classes
    apply (auto simp: size_of_def align_of_def align_field_def addr_card
                      wf_lf_def fd_cons_desc_def
                      fd_cons_double_update_def fd_cons_update_access_def
                      fd_cons_access_update_def fd_cons_length_def)
  done
end

definition
  "bogus_log2lessthree (n::nat) ==
             if n = 128 then 4
             else if n = 64 then (3::nat)
             else if n = 32 then 2
             else if n = 16 then 1
             else if n = 8 then 0
             else undefined"
definition
  "len_exp (x::('a::len) itself) \<equiv> bogus_log2lessthree (len_of TYPE('a))"

lemma lx8' [simp] : "len_exp (x::8 itself) = 0"
by (simp add: len_exp_def bogus_log2lessthree_def)

lemma lx16' [simp]: "len_exp (x::16 itself) = 1"
by (simp add: len_exp_def bogus_log2lessthree_def)

lemma lx32' [simp]: "len_exp (x::32 itself) = 2"
by (simp add: len_exp_def bogus_log2lessthree_def)

lemma lx64' [simp]: "len_exp (x::64 itself) = 3"
by (simp add: len_exp_def bogus_log2lessthree_def)

lemma lx_signed' [simp]: "len_exp (x::('a::len) signed itself) = len_exp (TYPE('a))"
  by (simp add: len_exp_def)

class len8 = len +
  (* this constraint gives us (in the most convoluted way possible) that we're only
     interested in words with a length that is divisible by 8 *)
  assumes len8_bytes: "len_of TYPE('a::len) = 8 * (2^len_exp TYPE('a))"
  (* len8_len class gives us that the words are \<le> than 128 bits.
     This is a wacky restriction really, but we're really only interested in words
     up to 64 bits, so who cares. *)
  assumes len8_width: "len_of TYPE('a::len) \<le> 128"
begin

lemma len8_size:
  "len_of TYPE('a) div 8 < addr_card"
  apply(subgoal_tac "len_of TYPE('a) \<le> 128")
   apply(simp add: addr_card)
  apply(rule len8_width)
  done

lemma len8_dv8:
  "8 dvd len_of TYPE('a)"
  by (simp add: len8_bytes)

lemma len8_pow:
  "\<exists>k. len_of TYPE('a) div 8 = 2^k"
  by (simp add: len8_bytes)

end

fun
  nat_to_bin_string :: "nat \<Rightarrow> char list"
  where
  ntbs: "nat_to_bin_string n = (if (n = 0) then ''0'' else (if n mod 2 = 1 then CHR ''1'' else CHR ''0'') # nat_to_bin_string (n div 2))"

declare nat_to_bin_string.simps [simp del]

lemma nat_to_bin_string_simps:
  "nat_to_bin_string 0 = ''0''"
  "n > 0 \<Longrightarrow> nat_to_bin_string n =
      (if n mod 2 = 1 then CHR ''1'' else CHR ''0'') # nat_to_bin_string (n div 2)"
  apply (induct n, auto simp: nat_to_bin_string.simps)
  done

instance signed :: (len8) len8
  apply intro_classes
   apply (metis len8_bytes len_exp_def len_signed)
  apply (metis len8_width len_signed)
  done

end
