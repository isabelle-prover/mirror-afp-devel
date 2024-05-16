(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory aligned
  imports AutoCorres2.CTranslation
begin

install_C_file "aligned.c"

(* On a 64 Bit MacOS:

gcc -D GCC=1 aligned.c

alignof int: 4
sizeof int: 4

alignof my_struct0: 4
sizeof my_struct0: 8
offsetof (my_struct0, next): 4

alignof my_struct1: 64
sizeof my_struct1: 64
offsetof (my_struct1, next): 4

alignof my_struct2: 32
sizeof my_struct2: 32
offsetof (my_struct2, next): 4

alignof my_struct3: 32
sizeof my_struct3: 64
offsetof (my_struct3, next): 32

alignof my_struct4: 64
sizeof my_struct4: 64
offsetof (my_struct4, next): 4
*)

definition "align_int = align_of (TYPE(32 sword))" 
definition "size_int = size_of (TYPE(32 sword))" 

lemmas align_int_def[simp]  size_int_def[simp]

thm my_struct0_C_tag_def
lemma "align_of (TYPE(my_struct0_C)) = align_int"
  by simp
lemma "size_of (TYPE(my_struct0_C))  = 2 * size_int"
  by simp
text \<open>Offset of field "next" with structure:\<close>
lemma "snd (the (field_lookup (typ_info_t TYPE(my_struct0_C)) [''next_C''] 0)) = size_int"
  by (simp add: fl_Some_simps field_offset_def field_offset_untyped_def)


thm my_struct1_C_tag_def
lemma "align_of (TYPE(my_struct1_C)) = 64"
  by simp
lemma "size_of (TYPE(my_struct1_C)) = 64"
  by simp
text \<open>Offset of field "next" with structure:\<close>
lemma "snd (the (field_lookup (typ_info_t TYPE(my_struct1_C)) [''next_C''] 0)) = size_int"
  by (simp add: fl_Some_simps field_offset_def field_offset_untyped_def)

thm my_struct2_C_tag_def
lemma "align_of (TYPE(my_struct2_C)) = 32"
  by simp
lemma "size_of (TYPE(my_struct2_C)) = 32"
  by simp
text \<open>Offset of field "next" with structure:\<close>
lemma "snd (the (field_lookup (typ_info_t TYPE(my_struct2_C)) [''next_C''] 0)) = size_int"
  by (simp add: fl_Some_simps field_offset_def field_offset_untyped_def)

thm my_struct3_C_tag_def
lemma "align_of (TYPE(my_struct3_C)) = 32"
  by simp
lemma "size_of (TYPE(my_struct3_C)) = 64"
  by simp
lemma "snd (the (field_lookup (typ_info_t TYPE(my_struct3_C)) [''next_C''] 0)) = 32"
  by (simp add: fl_Some_simps field_offset_def field_offset_untyped_def)


thm my_struct4_C_tag_def
lemma "align_of (TYPE(my_struct4_C)) = 64"
  by simp
lemma "size_of (TYPE(my_struct4_C)) = 64"
  by simp
lemma "snd (the (field_lookup (typ_info_t TYPE(my_struct4_C)) [''next_C''] 0)) = size_int"
  by (simp add: fl_Some_simps field_offset_def field_offset_untyped_def)

term test_bit
context aligned_simpl
begin
thm foo_body_def
end

end
