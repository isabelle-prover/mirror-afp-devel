(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory CompoundCTypesExNew
  imports AutoCorres2.CTranslation
begin


text \<open>
This illustrates the construction of a member of a C-type of class @{class xmem_contained_type} 
via the combinators for extended type info. Note that the instance proofs do not have to re-examine
the nested types of fields.
\<close>

setup \<open>
RecursiveRecordPackage.define_record_type
  [{record_name = "x_struct_ex",
    fields = [{fldname = "x_example", fldty = @{typ "32 word"}},
              {fldname = "y_example", fldty = @{typ "32 word[2]"}},
              {fldname = "z_example", fldty = @{typ "8 word"}}]
  }]
\<close>


definition x_struct_ex_tag :: "x_struct_ex xtyp_info" where
  "x_struct_ex_tag \<equiv> (
    final_pad 0 \<circ>
    (ti_typ_pad_combine TYPE(8 word) z_example (z_example_update \<circ> (\<lambda>x _. x)) 0 ''z_example'') \<circ>
    (ti_typ_pad_combine TYPE(32 word[2]) y_example (y_example_update \<circ> (\<lambda>x _. x)) 0 ''y_example'') \<circ>
    (ti_typ_pad_combine TYPE(32 word) x_example (x_example_update \<circ> (\<lambda>x _. x)) 0 ''x_example''))
    (empty_typ_info 0 ''x_struct_ex'')"




instantiation x_struct_ex :: c_type
begin
definition "typ_name_itself (x::x_struct_ex itself) = ''x_struct_ex''"
definition x_struct_ex_typ_tag: "typ_info_t (x::x_struct_ex itself) \<equiv> x_struct_ex_tag"

instance 
  by intro_classes
    (simp add: typ_name_itself_x_struct_ex_def x_struct_ex_typ_tag x_struct_ex_tag_def)
end

lemma aggregate_x_struct_ex_tag [simp]:
  "aggregate x_struct_ex_tag"
  by (simp add: x_struct_ex_tag_def final_pad_def Let_def)


lemma  y_xfield: "wf_xfield y_example (y_example_update \<circ> (\<lambda>x _. x))"
  by (wf_xfield_solver)

 
lemma  x_xfield: "wf_xfield x_example (x_example_update \<circ> (\<lambda>x _. x))"
  by (wf_xfield_solver)

lemma  z_xfield: "wf_xfield z_example (z_example_update \<circ> (\<lambda>x _. x))"
  by (wf_xfield_solver)

lemmas xfields =
  y_xfield x_xfield z_xfield


lemma size_arr: "(size_td (typ_info_t TYPE(32 word[2]))) = 8"
  by (simp add: typ_info_array array_tag_def) 

lemma align_arr: "align_td (typ_info_t TYPE(32 word[2])) = 2"
  by (simp add: typ_info_array array_tag_def array_tag_n_def  
   align_td_uinfo) 

instantiation x_struct_ex :: xmem_contained_type
begin
instance
  apply (rule tuned_xmem_contained_type_class_intro)
           apply(auto simp: x_struct_ex_typ_tag x_struct_ex_tag_def)
(* wf_desc *)
apply(fastforce intro: wf_desc_final_pad wf_desc_ti_typ_pad_combine)

(* wf_size_desc *)
apply(fastforce intro: wf_size_desc_ti_typ_pad_combine wf_size_desc_final_pad)

(* align_of dvd size_of *)
apply(simp add: align_of_def size_of_def x_struct_ex_typ_tag
                x_struct_ex_tag_def)

(* wf_align_field *)
  subgoal
    apply (simp add: wf_align_field_simps)
    done

(* max_size *)
  subgoal
   apply(simp add: size_of_def x_struct_ex_typ_tag x_struct_ex_tag_def
                size_td_lt_final_pad size_td_lt_ti_typ_pad_combine
                size_td_lt_ti_typ_combine size_td_lt_ti_pad_combine padup_def
                addr_card align_of_final_pad align_of_def size_arr align_arr )
    done

(* update_eq *)
       apply (simp add: field_update_simps align_arr size_arr)
      apply (wf_component_descs_solver)
     apply (component_descs_independent_solver)
    apply (wf_field_descs_solver)
   apply (contained_field_descs_solver)
  apply (simp add: wf_padding_combinator_simps wf_padding)
 done
end


setup \<open>
RecursiveRecordPackage.define_record_type
  [{record_name = "nested_ex",
    fields = [{fldname = "s_example", fldty = @{typ "x_struct_ex"}},
              {fldname = "n_example", fldty = @{typ "8 word"}}]
  }]
\<close>


definition nested_ex_tag :: "nested_ex xtyp_info" where
  "nested_ex_tag \<equiv> (
    final_pad 0 \<circ>
    (ti_typ_pad_combine TYPE(8 word) n_example (n_example_update \<circ> (\<lambda>x _. x)) 0 ''n_example'') \<circ>
    (ti_typ_pad_combine TYPE(x_struct_ex) s_example (s_example_update \<circ> (\<lambda>x _. x)) 0 ''s_example''))
    (empty_typ_info 0 ''nested_struct_ex'')"

instantiation nested_ex :: c_type
begin
definition "typ_name_itself (x::nested_ex itself) = ''nested_struct_ex''"
definition nested_ex_typ_tag: "typ_info_t (x::nested_ex itself) \<equiv> nested_ex_tag"

instance 
  by intro_classes
     (simp add: typ_name_itself_nested_ex_def nested_ex_typ_tag nested_ex_tag_def)
end

lemma align_x_struct_ex: "align_td (typ_info_t TYPE(x_struct_ex)) = 2"
  by (simp add: x_struct_ex_typ_tag x_struct_ex_tag_def align_of_final_pad align_arr)

lemma size_x_struct_ex: "(size_td (typ_info_t TYPE(x_struct_ex))) = 16"
  by (simp add: x_struct_ex_typ_tag x_struct_ex_tag_def align_arr field_update_simps size_arr)

lemmas nested_size_align = align_x_struct_ex size_x_struct_ex

instantiation nested_ex :: xmem_contained_type
begin
instance
  apply (rule tuned_xmem_contained_type_class_intro)
  apply(auto simp: nested_ex_typ_tag nested_ex_tag_def)
(* wf_desc *)
apply(fastforce intro: wf_desc_final_pad wf_desc_ti_typ_pad_combine)

(* wf_size_desc *)
apply(fastforce intro: wf_size_desc_ti_typ_pad_combine wf_size_desc_final_pad)

(* align_of dvd size_of *)
apply(simp add: align_of_def size_of_def nested_ex_typ_tag
                nested_ex_tag_def)

(* wf_align_field *)
  apply(simp add: wf_align_field_simps)

(* max_size *)
apply(simp add: size_of_def nested_ex_typ_tag nested_ex_tag_def
                size_td_lt_final_pad size_td_lt_ti_typ_pad_combine
                size_td_lt_ti_typ_combine size_td_lt_ti_pad_combine padup_def
                addr_card align_of_final_pad align_of_def size_arr align_arr nested_size_align)

(* update_eq *)
       apply (simp add: field_update_simps )
      apply (wf_component_descs_solver)
     apply (component_descs_independent_solver)
    apply (wf_field_descs_solver)
   apply (contained_field_descs_solver)
  apply (simp add: wf_padding_combinator_simps wf_padding)
  done
end


end
