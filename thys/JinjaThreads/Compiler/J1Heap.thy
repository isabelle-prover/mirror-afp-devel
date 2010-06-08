(*  Title:      JinjaThreads/Compiler/J1Heap.hty
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Abstract heap locales for J1 programs} *}

theory J1Heap imports
  "J1State"
  "../Common/Conform"
begin

locale J1_heap_base = heap_base +
  constrains empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool"

locale J1_heap = heap + 
  constrains empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool"

sublocale J1_heap < J1_heap_base .

locale J1_heap_conf_base = heap_conf_base +
  constrains empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P :: "J1_prog"

sublocale J1_heap_conf_base < J1_heap_base .

locale J1_heap_conf = 
  J1_heap_conf_base +
  heap_conf +
  constrains empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P1 :: "J_prog"

sublocale J1_heap_conf < J1_heap by(unfold_locales)

locale J1_conf_read =
  J1_heap_conf +
  heap_conf_read +
  constrains empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P1 :: "J_prog"

end

