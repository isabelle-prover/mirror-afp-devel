(*  Title:      JinjaThreads/J/JHeap.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Abstract heap locales for source code programs} *}

theory JHeap imports
  "../Common/Conform"
  "Expr"
begin

locale J_heap_base = heap_base +
  constrains empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool"

locale J_heap = heap + 
  constrains empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool"

sublocale J_heap < J_heap_base .

locale J_heap_conf_base = heap_conf_base +
  constrains empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P :: "J_prog"

sublocale J_heap_conf_base < J_heap_base .

locale J_heap_conf = 
  J_heap_conf_base +
  heap_conf +
  constrains empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P :: "J_prog"

locale J_progress =
  heap_progress +
  J_heap_conf_base +
  constrains empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P :: "J_prog"

sublocale J_progress < J_heap by(unfold_locales) 

locale J_conf_read =
  heap_conf_read +
  J_heap_conf +
  constrains empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P :: "J_prog"

sublocale J_conf_read < J_heap by(unfold_locales)

locale J_typesafe =
  heap_typesafe +
  J_conf_read +
  J_progress +
  constrains empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> addr option)"
  and typeof_addr :: "'heap \<Rightarrow> addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> addr \<Rightarrow> addr_loc \<Rightarrow> val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and P :: "J_prog"

end