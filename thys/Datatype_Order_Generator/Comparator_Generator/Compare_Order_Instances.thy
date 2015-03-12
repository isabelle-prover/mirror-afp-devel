theory Compare_Order_Instances
imports
  Compare_Instances
begin

section \<open>Defining comparators and orders for standard types\<close>

text \<open>For all of the following types, we now also instantiate class @{class linorder} via
  the comparators.:
  @{type sum}, @{type option}, @{type list},
  and @{type prod}.\<close>

derive compare_order sum list prod option

end