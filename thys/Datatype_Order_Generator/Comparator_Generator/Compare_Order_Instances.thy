subsection \<open>Defining Compare-Order-Instances for Common Types\<close>

theory Compare_Order_Instances
imports
  Compare_Instances
begin

text \<open>For all of the following types, we now also instantiate class @{class linorder} via
  the comparators.:
  @{type sum}, @{type option}, @{type list},
  and @{type prod}.\<close>

derive compare_order sum list prod option

end