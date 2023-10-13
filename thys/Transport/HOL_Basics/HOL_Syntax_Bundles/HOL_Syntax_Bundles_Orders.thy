\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Order Syntax\<close>
theory HOL_Syntax_Bundles_Orders
  imports HOL.Orderings
begin

bundle HOL_order_syntax
begin
notation
  less_eq  ("'(\<le>')") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50) and
  less  ("'(<')") and
  less  ("(_/ < _)"  [51, 51] 50)
notation (input) greater_eq (infix "\<ge>" 50)
notation (input) greater (infix ">" 50)
notation (ASCII)
  less_eq  ("'(<=')") and
  less_eq  ("(_/ <= _)" [51, 51] 50)
notation (input) greater_eq (infix ">=" 50)
end
bundle no_HOL_order_syntax
begin
no_notation
  less_eq  ("'(\<le>')") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50) and
  less  ("'(<')") and
  less  ("(_/ < _)"  [51, 51] 50)
no_notation (input) greater_eq (infix "\<ge>" 50)
no_notation (input) greater (infix ">" 50)
no_notation (ASCII)
  less_eq  ("'(<=')") and
  less_eq  ("(_/ <= _)" [51, 51] 50)
no_notation (input) greater_eq (infix ">=" 50)
end


end