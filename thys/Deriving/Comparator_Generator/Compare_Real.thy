(*
    Author:      René Thiemann
    License:     LGPL
*)
subsection \<open>Compare Instance for Real Numbers\<close>

theory Compare_Real
imports
  Compare_Generator
  Real
begin
  
derive (linorder) compare_order real

end
