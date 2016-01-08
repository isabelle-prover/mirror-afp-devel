(*  
    Author:      René Thiemann 
    License:     LGPL
*)
subsection \<open>Compare Instance for Rational Numbers\<close>

theory Compare_Rat
imports
  Compare_Generator
  Rat
begin
  
derive (linorder) compare_order rat

end