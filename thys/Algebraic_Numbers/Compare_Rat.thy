(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
subsection \<open>Compare Instance for Rational Numbers\<close>

text \<open>TODO: This theory belongs into Derive-AFP entry.\<close>

theory Compare_Rat
imports
  "$AFP/Derive/Compare_Generator"
  Rat
begin
  
derive (linorder) compare_order rat

end