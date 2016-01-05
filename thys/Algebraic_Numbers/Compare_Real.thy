subsection \<open>Compare Instance for Real Numbers\<close>

text \<open>TODO: This theory belongs into Derive-AFP entry.\<close>

theory Compare_Real
imports
  "$AFP/Derive/Compare_Generator"
  Real
begin
  
derive (linorder) compare_order real

end