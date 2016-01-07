(*  
    Author:      René Thiemann 
    License:     LGPL
*)
section \<open>Show Implemetation for Real Numbers via Rational Numbers\<close>

text \<open>We just provide an implementation for show of real numbers where we assume
  that real numbers are implemented via rational numbers.\<close>
  
theory Show_Real_Impl
imports 
  Show_Real
  Show_Instances
begin

text \<open>We now define @{const show_real}.\<close>
defs show_real: "show_real x \<equiv> (if (\<exists> y. x = Ratreal y) then show (THE y. x = Ratreal y) else ''Irrational'')"

lemma show_real_code[code]: "show_real (Ratreal x) = show x"
  unfolding show_real by auto
end