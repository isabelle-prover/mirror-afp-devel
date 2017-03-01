(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
theory Code_Abort_Gcd
imports   
  "~~/src/HOL/Library/Polynomial_Factorial"
begin

text \<open>Dummy code-setup for @{const Gcd} and @{const Lcm} in the presence of 
  Container.\<close>

definition "dummy_Gcd x = (Code.abort (STR ''Gcd on int'') (\<lambda> _. Gcd (x :: int set)))" 
definition "dummy_Lcm x = (Code.abort (STR ''Lcm on int'') (\<lambda> _. Lcm (x :: int set)))" 
lemma [code]: "Gcd = dummy_Gcd" unfolding dummy_Gcd_def by simp
lemma [code]: "Lcm = dummy_Lcm" unfolding dummy_Lcm_def by simp 

declare [[code abort: Euclidean_Algorithm.Gcd Euclidean_Algorithm.Lcm]]

end
