theory Divmod_Nat
imports Main
begin

text \<open>We explicitly provide a version simultaneous division and mod-computation  
  for efficiency reasons.\<close>
  
definition divmod_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  [simp]: "divmod_nat n m = (n div m, n mod m)"

lemma divmod_nat_code[code]: "divmod_nat n m = TODO" oops

end