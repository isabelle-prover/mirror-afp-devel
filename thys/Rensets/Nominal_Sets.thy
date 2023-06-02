section \<open>Nominal sets \<close>

theory Nominal_Sets 
imports Lambda_Terms
begin

text \<open> This theory introduces pre-nominal sets, and then nominal sets as pre-nominal 
sets of finite support.  
\<close>

locale Pre_Nominal_Set = 
fixes swapA :: "'A \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'A"
assumes 
swapA_id: "\<And>a x. swapA a x x = a"
and 
swapA_invol: "\<And>a x y. swapA (swapA a x y) x y = a"
and 
swapA_cmp: 
"\<And>x y a z1 z2. swapA (swapA a x y) z1 z2 = 
  swapA (swapA a z1 z2) (sw x z1 z2) (sw y z1 z2)"
begin

(* freshness: *)
definition freshA where "freshA x a \<equiv> finite {y. swapA a y x \<noteq> a}"

end (* context Pre_Nominal_Set *)


locale Nominal_Set = Pre_Nominal_Set swapA 
for swapA :: "'A \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'A" 
+
assumes cofinite_freshA: "\<And>a. finite {x. \<not> freshA x a}"


locale Nominal_Morphism = 
A: Nominal_Set swapA + B: Nominal_Set swapB
for swapA :: "'A \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'A" and swapB :: "'B \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'B"
+
fixes f :: "'A \<Rightarrow> 'B"
assumes f_swapA_swapB: "\<And>a z1 z2. f (swapA a z1 z2) = swapB (f a) z1 z2"


end