subsection \<open>Compare Generator\<close>

theory Compare_Generator
imports 
  Comparator_Generator
  Compare
begin

text \<open>We provide a generator which takes the comparators of the comparator generator
  to synthesize suitable @{const compare}-functions from the @{class compare}-class.

One can further also use these comparison functions to derive an instance of the
@{class compare_order}-class, and therefore also for @{class linorder}.\<close>

lemma linorder_axiomsD: assumes "class.linorder le lt"
  shows 
  "lt x y = (le x y \<and> \<not> le y x)" (is ?a)
  "le x x" (is ?b)
  "le x y \<Longrightarrow> le y z \<Longrightarrow> le x z" (is "?c1 \<Longrightarrow> ?c2 \<Longrightarrow> ?c3") 
  "le x y \<Longrightarrow> le y x \<Longrightarrow> x = y" (is "?d1 \<Longrightarrow> ?d2 \<Longrightarrow> ?d3")
  "le x y \<or> le y x" (is ?e)
proof -
  interpret linorder le lt by fact
  show ?a ?b "?c1 \<Longrightarrow> ?c2 \<Longrightarrow> ?c3" "?d1 \<Longrightarrow> ?d2 \<Longrightarrow> ?d3" ?e by auto
qed
 
named_theorems compare_simps "simp theorems to derive \"compare = comparator_of\""

ML_file "compare_generator.ML"

end