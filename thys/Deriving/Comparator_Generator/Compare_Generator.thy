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


named_theorems compare_simps "simp theorems to derive \"compare = comparator_of\""

ML_file "compare_generator.ML"

end