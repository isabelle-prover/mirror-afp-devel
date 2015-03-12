theory Compare_Generator
imports 
  Comparator_Generator
  Compare
begin

named_theorems compare_simps "simp theorems to derive \"compare = comparator_of\""

ML_file "compare_generator.ML"

end

