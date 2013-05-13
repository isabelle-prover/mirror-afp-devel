theory Benchmark_Set_Default 
imports
  Benchmark_Set
  "~~/src/HOL/Library/Code_Target_Nat"
begin

text {* Implement set equality for all combinations of @{term "List.set"} and @{term "List.coset"} *}
lemma [code]: "equal_class.equal A B \<longleftrightarrow> Cardinality.eq_set A B" 
 by(simp add: equal_eq)

ML_val {*
  val seed = (Code_Numeral.natural_of_integer 12345, Code_Numeral.natural_of_integer 67889);
  val n = @{code nat_of_integer} 30;
  val m = @{code nat_of_integer} 40;
  val c = @{code complete} n m seed;
*}

notepad begin
  have "complete 30 40 (12345, 67889) = (30, 4294967296)" by eval
end

end
