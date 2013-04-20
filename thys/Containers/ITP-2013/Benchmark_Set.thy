theory Benchmark_Set
imports
  "~~/src/HOL/Word/Word"
  "~~/src/HOL/Libary/Cardinality"
begin

instantiation word :: (len) card_UNIV begin
definition "finite_UNIV = Phantom('a word) True"
definition "card_UNIV = Phantom('a word) (2 ^ len_of TYPE('a))"
instance by(intro_classes)(simp_all add: card_UNIV_word_def card_word finite_UNIV_word_def)
end

definition word_of :: "code_numeral \<Rightarrow> 'a::len0 word"
where "word_of = word_of_int o Code_Numeral.int_of"

lemma word_of_code [code]:
  "word_of k = (if k = 0 then 0
    else (if k mod 2 = 0 then 2 * word_of (k div 2) else 2 * word_of (k div 2) + 1))"
apply(unfold word_of_def o_def)
apply(subst Code_Numeral.int_of_code)
apply(clarsimp)
apply(metis wi_hom_mult one_word.abs_eq plus_word.abs_eq times_word.abs_eq word_of_int_numeral)
done

text {* randomly generate a set of (up to) n elements drawn from 0 to bound *}

fun gen_build1 :: "code_numeral \<Rightarrow> nat \<Rightarrow> (32 word set \<times> Random.seed) \<Rightarrow> (32 word set \<times> Random.seed)"
where 
  "gen_build1 bound n (A, seed) =
  (if n = 0 then (A, seed) 
   else let (x, seed') = Random.range bound seed in gen_build1 bound (n - 1) (insert (word_of x) A, seed'))"

declare gen_build1.simps[simp del]

definition build1 :: "code_numeral \<Rightarrow> Random.seed \<Rightarrow> (32 word set \<times> Random.seed)"
where 
  "build1 bound seed =
  (let (n', seed') = Random.range bound seed;
       (compl, seed'') = Random.range 2 seed;
       (x, seed''') = gen_build1 bound (Code_Numeral.nat_of n') ({}, seed'')
   in (if compl = 0 then x else - x, seed'''))"

text {* randomly generate a set of (up to) n sets each with a random number between 0 and bound of elements between 0 and bound *}

fun gen_build2 :: "code_numeral \<Rightarrow> nat \<Rightarrow> (32 word set set \<times> Random.seed) \<Rightarrow> (32 word set set \<times> Random.seed)"
where
  "gen_build2 bound n (A, seed) =
  (if n = 0 then (A, seed)
   else let (x, seed') = build1 bound seed
        in gen_build2 bound (n - 1) (insert x A, seed'))"

declare gen_build2.simps[simp del]

definition build :: "nat \<Rightarrow> nat \<Rightarrow> Random.seed \<Rightarrow> 32 word set set \<times> Random.seed"
where "build n m seed = gen_build2 (of_nat m) n ({}, seed)"

fun gen_lookup :: "32 word set set \<Rightarrow> code_numeral \<Rightarrow> nat \<Rightarrow> (nat \<times> Random.seed) \<Rightarrow> (nat \<times> Random.seed)"
where
  "gen_lookup A bound n (hits, seed) =
  (if n = 0 then (hits, seed)
   else let (x, seed') = build1 bound seed
        in gen_lookup A bound (n - 1) (if x : A then hits + 1 else hits, seed'))"

declare gen_lookup.simps [simp del]

primrec lookup :: "nat \<Rightarrow> nat \<Rightarrow> (32 word set set \<times> Random.seed) \<Rightarrow> (nat \<times> Random.seed)"
where "lookup n m (A, seed) = gen_lookup A (of_nat m) 100 (0, seed)"

definition covered :: "32 word set set \<Rightarrow> nat"
where "covered A = card (\<Union>A)"

definition complete :: "nat \<Rightarrow> nat \<Rightarrow> Random.seed \<Rightarrow> (nat \<times> nat)"
where "complete n m seed = (let (A, seed') = build n m seed in (fst (lookup n m (A, seed)), covered A))"

end