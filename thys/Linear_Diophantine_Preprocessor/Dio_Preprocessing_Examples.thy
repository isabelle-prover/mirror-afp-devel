section \<open>Examples\<close>

theory Dio_Preprocessing_Examples
  imports 
    Dio_Preprocessor
begin  


text \<open>Encoding of an example task of \<^url>\<open>https://adventofcode.com/2025/day/10\<close>, part 2.
 
  The aim is to find the minimum value x0 for some satisfying assignment. 
  Here, the assignment needs to be over natural numbers, so we add constraints @{term "- xi \<le> 0"}.
  There are also implicit upper limits for each variable that are extracted from the equations.\<close>
definition aoc_2025_10_2 :: "var dleq list \<times> var dlineq list" where
  "aoc_2025_10_2 = (let xs = map var_l [0 ..< 11] in case xs of
     [x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10] \<Rightarrow>
     ([x1 + x4 + x5 + x6 + x8 - const_l 35,
       x3 + x4 + x5 + x7 - const_l 44,
       x1 + x2 + x3 + x5 + x6 + x7 + x8 + x10 - const_l 107,
       x2 + x3 + x4 + x5 + x8 + x9 + x10 - const_l 74,
       x4 + x6 + x10 - const_l 41,
       x3 + x4 + x5 + x6 + x8 - const_l 44,
       x1 + x4 + x7 - const_l 31,
       x1 + x3 + x4 + x5 + x6 + x7 + x9 - const_l 81,
       x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 - x0
      ], map (\<lambda> xi. - xi) (tl xs) @ 
        [ x1 - const_l 31, 
          x2 - const_l 74,
          x3 - const_l 44,
          x4 - const_l 31,
          x5 - const_l 35,
          x6 - const_l 35,
          x7 - const_l 31,
          x8 - const_l 35,
          x9 - const_l 74,
          x10 - const_l 74]))" 

text \<open>Preprocessing reduces the number of variables from 11 down to 2\<close>

lemma "case aoc_2025_10_2 of (eqs, ineqs) \<Rightarrow> case dio_preprocess eqs ineqs of
     Some (ineqs1, sol) \<Rightarrow> let alpha = (undefined(8 := a))(11 := b) 
      in (map (eval_l alpha) ineqs1, sol alpha 0)
  = (\<comment> \<open>new inequalities ... <= 0\<close>
    [- a - 2 * b - 17, 
     19 + 5 * a + 6 * b, 
     - a - 2 * b - 22, 
     3 + a + b, 
     1 + 2 * a + 3 * b,
     1 + a + 3 * b, 
     - a, 
     b - 3, 
     - 3 * a - 4 * b - 45, 
     2 + a + 2 * b, 
     - 5 * a - 6 * b - 93, 
     a + 2 * b,
     - a - b - 34, 
     - 2 * a - 3 * b - 36, 
     - a - 3 * b - 32, 
     a - 35, 
     - 71 - b, 
     3 * a + 4 * b - 29], 
   \<comment> \<open>new expression to be minimized\<close>
   107 - a - 2 * b)" 
  by normalization simp

text \<open>After preprocessing, a brute-force approach to determine the minimum value x0 = 114 is possible: 
  from @{term "- a \<le> (0 :: int)"} and @{term "a - 35 \<le> (0 :: int)"} we know @{term "(0 :: int) \<le> a \<and> a \<le> 35"},
  from @{term "-3 + b \<le> (0 :: int)"} and @{term "- 71 - b \<le> (0 :: int)"} we get @{term "-71 \<le> b \<and> b \<le> (3 :: int)"}.\<close>

lemma "114 = min_list [107 - a - 2 * b . a \<leftarrow> [0..35], b \<leftarrow> [-71 .. 3], 
     - a - 2 * b - 17 \<le> 0, 
     19 + 5 * a + 6 * b \<le> 0, 
     - a - 2 * b - 22 \<le> 0, 
     3 + a + b \<le> 0, 
     1 + 2 * a + 3 * b \<le> 0,
     1 + a + 3 * b \<le> 0, 
     - a \<le> 0, 
     b - 3 \<le> 0, 
     - 3 * a - 4 * b - 45 \<le> 0, 
     2 + a + 2 * b \<le> 0, 
     - 5 * a - 6 * b - 93 \<le> 0, 
     a + 2 * b \<le> 0,
     - a - b - 34 \<le> 0, 
     - 2 * a - 3 * b - 36 \<le> 0, 
     - a - 3 * b - 32 \<le> 0, 
     a - 35 \<le> 0, 
     - 71 - b \<le> 0, 
     3 * a + 4 * b - 29 \<le> 0]" 
  by eval


text \<open>Inequalities where branch-and-bound algorithm is not terminating without 
  setting global bounds\<close>
definition example_3_x_min_y :: "var dlineq list" where
  "example_3_x_min_y = (let x = var_l 1; y = var_l 2 in
     [const_l 1 - smult_l 3 x + smult_l 3 y,
      smult_l 3 x - smult_l 3 y - const_l 2])" 

text \<open>Preprocessing can detect unsat\<close>
lemma "case dio_preprocess [] example_3_x_min_y of None \<Rightarrow> True | Some _ \<Rightarrow> False" 
  by eval



text \<open>Griggio, example 1, unsat detection by preprocessing\<close>
definition griggio_example_1_eqs :: "var dleq list" where
  "griggio_example_1_eqs = (let x1 = var_l 1; x2 = var_l 2; x3 = var_l 3 in
      [smult_l 3 x1 + smult_l 3 x2 + smult_l 14 x3 - const_l 4,
      smult_l 7 x1 + smult_l 12 x2 + smult_l 31 x3 - const_l 17])" 

lemma "case dio_preprocess griggio_example_1_eqs [] of None \<Rightarrow> True | Some _ \<Rightarrow> False" 
  by eval

text \<open>Griggio, example 2, unsat detection by preprocessing\<close>
definition griggio_example_2_eqs :: "var dleq list" where
  "griggio_example_2_eqs = (let x1 = var_l 1; x2 = var_l 2; x3 = var_l 3; x4 = var_l 4 in
      [smult_l 2 x1 - smult_l 5 x3,
       x2 - smult_l 3 x4])" 

definition griggio_example_2_ineqs :: "(int,var) lpoly list" where
  "griggio_example_2_ineqs = (let x1 = var_l 1; x2 = var_l 2; x3 = var_l 3 in
      [- smult_l 2 x1 - x2 - x3 + const_l 7,
        smult_l 2 x1 + x2 + x3 - const_l 8])" 

lemma "case dio_preprocess griggio_example_2_eqs griggio_example_2_ineqs
       of None \<Rightarrow> True | Some _ \<Rightarrow> False" 
  by eval

text \<open>Termination proof of binary logarithm program \<open>n := 0; while (x > 1) {x := x div 2; n := n + 1}\<close>\<close>

definition example_log_transition_formula :: "(int,var) lpoly list"
  where "example_log_transition_formula = (let x = var_l 1; x' = var_l 2; n = var_l 3; n' = var_l 4
   in [const_l 1 - x,
      n' - n,
      n - n',
      smult_l 2 x' - x,
      x - smult_l 2 x' - const_l 1])" 

text \<open>\<open>x\<close> is decreasing in each iteration\<close>
value (code) "let x = var_l 1; x' = var_l 2 in dio_preprocess [] ((x - x') # example_log_transition_formula)" 

text \<open>\<open>x\<close> is bounded by -2\<close>
value (code) "let x = var_l 1 in dio_preprocess [] ((x + const_l 2) # example_log_transition_formula)"

end