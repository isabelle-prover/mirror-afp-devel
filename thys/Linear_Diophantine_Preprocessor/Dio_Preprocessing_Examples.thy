section \<open>Examples\<close>

theory Dio_Preprocessing_Examples
  imports 
    Dio_Preprocessor
begin  


text \<open>Inequalities where branch-and-bound algorithm is not terminating without 
  setting global bounds\<close>
definition example_3_x_min_y :: "(int,var)lpoly list" where
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