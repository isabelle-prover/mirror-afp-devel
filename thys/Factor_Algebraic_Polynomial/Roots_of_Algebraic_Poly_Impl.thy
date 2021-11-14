subsection \<open>Executable Version to Compute Representative Polynomials\<close>

theory Roots_of_Algebraic_Poly_Impl
imports 
  Roots_of_Algebraic_Poly
  Polynomials.MPoly_Type_Class_FMap
begin

text \<open>We need to specialize our code to real and complex polynomials, 
  since @{const algebraic} and @{const min_int_poly} are
  not executable in their parametric versions.\<close>

definition initial_root_problem_real :: "real poly \<Rightarrow> _" where
  [simp]: "initial_root_problem_real p = initial_root_problem p" 

definition initial_root_problem_complex :: "complex poly \<Rightarrow> _" where
  [simp]: "initial_root_problem_complex p = initial_root_problem p" 

lemmas initial_root_problem_code = 
  initial_root_problem_real_def[unfolded initial_root_problem_def]
  initial_root_problem_complex_def[unfolded initial_root_problem_def]

declare initial_root_problem_code[code]

lemma initial_root_problem_code_unfold[code_unfold]: 
  "initial_root_problem = initial_root_problem_complex" 
  "initial_root_problem = initial_root_problem_real" 
  by (intro ext, simp)+

definition representative_poly_real :: "real poly \<Rightarrow> _" where
  [simp]: "representative_poly_real p = representative_poly p" 

definition representative_poly_complex :: "complex poly \<Rightarrow> _" where
  [simp]: "representative_poly_complex p = representative_poly p" 

lemmas representative_poly_code = 
  representative_poly_real_def[unfolded representative_poly_def]
  representative_poly_complex_def[unfolded representative_poly_def]

declare representative_poly_code[code]

lemma representative_poly_code_unfold[code_unfold]: 
  "representative_poly = representative_poly_complex" 
  "representative_poly = representative_poly_real" 
  by (intro ext, simp)+
 
end