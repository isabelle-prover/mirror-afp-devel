subsection \<open>Compare\<close>

theory Compare
imports Comparator
keywords "compare_code" :: thy_decl
begin

text \<open>This introduces a type class for having a proper comparator, similar to @{class linorder}.
  Since most of the Isabelle/HOL algorithms work on the latter, we also provide a method which 
  turns linear-order based algorithms into comparator-based algorithms, where two consecutive 
  invocations of linear orders and equality are merged into one comparator invocation.
  We further define a class which both define a linear order and a comparator, and where the
  induces orders coincide.\<close>

class compare =
  fixes compare :: "'a comparator"
  assumes comparator_compare: "comparator compare"
begin

lemma compare_Eq_is_eq [simp]:
  "compare x y = Eq \<longleftrightarrow> x = y"
  by (rule comparator.eq [OF comparator_compare])
  
lemma compare_refl [simp]:
  "compare x x = Eq"
  by simp

end

lemma (in linorder) le_lt_comparator_of:
  "le_of_comp comparator_of = op \<le>" "lt_of_comp comparator_of = op <"
  by (intro ext, auto simp: comparator_of_def le_of_comp_def lt_of_comp_def)+

class compare_order = ord + compare +
  assumes ord_defs: "le_of_comp compare = op \<le> " "lt_of_comp compare = op <"

text \<open> @{class compare_order} is @{class compare} and @{class linorder}, where comparator and orders 
  define the same ordering.\<close>

subclass (in compare_order) linorder
  by (unfold ord_defs[symmetric], rule comparator.linorder, rule comparator_compare)

context compare_order
begin

lemma compare_is_comparator_of: 
  "compare = comparator_of" 
proof (intro ext)
  fix x y :: 'a
  show "compare x y = comparator_of x y"
    by  (unfold comparator_of_def, unfold ord_defs[symmetric] lt_of_comp_def, 
      cases "compare x y", auto)
qed

lemma two_comparisons_into_compare: 
  "(if x \<le> y then (if x = y then P else Q) else R) = (case_order P Q R (compare x y))" 
  "(if x \<le> y then (if y = x then P else Q) else R) = (case_order P Q R (compare x y))" 
  "(if x \<le> y then (if x < y then Q else P) else R) = (case_order P Q R (compare x y))" 
  "(if x < y then Q else (if y < x then R else P)) = (case_order P Q R (compare x y))" 
  "(if x < y then Q else (if x = y then P else R)) = (case_order P Q R (compare x y))" 
  "(if x < y then Q else (if y = x then P else R)) = (case_order P Q R (compare x y))" 
  "(if x = y then P else (if y < x then R else Q)) = (case_order P Q R (compare x y))" 
  "(if x = y then P else (if x < y then Q else R)) = (case_order P Q R (compare x y))" 
  "(if x = y then P else (if y \<le> x then R else Q)) = (case_order P Q R (compare x y))" 
  "(if x = y then P else (if x \<le> y then Q else R)) = (case_order P Q R (compare x y))" 
  by (auto simp: compare_is_comparator_of comparator_of_def)  
end

ML_file "compare_code.ML"

text \<open>@{text "Compare_Code.change_compare_code const ty-vars"} changes the code equations of some constant such that
  two consecutive comparisons via @{term "op <="}, @{term "op <"}", or @{term "op ="} are turned into one
  invocation of @{const compare}. 
  The difference to a standard @{text "code_unfold"} is that here we change the code-equations
  where an additional sort-constraint on @{class compare_order} can be added. Otherwise, there would
  be no @{const compare}-function.\<close>

end