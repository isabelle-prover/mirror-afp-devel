(* Author: Xingyuan Zhang, Chunhan Wu, Christian Urban *)
theory Folds
imports "../Regular-Sets/Regular_Exp"
begin

section {* ``Summation'' for regular expressions *}

text {*
  To obtain equational system out of finite set of equivalence classes, a fold operation
  on finite sets @{text "folds"} is defined. The use of @{text "SOME"} makes @{text "folds"}
  more robust than the @{text "fold"} in the Isabelle library. The expression @{text "folds f"}
  makes sense when @{text "f"} is not @{text "associative"} and @{text "commutitive"},
  while @{text "fold f"} does not.  
*}


definition 
  folds :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b"
where
  "folds f z S \<equiv> SOME x. fold_graph f z S x"

text {* Plus-combination for a set of regular expressions *}

abbreviation
  Setalt :: "'a rexp set \<Rightarrow> 'a rexp" ("\<Uplus>_" [1000] 999) 
where
  "\<Uplus>A \<equiv> folds Plus Zero A"

text {* 
  For finite sets, @{term Setalt} is preserved under @{term lang}.
*}

lemma folds_plus_simp [simp]:
  fixes rs::"('a rexp) set"
  assumes a: "finite rs"
  shows "lang (\<Uplus>rs) = \<Union> (lang ` rs)"
unfolding folds_def
apply(rule set_eqI)
apply(rule someI2_ex)
apply(rule_tac finite_imp_fold_graph[OF a])
apply(erule fold_graph.induct)
apply(auto)
done

end