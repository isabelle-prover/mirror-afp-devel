(* Author: R. Thiemann *)
section \<open>Elimination of CARD('n)\<close>

text \<open>In the following theory we provide a method which modifies theorems
  of the form $P[CARD('n)]$ into $n != 0 \Longrightarrow P[n]$, so that they can more
  easily be applied.
  
  Known issues: there might be problems with nested meta-implications and meta-quantification.\<close>

theory Cancel_Card_Constraint
imports 
  "Types_To_Sets/Types_To_Sets"
  "~~/src/HOL/Library/Cardinality"
begin

lemma n_zero_nonempty: "n \<noteq> 0 \<Longrightarrow> {0 ..< n :: nat} \<noteq> {}" by auto

lemma type_impl_card_n: assumes "\<exists>(Rep :: 'a \<Rightarrow> nat) Abs. type_definition Rep Abs {0 ..< n :: nat}"
  shows "class.finite (TYPE('a)) \<and> CARD('a) = n"
proof -
  from assms obtain rep :: "'a \<Rightarrow> nat" and abs :: "nat \<Rightarrow> 'a" where t: "type_definition rep abs {0 ..< n}" by auto
  have "card (UNIV :: 'a set) = card {0 ..< n}" using t by (rule type_definition.card)
  also have "\<dots> = n" by auto
  finally have bn: "CARD ('a) = n" .
  have "finite (abs ` {0 ..< n})" by auto
  also have "abs ` {0 ..< n} = UNIV" using t by (rule type_definition.Abs_image)
  finally have "class.finite (TYPE('a))" unfolding class.finite_def .
  with bn show ?thesis by blast
qed  

ML_file "cancel_card_constraint.ML"

end