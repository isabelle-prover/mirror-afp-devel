theory Comparator
imports Main
begin

datatype order = Eq | Lt | Gt

type_synonym 'a comparator = "'a \<Rightarrow> 'a \<Rightarrow> order"

section \<open>Connection between comparators and linear orders\<close>

definition lt_of_comp :: "'a comparator \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "lt_of_comp acomp x y = (case acomp x y of Lt \<Rightarrow> True | _ \<Rightarrow> False)"

definition le_of_comp :: "'a comparator \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "le_of_comp acomp x y = (case acomp x y of Gt \<Rightarrow> False | _ \<Rightarrow> True)"

fun sym_order:: "order \<Rightarrow> order" where
  "sym_order Lt = Gt" |
  "sym_order Gt = Lt" |
  "sym_order Eq = Eq"

locale comparator =
  fixes comp :: "'a comparator"
  assumes sym: "sym_order (comp x y) = comp y x"
    and weak_eq: "comp x y = Eq \<Longrightarrow> x = y"
    and trans: "comp x y = Lt \<Longrightarrow> comp y z = Lt \<Longrightarrow> comp x z = Lt"
begin 

lemma eq: "(comp x y = Eq) = (x = y)"
proof
  assume "x = y"
  with sym [of y y] show "comp x y = Eq" by (cases "comp x y") auto
qed (rule weak_eq)

lemma comp_same [simp]:
  "comp x x = Eq"
  by (simp add: eq)

abbreviation "lt \<equiv> lt_of_comp comp"
abbreviation "le \<equiv> le_of_comp comp"

lemma linorder: "class.linorder le lt"
proof
  note [simp] = lt_of_comp_def le_of_comp_def
  fix x y z :: 'a
  show "lt x y = (le x y \<and> \<not> le y x)"
    using sym [of x y] by (cases "comp x y") (simp_all)
  show "le x y \<or> le y x"
    using sym [of x y] by (cases "comp x y") (simp_all)
  show "le x x" using eq [of x x] by (simp)
  show "le x y \<Longrightarrow> le y x \<Longrightarrow> x = y"
    using sym [of x y] by (cases "comp x y") (simp_all add: eq)
  show "le x y \<Longrightarrow> le y z \<Longrightarrow> le x z"
    by (cases "comp x y" "comp y z" rule: order.exhaust [case_product order.exhaust])
       (auto dest: trans simp: eq)
qed

end

definition (in linorder) comparator_of :: "'a comparator" where
  "comparator_of x y = (if x < y then Lt else if x = y then Eq else Gt)"

lemma comparator_of: "comparator comparator_of"
  by (unfold_locales) (auto split: if_splits simp: comparator_of_def)

end
