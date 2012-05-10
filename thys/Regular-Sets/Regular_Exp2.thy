(* Author: Tobias Nipkow *)

header "Extended Regular Expressions"

theory Regular_Exp2
imports Regular_Set
begin

datatype 'a rexp =
  Zero |
  One |
  Atom 'a |
  Plus "('a rexp)" "('a rexp)" |
  Times "('a rexp)" "('a rexp)" |
  Star "('a rexp)" |
  Not "('a rexp)" |
  Inter "('a rexp)" "('a rexp)"

context
fixes S :: "'a set"
begin

primrec lang :: "'a rexp => 'a lang" where
"lang Zero = {}" |
"lang One = {[]}" |
"lang (Atom a) = {[a]}" |
"lang (Plus r s) = (lang r) Un (lang s)" |
"lang (Times r s) = conc (lang r) (lang s)" |
"lang (Star r) = star(lang r)" |
"lang (Not r) = lists S - lang r" |
"lang (Inter r s) = (lang r Int lang s)"

end

primrec atoms :: "'a rexp \<Rightarrow> 'a set"
where
"atoms Zero = {}" |
"atoms One = {}" |
"atoms (Atom a) = {a}" |
"atoms (Plus r s) = atoms r \<union> atoms s" |
"atoms (Times r s) = atoms r \<union> atoms s" |
"atoms (Star r) = atoms r" |
"atoms (Not r) = atoms r" |
"atoms (Inter r s) = atoms r Un atoms s"

lemma lang_subset_lists: "atoms r \<subseteq> S \<Longrightarrow> lang S r \<subseteq> lists S"
by(induction r)(auto simp: conc_subset_lists star_subset_lists)

end
