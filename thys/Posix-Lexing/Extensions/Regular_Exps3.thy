(* Adapted from Tobias Nipkow in order to accommodate 
   bounded regular expressions *)

section "Extended Regular Expressions 3"

theory Regular_Exps3
imports "Regular-Sets.Regular_Set"
begin

datatype (atoms: 'a) rexp =
  is_Zero: Zero |
  is_One: One |
  Atom 'a |
  Plus "('a rexp)" "('a rexp)" |
  Times "('a rexp)" "('a rexp)" |
  Star "('a rexp)" |
  NTimes "('a rexp)" "nat" | (* r{n}    - exactly n-times *)
  Upto "('a rexp)" "nat"     (* r{..n}  - up to n-times *)  

fun lang :: "'a rexp => 'a lang" where
"lang Zero = {}" |
"lang One = {[]}" |
"lang (Atom a) = {[a]}" |
"lang (Plus r s) = (lang r) Un (lang s)" |
"lang (Times r s) = conc (lang r) (lang s)" |
"lang (Star r) = star(lang r)" |
"lang (NTimes r n) = ((lang r) ^^ n)" | 
"lang (Upto r n) = (\<Union>i \<in> {..n}. (lang r) ^^ i)"


lemma lang_subset_lists: 
  "atoms r \<subseteq> A \<Longrightarrow> lang r \<subseteq> lists A"
  apply (induction r)
  apply(auto simp: conc_subset_lists star_subset_lists lang_pow_subset_lists)
  by (meson in_listsD lang_pow_subset_lists subsetD)
  

primrec nullable :: "'a rexp \<Rightarrow> bool" where
"nullable Zero = False" |
"nullable One = True" |
"nullable (Atom c) = False" |
"nullable (Plus r1 r2) = (nullable r1 \<or> nullable r2)" |
"nullable (Times r1 r2) = (nullable r1 \<and> nullable r2)" |
"nullable (Star r) = True" |
"nullable (NTimes r n) = (if n = 0 then True else nullable r)" |
"nullable (Upto r n) = True"


lemma pow_empty_iff:
  shows "[] \<in> (lang r) ^^ n \<longleftrightarrow> (if n = 0 then True else [] \<in> (lang r))"
  by (induct n)(auto)

lemma nullable_iff: 
  shows "nullable r \<longleftrightarrow> [] \<in> lang r"
  by (induct r) (auto simp add: conc_def pow_empty_iff split: if_splits)

end
