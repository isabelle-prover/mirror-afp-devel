(*
 * Code setup for native strings.
 * Author: René Neumann <rene.neumann@in.tum.de>
 *)
theory Code_String
imports
  "~~/src/HOL/Library/Code_Char"
  "~~/src/HOL/Library/List_lexord"
  "Collections_Patch2"
begin

text {* Instantiate linorder for String.literal and also use ordering on strings in the target language. This saves us casting between String.literal and string. *}

instantiation String.literal :: linorder
begin

(* Explicitly force lexicographic order *)
definition less_literal :: "String.literal \<Rightarrow> String.literal \<Rightarrow> bool"
where
  "less_literal s1 s2 \<longleftrightarrow> (explode s1, explode s2) \<in> lexord {(u,v). u < v}"

definition less_eq_literal :: "String.literal \<Rightarrow> String.literal \<Rightarrow> bool"
where
  "less_eq_literal s1 s2 \<longleftrightarrow> s1 < s2 \<or> s1 = s2"

(* Lift to using class-operations *)
lemma less_literal_alt_def:
  "s1 < s2 \<longleftrightarrow> explode s1 < explode s2"
unfolding less_literal_def
by (simp add: list_less_def)

lemma less_eq_literal_alt_def:
  "s1 \<le> s2 \<longleftrightarrow> explode s1 \<le> explode s2"
unfolding less_eq_literal_def
by (simp add: less_literal_alt_def list_le_def explode_inject)

instance
  apply default
  apply (auto simp add: less_literal_alt_def less_eq_literal_alt_def)
  apply (metis explode_inject)
  done
end

code_printing
  constant "Orderings.less_eq :: String.literal \<Rightarrow> String.literal \<Rightarrow> bool" \<rightharpoonup>
    (SML) "!((_ : string) <= _)"
    and (OCaml) "!((_ : string) <= _)"
    and (Haskell) infix 4 "<="
| constant "Orderings.less :: String.literal \<Rightarrow> String.literal \<Rightarrow> bool" \<rightharpoonup>
    (SML) "!((_ : string) < _)"
    and (OCaml) "!((_ : string) < _)"
    and (Haskell) infix 4 "<"


instantiation String.literal :: hashable_uint
begin
  definition hashcode_uint_literal :: "String.literal \<Rightarrow> uint32" 
    where "hashcode_uint_literal s = hashcode_uint (explode s)"

  definition def_hashmap_size_uint_literal 
    :: "String.literal itself \<Rightarrow> nat" where
    "def_hashmap_size_uint_literal _ = 10"

  instance proof
  qed (simp_all only: def_hashmap_size_uint_literal_def)
end

instantiation String.literal :: hashable
begin
  definition hashcode_literal :: "String.literal \<Rightarrow> nat" 
    where "hashcode_literal \<equiv> hashcode_nat"

  definition bounded_hashcode_literal :: "nat \<Rightarrow> String.literal \<Rightarrow> nat" 
    where "bounded_hashcode_literal = bounded_hashcode_nat"

  definition def_hashmap_size_literal :: "String.literal itself \<Rightarrow> nat" 
    where "def_hashmap_size_literal \<equiv> def_hashmap_size_uint"

  instance
    apply default
    unfolding def_hashmap_size_literal_def bounded_hashcode_literal_def
    using hashable_from_hashable_uint by auto
end

end
