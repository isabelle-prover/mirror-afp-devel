theory Typing
  imports Main
begin

locale typing =
  fixes welltyped :: "'expr \<Rightarrow> 'ty \<Rightarrow> bool"
  assumes right_unique: "right_unique welltyped"
begin

lemmas right_uniqueD [dest] = right_uniqueD[OF right_unique]

end

locale base_typing = typing
begin

abbreviation is_welltyped where 
  "is_welltyped expr \<equiv> \<exists>\<tau>. welltyped expr \<tau>"

end

locale typing_lifting = sub: typing where welltyped = sub_welltyped 
  for sub_welltyped :: "'sub \<Rightarrow> 'ty \<Rightarrow> bool" +
  fixes to_set :: "'expr \<Rightarrow> 'sub set" 
begin

definition is_welltyped where
  "is_welltyped expr \<equiv> \<exists>\<tau>. \<forall>sub \<in> to_set expr. sub_welltyped sub \<tau>"

abbreviation welltyped where
  "welltyped expr (_::unit) \<equiv> is_welltyped expr"

sublocale typing where welltyped = welltyped
  by unfold_locales (auto simp: right_unique_def)

end

locale typing_lifting' =
  fixes
    sub_welltyped :: "'extra \<Rightarrow> 'sub \<Rightarrow> 'ty' \<Rightarrow> bool" and 
    to_set :: "'expr \<Rightarrow> 'sub set"
  assumes lifting: "\<And>extra. typing_lifting (sub_welltyped extra)"
begin

sublocale typing_lifting where
  sub_welltyped = "sub_welltyped \<V>" and to_set = to_set
  by (rule lifting)

end

end
