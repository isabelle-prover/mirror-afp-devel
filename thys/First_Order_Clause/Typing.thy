theory Typing
  imports Main
begin

locale typed =
  fixes typed :: "'expr \<Rightarrow> 'ty \<Rightarrow> bool"
  assumes right_unique: "right_unique typed"
begin

lemmas right_uniqueD [dest] = right_uniqueD[OF right_unique]

end

locale base_typed = typed
begin

abbreviation is_typed where 
  "is_typed expr \<equiv> \<exists>\<tau>. typed expr \<tau>"

end

(* TODO: Generalize? *)
locale typed_lifting =
  sub: typed where typed = sub_typed 
for sub_typed :: "'sub \<Rightarrow> 'ty \<Rightarrow> bool" +
fixes to_set :: "'expr \<Rightarrow> 'sub set" 
begin

definition is_typed where
  "is_typed expr \<equiv> \<exists>\<tau>. \<forall>sub \<in> to_set expr. sub_typed sub \<tau>"

abbreviation typed where
  "typed expr (_::unit) \<equiv> is_typed expr"

sublocale typed where typed = typed
  by unfold_locales (auto simp: right_unique_def)

end

locale typing =
  typed: typed where typed = typed +
  welltyped: typed where typed = welltyped
for typed welltyped :: "'expr \<Rightarrow> 'ty \<Rightarrow> bool" +
assumes typed_if_welltyped: "\<And>expr \<tau>. welltyped expr \<tau> \<Longrightarrow> typed expr \<tau>"

locale base_typing =
  typing +
  typed: base_typed where typed = typed +
  welltyped: base_typed where typed = welltyped
begin

abbreviation is_typed where
  "is_typed \<equiv> typed.is_typed"

abbreviation is_welltyped where
  "is_welltyped \<equiv> welltyped.is_typed"

lemma is_typed_if_is_welltyped: "is_welltyped expr \<Longrightarrow> is_typed expr"
  using typed_if_welltyped
  by blast

end

locale typing_lifting = 
 sub: typing where typed = sub_typed and welltyped = sub_welltyped +
 typed: typed_lifting where sub_typed = sub_typed +
 welltyped: typed_lifting where sub_typed = sub_welltyped
for sub_typed sub_welltyped :: "'sub \<Rightarrow> 'ty \<Rightarrow> bool"
begin

abbreviation typed where
  "typed \<equiv> typed.typed"

abbreviation welltyped where
  "welltyped \<equiv> welltyped.typed"

abbreviation is_typed where
  "is_typed \<equiv> typed.is_typed"

abbreviation is_welltyped where
  "is_welltyped \<equiv> welltyped.is_typed"

lemmas is_typed_def = typed.is_typed_def

lemmas is_welltyped_def = welltyped.is_typed_def

sublocale typing where typed = typed and welltyped = welltyped
  by unfold_locales (auto simp: is_typed_def is_welltyped_def intro: sub.typed_if_welltyped)

lemmas is_typed_if_is_welltyped = typed_if_welltyped

end

locale typing_lifting' =
fixes
  sub_typed sub_welltyped :: "'extra \<Rightarrow> 'sub \<Rightarrow> 'ty' \<Rightarrow> bool" and 
  to_set :: "'expr \<Rightarrow> 'sub set"
assumes lifting: "\<And>extra. typing_lifting (sub_typed extra) (sub_welltyped extra)"
begin

sublocale typing_lifting where
  sub_typed = "sub_typed \<V>" and sub_welltyped = "sub_welltyped \<V>" and to_set = to_set
  by (rule lifting)

end

end
