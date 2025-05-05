theory Term_Typing
  imports Typing Context_Extra
begin

locale context_compatible_typing =
  fixes Fun welltyped
  assumes
   welltyped_context_compatible [intro]:
    "\<And>t t' c \<tau>.
      \<forall>\<tau>'. welltyped t \<tau>' \<longleftrightarrow> welltyped t' \<tau>' \<Longrightarrow>
      welltyped (Fun\<langle>c; t\<rangle>) \<tau> \<Longrightarrow>
      welltyped (Fun\<langle>c; t'\<rangle>) \<tau>"

locale term_typing =
  base_typing +
  context_compatible_typing where welltyped = welltyped

end
