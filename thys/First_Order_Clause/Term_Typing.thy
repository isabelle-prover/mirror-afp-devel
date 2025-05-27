theory Term_Typing
  imports
    Context_Notation
    Typing
begin

(* TODO: Notation for welltyped *)
locale context_compatible_typing =
  apply_context_notation +
  fixes welltyped
  assumes
   welltyped_context_compatible [intro]:
    "\<And>t t' c \<tau> \<tau>'.
      welltyped t \<tau>' \<Longrightarrow>
      welltyped t' \<tau>' \<Longrightarrow>
      welltyped c\<langle>t\<rangle> \<tau> \<Longrightarrow>
      welltyped c\<langle>t'\<rangle> \<tau>"

locale subterm_typing =
  apply_context_notation +
  fixes welltyped
  assumes
   welltyped_subterm [intro]:
    "welltyped c\<langle>t\<rangle> \<tau> \<Longrightarrow> \<exists>\<tau>'. welltyped t \<tau>'"

locale term_typing =
  base_typing +
  context_compatible_typing +
  subterm_typing

end
