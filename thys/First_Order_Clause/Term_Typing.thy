theory Term_Typing
  imports Typing Context_Extra
begin

locale context_compatible_typing =
  fixes Fun welltyped
  assumes
   welltyped_context_compatible [intro]:
    "\<And>t t' c \<tau> \<tau>'.
      welltyped t \<tau>' \<Longrightarrow>
      welltyped t' \<tau>' \<Longrightarrow>
      welltyped (Fun\<langle>c; t\<rangle>) \<tau> \<Longrightarrow>
      welltyped (Fun\<langle>c; t'\<rangle>) \<tau>"

locale subterm_typing =
  fixes Fun welltyped
  assumes
    welltyped_subterm': "\<And>f ts \<tau>. welltyped (Fun f ts) \<tau> \<Longrightarrow> \<forall>t\<in>set ts. \<exists>\<tau>'. welltyped t \<tau>'"
begin

lemma welltyped_subterm: "welltyped (Fun\<langle>c; t\<rangle>) \<tau> \<Longrightarrow> \<exists>\<tau>. welltyped t \<tau>"
proof(induction c arbitrary: \<tau>)
  case Hole
  then show ?case
    by auto
next
  case (More f ss1 c ss2)

 then have "welltyped (Fun f (ss1 @ Fun\<langle>c;t\<rangle> # ss2)) \<tau>"
    by simp

  then have "\<exists>\<tau>. welltyped (Fun\<langle>c;t\<rangle>) \<tau>"
    using welltyped_subterm'
    by simp

  then obtain \<tau>' where "welltyped (Fun\<langle>c;t\<rangle>) \<tau>'"
    by blast

  then show ?case
    using More.IH
    by simp
qed

end

locale term_typing =
  base_typing +
  context_compatible_typing where welltyped = welltyped +
  subterm_typing where welltyped = welltyped

end
