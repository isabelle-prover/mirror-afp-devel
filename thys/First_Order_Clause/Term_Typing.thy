theory Term_Typing
  imports Typing Context_Extra
begin

type_synonym ('f, 'ty) fun_types = "'f \<Rightarrow> nat \<Rightarrow> 'ty list \<times> 'ty"

locale context_compatible_typing =
  fixes Fun welltyped
  assumes
   context_compatible [intro]:
    "\<And>t t' c \<tau> \<tau>'.
      welltyped t \<tau>' \<Longrightarrow>
      welltyped t' \<tau>' \<Longrightarrow>
      welltyped (Fun\<langle>c; t\<rangle>) \<tau> \<Longrightarrow>
      welltyped (Fun\<langle>c; t'\<rangle>) \<tau>"

locale subterm_typing =
  fixes Fun welltyped
  assumes
    subterm': "\<And>f ts \<tau>. welltyped (Fun f ts) \<tau> \<Longrightarrow> \<forall>t\<in>set ts. \<exists>\<tau>'. welltyped t \<tau>'"
begin

lemma subterm: "welltyped (Fun\<langle>c; t\<rangle>) \<tau> \<Longrightarrow> \<exists>\<tau>. welltyped t \<tau>"
proof(induction c arbitrary: \<tau>)
  case Hole
  then show ?case
    by auto
next
  case (More f ss1 c ss2)

 then have "welltyped (Fun f (ss1 @ Fun\<langle>c;t\<rangle> # ss2)) \<tau>"
    by simp

  then have "\<exists>\<tau>. welltyped (Fun\<langle>c;t\<rangle>) \<tau>"
    using subterm'
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
  typed: context_compatible_typing where welltyped = welltyped +
  welltyped: context_compatible_typing where welltyped = welltyped +
  welltyped: subterm_typing where welltyped = welltyped

end
