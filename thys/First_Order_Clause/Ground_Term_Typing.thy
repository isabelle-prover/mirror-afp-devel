theory Ground_Term_Typing
  imports
    Term_Typing
    Ground_Term_Extra
    Ground_Context
begin

type_synonym ('f, 'ty) fun_types = "'f \<Rightarrow> nat \<Rightarrow> 'ty list \<times> 'ty"

inductive welltyped for \<F> where 
  GFun: "\<F> f (length ts) = (\<tau>s, \<tau>) \<Longrightarrow> list_all2 (welltyped \<F>) ts \<tau>s \<Longrightarrow> welltyped \<F> (GFun f ts) \<tau>"

notation welltyped (\<open>_ \<turnstile> _ : _\<close> [1000, 0] 50)

global_interpretation "term": term_typing where
  welltyped = "welltyped \<F>" and Fun = GFun
proof unfold_locales

  show right_unique_welltyped: "right_unique (welltyped \<F>)"
  proof (rule right_uniqueI)
    fix t \<tau>\<^sub>1 \<tau>\<^sub>2
    assume "\<F> \<turnstile> t : \<tau>\<^sub>1" and "\<F> \<turnstile> t : \<tau>\<^sub>2"

    thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
      by (auto elim!: welltyped.cases)
  qed

  fix t t' c \<tau> \<tau>'
  assume  
    t_type: "\<F> \<turnstile> t : \<tau>'" and
    t'_type: "\<F> \<turnstile> t' : \<tau>'" and
    c_type: "\<F> \<turnstile> c\<langle>t\<rangle>\<^sub>G : \<tau>"

  from c_type show "\<F> \<turnstile> c\<langle>t'\<rangle>\<^sub>G : \<tau>"
  proof (induction c arbitrary: \<tau>)
    case Hole
    thus ?case
      using t_type t'_type
      using right_unique_welltyped[THEN right_uniqueD]
      by fastforce
  next
    case (More f ss1 c ss2)

    have "\<F> \<turnstile> GFun f (ss1 @ c\<langle>t\<rangle>\<^sub>G # ss2) : \<tau>"
      using More.prems
      by simp

    hence "\<F> \<turnstile> GFun f (ss1 @ c\<langle>t'\<rangle>\<^sub>G # ss2) : \<tau>"
    proof (cases \<F> "GFun f (ss1 @ c\<langle>t\<rangle>\<^sub>G # ss2)" \<tau> rule: welltyped.cases)
      case (GFun \<tau>s)

      show ?thesis
      proof (rule welltyped.GFun)

        show "\<F> f (length (ss1 @ c\<langle>t'\<rangle>\<^sub>G # ss2)) = (\<tau>s, \<tau>)"
          using GFun(1)
          by simp
      next

        show "list_all2 (welltyped \<F>) (ss1 @ c\<langle>t'\<rangle>\<^sub>G # ss2) \<tau>s"
          using GFun(2) More.IH
          by (smt (verit, del_insts) list_all2_Cons1 list_all2_append1 list_all2_lengthD)
      qed
    qed

    thus ?case
      by simp
  qed
next
  fix f ts \<tau>
  assume "\<F> \<turnstile> GFun f ts : \<tau>"

  then show "\<forall>t\<in>set ts. \<exists>\<tau>'. \<F> \<turnstile> t : \<tau>'"
    by (metis gterm.inject in_set_conv_nth list_all2_conv_all_nth welltyped.simps)
qed

end
