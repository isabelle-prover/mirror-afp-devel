theory Ground_Typing
  imports
    Ground_Clause
    Clause_Typing
    Term_Typing
begin

inductive welltyped for \<F> where
  GFun: "\<F> f (length ts) = (\<tau>s, \<tau>) \<Longrightarrow> list_all2 (welltyped \<F>) ts \<tau>s \<Longrightarrow> welltyped \<F> (GFun f ts) \<tau>"

lemma right_unique_welltyped[iff]: "right_unique (welltyped \<F>)"
proof (rule right_uniqueI)
  fix t \<tau>\<^sub>1 \<tau>\<^sub>2
  assume "welltyped \<F> t \<tau>\<^sub>1" and "welltyped \<F> t \<tau>\<^sub>2"
  thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
    by (auto elim!: welltyped.cases)
qed

lemma welltyped_context_compatible:
  assumes
    t_type: "welltyped \<F> t \<tau>'" and
    t'_type: "welltyped \<F> t' \<tau>'" and
    c_type: "welltyped \<F> c\<langle>t\<rangle>\<^sub>G \<tau>"
  shows "welltyped \<F> c\<langle>t'\<rangle>\<^sub>G \<tau>"
proof -
  from c_type show "welltyped \<F> c\<langle>t'\<rangle>\<^sub>G \<tau>"
  proof (induction c arbitrary: \<tau>)
    case Hole
    thus ?case
      using t_type t'_type
      using right_unique_welltyped[THEN right_uniqueD]
      by fastforce
  next
    case (More f ss1 c ss2)

    have "welltyped \<F> (GFun f (ss1 @ c\<langle>t\<rangle>\<^sub>G # ss2)) \<tau>"
      using More.prems
      by simp

    hence "welltyped \<F> (GFun f (ss1 @ c\<langle>t'\<rangle>\<^sub>G # ss2)) \<tau>"
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
qed

lemma welltyped_subterms:
  fixes f ts \<tau>
  assumes "welltyped \<F> (GFun f ts) \<tau>"
  shows "\<forall>t\<in>set ts. \<exists>\<tau>'. welltyped \<F> t \<tau>'"
  using assms
  by (metis gterm.inject in_set_conv_nth list_all2_conv_all_nth welltyped.simps)

global_interpretation "term": term_typing where
  welltyped = "welltyped \<F>" and Fun = GFun
  for \<F> :: "('f, 'ty) fun_types"
  by unfold_locales
    (auto intro: welltyped_context_compatible welltyped_subterms[rule_format])

global_interpretation clause_typing where
  term_welltyped = "welltyped \<F>"
  for \<F> :: "('f, 'ty) fun_types"
  by unfold_locales

end
