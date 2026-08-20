theory Sorted_Terms_Typing
  imports
    Nonground_Term_Typing
    Sorted_Terms.Sorted_Terms
    IsaFoR_Nonground_Term
    Typed_IMGU
    Monomorphic_Typing_Compatibility
begin

locale sorted_terms_typing =
  fixes \<F> :: "'f \<times> 'ty list \<Rightarrow> 'ty option"
begin

abbreviation welltyped :: "('v, 'ty) var_types \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> 'ty \<Rightarrow> bool" where
  "welltyped \<V> t \<tau> \<equiv> t : \<tau> in \<T>(\<F>, Some \<circ> \<V>)"

notation welltyped (\<open>_ \<turnstile> _ : _\<close> [1000, 0, 50] 50)

sublocale "term": base_typing where
  welltyped = "welltyped \<V>" for \<V>
proof unfold_locales
  show "right_unique (welltyped \<V>)"
  proof (rule right_uniqueI)
    fix t \<tau>\<^sub>1 \<tau>\<^sub>2
    assume "\<V> \<turnstile> t : \<tau>\<^sub>1" and "\<V> \<turnstile> t : \<tau>\<^sub>2"

    thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
      by fastforce
  qed
qed

sublocale "term": term_typing where 
  welltyped = "welltyped \<V>" and apply_context = ctxt_apply_term for \<V>
proof unfold_locales
  fix t t' c \<tau> \<tau>'

  assume
    welltyped_t_t': "\<V> \<turnstile> t : \<tau>'" "\<V> \<turnstile> t' : \<tau>'" and
    welltyped_c_t: "\<V> \<turnstile> c\<langle>t\<rangle> : \<tau>"

  from welltyped_c_t show "\<V> \<turnstile> c\<langle>t'\<rangle> : \<tau>"
  proof (induction c arbitrary: \<tau>)
    case Hole

    then show ?case 
      using welltyped_t_t'
      by (metis has_same_type intp_actxt.simps(1))
  next
    case (More f ss1 c ss2)

    have "\<V>  \<turnstile> Fun f (ss1 @ c\<langle>t\<rangle> # ss2) : \<tau>"
      using More.prems
      by (metis intp_actxt.simps(2))

    then have "\<V>  \<turnstile> Fun f (ss1 @ c\<langle>t'\<rangle> # ss2) : \<tau>"
      unfolding Fun_hastype
      by (smt (verit, ccfv_threshold) More.IH list_all2_Cons1 list_all2_append list_all2_append1)

    then show ?case
      by (metis intp_actxt.simps(2))
  qed
next
  fix c t \<tau>
  assume "\<V> \<turnstile> c\<langle>t\<rangle> : \<tau>"

  then show "\<exists>\<tau>'. \<V> \<turnstile> t : \<tau>'"
    by 
      (induction c arbitrary: \<tau>)
      (auto simp: Fun_hastype list_all2_Cons1 list_all2_append1)
qed

sublocale "term": base_typing_properties where
  id_subst = "Var :: 'v \<Rightarrow> ('f, 'v) term" and comp_subst = "(\<circ>\<^sub>s)" and subst = "(\<cdot>)" and
  vars = term.vars and is_ground = term.is_ground and welltyped = "welltyped" and
  to_ground = term.to_ground and from_ground = term.from_ground and subst_update = fun_upd and
  apply_subst = apply_subst
proof unfold_locales
  fix t :: "('f, 'v) term" and \<V> \<sigma> \<tau>
  assume type_preserving_\<sigma>: "\<forall>x\<in>vars t. \<V> \<turnstile> term.Var x : \<V> x \<longrightarrow> \<V> \<turnstile> \<sigma> x : \<V> x"

  show "\<V> \<turnstile> t \<cdot> \<sigma> : \<tau> \<longleftrightarrow> \<V> \<turnstile> t : \<tau>"  
  proof (rule iffI)
    assume "\<V> \<turnstile> t : \<tau>"

    then show "\<V> \<turnstile> t \<cdot> \<sigma> : \<tau>"
      using type_preserving_\<sigma>
      by (smt (verit, best) Term.simps(1) comp_apply eq_Some_iff_hastype subst_hastype_iff_vars)
   
  next
    assume "\<V> \<turnstile> t \<cdot> \<sigma> : \<tau>"

    then show "\<V> \<turnstile> t : \<tau>"
      using type_preserving_\<sigma>
      by (smt (verit, ccfv_SIG) Var_hastype comp_apply eq_Some_iff_hastype subst_hastype_iff_vars)
  qed
next
  fix t :: "('f, 'v) term" and \<V> \<V>' \<tau>

  assume "\<V> \<turnstile> t : \<tau>" "\<forall>x\<in>term.vars t. \<V> x = \<V>' x"

  then show "\<V>' \<turnstile> t : \<tau>"
    by (smt (verit, del_insts) Var_hastype hastype_in_o subst_hastype_iff_vars)
next
  fix \<V> \<V>' :: "('v, 'ty) var_types" and t :: "('f, 'v) term" and \<rho> :: "('f, 'v) subst" and \<tau>

  assume
    renaming: "term.is_renaming \<rho>" and
    \<V>: "\<forall>x\<in>term.vars t. \<V> x = \<V>' (term.rename \<rho> x)"

  then show "\<V>' \<turnstile> t \<cdot> \<rho> : \<tau> \<longleftrightarrow> \<V> \<turnstile> t : \<tau>"
  proof(intro iffI)

    assume "\<V>' \<turnstile> t \<cdot> \<rho> : \<tau>"

    with \<V> show "\<V> \<turnstile> t : \<tau>"
    proof(induction t arbitrary: \<tau>)
      case (Var x)

      then have "\<V>' (term.rename \<rho> x) = \<tau>"
        using renaming term_id_subst_rename 
        by fastforce

      then have "\<V> x = \<tau>"
        by (simp add: Var.prems(1))

      then show ?case
        by simp
    next
      case (Fun f ts)

      then have "\<V>' \<turnstile> Fun f (map (\<lambda>s. s \<cdot> \<rho>) ts) : \<tau>"
        by (metis eval_term.simps(2))

      then obtain \<tau>s where 
        \<tau>s: "those (map \<T>(\<F>, Some \<circ> \<V>') (map (\<lambda>s. s \<cdot> \<rho>) ts)) = Some \<tau>s"  and 
        \<F>: "\<F> (f, \<tau>s) = Some \<tau>"
        by (meson Fun_hastype fun_hastype_def hastype_list_iff_those)

      then show ?case
        by (smt (verit, best) Fun.prems Var_hastype exists_nonground_term
            hastype_in_o renaming subst_hastype_iff_vars
            term.id_subst_rename)
    qed
  next
    assume "\<V> \<turnstile> t : \<tau>"

    then show "\<V>' \<turnstile> t \<cdot> \<rho> : \<tau>"
      using \<V>
      by (smt (verit, best) Var_hastype hastype_in_o renaming
          subst_hastype_iff_vars term_id_subst_rename)
  qed
next
  fix \<V> :: "('v, 'ty) var_types"  and x

  show "\<V> \<turnstile> Var x : \<V> x \<or> \<not> term.is_welltyped \<V> (Var x)"
    by simp
qed

sublocale "term": typed_term_imgu where 
  welltyped = "welltyped :: ('v \<Rightarrow> 'ty) \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> 'ty \<Rightarrow> bool"
  by unfold_locales

lemma exists_witness_if_exists_const_for_all_types: 
  assumes "\<And>\<tau>. \<exists>f. \<F> (f, []) = Some \<tau>"
  shows "\<exists>t. term.is_ground t \<and> welltyped \<V> t \<tau>"
  by (meson Term_empty_vars_subst assms fun_hastype_def list_all2_Nil2 subst_Term_empty_hastype
      term.sort_matches)

end

end
