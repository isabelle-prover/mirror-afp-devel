subsubsection \<open>Sets of Unifiers\<close>

theory Unifiers_More
  imports
    First_Order_Terms.Term_More
    First_Order_Terms.Unifiers
begin

lemma is_mguI:
  fixes \<sigma> :: "('f, 'v) subst"
  assumes "\<forall>(s, t) \<in> E. s \<cdot> \<sigma> = t \<cdot> \<sigma>"
    and "\<And>\<tau> :: ('f, 'v) subst. \<forall>(s, t) \<in> E. s \<cdot> \<tau> = t \<cdot> \<tau> \<Longrightarrow> \<exists>\<gamma> :: ('f, 'v) subst. \<tau> = \<sigma> \<circ>\<^sub>s \<gamma>"
  shows "is_mgu \<sigma> E"
  using assms by (fastforce simp: is_mgu_def unifiers_def)

lemma subst_set_insert [simp]:
  "subst_set \<sigma> (insert e E) = insert (fst e \<cdot> \<sigma>, snd e \<cdot> \<sigma>) (subst_set \<sigma> E)"
  by (auto simp: subst_set_def)

lemma unifiable_UnD [dest]:
  "unifiable (M \<union> N) \<Longrightarrow> unifiable M \<and> unifiable N"
  by (auto simp: unifiable_def)

lemma supt_imp_not_unifiable:
  assumes "s \<rhd> t"
  shows "\<not> unifiable {(t, s)}"
proof
  assume "unifiable {(t, s)}"
  then obtain \<sigma> where "\<sigma> \<in> unifiers {(t, s)}"
    by (auto simp: unifiable_def)
  then have "t \<cdot> \<sigma> = s \<cdot> \<sigma>" by (auto)
  moreover have "s \<cdot> \<sigma> \<rhd> t \<cdot> \<sigma>"
    using assms by (metis instance_no_supt_imp_no_supt)
  ultimately show False by auto
qed

lemma unifiable_insert_Var_swap [simp]:
  "unifiable (insert (t, Var x) E) \<longleftrightarrow> unifiable (insert (Var x, t) E)"
  by (rule unifiable_insert_swap)

lemma unifiers_Int1 [simp]:
  "(s, t) \<in> E \<Longrightarrow> unifiers {(s, t)} \<inter> unifiers E = unifiers E"
  by (auto simp: unifiers_def)

lemma imgu_linear_var_disjoint:
  assumes "is_imgu \<sigma> {(l2 |_ p, l1)}"
    and "p \<in> poss l2"
    and "linear_term l2"
    and "vars_term l1 \<inter> vars_term l2 = {}"
    and "q \<in> poss l2"
    and "parallel_pos p q"
  shows "l2 |_ q = l2 |_ q \<cdot> \<sigma>"
  using assms
proof (induct p arbitrary: q l2)
  case (Cons i p)
  from this(3) obtain f ls where 
    l2[simp]: "l2 = Fun f ls" and 
    i: "i < length ls" and 
    p: "p \<in> poss (ls ! i)"
    by (cases l2) (auto)
  then have l2i: "l2 |_ ((i # p)) = ls ! i |_ p" by auto
  have "linear_term (ls ! i)" using Cons(4) l2 i by simp
  moreover have "vars_term l1 \<inter> vars_term (ls ! i) = {}" using Cons(5) l2 i by force
  ultimately have IH: "\<And>q. q \<in> poss (ls ! i) \<Longrightarrow> p \<bottom> q \<Longrightarrow> ls ! i |_ q = ls ! i |_ q \<cdot> \<sigma>" 
    using Cons(1)[OF Cons(2)[unfolded l2i] p] by blast
  from Cons(7) obtain j q' where q: "q = j # q'" by (cases q) auto
  show ?case
  proof (cases "j = i") 
    case True with Cons(6,7) IH q show ?thesis by simp
  next
    case False
    from Cons(6) q have j: "j < length ls" by simp 
    { fix y
      assume y: "y \<in> vars_term (l2 |_ q)"
      let ?\<tau> = "\<lambda>x. if x = y then Var y else \<sigma> x"
      from y Cons(6) q j have yj:"y \<in> vars_term (ls ! j)" 
        by simp (meson subt_at_imp_supteq subteq_Var_imp_in_vars_term supteq_Var supteq_trans)
      { fix i j
        assume j:"j < length ls" and i:"i < length ls" and neq: "i \<noteq> j"
        from j Cons(4) have "\<forall>i < j. vars_term (ls ! i) \<inter> vars_term (ls ! j) = {}"
          by (auto simp : is_partition_def)
        moreover from i Cons(4) have "\<forall>j < i. vars_term (ls ! i) \<inter> vars_term (ls ! j) = {}"
          by (auto simp : is_partition_def)
        ultimately have "vars_term (ls ! i) \<inter> vars_term (ls ! j) = {}" 
          using neq by (cases "i < j") auto
      }
      from this[OF i j False] have "y \<notin> vars_term (ls ! i)" using yj by auto
      then have "y \<notin> vars_term (l2 |_ ((i # p)))"
        by (metis l2i p subt_at_imp_supteq subteq_Var_imp_in_vars_term supteq_Var supteq_trans)
      then have "\<forall>x \<in> vars_term (l2 |_ ((i # p))). ?\<tau> x = \<sigma> x" by auto
      then have l2\<tau>\<sigma>: "l2 |_ ((i # p)) \<cdot> ?\<tau> = l2 |_ ((i # p)) \<cdot> \<sigma>" using term_subst_eq[of _ \<sigma> ?\<tau>] by simp
      from Cons(5) have "y \<notin> vars_term l1" using y Cons(6) vars_term_subt_at by fastforce
      then have "\<forall>x \<in> vars_term l1. ?\<tau> x = \<sigma> x" by auto
      then have l1\<tau>\<sigma>:"l1 \<cdot> ?\<tau> = l1 \<cdot> \<sigma>" using term_subst_eq[of _ \<sigma> ?\<tau>] by simp
      have "l1 \<cdot> \<sigma> = l2 |_ (i # p) \<cdot> \<sigma>" using Cons(2) unfolding is_imgu_def by auto
      then have "l1 \<cdot> ?\<tau> = l2 |_ (i # p) \<cdot> ?\<tau>"  using l1\<tau>\<sigma> l2\<tau>\<sigma> by simp
      then have "?\<tau> \<in> unifiers {(l2 |_ (i # p), l1)}" unfolding unifiers_def by simp
      with Cons(2) have \<tau>\<sigma>:"?\<tau> = \<sigma> \<circ>\<^sub>s ?\<tau>" unfolding is_imgu_def by blast
      have "Var y = Var y \<cdot> \<sigma>"
      proof (rule ccontr)
        let ?x = "Var y \<cdot> \<sigma>"
        assume *:"Var y \<noteq> ?x"
        have "Var y = Var y \<cdot> ?\<tau>" by auto
        also have "... = (Var y \<cdot> \<sigma>) \<cdot> ?\<tau>" using \<tau>\<sigma> subst_subst by metis 
        finally have xy:"?x \<cdot> \<sigma> = Var y" using * by (cases "\<sigma> y") auto 
        have "\<sigma> \<circ>\<^sub>s \<sigma> = \<sigma>" using Cons(2) unfolding is_imgu_def by auto
        then have "?x \<cdot> (\<sigma> \<circ>\<^sub>s \<sigma>) = Var y" using xy by auto
        moreover have "?x \<cdot> \<sigma> \<cdot> \<sigma> = ?x" using xy by auto
        ultimately show False using * by auto
      qed
    }
    then show ?thesis by (simp add: term_subst_eq)
  qed
qed auto

end