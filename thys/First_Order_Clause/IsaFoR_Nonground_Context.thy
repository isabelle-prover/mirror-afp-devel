theory IsaFoR_Nonground_Context
  imports 
    IsaFoR_Nonground_Term
    IsaFoR_Ground_Context
    Nonground_Context
    Context_Functor
begin

type_synonym ('f, 'v) "context" = "('f, 'v) ctxt"

abbreviation occurences where
  "occurences t x \<equiv> count (vars_term_ms t) x"

interpretation "context": term_based_lifting where
  comp_subst = "(\<circ>\<^sub>s)" and id_subst = Var and apply_subst = apply_subst and
  subst_update = fun_upd and subst_updates = subst_updates and
  sub_subst = "(\<cdot>)" and sub_vars = term.vars and sub_to_ground = term.to_ground and
  sub_from_ground = term.from_ground and term_vars = term.vars and term_subst = "(\<cdot>)" and
  term_to_ground = term.to_ground and term_from_ground = term.from_ground and
  to_ground_map = map_args_actxt and ground_map = map_args_actxt and
  from_ground_map = map_args_actxt and map = map_args_actxt and to_set = set2_actxt and
  to_set_ground = set2_actxt
  by unfold_locales

no_notation subst_apply_actxt (infixl \<open>\<cdot>\<^sub>c\<close> 67)
notation context.subst (infixl \<open>\<cdot>\<^sub>c\<close> 67)

interpretation "context": nonground_context where
  comp_subst = "(\<circ>\<^sub>s)" and id_subst = Var and subst_update = fun_upd and 
  subst_updates = subst_updates and apply_subst = apply_subst and term_subst = "(\<cdot>)" and
  term_vars = term.vars and compose_context = "(\<circ>\<^sub>c)" and term_from_ground = term.from_ground and
  term_to_ground = term.to_ground and map_context = map_args_actxt and
  to_ground_context_map = map_args_actxt and from_ground_context_map = map_args_actxt and
  context_to_set = set2_actxt and hole = \<box> and apply_context = ctxt_apply_term and 
  ground_hole = \<box> and compose_ground_context = "(\<circ>\<^sub>c)" and ground_context_map = map_args_actxt and
  ground_context_to_set = set2_actxt and apply_ground_context = apply_ground_context
proof unfold_locales
  fix c and t :: "('f, 'v) term"

  show "term.to_ground c\<langle>t\<rangle> = (context.to_ground c)\<langle>term.to_ground t\<rangle>\<^sub>G"
    by (induction c) (auto simp: context.to_ground_def)
next
  fix c\<^sub>G and t\<^sub>G :: "'f gterm"

  show "term.from_ground c\<^sub>G\<langle>t\<^sub>G\<rangle>\<^sub>G = (context.from_ground c\<^sub>G)\<langle>term.from_ground t\<^sub>G\<rangle>"
    by (induction c\<^sub>G) (auto simp: context.from_ground_def)
next
  fix c and t :: "('f, 'v) term"

  show "term.is_ground c\<langle>t\<rangle> \<longleftrightarrow> context.is_ground c \<and> term.is_ground t"
    by (induction c) (auto simp: context.vars_def)
next
  fix f :: "('f, 'v) term \<Rightarrow> ('f, 'v) term" and c c' :: "('f, 'v) context"

  show "map_args_actxt f (c \<circ>\<^sub>c c') = map_args_actxt f c \<circ>\<^sub>c map_args_actxt f c'"
    by (induction c) auto
next
  fix c c' :: "'f ground_context"

  show "context.from_ground (c \<circ>\<^sub>c c') = context.from_ground c \<circ>\<^sub>c context.from_ground c'"
    by (induction c) (auto simp: context.from_ground_def)
next
  fix c and t :: "('f, 'v) term"

  show "term.vars c\<langle>t\<rangle> = context.vars c \<union> term.vars t"
    unfolding context.vars_def
    by (induction c) auto
next
  fix c t and \<sigma> :: "('f, 'v) subst"

  show "c\<langle>t\<rangle> \<cdot> \<sigma> = (c \<cdot>\<^sub>c \<sigma>)\<langle>t \<cdot> \<sigma>\<rangle>"
    by (metis context.subst_def subst_apply_term_ctxt_apply_distrib)
next
  fix x and t :: "('f, 'v) term"

  show "x \<in> term.vars t \<longleftrightarrow> (\<exists>c. t = c\<langle>Var x\<rangle>)"
    by (metis Un_iff supteq_Var supteq_ctxtE term.set_intros(3) vars_term_ctxt_apply)
next
  fix c\<^sub>G t\<^sub>G and \<sigma> :: "('f, 'v) subst" and t :: "('f, 'v) term"
  assume t_\<sigma>: "t \<cdot> \<sigma> = c\<^sub>G\<langle>t\<^sub>G\<rangle>"

  {
    assume "\<nexists>c t'. t = c\<langle>t'\<rangle> \<and> t' \<cdot> \<sigma> = t\<^sub>G \<and> c \<cdot>\<^sub>c \<sigma> = c\<^sub>G"
    with t_\<sigma> have "\<exists>c c' x. t = c\<langle>Var x\<rangle> \<and> (c \<cdot>\<^sub>c \<sigma>) \<circ>\<^sub>c c' = c\<^sub>G"
    proof(induction t arbitrary: c\<^sub>G)
      case (Var x)

      show ?case
      proof (intro exI conjI)

        show "Var x = \<box>\<langle>Var x\<rangle>"
          by simp
      next

        show "(\<box> \<cdot>\<^sub>c \<sigma>) \<circ>\<^sub>c c\<^sub>G = c\<^sub>G"
          by (simp add: context.subst_def)
      qed
    next
      case (Fun f ts)

      have "c\<^sub>G \<noteq> \<box>"
        using Fun.prems(1, 2)
        by (metis actxt.simps(8) context.subst_def intp_actxt.simps(1))

      then obtain ts\<^sub>G\<^sub>1 c\<^sub>G' ts\<^sub>G\<^sub>2 where
        c\<^sub>G: "c\<^sub>G = More f ts\<^sub>G\<^sub>1 c\<^sub>G' ts\<^sub>G\<^sub>2"
        using Fun.prems
        by (cases c\<^sub>G) auto

      have "map (\<lambda>t. t \<cdot> \<sigma>) ts = ts\<^sub>G\<^sub>1 @ c\<^sub>G'\<langle>t\<^sub>G\<rangle> # ts\<^sub>G\<^sub>2"
        using Fun.prems(1) 
        unfolding c\<^sub>G
        by simp

      moreover then obtain ts\<^sub>1 t ts\<^sub>2 where
        ts: "ts = ts\<^sub>1 @ t # ts\<^sub>2" and
        ts\<^sub>1_\<gamma>: "map (\<lambda>t. t \<cdot> \<sigma>) ts\<^sub>1 = ts\<^sub>G\<^sub>1" and
        ts\<^sub>2_\<gamma>: "map (\<lambda>t. t \<cdot> \<sigma>) ts\<^sub>2 = ts\<^sub>G\<^sub>2"
        by (smt append_eq_map_conv map_eq_Cons_D)

      ultimately have t_\<gamma>: "t \<cdot> \<sigma> = c\<^sub>G'\<langle>t\<^sub>G\<rangle>"
        by simp

      obtain x c\<^sub>1 c\<^sub>G'' where "t = c\<^sub>1\<langle>Var x\<rangle>" and "c\<^sub>G' = (c\<^sub>1 \<cdot>\<^sub>c \<sigma>) \<circ>\<^sub>c c\<^sub>G''"
      proof -

        have "t \<in> set ts"
          by (simp add: ts)

        moreover have "\<nexists>c t'. t = c\<langle>t'\<rangle> \<and> t' \<cdot> \<sigma> = t\<^sub>G \<and> c \<cdot>\<^sub>c \<sigma> = c\<^sub>G'"
        proof(rule notI, elim exE conjE)
          fix c t'
          assume "t = c\<langle>t'\<rangle>" "t' \<cdot> \<sigma> = t\<^sub>G" "c \<cdot>\<^sub>c \<sigma> = c\<^sub>G'"

          moreover then have
            "Fun f ts = (More f ts\<^sub>1 c ts\<^sub>2)\<langle>t'\<rangle>"
            "(More f ts\<^sub>1 c ts\<^sub>2) \<cdot>\<^sub>c \<sigma> = c\<^sub>G"
            unfolding c\<^sub>G ts context.subst_def
            using ts\<^sub>1_\<gamma> ts\<^sub>2_\<gamma>
            by auto

          ultimately show False
            using Fun.prems(2) 
            by blast
        qed

        ultimately show ?thesis
          using Fun(1) t_\<gamma> that
          by blast
      qed

      moreover then have
        "Fun f ts = (More f ts\<^sub>1 c\<^sub>1 ts\<^sub>2)\<langle>Var x\<rangle>"
        "c\<^sub>G = (More f ts\<^sub>1 c\<^sub>1 ts\<^sub>2 \<cdot>\<^sub>c \<sigma>) \<circ>\<^sub>c c\<^sub>G''"
        using ts\<^sub>1_\<gamma> ts\<^sub>2_\<gamma>
        unfolding c\<^sub>G ts context.subst_def
        by auto

      ultimately show ?case
        using Fun.prems(1)
        by blast
    qed
  }

  then show "(\<exists>c t'. t = c\<langle>t'\<rangle> \<and> t' \<cdot> \<sigma> = t\<^sub>G \<and> c \<cdot>\<^sub>c \<sigma> = c\<^sub>G) \<or>
        (\<exists>c c\<^sub>G' x. t = c\<langle>Var x\<rangle> \<and> c\<^sub>G = (c \<cdot>\<^sub>c \<sigma>) \<circ>\<^sub>c c\<^sub>G')"
    by metis
next
  fix c and t :: "('f, 'v) term"
  assume "c\<langle>t\<rangle> = t"
  then show "c = \<box>"
    by (metis less_not_refl size_ne_ctxt)
qed auto

interpretation "term": occurences where
  comp_subst = "(\<circ>\<^sub>s)" and id_subst = Var and subst_update = fun_upd and 
  subst_updates = subst_updates and apply_subst = apply_subst and term_subst = "(\<cdot>)" and
  term_vars = term.vars and compose_context = "(\<circ>\<^sub>c)" and term_from_ground = term.from_ground and
  term_to_ground = term.to_ground and map_context = map_args_actxt and
  to_ground_context_map = map_args_actxt and from_ground_context_map = map_args_actxt and
  context_to_set = set2_actxt and hole = \<box> and apply_context = ctxt_apply_term and 
  ground_hole = \<box> and compose_ground_context = "(\<circ>\<^sub>c)" and ground_context_map = map_args_actxt and
  ground_context_to_set = set2_actxt and apply_ground_context = apply_ground_context and
  occurences = occurences
proof unfold_locales
  fix x c and t :: "('f, 'v) term"
  assume "term.is_ground t"

  then have "vars_term_ms t = {#}"
    by (induction t) auto

  then have "occurences t x = 0"
    by auto

  then show "occurences c\<langle>Var x\<rangle> x = Suc (occurences c\<langle>t\<rangle> x)"
    by (induction c) auto
next
  fix x and t :: "('f, 'v) term"

  show "x \<in> vars_term t \<longleftrightarrow> 0 < occurences t x"
    by auto
qed

end
