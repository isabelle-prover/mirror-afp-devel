theory Ground_Superposition_Compatibility
  imports
    Abstract_Substitution.Noop_Substitution
    Ground_Superposition
    Untyped_Superposition
begin

(* TODO: Create the same for ordered resolution *)

locale noop_lifting = term_based_lifting where
  comp_subst = noop_comp_subst and id_subst = noop_id_subst and term_vars = noop_vars and
  term_is_ground = noop_is_ground and subst_update = noop_subst_update and
  apply_subst = noop_apply_subst and term_subst = noop_subst and
  subst_updates = noop_subst_updates and term_to_ground = id and
  term_from_ground = id and to_ground_map = map and from_ground_map = map and
  ground_map = map and to_set_ground = to_set
begin

(* TODO: *)
lemma noop_is_ground [simp]: "is_ground expr"
  unfolding is_ground_def
  using sub.exists_nonground_iff_base_exists_nonground
  by auto

lemma noop_vars [simp]: "vars expr = {}"
  using no_vars_if_is_ground
  by force

end

context nonground_clause
begin

sublocale atom.noop: noop_lifting where
  sub_vars = noop_vars and sub_subst = noop_subst and map = map_uprod and
  to_set = set_uprod and sub_to_ground = id and sub_from_ground = id and 
  sub_is_ground = noop_is_ground
  using unit.neutral_is_right_invertible
  by unfold_locales (auto simp: abstract_substitution_ops.is_ground_subst_def)

sublocale literal.noop: noop_lifting where
  sub_vars = atom.noop.vars and sub_subst = atom.noop.subst and map = map_literal and
  to_set = set_literal and sub_to_ground = id and sub_from_ground = id and
  sub_is_ground = atom.noop.is_ground
  by unfold_locales (use atom.exists_nonground_iff_sub_exists_nonground in auto)

sublocale clause.noop: noop_lifting where
  sub_vars = literal.noop.vars and sub_subst = literal.noop.subst and map = image_mset and
  to_set = set_mset and sub_to_ground = id and sub_from_ground = id  and
  sub_is_ground = literal.noop.is_ground
  by unfold_locales (use literal.exists_nonground_iff_sub_exists_nonground in auto)

end

context nonground_term_with_context
begin


sublocale context.noop: noop_lifting where
  sub_vars = noop_vars and  sub_subst = noop_subst and map = map_context and
  to_set = context_to_set and sub_to_ground = id and sub_from_ground = id and
  sub_is_ground = noop_is_ground
  using unit.neutral_is_right_invertible
  by unfold_locales (auto simp: abstract_substitution_ops.is_ground_subst_def)

end

(* TODO: Instantiate *)
locale ground_superposition_compatibility = untyped_superposition_calculus where
  comp_subst = noop_comp_subst and id_subst = noop_id_subst and term_vars = noop_vars and
  subst_update = noop_subst_update and apply_subst = noop_apply_subst and
  term_subst = noop_subst and subst_updates = noop_subst_updates and term_to_ground = id and
  term_from_ground = id and ground_hole = hole and compose_ground_context = compose_context and
  from_ground_context_map = map_context and to_ground_context_map = map_context and
  ground_context_map = map_context and ground_context_to_set = context_to_set and
  apply_ground_context = apply_context and occurences = "\<lambda>_ _. 0" and 
  term_is_ground = noop_is_ground
begin

interpretation grounded: ground_superposition_calculus 
proof unfold_locales

  show "wfp (\<prec>\<^sub>t)"
    using term.order.wfp
    by simp
next

  show "totalp (\<prec>\<^sub>t)"
    using term.order.totalp
    by simp
next
  fix t c
  assume "c \<noteq> \<box>"

  then show "t \<prec>\<^sub>t c\<langle>t\<rangle>"
    by (metis id_apply term.order.less\<^sub>r_def term.restriction.subterm_property)
qed simp

lemma eq_resolution_compatibility: "eq_resolution D C \<longleftrightarrow> grounded.eq_resolution D C"
proof (rule iffI)
  assume "grounded.eq_resolution D C"

  then show "eq_resolution D C"
  proof(cases rule: grounded.eq_resolution.cases)
    case grounded_eq_resolutionI: (eq_resolutionI l D' t)

    show ?thesis
    proof (intro eq_resolutionI; (rule grounded_eq_resolutionI)?)

      show "term.noop.is_imgu noop_id_subst {{t, t}}"
        using term.is_imgu_id_subst_empty
        by auto
    next

      show "select D = {#} \<Longrightarrow> is_maximal (l \<cdot>l noop_id_subst) (D \<cdot> noop_id_subst)"
        using grounded_eq_resolutionI(3) is_maximal_not_empty 
        by auto
    next

      show "select D \<noteq> {#} \<Longrightarrow> is_maximal (l \<cdot>l noop_id_subst) (select D \<cdot> noop_id_subst)"
        using grounded_eq_resolutionI(3)
        by simp
    next

      show "C = D' \<cdot> noop_id_subst"
        using grounded_eq_resolutionI(4) 
        by simp
    qed
  qed
next
  assume "eq_resolution D C"

  then show "grounded.eq_resolution D C"
  proof(cases rule: eq_resolution.cases)
    case (eq_resolutionI \<mu> t t' l D')

    show ?thesis
    proof (intro grounded.eq_resolutionI; (rule eq_resolutionI)?)

      show "D = add_mset l (D' \<cdot> \<mu>)"
        by (simp add: eq_resolutionI(4))
    next

      show "l = t !\<approx> t"
        using eq_resolutionI(1,5)
        unfolding term.noop.is_imgu_def
        by auto
    next

      show "select D = {#} \<and> is_maximal l D \<or> is_maximal l (select D)"
        using eq_resolutionI(2, 3)
        by fastforce
    qed
  qed
qed

lemma eq_factoring_compatibility: "eq_factoring D C \<longleftrightarrow> grounded.eq_factoring D C"
proof (rule iffI)
  assume "grounded.eq_factoring D C"

  then show "eq_factoring D C"
  proof(cases rule: grounded.eq_factoring.cases)
    case grounded_eq_factoringI: (eq_factoringI l\<^sub>1 l\<^sub>2 D' t t' t'')

    show ?thesis
    proof (intro eq_factoringI[where l\<^sub>1 = l\<^sub>1 and l\<^sub>2 = l\<^sub>2]; (rule grounded_eq_factoringI)?)

      show "is_maximal (l\<^sub>1 \<cdot>l noop_id_subst) (D \<cdot> noop_id_subst)"
        by (simp add: grounded_eq_factoringI(5))
    next

      show "\<not> noop_subst t noop_id_subst \<preceq>\<^sub>t noop_subst t' noop_id_subst"
        using grounded_eq_factoringI(6)
        by force
    next

      show "term.noop.is_imgu noop_id_subst {{t, t}}"
        using unit.noop.is_imgu_id_subst_empty 
        by simp
    next

      show "C = add_mset (t \<approx> t'') (add_mset (t' !\<approx> t'') D') \<cdot> noop_id_subst"
        using grounded_eq_factoringI(7)
        by simp
    qed
  qed
next
  assume "eq_factoring D C"

  then show "grounded.eq_factoring D C"
  proof (cases rule: eq_factoring.cases)
    case (eq_factoringI l\<^sub>1 \<mu> t\<^sub>1 t\<^sub>1' t\<^sub>2 l\<^sub>2 D' t\<^sub>2')

    show ?thesis
    proof (intro grounded.eq_factoringI; (rule eq_factoringI(1, 5))?)

      show "is_maximal l\<^sub>1 D"
        using eq_factoringI(2)
        by auto
    next

      show "t\<^sub>1' \<prec>\<^sub>t t\<^sub>1"
        using eq_factoringI(3) 
        by auto
    next

      show "C = add_mset (t\<^sub>1' !\<approx> t\<^sub>2') (add_mset (t\<^sub>1 \<approx> t\<^sub>2') D')"
        by (simp add: local.eq_factoringI(8))
    next

      show "l\<^sub>1 = t\<^sub>1 \<approx> t\<^sub>1'"
        using eq_factoringI(6) . 
    next

      show "l\<^sub>2 = t\<^sub>1 \<approx> t\<^sub>2'"
        using eq_factoringI(4,7) term.subst_imgu_eq_subst_imgu 
        by auto
    qed
  qed
qed



lemma superposition_compatibility: "superposition D E C \<longleftrightarrow> grounded.superposition D E C"
proof (rule iffI)
  assume "grounded.superposition D E C"

  then show "superposition D E C"
  proof (cases rule: grounded.superposition.cases)
    case grounded_superpositionI: (superpositionI l\<^sub>1 E' l\<^sub>2 D' \<P> c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2')

    show ?thesis
    proof (intro superpositionI; (rule grounded_superpositionI(4))?)

      show "term.is_renaming noop_id_subst" "term.is_renaming noop_id_subst"
        using unit.is_right_invertible_def
        by simp_all
    next

      show "term.noop.is_imgu noop_id_subst
             {{noop_subst t\<^sub>1 noop_id_subst, noop_subst t\<^sub>1 noop_id_subst}}"
        using term.is_imgu_id_subst_empty
        by simp
    next

      show "\<not> E \<cdot> noop_comp_subst noop_id_subst noop_id_subst \<preceq>\<^sub>c
            D \<cdot> noop_comp_subst noop_id_subst noop_id_subst"
        using grounded_superpositionI(3)
        by auto
    next

      show "\<not> noop_subst c\<^sub>1\<langle>t\<^sub>1\<rangle> (noop_comp_subst noop_id_subst noop_id_subst) \<preceq>\<^sub>t
            noop_subst t\<^sub>1' (noop_comp_subst noop_id_subst noop_id_subst)"
        using grounded_superpositionI(7)
        by auto
    next

      show "\<not> noop_subst t\<^sub>1 (noop_comp_subst noop_id_subst noop_id_subst) \<preceq>\<^sub>t
              noop_subst t\<^sub>2' (noop_comp_subst noop_id_subst noop_id_subst)"
        using grounded_superpositionI(8)
        by auto
    next

      show "\<P> = Pos \<Longrightarrow> select E = {#}"
        using grounded_superpositionI(9)
        by auto
    next

      show "\<P> = Pos \<Longrightarrow>
            is_strictly_maximal 
              (l\<^sub>1 \<cdot>l noop_comp_subst noop_id_subst noop_id_subst)
              (E \<cdot> noop_comp_subst noop_id_subst noop_id_subst)"
        using grounded_superpositionI(9)
        by auto
    next
      assume "select E = {#}"

      then show "is_maximal
                  (l\<^sub>1 \<cdot>l noop_comp_subst noop_id_subst noop_id_subst)
                  (E \<cdot> noop_comp_subst noop_id_subst noop_id_subst)"
        using grounded_superpositionI(9) is_maximal_not_empty
        by auto
    next
      assume "select E  \<noteq> {#}"

      then show "is_maximal 
                  (l\<^sub>1 \<cdot>l noop_comp_subst noop_id_subst noop_id_subst)
                  (select E \<cdot> noop_comp_subst noop_id_subst noop_id_subst)"
        using grounded_superpositionI(9)
        by auto
    next

      show "select D = {#}"
        by (simp add: grounded_superpositionI(10))
    next

      show "is_strictly_maximal
              (l\<^sub>2 \<cdot>l noop_comp_subst noop_id_subst noop_id_subst)
              (D \<cdot> noop_comp_subst noop_id_subst noop_id_subst)"
        by (simp add: grounded_superpositionI(11))
    next


      show "E = add_mset l\<^sub>1 E'" "D = add_mset l\<^sub>2 D'" "l\<^sub>1 = \<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1')" "l\<^sub>2 = t\<^sub>1 \<approx> t\<^sub>2'"
        using grounded_superpositionI(1, 2, 5, 6) .
    next

      show "C = add_mset
                  (\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c noop_id_subst)\<langle>noop_subst t\<^sub>2' noop_id_subst\<rangle> 
                            (noop_subst t\<^sub>1' noop_id_subst)))
                  (E' \<cdot> noop_id_subst + D' \<cdot> noop_id_subst) \<cdot> noop_id_subst"
        using grounded_superpositionI(12) 
        by auto
    qed auto
  qed
next
  assume "superposition D E C"

  then show "grounded.superposition D E C"
  proof (cases rule: superposition.cases)
    case (superpositionI \<P> \<rho>\<^sub>1 \<rho>\<^sub>2 t\<^sub>1 \<mu> t\<^sub>2 c\<^sub>1 t\<^sub>1' t\<^sub>2' l\<^sub>1 l\<^sub>2 E' D')

    have t\<^sub>1_t\<^sub>2: "t\<^sub>1 = t\<^sub>2"
      using superpositionI(6) term.subst_imgu_eq_subst_imgu
      by simp

    show ?thesis
    proof (intro grounded.superpositionI)
      show "\<P> \<in> {Pos, Neg}"
        using superpositionI(1) 
        by blast
    next

      show "E = add_mset l\<^sub>1 E'" "D = add_mset l\<^sub>2 D'" "l\<^sub>1 = \<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1')"
        using superpositionI(16-18) .
    next

      show "l\<^sub>2 = t\<^sub>1 \<approx> t\<^sub>2'"
        using  superpositionI(19)
        unfolding t\<^sub>1_t\<^sub>2 .
    next

      show "D \<prec>\<^sub>c E"
        using superpositionI(7)
        by auto
    next

      show "t\<^sub>1' \<prec>\<^sub>t c\<^sub>1\<langle>t\<^sub>1\<rangle>"
        using superpositionI(8)
        by auto
    next

      show "t\<^sub>2' \<prec>\<^sub>t t\<^sub>1"
        using superpositionI(9) t\<^sub>1_t\<^sub>2
        by fastforce
    next

      show "\<P> = Pos \<and> select E = {#} \<and> is_strictly_maximal l\<^sub>1 E \<or>
            \<P> = Neg \<and> (select E = {#} \<and> is_maximal l\<^sub>1 E \<or> is_maximal l\<^sub>1 (select E))"
        using superpositionI(1, 10-13)
        by auto
    next

      show "select D = {#}"
        by (simp add: superpositionI(14))
    next

      show "is_strictly_maximal l\<^sub>2 D"
        using superpositionI(15)
        by auto
    next

      show "C = add_mset (\<P> (Upair c\<^sub>1\<langle>t\<^sub>2'\<rangle> t\<^sub>1')) (E' + D')"
        by (simp add: superpositionI(20))
    qed
  qed
qed

end

end
