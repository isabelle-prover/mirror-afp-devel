theory Nonground_Term_Order
  imports
    Nonground_Context
    Ground_Term_Order 
    Grounded_Order 
begin

locale ground_context_compatible_order =
  nonground_term_with_context +
  restricted_total_strict_order where restriction = "range term.from_ground" +
assumes ground_context_compatibility:
  "\<And>c t\<^sub>1 t\<^sub>2.
      term.is_ground t\<^sub>1 \<Longrightarrow>
      term.is_ground t\<^sub>2 \<Longrightarrow>
      context.is_ground c \<Longrightarrow>
      t\<^sub>1 \<prec> t\<^sub>2 \<Longrightarrow>
      c\<langle>t\<^sub>1\<rangle> \<prec> c\<langle>t\<^sub>2\<rangle>"
begin

sublocale context_compatible_restricted_order where
  restriction = "range term.from_ground" and context_restriction = "range context.from_ground" and
  restricted = term.is_ground and restricted_context = context.is_ground
  using ground_context_compatibility
  by unfold_locales
    (auto simp: term.is_ground_iff_range_from_ground context.is_ground_iff_range_from_ground)

end

locale ground_subterm_property =
  nonground_term_with_context +
  fixes R
  assumes ground_subterm_property:
    "\<And>t\<^sub>G c\<^sub>G. term.is_ground t\<^sub>G \<Longrightarrow> context.is_ground c\<^sub>G \<Longrightarrow> c\<^sub>G \<noteq> \<box> \<Longrightarrow> R t\<^sub>G c\<^sub>G\<langle>t\<^sub>G\<rangle>"

locale base_grounded_order =
  order: base_subst_update_stable_grounded_order  +
  order: grounded_restricted_total_strict_order +
  order: grounded_restricted_wellfounded_strict_order +
  order: ground_subst_stable_grounded_order +
  grounding

locale nonground_term_order =
  nonground_term_with_context where
  Var = "Var :: 'v \<Rightarrow> 't" and
  from_ground_context_map = "from_ground_context_map :: ('t\<^sub>G \<Rightarrow> 't) \<Rightarrow> 'c\<^sub>G \<Rightarrow> 'c" +
  order: restricted_wellfounded_strict_order where
  less = less\<^sub>t and restriction = "range term.from_ground" +
  order: ground_subst_stability where R = less\<^sub>t and comp_subst = "(\<odot>)" and subst = "(\<cdot>t)" and
  vars = term.vars and id_subst = Var and to_ground = term.to_ground and
  from_ground = "term.from_ground" +
  order: ground_context_compatible_order where less = less\<^sub>t +
  order: ground_subterm_property where R = less\<^sub>t
for less\<^sub>t
begin

interpretation term_order_notation .
              
sublocale base_grounded_order where
  subst = "(\<cdot>t)" and vars = term.vars and id_subst = Var and comp_subst = "(\<odot>)" and
  to_ground = term.to_ground and from_ground = "term.from_ground" and less = "(\<prec>\<^sub>t)"
proof unfold_locales
  fix update x \<gamma> t
  assume
    update_is_ground: "term.is_ground update" and
    update_less: "update \<prec>\<^sub>t \<gamma> x" and
    term_grounding: "term.is_ground (t \<cdot>t \<gamma>)" and
    x_in_t: "x \<in> term.vars t"

  from x_in_t term_grounding show "t \<cdot>t \<gamma>(x := update) \<prec>\<^sub>t t \<cdot>t \<gamma>"
  proof (induction "occurences t x - 1" arbitrary: t)
    case 0

    then have "occurences t x = 1"
      by (simp add: vars_occurences)

    then obtain c where t: "t = c\<langle>Var x\<rangle>" and "x \<notin> context.vars c"
      using one_occurence_obtain_context 
      by blast

    then have c_update: "c\<langle>Var x\<rangle> \<cdot>t \<gamma>(x := update) = (c \<cdot>t\<^sub>c \<gamma>)\<langle>update\<rangle>"
      by auto

    show ?case
      using 0(3) update_less update_is_ground
      unfolding t c_update
      by auto
  next
    case (Suc n)

    obtain c where t: "t = c\<langle>Var x\<rangle>"
      using Suc.prems(1) context.context_Var
      by blast

    let ?t' = "c\<langle>update\<rangle>"

    have "?t' \<cdot>t \<gamma>(x := update) \<prec>\<^sub>t ?t' \<cdot>t \<gamma>"
    proof (rule Suc.hyps(1))

      show "n = occurences c\<langle>update\<rangle> x - 1"
        using Suc.hyps(2) occurences t update_is_ground 
        by auto
    next

      have "occurences c\<langle>update\<rangle> x = Suc n"
        using Suc.hyps(2)
        unfolding t occurences[OF update_is_ground]
        by auto

      then show "x \<in> term.vars c\<langle>update\<rangle>"
        using vars_occurences
        by presburger
    next

      show "term.is_ground (c\<langle>update\<rangle> \<cdot>t \<gamma>)"
        using Suc.prems(2) update_is_ground
        unfolding t
        by fastforce
    qed

    moreover have "c\<langle>update\<rangle> \<cdot>t \<gamma>(x := update) = c\<langle>Var x\<rangle> \<cdot>t \<gamma>(x := update)"
      using update_is_ground
      by auto

    moreover have less: "c\<langle>update\<rangle> \<cdot>t \<gamma> \<prec>\<^sub>t c\<langle>Var x\<rangle> \<cdot>t \<gamma>"
      using Suc.prems(2) update_is_ground update_less
      unfolding t
      by auto

    ultimately show ?case
      unfolding t
      by auto
  qed
qed

(* TODO: Find way to not have this twice *)
notation order.less\<^sub>G (infix "\<prec>\<^sub>t\<^sub>G" 50)
notation order.less_eq\<^sub>G (infix "\<preceq>\<^sub>t\<^sub>G" 50)

sublocale restriction: ground_term_order where 
  less\<^sub>t = "(\<prec>\<^sub>t\<^sub>G)" and compose_context = compose_ground_context and
  apply_context = apply_ground_context and hole = ground_hole
proof unfold_locales
  fix c t t'
  assume "t \<prec>\<^sub>t\<^sub>G t'"

  then show "c\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t\<^sub>G c\<langle>t'\<rangle>\<^sub>G"
    using
      order.ground_context_compatibility[OF
        term.ground_is_ground term.ground_is_ground context.ground_is_ground]
    unfolding order.less\<^sub>G_def
    by simp
next
  fix t :: "'t\<^sub>G" and c :: "'c\<^sub>G"
  assume "c \<noteq> \<box>\<^sub>G"

  then show "t \<prec>\<^sub>t\<^sub>G c\<langle>t\<rangle>\<^sub>G"
    using order.ground_subterm_property[OF term.ground_is_ground context.ground_is_ground]
    unfolding order.less\<^sub>G_def
    by simp
qed

end

end
