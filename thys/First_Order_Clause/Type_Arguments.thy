theory Type_Arguments
  imports Polymorphic_Term
begin

abbreviation (input) type_arg_apply_subst where
  "type_arg_apply_subst x \<sigma> \<equiv> snd \<sigma> x"

abbreviation (input) type_arg_subst_update where
  "type_arg_subst_update \<sigma> x update \<equiv> (fst \<sigma>, (snd \<sigma>)(x:=update))"

abbreviation (input) type_arg_subst where
  "type_arg_subst t \<sigma> \<equiv> t \<cdot> snd \<sigma>"

interpretation type_arg: substitution where
  comp_subst = "(\<odot>)" and id_subst = id_subst and is_ground = term.is_ground and
  subst = type_arg_subst and vars = term.vars and apply_subst = type_arg_apply_subst
  by unfold_locales (auto simp add: compose_subst_def)

interpretation type_arg: nonground_term where
  comp_subst = "(\<odot>)" and id_subst = id_subst and apply_subst = type_arg_apply_subst and
  subst_update = type_arg_subst_update and term_vars = term.vars and term_subst = type_arg_subst and
  term_to_ground = term.to_ground and term_from_ground = term.from_ground and
  term_is_ground = term.is_ground
proof unfold_locales
  fix \<rho> :: "('f, 'v, 'tyf, 'tyv) poly_subst"
  assume "poly_term.is_renaming \<rho>"

  then show "inj (snd \<rho>) \<and> (\<forall>x. \<exists>x'. snd \<rho> x = snd id_subst x')"
    unfolding poly_term.is_renaming_def compose_subst_def
    using term.is_renaming_def term_is_renaming_iff
    by auto 
next
  fix \<rho> :: "('f, 'v, 'tyf, 'tyv) poly_subst" and t
  assume \<rho>: "poly_term.is_renaming \<rho>"

  then have snd_\<rho>: "term.is_renaming (snd \<rho>)"
    unfolding poly_term.is_renaming_def term.is_renaming_def compose_subst_def
    by auto

  have "type_arg.rename \<rho> = term.rename (snd \<rho>)"
    unfolding term.rename_def[OF snd_\<rho>] type_arg.rename_def[OF \<rho>]
    by simp

  then show "term.vars (t \<cdot> snd \<rho>) = type_arg.rename \<rho> ` term.vars t"
    using term.rename_variables[OF snd_\<rho>]
    by presburger
next
  fix us us' :: "('tyv \<times> ('tyf, 'tyv) term) list"

  define upd ::
    "('tyv \<times> ('tyf, 'tyv) term) \<Rightarrow>
     ('f, 'v, 'tyf, 'tyv) poly_subst \<Rightarrow>
     ('f, 'v, 'tyf, 'tyv) poly_subst" where
  "upd \<equiv> \<lambda>(x, b) \<sigma>. type_arg_subst_update \<sigma> x b" 

  have "fold upd us \<sigma> = (fst \<sigma>, fold (\<lambda>(x, b) \<sigma>. \<sigma>(x:= b)) us (snd \<sigma>))" for us \<sigma>
    by (induction us arbitrary: \<sigma>) (auto simp: upd_def)

  moreover have "snd (fold upd us \<sigma>) = fold (\<lambda>(x, b) \<sigma>. \<sigma>(x:= b)) us (snd \<sigma>)" for us \<sigma>
    by (induction us arbitrary: \<sigma>) (auto simp: upd_def)

  moreover assume "\<And>x. snd (fold upd us id_subst \<odot> fold upd us' id_subst) x = snd id_subst x"

  ultimately show "fold upd us id_subst \<odot> fold upd us' id_subst = id_subst"
    unfolding compose_subst_def
    by auto
next
  fix t XX and \<mu> :: "('f, 'v, 'tyf, 'tyv) poly_subst"
  assume is_imgu: "type_arg.is_imgu \<mu> XX" and "finite XX" "\<forall>X\<in>XX. finite X"

  moreover have "term.is_imgu (snd \<mu>) XX"
    using is_imgu
    unfolding 
      type_arg.is_imgu_def term.is_imgu_def 
      type_arg.is_unifier_set_def term.is_unifier_set_def
      type_arg.is_unifier_def term.is_unifier_def
      type_arg.subst_set_def term.subst_set_def
      compose_subst_def
    by (cases \<mu>) auto

  ultimately show "term.vars (t \<cdot> snd \<mu>) \<subseteq> term.vars t \<union> \<Union> (term.vars ` \<Union> XX)"
    using term.variables_in_base_imgu 
    by metis
qed (use term.all_subst_ident_iff_ground term.range_from_ground_iff_is_ground in
     \<open>auto simp: term.exists_ground term.exists_non_ident_subst compose_subst_def
       term.comp_subst_iff vars_term_subst\<close>)

interpretation type_args: term_based_lifting where
  comp_subst = "(\<odot>)" and id_subst = id_subst and apply_subst = type_arg_apply_subst and
  subst_update = type_arg_subst_update and sub_subst = type_arg_subst and sub_vars = term.vars and
  sub_to_ground = term.to_ground and sub_from_ground = term.from_ground and
  term_vars = term.vars and term_subst = type_arg_subst and term_to_ground = term.to_ground and
  term_from_ground = term.from_ground and term_is_ground = term.is_ground and
  sub_is_ground = term.is_ground and to_ground_map = map and ground_map = map and
  from_ground_map = map and map = map and to_set = set and to_set_ground = set
  by unfold_locales auto

end
