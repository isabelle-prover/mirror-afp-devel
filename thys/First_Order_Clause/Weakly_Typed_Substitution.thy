theory Weakly_Typed_Substitution
  imports Typed_Substitution_Lifting Weak_Typing
begin

locale weakly_welltyped_substitution =
  typed_substitution where welltyped = welltyped 
for 
  weakly_welltyped :: "('v \<Rightarrow> 'ty_base) \<Rightarrow> 'expr \<Rightarrow> bool" and 
  welltyped :: "('v \<Rightarrow> 'ty_base) \<Rightarrow> 'expr \<Rightarrow> 'ty \<Rightarrow> bool"  +
assumes 
  "\<And>\<V>. Weak_Typing.weakly_welltyped (welltyped \<V>) (weakly_welltyped \<V>)"
begin

sublocale weakly_welltyped where
  welltyped = "welltyped \<V>" and weakly_welltyped = "weakly_welltyped \<V>" for \<V>
  by (metis weakly_welltyped_substitution_axioms weakly_welltyped_substitution_axioms_def
     weakly_welltyped_substitution_def)

end

locale weakly_welltyped_unifier = weakly_welltyped_substitution +
fixes to_base_set
assumes
  is_unifier_weakly_welltyped: 
  "\<And>expr \<V> \<upsilon>. base.type_preserving_on (vars expr) \<V> \<upsilon> \<Longrightarrow> base.is_unifier \<upsilon> (to_base_set expr) \<Longrightarrow>
      weakly_welltyped \<V> expr"
begin

lemma is_unifier_set_weakly_welltyped [intro]:
  assumes 
    "base.type_preserving_on (vars expr) \<V> \<upsilon>" 
    "base.is_unifier_set \<upsilon> {to_base_set expr}"
  shows "weakly_welltyped \<V> expr"
  using is_unifier_weakly_welltyped assms
  unfolding base.is_unifier_set_def
  by auto

lemma is_imgu_weakly_welltyped [intro]:
  assumes "base.type_preserving_on (vars expr) \<V> \<mu>" "base.is_imgu \<mu> {to_base_set expr}"
  shows "weakly_welltyped \<V> expr"
  using is_unifier_set_weakly_welltyped assms
  unfolding base.is_imgu_def
  by auto

end

locale weakly_welltyped_subst_stability = weakly_welltyped_substitution +
  assumes 
    weakly_welltyped_subst_stability [simp]: 
    "\<And>expr \<V> \<sigma>. base.type_preserving_on (vars expr) \<V> \<sigma> \<Longrightarrow>
       weakly_welltyped \<V> (subst expr \<sigma>) \<longleftrightarrow> weakly_welltyped \<V> expr"

locale weakly_welltyped_renaming = weakly_welltyped_substitution +
  assumes
    weakly_welltyped_renaming [simp]: 
    "\<And>expr \<V> \<V>' \<rho>. is_renaming \<rho> \<Longrightarrow> \<forall>x\<in>vars expr. \<V> x = \<V>' (rename \<rho> x) \<Longrightarrow>
       weakly_welltyped \<V>' (expr \<cdot> \<rho>) \<longleftrightarrow> weakly_welltyped \<V> expr"

locale base_weakly_welltyped_substitution =
  typed_substitution_lifting where 
  sub_welltyped = base_welltyped and sub_subst = base_subst and sub_vars = base_vars and
  sub_is_ground = base_is_ground and base_welltyped = base_welltyped
for base_welltyped :: "('v \<Rightarrow> 'ty) \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" +
assumes "\<And>\<V>. weakly_welltyped_base (base_welltyped \<V>)"
begin

sublocale weakly_welltyped_base where sub_welltyped = "base_welltyped \<V>" for \<V> 
  by unfold_locales

end

locale base_weakly_welltyped_unifier =
  base_weakly_welltyped_substitution +
  typed_subst_stability_lifting where sub_subst = base_subst and sub_vars = base_vars and 
  sub_is_ground = base_is_ground and sub_welltyped = base_welltyped
begin

sublocale weakly_welltyped_unifier where 
  subst = subst and vars = vars and is_ground = is_ground and 
  welltyped = welltyped and weakly_welltyped = "weakly_welltyped" and 
  to_base_set = to_set
proof unfold_locales
  fix expr \<V> \<upsilon>

  assume 
    type_preserving_on: "sub.base.type_preserving_on (vars expr) \<V> \<upsilon>" and 
    unifier: "sub.is_unifier \<upsilon> (to_set expr)"

  show "weakly_welltyped \<V> expr"
    using sub.type_preserving_is_unifier[OF unifier] type_preserving_on
    unfolding vars_def weakly_welltyped_def
    by presburger
qed

end

locale base_weakly_welltyped_renaming =
  typed_renaming_lifting where sub_subst = base_subst and sub_vars = base_vars and 
  sub_is_ground = base_is_ground and
  sub_welltyped = "base_welltyped :: ('v \<Rightarrow> 'ty) \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" +
  base_weakly_welltyped_substitution
begin

sublocale weakly_welltyped_renaming where 
  subst = subst and vars = vars and is_ground = is_ground and 
  welltyped = welltyped and weakly_welltyped = "weakly_welltyped"
proof unfold_locales
  fix expr \<rho> and \<V> \<V>' :: "'v \<Rightarrow> 'ty"

  assume 
    \<rho>: "sub.is_renaming \<rho>" and 
    \<V>_\<V>': "\<forall>x\<in>vars expr. \<V> x = \<V>' (rename \<rho> x)"

  show "weakly_welltyped \<V>' (subst expr \<rho>) \<longleftrightarrow> weakly_welltyped \<V> expr"
  proof (cases "is_welltyped \<V> expr")
    case True

    then show ?thesis
      using \<V>_\<V>' \<rho>
      by auto
  next
   case False

   show ?thesis
   proof (rule iffI)
     assume "weakly_welltyped \<V> expr"

     then have "\<forall>base\<in>to_set expr. \<forall>\<tau>. \<not> base_welltyped \<V> base \<tau>"
       using all_sub_not_welltyped[OF False] 
       by argo

     then have "\<forall>base\<in>to_set expr. \<forall>\<tau>. \<not> base_welltyped \<V>' (base_subst base \<rho>) \<tau>"
       using \<V>_\<V>' \<rho> vars_def
       by auto

     then show "weakly_welltyped \<V>' (subst expr \<rho>)"
       unfolding weakly_welltyped_def to_set_image
       by blast
   next
     assume "weakly_welltyped \<V>' (subst expr \<rho>)"

     then have "\<forall>base\<in>to_set expr. \<forall>\<tau>. \<not> base_welltyped \<V>' (base_subst base \<rho>) \<tau>"
       using all_sub_not_welltyped False welltyped_renaming \<rho> \<V>_\<V>'
       by blast

     then show "weakly_welltyped \<V> expr"
       using sub.base.welltyped_renaming[OF \<rho>] \<V>_\<V>'
       unfolding weakly_welltyped_def vars_def
       by blast 
    qed
  qed
qed

end

locale base_weakly_welltyped_subst_stability =
  base_weakly_welltyped_substitution +
  typed_subst_stability_lifting where sub_subst = base_subst and sub_vars = base_vars and 
  sub_is_ground = base_is_ground and sub_welltyped = base_welltyped
begin

sublocale weakly_welltyped_subst_stability where 
  subst = subst and vars = vars and is_ground = is_ground and 
  welltyped = welltyped and weakly_welltyped = "weakly_welltyped"
proof unfold_locales
  fix expr \<V> \<sigma>
  assume type_preserving: "sub.base.type_preserving_on (vars expr) \<V> \<sigma>"
  
  show "weakly_welltyped \<V> (subst expr \<sigma>) \<longleftrightarrow> weakly_welltyped \<V> expr"
  proof (cases "is_welltyped \<V> expr")
    case True

    then show ?thesis 
      by (simp add: type_preserving weakly_welltyped_if_welltyped)
  next
    case False

    show ?thesis
    proof (rule iffI)
      assume "weakly_welltyped \<V> expr"

      then have "\<forall>base\<in>to_set expr. \<forall>\<tau>. \<not> base_welltyped \<V> base \<tau>"
        using all_sub_not_welltyped[OF False] 
        by argo

      then have "\<forall>base\<in>to_set expr. \<forall>\<tau>. \<not> base_welltyped \<V> (base_subst base \<sigma>) \<tau>"
        using type_preserving
        by (simp add: vars_def)

      moreover then have "\<forall>base\<in>to_set (subst expr \<sigma>). \<forall>\<tau>. \<not> base_welltyped \<V> base \<tau>"
        unfolding to_set_image
        by auto

      ultimately show "weakly_welltyped \<V> (subst expr \<sigma>)"
        unfolding weakly_welltyped_def to_set_image
        by auto
    next
      assume "weakly_welltyped \<V> (subst expr \<sigma>)"

      then have "\<forall>base\<in>to_set expr. \<forall>\<tau>. \<not> base_welltyped \<V> (base_subst base \<sigma>) \<tau>"
        using all_sub_not_welltyped type_preserving False
        by (metis subst_in_to_set_subst welltyped_subst_stability)

      then show "weakly_welltyped \<V> expr"
        using type_preserving
        unfolding vars_def weakly_welltyped_def
        by simp
    qed
  qed
qed

end

locale weakly_welltyped_substitution_lifting =
  sub: weakly_welltyped_substitution where 
  weakly_welltyped = sub_weakly_welltyped and subst = sub_subst and vars = sub_vars and
  is_ground = sub_is_ground and welltyped = sub_welltyped +

  typed_substitution_lifting
for
  sub_weakly_welltyped :: "('v \<Rightarrow> 'ty) \<Rightarrow> 'sub \<Rightarrow> bool"
begin

sublocale weakly_welltyped_lifting where 
  sub_weakly_welltyped = "sub_weakly_welltyped \<V>" and sub_welltyped = "sub_welltyped \<V>"
  by unfold_locales

end

locale weakly_welltyped_unifier_lifting =
  sub: weakly_welltyped_unifier where 
  to_base_set = sub_to_base_set and weakly_welltyped = sub_weakly_welltyped and
  subst = sub_subst and vars = sub_vars and is_ground = sub_is_ground and
  welltyped = sub_welltyped +

  weakly_welltyped_substitution_lifting +
  typed_subst_stability_lifting
for
  sub_to_base_set :: "'sub \<Rightarrow> 'base set"
begin

abbreviation to_base_set where
  "to_base_set expr \<equiv> \<Union>(sub_to_base_set ` to_set expr)"

sublocale weakly_welltyped_unifier where 
   subst = subst and vars = vars and is_ground = is_ground and welltyped = welltyped and
   weakly_welltyped = weakly_welltyped and to_base_set = to_base_set 
proof unfold_locales
  fix expr \<V> \<upsilon>

  assume 
    type_preserving: "sub.base.type_preserving_on (vars expr) \<V>  \<upsilon>" and 
    unifier: "sub.base.is_unifier \<upsilon> (to_base_set expr)"

  then show "weakly_welltyped \<V> expr"
    using sub.is_unifier_weakly_welltyped
    unfolding weakly_welltyped_def vars_def
    by (metis (mono_tags, opaque_lifting) UN_I sub.base.is_unifier_iff)
qed

end

locale weakly_welltyped_renaming_lifting =
  sub: weakly_welltyped_renaming where 
  weakly_welltyped = sub_weakly_welltyped and subst = sub_subst and vars = sub_vars and
  is_ground = sub_is_ground and welltyped = "sub_welltyped :: ('v \<Rightarrow> 'ty) \<Rightarrow> 'sub \<Rightarrow> 'ty' \<Rightarrow> bool" +

  weakly_welltyped_substitution_lifting +
  typed_renaming_lifting
begin

sublocale weakly_welltyped_renaming where
   subst = subst and vars = vars and is_ground = is_ground and welltyped = welltyped and
   weakly_welltyped = weakly_welltyped
proof unfold_locales
  fix expr \<rho> and \<V> \<V>' :: "'v \<Rightarrow> 'ty"
  assume \<rho>: "sub.is_renaming \<rho>" and "\<forall>x\<in>vars expr. \<V> x = \<V>' (rename \<rho> x)"

  then have "\<forall>sub \<in> to_set expr. \<forall>x\<in>sub_vars sub. \<V> x = \<V>' (rename \<rho> x)"
    using vars_def
    by force

  then have "\<forall>sub \<in> to_set expr. sub_weakly_welltyped \<V>' (sub \<cdot>\<^sub>s \<rho>) = sub_weakly_welltyped \<V> sub"
    using sub.weakly_welltyped_renaming \<rho>
    by simp

  then show "weakly_welltyped \<V>' (expr \<cdot> \<rho>) \<longleftrightarrow> weakly_welltyped \<V> expr"
    unfolding weakly_welltyped_def subst_def
    by auto
qed

end

locale weakly_welltyped_subst_stability_lifting =
  sub: weakly_welltyped_subst_stability where 
  weakly_welltyped = sub_weakly_welltyped and subst = sub_subst and vars = sub_vars and
  is_ground = sub_is_ground and welltyped = sub_welltyped +

  weakly_welltyped_substitution_lifting +
  typed_subst_stability_lifting
begin

sublocale weakly_welltyped_subst_stability where 
   subst = subst and vars = vars and is_ground = is_ground and welltyped = welltyped and
   weakly_welltyped = weakly_welltyped
proof unfold_locales
  fix expr \<V> \<sigma>
  assume "sub.base.type_preserving_on (vars expr) \<V> \<sigma>"

  then have "\<forall>sub \<in> to_set expr. sub.base.type_preserving_on (sub_vars sub) \<V> \<sigma>"
    using vars_def
    by force

  then have "\<forall>sub \<in> to_set expr. sub_weakly_welltyped \<V> (sub \<cdot>\<^sub>s \<sigma>) = sub_weakly_welltyped \<V> sub"
    using sub.weakly_welltyped_subst_stability
    by simp

  then show "weakly_welltyped \<V> (expr \<cdot> \<sigma>) \<longleftrightarrow> weakly_welltyped \<V> expr"
    unfolding weakly_welltyped_def subst_def
    by auto
qed

end

end
