theory Entailment_Lifting
  imports Abstract_Substitution.Based_Substitution_Lifting
begin

locale entailment =
  based: based_substitution where base_subst = base_subst and vars = vars +
  base: grounding where subst = base_subst and vars = base_vars and to_ground = base_to_ground and
  from_ground = base_from_ground for
  vars :: "'expr \<Rightarrow> 'var set" and
  base_subst :: "'base \<Rightarrow> 'subst \<Rightarrow> 'base" and
  base_to_ground :: "'base \<Rightarrow> 'base\<^sub>G" and
  base_from_ground +
fixes 
  entails_def :: "'expr \<Rightarrow> bool" ("(\<Turnstile> _)" [50] 50) and 
  I ::  "('base\<^sub>G \<times> 'base\<^sub>G) set"
assumes
  congruence: "\<And>expr \<gamma> x update.
        based.base.is_ground update \<Longrightarrow>
        based.base.is_ground (x \<cdot>v \<gamma>) \<Longrightarrow>
        (base_to_ground (x \<cdot>v \<gamma>), base_to_ground update) \<in> I \<Longrightarrow>
        based.is_ground (expr \<cdot> \<gamma>) \<Longrightarrow>
        \<Turnstile> expr \<cdot> \<gamma>\<lbrakk>x := update\<rbrakk> \<Longrightarrow>
        \<Turnstile> expr \<cdot> \<gamma>"
begin

abbreviation entails where
  "entails \<equiv> entails_def"

end

locale symmetric_entailment = entailment +
  assumes sym: "sym I"
begin

lemma symmetric_congruence:
  assumes
    update_is_ground: "based.base.is_ground update" and
    var_grounding: "based.base.is_ground (x \<cdot>v \<gamma>)" and
    var_update: "(base_to_ground (x \<cdot>v \<gamma>), base_to_ground update) \<in> I" and
    expr_grounding: "based.is_ground (subst expr \<gamma>)"
  shows "\<Turnstile> expr \<cdot> \<gamma>\<lbrakk>x := update\<rbrakk> \<longleftrightarrow> \<Turnstile> expr \<cdot> \<gamma>"
proof (rule iffI)
  assume "\<Turnstile> expr \<cdot> subst_update \<gamma> x update"

  then show "\<Turnstile> expr \<cdot> \<gamma>"
    by(rule congruence[OF assms])
next
  assume "\<Turnstile> expr \<cdot> \<gamma>"
  then show "\<Turnstile> expr \<cdot> subst_update \<gamma> x update"
    using congruence[OF var_grounding, of x "(subst_update \<gamma> x update)" expr] assms
    by (metis based.ground_subst_update based.subst_eq based.subst_update sym symE)
qed

end

locale symmetric_base_entailment =
  base_substitution where subst = subst +
  grounding where subst = subst and to_ground = to_ground for
  subst :: "'base \<Rightarrow> 'subst \<Rightarrow> 'base"  (infixl "\<cdot>" 70) and
  to_ground :: "'base \<Rightarrow> 'base\<^sub>G" +
fixes I :: "('base\<^sub>G \<times> 'base\<^sub>G) set"
assumes
  sym: "sym I" and
  congruence: "\<And>expr expr' update \<gamma> x.
      is_ground update \<Longrightarrow>
      is_ground (x \<cdot>v \<gamma>) \<Longrightarrow>
      (to_ground (x \<cdot>v \<gamma>), to_ground update) \<in> I \<Longrightarrow>
      is_ground (expr \<cdot> \<gamma>) \<Longrightarrow>
      (to_ground (expr \<cdot> \<gamma>\<lbrakk>x := update\<rbrakk>), expr') \<in> I \<Longrightarrow>
      (to_ground (expr \<cdot> \<gamma>), expr') \<in> I"
begin

lemma symmetric_congruence:
  assumes
    update_is_ground: "is_ground update" and
    var_grounding: "is_ground (x \<cdot>v \<gamma>)" and
    expr_grounding: "is_ground (expr \<cdot> \<gamma>)" and
    var_update: "(to_ground (x \<cdot>v \<gamma>), to_ground update) \<in> I"
  shows "(to_ground (expr \<cdot> \<gamma>\<lbrakk>x := update\<rbrakk>), expr') \<in> I \<longleftrightarrow> (to_ground (expr \<cdot> \<gamma>), expr') \<in> I"
  using assms congruence[OF var_grounding, of x "\<gamma>\<lbrakk>x := update\<rbrakk>"] congruence
  by (smt (verit, del_insts) ground_subst_update sym subst_eq symE subst_update)

lemma simultaneous_congruence:
  assumes
    update_is_ground: "is_ground update" and
    var_grounding: "is_ground (x \<cdot>v \<gamma>)" and
    var_update: "(to_ground (x \<cdot>v \<gamma>), to_ground update) \<in> I" and
    expr_grounding: "is_ground (expr \<cdot> \<gamma>)" "is_ground (expr' \<cdot> \<gamma>)"
  shows
    "(to_ground (expr \<cdot> (\<gamma>\<lbrakk>x := update\<rbrakk>)), to_ground (expr' \<cdot> (\<gamma>\<lbrakk>x := update\<rbrakk>))) \<in> I \<longleftrightarrow>
        (to_ground (expr \<cdot> \<gamma>), to_ground (expr' \<cdot> \<gamma>))  \<in> I"
  using assms
  by (meson sym symD symmetric_congruence)

end

locale entailment_lifting =
  based_substitution_lifting where map = "map :: ('sub \<Rightarrow> 'sub) \<Rightarrow> 'expr \<Rightarrow> 'expr" +
  finite_variables_lifting +
  sub: symmetric_entailment where subst = sub_subst and vars = sub_vars and entails_def = sub_entails
  for sub_entails ("(\<Turnstile>\<^sub>s _)" [50] 50) +
  fixes
    is_negated :: "'expr \<Rightarrow> bool" and
    empty :: bool and
    connective :: "bool \<Rightarrow> bool \<Rightarrow> bool" and
    entails_def ("(\<Turnstile> _)" [50] 50)
  assumes
    is_negated_subst: "\<And>expr \<sigma>. is_negated (expr \<cdot> \<sigma>) \<longleftrightarrow> is_negated expr" and
    entails_def: "\<And>expr. \<Turnstile> expr \<longleftrightarrow>
      (if is_negated expr then Not else (\<lambda>x. x))
        (Finite_Set.fold connective empty (sub_entails  ` to_set expr))"
begin

sublocale symmetric_entailment where subst = subst and vars = vars and entails_def = entails_def
proof unfold_locales
  fix expr \<gamma> x update P
  assume
    "base.is_ground update"
    "base.is_ground (x \<cdot>v \<gamma>)"
    "is_ground (expr \<cdot> \<gamma>)"
    "(base_to_ground (x \<cdot>v \<gamma>), base_to_ground update) \<in> I"
    "\<Turnstile> expr \<cdot> \<gamma>\<lbrakk>x := update\<rbrakk>"

  moreover then have "\<forall>sub \<in> to_set expr. (\<Turnstile>\<^sub>s sub \<cdot>\<^sub>s \<gamma>\<lbrakk>x := update\<rbrakk>) \<longleftrightarrow> \<Turnstile>\<^sub>s sub \<cdot>\<^sub>s \<gamma>"
    using sub.symmetric_congruence to_set_is_ground_subst
    by blast

  ultimately show "\<Turnstile> expr \<cdot> \<gamma>"
    unfolding is_negated_subst entails_def
    by(auto simp: image_image subst_def)

qed (simp_all add: is_grounding_iff_vars_grounded sub.sym )

end

locale entailment_lifting_conj = entailment_lifting where
  connective = "(\<and>)" and empty = True

locale entailment_lifting_disj = entailment_lifting where
  connective = "(\<or>)" and empty = False

end
