section \<open> Scenes \<close>

theory Scenes
  imports Lens_Symmetric
begin

text \<open> Like lenses, scenes characterise a region of a source type. However, unlike lenses, scenes
  do not explicitly assign a view type to this region, and consequently they have just one type
  parameter. This means they can be more flexibly composed, and in particular it is possible to
  show they form nice algebraic structures in Isabelle/HOL. They are mainly of use in characterising
  sets of variables, where, of course, we do not care about the types of those variables and
  therefore representing them as lenses is inconvenient. \<close>

subsection \<open> Overriding Functions \<close>

text \<open> Overriding functions provide an abstract way of replacing a region of an existing source
  with the corresponding region of another source. \<close>

locale overrider =
  fixes F  :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infixl \<open>\<triangleright>\<close> 65)
  assumes 
    ovr_overshadow_left: "x \<triangleright> y \<triangleright> z = x \<triangleright> z" and
    ovr_overshadow_right: "x \<triangleright> (y \<triangleright> z) = x \<triangleright> z"
begin
  lemma ovr_assoc: "x \<triangleright> (y \<triangleright> z) = x \<triangleright> y \<triangleright> z"
    by (simp add: ovr_overshadow_left ovr_overshadow_right)
end

locale idem_overrider = overrider +
  assumes ovr_idem: "x \<triangleright> x = x"

declare overrider.ovr_overshadow_left [simp]
declare overrider.ovr_overshadow_right [simp]
declare idem_overrider.ovr_idem [simp]

subsection \<open> Scene Type \<close>

typedef 's scene = "{F :: 's \<Rightarrow> 's \<Rightarrow> 's. overrider F}"
  by (rule_tac x="\<lambda> x y. x" in exI, simp, unfold_locales, simp_all)

setup_lifting type_definition_scene

lift_definition idem_scene :: "'s scene \<Rightarrow> bool" is idem_overrider .

lift_definition region :: "'s scene \<Rightarrow> 's rel" 
is "\<lambda> F. {(s\<^sub>1, s\<^sub>2). (\<forall> s. F s s\<^sub>1 = F s s\<^sub>2)}" .

lift_definition coregion :: "'s scene \<Rightarrow> 's rel" 
is "\<lambda> F. {(s\<^sub>1, s\<^sub>2). (\<forall> s. F s\<^sub>1 s = F s\<^sub>2 s)}" .

lemma equiv_region: "equiv UNIV (region X)"
  apply (transfer)
  apply (rule equivI)
  subgoal
    by simp
  subgoal
    by (rule refl_onI) auto
  subgoal
    by (rule symI) auto
  subgoal
    by (rule transI) auto
  done

lemma equiv_coregion: "equiv UNIV (coregion X)"
  apply (transfer)
  apply (rule equivI)
  subgoal
    by simp
  subgoal
    by (rule refl_onI) auto
  subgoal
    by (rule symI) auto
  subgoal
    by (rule transI) auto
  done

lemma region_coregion_Id:
  "idem_scene X \<Longrightarrow> region X \<inter> coregion X = Id"
  by (transfer, auto, metis idem_overrider.ovr_idem)

lemma state_eq_iff: "idem_scene S \<Longrightarrow> x = y \<longleftrightarrow> (x, y) \<in> region S \<and> (x, y) \<in> coregion S"
  by (metis IntE IntI pair_in_Id_conv region_coregion_Id)

lift_definition scene_override :: "'a \<Rightarrow> 'a \<Rightarrow> ('a scene) \<Rightarrow> 'a" (\<open>_ \<oplus>\<^sub>S _ on _\<close> [95,0,96] 95)
is "\<lambda> s\<^sub>1 s\<^sub>2 F. F s\<^sub>1 s\<^sub>2" .

abbreviation (input) scene_copy :: "'a scene \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a)" (\<open>cp\<^bsub>_\<^esub>\<close>) where
"cp\<^bsub>A\<^esub> s \<equiv> (\<lambda> s'. s' \<oplus>\<^sub>S s on A)"

lemma scene_override_idem [simp]: "idem_scene X \<Longrightarrow> s \<oplus>\<^sub>S s on X = s"
  by (transfer, simp)

lemma scene_override_overshadow_left [simp]:
  "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on X \<oplus>\<^sub>S S\<^sub>3 on X = S\<^sub>1 \<oplus>\<^sub>S S\<^sub>3 on X"
  by (transfer, simp)

lemma scene_override_overshadow_right [simp]:
  "S\<^sub>1 \<oplus>\<^sub>S (S\<^sub>2 \<oplus>\<^sub>S S\<^sub>3 on X) on X = S\<^sub>1 \<oplus>\<^sub>S S\<^sub>3 on X"
  by (transfer, simp)

definition scene_equiv :: "'a \<Rightarrow> 'a \<Rightarrow> ('a scene) \<Rightarrow> bool" (\<open>_ \<approx>\<^sub>S _ on _\<close> [65,0,66] 65) where
[lens_defs]: "S\<^sub>1 \<approx>\<^sub>S S\<^sub>2 on X = (S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on X = S\<^sub>1)"

lemma scene_equiv_region: "idem_scene X \<Longrightarrow> region X = {(S\<^sub>1, S\<^sub>2). S\<^sub>1 \<approx>\<^sub>S S\<^sub>2 on X}"
  by (simp add: lens_defs, transfer, auto)
     (metis idem_overrider.ovr_idem, metis overrider.ovr_overshadow_right)

lift_definition scene_indep :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" (infix \<open>\<bowtie>\<^sub>S\<close> 50)
is "\<lambda> F G. (\<forall> s\<^sub>1 s\<^sub>2 s\<^sub>3. G (F s\<^sub>1 s\<^sub>2) s\<^sub>3 = F (G s\<^sub>1 s\<^sub>3) s\<^sub>2)" .

lemma scene_indep_override:
  "X \<bowtie>\<^sub>S Y = (\<forall> s\<^sub>1 s\<^sub>2 s\<^sub>3. s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on X \<oplus>\<^sub>S s\<^sub>3 on Y = s\<^sub>1 \<oplus>\<^sub>S s\<^sub>3 on Y \<oplus>\<^sub>S s\<^sub>2 on X)"
  by (transfer, auto)

lemma scene_indep_copy:
  "X \<bowtie>\<^sub>S Y = (\<forall> s\<^sub>1  s\<^sub>2. cp\<^bsub>X\<^esub> s\<^sub>1 \<circ> cp\<^bsub>Y\<^esub> s\<^sub>2 = cp\<^bsub>Y\<^esub> s\<^sub>2 \<circ> cp\<^bsub>X\<^esub> s\<^sub>1)"
  by (auto simp add: scene_indep_override comp_def fun_eq_iff)

lemma scene_indep_sym:
  "X \<bowtie>\<^sub>S Y \<Longrightarrow> Y \<bowtie>\<^sub>S X"
  by (transfer, auto)  

text \<open> Compatibility is a weaker notion than independence; the scenes can overlap but they must
  agree when they do. \<close>

lift_definition scene_compat :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" (infix \<open>##\<^sub>S\<close> 50)
is "\<lambda> F G. (\<forall> s\<^sub>1 s\<^sub>2. G (F s\<^sub>1 s\<^sub>2) s\<^sub>2 = F (G s\<^sub>1 s\<^sub>2) s\<^sub>2)" .

lemma scene_compat_copy:
  "X ##\<^sub>S Y = (\<forall> s. cp\<^bsub>X\<^esub> s \<circ> cp\<^bsub>Y\<^esub> s = cp\<^bsub>Y\<^esub> s \<circ> cp\<^bsub>X\<^esub> s)"
  by (transfer, auto simp add: fun_eq_iff)

lemma scene_indep_compat [simp]: "X \<bowtie>\<^sub>S Y \<Longrightarrow> X ##\<^sub>S Y"
  by (transfer, auto)

lemma scene_compat_refl: "X ##\<^sub>S X"
  by (transfer, simp)

lemma scene_compat_sym: "X ##\<^sub>S Y \<Longrightarrow> Y ##\<^sub>S X"
  by (transfer, simp)

lemma scene_override_commute_indep:
  assumes "X \<bowtie>\<^sub>S Y"
  shows "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on X \<oplus>\<^sub>S S\<^sub>3 on Y = S\<^sub>1 \<oplus>\<^sub>S S\<^sub>3 on Y \<oplus>\<^sub>S S\<^sub>2 on X"
  using assms
  by (transfer, auto)

instantiation scene :: (type) "{bot, top, uminus, sup, inf}"
begin
  lift_definition bot_scene    :: "'a scene" is "\<lambda> x y. x" by (unfold_locales, simp_all)
  lift_definition top_scene    :: "'a scene" is "\<lambda> x y. y" by (unfold_locales, simp_all)
  lift_definition uminus_scene :: "'a scene \<Rightarrow> 'a scene" is "\<lambda> F x y. F y x"
    by (unfold_locales, simp_all)
  text \<open> Scene union requires that the two scenes are at least compatible. If they are not, the
        result is the bottom scene. \<close>
  lift_definition sup_scene :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> 'a scene" 
    is "\<lambda> F G. if (\<forall> s\<^sub>1 s\<^sub>2. G (F s\<^sub>1 s\<^sub>2) s\<^sub>2 = F (G s\<^sub>1 s\<^sub>2) s\<^sub>2) then (\<lambda> s\<^sub>1 s\<^sub>2. G (F s\<^sub>1 s\<^sub>2) s\<^sub>2) else (\<lambda> s\<^sub>1 s\<^sub>2. s\<^sub>1)"
    by (unfold_locales, auto, metis overrider.ovr_overshadow_right)
  definition inf_scene :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> 'a scene" where
    [lens_defs]: "inf_scene X Y = - (sup (- X) (- Y))"
  instance ..
end

abbreviation union_scene :: "'s scene \<Rightarrow> 's scene \<Rightarrow> 's scene" (infixl \<open>\<squnion>\<^sub>S\<close> 65)
where "union_scene \<equiv> sup"

abbreviation inter_scene :: "'s scene \<Rightarrow> 's scene \<Rightarrow> 's scene" (infixl \<open>\<sqinter>\<^sub>S\<close> 70)
where "inter_scene \<equiv> inf"

abbreviation top_scene :: "'s scene" (\<open>\<top>\<^sub>S\<close>)
where "top_scene \<equiv> top"

abbreviation bot_scene :: "'s scene" (\<open>\<bottom>\<^sub>S\<close>)
where "bot_scene \<equiv> bot"

instantiation scene :: (type) "minus"
begin
  definition minus_scene :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> 'a scene" where
    "minus_scene A B = A \<sqinter>\<^sub>S (- B)"
instance ..
end

lemma bot_idem_scene [simp]: "idem_scene \<bottom>\<^sub>S"
  by (transfer, unfold_locales, simp_all)

lemma top_idem_scene [simp]: "idem_scene \<top>\<^sub>S"
  by (transfer, unfold_locales, simp_all)

lemma uminus_top_scene [simp]: "- \<top>\<^sub>S = \<bottom>\<^sub>S"
  by (transfer, simp)

lemma uminus_bot_scene [simp]: "- \<bottom>\<^sub>S = \<top>\<^sub>S"
  by (transfer, simp)

lemma uminus_scene_twice: "- (- (X :: 's scene)) = X"
  by (transfer, simp)

lemma scene_override_id [simp]: "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on \<top>\<^sub>S = S\<^sub>2"
  by (transfer, simp)

lemma scene_override_unit [simp]: "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on \<bottom>\<^sub>S = S\<^sub>1"
  by (transfer, simp)

lemma scene_override_commute: "S\<^sub>2 \<oplus>\<^sub>S S\<^sub>1 on (- X) = S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on X"
  by (transfer, simp)

lemma scene_union_incompat: "\<not> X ##\<^sub>S Y \<Longrightarrow> X \<squnion>\<^sub>S Y = \<bottom>\<^sub>S"
  by (transfer, auto)

lemma scene_override_union: "X ##\<^sub>S Y \<Longrightarrow> S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on (X \<squnion>\<^sub>S Y) = (S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on X) \<oplus>\<^sub>S S\<^sub>2 on Y"
  by (transfer, auto)

lemma scene_override_inter: "-X ##\<^sub>S -Y \<Longrightarrow> S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on (X \<sqinter>\<^sub>S Y) = S\<^sub>1 \<oplus>\<^sub>S S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on X on Y"
  by (simp add: inf_scene_def scene_override_commute scene_override_union)

lemma scene_equiv_bot [simp]: "a \<approx>\<^sub>S b on \<bottom>\<^sub>S"
  by (simp add: scene_equiv_def)

lemma scene_equiv_refl [simp]: "idem_scene a \<Longrightarrow> s \<approx>\<^sub>S s on a"
  by (simp add: scene_equiv_def)

lemma scene_equiv_sym [simp]: "idem_scene a \<Longrightarrow> s\<^sub>1 \<approx>\<^sub>S s\<^sub>2 on a \<Longrightarrow> s\<^sub>2 \<approx>\<^sub>S s\<^sub>1 on a"
  by (metis scene_equiv_def scene_override_idem scene_override_overshadow_right)

lemma scene_union_unit [simp]: "X \<squnion>\<^sub>S \<bottom>\<^sub>S = X" "\<bottom>\<^sub>S \<squnion>\<^sub>S X = X"
  by (transfer, simp)+

lemma scene_indep_bot [simp]: "X \<bowtie>\<^sub>S \<bottom>\<^sub>S"
  by (transfer, simp)

text \<open> A unitary scene admits only one element, and therefore top and bottom are the same. \<close>

lemma unit_scene_top_eq_bot: "(\<bottom>\<^sub>S :: unit scene) = \<top>\<^sub>S"
  by (transfer, simp)

lemma idem_scene_union [simp]: "\<lbrakk> idem_scene A; idem_scene B \<rbrakk> \<Longrightarrow> idem_scene (A \<squnion>\<^sub>S B)"
  apply (transfer, auto)
   apply (unfold_locales, auto)
   apply (metis overrider.ovr_overshadow_left)
  apply (metis overrider.ovr_overshadow_right)
  done

lemma scene_union_annhil: "idem_scene X \<Longrightarrow> X \<squnion>\<^sub>S \<top>\<^sub>S = \<top>\<^sub>S"
  by (transfer, simp)

lemma scene_union_pres_compat: "\<lbrakk> A ##\<^sub>S B; A ##\<^sub>S C \<rbrakk> \<Longrightarrow> A ##\<^sub>S (B \<squnion>\<^sub>S C)"
  by (transfer, auto)

lemma scene_indep_pres_compat: "\<lbrakk> A \<bowtie>\<^sub>S B; A \<bowtie>\<^sub>S C \<rbrakk> \<Longrightarrow> A \<bowtie>\<^sub>S (B \<squnion>\<^sub>S C)"
  by (transfer, auto)

lemma scene_indep_self_compl: "A \<bowtie>\<^sub>S -A"
  by (transfer, simp)

lemma scene_compat_self_compl: "A ##\<^sub>S -A"
  by (transfer, simp)

lemma scene_compat_bot [simp]: "a ##\<^sub>S \<bottom>\<^sub>S" "\<bottom>\<^sub>S ##\<^sub>S a"
  by (transfer, simp)+

lemma scene_compat_top [simp]: 
  "idem_scene a \<Longrightarrow> a ##\<^sub>S \<top>\<^sub>S" 
  "idem_scene a \<Longrightarrow> \<top>\<^sub>S ##\<^sub>S a"
  by (transfer, simp)+

lemma scene_union_assoc: 
  assumes "X ##\<^sub>S Y" "X ##\<^sub>S Z" "Y ##\<^sub>S Z"
  shows "X \<squnion>\<^sub>S (Y \<squnion>\<^sub>S Z) = (X \<squnion>\<^sub>S Y) \<squnion>\<^sub>S Z"
  using assms by (transfer, auto)

lemma scene_inter_indep:
  assumes "idem_scene X" "idem_scene Y" "X \<bowtie>\<^sub>S Y"
  shows "X \<sqinter>\<^sub>S Y = \<bottom>\<^sub>S"
  using assms
  unfolding lens_defs
  apply (transfer, auto)
   apply (metis (no_types, opaque_lifting) idem_overrider.ovr_idem overrider.ovr_assoc overrider.ovr_overshadow_right)
  apply (metis (no_types, opaque_lifting) idem_overrider.ovr_idem overrider.ovr_overshadow_right)
  done

lemma scene_union_indep_uniq:
  assumes "idem_scene X" "idem_scene Y" "idem_scene Z" "X \<bowtie>\<^sub>S Z" "Y \<bowtie>\<^sub>S Z" "X \<squnion>\<^sub>S Z = Y \<squnion>\<^sub>S Z"
  shows "X = Y"
  using assms apply (transfer, simp)
  by (metis (no_types, opaque_lifting) ext idem_overrider.ovr_idem overrider_def)

lemma scene_union_idem: "X \<squnion>\<^sub>S X = X"
  by (transfer, simp)

lemma scene_union_compl: "idem_scene X \<Longrightarrow> X \<squnion>\<^sub>S - X = \<top>\<^sub>S"
  by (transfer, auto)

lemma scene_inter_idem: "X \<sqinter>\<^sub>S X = X"
  by (simp add: inf_scene_def, transfer, auto)

lemma scene_union_commute: "X \<squnion>\<^sub>S Y = Y \<squnion>\<^sub>S X"
  by (transfer, auto)

lemma scene_inter_compl: "idem_scene X \<Longrightarrow> X \<sqinter>\<^sub>S - X = \<bottom>\<^sub>S"
  by (simp add: inf_scene_def, transfer, auto)

lemma scene_demorgan1: "-(X \<squnion>\<^sub>S Y) = -X \<sqinter>\<^sub>S -Y"
  by (simp add: inf_scene_def, transfer, auto)

lemma scene_demorgan2: "-(X \<sqinter>\<^sub>S Y) = -X \<squnion>\<^sub>S -Y"
  by (simp add: inf_scene_def, transfer, auto)

lemma scene_inter_commute: "X \<sqinter>\<^sub>S Y = Y \<sqinter>\<^sub>S X"
  by (simp add: inf_scene_def scene_union_commute)

lemma scene_union_inter_distrib:
  "\<lbrakk> idem_scene x; x \<bowtie>\<^sub>S y; x \<bowtie>\<^sub>S z; y ##\<^sub>S z \<rbrakk> \<Longrightarrow> x \<squnion>\<^sub>S y \<sqinter>\<^sub>S z = (x \<squnion>\<^sub>S y) \<sqinter>\<^sub>S (x \<squnion>\<^sub>S z)"
  apply (simp add: inf_scene_def, transfer)
  apply (auto simp add: fun_eq_iff)
     apply (unfold overrider_def idem_overrider_def idem_overrider_axioms_def)
     apply metis+
  done  

lemma idem_scene_uminus [simp]: "idem_scene X \<Longrightarrow> idem_scene (- X)"
  by (simp add: uminus_scene_def idem_scene_def Abs_scene_inverse idem_overrider_axioms_def idem_overrider_def overrider.intro)

lemma scene_minus_cancel: "\<lbrakk> a \<bowtie>\<^sub>S b; idem_scene a; idem_scene b \<rbrakk> \<Longrightarrow> a \<squnion>\<^sub>S (b \<sqinter>\<^sub>S - a) = a \<squnion>\<^sub>S b"
  apply (simp add: lens_defs, transfer, auto simp add: fun_eq_iff)
   apply (metis (mono_tags, lifting) overrider.ovr_overshadow_left)
  apply (metis (no_types, opaque_lifting) idem_overrider.ovr_idem overrider.ovr_overshadow_right)
  done

instantiation scene :: (type) ord
begin
  text \<open> $X$ is a subscene of $Y$ provided that overriding with first $Y$ and then $X$ can
         be rewritten using the complement of $X$. \<close>
  definition less_eq_scene :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" where
  [lens_defs]: "less_eq_scene X Y = (\<forall> s\<^sub>1 s\<^sub>2 s\<^sub>3. s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on Y \<oplus>\<^sub>S s\<^sub>3 on X = s\<^sub>1 \<oplus>\<^sub>S (s\<^sub>2 \<oplus>\<^sub>S s\<^sub>3 on X) on Y)"
  definition less_scene :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" where
  [lens_defs]: "less_scene x y = (x \<le> y \<and> \<not> y \<le> x)"
instance ..
end

abbreviation subscene :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" (infix \<open>\<subseteq>\<^sub>S\<close> 55)
where "subscene X Y \<equiv> X \<le> Y"

lemma subscene_refl: "X \<subseteq>\<^sub>S X"
  by (simp add: less_eq_scene_def)

lemma subscene_trans: "\<lbrakk> idem_scene Y; X \<subseteq>\<^sub>S Y; Y \<subseteq>\<^sub>S Z \<rbrakk> \<Longrightarrow> X \<subseteq>\<^sub>S Z"
  by (simp add: less_eq_scene_def, transfer, auto, metis (no_types, opaque_lifting) idem_overrider.ovr_idem)

lemma subscene_antisym: "\<lbrakk> idem_scene Y; X \<subseteq>\<^sub>S Y; Y \<subseteq>\<^sub>S X \<rbrakk> \<Longrightarrow> X = Y"
  apply (simp add: less_eq_scene_def, transfer, auto)
  apply (rule ext)
  apply (rule ext)
  apply (metis (full_types) idem_overrider.ovr_idem overrider.ovr_overshadow_left)
  done

lemma subscene_copy_def:
  assumes "idem_scene X" "idem_scene Y"
  shows "X \<subseteq>\<^sub>S Y = (\<forall> s\<^sub>1 s\<^sub>2. cp\<^bsub>X\<^esub> s\<^sub>1 \<circ> cp\<^bsub>Y\<^esub> s\<^sub>2 = cp\<^bsub>Y\<^esub> (cp\<^bsub>X\<^esub> s\<^sub>1 s\<^sub>2))"
  using assms
  by (simp add: less_eq_scene_def fun_eq_iff, transfer, auto)

lemma subscene_eliminate:
  "\<lbrakk> idem_scene Y; X \<le> Y \<rbrakk> \<Longrightarrow> s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on X \<oplus>\<^sub>S s\<^sub>3 on Y = s\<^sub>1 \<oplus>\<^sub>S s\<^sub>3 on Y"
  by (metis less_eq_scene_def scene_override_overshadow_left scene_override_idem)
    
lemma scene_bot_least: "\<bottom>\<^sub>S \<le> X"
  unfolding less_eq_scene_def by (transfer, auto)

lemma scene_top_greatest: "X \<le> \<top>\<^sub>S"
  unfolding less_eq_scene_def by (transfer, auto)

lemma scene_union_ub: "\<lbrakk> idem_scene Y; X \<bowtie>\<^sub>S Y \<rbrakk> \<Longrightarrow> X \<le> (X \<squnion>\<^sub>S Y)"
  by (simp add: less_eq_scene_def, transfer, auto)
     (metis (no_types, opaque_lifting) idem_overrider.ovr_idem overrider.ovr_overshadow_right)

lemma scene_union_lb: "\<lbrakk> a ##\<^sub>S b; a \<le> c; b \<le> c \<rbrakk> \<Longrightarrow> a \<squnion>\<^sub>S b \<le> c"
  by (simp add: less_eq_scene_def scene_override_union)

lemma scene_union_mono: "\<lbrakk> a \<subseteq>\<^sub>S c; b \<subseteq>\<^sub>S c; a ##\<^sub>S b; idem_scene a; idem_scene b \<rbrakk> \<Longrightarrow> a \<squnion>\<^sub>S b \<subseteq>\<^sub>S c"
  by (simp add: less_eq_scene_def, transfer, auto)

lemma scene_le_then_compat: "\<lbrakk> idem_scene X; idem_scene Y; X \<le> Y \<rbrakk> \<Longrightarrow> X ##\<^sub>S Y"
  unfolding less_eq_scene_def
  by (transfer, auto, metis (no_types, lifting) idem_overrider.ovr_idem overrider_def)

lemma indep_then_compl_in: "A \<bowtie>\<^sub>S B \<Longrightarrow> A \<le> -B"
  unfolding less_eq_scene_def by (transfer, simp)

lemma scene_le_iff_indep_inv:
  "A \<bowtie>\<^sub>S - B \<longleftrightarrow> A \<le> B"
  by (auto simp add: less_eq_scene_def scene_indep_override scene_override_commute)

lift_definition scene_comp :: "'a scene \<Rightarrow> ('a \<Longrightarrow> 'b) \<Rightarrow> 'b scene" (infixl \<open>;\<^sub>S\<close> 80)
is "\<lambda> S X a b. if (vwb_lens X) then put\<^bsub>X\<^esub> a (S (get\<^bsub>X\<^esub> a) (get\<^bsub>X\<^esub> b)) else a"
  by (unfold_locales, auto)

lemma scene_comp_idem [simp]: "idem_scene S \<Longrightarrow> idem_scene (S ;\<^sub>S X)"
  by (transfer, unfold_locales, simp_all)

lemma scene_comp_lens_indep [simp]: "X \<bowtie> Y \<Longrightarrow> (A ;\<^sub>S X) \<bowtie>\<^sub>S (A ;\<^sub>S Y)"
  by (transfer, auto simp add: lens_indep.lens_put_comm lens_indep.lens_put_irr2)

lemma scene_comp_indep [simp]: "A \<bowtie>\<^sub>S B \<Longrightarrow> (A ;\<^sub>S X) \<bowtie>\<^sub>S (B ;\<^sub>S X)"
  by (transfer, auto)

lemma scene_comp_bot [simp]: "\<bottom>\<^sub>S ;\<^sub>S x = \<bottom>\<^sub>S"
  by (transfer, auto)

lemma scene_comp_id_lens [simp]: "A ;\<^sub>S 1\<^sub>L = A"
  by (transfer, auto, simp add: id_lens_def)

lemma scene_union_comp_distl: "a ##\<^sub>S b \<Longrightarrow> (a \<squnion>\<^sub>S b) ;\<^sub>S x = (a ;\<^sub>S x) \<squnion>\<^sub>S (b ;\<^sub>S x)"
  by (transfer, auto simp add: fun_eq_iff)

lemma scene_comp_assoc: "\<lbrakk> vwb_lens X; vwb_lens Y \<rbrakk> \<Longrightarrow> A ;\<^sub>S X ;\<^sub>S Y = A ;\<^sub>S (X ;\<^sub>L Y)"
  by (transfer, auto simp add: lens_comp_def fun_eq_iff)
     (metis comp_vwb_lens lens_comp_def)

lift_definition scene_quotient :: "'b scene \<Rightarrow> ('a \<Longrightarrow> 'b) \<Rightarrow> 'a scene" (infixl \<open>'/\<^sub>S\<close> 80)
is "\<lambda> S X a b. if (vwb_lens X \<and> (\<forall>s\<^sub>1 s\<^sub>2 s\<^sub>3. S (s\<^sub>1 \<triangleleft>\<^bsub>X\<^esub> s\<^sub>2) s\<^sub>3 = s\<^sub>1 \<triangleleft>\<^bsub>X\<^esub> S s\<^sub>2 s\<^sub>3)) then get\<^bsub>X\<^esub> (S (create\<^bsub>X\<^esub> a) (create\<^bsub>X\<^esub> b)) else a"
  by (unfold_locales, auto simp add: lens_create_def lens_override_def)
     (metis (no_types, lifting) overrider.ovr_overshadow_right)

lemma scene_quotient_idem: "idem_scene S \<Longrightarrow> idem_scene (S /\<^sub>S X)"
  by (transfer, unfold_locales, auto simp add: lens_create_def lens_override_def)
     (metis (no_types, lifting) overrider.ovr_overshadow_right) 

lemma scene_quotient_indep: "A \<bowtie>\<^sub>S B \<Longrightarrow> (A /\<^sub>S X) \<bowtie>\<^sub>S (B /\<^sub>S X)"
  by (transfer, auto simp add: lens_create_def lens_override_def)

lemma scene_bot_quotient [simp]: "\<bottom>\<^sub>S /\<^sub>S X = \<bottom>\<^sub>S"
  by (transfer, auto)

lemma scene_comp_quotient: "vwb_lens X \<Longrightarrow> (A ;\<^sub>S X) /\<^sub>S X = A"
  by (transfer, auto simp add: fun_eq_iff lens_override_def)

lemma scene_quot_id_lens [simp]: "(A /\<^sub>S 1\<^sub>L) = A"
  by (transfer, simp, simp add: lens_defs)

subsection \<open> Linking Scenes and Lenses \<close>

text \<open> The following function extracts a scene from a very well behaved lens \<close>

lift_definition lens_scene :: "('v \<Longrightarrow> 's) \<Rightarrow> 's scene" (\<open>\<lbrakk>_\<rbrakk>\<^sub>\<sim>\<close>) is
"\<lambda> X s\<^sub>1 s\<^sub>2. if (mwb_lens X) then s\<^sub>1 \<oplus>\<^sub>L s\<^sub>2 on X else s\<^sub>1"
  by (unfold_locales, auto simp add: lens_override_def)

lemma vwb_impl_idem_scene [simp]:
  "vwb_lens X \<Longrightarrow> idem_scene \<lbrakk>X\<rbrakk>\<^sub>\<sim>"
  by (transfer, unfold_locales, auto simp add: lens_override_overshadow_left lens_override_overshadow_right)

lemma idem_scene_impl_vwb:
  "\<lbrakk> mwb_lens X; idem_scene \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<rbrakk> \<Longrightarrow> vwb_lens X"
  apply (cases "mwb_lens X")
   apply (transfer, unfold idem_overrider_def overrider_def, auto)
  apply (simp add: idem_overrider_axioms_def override_idem_implies_vwb)
  done

lemma lens_compat_scene: "\<lbrakk> mwb_lens X; mwb_lens Y \<rbrakk> \<Longrightarrow> X ##\<^sub>L Y \<longleftrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> ##\<^sub>S \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  by (auto simp add: lens_scene.rep_eq scene_compat.rep_eq lens_defs)

text \<open> Next we show some important congruence properties \<close>

lemma zero_lens_scene: "\<lbrakk>0\<^sub>L\<rbrakk>\<^sub>\<sim> = \<bottom>\<^sub>S"
  by (transfer, simp)

lemma one_lens_scene: "\<lbrakk>1\<^sub>L\<rbrakk>\<^sub>\<sim> = \<top>\<^sub>S"
  by (transfer, simp)

lemma scene_comp_top_scene [simp]: "vwb_lens x \<Longrightarrow> \<top>\<^sub>S ;\<^sub>S x = \<lbrakk>x\<rbrakk>\<^sub>\<sim>"
  by (transfer, simp add: fun_eq_iff lens_override_def)

lemma scene_comp_lens_scene_indep [simp]: "x \<bowtie> y \<Longrightarrow> \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<bowtie>\<^sub>S a ;\<^sub>S y"
  by (transfer, simp add: lens_indep.lens_put_comm lens_indep.lens_put_irr2 lens_override_def)

lemma lens_scene_override: 
  "mwb_lens X \<Longrightarrow> s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on \<lbrakk>X\<rbrakk>\<^sub>\<sim> = s\<^sub>1 \<oplus>\<^sub>L s\<^sub>2 on X"
  by (transfer, simp)

lemma lens_indep_scene:
  assumes "vwb_lens X" "vwb_lens Y"
  shows "(X \<bowtie> Y) \<longleftrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<bowtie>\<^sub>S \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  using assms
  by (auto, (simp add: scene_indep_override, transfer, simp add: lens_indep_override_def)+)

lemma lens_indep_impl_scene_indep [simp]:
  "(X \<bowtie> Y) \<Longrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<bowtie>\<^sub>S \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  by (transfer, auto simp add: lens_indep_comm lens_override_def)

lemma get_scene_override_indep: "\<lbrakk> vwb_lens x; \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<bowtie>\<^sub>S a \<rbrakk> \<Longrightarrow> get\<^bsub>x\<^esub> (s \<oplus>\<^sub>S s' on a) = get\<^bsub>x\<^esub> s"
proof -
  assume a1: "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<bowtie>\<^sub>S a"
  assume a2: "vwb_lens x"
  then have "\<forall>b ba bb. bb \<oplus>\<^sub>S b \<oplus>\<^sub>S ba on a on \<lbrakk>x\<rbrakk>\<^sub>\<sim> = bb \<oplus>\<^sub>S b on \<lbrakk>x\<rbrakk>\<^sub>\<sim>"
    using a1 by (metis idem_scene_uminus indep_then_compl_in scene_indep_sym scene_override_commute subscene_eliminate vwb_impl_idem_scene)
  then show ?thesis
    using a2 by (metis lens_override_def lens_scene_override mwb_lens_def vwb_lens_mwb weak_lens.put_get)
qed

lemma put_scene_override_indep:
  "\<lbrakk> vwb_lens x; \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<bowtie>\<^sub>S a \<rbrakk> \<Longrightarrow> put\<^bsub>x\<^esub> s v \<oplus>\<^sub>S s' on a = put\<^bsub>x\<^esub> (s \<oplus>\<^sub>S s' on a) v"
  by (transfer, auto)
     (metis lens_override_def mwb_lens_weak vwb_lens_mwb weak_lens.put_get)

lemma get_scene_override_le: "\<lbrakk> vwb_lens x; \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<le> a \<rbrakk> \<Longrightarrow> get\<^bsub>x\<^esub> (s \<oplus>\<^sub>S s' on a) = get\<^bsub>x\<^esub> s'"
  by (metis get_scene_override_indep scene_le_iff_indep_inv scene_override_commute)

lemma put_scene_override_le: "\<lbrakk> vwb_lens x; idem_scene a; \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<le> a \<rbrakk> \<Longrightarrow>  put\<^bsub>x\<^esub> s v \<oplus>\<^sub>S s' on a = s \<oplus>\<^sub>S s' on a"
  by (metis lens_override_idem lens_override_put_right_in lens_scene_override sublens_refl subscene_eliminate vwb_lens_mwb)

lemma put_scene_override_le_distrib: 
  "\<lbrakk> vwb_lens x; idem_scene A; \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<le> A \<rbrakk> \<Longrightarrow> put\<^bsub>x\<^esub> (s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on A) v = (put\<^bsub>x\<^esub> s\<^sub>1 v) \<oplus>\<^sub>S (put\<^bsub>x\<^esub> s\<^sub>2 v) on A"
  by (metis put_scene_override_indep put_scene_override_le scene_le_iff_indep_inv scene_override_commute)

lemma lens_plus_scene:
  "\<lbrakk> vwb_lens X; vwb_lens Y; X \<bowtie> Y \<rbrakk> \<Longrightarrow> \<lbrakk>X +\<^sub>L Y\<rbrakk>\<^sub>\<sim> = \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<squnion>\<^sub>S \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  by (transfer, auto simp add: lens_override_plus lens_indep_override_def lens_indep_overrideI)

lemma subscene_implies_sublens': "\<lbrakk> vwb_lens X; vwb_lens Y \<rbrakk> \<Longrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<le> \<lbrakk>Y\<rbrakk>\<^sub>\<sim> \<longleftrightarrow> X \<subseteq>\<^sub>L' Y"
  by (simp add: lens_defs, transfer, simp add: lens_override_def)

lemma sublens'_implies_subscene: "\<lbrakk> vwb_lens X; vwb_lens Y; X \<subseteq>\<^sub>L' Y \<rbrakk> \<Longrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<le> \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  by (simp add: lens_defs, auto simp add: lens_override_def lens_scene_override)

lemma sublens_iff_subscene:
  assumes "vwb_lens X" "vwb_lens Y"
  shows "X \<subseteq>\<^sub>L Y \<longleftrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<le> \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  by (simp add: assms sublens_iff_sublens' subscene_implies_sublens')

lemma lens_scene_indep_compl [simp]: 
  assumes "vwb_lens x" "vwb_lens y"
  shows "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<bowtie>\<^sub>S - \<lbrakk>y\<rbrakk>\<^sub>\<sim> \<longleftrightarrow> x \<subseteq>\<^sub>L y"
  by (simp add: assms scene_le_iff_indep_inv sublens_iff_subscene)

lemma lens_scene_comp: "\<lbrakk> vwb_lens X; vwb_lens Y \<rbrakk> \<Longrightarrow> \<lbrakk>X ;\<^sub>L Y\<rbrakk>\<^sub>\<sim> = \<lbrakk>X\<rbrakk>\<^sub>\<sim> ;\<^sub>S Y"
  by (transfer, simp add: fun_eq_iff comp_vwb_lens)
     (simp add: lens_comp_def lens_override_def)

lemma scene_comp_pres_indep: "\<lbrakk> idem_scene a; idem_scene b; a \<bowtie>\<^sub>S \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<rbrakk> \<Longrightarrow> a \<bowtie>\<^sub>S b ;\<^sub>S x"
  by (transfer, auto)
     (metis (no_types, opaque_lifting) lens_override_def lens_override_idem vwb_lens_def wb_lens_weak weak_lens.put_get)

lemma scene_comp_le: "A ;\<^sub>S X \<le> \<lbrakk>X\<rbrakk>\<^sub>\<sim>"
  unfolding less_eq_scene_def by (transfer, auto simp add: fun_eq_iff lens_override_def)

lemma scene_quotient_comp: "\<lbrakk> vwb_lens X; idem_scene A; A \<le> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<rbrakk> \<Longrightarrow> (A /\<^sub>S X) ;\<^sub>S X = A"
  unfolding less_eq_scene_def
proof (transfer, simp add: fun_eq_iff, safe)
  fix Xa :: "'a \<Longrightarrow> 'b" and Aa :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" and x :: 'b and xa :: 'b
  assume a1: "vwb_lens Xa"
  assume a2: "overrider Aa"
  assume a3: "idem_overrider Aa"
  assume a4: "\<forall>s\<^sub>1 s\<^sub>2 s\<^sub>3. Aa (s\<^sub>1 \<triangleleft>\<^bsub>Xa\<^esub> s\<^sub>2) s\<^sub>3 = s\<^sub>1 \<triangleleft>\<^bsub>Xa\<^esub> Aa s\<^sub>2 s\<^sub>3"
  have "\<And>b. Aa b b = b"
    using a3 by simp
  then have "Aa x (put\<^bsub>Xa\<^esub> src\<^bsub>Xa\<^esub> (get\<^bsub>Xa\<^esub> xa)) = Aa x xa"
    by (metis a2 a4 lens_override_def overrider.ovr_overshadow_right)
  then show "put\<^bsub>Xa\<^esub> x (get\<^bsub>Xa\<^esub> (Aa (create\<^bsub>Xa\<^esub> (get\<^bsub>Xa\<^esub> x)) (create\<^bsub>Xa\<^esub> (get\<^bsub>Xa\<^esub> xa)))) = Aa x xa"
    using a4 a1 by (metis lens_create_def lens_override_def vwb_lens_def wb_lens.get_put wb_lens_weak weak_lens.put_get)
qed

lemma lens_scene_quotient: "\<lbrakk> vwb_lens Y; X \<subseteq>\<^sub>L Y \<rbrakk> \<Longrightarrow> \<lbrakk>X /\<^sub>L Y\<rbrakk>\<^sub>\<sim> = \<lbrakk>X\<rbrakk>\<^sub>\<sim> /\<^sub>S Y"
  by (metis lens_quotient_comp lens_quotient_vwb lens_scene_comp scene_comp_quotient sublens_pres_vwb vwb_lens_def wb_lens_weak)

lemma scene_union_quotient: "\<lbrakk> A ##\<^sub>S B; A \<le> \<lbrakk>X\<rbrakk>\<^sub>\<sim>; B \<le> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<rbrakk> \<Longrightarrow> (A \<squnion>\<^sub>S B) /\<^sub>S X = (A /\<^sub>S X) \<squnion>\<^sub>S (B /\<^sub>S X)"
  unfolding less_eq_scene_def
  by (case_tac "vwb_lens X"; transfer, auto simp add: lens_create_def lens_override_def)

text \<open> Equality on scenes is sound and complete with respect to lens equivalence. \<close>

lemma lens_equiv_scene:
  assumes "vwb_lens X" "vwb_lens Y"
  shows "X \<approx>\<^sub>L Y \<longleftrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> = \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
proof
  assume a: "X \<approx>\<^sub>L Y"
  show "\<lbrakk>X\<rbrakk>\<^sub>\<sim> = \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
    by (meson a assms lens_equiv_def sublens_iff_subscene subscene_antisym vwb_impl_idem_scene)
next
  assume b: "\<lbrakk>X\<rbrakk>\<^sub>\<sim> = \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  show "X \<approx>\<^sub>L Y"
    by (simp add: assms b lens_equiv_def sublens_iff_subscene subscene_refl)
qed

lemma lens_scene_top_iff_bij_lens: "mwb_lens x \<Longrightarrow> \<lbrakk>x\<rbrakk>\<^sub>\<sim> = \<top>\<^sub>S \<longleftrightarrow> bij_lens x"
  apply (transfer)
  apply (auto simp add: fun_eq_iff lens_override_def)
  apply (unfold_locales)
   apply auto
  done

subsection \<open> Function Domain Scene \<close>

lift_definition fun_dom_scene :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::two) scene" (\<open>fds\<close>) is
"\<lambda> A f g. override_on f g A" by (unfold_locales, simp_all add: override_on_def fun_eq_iff)

lemma fun_dom_scene_empty: "fds({}) = \<bottom>\<^sub>S"
  by (transfer, simp)

lemma fun_dom_scene_union: "fds(A \<union> B) = fds(A) \<squnion>\<^sub>S fds(B)"
  by (transfer, auto simp add: fun_eq_iff override_on_def)

lemma fun_dom_scene_compl: "fds(- A) = - fds(A)"
  by (transfer, auto simp add: fun_eq_iff override_on_def)

lemma fun_dom_scene_inter: "fds(A \<inter> B) = fds(A) \<sqinter>\<^sub>S fds(B)"
  by (simp add: inf_scene_def fun_dom_scene_union[THEN sym] fun_dom_scene_compl[THEN sym])

lemma fun_dom_scene_UNIV: "fds(UNIV) = \<top>\<^sub>S"
  by (transfer, auto simp add: fun_eq_iff override_on_def)

lemma fun_dom_scene_indep [simp]:   
  "fds(A) \<bowtie>\<^sub>S fds(B) \<longleftrightarrow> A \<inter> B = {}"
  by (transfer, auto simp add: override_on_def fun_eq_iff, meson two_diff)

lemma fun_dom_scene_always_compat [simp]: "fds(A) ##\<^sub>S fds(B)"
  by (transfer, simp add: override_on_def fun_eq_iff)

lemma fun_dom_scene_le [simp]: "fds(A) \<subseteq>\<^sub>S fds(B) \<longleftrightarrow> A \<subseteq> B"
  unfolding less_eq_scene_def
  by (transfer, auto simp add: override_on_def fun_eq_iff, meson two_diff)

text \<open> Hide implementation details for scenes \<close>  

lifting_update scene.lifting
lifting_forget scene.lifting

end