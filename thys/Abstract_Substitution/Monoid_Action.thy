theory Monoid_Action
  imports Main
begin

section \<open>General Results on Groups\<close>

lemma (in monoid) right_inverse_idem:
  fixes inv
  assumes right_inverse:  "\<And>a. a \<^bold>* inv a = \<^bold>1"
  shows "\<And>a. inv (inv a) = a"
    by (metis assoc right_inverse right_neutral)

lemma (in monoid) left_inverse_if_right_inverse:
  fixes inv
  assumes
    right_inverse:  "\<And>a. a \<^bold>* inv a = \<^bold>1"
  shows "inv a \<^bold>* a = \<^bold>1"
  by (metis right_inverse_idem right_inverse)

lemma (in monoid) group_wrt_right_inverse:
  fixes inv
  assumes right_inverse:  "\<And>a. a \<^bold>* inv a = \<^bold>1"
  shows "group (\<^bold>*) \<^bold>1 inv"
proof unfold_locales
  show "\<And>a. \<^bold>1 \<^bold>* a = a"
    by simp
next
  show "\<And>a. inv a \<^bold>* a = \<^bold>1"
    by (metis left_inverse_if_right_inverse right_inverse)
qed


section \<open>Monoid\<close>

definition (in monoid) is_left_invertible \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> where
  "is_left_invertible a \<longleftrightarrow> (\<exists>a_inv. a_inv \<^bold>* a = \<^bold>1)"

definition (in monoid) is_right_invertible \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> where
  "is_right_invertible a \<longleftrightarrow> (\<exists>a_inv. a \<^bold>* a_inv = \<^bold>1)"

definition (in monoid) left_inverse \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> where
  "is_left_invertible a \<Longrightarrow> left_inverse a = (SOME a_inv. a_inv \<^bold>* a = \<^bold>1)"

definition (in monoid) right_inverse \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> where
  "is_right_invertible a \<Longrightarrow> right_inverse a = (SOME a_inv. a \<^bold>* a_inv = \<^bold>1)"

lemma (in monoid) comp_left_inverse [simp]: \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close>
  "is_left_invertible a \<Longrightarrow> left_inverse a \<^bold>* a = \<^bold>1"
  by (auto simp: is_left_invertible_def left_inverse_def intro: someI_ex)

lemma (in monoid) comp_right_inverse [simp]: \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close>
  "is_right_invertible a \<Longrightarrow> a \<^bold>* right_inverse a = \<^bold>1"
  by (auto simp: is_right_invertible_def right_inverse_def intro: someI_ex)

lemma (in monoid) neutral_is_left_invertible [simp]: \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close>
  "is_left_invertible \<^bold>1"
  by (simp add: is_left_invertible_def)

lemma (in monoid) neutral_is_right_invertible [simp]: \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close>
  "is_right_invertible \<^bold>1"
  by (simp add: is_right_invertible_def)


section \<open>Semigroup Action\<close>

text \<open>We define both left and right semigroup actions. Left semigroup actions seem to be prevalent
in algebra, but right semigroup actions directly uses the usual notation of term/atom/literal/clause
substitution.\<close>

locale left_semigroup_action = semigroup +
  fixes action :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" (infix \<open>\<cdot>\<close> 70)
  assumes action_compatibility[simp]: "\<And>a b x. (a \<^bold>* b) \<cdot> x = a \<cdot> (b \<cdot> x)"

locale right_semigroup_action = semigroup +
  fixes action :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" (infix \<open>\<cdot>\<close> 70)
  assumes action_compatibility[simp]: "\<And>x a b. x \<cdot> (a \<^bold>* b) = (x \<cdot> a) \<cdot> b"

text \<open>We then instantiate the right action in the context of the left action in order to get access
to any lemma proven in the context of the other locale. We do analogously in the context of the
right locale.\<close>

sublocale left_semigroup_action \<subseteq> right: right_semigroup_action where
  f = "\<lambda>x y. f y x" and action = "\<lambda>x y. action y x"
proof unfold_locales
  show "\<And>a b c. c \<^bold>* (b \<^bold>* a) = c \<^bold>* b \<^bold>* a"
    by (simp only: assoc)
next
  show "\<And>x a b. (b \<^bold>* a) \<cdot> x = b \<cdot> (a \<cdot> x)"
    by simp
qed

sublocale right_semigroup_action \<subseteq> left: left_semigroup_action where
  f = "\<lambda>x y. f y x" and action = "\<lambda>x y. action y x"
proof unfold_locales
  show "\<And>a b c. c \<^bold>* (b \<^bold>* a) = c \<^bold>* b \<^bold>* a"
    by (simp only: assoc)
next
  show "\<And>a b x. x \<cdot> (b \<^bold>* a) = (x \<cdot> b) \<cdot> a"
    by simp
qed

lemma (in right_semigroup_action) lifting_semigroup_action_to_set:
  "right_semigroup_action (\<^bold>*) (\<lambda>X a. (\<lambda>x. action x a) ` X)"
proof unfold_locales
  show "\<And>x a b. (\<lambda>x. x \<cdot> (a \<^bold>* b)) ` x = (\<lambda>x. x \<cdot> b) ` (\<lambda>x. x \<cdot> a) ` x"
    by (simp add: image_comp)
qed

lemma (in right_semigroup_action) lifting_semigroup_action_to_list:
  "right_semigroup_action (\<^bold>*) (\<lambda>xs a. map (\<lambda>x. action x a) xs)"
proof unfold_locales
  show "\<And>x a b. map (\<lambda>x. x \<cdot> (a \<^bold>* b)) x = map (\<lambda>x. x \<cdot> b) (map (\<lambda>x. x \<cdot> a) x)"
    by (simp add: image_comp)
qed


section \<open>Monoid Action\<close>

locale left_monoid_action = monoid +
  fixes action :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" (infix \<open>\<cdot>\<close> 70)
  assumes
    monoid_action_compatibility: "\<And>a b x. (a \<^bold>* b) \<cdot> x = a \<cdot> (b \<cdot> x)" and
    action_neutral[simp]: "\<And>x. \<^bold>1 \<cdot> x = x"

locale right_monoid_action = monoid +
  fixes action :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" (infix \<open>\<cdot>\<close> 70)
  assumes
    monoid_action_compatibility: "\<And>x a b. x \<cdot> (a \<^bold>* b) = (x \<cdot> a) \<cdot> b" and
    action_neutral[simp]: "\<And>x. x \<cdot> \<^bold>1 = x"

sublocale left_monoid_action \<subseteq> left_semigroup_action
  by unfold_locales (fact monoid_action_compatibility)

sublocale right_monoid_action \<subseteq> right_semigroup_action
  by unfold_locales (fact monoid_action_compatibility)

sublocale left_monoid_action \<subseteq> right: right_monoid_action where
  f = "\<lambda>x y. f y x" and action = "\<lambda>x y. action y x"
  by unfold_locales simp_all

sublocale right_monoid_action \<subseteq> left: left_monoid_action where
  f = "\<lambda>x y. f y x" and action = "\<lambda>x y. action y x"
  by unfold_locales simp_all

lemma (in right_monoid_action) lifting_monoid_action_to_set:
  "right_monoid_action (\<^bold>*) \<^bold>1 (\<lambda>X a. (\<lambda>x. action x a) ` X)"
proof (unfold_locales)
  show "\<And>x a b. (\<lambda>x. x \<cdot> (a \<^bold>* b)) ` x = (\<lambda>x. x \<cdot> b) ` (\<lambda>x. x \<cdot> a) ` x"
    by (simp add: image_comp)
next
  show "\<And>x. (\<lambda>x. x \<cdot> \<^bold>1) ` x = x"
    by simp
qed

lemma (in right_monoid_action) lifting_monoid_action_to_list:
  "right_monoid_action (\<^bold>*) \<^bold>1 (\<lambda>xs a. map (\<lambda>x. action x a) xs)"
proof unfold_locales
  show "\<And>x a b. map (\<lambda>x. x \<cdot> (a \<^bold>* b)) x = map (\<lambda>x. x \<cdot> b) (map (\<lambda>x. x \<cdot> a) x)"
    by simp
next
  show "\<And>x. map (\<lambda>x. x \<cdot> \<^bold>1) x = x"
    by simp
qed


section \<open>Group Action\<close>

locale left_group_action = group +
  fixes action :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" (infix \<open>\<cdot>\<close> 70)
  assumes
    group_action_compatibility: "\<And>a b x. (a \<^bold>* b) \<cdot> x = a \<cdot> (b \<cdot> x)" and
    group_action_neutral: "\<And>x. \<^bold>1 \<cdot> x = x"

locale right_group_action = group +
  fixes action :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" (infixl \<open>\<cdot>\<close> 70)
  assumes
    group_action_compatibility: "\<And>x a b. x \<cdot> (a \<^bold>* b) = (x \<cdot> a) \<cdot> b" and
    group_action_neutral: "\<And>x. x \<cdot> \<^bold>1 = x"

sublocale left_group_action \<subseteq> left_monoid_action
  by unfold_locales (fact group_action_compatibility group_action_neutral)+

sublocale right_group_action \<subseteq> right_monoid_action
  by unfold_locales (fact group_action_compatibility group_action_neutral)+

sublocale left_group_action \<subseteq> right: right_group_action where
  f = "\<lambda>x y. f y x" and action = "\<lambda>x y. action y x"
  by unfold_locales simp_all

sublocale right_group_action \<subseteq> left: left_group_action where
  f = "\<lambda>x y. f y x" and action = "\<lambda>x y. action y x"
  by unfold_locales simp_all

end
