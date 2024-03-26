\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Bijections\<close>
theory Functions_Bijection
  imports
    Functions_Inverse
    Functions_Monotone
begin

consts bijection_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"

overloading
  bijection_on_pred \<equiv> "bijection_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "bijection_on_pred P P' f g \<equiv>
    ([P] \<Rrightarrow>\<^sub>m P') f \<and>
    ([P'] \<Rrightarrow>\<^sub>m P) g \<and>
    inverse_on P f g \<and>
    inverse_on P' g f"
end

lemma bijection_onI [intro]:
  assumes "([P] \<Rrightarrow>\<^sub>m P') f"
  and "([P'] \<Rrightarrow>\<^sub>m P) g"
  and "inverse_on P f g"
  and "inverse_on P' g f"
  shows "bijection_on P P' f g"
  using assms unfolding bijection_on_pred_def by blast

lemma bijection_onE [elim]:
  assumes "bijection_on P P' f g"
  obtains "([P] \<Rrightarrow>\<^sub>m P') f" "([P'] \<Rrightarrow>\<^sub>m P) g"
    "inverse_on P f g" "inverse_on P' g f"
  using assms unfolding bijection_on_pred_def by blast

context
  fixes P :: "'a \<Rightarrow> bool" and P' :: "'b \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a"
begin

lemma mono_wrt_pred_if_bijection_on_left:
  assumes "bijection_on P P' f g"
  shows "([P] \<Rrightarrow>\<^sub>m P') f"
  using assms by (elim bijection_onE)

lemma mono_wrt_pred_if_bijection_on_right:
  assumes "bijection_on P P' f g"
  shows "([P'] \<Rrightarrow>\<^sub>m P) g"
  using assms by (elim bijection_onE)

lemma bijection_on_pred_right:
  assumes "bijection_on P P' f g"
  and "P x"
  shows "P' (f x)"
  using assms by blast

lemma bijection_on_pred_left:
  assumes "bijection_on P P' f g"
  and "P' y"
  shows "P (g y)"
  using assms by blast

lemma inverse_on_if_bijection_on_left_right:
  assumes "bijection_on P P' f g"
  shows "inverse_on P f g"
  using assms by (elim bijection_onE)

lemma inverse_on_if_bijection_on_right_left:
  assumes "bijection_on P P' f g"
  shows "inverse_on P' g f"
  using assms by (elim bijection_onE)

lemma bijection_on_left_right_eq_self:
  assumes "bijection_on P P' f g"
  and "P x"
  shows "g (f x) = x"
  using assms inverse_on_if_bijection_on_left_right
  by (intro inverse_onD)

lemma bijection_on_right_left_eq_self':
  assumes "bijection_on P P' f g"
  and "P' y"
  shows "f (g y) = y"
  using assms inverse_on_if_bijection_on_right_left by (intro inverse_onD)

lemma bijection_on_right_left_if_bijection_on_left_right:
  assumes "bijection_on P P' f g"
  shows "bijection_on P' P g f"
  using assms by auto

end

context
  fixes P :: "'a \<Rightarrow> bool" and P' :: "'b \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a"
begin

lemma injective_on_if_bijection_on_left:
  assumes "bijection_on P P' f g"
  shows "injective_on P f"
  using assms
  by (intro injective_on_if_inverse_on inverse_on_if_bijection_on_left_right)

lemma injective_on_if_bijection_on_right:
  assumes "bijection_on P P' f g"
  shows "injective_on P' g"
  by (intro injective_on_if_inverse_on)
  (fact inverse_on_if_bijection_on_right_left[OF assms])

end

lemma bijection_on_compI:
  fixes P :: "'a \<Rightarrow> bool" and P' :: "'b \<Rightarrow> bool" and P'' :: "'c \<Rightarrow> bool"
  and f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a" and f' :: "'b \<Rightarrow> 'c" and g' :: "'c \<Rightarrow> 'b"
  assumes "bijection_on P P' f g"
  and "bijection_on P' P'' f' g'"
  shows "bijection_on P P'' (f' \<circ> f) (g \<circ> g')"
  using assms by (intro bijection_onI)
  (auto intro: dep_mono_wrt_pred_comp_dep_mono_wrt_pred_compI' inverse_on_compI
    elim!: bijection_onE)


consts bijection :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  bijection \<equiv> "bijection :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "(bijection :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool) \<equiv>
    bijection_on (\<top> :: 'a \<Rightarrow> bool) (\<top> :: 'b \<Rightarrow> bool)"
end

lemma bijection_eq_bijection_on:
  "(bijection :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool) = bijection_on (\<top> :: 'a \<Rightarrow> bool) (\<top> :: 'b \<Rightarrow> bool)"
  unfolding bijection_def ..

lemma bijection_eq_bijection_on_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  and "Q \<equiv> (\<top> :: 'b \<Rightarrow> bool)"
  shows "(bijection :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool) = bijection_on P Q"
  using assms by (simp add: bijection_eq_bijection_on)

context
  fixes P :: "'a \<Rightarrow> bool" and P' :: "'b \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a"
begin

lemma bijectionI [intro]:
  assumes "inverse f g"
  and "inverse g f"
  shows "bijection f g"
  by (urule bijection_onI) (simp | urule assms)+

lemma bijectionE [elim]:
  assumes "bijection f g"
  obtains "inverse f g" "inverse g f"
  using assms by (urule (e) bijection_onE)

lemma inverse_if_bijection_left_right:
  assumes "bijection f g"
  shows "inverse f g"
  using assms by (elim bijectionE)

lemma inverse_if_bijection_right_left:
  assumes "bijection f g"
  shows "inverse g f"
  using assms by (elim bijectionE)

end

context
  fixes P :: "'a \<Rightarrow> bool" and P' :: "'b \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a"
begin

lemma bijection_right_left_if_bijection_left_right:
  assumes "bijection f g"
  shows "bijection g f"
  using assms by auto

paragraph \<open>Instantiations\<close>

lemma bijection_on_self_id: "bijection_on P P (id :: 'a \<Rightarrow> 'a) (id :: 'a \<Rightarrow> 'a)"
  by (intro bijection_onI inverse_onI dep_mono_wrt_predI) simp_all

end

end