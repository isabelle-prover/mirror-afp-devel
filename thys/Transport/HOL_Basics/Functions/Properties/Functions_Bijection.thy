\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Bijection\<close>
theory Functions_Bijection
  imports
    Functions_Inverse
    Functions_Monotone
begin

consts bijection_on :: "'a \<Rightarrow> 'b \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'c) \<Rightarrow> bool"

overloading
  bijection_on_pred \<equiv> "bijection_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
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

lemma bijection_onE:
  assumes "bijection_on P P' f g"
  obtains "([P] \<Rrightarrow>\<^sub>m P') f" "([P'] \<Rrightarrow>\<^sub>m P) g"
    "inverse_on P f g" "inverse_on P' g f"
  using assms unfolding bijection_on_pred_def by blast

context
  fixes P :: "'a \<Rightarrow> bool"
  and P' :: "'b \<Rightarrow> bool"
  and f :: "'a \<Rightarrow> 'b"
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
  using assms by (blast elim: bijection_onE)

lemma bijection_on_pred_left:
  assumes "bijection_on P P' f g"
  and "P' y"
  shows "P (g y)"
  using assms by (blast elim: bijection_onE)

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
  using assms by (auto elim: bijection_onE)

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


definition "bijection (f :: 'a \<Rightarrow> 'b) \<equiv> bijection_on (\<top> :: 'a \<Rightarrow> bool) (\<top> :: 'b \<Rightarrow> bool) f"

lemma bijection_eq_bijection_on:
  "bijection (f :: 'a \<Rightarrow> 'b) = bijection_on (\<top> :: 'a \<Rightarrow> bool) (\<top> :: 'b \<Rightarrow> bool) f"
  unfolding bijection_def ..

lemma bijectionI [intro]:
  assumes "inverse f g"
  and "inverse g f"
  shows "bijection f g"
  unfolding bijection_eq_bijection_on using assms
  by (intro bijection_onI inverse_on_if_inverse dep_mono_wrt_predI) simp_all

lemma bijectionE [elim]:
  assumes "bijection f g"
  obtains "inverse f g" "inverse g f"
  using assms unfolding bijection_eq_bijection_on inverse_eq_inverse_on
  by (blast elim: bijection_onE)

lemma inverse_if_bijection_left_right:
  assumes "bijection f g"
  shows "inverse f g"
  using assms by (elim bijectionE)

lemma inverse_if_bijection_right_left:
  assumes "bijection f g"
  shows "inverse g f"
  using assms by (elim bijectionE)

lemma bijection_right_left_if_bijection_left_right:
  assumes "bijection f g"
  shows "bijection g f"
  using assms by auto


paragraph \<open>Instantiations\<close>

lemma bijection_on_self_id:
  fixes P :: "'a \<Rightarrow> bool"
  shows "bijection_on P P (id :: 'a \<Rightarrow> _) id"
  by (intro bijection_onI inverse_onI dep_mono_wrt_predI) simp_all


end