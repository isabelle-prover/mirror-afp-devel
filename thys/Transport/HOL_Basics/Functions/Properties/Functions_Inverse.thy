\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Inverse\<close>
theory Functions_Inverse
  imports
    Functions_Injective
begin

consts inverse_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> bool"

overloading
  inverse_on_pred \<equiv> "inverse_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "inverse_on_pred P f g \<equiv> \<forall>x. P x \<longrightarrow> g (f x) = x"
end

lemma inverse_onI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> g (f x) = x"
  shows "inverse_on P f g"
  unfolding inverse_on_pred_def using assms by blast

lemma inverse_onD:
  assumes "inverse_on P f g"
  and "P x"
  shows "g (f x) = x"
  using assms unfolding inverse_on_pred_def by blast

lemma injective_on_if_inverse_on:
  assumes inv: "inverse_on (P :: 'a \<Rightarrow> bool) (f :: 'a \<Rightarrow> _) g"
  shows "injective_on P f"
proof (rule injective_onI)
  fix x x'
  assume Px: "P x" and Px': "P x'" and f_x_eq_f_x': "f x = f x'"
  from inv have "x = g (f x)" using Px by (intro inverse_onD[symmetric])
  also have "... = g (f x')" by (simp only: f_x_eq_f_x')
  also have "... = x'" using inv Px' by (intro inverse_onD)
  finally show "x = x'" .
qed

definition "inverse (f :: 'a \<Rightarrow> _) \<equiv> inverse_on (\<top> :: 'a \<Rightarrow> bool) f"

lemma inverse_eq_inverse_on:
  "inverse (f :: 'a \<Rightarrow> _) = inverse_on (\<top> :: 'a \<Rightarrow> bool) f"
  unfolding inverse_def ..

lemma inverseI [intro]:
  assumes "\<And>x. g (f x) = x"
  shows "inverse f g"
  unfolding inverse_eq_inverse_on using assms by (intro inverse_onI)

lemma inverseD:
  assumes "inverse f g"
  shows "g (f x) = x"
  using assms unfolding inverse_eq_inverse_on by (auto dest: inverse_onD)

lemma inverse_on_if_inverse:
  fixes P :: "'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
  assumes "inverse f g"
  shows "inverse_on P f g"
  using assms by (intro inverse_onI) (blast dest: inverseD)


end