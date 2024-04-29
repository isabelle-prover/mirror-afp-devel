\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Inverse\<close>
theory Functions_Inverse
  imports
    Functions_Injective
    Binary_Relations_Function_Evaluation
begin

consts inverse_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"

overloading
  inverse_on_pred \<equiv> "inverse_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "inverse_on_pred P f g \<equiv> \<forall>x : P. g (f x) = x"
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
  assumes inv: "inverse_on (P :: 'a \<Rightarrow> bool) (f :: 'a \<Rightarrow> 'b) (g :: 'b \<Rightarrow> 'a)"
  shows "injective_on P f"
proof (rule injective_onI)
  fix x x'
  assume Px: "P x" and Px': "P x'" and f_x_eq_f_x': "f x = f x'"
  from inv have "x = g (f x)" using Px by (intro inverse_onD[symmetric])
  also have "... = g (f x')" by (simp only: f_x_eq_f_x')
  also have "... = x'" using inv Px' by (intro inverse_onD)
  finally show "x = x'" .
qed

lemma inverse_on_compI:
  fixes P :: "'a \<Rightarrow> bool" and P' :: "'b \<Rightarrow> bool"
  and f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a" and f' :: "'b \<Rightarrow> 'c" and g' :: "'c \<Rightarrow> 'b"
  assumes "(P \<Rightarrow> P') f"
  and "inverse_on P f g"
  and "inverse_on P' f' g'"
  shows "inverse_on P (f' \<circ> f) (g \<circ> g')"
  using assms by (intro inverse_onI) (auto dest!: inverse_onD)

consts inverse :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  inverse \<equiv> "inverse :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "(inverse :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool) \<equiv> inverse_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma inverse_eq_inverse_on:
  "(inverse :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool) = inverse_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding inverse_def ..

lemma inverse_eq_inverse_on_uhint [uhint]:
  assumes "P \<equiv>  \<top> :: 'a \<Rightarrow> bool"
  shows "inverse :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool \<equiv> inverse_on P"
  using assms by (simp add: inverse_eq_inverse_on)

lemma inverseI [intro]:
  assumes "\<And>x. g (f x) = x"
  shows "inverse f g"
  using assms by (urule inverse_onI)

lemma inverseD:
  assumes "inverse f g"
  shows "g (f x) = x"
  using assms by (urule (d) inverse_onD where chained = insert) simp_all

lemma inverse_on_if_inverse:
  fixes P :: "'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a"
  assumes "inverse f g"
  shows "inverse_on P f g"
  using assms by (intro inverse_onI) (blast dest: inverseD)

lemma right_unique_eq_app_if_injective:
  assumes "injective f"
  shows "right_unique (\<lambda>y x. y = f x)"
  using assms by (auto dest: injectiveD)

lemma inverse_eval_eq_app_if_injective:
  assumes "injective f"
  shows "inverse f (eval (\<lambda>y x. y = f x))"
  by (urule inverseI eval_eq_if_right_unique_onI right_unique_eq_app_if_injective)+
  (use assms in simp_all)

lemma inverse_if_injectiveE:
  assumes "injective (f :: 'a \<Rightarrow> 'b)"
  obtains g :: "'b \<Rightarrow> 'a" where "inverse f g"
  using assms inverse_eval_eq_app_if_injective by blast


end