\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Inverse\<close>
theory Functions_Inverse
  imports
    Functions_Injective
    Binary_Relations_Function_Evaluation
    Bounded_Definite_Description
begin

consts the_inverse_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"

definition "the_inverse_on_pred P f \<equiv> \<lambda>y. THE x : P. y = f x"
adhoc_overloading the_inverse_on the_inverse_on_pred

lemma the_inverse_on_eq_if_injective_onI:
  assumes "injective_on P f"
  and "y = f x"
  and "P x"
  shows "the_inverse_on P f y = x"
  unfolding the_inverse_on_pred_def using assms by (intro bthe_eqI) (auto dest: injective_onD)

lemma the_inverse_on_app_eq_if_injective_onI [simp]:
  assumes "injective_on P f"
  and "P x"
  shows "the_inverse_on P f (f x) = x"
  using assms by (intro the_inverse_on_eq_if_injective_onI) auto

consts the_inverse :: "'a \<Rightarrow> 'b"

definition "the_inverse_fun \<equiv> the_inverse_on (\<top> :: 'a \<Rightarrow> bool)"
adhoc_overloading the_inverse the_inverse_fun

lemma the_inverse_eq_the_inverse_on:
  "the_inverse = the_inverse_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding the_inverse_fun_def ..

lemma the_inverse_eq_the_inverse_on_uhint [uhint]:
  assumes "P \<equiv>  \<top> :: 'a \<Rightarrow> bool"
  shows "the_inverse :: ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a \<equiv> the_inverse_on P"
  using assms by (simp add: the_inverse_eq_the_inverse_on)

lemma the_inverse_eq_if_injectiveI:
  assumes "injective f"
  and "y = f x"
  shows "the_inverse f y = x"
  using assms by (urule the_inverse_on_eq_if_injective_onI) auto

lemma the_inverse_app_eq_if_injectiveI [simp]:
  assumes "injective f"
  shows "the_inverse f (f x) = x"
  using assms by (urule the_inverse_on_app_eq_if_injective_onI) auto

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

lemma inverse_onE:
  assumes "inverse_on P f g"
  obtains "\<And>x. P x \<Longrightarrow> g (f x) = x"
  using assms inverse_onD by fastforce

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

lemma inverse_on_the_inverse_on_if_injective_on:
  fixes P :: "'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
  assumes "injective_on P f"
  shows "inverse_on P f (the_inverse_on P f)"
  using assms by (intro inverse_onI the_inverse_on_eq_if_injective_onI) auto

lemma inverse_on_has_inverse_on_the_inverse_on_if_injective_on:
  assumes "injective_on P f"
  shows "inverse_on (has_inverse_on P f) (the_inverse_on P f) f"
  using assms by (intro inverse_onI) auto

lemma antimono_inverse_on: "antimono (inverse_on ::  ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool)"
  by (fastforce dest: inverse_onD)

lemma inverse_on_compI:
  fixes P :: "'a \<Rightarrow> bool" and P' :: "'b \<Rightarrow> bool"
  and f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a" and f' :: "'b \<Rightarrow> 'c" and g' :: "'c \<Rightarrow> 'b"
  assumes "(P \<Rightarrow> P') f"
  and "inverse_on P f g"
  and "inverse_on P' f' g'"
  shows "inverse_on P (f' \<circ> f) (g \<circ> g')"
  using assms by (intro inverse_onI) (force dest: inverse_onD)

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

lemma inverseE:
  assumes "inverse f g"
  obtains "\<And>x. g (f x) = x"
  using assms by (urule (e) inverse_onE where chained = insert) simp_all

lemma inverse_on_if_inverse:
  fixes P :: "'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a"
  assumes "inverse f g"
  shows "inverse_on P f g"
  using assms by (intro inverse_onI) (blast dest: inverseD)

lemma injective_if_inverse:
  assumes "inverse (f :: 'a \<Rightarrow> 'b) (g :: 'b \<Rightarrow> 'a)"
  shows "injective f"
  using assms by (urule injective_on_if_inverse_on)

lemma inverse_the_inverse_if_injective:
  assumes "injective f"
  shows "inverse f (the_inverse f)"
  using assms by (urule inverse_on_the_inverse_on_if_injective_on)

lemma inverse_on_has_inverse_the_inverse_if_injective:
  assumes "injective f"
  shows "inverse_on (has_inverse f) (the_inverse f) f"
  using assms by (urule inverse_on_has_inverse_on_the_inverse_on_if_injective_on)

end