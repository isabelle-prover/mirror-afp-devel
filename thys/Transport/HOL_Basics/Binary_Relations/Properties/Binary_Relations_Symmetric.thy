\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Symmetric\<close>
theory Binary_Relations_Symmetric
  imports
    Functions_Monotone
begin

consts symmetric_on :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  symmetric_on_pred \<equiv> "symmetric_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "symmetric_on_pred P R \<equiv> \<forall>x y : P. R x y \<longrightarrow> R y x"
end

lemma symmetric_onI [intro]:
  assumes "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> R x y \<Longrightarrow> R y x"
  shows "symmetric_on P R"
  unfolding symmetric_on_pred_def using assms by blast

lemma symmetric_onD:
  assumes "symmetric_on P R"
  and "P x" "P y"
  and "R x y"
  shows "R y x"
  using assms unfolding symmetric_on_pred_def by blast

lemma symmetric_on_rel_inv_iff_symmetric_on [iff]:
  "symmetric_on P R\<inverse> \<longleftrightarrow> symmetric_on (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  by (blast dest: symmetric_onD)

lemma antimono_symmetric_on: "antimono (symmetric_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool)"
  by (intro antimonoI) (auto dest: symmetric_onD)

lemma symmetric_on_if_le_pred_if_symmetric_on:
  fixes P' :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "symmetric_on P R"
  and "P' \<le> P"
  shows "symmetric_on P' R"
  using assms antimono_symmetric_on by blast

consts symmetric :: "'a \<Rightarrow> bool"

overloading
  symmetric \<equiv> "symmetric :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "(symmetric :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) \<equiv> symmetric_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma symmetric_eq_symmetric_on:
  "(symmetric :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) = symmetric_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding symmetric_def ..

lemma symmetric_eq_symmetric_on_uhint [uhint]:
  "P \<equiv> (\<top> :: 'a \<Rightarrow> bool) \<Longrightarrow> (symmetric :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) \<equiv> symmetric_on P"
  by (simp add: symmetric_eq_symmetric_on)

lemma symmetricI [intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> R y x"
  shows "symmetric R"
  using assms by (urule symmetric_onI)

lemma symmetricD:
  assumes "symmetric R"
  and "R x y"
  shows "R y x"
  using assms by (urule (d) symmetric_onD chained: insert) simp_all

lemma symmetric_on_if_symmetric:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "symmetric R"
  shows "symmetric_on P R"
  using assms by (intro symmetric_onI) (blast dest: symmetricD)

lemma symmetric_rel_inv_iff_symmetric [iff]: "symmetric R\<inverse> \<longleftrightarrow> symmetric (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  by (blast dest: symmetricD)

lemma rel_inv_eq_self_if_symmetric [simp]:
  assumes "symmetric R"
  shows "R\<inverse> = R"
  using assms by (blast dest: symmetricD)

lemma rel_iff_rel_if_symmetric:
  assumes "symmetric R"
  shows "R x y \<longleftrightarrow> R y x"
  using assms by (blast dest: symmetricD)

lemma symmetric_if_rel_inv_eq_self:
  assumes "R\<inverse> = R"
  shows "symmetric R"
  by (intro symmetricI, subst assms[symmetric]) simp

lemma symmetric_iff_rel_inv_eq_self: "symmetric R \<longleftrightarrow> R\<inverse> = R"
  using rel_inv_eq_self_if_symmetric symmetric_if_rel_inv_eq_self by blast

lemma symmetric_if_symmetric_on_in_field:
  assumes "symmetric_on (in_field R) R"
  shows "symmetric R"
  using assms by (intro symmetricI) (blast dest: symmetric_onD)

corollary symmetric_on_in_field_iff_symmetric [iff]:
  "symmetric_on (in_field R) R \<longleftrightarrow> symmetric R"
  using symmetric_if_symmetric_on_in_field symmetric_on_if_symmetric
  by blast


paragraph \<open>Instantiations\<close>

lemma symmetric_eq [iff]: "symmetric (=)"
  by (rule symmetricI) (rule sym)

lemma symmetric_top: "symmetric (\<top> :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  by (rule symmetricI) auto

end