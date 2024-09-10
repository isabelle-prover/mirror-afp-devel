\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Irreflexive\<close>
theory Binary_Relations_Irreflexive
  imports
    Functions_Monotone
begin

consts irreflexive_on :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  irreflexive_on_pred \<equiv> "irreflexive_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "irreflexive_on_pred P R \<equiv> \<forall>x : P. \<not>(R x x)"
end

lemma irreflexive_onI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> \<not>(R x x)"
  shows "irreflexive_on P R"
  using assms unfolding irreflexive_on_pred_def by blast

lemma irreflexive_onD [dest]:
  assumes "irreflexive_on P R"
  and "P x"
  shows "\<not>(R x x)"
  using assms unfolding irreflexive_on_pred_def by blast

lemma antimono_irreflexive_on:
  "((\<le>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<ge>)) (irreflexive_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool)"
  by blast


consts irreflexive :: "'a \<Rightarrow> bool"

overloading
  irreflexive \<equiv> "irreflexive :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "(irreflexive :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> irreflexive_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma irreflexive_eq_irreflexive_on:
  "(irreflexive :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) = irreflexive_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding irreflexive_def ..

lemma irreflexive_eq_irreflexive_on_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  shows "irreflexive :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _ \<equiv> irreflexive_on P"
  using assms by (simp add: irreflexive_eq_irreflexive_on)

lemma irreflexiveI [intro]:
  assumes "\<And>x. \<not>(R x x)"
  shows "irreflexive R"
  using assms by (urule irreflexive_onI)

lemma irreflexiveD:
  assumes "irreflexive R"
  shows "\<not>(R x x)"
  using assms by (urule (d) irreflexive_onD where chained = insert) simp

lemma irreflexive_on_if_irreflexive:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "irreflexive R"
  shows "irreflexive_on P R"
  using assms by (intro irreflexive_onI) (blast dest: irreflexiveD)


end