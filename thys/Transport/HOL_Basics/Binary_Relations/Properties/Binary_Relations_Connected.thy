\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Connected\<close>
theory Binary_Relations_Connected
  imports
    Binary_Relation_Functions
begin

consts connected_on :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  connected_on_pred \<equiv> "connected_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "connected_on_pred P R \<equiv> \<forall>x y : P. x \<noteq> y \<longrightarrow> R x y \<or> R y x"
end

lemma connected_onI [intro]:
  assumes "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> x \<noteq> y \<Longrightarrow> R x y \<or> R y x"
  shows "connected_on P R"
  using assms unfolding connected_on_pred_def by blast

lemma connected_onE [elim]:
  assumes "connected_on P R"
  and "P x" "P y"
  obtains "x = y" | "R x y" | "R y x"
  using assms unfolding connected_on_pred_def by auto

lemma connected_on_rel_inv_iff_connected_on [iff]:
  "connected_on (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool)\<inverse> \<longleftrightarrow> connected_on P R"
  by blast

consts connected :: "'a \<Rightarrow> bool"

overloading
  connected \<equiv> "connected :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "connected :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> connected_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma connected_eq_connected_on:
  "(connected :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) = connected_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding connected_def ..

lemma connected_eq_connected_on_uhint [uhint]:
  "P \<equiv> (\<top> :: 'a \<Rightarrow> bool) \<Longrightarrow> (connected :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) \<equiv> connected_on P"
  by (simp add: connected_eq_connected_on)

lemma connectedI [intro]:
  assumes "\<And>x y. x \<noteq> y \<Longrightarrow> R x y \<or> R y x"
  shows "connected R"
  using assms by (urule connected_onI)

lemma connectedE [elim]:
  assumes "connected R"
  and "x \<noteq> y"
  obtains "R x y" | "R y x"
  using assms by (urule (e) connected_onE where chained = insert) auto

lemma connected_on_if_connected:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "connected R"
  shows "connected_on P R"
  using assms by (intro connected_onI) blast


end