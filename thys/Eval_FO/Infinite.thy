theory Infinite
  imports Main
begin

class infinite =
  assumes infinite_UNIV: "infinite (UNIV :: 'a set)"
begin

lemma arb_element: "finite Y \<Longrightarrow> \<exists>x :: 'a. x \<notin> Y"
  using ex_new_if_finite infinite_UNIV
  by blast

lemma arb_finite_subset: "finite Y \<Longrightarrow> \<exists>X :: 'a set. Y \<inter> X = {} \<and> finite X \<and> n \<le> card X"
proof -
  assume fin: "finite Y"
  then obtain X where "X \<subseteq> UNIV - Y" "finite X" "n \<le> card X"
    using infinite_UNIV
    by (metis Compl_eq_Diff_UNIV finite_compl infinite_arbitrarily_large order_refl)
  then show ?thesis
    by auto
qed

lemma arb_countable_map: "finite Y \<Longrightarrow> \<exists>f :: (nat \<Rightarrow> 'a). inj f \<and> range f \<subseteq> UNIV - Y"
  using infinite_UNIV
  by (auto simp: infinite_countable_subset)

end

instance nat :: infinite
  by standard auto

end
