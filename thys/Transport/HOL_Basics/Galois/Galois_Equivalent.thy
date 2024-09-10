\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Galois_Equivalent
  imports
    Transport_Compositions_Agree_Galois_Equivalence
begin

context
begin

interpretation galois L R l r for L R l r .

definition "galois_equivalent L R \<equiv> \<exists>l r. (L \<equiv>\<^sub>G R) l r"

lemma galois_equivalentI [intro]:
  assumes "(L \<equiv>\<^sub>G R) l r"
  shows "galois_equivalent L R"
  using assms unfolding galois_equivalent_def by auto

lemma galois_equivalentE [elim]:
  assumes "galois_equivalent L R"
  obtains l r where "(L \<equiv>\<^sub>G R) l r"
  using assms unfolding galois_equivalent_def by auto

lemma galois_equivalent_if_galois_equivalent:
  assumes "galois_equivalent L R"
  shows "galois_equivalent R L"
  using assms by (elim galois_equivalentE) auto

lemma galois_equivalent_trans [trans]:
  assumes "galois_equivalent L M"
  and "galois_equivalent M R"
  shows "galois_equivalent L R"
  using assms by (elim galois_equivalentE) (auto intro: transport_comp_same.galois_equivalenceI)

end

end