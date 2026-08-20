theory Fun_Extra \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 
  imports Main
begin

definition bij_partition where
  "bij_partition S T \<equiv> SOME h. bij_betw h (T - S) (S - T)"

lemma bij_partition:
  assumes "finite S" "finite T" "card S = card T"
  shows "bij_betw (bij_partition S T) (T - S) (S - T)"
  using assms
  unfolding bij_partition_def
  by (metis add_diff_cancel_left' card_add_diff_finite finite_Diff finite_same_card_bij someI)

end
