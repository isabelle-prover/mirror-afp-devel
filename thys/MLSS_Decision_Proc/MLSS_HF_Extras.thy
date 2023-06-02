theory MLSS_HF_Extras
  imports HereditarilyFinite.Rank
begin

lemma hcard_ord_of[simp]:
  "hcard (ord_of n) = n"
  unfolding hcard_def hfset_ord_of card_image[OF inj_ord_of]
  by simp

lemma hcard_HF: "finite A \<Longrightarrow> hcard (HF A) = card A"
  unfolding hcard_def using hfset_HF by simp

end