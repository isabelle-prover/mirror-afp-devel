theory PAC_Misc
  imports Main
begin

text "I believe this should be added to the simplifier by default..."
lemma Collect_eq_comp':
  "{(x, y). P x y} O {(c, a). c = f a} = {(x, a). P x (f a)}"
  by auto

lemma in_set_conv_iff:
  "x \<in> set (take n xs) \<longleftrightarrow> (\<exists>i<n. i < length xs \<and> xs ! i = x)"
  by (metis in_set_conv_nth length_take min_less_iff_conj nth_take)

lemma in_set_take_conv_nth:
  "x \<in> set (take n xs) \<longleftrightarrow> (\<exists>i<min n (length xs). xs ! i = x)"
  by (simp add: in_set_conv_iff)

lemma in_set_remove1D:
  "a \<in> set (remove1 x xs) \<Longrightarrow> a \<in> set xs"
  by (meson notin_set_remove1)

end
