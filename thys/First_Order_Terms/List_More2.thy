subsection \<open>Auxiliary Lemmas on Lists\<close>

theory List_More2
imports
  Main
begin

lemma upt_append_upt: "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> [i..<j] @ [j..<k] = [i..<k]"
  using upt_add_eq_append[of i j "k - j"] by auto

lemma split_list_index: assumes "i < length xs"
  shows "xs = map ((!) xs) [0..<i] @ xs ! i # map ((!) xs) [Suc i..<length xs]"
  using assms
  by (metis list.map(2) map_append map_nth nat_less_le
      upt_append_upt upt_conv_Cons zero_order(1))
end