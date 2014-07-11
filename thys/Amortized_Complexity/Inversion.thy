theory Inversion
imports "../List-Index/List_Index"
begin

section "List Inversion"

abbreviation "dist_perm xs ys \<equiv> distinct xs \<and> distinct ys \<and> set xs = set ys"

definition before_in :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"
  ("(_ </ _/ in _)" [55,55,55] 55) where
"x < y in xs = (index xs x < index xs y \<and> y \<in> set xs)"

definition Inv :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a * 'a) set" where
"Inv xs ys = {(x,y). x < y in xs \<and> y < x in ys}"

lemma before_in_setD1: "x < y in xs \<Longrightarrow> x : set xs"
by (metis index_conv_size_if_notin index_less before_in_def less_asym order_refl)

lemma before_in_setD2: "x < y in xs \<Longrightarrow> y : set xs"
by (simp add: before_in_def)

lemma not_before_in:
  "x : set xs \<Longrightarrow> y : set xs \<Longrightarrow> \<not> x < y in xs \<longleftrightarrow> y < x in xs \<or> x=y"
by (metis index_eq_index_conv before_in_def less_asym linorder_neqE_nat)

lemma no_before_inI[simp]: "x < y in xs \<Longrightarrow> (\<not> y < x in xs) = True"
by (metis before_in_setD1 not_before_in)

lemma finite_Invs[simp]:  "finite(Inv xs ys)"
apply(rule finite_subset[where B = "set xs \<times> set ys"])
apply(auto simp add: Inv_def before_in_def)
apply(metis index_conv_size_if_notin index_less_size_conv less_asym)+
done

lemma Inv_id[simp]: "Inv xs xs = {}"
by(auto simp add: Inv_def before_in_def)

lemma card_Inv_sym: "card(Inv xs ys) = card(Inv ys xs)"
proof -
  have "Inv xs ys = (\<lambda>(x,y). (y,x)) ` Inv ys xs" by(auto simp: Inv_def)
  thus ?thesis by (metis card_image swap_inj_on)
qed

lemma Inv_tri_ineq:
  "dist_perm xs ys \<Longrightarrow> dist_perm ys zs \<Longrightarrow>
  Inv xs zs \<subseteq> Inv xs ys Un Inv ys zs"
by(auto simp: Inv_def) (metis before_in_setD1 not_before_in)

lemma card_Inv_tri_ineq:
  "dist_perm xs ys \<Longrightarrow> dist_perm ys zs \<Longrightarrow>
  card (Inv xs zs) \<le> card(Inv xs ys) + card (Inv ys zs)"
using card_mono[OF _ Inv_tri_ineq[of xs ys zs]]
by auto (metis card_Un_Int finite_Invs trans_le_add1)


definition "mtf x xs =
  (if x \<in> set xs then x # (take (index xs x) xs) @ drop (index xs x + 1) xs
   else xs)"

lemma mtf_id[simp]: "x \<notin> set xs \<Longrightarrow> mtf x xs = xs"
by(simp add: mtf_def)

lemma before_in_mtf: assumes "z \<in> set xs"
shows "x < y in mtf z xs  \<longleftrightarrow>
      (y \<noteq> z \<and> (if x=z then y \<in> set xs else x < y in xs))"
proof-
  have 0: "index xs z < size xs" by (metis assms index_less_size_conv)
  let ?xs = "take (index xs z) xs @ xs ! index xs z # drop (Suc (index xs z)) xs"
  have "x < y in mtf z xs = (y \<noteq> z \<and> (if x=z then y \<in> set ?xs else x < y in ?xs))"
    using assms
    by(auto simp add: mtf_def before_in_def index_append)
      (metis add_lessD1 index_less_size_conv length_take less_Suc_eq not_less_eq)
  with id_take_nth_drop[OF 0, symmetric] show ?thesis by(simp)
qed

lemma Inv_mtf: "set xs = set ys \<Longrightarrow> z : set ys \<Longrightarrow> Inv xs (mtf z ys) =
 Inv xs ys \<union> {(x,z)|x. x < z in xs \<and> x < z in ys}
 - {(z,x)|x. z < x in xs \<and> x < z in ys}"
by(auto simp add: Inv_def before_in_mtf not_before_in dest: before_in_setD1)

lemma set_mtf[simp]: "set(mtf x xs) = set xs"
by(simp add: mtf_def)
  (metis append_take_drop_id drop_Suc_conv_tl index_less le_refl Un_insert_right nth_index set_append set_simps(2))

lemma length_mtf[simp]: "size (mtf x xs) = size xs"
by (auto simp add: mtf_def min_def) (metis index_less_size_conv leD)

lemma distinct_mtf[simp]: "distinct (mtf x xs) = distinct xs"
by (metis length_mtf set_mtf card_distinct distinct_card)


definition "swapSuc n xs = xs[n := xs!Suc n, Suc n := xs!n]"

lemma index_swapSuc_distinct:
  "distinct xs \<Longrightarrow> Suc n < length xs \<Longrightarrow>
  index (swapSuc n xs) x =
  (if x = xs!n then Suc n else if x = xs!Suc n then n else index xs x)"
by(auto simp add: swapSuc_def index_swap_if_distinct)

lemma set_swapSuc[simp]: "Suc n < size xs \<Longrightarrow> set(swapSuc n xs) = set xs"
by(auto simp add: swapSuc_def set_conv_nth nth_list_update) metis

lemma before_in_swapSuc:
 "dist_perm xs ys \<Longrightarrow> Suc n < size xs \<Longrightarrow>
  x < y in (swapSuc n xs) \<longleftrightarrow>
  x < y in xs \<and> \<not> (x = xs!n \<and> y = xs!Suc n) \<or> x = xs!Suc n \<and> y = xs!n"
by(simp add:before_in_def index_swapSuc_distinct)
  (metis Suc_lessD Suc_lessI index_less_size_conv index_nth_id less_Suc_eq n_not_Suc_n nth_index)

lemma Inv_swap: assumes "dist_perm xs ys" "Suc n < size xs"
shows "Inv xs (swapSuc n ys) = 
  (if ys!n < ys!Suc n in xs
   then Inv xs ys \<union> {(ys!n, ys!Suc n)}
   else Inv xs ys - {(ys!Suc n, ys!n)})"
proof-
  have "length xs = length ys" using assms by (metis distinct_card)
  with assms show ?thesis
    by(simp add: Inv_def set_eq_iff)
      (metis before_in_def not_before_in before_in_swapSuc)
qed

end

