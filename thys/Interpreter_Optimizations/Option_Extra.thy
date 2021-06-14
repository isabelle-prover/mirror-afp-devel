theory Option_Extra
  imports Main
begin

fun ap_option (infixl "\<diamondop>" 60) where
  "(Some f) \<diamondop> (Some x) = Some (f x)" |
  "_ \<diamondop> _ = None"

lemma ap_option_eq_Some_conv: "f \<diamondop> x = Some y \<longleftrightarrow> (\<exists>f' x'. f = Some f' \<and> x = Some x' \<and> y = f' x')"
  by (cases f; simp; cases x; auto)

definition ap_map_prod where
  "ap_map_prod f g p \<equiv> Some Pair \<diamondop> f (fst p) \<diamondop> g (snd p)"

lemma ap_map_prod_eq_Some_conv:
  "ap_map_prod f g p = Some p' \<longleftrightarrow> (\<exists>x y. p = (x, y) \<and> (\<exists>x' y'. p' = (x', y') \<and> f x = Some x' \<and> g y = Some y'))"
proof (cases p)
  case (Pair x y)
  then show ?thesis
    unfolding ap_map_prod_def
    by (auto simp add: ap_map_prod_def ap_option_eq_Some_conv)
qed

fun ap_map_list :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "ap_map_list _ [] = Some []" |
  "ap_map_list f (x # xs) = Some (#) \<diamondop> f x \<diamondop> ap_map_list f xs"

lemma length_ap_map_list: "ap_map_list f xs = Some ys \<Longrightarrow> length ys = length xs"
  by (induction xs arbitrary: ys) (auto simp add: ap_option_eq_Some_conv)

lemma ap_map_list_imp_rel_option_map_of:
  assumes "ap_map_list f xs = Some ys" and
    "\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> f x = Some y \<Longrightarrow> fst x = fst y"
  shows "rel_option (\<lambda>x y. f (k, x) = Some (k, y)) (map_of xs k) (map_of ys k)"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  from Cons.prems show ?case
    apply (auto simp add: ap_option_eq_Some_conv option_rel_Some1 elim!: Cons.IH)
      apply (metis prod.collapse)
     apply (metis prod.collapse)
    by blast
qed

lemma ap_map_list_ap_map_prod_imp_rel_option_map_of:
  assumes "ap_map_list (ap_map_prod Some f) xs = Some ys"
  shows "rel_option (\<lambda>x y. f x = Some y) (map_of xs k) (map_of ys k)"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  from Cons.prems show ?case
    by (auto simp: ap_option_eq_Some_conv ap_map_prod_eq_Some_conv elim: Cons.IH[simplified])
qed

lemma ex_ap_map_list_eq_SomeI:
  assumes "list_all (\<lambda>x. \<exists>y. f x = Some y) xs"
  shows "\<exists>ys. ap_map_list f xs = Some ys"
  using assms
  by (induction xs) auto

lemma ap_map_list_iff_list_all2:
  "ap_map_list f xs = Some ys \<longleftrightarrow> list_all2 (\<lambda>x y. f x = Some y) xs ys"
proof (rule iffI)
  show "ap_map_list f xs = Some ys \<Longrightarrow> list_all2 (\<lambda>x y. f x = Some y) xs ys"
    by (induction xs arbitrary: ys) (auto simp: ap_option_eq_Some_conv)
next
  show "list_all2 (\<lambda>x y. f x = Some y) xs ys \<Longrightarrow> ap_map_list f xs = Some ys"
    by (induction xs ys rule: list.rel_induct) auto
qed

lemma ap_map_list_map_conv:
  assumes
    "ap_map_list f xs = Some ys" and
    "\<And>x y. x \<in> set xs \<Longrightarrow> f x = Some y \<Longrightarrow> y = g x"
  shows "ys = map g xs"
  using assms
  by (induction xs arbitrary: ys) (auto simp: ap_option_eq_Some_conv)

end