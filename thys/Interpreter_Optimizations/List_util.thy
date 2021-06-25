theory List_util
  imports Main
begin

inductive same_length :: "'a list \<Rightarrow> 'b list \<Rightarrow> bool" where
  same_length_Nil: "same_length [] []" |
  same_length_Cons: "same_length xs ys \<Longrightarrow> same_length (x # xs) (y # ys)"

code_pred same_length .

lemma same_length_iff_eq_lengths: "same_length xs ys \<longleftrightarrow> length xs = length ys"
proof
  assume "same_length xs ys"
  then show "length xs = length ys"
    by (induction xs ys rule: same_length.induct) simp_all
next
  assume "length xs = length ys"
  then show "same_length xs ys"
  proof (induction xs arbitrary: ys)
    case Nil
    then show ?case
      by (simp add: same_length_Nil)
  next
    case (Cons x xs)
    then show ?case
      by (metis length_Suc_conv same_length_Cons)
  qed
qed

lemma same_length_Cons:
  "same_length (x # xs) ys \<Longrightarrow> \<exists>y ys'. ys = y # ys'"
  "same_length xs (y # ys) \<Longrightarrow> \<exists>x xs'. xs = x # xs'"
proof -
  assume "same_length (x # xs) ys"
  then show "\<exists>y ys'. ys = y # ys'"
    by (induction "x # xs" ys rule: same_length.induct) simp
next
  assume "same_length xs (y # ys)"
  then show "\<exists>x xs'. xs = x # xs'"
    by (induction xs "y # ys" rule: same_length.induct) simp
qed


section \<open>nth\_opt\<close>

fun nth_opt where
  "nth_opt (x # _) 0 = Some x" |
  "nth_opt (_ # xs) (Suc n) = nth_opt xs n" |
  "nth_opt _ _ = None"

lemma nth_opt_eq_Some_conv: "nth_opt xs n = Some x \<longleftrightarrow> n < length xs \<and> xs ! n = x"
  by (induction xs n rule: nth_opt.induct; simp)

lemmas nth_opt_eq_SomeD[dest] = nth_opt_eq_Some_conv[THEN iffD1]


section \<open>Generic lemmas\<close>

lemma list_rel_imp_pred1:
  assumes
    "list_all2 R xs ys" and
    "\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> R x y \<Longrightarrow> P x"
  shows "list_all P xs"
  using assms
  by (induction xs ys rule: list.rel_induct) auto

lemma list_rel_imp_pred2:
  assumes
    "list_all2 R xs ys" and
    "\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> R x y \<Longrightarrow> P y"
  shows "list_all P ys"
  using assms
  by (induction xs ys rule: list.rel_induct) auto

lemma eq_append_conv_conj: "(zs = xs @ ys) = (xs = take (length xs) zs \<and> ys = drop (length xs) zs)"
  by (metis append_eq_conv_conj)

lemma list_all_list_updateI: "list_all P xs \<Longrightarrow> P x \<Longrightarrow> list_all P (list_update xs n x)"
  by (induction xs arbitrary: n) (auto simp add: nat.split_sels(2))

lemmas list_all2_update1_cong = list_all2_update_cong[of _ _ ys _ "ys ! i" i for ys i, simplified]
lemmas list_all2_update2_cong = list_all2_update_cong[of _ xs _ "xs ! i" _ i for xs i, simplified]

lemma map_list_update_id:
  "f (xs ! pc) = f instr \<Longrightarrow> map f (xs[pc := instr]) = map f xs"
  using list_update_id map_update by metis

lemma list_all_eq_const_imp_replicate:
  assumes "list_all (\<lambda>x. x = y) xs"
  shows "xs = replicate (length xs) y"
  using assms
  by (induction xs; simp)

lemma list_all_eq_const_imp_replicate':
  assumes "list_all ((=) y) xs"
  shows "xs = replicate (length xs) y"
  using assms
  by (induction xs; simp)

lemma list_all_eq_const_replicate_lhs[intro]:
  "list_all (\<lambda>x. y = x) (replicate n y)"
  by (simp add: list_all_length)

lemma list_all_eq_const_replicate_rhs[intro]:
  "list_all (\<lambda>x. x = y) (replicate n y)"
  by (simp add: list_all_length)

lemma list_all_eq_const_replicate[simp]: "list_all ((=) c) (replicate n c)"
  by (simp add: list_all_length)

lemma replicate_eq_map:
  assumes "n = length xs" and "\<And>y. y \<in> set xs \<Longrightarrow> f y = x"
  shows "replicate n x = map f xs"
  using assms
proof (induction xs arbitrary: n)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  thus ?case by (cases n; auto)
qed

lemma replicate_eq_impl_Ball_eq:
  shows "replicate n c = xs \<Longrightarrow> (\<forall>x \<in> set xs. x = c)"
  by (meson in_set_replicate)

lemma rel_option_map_of:
  assumes "list_all2 (rel_prod (=) R) xs ys"
  shows "rel_option R (map_of xs l) (map_of ys l)"
  using assms
proof (induction xs ys rule: list.rel_induct)
  case Nil
  thus ?case by simp
next
  case (Cons x xs y ys)
  from Cons.hyps have "fst x = fst y" and "R (snd x) (snd y)"
    by (simp_all add: rel_prod_sel)
  show ?case
  proof (cases "l = fst y")
    case True
    then show ?thesis
      by (simp add: \<open>fst x = fst y\<close> \<open>R (snd x) (snd y)\<close>)
  next
    case False
    then show ?thesis
      using Cons.IH
      by (simp add: \<open>fst x = fst y\<close> )
  qed
qed

lemma list_all2_rel_prod_nth:
  assumes "list_all2 (rel_prod R1 R2) xs ys" and "n < length xs"
  shows "R1 (fst (xs ! n)) (fst (ys ! n)) \<and> R2 (snd (xs ! n)) (snd (ys ! n))"
  using assms
proof (induction n arbitrary: xs ys)
  case 0
  then show ?case
    using assms(1,2)
    by (auto elim: list.rel_cases)
next
  case (Suc n)
  then obtain x xs' y ys' where xs_def[simp]: "xs = x # xs'" and ys_def[simp]: "ys = y # ys'"
    by (auto elim: list.rel_cases)
  show ?case
    using Suc.prems Suc.IH[of xs' ys']
    by force
qed

lemma list_all2_rel_prod_fst_hd:
  assumes "list_all2 (rel_prod R1 R2) xs ys" and "xs \<noteq> [] \<or> ys \<noteq> []"
  shows "R1 (fst (hd xs)) (fst (hd ys)) \<and> R2 (snd (hd xs)) (snd (hd ys))"
  using assms
  by (auto simp: rel_prod_sel elim: list.rel_cases)

lemma list_all2_rel_prod_fst_last:
  assumes "list_all2 (rel_prod R1 R2) xs ys" and "xs \<noteq> [] \<or> ys \<noteq> []"
  shows "R1 (fst (last xs)) (fst (last ys)) \<and> R2 (snd (last xs)) (snd (last ys))"
proof -
  have "xs \<noteq> []" and "ys \<noteq> []"
    using assms by (auto elim: list.rel_cases)
  moreover have "length xs = length ys"
    by (rule assms(1)[THEN list_all2_lengthD])
  ultimately show ?thesis
    using list_all2_rel_prod_nth[OF assms(1)]
    by (simp add: last_conv_nth)
qed

lemma list_all_nthD[intro]: "list_all P xs \<Longrightarrow> n < length xs \<Longrightarrow> P (xs ! n)"
  by (simp add: list_all_length)

lemma "list_all P xs \<Longrightarrow> \<forall>x\<in> set xs. P x"
  using list_all_iff list.pred_set
  by (simp add: list_all_iff)


lemma list_all_map_of_SomeD:
  assumes "list_all P kvs" and "map_of kvs k = Some v"
  shows "P (k, v)"
  using assms
  unfolding list.pred_set
  by (auto dest: map_of_SomeD)

lemma list_all_not_nthD:"list_all P xs \<Longrightarrow> \<not> P (xs ! n) \<Longrightarrow> length xs \<le> n"
proof (induction xs arbitrary: n)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  then show ?case
    by (cases n) simp_all
qed

lemma list_all_butlast_not_nthD: "list_all P (butlast xs) \<Longrightarrow> \<not> P (xs ! n) \<Longrightarrow> length xs \<le> Suc n"
  using list_all_not_nthD[of _ "butlast xs" for xs, simplified]
  by (smt (z3) One_nat_def Suc_pred le_Suc_eq length_butlast length_greater_0_conv less_Suc_eq list.pred_inject(1) list_all_not_nthD not_le nth_butlast)

lemma list_all_replicateI[intro]: "P x \<Longrightarrow> list_all P (replicate n x)"
  unfolding list.pred_set
  by simp

lemma map_eq_append_replicate_conv:
  assumes "map f xs = replicate n x @ ys"
  shows "map f (take n xs) = replicate n x"
  using assms
  by (metis append_eq_conv_conj length_replicate take_map)

lemma map_eq_replicate_imp_list_all_const:
  "map f xs = replicate n x \<Longrightarrow> n = length xs \<Longrightarrow> list_all (\<lambda>y. f y = x) xs"
  by (induction xs arbitrary: n) simp_all

lemma map_eq_replicateI: "length xs = n \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> f x = c) \<Longrightarrow> map f xs = replicate n c"
  by (induction xs arbitrary: n) auto

lemma list_all_dropI[intro]: "list_all P xs \<Longrightarrow> list_all P (drop n xs)"
  by (metis append_take_drop_id list_all_append)


section \<open>Non-empty list\<close>

type_synonym 'a nlist = "'a \<times> 'a list"

end
