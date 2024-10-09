theory Valid_List_Util
  imports List_Lexorder_Util List_Lexorder_NS Valid_List
begin

section \<open>Order Equivalence\<close>

lemma valid_list_list_less_equiv_list_less_ns:
  assumes "valid_list s1"
  and     "valid_list s2"
shows "s1 < s2 = list_less_ns s1 s2"
proof
  assume "s1 < s2"
  hence "s1 \<noteq> s2"
    by simp
  with valid_list_neqE[OF assms(1,2)]
  obtain x y as bs cs where
    "s1 = as @ x # bs" "s2 = as @ y # cs" "x \<noteq> y"
    by blast
  hence "x < y"
    by (metis \<open>s1 < s2\<close> linorder_less_linear list_less_ex order_less_imp_not_less)
  then have "list_less_ns_ex s1 s2"
    using \<open>s1 = as @ x # bs\<close> \<open>s2 = as @ y # cs\<close> list_less_ns_ex_def by fastforce
  then show "list_less_ns s1 s2"
    by (simp add: list_less_ns_alt_def)
next
  assume "list_less_ns s1 s2"
  hence "s1 \<noteq> s2"
    by fastforce
  with valid_list_neqE[OF assms(1,2)]
  obtain x y as bs cs where
    "s1 = as @ x # bs" "s2 = as @ y # cs" "x \<noteq> y"
    by blast
  hence "x < y"
    by (metis \<open>list_less_ns s1 s2\<close> list.distinct(1) list.sel(1) list_less_ns_app_same
              list_less_ns_recurse)
  then show "s1 < s2"
    using \<open>s1 = as @ x # bs\<close> \<open>s2 = as @ y # cs\<close> list_less_ex by fastforce
qed

lemma valid_list_list_less_eq_equiv_list_less_eq_ns:
  assumes "valid_list s1"
  and     "valid_list s2"
shows "s1 \<le> s2 = list_less_eq_ns s1 s2"
  by (simp add: assms order_le_less ordlistns.le_less valid_list_list_less_equiv_list_less_ns)


section \<open>Classical Lexicographical Order\<close>

lemma valid_list_list_less_imp:
  assumes "valid_list (xs @ [bot])"
  and     "valid_list (ys @ [bot])"
  and     "(xs @ [bot]) < (ys @ [bot])"
shows "xs < ys"
proof -
  from assms(3)
  have "xs @ [bot] \<noteq> ys @ [bot]"
    by fastforce
  with valid_list_neqE[OF assms(1,2)]
  obtain x y as bs cs where
    "xs @ [bot] = as @ x # bs" "ys @ [bot] = as @ y # cs" "x \<noteq> y"
    by blast
  hence "x < y"
    by (metis assms(3) linorder_less_linear list_less_ex order_less_imp_not_less)
  then show ?thesis
    by (metis \<open>xs @ [bot] = as @ x # bs\<close> \<open>ys @ [bot] = as @ y # cs\<close> append_self_conv
              bot.extremum_strict butlast.simps(2) butlast_append last_snoc list_less_ex
              list_neq_rc1)
qed

lemma strict_mono_on_list_less_map:
  fixes \<alpha> :: "'a :: preorder \<Rightarrow> 'b :: ord"
  assumes "strict_mono_on A \<alpha>"
  and     "set xs \<subseteq> A"
  and     "set ys \<subseteq> A"
  and     "xs < ys"
shows "(map \<alpha> xs) < (map \<alpha> ys)"
  using assms(2-4)
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case
    using list_le_def by fastforce
next
  case (Cons a xs)
  note IH = this

  have "\<exists>z zs. a \<le> z \<and> ys = z # zs"
    by (metis Cons_less_Cons IH(4) dual_order.refl dual_order.strict_iff_not neq_Nil_conv
              not_less_Nil)
  then obtain z zs where
    "a \<le> z" "ys = z # zs"
    by blast
  then show ?case
    using IH assms(1) strict_mono_onD by fastforce
qed

lemma strict_mono_list_less_map:
  assumes "strict_mono \<alpha>"
  and     "xs < ys"
shows "map \<alpha> xs < map \<alpha> ys"
  using assms(1) assms(2) strict_mono_on_list_less_map by blast

lemma strict_mono_on_map_list_less:
  fixes \<alpha> :: "'a :: linorder \<Rightarrow> 'b :: order"
  assumes "strict_mono_on A \<alpha>"
  and     "set xs \<subseteq> A"
  and     "set ys \<subseteq> A"
  and     "(map \<alpha> xs) < (map \<alpha> ys)"
shows "xs < ys"
  using assms(2-4)
proof (induct xs arbitrary: ys)
case Nil
  then show ?case
    using list_le_def by fastforce
next
  case (Cons a xs)
  note IH = this

  have "ys = [] \<or> (\<exists>b zs. ys = b # zs)"
    using neq_Nil_conv by blast
  moreover
  have "ys = [] \<Longrightarrow> ?case"
    using Cons.prems by auto
  moreover
  have "\<exists>b zs. ys = b # zs \<Longrightarrow> ?case"
    by (metis IH(2-4) assms(1) linorder_neq_iff order_less_asym strict_mono_on_list_less_map)
  ultimately show ?case
    by blast
qed

lemma strict_mono_map_list_less:
  fixes \<alpha> :: "'a :: linorder \<Rightarrow> 'b :: order"
  assumes "strict_mono \<alpha>"
  and     "(map \<alpha> xs) < (map \<alpha> ys)"
shows "xs < ys"
  using assms(1) assms(2) strict_mono_on_map_list_less by blast

section \<open>Non-standard Lexicographical Ordering\<close>

lemma sorted_list_less_ns:
  assumes "sorted (a # bs @ [c])"
  and     "c < d"
shows "list_less_ns (a # bs @ [c, d] @ xs) (bs @ [c, d] @ ys)"
  using assms
proof (induct bs arbitrary: a)
  case Nil
  then show ?case
    by (metis append_Cons append_Nil le_less list_less_ns_cons_diff list_less_ns_cons_same sorted2)
next
  case (Cons a bs x)
  note IH = this

  from IH(2)
  have "sorted (a # bs @ [c])"
    by simp
  with IH(1)[OF _ assms(2)]
  have "list_less_ns (a # bs @ [c, d] @ xs) (bs @ [c, d] @ ys)" .
  with sorted_nth_mono[OF IH(2), of 0 "Suc 0", simplified]
  show ?case
    by (simp add: list_less_ns_cons)
qed

lemma rev_sorted_list_less_ns:
  assumes "sorted (rev (a # bs @ [c]))"
  and     "c > d"
shows "list_less_ns (bs @ [c, d] @ xs) (a # bs @ [c, d] @ ys)"
  using assms
proof (induct bs arbitrary: a)
  case Nil
  then show ?case
    using list_less_ns_cons list_less_ns_cons_diff by fastforce
next
  case (Cons a bs x)
  note IH = this

  from IH(2)
  have "sorted (rev (a # bs @ [c]))"
    by (simp add: sorted_append)
  with IH(1)[OF _ assms(2)]
  have "list_less_ns (bs @ [c, d] @ xs) (a # bs @ [c, d] @ ys)" .
  with sorted_rev_nth_mono[OF IH(2), of 0 "Suc 0", simplified]
  show ?case
    using list_less_ns_cons by auto
qed

lemma sorted_cons_list_less_ns:
  assumes "sorted (a # bs)"
  shows "list_less_ns (a # bs) bs"
  using assms
proof (induct bs arbitrary: a)
case Nil
  then show ?case
    by (simp add: list_less_ns_nil)
next
  case (Cons a bs x)
  note IH = this

  from IH(2)
  have "sorted (a # bs)"
    by simp
  with IH(1)
  have "list_less_ns (a # bs) bs" .
  with sorted_nth_mono[OF IH(2), of 0 "Suc 0", simplified]
  show ?case
    by (simp add: list_less_ns_cons)
qed

end