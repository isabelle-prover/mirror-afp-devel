
section \<open>Lemmas on list operations\<close>

theory Even_More_List
  imports
    Main
begin

lemma replicate_numeral [simp]: "replicate (numeral k) x = x # replicate (pred_numeral k) x"
  by (simp add: numeral_eq_Suc)

lemma list_exhaust_size_gt0:
  assumes "\<And>a list. y = a # list \<Longrightarrow> P"
  shows "0 < length y \<Longrightarrow> P"
  apply (cases y)
   apply simp
  apply (rule assms)
  apply fastforce
  done

lemma list_exhaust_size_eq0:
  assumes "y = [] \<Longrightarrow> P"
  shows "length y = 0 \<Longrightarrow> P"
  apply (cases y)
   apply (rule assms)
   apply simp
  apply simp
  done

lemma size_Cons_lem_eq: "y = xa # list \<Longrightarrow> size y = Suc k \<Longrightarrow> size list = k"
  by auto

lemma takeWhile_take_has_property:
  "n \<le> length (takeWhile P xs) \<Longrightarrow> \<forall>x \<in> set (take n xs). P x"
  by (induct xs arbitrary: n; simp split: if_split_asm) (case_tac n, simp_all)

lemma takeWhile_take_has_property_nth:
  "\<lbrakk> n < length (takeWhile P xs) \<rbrakk> \<Longrightarrow> P (xs ! n)"
  by (induct xs arbitrary: n; simp split: if_split_asm) (case_tac n, simp_all)

lemma takeWhile_replicate:
  "takeWhile f (replicate len x) = (if f x then replicate len x else [])"
  by (induct_tac len) auto

lemma takeWhile_replicate_empty:
  "\<not> f x \<Longrightarrow> takeWhile f (replicate len x) = []"
  by (simp add: takeWhile_replicate)

lemma takeWhile_replicate_id:
  "f x \<Longrightarrow> takeWhile f (replicate len x) = replicate len x"
  by (simp add: takeWhile_replicate)

lemma nth_rev: "n < length xs \<Longrightarrow> rev xs ! n = xs ! (length xs - 1 - n)"
  using rev_nth by simp

lemma nth_rev_alt: "n < length ys \<Longrightarrow> ys ! n = rev ys ! (length ys - Suc n)"
  by (simp add: nth_rev)

lemma hd_butlast: "length xs > 1 \<Longrightarrow> hd (butlast xs) = hd xs"
  by (cases xs) auto

lemma upt_add_eq_append':
  assumes "i \<le> j" and "j \<le> k"
  shows "[i..<k] = [i..<j] @ [j..<k]"
  using assms le_Suc_ex upt_add_eq_append by blast

lemma split_upt_on_n:
  "n < m \<Longrightarrow> [0 ..< m] = [0 ..< n] @ [n] @ [Suc n ..< m]"
  by (metis append_Cons append_Nil less_Suc_eq_le less_imp_le_nat upt_add_eq_append'
            upt_rec zero_less_Suc)

lemma length_takeWhile_less:
  "\<exists>x\<in>set xs. \<not> P x \<Longrightarrow> length (takeWhile P xs) < length xs"
  by (induct xs) (auto split: if_splits)

lemma drop_eq_mono:
  assumes le: "m \<le> n"
  assumes drop: "drop m xs = drop m ys"
  shows "drop n xs = drop n ys"
proof -
  have ex: "\<exists>p. n = p + m" by (rule exI[of _ "n - m"]) (simp add: le)
  then obtain p where p: "n = p + m" by blast
  show ?thesis unfolding p drop_drop[symmetric] drop by simp
qed

lemma drop_Suc_nth:
  "n < length xs \<Longrightarrow> drop n xs = xs!n # drop (Suc n) xs"
  by (simp add: Cons_nth_drop_Suc)

lemma and_len: "xs = ys \<Longrightarrow> xs = ys \<and> length xs = length ys"
  by auto

lemma tl_if: "tl (if p then xs else ys) = (if p then tl xs else tl ys)"
  by auto

lemma hd_if: "hd (if p then xs else ys) = (if p then hd xs else hd ys)"
  by auto

lemma if_single: "(if xc then [xab] else [an]) = [if xc then xab else an]"
  by auto

\<comment> \<open>note -- \<open>if_Cons\<close> can cause blowup in the size, if \<open>p\<close> is complex, so make a simproc\<close>
lemma if_Cons: "(if p then x # xs else y # ys) = If p x y # If p xs ys"
  by auto

lemma list_of_false:
  "True \<notin> set xs \<Longrightarrow> xs = replicate (length xs) False"
  by (induct xs, simp_all)

end
