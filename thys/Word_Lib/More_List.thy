
section \<open>Lemmas on list operations\<close>

theory More_List
  imports
    Main
    "HOL-Library.Sublist"
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

lemma same_length_is_parallel:
  assumes len: "\<forall>y \<in> set as. length y = x"
  shows  "\<forall>x \<in> set as. \<forall>y \<in> set as - {x}. x \<parallel> y"
proof (rule, rule)
  fix x y
  assume xi: "x \<in> set as" and yi: "y \<in> set as - {x}"
  from len obtain q where len': "\<forall>y \<in> set as. length y = q" ..

  show "x \<parallel> y"
  proof (rule not_equal_is_parallel)
    from xi yi show "x \<noteq> y" by auto
    from xi yi len' show "length x = length y" by (auto dest: bspec)
  qed
qed

lemma sublist_equal_part:
  "prefix xs ys \<Longrightarrow> take (length xs) ys = xs"
  by (clarsimp simp: prefix_def)

lemma prefix_length_less:
  "strict_prefix xs ys \<Longrightarrow> length xs < length ys"
  apply (clarsimp simp: strict_prefix_def)
  apply (frule prefix_length_le)
  apply (rule ccontr, simp)
  apply (clarsimp simp: prefix_def)
  done

lemmas take_less = take_strict_prefix

lemma not_prefix_longer:
  "\<lbrakk> length xs > length ys \<rbrakk> \<Longrightarrow> \<not> prefix xs ys"
  by (clarsimp dest!: prefix_length_le)

lemma map_prefixI:
  "prefix xs ys \<Longrightarrow> prefix (map f xs) (map f ys)"
  by (clarsimp simp: prefix_def)

lemma list_all2_induct_suffixeq [consumes 1, case_names Nil Cons]:
  assumes lall: "list_all2 Q as bs"
  and     nilr: "P [] []"
  and    consr: "\<And>x xs y ys.
  \<lbrakk>list_all2 Q xs ys; Q x y; P xs ys; suffix (x # xs) as; suffix (y # ys) bs\<rbrakk>
  \<Longrightarrow> P (x # xs) (y # ys)"
  shows  "P as bs"
proof -
  define as' where "as' == as"
  define bs' where "bs' == bs"

  have "suffix as as' \<and> suffix bs bs'" unfolding as'_def bs'_def by simp
  then show ?thesis using lall
  proof (induct rule: list_induct2 [OF list_all2_lengthD [OF lall]])
    case 1 show ?case by fact
  next
    case (2 x xs y ys)

    show ?case
    proof (rule consr)
      from "2.prems" show "list_all2 Q xs ys" and "Q x y" by simp_all
      then show "P xs ys" using "2.hyps" "2.prems" by (auto dest: suffix_ConsD)
      from "2.prems" show "suffix (x # xs) as" and "suffix (y # ys) bs"
      by (auto simp: as'_def bs'_def)
    qed
  qed
qed

lemma take_prefix:
  "(take (length xs) ys = xs) = prefix xs ys"
proof (induct xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case Cons then show ?case by (cases ys) auto
qed

end
