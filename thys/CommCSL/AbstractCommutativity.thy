section \<open>Soundness of CommCSL\<close>

subsection \<open>Abstract Commutativity\<close>

theory AbstractCommutativity
  imports Main CommCSL "HOL-Library.Multiset"
begin

datatype ('i, 'a, 'b) action = Shared (get_s: 'a) | Unique (get_i: 'i) (get_u: 'b)

text \<open>We consider a family of unique actions indexed by 'i\<close>

lemma sabstract:
  assumes "all_axioms \<alpha> sact spre uact upre"
  shows "\<alpha> v = \<alpha> v' \<and> spre sarg sarg' \<Longrightarrow> \<alpha> (sact v sarg) = \<alpha> (sact v' sarg')"
  using all_axioms_def[of \<alpha> sact spre uact upre] assms by fast

lemma uabstract:
  assumes "all_axioms \<alpha> sact spre uact upre"
  shows "\<alpha> v = \<alpha> v' \<and> upre i uarg uarg' \<Longrightarrow> \<alpha> (uact i v uarg) = \<alpha> (uact i v' uarg')"
  using all_axioms_def[of \<alpha> sact spre uact upre] assms by fast

lemma spre_refl:
  assumes "all_axioms \<alpha> sact spre uact upre"
  shows "spre sarg sarg' \<Longrightarrow> spre sarg' sarg'"
  using all_axioms_def[of \<alpha> sact spre uact upre] assms by fast

lemma upre_refl:
  assumes "all_axioms \<alpha> sact spre uact upre"
  shows "upre i uarg uarg' \<Longrightarrow> upre i uarg' uarg'"
  using all_axioms_def[of \<alpha> sact spre uact upre] assms by fast

lemma ss_com:
  assumes "all_axioms \<alpha> sact spre uact upre"
  shows "\<alpha> v = \<alpha> v' \<Longrightarrow> spre sarg sarg \<and> spre sarg' sarg' \<Longrightarrow> \<alpha> (sact (sact v sarg) sarg') = \<alpha> (sact (sact v' sarg') sarg)"
  using all_axioms_def[of \<alpha> sact spre uact upre] assms by blast

lemma su_com:
  assumes "all_axioms \<alpha> sact spre uact upre"
  shows "\<alpha> v = \<alpha> v' \<Longrightarrow> spre sarg sarg \<and> upre i uarg uarg \<Longrightarrow> \<alpha> (sact (uact i v uarg) sarg) = \<alpha> (uact i (sact v' sarg) uarg)"
  using all_axioms_def[of \<alpha> sact spre uact upre] assms by blast

lemma uu_com:
  assumes "all_axioms \<alpha> sact spre uact upre"
      and "i \<noteq> i'"
      and "\<alpha> v = \<alpha> v'"
      and "upre i' uarg' uarg'"
      and "upre i uarg uarg"
    shows "\<alpha> (uact i' (uact i v uarg) uarg') = \<alpha> (uact i (uact i' v' uarg') uarg)"
proof -
  have "\<And>v v' uarg uarg' i i'.
             i \<noteq> i' \<and> \<alpha> v = \<alpha> v' \<and> upre i uarg uarg \<and> upre i' uarg' uarg' \<longrightarrow> \<alpha> (uact i' (uact i v uarg) uarg') = \<alpha> (uact i (uact i' v' uarg') uarg)"
  using all_axioms_def[of \<alpha> sact spre uact upre] assms(1)
  by blast
  then show ?thesis
    using assms(2) assms(3) assms(4) assms(5) by blast
qed


definition PRE_shared :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "PRE_shared spre sargs sargs' \<longleftrightarrow> (\<exists>ms. image_mset fst ms = sargs \<and> image_mset snd ms = sargs' \<and> (\<forall>x \<in># ms. spre (fst x) (snd x)))"

lemma PRE_shared_same_size:
  assumes "PRE_shared spre sargs sargs'"
  shows "size sargs = size sargs'"
proof -
  obtain ms where "image_mset fst ms = sargs \<and> image_mset snd ms = sargs' \<and> (\<forall>x \<in># ms. spre (fst x) (snd x))"
    by (metis PRE_shared_def assms)
  then have "size sargs = size ms \<and> size ms = size sargs'"
    by force
  then show ?thesis
    by simp
qed

definition is_Unique :: "('i, 'a, 'b) action \<Rightarrow> bool" where
  "is_Unique a \<longleftrightarrow> \<not> is_Shared a"

definition is_Unique_i :: "'i \<Rightarrow> ('i, 'a, 'b) action \<Rightarrow> bool" where
  "is_Unique_i i a \<longleftrightarrow> is_Unique a \<and> get_i a = i"

definition possible_sequence :: "'a multiset \<Rightarrow> ('i \<Rightarrow> 'b list) \<Rightarrow> ('i, 'a, 'b) action list \<Rightarrow> bool" where
  "possible_sequence sargs uargs s \<longleftrightarrow> ((\<forall>i. uargs i = map get_u (filter (is_Unique_i i) s)) \<and> sargs = image_mset get_s (filter_mset is_Shared (mset s)))"

lemma possible_sequenceI:
  assumes "\<And>i. uargs i = map get_u (filter (is_Unique_i i) s)"
      and "sargs = image_mset get_s (filter_mset is_Shared (mset s))"
    shows "possible_sequence sargs uargs s"
  using assms(1) assms(2) possible_sequence_def by blast

fun remove_at_index :: "nat \<Rightarrow> 'd list \<Rightarrow> 'd list" where
  "remove_at_index _ [] = []"
| "remove_at_index 0 (x # xs) = xs"
| "remove_at_index (Suc n) (x # xs) = x # (remove_at_index n xs)"

lemma remove_at_index:
  assumes "n < length l"
  shows "length (remove_at_index n l) = length l - 1"
    and "i \<ge> 0 \<and> i < n \<Longrightarrow> remove_at_index n l ! i = l ! i"
    and "i \<ge> n \<and> i < length l - 1 \<Longrightarrow> remove_at_index n l ! i = l ! (i + 1)"
  using assms
proof (induct l arbitrary: n i)
  case (Cons a l)
  {
    case 1
    then show ?case
    proof (cases n)
      case (Suc k)
      then show ?thesis
        using "1" Cons.hyps(1) by force
    qed (simp)
  next
    case 2
    then show ?case
    proof (cases n)
      case (Suc k)
      then show ?thesis
        using "2.prems"(1) "2.prems"(2) Cons.hyps(2) Suc_less_eq2 less_Suc_eq_0_disj by auto
    qed (simp)
  next
    case 3
    then show ?case
    proof (cases n)
      case (Suc k)
      then have "remove_at_index (Suc k) (a # l) ! i = (a # l) ! (i + 1)"
        apply (cases i)
        using "3.prems"(1) apply blast
        using "3.prems"(1) Cons.hyps(3) Suc_less_eq2 by auto
      then show "remove_at_index n (a # l) ! i = (a # l) ! (i + 1)"
        using Suc by blast
    qed (simp)
  }
qed (auto)

fun insert_at :: "nat \<Rightarrow> 'd \<Rightarrow> 'd list \<Rightarrow> 'd list" where
  "insert_at 0 x l = x # l"
| "insert_at _ x [] = [x]"
| "insert_at (Suc n) x (h # xs) = h # (insert_at n x xs)"

lemma insert_at_index:
  assumes "n \<le> length l"
  shows "length (insert_at n x l) = length l + 1"
    and "i \<ge> 0 \<and> i < n \<Longrightarrow> insert_at n x l ! i = l ! i"
    and "n \<ge> 0 \<Longrightarrow> insert_at n x l ! n = x"
    and "i > n \<and> i < length l + 1 \<Longrightarrow> insert_at n x l ! i = l ! (i - 1)"
  using assms
proof (induct l arbitrary: n i)
  case (Cons a l)
  {
    case 1
    then show ?case by (cases n) (simp_all add: Cons.hyps(1))
  next
    case 2
    then show ?case apply (cases n)
       apply blast
      using Cons.hyps(2) less_Suc_eq_0_disj by force
  next
    case 3
    then show ?case apply (cases n)
       apply simp
      by (simp add: Cons.hyps(3))
  next
    case 4
    then show ?case apply (cases n)
       apply simp
      by (metis (no_types, lifting) "4.prems"(1) "4.prems"(2) Cons.hyps(4) Nat.add_0_right One_nat_def Suc_le_length_iff Suc_less_eq Suc_pred add_Suc_right bot_nat_0.not_eq_extremum insert_at.simps(3) less_zeroE list.inject list.size(4) nat.simps(3) nth_Cons' nth_Cons_Suc)
  }
qed (simp_all)

lemma list_ext:
  assumes "length a = length b"
      and "\<And>i. i \<ge> 0 \<and> i < length a \<Longrightarrow> a ! i = b ! i"
    shows "a = b"
  by (meson assms(1) assms(2) bot_nat_0.extremum nth_equalityI)

lemma mset_remove_index:
  assumes "i \<ge> 0 \<and> i < length l"
  shows "mset l = mset (remove_at_index i l) + {# l ! i #}"
  using assms
proof (induct l arbitrary: i)
  case (Cons a l)
  then show ?case
  proof (cases i)
    case (Suc k)
    then show ?thesis
      using Cons.hyps Cons.prems by force
  qed (auto)
qed (simp)

lemma filter_remove:
  assumes "k \<ge> 0 \<and> k < length s"
      and "\<not> P (s ! k)"
    shows "filter P (remove_at_index k s) = filter P s"
  using assms
proof (induct k arbitrary: s)
  case 0
  then have "s = hd s # tl s"
    by simp
  then show ?case
    by (metis "0.prems"(2) filter.simps(2) nth_Cons_0 remove_at_index.simps(2))
next
  case (Suc k)
  then show ?case
    by (cases s) simp_all
qed

lemma exists_index_in_sequence_shared:
  assumes "a \<in># sargs"
      and "possible_sequence sargs uargs s"
    shows "\<exists>i. i \<ge> 0 \<and> i < length s \<and> s ! i = Shared a \<and> possible_sequence (sargs - {# a #}) uargs (remove_at_index i s)"
proof -
  have "a \<in># image_mset get_s (filter_mset is_Shared (mset s))"
    by (metis assms(1) assms(2) possible_sequence_def)
  then have "Shared a \<in> set s"
    by fastforce
  then obtain i where "i \<ge> 0 \<and> i < length s \<and> s ! i = Shared a"
    by (meson bot_nat_0.extremum in_set_conv_nth)
  let ?s = "remove_at_index i s"
  have "sargs - {# a #} = image_mset get_s (filter_mset is_Shared (mset ?s))"
  proof -
    have "sargs = image_mset get_s (filter_mset is_Shared (mset s))"
      using possible_sequence_def assms(2) by blast
    moreover have "mset s = mset ?s + {# Shared a #}"
      by (metis \<open>0 \<le> i \<and> i < length s \<and> s ! i = Shared a\<close> mset_remove_index)
    ultimately show ?thesis
      by simp
  qed
  moreover have "\<And>i. uargs i = map get_u (filter (is_Unique_i i) ?s)"
    by (metis \<open>0 \<le> i \<and> i < length s \<and> s ! i = Shared a\<close> action.disc(1) assms(2) filter_remove is_Unique_def is_Unique_i_def possible_sequence_def)
  ultimately show ?thesis
    using \<open>0 \<le> i \<and> i < length s \<and> s ! i = Shared a\<close> possible_sequence_def by blast
qed

lemma head_possible_exists_first_unique:
  assumes "a = hd (uargs j)"
      and "uargs j \<noteq> []"
      and "possible_sequence sargs uargs s"
    shows "\<exists>i. i \<ge> 0 \<and> i < length s \<and> s ! i = Unique j a \<and> (\<forall>k. k \<ge> 0 \<and> k < i \<longrightarrow> \<not> is_Unique_i j (s ! k))"
  using assms
proof (induct s arbitrary: sargs uargs)
  case Nil
  then show ?case by (simp add: possible_sequence_def)
next
  case (Cons x xs)
  then show "\<exists>i\<ge>0. i < length (x # xs) \<and> (x # xs) ! i = Unique j a \<and> (\<forall>k. 0 \<le> k \<and> k < i \<longrightarrow> \<not> is_Unique_i j ((x # xs) ! k))"
  proof (cases x)
    case (Shared sarg)
    moreover have "possible_sequence (sargs - {# sarg #}) uargs xs"
    proof (rule possible_sequenceI)
      show "sargs - {#sarg#} = image_mset get_s (filter_mset is_Shared (mset xs))"
        using Cons.prems(3) action.disc(1) action.sel(1) add_mset_remove_trivial[of sarg ]
          calculation
          filter_mset_add_mset image_mset_add_mset mset.simps(2) possible_sequence_def[of sargs uargs "x # xs"]
        by auto
      fix i show "uargs i = map get_u (filter (is_Unique_i i) xs)"
        using Cons.prems(3) action.disc(1) calculation filter_remove is_Unique_def is_Unique_i_def
          le_numeral_extra(3) length_greater_0_conv list.discI nth_Cons_0 possible_sequence_def[of sargs uargs "x # xs"]
          remove_at_index.simps(2)
        by metis
    qed
    then obtain i where "i \<ge> 0 \<and> i < length xs \<and> xs ! i = Unique j a \<and> (\<forall>k. 0 \<le> k \<and> k < i \<longrightarrow> \<not> is_Unique_i j (xs ! k))"
      using Cons.hyps[of uargs] Cons.prems(1) Cons.prems(2) by auto
    moreover have "\<And>k. 0 \<le> k \<and> k < i + 1 \<longrightarrow> \<not> is_Unique_i j ((x # xs) ! k)"
    proof 
      fix k assume "0 \<le> k \<and> k < i + 1"
      then show "\<not> is_Unique_i j ((x # xs) ! k)"
        apply (cases k)
         apply (simp add: Shared is_Unique_def is_Unique_i_def)
        by (simp add: calculation(2))
    qed
    ultimately show ?thesis
      by (metis Suc_eq_plus1 Suc_less_eq bot_nat_0.extremum length_Cons nth_Cons_Suc)
  next
    case (Unique k uarg)
    then show ?thesis
    proof (cases "j = k")
      case True
      then have "uargs j = map get_u (filter (is_Unique_i j) (x # xs))"
        by (meson Cons.prems(3) possible_sequence_def)
      then have "uarg = a"
        by (simp add: True Unique Cons.prems(1) is_Unique_def is_Unique_i_def)
      then show ?thesis
        using True Unique by fastforce
    next
      case False
      moreover have "possible_sequence sargs (uargs(k := tl (uargs k))) xs"
      proof (rule possible_sequenceI)
        show "sargs = image_mset get_s (filter_mset is_Shared (mset xs))"
          by (metis (mono_tags, lifting) Cons.prems(3) Unique action.disc(2) filter_mset_add_mset mset.simps(2) possible_sequence_def)
        fix i show "(uargs(k := tl (uargs k))) i = map get_u (filter (is_Unique_i i) xs)"
        proof (cases "i = k")
          case True
          then show ?thesis
            using Cons.prems(3) Unique action.disc(2) action.sel(2) filter.simps(2) fun_upd_same
              is_Unique_def is_Unique_i_def list.sel(3) map_tl possible_sequence_def[of sargs uargs "x # xs"]
            by metis
        next
          case False
          then show ?thesis
            using Cons.prems(3) Unique action.sel(2) filter_remove fun_upd_apply is_Unique_i_def
            le_numeral_extra(3) length_greater_0_conv list.discI nth_Cons_0 possible_sequence_def[of sargs uargs "x # xs"]
            remove_at_index.simps(2) by metis
        qed
      qed
      then obtain i where "i \<ge> 0 \<and> i < length xs \<and> xs ! i = Unique j a \<and> (\<forall>k. 0 \<le> k \<and> k < i \<longrightarrow> \<not> is_Unique_i j (xs ! k))"
        by (metis Cons.hyps Cons.prems(1) Cons.prems(2) calculation fun_upd_other)
      moreover have "\<And>k. 0 \<le> k \<and> k < i + 1 \<longrightarrow> \<not> is_Unique_i j ((x # xs) ! k)"
      proof 
        fix k assume "0 \<le> k \<and> k < i + 1"
        then show "\<not> is_Unique_i j ((x # xs) ! k)"
          apply (cases k)
           apply (metis False Unique action.sel(2) is_Unique_i_def nth_Cons_0)
          by (simp add: calculation(2))
      qed
      ultimately show ?thesis
        by (metis Suc_eq_plus1 Suc_less_eq bot_nat_0.extremum length_Cons nth_Cons_Suc)
    qed
  qed
qed

lemma remove_at_index_filter:
  assumes "i \<ge> 0 \<and> i < length s \<and> P (s ! i)"
      and "\<And>j. j \<ge> 0 \<and> j < i \<Longrightarrow> \<not> P (s ! j)"
    shows "tl (map get_u (filter P s)) = map get_u (filter P (remove_at_index i s))"
  using assms
proof (induct s arbitrary: i)
  case (Cons a s)
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using Cons.prems(1) by auto
  next
    case (Suc k)
    then have "tl (map get_u (filter P s)) = map get_u (filter P (remove_at_index k s))"
      apply (cases s)
       apply simp
      by (metis Cons.hyps Cons.prems(1) Cons.prems(2) Suc_less_eq bot_nat_0.extremum length_Cons nth_Cons_Suc)
    then show ?thesis
      by (metis Cons.prems(2) Suc bot_nat_0.extremum filter.simps(2) nth_Cons_0 remove_at_index.simps(3) zero_less_Suc)
  qed
qed (simp)

definition tail_kth where
  "tail_kth uargs k = uargs(k := tl (uargs k))"

lemma exists_index_in_sequence_unique:
  assumes "a = hd (uargs k)"
      and "uargs k \<noteq> []"
      and "possible_sequence sargs uargs s"
    shows "\<exists>i. i \<ge> 0 \<and> i < length s \<and> s ! i = Unique k a \<and> possible_sequence sargs (tail_kth uargs k) (remove_at_index i s)
          \<and> (\<forall>j. j \<ge> 0 \<and> j < i \<longrightarrow> \<not> is_Unique_i k (s ! j))"
proof -
  obtain i where "i \<ge> 0 \<and> i < length s \<and> s ! i = Unique k a \<and> (\<forall>j. j \<ge> 0 \<and> j < i \<longrightarrow> \<not> is_Unique_i k (s ! j))"
    by (metis assms(1) assms(2) assms(3) head_possible_exists_first_unique)
  let ?s = "remove_at_index i s"
  have "sargs = image_mset get_s (filter_mset is_Shared (mset ?s))" 
    by (metis \<open>0 \<le> i \<and> i < length s \<and> s ! i = Unique k a \<and> (\<forall>j. 0 \<le> j \<and> j < i \<longrightarrow> \<not> is_Unique_i k (s ! j))\<close> action.disc(2) add.right_neutral assms(3) filter_single_mset filter_union_mset mset_remove_index possible_sequence_def)
  moreover have "tl (uargs k) = map get_u (filter (is_Unique_i k) ?s)"
  proof -
    have "uargs k = map get_u (filter (is_Unique_i k) s)"
      by (meson assms(3) possible_sequence_def)
    then show ?thesis
      by (metis \<open>0 \<le> i \<and> i < length s \<and> s ! i = Unique k a \<and> (\<forall>j. 0 \<le> j \<and> j < i \<longrightarrow> \<not> is_Unique_i k (s ! j))\<close> action.disc(2) action.sel(2) is_Unique_def is_Unique_i_def remove_at_index_filter)
  qed
  moreover have "possible_sequence sargs (tail_kth uargs k) (remove_at_index i s)"
  proof (rule possible_sequenceI)
    show "sargs = image_mset get_s (filter_mset is_Shared (mset (remove_at_index i s)))"
      by (simp add: calculation(1))
    fix ia show "tail_kth uargs k ia = map get_u (filter (is_Unique_i ia) (remove_at_index i s))"
      by (metis (mono_tags, lifting) \<open>0 \<le> i \<and> i < length s \<and> s ! i = Unique k a \<and> (\<forall>j. 0 \<le> j \<and> j < i \<longrightarrow> \<not> is_Unique_i k (s ! j))\<close> action.sel(2) assms(3) calculation(2) filter_remove fun_upd_other fun_upd_same is_Unique_i_def possible_sequence_def tail_kth_def)
  qed
  ultimately show ?thesis
    using \<open>0 \<le> i \<and> i < length s \<and> s ! i = Unique k a \<and> (\<forall>j. 0 \<le> j \<and> j < i \<longrightarrow> \<not> is_Unique_i k (s ! j))\<close> by blast
qed

lemma possible_sequence_where_is_unique:
  assumes "possible_sequence sargs uargs (Unique k a # s)"
  shows "a = hd (uargs k)"
proof -
  let ?s = "Unique k a # s"
  have "Unique k a = hd (filter is_Unique ?s)"
    by (simp add: is_Unique_def)
  then have "a = hd (map get_u (filter is_Unique ?s))"
    by (simp add: is_Unique_def)
  then show ?thesis
    using action.disc(2) action.sel(2) assms filter.simps(2) hd_map is_Unique_def
      is_Unique_i_def list.discI list.sel(1) possible_sequence_def[of sargs uargs "Unique k a # s"]
    by metis
qed

lemma possible_sequence_where_is_shared:
  assumes "possible_sequence sargs uargs (Shared a # s)"
  shows "a \<in># sargs"
proof -
  let ?s = "Shared a # s"
  have "a \<in> set (map get_s (filter is_Shared ?s))"
    by simp
  then show ?thesis
    by (metis (no_types, lifting) assms mset_filter mset_map possible_sequence_def set_mset_mset)
qed


lemma PRE_unique_tlI:
  assumes "PRE_unique upre qa qb"
      and "upre ta tb"
    shows "PRE_unique upre (ta # qa) (tb # qb)"
proof (rule PRE_uniqueI)
  show "length (ta # qa) = length (tb # qb)"
    using PRE_unique_def assms(1) by auto
  fix i
  show "0 \<le> i \<and> i < length (tb # qb) \<Longrightarrow> upre ((ta # qa) ! i) ((tb # qb) ! i)"
  proof (cases i)
    case 0
    then show ?thesis
      using assms(2) by auto
  next
    case (Suc k)
    assume "0 \<le> i \<and> i < length (tb # qb)"
    then have "(ta # qa) ! i = qa ! k \<and> (tb # qb) ! i = qb ! k"
      by (simp add: Suc)
    then show ?thesis using assms(1) PRE_unique_def
      using Suc \<open>0 \<le> i \<and> i < length (tb # qb)\<close> by auto
  qed
qed

fun abstract_pre :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('i \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('i, 'a, 'b) action \<Rightarrow> ('i, 'a, 'b) action \<Rightarrow> bool" where
  "abstract_pre spre upre (Shared sarg) (Shared sarg') \<longleftrightarrow> spre sarg sarg'"
| "abstract_pre spre upre (Unique k uarg) (Unique k' uarg') \<longleftrightarrow> k = k' \<and> upre k uarg uarg'"
| "abstract_pre spre upre _ _ \<longleftrightarrow> False"

definition PRE_sequence :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('i => 'b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('i, 'a, 'b) action list \<Rightarrow> ('i, 'a, 'b) action list \<Rightarrow> bool" where
  "PRE_sequence spre upre s s' \<longleftrightarrow> length s = length s' \<and> (\<forall>i. i \<ge> 0 \<and> i < length s \<longrightarrow> abstract_pre spre upre (s ! i) (s' ! i))"

lemma PRE_sequenceE:
  assumes "PRE_sequence spre upre s s'"
      and "i \<ge> 0 \<and> i < length s"
    shows "abstract_pre spre upre (s ! i) (s' ! i)"
  using PRE_sequence_def assms(1) assms(2) by blast

lemma PRE_sequenceI:
  assumes "length s = length s'"
      and "\<And>i. i \<ge> 0 \<and> i < length s \<Longrightarrow> abstract_pre spre upre (s ! i) (s' ! i)"
    shows "PRE_sequence spre upre s s'"
  by (simp add: PRE_sequence_def assms(1) assms(2))

lemma PRE_sequenceI_rec:
  assumes "PRE_sequence spre upre s s'"
      and "abstract_pre spre upre a b"
    shows "PRE_sequence spre upre (a # s) (b # s')"
  using PRE_sequence_def[of spre upre "a # s" "b # s'"] PRE_sequence_def[of spre upre s s']
  assms(1) assms(2) less_Suc_eq_0_disj length_Cons less_Suc_eq_le nth_Cons_0 nth_Cons_Suc
  by force
  
lemma PRE_sequenceE_rec:
  assumes "PRE_sequence spre upre (a # s) (b # s')"
  shows "PRE_sequence spre upre s s'"
      and "abstract_pre spre upre a b"
  using PRE_sequence_def[of spre upre "a # s" "b # s'"] PRE_sequence_def[of spre upre s s']
  apply (metis Suc_less_eq assms bot_nat_0.extremum diff_Suc_1 length_Cons nth_Cons_Suc)
  by (metis PRE_sequenceE assms length_Cons list.size(3) nth_Cons_0 remdups_adj.simps(1) remdups_adj_length zero_less_Suc)

fun compute :: "('v \<Rightarrow> 'a \<Rightarrow> 'v) \<Rightarrow> ('i \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> ('i, 'a, 'b) action list \<Rightarrow> 'v" where
  "compute sact uact v0 [] = v0"
| "compute sact uact v0 (Shared sarg # s) = sact (compute sact uact v0 s) sarg"
| "compute sact uact v0 (Unique k uarg # s) = uact k (compute sact uact v0 s) uarg"


lemma obtain_other_elem_ms:
  assumes "PRE_shared spre sargs sargs'"
      and "sarg \<in># sargs"
    shows "\<exists>sarg'. sarg' \<in># sargs' \<and> spre sarg sarg' \<and> PRE_shared spre (sargs - {# sarg #}) (sargs' - {# sarg' #})"
proof -
  obtain ms where asm: "image_mset fst ms = sargs \<and> image_mset snd ms = sargs' \<and> (\<forall>x \<in># ms. spre (fst x) (snd x))"
    using PRE_shared_def assms(1) by blast
  then obtain x where "x \<in># ms" "fst x = sarg"
    using assms(2) by auto
  then have "snd x \<in># sargs' \<and> spre sarg (snd x)"
    using asm by force
  moreover have "PRE_shared spre (sargs - {# sarg #}) (sargs' - {# snd x #})"
  proof -
    let ?ms = "ms - {# x #}"
    have "image_mset fst ?ms = (sargs - {# sarg #}) \<and> image_mset snd ?ms = (sargs' - {# snd x #})"
      by (simp add: \<open>fst x = sarg\<close> \<open>x \<in># ms\<close> asm image_mset_Diff)
    moreover have "\<And>y. y \<in># ?ms \<Longrightarrow> spre (fst y) (snd y)"
      by (meson asm in_diffD)
    ultimately show ?thesis
      using PRE_shared_def by blast
  qed
  ultimately show ?thesis
    by blast
qed

lemma exists_aligned_sequence:
  assumes "possible_sequence sargs uargs s"
      and "possible_sequence sargs' uargs' s'"

      and "PRE_shared spre sargs sargs'"
      and "\<And>k. PRE_unique (upre k) (uargs k) (uargs' k)"

    shows "\<exists>s''. possible_sequence sargs' uargs' s'' \<and> PRE_sequence spre upre s s''"
  using assms
proof (induct s arbitrary: sargs uargs sargs' uargs' s')
  case Nil
  then have "sargs = mset [] \<and> (\<forall>k. uargs k = [])"
    by (simp add: possible_sequence_def)
  then have "sargs' = {#} \<and> (\<forall>k. uargs' k = [])"
    by (metis Nil.prems(3) Nil.prems(4) PRE_shared_same_size PRE_unique_def length_0_conv mset.simps(1) size_eq_0_iff_empty)
  then show "\<exists>s''. possible_sequence sargs' uargs' s'' \<and> PRE_sequence spre upre [] s''"
    by (simp add: PRE_sequence_def possible_sequence_def)
next
  case (Cons act s)

  show "\<exists>s''. possible_sequence sargs' uargs' s'' \<and> PRE_sequence spre upre (act # s) s''"
  proof (cases act)
    case (Shared sarg)

    then have "sarg \<in># sargs"
      by (metis Cons.prems(1) possible_sequence_where_is_shared)
    then obtain sarg' where "sarg' \<in># sargs'" "spre sarg sarg'" "PRE_shared spre (sargs - {# sarg #}) (sargs' - {# sarg' #})"
      by (metis Cons.prems(3) obtain_other_elem_ms)
    let ?sargs = "sargs - {# sarg #}"
    let ?sargs' = "sargs' - {# sarg' #}"
    have "possible_sequence ?sargs uargs s"
    proof (rule possible_sequenceI)
      show "\<And>i. uargs i = map get_u (filter (is_Unique_i i) s)"
        using Cons.prems(1) Shared action.disc(1) filter.simps(2) is_Unique_def is_Unique_i_def
          possible_sequence_def[of sargs uargs "act # s"]
        by metis
      have "sargs = image_mset get_s (filter_mset is_Shared (mset(Shared sarg # s)))"
        using Cons.prems(1) Shared possible_sequence_def by blast
      then show "sargs - {#sarg#} = image_mset get_s (filter_mset is_Shared (mset s))" by simp
    qed

    obtain i where "i \<ge> 0 \<and> i < length s' \<and> s' ! i = Shared sarg' \<and> possible_sequence ?sargs' uargs' (remove_at_index i s')"
      by (meson Cons.prems(2) \<open>sarg' \<in># sargs'\<close> exists_index_in_sequence_shared)
    
    then obtain s'' where "possible_sequence ?sargs' uargs' s'' \<and> PRE_sequence spre upre s s''"
      using Cons.hyps Cons.prems(4) \<open>PRE_shared spre (sargs - {#sarg#}) (sargs' - {#sarg'#})\<close> \<open>possible_sequence (sargs - {#sarg#}) uargs s\<close> by blast

    let ?s'' = "Shared sarg' # s''"

    have "possible_sequence sargs' uargs' ?s''"
    proof (rule possible_sequenceI)
      show "\<And>i. uargs' i = map get_u (filter (is_Unique_i i) (Shared sarg' # s''))"
        by (metis \<open>possible_sequence (sargs' - {#sarg'#}) uargs' s'' \<and> PRE_sequence spre upre s s''\<close> action.disc(1) filter.simps(2) is_Unique_def is_Unique_i_def possible_sequence_def)
      show "sargs' = image_mset get_s (filter_mset is_Shared (mset (Shared sarg' # s'')))"
        using \<open>possible_sequence (sargs' - {#sarg'#}) uargs' s'' \<and> PRE_sequence spre upre s s''\<close> \<open>sarg' \<in># sargs'\<close>
          insert_DiffM[of sarg' sargs'] possible_sequence_def[of "sargs' - {#sarg'#}" uargs' s'']
          action.disc(1) action.sel(1) filter_mset_add_mset msed_map_invL mset.simps(2)
        by auto
    qed

    moreover have "PRE_sequence spre upre (act # s) ?s''"
      by (simp add: PRE_sequenceI_rec Shared \<open>possible_sequence (sargs' - {#sarg'#}) uargs' s'' \<and> PRE_sequence spre upre s s''\<close> \<open>spre sarg sarg'\<close>)

    ultimately show "\<exists>s''. possible_sequence sargs' uargs' s'' \<and> PRE_sequence spre upre (act # s) s''" by auto
  next
    case (Unique k uarg)
    then have "hd (uargs k) = uarg"
      by (metis Cons.prems(1) possible_sequence_where_is_unique)
    moreover have "uargs k \<noteq> []"
      by (metis (no_types, lifting) Cons.prems(1) Unique action.disc(2) action.sel(2) dropWhile_eq_Cons_conv dropWhile_eq_self_iff filter.simps(2) is_Unique_def is_Unique_i_def list.map_disc_iff possible_sequence_def)
    ultimately have "uargs k = uarg # tl (uargs k)"
      by fastforce
    moreover have "uargs' k = hd (uargs' k) # tl (uargs' k)"
      by (metis Cons.prems(4) PRE_unique_def calculation length_Cons list.exhaust_sel list.size(3) nat.simps(3))
    ultimately have "upre k uarg (hd (uargs' k))"
      by (metis Cons.prems(4) PRE_unique_def length_greater_0_conv list.simps(3) list.size(3) nth_Cons_0 remdups_adj.simps(1) remdups_adj_length)
    moreover have "PRE_unique (upre k) (tl (uargs k)) (tl (uargs' k))"
      by (metis Cons.prems(4) PRE_unique_implies_tl \<open>uargs k = uarg # tl (uargs k)\<close> \<open>uargs' k = hd (uargs' k) # tl (uargs' k)\<close>)
    moreover have "possible_sequence sargs (tail_kth uargs k) s"
    proof (rule possible_sequenceI)
      show "\<And>i. tail_kth uargs k i = map get_u (filter (is_Unique_i i) s)"
      proof -
        fix i 
        obtain ii where asms: "ii \<ge> 0" "ii < length (act # s) \<and>
           (act # s) ! ii = Unique k uarg \<and>
           possible_sequence sargs (tail_kth uargs k) (remove_at_index ii (act # s)) \<and> (\<forall>j. 0 \<le> j \<and> j < ii \<longrightarrow> \<not> is_Unique_i k ((act # s) ! j))"
          by (metis Cons.prems(1) \<open>hd (uargs k) = uarg\<close> \<open>uargs k \<noteq> []\<close> exists_index_in_sequence_unique)
        then show "tail_kth uargs k i = map get_u (filter (is_Unique_i i) s)"
          by (metis Unique action.disc(2) action.sel(2) bot_nat_0.extremum bot_nat_0.not_eq_extremum is_Unique_def is_Unique_i_def nth_Cons_0 possible_sequence_def remove_at_index.simps(2))
      qed
      show "sargs = image_mset get_s (filter_mset is_Shared (mset s))"
        by (metis (mono_tags, lifting) Cons.prems(1) Unique action.disc(2) filter_mset_add_mset mset.simps(2) possible_sequence_def)
    qed
    let ?uarg' = "hd (uargs' k)"
    
    obtain i where "i \<ge> 0 \<and> i < length s' \<and> s' ! i = Unique k ?uarg' \<and> possible_sequence sargs' (tail_kth uargs' k) (remove_at_index i s')"
      by (metis Cons.prems(2) \<open>uargs' k = hd (uargs' k) # tl (uargs' k)\<close> exists_index_in_sequence_unique list.discI)
    then obtain s'' where "possible_sequence sargs' (tail_kth uargs' k) s'' \<and> PRE_sequence spre upre s s''"
      using Cons.hyps[of sargs "tail_kth uargs k" sargs' "tail_kth uargs' k"] Cons.prems(3) \<open>possible_sequence sargs (tail_kth uargs k) s\<close> calculation(2)
        Cons.prems(4) fun_upd_other fun_upd_same tail_kth_def
      by metis

    let ?s'' = "Unique k (hd (uargs' k)) # s''" 
    have "PRE_sequence spre upre (act # s) ?s''"
      by (simp add: PRE_sequenceI_rec Unique \<open>possible_sequence sargs' (tail_kth uargs' k) s'' \<and> PRE_sequence spre upre s s''\<close> calculation(1))
    moreover have "possible_sequence sargs' uargs' ?s''"
    proof (rule possible_sequenceI)
      show "\<And>i. uargs' i = map get_u (filter (is_Unique_i i) (Unique k (hd (uargs' k)) # s''))"
      proof -
        fix i
        obtain ii where ii_def: "ii \<ge> 0 \<and> ii < length s' \<and>
       s' ! ii = Unique k (hd (uargs' k)) \<and>
       possible_sequence sargs' (tail_kth uargs' k) (remove_at_index ii s') \<and> (\<forall>j. 0 \<le> j \<and> j < ii \<longrightarrow> \<not> is_Unique_i k (s' ! j))"
          by (metis Cons.prems(2) \<open>uargs' k = hd (uargs' k) # tl (uargs' k)\<close> exists_index_in_sequence_unique list.discI)
        then show "uargs' i = map get_u (filter (is_Unique_i i) (Unique k (hd (uargs' k)) # s''))"
          using filter_remove[of ii s' "is_Unique_i i"] remove_at_index_filter[of ii s' "is_Unique_i i"]
            Cons.prems(2) \<open>possible_sequence sargs' (tail_kth uargs' k) s'' \<and> PRE_sequence spre upre s s''\<close>
            \<open>uargs' k = hd (uargs' k) # tl (uargs' k)\<close> action.sel(2) action.sel(3)
            filter.simps(2)[of "is_Unique_i i" "Unique k (hd (uargs' k))" s'']
             is_Unique_i_def list.simps(9)[of get_u]
            possible_sequence_def[of sargs' "tail_kth uargs' k" "remove_at_index ii s'"]
            possible_sequence_def[of sargs' uargs' s']
            possible_sequence_def[of sargs' "tail_kth uargs' k" s''] ii_def
          by metis
      qed
      show "sargs' = image_mset get_s (filter_mset is_Shared (mset (Unique k (hd (uargs' k)) # s'')))"
        using \<open>possible_sequence sargs' (tail_kth uargs' k) s'' \<and> PRE_sequence spre upre s s''\<close> possible_sequence_def by auto
    qed
    ultimately show "\<exists>s''. possible_sequence sargs' uargs' s'' \<and> PRE_sequence spre upre (act # s) s''" by blast
  qed
qed

lemma insert_remove_same_list:
  assumes "k \<ge> 0 \<and> k < length s"
      and "s ! k = x"
  shows "s = insert_at k x (remove_at_index k s)"
proof (rule list_ext)
  show "length s = length (insert_at k x (remove_at_index k s))"
    by (metis One_nat_def Suc_pred add.commute assms(1) insert_at_index(1) length_greater_0_conv less_Suc_eq_le linorder_not_le list.size(3) plus_1_eq_Suc remove_at_index(1))
  fix i assume asm0: "0 \<le> i \<and> i < length s"
  show "s ! i = insert_at k x (remove_at_index k s) ! i"
  proof (cases "i < k")
    case True
    then show ?thesis
      by (metis (no_types, lifting) One_nat_def Suc_pred asm0 assms(1) insert_at_index(2) less_Suc_eq_le order_le_less_trans remove_at_index(1) remove_at_index(2))
  next
    case False
    then have "i \<ge> k" by simp
    then show ?thesis
    proof (cases "i = k")
      case True
      then show ?thesis
        by (metis (no_types, lifting) One_nat_def Suc_pred assms(1) assms(2) insert_at_index(3) less_Suc_eq_le order_le_less_trans remove_at_index(1))
    next
      case False
      then have "i > k"
        using \<open>k \<le> i\<close> nless_le by blast
      then show "s ! i = insert_at k x (remove_at_index k s) ! i"
        apply (cases i)
         apply blast
        using Groups.add_ac(2) One_nat_def Suc_less_eq Suc_pred asm0 assms(1)
          insert_at_index(4)[of k _ i x]
          less_Suc_eq_le order_le_less_trans plus_1_eq_Suc remove_at_index(1)[of k s]
          remove_at_index(3)[of k s  ]
        by fastforce
    qed
  qed
qed

lemma swap_works:
  assumes "length s = length s'"
      and "k < length s - 1"
      and "\<And>i. i \<ge> 0 \<and> i < length s \<and> i \<noteq> k \<and> i \<noteq> k + 1 \<Longrightarrow> s ! i = s' ! i"
      and "s ! k = s' ! (k + 1)"
      and "s' ! k = s ! (k + 1)"
      and "PRE_sequence spre upre s s"
      and "\<alpha> v0 = \<alpha> v0'"
      and "\<not> (\<exists>k'. is_Unique_i k' (s ! k) \<and> is_Unique_i k' (s ! (k + 1)))"
      and "all_axioms \<alpha> sact spre uact upre"
    shows "\<alpha> (compute sact uact v0 s) = \<alpha> (compute sact uact v0' s')" (is "?A = ?B")
  using assms
proof (induct k arbitrary: s s')
  case 0
  then obtain x1 x2 xs where "s = x1 # x2 # xs"
    by (metis Suc_length_conv Suc_pred add_0 le_add_diff_inverse less_diff_conv less_imp_le_nat plus_1_eq_Suc)
  then have "hd s' = x2"
    by (metis "0.prems"(1) "0.prems"(2) "0.prems"(5) One_nat_def add_0 hd_conv_nth length_greater_0_conv length_tl list.sel(2) nth_Cons_0 nth_Cons_Suc)
  moreover have "hd (tl s') = x1"
    by (metis "0.prems"(1) "0.prems"(2) "0.prems"(4) Suc_eq_plus1 \<open>s = x1 # x2 # xs\<close> hd_conv_nth length_greater_0_conv length_tl nth_Cons_0 nth_tl)
  ultimately obtain xs' where "s' = x2 # x1 # xs'"
    by (metis "0.prems"(1) "0.prems"(2) length_greater_0_conv length_tl list.collapse list.sel(2))
  moreover have "xs = xs'"
  proof (rule list_ext)
    show "length xs = length xs'"
      using "0.prems"(1) \<open>s = x1 # x2 # xs\<close> calculation by auto
    fix i assume "0 \<le> i \<and> i < length xs"
    then show "xs ! i = xs' ! i"
      by (metis "0.prems"(3) Suc_eq_plus1 Suc_less_eq \<open>s = x1 # x2 # xs\<close> bot_nat_0.extremum calculation diff_Suc_1 length_Cons nat.simps(3) nth_Cons_Suc)
  qed
  have "PRE_sequence spre upre xs xs"
    apply (cases x1) apply (cases x2)
    using "0.prems"(6) \<open>s = x1 # x2 # xs\<close> PRE_sequenceE_rec(1) by blast+
  then have "\<alpha> (compute sact uact v0 xs) = \<alpha> (compute sact uact v0' xs)"
    using assms(7)
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then have "\<alpha> (compute sact uact v0 xs) = \<alpha> (compute sact uact v0' xs)"
      using PRE_sequenceE_rec(1) by blast
    then show "\<alpha> (compute sact uact v0 (a # xs)) = \<alpha> (compute sact uact v0' (a # xs))"
    proof (cases a)
      case (Shared x1)
      then show ?thesis
        by (metis \<open>all_axioms \<alpha> sact spre uact upre\<close> Cons.prems(1) PRE_sequenceE_rec(2) \<open>\<alpha> (compute sact uact v0 xs) = \<alpha> (compute sact uact v0' xs)\<close> abstract_pre.simps(1) compute.simps(2) sabstract)
    next
      case (Unique x2)
      then show ?thesis
        by (metis \<open>all_axioms \<alpha> sact spre uact upre\<close> Cons.prems(1) PRE_sequenceE_rec(2) \<open>\<alpha> (compute sact uact v0 xs) = \<alpha> (compute sact uact v0' xs)\<close> abstract_pre.simps(2) compute.simps(3) uabstract)
    qed
  qed
  then show ?case
  proof (cases x1)
    case (Shared sarg1)
    then have "x1 = Shared sarg1" by simp
    then show ?thesis
    proof (cases x2)
      case (Shared sarg2)
      then show "\<alpha> (compute sact uact v0 s) = \<alpha> (compute sact uact v0' s')"
        using \<open>all_axioms \<alpha> sact spre uact upre\<close> "0.prems"(2) "0.prems"(5) "0.prems"(6) One_nat_def
          PRE_sequenceE_rec(2)[of spre upre x1 "x2 # xs" x1 "x2 # xs"]
          PRE_sequence_def[of spre upre s s] Suc_eq_plus1
          \<open>\<alpha> (compute sact uact v0 xs) = \<alpha> (compute sact uact v0' xs)\<close> \<open>s = x1 # x2 # xs\<close>
          \<open>x1 = Shared sarg1\<close> \<open>xs = xs'\<close>
          abstract_pre.simps(1)[of spre upre sarg2 sarg2]
          abstract_pre.simps(1)[of spre upre sarg1 sarg1]
          calculation compute.simps(2)[of sact uact v0]
          calculation compute.simps(2)[of sact uact v0']
          nth_Cons_0 ss_com[of \<alpha> sact spre uact upre] zero_less_diff zero_less_one_class.zero_le_one
        by metis
    next
      case (Unique uarg2)
      then show ?thesis
        using \<open>all_axioms \<alpha> sact spre uact upre\<close> "0.prems"(6) PRE_sequenceE_rec(1)[of spre upre x1 "x2 # xs" x1 "x2 # xs"]
          PRE_sequenceE_rec(2)[of spre upre ]
          Shared \<open>\<alpha> (compute sact uact v0 xs) = \<alpha> (compute sact uact v0' xs)\<close> \<open>s = x1 # x2 # xs\<close> \<open>xs = xs'\<close>
          abstract_pre.simps(1)[of spre upre] abstract_pre.simps(2)[of spre upre] calculation
          compute.simps(2)[of sact uact ] compute.simps(3)[of sact uact]
          su_com[of \<alpha> sact spre uact upre]
        by metis
    qed
  next
    case (Unique k1 uarg1)
    then have "x1 = Unique k1 uarg1" by simp
    then show ?thesis
    proof (cases x2)
      case (Shared sarg2)
      then have "spre sarg2 sarg2 \<and> upre k1 uarg1 uarg1"
        by (metis "0.prems"(6) PRE_sequenceE_rec(1) PRE_sequenceE_rec(2) Unique \<open>s = x1 # x2 # xs\<close> abstract_pre.simps(1) abstract_pre.simps(2))
      then show ?thesis
      using \<open>all_axioms \<alpha> sact spre uact upre\<close> Unique \<open>\<alpha> (compute sact uact v0 xs) = \<alpha> (compute sact uact v0' xs)\<close>
        \<open>s = x1 # x2 # xs\<close> \<open>s' = x2 # x1 # xs'\<close> \<open>xs = xs'\<close> compute.simps(2)[of sact uact]
        compute.simps(3)[of sact uact] su_com[of \<alpha> sact spre uact upre]
      by (metis Shared)
    next
      case (Unique k2 uarg2)
      then have "k1 \<noteq> k2"
        by (metis "0.prems"(5) "0.prems"(8) Suc_eq_plus1 \<open>\<And>thesis. (\<And>xs'. s' = x2 # x1 # xs' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>s = x1 # x2 # xs\<close> \<open>x1 = Unique k1 uarg1\<close> action.disc(2) action.sel(2) is_Unique_def is_Unique_i_def nth_Cons_0)
      then have "upre k2 uarg2 uarg2 \<and> upre k1 uarg1 uarg1"
        by (metis "0.prems"(6) PRE_sequenceE_rec(1) PRE_sequenceE_rec(2) Unique \<open>s = x1 # x2 # xs\<close> \<open>x1 = Unique k1 uarg1\<close> abstract_pre.simps(2))

      then show ?thesis
      using \<open>all_axioms \<alpha> sact spre uact upre\<close> Unique \<open>\<alpha> (compute sact uact v0 xs) = \<alpha> (compute sact uact v0' xs)\<close>
        \<open>s = x1 # x2 # xs\<close> \<open>s' = x2 # x1 # xs'\<close> \<open>xs = xs'\<close> compute.simps(2)[of sact uact]
        uu_com[of \<alpha> sact spre uact upre k1 k2 "compute sact uact v0' xs" "compute sact uact v0 xs"]
         \<open>k1 \<noteq> k2\<close> \<open>x1 = Unique k1 uarg1\<close> compute.simps(3)
      by auto
    qed
  qed
next
  case (Suc k)
  then obtain x xs x' xs' where "s = x # xs" "s' = x' # xs'"
    by (metis diff_0_eq_0 length_0_conv neq_Nil_conv not_less_zero)
  then have "x = x'"
    using Suc.prems(3) by force
  moreover have "\<alpha> (compute sact uact v0 (tl s)) = \<alpha> (compute sact uact v0' (tl s'))"
  proof (rule Suc(1))
    show "length (tl s) = length (tl s')"
      by (simp add: Suc.prems(1))
    show "k < length (tl s) - 1"
      using Suc.prems(2) by auto
    show "\<And>i. 0 \<le> i \<and> i < length (tl s) \<and> i \<noteq> k \<and> i \<noteq> k + 1 \<Longrightarrow> tl s ! i = tl s' ! i"
      by (metis Suc.prems(3) Suc_eq_plus1 \<open>length (tl s) = length (tl s')\<close> length_tl less_diff_conv nat.inject nat_le_linear not_less_eq_eq nth_tl)
    show "tl s ! k = tl s' ! (k + 1)"
      by (metis Suc.prems(4) Suc_eq_plus1 \<open>s = x # xs\<close> \<open>s' = x' # xs'\<close> add_diff_cancel_right' add_gr_0 le_neq_implies_less list.sel(3) not_one_le_zero nth_Cons_pos zero_less_one_class.zero_le_one)
    show "tl s' ! k = tl s ! (k + 1)"
      by (metis Suc.prems(5) Suc_eq_plus1 \<open>s = x # xs\<close> \<open>s' = x' # xs'\<close> list.sel(3) nth_Cons_Suc)
    show "PRE_sequence spre upre (tl s) (tl s)"
      by (metis Suc.prems(6) \<open>s = x # xs\<close> PRE_sequenceE_rec(1) list.sel(3))
    show "\<alpha> v0 = \<alpha> v0'"
      by (simp add: assms(7))
    show "\<not> (\<exists>k'. is_Unique_i k' (tl s ! k) \<and> is_Unique_i k' (tl s ! (k + 1)))"
      using Suc.prems(8) \<open>s = x # xs\<close> by force
    show "all_axioms \<alpha> sact spre uact upre"
      by (simp add: Suc.prems(9))
  qed
  ultimately show ?case
  proof (cases x)
    case (Shared x1)
    then show ?thesis
      using \<open>all_axioms \<alpha> sact spre uact upre\<close> PRE_sequenceE_rec(2) Suc.prems(6) \<open>\<alpha> (compute sact uact v0 (tl s)) = \<alpha> (compute sact uact v0' (tl s'))\<close> \<open>s = x # xs\<close> \<open>s' = x' # xs'\<close> \<open>x = x'\<close> sabstract 
      by fastforce
  next
    case (Unique x2)
    then show ?thesis
      using \<open>all_axioms \<alpha> sact spre uact upre\<close> PRE_sequenceE_rec(2) Suc.prems(6)
        \<open>\<alpha> (compute sact uact v0 (tl s)) = \<alpha> (compute sact uact v0' (tl s'))\<close> \<open>s = x # xs\<close> \<open>s' = x' # xs'\<close>
        \<open>x = x'\<close> uabstract[of \<alpha> sact spre uact upre]
      by fastforce
  qed
qed

lemma mset_remove:
  assumes "k \<ge> 0 \<and> k < length s"
  shows "mset s = mset (remove_at_index k s) + {# s ! k #}"
  using assms
proof (induct s arbitrary: k)
  case Nil
  then show ?case
    by simp
next
  case (Cons a s)
  then show ?case
    using less_Suc_eq_0_disj by auto
qed

lemma abstract_pre_refl:
  assumes "abstract_pre spre upre a b"
      and "all_axioms \<alpha> sact spre uact upre"
  shows "abstract_pre spre upre b b"
  apply (cases a)
   apply (cases b)
  using abstract_pre.simps(1) assms spre_refl apply metis
  using assms apply force
   apply (cases b)
  using assms apply force
  using abstract_pre.simps(2) assms upre_refl by metis

lemma PRE_sequence_refl:
  assumes "PRE_sequence spre upre s s'"
      and "all_axioms \<alpha> sact spre uact upre"
  shows "PRE_sequence spre upre s' s'"
proof (rule PRE_sequenceI)
  show "length s' = length s'"
    by simp
  fix i assume "0 \<le> i \<and> i < length s'"
  then show "abstract_pre spre upre (s' ! i) (s' ! i)"
    by (metis PRE_sequence_def abstract_pre_refl assms)
qed

lemma PRE_sequence_removes:
  assumes "PRE_sequence spre upre s s"
  shows "PRE_sequence spre upre (remove_at_index n s) (remove_at_index n s)"
  using assms
proof (induct n arbitrary: s)
  case 0
  then show ?case
    by (metis PRE_sequenceE_rec(1) nat.simps(3) remove_at_index.elims)
next
  case (Suc n)
  then show ?case
    apply (cases s)
     apply force
    by (metis PRE_sequenceE_rec(1) PRE_sequenceE_rec(2) PRE_sequenceI_rec remove_at_index.simps(3))
qed

lemma PRE_sequence_insert:
  assumes "abstract_pre spre upre x x"
    and "PRE_sequence spre upre s s"
    shows "PRE_sequence spre upre (insert_at n x s) (insert_at n x s)"
  using assms
proof (induct n arbitrary: s)
  case 0
  then show ?case
    by (simp add: PRE_sequenceI_rec)
next
  case (Suc n)
  then show ?case
    apply (cases s)
     apply (simp add: PRE_sequenceI_rec)
    by (metis PRE_sequenceE_rec(1) PRE_sequenceE_rec(2) PRE_sequenceI_rec insert_at.simps(3))
qed

lemma empty_possible_sequence:
  assumes "possible_sequence sargs uargs []"
      and "possible_sequence sargs uargs s'"
  shows "s' = []"
proof (rule ccontr)
  assume "s' \<noteq> []"
  then obtain x q where "s' = x # q"
    by (meson neq_Nil_conv)
  then show False
  proof (cases x)
    case (Shared x1)
    then show ?thesis
      by (metis \<open>s' = x # q\<close> assms(1) assms(2) exists_index_in_sequence_shared less_zeroE list.size(3) possible_sequence_where_is_shared)
  next
    case (Unique k uarg)
    then have "uargs k \<noteq> []"
      by (metis (no_types, lifting) \<open>s' = x # q\<close> action.disc(2) action.sel(2) assms(2) filter.simps(2) is_Unique_def is_Unique_i_def list.discI list.map_disc_iff possible_sequence_def)
    then show ?thesis
      by (metis assms(1) exists_index_in_sequence_unique less_nat_zero_code list.size(3))
  qed
qed

lemma it_all_commutes:
  assumes "possible_sequence sargs uargs s"
      and "possible_sequence sargs uargs s'"
      and "\<alpha> v0 = \<alpha> v0'"
      and "PRE_sequence spre upre s s"
      and "PRE_sequence spre upre s' s'"
      and "all_axioms \<alpha> sact spre uact upre"
    shows "\<alpha> (compute sact uact v0 s) = \<alpha> (compute sact uact v0' s')"
  using assms
proof (induct "size s" arbitrary: sargs uargs s s')
  case 0
  then have "s = [] \<and> s' = []"
    by (simp add: empty_possible_sequence)
  then show ?case
    by (simp add: "0.prems"(1) "0.prems"(2) assms(3))
next
  case (Suc n)
  moreover obtain x s1 where "s = x # s1"
    by (meson Suc.hyps(2) Suc_length_conv)
  then have "abstract_pre spre upre x x"
    using Suc.prems(4) PRE_sequenceE_rec(2) by blast
  then show ?case
  proof (cases x)
    case (Shared sarg)
    then have "Shared sarg \<in> set s'"
      by (metis Suc.prems(1) Suc.prems(2) \<open>s = x # s1\<close> exists_index_in_sequence_shared nth_mem possible_sequence_where_is_shared)
    then obtain k where "k \<ge> 0 \<and> k < length s' \<and> s' ! k = x"
      by (metis Shared bot_nat_0.extremum in_set_conv_nth)

    let ?s' = "remove_at_index k s'"
    have "length ?s' = length s' - 1"
      by (simp add: \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close> remove_at_index(1))
    moreover have "k < length s'"
      by (simp add: \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close>)
    then have "s' = insert_at k x ?s'"
      by (simp add: \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close> insert_remove_same_list)
    define i :: nat where "i = k"
    have "i \<ge> 0 \<and> i \<le> k \<Longrightarrow> \<alpha> (compute sact uact v0' (insert_at (k - i) x ?s')) = \<alpha> (compute sact uact v0' s')" 
    proof (induct i)
      case 0
      then show ?case
        using \<open>s' = insert_at k x (remove_at_index k s')\<close> by auto
    next
      case (Suc i)
      then have "\<alpha> (compute sact uact v0' (insert_at (k - i) x (remove_at_index k s'))) = \<alpha> (compute sact uact v0' s')"
        using Suc_leD by blast
      moreover have "\<alpha> (compute sact uact v0' (insert_at (k - Suc i) x (remove_at_index k s'))) = \<alpha> (compute sact uact v0' (insert_at (k - i) x (remove_at_index k s')))"
      proof (rule swap_works)
        show "length (insert_at (k - Suc i) x (remove_at_index k s')) = length (insert_at (k - i) x (remove_at_index k s'))"
          by (metis (no_types, lifting) Suc_pred' \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close> \<open>length (remove_at_index k s') = length s' - 1\<close> diff_le_self insert_at_index(1) less_Suc_eq_le order_le_less_trans)
        show "PRE_sequence spre upre (insert_at (k - Suc i) x (remove_at_index k s')) (insert_at (k - Suc i) x (remove_at_index k s'))"
        proof -
          have "PRE_sequence spre upre (remove_at_index k s') (remove_at_index k s')" using \<open>PRE_sequence spre upre s' s'\<close>
            using PRE_sequence_removes by auto
          then show ?thesis using PRE_sequence_insert \<open>abstract_pre spre upre x x\<close> by blast
        qed
        show "\<alpha> v0' = \<alpha> v0'" by simp
        let ?k = "k - Suc i"

        show "?k < length (insert_at (k - Suc i) x (remove_at_index k s')) - 1"
          using One_nat_def Suc.prems Suc_diff_Suc Suc_le_lessD \<open>k < length s'\<close> \<open>length (remove_at_index k s') = length s' - 1\<close>
            \<open>s' = insert_at k x (remove_at_index k s')\<close> diff_le_self diff_zero
            insert_at_index(1)[of "k - Suc i" _ x] insert_at_index(1)[of k _ x] less_Suc_eq_le order_le_less_trans
          by simp
        show "insert_at (k - Suc i) x (remove_at_index k s') ! ?k = insert_at (k - i) x (remove_at_index k s') ! (?k + 1)"
          apply (cases k)
          using Suc.prems apply blast
          apply (cases ?k)
           apply (metis (no_types, lifting) Suc.prems Suc_eq_plus1 Suc_leI \<open>k - Suc i < length (insert_at (k - Suc i) x (remove_at_index k s')) - 1\<close> add_diff_cancel_right' diff_diff_cancel diff_zero insert_at_index(1) insert_at_index(3) le_numeral_extra(3) length_greater_0_conv list.size(3) nat_less_le plus_1_eq_Suc)
        proof -
          fix nat nata assume r: "k = Suc nat" "k - Suc i = Suc nata"
          moreover have "insert_at (k - i) x (remove_at_index k s') ! (k - i) = x"
            by (metis Suc_pred' \<open>k < length s'\<close> \<open>length (remove_at_index k s') = length s' - 1\<close> bot_nat_0.extremum diff_le_self insert_at_index(3) less_Suc_eq_le order_le_less_trans)
          moreover have "\<And>x. insert_at (k - Suc i) x (remove_at_index k s') ! (k - Suc i) = x"
            by (metis Suc_leI Suc_le_mono Suc_pred' \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close> \<open>length (remove_at_index k s') = length s' - 1\<close> bot_nat_0.extremum diff_le_self insert_at_index(3) order_le_less_trans)
          ultimately show ?thesis
            by (metis Suc.prems Suc_diff_Suc Suc_eq_plus1 Suc_le_lessD)
        qed
        show "insert_at (k - i) x (remove_at_index k s') ! ?k = insert_at (k - Suc i) x (remove_at_index k s') ! (?k + 1)"
        proof -
          have "insert_at (k - i) x (remove_at_index k s') ! (k - Suc i) = remove_at_index k s' ! (k - Suc i)"
            by (metis (no_types, lifting) Suc.prems Suc_diff_Suc Suc_eq_plus1 Suc_leI Suc_le_lessD \<open>k < length s'\<close> \<open>length (remove_at_index k s') = length s' - 1\<close> add_leE insert_at_index(2) le_add_diff_inverse2 le_add_same_cancel2 lessI less_Suc_eq_le)
          moreover have "length (insert_at (k - Suc i) x (remove_at_index k s')) = length (remove_at_index k s') + 1"
            by (metis Suc_eq_plus1 \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close> \<open>length (remove_at_index k s') = length s' - 1\<close> add_le_imp_le_diff insert_at_index(1) less_eq_Suc_le less_imp_diff_less)
          then have "insert_at (k - Suc i) x (remove_at_index k s') ! (k - Suc i + 1) = remove_at_index k s' ! (k - Suc i + 1 - 1)"
            by (metis \<open>k - Suc i < length (insert_at (k - Suc i) x (remove_at_index k s')) - 1\<close> add_diff_cancel_right' insert_at_index(4) less_add_one less_diff_conv less_imp_le_nat)
          ultimately show ?thesis
            by simp
        qed

        show "\<not> (\<exists>k'. is_Unique_i k' (insert_at (k - Suc i) x (remove_at_index k s') ! (k - Suc i)) \<and>
         is_Unique_i k' (insert_at (k - Suc i) x (remove_at_index k s') ! (k - Suc i + 1)))"
          by (metis (no_types, lifting) One_nat_def Shared Suc.prems Suc_diff_Suc \<open>k < length s'\<close> \<open>length (remove_at_index k s') = length s' - 1\<close> action.disc(1) add_leE diff_zero insert_at_index(3) is_Unique_def is_Unique_i_def le_add_diff_inverse2 le_add_same_cancel2 less_Suc_eq_le order_le_less_trans)

        show "\<And>j. 0 \<le> j \<and> j < length (insert_at (k - Suc i) x (remove_at_index k s')) \<and> j \<noteq> ?k \<and> j \<noteq> ?k + 1 \<Longrightarrow>
         insert_at (k - Suc i) x (remove_at_index k s') ! j = insert_at (k - i) x (remove_at_index k s') ! j"
        proof (clarify)
          fix j assume "0 \<le> j" "j < length (insert_at (k - Suc i) x (remove_at_index k s'))" "j \<noteq> k - Suc i" "j \<noteq> k - Suc i + 1"
          moreover have "length (insert_at (k - Suc i) x (remove_at_index k s')) = length (remove_at_index k s') + 1"
            by (metis (no_types, lifting) One_nat_def Suc.prems Suc_diff_Suc \<open>k < length s'\<close> \<open>length (remove_at_index k s') = length s' - 1\<close> add_leE diff_zero insert_at_index(1) le_add_diff_inverse2 less_Suc_eq_le order_le_less_trans)
          moreover have "k - Suc i \<le> length (remove_at_index k s')"
            using \<open>k - Suc i < length (insert_at (k - Suc i) x (remove_at_index k s')) - 1\<close> calculation(5) by force
          ultimately show "insert_at (k - Suc i) x (remove_at_index k s') ! j = insert_at (k - i) x (remove_at_index k s') ! j"
            apply (cases "j < k - Suc i")
            using insert_at_index(2)[of "k - Suc i" "remove_at_index k s'" j x] insert_at_index(2)[of "k - i" "remove_at_index k s'" j x]
            apply (metis Suc.prems Suc_diff_le Suc_eq_plus1 Suc_leI \<open>k - Suc i < length (insert_at (k - Suc i) x (remove_at_index k s')) - 1\<close> diff_Suc_1 diff_Suc_Suc less_Suc_eq)
            by (simp add: insert_at_index(4) nat_neq_iff)
        qed
        show "all_axioms \<alpha> sact spre uact upre"
          by (simp add: assms(6))
      qed
      ultimately show ?case
        by presburger
    qed
    then have "\<alpha> (compute sact uact v0' (x # ?s')) = \<alpha> (compute sact uact v0' s')"
      using i_def by force
    moreover have "\<alpha> (compute sact uact v0 s1) = \<alpha> (compute sact uact v0' ?s')"
    proof (rule Suc(1))
      show "n = length s1"
        using Suc.hyps(2) \<open>s = x # s1\<close> by auto
      show "\<alpha> v0 = \<alpha> v0'"
        using assms(3) by auto
      show "PRE_sequence spre upre s1 s1"
        using PRE_sequenceE_rec(1) Suc.prems(4) \<open>s = x # s1\<close> by blast
      show "possible_sequence (sargs - {# sarg #}) uargs s1"
      proof (rule possible_sequenceI)
        show "\<And>i. uargs i = map get_u (filter (is_Unique_i i) s1)"
          by (metis (mono_tags, lifting) Shared Suc.hyps(2) Suc.prems(1) \<open>s = x # s1\<close> action.disc(1) filter_remove is_Unique_def is_Unique_i_def le_numeral_extra(3) nth_Cons_0 possible_sequence_def remove_at_index.simps(2) zero_less_Suc)
        show "sargs - {#sarg#} = image_mset get_s (filter_mset is_Shared (mset s1))"
          using Shared Suc.prems(1) \<open>s = x # s1\<close> action.disc(1)[of sarg] action.sel(1)[of sarg] add_mset_diff_bothsides diff_empty
            filter_mset_add_mset msed_map_invL mset.simps(2) possible_sequence_def[of sargs uargs s]
          by simp
      qed

      show "possible_sequence (sargs - {#sarg#}) uargs (remove_at_index k s')"
      proof (rule possible_sequenceI)
        show "\<And>i. uargs i = map get_u (filter (is_Unique_i i) (remove_at_index k s'))"
        proof (rule list_ext)
          have "filter is_Unique (remove_at_index k s') = filter is_Unique s'"
            by (simp add: Shared \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close> filter_remove is_Unique_def)
          then show "\<And>i. length (uargs i) = length (map get_u (filter (is_Unique_i i) (remove_at_index k s')))"
            by (metis Shared Suc.prems(2) \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close> action.disc(1) filter_remove is_Unique_def is_Unique_i_def possible_sequence_def)
          show "\<And>i ia. 0 \<le> ia \<and> ia < length (uargs i) \<Longrightarrow> uargs i ! ia = map get_u (filter (is_Unique_i i) (remove_at_index k s')) ! ia"
            by (metis Shared Suc.prems(2) \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close> action.disc(1) filter_remove is_Unique_def is_Unique_i_def possible_sequence_def)
        qed
        have "sargs = image_mset get_s (filter_mset is_Shared (mset s'))"
          using Suc.prems(2) possible_sequence_def by blast
        show "sargs - {#sarg#} = image_mset get_s (filter_mset is_Shared (mset (remove_at_index k s')))"
        proof -
          have "mset s' = mset (remove_at_index k s') + {# x #}"
            using \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close> mset_remove_index by blast
          then show ?thesis
            by (simp add: Shared \<open>sargs = image_mset get_s (filter_mset is_Shared (mset s'))\<close>)
        qed
      qed
      show "PRE_sequence spre upre (remove_at_index k s') (remove_at_index k s')" using Suc.prems(5) PRE_sequence_removes by blast
      show "all_axioms \<alpha> sact spre uact upre" by (simp add: assms(6))
    qed
    ultimately show ?thesis
      using \<open>all_axioms \<alpha> sact spre uact upre\<close> PRE_sequenceE_rec(2) Shared Suc.prems(4) \<open>s = x # s1\<close> abstract_pre.simps(1) compute.simps(2) sabstract
      by fastforce
  next
    case (Unique ind uarg)
    let ?uargs = "uargs ind"
    have "hd ?uargs = uarg"
      by (metis Unique \<open>s = x # s1\<close> calculation(3) possible_sequence_where_is_unique)
    moreover have "?uargs \<noteq> []"
      by (metis (no_types, opaque_lifting) Suc.prems(1) Unique \<open>s = x # s1\<close> action.disc(2) action.sel(2) filter.simps(2) is_Unique_def is_Unique_i_def list.distinct(1) list.map_disc_iff possible_sequence_def)
    ultimately have "?uargs = uarg # tl ?uargs"
      by force
    then obtain k where "k \<ge> 0 \<and> k < length s' \<and> s' ! k = x" "\<And>j. j \<ge> 0 \<and> j < k \<Longrightarrow> \<not> is_Unique_i ind (s' ! j)"
      by (metis Suc.prems(2) Unique \<open>hd (uargs ind) = uarg\<close> \<open>uargs ind \<noteq> []\<close> exists_index_in_sequence_unique)
    let ?s' = "remove_at_index k s'"
    have "length ?s' = length s' - 1"
      by (simp add: \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close> remove_at_index(1))
    moreover have "k < length s'"
      by (simp add: \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close>)
    then have "s' = insert_at k x ?s'"
      by (simp add: \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close> insert_remove_same_list)
    define i :: nat where "i = k"
    have "i \<ge> 0 \<and> i \<le> k \<Longrightarrow> \<alpha> (compute sact uact v0' (insert_at (k - i) x ?s')) = \<alpha> (compute sact uact v0' s')" 
    proof (induct i)
      case 0
      then show ?case
        using \<open>s' = insert_at k x (remove_at_index k s')\<close> by auto
    next
      case (Suc i)
      then have "\<alpha> (compute sact uact v0' (insert_at (k - i) x (remove_at_index k s'))) = \<alpha> (compute sact uact v0' s')"
        using Suc_leD by blast
      moreover have "\<alpha> (compute sact uact v0' (insert_at (k - Suc i) x (remove_at_index k s'))) = \<alpha> (compute sact uact v0' (insert_at (k - i) x (remove_at_index k s')))"
      proof (rule swap_works)
        show "length (insert_at (k - Suc i) x (remove_at_index k s')) = length (insert_at (k - i) x (remove_at_index k s'))"
          by (metis (no_types, lifting) Suc_pred' \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close> \<open>length (remove_at_index k s') = length s' - 1\<close> insert_at_index(1) less_Suc_eq_le less_imp_diff_less order_le_less_trans)
        show "PRE_sequence spre upre (insert_at (k - Suc i) x (remove_at_index k s')) (insert_at (k - Suc i) x (remove_at_index k s'))"
        proof -
          have "PRE_sequence spre upre (remove_at_index k s') (remove_at_index k s')"
            using \<open>PRE_sequence spre upre s' s'\<close>
            by (simp add: PRE_sequence_removes)
          then show ?thesis
            using \<open>abstract_pre spre upre x x\<close> PRE_sequence_insert by blast
        qed

        show "\<alpha> v0' = \<alpha> v0'" by simp
        let ?k = "k - Suc i"


        show "?k < length (insert_at (k - Suc i) x (remove_at_index k s')) - 1"
          using One_nat_def Suc.prems Suc_diff_Suc Suc_le_lessD \<open>k < length s'\<close>
            \<open>length (remove_at_index k s') = length s' - 1\<close> \<open>s' = insert_at k x (remove_at_index k s')\<close>
            diff_le_self diff_zero insert_at_index(1)[of k "remove_at_index k s'" x] insert_at_index(1)[of "k - Suc i" "remove_at_index k s'" x]
            less_Suc_eq_le order_le_less_trans
          by simp
        show "insert_at (k - Suc i) x (remove_at_index k s') ! ?k = insert_at (k - i) x (remove_at_index k s') ! (?k + 1)"
        proof -
          have "insert_at (k - Suc i) x (remove_at_index k s') ! (k - Suc i) = x"
            by (metis Suc_pred' \<open>k < length s'\<close> \<open>length (remove_at_index k s') = length s' - 1\<close> bot_nat_0.extremum diff_self_eq_0 insert_at_index(3) less_Suc_eq_le less_imp_diff_less)
          moreover have "insert_at (k - i) x (remove_at_index k s') ! (k - i) = x"
            by (metis Suc_pred' \<open>k < length s'\<close> \<open>length (remove_at_index k s') = length s' - 1\<close> bot_nat_0.extremum insert_at_index(3) less_Suc_eq_le less_imp_diff_less less_nat_zero_code not_gr_zero)
          ultimately show ?thesis
            by (simp add: Suc.prems Suc_diff_Suc Suc_le_lessD)
        qed
        have "insert_at (k - i) x (remove_at_index k s') ! (k - Suc i) = remove_at_index k s' ! (k - Suc i)"
          by (metis (no_types, lifting) Suc.prems Suc_diff_Suc Suc_eq_plus1 Suc_leI Suc_le_lessD \<open>k < length s'\<close> \<open>length (remove_at_index k s') = length s' - 1\<close> add_leE insert_at_index(2) le_add_diff_inverse2 le_add_same_cancel2 lessI less_Suc_eq_le)
        then 
        show "insert_at (k - i) x (remove_at_index k s') ! ?k = insert_at (k - Suc i) x (remove_at_index k s') ! (?k + 1)"
          using  One_nat_def Suc.prems Suc_diff_Suc \<open>k - Suc i < length (insert_at (k - Suc i) x (remove_at_index k s')) - 1\<close>
            \<open>k < length s'\<close> \<open>length (remove_at_index k s') = length s' - 1\<close> add_diff_cancel_right'
            add_leE diff_zero insert_at_index(1)[of "k - Suc i" "remove_at_index k s'" x] insert_at_index(4)[of "k - Suc i" "remove_at_index k s'"]
            le_add_diff_inverse2 less_Suc_eq_le
            less_add_same_cancel1 less_diff_conv order_le_less_trans zero_less_one
          by simp

        have "insert_at (k - Suc i) x (remove_at_index k s') ! (k - Suc i + 1) = remove_at_index k s' ! (k - Suc i + 1 - 1)"
          using \<open>insert_at (k - i) x (remove_at_index k s') ! (k - Suc i) = insert_at (k - Suc i) x (remove_at_index k s') ! (k - Suc i + 1)\<close> \<open>insert_at (k - i) x (remove_at_index k s') ! (k - Suc i) = remove_at_index k s' ! (k - Suc i)\<close> by auto
        then have "\<not> is_Unique_i ind (insert_at (k - Suc i) x (remove_at_index k s') ! (?k + 1))"
          by (metis One_nat_def Suc.prems Suc_le_lessD \<open>\<And>j. 0 \<le> j \<and> j < k \<Longrightarrow> \<not> is_Unique_i ind (s' ! j)\<close> \<open>k < length s'\<close> add_diff_cancel_right' add_leE diff_Suc_less le_add2 le_add_same_cancel2 plus_1_eq_Suc remove_at_index(2))
        then show "\<not> (\<exists>k'. is_Unique_i k' (insert_at (k - Suc i) x (remove_at_index k s') ! (k - Suc i)) \<and>
         is_Unique_i k' (insert_at (k - Suc i) x (remove_at_index k s') ! (k - Suc i + 1)))"
          by (metis (no_types, lifting) One_nat_def Suc.prems Suc_diff_Suc Unique \<open>k < length s'\<close> \<open>length (remove_at_index k s') = length s' - 1\<close> action.sel(2) diff_zero insert_at_index(3) is_Unique_i_def le_add2 le_add_diff_inverse le_add_same_cancel2 less_Suc_eq_le order_le_less_trans)
        show "\<And>j. 0 \<le> j \<and> j < length (insert_at (k - Suc i) x (remove_at_index k s')) \<and> j \<noteq> ?k \<and> j \<noteq> ?k + 1 \<Longrightarrow>
         insert_at (k - Suc i) x (remove_at_index k s') ! j = insert_at (k - i) x (remove_at_index k s') ! j"
        proof -
          fix j assume "0 \<le> j \<and> j < length (insert_at (k - Suc i) x (remove_at_index k s')) \<and> j \<noteq> ?k \<and> j \<noteq> ?k + 1"
          moreover have "k - Suc i \<le> length (remove_at_index k s')"
            using \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close> \<open>length (remove_at_index k s') = length s' - 1\<close> by force
          moreover have "k - i \<le> length (remove_at_index k s')"
            using \<open>k < length s'\<close> \<open>length (remove_at_index k s') = length s' - 1\<close> by linarith
          then show "insert_at (k - Suc i) x (remove_at_index k s') ! j = insert_at (k - i) x (remove_at_index k s') ! j"
            apply (cases "j < k - i")
            apply (metis Suc.prems Suc_diff_Suc Suc_le_lessD calculation(1) calculation(2) insert_at_index(2) less_Suc_eq)
            by (metis Suc.prems Suc_diff_Suc Suc_eq_plus1 Suc_le_lessD calculation(1) calculation(2) insert_at_index(1) insert_at_index(4) linorder_le_less_linear linorder_neqE_nat)
        qed
        show "all_axioms \<alpha> sact spre uact upre" by (simp add: assms(6))
      qed
      ultimately show ?case
        by presburger
    qed
    then have "\<alpha> (compute sact uact v0' (x # ?s')) = \<alpha> (compute sact uact v0' s')"
      using i_def by force
    moreover have "\<alpha> (compute sact uact v0 s1) = \<alpha> (compute sact uact v0' ?s')"
    proof (rule Suc(1))
      show "all_axioms \<alpha> sact spre uact upre" by (simp add: assms(6))
      show "n = length s1"
        using Suc.hyps(2) \<open>s = x # s1\<close> by auto
      show "\<alpha> v0 = \<alpha> v0'"
        using assms(3) by auto
      show "PRE_sequence spre upre s1 s1"
        using Suc.prems(4) \<open>s = x # s1\<close> PRE_sequenceE_rec(1) by blast
      show "possible_sequence sargs (tail_kth uargs ind) s1"
      proof (rule possible_sequenceI)
        show "\<And>i. tail_kth uargs ind i = map get_u (filter (is_Unique_i i) s1)"
        proof -
          fix i show "tail_kth uargs ind i = map get_u (filter (is_Unique_i i) s1)"
          proof (cases "i = ind")
            case True
            then have "tail_kth uargs ind i = tl ?uargs"
              by (simp add: tail_kth_def)
            then show ?thesis using exists_index_in_sequence_unique[of uarg uargs ind sargs s]
              by (metis Suc.prems(1) Unique \<open>hd (uargs ind) = uarg\<close> \<open>s = x # s1\<close> \<open>uargs ind \<noteq> []\<close> action.disc(2) action.sel(2) is_Unique_def is_Unique_i_def le_eq_less_or_eq nth_Cons_0 possible_sequence_def remove_at_index.simps(2))
          next
            case False
            then show ?thesis
              using Suc.hyps(2) Suc.prems(1) Unique \<open>s = x # s1\<close> action.sel(2) filter_remove
                fun_upd_apply is_Unique_i_def le_numeral_extra(3) nth_Cons_0[of x s1] possible_sequence_def[of sargs uargs s]
                remove_at_index.simps(2)[of x s1] tail_kth_def zero_less_Suc
              by metis
          qed
        qed
        show "sargs = image_mset get_s (filter_mset is_Shared (mset s1))"
          by (metis Suc.prems(1) Unique \<open>s = x # s1\<close> action.disc(2) filter_mset_add_mset mset.simps(2) possible_sequence_def)
      qed
      show "possible_sequence sargs (tail_kth uargs ind) (remove_at_index k s')"
      proof (rule possible_sequenceI)
        show "\<And>i. tail_kth uargs ind i = map get_u (filter (is_Unique_i i) (remove_at_index k s'))"
          using Suc.prems(1) Suc.prems(2) Unique \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close> \<open>\<And>j. 0 \<le> j \<and> j < k \<Longrightarrow> \<not> is_Unique_i ind (s' ! j)\<close>
            \<open>possible_sequence sargs (tail_kth uargs ind) s1\<close> \<open>s = x # s1\<close> action.sel(2) filter.simps(2)
            filter_remove fun_upd_same is_Unique_i_def possible_sequence_def[of sargs "tail_kth uargs ind" s1]
            possible_sequence_def[of sargs uargs s] possible_sequence_def[of sargs uargs s']
            remove_at_index_filter tail_kth_def
          by metis
        show "sargs = image_mset get_s (filter_mset is_Shared (mset (remove_at_index k s')))"
          by (metis Suc.prems(2) Unique \<open>0 \<le> k \<and> k < length s' \<and> s' ! k = x\<close> action.disc(2) filter_remove mset_filter possible_sequence_def)
      qed
      show "PRE_sequence spre upre (remove_at_index k s') (remove_at_index k s')"
        using PRE_sequence_removes Suc.prems(5) by auto
    qed
    ultimately show ?thesis
      using Unique \<open>abstract_pre spre upre x x\<close> \<open>s = x # s1\<close> abstract_pre.simps(2)[of ]
        assms(6) compute.simps(3)[of sact uact] uabstract[of \<alpha> sact spre uact upre ]
      by metis
  qed
qed

lemma PRE_sequence_same_abstract:
  assumes "PRE_sequence spre upre s s'"
      and "\<alpha> v0 = \<alpha> v0'"
      and "all_axioms \<alpha> sact spre uact upre"
    shows "\<alpha> (compute sact uact v0 s) = \<alpha> (compute sact uact v0' s')"
  using assms
proof (induct s' arbitrary: s v0 v0')
  case Nil
  then show ?case
    by (simp add: PRE_sequence_def)
next
  case (Cons act' s')
  then show ?case
  proof (cases act')
    case (Shared sarg')
    then obtain sarg s0 where "s = Shared sarg # s0" "spre sarg sarg'" "PRE_sequence spre upre s0 s'"
      by (metis Cons.prems(1) PRE_sequenceE_rec(1) PRE_sequenceE_rec(2) PRE_sequence_def abstract_pre.simps(1) abstract_pre.simps(3) action.exhaust length_0_conv neq_Nil_conv)
    then show ?thesis
      using Cons.hyps Cons.prems(2) Cons.prems(3) Shared sabstract by fastforce
  next
    case (Unique k uarg')
    then obtain uarg s0 where "s = Unique k uarg # s0" "upre k uarg uarg'" "PRE_sequence spre upre s0 s'"
      by (metis Cons.prems(1) PRE_sequenceE_rec(1) PRE_sequenceE_rec(2) PRE_sequence_def abstract_pre.simps(2) abstract_pre.simps(4) action.exhaust length_0_conv neq_Nil_conv)
    then show ?thesis
      using Cons.hyps Cons.prems(2) Unique assms(3) uabstract by fastforce
  qed
qed

lemma simple_possible_PRE_seq:
  assumes "possible_sequence sargs uargs s"
      and "possible_sequence sargs' uargs' s'"
      and "PRE_shared spre sargs sargs'"
      and "\<And>k. PRE_unique (upre k) (uargs k) (uargs' k)"
      and "all_axioms \<alpha> sact spre uact upre"
    shows "PRE_sequence spre upre s' s'"
proof (rule PRE_sequenceI)
  show "length s' = length s'" by simp
  fix i assume "0 \<le> i \<and> i < length s'"
  then show "abstract_pre spre upre (s' ! i) (s' ! i)"
  proof (cases "s' ! i")
    case (Shared sarg')
    then have "Shared sarg' \<in># filter_mset is_Shared (mset s')"
      using \<open>0 \<le> i \<and> i < length s'\<close> nth_mem_mset by fastforce
    then have "sarg' \<in># sargs'"
      by (metis (mono_tags, lifting) action.sel(1) assms(2) imageI possible_sequence_def set_image_mset)
    moreover obtain ms where "image_mset fst ms = sargs \<and> image_mset snd ms = sargs' \<and> (\<forall>x \<in># ms. spre (fst x) (snd x))"
      using PRE_shared_def assms(3) by blast
    then obtain x where "x \<in># ms" "snd x = sarg'"
      using calculation by fastforce
    then show ?thesis
      using Shared \<open>image_mset fst ms = sargs \<and> image_mset snd ms = sargs' \<and> (\<forall>x\<in>#ms. spre (fst x) (snd x))\<close> spre_refl
      by (metis abstract_pre.simps(1) assms(5))
  next
    case (Unique k uarg')
    then have "Unique k uarg' \<in> set (filter is_Unique s')"
      by (metis \<open>0 \<le> i \<and> i < length s'\<close> is_Unique_def action.disc(2) filter_set member_filter nth_mem)
    then have "uarg' \<in> set (map get_u (filter (is_Unique_i k) s'))"
      by (metis (no_types, lifting) action.sel(2) action.sel(3) filter_set image_eqI is_Unique_i_def list.set_map member_filter)
    then obtain i where "i \<ge> 0 \<and> i < length (uargs' k) \<and> uarg' = (uargs' k) ! i"
      by (metis assms(2) gr_implies_not_zero in_set_conv_nth linorder_le_less_linear possible_sequence_def)
    then have "upre k ((uargs k) ! i) ((uargs' k) ! i)"
      using PRE_unique_def assms(4) by blast
    then show ?thesis
      using Unique \<open>0 \<le> i \<and> i < length (uargs' k) \<and> uarg' = uargs' k ! i\<close> assms(5) upre_refl by fastforce
  qed
qed

lemma main_lemma:
  assumes "possible_sequence sargs uargs s"
      and "possible_sequence sargs' uargs' s'"

      and "PRE_shared spre sargs sargs'"
      and "\<And>k. PRE_unique (upre k) (uargs k) (uargs' k)"

      and "\<alpha> v0 = \<alpha> v0'"
      and "all_axioms \<alpha> sact spre uact upre"

    shows "\<alpha> (compute sact uact v0 s) = \<alpha> (compute sact uact v0' s')"
proof -
  obtain s'' where "possible_sequence sargs' uargs' s'' \<and> PRE_sequence spre upre s s''"
    using assms(1) assms(2) assms(3) assms(4) exists_aligned_sequence by blast
  have "\<alpha> (compute sact uact v0' s'') = \<alpha> (compute sact uact v0' s')"
  proof (rule it_all_commutes)
    show "possible_sequence sargs' uargs' s''"
      by (simp add: \<open>possible_sequence sargs' uargs' s'' \<and> PRE_sequence spre upre s s''\<close>)
    show "possible_sequence sargs' uargs' s'"
      by (simp add: assms(2))
    show "\<alpha> v0' = \<alpha> v0'"
      by simp
    show "PRE_sequence spre upre s'' s''"
      using \<open>possible_sequence sargs' uargs' s'' \<and> PRE_sequence spre upre s s''\<close> PRE_sequence_refl assms(6) by blast
    show "PRE_sequence spre upre s' s'"
      using simple_possible_PRE_seq assms(1) assms(2) assms(3) assms(4) assms(6) by blast
    show "all_axioms \<alpha> sact spre uact upre"
      using assms(6) by auto
  qed
  moreover have "\<alpha> (compute sact uact v0' s'') = \<alpha> (compute sact uact v0 s)"
    using PRE_sequence_same_abstract \<open>possible_sequence sargs' uargs' s'' \<and> PRE_sequence spre upre s s''\<close> assms(1) assms(5) assms(6) by metis
  ultimately show ?thesis
    by auto
qed

inductive reachable_value :: "('v \<Rightarrow> 'a \<Rightarrow> 'v) \<Rightarrow> ('i \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> 'a multiset \<Rightarrow> ('i \<Rightarrow> 'b list) \<Rightarrow> 'v \<Rightarrow> bool" where
  Self: "reachable_value sact uact v0 {#} (\<lambda>k. []) v0"
| SharedStep: "reachable_value sact uact v0 sargs uargs v1 \<Longrightarrow> reachable_value sact uact v0 (sargs + {# sarg #}) uargs (sact v1 sarg)"
| UniqueStep: "reachable_value sact uact v0 sargs uargs v1 \<Longrightarrow> reachable_value sact uact v0 sargs (uargs(k := uarg # uargs k)) (uact k v1 uarg)"

lemma reachable_then_possible_sequence_and_compute:
  assumes "reachable_value sact uact v0 sargs uargs v1"
  shows "\<exists>s. possible_sequence sargs uargs s \<and> v1 = compute sact uact v0 s"
  using assms
proof (induct rule: reachable_value.induct)
  case (Self sact uact v0)
  have "possible_sequence {#} (\<lambda>k. []) [] \<and> v0 = compute sact uact v0 []"
    by (simp add: possible_sequenceI)
  then show ?case by blast
next
  case (SharedStep sact uact v0 sargs uargs v1 sarg)
  then obtain s where "possible_sequence sargs uargs s \<and> v1 = compute sact uact v0 s" by blast
  let ?s = "Shared sarg # s"
  have "possible_sequence (sargs + {#sarg#}) uargs ?s"
  proof (rule possible_sequenceI)
    show "\<And>i. uargs i = map get_u (filter (is_Unique_i i) (Shared sarg # s))"
      by (metis \<open>possible_sequence sargs uargs s \<and> v1 = compute sact uact v0 s\<close> action.disc(1) filter.simps(2) is_Unique_def is_Unique_i_def possible_sequence_def)
    show "sargs + {#sarg#} = image_mset get_s (filter_mset is_Shared (mset (Shared sarg # s)))"
      using \<open>possible_sequence sargs uargs s \<and> v1 = compute sact uact v0 s\<close> possible_sequence_def by auto
  qed
  then show ?case
    using \<open>possible_sequence sargs uargs s \<and> v1 = compute sact uact v0 s\<close> by auto
next
  case (UniqueStep sact uact v0 sargs uargs v1 k uarg)
  then obtain s where "possible_sequence sargs uargs s \<and> v1 = compute sact uact v0 s" by blast
  let ?s = "Unique k uarg # s"
  have "possible_sequence sargs (uargs(k := uarg # uargs k)) ?s"
  proof (rule possible_sequenceI)
    show "\<And>i. (uargs(k := uarg # uargs k)) i = map get_u (filter (is_Unique_i i) (Unique k uarg # s))"
    proof -
      fix i show "(uargs(k := uarg # uargs k)) i = map get_u (filter (is_Unique_i i) (Unique k uarg # s))"
      proof (cases "i = k")
        case True
        then show ?thesis
          using Cons_eq_map_conv \<open>possible_sequence sargs uargs s \<and> v1 = compute sact uact v0 s\<close>
            action.disc(2) action.sel(2) action.sel(3) filter.simps(2) fun_upd_same is_Unique_def
            is_Unique_i_def possible_sequence_def[of sargs uargs s]
          by fastforce
      next
        case False
        then show ?thesis
          by (metis \<open>possible_sequence sargs uargs s \<and> v1 = compute sact uact v0 s\<close> action.sel(2) filter.simps(2) fun_upd_other is_Unique_i_def possible_sequence_def)
      qed
    qed
    show "sargs = image_mset get_s (filter_mset is_Shared (mset (Unique k uarg # s)))"
      using \<open>possible_sequence sargs uargs s \<and> v1 = compute sact uact v0 s\<close> possible_sequence_def by force
  qed
  then show ?case using \<open>possible_sequence sargs uargs s \<and> v1 = compute sact uact v0 s\<close>
    by (metis compute.simps(3))
qed

lemma PRE_shared_simpler_implies:
  assumes "PRE_shared_simpler spre a b"
  shows "PRE_shared spre a b"
  using assms
proof (induct rule: PRE_shared_simpler.induct)
  case (Empty spre)
  then show ?case
    by (simp add: PRE_shared_def)
next
  case (Step spre a b xa xb)
  then obtain ms where "image_mset fst ms = a \<and> image_mset snd ms = b \<and> (\<forall>x\<in>#ms. spre (fst x) (snd x))"
    by (metis PRE_shared_def)
  then have "image_mset fst (ms + {# (xa, xb) #}) = (a + {#xa#}) \<and> image_mset snd (ms + {# (xa, xb) #}) = (b + {#xb#}) \<and> (\<forall>x\<in>#(ms + {# (xa, xb) #}). spre (fst x) (snd x))"
    using Step.hyps(3) by auto
  then show ?case using PRE_shared_def by blast
qed

theorem main_result:
  assumes "reachable_value sact uact v0 sargs uargs v"
      and "reachable_value sact uact v0' sargs' uargs' v'"
      and "PRE_shared_simpler spre sargs sargs'"
      and "\<And>k. PRE_unique (upre k) (uargs k) (uargs' k)"
      and "\<alpha> v0 = \<alpha> v0'"
      and "all_axioms \<alpha> sact spre uact upre"
    shows "\<alpha> v = \<alpha> v'"
proof -
  obtain s s' where "possible_sequence sargs uargs s \<and> v = compute sact uact v0 s" "possible_sequence sargs' uargs' s' \<and> v' = compute sact uact v0' s'" 
    using assms(1) assms(2) reachable_then_possible_sequence_and_compute
    by metis
  then show ?thesis
    by (meson PRE_shared_simpler_implies assms(3) assms(4) assms(5) assms(6) main_lemma)
qed

end
