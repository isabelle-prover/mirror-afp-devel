theory Earley_Recognizer
  imports
    Earley_Fixpoint
begin

section \<open>Earley recognizer\<close>

subsection \<open>List auxilaries\<close>

fun filter_with_index' :: "nat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) list" where
  "filter_with_index' _ _ [] = []"
| "filter_with_index' i P (x#xs) = (
    if P x then (x,i) # filter_with_index' (i+1) P xs
    else filter_with_index' (i+1) P xs)"

definition filter_with_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) list" where
  "filter_with_index P xs = filter_with_index' 0 P xs"

lemma filter_with_index'_P:
  "(x, n) \<in> set (filter_with_index' i P xs) \<Longrightarrow> P x"
  by (induction xs arbitrary: i) (auto split: if_splits)

lemma filter_with_index_P:
  "(x, n) \<in> set (filter_with_index P xs) \<Longrightarrow> P x"
  by (metis filter_with_index'_P filter_with_index_def)

lemma filter_with_index'_cong_filter:
  "map fst (filter_with_index' i P xs) = filter P xs"
  by (induction xs arbitrary: i) auto

lemma filter_with_index_cong_filter:
  "map fst (filter_with_index P xs) = filter P xs"
  by (simp add: filter_with_index'_cong_filter filter_with_index_def)

lemma size_index_filter_with_index':
  "(x, n) \<in> set (filter_with_index' i P xs) \<Longrightarrow> n \<ge> i"
  by (induction xs arbitrary: i) (auto simp: Suc_leD split: if_splits)

lemma index_filter_with_index'_lt_length:
  "(x, n) \<in> set (filter_with_index' i P xs) \<Longrightarrow> n-i < length xs"
  by (induction xs arbitrary: i)(auto simp: less_Suc_eq_0_disj split: if_splits; metis Suc_diff_Suc leI)+

lemma index_filter_with_index_lt_length:
  "(x, n) \<in> set (filter_with_index P xs) \<Longrightarrow> n < length xs"
  by (metis filter_with_index_def index_filter_with_index'_lt_length minus_nat.diff_0)

lemma filter_with_index'_nth:
  "(x, n) \<in> set (filter_with_index' i P xs) \<Longrightarrow> xs ! (n-i) = x"
proof (induction xs arbitrary: i)
  case (Cons y xs)
  show ?case
  proof (cases "x = y")
    case True
    thus ?thesis
      using Cons by (auto simp: nth_Cons' split: if_splits)
  next
    case False
    hence "(x, n) \<in> set (filter_with_index' (i+1) P xs)"
      using Cons.prems by (cases xs) (auto split: if_splits)
    hence "n \<ge> i + 1" "xs ! (n - i - 1) = x"
      by (auto simp: size_index_filter_with_index' Cons.IH)
    thus ?thesis
      by simp
  qed
qed simp

lemma filter_with_index_nth:
  "(x, n) \<in> set (filter_with_index P xs) \<Longrightarrow> xs ! n = x"
  by (metis diff_zero filter_with_index'_nth filter_with_index_def)

lemma filter_with_index_nonempty:
  "x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> filter_with_index P xs \<noteq> []"
  by (metis filter_empty_conv filter_with_index_cong_filter list.map(1))

lemma filter_with_index'_Ex_first:
  "(\<exists>x i xs'. filter_with_index' n P xs = (x, i)#xs') \<longleftrightarrow> (\<exists>x \<in> set xs. P x)"
  by (induction xs arbitrary: n) auto

lemma filter_with_index_Ex_first:
  "(\<exists>x i xs'. filter_with_index P xs = (x, i)#xs') \<longleftrightarrow> (\<exists>x \<in> set xs. P x)"
  using filter_with_index'_Ex_first filter_with_index_def by metis


subsection \<open>Definitions\<close>

datatype pointer =
  Null
  | Pre nat \<comment>\<open>pre\<close>
  | PreRed "nat \<times> nat \<times> nat" "(nat \<times> nat \<times> nat) list" \<comment>\<open>k', pre, red\<close>

type_synonym 'a bin = "('a item \<times> pointer) list"
type_synonym 'a bins = "'a bin list"

definition items :: "'a bin \<Rightarrow> 'a item list" where
  "items b \<equiv> map fst b"

definition pointers :: "'a bin \<Rightarrow> pointer list" where
  "pointers b \<equiv> map snd b"

definition bins_eq_items :: "'a bins \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "bins_eq_items bs0 bs1 \<equiv> map items bs0 = map items bs1"

definition bins :: "'a bins \<Rightarrow> 'a item set" where
  "bins bs \<equiv> \<Union> { set (items (bs!k)) | k. k < length bs }"

definition bin_upto :: "'a bin \<Rightarrow> nat \<Rightarrow> 'a item set" where
  "bin_upto b i \<equiv> { items b ! j | j. j < i \<and> j < length (items b) }"

definition bins_upto :: "'a bins \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a item set" where
  "bins_upto bs k i \<equiv> \<Union> { set (items (bs ! l)) | l. l < k } \<union> bin_upto (bs ! k) i"

definition wf_bin_items :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a item list \<Rightarrow> bool" where
  "wf_bin_items \<G> \<omega> k xs \<equiv> \<forall>x \<in> set xs. wf_item \<G> \<omega> x \<and> end_item x = k"

definition wf_bin :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a bin \<Rightarrow> bool" where
  "wf_bin \<G> \<omega> k b \<equiv> distinct (items b) \<and> wf_bin_items \<G> \<omega> k (items b)"

definition wf_bins :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "wf_bins \<G> \<omega> bs \<equiv> \<forall>k < length bs. wf_bin \<G> \<omega> k (bs!k)"

definition \<epsilon>_free :: "'a cfg \<Rightarrow> bool" where
  "\<epsilon>_free \<G> = (\<forall>r \<in> set (\<RR> \<G>). rhs_rule r \<noteq> [])"

definition nonempty_derives :: "'a cfg \<Rightarrow> bool" where
  "nonempty_derives \<G> \<equiv> \<forall>s. \<not> \<G> \<turnstile> [s] \<Rightarrow>\<^sup>* []"

definition Init\<^sub>L :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a bins" where
  "Init\<^sub>L \<G> \<omega> \<equiv>
    let rs = filter (\<lambda>r. lhs_rule r = \<SS> \<G>) (remdups (\<RR> \<G>)) in
    let b0 = map (\<lambda>r. (init_item r 0, Null)) rs in
    let bs = replicate (length \<omega> + 1) ([]) in
    bs[0 := b0]"

definition Scan\<^sub>L :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a item \<Rightarrow> nat \<Rightarrow> ('a item \<times> pointer) list" where
  "Scan\<^sub>L k \<omega> a x pre \<equiv>
    if \<omega>!k = a then
      let x' = inc_item x (k+1) in
      [(x', Pre pre)]
    else []"

definition Predict\<^sub>L :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a \<Rightarrow> ('a item \<times> pointer) list" where
  "Predict\<^sub>L k \<G> X \<equiv>
    let rs = filter (\<lambda>r. lhs_rule r = X) (\<RR> \<G>) in
    map (\<lambda>r. (init_item r k, Null)) rs"

definition Complete\<^sub>L :: "nat \<Rightarrow> 'a item \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> ('a item \<times> pointer) list" where
  "Complete\<^sub>L k y bs red \<equiv>
    let orig = bs ! (start_item y) in
    let is = filter_with_index (\<lambda>x. next_symbol x = Some (lhs_item y)) (items orig) in
    map (\<lambda>(x, pre). (inc_item x k, PreRed (start_item y, pre, red) [])) is"

fun upd_bin :: "'a item \<times> pointer \<Rightarrow> 'a bin \<Rightarrow> 'a bin" where
  "upd_bin e' [] = [e']"
| "upd_bin e' (e#es) = (
    case (e', e) of
      ((x, PreRed px xs), (y, PreRed py ys)) \<Rightarrow>
        if x = y then (x, PreRed py (px#xs@ys)) # es
        else e # upd_bin e' es
      | _ \<Rightarrow>
        if fst e' = fst e then e # es
        else e # upd_bin e' es)"

fun upds_bin :: "('a item \<times> pointer) list \<Rightarrow> 'a bin \<Rightarrow> 'a bin" where
  "upds_bin [] b = b"
| "upds_bin (e#es) b = upds_bin es (upd_bin e b)"

definition upd_bins :: "'a bins \<Rightarrow> nat \<Rightarrow> ('a item \<times> pointer) list \<Rightarrow> 'a bins" where
  "upd_bins bs k es \<equiv> bs[k := upds_bin es (bs!k)]"

partial_function (tailrec) Earley\<^sub>L_bin' :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a bins" where
  "Earley\<^sub>L_bin' k \<G> \<omega> bs i = (
    if i \<ge> length (items (bs ! k)) then bs
    else
      let x = items (bs!k) ! i in
      let bs' =
        case next_symbol x of
          Some a \<Rightarrow> (
            if a \<notin> nonterminals \<G> then
              if k < length \<omega> then upd_bins bs (k+1) (Scan\<^sub>L k \<omega> a x i)
              else bs
            else upd_bins bs k (Predict\<^sub>L k \<G> a))
        | None \<Rightarrow> upd_bins bs k (Complete\<^sub>L k x bs i)
      in Earley\<^sub>L_bin' k \<G> \<omega> bs' (i+1))"

declare Earley\<^sub>L_bin'.simps[code]

definition Earley\<^sub>L_bin :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a bins \<Rightarrow> 'a bins" where
  "Earley\<^sub>L_bin k \<G> \<omega> bs = Earley\<^sub>L_bin' k \<G> \<omega> bs 0"

fun Earley\<^sub>L_bins :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a bins" where
  "Earley\<^sub>L_bins 0 \<G> \<omega> = Earley\<^sub>L_bin 0 \<G> \<omega> (Init\<^sub>L \<G> \<omega>)"
| "Earley\<^sub>L_bins (Suc n) \<G> \<omega> = Earley\<^sub>L_bin (Suc n) \<G> \<omega> (Earley\<^sub>L_bins n \<G> \<omega>)"

definition Earley\<^sub>L :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a bins" where
  "Earley\<^sub>L \<G> \<omega> \<equiv> Earley\<^sub>L_bins (length \<omega>) \<G> \<omega>"

definition recognizer :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> bool" where
  "recognizer \<G> \<omega> = (\<exists>x \<in> set (items (Earley\<^sub>L \<G> \<omega> ! length \<omega>)). is_finished \<G> \<omega> x)"


subsection \<open>Epsilon productions\<close>

lemma \<epsilon>_free_impl_non_empty_word_deriv:
  "\<epsilon>_free \<G> \<Longrightarrow> a \<noteq> [] \<Longrightarrow> \<not> Derivation \<G> a D []"
proof (induction "length D" arbitrary: a D rule: nat_less_induct)
  case 1
  show ?case
  proof (rule ccontr)
    assume assm: "\<not> \<not> Derivation \<G> a D []"
    show False
    proof (cases "D = []")
      case True
      then show ?thesis
        using "1.prems"(2) assm by auto
    next
      case False
      then obtain d D' \<alpha> where *:
        "D = d # D'" "Derives1 \<G> a (fst d) (snd d) \<alpha>" "Derivation \<G> \<alpha> D' []" "snd d \<in> set (\<RR> \<G>)"
        using list.exhaust assm Derives1_def by (metis Derivation.simps(2))
      show ?thesis
      proof cases
        assume "\<alpha> = []"
        thus ?thesis
          using *(2,4) Derives1_split \<epsilon>_free_def rhs_rule_def "1.prems"(1) by (metis append_is_Nil_conv)
      next
        assume "\<not> \<alpha> = []"
        thus ?thesis
          using *(1,3) "1.hyps" "1.prems"(1) by auto
      qed
    qed
  qed
qed

lemma \<epsilon>_free_impl_nonempty_derives:
  "\<epsilon>_free \<G> \<Longrightarrow> nonempty_derives \<G>"
  using \<epsilon>_free_impl_non_empty_word_deriv derives_implies_Derivation nonempty_derives_def by (metis not_Cons_self2)

lemma nonempty_derives_impl_\<epsilon>_free:
  assumes "nonempty_derives \<G>"
  shows "\<epsilon>_free \<G>"
proof (rule ccontr)
  assume "\<not> \<epsilon>_free \<G>"
  then obtain N \<alpha> where *: "(N, \<alpha>) \<in> set (\<RR> \<G>)" "rhs_rule (N, \<alpha>) = []"
    unfolding \<epsilon>_free_def by auto
  hence "\<G> \<turnstile> [N] \<Rightarrow> []"
    unfolding derives1_def rhs_rule_def by auto
  hence "\<G> \<turnstile> [N] \<Rightarrow>\<^sup>* []"
    by auto
  thus False
    using assms(1) nonempty_derives_def by fast
qed

lemma nonempty_derives_iff_\<epsilon>_free:
  shows "nonempty_derives \<G> \<longleftrightarrow> \<epsilon>_free \<G>"
  using \<epsilon>_free_impl_nonempty_derives nonempty_derives_impl_\<epsilon>_free by blast


subsection \<open>Bin lemmas\<close>

lemma length_upd_bins[simp]:
  "length (upd_bins bs k es) = length bs"
  unfolding upd_bins_def by simp

lemma length_upd_bin:
  "length (upd_bin e b) \<ge> length b"
  by (induction e b rule: upd_bin.induct) (auto split: pointer.splits)

lemma length_upds_bin:
  "length (upds_bin es b) \<ge> length b"
  by (induction es arbitrary: b) (auto, meson le_trans length_upd_bin)

lemma length_nth_upd_bin_bins:
  "length (upd_bins bs k es ! n) \<ge> length (bs ! n)"
  unfolding upd_bins_def using length_upds_bin
  by (metis linorder_not_le list_update_beyond nth_list_update_eq nth_list_update_neq order_refl)

lemma nth_idem_upd_bins:
  "k \<noteq> n \<Longrightarrow> upd_bins bs k es ! n = bs ! n"
  unfolding upd_bins_def by simp

lemma items_nth_idem_upd_bin:
  "n < length b \<Longrightarrow> items (upd_bin e b) ! n = items b ! n"
  by (induction b arbitrary: e n) (auto simp: items_def less_Suc_eq_0_disj split!: pointer.split)

lemma items_nth_idem_upds_bin:
  "n < length b \<Longrightarrow> items (upds_bin es b) ! n = items b ! n"
  by (induction es arbitrary: b)
    (auto, metis items_nth_idem_upd_bin length_upd_bin order.strict_trans2)

lemma items_nth_idem_upd_bins:
  "n < length (bs ! k) \<Longrightarrow> items (upd_bins bs k es ! k) ! n = items (bs ! k) ! n"
  unfolding upd_bins_def using items_nth_idem_upds_bin
  by (metis linorder_not_less list_update_beyond nth_list_update_eq)

lemma bin_upto_eq_set_items:
  "i \<ge> length b \<Longrightarrow> bin_upto b i = set (items b)"
  by (auto simp: bin_upto_def items_def, metis fst_conv in_set_conv_nth nth_map order.strict_trans2)

lemma bins_upto_empty:
  "bins_upto bs 0 0 = {}"
  unfolding bins_upto_def bin_upto_def by simp

lemma set_items_upd_bin:
  "set (items (upd_bin e b)) = set (items b) \<union> {fst e}"
proof (induction b arbitrary: e)
  case (Cons b bs)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = (x, PreRed xp xs) \<and> b = (y, PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where "e = (x, PreRed xp xs)" "b = (y, PreRed yp ys)"
      by blast
    thus ?thesis
      using Cons.IH by (auto simp: items_def)
  next
    case False
    then show ?thesis
    proof cases
      assume *: "fst e = fst b"
      hence "upd_bin e (b # bs) = b # bs"
        using False by (auto split: pointer.splits prod.split)
      thus ?thesis
        using * by (auto simp: items_def)
    next
      assume *: "\<not> fst e = fst b"
      hence "upd_bin e (b # bs) = b # upd_bin e bs"
        using False by (auto split: pointer.splits prod.split)
      thus ?thesis
        using * Cons.IH by (auto simp: items_def)
    qed
  qed
qed (auto simp: items_def)

lemma set_items_upds_bin:
  "set (items (upds_bin es b)) = set (items b) \<union> set (items es)"
  apply (induction es arbitrary: b)
      apply (auto simp: items_def)
  by (metis Domain.DomainI Domain_fst Un_insert_right fst_conv insert_iff items_def list.set_map set_items_upd_bin sup_bot.right_neutral)+

lemma bins_upd_bins:
  assumes "k < length bs"
  shows "bins (upd_bins bs k es) = bins bs \<union> set (items es)"
proof -
  let ?bs = "upd_bins bs k es"
  have "bins (upd_bins bs k es) = \<Union> {set (items (?bs ! k)) |k. k < length ?bs}"
    unfolding bins_def by blast
  also have "... = \<Union> {set (items (bs ! l)) |l. l < length bs \<and> l \<noteq> k} \<union> set (items (?bs ! k))"
    unfolding upd_bins_def using assms by (auto, metis nth_list_update)
  also have "... = \<Union> {set (items (bs ! l)) |l. l < length bs \<and> l \<noteq> k} \<union> set (items (bs ! k)) \<union> set (items es)"
    using set_items_upds_bin[of es "bs!k"] by (simp add: assms upd_bins_def sup_assoc)
  also have "... = \<Union> {set (items (bs ! k)) |k. k < length bs} \<union> set (items es)"
    using assms by blast
  also have "... = bins bs \<union> set (items es)"
    unfolding bins_def by blast
  finally show ?thesis .
qed

lemma kth_bin_sub_bins:
  "k < length bs \<Longrightarrow> set (items (bs ! k)) \<subseteq> bins bs"
  unfolding bins_def bins_upto_def bin_upto_def by blast+

lemma bin_upto_Cons_0:
  "bin_upto (e#es) 0 = {}"
  by (auto simp: bin_upto_def)

lemma bin_upto_Cons:
  assumes "0 < n"
  shows "bin_upto (e#es) n = { fst e } \<union> bin_upto es (n-1)"
proof -
  have "bin_upto (e#es) n = { items (e#es) ! j | j. j < n \<and> j < length (items (e#es)) }"
    unfolding bin_upto_def by blast
  also have "... = { fst e } \<union> { items es ! j | j. j < (n-1) \<and> j < length (items es) }"
    using assms by (cases n) (auto simp: items_def nth_Cons', metis One_nat_def Zero_not_Suc diff_Suc_1 not_less_eq nth_map)
  also have "... = { fst e } \<union> bin_upto es (n-1)"
    unfolding bin_upto_def by blast
  finally show ?thesis .
qed

lemma bin_upto_nth_idem_upd_bin:
  "n < length b \<Longrightarrow> bin_upto (upd_bin e b) n = bin_upto b n"
proof (induction b arbitrary: e n)
  case (Cons b bs)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = (x, PreRed xp xs) \<and> b = (y, PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where "e = (x, PreRed xp xs)" "b = (y, PreRed yp ys)"
      by blast
    thus ?thesis
      using Cons bin_upto_Cons_0
      by (cases n) (auto simp: items_def bin_upto_Cons, blast+)
  next
    case False
    then show ?thesis
    proof cases
      assume *: "fst e = fst b"
      hence "upd_bin e (b # bs) = b # bs"
        using False by (auto split: pointer.splits prod.split)
      thus ?thesis
        using * by (auto simp: items_def)
    next
      assume *: "\<not> fst e = fst b"
      hence "upd_bin e (b # bs) = b # upd_bin e bs"
        using False by (auto split: pointer.splits prod.split)
      thus ?thesis
        using * Cons
        by (cases n) (auto simp: items_def bin_upto_Cons_0 bin_upto_Cons)
    qed
  qed
qed (auto simp: items_def)

lemma bin_upto_nth_idem_upds_bin:
  "n < length b \<Longrightarrow> bin_upto (upds_bin es b) n = bin_upto b n"
  using bin_upto_nth_idem_upd_bin length_upd_bin
  apply (induction es arbitrary: b)
   apply auto
  using order.strict_trans2 order.strict_trans1 by blast+

lemma bins_upto_kth_nth_idem:
  assumes "l < length bs" "k \<le> l" "n < length (bs ! k)"
  shows "bins_upto (upd_bins bs l es) k n = bins_upto bs k n"
proof -
  let ?bs = "upd_bins bs l es"
  have "bins_upto ?bs k n = \<Union> {set (items (?bs ! l)) |l. l < k} \<union> bin_upto (?bs ! k) n"
    unfolding bins_upto_def by blast
  also have "... = \<Union> {set (items (bs ! l)) |l. l < k} \<union> bin_upto (?bs ! k) n"
    unfolding upd_bins_def using assms(1,2) by auto
  also have "... = \<Union> {set (items (bs ! l)) |l. l < k} \<union> bin_upto (bs ! k) n"
    unfolding upd_bins_def using assms(1,3) bin_upto_nth_idem_upds_bin
    by (metis (no_types, lifting) nth_list_update)
  also have "... = bins_upto bs k n"
    unfolding bins_upto_def by blast
  finally show ?thesis .
qed

lemma bins_upto_sub_bins:
  "k < length bs \<Longrightarrow> bins_upto bs k n \<subseteq> bins bs"
  unfolding bins_def bins_upto_def bin_upto_def using less_trans by (auto, blast)

lemma bins_upto_Suc_Un:
  "n < length (bs ! k) \<Longrightarrow> bins_upto bs k (n+1) = bins_upto bs k n \<union> { items (bs ! k) ! n }"
  unfolding bins_upto_def bin_upto_def using less_Suc_eq by (auto simp: items_def, metis nth_map)

lemma bins_bin_exists:
  "x \<in> bins bs \<Longrightarrow> \<exists>k < length bs. x \<in> set (items (bs ! k))"
  unfolding bins_def by blast

lemma distinct_upd_bin:
  "distinct (items b) \<Longrightarrow> distinct (items (upd_bin e b))"
proof (induction b arbitrary: e)
  case (Cons b bs)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = (x, PreRed xp xs) \<and> b = (y, PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where "e = (x, PreRed xp xs)" "b = (y, PreRed yp ys)"
      by blast
    thus ?thesis
      using Cons
      apply (auto simp: items_def split: prod.split)
      by (metis Domain.DomainI Domain_fst UnE empty_iff fst_conv insert_iff items_def list.set_map set_items_upd_bin)
  next
    case False
    then show ?thesis
    proof cases
      assume *: "fst e = fst b"
      hence "upd_bin e (b # bs) = b # bs"
        using False by (auto split: pointer.splits prod.split)
      thus ?thesis
        using * Cons.prems by (auto simp: items_def)
    next
      assume *: "\<not> fst e = fst b"
      hence "upd_bin e (b # bs) = b # upd_bin e bs"
        using False by (auto split: pointer.splits prod.split)
      moreover have "distinct (items (upd_bin e bs))"
        using Cons by (auto simp: items_def)
      ultimately show ?thesis
        using * Cons.prems set_items_upd_bin
        by (metis Un_insert_right distinct.simps(2) insertE items_def list.simps(9) sup_bot_right)
    qed
  qed
qed (auto simp: items_def)

lemma distinct_upds_bin:
  "distinct (items b) \<Longrightarrow> distinct (items (upds_bin es b))"
  by (induction es arbitrary: b) (auto simp add: distinct_upd_bin)

lemma wf_bins_kth_bin:
  "wf_bins \<G> \<omega> bs \<Longrightarrow> k < length bs \<Longrightarrow> x \<in> set (items (bs ! k)) \<Longrightarrow> wf_item \<G> \<omega> x \<and> end_item x = k"
  using wf_bin_def wf_bins_def wf_bin_items_def by blast

lemma wf_bin_upd_bin:
  assumes "wf_bin \<G> \<omega> k b" "wf_item \<G> \<omega> (fst e) \<and> end_item (fst e) = k"
  shows "wf_bin \<G> \<omega> k (upd_bin e b)"
  using assms
proof (induction b arbitrary: e)
  case (Cons b bs)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = (x, PreRed xp xs) \<and> b = (y, PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where "e = (x, PreRed xp xs)" "b = (y, PreRed yp ys)"
      by blast
    thus ?thesis
      using Cons distinct_upd_bin wf_bin_def wf_bin_items_def set_items_upd_bin
      by (smt (verit, best) Un_insert_right insertE sup_bot.right_neutral)
  next
    case False
    then show ?thesis
    proof cases
      assume *: "fst e = fst b"
      hence "upd_bin e (b # bs) = b # bs"
        using False by (auto split: pointer.splits prod.split)
      thus ?thesis
        using * Cons.prems by (auto simp: items_def)
    next
      assume *: "\<not> fst e = fst b"
      hence "upd_bin e (b # bs) = b # upd_bin e bs"
        using False by (auto split: pointer.splits prod.split)
      thus ?thesis
        using * Cons.prems set_items_upd_bin distinct_upd_bin wf_bin_def wf_bin_items_def
        by (smt (verit, best) Un_insert_right insertE sup_bot_right)
    qed
  qed
qed (auto simp: items_def wf_bin_def wf_bin_items_def)

lemma wf_upd_bins_bin:
  assumes "wf_bin \<G> \<omega> k b"
  assumes "\<forall>x \<in> set (items es). wf_item \<G> \<omega> x \<and> end_item x = k"
  shows "wf_bin \<G> \<omega> k (upds_bin es b)"
  using assms by (induction es arbitrary: b) (auto simp: wf_bin_upd_bin items_def)

lemma wf_bins_upd_bins:
  assumes "wf_bins \<G> \<omega> bs"
  assumes "\<forall>x \<in> set (items es). wf_item \<G> \<omega> x \<and> end_item x = k"
  shows "wf_bins \<G> \<omega> (upd_bins bs k es)"
  unfolding upd_bins_def using assms wf_upd_bins_bin wf_bins_def
  by (metis length_list_update nth_list_update_eq nth_list_update_neq)

lemma wf_bins_impl_wf_items:
  "wf_bins \<G> \<omega> bs \<Longrightarrow> \<forall>x \<in> (bins bs). wf_item \<G> \<omega> x"
  unfolding wf_bins_def wf_bin_def wf_bin_items_def bins_def by auto

lemma upds_bin_eq_items:
  "set (items es) \<subseteq> set (items b) \<Longrightarrow> set (items (upds_bin es b)) = set (items b)"
  apply (induction es arbitrary: b)
   apply (auto simp: set_items_upd_bin set_items_upds_bin)
   apply (simp add: items_def)
  by (metis Un_upper2 upds_bin.simps(2) in_mono set_items_upds_bin sup.orderE)

lemma bin_eq_items_upd_bin:
  "fst e \<in> set (items b) \<Longrightarrow> items (upd_bin e b) = items b"
proof (induction b arbitrary: e)
  case (Cons b bs)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = (x, PreRed xp xs) \<and> b = (y, PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where "e = (x, PreRed xp xs)" "b = (y, PreRed yp ys)"
      by blast
    thus ?thesis
      using Cons by (auto simp: items_def, metis fst_conv image_eqI)
  next
    case False
    then show ?thesis
    proof cases
      assume *: "fst e = fst b"
      hence "upd_bin e (b # bs) = b # bs"
        using False by (auto split: pointer.splits prod.split)
      thus ?thesis
        using * Cons.prems by (auto simp: items_def)
    next
      assume *: "\<not> fst e = fst b"
      hence "upd_bin e (b # bs) = b # upd_bin e bs"
        using False by (auto split: pointer.splits prod.split)
      thus ?thesis
        using * Cons by (auto simp: items_def)
    qed
  qed
qed (auto simp: items_def)

lemma bin_eq_items_upds_bin:
  assumes "set (items es) \<subseteq> set (items b)"
  shows "items (upds_bin es b) = items b"
  using assms
proof (induction es arbitrary: b)
  case (Cons e es)
  have "items (upds_bin es (upd_bin e b)) = items (upd_bin e b)"
    using Cons upds_bin_eq_items set_items_upd_bin set_items_upds_bin
    by (metis Un_upper2 upds_bin.simps(2) sup.coboundedI1)
  moreover have "items (upd_bin e b) = items b"
    by (metis Cons.prems bin_eq_items_upd_bin items_def list.set_intros(1) list.simps(9) subset_code(1))
  ultimately show ?case
    by simp
qed (auto simp: items_def)

lemma bins_eq_items_upd_bins:
  assumes "set (items es) \<subseteq> set (items (bs!k))"
  shows "bins_eq_items (upd_bins bs k es) bs"
  unfolding upd_bins_def using assms bin_eq_items_upds_bin bins_eq_items_def
  by (metis list_update_id map_update)

lemma bins_eq_items_imp_eq_bins:
  "bins_eq_items bs bs' \<Longrightarrow> bins bs = bins bs'"
  unfolding bins_eq_items_def bins_def items_def
  by (metis (no_types, lifting) length_map nth_map)

lemma bin_eq_items_dist_upd_bin_bin:
  assumes "items a = items b"
  shows "items (upd_bin e a) = items (upd_bin e b)"
  using assms
proof (induction a arbitrary: e b)
  case (Cons a as)
  obtain b' bs where bs: "b = b' # bs" "fst a = fst b'" "items as = items bs"
    using Cons.prems by (auto simp: items_def)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = (x, PreRed xp xs) \<and> a = (y, PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where #: "e = (x, PreRed xp xs)" "a = (y, PreRed yp ys)"
      by blast
    show ?thesis
    proof cases
      assume *: "x = y"
      hence "items (upd_bin e (a # as)) = x # items as"
        using # by (auto simp: items_def)
      moreover have "items (upd_bin e (b' # bs)) = x # items bs"
        using bs # * by (auto simp: items_def split: pointer.splits prod.splits)
      ultimately show ?thesis
        using bs by simp
    next
      assume *: "\<not> x = y"
      hence "items (upd_bin e (a # as)) = y # items (upd_bin e as)"
        using # by (auto simp: items_def)
      moreover have "items (upd_bin e (b' # bs)) = y # items (upd_bin e bs)"
        using bs # * by (auto simp: items_def split: pointer.splits prod.splits)
      ultimately show ?thesis
        using bs Cons.IH by simp
    qed
  next
    case False
    then show ?thesis
    proof cases
      assume *: "fst e = fst a"
      hence "items (upd_bin e (a # as)) = fst a # items as"
        using False by (auto simp: items_def split: pointer.splits prod.splits)
      moreover have "items (upd_bin e (b' # bs)) = fst b' # items bs"
        using bs False * by (auto simp: items_def split: pointer.splits prod.splits)
      ultimately show ?thesis
        using bs by simp
    next
      assume *: "\<not> fst e = fst a"
      hence "items (upd_bin e (a # as)) = fst a # items (upd_bin e as)"
        using False by (auto simp: items_def split: pointer.splits prod.splits)
      moreover have "items (upd_bin e (b' # bs)) = fst b' # items (upd_bin e bs)"
        using bs False * by (auto simp: items_def split: pointer.splits prod.splits)
      ultimately show ?thesis
        using bs Cons by simp
    qed
  qed
qed (auto simp: items_def)

lemma bin_eq_items_dist_upds_bin_bin:
  assumes "items a = items b"
  shows "items (upds_bin es a) = items (upds_bin es b)"
  using assms
proof (induction es arbitrary: a b)
  case (Cons e es)
  hence "items (upds_bin es (upd_bin e a)) = items (upds_bin es (upd_bin e b))"
    using bin_eq_items_dist_upd_bin_bin by blast
  thus ?case
    by simp
qed simp

lemma bin_eq_items_dist_upd_bin_entry:
  assumes "fst e = fst e'"
  shows "items (upd_bin e b) = items (upd_bin e' b)"
  using assms
proof (induction b arbitrary: e e')
  case (Cons a as)
  show ?case
  proof (cases "\<exists>x xp xs y yp ys. e = (x, PreRed xp xs) \<and> a = (y, PreRed yp ys)")
    case True
    then obtain x xp xs y yp ys where #: "e = (x, PreRed xp xs)" "a = (y, PreRed yp ys)"
      by blast
    show ?thesis
    proof cases
      assume *: "x = y"
      thus ?thesis
        using # Cons.prems by (auto simp: items_def split: pointer.splits prod.splits)
    next
      assume *: "\<not> x = y"
      thus ?thesis
        using # Cons.prems
        by (auto simp: items_def split!: pointer.splits prod.splits, metis Cons.IH Cons.prems items_def)+
    qed
  next
    case False
    then show ?thesis
    proof cases
      assume *: "fst e = fst a"
      thus ?thesis
        using Cons.prems by (auto simp: items_def split: pointer.splits prod.splits)
    next
      assume *: "\<not> fst e = fst a"
      thus ?thesis
        using Cons.prems
        by (auto simp: items_def split!: pointer.splits prod.splits, metis Cons.IH Cons.prems items_def)+
    qed
  qed
qed (auto simp: items_def)

lemma bin_eq_items_dist_upds_bin_entries:
  assumes "items es = items es'"
  shows "items (upds_bin es b) = items (upds_bin es' b)"
  using assms
proof (induction es arbitrary: es' b)
  case (Cons e es)
  then obtain e' es'' where "fst e = fst e'" "items es = items es''" "es' = e' # es''"
    by (auto simp: items_def)
  hence "items (upds_bin es (upd_bin e b)) = items (upds_bin es'' (upd_bin e' b))"
    using Cons.IH
    by (metis bin_eq_items_dist_upd_bin_entry bin_eq_items_dist_upds_bin_bin)
  thus ?case
    by (simp add: \<open>es' = e' # es''\<close>)
qed (auto simp: items_def)

lemma bins_eq_items_dist_upd_bins:
  assumes "bins_eq_items as bs" "items aes = items bes" "k < length as"
  shows "bins_eq_items (upd_bins as k aes) (upd_bins bs k bes)"
proof -
  have "k < length bs"
    using assms(1,3) bins_eq_items_def map_eq_imp_length_eq by metis
  hence "items (upds_bin (as!k) aes) = items (upds_bin (bs!k) bes)"
    using bin_eq_items_dist_upds_bin_entries bin_eq_items_dist_upds_bin_bin bins_eq_items_def assms
    by (metis (no_types, lifting) nth_map)
  thus ?thesis
    using \<open>k < length bs\<close> assms bin_eq_items_dist_upds_bin_bin bin_eq_items_dist_upds_bin_entries
      bins_eq_items_def upd_bins_def by (smt (verit) map_update nth_map)
qed


subsection \<open>Well-formed bins\<close>

lemma wf_bins_Scan\<^sub>L':
  assumes "wf_bins \<G> \<omega> bs" "k < length bs" "x \<in> set (items (bs ! k))"
  assumes "k < length \<omega>" "next_symbol x \<noteq> None" "y = inc_item x (k+1)"
  shows "wf_item \<G> \<omega> y \<and> end_item y = k+1"
  using assms wf_bins_kth_bin[OF assms(1-3)]
  unfolding wf_item_def inc_item_def next_symbol_def is_complete_def rhs_item_def
  by (auto split: if_splits)

lemma wf_bins_Scan\<^sub>L:
  assumes "wf_bins \<G> \<omega> bs" "k < length bs" "x \<in> set (items (bs ! k))" "k < length \<omega>" "next_symbol x \<noteq> None"
  shows "\<forall>y \<in> set (items (Scan\<^sub>L k \<omega> a x pre)). wf_item \<G> \<omega> y \<and> end_item y = (k+1)"
  using wf_bins_Scan\<^sub>L'[OF assms] by (simp add: Scan\<^sub>L_def items_def)

lemma wf_bins_Predict\<^sub>L:
  assumes "wf_bins \<G> \<omega> bs" "k < length bs" "k \<le> length \<omega>"
  shows "\<forall>y \<in> set (items (Predict\<^sub>L k \<G> X)). wf_item \<G> \<omega> y \<and> end_item y = k"
  using assms by (auto simp: Predict\<^sub>L_def wf_item_def wf_bins_def wf_bin_def init_item_def items_def)

lemma wf_item_inc_item:
  assumes "wf_item \<G> \<omega> x" "next_symbol x = Some a" "start_item x \<le> k" "k \<le> length \<omega>"
  shows "wf_item \<G> \<omega> (inc_item x k) \<and> end_item (inc_item x k) = k"
  using assms by (auto simp: wf_item_def inc_item_def rhs_item_def next_symbol_def is_complete_def split: if_splits)

lemma wf_bins_Complete\<^sub>L:
  assumes "wf_bins \<G> \<omega> bs" "k < length bs" "y \<in> set (items (bs ! k))"
  shows "\<forall>x \<in> set (items (Complete\<^sub>L k y bs red)). wf_item \<G> \<omega> x \<and> end_item x = k"
proof -
  let ?orig = "bs ! (start_item y)"
  let ?is = "filter_with_index (\<lambda>x. next_symbol x = Some (lhs_item y)) (items ?orig)"
  let ?is' = "map (\<lambda>(x, pre). (inc_item x k, PreRed (start_item y, pre, red) [])) ?is"
  {
    fix x
    assume *: "x \<in> set (map fst ?is)"
    have "end_item x = start_item y"
      using * assms wf_bins_kth_bin wf_item_def filter_with_index_cong_filter
      by (metis dual_order.strict_trans2 filter_is_subset subsetD)
    have "wf_item \<G> \<omega> x"
      using * assms wf_bins_kth_bin wf_item_def filter_with_index_cong_filter
      by (metis dual_order.strict_trans2 filter_is_subset subsetD)
    moreover have "next_symbol x = Some (lhs_item y)"
      using * by (simp add: filter_set filter_with_index_cong_filter)
    moreover have "start_item x \<le> k"
      using \<open>end_item x = start_item y\<close> \<open>wf_item \<G> \<omega> x\<close> assms wf_bins_kth_bin wf_item_def
      by (metis dual_order.order_iff_strict dual_order.strict_trans1)
    moreover have "k \<le> length \<omega>"
      using assms wf_bins_kth_bin wf_item_def by blast
    ultimately have "wf_item \<G> \<omega> (inc_item x k)" "end_item (inc_item x k) = k"
      by (simp_all add: wf_item_inc_item)
  }
  hence "\<forall>x \<in> set (items ?is'). wf_item \<G> \<omega> x \<and> end_item x = k"
    by (auto simp: items_def rev_image_eqI)
  thus ?thesis
    unfolding Complete\<^sub>L_def by presburger
qed

lemma Ex_wf_bins:
  "\<exists>n bs \<omega> \<G>. n \<le> length \<omega> \<and> length bs = Suc (length \<omega>) \<and> wf_bins \<G> \<omega> bs"
  apply (rule exI[where x="0"])
  apply (rule exI[where x="[[]]"])
  apply (rule exI[where x="[]"])
  by (auto simp: wf_bins_def wf_bin_def wf_bin_items_def items_def split: prod.splits)

definition wf_earley_input :: "(nat \<times> 'a cfg \<times> 'a list \<times> 'a bins) set" where
  "wf_earley_input = {
    (k, \<G>, \<omega>, bs) | k \<G> \<omega> bs.
      k \<le> length \<omega> \<and>
      length bs = length \<omega> + 1 \<and>
      wf_bins \<G> \<omega> bs
  }"

typedef 'a wf_bins = "wf_earley_input::(nat \<times> 'a cfg \<times> 'a list \<times> 'a bins) set"
  morphisms from_wf_bins to_wf_bins
  using Ex_wf_bins by (auto simp: wf_earley_input_def)

lemma wf_earley_input_elim:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  shows "k \<le> length \<omega> \<and> k < length bs \<and> length bs = length \<omega> + 1 \<and> wf_bins \<G> \<omega> bs"
  using assms(1) from_wf_bins wf_earley_input_def by (smt (verit) Suc_eq_plus1 less_Suc_eq_le mem_Collect_eq prod.sel(1) snd_conv)

lemma wf_earley_input_intro:
  assumes "k \<le> length \<omega>" "length bs = length \<omega> + 1" "wf_bins \<G> \<omega> bs"
  shows "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  by (simp add: assms wf_earley_input_def)

lemma wf_earley_input_Complete\<^sub>L:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input" "\<not> length (items (bs ! k)) \<le> i"
  assumes "x = items (bs ! k) ! i" "next_symbol x = None"
  shows "(k, \<G>, \<omega>, upd_bins bs k (Complete\<^sub>L k x bs red)) \<in> wf_earley_input"
proof -
  have *: "k \<le> length \<omega>" "length bs = length \<omega> + 1" "wf_bins \<G> \<omega> bs"
    using wf_earley_input_elim assms(1) by metis+
  have x: "x \<in> set (items (bs ! k))"
    using assms(2,3) by simp
  have "start_item x < length bs"
    using x wf_bins_kth_bin * wf_item_def
    by (metis One_nat_def add.right_neutral add_Suc_right dual_order.trans le_imp_less_Suc)
  hence "wf_bins \<G> \<omega> (upd_bins bs k (Complete\<^sub>L k x bs red))"
    using * Suc_eq_plus1 le_imp_less_Suc wf_bins_Complete\<^sub>L wf_bins_upd_bins x by metis
  thus ?thesis
    by (simp add: *(1-3) wf_earley_input_def)
qed

lemma wf_earley_input_Scan\<^sub>L:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input" "\<not> length (items (bs ! k)) \<le> i"
  assumes "x = items (bs ! k) ! i" "next_symbol x = Some a"
  assumes "k < length \<omega>"
  shows "(k, \<G>, \<omega>, upd_bins bs (k+1) (Scan\<^sub>L k \<omega> a x pre)) \<in> wf_earley_input"
proof -
  have *: "k \<le> length \<omega>" "length bs = length \<omega> + 1" "wf_bins \<G> \<omega> bs"
    using wf_earley_input_elim assms(1) by metis+
  have x: "x \<in> set (items(bs ! k))"
    using assms(2,3) by simp
  have "wf_bins \<G> \<omega> (upd_bins bs (k+1) (Scan\<^sub>L k \<omega> a x pre))"
    using * x assms(1,4,5) wf_bins_Scan\<^sub>L wf_bins_upd_bins wf_earley_input_elim
    by (metis option.discI)
  thus ?thesis
    by (simp add: *(1-3) wf_earley_input_def)
qed

lemma wf_earley_input_Predict\<^sub>L:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input" "\<not> length (items (bs ! k)) \<le> i"
  assumes "x = items (bs ! k) ! i" "next_symbol x = Some a"
  shows "(k, \<G>, \<omega>, upd_bins bs k (Predict\<^sub>L k \<G> a)) \<in> wf_earley_input"
proof -
  have *: "k \<le> length \<omega>" "length bs = length \<omega> + 1" "wf_bins \<G> \<omega> bs"
    using wf_earley_input_elim assms(1) by metis+
  have x: "x \<in> set (items (bs ! k))"
    using assms(2,3) by simp
  hence "wf_bins \<G> \<omega> (upd_bins bs k (Predict\<^sub>L k \<G> a))"
    using * x assms(1,4) wf_bins_Predict\<^sub>L wf_bins_upd_bins wf_earley_input_elim by metis
  thus ?thesis
    by (simp add: *(1-3) wf_earley_input_def)
qed

fun earley_measure :: "nat \<times> 'a cfg \<times> 'a list \<times> 'a bins \<Rightarrow> nat \<Rightarrow> nat" where
  "earley_measure (k, \<G>, \<omega>, bs) i = card { x | x. wf_item \<G> \<omega> x \<and> end_item x = k } - i"

lemma Earley\<^sub>L_bin'_simps[simp]:
  "i \<ge> length (items (bs ! k)) \<Longrightarrow> Earley\<^sub>L_bin' k \<G> \<omega> bs i = bs"
  "\<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs!k) ! i \<Longrightarrow> next_symbol x = None \<Longrightarrow>
    Earley\<^sub>L_bin' k \<G> \<omega> bs i = Earley\<^sub>L_bin' k \<G> \<omega> (upd_bins bs k (Complete\<^sub>L k x bs i)) (i+1)"
  "\<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
    a \<notin> nonterminals \<G> \<Longrightarrow> k < length \<omega> \<Longrightarrow> Earley\<^sub>L_bin' k \<G> \<omega> bs i = Earley\<^sub>L_bin' k \<G> \<omega> (upd_bins bs (k+1) (Scan\<^sub>L k \<omega> a x i)) (i+1)"
  "\<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
    a \<notin> nonterminals \<G> \<Longrightarrow> \<not> k < length \<omega> \<Longrightarrow> Earley\<^sub>L_bin' k \<G> \<omega> bs i = Earley\<^sub>L_bin' k \<G> \<omega> bs (i+1)"
  "\<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs!k) ! i \<Longrightarrow> next_symbol x = Some a \<Longrightarrow>
    a \<in> nonterminals \<G> \<Longrightarrow> Earley\<^sub>L_bin' k \<G> \<omega> bs i = Earley\<^sub>L_bin' k \<G> \<omega> (upd_bins bs k (Predict\<^sub>L k \<G> a)) (i+1)"
  by (subst Earley\<^sub>L_bin'.simps, auto)+

lemma Earley\<^sub>L_bin'_induct[case_names Base Complete\<^sub>F Scan\<^sub>F Pass Predict\<^sub>F]:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes base: "\<And>k \<G> \<omega> bs i. i \<ge> length (items (bs ! k)) \<Longrightarrow> P k \<G> \<omega> bs i"
  assumes complete: "\<And>k \<G> \<omega> bs i x. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = None \<Longrightarrow> P k \<G> \<omega> (upd_bins bs k (Complete\<^sub>L k x bs i)) (i+1) \<Longrightarrow> P k \<G> \<omega> bs i"
  assumes scan: "\<And>k \<G> \<omega> bs i x a. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> a \<notin> nonterminals \<G> \<Longrightarrow> k < length \<omega> \<Longrightarrow>
            P k \<G> \<omega> (upd_bins bs (k+1) (Scan\<^sub>L k \<omega> a x i)) (i+1) \<Longrightarrow> P k \<G> \<omega> bs i"
  assumes pass: "\<And>k \<G> \<omega> bs i x a. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> a \<notin> nonterminals \<G> \<Longrightarrow> \<not> k < length \<omega> \<Longrightarrow>
            P k \<G> \<omega> bs (i+1) \<Longrightarrow> P k \<G> \<omega> bs i"
  assumes predict: "\<And>k \<G> \<omega> bs i x a. \<not> i \<ge> length (items (bs ! k)) \<Longrightarrow> x = items (bs ! k) ! i \<Longrightarrow>
            next_symbol x = Some a \<Longrightarrow> a \<in> nonterminals \<G> \<Longrightarrow>
            P k \<G> \<omega> (upd_bins bs k (Predict\<^sub>L k \<G> a)) (i+1) \<Longrightarrow> P k \<G> \<omega> bs i"
  shows "P k \<G> \<omega> bs i"
  using assms(1)
proof (induction n\<equiv>"earley_measure (k, \<G>, \<omega>, bs) i" arbitrary: bs i rule: nat_less_induct)
  case 1
  have wf: "k \<le> length \<omega>" "length bs = length \<omega> + 1" "wf_bins \<G> \<omega> bs"
    using "1.prems" wf_earley_input_elim by metis+
  hence k: "k < length bs"
    by simp
  have fin: "finite { x | x. wf_item \<G> \<omega> x \<and> end_item x = k }"
    using finiteness_UNIV_wf_item by fastforce
  show ?case
  proof cases
    assume "i \<ge> length (items (bs ! k))"
    then show ?thesis
      by (simp add: base)
  next
    assume a1: "\<not> i \<ge> length (items (bs ! k))"
    let ?x = "items (bs ! k) ! i"
    have x: "?x \<in> set (items (bs ! k))"
      using a1 by fastforce
    show ?thesis
    proof cases
      assume a2: "next_symbol ?x = None"
      let ?bs' = "upd_bins bs k (Complete\<^sub>L k ?x bs i)"
      have "start_item ?x < length bs"
        using wf(3) k wf_bins_kth_bin wf_item_def x by (metis order_le_less_trans)
      hence wf_bins': "wf_bins \<G> \<omega> ?bs'"
        using wf_bins_Complete\<^sub>L wf(3) wf_bins_upd_bins k x by metis
      hence wf': "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
        using wf(1,2,3) wf_earley_input_intro by fastforce
      have sub: "set (items (?bs' ! k)) \<subseteq> { x | x. wf_item \<G> \<omega> x \<and> end_item x = k }"
        using wf(1,2) wf_bins' unfolding wf_bin_def wf_bins_def wf_bin_items_def using order_le_less_trans by auto
      have "i < length (items (?bs' ! k))"
        using a1 by (metis dual_order.strict_trans1 items_def leI length_map length_nth_upd_bin_bins)
      also have "... = card (set (items (?bs' ! k)))"
        using wf(1,2) wf_bins' distinct_card wf_bins_def wf_bin_def by (metis k length_upd_bins)
      also have "... \<le> card {x |x. wf_item \<G> \<omega> x \<and> end_item x = k}"
        using card_mono fin sub by blast
      finally have "card {x |x. wf_item \<G> \<omega> x \<and> end_item x = k} > i"
        by blast
      hence "earley_measure (k, \<G>, \<omega>, ?bs') (Suc i) < earley_measure (k, \<G>, \<omega>, bs) i"
        by simp
      thus ?thesis
        using 1 a1 a2 complete wf' by simp
    next
      assume a2: "\<not> next_symbol ?x = None"
      then obtain a where a_def: "next_symbol ?x = Some a"
        by blast
      show ?thesis
      proof cases
        assume a3: "a \<notin> nonterminals \<G>"
        show ?thesis
        proof cases
          assume a4: "k < length \<omega>"
          let ?bs' = "upd_bins bs (k+1) (Scan\<^sub>L k \<omega> a ?x i)"
          have wf_bins': "wf_bins \<G> \<omega> ?bs'"
            using wf_bins_Scan\<^sub>L wf(1,3) wf_bins_upd_bins a2 a4 k x by metis
          hence wf': "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
            using wf(1,2,3) wf_earley_input_intro by fastforce
          have sub: "set (items (?bs' ! k)) \<subseteq> { x | x. wf_item \<G> \<omega> x \<and> end_item x = k }"
            using wf(1,2) wf_bins' unfolding wf_bin_def wf_bins_def wf_bin_items_def using order_le_less_trans by auto
          have "i < length (items (?bs' ! k))"
            using a1 by (metis dual_order.strict_trans1 items_def leI length_map length_nth_upd_bin_bins)
          also have "... = card (set (items (?bs' ! k)))"
            using wf(1,2) wf_bins' distinct_card wf_bins_def wf_bin_def
            by (metis Suc_eq_plus1 le_imp_less_Suc length_upd_bins)
          also have "... \<le> card {x |x. wf_item \<G> \<omega> x \<and> end_item x = k}"
            using card_mono fin sub by blast
          finally have "card {x |x. wf_item \<G> \<omega> x \<and> end_item x = k} > i"
            by blast
          hence "earley_measure (k, \<G>, \<omega>, ?bs') (Suc i) < earley_measure (k, \<G>, \<omega>, bs) i"
            by simp
          thus ?thesis
            using 1 a1 a_def a3 a4 scan wf' by simp
        next
          assume a4: "\<not> k < length \<omega>"
          have sub: "set (items (bs ! k)) \<subseteq> { x | x. wf_item \<G> \<omega> x \<and> end_item x = k }"
            using wf unfolding wf_bin_def wf_bins_def wf_bin_items_def using order_le_less_trans by auto
          have "i < length (items (bs ! k))"
            using a1 by simp
          also have "... = card (set (items (bs ! k)))"
            using wf distinct_card wf_bins_def wf_bin_def by (metis Suc_eq_plus1 le_imp_less_Suc)
          also have "... \<le> card {x |x. wf_item \<G> \<omega> x \<and> end_item x = k}"
            using card_mono fin sub by blast
          finally have "card {x |x. wf_item \<G> \<omega> x \<and> end_item x = k} > i"
            by blast
          hence "earley_measure (k, \<G>, \<omega>, bs) (Suc i) < earley_measure (k, \<G>, \<omega>, bs) i"
            by simp
          thus ?thesis
            using 1 a1 a3 a4 a_def pass by simp
        qed
      next
        assume a3: "\<not> a \<notin> nonterminals \<G>"
        let ?bs' = "upd_bins bs k (Predict\<^sub>L k \<G> a)"
        have wf_bins': "wf_bins \<G> \<omega> ?bs'"
          using wf_bins_Predict\<^sub>L wf wf_bins_upd_bins k x by metis
        hence wf': "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
          using wf(1,2,3) wf_earley_input_intro by fastforce
        have sub: "set (items (?bs' ! k)) \<subseteq> { x | x. wf_item \<G> \<omega> x \<and> end_item x = k }"
          using wf(1,2) wf_bins' unfolding wf_bin_def wf_bins_def wf_bin_items_def using order_le_less_trans by auto
        have "i < length (items (?bs' ! k))"
          using a1 by (metis dual_order.strict_trans1 items_def leI length_map length_nth_upd_bin_bins)
        also have "... = card (set (items (?bs' ! k)))"
          using wf(1,2) wf_bins' distinct_card wf_bins_def wf_bin_def
          by (metis Suc_eq_plus1 le_imp_less_Suc length_upd_bins)
        also have "... \<le> card {x |x. wf_item \<G> \<omega> x \<and> end_item x = k}"
          using card_mono fin sub by blast
        finally have "card {x |x. wf_item \<G> \<omega> x \<and> end_item x = k} > i"
          by blast
        hence "earley_measure (k, \<G>, \<omega>, ?bs') (Suc i) < earley_measure (k, \<G>, \<omega>, bs) i"
          by simp
        thus ?thesis
          using 1 a1 a_def a3 a_def predict wf' by simp
      qed
    qed
  qed
qed

lemma wf_earley_input_Earley\<^sub>L_bin':
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  shows "(k, \<G>, \<omega>, Earley\<^sub>L_bin' k \<G> \<omega> bs i) \<in> wf_earley_input"
  using assms
proof (induction i rule: Earley\<^sub>L_bin'_induct[OF assms(1), case_names Base Complete\<^sub>F Scan\<^sub>F Pass Predict\<^sub>F])
  case (Complete\<^sub>F k \<G> \<omega> bs i x)
  let ?bs' = "upd_bins bs k (Complete\<^sub>L k x bs i)"
  have "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Complete\<^sub>F.hyps Complete\<^sub>F.prems wf_earley_input_Complete\<^sub>L by blast
  thus ?case
    using Complete\<^sub>F.IH Complete\<^sub>F.hyps by simp
next
  case (Scan\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs (k+1) (Scan\<^sub>L k \<omega> a x i)"
  have "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Scan\<^sub>F.hyps Scan\<^sub>F.prems wf_earley_input_Scan\<^sub>L by metis
  thus ?case
    using Scan\<^sub>F.IH Scan\<^sub>F.hyps by simp
next
  case (Predict\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs k (Predict\<^sub>L k \<G> a)"
  have "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Predict\<^sub>F.hyps Predict\<^sub>F.prems wf_earley_input_Predict\<^sub>L by metis
  thus ?case
    using Predict\<^sub>F.IH Predict\<^sub>F.hyps by simp
qed simp_all

lemma wf_earley_input_Earley\<^sub>L_bin:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  shows "(k, \<G>, \<omega>, Earley\<^sub>L_bin k \<G> \<omega> bs) \<in> wf_earley_input"
  using assms by (simp add: Earley\<^sub>L_bin_def wf_earley_input_Earley\<^sub>L_bin')

lemma length_bins_Earley\<^sub>L_bin':
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  shows "length (Earley\<^sub>L_bin' k \<G> \<omega> bs i) = length bs"
  by (metis assms wf_earley_input_Earley\<^sub>L_bin' wf_earley_input_elim)

lemma length_nth_bin_Earley\<^sub>L_bin':
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  shows "length (items (Earley\<^sub>L_bin' k \<G> \<omega> bs i ! l)) \<ge> length (items (bs ! l))"
  using length_nth_upd_bin_bins order_trans
  by (induction i rule: Earley\<^sub>L_bin'_induct[OF assms]) (auto simp: items_def, blast+)

lemma wf_bins_Earley\<^sub>L_bin':
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  shows "wf_bins \<G> \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> bs i)"
  using assms wf_earley_input_Earley\<^sub>L_bin' wf_earley_input_elim by blast

lemma wf_bins_Earley\<^sub>L_bin:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  shows "wf_bins \<G> \<omega> (Earley\<^sub>L_bin k \<G> \<omega> bs)"
  using assms Earley\<^sub>L_bin_def wf_bins_Earley\<^sub>L_bin' by metis

lemma kth_Earley\<^sub>L_bin'_bins:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "j < length (items (bs ! l))"
  shows "items (Earley\<^sub>L_bin' k \<G> \<omega> bs i ! l) ! j = items (bs ! l) ! j"
  using assms(2)
proof (induction i rule: Earley\<^sub>L_bin'_induct[OF assms(1), case_names Base Complete\<^sub>F Scan\<^sub>F Pass Predict\<^sub>F])
  case (Complete\<^sub>F k \<G> \<omega> bs i x)
  let ?bs' = "upd_bins bs k (Complete\<^sub>L k x bs i)"
  have "items (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i + 1) ! l) ! j = items (?bs' ! l) ! j"
    using Complete\<^sub>F.IH Complete\<^sub>F.prems length_nth_upd_bin_bins items_def order.strict_trans2 by (metis length_map)
  also have "... = items (bs ! l) ! j"
    using Complete\<^sub>F.prems items_nth_idem_upd_bins nth_idem_upd_bins length_map items_def by metis
  finally show ?case
    using Complete\<^sub>F.hyps by simp
next
  case (Scan\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs (k+1) (Scan\<^sub>L k \<omega> a x i)"
  have "items (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i + 1) ! l) ! j = items (?bs' ! l) ! j"
    using Scan\<^sub>F.IH Scan\<^sub>F.prems length_nth_upd_bin_bins order.strict_trans2 items_def by (metis length_map)
  also have "... = items (bs ! l) ! j"
    using Scan\<^sub>F.prems items_nth_idem_upd_bins nth_idem_upd_bins length_map items_def by metis
  finally show ?case
    using Scan\<^sub>F.hyps by simp
next
  case (Predict\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs k (Predict\<^sub>L k \<G> a)"
  have "items (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i + 1) ! l) ! j = items (?bs' ! l) ! j"
    using Predict\<^sub>F.IH Predict\<^sub>F.prems length_nth_upd_bin_bins order.strict_trans2 items_def by (metis length_map)
  also have "... = items (bs ! l) ! j"
    using Predict\<^sub>F.prems items_nth_idem_upd_bins nth_idem_upd_bins length_map items_def by metis
  finally show ?case
    using Predict\<^sub>F.hyps by simp
qed simp_all

lemma nth_bin_sub_Earley\<^sub>L_bin':
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  shows "set (items (bs ! l)) \<subseteq> set (items (Earley\<^sub>L_bin' k \<G> \<omega> bs i ! l))"
proof standard
  fix x
  assume "x \<in> set (items (bs ! l))"
  then obtain j where *: "j < length (items (bs ! l))" "items (bs ! l) ! j = x"
    using in_set_conv_nth by metis
  have "x = items (Earley\<^sub>L_bin' k \<G> \<omega> bs i ! l) ! j"
    using kth_Earley\<^sub>L_bin'_bins assms * by metis
  moreover have "j < length (items (Earley\<^sub>L_bin' k \<G> \<omega> bs i ! l))"
    using assms *(1) length_nth_bin_Earley\<^sub>L_bin' less_le_trans by blast
  ultimately show "x \<in> set (items (Earley\<^sub>L_bin' k \<G> \<omega> bs i ! l))"
    by simp
qed

lemma nth_Earley\<^sub>L_bin'_eq:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  shows "l < k \<Longrightarrow> Earley\<^sub>L_bin' k \<G> \<omega> bs i ! l = bs ! l"
  by (induction i rule: Earley\<^sub>L_bin'_induct[OF assms]) (auto simp: upd_bins_def)

lemma set_items_Earley\<^sub>L_bin'_eq:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  shows "l < k \<Longrightarrow> set (items (Earley\<^sub>L_bin' k \<G> \<omega> bs i ! l)) = set (items (bs ! l))"
  by (simp add: assms nth_Earley\<^sub>L_bin'_eq)

lemma bins_upto_k0_Earley\<^sub>L_bin'_eq:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  shows "bins_upto (Earley\<^sub>L_bin k \<G> \<omega> bs) k 0 = bins_upto bs k 0"
  unfolding bins_upto_def bin_upto_def Earley\<^sub>L_bin_def using set_items_Earley\<^sub>L_bin'_eq assms nth_Earley\<^sub>L_bin'_eq by fastforce

lemma wf_earley_input_Init\<^sub>L:
  assumes "k \<le> length \<omega>"
  shows "(k, \<G>, \<omega>, Init\<^sub>L \<G> \<omega>) \<in> wf_earley_input"
proof -
  let ?rs = "filter (\<lambda>r. lhs_rule r = \<SS> \<G>) (remdups (\<RR> \<G>))"
  let ?b0 = "map (\<lambda>r. (init_item r 0, Null)) ?rs"
  let ?bs = "replicate (length \<omega> + 1) ([])"
  have "distinct (items ?b0)"
    using assms unfolding wf_bin_def wf_item_def items_def
    by (auto simp: init_item_def distinct_map inj_on_def)
  moreover have "\<forall>x \<in> set (items ?b0). wf_item \<G> \<omega> x \<and> end_item x = 0"
    using assms unfolding wf_bin_def wf_item_def by (auto simp: init_item_def items_def)
  moreover have "wf_bins \<G> \<omega> ?bs"
    unfolding wf_bins_def wf_bin_def wf_bin_items_def items_def using less_Suc_eq_0_disj by force
  ultimately show ?thesis
    using assms length_replicate wf_earley_input_intro
    unfolding wf_bin_def Init\<^sub>L_def wf_bin_def wf_bin_items_def wf_bins_def
    by (metis (no_types, lifting) length_list_update nth_list_update_eq nth_list_update_neq)
qed

lemma length_bins_Init\<^sub>L[simp]:
  "length (Init\<^sub>L \<G> \<omega>) = length \<omega> + 1"
  by (simp add: Init\<^sub>L_def)

lemma wf_earley_input_Earley\<^sub>L_bins[simp]:
  assumes "k \<le> length \<omega>"
  shows "(k, \<G>, \<omega>, Earley\<^sub>L_bins k \<G> \<omega>) \<in> wf_earley_input"
  using assms
proof (induction k)
  case 0
  have "(k, \<G>, \<omega>, Init\<^sub>L \<G> \<omega>) \<in> wf_earley_input"
    using assms wf_earley_input_Init\<^sub>L by blast
  thus ?case
    by (simp add: assms wf_earley_input_Init\<^sub>L wf_earley_input_Earley\<^sub>L_bin)
next
  case (Suc k)
  have "(Suc k, \<G>, \<omega>, Earley\<^sub>L_bins k \<G> \<omega>) \<in> wf_earley_input"
    using Suc.IH Suc.prems(1) Suc_leD assms wf_earley_input_elim wf_earley_input_intro by metis
  thus ?case
    by (simp add: wf_earley_input_Earley\<^sub>L_bin)
qed

lemma length_Earley\<^sub>L_bins[simp]:
  assumes "k \<le> length \<omega>"
  shows "length (Earley\<^sub>L_bins k \<G> \<omega>) = length (Init\<^sub>L \<G> \<omega>)"
  using assms wf_earley_input_Earley\<^sub>L_bins wf_earley_input_elim by fastforce

lemma wf_bins_Earley\<^sub>L_bins[simp]:
  assumes "k \<le> length \<omega>"
  shows "wf_bins \<G> \<omega> (Earley\<^sub>L_bins k \<G> \<omega>)"
  using assms wf_earley_input_Earley\<^sub>L_bins wf_earley_input_elim by fastforce

lemma wf_bins_Earley\<^sub>L:
  "wf_bins \<G> \<omega> (Earley\<^sub>L \<G> \<omega>)"
  by (simp add: Earley\<^sub>L_def)


subsection \<open>Soundness\<close>

lemma Init\<^sub>L_eq_Init\<^sub>F:
  "bins (Init\<^sub>L \<G> \<omega>) = Init\<^sub>F \<G>"
proof -
  let ?rs = "filter (\<lambda>r. lhs_rule r = \<SS> \<G>) (remdups (\<RR> \<G>))"
  let ?b0 = "map (\<lambda>r. (init_item r 0, Null)) ?rs"
  let ?bs = "replicate (length \<omega> + 1) ([])"
  have "bins (?bs[0 := ?b0]) = set (items ?b0)"
  proof -
    have "bins (?bs[0 := ?b0]) = \<Union> {set (items ((?bs[0 := ?b0]) ! k)) |k. k < length (?bs[0 := ?b0])}"
      unfolding bins_def by blast
    also have "... = set (items ((?bs[0 := ?b0]) ! 0)) \<union> \<Union> {set (items ((?bs[0 := ?b0]) ! k)) |k. k < length (?bs[0 := ?b0]) \<and> k \<noteq> 0}"
      by fastforce
    also have "... = set (items (?b0))"
      by (auto simp: items_def)
    finally show ?thesis .
  qed
  also have "... = Init\<^sub>F \<G>"
    by (auto simp: Init\<^sub>F_def items_def lhs_rule_def)
  finally show ?thesis
    by (auto simp: Init\<^sub>L_def)
qed

lemma Scan\<^sub>L_sub_Scan\<^sub>F:
  assumes "wf_bins \<G> \<omega> bs" "bins bs \<subseteq> I" "x \<in> set (items (bs ! k))" "k < length bs" "k < length \<omega>"
  assumes "next_symbol x = Some a"
  shows "set (items (Scan\<^sub>L k \<omega> a x pre)) \<subseteq> Scan\<^sub>F k \<omega> I"
proof standard
  fix y
  assume *: "y \<in> set (items (Scan\<^sub>L k \<omega> a x pre))"
  have "x \<in> bin I k"
    using kth_bin_sub_bins assms(1-4) items_def wf_bin_def wf_bins_def wf_bin_items_def bin_def by fastforce
  {
    assume #: "k < length \<omega>" "\<omega>!k = a"
    hence "y = inc_item x (k+1)"
      using * unfolding Scan\<^sub>L_def by (simp add: items_def)
    hence "y \<in> Scan\<^sub>F k \<omega> I"
      using \<open>x \<in> bin I k\<close> # assms(6) unfolding Scan\<^sub>F_def by blast
  }
  thus "y \<in> Scan\<^sub>F k \<omega> I"
    using * assms(5) unfolding Scan\<^sub>L_def by (auto simp: items_def)
qed

lemma Predict\<^sub>L_sub_Predict\<^sub>F:
  assumes "wf_bins \<G> \<omega> bs" "bins bs \<subseteq> I" "x \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol x = Some X"
  shows "set (items (Predict\<^sub>L k \<G> X)) \<subseteq> Predict\<^sub>F k \<G> I"
proof standard
  fix y
  assume *: "y \<in> set (items (Predict\<^sub>L k \<G> X))"
  have "x \<in> bin I k"
    using kth_bin_sub_bins assms(1-4) items_def wf_bin_def wf_bins_def bin_def wf_bin_items_def by fast
  let ?rs = "filter (\<lambda>r. lhs_rule r = X) (\<RR> \<G>)"
  let ?xs = "map (\<lambda>r. init_item r k) ?rs"
  have "y \<in> set ?xs"
    using * unfolding Predict\<^sub>L_def items_def by simp
  then obtain r where "y = init_item r k" "lhs_rule r = X" "r \<in> set (\<RR> \<G>)" "next_symbol x = Some (lhs_rule r)"
    using assms(5) by auto
  thus "y \<in> Predict\<^sub>F k \<G> I"
    unfolding Predict\<^sub>F_def using \<open>x \<in> bin I k\<close> by blast
qed

lemma Complete\<^sub>L_sub_Complete\<^sub>F:
  assumes "wf_bins \<G> \<omega> bs" "bins bs \<subseteq> I" "y \<in> set (items (bs ! k))" "k < length bs"
  assumes "next_symbol y = None"
  shows "set (items (Complete\<^sub>L k y bs red)) \<subseteq> Complete\<^sub>F k I"
proof standard
  fix x
  assume *: "x \<in> set (items (Complete\<^sub>L k y bs red))"
  have "y \<in> bin I k"
    using kth_bin_sub_bins assms items_def wf_bin_def wf_bins_def bin_def wf_bin_items_def by fast
  let ?orig = "bs ! start_item y"
  let ?xs = "filter_with_index (\<lambda>x. next_symbol x = Some (lhs_item y)) (items ?orig)"
  let ?xs' = "map (\<lambda>(x, pre). (inc_item x k, PreRed (start_item y, pre, red) [])) ?xs"
  have 0: "start_item y < length bs"
    using wf_bins_def wf_bin_def wf_item_def wf_bin_items_def assms(1,3,4)
    by (metis Orderings.preorder_class.dual_order.strict_trans1 leD not_le_imp_less)
  {
    fix z
    assume *: "z \<in> set (map fst ?xs)"
    have "next_symbol z = Some (lhs_item y)"
      using * by (simp add: filter_with_index_cong_filter)
    moreover have "z \<in> bin I (start_item y)"
      using 0 * assms(1,2) bin_def kth_bin_sub_bins wf_bins_kth_bin filter_with_index_cong_filter
      by (metis (mono_tags, lifting) filter_is_subset in_mono mem_Collect_eq)
    ultimately have "next_symbol z = Some (lhs_item y)" "z \<in> bin I (start_item y)"
      by simp_all
  }
  hence 1: "\<forall>z \<in> set (map fst ?xs). next_symbol z = Some (lhs_item y) \<and> z \<in> bin I (start_item y)"
    by blast
  obtain z where z: "x = inc_item z k" "z \<in> set (map fst ?xs)"
    using * unfolding Complete\<^sub>L_def by (auto simp: rev_image_eqI items_def)
  moreover have "next_symbol z = Some (lhs_item y)" "z \<in> bin I (start_item y)"
    using 1 z by blast+
  ultimately show "x \<in> Complete\<^sub>F k I"
    using \<open>y \<in> bin I k\<close> assms(5) unfolding Complete\<^sub>F_def next_symbol_def by (auto split: if_splits)
qed

lemma sound_Scan\<^sub>L:
  assumes "wf_bins \<G> \<omega> bs" "bins bs \<subseteq> I" "x \<in> set (items (bs!k))" "k < length bs" "k < length \<omega>"
  assumes "next_symbol x = Some a" "\<forall>x \<in> I. wf_item \<G> \<omega> x" "\<forall>x \<in> I. sound_item \<G> \<omega> x"
  shows "\<forall>x \<in> set (items (Scan\<^sub>L k \<omega> a x i)). sound_item \<G> \<omega> x"
proof standard
  fix y
  assume "y \<in> set (items (Scan\<^sub>L k \<omega> a x i))"
  hence "y \<in> Scan\<^sub>F k \<omega> I"
    by (meson Scan\<^sub>L_sub_Scan\<^sub>F assms(1-6) in_mono)
  thus "sound_item \<G> \<omega> y"
    using sound_Scan assms(7,8) unfolding Scan\<^sub>F_def inc_item_def bin_def
    by (smt (verit, best) item.exhaust_sel mem_Collect_eq)
qed

lemma sound_Predict\<^sub>L:
  assumes "wf_bins \<G> \<omega> bs" "bins bs \<subseteq> I" "x \<in> set (items (bs!k))" "k < length bs"
  assumes "next_symbol x = Some X" "\<forall>x \<in> I. wf_item \<G> \<omega> x" "\<forall>x \<in> I. sound_item \<G> \<omega> x"
  shows "\<forall>x \<in> set (items (Predict\<^sub>L k \<G> X)). sound_item \<G> \<omega> x"
proof standard
  fix y
  assume "y \<in> set (items (Predict\<^sub>L k \<G> X))"
  hence "y \<in> Predict\<^sub>F k \<G> I"
    by (meson Predict\<^sub>L_sub_Predict\<^sub>F assms(1-5) subsetD)
  thus "sound_item \<G> \<omega> y"
    using sound_Predict assms(6,7) unfolding Predict\<^sub>F_def init_item_def bin_def
    by (smt (verit, del_insts) item.exhaust_sel mem_Collect_eq)
qed

lemma sound_Complete\<^sub>L:
  assumes "wf_bins \<G> \<omega> bs" "bins bs \<subseteq> I" "y \<in> set (items (bs!k))" "k < length bs"
  assumes "next_symbol y = None" "\<forall>x \<in> I. wf_item \<G> \<omega> x" "\<forall>x \<in> I. sound_item \<G> \<omega> x"
  shows "\<forall>x \<in> set (items (Complete\<^sub>L k y bs i)). sound_item \<G> \<omega> x"
proof standard
  fix x
  assume "x \<in> set (items (Complete\<^sub>L k y bs i))"
  hence "x \<in> Complete\<^sub>F k I"
    using Complete\<^sub>L_sub_Complete\<^sub>F assms(1-5) by blast
  thus "sound_item \<G> \<omega> x"
    using sound_Complete assms(6,7) unfolding Complete\<^sub>F_def inc_item_def bin_def
    by (smt (verit, del_insts) item.exhaust_sel mem_Collect_eq)
qed

lemma sound_Earley\<^sub>L_bin':
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "\<forall>x \<in> bins bs. sound_item \<G> \<omega> x"
  shows "\<forall>x \<in> bins (Earley\<^sub>L_bin' k \<G> \<omega> bs i). sound_item \<G> \<omega> x"
  using assms
proof (induction i rule: Earley\<^sub>L_bin'_induct[OF assms(1), case_names Base Complete\<^sub>F Scan\<^sub>F Pass Predict\<^sub>F])
  case (Complete\<^sub>F k \<G> \<omega> bs i x)
  let ?bs' = "upd_bins bs k (Complete\<^sub>L k x bs i)"
  have "x \<in> set (items (bs ! k))"
    using Complete\<^sub>F.hyps(1,2) by force
  hence "\<forall>x \<in> set (items (Complete\<^sub>L k x bs i)). sound_item \<G> \<omega> x"
    using sound_Complete\<^sub>L Complete\<^sub>F.hyps(3) Complete\<^sub>F.prems wf_earley_input_elim wf_bins_impl_wf_items by fastforce
  moreover have "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Complete\<^sub>F.hyps Complete\<^sub>F.prems(1) wf_earley_input_Complete\<^sub>L by blast
  ultimately have "\<forall>x \<in> bins (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i + 1)). sound_item \<G> \<omega> x"
    using Complete\<^sub>F.IH Complete\<^sub>F.prems(2) length_upd_bins bins_upd_bins wf_earley_input_elim
      Suc_eq_plus1 Un_iff le_imp_less_Suc by metis
  thus ?case
    using Complete\<^sub>F.hyps by simp
next
  case (Scan\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs (k+1) (Scan\<^sub>L k \<omega> a x i)"
  have "x \<in> set (items (bs ! k))"
    using Scan\<^sub>F.hyps(1,2) by force
  hence "\<forall>x \<in> set (items (Scan\<^sub>L k \<omega> a x i)). sound_item \<G> \<omega> x"
    using sound_Scan\<^sub>L Scan\<^sub>F.hyps(3,5) Scan\<^sub>F.prems(1,2) wf_earley_input_elim wf_bins_impl_wf_items by fast
  moreover have "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Scan\<^sub>F.hyps Scan\<^sub>F.prems(1) wf_earley_input_Scan\<^sub>L by metis
  ultimately have "\<forall>x \<in> bins (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i + 1)). sound_item \<G> \<omega> x"
    using Scan\<^sub>F.IH Scan\<^sub>F.hyps(5) Scan\<^sub>F.prems(2) length_upd_bins bins_upd_bins wf_earley_input_elim
    by (metis UnE add_less_cancel_right)
  thus ?case
    using Scan\<^sub>F.hyps by simp
next
  case (Predict\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs k (Predict\<^sub>L k \<G> a)"
  have "x \<in> set (items (bs ! k))"
    using Predict\<^sub>F.hyps(1,2) by force
  hence "\<forall>x \<in> set (items(Predict\<^sub>L k \<G> a)). sound_item \<G> \<omega> x"
    using sound_Predict\<^sub>L Predict\<^sub>F.hyps(3) Predict\<^sub>F.prems wf_earley_input_elim wf_bins_impl_wf_items by fast
  moreover have "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Predict\<^sub>F.hyps Predict\<^sub>F.prems(1) wf_earley_input_Predict\<^sub>L by metis
  ultimately have "\<forall>x \<in> bins (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i + 1)). sound_item \<G> \<omega> x"
    using Predict\<^sub>F.IH Predict\<^sub>F.prems(2) length_upd_bins bins_upd_bins wf_earley_input_elim
    by (metis Suc_eq_plus1 UnE)
  thus ?case
    using Predict\<^sub>F.hyps by simp
qed simp_all

lemma sound_Earley\<^sub>L_bin:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "\<forall>x \<in> bins bs. sound_item \<G> \<omega> x"
  shows "\<forall>x \<in> bins (Earley\<^sub>L_bin k \<G> \<omega> bs). sound_item \<G> \<omega> x"
  using sound_Earley\<^sub>L_bin' assms Earley\<^sub>L_bin_def by metis

lemma Earley\<^sub>L_bin'_sub_Earley\<^sub>F_bin:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "bins bs \<subseteq> I"
  shows "bins (Earley\<^sub>L_bin' k \<G> \<omega> bs i) \<subseteq> Earley\<^sub>F_bin k \<G> \<omega> I"
  using assms
proof (induction i arbitrary: I rule: Earley\<^sub>L_bin'_induct[OF assms(1), case_names Base Complete\<^sub>F Scan\<^sub>F Pass Predict\<^sub>F])
  case (Base k \<G> \<omega> bs i)
  thus ?case
    using Earley\<^sub>F_bin_mono by fastforce
next
  case (Complete\<^sub>F k \<G> \<omega> bs i x)
  let ?bs' = "upd_bins bs k (Complete\<^sub>L k x bs i)"
  have "x \<in> set (items (bs ! k))"
    using Complete\<^sub>F.hyps(1,2) by force
  hence "bins ?bs' \<subseteq> I \<union> Complete\<^sub>F k I"
    using Complete\<^sub>L_sub_Complete\<^sub>F Complete\<^sub>F.hyps(3) Complete\<^sub>F.prems(1,2) bins_upd_bins wf_earley_input_elim by blast
  moreover have "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Complete\<^sub>F.hyps Complete\<^sub>F.prems(1) wf_earley_input_Complete\<^sub>L by blast
  ultimately have "bins (Earley\<^sub>L_bin' k \<G> \<omega> bs i) \<subseteq> Earley\<^sub>F_bin k \<G> \<omega> (I \<union> Complete\<^sub>F k I)"
    using Complete\<^sub>F.IH Complete\<^sub>F.hyps by simp
  also have "... \<subseteq> Earley\<^sub>F_bin k \<G> \<omega> (Earley\<^sub>F_bin k \<G> \<omega> I)"
    using Complete\<^sub>F_Earley\<^sub>F_bin_mono Earley\<^sub>F_bin_mono Earley\<^sub>F_bin_sub_mono by (metis Un_subset_iff)
  finally show ?case
    using Earley\<^sub>F_bin_idem by blast
next
  case (Scan\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs (k+1) (Scan\<^sub>L k \<omega> a x i)"
  have "x \<in> set (items (bs ! k))"
    using Scan\<^sub>F.hyps(1,2) by force
  hence "bins ?bs' \<subseteq> I \<union> Scan\<^sub>F k \<omega> I"
    using Scan\<^sub>L_sub_Scan\<^sub>F Scan\<^sub>F.hyps(3,5) Scan\<^sub>F.prems bins_upd_bins wf_earley_input_elim
    by (metis add_mono1 sup_mono)
  moreover have "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Scan\<^sub>F.hyps Scan\<^sub>F.prems(1) wf_earley_input_Scan\<^sub>L by metis
  ultimately have "bins (Earley\<^sub>L_bin' k \<G> \<omega> bs i) \<subseteq> Earley\<^sub>F_bin k \<G> \<omega> (I \<union> Scan\<^sub>F k \<omega> I)"
    using Scan\<^sub>F.IH Scan\<^sub>F.hyps by simp
  thus ?case
    using Scan\<^sub>F_Earley\<^sub>F_bin_mono Earley\<^sub>F_bin_mono Earley\<^sub>F_bin_sub_mono Earley\<^sub>F_bin_idem
    by (metis Un_subset_iff subset_trans)
next
  case (Pass k \<G> \<omega> bs i x a)
  thus ?case
    by simp
next
  case (Predict\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs k (Predict\<^sub>L k \<G> a)"
  have "x \<in> set (items (bs ! k))"
    using Predict\<^sub>F.hyps(1,2) by force
  hence "bins ?bs' \<subseteq> I \<union> Predict\<^sub>F k \<G> I"
    using Predict\<^sub>L_sub_Predict\<^sub>F Predict\<^sub>F.hyps(3) Predict\<^sub>F.prems bins_upd_bins wf_earley_input_elim
    by (metis sup_mono)
  moreover have "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Predict\<^sub>F.hyps Predict\<^sub>F.prems(1) wf_earley_input_Predict\<^sub>L by metis
  ultimately have "bins (Earley\<^sub>L_bin' k \<G> \<omega> bs i)  \<subseteq> Earley\<^sub>F_bin k \<G> \<omega> (I \<union> Predict\<^sub>F k \<G> I)"
    using Predict\<^sub>F.IH Predict\<^sub>F.hyps by simp
  thus ?case
    using Predict\<^sub>F_Earley\<^sub>F_bin_mono Earley\<^sub>F_bin_mono Earley\<^sub>F_bin_sub_mono Earley\<^sub>F_bin_idem
    by (metis Un_subset_iff subset_trans)
qed

lemma Earley\<^sub>L_bin_sub_Earley\<^sub>F_bin:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "bins bs \<subseteq> I"
  shows "bins (Earley\<^sub>L_bin k \<G> \<omega> bs) \<subseteq> Earley\<^sub>F_bin k \<G> \<omega> I"
  using assms Earley\<^sub>L_bin'_sub_Earley\<^sub>F_bin Earley\<^sub>L_bin_def by metis

lemma Earley\<^sub>L_bins_sub_Earley\<^sub>F_bins:
  assumes "k \<le> length \<omega>"
  shows "bins (Earley\<^sub>L_bins k \<G> \<omega>) \<subseteq> Earley\<^sub>F_bins k \<G> \<omega>"
  using assms
proof (induction k)
  case 0
  have "(k, \<G>, \<omega>, Init\<^sub>L \<G> \<omega>) \<in> wf_earley_input"
    using assms(1) assms wf_earley_input_Init\<^sub>L by blast
  thus ?case
    by (simp add: Init\<^sub>L_eq_Init\<^sub>F Earley\<^sub>L_bin_sub_Earley\<^sub>F_bin assms wf_earley_input_Init\<^sub>L)
next
  case (Suc k)
  have "(Suc k, \<G>, \<omega>, Earley\<^sub>L_bins k \<G> \<omega>) \<in> wf_earley_input"
    by (simp add: Suc.prems(1) Suc_leD assms wf_earley_input_intro)
  thus ?case
    by (simp add: Suc.IH Suc.prems(1) Suc_leD Earley\<^sub>L_bin_sub_Earley\<^sub>F_bin assms)
qed

lemma Earley\<^sub>L_sub_Earley\<^sub>F:
  "bins (Earley\<^sub>L \<G> \<omega>) \<subseteq> Earley\<^sub>F \<G> \<omega>"
  using Earley\<^sub>L_bins_sub_Earley\<^sub>F_bins Earley\<^sub>F_def Earley\<^sub>L_def by (metis dual_order.refl)

theorem soundness_Earley\<^sub>L:
  assumes "recognizing (bins (Earley\<^sub>L \<G> \<omega>)) \<G> \<omega>"
  shows "\<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>"
  using assms Earley\<^sub>L_sub_Earley\<^sub>F recognizing_def soundness_Earley\<^sub>F by (meson subsetD)


subsection \<open>Completeness\<close>

lemma bin_bins_upto_bins_eq:
  assumes "wf_bins \<G> \<omega> bs" "k < length bs" "i \<ge> length (items (bs ! k))" "l \<le> k"
  shows "bin (bins_upto bs k i) l = bin (bins bs) l"
  unfolding bins_upto_def bins_def bin_def using assms nat_less_le
  apply (auto simp: nth_list_update bin_upto_eq_set_items wf_bins_kth_bin items_def)
      apply (metis fst_conv image_eqI order.strict_trans2)
  by (metis fst_conv image_eqI items_def list.set_map wf_bins_kth_bin)

lemma impossible_complete_item:
  assumes "sound_item \<G> \<omega> x" "is_complete x"  "start_item x = k" "end_item x = k" "nonempty_derives \<G>"
  shows False
proof -
  have "\<G> \<turnstile> [lhs_item x] \<Rightarrow>\<^sup>* []"
    using assms(1-4) by (simp add: slice_empty is_complete_def sound_item_def \<beta>_item_def)
  thus ?thesis
    by (meson assms(5) nonempty_derives_def)
qed

lemma Complete\<^sub>F_Un_eq_terminal:
  assumes "next_symbol z = Some a" "a \<notin> nonterminals \<G>" "\<forall>x \<in> I. wf_item \<G> \<omega> x" "wf_item \<G> \<omega> z"
  shows "Complete\<^sub>F k (I \<union> {z}) = Complete\<^sub>F k I"
proof (rule ccontr)
  assume "Complete\<^sub>F k (I \<union> {z}) \<noteq> Complete\<^sub>F k I"
  hence "Complete\<^sub>F k I \<subset> Complete\<^sub>F k (I \<union> {z})"
    using Complete\<^sub>F_sub_mono by blast
  then obtain w x y  where *:
    "w \<in> Complete\<^sub>F k (I \<union> {z})" "w \<notin> Complete\<^sub>F k I" "w = inc_item x k"
    "x \<in> bin (I \<union> {z}) (start_item y)" "y \<in> bin (I \<union> {z}) k"
    "is_complete y" "next_symbol x = Some (lhs_item y)"
    unfolding Complete\<^sub>F_def by fast
  show False
  proof (cases "x = z")
    case True
    have "lhs_item y \<in> nonterminals \<G>"
      using *(5,6) assms
      by (auto simp: wf_item_def bin_def lhs_item_def lhs_rule_def next_symbol_def nonterminals_def)
    thus ?thesis
      using True *(7) assms by simp
  next
    case False
    thus ?thesis
      using * assms(1) by (auto simp: next_symbol_def Complete\<^sub>F_def bin_def)
  qed
qed

lemma Complete\<^sub>F_Un_eq_nonterminal:
  assumes "\<forall>x \<in> I. wf_item \<G> \<omega> x" "\<forall>x \<in> I. sound_item \<G> \<omega> x"
  assumes "nonempty_derives \<G>" "wf_item \<G> \<omega> z"
  assumes "end_item z = k" "next_symbol z \<noteq> None"
  shows "Complete\<^sub>F k (I \<union> {z}) = Complete\<^sub>F k I"
proof (rule ccontr)
  assume "Complete\<^sub>F k (I \<union> {z}) \<noteq> Complete\<^sub>F k I"
  hence "Complete\<^sub>F k I \<subset> Complete\<^sub>F k (I \<union> {z})"
    using Complete\<^sub>F_sub_mono by blast
  then obtain x x' y where *:
    "x \<in> Complete\<^sub>F k (I \<union> {z})" "x \<notin> Complete\<^sub>F k I" "x = inc_item x' k"
    "x' \<in> bin (I \<union> {z}) (start_item y)" "y \<in> bin (I \<union> {z}) k"
    "is_complete y" "next_symbol x' = Some (lhs_item y)"
    unfolding Complete\<^sub>F_def by fast
  consider (A) "x' = z" | (B) "y = z"
    using *(2-7) Complete\<^sub>F_def by (auto simp: bin_def; blast)
  thus False
  proof cases
    case A
    have "start_item y = k"
      using *(4) A bin_def assms(5) by (metis (mono_tags, lifting) mem_Collect_eq)
    moreover have "end_item y = k"
      using *(5) bin_def by blast
    moreover have "sound_item \<G> \<omega> y"
      using *(5,6) assms(2,6) by (auto simp: bin_def next_symbol_def sound_item_def)
    moreover have "wf_item \<G> \<omega> y"
      using *(5) assms(1,4) wf_item_def by (auto simp: bin_def)
    ultimately show ?thesis
      using impossible_complete_item *(6) assms(3) by blast
  next
    case B
    thus ?thesis
      using *(6) assms(6) by (auto simp: next_symbol_def)
  qed
qed

lemma wf_item_in_kth_bin:
  "wf_bins \<G> \<omega> bs \<Longrightarrow> x \<in> bins bs \<Longrightarrow> end_item x = k \<Longrightarrow> x \<in> set (items (bs ! k))"
  using bins_bin_exists wf_bins_kth_bin wf_bins_def by blast

lemma Complete\<^sub>F_bins_upto_eq_bins:
  assumes "wf_bins \<G> \<omega> bs" "k < length bs" "i \<ge> length (items (bs ! k))"
  shows "Complete\<^sub>F k (bins_upto bs k i) = Complete\<^sub>F k (bins bs)"
proof -
  have "\<And>l. l \<le> k \<Longrightarrow> bin (bins_upto bs k i) l = bin (bins bs) l"
    using bin_bins_upto_bins_eq[OF assms] by blast
  moreover have "\<forall>x \<in> bins bs. wf_item \<G> \<omega> x"
    using assms(1) wf_bins_impl_wf_items by metis
  ultimately show ?thesis
    unfolding Complete\<^sub>F_def bin_def wf_item_def wf_item_def by auto
qed

lemma Complete\<^sub>F_sub_bins_Un_Complete\<^sub>L:
  assumes "Complete\<^sub>F k I \<subseteq> bins bs" "I \<subseteq> bins bs" "is_complete z" "wf_bins \<G> \<omega> bs" "wf_item \<G> \<omega> z"
  shows "Complete\<^sub>F k (I \<union> {z}) \<subseteq> bins bs \<union> set (items (Complete\<^sub>L k z bs red))"
proof standard
  fix w
  assume "w \<in> Complete\<^sub>F k (I \<union> {z})"
  then obtain x y where *:
    "w = inc_item x k" "x \<in> bin (I \<union> {z}) (start_item y)" "y \<in> bin (I \<union> {z}) k"
    "is_complete y" "next_symbol x = Some (lhs_item y)"
    unfolding Complete\<^sub>F_def by blast
  consider (A) "x = z" | (B) "y = z" | "\<not> (x = z \<or> y = z)"
    by blast
  thus "w \<in> bins bs \<union> set (items (Complete\<^sub>L k z bs red))"
  proof cases
    case A
    thus ?thesis
      using *(5) assms(3) by (auto simp: next_symbol_def)
  next
    case B
    let ?orig = "bs ! start_item z"
    let ?is = "filter_with_index (\<lambda>x. next_symbol x = Some (lhs_item z)) (items ?orig)"
    have "x \<in> bin I (start_item y)"
      using B *(2) *(5) assms(3) by (auto simp: next_symbol_def bin_def)
    moreover have "bin I (start_item z) \<subseteq> set (items (bs ! start_item z))"
      using wf_item_in_kth_bin assms(2,4) bin_def by blast
    ultimately have "x \<in> set (map fst ?is)"
      using *(5) B by (simp add: filter_with_index_cong_filter in_mono)
    thus ?thesis
      unfolding Complete\<^sub>L_def *(1) by (auto simp: rev_image_eqI items_def)
  next
    case 3
    thus ?thesis
      using * assms(1) Complete\<^sub>F_def by (auto simp: bin_def; blast)
  qed
qed

lemma Complete\<^sub>L_eq_start_item:
  "bs ! start_item y = bs' ! start_item y \<Longrightarrow> Complete\<^sub>L k y bs red = Complete\<^sub>L k y bs' red"
  by (auto simp: Complete\<^sub>L_def)

lemma kth_bin_bins_upto_empty:
  assumes "wf_bins \<G> \<omega> bs" "k < length bs"
  shows "bin (bins_upto bs k 0) k = {}"
proof -
  {
    fix x
    assume "x \<in> bins_upto bs k 0"
    then obtain l where "x \<in> set (items (bs ! l))" "l < k"
      unfolding bins_upto_def bin_upto_def by blast
    hence "end_item x = l"
      using wf_bins_kth_bin assms by fastforce
    hence "end_item x < k"
      using \<open>l < k\<close> by blast
  }
  thus ?thesis
    by (auto simp: bin_def)
qed

lemma Earley\<^sub>L_bin'_mono:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  shows "bins bs \<subseteq> bins (Earley\<^sub>L_bin' k \<G> \<omega> bs i)"
  using assms
proof (induction i rule: Earley\<^sub>L_bin'_induct[OF assms(1), case_names Base Complete\<^sub>F Scan\<^sub>F Pass Predict\<^sub>F])
  case (Complete\<^sub>F k \<G> \<omega> bs i x)
  let ?bs' = "upd_bins bs k (Complete\<^sub>L k x bs i)"
  have wf: "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Complete\<^sub>F.hyps Complete\<^sub>F.prems(1) wf_earley_input_Complete\<^sub>L by blast
  hence "bins bs \<subseteq> bins ?bs'"
    using length_upd_bins bins_upd_bins wf_earley_input_elim by (metis Un_upper1)
  also have "... \<subseteq> bins (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i + 1))"
    using wf Complete\<^sub>F.IH by blast
  finally show ?case
    using Complete\<^sub>F.hyps by simp
next
  case (Scan\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs (k+1) (Scan\<^sub>L k \<omega> a x i)"
  have wf: "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Scan\<^sub>F.hyps Scan\<^sub>F.prems(1) wf_earley_input_Scan\<^sub>L by metis
  hence "bins bs \<subseteq> bins ?bs'"
    using Scan\<^sub>F.hyps(5) length_upd_bins bins_upd_bins wf_earley_input_elim
    by (metis add_mono1 sup_ge1)
  also have "... \<subseteq> bins (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i + 1))"
    using wf Scan\<^sub>F.IH by blast
  finally show ?case
    using Scan\<^sub>F.hyps by simp
next
  case (Predict\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs k (Predict\<^sub>L k \<G> a)"
  have wf: "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Predict\<^sub>F.hyps Predict\<^sub>F.prems(1) wf_earley_input_Predict\<^sub>L by metis
  hence "bins bs \<subseteq> bins ?bs'"
    using length_upd_bins bins_upd_bins wf_earley_input_elim by (metis sup_ge1)
  also have "... \<subseteq> bins (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i + 1))"
    using wf Predict\<^sub>F.IH by blast
  finally show ?case
    using Predict\<^sub>F.hyps by simp
qed simp_all

lemma Earley\<^sub>F_bin_step_sub_Earley\<^sub>L_bin':
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "Earley\<^sub>F_bin_step k \<G> \<omega> (bins_upto bs k i) \<subseteq> bins bs"
  assumes "\<forall>x \<in> bins bs. sound_item \<G> \<omega> x" "is_word \<G> \<omega>" "nonempty_derives \<G>"
  shows "Earley\<^sub>F_bin_step k \<G> \<omega> (bins bs) \<subseteq> bins (Earley\<^sub>L_bin' k \<G> \<omega> bs i)"
  using assms
proof (induction i rule: Earley\<^sub>L_bin'_induct[OF assms(1), case_names Base Complete\<^sub>F Scan\<^sub>F Pass Predict\<^sub>F])
  case (Base k \<G> \<omega> bs i)
  have "bin (bins bs) k = bin (bins_upto bs k i) k"
    using Base.hyps Base.prems(1) bin_bins_upto_bins_eq wf_earley_input_elim by blast
  thus ?case
    using Scan\<^sub>F_bin_absorb Predict\<^sub>F_bin_absorb Complete\<^sub>F_bins_upto_eq_bins wf_earley_input_elim
      Base.hyps Base.prems(1,2,3,5) Earley\<^sub>F_bin_step_def Complete\<^sub>F_Earley\<^sub>F_bin_step_mono
      Predict\<^sub>F_Earley\<^sub>F_bin_step_mono Scan\<^sub>F_Earley\<^sub>F_bin_step_mono Earley\<^sub>L_bin'_mono
    by (metis (no_types, lifting) Un_assoc sup.orderE)
next
  case (Complete\<^sub>F k \<G> \<omega> bs i x)
  let ?bs' = "upd_bins bs k (Complete\<^sub>L k x bs i)"
  have x: "x \<in> set (items (bs ! k))"
    using Complete\<^sub>F.hyps(1,2) by auto
  have wf: "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Complete\<^sub>F.hyps Complete\<^sub>F.prems(1) wf_earley_input_Complete\<^sub>L by blast
  hence sound: "\<forall>x \<in> set (items (Complete\<^sub>L k x bs i)). sound_item \<G> \<omega> x"
    using sound_Complete\<^sub>L Complete\<^sub>F.hyps(3) Complete\<^sub>F.prems wf_earley_input_elim wf_bins_impl_wf_items x
    by (metis dual_order.refl)
  have "Scan\<^sub>F k \<omega> (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Scan\<^sub>F k \<omega> (bins_upto ?bs' k (i + 1)) = Scan\<^sub>F k \<omega> (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using Complete\<^sub>F.hyps(1) bins_upto_Suc_Un length_nth_upd_bin_bins items_def
      by (metis length_map linorder_not_less sup.boundedE sup.order_iff)
    also have "... = Scan\<^sub>F k \<omega> (bins_upto bs k i \<union> {x})"
      using Complete\<^sub>F.hyps(1,2) Complete\<^sub>F.prems(1) items_nth_idem_upd_bins bins_upto_kth_nth_idem wf_earley_input_elim
      by (metis dual_order.refl items_def length_map not_le_imp_less)
    also have "... \<subseteq> bins bs \<union> Scan\<^sub>F k \<omega> {x}"
      using Complete\<^sub>F.prems(2,3) Scan\<^sub>F_Un Scan\<^sub>F_Earley\<^sub>F_bin_step_mono by fastforce
    also have "... = bins bs"
      using Complete\<^sub>F.hyps(3) by (auto simp: Scan\<^sub>F_def bin_def)
    finally show ?thesis
      using Complete\<^sub>F.prems(1) wf_earley_input_elim bins_upd_bins by blast
  qed
  moreover have "Predict\<^sub>F k \<G> (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Predict\<^sub>F k \<G> (bins_upto ?bs' k (i + 1)) = Predict\<^sub>F k \<G> (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using Complete\<^sub>F.hyps(1) bins_upto_Suc_Un length_nth_upd_bin_bins
      by (metis dual_order.strict_trans1 items_def length_map not_le_imp_less)
    also have "... = Predict\<^sub>F k \<G> (bins_upto bs k i \<union> {x})"
      using Complete\<^sub>F.hyps(1,2) Complete\<^sub>F.prems(1) items_nth_idem_upd_bins bins_upto_kth_nth_idem wf_earley_input_elim
      by (metis dual_order.refl items_def length_map not_le_imp_less)
    also have "... \<subseteq> bins bs \<union> Predict\<^sub>F k \<G> {x}"
      using Complete\<^sub>F.prems(2,3) Predict\<^sub>F_Un Predict\<^sub>F_Earley\<^sub>F_bin_step_mono by blast
    also have "... = bins bs"
      using Complete\<^sub>F.hyps(3) by (auto simp: Predict\<^sub>F_def bin_def)
    finally show ?thesis
      using Complete\<^sub>F.prems(1) wf_earley_input_elim bins_upd_bins by blast
  qed
  moreover have "Complete\<^sub>F k (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Complete\<^sub>F k (bins_upto ?bs' k (i + 1)) = Complete\<^sub>F k (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using bins_upto_Suc_Un length_nth_upd_bin_bins Complete\<^sub>F.hyps(1)
      by (metis (no_types, opaque_lifting) dual_order.trans items_def length_map not_le_imp_less)
    also have "... = Complete\<^sub>F k (bins_upto bs k i \<union> {x})"
      using items_nth_idem_upd_bins Complete\<^sub>F.hyps(1,2) bins_upto_kth_nth_idem Complete\<^sub>F.prems(1) wf_earley_input_elim
      by (metis dual_order.refl items_def length_map not_le_imp_less)
    also have "... \<subseteq> bins bs \<union> set (items (Complete\<^sub>L k x bs i))"
      using Complete\<^sub>F_sub_bins_Un_Complete\<^sub>L Complete\<^sub>F.hyps(3) Complete\<^sub>F.prems(1,2,3) next_symbol_def
        bins_upto_sub_bins wf_bins_kth_bin x Complete\<^sub>F_Earley\<^sub>F_bin_step_mono wf_earley_input_elim
      by (smt (verit, best) option.distinct(1) subset_trans)
    finally show ?thesis
      using Complete\<^sub>F.prems(1) wf_earley_input_elim bins_upd_bins by blast
  qed
  ultimately have "Earley\<^sub>F_bin_step k \<G> \<omega> (bins ?bs') \<subseteq> bins (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1))"
    using Complete\<^sub>F.IH Complete\<^sub>F.prems sound wf Earley\<^sub>F_bin_step_def bins_upto_sub_bins
      wf_earley_input_elim bins_upd_bins
    by (metis UnE sup.boundedI)
  thus ?case
    using Complete\<^sub>F.hyps Complete\<^sub>F.prems(1) Earley\<^sub>L_bin'_simps(2) Earley\<^sub>F_bin_step_sub_mono bins_upd_bins wf_earley_input_elim
    by (smt (verit, best) sup.coboundedI2 sup.orderE sup_ge1)
next
  case (Scan\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs (k+1) (Scan\<^sub>L k \<omega> a x i)"
  have x: "x \<in> set (items (bs ! k))"
    using Scan\<^sub>F.hyps(1,2) by auto
  hence sound: "\<forall>x \<in> set (items (Scan\<^sub>L k \<omega> a x i)). sound_item \<G> \<omega> x"
    using sound_Scan\<^sub>L Scan\<^sub>F.hyps(3,5) Scan\<^sub>F.prems(1,2,3) wf_earley_input_elim wf_bins_impl_wf_items x
    by (metis dual_order.refl)
  have wf: "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Scan\<^sub>F.hyps Scan\<^sub>F.prems(1) wf_earley_input_Scan\<^sub>L by metis
  have "Scan\<^sub>F k \<omega> (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Scan\<^sub>F k \<omega> (bins_upto ?bs' k (i + 1)) = Scan\<^sub>F k \<omega> (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using bins_upto_Suc_Un Scan\<^sub>F.hyps(1) nth_idem_upd_bins
      by (metis Suc_eq_plus1 items_def length_map lessI less_not_refl not_le_imp_less)
    also have "... = Scan\<^sub>F k \<omega> (bins_upto bs k i \<union> {x})"
      using Scan\<^sub>F.hyps(1,2,5) Scan\<^sub>F.prems(1,2) nth_idem_upd_bins bins_upto_kth_nth_idem wf_earley_input_elim
      by (metis add_mono_thms_linordered_field(1) items_def length_map less_add_one linorder_le_less_linear not_add_less1)
    also have "... \<subseteq> bins bs \<union> Scan\<^sub>F k \<omega> {x}"
      using Scan\<^sub>F.prems(2,3) Scan\<^sub>F_Un Scan\<^sub>F_Earley\<^sub>F_bin_step_mono by fastforce
    finally have *: "Scan\<^sub>F k \<omega> (bins_upto ?bs' k (i + 1)) \<subseteq> bins bs \<union> Scan\<^sub>F k \<omega> {x}" .
    show ?thesis
    proof cases
      assume a1: "\<omega>!k = a"
      hence "Scan\<^sub>F k \<omega> {x} = {inc_item x (k+1)}"
        using Scan\<^sub>F.hyps(1-3,5) Scan\<^sub>F.prems(1,2) wf_earley_input_elim apply (auto simp: Scan\<^sub>F_def bin_def)
        using wf_bins_kth_bin x by blast
      hence "Scan\<^sub>F k \<omega> (bins_upto ?bs' k (i + 1)) \<subseteq> bins bs \<union> {inc_item x (k+1)}"
        using * by blast
      also have "... = bins bs \<union> set (items (Scan\<^sub>L k \<omega> a x i))"
        using a1 Scan\<^sub>F.hyps(5) by (auto simp: Scan\<^sub>L_def items_def)
      also have "... = bins ?bs'"
        using Scan\<^sub>F.hyps(5) Scan\<^sub>F.prems(1) wf_earley_input_elim bins_upd_bins by (metis add_mono1)
      finally show ?thesis .
    next
      assume a1: "\<not> \<omega>!k = a"
      hence "Scan\<^sub>F k \<omega> {x} = {}"
        using Scan\<^sub>F.hyps(3) by (auto simp: Scan\<^sub>F_def bin_def)
      hence "Scan\<^sub>F k \<omega> (bins_upto ?bs' k (i + 1)) \<subseteq> bins bs"
        using * by blast
      also have "... \<subseteq> bins ?bs'"
        using Scan\<^sub>F.hyps(5) Scan\<^sub>F.prems(1) wf_earley_input_elim bins_upd_bins
        by (metis Un_left_absorb add_strict_right_mono subset_Un_eq)
      finally show ?thesis .
    qed
  qed
  moreover have "Predict\<^sub>F k \<G> (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Predict\<^sub>F k \<G> (bins_upto ?bs' k (i + 1)) = Predict\<^sub>F k \<G> (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using bins_upto_Suc_Un Scan\<^sub>F.hyps(1) nth_idem_upd_bins
      by (metis Suc_eq_plus1 dual_order.refl items_def length_map lessI linorder_not_less)
    also have "... = Predict\<^sub>F k \<G> (bins_upto bs k i \<union> {x})"
      using Scan\<^sub>F.hyps(1,2,5) Scan\<^sub>F.prems(1,2) nth_idem_upd_bins bins_upto_kth_nth_idem wf_earley_input_elim
      by (metis add_strict_right_mono items_def le_add1 length_map less_add_one linorder_not_le)
    also have "... \<subseteq> bins bs \<union> Predict\<^sub>F k \<G> {x}"
      using Scan\<^sub>F.prems(2,3) Predict\<^sub>F_Un Predict\<^sub>F_Earley\<^sub>F_bin_step_mono by fastforce
    also have "... = bins bs"
      using Scan\<^sub>F.hyps(3,4) Scan\<^sub>F.prems(1) wf_earley_input_elim
      apply (auto simp: Predict\<^sub>F_def bin_def lhs_rule_def)
      by (smt (verit) UnCI in_set_zipE nonterminals_def zip_map_fst_snd)
    finally show ?thesis
      using Scan\<^sub>F.hyps(5) Scan\<^sub>F.prems(1) by (simp add: bins_upd_bins sup.coboundedI1 wf_earley_input_elim)
  qed
  moreover have "Complete\<^sub>F k (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Complete\<^sub>F k (bins_upto ?bs' k (i + 1)) = Complete\<^sub>F k (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using bins_upto_Suc_Un Scan\<^sub>F.hyps(1) nth_idem_upd_bins
      by (metis Suc_eq_plus1 items_def length_map lessI less_not_refl not_le_imp_less)
    also have "... = Complete\<^sub>F k (bins_upto bs k i \<union> {x})"
      using Scan\<^sub>F.hyps(1,2,5) Scan\<^sub>F.prems(1,2) nth_idem_upd_bins bins_upto_kth_nth_idem wf_earley_input_elim
      by (metis add_mono1 items_def length_map less_add_one linorder_not_le not_add_less1)
    also have "... = Complete\<^sub>F k (bins_upto bs k i)"
      using Complete\<^sub>F_Un_eq_terminal Scan\<^sub>F.hyps(3,4) Scan\<^sub>F.prems bins_upto_sub_bins subset_iff
        wf_bins_impl_wf_items wf_bins_kth_bin wf_item_def x wf_earley_input_elim
      by (smt (verit, ccfv_threshold))
    finally show ?thesis
      using Scan\<^sub>F.hyps(5) Scan\<^sub>F.prems(1,2,3) Complete\<^sub>F_Earley\<^sub>F_bin_step_mono by (auto simp: bins_upd_bins wf_earley_input_elim, blast)
  qed
  ultimately have "Earley\<^sub>F_bin_step k \<G> \<omega> (bins ?bs') \<subseteq> bins (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1))"
    using Scan\<^sub>F.IH Scan\<^sub>F.prems Scan\<^sub>F.hyps(5) sound wf Earley\<^sub>F_bin_step_def bins_upto_sub_bins wf_earley_input_elim
      bins_upd_bins by (metis UnE add_mono1 le_supI)
  thus ?case
    using Earley\<^sub>F_bin_step_sub_mono Earley\<^sub>L_bin'_simps(3) Scan\<^sub>F.hyps Scan\<^sub>F.prems(1) wf_earley_input_elim bins_upd_bins
    by (smt (verit, ccfv_SIG) add_mono1 sup.cobounded1 sup.coboundedI2 sup.orderE)
next
  case (Pass k \<G> \<omega> bs i x a)
  have x: "x \<in> set (items (bs ! k))"
    using Pass.hyps(1,2) by auto
  have "Scan\<^sub>F k \<omega> (bins_upto bs k (i + 1)) \<subseteq> bins bs"
    using Scan\<^sub>F_def Pass.hyps(5) by auto
  moreover have "Predict\<^sub>F k \<G> (bins_upto bs k (i + 1)) \<subseteq> bins bs"
  proof -
    have "Predict\<^sub>F k \<G> (bins_upto bs k (i + 1)) = Predict\<^sub>F k \<G> (bins_upto bs k i \<union> {items (bs ! k) ! i})"
      using bins_upto_Suc_Un Pass.hyps(1) by (metis items_def length_map not_le_imp_less)
    also have "... = Predict\<^sub>F k \<G> (bins_upto bs k i \<union> {x})"
      using Pass.hyps(1,2,5) nth_idem_upd_bins bins_upto_kth_nth_idem by simp
    also have "... \<subseteq> bins bs \<union> Predict\<^sub>F k \<G> {x}"
      using Pass.prems(2) Predict\<^sub>F_Un Predict\<^sub>F_Earley\<^sub>F_bin_step_mono by blast
    also have "... = bins bs"
      using Pass.hyps(3,4) Pass.prems(1) wf_earley_input_elim
      apply (auto simp: Predict\<^sub>F_def bin_def lhs_rule_def)
      by (smt (verit, ccfv_SIG) UnCI fst_conv imageI list.set_map nonterminals_def)
    finally show ?thesis
      using bins_upd_bins Pass.hyps(5) Pass.prems(3) by auto
  qed
  moreover have "Complete\<^sub>F k (bins_upto bs k (i + 1)) \<subseteq> bins bs"
  proof -
    have "Complete\<^sub>F k (bins_upto bs k (i + 1)) = Complete\<^sub>F k (bins_upto bs k i \<union> {x})"
      using bins_upto_Suc_Un Pass.hyps(1,2)
      by (metis items_def length_map not_le_imp_less)
    also have "... = Complete\<^sub>F k (bins_upto bs k i)"
      using Complete\<^sub>F_Un_eq_terminal Pass.hyps Pass.prems bins_upto_sub_bins subset_iff
        wf_bins_impl_wf_items wf_item_def wf_bins_kth_bin x wf_earley_input_elim by (smt (verit, best))
    finally show ?thesis
      using Pass.prems(1,2) Complete\<^sub>F_Earley\<^sub>F_bin_step_mono wf_earley_input_elim by blast
  qed
  ultimately have "Earley\<^sub>F_bin_step k \<G> \<omega> (bins bs) \<subseteq> bins (Earley\<^sub>L_bin' k \<G> \<omega> bs (i+1))"
    using Pass.IH Pass.prems Earley\<^sub>F_bin_step_def bins_upto_sub_bins wf_earley_input_elim
    by (metis le_sup_iff)
  thus ?case
    using bins_upd_bins Pass.hyps Pass.prems by simp
next
  case (Predict\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs k (Predict\<^sub>L k \<G> a)"
  have "k \<ge> length \<omega> \<or> \<not> \<omega>!k = a"
    using Predict\<^sub>F.hyps(4) Predict\<^sub>F.prems(4) is_word_def
    by (metis Set.set_insert insert_disjoint(1) not_le_imp_less nth_mem)
  have x: "x \<in> set (items (bs ! k))"
    using Predict\<^sub>F.hyps(1,2) by auto
  hence sound: "\<forall>x \<in> set (items(Predict\<^sub>L k \<G> a)). sound_item \<G> \<omega> x"
    using sound_Predict\<^sub>L Predict\<^sub>F.hyps(3) Predict\<^sub>F.prems wf_earley_input_elim wf_bins_impl_wf_items by fast
  have wf: "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Predict\<^sub>F.hyps Predict\<^sub>F.prems(1) wf_earley_input_Predict\<^sub>L by metis
  have len: "i < length (items (?bs' ! k))"
    using length_nth_upd_bin_bins Predict\<^sub>F.hyps(1)
    by (metis dual_order.strict_trans1 items_def length_map linorder_not_less)
  have "Scan\<^sub>F k \<omega> (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Scan\<^sub>F k \<omega> (bins_upto ?bs' k (i + 1)) = Scan\<^sub>F k \<omega> (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using Predict\<^sub>F.hyps(1) bins_upto_Suc_Un by (metis items_def len length_map)
    also have "... = Scan\<^sub>F k \<omega> (bins_upto bs k i \<union> {x})"
      using Predict\<^sub>F.hyps(1,2) Predict\<^sub>F.prems(1) items_nth_idem_upd_bins bins_upto_kth_nth_idem wf_earley_input_elim
      by (metis dual_order.refl items_def length_map not_le_imp_less)
    also have "... \<subseteq> bins bs \<union> Scan\<^sub>F k \<omega> {x}"
      using Predict\<^sub>F.prems(2,3) Scan\<^sub>F_Un Scan\<^sub>F_Earley\<^sub>F_bin_step_mono by fastforce
    also have "... = bins bs"
      using Predict\<^sub>F.hyps(3) \<open>length \<omega> \<le> k \<or> \<omega> ! k \<noteq> a\<close> by (auto simp: Scan\<^sub>F_def bin_def)
    finally show ?thesis
      using Predict\<^sub>F.prems(1) wf_earley_input_elim bins_upd_bins by blast
  qed
  moreover have "Predict\<^sub>F k \<G> (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Predict\<^sub>F k \<G> (bins_upto ?bs' k (i + 1)) = Predict\<^sub>F k \<G> (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using Predict\<^sub>F.hyps(1) bins_upto_Suc_Un by (metis items_def len length_map)
    also have "... = Predict\<^sub>F k \<G> (bins_upto bs k i \<union> {x})"
      using Predict\<^sub>F.hyps(1,2) Predict\<^sub>F.prems(1) items_nth_idem_upd_bins bins_upto_kth_nth_idem wf_earley_input_elim
      by (metis dual_order.refl items_def length_map not_le_imp_less)
    also have "... \<subseteq> bins bs \<union> Predict\<^sub>F k \<G> {x}"
      using Predict\<^sub>F.prems(2,3) Predict\<^sub>F_Un Predict\<^sub>F_Earley\<^sub>F_bin_step_mono by fastforce
    also have "... = bins bs \<union> set (items (Predict\<^sub>L k \<G> a))"
      using Predict\<^sub>F.hyps Predict\<^sub>F.prems(1-3) wf_earley_input_elim
      apply (auto simp: Predict\<^sub>F_def Predict\<^sub>L_def bin_def items_def)
      using wf_bins_kth_bin x by blast
    finally show ?thesis
      using Predict\<^sub>F.prems(1) wf_earley_input_elim bins_upd_bins by blast
  qed
  moreover have "Complete\<^sub>F k (bins_upto ?bs' k (i + 1)) \<subseteq> bins ?bs'"
  proof -
    have "Complete\<^sub>F k (bins_upto ?bs' k (i + 1)) = Complete\<^sub>F k (bins_upto ?bs' k i \<union> {items (?bs' ! k) ! i})"
      using bins_upto_Suc_Un len by (metis items_def length_map)
    also have "... = Complete\<^sub>F k (bins_upto bs k i \<union> {x})"
      using items_nth_idem_upd_bins Predict\<^sub>F.hyps(1,2) Predict\<^sub>F.prems(1) bins_upto_kth_nth_idem wf_earley_input_elim
      by (metis dual_order.refl items_def length_map not_le_imp_less)
    also have "... = Complete\<^sub>F k (bins_upto bs k i)"
      using Complete\<^sub>F_Un_eq_nonterminal Predict\<^sub>F.prems bins_upto_sub_bins Predict\<^sub>F.hyps(3)
        subset_eq wf_bins_kth_bin x wf_bins_impl_wf_items wf_item_def wf_earley_input_elim
      by (smt (verit, ccfv_SIG) option.simps(3))
    also have "... \<subseteq> bins bs"
      using Complete\<^sub>F_Earley\<^sub>F_bin_step_mono Predict\<^sub>F.prems(2) by blast
    finally show ?thesis
      using bins_upd_bins Predict\<^sub>F.prems(1,2,3) wf_earley_input_elim by blast
  qed
  ultimately have "Earley\<^sub>F_bin_step k \<G> \<omega> (bins ?bs') \<subseteq> bins (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1))"
    using Predict\<^sub>F.IH Predict\<^sub>F.prems sound wf Earley\<^sub>F_bin_step_def bins_upto_sub_bins
      bins_upd_bins wf_earley_input_elim by (metis UnE le_supI)
  hence "Earley\<^sub>F_bin_step k \<G> \<omega> (bins ?bs') \<subseteq> bins (Earley\<^sub>L_bin' k \<G> \<omega> bs i)"
    using Predict\<^sub>F.hyps Earley\<^sub>L_bin'_simps(5) by simp
  moreover have "Earley\<^sub>F_bin_step k \<G> \<omega> (bins bs) \<subseteq> Earley\<^sub>F_bin_step k \<G> \<omega> (bins ?bs')"
    using Earley\<^sub>F_bin_step_sub_mono Predict\<^sub>F.prems(1) wf_earley_input_elim bins_upd_bins by (metis Un_upper1)
  ultimately show ?case
    by blast
qed

lemma Earley\<^sub>F_bin_step_sub_Earley\<^sub>L_bin:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "Earley\<^sub>F_bin_step k \<G> \<omega> (bins_upto bs k 0) \<subseteq> bins bs"
  assumes "\<forall>x \<in> bins bs. sound_item \<G> \<omega> x" "is_word \<G> \<omega>" "nonempty_derives \<G>"
  shows "Earley\<^sub>F_bin_step k \<G> \<omega> (bins bs) \<subseteq> bins (Earley\<^sub>L_bin k \<G> \<omega> bs)"
  using assms Earley\<^sub>F_bin_step_sub_Earley\<^sub>L_bin' Earley\<^sub>L_bin_def by metis

lemma bins_eq_items_Complete\<^sub>L:
  assumes "bins_eq_items as bs" "start_item x < length as"
  shows "items (Complete\<^sub>L k x as i) = items (Complete\<^sub>L k x bs i)"
proof -
  let ?orig_a = "as ! start_item x"
  let ?orig_b = "bs ! start_item x"
  have "items ?orig_a = items ?orig_b"
    using assms by (metis (no_types, opaque_lifting) bins_eq_items_def length_map nth_map)
  thus ?thesis
    unfolding Complete\<^sub>L_def by simp
qed

lemma Earley\<^sub>L_bin'_bins_eq:
  assumes "(k, \<G>, \<omega>, as) \<in> wf_earley_input"
  assumes "bins_eq_items as bs" "wf_bins \<G> \<omega> as"
  shows "bins_eq_items (Earley\<^sub>L_bin' k \<G> \<omega> as i) (Earley\<^sub>L_bin' k \<G> \<omega> bs i)"
  using assms
proof (induction i arbitrary: bs rule: Earley\<^sub>L_bin'_induct[OF assms(1), case_names Base Complete\<^sub>F Scan\<^sub>F Pass Predict\<^sub>F])
  case (Base k \<G> \<omega> as i)
  have "Earley\<^sub>L_bin' k \<G> \<omega> as i = as"
    by (simp add: Base.hyps)
  moreover have "Earley\<^sub>L_bin' k \<G> \<omega> bs i = bs"
    using Base.hyps Base.prems(1,2) unfolding bins_eq_items_def
    by (metis Earley\<^sub>L_bin'_simps(1) length_map nth_map wf_earley_input_elim)
  ultimately show ?case
    using Base.prems(2) by presburger
next
  case (Complete\<^sub>F k \<G> \<omega> as i x)
  let ?as' = "upd_bins as k (Complete\<^sub>L k x as i)"
  let ?bs' = "upd_bins bs k (Complete\<^sub>L k x bs i)"
  have k: "k < length as"
    using Complete\<^sub>F.prems(1) wf_earley_input_elim by blast
  hence wf_x: "wf_item \<G> \<omega> x"
    using Complete\<^sub>F.hyps(1,2) Complete\<^sub>F.prems(3) wf_bins_kth_bin by fastforce
  have "(k, \<G>, \<omega>, ?as') \<in> wf_earley_input"
    using Complete\<^sub>F.hyps Complete\<^sub>F.prems(1) wf_earley_input_Complete\<^sub>L by blast
  moreover have "bins_eq_items ?as' ?bs'"
    using Complete\<^sub>F.hyps(1,2) Complete\<^sub>F.prems(2,3) bins_eq_items_dist_upd_bins bins_eq_items_Complete\<^sub>L
      k wf_x wf_bins_kth_bin wf_item_def by (metis dual_order.strict_trans2 leI nth_mem)
  ultimately have "bins_eq_items (Earley\<^sub>L_bin' k \<G> \<omega> ?as' (i + 1)) (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i + 1))"
    using Complete\<^sub>F.IH wf_earley_input_elim by blast
  moreover have "Earley\<^sub>L_bin' k \<G> \<omega> as i = Earley\<^sub>L_bin' k \<G> \<omega> ?as' (i+1)"
    using Complete\<^sub>F.hyps by simp
  moreover have "Earley\<^sub>L_bin' k \<G> \<omega> bs i = Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)"
    using Complete\<^sub>F.hyps Complete\<^sub>F.prems unfolding bins_eq_items_def
    by (metis Earley\<^sub>L_bin'_simps(2) map_eq_imp_length_eq nth_map wf_earley_input_elim)
  ultimately show ?case
    by argo
next
  case (Scan\<^sub>F k \<G> \<omega> as i x a)
  let ?as' = "upd_bins as (k+1) (Scan\<^sub>L k \<omega> a x i)"
  let ?bs' = "upd_bins bs (k+1) (Scan\<^sub>L k \<omega> a x i)"
  have "(k, \<G>, \<omega>, ?as') \<in> wf_earley_input"
    using Scan\<^sub>F.hyps Scan\<^sub>F.prems(1) wf_earley_input_Scan\<^sub>L by fast
  moreover have "bins_eq_items ?as' ?bs'"
    using Scan\<^sub>F.hyps(5) Scan\<^sub>F.prems(1,2) bins_eq_items_dist_upd_bins add_mono1 wf_earley_input_elim by metis
  ultimately have "bins_eq_items (Earley\<^sub>L_bin' k \<G> \<omega> ?as' (i + 1)) (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i + 1))"
    using Scan\<^sub>F.IH wf_earley_input_elim by blast
  moreover have "Earley\<^sub>L_bin' k \<G> \<omega> as i = Earley\<^sub>L_bin' k \<G> \<omega> ?as' (i+1)"
    using Scan\<^sub>F.hyps by simp
  moreover have "Earley\<^sub>L_bin' k \<G> \<omega> bs i = Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)"
    using Scan\<^sub>F.hyps Scan\<^sub>F.prems unfolding bins_eq_items_def
    by (smt (verit, ccfv_threshold) Earley\<^sub>L_bin'_simps(3) length_map nth_map wf_earley_input_elim)
  ultimately show ?case
    by argo
next
  case (Pass k \<G> \<omega> as i x a)
  have "bins_eq_items (Earley\<^sub>L_bin' k \<G> \<omega> as (i + 1)) (Earley\<^sub>L_bin' k \<G> \<omega> bs (i + 1))"
    using Pass.prems Pass.IH by blast
  moreover have "Earley\<^sub>L_bin' k \<G> \<omega> as i = Earley\<^sub>L_bin' k \<G> \<omega> as (i+1)"
    using Pass.hyps by simp
  moreover have "Earley\<^sub>L_bin' k \<G> \<omega> bs i = Earley\<^sub>L_bin' k \<G> \<omega> bs (i+1)"
    using Pass.hyps Pass.prems unfolding bins_eq_items_def
    by (metis Earley\<^sub>L_bin'_simps(4) map_eq_imp_length_eq nth_map wf_earley_input_elim)
  ultimately show ?case
    by argo
next
  case (Predict\<^sub>F k \<G> \<omega> as i x a)
  let ?as' = "upd_bins as k (Predict\<^sub>L k \<G> a)"
  let ?bs' = "upd_bins bs k (Predict\<^sub>L k \<G> a)"
  have "(k, \<G>, \<omega>, ?as') \<in> wf_earley_input"
    using Predict\<^sub>F.hyps Predict\<^sub>F.prems(1) wf_earley_input_Predict\<^sub>L by fast
  moreover have "bins_eq_items ?as' ?bs'"
    using Predict\<^sub>F.prems(1,2) bins_eq_items_dist_upd_bins wf_earley_input_elim by blast
  ultimately have "bins_eq_items (Earley\<^sub>L_bin' k \<G> \<omega> ?as' (i + 1)) (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i + 1))"
    using Predict\<^sub>F.IH wf_earley_input_elim by blast
  moreover have "Earley\<^sub>L_bin' k \<G> \<omega> as i = Earley\<^sub>L_bin' k \<G> \<omega> ?as' (i+1)"
    using Predict\<^sub>F.hyps by simp
  moreover have "Earley\<^sub>L_bin' k \<G> \<omega> bs i = Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)"
    using Predict\<^sub>F.hyps Predict\<^sub>F.prems unfolding bins_eq_items_def
    by (metis Earley\<^sub>L_bin'_simps(5) length_map nth_map wf_earley_input_elim)
  ultimately show ?case
    by argo
qed

lemma Earley\<^sub>L_bin'_idem:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "i \<le> j" "\<forall>x \<in> bins bs. sound_item \<G> \<omega> x" "nonempty_derives \<G>"
  shows "bins (Earley\<^sub>L_bin' k \<G> \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> bs i) j) = bins (Earley\<^sub>L_bin' k \<G> \<omega> bs i)"
  using assms
proof (induction i arbitrary: j rule: Earley\<^sub>L_bin'_induct[OF assms(1), case_names Base Complete\<^sub>F Scan\<^sub>F Pass Predict\<^sub>F])
  case (Complete\<^sub>F k \<G> \<omega> bs i x)
  let ?bs' = "upd_bins bs k (Complete\<^sub>L k x bs i)"
  have x: "x \<in> set (items (bs ! k))"
    using Complete\<^sub>F.hyps(1,2) by auto
  have wf: "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Complete\<^sub>F.hyps Complete\<^sub>F.prems(1) wf_earley_input_Complete\<^sub>L by blast
  hence "\<forall>x \<in> set (items (Complete\<^sub>L k x bs i)). sound_item \<G> \<omega> x"
    using sound_Complete\<^sub>L Complete\<^sub>F.hyps(3) Complete\<^sub>F.prems wf_earley_input_elim wf_bins_impl_wf_items x
    by (metis dual_order.refl)
  hence sound: "\<forall>x \<in> bins ?bs'. sound_item \<G> \<omega> x"
    by (metis Complete\<^sub>F.prems(1,3) UnE bins_upd_bins wf_earley_input_elim)
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using wf sound Complete\<^sub>F Earley\<^sub>L_bin'_simps(2) by metis
  next
    assume "\<not> i+1 \<le> j"
    hence "i = j"
      using Complete\<^sub>F.prems(2) by simp
    have "bins (Earley\<^sub>L_bin' k \<G> \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> bs i) j) = bins (Earley\<^sub>L_bin' k \<G> \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)) j)"
      using Earley\<^sub>L_bin'_simps(2) Complete\<^sub>F.hyps(1-3) by simp
    also have "... = bins (Earley\<^sub>L_bin' k \<G> \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)) (j+1))"
    proof -
      let ?bs'' = "Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)"
      have "length (items (?bs'' ! k)) \<ge> length (items (bs ! k))"
        using length_nth_bin_Earley\<^sub>L_bin' length_nth_upd_bin_bins order_trans wf Complete\<^sub>F.hyps Complete\<^sub>F.prems(1)
        by (smt (verit, ccfv_threshold) Earley\<^sub>L_bin'_simps(2))
      hence 0: "\<not> length (items (?bs'' ! k)) \<le> j"
        using \<open>i = j\<close> Complete\<^sub>F.hyps(1) by linarith
      have "x = items (?bs' ! k) ! j"
        using \<open>i = j\<close> items_nth_idem_upd_bins Complete\<^sub>F.hyps(1,2)
        by (metis items_def length_map not_le_imp_less)
      hence 1: "x = items (?bs'' ! k) ! j"
        using \<open>i = j\<close> kth_Earley\<^sub>L_bin'_bins Complete\<^sub>F.hyps Complete\<^sub>F.prems(1) Earley\<^sub>L_bin'_simps(2) leI by metis
      have "bins (Earley\<^sub>L_bin' k \<G> \<omega> ?bs'' j) = bins (Earley\<^sub>L_bin' k \<G> \<omega> (upd_bins ?bs'' k (Complete\<^sub>L k x ?bs'' i)) (j+1))"
        using Earley\<^sub>L_bin'_simps(2) 0 1 Complete\<^sub>F.hyps(1,3) Complete\<^sub>F.prems(2) \<open>i = j\<close> by auto
      moreover have "bins_eq_items (upd_bins ?bs'' k (Complete\<^sub>L k x ?bs'' i)) ?bs''"
      proof -
        have "k < length bs"
          using Complete\<^sub>F.prems(1) wf_earley_input_elim by blast
        have 0: "set (Complete\<^sub>L k x bs i) = set (Complete\<^sub>L k x ?bs'' i)"
        proof (cases "start_item x = k")
          case True
          thus ?thesis
            using impossible_complete_item kth_bin_sub_bins Complete\<^sub>F.hyps(3) Complete\<^sub>F.prems wf_earley_input_elim
              wf_bins_kth_bin x next_symbol_def by (metis option.distinct(1) subsetD)
        next
          case False
          hence "start_item x < k"
            using x Complete\<^sub>F.prems(1) wf_bins_kth_bin wf_item_def nat_less_le by (metis wf_earley_input_elim)
          hence "bs ! start_item x = ?bs'' ! start_item x"
            using False nth_idem_upd_bins nth_Earley\<^sub>L_bin'_eq wf by metis
          thus ?thesis
            using Complete\<^sub>L_eq_start_item by metis
        qed
        have "set (items (Complete\<^sub>L k x bs i)) \<subseteq> set (items (?bs' ! k))"
          by (simp add: \<open>k < length bs\<close> upd_bins_def set_items_upds_bin)
        hence "set (items (Complete\<^sub>L k x ?bs'' i)) \<subseteq> set (items (?bs' ! k))"
          using 0 by (simp add: items_def)
        also have "... \<subseteq> set (items (?bs'' ! k))"
          by (simp add: wf nth_bin_sub_Earley\<^sub>L_bin')
        finally show ?thesis
          using bins_eq_items_upd_bins by blast
      qed
      moreover have "(k, \<G>, \<omega>, upd_bins ?bs'' k (Complete\<^sub>L k x ?bs'' i)) \<in> wf_earley_input"
        using wf_earley_input_Earley\<^sub>L_bin' wf_earley_input_Complete\<^sub>L Complete\<^sub>F.hyps Complete\<^sub>F.prems(1)
          \<open>length (items (bs ! k)) \<le> length (items (?bs'' ! k))\<close> kth_Earley\<^sub>L_bin'_bins 0 1 by blast
      ultimately show ?thesis
        using Earley\<^sub>L_bin'_bins_eq bins_eq_items_imp_eq_bins wf_earley_input_elim by blast
    qed
    also have "... = bins (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i + 1))"
      using Complete\<^sub>F.IH[OF wf _ sound Complete\<^sub>F.prems(4)] \<open>i = j\<close> by blast
    finally show ?thesis
      using Complete\<^sub>F.hyps by simp
  qed
next
  case (Scan\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs (k+1) (Scan\<^sub>L k \<omega> a x i)"
  have x: "x \<in> set (items (bs ! k))"
    using Scan\<^sub>F.hyps(1,2) by auto
  hence "\<forall>x \<in> set (items (Scan\<^sub>L k \<omega> a x i)). sound_item \<G> \<omega> x"
    using sound_Scan\<^sub>L Scan\<^sub>F.hyps(3,5) Scan\<^sub>F.prems(1,2,3) wf_earley_input_elim wf_bins_impl_wf_items x
    by (metis dual_order.refl)
  hence sound: "\<forall>x \<in> bins ?bs'. sound_item \<G> \<omega> x"
    using Scan\<^sub>F.hyps(5) Scan\<^sub>F.prems(1,3) bins_upd_bins wf_earley_input_elim
    by (metis UnE add_less_cancel_right)
  have wf: "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Scan\<^sub>F.hyps Scan\<^sub>F.prems(1) wf_earley_input_Scan\<^sub>L by metis
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using sound Scan\<^sub>F by (metis Earley\<^sub>L_bin'_simps(3) wf_earley_input_Scan\<^sub>L)
  next
    assume "\<not> i+1 \<le> j"
    hence "i = j"
      using Scan\<^sub>F.prems(2) by auto
    have "bins (Earley\<^sub>L_bin' k \<G> \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> bs i) j) = bins (Earley\<^sub>L_bin' k \<G> \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)) j)"
      using Scan\<^sub>F.hyps by simp
    also have "... = bins (Earley\<^sub>L_bin' k \<G> \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)) (j+1))"
    proof -
      let ?bs'' = "Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)"
      have "length (items (?bs'' ! k)) \<ge> length (items (bs ! k))"
        using length_nth_bin_Earley\<^sub>L_bin' length_nth_upd_bin_bins order_trans Scan\<^sub>F.hyps Scan\<^sub>F.prems(1) Earley\<^sub>L_bin'_simps(3)
        by (smt (verit, ccfv_SIG))
      hence "bins (Earley\<^sub>L_bin' k \<G> \<omega> ?bs'' j) = bins (Earley\<^sub>L_bin' k \<G> \<omega> (upd_bins ?bs'' (k+1) (Scan\<^sub>L k \<omega> a x i)) (j+1))"
        using \<open>i = j\<close> kth_Earley\<^sub>L_bin'_bins nth_idem_upd_bins Earley\<^sub>L_bin'_simps(3) Scan\<^sub>F.hyps Scan\<^sub>F.prems(1) by (smt (verit, best) leI le_trans)
      moreover have "bins_eq_items (upd_bins ?bs'' (k+1) (Scan\<^sub>L k \<omega> a x i)) ?bs''"
      proof -
        have "k+1 < length bs"
          using Scan\<^sub>F.hyps(5) Scan\<^sub>F.prems wf_earley_input_elim by fastforce+
        hence "set (items (Scan\<^sub>L k \<omega> a x i)) \<subseteq> set (items (?bs' ! (k+1)))"
          by (simp add: upd_bins_def set_items_upds_bin)
        also have "... \<subseteq> set (items (?bs'' ! (k+1)))"
          using wf nth_bin_sub_Earley\<^sub>L_bin' by blast
        finally show ?thesis
          using bins_eq_items_upd_bins by blast
      qed
      moreover have "(k, \<G>, \<omega>, upd_bins ?bs'' (k+1) (Scan\<^sub>L k \<omega> a x i)) \<in> wf_earley_input"
        using wf_earley_input_Earley\<^sub>L_bin' wf_earley_input_Scan\<^sub>L Scan\<^sub>F.hyps Scan\<^sub>F.prems(1)
          \<open>length (items (bs ! k)) \<le> length (items (?bs'' ! k))\<close> kth_Earley\<^sub>L_bin'_bins
        by (smt (verit, ccfv_SIG) Earley\<^sub>L_bin'_simps(3) linorder_not_le order.trans)
      ultimately show ?thesis
        using Earley\<^sub>L_bin'_bins_eq bins_eq_items_imp_eq_bins wf_earley_input_elim by blast
    qed
    also have "... = bins (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i + 1))"
      using \<open>i = j\<close> Scan\<^sub>F.IH Scan\<^sub>F.prems Scan\<^sub>F.hyps sound wf_earley_input_Scan\<^sub>L by fast
    finally show ?thesis
      using Scan\<^sub>F.hyps by simp
  qed
next
  case (Pass k \<G> \<omega> bs i x a)
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using Pass by (metis Earley\<^sub>L_bin'_simps(4))
  next
    assume "\<not> i+1 \<le> j"
    show ?thesis
      using Pass Earley\<^sub>L_bin'_simps(1,4) kth_Earley\<^sub>L_bin'_bins by (metis Suc_eq_plus1 Suc_leI antisym_conv2 not_le_imp_less)
  qed
next
  case (Predict\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs k (Predict\<^sub>L k \<G> a)"
  have x: "x \<in> set (items (bs ! k))"
    using Predict\<^sub>F.hyps(1,2) by auto
  hence "\<forall>x \<in> set (items(Predict\<^sub>L k \<G> a)). sound_item \<G> \<omega> x"
    using sound_Predict\<^sub>L Predict\<^sub>F.hyps(3) Predict\<^sub>F.prems wf_earley_input_elim wf_bins_impl_wf_items by fast
  hence sound: "\<forall>x \<in> bins ?bs'. sound_item \<G> \<omega> x"
    using Predict\<^sub>F.prems(1,3) UnE bins_upd_bins wf_earley_input_elim by metis
  have wf: "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Predict\<^sub>F.hyps Predict\<^sub>F.prems(1) wf_earley_input_Predict\<^sub>L by metis
  have len: "i < length (items (?bs' ! k))"
    using length_nth_upd_bin_bins Predict\<^sub>F.hyps(1) Orderings.preorder_class.dual_order.strict_trans1 linorder_not_less
    by (metis items_def length_map)
  show ?case
  proof cases
    assume "i+1 \<le> j"
    thus ?thesis
      using sound wf Predict\<^sub>F by (metis Earley\<^sub>L_bin'_simps(5))
  next
    assume "\<not> i+1 \<le> j"
    hence "i = j"
      using Predict\<^sub>F.prems(2) by auto
    have "bins (Earley\<^sub>L_bin' k \<G> \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> bs i) j) = bins (Earley\<^sub>L_bin' k \<G> \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)) j)"
      using Predict\<^sub>F.hyps by simp
    also have "... = bins (Earley\<^sub>L_bin' k \<G> \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)) (j+1))"
    proof -
      let ?bs'' = "Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)"
      have "length (items (?bs'' ! k)) \<ge> length (items (bs ! k))"
        using length_nth_bin_Earley\<^sub>L_bin' length_nth_upd_bin_bins order_trans wf
        by (metis (no_types, lifting) items_def length_map)
      hence "bins (Earley\<^sub>L_bin' k \<G> \<omega> ?bs'' j) = bins (Earley\<^sub>L_bin' k \<G> \<omega> (upd_bins ?bs'' k (Predict\<^sub>L k \<G> a)) (j+1))"
        using \<open>i = j\<close> kth_Earley\<^sub>L_bin'_bins nth_idem_upd_bins Earley\<^sub>L_bin'_simps(5) Predict\<^sub>F.hyps Predict\<^sub>F.prems(1) length_bins_Earley\<^sub>L_bin'
          wf_bins_Earley\<^sub>L_bin' wf_bins_kth_bin wf_item_def x by (smt (verit, ccfv_SIG) linorder_not_le order.trans)
      moreover have "bins_eq_items (upd_bins ?bs'' k (Predict\<^sub>L k \<G> a)) ?bs''"
      proof -
        have "k < length bs"
          using wf_earley_input_elim[OF Predict\<^sub>F.prems(1)] by blast
        hence "set (items (Predict\<^sub>L k \<G> a)) \<subseteq> set (items (?bs' ! k))"
          by (simp add: upd_bins_def set_items_upds_bin)
        also have "... \<subseteq> set (items (?bs'' ! k))"
          using wf nth_bin_sub_Earley\<^sub>L_bin' by blast
        finally show ?thesis
          using bins_eq_items_upd_bins by blast
      qed
      moreover have "(k, \<G>, \<omega>, upd_bins ?bs'' k (Predict\<^sub>L k \<G> a)) \<in> wf_earley_input"
        using wf_earley_input_Earley\<^sub>L_bin' wf_earley_input_Predict\<^sub>L Predict\<^sub>F.hyps Predict\<^sub>F.prems(1)
          \<open>length (items (bs ! k)) \<le> length (items (?bs'' ! k))\<close> kth_Earley\<^sub>L_bin'_bins
        by (smt (verit, best) Earley\<^sub>L_bin'_simps(5) dual_order.trans not_le_imp_less)
      ultimately show ?thesis
        using Earley\<^sub>L_bin'_bins_eq bins_eq_items_imp_eq_bins wf_earley_input_elim by blast
    qed
    also have "... = bins (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i + 1))"
      using \<open>i = j\<close> Predict\<^sub>F.IH Predict\<^sub>F.prems sound wf by (metis order_refl)
    finally show ?thesis
      using Predict\<^sub>F.hyps by simp
  qed
qed simp

lemma Earley\<^sub>L_bin_idem:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "\<forall>x \<in> bins bs. sound_item \<G> \<omega> x" "nonempty_derives \<G>"
  shows "bins (Earley\<^sub>L_bin k \<G> \<omega> (Earley\<^sub>L_bin k \<G> \<omega> bs)) = bins (Earley\<^sub>L_bin k \<G> \<omega> bs)"
  using assms Earley\<^sub>L_bin'_idem Earley\<^sub>L_bin_def le0 by metis

lemma funpower_Earley\<^sub>F_bin_step_sub_Earley\<^sub>L_bin:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "Earley\<^sub>F_bin_step k \<G> \<omega> (bins_upto bs k 0) \<subseteq> bins bs" "\<forall>x \<in> bins bs. sound_item \<G> \<omega> x"
  assumes "is_word \<G> \<omega>" "nonempty_derives \<G>"
  shows "funpower (Earley\<^sub>F_bin_step k \<G> \<omega>) n (bins bs) \<subseteq> bins (Earley\<^sub>L_bin k \<G> \<omega> bs)"
  using assms
proof (induction n)
  case 0
  thus ?case
    using Earley\<^sub>L_bin'_mono Earley\<^sub>L_bin_def by (simp add: Earley\<^sub>L_bin'_mono Earley\<^sub>L_bin_def)
next
  case (Suc n)
  have 0: "Earley\<^sub>F_bin_step k \<G> \<omega> (bins_upto (Earley\<^sub>L_bin k \<G> \<omega> bs) k 0) \<subseteq> bins (Earley\<^sub>L_bin k \<G> \<omega> bs)"
    using Earley\<^sub>L_bin'_mono bins_upto_k0_Earley\<^sub>L_bin'_eq assms(1,2) Earley\<^sub>L_bin_def order_trans
    by (metis (no_types, lifting))
  have "funpower (Earley\<^sub>F_bin_step k \<G> \<omega>) (Suc n) (bins bs) \<subseteq> Earley\<^sub>F_bin_step k \<G> \<omega> (bins (Earley\<^sub>L_bin k \<G> \<omega> bs))"
    using Earley\<^sub>F_bin_step_sub_mono Suc by (metis funpower.simps(2))
  also have "... \<subseteq> bins (Earley\<^sub>L_bin k \<G> \<omega> (Earley\<^sub>L_bin k \<G> \<omega> bs))"
    using Earley\<^sub>F_bin_step_sub_Earley\<^sub>L_bin Suc.prems wf_bins_Earley\<^sub>L_bin sound_Earley\<^sub>L_bin 0 wf_earley_input_Earley\<^sub>L_bin by blast
  also have "... \<subseteq> bins (Earley\<^sub>L_bin k \<G> \<omega> bs)"
    using Earley\<^sub>L_bin_idem Suc.prems by blast
  finally show ?case .
qed

lemma Earley\<^sub>F_bin_sub_Earley\<^sub>L_bin:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "Earley\<^sub>F_bin_step k \<G> \<omega> (bins_upto bs k 0) \<subseteq> bins bs" "\<forall>x \<in> bins bs. sound_item \<G> \<omega> x"
  assumes "is_word \<G> \<omega>" "nonempty_derives \<G>"
  shows "Earley\<^sub>F_bin k \<G> \<omega> (bins bs) \<subseteq> bins (Earley\<^sub>L_bin k \<G> \<omega> bs)"
  using assms funpower_Earley\<^sub>F_bin_step_sub_Earley\<^sub>L_bin Earley\<^sub>F_bin_def elem_limit_simp by fastforce

lemma Earley\<^sub>F_bins_sub_Earley\<^sub>L_bins:
  assumes "k \<le> length \<omega>"
  assumes "is_word \<G> \<omega>" "nonempty_derives \<G>"
  shows "Earley\<^sub>F_bins k \<G> \<omega> \<subseteq> bins (Earley\<^sub>L_bins k \<G> \<omega>)"
  using assms
proof (induction k)
  case 0
  hence "Earley\<^sub>F_bin 0 \<G> \<omega> (Init\<^sub>F \<G>) \<subseteq> bins (Earley\<^sub>L_bin 0 \<G> \<omega> (Init\<^sub>L \<G> \<omega>))"
    using Earley\<^sub>F_bin_sub_Earley\<^sub>L_bin Init\<^sub>L_eq_Init\<^sub>F length_bins_Init\<^sub>L Init\<^sub>L_eq_Init\<^sub>F sound_Init bins_upto_empty
      Earley\<^sub>F_bin_step_empty bins_upto_sub_bins wf_earley_input_Init\<^sub>L wf_earley_input_elim
    by (smt (verit, ccfv_threshold) Init\<^sub>F_sub_Earley basic_trans_rules(31) sound_Earley wf_bins_impl_wf_items)
  thus ?case
    by simp
next
  case (Suc k)
  have wf: "(Suc k, \<G>, \<omega>, Earley\<^sub>L_bins k \<G> \<omega>) \<in> wf_earley_input"
    by (simp add: Suc.prems(1) Suc_leD assms(2) wf_earley_input_intro)
  have sub: "Earley\<^sub>F_bin_step (Suc k) \<G> \<omega> (bins_upto (Earley\<^sub>L_bins k \<G> \<omega>) (Suc k) 0) \<subseteq> bins (Earley\<^sub>L_bins k \<G> \<omega>)"
  proof -
    have "bin (bins_upto (Earley\<^sub>L_bins k \<G> \<omega>) (Suc k) 0) (Suc k) = {}"
      using kth_bin_bins_upto_empty wf Suc.prems wf_earley_input_elim by blast
    hence "Earley\<^sub>F_bin_step (Suc k) \<G> \<omega> (bins_upto (Earley\<^sub>L_bins k \<G> \<omega>) (Suc k) 0) = bins_upto (Earley\<^sub>L_bins k \<G> \<omega>) (Suc k) 0"
      unfolding Earley\<^sub>F_bin_step_def Scan\<^sub>F_def Complete\<^sub>F_def Predict\<^sub>F_def bin_def by blast
    also have "... \<subseteq> bins (Earley\<^sub>L_bins k \<G> \<omega>)"
      using wf Suc.prems bins_upto_sub_bins wf_earley_input_elim by blast
    finally show ?thesis .
  qed
  have sound: "\<forall>x \<in> bins (Earley\<^sub>L_bins k \<G> \<omega>). sound_item \<G> \<omega> x"
    using Suc Earley\<^sub>L_bins_sub_Earley\<^sub>F_bins by (metis Suc_leD Earley\<^sub>F_bins_sub_Earley in_mono sound_Earley wf_Earley)
  have "Earley\<^sub>F_bins (Suc k) \<G> \<omega> \<subseteq> Earley\<^sub>F_bin (Suc k) \<G> \<omega> (bins (Earley\<^sub>L_bins k \<G> \<omega>))"
    using Suc Earley\<^sub>F_bin_sub_mono by simp
  also have "... \<subseteq> bins (Earley\<^sub>L_bin (Suc k) \<G> \<omega> (Earley\<^sub>L_bins k \<G> \<omega>))"
    using Earley\<^sub>F_bin_sub_Earley\<^sub>L_bin wf sub sound Suc.prems by fastforce
  finally show ?case
    by simp
qed

lemma Earley\<^sub>F_sub_Earley\<^sub>L:
  assumes "is_word \<G> \<omega>" "\<epsilon>_free \<G>"
  shows "Earley\<^sub>F \<G> \<omega> \<subseteq> bins (Earley\<^sub>L \<G> \<omega>)"
  using assms Earley\<^sub>F_bins_sub_Earley\<^sub>L_bins Earley\<^sub>F_def Earley\<^sub>L_def
  by (metis \<epsilon>_free_impl_nonempty_derives dual_order.refl)

theorem completeness_Earley\<^sub>L:
  assumes "\<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>" "is_word \<G> \<omega>" "\<epsilon>_free \<G>"
  shows "recognizing (bins (Earley\<^sub>L \<G> \<omega>)) \<G> \<omega>"
  using assms Earley\<^sub>F_sub_Earley\<^sub>L Earley\<^sub>L_sub_Earley\<^sub>F completeness_Earley\<^sub>F by (metis subset_antisym)


subsection \<open>Correctness\<close>

theorem Earley_eq_Earley\<^sub>L:
  assumes "is_word \<G> \<omega>" "\<epsilon>_free \<G>"
  shows "Earley \<G> \<omega> = bins (Earley\<^sub>L \<G> \<omega>)"
  using assms Earley\<^sub>F_sub_Earley\<^sub>L Earley\<^sub>L_sub_Earley\<^sub>F Earley_eq_Earley\<^sub>F by blast

lemma correctness_recognizer:
  assumes "is_word \<G> \<omega>" "\<epsilon>_free \<G>"
  shows "recognizer \<G> \<omega> \<longleftrightarrow> \<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>" (is "?L \<longleftrightarrow> ?R")
proof standard
  assume ?L
  then obtain x where "x \<in> set (items (Earley\<^sub>L \<G> \<omega> ! length \<omega>))" "is_finished \<G> \<omega> x"
    using assms(1) unfolding recognizer_def by blast
  moreover have "x \<in> bins (Earley\<^sub>L \<G> \<omega>)"
    using assms(2) kth_bin_sub_bins \<open>x \<in> set (items (Earley\<^sub>L \<G> \<omega> ! length \<omega>))\<close>
    by (metis (no_types, lifting) Earley\<^sub>L_def dual_order.refl length_Earley\<^sub>L_bins length_bins_Init\<^sub>L less_add_one subsetD)
  ultimately show ?R
    using recognizing_def soundness_Earley\<^sub>L by blast
next
  assume ?R
  thus ?L
    using assms wf_item_in_kth_bin recognizing_def is_finished_def
    by (metis completeness_Earley\<^sub>L recognizer_def wf_bins_Earley\<^sub>L)
qed

end