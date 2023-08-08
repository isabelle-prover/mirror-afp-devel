theory Earley_Parser
  imports
    Earley_Recognizer
    "HOL-Library.Monad_Syntax"
begin

section \<open>Earley parser\<close>

subsection \<open>Pointer lemmas\<close>

definition predicts :: "'a item \<Rightarrow> bool" where
  "predicts x \<equiv> item_origin x = item_end x \<and> item_dot x = 0"

definition scans :: "'a sentence \<Rightarrow> nat \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> bool" where
  "scans \<omega> k x y \<equiv> y = inc_item x k \<and> (\<exists>a. next_symbol x = Some a \<and> \<omega>!(k-1) = a)"

definition completes :: "nat \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> bool" where
  "completes k x y z \<equiv> y = inc_item x k \<and> is_complete z \<and> item_origin z = item_end x \<and>
    (\<exists>N. next_symbol x = Some N \<and> N = item_rule_head z)"

definition sound_null_ptr :: "'a entry \<Rightarrow> bool" where
  "sound_null_ptr e \<equiv> (pointer e = Null \<longrightarrow> predicts (item e))"

definition sound_pre_ptr :: "'a sentence \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a entry \<Rightarrow> bool" where
  "sound_pre_ptr \<omega> bs k e \<equiv> \<forall>pre. pointer e = Pre pre \<longrightarrow>
    k > 0 \<and> pre < length (bs!(k-1)) \<and> scans \<omega> k (item (bs!(k-1)!pre)) (item e)"

definition sound_prered_ptr :: "'a bins \<Rightarrow> nat \<Rightarrow> 'a entry \<Rightarrow> bool" where
  "sound_prered_ptr bs k e \<equiv> \<forall>p ps k' pre red. pointer e = PreRed p ps \<and> (k', pre, red) \<in> set (p#ps) \<longrightarrow>
    k' < k \<and> pre < length (bs!k') \<and> red < length (bs!k) \<and> completes k (item (bs!k'!pre)) (item e) (item (bs!k!red))"

definition sound_ptrs :: "'a sentence \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "sound_ptrs \<omega> bs \<equiv> \<forall>k < length bs. \<forall>e \<in> set (bs!k).
    sound_null_ptr e \<and> sound_pre_ptr \<omega> bs k e \<and> sound_prered_ptr bs k e"

definition mono_red_ptr :: "'a bins \<Rightarrow> bool" where
  "mono_red_ptr bs \<equiv> \<forall>k < length bs. \<forall>i < length (bs!k).
    \<forall>k' pre red ps. pointer (bs!k!i) = PreRed (k', pre, red) ps \<longrightarrow> red < i"

lemma nth_item_bin_upd:
  "n < length es \<Longrightarrow> item (bin_upd e es ! n) = item (es!n)"
  by (induction es arbitrary: e n) (auto simp: less_Suc_eq_0_disj split: entry.splits pointer.splits)

lemma bin_upd_append:
  "item e \<notin> set (items es) \<Longrightarrow> bin_upd e es = es @ [e]"
  by (induction es arbitrary: e) (auto simp: items_def split: entry.splits pointer.splits)

lemma bin_upd_null_pre:
  "item e \<in> set (items es) \<Longrightarrow> pointer e = Null \<or> pointer e = Pre pre \<Longrightarrow> bin_upd e es = es"
  by (induction es arbitrary: e) (auto simp: items_def split: entry.splits)

lemma bin_upd_prered_nop:
  assumes "distinct (items es)" "i < length es"
  assumes "item e = item (es!i)" "pointer e = PreRed p ps" "\<nexists>p ps. pointer (es!i) = PreRed p ps"
  shows "bin_upd e es = es"
  using assms
  by (induction es arbitrary: e i) (auto simp: less_Suc_eq_0_disj items_def split: entry.splits pointer.splits)

lemma bin_upd_prered_upd:
  assumes "distinct (items es)" "i < length es"
  assumes "item e = item (es!i)" "pointer e = PreRed p rs" "pointer (es!i) = PreRed p' rs'" "bin_upd e es = es'"
  shows "pointer (es'!i) = PreRed p' (p#rs@rs') \<and> (\<forall>j < length es'. i\<noteq>j \<longrightarrow> es'!j = es!j) \<and> length (bin_upd e es) = length es"
  using assms
proof (induction es arbitrary: e i es')
  case (Cons e' es)
  show ?case
  proof cases
    assume *: "item e = item e'"
    show ?thesis
    proof (cases "\<exists>x xp xs y yp ys. e = Entry x (PreRed xp xs) \<and> e' = Entry y (PreRed yp ys)")
      case True
      then obtain x xp xs y yp ys where ee': "e = Entry x (PreRed xp xs)" "e' = Entry y (PreRed yp ys)" "x = y"
        using * by auto
      have simp: "bin_upd e (e' # es') = Entry x (PreRed yp (xp # xs @ ys)) # es'"
        using True ee' by simp
      show ?thesis
        using Cons simp ee' apply (auto simp: items_def)
        using less_Suc_eq_0_disj by fastforce+
    next
      case False
      hence "bin_upd e (e' # es') = e' # es'"
        using * by (auto split: pointer.splits entry.splits)
      thus ?thesis
        using False * Cons.prems(1,2,3,4,5) by (auto simp: less_Suc_eq_0_disj items_def split: entry.splits)
    qed
  next
    assume *: "item e \<noteq> item e'"
    have simp: "bin_upd e (e' # es) = e' # bin_upd e es"
      using * by (auto split: pointer.splits entry.splits)
    have 0: "distinct (items es)"
      using Cons.prems(1) unfolding items_def by simp
    have 1: "i-1 < length es"
      using Cons.prems(2,3) * by (metis One_nat_def leI less_diff_conv2 less_one list.size(4) nth_Cons_0)
    have 2: "item e = item (es!(i-1))"
      using Cons.prems(3) * by (metis nth_Cons')
    have 3: "pointer e = PreRed p rs"
      using Cons.prems(4) by simp
    have 4: "pointer (es!(i-1)) = PreRed p' rs' "
      using Cons.prems(3,5) * by (metis nth_Cons')
    have "pointer (bin_upd e es!(i-1)) = PreRed p' (p # rs @ rs') \<and>
      (\<forall>j < length (bin_upd e es). i-1 \<noteq> j \<longrightarrow> (bin_upd e es) ! j = es ! j)"
      using Cons.IH[OF 0 1 2 3 4] by blast
    hence "pointer ((e' # bin_upd e es) ! i) = PreRed p' (p # rs @ rs') \<and>
      (\<forall>j < length (e' # bin_upd e es). i \<noteq> j \<longrightarrow> (e' # bin_upd e es) ! j = (e' # es) ! j)"
      using * Cons.prems(2,3) less_Suc_eq_0_disj by auto
    moreover have "e' # bin_upd e es = es'"
      using Cons.prems(6) simp by auto
    ultimately show ?thesis
      by (metis 0 1 2 3 4 Cons.IH Cons.prems(6) length_Cons)
  qed
qed simp

lemma sound_ptrs_bin_upd:
  assumes "sound_ptrs \<omega> bs" "k < length bs" "es = bs!k" "distinct (items es)"
  assumes "sound_null_ptr e" "sound_pre_ptr \<omega> bs k e" "sound_prered_ptr bs k e"
  shows "sound_ptrs \<omega> (bs[k := bin_upd e es])"
  unfolding sound_ptrs_def
proof (standard, standard, standard)
  fix idx elem
  let ?bs = "bs[k := bin_upd e es]"
  assume a0: "idx < length ?bs"
  assume a1: "elem \<in> set (?bs ! idx)"
  show "sound_null_ptr elem \<and> sound_pre_ptr \<omega> ?bs idx elem \<and> sound_prered_ptr ?bs idx elem"
  proof cases
    assume a2: "idx = k"
    have "elem \<in> set es \<Longrightarrow> sound_pre_ptr \<omega> bs idx elem"
      using a0 a2 assms(1-3) sound_ptrs_def by blast
    hence pre_es: "elem \<in> set es \<Longrightarrow> sound_pre_ptr \<omega> ?bs idx elem"
      using a2 unfolding sound_pre_ptr_def by force
    have "elem = e \<Longrightarrow> sound_pre_ptr \<omega> bs idx elem"
      using a2 assms(6) by auto
    hence pre_e: "elem = e \<Longrightarrow> sound_pre_ptr \<omega> ?bs idx elem"
      using a2 unfolding sound_pre_ptr_def by force
    have "elem \<in> set es \<Longrightarrow> sound_prered_ptr bs idx elem"
      using a0 a2 assms(1-3) sound_ptrs_def by blast
    hence prered_es: "elem \<in> set es \<Longrightarrow> sound_prered_ptr (bs[k := bin_upd e es]) idx elem"
      using a2 assms(2,3) length_bin_upd nth_item_bin_upd unfolding sound_prered_ptr_def
      by (smt (verit, ccfv_SIG) dual_order.strict_trans1 nth_list_update)
    have "elem = e \<Longrightarrow> sound_prered_ptr bs idx elem"
      using a2 assms(7) by auto
    hence prered_e: "elem = e \<Longrightarrow> sound_prered_ptr ?bs idx elem"
      using a2 assms(2,3) length_bin_upd nth_item_bin_upd unfolding sound_prered_ptr_def
      by (smt (verit, best) dual_order.strict_trans1 nth_list_update)
    consider (A) "item e \<notin> set (items es)" |
      (B) "item e \<in> set (items es) \<and> (\<exists>pre. pointer e = Null \<or> pointer e = Pre pre)" |
      (C) "item e \<in> set (items es) \<and> \<not> (\<exists>pre. pointer e = Null \<or> pointer e = Pre pre)"
      by blast
    thus ?thesis
    proof cases
      case A
      hence "elem \<in> set (es @ [e])"
        using a1 a2 bin_upd_append assms(2) by force
      thus ?thesis
        using assms(1-3,5) pre_e pre_es prered_e prered_es sound_ptrs_def by auto
    next
      case B
      hence "elem \<in> set es"
        using a1 a2 bin_upd_null_pre assms(2) by force
      thus ?thesis
        using assms(1-3) pre_es prered_es sound_ptrs_def by blast
    next
      case C
      then obtain i p ps where C: "i < length es \<and> item e = item (es!i) \<and> pointer e = PreRed p ps"
        by (metis assms(4) distinct_Ex1 items_def length_map nth_map pointer.exhaust)
      show ?thesis
      proof cases
        assume "\<nexists>p' ps'. pointer (es!i) = PreRed p' ps'"
        hence C: "elem \<in> set es"
          using a1 a2 C bin_upd_prered_nop assms(2,4) by (metis nth_list_update_eq)
        thus ?thesis
          using assms(1-3) sound_ptrs_def pre_es prered_es by blast
      next
        assume "\<not> (\<nexists>p' ps'. pointer (es!i) = PreRed p' ps')"
        then obtain p' ps' where D: "pointer (es!i) = PreRed p' ps'"
          by blast
        hence 0: "pointer (bin_upd e es!i) = PreRed p' (p#ps@ps') \<and> (\<forall>j < length (bin_upd e es). i\<noteq>j \<longrightarrow> bin_upd e es!j = es!j)"
          using C assms(4) bin_upd_prered_upd by blast
        obtain j where 1: "j < length es \<and> elem = bin_upd e es!j"
          using a1 a2 assms(2) C items_def bin_eq_items_bin_upd by (metis in_set_conv_nth length_map nth_list_update_eq nth_map)
        show ?thesis
        proof cases
          assume a3: "i=j"
          hence a3: "pointer elem = PreRed p' (p#ps@ps')"
            using 0 1 by blast
          have "sound_null_ptr elem"
            using a3 unfolding sound_null_ptr_def by simp
          moreover have "sound_pre_ptr \<omega> ?bs idx elem"
            using a3 unfolding sound_pre_ptr_def by simp
          moreover have "sound_prered_ptr ?bs idx elem"
            unfolding sound_prered_ptr_def
          proof (standard, standard, standard, standard, standard, standard)
            fix P PS k' pre red
            assume a4: "pointer elem = PreRed P PS \<and> (k', pre, red) \<in> set (P#PS)"
            show "k' < idx \<and> pre < length (bs[k := bin_upd e es]!k') \<and> red < length (bs[k := bin_upd e es]!idx) \<and>
              completes idx (item (bs[k := bin_upd e es]!k'!pre)) (item elem) (item (bs[k := bin_upd e es]!idx!red))"
            proof cases
              assume a5: "(k', pre, red) \<in> set (p#ps)"
              show ?thesis
                using 0 1 C a2 a4 a5 prered_es assms(2,3,7) sound_prered_ptr_def length_bin_upd nth_item_bin_upd
                by (smt (verit) dual_order.strict_trans1 nth_list_update_eq nth_list_update_neq nth_mem)
            next
              assume a5: "(k', pre, red) \<notin> set (p#ps)"
              hence a5: "(k', pre, red) \<in> set (p'#ps')"
                using a3 a4 by auto
              have "k' < idx \<and> pre < length (bs!k') \<and> red < length (bs!idx) \<and>
                completes idx (item (bs!k'!pre)) (item e) (item (bs!idx!red))"
                using assms(1-3) C D a2 a5 unfolding sound_ptrs_def sound_prered_ptr_def by (metis nth_mem)
              thus ?thesis
                using 0 1 C a4 assms(2,3) length_bin_upd nth_item_bin_upd prered_es sound_prered_ptr_def
                by (smt (verit, best) dual_order.strict_trans1 nth_list_update_eq nth_list_update_neq nth_mem)
            qed
          qed
          ultimately show ?thesis
            by blast
        next
          assume a3: "i\<noteq>j"
          hence "elem \<in> set es"
            using 0 1 by (metis length_bin_upd nth_mem order_less_le_trans)
          thus ?thesis
            using assms(1-3) pre_es prered_es sound_ptrs_def by blast
        qed
      qed
    qed
  next
    assume a2: "idx \<noteq> k"
    have null: "sound_null_ptr elem"
      using a0 a1 a2 assms(1) sound_ptrs_def by auto
    have "sound_pre_ptr \<omega> bs idx elem"
      using a0 a1 a2 assms(1,2) unfolding sound_ptrs_def by simp
    hence pre: "sound_pre_ptr \<omega> ?bs idx elem"
      using assms(2,3) length_bin_upd nth_item_bin_upd unfolding sound_pre_ptr_def
      using dual_order.strict_trans1 nth_list_update by fastforce
    have "sound_prered_ptr bs idx elem"
      using a0 a1 a2 assms(1,2) unfolding sound_ptrs_def by simp
    hence prered: "sound_prered_ptr ?bs idx elem"
      using assms(2,3) length_bin_upd nth_item_bin_upd unfolding sound_prered_ptr_def
      by (smt (verit, best) dual_order.strict_trans1 nth_list_update)
    show ?thesis
      using null pre prered by blast
  qed
qed

lemma mono_red_ptr_bin_upd:
  assumes "mono_red_ptr bs" "k < length bs" "es = bs!k" "distinct (items es)"
  assumes "\<forall>k' pre red ps. pointer e = PreRed (k', pre, red) ps \<longrightarrow> red < length es"
  shows "mono_red_ptr (bs[k := bin_upd e es])"
  unfolding mono_red_ptr_def
proof (standard, standard)
  fix idx
  let ?bs = "bs[k := bin_upd e es]"
  assume a0: "idx < length ?bs"
  show "\<forall>i < length (?bs!idx). \<forall>k' pre red ps. pointer (?bs!idx!i) = PreRed (k', pre, red) ps \<longrightarrow> red < i"
  proof cases
    assume a1: "idx=k"
    consider (A) "item e \<notin> set (items es)" |
      (B) "item e \<in> set (items es) \<and> (\<exists>pre. pointer e = Null \<or> pointer e = Pre pre)" |
      (C) "item e \<in> set (items es) \<and> \<not> (\<exists>pre. pointer e = Null \<or> pointer e = Pre pre)"
      by blast
    thus ?thesis
    proof cases
      case A
      hence "bin_upd e es = es @ [e]"
        using bin_upd_append by blast
      thus ?thesis
        using a1 assms(1-3,5) mono_red_ptr_def
        by (metis length_append_singleton less_antisym nth_append nth_append_length nth_list_update_eq)
    next
      case B
      hence "bin_upd e es = es"
        using bin_upd_null_pre by blast
      thus ?thesis
        using a1 assms(1-3) mono_red_ptr_def by force
    next
      case C
      then obtain i p ps where C: "i < length es" "item e = item (es!i)" "pointer e = PreRed p ps"
        by (metis in_set_conv_nth items_def length_map nth_map pointer.exhaust)
      show ?thesis
      proof cases
        assume "\<nexists>p' ps'. pointer (es!i) = PreRed p' ps'"
        hence "bin_upd e es = es"
          using bin_upd_prered_nop C assms(4) by blast
        thus ?thesis
          using a1 assms(1-3) mono_red_ptr_def by (metis nth_list_update_eq)
      next
        assume "\<not> (\<nexists>p' ps'. pointer (es!i) = PreRed p' ps')"
        then obtain p' ps' where D: "pointer (es!i) = PreRed p' ps'"
          by blast
        have 0: "pointer (bin_upd e es!i) = PreRed p' (p#ps@ps') \<and>
          (\<forall>j < length (bin_upd e es). i \<noteq> j \<longrightarrow> bin_upd e es!j = es!j) \<and>
          length (bin_upd e es) = length es"
          using C D assms(4) bin_upd_prered_upd by blast
        show ?thesis
        proof (standard, standard, standard, standard, standard, standard, standard)
          fix j k' pre red PS
          assume a2: "j < length (?bs!idx)"
          assume a3: "pointer (?bs!idx!j) = PreRed (k', pre, red) PS"
          have 1: "?bs!idx = bin_upd e es"
            by (simp add: a1 assms(2))
          show "red < j"
          proof cases
            assume a4: "i=j"
            show ?thesis
              using 0 1 C(1) D a3 a4 assms(1-3) unfolding mono_red_ptr_def by (metis pointer.inject(2))
          next
            assume a4: "i\<noteq>j"
            thus ?thesis
              using 0 1 a2 a3 assms(1) assms(2) assms(3) mono_red_ptr_def by force
          qed
        qed
      qed
    qed
  next
    assume a1: "idx\<noteq>k"
    show ?thesis
      using a0 a1 assms(1) mono_red_ptr_def by fastforce
  qed
qed

lemma sound_mono_ptrs_bin_upds:
  assumes "sound_ptrs \<omega> bs" "mono_red_ptr bs" "k < length bs" "b = bs!k" "distinct (items b)" "distinct (items es)"
  assumes "\<forall>e \<in> set es. sound_null_ptr e \<and> sound_pre_ptr \<omega> bs k e \<and> sound_prered_ptr bs k e"
  assumes "\<forall>e \<in> set es. \<forall>k' pre red ps. pointer e = PreRed (k', pre, red) ps \<longrightarrow> red < length b"
  shows "sound_ptrs \<omega> (bs[k := bin_upds es b]) \<and> mono_red_ptr (bs[k := bin_upds es b])"
  using assms
proof (induction es arbitrary: b bs)
  case (Cons e es)
  let ?bs = "bs[k := bin_upd e b]"
  have 0: "sound_ptrs \<omega> ?bs"
    using sound_ptrs_bin_upd Cons.prems(1,3-5,7) by (metis list.set_intros(1))
  have 1: "mono_red_ptr ?bs"
    using mono_red_ptr_bin_upd Cons.prems(2-5,8) by auto
  have 2: "k < length ?bs"
    using Cons.prems(3) by simp
  have 3: "bin_upd e b = ?bs!k"
    using Cons.prems(3) by simp
  have 4: "\<forall>e' \<in> set es. sound_null_ptr e' \<and> sound_pre_ptr \<omega> ?bs k e' \<and> sound_prered_ptr ?bs k e'"
    using Cons.prems(3,4,7) length_bin_upd nth_item_bin_upd sound_pre_ptr_def sound_prered_ptr_def
    by (smt (verit, ccfv_threshold) list.set_intros(2) nth_list_update order_less_le_trans)
  have 5: "\<forall>e' \<in> set es. \<forall>k' pre red ps. pointer e' = PreRed (k', pre, red) ps \<longrightarrow> red < length (bin_upd e b)"
    by (meson Cons.prems(8) length_bin_upd order_less_le_trans set_subset_Cons subsetD)
  have "sound_ptrs \<omega> ((bs[k := bin_upd e b])[k := bin_upds es (bin_upd e b)]) \<and>
    mono_red_ptr (bs[k := bin_upd e b, k := bin_upds es (bin_upd e b)])"
    using Cons.IH[OF 0 1 2 3 _ _ 4 5] distinct_bin_upd Cons.prems(4,5,6) items_def by (metis distinct.simps(2) list.simps(9))
  thus ?case
    by simp
qed simp

lemma sound_mono_ptrs_Earley\<^sub>L_bin':
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "sound_ptrs \<omega> bs" "\<forall>x \<in> bins bs. sound_item \<G> \<omega> x"
  assumes "mono_red_ptr bs"
  assumes "nonempty_derives \<G>" "wf_\<G> \<G>"
  shows "sound_ptrs \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> bs i) \<and> mono_red_ptr (Earley\<^sub>L_bin' k \<G> \<omega> bs i)"
  using assms
proof (induction i rule: Earley\<^sub>L_bin'_induct[OF assms(1), case_names Base Complete\<^sub>F Scan\<^sub>F Pass Predict\<^sub>F])
  case (Complete\<^sub>F k \<G> \<omega> bs i x)
  let ?bs' = "bins_upd bs k (Complete\<^sub>L k x bs i)"
  have x: "x \<in> set (items (bs ! k))"
    using Complete\<^sub>F.hyps(1,2) by force
  hence "\<forall>x \<in> set (items (Complete\<^sub>L k x bs i)). sound_item \<G> \<omega> x"
    using sound_Complete\<^sub>L Complete\<^sub>F.hyps(3) Complete\<^sub>F.prems wf_earley_input_elim wf_bins_impl_wf_items x
    by (metis dual_order.refl)
  hence sound: "\<forall>x \<in> bins ?bs'. sound_item \<G> \<omega> x"
    by (metis Complete\<^sub>F.prems(1,3) UnE bins_bins_upd wf_earley_input_elim)
  have 0: "k < length bs"
    using Complete\<^sub>F.prems(1) wf_earley_input_elim by auto
  have 1: "\<forall>e \<in> set (Complete\<^sub>L k x bs i). sound_null_ptr e"
    unfolding Complete\<^sub>L_def sound_null_ptr_def by auto
  have 2: "\<forall>e \<in> set (Complete\<^sub>L k x bs i). sound_pre_ptr \<omega> bs k e"
    unfolding Complete\<^sub>L_def sound_pre_ptr_def by auto
  {
    fix e
    assume a0: "e \<in> set (Complete\<^sub>L k x bs i)"
    fix p ps k' pre red
    assume a1: "pointer e = PreRed p ps" "(k', pre, red) \<in> set (p#ps)"
    have "k' = item_origin x"
      using a0 a1 unfolding Complete\<^sub>L_def by auto
    moreover have "wf_item \<G> \<omega> x" "item_end x = k"
      using Complete\<^sub>F.prems(1) x wf_earley_input_elim wf_bins_kth_bin by blast+
    ultimately have 0: "k' \<le> k"
      using wf_item_def by blast
    have 1: "k' \<noteq> k"
    proof (rule ccontr)
      assume "\<not> k' \<noteq> k"
      have "sound_item \<G> \<omega> x"
        using Complete\<^sub>F.prems(1,3) x kth_bin_sub_bins wf_earley_input_elim by (metis subset_eq)
      moreover have "is_complete x"
        using Complete\<^sub>F.hyps(3) by (auto simp: next_symbol_def split: if_splits)
      moreover have "item_origin x = k"
        using \<open>\<not> k' \<noteq> k\<close> \<open>k' = item_origin x\<close> by auto
      ultimately show False
        using impossible_complete_item Complete\<^sub>F.prems(1,5) wf_earley_input_elim \<open>item_end x = k\<close> \<open>wf_item \<G> \<omega> x\<close> by blast
    qed
    have 2: "pre < length (bs!k')"
      using a0 a1 index_filter_with_index_lt_length unfolding Complete\<^sub>L_def by (auto simp: items_def; fastforce)
    have 3: "red < i+1"
      using a0 a1 unfolding Complete\<^sub>L_def by auto

    have "item e = inc_item (item (bs!k'!pre)) k"
      using a0 a1 0 2 Complete\<^sub>F.hyps(1,2,3) Complete\<^sub>F.prems(1) \<open>k' = item_origin x\<close> unfolding Complete\<^sub>L_def
      by (auto simp: items_def, metis filter_with_index_nth nth_map)
    moreover have "is_complete (item (bs!k!red))"
      using a0 a1 0 2 Complete\<^sub>F.hyps(1,2,3) Complete\<^sub>F.prems(1) \<open>k' = item_origin x\<close> unfolding Complete\<^sub>L_def
      by (auto simp: next_symbol_def items_def split: if_splits)
    moreover have "item_origin (item (bs!k!red)) = item_end (item (bs!k'!pre))"
      using a0 a1 0 2 Complete\<^sub>F.hyps(1,2,3) Complete\<^sub>F.prems(1) \<open>k' = item_origin x\<close> unfolding Complete\<^sub>L_def
      apply (clarsimp simp: items_def)
      by (metis dual_order.strict_trans index_filter_with_index_lt_length items_def le_neq_implies_less nth_map nth_mem wf_bins_kth_bin wf_earley_input_elim)
    moreover have "(\<exists>N. next_symbol (item (bs ! k' ! pre)) = Some N \<and> N = item_rule_head (item (bs ! k ! red)))"
      using a0 a1 0 2 Complete\<^sub>F.hyps(1,2,3) Complete\<^sub>F.prems(1) \<open>k' = item_origin x\<close> unfolding Complete\<^sub>L_def
      by (auto simp: items_def, metis (mono_tags, lifting) filter_with_index_P filter_with_index_nth nth_map)
    ultimately have 4: "completes k (item (bs!k'!pre)) (item e) (item (bs!k!red))"
      unfolding completes_def by blast
    have "k' < k" "pre < length (bs!k')" "red < i+1" "completes k (item (bs!k'!pre)) (item e) (item (bs!k!red))"
      using 0 1 2 3 4 by simp_all
  }
  hence "\<forall>e \<in> set (Complete\<^sub>L k x bs i). \<forall>p ps k' pre red. pointer e = PreRed p ps \<and> (k', pre, red) \<in> set (p#ps) \<longrightarrow>
    k' < k \<and> pre < length (bs!k') \<and> red < i+1 \<and> completes k (item (bs!k'!pre)) (item e) (item (bs!k!red))"
    by force
  hence 3: "\<forall>e \<in> set (Complete\<^sub>L k x bs i). sound_prered_ptr bs k e"
    unfolding sound_prered_ptr_def using Complete\<^sub>F.hyps(1) items_def by (smt (verit) discrete dual_order.strict_trans1 leI length_map)
  have 4: "distinct (items (Complete\<^sub>L k x bs i))"
    using distinct_Complete\<^sub>L x Complete\<^sub>F.prems(1) wf_earley_input_elim wf_bin_def wf_bin_items_def wf_bins_def wf_item_def
    by (metis order_le_less_trans)
  have "sound_ptrs \<omega> ?bs' \<and> mono_red_ptr ?bs'"
    using sound_mono_ptrs_bin_upds[OF Complete\<^sub>F.prems(2) Complete\<^sub>F.prems(4) 0] 1 2 3 4 sound_prered_ptr_def
      Complete\<^sub>F.prems(1) bins_upd_def wf_earley_input_elim wf_bin_def wf_bins_def
    by (smt (verit, ccfv_SIG) list.set_intros(1))
  moreover have "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Complete\<^sub>F.hyps Complete\<^sub>F.prems(1) wf_earley_input_Complete\<^sub>L by blast
  ultimately have "sound_ptrs \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)) \<and> mono_red_ptr (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1))"
    using Complete\<^sub>F.IH Complete\<^sub>F.prems(4-6) sound by blast
  thus ?case
    using Complete\<^sub>F.hyps by simp
next
  case (Scan\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "bins_upd bs (k+1) (Scan\<^sub>L k \<omega> a x i)"
  have "x \<in> set (items (bs ! k))"
    using Scan\<^sub>F.hyps(1,2) by force
  hence "\<forall>x \<in> set (items (Scan\<^sub>L k \<omega> a x i)). sound_item \<G> \<omega> x"
    using sound_Scan\<^sub>L Scan\<^sub>F.hyps(3,5) Scan\<^sub>F.prems(1,2,3) wf_earley_input_elim wf_bins_impl_wf_items wf_bins_impl_wf_items by fast
  hence sound: "\<forall>x \<in> bins ?bs'. sound_item \<G> \<omega> x"
    using Scan\<^sub>F.hyps(5) Scan\<^sub>F.prems(1,3) bins_bins_upd wf_earley_input_elim
    by (metis UnE add_less_cancel_right)
  have 0: "k+1 < length bs"
    using Scan\<^sub>F.hyps(5) Scan\<^sub>F.prems(1) wf_earley_input_elim by force
  have 1: "\<forall>e \<in> set (Scan\<^sub>L k \<omega> a x i). sound_null_ptr e"
    unfolding Scan\<^sub>L_def sound_null_ptr_def by auto
  have 2: "\<forall>e \<in> set (Scan\<^sub>L k \<omega> a x i). sound_pre_ptr \<omega> bs (k+1) e"
    using Scan\<^sub>F.hyps(1,2,3) unfolding sound_pre_ptr_def Scan\<^sub>L_def scans_def items_def by auto
  have 3: "\<forall>e \<in> set (Scan\<^sub>L k \<omega> a x i). sound_prered_ptr bs (k+1) e"
    unfolding Scan\<^sub>L_def sound_prered_ptr_def by simp
  have 4: "distinct (items (Scan\<^sub>L k \<omega> a x i))"
    using distinct_Scan\<^sub>L by fast
  have "sound_ptrs \<omega> ?bs' \<and> mono_red_ptr ?bs'"
    using sound_mono_ptrs_bin_upds[OF Scan\<^sub>F.prems(2) Scan\<^sub>F.prems(4) 0] 0 1 2 3 4 sound_prered_ptr_def
      Scan\<^sub>F.prems(1) bins_upd_def wf_earley_input_elim wf_bin_def wf_bins_def
    by (smt (verit, ccfv_threshold) list.set_intros(1))
  moreover have "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Scan\<^sub>F.hyps Scan\<^sub>F.prems(1) wf_earley_input_Scan\<^sub>L by metis
  ultimately have "sound_ptrs \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)) \<and> mono_red_ptr (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1))"
    using Scan\<^sub>F.IH Scan\<^sub>F.prems(4-6) sound by blast
  thus ?case
    using Scan\<^sub>F.hyps by simp
next
  case (Predict\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "bins_upd bs k (Predict\<^sub>L k \<G> a)"
  have "x \<in> set (items (bs ! k))"
    using Predict\<^sub>F.hyps(1,2) by force
  hence "\<forall>x \<in> set (items(Predict\<^sub>L k \<G> a)). sound_item \<G> \<omega> x"
    using sound_Predict\<^sub>L Predict\<^sub>F.hyps(3) Predict\<^sub>F.prems wf_earley_input_elim wf_bins_impl_wf_items by fast
  hence sound: "\<forall>x \<in> bins ?bs'. sound_item \<G> \<omega> x"
    using Predict\<^sub>F.prems(1,3) UnE bins_bins_upd wf_earley_input_elim by metis
  have 0: "k < length bs"
    using Predict\<^sub>F.prems(1) wf_earley_input_elim by force
  have 1: "\<forall>e \<in> set (Predict\<^sub>L k \<G> a). sound_null_ptr e"
    unfolding sound_null_ptr_def Predict\<^sub>L_def predicts_def by (auto simp: init_item_def)
  have 2: "\<forall>e \<in> set (Predict\<^sub>L k \<G> a). sound_pre_ptr \<omega> bs k e"
    unfolding sound_pre_ptr_def Predict\<^sub>L_def by simp
  have 3: "\<forall>e \<in> set (Predict\<^sub>L k \<G> a). sound_prered_ptr bs k e"
    unfolding sound_prered_ptr_def Predict\<^sub>L_def by simp
  have 4: "distinct (items (Predict\<^sub>L k \<G> a))"
    using Predict\<^sub>F.prems(6) distinct_Predict\<^sub>L by fast
  have "sound_ptrs \<omega> ?bs' \<and> mono_red_ptr ?bs'"
    using sound_mono_ptrs_bin_upds[OF Predict\<^sub>F.prems(2) Predict\<^sub>F.prems(4) 0] 0 1 2 3 4 sound_prered_ptr_def
      Predict\<^sub>F.prems(1) bins_upd_def wf_earley_input_elim wf_bin_def wf_bins_def
    by (smt (verit, ccfv_threshold) list.set_intros(1))
  moreover have "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Predict\<^sub>F.hyps Predict\<^sub>F.prems(1) wf_earley_input_Predict\<^sub>L by metis
  ultimately have "sound_ptrs \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)) \<and> mono_red_ptr (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1))"
    using Predict\<^sub>F.IH Predict\<^sub>F.prems(4-6) sound by blast
  thus ?case
    using Predict\<^sub>F.hyps by simp
qed simp_all

lemma sound_mono_ptrs_Earley\<^sub>L_bin:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "sound_ptrs \<omega> bs" "\<forall>x \<in> bins bs. sound_item \<G> \<omega> x"
  assumes "mono_red_ptr bs"
  assumes "nonempty_derives \<G>" "wf_\<G> \<G>"
  shows "sound_ptrs \<omega> (Earley\<^sub>L_bin k \<G> \<omega> bs) \<and> mono_red_ptr (Earley\<^sub>L_bin k \<G> \<omega> bs)"
  using assms sound_mono_ptrs_Earley\<^sub>L_bin' Earley\<^sub>L_bin_def by metis

lemma sound_ptrs_Init\<^sub>L:
  "sound_ptrs \<omega> (Init\<^sub>L \<G> \<omega>)"
  unfolding sound_ptrs_def sound_null_ptr_def sound_pre_ptr_def sound_prered_ptr_def
    predicts_def scans_def completes_def Init\<^sub>L_def
  by (auto simp: init_item_def less_Suc_eq_0_disj)

lemma mono_red_ptr_Init\<^sub>L:
  "mono_red_ptr (Init\<^sub>L \<G> \<omega>)"
  unfolding mono_red_ptr_def Init\<^sub>L_def
  by (auto simp: init_item_def less_Suc_eq_0_disj)

lemma sound_mono_ptrs_Earley\<^sub>L_bins:
  assumes "k \<le> length \<omega>" "wf_\<G> \<G>" "nonempty_derives \<G>" "wf_\<G> \<G>"
  shows "sound_ptrs \<omega> (Earley\<^sub>L_bins k \<G> \<omega>) \<and> mono_red_ptr (Earley\<^sub>L_bins k \<G> \<omega>)"
  using assms
proof (induction k)
  case 0
  have "(0, \<G>, \<omega>, (Init\<^sub>L \<G> \<omega>)) \<in> wf_earley_input"
    using assms(2) wf_earley_input_Init\<^sub>L by blast
  moreover have "\<forall>x \<in> bins (Init\<^sub>L \<G> \<omega>). sound_item \<G> \<omega> x"
    by (metis Init\<^sub>L_eq_Init\<^sub>F Init\<^sub>F_sub_Earley sound_Earley subsetD wf_Earley)
  ultimately show ?case
    using sound_mono_ptrs_Earley\<^sub>L_bin sound_ptrs_Init\<^sub>L mono_red_ptr_Init\<^sub>L "0.prems"(2,3) by fastforce
next
  case (Suc k)
  have "(Suc k, \<G>, \<omega>, Earley\<^sub>L_bins k \<G> \<omega>) \<in> wf_earley_input"
    by (simp add: Suc.prems(1) Suc_leD assms(2) wf_earley_input_intro)
  moreover have "sound_ptrs \<omega> (Earley\<^sub>L_bins k \<G> \<omega>)"
    using Suc by simp
  moreover have "\<forall>x \<in> bins (Earley\<^sub>L_bins k \<G> \<omega>). sound_item \<G> \<omega> x"
    by (meson Suc.prems(1) Suc_leD Earley\<^sub>L_bins_sub_Earley\<^sub>F_bins Earley\<^sub>F_bins_sub_Earley assms(2)
        sound_Earley subsetD wf_bins_Earley\<^sub>L_bins wf_bins_impl_wf_items)
  ultimately show ?case
    using Suc.prems(1,3,4) sound_mono_ptrs_Earley\<^sub>L_bin Suc.IH by fastforce
qed

lemma sound_mono_ptrs_Earley\<^sub>L:
  assumes "wf_\<G> \<G>" "nonempty_derives \<G>"
  shows "sound_ptrs \<omega> (Earley\<^sub>L \<G> \<omega>) \<and> mono_red_ptr (Earley\<^sub>L \<G> \<omega>)"
  using assms sound_mono_ptrs_Earley\<^sub>L_bins Earley\<^sub>L_def by (metis dual_order.refl)


subsection \<open>Common Definitions\<close>

datatype 'a tree =
  Leaf 'a
  | Branch 'a "'a tree list"

fun yield_tree :: "'a tree \<Rightarrow> 'a sentence" where
  "yield_tree (Leaf a) = [a]"
| "yield_tree (Branch _ ts) = concat (map yield_tree ts)"

fun root_tree :: "'a tree \<Rightarrow> 'a" where
  "root_tree (Leaf a) = a"
| "root_tree (Branch N _) = N"

fun wf_rule_tree :: "'a cfg \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "wf_rule_tree _ (Leaf a) \<longleftrightarrow> True"
| "wf_rule_tree \<G> (Branch N ts) \<longleftrightarrow> (
    (\<exists>r \<in> set (\<RR> \<G>). N = rule_head r \<and> map root_tree ts = rule_body r) \<and>
    (\<forall>t \<in> set ts. wf_rule_tree \<G> t))"

fun wf_item_tree :: "'a cfg \<Rightarrow> 'a item \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "wf_item_tree \<G> _ (Leaf a) \<longleftrightarrow> True"
| "wf_item_tree \<G> x (Branch N ts) \<longleftrightarrow> (
    N = item_rule_head x \<and> map root_tree ts = take (item_dot x) (item_rule_body x) \<and>
    (\<forall>t \<in> set ts. wf_rule_tree \<G> t))"

definition wf_yield_tree :: "'a sentence \<Rightarrow> 'a item \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "wf_yield_tree \<omega> x t \<longleftrightarrow> yield_tree t = slice (item_origin x) (item_end x) \<omega>"

datatype 'a forest =
  FLeaf 'a
  | FBranch 'a "'a forest list list"

fun combinations :: "'a list list \<Rightarrow> 'a list list" where
  "combinations [] = [[]]"
| "combinations (xs#xss) = [ x#cs . x <- xs, cs <- combinations xss ]"

fun trees :: "'a forest \<Rightarrow> 'a tree list" where
  "trees (FLeaf a) = [Leaf a]"
| "trees (FBranch N fss) = (
    let tss = (map (\<lambda>fs. concat (map (\<lambda>f. trees f) fs)) fss) in
    map (\<lambda>ts. Branch N ts) (combinations tss)
  )"

lemma list_comp_flatten:
  "[ f xs . xs <- [ g xs ys . xs <- as, ys <- bs ] ] = [ f (g xs ys) . xs <- as, ys <- bs ]"
  by (induction as) auto

lemma list_comp_flatten_Cons:
  "[ x#xs . x <- as, xs <- [ xs @ ys. xs <- bs, ys <- cs ] ] = [ x#xs@ys. x <- as, xs <- bs, ys <- cs ]"
  by (induction as) (auto simp: list_comp_flatten)

lemma list_comp_flatten_append:
  "[ xs@ys . xs <- [ x#xs . x <- as, xs <- bs ], ys <- cs ] = [ x#xs@ys . x <- as, xs <- bs, ys <- cs ]"
  by (induction as) (auto simp: o_def, meson append_Cons map_eq_conv)

lemma combinations_append:
  "combinations (xss @ yss) = [ xs @ ys . xs <- combinations xss, ys <- combinations yss ]"
  by (induction xss) (auto simp: list_comp_flatten_Cons list_comp_flatten_append map_idI)

lemma trees_append:
  "trees (FBranch N (xss @ yss)) = (
    let xtss = (map (\<lambda>xs. concat (map (\<lambda>f. trees f) xs)) xss) in
    let ytss = (map (\<lambda>ys. concat (map (\<lambda>f. trees f) ys)) yss) in
    map (\<lambda>ts. Branch N ts) [ xs @ ys . xs <- combinations xtss, ys <- combinations ytss ])"
  using combinations_append by (metis map_append trees.simps(2))

lemma trees_append_singleton:
  "trees (FBranch N (xss @ [ys])) = (
    let xtss = (map (\<lambda>xs. concat (map (\<lambda>f. trees f) xs)) xss) in
    let ytss = [concat (map trees ys)] in
    map (\<lambda>ts. Branch N ts) [ xs @ ys . xs <- combinations xtss, ys <- combinations ytss ])"
  by (subst trees_append, simp)

lemma trees_append_single_singleton:
  "trees (FBranch N (xss @ [[y]])) = (
    let xtss = (map (\<lambda>xs. concat (map (\<lambda>f. trees f) xs)) xss) in
    map (\<lambda>ts. Branch N ts) [ xs @ ys . xs <- combinations xtss,  ys <- [ [t] . t <- trees y ] ])"
  by (subst trees_append_singleton, auto)


subsection \<open>foldl lemmas\<close>

lemma foldl_add_nth:
  "k < length xs \<Longrightarrow> foldl (+) z (map length (take k xs)) + length (xs!k) = foldl (+) z (map length (take (k+1) xs))"
proof (induction xs arbitrary: k z)
  case (Cons x xs)
  then show ?case
  proof (cases "k = 0")
    case False
    thus ?thesis
      using Cons by (auto simp add: take_Cons')
  qed simp
qed simp

lemma foldl_acc_mono:
  "a \<le> b \<Longrightarrow> foldl (+) a xs \<le> foldl (+) b xs" for a :: nat
  by (induction xs arbitrary: a b) auto

lemma foldl_ge_z_nth:
  "j < length xs \<Longrightarrow> z + length (xs!j) \<le> foldl (+) z (map length (take (j+1) xs))"
proof (induction xs arbitrary: j z)
  case (Cons x xs)
  show ?case
  proof (cases "j = 0")
    case False
    have "z + length ((x # xs) ! j) = z + length (xs!(j-1))"
      using False by simp
    also have "... \<le> foldl (+) z (map length (take (j-1+1) xs))"
      using Cons False by (metis add_diff_inverse_nat length_Cons less_one nat_add_left_cancel_less plus_1_eq_Suc)
    also have "... = foldl (+) z (map length (take j xs))"
      using False by simp
    also have "... \<le> foldl (+) (z + length x) (map length (take j xs))"
      using foldl_acc_mono by force
    also have "... = foldl (+) z (map length (take (j+1) (x#xs)))"
      by simp
    finally show ?thesis
      by blast
  qed simp
qed simp

lemma foldl_add_nth_ge:
  "i \<le> j \<Longrightarrow> j < length xs \<Longrightarrow> foldl (+) z (map length (take i xs)) + length (xs!j) \<le> foldl (+) z (map length (take (j+1) xs))"
proof (induction xs arbitrary: i j z)
  case (Cons x xs)
  show ?case
  proof (cases "i = 0")
    case True
    have "foldl (+) z (map length (take i (x # xs))) + length ((x # xs) ! j) = z + length ((x # xs) ! j)"
      using True by simp
    also have "... \<le> foldl (+) z (map length (take (j+1) (x#xs)))"
      using foldl_ge_z_nth Cons.prems(2) by blast
    finally show ?thesis
      by blast
  next
    case False
    have "i-1 \<le> j-1"
      by (simp add: Cons.prems(1) diff_le_mono)
    have "j-1 < length xs"
      using Cons.prems(1,2) False by fastforce
    have "foldl (+) z (map length (take i (x # xs))) + length ((x # xs) ! j) =
      foldl (+) (z + length x) (map length (take (i-1) xs)) + length ((x#xs)!j)"
      using False by (simp add: take_Cons')
    also have "... = foldl (+) (z + length x) (map length (take (i-1) xs)) + length (xs!(j-1))"
      using Cons.prems(1) False by auto
    also have "... \<le> foldl (+) (z + length x) (map length (take (j-1+1) xs))"
      using Cons.IH \<open>i - 1 \<le> j - 1\<close> \<open>j - 1 < length xs\<close> by blast
    also have "... = foldl (+) (z + length x) (map length (take j xs))"
      using Cons.prems(1) False by fastforce
    also have "... = foldl (+) z (map length (take (j+1) (x#xs)))"
      by fastforce
    finally show ?thesis
      by blast
  qed
qed simp

lemma foldl_ge_acc:
  "foldl (+) z (map length xs) \<ge> z"
  by (induction xs arbitrary: z) (auto elim: add_leE)

lemma foldl_take_mono:
  "i \<le> j \<Longrightarrow> foldl (+) z (map length (take i xs)) \<le> foldl (+) z (map length (take j xs))"
proof (induction xs arbitrary: z i j)
  case (Cons x xs)
  show ?case
  proof (cases "i = 0")
    case True
    have "foldl (+) z (map length (take i (x # xs))) = z"
      using True by simp
    also have "... \<le> foldl (+) z (map length (take j (x # xs)))"
      by (simp add: foldl_ge_acc)
    ultimately show ?thesis
      by simp
  next
    case False
    then show ?thesis
      using Cons by (simp add: take_Cons')
  qed
qed simp


subsection \<open>Parse tree\<close>

partial_function (option) build_tree' :: "'a bins \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a tree option" where
  "build_tree' bs \<omega> k i = (
    let e = bs!k!i in (
    case pointer e of
      Null \<Rightarrow> Some (Branch (item_rule_head (item e)) []) \<comment>\<open>start building sub-tree\<close>
    | Pre pre \<Rightarrow> ( \<comment>\<open>add sub-tree starting from terminal\<close>
        do {
          t \<leftarrow> build_tree' bs \<omega> (k-1) pre;
          case t of
            Branch N ts \<Rightarrow> Some (Branch N (ts @ [Leaf (\<omega>!(k-1))]))
          | _ \<Rightarrow> undefined \<comment>\<open>impossible case\<close>
        })
    | PreRed (k', pre, red) _ \<Rightarrow> ( \<comment>\<open>add sub-tree starting from non-terminal\<close>
        do {
          t \<leftarrow> build_tree' bs \<omega> k' pre;
          case t of
            Branch N ts \<Rightarrow>
              do {
                t \<leftarrow> build_tree' bs \<omega> k red;
                Some (Branch N (ts @ [t]))
              }
          | _ \<Rightarrow> undefined \<comment>\<open>impossible case\<close>
        })
  ))"

declare build_tree'.simps [code]

definition build_tree :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins \<Rightarrow> 'a tree option" where
  "build_tree \<G> \<omega> bs = (
    let k = length bs - 1 in (
    case filter_with_index (\<lambda>x. is_finished \<G> \<omega> x) (items (bs!k)) of
      [] \<Rightarrow> None
    | (_, i)#_ \<Rightarrow> build_tree' bs \<omega> k i
  ))"

lemma build_tree'_simps[simp]:
  "e = bs!k!i \<Longrightarrow> pointer e = Null \<Longrightarrow> build_tree' bs \<omega> k i = Some (Branch (item_rule_head (item e)) [])"
  "e = bs!k!i \<Longrightarrow> pointer e = Pre pre \<Longrightarrow> build_tree' bs \<omega> (k-1) pre = None \<Longrightarrow>
   build_tree' bs \<omega> k i = None"
  "e = bs!k!i \<Longrightarrow> pointer e = Pre pre \<Longrightarrow> build_tree' bs \<omega> (k-1) pre = Some (Branch N ts) \<Longrightarrow>
   build_tree' bs \<omega> k i = Some (Branch N (ts @ [Leaf (\<omega>!(k-1))]))"
  "e = bs!k!i \<Longrightarrow> pointer e = Pre pre \<Longrightarrow> build_tree' bs \<omega> (k-1) pre = Some (Leaf a) \<Longrightarrow>
   build_tree' bs \<omega> k i = undefined"
  "e = bs!k!i \<Longrightarrow> pointer e = PreRed (k', pre, red) reds \<Longrightarrow> build_tree' bs \<omega> k' pre = None \<Longrightarrow>
   build_tree' bs \<omega> k i = None"
  "e = bs!k!i \<Longrightarrow> pointer e = PreRed (k', pre, red) reds \<Longrightarrow> build_tree' bs \<omega> k' pre = Some (Branch N ts) \<Longrightarrow>
   build_tree' bs \<omega> k red = None \<Longrightarrow> build_tree' bs \<omega> k i = None"
  "e = bs!k!i \<Longrightarrow> pointer e = PreRed (k', pre, red) reds \<Longrightarrow> build_tree' bs \<omega> k' pre = Some (Leaf a) \<Longrightarrow>
   build_tree' bs \<omega> k i = undefined"
  "e = bs!k!i \<Longrightarrow> pointer e = PreRed (k', pre, red) reds \<Longrightarrow> build_tree' bs \<omega> k' pre = Some (Branch N ts) \<Longrightarrow>
   build_tree' bs \<omega> k red = Some t \<Longrightarrow>
   build_tree' bs \<omega> k i = Some (Branch N (ts @ [t]))"
  by (subst build_tree'.simps, simp)+

definition wf_tree_input :: "('a bins \<times> 'a sentence \<times> nat \<times> nat) set" where
  "wf_tree_input = {
    (bs, \<omega>, k, i) | bs \<omega> k i.
      sound_ptrs \<omega> bs \<and>
      mono_red_ptr bs \<and>
      k < length bs \<and>
      i < length (bs!k)
  }"

fun build_tree'_measure :: "('a bins \<times> 'a sentence \<times> nat \<times> nat) \<Rightarrow> nat" where
  "build_tree'_measure (bs, \<omega>, k, i) = foldl (+) 0 (map length (take k bs)) + i"

lemma wf_tree_input_pre:
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  assumes "e = bs!k!i" "pointer e = Pre pre"
  shows "(bs, \<omega>, (k-1), pre) \<in> wf_tree_input"
  using assms unfolding wf_tree_input_def
  using less_imp_diff_less nth_mem by (fastforce simp: sound_ptrs_def sound_pre_ptr_def)

lemma wf_tree_input_prered_pre:
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  assumes "e = bs!k!i" "pointer e = PreRed (k', pre, red) ps"
  shows "(bs, \<omega>, k', pre) \<in> wf_tree_input"
  using assms unfolding wf_tree_input_def
  apply (auto simp: sound_ptrs_def sound_prered_ptr_def)
  apply metis+
  apply (metis dual_order.strict_trans nth_mem)
  by (metis nth_mem)

lemma wf_tree_input_prered_red:
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  assumes "e = bs!k!i" "pointer e = PreRed (k', pre, red) ps"
  shows "(bs, \<omega>, k, red) \<in> wf_tree_input"
  using assms unfolding wf_tree_input_def
  apply (auto simp add: sound_ptrs_def sound_prered_ptr_def)
  apply (metis nth_mem)+
  done

lemma build_tree'_induct:
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  assumes "\<And>bs \<omega> k i.
    (\<And>e pre. e = bs!k!i \<Longrightarrow> pointer e = Pre pre \<Longrightarrow> P bs \<omega> (k-1) pre) \<Longrightarrow>
    (\<And>e k' pre red ps. e = bs!k!i \<Longrightarrow> pointer e = PreRed (k', pre, red) ps \<Longrightarrow> P bs \<omega> k' pre) \<Longrightarrow>
    (\<And>e k' pre red ps. e = bs!k!i \<Longrightarrow> pointer e = PreRed (k', pre, red) ps \<Longrightarrow> P bs \<omega> k red) \<Longrightarrow>
    P bs \<omega> k i" 
  shows "P bs \<omega> k i"
  using assms(1)
proof (induction n\<equiv>"build_tree'_measure (bs, \<omega>, k, i)" arbitrary: k i rule: nat_less_induct)
  case 1
  obtain e where entry: "e = bs!k!i"
    by simp
  consider (Null) "pointer e = Null"
    | (Pre) "\<exists>pre. pointer e = Pre pre"
    | (PreRed) "\<exists>k' pre red reds. pointer e = PreRed (k', pre, red) reds"
    by (metis pointer.exhaust surj_pair)
  thus ?case
  proof cases
    case Null
    thus ?thesis
      using assms(2) entry by fastforce
  next
    case Pre
    then obtain pre where pre: "pointer e = Pre pre"
      by blast
    define n where n: "n = build_tree'_measure (bs, \<omega>, (k-1), pre)"
    have "0 < k" "pre < length (bs!(k-1))"
      using 1(2) entry pre unfolding wf_tree_input_def sound_ptrs_def sound_pre_ptr_def
      by (smt (verit) mem_Collect_eq nth_mem prod.inject)+
    have "k < length bs"
      using 1(2) unfolding wf_tree_input_def by blast+
    have "foldl (+) 0 (map length (take k bs)) + i - (foldl (+) 0 (map length (take (k-1) bs)) + pre) =
      foldl (+) 0 (map length (take (k-1) bs)) + length (bs!(k-1)) + i - (foldl (+) 0 (map length (take (k-1) bs)) + pre)"
      using foldl_add_nth[of \<open>k-1\<close> bs 0] by (simp add: \<open>0 < k\<close> \<open>k < length bs\<close> less_imp_diff_less)
    also have "... = length (bs!(k-1)) + i - pre"
      by simp
    also have "... > 0"
      using \<open>pre < length (bs!(k-1))\<close> by auto
    finally have "build_tree'_measure (bs, \<omega>, k, i) - build_tree'_measure (bs, \<omega>, (k-1), pre) > 0"
      by simp
    hence "P bs \<omega> (k-1) pre"
      using 1 n wf_tree_input_pre entry pre zero_less_diff by blast
    thus ?thesis
      using assms(2) entry pre pointer.distinct(5) pointer.inject(1) by presburger
  next
    case PreRed
    then obtain k' pre red ps where prered: "pointer e = PreRed (k', pre, red) ps"
      by blast
    have "k' < k" "pre < length (bs!k')"
      using 1(2) entry prered unfolding wf_tree_input_def sound_ptrs_def sound_prered_ptr_def
      apply simp_all
      apply (metis nth_mem)+
      done
    have "red < i"
      using 1(2) entry prered unfolding wf_tree_input_def mono_red_ptr_def by blast
    have "k < length bs" "i < length (bs!k)"
      using 1(2) unfolding wf_tree_input_def by blast+
    define n_pre where n_pre: "n_pre = build_tree'_measure (bs, \<omega>, k', pre)"
    have "0 < length (bs!k') + i - pre"
      by (simp add: \<open>pre < length (bs!k')\<close> add.commute trans_less_add2)
    also have "... = foldl (+) 0 (map length (take k' bs)) + length (bs!k') + i - (foldl (+) 0 (map length (take k' bs)) + pre)"
      by simp
    also have "... \<le> foldl (+) 0 (map length (take (k'+1) bs)) + i - (foldl (+) 0 (map length (take k' bs)) + pre)"
      using foldl_add_nth_ge[of k' k' bs 0] \<open>k < length bs\<close> \<open>k' < k\<close> by simp
    also have "... \<le> foldl (+) 0 (map length (take k bs)) + i - (foldl (+) 0 (map length (take k' bs)) + pre)"
      using foldl_take_mono by (metis Suc_eq_plus1 Suc_leI \<open>k' < k\<close> add.commute add_le_cancel_left diff_le_mono)
    finally have "build_tree'_measure (bs, \<omega>, k, i) - build_tree'_measure (bs, \<omega>, k', pre) > 0"
      by simp
    hence x: "P bs \<omega> k' pre"
      using 1(1) zero_less_diff by (metis "1.prems" entry prered wf_tree_input_prered_pre)
    define n_red where n_red: "n_red = build_tree'_measure (bs, \<omega>, k, red)"
    have "build_tree'_measure (bs, \<omega>, k, i) - build_tree'_measure (bs, \<omega>, k, red) > 0"
      using \<open>red < i\<close> by simp
    hence y: "P bs \<omega> k red"
      using "1.hyps" "1.prems" entry prered wf_tree_input_prered_red zero_less_diff by blast
    show ?thesis
      using assms(2) x y entry prered 
      by (smt (verit, best) Pair_inject filter_cong pointer.distinct(5) pointer.inject(2))
  qed
qed

lemma build_tree'_termination:
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  shows "\<exists>N ts. build_tree' bs \<omega> k i = Some (Branch N ts)"
proof -
  have "\<exists>N ts. build_tree' bs \<omega> k i = Some (Branch N ts)"
    apply (induction rule: build_tree'_induct[OF assms(1)])
    subgoal premises IH for bs \<omega> k i
    proof -
      define e where entry: "e = bs!k!i"
      consider (Null) "pointer e = Null"
        | (Pre) "\<exists>pre. pointer e = Pre pre"
        | (PreRed) "\<exists>k' pre red ps. pointer e = PreRed (k', pre, red) ps"
        by (metis pointer.exhaust surj_pair)
      thus ?thesis
      proof cases
        case Null
        thus ?thesis
          using build_tree'_simps(1) entry by simp
      next
        case Pre
        then obtain pre where pre: "pointer e = Pre pre"
          by blast
        obtain N ts where Nts: "build_tree' bs \<omega> (k-1) pre = Some (Branch N ts)"
          using IH(1) entry pre by blast
        have "build_tree' bs \<omega> k i = Some (Branch N (ts @ [Leaf (\<omega>!(k-1))]))"
          using build_tree'_simps(3) entry pre Nts by simp         
        thus ?thesis
          by simp
      next
        case PreRed
        then obtain k' pre red ps where prered: "pointer e = PreRed (k', pre, red) ps"
          by blast
        then obtain N ts where Nts: "build_tree' bs \<omega> k' pre = Some (Branch N ts)"
          using IH(2) entry prered by blast
        obtain t_red where t_red: "build_tree' bs \<omega> k red = Some t_red"
          using IH(3) entry prered Nts by (metis option.exhaust)
        have "build_tree' bs \<omega> k i = Some (Branch N (ts @ [t_red]))"
          using build_tree'_simps(8) entry prered Nts t_red by auto
        thus ?thesis
          by blast
      qed
    qed
    done
  thus ?thesis
    by blast
qed

lemma wf_item_tree_build_tree':
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  assumes "wf_bins \<G> \<omega> bs"
  assumes "k < length bs" "i < length (bs!k)"
  assumes "build_tree' bs \<omega> k i = Some t"
  shows "wf_item_tree \<G> (item (bs!k!i)) t"
proof -
  have "wf_item_tree \<G> (item (bs!k!i)) t"
    using assms
    apply (induction arbitrary: t rule: build_tree'_induct[OF assms(1)])
    subgoal premises prems for bs \<omega> k i t
    proof -
      define e where entry: "e = bs!k!i"
      consider (Null) "pointer e = Null"
        | (Pre) "\<exists>pre. pointer e = Pre pre"
        | (PreRed) "\<exists>k' pre red ps. pointer e = PreRed (k', pre, red) ps"
        by (metis pointer.exhaust surj_pair)
      thus ?thesis
      proof cases
        case Null
        hence "build_tree' bs \<omega> k i = Some (Branch (item_rule_head (item e)) [])"
          using entry by simp
        have simp: "t = Branch (item_rule_head (item e)) []"
          using build_tree'_simps(1) Null prems(8) entry by simp
        have "sound_ptrs \<omega> bs"
          using prems(4) unfolding wf_tree_input_def by blast
        hence "predicts (item e)"
          using Null prems(6,7) nth_mem entry unfolding sound_ptrs_def sound_null_ptr_def by blast
        hence "item_dot (item e) = 0"
          unfolding predicts_def by blast
        thus ?thesis
          using simp entry by simp
      next
        case Pre
        then obtain pre where pre: "pointer e = Pre pre"
          by blast
        obtain N ts where Nts: "build_tree' bs \<omega> (k-1) pre = Some (Branch N ts)"
          using build_tree'_termination entry pre prems(4) wf_tree_input_pre by blast
        have simp: "build_tree' bs \<omega> k i = Some (Branch N (ts @ [Leaf (\<omega>!(k-1))]))"
          using build_tree'_simps(3) entry pre Nts by simp
        have "sound_ptrs \<omega> bs"
          using prems(4) unfolding wf_tree_input_def by blast
        hence "pre < length (bs!(k-1))"
          using entry pre prems(6,7) unfolding sound_ptrs_def sound_pre_ptr_def by (metis nth_mem)
        moreover have "k-1 < length bs"
          by (simp add: prems(6) less_imp_diff_less)
        ultimately have IH: "wf_item_tree \<G> (item (bs!(k-1)!pre)) (Branch N ts)"
          using prems(1,2,4,5) entry pre Nts by (meson wf_tree_input_pre)
        have scans: "scans \<omega> k (item (bs!(k-1)!pre)) (item e)"
          using entry pre prems(6-7) \<open>sound_ptrs \<omega> bs\<close> unfolding sound_ptrs_def sound_pre_ptr_def by simp
        hence *: 
          "item_rule_head (item (bs!(k-1)!pre)) = item_rule_head (item e)"
          "item_rule_body (item (bs!(k-1)!pre)) = item_rule_body (item e)"
          "item_dot (item (bs!(k-1)!pre)) + 1 = item_dot (item e)"
          "next_symbol (item (bs!(k-1)!pre)) = Some (\<omega>!(k-1))"
          unfolding scans_def inc_item_def by (simp_all add: item_rule_head_def item_rule_body_def)
        have "map root_tree (ts @ [Leaf (\<omega>!(k-1))]) = map root_tree ts @ [\<omega>!(k-1)]"
          by simp
        also have "... = take (item_dot (item (bs!(k-1)!pre))) (item_rule_body (item (bs!(k-1)!pre))) @ [\<omega>!(k-1)]"
          using IH by simp
        also have "... = take (item_dot (item (bs!(k-1)!pre))) (item_rule_body (item e)) @ [\<omega>!(k-1)]"
          using *(2) by simp
        also have "... = take (item_dot (item e)) (item_rule_body (item e))"
          using *(2-4) by (auto simp: next_symbol_def is_complete_def split: if_splits; metis leI take_Suc_conv_app_nth)
        finally have "map root_tree (ts @ [Leaf (\<omega>!(k-1))]) = take (item_dot (item e)) (item_rule_body (item e))" .
        hence "wf_item_tree \<G> (item e) (Branch N (ts @ [Leaf (\<omega>!(k-1))]))"
          using IH *(1) by simp
        thus ?thesis
          using entry prems(8) simp by auto
      next
        case PreRed
        then obtain k' pre red ps where prered: "pointer e = PreRed (k', pre, red) ps"
          by blast
        obtain N ts where Nts: "build_tree' bs \<omega> k' pre = Some (Branch N ts)"
          using build_tree'_termination entry prems(4) prered wf_tree_input_prered_pre by blast
        obtain N_red ts_red where Nts_red: "build_tree' bs \<omega> k red = Some (Branch N_red ts_red)"
          using build_tree'_termination entry prems(4) prered wf_tree_input_prered_red by blast
        have simp: "build_tree' bs \<omega> k i = Some (Branch N (ts @ [Branch N_red ts_red]))"
          using build_tree'_simps(8) entry prered Nts Nts_red by auto
        have "sound_ptrs \<omega> bs"
          using prems(4) wf_tree_input_def by fastforce
        have bounds: "k' < k" "pre < length (bs!k')" "red < length (bs!k)"
          using prered entry prems(6,7) \<open>sound_ptrs \<omega> bs\<close>
          unfolding sound_prered_ptr_def sound_ptrs_def by fastforce+
        have completes: "completes k (item (bs!k'!pre)) (item e) (item (bs!k!red))"
          using prered entry prems(6,7) \<open>sound_ptrs \<omega> bs\<close>
          unfolding sound_ptrs_def sound_prered_ptr_def by fastforce
        have *: 
          "item_rule_head (item (bs!k'!pre)) = item_rule_head (item e)"
          "item_rule_body (item (bs!k'!pre)) = item_rule_body (item e)"
          "item_dot (item (bs!k'!pre)) + 1 = item_dot (item e)"
          "next_symbol (item (bs!k'!pre)) = Some (item_rule_head (item (bs!k!red)))"
          "is_complete (item (bs!k!red))"
          using completes unfolding completes_def inc_item_def
          by (auto simp: item_rule_head_def item_rule_body_def is_complete_def)
        have "(bs, \<omega>, k', pre) \<in> wf_tree_input"
          using wf_tree_input_prered_pre[OF prems(4) entry prered] by blast
        hence IH_pre: "wf_item_tree \<G> (item (bs!k'!pre)) (Branch N ts)"
          using prems(2)[OF entry prered _ prems(5)] Nts bounds(1,2) order_less_trans prems(6) by blast
        have "(bs, \<omega>, k, red) \<in> wf_tree_input"
          using wf_tree_input_prered_red[OF prems(4) entry prered] by blast   
        hence IH_r: "wf_item_tree \<G> (item (bs!k!red)) (Branch N_red ts_red)"
          using bounds(3) entry prems(3,5,6) prered Nts_red by blast
        have "map root_tree (ts @ [Branch N_red ts_red]) = map root_tree ts @ [root_tree (Branch N_red ts)]"
          by simp
        also have "... = take (item_dot (item (bs!k'!pre))) (item_rule_body (item (bs!k'!pre))) @ [root_tree (Branch N_red ts)]"
          using IH_pre by simp
        also have "... = take (item_dot (item (bs!k'!pre))) (item_rule_body (item (bs!k'!pre))) @ [item_rule_head (item (bs!k!red))]"
          using IH_r by simp
        also have "... = take (item_dot (item e)) (item_rule_body (item e))"
          using * by (auto simp: next_symbol_def is_complete_def split: if_splits; metis leI take_Suc_conv_app_nth)
        finally have roots: "map root_tree (ts @ [Branch N_red ts]) = take (item_dot (item e)) (item_rule_body (item e))" by simp
        have "wf_item \<G> \<omega> (item (bs!k!red))"
          using prems(5,6) bounds(3) unfolding wf_bins_def wf_bin_def wf_bin_items_def by (auto simp: items_def) 
        moreover have "N_red = item_rule_head (item (bs!k!red))"
          using IH_r by fastforce
        moreover have "map root_tree ts_red = item_rule_body (item (bs!k!red))"
          using IH_r *(5) by (auto simp: is_complete_def)
        ultimately have "\<exists>r \<in> set (\<RR> \<G>). N_red = rule_head r \<and> map root_tree ts_red = rule_body r"
          unfolding wf_item_def item_rule_body_def item_rule_head_def by blast
        hence "wf_rule_tree \<G> (Branch N_red ts_red)"
          using IH_r by simp
        hence "wf_item_tree \<G> (item (bs!k!i)) (Branch N (ts @ [Branch N_red ts_red]))"
          using "*"(1) roots IH_pre entry by simp
        thus ?thesis
          using Nts_red prems(8) simp by auto
      qed
    qed
    done
  thus ?thesis
    using assms(2) by blast
qed

lemma wf_yield_tree_build_tree':
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  assumes "wf_bins \<G> \<omega> bs"
  assumes "k < length bs" "i < length (bs!k)" "k \<le> length \<omega>"
  assumes "build_tree' bs \<omega> k i = Some t"
  shows "wf_yield_tree \<omega> (item (bs!k!i)) t"
proof -
  have "wf_yield_tree \<omega> (item (bs!k!i)) t"
    using assms
    apply (induction arbitrary: t rule: build_tree'_induct[OF assms(1)])
    subgoal premises prems for bs \<omega> k i t
    proof -
      define e where entry: "e = bs!k!i"
      consider (Null) "pointer e = Null"
        | (Pre) "\<exists>pre. pointer e = Pre pre"
        | (PreRed) "\<exists>k' pre red reds. pointer e = PreRed (k', pre, red) reds"
        by (metis pointer.exhaust surj_pair)
      thus ?thesis
      proof cases
        case Null
        hence "build_tree' bs \<omega> k i = Some (Branch (item_rule_head (item e)) [])"
          using entry by simp
        have simp: "t = Branch (item_rule_head (item e)) []"
          using build_tree'_simps(1) Null prems(9) entry by simp
        have "sound_ptrs \<omega> bs"
          using prems(4) unfolding wf_tree_input_def by blast
        hence "predicts (item e)"
          using Null prems(6,7) nth_mem entry unfolding sound_ptrs_def sound_null_ptr_def by blast
        thus ?thesis
          unfolding wf_yield_tree_def predicts_def using simp entry by (auto simp: slice_empty)
      next
        case Pre
        then obtain pre where pre: "pointer e = Pre pre"
          by blast
        obtain N ts where Nts: "build_tree' bs \<omega> (k-1) pre = Some (Branch N ts)"
          using build_tree'_termination entry pre prems(4) wf_tree_input_pre by blast
        have simp: "build_tree' bs \<omega> k i = Some (Branch N (ts @ [Leaf (\<omega>!(k-1))]))"
          using build_tree'_simps(3) entry pre Nts by simp
        have "sound_ptrs \<omega> bs"
          using prems(4) unfolding wf_tree_input_def by blast
        hence bounds: "k > 0" "pre < length (bs!(k-1))"
          using entry pre prems(6,7) unfolding sound_ptrs_def sound_pre_ptr_def by (metis nth_mem)+
        moreover have "k-1 < length bs"
          by (simp add: prems(6) less_imp_diff_less)
        ultimately have IH: "wf_yield_tree \<omega> (item (bs!(k-1)!pre)) (Branch N ts)"
          using prems(1) entry pre Nts wf_tree_input_pre prems(4,5,8) by fastforce
        have scans: "scans \<omega> k (item (bs!(k-1)!pre)) (item e)"
          using entry pre prems(6-7) \<open>sound_ptrs \<omega> bs\<close> unfolding sound_ptrs_def sound_pre_ptr_def by simp
        have wf: 
          "item_origin (item (bs!(k-1)!pre)) \<le> item_end (item (bs!(k-1)!pre))"
          "item_end (item (bs!(k-1)!pre)) = k-1"
          "item_end (item e) = k"
          using entry prems(5,6,7) bounds unfolding wf_bins_def wf_bin_def wf_bin_items_def items_def wf_item_def
          by (auto, meson less_imp_diff_less nth_mem)
        have "yield_tree (Branch N (ts @ [Leaf (\<omega>!(k-1))])) = concat (map yield_tree (ts @ [Leaf (\<omega>!(k-1))]))"
          by simp
        also have "... = concat (map yield_tree ts) @ [\<omega>!(k-1)]"
          by simp
        also have "... = slice (item_origin (item (bs!(k-1)!pre))) (item_end (item (bs!(k-1)!pre))) \<omega> @ [\<omega>!(k-1)]"
          using IH by (simp add: wf_yield_tree_def)
        also have "... = slice (item_origin (item (bs!(k-1)!pre))) (item_end (item (bs!(k-1)!pre)) + 1) \<omega>"
          using slice_append_nth wf \<open>k > 0\<close> prems(8)
          by (metis diff_less le_eq_less_or_eq less_imp_diff_less less_numeral_extra(1))
        also have "... = slice (item_origin (item e)) (item_end (item (bs!(k-1)!pre)) + 1) \<omega>"
          using scans unfolding scans_def inc_item_def by simp
        also have "... = slice (item_origin (item e)) k \<omega>"
          using scans wf unfolding scans_def by (metis Suc_diff_1 Suc_eq_plus1 bounds(1))
        also have "... = slice (item_origin (item e)) (item_end (item e)) \<omega>"
          using wf by auto
        finally show ?thesis
          using wf_yield_tree_def entry prems(9) simp by force
      next
        case PreRed
        then obtain k' pre red ps where prered: "pointer e = PreRed (k', pre, red) ps"
          by blast
        obtain N ts where Nts: "build_tree' bs \<omega> k' pre = Some (Branch N ts)"
          using build_tree'_termination entry prems(4) prered wf_tree_input_prered_pre by blast
        obtain N_red ts_red where Nts_red: "build_tree' bs \<omega> k red = Some (Branch N_red ts_red)"
          using build_tree'_termination entry prems(4) prered wf_tree_input_prered_red by blast
        have simp: "build_tree' bs \<omega> k i = Some (Branch N (ts @ [Branch N_red ts_red]))"
          using build_tree'_simps(8) entry prered Nts Nts_red by auto
        have "sound_ptrs \<omega> bs"
          using prems(4) wf_tree_input_def by fastforce
        have bounds: "k' < k" "pre < length (bs!k')" "red < length (bs!k)"
          using prered entry prems(6,7) \<open>sound_ptrs \<omega> bs\<close>
          unfolding sound_ptrs_def sound_prered_ptr_def by fastforce+
        have completes: "completes k (item (bs!k'!pre)) (item e) (item (bs!k!red))"
          using prered entry prems(6,7) \<open>sound_ptrs \<omega> bs\<close>
          unfolding sound_ptrs_def sound_prered_ptr_def by fastforce
        have "(bs, \<omega>, k', pre) \<in> wf_tree_input"
          using wf_tree_input_prered_pre[OF prems(4) entry prered] by blast
        hence IH_pre: "wf_yield_tree \<omega> (item (bs!k'!pre)) (Branch N ts)"
          using prems(2)[OF entry prered _ prems(5)] Nts bounds(1,2) prems(6-8)
          by (meson dual_order.strict_trans1 nat_less_le)
        have "(bs, \<omega>, k, red) \<in> wf_tree_input"
          using wf_tree_input_prered_red[OF prems(4) entry prered] by blast
        hence IH_r: "wf_yield_tree \<omega> (item (bs!k!red)) (Branch N_red ts_red)"
          using bounds(3) entry prems(3,5,6,8) prered Nts_red by blast
        have wf1: 
          "item_origin (item (bs!k'!pre)) \<le> item_end (item (bs!k'!pre))"
          "item_origin (item (bs!k!red)) \<le> item_end (item (bs!k!red))"
          using prems(5-7) bounds unfolding wf_bins_def wf_bin_def wf_bin_items_def items_def wf_item_def
          by (metis length_map nth_map nth_mem order_less_trans)+
        have wf2:
          "item_end (item (bs!k!red)) = k"
          "item_end (item (bs!k!i)) = k"
          using prems(5-7) bounds unfolding wf_bins_def wf_bin_def wf_bin_items_def items_def by simp_all
        have "yield_tree (Branch N (ts @ [Branch N_red ts_red])) = concat (map yield_tree (ts @ [Branch N_red ts_red]))"
          by (simp add: Nts_red)
        also have "... = concat (map yield_tree ts) @ yield_tree (Branch N_red ts_red)"
          by simp
        also have "... = slice (item_origin (item (bs!k'!pre))) (item_end (item (bs!k'!pre))) \<omega> @ 
          slice (item_origin (item (bs!k!red))) (item_end (item (bs!k!red))) \<omega>"
          using IH_pre IH_r by (simp add: wf_yield_tree_def)
        also have "... = slice (item_origin (item (bs!k'!pre))) (item_end (item (bs!k!red))) \<omega>"
          using slice_concat wf1 completes_def completes by (metis (no_types, lifting))
        also have "... = slice (item_origin (item e)) (item_end (item (bs!k!red))) \<omega>"
          using completes unfolding completes_def inc_item_def by simp
        also have "... = slice (item_origin (item e)) (item_end (item e)) \<omega>"
          using wf2 entry by presburger
        finally show ?thesis
          using wf_yield_tree_def entry prems(9) simp by force
      qed
    qed
    done
  thus ?thesis
    using assms(2) by blast
qed

theorem wf_rule_root_yield_tree_build_forest:
  assumes "wf_bins \<G> \<omega> bs" "sound_ptrs \<omega> bs" "mono_red_ptr bs" "length bs = length \<omega> + 1"
  assumes "build_tree \<G> \<omega> bs = Some t"
  shows "wf_rule_tree \<G> t \<and> root_tree t = \<SS> \<G> \<and> yield_tree t = \<omega>"
proof -
  let ?k = "length bs - 1"
  define finished where finished_def: "finished = filter_with_index (is_finished \<G> \<omega>) (items (bs!?k))"
  then obtain x i where *: "(x,i) \<in> set finished" "Some t = build_tree' bs \<omega> ?k i"
    using assms(5) unfolding finished_def build_tree_def by (auto simp: Let_def split: list.splits, presburger)
  have k: "?k < length bs" "?k \<le> length \<omega>"
    using assms(4) by simp_all
  have i: "i < length (bs!?k)"
    using index_filter_with_index_lt_length * items_def finished_def by (metis length_map)
  have x: "x = item (bs!?k!i)"
    using * i filter_with_index_nth items_def nth_map finished_def by metis
  have finished: "is_finished \<G> \<omega> x"
    using * filter_with_index_P finished_def by metis
  have wf_trees_input: "(bs, \<omega>, ?k, i) \<in> wf_tree_input"
    unfolding wf_tree_input_def using assms(2,3) i k(1) by blast
  hence wf_item_tree: "wf_item_tree \<G> x t"
    using wf_item_tree_build_tree' assms(1,2) i k(1) x *(2) by metis
  have wf_item: "wf_item \<G> \<omega> (item (bs!?k!i))"
    using k(1) i assms(1) unfolding wf_bins_def wf_bin_def wf_bin_items_def by (simp add: items_def)
  obtain N ts where t: "t = Branch N ts"
    by (metis *(2) build_tree'_termination option.inject wf_trees_input)
  hence "N = item_rule_head x"
    "map root_tree ts = item_rule_body x"
    using finished wf_item_tree by (auto simp: is_finished_def is_complete_def)
  hence "\<exists>r \<in> set (\<RR> \<G>). N = rule_head r \<and> map root_tree ts = rule_body r"
    using wf_item x unfolding wf_item_def item_rule_body_def item_rule_head_def by blast
  hence wf_rule: "wf_rule_tree \<G> t"
    using wf_item_tree t by simp
  have root: "root_tree t = \<SS> \<G>"
    using finished t \<open>N = item_rule_head x\<close> by (auto simp: is_finished_def)
  have "yield_tree t = slice (item_origin (item (bs!?k!i))) (item_end (item (bs!?k!i))) \<omega>"
    using k i assms(1) wf_trees_input wf_yield_tree_build_tree' wf_yield_tree_def *(2) by (metis (no_types, lifting))
  hence yield: "yield_tree t = \<omega>"
    using finished x unfolding is_finished_def by simp
  show ?thesis
    using * wf_rule root yield assms(4) unfolding build_tree_def by simp
qed

corollary wf_rule_root_yield_tree_build_tree_Earley\<^sub>L:
  assumes "wf_\<G> \<G>" "nonempty_derives \<G>"
  assumes "build_tree \<G> \<omega> (Earley\<^sub>L \<G> \<omega>) = Some t"
  shows "wf_rule_tree \<G> t \<and> root_tree t = \<SS> \<G> \<and> yield_tree t = \<omega>"
  using assms wf_rule_root_yield_tree_build_forest wf_bins_Earley\<^sub>L sound_mono_ptrs_Earley\<^sub>L Earley\<^sub>L_def
    length_Earley\<^sub>L_bins length_bins_Init\<^sub>L by (metis nle_le)

theorem correctness_build_tree_Earley\<^sub>L:
  assumes "wf_\<G> \<G>" "is_word \<G> \<omega>" "nonempty_derives \<G>"
  shows "(\<exists>t. build_tree \<G> \<omega> (Earley\<^sub>L \<G> \<omega>) = Some t) \<longleftrightarrow> derives \<G> [\<SS> \<G>] \<omega>" (is "?L \<longleftrightarrow> ?R")
proof standard
  assume *: ?L
  let ?k = "length (Earley\<^sub>L \<G> \<omega>) - 1"
  define finished where finished_def: "finished = filter_with_index (is_finished \<G> \<omega>) (items ((Earley\<^sub>L \<G> \<omega>)!?k))"
  then obtain t x i where *: "(x,i) \<in> set finished" "Some t = build_tree' (Earley\<^sub>L \<G> \<omega>) \<omega> ?k i"
    using * unfolding finished_def build_tree_def by (auto simp: Let_def split: list.splits, presburger)
  have k: "?k < length (Earley\<^sub>L \<G> \<omega>)" "?k \<le> length \<omega>"
    by (simp_all add: Earley\<^sub>L_def assms(1))
  have i: "i < length ((Earley\<^sub>L \<G> \<omega>) ! ?k)"
    using index_filter_with_index_lt_length * items_def finished_def by (metis length_map)
  have x: "x = item ((Earley\<^sub>L \<G> \<omega>)!?k!i)"
    using * i filter_with_index_nth items_def nth_map finished_def by metis
  have finished: "is_finished \<G> \<omega> x"
    using * filter_with_index_P finished_def by metis
  moreover have "x \<in> set (items ((Earley\<^sub>L \<G> \<omega>) ! ?k))"
    using x by (auto simp: items_def; metis One_nat_def i imageI nth_mem)
  ultimately have "recognizing (bins (Earley\<^sub>L \<G> \<omega>)) \<G> \<omega>"
    by (meson k(1) kth_bin_sub_bins recognizing_def subsetD)
  thus ?R
    using correctness_Earley\<^sub>L assms by blast
next
  assume *: ?R
  let ?k = "length (Earley\<^sub>L \<G> \<omega>) - 1"
  define finished where finished_def: "finished = filter_with_index (is_finished \<G> \<omega>) (items ((Earley\<^sub>L \<G> \<omega>)!?k))"
  have "recognizing (bins (Earley\<^sub>L \<G> \<omega>)) \<G> \<omega>"
    using assms * correctness_Earley\<^sub>L by blast
  moreover have "?k = length \<omega>"
    by (simp add: Earley\<^sub>L_def assms(1))
  ultimately have "\<exists>x \<in> set (items ((Earley\<^sub>L \<G> \<omega>)!?k)). is_finished \<G> \<omega> x"
    unfolding recognizing_def using assms(1) is_finished_def wf_bins_Earley\<^sub>L wf_item_in_kth_bin by metis
  then obtain x i xs where xis: "finished = (x,i)#xs"
    using filter_with_index_Ex_first by (metis finished_def)
  hence simp: "build_tree \<G> \<omega> (Earley\<^sub>L \<G> \<omega>) = build_tree' (Earley\<^sub>L \<G> \<omega>) \<omega> ?k i"
    unfolding build_tree_def finished_def by auto
  have "(x,i) \<in> set finished"
    using xis by simp
  hence "i < length ((Earley\<^sub>L \<G> \<omega>)!?k)"
    using index_filter_with_index_lt_length by (metis finished_def items_def length_map)
  moreover have "?k < length (Earley\<^sub>L \<G> \<omega>)"
    by (simp add: Earley\<^sub>L_def assms(1))
  ultimately have "(Earley\<^sub>L \<G> \<omega>, \<omega>, ?k, i) \<in> wf_tree_input"
    unfolding wf_tree_input_def using sound_mono_ptrs_Earley\<^sub>L assms(1,3) by blast
  then obtain N ts where "build_tree' (Earley\<^sub>L \<G> \<omega>) \<omega> ?k i = Some (Branch N ts)"
    using build_tree'_termination by blast
  thus ?L
    using simp by simp
qed


subsection \<open>those, map, map option lemmas\<close>

lemma those_map_exists:
  "Some ys = those (map f xs) \<Longrightarrow> y \<in> set ys \<Longrightarrow> \<exists>x. x \<in> set xs \<and> Some y \<in> set (map f xs)"
proof (induction xs arbitrary: ys)
  case (Cons a xs)
  then show ?case
    apply (clarsimp split: option.splits)
    by (smt (verit, best) map_option_eq_Some set_ConsD)
qed auto

lemma those_Some:
  "(\<forall>x \<in> set xs. \<exists>a. x = Some a) \<longleftrightarrow> (\<exists>ys. those xs = Some ys)"
  by (induction xs) (auto split: option.splits)

lemma those_Some_P:
  assumes "\<forall>x \<in> set xs. \<exists>ys. x = Some ys \<and> (\<forall>y \<in> set ys. P y)"
  shows "\<exists>yss. those xs = Some yss \<and> (\<forall>ys \<in> set yss. \<forall>y \<in> set ys. P y)"
  using assms by (induction xs) auto

lemma map_Some_P:
  assumes "z \<in> set (map f xs)"
  assumes "\<forall>x \<in> set xs. \<exists>ys. f x = Some ys \<and> (\<forall>y \<in> set ys. P y)"
  shows "\<exists>ys. z = Some ys \<and> (\<forall>y \<in> set ys. P y)"
  using assms by (induction xs) auto

lemma those_map_FBranch_only:
  assumes "g = (\<lambda>f. case f of FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [[FLeaf (\<omega>!(k-1))]])) | _ \<Rightarrow> None)"
  assumes "Some fs = those (map g pres)" "f \<in> set fs"
  assumes "\<forall>f \<in> set pres. \<exists>N fss. f = FBranch N fss"
  shows "\<exists>f_pre N fss. f = FBranch N (fss @ [[FLeaf (\<omega>!(k-1))]]) \<and> f_pre = FBranch N fss \<and> f_pre \<in> set pres"
  using assms
  apply (induction pres arbitrary: fs f)
  apply (auto)
  by (smt (verit, best) list.inject list.set_cases map_option_eq_Some)

lemma those_map_Some_concat_exists:
  assumes "y \<in> set (concat ys)"
  assumes "Some ys = those (map f xs)"
  shows "\<exists>ys x. Some ys = f x \<and> y \<in> set ys \<and> x \<in> set xs"
  using assms
  apply (induction xs arbitrary: ys y) 
  apply (auto split: option.splits)
  by (smt (verit, ccfv_threshold) list.inject list.set_cases map_option_eq_Some)

lemma map_option_concat_those_map_exists:
  assumes "Some fs = map_option concat (those (map F xs))"
  assumes "f \<in> set fs"
  shows "\<exists>fss fs'. Some fss = those (map F xs) \<and> fs' \<in> set fss \<and> f \<in> set fs'"
  using assms
  apply (induction xs arbitrary: fs f)
  apply (auto split: option.splits)
  by (smt (verit, best) UN_E map_option_eq_Some set_concat)

lemma [partial_function_mono]:
  "monotone option.le_fun option_ord
    (\<lambda>f. map_option concat (those (map (\<lambda>((k', pre), reds).
      f ((((r, s), k'), pre), {pre}) \<bind>
        (\<lambda>pres. those (map (\<lambda>red. f ((((r, s), t), red), b \<union> {red})) reds) \<bind>
          (\<lambda>rss. those (map (\<lambda>f. case f of FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [concat rss])) | _ \<Rightarrow> None) pres))))
    xs)))"
proof -
  let ?f = "
    (\<lambda>f. map_option concat (those (map (\<lambda>((k', pre), reds).
      f ((((r, s), k'), pre), {pre}) \<bind>
        (\<lambda>pres. those (map (\<lambda>red. f ((((r, s), t), red), b \<union> {red})) reds) \<bind>
          (\<lambda>rss. those (map (\<lambda>f. case f of FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [concat rss])) | _ \<Rightarrow> None) pres))))
    xs)))"
  have 0: "\<And>x y. option.le_fun x y \<Longrightarrow> option_ord (?f x) (?f y)"
    apply (auto simp: flat_ord_def fun_ord_def option.leq_refl split: option.splits forest.splits)
    subgoal premises prems for x y
    proof -
      let ?t = "those (map (\<lambda>((k', pre), reds).
        x ((((r, s), k'), pre), {pre}) \<bind>
          (\<lambda>pres. those (map (\<lambda>red. x ((((r, s), t), red), insert red b)) reds) \<bind>
            (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres))))
        xs) = None"
      show ?t
      proof (rule ccontr)
        assume a: "\<not>?t"
        obtain fss where fss: "those (map (\<lambda>((k', pre), reds).
        x ((((r, s), k'), pre), {pre}) \<bind>
          (\<lambda>pres. those (map (\<lambda>red. x ((((r, s), t), red), insert red b)) reds) \<bind>
            (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres))))
        xs) = Some fss"
          using a by blast
        {
          fix k' pre reds
          assume *: "((k', pre), reds) \<in> set xs"
          obtain pres where pres: "x ((((r, s), k'), pre), {pre}) = Some pres"
            using fss * those_Some by force
          have "\<exists>fs. Some fs = those (map (\<lambda>red. x ((((r, s), t), red), insert red b)) reds) \<bind>
            (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres))"
          proof (rule ccontr)
            assume "\<nexists>fs. Some fs =
              those (map (\<lambda>red. x ((((r, s), t), red), insert red b)) reds) \<bind>
                (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres))"
            hence "None =
              those (map (\<lambda>red. x ((((r, s), t), red), insert red b)) reds) \<bind>
                (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres))"
              by (smt (verit) not_None_eq)
            hence "None = x ((((r, s), k'), pre), {pre}) \<bind>
              (\<lambda>pres. those (map (\<lambda>red. x ((((r, s), t), red), insert red b)) reds) \<bind>
                (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres)))"
              by (simp add: pres)
            hence "\<exists>((k', pre), reds) \<in> set xs. None = x ((((r, s), k'), pre), {pre}) \<bind>
              (\<lambda>pres. those (map (\<lambda>red. x ((((r, s), t), red), insert red b)) reds) \<bind>
                (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres)))"
              using * by blast
            thus False
              using fss those_Some by force
          qed
          then obtain fs where fs: "Some fs = those (map (\<lambda>red. x ((((r, s), t), red), insert red b)) reds) \<bind>
            (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres))"
            by blast
          obtain rss where rss: "those (map (\<lambda>red. x ((((r, s), t), red), insert red b)) reds) = Some rss"
            using fs by force
          have "x ((((r, s), k'), pre), {pre}) = y ((((r, s), k'), pre), {pre})"
            using pres prems(1) by (metis option.distinct(1))
          moreover have "those (map (\<lambda>red. x ((((r, s), t), red), insert red b)) reds) \<bind>
            (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres))
          = those (map (\<lambda>red. y ((((r, s), t), red), insert red b)) reds) \<bind>
            (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres))"
          proof -
            have "\<forall>red \<in> set reds. x ((((r, s), t), red), insert red b) = y ((((r, s), t), red), insert red b)"
            proof standard
              fix red
              assume "red \<in> set reds"
              have "\<forall>x\<in>set (map (\<lambda>red. x ((((r, s), t), red), insert red b)) reds) . \<exists>a. x = Some a"
                using rss those_Some by blast
              then obtain f where "x ((((r, s), t), red), insert red b) = Some f"
                using \<open>red \<in> set reds\<close> by auto
              thus "x ((((r, s), t), red), insert red b) = y ((((r, s), t), red), insert red b)"
                using prems(1) by (metis option.distinct(1))
            qed
            thus ?thesis
              by (smt (verit, best) map_eq_conv)
          qed
          ultimately have " x ((((r, s), k'), pre), {pre}) \<bind>
          (\<lambda>pres. those (map (\<lambda>red. x ((((r, s), t), red), insert red b)) reds) \<bind>
            (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres)))
        = y ((((r, s), k'), pre), {pre}) \<bind>
          (\<lambda>pres. those (map (\<lambda>red. y ((((r, s), t), red), insert red b)) reds) \<bind>
            (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres)))"
            by (metis bind.bind_lunit pres)
        }
        hence "\<forall>((k', pre), reds) \<in> set xs. x ((((r, s), k'), pre), {pre}) \<bind>
          (\<lambda>pres. those (map (\<lambda>red. x ((((r, s), t), red), insert red b)) reds) \<bind>
            (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres)))
        = y ((((r, s), k'), pre), {pre}) \<bind>
          (\<lambda>pres. those (map (\<lambda>red. y ((((r, s), t), red), insert red b)) reds) \<bind>
            (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres)))"
          by blast
        hence "those (map (\<lambda>((k', pre), reds).
        x ((((r, s), k'), pre), {pre}) \<bind>
          (\<lambda>pres. those (map (\<lambda>red. x ((((r, s), t), red), insert red b)) reds) \<bind>
            (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres))))
        xs) = those (map (\<lambda>((k', pre), reds).
        y ((((r, s), k'), pre), {pre}) \<bind>
          (\<lambda>pres. those (map (\<lambda>red. y ((((r, s), t), red), insert red b)) reds) \<bind>
            (\<lambda>rss. those (map (case_forest Map.empty (\<lambda>N fss. Some (FBranch N (fss @ [concat rss])))) pres))))
        xs)"
          using prems(1) by (smt (verit, best) case_prod_conv map_eq_conv split_cong)
        thus False
          using prems(2) by simp
      qed
    qed
    done
  show ?thesis
    using monotoneI[of option.le_fun option_ord ?f, OF 0] by blast
qed

subsection \<open>Parse trees\<close>

fun insert_group :: "('a \<Rightarrow> 'k) \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'a \<Rightarrow> ('k \<times> 'v list) list \<Rightarrow> ('k \<times> 'v list) list" where
  "insert_group K V a [] = [(K a, [V a])]"
| "insert_group K V a ((k, vs)#xs) = (
    if K a = k then (k, V a # vs) # xs
    else (k, vs) # insert_group K V a xs  
  )"

fun group_by :: "('a \<Rightarrow> 'k) \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'a list \<Rightarrow> ('k \<times> 'v list) list" where
  "group_by K V [] = []"
| "group_by K V (x#xs) = insert_group K V x (group_by K V xs)"

lemma insert_group_cases:
  assumes "(k, vs) \<in> set (insert_group K V a xs)"
  shows "(k = K a \<and> vs = [V a]) \<or> (k, vs) \<in> set xs \<or> (\<exists>(k', vs') \<in> set xs. k' = k \<and> k = K a \<and> vs = V a # vs')"
  using assms by (induction xs) (auto split: if_splits)

lemma group_by_exists_kv:
  "(k, vs) \<in> set (group_by K V xs) \<Longrightarrow> \<exists>x \<in> set xs. k = K x \<and> (\<exists>v \<in> set vs. v = V x)"
  using insert_group_cases by (induction xs) (simp, force)

lemma group_by_forall_v_exists_k:
  "(k, vs) \<in> set (group_by K V xs) \<Longrightarrow> v \<in> set vs \<Longrightarrow> \<exists>x \<in> set xs. k = K x \<and> v = V x"
proof (induction xs arbitrary: vs)
  case (Cons x xs)
  show ?case
  proof (cases "(k, vs) \<in> set (group_by K V xs)")
    case True
    thus ?thesis
      using Cons by simp
  next
    case False
    hence "(k, vs) \<in> set (insert_group K V x (group_by K V xs))"
      using Cons.prems(1) by force
    then consider (A) "(k = K x \<and> vs = [V x])"
      | (B) "(k, vs) \<in> set (group_by K V xs)"
      | (C) "(\<exists>(k', vs') \<in> set (group_by K V xs). k' = k \<and> k = K x \<and> vs = V x # vs')"
      using insert_group_cases by fastforce
    thus ?thesis
    proof cases
      case A
      thus ?thesis
        using Cons.prems(2) by auto
    next
      case B
      then show ?thesis
        using False by linarith
    next
      case C
      then show ?thesis
        using Cons.IH Cons.prems(2) by fastforce
    qed
  qed
qed simp

partial_function (option) build_trees' :: "'a bins \<Rightarrow> 'a sentence \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> 'a forest list option" where
  "build_trees' bs \<omega> k i I = (
    let e = bs!k!i in (
    case pointer e of
      Null \<Rightarrow> Some ([FBranch (item_rule_head (item e)) []]) \<comment>\<open>start building sub-trees\<close>
    | Pre pre \<Rightarrow> ( \<comment>\<open>add sub-trees starting from terminal\<close>
        do {
          pres \<leftarrow> build_trees' bs \<omega> (k-1) pre {pre};
          those (map (\<lambda>f.
            case f of
              FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [[FLeaf (\<omega>!(k-1))]]))
            | _ \<Rightarrow> None  \<comment>\<open>impossible case\<close>
          ) pres)
        })
    | PreRed p ps \<Rightarrow> ( \<comment>\<open>add sub-trees starting from non-terminal\<close>
        let ps' = filter (\<lambda>(k', pre, red). red \<notin> I) (p#ps) in
        let gs = group_by (\<lambda>(k', pre, red). (k', pre)) (\<lambda>(k', pre, red). red) ps' in
        map_option concat (those (map (\<lambda>((k', pre), reds).
          do {
            pres \<leftarrow> build_trees' bs \<omega> k' pre {pre};
            rss \<leftarrow> those (map (\<lambda>red. build_trees' bs \<omega> k red (I \<union> {red})) reds);
            those (map (\<lambda>f.
              case f of
                FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [concat rss]))
              | _ \<Rightarrow> None \<comment>\<open>impossible case\<close>
            ) pres)
          }
        ) gs))
      )
  ))"

declare build_trees'.simps [code]

definition build_trees :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a bins \<Rightarrow> 'a forest list option" where
  "build_trees \<G> \<omega> bs = (
    let k = length bs - 1 in
    let finished = filter_with_index (\<lambda>x. is_finished \<G> \<omega> x) (items (bs!k)) in
    map_option concat (those (map (\<lambda>(_, i). build_trees' bs \<omega> k i {i}) finished))
  )"

lemma build_forest'_simps[simp]:
  "e = bs!k!i \<Longrightarrow> pointer e = Null \<Longrightarrow> build_trees' bs \<omega> k i I = Some ([FBranch (item_rule_head (item e)) []])"
  "e = bs!k!i \<Longrightarrow> pointer e = Pre pre \<Longrightarrow> build_trees' bs \<omega> (k-1) pre {pre} = None \<Longrightarrow> build_trees' bs \<omega> k i I = None"
  "e = bs!k!i \<Longrightarrow> pointer e = Pre pre \<Longrightarrow> build_trees' bs \<omega> (k-1) pre {pre} = Some pres \<Longrightarrow>
    build_trees' bs \<omega> k i I = those (map (\<lambda>f. case f of FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [[FLeaf (\<omega>!(k-1))]])) | _ \<Rightarrow> None) pres)"
  by (subst build_trees'.simps, simp)+

definition wf_trees_input :: "('a bins \<times> 'a sentence \<times> nat \<times> nat \<times> nat set) set" where
  "wf_trees_input = {
    (bs, \<omega>, k, i, I) | bs \<omega> k i I.
      sound_ptrs \<omega> bs \<and>
      k < length bs \<and>
      i < length (bs!k) \<and>
      I \<subseteq> {0..<length (bs!k)} \<and>
      i \<in> I
  }"

fun build_forest'_measure :: "('a bins \<times> 'a sentence \<times> nat \<times> nat \<times> nat set) \<Rightarrow> nat" where
  "build_forest'_measure (bs, \<omega>, k, i, I) = foldl (+) 0 (map length (take (k+1) bs)) - card I"

lemma wf_trees_input_pre:
  assumes "(bs, \<omega>, k, i, I) \<in> wf_trees_input"
  assumes "e = bs!k!i" "pointer e = Pre pre"
  shows "(bs, \<omega>, (k-1), pre, {pre}) \<in> wf_trees_input"
  using assms unfolding wf_trees_input_def
  apply (auto simp: sound_ptrs_def sound_pre_ptr_def)
  apply (metis nth_mem)
  done

lemma wf_trees_input_prered_pre:
  assumes "(bs, \<omega>, k, i, I) \<in> wf_trees_input"
  assumes "e = bs!k!i" "pointer e = PreRed p ps"
  assumes "ps' = filter (\<lambda>(k', pre, red). red \<notin> I) (p#ps)"
  assumes "gs = group_by (\<lambda>(k', pre, red). (k', pre)) (\<lambda>(k', pre, red). red) ps'"
  assumes "((k', pre), reds) \<in> set gs"
  shows "(bs, \<omega>, k', pre, {pre}) \<in> wf_trees_input"
proof -
  obtain red where "(k', pre, red) \<in> set ps'"
    using assms(5,6) group_by_exists_kv by fast
  hence *: "(k', pre, red) \<in> set (p#ps)"
    using assms(4) by (meson filter_is_subset in_mono)
  have "k < length bs" "e \<in> set (bs!k)"
    using assms(1,2) unfolding wf_trees_input_def by auto
  hence "k' < k" "pre < length (bs!k')"
    using assms(1,3) * unfolding wf_trees_input_def sound_ptrs_def sound_prered_ptr_def by blast+
  thus ?thesis
    using assms by (simp add: wf_trees_input_def)
qed

lemma wf_trees_input_prered_red:
  assumes "(bs, \<omega>, k, i, I) \<in> wf_trees_input"
  assumes "e = bs!k!i" "pointer e = PreRed p ps"
  assumes "ps' = filter (\<lambda>(k', pre, red). red \<notin> I) (p#ps)"
  assumes "gs = group_by (\<lambda>(k', pre, red). (k', pre)) (\<lambda>(k', pre, red). red) ps'"
  assumes "((k', pre), reds) \<in> set gs" "red \<in> set reds"
  shows "(bs, \<omega>, k, red, I \<union> {red}) \<in> wf_trees_input"
proof -
  have "(k', pre, red) \<in> set ps'"
    using assms(5,6,7) group_by_forall_v_exists_k by fastforce
  hence *: "(k', pre, red) \<in> set (p#ps)"
    using assms(4) by (meson filter_is_subset in_mono)
  have "k < length bs" "e \<in> set (bs!k)"
    using assms(1,2) unfolding wf_trees_input_def by auto
  hence 0: "red < length (bs!k)"
    using assms(1,3) * unfolding wf_trees_input_def sound_ptrs_def sound_prered_ptr_def by blast
  moreover have "I \<subseteq> {0..<length (bs!k)}"
    using assms(1) unfolding wf_trees_input_def by blast
  ultimately have 1: "I \<union> {red} \<subseteq> {0..<length (bs!k)}"
    by simp
  show ?thesis
    using 0 1 assms(1) unfolding wf_trees_input_def by blast
qed

lemma build_trees'_induct:
  assumes "(bs, \<omega>, k, i, I) \<in> wf_trees_input"
  assumes "\<And>bs \<omega> k i I.
    (\<And>e pre. e = bs!k!i \<Longrightarrow> pointer e = Pre pre \<Longrightarrow> P bs \<omega> (k-1) pre {pre}) \<Longrightarrow>
    (\<And>e p ps ps' gs k' pre reds. e = bs!k!i \<Longrightarrow> pointer e = PreRed p ps \<Longrightarrow>
      ps' = filter (\<lambda>(k', pre, red). red \<notin> I) (p#ps) \<Longrightarrow>
      gs = group_by (\<lambda>(k', pre, red). (k', pre)) (\<lambda>(k', pre, red). red) ps' \<Longrightarrow>
      ((k', pre), reds) \<in> set gs \<Longrightarrow> P bs \<omega> k' pre {pre}) \<Longrightarrow>
    (\<And>e p ps ps' gs k' pre red reds reds'. e = bs!k!i \<Longrightarrow> pointer e = PreRed p ps \<Longrightarrow>
      ps' = filter (\<lambda>(k', pre, red). red \<notin> I) (p#ps) \<Longrightarrow>
      gs = group_by (\<lambda>(k', pre, red). (k', pre)) (\<lambda>(k', pre, red). red) ps' \<Longrightarrow>
      ((k', pre), reds) \<in> set gs \<Longrightarrow> red \<in> set reds \<Longrightarrow> P bs \<omega> k red (I \<union> {red})) \<Longrightarrow>
    P bs \<omega> k i I" 
  shows "P bs \<omega> k i I"
  using assms(1)
proof (induction n\<equiv>"build_forest'_measure (bs, \<omega>, k, i, I)" arbitrary: k i I rule: nat_less_induct)
  case 1
  obtain e where entry: "e = bs!k!i"
    by simp
  consider (Null) "pointer e = Null"
    | (Pre) "\<exists>pre. pointer e = Pre pre"
    | (PreRed) "\<exists>p ps. pointer e = PreRed p ps"
    by (metis pointer.exhaust)
  thus ?case
  proof cases
    case Null
    thus ?thesis
      using assms(2) entry by fastforce
  next
    case Pre
    then obtain pre where pre: "pointer e = Pre pre"
      by blast
    define n where n: "n = build_forest'_measure (bs, \<omega>, (k-1), pre, {pre})"
    have "0 < k" "pre < length (bs!(k-1))"
      using 1(2) entry pre unfolding wf_trees_input_def sound_ptrs_def sound_pre_ptr_def
      by (smt (verit) mem_Collect_eq nth_mem prod.inject)+
    have "k < length bs" "i < length (bs!k)" "I \<subseteq> {0..<length (bs!k)}" "i \<in> I"
      using 1(2) unfolding wf_trees_input_def by blast+
    have "length (bs!(k-1)) > 0"
      using \<open>pre < length (bs!(k-1))\<close> by force
    hence "foldl (+) 0 (map length (take k bs)) > 0"
      by (smt (verit, del_insts) foldl_add_nth \<open>0 < k\<close> \<open>k < length bs\<close> 
          add.commute add_diff_inverse_nat less_imp_diff_less less_one zero_eq_add_iff_both_eq_0)
    have "card I \<le> length (bs!k)"
      by (simp add: \<open>I \<subseteq> {0..<length (bs ! k)}\<close> subset_eq_atLeast0_lessThan_card)
    have "card I + (foldl (+) 0 (map length (take (Suc (k - Suc 0)) bs)) - Suc 0) =
      card I + (foldl (+) 0 (map length (take k bs)) - 1)"
      using \<open>0 < k\<close> by simp
    also have "... = card I + foldl (+) 0 (map length (take k bs)) - 1"
      using \<open>0 < foldl (+) 0 (map length (take k bs))\<close> by auto
    also have "... < card I + foldl (+) 0 (map length (take k bs))"
      by (simp add: \<open>0 < foldl (+) 0 (map length (take k bs))\<close>)
    also have "... \<le> foldl (+) 0 (map length (take k bs)) + length (bs!k)"
      by (simp add: \<open>card I \<le> length (bs ! k)\<close>)
    also have "... = foldl (+) 0 (map length (take (k+1) bs))"
      using foldl_add_nth \<open>k < length bs\<close> by blast
    finally have "build_forest'_measure (bs, \<omega>, k, i, I) - build_forest'_measure (bs, \<omega>, (k-1), pre, {pre}) > 0"
      by simp
    hence "P bs \<omega> (k-1) pre {pre}"
      using 1 n wf_trees_input_pre entry pre zero_less_diff by blast
    thus ?thesis
      using assms(2) entry pre pointer.distinct(5) pointer.inject(1) by presburger
  next
    case PreRed
    then obtain p ps where pps: "pointer e = PreRed p ps"
      by blast
    define ps' where ps': "ps' = filter (\<lambda>(k', pre, red). red \<notin> I) (p#ps)"
    define gs where gs: "gs = group_by (\<lambda>(k', pre, red). (k', pre)) (\<lambda>(k', pre, red). red) ps'"
    have 0: "\<forall>(k', pre, red) \<in> set ps'. k' < k \<and> pre < length (bs!k') \<and> red < length (bs!k)"
      using entry pps ps' 1(2) unfolding wf_trees_input_def sound_ptrs_def sound_prered_ptr_def
      apply (auto simp del: filter.simps)
      apply (metis nth_mem prod_cases3)+
      done
    hence sound_gs: "\<forall>((k', pre), reds) \<in> set gs. k' < k \<and> pre < length (bs!k')"
      using gs group_by_exists_kv by fast
    have sound_gs2: "\<forall>((k', pre), reds) \<in> set gs. \<forall>red \<in> set reds. red < length (bs!k)"
    proof (standard, standard, standard, standard)
      fix x a b k' pre red
      assume "x \<in> set gs" "x = (a, b)" "(k', pre) = a" "red \<in> set b"
      hence "\<exists>x \<in> set ps'. red = (\<lambda>(k', pre, red). red) x"
        using group_by_forall_v_exists_k gs ps' by meson
      thus "red < length (bs!k)"
        using 0 by fast
    qed
    {
      fix k' pre reds red
      assume a0: "((k', pre), reds) \<in> set gs"
      define n_pre where n_pre: "n_pre = build_forest'_measure (bs, \<omega>, k', pre, {pre})"
      have "k < length bs" "i < length (bs!k)" "I \<subseteq> {0..<length (bs!k)}" "i \<in> I"
        using 1(2) unfolding wf_trees_input_def by blast+
      have "k' < k" "pre < length (bs!k')"
        using sound_gs a0 by fastforce+
      have "length (bs!k') > 0"
        using \<open>pre < length (bs!k')\<close> by force
      hence gt0: "foldl (+) 0 (map length (take (k'+1) bs)) > 0"
        by (smt (verit, del_insts) foldl_add_nth \<open>k < length bs\<close> \<open>k' < k\<close> add_gr_0 order.strict_trans)
      have card_bound: "card I \<le> length (bs!k)"
        by (simp add: \<open>I \<subseteq> {0..<length (bs ! k)}\<close> subset_eq_atLeast0_lessThan_card)
      have "card I + (foldl (+) 0 (map length (take (Suc k') bs)) - Suc 0) =
      card I + foldl (+) 0 (map length (take (Suc k') bs)) - 1"
        by (metis Nat.add_diff_assoc One_nat_def Suc_eq_plus1 Suc_leI \<open>0 < foldl (+) 0 (map length (take (k' + 1) bs))\<close>)
      also have "... < card I + foldl (+) 0 (map length (take (Suc k') bs))"
        using gt0 by auto
      also have "... \<le> foldl (+) 0 (map length (take (Suc k') bs)) + length (bs!k)"
        using card_bound by simp
      also have "... \<le> foldl (+) 0 (map length (take (k+1) bs))"
        using foldl_add_nth_ge Suc_leI \<open>k < length bs\<close> \<open>k' < k\<close> by blast
      finally have "build_forest'_measure (bs, \<omega>, k, i, I) - build_forest'_measure (bs, \<omega>, k', pre, {pre}) > 0"
        by simp
      hence "P bs \<omega> k' pre {pre}"
        using 1(1) wf_trees_input_prered_pre[OF "1.prems"(1) entry pps ps' gs a0] zero_less_diff by blast
    }
    moreover {
      fix k' pre reds red
      assume a0: "((k', pre), reds) \<in> set gs"
      assume a1: "red \<in> set reds"
      define n_red where n_red: "n_red = build_forest'_measure (bs, \<omega>, k, red, I \<union> {red})"
      have "k < length bs" "i < length (bs!k)" "I \<subseteq> {0..<length (bs!k)}" "i \<in> I"
        using 1(2) unfolding wf_trees_input_def by blast+
      have "k' < k" "pre < length (bs!k')" "red < length (bs!k)"
        using a0 a1 sound_gs sound_gs2 by fastforce+
      have "red \<notin> I"
        using a0 a1 unfolding gs ps'
        by (smt (verit, best) group_by_forall_v_exists_k case_prodE case_prod_conv mem_Collect_eq set_filter)
      have card_bound: "card I \<le> length (bs!k)"
        by (simp add: \<open>I \<subseteq> {0..<length (bs ! k)}\<close> subset_eq_atLeast0_lessThan_card)
      have "length (bs!k') > 0"
        using \<open>pre < length (bs!k')\<close> by force
      hence gt0: "foldl (+) 0 (map length (take (k'+1) bs)) > 0"
        by (smt (verit, del_insts) foldl_add_nth \<open>k < length bs\<close> \<open>k' < k\<close> add_gr_0 order.strict_trans)
      have lt: "foldl (+) 0 (map length (take (Suc k') bs)) + length (bs!k) \<le> foldl (+) 0 (map length (take (k+1) bs))"
        using foldl_add_nth_ge Suc_leI \<open>k < length bs\<close> \<open>k' < k\<close> by blast
      have "card I + (foldl (+) 0 (map length (take (Suc k) bs)) - card (insert red I)) =
        card I + (foldl (+) 0 (map length (take (Suc k) bs)) - card I - 1)"
        using \<open>I \<subseteq> {0..<length (bs ! k)}\<close> \<open>red \<notin> I\<close> finite_subset by fastforce
      also have "... = foldl (+) 0 (map length (take (Suc k) bs)) - 1"
        using gt0 card_bound lt by force
      also have "... < foldl (+) 0 (map length (take (Suc k) bs))"
        using gt0 lt by auto
      finally have "build_forest'_measure (bs, \<omega>, k, i, I) - build_forest'_measure (bs, \<omega>, k, red, I \<union> {red}) > 0"
        by simp
      moreover have "(bs, \<omega>, k, red, I \<union> {red}) \<in> wf_trees_input"
        using wf_trees_input_prered_red[OF "1"(2) entry pps ps' gs] a0 a1 by blast
      ultimately have "P bs \<omega> k red (I \<union> {red})"
        using 1(1) zero_less_diff by blast
    }
    moreover have "(\<And>e pre. e = bs!k!i \<Longrightarrow> pointer e = Pre pre \<Longrightarrow> P bs \<omega> (k-1) pre {pre})"
      using entry pps by fastforce
    ultimately show ?thesis
      using assms(2) entry gs pointer.inject(2) pps ps' by presburger
  qed
qed

lemma build_trees'_termination:
  assumes "(bs, \<omega>, k, i, I) \<in> wf_trees_input"
  shows "\<exists>fs. build_trees' bs \<omega> k i I = Some fs \<and> (\<forall>f \<in> set fs. \<exists>N fss. f = FBranch N fss)"
proof -
  have "\<exists>fs. build_trees' bs \<omega> k i I = Some fs \<and> (\<forall>f \<in> set fs. \<exists>N fss. f = FBranch N fss)"
    apply (induction rule: build_trees'_induct[OF assms(1)])
    subgoal premises IH for bs \<omega> k i I
    proof -
      define e where entry: "e = bs!k!i"
      consider (Null) "pointer e = Null"
        | (Pre) "\<exists>pre. pointer e = Pre pre"
        | (PreRed) "\<exists>k' pre red reds. pointer e = PreRed (k', pre, red) reds"
        by (metis pointer.exhaust surj_pair)
      thus ?thesis
      proof cases
        case Null
        have "build_trees' bs \<omega> k i I = Some ([FBranch (item_rule_head (item e)) []])"
          using build_forest'_simps(1) Null entry by simp
        thus ?thesis
          by simp
      next
        case Pre
        then obtain pre where pre: "pointer e = Pre pre"
          by blast
        obtain fs where fs: "build_trees' bs \<omega> (k-1) pre {pre} = Some fs"
          "\<forall>f \<in> set fs. \<exists>N fss. f = FBranch N fss"
          using IH(1) entry pre by blast
        let ?g = "\<lambda>f. case f of FLeaf a \<Rightarrow> None
          | FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [[FLeaf (\<omega>!(k-1))]]))"
        have simp: "build_trees' bs \<omega> k i I = those (map ?g fs)"
          using build_forest'_simps(3) entry pre fs by blast
        moreover have "\<forall>f \<in> set (map ?g fs). \<exists>a. f = Some a"
          using fs(2) by auto
        ultimately obtain fs' where fs': "build_trees' bs \<omega> k i I = Some fs'"
          using those_Some by (smt (verit, best))
        moreover have "\<forall>f \<in> set fs'. \<exists>N fss. f = FBranch N fss"
        proof standard
          fix f
          assume "f \<in> set fs'"
          then obtain x where "x \<in> set fs" "Some f \<in> set (map ?g fs)"
            using those_map_exists by (metis (no_types, lifting) fs' simp)
          thus "\<exists>N fss. f = FBranch N fss"
            using fs(2) by auto
        qed
        ultimately show ?thesis
          by blast
      next
        case PreRed
        then obtain p ps where pps: "pointer e = PreRed p ps"
          by blast
        define ps' where ps': "ps' = filter (\<lambda>(k', pre, red). red \<notin> I) (p#ps)"
        define gs where gs: "gs = group_by (\<lambda>(k', pre, red). (k', pre)) (\<lambda>(k', pre, red). red) ps'"
        let ?g = "\<lambda>((k', pre), reds).
            do {
              pres \<leftarrow> build_trees' bs \<omega> k' pre {pre};
              rss \<leftarrow> those (map (\<lambda>red. build_trees' bs \<omega> k red (I \<union> {red})) reds);
              those (map (\<lambda>f.
                case f of
                  FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [concat rss]))
                | _ \<Rightarrow> None \<comment>\<open>impossible case\<close>
              ) pres)
            }"
        have simp: "build_trees' bs \<omega> k i I = map_option concat (those (map ?g gs))"
          using entry pps ps' gs by (subst build_trees'.simps) (auto simp del: filter.simps)
        have "\<forall>fso \<in> set (map ?g gs). \<exists>fs. fso = Some fs \<and> (\<forall>f \<in> set fs. \<exists>N fss. f = FBranch N fss)"
        proof standard
          fix fso
          assume "fso \<in> set (map ?g gs)"
          moreover have "\<forall>ps \<in> set gs. \<exists>fs. ?g ps = Some fs \<and> (\<forall>f \<in> set fs. \<exists>N fss. f = FBranch N fss)"
          proof standard
            fix ps
            assume "ps \<in> set gs"
            then obtain k' pre reds where *: "((k', pre), reds) \<in> set gs" "((k', pre), reds) = ps"
              by (metis surj_pair)
            then obtain pres where pres: "build_trees' bs \<omega> k' pre {pre} = Some pres"
              "\<forall>f \<in> set pres. \<exists>N fss. f = FBranch N fss"
              using IH(2) entry pps ps' gs by blast
            have "\<forall>f \<in> set (map (\<lambda>red. build_trees' bs \<omega> k red (I \<union> {red})) reds). \<exists>a. f = Some a"
              using IH(3)[OF entry pps ps' gs *(1)] by auto
            then obtain rss where rss: "Some rss = those (map (\<lambda>red. build_trees' bs \<omega> k red (I \<union> {red})) reds)"
              using those_Some by (metis (full_types))
            let ?h = "\<lambda>f. case f of FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [concat rss])) | _ \<Rightarrow> None"
            have "\<forall>x \<in> set (map ?h pres). \<exists>a. x = Some a"
              using pres(2) by auto
            then obtain fs where fs: "Some fs = those (map ?h pres)"
              using those_Some by (smt (verit, best))
            have "\<forall>f \<in> set fs. \<exists>N fss. f = FBranch N fss"
            proof standard
              fix f
              assume *: "f \<in> set fs"
              hence "\<exists>x. x \<in> set pres \<and> Some f \<in> set (map ?h pres)"
                using those_map_exists[OF fs *] by blast
              then obtain x where x: "x \<in> set pres \<and> Some f \<in> set (map ?h pres)"
                by blast
              thus "\<exists>N fss. f = FBranch N fss"
                using pres(2) by auto
            qed
            moreover have "?g ps = Some fs"
              using fs pres rss * by (auto, metis bind.bind_lunit)
            ultimately show "\<exists>fs. ?g ps = Some fs \<and> (\<forall>f\<in>set fs. \<exists>N fss. f = FBranch N fss)"
              by blast
          qed
          ultimately show "\<exists>fs. fso = Some fs \<and> (\<forall>f \<in> set fs. \<exists>N fss. f = FBranch N fss)"
            using map_Some_P by auto
        qed
        then obtain fss where "those (map ?g gs) = Some fss" "\<forall>fs \<in> set fss. \<forall>f \<in> set fs. \<exists>N fss. f = FBranch N fss"
          using those_Some_P by blast
        hence "build_trees' bs \<omega> k i I = Some (concat fss)" "\<forall>f \<in> set (concat fss). \<exists>N fss. f = FBranch N fss"
          using simp by auto
        thus ?thesis
          by blast
      qed
    qed
    done
  thus ?thesis
    by blast
qed

lemma wf_item_tree_build_trees':
  assumes "(bs, \<omega>, k, i, I) \<in> wf_trees_input"
  assumes "wf_bins \<G> \<omega> bs"
  assumes "k < length bs" "i < length (bs!k)"
  assumes "build_trees' bs \<omega> k i I = Some fs"
  assumes "f \<in> set fs"
  assumes "t \<in> set (trees f)"
  shows "wf_item_tree \<G> (item (bs!k!i)) t"
proof -
  have "wf_item_tree \<G> (item (bs!k!i)) t"
    using assms
    apply (induction arbitrary: fs f t rule: build_trees'_induct[OF assms(1)])
    subgoal premises prems for bs \<omega> k i I fs f t
    proof -
      define e where entry: "e = bs!k!i"
      consider (Null) "pointer e = Null"
        | (Pre) "\<exists>pre. pointer e = Pre pre"
        | (PreRed) "\<exists>p ps. pointer e = PreRed p ps"
        by (metis pointer.exhaust)
      thus ?thesis
      proof cases
        case Null
        hence simp: "build_trees' bs \<omega> k i I = Some ([FBranch (item_rule_head (item e)) []])"
          using entry by simp
        moreover have "f = FBranch (item_rule_head (item e)) []"
          using build_forest'_simps(1) Null prems(8,9) entry by auto
        ultimately have simp: "t = Branch (item_rule_head (item e)) []"
          using prems(10) by simp
        have "sound_ptrs \<omega> bs"
          using prems(4) unfolding wf_trees_input_def by blast
        hence "predicts (item e)"
          using Null prems(6,7) nth_mem entry unfolding sound_ptrs_def sound_null_ptr_def by blast
        hence "item_dot (item e) = 0"
          unfolding predicts_def by blast
        thus ?thesis
          using simp entry by simp
      next
        case Pre
        then obtain pre where pre: "pointer e = Pre pre"
          by blast
        have sound: "sound_ptrs \<omega> bs"
          using prems(4) unfolding wf_trees_input_def by blast
        have scans: "scans \<omega> k (item (bs!(k-1)!pre)) (item e)"
          using entry pre prems(6-7) \<open>sound_ptrs \<omega> bs\<close> unfolding sound_ptrs_def sound_pre_ptr_def by simp
        hence *: 
          "item_rule_head (item (bs!(k-1)!pre)) = item_rule_head (item e)"
          "item_rule_body (item (bs!(k-1)!pre)) = item_rule_body (item e)"
          "item_dot (item (bs!(k-1)!pre)) + 1 = item_dot (item e)"
          "next_symbol (item (bs!(k-1)!pre)) = Some (\<omega>!(k-1))"
          unfolding scans_def inc_item_def by (simp_all add: item_rule_head_def item_rule_body_def)
        have wf: "(bs, \<omega>, k-1, pre, {pre}) \<in> wf_trees_input"
          using entry pre prems(4) wf_trees_input_pre by blast
        then obtain pres where pres: "build_trees' bs \<omega> (k-1) pre {pre} = Some pres"
          "\<forall>f \<in> set pres. \<exists>N fss. f = FBranch N fss"
          using build_trees'_termination wf by blast
        let ?g = "\<lambda>f. case f of FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [[FLeaf (\<omega>!(k-1))]])) | _ \<Rightarrow> None"
        have "build_trees' bs \<omega> k i I = those (map ?g pres)"
          using entry pre pres by simp
        hence fs: "Some fs = those (map ?g pres)"
          using prems(8) by simp
        then obtain f_pre N fss where Nfss: "f = FBranch N (fss @ [[FLeaf (\<omega>!(k-1))]])"
          "f_pre = FBranch N fss" "f_pre \<in> set pres"
          using those_map_FBranch_only fs pres(2) prems(9) by blast
        define tss where tss: "tss = map (\<lambda>fs. concat (map (\<lambda>f. trees f) fs)) fss"
        have "trees (FBranch N (fss @ [[FLeaf (\<omega>!(k-1))]])) = 
          map (\<lambda>ts. Branch N ts) [ ts @ [Leaf (\<omega>!(k-1))] . ts <- combinations tss ]"
          by (subst tss, subst trees_append_single_singleton, simp)
        moreover have "t \<in> set (trees (FBranch N (fss @ [[FLeaf (\<omega>!(k-1))]])))"
          using Nfss(1) prems(10) by blast
        ultimately obtain ts where ts: "t = Branch N (ts @ [Leaf (\<omega>!(k-1))]) \<and> ts \<in> set (combinations tss)"
          by auto
        have "sound_ptrs \<omega> bs"
          using prems(4) unfolding wf_trees_input_def by blast
        hence "pre < length (bs!(k-1))"
          using entry pre prems(6,7) unfolding sound_ptrs_def sound_pre_ptr_def by (metis nth_mem)
        moreover have "k - 1 < length bs"
          by (simp add: prems(6) less_imp_diff_less)
        moreover have "Branch N ts \<in> set (trees (FBranch N fss))"
          using ts tss by simp
        ultimately have IH: "wf_item_tree \<G> (item (bs!(k-1)!pre)) (Branch N ts)"
          using prems(1,2,4,5) entry pre Nfss(2,3) wf pres(1) by blast
        have "map root_tree (ts @ [Leaf (\<omega>!(k-1))]) = map root_tree ts @ [\<omega>!(k-1)]"
          by simp
        also have "... = take (item_dot (item (bs!(k-1)!pre))) (item_rule_body (item (bs!(k-1)!pre))) @ [\<omega>!(k-1)]"
          using IH by simp
        also have "... = take (item_dot (item (bs!(k-1)!pre))) (item_rule_body (item e)) @ [\<omega>!(k-1)]"
          using *(2) by simp
        also have "... = take (item_dot (item e)) (item_rule_body (item e))"
          using *(2-4) by (auto simp: next_symbol_def is_complete_def split: if_splits; metis leI take_Suc_conv_app_nth)
        finally have "map root_tree (ts @ [Leaf (\<omega>!(k-1))]) = take (item_dot (item e)) (item_rule_body (item e))" .
        hence "wf_item_tree \<G> (item e) (Branch N (ts @ [Leaf (\<omega>!(k-1))]))"
          using IH *(1) by simp
        thus ?thesis
          using ts entry by fastforce
      next
        case PreRed
        then obtain p ps where prered: "pointer e = PreRed p ps"
          by blast
        define ps' where ps': "ps' = filter (\<lambda>(k', pre, red). red \<notin> I) (p#ps)"
        define gs where gs: "gs = group_by (\<lambda>(k', pre, red). (k', pre)) (\<lambda>(k', pre, red). red) ps'"
        let ?g = "\<lambda>((k', pre), reds).
            do {
              pres \<leftarrow> build_trees' bs \<omega> k' pre {pre};
              rss \<leftarrow> those (map (\<lambda>red. build_trees' bs \<omega> k red (I \<union> {red})) reds);
              those (map (\<lambda>f.
                case f of
                  FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [concat rss]))
                | _ \<Rightarrow> None \<comment>\<open>impossible case\<close>
              ) pres)
            }"
        have simp: "build_trees' bs \<omega> k i I = map_option concat (those (map ?g gs))"
          using entry prered ps' gs by (subst build_trees'.simps) (auto simp del: filter.simps)
        have "\<forall>fso \<in> set (map ?g gs). \<exists>fs. fso = Some fs \<and> (\<forall>f \<in> set fs. \<forall>t \<in> set (trees f). wf_item_tree \<G> (item (bs!k!i)) t)"
        proof standard
          fix fso
          assume "fso \<in> set (map ?g gs)"
          moreover have "\<forall>ps \<in> set gs. \<exists>fs. ?g ps = Some fs \<and> (\<forall>f \<in> set fs. \<forall>t \<in> set (trees f). wf_item_tree \<G> (item (bs!k!i)) t)"
          proof standard
            fix g
            assume "g \<in> set gs"
            then obtain k' pre reds where g: "((k', pre), reds) \<in> set gs" "((k', pre), reds) = g"
              by (metis surj_pair)
            moreover have wf_pre: "(bs, \<omega>, k', pre, {pre}) \<in> wf_trees_input"
              using wf_trees_input_prered_pre[OF prems(4) entry prered ps' gs g(1)] by blast
            ultimately obtain pres where pres: "build_trees' bs \<omega> k' pre {pre} = Some pres"
              "\<forall>f_pre \<in> set pres. \<exists>N fss. f_pre = FBranch N fss"
              using build_trees'_termination by blast
            have wf_reds: "\<forall>red \<in> set reds. (bs, \<omega>, k, red, I \<union> {red}) \<in> wf_trees_input"
              using wf_trees_input_prered_red[OF prems(4) entry prered ps' gs g(1)] by blast
            hence "\<forall>f \<in> set (map (\<lambda>red. build_trees' bs \<omega> k red (I \<union> {red})) reds). \<exists>a. f = Some a"
              using build_trees'_termination by fastforce
            then obtain rss where rss: "Some rss = those (map (\<lambda>red. build_trees' bs \<omega> k red (I \<union> {red})) reds)"
              using those_Some by (metis (full_types))
            let ?h = "\<lambda>f. case f of FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [concat rss])) | _ \<Rightarrow> None"
            have "\<forall>x \<in> set (map ?h pres). \<exists>a. x = Some a"
              using pres(2) by auto
            then obtain fs where fs: "Some fs = those (map ?h pres)"
              using those_Some by (smt (verit, best))
            have "\<forall>f \<in> set fs. \<forall>t \<in> set (trees f). wf_item_tree \<G> (item (bs!k!i)) t"
            proof (standard, standard)
              fix f t
              assume ft: "f \<in> set fs" "t \<in> set (trees f)"
              hence "\<exists>x. x \<in> set pres \<and> Some f \<in> set (map ?h pres)"
                using those_map_exists[OF fs ft(1)] by blast
              then obtain f_pre N fss where f_pre: "f_pre \<in> set pres" "f_pre = FBranch N fss"
                "f = FBranch N (fss @ [concat rss])"
                using pres(2) by force
              define tss where tss: "tss = map (\<lambda>fs. concat (map (\<lambda>f. trees f) fs)) fss"
              have "trees (FBranch N (fss @ [concat rss])) =
                map (\<lambda>ts. Branch N ts) [ ts0 @ ts1 . ts0 <- combinations tss,
                  ts1 <- combinations [concat (map (\<lambda>f. trees f) (concat rss)) ] ]"
                by (subst tss, subst trees_append_singleton, simp)
              moreover have "t \<in> set (trees (FBranch N (fss @ [concat rss])))"
                using ft(2) f_pre(3) by blast
              ultimately obtain ts0 ts1 where tsx: "t = Branch N (ts0 @ [ts1])" "ts0 \<in> set (combinations tss)"
                "ts1 \<in> set (concat (map (\<lambda>f. trees f) (concat rss)))"
                by fastforce
              then obtain f_red where f_red: "f_red \<in> set (concat rss)" "ts1 \<in> set (trees f_red)"
                by auto
              obtain fs_red red where red: "Some fs_red = build_trees' bs \<omega> k red (I \<union> {red})"
                "f_red \<in> set fs_red" "red \<in> set reds"
                using f_red(1) rss those_map_Some_concat_exists by fast
              then obtain N_red fss_red where "f_red = FBranch N_red fss_red"
                using build_trees'_termination wf_reds by (metis option.inject)
              then obtain ts where ts: "Branch N_red ts = ts1"
                using tsx(3) f_red by auto
              have "(k', pre, red) \<in> set ps'"
                using group_by_forall_v_exists_k \<open>((k', pre), reds) \<in> set gs\<close> gs \<open>red \<in> set reds\<close> by fast
              hence mem: "(k', pre, red) \<in> set (p#ps)"
                using ps' by (metis filter_set member_filter)
              have "sound_ptrs \<omega> bs"
                using prems(4) wf_trees_input_def by fastforce
              have bounds: "k' < k" "pre < length (bs!k')" "red < length (bs!k)"
                using prered entry prems(6,7) \<open>sound_ptrs \<omega> bs\<close>
                unfolding sound_ptrs_def sound_prered_ptr_def by (meson mem nth_mem)+
              have completes: "completes k (item (bs!k'!pre)) (item e) (item (bs!k!red))"
                using prered entry prems(6,7) \<open>sound_ptrs \<omega> bs\<close>
                unfolding sound_ptrs_def sound_prered_ptr_def by (metis mem nth_mem)
              have transform: 
                "item_rule_head (item (bs!k'!pre)) = item_rule_head (item e)"
                "item_rule_body (item (bs!k'!pre)) = item_rule_body (item e)"
                "item_dot (item (bs!k'!pre)) + 1 = item_dot (item e)"
                "next_symbol (item (bs!k'!pre)) = Some (item_rule_head (item (bs!k!red)))"
                "is_complete (item (bs!k!red))"
                using completes unfolding completes_def inc_item_def
                by (auto simp: item_rule_head_def item_rule_body_def is_complete_def)
              have "Branch N ts0 \<in> set (trees (FBranch N fss))"
                using tss tsx(2) by simp
              hence IH_pre: "wf_item_tree \<G> (item (bs!k'!pre)) (Branch N ts0)"
                using prems(2)[OF entry prered ps' gs \<open>((k', pre), reds) \<in> set gs\<close> wf_pre prems(5)]
                  pres(1) f_pre f_pre(3) bounds(1,2) prems(6) by fastforce
              have IH_r: "wf_item_tree \<G> (item (bs!k!red)) (Branch N_red ts)"
                using prems(3)[OF entry prered ps' gs \<open>((k', pre), reds) \<in> set gs\<close> \<open>red \<in> set reds\<close> _ prems(5)]
                  bounds(3) f_red(2) red ts wf_reds prems(6) by metis
              have "map root_tree (ts0 @ [Branch N_red ts]) = map root_tree ts0 @ [root_tree (Branch N_red ts)]"
                by simp
              also have "... = take (item_dot (item (bs!k'!pre))) (item_rule_body (item (bs!k'!pre))) @ [root_tree (Branch N_red ts)]"
                using IH_pre by simp
              also have "... = take (item_dot (item (bs!k'!pre))) (item_rule_body (item (bs!k'!pre))) @ [item_rule_head (item (bs!k!red))]"
                using IH_r by simp
              also have "... = take (item_dot (item e)) (item_rule_body (item e))"
                using transform by (auto simp: next_symbol_def is_complete_def split: if_splits; metis leI take_Suc_conv_app_nth)
              finally have roots: "map root_tree (ts0 @ [Branch N_red ts]) = take (item_dot (item e)) (item_rule_body (item e))" .
              have "wf_item \<G> \<omega> (item (bs!k!red))"
                using prems(5,6) bounds(3) unfolding wf_bins_def wf_bin_def wf_bin_items_def by (auto simp: items_def) 
              moreover have "N_red = item_rule_head (item (bs!k!red))"
                using IH_r by fastforce
              moreover have "map root_tree ts = item_rule_body (item (bs!k!red))"
                using IH_r transform(5) by (auto simp: is_complete_def)
              ultimately have "\<exists>r \<in> set (\<RR> \<G>). N_red = rule_head r \<and> map root_tree ts = rule_body r"
                unfolding wf_item_def item_rule_body_def item_rule_head_def by blast
              hence "wf_rule_tree \<G> (Branch N_red ts)"
                using IH_r by simp
              hence "wf_item_tree \<G> (item (bs!k!i)) (Branch N (ts0 @ [Branch N_red ts]))"
                using transform(1) roots IH_pre entry by simp
              thus "wf_item_tree \<G> (item (bs!k!i)) t"
                using tsx(1) red ts by blast
            qed
            moreover have "?g g = Some fs"
              using fs pres rss g by (auto, metis bind.bind_lunit)
            ultimately show "\<exists>fs. ?g g = Some fs \<and> (\<forall>f \<in> set fs. \<forall>t \<in> set (trees f). wf_item_tree \<G> (item (bs!k!i)) t)"
              by blast
          qed
          ultimately show "\<exists>fs. fso = Some fs \<and> (\<forall>f \<in> set fs. \<forall>t \<in> set (trees f). wf_item_tree \<G> (item (bs!k!i)) t)"
            using map_Some_P by auto
        qed
        then obtain fss where "those (map ?g gs) = Some fss" "\<forall>fs \<in> set fss. \<forall>f \<in> set fs. \<forall>t \<in> set (trees f). wf_item_tree \<G> (item (bs!k!i)) t"
          using those_Some_P by blast
        hence "build_trees' bs \<omega> k i I = Some (concat fss)" "\<forall>f \<in> set (concat fss). \<forall>t \<in> set (trees f). wf_item_tree \<G> (item (bs!k!i)) t"
          using simp by auto
        thus ?thesis
          using prems(8-10) by auto
      qed
    qed
    done
  thus ?thesis
    by blast
qed

lemma wf_yield_tree_build_trees':
  assumes "(bs, \<omega>, k, i, I) \<in> wf_trees_input"
  assumes "wf_bins \<G> \<omega> bs"
  assumes "k < length bs" "i < length (bs!k)" "k \<le> length \<omega>"
  assumes "build_trees' bs \<omega> k i I = Some fs"
  assumes "f \<in> set fs"
  assumes "t \<in> set (trees f)"
  shows "wf_yield_tree \<omega> (item (bs!k!i)) t"
proof -
  have "wf_yield_tree \<omega> (item (bs!k!i)) t"
    using assms
    apply (induction arbitrary: fs f t rule: build_trees'_induct[OF assms(1)])
    subgoal premises prems for bs \<omega> k i I fs f t
    proof -
      define e where entry: "e = bs!k!i"
      consider (Null) "pointer e = Null"
        | (Pre) "\<exists>pre. pointer e = Pre pre"
        | (PreRed) "\<exists>p ps. pointer e = PreRed p ps"
        by (metis pointer.exhaust)
      thus ?thesis
      proof cases
        case Null
        hence simp: "build_trees' bs \<omega> k i I = Some ([FBranch (item_rule_head (item e)) []])"
          using entry by simp
        moreover have "f = FBranch (item_rule_head (item e)) []"
          using build_forest'_simps(1) Null prems(9,10) entry by auto
        ultimately have simp: "t = Branch (item_rule_head (item e)) []"
          using prems(11) by simp
        have "sound_ptrs \<omega> bs"
          using prems(4) unfolding wf_trees_input_def by blast
        hence "predicts (item e)"
          using Null prems(6,7) nth_mem entry unfolding sound_ptrs_def sound_null_ptr_def by blast
        thus ?thesis
          unfolding wf_yield_tree_def predicts_def using simp entry by (auto simp: slice_empty)
      next
        case Pre
        then obtain pre where pre: "pointer e = Pre pre"
          by blast
        have sound: "sound_ptrs \<omega> bs"
          using prems(4) unfolding wf_trees_input_def by blast
        hence bounds:  "k > 0" "pre < length (bs!(k-1))"
          using entry pre prems(6,7) unfolding sound_ptrs_def sound_pre_ptr_def by (metis nth_mem)+
        have scans: "scans \<omega> k (item (bs!(k-1)!pre)) (item e)"
          using entry pre prems(6-7) \<open>sound_ptrs \<omega> bs\<close> unfolding sound_ptrs_def sound_pre_ptr_def by simp
        have wf: "(bs, \<omega>, k-1, pre, {pre}) \<in> wf_trees_input"
          using entry pre prems(4) wf_trees_input_pre by blast
        then obtain pres where pres: "build_trees' bs \<omega> (k-1) pre {pre} = Some pres"
          "\<forall>f \<in> set pres. \<exists>N fss. f = FBranch N fss"
          using build_trees'_termination wf by blast
        let ?g = "\<lambda>f. case f of FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [[FLeaf (\<omega>!(k-1))]])) | _ \<Rightarrow> None"
        have "build_trees' bs \<omega> k i I = those (map ?g pres)"
          using entry pre pres by simp
        hence fs: "Some fs = those (map ?g pres)"
          using prems(9) by simp
        then obtain f_pre N fss where Nfss: "f = FBranch N (fss @ [[FLeaf (\<omega>!(k-1))]])"
          "f_pre = FBranch N fss" "f_pre \<in> set pres"
          using those_map_FBranch_only fs pres(2) prems(10) by blast
        define tss where tss: "tss = map (\<lambda>fs. concat (map (\<lambda>f. trees f) fs)) fss"
        have "trees (FBranch N (fss @ [[FLeaf (\<omega>!(k-1))]])) = 
          map (\<lambda>ts. Branch N ts) [ ts @ [Leaf (\<omega>!(k-1))] . ts <- combinations tss ]"
          by (subst tss, subst trees_append_single_singleton, simp)
        moreover have "t \<in> set (trees (FBranch N (fss @ [[FLeaf (\<omega>!(k-1))]])))"
          using Nfss(1) prems(11) by blast
        ultimately obtain ts where ts: "t = Branch N (ts @ [Leaf (\<omega>!(k-1))]) \<and> ts \<in> set (combinations tss)"
          by auto
        have "sound_ptrs \<omega> bs"
          using prems(4) unfolding wf_trees_input_def by blast
        hence "pre < length (bs!(k-1))"
          using entry pre prems(6,7) unfolding sound_ptrs_def sound_pre_ptr_def by (metis nth_mem)
        moreover have "k-1 < length bs"
          by (simp add: prems(6) less_imp_diff_less)
        moreover have "Branch N ts \<in> set (trees (FBranch N fss))"
          using ts tss by simp
        ultimately have IH: "wf_yield_tree \<omega> (item (bs!(k-1)!pre)) (Branch N ts)"
          using prems(1,2,4,5,8) entry pre Nfss(2,3) wf pres(1) by simp
        have transform: 
          "item_origin (item (bs!(k-1)!pre)) \<le> item_end (item (bs!(k-1)!pre))"
          "item_end (item (bs!(k-1)!pre)) = k-1"
          "item_end (item e) = k"
          using entry prems(5,6,7) bounds unfolding wf_bins_def wf_bin_def wf_bin_items_def items_def wf_item_def
          by (auto, meson less_imp_diff_less nth_mem)
        have "yield_tree t = concat (map yield_tree (ts @ [Leaf (\<omega>!(k-1))]))"
          by (simp add: ts)
        also have "... = concat (map yield_tree ts) @ [\<omega>!(k-1)]"
          by simp
        also have "... = slice (item_origin (item (bs!(k-1)!pre))) (item_end (item (bs!(k-1)!pre))) \<omega> @ [\<omega>!(k-1)]"
          using IH by (simp add: wf_yield_tree_def)
        also have "... = slice (item_origin (item (bs!(k-1)!pre))) (item_end (item (bs!(k-1)!pre)) + 1) \<omega>"
          using slice_append_nth transform \<open>k > 0\<close> prems(8)
          by (metis diff_less le_eq_less_or_eq less_imp_diff_less less_numeral_extra(1))
        also have "... = slice (item_origin (item e)) (item_end (item (bs!(k-1)!pre)) + 1) \<omega>"
          using scans unfolding scans_def inc_item_def by simp
        also have "... = slice (item_origin (item e)) k \<omega>"
          using scans transform unfolding scans_def by (metis Suc_diff_1 Suc_eq_plus1 bounds(1))
        also have "... = slice (item_origin (item e)) (item_end (item e)) \<omega>"
          using transform by auto
        finally show ?thesis
          using wf_yield_tree_def entry by blast
      next
        case PreRed
        then obtain p ps where prered: "pointer e = PreRed p ps"
          by blast
        define ps' where ps': "ps' = filter (\<lambda>(k', pre, red). red \<notin> I) (p#ps)"
        define gs where gs: "gs = group_by (\<lambda>(k', pre, red). (k', pre)) (\<lambda>(k', pre, red). red) ps'"
        let ?g = "\<lambda>((k', pre), reds).
            do {
              pres \<leftarrow> build_trees' bs \<omega> k' pre {pre};
              rss \<leftarrow> those (map (\<lambda>red. build_trees' bs \<omega> k red (I \<union> {red})) reds);
              those (map (\<lambda>f.
                case f of
                  FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [concat rss]))
                | _ \<Rightarrow> None \<comment>\<open>impossible case\<close>
              ) pres)
            }"
        have simp: "build_trees' bs \<omega> k i I = map_option concat (those (map ?g gs))"
          using entry prered ps' gs by (subst build_trees'.simps) (auto simp del: filter.simps)
        have "\<forall>fso \<in> set (map ?g gs). \<exists>fs. fso = Some fs \<and> (\<forall>f \<in> set fs. \<forall>t \<in> set (trees f). wf_yield_tree \<omega> (item (bs!k!i)) t)"
        proof standard
          fix fso
          assume "fso \<in> set (map ?g gs)"
          moreover have "\<forall>ps \<in> set gs. \<exists>fs. ?g ps = Some fs \<and> (\<forall>f \<in> set fs. \<forall>t \<in> set (trees f). wf_yield_tree \<omega> (item (bs!k!i)) t)"
          proof standard
            fix g
            assume "g \<in> set gs"
            then obtain k' pre reds where g: "((k', pre), reds) \<in> set gs" "((k', pre), reds) = g"
              by (metis surj_pair)
            moreover have wf_pre: "(bs, \<omega>, k', pre, {pre}) \<in> wf_trees_input"
              using wf_trees_input_prered_pre[OF prems(4) entry prered ps' gs g(1)] by blast
            ultimately obtain pres where pres: "build_trees' bs \<omega> k' pre {pre} = Some pres"
              "\<forall>f_pre \<in> set pres. \<exists>N fss. f_pre = FBranch N fss"
              using build_trees'_termination by blast
            have wf_reds: "\<forall>red \<in> set reds. (bs, \<omega>, k, red, I \<union> {red}) \<in> wf_trees_input"
              using wf_trees_input_prered_red[OF prems(4) entry prered ps' gs g(1)] by blast
            hence "\<forall>f \<in> set (map (\<lambda>red. build_trees' bs \<omega> k red (I \<union> {red})) reds). \<exists>a. f = Some a"
              using build_trees'_termination by fastforce
            then obtain rss where rss: "Some rss = those (map (\<lambda>red. build_trees' bs \<omega> k red (I \<union> {red})) reds)"
              using those_Some by (metis (full_types))
            let ?h = "\<lambda>f. case f of FBranch N fss \<Rightarrow> Some (FBranch N (fss @ [concat rss])) | _ \<Rightarrow> None"
            have "\<forall>x \<in> set (map ?h pres). \<exists>a. x = Some a"
              using pres(2) by auto
            then obtain fs where fs: "Some fs = those (map ?h pres)"
              using those_Some by (smt (verit, best))
            have "\<forall>f \<in> set fs. \<forall>t \<in> set (trees f). wf_yield_tree \<omega> (item (bs!k!i)) t"
            proof (standard, standard)
              fix f t
              assume ft: "f \<in> set fs" "t \<in> set (trees f)"
              hence "\<exists>x. x \<in> set pres \<and> Some f \<in> set (map ?h pres)"
                using those_map_exists[OF fs ft(1)] by blast
              then obtain f_pre N fss where f_pre: "f_pre \<in> set pres" "f_pre = FBranch N fss"
                "f = FBranch N (fss @ [concat rss])"
                using pres(2) by force
              define tss where tss: "tss = map (\<lambda>fs. concat (map (\<lambda>f. trees f) fs)) fss"
              have "trees (FBranch N (fss @ [concat rss])) =
                map (\<lambda>ts. Branch N ts) [ ts0 @ ts1 . ts0 <- combinations tss,
                  ts1 <- combinations [concat (map (\<lambda>f. trees f) (concat rss)) ] ]"
                by (subst tss, subst trees_append_singleton, simp)
              moreover have "t \<in> set (trees (FBranch N (fss @ [concat rss])))"
                using ft(2) f_pre(3) by blast
              ultimately obtain ts0 ts1 where tsx: "t = Branch N (ts0 @ [ts1])" "ts0 \<in> set (combinations tss)"
                "ts1 \<in> set (concat (map (\<lambda>f. trees f) (concat rss)))"
                by fastforce
              then obtain f_red where f_red: "f_red \<in> set (concat rss)" "ts1 \<in> set (trees f_red)"
                by auto
              obtain fs_red red where red: "Some fs_red = build_trees' bs \<omega> k red (I \<union> {red})"
                "f_red \<in> set fs_red" "red \<in> set reds"
                using f_red(1) rss those_map_Some_concat_exists by fast
              then obtain N_red fss_red where "f_red = FBranch N_red fss_red"
                using build_trees'_termination wf_reds by (metis option.inject)
              then obtain ts where ts: "Branch N_red ts = ts1"
                using tsx(3) f_red by auto
              have "(k', pre, red) \<in> set ps'"
                using group_by_forall_v_exists_k \<open>((k', pre), reds) \<in> set gs\<close> gs \<open>red \<in> set reds\<close> by fast
              hence mem: "(k', pre, red) \<in> set (p#ps)"
                using ps' by (metis filter_set member_filter)
              have "sound_ptrs \<omega> bs"
                using prems(4) wf_trees_input_def by fastforce
              have bounds: "k' < k" "pre < length (bs!k')" "red < length (bs!k)"
                using prered entry prems(6,7) \<open>sound_ptrs \<omega> bs\<close>
                unfolding sound_ptrs_def sound_prered_ptr_def by (meson mem nth_mem)+
              have completes: "completes k (item (bs!k'!pre)) (item e) (item (bs!k!red))"
                using prered entry prems(6,7) \<open>sound_ptrs \<omega> bs\<close>
                unfolding sound_ptrs_def sound_prered_ptr_def by (metis mem nth_mem)
              have transform: 
                "item_rule_head (item (bs!k'!pre)) = item_rule_head (item e)"
                "item_rule_body (item (bs!k'!pre)) = item_rule_body (item e)"
                "item_dot (item (bs!k'!pre)) + 1 = item_dot (item e)"
                "next_symbol (item (bs!k'!pre)) = Some (item_rule_head (item (bs!k!red)))"
                "is_complete (item (bs!k!red))"
                using completes unfolding completes_def inc_item_def
                by (auto simp: item_rule_head_def item_rule_body_def is_complete_def)
              have "Branch N ts0 \<in> set (trees (FBranch N fss))"
                using tss tsx(2) by simp
              hence IH_pre: "wf_yield_tree \<omega> (item (bs!k'!pre)) (Branch N ts0)"
                using prems(2)[OF entry prered ps' gs \<open>((k', pre), reds) \<in> set gs\<close> wf_pre prems(5)]
                  pres(1) f_pre f_pre(3) bounds(1,2) prems(6,8) by simp
              have IH_r: "wf_yield_tree \<omega> (item (bs!k!red)) (Branch N_red ts)"
                using prems(3)[OF entry prered ps' gs \<open>((k', pre), reds) \<in> set gs\<close> \<open>red \<in> set reds\<close> _ prems(5)]
                  bounds(3) f_red(2) red ts wf_reds prems(6,8) by metis
              have wf1: 
                "item_origin (item (bs!k'!pre)) \<le> item_end (item (bs!k'!pre))"
                "item_origin (item (bs!k!red)) \<le> item_end (item (bs!k!red))"
                using prems(5-7) bounds unfolding wf_bins_def wf_bin_def wf_bin_items_def items_def wf_item_def
                by (metis length_map nth_map nth_mem order_less_trans)+
              have wf2:
                "item_end (item (bs!k!red)) = k"
                "item_end (item (bs!k!i)) = k"
                using prems(5-7) bounds unfolding wf_bins_def wf_bin_def wf_bin_items_def items_def by simp_all
              have "yield_tree t = concat (map yield_tree (ts0 @ [Branch N_red ts]))"
                by (simp add: ts tsx(1))
              also have "... = concat (map yield_tree ts0) @ yield_tree (Branch N_red ts)"
                by simp
              also have "... = slice (item_origin (item (bs!k'!pre))) (item_end (item (bs!k'!pre))) \<omega> @ 
                slice (item_origin (item (bs!k!red))) (item_end (item (bs!k!red))) \<omega>"
                using IH_pre IH_r by (simp add: wf_yield_tree_def)
              also have "... = slice (item_origin (item (bs!k'!pre))) (item_end (item (bs!k!red))) \<omega>"
                using slice_concat wf1 completes_def completes by (metis (no_types, lifting))
              also have "... = slice (item_origin (item e)) (item_end (item (bs!k!red))) \<omega>"
                using completes unfolding completes_def inc_item_def by simp
              also have "... = slice (item_origin (item e)) (item_end (item e)) \<omega>"
                using wf2 entry by presburger
              finally show "wf_yield_tree \<omega> (item (bs!k!i)) t"
                using wf_yield_tree_def entry by blast
            qed
            moreover have "?g g = Some fs"
              using fs pres rss g by (auto, metis bind.bind_lunit)
            ultimately show "\<exists>fs. ?g g = Some fs \<and> (\<forall>f \<in> set fs. \<forall>t \<in> set (trees f). wf_yield_tree \<omega> (item (bs!k!i)) t)"
              by blast
          qed
          ultimately show "\<exists>fs. fso = Some fs \<and> (\<forall>f \<in> set fs. \<forall>t \<in> set (trees f). wf_yield_tree \<omega> (item (bs!k!i)) t)"
            using map_Some_P by auto
        qed
        then obtain fss where "those (map ?g gs) = Some fss" "\<forall>fs \<in> set fss. \<forall>f \<in> set fs. \<forall>t \<in> set (trees f). wf_yield_tree \<omega> (item (bs!k!i)) t"
          using those_Some_P by blast
        hence "build_trees' bs \<omega> k i I = Some (concat fss)" "\<forall>f \<in> set (concat fss). \<forall>t \<in> set (trees f). wf_yield_tree \<omega> (item (bs!k!i)) t"
          using simp by auto
        thus ?thesis
          using prems(9-11) by auto
      qed
    qed
    done
  thus ?thesis
    using assms(2) by blast
qed

theorem wf_rule_root_yield_tree_build_trees:
  assumes "wf_bins \<G> \<omega> bs" "sound_ptrs \<omega> bs" "length bs = length \<omega> + 1"
  assumes "build_trees \<G> \<omega> bs = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "wf_rule_tree \<G> t \<and> root_tree t = \<SS> \<G> \<and> yield_tree t = \<omega>"
proof -
  let ?k = "length bs - 1"
  define finished where finished_def: "finished = filter_with_index (is_finished \<G> \<omega>) (items (bs!?k))"
  have #: "Some fs = map_option concat (those (map (\<lambda>(_, i). build_trees' bs \<omega> ?k i {i}) finished))"
    using assms(4) build_trees_def finished_def by (metis (full_types))
  then obtain fss fs' where fss: "Some fss = those (map (\<lambda>(_, i). build_trees' bs \<omega> ?k i {i}) finished)"
    "fs' \<in> set fss" "f \<in> set fs'"
    using map_option_concat_those_map_exists assms(5) by fastforce
  then obtain x i where *: "(x,i) \<in> set finished" "Some fs' =  build_trees' bs \<omega> (length bs - 1) i {i}"
    using those_map_exists[OF fss(1,2)] by auto
  have k: "?k < length bs" "?k \<le> length \<omega>"
    using assms(3) by simp_all
  have i: "i < length (bs!?k)"
    using index_filter_with_index_lt_length * items_def finished_def by (metis (no_types, opaque_lifting) length_map)
  have x: "x = item (bs!?k!i)"
    using * i filter_with_index_nth items_def nth_map finished_def assms(3) by metis
  have finished: "is_finished \<G> \<omega> x"
    using * filter_with_index_P finished_def by metis
  have "{i} \<subseteq> {0..<length (bs!?k)}"
    using atLeastLessThan_iff i by blast
  hence wf: "(bs, \<omega>, ?k, i, {i}) \<in> wf_trees_input"
    unfolding wf_trees_input_def using assms(2) i k(1) by simp
  hence wf_item_tree: "wf_item_tree \<G> (item (bs!?k!i)) t"
    using wf_item_tree_build_trees' assms(1,2,5,6) i k(1) x *(2) fss(3) by metis
  have wf_item: "wf_item \<G> \<omega> (item (bs!?k!i))"
    using k(1) i assms(1) unfolding wf_bins_def wf_bin_def wf_bin_items_def by (simp add: items_def)
  obtain N fss where Nfss: "f = FBranch N fss"
    using build_trees'_termination[OF wf] by (metis "*"(2) fss(3) option.inject)
  then obtain ts where ts: "t = Branch N ts"
    using assms(6) by auto
  hence "N = item_rule_head x"
    "map root_tree ts = item_rule_body x"
    using finished wf_item_tree x by (auto simp: is_finished_def is_complete_def)
  hence "\<exists>r \<in> set (\<RR> \<G>). N = rule_head r \<and> map root_tree ts = rule_body r"
    using wf_item x unfolding wf_item_def item_rule_body_def item_rule_head_def by blast
  hence wf_rule: "wf_rule_tree \<G> t"
    using wf_item_tree ts by simp
  have root: "root_tree t = \<SS> \<G>"
    using finished ts \<open>N = item_rule_head x\<close> by (auto simp: is_finished_def)
  have "yield_tree t = slice (item_origin (item (bs!?k!i))) (item_end (item (bs!?k!i))) \<omega>"
    using k i assms(1,6) wf wf_yield_tree_build_trees' wf_yield_tree_def *(2) fss(3) by (smt (verit, best))
  hence yield: "yield_tree t = \<omega>"
    using finished x unfolding is_finished_def by simp
  show ?thesis
    using * wf_rule root yield assms(4) unfolding build_trees_def by simp
qed

corollary wf_rule_root_yield_tree_build_trees_Earley\<^sub>L:
  assumes "wf_\<G> \<G>" "nonempty_derives \<G>"
  assumes "build_trees \<G> \<omega> (Earley\<^sub>L \<G> \<omega>) = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "wf_rule_tree \<G> t \<and> root_tree t = \<SS> \<G> \<and> yield_tree t = \<omega>"
  using assms wf_rule_root_yield_tree_build_trees wf_bins_Earley\<^sub>L Earley\<^sub>L_def
    length_Earley\<^sub>L_bins length_bins_Init\<^sub>L sound_mono_ptrs_Earley\<^sub>L
  by (metis dual_order.eq_iff )

theorem soundness_build_trees_Earley\<^sub>L:
  assumes "wf_\<G> \<G>" "is_word \<G> \<omega>" "nonempty_derives \<G>"
  assumes "build_trees \<G> \<omega> (Earley\<^sub>L \<G> \<omega>) = Some fs" "f \<in> set fs" "t \<in> set (trees f)"
  shows "derives \<G> [\<SS> \<G>] \<omega>"
proof -
  let ?k = "length (Earley\<^sub>L \<G> \<omega>) - 1"
  define finished where finished_def: "finished = filter_with_index (is_finished \<G> \<omega>) (items ((Earley\<^sub>L \<G> \<omega>)!?k))"
  have #: "Some fs = map_option concat (those (map (\<lambda>(_, i). build_trees' (Earley\<^sub>L \<G> \<omega>) \<omega> ?k i {i}) finished))"
    using assms(4) build_trees_def finished_def by (metis (full_types))
  then obtain fss fs' where fss: "Some fss = those (map (\<lambda>(_, i). build_trees' (Earley\<^sub>L \<G> \<omega>) \<omega> ?k i {i}) finished)"
    "fs' \<in> set fss" "f \<in> set fs'"
    using map_option_concat_those_map_exists assms(5) by fastforce
  then obtain x i where *: "(x,i) \<in> set finished" "Some fs' =  build_trees' (Earley\<^sub>L \<G> \<omega>) \<omega> ?k i {i}"
    using those_map_exists[OF fss(1,2)] by auto
  have k: "?k < length (Earley\<^sub>L \<G> \<omega>)" "?k \<le> length \<omega>"
    by (simp_all add: Earley\<^sub>L_def assms(1))
  have i: "i < length ((Earley\<^sub>L \<G> \<omega>) ! ?k)"
    using index_filter_with_index_lt_length * items_def finished_def by (metis length_map)
  have x: "x = item ((Earley\<^sub>L \<G> \<omega>)!?k!i)"
    using * i filter_with_index_nth items_def nth_map finished_def by metis
  have finished: "is_finished \<G> \<omega> x"
    using * filter_with_index_P finished_def by metis
  moreover have "x \<in> set (items ((Earley\<^sub>L \<G> \<omega>) ! ?k))"
    using x by (auto simp: items_def; metis One_nat_def i imageI nth_mem)
  ultimately have "recognizing (bins (Earley\<^sub>L \<G> \<omega>)) \<G> \<omega>"
    by (meson k(1) kth_bin_sub_bins recognizing_def subsetD)
  thus ?thesis
    using correctness_Earley\<^sub>L assms by blast
qed

theorem termination_build_tree_Earley\<^sub>L:
  assumes "wf_\<G> \<G>" "nonempty_derives \<G>" "derives \<G> [\<SS> \<G>] \<omega>"
  shows "\<exists>fs. build_trees \<G> \<omega> (Earley\<^sub>L \<G> \<omega>) = Some fs"
proof -
  let ?k = "length (Earley\<^sub>L \<G> \<omega>) - 1"
  define finished where finished_def: "finished = filter_with_index (is_finished \<G> \<omega>) (items ((Earley\<^sub>L \<G> \<omega>)!?k))"
  have "\<forall>f \<in> set finished. (Earley\<^sub>L \<G> \<omega>, \<omega>, ?k, snd f, {snd f}) \<in> wf_trees_input"
  proof standard
    fix f
    assume a: "f \<in> set finished"
    then obtain x i where *: "(x,i) = f"
      by (metis surj_pair)
    have "sound_ptrs \<omega> (Earley\<^sub>L \<G> \<omega>)"
      using sound_mono_ptrs_Earley\<^sub>L assms by blast
    moreover have "?k < length (Earley\<^sub>L \<G> \<omega>)"
      by (simp add: Earley\<^sub>L_def assms(1))
    moreover have "i < length ((Earley\<^sub>L \<G> \<omega>)!?k)"
      using index_filter_with_index_lt_length a * items_def finished_def by (metis length_map)
    ultimately show "(Earley\<^sub>L \<G> \<omega>, \<omega>, ?k, snd f, {snd f}) \<in> wf_trees_input"
      using * unfolding wf_trees_input_def by auto
  qed
  hence "\<forall>fso \<in> set (map (\<lambda>(_, i). build_trees' (Earley\<^sub>L \<G> \<omega>) \<omega> ?k i {i}) finished). \<exists>fs. fso = Some fs"
    using build_trees'_termination by fastforce
  then obtain fss where fss: "Some fss = those (map (\<lambda>(_, i). build_trees' (Earley\<^sub>L \<G> \<omega>) \<omega> ?k i {i}) finished)"
    by (smt (verit, best) those_Some)
  then obtain fs where fs: "Some fs = map_option concat (those (map (\<lambda>(_, i). build_trees' (Earley\<^sub>L \<G> \<omega>) \<omega> ?k i {i}) finished))"
    by (metis map_option_eq_Some)
  show ?thesis
    using finished_def fss fs build_trees_def by (metis (full_types))
qed

end