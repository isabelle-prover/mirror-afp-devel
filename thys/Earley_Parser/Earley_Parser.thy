theory Earley_Parser
  imports
    Earley_Recognizer
    "HOL-Library.Monad_Syntax"
begin

section \<open>Earley parser\<close>

subsection \<open>Pointer lemmas\<close>

definition predicts :: "'a item \<Rightarrow> bool" where
  "predicts x \<equiv> start_item x = end_item x \<and> dot_item x = 0"

definition scans :: "'a list \<Rightarrow> nat \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> bool" where
  "scans \<omega> k x y \<equiv> y = inc_item x k \<and> (\<exists>a. next_symbol x = Some a \<and> \<omega>!(k-1) = a)"

definition completes :: "nat \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> 'a item \<Rightarrow> bool" where
  "completes k x y z \<equiv> y = inc_item x k \<and> is_complete z \<and> start_item z = end_item x \<and>
    (\<exists>N. next_symbol x = Some N \<and> N = lhs_item z)"

definition sound_null_ptr :: "'a item \<times> pointer \<Rightarrow> bool" where
  "sound_null_ptr e \<equiv> (snd e = Null \<longrightarrow> predicts (fst e))"

definition sound_pre_ptr :: "'a list \<Rightarrow> 'a bins \<Rightarrow> nat \<Rightarrow> 'a item \<times> pointer \<Rightarrow> bool" where
  "sound_pre_ptr \<omega> bs k e \<equiv> \<forall>pre. snd e = Pre pre \<longrightarrow>
    k > 0 \<and> pre < length (bs!(k-1)) \<and> scans \<omega> k (fst (bs!(k-1)!pre)) (fst e)"

definition sound_prered_ptr :: "'a bins \<Rightarrow> nat \<Rightarrow> 'a item \<times> pointer \<Rightarrow> bool" where
  "sound_prered_ptr bs k e \<equiv> \<forall>p ps k' pre red. snd e = PreRed p ps \<and> (k', pre, red) \<in> set (p#ps) \<longrightarrow>
    k' < k \<and> pre < length (bs!k') \<and> red < length (bs!k) \<and> completes k (fst (bs!k'!pre)) (fst e) (fst (bs!k!red))"

definition sound_ptrs :: "'a list \<Rightarrow> 'a bins \<Rightarrow> bool" where
  "sound_ptrs \<omega> bs \<equiv> \<forall>k < length bs. \<forall>e \<in> set (bs!k).
    sound_null_ptr e \<and> sound_pre_ptr \<omega> bs k e \<and> sound_prered_ptr bs k e"

definition mono_red_ptr :: "'a bins \<Rightarrow> bool" where
  "mono_red_ptr bs \<equiv> \<forall>k < length bs. \<forall>i < length (bs!k).
    \<forall>k' pre red ps. snd (bs!k!i) = PreRed (k', pre, red) ps \<longrightarrow> red < i"

lemma nth_item_upd_bin:
  "n < length es \<Longrightarrow> fst (upd_bin e es ! n) = fst (es!n)"
  by (induction es arbitrary: e n) (auto simp: less_Suc_eq_0_disj split: prod.splits pointer.splits)

lemma upd_bin_append:
  "fst e \<notin> set (items es) \<Longrightarrow> upd_bin e es = es @ [e]"
  by (induction es arbitrary: e) (auto simp: items_def split: prod.splits pointer.splits)

lemma upd_bin_null_pre:
  "fst e \<in> set (items es) \<Longrightarrow> snd e = Null \<or> snd e = Pre pre \<Longrightarrow> upd_bin e es = es"
  by (induction es arbitrary: e) (auto simp: items_def split: prod.splits, fastforce+)

lemma upd_bin_prered_nop:
  assumes "distinct (items es)" "i < length es"
  assumes "fst e = fst (es!i)" "snd e = PreRed p ps" "\<nexists>p ps. snd (es!i) = PreRed p ps"
  shows "upd_bin e es = es"
  using assms
  by (induction es arbitrary: e i) (auto simp: less_Suc_eq_0_disj items_def split: prod.splits pointer.splits)

lemma upd_bin_prered_upd:
  assumes "distinct (items es)" "i < length es"
  assumes "fst e = fst (es!i)" "snd e = PreRed p rs" "snd (es!i) = PreRed p' rs'" "upd_bin e es = es'"
  shows "snd (es'!i) = PreRed p' (p#rs@rs') \<and> (\<forall>j < length es'. i\<noteq>j \<longrightarrow> es'!j = es!j) \<and> length (upd_bin e es) = length es"
  using assms
proof (induction es arbitrary: e i es')
  case (Cons e' es)
  show ?case
  proof cases
    assume *: "fst e = fst e'"
    show ?thesis
    proof (cases "\<exists>x xp xs y yp ys. e = (x, PreRed xp xs) \<and> e' = (y, PreRed yp ys)")
      case True
      then obtain x xp xs y yp ys where ee': "e = (x, PreRed xp xs)" "e' = (y, PreRed yp ys)" "x = y"
        using * by auto
      have simp: "upd_bin e (e' # es') = (x, PreRed yp (xp # xs @ ys)) # es'"
        using True ee' by simp
      show ?thesis
        using Cons simp ee' apply (auto simp: items_def)
        using less_Suc_eq_0_disj by fastforce+
    next
      case False
      hence "upd_bin e (e' # es') = e' # es'"
        using * by (auto split: pointer.splits prod.splits)
      thus ?thesis
        using False * Cons.prems(1,2,3,4,5) by (auto simp: less_Suc_eq_0_disj items_def split: prod.splits)
    qed
  next
    assume *: "fst e \<noteq> fst e'"
    have simp: "upd_bin e (e' # es) = e' # upd_bin e es"
      using * by (auto split: pointer.splits prod.splits)
    have 0: "distinct (items es)"
      using Cons.prems(1) unfolding items_def by simp
    have 1: "i-1 < length es"
      using Cons.prems(2,3) * by (metis One_nat_def leI less_diff_conv2 less_one list.size(4) nth_Cons_0)
    have 2: "fst e = fst (es!(i-1))"
      using Cons.prems(3) * by (metis nth_Cons')
    have 3: "snd e = PreRed p rs"
      using Cons.prems(4) by simp
    have 4: "snd (es!(i-1)) = PreRed p' rs' "
      using Cons.prems(3,5) * by (metis nth_Cons')
    have "snd (upd_bin e es!(i-1)) = PreRed p' (p # rs @ rs') \<and>
      (\<forall>j < length (upd_bin e es). i-1 \<noteq> j \<longrightarrow> (upd_bin e es) ! j = es ! j)"
      using Cons.IH[OF 0 1 2 3 4] by blast
    hence "snd ((e' # upd_bin e es) ! i) = PreRed p' (p # rs @ rs') \<and>
      (\<forall>j < length (e' # upd_bin e es). i \<noteq> j \<longrightarrow> (e' # upd_bin e es) ! j = (e' # es) ! j)"
      using * Cons.prems(2,3) less_Suc_eq_0_disj by auto
    moreover have "e' # upd_bin e es = es'"
      using Cons.prems(6) simp by auto
    ultimately show ?thesis
      by (metis 0 1 2 3 4 Cons.IH Cons.prems(6) length_Cons)
  qed
qed simp

lemma sound_ptrs_upd_bin:
  assumes "sound_ptrs \<omega> bs" "k < length bs" "es = bs!k" "distinct (items es)"
  assumes "sound_null_ptr e" "sound_pre_ptr \<omega> bs k e" "sound_prered_ptr bs k e"
  shows "sound_ptrs \<omega> (bs[k := upd_bin e es])"
  unfolding sound_ptrs_def
proof (standard, standard, standard)
  fix idx elem
  let ?bs = "bs[k := upd_bin e es]"
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
    hence prered_es: "elem \<in> set es \<Longrightarrow> sound_prered_ptr (bs[k := upd_bin e es]) idx elem"
      using a2 assms(2,3) length_upd_bin nth_item_upd_bin unfolding sound_prered_ptr_def
      by (smt (verit, ccfv_SIG) dual_order.strict_trans1 nth_list_update)
    have "elem = e \<Longrightarrow> sound_prered_ptr bs idx elem"
      using a2 assms(7) by auto
    hence prered_e: "elem = e \<Longrightarrow> sound_prered_ptr ?bs idx elem"
      using a2 assms(2,3) length_upd_bin nth_item_upd_bin unfolding sound_prered_ptr_def
      by (smt (verit, best) dual_order.strict_trans1 nth_list_update)
    consider (A) "fst e \<notin> set (items es)" |
      (B) "fst e \<in> set (items es) \<and> (\<exists>pre. snd e = Null \<or> snd e = Pre pre)" |
      (C) "fst e \<in> set (items es) \<and> \<not> (\<exists>pre. snd e = Null \<or> snd e = Pre pre)"
      by blast
    thus ?thesis
    proof cases
      case A
      hence "elem \<in> set (es @ [e])"
        using a1 a2 upd_bin_append assms(2) by fastforce
      thus ?thesis
        using assms(1-3,5) pre_e pre_es prered_e prered_es sound_ptrs_def by auto
    next
      case B
      hence "elem \<in> set es"
        using a1 a2 upd_bin_null_pre assms(2) by fastforce
      thus ?thesis
        using assms(1-3) pre_es prered_es sound_ptrs_def by blast
    next
      case C
      then obtain i p ps where C: "i < length es \<and> fst e = fst (es!i) \<and> snd e = PreRed p ps"
        by (metis assms(4) distinct_Ex1 items_def length_map nth_map pointer.exhaust)
      show ?thesis
      proof cases
        assume "\<nexists>p' ps'. snd (es!i) = PreRed p' ps'"
        hence C: "elem \<in> set es"
          using a1 a2 C upd_bin_prered_nop assms(2,4) by (metis nth_list_update_eq)
        thus ?thesis
          using assms(1-3) sound_ptrs_def pre_es prered_es by blast
      next
        assume "\<not> (\<nexists>p' ps'. snd (es!i) = PreRed p' ps')"
        then obtain p' ps' where D: "snd (es!i) = PreRed p' ps'"
          by blast
        hence 0: "snd (upd_bin e es!i) = PreRed p' (p#ps@ps') \<and> (\<forall>j < length (upd_bin e es). i\<noteq>j \<longrightarrow> upd_bin e es!j = es!j)"
          using C assms(4) upd_bin_prered_upd by blast
        obtain j where 1: "j < length es \<and> elem = upd_bin e es!j"
          using a1 a2 assms(2) C items_def bin_eq_items_upd_bin by (metis in_set_conv_nth length_map nth_list_update_eq nth_map)
        show ?thesis
        proof cases
          assume a3: "i=j"
          hence a3: "snd elem = PreRed p' (p#ps@ps')"
            using 0 1 by blast
          have "sound_null_ptr elem"
            using a3 unfolding sound_null_ptr_def by simp
          moreover have "sound_pre_ptr \<omega> ?bs idx elem"
            using a3 unfolding sound_pre_ptr_def by simp
          moreover have "sound_prered_ptr ?bs idx elem"
            unfolding sound_prered_ptr_def
          proof (standard, standard, standard, standard, standard, standard)
            fix P PS k' pre red
            assume a4: "snd elem = PreRed P PS \<and> (k', pre, red) \<in> set (P#PS)"
            show "k' < idx \<and> pre < length (bs[k := upd_bin e es]!k') \<and> red < length (bs[k := upd_bin e es]!idx) \<and>
              completes idx (fst (bs[k := upd_bin e es]!k'!pre)) (fst elem) (fst (bs[k := upd_bin e es]!idx!red))"
            proof cases
              assume a5: "(k', pre, red) \<in> set (p#ps)"
              show ?thesis
                using 0 1 C a2 a4 a5 prered_es assms(2,3,7) sound_prered_ptr_def length_upd_bin nth_item_upd_bin
                by (smt (verit) dual_order.strict_trans1 nth_list_update_eq nth_list_update_neq nth_mem)
            next
              assume a5: "(k', pre, red) \<notin> set (p#ps)"
              hence a5: "(k', pre, red) \<in> set (p'#ps')"
                using a3 a4 by auto
              have "k' < idx \<and> pre < length (bs!k') \<and> red < length (bs!idx) \<and>
                completes idx (fst (bs!k'!pre)) (fst e) (fst (bs!idx!red))"
                using assms(1-3) C D a2 a5 unfolding sound_ptrs_def sound_prered_ptr_def by (metis nth_mem)
              thus ?thesis
                using 0 1 C a4 assms(2,3) length_upd_bin nth_item_upd_bin prered_es sound_prered_ptr_def
                by (smt (verit, best) dual_order.strict_trans1 nth_list_update_eq nth_list_update_neq nth_mem)
            qed
          qed
          ultimately show ?thesis
            by blast
        next
          assume a3: "i\<noteq>j"
          hence "elem \<in> set es"
            using 0 1 by (metis length_upd_bin nth_mem order_less_le_trans)
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
      using assms(2,3) length_upd_bin nth_item_upd_bin unfolding sound_pre_ptr_def
      using dual_order.strict_trans1 nth_list_update by (metis (no_types, lifting))
    have "sound_prered_ptr bs idx elem"
      using a0 a1 a2 assms(1,2) unfolding sound_ptrs_def by simp
    hence prered: "sound_prered_ptr ?bs idx elem"
      using assms(2,3) length_upd_bin nth_item_upd_bin unfolding sound_prered_ptr_def
      by (smt (verit, best) dual_order.strict_trans1 nth_list_update)
    show ?thesis
      using null pre prered by blast
  qed
qed

lemma mono_red_ptr_upd_bin:
  assumes "mono_red_ptr bs" "k < length bs" "es = bs!k" "distinct (items es)"
  assumes "\<forall>k' pre red ps. snd e = PreRed (k', pre, red) ps \<longrightarrow> red < length es"
  shows "mono_red_ptr (bs[k := upd_bin e es])"
  unfolding mono_red_ptr_def
proof (standard, standard)
  fix idx
  let ?bs = "bs[k := upd_bin e es]"
  assume a0: "idx < length ?bs"
  show "\<forall>i < length (?bs!idx). \<forall>k' pre red ps. snd (?bs!idx!i) = PreRed (k', pre, red) ps \<longrightarrow> red < i"
  proof cases
    assume a1: "idx=k"
    consider (A) "fst e \<notin> set (items es)" |
      (B) "fst e \<in> set (items es) \<and> (\<exists>pre. snd e = Null \<or> snd e = Pre pre)" |
      (C) "fst e \<in> set (items es) \<and> \<not> (\<exists>pre. snd e = Null \<or> snd e = Pre pre)"
      by blast
    thus ?thesis
    proof cases
      case A
      hence "upd_bin e es = es @ [e]"
        using upd_bin_append by blast
      thus ?thesis
        using a1 assms(1-3,5) mono_red_ptr_def
        by (metis length_append_singleton less_antisym nth_append nth_append_length nth_list_update_eq)
    next
      case B
      hence "upd_bin e es = es"
        using upd_bin_null_pre by blast
      thus ?thesis
        using a1 assms(1-3) mono_red_ptr_def by force
    next
      case C
      then obtain i p ps where C: "i < length es" "fst e = fst (es!i)" "snd e = PreRed p ps"
        by (metis in_set_conv_nth items_def length_map nth_map pointer.exhaust)
      show ?thesis
      proof cases
        assume "\<nexists>p' ps'. snd (es!i) = PreRed p' ps'"
        hence "upd_bin e es = es"
          using upd_bin_prered_nop C assms(4) by blast
        thus ?thesis
          using a1 assms(1-3) mono_red_ptr_def by (metis nth_list_update_eq)
      next
        assume "\<not> (\<nexists>p' ps'. snd (es!i) = PreRed p' ps')"
        then obtain p' ps' where D: "snd (es!i) = PreRed p' ps'"
          by blast
        have 0: "snd (upd_bin e es!i) = PreRed p' (p#ps@ps') \<and>
          (\<forall>j < length (upd_bin e es). i \<noteq> j \<longrightarrow> upd_bin e es!j = es!j) \<and>
          length (upd_bin e es) = length es"
          using C D assms(4) upd_bin_prered_upd by blast
        show ?thesis
        proof (standard, standard, standard, standard, standard, standard, standard)
          fix j k' pre red PS
          assume a2: "j < length (?bs!idx)"
          assume a3: "snd (?bs!idx!j) = PreRed (k', pre, red) PS"
          have 1: "?bs!idx = upd_bin e es"
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

lemma sound_mono_ptrs_upds_bin:
  assumes "sound_ptrs \<omega> bs" "mono_red_ptr bs" "k < length bs" "b = bs!k" "distinct (items b)"
  assumes "\<forall>e \<in> set es. sound_null_ptr e \<and> sound_pre_ptr \<omega> bs k e \<and> sound_prered_ptr bs k e"
  assumes "\<forall>e \<in> set es. \<forall>k' pre red ps. snd e = PreRed (k', pre, red) ps \<longrightarrow> red < length b"
  shows "sound_ptrs \<omega> (bs[k := upds_bin es b]) \<and> mono_red_ptr (bs[k := upds_bin es b])"
  using assms
proof (induction es arbitrary: b bs)
  case (Cons e es)
  let ?bs = "bs[k := upd_bin e b]"
  have 0: "sound_ptrs \<omega> ?bs"
    using sound_ptrs_upd_bin Cons.prems(1,3-5,6) by (metis list.set_intros(1))
  have 1: "mono_red_ptr ?bs"
    using mono_red_ptr_upd_bin Cons.prems(2-5,7) by (metis list.set_intros(1))
  have 2: "k < length ?bs"
    using Cons.prems(3) by simp
  have 3: "upd_bin e b = ?bs!k"
    using Cons.prems(3) by simp
  have 4: "\<forall>e' \<in> set es. sound_null_ptr e' \<and> sound_pre_ptr \<omega> ?bs k e' \<and> sound_prered_ptr ?bs k e'"
    using Cons.prems(3,4,6) length_upd_bin nth_item_upd_bin sound_pre_ptr_def sound_prered_ptr_def
    by (smt (verit, ccfv_threshold) list.set_intros(2) nth_list_update order_less_le_trans)
  have 5: "\<forall>e' \<in> set es. \<forall>k' pre red ps. snd e' = PreRed (k', pre, red) ps \<longrightarrow> red < length (upd_bin e b)"
    by (meson Cons.prems(7) length_upd_bin order_less_le_trans set_subset_Cons subsetD)
  have "sound_ptrs \<omega> ((bs[k := upd_bin e b])[k := upds_bin es (upd_bin e b)]) \<and>
    mono_red_ptr (bs[k := upd_bin e b, k := upds_bin es (upd_bin e b)])"
    using Cons.IH[OF 0 1 2 3 _ _] distinct_upd_bin Cons.prems(4,5,6) items_def 4 5 by blast
  thus ?case
    by simp
qed simp

lemma sound_mono_ptrs_Earley\<^sub>L_bin':
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "sound_ptrs \<omega> bs" "\<forall>x \<in> bins bs. sound_item \<G> \<omega> x"
  assumes "mono_red_ptr bs"
  assumes "nonempty_derives \<G>"
  shows "sound_ptrs \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> bs i) \<and> mono_red_ptr (Earley\<^sub>L_bin' k \<G> \<omega> bs i)"
  using assms
proof (induction i rule: Earley\<^sub>L_bin'_induct[OF assms(1), case_names Base Complete\<^sub>F Scan\<^sub>F Pass Predict\<^sub>F])
  case (Complete\<^sub>F k \<G> \<omega> bs i x)
  let ?bs' = "upd_bins bs k (Complete\<^sub>L k x bs i)"
  have x: "x \<in> set (items (bs ! k))"
    using Complete\<^sub>F.hyps(1,2) by force
  hence "\<forall>x \<in> set (items (Complete\<^sub>L k x bs i)). sound_item \<G> \<omega> x"
    using sound_Complete\<^sub>L Complete\<^sub>F.hyps(3) Complete\<^sub>F.prems wf_earley_input_elim wf_bins_impl_wf_items x
    by (metis dual_order.refl)
  hence sound: "\<forall>x \<in> bins ?bs'. sound_item \<G> \<omega> x"
    by (metis Complete\<^sub>F.prems(1,3) UnE bins_upd_bins wf_earley_input_elim)
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
    assume a1: "snd e = PreRed p ps" "(k', pre, red) \<in> set (p#ps)"
    have "k' = start_item x"
      using a0 a1 unfolding Complete\<^sub>L_def by auto
    moreover have "wf_item \<G> \<omega> x" "end_item x = k"
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
      moreover have "start_item x = k"
        using \<open>\<not> k' \<noteq> k\<close> \<open>k' = start_item x\<close> by auto
      ultimately show False
        using impossible_complete_item Complete\<^sub>F.prems(1,5) wf_earley_input_elim \<open>end_item x = k\<close> \<open>wf_item \<G> \<omega> x\<close> by blast
    qed
    have 2: "pre < length (bs!k')"
      using a0 a1 index_filter_with_index_lt_length unfolding Complete\<^sub>L_def by (auto simp: items_def; fastforce)
    have 3: "red < i+1"
      using a0 a1 unfolding Complete\<^sub>L_def by auto

    have "fst e = inc_item (fst (bs!k'!pre)) k"
      using a0 a1 0 2 Complete\<^sub>F.hyps(1,2,3) Complete\<^sub>F.prems(1) \<open>k' = start_item x\<close> unfolding Complete\<^sub>L_def
      by (auto simp: items_def, metis filter_with_index_nth nth_map)
    moreover have "is_complete (fst (bs!k!red))"
      using a0 a1 0 2 Complete\<^sub>F.hyps(1,2,3) Complete\<^sub>F.prems(1) \<open>k' = start_item x\<close> unfolding Complete\<^sub>L_def
      by (auto simp: next_symbol_def items_def split: if_splits)
    moreover have "start_item (fst (bs!k!red)) = end_item (fst (bs!k'!pre))"
      using a0 a1 0 2 Complete\<^sub>F.hyps(1,2,3) Complete\<^sub>F.prems(1) \<open>k' = start_item x\<close> unfolding Complete\<^sub>L_def
      apply (auto simp: items_def)
      by (metis dual_order.strict_trans index_filter_with_index_lt_length items_def le_neq_implies_less nth_map nth_mem wf_bins_kth_bin wf_earley_input_elim)
    moreover have "(\<exists>N. next_symbol (fst (bs ! k' ! pre)) = Some N \<and> N = lhs_item (fst (bs ! k ! red)))"
      using a0 a1 0 2 Complete\<^sub>F.hyps(1,2,3) Complete\<^sub>F.prems(1) \<open>k' = start_item x\<close> unfolding Complete\<^sub>L_def
      by (auto simp: items_def, metis (mono_tags, lifting) filter_with_index_P filter_with_index_nth nth_map)
    ultimately have 4: "completes k (fst (bs!k'!pre)) (fst e) (fst (bs!k!red))"
      unfolding completes_def by blast
    have "k' < k" "pre < length (bs!k')" "red < i+1" "completes k (fst (bs!k'!pre)) (fst e) (fst (bs!k!red))"
      using 0 1 2 3 4 by simp_all
  }
  hence "\<forall>e \<in> set (Complete\<^sub>L k x bs i). \<forall>p ps k' pre red. snd e = PreRed p ps \<and> (k', pre, red) \<in> set (p#ps) \<longrightarrow>
    k' < k \<and> pre < length (bs!k') \<and> red < i+1 \<and> completes k (fst (bs!k'!pre)) (fst e) (fst (bs!k!red))"
    by force
  hence 3: "\<forall>e \<in> set (Complete\<^sub>L k x bs i). sound_prered_ptr bs k e"
    unfolding sound_prered_ptr_def using Complete\<^sub>F.hyps(1) items_def
    by (smt (verit, del_insts) le_antisym le_eq_less_or_eq le_trans length_map length_pos_if_in_set less_imp_add_positive less_one nat_add_left_cancel_le nat_neq_iff plus_nat.add_0)
  have "sound_ptrs \<omega> ?bs' \<and> mono_red_ptr ?bs'"
    using sound_mono_ptrs_upds_bin[OF Complete\<^sub>F.prems(2) Complete\<^sub>F.prems(4) 0] 1 2 3 sound_prered_ptr_def
      Complete\<^sub>F.prems(1) upd_bins_def wf_earley_input_elim wf_bin_def wf_bins_def
    by (smt (verit, ccfv_SIG) list.set_intros(1))
  moreover have "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Complete\<^sub>F.hyps Complete\<^sub>F.prems(1) wf_earley_input_Complete\<^sub>L by blast
  ultimately have "sound_ptrs \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)) \<and> mono_red_ptr (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1))"
    using Complete\<^sub>F.IH Complete\<^sub>F.prems(4-5) sound by blast
  thus ?case
    using Complete\<^sub>F.hyps by simp
next
  case (Scan\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs (k+1) (Scan\<^sub>L k \<omega> a x i)"
  have "x \<in> set (items (bs ! k))"
    using Scan\<^sub>F.hyps(1,2) by force
  hence "\<forall>x \<in> set (items (Scan\<^sub>L k \<omega> a x i)). sound_item \<G> \<omega> x"
    using sound_Scan\<^sub>L Scan\<^sub>F.hyps(3,5) Scan\<^sub>F.prems(1,2,3) wf_earley_input_elim wf_bins_impl_wf_items wf_bins_impl_wf_items by fast
  hence sound: "\<forall>x \<in> bins ?bs'. sound_item \<G> \<omega> x"
    using Scan\<^sub>F.hyps(5) Scan\<^sub>F.prems(1,3) bins_upd_bins wf_earley_input_elim
    by (metis UnE add_less_cancel_right)
  have 0: "k+1 < length bs"
    using Scan\<^sub>F.hyps(5) Scan\<^sub>F.prems(1) wf_earley_input_elim by force
  have 1: "\<forall>e \<in> set (Scan\<^sub>L k \<omega> a x i). sound_null_ptr e"
    unfolding Scan\<^sub>L_def sound_null_ptr_def by auto
  have 2: "\<forall>e \<in> set (Scan\<^sub>L k \<omega> a x i). sound_pre_ptr \<omega> bs (k+1) e"
    using Scan\<^sub>F.hyps(1,2,3) unfolding sound_pre_ptr_def Scan\<^sub>L_def scans_def items_def by auto
  have 3: "\<forall>e \<in> set (Scan\<^sub>L k \<omega> a x i). sound_prered_ptr bs (k+1) e"
    unfolding Scan\<^sub>L_def sound_prered_ptr_def by simp
  have "sound_ptrs \<omega> ?bs' \<and> mono_red_ptr ?bs'"
    using sound_mono_ptrs_upds_bin[OF Scan\<^sub>F.prems(2) Scan\<^sub>F.prems(4) 0] 0 1 2 3 sound_prered_ptr_def
      Scan\<^sub>F.prems(1) upd_bins_def wf_earley_input_elim wf_bin_def wf_bins_def
    by (smt (verit, ccfv_threshold) list.set_intros(1))
  moreover have "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Scan\<^sub>F.hyps Scan\<^sub>F.prems(1) wf_earley_input_Scan\<^sub>L by metis
  ultimately have "sound_ptrs \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)) \<and> mono_red_ptr (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1))"
    using Scan\<^sub>F.IH Scan\<^sub>F.prems(4-5) sound by blast
  thus ?case
    using Scan\<^sub>F.hyps by simp
next
  case (Predict\<^sub>F k \<G> \<omega> bs i x a)
  let ?bs' = "upd_bins bs k (Predict\<^sub>L k \<G> a)"
  have "x \<in> set (items (bs ! k))"
    using Predict\<^sub>F.hyps(1,2) by force
  hence "\<forall>x \<in> set (items(Predict\<^sub>L k \<G> a)). sound_item \<G> \<omega> x"
    using sound_Predict\<^sub>L Predict\<^sub>F.hyps(3) Predict\<^sub>F.prems wf_earley_input_elim wf_bins_impl_wf_items by fast
  hence sound: "\<forall>x \<in> bins ?bs'. sound_item \<G> \<omega> x"
    using Predict\<^sub>F.prems(1,3) UnE bins_upd_bins wf_earley_input_elim by metis
  have 0: "k < length bs"
    using Predict\<^sub>F.prems(1) wf_earley_input_elim by force
  have 1: "\<forall>e \<in> set (Predict\<^sub>L k \<G> a). sound_null_ptr e"
    unfolding sound_null_ptr_def Predict\<^sub>L_def predicts_def by (auto simp: init_item_def)
  have 2: "\<forall>e \<in> set (Predict\<^sub>L k \<G> a). sound_pre_ptr \<omega> bs k e"
    unfolding sound_pre_ptr_def Predict\<^sub>L_def by simp
  have 3: "\<forall>e \<in> set (Predict\<^sub>L k \<G> a). sound_prered_ptr bs k e"
    unfolding sound_prered_ptr_def Predict\<^sub>L_def by simp
  have "sound_ptrs \<omega> ?bs' \<and> mono_red_ptr ?bs'"
    using sound_mono_ptrs_upds_bin[OF Predict\<^sub>F.prems(2) Predict\<^sub>F.prems(4) 0] 0 1 2 3 sound_prered_ptr_def
      Predict\<^sub>F.prems(1) upd_bins_def wf_earley_input_elim wf_bin_def wf_bins_def
    by (smt (verit, ccfv_threshold) list.set_intros(1))
  moreover have "(k, \<G>, \<omega>, ?bs') \<in> wf_earley_input"
    using Predict\<^sub>F.hyps Predict\<^sub>F.prems(1) wf_earley_input_Predict\<^sub>L by metis
  ultimately have "sound_ptrs \<omega> (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1)) \<and> mono_red_ptr (Earley\<^sub>L_bin' k \<G> \<omega> ?bs' (i+1))"
    using Predict\<^sub>F.IH Predict\<^sub>F.prems(4-5) sound by blast
  thus ?case
    using Predict\<^sub>F.hyps by simp
qed simp_all

lemma sound_mono_ptrs_Earley\<^sub>L_bin:
  assumes "(k, \<G>, \<omega>, bs) \<in> wf_earley_input"
  assumes "sound_ptrs \<omega> bs" "\<forall>x \<in> bins bs. sound_item \<G> \<omega> x"
  assumes "mono_red_ptr bs"
  assumes "nonempty_derives \<G>"
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
  assumes "k \<le> length \<omega>" "nonempty_derives \<G>"
  shows "sound_ptrs \<omega> (Earley\<^sub>L_bins k \<G> \<omega>) \<and> mono_red_ptr (Earley\<^sub>L_bins k \<G> \<omega>)"
  using assms
proof (induction k)
  case 0
  have "(0, \<G>, \<omega>, (Init\<^sub>L \<G> \<omega>)) \<in> wf_earley_input"
    using assms(2) wf_earley_input_Init\<^sub>L by blast
  moreover have "\<forall>x \<in> bins (Init\<^sub>L \<G> \<omega>). sound_item \<G> \<omega> x"
    by (metis Init\<^sub>L_eq_Init\<^sub>F Init\<^sub>F_sub_Earley sound_Earley subsetD wf_Earley)
  ultimately show ?case
    using sound_mono_ptrs_Earley\<^sub>L_bin sound_ptrs_Init\<^sub>L mono_red_ptr_Init\<^sub>L "0.prems" by fastforce
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
    using Suc.prems sound_mono_ptrs_Earley\<^sub>L_bin Suc.IH by fastforce
qed

lemma sound_mono_ptrs_Earley\<^sub>L:
  assumes "nonempty_derives \<G>"
  shows "sound_ptrs \<omega> (Earley\<^sub>L \<G> \<omega>) \<and> mono_red_ptr (Earley\<^sub>L \<G> \<omega>)"
  using assms sound_mono_ptrs_Earley\<^sub>L_bins Earley\<^sub>L_def by (metis dual_order.refl)


subsection \<open>Common Definitions\<close>

datatype 'a tree =
  Leaf 'a
  | Branch 'a "'a tree list"

fun yield :: "'a tree \<Rightarrow> 'a list" where
  "yield (Leaf a) = [a]"
| "yield (Branch _ ts) = concat (map yield ts)"

fun root :: "'a tree \<Rightarrow> 'a" where
  "root (Leaf a) = a"
| "root (Branch N _) = N"

fun wf_rule_tree :: "'a cfg \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "wf_rule_tree _ (Leaf a) \<longleftrightarrow> True"
| "wf_rule_tree \<G> (Branch N ts) \<longleftrightarrow> (
    (\<exists>r \<in> set (\<RR> \<G>). N = lhs_rule r \<and> map root ts = rhs_rule r) \<and>
    (\<forall>t \<in> set ts. wf_rule_tree \<G> t))"

fun wf_item_tree :: "'a cfg \<Rightarrow> 'a item \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "wf_item_tree \<G> _ (Leaf a) \<longleftrightarrow> True"
| "wf_item_tree \<G> x (Branch N ts) \<longleftrightarrow> (
    N = lhs_item x \<and> map root ts = take (dot_item x) (rhs_item x) \<and>
    (\<forall>t \<in> set ts. wf_rule_tree \<G> t))"

definition wf_yield :: "'a list \<Rightarrow> 'a item \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "wf_yield \<omega> x t \<longleftrightarrow> yield t = slice \<omega> (start_item x) (end_item x)"


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

partial_function (option) build_tree' :: "'a bins \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a tree option" where
  "build_tree' bs \<omega> k i = (
    let e = bs!k!i in (
    case snd e of
      Null \<Rightarrow> Some (Branch (lhs_item (fst e)) []) \<comment>\<open>start building sub-tree\<close>
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

definition build_tree :: "'a cfg \<Rightarrow> 'a list \<Rightarrow> 'a bins \<Rightarrow> 'a tree option" where
  "build_tree \<G> \<omega> bs = (
    let k = length bs - 1 in (
    case filter_with_index (\<lambda>x. is_finished \<G> \<omega> x) (items (bs!k)) of
      [] \<Rightarrow> None
    | (_, i)#_ \<Rightarrow> build_tree' bs \<omega> k i
  ))"

lemma build_tree'_simps[simp]:
  "e = bs!k!i \<Longrightarrow> snd e = Null \<Longrightarrow> build_tree' bs \<omega> k i = Some (Branch (lhs_item (fst e)) [])"
  "e = bs!k!i \<Longrightarrow> snd e = Pre pre \<Longrightarrow> build_tree' bs \<omega> (k-1) pre = None \<Longrightarrow>
   build_tree' bs \<omega> k i = None"
  "e = bs!k!i \<Longrightarrow> snd e = Pre pre \<Longrightarrow> build_tree' bs \<omega> (k-1) pre = Some (Branch N ts) \<Longrightarrow>
   build_tree' bs \<omega> k i = Some (Branch N (ts @ [Leaf (\<omega>!(k-1))]))"
  "e = bs!k!i \<Longrightarrow> snd e = Pre pre \<Longrightarrow> build_tree' bs \<omega> (k-1) pre = Some (Leaf a) \<Longrightarrow>
   build_tree' bs \<omega> k i = undefined"
  "e = bs!k!i \<Longrightarrow> snd e = PreRed (k', pre, red) reds \<Longrightarrow> build_tree' bs \<omega> k' pre = None \<Longrightarrow>
   build_tree' bs \<omega> k i = None"
  "e = bs!k!i \<Longrightarrow> snd e = PreRed (k', pre, red) reds \<Longrightarrow> build_tree' bs \<omega> k' pre = Some (Branch N ts) \<Longrightarrow>
   build_tree' bs \<omega> k red = None \<Longrightarrow> build_tree' bs \<omega> k i = None"
  "e = bs!k!i \<Longrightarrow> snd e = PreRed (k', pre, red) reds \<Longrightarrow> build_tree' bs \<omega> k' pre = Some (Leaf a) \<Longrightarrow>
   build_tree' bs \<omega> k i = undefined"
  "e = bs!k!i \<Longrightarrow> snd e = PreRed (k', pre, red) reds \<Longrightarrow> build_tree' bs \<omega> k' pre = Some (Branch N ts) \<Longrightarrow>
   build_tree' bs \<omega> k red = Some t \<Longrightarrow>
   build_tree' bs \<omega> k i = Some (Branch N (ts @ [t]))"
  by (subst build_tree'.simps, simp)+

definition wf_tree_input :: "('a bins \<times> 'a list \<times> nat \<times> nat) set" where
  "wf_tree_input = {
    (bs, \<omega>, k, i) | bs \<omega> k i.
      sound_ptrs \<omega> bs \<and>
      mono_red_ptr bs \<and>
      k < length bs \<and>
      k \<le> length \<omega> \<and>
      i < length (bs!k)
  }"

fun build_tree'_measure :: "('a bins \<times> 'a list \<times> nat \<times> nat) \<Rightarrow> nat" where
  "build_tree'_measure (bs, \<omega>, k, i) = foldl (+) 0 (map length (take k bs)) + i"

lemma wf_tree_input_pre:
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  assumes "e = bs!k!i" "snd e = Pre pre"
  shows "(bs, \<omega>, (k-1), pre) \<in> wf_tree_input"
  using assms unfolding wf_tree_input_def
  apply (auto simp: sound_ptrs_def sound_pre_ptr_def)
  apply (metis nth_mem)
  done

lemma wf_tree_input_prered_pre:
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  assumes "e = bs!k!i" "snd e = PreRed (k', pre, red) ps"
  shows "(bs, \<omega>, k', pre) \<in> wf_tree_input"
  using assms unfolding wf_tree_input_def
  apply (auto simp: sound_ptrs_def sound_prered_ptr_def)
  apply (metis fst_conv snd_conv)+
  apply (metis dual_order.strict_trans nth_mem)
  apply fastforce
  by (metis nth_mem)

lemma wf_tree_input_prered_red:
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  assumes "e = bs!k!i" "snd e = PreRed (k', pre, red) ps"
  shows "(bs, \<omega>, k, red) \<in> wf_tree_input"
  using assms unfolding wf_tree_input_def
  apply (auto simp add: sound_ptrs_def sound_prered_ptr_def)
  apply (metis fst_conv snd_conv nth_mem)+
  done

lemma build_tree'_induct:
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  assumes "\<And>bs \<omega> k i.
    (\<And>e pre. e = bs!k!i \<Longrightarrow> snd e = Pre pre \<Longrightarrow> P bs \<omega> (k-1) pre) \<Longrightarrow>
    (\<And>e k' pre red ps. e = bs!k!i \<Longrightarrow> snd e = PreRed (k', pre, red) ps \<Longrightarrow> P bs \<omega> k' pre) \<Longrightarrow>
    (\<And>e k' pre red ps. e = bs!k!i \<Longrightarrow> snd e = PreRed (k', pre, red) ps \<Longrightarrow> P bs \<omega> k red) \<Longrightarrow>
    P bs \<omega> k i" 
  shows "P bs \<omega> k i"
  using assms(1)
proof (induction n\<equiv>"build_tree'_measure (bs, \<omega>, k, i)" arbitrary: k i rule: nat_less_induct)
  case 1
  obtain e where entry: "e = bs!k!i"
    by simp
  consider (Null) "snd e = Null"
    | (Pre) "\<exists>pre. snd e = Pre pre"
    | (PreRed) "\<exists>k' pre red reds. snd e = PreRed (k', pre, red) reds"
    by (metis pointer.exhaust surj_pair)
  thus ?case
  proof cases
    case Null
    thus ?thesis
      using assms(2) entry by fastforce
  next
    case Pre
    then obtain pre where pre: "snd e = Pre pre"
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
    then obtain k' pre red ps where prered: "snd e = PreRed (k', pre, red) ps"
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
      consider (Null) "snd e = Null"
        | (Pre) "\<exists>pre. snd e = Pre pre"
        | (PreRed) "\<exists>k' pre red ps. snd e = PreRed (k', pre, red) ps"
        by (metis pointer.exhaust surj_pair)
      thus ?thesis
      proof cases
        case Null
        thus ?thesis
          using build_tree'_simps(1) entry by simp
      next
        case Pre
        then obtain pre where pre: "snd e = Pre pre"
          by blast
        obtain N ts where Nts: "build_tree' bs \<omega> (k-1) pre = Some (Branch N ts)"
          using IH(1) entry pre by blast
        have "build_tree' bs \<omega> k i = Some (Branch N (ts @ [Leaf (\<omega>!(k-1))]))"
          using build_tree'_simps(3) entry pre Nts by simp         
        thus ?thesis
          by simp
      next
        case PreRed
        then obtain k' pre red ps where prered: "snd e = PreRed (k', pre, red) ps"
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
  assumes "build_tree' bs \<omega> k i = Some t"
  shows "wf_item_tree \<G> (fst (bs!k!i)) t"
proof -
  have "wf_item_tree \<G> (fst (bs!k!i)) t"
    using assms
    apply (induction arbitrary: t rule: build_tree'_induct[OF assms(1)])
    subgoal premises prems for bs \<omega> k i t
    proof -
      define e where entry: "e = bs!k!i"
      have bounds: "k < length bs" "k \<le> length \<omega>" "i < length (bs!k)"
        using prems(4) wf_tree_input_def by force+
      consider (Null) "snd e = Null"
        | (Pre) "\<exists>pre. snd e = Pre pre"
        | (PreRed) "\<exists>k' pre red ps. snd e = PreRed (k', pre, red) ps"
        by (metis pointer.exhaust surj_pair)
      thus ?thesis
      proof cases
        case Null
        hence "build_tree' bs \<omega> k i = Some (Branch (lhs_item (fst e)) [])"
          using entry by simp
        have simp: "t = Branch (lhs_item (fst e)) []"
          using build_tree'_simps(1) Null prems(6) entry by simp
        have "sound_ptrs \<omega> bs"
          using prems(4) unfolding wf_tree_input_def by blast
        hence "predicts (fst e)"
          using Null nth_mem entry bounds unfolding sound_ptrs_def sound_null_ptr_def by blast
        hence "dot_item (fst e) = 0"
          unfolding predicts_def by blast
        thus ?thesis
          using simp entry by simp
      next
        case Pre
        then obtain pre where pre: "snd e = Pre pre"
          by blast
        obtain N ts where Nts: "build_tree' bs \<omega> (k-1) pre = Some (Branch N ts)"
          using build_tree'_termination entry pre prems(4) wf_tree_input_pre by blast
        have simp: "build_tree' bs \<omega> k i = Some (Branch N (ts @ [Leaf (\<omega>!(k-1))]))"
          using build_tree'_simps(3) entry pre Nts by simp
        have "sound_ptrs \<omega> bs"
          using prems(4) unfolding wf_tree_input_def by blast
        hence "pre < length (bs!(k-1))"
          using entry pre bounds unfolding sound_ptrs_def sound_pre_ptr_def by (metis nth_mem)
        moreover have "k-1 < length bs"
          by (simp add: bounds less_imp_diff_less)
        ultimately have IH: "wf_item_tree \<G> (fst (bs!(k-1)!pre)) (Branch N ts)"
          using prems(1,2,4,5) entry pre Nts by (meson wf_tree_input_pre)
        have scans: "scans \<omega> k (fst (bs!(k-1)!pre)) (fst e)"
          using entry pre bounds \<open>sound_ptrs \<omega> bs\<close> unfolding sound_ptrs_def sound_pre_ptr_def by simp
        hence *: 
          "lhs_item (fst (bs!(k-1)!pre)) = lhs_item (fst e)"
          "rhs_item (fst (bs!(k-1)!pre)) = rhs_item (fst e)"
          "dot_item (fst (bs!(k-1)!pre)) + 1 = dot_item (fst e)"
          "next_symbol (fst (bs!(k-1)!pre)) = Some (\<omega>!(k-1))"
          unfolding scans_def inc_item_def by (simp_all add: lhs_item_def rhs_item_def)
        have "map root (ts @ [Leaf (\<omega>!(k-1))]) = map root ts @ [\<omega>!(k-1)]"
          by simp
        also have "... = take (dot_item (fst (bs!(k-1)!pre))) (rhs_item (fst (bs!(k-1)!pre))) @ [\<omega>!(k-1)]"
          using IH by simp
        also have "... = take (dot_item (fst (bs!(k-1)!pre))) (rhs_item (fst e)) @ [\<omega>!(k-1)]"
          using *(2) by simp
        also have "... = take (dot_item (fst e)) (rhs_item (fst e))"
          using *(2-4) by (auto simp: next_symbol_def is_complete_def split: if_splits; metis leI take_Suc_conv_app_nth)
        finally have "map root (ts @ [Leaf (\<omega>!(k-1))]) = take (dot_item (fst e)) (rhs_item (fst e))" .
        hence "wf_item_tree \<G> (fst e) (Branch N (ts @ [Leaf (\<omega>!(k-1))]))"
          using IH *(1) by simp
        thus ?thesis
          using entry prems(6) simp by auto
      next
        case PreRed
        then obtain k' pre red ps where prered: "snd e = PreRed (k', pre, red) ps"
          by blast
        obtain N ts where Nts: "build_tree' bs \<omega> k' pre = Some (Branch N ts)"
          using build_tree'_termination entry prems(4) prered wf_tree_input_prered_pre by blast
        obtain N_red ts_red where Nts_red: "build_tree' bs \<omega> k red = Some (Branch N_red ts_red)"
          using build_tree'_termination entry prems(4) prered wf_tree_input_prered_red by blast
        have simp: "build_tree' bs \<omega> k i = Some (Branch N (ts @ [Branch N_red ts_red]))"
          using build_tree'_simps(8) entry prered Nts Nts_red by auto
        have "sound_ptrs \<omega> bs"
          using prems(4) wf_tree_input_def by fastforce
        have bounds': "k' < k" "pre < length (bs!k')" "red < length (bs!k)"
          using prered entry bounds \<open>sound_ptrs \<omega> bs\<close>
          unfolding sound_prered_ptr_def sound_ptrs_def by fastforce+
        have completes: "completes k (fst (bs!k'!pre)) (fst e) (fst (bs!k!red))"
          using prered entry bounds \<open>sound_ptrs \<omega> bs\<close>
          unfolding sound_ptrs_def sound_prered_ptr_def by force
        have *: 
          "lhs_item (fst (bs!k'!pre)) = lhs_item (fst e)"
          "rhs_item (fst (bs!k'!pre)) = rhs_item (fst e)"
          "dot_item (fst (bs!k'!pre)) + 1 = dot_item (fst e)"
          "next_symbol (fst (bs!k'!pre)) = Some (lhs_item (fst (bs!k!red)))"
          "is_complete (fst (bs!k!red))"
          using completes unfolding completes_def inc_item_def
          by (auto simp: lhs_item_def rhs_item_def is_complete_def)
        have "(bs, \<omega>, k', pre) \<in> wf_tree_input"
          using wf_tree_input_prered_pre[OF prems(4) entry prered] by blast
        hence IH_pre: "wf_item_tree \<G> (fst (bs!k'!pre)) (Branch N ts)"
          using prems(2)[OF entry prered _ prems(5)] Nts bounds(1,2) order_less_trans prems(6) by blast
        have "(bs, \<omega>, k, red) \<in> wf_tree_input"
          using wf_tree_input_prered_red[OF prems(4) entry prered] by blast   
        hence IH_r: "wf_item_tree \<G> (fst (bs!k!red)) (Branch N_red ts_red)"
          using bounds'(3) entry prems(3,5,6) prered Nts_red by blast
        have "map root (ts @ [Branch N_red ts_red]) = map root ts @ [root (Branch N_red ts)]"
          by simp
        also have "... = take (dot_item (fst (bs!k'!pre))) (rhs_item (fst (bs!k'!pre))) @ [root (Branch N_red ts)]"
          using IH_pre by simp
        also have "... = take (dot_item (fst (bs!k'!pre))) (rhs_item (fst (bs!k'!pre))) @ [lhs_item (fst (bs!k!red))]"
          using IH_r by simp
        also have "... = take (dot_item (fst e)) (rhs_item (fst e))"
          using * by (auto simp: next_symbol_def is_complete_def split: if_splits; metis leI take_Suc_conv_app_nth)
        finally have roots: "map root (ts @ [Branch N_red ts]) = take (dot_item (fst e)) (rhs_item (fst e))" by simp
        have "wf_item \<G> \<omega> (fst (bs!k!red))"
          using bounds bounds'(3) prems(5) wf_bins_def wf_bin_def wf_bin_items_def
          by (metis items_def length_map nth_map nth_mem)
        moreover have "N_red = lhs_item (fst (bs!k!red))"
          using IH_r by fastforce
        moreover have "map root ts_red = rhs_item (fst (bs!k!red))"
          using IH_r *(5) by (auto simp: is_complete_def)
        ultimately have "\<exists>r \<in> set (\<RR> \<G>). N_red = lhs_rule r \<and> map root ts_red = rhs_rule r"
          unfolding wf_item_def rhs_item_def lhs_item_def by blast
        hence "wf_rule_tree \<G> (Branch N_red ts_red)"
          using IH_r by simp
        hence "wf_item_tree \<G> (fst (bs!k!i)) (Branch N (ts @ [Branch N_red ts_red]))"
          using "*"(1) roots IH_pre entry by simp
        thus ?thesis
          using Nts_red prems(6) simp by auto
      qed
    qed
    done
  thus ?thesis
    using assms(2) by blast
qed

lemma wf_yield_build_tree':
  assumes "(bs, \<omega>, k, i) \<in> wf_tree_input"
  assumes "wf_bins \<G> \<omega> bs"
  assumes "build_tree' bs \<omega> k i = Some t"
  shows "wf_yield \<omega> (fst (bs!k!i)) t"
proof -
  have "wf_yield \<omega> (fst (bs!k!i)) t"
    using assms
    apply (induction arbitrary: t rule: build_tree'_induct[OF assms(1)])
    subgoal premises prems for bs \<omega> k i t
    proof -
      define e where entry: "e = bs!k!i"
      have bounds: "k < length bs" "k \<le> length \<omega>" "i < length (bs!k)"
        using prems(4) wf_tree_input_def by force+
      consider (Null) "snd e = Null"
        | (Pre) "\<exists>pre. snd e = Pre pre"
        | (PreRed) "\<exists>k' pre red reds. snd e = PreRed (k', pre, red) reds"
        by (metis pointer.exhaust surj_pair)
      thus ?thesis
      proof cases
        case Null
        hence "build_tree' bs \<omega> k i = Some (Branch (lhs_item (fst e)) [])"
          using entry by simp
        have simp: "t = Branch (lhs_item (fst e)) []"
          using build_tree'_simps(1) Null prems(6) entry by simp
        have "sound_ptrs \<omega> bs"
          using prems(4) unfolding wf_tree_input_def by blast
        hence "predicts (fst e)"
          using Null bounds nth_mem entry unfolding sound_ptrs_def sound_null_ptr_def by blast
        thus ?thesis
          unfolding wf_yield_def predicts_def using simp entry by (auto simp: slice_empty)
      next
        case Pre
        then obtain pre where pre: "snd e = Pre pre"
          by blast
        obtain N ts where Nts: "build_tree' bs \<omega> (k-1) pre = Some (Branch N ts)"
          using build_tree'_termination entry pre prems(4) wf_tree_input_pre by blast
        have simp: "build_tree' bs \<omega> k i = Some (Branch N (ts @ [Leaf (\<omega>!(k-1))]))"
          using build_tree'_simps(3) entry pre Nts by simp
        have "sound_ptrs \<omega> bs"
          using prems(4) unfolding wf_tree_input_def by blast
        hence bounds': "k > 0" "pre < length (bs!(k-1))"
          using entry pre bounds unfolding sound_ptrs_def sound_pre_ptr_def by (metis nth_mem)+
        moreover have "k-1 < length bs"
          by (simp add: bounds less_imp_diff_less)
        ultimately have IH: "wf_yield \<omega> (fst (bs!(k-1)!pre)) (Branch N ts)"
          using prems(1) entry pre Nts wf_tree_input_pre prems(4,5,6) by fastforce
        have scans: "scans \<omega> k (fst (bs!(k-1)!pre)) (fst e)"
          using entry pre bounds \<open>sound_ptrs \<omega> bs\<close> unfolding sound_ptrs_def sound_pre_ptr_def by simp
        have wf: 
          "start_item (fst (bs!(k-1)!pre)) \<le> end_item (fst (bs!(k-1)!pre))"
          "end_item (fst (bs!(k-1)!pre)) = k-1"
          "end_item (fst e) = k"
          using entry prems(5) bounds' bounds unfolding wf_bins_def wf_bin_def wf_bin_items_def items_def wf_item_def
          by (auto, meson less_imp_diff_less nth_mem)
        have "yield (Branch N (ts @ [Leaf (\<omega>!(k-1))])) = concat (map yield (ts @ [Leaf (\<omega>!(k-1))]))"
          by simp
        also have "... = concat (map yield ts) @ [\<omega>!(k-1)]"
          by simp
        also have "... = slice \<omega> (start_item (fst (bs!(k-1)!pre))) (end_item (fst (bs!(k-1)!pre))) @ [\<omega>!(k-1)]"
          using IH by (simp add: wf_yield_def)
        also have "... = slice \<omega> (start_item (fst (bs!(k-1)!pre))) (end_item (fst (bs!(k-1)!pre)) + 1)"
          using slice_append_nth wf \<open>k > 0\<close>
          by (metis One_nat_def Suc_pred bounds(2) le_neq_implies_less lessI less_imp_diff_less)
        also have "... = slice \<omega> (start_item (fst e)) (end_item (fst (bs!(k-1)!pre)) + 1)"
          using scans unfolding scans_def inc_item_def by simp
        also have "... = slice \<omega> (start_item (fst e)) k"
          using scans wf unfolding scans_def by (metis Suc_diff_1 Suc_eq_plus1 bounds'(1))
        also have "... = slice \<omega> (start_item (fst e)) (end_item (fst e))"
          using wf by auto
        finally show ?thesis
          using wf_yield_def entry prems(6) simp by force
      next
        case PreRed
        then obtain k' pre red ps where prered: "snd e = PreRed (k', pre, red) ps"
          by blast
        obtain N ts where Nts: "build_tree' bs \<omega> k' pre = Some (Branch N ts)"
          using build_tree'_termination entry prems(4) prered wf_tree_input_prered_pre by blast
        obtain N_red ts_red where Nts_red: "build_tree' bs \<omega> k red = Some (Branch N_red ts_red)"
          using build_tree'_termination entry prems(4) prered wf_tree_input_prered_red by blast
        have simp: "build_tree' bs \<omega> k i = Some (Branch N (ts @ [Branch N_red ts_red]))"
          using build_tree'_simps(8) entry prered Nts Nts_red by auto
        have "sound_ptrs \<omega> bs"
          using prems(4) wf_tree_input_def by fastforce
        have bounds': "k' < k" "pre < length (bs!k')" "red < length (bs!k)"
          using prered entry bounds \<open>sound_ptrs \<omega> bs\<close>
          unfolding sound_ptrs_def sound_prered_ptr_def by fastforce+
        have completes: "completes k (fst (bs!k'!pre)) (fst e) (fst (bs!k!red))"
          using prered entry bounds \<open>sound_ptrs \<omega> bs\<close>
          unfolding sound_ptrs_def sound_prered_ptr_def by fastforce
        have "(bs, \<omega>, k', pre) \<in> wf_tree_input"
          using wf_tree_input_prered_pre[OF prems(4) entry prered] by blast
        hence IH_pre: "wf_yield \<omega> (fst (bs!k'!pre)) (Branch N ts)"
          using prems(2)[OF entry prered _ prems(5)] Nts bounds'(1,2) prems(6)
          by (meson dual_order.strict_trans1 nat_less_le)
        have "(bs, \<omega>, k, red) \<in> wf_tree_input"
          using wf_tree_input_prered_red[OF prems(4) entry prered] by blast
        hence IH_r: "wf_yield \<omega> (fst (bs!k!red)) (Branch N_red ts_red)"
          using bounds(3) entry prems(3,5,6) prered Nts_red by blast
        have wf1: 
          "start_item (fst (bs!k'!pre)) \<le> end_item (fst (bs!k'!pre))"
          "start_item (fst (bs!k!red)) \<le> end_item (fst (bs!k!red))"
          using prems(5) bounds bounds' unfolding wf_bins_def wf_bin_def wf_bin_items_def items_def wf_item_def
          by (metis length_map nth_map nth_mem order.strict_trans)+
        have wf2:
          "end_item (fst (bs!k!red)) = k"
          "end_item (fst (bs!k!i)) = k"
          using prems(5) bounds bounds' unfolding wf_bins_def wf_bin_def wf_bin_items_def items_def by simp_all
        have "yield (Branch N (ts @ [Branch N_red ts_red])) = concat (map yield (ts @ [Branch N_red ts_red]))"
          by (simp add: Nts_red)
        also have "... = concat (map yield ts) @ yield (Branch N_red ts_red)"
          by simp
        also have "... = slice \<omega> (start_item (fst (bs!k'!pre))) (end_item (fst (bs!k'!pre))) @ 
          slice \<omega> (start_item (fst (bs!k!red))) (end_item (fst (bs!k!red)))"
          using IH_pre IH_r by (simp add: wf_yield_def)
        also have "... = slice \<omega> (start_item (fst (bs!k'!pre))) (end_item (fst (bs!k!red)))"
          using slice_concat wf1 completes_def completes by (metis (no_types, lifting))
        also have "... = slice \<omega> (start_item (fst e)) (end_item (fst (bs!k!red)))"
          using completes unfolding completes_def inc_item_def by simp
        also have "... = slice \<omega> (start_item (fst e)) (end_item (fst e))"
          using wf2 entry by presburger
        finally show ?thesis
          using wf_yield_def entry prems(6) simp by force
      qed
    qed
    done
  thus ?thesis
    using assms(2) by blast
qed

theorem wf_rule_root_yield_build_tree:
  assumes "wf_bins \<G> \<omega> bs" "sound_ptrs \<omega> bs" "mono_red_ptr bs" "length bs = length \<omega> + 1"
  assumes "build_tree \<G> \<omega> bs = Some t"
  shows "wf_rule_tree \<G> t \<and> root t = \<SS> \<G> \<and> yield t = \<omega>"
proof -
  let ?k = "length bs - 1"
  define finished where finished_def: "finished = filter_with_index (is_finished \<G> \<omega>) (items (bs!?k))"
  then obtain x i where *: "(x,i) \<in> set finished" "Some t = build_tree' bs \<omega> ?k i"
    using assms(5) unfolding finished_def build_tree_def by (auto simp: Let_def split: list.splits, presburger)
  have k: "?k < length bs" "?k \<le> length \<omega>"
    using assms(4) by simp_all
  have i: "i < length (bs!?k)"
    using index_filter_with_index_lt_length * items_def finished_def by (metis length_map)
  have x: "x = fst (bs!?k!i)"
    using * i filter_with_index_nth items_def nth_map finished_def by metis
  have finished: "is_finished \<G> \<omega> x"
    using * filter_with_index_P finished_def by metis
  have wf_trees_input: "(bs, \<omega>, ?k, i) \<in> wf_tree_input"
    unfolding wf_tree_input_def using assms(2,3) i k by blast
  hence wf_item_tree: "wf_item_tree \<G> x t"
    using wf_item_tree_build_tree' assms(1,2) i k(1) x *(2) by metis
  have wf_item: "wf_item \<G> \<omega> (fst (bs!?k!i))"
    using k(1) i assms(1) unfolding wf_bins_def wf_bin_def wf_bin_items_def by (simp add: items_def)
  obtain N ts where t: "t = Branch N ts"
    by (metis *(2) build_tree'_termination option.inject wf_trees_input)
  hence "N = lhs_item x"
    "map root ts = rhs_item x"
    using finished wf_item_tree by (auto simp: is_finished_def is_complete_def)
  hence "\<exists>r \<in> set (\<RR> \<G>). N = lhs_rule r \<and> map root ts = rhs_rule r"
    using wf_item x unfolding wf_item_def rhs_item_def lhs_item_def by blast
  hence wf_rule: "wf_rule_tree \<G> t"
    using wf_item_tree t by simp
  have root: "root t = \<SS> \<G>"
    using finished t \<open>N = lhs_item x\<close> by (auto simp: is_finished_def)
  have "yield t = slice \<omega> (start_item (fst (bs!?k!i))) (end_item (fst (bs!?k!i)))"
    using k i assms(1) wf_trees_input wf_yield_build_tree' wf_yield_def *(2) by (metis (no_types, lifting))
  hence yield: "yield t = \<omega>"
    using finished x unfolding is_finished_def by simp
  show ?thesis
    using * wf_rule root yield assms(4) unfolding build_tree_def by simp
qed

corollary wf_rule_root_yield_build_tree_Earley\<^sub>L:
  assumes "\<epsilon>_free \<G>"
  assumes "build_tree \<G> \<omega> (Earley\<^sub>L \<G> \<omega>) = Some t"
  shows "wf_rule_tree \<G> t \<and> root t = \<SS> \<G> \<and> yield t = \<omega>"
  using assms wf_rule_root_yield_build_tree wf_bins_Earley\<^sub>L sound_mono_ptrs_Earley\<^sub>L Earley\<^sub>L_def
    length_Earley\<^sub>L_bins length_bins_Init\<^sub>L by (metis \<epsilon>_free_impl_nonempty_derives le_refl)

theorem correctness_build_tree_Earley\<^sub>L:
  assumes "is_word \<G> \<omega>" "\<epsilon>_free \<G>"
  shows "(\<exists>t. build_tree \<G> \<omega> (Earley\<^sub>L \<G> \<omega>) = Some t) \<longleftrightarrow> \<G> \<turnstile> [\<SS> \<G>] \<Rightarrow>\<^sup>* \<omega>" (is "?L \<longleftrightarrow> ?R")
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
  have x: "x = fst ((Earley\<^sub>L \<G> \<omega>)!?k!i)"
    using * i filter_with_index_nth items_def nth_map finished_def by metis
  have finished: "is_finished \<G> \<omega> x"
    using * filter_with_index_P finished_def by metis
  moreover have "x \<in> set (items ((Earley\<^sub>L \<G> \<omega>) ! ?k))"
    using x by (auto simp: items_def; metis One_nat_def i imageI nth_mem)
  ultimately have "recognizing (bins (Earley\<^sub>L \<G> \<omega>)) \<G> \<omega>"
    by (meson k(1) kth_bin_sub_bins recognizing_def subsetD)
  thus ?R
    using soundness_Earley\<^sub>L by blast
next
  assume *: ?R
  let ?k = "length (Earley\<^sub>L \<G> \<omega>) - 1"
  define finished where finished_def: "finished = filter_with_index (is_finished \<G> \<omega>) (items ((Earley\<^sub>L \<G> \<omega>)!?k))"
  have "recognizing (bins (Earley\<^sub>L \<G> \<omega>)) \<G> \<omega>"
    using assms * completeness_Earley\<^sub>L by blast
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
    unfolding wf_tree_input_def using sound_mono_ptrs_Earley\<^sub>L assms \<epsilon>_free_impl_nonempty_derives
    using \<open>length (Earley\<^sub>L \<G> \<omega>) - 1 = length \<omega>\<close> by auto
  then obtain N ts where "build_tree' (Earley\<^sub>L \<G> \<omega>) \<omega> ?k i = Some (Branch N ts)"
    using build_tree'_termination by blast
  thus ?L
    using simp by simp
qed

end