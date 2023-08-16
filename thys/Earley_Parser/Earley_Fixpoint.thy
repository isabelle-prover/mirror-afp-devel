theory Earley_Fixpoint
  imports
    Earley
    Limit
begin

section \<open>Earley recognizer\<close>

subsection \<open>Earley fixpoint\<close>

definition init_item :: "'a rule \<Rightarrow> nat \<Rightarrow> 'a item" where
  "init_item r k \<equiv> Item r 0 k k"

definition inc_item :: "'a item \<Rightarrow> nat \<Rightarrow> 'a item" where
  "inc_item x k \<equiv> Item (item_rule x) (item_dot x + 1) (item_origin x) k"

definition bin :: "'a item set \<Rightarrow> nat \<Rightarrow> 'a item set" where
  "bin I k \<equiv> { x . x \<in> I \<and> item_end x = k }"

definition Init\<^sub>F :: "'a cfg \<Rightarrow> 'a item set" where
  "Init\<^sub>F \<G> \<equiv> { init_item r 0 | r. r \<in> set (\<RR> \<G>) \<and> fst r = (\<SS> \<G>) }"

definition Scan\<^sub>F :: "nat \<Rightarrow> 'a sentence \<Rightarrow> 'a item set \<Rightarrow> 'a item set" where
  "Scan\<^sub>F k \<omega> I \<equiv> { inc_item x (k+1) | x a.
    x \<in> bin I k \<and>
    \<omega>!k = a \<and>
    k < length \<omega> \<and>
    next_symbol x = Some a }"

definition Predict\<^sub>F :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a item set \<Rightarrow> 'a item set" where
  "Predict\<^sub>F k \<G> I \<equiv> { init_item r k | r x.
    r \<in> set (\<RR> \<G>) \<and>
    x \<in> bin I k \<and>
    next_symbol x = Some (rule_head r) }"

definition Complete\<^sub>F :: "nat \<Rightarrow> 'a item set \<Rightarrow> 'a item set" where
  "Complete\<^sub>F k I \<equiv> { inc_item x k | x y.
    x \<in> bin I (item_origin y) \<and>
    y \<in> bin I k \<and>
    is_complete y \<and>
    next_symbol x = Some (item_rule_head y) }"

definition Earley\<^sub>F_bin_step :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item set \<Rightarrow> 'a item set" where
  "Earley\<^sub>F_bin_step k \<G> \<omega> I \<equiv> I \<union> Scan\<^sub>F k \<omega> I \<union> Complete\<^sub>F k I \<union> Predict\<^sub>F k \<G> I"

definition Earley\<^sub>F_bin :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item set \<Rightarrow> 'a item set" where
  "Earley\<^sub>F_bin k \<G> \<omega> I \<equiv> limit (Earley\<^sub>F_bin_step k \<G> \<omega>) I"

fun Earley\<^sub>F_bins :: "nat \<Rightarrow> 'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item set" where
  "Earley\<^sub>F_bins 0 \<G> \<omega> = Earley\<^sub>F_bin 0 \<G> \<omega> (Init\<^sub>F \<G>)"
| "Earley\<^sub>F_bins (Suc n) \<G> \<omega> = Earley\<^sub>F_bin (Suc n) \<G> \<omega> (Earley\<^sub>F_bins n \<G> \<omega>)"

definition Earley\<^sub>F :: "'a cfg \<Rightarrow> 'a sentence \<Rightarrow> 'a item set" where
  "Earley\<^sub>F \<G> \<omega> \<equiv> Earley\<^sub>F_bins (length \<omega>) \<G> \<omega>"


subsection \<open>Monotonicity and Absorption\<close>

lemma Earley\<^sub>F_bin_step_empty:
  "Earley\<^sub>F_bin_step k \<G> \<omega> {} = {}"
  unfolding Earley\<^sub>F_bin_step_def Scan\<^sub>F_def Complete\<^sub>F_def Predict\<^sub>F_def bin_def by blast

lemma Earley\<^sub>F_bin_step_setmonotone:
  "setmonotone (Earley\<^sub>F_bin_step k \<G> \<omega>)"
  by (simp add: Un_assoc Earley\<^sub>F_bin_step_def setmonotone_def)

lemma Earley\<^sub>F_bin_step_continuous:
  "continuous (Earley\<^sub>F_bin_step k \<G> \<omega>)"
  unfolding continuous_def
proof (standard, standard, standard)
  fix C :: "nat \<Rightarrow> 'a item set"
  assume "chain C"
  thus "chain (Earley\<^sub>F_bin_step k \<G> \<omega> \<circ> C)"
    unfolding chain_def Earley\<^sub>F_bin_step_def by (auto simp: Scan\<^sub>F_def Predict\<^sub>F_def Complete\<^sub>F_def bin_def subset_eq)
next
  fix C :: "nat \<Rightarrow> 'a item set"
  assume *: "chain C"
  show "Earley\<^sub>F_bin_step k \<G> \<omega> (natUnion C) = natUnion (Earley\<^sub>F_bin_step k \<G> \<omega> \<circ> C)"
    unfolding natUnion_def
  proof standard
    show "Earley\<^sub>F_bin_step k \<G> \<omega> (\<Union> {C n |n. True}) \<subseteq> \<Union> {(Earley\<^sub>F_bin_step k \<G> \<omega> \<circ> C) n |n. True}"
    proof standard
      fix x
      assume #: "x \<in> Earley\<^sub>F_bin_step k \<G> \<omega> (\<Union> {C n |n. True})"
      show "x \<in> \<Union> {(Earley\<^sub>F_bin_step k \<G> \<omega> \<circ> C) n |n. True}"
      proof (cases "x \<in> Complete\<^sub>F k (\<Union> {C n |n. True})")
        case True
        then show ?thesis
          using * unfolding chain_def Earley\<^sub>F_bin_step_def Complete\<^sub>F_def bin_def
        proof clarsimp
          fix y :: "'a item" and z :: "'a item" and n :: nat and m :: nat
          assume a1: "is_complete z"
          assume a2: "item_end y = item_origin z"
          assume a3: "y \<in> C n"
          assume a4: "z \<in> C m"
          assume a5: "next_symbol y = Some (item_rule_head z)"
          assume "\<forall>i. C i \<subseteq> C (Suc i)"
          hence f6: "\<And>n m. \<not> n \<le> m \<or> C n \<subseteq> C m"
            by (meson lift_Suc_mono_le)
          hence f7: "\<And>n. \<not> m \<le> n \<or> z \<in> C n"
            using a4 by blast
          have "\<exists>n \<ge> m. y \<in> C n"
            using f6 a3 by (meson le_sup_iff subset_eq sup_ge1)
          thus "\<exists>I.
                  (\<exists>n. I = C n \<union>
                           Scan\<^sub>F (item_end z) \<omega> (C n) \<union>
                           {inc_item i (item_end z) |i.
                              i \<in> C n \<and>
                              (\<exists>j.
                                item_end i = item_origin j \<and>
                                j \<in> C n \<and>
                                item_end j = item_end z \<and>
                                is_complete j \<and>
                                next_symbol i = Some (item_rule_head j))} \<union>
                           Predict\<^sub>F (item_end z) \<G> (C n))
                  \<and> inc_item y (item_end z) \<in> I"
            using f7 a5 a2 a1 by blast
        qed
      next
        case False
        thus ?thesis
          using # Un_iff by (auto simp: Earley\<^sub>F_bin_step_def Scan\<^sub>F_def Predict\<^sub>F_def bin_def; blast)
      qed
    qed
  next
    show "\<Union> {(Earley\<^sub>F_bin_step k \<G> \<omega> \<circ> C) n |n. True} \<subseteq> Earley\<^sub>F_bin_step k \<G> \<omega> (\<Union> {C n |n. True})"
      unfolding Earley\<^sub>F_bin_step_def
      using * by (auto simp: Scan\<^sub>F_def Predict\<^sub>F_def Complete\<^sub>F_def chain_def bin_def, metis+)
  qed
qed

lemma Earley\<^sub>F_bin_step_regular:
  "regular (Earley\<^sub>F_bin_step k \<G> \<omega>)"
  by (simp add: Earley\<^sub>F_bin_step_continuous Earley\<^sub>F_bin_step_setmonotone regular_def)

lemma Earley\<^sub>F_bin_idem:
  "Earley\<^sub>F_bin k \<G> \<omega> (Earley\<^sub>F_bin k \<G> \<omega> I) = Earley\<^sub>F_bin k \<G> \<omega> I"
  by (simp add: Earley\<^sub>F_bin_def Earley\<^sub>F_bin_step_regular limit_is_idempotent)

lemma Scan\<^sub>F_bin_absorb:
  "Scan\<^sub>F k \<omega> (bin I k) = Scan\<^sub>F k \<omega> I"
  unfolding Scan\<^sub>F_def bin_def by simp

lemma Predict\<^sub>F_bin_absorb:
  "Predict\<^sub>F k \<G> (bin I k) = Predict\<^sub>F k \<G> I"
  unfolding Predict\<^sub>F_def bin_def by simp

lemma Scan\<^sub>F_Un:
  "Scan\<^sub>F k \<omega> (I \<union> J) = Scan\<^sub>F k \<omega> I \<union> Scan\<^sub>F k \<omega> J"
  unfolding Scan\<^sub>F_def bin_def by blast

lemma Predict\<^sub>F_Un:
  "Predict\<^sub>F k \<G> (I \<union> J) = Predict\<^sub>F k \<G> I \<union> Predict\<^sub>F k \<G> J"
  unfolding Predict\<^sub>F_def bin_def by blast

lemma Scan\<^sub>F_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Scan\<^sub>F k \<omega> I \<subseteq> Scan\<^sub>F k \<omega> J"
  unfolding Scan\<^sub>F_def bin_def by blast

lemma Predict\<^sub>F_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Predict\<^sub>F k \<G> I \<subseteq> Predict\<^sub>F k \<G> J"
  unfolding Predict\<^sub>F_def bin_def by blast

lemma Complete\<^sub>F_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Complete\<^sub>F k I \<subseteq> Complete\<^sub>F k J"
  unfolding Complete\<^sub>F_def bin_def by blast

lemma Earley\<^sub>F_bin_step_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Earley\<^sub>F_bin_step k \<G> \<omega> I \<subseteq> Earley\<^sub>F_bin_step k \<G> \<omega> J"
  unfolding Earley\<^sub>F_bin_step_def using Scan\<^sub>F_sub_mono Predict\<^sub>F_sub_mono Complete\<^sub>F_sub_mono by (metis sup.mono)

lemma funpower_sub_mono:
  "I \<subseteq> J \<Longrightarrow> funpower (Earley\<^sub>F_bin_step k \<G> \<omega>) n I \<subseteq> funpower (Earley\<^sub>F_bin_step k \<G> \<omega>) n J"
  by (induction n) (auto simp: Earley\<^sub>F_bin_step_sub_mono)

lemma Earley\<^sub>F_bin_sub_mono:
  "I \<subseteq> J \<Longrightarrow> Earley\<^sub>F_bin k \<G> \<omega> I \<subseteq> Earley\<^sub>F_bin k \<G> \<omega> J"
proof standard
  fix x
  assume "I \<subseteq> J" "x \<in> Earley\<^sub>F_bin k \<G> \<omega> I"
  then obtain n where "x \<in> funpower (Earley\<^sub>F_bin_step k \<G> \<omega>) n I"
    unfolding Earley\<^sub>F_bin_def limit_def natUnion_def by blast
  hence "x \<in> funpower (Earley\<^sub>F_bin_step k \<G> \<omega>) n J"
    using \<open>I \<subseteq> J\<close> funpower_sub_mono by blast
  thus "x \<in> Earley\<^sub>F_bin k \<G> \<omega> J"
    unfolding Earley\<^sub>F_bin_def limit_def natUnion_def by blast
qed

lemma Scan\<^sub>F_Earley\<^sub>F_bin_step_mono:
  "Scan\<^sub>F k \<omega> I \<subseteq> Earley\<^sub>F_bin_step k \<G> \<omega> I"
  using Earley\<^sub>F_bin_step_def by blast

lemma Predict\<^sub>F_Earley\<^sub>F_bin_step_mono:
  "Predict\<^sub>F k \<G> I \<subseteq> Earley\<^sub>F_bin_step k \<G> \<omega> I"
  using Earley\<^sub>F_bin_step_def by blast

lemma Complete\<^sub>F_Earley\<^sub>F_bin_step_mono:
  "Complete\<^sub>F k I \<subseteq> Earley\<^sub>F_bin_step k \<G> \<omega> I"
  using Earley\<^sub>F_bin_step_def by blast

lemma Earley\<^sub>F_bin_step_Earley\<^sub>F_bin_mono:
  "Earley\<^sub>F_bin_step k \<G> \<omega> I \<subseteq> Earley\<^sub>F_bin k \<G> \<omega> I"
proof -
  have "Earley\<^sub>F_bin_step k \<G> \<omega> I \<subseteq> funpower (Earley\<^sub>F_bin_step k \<G> \<omega>) 1 I"
    by simp
  thus ?thesis
    by (metis Earley\<^sub>F_bin_def limit_elem subset_eq)
qed

lemma Scan\<^sub>F_Earley\<^sub>F_bin_mono:
  "Scan\<^sub>F k \<omega>  I \<subseteq> Earley\<^sub>F_bin k \<G> \<omega> I"
  using Scan\<^sub>F_Earley\<^sub>F_bin_step_mono Earley\<^sub>F_bin_step_Earley\<^sub>F_bin_mono by force

lemma Predict\<^sub>F_Earley\<^sub>F_bin_mono:
  "Predict\<^sub>F k \<G> I \<subseteq> Earley\<^sub>F_bin k \<G> \<omega> I"
  using Predict\<^sub>F_Earley\<^sub>F_bin_step_mono Earley\<^sub>F_bin_step_Earley\<^sub>F_bin_mono by force

lemma Complete\<^sub>F_Earley\<^sub>F_bin_mono:
  "Complete\<^sub>F k I \<subseteq> Earley\<^sub>F_bin k \<G> \<omega> I"
  using Complete\<^sub>F_Earley\<^sub>F_bin_step_mono Earley\<^sub>F_bin_step_Earley\<^sub>F_bin_mono by force

lemma Earley\<^sub>F_bin_mono:
  "I \<subseteq> Earley\<^sub>F_bin k \<G> \<omega> I"
  using Earley\<^sub>F_bin_step_Earley\<^sub>F_bin_mono Earley\<^sub>F_bin_step_def by blast

lemma Init\<^sub>F_sub_Earley\<^sub>F_bins:
  "Init\<^sub>F \<G> \<subseteq> Earley\<^sub>F_bins n \<G> \<omega>"
  by (induction n) (use Earley\<^sub>F_bin_mono in fastforce)+

subsection \<open>Soundness\<close>

lemma Init\<^sub>F_sub_Earley:
  "Init\<^sub>F \<G> \<subseteq> Earley \<G> \<omega>"                                     
  unfolding Init\<^sub>F_def init_item_def using Init by blast

lemma Scan\<^sub>F_sub_Earley:
  assumes "I \<subseteq> Earley \<G> \<omega>"
  shows "Scan\<^sub>F k \<omega> I \<subseteq> Earley \<G> \<omega>"
  unfolding Scan\<^sub>F_def inc_item_def bin_def using assms Scan 
  by (smt (verit, ccfv_SIG) item.exhaust_sel mem_Collect_eq subsetD subsetI)

lemma Predict\<^sub>F_sub_Earley:
  assumes "I \<subseteq> Earley \<G> \<omega>"
  shows "Predict\<^sub>F k \<G> I \<subseteq> Earley \<G> \<omega>"
  unfolding Predict\<^sub>F_def init_item_def bin_def using assms Predict
  using item.exhaust_sel by blast

lemma Complete\<^sub>F_sub_Earley:
  assumes "I \<subseteq> Earley \<G> \<omega>"
  shows "Complete\<^sub>F k I \<subseteq> Earley \<G> \<omega>"
  unfolding Complete\<^sub>F_def inc_item_def bin_def using assms Complete
  by (smt (verit, del_insts) item.exhaust_sel mem_Collect_eq subset_eq)

lemma Earley\<^sub>F_bin_step_sub_Earley:
  assumes "I \<subseteq> Earley \<G> \<omega>"
  shows "Earley\<^sub>F_bin_step k \<G> \<omega> I \<subseteq> Earley \<G> \<omega>"
  unfolding Earley\<^sub>F_bin_step_def using assms Complete\<^sub>F_sub_Earley Predict\<^sub>F_sub_Earley Scan\<^sub>F_sub_Earley by (metis le_supI)

lemma Earley\<^sub>F_bin_sub_Earley:
  assumes "I \<subseteq> Earley \<G> \<omega>"
  shows "Earley\<^sub>F_bin k \<G> \<omega> I \<subseteq> Earley \<G> \<omega>"
  using assms Earley\<^sub>F_bin_step_sub_Earley by (metis Earley\<^sub>F_bin_def limit_upperbound)

lemma Earley\<^sub>F_bins_sub_Earley:
  shows "Earley\<^sub>F_bins n \<G> \<omega> \<subseteq> Earley \<G> \<omega>"
  by (induction n) (auto simp: Earley\<^sub>F_bin_sub_Earley Init\<^sub>F_sub_Earley)

lemma Earley\<^sub>F_sub_Earley:
  shows "Earley\<^sub>F \<G> \<omega> \<subseteq> Earley \<G> \<omega>"
  by (simp add: Earley\<^sub>F_bins_sub_Earley Earley\<^sub>F_def)

theorem soundness_Earley\<^sub>F:
  assumes "recognizing (Earley\<^sub>F \<G> \<omega>) \<G> \<omega>"
  shows "derives \<G> [\<SS> \<G>] \<omega>"
  using soundness_Earley Earley\<^sub>F_sub_Earley assms recognizing_def by (metis subsetD)


subsection \<open>Completeness\<close>

definition prev_symbol :: "'a item \<Rightarrow> 'a option" where
  "prev_symbol x \<equiv> if item_dot x = 0 then None else Some (item_rule_body x ! (item_dot x - 1))"

definition base :: "'a sentence \<Rightarrow> 'a item set \<Rightarrow> nat \<Rightarrow> 'a item set" where
  "base \<omega> I k \<equiv> { x . x \<in> I \<and> item_end x = k \<and> k > 0 \<and> prev_symbol x = Some (\<omega>!(k-1)) }"

lemma Earley\<^sub>F_bin_sub_Earley\<^sub>F_bin:
  assumes "Init\<^sub>F \<G> \<subseteq> I"
  assumes "\<forall>k' < k. bin (Earley \<G> \<omega>) k' \<subseteq> I"
  assumes "base \<omega> (Earley \<G> \<omega>) k \<subseteq> I"
  shows "bin (Earley \<G> \<omega>) k \<subseteq> bin (Earley\<^sub>F_bin k \<G> \<omega> I) k"
proof standard
  fix x
  assume *: "x \<in> bin (Earley \<G> \<omega>) k" 
  hence "x \<in> Earley \<G> \<omega>"
    using bin_def by blast
  thus "x \<in> bin (Earley\<^sub>F_bin k \<G> \<omega> I) k"
    using assms *
  proof (induction rule: Earley.induct)
    case (Init r)
    thus ?case
      unfolding Init\<^sub>F_def init_item_def bin_def using Earley\<^sub>F_bin_mono by fast
  next
    case (Scan x r b i j a)
    have "j+1 = k"
      using Scan.prems(4) bin_def by (metis (mono_tags, lifting) CollectD item.sel(4))
    have "prev_symbol (Item r (b+1) i (j+1)) = Some (\<omega>!(k-1))"
      using Scan.hyps(1,3,5) \<open>j+1 = k\<close> by (auto simp: next_symbol_def prev_symbol_def item_rule_body_def split: if_splits)
    hence "Item r (b+1) i (j+1) \<in> base \<omega> (Earley \<G> \<omega>) k"
      unfolding base_def using Scan.prems(4) bin_def by fastforce
    hence "Item r (b+1) i (j+1) \<in> I"
      using Scan.prems(3) by blast
    hence "Item r (b+1) i (j+1) \<in> Earley\<^sub>F_bin k \<G> \<omega> I"
      using Earley\<^sub>F_bin_mono by blast
    thus ?case
      using \<open>j+1 = k\<close> bin_def by fastforce
  next
    case (Predict x r b i j r')
    have "j = k"
      using Predict.prems(4) bin_def by (metis (mono_tags, lifting) CollectD item.sel(4))
    hence "x \<in> bin (Earley \<G> \<omega>) k"
      using Predict.hyps(1,2) bin_def by fastforce
    hence "x \<in> bin (Earley\<^sub>F_bin k \<G> \<omega> I) k"
      using Predict.IH Predict.prems(1-3) by blast
    hence "Item r' 0 j j \<in> Predict\<^sub>F k \<G> (Earley\<^sub>F_bin k \<G> \<omega> I)"
      unfolding Predict\<^sub>F_def init_item_def using Predict.hyps(1,3,4) \<open>j = k\<close> by blast
    hence "Item r' 0 j j \<in> Earley\<^sub>F_bin_step k \<G> \<omega> (Earley\<^sub>F_bin k \<G> \<omega> I)"
      using Predict\<^sub>F_Earley\<^sub>F_bin_step_mono by blast
    hence "Item r' 0 j j \<in> Earley\<^sub>F_bin k \<G> \<omega> I"
      using Earley\<^sub>F_bin_idem Earley\<^sub>F_bin_step_Earley\<^sub>F_bin_mono by blast
    thus ?case
      by (simp add: \<open>j = k\<close> bin_def)
  next
    case (Complete x r\<^sub>x b\<^sub>x i j y r\<^sub>y b\<^sub>y l)
    have "l = k"
      using Complete.prems(4) bin_def by (metis (mono_tags, lifting) CollectD item.sel(4))
    hence "y \<in> bin (Earley \<G> \<omega>) l"
      using Complete.hyps(3,4) bin_def by fastforce
    hence 0: "y \<in> bin (Earley\<^sub>F_bin k \<G> \<omega> I) k"
      using Complete.IH(2) Complete.prems(1-3) \<open>l = k\<close> by blast
    have 1: "x \<in> bin (Earley\<^sub>F_bin k \<G> \<omega> I) (item_origin y)"
    proof (cases "j = k")
      case True
      hence "x \<in> bin (Earley \<G> \<omega>) k"
        using Complete.hyps(1,2) bin_def by fastforce
      hence "x \<in> bin (Earley\<^sub>F_bin k \<G> \<omega> I) k"
        using Complete.IH(1) Complete.prems(1-3) by blast
      thus ?thesis
        using Complete.hyps(3) True by simp
    next
      case False
      hence "j < k"
        using \<open>l = k\<close> wf_Earley wf_item_def Complete.hyps(3,4) by force
      moreover have "x \<in> bin (Earley \<G> \<omega>) j"
        using Complete.hyps(1,2) bin_def by force
      ultimately have "x \<in> I"
        using Complete.prems(2) by blast
      hence "x \<in> bin (Earley\<^sub>F_bin k \<G> \<omega> I) j"
        using Complete.hyps(1) Earley\<^sub>F_bin_mono bin_def by fastforce
      thus ?thesis
        using Complete.hyps(3) by simp
    qed
    have "Item r\<^sub>x (b\<^sub>x + 1) i k \<in> Complete\<^sub>F k (Earley\<^sub>F_bin k \<G> \<omega> I)"
      unfolding Complete\<^sub>F_def inc_item_def using 0 1 Complete.hyps(1,5,6) by force
    hence "Item r\<^sub>x (b\<^sub>x + 1) i k \<in> Earley\<^sub>F_bin_step k \<G> \<omega> (Earley\<^sub>F_bin k \<G> \<omega> I)"
      unfolding Earley\<^sub>F_bin_step_def by blast
    hence "Item r\<^sub>x (b\<^sub>x + 1) i k \<in> Earley\<^sub>F_bin k \<G> \<omega> I"
      using Earley\<^sub>F_bin_idem Earley\<^sub>F_bin_step_Earley\<^sub>F_bin_mono by blast
    thus ?case
      using bin_def \<open>l = k\<close> by fastforce
  qed
qed

lemma Earley_base_sub_Earley\<^sub>F_bin:
  assumes "Init\<^sub>F \<G> \<subseteq> I"
  assumes "\<forall>k' < k. bin (Earley \<G> \<omega>) k' \<subseteq> I"
  assumes "base \<omega> (Earley \<G> \<omega>) k \<subseteq> I"
  assumes "wf_\<G> \<G>" "is_word \<G> \<omega>"
  shows "base \<omega> (Earley \<G> \<omega>) (k+1) \<subseteq> bin (Earley\<^sub>F_bin k \<G> \<omega> I) (k+1)"
proof standard
  fix x
  assume *: "x \<in> base \<omega> (Earley \<G> \<omega>) (k+1)" 
  hence "x \<in> Earley \<G> \<omega>"
    using base_def by blast
  thus "x \<in> bin (Earley\<^sub>F_bin k \<G> \<omega> I) (k+1)"
    using assms *
  proof (induction rule: Earley.induct)
    case (Init r)
    have "k = 0"
      using Init.prems(6) unfolding base_def by simp
    hence False
      using Init.prems(6) unfolding base_def by simp
    thus ?case
      by blast
  next
    case (Scan x r b i j a)
    have "j = k"
      using Scan.prems(6) base_def by (metis (mono_tags, lifting) CollectD add_right_cancel item.sel(4))
    hence "x \<in> bin (Earley\<^sub>F_bin k \<G> \<omega> I) k"
      using Earley\<^sub>F_bin_sub_Earley\<^sub>F_bin Scan.prems Scan.hyps(1,2) bin_def
      by (metis (mono_tags, lifting) CollectI item.sel(4) subsetD)
    hence "Item r (b+1) i (j+1) \<in> Scan\<^sub>F k \<omega> (Earley\<^sub>F_bin k \<G> \<omega> I)"
      unfolding Scan\<^sub>F_def inc_item_def using Scan.hyps \<open>j = k\<close> by force
    hence "Item r (b+1) i (j+1) \<in> Earley\<^sub>F_bin_step k \<G> \<omega> (Earley\<^sub>F_bin k \<G> \<omega> I)"
      using Scan\<^sub>F_Earley\<^sub>F_bin_step_mono by blast
    hence "Item r (b+1) i (j+1) \<in> Earley\<^sub>F_bin k \<G> \<omega> I"
      using Earley\<^sub>F_bin_idem Earley\<^sub>F_bin_step_Earley\<^sub>F_bin_mono by blast
    thus ?case
      using \<open>j = k\<close> bin_def by fastforce
  next
    case (Predict x r b i j r')
    have False
      using Predict.prems(6) unfolding base_def by (auto simp: prev_symbol_def)
    thus ?case
      by blast
  next
    case (Complete x r\<^sub>x b\<^sub>x i j y r\<^sub>y b\<^sub>y l)
    have "l-1 < length \<omega>"
      using Complete.prems(6) base_def wf_Earley wf_item_def
      by (metis (mono_tags, lifting) CollectD add.right_neutral add_Suc_right add_diff_cancel_right' item.sel(4) less_eq_Suc_le plus_1_eq_Suc)
    hence "is_terminal \<G> (\<omega>!(l-1))"
      using Complete.prems(5) is_word_is_terminal by blast
    moreover have "is_nonterminal \<G> (item_rule_head y)"
      using Complete.hyps(3,4) Complete.prems(4) wf_Earley wf_item_def
      by (metis item_rule_head_def prod.collapse rule_head_def rule_nonterminal_type)
    moreover have "prev_symbol (Item r\<^sub>x (b\<^sub>x+1) i l) = next_symbol x"
      using Complete.hyps(1,6)
      by (auto simp: next_symbol_def prev_symbol_def is_complete_def item_rule_body_def split: if_splits)
    moreover have "prev_symbol (Item r\<^sub>x (b\<^sub>x+1) i l) = Some (\<omega>!(l-1))"
      using Complete.prems(6) base_def by (metis (mono_tags, lifting) CollectD item.sel(4))
    ultimately have False
      using Complete.hyps(6) Complete.prems(4) is_terminal_nonterminal by fastforce
    thus ?case
      by blast
  qed
qed

lemma Earley\<^sub>F_bin_k_sub_Earley\<^sub>F_bins:
  assumes "wf_\<G> \<G>" "is_word \<G> \<omega>" "k \<le> n"
  shows "bin (Earley \<G> \<omega>) k \<subseteq> Earley\<^sub>F_bins n \<G> \<omega>"
  using assms
proof (induction n arbitrary: k)
  case 0
  have "bin (Earley \<G> \<omega>) 0 \<subseteq> bin (Earley\<^sub>F_bin 0 \<G> \<omega> (Init\<^sub>F \<G>)) 0"
    using Earley\<^sub>F_bin_sub_Earley\<^sub>F_bin base_def by fastforce
  thus ?case
    unfolding bin_def using "0.prems"(3) by auto
next
  case (Suc n)
  show ?case
  proof (cases "k \<le> n")
    case True
    thus ?thesis
      using Suc Earley\<^sub>F_bin_mono by force
  next
    case False
    hence "k = n+1"
      using Suc.prems(3) by force
    have 0: "\<forall>k' < k. bin (Earley \<G> \<omega>) k' \<subseteq> Earley\<^sub>F_bins n \<G> \<omega>"
      using Suc by simp
    moreover have "base \<omega> (Earley \<G> \<omega>) k \<subseteq> Earley\<^sub>F_bins n \<G> \<omega>"
    proof -
      have "\<forall>k' < k-1. bin (Earley \<G> \<omega>) k' \<subseteq> Earley\<^sub>F_bins n \<G> \<omega>"
        using Suc \<open>k = n + 1\<close> by auto
      moreover have "base \<omega> (Earley \<G> \<omega>) (k-1) \<subseteq> Earley\<^sub>F_bins n \<G> \<omega>"
        using 0 bin_def base_def False \<open>k = n+1\<close> 
        by (smt (verit) Suc_eq_plus1 diff_Suc_1 linorder_not_less mem_Collect_eq subsetD subsetI)
      ultimately have "base \<omega> (Earley \<G> \<omega>) k \<subseteq> bin (Earley\<^sub>F_bin n \<G> \<omega> (Earley\<^sub>F_bins n \<G> \<omega>)) k"
        using Suc.prems(1,2) Earley_base_sub_Earley\<^sub>F_bin \<open>k = n + 1\<close> Init\<^sub>F_sub_Earley\<^sub>F_bins by (metis add_diff_cancel_right')
      hence "base \<omega> (Earley \<G> \<omega>) k \<subseteq> bin (Earley\<^sub>F_bins n \<G> \<omega>) k"
        by (metis Earley\<^sub>F_bins.elims Earley\<^sub>F_bin_idem)
      thus ?thesis
        using bin_def by blast
    qed
    ultimately have "bin (Earley \<G> \<omega>) k \<subseteq> bin (Earley\<^sub>F_bin k \<G> \<omega> (Earley\<^sub>F_bins n \<G> \<omega>)) k"
      using Earley\<^sub>F_bin_sub_Earley\<^sub>F_bin Init\<^sub>F_sub_Earley\<^sub>F_bins by metis
    thus ?thesis
      using Earley\<^sub>F_bins.simps(2) \<open>k = n + 1\<close> bin_def by auto
  qed
qed

lemma Earley_sub_Earley\<^sub>F:
  assumes "wf_\<G> \<G>" "is_word \<G> \<omega>"
  shows "Earley \<G> \<omega> \<subseteq> Earley\<^sub>F \<G> \<omega>"
proof -
  have "\<forall>k \<le> length \<omega>. bin (Earley \<G> \<omega>) k \<subseteq> Earley\<^sub>F \<G> \<omega>"
    by (simp add: Earley\<^sub>F_bin_k_sub_Earley\<^sub>F_bins Earley\<^sub>F_def assms)
  thus ?thesis
    using wf_Earley wf_item_def bin_def by blast
qed

theorem completeness_Earley\<^sub>F:
  assumes "derives \<G> [\<SS> \<G>] \<omega>" "is_word \<G> \<omega>" "wf_\<G> \<G>"
  shows "recognizing (Earley\<^sub>F \<G> \<omega>) \<G> \<omega>"
  using assms Earley_sub_Earley\<^sub>F Earley\<^sub>F_sub_Earley completeness_Earley by (metis subset_antisym)

subsection \<open>Correctness\<close>

theorem Earley_eq_Earley\<^sub>F:
  assumes "wf_\<G> \<G>" "is_word \<G> \<omega>"
  shows "Earley \<G> \<omega> = Earley\<^sub>F \<G> \<omega>"
  using Earley_sub_Earley\<^sub>F Earley\<^sub>F_sub_Earley assms by blast

theorem correctness_Earley\<^sub>F:
  assumes "wf_\<G> \<G>" "is_word \<G> \<omega>"
  shows "recognizing (Earley\<^sub>F \<G> \<omega>) \<G> \<omega> \<longleftrightarrow> derives \<G> [\<SS> \<G>] \<omega>"
  using assms Earley_eq_Earley\<^sub>F correctness_Earley by fastforce

end
