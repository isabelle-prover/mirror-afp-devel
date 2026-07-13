theory Lazy_Greedy_Oracle
  imports "Greedy_Submodular_Construct"
begin

text \<open>
  This theory provides auxiliary lazy-selection primitives based on cached
  upper bounds for marginal gains. It is used by the stateful lazy greedy
  construction below, while the final approximation theorem is stated in the
  proof layer.
\<close>

section \<open>Lazy selection via cached upper bounds\<close>

context Submodular_Func
begin

definition ub_valid :: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" where
  "ub_valid S A ub \<longleftrightarrow> (\<forall>x\<in>A. gain S x \<le> ub x)"

definition untight :: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a set" where
  "untight S A ub = {x\<in>A. ub x > gain S x}"

definition tighten :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> real)" where
  "tighten S ub x = ub(x := gain S x)"

definition pick_ub_some :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a" where
  "pick_ub_some A ub = (SOME x. x \<in> A \<and> is_arg_max ub (\<lambda>y. y \<in> A) x)"

lemma pick_ub_some_mem:
  assumes finA: "finite A" and neA: "A \<noteq> {}"
  shows "pick_ub_some A ub \<in> A"
proof -
  have exB: "\<exists>x\<in>A. is_arg_max ub (\<lambda>y. y \<in> A) x"
    using finite_is_arg_max_in[OF finA neA] by blast
  have ex: "\<exists>x. x \<in> A \<and> is_arg_max ub (\<lambda>y. y \<in> A) x"
    using exB by auto
  show ?thesis
    unfolding pick_ub_some_def
    using someI_ex[OF ex] by blast
qed

lemma pick_ub_some_max:
  assumes finA: "finite A" and neA: "A \<noteq> {}" and yA: "y \<in> A"
  shows "ub y \<le> ub (pick_ub_some A ub)"
proof -
  have exB: "\<exists>x\<in>A. is_arg_max ub (\<lambda>z. z \<in> A) x"
    using finite_is_arg_max_in[OF finA neA] by blast
  have ex: "\<exists>x. x \<in> A \<and> is_arg_max ub (\<lambda>z. z \<in> A) x"
    using exB by auto
  have chosen: "is_arg_max ub (\<lambda>z. z \<in> A) (pick_ub_some A ub)"
    unfolding pick_ub_some_def
    using someI_ex[OF ex] by blast
  show ?thesis
    using is_arg_maxD_le[OF chosen yA] .
qed

fun lazy_argmax_gain_fuel ::
  "nat \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a"
where
  "lazy_argmax_gain_fuel 0 S A ub = pick_ub_some A ub"
| "lazy_argmax_gain_fuel (Suc n) S A ub =
    (let x = pick_ub_some A ub in
     if ub x = gain S x then x
     else lazy_argmax_gain_fuel n S A (tighten S ub x))"

definition lazy_argmax_gain :: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a" where
  "lazy_argmax_gain S A ub = lazy_argmax_gain_fuel (card A) S A ub"

lemma ub_valid_tighten:
  assumes ubv: "ub_valid S A ub"
  shows "ub_valid S A (tighten S ub x)"
  using ubv unfolding ub_valid_def tighten_def by auto

lemma untight_tighten:
  assumes xA: "x \<in> A" and gt: "ub x > gain S x"
  shows "untight S A (tighten S ub x) = untight S A ub - {x}"
  using xA gt
  unfolding untight_def tighten_def
  by auto


lemma finite_untight:
  assumes finA: "finite A"
  shows "finite (untight S A ub)"
  using finA unfolding untight_def by simp

lemma lazy_argmax_gain_fuel_max:
  assumes finA: "finite A" and neA: "A \<noteq> {}"
  shows "ub_valid S A ub \<Longrightarrow> card (untight S A ub) \<le> n \<Longrightarrow>
         \<forall>y\<in>A. gain S y \<le> gain S (lazy_argmax_gain_fuel n S A ub)"
proof (induction n arbitrary: ub)
  case 0
  from 0 have ubv: "ub_valid S A ub" by simp
  from 0 have bound: "card (untight S A ub) \<le> 0" by simp

  have finU: "finite (untight S A ub)" using finite_untight[OF finA] .
  have U0: "untight S A ub = {}"
    using bound finU by auto

  have ub_le_gain: "\<forall>y\<in>A. ub y \<le> gain S y"
  proof (intro ballI)
    fix y assume yA: "y \<in> A"
    have "\<not> (ub y > gain S y)"
      using U0 yA unfolding untight_def by auto
    thus "ub y \<le> gain S y" by simp
  qed

  have ub_eq_gain: "\<forall>y\<in>A. ub y = gain S y"
  proof (intro ballI)
    fix y assume yA: "y \<in> A"
    have "gain S y \<le> ub y"
      using ubv yA unfolding ub_valid_def by auto
    moreover have "ub y \<le> gain S y"
      using ub_le_gain yA by auto
    ultimately show "ub y = gain S y" by simp
  qed

  let ?x = "pick_ub_some A ub"
  have xA: "?x \<in> A" using pick_ub_some_mem[OF finA neA] .
  have ubx: "ub ?x = gain S ?x"
    using ub_eq_gain xA by auto

  show ?case
  proof (intro ballI)
    fix y assume yA: "y \<in> A"
    have "gain S y = ub y" using ub_eq_gain yA by auto
    also have "\<dots> \<le> ub ?x"
      using pick_ub_some_max[OF finA neA yA] .
    also have "\<dots> = gain S ?x"
      using ubx by simp
    finally show "gain S y \<le> gain S (lazy_argmax_gain_fuel 0 S A ub)"
      by (simp add: Let_def)
  qed
next
  case (Suc n ub)
  from Suc.prems have ubv: "ub_valid S A ub" by simp
  from Suc.prems have bound: "card (untight S A ub) \<le> Suc n" by simp

  let ?x = "pick_ub_some A ub"
  have xA: "?x \<in> A" using pick_ub_some_mem[OF finA neA] .

  show ?case
  proof (cases "ub ?x = gain S ?x")
    case True
    show ?thesis
    proof (intro ballI)
      fix y assume yA: "y \<in> A"
      have "gain S y \<le> ub y"
        using ubv yA unfolding ub_valid_def by auto
      also have "\<dots> \<le> ub ?x"
        using pick_ub_some_max[OF finA neA yA] .
      finally show "gain S y \<le> gain S (lazy_argmax_gain_fuel (Suc n) S A ub)"
        using True by (simp add: Let_def)
    qed
  next
    case False
    have le_gx: "gain S ?x \<le> ub ?x"
      using ubv xA unfolding ub_valid_def by auto
    have gt: "ub ?x > gain S ?x"
      using le_gx False by (meson eq_iff not_le order_le_less)

    have Ueq: "untight S A (tighten S ub ?x) = untight S A ub - {?x}"
      using xA gt by (simp add: untight_tighten)

    have xU: "?x \<in> untight S A ub"
      using xA gt unfolding untight_def by auto

    have finU: "finite (untight S A ub)"
      using finite_untight[OF finA] .

    have bound': "card (untight S A (tighten S ub ?x)) \<le> n"
    proof -
      have "card (untight S A (tighten S ub ?x)) = card (untight S A ub - {?x})"
        by (simp add: Ueq)
      also have "\<dots> = card (untight S A ub) - 1"
        using finU xU by (simp add: card_Diff_singleton)
      finally show ?thesis
        using bound by arith
    qed

    have IH: "\<forall>y\<in>A. gain S y \<le> gain S (lazy_argmax_gain_fuel n S A (tighten S ub ?x))"
      using Suc.IH[OF ub_valid_tighten[OF ubv] bound'] .

    show ?thesis
      using False IH by (simp add: Let_def)
  qed
qed

lemma lazy_argmax_gain_fuel_mem:
  assumes finA: "finite A" and neA: "A \<noteq> {}"
  shows "lazy_argmax_gain_fuel n S A ub \<in> A"
proof (induction n arbitrary: ub)
  case 0
  show ?case
    using pick_ub_some_mem[OF finA neA] by simp
next
  case (Suc n)
  let ?x = "pick_ub_some A ub"
  have xA: "?x \<in> A"
    using pick_ub_some_mem[OF finA neA] .

  show ?case
  proof (cases "ub ?x = gain S ?x")
    case True
    then show ?thesis
      using xA by (simp add: Let_def)
  next
    case False
    then show ?thesis
      using Suc.IH[of "tighten S ub ?x"] finA neA
      by (simp add: Let_def)
  qed
qed

lemma lazy_argmax_gain_mem:
  assumes finA: "finite A" and neA: "A \<noteq> {}"
  shows "lazy_argmax_gain S A ub \<in> A"
  unfolding lazy_argmax_gain_def
  by (rule lazy_argmax_gain_fuel_mem[OF finA neA])

lemma lazy_argmax_gain_max:
  assumes finA: "finite A" and neA: "A \<noteq> {}"
      and ubv: "ub_valid S A ub"
  shows "\<forall>y\<in>A. gain S y \<le> gain S (lazy_argmax_gain S A ub)"
proof -
  have finU: "finite (untight S A ub)"
    using finite_untight[OF finA] .
  have "card (untight S A ub) \<le> card A"
    using card_mono[OF finA] unfolding untight_def by auto
  hence "\<forall>y\<in>A. gain S y \<le> gain S (lazy_argmax_gain_fuel (card A) S A ub)"
    using lazy_argmax_gain_fuel_max[OF finA neA ubv] by blast
  thus ?thesis
    unfolding lazy_argmax_gain_def .
qed

end

end